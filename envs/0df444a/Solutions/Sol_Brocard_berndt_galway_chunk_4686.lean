-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4686
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:49.11081+00:00
-- url     : https://prove2.me/submissions/f0f144d4-5b28-40a9-b8c3-bc8af281f19c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 842625899 ≤ n < 842805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 842627149 1250 842625899 842625913
    0x161e050412060605100c02062502030709050a140108060412120c0c02040609020c0622020a0b1c1b200f071701090305090d050c1c060b0306060105070320 67
    0x2071480c001c3c80a400b50034031400c100354001d80d001b446031b0b201c000c243d0b400410381b6250006c0d4007000350744110001e416582040310b00140c000542d80034040c1c0402483c50303286c081030500c0c0103443c80c4200c4070041480d03a102c0072050014050030700c00040540d440760348400c01c3ca443c07a444502c10f6510480c0000742800680c10100c1146c9499070025906010302c0c4242c8052250b82c1e1034968030070503805903094540e0342e5032100c0c0026071801401103142c03c0d0120a41c13124194001c0b50717008154403140680181c40700b00340c00540c50041c40d042060103000940710440c00c00c101c2c910a610f074264035000c03403482001c100102d2203104254110a03100c4c200d0724058802c41381c44890307134022b0036180c2d240c0c0e20400e21251800d0000348040a4180071300b2011a42c10f5503010300d000c51800420024500003541514244601600c400140c3c8075080c0203e0740d003807400c2c1220035010b45490308405070b0b403c0340c3c82d41c0c0c0640c019006010090b40c1050949032915410b05208500303c1c0684c0340d4141c00d010482c4070b0003040c81841 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 842628399 1250 842627149 842627153
    0x6030a0b04060807060e240a030f0516260712020c0a0c1701020a02101a04090c150519081f030b160c03090b03060114071406161e050412 60
    0x40300c1c1d040350100c4d01d814280ba200641003240d107a0071003181c691075002452440480184000003044024412700f00000d0703192a01d440041110402c581c07403180084180001500070740c00622100010b00c0c40040016651040030740c2e603699020103443d900a02c4844840111685d0b03998059452218000084951204041c00c0051a0354014800c03854456086203e401030200c043c001c88080110703940042c046d110094a0400c010300d2190346c489810220881c12500799616800380b00d031241e000751010742d4081d050520b10303050001c9807917680041c0003040001e1507030107216802280b00e010003410100c5541d65800514608840e5031300342c210072000048008001c2000305160030340540d03480b1071903905074410794200340c2c0e150561140180218100c103d00308068260540110303032018041c90544180d00040c6403020705500a400201c9008024804a00c0040e404015081e402a08804503440d00c04402d0b10203408465070400840d81a101d400820540d00d008908860040081c120006102c03041c42c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 842629649 1250 842628399 842628403
    0x807080901080601020d0207060c0314120a06080c010c0f080403020306190501052704050705060a0507061b1202070602040509070c032717010603080f030f0a021806030a0b040608 78
    0x5000d5140464018408900c1c1c552000a0078200c0500903001800c0c810700b403520136035003200d070000c0031010000312350700d011103031030f00b00020b840086a580341c50b210380c0c1041c19500301078951030b030003c40440e80700310120380711a070b801070000220301c1e080413281c05c3d0301000d810f04804034803860700040d4040c4507080c144190103034000f030a00c4c030420484108001a036210802c11001000c0103070a814006804d90811110011441017150070a100c2c00841e090030f946c48010444a800c02c0041d0f0001c0f4901081403424004039000d03460b40c01410390b81300691300c20308460140009005090003114550701188040820086904403800303090010300c01d0180c0d1828407401070183d052400d003140090030304540e03203081c00314040f105d107101000d02596118090501e10303d1540d00038600501d01c910740d00c451001011500c0d80004140007080c0c1d550b21952490402030044a001028040310840352040101c902c001441100f41044030004941c41540d9032030300383c0504051f01c8140b2075140c1c0b007881d048002446000c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 842630899 1250 842629649 842629657
    0xc0403061113080604030906050a02010b151c0b0a03030507030e040504060f18030516030c023307030509091e16030e1b0d0807050604080a08060f010e040216080708 72
    0x42d0801c0090955140e62042e900c5030301c2070350003c020402c90503080c84114003840241002603402e200010301540c180c03001a52501e4030814046201e800014113842c00e0720030041c2100400c14206040c0000c00c540c00c0802d540c021284005001c1050104004c803c240c0b0911801c0d40c03600000304103100904007410640003c06900d20403045880c6048044410049800b107640212078040d2942030520084410241c002e403d030200440030001d24059120060b600c090a254070354410540c0404052440f80d400e00107000140100050740ca000e20501000135400320469801d2541030741c4100c1c15072155020054204c407903451f494640c00b100000c1003588103100c11050200361083d41d007440350744940360301c403a184c1c844500c0c038000d20000000c60520a0414031099060b4900c902c40461400b503240d122340d41411800d03a0100c4600b100000d040b0001c070f030702c0f5503401d03040041183c45103002004180040d10904456000c00e009640200d80c2950840c80909010b80d9241c12101c0e0545d220603d140044c0ba6a00c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 842632149 1250 842630899 842630917
    0x100e010902181002151803040308090102150910091719091a03060607080717030115050f1207090f0305010b100302130308030402030307060c030933050c04030611 71
    0x421101480814030f00300d1079075940000340e50080c1c03d201d000102c54900488000700612102090350ba00b181d00041d0400c020002140a0180c064032529280c0009041454408500094008040038003207050404280b00c8003201140d04001138910180c0340c1807040e0980c181110b00c100d0000706610a84503004428403c0041c0b41e0740e203d2403001c2e240c892150745c08103642104a1404400e1000607840e04040002f4030010b4018904c0743e00b00b03203995036051140810042000c81e4032002100400240c2603090b0720300c200d04114108541400d078009019082801100149218a560720f00891543c0e03004034411030192444041d1413aa5644071305116029003541d40c8118043c640c80c808840c00244a4400e40c2c0010301c0c5120188541440c42c2c0f5012440d400250051340d060008000b00000241584551400c03c1416100881d10842600302201118000c00c80554601c138402e8840308420301904145000c500d084000141c142c550840d41a494092a000144454500115500041200c0c000303000200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 842633399 1250 842632149 842632177
    0x803040512030702030616031b0c030f0f0c0818030307150506010314190b060a0201020a0e03240712051e3103020a0507080c0a08011107110d051e190506040209100e010902 75
    0x11490cc041260355000340224003000035840c4200700700150319172b401021180d81e80b00151310018032610010381194042c500884410080c1c0403141c500034031901406901035004d003420811807080b4903012404440042030610a03080c500c0038441c0b0602540d100b0021004c01800040d114440d00c03034040d000394007844061021410303185412440d03203070000f00c410180210386070a815070341a0150740c41c01428050410001e000608400c203460b13011a00c0341c00c1c403c0030301070000e0040401d040384545181074003401502500a03003600b0516200703004e866a00b1450204c10486407440042c1c00d040b07040c04600003000300079009035040003440e11000103841c02e40ca03804844c2e02a030030346c1da805558202d412240060401140902c07541c0041804814038000b410805404c0da601d14056039982402d00c501f0b644120924025010492503501c1c04004140d010103803204c40c1d0380c0c1e50801c0d03124a0b030781e54402040240300d16000c10029841c040403c4401c2d00811854421807103d5071200705c82c1001e50454a0820881 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 842634649 1250 842633399 842633417
    0x5060d140f0a0b0d0f0201050a12020a0507480e040b0906010b0c0622060e060f07050403020a0509090109140105061302072a0503070803040512030702030616031b0c03 73
    0x9844c004848007080c0c0d0b440b00003030b40524010741c019100c81e001750307625005001e90b4500c1c0d00d010140358001010088000c0d901c0319541c1d2003034a8109510001800d440300250500300b248030035040100e4064003611f031042d170b10051b042c03801c2d44000455074094104d40c4024224405001c00c22110055460040c01c20000b5076181d6a2280b05d40c00c4030340100c140013595507104401044880001c0ca00040490b941b8075140364487d5002d440f00c0d820b56118040c55021940024204103003040040d1606401522a140041c605440d540003d081c1480074042d0521481c0500007240350420b0035846444d5099102d40c140f03820300d600f144841e00a050440b0705900440d10500540b001902c01c0c4200c402d529486807205080e0311040c0a680155008543c1c00b40350201c2034007000c1907564041104a0052200c0d0005681e228100070134010347d00000d201c07901d099402808440010f9078080b48041c0c3c00301d50b00c891031100d095140c104030040e200543d010000b40b41000604a0f0340c41d032010094071114000d880342c03084 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 842635899 1250 842634649 842634671
    0x1d03010e0a060b3007090501120b0603070f031a060907080411211015030b010b0304080415031d0d0207120507030506070c021f0905060d140f0a 63
    0x990303600c48600381032a0440300c20080000c49540c44010103c20103045034400f80c114000102405508031110b80520b400f402e40101c0100c1d082118074050b0065030014841541b500d01c0c200c1c2c001d04403d9000b0101d000107000100f19840800038140104084c05086404560700d042039404150782c0080c00440542050005909d4108156024040d24446e51a546035590b90b0321103003000c81e0602540b5a0211100c9040c1c0080018051001c3c141c841d494081c0c154403858072203400494a02c0307480101010429031040012035100d070030841c112034204504550380e40d19407a01004c144030350741244200c0050656441c40080c0d041e40300c03000e5090101003a05813105810071031b40c1d03620101051040141d000117001c1c064001d42c40c8244191078426400c41d2540d82d1643c0d107550421504845020000e141507680c10305503d000c900c0c04802054131844c5580480350380c0300c01071055520703000705802031074000303000c451302c03030315075103c1c03020042c100b00c001c2c1171802d108180600003041910303c0d001003410441b02c492 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 842637149 1250 842635899 842635901
    0x9010b04050a08150a110936160302030c071e03090518040809060c03040e0405070b0c0d0810030605040f0b0a02040f120602040e0414120a0522050607031d0301 70
    0x401c0c0348841813030300e05584950030200588000f0080341c900900502400c0c8558590a00ea4140c030101701040e411880031003a003000095a0075504e150090141e081440800189003a5070344141c419031038023680e00d076644223059016101c0c240303008220001035002802e40c414007144d00001c4c81d10941c0c0311082d007542d8404012200000c040042080500140410700160b6503000030f05000001030122030620304070078009825600240d02c5042c0c1c90014004201c1000014001c0c0700141c0800c1d052241821251114039503100015039858050106020204403035034800e584080056500c000700384818640342ca0024400050300790300b22820b5090f0404a110002d040c004d0720b069959046e055410b1074500b00d404294801c4600c41901e2040c2c0c00c001c0072420340080a481d910880c001c0d10b00010024041c202580303480c00c2c0c1c04a0800c100420301000340800d41c014203c59080c810010329041080000c94078080315003540d481f10364004000142c1800f05900022039154000c42004406142c600c9881814 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 842638399 1250 842637149 842637163
    0x20307060c030e1b040b0d0605150102030c072112050c060907060512040c030501050915250806031e1e0102040501020706080a090b07030b0906010c02060f07030e09010b04050a08 78
    0x100343c40c2c2004068803806800b21903032494243c030050010440310311120100d1604546241c0030303690f4030749400801041c0d403803043c01c080c00c6030828801185070041d5280e0740358032100c83e406000040030400d184a510141c014803500c12642d00102003002c214464280500607511880c4d143c0254042d10000401c3c500000c2007600883d4400c0e104c0910f0064021b16007884085c0052049500c000012004130104800348141c0e07200e0b11903440184082070707954042c500144030040444640c0b810b01d07141c1d800d480700400e40a4140f1100c500340000c840d202c11000a00380440c4440088500c03400c14040360b07100d0300010f0443c2c50140310980d16044081414041d07401e0b0f101d09e011326809a803203907234104012886902141d5001d401001d0000d0250308564800202c40015607c040009803100c912031080d1a1000748160440c000b420405044840b90b40414001c3c081c003403481c19002800b00e010000e040c010449801900744c0245520565a1203409a0340e50b50031601410b4015148000041280200042d00f2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 842639649 1250 842638399 842638421
    0x141005010f0915050901141305150f0f030901020c0a03030c1b050d051b101406060c1b06070b0c070b0f070e0d0212190212011103040f031806020307060c03 68
    0x600d80c605a80f0070035100c07640100245170400c5a07140302c25080515590207080000b4513016500143c624010801803801003203520340340c0c03803101046018500c0000500300c0d1100d01900c2185078599441080c0700b40240140300195001d801028203003010107515510030391812a0907181c00e80b2803061480401c40043c0c0140c0c000b031041d07202d80d80032100f49014001401d5100c81c00346200c200040d41c1c000032814042c19101070302c0071a84580c0d81c1e10305801c900940d1a03210b60160750395420f1100e0000d07074035500c40c170a5129410700c652107140c0f416030b510b4400440d03401c142c1144002d60705060407011038090f80e10440d0140d5010300c041c00800d0141d1041d0014500481240d0b031aa58251492801c00441401400d0101c2e4402002480800b04842c24000c0941000ea020184d8807986d8039801807106000c0500841e40306a45407101c5254604004419640c000341c00c0303102002c0307401907490107980005400c2c0c4008101c0185010000b0040d500200404403a80300f003000313105002502c0010307030a88500040e8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 842640899 1250 842639649 842639669
    0x3110a0902030a0e0d03380d1b0902070519080d09081e0a020d0e04090605090d110c010c0809030307020405010e04060c021513150513020f031b060d141005010f09 71
    0x41c804801f04400a400d0b5441c01c60385801e182e041c0180040c100c4c0394680e0f03003140c40080fa91040e1441600c2212118002c1a85000139803500022f81d4503191640700400d4892410440301050320148604179040d01c42d01504004200000c4642c0e08080605070080d10080c42e585460000346010b01891f0b00c180c9640e240306030002d024503409803005413940720303280c0d5015800aa803441128041005801a240104d203040c02600744201d40341da0040007058800c055401c1c903400020301105a9900078020741d4856002003089454000101c0040d0440c07103800c60280d4041d04002c008900e41d02d24072050743c0187d00c1114200302604480405030703262071041410f83c0c1c4e40c500340b500052a4402041f0b1450300303580314844d040d0507181031004a0044030340c00d4070314035106840c802500f000c40c2060001035400b2081180108104c005508a1400d080364010350503001ea03402140c000c0d100c011a0304442c0c220369810b86000380341c2c580000741c0340019403180325490000d40c0602084100502412005090b07c8800c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 842642149 1250 842640899 842640941
    0xe0c0f03010b0304030216060305160c0c050409050a02040e030421030f1b0b0411011805030604020d1e08090411030f0a05181002040e011e03110a0902030a0e0d03 71
    0xc0c02d0100d5000100b0590950281289000a149401e59400080c1c20583c074006218105107598007050b20582c2401010b000c3c04400100200311508100001c031101141c02298001e1a440d282c0d040c29451440290014141010f4094101d03000c0094416500403404c0c0c825102e064110696800c0c40e114000743c003003601c0c02c80c040f40e1244166514502c048001c980041d205100b5681c881526074200d500f511210f008550a02c00c543e403000c88074041c2c000300d40320f1403003032420140021b0302c900005d48000e01c00c2d00881701500401010329031644c401d082c0a80e030070720b03c60801c1c01c2103009a4000107603e48114580351500000d10480400d41e4014002c1e00c444445980c0d802e1076900042401426601c10103c04000d00b00749100c0c10824150100101d0101603262803415089011352141030308204156624140a0210f81580c0d070004130480f0380110002050f8404a00864000e05080d000182502d00000800c401c2d405941c10103070f014111070080320b41c8110020340407000c80c1e1800e098101070501000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 842643399 1250 842642149 842642159
    0x24040206030a09080703020d020f0309031c091d09010b04050f180c060d140a0c02030d020a0504090e0d02070803030601090302042714160b19020717070e0c0f0301 71
    0x409142c1c44402414000303803140f01034803000310542102a0860059100100c0b06000c0c03541449076110041c1440c00860620460f04002500c03507401610b002210b018400c1e101040301d12451441c002044004002500c02c510b00c4182e1118078000c444449256081070103ea00a0034135101c2c9910130b001011660500e81c60300b2841d507000d00815100380030f07103106440c0d030a201942c80500a02c03e00c201c4500c0011b1848a0598801811100400c1d43c00340c9840d0100140c01d00d50007000700c403040b13800c4020040e5918401c0e28182d849001d00c1d042965214a400c1d14000c06100001d01c40c0d9581d1029021541d820f40e0340e0b01d146076640b0007140d980340000c4404038100300509164000040ba5505941d0114240569101d6800300040c00c001c25070340094180744940d00c6441c20f000e84026003e428013881d2009082003400100e0f84109206c804c0780b04211034010078004e10900070b1001401e480c1020380c082c1c2d6507142625642d0500d500604210a9100021805580120782100c035074903001c601d16400c40c1e02c1d00e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 842644649 1250 842643399 842643409
    0x60f040c12060b0301020412060b03030301030201020a170d050f0403020139090905041b080309031b1819150503070902070f060e010f270209190504110102240402 71
    0x11070012900180c655454900a40e42800608041c003541070210f1020f1245080040944030015040f5010341c004100500260340e0102e030a1040742d8000d42d8010864100b840980c14510034001810401031800e810310038800ca011107403e0045010f6802404961104420801c51801d0a2a8601098003c03480c0f2450715003018010f40094109060070f10600f59900040010758804031070480d8000c0c16407031404804808810810b016240d08001581050030820202ea40c66615589540d100309103200c20f205070707603901d0ba000c1a0743d4a20311003d11b0a410052603031a180003400e400603000500384a8104611140e0b028018120f82004000780003551500c0c114400035800720704207079000380400c1789100c0481d0240c0242c00b084c418030710000541c59448a80b8204a420b4007807400484200030080403407050740400020a2290111848101522814900404401e1420f001190705003400200400c0c81480b0307150244181003a02541c1801c0075410b1048000300c1032100400310300c000100454054208 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 842645899 1250 842644649 842644679
    0x1406071e090902040f080f0f060606030c04180b01120b0d0b040503091e09100321020f0f0109141204060f02120d1505150f030c130f0602060f040c 64
    0xc14204565900c1d00c8004030400e81e0700c941c0000150400c000d9080000000030000030f0f60a458107005081d040a40081441c0c5941d07018003007600c02c03c0080082a014803520084600400360b20f0b00a515411a04d191030740500310441e50030f408201009143d884598060042c41c01020f0020a01e1038403e0311a62041104034004d0800e0703807140300901810f01a030b1645071020b82080390041c0f20f050301d0b0b41000100f21404400400c0c82c0d0b50191101010030020701307029201c540880b04d01415248200404004914003900c41d0051911482030310754031260400103600c03503d2580e0280180c9070369280810310455a40e803010300c071013a1580040008004980c412508010329041c5841a11003042000380c041c805074004201d0810b920360b80c0c2490309031051345c19001000500080d2641084034145282c075007420300076850900d82c031403070000020b100710b5007000413903010504c10b4005503519512001c01488800e0f5a014840152086101117030722542c904034642e105d154000012040d003030404170f482c040b40710303 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 842647149 1250 842645899 842645957
    0x3030c08120c030a0c0318061d030318010614010503190b06040303030507030e0c060d0b0a0b03010b0301171c0f050c01050f150d0c0509061903030c140607 68
    0x9007400722491080341c4050081c010201c20741c085840b41401400c00c1c0031070700030820000601d0302e484400340307a44c00601091030103103400290004001402c102000e0390820404417aa1b0300d408000200200c0c3c1015070310f0000b0403003640d8004c00c070300303901e582030700d10207c03401501385020560900002c0c00d804608101010848000400440ca501842e00494a682c1150f003007180880e07101c5007004203043e80f5220b20030032110944000c281141240c8041045131058001103056142c4450042c0566200c00c401c04000300002c01c4140c1d52582d440205892503002802036004055486c0d00c1d010360080c00080700112016254030407c00303c40e89850a8071030903910b461007401c0c4101444503450110080c4100c6106100d0004500441d2410050b104091051946030790b1050742020504408510000e02030703c29150241c070280d0240d1100000190200301d10300240c0450a0308103004010540c3c400d80c0c010070781c0e220790044842804d00203034039500c9540448100300080c8c40003800208040181c101404e5010b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 842648399 1250 842647149 842647163
    0x50c030f0c071d06090f06103c1715060706110d0e24010b0a110d020706090f1805061c0b0f09030705190201050d020c0d141303030c 58
    0x360384150b07840c0702c40426044196070b40300c039a08100050a1903008540d00103806802150140f6050b400903030040401d2350582d00b04040c07a104040007150061601a401e04840c1500c5d074540840c2403628110002d5075a14000287c040e1468203181d100803609a004a48155810050a81c40c005000190b0040c00782aa080c0b62504850b45105c40d03880018410014117120100307241d20803c4150340b50006803964500a9942031a42c1901450119050b03810740710745040ea81d9480c0107400c0c2c0ac4a074148d5a82500d103403401041206a007051b0002514801c99609444a08030030350754040c01008403000e48039003041c00e12408100c104049007a8445548281c00510003801c22a840f240c0010311000c05d00c0481e00d140f2200305000d42c0014076201c0f8cc0c0c1c07203c5200025894a1020782d90107464070b03100d0741c81000e00028800c2c1101160300071800d4035171035106030304115101c1103007880c0269102c0248003020701090700a2140b085101d04641256155080c404207000c5080c51541d0407100c060301244156451 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 842649649 1250 842648399 842648413
    0x92f0a02061810023c090d051e0607080c030c040902070f0c0b1804020c070e1518070e03070803030601050a05070b041a070315050d021f0503090c01050c030f0c 70
    0x8840c2c900c0604402500e244500c0d803505d0300446400c0e007050071440d0340107244565002850100200701d040710810745c0c040e61104c50b00f4041e07180030340c03814030b00000c14980700b40785140410f004a800210544134040c00d5581f80040d40700c10110361719070b200980301c0389810b8008100c180720008494005004c41480f8112884000a103503c840d10f00000b65042003c04510002e000c1c0d8540c0031815115005a000720b500311701e45450b450f0030300d41d12560361044145040106c40020f0504114120035000d41c003024124540400320560b0107a0500307005c4618002042e04002204014100041e07200709885210f4000e5184d6150f00b00155040c0d0042113044080180404c030500000b0b80201440740943e110303440e84c40e248445800103180701c0d00020050b500301490102009190231200d8844800c450080c0c0740e912105010740040b0701c03100700304248000c10f08004410240e610f40d020005600c54017158040d85d0511840c0401110103100d01e00901981d42d00034011221540050340091510420103c00c036081c1e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 842650899 1250 842649649 842649673
    0x70c0302030303042d0302211216110c1e1507050a03030e0a02150d0608160e180d140720010e042003070507020306010306020a03050105040b130f06092f0a020618 71
    0x149d44011185440000c10003484040ca15400c000c1c4141507880c4c04020b40701c65050f2002240710100010107031108030032250300043c010344404d5400d0f8056040b460303000342d58011900f00755070b0b02d1920850450019240c00c1901080c108045822143c40364020501c07038034075481d10f80340384994000701040c03e03055a4401d0005051841002401000d2010740760480b40185468a500103840d0014001501e00c2034000320345010b800007241ca08000c01d06802c0039401c0440110712200c45c1d0203019401040012600c4402c00000c0226100c42e41c0000c09a80724107103000818103000c2543c0e14100000060440c04503401e09003051032019681c407080381d1404505000007600000d207003004c02c3c0d1069860030b038006803450303a2542c103009950140109031030610401420b0300100c2c5401c461521041ca03c19900c0303120341c2040f199070f004032004041e002c20902c0740309180e014480c42c40b182d28601402024500440000c01200a002d450750f68030290050640ca44d610b15080611541ca5041e01000c2c0c002c40d001588 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 842652149 1250 842650899 842650927
    0x31a01030e07081501031a0709120606030209090c03010e0c01020d0c11041e0b04020a0c0602030601031104061d100e13060f150e03071406070c0302030303042d030221 73
    0x100c4042c0c613070b070304402c1d515504005288111030301810441079041800c0144081e0004101c8046844035240b0b0000d5124905048005160304e420003940500c0c6007060001024000520f000440c10844c020007800c1000e030020f50342d0b85a04d85502d40035800458040000074000c1107842020703805142070790b00070305c10030740010111840c0e40d0034610403030440c580b51070001c4050f10425080781800d0f1411881c28000a4024028480c0148000d05c5641c002001078101c6c0d110790413111a55004400d50f079150764403010040c2020052400c003030071218500310f00310914a00382280344040e90654031441201c03140c01003030080001002844220342e030b45500c5c0004e10b0a0340f004000c4002d261a08414107580b54654000b000c8035100400366103c0c0d030124000703100d440e80c05404000845411103000c2e50f14150f40c0341c003044c421540d41c006075042c040481000284038400440000f203800300314841d0b0401c81350303d0760600316290b108006801640070403200e0340342c010f03c90f14100c039028000308414207050001400355 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 842653399 1250 842652149 842652163
    0x20d05060121092102151302030721020a03050106093204020607050d090e01061e050a0c0f06050f06060f0405010e06041509050907030b060702060d0615030e0d031a01030e0708 77
    0x304c0142c0c030440c021442c0b600303c09009034009508552240d00c6003e9600000c1d9180c0550040c80f402880d17000441021414103c107001015034041c0c1621001562818075900a08942c414034840900b0840030001010818010120f20b900b0f4003110011090403d04040441c4130080040b604a0810801440428001c0044060000188d0342d1400d48908000040c0c0e14084180d101e01c05001c200132790300340c40545c007010030081100b0f03500e0441e84802595070202c032281e80382400a00150f02084c0303040b0521a07960000752142e80d107103248061903200c1c40d040c00717118030408900c0b1240d00810300040c485903104e0403c182800400402031802c084d15004000016480c0b108242d000c00c00102c0d04110a08017000e025a200e01c07141001c0180000389008103501e0b114080e402803055a00203002c140e9413416a02180c0074000184100b40c1585040c0c0014004142e074030b030a0788451241410b180d0026210b40100500081010911500c007000000158040e041c079031406c0c00070b405920300221346101c2c104021 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 842654649 1250 842653399 842653463
    0x15021b030c0a0e060406060c050a12050d020d0f05090f030a03050423010c0e0109080c0d0812180c0405010b0d022128090803061302040f0306020d0506012109 69
    0x10a0f039814401c1c204401c84a00d644140c05210b04202e81c40c01040021a00d2040711340c0043c000500c00008040c12919071113070410141da55072011a103a412100964025a81076541820801144d29040c084668644044100030360780d03401003100c0001c041c030035006150402d1003280c0050911204884414281b0852004038185079550702c002c9400a0740b02c042501002030a00786a03d5907410702d01c419844051059055004400090400341000b07418800c031141300c403203020440010f080808209414424140301c6403180c0c401e0030030248140ca024401c0314100c8400c14060781c40c2011110047c000380d000203c144c80e8510044003c4038010f1860183d00303100310140044004040c140c070321907818080082c126520080c2c6030481d12000203680c0720072070b038000100325414000300c40c1da8000b40019204030f41000060403414100081041a84e8002c2c01c440c406851040c44659194001191b020a61421200c205011911070f80c010480b40d61000b0303082c501070350341d4510940400c5051a0403070104210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 842655899 1250 842654649 842654669
    0xe0f2206180c0e1219030c060e0105010317031027090b0105040f05040c0302120f150f01210611040801051306060b04030b0705160b07020f01050115021b030c0a 70
    0x81e110b490350028028a200741c04136281c041049400d0400c0b40c0d00d15184c0552000122900d2001c028540102d2086c200b00b648140d09001099901413007034040d02c030070311040350301c0008040d0300c40075074800d80d05a0b032040013002461200e481c90240001048024481c150349140a8104d09000d4044203000341d0b41454014030002ca1554544024842150900042c40304a140b40034148070010743d0560039042240c0c0c048a80009615a44800307a04049d590b4140783c00c9403151040607020700b881c0c228858440d0089424980f180d80c1c1e111070103a2040d002066a40c8801c540e1501080051a00d611400c400510041400c1c01c043c0c0f280c00550031140d0555500b446110040344240c108650ba000c2e43d070203059252021400c0c03900e90380d82c404901c0740140c9070006021010034065050404103c41c2c8035220b800054a0200d400c0800d03001c1d403185008440b404032942440001308290522080c40030844a8982c0100642c58030002e0990104900400c3c05915000701c9002a403145c0d030b4071030540060208108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 842657149 1250 842655899 842655911
    0xf1b11030606120712170a08150a030b07140f161403040b070308090c040903180f060906050327070611190807020409060e0d0e0f220618 60
    0x1042514101c00140020302c03814410103207094103100894144100e5240340e1607585030074040d140c511100d5450080700e5290443c08603103041d005038001c2d911402401d03029804442c800340d040034805235100900014003400041c8020840141c880c81d882c04504240c41d8036541030201e500c00f88041079001038441c0d01c200c0c002c16200750a1090220440c0c810904900040d4580391412040000c00c0c050014080d003441624800540141428030462800f050f004004011440161a02400941e403490310101902070002c00803c2d201e483d403d100094600589130410700c00c1c0342603011501540010025203030b8002e110300a040805158820b40000045100680165414100003c26400081164a04560040c20120a141590b180000c4083d40281d8603da4541442c001310f00508070040c4c000300117900e01104000c2030000421440c01d4010942e840b40d103843c042804011500d40300a071401c3d807040300895408084140c1410300da595103400707035000c0384466454040c0406451000a4546072503203450b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 842658399 1250 842657149 842657183
    0x30307090e092d19080304030e030c090c09040e0616140405060301060c080913020c0d0206040b0a05040f050307030504060806010f02100b19120c0e040b070f1b 70
    0x4640254021250001480504100e241200e52010601070b001d01d802141183d10102d11014011101030080c810040c07000f50006240c408003c0e40201c40a4000884001500c40c041c900800d04040d0703160018068041600d4054071a0b04641c0500c0045070f01950300d8000345404036050101600c5010010021400115200f03405021b91070440da604150b0702c0308100c20f00107541c4038025207054462502c0e20708000e01d6107190010a900c240381f030040d0b002115081110b980f409076001800c203400b03290b05403014540c81d000183da0f03d10040d40d00402c01c80e200000a082000251b000c640c0c45400380c28016510442c075110a41181e20069064000500000d8140807084d0007100440e001036003840d001c0701141c209407000352515041c0034000f02458488038201e040780d992450301d030142c11000703940140b0b159503115078106510440d881180c040047c50000200065078030840c62080707400180c16030250307849032001c554410955190105121000d0040c15829041c0405c1c0c24010344280070000350031030341d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 842659649 1250 842658399 842658419
    0x1703011e030308150103060b0c0607120c02070506071704060e0901150c02150c01020f040503060c0406080f040c030602030406050a0614010918060b3006060306061b03030709 76
    0x19080960400c001081000030f03400085140c2c80150498030101070f20710180124040d0241c1c1e404072545040101e5030a84e80800459402c2c05526075490b030b200d8a001d609480d0065900c881461005600a204c0802180c1050401400c25910031078030002500c03014000c6850b40e81140e0000c038001000c5450740d51183c10322005503070140c4030120031441071032030340c5030010801004440d0090080c2c05841c44c4110700c051b0081510080b2000500a64a6001540c80100705412034801d9501c80d21880c03010441c1510340400300c0d800d0345c04503611010795941301003168082e5a005481203440e1303000b105d070000c0401e0080c805103014a110344000300d00303070404542c20004d58200303404c403c032130f0096403001044070781c0c01070981c500701d481189500042000c040040801800340781d04c00c2e440e4030b1700085d0301202d05d1808400140d0825020300c81e800ea881d168454408590011201c00e50041070410109207a89044400f070041100999499107400c18020052400d581082d204007000c40c1038030034288031030713090 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 842660899 1250 842659649 842659679
    0x6210515070c15110901030903090e01150212130b0f0c010914060f060f100c020303130e0903210a2307020c0d110d030507050a0803070f02010e06150d170301 69
    0x15403c0140104c10443d541450580715811348036050554030401c1d8000c050080384180002c20100025206a40c0d40f03035900303010498800340303800041c0100700121106002c4902a10030803a001c0300a621424104680c10388241e00445284285150912243d00020001d00071900707241c2c0301d1141411154800c0380c001e0b02c0d001010f0410700c2e101d0030b000b041100c591221101170059640c12a16444002c40385002a641007140010294160100140e0300b4101c3c1105801003044400c580105145562840c11680c2c0324011904c0d0400d0a074032031440380320800c0c2c000c0080c1e90001122000000c540c2451040e0301c02103038041c54000c04020916041040c070700d40600150744804000d035080c80311072200c0c1c1d03035001061410136011032060346051004070070f140c81682901c0003641d0107001c444036014603007094142c42d0000c54a410010b8003e01800484c0e41c0706000f2003180d04074013801059a40c07185203050218055181c80c907a0444045652000824290303452003038442c201010407a6654140003100490881d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 842662149 1250 842660899 842660933
    0xf041a0a0e06071a150306091b032b030609051302090114010903080d0605060f07050106171e0120040f0504050405072d090b0306090106210515070c 65
    0x2d002c1c03240602084400c0196001c0b2030428207001240e40d100d81000c1c1d4454400b1000581520900040044024000035200000c1883c04403951060707441c01c0801d9171b10140d82d1986241c00380d0314480c040c3d943c0307c00051140745d5009800d000c501c0e282c0711440ca00c1112000c42e240c4d1b280781ea50450420a500b8426403c078050280301c0f0052800300520030000e041003010b07100c01010904001445c0300145159440701000d07100041040303903940200c4070030102c1a000b182064450b54645440000c0e400c3c2c10030040042d80d64130101a050706100c2c05014202c83d0b0507110015625504da01000080c107160700c01341440141030700000e40e221820106110f00c030302110380000d4081d52400d810b00c4049140061014101c03040319030440b502040c81c1541203800401404010081d00104001281b00140c941141074035840981c01c031a080e43c0d0300c0002900f80c80b124131841841e88587c07588101c580c62002c8000203100d00500403243ca0300c0c04803816100007002103400000040b40c442826003040b60403420f0f801611 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 842663399 1250 842662149 842662159
    0x120304020d201801530c01020706140c0f030318060105030609070b0c120f0403110d320a1b081c050d1509052d0c0f041a0a0e 55
    0x140c100306908001008403005914242c0001540714600040180580141c5a003004084039107450507218001c1400280c011505d1030141404140181d480051031504a4026649110711140c0009884515620802c007050704c034042c40151141540d400c00c001c3d80115000e002c040405107101c244d060620701c060708201d101360003810a2141610380000c0c60300a0b10003190040d540c985000b00280d18000194607030f42c0c42141c01044603188100c03d500a80200d90003000140010282c41042028504500c5070051000880320203000110f800c0c0d51001d02001000c80c0b600815145050340c143c6456018041111020351115000000062025a02c00100501c1c80100310340304c0744541c01b2850320750341084401080800700c2d901c0c400c4a0f0700e40100309284400040b200c1e400343c8880307004000e01411101d2991a00c2d0b03656001401030064080d150072413100040304840c40e21507025800c80380d40101440e0301055801e001c0440c0e559000b1242000307031090346018659405484001800308034290142c1c510403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 842664649 1250 842663399 842663401
    0x2407060603150e01060815100f090b0f01031509110408012a0503010b2d070b010812070c1205010254040902030709020a0c1112120304020d2018 63
    0x10301c0001d030070300d000e5003a003c40e519550755012142d06074802540127241e580306c0031400284920041e0300c401c0146605030380200c0320040780d030019400d0b514039180c505c4400c0481c4101300641c1c03015034000341034416031030383c101d1034266102c1c0b185d401d480b12a14180940822001d440700d915500c0071020742e8455181c00e00c281950f01d400701c81c204030300403894088140790100b884407140c40e58403980d03134111441c0c04002507160425070404802c458000d0103021814071030045444c3c103070b0180d00143c600e00b643c007104141d25903003400d83c0300040300d40c036400481e003540d000c3c404110b60300002e0200da86007120208110070b012400314401c0b0440400c2c4020b2040c050302403071002000d440c5446640070802403d40300407444103940d10200c4c1c50a080c640c000d05100e0f102150403290142d100c105c00740441c0c043d1000c010300380780603030030445001c200201c0c01c0c0c01588100c1103064110380901c091a403060005101000c1d80d40c0c41d4465940c00d003644c04569000c10442c4250034083d00d40344500c0801d1102d401110181 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 842665899 1250 842664649 842664659
    0x21c031413021c020a03020607060c090812091302070804150e1c020d0f0b01180b0a12030c17030c120a141b041805011d062407060603150e0106 63
    0x20030403103075000e500b00c0354854083c00c055455244201c80210f034094000c0d80c3d00c603400d052007001000001502c4000820100707002421260009108036201e81c10403483e4074007041281004001c1c08182154000e15800b4040c88010603102c0014200509901540481c40c4903002002007244140c911360301d120350401a940d01041d010001084075407030f415940c07000020361504150200442011005010071149000881d01c0e406603032000402c0b5445140c1840a41c120408201d044213460003420002c10804107000007203441640d460034003d005401540c0b59070800402110581d1040303030f0f030f800004d100068010112030480381d1a94411800782d01009031149040940c07070310030000b400980203804060800c0140c41113070000c03240101104001c1c40c1d06950070050041c082c09091040b00301001d003d901220380d050040d0790883c0b1958000b00142c2803c2a45170360910f8900c00c000714850624018807100c400a0913610954001d18040c0c13103181c01741d2011181c40000c0c0d41080444000a90501d8000c02c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 842667149 1250 842665899 842665909
    0x2040e0114060705010c09080d02030c030a14130b03010e060402070c090c030e0313030b06011809270b1902040305100c1b0803010509011401020319021c03141302 71
    0x8196188000700d0310031003200714009001c074010964050301552074145a6040da41c0c0101e503a030111039881c01600e11404440302c060340c890040000014043d00200008000c261054071180100101e40a200e8282500c04802d0820070722150040800a10000010301411040c0d4100a41c840c0e070880b8103501d005499911f1031400000c600c03a80b80c0194440c050a104d15002e500850b440c080b200c0c044035100c0030460183c0749404210b00c015120720081e940405c0d0b82d5417180318241100405807040048903441c180700400200407030b00d0702322041081241902d0b040c00b20030100a81c1c640c054601141c140c1404490140202c022503465040c482c4104410000140040b480644090181d200002d100444450a0320741c41d00c90b28581e10815541600c07541006030a0340514141c078010b0700c2d2001c1c280e03250b0700074020f40c1c40800d108031302503402030040c41c0c24084020b21403407160714248142c07100a0704490001c52a0a28804100046034884400000c8044036502d0f003076000101d109844034203502900421 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 842668399 1250 842667149 842667151
    0x4050615030d0e03071e05120c0901150e2206210201080a0204030219030302010f0c0905060a200309010e0603040209071101090807140f0c0619030b03121c02040e 71
    0x100f800301c80e0741c0d11032091341c00f0301c14000105041800309162000c0812914400061400742c5441411104011070f8800d500103201642024040d10882080e400c0c554114894901d43c440c16003007010291039000f0350781300c0c0b0044030798814441061820561280c0030741801d640b00c0d5017150b00d03411425094001002e10a000742445540c0a08003401c480d11540c0810019210315040603420000c203200f001103049100c144202180c2c0203034000c101016440c0e56181c15a0750130305215002035825101402140752601c010310380300c2000d040c6180c0da40d6060440c00b0160240051130513198001050100640d42c00c042c148800c81002c803540761640c036146c0e0009031284805000a000c2001002101440040942c400c1105a8210041e25150007051421100c01c01100368484007501540c1c60020042000182c1c08060b103c00410490419504070307580001d60201c01c03084410140c44403a24000b545007480303016010300303104070079581c2d0304d4200a403045100601c400c0c2060440c4101f0040043c9003401d030b811 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 842669649 1250 842668399 842668423
    0xf0a09080a110f0a0209180a0203010c0e1008010503030304021302091206100605250812090a060605180402060c010f05010b04030209090d02060a0b010e100c0b01080328090b0c01050405061503 84
    0x41d000849040282d0389881e230801d41c02500756103070101403a0a550003c40008981e5002c585590380304102c0101110030500c28805c00f605940140f010500500d004483c4100410301c0c664010308080b207050001b0b80740c06518640b902590010014402d08040080c2c0a002074442030801c05e00d0880303099503d0390304d1a0394002c1404044804a007200400c40e4400480d40c14569035000e003601c9080a040c42a120207100508403800c07450440009054103007482182c540e052100c0942d08280d451b0b40910009900425841e5802c1d540d895845404290600c5150301030400c41d480d090320780f170861050110740200a8030340340b80d55211400c10144268005040b030307400701c1190800b1805410320801078903145107c804855012640254240e800c0b944620300c16552402004e401013940da0303910a19813240b2520b07000d4807446e83d503d12010b104149046000404004c1441c0444d03000f41d544c5074682c4550400001c540803039454805100a201080001e2504019a952045440301c480d0700000d039100507082030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 842670899 1250 842669649 842669671
    0x60b0d0b01150504180e010b0a03050604020d03050d06090605030c0306041212090605010b0712091206020906040306020403050307050f0c011209140d0c1e02090f0a09080a110f0a0209 80
    0x2080c10b086204500740c800400d1020128040203a01c48410b4000d8400b0520503134440d0700c0c0030310050561410701c0c1d03040110b0343c01c0300c060941a201c84c3c081c00110740140c0c0382541404000c00541d00e61180318840c0360011f00d11f0040005030a0b080c00d0816042a10102a45120350701c04803c0c80049101c003001083c0c0e4881c01e080c040d001d030002d0386044018004002024101c145050000038031200c680c0c00400c0b05911450030038144400c080d4003030b00d103c3c01074010700340c400c03001c1c0c2c0784400091055401002d840c00010321441c2410f81c0d0340d44d11b005a0340a81c1080700c15800100d5500100541003040c400c0780e90802c8041c1c900c1150180000700341c0c019182c02c5002c0c040e01c91003071038203120780c460420790700341e0012003581c150b041ea407075026241c0210034008a4400ea9800c02c42400708102120500c1c002c0d6008102240d0b64640218448113a50050808004c490f0381c0c90601c0c00040101c8014241c0f0f0059403105462240f040e0859428180141c000e9072450708a040302c540103030349500029610042d000c20b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 842672149 1250 842670899 842670929
    0x30206090d060902131a01021606050c0304030c09150e010602060708130f0b16050906030604020c12030403090512012307141b01180510050411040513060b0d0b01 71
    0x40482c0035203103a07440650858401120400e01d4851604800309950319841280010311a0100482e5a49200782c650f2611300c0c00d961083c040d40d840b980c010060941500100c0b42400d4881d02d41003400b504070341c404103c040d9550440b040070b115020007040141b030103005082d010b604d0300074003a403141001800c02d000c0040600000700301200d1404130001c2140c100c021151100400d01c3c0409813405d084d00e42112400900010300f00301e6125000312a0f81040107071107a41142c40e40070511010b50843c4602d5019801244400010004407002551240c1e01a03a10207108a242c02e0a001000c0700039100640076034105000f0606080d0014840c1c101c0302e000c2d81100c0050b03510b8402c1210718400b00b918200700c1c5500065900340c41c0e031102d101b881d8585034400082000200074804954401400e50001300b054000000c14903001c21158801548180030341200c98044d007000d030004045440845a106505c61501101014001a44600814002c003610504440515510b0712492030038140f04629041150394 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 842673399 1250 842672149 842672153
    0xc23011d090c19080718030f020d0f080f180108010b160212010612020307090c02060c0c0709050403170703061a0f0d091a06091023030706020a051006030206090d 71
    0x3000711040d6003036408030010640d030034000040a00b4429200c0c2d0001404d06c0e491039a104003032200d07000c1280d41c08820032441d043e295083c480310041c81c5c6015243c81d0711210111010a5280c4010040801ca4909041e502c9032038034080b80309904a00d9040707041000100040c0600c85400048038a00c2c2c001400c050f130501c001d44000741504013811400c051769420180f0000f4034480c03500c02c0c0c5001c3ca10072000d45c0c031541d84401c00c55003240c2040c1e0103480181e00c0307400850001140302000303101c01c0d2a030f1000d6448140d203490800c4295081542d04400050768603074840114070000c1005504850a490103208140c50007030200000e101c01080304007008400580500c04c8028071084403030404410105000c440305500340b450306800440450401404240005091481c0c8064850b100314050851140201e090604001d16521030300d0b0080f2155401c00450300a541d820030403c13008061b90b50040c5985201c0789011f5040c1a0800701182005081c84024001683c42c0b006652002e48299641c1903511424 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 842674649 1250 842673399 842673421
    0x51e15060409170a03060303030e1501030f0606030c0b0909100e0c0a02150a05040210050702011205060d02091f090b0f06031902030c03010e010e0f1f030c23011d09 72
    0x11403030a5100c00500d01c2004c9405411010460707003ea14100900e4030941041600c0c1e40380286c81c900c010300c085006000280301c8921a210580c01640700240c041d8695403195030214140c0c000f120b44180108008440b0f2070300002860b4851840ea04414405242000ca41c0b4031000142c80103036503900118505d0000c510070840e841c0720070111b14100940d820010003005c02080c0596080e800340c1c46c5101c038054040e01646c101c1c0c0c40164180c0d640408100340c030342d40400606015150b59845581e840c2e400b4056650311500074066010600181c00c442c41c10009101d80440740d500c4002d40506020b420000c9558184c0003410481007501c1c072950b00e0751080208001c00c0188440fa400d21440442441f441c2c201e42c10146060700c076000540011642c80360840c00381c0300011a0811104040e04000400030f440003132182a12050920088540a4403552014001e00d855005060050464541556100c0d0071060b00700c2010401c4c00c25104c15001c500d1500c69024291700c0c402c0c011046000400c10105071 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 842675899 1250 842674649 842674673
    0x120e01090b0d0e03040f080c010503010e0402040513060c0f0f0908060a020c030c0a0812060402040e34030b10081e070c08040612050a020c07061d0409051e15060409 72
    0x43d80c1d0035656502d45036451030854001900a071b00300c510901032800c0e19540628116410b031010080030800c01d030340310740c20040070300401041e01f400c26522400d03000028005000d2141c001580c1d494900d040800070740010704201420300001d00b04810703403808000180d80441e030a50046041100980d807007601d101107074a1440b030145026181c0c401e43d01c00c10103003c1c48401034003415102c0300c000d28040d02e0f1007003000107a0040b070040720340c12020000481c06100c8000030034404000f4143d008041d00c00d95502039040320f00700360304020220b81c90b018044c1d140d2404071074020444e05103051401886c100b007042508051081f0709070480620410700442c0c030b418000d2411903101c40d4800380e8160342d0b646805004000f46182c0801d90440b50400001c1003000d413441c000d84001c030403090014041c030b600e00750040310756202610080410082540d036404e410307159400f681507114014001070521302c0302c1c2c110440c08607a41d180c103542c85070810f0740700b801a0100b41d035415030022803c030713400700c2d1005c410306002500d260 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 842677149 1250 842675899 842675921
    0x501150302250b1f0b1b0a050111040806011a120703140403030f0e0106080c131e0501051c0c0e0702030c0106030506180c090601200109060504120e01090b0d 69
    0x4602454001080030800c00f05124242c00360340d014101c0b072001d50308415403a090085000042003800021b4000014101006001c0010030071914402440d40320300d400c441518806800700318001400341f0246c81c04003c00340c01444038180c40310030b80c03024940b400d0050090460340140b140c44c0101040303004e482900488011490100f02e19481e041c9494040c004001c041c00c8140c1c0642880210309a018040c07250b00219810f5030040d04800d1503c07020000e01c50701e6010036100056072140d25a4001c0c07010701824001c0d85403007000185d254140000c1004100320710111454000c1406d5050300001c3c0d00840c1c42c400c54104501e1061591035808041c0d040d40280700404286600e480c0000040c080c00282c2d00e4000c101807001315103218800c20002d9120305185003001d13004130340d18010842c15403003054000009000c00ba126a01d1800021481e42581d0080381c0c04d590460300c401c04e00003404103807a030490341d40216040000c5c103840b003200080d00390190740c4035244104002049a0503185110341103500342803 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 842678399 1250 842677149 842677207
    0x501030b011803111f030b01030524120f0604050109110621060d140d0305071815020f0d1d04090b15130f0e120a0210050a140108031c0501150302 64
    0x117048004020300900c40c940b4898000380c140404122101e840b10180030601000c0040c25504529550030b00c000d0141c60801c2c400c01e4400c2005400c0c1c14002480f140340150312034800418080c84500b080a00b95a00006a80c8a1750040101d803180c00340200401d500499102c08081e2682c0e02e0500040500314140400b40800948000c500080300003c1124408021a40c40410154031020001c5444030800146042c0c01007a1120501211100a610060300f1a040c8100c0d000b00c1000d854017410440c41207200b4011aa00102d81494074006a2240300075400c10354081200f210a038480004400c03000d440c102201440c502c03448141d4880100141c0c8060014505000002c0c0c030b440250000c150181e0480074074020211006002000c40c0d003103c8134081a64001c0c08020b0031048150002e00d409008525126681c0b104111100424020030b4000e100f800069a2104030400303404000800c0c4101c0c900360249040d006000340310090f00c1010030142d0520b0300584130707d0215403141a8000645001d9805 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 842679649 1250 842678399 842678449
    0x2120703150b0d020904060603110d0902150c0a031d0f040b0a030602220b0c250e0103060606030e3016060c021b01020a0210270501030b01180311 64
    0x100c3d005070024040f100041d0780c00c000041d6075000450407207408030410806c0503400c00403851514591303001410042c0c00240a80584920b102a1070f9050340070020201c040d40007400e0040a15400c030381d0ad01c508490307051402c40714140e0500002c076070082c81001684036594031180c100103910f8021001d8050342d4000011075855201284000800d554803601e814031b020026408942c524420003a14030800b1502d00030049250460182c4402c040210003000369501c0d00040000d40180c042e6004d4001d5008040005410b403c0101c01010b91704000c0a2441c02d50091407000c00e01c004c00c00741c603008409003249420f006078200c00c43e00b5861003490181402841e04445680900003950b1000d4440c0c9032903003c0303807649607076580c03044d401c04500004180540c1060154602501700004e50740c107502e110386804442503e02c402c800e82045120070b02901442040e0900707204950b0940705105480000342440309043c1d44115100d510304000d40001001d00329448052001a200c011118003490300e8181030b40e0300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 842680899 1250 842679649 842679667
    0xd021209010809101a0307230609180703052502060403050a09050a03050c030105130c06051e07030804050c062b1d061506041d04030504050a030506041502120703150b 73
    0x303100b4505440c18071a0003440d10021381c00d1005e10600d406514841da023001442e6407501007201d01d400010306641c00c1b0100f03c1110310641007544041c0d2007100b403614001980d0819010803180306420710000c15403441107200014103540c0008074143e1041c0c0c07522300555100303140b4408070b0704510035902803900590401008030400501281e8440c16107025002040641d446103d0b0a1a02101520107492020592004d01075588a03400510f500b40782c180c00c01808071201861000e00d980007100980c002002a01400100082480ba1000e684000c1703a0640c00c0801441c0b180003803078641c0c034201068102d42d00c02c402d85030025030845038050000101461000c0ca147c2e404039100c0c5c0b070848008650f1050f01c0e5402800386003c3c801e90701500c010012020ba119111152403a0408014100385c050100510001846a4524143c980910320500181c0f00f103040516080c2d21148143e40c52025a074018808017442060251a503a84004289408104031064403030300205c0301c060f038100095903040080c81d460 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 842682149 1250 842680899 842680931
    0x50c12060a082b020d1b08160818030313051c02060f030114060708090918120d0b0607030c2319030e030601080706050706140412020d02120901080910 66
    0x1a5101c18500190001c41d40380008907100c0b406010784501084210f1b60100c031200340030340c4060b09148501c56151406184428200400242c200102d41001000580d40b42212009511200fa440b09500442c20312198900844081550f03000303441c0540c1581c5a4003285581c80d401d03135803065401800e02c6688a121102c0700c60a54070034001c0340100700300818030b16524148401110005034114084500704045c00080003203000000c0d00d140310703072044248040042d41c424040c15010007440002c3c0e50b5a05900e08a4800743c5030380203145481340d1410320028021a40124442e207000d46d1011020b0380708100e00326629000c00803521240351510804558503100d1621020440940e80641c0394101c91040c42010141d9900c130900442886811511040003400d004601504020303118810210354540c41c14090003800200300c40643d074503082c80000c074050350780501080c1c0700c2880ca0320180200782204000002688241c08c0070038104a00303140040e04c1d00000380b01da840b071300052a0301030002c51b1510141d40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 842683399 1250 842682149 842682193
    0x2070305160c06020d0e1e010e04140a0b0405060310020f0706181a071e050403050105041209121101180e07090608090c2209020612090709050c12060a08 67
    0x3e00544110180b0041d002e00916100114820042150171140704e164512445034602c010142d05212407105e00c2c00e06580d45000307030b5407144803500004030146006c100c8a02030b01c46418101c0d00a901c1c0030248042c3d92404170b010f0b04001c040c00c10140c0c0c3c4180d20740d040c004901c52040c0103000c05141814900080e10f12400c940c08040c020180001a0792111f00301c050380c518140c0d069004550300c14214006401c0b003c24000300a4918103246041a40d0380c1c1b169803c0d64011581203d501c50451000696070340c0000010000d00f8003c420b4082031021541c4170000010b03001d14803410f1201c403010b400d4038508907400349006402a1a10401141001780d0003418411050180001043d030300bc00084d550310000418145100c00145010b202a1004001100350300c42c0140a0554a4664035140c0161b19554004e0200c10030130450842c0a281c900134150802c251508121009810107051048200865003a6030300d01910324a10170458549030700041a0792003680c40610780e4081c4000c1c00105023000c900070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 842684649 1250 842683399 842683409
    0x7020604090f0b010f0e012a03020309090703060f03080d1b02012901020c010e0307090615030c050301050a05010e1807361e0801092906090a02070305160c 68
    0x148510f8425600540c2d80080e000342440000342025406900d40d0b02c5002200200c0321103030540c810703c40c0d0b001d0311a660108401416000b603480000c0100e400d090005032940c3c0440c8519081108030f08000402c41031010394400504010700c0441d01c0020340302c855003c100700b8840880d01109222500d00c001e4040d00c0e5941c050460300560488821101104070051070403008141d02a000a03004a001902c1d006500d42c40750384c241c42415000b0403000b0f410311408014100000554101d2000400010306550302e020120042000500c0108801e494040c16842619003d0034528041c031070303420100d08250081c8800b6444c0c00c00f500c05000300e2941114034440c400800f00652001e07104082c80e00c030705845a046001c901e9080c14039080103171081011205401c4454500c1841c00ca81d40c41c03203018255040d011040e2184103118100e5100041c0d40d20000d024045020f5040c4d00300d01c0c0880c0054010030000300402c4946030002407401c00c140c4110300b22001410118071040c006041402c1140740c805040c081c03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 842685899 1250 842684649 842684651
    0x180a0e06010f08060a0513020903151803210402180411010e0a080d080402030f0d09180b010c02040e07030c0f0914011802130e0a140a11091507020604090f 68
    0x2c0003101d80d00c0784003e14840c260150400903402d18000a00c00c402c45181d00000c2038603400d2151602c0c44d0f400303100c5560030020040003c0314500340510303e200d614800080e0880103510402c280c0308003201c010205910309004100d1f61810396214004a104200c1d9400a0800d000c591000c000400100d07407149081001d0030b984410b920141d85060041d8040b85005a10043d400103410010f05c911581403694010301c05401c0e00c012140902500c0d141c40c88070101800424100e001c02c1c448401d000c1000c188103413410301c0600c0303901c0c51240040c049a1078002e0107070040362500381c81203100030100a40d000456000b2100321882ea6508511b421075038a030b00900c62a2800c0c9071210b05c40185550207a41a241141700b864280f24400c0070903002913102c1c45511a603141c00300c0b00090039440c140e01642c800d130001d40020546010602801d640508018400d2166a02d003002d0b52580d0800c04041d00c0075000c0079110050b5a081041910209004400e0f00a500410004010440c08070f10b4206100c222a00701c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 842687149 1250 842685899 842685917
    0x5090d05071e1404020d02070b01060509030d05030f040b1812030a0f090203030301090b04111b010c030c05120c09061c0c050403020603040609020109030501020d06050a1415180a0e0601 81
    0xd400b0540480d0b84070302640b140490900314041d1810754000c1c14601c030108401032400c103459890000405090744100045800031500440d142010300503036101082c82d10700f42e441c41c0362503941c107003c0701d50240c000741c4240c80300c50000e0540f10f043e00c11002070010441c1250001042003095010550045448400c06400c2c08001e240c0007032309001d80070030658000c025508580c03e0000442c020b2000d105403540c051385030720718800c50400000041000c140380072502c03907050200303480305400d507030303101041004161601001590082e485025a8482125120026181d44441c1c6050762540921458180d1140e00094001002511766100c5400701204800500c490440f5107010b070796501640c07001035003282c03040000400260103580603104407441410140d00c455120b1b01d401d030880c2c210348404108580d69000070310041c50850a420000c00309412035030003804010b80400c40030b01c0c0d6810301010511011640c2e48102010845540c40154040c10007440280c0d50300c0017085d0400b05440c0c482c08940045 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 842688399 1250 842687149 842687189
    0x4050f0106080a1b0b040b0c0c0402030411010e030a0302101517030408070e0c040312020a0b040c0f0b04120b04031103071514150105090a030602120609330105090d0507 74
    0x201810417034003c0e0010a003050b281030425040c40e40701c4600002640140d02c00381a096480d8400f45014500948104408000c60300014040305500c3d0700340d5100e80d001070b8500c000a680080d5099203c1746003074002c40c5001480003d900d9040302504240085100c0e03100c00f400c001400809001210b555600300c40710295145403020816800b514040b403071312810081400805d810f0130034407a05d02d070b8a1040b00c840342166190044880740c15682200d02e01001e2404000d4000c40035502e0024004040c0294070b40782c07511402d202c03001500c8600602d99403940c80081c0c181806501501c01004014080d00e80d80e500a203840020381c02c140b019200d0b00341c5885508402d40300e0081c41c140c071440c0314601c620100d160b12001034410350095527840354442c00502c0044001141e5002030900c15901e41d6168566007022010040015070044c40c0380ca08000614980041801814001c03880040c1544499440390800004070356a124490003d0741014040d50158104507000402c0c0c2c04407419080e0000e03d0007010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 842689649 1250 842688399 842688443
    0x20c06061002190807140705010f030b010801030b060312030406091a0c40030b063001020d0507051b060c0a0e030115060801080c0103060b030f04050f0106080a 70
    0x7009000c010b0740107a07000a00c0030010640c0d60b50143c040c03451a41001d1296413401180807481d0312030205600074410402595800a50860a01d0468141030021500c0e0200007808600305110240140d1145404204191414801400c501c12a5050140e8038501414004003500c00380400710340b4003e038800500c80300154001100d014980400c1564502039800c1c800d03601c008102541d400c02c4032201400b00c944440803500c0360b6500790743c041d40c13890391710301d0741c201542601d00042006025540c000036222080410041e401122500c60306024051580340e00304070300a0250b4007280024a181406202c03855401c140034160b02598803203185039602080c1800358072010300b0758084990710401d010254803233004142c0060000303000350001441107100c90b210380040100307030f020f1000318200c400180b190410902518803024000c0c241031040925042204800303110080c40f03482811b04610104040110910802c04410341140003485800e4070b982c001910b80c403070600c1c00ca60702e003021443c1c40443c82035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 842690899 1250 842689649 842689669
    0x6040b071710120c0801064205070606050904030c05060a0c05030601030f0b030a061b05040503030a120212010b0a030606020f030415020316031d03190201030f0b0a030501020c0606 79
    0x41c40300c1c068810b5142124240762400050021034040d9450724011600610903c40c0800030b0108030160b4002e142902c040003030040c600c102e03603250603c451034003046210b01000b1940c0d00e1400d42c64599615440350612070010700b66070700b180d0350050b002030a0000740742c4c0c060001c000b1903008505880d0f40752945481c42040318031428007000481c009000050040d8029070080108030314401c1c010581c0d060354400a0f04242d031407a421980c0c00ea1b2000c000410243d0b903000300601101a0404030b1401e414036000a5803400b0b9401c0010802c00300c5220f01580c1005074068407151503210311300c3c260650b1944001501d0b90000b40020780002c0c40c12000080082c07000856a90a00d5250069440c0070300348980075100b52200b0004a09521003002021554480e080342c2e40c40b04ca001c1d40d20180c01008810202d042000c0140c403041c404c3d441a41074818092002030540c011660900f800181001101042d402612000128550195541d02c000090040640040a80004201c00d0317526940e501c40030001c036000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 842692149 1250 842690899 842690911
    0x902040e011404110a031406040b060109080606041a04051303031118060a091503020c060610022508010c0504080705010c050712030e04020d14070203031e100806040b0717 75
    0x48010106000c00c04e404489582841d0141002d03d0f200d807a070715551505200045c8480e12a403141003040240b0805058013600b100c400d1030581035440c5024151650b8110140c8100c0c42141e0f40c850400700c03030840000c00c2d10b803a00b01520600107440c0040a46040e0b07070b25100180c001c01d0811850078014159002110804005542101c910b0750007007090144036080000d810041c4407003080c0c0425580d070b00950707034140102d40e507801603502c00c5000901030411601611243c003036811003042029450b008952401581030180400c07600d9016541c440140841a9200c000749501c2d000c401d40701c2c10360100040007030b242c05100b02c1d9a41a520401181c160440e40000341c01c9030008035092140c2ca008284030301c901402032810320f001c51341900004003241d00072207003182410354a40c0602140c14511140582c80300081c00031b1070462502d0034600e0b03140d60b0882c46c0300c00c1250140c0d0000b541c2000c0c1090140103400301c14111486031030a45400c0c0d580d14010b43e10407010034540c0c052407440000a1080600c154 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 842693399 1250 842692149 842692181
    0x209030316020301020903121b03090d0f03020715020109050105010803030405031903020d150302040b120d0c1b080618030a0c02060304060e0609011a04091a070c05010e010902040e01 80
    0x8000da448420402841d000101d03499502040608240c1d50100120003040480103500b6654070341101e40c1042011b00e070030303040529820034400d164580e51081c000e02026600301c00c1d2016082e01034032703089080c41101d80101c0526144043c00d00e07406981503008203180c070700c039030020021642c030742c0003041d039a0104440c020840c1d80104100107240b0030b140110054080039040242c113100542510b18250ba501e20400401605900020019841e06006020180b802620100480500103030070507201c3d04005030790010701101d0180d035402c01c034079a10714541d07805c02a4020284113880e05d02090300d61a0a80d4140c0c0302c3e80da44444201003074004000c850100443d41c5803508448403d60a2084940005000707481e00d40c1d8800705842000d00c00d110a038130601249000040d90301034400c000921420b4000e03c1d600503441c00c005140000c95400b030418507058405a40d24459403554001ca80700d1440140080255090450039a40300b00305400c0101424800ca506020196910302c1c6242255400c1003941050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 842694649 1250 842693399 842693407
    0x14060702060c0f1207020a0608060f1e031009030915050d11040b0c070f090e121614010c1b0b0714090303041d010504020703050414060403020907111002090303 70
    0x1441c00000034015941d100c400d44200310405156182020b03021040001a51000280e1408624105403c08050322890801900608082011a5600308031405240c0140f0b00002680152408140c000c40d0040000f800c45100b03030701c40c00040c005400c001a048020421003130000c1081c024120440c0c900d100b1680d210360a00756440c0450340908602190000043c100700004288003005000401104030b1b880700070a1610f280c42d1050121605070781c00444501d240410500051801007180f032084050601c40c42c0d110f500300c08420020920700e05e00206a4944d6001140d0005c5041d0480c0079440816102c21440c442d465051a601e50704507000141041222400104246e028108122080c2180306220342061048404245981c1c03043d009100e80c0b2050590301c801425121081c0390151030190303015424480c090350007800a0080d8040d88072a2a02ea883c0c59955444150070b441c029a0020100c0d01241011040506190003018103598140960415008140e13458003c0f030b88003c401500840ca4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 842695899 1250 842694649 842694653
    0x32406050711030604242a09080102160305091c0f05190b01050103180b01081b03010204080c06031308040f05010206180c130207171312020105070609050c0904050c0109140607 77
    0x20816402c40c5d9040c02c65440701c0c4083c42c0001071704031001f078000f01b40d00c0e96050440c0920103401600716610050150307004000001640c041056408201c590500300552249140400203600034014040e0705001080a04030030244544002e4886003a8081c2c010390390074002c08039214403c2e041418014201c21034440040015520990050b131023141307400381021468060b65107140d5101c41c282e00c84c400315807104c1c5013000780903980c41328440704010403802141b919180c003944585504101e80030354070989002c40001d8a031007000100c0c461840d481a01c0c680d5907030312085c00d154046128082c6500501c90040001d101810382a0328418540b03036400100513a101803030400018200d0841c3c4000395a8081c042400013440c0040240c00c0629088000c585030003c002401c42640701940c4a04003491112408402503600601202d140a804c103001064201d107505040d0301d00928009000e03000714000341000203101021841100b0480240c1e504004550344035035442c8500040f800c1541d11210402c240f0b00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 842697149 1250 842695899 842695943
    0xe0a030b070201091401050601030c0908070b0a21020d0c08091c210507022a0d02010323190b0303040e09010b0307120201020d08090d032406050711030604 68
    0x103030004003880045444e071611342c1d400203102c22554a03981c4507034465050100381d40c0c06001d0ba441101c02450034200840c503000c030040e62000356100c1c01418160000e1a02d03926445154942240180d01156401c070001407a83e05000350703c0131151540c101d01d401710840e016441500114001c4001500800c1483e25066040d00b240202c20480e9003030015050343d41e00c44020b0200f8214030500c40541c0001e151034103080282c104015000c403004250205d119440c0311100b81d490351a0b440c1d40949544400d03000610040e0000c05040c0f4900814030140d4240e1250300189403520384c414640701c110202c0e0101d2218551003501c40301d10f030309070340b5400501040c0814000708030402d901031103003000410138410100209003400b4603900315885000c940c1d005503040d960100f2120301c041c0f410b8075001c489840d000f03942c1d41c2c131000002c080400b09602c0301120340c903000343e8107001040340d1154520f030383c5010795510024140341d110242c11942061203030504440d0707140200701030384500d8000005414221700148115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 842698399 1250 842697149 842697151
    0x705070b0606160605060a0e09031213020604081b0102071404021602120f010e0a2301060306060b0703022b080406020c030316030f0c09050d0335070e0a030b 69
    0x250440b00910800f01803420301c00c40d60b90498080d80d0300140604041040c030400b8141134210300011003c40080c84a1000000f044503a100c10301034010340c00b900c3d034400c59118100d480c44040d504c04008500890400c0000c10317034110a0120301501020075440d0700c0103a8481001d40f0506403500d1075000980c0300c80c105034000300300c651162001c800341c02c0e5095000513100701c40c101007861568040e0424846105091094040c01441c1c0c00080407142030507a20710b0120004920380c0303c424807405280c0200341c642500100b02540e40078009024090700c9215070b082c2c07a04904030580061150102481c281d24811072183c29407410303101c02c007e004e40107600a58500c1c101074401c540c1c0340c0e420001003458030000c2c0007640c0202065103440860420352035000f019210103000511100c0d142c410000070840c0c002078141d040324010380d0016007203016410306649030740f03140c050810345052441240a140240e0442d8003603890740000304a040c0d880d0f246044070b03894418015030b504101c8079002840411007680e015 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 842699649 1250 842698399 842698411
    0x5190e0c0a1101021818040c090c110109030f09090e0304090e0708100605040e190201080a150f2409060e060c15010f1403030912070e0f010f05090705070b 68
    0x802c0030984a0301c51542241d0003031a2031707880e040030340b0351500b03003850300c8a503038150951408a503003070505180d110340703254600074030800d080140d48020031000c0500614044210745104c2c8002c1220380d0302414060404a4800c00c02000506120b80c0410105814803d030544100d030000190300342403c10080301c004003280324007441c8034441d10000086051040003090300400323413060301151051800c2d0901c03042ea11031881001c0581c01210710a000c0c0428280c1c14004290240f0f00b0f00301c651903580b4210002e1940030304bc5180d020301074101040502040000500700e5003002400e8500c00910030481d51009002c0c0d1a040c00612845c2041000c18426131000d032038048001c0c0f90304e140c8000d40b03070014a400142840894800b510200400800b54901003036801080c9130003003d4110302d00000020789a22541001038418040d10b01c206c0b20102c01081100c0c00b5100000201c101303403d041080450740602440fa02280d4035225001154034200507030b00c0c0e4020b0506888590911815603035803019420b005000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 842700899 1250 842699649 842699657
    0x203070302060a0f09090603030816030b06180907091203050f0d0e0a020f06040f1e0503070e090d030b0a060818010c090602070e0c0715060503061005190e0c0a 70
    0x1011026988031402014840540c0d1541ca0001302280b0001e40040b11381d0784010301051500390108003090b0070400c030303c0d44141c03120ba00704035201e003403101a0001c00608108680000012032044104504400391080c42401241e00c7c815558440c41d08a6039171101d406801d2207805901e203000300207401031024203000754002000c40d00f095103281c4820100c0360702d000c00c1d102c81d5001c10030030815400d03c40e42c3d02c1d0410b0342c1038541615003410402104a40b1a080c030910813414411080303040b0000803204184090f00f401402d80300960365418001c505158140d422100c0e501030040b06959450282c481c01d00a202d000e4200440359190000c1520343c240000c00c8110100e0140951180100003840b891800345c0258562a07581810984001c0ca084001d0b040819911480340621560300610707400d484680340c1c0403030300010f8100c08464100240c41c40d030340001c0e014407845091109141c0e42c201e40c201511403e0fa40c0701414650101d80b081c00d80510f00c6880b0422400c1c40120320400f00c1c4400034184d40c4110300f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 842702149 1250 842700899 842700913
    0x609060a0e03100603210504140612040b0601260601050307020a05060103030f090e010b071e08030c041703191b17120907080d0503040f08030901050103030909020c03160203 76
    0x1000c20b00b4210088030f01460310307642e600309104001c00140c440340f0301140441c12400a000003c4064501c0c400c6014111200c0711082d4100d20594a500840c0e00000f010540184141454500206800d00a462040c08180c0001403e00028480c101003a49080c00e1181180107868038001524030794400340404046019101314140880d104000d030038001c51007030760740340c11000c2d50f0103000f090784469402000c202900440104075813519442039a030040d402201501c41040841c214240c44011410000c040301008400c10240790350322006007088071107890040c2011080300c0242504c901c100010103400844130000075440304c0c80381546441c1e110014466083c00c9507591900b20304040880b03884459010001505155201b1407079805030400780703140c024036040f410800764944030030b2106100c0341004400700005050213110100d528000307402c80c071101c0c0d680c242031070050f000c0c2109000a03000700c0c81c60307440010800c0d8607100300c0b1224a280c102842c1010b010b6541121010503c03141643d262040607 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 842703399 1250 842702149 842702177
    0x512031909030f02010b0f0f0f0d0c0e010614090919060911030411010c08040e04050309040504080909060306150d0501061d0412020309010c06020d09050d0203270609060a 75
    0x11040301c00c12030080e00c0c2c42e1204220f42800078203490b03085104601501d011403503154203840e0300400400102040702e40b0100710300c0c60340c08151015095900904007440901001a4519040d240d035070690b06181d85480155641102030b601c64405d1040550300038003044d0001d00319035a0001002403250380f203140400d80555502c0e0400c2514207898410041510010600081290110105030170400a00b4440307618081521a0001c2d4007451041c1502c01800700000f4081010900499143c080000d00c20000c1e030500e420407a2503500480005400740c9021008950310340f03400100b15100d50b0740395011080700710821062011440c41c01008070b40940d00d4040218003580c041c98041c41e00e010072404050245801e042000008207075a03260425034104000c0c0c0d00b201d0343d0102a480110742c10070405662803120b0666500146601030380a0480d000319800ba40d9441e03400700045c05e02e03001401103950380540d03419031881c07140741507040303103900c04001c00c815110350500e6406442d9088040c00c0005c4140d4980d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 842704649 1250 842703399 842703401
    0x903051821010f0b030a080702060a020f0115150305010b1903060b071a070305063d02011d1f0507020a0f0b07110f10051008010f0506091305120319 65
    0x10741c140202d9440300c07001c03041c0a03100e100d500030030b860032401030041800030b4641406520454101070b02903170f07000034000c4001c0c1c002c010341c840780380301c0c0c1c00200018104100c044124011034010003c18a8101070b0060380a442409002c0c1601c2203042400e140c0010003000351000490a1000c0c003d168407080001000d8071144003500780c030740c05009000500c1c450030407003c46600e0000e160348285032a03c4240b0826884070340c20030060030300082c910000f0440c180743c4070300d0600d071240c1c48040302c0b001054030700342d042d90640000480141c01450501c4292400514a4840400b00c8001905107003405001d00c40070303d203410440d0061024010b44020040c1d6894a001c2c4091032903090700c90749494000d00504984c00440b08a140990314007a01c042c52900c1a030a840e41c540c031000001d22502c3d000800c0041c902400510000c010740c800030408501da000c0090040d200455200c2d1260304004000380e101144030a80c90034140c2e003c80070340615400f09280c1420303074002500205c040d60101c60300e00952040f03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 842705899 1250 842704649 842704699
    0x50903060c03190e16151205040804080f010b030610060e0904170a02030a0f0503151201290a0803030f0f07050f040e15040b030d030f0207052a0409030518 68
    0x4690161074005440c45c1013000710480390344070307901103445030943c20f41c20343d070003138005184500e44403022640c0d407541c1c14045680e02441e0007150850044440711045840c0547c81400b5031082641a03440e6035035403292800c0b80f825184110008181894104c510754613104060681c068454403020000c0c95000e410070704150440701c0d0001c0903038400240b4401c0241c102c07080b0101d05009282180c610f19250740c00c4a000f420001001e0701800c0800d142c000304550a41003941c00700440650201d1700c00d402c0c00c50420700c440741089240608407444021904100c0030080b40d1084880c0d0028204c1500c0781820f0050704800186041c0400074203003e40c00f03888011000500040c10841079844643c18800c500d020b119902816540c80ba52504a030180b2a0318040340c0342c1da80d00294180007541c1a69240340b071008e8403651000610501985015503444001c1c00d9410301401c0c0d100c0459500d000d035540510040344d01400018011440078400007402c3d06840d514040380c1000500a00d1280d10307400890004102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 842707149 1250 842705899 842705921
    0x30d020c0708010c11010509030a0c060e0c030613020f0616030f260f09071809020114040803120106030905061b090d0c05040c05090901050108040c1e03020f01050903060c0319 77
    0x1320308a10305403105c02400740c1e03908540050041d40c949105014054000320035510001d01c02500c1d5400c00f14601400d20650750b0100e400742c26201d040c81d240d126054030a4200704100d00c295403043c9916000d05000d803c0d43c5402003400580080000c840e2000e07034071008100710510802c84c54482c01ca64000030712121500c8000c1510a00395141004c1c17070a0200420014111603846d40107140401c10800310720612041c1c4250745100042640703803030004990710700d000c10040041000001f80015202d00c0003005110b0720711000d403d10710f42e0341c0703d910840c2070b555418000b90540d0300070000705100840119001410342620100c241c80d000c0d402c00451181811298150340c07412483d04100a2070a29001d0248400041d00d0000d250040c5a000a01d88070302c1070044038100a8a100007500308200c1c01c921101510294140c0c0c80e5541100e4090241031003030707000890103500111301140d0381b94001d00a980240c940100500780e5555682142070240d04020402d10305090003501e80b0f0f112695502c10703008028 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 842708399 1250 842707149 842707157
    0xe1b040803031e06240c01020c0d030c021906020a031e0e16030507090b0103090813050f0618040e1c02071d010807090b030a080309161502030d020c0708010c 69
    0x115043ca266054101d2603021040c1e4074003800c0801401d03650300b5a0580c811001a42c0d500c1d00800354003d0b00b80a80a441c000c0e045940c80018440c5846400040c1d01c80300c265161f13814424290b04131000c036210680002c00b135100c1c08502002600044064000d491161181e1030001450050064440c921a0744a0001c1c5c288555403403001010081c14071039407841d0f51681c1a00c41686186907603041e92140a84286582150384021080c0d01e43c0c481c0c0c10481030340386c01186264031062035080803c3d24404e24442d15205002d01c128003011800c1850a66100045080f10103512002080500c405071080c444c5281c054080c034501705400c882c80c42c008046014969000301005420660704215001d15911400c803184400740c010010108002403800c1a6040e826020610010341d00209281682c4140300503c1280c000c410841c8040300010020f400e00c4a1322120300485a03550440e40c09030152a520345d0050300100f00602183c401a0010a002e070110b02c00c603148148e444202c2421120316440c200002 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 842709649 1250 842708399 842708401
    0x506072402180907050415030b030a1712060306060a051c0b0112150213060c050c0307060e09070c02060a0c020d05030a02060403080f0112020f06070b0a0b1314010e1b04080303 77
    0x14140f8849141e03001e10f00e0300f0110f140c01d0a00b0244041b5100f811502c404254941ea00720140d030328148141c409803035114400c10450030548142804e1604000180d03241c00c6c01034000100e15180020b00a806814041c1c10001454244014882c0c0f8101c01020702041a412007180c1c00004d0444403024005c1007410342512400845241880d80080c1a44001c034416006004104000d00704007403002c210f0b2110b040c02003271841c1c0c0b80340071810f103500755031001d9050081070340c0060703010b800c0401441c014004407502c07440ea81d40d05c03006966118840070080d402c1013044c00f11100d11030080c02410b80003030005008010b117407a642c0e212451a031082c0001d500581006050108050304100b600b600b10094a02500f01503051a405030302042c20048040d02c20700107049140c0c103d840311406c0328440f58000039250300904e8840c0c011005060050322a84c05030840340d0b2900c40f403241c20f200384000c80c1d03102c9000b000c035030b481d020100c50300000140100ca40c080d412040b0b484400daa0000074001054000061078032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 842710899 1250 842709649 842709697
    0x9010f0602010614150703090e0408030a1d07091104051909111602010806060904020a080910110919050a080c01081b030a1a0d03081801060506072402 66
    0x83d41c10507840b14a010544d182c02c02c04d25a544840306080d200f01c100090b44032040750400b1a60011254401107900c48160280f1050244c900000c510400b048031050161170030440c03811008a03100c08208500350031841091010884036040078507003410034209503040a85400020710b0340709410b08182c0900080034001c000e500c280f0b014150300d00e1250a00b803414000f003000e040c10072120805e0300074100304071400010170342c2c3c0e118000e540d080c00e40500110b460303820030500913014984c15520000244605c519052204626009142d07100f0980201c080c2011852000e000c22456100360074000302c0c40384000400c6170717150148840e0040000000070046d41c036806002400c4614082d0441018031b00d101e4800300b8020340e00080b241c00041c0013000148440c1261952510007800741181940480c0c5030302a1414140d201100500800d44a24800b2403030031803840039402c1711007034869240c01c01c806000318004501500b000282030b50101a11450355940d80d06014203d0703120100580e03a4460080480784 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 842712149 1250 842710899 842710901
    0x1008030d050a0b091b1e030f09060108031c1e1401060f0f080114040b1c210f120e191a040503030a09020a0521250905070e09010f060201 60
    0x10780f01d0054031202041c2c10440d0f00c44038140d25002c45a60150800500940d20034000340384081c508400310542c0d80c5a08000c2070b117060814058500050900c640d100100b40380038040300702c541c0c03d201c1c20107064010f54101c503814040e082c4210b0b58a041100b03600551024441e030700034840c2844480c0200110756050103805000030b44211452020018101044442a81c1040c003450550340000d00581d584546900007030058407006403c4c581100e070b078103c220285d600d4540d10290983c4030f40b043d6a0040300c1e00841d003030071a03684180040003456442152070514000c410740b8802010202002c40c2d00422105114a4069805000100340111401000902c412070b446041d1700c0860307810501c6541015160345a0f00d0001402601e0015601d154180865440c030a4890090101801150a018000184100c031120012000c8c4480c05081c01d5101004155058810348501004034062a2420803200400034003001304039109024500d184400301e036980c01d038614002c00344145560001401c1800080c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 842713399 1250 842712149 842712161
    0x1710150501080f0103051f1514010f050c1e150907050f031c0f02030408060901060e0f070206040609291008030a1409010306210204060b030903070b1008030d050a 71
    0x51402e0f800041c0b0015001060001c151290240c03510b5940609a5441c1e005001f49203068100001c0c0c000c0006403a0349844c00345481030026281d040c454100418203070340911034180c0542c0d950300724a204800c07480030b5690440c4d19400c3d0401b1280410351a2950300b0550f40b0641700074031a9804003d04001034900700903030402c6070301c2c15000350465880442600400200408221090203d91542214120310070401c0d58000c000700d900b10f42c084d0034140c607540d0092945004442400d42800d001400101019400e640a41ca669004010568403622490001c02d00311000320b0f0341e03048070034045103850384007040d08205000b009541011810041009000c041d1982d0125190740c01c1030042244581d0401898500c01d030300f08440564031151140101c00408080c0c2240c81d06d03068441e421480030801b4986980040e00c00c1d10200061600c4000c1100c16010807121440d856008100d0320000658650090b038012900304080c240c0c1da601c1d00b12032425038211031030325100c036680c60040000142d5180030341 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 842714649 1250 842713399 842713411
    0x5090a0e0607030b15040603050a0b030a050714010309080301062006060f0d021215040314181e03120a020601051e06030c041a0c0d020d09171015050108 67
    0x810203100c0d5030194980314407009240c01d05069a840d40740000343c4503000444144042161001d0703445458520150003000140d5012002c107203007018a8903035050003d51000d280d9009001051200d00c0c2c1005400100c0342104103504164a1341142400142c1d040d019501034521a100c06035441410b1584159064000e00c4001c4164003c2044c00801e803140c015103488003070261034482204a03503002090100340030344c0491500d48a580c00e007100c002200c1c61224080c074403d95803081109098004000140181c42c8140a03911205076000c0031458508401c03e0300321a0b01c0620403082030031900003400c0100f901c3e00c0a40c00840001d46520250b0705201c0b05000d003904803074480354503c200c00303a040500841d080860207001c00101251039003200c0c0054070001d05203801c55620108030100400340030f40012030703800080d10444e12000c100314004140d00c420b00100e030741c07903c1010b8540101040710074010130707410b005401122400c000318881401030010488220b800010320b5498440010b0000200a2070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 842715899 1250 842714649 842714651
    0x702030622051c0201150506090d0807080d1e060b030109050403021c090f0902120412091e051f23041a12090706170a0e03030a05070e030c1c240605090a 67
    0x811f120f20ba51b80e4082d5184040709441c910070b15a9680b4040c1d040344100700d4050600b04012030344903d050401c0e0000d4030b810145e1a070302141c0a20728004102070300c016000b10544964103000501c8810700d264406a8064013920403982c48040c40c0c000e4a1500700302c141c1d1500002e00e0340b0814404002c41d4880b000040245000451820401d5000440381680c0940002d000030700103000c0800403445420301d50b01800005298840240708200d03079208a076000c0c801e040c0500d207004580004858107502c0c0e29452002c1e601c40c040c0030440e400c080768014441c0c4001c00c1511100b0300c00404c3d6000e10344100d24040051115590741d4890125010307104010040c40401380d030740000802d002c80c5511000d01c1046002c00b01404820b522402c0701000500746802d0b4062840c44003000b04044010b054111501444054482402c2c0c006030344141625440a0121160018422038000641008290a8070405800b40f151240c175001c00c1c404560310200d0284080300002e45444042c4403e246c400d490079048484100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 842717149 1250 842715899 842715941
    0x2f0423040e010f0e0a030912210e09060f21010609020c03040503010e0d0215061c030807080105150405150f040602070305010b0d0f0b1902030711120702030622051c0201 74
    0x41c0007081c1c00404d0003039030040482014a58104010b009c84d00310382880b40343e6a0000c000c44550000e000060408880344100c1168020a403541007501c000e4040410140c0300101400304401c1004806950041d56401c665941800081103800c520140004c0e031303051001746036038034a8070b0101420b4404402240040313400010400303080a40000703100320440b00c200f1640c001e55840304002f8140c0f64400303800d0021015181034400402d984190010b200303a00c00d49801c0504d0f43c80d034050101045141400b5482400e0402c01401a884c01c44a80c404200109601d28540150034800550707540050f031248025900c00700d02402008000e004805203601d0030784030044090340c95121038034626000300c8041c00002d80100070407040c2c81009040c1d0010384500e041507540b0b040c0300d1340c01031411282e800ea000060255030481e0500d216400c080ba4502d81c0c00500914040d151000700c0d00d0400300c0c2c0b40c07003400212840c5400e41c001500a201035150740b5600855801d8480040030040d0a48042544481c0540105c203 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 842718399 1250 842717149 842717153
    0x30b01050306101e03080a09030614061c0f0f0b101d0109020703030b0a0e06040606020105010302150a202805120c03090904062f0423040e010f0e0a 65
    0xd00e42c0022501034513091803160391000004210346540340c0020700600000035043e100355403c0001001100e11801d0200101621450b00303140c1004140c42150b40065403800e00ca03c442d48100ac00065280200140300e907080480da600004080200003c030b890b4002d1030201301003001d040d001c090061080c140c01c0c02002c642100c2e82d030040a0b05000b56182c465011500380b00345032003540f15166400000e083c040c441c43d01d4040e109900c1d8021208240b1071400d110000c101c0603c1070051504072640900801c50080c41c0f01180d61240c1c011041401c2048000004005c0c680b41040000410b0203408000d00202140c0581250070707602d442ca0891031808903102107500040c00020b0200c50b4420380c0c0320f016120100c80620310b04500c114420640c1c0048074206000c180a400d0307108a51007030000120500ca803c07800344c2d505168910060000c24100244402c01941d00b0600b5110300c4c0c88814009140607800e01ca001a0031151050241e03a8969910401c81a01d0881b078072513618090058002041034900035 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 842719649 1250 842718399 842718421
    0x30a0b0a0e150c030a0603050105130512090d0b040204140c0309010b040b0105190201020c01060602160504051308070807020414040b010806060d140705370b09100e1207030b01050306 80
    0x342c00a6661400040020b05d1100a540014060346c0d0000003804607082c004401c010342d00c699442501c6038001e10710715600c101402411101e102c000036041b5110713515140c450050640c0d0003041683c0240d03d40300c202c005c0300224500300f0310a20251409980700c0c20941030f06404c541908031290b02507445c10f4191a226070f0080c1c240e03200380041c0e180f0300740c00d0401d034542240640101d13080b4940e0382d82880c10206003da000f00d90550886202e202140003159203d00b04000e542d0113444440f1516908018000459581801400780d43d010b480c050b464108154081001c13210450711018150082d80d0601081000040c881c3c1e00400d1031744002d000030f04003d00003900a0800c510f000f03028a0000f6442c40038282d040c84407000425000f030001c840322100e8901c0d450400c40ca00d075201494494060704241425140d840300094030100341c409424240c0c210700307200c18603a42c0c080f10024041e40e1202c007000c81e91202050102d0640581c080c141b064518580480d4500040e00001d11a4000908100d020502c0c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 842720899 1250 842719649 842719651
    0xb0306040f020906360a0c35040303021804290f090c12070c03140904021b1b03010e060a0519060602070e16020a20030a0b0a0e15 57
    0x4807030014542c0c0710340c800542490705410401c1c1c883d50a04014800381744015042d810202c0c54458843d80c0c0382e940350703810303c101c80000f40001c0100e000440c0c485101c8220f13180d219041c50a01240784c415000b6074280769a212001c4030101d0000c0e400282c102e134030300040c021161103004261414400016507107011000d51404c00140c2c40314100e80860410700b0b6503001d150079504140a00700c0c102c6428107056150b90781c0c6c08503000000b80c2401d1000b29100a00c210302c641b815a4159480550342d03003074031011804a901040310381e0b51140e001d00be171414807101a86401c00003001200104030202680d0315121008102d41c1e0260720030392415410950400000c545150310120b03e540c0011290342d0500c10211810172031903d100c40031f180c20b202080e007030380007d8060150f071411810103440e9502c00748a6034050600a14100040c0c01150715400050200c4018801514494030010550700c40078003ca880c1c0100c5003025240c0704550003d00480783c2040c45910750100460f000323400401c0031880d0808603088 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 842722149 1250 842720899 842720903
    0x180801022217150a0b060f0309070807030c060f1e020c0111030906071b1206060608162708030a050711040b180402130501091b020f0709020706090503040b0307030b0306040f 76
    0x9150001d1300f4101a0352020b030703880d02c004001c1d81d182d07202c0c6143d02c4015007007200d001c1e085100f0310701d001c980035100180c088220380d845140040301c1030074000101c070301b401000d02131014400da0003524100b0780c80000241850058035401400aa00200001040b4160310800c055950700104907020042d1181400c0343d21107500603d88010400b5035a0069122440036070180340c0201500e480310040003044d410a80480304180d440b860640c4030743d540d101c00106040042780100700300400c0c0e030014100d2480d6501105100c0c20201240d95070b2480214290707440b00104000103440001d08004100d00201c42c0003006109079010032410f09003c000c2440340100010140c5400c01030030004045554401d80f04210590418050005503991300281c03025004030132686c08140030126902415038400640781e03201c024208010690985800b41000c000d5008060554850b81c543c001007000c01c500f00010300041002e10301d0550303640b40c6080c1c004c4c12120260340051094201909110115840041c5504615 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 842723399 1250 842722149 842722183
    0x906090302061309060605131a1801032c06090102044b0311011103041e090c080612150c1c0603060b040c0503040c0303180801022217 59
    0x4048010a000340d801c1e611581307080e814564040f80859010000d0141140004400340c840d030b45441c445a11802c004200b00c1044074148010f0442c0c00c5070115048030600d06060020310b4115513400c522446000d502c1050003003103546004040d032102008000c1d030081806000310709003406c0c1048082d50f8004d00a40318400500941040150341640400c3d014440b840074500201c42403420350204a191280320039100801c03103001c1d0f100b141d4054414500b00c091400040c41c942800c0514810142000300402e41d00751140400c0440d6005680c0700300315881480d40c80d03440c0e45103864070820001444040c400c0c0b102e40c010b0030100b40d12008024401c0d0300034942e040429207445800818489103400840c80d401060308014002091045590182c40c0c000c1e001d5a06020a4102460585080c4416200100079131400344003000802d10441c103102c1120004203a071190556079480702c03820b9800540140700c4075400c01c0030307240040c038040058000402c01108610009881c3e20f002036103d40320341710707202d41c90 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 842724649 1250 842723399 842723407
    0x3070608221b0807051c0c0e0a1112040606050a080714012604060f110f07050c060a080f100b03060103050a150b210c18011b030c12090609030206 64
    0x72060840c648240d0700c0b12120702203056500c1404650f91141031044c140654180c01400b1400000704410540c0290004240b018042c80c02c448080d00c240700600b07200034150341d40366000780414800001c000c24043e410600b041428a41401c41c11075280d680030303070321401e2403007810000360074041941011501c80200e090800d130458001070364448526200302c180c0150008540c0d4190044440e4036028a024034001c00112941030705890440340c40c01c0b41c075400c0000034048041c1214124000b481044d100758103071001a03200d01c0c04102c60b0742100c004080865003010402c001c03d45401200e6502500d80008181880e140c030f031040b08107100c040c214504241d1204001000a10030383c000c04043e100307280021403099035600c907001b4035401048003207245841c4500820380c0c00b0b02c4100322030701541c1c1400b403203460030078540c03409402c034050102d20505001c04031070340c10340c0e0f4108034076107000b02406a100c5003090203a0380f03007a4811080702c0750044248218200e050150f207034859400c105480d0b040d2641e582c0c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 842725899 1250 842724649 842724653
    0x7060513030f050a210203090f0309061813230702010b0607020915090c0c0f010b0a0e0a0e0601141f0e0d17030c1e0301030f060506180708060307060822 67
    0x2825003921703040031407084500b01e0594040d80950003148220101015113904206070828a41c80e4420403140e00ea1041041c41008249160300104c1105600014810b1400b841c07841081c3c0181c50824402d09450301c00ca07802210402c4a03004040d034403282034402003020f41324040014009020300940130303000c2c40c6600006541202c074160310490100000740308a400e4a030100302d00700e15030304c4682520014003e010380310f62111014040d8a000079801130104621074100302200b0810305004045003200b070f031900700d0f00000000901006000c2e107a0310180880e41c0c5002c205020b4a004480500301e0144010011111a294459030300074011008481d4204181075506107180d00c0d02c03c0740d81c040d42c00c50001060010814490340100b400c000f07079840100c1c4112107100c250016010034480a0f11a0060320520000601d142d4440c940c00080204950000c88000e85000301c1035034100c0f080800b18022205006c041c2c074081208000030141032510f0002d9203018403d10510003004041c04c51100c00756908442 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 842727149 1250 842725899 842725907
    0x310060b04030b1314030c011a030601090b0607120503060411030f04140c0402030a090317100513140a09110415120618030c030807080624130b07060513030f050a 71
    0x11320358100d1a0849082c41c0064059180e40c4081002c051642c0380400005a41c0039020003642c1e468401006071105a10781403151014005544946034045020440e51001411400040d00440c480d40e54668603031a0800034841154803800103405140418410000800360304d0f0317030040d441540011000c00d01541c0f1440d82d0325107a03060580e03a50103400881000700d50b001e40d03401009087c0c003c0d40ca0822642c1c0d1814103102512060302c0380f4030f409180042c01d10083c01c05254080b901d80e04941c001032a0054125500790b50300e000d072090800c2a48a031808030034013140900070a14088200c07020415409106010707000f0003103901c507190700300002c501e00b182484400c0e0b0045042c40494402010780c80c100c2c2c503005028050f440d0b000c5000ca2600700c0824825481107040d00d2160340301034080080340d51a000c460071030030340001101219150803c101204404c0031214000141a0b00342c80c0c42c0c460b50345150104c01c0c0c1c4d0004100321056240b000170710700405d900c5041c040c0c1428140c240b140d40c82c19000d400312 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 842728399 1250 842727149 842727181
    0x50735010204180203040210050a0c030e031c1215060c0615091806181a1801110c010b0306090c12010f02070b06010315080303010b1c1503020310060b04030b 69
    0x9004016030920f00e0320354003580e0b0002c0d84a0741c400c4501d0f840d8070180310019605030047d1120b0400041a100c845030000703000346641d03908010007d040f520300704040c2d418115813451401074a000148610340d881c070a85042c4c05109262179108200448203414500028240d0514403005400181c841001071019a101d10f00a80941001441030081c414400d03142c00c402c01c000002101c1d403500d000c104990103014540c10002040d440340c2004006e000e102003001070848003034400c8008800c0035500211009091192300d0181042c10b0000340c517403e04244c0c89085841c284140303402604008100241800080344d0706603500c804070340c00c04600b00084200c034010a0f034a001001910300c0011954144850709040038803640c000d9030b0500ca4001c1044030703065204024440c03401f4980c0700780014014003048801602a41c500b000320342d6408403580924405031140d6495200100c810828248150f06081c8200b045840308800140281c614041c1c0d20182c5104520003e0b01c0040d0719800300300341d403403003070100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 842729649 1250 842728399 842728409
    0x11d090c0a0e031c080a06151d0405180c0619030c140307050d06120c06030f0b0319141606050d02210f010602010902090606090a0e13050735010204 65
    0x144c0240d44903860001080641d00c4440000c01e19620004000c1c6d0501d00505c0142d612202c00c180d80030301c0c00103003650200b4010070340b20b41c524000e000c0e48030b041c0c0b030761b102c7c80d4444c42d03080310b0501080c501650140c0c10101640c40040c0101000c201d0300f01c1e5454104164056600305180014015860040446000b0b1007840b54140ca0417002050244141c0c0c01006031000c3c240f10b803010048140c8d90b000c074400c0041501001400c124281d902007201c90300a501c01d48071480300441c0450720b501981c0002e030508a03541d901a1140e6581c54103201809110710790940c4200c40f6000a2100c07072001c1d20300700360440b25882110100200010714805401c0c07580c058a045807005002e2007150904c4010507160148100c0300c0680c4040303140d000041b06441405080343c180d4010b031101c0303495225007042c4041035000b42c2e01c1907006102c85c0b200244030841e50000034030401102d18001c0040c0484d00e4400d0034200d055004100516052946803280c20320345007048400b003544034400d40c460341001d003c14003a000701d500c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 842730899 1250 842729649 842729653
    0x271a120a0c020d0903030824131a0604030507030f02010923010f05090d0308100f08030c0f0114010504023117070609150507020409080702011d090c0a0e03 68
    0x9114428210750080341c00350300340303409441c0d21020030802150345801600c8098001000000801c1c02c1103a01c0b005c2501300a548000c0700c0341e50f0241c1d40441c000112020100e60115900d07000c2d44c40c4948120303455412102c04035460ba00d41450344d110300342e0751f000c2800301a15000b000c2f002d4000310380c02201c40c0d10003401c60000c0c644074001c02d42d003045221412088140e01150b60680045c8109203d48200d90b6030240042c08110340102503141214182d400030700303c5d60036115070b00001c16914040d030840c600509142c80156603a840f005042410301d0301c2d9030001c507840c1c1c0c1031081c03079000400405142415a80c00b03841c0180c03542e0003091002c81c4c0060919200340f20555801e400c042124101607458199100307030303038418a17035103003200703c166030308142d00c42c1500140780181c05000c4d00003205c0308545030480c40d140090070000302d40c00107412912800411503401400040b150b003196004a20424541302811050360b00ca8501c00102c0e0441c2001811003000d024005000d44007c0d00a0030a240c0100780541 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 842732149 1250 842730899 842730901
    0x131b110115030f050c0904080a1d1507031e02060604051317040501021501050f010309020d050d0c020901050d0f060c020708060c041a03041518140105010501271a12 72
    0x100405802c220f00d0098a5500400c1d4640689007862503440f40200d501c1119107203800000401280c4003100d0409003114202e146541150035559800048001c070000b000041c1c1e1005189030140100100d0300304106e5403542000070402d100c0d0007081e00c0e07600c842e06880226541da0b0301c028002c3c0524075020014646c080041000500446503400340c0203552003a000c42d4102840c0507030145482409120b401d0740529a00310078102944242c020345041d9101500c001c0c411300c0e039561001d040500a50250780000c0501170000203615200038454010003040e280240c400340f00b510303902030b0218082d801403e410b0301d0340b040c440c205100b081440010100f14058403420306001c107014809a00034400d60b105021580c1059500c1c54850007140e0040b80d000030b401d0882070400070904040c1001d01c1d4200d074850100610140400d41031801030b56601170040001a40350304100015040e050034008690814149040e9500807482c0044c071030081d20a080d003500042c040741c803884102c501c2a0188014000c0c4144 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 842733399 1250 842732149 842732153
    0x120d0605041e0c030e0c150c0709051608012913060302180108010503071215020c0d091415030c070204110d0b060a0c080c2802131b11011503 62
    0x30349102c180400c1400344a00300703081d94100d0698001600b418101c4d085030740d6820552400040c5885e40030003079040c0600b001007030195241015940d9109480d513031b8480e42002042d2980240c00205161075080815165052140e548000001e12400150301c92640051011030382d2110142e421520290910410301a11000000c0c041d400c24038441000600300081d032050b640c05100c00c181030318800380040030020714024804205d40070080094038000070380414010700003000c0c0000c118030f1198800800002d99140c1c402070200780781c2d40c0400403c00504454180a42d154110001c1c003001209042d43c40b51550300303030044188076610000350311514000c201950b6507000da000c0c000000041000300003654456061055074400c805500c00001c00c0d802d14400080d160030040d1209051100846038800074008190b0990b01c0c00903010707010b0b1008142c0003c00c603d803200700d44204160a4105010703918100001c4280302c69018108003d20041040b4404001401d51001081104281c184543d0076600c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 842734649 1250 842733399 842733431
    0x18120d0b0109080705150a110601030c081b011b080405030303010e06090c0c060703090f05060a240f0b0307020a0623091b0f011106010b0301060e12120d060504 70
    0x8005803501050070304600103210306000c901c2404079580640001c10a011039406d60000707900803402603040c450380c0344507a944000d08001a42c0658846c140d40e04510707080c408803a18111002c501e05040307002001111080340d90000c1d8043c48034090b407d034100541150726119416004a8018641510002c000025089074805115005203825035984205440b02009110301e4402e4060503506503001a01080450b4401c1d8000c0010344d009412400e910040d82e5500c1b4288001910712045954a4100a03565481c074407080d801c04414140301600361a01d8401c0202c1c0d047c0c0b40d803144811f0038a0100014940500900c41c0c0f951060344000d0030065501003803051810300001e2030b208040314002c41c000640404001600c010f070080728200d0313480e4108501c2c01304007a0108020b200b504000c1c009154584002d000c00c02c55001e810440c0c03000303440b076042c8280100145845082c042c41102d080c0030f00c80842c01c000c12000c0f0001c8280d40c83d90ba42d40809441400030707001940c80160014904401c1265150f82 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 842735899 1250 842734649 842734661
    0x705030d1a060c030304080702060c0a060c20190303180501020c010b0901061b02210c090903040f0b09010c14010b01020c1210180f0b09060708010e18120d 68
    0xe00750741512030006a05114840c0601040d44180f50b20810100b008201d101001c1c00c1c83e81d100621440c82d00d40b414514a04155070403100320f440580700c80c88500210740014801151401c8803110382c0d5440100b811071039640e00344201ca00c80300c40b8846d40180500d84a0f03002142c0c3c4560f1408030034140e00c01481c0440c000e5000d1314041c00f00e9480c025884a003442c05404447c104c1c1e170569900100c0206c0510044505100060300f2a0700c5445410704030f244110078425800211841e4016051000403035013400414a4010020346454008110504c03200d001d401c403401c16186110222920342c64002d00503034008009106c09407404000d44060160303050305401c0400a20000c0e420b441a40501600b840210002109035166a400801c048000c1c0c4042d82d00a10740e00c07000394426040c14076a629601811608000c080e5a094048020080100030402001c1e0300301650f4540996591b00d0410942e0301e21a0180c84442d5010036400b00007014202008107048840a54100640d2103211900907801001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 842737149 1250 842735899 842735921
    0xd110402090409121202030c0306060a021c090f081203070809160906060e0d031e0311030a0203090d08150d0809030d05030a061e0504020f0f040609031103010b0102210705030d 77
    0x10f400c0c8150020001703d00a4070f00a20a0b03101d034500307688521041000c03a81040b0509021441540e042c100508100000c02c045010592241c03070b00076003840110b0030701c00441d42103038840d50b116484400324005102d045a50055151511000c5c640710f00c0c100a01344199207100c0015182800001302d03041d10f00380e000d60304648140e2241150410382c1021b02607240da0051019000c1551303420b140803d0b40007094182c40002c0c0b0b610700058102d07103000750000681c00c20755003c44020750110412200d800100095540c00b040c03400c1400040c5022140358500801c401b5815019480030b900e64010003030f0707890659940000080958000710300502c001170441c1c0003129100c10081c10520b0010f0364410320000310443c3e4014140560506041070148400b03540401012800484100641f01020303544001600103008070340c0c2d030608402e156050410083c4080c012044c0710343d00d0301c2080507842c0c0c0c00180c01d00c0b20900030210104020200c10001c9014029010040d01d14000060103000302840b136802142000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 842738399 1250 842737149 842737157
    0x3020d030e06070c06050a020906030c0d051b04090c110109062702090a0209010519031b05121602120705011409060403050301060c0512040602010b15090d11040209040912 75
    0xc611641d03039540c15080e0303000000325403680c000c00c001c198603400c0b05503c11400c2101514080741d460225440340d0007254a0100700c40e02180900362060701d4001d9035000304651103184042000601610341500c654410040d003155a8218500824001c00c2d841c0d90700c0d1403602c0200300d0211b140c1081000b8000f110200c602c0e480030740245840c40f0300759200c401445034018200d00c21554801c10711000075071110b2140d07418440203100ca46074013004a40b012804c01c0075541c021403d01c04d0364107880c1074a0011a17060080c00700a1000b20508582a00c81c5613110b058101410200c400000d010382c20000c1c5030700040740240300012003406101054121a010551902103100d550b501c014030304e511408140c60090025034100010410541f044101d640890700400658000c1c40340030369813840b01d034460340c0001c0250351102c5002d040382c50142d80c81440341c056105054500b024010000f848040c1c1002e0090804c08081040042078a455050780e05410000c0c01c00c02040c1e00303034100911125040c01441c4005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 842739649 1250 842738399 842738411
    0xc021f1b0807200111131a0906160f08220905100e070908031809090a121b1205070b1003030801060806120d0e040608030304050303040219080a03020d03 67
    0x1280c4104181d5100760843d554038006081d210410340040200320305040c14a40d00c031107414440c0b41041004140c030044121010b4080b0380703080005411040c070b040d22503803602c0e424000c01900e070301c49100311001500c1c9080c800c45020308a140c264481811060041c2841e100850380040c9545048000a440c0030031040c220640d60748c40040c0001d594040700c070403c40c0042d1003030405c6040c400354695500b151203800c00000756a00d4051251840e04041d540b41c45a4540022820707407030070f10071045908201f1010151818600c151112103140c109200e100e820800302c0e41c841a00c0100320b0200d600301c0756100139900e208502603a0018a90342120f070040c1c640a6442e004241c1c00550704040104803640b603106d144541e843c1c060180c40561000381100d0f004034804103000d908040a00465480402036201c00b04611140f00501c8200c80e86508140d016910810070300001c2180001075941c841e0b4100d03400b201016542e407041c2c5023009a030340b01d40910304c41c803c00a82095004564141c9804250b43c0c20001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 842740899 1250 842739649 842739701
    0xb04060c050f07060e1c08071209030602130906050111150907051e180f060f040207020d1b050604081b0307050306010e1b040303050711030f150a0c0809030d0c021f 72
    0x1c20141b220020002d410410610000450513840300c842c9050314180260300660300c0e100c00c003d07a0710a0001c10908000000140500400e5106941c00ba120a1811001038010b1030141c941e143e0b110303400e000400101c000040c41e22281001044060078001d0b02e007902c2100c1000a54000207800352034170340715420b211750390042404045961840b0b82d0b440c80307100f0300c43e407540c105201045100480c180d0b0000c0e001c01500d000b503201d000b203050380d1900c5020090b440d1003029820054800140c0c204c20310429081000f00320507000094503048400540507881e00515281c4006407500031a43e0202e9010b0040400000e0003104a9050078800d10080d4048900c1c114400e4800c4d08500c42c502000b00425800d0041c0c0001c11250200c0c4003202c03001508030360000001140561030540d41e000d26141c980100d0003040300b4a9858080c460300c80d40c55003080906800c2144400d516800b07007600d5450a19600c9800003801132080040d8a9190311104175001144000089003020f40300340100305454070401181451 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 842742149 1250 842740899 842740939
    0x5010e0403020a030c0503090919050601050a1d030a061d071d04060f09060f0b0f030106030b0f0a090605010b0c010b190909050a17090111070b04060c050f07060e 71
    0x112881d4180d015000c00c0c40e0300c0d0b0301550071000b901010381c0c2c40e2000380325003540c0b511042c9485002d0425203030000c3d04811001244015604010841030420505101300721405030000008401c004002800060007440000440d10b8142802030180240d802d00c1112418480800810903809503104141c4503241d442e0b002c9035010425040a00c05003012010016000c6034991780300070380c111024400403403400c5850311840709694070000c440c41c2d0300c0e584003412122842c10450014000c0000d40c02480f5442c0b440c0c4600c03450010092198040701c0781c2d00d00003410101a58454003140341d0001c2e08100a5846581407401ea40207600c51440d03542c40c003981c17120140b81814001075144003020250a070b55091040e4034004d42102c5c007040703032144a4980d6410001d43c071100196855003040c03c80780c1d00d6070940e400040031043e0b00452003d850308042024008000c3c50b0089500390380e814140305440034140e160107460501c81103c8c2c81410300940d0f501041080c1c3c490b100450b0404103c070368850388001d1031803183e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 842743399 1250 842742149 842742151
    0x901091d040303020a020109051209041d030412051c0305011403060907090e070305100207020108010b16030e0f18010303200c0d06110409020309010513110d0c05060a110105010e 78
    0x160040c29100018001a200760020030800d1217520020a840c54150341e079501c1c16420400340c1100c000c001c55a54041d080c50702c96000000340e400300050380311070200c15540e120310450051000080c00a240361080c48400c000400c9210104c090440c000c841014004008140030b000d109181e08104654072020310f0000b421074042d0940d2170252980c1ca14154100700104840241c80741c2c43d00801c0000400b082d400d11144c401000031081c0566259a03600c001051110140c01007801004140049081c2d03400400c0512292a49420700c252000c5c000b074000344003d00380404440e8041400100390301c0b0851070095440c102ca201e030f12000b101030b52a40100310000c805041e004016400790002c0c10711480d0000700c81108a008020004401e500460745050580c01038111030788182d000411320000c20024400d0581c0034800c211841e4070743d5100c2c0d80b840c0c14007400240a6210b0b40e02c60a982d401e00000003641002000c0c0149183c0c1d44081c3c0090141800c15559102e2120794a814000105218007541213 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 842744649 1250 842743399 842743439
    0x41a0a09060c2f040f0f06050a121101140a05190302090102150c040e070903030e0f0609060c01060e130b0105030c150c030d110706390e060f090109 65
    0x148018403009a07003a1a20300514400403403548680b0b000d40c807030b500c9900c00d051740112188800b0601c2802061000d0646862350b02940c09189898001c004403005d61180a0803a580700018110f4a13882d080103c4426509005006211b90002031540181743c00c00d0080002e90601420300c08900c100850075012405004a45405030f0440e21065800380c03640d20841d5800f01d03003800503606083d202c083c1c55071042421550080811114071083c028541c201400760998013041b0740e950a10303051745001c100c0900402d21014011200401d030019004000e40142e4003600601c0d00c0f400c0b2502d0582520100340c40c0c451019100c0300174240c008190b50601141c08071014101030030100c5e448442181c581120b912102021045020031311100c01c0d2000180138142c1c0880d0582442916003645017824011a00000e0f4515115000e1a415403118800034032903218150001c19103000ad8000043e040c0d458078204111194088000607800c03541c006500c000d414145400c1c0e03240803070240c03036400100c00e0720081c03200 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 842745899 1250 842744649 842744663
    0x503012306152a0f011506050f09031006170313050d2d0c0914010504110c03040f1d130f060905030304051c14190302041a0a09060c 58
    0x582541082c0300c490784503061042c82c02e0310f03010400060810703588400310625540342d9003800303210441d401007145804189820000300f02a07848200120707007205062164609001011825105016407481a551606806001e0361020003420003c44000d0a013801207400c4480d60140000d0340d50000800d0380c405101000903001c01a04007010001e4201c0007800446040078070584031842c85080d191140c400d80880c403151041846a40b030088016120398005400a510300305941e401002c2403002c0c87d0441d5429100040d45119a2034844d0152141d006030030b240384000100091202c031a84162001c55100c80b149030724010030080c00156000c001d5400d07035010f000842c260030100307034420321707410700d544c490b48000859121680d1030303e0664104503819034007a00160250707043c800010b451480952094586070030240c6d40c0c2214031100d401120307491186201800c041041070f60080e41220043c103140c0c0c01c0e1024180d24058084143e511a00072040040d240f064005016401391048041003540005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 842747149 1250 842745899 842745901
    0x90f0608031602040603080d0e100212060108060402040f060914060301080303042d060b0901090c0f03021b2d0109020d0f03030615030b03070807030302060f13060f020405030123 78
    0x10b1400c4294090201664000d0307454800000003981500140f07403070712801c500440c40880c00710015090044d0354105250050040219001c1ca120801899a0100003400c02e030040d82c40f5640810024003c941180046000f180c901042550300803030440c04803604c025440d0005130001c020721072a8002841004550390084c004034000601d030a411501c50680e8210007044220010070160b4014400c42d4207444140c3d440d6007882190030014031080c0900850708060150607010300b4001c0024070745250240400d03501003016031202c1584003400c44260300150807070740b041e02140442480490040f00c2030080841e6005512180d20043c01529000d0707070001d01c42c0314031104545504140c461800c00450405603a1200031500b130010110000c1c01c80c0855800103540017880d0107051503e452030b0880200c0382e003c000300304002580021556031003541e2504181d4a6101c9030403400c3e24000c41c1c00300502c1c0c07500700003452a2080341c940c00341c0200c5800328000d1191410310121f440101e10070342d840620080604c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 842748399 1250 842747149 842747167
    0xa0504061d070c020405010b03250f051b0601080d12110f16050604060e0d0503010b0d02160b04050307060b101e020c040509101d06280e07090f060803 66
    0x4000030b580720072141405040203515a0000d822200b0036048208403090203c180002c854020202c030504102500ba09140703048200405840824080d03100410804000f800b8626031008003c0d00380500001811202196110749506840d1061904448005000c0a003140060050390141c2505402d1850390140b402a034015542d00c140e0005041f2505c40e1009120340000134420000d00384518001e441c00500c0d60303004041507091101c131000f51010000f0134401030045104081c2250b100300c030440401641c0b003070480c4200007120f00381c10000e4420700c440c600300024400040010540d1074840e440c1000746503180020054600d404240d808001074160742d00c0051182c4010b6100000700742801102e80e50203114000a06550044030449040e400c203040d0441d00300c1240c00340c010a500c10302035010405110f8540f890303965000401d81410300c080100860b0562015008824510212881c144000680813450300c1ea215128402d10b0125454204405402107543c41f85005803040040034514040c140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 842749649 1250 842748399 842748449
    0xe04021215160c050d0c05070b12061212190906170406110c0109150e070e0a18140303040c061b08130b04060809061005063001140a050406 61
    0x54044081400380b014040c00204204005c90004408a640c4c0d0a0f40d003031851608a05140c201da01030b15813004284070034800070904405c0d41d03a001106980f12948a0091500c151414a406101c4030380c2c10800907c3c0010850880c0881a0140030b9440b0015200d03512401290300c001034101c40c0d101c000c02176002c6400206503030091800310004c60003242c01c0000e48141c135400c65241020844100000e19050131281d40e00b4024501d049442c28040c0038014030381071070343d40ca200e1300a00c0c08038596954103d50300c41030b40c07040f1542c00341608009000c03000d03482e991070141d5035031050700c06403a1682031100000c0d0140c401c000009000f0250141d01c482545942e4075000300360000c030200c03100030700d158bc00032403e4007604004d48000c24855884e46101d0820b12100e50901c00041c2103a181d8040704081840741c4d0710b50008641c2d0354910a01903a10681ca0809803a1102146d410741c01c85110300140006070320700682e88145800c0707504640300381c52695a0000c000442c1c885110354039100310805041c400c0111a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 842750899 1250 842749649 842749681
    0x110a021f0e1908010f050702071203020a0f030c110f03191e030207060807030b01050f03060607020a03140f01020304020d030f050c0a120905030a02180711070e04021215 74
    0x1407424440400481c031000141c1c0344000048050201e400310800f040f20070401d01540c3c00b1943d41d2481003010f800c1550001307480d04440e00401700002c44140c0c035441014800c0007100340701d6070415074000c14203240f4640101700e4a0f000d8001e984840c8007107250019450261064010b40c00d0080040511070322010000404900b101015900d921941d0100c2c090841d100c00140d80344e41c444d60140640138200400a00b8520014050004040c50f02050000c666080300448a46085030304055450b0b69940f8001904c40c071030031000a4000120740400010800d010281c083c0c65041c610941e103030351898280706030803030204139001b0751700c107440a90800c040790103001c0101c0048131900c0c0461034040c0400b0b0892400703525503021070300401508100950560711900c2000903010071400f4100ba00c0301c51300050440d00010f8011817451090002060000b400b640180d441720782c8610585442039562051102004011541640201e0150b200242d11540108904455032081414140592541c90040b488004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 842752149 1250 842750899 842750959
    0x510021306020613140c060313021809120f1615060803090a0b0304050106030f0f170f07060b040f090c03020a050906130903141909050103060614030a0b0619110a02 72
    0x2240c51786d02c040e4640b00c000754440c003034201d405c6160f8240c03441400201411901550300c0160b0f040144141c089000c00e000300c4106420388480e44800c0da042c45a2030314460079802207a1950084030b650100455917945c403010703440c0361804000c000d503103000ba66100e1082c8240c01e644804c1d00703001400345a100001954100703018500002d01e4039225a01c0500114008000f640e0450000b40318a0030050342c3e205204030a0030509145042c00c0300310309840358902503400010510303a00c902d440152500d40d43c0c4400740386441000140403104c0310b401e10015520380e0b0301090380140544080406c20b03042c02c0720003601a03080a81810201c80c0305440d13600042112500440810917a90380075040f0504d0314000d002c1000845100b102c00a940d5203003e002c40d40a075010505040c20603400700718064204801e0042d00c040d203800c80d0380d20358983c0340003001031401c40340c80c640c030032030101d80c000280c09000302400420f0815212041c03554405080660344e100394100095000b600701305481d00074412036000e02c2c410a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 842753399 1250 842752149 842752153
    0xf07080c0c060a09080c0d030e040e0c22050a06060504061b1506060f0309260d0c0806030d170402060906090406060201270507060503090a051002130602061314 70
    0x2116800140320b581c09141d03d0740000b00140b1080c4280305040c401d40d400404111107d01140c1c08981c1d02410380c0005681c0c2c9441207503220501c03482c050003440b2100e00410024116101c21242c0040c1d001841c80d080004104d1500c0e000000c0d00103021881401d096030910303243c8904051030300d00120760243c506c110543c1c2401d045c0c1c40400020341d8070240240c022801001c0896043d09001c4000c0c04140c7c00403000c010182000c03521b001180071100c051042558950800d5003c0140049807489449104404a4044c2ca400018440503612814040c010041201030365400b074080b000071103035862298070300d03031215000c2d0b004540140f924000900d02804054034480c14003585100003811607a80d6440403026035103420300040c03800c907109048030b241520001203001e801e8054843e203581d030410740140400d0200000208590728070810240315602c1e03001044841c070001950028001c0d4005206030001440344020100d9840e0000c94094070900403103180301c20a00c0151100c640841f1450310081ca24 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 842754649 1250 842753399 842753413
    0x2060606160309090f06210b0c0d0e060c0c19120e0d02130e01050a23060409150903020d17070c030302040f0306090212010203070504090507030f0614030f030f07080c 73
    0x218015005d41c4040c1c0e80c0b00f50000034480d00e480d18005c00c000c010290100d04480c0030f00ca0340c00082c0c00c0398205030402e40c2d041c9036039201c122a080c110b009002c130700c0d940c9049210303503000c0048403420000101950b2080c0e505031120320307182005250080c8215a0002c00315a0303440c0900d41c203544503040c00984c075800142a540300400030703000324480c10b40e4041c0031070f03000d5110540c0e164592402d01810381c0000c000f1070104003044917641c440386400c203031400d880c02d204425008511507035516041160400e80104c2404907844107202c0742c1c8014006010203c002d070003000c0c990048a4007814104486040749280e54000b03668111044900441060302101890785c24000440c0c11a0040d0060340a184034a000041c090788500401030a0720320000b940d00319070300400400c418280d2001c280c07011908000c9000c15661510542074000d800e0700c0c10401142480c001000941c05070054446071a0041a01a51800401191001e07100d103c0c5081d86840700d64100b00c0d450001d5018030007824218803503411b41d098 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 842755899 1250 842754649 842754659
    0x20a0b010308070c0f06090501030e012301081507050316021e070602060c040f0501120e03160b060307030203120703110f030a09090209030d122c0d02060606160309 72
    0x194020070303001a1030295011805800700900005000040e0014829002c0c50501d000700041005589008150405458840740340e034150003504031008e10301c1c40801001a0424403103150740500b50912914066204100f940000e40808850301070043d400d030341d1294915075882c503102ca012a6041c184400b14421080c0e0b0411000ba04100d4071042c083e010060985d107840c3c400000c0c42c012001d080d800860310100400c04c04001c80c40c00000440c0d10030b08080e656a213001540c3c40050081001300105400001a800500b80180141c0c203251840b03102c007111161205000c1c141e40b40621b0000940651045014841030340c403c0002e045a14440d20f01200111000d80c3c1841c141700201d0b450364096071011800e012807541100058001e0500c0030021030400920400095440907011140424008524100d589078511a00804c0c10b8800049603081c003c11480c0c825180807611004c00310183c05031040c80d00d044e51002c1440d0340660300c0103080f28140300c03649150341001308500c141181804610080022 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 842757149 1250 842755899 842755913
    0x90c1203170612160906050621070912050d03060b07020d1527050f0d080c0d1b092409030803070c022101050703020a2c0a26030a0c060507020a 63
    0x3c820100e21340001c10040c5840d103070303505030b410701c0d00b145108a106100e502a1201052901a007120310b203142e0000e680c48070302054514444a03004945d603580380310903c40074060005813440208006039802c0000c0b0350395000346086e0f0700552800070351064942c2c80c003802103065403060701d022181031807000030fa00300d803142a003d80b0b11300440007510301c620101015044c00810300042c4424814800078040d04804200010001c3c05c008000d9445110003164900441000e0381c80307100c01c00e00c0030751441c0380443c80090203130440c9580e1152442412182020203107403001c50b40c066140da03015403070701544182165240c0c64260401020501040070040c3c902e030240c0e0300d0402a102d403070340c82a522100e03028042d0599003580c40c0240311600b40b5004010520501c0e9100d011006408820303030b10b2030400c0c01d01d990707004440c07840040c885502000014011980300f034a1540c40d41e1010f082030400402c600f1003500780b03890740074440d8143c02081c850501000880c0c2503801c07081c0d10246920550f1425030326035440030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 842758399 1250 842757149 842757163
    0x201050901210e06010e15010203030406090c1d1807050604050409060e19050c0a1d041505090c0f0d02060714120301090903021005060604091d0307030201090c1203170612 75
    0x205240c4c001c0004001c51800054841d0700f10b4003c0021400c040341d40d000207075991002030402040349940d0210601408a04080e1a01900c03c9400c07401c10b5140603940d0310070540c0140c50314a14000c040d04040044e00380090007004554006d0141800c05103844100402824241e00c2a07070f600c0c0d210040c85840200a2016520100382c1d0900400058170504002e40303005440c400c4580a10b042920078003100080caa0324500b0152260401075143e5524a8030036404000d6040c55004035040c0303418402003580c0410049000a8140c800d00e00039603c004c06c00500d2000d100029401c00e504020000c0864403808010b49810109011200c81541d074000d2408558400d03442a14215541c0111104040d8144104100d01601d1034003880340307080c0100000ca451181e0b04c984504650b60341c01c01c800301085041c64015481100060b00d450703403014280a800b0707043c1004116030300e1140b9000442e003800403500a003000c94150391780e083c4410350707010a030003000401760401e681700c6142c42100900e800100310503 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 842759649 1250 842758399 842758421
    0xd080a0b150a0302130b040515090301240501171005010f20070e010b030f0612160305030a020111040806161407031707020a051009112d0d020105090121 67
    0x165540c0d056804100c0c5c4902e5a0800241401c01700700411481e030b5000c4407c25200b641c4044581e580d40140b001a0042070504070b85142c0c47d1030794242c0c2c0301c0807840403009000c0740c0080c0c0301c281c9a0507840c19840030340d04044941e0b40c0b42042000007030003e548522040500103905040c446c95501031003081400310101108164843d521485d000e00803e002e0b4015a401040e40249150660a01e86203103500c125005042600582940e0314901c1400d07001c1050310b1014440070303113645465480e42801600c0b0f0b44030717100d01c03809503080404407540114918211800c407000c80d0080c00d49030311141d1200c8822540030540d41d040240c1b00310701004611501004040c0e42e80709803a0340039016007800513400ca018004140e6001d5400c1281e004011070404210500c0410017054005840c841500c1c2c110342108819020503004120b05501c15201000c03586201c0c02c04501e09070001c0784007400002c0010420307800c0d100031700041d405c2c00594038550007070036060111844400b0513140c90704d220340c0c01c40481d00030a0304 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 842760899 1250 842759649 842759651
    0xc081609120c05010f0c020f19180e1e0a080705030d050f070e120a1515080307060f150b13051017090102070807080708040302041401030b090d080a0b150a03 69
    0x403c0107a9a0043c40c681c070440010b050a0352041926000540c145c0c0c000c200481c01440000c8041e038900c0b108403152401b0300f005c1c03080d000651000312180b0000300807600301e242c12845420072609012101c640504000007000004004000c080d0b5100c1c413068210000440d0548018070140d00c40600e03d002c5d091280d500740217441c0d840d00e0501001411003160160f4180541c100300494128080041400d0f4205900710600410b042c01c1140420700900011240441003619408040f490b400b000c001001c0b03a82c000e5000780f04010a01c00410110b074a00040c105510391410b80400039401850702801c90701e031020300404009980c44010034400103a0b0080140003d0030070b003400c0401d1584104460704218000c000f10700b0100b04d1382d91140e803442580b1020340b80c01404681081000400310840b030180da0b0180050216003492003208501039020b000403108002440c000030040c0d100003501501c0d01c102c81c0d440303540c20f465011000e8000e191210000d0340100104503003482d21121200100701024450394 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 842762149 1250 842760899 842760923
    0x504121205092109040e0a0b0108010605031b040f052d06060403030c050f120403140604032f1903020601051c03080a090618060c030c08160912 63
    0x40010440d220301a6003011031480d10080c440c070340e1400940d55141d4210140140c032480d80d4280b4040c800d0090069a0394020b0405110007000030000c181000a188a12801c1e81584d807503a00722802c0e1a814001c40f03030507031b000d80d104481c2d030b400382c178880078910902900c005000c111413079204003603030000c41c3c1e00b110b102e4040c01402641d81c141440040501d0100300c1001081c184100024142d2041d480040c08000c500c03082c00b01881b006010980b6020001c01c202c92200000020000305a080707484142ca9440325001d59003001a4007141c85407080d07605544d50f484803100444041e070303c2e680c2c0c0e22810b81ca0b900c00094940031000d040100041e00c03105032500d102c4502d03040c0380007450610142c0209001c0e02c66996940c500c5002d800c000c81c0c243d80e15051564960740d55a0348613004152504004c2d00650400a942d000d000642060b481164020784091059a03a003540a0b01507505110346000003070b00144c0040d030018100c166480d600e414501e0612481541c6a400c0c400c0810040e40a80b45881441 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 842763399 1250 842762149 842762183
    0x30f06060907030b011409061306021b0117060405100b040801051501020109120c030203090a140a0608221403030c030919020109150e0406060c15020705210d0504 71
    0xd42c82580303482d0074400401c10310f0000302101ea0b04068240c509001043d2010203944034000e68104041907501d040c4941d54411009694980311902c0601d40c003245a4250425403266032080c0c5031071200c2c1071008040e02c9071014040109070040001c134903840b81d01e0b404107440b0148801880140a5040041114140f4802d03844201038081c2026065a140c099002d00044001da080410039065003008032044d0080e080c282e0840c401c402d07690354041090310f8041485e6030302c400084808501a182601c01640764207003a9818201940c20480000000a40311104041c007008829130600c00d5101000c011b0107448154a55001038501100c01e010100811104440801c605140c0c00f1040b07411106501990b00080c200c0b0390140507000700390740d03040e050802190041d4400d0b0101d400c0544200042651003000426030001c505007103030030150348090b8088048450080e2511700d03070080e01415943c420407031440d0364208034080f030038a880303018060700303031501c5241c407406200754000e10034039100c00710171 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 842764649 1250 842763399 842763409
    0xc0703060e0102270315070c0f15050f0c0306120309030607110d0905060904021b0d02101409070501030209010c06020c010507030e03070c0312050d020d1a10021005070e030f0606 78
    0x80848402519203030b092000c1d045d5070000c0d0040032800541030014054480c4c59088034007520350780b80540741c80d00800c56a02005a040c2011001c0507100400300165107c4240d2040400341c01c1e240d4a003c28018000704d101307407030400322040c481c100075030450303250130900000f00b4246401111440d002c1a27208580180d202e00501001400310918501a0486414031002564074041d20700200d0290b0360226080729042003d070200b5001c0002c140440d003841c440114002d5807107203461800140c50b801c0c0103842291056585105000301d2102026140031820000114001d40151480c12304004c886080304021a0a07440100200a080000402c9a1a214001605407041a01140d0265000f0402140840c2c1028884815603610181c0c444100c8081c84045030280100448060300510015203201e00200c958410800e8420341b4164200032481101007002000440d00c100026800c1f1070b40110302240550700c0381c3c0c0e12601505081501611050110f40340c0084112094a968001c03c28011a840d003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 842765899 1250 842764649 842764687
    0x1e0504050c061314210c01020c0409150948030b0402090903040b0c07030b070f211b0507030e060c0d081503060412080f04080f0c0703060e0102 63
    0x20580d10749150110043c50410044640e1207402148650400081c04a540c1c0c0c42900100141a802814400740503840c0c00340c5924055501d00e002d40b040e040b40b0b4116081c1130080c0c400c40c540103020800c4025005c80540090000300000b110500100c0c0914040e0f40784001d8588000d51f41c3c6203541c81d890455411421300b10381c0a10b01803c8100e40702101b0400036a040b0440c3e075006a05031401e03038464a46d038613141d24600440c0c00426018602051130306000f04001003a004603801001c04200d80e4a85ca8010303207980c1c00040d40c48001820241c41c030303c0c00d80100844041250040407001071f0307929104d2808000b0406110010000450000e0705106056010703011a400b8001141e4032450081e2681c41076a4600e142105030044c004200001903024680b81d511412078070b406401d854040c038140c90201c0003040002c60b550041421440492088020969403d115039801070441c2c3c9032100c0600390a15130b0704582c241007501e218503000440042c455002c5c21492100010026071100200e90310001c0c0e03454 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 842767149 1250 842765899 842765923
    0x50609150103020d0f06110c010b0d02030604021e1c140736020c03041d15121603030509030c0607080a2105090606090702030a0c03050d1e050405 64
    0x30000201440340c14106090390304480c0e048440760030396101468102c101442a91010b0701040c0303444218004d0060100051a150034690008c01105401908000c00180308100c060340561003840000c1c0142003003034800e5101088034a90f5403400301c1880028004da1803014040b10402410881c9000f0040c0da40255203070030650701e0140c00070b6403c06800100c010042c224010074040f007200303048200e00c41c40424852101c5400d105560380d018108855603a58043d201380b40f8040c08c82003260100c1d4070b01070034841c0105200d014620342c0075200804c10848422207101c56603a40504900c3e00c1e600c0054090141c0158403e490340354960001c80e0805d410a10640201802004100034420010341448100c0d41000010304001040050311580c990350800d42c240414001407510051050525002405a03c1800c0480e03020b84960b441d28002ca840780070360207600020034005480328002030701402c041c0028412103103000030f51440109003400b10f20711982c01c00090940c0c4509001c00c2c09030901400e05040d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 842768399 1250 842767149 842767153
    0x30e0102060f06061c0f020405090121060b0109050913020102060c09031e011803081b0f0d11220f0b03010e0708061323102603070c030807050609 64
    0x120b0084000c042c05800207050b148207100003c1c01d010741c4951049060344c1940b491204028039104914814001e51081c000c0078410310300300b0000614000ca2144c43c0303000d40c0000880d01c8600c0c40f950ba03030901529000c9a564180700c2c2000000c903403915900c01480c400d0042054201d444201400064108400900079924261040014242a4a000402c0c0110300050b5240c0d010010200c0c2d0706030300400c00b0380c40e01c10f503000c0817503150030605502c10140d074020a200d041420085c1d0100c0d81003074840c0300714003d5205446080c4070078441890340e5480408002c050318802454209892020007030540c02c200e460035211810f800c1400140010405200549407035101c840c51941400000124103000400c1c110401580000150054490010b01d403030385101c922051001c2c8a841184ca030180c0c81d20040c20140c5000c07600010399007109106e0000880740320055882c1c1d400201240516001c8220130007107546e00c030410204000519240c00000158051a903c6448040b580750003410080050514010382e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 842769649 1250 842768399 842768401
    0x306110d0c0f0e0607060b06030702031b03090109031b0e010902070303140405032d030c0d0e01090b0601050a09051504031b050f0d0201020f010c021b090c03060f030312040f030e010206 81
    0x40c54009064a0f8100400c8458944500180c5003000103001044001c0d60001808410300c010150008054403140d01c054501c0031074100304802840e036a00607804950700040029208002244000c0c50b5400e0106000e400c0d201102c0d183c035010001444d007a80440e00090f800202001819454800c2121000c030713034074000d0818145501ca4540d01e002d02e02007504041c901e2005410040d045486100c009182107000a807246444410a8019009550303540380142c1044562265610184107035441d2542c4100004d40c01c2e00c1b0f8600444a0b80c0000d01000203110b07002ca40400c441d0389800d00401c10b1840c0300b000507550b5040d8035208845030960070226041020091051109559110380241c40c401c041e607510413200000e00040b840d003128409200b8030365203441903860030603a010407084181e003440c02c8203000560061081c09071000c800c58462800120a102184c0c003132802c9026034000c01c00050440f030901c0d00b25040100c0328801a0741c100c50072480e6146010805811082440201400340003400103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 842770899 1250 842769649 842769677
    0x20c0706111005010e34050901030c180303031e060f1a12010b1806031f23090726010e100506030601110304081504051b10050706060306110d0c 63
    0x15100e02030500c88011940180300b0410110345440c80d15000d406c04411800c1d4174443c04080c000360311144019002a0408090541d481d0040305411000943e200e5070401d102e2854508800030405401c80701034641c41c03186ca500c2084280e004031000b50448100b100324440c90000301003a048507080c03c00e0000001401003454002c40c0341c01c1c107411141c2c40c1400c1036071881d02c43c08802e4114420b05049611400c048184160400c601c005080c00222246448124949602d41c2e15108202154650350504501000658a060484e003660700304e445810300a1802503100542207914034603407280900c61001c02d00401c1040482a65180c0243d540c00c0c0d5070400394102004110f4505c0000c2002e410300c11054801f112001c0d0800c21180240308450030765121000ba0003085400c00c0095400381c4072403282411810791f0000e80c5082c0300740510001c100742c144000c003031025074241d082580242c444030b54400300000840c0ca5405200300548109880c0c6a0b0780180c5001d181c22143c03d4250f010030012030780c401550f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 842772149 1250 842770899 842770919
    0x715020610060c031205190905060a0f0509030a1404120312270b270106140301050f070f021c03050601021506100c050102040b070f0b091f050a020c070611100501 71
    0x60540d1702e000c0480d20341c7c0d9804031003c401d691b1220445100b8a01800e0200b80000441c1d564080d10111105110030303050011310000b074800c00e4800900716041046503072103880c0903800e440071b0305481072240f500f0300c0e6481c102901c00641440d400e4011491101000c40d608040d481502010b40791101c40c044000003520134880102c3d031001005288180b40c0300800d40c180003290318540242c00740410500211358408005000c2c04140c410811034a1240d018100703a80307010b0150a108515000010010b80e444043c1220700041c280001d001b58090340030500c00e120a800c1e0b49030034210032610045050708040000901d44a10070601c40d030000c00c0e040a0241503070754400200320000207484c20200c0c075800d9050090080c89254407421041400080b81350401c8406042002c00724062804041c07643e869211103074585212041a8801040c40b501c04215600640d010319041140d80700014100841012058a40038058101c0008250622489400d000c400c004010420050703190030720207549422000d103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 842773399 1250 842772149 842772167
    0xc0515010303140c160801150902040e2a030103050c0a0e09151012060902120307210306090e061f0e24060f0405150307050304020d0201020715020610060c03 69
    0x1c4486480042d80c0444d0034410805500d00741076103a42450220303944c900003030080524101e4480c49080344500054405036910903281110445210a401d175039414440051990304510300444c812040124031981044840107036019500c01c0c001030140c15020410004828882c1d48900b0303861560320308004003100080360382e20340e440100c0101c2d0125110700f555203083d003110783c000d0701501d42090386000038810b15400101c0e009000340c442c81c0c48039192200081c0c0324070950402070f14545200108202e80c1c1825104034882001604c0c0021b140360b101c129040545440d004020b016038003480501c6105ca040142c502070061000100304c0c116403501100260180e0010304c18a0500301c03415442d200d2401e00d000c018081c0500808840c0d40c1e4007203044441d595082401030a02513145051101050040041280c2c050a800e0701c1701c906581d1641d003000030f1b03a807038054124114010644009014001000d030b00c80b41c618250050308103450070140e41e20444060f40d00c40001c20019451a90109410101c00c1c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 842774649 1250 842773399 842773427
    0x1060e06030a060902060912070e0c04270f0204030f1202030c0c010c0f0b0c031609061205040203070302040e0c01080a090317070525150605060405040c0306080d0c0515010303 77
    0x100c2e8810040c000600d184c05000310710380d00900201200f601c00007000c039900b029545281c00d2b0b02c02c80d8403045840d80361809117005102031090805030302c03001d000003240b80500d070b00b4480c40003207021a0b01082c01030690300f065104441c0d201c1120201800c008640075841e0420909100860402d0000040c0301e5031081c000f46002e0500c410052000203000480440b03101442c1c01c800300100310b082c910601c844c0c035402140d2100d188000d0000c00c5010501c2410740b041104d0701a500c6600c100c02d5002894003c000140c4100e0b031600c1000c8001005071228020310090540002c09000003100100000d031074090024103003d55240707402d41d1400000d400206c41c0c1c02c00346501c40007c1d4540d40d807110580f414801d08444224081d8038081941d076807070040c010414050311130014514034580b80c1000e601030b10b07054040e407548000148000d1240b410070350b210001d00d0036035150224071940e4820040b810510400000d80008050180c440e0a01c041000101c000982d42c41d00f0120561454a00034079001900c505 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 842775899 1250 842774649 842774651
    0x90405070501050a170f040c0f0803040501031d1002130522090203070801091b09020a09152604050607050a120921030501060e06070c050f03120f0304020301060e06030a06 75
    0x34100d480d40302e5080d6082d04e4444c5a0301005e0f40c101560180250794046034219100043e410000c200c0c0368080c0b00307200464000500560503d030400006501400300a03440895150034050f59801c0603800f048003060000c071406c0016a118501d1088154036001c64000500800c5030082000d145240f8480098040d10811400101c0d5020343c8006400d0180c1940080c0c141c1d801c02101d0b80038848242025450241c841caa0341d981e0503a500c0806090380140f04950010440380c0c1c400700815050300c250301030412020301d00348000082c5034200c400281712940510b000010107000304002c0200030802a500214603042403800c2100d59000100b03132401091003440e04540751658a0304110084921010050551926001b24035200000400400d030901c1844000f400020a444280c28081c0855440da6003014420030228148800d100140305d82d281307074640501c0b83d4050440e102e9130030b0010342440740c0c1d1440d48680e281058010103080d00d141d030b0803c1c400444101d0912100c1e944c0000c006640030350000c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 842777149 1250 842775899 842775907
    0xf0c1003020702060315180601080708100f080c12030405030304030f0614160810060203120c04090207030c050d0f0801180914070e0f010803070314043209040507050105 74
    0x24045000c0d01a0700d60080d0804004014003e000030124200c07110710000f034550102800c0b2806c5a61109501030350018007060040380481c01941c41000340c658060081d428200c1c582c0d07910725801c40e520005620800490308241a60b003602e2505400000010180000860405080c4000291a4030452100808820810007410108080b03038010311240301c00310816401500d49120030603601040c04c140c110010343d8030300000e2171101040c0c0c50441541c00f01d85c01107003005512181c242d440d000c041c018000814040c00000f819920a000404059119668510b034000103031424620380000f01c02418240040d0700d030391401c45503124420358110fa000740300d1620002c902c0b40e000710044c400c4034009450200440e412076600c190006140c011036116003a0520642e03500c0c000b002c00300070f0a00414003150420011540428441c004010a4107050b9465914117a80e8042c3d0000d41d0042c507404030301030140000c0007400e8404994682501900c10b507001000c501e40b55840e9600c0d01301500440c0c0c10300c00042 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 842778399 1250 842777149 842777179
    0xa0504050d120e0a20031b01120b030106031113050708272a01110c06091206070804060f051302090a060905010f030512070804140d0803070f0e030f0c 66
    0x40c0010b03036200900425209080c40c1401d144180650f00d0074040c0e142c0145074900302d00d82c200001c00000c070131040711080700c440402c0347c0111800f00c90301e251460000e80b0741c50300d44031695080c8243c03001184110ba0800300341186100740481c0440c43c48242803031071f24100403c8003c40e0401c2d0881d60100c968940311800c44400580854100032440141c2441c1c8501030392200301090341045480d050005061610104020300c0044848204180d0710003406e8120040021890074202c0151031174207002085404000f03400f8026030b00e0300c4000c480c0d81c0c0003c2c11200510003030080900c00c041582c691701100740131614001c9a00c0300c0480c951500280200030310300c005844c040b82c5a100c0009400c84001c24011965a111a400a0740044c0025a064010000c03040352240d10041220005a8801c440a040614085c20903503034000030000540c00c0360300c0f40a034500042d680c00045124031603e031107a400000ea0003c0081048e41c15040d00e9020782d00030105652000030024005062100440305803542d03014803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 842779649 1250 842778399 842778401
    0xc060f0f072f07090b030c0112090c05060a020d090501080121060e030f0d050c04050d12090302102006010f0b09060906040e040308060405040b01090b030a081801080a0504050d12 78
    0x204410b1031070110003640010102c0000c1030503400c50758407007000c0c041001d0003000c140e26000d440c04110701048451024810010080d0072142c7c2c13032405064142030140da0380d408207945070b00c80c05044006030469072000401c0c13030700820400080c00c000e1034086010760510762601441100f102207440000c04085c01c207002c21001d03030800000e82e0f590304181d90b20b4980030800c1c1c8402d600a410200300a90606c80069144a42e4074192001c0b140c0040031540301e4195030b25848045101030410104000c4864404009078940e450f80c080f01c0426665280d412030307404800d80c0070360045007400c0c008a4001000401c060036240001006031188482e220f555000703058006007617841440c062a400c254040744c0080c0949001081c0c0740304500036182d410040d62010104401c482003140c0c001d00410320f20300140105015540300d03009503180582250000000c9448405168121089240071120840c00b4032045585c4039600e182c00000c079078810b001c02c2c10290758940d210010b00c41c01750104490800d00078101445 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 842780899 1250 842779649 842779697
    0x9020d022815080f2205210c010c03090302030a03020c071d1819030503040f0209040b0a0b0f2b0b01031101140a140f040302060309030c060f0f07 64
    0x148046503540c0e0b51009640c01020000020081401c05000a0010540001d5035205440c00100f40301103d840445000c400900004141c5892090f103000601c102803000d040c00d02c0e038a00c00c0c19240c4580c0c1d00c075192400d680fa503e07403032020181020040c40020350000155424161a82009620341d200410883d02c0d081d01603201140308003206076540d1000742d030305904071b001d21051165102d02c07161300075443e42c0c0c54100d82c2e494000740a12600340400b0a120742c0c00b40d600a4410010200c00b000c041d00060f0085c00261415241d40c0795040030300203030080602c0b0b1000c035070328141c50880180c0700da940001c0c40c0036a480d2081d509442c9800c0804281c80e5400503c201382d551040000c480b07541c503420400d10205c403241070325011a5030740c0c0c0200c56402c5043c0c01e49204198a0b9a00450b00110328102c404c1c0d50000130040424000a100200c0181c0d140340146100d200800000d5407038000e284c6001c2d26210014000c0d0204d100400140321240003140d0440e640700f400c90818022a5404400c22514480 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 842782149 1250 842780899 842780959
    0xa090603111c020c0d0207060e0402180d110f030a0201120f0207020904200a0308270a030303050f06090c040603020304020f1f230a14090d050601090f09020d02 70
    0x820884040000d00c2d66018103030000942044074101754600405a9956180f400f402000c01e442913204100c1d0318181d001811911581c060500010000f480822007a02000000315101e0410010407005410a0704c0e60607c2c0207030440040c61a0141174002038a044100000199400e4440300c031404030119980440f031206a020b0002e0000340307000e00708055200d0a4062004c81440355140a04039860074003000400e903604031544074903010000c61601c0030000c05665000000c00e5108034103191703030350740c281e09801140607840c04911490019128110440700a2040384a0b1904c10180080301e000041614255900ba042c0140ea980300d6000085000c070a50a81c40d41c0710004000900c005003801c4080440b0408603110b110207009400b44600d240c041d0f0000c1e240c022901405030610581c400e9070001c80450700c0d01106440c0c410b000001c0f9200340380100d01075955512a100410603500d044c4101d80a115041c80d08004e031081540c00141c41c0031403003001a1240c00b50810041d20b02d0000382040b0300c0c0710 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 842783399 1250 842782149 842782177
    0x50f120a0b0705030406051b03060402130b03090706030b041a06070302070f090f1d0c191e05030d02030c0d0305040317070e0315010f03080c07181508030a09060311 72
    0x880c0c4814001c040740d04c1210704507101d50411001c00c45800c0c01030041008442004111801c60359640d0030302000350003024000140b2848a60300196150815005500800741440a0312016040c60300180c00c2e188260040d03405a072520001071940f41441110400c10348045580030b41e900b801d0f007806c134a403041507001050387d14411240060310400c10f510140b030366054203100b0b02884007c400403100304225400b00250541184402040c43d1800880001c861420b5140480007140c03609848810000b085400700d02440508006010514080018000a07011840110700d418141d140760742d2103c000290700380616031140045010940106010015801442480119494840030041c000040300700401d010740213000092a4981c45806c206050b590300a0b00341d400d1914564602e010b03a8007869043c0c1060040c0280410480300c803904001004d2180350303001c1501e0189140050070042142d00894181e071003004140300154019241c20119041400d000071828a40c491050381c071b101c0c000c1000c941c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 842784649 1250 842783399 842783401
    0x7061e060b040501120b0f0f03100f15151707031b030b040605040b06181206010602070e0c04210312090525061e0302070b160216050f120a0b 62
    0xa041401d010b441283c074244e03174082000902c0c201d00000c603144c50425503002400701c00c04240380d04107040d460320a490090111101031040003018800c503290015000c180688510312013030300c1800403482a0203843c0b070349a648114025400b01500311b00f07040907080452540600028261402584010500306585010341012413450034014000c1440e490200e110f00d1824001040500300740c030840c0c1544201620381840c184000300359801c0780d5000300660394010032100182c001d04000707000241c000e024030307001410460704004400000c03500042c074000f190131040c0020003811711844070314540158002d0800300d88414a040c12500b080303210071106441c50400001d01d0400000040c2004982c0070704e03c0d0b03201411b00061a10305071003128420500051004054030031588004194140c003688070342001031802280c4c0d81d8a00000c0782c1141c023412181403460407440c0d200d8060007103003105252001d2070034001d41800c000503032020b001c00c1c1d482e0140f0091904100d65080420a00d07015580142d000142 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 842785899 1250 842784649 842784659
    0x6071118011e060e010f0804020a0504110c07050d020f10020f030c0c03120415050d150329070f0c060207152a02120304051c050c0f0f0307061e06 64
    0x64a403558551595503203542c0c03000200180319007140d1012039416500c50b2103548030000100d408020181c000e80e80140d1b00d12002455588601c201680c684092201c16141c0c1d9022040d075041400e550f114074090320030780c00c0304001660b90b0a00d0060300c1c502214514400f06150b4402c81c41c04041c01c0e985442444006421100c0c05000201c602960380300b00e04413180c41e00e6458440140b07021360300c2810300290526001520260007100901010b442070400007172004030900d2040b000c00001e50094a41060300c801c0c403940560603003076000c00003800074040303280c5081c00c1d04000c201180c900c00f00d20420170300022038070822040d03030115403c5981003901480c50710a01403140005150401201c4801c40d03402078001c1c8551010b000d41210903c068001d40000101c0c4501e025042e0710041003202d0500966804481c0d081c2c00b4902d8001c0c0e00c00c44c4d41c4117a01c8148800d0510701e0900e801c9007024190340141013002c900e04000040b104000d40c00003010420319264810107800041100c240350880d414020003040e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 842787149 1250 842785899 842785919
    0x11226030105103f02070317010506180906010e040221060901030506160509062a010207021e03010b090f0712020306090402010f11120903060c090607111801 69
    0x1042e54012180789071001444201a980042d4060b2503404081040001611421a481c0b80f0700349030030040508484c401c0d8005200080744d00c805011000b240380ca41041006441c038125650260509035082441c1c451072503c0303900c0c440c240c0020f2501c0351194500149140c2d205411440300844040c10540d02c503101c3c1d00d500130f030b001211a5140c40300c0e42d94000051003440d04000c841c3c1200d800c60050603042d164030740d0f544d409070350011200e01801002c01030040e00da26800020300406a641916084402c0390b4114040940080b403d014296801400600c0241c0d40301180c41045800d0200308044c0b0003c0070001c0b9016040e62180142c0c000d904600300250122030444040c0325403840da075801540d00300402c60504034041a034006d40c004001c0d0300013800650052030690402402405c00e110002e01101e00ca0b07151654510f0640c41d02440466850424201084400d4012803250801410040c1140c04a51076002c1e01e400940824990301034180d5079100c00c0c4640c00b00c584185840384582d0784440c2958 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 842788399 1250 842787149 842787151
    0xb060102071d160f0c0b0c120705030a050702010e0309040f230414011a0d020d0b0106030f0612081c020403050703030503070f02010c02060106050c070e16020d0509060301122603 78
    0x115140c4a66980c203001030384941860038003600151680305c0b0780c903a185c0701c1c51090b042c0140751580103882000050312020402c01e20307512401b810798a0550b246801c0b00a03000350359018241505580c10030b800803420034400301c150780f900c400035180001c50100c2c0341041005040403040784249208005603040c680303020084900c0c4124000e0007481001c041a001c018225500c56002c2d4038104654000c10784e1500d4883c40341c68010b80001d005048000300354586180719072080e440030002c2652080425142d035a6030080000414201e10340400c040e040e40c40c0c00314607204150b1b810b8280e24103100f15916000c0786038140c80c080c603000380c101c610107074407031074090450f0380f00740c4030030010900002190302450300c14040c403903801d012640607001d03591030240e060303950350091003a030905030255050106070b507c00d9160741441134030b5480b00c0c4040d00d544144081d003481240148481080410440c1d40d0140d11000d04072411a16a500d501c241d07590b482c180240c00c0c03851117561141c0b812f030444001a40c1e4940002031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 842789649 1250 842788399 842788411
    0x2b060303031b080c0301030314070b010e100803030408030a05040507120804051305040203100f0e15070305180c130b060304060e0708150a05100b120103060f05130b060102071d 77
    0x2100c1e0052050300960f80118112400ea241c404100010700c00244a800840c107603a001d980c4450a100690381c4041200109801c00b0759980640010002040031000b004030091002c04090362440c1820349070480e41c1c0c40010b00358158180c603000442d003000020810300c0018801c8958004e0b00c102540781107502540180310710361090300e5021000c0581e120b10710901d400f4039070060060111400d02d15842014000e204e004040071550740030114900d046c140441105813400d440d03642c150340b9001001804440000e448454000c600f1640071402c041d00040401070600205c95501840140c2c0070340c40050594601d40d00c0d002031000c428081000119080010000b040c03400342c03005580c481c8038680c1e44080f148809208400d04402282d0040f510350300c5507400c0424841000700e010389900031849030f5481680c030294901134a000400900190b4800c0340c0d564032212200b0300880c141950f00814466008001a2900a40f0000b10300568000c002820080000c561480108240c035200c2d0301d01c0c030f0021110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 842790899 1250 842789649 842789681
    0xa0b030601080c09010c060506061c2004060f05071b0602030d0b0306060f042c0312160f1d1f02070e0609010312090b0712110a082b06030303 62
    0xc1014003060f43c0a94a1000381030303450020004068036014041c00300508000c0d0415070402030b2013441103017842c04428800000801040440322182440008000c0c0c2e41142c07001e40080c8020301c8119405107121441d6411454229203036542d41c00c08041013181c0348081e40040c4004900001c48903008409403944d001740500070001e4651007070030b06486100132501e0079400440ca40382c9418521f0254010a52110004030b860381a420030480e00b0112076100312403c107140e001042c0041000c240400280d031104040c02110395003441a000070309202d4050001c0c0d401c1c01604000303a01c0030785014481408c10a0000c2c4100350007052600c40222001840d00741400500035034802040c14601d28400310b004840251208405030300c1c64481c605040203030480ca4042020381d900005040403094042c0410134094070714821000590040500090003520200c080303508200c110102040251003070b074107040711610703501188401040c45d05207000a00480300088514020001c814168160300002c200c00354055 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 842792149 1250 842790899 842790901
    0xb030a0c17120a050f04090e070e10060233040b07140c0601030314040906030b01150e01020d050a030e0f010603060c050705030703051312211b12020c0a0b03060108 72
    0x2080340c8401c40301206442d070704400c002142040344120001c0c0b078055183c80541d410705450f41143d509840c44266020385640c01080300740400000340d43c3c0240c0209521078180f44152500e940031351101c403142031082100740c00b44031035085a2100c035224003150707a80c0581c000040c0b402d403800d14484c00c0107469020000c1c0782c5624900300010321504807440b07218030500824080e80b0b555011140180382250354030300710740248800940004035000e1301d002303544900d8040142d981088014540049840c203001c2c10032802d07908040242c0d8020680d040c01040c42c8c54402d560720f603407980603006860181c3d20b081c411b104a00422031001819440300c41584d20458043c014081c003c6000c0703c2500a02070082d0843d00100500301c0080c2c054401000103181c0c1114001100b6900d03808801d011225820035980300801c0402000c4200000c1913040310000b5a01b00b042143c540c0780c40e045040e0100301002043c1e6645600158419030081009242c1504020107280300283c8075243d46c05030b5007050f03603918003280a0320 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 842793399 1250 842792149 842792189
    0x1e0903030912030b150705030408062806050907120b0d030c0606060804170c01060e01060302071412090f1315210f0602090f1002010212010506120115030b030a0c 71
    0x80505944014000c10303c0d91001d245c5041c030326842d4468142243c0c244810000080c120400780711031031168581080503031040c45440010000b08618490900c2c03a84d10344442403006a9030740400c1e136004103091030030b120b000c02009065401001140d200c540d1000100c10b01c80308042d80517060f401d001c1d00c200307002e0182035650383c0142e070600c1e0166001400d0b2550712012106e2440c96001900c81e192241001092541c1d076040c60703d4498000f81c0082c000250001060000c3c44004103002000b41507990050945881241d81e4900344d0048545191080755203922001581d681e02c80f000324082040301041219400c607206490a001540c458441c09030350710300000f19180080002503c01a410a07480001c1002e5075403048001d51048820b41e52042c15460a103089407503c1c2c0c412120080141c0005980d00100d41016061010584c0514840c076420001c54020441880596044552005c0b1100099101c0101a000340171403006080d00b51040c000e00714148006100d070304c000c03504c003000440c10782c440d14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 842794649 1250 842793399 842793401
    0x4090f0e010905151f181505090c13050402030a060510020c0f010c03111507020f07031208090a080316091d061e150d2d1e090303091203 60
    0x481e07014040341c128a007011310010550840c41d52103580c10702c480e4140e44440112610024194002c0fa5142d110a400e420f0740d90154421105200c0c440d280c42d0344041c1c5414000360f1402401040000c00803000b00e42130512030b55043c8484050040204195200d2030300380503d04c01000e6a2246034070070642d079080c9800041c00450030203d0100b010b40301c0d03c40006c000d40191b503844403a40c0c04604000304910030680c419018800140c169105046139041402c9c01d5900a1401c000c040e00200b05401500d001c100154010f0f84071003881940b070500700040da45150855003821703040311015001c170400004010b11101e40f0003140d82201c0da036480b0b503148241c891108411520501d41c6130740c0c5090645012504914181c151003604021b489081410100c40c0004115000181088001060f0003c50380e803500e13100707902811a581e11460a2402d4142004401070082c44061040550065503140c2d801c00061122405c2c00c103040d60790b0000d102c100401d2400070f00400c6001000c1c0c070400e000c032103070304506842 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 842795899 1250 842794649 842794661
    0x1e0b060406050708070c0b122509031704050d420504240f061a071103190f020a092016052410031a0601020f0304090f0e01 54
    0x16550300d0b5418450203586100759580710703110581e0001d4808000241c8641c0303000091511500c10000343c03055092504c419940c600d1500c030080107236244007a4885d07071180d00001700c50031a0f4128080f904600080c804510151051340c006c03503000700c00c1c0004041400007888100508058829103002e0500680403022a07541c14036000244903084082e124030000c16070f1b00400e4015019a41d04141c4598240040750204010300340c4408854a400500c680e600c840c3c842c0c0b0703000700341e00400c5910b200e40d80d19412a0512518000801e40100450700c2e80301f54804020242c1d043c0700301c0032050007141260800c44085a40044100d11400b03e201c004100301c48180141c0d05021021691580c0100312898440c5907074001281c0018410307451074900c00480c504001210040b402c04070400c06e24001d0b000810450700d00189090952110103608000050603100e010f084100c51606031280ca481d40c000403801c02c01402c1c10b00d1340a10011401080031200e5a1101509014411040020110f007100c21030076622 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 842797149 1250 842795899 842795909
    0x3040608010302010c030e040c0e0f0402030f06120a0f060e0f010b03071701140115021e0c0906010e090a0b01020f21030c13060815010206090c01140c011e0b0604 71
    0x18035000100300550007601005480d902c2414025840002c0d08003080856031165115070009030b11840300042c0341041510400120029941545149440f802c180420040644158091440c020348504503a40521251104583c820200300c550101c60900710054a41c04a0503201406010482c41e14054140318071038090350058003412101e860040004030004140034603100301d540b590703080032001c3d811010940c007070407081c10b0380c0d400320324074810081c5003040c2c0c0c44c40008200360003c04620360200003c3d29040801d0211400c9006554200048a102191207101600541d00000340148040e542d006900e8040c420307400c880c03c1c41d80b1a03030495075554400c4088072140c0c02c03010150502940b04001150702001001945180240c41e002c03880c00e41e003807544107000250214090206c0c100010001d420410030920003015070341015440503480d23503c1244254188000c100203448204a403100740d5101c413107890020001c5c1c030440c030301c2410719107110412003240324036080b9006d036280340c2001554280c1d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 842798399 1250 842797149 842797157
    0x10e04030c1b0b031006020715080609130203060f060306070e06032406070803010f050d051504210c02030606150a05070c03061b11030307020307060207020d120203040314030406 78
    0xd15900d07400c07440018005004103035080d980d00412102c01501c02035005d50000b0340503065461820390020306140407500404d024036000ca0411030354603804406c1c541c000030b003120300486a4031540d500302044610044025094081d8000308198000c2080c401882400294142c652642d1001411210019049a2643e121000344045688200003c201c4a082d02084014800c0600c0000001d86c60b40c01c0500100c0710f000780040184004800e4090210040409540c05001603c0e95915161a4400544032841030b1543c240054103200155801d000250b0812218480401c032640b0001c0800440140507400b9100c0c6001080e40d60900c01c01c040580035a11400e07509100c03651b4030484081e0b000380425520392402a1022000c51468450320a00012040f0701e0f030356150828030084d14900d280d0351181c00c0c2c1d410a00c10041c10640120465100310f902c03603070050f03403825184001001d0b003012040107024840a079841a26580d000001030064a002c2c040340c81e644015902c80a80d6446180078a200203 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 842799649 1250 842798399 842798417
    0x2070b06030d120902040e07180e0d0c030f09030204020c0705010e100c1223030601120605150906040b0706021209031303021201140a05010f1409150a080d0c0b010e0403 74
    0x3e088035481910031503c010004550780741c184421602e0701a042e0046900141300340c401c0c803130404280c07040c0303031980843c41c001d8010344c000300034041c0c0340000c03051001d42446808040900f111348a24094009554010030842d101d2138500411507440800380120350110b0740180f08035401d460401643c1802101c03d0741d1388500d56240c2d54586034080f9804003000c007070000d804000d90b5100a0300c68813018908075103c02030748915010000500b4041399038000034006203440b01c18422a20350444120100c036100c1842543e41005102080789807140340e101094044010680104004180d00100303410704040c0764045c01d98480940c11501c1c0e04c9900322002c88145094030810060402200040034024200000a1100041c10301890101012105880c1c85607590f070042c0494240c0d090312001402d14200c11505070340c2000301143e11a1000307003184000e0701040d507400c0d40c595107150307811028040b42d8083d50003a48840b0b0024005980c01d500c11188040303003100109041d01103da189201d04d4040d9565540 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 842800899 1250 842799649 842799677
    0x30c0503060a1a070b0a091106030907092c0303012c06040f020702090a0b09072a06021c0f18240e07030b04060509120714070905040602070b06030d 65
    0x205000a11801c49a044240682c201140d440c0240038421105c4840109405919252104541c48c0c03000c5240e124040a2040c0041000c6c0003506000f0b5500300040003419541c2c80b074120401009550401603100403c52003958400c0c8040050741c1259034940910070000802d080581d41c030701081014106400210b000202d4501c0c003904110110482440014541400368002c1407001170125807483c45c540d16030030307080301600f04a501036500c2407030703450300c034401aa188032401110314090150681100c101807403a000d02003554100e490002c044403240ca003100c24001c900019245035541094180d252502e000d6800e0710341a0072f28105a03200b4040100c00c680c2604021541d4a0044000c24090340c500c410740e80c1550401046002d54050141c3e0840da251525004046d980020420089900103104607280c54241e8820385818079030000700f003200c00700c00500141c034000d9268807400580f41050240811b010296004042c0d03940034621000060343d80c0c00c203040d5901d0030f54541e400018409004a00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 842802149 1250 842800899 842800919
    0x1502010b1f05041206020c0709050c0406030905030c012d0204050906011209022101150509010506030403030212070309050d0e01020c010c060b040204080c030615030606040f18060c030c0503060a 85
    0x71407480d280c1041410a42c5814882c40205007805040f203c41d5400620b0a42c8400104149401032800712020700061815006a010741d000341d106100915488010241c00c00c0b5080c819103500456000081007503484900801d28540400d140c10401503003141102c00300030b0020b000312002d4842c0901125401c1c0c80d4080115034040c7c40000118000d0798074070340c20005941740355446400c0c0d0340c00d502090202804440807821150400d800300f103010041d0784104044d85070102c15604403002103400e103850317032f9642c01c0603000380c4148814041d205078030314100a6441e400d0341c0201407840c001d8045a141d4000c040d0280d480f4a1058401c60240e070002c00c03680d140358441c41c3c1e000c0c10280311b0000498901500f40c08102039030060703049900355421540c285d50107405c040082c81d034031816400c00121040b08400101b602e5940c083c1281e40255102c01c420300d00307889540c011504507100807621403c0011039041030001031000b03181040001c0d080c0500d03601e0300381c030074001e07a4045d0400400d1250389a15241e007070b135 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 842803399 1250 842802149 842802199
    0x1a0601020703151808040f12050c010516210905040504210e030a06061d0f010302040513050604150e0c011407021c0b041b08030706200705071502010b 66
    0x70f15407901c6100e1a240c0042440000071071013440e4594035a810108107481c0c8201c02d400c6009103c0c0403402c2003003c180700044510741c901c420b080491b55220000386600306103da00c0b1002e0110554402000c085010301c4919610048103595518121600e8200300001d481c41950054240b504500c00d1000360740d0300f540f000f0015503a50526082d00c141040c04a0700f40940007070142c8007540e135050104100c28a4050a48000300d41c080304541920304036800440c5181706000183c0035654440000390300e000c0d44035104503480c4c1c2050032150300d0b24241c82c0a0385103030000d87e40d1903640c60030701c0b0240b07d9000000450103030198058607000500161284210b0594001102c1a40d121584100320904241d00c0303079a095209014052240807850b041c100107540b03007c0c0392112140c03108190b030100038060300801036806640e0301000100712141020042062a40024500845032400248100400c08000b65040c111303500310041960602c08404264201c030b440e6a14107802107101c0c00d01c0a00040311803544 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 842804649 1250 842803399 842803433
    0x70f0f0e0a18020411092814060a0c060b123a0e04092a210b06150408010903120b1c030306120c030b060d02221b050301031a0601020703 60
    0x814181b041c81c80c001641c52100e401900c4000b8241c04900c481e1001c3d551301e040c042c160022989000450070070110b17841e440380100c054200200e40098800300602a0001d07801c010b40182855003104503588019200c0c541074117140c49481c5d40d406400603c03900903440c0c1d1010800e144d4001d02c840001c02c5c0a0300c13110396101ca100ea000390781c1c120030b10000c1c58114a030007510000d004614181311000c0a0454040643c0d002119410310040f84100c402d2000c0340000c0490fa0701030284031a580b035410100341032924140903281400c1c4007140102d042481503108a5080303019a0352200100c800c04208800c40c1ca20312845608070903900c204860243d50782c080780d151644607250010b03003e03071b880d407004404600c10030048410020300c200c1001800320144080d44c10140450701200703d09102da0009001d040c02e11041030318031800700000c200142c441d60002c10700e1014100c15a6000799501c000a059a1003400216036226041400d1540100c1001c80d99114a4040e002000890300303680704c0c101904051190 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 842805755 1106 842804649 842804681
    0x31b0c06100e0a14010b0d1805060a0f021606020f04030b011508070806030c01120e010218040c080108190f050f1e0d02030d0e070f0f0e0a180204 64
    0x129045514a001880d500c5403403108103005440f6464204408c0700b80c0c107408005014020034043c0c0b040291000411403801440e0f0703210128001d008150700b078440030060340d10001e0b5041e80184015200c481e8624101662aa120360042900341c02c90440d542503014405145900b003080b4540000301410000317824035240011942d42c10b9407400d500c2c100721443c4101b058140076940130603170b03400c0c158000759a60ba8010401c842d01000d007004946c00f07149000240d8040d2482034034281d05071160113021340740c03c1844940300039400c0000241030b81c4241700c0903480400208204003001e035000a01008d00341c258903644040c4920041c1c0c0310b255803e600031000d0610f549502008036200711071000310000b0203403c1001100d290244e10340001d4080309000f0000300743c04e00c055101034200c4602415a03242c0d0340c2d0f808007071415101c0303414804c2003196500a00000520b00f1b90060325214030b040c0a = true := by decide +kernel

theorem cover : BRFrame.Cov 842625899 842805755 := by
  have h0 := BRFrame.cov_init 842625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 842625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 842625899 ≤ n) (h2 : n < 842805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
