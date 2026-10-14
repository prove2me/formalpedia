-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3193
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:29.384977+00:00
-- url     : https://prove2.me/submissions/8146ce75-2bec-4058-b20a-7e40df6acb3b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 574100719 ≤ n < 574280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 574101969 1250 574100719 574100729
    0x1d033f190506013608010f06061e0f02070b03010308182706040608060a091118040f0f060216031805010c020d080c0607080412030605090f0a0b030d0201020d06 70
    0x2031101d4100741c00000c1403800007a45001e00d110030000050303070400801c1c22505096200350001c05400e81c66910035402030403d000300c07950309460f003080010300310300981071000c41c03c41c0310352500314100031080306680402900c400b02085000700d01000c40c00c0d885010196010358010100a0b4071400303c65000184406c003c45002d00c182c201214035240c2442c4009000f141144207100450f4907142d103004240035103075541005400d801001c08000480b100c03a800f103036016000e58040c112400401c0103200c24a502c200013440c111246070009808990301a05521040d40f0400c04145c002c505d03070715101c080340c202c0818800c1201e040a0084149507101880b0080000d6840b0000882c9107400c001822002080717400a020f207058643e200e042c0301c4084142d074489929001510458a0000300042c882e901c00c0303600321200d1120740583c0c9680d510a00c150400e81c0e0028150240361380742d072480f5456010b002809130802075110f004000c200e481c1404001e241400640015858411441c1c003842614515045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 574103219 1250 574101969 574101971
    0xa050606010923031903020c0f01050f0d1a04020c0c0906010203041818080307092c062206060c02090f060306010618050d0b0105041d033f19 62
    0x400d01121100c0150b100901080340b40f19507080d81e419022908000141c5115041e10481020200501da00807038000903002c800c0f1010001c042005005440300e0083c200316140c0301e90140b200c151044903562055034064103410030041811400300015090341c2c0020080640ca8109801402441c1082ca01054000600340061070520b41400d40220344030b800c00d6070340c0751401c0d1240c1005041451486c8210b1480d90020349959680c80c00c00f070041d040300c41904c0382802c140850100d100c0d0103500810b42d004201d032003100c4544642c03142401c0014960071110041800c02d10b4140120800c01d280c400e1000078006603c03400d01c421807d004010b040340008285c0c080c124000c3d81049459500401c5081c19210076080415003c181c7d600c113807502c0d4100b84c000315000103c0e03000c0b05050200661006040f2a0f0499044c080320003441000442c60940c080e0340c40090344180b2841009102e0440f140809031150000759049400300070b952400001032a1000801c006140148030b040061214048000340440c14 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 574104469 1250 574103219 574103237
    0x40804150c0510091e03030b03100e060f0c130905150303070b0115090b0406120e010209030c060c10020720091302010311271c031202030c0405120a05060601 69
    0xa40503101d02c401c42c000e10926640308840c0f002c0203e0f10011001d070118280103450044d0b5280350140c010075150091174400e12a411000d02e04c0002400740744640b035062f030007400032511036a510110150303001d0960040e6010074850301460b2415050f04e0002030100340700100c0d560134103603114504c3c0300e455070215000341c004004042c0440d00c2c01000c1411a503066014044080081d10202c035110740782d400c000e48040001500113a41c65024003141e100902078a800c010004040040b6403c070b1003400e80480d0941c00c804e84401d81450008040c3c4038200d249001e8806501010025008030391001c401101d44800e00d21400780d5601d200c05102c080c200c1b040d5000031907400c0c10b0718000303508141d00100a04040d02d8640c440c804981820684200304101c0100380d0038407648455100184c098a641e55000f0541031040050540003801003043c2280c00d40c0354280c0c0e50b80780301e0222000c2d500c01000c0c03078031b005800c00c0009103a840314004602d84051400161400c000c4510f801400e200c0054041410401009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 574105719 1250 574104469 574104473
    0x161b060c03150603200a030b06070b040c0504020319050a0b2d030105060303030a090c260f2109030a0516150801060503130303110a02030a121104061412040804150c 72
    0x45d40d0140b5100a004881e49030440001c048000e000121202500144e01282d40b5007004155801107010724860300014210701e407100d0620080703000c03c660040c1514414103041495115a0740b002d43c00c504000d002080701440c03100070507480240701190700c06100c0e05441e00282c0450311420042448c1c5c04034003d01c82810a03000007652030001510701c01489030b030b032030b514000c000d40d030722064004004840e6800181e104e42d4500480341c910549400e0010301480705040d01c00c01001c80d1036020b465048010400e4503444103280301e00364124169954140c420104d018000c1401040380700360302981500034a8009085c1400e070f054000c4551034010a000191300144105504442a258044001d004109094901d030a0440c003519504010754240c903000038446a40e00d50200050280c560356403a00e58228440f0705150b000c40d00d05401000240b1803e000900400b8071074020100304140c1d00d41c0d40c40c02c0c4015100c590302d10200a0b80c088581c080300003810010304d0001c200390b16801d8080c0c01c04001c0c00e1155 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 574106969 1250 574105719 574105751
    0x10b060f070b10050d030804150608060c0c0f060a09020111070f0303030e0a0611090a170715110708071401020a0c0905090f19020315161b060c03150603 67
    0x40c1100070310035070b814000070700032151514400004210007000081c02d5511410082c080328420b45068603c4095480c0c58030300b04c50903010b240c08844000300100707580d680e6210f40702c4082e0001406c07400a402001e40307000c1e4100c4200a114010103101c0720000741d17000c483c8005860405152039450f6a07030007824082013403c0a9044000c1145c1d01800d010035540c9184203514100303c24041d004003924a0419188603595800001e0210301e00103840c4d030007415855107911541c03141520200c50361a8402e05062200c0c41800600201091090500f010b003041070784110382c10710040c0e8210703d0641d4400d510410182d81c01418040d440c1c0001c0c0040c040c14801c0303880c2c200c1c02c0e1415015803006c003611b80b00411681d820030071018421246050507940c0d510b01c2d03085840c9030f1004209043c0c0c828400d801912500e420341d14606405a1a44041010302c21b00e54082035801c2d2041001d10040c0050400c00c00c801b00d1014010b10700c0120f980d0b500080c0610b25540c840d00050703410342000c000c042c94101e222400030300c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 574108219 1250 574106969 574106977
    0x1201150c0b2205031306090504060f140303041215060b0c0d1d062704290f0907050c07080606010f03020c030f130e0c180103090212061602010b060f 65
    0x100c0c80d0000441c541c001840c440d804a540e02c001e04511000500c0d16404034404001d8041d6815039680303e43c0036980703608000030360b00c2c1400341c044501c0c3e960000700945c02d41021420303142d14000c1c0550341401d0b03491500300c40c10a035041e0180d034000000341e10760a05490911611019103148038409040c420007a6171241d8407549809845c05221201911659842c0d54646114207124000d04065403600003105e00895211590744140a00303508050303c520615081c0030b80c41a100f440301104581544040024903070480d0103143d20b41100103101801029201c034254144214000d44525560382000d00007a0b160001c00d6014001d030703410803400d003d4243e038050840000c0814a180160f00c07000301030905800c610440443c118140302c00944800d829100c281441c0454040d80098081a40d076001c0c2c059092144246c498803082200c00394054a60007036000303c1403103002030710104111a0b182c01c03451508a040d41e9a5100c0742d9007101c09942ca96090140d80b00c09041510a14101481540002e8590007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 574109469 1250 574108219 574108231
    0x3130b0702100507030b180c03040b0a060513050414070b0f0706020c0304030c05100207060e0d060902030d020601150c2321030114060304210e061201150c0b 69
    0x5080000300301818030030840403600a2032860b0810083c107040801800901052007441e01602c41c0804244154140c0d00310307107118100d009011071070341d55180d0350340310840303801800b9443c00c55032a680855140c03600e2800b041030945090340003c0078102070601541c0b80384822070800c00d5500082080c007901c0071200503540024000e40c240750301d6102c0303071a0610290250f406002014800410b0002c18040300005d00022590300381d5854000c0000644126110000380c0950781c040f03012031901044a0800c0202d003040c4500411000511511550009043c68000c107010720041e40503c0040c001c1e021032026078540010b07a428078811108060ba0356600d020b1075019140c02280e0500171a07220508188103001c48901e01ca02106465000c407103607080e039900700b0b004100d0b00840f00c1d801860941480404caa02454100c4a100c5450000006135452095140400410000b80391180400e54891201800c00c2034035101002200c0c2d030410340c0038214015100c141d44104040b400402d800329000d05c05854000e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 574110719 1250 574109469 574109483
    0x100204031a2d090307060509031b0615010c06020f0711040c050a020a0f0c030c03150b0406120b040222020309010513030512060a030b0108060702071509060c060b06030408030901050a020313 83
    0xd56003041d490301314051900b0180080741007808010344048080002c0c6150301c10703010b225056038000000c0c103031f94050450f004400703005180c4802c40298060f540030808144030390350140c54416880322542d44d580148808540124116040241c20700d800d0103150796041803864194100034513018000c0d61910803642c003810951016845509200d403c071616009560004402c03500160f4a00c0e05501030581400d40201b030a240000a142c00d2400e0700400044400e110200c8404500a8840c14980c1d01c0c0a4012030f8094100900380d1178601e040380714600000c40700100140c8910307000c02000c5c00d44034020b01900da08042c03c6032840019030420191610300d807440e00740703c8003680d414011406030403480d0005800e484a10000250f40c040015140d4400c1d8695400c1d145215522001032031044012040e55012030400c1506014084c4240044040140246d801050025510300800d9041e48182c07002c0c2d841da02c0c00810094060824001c240c4c000340414811842d6241c0744000e0901004032220051500d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 574111969 1250 574110719 574110721
    0xd050906190c05010609140412090509070201090b090613080711040218010f081b0c010902060d0603050d230703030b030d080603070801090c06050c100204031a2d 71
    0xc0d00e03040155505030250144041c0320724030312a8007a010110200048805608021012130f103413526000b8014107480c20540c207c0c4586039a035808220030001500b0300100504110002036580d03400c807103c5c0c0110556000011300b040030b401e104041c03940040200c0c000d81d10182c01d11982c4e41c52195140c08080e0880c0800d80c8900b03003864002811391042c0350050344580041881d00340d1588043c1c1c41c03240050700341c982e01201004220261041181110603c2050000b1104990b0780e070000c50040040b09003c5e000084e1214280e40010050703003009a04ac15602e41ea15014410031200b008443c0d10300b155818114035000c49451154041e443c1d500c2c400c0b03442c03680440c0007410103019810440d00070100030191030703401b0802e200c02080301c403044840c5442445030b46000a500c1d54180b040c02855a0000900000f00c1c0c10610165200d1340404a010ba140c442c11074005c1d0800940d1006e0406184508114190300b410001d07020741200e8040c108130b1505100754620403480710083c031140401d400c0030446401d6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 574113219 1250 574111969 574111987
    0x60d080c070902120609240a0305070f090c08010b070305090a0518040201020c18150607140c100f2f010e0303192c2803120b01020d05 59
    0x140340980001a4418424a01c001c0b910884980242c0550030755102001129070741c40e4100100355605580501544a011240544802ca044407c40b00310307002418818216070390b580c0f030b907282c0801a40801510b40488406100d009110b01074001050b21914000210b54100608000c40c0d2113811401018400d00059000c4561200b86140b002090014030807096032001603800702c0c96801c200c404034011b00520915620500c0c0041910001c002d51480e18402640d4900403051041c04810b0020f502c0402032007820001064046400c40c4d1020400142c54038100820501403100300d808010f20502200400f00f5071100d9200c9581449020050380d42061a012001d1242100c0801c0d00152120b50031314010b54102e00c0000000c2d400740045100d006d0000d640201120300319400042490515070740d102600c80562481c6500c9101c9812120540701012002c84035654038220b4000243c2d0390210070441603041c55080024050104010b490034094940340200007507c4000110b2507000b0710001080100c0c0c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 574114469 1250 574113219 574113233
    0x3050702150c090a0e07120e1c1d03030702090c0a0903050f01090c0e090c011412010e04120c05030301050d0501090c060504051c020a030201140c07030c080d08010e060d 74
    0x601600c0440040c40d07030802c840410b031070f6404160141d001e018031318400581050120800382c803884050fa00e46150084460b541005064126034614031849400c0d003421000e4050049116100055180c0c2038900d00b051a083d020b652264004034442c7d002402900c0140c0c442c40e4840350f0200c454090b0759070f80c89062030147c9041c20a900042d066120714500030915560540c00041d61750702801f00e0384101c0da80d924071024006021514030038141c201e05131016540d4081c54030600861942407a241c1030825105210b6014407090f030040c1142c0907103000f03001c107014040c81d00d851490224603094004420f103485151366844103114442c06414806000d1050150030b40c403541040f42c0c4003507545a810b40e10740c00201079030400e018640c0701d000183c50b6081c0fa030f00d050042d20040c030ba028103950310042c0366800548251032401e1403004555001c200c402c034100400d100c4032001e5881023040580c21414416014505105503001c0300c03e1007031507001408110396914080e40d12410031a1001c0c4c0100081c03030103031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 574115719 1250 574114469 574114483
    0x101502030702010521090d1101021c0c0504031b0e0702060402030c0913080c2805150406090203010e0f010b030102040e130c0e070e01140a052d0d0f0c02010c0f03050702 74
    0x1158175004051095100002c00d070080e09141d651398100303421148100d041d08070700c2492881da03003000011601451605603500040451007080c203002c1c0c14143e8a071144520003ca21001c0007061102940c103101a0034410b040382d8115159200800e081d00d41a40460355420300045114441d541d2640042e0408900c4000c80c241c49600c028041d0b00c80308503031483c9a9501c03000008909048d00000c1d0501030a20400c00b5003000ea4010f0000c26600070b9002003610a1040540140c442c0e5031504903440c00b58909000e1402d0b8280c4a50003003211040c0d0040c49402c44036403d140611903401000204401280003580f5604009203500405440a951911118802c5030f03038000b9131004224000c0041c810380180c0320b01c402900030b0300c030800c0c021424a20552988600106d1002090051040c0b82206220358183d400804003440f84800140d1001948081c6c1c2e0400d2125032810f944510003041da100e02401012582041c6000901150100e06805002c205048081000f00369690001031105442000a0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 574116969 1250 574115719 574115767
    0x4020f03030f0c0a020a05030c090a18081c0507050c070504050c1603020f1006030c0b1309020408100b040606020606100c0b16181a070f06141015020307020105 70
    0xd940d03121843c6071580312040801d05034402c911305440001c081c00d01180030000c0e444001c018040c2039a1303104141c402441e600021060018850700f4410014020000400c2d44165508081d0b42c88415007002d00e00b59003004090004004091081c200781180004015066882c101d40105a998803050a00301c54007a500440c81c00c0860000d8103020702d5004591482004a00e905803035140c0c048d00c1c01081522100c1c800100003c100d59801c202100303203080035003d40c000911540402c9a80c1da0060303c00e913040764100300c0680c0c000d00040f03403c1209510030804024010707a0144a0b2501e041c901940300c2038000c0c00d4038004c0e15040c102c0c4403c9403054004540841d8000b40300c10141c21300c3c401c156031482c1c1410400c070100d102140c229001812011a82007151010440c0983d0b03104bc03480b4103689604445012188000780c7e0a03d02e0000b80e1500401c209a00c101240514070700c7c0540c0054007040455006088900030b0f02c0000d12040e90200880b911140c0a080440d5200c03000c40030b6402800c100511 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 574118219 1250 574116969 574116997
    0x111160314040311010206090606130c021f020d06050a080c0607080f03100302090c1207050a11072c1003030513170d0f1115090102160302011b140304020f0303 70
    0x30103c01c108031300300d894101440a90880d2503996410301c910ba5160b40585441d0b43c0400c0c01c040d410003404064020500c0c038102c91050324507124503400840807406003003405150a40d0042496401c42000340f145030004c01d02281c40e403480710300e0102c425885544850301d542c05003800141107030030f00c1a0b800c111070b081146171440580c0c0746000c00d902c030703031801950104038070441c9183d001ca85070700003440030b490081810307007002c410036101c3d0441907415a00c005010000c0c010111001ca50301c1d0001c1c0003c0c0e0041c4001001c40c80040503d4640c40029000c12602e00c0c4900441d00503c0181e60100d4841c40c1a66894242682da684006030105545511a0700180c41900e155843d220703030800120300200e000f42c841d00c400c1c2440004480c19070314072583e00100041039010014402c003488913207a290343c0007007500000500e8207186417610f510000c80e1517070550160303442e2840c15036041c85444240340e01d40242d1408103134000c1c0341c0c4032240c444c0c070016001078854000700e20b180186507000d00480d00301d0581802 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 574119469 1250 574118219 574118227
    0x80a110f0f0712090506031303020c030a050a11010c032307021215010819061d1207050f070e0a020c010b04150801050105030106120f03020a0b010603060e090111160314 74
    0x44100555101c1d07442183c030100c11401403850705024141c5401612002000d10b419641d490f40d110311100c0c4c1080013031301188074850f80f80203240c40501440c01014014000b5005080250418030885810301030414100551041d4a5000c01d521040704203d100f0b50324041d24461420343c0c140343d81e0303006500001c2d60140b404100100c8032080000d0310201044000885e012980ea244910358442010b036154003d01005201e4680008103298040608008191414a407032080f00828618025072058503c02d8648009048428000100103550100320541c000308903181c10003000c1204140301410f0590065000f140c4800002000c0d0055007080502800070040e15001901742c14400b00d280c4144105035280000201d854107040c02108243c60210402c1e407442c20a5035079202160b94030000c26400c60158459010000704034421090007000c1d50750b000b040f1107043c0400b940080030003504007801707a85448064124508a48144c0303100d00007180346901000c0c00360a0641e072402610702d83e0011900700007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 574120719 1250 574119469 574119487
    0x51903080a03020c1c0e01140403050102030106080618010501020717030c0d030219090311061b060114041404050d0f110a0f0506010f030f0f081c0e0f030703080a110f 73
    0x54003514207000340b41d041700c420318940c0904035510f051400540001071641a6214501c0d40210a109892131000c04400d1401c0c1d542d032225822600b00313801507000154000180a0740b440e00001112030700c5591900480702d540b401c0000303540d40c90244205440d007108080c0f507040b00003007401500c0782c6a565200342d0b0020300300894024002d41c8030401500c0045804802c01030141d124080c2c0c1015a980508603030b540c0c1801c98200a015041034010181c1141c82e00c003944cad0400d0b01407128500804030501c507025000c25003010803040e01c1c0c40c000441d08040d41c070020800407420000b0350140702911070402440c007807034101045820011714501d0705054803642a61000304040c09a03c091810f010740180c1da4207988440960460a81da8400900020a40e00b0300001180440c01107500071886141c80e03d00e4500071800b01800b400c0300e001e2008003213a81d070040329208038051240e881c000d60700c80301461420540c1d0b82c015110392009031a00403210768407010304407202d916500b124ee1160448800c0c540340e001d58 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 574121969 1250 574120719 574120721
    0xc0d0201140a2706060b04030c06030513030c020d08040f0e0a050f19020a020129121f0f0902120f0705190e060d231b0a051903080a03 59
    0xd500044114100c200240d400c0b2014815108001000b0741c180300301100140d494403001031100b2065602558071130780042c0b0400c924005100540c0301d80b2003d00d01d2850400c0c042c0855500920344102e41e43d0605102c13001070703840700011116039411604540c03400900d05040d1800d000707907000707005403030a2004003245814109034036a22404170340c00280500e940e0b0781140c82292409035010000d0504d601e500704e91009094016000c030b02c40c07510000640d04200b0441c00c80e080c0701c440d20303c020003a1503048070146081c0700781d462003aa6103010040000b0010402c82c42c0340c2c006040b140710070350350b512414980c1169aa0b08140e01443e0000c1c01400c821402680d01620f4802a01403900184140c040001c1c440c1010030140b1a8401090100303d4524540544c01d158140c0c020301080d4401c10410b1150002500007200000802001d44d240d640c4400038080e01c1c0c0343c16070320003a1b000e0680491001445d10b94a0900074004d5070010f0b603071101c046184441035030310107800d50001000d0b5000803030000041581 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 574123219 1250 574121969 574121981
    0x70f0314040821130522060e0402031515010c140102072102060405100f0f0e01020a0e01090f03020d0203030d0218091524040305030403060905070e19090201050c0d0201 74
    0x8400b003001001080d8040c000380b10311030740a005204d030105aa003040180b5200900c40280410b006403640d100011854a400311503882d04007102c84201d400510055080820200341720a0407031402d0491030800301d4880081689442c0224104940500c0710400c1000e80c9451941481041009648522181c541030002070a9402032005511000d000001840c1c40001d40c07a0103280c000018040000e240d50100c009451482c01e1310080302d448281d80080e4583c14450000c000405800050f100e44240c41c00401c92051111582e04011030500203009403981e20180ca000c503981102c40b0254072410b0320100e13041d07010742c8520304080381c07011402c0d06800410706400d4501190884031892a592208501560033f005000702c96004403420024000f09120702400c4010b01c84003010003070501e0364a6880720700c1d551158004480301500d038841e4200300502001060b001d04440220544546020381c030540d4190f00c810407001c001c545600b030303010030369000d80c00325042541443c0682d28603e02c1038502901900c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 574124469 1250 574123219 574123243
    0x100915080f0601091401030b15210c12070501020615012c0a05040c02030a1817070801150b07080d0216061506050901050a0c020a05040c020d030e0111070f03140408 72
    0x1045c9017035440803c10b040c0845043e25402101003281c5d0f160381000b44000c105924031590000b1040c4a10b400f11003d0418030b16420054500030b002c903220003824085a041702c012400c18581c000d0714240070341e030380200e2800d51206250410750700356103031103004035072034401071415140446a50000007103007101c0040b060b984c84010340e51149100d64880610080347c508401307040061300280001c0c41c0c2c00e80f194903d101591441c9580742401525006400703c07100850b4425100390b03006880c20400d50a00307000341c203400e103a124100921a480d024040d1114821040f004121000000c1c0b40c000c40000e66054840d00104000c4442d48660316207061300007410310307140f1600c1c00c005400740020640c0c4204220342d0b01d00f506139611410921040c209070b03007001d0a1031003283d000e00014804209030701c4500c82c480c4c024aa0f94000c1250144181016080302d0a44042c01441d90402d600e00c014110301078101e81c8407680c07050040d030600c5860f0400721030056681e44041e4880000040008404a00141c2d03014030007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 574125719 1250 574124469 574124471
    0xa060213062604260412050f010c020d050f0408030304030309051506060d0c0318050717030301050a06080a0b13051e0f04140a1202160e100915080f060109 68
    0x210400348211188810b42010560b00c010300d10010700024091801840c0701c105404110381c0380e6402a815280a070010740051990900010030a0144481040050b4034003030002c0081221041d145002074844219111000c2403000010702d014030503009e44221402030200b24141d0351242018035009002e01055003082d03c05114417035200076203c2414040d41d020b020018541440c1510741c01c441c1c0083d148a0003050140f507a06d16440050011075030f01c013503440348910003501183d402c00101c0e81c001d501d580c002840c036a00900040c400d03500d03010041070940c0c800707003480a230540e80d49501602628160044503001980601c240062a0964000764010121002942241218030a19400c041c80465400d0340b00c4104601090108000300341c46401c1440c0901034500c0140b040e101d0308030312410130b5001d10045e440600400c01c0900c04e00d1412004e0b111030203000500703040806421075100c140340116015650355001d5032901c0612080c2c04002000a0350541d08107090a000154440409202c0c06c8901 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 574126969 1250 574125719 574125737
    0x30e0109090203060f041d250f1503051b1908070c05030702090601020a0c0f09050105040b010210150f0602011401140603040f0609061107023604050a06021306 70
    0xd68442c02541e105030743c05008418810b40107006c000180045003a0300c90b010510784108980c11350b051050030000300d8421001480031640d41110510752580c3e03841480d05003c000c0080c008412110708c24404030740180750118180d1500c207180d1040800140040401010000b00071910311000c1b188211004040c0e2a0302c030481d035800d5003c0c0e8030403a4540c0020402c1e08100943c0006150254074031b5003252062045500402c031035039030300a400409800140100350394105c200a406d605000c7d250240c841070300c1c10b0281104c0240043d65540c00b003c01d0014850f2122580d0840b143c80b00b4460009040000c400400166a810042e00a0265998494209003035000105031707000002c081541e02d00c0044c1c178079441e6607100e031110040c0e1000803200712059a00c4003204000f1465501403180e0307140f00084000e5488905204100034004804003054044807036014a000d0381d000c9001c0086081304001d200000756035140b900c103042c03541c20800180054808108545103599000140c400d44003261224812 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 574128219 1250 574126969 574126979
    0xd0f0f0606030e0c0d050313030c090b0307060914030c060d2a050403080d18110f040b030c060f090603040605100b0c1b0301020c06040503091c0203120c07090504030e0109 75
    0x36902040c00c4458a50b01401d051419402c008400f245c08500078026203040c0b24000701c6c0140c98070102d40c81951100c182c40000d100350b040c0f40c454079001b210200c0040254628010010703055407054801d65000440c1e207040110a070f101800080e6030f2003001803238243d8a04a101c903a000134002150002550b80045444040c01005000198088419030f1111806d00b4515074404801d030707202070900320141351901c02c02c84041f00f480520b0717888588034803188483d040080d000c0c81142a000102c5612890403c401c4a8082d1404500c800b2000002d030b0f07115940340398a1070841300c0d40c0308040310660006000010801480b00c264402400350001101540685544112482803402000c111880d560409a200c0c464002c04110b0000103100260025081c9881d45200b01c0c109502140c081d1503e030000200c0d2a114503040030b00306022407004c01c1001034034865402081c1d40d03540d0480e00d5044071344c00044d01c4440080800403100205a010030601880c0b41501e00100350701908110240800c0021401240d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 574129469 1250 574128219 574128221
    0x41d0103021503061203031006080601050a09030b09070e011818120c030e10030e010b011814040b10050a02060c071a0402040f020c06041a0403080c0c030d0f0f060603 73
    0x204998004168011901c2e00907070000c4154005094142d2290405c25486100f400c180301540c441c80f030210302d102c121031502401a068240090040c0d0401001b048a1400303107800480b524103480e0000f200200e140e450092451400d0025002002d954810f40c0001500302e043c2e4a0f91108032849000c14011080340030110040002e80c01d2000304950003203181c2c404071a1244641050460213468513181ca504850f000c40e804205050807540000d49542c2501c000050074095090084020718141d54103403407500c410344503c15036006200f80581c04484c1c0071300c0c0359200d40016000c07510003003181060342210080500694010000c0d10058000c000000750340420404c16142001d0b0403054020130740642d55060010403100800483e40207071b8420301c9140046451000d000ca0003074050080030b1504017424685c13441e500358008080252645010440060360103001190069809a860354071907040e0750700c07582540214800d00802c6450300300ca441344440382d80c11000c40a4043c3c0f6040041540f0388604034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 574130719 1250 574129469 574129471
    0xf021c1b030501060503010b0702040b04112d120a0f0608030d29121c0c0b010b031e0a0e190b090a1707020109090507050a0906020303070f0c0f050109030302041d 71
    0x40890000d000410008c2c0f401401012141e20007000064521082d00c0068201c40d014040c0d54860740b40400c0f2a001c13001a034034418503644100700c420b0b154000b0302d40310306450b202e01005403004180150110300c0b0884190000000400f0102060041d140c50381c131007a03502d40102040644460900391076022aa0340c0c580025808401c80703040441d8011510180480307004600108009803045405000311000b11441d080c241c42520360700e080842803241018060203034185c110b079802c45020010b0001395038040d40350a4141d070500041c0560343c0d48003210a0000c190075801d0380524058128080070544088040041d100d20640c440c0500e619a4038900c0d40e10210395034005c0031061030440d900c0c0082580000382912504c140760221051fa103c1e107124003070b03900c16110080828030100d500c08049400004090160100d40700540c114030300000c2c01000b80140e10f03600005d1090303041644c000e2280150450301569080802030060015614004000354001c0c8585500303040175101024807060448071742 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 574131969 1250 574130719 574130729
    0xf0303050403111c0602030108070e0c09010e0a08060c040501080915010e2205010203060108180c0f0103020d1506021608031218060103030305090105070804020d060f021c1b030501 79
    0x9080c01c2c10b6659601d2081aa400000e52111041c84200d41303060340c104182901520540026031070f03514111550b443e2501725040310805003a41001c0201c1e4480b2003094803a00d410900e030180e1820040d0000c1010b140858001c0c81050080900b0010700d1032505009000303d9201707a0341c07007006075944103002e500c540c00c000194444481da00d0041183d884140601500038070303210f8841c0c010308040941c2c080702c9940c204040360070b6500031080055542e04078007540e03881311903803c040d1005c0f2200180740c0c0d1518a0301101c40d03c2401d02c03032401c143c01c5c0d1081c0d050761400400c0340400c2144d00c00a044000070309500340300d120014460103000c0005400f62400382c100310ba403c18001c0d8107201c0d01d00c1071640c01c584000c0200c88890454914000408010480c0600950080e24000f4050400101944c00d44200420780c0742031014034001d010040e100c0c032070009001c0f41c01c2240042c000c005c0b001280e0180c420b24450a04c0382950030a1488284803540c854140744203a40d400c01c1302244801d20507000c1c1da00034825 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 574133219 1250 574131969 574131977
    0xd021605030616030b130f14060907031802040c020c100f0f0e1f120b100f0810080115091b02120f090307060e040c0c02090711150403080405070f0303 66
    0x890112420f00d401078002e112942400f00301d01c080440494180e00c400380c0c541d5003081d1200400c1080c80c0c150310903c18420742e155002c42080ca0300d1004170708000f101400e18410990381e110f200c116000c004081911242c5d009006009503c002c0c20029680d2400c20380c3da5229065601c5c56060481c042d0a40303c1d4107082c10b46400c0d2507000407060980700e01002c3d03c42d0b070360130030400cec20710b059400d6280703501c0c20440d005501c03507800c0d0761021901c54040700c088031126170090541e01f02c01d01c119600411300c0000101207141c1181c860f500d180700c1c1c007003003e00359222500e19030810207003010380080e07244802d060312702d6060100000d10070300c8210b00d030044019601d0701c0540c00070f00600b94011140f400410044c118484030505d820300010119140c9200f5074400ca001401d400c3e08890145007038080c0da100c40b455441c0002e10f181d4540c000468030032001c0c050034140724840d580703c41e90351000e000e402c03030545144e83c0e409004d240c03030308010f8110340e0102c1e8102c4850144107000304016200070000810b40f501562 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 574134469 1250 574133219 574133221
    0x60605060430021c0f05030301030303060611190206030703090b01090b0f03030315090402010c0b0106022404050d08220b0627040f0309080f010b04050603030a050f0d0b030f0d0216050306 82
    0xc14120134078022003a60f007600c0e0f180d03c034404034404000940c0207510a550004003103160060041c20360714141e00f21542034020140b520742d2440820b41c01c0e565542c045581030b42c0c0b030320781c0039041e801800701400c000e06c0c1101e840c00001d00e81c426030703003c1002e001d0305403901200e04500f6001c05072244004c80d1802600009050410203d082c04041c0030352091040c10400c0c0c1d03075852604c070f4a103910380036406030005030701c40c544001400c0821104a2055001104240701c40c0c02c060f5240c5495a01d1403100108200c0d41ca03001990a40c94403d20540c0f0f400300310400320618685003003036001d00d20111803c3d4068030b10310896440d020180e507003107540c0400421010f10b0945965945007030441101e401030301040003105000c50300704010b01140101188044c00062508400c80502094400050403d071181d0418090016000e4101c0111041c4118000809540d07500402240e0010721043c880c0c0317605489040e1118088075030004200c0f20098050f000c4502191920a070b02c001d151542c00740c1e9401d03420841c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 574135719 1250 574134469 574134499
    0x26060406050f1c05120c0c0a0b07080d0c030b060703120510080d21060806040209070302040b040902070f12051b010c0e0103020313052d0f07060c06060506043002 71
    0x8030100f500078402e40a5403450002540d415040c0d8001c0c40342142c0b1070f0024006c0c0b25440c503001810380300504012204a050907280d44440742c1902401d014101815110301505030f0540c0301e17038405810214002c18907034890141d0309004200034140e00e60702c5016868500070031541814540002d00311800740700140303c14003040c0d10445011a0140421b41440000711622000c4e2a90b405120702820900d801043c00745403600400c030010502404450030700d4030400007070140303c00c45c008440030b803201d182c005a80c131852450031620510104a0207040d00711505d01c100c01c00d6034030400415402d5440f1440c0d91684410102c0300b422503100c1002c0c20b021031001000400f041d4026009158400010343c3c0383d039646000380c0c880c00e0400321114910101074013606040c0030004404600c6881e40000740e00103111145848030501d0380d91015006580501c48c1c1041c1c0801000364540003580540805040300d9100c82d039421400307860083c030f00424800702c0007040040c0701d032484680d180058036800500343c0016050f0301c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 574136969 1250 574135719 574135759
    0xe15130b0c070605130308040909061d0c101202030903130b040b090108040602070b04030f0909050903040902031f03030210060803090a030b0601050408010515090f01081c26060406050f 81
    0x6034140c1a0030105c2c08001010901c10030150000307044000d800b02d0440c18034500701080b02c2400c40c08034406030001e43d205101c5c0100051042980d10152041240300303208150565040c2c07102050074114138000410040c1c0d045c000f10107080d280c1c490608000c40e1a845552601e030300e00841c0a07814071810140000c418130741c41042c4868226000340001450005251200461014120b03010740103e00200b90006000390f115181e4002825417010402450074458a210384a114512504114917004000314805040c00300c070741c2c000c410b5191402002e041c0d59203406511800d0301c4000e090450310308040021509800f2048a29540307000740921102c504503a00d5070402d800240c807060421805110201c3d0090003403060b98010403144040307440501d001d100b084900e0780010b0840320300312081d000401c40d00304c0000d0902c40401080c0312851580c008078408503081000c400c141c515043c007848001c04540c4440d40c9007405220195424082c6540798000d02000c0d002114850f908100e500203080c0e440c0c094 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 574138219 1250 574136969 574136977
    0xf040e07080c0139210c1106090307090c02010b0a08070e0a0c05190918050405062d06011b080c0d020c061b03070827011d0d030e15130b0c070605 64
    0x490f0f2040b90b11450318185220700118070140302004120201c406c882801101a00b281441001b2129580350400350000302c0e4540b011031140002890b199080c41c017034070f4000c1d0068054200081d0003a800b00c0c3e13541036059540c070000d105403244d0050f820701107500c1104a000b03c8241ca4155140c0313a10780310100c12840050881801110b0421404401c0800d00381c0c403140342d54900c00303d801d0010615040c6400c2c10317410a1800741450381c06e44140b50030074000c40350111030410341502880c0c00640d59540d01d070058415403043c2d030308030a5554800010380c007082490006400c0c1c0074103100444045440000003613a0340c002c92501503a0041050005000784003e540314201c1103011442683e090011a640b80b00d0642c03c820715804045628680c0c002c0c2e58041401e9102c562203092900d421044c07002c4480c101560a40750400b4021715182940e0400d240c02a40507485080c8003400e400104a120200045150050700640c01c03580c03444280044c089c40700d241595400182e040240c111145007000a4800d540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 574139469 1250 574138219 574138223
    0x10e090618131406011a160803010b03090f0a02150d0204090606020102070203240103060b01170c09010e01211e020a0c11120604020f040e07080c0139 66
    0x708a0801c24591404800709401000355044140110450303207014040301d005800c5030f84280c0c1c400740040000607016103902482c2c2c05040c540d240da620310490465008210034402416102000000296a078045001148100d1009081c2d4108501c54039100f41c440b14201800ba60140504e0048210b0381c5a040040114511070900146000d80e212a04020784101d1392007840545d40c0400d4850039402c0502070030051900e24444900c130035440e01c0e41ea401d03041040c000034006550754400410164082d00510b00c0001d034150301c540c1c891911840f070b0442c5500201d02c2900040c00200c460301c1a50040f84020704003500100074a0400307050500000052440c121038140440c04030b81c04115101c80c3e4401042c0a00844d0348154420307625051050b0081284010f842c022030301c0e40d01341074045001092180d00141c0c11142801200480d00018002e48100e0440031441e014852001030600c40024000c000881c6c2a00c6941c80001e80110781f0382e240340d0200e011703034030190102403612070580b07010400b100c0b20b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 574140719 1250 574139469 574139479
    0x12021b06120c0a0c0611070201090609080601030303090206070b240604060e0904020103111209010b1c020405070306210b09010c0516030203040f080f07170a0204021e030c0403120c02010e0906 84
    0x5155850381700c107075040001c0707820080394005410800e65038403040860150603e0306144a40d10b20700342100317655100512018080640c1c0d60070302411541c80300211929140c1190140020382001e120701d0801e2450b13880098610050042800e81900300349040d01c04a511a485425921030020240b190039500108102d0400d81d0712a452000c840845000e003207210103800d0102001c1c41c10400c403d0843d000900c0d1540b044801801c40c843c0b000d01115101845681501d01181d65182d01c281500500413980003121101010003a11242a0a00e07003000038440c05204c03040075a071a15040d1500301e41c0d03010140c0300019402c100902c2d02244d400700c03c01c00f40d440b91044915180c0d42c0e00903400c1500240e045000710307821000c081200c4003800c020580c042c0004088501e40d1a0301e224250b40d031507003080380081c025500440c0440c00e6120b803105a91450703101100703540d92031500320170500e00341c0e200f400100d411100440075941e07250300c00d8010080d06907042c2c4a107803026a411040001039603004100c070fa03000c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 574141969 1250 574140719 574140737
    0x90d030b0a2315041502070609030b0403050a02010f02030a020715050103111c02040207111002060c1b0a0c03111315031e05010c02010e0d080f06041812021b06120c0a 73
    0x21008400c02000107104682c62005170201400c002400c04030740754407103820041541401d0000c9071710080030603003050b803608280c0c2e5941100c2e98280e003d440d000e02c0202030035102008000c0800e90640042c000c1610030903141c8802204022a0400c98a080c00060111309040d12803c055052105e442000418081035003100e0300c0c0356600080c203036070101c40e08641880c0a01000f0b61282401c10400144403aa8000b4001030b14004211400900504120001440181d42c840c3e40b124800e01c0940580c3d0b4001991080041c3c81742050040e014180040b030780201704a03c01c04410000501c104600c0c0008000c0002e03903646540c071a64824200d000d1158144120350141c2c0300017840074882d074201e020090b00040ba442000203046400e020040188030180446c1c20104603040c802d810f2a20307030040040360002207002481e6149520b443c007003000180720481c11a02610480d800041c901c00c601069090300c00e807078a1200c2801014041d441006a0b03040700000461071512201000c0c0c00480003034606040c803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 574143219 1250 574141969 574141999
    0x2d030b01090609050c18010c0f08040f06050c0c0424030f0b160e06092101050f01050f060d05130f0c300201031a0411031605041203140f03090d030b0a23 67
    0x2560270301d0304044820f50720000e41080007004050000c0000c10503424140c0c200300d022884c0948400019104510407503440741d03003c000f09647d200c0100c94151543c1141039068403403800f80c0c20328460281c1600e03e2304181e800544c00f80c0c0c00102181040106640750b11103010303403105108141c3c0101c60440d500101c0403d815000360441d0014007441852480042a94100007407034100b0501c0c1030308001d002d50f000740b4911125071540380c121904410303c0a8002040e41c0e6000030300c5008550302c034000707041e500201c503001c080c001d01d000380e402a02c0240c0121060500440010a45441010350901a59446212002c0998081c1c0d105180f032501d03420208203115030410004003254803400b811001040b0100a0081c0500d0b42d051002d105090303070519914260a021b41d0300c0d407002c00404002c04006245410103920b0b9820010307146051480c0c0442901c1c0d0600403080d40c2c4450f555800c401c00a07151090a411910b0b101100b0b008955481c44402c2d40c00f625030080402840080550540007030201e044148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 574144469 1250 574143219 574143233
    0xd0f0207051608060c0f0306240301060e01090e1906090c0302040f0506040302060301150c060906050613060b03010611010b03160302090a0e06012d030b01090609050c18010c 76
    0x10610348250701404003046a8080c0e506026402d810040307095001c00100320507200c04104584407101c1e001d601d40d840365250030014108044160505034060301700e0540750a59680d000145043e140c3c1038454501c08a20039004440c40c413050705c100c16540411001041000c400805020381240c8524404201152180491802e898078039017003c0c0001d0380010104424403089100a000c1e03c412500c4910705840d40e0000b400a00043c00340ca0303030b50b07401c100050000c54041c5001d080c045510200038041406a828881d006020480d1014001d00e01044002c00c0c0400a01c00d900948450305603141c00c40c4d0a00c0c80460b00c1600d00380f50490b03a50f40e55030702480c0c81c4e0740030400081c038105151403034640355003148140401c480014080d03c5401341004000048041d022403554151032030f200303100300b4500d200d00d03030100401d184013001d90089000b11401310070301400c211720760705884d1100402d115940c0d440c8105c90480351300b00c0341c040e1500c1007405400e4541d8140d5004850039241450803141c6d950031900c400c030b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 574145719 1250 574144469 574144477
    0x5070203010917180d0c050114040905010f03021c02031c090503010e01052a030c070c05040903090905070c0b0c1608040e0601030c030203060105092202070602180a0b0a050d0f02 78
    0x207080d100e0110300c0c21051014004c0c19080d0440c2900d00c24040c2c0c8a07a5190402c050321400356505010740172580c50111080882980c008060000040c440b5580d52282d4220100950000341c2c02070003040b60000d0038061a42a410030305034050020840100300c45070101403102c2180504040081c07100c000101e541d000d0088078181515038000041e1030520b40014035154a2081e486070000e49118103a0b03406a06e084156540310140002e01a514000b9261001e102105070300016032240c80c0c400020309044c0d020304c048041d031307200361010007081d12094416100c1103145071008140d5051840040d28000c0030101504001600d28001e51040c0d02d07981d201c0401da0080c0c0c00035400c030740001c0200503140d81d240c064991103095034101180785080c40000241180b203502070359070103220001d41801103481c00900c07103542200c108a00b15101c3e000d07840d00401940c0503040320311141c0c12012901e0722600e08034014804076154a2021482c0c11440c41007075031960004d40750b00490316074038218540c120009000034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 574146969 1250 574145719 574145753
    0x40c0813110d110418030903030e06040306060603021e0c03180316230a380301060314061c030f0c0c0303050304230712020609030106060c0210030b060a050702030109 73
    0x20f54400b80c2501c0c140800c0324540c000f40380310f0604d6044001c000c070340c20048960a891f01803401c4400d210031040130400c94862984001c041030b103029400501d0550650262074001a11400304502e281d01c108815010300407000070700701c5500104114144030421020764800c694024003a50050100342c10300301000039160f03010302c03070354180f080c8240142e03190f05d52141d00c80c010031a00f401c210760601d58200314203124000d4000080c3c01c2c46503200b2068124141606030b0540500b98590f4943e114000203000e0800f59001a41c02d10f40a00803c9180c50312140c4060801c940441903a0888140d0314115010079892441c0c000f4418402c00400c08202c0840c80c08019600070784034169642414a043d0940d0ba4218880d03c22103c0740a40c0c480c817241d804207025040303400c10701e24504034102500000303816104185d889039042d071030250f0020342d10790070024a542690003200c030081d4542451000b94180d40c641440d081e4401c1d02080480d00f100d0244016205442c000b0b80000341000c507560f141c4240300d0000c516 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 574148219 1250 574146969 574146983
    0xf090a0f0b04050117070206130318030c1509030f080304081b06062817031c0c021c0203090108150402070303050a0f14010506031b03010b07030e040c0813110d 70
    0x4103008035608040f0402c805c00d16130118045030b00d401d84000f5290304c40902869614501e0420040078980f003000100f0f09615140c05504215541c0d113440404a000341c1716541c1c60200b00500d8044450180d601c12045a030003d010034280c904640d00c000640e440100102d4284005021895030413010600e003041d41c00c0f419000307140d00c0c10600100302402000b1940621122400d41d0314011100c2d609120404070345201800c0e40d07818500194660960089448481c400f14448450150086186d00700445114194003038580201001c0041c0070071003415094034000d03038401c000c1040c49500c64030340c15070301041e40044016550420070000e01a039214100a4000030b4031041401070030480c6116a42d4608088002004455501541422041b4052141c00d200c1e50740800042e0450542c500016446102d2003d039564943c1c54050016507900811010760000e10003210260302c90900d482421210724650b100d100c05940d07a482100c03906201050102e51800e50002c0008603911410b2810290303520505d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 574149469 1250 574148219 574148227
    0x803060d23100b0607470c04030803070806060d0903020102281b110316090f0203070804020f01030b04230c04061e35060a0b0f090a0f0b 60
    0x1440302e10709640c510740070182e07901d0042000745941c0d4240c1150b03440341c1d21001c414003481c441c40800800728101c20180c4242448214040d0722418045941c1c00b107150003042151180e21030910640d0786001d0783c00001c24100c406c00200f04a1030003034144680c402c2c0000c1040e4036145204583c00260ba05500007140503170340200c0e60450032514003205000170b000440040404040403400201303004090b0750051140010700b02d40d00305000c40c41840300103244015003141c150301080d50140fa0683c149110741201145095070406107644030380200d178056640742e80c2c0e165040e220344d000c110104115031805418944c0c3c2d01e901003030030380399805070b020400000c0d082c0c510b04d10300365011110182e10050200300110001c1000b4032040c1e400c40c50341180c034402c81904004400b190481034490410308860740c10035040d81b15000c6258140c030403644498110080f880f55158940e5418003501941500a20f554007009100c81008034403070710090111050000c01c480031255a6521340c2031401d0154000350500c0c24009 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 574150719 1250 574149469 574149533
    0xf04030c180c091e0e040309030b1501020d0f0302120a0f060605090303040603110c06310f02120114010b12130809220e0d09170a0803060d 61
    0x650014410885040c1c20b00c12079040820003010940d190183c2c1050380c0c40c10302d04446129a45041101400351561000418106420050821001707840110b40005039140082c4a82051495050003104183c00502c855180314801303640074403c14078844201642805002c140c4200e00c1c000c2801a04006070020349001e20407004001d44066800c00790510104100f00c1115860001c00c8404031031040c174001402000c140c065003018441c08004c8070180c440c103c00e114035010415a4006102c10300385040342c900110079240b07860070010b01d80103040d441c85404a04094180081500c82c0d80400e24000076802c00c1604035186485001e8000c03075001080407403103030940140140102d410000c101c460b001c04007010b07a81c0105902c038943d45203018078410507910781c04c241d81c1d0321007100c0c5918910040c400f0703005940c21141c0d98000c2c415414005a02048001258099003e807008030001c00d601806281d082d07a108c016143c3d001815072600030071444610740c04030740d00712010b1106150036403210265080d64 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 574151969 1250 574150719 574150739
    0x1020a17070c030206150a1a13300c2105060708091009020103060e0411130c0c030e03070b031006020105010503011b0c05210a0210051e0405030f04030c 67
    0x10007440500114101c1480031940016a442e807003c8102180c8071082c910034041581080790b544142050600d2144200320400208003910402244d401c40803500d9a89040707000c400e01140a240142040e01301d11003200c56003240040200c41c1c0120344298180c0e55440d0241d9030b00b40b4904c030f01411600d14807254003c1100900080380c21a00038a041103d90404d45441c0d52128400c0d0b14042c3d1055030b902d000c50440e400f0750000c80052244041810803842c1c00d050025a0b04d00c0b02c3c2d040c500c9084039452460240e2081c2c820003101c40801c0e0f41d4000d154806603020746c1e01c0c0d0f5401c038007a41e0500c43c1120004245900d50002d41c4903102c0c0c0c0400143c164074000b80607096500c1030704054426418030310700e5170f0082c41000f6000300c400c01d5841c02032201305003410000d08150800030080d045400d9502d150160038203160040071000f5059088400c211301415040702100e105442038150f145403820030366140e14400244036040b90041c0f0580c4e01d40707041503841480301e0740181c4c000c86100707031000ca04204100760 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 574153219 1250 574151969 574151971
    0x41814070e0a0e060c07050f070e160906090b0f1c0c09140d03081801092d0c0509071101050415050f060312030c0f0c1513050a03050a030e01020a17 65
    0x218410a01000c3c00302022580c031484001c1031452004000b0a0603001e00c20100030040a0650580c10344902c544c8407010100d46003c1100d9440d240c0041000c081d0039a40f00ea41e0070001c8400682e2000110f60900401e45615030090480c0800400103126011084541290704d44a1a2101c42c00081c01610030501403d03070b05040d4400309041025091000058448028a003429940b51800308042d0351001903140c0380404000c4650420342c40d110980040080e4140c820101c9904003158110180f8028000c551613055000020103140715105c08012609140c43c0b42e0380c2105660410054200c114000b140c01c40b9000c540c02c1c0e5410b071038a5009a50f00c0300750b03c00c2d00d41150350322125444038600000441e6451718683d98000799960001300040204c580401a0f41190064069081d80d84041030340380d41c1c1d61301031010350507100c0c0b8180001c01e0468a0500021001325405805000002c0c450b4406840642129102e00d0a040c0c8031108810210401c8c401010f01c00440e89601c40b0382044054030450b00380c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 574154469 1250 574153219 574153231
    0x2070618030905060304081602040924050109020c0319030603021008010905070e030d0806011e050d0e0c180705090d05010c030615170c1e0c010b030a0f02041814070e 73
    0x13410024000899100c40c201d520100408c40341e11007840161001c20010305039200c3c082c200f40350111985410038956540c9041e131900b008c0f030070700c43c0da40c076505200b04a1203044038942c801d0740208801005410010200300303918420303050025005690740c01140012511022200010b1074503001402050710a100d8190040300c2ca250416001494801107139540011010000c00d104041e0005050390703101c3d4045c090f84103010668204120601000075281c3c0d0040019945400c0c10200860510f4000044074020598000d01c00100c00402e0201a20480e0004c2e00000420508010b801203648450207548212071240c2c0000136241001000103049588075006184640801038100c460351b540242480030305d20324a007031441c441d01c4035610001c480c403d158507051842c2c0d40150500014041301c0192005c14140c000034010300c0700200401d40c0b20b03d43c00704020040e143c1485180c004d0700701544116500c08100e408400880c0540d102c40b21002040d0059440a6000003030030b103d081d440502c0503401c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 574155719 1250 574154469 574154479
    0x1e2502030307170f010b07141e06150306060603100906060c03020d020601052d1203030430030e031b01020a09090203040c0621020406090303080c0a2102070618030905 73
    0x130602d604202d81e0101e0602c14181802d402103141c0301405010310714100b07440286000c46103164076030078041d041d90400c10030042850081400141c1d803000040148804690020050507155403014100491074101510080c0b03c02030120340801d10141d948964000f0b4041c50311490034035560307490000e10780728103120f20314215000180100116210b40d0050052400e05542003200d0030b002c2d000142a03072080d4000e0b01e03070050240c841e90080240200045008900602d104034014a41ca01c17000303001134149a0320000c1201d60144454002d100c1c1e4054400705a00c0c80680c1c0c0f0b843c166800190343c0c45c0e03850800201e680d500180c2c2220654001d0305c0840105010f0400b54211302d0183c540302e0368940329200b200107014401f070722550501942da05810785021510710440d1290f880f00401003c0d602a40400c90101e2400c4020540900160040d02c80f003031100e0741c07003800c031140d21081d05c00c180703420410303501a654080c4403220000e200783c0101d0341150084440c0494810080c140144510b100d544030174016 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 574156969 1250 574155719 574155721
    0xc1406040b1e0a0218060f03010317030f0c090a080f060a0f0c14030408070803150102101107140f0304080303150406030b071b02220c0302031e250203030717 69
    0x741004400194800f905110050310b400021500e036151162007007445134044c030700080070608030940030b000d58141d0f8002c080e1807010640031101e12203240300c1601c92081421805c40095818000030009007030100c0d0280c5460810780c0e0f900400c6141c02a001401100c98211500b04110101380b4403c00c222500700f104248481120484040c0c8280d00b004202c2c0341d0b0810000004d018044140101c490550b481000d00717969241545482415042d441da64a00601800400e50341c00c80301401210710071450210200e00e85403956a585101140c0c0880c0310342303207000f03005101e0840c0c43c0c1800a0030051860102941d640c0ca0b00d041e04440c0c1c030002d5800d407032003186440014030104000460017a4401c1442c00d055401480c2c4002e20b1ba458035000c034000b903001508806d80c0c1200c0c1c00c014102c2c0003443e1403140c10701206a40c0c1d0070940680c08100c0e82c00b08034914003030000020900da4522280c00210b01d5102d2a048004910000e4a00e064461500d0150b4000014401146c0e1701141c2400e003c0340c5c10300e0680319 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 574158219 1250 574156969 574157011
    0x1507060b031b09090705030a030207091401050618030a050303090a02010908210c0a08070c0303080f150f040902040f0605030708060c0405040c02100501060206061c02150a0c1406040b 80
    0x80c500c801c2c0d8640102d10070400540d001c0810020100600340050443c0c0a072640c1c0c0c54002d41d035200c00e004031200c850a01561440d10140c0494582c162900103082a041454014000c180100108030b441d038940b1070707400e0b04408610240b0056000381c450b140600b000540600014105240ea83e010700c6886e80f26952482108046808080300080301c800e24a0b80d034410740100310b141c0300110300c0180c1f00e02000070f03000c02000605034281048074800d03103401c5216503030347d040c001000c0740459256450b41040b103820102c84c41c0102d01e90030741410082c40000c44071810340214088529082980490664400d0140101d103010005400108a00c5d401802c087c80c10503a0001980158420280130300e807100c0c12045264001e2101240d00b07845e81c0c400300141e607502d80000b55100c4041d1a0f00380561403884188a0b810302d140400340c20160082c2a031a0916418102c000c01580110984410451602c601e00002101c2c040103503800380200006290074280741c00c154400000140a800020b1510920105 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 574159469 1250 574158219 574158253
    0x3011a030c010f09180203190b0a150224060111030a0912080d0c18060c0309050d0807170702090a060e04331d030f030117010b1507060b03 61
    0x71103140a00c0d22000c80300200c107080d02c040d01c16411018000c038498518588001c440d6000d984901030360a030300003400c1d886889110854451440301e41d006450704105100102d8030701c440d1803040090344111080d4410000184000c00340302100344065007080014440190b030300003251412084980059807808080d0722000d042c0711010302c10705901c0181116204107012003001590201450081e0900a841407240020b01600000d1411700340901c00450202d1410b1094586111041d41074580e40c1083d420b080c200440500f00318001c41e4074000420200300001d4961a03880d504042c1880d455440d0380d4144104120f06900400e00c10405161100c00c0210074282c820a41d0415081681201d8803d180030340c210b109609044c03041d43c00306007004202584d400720303400481421880f500c4c40300340c0c503030b40808030391648100a42d4210988040c00103000380c0000009034402d0505140c00040c41c07000410100e51651565441c14004860101340b400a000c41d501810314644001c030050911110100d103c01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 574160719 1250 574159469 574159483
    0x1216080a021207060c060506010309170c011a0d081c090b010f1a030a093011030c2107020d03030504060f0605030618030705010626161206020d0501031103011a03 71
    0x385c00162941c1c0232410b541d010b41d005a0701c1d150055403800c1b05000300d1408030030540c4841e03d11b0040350703e8803012403046641c14000c43c180580083c500d088084c1c1944900403a0341003001d0703501d070001c0400c082c1c1d4011402442680c00840c8100c0290b40316601d030028560080309558001d03e07002d41442000400d003501a000c0340ea04c01803801e00094a0b0f00242000c003500a503a039583e4004020385245010b013051002007000080b109640c2e003848400e941e60100e0340300c0c0a0064060741c6580606001024603103400300e48000d10741107100213810800c241e00050150804001c007034001c00c0e5140300307200238000b07503000d050030130a000760301801043d1401021990780c8000600b0308134a600c40c191842214041481150b00e03241d01300009100c03550f02c41c850140036a090820b00c58000d0f40001c3c2080c81141c02280c00b400307450116002d9086640340078902034240c81d80781002c5818590800c0504100f01c2e2038802c3e0343c01385004003201c0740f0f085c441b80c080c1401c540d000d154505043c5400361011803181d400050036 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 574161969 1250 574160719 574160723
    0xf0803030c091e0406081f111602032e05060103020c0c010e040f050103140c0a1a030601031410030204200409021e0418051b091216080a021207060c 65
    0x40d502003038240040d84030704507003914007a80139082604c0000e1040d40000c103804c10b0300001c603011650380744001058044034818007c07800c081900b8001c40c01d1500041e0119200a400541550100440030f41102c840d00701220201e8203000b004d1500020740031140c46141d80c081c0d0b003800c0c1140f0f41445c1031070040c2e40316014003559040103016070300d94855442c0d9400000701140100400c1c03009584902d00b21626500c0c2c01c100303441c14450602d8801a070325010841d6004c032159200302c0d5441801001c0c3c40200c0340d1005007258140b5490340b014004003006460364920941c0035240f103e00103400d51040000342c40e00f1807400b46140c80c504108180922529044504940405170010b0b80c403500d80003000c02c03401200c030002e4100c4101060004010401a54000c4280d055280800856540021a4103019050010594501424004c3c0620381c1040d03183d50b440c1841803421200010303c00700c1440d05011080d00410459002400c2001c00c60801c981039a05810306074000c0c114260400310700800d5041d16101c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 574163219 1250 574161969 574161979
    0x418060f0e0906042604030c03051006180509030910080709060f050901081e09031b01090f020f0f040612021e03030915070203010908190e090a1d0a05070f0803030c09 73
    0x4920128101c4083e01d401181101485d52126924141441000c0803440f05680724010007808102c182c9240c802d880580d84c2c50b0184024138080c00008100070a00240800c05600c820482448941d5a032a04540da2250030303601e410a82c50020002000555154410b005120800414500ba01d8101058803c1c1d21402c1c60504041c7ea1003600283c500350a4100000c2e0100c800001e0100030741c00407000b01920b16544214101c0c880800a0060880b000c2042c0540113103002400d00f001482c0c075242c0603d802000403c481d43c00b210030b030001400c03924568001c0503203040340400c3c4021428840d642540611a0081101143d0795160200b5200d100301784070540b262903a940104a504000e078141d507030032a0050b000700075001c80d524040f0010391189000c500c40407032400c07052061030f100380d11444503418007400c4003440e9150500d02c031024281004010003540c903403200c00f107455071040006920450117000180145841c10902001000c3c007a002551030b908100304100304141200215400c03c00c09a40b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 574164469 1250 574163219 574163243
    0x1d1b010203040f061e02070302030a060207151406040b03011515020a05150a060506130303080c07020904050a1110050307120b040207060e0d0201020702130f020418060f0e090604 78
    0x40707045200d10780040c0c81000302c000000c1400da6110400c0e0f82c11035900c050540f030341030003900700341d0b5034005510000358035600034400003000508540242c8449407007083d482c02011202c20701c46040e030f00034242c4021304242c80c400308505031501b4090b8906600c3c0c10350080010094000300300718800414003650348100d000400700c81980e4800c1007003001280d000810fa82180790020610b000c0040309031980548241010008202c519101c401c989620b0000622400d07550315669083e10920001845000d1240c0203104607805a112040c000344500d1241c806881000810302d0b0075054030380300a0100b8019001c40084404240c5c001d022031360804103d080a200c14a0110800c0003d040c0c1c401078203400500104600d02045005c1e0000c80d81c046040741a2180e104050070304a01f02d004141000e9801081b2252480001b41c0750707400350601500d04040949000e89515484400391003062003400350541d00c080c10064171090780604000303400030212140250406c01081c4d5942d240141000d0801c9007406 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 574165719 1250 574164469 574164523
    0x18030f09030a02180f010501050f03280f0609060f030f060e0705100807080c13050609060d0203180606010206162d090602010e060c070b0910090c0305011d 68
    0x400060312950092000b125000079103003080304168140d1707007250b0341040400042010b46c051b200781d4610b2400a0031460035680c5140d103403040f0103030441c00b0300c4080042c011502e0b2911040c1c0698100184440c2c000710750585040303001c1046070f5495102000030404c4032410300005074010f01031618070b6000f02d0003291600f200e011150070498a40d0000da407200c000c12640851a80225000780301e13801c0c1d0303100d40403203654040d0702d91454840c90620340d1001c052020107000780d02c4e2105c09820313001d00280c20349007403071003d20061040f40c0c8207844502d01201c0307581c0d044c194000c1c10030105501450a101800359030600541c4c81c0903140015020406020750301e81101803d08460030002000c1065091550800c80c0420026000340040e000c2c2074019400c008414070024000202240148038842d101880c4c0241510354400221019094443d68003850601d101008801d000e000c445d940074050f01064149180f40a90849a00e51a00710304125002c4445010203008100303070189505558030100200125 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 574166969 1250 574165719 574165723
    0x150a020d0c1d0a0e06131410051003060303020d030b04020903060103030e03010609091e150507050901090504150b030a11070c0306060e19020a03060302041409010518030f0903 77
    0x1184400034941d2510315140c181c80e5221080b510070080e088200900300d00018103114003c0024040c01d03640d9802000031407418281078080e08440d80c000e0074006a070b801c04c00b003c00035040c403e4951122011400b01e041c0700034600510b0b200c090350010b007400c020003891603030040e444a108241c3d05d0149603035003040030116165a01155180300740101a22525030712480c01800300821844898001e6290603008035208030b0b41d114102030980c020700071001101c1c1c002105140318400c444212122100c0b07140d0b040c10700d00603015182c0543d415854140d103a40050300014400561940540d118034144080492201c079409050b90903034244044056072a551903030117074094031800010300002540007400d001802030a2005100b504e2080034144509541e600001c40c1c1c450302900c1e14031200c10448184400170025600034a40305519080114019a494000800301c07211100080512356120040124120081c0f140350f80c00041c3c40036009003040c07070382d640035901d0003000c03014903c400000030780c8106a582 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 574168219 1250 574166969 574166977
    0x71d06090d390b070302010b1507030314010e15010516030306030b01090b01051602041d0a11061c09080405041d060f0408070209041b1502060c040503150a02 69
    0x64a61102100c880c80d00750310b41d50840140001580401030000c81c440150041d90080c0c204199480010798180801102e950f40420b404405565031440268810784810054035990040c0700c0c0c805450b00218100501074800940088500400e040300502c00d83c0c4000c2c502c1074100f2014418200e1050070040145e905101d800a1810707101076012030070381016416040b910549202d20b4100c0c24590b62070100b0800c1da0540c02d612070100c1e80c1444240e01d040b003101210042d1600080011884c407507031080820806007802440304c2940c0104e0402c209120072640018140c41c01915580e2030404050203441072800314000c103041e40c0d51148191000e1000c004161400707803c00a00800c15086002d080d001d5101004144c0903d038040c031400a2101c0b0146d00a6500c42c9801110091030700000350308102201200500441e265014000700c0b40c0344002480402e0041c11400500703002c02d50f940780e0040e00c0c01c8001000030b04540803c200521054501080d84800c0508000c40080240c484504071006402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 574169469 1250 574168219 574168237
    0xf070219230115140f0a05181308070b16170106110f0105010807030c08030307080a0c17073212070c151505010314070f051b0c03060105010206071d06 66
    0xd00d00d50201e058000c01609400c0c4c0101100d918000c025903030309129000c900c038443c00c0e42c000392030341e0145104d21019410552104420141c8003040405554481e0a0b82007803506945046421003008554440700d00c3c00c0e246550705003402141d50b0880909681000414080d80c410040e0b80a50486a104c00300101d00c0c0100c0544004e20141da10b1f8441142d854401e4070082d91541504640014161404400c42b40075200c665210845c41c2e55150300c6c44050300f000c450150030000100b10030340419000d280d2290040c14140c0d6001c03601d00a00840382e224401320368010401060b203000c24890062441c04031600c02003080c42c0a880c0380c1e1074840c01da6200d4112180070700003036072488480346900700075031040c403180c0a044040700c84107840307500450844005209000300400d01038042201c550181c5a01c20b0852414500300d0718280c00882030a0b84928a4140070b2034a5220744003140b064a0107218440c0500401e100410f420b14144000034442040c400030701070301045018446055440d08011202504 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 574170719 1250 574169469 574169501
    0x31106060f150d05180610120201051b160519060c1101020a02090403051c0507020c01030f060f030614010b09030703030e0a05150909060102010c1211120f0702192301 73
    0x12800c0f500d48500301d00e20071402c140900480b0300041110318110701f02010b8602c04180764466009960055840ea0701020300744d030140304131442c051a452401c020070500e490381c0b840140411840c00c01405180c002c4181040310394a400350060100d02d5110400f40c04580d004080c12041491040060b401c125038084040e40000c020800c000a068024008000007030240b07401028600081446904641040d9a00001a00101c042c0307100e941c0f080d042490503d0f03000c0000030704c103607030380b0250580d9403c1d0703500c01c880c116250403d0f10420030074001482e004080f03e103d45072034641c035030000a0306d69015010040c144406610703c00300030740b50020f02e4006414003420f0643c01482c0c41d845c484281d0801742a040c4120703100d0f00042c5165106003e16034000d009a120700c1c0d81c2007140c100b01400341400088284840c2e03014040304074941c1121a825010380d413071000e14a642d08080301c00070308045890442c034070021900740449002904058600103220080c08900c0c242c004030300301c09400351103613011400c090f07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 574171969 1250 574170719 574170721
    0x5011d1801030f1202060708131104021c0f05130f0311010f020405040e0c010221071a190207110f0303090406080c0a080a080d091406070c031106060f150d05 69
    0x129803246042c0e64203003e00d8004100c130a14141c100d81e142c1c41110031500165260300440c0741110700e014410278582c41200040174481c9580b0101d0200d07000b62a540803482107003074124980309500d1266411480c0b10b800305000314074213000b44240950348000001c15030600c04001405161240318109040e80c402c0780203100b00c004404500019412038090180325903d001c2c0e03911600b190003c2e40ca40e86003c1a0054944850f170352054200605072816100e452003002c00202c80052402c06e03541113000d274403460700509818504650a200c258a41603144d04500c101301e03000c0490800404d50350b800030b048803e130b008010303507001203410b6015691070950004d0804401084004000c560002803100541d09007000a51392298569140c280483c0546190030030061912040c2c440e42204036000c0c016016801000504070140345041000c59500c000180c030350f5178090406601901003808901c104008040508080001524102d03c000e800c034440c050f0802c04100c815000380595020610380c0c1410003031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 574173219 1250 574171969 574171973
    0x60f15090f0e15060309120a030e06011d070801080c090c0d0f09110616060903170c03190605130c0306090e060f0609010305060117010f0c0f030b060405011d180103 72
    0x10060030348142114103c03c6000801d10f0918000380e07840b41429900601c407a01c2c4859415801e80c0c0803c5024041541318143e006515004010140c0284540c40e00c0f10780c94401f503010842c1202d0013030001820800c0190040100742000a00b07a80149421209503025840e001aa94814851001107511190034010184440400c652040d0101805015902c44030302040301080082e1147c1d1060102d0340500b15401c1000c21071036400110918400d0030030340e4014107100800b401c1440d00300c8910642c440b00000704007000c4907644a078003041c8400c1901744452420f08000501d10700443e10050b003000d0703a4190360020302e4442d80108000f010007601c100524408040e03110784527a0102c803101000203920b00801c1550030300d08252030403240c00c0300183c0000e9013803658200012108261141c1d0a640300c0b03501d817a64409610580303d0030059601d40341108a600c200c040d007603602e010021803041000344010411a40c120000c55082d58442c400c201200c5c2d4004001000e8840300541c851382c2851040000c01 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 574174469 1250 574173219 574173239
    0x203061807171c0f110304181a0409120906051317210405190b03040b130c0e19060605190309060c02030306090c040308070305070f021e13060f15090f 66
    0x5400d55503580217000b0342030072185540b445948906520342d540b41d00008001d2583c0d900c00316881941141c0c06581800d903000003002e48004175000d9034059080c040c0b0780d002941002011005000780d00781142080c150480415141d180c91290035852401c0920301c0281d1031090250700e075040200480c103d96410410701600c959000f03809501e0060042c61003485644e2441400041182c051104040c51a03865070740704c0121040c05898501c20503204040742c800101e4202030b0b2030140141021414892501940580703034004d201c0344148c1200e242c040c0610034103500c81d0480361140480d43e0702541c01c000c2007d04030000d014241010740400e1070100700c00500f690100c0150f000f038008403000e82103525007040c1c1003514815403000500c000003c01c808400030340a20302070111385000b940312803110f16150300400d00360f485115080e5103120740b400b03884000c0e02d00341c804244056820542000050300b00302041001a0f118003a05406141140c4040314083c0f0030f90048004e410441c270701050785a5550340c820 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 574175719 1250 574174469 574174487
    0x11060703150812040303051e04030f11011803030f14040b030105030715020d0305060120060412020a1a060d0c141e0108040201030b0a0801060806040203061807171c 72
    0x940e80007000000241c810000442e00481c04038201d00a1a081c9156029201755011404000801887d800c80460101c580400b43c00103501481e10142107252505e400d544141400c001c4a05010000c00500c9101c081441c41000b0350741c0c1801e0101e03018560420a40d10710403106e0b0241714840e800140418a440b00801650407200700380d00700c1f622a51114902030b907088a841d80341005a100490582da0f8600c40d801282d0400d4040c140542c00440000c4881d031085101c4440308034a91102003400b04203c1c49a0b440361040300c02c1d20191409043d01c0c3da40c0798a481c02c00210000d041e0100020030f4181d0b50705225404007941c082800082c4ca0707550520b220713000001e4101c10748a401c0f10304e80c103821180380c0c441385003611030143d450356080e507215030040d03006201410340a1b0b0800348040011907030355001d100c7c44000d8515038009195034a00740c4101883c1c0b6900030141d60101c4000c02044038080070000301407050f1280d203209941004202e640c01c6d490141c02da04043e807104210345508c95481d41184143c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 574176969 1250 574175719 574175741
    0x905041805010501080a020102120904020f041e1a0901030f0f090c080d08160f09031407050a080c0a03080d0209190e07080114010e0a0e0403030b240a0f11060703 71
    0x28007440e0385e10b21a15440d0138840b500680540c00400203003080060b003400070050503400600c01810607a4081b00c0900c0e64001c0d03000300b03203c4900e508600c80107024040c0002c000b41003203901d41c0c2c1108203912612500d8043c0e41321060515490382661411408643c001d00d4114030015420030800381d06003400b11062406d8810301010340540840100003a01c01c48040d4400c042d060080045030b201d2032400c5403d0b0120f070350100d080201c401c41c00b2002039840513086029100c540010700445045c0b00800030182401c0e0300c000740c1c9074041000440b0700d0315102c10983c1140d0700030307030740365241c20300c110307842c40644a00301181d03074850100b1080800000d502a0b01340c056404141c1c0c4803030141d81e01d442c10f44525000780a1008a044d0103d0103c04540c840c0b45401203e400203480b51141c0350b95a00000c41606041d00c0c21000b10f0b07110b5030300c610141420f50034568030070070b49104540707450304c560b540b400580708100312002001f484418503100180903020b01d401d202400000c4070001c0c0703810a0020010422a104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 574178219 1250 574176969 574176971
    0x902010909050c07020904030521091b10050913020301230f09040803090709021204120206040b041e050f0105090705010309080f0c070e070906140a170403090504180501 74
    0x4041941805441a98414103403070b03000604d81001e6800708030003030384010800c604001c002c20030b12070020008411203008611407002c0340b0316420264401824207a40e50242c803111107060200211541d20958044c9803e038480c1402a902c0d030540d4081640702d07080703101c0400c02d50b00000000480e1854864042d028440074254030041d14140c07820041b10410414003150b0020301d00c000305002c19104030045420600000c2210070150340d480544040e60006850014120302000c104400e000400350001c0c0c0d91101403015029601d00303542c1d560a0b0500107000904158030f005901c4034030386040301710803401301d81000840b41402e030111800f50280c4012158072103e405805800540ca501a001c0c0c46521a4411146030038403480c1c6c50403480319000700752507058078484c0f6000080c00301c10035540f40b40900d44075a100340707a5600b00030001d8514060352841d80c400c08400c01900160990080102d000c0d0710440c404071007261100c1c10201c40050458100c59881403400c2c0e20000d0f424094101101d82500c45c0340 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 574179469 1250 574178219 574178237
    0x30620070503091314040b060f040e0c0a0906080d051e030406092001050d05040c09050f180c0f0118091a120703050634050c0c030c061605030d0f090201 67
    0x49000103a170910b400403440c6551840110340050042c03c0807961122020b031860b44003030703420400102a900240c5081d989d0b0380014140c1011400c0101444020340070742c000910656143c50002c6507038001400c1d0300780c10000003140d400b100c00b4070607868131206000c2041c01c0e6140c0c101030805070014218681c04542c41c031086e6002002001070b0b518804007501058640f40c0c10100c0703900040000d040001d104580d80d1903001c10210344079140c0c3c40703890700403090400081546d16020071118200154411411000e91204075008032070354503500351108000080c0b0740324400070110040c104110249810011426050401d103075101c0b25000150310070181e08130f46521504080c01c040d0782d108c0700320b400054081c2d04408005003080c60310b4400501c454003d16490900e81a5070349001d90b0128428030643c0c00500d0014810a03420400c0062100c8904220082c142e924802c4000402604c5500c12010113202c120481505015090040d158045000c18051014130780d400c42c80d01c010560300c6012408034526807 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 574180719 1250 574179469 574179499
    0x1021006050a050d0c03020409030503160c26070b01080606130905060a0905210a031a0f01122019050703081f030812010e0c120103062007050309 64
    0x4040c40044030005002d603880e00f400d200c1881100f0701110400c2d030354000320840000c016142c0384140310070340e4080c0d580c00d9100c1c00c0c848100c0e54080c1107000c4c81c1d41004540300000300811900305d958120071903582c121081584200718201030600881384042e06c4410090000104841d003c5a09407140c4130480f81c2c881e0f06d04070304c20344804650707040d600504503510110001e840b0401e240d000d40d11003409002262008040414040d1000800c2d034042c02955001080c4414815014080d8044050f404403011140609080105107001900c440c158100040540c08021100141e401a0510000d4100a445180010181c0c82e9558070061820340c0b008100d0b080031403200d100c2d4007550009940766840207156214241c0526580d221003080b14640d54000000000291014000704042103500302c500c03040d98540108004400c400034241d00394031004000420700b00b100d010304541035950102d0f00103590740d4030842d0402030041490405044550005a80e0207100f800005400c000314101c1d2140c0041c0040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 574181969 1250 574180719 574180721
    0x70602122b020f0409060e010e0705030a090804150915030203090a110f1c06113f010305060906070201060501090b0a141b15040b061905060a0509010210 67
    0x90728000d65101d41100d5404a041c051801e45078820441410242c208100b400c240b100691260344210122940e0b20070800004c074103040c0710b40c0100300c80d03e00c0105500d02030703a010b0401d00c001040c0807003503035561071520104a040800d8901070204003181c0056000c504402610480090291450441e1020340803800c582c0303c1e00840e441202981c015109080c81c942d1030f1001c1c221103908a6500058500214509884180350101225001102c10710000590b0400c4802c40f00200100703140d55400f000b020b100141418607091003180c02810404601c642103400010b40c4800821902c801003101d0b000005011001030618000c0d0794410999a0644031450107900300c45080c8101400300d00803031002c201c1051010003074111041c0d03905120001c1d2410102c12090342e0b20110407075040a510068040350804e08025561030a01691620103042c02c0603110340042c1d01004101500c54404031040207851041c4e440321074010080a0011a1142000800030306240c20000c3e00c24018070950900a59007845 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 574183219 1250 574181969 574181977
    0x18180609030307020703020126250306050307050607020d060e0115090506010c0f050c0a03060c0f030911040e031e092b1103160905040b0705040e010e13050f07060212 73
    0x200350010301181b855a401501c2100c2d81055660740c0d14810002100b400a403029002e200302106655a00000100d4000c641641c114060003000c040c5016400d00c101d840004124007695800c0320740603101d5046100181002c60b61b010003c00c05405c00e01020002c800540007181103400304134001040da0f445142c11001c5640403103041e80000d1240030700c0400300e0005c015018006010b01c003a00d803c3c442403070104200c0102644200c803480d0f40c443c0c90003480c0b07034800030280064805140600c800d070426212100503052040007280319035966911000e68481c10411640d204ac1044000c80d07504101c2c03103042441d60049107407207004400d240c0050f00310310500c8078840d908221805031009848070548400f04082c18440c141a0944a1016000395030307440850030100503e461000032415240a140c03800550384081c00490038400140030501411010f10307481810340c1e00018030f030070041c2e64402210030044036250000c0c2c0240104054540e031080d012412070161211a006c03141074039800e210300015442 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 574184469 1250 574183219 574183231
    0x414011a07051507120e070602010f06060509211e010b0406030b15040b0d0c09140405120319050103080304020a0b25020a0807083403060902181806090303 68
    0x41d008941490f00c030301c0702854010256181568400c4981c0e030b04041121100b80494182d5400351004200070f80d0709004000c145440d0000c21700ca014908007000c6d16a01a856042e031043c00050520503d2001060540e600d4142c00012112080d0001c900907040600354014020903500700508015582814050390003103a611030030040c2d107661040341807451864000e0720664450745512062016540315054402c40601a65140078860b180085d50000c03500c100303803803a08802c0c943d000c0101184010500d0807400f00c2c2d0f40c00650780d03561400588259400c1a40d01440c100d4a0b0800100520003c400a07602c154800e95019201c161600042e550600500c0c2d4041446d1038029008004680064034413202c0c9440a00441c00c81500c59032120b0a0584a030031105203944103090011100c0140c5a50031a0b8090703100800c80c694034481e0030008150403502003d092103460309101c40c00c54a90101c01c2c00940c2a11100f4171780c0e03003015100300c005400c59444522451182030045a0307180702c00300407240039503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 574185719 1250 574184469 574184473
    0x20412031d010c02040b1503010815010807032402090a0b0d0e06010f053c030d050c07090209031006080607090609080d0807050f0403030f17190216020414011a0705 72
    0x444154200400b5207524442260484810400d100500c2d61f1100694060058040600410032002c00509290301c416480710b5100c0d0b003d240d040002c1111511007003044107840140b003400c00600344890780644151109180c2103901c180001800550200203050845034042c4144100100a100250b0f02e44c0c0038014071803418440e031070410162030f044c40c049600051034031202c0c0300e07000c0e0045076480d00142252440d00c0090b641542d07649030325042c400700340d50940034244141058001c00b810741c2d41e5002809410384031030780041c00185d1980d080001c40d0a003d150f900c180f1039035446050031703034580710180d611001007600c6034804201507024445000581c0c81c40c2c0010030216541c139008031425000944030750b003400420004443c01c000b4020080018500031303121002c1542411000800c1d00181181d15100c42c0c85c1d04042c0f03c0e4030391004106c44080d000c1d0100c050b844044c01644032004030380c0d030704000b5030142c98040d0986c0c880c002c03000c503181250300c00c0b9204c419a000d015401e60b51841120b400414907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 574186969 1250 574185719 574185737
    0x30f02041a090c0a020a020a09050a0b01050f18040912030e0d090b0d0b150403050c030d0807020d080c0c0a060b0405160c06020a14040b071101091a0319020412031d01 73
    0x400900009044d51a100f0f00c100c41000d10550007003141c41c015500480400d44d292410030003004e5035405a09002c035403c0c6449072420006501e50b80942c0110402c4080d4001100c0c5841c00c0b50b522600130070a6542c0110726010461102315015006110907800c1d070b8068050b080c034940b0300c076019481034001c941c07036085802d10b040ba50000410040c40500702c116800282100340082d0009160081c0c8040c5d48508010540c45110f03204061400d00c0e8080c05004000481c800c020b9804e60100f100034070303440c450074120660340b90000500d4440c001c42d51050034510403400c8103410321007a908100346082081e1020040340c3c8618803c200454000e040c501c01040000100c880000c07030942c02411014178910b0300c0200c141d410743d40c09216a000350701c088506017020880c0401e0001c0380382d80c0c4006c202d003402c00b01c068a1400468000f06102e41c0c01140d401003000c40000c600c1034220034647e00c400d02c52041155103a84800840700c0076190181c2c15400646010000e402c0005400908001c410058552002d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 574188219 1250 574186969 574186981
    0x1020304030f170a05121f12140d0f1b080406230711040506090103020f040b0f10020607170705040b031e190f0605060304080309031201030f02041a09 66
    0x2a900b03082c40d040f40c4241118294094440c40c0c4809800c60744c034039544081e600c0032044c0c1c03503445400c0c018100b00408030140c210050300d4000c00024030200c40d00f00d1244880005642480c4682c2c2134072481c113842c0c600840d801e020010340c1c4090042d0601a09844105001c441e00c00700311402c103081c682c014074188040109100407401a402c88401000c901c0c03000d00c03c0d03424850f883c0055007180740200d0b60340088139a41011860a03000703070740e41b101056030700c000150316580016041d503d5007840c0c03c4c0595601c081c2c946c01903d6a198000c4440b030f0141a9194003140b504001307607100030485441c40018030703109040b182c6a0b101c00c801405000d41d96159803c207418644281802c0c0d0000d890070000c1000801260003140351740742d0340e920441000701d03000c0c5080d80d203078440001d985106c00054203191400300140a69959441566007043d0000c82658495a860074100c2c503501c10700034003815000c40d4100000c10403400c80d1615800510075241406800c41081070070001645a01c45583d00030020343c00606 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 574189469 1250 574188219 574188233
    0x20c030a052505060a0c05030402031c021515030111030f01030204110714060f0c04081510080a200a080d080402150c010605100c02060307080603010204030c080c1305060102030403 79
    0x618281d03088500c000381c00400781c5900350501e03a07820443c3c964119100300301540c00144258055208941406450b600c4c240e40000e0b04d40d13400e107204040300170032042003030300b4a48200140444200d511108140501b0400300240340010040c0800b480b96003060074106521040b80184c0b4028074036160480f08590a590030031014000704000d00c8a5000107018420204003440b9101d035807008000064080c0d401c2900044540e0343c402462010840c50820042088000004000506031154a80d8200d00d445410311551525950307408400a4442d00629900f0301168503100042d4000030358007024004100d009010300c0c60380520480403c1d0b04000d02041c10240560741059100d84001c040c41d996030303808000b042654020a040001c01c0c0c0d5030748014405d070705000301c0c1c0d081d1100113820154400c02003540001d0651000810000c1002164408500d0549094041d01d024591200840600790781766140556255661091f5900c5820314503800168a513140c480e1901410040e80074500d003509644030a2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 574190719 1250 574189469 574189477
    0xf14030f12060d080304081206030f030403240c02070602010c03060b030609060d0605100e090f060105060f0906040902120a1b050f072a090c021c030f060e100603020c030a05 76
    0x540204002c040b04000961013401544200e01c140ca20540b1000c2ca0128100f24500c000c10082c000d46c44840010300c0e503135002043e0340072a40c0c044080c40641d01c04c0a1201004002041d118603014201106422441d801060542c281c1d44240c0c02044160071814084043d50f100e80f08035504c1140c200041075140c1051070300c032903010802611005024005035100c0d012140120b440c1d044402d1114418400c01422003c850b41021010300248900c20b040c8620b00e46803001845501e11070a000a42000c4131a01681941c01100c1c00034509034589581b1805140a136100c2c1058042125950000980c80316a9221325041140f43c11402e9045540c1c550003500c3e16172001d0315031000c00d20280711000000b8030b90044100c01c030700010b2845d8012641e00d21500e0081c2001d400203048a8145501003e40550020701d400060900d040d0041b14024030039030940c02022a05c50b03032407440d824a680442c1c51701080c410240a4014041c0080c04a55242d004908038002d00c01c9090072500100101d5002c5840341d4050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 574191969 1250 574190719 574190731
    0x3020417030403020f0907182312060f131a010e0c180103021c0609020909071704021c060e01090212160315150e0a0c0309020306070c060b0a030f14030f12 68
    0x2045031a00504e450500020b441e44c4060704001204800007800308940100789000c09c001c0d91114080d114400700c42d51503104c018804c45000c1d0b40040001c288801d0020744100035904035485240758040202081c0100030240100c06101101c1d41c04a030b0842d0398541103910702d0440e00c283c3c461030f0040c40e0044000c1c0d408001da0050200381003005140030303441c42c81048010405c41c140146d40c0d003203602c248880e409004003d1400d01c0440d0128102c502d140032001c030380c001e50407900310041d41c0700315464090101110304007600080c0352007806041d8032015070103010018021158002408191030310940d0b00e40a02c844401c2c0114200030410014501520411080c12070040205c2e405181c0f051a0603003460740c2d8490b6103211040350600003200d50768446e03610060f0b5146400c3c0300420268001c0380e91100040c068030100075951303042909205140c2d10520002d0700041255211325030b64103040f40d40e03100303c1505440040311000d64001402c800411103008403005100581400c00da041030b0f002c039040c02414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 574193219 1250 574191969 574191977
    0x402060703140c03040e010e060a050607060b01030221091507090504180506042003030f07080306040b270c03090c010c08041a0301030b070c3f03020417030403020f0907 74
    0x1e0b000d1041080c4094000b404041b0343c4980558036140e184080110050001c0c0d0185103455014003c517201d8008941c0e01075080900401e0080c180c000480003441120030300007071b4000c2c503150700b40240301120f44680108408030844000d00066128040028410f450350307000304070300391000c20050a150b08a901401c800703215101c03600105032101410030b201210122080368400d42d840c40c1040000d8203044080405400440c1032441d02241c2c1e0a41c1c0c0b183c40c0b006882c850300800002d240c3d5886400075624010081c020a80c2c144c07544031101140700e0070f41a01ca244070704910000381c16103111001c0e00c4c881c02c105c3c402000e6800880c001540d41c060f8250301035800c010700b00400328580280c00078806800782200e006540d2903141d404c20910350702000e4440410011641e5108006c54580880103a051311807040840b2142c800720b04035195800700902503003001100900104001d0303010390241049554415901000180c02d010980d12407155000c002c0d4440594141c0c0210f03410200c006c4c079400903c1c0c2c20 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 574194469 1250 574193219 574193227
    0xb16021203240d080406180503030a0305060f0a0e160309050c2106010621021204020111030702030f010c0201153605091b060a090e070c120c1109040206070314 70
    0x10200d003100d2070783c5005580300714000408001482d40b100400710b0064020f01c0c441040c42c2043c0000ba00d91103010007080425880b1030114017107944517064980403281c0100000303111035440074480340040e02150004100e1f44008090320800d13019020350170070180e03c2009003440701d0400040081c8100c4003001008098000a03071111050f50030070000d4044c0038035407140a00c2503d94000c101800d0240501028241c0c01840701c04082c11104a005810942c24248548907c0c0004c3ca003a14500450002030f41c54030651040340b00340541980b02c114214030b258001d20442c0301341580100c0606040c400ca0030510b034405c204008042d03456000c10032507402e04e82000200c20b1400500c0003a04d1054403644241c3c0c111000d02c400c4d0900c1d445280c041c02406607102810040354a101a203000540d1040c0301800d1002070000e01518424030004c03185a90103906100100641d150040900305562011200d5514400b0141d010b8a812201944103a5000301024902051990201d445c110300000b04422140e00348 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 574195719 1250 574194469 574194541
    0x12060c020c061c0e03190e0a050a060203030a0b031002040e06090a0b030d08040206070c14030714031b04022a07080318060a11070602032836030b16021203 68
    0x5d8006000c009681da181f02c1d5640901d005c100d400205c90740500e02c41c1c1e0304070b481008210303000300940390711452100303000510180380e030b01090810240001180082d40700080114003805640283c500900061360603d4041c0d841807034410403911502a2144c0c10f9000040003a0f00912658940d5441032028022600340f0402d03607588040c60880d500b208003031540b01c40d44d15007541030800c801d00041c80c111a0f4480005000c4021988600c520291080c0c440020100c06400751287d80407101401140c151b2454503004c5c0c0d5500006a00080440602900580c80002403074800002541d0040501d458641c2c0603040460420585d1740c825001002841040c403e0003506030303001d20206d40140f0030303a00515503414100a01c00001c4170602e00b80aa042034402071644c596602c404007812642c1c0c035910107885101c2040603c00c04050710b5403540c08543c82c202000c004c2115440140b0700928440c1102c206840384541d01340e807070702400040c05207807500034800030f402054120590303004040c550740d103848941440 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 574196969 1250 574195719 574195747
    0xf01080c030c0f031303110d0f0c062c07080c01020706111504050609070e0405071203170429060904110114070b100e091c0912060c020c061c0e03 64
    0x200c0d80b0342130038103c000d0005d0038550440f0703480f842009680060038090040381c00140171074440c0c80e025401c00000361101406c1190603480301c43c3c081d81d8088028207400e1410f036905c0103e00f08400309091802902e400113107401000406194891058001d05505410564225400d46012810200602c140300d050040c409042040341e0150340280302408071840d000b032405251a102c0d134018030304160504104004100c003c40c165081d149210320400c20340003076040481c0c1c0fa0540745960000601c1c040c00303100c10464500e45020080707036540c2c0b4050b401411144000d140c60022070b0415081103110002500180c1c8001e084070504805040030403d80c051988813080315001100129040850803060000402007211014000d210213441d02090b854240c040356200c211581c0704900080448070008259401444c0440140c498544425000191030078564090050f0098580c09409900c481100608000b01100c0c01c0c0c00005410800500012112100900320081c80a000f03000501400290301c040c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 574198219 1250 574196969 574196971
    0x1b040801091b23012705040b06090117040609050f0c0922020f04020c010204120209091c0c02010306031218050109080d0804020301020d05180d02010209180619090e010b0f01080c030c0f03 82
    0x603405c184651030b0305213000c0c0001c0700d55180c08644030355010310079890143c0c0e1000314005a1000090118141c2c0c0766031078680d0241140040040140c045c0480c8015104000945105650012034401100d9100c8000c6180070690310700d02d10088034038618014000d030038545640c00c20b4202c007410052400380c00c521000c1c2280c0190b00428141c1520a1f5014254608503032800d13002142d42d0040d04c0070420300c003c0c9000360101d01540105101040f0340540a6a000e03030f03c4040255000418035501007281034000b444080d9690741410610001d990201d1365510803a42e40d401d6404070b400401c1d25680500055038000300080c01281e0564013080303980e100101e94054107000e80a10b80d0000801211502110705128540c141c0400311381c8140302c141c51580d0340c0e0f08810f10003030700c240c1c211010303848031070110f000b510b0001e003442c1c122402c4401c00030343c01c5c0340c91344003100c4411214000c02c440c0001d075003004000c0040742c00050026550038041081088905d0085800810b543ca40d5403a058075401c04d070081d608 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 574199469 1250 574198219 574198277
    0xc03020f0619240e0c040e0109020a020f011a13060b0d150816170c1018120b04060b01050c12130902120f1b040801091b2301 55
    0x2200c18000b21902e4035000c2c0c40159408100c42000000c2c1804486100e25150300c500c0024105200201e092103008000316006041e4010304000b02d5a140c855401c042d500001741d100c010b100741c402c107400404042c403510000303007034248000008807840c204001e4603e448211131480981e4030000001c1441034880140101207050401003030b9000304103a544001d0359242d10600e1150000705441c41075020300d050786070640340c4400c41d00044034500740e51326240110982815801c881601c100c02495a00502e03030340c2a91100d1001031120a445400342d00510f880700000414140060000c20001100c1341c100400040e018940b10f400c24440e2031805140807a090318280d18240c0000341c10030b00347c035032200442c06030851280c2980703004800315403041001c9008100d9506582218081568800790807400502d428103e02c805445c3d5031100581d900800d0001c004807440112000c0d01010020001e8a200448105264400c10a0050801d1301a40e20310350b01000d04100c8031b80d14110b000e82d5102d18520b0724407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 574200719 1250 574199469 574199491
    0x12110615090a0e0f10060e070c0f03031b170105010309020303032205070312080f010612090302010b1e040c080405100915020304060b030622030e0f1f080a1a010c03020f06 75
    0x4000200c501080346e0190b00111101c030f880404002101c0e40020814104036400101200e035400c441c00c0440082050b084201c40302d05081140c1e98245a003c2e01f030211000101c01041c0d0580d0380d5800550413601c1c106002505034005000003160418000700070325281c40c0100801c4100340340c079918141402d220390001c994103c2200c11f40c031311a503480070555900403108070146505505001020700802414640c0e590050b403201142e0040600c01c0d00710b6030400f0405800c00302d914880f011190703826060032403518003c40c5003c404660a03482110110300440d000f90103401074580542c402000b0f042c0c5482e090700c1041a6100009003690280300661085010f482c0000f001940300c8101402c048025045210000f103c140001c10300344200008506240c1c5030424058004020000c100c682c0d03080d01c10310368007070f110131415003450300310b00e030b942000010a80e07482c08580da40c1000401100c2680005103a01c0354182007140751540136000c440c1066001c0e00440c0c43e184000040c00d4030b8140103c601d05140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 574201969 1250 574200719 574200733
    0x60403030c0c05041112150a090b014109211c3609090c1e0302100c0b012c0906160903060912110615090a0e0f 49
    0x40007440d0b54440151508440078041c43d81c094014880d680180c00d00d155408170802c000c2440c0c000900181d881c50340000d40501c880320394600c4048000d140040125010980640c021200c09451421401c20f403440d548c001603240d2540484503103102044410400c103c5c0c0200589426039a039428105128442d0000600b20101e6404003c0c0c103220580f121748500b15844020214003a030069001c41c000340d000898040d00600c400083c1c14001089036504841c0c041616000c1986100382d044803041900803026500c50580d00c0500c3c10360160766036003506180171846000d10040c900401212403803022132410307003d40f0f005901e650401344420b07401100a91445501c011005142040082c00455654518055498800c8200e07440c2e0400800040261448000c0121083e00488601014580002d010404881940f410000a810700126540071515902d405c0350322545c0051114030941171750000111001c02c0c102400095200940101c0c0d409442d003000d80926081005520350f01b600e44001480e51f = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 574203219 1250 574201969 574201973
    0x4030f0803010302040f0c0e0625060c02010506062704021c0e07060e0d0204051b0a0201060f090905030d15050d0609111219150c02031b030412031d060403030c 70
    0x1c0b100700440d0120880e08001d1210f0341d090308460400c80c1030100703880d001c0e500e4440c04000180ad8114030b0020303180744040400e610612105078404980c03801180c0013041203884240802c58540074160701040055962014456246560a0b1142070914040c1c000b5060881c50f00c040c44810b203100d20010005a520a000041403904212030401400141080114100e01d2000300c0e400c5070007020042d001e942c42d040440c0c0407a14101d52503d610700c100c0289030b12880070081c0240605482c5c4908808540c0122000c40c090403a403047e5849260701c580154640480048090058141c600c1c6840130794503d0600043c0310780310314900301c0c00c0601c15030b80041c004046207404440309458030750183c000c056000000c5404100055420062528401c1c1c1716034904841c81c0480785000021107480103103080600300219031b90000701401403164204100d52041403030040b0140d4034003840c81010500103805c506080409e005d1160b00820020303004e41404980c285c0350110328aa40076500c210005100e040010b01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 574204469 1250 574203219 574203221
    0xf06060103060f0302060304081612090e10090506040b060c0708152a070519021216170304090507020303060913030f0518120c0a08060c031b04030f080301030204 71
    0x291001090a082024600f80400520600321a0200034001d850000114091049820a6809d0300342901003060243c04d440c9003100307500004500c11804a4039503800420180d2424034140e01c43e00d81807241011035803402440034048c00703015110a410a07a1055411825112074000300700060440c00100501c0f450116402c0c0340031041510349440c00251800d01c0a01407102800e80d0002100b1001010701d02c41401c03141c010303846403040041c07440c030070328862100307042c0b012601d003204134022604400d41c0904414810b84822802e032020b000d106400c1004e20881c5030800c040d2414100d0042141d06050b102c892000849800707444e000e000d60710100810010303162200c0c3c07461b031120a0711598443e0314141c0e980a4140c0080074074420074084040351800d0340b01074001e4803840c2c803c40140b5810041c0d0320a44295100c40e44514194040c520400d8041111200010f00c03501481501030300502d90340d2441180031a080017446007900e00c031410400080400e5402005400a82c020b140881c1e5a515501c1040 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 574205719 1250 574204469 574204471
    0xc03070909091e1a040515061804021c061113080706020d080712021305030c03010b0117040203011e0515090103020d06090507081002032d160215090f06 67
    0x81c4605040c80400000d01071840c103a00c1900907a02240d280e0914508503148405141036000404103180801051040c0010b80324880c17480d02607541d4054940310244040b00c000751036101c0085114034013040050410205c510650006842401480c1840d5501c15080d02d49210701c580000202240091070f03086244240402404114000c000151810601a44459041c41c441050203095400518050f0040640e100341d8500b0082c21950b500e8000c08850741f1000340e0151a01030301c1441010a114241440b400c00c0180b016190800c280d0860759400c004648003c004036003654859104109030300b00391f0741000d0350a00307010020440b4070302162500b90442c2b45038500362103a0314400042015032900c541c0c00f030004d5000200403480545a05040345051225400400c95100c3c481c3c0b051070303024075603001d940103004030050f9100e0b9a4019455420041c49220b8200103807a807070740401c129008068807001224214010303030710304c080d203026007030442c0d4001c94280c055034102c01826035120100384405 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 574206969 1250 574205719 574205729
    0x90312040806280b0102070504180b0718030206031e0106080f07080708190b0603010f06080c0406020715020109120905180f07050c0a080a09050a0b0c15070c0b0c030709 74
    0xa00d10030040303100014400d01c58140d0b038103c080e552034a020003640300f48001c1c80a000e0180040c803242581010402e45004c15440a562400c0c044003c220824401c1d07004c44890621142003c0c4418216003c00c0030f59840a8000c0b2450001000003a8040000c400c03003600809040d252207005240c0f0400040d0001402800c5030104100071080040180e08440c0094001c05014440d0843c00d5080f03d00c40c00400c8082c81195102e013010000107030700308c3c0001d540700a882e2182e840301c406446061060403140a40c7c0140800360704940024001d403000c2c08250000130300188004540b00e0b14940320700300c50030030074000e8400103a402c020600c503c1c01d0144091200c1c0d004000d20541e0343c80d128a103c07010050282005040101c00501e804c1d50540400c80c144400d40c20825060350b600c3c0c1d040c00607045802c244201e5000300110313100047c1c0071a10100b61889070684402070000c1508820181405450040c1490140821400e52202181e203006455200f00042507ca44c0d40e4100050080c0c4402070079030203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 574208219 1250 574206969 574206991
    0xc080a03020613021f0c050f1029090403091a12060316060806010203071401050108011d070303031512230c01050904200c0709050106052508090312040806 68
    0x540343c01601c03521000302450b601c11400c0101c41c40111011504007500e041c0c040e1040c420344004101600002c1802011040110b404101c00c0084200000b44943e48400c68805801d4401036100d5600340b02010640c418481c0c40d05030352140e150290302ca000700140c040051001404507030745100d0b2100c2c0040c0c54116100f1001881404800f5150700c141c041c990160700200a090b00c0810043c0c1d000301b09642915501c03c60b6000b400e80c55419190003440244a104170560030310004280e05a0700b501071240c200002c2000d015070600b140c6060713001d030001c810007600140d9021f42c006420b011aa20003030001d8800c40207940380c811140c41e240000c441c0b411030803002d070700002d004e20b00aa8024048810104080d074020804044004205400d0340580c010742c0700000c400500140d40200116005041d600b100c10100401c6c0d8a0b612300b00d0340b9008000c99002040b144204d8a082419a00520154248a6003c06183c191507201180c1400c41100619550080100c3c2c284072444080c05800c0d40300d065050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 574209469 1250 574208219 574208251
    0xf070504060803160302031603230301060f1b0c08060a0e010203220c08010905060717010e07050c010e01151802030c07020d060603081207081b04060f0302070c080a030206 75
    0x14106450381300c0c15005104100d1640784c06000c0500a2069406089096001d0340d905259420041c024007032035000c008504000303103a603c01c4402c100054030b041e15200d58889440b56440c0c8010765009541c10000c1002d040040f0a000000c2d0042643c94050f00d0910b024008a06100c2a03600c02c0d2154402a03022590040c01040103004c50042d00c411150440c0920902400e11401c1c925025003464000d00e545508015808040c0000020954020612541d440400e0091480001c454000c203010310715100341003001040206204401411001e04100c00000e02190300081071400c41d1075003045400041307180002005084030b4001e00a501c40003812080d803651420b0132030701e000391050510080c41030100c00000380038042c1c00e03031040b8043e6074000b4109036a011000d039040601c40c011a04600010340c09000500a0006003100c007240c61104900b080c141428144146c9001c004080c1d2402010350a22614001c52014030000000348900ca0140c01a041e140c00e00900f0400d005100e81002c54042c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 574210719 1250 574209469 574209479
    0xc080702072103050c0601090b0111061315020c0d03060f060311070f0f0605010303020102070210020a0201170a140c040911120c0a0c12030c080601170a2c0f07050406 73
    0xb024a500c0701940c0081c155403030b42d1034103440c54000e5081c103040a2003a0000480c80261541c403d590350842600c401d8808103001c40c0003a82c40104503804103440c0c054085000006d8255030130406d00c0c111413040942040c3d13808000900d4244026070b000c001944518041280c0020780c81920b0181c03005140600c000500194a070b0a18814590000c00d00100c00700d40c00b051000e0005d824880550015043c0259650303070400030b010703400019080e1b2007001c05140c00804280009000c1d112164180c4803400052036682c441401800300a040f1400d460716410481042018100040d109254256055032034909142604007195850b01c811840518100501200294070241c095405003519109079604e140f07080f400c41c1c2290791150010301101000c000f411103030f90542c10401d01580c003a42e400605a4400004580d07081202c140d400d8845030b50030101d81409a540c00400080c08400b0304128081103907803880019241c0c81c0240c02498200a071140b6196074188044401024211020b0044608007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 574211969 1250 574210719 574210739
    0x16050114250302010b06191202090d030f1b03020f060a020f0f0904110307030e121c090204060506040e09011406060904050403030b0a270c0e0120100c08070207 70
    0x1484524801c1a050140c00c402c0500c01d4120003085680030384200d882d1020644040e5407510340100304408649041c08001000c01144203071000864001d000c1c0b40c0001280d1015038600180303080700000c00c01090301d8009641c0254000c00c41c4144030760300500c5400001e01804d42400c4010305004c036058010003400881814200a0714448025171034215a2081c0500c0010700600d502c102c2c88260316004010018481c0e0590b01542905040e0707005e5550090244c5603c0d5614400c0e80006252454584050406126180c2c00a080d00b031001c2c00000d103081d10f800000d00207803c2580451944540c80042104c02c02c400e0043e400b0800032119030341c03818100100016140d0040700206030141d81d07114001000d043c0f00341c024640f010b0020700740440090300c0e440d20705a04284808103880d4141c861104090280700780c451074444450603500d507860404c0c4c04d401114019114140034581001c12400b281403610180301002c4102015070300000c2111320280c010b007c0c020014941e1007907401c581c070708000c3c484003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 574213219 1250 574211969 574212007
    0x706020a0b25121404050712020316090c110f0601150e100518010503010e010506070213020d02040504111201180608030c07030512162316050114 64
    0x40403156050300ea44480211101c2c0040b5201d0040444050031200c0c8080d402200c011207911140e102403008040300e6045802d1060240c0d801003481e844801d00700041100102c0b2800e18500c01000d844002d5030150b403281c1d2440ca80e410510a00da9102e4009240390742040503102002000d4002e01140b0107079801894030f85a0520590114910060300340b04010304c5036a06007032070b0500600c3d40714400b03030580e03000b46140c111041c60303115616024104601c560084041d24125449949000300503800d1905004641d01b20080807600203184c00b480080088480c0091302d81d00c036104cbc40050302c980c9444208800d80d01e1090f42603044000401c6000031400741e400e0385174190f6461401e0f000d401030902c501280200b000d907000004c24040420600f01e0001c012a100c82141c2c0079200f00d58803000d1401c2501d8152240c1903004c400d22004051100015202e8505544107289218043c2c00d02030642c4e034200e09001c000c40c00304010b00041d01c0184030b250b81141c82000403001d16003460f8108089130300507940c034801c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 574214469 1250 574213219 574213223
    0x170a020603040c2103031109030a02120a0506191503121d1008040501150b04060f020304090608010c0f030b0607020114210a1b08012c0106090e090706020a 68
    0x80e0010010b4107100811a002c001000034800d20700761074001410104001c1c240c00000c50000e1b0429410701400001e9900760b0341c0c00d20f0b004020f004418065801c00c50000b140d03000f1918180503c4c1e0807100800e0040c00b615118256109161460048503206081180c1c2012100502d480c2d9103201030010500c070600100200c0390f542005205200d60b15910001d0320300c1804410fa02c0350701d205e600b04031141e1203425140524072800037480340661190201d100398010380140d0030300d0b200c07e000420096228600502070010349006480c90140c40d00b00d444140d0f8200c0d00200c0d8560b460703009400706113521203854200e1003403503d8204140350110002400500c2192000380c10000884411081e480800040311806411080d9131540340c1c8161241e041820340490350104000e25040310492002241ca41511002140e5940c0783d285a00341031032401000b40403a00b078442c00c12a00b00010b14101c81c500c00d1400303010320b42c540c0e000f00c03450100070414013400146125556003041c101084010340005403400710b15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 574215719 1250 574214469 574214479
    0x1002030c070f0f0507081e060c160804080d0903120e1e0103140f040506101203031109030703050c03160e0114011e08100902180402030601020a050303040c060801170a02 74
    0x42c1450070031100c00341c40081d018001740a040300000d80500006101e601c5078004842d044403a406100500f5152602140c107844800300c01c00c18502072a064005810340349108440d0340c0d09264a90009a1130003018050880101c1d40c5010140f0600910b00880c00030f110351450b040c5035210f4040086084600411150171511402d0180c1d506540e0282d040006600e4142100d4402890054100c2d10806000d07142a140342c05a0740119170180103419500341510071000b80b5844c00b00c2c55075030481c010407070100412042c5105011180060b43c043c00203800650007000241040e0180da0101400d04060003c060055120140104000d10080d09040c2c111201d100d00d01c004280244010385441e018040400c1024929400c074010f03117078004c801d15001340c9008100c040c01a4940c5120400c81c41444040243c82007050110140b6103000c3e001903a0040043c815a002c100950307403024075580041e01e04890544060400348012680409068014211501094140908480c44a840d82daa003d4068060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 574216969 1250 574215719 574215743
    0x20a022806050f0708030408190c11090709180603060b041e0504020d330209010c0b09100204081b030304060914240d0b0a060e09040c0b1b1002030c07 66
    0x80c4040d002130301d02c12600300c03031178a41e02e00c0c2030b2a18029660188852400b140070240c1030310b00040c1305141401031650721080c0820125105001c000120800400170020480200008240365050303c0d0341e4010004403d0010400900390b1501c40142e0b140206a540514075040c0681000090641c07042c0d01f840960100045a03203e80c000306011000100300604080c1d140000403607056844d0021001400c40820f04d080c1c0c0501c0c0c604e24809a01c1141030b4a40000d0030718581602246855094507008502403007103131482c1034151116400d90b04242c0c4a0580d903080340719000f00c0200b112a440c1c80d0204214095490b003802c1c144050f04a540d980039803402d80300703000701410303035074441690607a100c1e40c14141d410001141b400d00040c4a41c48400b100038032a0a190b1107240505008000303405903442512070080d02040141886140a0010401d40d010040d600ac00203540700124000d143c0c0d10100c607054440c03540740d0100d031481c29544d507045604031441041000245051942540c40c0b030703a0720010301703214 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 574218219 1250 574216969 574216987
    0x1050403150b10230304111002010b030d05130b040302031e0a02030106151b11101b0605010303021c05030c0306030a0210120e0106050f0f0303040312020a02280605 72
    0x303080310307862190410b40f03510481c030115412214070502922507118455408000140c2e00c591804107840003080340c02c21b04811381030307407030f2010020361204620b00c0000385101d03005000901e0f10700d0101618010030000140d000680c8500320028016060760f00682d45024a5035010a0391120744081a24017846403c4154581000500c90007841c917400800034443d582d1945586d44141c06140d0b030b40008159244e038801180b800048102101c241c0040e030040159120005006107a51150846004c10070841103400019540c00d10005049010f0a40040c06604615000e46081c0840880280c100103603078070300020700d40c0f00341102e52008264002645035140e00001c00e103800700d002070081d8020000c440d04044540d1000b0880c04070f94084006101707070a031003003c817800c8440360b016554018000500c45542400c050301d02f440c11141c09001c0368940707552921107130400b09a8404030070041e00b10000380340552074080150005500542c102242c2d0840c540d15101c010516842040b00f4401c0106040034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 574219469 1250 574218219 574218221
    0x90b15030c0c16031208010503010c0f050a03060b04030803010918150c0507150f291e03101415091801060b0c0f0708010605030709051b07060b010801140105040315 72
    0x32103402c3c1c0300c0c0400180d200e1420703a0040ca80c0510341c000080c8060000a41d81c070301401084185800b80d00d03180d0617080d680404840310344c01898018180b5866800019562840e40001c00055000300c00300e9440c1e504180c2608142c81c0f4840b00390217142014040e540c00b01e1480002c170060789041c16000200d0a41303030b1340e09442c58043ca0501825200c4590590100003407182c01a5020400802040001d2600400c1011032070b004140811640300c0496003c8045040c8081c0c0a08a030126040c20546040101c00091402a0301c0c4510690151100103410795901c0744100070307070081c902c0000e0321015032881012900c482e00007021460b2856081c4125072100300300b0360010015200203101c89a80d944070310030a985c0c0e00542d000c4480203201d190300028031040184603000945030010003901005182072440f030060540600717441c1d04c0700305050b860403012410a00034025948200303004241c8045c0100054001ca005030f01502c87c3d010900008480d6a03071003400c54042d2980008004506910309600e44 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 574220719 1250 574219469 574219483
    0xc110d03020a0611073309150e0d02070b0d180f03020705010305010b0702010c0303110313110a0303020316080f04090f0e0f0d050a230910090e240415090b15030c0c 72
    0x801040c7c074142054061222007503500c10b03c2591618240400076541811542d40c20540c020200180c003c041c05011142500d0020005030f4826000499001c0700c0c031103161500300200d10100e441307000c500d1014003010b070103000580041409083c10441c96151081e20780a51044000c028100040f0401040170507010364000301c0141505000540c4a1030030000310b8100c44141d440c142d90710481c2da210220245414141801643c1d4564059400c000300000c0302288401c001908035085d802c14070409004c6420030700500003c1102c41e070003003451004007030500102c0d0140108100207411030b100304010b101c400101a40600c8403443c00b266550650741c4112100307200c01d11800c40242e080c2a4401e030326005000036240c0044201c80354048500c215000782c404000a200b4111960107080010720042240d1041d044540d00011548003180d00303900009040b600d04c40110301c2c0a10205c2803e200568030fa04c81c03070104032020380342010401e040c0d0001c04005e000081c0500d100000005490044180601000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 574221969 1250 574220719 574220813
    0x4180501180f0228020111180405041502131403010903020a020f040618050106020d090608060d0206070501020d06030611270307180b04050a09030e010c110d03020a061107 75
    0x5055604131203010200a550007011000660900070811881c1c020340c003c0381c101c1141c400340c94011544050078000a044000c000380d40c100103400e000d81401e0900c1c0010300207601c640420509044c10b25115803044000814202d000e41e1510200500190300014081c1e0020380441e40c00360146c8440e00040c002d4461030300700c0590000c0390844c0e804404c00542006050310240c0c2c090315001c0d01e68100c00c9071040e015200e00070002d81c200b00414001d00708030218080c0300c2d00281ca528078003017258480500366803000d42e56140d00c6139034980030003e00c8803030310172100c461034054402440d12085010544040c5014443c1e005070304601414580316030707030410070b0300014131070000c00014030150b9020032030051104d1480140968285000904155240d100b0040302d180d0588a0482840f042e1004440d4003000007401c80d90310b4050b2142102540e120a0a445500d119600908200c41c032803802303009481101090003480311041c48211300042071421180b602e0149400f800403540100c04421410081c40c080d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 574223219 1250 574221969 574221997
    0x60c0109060b1e0901060c060209040518070f1a090301180515060901050109120c0812210c0a0c0501060306090809031e031b0c100504180501180f02 65
    0x100c00c0101c00e400040540100300c40c1000c0a640c141d9801150b00e00c065501d0b640106000010700c2214040d4a00ea002540103140040c144408c200c045405c8810030303a00e41f0034015610072041880c020801c648000b905d80300c03000580d000d00d085010030018084408540c040140810302040c00e8409500c1002e41003ca03140d980c618034030500304141c4400c94010b0b09050740c02d4120003d200c0d410410303035250486c2c84c181e40d071800310b0b80740c10500c98441000c000112002c034125100090498400c01c1030301151900905810b94410310703203404d54052285103850b100e10380000c1c0100802000d081003074880a0b019402e1281213540217203010342c0107084a400c02410035240c030604000f40b00c0e50034044d04000750142d00716681d24991000e10032a10010b003500a0080d0b0007040160320b280444400e21440315503103800c44c5c080401200010354480302c1c0804640003d140420304100f10742c000b09074108841400141004a035062580940c01c1c0600b80310100f81e030b9521500441c3d00b01c515941265100031035086 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 574224469 1250 574223219 574223231
    0x40e0a0506250302090a03061e06060503070e01110a0b060a03140606010f080f01030222090818010c05070605130503011a01140405010503130611030c0d0632060c01 72
    0x32020381a4114402540d0742c44000001c5140034081d200711000c204000304041c4441e4510764800029080341050000e00343c4008580c201070103802c7c014080a009161a2240c480c9440760004000c1606100d074030f41045000c1a03c0e15281102190700c040c13440e000380c08040b6954030900030408458055200410070003100140c185035210100b449802850240c1e60440c20088424040b0341d80c83c0180c66030080310244200410040c40c2c41e1246c6035120034a00d48030500c041c1c1611258003107030080413003582d80c030400040850b074201480c5110031207003109090142d00ea0050340c441e960307a0303152030080710103220000440044641d10000702000825004000f88078034044513050070385411180c0e0b5501c0c049541d2038540302842c1110400d840c00d85a042c0e5950307042d039961a030381034000020510240d0300103035150150091280c00380e00462145d02408441d0f030741c070580100100b0031241c3c1d0340c1c49107940d13220705000b40000380115240f0b84080d001c00d85130012100c01e07600014410f48102903141c946c96113810 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 574225719 1250 574224469 574224481
    0x6030f0816050d11100e03030a05101503151505120a0204030c0311120d140d0b190e0708040f0308090c0306100303111605010c081303081801030c020705040e0a0506 72
    0x900c00c20b85000481301036405d00c81d83c1e003160f2010b6900311204040240c00c02e00018141010641c8220b9000450501c58119a0703580d0406d90190880000c082000940760190840702444440c150001409038003424508442030140050842c0546002d001002007200302040d03448110f901a10082c40d00512000e61069403450011209102d1408550040c0e0b0300c20760343d1042c084c0100300c01368100b0890f110111801e01c2034201c0c50a075844100e0410105540d0b802012031038560403107005030300b141070003881c005600f1324091483c0b810000b014001000b016004001c00100d810b9000d10310183d00d404e26030309644501051908003610244140e070944151020041038890015412007201c0c00f0f501c03031a60303d90812401c0c3c0d459020740e10b035038000081c80309401c10155202e15580d451032802841020b08240e581c0122410a4680d644155003d050202c1c424244201103002000a08002d00f000c00400300309840c0070b9103c500030f21865100701c0c0e4944106219007802d03c80c88400311b5101d41552040d01e068 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 574226969 1250 574225719 574225727
    0x6030f070c0218150109080715030204031a041a04080906071109070503070908060405030915040b03090a20010806130b06210105060a0210050703020c0a0b160306030f0816050d 77
    0x1241c48074181d448880d2401310550250394031178166030040025218090409006202e000030381040007040642c20000080811828082c00d22002e01c101c50a0149003041d04041520314800416141103114000c03c0c03000262814044400f0a241034a22644030f001c0d0b8181200002c140c9900700390002c2100d000c110036150710400440c462a00c907111404c8481d1119125030342e9040807940240254410041f203d43d41c81c00c0c1c3d0088164004a0540502d4a502c0d948801c443d90000d5501200540c44490040c00b00850203400305601c880c0501580d0000c0c00e40c5000038007110000d000c0c98002d0509461064400c02190003c2c020304602900055544400202e10f03c1d624482001d00c007070301d124503000460140352500c115015400507500411902d00102244001080040c0220303080c1503007017090100b2180240b0044200c180144001c800610b42680701c68540002031205508052400006000041d040b0119440464000c00741d41d45540451745841005141302c5400f500c00e116020020b00c5a90340 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 574228219 1250 574226969 574226971
    0x90d0201111f050109020a080a18170307021b0d1502090402130302040c140d021614030c070911070303091b030813120804060f0c0b0a0b1207030206030f070c0218 71
    0xb604041140e0b0b07030381d1082c82081b400b8040f00c42c00024a000007088000c211604482000c20800c41010030440b070359591008a400404030340f10a200700401004201e07601031001010b01c1d1840810320910307922510020340215001340004040614889032420740d500740d80d066030501d04014104642d00d4400c08048503400d11144003c0784a641820a4075600030b02c1406550025840c0010540c00c20001e0308408010350016500010f1214641c603403000840d1030018891201a558400b450f03440559940c2c03181484807a801003000d141c1801050300740b403494042201d1050783c00d8640012001403518224101c0da0401e2030b80000100f6001c0013006229002c0c0c01400340d0003001c414400e04680d00c1d1096400800d00304030261140c0c1060000f088014000c40e2201c098000c1886c03c07803d8004142d4400ea80c8038001c1d00c41c40c072059a603130105811800c28910907200c507568100282001403965000502d04d2100428000070403031842c012400307940c00341c00f6441d07030301d94024026220a58001c0c0c801c040c03414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 574229469 1250 574228219 574228273
    0x70203010605030a05030901080a0213120b060f1f170103141c050913140c34080c07090603030e010e0111070b090f03060a090201091505090d020111 65
    0x101c1c094001600d8500083d6a040180d0700501850400a009006550301d00c0010082d11603a0b40800128000c6041005500050310a8038008407210b141800c0516013503034010501c80c082c60158074204100d0b981d01603504840401d902001d00010114002111201620b02c000c03520010760a00100802c1020006942d1a1203001c040b01c4549441d1450402d0504108105101040c000c02518504d401c1c0340229401307540c4034082c0403c1240142500700300d58070301118150001c01d004a40c0d01c0300881c051421000114081d40070002d4a14100300030f8041c08814140100b1114001401441103202401071000910f481c00f41001400d0762410090301800c0100d0a442c001000e031a03102d841580100841004804140028941181031103202d840c0d40d4041a06198800c04c040441d070403503a420040c1500c50f604540d00072620061502c009881c5448a80041640815080c2c0000300d81ea80300d0240d5426031412200c4240c4104a0300040e207070342103c3c500c12282030080c40c4024030b595035201182d5003894 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 574230719 1250 574229469 574229471
    0x504110c010e060c0306010c030905090411030c030d050313020d080304060c020c010f0e010f05270f1210091a0408270a03020103021e0a0801030b0603010c0e0904050a06020f07020301 80
    0x10442c8a02c03107840d40d90845003e581c030041800880c2d080c0d40b03d0140c003588144070f8109034000e151903400241d0079207011503003120380d06d58074440e047c0c0504041c070110301482c1e41640180500da0246002400a01004150550000758130440c04159516010f21000443d004192203580c0c0c2018244080502841007502c00944142c55010b0f400d544100d001403400038036681d4154510301504011101c1807501304614007000750500c08078044210040314218041d440b40711141e00f8210100c10b101a100d481c41d2010310506904401103448c0d000803c1c109901603d0070390000d003804107803070034010100c0240c0b0141c0d12200321901300010000000010020503d0101d0300d1101d90b1031080d07c0d0520070f00e4031141e80e600440b139010204019400b035000340101d0f400524815040302c800b10851507094104031031003000140d01030300400c140651482ca0701d030001300c150000e10240301e18400c042d000580c80030b840c40c000c440d0140000e0510500380454051564044419556a04200c006100c15005410264869 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 574231969 1250 574230719 574230731
    0x60403050d08250807090f1502071d040f052407020f0609071a0d0c020105041e111309062d0608060109050403140d05010f1e0b090a0504110c01 63
    0x242007211194111000f0f40154502100700e6500c220f621060142559050050260001c07401c400c40e8071043c0003405040f41121000325920388001e28000a07030703004a5202d42e0741c01400314a500c01c0c244041d40300341c22074106003002d0207030700c0c029140c134030340310240805c401c0340410b90003290788480b801c01d000b104107508513007580807421030660b10341c54181c840031019070083c40104589090f1441081c2c45103a22008070342003030665801c9000750764100ca00013005075541c41c100003c0020341c03c884c40e07200104420305003200203260b881c03214840c030b40c1d40040c1c8100311391600c4204101c41d5810a43c00741e944140188000301e02800400c0303480034010f04200844068001c1c001e244034035480b0b94002c9070070314070040036564079203407402c0018040038206800300180c1c04040c45208000600412070510b040200060b00c1d03140c40000f05078080c0d5500055254204440c00115940501c01401c1c140e5804640c00b0380c4e1760200c140018031030505684442e403c03500300420240b5640d902c00291404000c3c1500034090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 574233219 1250 574231969 574231981
    0x1005011508070c11040e060a050103050f1603031b0f060609050702030a05041202030a080307020705010e01030216120e03010c0e0f120d05070302010609020408030a031505010903060e0c060403050d08 87
    0xe1180480e06207000641c100c14a00c0481d00242402d4100b804c09403000490000d544805410600c08580c0000910780721001041005001c111300c071801c0301d10300058951603d041d1500b030418801488098200481e01410801645442076502485d036809400030701c84207a14a800d001800240c81250240b0f407030100000e038203900100c11a279940a07550365283c50b050a18040608440d500b0344140d8161140640d4030700003841c0000114090500d0b034000b08009460100014030f1a8056503250f41007500520494042240111030074030b46681c48000c602c000d5440d228110303160385642142e1641503003003c4a04e8405034001e9042e030b044402c00d5808000351500030052006440c15030030401416480003428015182c801d201420201d4030034400814044c3d951030900c0306030307006600a201c071600005600268560036206440b4407180c03500c0745c100300d24030b0140003030320120300c900c806041c0790b0f1107001000c81c01d1024429101d01c00801420b0945403500d904015645049656950020848050100356 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 574234469 1250 574233219 574233227
    0x80c0a0f0b0909041103060711060132041e090201140c031c0921180b030a0216140a02120c03061504021e09010311251410050115 57
    0x20303103520034080740c6404040c0060000c0c0c2c030f00080040ea185400602a0081a070702030181034040d460303554680c50b0404140c01c8450030220107034490050154400844d140700015a03491594810070304528299402d070b50804a0007904c2c9424400a0b00e81109509041004c1e10323520905640e4006c1c0d8910784901c86e52080351406100e000c1cad8013000c60340f0030b2052030307000240c40b540500210b54100d00491170b41c00a0380c40c0e01040090b501104182c0c00703122404045c1d5079000300c42465000c90038400410803403800b030010545201c0a000c42e40b081e03400050044200c525021071074080e44e03000482103810500030340e8864940032665801c91007552080805044100c0006480c0d60101c001030203021551208002408018103041905402c95001c0c0030481d44803490501400c081c03403058004a1303460340c3c450001400c80f0030f82c1a0031401c40c817040c03192904d00340000080101c03040f0b00700c0e8104207200240c142001140c4c0e4041a9003200d125010581146040710741100d8101c6c1e403407610054603500c4105050b2 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 574235719 1250 574234469 574234499
    0x20f0906030c49110607080f07020f030303040b1f05121b180604090f052410060905060724060612021903150f0603050f0714030f04051204080c0a 64
    0x95103040c95089010013142c02400e851010510007031900c0d00d00011a078400c01e1075000041e56104112000c01d6030001d60800e000c0f000040b400c00c40241d440c6103080d0740c4a01c20b007400a0540c03410900051429182c048800c000c403c080c0200401520000145003211503641d260951901103a42d400c1c01c88482500381721256484070510249004496924901480001c11880c0340c1502c00c2c0e510500c4083c013080090020360040d02159401154402400151281190010305204540d04405d10204800f640c00255801581c60444029030b81d01551308000c440445080f00c4080c1c151900301ea08240790b412680b00600310381c01602c40900d00750003441c1100c102c0c01030884400c103098142c6030b07100800784070360700056a400c03c40c01e42090191b101c90503040102c00907000f01d004203665509000401c0a40840c4a03131000441c82d120010074600060042c0a000240c14603050340c1001e80428100b0401380010100c0045004009440740e03a514942a90b42400008081c080c0d048403001081c401c0450f8406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 574236969 1250 574235719 574235839
    0x1b090402031e0c21120f090f060c01020c07060906021606030216050115060314060a06180815010501260c0d09230d02030403020f0906030c 61
    0x60081d206001e600d40c02c21121042e03088a05000321003000103503503111000e0b541c104042c4201520450a4032040c1454200d04c1d10191180301020300104280d10050300c01c07104c03e00025038040c0c40080c1410701180d11405075551510743ca50002c1042c40101400281c940101c0f00f02750b581c01035480d80c43c030040c1d0300ca100b100100151915007a00912815009800804006200c0905103840003904d0f00c410f030841e0000d0041c1c3d10701422210f000c201c80e951501480703040d00a0001e61805a040c01d0f0001507004100348100014084189011a40a0550a4450300038045082a140070701e845401060307402d0780900640b404902c0c015041c6020800890000c00b80090014404101e5142d0818030345003900f00b40f021118007034407048410d0000382d0400c4c100303c0c8040c1c41200b50f0710100f144503055080c005206800001c652040c4810009669401811000f00c1410f44800c6d40a0b00d8100c0481e0900d048219070303540024441c80c54107aa220164681c0002d200303000d42900c1c5014036202d05800d08c01d140b1100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 574238219 1250 574236969 574236973
    0x181c02070608040201051306231201030303051003050601032609030c130f06080307140d0e060f0910021b0d170a05091c02040605090c070b060109171b09040203 70
    0x20602005000b103100c00d82081c01414070700d0034003144098441c070000b9550401c600103210a031644195192140d46091a40c0b0060078103030400801c502c0702c40011070140b201604140d00c0f2030114603401004244c2c80003440e0000140d490540e1070f424408641029841d0680d03007200c01441d83c1c03403148104420380308800002000742100124400c1000126581c0100d180c10035555461070040142103031003150014020140510b0300d5021505046032103c2c44400007034526005101d4808650703030320280c600c000040484140c1d40b02d00f046886407078103014444c00c2c03c1c3c0015034071414015268002600c410592220400e108201040405000c0c0008980c400240000b210b030000c030b800c40107410040c00c01143e2038038146040800701b10010300c05003410150751000c0c0319200d4005080d07003080d009140c090001540ca41c03100b41000032020f01e880c030070180701810102500c00429010b0b0311422415000700710015203810710101d4000c4080e00c511150f403143c4011503480310228880c1c1086868244140e40082c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 574239469 1250 574238219 574238233
    0x1090509100e012c060f041e0305070602070303050a0608010605060d020304050102130f09150b09010f0909061d1014011b0f14060702070506250803181c02 68
    0x3032007405072050350320030b184075502c441002e051001452090346100442014840c401e240c0b0010035401d185014008042e4108a0780420001c1041d03000209444030209440664003016414100c03031a0003003400c010305d924000a1f01e00c0c18036505070845402801c08a50400005585824941c222181c9102d1190041800d1020920490480d4095a4020701442c0090301e44030311030b210300c0301303904558000701c1524030030398000d0060124611403000c0401034918042c11090800c104070380c10340213044000741000342d041500d8041da03104020140c020401340500f0300002e503c0300140a03400f00d8400900101048141c000f45824a070300d1400800c483e043e102068070050441f004441507043c0c103003001c0e4420032101c2c807400007405081600484074041c401d880050840c10000c1401d02d08040d11210031544038a009000c2551140129601070310300d450282d40001c40d2281c000e01c43c05030707098041c042a00100030403010781d002c07211008004906405440b100e28052005804022024190f01c00581c4400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 574240719 1250 574239469 574239493
    0x90307080a12390e0a03060207032a1e0b0c041505030411010c1412180118090507030e031c0507170a050a02040806070f0e330705031201080601090509 66
    0x301c40c400c251005444c06030880c0c09a00c001c01c00c0400c1d00d91044600c0e560006040c014589d108441141e251131060009034169810842021007140741c0e18090883d69001c00f8800b100d00600030148035003640480d8000d402e1810030140070680d0428450422800604070b8414030700b40c80340c800c0b00e105952000c668a01030a0b0180112941c591549003140c05940c0c06090316040d110420074850011206210309030f0b0b580c038100b00141c840b521a0110350510026503146490b041c0240161800e80790300c403200056561300d00d40128043c010204450340e56000008003180e1240f0a00c640c1c00391090045000e009035100c1b0001251040f83c08980c001e001020b07440815280d031280c2d04600e40141c103030f40c405420240c0380c42d0943c3c101602035403c400852030200c818000180c12545c40c0340203440446030240c10b4040702070f402207d9640c80842d00910580e44104220044100707050792045500401180d454024011b002a25004c087c000d00015200b508000a280a814003a05115031031030809401c41001305 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 574241969 1250 574240719 574240811
    0x403080901060e0a180f0c03020f04050112020d03120c0804020315010b0313081905030f33120618100501270b040f09020414040c0e090307080a12 64
    0x1701d50842444800f421103503010407401421a200d060040000b01c00b0145544108882001000902d60150f81130000410807198000c014060315074054941400b003880c41d180840d8901030b601c070390400080c58200c11440d00c2c1e03404031003a03106038070076030440380c107800013008111088400348514101d8000400c000780340b50351b007101e800120750b10030300c41c0700d0034143c002c40c08000440b00380d8020000604044100241072902c00c201e01d4002c9100e01840004a1264443e4640c84106a2a5146c0708100c2c4003102c60548801101e050113080107803e55549003441e03d48000312203d9a89034040c51300c10404003c000030428803d40341218074050a032102c000703910024500350440000d0045901e41d8840403492186c40b1070140b60f041c050360480018070480240f041204031b8500c800c09820780c030840020000040c406010000a03250041d140003844d5072581d01c4207265101e0300100901c3c43e40c02107031002c802d80d001066010540e80580c41400203035100806030700789420030188680c041062480440300c980360 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 574243219 1250 574241969 574241981
    0xc1e10050a031b0503070f0906051803070503060906101d01050d0302150903130e0402090a020c0a1202011b0206040f060b03030c120903010b15030a0b270403080901060e0a 75
    0x11a0070042140c1e10a01e40741c43ea011060040c0c00003280300001041006984081c070071400c0186424540800c2d070a01c08018080e028026140f008280052208582a60100000b4005140c0142205c40b5450a9001d4235190041643c50841c0d1f4114801e0215403035210b050300e051044c62810111072240c2c030b00001c01141c021400c00580070b42c024000c50740c895165000b03500e889580200000c50360780641007042e1070022080c0c0e10070700000c0b504000340030050341c400f04644d0300103070340703280c05a1910540c4001c40d04020384100010a00b1208040d42007141b60190060205000b01201c01154512681d000380e8861600300e800902c000f111154003400103881d82e0045480580240031241400000005a0324005031740c1c5400d01d50190220304da800b586024058200d203110191400c0c0c5d55520102d80c0b2101c907003c090300b00340d03c01c0d0711581e004849032035610300346110380c0340f1840504254180018003003040700c05031016000150030800149a007001409002c04803000c00f0485422550f403048c0311343c01040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 574244469 1250 574243219 574243237
    0x5010213051f08190e0c030601060908100b01050408060112120e012f070e10050303071e03051e0702010807210506030a170406081f18060b0301080c1e1005 68
    0x6900d00d000713640e10b1081c2c00c1d124011500603c881644603040600c0d107031050b070001c010004004024001d458010079088012030018802043d0340d0311100c0140c5080c00307940c028050b07903c542c500000340601c070719400c1071101b4060150656640c0b0319100c112120320b01c0105c0c0d02c1c0459440440509c4070030300e65a98080700e050b2180c0f039a01c16075011000c241401c1d42503100e91200c046c1c4c0f40c1408070845d01e024003d00104801c800441c03802175241d845020304514179200041440c2c01c3d0440360149400361003101e00c92561081010507046c207007440040550852002a400103900d00c000811300c900801212141010000300a05100b528504180107071000402254250040440394030014a100150103103501f00285000d44450401d0710040048100814100c8000d8a202010308004000b001d41e4003a01c1d990754210030380c8502d914400010b000254040081c06800000025102401007140404d90b2011031700b0b06541d0020403450500c20143e4404290b2080780700f80d80514a41c013500080901350 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 574245719 1250 574244469 574244491
    0x1110f030a1103011e0f03053316261504021b07080d0504180e0319030605041104140d03120216030e01050315060f040e0405010213051f08 61
    0x4079214442c6500f90000e81c85041054040f40c0004c0c642981401031001074601241e646103000d1960b19000d542d061aa4030100e644285801145951000b040c19603201d68034543d0101000d0270000c03d01800000c50784ca0550002d0380782440a0251400099021002d1080203000903881c2c40b6804069061000d580060364015400c0214801c015891103403100036000150142c5010340c9405030b4541003d516260901c10010100000c1c4108008020b164100021341c100024a5410310000d09185105003840c04d02a4410803080c2c00c6030a9060b04400e040e54400c0c0d40030f001030040814048414007550103020036014460028400f682440c0d0440017400303010b8a011301e000308221084c0f030200c4e0710000002c0398041c6030508083c141900401c038008884028a802851442d00c520755900707424003030703900303600c00c500c001018010348003000b00f50340c0501260100061141400e04e820790007580034a5003240d009401c5c040c0010140742c00600325081c011085000790042074180c400725000b440080034100c0701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 574246969 1250 574245719 574245731
    0x16020d0e0406180515030307050d080604091e1407120b0703060e090615010f0c140f100204050f030a0f030c0201030213031104050c03090d1803051504120201110f030a 73
    0x103081c038810015410300e0802d400003a41d05210a80f00a80051700000c58002d61081106000185000500850003040d9103010300d2640c959400103006404092400741000351000b08002c8001c641000d102c5511b80705102c54034510b808190300648582291007811447d661182c8008042400e40414581c811480d240c00a0400d03101c2c4002c201e03440050342c041040b58489020045003060020180060344000d00b440c040810000300002d04040300d01000030061184954100618a0200040e40e80f040f507141c15a5442c240301c902e1000250441e00c2480d100700c601c80d000c42168103000c102e0300c8015803c001c0c070120705003e41e1410b5030706550a031000c0741019401c1221412115000304072401543c03141c0c2c010ba6800d03603075504110640e07070081d00e1024000001c20900001090025520040044d203042484406541c0480543c0341446684042e0480c010345a060501c6102e000302c16210700d104500c544004100c40758202d0803681032400446002c0820000344200000c130342e000d958006100760003c564 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 574248219 1250 574246969 574246979
    0x703050c2b0219180302061b010e01020c0f1204030f0b070504050607060605012d030e120406020706230a14091513090509030301050103020304080d050106021516020d0e0406 76
    0x4070383c0b0030803a08201800c140c520046007940070b808a03c1c2c400d00c0c0900c181c0c105007150005005803140140045140c0d07440284861808000e40040504100410003151202c090f10300f680c0d2281c12740d9101030b02501443e80d401d01140301c1c800c1503c064981080c1c9030341600082d41e891101141e4041c00b01014000e05000c0080c2c190f603260700401d806481048085241d40ca0040054400c40c5022200d0450001030414840d84554440140061902514001c20440542840d09080c0303809040a03042600c0001400f190894000811900b1540196a40480340d0541400c0040c0340703050341403420301c01c04100000345400f03110710300b18031904503254205880c040c1c500d0005031081d00807100311511030102003030700c1d0405907074250420020283e08505000c9481c0c04e140198032840140a480c1c1410350100105061095607011f0340c02c1c030413038ac6c84200004e58664101a40d04c890a203400381c484003407800000c0400b01340c440f0006850b0140c0e0000c01003614404002c1c3ca00603030650395030350895130f500d4000039 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 574249469 1250 574248219 574248221
    0xa0f03021f09060b0306070e0f0d0206071b0611030a031509090507080f07030512030c040506040305030304061a1c0312020409021b0601081b1305090606090703050c2b 73
    0x741c0c001c00180300154940d06031038014152162050014803940124041003100b50b041a0300d10001ca000b205c0028420408000150b4404a01c400c040e400c1140441c0c0c200c100904e02808004800228103070540890303641d0004c407003144150000140c260018480801d81a0203600506031000302173703420500c407075181e412002c102c0d0b1010805030390940c001c400c100002c8905102810000040c07501800301c1504586409540c1c4402210401c0c05000000c001621761196800b640c000e010010080f5030f540b42c2c4d07810910350307980080e00c1c280d44e168905031300081281c490b0120001c9000016040102c0e82d0302902071401c03036082c10380c825024003807001501618480300344010320152988420058031034241401080b40822524020140c55100d24014815400300094410000440c04089030207107850b2000305103010f00300000d260322103041c1010f128081002098041c480c01050f61901456550032800710140c4009540e0085052000c02c44045011b0701500e503611042c0e1340310b000390402203d070700d4590 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 574250719 1250 574249469 574249513
    0x405070504091209062c06070807030c0b01050f0a03061a090a0903020c0d0804050d03050d090c03031704020a0b1b0703050307020310050c04050f1f03050a0c030501080a0f0302 77
    0x940c01c1d4818010040c0e4107412920003c068401740c981104050050480328461a90100b06520003032a18400743c65a5034805049a5400da80a22040c0d2a0f90141c50080c0256080c4582124190841800860340c8e00340380390b85058081009003101104d510750f03210764000744403060b444160850100c1d01810191610401240529000400000d030b044407410000d05083c03024550f244900c07a045200c0c00410300708005d179401e88600700c1300b141c07644010303140c15181845a01d10024100d401d101924040c46900f42c02101241e02070f8a81e81c4c00343c80907062a90880004490080d400420350320240302115650010340070f901448901c0ca510612000d801510b000e59641c0110707202c2d400010700380210b050502c0200040b400c0031000340300a0804081d1036003030f80100d00409004921503882c40003190384012102d81411401000720741c0700c00025100138040c05044481f000c69501f01000040c600744a0b00c12503040340d01801c060072902c011543c1c3e80806860f040340070b4045100702100c4aa14100320481d507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 574251969 1250 574250719 574250723
    0x1504030c06060821072001050c120306120109020a061d1504170a03080705070c210c060c02030709090614010e040317061f0504120c05091b0d05040507050409 69
    0x2007001070300c814aa0281205400701c5402e1424050101400160202c0c455411944502c9401004001b5600041700d90f4054112080700b90b205d0202c3c504e0003121140c0045000300425200c04010b60060400603081c0d940b001700094001e0740c030480802040388035041200441108001480340c100030030000070341040300101c141c44ca8041c0040d08105003940404e003510f17680481405069003019646000d4614100109041c050150001c0c0041c104904c403c4200080c0000b21650b000401250802d01000c0300380080032030303503040040350105500303014003003186000341d0040040001c181401c1401c0301070501100101d60b400d0319401040003020340000000c0c0a000d40042000040c501380c24014003e0340030b0f03100104030161078400d0020940301d15418082c101c02140c0c4034240e00b020100b0444a0f0b00c03032640b01c080d40b01038190400381004880c5500e001107400c102e4240300309880b13104006e0b080745203480b007645e008441000300403115400e682000e9401402001907820044d910700200d02581c1c0c0c00001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 574253219 1250 574251969 574251973
    0x30c0717010606030908070308250f08060405010b0418060b070807030e0a0b0f1b1603020a09181410020a030f0c0f2a05161a0c1504030c060608 63
    0x5030400315031092140b00700500c428078040c4500291526210007510800b00c000d000c010350080060072076100303c42d00c00100108040c0070280d01c00c7d050b0004000d10440d4120303800203074000c0d001c18070511b0540181070603100780b50389442c900303450404101815070030203038200c5c0a46e494001c0021540d20300743c054040c440c051070909980b01168030b00200700080311103d0328401d80c0400b1040c81907114410940d6004041e0584003587c81d00c0c0d189098030840095104446103200e416850113400070a0707001c100c1202d200f65040c2d1040354962080e00c0984c0c0c8849007858801801d9a42200801d40c8821103042c0c18200005030341c110110109050141e074040198800800d483e081c0c9643c083c0707801d200d02d5a000d04180342c06444c06440c000024503a80d60840c512003814200805243d810010002201d0610ba014007241d110340c0b01085508a5031250744146070020b81004a05c1c000d02c60002c1c115101d8200e42405051201c01101c810011150090000c2d010406565903c1e00002d90034403401010340003000c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 574254469 1250 574253219 574253249
    0x20a02090f0907091e110c0d051803060108060403081314010c090b030708060105030a14011e0e091911090703060e2a090105091e010314040f1202030c07 67
    0x16091801c000b5901c8000258030f070005e542c0c0081d0a9002e0613107108200d40011802212039110a80c05c0e0003650b0b4445240c0c02140588586650494001c2054940780c28070700d00030300300d10010562941c4091280c0d0701907401060000380020310074020300740c1c490002a048071141e042512a004240300039203131209960b554185010159400a540c20300822a01504515501d040c7c80300509168024214a051003070210128504241070f1b00700b441c0006c0c0d668100a059030f52210004000d108a0344150401c0c070001c1c0f0040f0b114805410958452800700300102409070401560100f000030b4000d05540f04141d0341c460030303026074580329800d0141906a40101e052802c00002c0022900094a80c1000c0a1401c01800d5400c815850151200241010341078039072a500c0300684152080c211095880481c14408103102c500303d0a80c200095420b030b908015503641c401e800c2281501c00d03140a0248a04402100001146034031108000712291042d01c0c01d000e01456200d1624a19070040c40c4c045140d81 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 574255719 1250 574254469 574254481
    0x90a050303041a0a1b0c020f100503151819060e09061b0a0e01140d02040b0c06100308030c030a0b0901080a14010912051318020711041515020a02090f 66
    0x1500f031541100f1002c0c810000518064140c074265202814007a0601200ba21107006556424a5145007680c02a03e1001c070b034200c4c040300404641c81180d1020341942c22384194042030401000c0007041081c03010144159849006400344009201c181440145880d0200400d94041002c00781c0d0040c81e5800084c281030900b0341488500340c0c5004520480d046003801a24607250f403103841c4440204080c00c00140014540c103c03220f9034418070110f10200e0340001400107100d00070100a000c486003400c1a00c0003520362441d83c01c0c0d1003000d440050541541840031400c1c19030800f0045410091511002410007028000300d00b08590076400801185c11007402501808210021403034030110043c000c011449040c1d9403c100c001014407040d04115000c1000284070300110347e1000a440f00f120480c0700c40364100a400040c1d03001c84401c95440c400e0409a104078100342c00303107403000c0840c03001c03800340c19003040300c00c106070300c075988184045119001c0e0b090302503268451094080c00f5442e622035040e02d441 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 574256969 1250 574255719 574255763
    0x20729070b04061a0f1201090c260303010810050c070b2e050306040807151a040b010309020a030b06010215130203060615030a020f0d021201080111040f0e090a05030304 74
    0x64030005200407221141303450a44e60b0401440c0403031003c40b18800d001c08440e42041c0103100d40800108502c2201c4808100a020349072110111240880c011910910035804140c40740000c2c416800311f5440b81070108241c40880c3c201640c485002800507003010460703168a00c0c0b01206035203200f2040303007203035900c2c01003c0761040149c0100c034855400b0100901d00f0002c00c0e61000c00500c0034040c2d078000714071308080204221b0140340101c03000b0010f10074003402c595a00d00201c0500c110310310444ca0f01c603500645502a004050303c0940040c001c0f4442c1d0f2861f11810000130004202034118010400da0314019028903043c0f5011f10030500000d40a45130034810b1601e01200944078034802c480074a483d40340c1000440440f6404071a03108c004d61100684420712159000320f1103514038683c008105510004500880f05040b204400001e01051004c4908180e0900c036600440341c078101300d00300600040307040c201d01e19084007010046808910640e00e0b16801c0d60016942269417000010010101c0428 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 574258219 1250 574256969 574256981
    0x3010c0f080c0a091724061003061202041508030d020405130b0319020a0b0c0d02100506030a0f020a260d0302191d030d030b091006020729070b0406 65
    0x1c002e0349241503110080602614200e110364609004821000a04010140f003048034540c02c17900c0e1030045806100020091060464030700d0300528100e200e141c20346100340586c00c2100c00303032003450282039070a409200141482046d01d071052503c000c8005105d060800003011105d400c0d0f100103840ba130401040000162a041c00000c0c0c803409c14030049015030b4040740c0420401e4142d00907201800e00703840418294849544102040140402d04449450001c41d64030641d411030b60a8074030f119881e40901c4111001620719580640c00b00c91020000f0390760307034001d401540c0020409aa4941e40ea101c141301c000301e01c0503500340128045c40d01c80c01e540301080344010250140c103040d0704002031088140718107010840d40c802046028003c14440c124601a2803070602d03005016103030000c4007080040e001c0e00c450211136000c0c101281c0010041c1c0501880c00054850380e5001d0a410f924212100300684103070034140030440b04256035204030000000c014001d9900c95080c2d104185003504080c0100d480c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 574259469 1250 574258219 574258231
    0x923130203070e1e0303040e07170c1603030e0d0f02060a110702040b01030e010e0f0d050c100507091205160603140403080711010e010b1f141803010c0f08 68
    0x1005000b03001005800c4182c030800d02d02d0a4a402284040107404461444444003003140c240c040054085042420181d10600c20b00d26030301c070410035001c03040c0e50401103c8103c40040c02032409000c09100780c000880c01c251114040e02c0c0100d940711032148141d0400741020800e0010410300240e00180e250140645940040001401c00409800c020111020700c80c0300380c005c1c40341d66201001400d0341c1c0240e00200445001ca4002c1000300904000d15076510280400c04406102d0600d44944642c451401c03102240c51080c094050041d01088010140001070301c604140300d0660008030307155170403a42c815021303030040b4020160210969900c541c103900c1500510b00309030403c0c2100540cbc03c10340e8171403a00550b140c0791040c400e559464045868440b4103902107419420104030760020401500820b2080004a40107058080901d03560644c030552400028040307036001500d40075080116004e400c1171014681d40e00400030a020000f401c641000341e0381000302b111001c5203106107910450315540a9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 574260719 1250 574259469 574259471
    0x303090608070e061b06040311120a1b0302010e0a080307030510030f0311030d18050c01030c0210110702060c0f0607020d12050604110f07050c0405070807050a092313 73
    0x814280c2c40200342d066249215802200b00144d10f140c005a800241c0d003003000c1040580d4801d00740b6280051603001e4484040c64a48600d02c1040c000000900445855203000e0b180d424007000f2041c12000040740a103810703003e6559580891000400c14041c5520799807184111b00d0307a80c60035090141c21504090005440c42c0c004c0070007800020b41c9002e10560054050074006001030707400d031102d403642c440d01250344090303803c0100307202c1240c00c0a407500a40324410310a8500c0e814510b0011012211090200c0300144c0c04000c1904442e0320035030040c4186045a00c1c1f96141001a40201e5216482044a00081c0d40100b0030424982d2040c407815400184a1002d4617005036042e0340206003c00082c511700c101982c400118040b80d07aa41c0c032003000400c0f90000b480d01c66600c03000310720468002c034006660901031031007a40035a10302441500d1160119403038504164940700400c80b0540c01c01074607102402840c000c08150103402040c200c091645000784504c6c89441d10301808641d11320002c9418400f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 574261969 1250 574260719 574260721
    0x90624060306040f0605120106180b0a030b090703021005120615030a0e03160305040f1a030c03040f0b01033203040501031806051e090f0c04021b060108070303090608 73
    0x5540c4400480b60810811200420006200b0f1030010007400e107580001c1d80030700c0007980c007a1b0711003040d0080011a40c0c5031a083c09004841e000c200244c0314a12015540007114403402d200048bc034002d2039800500820403a0207107030301d0307a01048001c0e08001c12040402d102007140d4284101200800d0760103601507802e01f0000c2080e00b14803d00d40409800c0b0301007942c0f10b5064540440c010001d4882c902e5584800c40d118108500700689150f201d40201a28140100c4022940c0341034001c2d401e03140b4030340c01c104920315900d0a588000c5600040c0080301c4548050300c103400490780141d59903019500810540e01c0d4454490404c1040748280001c004006a00900005c280c4601209a070704031074080c02c000c01c102071403540360b524017403a0b490020200e9142074284603003010804803440f0b00c0002000074904540b100c05c1283da5a110020101c15180c0c00801861241e040c690080c29031490703840f0020091040c4070040d9810a0026008401140d01940040003030540c44081d03980140a05d00380640d03a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 574263219 1250 574261969 574262041
    0x90a02010c030f18030b10060801030c0e07030f022a01090206040e0907050a0b090a060509061905090d0b15040507080c0705030f0f09030c010806030307170706050906 73
    0x44000c4070500a814001c604401c14419030103800408120400e0024800350152030340b501e640c0700300b0242d81240e0080e141000c00300d005402402070300d040e03076001000c4000803458007000b24034480000701410105600d540030a02d1042d51030000c1d012102d803031241e5000c01170320380b246140c0081c0f8618982c0315580c14104d0000c00b503103c0c001203d0030340b00c41c1070b000c0420b581c031180070034600506c50744010b4014880300000070703003201080060014184125041000c50b0b0380c0d8403046406001e243c201990141041044200b06099101c040210090600b0418240705075074000a080000c001410f9030f40812000421a00f081241c451103250340d0215410031007400d09920041402c032001300455040100095088244002007007595103a02c01c48050f10340d02e410040c50035881d6089104035078040c1c494200448440e40c020000c0510a0b00050300071400c00354961202801e49001d000b4088001f0320401100012a42a00070f507407058502d04010500c0d41850744101c060112030100010981c19040c0d61403107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 574264469 1250 574263219 574263227
    0x90f0105040b16060e030c0304030c0b040509070e01022a010e0423070c0206070c0816150f09080105010303050a180e010e150907020709110405150c0709050f0f090a0201 74
    0x30f100311a80ea015840c40c1c0c591902400400c041018029607200101d5840c101c010b00200030b00c11703288a4881b100d00207945002c0043d060045000d0f29920030b10714400140514030840e82c021020303605204480501074404012144d102aa54461010446600c00240c0b00d58001409100f005015582003000111510401240780c2c10003006461007120700001c20105441780160b1414a90001c22050380d403403852401e4503120312288105842c9000d00c220f03007903851040b400044125600c0741d4002c0c0201c01a50070484800d00e041c0c14031428444400008910ac010901c6244c0c00786119440d00c41da210302c981c001418403d0401a0814403800045041c0300300f9204000990458020a80c00b24840c4c4601032000d03842c00420b10440d402201032404c020095600041c048215818910100140b40400584070081e114034001c0c96000360345111040100402742c801400220190000e0743c1c095500ca50050054820540d0b07204900c54548050040f81c4031442445900200004000d1618040541c0068 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 574265719 1250 574264469 574264477
    0x20d1407110f0d1e06060905063729040303020714010504080d0309020f1e060d1b030c020d0525060e0d02060f0906040819030605040203010605090f0105040b 69
    0x15018000102c0c401081d074540c5000f488850340d120480e0622400c02010f49034001c03103080001d0703c115091420000701c000d05c62203603078040c91000d40640e509c0050b404400e078005220b408550009100400110380b00d521002c103907006095141c07070064270030301c01000d0107010450341c000843d8a04000c020400001c1d8000950f80700300e459458842510320704a1005940c2c50055510010b900d000f81401001d2a613410b80c4010001c5100701d40c440c2d1512186028015540300403a0070b10003000100c4c1c600380c29803414101400306021a0b00c004a40901a00d0f0004050f14a4460301004262942940c08042ea01032005609003000c900d0f001c1c2c1043d540301c0d464881541c0d60b08104480c0c1040e001c03404284003417a003180d035094240108480300c480038800003c2d81c0309400c80d840d9119001c40000325441c5000030600f50b0055802c0410281000d0000b0320024144c0e0540d85035400b03060751840000b84075203071800510b0003403689860b25521080c0d100d0a000c2070340000c803500e44c100300d0100414000819080203035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 574266969 1250 574265719 574265753
    0x40b0c13061101020715020903160503070504091b1212080c090d030c1202030a1d03030306011808011e0c030b012a0807230102090306061c020a06020d1407 68
    0x40c05052611060034020f101d040b502600101b0010402003521999030002d00d1700010507000c951000d4016050401408100d000b038a81c1504411000c110030319190f000308020a01804900054003894542800401495402485e40d41c070b036091081c05006e0340e0907010600220b9814509402e10b0048040382c200d104000fa9148216a00049041814405c0404c2e89840b40e100490340010503004001030b40c2c1e5007000005078001080600d0081c950903207081e14011846024008505584500c401501c1c400000500d48240d110300d0b01000034400000d004508840e403000001d481c400100c3e151000c10780300b1034040303d01458140540d4014a0740c0c80a00c0c2d07987d0988055a945180218840c1c400740304d0005d5001900c00b110124a1400313121090000381042d0b1200090b60245400c0c2c200250309070702548030056456001a8002280750070210b1081c03040800081412036800c51580c00101d5006443d00f000f0700603403001000700001c0c0e03003264481009104141000b810614155200d043c1210b00e8104 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 574268219 1250 574266969 574266977
    0x5040509090a0c0e09010f060506090d021f0509010809030c070b09040906020f0c01150b0403110a030f050606010e0a0810110909040f0302060717152403040b0c1306 72
    0x144030500188404442c9580c44036404164130350714405003d1840d0284d403407000b113501e8061515080c199030b1140704104c4401070310301414105514100402c110340c000050384c10001c0c43c1040c9502113160b20800402c0d80c216220300740c403002c0160005040e00d60040045c40a68010004c91845c8800020003c00310b80c180c1260300d03581c8405a01140150031207902c020075007030000c590280701c1651003000c0c2084400c441c000b000020000403400c0c03040070152140c06402c1400f0041800400c5440c2094407510002070201200c44e5541d540f4110313041c4412100f900c03a40c0004007801070725030788205640c0c16948102c0340740c032200d418114017035142d66140f06002d03078140c0c0d10010703201c010101c1d80603030f100610014510049443c2c1402d00c180001891780e011001030081c80300040c0c4140c02600e00900c500c403048810082c50b920031a51300f020040e4403510742d41c0320203182d10340c0400c1d01800b44505da6428500c0b5507291282484e2030302c1d500f159400b0307083c00d00c0514144541000b540e016001c440031143e441c94 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 574269469 1250 574268219 574268221
    0xb060d030201021b0a050c06032202030106030b150f040506061b2e140c040306090c090c05070506090a170703090b031315060b0d0e0c130603020a0902090105040509 72
    0x14050740288200400c402c0b04da200c10f05650305102c00401c481404034003070402c2d07074180f440e6901085020700c0f04640c001c5008010540e40d280824004142c281094400380001481e035490f41c803a8691800c080341c005003806d1609103001c6032070908100c48041210103440602040c1440d400241d100d003e142900c443c14640703400161035000e0704202c000219505040c070740e2034000c070050300803003101b018404101d54903003000030b100c05407100e000c07520f4070941c00f8414940c105400e40c1d443c040940500a23042d01c00540182d008200c130341c8903102c1c041451b120340d00c1d5182c0c0c810245c60140d0501000401c80ca615402c100f683c10082208901d40d001a03440f0441d65075a184c4040c5010765120390540c11002d140800403042107520100b0000c403650490140c01e0046540b03a0b80010030082d90058021050b0b20720090100041142d40c0350001b005840350501a43d170f1282c4040c0c082200040d8404031006040e484000c00c00560070072424100141540c02d40542c540007905002a02c0780c81903205460007448584 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 574270719 1250 574269469 574269473
    0x90308130f021201051602071202060a030906060f05100e0306040b0c1201080c09060909072903101d0c040b1315080f1f030818100c110108040b060d 65
    0x10094100c807a074000c02c43d0345460800c614031030003010100d41d01100c484c00700540f2080c2a00003d1880100d400c1e4204505020755242e0907c0b80503046207526030103140d103441c0c062000510740d01554000e00203600c90103c1c164540b40800c911246030103854014080780c5c48820185450210710b580e801900b00b081141c5544a0500120117440760360321043c580c000307210012420304404141c40038034203011103400120b52515003c0084103a4180d440d45d00315031044c0420046200c0003402100c4d000c3c0f10800201340703004881303119503c50b0300846400031186400c0b041800342000f24050200700d551800020380403840c061101600d113100b14040d030030748000b0110741140c00360800040e00d00500040d0300c10346401e008043e0050034610051341c00c40b41c3d00381034070000f4003880e1a50804422080400d03917061446071441d07e41d100c00e94045681c91004540b120145441500d65207a422081030302d83d0340325a242074003424901801c00108000d503040018a509220100e0905088680c1142d0100c442c110051014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 574271969 1250 574270719 574270733
    0xa02060f070507020a030c1d13170c0a0b0f090303010f0b300a06142d12100e010504020609041806150602070b0309061f0302030709020d0e0109030813 66
    0x100c3d00003907110344003d601004001c030400300881226003051450402000d41c40704104c0304a012140649100318043c5500041004511844d0b022564850b0151400905121282c2000712141064911406060501000140408505510140350f1001c2d40c1154104108910f40110a00c01d403018071801185a100e0213424150881d4040c40d01142046180482d13000c620100e94104c2c1c5c104801460f10301c0000c6c504020303221300700c0341c0d210003000c809044a09801c940100d480005500e24070052440410415440c0c07001d0818030100b14800030422100c04907200d00c26500f030340c05500303038503410f00041c4001030703c07480c1c103844140804503004654030b80c096420440ca0002c400000e004241000d514844c524502344504051314500d138251007400d510340c5007440580c4810385a05241c0c1d0320010000e4100c00c107403100072000301120042d0300c1d00d0664a4001030714104854000e0001103900041e0340c50720b1a00c0d84142480180d05100910088015844c00b61200310014020040e80307001409030b100300102c07 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 574273219 1250 574271969 574271977
    0x804081e0a35030a0905010f0c140c010213081f06050f1003020c12040918020901120201050c0607021c080f041b0302041802100809030d090614070e10050a02060f0705 73
    0x40301c42c0d6203489141103e0100084c003688102994594a445444c2c05441d006010b50717040d551103034a0740381c02148000d0103c1703070940c040801050695400d000f011251a10100e028009252280040c100406003070703080780b100c201801e102601503103403810421a680303c522158144090880e4420303410800e401040e000b83c851007a402806000e0752224441541e0380350080d00550b24010410000a0450b1600d901c11006061010754000090f000400102003c50a0321003090b20601d4030ba414811501d075490325180d400d44403880981c0001000d5014100d1040f080b074a400100e18101c1c69030304201b010352a0640300544041e00050300328051503002c0035804030034402954054001c000510016400c1c0421601d1400100d105118501110010a1085114a000b810640d024510304494040000014240d170305007165101c0e01c40300701403c0c1d452400c59552152400f51109003030843d1840821483c0d00c2041030403014408188840f080940d400140c1d0350b802104001d03043d1054481c240d00b9642401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 574274469 1250 574273219 574273313
    0x910050d0804050d0b16050a091e0b0a0c02041a0d032a08031909080415090518040203060a1e0e07050925030b100c0f0804081e0a 57
    0x80e04c04002002640e0518903c44c2000340c004003c01119520122001c0c480e818820340069031010090041d4202907143d43d0241c2e0b02200000200c9039181418180d5402c102220800f0806800482d402c0d824075010f1f140020860b0491100945402c200007140d803550080e000c0d0400009a07943d94281e06000c001343d88c00d1003c0286039141c02c2d198500700f503442d841101e008040c0c020311a0070a40030b4039240104041250b124460710704080c00d21040b03900f03c420300c0c6c1410040100700d002c0000c940d25802200b84110b4560083c0d203585140c9801403528020f00500b8140105250000c00c14041c103034481040100c038409500421041c8083c0403c6140c1200c5070004c1e1381c88032a4009101d510120b10029980e809086201d60411030b0030780130b06030704981140c1d44054011180301c46e011651807060200d100c0c00791040310be0f504d40d0501c0d40c45440c210780107034101ca40654810040b40c4007800c1e84200165840e0680b0008000e240784940d20030350281030000c1181d500c0c1509440703006040c1000090140200 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 574275719 1250 574274469 574274479
    0xc0c12050c1c0303060f0815150a03151803091401050909130b01062d03020c01060b040602070b0903121e0c063c090703151401050910050d080405 64
    0x41c0c0140744200800b030008030202c0c0828605100019506d900c5400c0d00101e564000107880c05000c141000390607098014122803040d04a1442264540d0395006880c000c2c50103a802d901c2203085204041044039148000d10680c03074000c211220020354080105803d8a802d041c940c2c0701c0441840044e0340d18050401042d5011481c42c040210f040c803151075034201030740203400c003007902e99842c0010355442d805401216642c46410300c00710301a608801010701c2a200500d0014580741104855074210b0b001d030340141210110000c1c0402400d0b0f81005030300003038100080050310b4902082d0000f6641e01052030300b150030f290049110294a5a909040421001000c241a81d0b4002081d821610707000216512078190940e81000e080703c1c400010029610745030207108043c5e89101c441c9001040308010017900b00c903c501c61001c0006102800c200742400381000c070204240481d0206501490307416044a40562521010807130105c05600749582118403d41c0e91114000c1c15040030b100700d00c038541125400c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 574276969 1250 574275719 574275739
    0x6090411160b071b0b060109030209070c030f0e030304051c171e0f070209091009060609050106051c02070f060519050a06050a170f011103090d0c0c12050c 68
    0x1007400c00740400c0c05881a4481c0c001c90740c2e03003c4250f512200d00b50100100c00c800900c20000110b641e101c6540244050425234440c1da075960000b003001380c00311502c4000611050b010b07010150810780644007002e8a0030b003544034002c4900400e99034041c1e44140e034421070640c41d02d0b0007845164600d0000031038201070030650105500b0720203109903003d1303c1d90084003c080c07160f039036100034078205488000d0800306103280750a00f036400f000003080e4041c180500d1030250041c2c142c2080010700c20008994030582011410528128020046600590044c000d0040030442e0fa4a41261155400d241501d4101c00503241c203414104850000e8000100a080740e00c0c2c0414031060002e0101c07202400e5120b440180200c3d501c20f10703600d00f900c00c18421a40c0112204500307000c521580c07601c00d840e810356031080380c00111000701454203488040c5680344520000205201c14208140b08201c0700c0d01e21801c2490003444d4655914414804502c030341543e05203a00901d80822009111400b19001c008054100d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 574278219 1250 574276969 574276987
    0x60c02040906020903030a0c0b0112030905101205090d0e0315180712060203010305100b090a0b010302190306061205010e1b071403090406050d05060103080309070f030302070e01060203090f06090411 87
    0x7044200c8107003912140250000003842041a1207403000bdaa45507641501d680d14010520191200798100e20042c000c840c41496400714041c0307e400d1103803901d1801000d01c8103940f04058407030814801c600b8040e8114000000804d1541d10950380c104454860380c1d01c01a0a14503154100059a08441240c00c1245003000501505401031410703217005e00c003038640c0042507a41c0041120f0110038160b401410010006054048a50106500030410705000d4684100c1418142c1c84000c400d1000e0042039035681c080c0011540035200348546500750b4410001541403a8100c00c6400c0001c1c15451886107c003004102c00300304000b83c4095540c08500342c0104490403640940300d40144062038010383c6045400119454004440a031941c5c1080141586900f540c40d02d11040d4001045841c0c144034000d8001115100d06d404807008501941c041c1c6036450078071034400100322040e84848110350007400300164980d100d940c0f10000d0780c41113440f40e540e810482c0102e030240c030740311008801c1600c0c045001d0403 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 574279469 1250 574278219 574278227
    0x1218030a050a05070303030605030105060f060915030103140c01020312150d0f0317070f0c0b0c0c300a021506121f0c0f0f08060f1203090910060c02040906020903030a 73
    0xd1700e10070344040c0801c1d501d86c018507088440448420380d100c5040d401d070340000e0400c40000e0844481c080c0811140752940322000010768020380c000c44110841c43c0d092172403030005010f20103004000348061490034403104160203c001d03002c1c200c194804a03411244015694a501d012842179004080400c40120350401410461800707041c09031002c1c0d0340300050603da1003001c01d600700c000c039070701c902900300143c2c0c61b060b0548a0050024101510402035084d03c07220800800c0801003040413910340464a011b031490680040d84a245040a4240900092146c0101e4200320310204010007a10694507180010000701700500c0c0d084031400b510484540f1001c9140c00e401c2031608a030418888900041c4044030301c0700e00403520000003100c0c0b111841c415071090202c41c0d0070640042401b030f8101144000604011000e0b00460ba8680c00003a4031403a50520700d94032507000c0000710740f040740d803450814064282d10950100070711039940c3d400e101c0c0c10800c032030703040e10400c0c0f01c064120381d00d03180b820780050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 574280575 1106 574279469 574279483
    0xe0303011a3702010c170f1e0901230f0609040501060b030705090f04061a0d0e0106030804170705030c01050a0507020907051b1218030a050a05 63
    0x9400b1030510308603164141055001038005001c42c000a800c450358280118240007066030300400038844032400507130001c061820010f0a941c4c0c0800310030a42d455601030403804081109000c4c3c42c19056010f02d038841d0403010740040900204540c0030b2074100c1182c2c02241c0b00c8040002881c641810240950414416400814200d07154001c1030419002110048002400881d150760300e850400c003d055803032000d442c00c00c07500e410b01411940c47c881410280c00b010b00002046200d085140d841080d480403c10001c204580d143d190400c0640c2c0a4480c202008504a200b031540c020085054003c07502c1c018000e03e0300400f1030700150b900c0d07045842e540b0180b240900542000d038a0740c26540c0c1c401d40103640d800d540d5103c0c240e0410001150b8a40080b4a54040d005480e1401903060498889035981220003804241603400a071401d981d40700d0060650242502041c00c1050002d00d030 = true := by decide +kernel

theorem cover : BRFrame.Cov 574100719 574280575 := by
  have h0 := BRFrame.cov_init 574100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 574100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 574100719 ≤ n) (h2 : n < 574280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
