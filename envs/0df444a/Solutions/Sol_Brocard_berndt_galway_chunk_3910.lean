-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3910
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:02:13.140336+00:00
-- url     : https://prove2.me/submissions/c2a2c2cd-7068-4bf1-8d3a-773da7488b7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 703057553 ≤ n < 703237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 703058803 1250 703057553 703057601
    0x90501150309030206150f0a080309090a11090d08040306050106090e0604150b0d060321120e070605130302030303042a060f0c03050f03070306080d05161113 69
    0x100300a03040800605103400c1001c264a070340d00a4a80d00c0140c92550603402400b10300c000340c0d0721a50071822402c8000d100450031641d9071030081d200c0e0800d5100c2445a08a600082c4000210b8002c55440c003030542140ca140c10914420400c5080708050242d81c41e13182480044002641d9104850281513103441d00803034030b494003401d841d40100c010002401941403049214801c032103401c0340c07404e0b6681031402c1c1e521481003010b60710043c0000e1f03002a00c078510380d01103905030810341c0359a0058104103960b02c1d0b542c0d0381c2e1040b990081e15104800310380d443d4040b00080280314810000303011641e4160b0a014042d0360b580d00003a213160826030f015900c240e400743c0d004003540c94902403124140c0c41c0303064542c6402d29000e40036005081091650742484020000b0400f0140314030111440541e41305006900c038100400000d00030f00c41d40c080d100041c820000da1040d23460081c000e03158002c0d01c2221840b0402403035511425a16501c0880344d030002441648d05501940d4dd006020b6420400c034003d44084030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 703060053 1250 703058803 703058819
    0xb16090b0c0a15021c02030a021314030d09230604080601140f030627010e011506020d0923010512040605040b0c090d080a0e0909071404180b041b090501 67
    0xb0080500c00f03842c4108100c54240c2c0740c0f8081c3c0400702c0703d8000011784070b650b020151f1020f4814502d80030400a550f0f50b000c0390301c802c44054031254a0080e82201e1810b482d031031058908141901801e40788105ca52400380210f2160794201d07000c1940a400310341815601e640103840c0c50b0080e002a05452034080c0341e0801400c2280c0c00590708901203000701042d003046000e041d10303069400e0056420300d101e0160303900e60f03490035000041ca18006c00000c01c00c65100c1c0d1146031401c10343d030050100600940188210041c41140e8010079500b1040001c031440d95100b001c005100d0100724030f5410b2040c00e10013034442078100f400c002d101e9401040082101d14061030266011300e401000c484501c00309002c222126190086542a940d9001340704594808155100750390b032590000980d94000c86000421540c02c80100710481140c21164144443c441e40c074040005890500d0341000e500003200f00c6140115100d034000c030b604503006491011001d000c40203640754844136900315801c1c940d220001085141c1e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 703061303 1250 703060053 703060073
    0x12040b01061e05030f04020103110a11010b0604031e0f1502090301150b0a14040b1c06080d1e230406110c06090d03030b0405070306090e0a0b16090b0c0a 67
    0x403200d00b40c582600c5a20300001d440341c000036041a02c4000c811340007404590003940034016106110503065181e85040000400e190301861005070325508000d484c40190515070183c40959500000e0120b0307115107a000108031110b6032100b81d408410030300d4070001040b1616034194520760401c10143e138a00b6030f0003c0c0750035031b004090401d20680c0115000c004e401400010b48001240c0d5180c00340408020041000481c0125040241e15017000101d4841011400d60001c1c8001d0b00c8441c1444196550f04000b0386404200c8411804116040d9601d141001103507050120503a1a01742040d0791480c80d0aaa0000a807d09521841c003034000b0301405070a40180c10f4100c0b03840040e0051040c10030300c8010480764051110840d014004030320f5204105070007600041652a030240c0100a81d01e007400c03000300a070510b4415400424900001092a00c00105c1c442c0b90030741d0800c100041039104c1c510800d00c0c060800112004101e041c5001166103100c3d0001402c600f0301035001000c1180c40c5007410a122 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 703062553 1250 703061303 703061327
    0x506010e030d0503010620010c030b1c2117010305060910050903040501050f040b1201030b180d0f020a0c090c020d23070f0b0a050114100c061112040b0106 68
    0x1c2e40c03040401520b103907440402c49040d100c06280c0080064003080b020911410303541360074202c5508010034003a40581c503a0102c001030310203c8030203c4404028410540042d408800078124480300188020040000c0c1c0d021200842180707802d1302882c0040400c01d200080c01c0c4c00807122038100d142170121407001040803010507844010104403908000c2015a0740717110b50312460741800804591074441c1b01146080d60010402ca1980030b513a0040645600031000090100325040c01003000407440a81a5101e0640108011002000c044480c94800c0c5c07201a5045c0c0c107401180300303414580c0002005221300358000d0407220340124003c212801c0103402c4c1804445020204905c281320945030b005500c3c444c88403481c000a50035510741941c20b001c074020000b050081c001001150510a81c0520b03640000e04031590b040d6000c26182c11001000491003602117202d00107420310a907030010625990000000c40c00710031806140154041090862000889041d646000f16800420540c0e40204c012010303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 703063803 1250 703062553 703062559
    0x506010329120d0c12080108031812010e03071214030403030e010b0913151505060310050315040b07080412030510080f070f050904020d0f03210506010e 67
    0x1d188104502600c03000080c034254199400080c500c0002920303400d100300c85a44580041c3c0d010b602080e18041e0103601c003000100c40307194003d141041901d203d201c4281c141c0d25400041c620f00b80f0342c92400b080b9142038084040c1d2014140c00b108008000900c41c0d000b036500b11801960311075015050440100001207140010700028442160403401601c2c116548075615040c00202c141503907102c80c0c010640004801d802014410502403401a2608814602032190403071076207503941036000d0702c1075544c0340c0c81c04225102080c1084c821807400401030355010381421550f04003542d403007000034074107041c03440543d02c00781504061005024000c0c0c05143e101900c2c0c10456a942450f03a42c41803d02c00e452a0711041542d81d10104950a5a0240c460000c1038043c0841d0300005c00d0f01d0040b5240c031001d202e0a44140b08900d000a500c0c10510807003442036400402d0300610b03490989681c00c3c24940e102d41107040180c603071210080c9004512066403200bc0101002139a0300d04500090064403410b99080c2c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 703065053 1250 703063803 703063811
    0x51305010311010f0509221506090b0c0a05060c0702090a1413110a031b060201051b0a050d0219030522230a0b1005061206060711040e01090605060103 66
    0x105400030000300c4180b1080c6000d40004d01d0903c804c403428010640c5542d8000c20141c43c0c40000e801000b440c02a10303c0440e000c21000152000003500308140388103850100e0700d0701d0402c0140c003181c440030780800c41c0300d041603071120b07288c42e0b0790a82040e00c01c594040e0000400b00302c01d0b065081c03110000d40e00101c180c0b4200440c0c4002ca548200d140c90061000303040a42d54503685c41008401321030780e00a071401424041c1803684a140c42144407003030280304c80d5888000203000a003d4030500480e80606aa01c007510000b4000401c5064240c0c020018481409020407003500030791642c1c80103245107599050801c0f0b22044500000b4140c0d01c001e001c00d001c48103042940c809041c4052003602d81c8030b50104101d0143c542a4100030b5044c00007549154080c002c0e8991a0240912040d405101d402c080125034141907d8008110490044611480740418070900043c1e06042c200001c22106010340c01c0d84010f09a41e034001402d80344e50b44442c40442e5100c41c4e40504026880c01002d13040207090800348 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 703066303 1250 703065053 703065059
    0x50306090a0b15100f02191e051e03220b0d051510030209040c05030106080c1e072105040810050a020705030a0c14060c091e0a0f05130501 61
    0x395500074840002d44031181e4031011600b10441500e801c41c050300090899030f14071400083c00b0b055031110300040d41c098003c040080c0c00410b0810304903440f26a01c602070100d00540004924a10255104115018844e104052800d0142d10064800b46608400110343d1034030780240c000204c54014401c10030038080c036501408004104030aa07229543c4c0321200141d207680728036481060009044815800180c003e1149019aa01d81c0007441400825181030002415a00d011540b07403009101d580c00091251000c1504102030000038a0098820341d140b50355072484001c150400e910003803040314242c0b50810302010401513006850201c21442c1441ca04003840c1076407040d200c2010308014140141d80d1300002c0e222444d568180d41200307401c4030850703448002c07003030010300004440e034015030f090003110520001c034000000d5601d205040c0c1400c0941450159414050900214442404000e0046079680e0b026242d42000b0313402040c2001640801d1403a040c14002c071078042e43d28107045241440014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 703067553 1250 703066303 703066321
    0x40c08010c08060607110406090e06100501080f090f03030a0f050703270302031612020f1609050430121107030804020607060203041112030c070605030711010608060907050306 77
    0x2040c0d11070030550300313582d55045900e0318402d042c0c41c6802d0740398070502e4a5004140c00c03036151300c000ba41c08005000c403a2680ca8410f5a92001051403044900033901440011a010030705130940d5000242c80040b1020a012200d207142160403c03540c40e44084d82e03450820b042c4042c203000d526007046060800300040140036059002d46c4103190308050580d5940040c1c01c0c100344c03003002210205102c43c3d0320403400140e149450350700c040d0507810041c0144684c400a1039078100100e00d00811044140c0c20100b040d02d080c1c203200242200400980e0144183c540d4284014846a0203080c1400106c080308000d80c01104003a2a0803241c0c0007044065151852207044000f0210441e0001030b01801e154000e95145e1001034968414a0b030000c000c18004001c0c002002814512001110400c4a410351404c0f030318043d4940d41c0c01209413040781c0340d10503081081910b0080d8003c54119001f441c00c565002601c2b17041c9400c0d0342c0c01d5482511160312540400c95000f034148114400752008070054200d5007400c01b99 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 703068803 1250 703067553 703067567
    0x5070c090506150f0c03160209011a040306090606091e1b08041e0c09091a0c034011040204030510180209150103060e06180a0f090803040c08010c 64
    0x189a0f100300007440c0c4c0740d07150f01c0b503095891070310401045035510201003107940310715031110b907049005109030300002c1000e02e0030074513400343d51000041e01c0d4141403035500c1f441c0c00303404410000c0d11044d50303a0001280c80b60142c0201040c03102e69803440e01c86407002062000032074400e18158035004000c1b8000e805c506a00c90303080703078210b0340120030404007102d4810754114030024a0001001e8504a0030f00080d06042a00603881889c029000164100e04400d1000321071401280c0c00c400284c000c00001300c000c02e8102105140f050b00104807002403542803d640094440b8229681401d03080081080800143c0181d81500420036501541094919035680740d8440466500140040d00e486038021140001162861100d80050800d111801c007a1005d000748030441d00c1407400a401e100c40030801280c0c1140b010300511000e01500c00d0303814420110105034001130002d01803141c4544003000a45800e010302c05201c2d00440d0807a60720f0a107442c080c018841958040e0784140d0404c40114151900009 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 703070053 1250 703068803 703068829
    0xa05031002310303020106060503070c030503190612050c0f0f010c0f080f030621031e0403060606080609160903080f13170f1c03020c100c05070c090506 67
    0x120240c2c65040103410b44002ea901800b1081404071204002e410b5a04140030010842c0d0184c0c008211a0761140c00031100c40c402154400045421403120700d002030320400003168485c8401140c000d600001c401c0d080e0a6400a9105200980891081c10144030b1b0034080c482440c0004c41c0e01100580c4510041007141821b02c004a0500100503226414011318a03890301065a00641d0955685203540d4101c042da0000ea4043e030188210088441c02a0404d00c01e0400c080c400c403000310304240d4a01c540000d0140c0d0b02c0340040742c4400900c000030006000780074600240c40c50b520340e00b46038501141445100d641c000c00c0d41c142c15001400720f44070150407004c00b0301030341e4008000030b1f533601c01c00346019050b104584000012000c1000d0002d1006001c0900b03844410318081a580c10050704803d8a0307854000200043c3c2584001c9500c902030b41c080d0f4000c1c030444c7d880e2001c0c0c0c3d0609410b483e518089685040704140440c600040c20401c1001c241d0444010f003043c40c0080200313041c01d101040307095000c25 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 703071303 1250 703070053 703070083
    0x30213091a04080325080109020d0603022d06040f03020d021807030e060a0e060c090102280605010e160e01180f092f0d090206070317060a0503 63
    0x20120809104040003181299000c0710810000c5080c98a00034001c1d5000301c1d0001c030301d0346000340d805412102000702c0000c0a40d0fa40c0c0d070720a01d07900340000c52000b036200344050f1040360769500740000141c0b1041e15013000791008141180c201d03d050580c0407541c6036144141846030307508110500040202070411001c1c4e07070301584d400c02c1030340c440d2000c00d16508541002d400d41c80d0f1800e04002ea81617241e00840c0c05103142d001a40c3ca00e854401e00c0c10180c0c1c1e0f50080c0c00c136041e0814000140000440300242550440510444020840165254181c000c58030382882051303a5444801d010701a49018142c010103085c0c00f0a820f034542007065400c0c8840c120032140821040313502660f07640c2e2090302d9025001046100c40544242e40c1c8162440022031072080000f02810800000c0c40c0c0031305c03102048803401080c03207004040e03400b007407031550290311115546910070781d07030841e40025864410282050510035158200c0380840e002d10440c3d042c800800c4030348100c94110090007203440c08280c0313040c0814a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 703072553 1250 703071303 703071311
    0x70f0506040312170a0510060806181509010611010c050f040302040f090204020409140c18101e0e03010e06010b0f090402040b0705061602120913020c06040507060e010801030213 78
    0x94801154420304c8010024007160110b070500860300e01a0f84801e01401000c041e9080c103550b50003081d500d910040f1062075010320180e41c0141040c1003005050340c4440320a0703424880d042900001002e140081c0c11660019144011200c1d19142c248070340440c90680b030421609007a900c6d03902d51214407039800000d00403a190043c0540406190b08024125503000740155101c51b01d9140050081130114000c440c01c60201000c03034980072005041310f105510f285c591b45119410007051108412154500400300521300410f101c4000300958641281c098541d1511030070305a150415080d50740080b41c00103a5003190004120004000089451030b0800c1002d11b615910380341d0029000b070140f54424035007038100060510400a010481c18440c160720a40c5903d55161610101d07584e18000766044404d01c020800e140b4075180a20b451031005030800005480c100807552000e081c80d405031402c83d9642c0c8000c20034001a41c02040181c5000c0c03007071070039480d0b030347c0b640e000580c840d25118100300315140d407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 703073803 1250 703072553 703072583
    0x8071818020c01060311040b040501050d030e120613020a170d0809120708040515070305090f06070f0309090608010e0a1205040305061320100e0f10030509070f05060403 74
    0x6a01030710044041c2c00001c10405960f81424210088840d034228421b0b4074000f4108501d2420380715060584101a254400302d4840c1e0341d0654001d03640403d02d66011020b00c0100044141c2000740038424200e0b00c410032101c40241c0b0500c840041990032002804004084420b0709100020384800c0100d01840d0400c0c40742c40f490744140c00c10900c40c5c80a08003410001700501071041c4100200100c82c410746010240c000444044091350141d500b000780010407c12010402d0f28003a00c02c610703920307801842103243c8003440c2d8a1034200400075000b1030104040001c204140c442070b104201c000c10b0000003e011120070141966207508920380010600e0301c8010850f207441d4070400580300615030000440d1035900789580800c820210340407003103c00794685c01403440d00c02442140c003a0008005004010003119079035084d039002c140c0d45d49003508048a46070f0390089544201d10f403041d10005403030002c1c05081218216040031910780000314140010002041280c07103490813181240e400c100344901400d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 703075053 1250 703073803 703073849
    0x10f0513110a230c0f0c0d02030a20060c0c01181536030c1509030f060f0c05130f0b120c090a150201140705180f1f080718 54
    0x100360660f40d04840c001081c0d00c1601e02d0300084080c10f0001d0741048a94540d2114104280c00030350f91700c000c1d0141c12144036500000c40c216140c0f120260300380381c406101103015020500c00e1b048a508507550794000c080b0300b0103650b040403041e101103004c00f4094045609000f03d195171310002c000c01d81c0c200719101003164070400d040300c0a140d071540030100c86401f510384400880d1307546070a8001503610b04141c0c840000d00c40744002c8a81c800c9421502c0c0c0344000c0e441d580f118031641e40501c07020f6030782c0b944038101d180501c8a54800d08074051500d4842c551600085000b080b80b0b091290040b1040042111050060f550424203a81414020380344180056954126018040c003402940c0f94005944007008100c0c00482400303218405101d41c000c0105082d8800708070203181040e0351010200340d007000300603c2c003080e030300000c49601c1014000c650200076260200d8140e01091315240303189050440b0f00d503c2c041d80724098030f401402038540044494054180c1110005003449002e0085442004540d6159 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 703076303 1250 703075053 703075097
    0x507120204090204020a020c1003140a050601021501300203060c0a0908072417071d150405030d020d0203091306050325060302071104050406020f03010f0513110a 71
    0xf54007a0040d92250380c0100c1c00f9558401100b52288203c1e80c0b00400704c0b074941f00b4442c80d40d29504610391036041c2d894101d42c03a001000c2c0600040c5c114000c0792903880741c0c0e2035881c80c240e0080c2171202c4000c9000099030201028506c1c4694074031188170000003c0005a900040c1803030300444c80c0741c280c2c0d640c0c40d000c0d1401d407044449503010500d50b0141c9071f00003408681e485900c010322007031202090110082240f048640d00c680c4010b50174000041d0340030406942c400d5281150001d89080051101d0301c0b2000040c1a10004242c1403032408400941801281070034807164440c10141e000914451400c07400180d100d004200c101401500003010240d144412074002c64014500034090b50390b414016001c05c43c0d80c401d60107150580350444540040e13498464405c460109400003188070060360035800b0007002d400040c00a032211602406403180100d00a030040d4000d00007006400b0300d452030303e000d111040c010701c0114425a071a080b030340041d1400c01d800703c41d0515a45d25001c1100010508a40603072 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 703077553 1250 703076303 703076321
    0x80d091212031d0a0b1320120102180a050f010c15180302030a1710061211130e0604020403020913020d0813080705030a0c0314030c010c0906030c03090507120204 71
    0xc2c07000c009140d05460307002c04d1921006009200d0f001c459a58000c110700b9501503c10b0003020080044084941e1400240d04100750320750051198180c0301c4002406402c2e81c004141019220b9207a8000e49410700d0b0404503080188819038440c41444507120028260b034072444001340c0000d00186810080648551010405044180d00c4481c65400c40c10001c1d620f0304811800340104c1c28510f40701500c5011040720303d108140d1040480100f90a02e00d04072a21100e0404c0a0346485e01e4212054522502002401490070082162010380e03182c1244a0100b03400640301c07034041c030b1042009002584442601650086440b03c0da182010414804200c051030258000b40c05078502191100d00360a0403402d150450300c03914201d58900d6112001c0544a00d65411300624514011000700b00191805011296485180e0300383c03070405e10b054200030300b0748a031407a5a10003e42110824844190940300340852154203240c100000103942c0d5901e603855030039024014541c2049980d41d021542c17141c00c48000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 703078803 1250 703077553 703077581
    0x3060606090302120601080c13021306020d08010b0a0206040201050a050903060a05190204380c06160305040515130213050109060b0705190c0308070c080d09121203 72
    0x9964000060080781c4601049208654041c00350440100010340302d07040c1d461a0b006440088005403c0081241b20011000c078019000d20080ea110001991b40c08001d05503500a410751140d0002d005003041c0058202d65003840d401d022018585500046503603009134207007480c1e82d90300c80454082e210340c0128950309a00d4400d0b482000b00000250300814080c0b42510746110103050000706007400e9025034014000080c030111081030800203400c0420f81030380300079007240d03180041031500241030317074052444032030944c0c8084207000c4c07c0c0030b07503d1a003004520386150800c028103141c1e90f07082c0c4a41c2e03501c49078692081c2d0003010405442030034040710100d507401081c030211119522181c0300a407000344160101a46051000500071080c00120794125034400c024012102c3c0740403080c180c646c3d00b00030540d1442e40440b808400146007000400c46070380205248a000c82c6801115840c020403014602d040082e011020040d004a01c248040307440d80c058141801c0348010541140244419408211 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 703080053 1250 703078803 703078811
    0xe1806090703110409080906090d022e090509061005130305010e070503010603080d020313020d05210901020a15230714071101080a09050304080f06090a0b011e0306 72
    0x5140000010319008803440f400c120080c07444071000b040200c0702140c41c0642411800c11090032107160070801011001002403018402c00c0c25a008640241d02000d9a080d450324103014100040c661200302d06521301641c0340ca58007541c102004901e00501c00380445003e43c0102001c007824601540c1540d4407901600d08550407160b60f0704280c1c0c0600280850050a40039070800850342d820107001d0745080e680c120044c1841c0850503601080258802411200010800e42d52000143d403096547c8a841d03002c0e01c02808a0300b190b18505100b080700d014940a614420007500e8100e980118842d4896078100d88851542a581340a00c03020b03002c3c24100d88010107004103110101d076009000395009010342da65105401c00c420000b0f102c244200700010f0070760551011180f040d50704c10680c0991000b100316020400545a6a80351b2464215802407200781d002901a02a0405c081200303a03880a114002800140310319254a01c0c6c000040c0282c100031480c100d601e40c0c1c4040c10303040e443c00443e40071900704 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 703081303 1250 703080053 703080061
    0xf090a03061a0a090b03030316140a0e030c090609130201030e0a030503040302100204061e0210050405100b093d1e05061819080316030201050f100e1806 67
    0x3240d00c089244014840c82e0000350214200e01e0503c510307805c3d40c20243c000c42c5552900704140720a5019000184104149485928a80e0001c00c014108800b443c0d140c0d006401001800c16007024001310120b8002d6102104100042da20500400c0d0001c0d001c41400100d02aa4001240a4000b240c01c3e01d40c64844c2981c48030401d42e004004500c21270190382a00e0300001500b036100c2c140c0c030540c030039440091102641d01640300c000f005512464141c40c01120744143c00d895480e4180c0e48221016034854008040803000d10295020741c0740c0450086403041c1052419540d00114040d010310815168240c0400101040a507803040745030038001c101c0070000c5141c0d200e10300b20198140710054003070342489000008882c10314a0513600d41000300c030301107003a8040344000d1001404129001e40000f24411000040b800818002040d900d01c0700c0101c0680030000e804c01a00707448014010900c020300c19000c1004080c2201d45540540b480e907180402c0e80d444482c03800322035902640070404a406910240 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 703082553 1250 703081303 703081331
    0x10e06090307050604120201030e0a0f08030a18030e040c2f1e06070216060f030c020c130f060b09031f110309060709150509010e030a0602130614040b0f090a0306 71
    0x2c6d601138400d0740e050003405814490b81c1d85a512401c001042000b9140083c0000380444c4051135004181030800964201101402e580c0360048240540109003054a441194107060017440d009500b2418100c0340d0b05026284940700040145100903a5500b8840e00c050009040c0302c90501030400391004070304130104075600340c0c603550151403082c0540b044016081e54007000c995030800701da1454650a007101698403040d001b03819205201411030080105d030b0300880d070300c5007010250a10030349400900140036902c01012608290400103922500740085003140e034000400720109068594403000650356110064040e0902c021098002e00c4080104540d80c3c0000031907a00c07a100603a5001d40860752184484445800b01420760300180b01004041f90550041040d0044400042d045915004582c0c0f545422604946034070a08031441d5002080410f40c4000d40b1140031180040c03051616241c45540740d014450028580d200c4400402c81002555694590100564200c04244410302c000300300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 703083803 1250 703082553 703082579
    0x506090619172404020304050a020307080102040303080a090215070f0605040807050c040905100b1507080a0f17060d11180105360c07050d030c1706010e06090307050604 74
    0x900c0360450a14000603000000f03030006001c250b40007290040042d403c0b805020213540001e005541c1c1d440740c80f01c41e40c0140c808024040040a424000607210707070941c0740090003900c001d0116620320b41000142d4025030340e104800c0124101080c402d40c0e841c200c915000d00b05000c40d400c084c00c0c0501d0141003006200080000f8a101d41c494001c2c1c1d503007609400c040100f211607220b8050103690100c80401d03131040280e808628a0a03004020000b0945011800011640324540444203041d01040502c0c405400ca805210064420f0038071500401c20070004d2030003d90018041e62207900c40c1f046d01340074409046001d520f641c1001d00b000040010102d03004c08c014800b885514001c000c1e45d008805000c6010302402d91014411199540d0000080e80e0404580d20150a00c01800002c10070180001d41c208040d07491210561030201d44000c0805018090410481580f141c07102c001c0c0030800c15030380c00800100302c0a41101c0305525800745e1000f003480c2414980203030360004030008010440d0702e13034014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 703085053 1250 703083803 703083827
    0x403120c12060b130b0306040204030f060e06060a0b0f0a0504120c050102061f05040b04181101022b080703060f03060902190501022113030b0702060903130506090619 73
    0x24012183d40386040341041c4600804160b40481c080000c1c490b4030300032002940c0210b40100050300b007039103a40724004070502001084070610380d40d04805d4444641403000c02d5102404a80324240b03180740034030f242500c0c4100901e1401e00d50001a45c2c4404c1e80c001e600740c0b030240840529509143c8032902d044001540705006d86400b61103103800103100c915482c40c0351003454042c030319602e8000d8a0401488090300d0010400c0e075203da00c0b050758450880e44001e80700b49044c02003070045042204200060304208014120b40e801008a00340f8400701e00122110000c0340b4190702c0c05110ba40c0c1e400408034020141c98020380700780101e030507001090000c65040b95902c24002c450042040340d4130811010051114440c40b40503800c80000b211100d07000302c008241c1d290a42d80940c0c40d0a09450900500300c845070001c641803600362003404802c61b8104034507988860070b130000394902988610a02e465007028442c8a03c18500026004071645a10f015642810500582c80d059044207a03030240500d242c4076 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 703086303 1250 703085053 703085087
    0x6060b0f031f0602070501050d0f09232a0d1b06030b0609090f040c0510120e0601050102120c0f0610051801030b010b0c2121011d0403120c 61
    0x250900b50050206a4804450301c0e0f4000b80341e12440c003401540e6907045601450480c5980d02c0050160326201d0141b41241849011407484103034403070840580c8612403803074001403070b8401095100782030450060400c154107113102054510582030f0000302c800d80d41d41c8c0c006020414007040e0001080c0c20004039015201c071510144410300002041c00060b00590300c0d060b80c004100d4011403c0412144a4030340c01900400c02c0d4004941c40301c000c101003041003060071000400801c1840c2030140c45220382c421601404010b8803040d4580b0000075031b29450050f4240c0c80d0f200010301d41c0800f0f4002c0042ea41032850074010740c1d99a141c610b42c100c04010072440307010b000c2c280c4060f007042001141200395050300d070b100c0c14000043e42020050b001a401c9a40c0c000c44910542c02d05540513150300c030160000c20141c126480d034a000c1001119802e88000c0b0703035103003c00c0c5c003140144440d0340480649031402c15908415412643d4078142118a5010041019000e610780064071014960060040503a00622 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 703087553 1250 703086303 703086331
    0x50d020601061103030f071b050102130e1f05010e0f04091a0705070b07050d09140a0201090506131503060f06050712090b03070c0501020d06090e01050705070308070c06060b0f03 78
    0x490b0f8065141e02c402c5611050003a200c0000036046030054192100ba82051442c900080469070b907220708903030044090f09802c4101038001c01c41c020020006a5025000c40640d00b01d90040f0540703855126064000d103414040c4500801000c2d8032001040c04a09000078800e20030b00150341031294120a550200c038080c002d00328000381400c2d001d40c0c11100c50640c00001d0340b46559035540c00305c4242d00b007030501d204055240c002c04004100306d141702400421846014181c018032520000d0149079481d07001341c0c0102c105010b8400200c44002c0340f001241c80810480905449039203086000b440207402003040d01103020804203071603038000060240c25118080500e5140d420039800d54820196100326010700d10104005691644600c00110b01640b2a000160a01c07800b5004102603500c1508407001565594695211404090140b40d070031000d282040e0b80303040c1c06034030020980b5100402c85d83c14003081c101410b04006551f80f111005007039504040c0d031111000b050300b0070658070507602c086000000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 703088803 1250 703087553 703087577
    0x501090c021b2704120f09030f02012607080a0605030c040b0a0905070504140f100c02010315180621140708010207060507230928060e011701030f110d050d02060106 72
    0x2411b1002040241038071f07890005413945d03a070081c802103450780803410086502e2640200d0308041343d2140c942407812506100702d21340700300010452030300100000c00f147c1c20054100034985001c11740d069240429140401d80030343d050041503503a50107034030049a007442c0c4030810851a41c044007034010b0760b12407102c50304404450b5041140c50440070304443e6000304065158200340f0700800c0ca50784001d1040c1000300740781180c0d51044c007070741580d0740c0204518407060100305003c403084d102c2c0d6005403e007041411600d0a414140101b202000320300248190044a1845d17141c42c801c0000c4001000060001d5594082620b006806070005499050100b04050341008094900880c0c954000303104c007040a090401d01c00411111400c1b210090058020380110900010155807051029117066101d50b0b221098281c0010040740e40c001c4007103d4000303240c00501c009003186945c0c0101c40e400007117001030005501c001561030905444020601e2064146100d06641c001c03e15504843d01510b501c489450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 703090053 1250 703088803 703088807
    0x7030908060c04031a1905070201200309030a1b0c03060c1103090d0204180204050f0105031c0503010b130803160b010b0705032205060d0f0501090c021b270412 70
    0x600d0200501d9040c031440d44508007085d04d150340390b12a0741111201c0c030760706000284900b1104107642c1440142d4450080d140c2450411132240483d04641002c1e900d14541141a03607103d01410403104100070070380d03002d2143d00010059180600f80c01150301e24415039079140003401400049099008200681d210281105010081d034600b010701803d03c0f185c0c0d0501d6400c00000b070409042c40d50341c000c217811111026855510800b0300c60b100d10b08005144d541400101442d019040444492000340280003130b8003d80c0c00400c4d00d0443d908450b14586454408000d2440d00d02170ba0407a100c41c1c0300102e4140c0350352144503400302026003c0e0551080991300d81c00c0c01100c62160810191550384100a8040e0301c03101e40c0d0010105c511071006800c00c0075180d000007182c65003d114688201030322902c1d9680301201920500e4010300c4a01c034200051411880060f40351400c42001c200040c00804032a546522a5803410307180c5403c2400b03001c1d030101d05484041016030300751410f85209400f0342514210074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 703091303 1250 703090053 703090057
    0xf0203120d0b040606090302030607230d05010528180912020c0415121e020a080a050f011b0320031f050307061e020a05150421050d0c0c0807030908060c 67
    0x203230300580a0310885d502e030001603454201d1200403041c20104014100c0220740800098441c03410705006c081215450203007000380902c5022541943c50903940100c440c003480c10b00b001002c07a904070040001c0700c00f95500314001482e20001c00340510b40502d124000c00d5501041c07240410360212030400100c02101c4000e000a85d2a00900c014800b1a954030800304480031030380890203240b20302d100340b070001e6603000c210480c80c1076010b020a54403a14070481044070900c88030b04a004001c001300850a031803007085003290340c0702c00359205160b036900303403640c0c0019201c490120044007150225501d0820380800100c1d0b50a100303800201207821100405c16260200c0c1c4082103414598a0300215807042da1001c8900101c03400346000d40c4505201000026018000c0d8908035070207500050b50361400303042c00016003040304455032010405a2040040e02c0c1c100c401d0341d0900e25801400200340003500320580300c1000c5154040d110710000300705401003640c0401d5001c2501d0064050700d1082c0c550700c184521034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 703092553 1250 703091303 703091309
    0xc05031201270e100b13020a020a1401020a020604020f0103022b1103060d02040c0c0501290303090102122b200a1205100e0a06140609030304030f0203120d0b04060609 73
    0x35001444a00d240007503580004104040c001c2070030091006d500182400caa0003556000c000d40c00c0800c0050074040c101e0840744868034070070003d6281c084034120080d218040100024031074102d01c03466a0701d90b4461340c140d5000f0034003a0040035810010461040c200e104881038840118284080d4194800014064a0050b0f0003e008201210469401c00000d008280c01c0b10f02007003900006000498424025001496901c00a016900d802111b50266403184600d081c0d000e64010406040e180c0d07400a5003c100520003031350f440c0c81c1c1c000700d803150103c401881040075481559500c0e0340a86007195004140c031943e4101888901000304e0f600c45914010300080a020404083c0824284d8809401044c3d10500400b180301080c0d403504280c800400301982c0e8400000d9071280203214170180700b8441c174100c3c1000c68030341e400e148520700041d40c2c9108a001c0101300c1b40c0d00240f08404c6480810108000074154414107841c0c240c40360202c0d008040544c07011344200e04248000541c640544a0304c026 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 703093803 1250 703092553 703092581
    0x50c0d020a15170a0204050a1505070221030f090a0e090d0c03170c0a03051005220207060e030a1b03080f090708030418140105100c0503120127 63
    0xd0524000c002c01d6401503a081c4601444010405140c0399401d80c600f05200380114000162582e0411041c05503504107500a441d20b034401c08442d585850f002800c2e80c5030300e41d040302c00c540e040d818201d03120b20f0004400003845142c440401d042c02d0000d00701c8041c00c0840e005540b548030301d50b40d0350740c6052000c9060300c0b0003c40350068010000c50520881074120103d01074145051240ba011501c803008800840b03006c0d41075000422030901c4907500d8040d89402c14200c1161040c80f905241c0011403501408a070b030b80c029200051144500c03401074042c3c03900a034102c84104400c0800c142d12544951003101c8500001d0001c035003106071410301c1c80c004070807540c0655034249580d036102005880044007801c1001e1785d2140c00c0300041e25400400c001d01c0a4010924055070745041d4000c2a01956101541c60082180746401481542c4174243c460602c050145440c0f4080c14460414030706501c5156054110302d41200004929050141c10152800d0149142e0030b4011a683c0c01e0f01c01210001800c4801c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 703095053 1250 703093803 703093819
    0x60d0207261b01060806040b04060e0c031b030a060606050309070e0708070509011e0f0201060b04031a060a090e011e0203040c09150f0e010501030c1d19150c050c0d02 73
    0x208415503080c002102c08403000008420352500841e914000080360b046070f030007034808100010043d8500070380c0c0020340b10030001c3c9944621880043c2c0c550b282d648010100c40d1554030000c0187c0d4041140c0b032040c0e904590100000c81c0c95500051043c0d00868003200140b20340c40d0005012001d0041c403030300c02c001558623601d82d0340721070f030048840d684100d00c0d083c1000040034114202d081d0410b015100b14105459101600804840280c00d40310307540e00485450000380300070000303e8241021013201c002e00804958031551103600294001081340c12a40001d80b6080c0844040c0b8015481240c402d08505070b002100b1040500c2c04017644801c94008000384413003002007007040060b400a41c00184024050303910399403244c40400008019903c811006070703144c40100f00c00c3d60140300d00b4001150f42d2a0665460030240c6281d0881d210071401c96000d00280b80140110603d4406040050405051525080341a44600808001064606542d503008407242103610b460480c45506150707038040c21b040c07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 703096303 1250 703095053 703095067
    0x20a080708090a090f1d0a03020304030f0323040602060c28030209180a0c051303111f02011a120a0311013201060c11040902030c060d020726 62
    0x5050303000000038541001d5483c2e40441c1c50245400b03283c643d01d006680006486811300796002c902c840c800c100d01941d800256261000c29070200c2118242da0f00401034520b4103400f031a00722060200142d41400031090703182e004128050400c020001c072038071507084a400e5151901c076058113108109100550600c2462508280d81c01100b070240d9102080c01c0060070880201702060000304084007406a100d140b104100000109100b040402146172900609180740c842c00100d00c619240005004214121510000340d03503604405035270300900e02d034000721a924080020380645448813440b40021001c00e40030303045040150a110f10316425000500384040d040d10252080001ca114003c421f540781c200e4003100403031000980542c102c070800c5003a80c43c0500310101406e41c106801440030400d08880000100d020742c9568060000102d8000035a201d052000038544840d0b02c84e80340d003004c03022a000128400640c043c0606a00401c10200030300d40000645183d04040742032030240013000e001304 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 703097553 1250 703096303 703096313
    0x1020f04031101021510180516112401031109060f0d1112031c0e0c2101060611010b010203040b0f0915040801020304020f0609221410090b01020a0807 66
    0x20000342401801500e14010a4417845403040030121040d0548060f040c008103c12035900925000601c10440c003008182450318014110f031184a00c850104030040d43c9040340924280038003141c0d034001c0e8280d40008114000507040880c001d11003902c602071203100c002140e007003038040503100d150020840f034404151340307040190032805580300751110810309403403800c951903056004403810980402540c89503040240e014802200904174003144c0d00340a40c49001c44c4000511110011040314019072003800d00f260720240c1c00442d040e548044d82002d0340014460b0700902d500d0400200e0341c000340040041d410041e03a8a200f02c1c418004a170300200040294424020050b000c0d0a9004050f07440000140f6490303000382d0401c2e00300c0c06d1203960000a210452804034084480071074162942814040302600060401c4000045072468076601780a0120044e000c0c0d1051849200d00c512000300d909012894051000d5980220b000c01c82ca440454202507000180340a4481e80c000030880c901032a81d0f0f81e07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 703098803 1250 703097553 703097573
    0x50f0307031b08031c1b0c02060306040b190305010c0f021b150d140f1504050601020f10060e0703060308042c0108060a0b0f0307030807080d090503031801020f0403 72
    0x161041d9050b1060003050302c06051006000620400700f984083e0010740070400102c0d0f0f40200d110710400c18a02108460b107800443c0b0382120ba40490b0501c2c2c40380e80e90700104024200120340103910091a0003401d440103103070071030358080d20700400c000c101c10207003032a09642c1c04013408200c00c007581c403e1010981e00c001c0400c1a241100019001c198042c01c01c3d04103016542103e42c8403c0782c207484400007000b5001c0b0110481d449800418114201d090400c18a0b210024541c2030340c2c0036a4950000030a603900801801000e03010420403104640001c00b01280141114012102c2d11641e6102003400b1358030174012282274a40060200e881d2910309540400c4840d8481d01400040c144911140c2070300181d0600c1e2070003401600003800180c03a0600d5007104851140300700b20b1050089025441594030f00054200980e03074825001580e41099050042850280c4101040d2060500070b005040090210255018990b00c0200d0f68040c0d844032031040c01c1c0d001d04000051140010302003080400c032414070f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 703100053 1250 703098803 703098833
    0x712050405190503030403140711010806030a0212150f060a23040501090c020d031103070c06020c0f01020405120118351306020105010b300103110406050f030703 71
    0x822900d160b88810318001e084409100240c98940002c4104020315130400c156100b0443d6289600d0f2030090b0b203555802e4a16201c03400b0704d04001c81a030000d80b0a48040200816040e00205112081f03c280f0260981c1c0d00302c00700a01c0c0103901f05401080102d544150700602542d0010001c07100242041c4810300c0661070501d10301c1d46c480c20140b40400d0f075240c510415002c0c3c22100d80108034810544006803420084002420804d8504004034903040912015242c0080d520b10f4041d0389140e403400c0002c043d01802c500c1c466903004070030004540c0a0150f008004840e4140c0310b5401e10107643d610b0500304c514010550100b0214580d0000018030000240300e035296124000c01c00e0a20b4071805203500b1544401c2c83e940281c00001c3c8102a20b80301021030300204514802032144e5810b00702c0c02c0d00e0500543c0514075050241e5503060341e003840c02806000606114035102c410569481c10318168102e0845101c0d402a450180046900c2c148405440f2005a0207001010f8003440c43ea030f48242119030107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 703101303 1250 703100053 703100063
    0x90b09060913050a060c0206010e010b0a2106090e030903070e090a031b15050f011e1401090806070504091b0503070c0606080d050c0d0f02060114040f0c03050415020307120504 77
    0x16082500085041c0701b9070320140c0c140e90041002d50704003075003215290010b800119500e4004d02c111034001c0e50200200d01c52a1000c1d080f0341c00030b4640d201001c041d01050b044400c00305e0078801010201e80e8008040d003403a15040b0b0072140c00b180d0342d030613400401c4400e6400b107a680e0000d06640b03020a0140f4085107050501e0130030031107070203859210183d003040403480082117607840700b050106001040c00200d001d4a906030400d00e0480c001103419408000d82d06c20002d0307507448240c0100e0720381e016049060081140d0800d0b580a4604040001c080d0380c05402040c070340a1601e496032058080e4203090944078022900d84500e1074442c0d45081d60607041000c0304483c03081d212103002ca061582400780b0901304003d41c5803691a51800e85103581013014038410f0b031040002c1440b050200795800a03800e41104c0d0405a41010280141c0c041806480300100075070849090480d0840c0b100e42c10f03403141c0d1145000c1c0c5004041001c010110070140c2c8000d0b6100000100f030310b0f4488681d0842c03a40542e03009480f807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 703102553 1250 703101303 703101313
    0x307080708070c030b07080a0e190c050306010612050a0b01050702060d0608070603140603150403120905070b0706180c14060d09081308070b030f09190c090b0906091305 74
    0x40d0344907200e0f491250070440c1c82008210901c603019410007911600414034080901019a2140007071380d5030801a403d40080b0301101d801c1000740040e04040402802011302a54420343c0c45000c05440c00c41990740075a0401c0c500310018220a520348135850b41420140d44a07490f00c0040d030200043c03a0802c06071460041e0760b0b4100054030100800c072070001444151000701d20244c00c3d46080500d118010f103014000e40040d40081c0c02d074403001004070b92050b0f05040c134502e542c1001d40c9540080010801c0140b1920442101003446071916000e0250b0324031583c1c0c18040161507694030b04481011140062808070084e01c10b1260018403169601000400f43c2001e0400c1c0d100f0071920b0a03201c19182c00d41d800080042e40d030518510302c502c3c0304060030300900184000c5107464031840c110b100080c10f41110304002d102080e4201828001000082c200d105001421032071070824601815041c49034000c0e080c9040340741d005c0e908214803803921500005203110495601e100325140241c1c41c59000f11964020 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 703103803 1250 703102553 703102567
    0xb0a120201022e09050f0c0d080409230f0402150a0f051c021804061a07030f030209091905072d02070e040803150d020f01030f111b0601170307080708 66
    0xa8425842181e004000809130200090002e9003080f6403c0070144c01101040da500f00411204030842b000c60301031807030000d000484081c070350010201506001c91076094040074007155000d40c011850245000f19804242207011031040106442544d10001c08140907403440265180107001a041c4201d10701d200520510700d0894070001c9034031400814114804522500c5440d040034807039030001d002d10b41840040d4145070350351040e03180a8250020b042100210720490668800e80503646104d502a00d124280d0400c200780c2c050040c0a02005840c0501d0300f0006103078944651010b280017031000018400650084100c071030b82c1d80f46000660194410194009294402c0d01000c0d0b01c558002c0002648030304000176100d458150340c1d440c045c843c1d6200303e060b80250742c03801100000c502d0242400103c0360030810758840580203900c04009a56400b042c105442101103a1f41c0b00307000b42c1a002d03504c10ba0f0b00c07502102201c420280c1c86203d2948103005000009400c00010001140038003089410804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 703105053 1250 703103803 703103893
    0x3020a0b1510080906090703020904080d0906051302030f0d090e06060408070b0a0e0f0108010b090f06030a0e1c0207060507150c090e130209060f010c0609060b0a12020102 75
    0x540300700b810001401002c104101d001041c00000e80065064010300b040c5440d680006119100180001d0000e00c00004c60240c00006507001e004603d0b0b20034028841480c0400341c0781d00b280a10a070036030003408bc201d800e01c1000f02c08902108490741d00d448880c180c3e401e02c05c3ca450008001041107401600400010074054003c100340c10003404844a4203650f03880041c00101440c0100400900444c07a2418200d0541e802034001415151501c1c4c8036511501c0c02d031300190480c1a415482600803000005011518000781c0042068507008011103019032040000c0300110805110300e80c0060308540ca05101140c400d034001c00c0441d01079034007403400654001c0301c40116504000080c000c03070001502003000d411000d0340151b0010760070f208012300302c1d41070700460140000207101d940704031704240801110b83c0c05218040f1302260002e004001000481c038007400200303214505140700e4a9400c000090440c14045000040303513041e409480c1c0b1f503041004082c403250600611100c511013600110704030394 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 703106303 1250 703105053 703105069
    0x3070f0e120106150807170c070c060e040e03090307060f0504090c0503071106060a090209011b06020403050f0601061704110d030909060515040e040f0f050d030f02030403020a0b15 79
    0x10081c000a00305290100701e24051150010203818040e8a100b041003940e00071a800031840d14414005910742e44c0c000248200d8411010010030f980079080b40172a245a002941100d0603006440400c00700860140c265601d0181c90b0b00750354981c1c0303d060244a42445651480c030740301c0281c10083d003090b494039540d4bc182c0701210281400288084104081c159201c2802c00c03811404401400c4141800b0b0049158000740e4051070b03460f1034000800c034002d81d205005002c1c04c03902d030843c02d40e448802860310078080d40c000d1009030b6141c1b062842d44c15440402058182c100d408075180e5040c03030004c3c450080d5450500070800e03158001200c5c0905000d4589890a0951500c00c2c2e80f0010f2050410300c180f400c030f400340d40015004400d81004400117514841c103c9080d1000d1940d80e038000e0b9102d00c0c0c40c1001131519170005284800c1c20900108015000400400711503050b1014005da01000c1e001004034042201c002d030059108580440200d40c10010690304140c0d0340d070301140c00c050040c0201e1010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 703107553 1250 703106303 703106329
    0x110a080102031f0305150628150201060807121e05060a1a0105070311030f16060b18190b031c0e0d23010603120903120801080303070f0e 60
    0x140e5000420803261001203580d00094003245840c2580e89401c2d9200d0554400030350201c541160020000b0416a42c0e8040101254100c0c00f10760002d910a041107206c5d94941600c908554601821041d060a50041c014a07096640c1c000081406500d0041c00305130b41c02c00842e0030740b03070300c42e450780c041c0200381d100c814454610b0f0040005010034101000628210303001a081b13424112030810307011043e81e9002045940303054251401111107103699554a046104001c404941580300080c000c000ba61100811070382180104000c01c034080412081c03040e001800d11000e00c0c0700320361000003000c580c4003107440c08002210710000902e1007039140110346001802d05511910400300790944035010307441440d03111039400540d0300782c606941640d02c55503261400034245800b2600d02140d0140c9941c25032002c00115000403100301c4000e00c0c3e4901601310078035400240e42d00c2403201d000500d018001d000c141c0c12070340007200441c515504d6141c202c4444003000d05840410000981c08070301c42d59110802903103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 703108803 1250 703107553 703107569
    0xc260304021903030801060311040e070908061006120911090f01090605042a140d0203040b0708100501030c0302040e010b03061f050904050411040f05060109140f0d110a 74
    0xa64200360040103114059034080e9840c00c00c10701020b10000c3c2c1c0c4403440d241122000d0402041480030240d140441c4e02558003d254040304000401c9407440d44034429500300d50441d800d48000da1038910040b240d1860728068138011075041d0090300c540000d10740c002e00300c05001e100c11100d403500c2140042c00c0343d44251119103265010100510510b050b5118007401860100d40401c203a000310000351828460442500c404500014440104140200741c0e0300d8545800100ca55600e003081d03460400250015502502c034961004002100f81d802002410300481c60038404078907642c6420011405441308000c038a00700345d000d100014030060130845150107003001459040d1a45810000d124071240c0c004004400003800e0041040c241d90040c00b100d240780c000f540c01003615507603402c12100c1c102d1000120b40e00301d131810520081d20003a60f40024082c1c1e80c26603980314420f9688001403959581d0032403559000001c442501424900400400c140034810307114100b1640c160303000207990340031903401011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 703110053 1250 703108803 703108807
    0x9070e190e0f190e0a0605040819110d1b151d01061a0a2c09040f03020c09060a1701060b0412060506180c0a020f0f1f050114010c26 58
    0x180b034080d10148030058583c01003c00592028030344050303845400e4980030b0582540d07030340490184081c4904a4059207041c4214a0850000740340092445803441410700c098000c48003034000c2c42e842402c0c082c040550683c10681201d0503034440034191001c1c1010b0225560390b40507826104c806410f448120b12001d000001110307450b02c5000741e50401068000c0c0d0001200300700c0360780b046812159800c40e1681000c1c900a002c002004035038041c00b01007400a03801462041040100000d6810907800d151107682501d4108280c6014441d925030140d40c041d50200e5240030910000500352068000c1300003680012a002c2d070740303c403022543d92240c0c10004c0d0605990f0408800c0c07290394010290002d40944070000c0c80b050141e440003100b42c4c05492140e00003400200c0c1c8848500c20020108134003480300a481d615000d40d44095990507259000050074010080300380070010b0f05105043c109c40c50b4807410003444000d680110340d115800282100d50092603d003011120144110f070072080000301072019 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 703111303 1250 703110053 703110061
    0x30201270b0a11030a0c230109110f09010e0a2703080103050f120f0a030902040e0607030e010b090f041b03060b010905030118201201090b0609070e190e0f 68
    0x501c0c074220b49045000301c0c0e004115150707107250b1007000100d4017038000300400f5108001c0c0c9070448000089161507075840d82008400c0d4284400c099100030302540848140e52f60b070400700188000700e502441600349203d1400002806001c0a402c40341b21a9001c1601e04550400c503180b070522080d10010a90009028100500400004203c10510202080000d2221003c26001c0460781e201d40e040c100c4000102080145081d402600280e0000354024404d000e00141103108503078601085440b14002401c2c9044161a0301040c8903207100050081c0c1040b200b60303640e2a04481d9648041d208850302c8102980d941071943c4174100c60005107218000108020072080d00041c40860385400143c4281d14200c0506c01c199060100c2c2415181d03c552140c060881079401c0228003800c0c4030940341c1000842c1d0480c2403c0c0350640c4011000c0e8455a0f8184a5444800500083c0e1000b1203146003c90000242d2208500d0008e5134001d03035100040000c015030f13880c0c55241d1000ca00c25074015440e420584140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 703112553 1250 703111303 703111307
    0x3030c0f0f2506050f040b0c1005130819051204030302070209070e090a050c040906030b0f01060915080916030b040506070f0e0103020c0c060304030801030c0b0a09030201270b0a 78
    0x10400e2420031502c500c1c4030381503100d0260700503141885200288040050840300d240482803c0c0c40040481702a81926954a40c00c00c030307181d43c0f000ea6040d21003890b150000c0c0b1040072425100d420f240d000025181480c88462016480345035840524051040c00d00a2814449501242e50f00c00c501c241e601503222251172040c000c8468002d0314034030a102524200e043c40340c40300c25099901c051503480124031511503441d1034400d8451030300041c0b44a810007a02000303004c070094150380204150703000d241c841da9039120f04840c00405406403c0d044c00d01c5180c4c41413054071500701340303400100c410b06507040c20107200c0d2660221051940100d90209803541003005006c4248030a45e8030821606040a424000e40002081c041da070414103410304d9804141c90081c210208101900c1c080042d00711071f40d0341040d080203410f0a00900c0112030781103503240c01141c0079204d04103540b440941034075040142da04590064070714101006c21980404002a4141149200103503c8001000070208072540c41821101c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 703113803 1250 703112553 703112563
    0x1703190917070e040303150e09010204170105060a0303050706141311090c0d230126011404110f040f0b030c010c051b060d02040e071e09060e03030c0f0f 67
    0x9000079000b5040400448044442807580154986000240411999041040684c880d0015406002c40034204007400078154000e1007641c425114682c504020248a94241e030411a00190001201030003040003074001c0c4d0181003880d204043c0030540f030604a0b043c1c44030307807400c41d42402e040e080c40c1024000c0c0500400b404100312030684082002d480c00c0c20440c03405200300c0318588081566281d400c4442181d0700c01c21284d0304042200d034103055945078240411220314400343c0d0003030840ca003507044034400140710314007104007101708003a0a40ea590f11039924010b8440b5480c0d80221407a005801159202d100c0ca05600346070703910004100d4000400d01d840e220400c3c2c0128140420032022402040d030003d1713144540f80131070754403082802d0071101007555401801c02d60551b0f0b40c00410041010500b00075801e00c6500c1594500d50070100101100c0346603081c140c8a1004545450424405c0d40c1c81841901c4e03003494003a085134540186110450315152a0034800702c0c040d00854000b020080c81400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 703115053 1250 703113803 703113839
    0x120c011e1404080a02070803030c030901050903191d03341206110702131b03020a0e090403022a0405090c100e0109053706050417031909 60
    0x31040052603440710000100200150001c2c09250021030f040b180381344208900c1c0007a091b12010740c1e80301c0c01c0c641400041c40d041641c1c00c0074a54206400a184600b00000366a9820303180140c200800c54064400d640364815001a1055160784480000035503d042008030043c1d2400300c1c00840019501e0740c0d443c2d840459440b0308480102501d400c10028945400e0050201c1d04060b00207100030060360003c005225111009400013030b2002815102ca200b58000110b400f085200400c0307510507000118100c2c42500d4421020401080c0030040303d080211071a64850321900407a18200c0f4414101c0b110241d080c9401050521803079085103083c00d15025081d0480c0801004000030301742780300003c500c00c480d076501d101045500001040160302c80ea01841c0104000b0313024140001c90211520703101d1161704071300224134822080c80f809240c0c4061240045440c203680d150f00701070500d401d036455208066406a0680700c2409002a0307900e200003141c40ba8051a111070f809030749080c10b59458800d0300c0c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 703116303 1250 703115053 703115111
    0x80d03050c090307230d0b0106020105010803120a0b01020c061902100e0607080c120a0507030b010f091202030304170a14070806010506160c091d06040221120c01 71
    0xb10044805403030004821040d10380140f40b014560841603840c040030542d8550b00c99204210b01c00d0202409014441c51307040e02c2c0780364001d00280c2e803548140c607501c0c41408074022802000304006264501c103a07120700782102051040d5854000040300150172500140c5460101280384003040c0d040b20340400a5031600d685516042c007042e01011802511480001d00d400c00b0b101c4404001860030036007000f1100d00c001250000c00c01402c018510380002c0104991030804a03103010030741c4c042580034401c16100110707075585d40f1140034204a407028800030f4414013242c00d48810b1001240c41c1c0c40d108003214490380400000c0068681c03d0a16091540000d0901e5285400c004d80c28013400c400490301505640040d03541942c1da4803040c684148030001300201422884181c203010036407009a40104481000d94007401d1000c48072600d120351a20302c02e0b140254840741059180c0e00c100d0a6003144500c1104500a07240c10000140110034036034046070801403a65900d840b03544401c4001d0001c898500300384 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 703117553 1250 703116303 703116307
    0xc1203040f060912110a18090303060e090d0e151204120503010b041203111b040608070e1609051e0103050708070503070c11210708191416080d03050c 66
    0x200c071414118400381c01c0090080c40d410b0121750030030388540b012000200f408844100620702000a28030040060020440c002804d01800140300814043d5040c001d00c01310025159108007400103440c1d1112442555030014080c004041030301c40540007400c0282c058103980949440d180c500007080200c0c0561580c01d02905100501c04024000151815140954500100d45034a414280c1c1e500c1c400e0b801c000b81b10b114001401109042d46403038110091001d0ba002e01615440d15002919a1064000d0b009400d40b98400100c4c6802c00e160200049046400c3c900022a16880800e0300c02551002d81c1c0030041100d10710000c0765925200301ea601a20602c3c0040b914141301c40010181c9c40003401003000c10107000c50750b8040c40a02200701c013803803d0040110301c1150f820303200d40740000320602076604c2c140030340c04d0009070448010540d040303050b403800360b5003e00010950780e140020300c6000a0480714420f000040c540014111070000140480c8801015007400304d80004007a950020b03c1e5a20700241 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 703118803 1250 703117553 703117559
    0x4031b0e09060f07090b03070216062c040f020c0d1205240307090614040605040e0a0b1302030105071e0c0b06041e02070c1502120f0702030c1203040f0609 68
    0x3285090300406820b5145060b502c42c2e0307030105c03032a41c070741c0e017001c09007107400020301881355000140c0c40031100e000d42c0c400712001d40c0c440082e5040c0310526000c4003025031020884101071a2130b4515400c8000040c00014050021105582240c0100c02101d003540d0201c801440a1a0080002c80e0140c031800c1051120303140c40d0948155120704010480000003602c05121034599080c080c00c0042d041c0040b0400c2016501c282d101c80d11321501d2040c6001e81c0c6080808215410300740520b184040044000f8158010240e41341d1b08003000007048a40b181400650382001654203001c0e107401501240e44020290700f41662061404080c9980c1d0420302c501e08500c08005414201300e958851812500040c500345103881c801001408484440f24403480083c5010410108069920948815400000d48000a454166501c986040c40307200d034014244500190264564020401c0d903101030b007a101000c00c500046100c40d03881400e04122500041000d11120740302e545110f004007040d282c042d0780c09203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 703120053 1250 703118803 703118821
    0x109032f0304230414101e0608040311060c1e0703090b0309070305011103070212120112021810090506060a0503040f050109020d120305010501050702010f2304031b0e 73
    0x105038410000d0412405041d280d80101d003c40e007120000c409401132000303011388119441244811140b44505404480340411384401c80c404107140e900502c4003007101941040420f1300e641d08020800c804010315295030781010752081c00b10740d016600b000c2c40070ba195040c11207804c0c0d02c14050110741d00d410a0034050138000c00e89c48004201140d038036022a580c0d0352216200a130405040c1e4102929030341c01c110344041c4181140c07004602c100541c2d426a00e000108003c483c016204041c1c2100b506010400140b050705030b40881d08000d1407000704001c4054003d94a0500081c00895034010040840102040001030500840f54043c00448241e4508030050402500c0c500000e0702c05006294210344080401c03000350721910f1400c0d0020000002d010340b80c903124555501046100c00064209000000d8650007103003600c0c0b503980d05845186400951030300031600c1945d00c0d0008040f0b042c0c86034030b03613210b0b1440340e000f08041d501900510101d000a00c00407140c0641f25841245040061000c100040c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 703121303 1250 703120053 703120057
    0x30c0314060d08130e1e101401031e0e0d020705220207080712030e060c03010306050411090a020a110601060c1b1d0609060906010f050d06080109032f03 67
    0x34101d61108100b1100c0c03d00e5103050060b2510300140d40707030354000400c40c0d03080f13007070607621513581c030404419100c500c1c041c40081d550040e903003082c84001c0580c0c10b001d6140f50182c036201010381854002500602d86410b082e41a00703182140241b1030707540c4407122289000303206143da28003180c002009024680008900e1000074a000c1c00b42450303045e280540c101225404544030541c01540440c1c071403082e42088115a01080c4a940c04030785000f03110300e400c1c10301041151144502d071008605513032a40c0c031010301812005101301c0b100d00791400c44060075565000524054410040016250036000b1409061410a00700b54440365122600400400d5480703001500c80346d60000103415810f941020700c90710320b00c1d01d400c5590002d124400d41641c90b6000307059580300321021610072001d41ca50000b03000d001e0301c05849c1c0364001040c002d610900a8064001811039140780c1c0c000044507560399119600716441e00314100c002440b980e00e10100e40060a120800510300b10b0304441c1c03001001182250b0324 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 703122553 1250 703121303 703121311
    0xc02030d020c0a0b010305010518010908030f06130c05091e030a11010203040305060f1e07021c0e0d0f05070807060e0411091206011802133c06030c0314 67
    0x1039400103100350000b030741444100c411a0340319054094a507100e01d06503000e000200c81c0341400304003201084d0540c1005000d00010283c00c0100340349141c86030050002c244400411803508008140d00c5a50b140c0300c513100765901c146241d6206038648204a01700b001019a401c00c941850203000a02012036a000c20035500055000c01481e40ca001c080d40140d05501a43d8005003981c0a05001c101190760000c0c6d510340305150340e090303903501005075808105520009450320b10040e4070000100071803908d880c4042ca0300e81005d00300710044101c10800103035a1112002d0848242c02c110320f10004011040180c0005802105c0107000c84a080a600401c0190280707102440303140c4842c2100d0140407000300701e80c01a04080d0600c195540031410715640c40400784501c0300058482510060000e00034801d88460881003003d00c512180741250800d50710f0380220003265031020620802c4070110701c0100b0015120929003004030600d00d0880042c0454602c1d440701c10505080c01c0248040da10380030400c1c0e0788 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 703123803 1250 703122553 703122577
    0x51c02031b0a0f0e1b031909170708300712201206090c120402040e030a0c1b030f1e2003010b0406080607050c0c041a0f040c0203 57
    0x7191540314000307094148103903c801d401410381c0e100800c40ca9000c640040c0301d150041100344400107400d80c0350340d482c442110140700c0f16480d64141000d100703154000340f0301103010341041ca1f810071100c6820844c6a02c41581141c1c455400600c0c45882041c2c00030240c01513090704e46240e03840b0081d544500e81c82c01d0007401d040030460b060071107040c0003207141c0c0106180700d6619542c0003a18000341501c60994802c03000c64600d941341d81d0006042e8500707602118400c1e0340204030141000d0035110700480c07842d00603100300c0c4d0054503501c011070038620401c00340403102c2c0b1030350391340b400d1004a0804007000010b0105584112090200600201d442c1d685807143c1170b64010151940d10320000300a21103081008002404281d4a00815030500415039200c0c46a0800320700030820f10250204200c03c03600300b032140b03c0050b042600010031044c00b44000c0c040e0506020159011403024000040494042d01051200921030828a03a4039003031802892440105c25102004102c0b640d4402035030307a010f02900380b40 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 703125053 1250 703123803 703123843
    0xc0e0a090b011e120c0f030f0c021b010203040305030724050403021209010c0b0c04090b0d02130e0709090c09050c0304050a020405100503010203010b1905160303020904090219051c0203 81
    0x8005840341401310b42020b03090104000d01440c202c40240300d100c0c11009900041d080c003038102200c08451203441074418882d0010400e21514107650341c80000c501c0181030660105000c0000822418402060035030300c1450b1001000d409452400c050315494100030f05024a42030400001a0300081c0044040303114000d10ba441e41c4c0d0f020700481d48440000381c0208000040c2050011100010380a80f0903140d46010512900011400380b2a6241c03600c90040e600c4034521905001c1c554180d070041c51102844000e4800040e251014039050ba0050740003101c880c480600200003501143c89030ba508002d072040f4480c81d6051548405a460700400800b0f84a10380d0350700420391801e0811301c08001860080c009646030741e07540d0440c0200c0e811807002101000c0810b05451201c1c0c0c4034000315000e00a0b000e0441e003010034261401c40007034015804480e0443d60350b80e1100003680da40c199400040a401c452a00302906107024429a8110400d24510301245490344800694010805d0b01100c044004804 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 703126303 1250 703125053 703125107
    0xe0c0702060f070302010504020906041104050405090325020f0d021f030617101a030a060506030c0406170d2a17030403110d08040b01050409060f0c0e0a090b01 70
    0x391a9200b0000c58403516a00000d01500300354040d04260301c41d60080303a82d00c0d05a0f0f960810300082c0d171203240c1006c0010200b00000d00c100d02e030503445281c20442e4030007228141400420805803c142e0ba80c0407000136200c03191018210705d0b2401e0402402e5009032101e00d00703041103501240c101d40000c5102c4400001c1d0b49030b08240144243e001000415450841c5018500310800301900d40711080d0034849102e0402811914522280d0f01c40008404050024151062551104001008040e1180b40d040c042d02868030719584c0e0320b004000c0038109241c50020700100e0740000c24a03048a0740142c1040c40031441c2c1e4000c0d07010b40d00700003244204110000142c100c12528103d00321405c030781403e00880c04040144010705504c86011050020030704122103442e1070070b081c16a41903600310340c014441d032080c81c014091800e00390000001c00727110741e0000c16400c44900181098680c060394407400903100c0480000b4910309074540400800c03080c1c2d0100200c1d8844400203080c2d4101001ca0303010510307040055 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 703127553 1250 703126303 703126309
    0xc1b1e01111b1614180c0703050706090f06021902070501050406030c020c060f090108010803161218030605060114160f0c080d05120a05131e1a070f02070e0c0702 71
    0x1010f2969000e111082a40c840380b8030a42104035801d03440c0030702c4c0081080031002011102283c01004c40c4107401c0e080052698080ba11540481001c64825407584107050000300d850186115a511442c00980c56039440ea050070101c0c8a5507110348115404103034200b01a980000480381900c140340340224030230521076426481d1000040c205a008800000d860412140c0e5102605c98510240d0f1810f5461341d0390310500342e40380035910440a124808410900005085010152800845040032501c0d640304c0003220321000e009a1041d1200c988800c1080055a4804c4440314001100c078452170408003512001ca034104c11000e0000d03c0381d45034a00c0c241c14002c42d0f038505001030040d1070440306a402c2c10800180650001000400040c0380900802c1442c1d41d00c0c0103507482111010603091440c2d0b110b440d81c8500070740e0084640b0b2540200b000d0140032480a81504541c09544080c0148600300700703e001301501125840e84086400c011824041e002c101040709030011401c025060302c403440e40c000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 703128803 1250 703127553 703127563
    0xa0602043f172209060803040e0c13080f060103050f070803030a0b04021c0903090b09060a0f2f0f0304030b070e0a1d06240d050c1b1e01111b 62
    0x803444074005800b0242c0104445000f004107454100c401880581e0369007a0380c540c0c034001c0e40100d0f015071110400241200c12000f01810b070007601101d07114103d030756a00045003050190b480a0300160030035001401032003406c21080858880300c0c0d00402d0714625080419849000250480095036150340302c40200b9650b50701590486020f600c6418a00b1030001680001000321030400c6000c101f40d40b2000454000140a541469030040d200900d00b03908a1801c0b00c44081c00c04106040c041c104005485114a02c02100300e5020501d0903591140034040407076144c00300b04220302541d54402c010600c00100408480b84c3c0194250a20300280759480c2e001035010341042e08400c42c0700c4201c0286400143c0c022560a0084400307440b0078042485d841072001c0502a00c030b0004882a008019000b010103166002d50780c000d000f13140d403609120792284200001807111403220403a600c1202c42c50f843c000c00004200d007190070b46008000b0306103400120002c40c01920741d6108040c171403a2140e003000e031080c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 703130053 1250 703128803 703128817
    0x601121b0e10060f0306050f040e01110c03042907030f0c050307030503070f090509010b0a140310150504030b0f1f0806010810060e0105060c0a0602043f17 68
    0x54019075514000a030340680e0740d03640c4510000200088880304010f4082c0c45076006851000c1e02d03034220202e40790140005040c2c011036061b090341d6664400c0503141448009000000300781009190785e1460303c00032030700455018545503407190702c0c5195180d9a800c1d550445e03070305a030b040c1403010143e440b4407001e440c070001c880c1c4054824000016510704040d4080d00441c0706124517201c54908a0030030784202c9150041e4060550003098040051043c6441035010f81801031451500c281c4244482c219a449508242c88081c00201c03203420901024203400d1206100382c2c200d00d0900c0c1010b01e103403580901143c002d030120382c030407840c8000309558000754090408c000c2c040c0d0500c0041250344810f00380d0341c0e50003449a015540600000d50b0b160018900403e0704a4030000d400c070702140d09103820041c0381c0e4009045081e480c407800010b1400a40540050001407848020500f080424100981e03102c02c44180b102c140b0f007200c801400d0112441d10081d545103034001d802001524054440c443d06407140c04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 703131303 1250 703130053 703130069
    0xe0d060905100903030617030903070306050a1518110f030f0703090819021e0309040b06190305010f17150c090414040203011401061b150f09020907020601121b 70
    0xd030328020300d83c240c1c01910403245e00c1100b21502900c0c20702d1f82602c03030260040031603040c0c000070402c02c0800c4140d003040d50001002000002c540280049030201700d8000c0d40070301003004042c201080242520700c60705030450728001c01c0510384409141c06011510008001c1088400c3c3c000c00300f18128825030242c20603070f50020302d0b1030303483d40d61064298041c107202e2000720052299000c4c1c103864144080c0b21050f51030b0480000c50900d000441040b01401704d0848087c3c12007402d000c0b030302000140403003800b182191034038005190b5042c101c685039007031100d0300300d40c0995074000e211820885c000030b15050381e0109001c2c8041191541109c480c940c0c440c003049640e2190030701c80c58003468443d400d40e0303d024601c201c000708803141c20860380400440302489510041001e82a00c210814011130341d0701e021500c11180310b0801d0083c040b08d0401c41e00303440c9407840c03016030383c00c00b2108500b41181c1281e00400c0500081c02c0541c90000d58a41d0003490110040c5208801c260082e1102465001390340604800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 703132553 1250 703131303 703131311
    0xe040c0b030a02070b0105040e071a09060307081909020f10030902060f04060815010206040224030c0301090c021b0f031c081006090513390905010e0d06090510 70
    0x38582c08800303500018025280e00021100001d032600d468401c581890358810003400800d032408030401c41c2e07404e4250540c00c1002080160070880d58901d0b00a42c03040c0a00e8a0704600d50501000f000080c50052940d000c0f0189804130000159440d070041d5500b510040300d0300d011803440a502203024007a0030740002d4014201082d1550408559005082910100d54504c88203981d50054085940450030303844c0e02580040b0040b6000d401d003452103a201e003069078107000040070048400c0350154401c40b011400e90788080014840f00b109030107a103082c1b42c0a403008126003082c481d002e00300381c905041c51341c6c45954045c02d285115101440800c0d2035891021a132034600c02c0d80c0b24080c2c0218400c0f2400b4140081010000c10700c540602041000e40c0d001810201004008000000050404054076042d030388000b4954042d03a59082140040b404941c0c90541c5c5998560300c0182803082a6088a414081000e4040983d42c881c00c508500795130b045040410408183d043c52804d00700200c01034142c090030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 703133803 1250 703132553 703132561
    0x315010c0515012d0608040f1a070e0603150613030602030901050601260a0510030b070f0f1b080d0603020303070303020c0709020306030a12260f010b03100e040c0b03 73
    0x700010075040b54202401340c00c4054400b0309440102c11000c81e0800c000b0b4030102d052011503c00d0081c9a0320501c6205c420701049440d844880d40c0b0302c01030a403200c284140008100c0c1a42d80180a001148010399810b400c50074549288000d140b02c060b03900c4c0c041c800209000844c20700d041d4280b4000e5821040842d524240002e680340682000c80b400b0f400b04440070b03041d94160104821034802ca20045c1070b1540183c03283c85a15010b09000382c00204045c1003d14080041200d0492540c0101c005842d8240030098000380582410046000042400441440c0a015440d4244c1c0e0b0364400d64045c640721390301c0010300c41400c002c20490f003001e50144008240c40d01090b0305540184221038081045544096540740810160302c0b045804a4042d00100700c03c10004144098201205c601410400d030307a02074003445040b10315410b061030501030072045d0901501414004240b8003500c1c500048030310b0361805a9001509100b40c0c843d0307400c42c4451800180900024a05030f1020380340340080c066882c20 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 703135053 1250 703133803 703133833
    0x2701020414010e060f03150a08010b0405090316030e040608071e0509130605040204141617010b0a080702070f170d02211b06090105011e06050315010c05 67
    0x2040c01001001e03086010100d07030307a40c05030300c1000c82650002c10702440c16240c4000d07104640c00207030051014900600560b5940c3e940c0c1c910b60030144c504600002110100c1c4010442034801c0941000c500c1d4104100c0310751100704050f04030303100c160141098019082c070040031070000d10860b4003142043c050403202044d06030055450a10b83c440d82ca5409c44100e40751410004072490603283c005248044101c80710001e929500010352050008100060810b11103282c0751210b0b02c00c407140d91009030010388000d6019044052980210f60707c4207105070340d60524400d40418407480101c0b00900401d03100080c107280c401c001c000e010300091002100610f03900c00003002078a0f6a08400103850003284c842009103840091101c2d138803501100d4840c41d0001011084095501010441c8181c18035120f001c141c2c40820030400b806000342d81d000151940c903282000000c1014400c0c0256821400c2030100003081d0b120090300c2c0c000301c00d00810b40c404044030b001a504101c02c010000c0c424000c048040d91128 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 703136303 1250 703135053 703135057
    0xf0604060c020601080d08060f0f122401050904020402071511040f1706160306080a11030f060c0d0203070e0904051605030703020307090b220e0106060f0e010305270102 74
    0x8140780d0200c0b001c998072400b40546510004240e80002080a00000c8039403600803c040d5000001802c440c11810840000c02c010f04040042c28080c0e45c8600a508142111104035000401e4007048040c995418900090003050018002034070950300490054140400c03040f080001d0009c04000300241d400748002d248064100c0c0c0b00d01500d4046202c00055520a80f803203c0c1e0454072400042c14041d6110b003d03056090300c452300388400305592500302144411040062034560b9000750740b4240383c5980072040501e021012404aa416080340013802150004002901c888a0700701d680580c0340d5940e810111450f0040740041a8400008400c2c4824408081004e0896050003207009541c10344a5017419900e203028072000750944d0054000b00300030b03441d680c40702c4240000200240034a4030800010f401c202c60024100c0d20117581c0380c0c00041c1c8454240b04000c000c050b5424400f94003406480050494600341d00d04505240d11100010543c1d00c014070198000b140b50880311602c0b08200201c80d000f9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 703137553 1250 703136303 703136321
    0x604030c030213021603110f0d1e0f080103060b03101b0f0e15030907171b040605150318010c0e030613050d1b05150603060f0919050f060406 62
    0x7042e00100f03d06034600c15008650b1400b403900880d0040711a00d45c0d04640c010940d484210150195402e020342c3c600092246601c007110590364030b1360340c1403200502d281d425000b1603008248000b100c90041c591381c00401440c1180c0c0c12000000741c0d54548000301c2e003071200c7e41144054403817070814821002c0340c1c2c0025440112810740c5c0c403000040b0380c0541c02d480510302c503000180d100b07000c8082401401e07448001150321803a8001074030811079480c1c0703540080c1400c5506000c40354000388462492590f07580114036842104803070a20510b4a45008079044c951528050407400200100244500400c1e807424890422884020450202c0b0b60200405d80701100070b00f2071090013104003081c0049103070540b0382082034000340039001040600c10300b613940c0f40d07580d29000120820207200c0c2011807010f000030b00f842c3c95010072103103c070b00d0100100750130031000425070f41e01865007205014058800003040840007103080440f03800c6c1c1c031550038030511b0180c0d1800700c02c2c1244500003c00082068a401188031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 703138803 1250 703137553 703137559
    0x71b090f1a0f0f0a031403040501110c0f010f1e110c090115051b060a050f01170a02040515061305010806030303041104090c0504020a180527060f0604030c0302 70
    0x700c0d035200c0400d1181c064407280a59001624000c00b81c0c00c2d25209078111520358000708190f5036140d03039a9079000d4015400c0030b0704141d07810201d02045196008400082e00103484d40141050548860000b40417810550b541030400c0890451590311500070b0031501c0c0c80d96003500d203515180c00c0c80c1c2c00040800000e0f00d02101e00c0e000b0071006a074642008582c030750583d10005107070048079038410307400c55480d0001f00c40b0180e0030011101d00207911341c09009441c014050203601055519000310943c040000603403000b0f2032140040c519601910002c21542c40e001e60456001c17515880744089880f803043c0a40142c0c0e400700c4009031070201c03482c160304601c0440d002030702c42e000195124010141c80e0700089070054a00444800384003881d1806038041c485c12803107010400003864681c03010904076085a8490341c041110554a100710f080001c0f15140101001c44280c400c0a901c2d0704090402071040c1c1c90540c0702d07800d210106440b907070703680e800f205070b804090f15450703d466807418041c03200d000c50721050740 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 703140053 1250 703138803 703138811
    0x3050307051c0b03071202090a09050705060c161202010f1d0a060507060e03040b0f0d091703070207050a05060a0302130911070b060616020d0609080423040203011a071b090f 76
    0xb211000c1c80241445c0540051208e0619661084a00003419013010308607000e0082076404200c40d0782c0c1d0000b0f000078110883c01400d6031500d210240d00d04c2c0d034494208102801f00c0c410900d00503a400408004408041e10340680b459003030745c2d00908085134403181c085d4040540b00010a01c00d03884005009880d01512040c0003100340b0105c181e0f100d1155025600c0c0c804400c01c201040540798000810019020000000e040592500c9000c5900b80d014001100d00c0c4000042c01111a41080800c01405046518111203032900d03002501c14400e440300319040c0340d000b084004003074030140d400e84010100040e0601c80c04010441500080d0b008a00448403500e503d00450300c1820084260b800301120388414419801c032a400300f040007150420110358482e16030110000151208018000901d191807612040314414402025080300c4404480d024501c140010403082000300f03200e9840d4010600300a0b5100305905110b00c0750309140c4800700941c0c50820002492101903803055040c0d00760801c00704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 703141303 1250 703140053 703140059
    0x1409030d060b0c0606010521010b03040501051608180f100606023003220c05100804021014040b0c030306041a0d0312060f03060506010e12070303050307051c0b0307 72
    0x90b4040c01180160303041640500c0c006140c40d4001c070300500b924000300b030010030212000c030710946104030240c004049089000c0f051104000c42400760039044808000f01000c07070305030ba0030003c1c041200186491b1a100305241103205034202805865901140641a200d204455407124005440d00b80304e003200621903420740d130a8500b98088203580480700c100014000c0f034841c04d011500e81c1c10250007174069403000c0540b041c00442610b00385000a204248c5285564a03101c204000c03040c9401c49181030144050402c0010707962484c2014800c0224240b694ac403049004904039580201c0e00010120038001504d0035102c078002000c0c2d48603020855083c85501c080458a11500445115090704081c85202800019008410251940d060380d030001410710fa032410070700c103452402c1d44207a0300c240c0c1e144140300d40d559200302d0404484178160752041d00f603070a90f00d42550320280d41c1300c080d00700000400401c0c01c01e8469400c441d8030054080c444244492591030303010091512541d00c5100744503020b800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 703142553 1250 703141303 703141319
    0x130b030601081e0a0b130c090203070903050606010f0e150906070606150905130c030b040c0903061406030703080702010203160b15010824040b03060c040f0509010506180102011409030d06 82
    0x6800c4d015401914813071161242010000204008402160032083d001e0001c12400c0b02032020f0b40c4038481d691345880794603107541481d40c100f1402524035410802d48000d042c44040d0049145144c22078180d8814201c00c055248405150043c1105294070003c005250824418280c20200c250340c5a60b03120810448804010380d0038410510032503400c4883e00d401442a027100394040c03201080a030401040d0754450300f0000d000c4514000b610b002046a504060051000d9440f84100c01954801d0059090600d41d00084d50350609100080c82100d000a03413004592081c407d590040c01a50400f00c03800c0d295140c00810f91004442c8030321404008180703914117610a24031140034800c1214000041203904001d0002e00002d0321845030059241e026040650b2030400c4000d119155039842243c495060400c510007840440e8801c1388607100c04070040c01560780e51000c42d5169240078205040c071001090042c0d000d04030021542e805001c0d140e081001c4610080018010311038250b900b0800c4644408613 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 703143803 1250 703142553 703142563
    0xe0a2c090123090f1207200604051905130c0f020606100c0f0c08150a020a090504050601030905100f1404050705010513031e03030b06030f0402130b030601081e 70
    0x74014404040c01411a403a1881c000ca83d0003010002c1070340c18804695021a240c03a5420050240c100c0c80010002c0505c035900310600d00d1050400340c1d021911036000009241c7d8003d80c011144901c205141c20320001800b640c85100400024100c0b5039080d040c8000c0c0d074010603402000d02c02098142064070101480801c2d00c91080d040148012060010b811b42228103d500110892b400518400c0c10b00101d114441810700030240c0c2d40007890400c42a20802111141c0a015844118010700c44a00d41540080b507440076110155000189035550700012406031811113009007050003400803003001d03800650410442c2400c4a54144880b08094110203400103045071b0103021600291070034040742d84071320000d04403400d001351281c65040c0c03661145070091400c2000e014269150b407000108140c1c040c01400c01040307007101c0782c2c3e0075460030b0303440c0c0060000b000307100034450840c0b507011103401d0f000380d8811034103204054120750b0b00b90303150210a03a541502c4054888041c240d0307810400402000a4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 703145053 1250 703143803 703143821
    0x30506010c20030a08040501020d0503090a080307142205060906070803060d020604080a02130e190c09181406071d040b150702040501150507030e0a2c0901 68
    0x59460000400350b20b515107502c4002e82210700342685002d2110b141d68042040c0e80103a405032110566403803510001a2400c202911401c3c2844800e004201d8180408280f6030030458110344450350340c1c2c3d500042180d000f81d500740441c404c1322000c81c501e2030001d00d81038120030900d403080c0f40c110899143c03802c002290040ea950b40350700000801c140070004080b03a025581000c009015032148500c1c960009805800c0794010b401c00740c1c00100c0e80b40551038100c6000c06110310700c070000c0100240b0518482d44604480005400d44043c0810007403c026545503000004c080d84001081900040245494100c5002c00c003665038040300c5450000650011070201c3c0200d0080d115107400607001c15031680120b26554410b17074440e07035480030074402d601d038840c0c88840c105241080303a5842e007003032040104551040c4c1190001d401c081690114254019003214244d54260808001803001c090024031720260f242c22640c10b001303248611180d540a40014212103889040b880c020b181d84151880742214411300e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 703146303 1250 703145053 703145057
    0x3030503071419260f0a060605031512120a1d060414090705040b130617091e12040f0f06030212010b030a0902030a03080709060c0c0303180e040804090c03050601 71
    0xf0b0602c81030180224000e541040c00515402c288890003910060003100c01c0341c002201c10408410000030b0006d6200e818045c10050801c1421402c0002010007802c0320041014010700c1000b60b03003d0341110400102c0010f6035030501d22959801c0901c4010140c0038450804020400b500a00383ca1924015003a24265958900c0021946180004000110350060003401c18000104000705001071441c1c000d104521583d4502d410740b600d0000300520301052030b440c0c00c030421500c0742440385034080401c0020340c12045075881a6001401d1081c5420606134140d28608400005070005440103c0c1c0b454504440450000400d0340380e43e2001501640b08030080300000071182401070118140f41809903401541013200014125219800300e840d205001d5020b82c0415014010805603a9000740200007601031803401082000346590789108500d5a400700a0a00291502c03c0e100f00f4018141c0c40700610101c10000b8080c1030900f09603046074064048c012025042030300c003010130341c02801024092003040e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 703147553 1250 703146303 703146337
    0x702181f0b12072703030503060f180105061c0509071419181b180909021f180315110c03071704090c0e0a09060302010210020a021501030305030714 65
    0x2d01011900c0b05108040051440215010100c1c0100c4c0c2501a0010350f1094a440c0ea0343d007454001c001441c5602d40e241441580000c480a00110000403001d04503042650442c1c0c51344e0904a01c241c071518048040800309107484200610154001005401c481481101c43e00d440c03160010b00c5081040c1129201a00e20035240c200058070184032050342c3c001d910240050803100040382d040000380c41110800001e42a8104140d000f80070031040030040503500c104106c20b540942c04a50440321f00069034415100c03e410050000340074454141050b082c031012800e050b43c880c030b01500f80031101403075602114540006045911916422900040d41d6080191704042da15940d4070342c803400139124400da280d424400000d51031034500404103143e032161240101c107018003043c050070041913070101e0740480c20103002f000581d0300172a0342008a002a10003507a030b01e4074001c0517460302e0703000b4110314074541e942d074000414181d008001d9030140c48541e6030b0001c10344900f5000c4841c2d0140b180c12500703040d40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 703148803 1250 703147553 703147561
    0xe09040b04050703061109090108011512081306020303090f0a020a050d0203010f050a1d12090105180d060219081b1c090f0209160909020702181f0b12 66
    0xd420402035209101e50100c8aa0315142d903200d80c00e848040d01c1d03010001c1d00116500781685801d40c0c1407805005040e008000400f402c8902240e460391900c00c03800c02451b0484200300b800003103001c44001006111580100d41e0b505c180c0295641d00071038a04a07680078071a612401c038103011840603c296001420003031000d0405c0100310303210107409000c03a4950741e2400040c403480724600545104640304140004c1d5004241040b03400c540c5818945a00d5400040c0d001405010050540c1c40e840001c1c0b0b449500c90000003122201144090125940214020545002c0110070f40080c0041c591141d030148a00c0800d5505440f01503050340c02c55040c01000b960300c0c107038818010140c200e40c1c0720015055903c02c0c000768081e085940c4e611068611107540b00b03200040d81801d015098000c5180d20758a0205003142400404c1400d10303018841d011500041c0c1c0c001550303560b41842d020701d000800243d110382040c040b206d0a0040f0800144002c402a00002030901c22403403c0c1e07208103824420a50190f61 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 703150053 1250 703148803 703148813
    0x1c020c070b0f09040c020c010e04020301031e020102030c0a0f03030e03070b0601030f0f0527060f01050d15021b19020319051c05070b1501021b060405060c070509070e0904 75
    0x208807021030980103200b41d883c550f68a00642c00c080f4000d40152841c02c03e01000180001c40032108103005900400041000507600e41d009941200030700b80e1901e1035406880100e04521503441041180d209485182d824000d400031a030011034440d890401c4005614400d840d140d00800c0741c09003000000358000340c0154040c0c4c002d001e000e03040400004885078070115405c121042a540c990144080815a18505d40340045911701400c004000b005c8038588081c0c00c51458605008690160301c07002e41020811076004070b002c1c00000842000d43d15002c40c10a0070011143c6107508d03401d04d11488421802d1a41d50042c80d800490f0080c0190800500d240403c042c41400c00e82e04950754490044005100850243d4100d000501540c4155881440c1e003007031181c0352400b81c05a1644000710004c40c1d0075a0f0005000c14040d92180101c3ca9104040400603010303000d00d038001174100d800003070110302c1c1300c0010800c0c03800e0354021601130740c2e07030384030305604442000003883c4158212550300082008a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 703151303 1250 703150053 703150057
    0x30c0b0a0216030302070b090f0d2102030112110a050307050d1b03080304060b01090f03230708010605040510140909071206020c0d02060906010b0f090303040b1c020c070b 75
    0x104044005403070a07040c0c822020585a000c00142c3c000303540841c0c0d0100f00850110700da81c0040c264001000c45040750140d50b034603982c085c03030680140b01208254080814504031041061a04400119100d69441c400403d42c00394005080300ea401014428040a10749a450b0780190740010340140040d1b41004103010f0300158499041e144555254101044a481e800980001e98030031080309490303061030301d410810380341c9000d03d550602c911140240507891080114404490304990803800c00c04552421404c00b10705d16151540341c1c0a11440031860a005400581c102c1c4c9041e54108450703034a1990402040b8624000d056180140500e51461407600315003139900102550f0603075005650301c007280c2d818051090000c50313030303d5001705000040c560300307020320310306e10b00d05001a28035403506141b00d03611040e050050101800c03011405800b00036880040c0c5208083c06411640d5458440064201d640c100c1417408103941200c403080f000459941c0203407440e030000440100380301420061004455 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 703152553 1250 703151303 703151311
    0x1a0a0e0a0f0b18101a130606090b071e14060c09032a040207021203130509071707050c011805030d0b0604030c05010c030c1e0b09010c1b050a0506070f0e0d030c0b 71
    0x40400e8143c00c54190703641026031441b2032240000050350611b13041c1e0181810040d54001e11440c03a0074800c0da4089800c900d00c100c0a0744001d02c481403038409070329080710300b400e9145111446100e84010443c18100f2800140b1603084c0c11001c0310301c07c0380e15803024000060104180710900c649401440001d060a402500c88a880240384202c2804c40444451460b001000040b030000700b200300070049030030101c0c003c6030890020b140c400842c00c0258058490303184060408005c0010001c4c481101803001e42c0081d517050151010009400c0c010b003400c2e0b0b580c0e0403400c181c0510074a040d9113035034549441d00c200d41c1125444092401074a103004010f5403e01c010480560500007044041c1000801603000c4880c5180114184052401241801055510010f041300b803282c0c0340c030240411868103e0002400c064a84014034080f0b20103143c40f0f0300384000520018000c1c070520051229894100e0b0080903030300724541d02c45401606c10010082414000c8074085c0c041400c0400484c0412a420f900d07540c8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 703153803 1250 703152553 703152581
    0x91b0607210810170c01180510080412030c0f0f02010605040f0915020306010e040b0d060c2006040b01031e140c01090e041a0a0e0a0f0b1810 62
    0x70040c1c11100e00d10048611110780e000415800400c0a50b2881002c024090800004010004254144510390704c0e00000b840f503040c00010b03288400180c0798450003502801c00500a552140c40450b4060480c100039075040340d024180c41c1d06030301c17400d1081c4a0101901e4042ea02e0000301e05005105a0380a001c0701d0041046548403d8040303408d84a90156820040312004002500c1c0ba403800e20020700301c614481700902034010800d1103001da07845150100b0294080340c001411701041d000144c0d0103600e0540003403100c7e0030558200c0c034040d0010513606514000100002c000445110001d844010841c0c1c020300480c0c4240040c004520f04921300c0e96140700f850b510354400d02c0181c4400010315620184015513070b00003c085c1c6229640325103444007d00780030300100c186040c0307940c440c1d110301150b081490726030000740f002030210041a08003881041442c3e060f80e05698450810000d4410040001d59007507483e03201103000c00d0040345c07031a5003a07030f0203801510b03034818800c19500c0585901014921 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 703155053 1250 703153803 703153823
    0x1060f02100603080a030c02010b0306060411090907090317070f030305060414090303070219080703080903040b0c06060414091b06120c0c06160512100305010212040b091b0607 77
    0xd6201103840756002640c000c5441320344038a0f8109000b81611108944001164101101c0305425200003900a411200441d8003188020521110180c94040d080302198071150b14070902600a4006c000306056038082c003000380d908a400741c2600d800d072090240c0180b05698074001c00002c04d200e41c0c03080d07400c004020004074a07040344003042c13100c000d01501c000038290000018482240e40400c05d10702071f41030780302c0030120415150700c503075000d030244010240a000101c4001903c02400f84116030141400100c039603140e000c0000283d41d2003000300c4549000324600980c001c100c42102c01054491210200100002615016400c0e511214003240c541c0210b818020500701903100c0001c6407044070003071130680d2641660f500e403034a0084054030840c10551026400c80e041a4484c00712103005542c148440703d2901c481c1e03c03040d611040b40c0e202030a15403021030102801c801407403019000d47e009a03c0010203481c0d4000d1107485100c11a0560030300501682c219050341840c0300036100440c06000c00c40 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 703156303 1250 703155053 703155073
    0x8161e0803180915010210090602090a060e0a0e040209061504051309110111120a020c101d0603160309050a060e061b12060108090c03010204060210050a0c020601060f02 74
    0x1455500828160700d0760004420b0700311514200303410b000d54411030b40010042c010b9807580010751200554220032807065124450310f001d00c5001d40480741e125202070030a064150303903000c008008001c0e42507403030b00c110b2000d0b01c00207100a11585050140b900142030311741d0303a00c80c0410011030445089850880034414040068580c0d140e02003440c00c0e0425000c08201e81c45140781c1200b24113403032462541800b490302d40c3c80030703000d100160400200140e02000c0c0c1d41ca60300b14205a141840034001558801c1d0050409483c0755880703c000300c8540001007107825052000010030500b0300040324086115401050101669486504085503550066090f221158401d46601081c2d42c9002c00c507601d1540600e042c414154401c1d0101500892401004c0d4202544070180b200010743c0a001241080146404100166402e1010019041e4001c008564650b174034000030b9101c0b00d21104813000c1c1440c2c04002642c1601500803581c0003a51503028110300c3e03003029816295008010114030440c032a01c0000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 703157553 1250 703156303 703156319
    0x131d01151403070c21020a0b04060e0307210305060123072001080903070206120601050c0a0b060a09061206180501150e06030c031b0312030f04050708161e 68
    0xb18058a21075403295420038080c100121003200e008019100b5802440400017003d40c04103170446030316440308042055444d58100301000d81035101030050780f8000082c0b10020000d0710101c00f03c2032400d090411101c404601c10035400c855044035030700c2c085010040540e04000c10003003c0c445001c2d141c9029818140d45440e019141001400401c18850200c1d200501e190b821040507070340141e0b400c0087d460015144d0200b003850007500798080740740c03103040c01044d410ba005601340c030800918901120600c19041c100000e1908044d107225024041c10800410803002c07034041d610584107420183c4205040a947d1480108420700c2050381010881c204c001c0000e0084c041c1c01510724040744221802801d0281c3e8480d0301801810041c8a0760110f01d240c0c000341c401040c5c800d0102c07500d1700d00c01040010301021900303001140800c81c2400300c001080261169250240030f0280d4000c8080780c800944880d80030342d44204540c0c0300d41440712000d03020002c094002900c80943c1e540d010104c00310f1b40d40c0b4009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 703158803 1250 703157553 703157557
    0x3020f0408070b040905010b1c18060e060f15090c0313120f0905060712140d02070303091a09030f0a020712060f0b04050606041e030c0b131d011514 65
    0x101586003c00074003000500f0b581d014440c0900f06407080140f078107040d90b0071600c8081c00d04500d16592925400029921030b086803200380450f03044942404103003248145103803070b1641210055090003815000c00c0040c0d02c41d000c2e8a141c2e1501414000e0252682c0d100e180d0f441d0070040c44100400d54007486c503000200364400711108859a5111032174000c409410281c01d09145410031406464103000d00c1d000304044054800c961000ca0503ca038407811200c880621911170340c41d40710f41050001032090f00b096032540c00138400f14002d0708101d039800004084a00c03102000d6a0f8184180c3c4140034000700c0315148402880b0803011801260201b555520f182105942c00610544403290385403811105c40e0401e020b0424074641c00c5a041200f40b810301c002440e18003860144100038030481d1039034031202e00d1584d16000a1500800c00e00c110713230b80d964403d11050740104650000c000d07001d00c0c0010742503a00c88490014860245e81550340e0380c00c0c1402c0303840f81d08100402c94208508802504071404442c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 703160053 1250 703158803 703158809
    0x10f0b0d061a03032209021602100c081305090c0f0307300b03060a11030118140f04030212160209061906050405030d020c0d1112120d0e011401030303020f040807 71
    0x2001d054101c1c0c17500c40f01440ca00a9500c484c000324010040c40840c44d501c4840d03440b00d964125000380d004291110120340b101110307603008201c00f0300052003039071040d00e0b00d0026046503c12155001d80b0f03640d004500c2e40b180a450b034006035903082440484c4065000e581038603652541ea08020114803603080e4425000d03a81440c50750310640e6900e80e4040307181401d00580e035104080c04c0080c4034005282c200d44910340720500c14000314105080d242030a5409682007901380442551035031301c05007044002c02000300000e60b0100d000d4401d2092810200058405a0700760020187c1030844010458007032181d0705d54003e00300c1d85d10444020101c104402050801d202810807544c504d81c4540c2850141443d260048018070103661280e1102c0d0125954216543e40d01544031002041007040007000c2480e200d0380070f80200c0f076070103543d949408011540c006003441c3c5003018820b101e40320b4804e83e054200d13400704103120711100c034180051000c05d00a400030001502554280e40ca050350710b202290408500390 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 703161303 1250 703160053 703160077
    0x140105040b01021c0f1e020604080c0118052811040f0905011a0a061107170a051506010e0405060108042d110a0801050105010903142d010f0b0d061a0303 67
    0x103031102d0895034041c1d51010346c00b101c08071400b0240d14240e0043c0da074030300c000c000610501c00000c2c0040040350079045010100440f4003035007040740f500e2030b010307031500014200c0c61829410392030b076604003803c1003600c80e48480c4c01503105070b21000080d090001070221400d042c145a5106c400240000c1c80074443d0801340540e00341c80d910150041d00401024800c96802001040164210100d001c00c2c08550729040b20180c2501400d0b41c0c80d208680790405941c1c25001e45a03008900d41000050340078001244150400da0710002030380f0070041000201d0748240c0301c0c076000400440014002908002907483e41000b4218030031241c1605008000b400781d03075020111860701d81e0f1001030003142042c104c1040034008000090080d50b040c0400240000d020f0310025140c82070b202c01011002600f4080408a200b442002e0031080040d100b201c8403c0e00032012110566181000c41450100140300d032200220004221740c0c5440015181c0d100501902d2a030902984822074010f60310390b90810040112140705 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 703162553 1250 703161303 703161317
    0xa03060b220b0a050301110d1a1207181a010825120e061627170d030905030906090307090504030201090318050108010e0a0b040608100609140105040b01021c 69
    0x11030b040c03141507031260340518020383c1011094000d020b401020744030808202c1030b00081702d42011501c0d1011107001025290000d0700b101001d03043c2c12010134000140d81d1105658404102c0401c0c002d0100d440d2002c1d02003001014090b8851307158440c00805402000c00340c481c0d40c2047c12406008002003110020f880422a0700044007102c03100c1d40550080011840c024001c980b07064500c08000110000111080007411203040884107a070301041010765807485440d80c010b544406441300c0d0103c50440c00e0409109a60b08074403c0b034428050316454580c004090350825030b0000078048641c024980081c0e041c0640000800c06119030704c180c501c500d00075030000c40c0036007072406d02504405103440d8a0f080344801500070322a69070801c0101381140d000c0254403145541e843c08540c010721040c8c000f130b50312909004000405181c0081c1401c01c03d28150340812485a40e176101104561400c5224945802c41c40300401040c0360030b92200b11810010700580301c2c0301d21040c15214840b01c403000501c01003500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 703163803 1250 703162553 703162571
    0x3040807050109050a050906063c1318091401060321081b250311010b030a0f14070e01030c0f24030e0d0521060a03060b22 54
    0x10400402004210a080c503c215604013000f00c0c898101c58018503000b13030b80640104000392203a40c203d450a0902090a80400032012000e041d586101c502c602d000b07401c0e219074480000f02520455560741c1e1983e1345001c0301c41c6400c09000c40d42c110a0760301080c080d6500070b40ca0105441c5c0700170403845000000001103440c1140342107400c10034641e1411b4845200c0300c09242142d9040b52009c3e4001114000130b102e051843c00c4901028483d07415000604840140210039910703504000e041c466100e40c49180e038a682d800708103404c0b645a808650341c5540581e12850106010b4580580554020400414503400394001c80d46010b015074404420100c0100040061060001c0301c40003503c2c0710756058090528011624244070070036444209180c08001c9000e684901960100c9a1052000e00344c40104030761110260454201c0007001c1c1122200c003041c02d80010344041d0a03881598004c045480031030035504d1b240b00510b5224080c94003d251603090a0604407203012015038440302803408500849 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 703165053 1250 703163803 703163819
    0x30b09060a060305030414040906020406050a140c19020d0b1602011103060112051305010507030b01020f010603050304171203151c03080c09060d02030c031b0403050a03031a0a080304 80
    0x4014079258840d850300005100180d0301108440440d00a500c0c2c10b110070100300d00080041a00a0004080620010303000031035907000405483c37040c01984515441c04283d080080c1d007445020802900c54008621540340d00c0340e1101c1039600f00307001500c0580100600e6640810300718058840e4000286020084107400c2c3c1d0900440d2015255010558110f0034980006450640e09482c03030810140c03244001443c05030b43c52031040100350010003d1210b81001c1c1e401800070840e80e0729483c014046d84541010001c0140200400c59602200442c40c251810990208a51000c000400301d130042440746c0342c803845500701850144010525030621202c03c40d04005201707143c120000c1ea407010741e1880401080d00042c1080d40032041c90440ba03503ca94007000030340c9910400a00c12143c500c007106202c654a03100c0b000c3c600c112400155030315000701001484150703000d24400102076a200c5003101c5c000038030940000c0c580c2c1124803841c01e04140c010000034190740854222615580c070100c0c08110142e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 703166303 1250 703165053 703165063
    0x12030405010902120304080c06030403050706060b041707050604050907020703061406121506120c09040c140303031909020a15032f0405040c1b05011a10050a0311040807030b09 77
    0x1300840021841d140ca40054103031038403105d220841c80f07003d001c8006000d06026804451719a64031603000c000e41071311600d02c00d0164200c0c0c090800074941c07040c0d905102c3c1c100017910000f9120700030401810140f4041c104204550010440401c41c09400c000200258030b034068100b2001c0e031000c88004c189006001e00414000c3c40c0c0c1c0c2d004090b44624042c9070090100001c0907040402a5410252103c0c1d00b443c161034a0341e400c400c950009040360400003070101c2d001440e0103441102003008503c0340c400d001c00d560307408103913440c00c1c422002c1004080d80c010194049100d10b4406006c0c41002941c0f00301c48141140d00c8083c0030b0200b40c4465400402e00e0030030b40300703007401007045101140d68880da2110712098000c600440b406141c1d0f07200c90b80b501c0d50040d6840c0c041c5c0c510303c5510b2482101039152850182050340c00c08400d50001c0f00040c0d09914000d5400d5010820b140e8a281c200034001e14110b000e03214801d1503c4988104100218480100344004800b860081c1d22007109810038071303606031403c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 703167553 1250 703166303 703166329
    0x8030708060901050d030e01031b020115053a170d0b01030e0a0b040510060807030c06030506090406090309080f0c1e0d1202030405040f0615080c09011112030405010902 74
    0xc0d182d0800188660764800c2000228150145052006644400c005074024140401405003103c0c3c04080c00d100705505421001c00391b45030940d4880b03a190b540c020300c005651202c40032015510500090307460102c008100c2d40c000d098519140421a5a5444449107807038038081000303141c0800203111420001502a007100201d0030b2804105140e0312031542a100c0180910082c5140e20f083c0229051100c1005180b01150101c0d0341080507a40c0c414045940b41024130040b40e00c619143c5001841d24040d200d814803e000251040c0c080340d4032640d54100411030303614100c06120b44c648000c2410341c010058240d90b80785450050a81c0b10380d00c41081820b40310039403003000364201034903070f0380b1140c41e9001c0c0007050740c0d840713025050b14440302d442c00e0742540100d420a903086451700319840902c40301768101c4030842c2d8140d1041e80c182120104c089031034400c12104155015801c018801c01544110004181880da82c0141c0e14808140c030880107541e40251420f0f0754680d100d00004055103400f135144008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 703168803 1250 703167553 703167559
    0x4030606062c150408070b19090e01121b2709082a0a030206040c0602010e0c09070e04050103050607020d052d0c0102070c0603051303020c1507020d0803070806 70
    0x541030902e266020395100c41000d80e0700608002e01c0e0300590380c68074010b0b1409816003100f500c407501d840c0e17101030660f40c22020412034004141420901103500846005050750b4118102030308503070a050740840d2690781c16904032003200d4401c482e644269180d006140c064907460a8545000c40107201d031000918650740d01c218510328024090002a107080106c601a004003690300c2d245a86030f0240e0850201102d40481c464010800c8a10405034007081b80d5201e60f2098000c40d41441d16141c0c228201d136056080c1403200c0d4460a5400098a0a294074550040003482d05c401c642124202090503036500f0b030f000321145e50214003403014a0350107005000c01e1014519100e1304280131401a500b00c40300e06075904c00210b5680d108030100d00350032004c4503c3c8050800c0291b50f60201454084018011403180e000000e241c60f000c00c840c00404204003810a030107074001c102d03001685040005008440711040c031003010070042280180c940b0414138980382c1c0620080c0d07071246482d035000303403900500a10240c8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 703170053 1250 703168803 703168847
    0x218030c0a0b0403021207080708060f1012020d060209040e03180f012007050409050a021504060212090d050d0504030302010f14010b0904112a03040602030f031b0403060606 76
    0x4422035580040c0c50484c2d4040310080790100c024424a400e252090300f05510074040d5000108103c440010054050345001410000580d9420075401c2c4000141c051000f003e003090b2601000b51602113074820110f8069240107180400490000302202d4504045840c4e0350804101002085002d20030382c40a1002640c14203124012800001c058030f0006940102c421003003d4981021503080111401518020f003003000b0001c05401c010b0fa441d0310002049100e007008bc888102d20303905920a4400b110805c2d00107000b08040528405034030b0308080c600756080417240b0035a60115104004460036129242c17519661a03042d424000e0954480f05114550390741803081c541400118060710368112200384c29080d40300d0040000107800b0b46000b02100892203404a121045a401c0a210350704a459064a02c90410f481400c010748a000300d04c01c9901681041c8141104492540c008640c44503d8408000344590440403054298005400507299140d94040034089107170040d0008100000400600c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 703171303 1250 703170053 703170059
    0x31e06010e01062102090415030b24010309030c05100c080c0910080403052a010b0306040c0302092707170c24090904140d0c050a0b0601120218030c0a 66
    0x1d08002c071004e19048110104807440e108803203055050703407940800100700b4801c1000800800030b08074070b98003007600d89840c00d0002c107000e40c1003e482010700102034030340d40c40a0b2102e840190001c3c0302c0e1030810b500f40035405403800001042888014142c80d01c0600028014401c82001070205000400024841c00108510b02c1c0d40d030f441c030700a084251054608040607980f83e2500320b9041c0100a08812100e440c3e2494a5040d041c545403d041c108280000704400c0c0420340c101591600d060301c001e40341103250081070001d070070580415036003c00e02201000d80041084040040200385120030b14903608003010511041c0c455608800740101741000030f00d450f0f003d000009440d400841c0d00303030030048070003403c0b00b050740010800e81746800402450001d19240508000e198200300807420041406511008121240182c0c088400e103908440140212000f40d0741e8011041d0018202c54140068208240300c0c00c1c04c0750000740f68400e519610501e000c030703084051604c0e008200c00c90901c10780d0809070038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 703172553 1250 703171303 703171307
    0xf0609031e08010e101509050306060a032004060b0d090b1308031f0801020703091505070b010e0402010e060c160f1d04020f0414070e0a050105030609070e031e06010e0106 75
    0x40b90548280b03402c00202d83e1a0210040c14181c100e030322024481800201c10446513401601500885800b98160b0744965100760402c95a01c5103408000c044030304882105105622426140c1c0034500041e01c00900703103455125038130b080c1e0040c0d090170200a0325120444100112203031400d800856030802e02020301da1980d60300c8803d00000b41018003410394507860000130000c51101d2801880b002000315643d210a003401441c00300d484c0a03606402c13203c03504274001c440c4120106c1c0d4500b03800c40155811a400d2004540484402400980c1004140031080b00550794040c001c00d4035a01010007808600a21850070151840d180e104151015140c0c3d01049075031b00e1804500400b400506401d81190340300e10002c0c86100701c010105810618103c4201d1142d8601700d0101d020300705c1912400780e14600c2c00100b2814020078001d8500003072050010445500380341403100c0c0c0009450420b1618844c280f001700e850b0480d602c4440f00a240d02030148407045400740b061a000d00a214162540780d810400c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 703173803 1250 703172553 703172567
    0x109031202070c031b030611090303040b0309211b16090e0a0b0405031309090f06090f050f100c0903050c0d03090807060504140f0f01080c070f0609031e 67
    0x80c1240301900040e02e20100000c0405400142d42e000c43e40c0d50710118800300d051200f0980c2d0204982052501c3d40383d035032038481d00c000d0307481007840240214a01230030241e43c29129080680488118400c02c64181841e41190240c0380d9a550b0398003095448083e0411100c0301c10210f0040e82a40b6000700d54078202c80102074400700251402013002159030702c58000282e2800546003c0602800c40c07900900c010010080300411808242c14011000d0b162100300c0d05c01118005c2d08010400452540c54500080f0f0702d030000f03480701c0d025025644603550213490701400d100b840b040c402620307000110042c0d44c80c0c04900c2a00098a030a107000800103007550354050b0f0700c0c103004c1c52051280c859a13081c1c00405110b410302101030714002041c1c80c04280c0d02c12000d03205030454052101d0840c2e04000107a07050070f1011102e100380e00001c04040700740c1545001900c241d540508a8502d8000411404001c2101c04c126411601e1103102d00180c401c0180c1401010780403010200340103808005010008550712080e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 703175053 1250 703173803 703173827
    0x3030f0218090c0c2b090b0712050408150103030305070903020306010b0702040b100201092306060d0501021e0405040501050a0f0e061f020a050714010f1b240c02010903 74
    0x81d6181c6a0f110003194039214041c0c05910925841a80806035031203170582d0038400c25500190000120300c6841c02c00340c07040c00c028000c46103000303018044600403030780d0100b41e4400e00280d810802d24154490080380c1c102131100d00c1ca09150b00046004004040d1706115a540c04001481c1c5801c1c2941140d0001c0d440703401c18440c06181e1880410301c13409559032540102e0301074200401e841c411080b006806400380c0800102030741c1c6000b21040ca00300030010b0790f030082d800800400c090038065603404104a0b400ca102c140c199040e40d405c2c0b010f60002580804d030541c444902448041d107403442d0108020503508140c0000b8068140e074441000100b000c86509001d0300d140c0c4401c10744d5562401c002c5046203001035040c280712814805001d00a64005c50b03540c4c00540034006480c011921758402800303d90104090301c1c0050341e806c030402c01203841000030300c20b6140318844448c1c8210160303c9410b518200c80701039413284014081420540c0880340300720074143d840c500091011000a880281c080c0301503034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 703176303 1250 703175053 703175059
    0x504140c1c0206040b07150e150609130c06031e060509060105031906090b0f0406030b070c020d05100213060206060a0506071a010e06010e0a0f030602130e0109020703030f0218 77
    0x1241da004564428054501a160002030703140c4821007070508011420103190f0340c607803161030166180d81e00c90000ca69401d80c2000c821400f445606d5880c2442808000100442891040c01002100241d401c14103940140070603500420900802d01d0b8028031502d403110b10104031803820700c041095494a4542d070b5400f460909201d502c0f99100c43c1c0251946c4007a90305200c1302ea18020020030741000c607034001e000030712060314488141e40c03210040c0812201c140c080500318404d00300c002000c051042a07038254803031000c2c00700c1d155000300355201441c1100500e252906d50350085205502495030300390073300040c021840104036504040d0003060781e0141600134140a51000190340f0b01f0300040c4040100c62030712208020b2031035a55500c09040c104000d8807200c0c00244040002d25003880c00c016500141d44921040c00251440d542d518002940002e82c4000f808030020307800501d040c0c01c0f2403001c0c0280740d41ea0300540e440070b0380d24008040380c40c8102088045403050000318051118050842c2460b901070b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 703177553 1250 703176303 703176349
    0x20423031e0a0816060c180302040507171008120f04060804080f0307020a060e031c09020f0a030b07031119140c010f020c0c030f0a0809010c150504140c 67
    0x512505024000c80b01070482200040c0c1098503200324422030b000f02e4042c0ca010000c0340030305c00e8211a0b410440c4514002600e07600070500251810754021a0000580c0c1010380c2138040075030700c01803250022100040c95200701442081454401d001c0355803401c0d00d5218040c42c0c10601800f0301650300650090000b003190001c005010060780030100c0740071110103011a0b40b40c6c0b0301000e0003980d1f1440840d00301c40c41801c00541c001c1d40480041502c07411242c3d101e1154600c120794041c3c5c002000124010303070f8481000d280c202d103036403140c4040c50051402818907207610314243d400070b001c0e0b488001603e0200c841c2000100c0d075100c1d00d10003608603800d00d071400e007000d2100414424003a0191100728000c0754a8102c102e0a902050303030041000848540070303503400000f100101500c40f02901c250020903004200c640b40050720010051200e11014100303581410115104c070202c422190001070740442d03441d810700003882000c28a010724058440004c040d00000d05010500450380412001001d13140 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 703178803 1250 703177553 703177603
    0x1031e14010b34020d05030309010c0201020408030f1e120a05071704021003060f0f09180b18100204060c1a010b0a1817070302090a140c03060607021302042303 70
    0x3003c4404140141c00404403400c20082c1e04000352070340d006440c42140b40d03207800ea0100000303006000ba81d0440b10781070091400e21444031312001441d4808140c2103c04124a081050300d0700b4a5805858149501d0754039902d40d2521428520807540040d2519007400440e031120200d4118503282582c1c000d0741030303c44080307520b0b4814060b005010f40e500000c0c40e070345a110001c01c074500080114400c82300d41280078002100440320500300000c051070040c005038182000681ca003807045003900c60501c90740c0115680140301403440d60403a00141c01ca080042c030002d02d00b4084c0320038100010909002c2610360701d1a545800000b52051040d250800c0900045000e110035940700c0140d841e0041c044004c403002a29100b41145841e42c4003408102d12600310707003011a501142601c62500b051192400c021280d440303480b00410160001482d4a502c25800c10940d03006807100d0800a61031103118002503160f6003031030703107505100542c07c50451042c101c00c21656803596000170391a44582910342c0c250b00480b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 703180053 1250 703178803 703178887
    0x1060305040803010b090d05010e0c19030c1202060d09050c21060a0b0112090503072f060d0219030603050601051509060309010603080a050408070b070503071101031e14010b 76
    0x61f04034054840e52038121240c464071008a60b00e112007030100d40f081c1408010400580402c01c4a00004d03181c5140700809010a4140105003c28540010011803e119540c031490056442c101c0d41110303290440e400600850801868800c00403801455816140850031907040d900c2c1402000b1021070307612400301401ca64016902c0001c1801000c0041c0f260304202e003401ca64a034040d15084030003942c428000d03d4241c244540310801c407401c00e40c0c014814080501004560f030008108803100a0742005500e924240c1003040b8609060316440200e080c40c50760900030304010b0140c0c040790040d00030020480207081000c1c01ca030814902200e81548036207508286a004254940008201200010b401880650020007078811554654200c807591a281c82c01c03010030340076a4500610903070091100c440010981c04c04040303000b2040c940098844640680e031148003100310b0030f5140069484005a40d05100c008046015144070880986400452002c03a455142a85c9031500a501d01d101c0c3c08001c11 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 703181303 1250 703180053 703180069
    0x290f04110d0603020312030f011701112701030b0303070602070510020703110c031605010f020c13060302011107030b010b181834051c06080109030801060305040803010b09 75
    0x19014485081e01c0d04041201e10004110780e000582c482e124030078581c040b210760303241182e101c1c1403801c10b1084140d1a158042e400ca0041e0384564880303548079151150007444d1240500006031045070309031a084440354032002e40300a010b1880c0d0405061803440c0c1c4982c0c4001085503011640148010b03500d0700a400c1590401c0e440d0750300240d1060001030180c051580c094210541c1c550341d10305039200440c40c1ea0400d0354801506515010071240305000b0000c960080d1000c820503602401503070282d00c007a1001925942034181c1403042151396260031b20030341d41d11810600042220000a1103000d003035440d24511202c0521480c3d112a40001d1181002d84580f1016012000042d150031980000140301c0080000120f070010050320b007408086800081d2848400c2040f540202c0b0300c100d0b040454011038042d4040c80c1481c000201d14a4003001640c4544203071070040044900000d08034172146001001c0b100180c1c0f00f201098185414031010030080b0080702e0446042481850759010f031000850000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 703182553 1250 703181303 703181321
    0x703031407020c0901120b040f02042c120c0c0d080d0504080306090c07031421040f060e0a05070501050a0905090f090c01180302090c070f060e01290f04 67
    0x31035000040c0308086400040580d6440021241000140c1e29105020f50182c00c51070003034165040300002c100820103144216020500181000c580001912004510340440b2810710070100310300c5c1540201282e05204a01220844914151420720145501d560f10005030080e28459801c04407040100300c500300880d01c0c455140c050520951a0a08144a641e04201c031201e005e074181c4c1001a981e4890303d01101c010039415250800914210f0645004940005040300c28030b031904940039806100d07000d45184101d126512602d2a10001d28181065568000e8500c107545d1200303a00d10700140011495400b501c0c802c0c40c042e40ca616803080c044601015a6114903040305c1d0341d50503c800031469200440c030802001c1c080b24000d234010001100d9004e40468079103145401c860041c0010b103820741a41e600040303250500c5081860a0f100c0ca5103040182008440c2a540c0d0005048118001e000d800c03031061180d00b1082480c00c0c200d205201100c1100355a910801914000030010360307541d4450000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 703183803 1250 703182553 703182581
    0x5070207050909071a0307052a071d0f0402120a11040c03090c030b190c0e01090803040f18021b07030311060c1902100e03120a0204030f020d080c033f010b070303 71
    0x440e00701404c5142c842c04449800885030045600226004031581d0f10242e1410382c0c2f000c1480180c1d546064461180005030080f40c1c442c9000500060b100e0040145450050140c541094864541410401103030030302400082032505180c0700c6404610500c140d801107070741090340c901895940500c0f0b210610b9002051603015440c0011025150303a110440680022080c0c0b1040301141c0c80700d11071903881c0218401c6000310058940140507000807215900e0b038118179150090705040f03404141d54000000b580a040080e40401010000d150f80007a8069054034004060012403c2c076900c503100300d208540e501008203080d0300a00e02c03941c0c400c01a4001c940c1003000c08000c0c4210300158503440e03038403c101c0e0980502e569004600c10401c14400c540c00c90b6071150409004500d1503080c0641d1070301110701960005024090600c0a20040c001031540310000340010800301154400351101200081183c1034210058411620282c0e03004807144c1514900765080740c440c552486d00314003501030f41c0030801c0707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 703185053 1250 703183803 703183837
    0x507080a0b010510080c0405040c020c060f28080a05090c100305151c1410110306040608030310091d03040f09051e0703110d05070207050909071a030705 67
    0x30601144120403816102c0442d0300700608404890b00301d5010070240d0b900e80038003c0800040095103040d82c42030003983c0141c0180d414040c0c0380c0340010b90700d401400c64032040c40400140e80c8050b403010b080c4061355a00844c0d0b900900108084c1c02410f2410042c1225034081d614004100c075808108841ca502c9040103100d010503452815004006e482c0948400b0446118030b19140d2192500140268407030b9080c41d40c540b2a038105072078110445a204d070114bc079034003600d01c0302c0000c81c200d4010041d000988100003561f134240030051204580f00c5902030a095001801408062078843e042d6108840e0000c60210340750301c02d0103561009036400b102d0369059110010703000a486050042010460b0040b21007005250b542010340c4641c501e4000d03ca95040482400003198540250311000c1000041e071000c43c240b0105500c0601141c1081c1c031601c01680c0080c0007000985807014015a21801c4d082c050300300c3c0c81c901841c03028200041000060b10081c08000181d80a1041c000d40c1d0008158084c510 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 703186303 1250 703185053 703185073
    0xe04120503101502010e0706020d02032d0c03130e01121214070b041a010501120e0304170a060b060c0c12010b0a0e19110d0905120a02070f1d04020d050708 68
    0x2034000c01b40c84000c22068001d0000c00190180045007410380d8030a190003452400e01c0c1c1645a121030884c08140585000c8040350301d01100b00810007800194020b00000c581d01e030240e003444a0b481603580e02c80d4604518a100501c20034814040d2008001d40c0000261107480f4400300030b4580808091303445c0c8100b0130101d00e4405020084000d94082c074009e211001001d40c40c040c000c0b1940809005d01d5000ca04d03410229601d5080c20b138401e042c0c50300410b00380d13400c0980321100c00c0014120791406031115800314a034481802024419100e00110840b0003a2030b00303403424069500c4510301c612092182002c0e000d4040c3c411005e40260746408001407004412503186c4490119941d03040e0f0307002c0c92106041c0b0743c0c042c0066240c45010031407810f020425061614028184016101e0301070b0480e0103004280b5907075410b00580c03014006004042d00506500e030f0400988400c40301c0706901c2202c0e071008940824001c414040a09170b042501a180380c50f03a00801e05059290120550004800b803144090749 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 703187553 1250 703186303 703186307
    0x50607120b03030f0f0c0a080406050a0f0807022a190608090c0f0405130b010e0a230601081e09070320030714041509060f0e041205031015 61
    0x2010386091850100001400a000c0c180e0720700503540c08030340c81030381007260342d40c010350b00300290070341e030342d0040c2256111840e95440d803c4981080e441074001c2540070400511664101582e000c2c0c2c80007515083d025454880340081d034800402d022115021101081944460000201005102d9000c3e000460b440c031131380c1c1c01d80268541480350000065149020881d45000440c41e0206503a000304640e010b01e292030100002014041c10b0f00f0509914a242c2c200081c3c016800b59000f010710700560442803808400341710941d00c9a11020b0036050729a181e011a4400341b101840d00500300f8a41020180e444500c06155a00a460010340f08004002040001c80d80000c01e181a00d120f4190405141c0c1e1000103846072a4a0002a50303054100d9201800b41c00e840002c4110b2401d0028004141c015044c0d02c0e0000321001500451b0500b5203a01c000d02903a4003031044a0014075920900036180c0c5019241c0d20b0011074542c203840c1c100513000001c28404a20030124402078800e02050501b812144a80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 703188803 1250 703187553 703187567
    0x1e030b030f03191d04050709081005070f0531030f08040504200d2004080a05070506030f0f0a0204031a04020a09020c030406081801050c040602060c090f040216050607 73
    0xc2c00300c3d8160440350444140c4a168800f020f01c0240c103000312103041400400001d080014900000c003c07500000144032042008000c1640740b010b000003c01d0709009600600581c402d84100d818840e08000000b10056000342c50040e021503d00604411200200b0100700454180d1020b001e5112102e00e60042c419604010300841d40111410031480142a2082c40280011b5481035144001440a0103a02c4000d030461a03a00311034a41c0044048011701d070000343c0c2c3c0c000c1e03085084194044c01c2d4440411004100b0a00a1304003240c40d582540b401080480319201c0041043d440b2461401c08954030148980641d005544e0050b10050300d0341262134840c9845504030740580c0300c0c07000310000083c0108a0310842e0741c0d03e0250340c0954942400e0500030f8a24400c05448820100c0c510010007106140138480c00303000f004c1c1010016a82e514240c0c00034034209010744608046003040000d03c80381c1c0d461131012008520240d4015848079210045000c00b00c40021020301580129002c214040342e00144c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 703190053 1250 703188803 703188817
    0x9020901061d0d030c030e0307030b09010f200a0c0f050303040311190206030c090d0b07030203010303020f0102090108060d03120c0e042003040b1807150e03010c1e030b030f03 77
    0xb0341c030803101505400c200c03403051840760240100d1501c0030300c0b0020911425641a001401070111944145e4030f40d02d640107114229008c0c1b80a9646890501034103409000d05118a400c0d51050b181d10000600c0d60200c038030a01181605003c09015683c040180a02d08091101e030007000340c0c1e1702c03894507081c05000c0b09240d0004640c1c600441e01e508626040000d082c802c41074001d04481d00355034071795640b0a2250b200d110141c1c1d11400444204002500310751a151041d05a0ba5002d40c1f0303545145000391424102001113910703a4018000c414050f64070106c4942c0c8590201c44003001075801d804e0655101c045054074040160030500b400c2002d940286904054410030788040061108203421442344141340a21604030391010404140409c810000750b54000b040340300500004410450301c9441c0c269254440104c01100361140800e031030300a07075000710310380b801c1d8000c4c0002521307104c1c01005071800884070028400520031800c0342c18440c0d40007128038103001c1d08403001002401c2d202036803a04021 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 703191303 1250 703190053 703190087
    0x7060806031603060506030307080c0a0201080c0f12180102070609030f091d0405030c06010f06080a020c19081306020a06060801060e0c0a030920091006020a0b0a0902090106 76
    0x1102152840c01c0000720640c8619010510344049819070752420060a40a000d082e45071000b8014000407618104c01000720f412042c000740f05070f0181d0301c000b4060840090140900b40c20a005a1219607107100450f802c060103030500a04569030084035007402d8007400c1c40d0520540c40400c01100f001015446590103d000f078a403038411349051641210005103500903c1c8084040545194240c907013600d09513001813180c41500c1c01c106521617010304e04042640441200b402802d0308210840e08008243d1708808840d2041d031801032941043d03035882101114100314241c9a10000c0140401c3d03000781c0f44418000740c0d4559039141d031460008d40d2050342d240306440461070004005480c1c0e005100340780032034009006280c07a031b6465045d07211154024005000074142c80e050b6000024030220140318100894140c81c6400c9000b00e4284480114001e00b9888115043c00041c02039540001e038001555610040440c00c0e42c0d504156031000c2d20004038002e400005440004c03032050b4011803003020041c028 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 703192553 1250 703191303 703191317
    0x90f060902210d201614042d0f0c090302130b15071b060504060f0809060c09030a0812190b06030106050d0b09040602190201060b22090504050706 64
    0x1009840101d0b80100c00340312030340010b03d800c0e05280103641c000f03105200a00d4444464201141043c201010030055402041004d43c0c18071201d400440301c1071000400303403000c01c10703c02842a0b014070001100a20b01d010f980750408078204455a41007543d4a441142c01070000400c0d0076409401041c00380400c91058500405c84405c4507114422580c03010001031605201c190701c40300c02c0245d9440b5010540c1d101d01620740d070380807414600c1f02c0c40c001450b26a491681d518982180103140e0307041642600c0411845100748002024002802c0b070b041a89042c1e4265078030001d40001e03140000040e8020035480010a1680e0011240c80c00144942914000f9003056103603101071100325100c403080d0a80c001000c0c4014081e030341c072910142070113085101001900b202900006031141c08211011074540d41c00107220161030030141c0b421705052005000a0007101c0c14503c6503041c07405101c0000820000c039040d0702080030030340340d0503c0050245020800030b50915003045611803800740104000300e219 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 703193803 1250 703192553 703192579
    0x51810061d04020a0e04150c091427090718020a11071508100503150405120c030403110d0b04030c0519030e0d03090b1210051012020904090f060902 65
    0x40c030801030300c5154000c4c110403a49041c403140749004030b00038005440400c122101288003400300c0c8914507441e00c50f5160140401c0c60041c1582184900085c2d15011780813000c0164110b0012490f2900c00f031950381034040d1180d0b1120241e500d00b1080307038042458002114800340c150070a07540200080500c0782d41e00c0d0200d48411040c0d81d6180345d54400d40d0b00354800f0900c3c1065551040c00034030340025030b00c2004400079594200203450a9140c01c40da9582200007424042008002c100c410b2507158040c45150900a0300c07042c4640f28040c03440060b0841c0007281c0d402c0714558665a1041c0240c0e0300200c0110f10781401c2c1002410314000400c202c90900c110445001e1680403c24030044043e13059030b40c92284201c2d01c052180380d8510030800c40c1171100388071010440300b000310041c09a0010303ca49130f08091078441100c004190355a40503034081c8028015030b040040c0c1c00001c410103045003540c0541d4601000d00418002c200c03240001d070103c4021000401000119040010140d000b15040c0307144800e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 703195053 1250 703193803 703193849
    0x5030d06230a1215021204080307031505150f0c030a0908160e1807030210030b0307051c03180f0b040608310602070605040f05071e0905181006 63
    0x3040c2e014100f85004110b0428001941001184614010101d005400d007404403509122611082d10105d801c0c00b80030041001d03550b803520420082a4806081c001e0684c68080420084804c5020034078901d84002001c008070390398081250349030582c82d41141e5903000c000e04001e04010386401441410b00500162403003031980401801c042da5141138800c0003a440e590404c0081a500b10041076042c0a107440020150f0707156018008105565100854200e081808060509500750404c44c0308414464a56100c481e002001000d4ad6916050040b000d040b48500c05440031180c0e800b8058046040c03e0210b010707030001010308212500d989941103a91641030189221102840190b00210380001c0240805803107068103040050040300d0051421903151101c0041d140704480c1030f26403505800740c980c03c000e01000900c4c0103040c0d41c0030036070041400301e441d012600c0503445001912500c0f2004580303003040b020f0080d449c00a0800c1221003544045203050007170002441890076002100c00380f442c00703030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 703196303 1250 703195053 703195069
    0x7060908030304051c031d01020414040e0c040b01050c06071701170c1c0506041b06050c030315041404051509031c0f110d09021c08031305030d0623 65
    0x140d1010145c000c5403619003500c0c4d103001e040b10b0380c44201501e4050702d85005110188400e200001d8800140c1d81da0704001f003001c11000c3c045203660103a0714103414501c08030320114100080d0441180c4c0410600c12640040354507000e80e106c00100360042c4418840583e40024407000a011040d011a100d41ea039821204102080b0700c49403031103508140802c025610b0440089d0180c40d29522526414064580341c0905d400001c50701224500c058113610100c01120f0081c12000344024074120340350140b980300e4141c5901010b814070080d5020a190b010090703855070040f185245114001c01d04c03500c3c0a040c150f540350049604c00c440385019102080c03a00b2800700c100c41600c03140e0101140a90402105200100580703400409030340d90782d44015030b07c1240c004c010584641c00c550041000c00450041192803051090b0400b03403d01905111000100701c1c2054a0380412800549a4613040c2802d1050543c46103024403580a8509180403680c9180504441075546940512006090074142401400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 703197553 1250 703196303 703196311
    0x8030d0b0f03060711121614120a0e03011404081201060f0f0c050f0604050f01051501080408070303061503020c0606060915030c04081b040b01030b0619021608070609080303 76
    0x26401000006140502403c0b688005c13180e600100d800e43c1140c0ea2808003241c201c0704000f40d0a08140302d108041c4851841c003103030145510300241a0005092150040d00d01c80d10345c1034014810540c010305140c0c0d400303510455200c0e83d5400140d4152402d8540035200d98010603e02d01803134842400416001d108030701e8150001c181d03032a042c9250b1903050040c3e07000300710180b042316240b1071480d201031700a40501625009900c0b0300c0c020030040c80c12061985c03d49900900b041410500c040c4100c6a60b13a10400302500240c000692941d540b8035414110003a04007030300014a8404011081508030780d15900a25170410840e05607582512100200402486903401d010b0b4018500d902c4030440304004402540c00c0006c0410300788c5000e648449940c141a0541d040082c1e07201038849a14507402c0c640a8411600d500b407a040200d030780b0350400242140103000303081008065103001103040b00c0c02046103040b00c0541c1c031510030030107540e118610355404040c041c2c040020f07581c50000805500004c166402 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 703198803 1250 703197553 703197559
    0x703050a0c141303020d0f2604150e09010b090307140f01110a0b0106170604090c03080a091d0405070b1303030e0105090909060711030a120209180108030d0b0f 70
    0x258001200c0b1854054000361159418003403030f1500080140d5510903080e9900d485203900c0e6040a0060510829442d01400c0b80c0a00d850b040e01c1036a12582da0700700700c5059820001c02e075080206200c1040303908188004a60350420100d06c004100e284100b0702078103803080214125086140c82e0030408401a041840760381d0044206840c41403658051450b02c035030b0887c0c4c0400c40300c2d03105150310390114007802a400600454002e2610391129444aa0f10a50048041d181131010200c60f6440d000d40c00c9580c840501100301c0411541c5c01c5074850030810004200156440344291702208200b14800d1041c0d0b012a031030b100d0070000140f07104c0c0001c2554891440314034500321071895520261110002a840301e41042400c0001003c23071b40c1c072001c100d800f40d01039000070040c0e4500500c2c0070380b0481044e10240d80c2c582c800c1c00b20000c5241c0c4202c40744610a00303c0c2026032210300b5540490107000d0741c002450b01c2d0740700c40d00000c200201c000029005040b0300c4141405000322205c18030181041c540841b42d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 703200053 1250 703198803 703198817
    0x709182910020109052805030403030c020a0905010501050d0c051c021306140d0908070b0c180a0f061b050a03080712050408070b15060a09050a050405071b03050c060f0703050a0c 78
    0x380e68003840040010043c01e02c82c0021b0311000c240d440c20b0560303005400072004a0418001c034015821700e4403800b4042d190045081100d5410301e80081c0950181c212525030707582d01c1c1c20207124490710900503107040b405d001c0f0302d084a005413180000042d4020020910400a240600043c0e540c400d00c000d030f0352440064001c81c9808040c1c6002006010b44101c140c070924020862030000500309281c40e40705074400519241c4944820150000300703074010050b90b12a01c0c02e482c00f40445810603841100f03c80b0301d414034a809107110f4200b0611482d01200c041e03e00d01603480007005164010031201e1280001d950b070690084001504a0100d03a0b007960040c000c3c4405000400008040f0341800d40c1003095803003c08884045000010901c0e40021004400159034010402840c20200d600c1805024122400c0c001858642c0b00144034643c1c80b83c55015406030420484207260003401104c40c51803921040e6407203450700c062040200c9600b070714000006881c010000d107000740c1a1082e44001d18440d510b070301c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 703201303 1250 703200053 703200073
    0x9030905121e0d051c0b060a05030a050a0902031f0e0a05060106120606050403020f0424151d010f1202040e01230a260613020117070918291002010905 66
    0x38001d140c00d1280c0145d07a45011000b50b5960302c102400c8042200c1d9501d0703649150801d03100c1d040c0c0341c0151840b94000d0400b01c5460060344d000c200841c00491410346030807000b080300c800d403007e070109074000b400e68001c484203142440340115401d41a0b458035105c0341111100440f00d941106e030710b0710500001400500041c4010f16000341250041c0c64002d00c04515400d440e00d10001e00c88404040307400304031032018200b225400d080d0f15660001114103000e4540c1c100c2d0b0004010218040780828100513040d050344040d903002c1c2c02001180440301100b10348a503111100503504150a0041d003085507008280700440d864519480e0b106950702600f820401d52402140d071007a40484e01000c03460900400300800c03894420815940b08124841002220514500025007200002e0300010b03040100c078000c2141d00784d0441e20500495030040641c403106040008084010100110200c0c812621030b8070600800701e1041000307000800031580b1103090b600c3c2d907100345d080764003c40d0000d015401200d81c41d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 703202553 1250 703201303 703201327
    0x20609100c0e060d0f0c020d0507060203091213030221031b030904180b01060e0a06110a0606060e01080a0c0905130b030a0302060f060901030b01050409030905121e0d05 74
    0x902001d60181040480b0742003060020f240768200b501c0100f401130f80c8030074059641303c0310b010b2221141c10500180040b04081c00c00100319106400c000741030960000045240e8000404c170001d0756a0f00003107082c3d207603548070705e062108060301c1c803041c1e209200445290380010130b2941c111140031980402545130400c5000300810080c1c52000d518030600040c0107010054565000e9400c1984610000425411403490540004070040c1c10400400c110100103502c0d07600c54070303030b01c0041d00c0c07540c01e061070510b8010003101e25064068000800076414010005419500b020581d0a8030600342c03981401a500c9100c0b180484400c820344a001a00c1c0c83e030304001d00c0c202510b40742c490030315042001c40c40030501d001103840d000c0a1841100145e21010800c00484941640300e40c1042c421100d12040c1d500d50307119520100c5040c0902d91140d5501c103950410180a044104024100588064030300e00c1403c0300c054654103444103210400340402d240081112010400d5074105103a61101390a0001e200b040c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 703203803 1250 703202553 703202561
    0xf010e01061e0e0a1806081b06070503090a030f020102011406060d2c06010e010f05010c03200105090706020d0306030b01060c05150906010302100203130303030f020f0f0702030d02060910 82
    0x16042c103000058601021036100d00b02103901030035400003115229030014503001d04490003540080182d4010320020420720030604042070701841300302c80007906e64800d030621034154400d0315062980150304800001c20400c001501d02c02c424001d0b00200625540044640c0002e0002c03140d580c2e000004100d80c1000c9045680200c140d203050300b5241c0a00440d90f961041c2c06110b682e00c2c0c1c001c0d80e00c1000100003403210f03402102e0141c01c0749940711201c05c1c688800030300b0100200c50001c051010f02e18034800310980d0b10004c5007032490010001e0005081c1622016155002130003a400140101c010415680d4068001e10701202d0b80015292603580c0b0306074048400c2181080215168051801d00ba5280031071a4000c0e4001c0c0000006050b00303524510400c184240404810000d64200f03020b140307060744000610404481e00350a0100d040c03008090a50000c0c42040b0f09103006800108a00904444c2ca8010b031030701134401d5080711050f02c0f40217001d9942d05c8040b9000440c030b40c08207035034800051250700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 703205053 1250 703203803 703203857
    0x2040513150510030f0f11011103070602030a0915050a11070c1701020c0d170a0c02062403010e07050f0402030f010b0705010609060b0c010c03020310052106010e0f010e0106 76
    0xc070060f10251280e4a91048029100041c3c422842070001042032242c0c1034a1644503160901305801c0c0d0941944031a5104c1c0a508000380103558084002513440c01d054004d61945580541040c409007074180040004000540f03d0f19461032928402c142e403403070715000b1104441c0d00401c3c4804038501d08402204bd21341c5840401041d0f540a20209072841004c011654410310700791100303001000780203c0c0305c0740b0b140000c004822140c100a45844001c1d00800e405400250f5024003001149201104c54107040d044c1c591240c140d0f10740b48403400003010218224090740c10440720311040711544410823091703000548048140880300c000410503500041d00070301403076102d4000440c00a69138803912040300c08070303400030b00803200010701858034110a10540d00c68070041c0c2411415400c004020030039242c114010f01e0b02442c0c40354440b81c002588580003070304d804001012102103684401254020280c251030000c2d000c5020740021882c0d00361991018103850255036448900300140d44801c0020000c44 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 703206303 1250 703205053 703205071
    0x80a0e070b12093f0a05040e07020c220b0609100f090803030112030e0a03170702060c0106060c0302161404050a020903331323010903020109020405131505 68
    0x41514115503131482c06025801d03948110030345124800440c0c400401c0803a1020b5801c802000a40c3c00c4680003029130307059480f024044041c41e80c4189003a480c10b110512280d5220407882180400345802d003403510184903100d00107100005406090000500a102d8529400083e003252501a580703d010003d400078140c1c030340300310115a0b0381d81160450740280c00c8410110203c0441c4d80c28540c20800d5086d41c039405451884e1000d14548980c003801c0c00514174600040c0e00018600255036600c8103684200c80810000c01100355100c0c40901244140380048000d1b008800c0740d00542c0c588080e2030821900451104c014400084042000414000f403038000701540c240410003041c0c9041005800140d41d00071701300c80f002d07694941e00c11000400b500c80200c4160350010480c2110541d0100c1464981c072041c40d80c6802c10004401091918246d900038040d07180c500075030b05241c0e05401040c1340b03038001d81c1c0c2000b0684503030b20140d912904403076000d0082c0822461a074510100c075401550b015940ca = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 703207553 1250 703206303 703206313
    0x4230114011e030906060b13030b070c0804260f060f13060c0c11060403050a02040c05070f0f02010f050315120319090305060f01080d18030b07080a0e070b1209 70
    0x1400c44450203491109802c000303036585540d041086010b2043c400a040d051005ea41080e03000ca001441f40b2009010042551100c64080f500d0907004001407040c00e43d0144038261565281d006144c64101c8080134035201c481c502d010b40603282400301d14503406040400141805681c0c1c064140c801c6031000e0040f007042c0c40400030501c040303541445100c1200e44142d0711000c00b4000750419151455280404a1144000b04030400004070001030703064038039605035004103420103140710598443c02400000341050480c80404010000d5042291141e20710136210345003944102c0104444a02040340d00c080d1304030f810000c0420600e480408000360349840c8003142c1c070b4009035401000240016000b250b001c40c0c24050b0034404c03c0f9040c014603a001c810922104582d62500c06603541d40c124004040c02800150200341004d00b41040b03404000c0e6400113021101410b03d030300002c0c0340340012210a540c4510f41b00e609040d080c4007241c8403049070781c4440090f0511811000080b18110003401304a01842a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 703208803 1250 703207553 703207577
    0xe191118040f12090f0e0a1506020c0424260c010f0e03102d0e06010b0d111902060702060402030606280f030209010608010501050708030a1404060204050423011401 72
    0x85850101c00351046c8442c3c00d40d182020300700c1c24151980b00d210100c19411848060011550014000c1c543c0c01044801017005040b21000003842d0003d114510000c861441012030b02d030002131034403000c0b10f107d003440c1c12084800c2007000d500c840642e54050300203078045030480300d40ba10a211000002c1d00040588030702d00c9821084104450100e8003401c8594511000d01003084241d040b01c01508426050520165011102c00c0d40c660205004807031284401190200404445900c01c2041c400200e480c03580d0303080d00d10011000d00d10300881d040700611034040054255071001c24038600a035405001064241c8460041210640500e80f0001d00e5111402c00010b0300c41012070101c1c002e010262555420604500521044501c1608100140f21103132004100a03640581100c1c441500901807507266201d00d8209000b4141d0003160131000c49031102488180719480d030007401100c4013103604002004481404910000310211420240f6a040c0c0040140c1d060712070307408018840502d0070352607401c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 703210053 1250 703208803 703208819
    0x6070f11060f15030109112107030c2310050a05160c08010606020d0516020d0f0308010f2102061b030c0102030f010e0603100e191118040f1209 63
    0x641112810102c0000b201030018485482140e0610903000f913000b44801403640e100e030a1103c001c001c0850260400440d03109034050300c0d6100b800d5040c00b00d42905c201507500c1c01c2c0304003c54587d006551025a1200e040079604000030b25107414004041d00240c64002c030044251903680004951a09201c0c0400084203804082181074148a10861a156030710b4100b02c01d460844d8400d800903019948030701c00e001c03012500101074541d030612071412850f8138221361011403079281a640f801030007880c0209940040540200c40706042e2140c5a164518070b554810070b64450703040340910300c1032040088000c0809818203d00500907200900800500384448140035895584a041030700c02903540401403005544d24120628014081407a03c80c0982c144100043d03251144051030b91003540c1d40322802c906c244c27800d0107860210076800411840c105058105070f00071803c0c030701c0c141c0d00c658059030f25080c210600510301030250760440b61301c6500e4200342c2d4841e40611501c881d45000c2c041043e00005910b4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 703211303 1250 703210053 703210063
    0x6010e0310060e0a1808090d0b090109030f02011526060f160215130507051c03030f20070302010204230108060f0907030f06030c0b0a02190506070f11 66
    0x41c244010004040d071500318200d4082d9030181120301054180500e402400854213920f000035030b0007400d170030740d2504c0c003000142e07001d050404014a038240354420000004819031100e81c546000307480d800320304040c401c4201d003280c1659007100101283c0e60f40a10071105078000502204144140781001c002c14010f20380e18201d401c50755524082c0d4558100111280c407190180c4814409000500c002100c6050160034a5402850b00c00d600e400d0707023004010710404000b080b0081c1000b500c201c4003107222242d4201104403c10058010904004107460380c1513a0b48503042c020298007011100b501007001d000641680403040640c00c41d9000e00001c075900d040c1c07002800840b518a10404091909180050240e46c0010110b6100d0822541402200c1c0c0720a400c90f50300031003e140001396076400308545c0005000301e4201500900c105100464a655000e00070098001e05800715103614401c01e03000d5100d40c41c0500c00a205400480120307500d01c1c01000500c03105507840c10081040d03031400108614003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 703212553 1250 703211303 703211323
    0x1e0f060f0203100b0703051602060706090809010306080f0303070c0c080607030218010e0904030305060d1502041703040654141e0102070e250c020d030806010e03 71
    0x100360700005103c02c524044031050024181500914144003941c6c070b01401c01e0080c5000c40024203a40da166004642d680d40841d140d01c1d41c808001c00c070350440d40c202542140c12090711180443e00d00360001c512280c000501c0144c0030800401503181d562001c100316040301c6490800c50f40418580b002046020003800680e00c280815a80140c42d500c40b9500300508912641c010f905100100305100455101c250b622507115405050110310b42d2a1800030031001c0d20b558002900001101c03c000460a850303400034011100a120451551042c0604a54030791050b8407403100840c50242c4400300e4080103002402001c5802c810412005500c0984419800d010b140004011812030a002e0201126070351003901070104030b500c0f01c0784881c0d4400460341c1801c00ca000d28842850700e07441d40c10143c0c805c01c002c1d00a03080402c50440d031414200c584c4081d5a10418602d01c405407807859884000d031080f2000d00b40320380c0041c225121401c4544007540e4010001d8116030402c9011022683d458800300071003005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 703213803 1250 703212553 703212581
    0x111f03050a0b01030903120b0f04020f0d061706010915120809030124230d051c050708030403081902160201020709052701020d060603061d041e0f06 65
    0x300e40740100340c840032601040c1d4920f0605151022403808a507101c0070340c030f0540680c0d100000d47d0b94445000200503402500000b6030060000444108491440025091101c0112800d00c5919100c8414417011076030028104d245500920041001902c0c94004002150922146014207521544040c960740030804041d031300100001040651401e09104c0c6070b40d007610040240040c6a8015032096020001c0d03c42c5c0b4000001c41e4140412000d444100690000303c02060810080350710701c1d05603102c0d4242076000d1200c0b1045a600720390503002e80221644591712190180c40c66480740d40a40c1e0070300c0064680f00d090310002c0040c0109500c076200030074100400c034041821a00e23462000a2034650581c2001c05e0803400d03e01400000445141d41501c1c4815110282040c00c0a40d81800c3c02406003940a10100c0d09000000892680680c042e4003a00d440c001ea0444000c1c4001c1c102c1101c02041c5e500400d60317280c0301110920482c120400140262003500252044940d640703070f56068071825541346803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 703215053 1250 703213803 703213811
    0x7060f051312090f05040b1c11130c020c010c031125051e091b12180109051005071403011e080a1a04061d0a0611070f111f03 55
    0x203102d03541d10ba901d00103026107001c80c6514180740941c000302019100b00d50007151141c058140d181c0c0c94450b0500d5500103c010403011032090304042740c00c116803030740d142d00641d201e912426400685008140b607000d000c0d0001c14030000070b4130046424a032003032026001c00181c0c0b21a054188800e024110380c92900085203000700d810074181b10300140440c2e0105200303044150f0f11003030510380040c401c81c6134107040396007100700c3c0c0e95a0b0b00c80300c0030451001c0c00004102d0018403000d84030800140c0b00c2c007480d110a404244401040c80741401ca440103407025009521078030300c0e044002d4003504442d0b03010701a454603048401040b00e807040180c10030307045003c00d41a00f4009814158406400c0001010a040203180c100a140c0302c1c101380c144140449600500402c001805000300754008803003400309089200c207005480c44110307485540c042c0046a030b090030322142c440e8018000d403e8402280e00080020740c104002d40d2200354803002c603254550000c4400c0d0010321294250401c408000d6101c0c0c8001c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 703216303 1250 703215053 703215091
    0x30415090308060906100e0d030e100f02101109040b040b040f05010e070504121220030a0e01210e0a0b090f0d03090803010b030604060308030a0c120612030507060f05 73
    0x809000c4c002c10355030040524141406089900c0410b101c42c680050390701050300c4549003000c440c0d03c2406520aa0000001c0344000d60403a0f01c0b000d00d01608a00c1c0d401d0312181003101040b10181c138944500a5070466061000c03812620b03282e8846504030340005c0001501040002c086030541d01c400011001307040d41c4400421600d0140c2050301d5000302d8a280262500d8103058601d00d4200d111100507010403080000e400d00140114000143c42101c41c0c022118200f8034043e8540e20341c8400794010010f546d0f076888c40284c5d400340400d0b6100d001c03100641e000e100c0b0038560b11402404648060301c9507220304c004007004603101614007030007540c007680076080390560400740340c1c039100b80d5880400c1014039000c50300c00400c034400c05481c1550064442303207982c3d4480c0c80000f0060121500041c0c046000001440700054071b540c0205a031400e00d0721085141c803039959a01c821644540b10b0f40c40c03020182484040007a21640007001501e10072180003030020340e4640300400f2a10304640c001540d800d031101c00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 703217553 1250 703216303 703216309
    0x120203060607061805100f0b0909120724020c0f010c09050f030c27010b030c0301060e06070b10061115010b07031e030f0b04180201050c031c0c030e0304030f030503041509030806 78
    0x601600e171416a041c00c14ad06110b80c0c0c85680b0030a0742100d522070384c0003159500030041400701c05200c030100c490310800700101c0e01c0d80030070080d448481c48a54071f108a2611242607031042c0941d40c50103105031500444689000103009900022801d101c0d418014442c3e0040c01e9030b40c09a4040d4a8031005403481d60b40304000ca4a100f40110603040340d201340406004015822840e0300440b81900c600c4d00d4660380f0410382c40080388090103132803001424880b0541c100401006d890545c18126241a0382c0e100e4103c42000e00d40f9180d24083d121071008502d4207005206014801c40100809480313482c1807095400380000c0030180f8401c0c804d4840009860b96454151076809000d40f900303081048070108100b200b8282d12645210340800000d060000200303034280c45c48018410343e400401501200d15080e241651100024034100c0d4017480800e1078012400c140d48030000664090740d50001066405540710384069070300b600020001ca035101550749890b034840b0802d0081d41e0380203100351501081c07410141d0030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 703218803 1250 703217553 703217561
    0x501090c0908070311060f070510151d0a0b150414040507110c0f011817060a06030305030f0c070804140f041509020d230403120203060607061805100f 66
    0x440c0c24240d0101d0f00610105000f140d1642d07400f403088940503030362030141c4241d116600a040c00a4a5401020f003824003580158002030080c4401030381d4100c1541d290f0140411400c500440e5800c3c11301c401d000250802c4496000300203070040100104000300c4000c40055003a03020341c00c18405082c0308000041c19007024040c107500400d0760b0410851207511142500d071f8603041061040c0c0f141c6801c8801c00403607401015504064440f1241c405a455214104005000704104251400c0d200721400100a1040c0d40320349801e8a60603030301ca030300c0e6444100b6144c0c103600010381007114050082051500080b0303060010001045184070745102c1c1096a400c01c090511903080d80e500035401c02805501c0e0060091002d02070350000803006844040540b8080000e100003a81c2c0088500130300b80312a1041114080548120320035038900703c415000050205c10f0f40000d8170b00540000040c052000040c005803c2225040600c01c444802e540458a900f85800500c0c50000440d994800595804038460b0003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 703220053 1250 703218803 703218809
    0x302060721050403030b1302040e18061b120109050901150605040b0a111002190c120806030a1b061808030a080c0415030f0b0f01091502030d0501090c09 67
    0x1070260005800e18100c00d882400d040e0000390140e40e07080000d003014001c0e4401022500054400c0440101000b00034009510502840f00a220034100184d5440017803e40980e403281c904000c3e00c05ca840e080d99440c64120741a2008480c00d034240140288600903203180c500a120b2424040b4040c10321007401d5007107400c2414480c500c3d6001c110107101c00360f0010308440448000411041c3e4a6a2240e0304403009007120b81005000c0c01150078500c603010301c680103403042d004e010807411403a07a41268181e64021030b8003c0140f0f0a48034451940c0c1c0c850090440039032150001e81910300f981c000ba50b0fa0141e0f840550402d451a07008403000b0f01a66a10040b4418003105c03d4040380d03802420f00c20580c1da039010340c0450404004440e4005040015010207071001013900e00140b40903c4010b14014025180a02054034070070700c0c001501c0d40303030714050084076200318060b19095800345c201880384c02c05164451050701948003c00001ca00c02e4803610070705000b42902e040c00103460702c6040c001001d032400d0b40c0c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 703221303 1250 703220053 703220057
    0x118110f0f07020423040b0a0e030705100506180604020a11031b100c05030f04170a0909050f040b0a0c0306051c05011b0210151d04050705031c030b12070f0303020607 73
    0x17805c191142048818203400c80d41101c400b40007a55a003078200701410740c200f0000c0e003d000200e040420130400040440c686448401c0030701041d0359820501c0801d111610007181c480214402040141c102a801002148921f1400c0380c800341403240907918503401809803081c000b2201001c4643c051b070a0000d064a40041e20041c0103d0134413100c020988c1c00090410b141c03950f031010200f01040502c04800300c8110400d60440d0b210041080041c0c4030410521503580207608290009140e03840e801c950314440c1d64000350304001ca488100600000b4100e1110310b109040d614000400c2d565110792034103100d0060010503100901540c034100342514110b0322a04600745000500140564011034500a60413505000184d007801c01e5400700c81075540c80d400b1040c0450141c00c0c60700b04094111000e81702c0e50284d41202c0c070b51540e92052643d0ba24810350446a00341c498000740307440300c0c440d401510709054020400f1074541544651241407074041d80c0203528105000c10304200b007603018007410758408194 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 703222553 1250 703221303 703221341
    0x1080703020c0a03081f0617061f12090c17120c070302150d0c110d0f1d040b03010606080610080106050d110d060f0f050303030118110f0f070204 64
    0x409007032543c1d500000401814084070703a00007082d4481c0c1100841550b604074030341c03a4055036108801b5113120f400503008250807444200180c103d080c00c1a0700c5580703100b908030300100885000022101e1050360200002a070352140441c0000c00c84604c90113002c0c01f001421811611000c01d000d07443c103036050b181d03080180801c0c050290711002c040340b400222078064800100c0445008101d011500c140c40e130311860701d89010001e202860340a03070100d9000581404441441c150010140c40c5403e1a018400000b01c0b0310f2003c0440c440c60440041c03000030003600201d038444400000900751107194008100040c480b030200b082d01d150001d180c000f4000c003410001c00030350400b03400900c14440c3c62206a40342d0303115000c400742c0c552031000b2034428550040f81040500c1c2c0720020307510480075a220790051a2900c0d000842c0900c2c003c42168100c41c08000d403244010522903000010700241100c000f441c00c01030240302c651043c2c610061500c128007441259551449104010807507262041c042070076254 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 703223803 1250 703222553 703222567
    0x30c08090a020f031501030b0f07110c3a0615060804021c0506040c06090b0a0516060207120908060109020f030a24090f0c020a0302030a051303140604020108070302 72
    0xc0410401c0a49405a600c011180d421902080c50504204182c02c0c0c00d00d00783d0000800c5c4100309083d180507906450611500d62201c0404440000d101c5220207001c2c1c0100c07010312141c0ca030030b02540b4a03001c007a1001e09082400b101c0701000d1501200000718100748100104000c100781031054030324036940c01a0030040c0e5410003000424541005200034060003456604003010a082c1c000104040d62280480f13007a0701e400d10f0000076121552060f500461482c036004240a10031200361000e860442c0d9480d81081c88040041d074401e51014025a0303019802c11030346012640307030010500d85155544031403420b20b00d0440440c0c90305d40141d1281d110307284144406041a11024200d0780c20800f074100103d00c442d14012078036220320408d030ba041450f2400c04400074041d10766410031001300004c20700400074418561030607600c41e20350308401030041c1c0040008220301c50090018120407240364001d40090341d100e81d03486001d0512515030040c0c95119504000440d03900ca0002503101b110b62038150308004c8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 703225053 1250 703223803 703223821
    0x8010c0e04180b07050304030c06061706090f0a08030a2a0e0a0f18110d1a030f07150e030a060e010b0f0a09020c10150501080c030702060103120516030f030c08 70
    0x180104c0c041020000125060602c41e882c1303203201d07070f410a01c02c201c076981e80e1034403400c41400c1c0745490070980909400651001804180100c1c000e1020014103d80340c9959251102c641c4000c0280c0441c0ea03407403100c4400c010806010100020389d10841040310b0580300c00140155040d6071141d0b11804071400248440007004660904640309442030340905c01c14482650b015054a50018000000119500c405902d0319003188500000142e026100b5250802c05c0c0358030307010450032a10040d400148104180c82d421500940c00841c4c03071410008400000c0002420a00020001d0b1400b0351100e00200b003851b0280b08a0b4040300d01107074420301d500c00f0080802d52452681c4582038417154042203c1d54030950a10040e5004400c04a041212080303e4181054200e054003c45000a68040000f002507913944c046078060310468004003026865540d4840391401d40302055400c00ca014880c841b01010742607080395505200751101501e9010080004040710034940c08041000141001d0009600c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 703226303 1250 703225053 703225073
    0x1050a14090d0e010806040906050411190f0302090712140f07030b010f0509060c031204050c09090307080a090b0316030c02071208070309031703191e1508010c0e0418 73
    0x80c000c0c04d091141d40d540c08001001051198002703401c1e2802c010801c003c0140340044801c4141382114081200701094890407901c5280d4051480b51445a01050000d4a0810a000d52003151452724507150408202d1240540c1c142c5598400d40e070754250144041400440d201991210451808026070104100001d00c80d0480d00d0709071040c000001740d000b2041c3c0720b0100b1100c401840800300c941e201450802003400c501c00311400d0b2003034000c418100d840762030203056690251440344025420309100c2d8548040981c0454510014440d00950001d41109844040c51041445a40f070b13808500700b900014044d602165a00d00854005107414401c001f105542c4505198100e19240e403150181e103015100003105400140c402040203444586003030006000718410203130400590349024a12481a054a0f0400100c1c0b2404031503a0420000d44103030350002c1100c107101d00c48601e40d42e070703140099070031101d401d1003120000e040b0f0700c40e81e012814103014220450181544088030041c1541300d245441e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 703227553 1250 703226303 703226327
    0x9030c240720041b08041430161502160b04020a0501031e020d06050d080c0c010504030b01050d050a141605060304023007090501030b06011707030e0a0501050a14090d 73
    0xb0259480102c6c05000700c00d50150351421420040b108a000f4514400403144c814814040c0902e21141c0c4102403507034100151400855154031032030100b900c9984141024460186504100390b00f4403500700c9021242c0080400c0718040c1c9180a520304090044c842c0020642d00700c2818581010001200d000c0d00082c25410a2803014006850301ca5480c410009003040741c0c0040c1c2c2c00810030035034200f40301c1c1200090410721502e00445680c00800300c010b4500c5c0c003643c8405040400e00f01c004000505100c40c000c5480d9124009464036130f4107907a203000301134101d905901204d9218214100d520b021074090303500a4441150aa400c0d45450b6000504c00b00c6401c150740c1d00e4a07100481400740e8103c009148081d140004291a0600c1c0c40711600c1d03008050905c41640c01e40a039101185565000c3c0414200c40c15420f00300128541e03650300e00364003a201c074030003050085c41f0f080c0100011134000e100301805004201008640c202c21080820150356000d004141c1c4c94101c83e8002da0070a030440c14130456 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 703228803 1250 703227553 703227557
    0x5120603060411041107021009150e22090b0c030105040f060b0706020c07081917180f031005010815010503030a020a0204050c0405040c080702011109030c240720041b 73
    0x480b10140310025071031b0080c1b0388001c1d004120104103426040d000036001040c0c440300740308841322540c441d00807940040c06c84401600300002d20042d170001199108490401c0826101c0030451138515a0348003241c0344100c0b0354031000b00011005124501d0300c0d02074480c1c00e4840300707424000281485201c08185c1305032040100f003160b00080c440005802400f8400c024000e5206803041ca1201c12040358086000040440b070030420300601c224860300c51010f40e6001c06101d031201800e0700608082c000c1e08030040c01c0b07035549441480a500da0103015070140c180a804540c2c058003100858401c442c4003a00e045c0c000e103100c4d8100740090500c0300da000a5040006804135030210f055180c880d221000391099800281d009400d00c1c080140b4aa0801c8201c0d0149540d6130007004140ca44500100d101d00442688a41c036070045081102d00c3e161050044046032625102c42030740903c038090010940c3d0105500322540c0144603d03503107076580301d0010742990300420780e001c0c40b01001502c0414051541e520800007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 703230053 1250 703228803 703228811
    0xd290f0604032001270b09190602060f06300c1e09070309031d01050f0a0305040c060806030a0605060a081504060b04021801031a330703050a0c0303090c060512060306041104 76
    0xa803551902c210540000808c50f40912003134075000b0094640e00304850840c1d800d09200003003601420005004900c1d05600c250000e0f6000b00e0008085d2213500355100c814a501c1034a001c1e90040e6100003180d003a079603d854031076040c40c0d8190244110701c0c4008020381b09062070580b280011030b40001c099480b80758041da0403060303001e4030401030700c490042d843c2c6014021400300350f04c44004e42540c44140654010240c003030b0f02030350b100d9040721941d208450003a011b8100030180300018180e6000b003500600c00034000c1c01c0d225106c0c2c0d902c0d4075007801c0090003008890300074103000510895114040300c3c600c050b60198a0017080f140190004c03004201420b04160b500c00b81031803d009a00303c0e1068244004100d500e0746504651300380c4201f2441c0942c0a500c405a500302194851540126012182d060b00e640d400c0c140d80d90320589500e2080740c410340034541c44007000400958150381c040080c2c80c603602d600d03031600401b000e51003011200805290007588910144804107a0f081d00d842c2c001201118045 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 703231303 1250 703230053 703230067
    0x321501051f03020408010612140105092a120d091406040312022b0f020a020d020d081c050f01121a060612010b0d290f0604032001270b 59
    0x81c0244141c0e03105c0c02c0c240d40303004030108920041e5449600d80364041d18400c3e440c2c4030031a10706400c030742c810745000c41c584c3d02405040c3c1c000c181d1140760140e4094a11000c188a120480100e140c0da40c80904c5026a604040c101100c0503400400b1080604043c2e09034964151380380000c10201c0c03056020151521101d2032a800c1114401c006184007007070548460403001500c1b8251750040c40f03d250381000030032000158104903910000d10a41c416130020840305208480760203001c030908103200c2c1600e0300202001b0011f50380b0000c2c580444035982c4424000792500e40002c00401c0c032507060b0001b90080c0388240059020421001c2101c0d0f010b4403d48071000182c407024005600c43c46844020b00c100104c1000000c0c00741100005001808010601884111080d100c40200501c4050070544200b02c030301300c0721129051182f80c0141c1010081c0c00b451038a5280e807188184090030403c43c1a103161240340344800d47d6400610b0311400014054141900c45482012004034802c5009006980340049407034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 703232553 1250 703231303 703231307
    0x7030314070c2409060c0c091a060a0c06150825090c02060103050111030402090c07020d0209011e0e07050429120711030901050a0c321501051f 63
    0x40001000b545059914540401040640054608220f240801e0503041c001440318096a600814503034820f0001c00d041e030034111000004c0483c00882c9204100d00e0075122607544818000b45410a000e4440960744840741c030300301040da0384e08108400c03c004110310411502d4000070702402044d801c9180b11180c026681e0080b0030a00c07050784110201c074104403482c4095500442d695060702d01a400a108220840d0b10f00402840152002904140c612000ae6400c5000c1c9000d0b00361a8401804103403840d600703800103003000a00b81c00100c070b04515007c0006007000d1941c040c4008004a5000d42c6c00ea18181101802c0ca0085109075100010710001403000c1c142d000d45d4151600791081040c644800ca1070a00030070340603003101c0c4a00400c0c64201d0918116900000f035550a440c16034885140c18000036044980350822007080f9001c03804407402000f014907075500303965014002140c0000504e00701d28414948034141c5001032018004030010f1080792102502d0050081040c540c07a910501d040c101 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 703233803 1250 703232553 703232573
    0x1401181b0c150b0a0906030b130c0605210a020c0d1106180c04020c010e2407050a1209050303090d09030b0408070c091109040b0105030601170a0e1f06080703031407 72
    0x5540c050100313500441c0c1c50304941d002800303903801500b010b09140e549480c8c03911001e4030721130301610920203e1420040980304100400041c601001c55442e2000da00140782d04940e400d8440c0d041083e004940150740440401054421f0800d030324182c101800304041e12900c40c0c0e4013501e0181d9841840b0106d6a1120041204102ea10742c0a4821907891003407180c11402040200300c006a540540044040e010400d0314074105c040c801480e03003400c40d45403860192196400320365442d003802864041910502c440b03201e00640d003802400519039030301c0d000e1340c0307107041c40140400341c0d00b40504241c09001085d10041d89070362080d40041859a240014280170101c0c06999001407045070900c0750802c05490042d014040e010300555050250203025801504c1602003103c0380c0c2d00060100121a00000404000e96008a1003000008420030036802e054184121581ca00c0c550410300300440728040c000784a150020320b80c2c02c014015903411a87c0c000c101014240c010705803080013181000030b02480080d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 703235053 1250 703233803 703233821
    0x4030e120312040f020a0602030c060123040c0f0e040e0a0f060b060318060a050408120a06090c03050423030706050a0204050a030b0f0c04120f05011401181b0c15 71
    0x44000003d1a0a2802c40c0e51190241000c0340218880d56002030308a0000003951451525140030f8140d507070804040119100c40501c0300240b90001e03244030070450310707280714038007498099035999540e25a1498007e840c07d919042700c103002d203252403580c08400c1000301e98403041e00d6120000604500707035400c0140c060304920f50103d51180001042c024640c1c1c40b40e000310080d49801c1c0c103036125070b603440165000315441107401074a8081c08100380d11800c00c0c500000e5a2016102c0c500141c65070325880351070b0881e1540d12084021035680c000b4801406006048030410803014841c0302410484c505060391603006445006100949032400709a0b102e8507901954060709001d0070f4062260381e61305011078429000d40340540c4512861000c607155030fa40030210f5084c1c80e01c81d0921a892000d60781c900e00819038075281031310fa0355a1800c0d20740d40d1010f034500c014001c1001c9404001102402900c0504407a00043c4c0c140040601c43c584056490300001c00402c5542c0020005011106d1000c003040500241d02c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 703236303 1250 703235053 703235077
    0xb150d02030c12011d150604050f0a0e010801020904050603010e070e0a06090504030504051903032708011104080708010e1509011409010f0c0c0c0b07050f01181401020304030e1203 79
    0x40f00108084400488140581c0251000420175440b414503141001030360302c08844d0011000c0005111038181004182038402002d020901101d40d5480701d550907820a030000300803a5000200705c03429242c107001c2e82d50403036402c5000704000c81ea80c69800750360360010702c1803c40300c0c00b0300b200140d080d000b698001d80080140240034007051500b803500400e00c4d40503000d150b2041030495045c03058081c408502c40282d030f0345501d91080300110604400c120b04500321106c80e440303041c2c4070046001032003070080560500702c5403003050316281000503a50800b06160415850340e8982400364241c000001000c0e0b6141144000c107036a142ca03050f481601604065443e5014003412500f40241242c0c15400200b04000384034041011001e1010110b90680100a0207012066035010501c06000c8480040041501c2401118554190790320803509498040300c140c103c03c3c2803e038100050003414840111708424031402103103180340540d00a045105031440140c041d400703100d40c2c9489103030101f0407280e46080384 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 703237410 1107 703236303 703236337
    0x406140306090a020d0b0604080109211d010903142d0c0628090612020f03190e0a0b060a05100f08040f020a030311010b150d02030c 58
    0x120081103100e6a40312100543ca96404005000400400002242c45c0c8070506080034000c424800518001030804913541ccc2140d030002c000c10302c071503506d440b104284840c9001264110031a0708000c042c8034440040b0000d450000900c04800306000b5136002d0340001c0002011000003e20302280071030780c01440641c04900c6c100025000c070840c01a0841caa5001902080074100004041c0201080d031050701841074551080010f521542c11900a602d40082c00c03401008034440208080c2c0c1e615100050028031503a581c01c00c082030070f0b41c1811a45200000c3c01e00b0080c440c3c0030b0340c9040c41842b2424000801e8242034207010395a000d59185c1d61f6854032031340d20640d01c61100810407202c800000040c0001070740d5604903240618083d035550103030380e041ca103141801c4800980e0110320500100510a040300c0c13188084500e11410440c1c09a1251208803944e902401039030128481d540c44 = true := by decide +kernel

theorem cover : BRFrame.Cov 703057553 703237410 := by
  have h0 := BRFrame.cov_init 703057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 703057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 703057553 ≤ n) (h2 : n < 703237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
