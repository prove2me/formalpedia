-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4302
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:10:34.256594+00:00
-- url     : https://prove2.me/submissions/1cb42a54-cc99-4095-94ac-e52db2c37d7a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 773561151 ≤ n < 773741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 773562401 1250 773561151 773561153
    0x105090a2403030309020a14100e1f020a02010f021c030209040f061206051614090d020909031b0c10120e010203040b19290a0b070b0403021507090e04 66
    0x58901c0307010590301c004032042162241030140180a1001d0708a010b030321003450000d028030100402c0070611034000c10b030100c68404100c0484005581c3e1405507031000650744600c000b0220761140c158008000e4007c0d1900000500002d060315069040ca1415900103408100d108402d42c4001c40b583c50203800c005884035540c1c0017050050000011144030907141c1800811100e200c0a16000e180d0b100d00c609000640c1ea000b0240c0c0c414040040040c0070500c04113900c0c0030040e0302400b0704030300040500802c10005d180d40018841c6182910380d00007075040003840c00c44290307086490814040c100401081c20b4480080412024061011395408100d031400288020100c180c010010030304c044802951282400d0514060b488000d9402c07002180e08031503250b507006050702641d0b11004e07185c69840828814105a25014645110701503840789030017202003614607802c0003030001a4000c202c00c0c0481d160616010b480c2450310705070000401501010401110760101d0030905440d0812852200d036151 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 773563651 1250 773562401 773562431
    0x50c0f01050a1d030601030b010f2709060905070f051201151e09050106020c0f0306072a020627030604110607080f0a030f0b0402070f110d140d030c080105090a 70
    0xca00e12050b1305001c4d4900000a202510122074183c0d9400c03400f03003d605c0e544040e0550004500c0325000914070403460240010b05480d40b1a07e04180207040c0851504259a6820700304240350300003165440e02c1c10300a02c042d08040a1010304510a94020000f0034903040030749058403007a104140901c04403035500441140d07074400d62001040201421b00c8656180d0700040e4445d10444580383c020131681a104403e0710700054107c0c05800651900f10401200b42d8082130401c881503417400c2184004008000140c40d100020100c0c81041d4105000c1030842040294a030f5108101d103e10070b500220134480800c10301ca40c0d40095000481e94035039164081e141440f100c1c02401028425180081070002d040c3e50542c12008103211710301002c0101100704800c20049029154024018025840e109400500c12420101d55407000401c00c079400c40450707a079904443d040c01c3e8110000d400c108900c110540d014015000058414184145598180700119902140050400542d5500c5088a01e11601 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 773564901 1250 773563651 773563697
    0x1505061e16140106060f0f120903020f030a020c1f080c09030106051203090405070318060e070e010b040914060108160c050303070c0b01140a03030f03060504090c03050c0f01050a 78
    0x640100400c0300c0c5070110400b14000c011070f105110206907654207040d8a00d10403a018029240940c861001a45e04805880010004608210194070071078240d0410888100003801c02c000c0554000d0400205010501091a5030300c801680c00c20b421a500b0076000343c01904041c1c6c0144000c0f82183c03511010340000b0702500d00381d44005d4005400f5015a420841b000c40284424a0240c1c1c0602c52501d0701e800031401c80340a4541c00004003022502100040c3c1c031500300b2032205235010704554809032608001c3c3c02e00d810a9100003942c440c0050200010b0103c2d015480f80c0102d0004851807614048001a1102e00700034030150100706401d0b0258025030041c1141c1a5841d00102102d0700c07403810b040c0103420030701503c8040d500b50110030000240d0244020310140c9a100191003215814a11b9809030303021410f0310340000c2070589900340440d0b15280c91089014490180f8800034020703141d410010705040c1e0501c6101d029840c100c2c1800d4150360000c048481c01c0306903240144502d5007621402d00054 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 773566151 1250 773564901 773564903
    0xc030f21031302041503022d120319030e071703030606030c1603020f07080c060f0a112a010512160c0f060f0501080607021c0e04020d1505061e16 64
    0x40c9040802c46030060443d40e079030240d1f80300740d5500d6485004041080355940c1c0038000c050303518000340110110f504054506181001d108030890303090906441901c9100307500300342410f000a07a030307451990086804001c440700510303068007502200b1212050054807840300170044c0b406031703600002054409010304111040300746549440d5441c01c01c40c4c9002915160916401e074000d210310000426403090114038a00104001442c5e24503001201c1c00804280e0031400b84038051101c05041c2540f258000e1100005810803404805403412030504080f4401041403c0300381044401d01c9444040b4001400c00c0b9000101c8202c0705140100b030b59012601003810150050511040082180420500740c02512003128064820310040c2e0301e03881416600c0500b00d03030034030040e0b000003800848030060030311800010710300d860894803901c84c4e00c0200342a81d015182c452241560707541c280c00c0401c54146002c028201c00c42d140c6c0d2400421403110503501c203913884182020790001a060b190700018803000c10700c071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 773567401 1250 773566151 773566159
    0x7111e0405130201090f050109090b030309280e06220e1213080a051002071e1b08190b0a0f11120a02030402010903030c170c0c030f21031302 62
    0x585880c0820b11503800c010032003203000c01c81e02071011070072003402030240040c0e07541a5a14038925140c50224005001400ca1154150004110010083c1c44085124520510200e09060000c00d400c81d040031902d52a4403005540380b0000a0189036030315021045000342e0b008485030042d051a5950710300070328041242c0d048922442c400042940c002602810840d80c01c61030f800701490343d0700c0425031070b8200c0340801441500000820419a10903074041c1000d85c0c020341c0822990075015501015031902c2c80700981d0307030100c001b080740103089a0500d0310011b8081140a4007280c4041c6510044421105200900031590b410000d10a10300c1a0701c0265011413644080c440d08440344003044059010643d40301000582074001840c0d22200d0085a000d56410b0b5500030101c0d145440c11240103054040c12149108100300d0f6003031909590014081c200842ca01034000c005500080628090302d00d001da03401c0c1d0700b090380200a038280d9007180242e81241c0c0421159683d441e44103401203040031070802548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 773568651 1250 773567401 773567411
    0x10806041512020301060b0304020603280204060302030a0e0c030d030e0c0604030c1503020703080f0702030705060f01062616050c070f060f1821020603090c0306070507111e04 77
    0x658181011242e00c00c0d4000e600800c401d0f901e501140c5c000e4401282d02a4000da000c00c0444c008070907100c035101c0d40d40500203440500841e1020b0f00c0040e03034400c1c0d00010000350003005012402c80144207580901f846607008110243c08800800d4031109606804000d050b81c8603040d0070a00028007107040b507164010000c941d902e8891070000d4100c019070042c04011004004404000790013031089a0380981c042d00c5000403540c460410402d0505d0042407801107020510082e4001780041040c1030082040201c1a080b030760500e440100148204100c40f20000c48850801d0844842d401405400142d4001c0f1007036484100b03181940c25101c0c4408501e103e11946a0000d0311090b080c00c0720042c0d404a540d0080017a804200444400e1102407100081e40d544840420698600051407014096584400c0d2400030240e00050701079041144c40c4481500004c950f104289010f100c0b4aa0002081c140503003080c2d10703500e84540c8601d07075041c00e0740115200a00100040c036005281145024000d00500c1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 773569901 1250 773568651 773568659
    0x21002010f09050a12020f070b070f02030123060301113a0e10110a270f030b06100f0e03071203020309030115050127030b07051c020301050904020108060415 69
    0x40e840c04c0c41c9009840c0c1c4c080c0920a81c000f148081841c1d135181540d10f000341007145c2401c1508150383d1220004071000202d8030040f40041c1c40038000ca019000800b40c04c03021000c085001200c0e24200106031034401c0e40f52298181c91140b004064520a4424902c0d151414801c400c240c1c41108894141c4031410050f800c0c0030002d2000390300301400801c00f09099407107070410350f01e4140584607008032129901c1d01c01d11050b9105842055144054100c008a04001e400d10714410707001e00c8803e400c41c0c980b000c1030a1040c018000c03600e1250b0f800041c20340e92004d0321452044000c1007058003500c040100108041c2504a541d41080618050b040c580702449040c80fa0f0300d030107941e1364840b4201e18065400c19030b5a070700303081103007612404542060312624040c40c002c4c01b08000300c25040003001e2444510450100c0490016900140300300210346603287d03242c20310000a4065420b0352035095070035004000501250300c07910702c010b41050f420701b0a0200d903264400020007074800e507041840d844e240100009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 773571151 1250 773569901 773569903
    0xb01051b070e0c2101030f1203110c03040303180b160f20031506100e03160f030b100807051302160c060f080f07050304050f0d050307080105040c0c021002010f0905 72
    0x1000048130607180302040b00355414078524504013488060440e900245d806008265000342000007603065140c00504090314449071103454009010030034081c1d02c042424005c15801030306909402c1401d00c00411600e10300004c000300d07842284502c40a4040d604144010048005000000b069120341c07656218107070a5940784401d51082651840380c0301e0694484411400c00400c07500414001d44011a800c1c0441020340748680303c0c0c0c3d52541c140c800d5040d10076104c00e8043d10040600706d400d507011082451801d10100900d4050490540030305100b0081000759000600310007113a500f541e10140296410761113038004d00400a040c182d10103060b5240301000904801071050340d81c02d4803070a19103240ba02046800c0c400403907298401c21840d001050308240204055503000d07218500325048412a002441d00b405124201d40d00401d03008021701102d507400c204400d01610040c2c034100241031003441c00030310001d030107400a8020b80540e40c040800310b100303400c00011811040d50a11140146240c22 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 773572401 1250 773571151 773571157
    0x315020306180708271f060506030129091207030201031112180c0303040f050f1e090402010e0d0807150516051c051311040b01051b070e0c 61
    0x1a11800504126101150841c03039803c3c050405560394200c0c680c0c0b40060510a541e6500d142c0d141500a8100d0804042c41000303405048844000039040c001482e00c1e1190940d11603400a92065400380014085c0d5aa990890024000700d41e0100c102c0e40c3d03814140d83c43e0b0348142121541c114a210120308a010000942d51702203d1003a0f8080248511a400e11425400b90b00700500000f802c05001c81d2801c40c06035000c407048021031041c0ca09076080440081c0c61544035522041661041e54010841d40c500161070080f41c0406a619034000e51241d03980c07119103014000c00b103108100b03000c0031805691044600e8a00200080d00d40810005181031002450300032040869040c0200c00c0402c0010403540600d90044450104c0710040d491f030301d10141c800350400800c02c004210160300110103441d841c080d00e401172a18050180e2244020700f44000c1104d10032100c1f901660501d22015504d9030f201c4201d424020a20300140384003101e2000702c07810300ea204d6100400c0e0120040070b001c0e41407416002 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 773573651 1250 773572401 773572411
    0x602030705070b090d06020c0705040c080106030b0a0f270c030e1b061617070b191e0f0608030307020d09170601030803090115080c0a09050609040609020a03150203 72
    0x1c42c0c2d050741e0b55080c0319000303100c0c1520381c039008503c600c070000000303965401500c2c0000c440011f990f0101d0300c8502040031100c3c2c0810035000954400c0040013440c0c2c0500c030b1000b50006c01c2d14072140c004d04080d140c2d030307040700181b040940401a4901250700141c0c00900c032145c0400d0300c00d083c090504041401800b401c1c840e22a0b148902540c1c0707520118000c0411400d00703015014046c0b038203118541401c02e800c1480c21400303807840101d60580d2009503203c200241000d0388500b0600103241852404081c1d040442c1c017110404504d411030034400c814400303c403200ba1110f00f03100030030071a80c80e1020b000501801c0c1e22880f6036100100c14801c0b02900840d4000d0214190703550020704503a82c864001c01c4002c3d80c912510076400200c0148082141c5c540116445603411002103200b2441243c4100520250340c40350341d240c1c01c20f4580561914002a050000781042c2000f40f00500340381c400150a14006070004140b1503440c0d6206c2d007191602007120004542100e6002d001c0030380c502a1801a50007110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 773574901 1250 773573651 773573653
    0x8070c0303090c0f18051603050915100f08010236090a060608061503010b18100c201e0d2001030c0c03020a020d080d18050609060412080c12010602030705 68
    0x9007217501594244940c612402085000c40c0c01c801029078103400030000501a0440d5015004201450010a031401d5018005144590094515040c400500512103030441743d80307640100145d540f00c025451038130b410710550030503550542c41030741c5a40c803242d002240110340219003101008a40034050b070004003152000d17110510340347e0703a410400442400340c20502e02070310004e00050044040d0308024140001c0d483d0843c14441d0070b61000100603407104015000003d40d00008a010001030041d40d0b10030703603450701c001881e0400c007100080d9401c01c640c1c00062110703195031440083e6640c0098401d001d80d084104030142a031304808542c0380740c4071000424046820700380200c03400b600c20841188960f8040c4c1c00b60169010b69800c100c0c004c040100244ca2a030418080310041d84428800e02c0300785801c100301c17500f00040603d03100c0d007441d000034002c0078250005400c00c4080fa90610819107030800c0c1c4d150441d416519180640303114080e00703180f500c1c208840340000c0f13045a0004001d000084c0504 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 773576151 1250 773574901 773574929
    0x1051c0b0606041203111605090708100308070b07090e10051e0901060815030607080c0d0e03040807051f0203040e07090806100e0a0b011d03030c1005040b0a060608070c0303090c0f 79
    0x1a1200d0f00c0007c4911406410032615000681014031580f60f00b07400c80485d01025241039603a803100111500300c24070a0f20300214040c04c0c0110150082c2c03207038004000050400c00300e49803103024072050100e00c1c4144c41c0681c1041c440c0000c44a643c912094001d9001000d03003125507110307040204546401c1f44c5840c1211080e0801603428030700041c01d41e204030003541d2904c02c5035865240c14150b42c1c00141000e21459140d03507041102e41410710107400503215503002030044e90301d0603041058103461280d501d104030030156400a04550302200300c4058403e0501042015281c1200480c0c400d116980f085411740900001c0c0312000c1145002d110494040320f2034441142c032103610f46400c0341c481c000c026001c6030203034040021480440c0c07440000b00100800356410641100c440e1800c000901c2924202c465441040100708a011203050790089184007081041a040485c06810b014018002c0020301040f50681002c0501c41d4205009840c3e20400c05984650f49071141c2078014090702804298030500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 773577401 1250 773576151 773576173
    0x903080c03041511070f050f070b04150507030c05030c01050a0c030e0a0b13050f0c1816080c0403060e0c09060111030f03330901051c0b060604120311 66
    0x264081e60702854110750031400c040c030b403001c0c0c2000524503e4074910351044144a00b0002c15011302c2400703100d50180002d0403800c5001e500c0c036428507800f600044241ca1061000388400b01d0100382d04107003661070b400c0543ea01e02c5a411306494424070884003c2082c480062f080309600019003001e8001c1c4030300a014402629450415400da07030140140c030030f0720351100751000c000c50070880301d06400c2403000e2900d035650000c0741c507141d04041e2101c195090321380c4005180b0150303003011100800301030500742c42405241000051040200d1212a20804200304080403e071a18004001c40340111351143d4100300840e44507100e42c2c0c80e6400791003017900c2181d54000181c165402141c0c500d10320700340c0d4809545800c1c90804045001d0b00080e0500700008004409043c0a03540c1d00548142002d400c06031556030907104040082840301600800c0c010013544482c2d41d41c2e002500f5001d4012070b800100c0000039070b0341502040003401103520440f00a400301c4081c0e0181a00310000d00d0913410101e056070140d0402c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 773578651 1250 773577401 773577421
    0x3050c010f030b0906010e01112b0906050a0c03030212152d090a060e010611070906230f0a0909020a0504050f0718080a060e010c080405031e0409060306090308 70
    0xf07001161a0403a0b42c580002d2299840f444421040c401d0504000c0d010b00020b107080e502d00f03140c0000f1440c9140400440495447c0030800404180010749003d80c072250400394000c2103401106448e8092014022401c0c04044c080d8066640a910b0300001d2440c1e4a000c07240b00e440e00000e01032842c002c41c50808010f506400c807030400d4003a03210700400c8200504583c001d0240100c0000e1130780f404a42c0d5180d012640f4105264018000d100c640d0714504180d00340b1401c80d090400a501403c0f1844c9440010003101500c0c0801c0702030040d0802030103003040000e20104840c000f80e070f0681648244010310100e46d00c0c0079684481070050007510300e089140d41381c0061000f212815100f01c815070101e41c4c000b818441c880c040e500705a880c9080741490803640c42000d649048030107071007200d07403986850510b14150024420f900070303415141740a8129090507140c00340c50344209001d4088074541014810501e080110840b802003100581c03c1241c0365070b0b818604d004001144080313001419444c040747c0c0d030482c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 773579901 1250 773578651 773578661
    0x608130b06150c0f0f0d0e1e0d05010c0203030a060609030507120203120309010b09130c0b210c0c15010b04153506010908030d05100b0403050c010f03 66
    0x3038450104602900c403035040041503034066262000418080000d5030340c0d035906004041400c00c0702c0c401810070f0f8070400301e050300344400504a04100001202c815402e40c0d1440c030a58030410038001d10700944122100407a98410008d00c018200358282006014140c0c2e0000c015481091b0441c4100189900d40300100c8d17140d07a851001402c60790000ba41404083c02d000b10000c1c140d44000d0403a041c040fa2424201c3c1c0f540c0048584040d542d54810310701420342803021140d6800ba4840912440030b42c155070326030804502c14040c0700404200401c51075402e08030800d803140c1042e107009040c5043d1a0000080405a001d940c2e5050140650f207054000d01c1d9100340d0b018160780f06c103840d5504241c10075a0b03c802c0f030440c80300c010307081045542103c4801e41c281c008015071000c01c4c01d8095240c646801b8080035211000e040c0701d0400c018603808008542c4003000340d50510074612000b055584490b80d00180f685040e400440c450f00000070000100440010350000c103c0d001e0300c54840e0200c14941c1030741154 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 773581151 1250 773579901 773579903
    0x3040c08060603070612022508041d0105090f0402032802130227030111040303081b0f0d180507060503010602011103041509151107030e0415030b090708010510060813 73
    0xb4500340100700e068003047e00606101810750f071f14805080d0b80d07900c0035403e0b005040030a541c1510002000e12405d0015035005642c800200412030f101d51500001c01c0022100800807480d18805d603000c18119501803250300c04040c10b020f40386003030b107000c21030006a40904c40422880741e003a4060b404144410741c0242c0701d0118405540d020b000011510703940c1002c12821005515558845464200d500000040e01c05075009541c0d40407245400c80350390340c0440c0280c2040590340800d01000740311004000454480c61a6640c010400c0c14401c8180d008400c3c801100500d54041c130724022940640c0100654103c0707490743e0003405495450f0301845014427050358040c22080c0c003242c000d83e680809030001403449105440816003075000041c500100c46120070400485180001c52105155000450700c8aa2400321410017884181490001c080a031900c8014122240c5c0400036603160002d0102c40c00a02200c40240520b240601c2101c041c00e409000b694085400a00440e90601403801308011003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 773582401 1250 773581151 773581157
    0x3090108060306011406030a150e0601030b03120d02160203010c050703091202030c09041511210c03010509040c031b050a0e060d20060403060501030201171302010c030e0603040c080606030706 84
    0x9000c5c00d001c0b840c3e0000703040c900050f0311090320492800400c84100c00410f1300340010030060400100040684041c0b2810501c60740c8098201242d810800d8101c4001c070525001c0143c0e50490000c03644039100d00010080c0d81546080040d804994100e0004c0216600c00d40d00d0740c0a2a4460b520034407443d508600103500340d0b000920030481410324814158019010f042c102c44441010102203046c0d0340224006106918040751300401e03c40820841c50f00034a000c40e09070020701e800e0b01d00818a0205105076482405c0070b401207000e00c501040510091504000b040c031101e60312303503154281c00f080d92041d64020a9020000a1110750801d850343c001c02d8020b044400311500c0d0f031a69440540c400086480f1911440194151075507000003c02c021485084041070961540c0005010401515000e06070905034034108480f10b0b141e800345400c85542400c05010320207030b5040403145003c0300030310759410003000000d00060000b101d08810031517214501315422503640e40245a00c0c2e04151150b6004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 773583651 1250 773582401 773582429
    0xa15020307080f0720031006050919200408060a0c020c0108091f1d0601050612040c0308030a0b0a08010c05090d1509080c01060603060b1c0902120309010806030601 72
    0x80445005240c080d80a0300001d003401500e44805e819000f10340c0c44040c04100101050080b0b00302406010b400c10800780b4100b081b07520348808113072080c40040038050103806081031700010f50360035030000f80d840308013031400b1503103024500b030303042c0c0d80c0d40203019121035841100d0002c2e46034445070048030a4070392558007601209141710015212210003420052141c0a00305c000d00350011303600380c808100007000c607000c64074803203d8015502813165940d1058864101d50014002622480200d0b4044004104040041e035039608004c90110301070342005064600002c01d00c025180503410440380510111011002c80b907980d41010b080302c0421200c0f5011034000c9c0040111071500c004451503c07400b6080200c11244903101c030404454031802c0840b00b060001c03641e00441c040c248a5180038025038102041290b007080f00000440c002c0c0c60091004040c9403030400d00703005090300400040340e40174140c03080281101c003290380c80b90004c01c01540014815000640c40e0301e8000b03044e90481d01c0780045848 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 773584901 1250 773583651 773583653
    0x807032d02010c06090611072006090d1505010f03140a0b01091d030a020708190308241302030106030b1503010b090303130801060302090a02070b2d0103110a15020307 73
    0x11482c40f14070041d40c000d0fa407120070501207821800b500c81450b0078006800c0c1e9a09440c9450040191100702c8032000752510754001c480b82d2a1602140c02c1060101e40340f01080e5039902d02000070550340c3e26008003441c1802c000082200d0114041400d40b03101e0950300c1c400c2c00203502016500d00520b0006494610b20000410a0f0f8000c0d5014080f8054078070201c045580c8040909844c0d503200f030400744016400802d0030000c000e03051107540c80181c24040c14860b07010311501e00400740303100546048030340308502d080100848003140c10503185020192040d81c00501c0181420000e4009110707040219082103041c540703a00c5d00000e240d60040d120300c0d02c40e0031a420f140021052390080c003826a010b11040110080b03000345001c0d008001c01c000380c0007047c401d09600c1402035456003c1d125902c80c0b401405000b000034a0450061784c4660106982595540e07030901c3c6070303050010044002070012007c0008000c1c0003a65180c403180400c19103041d401c0a81c1c0d80c005d1790ac0078003030416110068205100c210 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 773586151 1250 773584901 773584907
    0x8060a170d051308071e0f080c060307031e05040b0703020406021b0a03150509011a01050702010f140d050114030c1014040302090c07032d080c0c06010807032d0201 72
    0x807000c0c035607002c90803540340d41340c4c001030385010741580101010032000c00c04241c80d8103001e10385502400e081c0e190790003154a401a550b96030004900c06c0d51180720044005a103244c482d601c000440409046400e803010307807031003d0700e0082c00142c45c151010040000040c080f03070300034000c4908130b588640c01040c00e00040300525551312248064158406041040003010520411004900c8480da10000a82d81000d08200d400c440707022901c82c030040070f500130031295680c100058400d00390702800c0c00780210100c0e8900b281c40c10940c0000318081000810706010441c103035800706050311983c540c00c4140e4000ca400f01a912501e50031110341c0035905070318000b00603209520000d2884443c1c01441d0a05481c0d900268003010201c42481c002c4401103403480500d503010f48000845100b40202407000c540a9210000c1c01202075024018003c8880101d90120103c5003120b1100800b4015a101f80d6165402c00340c95484504c82910400c032821022280348100710100c1c219004036409641d80090540d0040d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 773587401 1250 773586151 773586157
    0x50705040314010b0a24090609090c0306032f0a0b0a14071203021c05090309011b050717120309030301050d151b0306080a0203060c220608060a170d05 66
    0x2500055486450f105030030b8841074040b502078010011221070030b603030300d24041b18240481e84d081010004c801c001005031036048407840040d90040302c40030070850380121064002e006180d0000b0104168041c10000000310f0041c3c9412403098100d4881004405904005a00b000c0f4001d481c6401000c100300c0c82094002d06e19403400a185505003030405040381c0300e1540440c20480440e010135000510510310800340e1401075402d4800d0340c2c0400c0907041c64003102d5941e0103010042810f0000c880745820341020202000c6042a91041c111a500c1e80c03941030140e034030461145641c40900c42d20f40690b800b4000c01c81030768410400e0340000c1d801c5a02c0d21040046180d010001560314070802d42480c0320014150007504010b001e036107941240d110342d07020000c040346c1140d40003200c00e40103000064016907011a030150066941d482039130302c4100c03c031140c031107080b001d809441850000d001d001a80301c1d003204107180b14041c1216894540755581c1d04484040f01009181303800c5401440d5109840c90265020b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 773588651 1250 773587401 773587433
    0x100f0f0e07030e070b0301060819020703020c0f06070204020708090f0111330a05070801080a0512071b030303241217130e06030c01050a0215220605070f030507050403 73
    0x132140c182e59285075009080c2d10a030040c90000c3d10b19000c001e62840e081d09000041c40840e0030031482c4c0000d64078002d46548900e80035070f20607400c1202c40596507a81038250b4941c60f0b00204219070343c62507803600d03400320b500c90140c4600840e104d0180400c40c0d8028040421442c6180c8050a03070890021070901400c01f40d1086003221204d90141107851140d607045075441103500020000f25401d0a0102800c1040168030510140c0d0202c0440c40000703002003111000c0085070348410b511031400d0715045c400b9a14484142c0d100e8501405d00005255168001c0780c0315070300500d40c1d4403c0c0d00391907401d100c00d4074550060407115004051141c0001d441c588509040c084800c040908150b40342c01d8000400710540d0021403040310540501142c4d18060015891145090030039030325103404540b01a4075482d1001000c04c41400c20000a40c81103280700102005c075440b40d00001d040011171400500070101a10000d0001d0101c00c40c040340c0038041e1044501403800798a400703042c9841c40d620f8940c000c030b015803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 773589901 1250 773588651 773588653
    0x621150504030201200a171b070c03060b04060b0a110a06020c071404020414361e0402010905040b0d0b070206040515010b090d1a100f0f0e07030e 64
    0x804640804418480d040c0103038440c1d03002190031003201c0700c403002001d40ca018101c070149080012074461504080d643c00180469125072a01b41d80b155200003d482c20480c0c8081300c0980084c0380b204122081c1e10b00c03401c1d60310503401041045110810300046a8290040141d00501042240645802095106802105e50080b1203c6041c0c6545150903a0801c0d001c148865103d135506004102c03090748080300a45081d0303411401c06182010345008007142c030b940c10303001c2e048443d40e200c00d40b440c0301d07492616888040c0c0d0307100c803040081e100c060241c50304540340700700380c0c0f0b102200c1c01801c00e05400c0140250303016911006158200010031000303040c280e0300c83c1d5110005480e4000014060b80e1031f580315a1468001d40540d00d4982803050800300d149120880c1000410014000380640d00151050484160340381100d800c400d142140409401081c10380c825080b031310030013500d040d6082c0c514003a141800815140b542e52000304043c009014021480211508000038507064803990201070312a2100c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 773591151 1250 773589901 773589923
    0x9080f070f08240c0d0f0506010e0402090f092d0f06030a0b0a0f090506090708060f07023d090210090605030f09030403020603010803030f070804020906010c060b031b0301050108010621 81
    0xb00394142110700c0071b0040d03440f1030381701c80c1004040d60f04044049440038095906500e448010340c0001c00c000442480d082c460103501c004598186044d281502c510411140c141c1a5448041031205250004584006002c050040020441d08000c0f41c0c00c4a1544c1c880000b4030b150325402e0010014103a400c0760421001e40d1020413401144042007554060f15003e0040c21800d41088003071414110000c250241c500c080c1c6003132002c0b450740000c040501610b64030141949a0030300c1407090030b202001201260000260408103285003482c0c0c445011907100722980c207254410240c040d00d00048030f100e2a07000ca8800d2000449061604660381c0e48441420f0660b8680354883c0d0028440b5002a00716030b032154070110401c08602243d03015a070b0001d07451300780900703603183c00e50000304a000010120f504202028400304100090340d00900c082d5240102521140284a206980c1c0307036a000780304611075800c0000024007410184242e0003a0340340403140001101c00044080c1181044c2541161100e40178 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 773592401 1250 773591151 773591167
    0x10c0b040b1f0b09031002130614071203051006030c050a050309150c1206040612060e0f06070221120423030f0408160b030a0b0109080f070f08240c 65
    0x109491401408030925010740303484d2a28185494020420200300e02c2510402c40440c18030036a070000c40454490746040c0802940c01e80443d103842c0a400b00003081d5840320200d0108898050b00304612503107035440009403442c2e9489040702551260980040450700410035071b50041c0c401c0d0010b40e800000710f412103210b180c95081e10001d07000700703d41d4000009000315030744203003440681406411007070440c0c0c2030004a04115180040200045004041e555a0302820346802001c0c0301401c00070302d4030001d0b207034075251003000a912040918280c51518405201031003650441e4400c6d6440b000b044400b00c04071b0b40e5259180c80c0307080c4040900c054200a40885015115000c2005009030110450025155450140b0251800c5107103030304e8080c0d00710000c40038031071000c00720103480d40401202d1002c144015520016104525150004140c41c081c0d03003d4403a60042c0007a04408541c2281c440040b0a41d9419a4580310740d680c41c10240e2001500100b40b0104004054040d00000c0888004d80f5020031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 773593651 1250 773592401 773592451
    0x61b0e15040b1b010e340315020318030427090f0506011701090b07080c040305070609090e0312040201140d090b06120f120a090e1008010b0f0f10020a050d0c11010c0b040b 75
    0x711008c4020116000030030006d0303120780540d0070307114211b010008600306411b182c82e071011040c0701421103000041703c0c02e260507030b17081c00d40140303418a802c2048001481620304180d17803540d400340113190080700c1c51030260414110500c210000ba6030842c0101c42c6540354600100ca103040c020303098045d5101d0a000c0407010034802d02242000f0004c603165001110b1415038020b0607118400c402c813005410901c00d0b068502c1e04500c68503401682441d10340480703040300081000c58061012040c0b0010324290019040101440360340b8021002201c039515501802c1080a0740c65005491034407803600a041000b403039400c01000341c0048a202e08010349990340b80c02041140107070464050341104000c05040210348402c1c0726089490a0588110380300d160a4808110444c0d0301040080c014807c000300f225006109110103101154071000780e600e030482c0094002c0000061003001d0b175180301501e50320182da41c0905140e10080c4d902040580d06a65180c440c3c03c0780d1480241030864107030400800f48200c1007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 773594901 1250 773593651 773593673
    0x102031b0601030c0504090b1b0d0f060e100302101101270213020406091707080303180601120210050a09050306010909061b0e15040b1b010e3403 64
    0x19240c004041961442c10403850360f4080742d00103401903103400d0070000454464410241d00c1101c03442d5003805008000250700781391050780d1146c881c29141c40310700c9140ca601c80d0000b004550380d4040091139074640d000c5150a102d06403000030360001c204242c0c00c5549004031214040041460000602d412038011601100d0750501500ba41407007080062508501d03043e1807585030300c40800411810b16040030405008031071a401548507a841480d901040071104100d0480500000d030700f943d8580c20043c90910b45980102c60b01c9040d8040e81c80041445641e009507180c1c03007078000349030010000c03a1308411307201984903040d514100815030501213000e440070031013a402000d83c840005404005410150202d40001081e000c10782d98a030103000a50f40e01803e08000043c08956402090702030080c002c00034815540081c1c00000042a114000008d40c20031844880801c802840302c000a01a06529072034485c1200f900340e110f90710388814000e0480305d01c0c1c0305d101d051080b07448410784944940040d80 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 773596151 1250 773594901 773594947
    0xf180201080406090203011a0315040b1519060309140c010507061d06070e01091d2e03080a0338031504050a0302011104030b0a050a09020d05012f1602010203 69
    0x101c00d5054841d48c0c3d0500f0401030028040d414540305140c10150707500740d510b01c0040c02c031009440d415444021507613a00ba28854158802101b107007102987d41c1070141c0900030504060382d6011440542400d601d5000c680005c0012050b510585400030964490000300300c041e50762900c108401c692a00752081c1002850300400c01901e451180e5082d00c2d000406010b41c80c0c101524801e014000c0b210011583c051054120704140c100b04d500314400501400714500051043d801000840000420b10140c5c178020b14015803a9a0144420007070b80a044915040d1010075515505130402040403070048000741c0c024031b0070014144d801c2da060154a06203206015135080d01e03c0d0f088400d2050030140c0900c107500c1c175418584030a0b070405203551150600901e0040402044030344034800104042a40c0c1d00140303035294010640c02c01d104a03070400d6030003003121000085080f801d0171010b49814203105210203079210300b1454a40780c245102ca607204103405083c012410740c403003844100c050445115200c1c40e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 773597401 1250 773596151 773596181
    0x18040203040c0e181e1c1115070c1b080d030b031005010617091c0c0b070e0609150d02030c031009090804030f02030c0a06050d0f18020108040609020301 67
    0x482c0c180416005406406401c00201d0010383c4c0011089410118044240055005600c0c032800b900d1042c950808162001d80c600c1741640148400106070001d21081d881c1019208441c0005192380f07140c001c1000944055000c60310494080000646c0000c7d0b0000300c1480718210b498903656403208600e020181ca130013502007500d030311198015080402500c440282c1040042c0b015524006001c2d01e2590540b0301e100c8a144100005500000300f00202d205840349681c078038041004042005000300607001e411a000b21004000c921000d110b510b424400b008020300d86850980d0400401840048040b0700100c940c40c10f1141c0c00c24840b0503c05544142e4940c05820741d43e00c0e141000c04d40501260f0401c46000346412040c034082100b46040d01d00350703070f400030f840c800722a0503000003458050460406980318040d0300000c82d10b103500c100036000c400180301042c00011110000001511544e401039901e84040d000001c0140d889030071000e421500500300002d00c40e5058001c80d00b580c080751030221b42 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 773598651 1250 773597401 773597423
    0x9031415100501170601170411030a03080a150f17070e010b1b03070b0402040f0f0c020c04150b180d06060f06090905101a0904060801150e04030905061804020304 71
    0xb00d503000074010035060750f03451003150207260900000c0c10000c152080005040a06000201008800c003107809011500404951208440f0714004044c04011600c05450074104012400b030241d86c2d80840059601030140411045c1c105844d80e0b20381203150614887e140700e900400200007454441d8039004c1c00e20000c0350703544d4014080b0003414640c6034144801555004100440100700c424019075000ba50444020a500b2200a948006448800000c00017503141048200300150005201080c10906440030b005014425491007c3c485c618400c00c00480c50400038064504200a0214400c042c000c006901140d20703900c0c1d560803510700340c0103c1c03a1202c1500c02800341c10307002108807004000c421024007491a01c003848816540311440b9041418000071915a10803102d034083d00ca07a41c1c0054070400c00c050351400e24a0180001090611100b8400c0d8004684816112201440b0300d030103880d9440c80c0c43c039200a1101d035a02003442d91002e0a00044042d085a4450000b9401030303009004c5035035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 773599901 1250 773598651 773598659
    0xc0616111518210c011112150a0b1c18050a0206090111030301060c0521160c271805030a180f0e070201060b090a0e04081e070308090d0903141510 64
    0x1003100d440c0264080baa00040c01548601c0a61f00c0d01c003a844810350102c500c00411400115070a01c503140c0140d916240b01150500c250071044008600c080d82c2c0110503c01e510360300742c2801c05145007480241186e00208900c801500744a0b00410b1307040010b240006c01280c0000d680c0741550800c0e044113001503006c061107000d01c2820402c130848540c3c03041c0300b0381004400341122b01c0c1c1c1c0c1c45401d0b802010140401d036050148010b0503805030083c508070f04040040424460f84a031020348490203104494030307100c0900a0f0001008a00314400d0b44103000354a81142d03200c0550315803007080700d5040743c0010040b000c641c40f0800329038007005040196011210f41412100a0b081d01c14070b4001500f84601841641225620b00c1c0410701222003810074403040347c0302c90405a20920450108524201d030b8541d004030b0500818004044003030184d984d0070410348a64460700d840c2c540030412240041c1d9442c0702440814000c0340007844417501e980c1101d00c00c0058a80644106108980c1090b070310078140b800300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 773601151 1250 773599901 773599903
    0x100305070e0f0609160c0501060f0605041e1a18041e0507170a020f1b03070201091409061c0507150e010c0b0c090102030c0616111518210c 61
    0x154100f003080318016520b02d4822200c3da07407001168404010000400f483e07000b40301c004e62080c1c010380345215061500302d1300d4960207007156000340b00380320784004070700d8500c2c0342c04100c0010036003030760400d00c1d19608403160000004920b801c84d40c214003181c0445122905965901c2c8107056000e00d40040610020301050300c003030101c0d54000c12150031b010300341c1221b0b000d04404144807a0b211040c2c4000686502421000c0002c5000d00c195001c403c0081034080030000e02c0010140000b18400d80c1e80803130440d12a0911328804120a544640008038003021610503d000e038180d00104401c4041e031544c40c0d01d1078032441d16003c050303800b00820b101c1c14400c440076154848080e450100bc20308110a00003030540d98207041c4040280f02040d900e1010800703c82c41c1e84240308071040012071404032400e40c1480c502c81d505856201c40030704089441204d060042ca0f0000c02d003a403170074061706151120343c0c4e1618071a081c2c00e4240a0384040d5800740c0881c080000320465401598041d0a13142c1e1611501520080d07 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 773602401 1250 773601151 773601181
    0xd390b060906010c26040f0e010f03110f0402071b05010807110316020613090c020c100c1115040b1b01090507180207060e0604030e1017100305070e 65
    0x2a01800034082040300e144d0b0001c1c10304d07001d01c2e4484510303140e003c200440004404201c41968040140008002424840500c00401907034200b0f00403840302d981e00c440302032255920703120007054000c103140081c226180580310200b402c00050005403405c21103541e99030a072030003505a2071200d80c81c00002c0c4580c3d64490445503000440303091481a03440c03c071207815964052904400780440e442e40c00c02c411925000103031aa20480114180b44407070300c50340c00340e016101c011685401031003085404646071424a00141c0c0401150300d440c4800300c0300d91525000b0703102c0c146c0c0303580d0005080154850404100c1e80108010700454151585502c0d8021111685841d0040003040c140c1c14082a5070205401061400485001d98151400c4e40050150311029000d404c00140c00c0e14a89941d0305165500456a0b5104503c01d07501d00301c100c107002e0108401140310403009000290042c95403401d844d040c007442e6800008060400403915525a1958581200d540154075101000001e1080f04100780c0c1e08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 773603651 1250 773602401 773602411
    0x20102040b0706021c0c1b02040608012307022a0f03190203011a0a0506160609060903180b04060309030309050d020115080c06073018090203090d390b 66
    0x1060101082c500d030020f0201c1c00c9401c03200ea489000300c0c0200119034070342d40410001c10440008dc090b501d4101c1c061411600c820050241608500c0000b6088510104400240c0080b501e034900c0105909200a449001450901904001081400002c80c0d030704004044185000e4400303840382c604c1d18410b00d400d40d80740e410f54110b1a4020340200715903956940211042d11001e40798107468100104a44260700195080034050a00e480c0100741840034641006090038002d032295000803008224040c1c40c2d0034148207480a2110a0000b4001c80d4801e40005102c1d50091501045800e101c0c4c9074a030614803e4200c4c0000340c1c3d920f114100d81e94905091000c02408502c02070400300c034590012440070311030450024208818485c14100c0e00b140b0801d44808201e904003205284400602c01400324406c1804080c0344401c100c400003003140042c001c503481040341030084c0c8404100307518140c2e480e03540c0281c54000c400c0382542a900c0c501c0c080d410300000d000644002c00804109040513500300c0e1010300 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 773604901 1250 773603651 773603707
    0xa2f070e06030a0f030c06050907031217040611040305151605040f12140d1710081b0a03080a0305011409160c150614031902090a0c020102040b070602 66
    0x10020603a40c00b20f581e20001e0740100c40d00e104c00085140495141203080e80042c40d0a18150611800000004004040e648030303407440045443d0b6007401703540c28211200c1c0c0078403404035100090f0010f21142c22001a810b802041203003040d03129543c443c140070050120707840c800395140070081c040e552090350345944070040c2026481d1034100101c5049040890040243c2107203000070748401c200c042c002242c0041c405406451030701c49030000003040e040794414021100001180499170071001c641000c000c880075503001b00300c1c08002038202120200101e046075482111300c3c0000010611381401880d070000150b80000d80c0750705010f4624422030b49106118020420344041150190a500b40c400342601d590030204908095446c01d00300f0049503c5103892a02d0a0540000350344100a00c0c1c11038100c0e041302940c000002a4480b418003802000c4003039030008008020030310342081644807038032842c5a17100151920351514206580303a07000380d078100c4800c0e5000803000016851440340c02c0503114005 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 773606151 1250 773604901 773604929
    0xf060c1107090b2202030916050f090405010213080706080f07051206030a02030102180a050904050c090702030903070e01151403070327210e0907050a2f07 68
    0x200c001940d5032001d000e8420700341e03a584103154143e0303514120410310391240140c1051550311441114003039001910420762a2050302e20b040300080c00c01014600341c2d4000352800d00b81c0d141d44010407480d61000350046d1555507003005003010300c04030841c82034040c00d04000140300603850a40002d040d1b40b001800c501c81c10302224284010143e0000440321a04000b50004c0c8154070740c00002410702000c02002541980300280038240c541d00000f51072002130007102c04007440c659840610203019400c81c2c004001d5000101c00310801d150520000d9082005441124241034038280420710b130491680094070840c82c100010416a18105552021000c0f80c0c44c0101d12404ca00c00c4220b0b1318080034007040c013410345030340e08440d030a040c01481008040c07030a0304d450845181824240b5068042c0340007585000c40c480c40d14000280a2001010054005130420f04c43d0768a0240c00c85040e0400000501042110700b038100003520090841c00901c0021901e69040c058850b0666103840e4450f404840c50b04a22 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 773607401 1250 773606151 773606177
    0x1c030903170c1b0607180806010605070c0905010b070b0601020a0b1b071e0314130501120b060c010f050709060801030b0a0b060301081b0105070209130302190f060c 72
    0x185812291803105003000310300b0707141c24a05100900803003466201001c2c00201020b03d41c40c000580a010b10025107030701c0020a1101100c2107070700702070300a000c460381c0480300402103144507400500310507010f042031295143d21004040207580080c1e003e0008004c0114052060220862280e90800000d0008025400160b49d0303040c100c3c40300520485ca66081440e2500400d4403107000c8800041c0e002c40020041072582015140860b034201c3c0030380000b15074181e0a415202d24200f110886a01100b011342030510304801142c00c1c0600d4200c06071803540b900c0d180b000300e880704c00c0a08a010401c0d800815031081000140e402c03540000c2c80ca0b8104030701c90004009407900441142d040d00e821001c90402e660320440c810000e0115004d5064011350000000241074001080d00c003614110062080381c0500400011101d5004884010b54880740c003030007240303030314001191a5128a200f4015118403c405000a03084841440401d1344c43c08044414107040002d184100e042c00c0c2114140700c0050802 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 773608651 1250 773607401 773607407
    0x221030a1b090f0f0e192403050f01090507090c050d060b0d05060a14010e0a0503070312030c030507050301140a03021302090a0e040b130615090c030c020109050c22020c1c030903 78
    0x8082d11004003d1710120f5103543c0340381b01c0d401958000c058008001d40c0e15400820304120700c503680c80155100d014440070444900b00c1802030030b44803604103004000d030504080b07600000b068440c0740501131102c200001d8910082c503000c0e0400400401105036160202018020b00740c800c0108920700c940d910180c03d00454000031202e000342c50307084c43c00b80301210081d00400c0303203c1d901360040c40d854424100008100800500c0a600b0703900183c0d030500c081080503800b9025224180c81180100d503052005200e0000e510241e44183d40e00200320484403956900803514500000c649848015000680e90340d45042c00e000700700040010083c0c0610b41d1405858031034040101800c2100315280f07401d000000d212107500180c03000d00380c0c40f03605540981d513136041200a00481404101103403c0c41240d8080324018031030451203640050191040040000070040d2200d012102c0840f404280480c0400150491014203100c1c5500d030020101400c80440046681d81005010420941004011000658 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 773609901 1250 773608651 773608679
    0x6110f060a1104030204150816030c060e060d05013f0204050c0d18060b0d12050d0e0a15050606180f1305040c090b010221030a1b090f0f 60
    0x454180001520000850803030b0041c0319551020b5402410030808240c00741681400c101110040011564600c20158483c80c0225540c4805040c854014008000030360094030040c0407072100512152401080503141e404486007078104003541003040c0e04003014203c60101c40b242c04e11446d115000b03054400d00d00128181362420009026540710008202400128070030380b030f00d0301050842800b0861950200c1454152414011380708141416011901414011504020705802518030300080360003a50644d10395000614a07207260760390303920060168109100d07941400d442001305d542460142d442e1002035400c007401540c4100000c01c0301e4082444c0d8008813041c3c400d03098400c80003d070800000583c49c8101e4201c01e8404a0800040004201080e07070100300f40d070601c00301000359000035801241e4030b0742010100c0f00c0b40f081d000070241030540a0005507501004807032000c241150565620440300c92480c1e08500451080c1c0710502c01840c043c00110701821071115105545882e0083c141d20307841c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 773611151 1250 773609901 773609911
    0x110315330d06080703110103110a08040611040f0807051302120a110706020412120503011d040203010902120d110a0c0b0c070512030a0201110c210c100606110f06 71
    0x88030000350705141c070301c2581041c0b000b03200d5401511034165a07400c060740820000c3c045540003d240000c103021045600c8103507882e4842941d0b59104503030b0b550762020000d0899000d030b00340501c03062200180802c5608140c402908103c0050201c2c60300d41000d02c00b400d4048402c1005150051200300e80080c440e0030200c0e0700ca952841c1c0840c508080c080c82d20428820044080c040900004000c1803058150079100c8205225075003010b0074114255044450340001c2c0540c0c0c08050b1000c840c00c6807482041d01094110703000900016008a255000900d9401e4880e98404542c0107810b18460264102d01c0e40112074903014041c1000f211170707551703940c00308101b07014401d0506400324000c51103a108010350740c094903003d040c00b80705e8001200383c19569008940e0000041d07090000b169040c0d00084e06940c100000d1200600c100e21a000c41e41c81c0480300d0448114603c00107008003014000104244a0401d90710500060309909007200281500c504810308080d60b03000c0300001c001c840002404a83c40303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 773612401 1250 773611151 773611249
    0x60e030403020114070c031a0910150b0906040b0706051906051008070e03010507030f0b042009010516031206320d02031b1c0b010e0a110315 62
    0xc00d0b80740b0701810039500d250406012480c8000e144423600020b61301107401004900c08807012526a10045000c0d01e02c040304442c081c0031604002c1051241100281c04c00090003803040742800d8452481075656080b804e82034880c0340c0c44d801400801d000d00280240b00c1811440300340880b40c240700c00b00d280d1720085e8505c10104100b0742c001074880c0d0310545220703409000c01002448a801c000d54000c000d03000d80515040b5161400c2000d004c2440c240c03180000c41c280c1014004c030000c03014a0808861b0308805140f07411b0010800040014049100100c0b0780316129444070399076410350906d0070f422030b081c2d904001c200d000c6594138051070100840c03211402c20310030b0158401204086001c00c02c0c0480e00c480007500351090451a030f409040081e50038000e043e06580f009000941f0010000d18444030701300140802c44040010702a070400107000c0703030380700080c0540400c40c1e00e40011120748541c0304036081c1c0300c0808014181403442c54610381d0700c03551100d80342c0c4000742500300d9103d81d048820800c1641e855 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 773613651 1250 773612401 773612407
    0x905091606050f160b09010e03090a051009080303101a04140907020c0a0b03013b0405010920040b1906081003080a050a032901050304030c0b070903060e030403020114 73
    0x680d07403c1404031241c2a6200f948602a40e9862070702019400090302c48288950810780d2071105940b0000507102c007040020814814946804180801c401c0300d0011001000541030010844880800c0254082d450303407000d80f102240b52161401005540e100a007484003c204400c001030301d01d20f00c1c2030890364003c9510314010b40f2250400c0c1e203490248010950001c46900c0b0005000100e940618101c654050503540304102208600411128040010030584c0c184006010010b0304c0e055502d9200c0e200740300001c0c2900395600e03150240d0340580107040c0e0401070034900441509050050000000040e1101ca45103840361556940d4085c5500a403400c0000f000009000301c4603890303810004603004210941d07903108206004015600035214000868140380e040300109840f08041000c0021078007010301c14034002001181c07203a0003d07000b40c0801c19501c1100300400c2c05244040d005800d280ca415422a01e10300e080c0090b5201100c2680c0d441d08144401c10140c1d0b0450409116098041c00d0b26076 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773614901 1250 773613651 773613667
    0x7060c24090507140310232e08100507120b0310230f010605030109020d090210080a06061106060d030c080c2d100c05070f060204090509160605 63
    0x1004100c080000381c014490f1200c0010910a10041480849000e03000e076854005c03400002415581e103296170034070310400b0061040d5885540c401c841d42000c0c120307040e0504280c401d06a6003d04062034170200c80c1c6c150703c0b4420050b00c2020081e100c01c041c4808001d001360720b03003042c0183c11120000307070820301c4907141c1081c090a944c06102a96850341c19240400c020740d02107804030400383e40e44448075060350f50040030414808088040303504030b500540d2810302d540c4c20a002407000c6c1d08041f000c070346010745030f6608200580e039032090341c104d0384603c1d510840d4a142040384001039035455842801880752a4100b2141901d022401c4c076030001e419a001c03e42000b00745400c4508551030907015040b4200458942c3d1858400b003500300340b010a00282d08250118491003508107400241342c181160700810103420b295840303400a1a0703460310f0b401d1242c14032421b9114480c0c903040000003180e00d154002800d02035a000d51103803680003044803008001c0300404410401d84c4079103d004403420701c000815495 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 773616151 1250 773614901 773614973
    0x5100813020609060d0f14070c05060703090c0b07050a0b0c0a0914210106030308010603110904051b070b1b090901030b060d0614062e0c0507030c0602030304030207060c 74
    0x180502042440800c414100e690017a03000300b02d003582c40e8101c4280100428003a510801030127880b10341001c040c01c42074076828806d40c010400d03010110317001c1580c52400520b0b071000c1c80207401c04030300a50140595210354a0440c24602c0c000303016845402c1d061000089959104603c40140d030308a000794090f0640160005410b88611104040a4030360151590300403007040d048201101d10a80344c0303001c20790b20741b1000e400b519a10380b6465803409050080402600c0c240e046190007550012003130b16428013000a11142e6404006c09075440e84000c020700035621400c0030000c03008111040d070036003440e1078500054041c407010720000e0415046040418016521580c00d480b100354403103000c1014012500c10b4002b025070494071035101da003c0419210b01e500c4030322501c00c445540c0d0303c5026601c2079039010544200300034000c141c07206d20610307001000185270f135070104002d80302c41c1e001580c0380e150514000385040d01582023502040b4007800644001119014009080300303522260b04403060501c5504 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 773617401 1250 773616151 773616157
    0x606020f0d081015110f03040b0f070c031202070806010e0f01030311100603030905010f2109140f070806070c03020d05030604140f1e150f0d050d090510081302060906 73
    0x10510800f58184002c000c25004200c01700303001010420340d41040754191840fa2030b40918411542ea8440c00c02051940985000003802c129104484a2049544988450450300b0070401c0310000346e440742e1028014070310100405c5004042e503480f9200c06150500300c02c0e0b03200c4e5061000400713122b5040829484c41e842440b41172103000030f11000b0040c4590328140105040264070402e0f01140001400c2d0744128442d0030394000020168031004089410328010000415a1510540c0d00959045011041321018000134502158180c018880c540c14400454182000908a03905104207000f0343e00010740c020803142c404040d141400380c0c80e6665500403a01a0041e10501d0807140640002c0021038072420b0708041c00741c178105600300365040301d41030081060001583e80051006410031880b070180b0b0700c14403110480308090903000082c0910b50782d0515281400740c07044041703940c40320b0500c607030b003040c550710302a500e500e10b0401007600b02024611698600e80388068007c290005204009071a01800c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 773618651 1250 773617401 773617409
    0x204080d230c010c030c0f0c11190b0403021203131509030f0b090d0203040506030c0a2102070201080703090221030417010f060626060d240606020f0d0810 68
    0xc460b66494007900018000c0032801103101c003083c03500702c1042c0c3e440d110384800200a02c054944184600984d101c481e103030390380c2d500003a42c02240b80c81c01c03161140c000b00c40c07900100000100f440e2124110700c100700c001302000010b8100c0754824095089000b42502c155000c03110070003c6c0c800348c0240320004640c132451940024144600100826042180c01010380d40700302c22540558198202d90352040307031640b00700d01c81c440d400b81c02400401d882102c000014505100c01d400d02d4101c071141c09440e840b07003035001c0741c00550f800d81c08502030007035507004103501d030307010b030b481c0c41c0030070144015500107040c2c51200c081540140000c400810030f552000c0049070054206100340d469101c2d1052021806400c003d00007404450401d01c00154a600400718011201d10100d45e014020302c0401e500c0341803200007407600e680130280c605c500020941c07010885510030002e0102402d00100542d06d8800d684555020300c0856000f80c020761600d000100354000502100e2800c0d44954450681d00c003501c000c00d0304 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 773619901 1250 773618651 773618717
    0x102120715060509090706110705030f06071b023303130c0801020a170a0204030618140c06090105130504242102010323040b060a08010204080d 63
    0x248a401d0021100e80d034501d1030401c20702031100545600600094800546a01c0b07001c0d40f10b120f00f0f01503030307000720041d55440042d881199155581e0b440060301e402c00034405245c0e01d410a006100003030380d01c0840649501245034a116102e0069408178120150716291040303c40e0003101d440580702c107884a000c1080c0c1c66801e010b900e03400d00400b814004818102d0440300140000070014030140180262507502e0b46039196490b50707402c2030740c0108490b5030081041045a50030840400081d02d1403080449030103800d00c0a5000150314036004140a200d103180d10300b903501c50031a041c41e80e55483c0c2240c032407400170f2801c5a00c07008a010001c555482039004154010b04054071140e202c0b00c484405c3c100c20280300c0d1103044407642c1ea00c41402901c6400c440d21580b01c1045404070155000390002110b041d03d01041c1c406900c1100001981201c042d1030441d40c10b104801030040502d0400061405840614021898645002246543c1d00c10812024080c8000c5041c6000070300460b080a00014080c10 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 773621151 1250 773619901 773619907
    0x1031e020c070806060f0d03020a0b091b01020f1b0103060b1602040b091003020904020d061e0e010b06120c0c100f06060f0c030c1518050c030d0804060b010212 70
    0x856060040e4001006148161041d100001110480003a01d00d016070030141c4200241d880940600c6400d007035583c0290194803e168960340001e958412480c41048100d0140c030a402400071004115100202c070281150b00915144191000c0400c084510b9a0406c04c3c0d64a01a14440140e018000799440700d418114041829290190348802250302103100315000c001c815604010000508010384110344c242210345001d10060074100410750300300b8002403d5501c4045c2954841058544280030031482090005c040c5e04110503c1c0601e8441030b5001009103c01941100458154001c03092484140802007001c40e80103c10786084500a000d644140c460b402c402180300030207400303041e181c46c035081d181c10360010316580704140140c200c05041e950f1100204c0d15850460369140145801e54041c3c01d400b011061a0030903110b104d001d1040c0703141c810b003000e010b403e0280c10038400d03192840c082c0e04200441c0d8030059105202c250300640c001400a040800710300100d140c00885d045140d4124800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 773622401 1250 773621151 773621201
    0xb0301083715050a2309120a020a02030c04060b1c0204081204140409021f12150302040e030f091002121602040b040b030d0302480607020304060e0103 66
    0x1541416680c65418500744070f15158000150110340020445140e00c0d5064404104407422802c1c2664000c0c1c030340b5040f6002150030244816003a030003804001c0250b07010051150460405205030503100a003201d007001a1494003d1711600762182d40008906002030f4444007134150f0155060f10f000c2c00110044844002c50b95403080d010340e03c28010381070f070588070449442c1185042c4c05425080c1d58040c0c510750f4101400000700400788030484070f17001800100c40c100c0380484154464810044442c2c004028198a140140402c0ba101a9034810301c0f9001000201076003110030382100c484203402c2d690040391040b0400304905086101c08a03600841c40014505044507000b420256120b00840b4100701115034042040211400b100a171909500400b035050072581c0a54040d11800f0303080c02ea0142d00100d880e80042c810a860488052007082c0789090281c031740313103520000c090078260200a10070350a1161000c1d549014503c44d5400f004514000c441850b48240c03c000c0031014200b040c0c20800800d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 773623651 1250 773622401 773622413
    0xc040e15122803050f360105092b0501020319020325051c0501170d0f0e030304120b04050c0d11040f020d0e0d0e010e09011715040309030b010b03010837 67
    0x400246004440095006c943e100480300d4054090010584410f480d0602d55424402e04500810000c8186c1d001c01c0c0d000490302d410b10400034855441200016540e1030003040d410000e044101503424440d00c14000c11520404c042500100c0f10a40c0b8510303c01c0701800001102d2a1041a0f9048003604400c00e52920952264010300d040e90101d003d050f91018150505030303611800030241c40002104a8404030140340a10000f200032800641940d2400351500b0a01d260402400c204941d07a040d01c804000a0007400e112f880149282124044000d448985850040d0300300c00d000507205660301c001610011040b82e040300c84080d02403401b031110081c4054259200c10807021014003040000c40d81c20010360ac10314207c440c03504020955009a42001142001c021000d4403a8103644244bc500d0700c942040920564841e520039612003904504524000d1400070041c0c0c00400c034620207100610015034040358110b8144802c5040b007000760781c14210306d24141080b00441c5400b91102e9032603014024 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 773624901 1250 773623651 773623687
    0x18031306020a291302030106120305070b010b0f032d070e03010609050126010908070c14010e0121140c04060206150a0303080c040e15122803050f 64
    0xf004004141d6025640554140c002440ba14800c61403003000002498003580c20304401000780c0044c00010b150740d1504030a0302c1401d102581038001c100040303224010440c1c40038040d8050008400400d050a0b4250301050550002801c20a4860038407032525209240a00c812445100281c15003001c0c1c0c1420100500748041030035146010394241100031451007228041c0a04030b881500800220f0001400c0300c84034118a0311010b0802d5481c4c00c0920042003449000e400b0141c069943d40b04050b00d0821000034014801c4402410700c0490070140e05103a802c04c14403a035400e5090040c400000c8642c02050047c0b26403c0401115043c0c5420b020074000b008d80078006440385902210b03515201c0004100c4602c60381c010903070344404542010300009208400d25030f0040c000380e2000b41800c0e150030421081000890701480c42c05400c500c8200c0b0303440d20200f0031031030000b244003400d03d60443c112048514102040710089103901c030f6000c80d0800d03200d2821505150450100303030f9201c10140a01c900084 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 773626151 1250 773624901 773624903
    0x40302090a200c0313090209010f0801081506032d07050405010807260d0c38100e040b060f150a180902120a0501061718031306020a 58
    0xd00d90000681e503600c440c403030000381c07110400e0b00d001d8145020110181650003080400d1240c002840000e111072601000340d0050040e0711400b41c1c0700d072495000105000c0e0718001c400204190880100320b040b00c045915000f90304155101ca01c070755030340070200f842e001c035480071140c803106e42425490903586203001281500000c013090710001503480302048181c500a008029581c0c0240c6010880103010015104101e08402c5110040c4d080708101035003403042c1410000d02252211502004001440e60a21510014080c040307404024086400c1200d0310b0400301905411075071320200300a10020b0040d44024410401400581c0c034041ca40030000c00c0007038405d10300072400604045010320b41070301e02c9102089402c0320b00d4200300700d843c41152000034a0b054602071083d00a00400c0c0c914240c001460103413045035001c0080d04000e03400c1c008590050f400360741000b9420703000e400790040360300a0b290004001d150051002d44000700b058214420307504404209104814000f41041d004500d41d0205 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 773627401 1250 773626151 773626159
    0x1b030e0109080d080a02090f031906150b16050c04060902190f0503040b0403090e01060206070e0f0a05130b0901080d0201060909030e010f1808030423090606031b0708040302 76
    0x1030b6503209481e03480e004180e5075400b05090702e000034041030107039020300090100100743c440f2490305040844c0c10116075034040342d1070082c8000400c0510180b409010b0390b0303180c1d1482c4064494502000c407211805600c034190191910800214244002040704881c03005004104102d080c0c1e8a03c0a00001e5014a450000e441c00f030104110003140100a0710003c1c4866807035240c41c1d680c1d90b5031111700e0b96400800031018031028540110710240c1d08101a4042c00041c1c0040c001030401e0789014041c4000194405d01c00d0301060310252003a00c03120400c1044070b0040c0c0d0020f00c0440303c103580e8800b801040741180d810200940c00080d44950000d0301c0002e84441b0740080089030707241c1c140c0d00e06840c9880000360111b005800c0454071540700360361640d1a07c0d614a040e0040c80d0316582c3c407004590540d8031000d6541e10202e014046044500340d000342c0074103069030247d14000c8600105880340c00090109100d230b0340c080300141c25085969038510301e00f80c024200c00d580c2d40081c074201006070403901082c0d0107 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 773628651 1250 773627401 773627417
    0x60c070c0b0c03040b1e1b011a032d010c0f08010803070f12020f010507031b02160314030f040801090605010e060a090f0b0a090501080d050f090607031b030e01 70
    0x1003044008121020440d0360300c00743d403415080c070403c50031035803105800d0400f01120365001c00480080e00040e02c104d103591102ca00c20088840d11540c03e591441003060710a03002d01e8088c8203540c1d0700061121100020074000d1014070340d40041e072841f030b4280700518040d5500703102c416101c0c0c6a2150022a895485481300c3e20f0a03600d54120f590707240100074009144182e024120000f01e0901895204801b00c01d00c1103030142007550000600317440007030b40d103070303021070380340c90900b05800c075100e014224050043c0b0080c1000c6024041280d544101c82c0703c084d005200314032131711001c144180100c440c02c1c42d5044029503155910b051684c001c0a0300581038854071300d8900046815540c4903441e82c052a0018041a0754074100064000100340900002d00c0b080d81d11082c0030540d4940c0c0003107100510080761f0000ea10340c50302d001e032414249941220380c100b21007007013031311440184101a512201000e40c0d200c0d442d03074040d1806803400200b030946201e400c244080403030105940000340c065004002e90320022 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 773629901 1250 773628651 773628659
    0x1d010e03210c09040b1c060603230a0b0417070503041802072a0f08010902090a0507021c0c06110309070f080d1d040920010503061e01030e060c070c 65
    0x112006081e601400c034503404001103e01c928107034000c22072540c4000e0182c00000c159189403084414154000c46595881d8001041800240700b1b401e404c4003031034054034084d40000300d88542c407500c006000800340310343c0001281c00e210700643d21000d00c00c1c40716286660740c0240e04043d580c0c1c4e0854410352458001d03c10006202c80402e00039100c8140c2c1c8480041011425102000c40c03840004440b105a400c400c00005070320030200740c0900090003910700028040b851030050001c0c5c0c000040200031118201020b108034158001001c0d1282640c0d42d0600c52101e030b601d0b100711201a94403001400d10780c1099502d2040c003c404004500810180c0304803011a56a08912884a2100e02c9110369641280e128103036164020103100d005403800082d0100c89904101c006411610400c206840b001222035000c0302d031802000c0ca030b0101c3e51090070030608528080700002c0484c98041e4502e502100c440030b2150300f5074041d401221192004074103541c0c8604d0a03170b0500d20a0f8024903000d40c0d0b220b04240c4000707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 773631151 1250 773629901 773629957
    0xf030907050103060f090903181409060a140904060f020d0e1908030705180d0c0e0106111b0d0b040506191a010809120307050301060806030c0307091d010e03 69
    0x10381190b1700605594445460041000e004080c8088164148443c100035007130040e18000000024024840310070180040d40b00c01e00c80c0710080141003d00030400c1550500604404007031401ca041c0003200da00c0c51582d100d2a0420113400507141f689078250011441c030030041100d8001c0b0010302c501108881910b8541c14480803592041100584545410004501001c0c4902c6c02000030305e000200e015010703818000840c401c103d4152041e25500d0320030f00c0c180131442e265413440703006100d18a4401d1441d0480e01c0f00d20b48580000302c0c0c022803100002580c004030b80f10b01a0f00e121440e0800c0b984005c42c941800c0994403034200302c034403030342014070524580c8040741c0300c0c0b0a00c2014205040c91402d201401001501e89981c05010303103a1500c03c02c00581d81a120b900000c6210760440e81d40c55403654135010000d0035440b00a8030b09482500b000c0794848484e07c0004090302215980b08001c070b4551039440b80c80a10f12020302008400e0350925681c14543c01001005060090100f0868000f00d00c1c203086d40 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 773632401 1250 773631151 773631161
    0x90606080f060315060603070309020d05010f0501122a050402030a0c0801120302100905390d0210140903030714060c03100e06150d090c091b050c0102040504020f030907050103 77
    0x4e03403c0ca02610007250a505100018542c803079090f0400040c0aa81034000811031075084108a03003580d1500d0a400e410b5000b070158600504900541c0c0701500441c1d40c600070541c0401d00c02d4613941c9521050400d9217204a901c100c01800c002d44210b42e41c1c1021032518024252303440740d400100380325400004801c410b6080c2803001ea5013540c0500b00c4c50072151031800140000c0b030003d8034a8850750b41c107400d00200307050380c8008000c2101c03665483e0000c03101241414041c01c0e00c3c0d0302c0c850001c80d080803003d070321107a804502482d80c500d4050b66010750307402e101c40302e800f40e1411540c1500c03011a0610030802540142c00081e4143c10888200d0b99a80036400401d110842c0c0c404903600d4008401c00919080c1d665840d000940204140b40e46d07030b9121025101a081020316140542e1194207107003c0c030210a20000103030010340c3e0b007480405200070340803a0a920240c8080100000050300b41c80007607082d03060f46c1c080d1000610940d541e416105041302c19800c10b80c5c591002e8003c14400040543c0244a4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 773633651 1250 773632401 773632423
    0xc020f01092312030c0601150206070c32011a090c07080a171e070f0e210601090b011107060c080327030d0c052d04090606080f0603 58
    0x210b503103a15185040c51101c1040201e0150002198030f10140c01e1030040c030141c10a40a114000e0100d985426030f50740d060351180f8a483c0a40d0445c1081c020050b0b4170500741241d50307400c4030300214598a480360240d00700a443c005800750581000d1030000c1080190028031200702c9800d0740c402030680d1181080403171501510069242042040ba13000081d4000000d0301c20480242000c0300b03410b00000114200c0f071803c6460310300c0841c03091a03400440c6024051039400c2855407800c601021520704000d4440c454813030341644034211b1580744040c0701c000b18102d06aa1520f44090318004e507546c148100c00b03404120303403043c0803844102119410100009440381183c00a9441d081600443d0720713143c1d010340c00607200044109007003800c07665a041d002c40c0212952603250080d951381c11290441022119071001d00d0741080410000101d0740b40c5c82c00740c810075004a0005a0000003500207244141d07103e160301401d91141040c0c0c00045054010010030312170101c11551161503585c0030700f0035480d846c80c0c0b8a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 773634901 1250 773633651 773633669
    0x2e110f071101090b041212020c01020a0201080903090411090103050115020a0321020703090e0603011406121f05041505040803271209040c02060903070305130b07030c020f0109 77
    0x901808160640e20411080c1e006050140d039141c0c03183d040495962290308407a144151a411650070044650f800300030002051020b040750f2100c1d840002c3d10340034100c602a0400801e5030202d10b00c2e41c028001c80d549a00010070421507500c100b401d141031600465000f60110340b4203400021400d400380b10741d8244030304540c0648500d4840c3d95003610300c400c4440e0613061003180060b403010303180c00c10310050030505e0098031110b8840345481d1504400f410700411382406070f41001741c2d118007407a560f1441a0440401c80b4104c2c60700d01c0540300d41d8503004a0404500320021008940c003505c4071240d104a009038040c440a5001041c070550040680e10241d90003840c4981c2000000c9a1800240740b4a0070000070801c056149181c1c1072100d40fa0184500d00c02104800000d0600414a094400e00c04844500c1c0080c2580780707803480080c5e40340d008181014081c0800010040c0c0170f5491921880c000d040316aa0941d1142d072942030042141c0210b0394201d00482c00403040c0308496024251030703011a05c1d188 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 773636151 1250 773634901 773634907
    0x130812040f06080c0f0a0e040f0e030f030408160b01061701030309060e0301061e0f05090603150406020c010c050a2007050d02040e2401090219112e110f 67
    0xc0b408646039003000702603005013072051000707007084101c03500103280740c0d4510b81e14012001618030070001110481c5503081c0300940b518044030351700c03000030080d248800412001541c507a56103080a1001d403040094007907400d070200003540308005415017281c0c1030b520710f9950b000c403d42c400d043c61030000401380409030110300c41c645d0800815204520780200c000303015001150340c030ba075815070000000107442d40f03000944103500f0030310100c018120b4140013031004584042e80307414550301282e11000c204a07250010484000010140000c0307804494011351480300810035038585450040598000a10090000320300d10401c0c4403480301e2400d610f20751100100036104003450030f41000381c2e04500c01b40480c0c109486815006031407500717100b0a4a40d0a4000b212002c41b81001800d102c41c003816000014000d1060085541c1c02c030541c0d14000e810101030401e00c0d03100040c5078a052030000100560314040400091440c0d410030882c00250150310300305000d100c40200c401440c400350103a0320342803031150024 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 773637401 1250 773636151 773636159
    0x32a0307060e03210a0c0201061404020f04080a0819020f06060108190501092412060911041a09011202010c02060304061811130c08060d1106130812040f 67
    0x280e4040d002c0414603400320383c5089210035080303280d0b040c0000c0c030401c1c0884150400c1103007000c5006880b050b844030703c0200400d034181116100b55002910710940100d5021600725656103250045401524031142219001c103018030707040c21035510081103260070701c400d60b65501c003ca000083d50000141030310007400c01039580c1001161784503002840c2d00c109000b03034140041c0c1e06442e4464a07020304001100401c0480c101d60707600005c254801c0c140307030401c4511981008466000c900c1000860b502400120b032490084c2002ea01e003a0329901c803140e11910300040c131018034450503e00e01d102002560f60403090303a620300407170320035044800f0082c1c0801d13604102440140b40000003076500c00d100e11400030780b0030906600d21207003404840e4220384880158684080600c1c00e580c0c8010080c2544409000c10684a103000341880d0028007428050300c01d0004003800c00508540c3c921001c07101400003920748a0368091081e0b5401580306881d040d014110001c07500222180403030301540e0803039031150042854 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 773638651 1250 773637401 773637413
    0xb04020f0d03090e010509040804062d0509040e01060503070b0f0427111603050c101e150302010f050705010b0a0303030c02011b0906050703051605032a0307 69
    0x40089900030852889034045560324140e89401030b00950381c10660b242001d00c1801c0004042c1c10161190300c86008101c001034480c82141e09441c00c2d03240948030141c2109044100b000070070031040e03d4081c600f036003070b109690040145c0001c0200b220103001e224040030059080704d006005a1b601a00001014840340c4140c0c00108201e00100030000c1c9820350340c9050a0a0846100c42500d0740031a0020a0714a8941405403e19000004c502c042c540040c220712000c0308440504000d0502c000440c809040b01d50501159003950a507580603c903034045500540784649681c80c250341c0d400d24000c0c000341c0360b214015000d001d495041e160101c0100402a0503581900082e40441c0d040d901e50306180015151000d00070001c611a032008a159602e0041c06400c2d240c490501c00da204400071007151003d07030b01c605001c1c11900542456503a804043c10101c2e1a0b1081404045110160b64a0001000380000041c80300d038010394042d0740c04407814900841c3c003964106002e0341070b0788288040c1000c510 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 773639901 1250 773638651 773638673
    0x61602061302120102040906050102120306031f2c0f010902030303040f0c1703131e0501050f040b03090a06061a1206061b100515150d02070510061d06030604 69
    0x400280b20a005611010722075085e03074429003010f0556600c803a001c01c81c43d40c041001300f400f6201400018154540700c00440d6840d00c41d0042d1600807486084803040c2d00502d41d00050141604001004039102d80e14182880c54451440440527486809014444c0d01e20603c110110103500901440c0355860b82e0f1290385403443c034001e054a0188501e03000154483c0e130b4014034020001d4000296885040350002400c007840a0360260600306040080088044080703842c0b10152a4242403080e00d80d2086101e840741401142c01a00d03440d8000400d00a04100000c3c1d044003d0703116100034070001e900c91a070304442c02000580c5100c505003d1002442d070000b40c103641a80242c0142c002401c3c6601c420f041c9601d40c051045005154000654074021746055000b2250700c120700b0000c0b24a414203040205036080d03800c2c803e92214100c04100b090f904680c5404503084150003800301c074211525480d40b00d0040583d446004400c0c41b20700c145121140c04840907512984008000c0c1c0b035079580d25142c0c1e4010320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 773641151 1250 773639901 773639903
    0xa210503040e2e06020a0b09031902030309070807081002090103110a0309050d26061908071503060302011209020d0819390f0c03060e0616020613 64
    0xc0000d000104060240c0c07200325125404114180441c142c81c510744400281d14081c980030b026840110a100580d000104943c00580c81203c10a156850305501402c501405a003440440c007184402481260300001441c00f92048109403107800c0d507102c00e8a581c0d08a50b10542c04140c12600784600c2c0c601311a809400b8041040c1008229008941050407a0385c0c0b010b140300e000b199a80d003c004c04d0203c00c01150300c0c000c0407801c1c401d120328000e502281c001640d0200c1e0850b00500c1c4c1000031200d494030100c0122105085c0e0701b1710880e6484610054a07012580201d4001c600303220102402e241c440c2c02013900312030301a1580c0402e000c00c074100001400c59a0001e81c0c001184000001c0056901801440f90100c2034488844c015540403000b41011002c410154004078003040c92503c405000282405006507101c4503440e10203146003200c9400a40c260150814035800400014005150015280d540c2d001007550041d076505110740c038141241c00b507403078010713844030700020804200645241011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 773642401 1250 773641151 773641153
    0x605090f0705130e0105071e030507140c07050a08012319020325030204050a05090c09040b1507050c1f0f05160501060801060806010b07120f0509040903020a050c0a2105 74
    0x15201138241c0b0b6003074a00695100000400c0709810301003640790442410424400d91401340158100030200400500e950249103821060001e94503000100820614008210103080c5e00c07d07480c1d589021500034103140f07802a903c1d6807068120b102c140c1c02a1031107072241042d070800e001c0495011100c04001d40000f0403442a054000340013648203040014001c2c5401401da50140e43d560501c02400050811030780681e001741a00e03014401c068050006545030404107541c0003030841ca410340019182210702198075913500000816070280100402c0c8840d0070344c410351b00141198400d402c01c1040300788425103c4e0016000000483c5c003a481580105504143c80345802c41d48006a190242100c6a55202c2e00f056035540d042000840c41c1030080900402e0700d010014281500303034490300c080944580b140010016034120400034180900f007030ba95003c0c1d002e0b00400c544078551801039524418040c0c203880a03c280c0c05481e040e413504065142c10340d00c030071140e400124440f8509001d808400c51080790a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 773643651 1250 773642401 773642411
    0x20a080702040b09040b070207090b0a031502040b031503120901080f0703150b1c06051e010306030b0118060e070c111305161b0c031113020c0a0605090f070513 70
    0x326030313126081e41e8000c900030b038032000d00c506101e103029182c10a9540311038441d40c01c18030f0840300c41c1e5802c1c601d503044a82002c400c40344801d010b8640c0b030080c0729a4111003220080070003880030911242018554074402501150968a50714102d598030b8000c1b18422800100f1a10014411440000880b90800c2440c1404508400d21480e02210300000d0340042241d68008640c43e0032106a26210759075500f600c080400c0018140000700d4601200a18a4a40ca01005194000341c1c5d1080d030010000315003101080095584070034030710003808114400502c0c0c00b404c000010a08000d071401c1d09001d00400e4546140c402210798903601c00014040d040c1e82d010241314112001c541c11801410303c60400701c46038109603881850040d02407420919118507150103850404000b95407400c0500581e078006408038200e404901c00100b80d514001e0400c040c00340040741c240094000003036210b0030320b407107070009100d5036035030b0040c00365183d81031651003c482d80510010030950800405000c250a810315000c50 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 773644901 1250 773643651 773643671
    0x206071401270201120e1c0e0907120b091035210403020a0b0c0109060c03020301182c1203040f12081e0c09042408030406020a08070204 60
    0xb0707003040c1030003880e11141c100d0065542190303880040034125001404041058100306d041c41981d40c1100401300803030042c0a1000c2100318007030100744403a0a8000c4c40080d06243c490b100401001c25544c00c5100c42d8104290750b590780c0b510a154901c603454056410203a50b2078007480349032202000d1007e908450480b4041c2200c1207607200c01194420195000300f144e902449c15082071807285600140c0c0d01e400502040c0016902d1034400422212803840c01ca4482010319a41401040c1100380284594a03290347d00300c0e01c940507009076040f00d00f907140061140100042140c155103810802c840320300c900040c07038100f0090401048498040800840303c40c503829106922241d031059038291080308010424004006200d400c501403003c0a03d001691401c21f0101034030a40c0b1000a110282c8051600180350039200809451052030010401c3c0300102201110408130360458090a180000012020409042c0003040368100d41c82d9600070006c1d540142c8805070f540e0090003089071712548038a1020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 773646151 1250 773644901 773644931
    0x300f060906102a0c120f060221130b0a06060c15021312060b0607030f0e010e060a050408060c0702150d110a030509061f0e09011b050301080c030304030206071401 71
    0x1a40d600382d241000c600c0c8102d0418021a4105038440f41d1001c05c0c4180311400a01007058444465a214501503100c15503403001c01e40c407011016100b8607004290b010009003008030302003107044502402c1041101c0d01d9881800003610481c0c069000880e40e4200b80c1c100081c1d050800e00c0342c000d15590300504066841214002c00440741d8002d80300300c00301c4500d020510074280f01c1c00d08400022a182460311120703a03006032842090f14451004d1142004104800d6401104805843e110050240e56100d4400001070640d400600410000c0c3c03048000045480382c010045528007a0001c10382c000c00b26150b000c4001c00d6102c000b4a42042c0e0300c1c0e01030b032900c003000c18001c0d0405108a840114561070304035205403400c0c100a2000b42d0083d90f4480102100e0840c51451047d2900d0820503403c2d0354440078500d0140c010701c0300055009191200b01039901d64040041c2d41030b50f000c1c5050310102e031601d00c2090781d20f004034040030750300100c10003407003002400e01c4980320313290302840300045007541c5e02c0c40c014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 773647401 1250 773646151 773646197
    0xc020607140d050406110115030b070201092103201210080d2106031203020a14030708100608010b0d0209041d030414121c05300f06090610 61
    0x107501040010030181718240d08480e011501000e254000c001e011002d10042e41055012300c4082c03e540b0101b0b02007001c55100790042062540c002000e21303200d40190546003202d101c4650f82000007858101144451840d00324030b4400c10010310409814090140c651f1441c002c030203000c0196200f00d014001980354420302252450024036140c3c241e41c1840341c51045d000c64a0600000003c504c1c00c1820700c009150810b04c0c2e90061400d140068842401c0d00303050324005030304d42441080450210400c94055449425184500c050070072001e10569117034400c4c1c4a40304280112150316805000d013180c140d0381a8050602148014030100710040c0b40c001c01303211074800281c074940d241c10002d001d0260741519040d1403441c90081ea03600d20890412040b90383c80f842c0041021240303400c02017905a119110f0700503154901d60038034415004405241158007801814040191a01c000400140f2030300c254103881381c45400c3c007900560072503581804100c03885228030341d5001404001002043c603012102a9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 773648651 1250 773647401 773647423
    0xd02120f0a05063903100308041206180c1a160b010e0907050d083402040f0204050108040b10150203070c090510121115030f01060f0c02060714 63
    0x82c210f03a007043c2e2102e91605403682d072510001050034440c403c0720385020440541200420b80740316126100c4561121841c403555101030b006483c04100401e24106110820125510078641003001c100b900303444040108030404050305c2f0f221410b10400000d5001b914814009002c03901c528500300b40b2320748800d0414002d031000e503804107030440140541c101d040d0341c007900405018000c04000e494980040e020700e0540fa0001c0540c0d00201d00070001003801306020b00003d81603002d00d440040d502c40e12462505c130b080300c00d034031070350a0403041e4078101340500c212025030b101070f075810b80d440e03546803503404104070b0103015890003c800000016403500d200c082e6900550059001d55030315645418041390707180e81c036040030801a14207401e00041c40008118541124845000344080040d00e082980708880702107001500b000c680b840c9958412500b40003144943c0440d5aa6141640c075060212039000d100200d02001c0b410007001d010151030b1410180c210b00d0f214002440303840c5407150881c1c2c2821841c0704 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 773649901 1250 773648651 773648653
    0xa15020102190809010e06160e060409021204050d050316050c0c040c031a04060f150309050a0b0402011d10350403141305010e1f0801080d0e0d02120f0a05 68
    0x81032042c0b00f5400e0051b622840034880080c9598100980100111015504070a090050004c0e12044507200c00341910010141d1420840d110610309031400018801280c007103405000721086038400600903c2a28050303501c074000e240b100060031078103950561182084072510f00c00c910884c403c43da510f02620098041680d0007242d500800c1c0c0010116504100282c0e01c01c50502c10144014003048c0304d030100321880032b6090a20f10850740415001000d042c00007078800d00402540000340011624121702492007a40c82c0c072042007034440144900400320b48a240e001162a40c8402d5172441200003210b05034000c03008240307a5030180130026401e8000d40d0f548410380b4226041106042e040300203526042c0ca4034140614044070400300c0c80c0008018010706040c0a079401e00c0d07484c02d4407241d09100d071940d0008074400d540d500450300505600d000b480360305da041c8604e08030b00014a1041c9002c0346941809000d01402140c95420420342181d0160380e452148661b48001d00c41e1034080100b943c103980120 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 773651151 1250 773649901 773649917
    0x120201050c0c0a080c0f010e031903110f010c120c1707030b04060e04140706080609100305010507020f010b04060501170405121801030f0605030c130b060705160906050a1502010219 79
    0x2c0500c0750f0541590f0a6a050114201103002d090314081070020703070201000451141d5201514054034334038800742c2480740610801d41c10304244041544070110303c01e50354a940c01106610300c1002d0030340384400020f40004000c0c0c031003000a46007c01240e60080c101e82800301e5800803030340104080381d103035610030011405407000740310511010012400c000509080501103090404038060f01440b0043c1002d4002d1801c80b00180e072844003504d902e0060740c2e10070700a02075814a004000d507078124800d06204294600742c80d6500511f4184640b03411140b040c1c40d250101c5210010301c032200303040144259140d028a246580c5691007400003003902100045000782803950400c00103040359482e4034100e518526100050007280d80024600c001c01d6400c54220300042e6141c000382005d010b144426035040600401e0300310400c000400c407506500d04003c00c2c1d070161541da850020560b2454030a142c0c2181d2114800d200035407510b42c00006003501c0340000341c500f101d103141c3c00d0000581400427900280b82c04e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 773652401 1250 773651151 773651173
    0xc03031119022a1503070c0606030605060312270a09150303120603080d0903022b082a07060b0d080d05160f1b0506070c05060f01120201050c0c0a08 65
    0x16410b01e1800c1c0304103c8003a1801c004000100362824070008081510b4800400080d504512604102c0b001c039074403400a112035a81d910b000300c05810103882c642c0c424042e05d04040103a10b5084240c41020080085003200381200640d4000321400c40c0007601d4119168200104145441e0300644d0140104410702c94a5203286040050042212141411416042500030004100c40b4020b48500904880001031410f0312868141d1520380100d041d01c03c0a240042003480c0180e6071280c64840100d03540711500150380314100200c3d11002e224800000060f0000180c1c80e0b903003c0d6000e070036168841d0000044451000000580741004524115400300002400700c60041c0305000780d82e00144840f200090000c0b0001d8054003465a102c8030504200c180c1d44680b2140d0301554200440750b80041c2aa01181400c0303074000c00c0281800e000745c446200758008651082042d0804904845501c1640d0800707050a6004450603071103002840094440da0311200c655a07104610300c4010014403008100301292 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 773653651 1250 773652401 773652433
    0x30304051e1201020c071a09100801090b0405040c150908031227070302040e0304030f050d0e011110020a110616020d0e0904080d090f060606030501150c0303111902 72
    0xa40b00300d2640144a10409124009059410f80e0003020554a55070190207220509000d000025644000e5416400f08201c0d08460790b90705030b50000c4c00c140580c0421500740801d960341610300030b08040464200700408280d126004200d88410f103440460580d6030b81c882441e5421070200c820710106410140b004040c00202c04c40c1511400b1418403003d68524079946498900c517101c00317070045071569260f0914920600886019503801502c040d41c440703007030a00c2130750391820050000c04501195901d5100f0b41c090701e00d00100da52648003d081e8108824445806500a4107000041c02420000e001e1601418001c1c14829000c0f0389940320340b01038400d0002d143c5051074400200340242d040502005031207002016900c80d0300065071a41d16000d1425180c02040a298003804803030250300050100140b50f0070550440d01c3c60303502405503903243c201c4102d4540c3e0705404c802c0424004542800024080d400481500700c03e05135041c11700e60a824614100785400fa840d00041e0405107040204201d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 773654901 1250 773653651 773653669
    0x90c02070501080c0313061b031401050603060d0f0606270f060605161a0408030a051b031303110304060203130b090307120503130b04061214070e030304051e 69
    0x800d2800c64058113101c400f0384031a01c000b604111b9500005002c070004d002ca00d401c0100c51354411120081024000c80005005103000544c0c18007200822000080078a08841030b603000b000002d1070303880001c681c1d43e11440071098100003200e941e601c40c8000640343c00f041310307105840040041c042c11042422240749045401100d081c15021749041018410140d00905954800490f14041ca0b080c036085e00b032112441c5110460030f60101814410042049852000340d40101c1403400c042c01f0740e0700c81400140da550425401900464800d000165240c4407014100f05294040e08020540600c5a500b0504592040d0400710241e8800180d401c2c245900c0d0514400038180b0200407802c2c03040d100e000070303103030b0400d44a0350307501081c40d01c04a8140f040c14001c4914000c2038221100c10180d40da01c120200d0b4210344100c0c0c0128030b00302c5d00130040040034029008586c0302044034000590781c00f502610300001003149a6011307c02840082000d85400d0040031207030301400d00c1078842da805003040101c00b807 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 773656151 1250 773654901 773654909
    0x302100518090124140a0903021008040210050f070f2a050619091205070e0a051023031b0907050408030f0d2403051b09060906030f0601090c0207 64
    0x114400300100300034004c18100402c1146004d140c50001500380004403600e0701c031945194181480014501902500000080b0403244265200241032151500907952000121006500894001e10400c0207610500c020411003024407000340c00d0034001d440d041444072081408403980d40704200f5020070780d108200b038403841103044214620f109050001054a90248c00100c01c043c543d44141441c509004642c80c8016100329400e00e80460b0f40c5045c142d0303485036244a0028408010808900c0c4d0749403a0085620648070010600c408a15000c01d0040c6512019400380761006c1c4900c1070841a6801d20035500d550f0402d0b80002c1107030010600300192190090420407e01c8400c11007004610808410b50304084d586a214503110036000113400050844e803044116007580c0000c038000c1c1d1001c410303c17160603a40204100c8402c00d01c0c0c40001813100039490303036036540603000341e000071210714000389050791100e4003030140e43d124403044070380c40c0c50100c1c03e80001d40001c0d101d003a40d80c845070741001424018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 773657401 1250 773656151 773656159
    0x40305030c1621080318061317180f01020c060406031506080105030a03030902041e0e120c0a060504020f091608060609061206030708031b070504020702060f070c0302100518 76
    0x4040400e00f1003083c0c0c1e030000030050f40001c0300050100d05562881500c448480e000d4601501e0711050b00022004c200c1001c07280e5450b4150501d45041c00071080c1d80f030100000c0c00c9809615403000401110500204401d411485a00d030804e1460b190381020300010442c50324003140301d0749020707401030101219800040130407004200401440c0e90001e800900d1941506000416910038004900640b0300d2800300103109480c24a00440000158800400c5500b500f0a40303040a03100300070040c1c42d10400100e124290b100003000300114000d1f0384240d40040c8010301800040d484080400c40050088907084e21900c50f880320090625003100d078140c0c0c4118120340040c41c14241c01c0014105010300200030141c41c0c02c840005401e03440030807410340a08952800c0b40c0c5c680300c070480c0d0481d041840e0762103240302d0f0160840004183c2000e0096a101582c020800341c1411265450303030000e60010502907443c80307001c00000004d61076810f562842c18071150b95036a03032800f400503120003118443c0041409 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 773658651 1250 773657401 773657429
    0x6020d0c02120f03062106040f030807020a0210030c050c01060f0f0b031b07030522060f17010e1009060b070308061804020621010806040c08060c0a14040305030c16 72
    0x24554801044a43c810401c61700c6c00308480d000300102c81c9180e03c03075107103c10301d01c81d10b020301040c400c0c0f040d54419030394800e03a19409159100d81040ba19000740001c003c3d009901030f040c0264050182d0828291301409103405401c1480308000780e42510102d80c807602400c1140002840301800c902c06002c0070f0082c007419203295003032003032911403809a495802c1d250b4400124110040611a0048820b05090b08003036841040c1d04400000d044082c92144034082110a805080400c0c0281b40c0c1446620518400c095140c0c40c000c1c58900380000100305c900300c0b040c0c0b590701261840651246d00c020b81042ca075455280c214929000e801001c010344160700c540000d4486a82410104000340e0340180c0c1520300075204c055490b46202c81c0b21648100b00964032002d4000b168011780002c0d900e204502480f035000358103946a80c0c40341c603040190f030107000d0303007004000c3d101285020307843e501001a4003040349481e0540c0c13034640c9820364000c405094550f0b00080c404024109100c4081c3c1d0140030424078080b9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 773659901 1250 773658651 773658667
    0xc1401090f230d050f0a0504050310050105120118110109050a031a0f150f01050f0408160b0f030106030e030403060204260d0914060c06040b0f070806100503040f06020d0c0212 77
    0xa5020300c0c800602d142c840007801040780c0d1f120b40c060b54000c0401800b199200c4c0404041c040c0500024000e4a002e0000902100602c1c0014040c50481c0d034080250303003000c3c10880d2900c1c0c41c00700c0c51a12550521080040004464840b003490030300641c00303a40a103a043d1103040e07046010b00d0010302400300d1810070a05002e14801c40090030000d0003000c4035481070340683c10005071014064840004130940004c41c00003100303503010940d030009040080542400075150f001c1e42800e8066034003008808007040c40180001c030301a901503285a2590303402c0361b00703159803a694801664000e4100c0c019402d0060000081001c560154610007550711002e8441101c800d0001061030341c2d0f91080d000d90030388805014015031129402c443e1800421416624145420b0401140c6154281d80c14403010070301d480069280d0b0b115110860003036030014840b2034001641c1e40b046a07590006882914120180005040080c034244010000c3d00480200400c04504c4c84001906250100340a04210081005094 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 773661151 1250 773659901 773659907
    0x1215050f0405040317010605120c0406171305160518072708030a02030c060f0103020a060c020102010f050906070e0a18051f0323030a0c1401090f230d 66
    0x380c084403095074000b400c0c1c1c2c0c03103003011100c421802c01c3d0020b1703048201001080050b4018000c00030b003600381000038441e49071128554042e1140c1d202e0b41c03000803055444a1542c04042d13001c59002081052107082c002c3c0c80340c484c242400040c81152540000e441c1d020807117405c140381c460415a40035240d813421403a04d60b10203130103422802c03a5001c03006100d01c0540d00100704800741c80090200d100440b500c9000b0310700081e640fa03002c1800040d5520038500015080b6500c0e04420b03050f0b9a010b040b445070a41741c00310944180b101c412003241036540303c01c0400700340c2009109a0303100312500801401203092281c3d0180070150700001403801203000360f0013130110780d030340c617401004044e2280d1000485944450300ca19000c001c1c444070303504011071084000103100001d00d1400304050400000c100126401d0b1815507a0f02c41c030190040480d110180140101c0c05841c14a03c810309654000f2682c244280d980c00c421080c00c10007107510410001001c01601c12024002420700c0400000b482491800c850203 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 773662401 1250 773661151 773661169
    0x15020d18020f040f090f050105250e0405070917011a01020a0c031b0e010602070906060c11090c0f0d2007051905120301080c032509020d1407121505 65
    0x43c0601e445054030b03c010361842c3d00800c407241e0003000a80c80014285001806820f00b56426090801100d900590708800002c00000048154840c1c40240090030140310291000403d0300b0140901c01c10f0002d4800903c0c10482101541007000003006603520114045140c0340300c1d071450455000b1010903002451941e801c0041d640c00c0b07101c90802d540c0140607200c105505411002418603820300004085800181400995a0080c024461103484040c1115001003c0358041d140151a003c000e00f82e0401e02000c507040450380005a18081030100c20b064039a001c010b4032181c050b81c8010403040e19a40750700c82003c03c42d20101244ca44074a513181c8503500c6494800014003469003040003c20002c003000100d01c4919a40710254417580e60784685900c4510010a030341c0240180981c94400c408110f9000417a08540200ba103122810182c20317000940100003600c0b40203980d5a12210340c1e00f80341d84140e1086c00c456440c0a10700c03960704d0a9800b5100403d400400040f0500c405020b25a03d000d00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 773663651 1250 773662401 773662429
    0x3040b0d020c07080d080f06090403080406020d0b150405010320121f090603020f030d02120901020102160b04150515060304060902150a1403010806040f0f15020d1802 73
    0x580c0b9440120141c0f800d00c0c545512005561042101855149070005032941c0318924054407070703200d541d401052100320341003120010700082d15200050001041d507030180050070808500040d100d030403d80400c98803501d0504600305400301150400c030a40c2d15020301c400114a0000185401c1c0010115071200e01911094410032a410800191a001c403440348a8881c3c01c0c42d081400f0140d40c9440800007800300d404180d000d078104940442140c1000030300c802c140c02490b4000d013514110f01444480e03d400100780107046540070850090800e1081c03482d10311190140c50003110605180c5861001c00d222000300f20041c81c03c20f410480ca007181081c4101040c141a15065565a0340b454800300500c1c2c6404000d41c0044c54035920104030003410040d041c94086911207001d8001c08041c5004280170174403e03500c595200500103800501080c00e009615481161403050070800c56841d21400034103420803076059540810010040f00316805143e090034030013010700400e081d007174021800c0000c83e012 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 773664901 1250 773663651 773663677
    0xc020a05030d02160c240201050f0a1503020904120810060e0d080c010510050907230d2307090509012d090c030203091005010503062d07050702040e03040b 68
    0xa102000c5151a204a020840d44040c2420003aa06d8000b10281001540001030754400c0b01291043c0e00c40c01403090074060000c0c0102915035580300091040600034417045440c1d81824111b0002c0162649004640114858441025003a014440c000e25441d0000d28809501245540420078140c0041c1542000d41c1c00f82c8030501510740c0d605103614144240c1c2c592003c150300e400204007414074003404d0a01580e00032039803e0200d8032011400c45000ca9017503410080d6a41c0100320100c1040b03620000c06514295400100d01d0038030a611021403d100385810311183d050310700c01c22268036844040103001d0001202c11002030350501c103500e40e801070000d0b5003810400a0300e0303075201c00c0b02c18030510600030405280284034140d040c100040294100741c48208161040d0b0200d801141d56600806050360780240013088a642d401150010518008000c40c10b450540e201c0b51002d41e40b6116440d20944554441c00ccda07400c40791042c402221141d808160741a00107110922074611721300b0441d0341d800d0400c0707 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 773666151 1250 773664901 773664907
    0x60c07030b06092a13060806040b0411091e040c0255061517060708071404050a0609050915030c0f03030d020d05090f0321091f020d0c020a05030d02 65
    0x1300d400842c0307200342500c0f01e00000f1030402c001105588040311910851042c0c0f418000e60744c96100f40420703a0010300071105440d8060000c00c4484c10025226408813201c1442600e01000f00c8004c41d0494419403a00e50041c3c11640320800102c4004482200c06c0c10482c075124060554003290085000c0e1303508a0b24100000410b807040c009044001c0401300a40000e41002a0700a80740d8100c0340d00c4e030510580c42c08000041645001003c0815203c4c41440c1c1511101c89581d250201281c03413004030251039007120350500010440c0d4440a0102c80503000d42d0300d40c0c207009820807041002c045001004032165100c40001003885490101e030145070700c1016148542c4d41d1401900082c00d50103020140c400305032011604010b501120303081580600c0c82c0009481c1d4007450391590a480c0d00c20000c5400c103030344180030709a00d100104035440e80d003d24000305440154407800e9104103217203000e40200080d02c0d004220240d45c00064071071040401054001041501910b81e80c0f1601c901840003000803942d404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 773667401 1250 773666151 773666221
    0x30307020405061809030c010c02190605040206070c03060606080a1a0f03030d1b0f021902010503060a0509070309051c0912050f030c0321060d060515060c07030b0609 73
    0x42d403804e0740f0407419001414952400b08080c59494200e8020340340305d503003407420203641540007041140400320705200303140c900d00c0c1a8450102402010300100e800050401590001c501404640405148a00000b103a00b0f8900f2000400301d090203007110945518080d8070440d20000e40d07840c064081e406030f03032440100c4003a0001a0031400380d28038450310b040c20000c1016821045030107a11409080c6d499481d07c1d8207210303400b00e90304c001071002c820201030510300040142d03000d00c02a43c0d2091008000c11a180d4592010600c401008c0c0d600401090f00c504000c070400ca4240801100d01042c406080800054110f00900302e6030240300c0e520340143c80406000910100b80310042d00c0030002e00440f0768403030300c180325207640e6400404148081035180007024044c42400c042c0704e01a030343c01000c0c8100d440180c0c8841008001c05400744100117a04845d40c1003e458030006001128540409003d410f85981450008220000c101911030022a4100f0825440b04428a03007401c03805070709002e50310a2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 773668651 1250 773667401 773667409
    0x907210b0a0b10080f0109020a08010e040611070305070c05090903040b0c01090c0e0a0c1d01050c010609150e06120d18030c0b030a0b0301050412030e12030f1b070203030702040506 79
    0x4002d5419040700c041102d4115054011540ba401004942c001011aa903191580c40490089a03806070020340c080700100702648440c584550000d004600c00240c0c004000e200c40c025a00c400e0301240071400200b205424054141d80c907000601040d683c2c9d1004e0314200d40345907180e1145000d103000b170810102c0c2d07081240d2004d511502c48247d10502101c1c0032a21030005112104044814440c0342c0c1c00d050f40e10808521510012040e09103c0200070000b0480345c005483d10f0308035900b000511f660b61342c00050001c1032405080d051003403030741c481101207007041e1800c1840b28005050b00d00844400540340140d440028031181c000c0703507614101060450032001c032000315402d41d0018102e8001318801003440805c002c0114000d000100040110b42c0350b00080c10300f601c070121b90140c502400c04070b0020b240c07402070b0030014058007118281c5143c40310a040c0b03940680c100f03503214140c0007101020044008076806d0380d07000440e42c8901d094109051740c3c2c0066070364890002c00030f000d191904089149625 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 773669901 1250 773668651 773668661
    0x41e060b01023a0e0a080105041b0e04022701090509010f05131103031b010f0605120c0111011812180e0606090109030212060a1a09011401110a0b0907210b0a 69
    0x80042001c5c40c40c43d03590072094068501a101580c1c0380360000b04071a0110f90001001c8116030004500b90015a5160200810040b0109560032403014189004d41c0c5148844030050107401901d4000456040054040342120390305412803da1600c0e18007071005400f00394582000595101c0070651542c039030310303010134294000c2515807042c0814407245001d040388190003841ca5003820140030408165100d0030481d64681441e40c1c2c1d003d0ba0418154810a944074445000c3c0c0719202500100b00c0103503040c25200d581c480110140d4020030a10300b040c240c1075102660301019090080c421416a0078084030000e6000050019407080b200000d80c00c200384d005107840700045400405c00c04031001007582e52a01d9a504854020000e4a0304481d20309001c055240840d00c2500540702e994181c2c20441056000705500d14081d0520440180c010240d000400c541d4080ca80310b00102c09042c20420885403402800f0b8100c0301603810255003441000a10001c204462904820121003a0b00c82c9851900101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 773671151 1250 773669901 773669927
    0x708070e18120405041a24090a06020307120513060e010201091505040212030f09010e04150f09060b1606050402011211040311030309090708041e060b01023a 69
    0x101039203001001c42c2c44860090400c60700705880c00e00404103605078503c9102612036070650310006a1017100c0115201d4200b9612000c0c07502c2005181c04e0010000810540c96544000c006030700004101007005801c60700d01000340c005092650a00e54450005400306685010b6002041096030724408643e201f500000d1140e41c00c00f5400301c4e880405401c030005071008035030603805581c1c0023035a080d52150001c220740150720125005c5081c19040b200446503003000503691540a40c40d602582844c0d10011364400050400c03035030040b4601c5c54148202c0542e9296031184801500031301c87c21801034260a00121030300e6200764005569078580c401a00d04943c4c22241c06402440c03e401c1500000e070000082c004d0b02e000d40844000455039104040c0c1d41d1042640d0560041e00c950301044415001d14400303a003281c895030b09140102c51000c032071600c456484200751801c1e0344540d0500780070f5030180203c0c034890121116111002042d008441440862200030040c050071048003041080c1c815030362200c1c0d032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 773672401 1250 773671151 773671153
    0x3060f05010f03260f2d03011701111902150403080c07031b0821040c120c0b0a0e120a0f08130b070b010504050105010804050c060714010e0a0c080708070e18 69
    0x1c1c85d600c009062150b00442004507a40201100c2541c0340a03000380702560181e240c1151514680c01d00203103041c0800030400582480d0740b501d4035500040e1f00d0720090072170591044070002101151010091070040b401d40b104001500b0307003052002081d17008085070ba0044203000d8891365880340c1e02c3d048400302d0034900312904009100c02c40c0010001d0590060460482c02d1081c20411200100804295501039400600c5440712090400c00c0c0350101c0e2041c40000c2c00740c68030048207665030f820780e0072070303800f55070f00400081e0707a803414003050324047c100c1d00707140761040d4018861f0080d05c2da00c0030064003600a02510441011070354840250340801100003800c040c1c015903840d00c15915110400f00380c28010148503d0070840041400c1d4810002c80c0d1041c0e0b0041c006045038a001002d1040b69480210f0a6a031042d00c8106141800e409019445d0080c040c0c0005290b4020755081c40c0f20a505207411000c050f402c2282d00304401c0c0400034214080d20400c47c240f10b80350b2210919214182e801000b02c80103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 773673651 1250 773672401 773672407
    0x61509120c0102061b19021204030c03210e010e0f030a0303050108010509060919022707031b050406080c130602060702101e050415020d0603060f05010f0326 69
    0x440c0c0c0400c054031420000e808541c9242c9079511004905159414100400c03c000d001d00d500084610030703241d940c02c0345401078441003514a80219400c0c0c2c0250000d46501541c681c00b0170402542c18500d031760840ea071158040c0c0c0c128071004000c0c04800e91340710643c108110410700c1c840707569030000c200451b9180201140c5030920f240c5005001381c4800d1003400d181c2c2d460301000480100c00464042e100310884005000d044544040f0b4074031a00d01000140c2c9c00c186440d95210070514200703020300c5000d42c1c1060092240c170703000000509890500c41228026030010041401e45500720069800340d03900380c2081c0181340e17034002150b0b400780940203c00c40d0400c14998001400e90b00420114003c40d90b560030f0703c52034212019032109039040c440c41c11078600c1d400481b0030003408641d489160054032941041d402110200708440a81c3c01030300b0303020112590703131104108200f0345104d24842c050042d00180070a6241c0b0a201c42542200d00c4090880341800c5c1d0718003a12034520a1500243c40078500c041d40b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 773674901 1250 773673651 773673679
    0xe0a030c4401051302010813051911100c0b1305010b060a111b091902070c0303020d0f03150501111c031e1a010f05040807080d090518061509 62
    0x44004296404070005510f0880401c085004140d0300c920059010307140c4041c1911210141500c156800d007040c9c1c0c0d18001d40c0401442034030300f0200c040c0c0141c000c840c02c80d6100b80c01800c0100d03e9082d07983d060188445108000d000030031a150341544145000e11801c0303240b8260900340c0c05406032008c0b00358001800507a0071001c2c3e13041001c190446810070100d400041c1001190f520200550310103c0d4414203000000c0c003803504500d03840c11000348112016003001d22582d6240e02c0c180f055042200580c02181400910f07640c4008640031018031881c0c10300515030101d00e0035509401600400d0704000000945403543c3d1700c00c0100303c01001c00041c9666005030030b0200240100a1051010006410902142141d00e054060038061000c801082c209503500200155998512405400140701051000083ca074005000c0d900042c80b03114081c00844420480003808a2420b0300071501c150b4845d01d000c480004103006140d0b02c0b500946011817606111010406180170b4000c260341e000c00345036070441d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 773676151 1250 773674901 773675009
    0x13060333081f0c3e0a0c08060c073804060905150705092101020a0503061003020a0807050a0e09070e010206090304050d023d0e0a030c 59
    0x750311160701000b08400c4003011000c84080c000c0d90f403069801c072101076070030400c40c00ba041c405038402c8421345540a0314000c2039070241002202001512004600780081018080a002c0345600c40c2e14003003038030724007a200c0c1e5820510300e4045215102d180308484401d104e8000c0824540345400c401404601145442c7ca000d5000e42280c000464580c007070041d21480a1510078030841c0140000d80300c1504004c950310900404094603004002082041c007608901a00280300130a56140907649903940e0f07162190522803c214030038980b17010144100040842e0075801040c0300d4000400740740155036000c00c013208031080345c4c1c039101d4180e10201c018207011046800042032405842c0a809030741c0241c0e034141100d0303101c0c05030b80b01c0c407604482c060408000502e010802454010031521054a20240c02e11403601c1c0d075198298501742705800e5042d500c040903006103044030024021581841e1003030459031031a481c0186071040c603000207054040201ca03604800003040c88100512001070150704002194 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 773677401 1250 773676151 773676193
    0x5120c1b03071208100504020a1202031305010b0a0303081b0c0d0302071a04050d1b06060305010c1206140105090f040905060a060911070b090712081306033308 70
    0x48441c0c2078100f800d200001e01483c000ba204204003007001d4941c03450a0b0038007000e90700c0444908100440411005042e00e90751010714040e4503513600440c166905458013500719001022030318482d403414a01000025400748426500140c42d41030041c0150452404c901c1a000303e1951070702d2030080500d4940c1803949980074190182c001c480320b0358828185803c0d8201e1280c240c90140a9802604800303081500a414095081030082c1c108943c158007905d8000c1100c001d03810031600399450717588480e01940d1280c1c07013001034a1005d00400c141440c1172080c401e04104a400641480303400310f290b00310b0755035100343c002181401038401e000007102071030f2603500c600f01102c0c00c803c6240707004004507103210144640308149201c450a20720300001c5071148d407602c031402040a100e510510002048600c81d01c480151781500c5100c40986079071450f41c00350402c6829400543c2018900381c2088820548c04428030380c0c1c004001e0840d006441d8410102e1150021604038070098481e80e8144414441c8400304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 773678651 1250 773677401 773677403
    0x60d031b08280c0c06180e0c040e01061713020d0203030705010605130e12071407030303060602010c030506031b040e1e07050102150c0d0f05010b070605011505120c1b0307 75
    0x650748003091949001d031008803e4030341c05460048852010311405000381301960343d5400114043e43d0f541c1c0d031000203100c00d50045070080d070000d40c041800c0005101d1144200c0c0034102500b048686500c6501d485503441c00000c2180503d80b0100319480f09544800540e0000300d0740240a49a03180400e0030001c0c064219032007114080c20320400f000c0c00c20a4584182d411602031403020788600404030300c080b030058203c880c0c2034a04d08800e03003d02d400791100300701110085210741c5021842c18540760010b0b003110039108000c0c05160910040144c6981c010540701c0124003a0300c0710828030b51010011400a04001e02014040e200713550410791040150060200700071003803c01c46100c2a21136004980726008034400020b40d24028010030381c40d00400c400f40500d1061000c0000f00e00c0e8180a0710000e030364003039001c0d00c2c50f0700000440c3d0042c8144c60040758054030105d811103a20442025000780240f146030520041d241e00240403541ca405403030111580008860102811050217100042e1240d001c118 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 773679901 1250 773678651 773678707
    0xc0c120305090f0f10050910060e0f0a151203140a020c0909030f04060c140109230d120209060408120a1806020304061b0c03140114060d031b08 63
    0xc003c0c510400652104d00061881c0900032002d10040500c1c054003010704120414000c3da070034001d1420151090100502a04070b1075030305401d28544200b06514041e2134603681500b803d04080c0a402501e415131304880c1d04180040100780141021200d13403074500394020007440002401a800c3c0d900046048400300c0454402c1e4550b1034103104070340e0740d10074031201602d0510181f00810000707001b0ba0500081c140110010172110f400000b09508407150946c0403119544400905001c41000703a82d0074001810071001800d1084162001030031880c0d20295180c3e071550000f840c0d880584032002980c0083c0f21032004c6514001c0a02500149500800c00c44000141002c1c0c1e40e244240801455404581094018614003403c0c44000c48150310001c801c8004034641118550000d01030404403002503028000c245d95107081003489500b03403884040c1407410341c400300c411320010b5902d26804d10306891b81414500c0654010314040c510040c00d50b000075045c40e00c04600042c019401d00540c00030120181 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 773681151 1250 773679901 773679913
    0x506041406030715050f03010303020313050d1709010e0a0b04050312040f0b030a1d161a040e060d1e110126150409150606051c0c0c12030509 62
    0x38111444040c01203840300e0b416070120004101c0f011a0040c801e400c800b042c0380c0030745071410781c0c0f8161025a0080c2c0c0202d006a0000036038200e80751141d44524003502c1c044500d1070380c5284d603032109160b20800078485c0c1c1c060800001d01c04481da000350481c070254900070b0201088280d40f400c44bd100c030b0300a440b419009000b4002040ba01c0f0f840c7c041124255034055585609550414402200355040284180005903440004003401401050f0101068541307500a107001120502003403080c2581c0e0317005203a40038880c26480201c181d0801980c0070384800940010300c55079440c000480342c1d84854000343c48103040115110b000390720304149802d0140160b2520120007507250044072203410080700074a00642c0352001031543c200d0301f41441d8000c003480e04001207040a0343d000804442e0505c40440300004e000c101c46410303640074001e000c010030450030040c0c01c1c0a00e41c4102540c3c40345c7e0399540b141542d510b03243d2000d01402004945265900860030385104075004001400400050b10740c840188628 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 773682401 1250 773681151 773681171
    0x12040e010e0405030a0806010c021e13060b0906070f0209070203250b1305070512030409051008120a02070e07120e0105072a080a03140c03090a02010e04090f06050604 73
    0x9841c00340e000c1c0d58000025803034100300c004104d40160000e0a05810002280c0c0b500d00540e543d40c480400d002d1891510285103840030702040700b04c150840340d0401c29410030741c080000b8810754098400251081c0c440c242d9414140c030306405190001b0302e000b58814003d50503c00d580703034000054101040b1441090340c2d5120b103045020022607544400408070540a8001554003805040c0305400e039206c0d4045485a94446001800c200341c00303610015079910105041240d48814050541c02051031603141c8543c6090407001e03500c8100c504044003c062000404a101c0c078801c1003000e0082c498202259a181410f07a002000b036601c03d40750070725250411560b141d02400602c1580d00552040d00c0f810b40d51000101c1034079400f0490000449084100814803000c1142079000f00704290080c3d40000d404820501880010342c40074003010300347c0c9130a2003046200a0002490400300d6024207041c0b0340c4101100c00500940000c000041a00c14401c0303255082144a0f00a2401410200c0e018403005620b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 773683651 1250 773682401 773682419
    0x14060a02070503030a11120708150405040b010b1b060c03010f0e070c0201030506060408120c0d0903050c310b030d030b01080604110403081201081b061c0e12040e01 72
    0x9494019041e60410008148903420691154601c045c0d003c07021b504102e039101d61340b58040011030351000882d45100407c03031001951002c001041d14111000c0020b030400b501c6e00c68201405002c1ca08040d5000900c1c04d044034007070352503c0f00b130400300c10031100350303207000100721555401c00e1003440005400400081a075040040344203200b00047e40d00c18144000319001140504006401d60350000810400072403c940c0500101c2c0c5184012240075582c2e0b911202c1d00c5142628581c0108200940d000b0306100040340851407540c0990119079400300100340301802118840c030741049402020300000742c4082285a50007032102c0890407801d40741050504141541070b260002d400e50700142801000503920b2505034010075404184640850a081e02d03a603503150240c1c0605030030941e1025000041100600800150340c1c0b10342c40e03402613118030321400045005e41c0a180321a11620550100310030a40101d42d002007e8a01c4035012a115a2640e4810054607802401800400b0054038004103140007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 773684901 1250 773683651 773683657
    0x1606020c06190e0a081009140706050d020702030705100825090512120304030c05010e010b0f0d0f020a0914012102060a120504080c0c04050702100b030304050a0314060a02 75
    0x5880020148642c104604442500950345041d5200b501020b000c00d09401c00c0050303005110311178034001079401803802c02403130394001c0c04540e040700e034445401800010b9000c401c2c0c8840b601d104402680300d40380c4e403000a04000d0b2640001c0d8200359102209a15142d00824a42c0503036541840e000c010041e00c098004121604940d000100d03080b01c600f00524203148103455800c050000985a80185100c5004559030080e1002c0e00020035284480c4144902032068000200303082c40200000d040d5071011590306119903000300c0c490b840c00c00c19841800300319514004211340c001c0a44d040fa41e160402540103000d007115120300054540c0010400c214200c0000d03c980c040c90b09014080011a401c1200c03550010072403a040051402c1e1000c40101f542c042e21340144e204441880d1a05d602e410b03214900f0800030f00442c030841c10501804541074000c51200b020300c403441800315211060710080391841c0308a511540c1c000140d000c001080c400220441d88801c00c00b00182c41041e214071046500344c0c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 773686151 1250 773684901 773684917
    0x1205040507211b0510020303091e030903010e160504140604110d0c0210050a0c0e270f1b0c0312070309050a060e06062202070f051606020c06 62
    0x40d01004082c0000c00c002d54006804991007418240e07080321943c1c3e0400c40c9500890b40c2080411451020701980c5000f0420f00d000f290248000c3d8114545001d905071754258010780b454424110042050501c00207104031544c00314068000d004e450200001141c2d40c040d0400300117010720038603070085614074080c01340401c0101441c400780d1403a128101040300410f4002c0d07404480080402041202e042c01d03000741034411019401400100145044100540b00b00810340380c802841d100d50109056002800c3c0c1c81004402e560540f50528000d070381c0150300d007410802004444140080040d044030380c1c031480d40700d16100b0002039410083c140c841046401400403041c5190406e00c00400c190741c40c5022168010094500440c00006603102e550606192040c140c86072511654220844201040829004070058400017002060100d00300315040001c2c005250b455000a03c100a0200144942c10036035080000d071449108040d60302201c01151348251000760141c040c01442034038008094403054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 773687401 1250 773686151 773686153
    0xa050c1203090d0204180b0903120a020c0d030f0e01060308090a0515030a020703090e01320d02010c05242e05011b0503270f0a031707080f030712050405 67
    0x18402c660030840070746011003540201014803a40d5101144100c4211400348540c64040c1d80e92b9050b01342030040450004105a814900412070000e51040016805e9001180341c900000c3d100481e422901c00f030305070111640d41c1582807400c08000d0002003c01412421403c9840201e110358800c203011002c00c0459124005240034070024501a580780c0050040c144640742c180310443e02c03144940d200310820b82250700c0c04215100300180c00b860455145c20140f0300c0c50b8528104280540004400c088000d02c001d04025180b0310b0482000001c01c20a000d82110054140010103801034842012504990680fa00c1030060f110750031801030311b041c8660160700401a162580c1c2031034010b50341c2e40e64880000000021900070b4402003002032018043c0c07002080e0b00820301c07940c480c44000c3c10b03443c1001e81074070600311a01f204100c1c1d03403102c0c090022241d01040d600c06142c002c00345606503015405000c0c0c80c08000280040012043c140114812001c503110145c100c0c50720340c4c17000c0489030f00325001411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 773688651 1250 773687401 773687419
    0x3041d0603190515040f0303052a0f0c03070311100203070509040515040e0d03150e01141201091a0a02031608060f031626060610050c0a050c120309 65
    0x1c0b5180c000010b50185019400712101c00103640c50300307014040b0454080d20b0059a10550b4410035904d03001e40d0781c0144081c00312035003080b050310701003241c2c0c1c80e8049007038441a00011124400310310745040d40d05018107542502e480b4001da09015021628800001e2601e0090100b0b81e0342d060094400d4034000c0c407080d07507428100301c4000144402420064100d0060280300030040034a40c0d2b89010f45407560680601400d121000040080c1c20b540303035142c0003100c00b503161509004103d003007101c681c111600030000501501c04103001c9140d203a480c40006d50135500f0320944c0c00901a000d1001c030031642c5d4040450006946000610080380401c1d6a15042c5070381c1000f100018520480280c0e0300000010b100e944103007200b000192828040e510f101085c9441103c0406c00c2c8034140d04080e60204d4480003000c103200890340210f844110040c050b0384070722086200c0b00070141c4a0010b99030210344540841d081020641000ca0750741204202c0c2902c12185501444e010030004000c0d620361282c040c0140305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 773689901 1250 773688651 773688673
    0x100c241d06040f02060f16110d0b0a091e1b12080909060301021621030b130c050702040e01140a0c0509090606092706180c03060312040803041d0603 65
    0x207601d000b45000d0703a10020a00213441b40c818108000c00c8018004001c54884441c645006031a0381c03c5149132500c81c08149507007a01140148011640c440c504c1203001a5820301454028560716002c1682107682c11020f400000304001074035040000c00400b00504800c07580d403690003001c48580d0034000c1c1420024444d01c00c81c2c1c18042c01103500204010005818030b00515114130790b08691007810b803803444c982d0400d52102042c04401c0e5036181541e24013440149291004951901603118601e60321581e03995500621700e200b142030341c0c0c00070340c003c4c404d02500c403948102d140030708102d01c0444504042c010204001500c05c3c46904130f0b408039600e45a00701013441041010100000b001c6035000341c0c04000ca05015500c003840d8166202c11060002001400b01000003400b0100a180d28003030230326161030201c80010005d4242d0302008071500f1540c0c982d0b440000c04d06000400036075203800e0002140102d0000400f1001d481a250346140340300811146070102d40d160041501c1d00e607095046401b910b6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 773691151 1250 773689901 773689913
    0x70b0702210723060a0204050405061005040e040804051003050403020c011716030603080a030219080c0301030605040203010906150524031501020a240612020a05100c241d0604 77
    0x40018620940c1243c040000c08001c107003040000c03681040820741c00901400390b40381510880760050303416034403072401501c0307183d000d4140d104078003a040000c01810b00140410400408880c003521000c1e003081d00d0149100000f030054001618102d0142c02046101c41031948505c0c40d4115034900301358501e0b10380e25801075440702400c0c00d4110b45c00b003585492000c40450b10b4440180000801540d0069030f035407220064180070202c500344d8408000600040c8070160140d0750549054940100740002c03649c40300e20001317004050075880100042e0400a60018202d40b4205003412940b003030b100c1c000701d50341d698503642c03592010105842d100074051003c90420034808442000c05681030040725404541d68071070300c2010b0308000340392031a1010300d4010080d40030305014580041180319000001404242d00055040143d400340d54010082c2030300c8491841e100311144424603400502e02e0700e41c00d11071240c45003031221008511121506203402170340208400f60000144100040142c200c44e280c1d581d5030303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 773692401 1250 773691151 773691173
    0x1215060301090f0f030e090907090507050417010f0c0314160509030307060f0b010507050d0807090b07050a06050c0703090308070812181506010c020d06090503070b07022107 76
    0x2a0303015036a0304403100005000d04008203020f40240c0740d0842110319440c00030448034184e035226002c2c245403000d0140e07031000081d100003a60030a201c046103ea070381e19421a07650003a5030050341a0910651419001101035009904000028900340086a142881903040e2414104500b0418050f140041c5410862400003440502e20340ba00602c5c0005650000b440d5070072001046c0c95036661443c0c400742400030b500c80c02e10b6502e420308005040061a88030b240c0c84925680342907041c0071418000a50440c4115100720142c0582410303a84c030381d01c040c1001996084c1810044580600e05408103d20010040940710210703071640c0c40450581c1182e80d001c80c00e4205d000100c454180034400421600d56106e0001e2140603058600f078080d10300a11303a0f0340303803807100503020712001d40f501d043c0302d00d9036445442d1009c040d0701a40c0b807042c560160b1411000400c5801c03000341c11400003040c84401c010040344080c7c050400d503401c4607880001540030414400c0a4911107025240421211001510361404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 773693651 1250 773692401 773692411
    0xc020607140f0d0f0c021608070308180f030706020a02040612020a150e03030304111807052d07050102040e1005060403150b0918010e03090a030f15140a0b1215 70
    0x130031020490110a41682c0c0103030400707009a0400800c541545600700700e18130041400100170b00d0310038510703269444a407080e0220022510010280c50341e107900c47c0183c0b11542100a8101c450b1107903112002500d5000501b400c9110381d05100c00000c0e10501804d4125440c0d40081c882003101c4c2c6446e050700d02d200d920032822428401d003201800304a59051014600c076500a441011123080300e042040360310b00001c5181410280c0c001c06200382140e109003625484420190120111a0881301e40c0400c4440240c20003502c0c43c00080740c1040141c190042c06c03c48018030781614060706e506103803005900b44d40c000c60350488030501040000c80c40954a80d000668104e0001035a070b003680c0c0c04101e4900c0c007290301c140701c060480842500d0340424450640c1b641c01d00c0024605003044000051000035040c400030b0814070081c0c90000c10b1005043c0000c0b800501860108100c40303803400080c410f044102da1042c1d8181c60407010f00c146080040c4100c03801c180d8400a020500d1000791107648031600645 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 773694901 1250 773693651 773693677
    0xc0b0a2309040e21190203070309060807020f1605150f0a030b1c030905031b0306010302090a110d09200d0f060621060513050d1d040606030c020607140f 67
    0x110b0586003580b014034104e4407004050340c2d20f40d0351601444200ca00b0070b10781215803c6510030400d00d800300383d2001d001001c0c3c48c002c1c50f00d501c05440c1c40900700c4c503140119000c1d207044e004104800160119194102c8121101a1066040703a03039030b419a50355038050641007081c2e01808204004009200f40d2060410a00040608080d000804841940c6010421041340400c00364101480b4600d000c00402c00d603d16000c0303404001240031b9020a13240e04041c40001d00038815103010980704012a0000e188041042c83c1098032121250b1501015004082041d510600ca1441003280786c8088124a010144017a28a11442c040d5564070320415500080607a0038680d6080082181c000005034401e490700c070104140d200d00c030141002d41c201e480240400320000311491469001800102d00000c40b14410f090003007103510f1000c903421000d2004e0324526489490b140000c107103076415a014202d6135100303600321011a590f408080d00e007141d554000d100d2096043c41200d0380805108018444212240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 773696151 1250 773694901 773694913
    0x201080a1e11090301050a0605030a1e020402070c0f09050c0307080916080d0e06090a062607050307020616050f09010306050901060c0b070f0f030c03090c0b0a2309040e 74
    0x10701c45100701e074040c001c0e41030128400030350b01c440d03031600f40129900b100352003500700041c40c689800030b9518101d00900402003030142c4000c660203000ca200004890360041c0c0107540d21940d40c60a072242d1601c50180b000750688030403000c1070041851094510500c4104006440d40d110002d040e11a100e0080010859115244c2501d0424030000161001042d85400600b00d951b003041010707015400d2508002e0080c03c0c20b01c1903002035075a0350f440804690807800c0c80c00e600c1e881084110342c11009600456410003040003440f40087c0c3c00b1004600c284402c3e400d54442d515904000300c140401024000c1c0002d4052101e50840c0c402080140140901410000788030759407400440ea640800364820000302d00301144003001d1080036102d0640c00041890072455031804520041c040310401c1105104040c1d90303000c403c1031103020358070100425821a525182c1c4035500c044600e00d80c4c0c054600540003400e0340074800c030020701c03100d990000468529048c0d07060601707502c14000102028404010188100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 773697401 1250 773696151 773696201
    0xf03030d0903030204090e011107020105090112020415030c020309031c120615020106270f0b06070f021311030402040e0106051c030311040302130903120c08041403070201080a 77
    0x621a0709903562180d140907032140d26280b4139004039400c0041c60f4010303034100351034615486003c038100d0b00940d509007882d644500503140129002034800c1c5141504610000c1c000c0746400c00c00b8541c0c0c02c403034041d58080c8490802ca4804a80303e0040080064055000d04c103103c0f15824808070180101740680352483c200f00d282440c1e441921510fa22405504c001281110061982805507030054400300201428003240201c01104e5000e40092405140e03507034891800e1100c649802401d402e90300203080d00d8596496003414090380040400880c41603e0980004803460510f0040140740c095086c042400d60f9100d809000181024810403c0036540e2501c0c080740541c0c130b6407a00d102104c3c240700200502ca56628000e811502c0b1a403c030a2001024041040165a000e100006c403008449000c10b0118491805844905407404000d0045003090b0041001541c041580c62049019800c1040340c1c0340c110365419100d02c00c450000e400039581400150314903856410030040c4950044d103c0600880c170f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 773698651 1250 773697401 773697427
    0xc030f060e060f06130b07050307060603051b03120901030e0a0c180e1902040216080307120506120d110a1a1f140103090201050d060e040b0a15050f0303 67
    0x20541104420001d450103104403400c100841c400030840940d00c55142c00782d840704030000134000e440746130b01075507000420104100f0103106640205600860074012076840340342c0140ca51080e1440054550b04044080c042d80c6400200000400d5101d094a4a0050304030011405090b80d070540303020900c107a003221000540c00c200120001c1046402d05145800868000019544040b504011a43c45003003001e82410385a0720000305654103c6005a40d480c145051040b00d82e503002c03029290000100812141c1d43d0015104101490740c880c0411181d51f5220800c40a0061000d030020075034071046210010501800118440e0b85c200e40403502503400903500c2d403032060340e00041c5205010511041c0007201d4207801004004002c450402e201003828644440c3e0744030070720b0090380c1c100364840d86844e0959000d00200c2d40d41080c002010b002e0151a48140d000810043d41c08860101c2204001810700c042c52244c90368200b1500c03840303500145000708202c01e01d0b19210b601a4940010000c0705075420b4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 773699901 1250 773698651 773698661
    0x306010b031602240402030f0d09050a082107051f020703030e0606090a020a140c0a0209090d14070c0503010515090106020d021002181002010509010c0e0d0201030c030f 74
    0x880380145503403880e00d621990481444030440d8820342d44a101c101d44039500b0b450400c2c001c44400b009401c00c80d0b0300c5000003450903e0000c0711140711300601108281041d40328100e01d00352101074911a044030b5607004bc0790b50381c0040070105070f034014400c2440c02201c41e41c42c0041c001c0034051000c50380101f6400640b0070080e10305440090804da07001583c1020103030035019001c810103010024140d01d10b040004aa00d403e0010112020036900042520201b4014060079003104007510843d0f031500300e80707480701d9501c0c41420010392140040d940041c002c0100000c0c08102e2121690768902c4108503160340d1500380d0800070342200d14406600340404c490710244905842991704030541082c82c20050240a641401030300002c046402c08660321502580005540340303445d02e6142c0060f03517242208484160618500c036065440340c10344000c21581581500130714010840c0d20000c004060000c2400e0729403050304480c1c1c0d038103d0744600d42e40c0c0140d80030358054049100b82e42030220b4082d15050400f01110 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 773701151 1250 773699901 773699909
    0x6070b1e091614040209060a080118020a0e0d020420040905150a2702030408031e090c060310031e210e04020309010f05161b05060f090307050102120105040b0321070201030605030601 80
    0x1540c0200100808032001500c4600700bd6103400852030070b002d2001c000c00e00e10408541601900850070081b0464543d40d03c020010396841c8001c0425061840020400341d10074850743d60030905040100d503588000605201b036004004221000d074600c0d100014440c40380500003180d40c1c071146031040403000c2c0c1600003103120fa8424480e09580340740240d050180009601100c00d41c140080040140344480050413010001003291411340ba0741d03d11032560140c690507000189440c10054070010b5001200380c4403104c007031003541075601c080781c080c489101da408203d500c080055441110f8040d60304045d401150004586000810180e0180b54110183e500c203485403a00d89075103c05948001d43d0150030440000c62049102c010300c0b407641c48150361900042d2644008244090100300d10b400200704465040303510800039515039071651220076407010b09103d01805181003455081c0d19290100303030206442903d5020180e24400041d0050700c0b40c200c0ba40803030501d0340e2034002040c1580d0410002d4003c0c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 773702401 1250 773701151 773701157
    0x330a0e010606030b040c020a02210a0f060207031d0a030209180f0c03121201090b060403060f02041d040f03120f0e010c1b110f06070b1e091614040209060a 68
    0xc1c200c2001803101b1140107a10880454104085050040c0e0356060149203005290103000261107910454605003166030340c0040c1000071307028090041003999000380c2006030007516a04010050903c41414108501c3c292a038820f20035001440145081d00055030401a00000700f80c0185082c40858074104403041c40041d00d501080a0103014601040981d42108140c0b0303400d8101034440100c0006107a040c0240c0d640282c4070418455240c0720013050320002d540001c424071124500842540080d4000d014144001225590303540007000e0440409004540c49a0f0403c003580340c0b901c0c12603042c2c2100240b84e045980312006410102c103540580c1103100803178400003a203440c43e42000760036041a10b08010a91000c401d03d90003141c11081803c500600554079041c11000020000b901d074440c0b1032004080c00c50100c00d200c0000041c1204504e1440307821030240301a01d030100d1031a505c80400b40450b82100d078034401848181000b41a04005d558081c1002d81425092000187d103608081608000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 773703651 1250 773702401 773702411
    0x250e0d0c0302041a03030d0b121218011407030e040b061b010f050c040e0406020d02162303040614131d0109090c05060912010f0b03330a0e01060603 65
    0x150f14003441003035141c10307403107403040c0f10b8252600200e80ca0740030307d01c04040721903a580c5c1c07020300300d888030744c20150060f480c40c050b140c10201e405600d468030b8010181007030b40b40074400c0503200f0310350090714030100002c0c05150b12801c00303101d40d90807a0b4110720741072034540103500d400c80701c60755490324000b90000200311040c1e02c02d5040c000c1515400c50b49840d02100c2503505120a02907a0100c2c0740071542a501c0c1c0c40040c000030760303442c2042c2c00a4480d0506012000e84001440c1000a0100291003403091250354007035106441301c071059100101d859420344c07030b41e0420030040165a004901441c03045000c55103444c28061115100810340280d981b110008010300030062411417401442c56002d02032219041002d41181e4842c02d00d00c0000f405181d0080c880040c134961559601c1c600d1001d4066000e00038010f402c00502041e016140301000d10707000707200314030842a0103040702071042505081714070445101c51100c0c08250095901424410380141d4503800303d00a55001c0c024040038100c9600c0c0861 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 773704901 1250 773703651 773703653
    0x3090f0c03060403080f07022806140c03060609010e1302040f061e0809010f1a0a0501170a0c0507060603030806150711042301030b1e250e0d0c03 64
    0x10034180e60a041600c640c20000401c4002604030a089070048040c48060a003590f0312081070386000c03603089980503001007010440e03242c2c1424210141c80948107034000d021030201d0255010941794160790300000018180000748403410403401601121300145000d400803c4107a010910240070b07112079251b02900044c050102c1141412a403004142900c0c0100c44c40da01c00036123503a500550f403102c20400214401050405000750040e001c0501c002c2c0003003060b4010141400705400c2890a12030241c100400c0002e000c0d801642514020710b0030000703100542d500d004c0c2100c000d0040c610031600740203060000a000c501c1a00c40c41010350700c243c4030711200e4100f0320100300e02515141e41c08103002000704056800104220703640f8604590617100810390803030141103070b0314241402d010010102d0038600000240410040b07840e002e034006a0700001040038011094103954030458514035604401d007185c103900b025a210380602e944180c50007042c85964100058841011802d056803c2a841d41d4148 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 773706151 1250 773704901 773704903
    0x110114040f032d0b0411190905010506131406130f0e131e0309090c200d02060106050918090105090c03030301050a0e270601090f060e04080c100203090f 67
    0x785500041d200c000c10100d00f003050b607200501c0850006045541d1400498104801040500c0105400420f002099101e039038800110a0b09803241550690030240001054100b00088642100250016400c2d5500300000f40e100c02c1d101d40d96a51700000c0400400c1007000920a4800242458030b2042c0310442c9403112003100500c02611071341d0f403840500d81243c0014035180151003281044213180d5000710303541c1000c0c1d61103c0c07180e000080007404d2840d50303029190301c41e18080001d009540f0503c2d44280740341307003a42c2c0c509404110b140541c1c481c1005105160148015000f1503100602e41585c6000e4000d0b03000301c042c81600d004034070b0fa440b5420310403266014400a68000c10560040d421580342c0400101c16180c2c40c4101440000d41c0d4000c14080c4401c1e8200454030000802c50300450b4103902c140541d522024441c41ca683d41c03a000400c40c61840c0c90240d4000c980c0f5070310710060161110348032b03500c803984022a00170482c40760503007602c640c106034000745104800b21009411540c148800407 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 773707401 1250 773706151 773706173
    0x1050f2808061c120c08180a0b04030b01031b0302031905060a0b0a050d0303020c061e0703020f0405040b031c180b0c0601063b1e010903110114040f03 66
    0x8511841504403041d441c555140f100c0b202058010043c501c0c44409220241d070001212a40034045000c0000e074050400c0b034043d140140c4020581360594060b0343c40b01d007500c0c940150b000040c070f0b0004680c01000802e5100c400341a18200d80010700601da5600c0e800245010401641c507048544498401800e103d4144409988802c2d20481404040d00b01c4000038160b14450041c2403060568844403804e151195058600c0c0030800000c80787d9905040d44c82c418503084d46a04407510742400400103001c51f21a000396000d141020030001d0906081004105c042c0c4003003480943c051040d00c80390f131107124605c42c50006a000d541c45603414800400204201460140c1110b10700c00000c014000e81e5080c001841411588035183c4455014440500ba0040d400d4150060013104014522500318980c01081c80c1c43d583d01c21a802d060340040c043c0703400710302c841c05107449022820b2081e040011440c4d001c0b6890b40d00e003052514004110350345401c501242c01c82d420000031400c801d0004d01c1004010850 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 773708651 1250 773707401 773707411
    0x3040f0c06050c0d26130203191203200307080f0c09030606190803041401080a05090a0f050f121c02161b0b07051b0a080c01050f2808 59
    0x43c80c00c1481c40c07003c1d030380b151034003460f50412980400104d01d00400341c40900c000000000103500500700090300b104419010312050341300f4018288130b840c4032440c0a045284c1150b1164021071400002501a002490480180d01800d6003141c00d42419802600045204005a031a003042da400d101c03022880006008050400070002003185142590f000103a2590001d812510040d440a41d00440d941d40100c40d4004000f07071002142c007050703402d5003d5038150010300a80c0e07401e04907036030000c400044d9034042c0c4601145400810b000e27408030f500039107440802401641198441100c544100d813500c13010300c0d10070810400105205940c078104080045c00d42208400560501e011060400711b030f5105504014291000c041e80c414260400c100824001d08102d0b0722b80e0f85601a5040007a1910700b40d0b20707201607400464040505902d00f030a118000c0d600d400000f030482c44110001910107a00c00040202d04c49020700030001010700c02001c01e801481902140340041c031000001602500c80642 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 773709901 1250 773708651 773708657
    0x170309210c01050306030304033f1d0d06050402042c0c03060702062205060c250c17070906080a0b070f021b0105191d010e030606010305060a0b03040f0c06 68
    0x1446002d540007c01d44003620f0708000c011940e00c103284000b88030200707103495200035948001403951000a030824011408902d546a090215a94100d00703810340d04505600d0340e00100041d14100802e00d2540182d0380b240c4090310008030800c0316a0740d520f03035003a840c00700d60410000e0b001b421100002400030603541c01c0150002c06040c1481030010b511044000d24507035070034a0b00d24801c4108240300413510101c0b41c1200036581c060a291078201c001d0b50011600070508081400c06041c80c0c44101c428882650b0044040f683c890f0414641c60720a11040c54108558441d602011852008074860389004180c900c00a01d108105031230210b9826000918a00c03d001024511502c0ea039008130390180410002003107560024908401a94140681040458070407010030421080c55003105034500c80902e80c401c0321090f0001c88004407900d4030380302406905900704601103500c42d402038220b00e400a00040c0240c0100703849804014403600200c900f5a01c0c5a14826403d00340481e04070000090701d0286 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 773711151 1250 773709901 773709907
    0xf032c030114161b17031b0c061f0503060118050c0a0801050d02211f020708120a020705030c0a060507141605030c0d030f050903040609170309210c0105 67
    0x3d01403001c0300700c0c00d0966200780424605841a44031041c15880c691340c0d8408212135000b00421000d80186d0011180b20616189a9004640002000d016200700380c4042c0c00038412642e0344102441a00da1640810071045003585000c500b070741d000d000c0c45000c0d018800080c8248031411004500b640d2001d86010442031040080c4041168040b0925041d6881903908804605181c40490b0030b00420305044503461110700401040940c0211b5801c3c0000444102603c20000d02c855a904904c18001c000b0b01000040000300da500c0c002180301a0b008002c0c0800600301103454035102c0c110361080c203d10320aa0020809401000078500c2a941c000c482440c122070320040d030b46a4408680b00305661240c02c400101c04101c1001000c0040340d00e400204000c0d1120341c0c0d0b200c60302502400b100c5100101ca0f42c100400100044c50000940c1c0445085075140ca5800349000090000c0012400d000f1200740000c01405d04c264a4819154844a04c42016042d110300d000030780034240340c1c4005006040017820 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 773712401 1250 773711151 773711161
    0x1d01050708090307080c10020304110a0906181509021317010b010c02010806030a051b151201030f0503070611040503100509340306150905040206070f032c030114 71
    0x3c01c0e50566544400803556806070742c80034030724001294440310280d0340004100400c05c805840f88100c001c00a480c611503c607122040b001c191404d6000b80c100c0c401048081400c1016550005182d600c1c880c041040203d858055110580e0310101c90719404003443c1074100100c04002502c1d80440b10640000c00c00c04c201400000d040d141c41380d0303001e0304110400e00030421311390703050145001d02681b110881e400c0742d45c040b004404080001c0c640074402c021203a20503100c826103800b01c03600504118483d1341035a095071348068500c0511001555144828420840001c0c140c5c800d06a8001c28a401d00751942d15200030107242c1125091079421303150801c41404810700c4000b417000501d0181c00444548a40c42c645116801c401c0c01200300c1c0700000d041400024081250f0010100408401100803990f841c3d00b140d01c156041528003c0d0440d804101c01400701c0d9004162503942482858010b4039001d040c4510440540007040741004c00c4414070341c4c05c07690b00d002d01c07440f60080c0840e06503188525103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 773713651 1250 773712401 773712403
    0xb030f071203050a031404050d030b0103052512181203021306050c030c1b10080403080c07080904050907060305010f03150b01030207020d080a0306271e1d0105070809 73
    0x11560000c090140200340a0130041c041c1e086100c141800c01c8818181d850141080f550f01e03250709584034003103841e244022045520a0150310f10610303080c0b20043d64030704145010f00d1840c11a00c0075100300500350005400c1c20200317004440c420320001c011100d016401e810440c04104e080c00c00c107800c0c180b0420a8109206215001c101100e2041c10b01c640c68928814003070341140325040a080720390242d0407130003180e421940c10801c07800308191a0300640d8410804c05441202c5c003910040c001c01c04070303000225000c80007c01451194841c55442e0306000d0844042025202d0695105007190407948061001c154184501801004000c032140b00d01c900c5d589078100c0d82c8550b83c0003e0300c2644c4451a02109900a4048030007180d8041c212a2150f038450501102c903400040d10000001d00304a400207410140015024100c1d10f80070129618040400b005002000c80300040c01001415036420003d25040384514550445050300000801c0c43c1c0242070340c21640d000340b810301448102c2042c4045094 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 773714901 1250 773713651 773713679
    0x6150703020c04110d0f151409010b030a06091416020606060d0207050f06041a0106090e06040914160617090a150204050d06020d1a03031801110f010b030f07 69
    0x10080d100050382001c3c402140c5007a01c540030780c601d50a814191039000c50a104d40c0f01f0030208007600d15002030703141c03600b212301000d01c0001c1903940d02603002d20052000301c100308001d540007035000c1c0c40001c0b590741e01d4030f52206882d078401007210042140c1c000c01000c0f04081c40749202280c3c06202605a0b407a01c1c900055850048041420040d540480d4402c00c00c48100304180000e507000341140c9807071800d4070700007010011100c00c0c400c000b401c0d0380000480a009800c80019900d2181c1004451350b25182848011b11035807030281d810039803000410140c03c0b0700f40070564070144181152007205041070340107020010209911604030240c8020010150740205140c4210395110145504581481e01114080d0007503070042070380440e20501070700c101b00141e80100581029180e0500c40b568480c0904281074505007003081e09500100300e110071042010316041c03e0444141002c0c488600350780701007450319005902c80c842c1695201090300951408000f8003160b03290620061030024241411130190350 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 773716151 1250 773714901 773714923
    0x6060206011202010c050115151e0e03100504060203071b08030a0c110303070e01080105180402060f1b03030603120307021203071e031e0b0d12030905030705060615070302 75
    0x340910103540031a845001e000501700e070403c0003801204100c049640520501c5d101d510f011501d06000503038568040c0c002c1070750b1036065420098041d0b01003a401d840c20424109a5940b6000301e509800cc00c0c440b03849800d020b213008030707001a26490a4031001e48048400c65400340d0b80f540e814040d0700000d050310212680f10340701c40c40101d90210035603001da5100040307141c01d6070a0f001c00720170840125400569a05006c009030380c0d00c0c0d0740d43d03138a000380400844240c02006aa10b1658000740c00b42c14940c00800202101000c0a4034145c0c1901c0e610047d1661004001000c0e0000011300c00302d440c0411650010205c600415480e40c140014013030b41c1d6400c0c04610a94150380440040d4049005182c10150851150080600b811001c6c80080042c12011011240c43c01d44035030003011074505c0c0c800c24204220191000501d42c100e0f884200c0200e075080106c0c4105900ca0030b0031400608144060f002092182c001408542040402c0040385200351101e044142c07024001d20b0040b9030300141100c105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 773717401 1250 773716151 773716169
    0x606090402060702062d160f0c0503071d16021c0203160303091103010b030d0e01020a08220f05031e0c0a03080c07060216170c030f0d09050f060306010513270c030606020601 76
    0x72100a141c0951101c400754130036641402032800c00282034637260388080103402c42a444081d150f5506c9014806640080c400000580c410b415000c44894480f00c6211001c10070b004803414020b80307844031200303101c1d003a00460000b5250304100c0e04100c1224103100803d0b408600034092544000c0100b5500d41440640d101002401510446664000c2c00300200103071300f00f4103440d5200c12403403561300202c1d41d0300c2c0b203c1110110502c0000352410f82c081d021055400007009440c1c000a0700407805d00f8003c00f13500d0702c0d100303016043c101d58450780c0312a07009006502c03a080050b111212281e0140c1003a1060344803030305540204159225007032000d4107407800c3d10314051a1044481d40f07005400d241c07561142d0002c1d09031007442d10f0b048000f60005861241d40803503582d200c04c0d582e00d4800f48509002c680c070400d90000d00500110710310358003c101030210408030100a203800f940d9444240900000c032112000301448618404040d22118001c0440403005405c01f4001d017407134158003d6580c0014030810f034a13 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 773718651 1250 773717401 773717423
    0x70f0209100905071e02060105010e150f0c160f060e0d030507020312041a0c1002030c0c030f0406030c0318030302180a0e0f0610020606090402060702062d16 69
    0x11540100000c050044080c08024074a007210002c3c0403540171141100b0252051240312840398400100e0a0581d40182e66032440d602c6510203100c0142030181080e00c0c0c0c40790078440401c410007980064800400114021b008110107541d400001003882d80081071090384140003402041e40100340d210810030140c0e04505044581d05044406000781d0100075854060303c0400841906540060020349200c10720908000c0090340441c080741c41007040580041e000070310010f070301c80405c6d4055036100d01003803203040c034000030701d046e003821544038602d140e0084002240c18440355a06100c0c82101003600e050421032a40e45000d500090540d070b0400408041e0009070300e9150104444642208c42d1001c1c0030300c141079480c0c131604450844201da40c002d50101e014006000d61038a0701d504100520240c0203025030b5104c101c14001ca018004000f44d801020400c219001a21940c0050010f26000c442c150110505445900d440c805440c8c1c40380000ca02c01c0c0008801c00381989025015140c0c0402c0340c42c9 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 773719901 1250 773718651 773718661
    0x70e090610180b0d031716080c07021903050703050c04050103020607021e0a080c0f010f050a23040305031207142d040308071e030818070f090b011202070f0209 70
    0x64400f103105250005a03041c02a0308250b00000c2104165200403c2d26803280d80701c041c0b07500d0000501904500107800c00001c2039510040e0f100401c0014000b030b01a403100384440c8108410400c40343d004542942c0b02c03a40030003e000c1c0034070225041c00412201803109514503000030344c45d07009505010f8810425081e000410040d401066502c40030090b01e0782c00016590fa0071291144004640980a100f51482041032984111803032201c1801d240c40780303030410003510000c42d03c201100254200c140c200c1074511030030002460240009602c0303600119501d02280008080e900c0025010b001441002d910745d0a00d00115400da6645010b08003041c0c0d18444a144600000c81034444101c42c03240700020003009200c2050018403400f8018051030b0115080000d4014101c420041e002d0300207120200441c0c003802000c40d0055280c044c03002142e80c25a1180c041c20109042503000f49042036407058040d18070750300258420102c00043c6c00c01c40c1020590b41ba000512460103e000f40f0070364643d400a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 773721151 1250 773719901 773719949
    0x232415133b010b09190b04021303060b010f2003040513050106090b120403030b2701080705040207051b01090e0702070906171c0c14070e090610 63
    0x30307880059034010001c401c9914041030180c03a11020988491800080300d8010707105018000240001078050483d41d0348410110909882d101588280310b6101d40244403940c1c2c80380050324186010304040e91850f40340d80f83c000e00711180500113074140302201a0200d441d907000300074484201224542042e0384040381c032140741544610741080380e100c48051410016136940d0f0f800b0302d050398041d1300c43c011140d4943d84000c10070300a0083c40101a4460300c006400a032094002540f1507101400010300d80c403c40d800c2d4986010f04081030421200c1c41e5004000c3d1060801500c00209001c0d81e0462820b10a40c0b82c05440d101c00122600c00040c0008040b03a459101c0c603040001080000f0710030103181050382c4025251543c505c07403200c0560501c2002b00704107260310148d05800c10441d0003000582ca005029000055016032190140413000d001240481d1051511008041c0a880074005503420302e00c118806160141c1441c20950086041000380c2c01485108015913480908244013081030210f48 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 773722401 1250 773721151 773721161
    0x819020d060302030703050d02120f161a0405010f1d190804030c03060c2303160311040e0f09070501140d090c080a060e011802010c23241513 62
    0x2134041c480e5200000a000380815940d25a800503400d07100c600300c8010810086000e5400d10090794202001a03482c528101200c5e035050520030071440194180481044481500480d800c0e11b080e511001e00310001c0c1c006c0c1c402d55621000140c41c480b008440d803019580d80c0d80780341c13440444804610501d20180032a08003607030000c651041c2c07907145450700d80ca4103e0240c180301e100c100103c0d118180900c507110f540c071041e142d02070200840b40d0a60b981c0300c81210104041101308024195600d4200c0c5014504034010406004603202c01c0e0301c90708000c00f02d0003803104001c0164030b00f80c005207800e00481c2c0e4050324070b04280c0c0c3c175072681c0354891070b417904284014010004001d00c2e007100030078000345118002c07801d40500b9004680400020000014881c02d8414540d02620403171440c105041c01580181c1001924902039152807044030240085c5d0542d540b0545007140c1150b204100d4142c03030084980000503c0044020084140e042100f0900c003da6045100503110701c02200780b44404400690003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 773723651 1250 773722401 773722403
    0x203030304080d060b1c0c0306080f030414120c06180301051510020d0e010c060612050a0c080a030503011703070f030e01020f070f0504150e010e01150819020d0603 72
    0x9690340c03400c09103016241030740729445800c3c0d0341c1c1c00c10000080882081342903482404c1c0d80300c0c0b040d88001040d103d910081c442c029080003890740c0d40e44046a0000b08010161388604c5181c001c41d540c41c10844092020b80c0d50781080c52240020068412040f407003c107502960000c1500c002c0d403141034000340100c800c001808215010341c80e00040100300071029450702008242035501124035444007204076100c107029850800800c5803001c0740d40455104124400b0790364000c02d0005038490303c4120140f6400f0040c1402d0303c5650010102d8410b101c07801c4545402443d04500401c443c6410f43d07400340443c00144a07542c4060407100d20440c0660f8241300b00d40d8039942c460080380800c29035207009070009600302c0c5d40c2030062040554100b4800c0d00000c803001950441c1c03410035083d40c40d02007080040d004900c80b041199000c400300003484e480c600001400380044600c2c0801540c1401280b00a800152040c3300401c0410018410360740c859801060081c0b0b5440400b5a8610003d45500c01900395540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 773724901 1250 773723651 773723653
    0xc030a080703211505030c0a21020d150c02030c0a030804020d0f030914060a20011118030d030c2f03040902190c020112051513020703080c1c0b06070203 67
    0x183c0e049200c00558001807100341144070520450761104217060783da12452180c00d42012440d04e05210f5802c0512071030800360800300c40180d03032200e02d070701103240c0014220040340c1d8009030011249942c1441c0c058000e496070305100039030414a400b1200d55854520000c06400c1c0640350000c40c00355103810240b030010301d130010b401c08051112840c0003020008207101c0d03002c02e4400750510010074907200044400340034941d5500c81d09030700c190b0b000803400787c0d0b10f00d0352a8240d035a13044116060300c0408003801329110104c407038a4ac4840e607001031604040d21f1109510426241074002151107400405e90465000b0382c00e00c10012240400030008000c4541501c06a2371102040004580107141c0003420110382101c421000c04016107001e171198038180c20002d010403a0140403135520030715075200961241c0c0c407480b6042c000c002e030b0000c60004644401300701009a000682c50381410380020700c0c1a08141400d00c0289066400136140b20a0034000740c0244032180c50328290100b541c0c40b04280c41103560024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 773726151 1250 773724901 773724947
    0x1c0f2d0503030a0605061603050d090b04140f012703031d0c01030b09010b1204061811240a050c073503030105030a0206030711070306050a0e0c030a080703 68
    0x1003002a035903003040390701e0494181012400b10340350420109803808020f03c403810842c04001e640d420390325900710002d40c0c810381c1d80d01d0f91018081580c84021a010303601465036003003210b08254201e410040ca07144208680c0e8104104080b140340340b403031070030324002e052107442c0c45145441c038046000d013000b19404a101641482c0041c4040070208921101c65801d88040004083c010148100301500b40300390000d0700d03002e00151441c4060b19401a1b84039120341d00009260340f001003262000c1d140d0500c207442800084900c0300c0b940c1031485208003c0304402c51055281305180c1112019031103401d844001300031012501c920180030412170720000d0142401480b109405550f01d10449041b0110303903244c41030408058440c184000700440c3d041e00d402038040c10440b445031f001d00003a0780c4003409401c104043c0c0212403000046c1400054050752003140045450704210840c002500d40c2c8200014040d00714903090b420b11350740000c0145042d0b41c441a141d885002e00d00341030316440c1c4440d0f140d408200840f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 773727401 1250 773726151 773726153
    0x120507030e011a0a05150c0706030501090e011b120e030c060702070b0403030212070c12031e020d080103020d080405060d020a0212070f060527030403021c0f2d 70
    0x9500504088206000200014060250307907000000c5191103d6400211102c42880141031800a00d01480e180000d460b113400940d0744460318000781d542c0140b000a40e18401880038200600500c40c8150845000740310140080380000d2044c0340941600d4140100c04140300502c8107690082e2984504a9080d0782c0c0f02c40303410030090b4036408219400300040c00740d800080340c103940d24400d80341640c0e0190700400c41c2c01e0400046009940c0f012a00340c07154400070324000345106e030400c40404542e220b41d0394419440100105060308202c0980b4840c00d540080b1005100d00d0f5100011a04483d0101d030341c0031400141e814540001e1089400c204d0b00540001030b421040c4c503894005015404160742210700d92510000d101d4210f0080d001c00601c4080050006404940c4c00d400043d0008000c0d210b40743c22154070300302c00204000503105103507103400c003040800a51070720055001d14800c40c805103213010707541a607412907240c80d0320b0741c01414003500307001c006a844000948a9203140d042e000c004401c0c3e0301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 773728651 1250 773727401 773727407
    0x901201501050a08060c030712090b0a09030e100e0f120a0b0405070f2303101508060a050f0f0714070b012612160b010b0901080a0b10030b01120507 65
    0x400d002d0315000d5611508001041c4e031001505905c1a003990b00d081c0c1c259112030704200c40300e100c0c1c0e20b140b1068545900039440802d441d11540c1d0b0003100750010028440301c292030050080481c0303000d01440307a03a0400203503403090741081050b41c408000711041c90510304800009568004030405c1d0080d64070800e04200c080002e01480075008601600803240100c0d5a55074810309210103000704060a15084d0429007041e80004490400c2c080c01419a03204044203000902200e160429414080102480810034140280002038005903402020f000034600040307140c0540d44094000580c0d00726070800244858801c1034840c0300f03508a0481d01c2e550380300a080c440000502030240860317103144400100d0b60111102c031601314502001c4054000041203000110041c0c0040ca4400c07100042c40c1c02070000180c01d20f109501a0500c10400781d10750350309a00042c0790500041031401c90b035181000a04a9039070304040085a034940e4a0003084410344a0012070b00240c0419240c40c1f03540c2000140521560 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 773729901 1250 773728651 773728693
    0x4020d06030b07032414060906070516051905091f1203121d15090c1201150b03010f15030e061005030c010f05030c0307090308070b0103061a06090120 66
    0x46441c1e2842c1d00305c0c50070001640031806612602e031125186240c40000d40c04d04a01030084d06000604050a018450712058240794840440d2250342c00030001c03d10052a02d02c0d20740a20784c0b002050205001c4c10200424640180904003442d80840d020701c01000340c2129202100be041204802072003040d0b9858044c04150a2112441c012800d0842112007402c408008591103004100144107918110030707a0340d50b010028041400c40e015004a07a0b00315100e0441c1402e0700145072000207805503070500546110311b0f0303a40020307000303031000c0004028484503040418162071400092000c9400d290710180d004009024951055001d06810800740c2140703400001c1c00c46d030064064a24240e070207001155204c0c420f042c0c502c0810710601c0425a400045000381d40e00c00c3c5a82400251a40c40e620380301000c0c0c110301c20484071004408014801c02c0710718001d6040b4154903e80388585080d0040c0055543e020b003481c0d0604000d850001074a4000901800c2d5001c52000c030103692500494120a1611203 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 773731151 1250 773729901 773729921
    0x1a0d0303020d050f04020f0d0501060f030506010e010609050306190b130525200a050f03130f1229160e0d0503032406030a020a0e01020705010e04020d06030b0703 71
    0xd0301d480c00050050005490f010b02c117aa000308104030303078180c410420504504a440944040d03607188808242098031079111409140104028034081d07242c1034110222000580000d002c000c041c46042046032070004140d5040303482070790003d41c4030007515409001031402264655210711125500388444074568803a5020380003442001550707107400e41d2100c0c50b840c403040307003180000c070355400140c42400301850110800300448103072007121105440e55803408000a0070000d081d000000c03200e101d0036404400000802c100d00081340202e140c0f01504082d00c40303480000c2d080c07540d004180300c050329074820700140c401881c161401c2e05003400040d40d501c840505c054800800c002100d00021864410100d020303895120005616680e00c02502c002081d110740101200c5014031840c404040e038686000c0c51041c1c007070300d20041e25280080c0001703025410501000c1e0564004440034007071a41e00c001146040d00c000d6901583c1ca40407d1010780061049c0c3c3c1c0042c0200c01c080d818008940d40c99003204485c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 773732401 1250 773731151 773731177
    0xf0b10080c041103130f05030c0d12050c09040f0f0c09080c0a0e0615070b07050d05130c03060c020a05030c1b06040e01030611090303030a0905060a02120105041a0d030302 75
    0x114010824002201c12404603040380c0351050000820b81c41c07400c8051a0002c3c4031b2102c03240040701b16500c0c40d2854100107880762082c0c000d03030160701c9070b030741c2c442114604112015402d010341e052842c8992120311540142030300640d00d490301000003408036040105044510720003001484002040188520760500841c010390141d03070041000c41c03804100c60800d4071000400c04c0c406d074680e0400c100e41e000c0d180840b40a002014403100020450138140ca6204461945030184e4451340007203018111b807401441140c2c40031100b50310101081100500c6001d4030750041c030003c0ea110304c00c0700a80c80d1201100c1c00800c40d10000855a0740543c0c00f01e40310601081d00120b0f40c005040c00340070003075a0b0141d0b0003070480140c000d00c010000300c0c91b15040201c2e526001c1401626011302000400d04690084501c0400d0700c0e12402400100003041210b01d0344500400c404500b0031781403400c503c030440b40621880c1d00c141d031603590816162032104d038140c20040005096031152246460701401a400c41e015451f54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 773733651 1250 773732401 773732413
    0x902041b020a020405160e240706051501090b0715150915050105070302030d0f0f0509010e12030601050414150415021903090b0a0306031e0213140606070f0b1008 71
    0x8924900081d040601450780c80746541c3c2c521001c144168100c10841005285c081910600a0b0480300b23030042500c14001d02c00842d0721726004025650750603110800e1070402000c12010000100203005440e086a4400703012030b074890b11071800c0d601900708030800c0003075101c0d50400003544048a912900c24040342d044a005a1039441c0015140c50080792000b03005038000b04600807140441d40d1003803603450030460001030f58005c0610789004640c005c0f80e2103413840c0c0d900c034034040240700100611002d01e86c591940d18070b1407170900002007040c0280c1c4110291940d41d8285e1001030b030744044142807100c15121119458942e600143c480101e10b2048290150198441819040039103071424402a6010f032504a00c4c2c9141c010500266806001034004060740c80c00c011000941c1e04080c0c0c04140040c8291301c086240324010130002c00c4287e00b00c150158039000c480c18801a0301310f0f025512600499a5a881c0c08250038103501c080b00702d54004000500310400c100488004035414002d03105503408071341c2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 773734901 1250 773733651 773733661
    0x1080f100b030d080c1215090f060109090902010210020c0604140705210313060302130504090c14120a0c061101020a0e2b081803070b0d0902041b020a020405 69
    0xc072000700c0c0d041d40c1c1540003c11100c02d824080c9000b20742082003000716031720304041d00f280011200800e8800c041c040c0d1141c407410300c0700d00d401150a03030080101840782815043c40720000e00321004910480c0e00c000c0d01c40d40010f0039a07000340324523a002071400009558501248440c075490305801c940498260001000400311820001402d8054480103840e6000c6840c00403110803135480581a8a00540f0041101d0070100300d6040040300105000e490140c0ca400f14030840e01d8020400c1d4000300c0c0a5494003074840c4c0419000d40405085a030140d80d1144030740b90240104031860700324980c0201501c41c1c0880c8ca000c21490540702c00480d03086944222070040040180c500740c0c03041c2c983c0d4100088009680081c140740003029640001203800128005180c0c0c60b0f00c196901503030301001e603010030012584d4610080c1183d0002407a040441c00b4103e014207002a10465000c2c40e01940a440d41e42c0024604540703a580c4040b80200350b0a21140041c1c01000f4025030364a02140200d01550030440811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 773736151 1250 773734901 773734933
    0x31205070606031b080601030b0a02131e080d0201021c0f0b18040204140603031e0d060b0c060618011e0518061002031602150d06080708010e0c01320301080f 69
    0x1d06130ba921027508010b43d101c41244c0b90194010010716a80c00d01032000000300c08544000031034000c501c00b0074410707210b40703080b20076400c25425045000642e40100320406400d001129524080c20f4240340004000c0b41c0c8200d201d009245100e49980c01003054040041c2c05213100348410302c81e5200316004e20415034400031038a80003d0a403990758065000380503550b00343e8411030501d4250383c036001040f4144488426494141c62190744a031060381d200281c400725001c0280321030703944803000307480c442c1c1c0112070410000c5840300b0501c2074000b1a107501c22030003c81c240d14903113200280b034028220b00f41c9003c03000f210320f1160800d03284588900da01c1100c1e02d4642c2e00201c10b40b40d449014101d80c0300360040707039005e100e9a52075483d5010f400f51000c1102c00303c0d5401900c160700181224074002c1c0340341810944100e0131a8444000c1604607031210b031414903642e034042c02ca02040104400120103450020800c400c04114240c50b41072050f8001c00040759440000666082c26003120b021141103103000c0c4103103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 773737401 1250 773736151 773736163
    0x50c0c04151a070b010e09250905150105043308010e250c02040f090506040b13080904180605070e04141506030709080d0c060609050f01031205070606031b08 69
    0x5101c2410704c00104460600203100590103a103540a035a02d42c40100d0140c8600c41c0078490304620042040b0041c070a99406201e0280d004005d415020003080400380060220f014500c900300348281d4001a019138034501003090240028660b9100003c5c03a52000c0203041c018090140c049010a281d0000d14000c44c0744078001d00141d10841403038074004a0540480d07420f0350901041e6000f6440350501402c489541c458410414003070313805450b4900b4980742c4800c4602028280110801c3d64104460101e6280740413120480403c076400a0008408002052030554100303015000a150404000c1440d8000c03c6400808070b003102e041010f2402050889500e00301580c0704aa80c14044500031024200140255003014540c10091603c66440461030314028540007001c0c0026612058602007010754010780e00605246032060103a840c0808250f2004501403001800c0c03c50040d814403c901e0042007110995500004113101309600ea040c10402d4800042140181c2c0c41c4076000000e4260380801c036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 773738651 1250 773737401 773737403
    0x7020d0f020607120f02090a030f02090105101205130209160909090818060f0708090906060414010c03141201080c0d0f0f0c0b0a0206070f0f050703050c0c04151a07 72
    0xd00d1001400254130800a007000c1c140d82c0101035003000504100e58804540034015840380d00c143e000a9081e01c10b10040e2035040c1d12444c024401c00d0019101c00c0d800190038086500b010320002003990300d065455244100f421380103904160404140207009016110942109000d82c07100e011321542c8410b00ca0864180d888054100d82007404078200c0d828040e02d00000341c0e400181494103088034200c1c440c40c0b07540f14050490380341000281280540c20050078071751780702d0000ca40090a142c9890b40e440d50a803a0706401c0e9041100c4c078460f890401d0f00900d000400314a1005649458462101c4015140070087c010200144143c030100c144901d860000740e41001e600224607003495045585089450a03100c2007140c02043d1400046407505803038015184480059000788101d0524107409004c0c10f0100107034a04000d003549868060941020884c0c1040e54940b40aa58561000c0400c03070401c80280400c0b5409400d0038000101040d502c42c80405403082c581d000300e60003881d0580d400321881001c1c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 773739901 1250 773738651 773738657
    0x90912031104081b0d0c0e04050d03060332030301060921030f0f030605031501090e0a02060a0c08121e070503010806010504270c08240a0902120607020d0f020607 71
    0x1a007090540300e00c0c4180144d0741c3c0505a01c1707000081d43d03160001d1103904d401c076560b035207182c00c1000207112040000c5200c018213400e040080b6070542e19075201d40c0510400b0300c00324602d04030500d181d5100c0101c6000c400c1c40c0d83c3c07040e40d07100c1d41c40d05001064003000748149515044040341d12042403c841e00549280ca9050320740002001c64808142c50009081c0300e400305040d170b03440001071b042d28180190b1f0f050850701c0f11914460360406c0c0c104400c640340203001c190198000d2000d01c0060b00c8540842d01c04986071700388902001c0040c078010040e0301c20840c115120300750040c01e2052071210030700582031210000c120b905441d6181c4c14122000c4c0024413810701d040d840f04004000c07900705980801141d08401454101180f80040c5814800407580c004850700c441c04001000146002c0c880b070781c412035100301c4c545c620300c3c002c0340400c90b000005040042d85e01d90710707203601c0d045543d203c14501889250000b5504103203094078010303450324030b0720744540c0210714a07440200c41c1510104800c0d10460942d1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 773741007 1106 773739901 773739913
    0xf300a0605041d07050108190e06040308070215010501051303080a0c03020d1b02040b030717010e100b030a030c031211040911070b0c031009091203110408 68
    0x80201e040d4160b0803d18001c000341c04074800b401c4440902e440f5030903845940e40d449021b0170b0075584030348580c82c0500e402441e0402003101b9215900946a1400ca039503000401e0381c5030450b6900b00d0318805002ca005101c2980104040d01006000d10b41d0b40030f0044c3c8990b56418a503020644050202d00c00301c3c90f400415074100300c032682e040e0052502000700e52940e603485a14842d00c88000307210b1601c0c0c900301d0700741d91010803041004000078044501c03e0102c07081000d00902e00d101140b4050b0240c4148400b41c84000d000e0048c0348100030b030062500029980b0104c51541d03e0b66011005c010784441444001030680c0205050114503040d041d0390340d40340c403413844126150841d0219842105100c4000410310118085500403007910aa130ba40743e075080046020f4804542000c0001480c1c00c000c04c042c80484540b0341c400d640715440030072034450350391a140720b98011071182c444140c1c880 = true := by decide +kernel

theorem cover : BRFrame.Cov 773561151 773741007 := by
  have h0 := BRFrame.cov_init 773561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 773561151 ≤ n) (h2 : n < 773741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
