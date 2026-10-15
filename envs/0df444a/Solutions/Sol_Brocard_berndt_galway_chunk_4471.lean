-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4471
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:43:21.73498+00:00
-- url     : https://prove2.me/submissions/e159f7a8-090c-447a-b7d5-4a302a38e301

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 803956834 ≤ n < 804136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 803958084 1250 803956834 803956849
    0x1080105010e0310020d09020a080c0126060415030609060f24120f050601080309180610030e0c061c0b0301140708062403041a010501020c010305270304080c 69
    0x144a43c10b4210540d5240c9600703a035801400102c801c00000705104017107400007029100540c5c41240c0981144440e46a1980d00c0028006001500380100d40d00c2d04080740c0510b020400107140c0e60045d40e464055045098404007050010340d8071035010f0142c60800c6c80c0c2030010300190b21105e4005401d001e900d54404c00042002c03031600c649132101d041c0380d0740ba01c00401c1e215910301c00140c603114118a24500462004d0180902030078201d4019951044001b013400650b440e200c82c81031240402d0418003d8503034807050540c2041131f884c5000305d40d140c10a02540e0500340e00b0150386910a0000840d4004080702d83c010f900c0303069004034200706114009050609880c00041c441d400149070380c0001e60382d64040c0303001c03c0d00520068022015201c1d03186800944000d0000c030b80128a101004100801c1002400b0031044100c03400750b1001c9500d4000003035558040f4551003414152070700c0008440c05c800b8000e89901002088414143d4849585d0254881d8018000e8115a024403070405815040a00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 803959334 1250 803958084 803958107
    0xf0c020d12090203030c1e0d0905090a0608010c120608011104030b0c0c0703030509030f1203011a0c0d180905060d020f010c050604030e1002160e071103040e060108010501 75
    0x100030303101040019400321000d01460384a0764815540340d10742005601d040000d010143c1c0510001c10303500d500a1007080d44000491001c42440d8044010b0700710b881e0b40a05560210341e010764112155403264266407015041c181c0003941250710b4201d5002076180c0c8001c01c48240164440104420358407648101d01f0380310308059803807202c0d0040004100064040c500240d106005901040c05c0040b40c0101c1d41c201038440e0b00c19400a903003c41d2855a034a000e00100c5440303581c8500914410010081c0d014803404140b04c2c115000c90200c15521504500f6421640208140300030384034144400348002c2c0440c0c0b4448942c2e49140d0b1040004103078000188242405030308003c000003010001075003000340c01e490241d0340360704000040c0180d00028108000f04d6010354843d41312026002c1010084c441441402a113200455020060350091040c02c10ba41d00261625200030400341d690f055070503a118601c0032a000740038400054001102c500716440d031801034009030784004099030384400441d0b585c034816 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 803960584 1250 803959334 803959337
    0x280f0905090d0507020a0803130302131401091a12072d05100306211104060e1303090302090f090106120201020d3506030106051c1e170d0f0c 62
    0xb200100701240c050700c0035040b4a403005005c0c440c4203441d440f4041c19900035441d040b08001040302d090003180b80113090b103005242d0b034071003c20041c014549510034030130041c46021142641c4000ca000c0011031140c0c1e00c109040041d1aa03840800d4900d402552005144984611045c0c100340c7c2201c910300c81e45500310401201c4804100380ca0800741002420051055079000b456074441d00000d000300b11135210000f1000d00b010310034541100d1300b016181c08a0380c0e00703014410703032818030140103054101e91007640012401080940c05202072a0a440c291000d0b00082c2d0311428100030408815258040c251003410110000e101803655420082c1a01c0100d143c0203015030481448803c0d4070f8421b86962a0780b1189819100d1070540e10314010381210104030f0a100b00349010010040c0c2030900b40100c1b0001d100c1a15201c1203101c0000ba191200301401c40001e00010a103850310b2107000c1c2c0c00c01010040d0380c000501e034050b1a940d84407942c580d440040e49502090901c8200301c1c25038554402d044079503025 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 803961834 1250 803960584 803960593
    0xc1b1a09010207150f0e01050a020d1b0c180612080f030702011e1a09040305071b03060f0c17040206040b0c0a080c010905210f09280f090509 62
    0x81021094140c00c900300090451203108030020342d1840b1408502440000764681d03900f40003501900400896084c0102d6050006c10065407055550010b0700d218035604a2400c0c000b0300c00c03400b0146a11810001002e1b24441450002051400c212180c00c4090070101c4000c01006903101c2c2040d08003540003401030003207070045c011000344039200002503900608503c00007686907103440d80070741401c54040b49048402e50f00d20360740e213012000d0190402542d0044403d03c1a510b09aa4024001e00c40c140b801002074001d00c0380d084180c2d4842010401540d03007c603003130104070801207100d0003c18400324407000292001c64880b04040700907404502a50700504058070386810050703045615031220403202c2080c0300c1c408004020803240c801500110304080000b0401d0811401d2482c50843c8c0d12840f0044404d026504c0941025a24100c5807200001d0243c6902c41214000081c100100480303180d5807413811010800441d0852110082500c0740f001c4078081058864141404450040b5404070080e1301c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 803963084 1250 803961834 803961869
    0x903220303210b0307240216050f030709050130050c01260a0204140316060c1502130e1b0706051308210114030607030507110d0c1b 58
    0x20382c2507806001612040c00410346640d03280c0400d20700802c03540700c010345c0341d02c98514881955554242058401092005000c0c000c2d030354155000c941e215100b0307181b05106004d00e03400e80e92008c0c0921002800c01460800c8103603074400340a2000112205a1340702202d5500244400d000f0040107140e01e150400c0007000c0484c200c4d0010749000c040d01d0709200641d07450b807003081074181c2210641e6204540494000d41c4442c900a9290b1109070380c807907064440d411281100d4019402c410041d0b040310b11514000828541c282041042c0050101034800210300008100e038001012002c00c008071540382103000311595911a00180c45002042030030713074198003000a207001c2075094214582000d0302c0914902d18000564880c500e0b03a000907058007402d01c1402d4002c010003c01c102042c01481c010789051120900d0200003503c5281c01080c0d4002c3c5940c1c0c4000c201004d200c0d1040c90b55040c1200100c2c0c0e000740c440140606803081c51031044400303a400200004001001e013000c00c0407900424040640d111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 803964334 1250 803963084 803963117
    0xd0c050a110a1206020c0706021908070305040f240516060213170607110d21270519051207030e0904120f09060e06130801050903220303 60
    0x1092040c002d501c940a4000441c80c1c00e42503a480b0016441a600141d403400f00b07207403040c10908150300810554101c10900c5010120900c829030070680c0c06072180396200410301d030950340750007680c00c0022481500c500108400f410f41c6401254140c070b124a400320754902980c01c465074891158001c2285403410050400108030b90060558407841a20f800080354544000c1001141e46109510841c2c1c840c3c0309100c40ca94124414000070001880076200340002d1110103031031124558941d0f21902c580383c004521140d01da0f8000b80005000f0a4044001240c0c020007860005150380280c4a50291140352091078003800d00300c01400f98401c0140c0680401d0b440700810700d41003904c040d000d000e1100d801c0f04a82d500c0d040802d200d076101d0612060082a078100040488210700d0140c0280040481f06006281d0824804400001c0403102242c1d19240e2004001e8440c495078442d0040e50300b07110034010b01050102c00307000803400c0505408008210580d050400e41326901c0040c1c007003030f1203003210569030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 803965584 1250 803964334 803964353
    0x206090f03190903022814061209241803040f05040506130906060e06190519123c06090c030515040b0a020a171b030f04050d0c050a 58
    0x480b541403051030b0070383c1c0707030040384443c2003007400440d8003035003a20710040c0030340440d030204003a0004a2901c4030300489030380482d07040d00c02c0100c140c9400d110b80c000929080b404000c149001407810900c580f03030f801c216030130300d082d9102070342c1d80840071000e1603068619400c0041600d00b10303801c42c1203c0380d40500d0042407000030301024004d59000345005610071400302150050800300c030b20400b0005041884c0040484a0300b04c0640440d2050485504500a030f801c01c510090654608803103010a040c4a464515100c603080d90185d000110311507a0071052040000d00b500141c4030100800d8003003045828004280030360407052003402c280405441005c00d4043d4031255812784100300e580751582d12901e4441c42e04503400e15a2203580c0c0c0398800c01003040320411410b0340200440324151b0600c48240805041080301416800d990000240061302c1900300b00d800301d200750369100000c2e6590030030000004020908070f8003034801d84209001d8000c810f11540c1d140703240c1c1d5000350243c440e410495130303130b800507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 803966834 1250 803965584 803965627
    0x80105090a151d060105090609040b0406090e010b120a030c140a15020d0c031503031d101808030f04050d020301060801050703091a06010f180e01150206090f03 70
    0x401d542c400000c651006082c0c8501c2c05003407040d0542040306116110030b240c5010050915042002c188401600790700d900c3c0548115440480c1c000c074612103400040b8000b40381a40c80082498217004402c0182101940300407002c520a64000500c20030100752030780e907094034003002400103040c0032890000c945180703664000b0701e00520586021901a44600d4644a03809000c80315259000507141c050011501c030700402031b549810b051102118404003c801103049101c05010300c00130101030a039850b070b580d8459042c480c0042c03008904640342d0000401a01c000e01c80d101404a4a540102e00c07400b001043c0d81050f0341142025147c41d00782014442d11035603180c4200d07010b40d21004041603088083c040c145c82440242c2d07000803a2100ca0030100c00400d2501d90a41d81c140120060119690703001506040c48000c9041035500d001c43c800d01442502c9481e0700001903008140300102c2c80904422080d40380b10303d01d0707084882627242c11340318075100d00c181d4103400030170741c41082406201140e008600c041c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 803968084 1250 803966834 803966851
    0xc060f020c24072601090c080907030206041509030f050102130806040b040f0201110a0501020903190203070608070c0507080c10030c0206070807020703170a0201060b0a0e0f04022a0106050301090308010509 90
    0x8203948141c1e401c413541c48083e0442c865107074032011791b0038105a2100d12144d000304014003c280c040e180d41c021403064130560243d08034500508407159416406401003e0045900a0700200490003900301f040c000d42000d1242c1e4184010150300050b9020b000503203130f000c0d581003400360800344c40b036039602d0800110b8018228144450580e800ca1050130a001807104c1d58007400c005aa82c0c1e441c2c2080508014050b0000190100c0041c003540258030001200400d9444508210000761640803055400c00040f460040081c441d203000443c0034600410121440d0806480341e41110a51040c15410340780503642c0800140c0c4008005a001440752603801c0c0c1000b41401034800440e2a52607281901640c80624144548005100c481031913091092000403e104000c0900740300000030001e0100d040502003521079090942489440d65a0f94100c40400342d806e03640d000364103860580c011040b255030100f28065460f205001034a41018018041c20583c1599030845c0c60382418100b0032401f2020300301c000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 803969334 1250 803968084 803968127
    0x3061609140f0d0c0302151614011b1107330509030106090509240c07051504030305040c050906210a05160e0c04240c060f020c2407 58
    0x94454403402003d440c060215525541d046005101c200240610f5000c90b0b0f820030000d00040e410704075030200645034003201c3e0792800714034164294050030345651142006003440b14964112604200050300040c040710584d1031a590740c40d40c46080040c00d5080e10100020400f000d010941e03d03580280e007071340c1c40342881820a4082000b0070b08417203c1d500400400341e540c02c284152840100a03c400709403020060440610001c0c0d0004504071014005a01011000c6000b408011090181906800c400c03114030707500c0c0c54a81401000f501083c0c4050720341d01524140404d060a01441c441d00c41c10000d01001090200b2940c8ac04020000c007491300d056029158605c80012420300640b100da03400c403c20840180e0a0410803040c0c1038000e084904a20740401c41000308140504a1464503810003505103041c5402d000c0c1550880701040008240390302c1c1c46042c03105910b00d640074203240320307026085628081d0050311180030f08409201654450b00e52600088d43c0a120b0141c1006c04400c2c1034a40 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 803970584 1250 803969334 803969359
    0x609190e100b03070c061e02131403010506030d0807050708030709060e0d020f010516020310061a03090d050702180702060108010c0c260f03190c080f040813051903020306160914 78
    0x1f0000c07608003d00c44120011a0701c02003242c080c0ca00040c3c030a00d0b00c00c4008100a0511200090350307560700e840304100340101040010483c1d4015000e40780340d0398101984940d05c1c58455401083c802c800d006050200e00c0812400520b410801454043e41e64050039141c00c1286001c015681031b0400305c2c3c141d10008070224180c0050300d040c410900c44c10034445001c1115820000310340c004854006010400c22018010044000400a6426070304c1c00d590400b03c0d5620018000329250740c9000d00380c030344040c44420609c0f51380ca6000074070360704030f43c03000008100302c02c00500f080381c404540820140c103041646040d10340c052406c210144d082521070070042c1c039100d00e003500b000d05034204031440720a9a41c84140c07203200d21846d000d04087c00c41a85413585241c503000340d82214898010700082c0076044086141c8032041c01c0740c030f000f001814006182e031181e4280d42c954041200c4560208900030300446002c00d01510303000d441170002c0840c07526180400f0741410b82070941c444035145156800000341b2440c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 803971834 1250 803970584 803970641
    0x7052407020f071413111224060721020606030606060a09050907050412030c0b181009021903112821060f02092407020609190e100b03070c06 62
    0x461b8178140c1c035001015110040d50540304000c0c14000c00c2101c00d010a041c00950004138000e0602c0602021140281c450100741000c004e6400c0c1c010030500c266029520391840c95400141c000e128100c11400ca400d181e440c14180000c500440c036445000c5a01500107204610b084084203620508e00e1400a061070361740c6c3c41e4401c50120b02501070340070844a2a650041c010851880c40e03024100e039458070359441940001c21360300c020302800540c410742d076400318504641e6084050a115640c042c4034490140e100d090680d0300a058440d81446040f020342035029180d000c614407001002c0c032075185a00702e860054001100c1209042e072001080354982200b00040352440b03480d0300d00f0120000142c841d82c821040c1700c0c40c88666220000101c5d000343d4900c6002c3c200008a039100c0358103582464440603950040707138120b0f030302414407181896000b20105510150100c100c0c4100744010a250f0b00f03543c0c41440b03401e2440300f50342c0c0c000040c80002801c00452400e8010724041c03486000e0400651081000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 803973084 1250 803971834 803971841
    0x2210c1903090f050a1401111312060b03100b131a0613080d0903050c192c040308091b03061311130c030b0a18050402010507052407020f071413 63
    0x90481c6c540070100c004805480c4248650740307913105c0c1001c556181c0003203555035103c1004d00b40300d00000051010b04640800801750400d0700c11080c00350071182c0c1c502155014101a040c1003102a0050343c0350406469101400d01451701402c11804225001004100c00d200240c2e1186262501408000c0c00000f04803004000d10800d1b0925551030350302150443c903146080c8000c4000c243d102e90850b0600d20681405ea040440842f02c0c00040e0000d4207070304020340740040403004221041c0c00c2140003000b06158000c02c100e44a0368081e0152428050120b110302d100300e00744600d1a030550301281c0010060011640707085512402900f070102084120790000d02c0d40120120706824098a415804295a030140540c0700341c103008881910b03a035410a4108480c480c0c00c050043d20150725a4045015640100d08551b00e00c4d030800107842d81001c4200d4400448075803039002d681c8003a1154005403110340301244501c14040c89601a080b05441c0040004ad6501c250f0441584258407001d0740111000510 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 803974334 1250 803973084 803973103
    0x708061804051e0607120c090e040b040201091d06060706060510113915030c0301150824030f03041806090603150507090902210c1903090f05 62
    0x81c0200f100307005002c2d01d50140700700110750400c154042c405005006800448184500c0a07100b000158090501c1c0c0490300080c040c2e118041044491090100784004601a54803a0f4000e880340c000596648400c61002134580c01446c0ca0311907214003103856841d045000700110360103040c02250150b00c540025841c1c40c00360341c5100100d580c0041601407a00180070300e84421800700f900f91030903442d00d41080e4500c20818080d0b4420410403c8000143d40e0b8020000942e40107072a5407034a80c41d081c08409110350080c05013440281006814900c1244134040d402c3c03050a03600030344a0143c0c2011a15034072030b2012003220b5807601407004805540c20080015000038036640d0035490500d2568900b400813104140c0050303400d281080b1041c00421042440741000318003460707002500b0740d1680421a0446403640095002ea40001039620118180c010543c0c40c412044801c0243c0d912400004c05a41c03180107414407404440c0f0118403100b074043d5005404444c01002c1c0d13281512950391340c003410700c20b110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 803975584 1250 803974334 803974343
    0x4120611041202010e03034e01091104140f030a06020f0703030e15010e0910090f210e0d0804030b0403050705160303020318042009030d0c0206030708061804 69
    0xb090180a56038055041003101001307a01440c81d00d0081c005040341900c5144450034804008080f10141e20904121b211307800303440c0309500000041403070001002d00420300c52040702504204883d501c0b0700184d02220708030ba840403414408040304105001900d01800c204c1681400b079180c00e080440d4076400101240c40d02d043e856551810785140c05000c540c40000b150b542c81d404014104800d81001c3e400301c1c155140208604650b030f07914030415141c045d0010039201102e0510304560200b200201e0302c00c203030340c0c1308500060a001400c5d5891524108900701c01d400102444201110b42c00c14504c481d150034020103c10385025160b480e9040c0e1503509603130031000220005502003d0050909c0f64044801441c0040344015280d90ac000350f42e07005512040c0c003440817440e440703404d607610f541c80512143d164212008251030a064100010340000284078080d00503003a2402440d8403843d01d428800380c2c000c00b514150789410a04407210300b001031689800811340300110009900c0c8548a51150b03100303 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 803976834 1250 803975584 803975609
    0x3030605011202040803090913061505040c08060d030f050f130503060906040305070204050a231005270912040b0406020c090f0703200d0605120307080412061104 71
    0x18203000509081000c0c0604a0507881131209005240001c412940d1500040307611055503100e41c1518291801e00700d6004014501d4100404881e1014114403011280211401c100b80f481c1140c00380c85c0d603441210b0142e88120001030320400240075450410704102e480c54441d040104020300030343c0035030180c4c00e0b203a0007070301c4080100918641000b17142d91220040d005412681403d82e4044d1030343c0611007000b44110b4443d000941e2400c00c9070320414169481c1203e440b4100480280c25403507d1060350a4040b008946102145600b1309911603c1d2a12900800c10416060499001880c4801528580c0980200030046224460311400b81c0007515610081c10740d40c0f46402d00107813a200c2101e8035180109004000c02046081d01c061465018140e82004540d00c10358940c2ca03111020207030f01e02ca0038454085440380b4440d900c0c1e03011506032001920710b10400c6242ca0061946d90044540051108408000900c05001d03243d00e2000024444e00b00131039140f2140030f50b51499003054004601c44002e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 803978084 1250 803976834 803976839
    0xc0f0c0f06030f180803070c060b210f061504050411040204060f030e01150b03150603150a05030304050607080f0d02210a06050916050712090e0903040b16080c0109030306 75
    0x2032a01c01c0720a2103035444134145025a55139550f0084e030000801d443d0a1000c003000b04e1b01440415040382c4030b048002000b4505a605211404003d110541305240702413140c200741d80c01e01c000004800d406690381e0603052821220210400c406808000c0c4101c41358003810b41c01e10706030f0311107001503c0500501e0302c45035401da40c0808010203c0d4070001c001d5005030305042c1c10544401d00180d1400c01d45074000125652556051400405e6910010001d034105500004001d100780d1040c1842100d10307412680201038642e0340c41050760702e001718000c0e50b070b004608009c0500080c8010f401001860800340b1014203001002092500f03d0f0004e101e1180050008510394006441c1c09543d50b50100181c1d1040007445e0800000c1000c0b848024a00c2200b06d00c0d81e420b1190460080c42900ca41662100380c40001403904003004100796000d11480f0b4442d929100414046031020007a50140c8050f14581070501c003101081d49000070030900141c03050841040300e02c1c000740d0203000e0300c1401c078020f840c00300e030052 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 803979334 1250 803978084 803978111
    0xb0a0c1205070203101107030e061c0b0406050d050c210708060f0a090f03050319020c07030c05030d052b02070606230102061b160f020f04020702010c0f0c0f0603 71
    0x45e95120b0455142d8940f802c032039148031054050b603c0ea9900b5151034540c404d407074030105080f4403a40300c1c0d601c1040403002c1910030041c0160002c1803c1c1c00d054074140600355541d8184090820500801400c5410460020031142001b61164440c40e080400f50801030407294001821b00c40d06030000c5116801400030880050301c2c0541c03094102c560214100184416038491421105c40004002c080050010100d42c503916030610400b83d58a1141c006c44d51507441d0820256103094a2008507400030b41c0711000034243c038000c2407400c01034096894003403904c41c04030b900300c4c2034000a084104d021000c490140011055900c041c24000d88030f032800048450034010740070205400480c0d40030400e640b00e0f4412480342d1317010400e0341e000004080303080303c032820b445c03100c01c0b0034002d000c803d46944081040500512114001d020b106030b00942e0031140f040d11640501c016881086406404a2009508403001416419528070018001d1560030708858590030340c0c0794400e080d07602080000317440d58420074161 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 803980584 1250 803979334 803979343
    0x181401022107080f0702032713061a03041e050d090b0a0207140303070f0f2a0b03060f09070c0506250c0c0e040b0114190b0a0c1205070203 61
    0x24410195800c2070b140202005190040003880341381014481404680d10030b00810a0346c0403d10318041c000100304c202114007011854180040b48204e16142c4540080e1180348100015210341506501504100807000440c5600140044461550101e11a824864488203000240b44a00080c0c01c944110302402060070300369801c49c1300284020002070500a8001403032904503818407204029560800001a0642c0142280a0094034030b07003488008200480421242d03951003040050300001c07420b455609414041154548080e600b031006204403201d40000d103911890090500722084d1541e03021032404241901c590020030103d015500400005100560b80039500b01110342c204104010700c414600400d00340340c401e00034448034003802c0c00001114407002e4640004010054201403a10b013000200074440e16494140c1410701c44084c0c980786602e12942e840d02180c0d5009103081407400034265011f00e4a1000340244850000d0004803508007a0850741202c2c5c031125101c40d0207005240c04d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 803981834 1250 803980584 803980627
    0x91a0c060a14130302070e0a0e07060503070e1e28050603040c051912052118060d0f0618050f040b070e060408010e01051902040e060418140102 63
    0x705003480040307501c140704800220381c00303809079079041038040d80350905a060034019040301b403990b51070600300400c18003203820001500070030004488225a07607807001c07289404241ca40310001400021203000750320f405840d00c0c000d204400d00064800803044c00040c0d007a0216407072260b42ea165080000001c0104040210040c1020f0711043e02d54a40b5035a0801664010700031103208010511010700320070702d0380c520395003d081c0500c5450003541260401580e03806840418500208400c0b200210042c241d1056070000c040380701c0503c0c01c0c94600f42c104030280d002140400015035a50700b084040204a005101c02030040c1c103092a0700c4c0442040b8401511002001020380032002414031000443c0303c1c01071ba601ca0b400385404120304181c10001070f0b00d841194482d410390340c204200207800312010352085e4001c0303d040010380c013103070040d8040906a000310f00c96541c00707484590000300c060034160400c7c40760702c0084c0700f07214032003c40c1e90314410014541583c4400d90ba5000c10800305004514460188 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 803983084 1250 803981834 803981851
    0x6110d0f1d031804050702010e1002030f061807030f0b04090b090d080912030411130b010e040501080c0d060902060a2003070206030106030213081903090e0c19091a0c06 74
    0xa0700a5401005183e80d0600310580d0140f641c0b40c0006004034402c3d408070210909203010340f80c0d6842800380035000b0750000e4810325480124039000c985a4600304090b00106030125489c404d060307031840420743c020844035002d0803581d03403140b1500c5202d03502c40c070902415510805e20764070103082008055107801f18007002401030141b010140074a440000525680400641460a540303a44034980748241c1d00300615140c1e0040403901ea00c85084c01c160700111680741c1c00382d07038020203041d100080100b039030003e03c40c00c01d96404c412548640760815658401c0424000c603408142070f0b00690100d0904d51040c82014002141c16072243c5074001d8480c42c041500c5a800011400c1c0380e0540c00265503440103100d80028581d00086824010001003a03480041005105940300854201c59820556014260440014103c0341003c1100045c40175602d01840c071084541d824407408455001d4503003030508500c4240300c40e01e903000070300300250b152410074030308405107051719503100700c00c07052510901038006003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 803984334 1250 803983084 803983087
    0x709060902091f030207020a15020c0301090c150212030403031401140a061b0212010b01020111041a0c1c031b0c0201020a11040b03150f0906070c06110d0f1d03 70
    0x1203580d43c1c104071483d80070700d12000e001c000428050194028440c0c620020340000c0c80343d100040c00340f0004480a1500025001e5412004c0ba09d030400d4200da203031580041c240d41d4500340a1089084100743c0018900180c012a01c003d840641c405c40c4503002103400f140001c2d1101c9200d4003241c2d80100840c01000e1200407407000140c034030002100e80c1c41d03138020041001160103003458640e02d02c2d84076501a40e0094042c03142c5003c00d5114a000c0c1407120786103405982090704401032803a0360030448003101c101403150000c1c201481c01114582d400075117100011300ca40c1103c1200c90301050458100080c0544001600c009a22106210403494078a190140710b10307039443c4030160b6008110040c0c07480e4003038581000031546000040c000c00000c140b407074140c032510b0782c5401d02c484040c0090f07005280c2102c0184040e5542412251350310400c03203035880052412140f010002c0d10b00d030400c02c143c0742c0b030102c03044c1848108807134103040b030702c1401001c040c040d21081016448142c2807164155030001030f0186 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 803985584 1250 803984334 803984347
    0xe0d0308040809043b070e0408030a020906120f0c161e05070603060503060a11030610030e1009140f070909030c021804150e030f0c0a06020a1e030218060d14090709060902 75
    0x140140d1f130080003c1e0408800000061400380298116105050020601070715000a1052840701c1141100e83d146060494404156120003c0065407211800722010382072000444e9600660a4000000e9806800c3e05000b402c0000d1f500780108030103000542d5001030743da440c0c8401c1600c0c1240c084c00c10018a894018000790440740b02c1c0880c0c1c1c0c0102d0903242d050350f5030801c489c201d000703007020b03c01d2485c1ca0150703c0c1c0034103040903540c000f10310f91070003400c02d10000c40c0241030864488841c42c009010f42d0b44950020050171b040c070b8000071101c40c0a420500b01a407d141c001c506c80d42c40300c8180506800c4d10f00b080008000c60380fa26411001c8202c001040390001c4000025078a1043d981074100d200408100c01312801c1003080009800d990004044d51250301840014165000b00c5a40030340c012000480400118428403d80b0000315100c030400a64041030b40c00e200300ba0f40000c51441100351504010140020070404950140b91041d0013840800e01d041440302c111440d5400c4600031a0040120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 803986834 1250 803985584 803985599
    0xc0a020d0806100f020c0a0b04140612040b0a09020405100501021606300c03020910020f070b070f0c151101060f06210c020309010e0d0308040809043b07 67
    0x4036008507040707007003d200600104c8000d9140010b100b50165022490b1080441c130422564058001c4800c880448100c802112082102901030404142180e400310000180860301c3d003044260000902c0c0c40008000c0d00030b0700854280c03801221003180c001040d8000b00701c10b50341000700c6020328410340324400181b41480e20007850141d024000c18002c0000381c40400300160184441c45401d40108000c000c0d40a011308040c3c003a410400003203101e000c5400041c0d05090022032410041501200508030450a01c21f80108940000c3c0003540c1282181981e4000101c6030060304001d4052020084400f00080360b00070403071084030110400d5a41070500070032610700302d64040b60541e001410604140c04900300302029810800034551b40f0b01d41000c0c09040c0054000c401440402c0c82a40d91040303080c0341c142403203501180d50030028000383c401000a400325050002421440b07200a2010448240c10803110315048180042240350000f4540a00d00baa0460044068028401c0e0080c1c0143d40c504140c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 803988084 1250 803986834 803986849
    0x806090f091f050402091605040b07080c010c17091504023a020a21061a150c07090501120b06010c21080114060d020705010f050c0a020d0806 62
    0x14a0402081403001c80c4851030140000d20903481c41070707904048040c09003110b001510040c3c405038021483d40000c2140b80e00008919111800d05171031b01c901e00b900e46090000300e40d12003041079411400c140040b010b8a6400e00035880d91944a6a6aa5044542a064051403200644041e485501c540c1d650982c244c0c0074600341d9401a01141c9401c49c92140300302e608114100000115400c000000301540950000441c8101140c0296044071416444039590740800f080d41030070300750303079000682e4200c00640700340c210080056480700407215980004011031406e402c40642000c405074003040084500a003004000003c201e401c0e000c1c8219454861544e120b140410310280c0160100300014000d03900078500320405e6070b40310700c0c41e480c1f1440c020034951401c00302c0d10652002600d00000001d1001d42c14154003c1002c0040605141000001d8050025800304c40101d81954031008202498a928400d4501c00c07000e41c04401e54030031a0b004001d003172503031403040c078028424500d060001d0382d12101d9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 803989334 1250 803988084 803988091
    0x1a10061b020103021b01140708130308010b0c01090512071a15120a0b1801150f060c1a0406020909010e0c030109020a110604031d03240c0c0a1a0601080609 68
    0xd00696500356a170b4244410486245078181941c04d00c0b0b0a030042c544c289112074811552541c40021a890b400c03c030b0a40c90b04044406000140d805006100d018a04001049150f401c00000114245c0c4c580d142801c040b080d41e241a00307108013164210a200c0030742c00140d401840305c0441c01181c5005005201c000d4020090940103000607034021150f00c00400125040541000300c0349082d14140d90710400e403054011030014a9402d00403900c85880349000150309844202800c00452400d0800c125441c01381c0400c01d984c80c0500001715031204c0e04141825020307a01902016030340e0101102400968101a03002780005032000d010010419120800d490549480c10320140e6103150716082120880c1400002c2e82d21801f400c414401090b4100260010020700034804408040d0500f0403d80c80ba0340c4450b400c80300190500080715a03140440d82d13650310100c201c0c00d090034205041999490080c036031004451594296601121251580700075a1f40701d00246056003d524040c03020a41da9040035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 803990584 1250 803989334 803989337
    0x70c0b07020612160e060711010f122309150408160b0a050619030f06020c01061e0303030501050a03050a020409150e0307020f010c05060f0c04031a10061b0201 70
    0x85503040840d41c1e010304440c01a80d050107204042d08180d8a41c1060340d030b8060300d80000c188059100141400c00d03406441140e60800b8811034006000710055568101c1d4007070039010004d180000c2614035202c1e02c203040380c0303400c2d5810941c08258200e0000c5020300700501014640d038402c02040750601142c80c4480d910a0780002d1140e00c403025103407003010100e6480c00090440801741e003004501ca81c1c6920091040508803036985011032200f40510652105000141a042e00c40c02c481010685917001003454032040340c000560940d680962170008044600c000000c401c003840d080042c50b81c98012180980030450f000c2e506c1c60301d559a119511803182400900903604e6488407410302840050f10780842d441440240090402001e07030b103403280e01c490003c0780300382601d140c5419075501c12041c00e000c03540e004000f843c0d50307103409059a41850f0018001c00700b5440420000c000103407110b603041c0d017145038600100924100211324102000490b0499820062581c2038196003244200f60711031820340a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 803991834 1250 803990584 803990587
    0x5070516081c12020c03070501060b0a14090a05090108030a0e030d080402220203100611030a050403171e04030209070216140d050d02030a0801090605100305060102030c0706031a0105070c0b 83
    0xb040c005072580c01c80089000c0c1458404200c51901d0036000c401407200d18803a000070415281c803000258040d000b1031382d50200040991802040c0b0044841c0107100400c0014030400c48181da503c00030300e8800e000d03000700c9210740010070160402600014010404a411005441107541c0510020321658000300003a02c980c903460101c1c0104030000510180b00703901f0360019980c0f840c10440901e00483c19125a0b40010309016000103248008800c4e128010b80d580d03502032030103185448940c14030f1011901c034403048a08200d20f500056241d420845411a02d004540d140c500c1e41c010000e94030030042c0030000f55000303060041002001000460159400f5a045100ca0031516000c540c0d811b40c090002030052041c8202c000780c46400102400b04c80b091661420036681c0c9840b08001684c803148a0160080f00103410140b10b54025000194460010300c1143c0c14000407200e080d00e050030660114003c80c0c0d0f0b6104d445000d00840944008000c4282002480c001c80e42d554140c50280503c01da2103120030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 803993084 1250 803991834 803991883
    0x315010e0d0b010f060908030408030a0f050f0a0309021206060f04020a03060806090102040905070f020c0d171c0e030a0e0d02120d02061f060c0b04060b0a060507051608 74
    0x7240111000030580041d400b11042d81c4460702544130300305900511000c1080324100040f61000002204d003694101d00145003000785080d02a1900e045220101080c07100c1031040c0c8801108031406000c1040741681c000c110031680d0f0062200110108208140c0c80d0001d00801546d41c4070000180300591094900503640c55084004400501c8942c12600d01030003003200b4468444815005001502c0e044203080049485d00f220688a20210f101c8460241e00076003a400000e103022400284a80e01400c2c0c0b0401c2148041c4005040e40e10000303c0341a50202001724501c0b211013485258041003000d0011890320880c0d0340c020b030103025008070f071520034060b4095000c110340f50b90a05100d640120401c0795000c641d481c0340a5203421007165282442c05a1000745081070781d080d1049000c0b224240c17030340780c005601621041c000460040007a50101c1e00d581c3d85c440d20b6141d2a00d030b04020300490f6903150b181c1c0e480b4604a402e11150007035034544100c21f550300b40300c0b1020210361122850506003d1807001358 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 803994334 1250 803993084 803993089
    0xf0414010213030302011a03010905070b070c0f09140603030f0711040b0907020615091306020c0c06040b0406030b04060b0405010c050c030d0309150e030d0e0c03160501140315010e 79
    0x8504401d50b4890030660000004140d015000585a50103245c41e80148018001c2458200c0d07890040c05021a03018640801c6040c02120003001c01902842d951040230303450306000000c40d4801d50008100a940340f00d1131010700d500c03203511604042e0032000b56203410601060a40c90380036010014000103140504c2040d01c2d0707102d9010f1905072002900b1164a40741107800a5101d400407034601056036203640b0540020301d4101c2000e0b0ac5100c40340507000e819012174903045c0c001e4000c84403000207071084412080103175454102900c01000302110300c076612402c0c0303c0d00038165003407004494000e0b41440f206108036401482034406840081c41c10802c800030030f041c12403414000c0310100742c042c068080c28100c0c40758590400001103000d980c4401d07100190326006001c0790440240d00780035400900a00b606030b400340e003005c6d0302c03008100100e0703182400100c00030b801d22141000d46e41c0c284035010820400c0d035070401562003070321424414090039841c0807291401004105941d55042100d0b02c4103548059 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 803995584 1250 803994334 803994337
    0x1a01141b072403020c060f070c0b01031b121a04080409091209051f0e01020309090c0d0b0105041d06010512041101180f120804170a030f080f04140102 66
    0x5000500859071800c0d03032031500307800407034a0141000b030361444156118007150080c0210b42000d100e00c2d00510a81da510240c441c0c0482015082e101004041941c0d00c02003070490b0341c585d020b140510b000c13502c0f16400d040d20380754500d200e5002d2900c40d000c1608440100d03040840c0000610340480d80040c680d582d501e48548075100f00d8010021583c5000da070380003444861480c5000400e01a00e074a82d000340c484040240c0e01401881000061860710348400000e48180031b909454001801142d0405910a0001d0340800e0112b84c0d80300d103900042100008200d05004e01c1c00420401c0c01d08500e01402c002501011482440801045a41c100003080190344660101c1e1101107040c1240e1005044c03600c2d206a84500c111001400200440d9840601020481007001111001b5010705009441e09055400410060038241d600041c01d00000629001d441529181d0400050241504288500d000303400103904140c45402c002c014400c002241000007d0036400c95006841658441c1211026a029 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 803996834 1250 803995584 803995627
    0x100c080307170403030b03010c0801140f0f0d0b0a0b0109030503040303030e030d0207140601090501290702040606080f070c230c150d061707171011030702011a0114 72
    0xb000c001c0002c03c400e02d94503603c82106050114000e001120720040c045851120a000c0c42c0e00b0030714040000081031a080c01407035200c580141054206a007a0000110414509802645c0000b280410046250013900c250a52980d007400d04441590841d00c0c0c00d170b85e9004900005042c0b45c0c0d00e0b480410385240820956800154600c425075030340304146800413100083d9508401d0500ca013000104a00c2d6050268606030b5011004d50301c240729541840519901c0030780300410403150108038000242e140c0340100340107421180c031a1840d82c02e001400c861003810040c141420440200000b900041c00e442c00040030200c07a12601c2c03500c040c0400141c1c2000008000994801c007042d244070300000e03661011305408481d041003004819a541a031055401c40081c60034200d4002c0001440198010305110000c03403181001c40320207120803c0100d04603140040c010021207004820003a07116824010711102800d40300404500000c118000f91074150204409440c011000c0340c0da0140d0003039400c26162 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 803998084 1250 803996834 803996867
    0x31401140610090f061101050f060312130b03010801090b070815010804032105090d0201090f0201050f0d05040507050f01050901020a0327120201020f070b0f07020d05012405100c080307 81
    0x4d010795200c50142089030044202e05007542040001164407a0003000f992280101801602150b000380700c0031407256000501105d1100710081e0702142005071a00614040d10b00c0380c00005290310070b410034049416004100e07408114044080240d2490040d40030445010300303003006102a12140b60595004000204a100304080c83d02d80c20040724054000901030400901620200f004995041b030030b0b40c3c0d00c0c1c075000c0d1005880020920040d42709000505030031880f000d2540c18031004115440c162102500e050300e66511001c818807181c130b416032240030300b2403003400e10038a45401d4900203501d403025188050103000000400307030302b4801e1001d1607811074540400c89103003a40c1c40c1c0000b14445104034100340c2c018480c4401c0c070100c001002410100b91552400210700b00090480000300342e50016408a0b04081c0c00c1d2402d00c0016000d00409030025000244903026500100550240c5245c540c0700d60300c10304101c0b039040d4655070040c82c84003222f03030041c0c0d1065a80c0c1da50a400e840c3c04408002002c0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 803999334 1250 803998084 803998109
    0x1f2309070c0f0f170a080c03060f06270406140103090809041416051c050405030f0408032809030303090804081e060106080f1503012403140114061009 66
    0x18208882c01c0c001d800301c6480344d50070030400b003440700c00307840301d07000b01c090745004686003002080912120700d01442d031081c002045106d0b0340003124041030045d04958502280e0044150301e5200c1400c1034000050b07204000e4074200003051510f80e03c5039940031000e01c03a50515a4880c0402d00744000d003001c83c0c81c51440580b0501900c07000b4224180745110844002000c2c01c04085540070052250040703a150342c2d00b000b4030400b040c5000301014002d00014208596501c4108080510030031041e001d4001400c408001c1d40e1a0340070342452544030b0514491410303041c0303100302c8961304107a00400e0f034900f640e400d4a00010306001c58a40000c0c2031056803c000d08510584000040521028281c41c803482ea80c40c0070740c2e6517641e031083c0544041c4001e035000200d01c901c2500054141e980003070040111000180041788114240103030a0606041210210300c100c1099014000c0c805202c90304a4000e016000810402c01600c002c0186400050603441c46018010f5819119034450464807000d08031104502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 804000584 1250 803999334 803999363
    0x301110c0a020a0e0c03071107090615081302011b170d0204060f0c0302060105100201021201140111240c07050607080a05060f0306010513141f2309070c 67
    0x303a40d071a8607110403482042e0b0210f01284680800511900440041184038115110307104107440544070307680ca0461a105800300095801d003507000f060001d0500103c00604404c0000d8010305140c0010200155403003080e529200503644a002c0c00e042c1da00b84188140c6c00394180c54081400c48081c0780450f48070f180494402d54020140d40100121040707030700c44565032071040005984240300c40b800540036801c03071401044542842c10600c00c1d809010b100040c41d004000048412941d0203801050985000b01550b8410b541c00a500310380759000c820041480007650980e40030301d440c0160041040105860215405079211000d480202d94090141c40407480d002c04c00820742001220a10031702402c0101150303060409420081c00c200c07000d07000d04080e80c20319040c4a50880c4100f603010700c0a5480300c03604004410414118011503400000300710241c0082e641d0500d41817035821005179000c0c0a41400c3d84058000a80154100c095038081c09035520b003501503c0f205c07904070380500308600c1c100d9030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 804001834 1250 804000584 804000607
    0x7030c020c04110d051003050a02060901170a0903020c0103110f0702060f0412110607050322091d010509060907060c0201020c040c110f1c12090206040626060105040e06030111 77
    0x58134403405007100403c01c5660304114070018448501c4040d006400102d0b003580503040c0342000741020380c4c041c107000b60044181011034101d09001ca03007070b001c542d035100751400825605000d420500d8409203002e0005820300760486910744507001c082e20000000007660f03401c649811003901c0d1040352003d038580c0c17600c4d929405010a42c1500c44203d034000e08254088a840c600b40041ea185203070894001c50918050821410394404080522541c5040a00d00001c0c0e908160003003855076070a1040c500c2c098035541a07090b094450181c44041e882c2c00c04401c210344e46d540061803004583c202e01d45412445c81070300050f8201524040001d17001402e0592801900c0d400c2440f1402e030f6803040c000c440101c01803607800c40c0c0b22100c012001c40640c65110180805a20030b0034071f1038200221100c000307000c2d40a0b0340018902e50190707000d0404210400703404924400f82002d0b2145045031310740715070f002d46840400202244124020101080411004503a00e80c409500c08010301000400096950510300f51 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 804003084 1250 804001834 804001837
    0x100518011112090d14090f030f010c08130b040b0c0f0f040314010603030509220c020f06011a1b010222050a092016150212010e0402030607030c020c0411 67
    0x400c2e0802ca403510011400f5010001014080c5500c1a81d038a0002d4021a400d003d01c5d0b4003503a001a409004500b2254081d07a092100940e009000790000842c104181c102400303081c40100420500c0300c02c0f0a0503808580e0150f00194003941c0140c21b85129504c0e00c40004d02ca00402d207143d0315008011892020344c044d042c008bc02a43e01070f800980c482055003021900f600d4103400001c000a005120f60072072824030700e0700900c8031080c0001400c0c10003030311901c8d03804441c0c0e0680c81d24016442554030559202080c0040c602420f2103510046080c410780303004080c144184100c0e502032582e090751100220f0000e5050790000400300034245100c54041e03c0640c2c1c0145140601803140c00b280744000340f810b031148507809043d081755440ca106410034120005245d08201815403c02c0388848081c0d002910207070f00c5100c05a80d060b401611490b4801c001d500106050300729003003902e050400d00c0050380c2d000641316400b580c0e0b4a400310f840c00021000700c0c00c1118100e1840e4002e400c1151140d0354891910 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 804004334 1250 804003084 804003097
    0x3020d1415010e0105030a150f06120b01050a0f030507060503060d061802030f010212180703080a0c050616020a1103160807360f140906061003020a021005180111 71
    0x3490300c0c3c896600d480c00c040d1164100000200403d824484450003009541c0240e10001d880650002d40303507030356441040c03030202c1040b01200c414402c040180141d1078401d01c050041c0c42420940302c1e0b00ea00b0341d0b48066a51500f4058170040c4680440001c202d640d5801307224803a180c0c07141007408600d40c02d5003540070001400108a00c203014041a6005101c414820b40d608108031030764100c0d980e1101580710620f40314800042200d4020781c0300100202c0c181200910102e2910394901250300031600f8014101400a07005251811001047c41d4151b0750000d1031224460b041194651030008240000749050344c07103009407100728101600040c400301c0c0819840119504481c044195000c034180c200c480e0340320340310890154001c8a102e03c041083c56404003601d50300010000031038050ba0515a800200d0071074000c03003641d022004128550800ba5640c007606159401d0035403c1c1159081c001c0d458003001314420800e559240000340000294148600303154044a00130082103449210544056210702c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 804005584 1250 804004334 804004349
    0xc0c090c1d121f021207180803040b07030503060a0906260601060221090306010f03050d081510050708030c04032d03030c030b13150509040c03020d141501 68
    0x440c41810b00b00041d50001c0100c0b104090182220700c03c644a040068404284a0aa900740045102e000480c2c0c4c0c01400752545855850011403c40c0d21040039007031541054800c0e030003d0004001da011140142c0301243e0b454102035440e0f40c0c5007004983c4189075944035101340d03030810100054000500200c40d41009010b80764042c03502030100d806070349550038415400107078403c0806604941c00400c01c00144410010124600804400060b245c03802c00e8204080c0044001c0c010401c1000401080500201900f0818031600e807103507103002107803c1200e0b664041c1107203840300e01c500c80c819001c4407000c5602681c3c00341c4070304128080c0c02642d0024001118012040504904003540031000707010b44005080c2c4113102d0000c0e9503412000780c0f40d40810a0245901c8103804e0380f07940d4641d4140941d0b03024001d000a100410f040c821400508660b10441c0140a000c0c2448040340f040d1440078242c07601560b002c5901c0b480c80c64140a4180d041e81946101d0040100b0b0711000200750b1121812100c82c2c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 804006834 1250 804005584 804005627
    0xd02011b3b13050c0f030c1204031e030e060114040905100b0a080a05100c030b090a05040c05040c1e0212030f01090501090515010c02010e060c0606091501050a0c0c090c 74
    0xb040c541c481100c0301521816003080050003141092052813000f0340e0300410341c0320b900d410083d00c190340e0000c100c010385046010071261086042c58816403050604000c03010302c2c0501c1181081010705464480c1030141030400004407429454a0721160001c10846031300804490381182c8200c2c001000384409268688200302000001400301000203070249100c0e04240500001e11401c03501038010500c80742c0160504d030b00c070300c01480c0d95515010741c203109018a45000c640ca10b46483d04086940c0d0542145101e280741007805100c0c00e1b800b941080d40c020940300075000d0750040600607842c1005e0a060582d502d0b40001c04c0006184c11000402c0c103c80200c0c400b4861350342c0780c030902030036034000300c41c204551070304802520099071040803110758944c0103041c14440e85185401042859110000b1a1581d078040c000303004090a0200030300358088100840742820096980c0001c005d485100700792010080a50040c000b4020b441d20b4407401014910780401c4210098003000c0c00c20768100071403880c1c411a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 804008084 1250 804006834 804006859
    0x5060a0609030210050717070605070201060f0b0423030a08120f0c09040b0a05040513030e030f15190f050601080a0e070b16050601080a050d02011b3b 66
    0x940c00d85007500d900604200e13800200b92801c0300c540d049100c0030381d81269a0840c2036030700f550700d8004000203405031201060901d098200a4250383c1b240e0700081042080a0f0100411201700080d502500e100310042c01032420049602104c0c047e090107074541c103010b0180302000300031080c0300900081100080702100b581d60681e13040243d2800321044051648104000500c0c0d02d0a030f80807840344075004050201c499114408107084880440d0090b01400501180000745500f129000c65a4007086004114042151242a07103d0b80c0d036116001c95100c0c060b020400c02d0000c41031180c03008101113000c201c84030205403034602900c41a10914080b405c81c0003c83e03000056070107502c18280003500102420340c03802ca0481a554002496481205030f014000e500003602442894002c0020340c001703101080381c80c20000c2c07c3c00500c020745406d680c548215180d001c80c0c0194503800200e8141010202400090b0003580c103e142c070304801047c00c424a81051341c1c0c0511102c0404402c1064980354010340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 804009334 1250 804008084 804008087
    0x34b02100f090302040f021c1d0604120305040c0b0a05030709081605090a060306050a06090c020f070603181203050a050a29040212100302130b0f3105060a06 69
    0x149415079100010385240c00500243c14540c101d1050b510031110014909103403041101c6024a0200310b1401885d2503030041122002034200c01e5403089042c401414140c10542d03110448680d144440300d041c0340d2288005421702041d284808000c200e81c6901554441034240020a5a40200c03070010100790b00300310100d40400c0000f600754060b03106000800b040c0e82810100701201c08000d218210f610307194140840000c400740111070050401ca9004a0110f0602e040c40d01035401c2c2c807225108640c01080040d110300e10006a0400320707501c60a0008001c1002d8000c0c40100414420260181100d500d190080030b9055102c00c0c8551240031082046460382100c4500344c1d04030300110301c618031546e0014415803001c0e4290900001d80140018074144842e07442e40100c15080382c00340c0344000702c0c007010019403c0c0019040d400e2038064004101d0307003089000199140450031000b0307000b13242c00d445c8501084000d44d44082c0480b008070300c891040591070940b1019103801c0b10020300070303459001c000580d40d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 804010584 1250 804009334 804009347
    0x70209070f050703080a0608070803070b07030c08010e090c06030415050f0709032a030f0c0b0f0d020307030b030708010b2103190c06020f0a0e0901034b0210 69
    0x2018540d215860f10600391421107003004050320050016030b0741c140000310b000703003000014010800003000d0342c0c4030f00ca1820070180c0760300014020700c28141003140300100998030000700b5055a1550400c107070f8a85900b076031a89082c04000c845d5803c103038004144028080030214000902c0240c400501c078540d140c940b0f120031014149c2da50404110728420a10002e00b00c03c1121545c0c0b050340c40381c080c1c0141c03107025148980450398801c2d207a6102c440c400c642401003170301f55180500a144d40c201d18055403442c0702c0c205403189100c410b44469001c004a01006e201ea007180c06449002011200c945440b0102075000307021002c0701521034228403400d4000c96603040d140ac0ca01c1440b0030091401c2c2040c0502c0e07a1200052405408100940070035020300040952016228044010b11079a1320344003503101c0a4403c20083e0604d520840f03480c00100001541c07440707107c0f0711a505560303800d459007003101105d025600251240b0352110200d10507044042c100c00011040c81d00803070340d840e010100000281c522 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 804011834 1250 804010584 804010607
    0xb1501030e030f072423010303090b0f0909040501021c090209070c08040312120c0203070b07260a093e0a210c0b040f0306050a0612050307020907 64
    0x540003405140020318218018088130750091802c0f40401e00c0f958040c1d00324400560500300c806640304405101c070b203c0b505400b5540d01d0014a0488154150f44000e404807145104524040700005207075800d621041f4107440c2d440307801a0040c0c26504240c501503010350480c92288101c1c100c607600c42c4011409500540d01c1d526000f4000701c5440e04c907502c00f240c440c40340c1c10301500c50280400c80000054580c41450142904a43d222030703203200d40728102016034500840307010465106000b100041142c82c0d440780c2e006079850600344075070302c000c00c03d08540032100c070b03200740d4801110410082c2a03595a04030700050782c8541c240e20f00c801146200e03110f4081c0c5915420a0f40b05811403840201419809030000039000203100c58038155481400055445120501507118994000d850b410030510821100151a035070300094103007800c0c0051110140110310020f0308850702d42e0041840e034525030b07000c500034000074405010002444c0c01c0542d5240d000034000c0707020386a00340010307908912402d0184071 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 804013084 1250 804011834 804011861
    0x91e0f2003070e1306060905102111040603150506160609050109080d0e071a0f07080d090c0f0801020906041403070f080f010608060f180c0d0b150103 66
    0x60038010000540e403600700429400a01104801c9158150345002d120103802c14582d04c00724a00d0f0602c40004c220310611740c400b502448a03181c0a40d512a0440720342804080c5c04600810a051200903000c058060103014064090740050007140e81c96161700400d142c4662a541d10440a994400303018140c03088a441c40360030950816008001500c0340c0200c84480d00801c00401d0059003a00e030558590f0202980300c4600d991000d521107070000034450800100341007040d40f03100200745d92031840140704607941d00d810f0210001d000d0080081c1c0d28240c0d11030b15030b03095042058141c2c81c5841400c0303078024000c8050407219000e001449490500895070007600190009040038a04403810740d050800c6c0840f15414054648045203a6210325030520080c0b40040091016a0b060740d4880c0c02c49000703070801c40e442d4012008101c07600509003501504070040c514110304071902c200301c160814608810f40e0f90b10414444101050000c5200ca482c002c0e880200c0541d81d54210b20019412949040281c18 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 804014334 1250 804013084 804013121
    0x903050c12031c021c06060e01020c030606010c0c0e010603140a15060c030e100f030e071a07030c0c060e010e0d0302121b060f04050d09060509040510091e0f 69
    0x709022072500500090000c50f01025041441c000002010300081940041c110b035a2490200032040d403050070001040c00c20300141121003444000b00b5141c000041026041c4220700a0003410021100310610082a0303d03001c1104030f503143c3c0801400380c04004800c4c2c410780700a80110702c09801c2c52158140c60f51141460307010b06450104107441c5440414401c2e81400110b0303c40410f181c540d0f16107620107110aa0f50724120f88082e00d030140484100065070609540142c0d401e0040180391103405c058901c0403021140c84d0080b0b40f908031054a0f032840001d02c124100d40002843c1c81c0c00107440023200000341c0301c6440031030f00c0c1024804103d070f10304006401039020000c403006a100c00c10040c40707024448812144c400e041221100d00d040e8060f25003041303c14100e0104000e20a06124284880a061904054081c43d1820050440c010900003e2140717075144041104600580c0503d0b0007441c00c60014800300003002c151001c0c4100a0181c2441d00741003003200030018010f481403418052141800700c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 804015584 1250 804014334 804014347
    0x70f0507080f120d0c050c150702010c0c080403150e070306060305062d06030c0303070809090a090b01061404351c0c02030a0c23040902010f0c020d080a0903050c1203 73
    0x108058041010399406204040243c400c016805100a111208c600d41850b042810049002400c60704100c0c0b200c0d013040360b1161603d001a07540e0007100d0449030800020700e8614802c40100b0001c0c691280c1c0c0410314840c84200004010340d07600b100302201c0c000e0069604e640da58900d400c41070404010902290940c20000e400c83c00c004110940d08890f01904031203c508190012038a90362003014152241040443c040038186403100c000c3e0303840000d0034410300809080c1d40d100c40a43c401030042809010a02350b04500440380300c0c02744c2d001001000c03d2034103105c3c0c118000810445032408180c824980c5945540140800054411540d04103001c4140480301801c404503100d44002c001203a16002d945c005501160782032024001805690961855400c10000c0d4942201011000349004604240310a400b50781c08c030b600c0c07c00c2e101d8903081500d81103082d840080e001c1105000010b02441001c10f95442045e400300c0b420003640c0c426402c549401c01c4d003004108149401a2005906900401c03c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 804016834 1250 804015584 804015607
    0x20a050405090705100504080f030405030d1d03160608060901081b0102010f050906091e060103060e010f0c080a0e010614010f1e170a0513080a05070f0507080f12 71
    0x41c0d0340c41266101502c54803030700d5200255206800c0303440403000500103c3c0074801c00c0010300c02e022914075554020b500d000d00d000007003500c03101703031030100b4061106010041805040e00d1084d0150028002c003030341c400940e00400207007a5021070140200161080d00002c1e80d07820700d45a07040c142c0300c80c42c008101c2d51282c40480364803050692410750465490700c01140e05020039003e0346010701984d101030b0100f40341c241c03401172074640d00503485080c500800d425010581d902240740d03410b40f500f00401281100044141d2809400c0700c4840e0244646172100c0c03240c0142e40031040c0f50081000f818107000c6c603140481c42c1d5080e40d1940c010b0241071000002144019806442c008401d840d0600784401e00c0c170844400e03141c0c1040d03011040004030b81424030180d111400346c1c1c1c249900500c003044c01c111a0918042c02c604e181c1178001d00421180000500090341c6000d00107036424158888400348441d1a02d140651712154903200b2800b240c8900e0302c01080520022540c40d48003815004650b080003919800c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 804018084 1250 804016834 804016841
    0x60e0108100b0d022a061e4b151f030b090c071214180102010e01020a030b0909010204030206250b04030815040203060607110402090a030c090c020a020a0504 69
    0x2444101a9800c1011311a40700c00a00b0444c9649145c1500d8141120708489460500000801044c3d110001e0186440e40038804d504581c0c100c860000c0088181450141641d4502c4000c2c403009080300450040c001c2c1c80050003240c0510313442c071880145203515a003201000c3c640d0380304811680148603201141e10f2207101c5652041004042c41c0c04a07051808a0100f08085401c3e100319036290700015806041c0940c0a1070b200d244921403034004014007a80d140c031500c81c02083c40c5050921081090302c00c460380300b50402c00000d0700d440000c42d43c48501e07500c09001400310250035070007416541d0014130088011f100303460450342c0150055207004190055071024009074502982c040ca845001c0c0c6003c201a419418071980c425240c540240c1401c00b00000404500e802d6a0b2299004104105650701d0741c400340c902d0f159000440c0c40d20120702c000050040d0088002294100c4125440003007804152070710341c0700b00d41101ca82008007400000d0226298401c0d914007a40244c0312035420400c0b07041652 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 804019334 1250 804018084 804018097
    0xc021504080405060a0906020114070c020112290f040c0207060503040602130b120906190207051002180a0803120112051e0106050f0613060f0225060e0108100b 70
    0x941c89103072075164070003e1125040301300b000000a01151301840116024490360100e01c4202c0c42054076403400020041942d031980a00030704015003c01e9180b0142030725000040030340d01503910010707110542000d980031701d81021885840703449060406051420f16100703c42c42400140c0c0a8103c03281425400d8490f0f60025004540700d035801c008840d4034025100c440f9001c1c003402c00ca000d6403501a407440b900762400c05841015070750400001e00002461400820a46c2da10743c13140940c0b14580d9003000d5040c00346411a200c100750001821500002c0d100e850302c6403000040300c078801a25110752243e0341c1c0c0e004000001d400d505640005000e0008403400710030b80035103d5011201c40c0c011184101c800c00c0c00203c1059410fa440d42c1c000e00c8140313020380722201c500e94161036040c101000e00c500706288031520f21036a01070285100c0e480c03424a2003071100740d62a4103143d05440808140c840d460803881203500c541000180c0700711444900790b00c83c824003406241d841051a01240c1031048009043d40b001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 804020584 1250 804019334 804019343
    0x11814070f35070c170a03140f0106030c0203160b06180906040f02040f020d0b09010602031608090a1e06030f060303050703030507020c0d0f020a050d081b030409091b0501030c021504 80
    0x2801340500007101e01000d0007204c4068010b0b41d0721940e0242003d03081ea440803030200308105156041101a0a0b240741c00ba04580c0289004035180b601ca110503811881021011010040c448600704107000b0907410303082c05080705a580b14040c40c0c01055280c40c1410036510b800558000030301080204401d060501ea846000400c002800301103201403108a078407108038011003030748941510203036145c0440320600400d240c3c0080c0d0701e82010619003031081105c000008180fa2408201907581c0e403204200000a0980c415404601641d464034240c00103801d07100d01d03400a0b06040c0e00040d214824040c1408036136058440e542800e109a80540240000510900462043d01e02000c2180c2d00c4090040d00c050040c100c220200220780107020109090b03030441e50241d0b03016050000021200350445181b0105210810108240e000c0d03c84c1c00c6114a0b03006968542c01c00c08000c0502c80b80000c01844070515106502c100c9540301d0064080d9a80080800c0c05a04030b801520001810846542c0c5d04c513105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 804021834 1250 804020584 804020597
    0xf030f03021e010905010b010918051e0903070501320a11031e060307031a09030702040c09090b01081006030b01021e071d0f011814070f3507 62
    0x2641c00300d09201c80d42c00c4119409a4580344098144002803050030900e85080c40c2c5000098140080700c00d00c00a20610604880d07916800503c0f8107030116100c9100d5912550008140c1c10201c0c1c00903500c1e0085c24003a10107518001c43e114201011400a101d4860594440642c0d2040d00d02215904030004040340601c607122034480c4da81c80000070085108414200d00c1e81c507505101c4080e0b4038014001085240240c1c4184070620128454011360135150710000808216a943c1c05c0e002401c1d0300400030000d4001c2d0810b1400c2ca5034a800100d0300c003d55040790420000200c14100440300c0c401c0940350720400807880c1900b400958840e400c00310b03a0780c0701030046030200d000d91000c2088501c50302611801e90b421040c42400800c211030440c22182148011440043c2002034220013000e0041c81a01800300035810002c04c3c50210ba00b100c1007640901d00c02081a01d0100005855410394111030400205c103500071a00f245800e80b400d1201c103880540c251402c11480b101010703e004041d1090702480407 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 804023084 1250 804021834 804021853
    0x20d031d041506021b090c0f0c072603070308040b060a18060303110d050f0904180c03030905030d090e0c191d06070b0f0703020f0414190f030f0302 65
    0x6942c000c4100807441e104200c158107140c01c1d0020f042c0170540c040b04078524200d0b02001a0703540d0309011190040d2138050250303500d002c040c01c5000240704214214145000d40314000880c44a4074040701002100305032402c0d10200c0240100340c8a2103180030003404195002c01080100e01c0c910b0119178000800340c41c214503103840f1040070307849800b16141d460390a9111300c4e0900805500a940c0d000040c040c000401c96a1209013029059014403554154412404200110b5903a40d030f4115102d04003244c01d80503103450540c1030004801c55140000d60118804020028250400140f48401003c441d034403880340714281112207440003409040c00b00c600d00144048401040300240c0c01380201c000f61aa00c90070103d8480c20b428860355926014460b10080c071442011854202e4425401030760035075410941c0e41e07184000e82c000e000d41d002c041d510440114001c9500061070610070150403089404030030080b01141600c51140441c012000c4003010300c070b410000a4078480c05544480c0c031a00544000c0302 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 804024334 1250 804023084 804023089
    0x19020406090e100605040e1c0513140a0e07090b0f09060f070606060512070e2206030b06090105060924030f041406040818040204090203090c1c020d031d 67
    0x418558641c512600803d54070411540c00388a500018201a075080c488582502035043e11000561900e041c0301115215508180d8841e81c1103c0d5001032540f4000341c02d50301c0c0d10401090840340c03070070140500c500700310202e910b24065590341c2c800e1526643e01c0c012613080c00458480c580181c0b40e024010001441a03448079a1050080c0402034140e0103a01d44640160800c0e500b650903641c020340910008000030400540700251941d0f200b0b41d0341c1400813226140402166012195070101d04869001c2014075151100a030051403ca80c002d050450035500d400f000c1000051080c0f0842d580030f9020051400b603070402204001c2134144810700030846071316569208034940d00441e8580c41003440390041204111070341c0c00d040c040e4860b4100804d240e207096a5a00228801c00701c60050810198800c4401951079070101d40107421328145c00c0d501c90900441041c0c0da5140c00f04030b00d2140307502202e00c100300b520070003484500c03c3e0024401140080c90751030a035203601c000c02c80105034083d510042c0c48241c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 804025584 1250 804024334 804024341
    0xe150a0f090923030f070f230f030405100332070f031802150c030d06210b01090b0a050d050c030c0634150621051902040609 55
    0x1d0441020105094001d4038041c62568040c40a66501d50042414041510400001e941d09041d01003121552003202c0d060000710044103078801484c102c0c40140c41707203101031a003d0354001500080c0032030385200c1c014511152203014900529401a01381180c90300d107184242c01200c8030041c00c00360042c000c00074810b40310300000020840b100700b030030110512a2080d840251821003e0451034200902e070129002010003007401900640f0541d002107141c40c0340000d40003240d50032040441243d5860404910010243c9403c0c42000754088100c80b50f02800180c4031180800f071980030f04e20740c12980c24500420018040900160703080040000c000c6010707100c2d441c02c011060b0264000b0144e4646840402d4601130101c407100d40501414000c1440240c100c40f14100e000540161460384541d0f041c01601000c0040e181c0501500c0d4904800d800c020003075030202064807642029031066070400d004581030f1a40307076900105168000e001c1c10000d2910607002d403026a01c01000824510380d200d080c1005c0d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 804026834 1250 804025584 804025589
    0x20f2d040e03091e03390f0d060b100908060108060f19021303030e031b0a0303030e030904061e0f06050f0a02010b03100b011b12080426220e150a0f 65
    0x201c00c9081002c45100c000c5040450b0740d503c580c6d030b242d0340c1c001c031030011610820611181c0c6002d40c001e20010010811942c1140304031000182c6842d86e0403210400040002c50b02c0e2003070076003d004003c00803c000c2c001141c494403076002c0d80e1050180303441d001c1000d060446400405200554244510381220035000c1003100118001e503600a04c0511290415041906061000d001c03581c0a01c6488000d07101c80e441e510071a90141400103003079484140050840c03144032100c03540540781507800b0901c140c0b03c6c2044103c1c0a054011501041d845d00d2403241684081c2c05580c021440c140440c00700041824010000300d452440040303200c02d05500800d2034001810115540305440380c1000c80300d968401c6601d0301030000360300186a24400c941f540c1d003802c4400c07242c80c410403500c00002010711144007a0060408812800b030303100b85c2610604041035070002c08060302da2900051054400d28000301c0d201b01980c0fa030006020546e141d500040c1c1044021a5040c2d4000014420000309880b40a008000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 804028084 1250 804026834 804026863
    0x215180d03020c15061f020111030a09151e0b06070507060819060b0306041d06010803030f15150a09031a060109060507050604030c020f2d040e03091e03 67
    0x3250100c2c820500e0501d44c410745110410664002000942d5030780b45208100003015507544062802c002500f06d002d0600c62880c00040382002040c040c1e82c1034164800b13a01c503409039070501000b80c1d46007d52000c2d11b05040c009040800004441884007655500c18103803060004d02c0b0500d0b000c400d0703840b28108401e80c2d00c5180402e00030401c005c01030040380c5200b105511030320f40403c9200d040c00440d2255000103800326010310783d1010f52a4168110400700380d081000d0a08039101581d446505c560b40b54412201c64244100c91404141c0c50f107880080e42c03180b100d00800c40010321402c01889005a00407240d008104a042d50001001c40d0102d441d4040381108a00c440b501450030b031001620b40e0705558010030400c0801c000d004c0204201090403070304240e02d85000814070120b800080d940d44484850b460380500010b03c2861032124921510040c141020b800f100c1210318a0f0405c402c0300e000200154460308200900b443c80c5c5041c0103c1c0c00904a9590300c1c2120080c1000400d10f800040034981c030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 804029334 1250 804028084 804028087
    0x403020703051b0604140418110117010e04020d082517070503030a050c1b0c040f060506040b031e04030206010608010f060f0f030e0105100f0f060215180d0302 70
    0x206215050100c80102c0480001d1110002807040200704c06204501c901c4581034607000d60807181d42d480d038101e1240341c510b801542c03580c21581d05102c440c0b18a50716401b408181c40460041d294a0140c0905048400c22124042c2643d00c9400b40000490301c0c1400b1a0380700d908014104005081c00c600c444644000e8203510340d041d01d030f85800400c5204a120035850b5a40610294001503000800c40e540950070b07290208041d10744100b5600d050240910020a5500e00f09031050520740004002c0c42e03441089505210cc0007020b00458112000d03805a0b94000700c4c200f00a02c001e01c20a4025a00106003600c811000101d2003107c03c1021426102240141c1001004100c2194002c5a450141c021030078400c13100b51518001900011400000c03a0a204501070108901f0340240d100b05644054540240b11916217804a540005018000d4098218039910049032006280d6110b2040c0c5e125900140b403070030320505401829260041c0071580c0d189801d45981032001c428002e4a5000089840c0503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 804030584 1250 804029334 804029339
    0x213020a1103090d260a121503020906040b0d05070f0509101d040f0b1f06080c04090e070f09020a03050108011b030c030209040203011202010e030303100e0606090904030207 76
    0xc0c02001440480d1071154014420041d05565100090074400c0d44000144110541d40760102c000d400d802c0e0445026060118800000070317084030300320480304000c00c8104024245102000c40301c034071600020707400c041c107140081c442c0c1c1800c0d40f0035081c4a20082000d901040039550309460407055030008099111600420001820006152608070b44416803081d0307000d09010801c00c07001d04180d11005000e0601003c2000e03c0360081c10745c2020313604034040349018034120300e00280460b1455400301c081c0401c210002a0180304401e40e500138211180c201d0318040c42e24462001401c8880700c54241e81c01040c40000354020021111801480c1d0900d025131502c03807403c0d0107012250145d2016015904100302505d00c0c54604502c540d064086060014140c0e044040440087c06000c0f0480d405c68400000403540c00002201c035840e40e403007603942208641110060540701d00ac1681c40e00c150704101002440840c0280c0170056020001501d0b5904156600d40011007001003a0780540142c1c001207000d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 804031834 1250 804030584 804030587
    0x5070f06140609010b120711060f0f0c04060801050d061805010906110a020c04050408130e04020301150f120503250c0609050f010e03010e0609030339160213020a 71
    0x10a0303400b0008440c82c0320f456140407103030340c00c0b8460740002c0088420040001403546024908000701001c6441c00c40308070303141039020116a150240c402d0303100000e42c0c40000360800c1017601200c054503100d03074854056902e030000744452007030242e4003200e516031a404010340710704113101240f04544c003490002c204a001c5081000c11980424505010072104110108100d900010005072011040d100000d040d903850800c090b040c0104007581101d0000880d000510302d00c49100c0380e010714000c400030406003407080d4025001c1c810a11034125110034036007040202c40f100da90345c056024050004e076407410210307840070705a04200700c5d03420b600d061003e000c80c01489112001c80c8040c240742d044c2082c01900b0100001e80307106182030076504129100601d1f10740c0e51001c1d00102070500c0194100c1da960304011000d503480342c2048035450394070030703445081166040d1801440300d24490441001c0f0442821714039440b42e90303480b172446e10507405840031100d401078491a200124600076540f0044c0c8507034000b00d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 804033084 1250 804031834 804031871
    0x100e121203090d030c18060c1b470c07150807110f0717070510020109021c08090d1e150b180a021e0a020102250506011505070f06 57
    0x400401c0b040b40d0842c1c12840c0f01b22040003d840c1c5604028517603940764544024130352543c400a0b03643c1186080000740488a1410101e00c00b2881c40c92a02180d1025959141d0400051381540a0022881c80c910115145c030000b031503000c1c0c0d90070540e1115522a40c401d58681c100064007400148907108200d441d9601900c85117202e00c10901401c4540004805c49a8a1b8610f014520040b44042d403c91958002045000008e24028044032041c049624003e4005c0c0002c94050340030325800542001101008008442e84c1e680c02081d150425002d1000d03c80d024510460441e28000120810071800c900051550441031090900020954603000010103841c1e032555503601440e0001c0d4900c140d200420b054a80c0040c044a0040e281c000241c04601a1281c11103403030030000c3c0004444000642c19001040e0003170107080e805e00c0c800300601c0105824901e10001524940103903005015031444030040b01000b052601e00710382070042c03640762039100192042c011101c43c3c5c2c1d9501c1d56a105500a80c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 804034334 1250 804033084 804033101
    0x60103051609360209010b070303050105060309100914190501060602030c060a0908130603020c0105060a06021c031b08010905060d0302030714150a0515100e121203090d03 75
    0x1030180b0144840c241d81c0000321040001d066004400d01080340b2000074002c2da412030654000344803280e00c6d42d484010300c04540c0300b21800c1d00040d00340300020807141405170840f40a228088010107142c24070a1440e0f0003003c42a41c12602008911030050110340c081000c002c114035101c40b04c80c1d50700503905d130407400c4814070f038072500c20341d0400e101c1c20010410205a01e54021251840880c0d030608500e481115440340521102070306551400100310705e58142d0240c084401502d00800c501c0e21130b1006c101c00341e80710744924401a440b24144010094240d40c0b441403200aa00700880e114011100519038001800c005c040080d100d80010850070f803680c002c890b0003807402c0d1458040c01d106c60300d00940740d100301b2001511660a414104001c5913082020072602c2c0d00416201813207003402c000e070034007a20b0159091700b50003a0256210403e80380c4034a51003440e01c000d03212441c09d80740a01c1405450030120960b40a40e000d1062035450b0303044c0d04c1740210706c0b40300950054002502b020001408070384100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 804035584 1250 804034334 804034349
    0x906081e0609070611030d02040e040c051e0609040902031e060f0702030a0507031809020a02012405100912210507020112180c0e060f0105160f140601030516 69
    0x8009020b120031020486805880300b0345000011304450321045441c505c03814011443c44da100150008003800200034543c010303031280e00b17941642035039076081200400e42e0692901118008001c01e444071700e0321708002c01c0c140c00040c0c000700d0442c07603980004e4101548503152480c0003004040114004109001c01580180c3c640328400c0141007843d4000e6903406207402036018032030009008070034103000b0000119a925280c4840642c070f51a014048065001007000c400550700382107180483c82e01c48850022030a0b00140ca00d44068a044104405007030208500d4090050304100410b0061114507061034480c0286070780500c00d40001542c840d51380300c4400100402800b40907000041c0e82c88104c03c5030f201007195000c5111042c107894003c80c03410000c03000701504100134000a108034069606441000102d8001595500703010041d251489500300584031004926001c000045020b140707024403030701688807040303a103100c04410b130300d801d8003a001038603ea03015401b800601c0c00080c14000182014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 804036834 1250 804035584 804035593
    0xc030a0b0a0b040e1008160306110c0a03121103040b0603060f01120b060a080a0302070602060a150b0a05091203030f07170f060f0d060b030d020a0f0b060a0906081e 72
    0xd00180d00400d020b01c0c01000c140b1100380c0d0110328501c0b42e5000311700140010b070381540c484080007545850a04064070040f14850b081091803800341405106442c00c0701c030048003070300158059590490303e0080031030800d2011981c1d180004115400207016621441c07243c130226020341803040401d07250000040044035403101c07440050214001c60300b422103a41d54400d00ea900e85403204000165080c0e825008040607100300c0e03118405065000503058102c400540aa400c1e80d1038a01c0c40c80b00343e0310a40c40c140c94050581c0310070000544071a00420981c0c2507440c10b6402c2061507400100680c080701340400e4a54004000e22051902d00e055094022145003450018500b2003581603015041c0104141c452441d01000109140c580508126a0b04002040b000e183c071000e1510100a146c9e900c4014001c1c810000340d2486223000140c28804250031400505130042c581d41d488a02e10f000401c0c107504004502c1c00025001d45502806001e0004500074140c0702d202203920903422086003011420b00e900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 804038084 1250 804036834 804036839
    0x9030c0e011a0c190f0c050102010527070b130810180b090c04020307090806130c1703070203010c0302070b070e130c030905030c0a12030908090d020d0b0c030a0b0a 72
    0x601600d1030b401c0021900740d103500c0f001010f03882404e10348501c40310b07400c90900b4030000040083c2d5125186a1078031904a9050468445004a003281c0c01101d960300417005041c1d014280c3c88490a000302841010320440b040c590f150130060f000350f00030840781c00e41c9c205140c03000e01c80b0200502c08512070000344801080794a0b90790b05803446441f41900d001d0301d1905d10070007048048800344109904c0d0341c3e0291080d581c03401c02c580001c1407241c031f5104060280c02801c1c08507800e200380c43d07110b00d900790f0040507100311107081042d103c80991055141c0c1115100c1000303040b0042e2800e01030b00040d1031040d100141c40f402c15080450642c074005294500300020105010040e641c1c1869a10a80010101c0021107003000d078401d50080c41c10000103040c0e4407002c42c0e003420901c400603c001000d441400084802541020140c040d110901402020303502c1c10300030f9000c01e06207500b1001540d8001001c45045143c2511003820348101650440b05400e0004108107070740406010340d845149041d01c00204192 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 804039334 1250 804038084 804038099
    0x501080c0c16030c0602120a0e0103110c0111040f060c0b0a05070207030c030b04560115020d1803030804030c0209091e070503061909080414100302042411030a09030c0e01 75
    0x190749c038210724181a900c0c0b000c100f5210f120030660b1441d400c0c0b20001c009404019903a03140d0398020384540442c81e0308041004c90001c0c4254004050240c0c4141e407441c09440f41034041c00900300060a07a0704602c510743e00040403070400700f078890003140201200035181c10242070400709a4480c0140702c2d0b08480744407084011000e07043d0460500d600c0040014501c8003c20300d40b20b903900f2420314040004992f00300102d9910340e2132002c07600410b46502110410a150a402d403030744c00d03000f40f0254181021310010000300307001d080d40c81d03809842071400c69003e401c103a000a20616081d195012903501c18141070002c074580c083e4a58206600070014900d040c5050f0000c0d5035400b00034108a000c1100e075040c0b809000c0984c001e2240103600034009901d4a40b01e00c40d6400420b0711050642c41840f8620001c0e452501910840741904c51000111144145071601100d00f0300c14038610404202c21200d010403900801c0c0058512101e950f43c442c030030300d07107582000a00c0c1c0c07600707810501c8000f402800402142d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 804040584 1250 804039334 804039347
    0x1407120615051207020705030a0602120106141603090905070f180503070b0d0b121605040501030209040201030504050f0106090e3f070b010f0e0a060501080c0c16030c0602120a 77
    0x8a000d5104a1030340e80c0c04d10407130810851783c0c0941c1e010301c0380c0a980c000300001c54002e40003c0d14461800b551503039a448049a415040c0416078a804100b00f01203902c00706000090b0041c240641449e807031035a5900000380031a1411143d540000c0ca03d400e035280d444c2e0303114021840380e481104604440d1030a00001a072203558512800704da5034000900d034014895150000c000c3c1210042240c0c6030b00416040c82a00d5801444641ca4032a09041010546103002d204680c10b0f25006400c602e4141d60740d44c0194014140074000f030310144502000c40e4101c1009000d400c0c05400807030303008264000c04800280c5030504040da101100c5c5040074615080c1540c00840407110003c140c142016000a040074006511601d02c0107041e2400305e01c00420610a920344000031159228810702980c0e403400d0626040b24140c1c0152400544240e0215085403903220190041050b10340944d1803101c6c04100542c141035642d4412680303c0010181000816018440507030018600100540740c08015500208074 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 804041834 1250 804040584 804040597
    0x1504020306190e030c0607110a081b0a020d05030405180c07020d0c03052d0d1e0504050303070507030201020d0c0c05010810031b150215010902090301140712061505 72
    0x250b41c00c4a028144502c5900120350840315103080c0c139903514100c43e2407038603004215140d1010030081c50801e109007000180c480f03403031b90308201c049017410410a0401d441e20004203807840a8407402d040301c005a6684000e060400d0300c118021940c0c2ca1500d8180002e400c21510488207007150341042024824102d02100c81c01d5504031104410b44010786032250000240d604080d150303100c5c50b1040c0e001206c1000d850007420b0800d2501c0c0a428060940040e60385c5030041030080000e01b0543c40328040040580c1d440c00241c1e480c200541460385034070109185400c6580151000d500c0080100300f0b6580600160b841e1700040c0c0b0306172144200b07940f039104d080301062194a0422246e100010030212840107420023441d44200c11810403515600c14120070b640500442940382000c0068612039400001c3c0d810030200d0040d401c00d00c503840c0c40c81003070094000308601d503015520b8042c000002d4104c040418403400e120f480324492042c0924044049071507603000b000703104400440540c0d1541c2c114081e07914 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 804043084 1250 804041834 804041851
    0xc0415020a0b15010e271014060405130c051c15091107150906090f0c0501030e0706050f0706020307121116021c0b010602101506080610030e06040b04051504020306 72
    0x1106c104c00843c00344046c1c0801c05c0780c00e40410749010300c1600c0b80c02850030422110b41c40081c603c107003500300810030f0b01d108a104883e03120702803107410080340501d80c01c00700e458541c6027081410021141f18184070100302542040340d4683c0c0e070408000c44092155180e01034110214200a4050310755288201c5105800001e001004040380703100f801007443d00300e07440d8258003140c2800340c250130b0310740621b9003020840c0c00ca40e0301c0e002007004a11944248160b404c003030310200003802e819180c0481680d042d44409400071134104100001e2000c00c0c01800214003681c42540d50465009948102c8804c8494040e03602400e01010040941d1950712211104a82601111000311021801c0303c445c005d6000c0d2440203000511003000050321540100d000c1c002c10705400c0040c022110100a43c40e003200b0306004034400308908901050729070601e4680000f240040f0b0400103110020039030b04030300d046811501242c460180c0010441040340602440c1c4201040a00101c0d0328101540000c0d103401e4000d11140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 804044334 1250 804043084 804043099
    0xc28050a080a230708070c110411070507030809010206070908070e18011505031b03060106050a050c060a0605040f02130504020d0f020c0f0114040b010e0c0415020a0b15010e 76
    0x10a010410b50041c00300008100b100842584483d080350681001103444001141806002400e80d9014403000ca40d00756110705800c1d00020701d07400b000010240001e1002d20050180030820004208020000107540070b85402601d41e0341d810002441c102c0014600010406011003c103c00800051103d007034030300041d43c40d02281d0320300d1038104180346503040b58502c560900e601c10b800c200c4e95464980640b0416005e40e00d0b0301d80c0c0d0948000b108568800d0454141d40176078010881035200704c0c040c242c5544145004c2d403629800c0902745191000030748210320880d0f5211010801842e042c855011031070340c802c0080d810903042252200c1d074a101c3d8803a86000e25000640102c0b2801158003110841808a40c110b4441c0382035100b1581c0da04041c3d400003c0c5600e0700191594034100303801207a108950182c81203c82d41c5c203240b003e0622060103400468003100a11003ca4454000000b5004003440da0740244030036200c504043c0340200e009400c46598518a00e500030550345d1105c1940d010b06403e0b01c00c1d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 804045584 1250 804044334 804044341
    0xa18050a0b040f0b0f01090e240d0c08070f060f0806040f020c010b0f04020306030a080c10050c0703081032061204120203030c0306040e01090b0c28050a08 68
    0x202030301e80c1c004101d912618280d00c0380490fa4041d804006511015550b1450b40004403005460781c90312401800d460801313460006522130f0440264000c808541d20f01051958994004140700800520040341c421224440030b000078502044084010881046010a031a1403d0406003803003009040844c10418800002401c03038603650494a852580494115612039a402e00c642c02031000000417441040d050348103036001d141078001d0300c0c0203040080160070246030603a17400d03050b0f9204845c000441e00031800c032400d10b8000c5102d210301c6498121400c9646031814a801007413214000c0411242e04103091080c0041c03010034040000c1000012181044003104510340c4e413184099801d01544144000742d90030209056001a074040c0384a200e00d11945229800280c0e02c9000494418008583c207100082a0f8034254205002c915400400040d800c1c80c0c5480c4e5619548044510700c0b1803801c000380d815070b034141040000096a90103129118002854000240306100b441061010409a540072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 804046834 1250 804045584 804045601
    0xc020109030213271119050a0603021c151a0403051209011b080a081306050106031505011419110d090f0b12010e1e0c07020406050a1805 60
    0x544065074000b4401c00310906500f0001001d488000e00c110407444004c04801c103d600a01e5010014503072090100d9034084452040c030400c030260460190f2011541c2d1000951500d5050013074002e000c407568007590b280003009001c80c0e0050310300c0c11104c1c42c61401038113180d040e95554105055883c2d203d085d11000800302510070b0280a43d4001410602880b020386805081c501c0084c800050280c0368040a0103e080c600d0f0b81c0d004001002034801941000782030280e500c01c1950540c010400d19480f0b10200c00d540761b8400b01c9900743c0003c404a5990304078148010201e40b0640700030082446c00892032101c65841111f40d009100300c092041900c8050b036440c0a000b42c030000b1580745a03904403200d02d40c16103002001900f883c840d03452600000b43d408100214a041129107101202060703500a03481c0984110301c07100d000305080455010504800b03a581201001c190068401485080d282c240a00410045506942c000b911483c090901000750700d0000481003da660501000601580d40c101c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 804048084 1250 804046834 804046847
    0x150f030601031103120d0b0f060a120203042a0e061002030403120c05151b03060d0f0524010e09030c0a12031508030a11010c0905040915020f120901110a0c0201 70
    0x4075605c4041c0e011440b0940344802c2c4d400700c22020022542040c5240703442050160510417244201d000584500800900e07088540003150000c2c810791000d080d4a414644030b03101500c0728052520703400b41d03580c0c3c100001003006010681004003100ca00c1c0b1081c00ca0710010b0340c4c034402c910004204c0480026500600c0d402014110355142e042030903514907500d51441c080c0c8440003120040110058017079034682c110040d0094a01c50700f800b4040501c421a2900d0f2400a00542841110a407080c2e9407140f211039804502d5044111083d400344425504144c5c0e2880c9010006101c2445503109101d4004070f828001040300d505a0041548100d20200c2c0703600310043c04844541a106032a43c140001da64038001006091001c1c5c82e41d50400c0808c00315109909030380007080c0d03503000074020400c2403000b0320f4140d119880c3d0740d02c40d100700341d005500b0400c03440a903045a403940b5503a200100d00c5000c0020000d50b0300741d00141c000000c000d0115840e03000081405140a0102000300d40c43c042411a4003621 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 804049334 1250 804048084 804048103
    0x9040c03080304030c140a020d02240c0706271e0b160302011a030c040e07080609011515140c010e061602010b09010503061f03080a08150f030601031103 67
    0x8181e40d8a00e4581000303001315450f8103045a8081c207002004a110901051030422198001c0038014154259000c00c441d01ca00c3c1800e21842c001041c90400a04881100829240e60f80314090100703030b450034201030040000d48444006203c2c1e0103424014030407201d0406019107403c10314115000e0a80b07007204005614035084002e0810001071495081da4203c3c50080801c1d100354024040380312035182d00181c850900403695055031240484016919041d0042071507504c0c8402243d8043c0d50f183d82c0b841c03614100b901d11641c203955603190b41031048120400039028002a40180c1119400a20014114820025170001741f10b0302090394099082c0c02c0d04042c8001003c0012101e00f030920a0500b03e42e001080118800756182040220190502c061b415040390b4001b00600510f59990503c50329140d582041d240801080c1000480042e21801c0074104a4903960740c1d403100e500d080d41c0030f550040d0344001520320030b66003200801940c0d540050601d05696000e15411742c41c0c00c641c00030a140030a042d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 804050584 1250 804049334 804049343
    0xf0a0809070308040602060609011508010509060f0306010b0d05161b11060d0f050112020f04020c120309030a0215010803161b0b030405010b040533041407120e0c09040c03 75
    0x50000e41c91b07a000540c0b9001d0302d800c848944850366156003009000e02ea0740110000304408030010003462030910841540007201604009031303a807840780000c1c01c3c507000740c20524601a007c05d0030170105140d44103c80d408034501d6000c001c0c200c41541c001c0c044036100341d2410b80812042580c0b1007000041d282c0004101d801601058440c0500d6203401b02900c11214074800c1c0340d140400010700700c0488210017400326009031078402c10a0640f01408003960010050398a548074010001c040174140b0001184240c6520002d980c0f02c8104440081c20710140110441e4030304001401032040c0d00e00842260072920221078081c41c02c0545280000e4076100c14002104104541000050b250f05901c00640c445da101c2d5008108500ca20400c000c1120b1007960030f2051183d115080b480526034101545100c8841180400e042e01018070009041d10806461002440090000d0200745500b0465802c0d003404881c00034003240c0f80d848a42e0355902007100499201c1ca040c4400b26081c482c1c401000c0f00952f401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 804051834 1250 804050584 804050587
    0x1170408040e1314012702030304030b071805150307050c0c0916020708031216030f1a120f1b13020f0a090b090f01110c030a120909020f0a0809070308 66
    0x34082c3c0c0c02903120050801c0c3c60300041001e191160684c184117003c90740d0b0a42c807210710490700803140000c84290b007040803a018401000b012001c42c421003200da101d28080d940e503064800003e07001c031050044035808076001c0d40c00c000b800038034001d41c0f9060720b034809030340d151580d214290391a55a103031082c001c00d21600010352800340304402c98050f03c040e0314086150204c400440e901c0c014140e0328400c0d0420241c2111201c40485d0350024034a140841480040c500403455008403400d510484000c100b15450301080b90b2008043d908002401c05070000c140c2d0042e110f0004070261550b110301c041100c0c88690000e0500903041551044416806208000000c548840078007104104e6980f2444801c8003080c40d5900c0040c002c903000342290150900604403018082094005440f850341112401410f4028030030400300c0f5032010807044005038007400b800e900700007030044050042400b50700400301d850300402803071207440c415004881c05481c4c4c624000ca000d60f11001130364103161641d00000e00901c2e0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 804053084 1250 804051834 804051841
    0x80703150f0914060904240239100f0603051e01110a0210020d0b1e0a2310050f0f0d0f0c020c040b060c07091a040b01170408040e 57
    0x29200c4030800381c919803001000f074803c00e41000303080f00030110b440c43d5000d0380400000340040c0c02110142860003420007100400c00f490035242040c0e801c0b41d031100590461400207100c1690b0011004000703424001d2440c3e140b09031883c2d1564542c00054000400315846141f40030103460305500c0180150b41060584901850a0685108501c4100103610a0f90f01780104110004041011680484415001003503000107850304000650425103040094a964901c1c1807103540b94480b1000c54041d4091412100304c07145002c11044054a411624810010080c5030040c210b8040b411b10109a08880c05689040707616021203140c03244000c3c00e1200800415111034140f0b18001030a5203110039001400850111000c5c1c00c104c4000285000050784264800c10403414160b000c1c0e0345009014104074504000e41c1000c52400c80c49034040c2c4111542c030904590649540740c10111f920000705c4040c0b01c0c0c0c441c1100001c0001e000401e25280d0188440003260400072381004450050032500d5070340c0b54501c4c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 804054334 1250 804053084 804053099
    0x204050c090402070510061d07080a0219020c0405390c0a050307032303070e030703080c030a090f1a0c0a063b0d18090f05010f0b04050109030308070315 67
    0x8041e00c0710b202449040100c00700e2134111140d4444123080c001062044a40e03212541140e14040280c2996500c60b403c009590300c0d82d04003159250b498003c0d4000b080d0b86510042448100c41d0010302214540c2c150b800b40c400b043d060386612506044050070025105c1104d105103480b9446100700128517803042403202e008005002c00034194a50180d01c1d80400078203403010540300f50f000c0d140f29a03c503401c1007001a0070780d07004007001200c54170040c3c11030b0201d036100c1e03032207078a96030000302c2c40b02d8140c1c8003250041407254000e222001070b1078682c03084840645004183c48007803490065034000b509001c100240044401c01c10300001540004060240000d41284031034082c101098a00641e41c50400040300a0188085400c0904a5100400042519031011504d48900c0100001030350041240012450040c1c020103021070390380000010a9450700c1400c40703041e01240c1c040d4121100502c000c103c96070f0030800100459405051800c42e42c0d071408c004600401d5980f20011500385054804194034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 804055584 1250 804054334 804054343
    0xb18040612050715020606130e0a051f09080706050417040909020a08010b03100c0516150b150405040902010e031504030f032a02070b030c0a09050d0b040204050c0904020705 76
    0x81c051010f440c0850703124200c0c054121548104c002c0583e10000104a06041000c03020350407880403100021850380c0c5d02d10076410081c8210050b01c0303c1d0f120504280e5611039026032007101c2080350f6003c005c41c81c2c131503031204120700490b00c014006581d128005010f2007800d1241500050405041e90b0b5202e4403060f0030030042180742820380c0550115800401c5100b014411034061810050050540c0000c3c256542c0c003412282000008108040c070490819030620090990020320999601421488401112046030940d030307981c0784a43e4002c940d82113400045001c64080e907c003501d020640d88035600040c0d0f07489600400c00c80e05845500d4a051800708614500b50080e80700b980d4040c451580540220241d5001540329030140d9410101080d10a604c031107da18000042c2c01554505565141444010b4000700d549070113507440000c40030b091a0744030003168042c14040741c040640d111640c03980b11600c000248000e0003560f840b000708440403100e106641a005004100f0741d502c6140d441c00c01d484 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 804056834 1250 804055584 804055619
    0x14030c0d0513050a0e160e040e0c040e0d171314030a0201150812070f060207230d080112061b090509060f0d021302040f0b0702011e02070b180406 64
    0x703070901504040360038580315031200c08445c0c13502c0c02404071b40c43d052241030703a1031548600241800803031140e544031620343e40261200c1d081e4290203040500c1020080c4025106820396a10003900150825105c86402c060444100110030000340f01c1540e81a500304105505c0842c081c0002d0080ca40b4010f01c04070000c000c0440d14100d90090000c0d178010701c0302121203681f03400340a400380c011483c10029810640c0262070440c0c012403620509403d10f0f19280101d038482e00c400d90b01400c0c4100c211805410b491522000e034450340004206080005a005140c600c0601038400c02441501100d42481080d80021500d4007092200081d101220139015120f84042e104071400f511401c4001202443c022003088162140a07000100c0040540e08100168010744c10460115500740700c040b45100c90802018082c001c4903034680e64545032030001510121504c9204296900020014000c1983c0032506100325a041d6582c6030316107081e4070050b0051041c0da06284e40242c41d01500141d00e000183d5003c4a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 804058084 1250 804056834 804056857
    0x8032a0a0b041b030201020c1507020d0c170a020d140a0c080607200c04020a0521010518090c060f0f0d27080702060f040e160e0a05030a14030c0d05 65
    0x80b5000b1001c1c50b107560003d0720001c1e0140c0c00600d070705160341c2400714480044100c407424880c40c242c0c85500150000f0304207a800c0d1a443c000e05000e224100d8240e54004124646900034603140900c0d40c001040001c21080003840e420100500b005034060401c140402e107076010780d804680d1902c1c1d40400e03603030700c204276005400100d0086c010301e421001111210007400d40c0360041c1c00002201d9003408042c1d07020b0380c290310030000c0c1040104030004001c000c41d001c1a81000c1d40300b116502d001e007081807242c09003c0c49441ca80803a424001c20800015243c0f00200c0c0c144d6480d5200c0001c0000d0090300c0c040d009858060f07510000d4020203400320359212403d1401d010b03041400540c01c1024145140c412100c00920b104802c07c2000c5c0545000009846c0350554010030300d140a40f0343e40055140e01c800ea07031030700d5003120b00b0301c0e43d00030700b03401514020003080e0954901c20a58600f50020b0780e9101c0307101001d050005403084001300b01e0300070f00072600d03000c817404211000540111402851948005010031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 804059334 1250 804058084 804058103
    0x320609010b0405152b020307090f06170d0305150301020d090b1b04140a03120215010816030305070206070b011e0605030609060f04090b0114030c04050108032a0a0b04 73
    0x40e080444600c45451341d00f0082d0800e003041c00a00c0c10302203c1491076035001000c4061785d1070344005a40412100c00a003410450102e11049050840800d0790b13481d4008403581c1c02ca00307071071a080d48030020700502e50580d949800701d03ca4681c00c001984a010a082d4503030154000180e03015850525004103251900c10001c1c805241e450800c880c481a42c0d4003120729075901c0c01c00c01003109424008523410003010007000005181e55954a0b020011610040d407000f507005a000c090307014006006060042c00c480001e0007800101c07000030440b1410b580002030600c040480c0210540d22136509540c2c440e640290b01b40a0307941c40b0070148402c03400b03d0800b0082034048150205074a072050b0b00b92801441c000d002880310f9220002044840200b004c00075411031756071148240800c25142d0510300130001302c00c42110200a9905150800b8100c2d0100c501460520004111010340041184c10020042807204101c00c10b01d644000c01000004502025100f4110b0101c00c0c0003034801140d0065103d240290f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 804060584 1250 804059334 804059341
    0x703150f06170742020705220f0c02060115140a05030609180618010e010c0503190203090604020418080a0e0a121505070909151a030103320609010b0405 67
    0x9859002112410383c480703404d035481d48109250026107111183c0b4980140e5040f151103402040b5140c100721100d00c5009035000014002000c50702c103089000d00500c209015643c21038001a5030f030501803203450304a03081503003207103c028801c1103e04280c12607540d019540d1b60401d000186a50010380342e082c495003018000c6070300410702c5c0c0d00810b08201e400307001e810181e88128280356850400d106968540d500c40c0300c110007411081c81141e0841d5816100d41740c43c1d0030718070500b0403407114080e814541ea510403c1840003540c80022100d50055040700d01251101c04103050606800303080d078008105c610b000c20240222031700441c2c1003407108c005903849401e4075642c42c030702401c1130b152103005408242c500c20f8401024016400c281d9204c400341c144842c5a43e03440845208031261800802e03407500c0347d902c0600040000c04a0080348461a2034814155410741d11070203100c404043e90859600c0d12102c100204000368040102000307d1401990f1f0141b6021004074080d00590450038844d51500001 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 804061834 1250 804060584 804060629
    0x103050105180a0b0a0b12060708070c051c0e100305011a0406050909060f0d03080406050a06080304140f22050f192c030712020703150f061707 63
    0x144100c8082a0040043c1c00035034403210b82c07001c405410383c03050f292503c0e0788200c242ca07501010a450024000144803a1400b11002451031901900000402c008032482e02d01142c4002641d05a04104082c081c40d004c030020001e640b0640b03882407540d001004000304c041c1c131326056413041e4100d841c0c0c4840f44800003074483c941c1c4482d00c01d0780105404070b8070030b02510946042c82904140c0c000341c0a80501c07034919800700080c03440d8400c01011000505413801308002c210f1107005250708103407110024170990742407408007903c0740503d00820f1041d4602c4058424590340740c81103815030740d034050700c00036290b078800360252914425080c118000d00c5c20207010440000740c0c2e20000b84102c1c2c051043d4040a0140c5400c0e90140a0180d40f050361040041c1c4034800748100219081010141785004658801281ca0108000303035101c4580707010764000c0101000440c50f0380d007841c00510030280000464445142108000b851307a5044152646402d014161020000080794015108464603c8511001901c0e0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 804063084 1250 804061834 804061861
    0x10c02010b130203070c02090109060302040e07060f05071a0a02071407030305040612020903190209010801060e0402210d0908100b06041214030721020f0d051e0706050103050105 78
    0x75094111524614502e103824207603003d560062010320f0702c0c188111190300007507000d003800c0c0c2101d80c02940c2c1d000f00b00214075007441800444108038024000d564a4150b0282640403031a110f08103010340001c2403401c003c0300703010400801901d940340e804981420b550010082d00100c40403107070706c82c4904440b19010b0000079603000f2244d041d034840f031509082000880d5502c1480c1240b40c111074013440f2565a41c0c0c0e061101e281c622021a448a022948500402080700300603800000e259241400501c180100118601e0341b203501600c088401d880880d20007104c410300c0c101d540d0102c4c000e490701d0f500990b034043c0b010b80441c1e00382c804496800180c52541001c440c05100324941c00f0b075003008201b1200d0440110450900d010780c40c5601c548649140160440c2c2c8400c40c111004012a15510074043c00322294004002c83c03840104440400354000d2503564018400c3e04080c00f13800306022002801d1138814001820114548640702d80003403400350083c10003800101d805500301000599000342408 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 804064334 1250 804063084 804063101
    0x50d0c06030c02191b050909030d0903110109110a09020a0909150f03080306031903050a1d1c110409020604140a050d0f030e03010c051213060617010c0201 68
    0x1160512580c80c04000341c005200a08003501580556212009000c0c20503415041c024041c14840c1c080e2050004800200d9600d034000c10711406100707060005007800001a40c02000c0358403000910a4030605060f1140c40c1c00c4c4180c950150b0034500c401c010000c01c02070300c5442c42d0090356004e100d9521014080160702503110341c8000254040c40400140c1c17401d401024181c070144524480440c1c80d519800c0b2903101d190016a8001400001e000c01410b08121485004200d0714050000c111155002000c0c0c4c8282c048000c00c010701d1012458290038000300b0003440c044000c1030721041c80c1102070211002e0405140640e089026405140b42c17a04042c0100320095500a20161030301e41040e85540310070a28444450f0401d00940002c01e40d03880d02081c4400d80d5020346003114042500e40307001002c43c0d444401460080c1d0410003501c8096405c1420b070340501c6844c2516600607070300c0f41300300941c012501c0c10182480707080c400300284030012000e0254001c02e0f101c00900c100c4e100f801d0283e00781c91510 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 804065584 1250 804064334 804064343
    0x2210a020102101b143619050904051e0a06061202330417010e0d12270b040b070f05271005090301140f0103020103180609050c0a050d 59
    0x8013411821031041000e41d400c10003a01c2004d0500401880c40c3e48681201c0d2034001c060300410816511206a009003960750807401c880300342d1001115a421604415240b0440f03001d0243c103c00318040110501c070360041c04440e0b80110300d40d00222000030350f6400c3e240b0f005032400342c580f50021171100001c0049201141c2c018013040d50350400300040d40c0e2440d0b44101e485588034082852004c199640f24000c100401d00442c5501e42e00143d10b1010b4212280c6c03924000c503030390140c0a40511550002200d0707841034000500060464080d807903060030410307541d84480184034003403035903c10441c8030031500c4d02540c045d02d01522191396140b02511004282001e100c003081d0248070784110b06800b20808044403007800146d03603030868144040798222410b510603c01103031000c24904507500b000d20030f0b82d81404e91803031201e00c103003440d0329503410000042c0000303410035899850039040c0e2a0303004e80c0080c009078004010042c03486a41812a2603020141c00d0310b12940406070002403910300910300b4540302d07800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 804066834 1250 804065584 804065621
    0x30b030c0f01050a0203040e070509130b0f040f060b070606150c050a1b053706120902180915010909420209030d03141302210a02010210 60
    0x1200107583e140c0160a044003107100400001c140c40040007500ca01404c803903241c0d5078407114180c2c10001c05580c05c3e0302d0181114502840b010132582c0d0010707180c02c4184280d4000510305440760914001d4035007038100311102c04000075010104140703a0302810071a8444101800010702d0b004048038221410341c40a0102d5000c4030702c0f0004501000001468074242035100c0602c26518404540c10814541581d203124104503401e183c04000e612041030544200c8005600b07060401c0c0016000042040e000780501c1e91351460803086460307101c0914020b41185158900c1d5113800e5903203607071b1407003100106400ca96101c00002180f9841380943d01980ea4000010848000d150007015001c00300c036003207022036815880700001600c01c80c4c07400003821508504e026a03100c2c004028940b4000c0f0140340e410400d07207006540b5000c41085212142c00004840307031032000b82c01c00d00015a0f8080c0b00080381d840c52040700900011090000b803401d854601c00e801740e45400004401e090215001e02d4609040c0300c01e03 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 804068084 1250 804066834 804066859
    0x1801180e0c0d06081c030b010906051b012d0501050a031202071e1e0501050307050f0d0f02030f1b04050d0f05030a0c2a05210109080a030b030c 63
    0x92100302a80028103480d503509203501074840d601038840710b502c6600c0c281c01034042d4010700d2030800030040c3c0151250600744030032840100000c12402c054403c9004020010900360000750301c00d4a40000702001030001c0c0007030301e001c3c100420a40644205a0b49c420191038403001c4150482c0140b40c101d0300020003907101c0754503580341c00320789400120b020403c50042ca14040750310011180e0810109002c10020001a41008501424080c03880c00c911020340910030f04000c05d80c1d00108582d80300c03c6a02d406c82e155010040c0180361401101040e9075041d003030000211480d400356002c2c502c5500851440480c035141d00000110003581e1001105004208010038441e500b0451044000c0510411822166550940b0341c582190010000c4900151000d48650144005052202c825080021004804031054240190b003070f8014440c0d9805080c800c0541850140c3c100c00c1080c80303070080f400a009200701450803400d40d07800001228046450250701071010b040c0060540000e0f000504120080340 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 804069334 1250 804068084 804068099
    0x1204030f02031c120e120a26041212020901020c040b0109050a09050703110c0a17091906180f05310c030c034a03180118 53
    0x2000800c05981601c40c0300c018280b60019403800308284211a80d821100a01e04015103007501c1d41a03d402c003296020a0b114682c45000074200c0307542c1d04207420981c6011300000031048040303882110868404403010100320070b01c6015008507800215a81c2e0715a02064011018001c80c00340e40c4010703005901a860310846428640c3c013002420505041454480d035546001598100c025040540b0564035201880101501270081200c0c0086600d4214200031540072050f548840300e81024000750013a040c0c400b100015030084555501c009012030500b02c1007051608881c3c2d940b8851080000c0744108111000220030362502c0c15661a600e6407030b9911305d4082089000b6586180300c0001b0550741220085020b48002c1101590f503c0b40d0012910481225024003110748070303a2044140741c1002607a07121010500024581000c40d0001005040070052460061010b0b46088003046000e23491040d51a0030f00201a02003441a94400c552058404c0011203466262881c0c410074003004420600003403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 804070584 1250 804069334 804069353
    0x8070207092a110d02010603021309170f1902030a2a060515191e0e0c070611041d01081501060c050a0501020d020403031b020f0415051e09010602120403 67
    0x244201e103484000e03e00700b86030741030910100701d2145003d83c1d5108030400031810f0500030442c102503650070821141286803030b0100101011101d110b036802e80058040601442c0303905482100361404220f00c1d0b00d121060b006036890b40446005c1000c03d4019611241001d0890010b55a00c000ba503501c0180412640d12803014101c040c2800709081402c51a030f071b266458900d40b00e20000111107400540c58034158005503901c1a0105c40c1da4040c3e124a014040c090f12071100a030400a910300b03869482d85541040c200a081c50304c107072401305600040c000340c801f0840c540400c0040040d82c42d1003151b681d0305500380c3d031012881c83c149029400500100f00042c02070341c41c036106034000d2041d02e05080e15682e40e507007240e228401e032a4400f40e01003000d005140c6e10644104010080c116881c00000c006d80005000e00c4c00e00412602c035545a81c04421042c00d141301c244018031003e003000009800e50041c3c0d00d41e1400902d8441d0144d550b200002583d58070008440802c0b1065141503403030300d030440c0c0300e00110 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 804071834 1250 804070584 804070661
    0x60d12050c0c090f07080a0501030c0e1f0f06200a02010e211c030b0f040b0a05040e0c04050c03100315021b010509100920040b030601060807020709 65
    0x180c020b15850040e0ba80350307100d6041c850075038031228200fa07192800014180d8a0081c29040c0310710324080050000030800c1400105032080106180790559544902d0601e928002c2809074a6601d0540000744104070f03004200d0a4565036250051180500c5032804010441042480510b030700008a540140d4016452410811707806002092091490b4112030300003030019549240c1644008030400300c0039918051640d84104500d420f209441107c070000d50030600300760015115542d640981c42c41c0d81e5442c4a40d100a11000e4028010000030b05a80703520340070040841070180b4188800205902854811213107c0c1140f0040c0303a0b011800c640301c01446007409000210134690030003005071490b0030603001544100d00d24002040030f251001c403941c10b00b8903c4e88101c0016040c8a90751000446624403441d4072522008100010300152002074080c148801c80960180100c0c2c1c0040f50303940c1e010040705c0c0b1464160b0200c0e10450f5403805200c00300c40c00041d101700c05482440034400780d405042400721a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 804073084 1250 804071834 804071857
    0x503031c110f0318060606030105030d140918012309070305040206070f0b07020d08010609060806030c04050c131d060d0302010906060b070302070b03060105160606090c0305010e060d1205 82
    0xe02082d0400c0d0001c0d039109840920043e03100c1020140543e900300001c60f800340301501ca40d03056501d00b8021a60340c2410705002000e0048500b28202a0000308090302c0f5403d5004010b9051140c0000d040c62490900303025014800d8541c2480415030083c1c4911400c6c04600582180d40503611090101e004100282c0700700d902c58010802900419022024892001e000d811161240d0500d581e01a142882241407031051024100041158030b81040014007110070f1428005d099541e041b0001c1d0410b0003e880c0310743d10a1400c000d002101c20698080c01541f40f011201c4151300d40c4501c10520482e072030034031250078404e801e40001d085003800302c00c2020346440b900001c41c4056003556001d058030815001b62400c03240100c0c0c0030080c140d041010300d004001c18000305203141061000240b4911402c0c08120781d0f840111086030811559034002c7d00145540d890400428080c1e44000700640028420000f00c00c040c5408503689207029075191540030741c080d500c04000d5004000076030390364000290308817 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 804074334 1250 804073084 804073087
    0x604080412050111040b0a23270307090605120109050c1026060102010b010306050d0f021908030d0605220f11030a150816060c0c0506070f0203070503031c11 69
    0x75180d075404000780010b0b042c2c0440c11604d0f9042ca0400500b88d008586019040280660341d0143d01c601d040b04a840b08460500d2003040f0342d000c8801500215181c8441a8241c4583c00300016455200e6000800361030040303c0c41d664004641101310f090700c010290140264106494144040c0b5081980041c031074100d003030205507104404050392818009180c0710030b00b0f6080380200b001c4c5603820f201d5048503480c2403e04001190410010491095406100a08250840752200250756446c40c00071250a0354600b10038046450700c0c0c445441e50030050000105504248001c5040e02d4005130704035407803036890b0205d100547c085861101800401c102401c03403030340e640c0090b8040b20800004610030b181c0c0b010041001d00c00119003840304101584116066040241600800d03000380350308200312503951900301c0c590b407002d0400103d2041140d10403a8006400a03010080103100144000340c1802101554100b41c0d8030340c00d00d5140d00c1048a25035461441072140f81d01700f0760550002c0e0200c0103501d840ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 804075584 1250 804074334 804074351
    0xf081302040e100f020421031803060b01080a0905031204060f0906060f120f08221d24130209030a08070b060f010c20030303071106010806040804120501 67
    0xc0d045030410302d03040406811140f2404031882079405500c2101c2c101c030300114542494600500f09800380b00d4082c0034942d00c44c0040109062150040e864080c00c52281d00c1c080e1917480ca080b10041a61003034850104014a0000b414002144650194560003d010b50314080c545800351100311402841112203941c1e61422941103640c52061000080c0700c2d4038002070050404186020441055000c62030354035054001c2c4c400038548801818200c0d900144958895514411900c0101890300300c50640e409400d03c0000c0d848403840e06481084032800b41100c10707844106000c10414464007264a400c8401902c824407810070b40108a448200780c203006003020b05c417000286c20f01c00501802c0c1d500540100301c45081c41030880000b03401410031143c00c1c0701c03403420b50f002070b1a01080e545c4c0036080c50070852400d41d0940c41c80c04031138049480201034039681e140246015056032000781c41840e5030310a840c00070603d10000908980640e8114510174101441c118504450101c2c0402c100d6455483d603001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 804076834 1250 804075584 804075589
    0x70804020111031903320c0706020d020712090509010605090a23030d03020310210501050106050d2007060905070b131703030f0a0b0103020705191e030f081302 70
    0x4d00b00710842a404144484840000101501c0c410758244140c0080801c51407480c0020300e0883c01030600140c3d806c0480c0c2d441e404040140c1c01289000340c8924000114504c1c926415070040011906c6414807a040d058445070480700001580a50750300031410b4401804904d0144014020200000302146c001070303207d040f6180b80c08468100500c0f0074958240e9070398a850207020702c0d55102c0d210324046056291448030750340b0804a80c4180700c94050740000c4e0f000804d0010580ca01d403150444001e1101b03580d64000240240c1c4841103c88486251115200c0c20a011107161048262a211502d00f492000e4542c2c000801c451381080b1a80d114600700040c06507030400250050781218500d1144240c940002c00b1540111000000b445030800c00c204400504031040458000c1d90b4002d00280c100c01c0000140c00074071410f280540030f80704034600c000a449622080681d142d100303054202c0419044103000040241030000107010404640254035014811282264081c1c403002c85c40407001c003243c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 804078084 1250 804076834 804076837
    0xf0403050d09060c0b0c130e0f07032409020919060507051b060a1404090207081309050c340b24010509061303080c0f010c03050f07080402011103 64
    0x2044400380c0020036000320250700440b032440100001d08004075100d02aa50320014100010b1901c5481580420542840c5a425142002400740100b0000803814031420340c1000d1034045038039400003410300020101c08402ca9148100f0100301a0021200342e003004020000b940000702c440b508034a1955282c107074a8003481034080101401d441d800d0791141c1508180b4108410003010b41141544640b85250944955003201d1078072a40d860305080e850a44440c41c405841254060102c40e4000f1800000f882007481c020010300f50000b040207803c59a80c0c1c0c2c160142c803400c130b400c91900d82083c40428040707500c201c0000c40c1010340d90072080b01d40108080004403040805010303030b01100c0c5141082013a6a1103607502d03410307500009100004440100c0002c0442c42610340d0280290004110b20b100c90580480c4c00001d5507011001d00c0e103424800c031240c1d94410980d0b0301315030658241070940707070303102c0c0684910303809000604e03212411030352402415100700c20003038000ca041040d040054480e04000f1300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 804079334 1250 804078084 804078089
    0xa110c070504110c0a0b01032a03080d060906080c03010e01060305070b25111e030601090213090e03070b01090c080a0e03210711071d061f0c0c090e0a1103030f04 71
    0x3403646c800e0754114140743c1510102c03042e07581c411000c046c00c0620000300e000c8105007241c0d44005015038581144c10440c010b81042d91001c8201800c1401c08101d480000c20f40e1003e0f808c042d002000b203115201151820b8905a220180050300402014044409154001c0c00c40c002c1c0c251031104201d080c510000c07a4041d520300d065a100c00c0c0c4415010207407034294518048080c24114046014810100090311400306104081c6059400620f00c1c66036038101c0c04180040000ba0000c0280c04101c1d068141c80b80d1040307004440c20360003213001099a42ca180305d40f41c0320420b5559003114030355840300d10760001c1c03006e5005900140f005001050400000d055461100f08100654840358102100c1c0a0074280e1030884148594121041c2030004404500441c812005210201c2c031050300d402011a10701078070750340500090901500c1102099411142e50346e8842d1050780c0203240e166aa0605d4811a20070b00034002c0180c000110680100e4694522900d1480005041da46414007201c81034144d513200707a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 804080584 1250 804079334 804079343
    0x21080c060a051005030c01170907080a0f0308010b030c03011e030813050909030a0c1b03020d0606060e0d02030c09071803110a090221091002030109050a110c070504110c0a 75
    0x24000c100c1ca07002a03c00c00d00050005034010715520780d8180000e4085200c24810300e00440f4400006400860108420b6000b05110030a5440305402070601c4202054041c07019170204c1d1400f400000c17401014403c40e80310b583e0802159040da401c240803550351100d0354a004076882b500d55000301c0801c00303280040801c0d0b0a4554a900004d161409100d82414014540003890b0014805007010b103410140103044151b20941161010829840d40c001907c0035420103900102c100841c0010400703194007210548040b038035149040c00109040140d04e00c03000d000203405411600c3c40812a0420945a0360041900d08128507102c0c02c10100710418080c5a200b610300a060002401260170800c090354081c0041010075031408207400540356000c00b02c404160021041040003400b242400e2103580103400258900b50758039651000b000d00902829107141502c586000014043c0300d407810210b4658042c0d010242008a01c0c0404010041c298000c0750741c103840d42086044a01c103400e1001c1201e84c0e108 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 804081834 1250 804080584 804080591
    0x30d1b0b070507050d1e05030c1908070201060e01030807030810050618040f15180f020a08150109081f0f090308270309040207080d06081e03030121080c060a 69
    0x101c0c102185040058030280082c001ca2105d04103040d2414800440401b50740e081140d42d07a01d8609c8040214420100d6a000852085039003c0c1139541c00350034a40074607041c2c3d009105280e107803000c03400210804e10000b008043c0030480c00c030000c0e025010240d40800449214042f0315501e10100c0d08031350140050341c4494800c100c90a02c0c40c90184241e00440d01502d0323042080114401c0000003249041c010b040c00e009401041c62a811900e800c0789883d040e0b40350095484031845400500240402c0c0d8841401280b90844160994800c14200e001c42c1c8a44005200c500428214400d2003018002010b940c207484001450808616010301d0f5141886507403208590710381480d401c005001400c03444d800007541c585180001600c00001d8502c0d002c8201ca00598405062070300501c42d00c01c501342480014148980000c4840300821415100070030851403121b4119144800c9442c2e01c000d0181c1940e014184010030154110015111003851064109a2810308400045c62620600712060100c41ea01e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 804083084 1250 804081834 804081847
    0x20f130c022104150507051f0212010b091324030f03030605030d09090507120f0504030e060703080109151707081002040b07170d0212010e0601020705030d1b0b0705 72
    0x2001c01500c0d82200901c012420f190800a1000c60003000c0c007482803c03c14040713214014048280700d40c0309299114002c1a0711492806507800207900020450590a18101c00010307201010008560010000801c0100358013441600400200f0740c4000325840420141950410014400403510285000f2007211041c0c4d152032034000d09541090300070300e001e0b421102480340501d82241140f0255000d0400114a66940000442d038101c851283c0950703e600382003050711009110303400365009901954078240120186800d10010b4450b0180040c000307240080104040c1c80d4984c0403c8003202140b0380c92003070b6544c1c0c00d408601c40400c80d660041c9504680c004000b02e2500300000b6a12141c0320131b040d424140360440100303503402a214050010006012a440045486400c90310140451141151100d070b62800742e441d00f200034040e102c1002240d90205075258000a103160403030310700900030080074890b15411500c0707102a580a074841b801240d80d040c0017079600f1089a10032501c55650645804 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 804084334 1250 804083084 804083113
    0xe010e0102120a0c0f0516081201120b090c01091802040911030f07091a09032a040b040605061e0903031803150903040b0a12060b032e03020f130c02 65
    0x1660305403a6001d000c8031000408401d038000c0280e890880c1d0002d004000d100c11f82c2440300440c07050034854001039052800118203001d07511031034945180100b034003d6550f61030810055480e20224155400310300441c01c10400070440e076140340c1150f20760000150800d952082080199164400c0c00d0010a0011080080031408411000d600c24510300d880610175240113900d1728580e2000070420020100058100c10f113860030040b07104441e140b080d402422417030f889040c403283c055211400d8402c50520340e2003586445c0c0360040701c0035114010a03036441e05901007001c040d0300d903921268880318101840b002d00340e66000d00207072544032548035811083d8540441018208080815860602d418402c1071007c0e1940020580e0151140d88800755a2400144c2080d6400506126118000c81c1060b0300032402a40d10b0003c0c41c0583c400c9080340c4075618424914030226408070007010b0f03020940e850100003528081d884401d4042001e404002141c0020150b00141c85d644d81000c0b0150717001031101003030803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 804085584 1250 804084334 804084341
    0x501060504080d080402090609041e0303150e150f031014060a0e09071401090506041d10030308160c08030a06060e0d0c0b2a07080c01031e0e010e0102120a 68
    0x42d03c25103000c10080c509940010f40d00344015019038050746907140010304100c20350011800125040c10030940341203040c03400a02030030824030250110700181c0000680000c00c1c2c403105024403071040c00c0c42802c40031842400b14122151081c2a4103125407450441c08440030710820a018880402c028203500d0000d0030b200c5080700591014881c0301c1c0d090200404880c000c101c400542e10301c40e01484550f1460700040313030108402d420507544440006000510a1929015030300d103041502d000320203035600c141d1080c0400041c9d100140c040798400e4001100d8501c0d0400c1c4085080d010b0400c1c400a400d030740c0360000550000c81e90f90031041c2d174402c1c00b0310250790400715040025100700d038060506100307a41c0d41a2400d246204003000d00c10045002081301100009241400d00d000041000c5803040c4000156600054414230340ba07030085004900f003652180c000d91120328803050040e095420124000e00080007240d06406007556200d80101a0070301c03c0c0010f05e9400c4a600406d091400c0c07403000700048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 804086834 1250 804085584 804085603
    0x40f0f060f05070213050601020309130902040e0606130c03090f0303091106040b1e07080712110706090e06030a150204140909190c0e0c0a0f020708030f0904090501050106050408 78
    0x601400340303c18401030340c41009944000c00516004105d0b07844441c0181d140d40260303011036074001c030200c0080032240b4207540a089114021a010700101c92030034041c540342c000644960741c2082862400310f0700016150090180f66405240c0096808a203031690310b04094650300c2200040e8a521441c0700740300c4000b80c0345070091000c844c0b4900c3e081c40d1011000d00c5201e100204000142c0e11a00f0000704100c3e1000d03110103070341084440d82d036601c3c1031900c801c90410b50000900420084e190300448800f0000700c3c202540d415841d01c8181c24108420b542a20f40000c007119818828813940c140060306204c02600ca0071104040561100d0410507131180c10210031540d1805806a00104202d013500051549294600b0300c2404640310304d982400d07003203511982c01c801102005c1070700748809461160000c106a951640e0350745403005103194100d0329503c1c1449416001e038000d110007500050030100508440c10020300001d807012855441d207094031400d80c0b052000c41d001280820540e1030500c07a0210 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 804088084 1250 804086834 804086837
    0x105070201050705180a03141e01050415091103070f0f17030301121a0702070311060711130e10020a0e0102030a090902030c281b0b0c0708040f0f060f 66
    0x2245410f181c0140240038000c000019800000f204950355154120248007540c1c0202d105226007040c08203490b5a11601c40c00e140700c00ca41080d2403084c0c40b0040c4070341e6014035030020111007040b8901c0d200c94003a009903403003942e0302d40325926128000e9a080140c080106550070b807a010a034500560320401c407819500140303d4050030754034242608030101c203d90543d040b03404184088400c03400e010044809101400d80c50003c110141700b0000e80000390001124842c0000306c0d04c545860f01444444e000d500c80040481c41c0400140d41c1c90f10b007034503100e1495410301d207000400c4031400304c609140902c41741980b4074107580043c507501510b5100480c05083c0300280021440c20004810080c14040d040c0302d410242d40e400f10215400b02c0040c401c031004000c1049600c0c02c0c86a40f034800d511180c0c8422509000704810711040750101500c404000300d450380180d00040e05a50b401428803d950003954100c0340c000302001f01280c04400e4501c848007800464a110701001c2c01e040002d000c504c1414190030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 804089334 1250 804088084 804088091
    0x100902030f07020f0d0203120903070f0c140103110706050a11040909120f050301091119021006170a2406060c1202010501050f10030e0d0c020301060512151b03040308090105070201 79
    0x3084e240c0000480f1108c041c0070300211080e940e0180d000d4103500030074074010241001d80ea00300c801d01041603442425150900074251100600703074015000c4821b0b245090035203200034030a607008610154409940801740480204140d4004460409241d0007070708400041561461520f00f84810191a14406050707801c060403a965141030282c03580c00144280c0ca420340e10380c11034800340c02a907400d581c5030140140b05003c44201840c4040d403030f254a407054528103403900c100000c0d5419054850381e64025684054200e02005407210040420786d1403810307012010340c0f40c1540f4000b91920490340200f0803a0342d07014081c00301d480c0c11201c90006940a40440e0f04140051205940301030071a1012001102e0039441a40240c9081d80608a00071034801503024043c000404540c00143c46a401d5100302c0080250b83e8540c420072020859007005141681c2c00750320100c88905a403c4819001060f0003850701041494401d14151580122021000101400180324000500b40100c0d0f410401c240003d2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 804090584 1250 804089334 804089353
    0x42c0111030c03060d0f0b01030602040501020f0c0105041211030304060c0210020d0912230705190e040f05070b041e05011e03021b010615021c05090603100902030f07020f 75
    0x50020b00001c0e00c1c4c01d02c166882c89410003003001c0d82c80c64054903584410032580781c0da56810203a0081d08240709a0b405402020742100c003188011820004411050b1a1242802c1c01d01609030100b004c080012100301a080240c40704940e03040001d04024032243d9541030015150b44144640e0003c0c1d52050401d6611a4400c0c4035032542050401040d00e15121018004283d9410055101c44480c0700603250300040c2402c0c00e21882e4007041000070b07101c00703070342078400c03140d6420610041c203441d0b1142d68002c3c0c0d40440842c0028120000004101d0702480480c2e95160f12425000800d50041d4000c06010304041341813a004189004640c0c0144000d082650100341d21030041d00320320400f901c1e540b08140e800160400d4803802a481c0fa0030040c40000200071098030341d215480304035858101e08015105401e02004410003104410004624650f5500d040c401d00d40107000d020f800c042c002d440038800060b000b1a023505603101551188141c201c1010340e5040c203040290400350103002c64050ba81041106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 804091834 1250 804090584 804090601
    0x90a0b0c060105040f0f0212010501021207080f131a03240d0f0311010c08040b09010b030a11130515130506030c061605060c0a02010e03040f060806042c011103 70
    0x4141c11528180c13800701c3c0901c2c2040e0350030021b0283c6540420b0340c81c40402c0400c182000801c4140c1a07a40030f808480301095030481d080034502035000300a1508404018001c030404059002c1c09140f200784040c24441a140d40c03002054016000e0744055441c404410809689940d15070b050300300d00380300b1241c00c1d200e203000b004c00c040508011000e040522a00072a5081501c180c846a41c555001e00081004800103400208884000d0310280c0300005500041801c00ba418421794401480c010700a2410701d43e6a80d03035100c42050310020b981c0c03241d485404040d17000064001d0312f12804200b080700d6007464a9100b085070340803a20107000e004901c0c200c01c021054400080b041c2c0705480440d0402d4403424070194011040000f51002800b0340699020b00511030754802c050141ca070704680080c4a0141460480f660741e01a521901c070140da100241000518011400d060700050040d002050740204402402d00103030201c0d00005904000c0d84a08600c04800e00c90740080c0c4da030000c060761441c20311466 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 804093084 1250 804091834 804091843
    0x151e070c0c05061c06060f080a0c0905090702030d050a0204080d0804051e03070c0e0412140906030915042906150318010c170603061003060b01050403051002090a0b0c 73
    0x4280c003c200006011103c0c1d0440b144100a400201006004a6880d00c900501447d10b0001202c00f050b040c201195503184640110311040c091581c038818954640010001002c0010b42090254081001202c8000c0198000c05e4440c185601000d0382c2c1d2850006128503100c83c1031074440c108044482071000080c1e0104004944244190301c00c119003601408203030551041c1440140070010b42d68000400041908515100f107015048461220006507020307074080c24421f8074495400d004004808003850001d0245420140c103800f2a41041403450044450700425901680c040c4080c0b034640c1842e00d600c40b107400e84140400c400b80320314200f01d400f00340725481c100b01040c1c0c03004002c800038104181d290f543d2105152200028002c0c20080311000c0c0511207400055281c60280c4c20005030641800602070b8000d5055689020b9124a1a2104801041c4500d110340c1000001c00000000c00e000f004261000c00e000c060041c2d90f00d222104220900b04980d0007500040c5003480088040c00000c0f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 804094334 1250 804093084 804093089
    0x9010e06010e0a0b03030319140f220f03090f0609081906020903161a04050906091b04060302130807180905031605010b01030b012f151e070c0c 63
    0x1020442d00f600c03541521000ba02e01c0c0d201080d0035201c04420003580c041080e03440c01080d444d0f01030030050303000000340c09201128200c55400f04000c2000c0031035544a070309504101c4046031000c00c1413000c00b4503a503160840108810540001c4d079070402c24445e600c0d0a214881c024101030901c1c860303d510f041e0445450b040d201c980926040012000b10007404010f4044070200d00004054410b0940e0800d210034a0740180e0007003004800040e05000300c203079079001c11281030320b40040c820203881d42c4134020070902080c0144905400c0c050488a04242c0c01c0b80310260000d04025200580ca500520300d004103085080d5001c4015540400d10421075100c4901e1014003d081405020540441c00d007840e0b0324610680c0442000e103241d024021040c050190300111503011309981c14828145400300440c0e0f8800055450102d4040303141d0188040c1854000305283c1c11002d82c11340e5601c0094407003201041404480d86440c210901c49190030442c40849565449119030400350301860064403003070140b003140d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 804095584 1250 804094334 804094349
    0x3071407020a080102030903181e19080601180e0604080f3a051608160c0501020309210c030406030c051b0c040c08010510031d0a030306030b09010e0601 67
    0x24405007036440c0c05900d1005451a03000079541c070309040402d80d80ea580321822401c8900f030100d000360203d00d03004603d54003880350071100c15420140c440c01c0000e0080104400d41e02640c5600c000690a02c06001d01402040c2c0d0050010350810301d4000d40c01628541e40c0140059004841000300040703850003031f6030001c040e02c0b0880381c84040b11f943c0007040881c2c019020040603000e00e050111040c01b00752040140340424014412074545001050003844422072450210f0120b0b000100c0020794aa0346403e2200c1078580444003000d107440d030702d003240d1081d1100f8650360081d40380c401c0081d80010f011184058040030440c23401c0300540c01c103a00c82c050303805104205074491981c15a070a10030710a407184404811030b04140c3c84451910a959070031020b85043c015801e060000355054000c0590504031000504110a8030030401c0c811001044901103428081003030b10f0780340009000400001c8403d61094078000b48880c02c50800480102008001d107000303a041c40002c5000000104410b1b0449240 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 804096834 1250 804095584 804095587
    0x14041104090213170303160518040f0609140a06051f120608030a0804110d0c031403040b0304050307020a092a0905120105100b27040b041e0b06030714 66
    0x742100f8003220b0040c3c1c452460300d84942040000c5110100095008a40000342002c501000000990321806100102004001c0358000c00201c1e0410350000c943c42e0080d0034002490607207500b0220103c588107150304800841c41401c1000400b00c80c41944040c3c1000c540b003007903410b01d0700020f49010580c80503810030001c00c44c01e12840d21440e500040050522007003501d85031102650000e000b64000c0b0740075110701c03c004c0524845400d000e0000382410f84c010804d0300d406811901d60603042c083c0e94042901a200c00c00000402003101d00c06107002e60b224001455581d001da00410140d480c0b1600a0f18009183c0081180307002380c1d0501b060500c0e1820040c0200072081d54105581c0c215403984820341280d440c617104103400c0303019800544115003201d0184501600c8070311444060040204640e2120300e90911160000c0c1d000990b490410302c000d1000ca912171030071000c01c0603a03d02100c000b80e10b182c42180d404200d60315004010310743c1e0b03069802c1c608614040e000106024031030308015580420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 804098084 1250 804096834 804096847
    0x304050301060e0f070c0f170a1e1b0c051c150506093702070309080604050a080d06050618030c01081b090301021b060906010f0b1e160c140411040902 66
    0x4411f0300c0e000d03100d500654007807804800d2694444640e44244407480c000742d40b09200c101006205101d180104e5850b5541c10364005003400034121010f40c40100781c40c01c1c0340e80c8400141c190380d100841c038a501d034054004c0101404528118441145031304480c01d08c0c45c100000c05c4100e855244202e070f4030401c4014111202200303108504020070f41610f01c00360000e04207203102110060340e0014511588070303503110301100c2d42c2d5240103a1590030555004210f0b804c5501001c000c00c2032030020b0807162141c0000001d0301a0b0f81e40000f40f450348403444083c644800039040d00c246150070701c0103a07000f0700282801ca056280030b80403020885040b070444440c50360f002c11403200350f80b800d50503074a6415200c41c5c84801d007607004404558814045501c0811403040d4800401c0f034866018005080390700000103e810b00380c07291003607900381c04180c0c0400a1500c042c07000070b00b5048681100000f0f10301079110240c1c01d600f0540d0301e40e1040340020445010741d0501460702c4500c00034904440459518403001601c0c0e00 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 804099334 1250 804098084 804098093
    0x1170a150b0306180f2109011b060c030e0303100e0903070f08070507060c2d150c0e011803020609010c020916020c0109080a03080402150c0304050301060e0f070c 71
    0x45089642e401d8400d400410201e000c0710980d022150812100f252804101c0c01c24055551260111a0303540c4584a18060301310903040740070303215486050400007218044105183c000301400c000696615443e6403503100000c0d090302c200c180d102d01d42c80166195140005d080652410780c0c3c41500c40c108030707030300005209500500c191610b5550210419114155609160382c60750002c003c1582c1600400800280b03a502a0702c0310006507500c20041078049298000740e080c5e048240c8420001c483c0400305183c0014071072601000700f0007101c8400501410246801004136200a005a040c002c26100c80340010620340c5101c011640d04580c4550f480c02002c0040b61021024131000b500040304809000b02030b100d03850101300d0012164203d0300645021801120340b15580d2190305c01540014910f000403911409a555101d800640518241450810ba83c0e074180c0c0601210400c0e81c10202d0288120315080c01500002e00a042d024401b50400240103030301c104c8050452020f10403811580000c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 804100584 1250 804099334 804099341
    0xc020112060503010c0c050708030424091205011b080705040306180609051c0306050a03080c1204140f1807050d1401182a03090302070510020705030601170a15 70
    0x30b003000707030090018000440000c0c08950700310b0402c8440740100000825800030010075941166080242c1c40599059013407174042c1c042814041c00e0030480715410224149001000d01c0e11124032900000803680c080c4001c22701d086000d2103d007400c0040f80c809200420303520205883c141c0c1d801010008105031101c079284110381c1c1680e0000d00c024100450a000e005011554a60251031010b40c24504c15014004404031199402240da0103840c071002400860710b42005444441c0781081256014503481d000307051b81d82c000c0d03401240c81e48402d40340300c140b07401c0441c20200241c41c16100080180061501d0038024403009000c4000c1090109211500882036000703501e01000d0507240c4101c43d61107650005100482c1601c80740014140f05100b014891500c4038000024400b562200c05d80f4605441140030b0245108190114400d1440205903540c46d01020315007501c1980003041c9940c6070000741411300605902029210110710102070b40240e0111b41010515440130213103072100e210045441c001c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 804101834 1250 804100584 804100589
    0x6040e0f0d030504120908030a0305060d02041d0d11061303020703122003160201051b1b040b120a170c0115050120070b030604140a020d05060d02010c02011206 70
    0x1403007000481203070710b81c250f8400c038011400b0b0f80c841400307081d00440503203400f4894816980240d1041001c8002075100e984215004a0000c00504a0400e0b640014056a024100410070200c45103d42c140012041040b281d681007142040800300100c501141d80b1903d00811006002c812440080c0c1018800d00030301c0091540b00700000411101d0301001401d081500652844c00c0c0712091038a83c6c05030000007564080c1500e100d041e07085541c15401140c0d1504103521041c9103210040117130300340131014440060070a211300c9104020100280401c802e1710000c0004a0042c410b0991544280c00e011800000d1742ea00202201c5050f00d0708101948507105482103046554a0240a04480c2901d100ba003421114240c0e03038500907501c180e07110300c2d009507200c80d00c054541c452441080001d0200d0065907106400920000d050301d44104c644100850844071994020f5000401c8413122540d031113410380192040e115040e88001c0b40d070020f1b22018a500001e814441003080c1440c000c495034204001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 804103084 1250 804101834 804101863
    0x6170c131205060a18242c0106060306030503030c180d03030c023c0102070c060c03180b0f0304110406080a0209090309030703020d030e0907120506010e030606040e 72
    0x880005070514548074a0141c03200031605050024614203a8121001c070040b2079004504040c0349170342103200249a007106c03481445100c1c0c4440360407080c9001001c090b0001c04a80b1600e01d82605008500c0b03003103039400e410040a02d494a201030000c6070000096030707800302004010641c0c40c5400485200b854000710001070740030b021545c0e60020150705070400c0c1128041070302180d41001140640030b00300b100d0048206522400400b0050280700030850300c042220760840018039120741c41d21051440d001070780040d004580e506035210101a4041c2405000c0480c2c0f0144a0304c040c1004010200e9104011441d0419040031000c1002d01200c0d20b94004281c10040013081300d40c0e84c0e041c0d00c5d130700c1e03410304041a4400c4800c0d0001500491003c0308030345031810000c0203072110500315420010142c0e078401040c1c04010b000d000000d5642c83e0312103a140240065141c0e4440050880c110009a44004000e241085101c3e094105140c41c0094a1a04400110742c0030601c0110410b8043c03400080340c8003100e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 804104334 1250 804103084 804103109
    0x20f331302190509060d03080601140f0a0207260a060518100615091d090a080409060513021218100908120f010810090317100f06170c13 60
    0x1400b8051251040d0221402529800341507036801c410000300c00c54610005d000f080b8603100086583d840b440a50403500c0c4801c1200b4240032010007009100d800c4540e40b00056800400148004e000d0b0b40e9001054511078440402100c0700c0000702505c03a6000c10004004031b0f00d550200384d20b0000040e0700030040d84014100c1b40c8070900106500e01034003c0e4410110403184d101c9075030300710074400c90180c402c0d5144c5004001031100ca503100032040900040c200a280c2c020008031400144a0b800204000c000304072000c9106414401044220f581c4031500c404034910404c8448140040e50f003c03982c1c4448890b443c070f0300441e020032140d401c1c05540750503205c40354a042d00b040b00b00036502c0d001c0c203001e03260b90340c0c05407140d41ea020210302120402e02842c0d0181e48a0003852900307106076040380b6800e0740700349860842e00719100c15000c490700c02511034641c110000c002c01d06c4100707610740030940281450719141a1071182c0d25440901020003400c150340c800c200203070802104000006843c0282036113900710 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 804105584 1250 804104334 804104359
    0x31107050f1006170604120302070f0308100506120610030e070b071104020327161503050c1806090301020f12090c060a140304021906020f331302 64
    0x180c0c840014010003405549002001328400b002220000603c0c813a290003020a5122610f541d049a5401506181016005c2100d400000c19001100c500944280c0b59415142041101400035039402d030441d601520090083e001c034841c1c50907400d0340015098403242d11040c3c01e0b0340c0480280403401c040100c140f00303561000803190b0b0b80000030a4800d014184085141c05203104000c10380c80141d0710420103072030004c1d034001e0403450f883d001c54002c504481107e4440c1c010308101d442000056000c0b0814011403046190840d406002d60790f0b01c089003560b0146401001d014064a000000b1180c90140001180e0899161425411100e8003105620501d459210741406064565022100c98082c1d020705107420303140f0b003040300941740d101780d090704c9115629203505000c4541da0001031044c0ea2002c000c08070a01c00345418120403024200c65400f400a100a80042c07600c2c20086c101d003201e4825038106c840b404201e104640c043c1d0510000c40b000c50945694003140e00c01801e40700d020f5400400d07003411 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 804106834 1250 804105584 804105613
    0x20405071206170c040204050906011b0f060509060a090c06051c020c03030702120f180d120f03140405070608190c0e1203070201080402090703140c07060e030c0d03110705 75
    0x3c03200c0c00e100c00e01241e05281c101c4c0309000581c01180f1035245c000213158040f90f003a601600710301a00304040d10b8045130302010741e12000300401c460841900d5142d508e0040c482580310a003d6a5440f040026041c40000a81d503580c0100003645e105210400c4000700d88145401060558201c42c0400e049055486481d0511000d0f00c0703a00c107690400c058420304100d0050034060f401914000d400461019060020855000e00e440d00d95110442d8003c292800610000d1b80082d00100e031161640c1d6184004000ca844c09000c48020403000701d40f00711031500300800200c0028202c0c00740d41c8949000129900c0d0ba108404078061a1035031b030340290b801d210b080248191300035900340c07100d24202e40f100101201003070701c1a241d00c281103003c2c0c00a2220070000e805400d04030881c0303800c0061440d000503001a01c0e9402000f0702429500041929400500f6406109141c0140380105544002640c98040d401080390340d40c5003824440c106154850140300c00d1030301c10009558102d83c0003c140d5185c00c90203a00d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 804108084 1250 804106834 804106859
    0x21b01060f050f1e0904060b030a030206010906080c0f040c0e0a03030f0206011d07111f0f050a0e03071b05090a09140c03070603020f070c15110105060a03020405071206 74
    0x41c00b4003e200701e441002ca03a18115140344000711038401c8100b8140307250b03001e109030544000d005940c038580311103213002151400c010100b4810f020768040c0c0030035414217a081050303e659500078070399940034100740001c0340ea80c0c403200420541c1c1201c0010b80001840d000342c480160440700301e80d01c009103003000400d054010000c200d03401016403e0354a2681c940c407071b5004402040040c1c043c1c10502c0000513003128050724030804840700c1e140844140940d00e90140d4440180720304900040c6845000c009075140a50103540d4000d0740908040c04001a4031485a9a90154034005407091200440c0900391243c50740c045400b403c0b010781144160724002c01c462001d040302050440d600000858010000320b00410803000401c001009007040c02d180500803070180d0070100404d803030104200302500004840107401c0c0010071183c5035010442d10300ca540688100c000c2c010740007903641070200b0030449a540200c08000d89a0441d000140c50302c40c50300484d00d1510b540d0800011918059011131111030408 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 804109334 1250 804108084 804108089
    0x613110331020105090301060305010c0504090623090a09020603040f020f04061809050708060907061707080109050c120a06050a050f0a030605060d05030d090c210303021b01060f 78
    0x4003891030781081c00748640020500d04210425581c058884000540c8954010014504010300103c1c0c1c0584030348410382107030342540003500450310009040110402c58080c0714018a40da4078183c050703103044080030346006604070507d8410010030000480d040750320b0703100d00c0b5401e8001d88165202d103042c1c50320704101031100d80241e102c0e24803458104241e11741401440146c4e10341c142840c0c095071070701e01003001a1114200440c1d560160303080204805c5402c00c2010301c209020710060885a140c204003030003d102450f040681014032900b007100660308064190304403584d07404001156038400c00c104070f190082141c0145030610480c1070142100b43c9401c8081918130803134611900941d50020001d0410b000202690030100450301000443c0096010540c0000003a085d81c00a0032940e40b0faa00710b510030024600e082e6519600442401602e032000310240800c09a0201c41000d40c0691000703810190741c00804060700004d00e035080354810300b007034194680364400900c14952a0740003041100b540d070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 804110584 1250 804109334 804109351
    0x907080109031d030604020d0201050c03072a0e01080604030c0c0b0d0f0509010209090f09010908040803070309090b03030d0f1e02040512030304080a1d060c0f07080705030d050306131103 82
    0x900b0b11a18625000c04c1c0175000f25401403a003d100c1c0a20303401560705030001e580d4808176001c03e120150220320f5004850514015160b1052554600d1401701300785004141c11004421000c00c0c01444031000000700c0b2900650503040c001a6846186450b55141e510703038200181c0c85a0202e8803d0b00308125403c60303001420710307232420310846d511028054200c0c003840ca49954001000008031700d90f40b0005050301c3d04044d1101c00400c03c9400b035120210710780d0040d07110424136400014500c00f803661040c1294003506585a01b44005020000040d07a070f405190303c200106540c0303644410040c591a03201d014104000241c640120b1010482c1c03d0094016104981c05900a484400110035010003104c0c0300350741c0012020304181040e0021100481940d04980351001c5904100441d951580041e140144817000200b907514540e402c000d040c0416648040398a43c0014014003ca91b80880c00c04d80300304a51814588a07038900000880003844029030403503440c90800120626502c6100552103090076 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 804111834 1250 804110584 804110627
    0x6040207080d0213050105090f060c0c18070912020a090203091606050c0f01020f030103170918042303190e190e0c030408040b030903120a0506011101150608090708010903 75
    0x311401501e56200b0f0001070383d4005107008d0060128603114ac00303450b003500d41e10211082130b1040004642502d0702c07203007641c0011b075001042000a0f680040d1100141c4141c11381a15400301c9039010984000c45402a20030240d0080001814808208444c402d0740c0300c0c815405d0649643c440c0042d02e10b610114200d00316010312544040080304c14000c8915001c610486249941e02e141c0b10814125440c480501c001d11042118180a58424520a07019001c0f0319000e001810145441e401d01c80b203070f00c0f41c2d5404085002c5110702c6c0e05e1000c0305960604210070444000c04011000c1114840b103030015255114400480d0f10318404540c060120545509000c81d1840c0c0c4c480010030107003404112401080369008000510200d4007603005036402094203000c40c2d080c40e0145408144e91401200c0c9856856a940104405c941c6c0c031002411600c042c001c000c00c007840010010601c000802e00542040c450039601140c1e0307280d0708216240c000d10b1010006c004020b034074a4020100310384642b460050482 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 804113084 1250 804111834 804111839
    0x303050d060e191e060e1509071d0f060d020703020c0d120c0206120f063a0302190c0501020706170f060604080706091d1e06040207080d0213 62
    0xd82800c89009914060940200f83d4035908100f001d02107003855801c0c040882042400d11042c03e000e2000a49010402d482e44d610742007100b030031080701d480311440c4211480c2d41840709140d0029182c070044000c5c50402c0342d501d050307000820a904039120b00503800800014030307196401815030140800e03600c00da007981c40036400308041048204005002402541c2c015004138480350180002800041c405072105007041803000d147c940940040310342884413160301c000c0000519003220b007102d8600307407844009042d01004010f5940089a080b0410301891010508001e040c02004a00c80550500340ca4407106985072920403841a0984600c6000d4825628041012800754083ca4155a00000c84c070101d03540e40c3c0c41e8880c0241000e003015401c184104008104004244003d1000e46030b80c0e02c820810030b1401011100103020905095105410401401603808450400b103004613941900c440143c6c0343e60001600910500c080103010b0800000e0f240d203103450355000f40091560a0383e480d42c030f040e03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 804114334 1250 804113084 804113099
    0x90a031b0f030312051b070f03080907060c062a0504030b070503010b07150b190e2401080403020c03010f0912080403021002072120010905070626010303050d06 70
    0x60b020050106810104041018005510596018102c10ba0700b11000800e009041d1040d4000807080c0c8580a0180c51042410f4001d600c2c103030408100d80c02002528070b400310003030204241d6000201590b4231880340640e0340030003285024112b4203101100e0310020110001400d00d41c000e100c11a030201c03440300000c0c0450f0150f4140c030b0403200349140e518a13001d0259213620903d07007140942c07604255103a54005140d1030320304030300391804050040c03e12010b007000400b00381c50070000c12208485824007500e00011881350180354181c42d003801d00d2507903900c2c2d51034141d0a00e0461102c01f07400d5882d10444030410510303030700f00ea0b00b02409601c14107039100050710100d4102c0b104840141c0036910982c00604080e8050f030042072200d0281c40e800f908440d0200c8680802c0070984107403000109800e0241024038010780c0000ca04441510007042000940d0fa1050f450342680e11800d000d008864040c252103521403880c210300c04d180312131300402560f12450042e25580004848290a9107000c50206841 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 804115584 1250 804114334 804114359
    0x6080105030d4404121205060d030c02060412050a03090803120417130b0c06010b0a3e0a05010b1e0d0201091508060f010e0105091302090a031b 63
    0x700f0108010310180c125280c0c0103902900000a2543c404000e18060700d0580c1e031001d1284d000e144504144404160348035401007030308280041030300c045898070701400401e980e1400004040b950508010424149900004400d0302841c0d0000c68424190b112080812501040ca140c18034840e0310340000d5151a04441682c070300440003104054050503000c0390100d020288a06017426030000e1003460301141050194060215511040240c3d501194500326280d05000c0580540101e005d031074204220000010004030025445c0e440325408404030750428070107100d502158989220094966100000642c0d9031290000c4c030030f0307a1703552803c1c0c107841c543c5c80c1288522900055a840b10745050107285d0410524a803052070407811b00c414080005021600c0005010403001c1c0c2c1d4840e02c0b5140391a209001c03082020b10289410003001d0a1510941e03a00b00c81038901c04101035404801d030001180c070b0340000f4811034880a0f48001ca000000080168102a4079015690b8440740c0b0300e8a540c480740001007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 804116834 1250 804115584 804115607
    0x2d050106180507120e0709020a020307051c02030708030903040924090b060f090d0b160e3001091b061b0503160c1520150a0b030c0a06080105030d 64
    0x5100c3c28011002001326400a001840d24003007617803c41c540d905c008104070381c42020b007040960400315407841030000502c101c0e81c2c28034980c00000c49c900302c5001c009403240300740c03270740207110320404404600a54010425200a8030000404024094a0300c52840c0c60483c02284800300c401e0005000c2802003c0d4001d03d018407101406403818030800344d00340d5403203410031788540b07800290000d0f80c8000f24880b450500d0041a80e04804649000329a1004021112920310140140004010108814034501c40001b09a4280d0088144003071030054103405024075400c05050494443c0b00000c0840c0070031b04400440e8150344801c40f00c200791a85811142642c5030340a0701c590000c2c40b90b00c40000042c3d01c03607641035201d1f00d0002c0580c1e803594080f216043e90802c4038400508060429002c00c420880e81d10051681c0c80c005007401e5001080400007050018100c8468588401043e401500c040083c08050700c40203110035000d42d181c2000600000092090b18441e20840b5076407000c15000310310719100f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 804118084 1250 804116834 804116837
    0x30f100312321c0b09010b190e0310050705070c06030203190902100c02061c02030412031a1c060501080105060a060810030b1008062415072d050106180507 68
    0x1080451102203400d0500034035154101e1343c40e00300008140d40c8200c90f81d40a0111445100e840d0400a0002510140001490002e0102c40f40640b212031344c0c000740d036038080004a1404980341c0d6440c00215000d001d50000200b03a150703004004a6401c0c1c05d034020398401d011010198a160320313280e01c510150f0b00804070103500200000c4408215a101d409820005070014042a14040d4102c06000b0305510340f905c0f00c41071542c04000e00040003165800c125100c07000d0301c0c00703200d06504000e00c5100445260f072020f10038503001001316005400c900c1e100d8003040d04044104080d40e541c56019028180484030244942c40100303011507624000d409060040380e540c10300305812411641c2d80901028040d007a01d05400c03001000090f40482004a184914034000d82d90b0524103500581d0342d1034158603c981445044040f000300c0c1c5001d40a02911203064020900c41546e03103102d030740c0410080d40141d103421042c041d0400a030601c003054101404450030990400304200c0d81044420890303009503403400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 804119334 1250 804118084 804118087
    0x801021c1b0842010e060306030c0409140a03080603070b0705030d090c050d050a020108010f060f050304140a0b07080108030906030601050903010e0102181c0503030f10031232 77
    0x10690b0922403c043d6503110390006401c83c1011041c0c1d40010210245143c0d5404112541e0301d19840d648080c1c00d2003804015103c8504504000740041d0703ca500b10740906010301c5e078500741f84040c4034128009581038001c02c0180c3c0e02c403405030f081c002c083c241c0c2111030720b01a115801c800580004141c1c11034002a0704000514180002e0f41d002c134010300001038083e20a00c59030000031131550345081120f90074901ca4030082c62001c0c880e1001410418050344000d0b240d0f401c0301400c0100070b41048480008942d41e143c103d540760342e5890044520140b4103201c802ca840b949080340c00700000400308901880b055201c4e0100c680e03950400300c2d903920801781000d8100d041072002c510694098070103130020b514001c0000c41e00030726601c0c5040c2282c021301c0c1c0d5041c00c03c12040c01d40c1d8440c24031400140260042506a201090842c1c861907501d00c400b03010039580450342c50004269404440c224005180e01010308141014480001485e044050390111b07000c1642c110402094118568441e800710079801249 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 804120584 1250 804119334 804119341
    0x302010902040608011a0315011a0c010f0605010f0207140d060609020c06061503011a0a0c0614011503020f040308070f0602190807020a0308041b05090c0c07050d0c1208040801021c1b08 81
    0x840d0843d0350104ad40b440540611000d00011428002c228a52154000010300146000001400460002c21000640d00894818010b100000880611010064810303140d003001e10714000000f055640d0100300c42901c04504401060f5011803068021030307088808650302d4021031111400780c0300c01e02c0b8410354021920414071034180c803a0003603d8100c1460038100350805154035200141d480c0b505061110b5054000140010040320104120304902868110b09007000e000f4803154510407400301801501021850600f080061100c1d00c6010b0344c0030704150b488400c040d40f40403140b04d08980510100d2254000242010300c0000c03c9050a600f6070303100280c60300c1e0307915410340c6800215001426049055808942c0d510340c0b1504600071001d00509035a84c0d10303414440e90401d400358100c01e1080703011426100c041481e50b031640d016592071045400c2c000b5124036040c82c192159034007404042d4000304d54003454000e030143c054654948100140001023a01481d0030034280d441c0394400c045004000403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 804121834 1250 804120584 804120599
    0x100519032a031b050c070902030402040213060c0204180f030809070f03081c18110a05270c19110703020904050601081006140d0302010902040608011a031501 69
    0x200a0003104403a909080c001d00100060204984021000880e448031080b00c0c50501a84060707901d5501860642e0400c00307141041511088284101c8400503008004201503564543c12201ea100701c40184003203540ea10701020300b00002c43d0354242d108a00e4218030180001c91110b103000869846a000d05c0280d40715601642e26034000391107422580f1860201107445122075640901540c003d00708640c031012030b0549140d001da12542041c10384d5050007840c6e0008011555032501c11580159030742d413030042c103101281c0001d0f038a41c0081d500075030810541c8407290301030715007040d24044c4001940c1c49a442584187c001c0c4a1803502007103038003021043c0c17500786201e1900b90b01c825a07801d086e140403584e42e030005462140d0544003078800343c10031001000020401c111031540c2d003282e83d02c1403142520b0010820080000a4021802044203034102d40405200303500950701584d004104120403916444954002e08025a20000c504500c15184105280010350014082e100c1607084246a080c81311 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 804123084 1250 804121834 804121841
    0x110d0c120c020106030215040509040b091203191a0105090409020301020403020d080a020601120834380a0e0a140a0b1608070e0310020f03040210051903 67
    0x1088420811615a40d00340d0140e20075500c00e6600201c3d0304c07030540c01009140d00d200c000402c1514401c020402081c0c8998040c0b0b43d00940100d204825651100b441c0e80c03c1c01c42050030391404060000801c0040c0180300013040400750140b4003009525050300416550203400340b069030101c3c0d024001814207144c02d8010b02d01e924405000542080c2c0e0340c6d4082544000301000444907aa800301d000c400d21541000300c2401001d60106024201d02541c4031400326200b40250310400d2418952001e00d041300d011003d519402d403a082440b684032a84c1025080c1040500d0410301850403a91521007801d0010800b1044c180c000c00000800d4aa200d1500d00400c00c0c85e40880f11800f505500401060022160399400d58600c0b01402c14000e8078070b031801c100207000740707040720b0300b41740c0040c0880b0b103a80050480c0d44807140d401c162040303141c00302c0081d150101e0b14100c0c0403200c0c000a414402810f101c030240d40107034030a07140441c00d9000c0803c01c4d6054011403040034011015407100ea80954032030341 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 804124334 1250 804123084 804123101
    0x120c1e160b09010e03150714040608040807020619020703260306040e1204030c0906060f0e040b030c031218040204242303040308010806090307021e091603050a110d 72
    0x42201c18000444041703802d00c1ea5580042003440d040c03500b0800c1c0c01c0d401110380003400c50180d18062406d42090000b90980c500908040d0075440041440011034981d50301b19010302803507031910851041d58020003540c41190340000c0351f8480c01322104e1140c20084001070f00d8480d51010401d402c6580e030409003c0240341d07195118031ba610034201c2c1d4031101c0302d510004101550165a504500c2e0f03007403401d25015100b00340d0084d42008600300d07080d40c2481c2e008440f008443c0044902245003090480003070718000b10340d05225850301410241c0c41400c001c1030004c2c041404250031500c00c0c0003451040100b00c0c0140d01c18000200710700c0c003918411203c4d49041c003030407030010b0034108020310b06510310103034568a03884469280480003050205154000700900e006203042c2c0700802051900f14462520b0b0700a409000740034070002d00380c2c00441681841301c803504c990050808807051900045032860041440881c201203403410002c0b4581c52594080d20382c0f1081c0a02820b0b10f02494011458010802034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 804125584 1250 804124334 804124337
    0xa0302070b0f0402040f02160f170406020a0309051f0806130e0f06090a030203030f100905070908103c0507260105030d050d0e01090b0a060b0301050d0201030b03120c1e160b0901 78
    0x60ac818030380c180924094400390035680c0c01481460b05a1401400d07001080c1c2050344a500707103d81c030f0042c3c034800d0740341140f81100b5854aa4015125040441c40c1c0044120b50a0343c4141001580011008005403110508260008445c415100c00300c0407900d8100c1c00304040d00680007000000c0c01e110100c07510540003001004128002c69480c0c5098044410540d407260000d18100030802c042e54040000014040074a10f080001c41c202000101c4040c00384086100f503a406141022090040403c1c4400b2900e40758000b4007a516140700001c04400807441407003175480e0a8000b042c0300100100c8440c0c10b03140c028009001d5254410030980302da400400e620506140c50700618a01280c0c280100c00c80a88100400341090824030761107410384960380c0108401510520040081c5d594860403044100e40a08000078400007034000f00b401c001c0e0182070f04c588071000003881628803800058071040c0c415484600b400c18941c14080c5900c40301066a030041c0800c1c03d00c0c007030103045c01c1078006021a6005 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 804126834 1250 804125584 804125603
    0x60c050c120301151d13020412110414160c2102010504050609030a0909090f020d080d0612050a06240305010510120510020a0302070b0f0402040f02160f 67
    0xa1a103481c080240450048541c80440100b00190700d021443c2c100c1280e03403c294000c0d0640c448024002d0000100061107002c03007400c11042c4020300e80c101c1d40076004002c2c024100200600702100101c0d501030340b8a005a10300610144025005941c880c003c42c10a88100c180a034040401c0311402c0403084251140b0082c010400d44500000c200204400c40540000c1554901401c24034146100100325080035003007041071401c415030080c030305000e44500d01c80001d582d100c6410b2190981e10412402504001c1c040800c0040c01180800b03807140019614050103407035103400c4041c4c0c041c003406900030714561050aa2000003032550f0480e00c50344080c40b41a84580440242c16003d40040b94000d80341a503591060005c0035404800880140298101c01d41505902c0d549890313517403000c0d840c1c1c82d410347d901281150190f40310340c0440d000180c0200320800e46003000810410304001c1030b0707822071003a4a843c01d20400b81c2058000d85140d5036100410480c000c85c01d803503500341c80c50268403ca980403032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 804128084 1250 804126834 804126847
    0x4090c060e0301111909060f09030f140d0215061903060f0b061303020411030f071d100504141f11010f05011d010b030f0a020a1e050a120203060d060c05 67
    0xc00101416665104030002a050b08050401412513081504801f040001d011040281c1c00d030008411801c81c1c0c0d1000e009103441c40d81e07080c084110100020351a0a038003401903000c1170958006058400c0200c0101000000c0e11404100011400d400744103d2074034006850800108403642d0006080f01950b2001003003061040f400034080c0c0d40032184e040c6090403404d03814401d60602d4411602030058038101140340d42458124500903120080c10780d0304002200602da4030303040000c1001c082c030b0b15010709030002e0403055480103001904503010320400720391031000b105214504440482060800102d150500490702d90b81142c0080c2801c9401c5801c5d9200e201c22008140248a60350003010203845900020701c02403201801c0840c1039005181c01c04060081c0405400c60620503500306402c880016581d4502c0f501c2540d115414034a0643d800e98440722529001c0e400c01c004140c2204075540700c1c40704540d560104d204078003013541c00540201045000000080072030340800100106400c0c070604010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 804129334 1250 804128084 804128111
    0xe10050406020301140303030f180f1204151b0b1e15030609030c031813150f05180c09011103030c18010906020606010804021f02071404090c060e0301 66
    0x10000d40302100e269900000400640c240951001c001440031006145036007404040c07200da001025091f02c90304642c444201441c1a410003101119002d80c40c00e4400100c1c105d040301321950050b11910300810210401c01c4500c0344640b1b103a100d55034015009080f804510340314086900d100410945101ea40d04080d03040f015034000000d4410300002c2c801507407014040c0107060070076502521003032565205000e4041c1030f00e0040182d030004181052001140c0240c070001030780301780b40c0007110504a4500740c0c1240361078203041d0b8904290f94090644180c1036070b98400707001000342134841000c100b108060108107000c6100e0000d0021801c145002c00b0b0303017a130040805045920554108005002c00038444410407450b03070910800100900f0714440440c03a03c40c020307480701e400409a41c1002030b003500040c110350398070000007140003c01a200c103244118400180d610480c901031070004495500e0145003520300b50150010155205c4201da4800740340c12000e483d002d12400299505540b00c2540c003c102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 804130584 1250 804129334 804129341
    0xa0302100f03021c0906270f0302070905070e01020d020705030d080c04031205180603060d03120e0706020a020f041104060f02010e030703030c030f0b060418061509050307080706080403030e10 84
    0x20300c941c00140d44007076141203407c6801e42c803d203440c8544001c2c80301c000c0710614004156100d41100581004407900d140c22824084581c10020700036203058107101000b0f83c8030706d08031031460080c0c088407003028400c041640c2d01c50b010300c02c0540c0b5501410528104170302c181c00440d00080c0800000781003035141c2d607503102c103020b0016001c00061004680302d0184100f61b10341c1d005020003520100d18505000c008110705006290b000743c2805005104515940341c0c03039100c18403295071131060b159225241d160003516180c5141e02684030302c07140864074500f03151034455014028182c1c26940c0c5002d1034820f007940e0a500299881c001e6540e02c1e45400a220740030710050021510a540020b03d030014034034042d00b00c50141802581030342c80d00c2003002c11516408100c0b030070f40e03c0307000015401000c1c4010070005400d013600800e90454460180c2c0d001d040d00304403100300740c4908406603603107543c40d40740380c0b980c0310b40a1081000243c026000716022038040d91000b0401100c1d2404d6175030360b05070201505d098 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 804131834 1250 804130584 804130627
    0x30e09071d0402090409140f060a1b0e01021f0e3313050d120516121109030a0b0403020c030a05072105031c060b040605030a050c210f060a0302100f0302 67
    0x641040148019400c0e05000e4954840c030801c40030001c000300003e9652f40610322840040030b100e10361410ba404d60b070080110540e8820802c1400c0103482030b4189100250030f46c00c0f00110140b051b502e2250700455121104101d14200c3c0550001c065043c40748044c032003034050034044070030305a01480e101055040c03010782840c1d445134484441a00310715900b00119080200355003d050200a4010781c0d581d442114041114107030000414456002845009075103d0000240d03458402c0c0c0c03100c2400c002c0761030320491195001e41c003500c3c1041c3c40d8209241d1584030455004000c3c0d00949000d000804022104440d1641414501c0401c040d95a13600352840e481141e912040c444007602808820342c840c080c0700d01a200007000d9604140c5000707006416800054000203c0f2500d076400140b650b0078050039103069201380700c11041c00051810300c0540300202900c000e5811602c050002c0d0890400110b020200d0f80d0191034840c0740c190f60b113030840d07044030000c20010070550200203c5040360084e8459965 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 804133084 1250 804131834 804131873
    0x7080f0a0804050d0e130e030c0a050c031002090a0e0405010b1305090f0318121501030f060f02030c0d0b041b02070f0f050a031209030b04030e09071d0402090409 71
    0x7003030300303040c144185406074900c0300500b000340314107588070103803103051a8040b401d02c0107402168030149000b55504500910005006520501c42c512041c80310000b0030242c02d0300140e050720b401120f2514150b046c0d02c51110300d107401240402c000c00c00c80c503c104609900c140280000682d00009100086d600316010504145c1d154031001449201101888041d0060740c1c280d0046203052002e5104a1135660410740d03040c404d442030482402206018010000c0b40814001452200c0d81c4a00d0302010604080d07038241c0d8018a85403a20641c07222520031240201030903e00c0605200e07003100b041c005000e2400d00c03141c0080e114440403402008030140c0c24107a04003074014001041c201002c5554914072988516041800309104000c07503140c100c0300001340c1c1e03000210404040c01c081d000795240455a0b20040c10681c0d80001c00050652040e400c0304200710840d070501158035048012103170314075008108905901c074190307000701514055001f002000e01c05440490040d9007a01c501c240220308001220 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 804134334 1250 804133084 804133097
    0x20070308040e0115031e0914121207020a02010c1113380a0e18060916060e100809010603020a08011d1902040c050412060c08010f0b090607080f0a 64
    0x1001401859440c41c0d49807040c6030401203102d400549801012006d10781100242d40c80e48020180b049401060300e10901000440b8502a0040404980d66100c03484503400c00e1000c1c0041b60100d803011489070100e54059560000e50a09900e45d1103d0303146006415a200c01c4181506041c000f490088450b02140100c08060f01c07101200b42d580010040703070b103418155260074203400c10741d512141c40900f50303001400403010079a02c1d59411920303034044030505181d520500b010403c001c000000d1140d441c2a4524140e0b210302e90701d040c147d643c3c82c1da02c0b00031540a1015203000c0d00c154459052036901c4054a40040b56a0b41d803900450159051a0401c01850351075003c481986500006200c403000e043e43c0051206026080076007519000c1c0010080c480d5440b031842214a6106209440182241401030010900c5d1842c080d4002c0850503207500c086140d00000095403081307601a0301c00c80710070398071007071900e2030800800200760700c510401c440c26a81408441035030004070000e42020220354a50380b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 804135584 1250 804134334 804134339
    0x6020a121401030c0f03080d020309190f02030709050408160203010f110405150a1b020f0a08030705060f062407240b031c0302030915070c030905030703020120070308040e01 76
    0x2910080f1a400c034842c0038117502d00c100001543c0c60b0440d000c100c2600f40040c0c513611203100c03a07801d000540d414000380c840020000d809010110704030341d40e00340c4210112082c1c20390311808003043e03030000c075000341404034240038103080400500d041c000d0541c0700a00004103008401c00c29400c0750420003001803c00400f180500040c02c0201d0041ca0b44250302d103c90f030800c04030300303402004003580008103102401c140e801e51085441c0c0a092140c840720090003a00311940f24002180e60b40c01c001c0094071140305120204684148801000340919005403010300422034180380f10000d00c2807425070038042076003000142e01080c90a203038210741c200080189008502d00304000f409a074203a0740c1e0380c1c0c4a80c0216000307201c088210400e0418100e100e0402507140d5641901d07060802442881d04100c1140c03980401400e29484940d80f404180700f0f840c2d03040040c2d101e50030b05548002500000340442c036080d802d26402c2000d00400305510703200404071043d185c1c6940d0740e412a40c20582c072803a529102c0300f006 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 804136690 1106 804135584 804135593
    0x4030f1502070303020a020c0117160c150c090e0709060e030c130506180c040b070c150e0111010b150d0b0d0803090706091206020a12140103 62
    0x11522002c00307050160103940415000c400500034144445165030003041218590b0f1000060340d092503940e104205200c1580550360b0b000c0c030030007038042da000414020f43c4050081540b080861201d401c600050810a582e42000680f42804802c100f50f20381e125404408403040c919000b100001240007083c1450700c07a0726040d030048502c0380c0201c0300c07250a40000e030003440c0640317102c03100704407094500180c09400c1d100482c4040b4100410800384101801031302d805806121100e03032041c0d0310388100760341d40e4a2001080c0410480f110000c115a0088100c44617007003403000a1100704031150000f00c03190700120414100d1000460303488020005c4d0b620841d130800c0c01070039440e0080d90350304040000340c000f01d844c1001881008400304206100d281e140046a1141c074101c0341143c0c0a070380710406504803480d22001c0046410320000c202480d8007900518140000001250b9419800c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 803956834 804136690 := by
  have h0 := BRFrame.cov_init 803956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 803956834 ≤ n) (h2 : n < 804136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
