-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4470
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:43:20.338727+00:00
-- url     : https://prove2.me/submissions/a042c6e1-f458-4823-a780-9829aab25993

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 803776978 ≤ n < 803956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 803778228 1250 803776978 803776999
    0xb130807270b060d0c02010c180b030103110d1707020f040207201804050106050f12100f0608030a021605060901080406050901061d0a062313110a030501030c141c02 72
    0x2131000c2030f02c010781300d280050f035910070740c1940da55030201e01c0070b0f149000101015682407528486035064881484042d082c002c1040c0940e80c1c235944d00c010f40152a410000003841d007025103815041da40d2104508038441d80da0142d144207281001e0084d01e42c85504408441d1550a20481d5100200f02c9c44070302c10f50150000400d0044000f601c01194015130082c000011628141018001301070442c065040c1f10345031103095001c01040c001203014002d101e0b11000b042c151a485000c03005807201d500605800e001c042200c21506030b0020707021842c10f04510141c856107550310103011152280811340b40c00104d6100000b4003066150304001c1e04140700350000240c1659800783c0d4011059543c2d81c08540022100600400c5074541c003842e0040c2001417000d807040980030346161130340c0c4552010301e801100741e41561540c40c581ca520002203d80c500183c0e0b560351141100050040074240401c4448a40400012a5100e00890784a482040282410707a100b00008800c10703010a0f030342006c83c0e02030204003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 803779478 1250 803778228 803778247
    0x140a270312270b1815040f020310022b0e0703080f16080408060f0601090324050901020702011d061c060807030807050c0d0b06060a0201060b130807270b06 68
    0x9a0b65102c00d80a0301d40f40040f4100b5006440e01d40c11020900310346a0321800300024600e045e09461908103a02400d054969005031011908041300100551007151020400d181c800b09045400e03000205080943c1c0c24041018054504a038807055690459a110007003c1c000142100d0080020400c00410282000f01814807503d15500c020400c80c0d12400205007081545000c014136074009a92185200071850041c0008040c45080d20000d442510341c41d91b03144000d040b10000c004a4081c0e40c606100a01c0c0c85c150542c041e600c07005080303001903404c0001582c07480316540300d030581e01c20050400b0b00e04655110746050f620070248092280c3d41c0c0e10b84000030305482c100f11000007544180b040544850440c00c1c550b0405011800d60340c040c1e82c0c41d060680018482034282070348043d003100d0944d1180a150012401402c0e02d40080c42080303800503039015440707080400c0100b101d40c110111131501d80c4903125074002c00c96205244100502d01415144040a01c1d00804442500905030700c1c101010315 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 803780728 1250 803779478 803779541
    0x209040209033702030a020108040201030b2806050f0a05030405340b132d08210c0a020f01110a1104110403030c0b0a140a270312 57
    0x4004100c4980342e90000c440b0030080c0c1c01c4801080c100c003220f2880101c0c1e841c0c0200f13480e4600120003c0c1040f41020003c1c0442e806a800740c003403404003809803003c44420103161040d03c44400c4c1403090034050040002a003922a2301140c1042100d01d04960500040e00030a480b140c001901c03c031403600a0014910301010800054461018030762081008d1003076180c1d21462403a0b00d504074000f0640104880c00c070740402021541c0488a04c5142040302003222500f01107680c0500f4040050000d1a05000132012400151b00040c94850050f40e0b2079102c09250044030703489598680c500c5500114910409440c1c2101d2f4902d0500c0103040490400c0c05d400c50705410005814000c403142040d1041603002d5080610820500c4580d2554080c40d0505503180501404a052001000b52490200244022a050b044031806091300707480d140a50a00c10b400e0f0026020441c00840150b1010410785000030307681030440000758060321112203520b01004140050200c0020101240881c4090760f50044440c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 803781978 1250 803780728 803780743
    0x120207030510050118020a020a2010022410030b091002040e09150702030403150e0d120f060510201213141c1a0c0301050f0114030109020904020903 65
    0x2074102c0002c0940c18044061010b0391140c0c00290458418045e0340c0304943c0003c2c2c00c440286e04400c21202c01c040d510061001551802145c40d0003101c4110481a480d07000105603401824020384a01d00d0071400a400e0301030320040b155101d405a18600420100b080e4844031600002054103495603001d9000d4520160303032065000d851003000c00010080d84510034021810201d000101c49a00ea00b40b49900942e03a020320f0001901d04d41081000b02e000b00c841354040a1484010390544140c0045090040c14904003440d81310903140c240401d1001840091060b03505541004140b06809007040300122141d50700c0040c03040343e065209840c601b0340300040081c014409281101d1751344d614006000903540d801558001880c070900010101c0d140e60314107001c000385108022000100c0e154a00700100f8600c01c0144845807003440b80240302c111032250300114140c0c0c20a03108480307145110b500449000c1c041300401206128240014000488990010045414010005400c100c0d00b0000a03062050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 803783228 1250 803781978 803782003
    0x7060b060403290f180312090102070201090e01030206040e0c0c010e0303011d0c0a050a053c1206120a08030c04091b020a02010f05070b0f0708160203071202070305 72
    0x7081642d15120081049a0344a40720700e0703406011990422012040742000064880d0007543c42c2c6810ba40c505170300800030b8842d03c0842d0050781c0c1e103070300b010382440307000b503204402c103034000344140402107104550203030703845e040702d0313015141c64981031816083d000403200280c00ca80000c202000350841e000c0c001d029941158440801440c1ea0b94507102e81902521031a0101e1500b030041c0e030081040740140a02662038407075580c00c04950303840030607408032131910400c18540c0c03d48100390b0741112204580a000b05504151207100c1032842110b6020340141c1c0105010008800500b600085040c00d0109000b404006280308841c509403442e0f40d50025508101c0d102858400045801c00028509000704520018a008910300358110498025210300103400c01905004009400e4004030348a80d044800840e00a00c0d0b01d042400c01c00300308929698151405000079068500ac20b0000d041c4011040d08603007203800031481c124a95540441303c40c0e0003104007095000d450400000b10302c00780507c011a19 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 803784478 1250 803783228 803783243
    0x1030c030b04050a061e05011b1b0920161b090f02070b0711151009020409020702031213030b060a03020d12032f0d060302030d1101200f07060b060403 66
    0x41c2802c10810021081419035000d000401c1410807a0342d81240d4401c8020302955040364850403d420100ca2b005502c48a40c5410560010005192141648101c042d0311520000d010030345112420400d10780035801c0300c1a0741a8071003500d030000911b20390711011000c0c44c1c030100352400c0d40d40e1250304007120381c1c0f801c06005050700000d02804102100d1641380d800400350800341c0a502c24010041d594403483c0605402d040b041c540480c109281d00f4207103d000f401c8801d015595981c4401400010307401008080b4020305c20070013500c2e0b4903143c01c0152041c4c2e58441c14006c1c111445d50320340c0d00c4100d038098031480d0400340000c008800358407aa0300300800140100310328040f02502000081c100c40f180140c1a802c0002980f6480303940401d229182010070000c10070f292180b8802411400030003c81e40300a40c1803141300d10360000381d90404003038600c0e6581403000304480b12241d910810140e035400f82c070881c0468104054003130b07400150050710035113000e4a40014204c1b240c40210b102a481900140c075140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 803785728 1250 803784478 803784491
    0x30513050106090c1107031a091005180d09060f0c1a0709080708010c0507020108041e12030c0c023604050c0445061a0901051e01030c030b04050a 64
    0xc0382c001710f1024502d510000141241c0e451901c0d08502003607603110420001c130310a404641010410045130310b61405028080210341448413040c2d030600c9107010464110302030010800031041c0600c03051022503045407646203420006c103408032a04092404202c07071880c2002e1000c10440740e00c083d21445144607441c0c0200b00380c1002e1643c0d252001c0c030761003001e6030b0381040c1d000810340381d200c001d0380d00150f420700708410303d500d4502e030884c1040c0311194411040081100c0742000d0010b42c521100703a0003269102081303000e500e102c08942906c3c1c02400a500b20b211104c0b1106003120002c8000200d0958103496500800307800034030703000c0c070005450a6403554000d485c012840e00d001c2c86210740b1254403ea03103104a0300d000c220210018154102032504c0300010105020308c60f03194000d0301405a121900704152156008010300c0001003914176400b40e80c4072030000c036440c1403c0c1c2500e5400704040b00704404968095004501030100d101d031007410592a80c0c0c20031055140c038001c441c015210240040780c0c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 803786978 1250 803785728 803785751
    0x20705060903102f1305010e040e030a030906060501020f071a090d0c0603181e15020f0d051303021b0604030f03030906051b090603130b040b090c01050f090103051305010609 76
    0x40c646030800c44c04602804104a22031511044058402c40b442800c100304080f0740035001a000344409004450940000103405021542c1a405004510310440d03042000039100c43c01241c0c1c5000c0c686852200d944005014040310840c4ca4801e2f070380d80f40c07a01c021894003803403001080c00540442422a40c40c0d480705010b210b41c907010b000e90000702d0254201d002a00c42151540d07103a1540c3c0192a001d00c0001441ca40c3c04d02039404070391072042000c200199660f5047c241c58021591210014403005032401010500210003a600c8107065501607008011000400c0c6e80c4591403c42c0d52000d9038040b41c10071001000034041d14012100e0350094800061544c1d00e42841700649200a11307400e203403616851010412540d01c41940c0c0e40c00400d6806075102c0d41c6244054040400710403014060b5600c040810041023030b21801144990820300985072845032002c015a201d002d86004040341d00024801e68070f040d40f03c1d510290b842110a121400c41840640741c007421101542c0040080d1030715004400d50 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 803788228 1250 803786978 803787041
    0x730091407181b1202090a09051302090f06060337050106021902100309020d060e011506030905030301050132130f0b031b22060f030b0102070506090310 67
    0x541683c00740c0300032084044624001d00800c01118804e01e155404660703921070382c0752001070b88046c01c40c1d410f00300154148040b0391a440303080080c089224040c2c2c0400142c41c8201c041700320b8041c400190140d400c54503012005d91307020358840300c01607031050028022100e41c150700b0703032a06515030b0b00c4e60005815418201d0090410301806102c03000d50700d82e50b00c00d00043e2901070038000944000c9c81e00040b032036130070310004140510028000c8c007594100b414000010f41d040d40031142130540201c880303031529900c500036010f560780171001401c3c40e041440100003950007203a000c0e404642c0e140c030101c0a801031400c03484c0a040340c5140300e0b042920100300b00b8552403500701d43d44042c02c01002450400b03403402c0701d00c9a09200042c2035600100c04039800d0f0403c00e420000f40c0762000424401d011103400c2054007083d18405510a40c800180c210106ca00024000d10848402c02c006070301030a80c2034100828400c4071f81c0300741e9046070507203d004101240c00045104035610440401c09100704402825926074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 803789478 1250 803788228 803788241
    0x50910021c1a1011150103140c190e04020114070b01030204180b0a15030503070b0603010c030e150601140c0c0f0402130e100f0e073009140718 63
    0xb03581210700d140116561000101180d01c2120b141c000d16003101141e5141c1000c4442c20500d100c41c0a1070000310070488401900e8106041580885a1080b071284c10000a20000c00351003044a004a0b003c0c400001491400b550060040c14a5a096950504444800c0c1d0080784142c507210b0b440f000500461a1500480001c0008402c1484480070719440c0d0041c0f020000d014008500e6560441d0180032039504c0e882002907800c801075940712881c50904040c4100c0868407a413107540703400b4284404074024800c681403511030380300a007003200306c00017028010200604510b040c4403008101c0010140b00d000100250462034000e00842c80001050110710040e440c007092141c3d0050100100103a05a40c4441c1140c3c40444031400076250780c3c2001001801d5508011089074845101113054620600c0446c013548895407407469919501d07134440149003000240b0610038a8840c885035941c0910b030007280600c0d0040c0c12000e56009940c9007a882c0046a038440c84003550305410940b4100d90922406 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 803790728 1250 803789478 803789501
    0x818040501170d110106080d050a0320090f01140f040518130209041a01060801063209150d0605120d0c080a0203071b09240306050910021c 61
    0x402030b428115029a032140c224611400401c055a07100640303500c000d401410083c8141c00070380e81011034035100204035510043c1880d01080c141140000104a1040804998015060014100070b07c0c8020002055043c4461504101a0360000c0440d0802e150051240a181008150703559190106110841d04800010034414600c1800c0240040000c030580c03140c1a4101c0b0b0350310155503646029000440c000c40780900d20740d40040003003041500150100d041c1c032000e0b12001ca2074801c0c403072030b46140f4105206000e80c2d410041d034104590342d249070143c6414440100040c4034410360090496094004140107a0b042f81c9400c0c0c00c00c00b60518694140d10411108054007202020780c00142c84844010001050102c0008204407034501c2442991410340e031003007041c520108000c9102e04070343c03001d02401003a223183c1081034032440b10f4070221a0030309256403012049142b85803121001408000c200280600600f4003009000c6003d10041c0307004081c41403171310342104240f5010070480b1002e9800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 803791978 1250 803790728 803790749
    0x90c0a0501080f130305070501090c03032d080c040b07080306040c0903080315060d0e061005041a040c02071d071205010b070b0402040f090507080d0f050412050a0818040501 76
    0x24032500352511a5000d5000855402415800f44c8924003111a4424140050519442c0c652841e0400640d0b14040d01200d00a544404624080f8017042c4100c3c91081d280700012018200100801802452034a5200b401c40390141d00301561455440c0e0b165100c62800c84100e1800070401030145000c3c0300d0340512108620741051501d0a41e030354220a840060020519105408020510303551418222070442e1030004003030204d260740081c51642c2d940150390801c00000350303000100355818644207012200d05040d0070040310042c0d41d41804014401071215004502520b00b004c80c9010b0307480380540c15001c1341d400407855440e0040005002206102ea03038442c1030304190041014501c810143c039403070341d0080900b02091315a840080c0c000c04072004642115030402d01c42000380000880e9503403c0322514010703901c5100d1100001c4881050962021303020400911092214050050f20303000160f11070700403600b040b40c4a80b5044810b4001c0500c1c20007500da0858507800c00d082034081c0c5401405203420 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 803793228 1250 803791978 803791981
    0x90518030c070b030402040618050906330a0e0705131509090216170d180c0b0f07151b0305010602060106050c0c0604080d1106090a06021809090c0a050108 68
    0xc05071142c04900c107800340e042001c00820195030359070340000c0003000810100c13150f402c4071100050141000b1244000c00b40643c2e4005a050b10381c1c444e11614642130100c2d18200e03000c1010259203000208107255811031100d40c0046040705407217000074011682910b4464650038142041d41200c4803a400400c40b032108640e13002d421941041c401403c1c2d849c104c00158650056100f001c030f81480380c500151512060b0929036101020b000020510300f00702400c10300c070300880003e20810401e26040005c0c02d1403d48a000c1040e880d581010304100340c5196041450240b107a1100070a04c03243c01901c0303011650783d039655095480c002101510b1103800e810144013640c9001c8010352108014800e460500c071700000d0704561034609120074640d20800a040d1034585840b6074a09907104010b80394100410824844e103145030b000002d80c02d200303a0200700140034030303290b59680c98040d420021280c80c5501c14410010210b6490301c01852007401e000e00146901201c0c0d000300001c1c515a03502c440d0600c00c0700e20 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 803794478 1250 803793228 803793247
    0x2071a0c070605361314060d020d0804030606180c021c05090a08210310090216050f2b0e0415050d030503012c0402010806031609051803 60
    0x908100b02d54240c00c02640790b000030000c01920107407182c101284e010303c900080c4914040c0603625103541005894a0070440e5117000c03034108480c81d030a646101d941826001800720f180c060b40c1000d0340ca02c0900710280044282e91019031903001900216000c80e1101c0040c081480d0410f400701000014071810b01ca51500f83d000a9140c080c422500b0aa840c51071211300b207694050022500700c03943c06403141c00c4d502e5a590306903072503510400410b41070710720250b0181c92006022050700d014070b484001c9c540c0c0d05403800501c0002507100c012080311140d80b010300c20303000c07540500925001190000c060030010442020070407010000350868242c40000c0c011056034140d001c1c2c24040c0c81d110540c1d0001d400580659801040d4500f540f0096000890300b0410081560100165049903807035080581811540d01021a2001000321442c06808007180018007561064100c65001100607082c1d03125800d83c0e80291039400c01a40020a1041d11041800a21174100140012845107080911704015420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 803795728 1250 803794478 803794483
    0x3020307051e041e0510050a081f03140a0201030507031a06030a14090a030906090b030c1605031902060f10050d0302191101080601020a0b01051c0203060702071a0c 72
    0xe450050720003400c0c2c252401a100000300711006000300808184410301c1038524940107000320f00036140201c07440024103c00e18083d20507910501c1068550010382c0d681d00000d807480b0060070610607000c1800e181d00102142a914410f0583c0940310007400003600c0300c1c00098166140a030440d800c261502408000c00c05a036103e00d1640d4104664582d62600d1b0902d40c0000340089011072100c5010305400d00c031042c3c10005480c1c0b060303407198491450399a620081a186c4000c036216500c0024810400030351001c0b22080100f503558841d04012001d003905494462454228242c80078003403070078441440c026074040020582c0101030a50061036490b0045020079520501e01c600c2d401405d001c070480b0109402400340e0103240b0040301840150052500384038074030420f07285c81240800c042802289965201140040c0459000814540d03280d280c03000740511810782081e41c4504404004620006aa0a000035401088181d0007010060f00f0104062860b4642d080c0410b68510100000349154401 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 803796978 1250 803795728 803795737
    0x60b1c080d091a090f1006030804090f021e180a030f110105280801140901060f050903120414090403120b0a08030a020d08181207030903150b0306070302030705 70
    0x1c41402155000103031418890118200d000c0280c0601050100440d9010002d10140001000c104880c8406044401c20040761441d00006e40510810802844a0381c6140c1203217440743e420881c01441d040c102c1c614040360380c141441c840c400c0600021000c0c86000d111000741d1824804990725902d043c50b40d0f03244c110798151002d00802d039400c05000d4241d103a020740107039419003404500040c04500303038061180249180c0d000c0040801c404a0020881429017804c88050103400340c506d180690800170300303542044c0c0f40c1603000c0030028204174102451b05e0500101040030303161122241c61390300744040b280e4141d009480d82c174003a0101c2420040030039071201c060600c9030908000001c803580203c000c50a0480e04c0c1d0401000e03840700260812203594000f50b803007809060350b6034143c46500c0349811600428541d8203c90448c1d884924a0361300210504010600741c0c1c400d09160703004a03561356581e4420307241144a041c606035118206101e40c101400702e02e60000c020700d01145145406000680303180103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 803798228 1250 803796978 803796997
    0xc07150506131107110f150919120f02030102130905010314030a090e060409020604030f02040515030c04020f0d0c020a051204030f0b04020d02060c010c021c050415020a0f060b1c08 79
    0x4001030400c146c0324208441d0100d080648640e450b54102048141c45a104082c0503005802414420048903528000042a02ea440708203400c21026510b40d502c50640262040c1e9055600304480300454180540e40802086010004075096247d400c08080401151410321b100340c0040022910301ca03030044d091801e445428815200341d841c0c0c0c80114004080780c1c80000d400c200000703004028091990001e1000600c03c80741482655079070800c80c40400b030380e030682540540c0080091405403915801400c40c465031082c4150a080001280c0d000307440e217480c0144003680103c2c03200d005101d07080c403060b12201c00c0030003503030300c0d2521b56642c205541d41200340190100f01070802144c21036a0f10314891104a030014003d41d281c0781c1c1c41c071010b402044000e000c4009846013542002168000d01c01703400c403000340e544440d414640b07040a0078080380c0d58610108214014184d411001032510b08003400741c20302801d800a0050017510504c0701030301240405183e50842d4441c11000200c0c41c02c201c518015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 803799478 1250 803798228 803798243
    0x1d150a110f031324050603070f09180c06080405070e090606041a040c0509040c02010506031903020a080301080a06050c0c070306180c0b07031b0c06080c07150506131107 74
    0x15190340e0007071007441000f44014858000003011907079965107124200c91020300701c00308125607160740082560311f00713141c400c0c2c03008141021000c1003044003560242500c06207242541003840d0b41583c680a1a0704c4039000790000c0340d207007002c1c4024072204010311000307030094024241c024249605115a40c150083c0203070b2165484000d100c1c0d021840d03035002e24044001500c04c4c00003c10b1250090042d4020304112030250386000480702d45140b0502840b409100e001d00036125403011840f080c84458043c074400d90035403148184500009034048007c1d8001e148071400303840585d0f69031606d00d090381d0b0003030400301c2a0481440b01012034200402c1803004c0b00da1140c40040da00d8140c050341d01ca039030000e44000d021980f85410014a1041d844002c00e640e078070996605042507440321041e182a0b40c0e001c400b03041403521403414494180107000464001090402460130124176a4608281c07110202c03001d00c0c0d440d222404c1c0704c0242042c2c3e0010601d600c2c861300a0005d0088040350215900130a0000340043c2d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 803800728 1250 803799478 803799481
    0x40e0406110a1d06040b0a120c020d080c0c03070b040605060102011802091f12050102040801050109022b02040e0c073302030a06030c06090f0603051e0a1d150a110f03 73
    0x355144001c5400606c0c4110049031a00200d002c0a012504100e5028000d01c1c10100c140b82c01d14404646480315220a884019094a64150281c5a600310821201c4240720030440180400c805403e40b42c40f0b03074810800071a07070389007841c002400c1d2440b841841b418100342c0802e13400141d403520b9903103621107400c100c0710100508410300340622060580c02a50800260304c1e8503014414190000d01c2951090402480a66a200c00781d80c100d01c03410102c4201e6010f0140740702c140125440e00242a20400030b07000d42000d44a142c009003400040c6c0b04003030360364000580041004040c00c60a00303004030a40010003030421009170741c0c1d5081c0d50140d9841c1c6440c5c0c0000001c850003c030354072840107560002c1d440d8481503224840036001d6000ca000f6045000240100000c03142d2003030180030322a038106010b10b50500225641c048074000050507004c4041c0d243c648070100402d410030460a90103201d0700920030050042d000910000e00a4005c05000e030601c0d0411500d8800403007264074214100b0107540c3d6071f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 803801978 1250 803800728 803800787
    0x30e010212011e090c0908011116140a0204150503100b0105030c09030a120201050124020705090c120c1324110f0609060f16020a02060d020c0102040e0406110a 70
    0x110b043e030380285000c0c0b85407038421515580e2017881c21042d10351000c0200030511003501440c000340121074940c2c5071108a0a90000080c004007413801c2c4010b0410205c401c400310642c000b40942c0c500400d04440c00803401b10800c02864204260269040b04032410010320116038002805440010700001c0750142c002000d0f50140c400300300c416100780d040307140c0a40503035071000028082c0c07000388a000d098100f1542e89115a00343c1403070551041040f900203184291811040c8070307900d1070040058002050500940640f030340228205481a0b00421070580c1c1d0300b40c40300d214046504150800c03040c3c400c044080c095154440d0200b040720041a04107080e070000d6042440c1d02e40940b480008183c1c0c0140c10034480320042c0000c0090048141542604290341d810070600c1c54500355124036070046c1d01c64002d0101500f00a4018000c00b14000800b5140490803103c85003a6489a800140c40050480800090200070702c640358540114100d141c2c0f804158010081c5416103000300c81000e404800d040020f03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 803803228 1250 803801978 803802029
    0x4030e09100906090b01092c0411030102070515100e060f0402091003020a0f0c0b0a05070e061b150103050303150415120b0709180f0f02030c030403030e01021201 71
    0x1003844450500000c1d0f2100300720000317031070100380780c502040c00580040f90302000b4012174884007203c00d158102142080404c040c111b000a0000c0e6400b140c007100d804100d403800c0c001408014010801000031012400d0b108242201c000e0140500140008d002c1c000c03034140c1c20507181c009000304c0d0550ba142d44200000380081c8150743d25117900c02c07030100c480081550076030090560030f9070030f882d18140d0005960f0309a81a081d01c4000800783c84000d400035801c2241548008e1308041d4030b14051074140011004204142e004103040c00341c40c00741d8801558602001c018041320700f040103220b50099491075032104d0303507400041e01c4500014070641e4681c03400d45581c0d0005407100d10071840c848000c1d60380c00b50285400c2280f00141d17524001000040d1000340100400000c48140301881103d0300900c0d1241001017440c00c0b0020364040c0c442d8001c48104c6090f0020b503004030110aa21641d0f42007520700034048a003041e070b1007207603640144200d90042c01641c0c0c08604581c2d130403401514030074240b4507041 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 803804478 1250 803803228 803803261
    0x504121106190909050603120d050711070b18032803180308091e010509041a090108030c070f12030f1205090c10020c100c050f010c0206160804030e09 66
    0x1414003011242030302da26840103400080f1040084200481d845640a00d902d910303039881d0355400280c00700302d0349808180c41d500c0f60391300141d1403a14801d11a14030011f107041c0b0076258048100b24001150110107485009201c8104da00100c0c010510103104001c0340f4205c40080b00900c8440c0303902d0301e0390814140242d070f2214144a0070b0075040c00382c82c1c076031800009070f40204605a0240c2d0150306201c023018003441e0b800c40c188605842e054104a07007a01003102500081c0000b031000290030090085685034021254003800c4844059a15494180b003d9442d02405601280e0841d02c000b00800512010240642c0c0b0541c02d417602c0608030b440342e80140c90141800018049640c5003d0401c002888081001c41c09140111040c0b126910042022a51940810044c95102040c404182c60b01c034000e5100c0000b4074031542c1519400034002d00e60764211155240c0711405a0445004c000500e00602c0f9491b4042c0354500300344045041c02d0700e00820750740b5404c40382c90040818201140c0c141c3e50800210 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 803805728 1250 803804478 803804497
    0x5060f190c030305090105040c140f130507020f120d0c0e060d0606030c05120c0a170405010e0d0302210405030f1c0b0f0607082d0310060504121106 65
    0x110211051000414200d1440c40580000e40f510020401e1040180604c48c01180c0240c403075100c0d6030901600c04014814804111742c40f40620310703001c6080d110300c2190440f148103500300084134a80028042d04000032a103545020350407081907503145461420a80c0c0d198111004001100d000c803010030b60702040610041644100082001e00b98003060383c0014064480c1694284104448031009403950b00402c100c0000e44c03103801000804032080107025100401407407411000e0883c1804070381c0e042c03003025a0700307440310b9440c0c1a61800412040000c041020014a011031428001000c2024902d6480b070456124518a60206050060401c1911504805c1c0402d040d074468403903100101ca40459801140303c281841d100c0700d018034003001d448020100103003850f4603201c1141d65500c41c5900818103013a5107102c19031700385010302059042d08501750f9034006a0303669051034218a00f04030040d07070000042080400081c0003101815201101d19584142d465891100705400180d0034010060034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 803806978 1250 803805728 803805757
    0x10510030207171b07090b0a0314250603060b09090f10081b03010b03030c0a12031401060302280e0d031218031404080a030804061514040b010206090705060f 69
    0x3203290f00300105600258003031000c011648480c1d40c61b24810180c42c01c0100703895101038004010004100300d86c55102040554a05aa8480940400d0364800000380c445110300c000000205114598051042c2c10140100490140c00d00450000007050f82100903d6481c80086681c0410341301079403030740c09038040c040b56410758041c100c0500c10a004425402c42d840d1181d800c0441c0c50070743d41004812187c008804802400c1c0b0079565884e00c0350100401d039120707401c15079038846001132560b22103145400b070102a540540d640d1103099007405d14a0741046206030790f20012284071038032900080e441b001c3c0101928101c0d6061124181540c0f910311603458100304a0a01c000555000140d003003550b602c0e4420f0302d6480300d0102c101c848500034022801004402c2c2d0040582001290107030340c4241d4810b114540105030000303a080383e0000103110b80d00900c5c0700340305600f2060f4245440e009488034544288020000c528000112958501452003214025000010600c0c1016600000c030b80055025946 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 803808228 1250 803806978 803806987
    0x7060c20010b0f0f030601060509121002040e151f0c02180402120f0d0e0a05040911040506040c02060c09030a0c060c0302060c0f0712020115170c040501051003020717 73
    0x4019001e4664150b1041c0b14100780700040d5030380c0c0b510a90066803030798007400900c19a801c00c003003501e440c3c1c040680d4075440a03215405100c0300c41c042000c601940c104103005070300c643c9443c1107040720650241c15074031020507c6407c00c1c21606e0f0100c00c41945d90380ca0380318900d1803048140075900c0414229001e50003504c648040c1c0d20b0400c1c3d074403156014520955083c0c8440308c00080081c0c4903c01001e50061070740204004610041c4103c07440d003d2000b00504600c0703d259200c000508481c4100390440300c000320041c5920307141c60b06109080c1c2c004010340d41440743e60708001009450f80b000410f00c603140040810004a42d4404001c8158496400062541b80396100c03100176005030340c0010101c005120f4040020341e4030020307000752019070000802c1e403800c0c654640d45074401448208481c004541d640d036001ca601105200400f0024030760404141c410702540585d150070301c111403620f640124181001088191a112a007400080b1503140043e1240f0043c81d04030035920721607680364961000402d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 803809478 1250 803808228 803808287
    0x10c0c0f020f0406120812070806030a0f11060325020d0e1c050a0b0108010f1406010507030c1b0f17070e04060e0330060102061902090a0906031202060c07060c 70
    0xd00510403642e1f80700d610215556a0007040340c00080407602e140e0184c100c118414001401c04050b00081031003001c8084c1d0440700000400c60642086801c5041c00400038620b1080003818101403106801d24400750180e9604040c01501c0c1c02e50180c0880c0c080c40420902c1640103071012000418070380d11105844801ea07807801c200051000c00c3c003c01d0f26a518100c02882619114880e80030407200e903000d070112a039544001503605421031001901840340c04c4000030001614a140401a860781602c1c24031030300e040c003c040003010300707a400024814003c0752030b1a051203c0000c080e021144c401406e00b00556451800d50042c24038604104500d100c04200780041d03400081c07094940d92681c0760000c030b200c0d855810141607000b050b01e400d030258221750085030b040708040c14240c40000c814a405032605100402040030220254403440c1100d0751031100b0f1040044c406207130071200c20284000c142070700f06441c0a0000d03100b81040181100d6442c1c68180b100e0b4042d94644c4421001c903c4050210078004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 803810728 1250 803809478 803809493
    0x230f18071202160602031e041208071e0809070e091002070201090902031905150f0f041d06070f0212030112020a18050115090b0f1821010c0c0f020f040612 68
    0x241c0340c05042e517440301f10854100038644141480356801030351381000d004940310190f409840c05400601007105554050303180080c04406014000320541c1e0340200b1b86040e401b13003801c041e225084201c2d810000d4090003480b0703000046072107402150f02170043c0d4900701440180c80a10b09a071003906058000301c10442486640010301240302605170080c0030a0b0385009100040603400b075104c80e403107800500c5003031483c00c04d030b82504003001002d07000040d2079025401c1000b540e0070f84c580c00490350340140100406507501084d00e61024000e40024480c5040401b05544280014051407984468035240c0e06c007596500340c06c1e0303801000d8024446583c0e0612840c04000780c0400d0207582070100c010700c0300036181841261031104131900230185a080c00303140382200035541d210444c0d001002249140c480840c0da80c0d8005051101402c0708903001803103c1c236104500b075810018200043c84180d400140215295070342c20400142e0403100303201042015000100101034580005070384000c445801c40030080007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 803811978 1250 803810728 803810731
    0x30d0f020c01030b100305040c0f080304090c020c0102070b0f0f1911070f090b0d061103040b01050405040305030a0e0f06090307020102100209010c0209090106230f1807120216060203 80
    0x2964240d42071a6911001035042e2640980f449800445507280003648902c2940000e4100388a030070070001540d80c515400c0501902604404ad10317410005040101b5205840340140c2d450541c00a00071030051100040e440e40004e10031015194000264550410048011219010b984075111921000118090200b0215555803840852103842e0202030320440000d400e021158426044540681407941c1e03240a4204801d01c5504402111060000030f03d4900480d031185050f005100e44070318160422040725081a400140118075020600005c00e40c000c045903445243c000c0003080031000c0c44100c034503092002d0700c900c516000d904180b1409180100c010150507000b6400c8070240149129000120310803042030134003191301d540d0001d0041c1858001d441d88401400c1c000610b07682d1313940044803120ba090191200300d403c0c031714900c202480c3c00c000e11400c0020548081a48031883c40b12070300304c1800580600c00340040343d104d40c071b00f00d6510340448101581221104c64416060b10f08640607400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 803813228 1250 803811978 803812007
    0x3030b1c031115060f0103090f06090b22030e061e0a03140609011202030a080f03100603050615030a27050606010813120c0f0f03030b060a0e041505030d 67
    0x912014540303070280001000c01100742c1c2e03503075500710759144c950401607120b6085400340c0c1030684a001480200e4010081c40512500903c00481d0400a07485c04980c402001020030640e00303a0500300d01d0448c81c03203422048040e81d250030240b4900ca20034000a45a010348408090421604003420082962100140c00001e04a4400740020b5110000b42448008100c80080d00f2407021070041080400c00d800e60070034640058250b4072014140c0c0c9801c10300d6440034140c500d034050000140300e107c0d007004034180000c01c281d24040159041c00000507a48200c0b03006103180d21080400824401d0440758003d45140c85111103032040c3c1000d080c40c0210104a09009495501a8400003800d55028842c82c900c10300107800c1c1041030340354075680d003901a442503000d041082020008080000d0182411502160051616007004049450010181d0790546030680c0030344000d000c1e0803030320307504402d4044980a04036404100810711045d08180c12101c1d50000307915101d2014a0b40c0d4a81d0007034404125410f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 803814478 1250 803813228 803813237
    0x9130b16080c072004020708040f30240606020c03100501150c081608091201060b0702210129010807170709271802030d05030403030b1c03 61
    0x41d40c141c2c82c08020300681102500300518224001c58000340d00b8aa0080300800070001400c20341c0c6603d410f209034015412034000320315004010701c40c81c008260503072a810a50802c01a420300c0e145640c04002520240040c4001400c0c0d5a40440d8081d580706009452403480b0304100742a0740700d40082d036500541101900074003440c040700c0300c0c13079680e0b0048505950b000100700350481c403810303822035021202e0041503811042c10700518800c42d6220351070000d03007401004165100c1000c2d03020040b154648101d500c9080c1c2c2751602c10441c001554050342c41540e01155101980001c0b6980201011002c03a01006d60703519000c980400c02c0c4560b07108540b82071181442c824580b120700300646440300140e40500120b001880000105087c4013503855010f6602e140c8407601c15502c00d00f00d183c0c0b01000d001200621003110300900d25113407910501e044d1001081850b00340c08055000710f912803200c14070003804c011001000a0906020b904490550340e4090400d00004034031400918608110120450024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 803815728 1250 803814478 803814481
    0x40b18130b0a0e060901030f05030c01110304060c020d120c0314180f07061403150d0b1803040b0714073201020f0c100e0a090f0b03030a080609130b1608 67
    0xd03c2a165003c0c441e400107054a00c840e429034541040542454100f110244020003580304010802c3c02001c08600b0a8448162282041d00d050b80c1a0b82c00020004215801201c0c030b202c80d81d52101c02c6045944c208040001c1c00341d8168411405802076140030201d4400d80401d0200c0d849003514a501d004290200356003030f40c0080400d0b2515803850b4030030500007810104c0d0030600e00c98104000e54104180309a221a151078401c0410400d5041c840240c80c11002c060800150740c4070010454402c0a540e00910728245c00c00c80da0042d24001c05c0000740142c54000c5c0d2801511104100420107070200c200001044211840c851801e0340d15602ca002d0750950035002e000c8654000290045c00d104183d000d040e2080062040c4920140240d201d0010411000101c2e840c0e40c560700300c0c4102810070030b040032034040e5050b05107000f5188510b4561b402544104905005036a000c1d06098000c00101e49160150700d90160040c03090340602d5001c0d05d4107004e04140845840b4a41501c45645a41d4a640000303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 803816978 1250 803815728 803815739
    0x150a1d21061006050712120f050f0405010c03090302061803091e010e06071e11130e01060e01030b07030506031e0102030f010504151703251412040b18130b0a 69
    0x20b0140f03000003030500c9442c6d40342c1400140200c404803403655800a0005907885c108107582d0036a90b05443c103909883e20340040c00309005c4280500304002c1024241444850001c0c1c0d00207581d40401858509010802032440380f05003000d200301c50307e48074009c1480001d540c00c3e402d110080d0055441b141d0200f2094803c030b00c0d403805d061064540040c1c1003461441e89204480d2502e5035942500402c41d1200713920040c01d682c40d903901d041e803140c03d00c0b6400001541004601100d0071114550846a00d8602940041000035891120035501072814900401e4584810f4082440d11011582014007081107078013154407031a056000d14400e02966a802006982c1d410901007190f0a44041c10b4200380801401c1c0015824400c0e550325220800c401c99145c100c060725404440d44600441140994020074920280488964008504000315000c3e10f10f014603400306c60a01e2049104242c503031007005c15200468104600d1607081034001400341076100809801c03000c014091000024030461606001240703 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 803818228 1250 803816978 803816987
    0x70b040b07020a271b120902040f06060e0f1c081b030a170a06050109090b0a0b120123030318030a0209010b0c0706050f07030e0a0f060806150a1d21061006 68
    0x1d11681c0346c119480f44010458006409a120140c2c0c02a441d107440c0d819541c036601c41c40c0d00500c00d6030b0300c00303100e00c41c41401c1010300d03482c181005226030f001080e029500e5401600c03c2200300c1e03020300c1482e41c0e15845405504240020a1078420a01001c14884c0d40310303410440c22030440d852064441000d0341c9548095048405038010f01e400100303802003d00440500b640a1403904200402070a2882c3d5a102500110b51055100d0b948081c0c80d900100107410140301c000717074962001c00c018540c802c503002c086982d9010b103007007550341c0c8800001103200b20344041c0004d5080540182103441c0ca580c682c00c80e0780d601c0d030113159545c50511500c90000340e410f10410070b880802d071000d0701080c5008201d0b10129840300e120b89500d54000c22300707a4001004078968050380001d0070140c8401c15203103482d80401003a20b1030302d40741d40340c0013104004a90040d6032001040404407281600220141604808a12070007002d004101e805886241d11102c0420005640743c0b04507410119544091303162942100e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 803819478 1250 803818228 803818271
    0x50309040c031401090f020c0f330a0c050403020301140f010611030f090a0807060903411603060911030102040e0c071b030305070605010503070b040b07020a27 70
    0x10f030140e80400c014840302c00f854000d60390809408070050306200c0c1c0011070a003440e03070500b00c1001540c000e00031001c020424418290000e14019541c60300001d8800100d1420700700101030300422079641d841c2c1d0001c28010f005980146801170002c1142541c0607441c2c401c281000c1d9010004580b4580000410920070a40d078952030b0600703000b840c1003052545603469141c0200201030741c045140c14021824100800104000340042d50720203800c2891820640001c100320083d03000403003449407018590b2021103403031500e441c2400d10340030390400c10240f0300360402c0030900c203025145900350300001c00e03c003041d007005d88043d0040380e000c441108031904040c200d00c158801c400d0400c00d8000007030401e01c0381002420f03041c0d01403064507209000c2070a00113000d2486400c101c1c0400e03070101e466814031400b403103228090b15064000700100741c1080d0030402c081c021841403d030031b69000210b1380f045440d0040000c0003000120390641003020704000300da00308502c0c010b218103080d150448000c580c0140c00340e80c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 803820728 1250 803819478 803819501
    0x50603010203130b040221061501020307020109150e06210a02280c0c030602310b1309020c07150318031202070b0901150806010f060509031504050309040c03 69
    0x100b2800b00181d031131840d2008010000d80e4009284003042d001844608225020b01d04810301800c41850101c1101092802060789141103603c213200c1200141d800030899015107440c080707040103088100d1011500520010100354000d0804201840b4909403560900e01d01480d01130000390660b50752062004a0141c0103600d110780c414a00c6800300c10500204190314421f05141075038000e0302c962100e0900706443d41c411180d4a90000b107a2030034000342c441c0004000242441c41441900c2040016103041d46e42c0520113400f100025182c0ca1264107102c031000810304000c055445d120a128140d403100458410101895021a41c00703e64074840d1254801e1111050075000e100b03101500c080341d44d95507001d4081c2c9125400c103c014003142c441c5c00c51a109071401d00010410060032100b19030007071100d501c42000c550040b00148035640024003254280c85061603c55224000000045e260000008100250f100510203001c180107000c00200b034501070075182441480e101481c102d08407840003460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 803821978 1250 803820728 803820751
    0xc0908060c0906070201120c08180a03020a0b060d0c0f0e180a03122a0f0f050412050a14010923030307080703060503011a041b02031c1815050603010203 67
    0x22142450050044d24945006240c445003034015042030400b200c144a10b6031700418540010041c230f8040303407013690741d0040c41e04000e01400d808665000e50ba0312905600100104d81c01400981141c0360003d4800d40c00da0407040c507001040d590205498a41d03410b000d080c03080981e00001803250340e00e10040040002c062030003441201c02c08e0718200c807020300c5a07603217210345512100506030480050100004004820180b00c1d13800080301400703060701d00c038500c0100901400c00030700096244c020040e10115854141540000025844c0c02401c14807143c100406000c494034034045108015400150302c28440c04042585944a0141086661040014403005d03070003000006c0d03c00f0311a921150f0004558280803420940340c100003030a507020203119803402c0310205849112480c290080180e00074a9085100c0d6403581004029201c0c03083d4a0a22220070f5000031800040c200e5034407800308110091000341c0a00000c0c908030111440801c060100941041c0120707113949410302c00c590003210446007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 803823228 1250 803821978 803821987
    0x210304050105062409010c06091a01060809070603050402120303041a1b0405011d130b191401080702030f0409060501111b010c02040209040c03141303080f09011e0c0908060c 76
    0x104c81496001106043c100058a40c03094001480c2c2d00484804602c19664402c41d080480f019165294059000d282000100b00c103004d0840e0000c02c00005407049840d011a0f2a9214004104920082400301240d840004104805d121680050b02c14001c114510403184c2d8a41c0d40f13402000c5010a03041311600d060400c030400107580101c161070381044681d05032101c039040400000c0c00c4c2400d076280c00c0d801340d0b0312015204200c1c40c03d1480106455041140d1841e03040c1004141176000000c90001c3d0f05000701072020861071070080095401140580c8442c03541c0395200c06160000c0e290901c00c4a000c1031207409250a01000400c019540001600c0301010000002c00111a00c01d6615400c4e600a075007009014501e450318061003c0300107080d103001c98070148480b015540e2075802405400d003080b20042e020300295104480e19002003c00314080810b85440d80004d005010402ea080d61203507001d4103040300800c00c0d8001003003210003604c071041c070300d40e03606982c980740c202c11a000c0c1c0020a0400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 803824478 1250 803823228 803823289
    0x7080f0f0f1503010903030209030d0c051507110703030c0c120b0a02130503071401140c060406090606120c0509010f0506090402071b09021201060c0809100221030405010506 76
    0x18071a445540d030702120016400c4500800c0c2115215401a8002500065070420754202048101003402e01031801c05a401070b15100d580c1c4842d4245c2ca21124054a240803800281c80303070782c40031402c0200c60b09683d0b51075628600540400b1244074100c40c03105404000251403d03180100d104000e4106040380055990081014003c8d4045510003c0803950780101166540b002c1096901410b0100000043d40c0459800074000da1803c7c03100320044c4d0420000010380071000f00e1010703000783e40408d011505042a250140240c00c650300003907039031084c039264202840260000c000440e00252602445da988a021000b0402d03c1170040640011042000c014641403590080600301d001e01200809907024034031611040c0d007150b11101c40c00f500031842900102507001b4450041c01d0604100605c0104c0c5e03a1202694001c3c040d01d60311078a08201c0080c0c4e1640240210382014400550080c0d40800a4025070360b1a0010307181526151b1801700000c0103030900600e1340b003511015100c0c0101401441 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 803825728 1250 803824478 803824501
    0x20306060a23040f09150f0b0708040909030c210905010c0c090524010201020405010f05092e1211040e0910050705040504180201200304030f0b07080f0f 67
    0x450302d044544411140c0500c030300300c16a014002920342001c091414500c2d106011080e02c0d85038011050030525201d04000c1e00f81d0170b13184407084443d0044000d0301d6910504041c01c1c5800303242d210181942c01c111410301003540c0016080c00d0540705600500328241542a2032881282c2000035134042001d481003448075601680000e1f2a0510683c00c4c0b8503115111070562003560401d455295601200200983c22000402d05c0d80204140a100850130503141000080c40d540e4000d01860070700030005a0518240c03100402c0c1d00061a070246c2c0e80f101031021000481c458200729200b02c00040ca0700303070006110300c3c49011f5807400700a42804141481d04044400c020817a014001400d948a03030a1107104e01540380c02a60320983c8280c035000c0c0c5851518046c48259000141d6000c4028400c03011100140c3e0440d140c00107a2400300c2c55420300c0501345030414a1807149420140c0403d00c15480c071030800007406549482040f0a0303a4084041d22400104211940700342c0360745034010341c40f0000074440b6013407 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 803826978 1250 803825728 803825747
    0xe060f04020c030d0b13050f01090c02030c0106080d120e070303030c05070b010e040b0f0613110403150b04060e04050a020103020307030b10110f0d0e0f010203070209091b04020306060a 81
    0x30001450031034070070281d9241d40e0044092580d4292140b4004540349040c4448445000da044c0d0188018902610552150001400b0b4010440c0c3d46440410585200308255800110320300020048591034810060f5a0440d242c440c00000d205242000c1384a00c2900410905101c1d880043c000d06055030303002d03400303000e01c0c040400c01c0100500520f07001c01c41031fa0140b07008000740e02408903542041d05005c1c11101001f0f189513042d11380c0c0c4c8103010598a034820400b00325407207200001298041c5c0c101582c91403080364400b400c510100222074109038143e074000d103031500c3c04540802c100e030780d910400318001404441c003034000c0e08001c0146000d175009130010b540c40714007894001840c510120014007120401022400090b051994041c80c0b00010800200402c1c10316001f4254610f50510041960714034905040c022210b0f4645103503282d00070015290038950081c6840b5044c640018040d5540980c141810b55030300b402003c601e010f042900c03c0b01d02951020f4070892409044882c1502d41110307 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 803828228 1250 803826978 803827009
    0x3020112050705130b0a080f06100c020102070f0602060a0c020c130b0f041a0a090b030c041a060415080c0906090d140f100e151f05031509060a060e06 66
    0x1080003a907554406072841383c0003410204000e00d40740c50070300c10020180b900040c001e5680c0401001881415070b103915200340005601d1800d210101120710040b420300c1c1207031b0720014001020b0040442c40c0d9802280c5984102003d40e03007000b02c0041d60700e0490b641d0280c80142e070780202c81c4e250519041001c54001095914002e0311a00551b01424040303012240c024040010026034a00b98110ba4031308200072800400c0c4c0880c05101d05580d03c000030b0348804581b8417152240e6940c0da8260042e40300041e00252240008001c0d64130b545d56070110480d4501070004240001d40319030300143e05074440703005840d40d84030060581400e020303404041c05119850420141c07000c03480c015495542d92020040306024210032000380604880c403034a040141d41d85140080b5854020102c2d1801008a1446d066803104c1013003851039112600385000b10040c40f0700d40040e6098010740c0941c21031103111600c407a0085030060100c0310a40c0c0d504070084c040f078400c0d003d5401d05010100214429150454204d503c008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 803829478 1250 803828228 803828237
    0x30a1101050d0b03160311031b040b040e01060303181502070311180403030615030207020603070e0a0f03240c231c0b030f150109270303051906030201120507 69
    0x34010001c5c0c0740c200c010356030f00c00c1d10a48500030300070440000340709078130400290010440066420301d0990103941f10300300c9a000f599200706032961036480c0d8010200200182c0000c00c00307240c80b410001e0080080c03d2101c25552091030000480080100034140d640d600303a400f82441038116641c03480000101041564042584d00100a140310452034150186100351000201545400c413624101c842e900b0386c400506105000e42409038513000100c80d440030071460805006450707140006d10031001e0303401002d642c00204901000b049110764200c5000d140a141c40400c0b28051500003090b22448101140001c4280e03800816141a174007410b140c00da51074000a0401071000314284100403034000c03002880c0d07100e8600d40c14500b000e110ba02320000c20003004d4161243c001404164419040c803540c101d440c0d41c1d0f1401005140c5080a00c452a0301d005410214800c81e410024003a080948001d000784107a22080280e1319464810341c81200d80c182c5a031891103404609117030041000420510600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 803830728 1250 803829478 803829491
    0xc030813060609242412020a02071701020a0804022b0b0609060a050303120405070503010f0209041b0c08090d0b090c100503090d0809070302041d070501050414040b0301110a021506030a1101050d 85
    0x5469001238540e00c2510f40c01440c4d1b15103010460b0300070103402440091a41d1040189004a0360300c035803401c0d403098041d211010902510004a090400c01501c00007010540c0341c104010802242a138902485003190307102c4507920b801c030412004030502e00c10a0342c10b07441040301c1201c81802c004a1ba91150251041d82c03004c1766640701003400c4d10300706142101032300d0f07002910304650316083c0302c2c407091359807400d0071542c400243c84400b40010b40c0e4100060071030400465005095600c5502e1107912543c8010640c540d8109150260358540e0100065885000d64664555010340f0800a6a1048036414010554681018000d1310489000761001485c0e018015001c0003580744d5001d1030841c207003112001e8581e213242561890401501c0e81045040080c03c1200700040e028890354030140d0802201c0008040350500c00290040c440110006894140071442e07000054011035051080d0405544109999540c0d008160304e94403058130003000d801a44d0803544095100f4000b5003003100f941040000c95 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 803831978 1250 803830728 803830757
    0xe07110f071d0117070b22180c08040512070f14060f07020a030909020d02121f14131e0504050c10020c010c0308130606092424 56
    0x511801e5003019030b030881c1c1c00c20b0203060304000c1e030407440c010000305010409000d140c801d42034955295100c0c1c1104044007040d50784201441e800741040c0d4594a59000e0021a90b814860b42c61240d00020740ca1502e280440d51204980500390703281c07103543e100c0082e25070007003038070144812508200b000f80c0b503450a4001090010f00e120300c0c409100300b0148014500c03450a160b100700c8405005251500b103400c540d00d2000080e400c42c0000d01543d0000101586403280f03005940c00a004000900d202c1804103030a00c03000c030800400e40034003410490500800b0b2038403109107545401c20758284d40e80000c1030b25140d070709a4850358000452444c010b1002c142401c000701c0700c2410f403281139078142e82540101c00c0c1a03e09140044d100d81c8200070a00181c481250950006494035181680160901100000041d002182c0b41800040c0681c4104100000b546841040c002407020300c041e5030151110690500c14010440c5210049036440e00001c19000000c8585010307141c2e001c11000c0a004019072030012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 803833228 1250 803831978 803831983
    0x31508060c09030d17010e0a0b0402030a090312090807080f0712090e01050a1d2e0905100e15040b090a050610030c0518030f03070f030908070e07110f 66
    0x1106000349041d1030b04401800c040c202010351034654180043c841203c808a8100d003500c6044070b00341503403070000f5950881400b018000c00e503102540700341300204001cac20715100e03031001810f50300a03920b94010100d00308e0641c086502120000d40501424003088000a000394010102d04c114a09a1381c100103040d6124041d018200340000041100718000703000d40007101c1441070060100303e87e80c0759242d05d449564172840d0b2601000301c5001007034000181000c1c1c4091900b03001c0f404040038182031003100700008020340c0024020f01400904050204260503880540c02082d101d1515207a5919150740c42c541d452444600780302d64215444d00b084c2c512964411441c280301b40500a40428245482c03030800c042e0481c98960348051510306550080242d6018040d1041015490304030036650300101c001070725020700c50b00802201c4c400050f00c0c40800c01500b59005c01284a070311081590780c0c40320740703940d1038005901981c0c44034440600018080340c841e010300314400c0e400ca402d540c500e40303c4c0e03400b990 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 803834478 1250 803833228 803833231
    0x60603050a0c031101090b0a1d090c1201080d020d180b031005041404050303011202063c0c030d020928051203031515040f090501090b01020a050a020103150806 70
    0x951950380d541041090185045516031510024a0080110b03420b040300d075a2035000d038201c0d180402c6110f80401c0c01540c6035141c91110080c00400ad401189001101c1c0f09155003d00700543c824100c1200004140c00009502038104480340c002d44802c803603204046039510144521b0b017039030750081c4000095000460005501900b641ca04000401d03060106010684040b49416600740301440104008034001000b62410b42c2c08031140142b00030b41c58000182c150003114148000051202034454004181c600000e282c0ea010300c0c00102c003035030115030b54138050003020130140f030b56041080000400503e0b07a0087c441000028051ba1070400311076024040d6800e18170206204800d680d10900c0145002c200000c07001031044002d51075894080d400d5503090b900a041103004030b5001f0518410200f5580036100078200206594540303030740d9400020301a050a11030800e40d1842e264407030b40e1035440410740c5050503030000300600302c604440d40110010320711007681103840901c1d8440890444014850036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 803835728 1250 803834478 803834483
    0x102105250201020406082211030c040203090109020f10170a020c1b03100b0a033c17121b0c0d02011a0d020328020d0510050a18020d060603050a 63
    0x44c0c456050070009000b021001d0080781d11501e07503091041e5103100741118200351307d03404240c8445201c42140461715006041000c0c0754028000f03c01c210050390b05501601149000f2a02c48a21500040a00042d000544907807400112203c0d1001041c900c00318441d600008928401440c040f404102c4a0400c08403190085e521072a0100300003861404100f0840b2141d4801d10030058007166400089814440d4800204210000100703141c2c582034011403290b0b011000d01c1e518542d50303000619a00c10001b41041207032120000e1440e0070000000130706882001b202240300c0c02154030340c0340040b1a400013440b0086c80d014020408040c406001b482002810422034001041080702c114020008410300388402d402030f11007250300c40259800040d01002c80c400300d8408a440c40c0440086801703070540c42c5019401c24050450324003003040014041c1012943c00031304001544420240c0e5040d140740080d45904040100c4280f0094500241c9001445129141c00591150340359242c0d0709003200807100703 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 803836978 1250 803835728 803835731
    0x605070903240f0e0718020f0f0a0212090906040911060a020d020f0a020f010f0e04060b040302040e0106060207060e060c1203041505010605040909051504060b102105250201 76
    0x1d40c080c11207940146107403c84050018072130a1015028203540350010f00c01c044010000368400d008140d5030794100c0c1e81c0303001c003560b1301643c03030100400360100e070750220b52254010f1180301c00f80d100440e101c1c425a040000002c211081c1900d88400300400391560000503242d50395180d8100116607a420018a5840c010f83c010f0000212109006414103031b500c80c0c109981d400c40080d8030016a0380f00704542c80ba120074208400000000d4104491601d071074040340d0b8009240c10390225030580d0840151088030320840b410b0040216400040b401d031040380c810180940c2c088003080c45070701e004505013100300f040079000302e080c800c44095003450495044192510090004140002e001c84107070f14000e034081c52401801154541500101244614031840d05c0403a9994a200b040000a0001220950420350100c26a052609101d00181a42340e041482283d25540181d00d49006915400040c0910146040c8180c904060a4041c100c000e2103450044107083c501024410003240c000b4a03004d90307600 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 803838228 1250 803836978 803837033
    0x801080c090c07060e0307080d05060f0d0c05100203092e051318060e09060609090c060d11090a0305250b07062a030906060b09010503040605070903 65
    0x108508009400d405180a50103003020000c0460310281140d880e103521640024040e02c40010351411401004401030070800300054411412100d80c0040b405000101c44905000090070200600c40484040061540d41d100c4020003103440c1c03001800c4090340d51030040d0ba10301521940040d1800c005020000d0f03a40e900821403890754410a450343d80c0848035810114680017002c0100c00ca04003207442032403040144400145048a4a50020001404000c4240c001c03030405128440c0c031004100c2c0c0c01303800380c1023704c00240c881500181c1c00010f000003074003031480d02c0024480803014007180704c80d09507040401c01c41c00540341c642c1c815400c01180100060b1124020300d0031001862070700c0c4060049101540e0341d084c0070b070300e004001b1228240c3c0d120320001010003103c00094071004051446c42602d08079100e1040d1a203415401c445440c0e4850442042107c0d00c5401d0700c1c20a01444842900080041c400100014031981c0442c1e0044102e0416909083e501e954a006600d403003100ba0301d00d0144640c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 803839478 1250 803838228 803838239
    0x121d0114010506120f1320010f020106051e0f03030408031c0204030b0c0c010603060f020927220b0a0c0e030a0b130311060c0c0d0e060d02030a0209040c0801 69
    0x38106809003400720b814900d8540200c400c2c1990140141c03411140c0e401d01c0380854140010020251802c96000320040c40200e040491621501220302105011038190524540303a50b1041c4950400e070360005001c02247c00605d113084105d1200c0514017a00544040860225035034100060b100810554000303550310116130b45001c042000d200c4c01803a0441c0188810300c005807000d400c0660100b03010103015150602c0102490142031143e001078a0710749090303184806962550020610501d068890140303c250b04003171080704148450f40b00e1501244080400d000140c00150f01e03084504440040e460340419850b80031400e4404d0740c81118007582c2d03c20b4055910703080034400142d140103c02800410310280c80d8060591002040b007244a085042c11070308041c064070803050035013881403c654240c1307040c12194885601240010045204454600c00500e12030b440002007040041e0036903003800c03054401d0501940000e8010100d55400340088013542d100d81c07090100e0303c1d445560300701340f5503d8034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 803840728 1250 803839478 803839511
    0x311041401020d05032505130e0106022e02070302030f0d050402010305090a030c08031801090c030605100f150e0303070b06100f0c0b070e03060124050415121d01 71
    0x504a030000d0001c2881000100d106d8a06500e0045081101c9848040d44860701282c0c4c502c030300c0e0801c0d01801070b81440481d0b0400d45c3d0101d241610403503001c603180c02419801c0b0390b20050074518603102c0c6240803440c00c0c070017840c0f58020b8440c40b88030b0300403a030803c1c96080d9054400e4202510061209503070700d081105541e85401030980002c1c560014010440054600420840721240003910160002003c036140fa81c403a202e6402e0003440c0700081001910038a01060031019074030003507841c40d0034040826002a81c03000d802c0c0c1150348040182c0d203400e02d0203205010307000091086505201e6800c804d20380d2514217100030303c030240c0b00c1c40d0031003071900c3d01104024490b095144110308100c00300c038101d6889a0070051500c0303000d4009003810590307502e01d03104441011039094010b0f05400742000018140030000280c180703441681a050201d800001300441e0701c1d001c0c601c44d02040715805682038502c0d90040d90400403d5250a10106401e2810501580c00113040f06840c6a02d2303550398015403690810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 803841978 1250 803840728 803840743
    0x1c0b0a0501030912140c0a0821091c05070b010e06040e0f0c010309080d060b0c0106050d110907030608011b1404050f1c020d03050711090106120c031104140102 70
    0x7401c0800c070f10495521400c00e460825902c0e80705118015080440b103100714070584160f410144101d500945540c0383c000034513080b00b5602c00c88044107140715411481101000b40c45644d00d50010101503104a41c0d007841f19201c0c8524000b071000c1001440007040940082074040d180d9552110036905060040c00b04591451503006100d42282c445019120340c04543c3c4662501e007481c000c02c01c0c071124201180740f03225030750084c0c03a03603840c00340c0015042413001c0240100c04070310002000003a685105000c540811050014042c0b030b6010081c0c0181d2a00c501c007076800c01f80610b030010b0b0540d00d5015880c00c4130225100240381101e0408078080c13a5a01c03524401c184041c0d84016401e0070300d0f00003c034030280301480d100c0d4811402491100340d100622450b206c291900100740d00391503090740c10301400ca44e00681c0284d0302d20907050011015130902c9040507040310703856642d00801282c2d40840400401c2c040c5030360741c105600d8031046180900301002900261516900300c10914a9400004e0310345040e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 803843228 1250 803841978 803841989
    0x1206080607050304110307260105010e011415031e0903090306062b380103170c0d05190c2102070b03090304151b020603100e0901050402040b0409020616081c0b0a 71
    0x1002e0050214151091030309044829081000081021503070008000c071180101d00c40fe91000401003084d100710219400e1005d480403020031460342c03181120a07481784240c0c10620780680c04000400d405090150084281c4585654a190144005c8442c441c1d11140254207441042c2e41e41c40c003072500c0076401c0341418000c2c2035016100c660ba5203100b421152040c144400340501c048020030317034070001811045440c030090703100030b0341c0c2e01240e800c101807c41c0e08650750f6501c0e00840134000c20965801021540d10480d04440b0b000703c190314440741c0c0c030300e0b04040403801c00c214082d4580c0025034900140c05503000c2d55680000d152a541858440e000c90480480707035104010b264070070260201d4031103a000c0402901505e22568035950707900e14450300c1001d0303072100c06956030500420a00520640c40303035001d1403007154207000707d00901d4204025584070140180d40301c10100701490002000d030094100780c80c4940d001c2390070308480210b42503541d41342c0707150b0100054460314072840d245454200b1102604 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 803844478 1250 803843228 803843231
    0x20f07060c0831050f0d09090605011103431a01030201090303050f090904030e032a130e03030c030108120a050a0e04060f0902090112060806070503041103072601 71
    0x362070444003c4103020294440d803415030389030024800e00030300f4001800313040760400445040301c0c18100c0082140c800c510800465500d0700a01107515840780c40400e60010780c10004605154007050080002d0761000c000d40c0d80108052442c8421000c840c100351400303542092040344d030180c20b040000b1228181d1910700490600394005100603038105d250401034035054130f071003130b115038400f43c6511a0380319461841d940034180710200010503030303c02600c12802c42c080e016150b02211011840c1d81302030b5a402e41501c1003510a20718011420500a002007252110700c0100b000300b41c01030010b081d0740c4261112078217114000010f0114903c10804003543c0202a502149030089400000703141d4050703001c2c2c680820110031400ca40036911900081c025281020080e1803a0b83c5d11220b00e0b00a40c010049580070070140b120f18071410000348500c0d030484640c031025000756601e40104907007562008008807511089131034a020140c41c1044108040d100070748406003050445400d039015183d10a100d02c071076a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 803845728 1250 803844478 803844511
    0x51f05180a080a0e031912020708030a12061d0f07050405011d310c090f060c0201170a09030305220b1e10061112120a020f07060c08 58
    0x180e40059101c2109030403044207512000141c6046035a0920901e0040d4036101d04142000e1486d400e0a400c0c008910807144048803900a001c140d80300c91492180c580c03683c0045c40f030074488500901a004020000c020000344081d01d402d100c40d0103c41c010280c01541400c0c80401800454408400d07030892268105541807618104c0001c0010340c03900e445110100c41c01c90350300c040340c41d0040e4030310151450304442207240d85018801801e0b8a00c2025a120003810300c6038440704180110b20348826100342c403041014690818105030303001100004128104030845001281c68200b6080b11030194002480c00301d0301c03a800b41030040a135480a0701403460710340c010310f1170046100000300b00320b0130960000960b681075840c00f40c035240e900641410086080341c1c0d9400c10052a074010402c030b040d501135440740101e05030b01c0203e1995800c0545414051a4000c000ca40909680d44035020740c4003c645001500d0f01c5071001107450a5000b0040c1290031607182d40c0d0341004240c202e02403550101c0d00310309202c0309 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 803846978 1250 803845728 803845771
    0x510050c0307060207020a05030f1005100b0714150106020705100e062d070506180c0303031906050a06030e07241103071406010e0a090803011809051f05 67
    0x720302c614a80104000d07800a4554110344504c200b41004050040039a900072441404007a281c21443e148410f00c1072808d40050054080c0301c1c0302e5025241200c14290520301260341c0c00c00c003150300030601301e0940300d5040007801d4010840e01c094003070035140e400341005524140500c800f4a502c1d562010a0110742c010b141c00c95100c0f00b050300d115059000108210103d03169017104800302200042c1001000010007000341302000030820300540d4400d040200c200030034001142c442010280050f8160000c0000c80c42d080d071043d00c8403020040003900014559665400106c59070201c0e401040400e860314070a0009040038014440201800c0c5540641d000c07a4101d09034080c03404030396450500081e070f01500079400041040d01c05540e031000d40104004402100307503075540000d10030b0f02242c09070940003c120411902075071200c681e10846142c03e69003058130082580a00e03003441c040c0e503640d0b1b00c2c8680101c1d00821140300c4216440d10180070082c4101001010b42e407000703100c0f120018401640422 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 803848228 1250 803846978 803846983
    0x40e010e0610030b0a03021302040e0105040b063001030321050907210204020708133002030c030a082203021509011107080d0806030123090307060212010510050c 71
    0x88002c09450005201e000031070015103e02c01980010707411030510074001c0030101985e4010320940301d440c03a00f01c01581e6034208100c1640c070351001d10703500303d0390900107014180c0155441d0b03010022003081403000c1d20a1080b0103400c02809a1040c0c00240758210079400d203020302c040500f0070f01000842032100345000d00c00c0564619103441080e464000100031980180410382d55a03c4440d4014029945c603001820303c00055001020b02d184445c0451200107074400d006005207030581d03000c111258210700c40030b40e15a20310307000c40f1060346c05004014041040d55030500c0310b21280792041c0501a03c1e00c21048030100e0702e0950100d0300c1010080e1550501c0980d03104483d4038204401c0c03178002c40e5582000b50040f120301c1f09980000e1700d540b044c5000481c0c0c50300046400808402c940d80c41a403d030b80e424041500340c40108080030000d0003032442d00380743c0702c10322078800781c0c00a03c00084074504a195074403102243d00419120704c0340c0c0002801070065203448085488048002e1038454200341c40341c0707101c3d40c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 803849478 1250 803848228 803848249
    0x100c022a0f0108071b0f0606060c0c0510050403060203070903060b0f06190219030203030a11040e0a0902150c07150302040b1909090c18081b0909030c060c040e010e06 73
    0xb414809003900064005100da499485a081c01c0219888030050710310b00b0001031064480c0031101e0758140913020950f00d01ca00541340310241c200c10780156a034945002c1c02407240b0701047e08001c2200410002c004a0b959000440c0100501d0703580c410300074954103001c022201040440c1d0710030148601e151160340c0c1c1e0002607402c41e00d1044040001c4500c60031040c0d28004600c4195046007001c59003140600d600800034510580507608144036481c070580680800f8451030145207192064030001c5840500d6a500c070034400362020301184080382d51018603040c00d4100d0300100341c07035a12114043c4003055040c3e03900c50b007100150030103609007402c1195552042c000c1000b141d818440080c10f5284003481902610003e2122a00030004554551001080c0b0745941200c1301e040c0048800004404070000351303048100c02032048283c1910001c504000c4c66200252071a00380748428001c4101c604803e006640c060700204150300d039140d1420401664154050780107400040401080007142d840b640c0005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 803850728 1250 803849478 803849509
    0x90a0b0301180f09050d1206080604083016030e15060d080d1a1905031b060738150904060f060b0c070b0c030406050309100c022a 57
    0x10590700380f007980c801c00030014004050643e1040f8840788225136000201900b04c1e000b038203018041d403601d0f44e1200d60381305000d0320010034003c401c0211000b218090390095044000120a0343c0a01c449540c44001c00c080980e84802203000807044044807541502c1030559030f00b5183c0203000c110601401c50905010000c1400b8054800e45504108000100d000c0f0b41100007185803c1042080f6200c0001450303e510001c41e000300b0410119080080d00f0310702440869030f00a000b08600035040300d0452400c1c00c00c002c5160400001d00141000404122600b0a6170440c40000f10240c903203c00c191400300c0209404030b1520f0040028031101c0b00c2000310107220390348155018130a60311685444001008bc01e82c191301418076083c00131982c426000001d00310301000340c044480407034031b9540001c0d0504c2510111001a40b003003104124403401400a580d00900940595040700040220842138800c2600a00011307000500d195103c11a030740c00d90034588008104540c10340c4610004241400d0080aa9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 803851978 1250 803850728 803850731
    0x220b0304060b0109150207050a1d0705090109090908070b0f0f0c0f22060801050111071202031f0f1b051204060204080106080303090714030714060904050c090a0b030118 74
    0x2803201c03c0c1d0290241074010000c0380b008941c5041c040c440213444031002d0080382c0c407410760a280010070255106048840c07000014681c003458903017000584999110794122414801010030000781e09400b80b190346002030090603400e58402d614030300000103200007440b540d07240445c6020b1000740003401d444140c2c0429005031299488104e0103125500f405884060100c000602070540c902d50881111081142c07841d07182d481d2540d8070b640055a032100895400d8070310340d100600c2002001c0d0889888103880f8006420340e035002d0780004981900c21034a070b0350030003910f80b1202640c0003003c1c0c603c60b401c51248510001d4070907208202000b000ba100f2820544d510014a03c082010710061780d048030018801980208461503031003045c2030300c0c0e802c115415460750007000d0000800381000002164190001005403681d00d08003840e09050722030780f117901608210244404030b2140c0740c0e8440c4500941e0b030101e05a17118407240d020090a923119411402111409000401841d10012001500c03c08070040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 803853228 1250 803851978 803851991
    0x100b0907140a030204050406090f06150c020d0c12050303090606102709020315191406070c091a040c02010603030e12030c030d02091207030b0406021b0d0302220b030406 74
    0x10300f1006401076400480e485850454006151851a03000210000440c10148181d5030b480c2000c10741603181d03441e00d60101d15005600c0340185001c100c5c520340e1510441620380030300c0d01c841c90b42c0f03070302c00c2d000c503003106c0c0750380004184104501c0401400b03034008030460f8000d201900880e0020080001824090400e040c03610098003041700b0a5480c10241c00380c0342d011034403490108000d11345807219810321801002a40e484580d5040c0b03440105003518100c41400c602411080140a4164410b1100b40c416899050002c0b890001c03d00440508084142e002c20803c13800104110840d0716010f84042960b01d01501040081d03006000c001300003004a44961511121008a070300794030411803084070b58040068201014941da40c080e1105172019a43d812402400341880390380c0360060301015142031140c40000e00022601c0c1c0043c1000000d000d9010641068000f41c0c1d0703d0003041d2100301000c641c020034034403000c0d0340004504410003014440314503400c0ca862000c1da42488050000b801540d2500c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 803854478 1250 803853228 803853247
    0x108010806270109150203150904080a23120105122406030c040906051e040c0b0f0d050709051e0d060f061203090305100c0e1311040305100b090714 65
    0x103001c40601c64100308170780380c04840741004e403000f5842185e110003071012501d904c06d154202018020320455221581c1803034030f035103c4170590b22103071003402c02c00d8060a4480c40305004c80810000e0018484c103c0078042503941031800300f00407400e4009220540b584480424000e42005054440c0c0a0007070401c2c584054030741e640440e040a8103070741d086801a060000c15400c200c1ca0343d0003e407280718590103242d07002c0118a040401c45a00785c8002d000c041503180c2c203210b8140319900810403107044202ea01d180c18180251003080c0d400403980040800c440040420032800c00106d00c030140d41c0c10303d03d0f05c0c03403c6901c00c000848070b101c0130b0741c080c000d41e40d10b100501910300b5580c4280c0c054420172040d114041e0301458024043d0740240402c58040c01101c1c0e112550000394010900719148689920300000d640d9818003541300d00c002d0509031000d0700c6a480d0080301c2079a40c028000b650048020301000031503500d034601034038070140c03c503806500d8003000c00442c0b940c090300300280340303124076001540ca41026 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 803855728 1250 803854478 803854481
    0x10c1b05030d020f0f07030c0e07030f1404050c01030e19022e140a082a03011220030705010507060b04020f090321040909020102190605040201080108062701 69
    0x5400058042c4203140c5691007441e00000d040ca841c0340d400040380c2201002120745034607a00c02d4030004000311006681401170450030a400c030741c01551807a001802c850b00b016241e06482903000180f42e042208030034001880018400801103403800e090a2181802c0350040d40c2e40d808030701c600d803151014030540365821581c807034252410000019480c030300c5420a03961540e07007040182080c01c001c00c0a041d01111003484200c00d41e07101c61115155009903941b401d44a500703110800281081400000e15070701460030940d03002c0c6001c1c002c20000e1448031072151820b0703009400341801600809558000000342c0303503800070380c480555101f8070b07045844120798545071000c0c1c80b02c400c0c2d01e507206001060f4501c8100800703001c2d01c0b880400b101100c050402c2c0c080c2c02c0e0219010400d151200100401040c48582155046011203e01c1881103500c0090014941580300004100803a004c2d5181c0090105560340314051034003500480024000605201e00c0e0a400040c0c905c1294001c42c200100c00d0000300c1c0300303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 803856978 1250 803855728 803855783
    0x32411160f0501240e0c0a0c05010e1507110303061c020307031205030601320a090f090506030106080d1b1a1f0902090f060c161d01090b010c 62
    0xe1103044402820154501365a40425101e2100c000002680c94018401180120700c0e012400e850000c100342c0c21070708107503400300c2610310703640310081c071060440200060200cac80c4440400e10098101404000c14001016614400a900500500c0401d5031a00000820301c109041540b113a8203562000c40e050103400d03840035111569040c0c1c8052000d801c1030045114200c00d030307140040c101a110080d5030664141c2e8185006100d2013000c111030304507450003841c20605600b4013062940c4e541c540321080e01e0f10f54120b0078100741c44800707200c0c960400740964400b80602c031001d01202000000000d00303154a001483c81e080c088484080d0901420307106080d844045200c003400207140005050b2001d000c80000c0100b60314400e00000350000c860b00c265202d0810040c80e650030412100100400d82d088110035103501c2c05000c4040e10002601918800141746410301080c4c001d400e00501480d0090583c0684000c1e8242000c846280c0c0e80601d8000060380d204100c280c191001c1020039421151 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 803858228 1250 803856978 803856983
    0xb0f09060f06040e09010b0d050a14121b01150e070c0c15020307210906030222060c1209060804151b03090615050105030f0a0f06032411160f 62
    0x40000300402c125003a40040c40c17041c540a0028410902c0302028804c1c1144264006401a0005003090002030501301c00c4004210740e600440e00e102c0244120304a90b5417010703031000c00c1000280000c451071042802840069422185800d000c10315000018003000d10080c0b40d03800b000f04e951158410000c007151181c0103044c40040c1c44001c052201d01c080d64a40c08207000b46d0b0030690048240701c4440d80c50031880d00c500071665407100290f01c0c044040d00a900026801e01071040040b00105190454203e01c40c01841c455540782003900320f40c1003500c01b003200a2070f802d0401080880c14002650084465500158031050300001e0003421075a4000406414241c905045200c4905135406581500211246400783e04200440514403024207058003882c400c050100d4410302c0055503c2250001d102d85c4030202c480b0200300d403800b081d0148111242904103e580741400c60b041c40001080c2104110074001e011402c124480752403500490901410652864800b60340032084100129204c1001a099 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 803859478 1250 803858228 803858239
    0x50102040e010306050a1e020a0c02100206100609050d17270a0e01030209070315080601031b0603020a09031106130e16050f0405010c0309051e04050a0b0f09060f 71
    0x1d480d500e0045400e0020f100941e40c803401c040c0810a500e9052145404483c50f04401c1c0003070314203a0090074065002aa0f0b03200500841d4910003015031101684001303205100e501501d82850804161841c84242d504500104010007009024944407424070000958000380d000c3c146580034603068001c2c0c801c844d1140c03410582d00c0344407002d11200590504080b00308841581d40691a2008414051300074480650b000300f04801048565029a201010140000b100050314541b9403881c40d181c44800e0784200c680c52005545100748030200316402000d4141490154900203002d14010720042d00d0f8003002c1c2c2902e4a4035a002c815036101d50403254a44c0c0c908404031170752a0b945824040c9020708442038081e0362050100c582c88103110f1821242c002e01400d07c01400c150900004480328000c50340708405110040c01d01103860350362106c1e80c0f0390442e070000360117070805d80701428001601d901515460303030142403854a050340c3d40c4a003441026550151650365941d81c9400001e00c0b81c00c030550ba6640c10a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 803860728 1250 803859478 803859487
    0x705010e0601030312180615080304030305090a0e040f0221070b0904060e07090b0c100e030904110310090b060f0f180108040b0a051e2809080a0503070903050102 71
    0x121000301d1920b040b68040c0d11070b082e082c46000b51000a076500580001c0341310494032170060014006901050102d011a1031a5100c1c9882da007400c1d2440c1e000e601309030f0200d0004101840285810101c98018019410440e481070820765942c0c915001c040d00028440c1c040022400c0a030049035505410315050070085440c0569075008030346042d44244c403441d0103181000004a02ca190b000c1c005070086440d50781301c00300d061400a0f544000d410480100e02036000d41c202902c03070b004060003154400f480c4500070f16aa207401c03000300000c0b190003822801c8011030900c200030440e074441c483d13042103a0b1451740200d460410403000038204c3c42020081c21406002154100346006010f0203032910721170f0000710b2200f080c100d5006442020084034002c1c64084010005000643c540c3c01854201040026803021302e0103801d0215100c100403100c60255143e910426640441c2c0000d82800c1c0c0c011031081044603d800b40c94044481c4110038156080c404000041048a4422603581d0010354000d0000c6446 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 803861978 1250 803860728 803860751
    0x4201906020105090316080c010b04020a05190903020135070201050702060c0315010c15062306120114010c0501050108010b0f01030e0d0822060506091006020a0215070501 75
    0x14a10140119030040d840e2200041d591680001210340502c0310ba82c4500d5001d03007960f034840da1907000440b009819501c07498186015101d40c000741003000b020742c44440d00c0d010340020b2140442c425141480401c50030050400c0940d802c444c12442c0d4004041244403070100d030307101521208405026019014000000304031890381d040d03201030f0164006600351a82ba1300c1c1e2403407801040c001a190750f0f040c0207d5070700340b04176580103082c0044402d100e9060048285490710b030784411111158840d21020283c02c00c010054030340c0e50749403044e600044031454100001a54085c5040d081400703035522100c5006010110b581c000d50041d64181ea10500a02c020360f101d102040c043c0c5891013201c5e018840340c15411038a507001380203800d09807403070308014450b14260701001c030744880c0040c201901e10080d02002042c00da003034030410600701c0d0107001c004c64641441c905005ca000002030151001c039103000c40c00c3c44641c0d400314591010b01d4044800c0c84000514000408251051008c000c00d03561904150341d10 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 803863228 1250 803861978 803862019
    0x20915210a0933020c01020403051f0c021c230c07031118010b0706061a04080115030203060a05060f130b0f010503010506070f050c0a080a12021c12060519170c090420 73
    0x140d8005402050040200c03301c41a80d603129840d04038251400242c40c02508030707100724000451981c0c040c0c0c150880c1241c16280d8184e9a018106090140e0000d403000c0c0140034140c80701d20000402a29090780607030301011032100d00354040c0070302044da15001501c6014001c0c0c642160015010220b0042c000240f04105800d155002d4819500c10b5400d03c0e50850503260b0300808001107030f4000c0e004e405142c3c0ca4483c00f80c0102002410260300400110844101d620307a418a4a20509001c10000c8c0b0b81c901002040301015400d110241007201c108014406526501d0590b1612035014407080500c200c00d103403032404c8c5442413000f540c210201a1001460f00f00c00149210002d00400c1c1403202c8440c4100200d80340c01041c40043c040e5980e810071911200d04c5054507010b14036800700300144030398403030703000407043d604400702d08445107040602480400000000d5000d01c480c0c020003050016017240100e40074400040001d090503524246055008242d1161507102050040c50a4400c10701d0012021 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 803864478 1250 803863228 803863273
    0x70809130606120e0705130222060306030b160927090f060506120c0f0a080d0306150f09060818121c020915210a0933020c0102040305 59
    0x9040604010844c0d02442000c204503041d0780018014064000ba203001e41e030081d610801c4018046a00e004218501c841c0d0082901d02a00c0140c1c0c01041262079400d01d500804000740258800308140300d644903407179410600600481713103502e1454240c84c80c3d1480d0052010381c1071a02d031880c6403c0a5405041090800e1b0b81c0340580d01c15070080015444441c107010014074400b84804481d44852114002d91800d220306129403500285403884544c1c6a61000c0d0520303842c60014400b10351545000d0101130403111007059031031014542103a00c45500e990042c20341200e40f00300000d00058802040c0080b00b4204012005040c1400b141c583d484024038401080c4d022235020b40d0b91020f007010410620082d4000c032000564010030700d00101f0007150320404c44d90f0201c3e81e00202c4104c4000e04070078411140420b14802c41d214900018a4240c0341032401c500713070840e40007460241040842c04404071103200c1000c8204100080140c40b4000861040d00a00c5190000f078600c0c412030071880850b9100300c48a2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 803865728 1250 803864478 803864507
    0x2070e10050411130308160524060126071b030804030e120604110415080d0e0a06081302121002210403050a030209011701080a06110f070809130606 65
    0x1005074800e07000c0c02c4500d13030103490212030b0481500002000444e1450015000f2501c03080d07100651b801c100c2d41c56038a0015100306003e0000c13038800c2a81d5030b0b00d0805440c9588080c0a0070400403800e01c0103d0080c0290030b01c075000042c03510301c10100e80d4584c4162800400c402c41d481172013001c41594140036080d03180c22141240000e0606022034002d003840482955084204401082d59880300c0d42c5000c81010021459034010741d880c203441401c04600044580100480b602420030788440407401000900b1343c412440c09410280c40800c04942c0c81520241e20141c4001790b1100980180300140340050200308140c0c06100301c09030000d4040e0154001c4c00351002c940800c2e40c6001041c005a581e0080132200a80400c0b010b016a080340d40c040c0d0000e00c01c505051402d88140c1206060300250f40f0f0007a002070300d05904c81d590b010104904c500c907481c05c54402c102104d00b0090010003c4445128040004000607030102e141c0c81d80ea01e074159044c001400800050240c140c0f6600020100303000c02c101c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 803866978 1250 803865728 803865731
    0x314040b03150f1c050a020a03140106050d0305250b1021050a1e0b010609060305150f0f030726070603090803130807121d010207080d0c0302070e100504 67
    0x10322128600101140c0701c00001a010020804c03c43d810003010a2030400c4c1030b5001d0003002d600300010ba6505008202442c0301e030020405400700c40030340c242116540d81109000d03840c9202c5c5940880e4114060341d21000d4002401d00d00500c220b58085a00000f400d0010602ca44110502c09640801d0140c3c106892541848118000c0000400c83c004945e03a00c014215412a00b03506e0049005048410030309622000029a004010360b50780740c0300d0809070f010500160366a1024007034603070325002c0c0301d030004c40c8441031141820940380014071940840310110301c138401740140d0021903103060000b840106201021401400b01c05081100ca0340c44449010150740030381d0320007082550192040c1411142c0088000d03040d0b568201034070f006902c806109440c0c0c144144566000541600340c60803982c9099600d000a12000400c2501d8405902380c0c3c0e40c2c15074004020500c0505d00025100e408d90b5294501448040180e0906a0a1881d03507000b6400403001002082000004480c1200484200340c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 803868228 1250 803866978 803867011
    0x91305040b161b3201060501030b0d0c0510021203180d020a030203030f0c0c01180b0a0e0c1504121a10231c03170114060706090314040b03 61
    0x8994a2030041a50325041800e01490310205110034071034000c40d40244136003a1100c00301190100e4280c0800044c900980d1154003e0005d1f59250041281140381600c207a0107920700c540c5d035102c072081140181c41c010f1580d00c801403c1d0750701c01c00c40510203a2001c80c0c1c0c0d940d1790810341d00e040142080ca810b0300d0001c1c8101e45501031031510000301c0000b0305415501540c00c41e240c0e890000b0341c400700600101080401030120211031102032040c00741103072080342d91203c50196403030a0251144e00920ba000c40d40c1c075141541c2c80800380400d0089117038808450a502c62900c15090f10414016034215100c50b18403e000141000056141880140344912030307814540c1d6802c0c40440030720264010018054441303d061001a06010012884448000d14156140c0c107074440110010420315820750008440109403d21006083c44ac24050f000d0440440915140c0b80b020603071030300c60007400800701c650350b06803841031501c199042d0038288003840ca100d0751a60340c0d100300c500d41d401c141c603240f566406450 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 803869478 1250 803868228 803868271
    0x33190f0b240406030e0a0b0106020f0f030c120d06090612030e0f0109060503041403030c1e0304020d02121203040b0a1a090a0c031d0f161208091305040b 67
    0x11500c0e075070009080100d15160808100f2405000c460b00221024451500082c00203021507070518060b003450b0b40281003108c144201036280c0b41c840d01114606400c1049611302040d004a00000c0e0410004003d503035603005c19810b42c00500c4150310520a492408402140c3c514800041202880c00703560f45840c2c0b0422181008082e904441ea52800b003030042c442000518000c03070117907034441c2c001c0d00308000300b1240812a50440d4001c980381d03024000001072410940741d40d52240300b0701d136104503800742c15071030158040b600140807804080e10801d42840b014114000402c0710000040110800d01d481c1d0910703140c0812060b10035a18200d85900340480014111008a0710300d1404900400c0c43e04c050721600b07c20300040c28140fa041d0b08054640900b10780e0801c01002e90100600050b000301900c0c4034200c105420141e028204103828801502c080010394451881300220317a411080350f43d510309924001070284044102130950a5007001c003000248031113901d030607116600709441404551400e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 803870728 1250 803869478 803869519
    0x106080c090f040216050c0a0b04030b0a090c0b0a080f0604051b0a090e130614010e0601260711160305061305070e09030c33190f0b 58
    0x480c0c0c54249148148201d6060b89801c90302901d2011010f000145029207640001d41c42040c1c4200c15600e03540b0500d6081071500300100c040700100b01180700c07142410706640d24103601ca2006003001001540f500103450a008034001428020141450001d55501d505000508140c030102d881e00f107200ea50700c00180c03460030b150151610400440e81c501000c40c2c61000c0045090700070000d0f203000c0144544000c6003129284600c1802035844590000b1b4446041c902502950720600c00422150803520040210301041d06000f5000301027401c200c0c00d100c0c29003450140d0300360564640018003041801380190035400600155031523144800b075405281d61500d09640e1100303c0e210007440761f4070080000307481c20b011001303407010580710708182c940440d0754081c0412102d030242e9804103180c02c0003c1810341594204000d8110000700c45112030701d1040924059200e410366104030300d40903007000000b0007100703880c8044a0310b01c04145040080000e5078140000410240903018080d102c44180c0760b0064925 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 803871978 1250 803870728 803870731
    0xe060102070b190c033507030b0d1713090504050706030605030c12030705070e1015050901050d06082e090b011712070b0f0f10170f010f090506010608 66
    0x10b11400070741500c0303d0004559040c020301c0140e00700b08510b40842d203903000c0340c05401c8006086100c00c0611341d1148111001c003440180261040c0b51410a20203000e03150b11a511881c43c0d00180a080020306c1ca8030003548612030102002401c43e2102e00c0810b02d1f6000e94812809680502f0851340041c3d200c1905038100c44442c0a0541e0650001c6460203ca00d0b0065610501c248031074103417070a104150b80d4803031402c00681c0003614108815801c01590380740c107400704401014045003030401051103000180c96442200036190410100140c0014103046942002d402008020216000e000c0000440c07074550401e1100c52880b00346031950400000b815000c0c070a10350741c0002c03125120b80d00c1c5c14030304a00c80b2211071045845000c5c155510103207104000180103214060140641240ba0528007414484002020b00c411400c1d503405100c8201001e003842001e942109440c504681980d0310030606e8a2841c0b10710040310f600340540b071504481e458000040303040c41041122110703600d034103007910143c20 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 803873228 1250 803871978 803871997
    0xa1b02060f15030c04060303051c111204050109020315060103200301090c090312080f0c27040b12210c120304020607020d0c06020c10080a090512040e060102070b 71
    0x90001c20382101d409092498030315402422180040080008617090703680540c01a80416408101d00030300303181000071081c8024141ca4104a0030042c8660b0440c00c2c000c01030071420004880c000542001703025400349007040d4009003110500301c001d894203002c10104642c0b03603001034100038194007080c10300d01c004030090035000364031401c2d60700b4540e004005103520045a01041780001e0000042080c1806c0300c00d0b1890035a8841109103008020b010565401403e10800300c0c0b802c00107030024041158041c3c87d070040c001c2541a603441008000f80150172840c1c03505034006038181114010f460001030000401d501a0010845000d02651011660145c2540d014454000045c85030191940b00000d603845440103017502d0814500d5000b2074406491014211010b66010300700740000b0b41c0421400030390303900884201c0d11844071280000e0151101030b0107100ca02c0d446903104010801c06006111100b8000c0038855200c1d82d444147d624031001c103540307060150003140d0307002c21850380b460106c41c0c6110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 803874478 1250 803873228 803873251
    0x90306040b1b1603020c0108060f190b040e060301060e0603060c030405010f05130b010b1e070804050d0b040b060d0206071209080d11010b06030103020d17120a1b0206 73
    0x35a01d0311003103801c010080a0810000010701c800c140034096402820010b5034062884012402a1070b001c0d241100e80d00e40703941808442402c0000503580c032568001c4004059452680790b43d01440480f1100f13006ea00720702004000820b001c181022480d4195205010480c020701c0382599680044c01c03058002d0300c82c550113070003040c00200c0c0b0921650046400c42d1045000003034070160740b6282d2003110380c01c0c1e910140f4040c03105d412109101131240441d001d8003030104a145000c1c18000819040300e0600060407582d40c02140300300900030044113682c01010058104030031110070b4078040c0503c000490301181c10350780c5000454850704001c070140c900250302601042c0f400320300340c07503801010000315040f000304507840001058118091010100c0c1074056109e0803021200707410300c0303801e442d40b818180b0300031081400104090b0340c680d080c5424440d00320340c20014078024401c1c1c09803644503c041f92007554081c3c505000c1c80300c000345d00078a099401c815455030300078880141280c8034001074810000b0382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 803875728 1250 803874478 803874481
    0x3010f0c0e0f0f06030c16060c0504030b07020d0f0c03090810240e240d05032d070311190c050906030a0b010e090a1b1e080a030f03110309060105100203090306 70
    0x695098004000205101119207100e0080b982d034223040d585403040910000d10003040803c1003100e000d12040d0040305500203003965005807100103100583c000151002c00030217103007110605d4003a40144000d010314070305442a150302e4400b440301400603c2c03521148140264280d03001c8407501100c40082d1000302810102130f8488030150b04040d503026030089010511496104d503240e503001c0540962512a0010799100d1020401524614a0303540740c14240c204419283d4425032003d200300e980a07540350a1055100c000d0741c078980d1911b9040255200031072084017211051103520400a0210341040700d00303a502e0307501d0006046c3c5445140d44020001d401000040c4016007507036082030b91001d0104212400b00f070807515408075082c402180354a807408411000d1112002c070304113160382c1d460705400c079207030241c5001017040d90b0b0a0400c00180400c03a080d000582818802d8000301d03181d074401200a1740382d080480c20991209030a11540748034100d050310742030201d070011091300c60400c0001c026102c103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 803876978 1250 803875728 803875741
    0x3090d08010e06360613060b0714010e030406020c0a05040c0c060905031903050a0b1804060e010612080c0115080a03030b060c0313170715030b03010f0c0e0f0f0603 72
    0xc042c0c1d079800ca0740110314140304019041213030300355000c403031192098000c681c01c081c800c3c019503082c1e40c04220070b11400d1800c24410022000215050a036003c01d080599901c074500d90350040031200c449115501001034002281a030000b8040c4541c00d013100d006a070310f0356400811041b1111100b1140c045500f111070040415204d0b84030746e030203030f02803c1900c2c641159518080c00c4443c1c9200503001296131007043c8400003d844c4034545a850b001c0d83c10241c49450f810380c2441d0b80390002c00080040b5100c1c040a0107210003900048020600352031402c04404440c07400d4403a6402a145031001580b83c0500079440c40d00308090042110040006440302007070580b0118054103071541d4031a00003004001c47e400156042006200500c4450310404001c2d0071305a012540480c01001041d290b80407d9040c00f5951084002d01410f104c0c45c10006120441c000100e405031407090f950268251825030040f00241d0420204500b50808881c42102c4402e81810052004a04546182c00010910000350b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 803878228 1250 803876978 803876989
    0xb0d0602070c08012c0a050c1e0904080d0f11090d0602090d0b16050315120a0b010e07030b120604060513051006060807111b220203090d08010e06 64
    0x501c1d4003400c842d40b4001c0d00c5000f010309440645034007044149030205002c41c02d40700307510354810020a290283c149200d554595a55612072035101911441300b000404016085841c0507000c62540500000820b10b09070030416020b07003002c00760300c180c50b0074103c40f0030450045200e001181c0009540d001c1c100302e500e00c180810000801000c49000c0d900300507030101d40e5100503082c52854442e864810300751504081304042d83e0304040f03c00c41840b8050081c0000c9401150070001401c4003503810a21903002c1541c15483c02c481e5201c05403400b8000720000c56131703021465109105081d50b86040c06034000c50011301180805400c481256904401c010800052481d0041d98005038240040c01e0400d00c1e503221117003820741413040710401c0c9580b80401c120b40380e0405242c55000c8020b007000c1a5041d45011a80e449040607840561158019001c20030280d44010500715445550301c811087e13030f04104c0040300254020f07940b1030b400d442002d484480292140380d60b241a50312040c071112158946c4401e00a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 803879478 1250 803878228 803878237
    0xe01030f020111150f0a0e010207350306151b0d030b3c0a0608010303020c0901030b0f04021f0914040c231e1809010b1204050307020d0308190b0d0602 66
    0x400050b1240300031f0502240c240080c04015018007001051850b0310707132500c1440b082a0700001c0c0c01100700c05c00c60482410500c240c1b1b031300800030745074119001800c40c811140c9104042e001d110001c8d4402e0101144803000442600900c02901c0c104080c1040c6001c2040303980d054510f99440621201107204180c8207086540300c41d1100d000013881204a4100203207074000d00760050000564210010000e2560400c43c0b640c46000c02d880c446100c0d411900c84206070103008000d42c4e4071a4021011900319241c3e03480c801c002c0891408800002441841d0080c8a81003500c87c1480800030103455460300d00d4188582203030281c0b2504c5103002d14651514110484540c158400c589601c240104402089480103544199004d40714643d40e848000c10000202203107605c8a50195214000501060300390504540300c0000b030a00080307659949142c660315503ca0900c00a401c004a040380c44100750700419500d00400c18540b035524030300d007000d0b869411030b0100d461407076106510142c0388000c81c030030ba0b0051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 803880728 1250 803879478 803879491
    0xc0a03120e030313061103481b010216032001090c150905300d02150a0c0f050c010e011509060b090a050603060a0e01030f020111150f 59
    0x81103460040601c0c50554004a50b9054400350b9402400700f00052441031079105401c9810082c01d501300006951008040d01c48404c9810380202007001010320502690205500864131444a10380c604481e00c41c90340058441c050740360703880c9902490b11a418001c1d11806035081302c00910b4180705860480c1c1c8108803440980d021003801d004140c04200a003d0400d038903000d0010581c6003854000b0340a400102a5500420001d4094050206941d0300b0800420501488244840c8a420303242c1c20303a4041c46080056110303c1034103500e610302d640104010f0642540c03120231030b40315a81c8017050f030f00342c501e18850703140040c03005108080c500d40100301030031186400500026580e4002c440841c01c40c4d540060160301110640380c10840b01d0b509014810203801a80e102905182050380880c65144150068902c210781c0400020b42030b8071510031800040c1407400d4a01d06650b07580c105001480220b81c0141d00041d00e82021240481c80040c0061800843c1d042c11903c0e40d81b00507032081440e40c081c004 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 803881978 1250 803880728 803880731
    0x1060b090f130f1b0f08070e040b060714060c031e07120e0606090604090305030109110c0d0525030f11010e07030c090e010b01120c0c0b04080d0c050c0a0312 69
    0x400e90301c010680310f80b6400c880300c03100000c2c04071120304407480004084500c0804002001c40310501c0341d5441a411500304005007848801d910144c4005400390030b075010200d8002002048450511559207100c5881302200419107a558403020800441d0b403000f19803006000c0168011a43d4000c5d5180c0e041d0340c0b146062810311501404940c3d1241512081182c0c005151f1203a030521125107002c4c0c3c103141e00720300100c4080042d4042943d018059000c1445076102040e034550782c290085410360708803201030401d40c1c2030b1034410710600406440364208500c519100c0000744002c88248200300071001d00c044d09071300c801001030180441142c1d450016a8030103101c0d5200c0b40e0380b1095070010016800607512035a40b40074120704000c1c0304030480344d28080c1e90016070b06008010001e640c120f10f42605050545901048034410403c081d030303a000840c400100899208410403081c4035129015013071702e5205036814040380284410459140c09102500b483d150010b580c282e000038000d40c050784a14074001340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 803883228 1250 803881978 803881999
    0xc15040602210603070806060a0e0c0d0222080d0504030b0613020d0204090b06040e06011103070c0603020304020111060c040b070507030b010308090118030f0303020d023901060b090f 80
    0x1000d90910b00c100702032110480b0410501810f46418480a400391a00700c00400c258a0050700192049159100700001007201070b0210b2402c07a80d85003120791071822109d05555601c13850004070004403039000b4903031000c1407090300800c00c044007081c4281e040f01160740309400c0900b9522080340812000c0c01c11980b1448500c1040c07003283d200c1c0090705201c0043c0f0710050b115840d003282c9034107072900700d80304900c20b610420050244007980b58545410035802c1c0b9041001054ae10001d61441c464088040d2494a102100095899044d00114440c038030030ba0310b1003003403040c4500940d0b0722041500c1c1050b0000080c442030003040d01e134802518545009104440455680b92a402040182a0401c0c0c4007504006160307506940c100c950020038082103080321a00307070b18542314040748095803040101099000100148468520303010388694002c0c1509802610311580c004d41100c000c071070041420f032503005040f00c1d440e49041c42250100c0344011005440c204d410010451141e8410500700d43c041c03418030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 803884478 1250 803883228 803883247
    0xc0a0e040f020a0f11100902060d15141206181009150506120606010f03020903010c021c0e091f08060f060a0e040807120e1302040e0c0c15040602 64
    0x9100007044a8080c01681c3e280c40282c014000d8030a22049401d20107415803032200e04400054000400c0081500081d00d82d005100080c11b03840b4201e118080a41410494441d00401c0c1c2000c10448002c3e00242006070551414001648850020401c5580120000811449110103c102c0000d5040141c03108403e00d050240100c44403208140c90036034428120031041e040e03e00c2000c0d00804111008600b400d4501c0b00259900001490f050400c5001d0182c102e10f41e029405483c80b40c50020700034000c0c2c18002600031342c5e80c40c1000c1d01d200d513008030045d00340900c0d025010444070380b00042c15482e599603c14150040c598240307580003410038800703800000c0c40d250500029000f1400e2401c1c41005060400c10000341810f1900301039481c000501c2071000190600c07089449099201444089810044509917450718000d40c074150404400a0030008910a40c4c0c010f00550344840400b0303c02d904c3e8924082c050b4028402440704940c4078154542d014025905075650140c0b103a88090306d04036105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 803885728 1250 803884478 803884481
    0x10050915042c0105030705031c090b07150f0203060a0b0c0f030a05040801140c2d1b100b030c0d21090501030b1008011205010603120c0201090b070503030c0a0e04 71
    0x50303042d115051541107041036a50680328085006010480c0180200b904050010317449482480c8990311691000303030003068442c00381c4c021000030160404c2c0c858032003034a8200108030001d51001c6030400b520300b11007600b00800c58420f07680030341009010b000480c0d042290726000750b03120642c14a01c61284c04000017071001c00304020544082c042c2d6a00343c6881c54000e601e82598000c840001001e00c414003040301041114055646021100000303156848245418029104040d0b000072b0300018000780c10600a0780240100701550041d40843e260302c0e900032004006c030762529840c02d9051704880049141441d0160405000e01d000e5006802d200102522401c103203031114040401142c51080300304180d40e0184540301c071a5905a0b0304006c1c50720900720050014405001d0510000d0700301e8581c00030302209601c0440590303409900096001d04030700b406061840e035110103e000960b2400085402100c0e5804d03a012250311a005504540f605880d0540c2a001040000100543e506004282ea5200d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 803886978 1250 803885728 803885759
    0xb01020f03071b0602030a021002030606121005190e0402010e010512090d080127020c0c03030f090f01021b0f0111100906051308090427080a08061005091504 69
    0x182038008400002c2034800d901020310f640c40101035401c2400355201e8030ba004a45501c900802c40c03401682c039541c25000a80c80e000d8440392940c04942c2400b00f0128942024010701a108100e4080c0482031407a80044000c03c103601818224420441c040380c0154001c00500f1007400050400500340040500343c0110380c541103442d201c01e0744c0300c0111030301039603003014060340507258104200659402c0060110a4490b0016048905541c001010554a1400d000c941d070400402005d4135610940c811100840d0381100654900c554079006040781c0d150700005aa00203c1400241c501a081e01e880c2040703e6502441e0744541800f1061201090034002801003d01002d420040054036800d941840700c2150f0f8000c00d4482c0b55460301801c480441e10100594030705003812200032413507844a0203140302d569907544142c5c48108002e00780300c040103413030000740003408820782d50340b001d03039841c0703c10403e4000f580c10581010a104008603155802c2010040810010310102c86207401d554880712544403c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 803888228 1250 803886978 803886983
    0xa1e050c031c0f0c0813030203041701061a0408100b040b060a0c0c05040c1710050306180f070315021602120102040f05060903070e09011b08070e0910090b01020f0307 73
    0x155806002c5907400c0c480c0c0140e41640c01400c0100000c0000c020b018484003a1a0088107105140783c1e0f8109403003002214003410260300180b907143c1a40c5400c0c4c0c0030303203030354001c10321a03144212160b00306041c09001d503001c0341e012100908500303e000030014028401450308541050f1991065002c50301ca03800201600c016a60b106058a20a41020310710020076411a91107681062000c81989038001010440b02003c032103070403032607250400d0f440c0210940d61700098240c014001042441c1062100034074880b0b90a20642c1c07440e40c40115234540b140454040244044280011520040940c0c3c1c050202c400d8100d502d02d01050b5250001103001c240d0100c20301c203a0390009824032000296040c0365000342002d88025040c80305d080c00203615008180210440240300500040015909401260350030104000d0003000e20707074070781d00180360f00021a008000300d55440125085420841011880303014901d0101c43c0d52420030404601420303103042070380e0446c0704043c660105948140018101daa1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 803889478 1250 803888228 803888257
    0x30d0509011d0a030c0603180804050f01091a0304050f070b0d090501020903100630020f0315070201020406090b130e0604150b0c070b120f1b0a0801060e03030a1e050c03 74
    0x1460140000e042d40c0c030618141c0e07008d903460507643d00000d40450684050314000c540c40713104182c48034012140f000243e40419002c00e1107902030440320100034010750282c6d000340182c40080003001107656513800b40744144070343c108041000100e1401940e021546040c0304800242c03a142e218000070340341903002c200c0d010000e0703500c00c2c0801902c4402c483e00c2c0c00b5007450349080100302d040c1d070350940c0040052002c064000c03150102c00e880d03d55001c4c007007a05168a0700d0001081d40c204900024000c2d0007030f00460380862410180400c51003039810075201c0d1122200d0401d16070780d0801c80317070050f004409495250895150f0f014810102d00f04151080588240802549c07a01c40d40c1001c80d01d040c42030380c002c1c040c4402c100000d40320100310707000c01513002e601210382200c81d07200d15894135050307040c003000840e04480101e080121140e010303141038101d800c50383c2ca0320f02109060041640364030071040207002141f6021b41800040c4955441c2501190305404c0040c02c14124000c1c0c5030443d8040005603414a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 803890728 1250 803889478 803889503
    0x7080607051e030a1a18061c020a030818010e060921070306141f0902300402090105150706050c090411030108060109182a06090311030d0509011d0a03 66
    0x80032140301080d90451700312540340721880c00c0140710754040c40240c00390340607021b80b480300500d0075901e40c0900c19043d07002c0c00c1142c0c106e42d030741801d4407180c0042c51a2052a10020100903182d0b10404104500b008000c3c61545070000c01c0081019280b44e912008800c0c80204c03800c440a0b03042800404011801500c0c0850140c01800c00444414030081940c644c40c402142500c002c250b140456030b0507a86c0a40006985140d0014070300d601c81c00c0307074140381e20f60500b010011101981c0610454040c5109030b60391542c60b603c4000300a620401c0c055440201041486800c0c00714086400c241d0f00320620070151843c00746201c0106007500c018102e41421030340008010445042d013000300a0050198030010090f940d04001c011441c50344000300900210403400c14890086042d40140604580310100604103540e90395000d881401103100980341d55030410f1040115050100c0c440044115558070146040c820400646500c0c1c140340005c0c0d00030400700100e002e2910b614000304040c6029452420f0f84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 803891978 1250 803890728 803890751
    0x1c0c020a170301060f050f12040c08060708040201120c090b04080604030f0906020a06020d141006141c05070c0b070201050f01240305060117040807031107080607051e030a 75
    0x5841403018014241d00d010030041225950207990080c0f0f0f8241407501d1030f0340308126007008405d03000c0c00020b000841b824005100c04c02c80d600132403100321a45001522090740c1c0d07046080c0c03030780502103c0103030120b800b1803000c0c2c0000e01190720110b0b05400d80d040c00e00920f038803039540600c103402540140743e45a2054003400181a0807030040325400e4442e19150704180d04101c4000d41b01c1400400040a5540200300e440007500039401c41c2c5846c1c0703009140341419240440141003034106620500001c1090320b50444800140c034011500c01404400c441c02c51000a40303017480041000034031100803ca05204c1000c00100c0042da81070180c1069800420701d4100000001d06945040e0700542c090000d5082031880c01000c0c42180d0102d013060309001a403944e038035006a401120304040c45e45a003064a040004004c4a0340c01303008114001c0e514440c5d10300c0002d4815585103003900039101c07650b01110000f150144284010003907150100c0050314420445552554260001e0307a02e01102512002120744 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 803893228 1250 803891978 803891993
    0x5070e0915040f060515060703270b041401111006061b050d08101a0304170c060a0513080415140421110901060c150c05030c1c0c020a 59
    0x2007503141031494940e0781015a1504070700c8080010041030b02c0e882d1340000300c605040d100701c16160320b000342101c0e94442e980d1400a0030303c1d01e0a03000e10b006103c0c81c03820b52450309041184c40c060f15405008586800c3c18041203582801a62400904000000c2c944903090142404040c0306101201d001003803203420700e00702410084914201c8803102c080d0b0515200030400014010450b0551800d007100c00742c60700010050940c0058002110191030384800c1411b89411038019071107640510a40100f0b6584400141240d00c03031003c6d940c004e9440b42011940054040c1d1003c1c2d00001309024181a08209990380115900719601058030300c04480f004001d007980050340059060542d010741441c2c01d040899a0604440c040c0380c04004084440044082000e4501c6508401000401c2140309607980c4a00030003203c9518811035500011001d103002c44080c50003070340003500e502c0c1c4886003140c4d10040e96101d03e030007582900844001c41810901640c010f4404e103154803002d980030303100410050400c1039 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 803894478 1250 803893228 803893243
    0x50c0628081314010b1c1e1113020d15060206090a05030a110312010305031e0a08040305090103020d050702011d06040c03020105090a170a061b090306021605070e09 72
    0x61080c2441009040c6609031074600b074040e80603003001400d000d030800460040c6541c820792a08075060b15125100aa200c02002c214584a482580803600c0920545104000d400400400d01401d8007004070403898680322610034031030b003200b005081185002220b401d54000340c60000482c42151014004942c0c140700045e440242c000061903c01019652141d480c410038486c003003041000c00c1588500c0105200311280d40c0d03100400b1031803558403400c00c2502c2c1d91201c0411030380c01d00038503035124010b42880160f4540d2146612015410f40c2c50392000c2e10309a00560590341019800c0001310002d41c0144039060040229500000701000383c0c102940b104048560404c000743c1c8132008001c00507520f80c40d01001d59a085c030b81903442e440c00d200480c0c0340f100e07660404910074011003220301c1e00c0c4500240600d41c1c507000701c17010301c4091040c501140081b41c094444a000440201e424408207009400a1642c1e100030b035080d141d1030b0810380742c560802d0030f00e4204100880c506030a0080c59601001b80c207 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 803895728 1250 803894478 803894557
    0x20301030809270c0a09090207080c070e0906010e0c04051c050601050f130e03070c090c12050c031f150201060e100806070e03030409090f0303050c041809050c06 71
    0x344101000f56518020042006201d4041094000b80d001c0da801e04c55010740008084041c829520f5000301e02c2c0c1030560350032401040807103104c0c501000800702184216580181c05850162086908207800c10906070380040030110340358410040081c0c20740791680410b80da98806042c045001c402450034606000041c0d0100d4401d1100c00d1000009545c0c01d401c03541c881c01011000222000e00703240f414211b0150860103002907001503000540c20203150082c0f0028080c0759202452192240b04800031110113481c12140e0b50400c0c40010540000d40c442e104000591041d400003160f51180c28101c4404040320840c0181d44a407170800441c4100707003950350814107100748000310034105280144d40300c80007003100e02008101240c80c0007d403014001c440142c2507070601445210702c541808821101d00303184c114006440c010010b03101c03140d41c1c8203950691300c044030f2041080c0b0f001d455480140074005800d0b51203000c0d070205100c42d503480c0ca0080801c1449403101038403910745120110300f5070080302c17651b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 803896978 1250 803895728 803895769
    0xf031b2907140304050c120601030b0c12071112030c090108150d1218060f02160320060409141b0415030504140109032a3201020301030809 61
    0x60007003072a0480003001100b164242c0c415103a07650b0b401d05510f0300b903d5521050b0858206d0707500d1225a030000c100c043c16a07004141001154880030a01c0c14548511688000c9014000300070407a11803258040d400c08501507004c0b141c860300000743e151150f500a840d55010524006116191960040140365000740c2d0110700d0000f00e40001c01260600d019100002c0188000c502501421070280185000802481e850480041e0711404c010b00a59100c1421001510840c0c03d49203260b0000304140054a900c484c0890002c0031400c0d440c990054a800487c1d03000c2400d0002051805552045410484912419643c9400c2401d80d80800d00d40c0b940c0708804035503041105000940a100d10041491014136000506540d0350814143c4600718014040c0d407542403660120515a000303800f030b21131061035603c80c40600d00503901200450154540100301310035085180c80320301540c000f0130b080e1109112008d110f40c000a4880c0742240d00c00d8008844007800861460117a04291000041d0700050000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 803898228 1250 803896978 803896981
    0x907050109050d12021222170d11190b07080708040c0e0705071a01030204051014040b0307051009031b140d08190801170a020d0f031b29 60
    0xc58942051240058101c2e04c0006400c0c3c4c440348204100c03601c90101c40c441c1500d407407102450a01c055900015102d0140b1011070100314010001c94003030880400707d00401c0165030740b00080d6068440480754030120f0054070883c070156858240f44d02c60b43c41c450a0311980314640b10300040d00343c41000e0801b000b04403940080000040c0309945000585030010300242c09551501d40031039607441044001451089000c01280503070f20710440040c1a00d108032018000c03a5102441100050b540c1d105070300c40a9101c6c100041c1606280d404144400e2000c4d0969005644540109034100200c840d00000642003900c10001d0160700f680180501d6800c02d0700043d401e103081b8a4501480c0c2c8003030041d00c0b58180818071401c2103052030485403c0101c1c1c03105185220510385000c0c00100c000d214490454000f11500441e80d0404114014043c2c0e0080540d0288a05a194071a9a041c114000c4060101103210714a03240c41040048400c20300c100ea01c00303e002f1349032440c3c03441c5113416800500036240120 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 803899478 1250 803898228 803898239
    0x102030403110f0a080303070e040e1b0a03052d010b010905091003050105010f050109090e1e0106050d0f060b01111c0210061217040609150c0215030907050109 70
    0x1200d003140c0e042040034410031080c000003140b118034920140e5214848440009016001202030741c403a4200344c44e00c8940c8404d80043c0020754040c1d80c0f030040160041d084149078500311074146c00c3c003400b000e0003002e4441e80340d0f41c41c0ca10f84610780001d4170212035030601d2000c483c040c2c2050030607210400c0000b800301102410011301075071414041e4502c0b540905000448442d4072100c820300440e04030700207222550b0f6907040c83c401c1c03580030b01a80b80001c0e104c03000410307103a00c0c0d4060a400380c10000300402807180201108220380001400300c544e15501c0e43d500080543c0c4400c0b034010301c0341c024200e0310f030172a00324a0440212100c43d48100e0600c00280130301c1c0d003544008074403802120544503080c544506907010490034000710f420000c40c024071780000803d042c5003c4000d0b00903a40304124005100d00c0c449070a00302c0b07000b944600800902090005d12030450803030030394031488400c1e08000d500030303040341c1c00200900099940c604454402104001c10751104000d00d40c01400c00307003007440c903890519 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 803900728 1250 803899478 803899483
    0x50310090b0c030a090614070e060c034005120a23100615031d0709110c01090f0506130f082104050609120306180408131e0b07020102 59
    0xa1010749070b80004800109002001d0b00228a010341c011000c02001400e0b0a0b00e080340c020035200ca40001c0e0704200210106d007000780869402100c55402107013807001280710440d10340d001d06d07554855283da840c481d48122640c01683c0100380d00070300d11480564100300600c907900321841d00b0b80205d03500c08010740b00487d28880390304102905011a4421030a0744a0825107402c4858420f5400f00340b07805400a4105400c0055024105907958103011103110b00e20b55100c08070b83c01c040340d03081d80c114402c20032100d5047e61102c5120005c0200003400c02d0000600d06007161000a42514070060750080c0104010301032007000d41c0b080d0711030313078294141e80303070b91035940b81e1001c50310005040040000301018072005504820311510055806444145840e181036525118140c0d0394020398840ca09200411a4521007542c4c8200006424420301d6403c040c1d40341000100588141c4940324100308014440302002002000b4040781540000d9440b450b0f6800583d01200380d02c030070342c248400c1c0034000c0180c0c1d01 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 803901978 1250 803900728 803900731
    0x7051c0605090a2a09090e0105090d081b0c0c1008010617060d12170601031803051308060a20030105060415021912020c09010609091e090804050310090b 67
    0x10303220000301c4c14619210b500071864400c8a030741a0f0301081d07101c016903540c032801d0542540c0c0c044e2403d0154200910070b0b50f090340c070305035250303401c40d0000d0b5040251180b28941055006e48600c146240300021080040300d5540040030001c89900700a0203021039040041003540f03000f41c145803029040d0f00d84040200440300d1400c1034842809000049040307aa20450803640c0030750002340035401706055100c0034040c561280341150b1040f8889000600c2503009102d58108480002c0e07c041e440704107664100d07800e0740a041c0c95245c54880c8040442d042c0300030070060744940c1604000043c13004000c80c800369030144480750710402c07800400051109490381c00903036040780d40c14814004c0c0035966103026814045941203142d004800c100e008030170b200000000c0624440c654090f611401541028851408000d005140214000000c100071201c0503500080250300311440002140140184100682c1e1441e40d096030000800324003400140f4090000440c82d0210010030881c00c00e10b5619400d01031320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 803903228 1250 803901978 803901991
    0x503040501050f122a04030c14040f0509060907080c03190c080105072c010e3d032a05070c170a03140c0c040b030a080307051c060509 59
    0xd022804001e0900c0c1e0070700360b030491800d03900c0720b101c50b05d01100c8200811140e03283d540040c3e2a0a1418240008034204031019a41c0004001c4100d504000c02002c210074620a207541085d1794523240c42d0920f02c188502401143e024010380701768181209001c2c0703803049540060740b10f03400c0400c04c1602076a0002e001181940915283e6a4651041c1000800c01e5403d9224941070b5080c0b8040020560744020036108000456008c00b20390320b114071000d443e900480500e24042101503104100a241001481e18103400b030228680382c1c03216002c80b0108800b0311910364a1420001000387c0d074540d401d4000c01061002200e2905080c02e0449291540351991120400c18010f00042000c1400395000d80b280160000442e1991482001c201031552800c1c07801040c0c00044440c09036002100d56030080701d5a000030030009007002c9040c3c0041200912070741850550600c50400c03942c0c0042d5a400c003552041042c0c0c1c0701d46071110a41c0196402c820605d00000080c0341c6052401d00c031070760760101a6a0440e5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 803904478 1250 803903228 803903237
    0xc070312030207120e0310060e07180503070e150d0b0106050307051207120e0d0e040e010f1407030b0315040b1008070906030201180b0f0c010f05040f110d0503040501 73
    0x1000600070780c001c0c4a03d0070041e020001c5035950368119508113000d03011242d0142d085a044000c501c0040e405c80e800c5004081d024000c2c1004140024441c3d00f4140008086e90319007003100d035031040020310744055980300c07040d001c47c6401005040c40240d018040c0c0a0401d4821003000c0c212651000d47c41c04c0c050054106000010021891242c0700f4400d0300d04070005910226101d040c007400c003808080050740c00201940c2004640c0c43c0511000c2265a0160860388950905180340000c2002626040c01020a550b40c1e400da8000420480e015000320044c4540e0048654142090020151078130f40441034000d91240b1098941c10005c00c030183c1e0320a030400032580e00c9440d2144111200c09466018000d1445040c0c40070600c0c0302180e0105003141d00c00d0f04c880e24040911741c0508c004041d82e11030002d003200b0502a6919511040c4028518608840000100c000c0000001c41c11103009072415580b840c501c41d005010807c1c803192107000040f080b6814640e035800f503560709aa03803103030740102070401 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 803905728 1250 803904478 803904503
    0x9051513020702042c01110417030904050f06120a02060d0c170a06170c0a03060b0303071a04060c110a0210140f0a18181d010519110c0703 61
    0xa00c91541a07640c4264020030502c2214181401c01c80441d40040100d039404503442d0a500301c90005209480300c20368030340c09103400d081c0703403500307511040700540c056020a00040210403400c2d6aa40314003441740d07100386242111800d0200c240110b48240710003802459021200410144e910103043c0d8850301501600812410442c1c00201d130704090700b40403114456655000d210f5a400c02d03400003025610318601420007040c0c03094400d41e5641c5466107050708140d503100140007089143d00440207070307800a01121318112043e5115009120070b90240499491001d05100400c00b640c0903c1c1c080b40406d00d40700c090000102d40c070b5503e510a80000078800c841d015203d0130458050a10810000812a149515803840e0914000164402c8804400040c00300302054a81e003903d42d0083e041c0d0341644480f0072814490f2002c0e0300244603404482c0c0d08081c5e0202c40780c0d0080b50034021f0510500007401e2510008200d800c103941a900f60500010000078140440c1001000004150303046036000340d80300801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 803906978 1250 803905728 803905759
    0x130c0828020604050409060e0c0f01090b03100806070203090405160e0d02030f01090302150f07050409111306021b010915030515091e0a1109060703020c090a0603020901090515 77
    0x2900c036130f40c400e540150404d120301d4244082507112440414008040d10b0302c91040340704012801c1c65041d0201e0200d4090b03942844241070440103141e001d040b203404411081d032100002c0e8500034040301c2c041c00581c00020040190708060042c960403204003c5244001ca9505101402d50341138800440d0164a8411200342595400c0101245400652000b00190103690070000d441d0041044009110301700710010841280045800c1c40c403070304259039104c4c20f01e4180020400607105461050380f9110050000520700d10520010400418154004000e07940744005240500e4140703504041c14840d0040d001c1207481c01c01601c61982c810320b85000201039880200035504036400d0034119400000761030030000d200e044001000702e1503d10185020b8140d54081c1800305503603180100c032800607018008034a607424035501070203905202740190380c0120f1200c0d002c981c00c1c900440d086c1610b6501c2d02010029424107420f141e024082e001c906100c1403a0403100225614038501055014481c038024404130b = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 803908228 1250 803906978 803906989
    0x1c0203060d0809010e0402041d0c0412081b0304060804060f061401030209131104030506090105090c0906011704120f03020f03040f020d150f05070302070b061504080105130c082802 79
    0x1700d203070003030085468030345801c01d072000365002524130416100f0070b501045002030054103035400c443c0c4404034045c0d81211903540c0602900303c0300021141104803010b507010b915050000d030000c1c0c1001da03150801440c082c10305800f40e5180c01c5001d10028901181441b06030485200007030803002c00c0c2009650f490002c00071941140140c0180701c1114909100180314105030401481140d0007401240c40340c2d100c0803451400c840f810303528009994005e020382c001d0383c1010300c1c803540d01c900141412059441c0d0f0601000c00341c42c0454044035203284c400c00300507003a608001e10151124241c80e045080c03e00d1503025041c1c17840068805030503400e012640200f19070710209c610703002c20380c880240c0d4640414491200302511020a90307400f010301b4080010038562281c802d840080c2c0d0040035081030360300e696040c088000d505042d500c9007030004000114610809015003801845c0d6206011101e07481820111502d04868201d01500c1d000840708080b40b1030340d40d03401c800341c0000190007031126009100150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 803909478 1250 803908228 803908247
    0x9060b090f09090a020909072714220f080d090b01080a2607140105090d0e131d01021b0c0105030f070f171501120209012106090603081c0203060d080901 67
    0x5549c159820340304c4175204000c2d4600c8030300c0d003503005109426411701c2402d0900002c44445010b150f840075807826460282c99068141030051405041048050b00c4056155011034a8644a144c44200c200b042102541606004102c043c0140c05c844180d503075500d40e8189405a01c0d14440d1001c0c1d560340c0c88a1040c4101c99196600c50780903250300a0511140740030700000c44801d0010300500034000c11203405020f060f03001c1c00c1c004141420407014902028000c0410805828071984000c0154901d43d800344001d0215507203800032032208000c5c0004c813074606005008880d04001082c020b0100b00c80005455a8101915003040404010850400c0315022296a01d206c0004015403d11048111002030000320803001e82e5501d44410071004050142d02c10580010b0014a003d4480312641801d0003041c07025800a45000c520742e5a595501c1003599496081074030003400000310b002c4925009201030550030b200c20710035401c5140202c00162880900c6a019104110000303885156a108001c001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 803910728 1250 803909478 803909489
    0x10b0f01121b110607030b0109060c0512030109020702041d0c010c0503090a09052a03060105070c08030a08070810030b0606070204090c090605030709051b1309060b090f09090a02090907 81
    0x480510702c91401052080020004002c9020b51400b0610252090160504e00b10041c1c4505200518025084821041031602902c140c02500f080c25a5200b6140c004d5008051508001d600e40e480c41c0100000c990035400709202d2000d001092075499000072a004400f40308c01d0811800d641c540e03042282c110f1080102030781d400031000070b001c9140c0c0d000760700041c010402e0385450340b00d018540f511403407040c0f0312000111140d441400014041c0d0321520007401814412881110303842da56400142c0b958205500400104513040200848036920607034855101e0641d21034103050604c0c5032a040d19100e00640094028040040e110096450310b800000d02e040e40b1054062900d60345801d40d4008001d00d016480c401c4c00758030000a040e6203180101030196058000000c203001e0500c60b0b03054594091103016125404107000020807036642d20480000b031581810f181c0d41d4804e0003040080382030054040d988120082401d0280d4144005844020359a06880150700c54860b1a007591410500da07100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 803911978 1250 803910728 803910761
    0xc020a0c121a07050403032a1101030e0a060b0f0d0c06030b0d05100b01110a0b010509060d020d0510060923090c040e0a140303130318051005071202010b0f0112 70
    0x14061804d902c10b0040040368083e50b40c601c0450800300c141c0b060a09859801c80030751800039036007804603490030415881c1b02c0050400140541c1c250121030300348031413480d0a640055460051044c40c0c01c01d03040280301c840044400c5406100e0700d40d0340710075180c0c150141000f01070ba9207102c0c20681e203a6121184c0354903000320889501c0c24902d12107130b0241c0100d10b061030003c0c0c0c00c649601c2c040d030000115103c03003d50204c08811075030f080805112407108002c1c61164001503080c2d81c800580c455440c0552500d0082c4081c040080c40c0030003450943d102c0d07074003013a100d03880e184c07403141c244a400c0c0400c0300b9444c0b4484000100d4994000c00c0d8034004500c00700703640c0076141c0a00040003c0780010b4140c0154070031000d0444414041c4200344c0c0381e0204031500340c40094480e0349000003d02c50b50f8000c1070003216018240c1d2040d155004280c80801c00c060040110f000000c0700014000041c10f00c004001380c2d48000d021010100e00815540041c1c03030340544c10310140910f10304603c0c00c40e8002400d5101202e58 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 803913228 1250 803911978 803911981
    0x80f01052a0f0c030705150601050726040b0d0b0a0b0301060309030c140d0201050c04081c030227040b040504050c060c01021b0c100206010f0b2503120c020a0c121a 72
    0x1840c0c0b07130745c0600d030103c1b80c030f01c202d8010800030b11003005d01502c036400507110310303042100d1512004c4c0400f2001228440020a0f1101c8500c0381100c8070182c00a4018841415110f031941e0f40010b00705c40d1160104c034840d44458070204845138804d81203d042d0345113841c012905491074502a502034110380390013002c031140701c42c0410080c1c00000340309507c01103a9000740543c3c0c841003188005031103030b4000d070009a04403034a061076480f24111040c1c840c28040c82c005140c8400c1c0c0401280b075108030f9901d04061a415200d1607400d207480c1c010710803891000c540411080c14159540713642c40303e00c417120a01407640403034110f401e49003e42c1036642d189601c04017600c22216245070551a40c56410000d4807807503200c00e60b120040c1c80040c000d410b030760f50415880b11460500c122040c103500465007051200f2140d10144580c8556001540505442500c0383c000140c41c41c116070081d1078048164001b15804803003000c02084405040004640039201909828480c0d4200400803801101a03180d04020040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 803914478 1250 803913228 803913247
    0x4107060912110c0d1e170a090f0302030703080c150a06030b2401030506040b0604090203010e10031e020604120b010e0714090d060b0a03030c0209010f031a060a1707080f01052a0f 78
    0x4010164001140d980710403081c1c275031030540c010080c03a00006e50190b00c18035040c030005030309400402242e02d05004481c4001001d0038403150781e075402c0710403a19540d141e003410820480c100d903041c3d8010701c901b0050400e1402d070303244d40b00805400c00103407410103450340003103074154813154000900c0410240c00907956a841d01d10403006548203118550340c050302080003809520410b0843c81c2500d85c0303c1c60420044801d205200184002e492003640d12520401c40042c51408604c503190800344200c503110300035850300000c090b003050001c0524040c410303a4054600c40403420381c22110107902c111418402c11201d0b0606c0c0000385166018035400031844c4001205054000f64580c91040c42140c4100d01d0380c0c0c8401c04004460070301c9c400140700b00c45030404401d0068104c1e03501a4480400b0b800703080151782e269244103a0a00da543c41110303503000304005202c050340502c040310024004400074482814008420404e50524201038400340020254141101c06c0303580c21181e5142d81c0040f41e548500254 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 803915728 1250 803914478 803914523
    0x5070507120e1819230c0f04240e030d1107082a0f0114030a09020405070507050105090114060111030f18014107060912110c0d1e 57
    0xd13039041d009001da0001d81214412030707000e10692a8a185804507800c1d0048100b03c40184014003a184080801e201001a100c041e00240c0020702c11400e03030350b60202c3e143c501e00c8502c600890180c0c0420040114148141c2c5001900c0c1e003900d01c080c9400754400910340060307414051990400c40040c0202e000300107402e80002901c02d041c0c45107044491403044a842041202c03022006030501041d1165204590901c054010310344c494240e00c400b1031000150360005007150710032101706000c10380c08640141880402d01c26950301000d404000c00000090000500510034001c14040c10049100c0304c01000d040140240c401042c410002142c803229114851410303980481800ca002441d980b8400c448001142c0803181c0294010403d16400d40400c006200000c81298203e000341404100c070400143d290302c12011200d0245150100720030b2090b070010300a013000042c40a03580d002c80214000c2d681c032079041c1200964048034501c50f800a02c102454100c0b0b403440d0241040c0d20b07603910726a071410f41 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 803916978 1250 803915728 803915731
    0x607020409050a0311060f16030f140106140c25090911120d0815010e130e0606030a050d18080607031a04021608070305071712060405070507120e18 65
    0x90310b901e903800441c5c10005590b4101220060b259400c50340114403003400071120fa5183c80f48900d0003003040007018a0001c19600c600380c640c030002c0c50354401000310305c0d404401ca0010380042c1e03070024501440c0c1b284050fa0380401e0300f40c4825410740406417900e0f80b0f03e00f80e84600104080401030002d142181403803490710b0401503000707024038a41c1c000391000850102b0a0501c20b05d141c0c6865950391110a045040300031046d03001414460701da40703040116034442c00c0d4048012403641c0c012a510031404100c0d820000c0c050442400fa50000c254600011000703e11180c07541c00f40e01c0c000300ea0355050945420512201d0740959400c1c013a4600b8031402c0755054215455400300800035804065103a4144002c920680140c6440c010040300c0c0100040e600070024400f450184c0790860070000c1c2d6454007007161144140c10079080c1800644480b041104c64041da80c000002c0301e00b007010703140c02072000d81540b1030104c0c0100b0340d4001c402c2984c1c4590060200900115001d000b01a0118201c3c0c2c540d00810170 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 803918228 1250 803916978 803916983
    0xb1b060a0e010b0a05031908040f08010515030106030213020f04172506090b0309010b12150105040203070e0906010215090c030f0304150503100302060d1a0a230607020409050a 77
    0x919000030f9a50803d41c0708802119070180c001c050212600640019404130030900300c4105004010009880e0240e003e1031000e0404100000b50905100200391038601080c00340c14026410540100050398561608101d199005003026940d803003020002c40c00f0f440359401075261403211050786102c201c0b0002e90310020f1055812060162950340a0003642c0c00b103148a428005618141c0900a545600d8042c40c1c008003142d0000c00c0c900c07500c80c00925080703c06068844c683e4812204504100241c21100e0b0040030181c404610b54100204003c0c0b200b00180310311030058540030046000c99100700450f215440b00c131084a003450400034051a1101f200f903841a22901c16040000d0f5184c001100701c400304d407003e1641c0c04001c2c084030400e5542d500001c0941034a0390300000c0002c0581ca449000f0a180d192522000070546181212260340e040b0010380d241c041c046c007510501509000810440b19440500380101d030380d5030b203400042c0261041d41c40c0250000e00303111101d0704100001a8120080e032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 803919478 1250 803918228 803918231
    0x105010f030b10080d05071b030f2604060c0311070303030b040b040209060901030903020f030406050a1b110105031902040b07052401090c050d1a10050a090b1b060a0e01 74
    0x225030100308400050640280140c85d00428113102c0d885005400401605216001c84050007191100d138680300c3d010f070b600660301c001c031000d9030130f040240348041a052210300c55901200d0f4100600d070201d5134040d5008800520902021041c01d0602074a0243c5075000014200c8860310b4480c41c0003406130040c0303216107000c1c6060502001c10b0f80380c00c0c02602e480c1c0001034006414000048011406891030305d10903401c0d4001d040b0f41000340c3e44c003800180007400d425260b0030381e0b4403c03103400241600c542c518105d040d1030010307441600250b0400b4030240090000d1a01c551251a190716641000b0907481c80d6002552000900180c400c01c0d4070098801d03980240c09541490526010b4001e00240a03050300a480c0d4003a80180300070007032a800075034050351602c0c0803820008100044011104071421488240f51600c05201c00e41c0781a41e0443d1180c211880c0032401c14159181c0500000e8660107060400f00740401c00c4014603050101d040d016034000303c00c80d03186081200b607090081459400642055 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 803920728 1250 803919478 803919481
    0x12f0a0618050a0b040c262e05100b0403260702240d050406020d050106091a0c101104090f0207020d03030f0b030607030c02070806360105010f030b 65
    0x1055141d02484695400c0360160804802c640d03101c4c0d1a00200810884422800c0d0201003000c0c004a108a0b500c2d003581c0e02d0a0b6040030068002d82c0c41c11021030b4030720401d481980c1803094410540021303001410301c148008116a2030b010403901c8402c41a0b001170706460004980001030000780d41100422150026031001000042c4032090400c1c8564103020b90081d503d001d070324030700000280c0301040d400c01211015082c520403c5c11603099520994080d100b0300c1d00401e0310b4207485124400c0070300500460910700380ea28500b113103000790070b0301000321a10070040100d02c40d01d0980e014811880f001c844a0800c101305480e140000010390402d0264152103440c000e001c60705000c507842201c0420360014402c915046a82c5e07000c501505211414100c22504d60402048035141084405d000d80503070307240883c05103041c0034004d140215961261006a0080701407200400f601c0c1c0030006800c4006d0b19244020740183d601402e224803480410445610300310001607620118840d101c10341e0700c00e85509195 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 803921978 1250 803920728 803920751
    0xf210207050420270d140f0a03022a0604031b06030b0607020603070c0b04060b0f0405190b030a080c010614060a0207060f0e03030301030803011706090c012f0a06 71
    0xd0180f0205401d400c10040110032120500440c00d03081ca1100d40c114902e05a56100100d4688003500b10203c8070180162a1260144018013018000c10360b194000c4c1031a415075203000755600e20710102e02d4041d640545400c0301013903034800101c00000000c0d01c070b242d4440d84ca1405e1010a9816083c2e40751070f01d2061008152988280100103417048018101410f004a5400300400c59202410100601c08210031100005403440e451a103d00c1c06240001400302190b418002c2c15800e100710790b0322071fa2030a410044850747c1000221034041400702e00251000310080820324200d103801d0044c1410700b0101e500301c0e2100c0c1c1504810251152060070100c0051a01c0920a441c007401c0000e002582000806010452003494803081000052400128085c01480403c1c00d40c0d00a800a0305c91107030000040c41208002c0c0840b00200070444001c10303440c504003803800e0f2221407a011360390401218900056020100c0500140c0303000b40400140c1d400b44007880c901c1e51303401081c8400c6520034149400041d4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 803923228 1250 803921978 803922011
    0xb0303270d050d05030709050907030c02010c0215040b2211010207050f0904062004061706010c08190e04020a0c03141e030c122d0c070f2102070504 65
    0x101c0a600600400b5180440d070420380b0f0507003004025604104050390009030998980c14074500854050306c0c0082c04d1200c0c460003d0039201a4030081082d0f52010586103142c009800005511903003040401d8115140d209001c51301c43c3c0700d0f80000380d10310f03000d030030260511202766580c0b841c10b00260200c4840700d40d20418044a1140900100d0b44004050009000300f51a0340080300041c01c40c3c1d076203c1c1a2400c1d07021442007600690011030004085024060400c181c001003070390044002d09040d1041117450382c03094040c0c801c8094840c54041920101d1405c680207003a06810681c0062056444e503209110042a070061070b0030550014282c064081c01d0541d504084485000901000c110b506540b40000d5001e50310180083c4641601048460b130300b4005101c841e409009100f4850b00310b030043c8014400110800140a05045644410300c513410402000311049240e100d1121300c50780810b130902c040c1411104800031414008040d03460081030340860784505440c0b04460410581b404c0400904 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 803924478 1250 803923228 803923249
    0x50714011d06070c170c0115180510120210030609050a05060414060102061609050303040806060310020a080403030c0e0414010923011a0409020a080a180201080f09010b030327 77
    0x9002d401d003070001414030204c03040140741e040c06c034400110781030072200d43d200e030300d5115913101d00600b80e01488804c03180f00c40c50007901d800c110a200a4141d031814a26030942d03034a2078140080c03040a10841c0080087d0203900420b00030041580108224030782140d00101a200c01c6441a211310720700880529041d4114a0640c004c1d0010b9004141d5640d0b0329030b60b1024501d450903403205000d500003000456543c01c0000780081c0c8040006001c40d400c0090506d0700d04000b20054040150043c402600102d902c1915142c0c8603400d45800314511650010079640707607400d518001e03002410000c014109600e1085058103c91800c0d20400140d03d02010100107070002c44507001d00400003d00401814804407008141e407800003c0181c5130075628004e00d022a40501c9505000c1903040c410040c080c0828032940350000c41107049000540d1896000034940c000041c00301021840107000700706036400c250b0001c1401d00c8041d0407a03030750350548030104994030140e00e41d0000d0300390496652440360608600b4903 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 803925728 1250 803924478 803924483
    0x503030a09050f0a03050a05030c070e090d050f09030109030306030506060d0c1a090607050109030f110c190807030b04020a05030705010c0305030a270204060603060f0501050714011d06070c 83
    0x10781c0d0207420541003218503002d40901561150ba10600840402c00600001c04044d104000171035075200c5443c08542005c410b60b00011406254604110001c1c3e07010405503000c0225141261307540c400c1e140d00c10054003501140c0c94056107020305101c2010341544c00042500d0091040340d050340d41c1c3c0c404101d200f8141c00402080002c100347c2c10800140c11031400000f2000b4111803606000c4100301088a0750032060065606039100c0d50f14009045d04070b94082c0c028072941c44c0038800e14481e580c040f9a50a22aa20300b40a20311400d02c10400702c152500c1c01e0040c00c040c900369803040c3e559051020b00220103980c00d07441003880610010703107403a00040c2c2408507441038680c1c0744104a0360b141075409410081043d107006480c1c4a038240100740d1402001a480c41d1416003850f00805401840300326051500510306041c83c0210601564420003598070071203c092070b0003580d0320b00f185410011103180703442c0c0b00e0701d075803c06d140040c2c0c407500d1000d0b0b0007032141100100c45135680c2d06d8800301d0302c1c5180200007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 803926978 1250 803925728 803925737
    0xf030a05090f0a03020402072105180111070801020c16050609030d08150a0f0611010e06180109051603120e06070b04060e0708031908010311040c1205010803070c0503030a 75
    0x2111020b04140c01c65400c400c00061045000076980e401050503a031045e40f080710204024480010440c0701d00031402c0580c00d051a0090400a40455843c480e4020888140c1804400d0164480d01102040300d07101a120781c200a40d1100422064103541c0c10400b142d400310303022801000305050034080150781e10900001c1c010224440e020340191481c2d240a420101c1166240b00310f4861030300e96051502c010510107000e0440f65203400700c02050b48040d0401200c090341400143ca161100000d40a500302484070b42401c0800c980003401030041114000080c41402842d41c8420040e40a42a007001c49000d02c0703213121255a09582255089044400c1950240e028826680416000d4408541c418400c3d04009818000341081c039240003c0c031741c085440d69100086541d854000c810319403031042c8035410800140e50441d40c4450602e00b0203098103000300d580300340702c41d9454400d4408003607140291104000e1075840b8401191240e000038415241141e8100c800280340c10000100c5d501020705a46 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 803928228 1250 803926978 803926987
    0x20f07061a0a3c0812031902120c09010c05010504060e0c0306010b161716150903120203130b0712050708070804020d11040f02030a05090c01020d050903150a05090f030a05 75
    0xc03407440040c0c100c003070001400c00a80200318040100485248109616201070b16484d00300b07801031000d00388543c0c0702d0007e070042c44250703501d0390b00c584081e42050320080d02c9a1211b856500484003001c117800c1c0078140d03600300b5003408207009040e0300c142200401c0c2004e0b00c0010b04038005041c0c1e509400c0c45480b519803c01c000902e00443d0100950f260320740315080c407d0900046110003011604040c1d81e4030715804072101d5400030030490754001c81000c03800410a0051071002d44011300b5a10000d401c4a0a881d000400076030301c601303000004a0703050341c090512551410a203500400300c440109010b800b082c136041c0410440750103114118072071116030369040229904da90030b10100c10441c01c03007254007481c4415800c0c403a61b100d0051080d064484a00180c403450000d11180a44001078203d800b20b0b00040d902c0090359a012640c1c011618450600070365440d6007802081c500010305094520080d810818072106d00301a0300414007440c01002220b400740080070b09240c80c0d00c02c210f03c42c80820310070132 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 803929478 1250 803928228 803928299
    0x1e020415021609050c09040504050c240a080a11271c140a0b090309040f0e0601030f050a020904030309050c0a050105040501030c020f01330f0504020f07061a0a 70
    0x1040ba9600801418500d811b08a49101090558105031000c840c5904421700c5080d007424102d90201c0c10003c442d51081c01d041e03614440d40640d01c03c0c6a6440108068540000da0317a038000e402c1002851020f50f4116075400f02c1aa440c02d04107070940d050340062a078045044100d10789070b000440a0030070b400e28039076400340c00d40d2074800c41d4103480c40005081c00303042c40107804107444200c400c3c8902002d401565442c0c0c0c0001c2000121200e08203a040d0f414601000566129000103006064a43c4061041c2840c0d41d10300b03260f4684215044000d6121600f07400f0401090f9058114090440c400c0c4111141c20511000b005017150b018015580004c606010801280d03110340c102196410650046c0c800e0760402114860075100803921982c8840c070144140d4680d0b02c0805001284540349500040300750b0b01745007031196620a0b902ca900d202e1a0040b035200c500800b15401c03201c0d443d80c0300e4000c004610f54104150020003144510f24424a543c031000911441d4010121035001c04407204d5280041841 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 803930728 1250 803929478 803929481
    0x50c0d020c0c0901080d0f050705030921061003060605030606030a0303180c030c0503121620271303143f01061d0f041e020415021609 59
    0x2070000c01910701c40d0141c0c481494a4040f6018040d00c3c001001d0922040c81481c09000d8400681c1d400d0200401040f804003c1381021090301c00c801c40444e8080c043d140003880303812a05460729003070301c20b500590b010300c144507113000302c40800c0300c0c07055500b807090a0fa120f04064890200711016505074101581d84000607210b075001c3e0038101480d001ca852160a181c407000345005442c1c10894943c800c10405004a00d0b0400030700200f20044d6100714a01080540c0c000300001c22100002c7c200201d0a20700c00b0101c1480c492000f00030f402074162039040c40e50403614105501d0325403a03005103820300804542c000b401c1d8420510795642540f0b64a0301184039850440c415171242d01c03106100851544800c548204041004003858400c90b50314104555010503c03075040e1701070703024009028480c030b800f400d06541e040344501c01290448441160301000700100b03000d4041010700c030380000d01c248100c0101c601c01f46c0c00b80c42a542884032400d0803a5010030300f80c0c2d40b903200a0900030950002c440802205125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 803931978 1250 803930728 803930737
    0x180f021207030b01080c0a0f1403011d0309100203031b0d060e090a14010b0f100908030d06080f0a0c0e1003060c05090102010515090c0a030b12010b13050c0d02 70
    0x1822006005015201850810009802c1150525044001000307902d40800c20610315103801c6911030302e01d500c1c0c10390020514545220354081e0000c2c0c00e1603102c050f5401e500c040c41510301d01d4142d1242c456040708503a183e0b40100e81442c8904206c141a5418510000540b8072500e42010386d04404d00c030580d401c88642c1c210440d94601262504004514214003400440c0600400c00c01480605010f24005801070b80b140075030b80c0c1d01e1b854601c0e400c015950702002c1c6180d00909a610205a0b050440101d41001484e0040c54140c84005040b084041155104200301d584400a588017840804000c90b110340c1e85a101400742d2408040c2032100521400c1c0079a045030454000400013503999842a007999555400c0340081100451007088a58080c003030380b07600c20b861211000030b030341d9550001280400064414800400041400e4480038040d9100404000000745043d10b4000320f2941135018119603d01d0340d018800c0ca03c103481004e511805101c1c01000050f40c0c0504004440c060403009401 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 803933228 1250 803931978 803931983
    0x60f040302030f0f040510080709080a020102070605090102011b050904060b03191d161404051608060d050a08071202030a05071e080c0c10050703200a05150601080109180f 75
    0x134104800140b541d100c0b1000002001d81d030303c031203460f8585804083c042e00c040c0d0341700c100990450200d240c0145e0740454040141c03005401e00c9902c2d2a51080101c2c01800c06400e8030440510301400d40041d590480c01805e00c0707c0049406114441e102c0145130014081660348000c20844a1880b001001751600212440100809d078040050b420755041807500c001007840182c045411a020300190400c060301c038844001c152030610440c28107180d590505220410050b0800c41021301242c1aa130b0b0f000454540b058108086402d04d900f00d080100c225070000c481281c0091119003241c10290000c000e80d40a50000d49840741042e00b44d40300c01c5031200e003100ca401c6441010ba1403800009414102816000200100a042c41e48406051086080c0751141c0042480010b106180000703610035421050319000c0007813010082e103010b100c03c0ca0240218030090803405850300051081041024a40c4245001d984821807a40e0ba040e146045400e00c081c441c2c001d84400134032201140075a190310b0203451 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 803934478 1250 803933228 803933257
    0x908010b030c0d5102030906041401061d090d020609030d0903030b13020705010507021207170f210106230306010e031902090105190303110a02060703090602060f040302030f 76
    0x600d50214004d40a1407510412060364082900c04094840d80c0003012126904800c11451802c29100b910790341d060081c80100b55030103002000e08498402e42041780109858584821843c022110314403030854100c0d080f110921070405860031040c40010483e004c0c1501c2009545041c1e802050038000d050040c0d4250141034481c030b50500251146d401180d135900e52044010f884140e24135005096480c05445002194001e6600c0c102e045100170484001a91148840818500440f80980f00380940d542200070407a000c41c415000076407174201000b42e40300b40b24822000360f07252a4155082d0071900c052235000c0c7c2c10911094504509075000f1600700714141840002c8844040c0000e2606408901a0444040c032103a15011424604d10f41809404204c1b900f00e14540801d0a03201010720b544005010400d941c50074101070101403120140403500580306070754481c13a44c1000351244080340300d24070061003900000f41260040d001c0b054007942e030513070103945047c64401c5040c20320341201c550001001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 803935728 1250 803934478 803934533
    0xa140f0f0f13291003050c040605070201260f1b071524080f0a020609011b060f050717040b0a05180307110319122604030908010b030c0d 60
    0x10000c030000240c0512081080780d0f4901041801e01800c5503c4503c50800c2c14241000c0c40501c02c28a420381c0c040d20000e18000e912101e19000488844882c40b4104400b4030a10701c610394083d5044240a00c15161211200c3c0540c40f140000b85284802241c0284442002e0125100003030b02ca05000c1ca0004600201082000d030700c4404c103c00700d82110000020980fa20030070401c89400380164201552100054007079000300c0e0700402c18521911800a04000c00402d082c0805440300080031006500101c4c10400301024001e544010711040c2c4211300854840c4402c4041080381c08001c40c403c40d4800c1001c502a250801c201c07001c0c01c0c01030420180404c2035902c000840b00200085c02c0140c0c0a0222940e110680c441454103158203008240400d208114202000c5840c039040440f07480c80e00c0c5405181480700f0040000140b00c81e021114141b4560001d0005166001200c0300988084000802c11446100201a41c441181146603003000d070760140c1c1c402007100e20b60303140701c50003003200305d419070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 803936978 1250 803935728 803935751
    0x60b060a030902030c0a06090b031b0d02090a0b21060301020c1b120705061207090f06051908190b0612040b01080c0a0f0905060f0a140f0f0f13 63
    0x1541000c204000020307603603039100095103410071625965074004e0354440c52890524200524003aa14021400a80e400001096135841400501004030001d0000c2540b52204121440041d40c017401c00984074104085000c500303090498202c400074695102207150a02402801215103000100344a030315560a000013200c11109104452510221401140c540d4480d10104500400345510124a90348150070500054941c00211410850350001c03581c4940d03140c0c8002c0f140050030340c03c140b500301c8030036070002801500400500201003200485103064843e0b5a0201d444100840300b049103502c95044c00034854040d503100014200e0041e000e1880e04660411401c00d501050350125106220200100700c211028400c20700c802c1c100300e070f00c24899880e19815400d078803480d0088c0f40e001da5031900410140d42d0707012240510380f04068003400d503160f40d4034545110b0086038a14180543c0085000c904585401500d0205002d00181040140c505c50020300614120070711040444a0344c0301c0305c4000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 803938228 1250 803936978 803936989
    0xd0e01061518090504020627060d0207110102010b0f0d02010905040212071707051e09030a0302030315040e030a0318140106140102060708181510080c060711040207060b 74
    0xd51a040d120b540900e0364000c1ca69414101a0303010840d06880d20091000503511325007214040c031460700030010116a09000c03005504200c2002e140e001d540003070b4009001d1a0f9801410219008000161444040303a005a09031040501000da1202c2950b00c0c0c1d1380c81e8034003007819104031801071600c00c810507292004241241d00c840c44030000d99070000c04000711580c1c41a416405141d400074030311450304042d6009411030044440c0f46980c1d44044d0480307102c807603900c001d40b9020007000341180d99907406802c01075283e500c20fa07503011004101d041441181d080a02076440460340090046141501c4044220010803140f40740700c049000d00f800301008590340c03010a40b066901c3c0000007601a03c0c00c891144002e1400070028150340065007004103164120303a42da50301005a20505070404240a1440e083c050743d180700c0c0000c1c0d80340000b40704880110120000c241d481740c030308031018181800c04000c0d0500072160f0043c002c0180c4243c4040d24101030300039012a40c403c11003c2003014480c0000342 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 803939478 1250 803938228 803938259
    0x60d1b050a081501060203072103110d09030206070e030601090b1c03080a052202012001020c0c1003020301030c061d090103120e041a2101050903040306060605030105060d0e0106 78
    0x740b1980325410791040200044103aa0042c002c6000442c502090340e60b0311807200c401d80312180f400384400c01507501d00c40d00a41082a40080c00c0c0f5085640e01c90000103100103054401d8150010700c120400554124020840d01142d030740014001c00c4c00d607207406400c1c1c3c040c01914403d0368002e40395240300d4a5184041c481d9a210920945600d441ca18000c2c0c1014216680141b4074190b03140c0c255032080044030581c2a203941107130203290504486030400c00c08000c1c4110f503506102250300c00079400d07040f10400701320781510071811103403032346035020b0514100e0603800f0070300014004c003050040401c0050f0003042c050640710514101c124001c21440300181500400345d0040d220038182d80d0518105c10f622030030003034424408903000c004119001e02224a0f00c40c1c5928004d01410440303c00a65040440c22041c1c2c80d25800c0c0024084c6207000d11103541c0b02c2d0850312003101ca59003011401314459001d03406a9059500160400707060050b5951800050405400301d80c05a5503607840200e0b151180c103650b00c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 803940728 1250 803939478 803939489
    0x20a0506070506041109040c05010305130c170105060306220c082b0207080601180e07090212090109030c0b270d0215090c210a050c04050f060d1b050a 66
    0xb421913107011308000c60242d0300380000078450b011460400000440e11750350503065950a1a0004144d5070303402d400041d03480101005400d100c0034400000702e00c1a00c1d0801044949503500a101c5600c0d04018540d0f114020360b21881c0031b610402140f961102030200c20020725008481002c0e076281d503104007a00301035105101b00f10301c103008402034054a411103810645c1803090320041c2042031400d1490340e11100e040c02a400882985484540d80300300503040361481184c01700a55194980d41e5903020000c2d441455140c0c4034018003000507880141c18071414107219010b8030766014245944c3d44460012200802500e213458061603810844e56141400d0881071000c3e60040c010000b0303107000a8074011400e04070301d80030410001040350501001c00d10402c0300400340e9465283c100003100008207042c2c0b01d000b0940c01e10400c0c07110300038030030000361403a83c0113001c0e41c0c2000340e80c0b07800c050f046806e20201c5603207030070201c400000800501089000120703200344561105070305449100207119004640d028 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 803941978 1250 803940728 803940733
    0xe01031712090304060306060f0221040914010914010b07020609010c0f0b152e0201021b060a0b06040803120907091805070803031006030207020103090b040f0512041a07020a05060705 80
    0x61101d5070701b40c80317060b0280c2401c0c1854000790328004c038000c4d6a0389030800d00c05500380c3d0985030010364521040555020b0003c24606226082c00f0000c41208a0b400344500890241003050320401c0307101e410b078694140c82004040a207405015001e21481e40d02442c0b007581000f05180e1820041104101d0070f100740c5200d45e0b0034110b103041c03440c002883d2000380c90880740310b20b4211411105801c04040b2080e200038203001c0d0b001000300100c4050340240180c10044600c42124074506006620108019100e51b003020010880c500ba039070b040c8826801140142042c0b0f520802c00920403202c0072041650182e040d03004c03608090b4441c00c0b030006a4920f40c216110288a581d901c0080250502c0004083c0094078021821032070f21110350b02707805445d48078820525900081c660150b900c41d030402c0b0070b02074101d00500440d04041c03400b40d40110b12080c095500b40511021122240f9134041114100e8010011070740d4a018021100e0309983c1c4a076108030b80c002c000702000940c64440401078520300c0c0c0940301 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 803943228 1250 803941978 803941987
    0x17091005180c0111030a08090316051609020415080a0f11250f0b091005070509031903021b0d15021b010902090412201b04060e010317120903 62
    0x141989040b09259910341881044408400030001c00015a588075059143c4a0b0203a150541218158421188040c0e003400c0c28502c40018403030700045140500c0a0142c820301f4642da1089000100c0c01980a6040c20510510f464483e00307100f511001c6d08828070010002e10348003000030309811140d200f00074410310030340481c0300c2007500070346011001d0091515000000016081e40c8011001075002c60091001e03c01c4000f040500344100280c0f200440c1c652030801ca02d007800030010b44260040c60401d40b181c400c90090407a07103008035401d1a803040e03054008240c040c4140d00c0310030001c0c103080d0071250030114850f41100801c038031610320800e51400010041c1c1d207900c0c013460380c40c4169078100b00b560681c4c103050240300140c44a444c1d09a0040d08803030b0858108000300c100b1a1404104454034101045440300c141400c0b202041c1d60303d2410040c0c6000c07014811010922081d504c2501c140c15003599800c0042000ca071440200781d030910604d004080c50105001c014526100054403500016070010a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 803944478 1250 803943228 803943271
    0x20a03020c1f0f0e060f0405031b011b0c150c0c17030421143604061710021815030901050a02090f010309031e0c0c0f0617091005 57
    0x200300003e15405a0041c4409541040f2480d41e42c400030380141800041c0f034002900b8400d040c001e891007454200d02d061185002e0300369550190486070811010000c0302484d4071100d034090082005000d601c2501c6070170102406034440002e0a50504503014040800c000e840014924079400301c0540c0c0c42601c0c1d5441c2c1c24182440b8a03440071051007501444181c016961980ba001510020050b45448000c1d59582c82e410007032081c007001c91020039200025001d00106080c0d4080b410f0341014003920200200b43e591070f030702040c201c01084040707420f4101d82443c249507401b03038004001c2170460503d01c202441c0c160b008204000159408454803510201c00e02510090038021107070000300761002541003c14980c00034582e0404004030b0341c1403560f5000c03500c0800d0b002d03206031800c140048a0803400c4040d00c80018002d00b00b103920171503201c5a885004100142e480c001c60742030380d0246da0307006001207420031031900c01000940301960501c1034010061105a81d4000e06102c1d080e241c1c81c905103000d0b0364 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 803945728 1250 803944478 803944481
    0x180f03081b0a17030a1503050a17090a0506030a0212070c030e10050904150e0c0a0e0a06020705150c01060b07050c011d040c0c05010203040c061b02060409020a03020c1f 74
    0xc400451680c0214010360046618540f031000e10300e0f903030200e00d0740d65159451103500800e920305035042d102a07000000400d0020125418411034007400301e983e0344103040c40040b40e081c03181484040d408407042c4028000c50030410061030780720000c0f010040c47d02e410b100e1f6a41100601301c9144000580c0c0070054002c01da0300406860b0103030416102e00b000304001d000054460701071011010300440e551403902032a0b45000c1451001070003c2026888a41000c0c2c0c10b812195001180c0c900200321411070100c100c1c00c102c5075140c2241c0413a80a041c030302c0d00300300030046d03002c500002d00410300d203080c0401e421039030003846140003c113030805d025a0f89915524000b403c1000102a6505022841a052070410f20709407001040e09021107002809080c021400d03122102140f00103041d0758804002c200c03c114140f0b51040070b0320002e0700d130b80b0359024030a65502c0d060f4902ca203000750050170500c402c001e0108540c001d002d00c1d802500340035042041200d10103140070340b148001c41d501c94031107c002c0c070748203201d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 803946978 1250 803945728 803945767
    0x170c0d0b040314040609151b06050612060f070809100c0906091e14040f0207200a060c0f0c170105160302090a1a1209010c1209030c0201180f0308 64
    0x4405002c4c0c20030380b40c2440134100300c16a03c1800040c500383c8401d15030301c910900307043c008121014411920030b43c407401c000005150440e60507018010945680041c10301c0001d032170748190b801401c04032040e42ca00b070086912800260004c20709104600d00741041f04143c0c0141d100d4440550b0307c04c894140352620082c403003c5241d0041c01a528a1405007403600c0300b002005c400c2d00c0070f1100b4428040341c02d80201e0010324001101a0401740302042c540d042000352220b000c092089151030001803269001004042b840a114180100b0024025400090000d80e42c03081100d000d1400c0c112015581e88004080c201803034003c0700d542e59a0380c2000715950112b000914030b000b2500e030031030800360a440487d88071451401801003114410024059105400040b22100c0c4a900d04481560903c6003005028004e1a02d10601103900803002103840003440c4240c0b11030642560b149080340803c2c5d0010341d41032043c80903007450049001300c00304463f03502182000056104104403540c45042e45107000303802c0340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 803948228 1250 803946978 803947007
    0x102030703050f22050304150e0f040c0912230c010215060d0f0510060609150513030b04030e0402030c04080105010e0f04080c0a0c03060209010e0d0c170c0d0b0403 72
    0x1d0100130f01003214020b043c480b0043c0d0768044903040445150501070f01d0350080d940a01c1d048072602c0f81100c1d001e50701118404802d44c003030b14401d80d801102c8042106840041c0c00003000034441160410400091b0003540188602808000f450140001c8003d2119100c50302c40200c160700002c0525415603041001d1f00710382c0c516400500e11804c0c0600041c541000d07044000c0e0000303109003000d9060110030301c007040c00d000040100300701950740d030100074000e03800611502c8046052000c0503807003103010700200d035401500054941e0005085568103000c125010f072081d0b00700038216003000c40c01c1d1902d20041d40580e039903000385500e46103080103203401d42e001608001001c052034420701070300b003449080c50b94016030b00082e00d80d02c030300d03204504510700f064890016040743e48000c030000c24000d50303030f00030502d0400c03e0340c80c0300710b024822040c04900c00d1183c80c024488040142c0130841d803101070060060740c1c0464030541d490102c18400040d14034111120988100d0320b00001e00003019005400c1c1c0c000e030030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 803949478 1250 803948228 803948251
    0x30303021b0a020a060e0102070f0303110d050c03071712071e091a03040f051501031202011b050306010c0204020304050c0913030c02040b01112b02070e0114040905030a02010203070305 81
    0x805a43c08a01d50801c0f0744100030511031800142941c44e8020300011010700b80c00c01019500c55035038100107002d10aa4044010b040c025121400c2841c2e203c1c208543c24039011138000c602d4204e0566030148004c40c82c1000c2d0200365814450b400d130b0047d001c0360243c001c00d0380f035441003418642940404000d941c2c5020100621990300e401b0400a10704002c07000180c01800881901c03075403581005041c170081d0f044000c146004107040a003a0030713407410216058030f01907203515098620420040c0e080b19129290380e14070103c10a0084a040d07c1034009542c04401854645407840c0d0b241d0100b0180d030010b40d001c40d880d42014660800034140b0301c4881c4d9010000001d906122142174074041c0042e8070411000c4c2c000ca80303484405000e40d020304c41000410004804441c0d5030044200c4c01d19050044907805980c009401800d90750f040c0c400070b034010a0314808850380f02c65034a44040400300c5040442155001505c2d610036101040051001d02900d06e200d0700050b0b920b00d8803003030003021140c00406050901 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 803950728 1250 803949478 803949493
    0x20f0109021806030f070b07050d0f05031b0919150c0804090e120f0a0206060109180509010e031603080a0515090912030709082109060313020a030303021b 68
    0x6a5420b2030030b600c03038000075081e4040390f268600032038100481956000e50500c2001c8000405c89007001c0200001800398050720111414124120b900c01046101100042c0050000c60360007000c01005054080e2500c03071083c44c200c50040420301074554042c000728004082c4c101001000002054501c201308c903403600b543c1800840c1d80d2040180250700600c02c40a03a030b0781c02014030705010002850802d13040c0c1c00003030300c0b2562482c090490342d1240c0000801030107400041215940a145010166a15886141a80100c59070b4a1000b4840145902102d40d01c69015144114041c0020600c5040c42c503c000c019009034100a000004003402d404c620034a00401c02105511642151490a2044903800300d5521030109651070585122000090300000000b84007074150020392440403500341406941712040b041030842014003c10a0030a4480d0003000600c0c0640352402c0216400081c500710014001c4441d00411000c41141d001103021944c00514810750480c0d0030601140b10920301d0040024 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 803951978 1250 803950728 803950733
    0x60f11070f2c011505041a0403060b0301060b0a030b0a05061b0d0e030331140a08030f0714100203010f18020913050a0e060408070308060d030c1101050721020f0109 72
    0x2c00c00522560384020b910004207844280308004a0b0300402c880005200c0300c945211940d02e55034464882140d5541c60207a41190301c0c281030007030303104541c200c14102c2d040205460043d00603081440000b40d00c850354031800b050581d0785074040c044842c03080300e61500c001d14006c68286000782c1d9850f050305010213100703554a03580c2e00004551540d9030044010080310805140000c2c0d0460078403102142c411801e0004c45d00b4000550005d6030110101d85c480c03502940c0303240d110307124850307140300f1a07450000304144408151010744c103404080ca00800c448062880a0300748049820a8000010080040e0ba0402442c0700002d00002d04000c0205c0440c50a405c0b6000a07650600895080302d419440e1000140c003825190301c4481c0b074820403030503211145440d00d001c002c01d6000030030441c04206118046074540c10300c80341e10350095625455031745e2138180a440c1c104580c544008500d0400c80e08111143c00a0104004040103006100b07512288012036000641801d8203011030003902d81c90031070783d80b01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 803953228 1250 803951978 803952059
    0x5040b1e0103060f0b04230106090b0301140a0803271002032b090c080d090b040e0c071e05070503062206090206040e070311070c060f11070f 62
    0x1101d6006000150407904100510302a000c04220561b00a250103000e00012442c1090701c41440e0010568200680e00e40f01c043d1130420b5103003d40080c5200500040c00316102d00b841c240d0605800420b4032a0380782c0d540c4a494550790100055004800c0e8048140312440a404082c0c030320343e042144e440da11001007817002580c90081841107050300b10242d4801e9050122000001e410005040050000900c607082c00052003943d4811480d0f54804d0400c205c1000388904401400e544c84c5c000f4880c6441d141070912018020046c1c10001280c0042200000041c8a030760000458200540014580521801e00c0c600f003408950080e802608954100109281d00d0500c50032440d00c4140d480c80103607038500f0f25400501b0101c0303000750040000640031607088201d01689202d0000d6640901440c04001080c507200d00030403c0c020702d6207030300303040c184034030390280013443c0c42558a840c006103c21840440c4a01e842001e9001c4412000c4100041c019012030402212501c00381811441007607a18230702e030b0700 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 803954478 1250 803953228 803953231
    0x71118071d090106050a12050c1b0313090608010f11090d0807050d030506120106180b13050f0601111b060a1806031d010b13020f07021305040b1e 64
    0x8120500384040649469045040703003000001d42542560340e15000d000e000f640c070040078600440c3c00c8440e43d0b442c0811900400d032081887c80801d604002e1119126403071001204021300d5240418422102014250084000103144419020a2003807905c0f00c19800c54602084403454141018005180d814241c0d00325078801ca0256180c5207201903d00b00440305010b1020002e01c00d005a000050f122a403680101c5c0c01810115400d90410014511180c202c44c610b124424042050756092540c0e40c034294020841002c01400c2c81600c00e145079141c9040740c0b03044072031003070a07400036052000d40e5900642c42c5013a541d0100003045c0403104031002c10008103195032442c1c0300e04000603c0b021403d1142840c942000700e01c0d08200131050700c0e140c000d0080e0000410a0700400304091204481c0601406013018026018000d041040540c03400398029502c00300c200622118100021401a1030350415820a400e071510001068101850044000742028105c4400794107080c441040740042c803000603 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 803955728 1250 803954478 803954491
    0x80618011502070b0d06030501110a0206072109030201092d1203140114030d050f120924180303070813050c0a030f0213051005012d05071118 62
    0x2045610071001d01285041142c0d08001c80c11100844c10b141011102d0304503100382e80c4584028090a0a0a10300c2c038401d010700d06000d001030f0f02c110042180c0c01e000352013510720f440f40d0025058920650203542001d6071074450381103005030340d02c0030f00c0000d1110032044801c900310309884440007150301522460b40c00030341c900060880354210000507880340c020303030008500200111680c0341e60760b5038405101d0305212400c4417034080d0003050703084a0352520610880390441500d0207447c1c18440c000140440f50750000304844450304c0f0380c15403001081ca9440c0c0080600002000c0b1020510340a4018ac54986a5900c0b0000f10b50040c41403214540e0005889079000c0300c050004030060406040c014034190510382e00303d070040c6203c1000300c00d1004d043c0320200524001c1c0c0e100000300415290500460b841210000c000082902040c02190701c181c1c85008465000c80105020504080011110402840059020640000b805020815044041c0141807804c403106242d0b0b040407a5800c215010040c002c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 803956834 1106 803955728 803955749
    0x5270304080c15070605090f03030c13120f0803100b040605030a0b010810050f1f05130f050a05060706020c0a080a090905061003051b030a090308061801 67
    0x12040000025540600e80440c40d00c0317031001004080c2107512a40119041c4e1020720700c040016600560389103411b286d81e6070300100b002c1024003030f43e80000050081c14100c940071500320b004503000c00750041c6419540f55a025190015030b50315410081d903406007c680462003541c4000514819084c0b0705007004420340000040d1550441102c20f03c211585500f0300b40502d0510080d10f0300080c80c041c10600f4003c0c1445035101aa0845064040005402041c010b10310a203d0600c003000380300d1440031a202c42d042c0701c08980403000d18054203000d11000140c0b6410066568100ca0301c10720f0b0341c026140480308515084003940d000960520000703150400119070b403071152084500035140200b0f0410700700318464017500a824000e01c0150517850b04007034041001610001944940e00303615000aa1858919020b45900005003080e406960084c8865101814202c4041d0559446404 = true := by decide +kernel

theorem cover : BRFrame.Cov 803776978 803956834 := by
  have h0 := BRFrame.cov_init 803776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 803776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 803776978 ≤ n) (h2 : n < 803956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
