-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3840
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:49:49.562635+00:00
-- url     : https://prove2.me/submissions/ad494f7e-d038-436f-a028-ba544ca644d4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 690467625 ≤ n < 690647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 690468875 1250 690467625 690467669
    0xc120c070911030103080327010e030901080f0603070512030d020d1a0f03060c0c0a050a03020a051c1b0602091503060a0e040c0501270806010f15080411040b0a 70
    0x261802400d0364603002e400c56143d911001a01d100082410b0301d200450b40c2e4200b01001c591240841c103400380700081240350300c0a4030043c5e0b0380d0f102405450105500c14002951142c200c0c130b020f881a480034001c1d107081407400b803c0c460103003100000b0701045d00051240943e0b065051020344040b100c44900403401d4124407207107411180340c0b013540c1c9014101d94004461580c9001444e20740061404612665948205405074207080c2903500050050007000c0380d0405041e03002039940b10141c010b0041d900015042d05046212100c1d200000b0082400380b142110806504070400002c035008060252400b4000e10010300c0c0041d00403402802c0c0140807050020314241035030820040c1100313072541581c600307064460700000d100303a20070b2904200e802c42030410a03c51007103046c1e100c1c0d900980c00000300c03078407814910f07101c07042402005419144c3c903400217042502140c402080c240c0988441c0c0d100c1d102c40d111400c1c2140d01044441d0050307121440442181c4404d0308100040c05000d0f0702500c5c01403030304130b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 690470125 1250 690468875 690468881
    0x15020c040c110c0105210c0c2803120e01020a02010e06060303040b031b040b1303170307080f1005060a020f070e160c0f0821160e01050c120c0709 64
    0x9184040000d912600540d10754000395010010009007081e40d00d07001c020768854080c02c140c03042c0c0346e00415000c0030301c1007610340d8001800b00c0d1420181960041c1c0f0100d104d07948400c01001c08000303012107500100c00880d01521110540703942c3d581c0082a1442d20140311402ea9002c6000074006031354648c010011103800380b00d510340018048001d10726161034131114030380038000902041001c0d101e4280142041410500f04c5000301a801541500d40118483c082ea01e28250b120541c1e40c0141043c1c40000c2d02003800c02c80707102d44155101c0c0700c07081d01c6d072035003030f45035000e00402d00380d4502800f25001c1243c0c3e55010191000041c80e1380184600c1460200d140c2c101030340740c1d010000c51503002040c007000c10a001500401c840440c507203465161801e042c98010130203500b4001d442200700050380f817902c01c12038980d101800d0503070403940340640b01c0111243c91a450301c459480098040c07100c42c011580304500074400c00e0308050440b2a8040d5540040d460380d80040100b03d00b80d440040c0030000091180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 690471375 1250 690470125 690470141
    0x50604050708030406090306020924030915070518040b03190318240216030809010f080403020709150b0a0206093a0507050105010803041d1b0a050415020c04 69
    0x99070070146080400f0748225103d00004103040d4002c01c0c0300345c0365150701076000100e2003000700c00703008e0bc03000c500304c4c0d00140c0c0140c5516407180034800c0540c0d8182d44014605014330402e98403145068400c140b80348251034010700041d405900e90100c1102c0b071398100b00000c0321002c0103510b42c0446100f407a01400507015440110003209a41800700080c0701c0103049444100340d0800342c0803c00168000c100d050040540c001d01072418140804001d000c6904040e1081042c2a216000b444144071700c207891207000ac490060050340081000e220004007034014030f8500d081e0041c0d01e4040303a20381000b0017454100140020050b44074104108144100b0024495a403401001c0d440c01164142c0c43c3c100c41c40120290340780041006001d010b02c0a03c50303000c542002c3d4200f4020001945c680702e44a803240d00c644a500204560100000700441492600501501180100c428042c9901c05030801d940c002c2101b44042c8041840000740f451380c00085c0000c86a05940908074880130b15040004a400300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 690472625 1250 690471375 690471389
    0xa230306011a0703051909030c0816150e0405040b0709050d21051b010f060b12152101050103020307090c0f230f09090108013c090506040507 62
    0x50001001080b80e007030206a281d071012000140c2d1040d07941800c2d94a4815415610f030b201011032894100c2c184d12514000550780b190741c3e164001a070746d0310b03815a61140c07814505100d004440b400c100c0440031082500c3c0840340343c08c000411102c0100054102c2d841120305403440d08030001080041c0390310605900140408581e195002d000c1ca845406819005d040c0c04942d40d00000354854140303005d00180d03981941c25070210017166100c005054041e09400c0c1409102e541400310104400812105580030509031013070451080d654190750000350540030700c980b9005610380000403d0f03c2c10180d2940e8280c20a40008280e952451040c5894442d10340d016080321480c100c03101103400c0c0c1c442403a403501c035124540100c0702465074422858400d40040c012038200030016074001d02c0d4080c034026042d020030440c2c10340c44681c3e807521542d0aa03801009090003000344444c0c07120343c0c000703c410381c8042a040f41b165442c400c114041440100c1d03086182c15100d560140082204125042110b40c3c058082 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 690473875 1250 690472625 690472633
    0x180501140307120b06041107060e100203091203040807170309210a0e01090e15120d05030c130503060c03061009060801150c0602030708040c0803040b07020402180a2303 74
    0x103400c8030300c007001c40740c280000e24165013840400e40c80da8031904180c98440c2030703000c45640c88003103240034001006030901c0040603003c6e00f101083d002406200743c03880756807800041c05a48261894242c2d041d0310050044801520038400100401d548001803485c0d000e0305000b290b92818445403023403600004212031101009500c0015101031204016241d0803629802c041c0c559000c07410041c8c52106882e00301001c08440001002401080031582078513965041c6c031907001000103000703055101e00c26292160b010901c10000f04602851490003051680000840e2803007070f40d11400000d0a1510a0b00e000030242408800c0c07007020300d01031400101d446454145400d16928210300074010050501c00c94511070401280c0d10781726070080020400c0190700250447d602c1c905942c010f004241b06030380c240d416a8203da00409c203840c00000b100e0968940b01012810949140c1c2000081d40c0403010812036601030000c105c40ca61111040c84010b407644001c1d2075403070070000e103001a9100118050a200e988 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 690475125 1250 690473875 690473879
    0x9050a080d091404020c0604060606030c18030320011b080609040c0510020a1a2a09040504140609280201050906030a02070b04080909010b18010e0109180501140307 72
    0x20b08400908100c800c0c0004071450041000000f07030003400b50301d01c8014203026400410042103520750040c41510750903201000940c4600340300300c4050700e1410040e52030211051007440400c1c010014a800411100c0031488a5002000a1800d550420246011118161403410a401d41001c40d099110100381d039a200c0500e015150030b1045c060074840c003401743c041d03c1044292940f080c0700c01c003001c0c3d400840440c420041085920109181121004480401c0d45000c1d108035040f114080303241c02c00c1699850500d40881c081000420000e4030450703072140c08051804140d4000e2010a02c03401d486005460b1440723801a0517070303480400741d40e00740d1048840d9802c1310050f03070003000303684140b2000d41c0d100e40c1700d41d90b490b0410000e21030b50f440030704081464810401000005001040407040079100040c03e40d90314280c0c00042d00403d01c4403001001c0c44000f54616500c0b41c120700040c10381c14903001560a0b0b0310701a43c0c80150021011400c095141d100500c00407148034000d000c0d0300c0e000e40041c21068 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 690476375 1250 690475125 690475127
    0x70606060309081608040b1305150702010c120909110309010501140307030609060f020313050f030712230c070303020c060426030c100c1d010504150207080d09050a080d 74
    0x4803034861000c4e40b144021414600f030002c04000e0740c010b040481070b40da598680550b11010101150701c1404e00ca4241c00040610308000807040c2c1d01704640c1a140d05005500f40c0e0f4842c02d200305d810541c0c07001c2154002001806110b00d028007030220700c100040c3c66803424004811800c1d6001608001d0901e0b403840240b9406c3d440c00121501240e42228001030402210303d0903001400c1d40c01c6c0b107914454000320030701c005212802031078141c2c20700c208100c81d40d141d843e07801c90383c80f4020208040e029510841d00c4150660081c50b0410b5410f520203823103081009a84148501340d0805042e600c20780c1c1c0080e10600405404100480c01210216102400d1030716042e40000c48003890002036145225144465102d000d0410903100310701c0b400b0b410f07a00000307c4604142c004007104903030400040c141e264182840140a01000814101a521036140c14208119441d107640300e581280f0440c0f04200001641a1007842905038440b41c07980c480030100e1900381000420040780d04030004640050076200310003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 690477625 1250 690476375 690476377
    0x8060123031b040b0c010e07060801050a05010c0501020919140103050c04120212031c2909070c0b0c1902070803030130061d0102070302060c07050a020a060507060606030908 76
    0x40c050610580002c1001c407000082405a0382c0030107100c902c08500c3c40c050803419008042002178003001c0350071059403040103c40011080c402c59801120304d0030140007951140708240c03841d5000e000050314026842001c2540029400301c0305405140c5d1a83c01c2c0050191460001c110a100746402e00650411103650704031841948200f1140c1020041c00d0021529030800724110a00010280e94030765402000c0f8083c010884564480c1051800c03031000075210b2510400189140c400314200920500c9105002e400700d009080c610031b0155441414000954118141d44101c8443c0000358540c800380240c0881c0e0780615540c40159044031009120050001050b13a044400030480030884040303031080c0d02528142d0408520104a4503140c3c0800e211094209514035424012039000010f43d00c641103080380500040140103802210210b40c03c0c003072180c043c0041c3ca005600b41e42c20980c181d40000c80203144da03070000c0301181001c100310040c8001032141c0c2004101900b0140704414440e41c696a039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 690478875 1250 690477625 690477631
    0x30e01110d0903020f0601060801050907091202010f0e0a03050f0f0c09040803040f080301090b030c10170903090d141c050906221d10030201090e1e04030806012303 72
    0x296601c1d0b10302d209051081000b0020142154142c40c40c43d61102d0004005e1602405168058255400030822251040c51030308101d07942c030303840003040c00714583c011030f0384540480c0c07007204002c4202c0d00c001d419651048028000d45c400c600034010014400b04660502100c0c1000c4d00c5142c1002190301d6541d01d901050950059002c183d09a4070380e80e82c609049030030880301c40500005404000810301070260b520602d030300034088080703440c041c1c0c0c100108060011034a00c804002100000350f5142d8540e40415a90040c0300d12094a040480e000040b90224540020558580c840b88949055508080c058448840a8225118601348074100c002c0e003148035030424540100400240301164490001c424030f2010b1342c403580750601d1580c1c2c801d03190010380e4501c0580c8041c000302000c9000300307058800c241c2c02c4a6041e1100081a864070603510303d02840200062020310088091000341c25002c08114811031180c0c54100e03250521000040c581d0014411800405544510200c1010b80c1c40c3c050320f038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 690480125 1250 690478875 690478897
    0x406020102040812030c033c0f060301050412030c0e04050a0204050a0f0302030c121006080303010602010f060e0106031e180b0c1c051305060a0e061f1809020603130201030e0111 78
    0x2c020b551404000c1002c00e110544620180c0003003c840445000840816000340d940340080c91852b1116030815080380d00aa4008052089034050300003254042d400080c540340c4070303081c440751414040010805907107045035a007444a0340040d01740820b107420074029000d420106400c0f1441405c660200f03540307046001071548551540000048242410401a0202100083c041c0816603640440c0c07036903a0401e025940c05035081c0450515840741920803c01240e1038100f001c5060307460b060055006101c84031034490f40038031554244040740c403140510050808200300704842c00401d07041070704035000c0c042d01ca1420243c0400184c45800c100681c52105030a0814000031a510b501c42c1c2208154400c000084c254001e1604000340711f042ca27809900010004c2c000e2710000d60750500c80903070000701075584081d6084e010350103000451304071494040000310343c2000148805a6000503560350022503659203803049039440340c030440d60701d40549503480340f099000744030508550301098080d0041c00c004003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 690481375 1250 690480125 690480151
    0x1410060210050c0f0d0605031212041101090b0310150e01020d11010204081f14010e0c0c0304050d05030d2708090a09110a18030305190c06020406020102040812030c03 73
    0x605540c2c60004644c41040c03a01c0b0705a03910103600c0f0b4144090201171040c28468061004040e10b5410040212031050040000d1140c417950395599810140c408501d01c06d0401c2500c48002c2101001d081c01140600d0b505107490a0b031030310300310030241100c541550f650208545c3e034080d200503980005500d03030503c8403400c104e5a080000c0e1456402401a43d1000c00342d0300c1185103111711284c1400f0001130034018490144843d5000b054034950900081c810015800ea40c3e400045022480a000e40099180501520b151594480008401e8090a0019205500b0001d14070740340d062644154080030340d03110300c1440160705114040040d0082a0340141514000195503022035444011000141c15445020408260b801c0302c11710503900000502404034002861210496008030b2900d4116907050740d0341440c2100b05a0210300d500c1e000c0e008001449900361903480011003500141c00906429070005031101d14005001e0b00e0030058030051407000704100180b2060070700342c1c0201d80e401600c03130402c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 690482625 1250 690481375 690481381
    0x5010e070e06010203192613030e0405060a060f02151006110606030d030c030b0904030503010812032716060302032406040e0601020a06090c0306110a0206060108070c02040f141006021005 82
    0x420340304c0d80344260fa01ca4402481c00c02031050f04c2380d22900d94031070113641c42c040603481560070700c41122403d45c0d14503844424101d04000d00c1d440b0780d0600d00603603203c2c8103907007054500f142000004030f001c4c1e80111039026600010702049a2020072107416410500c000e0503142840404a612a1000e2050104064513105c2e50f8800c0c9009800c4005540009070450481d440e003130500405c281c200303009900250040c4030303440340404104004e503030190b0407400001c1190300c1803880c0b1410020702c85c0c2c409007442c007aa4440c4038038800160884001014540c07809070350780c038201d400c4022a154940700618034104884a84060f81c407207500f61030540e903007000d0450681d00d40c00c0c0140e14040d400440100315608080914080050034500e190459108000600031081e04000b110403502030b0415a20043e406000051255072090500365004807290a1000c0881c04540104007643c043c00e00003030003070743c8480301c1c50109100c40050310380c40840c84031010811400d00e0320080d00d031800030002c040c0389500c400c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 690483875 1250 690482625 690482657
    0x302060f0c030d020a1103070312050a0906090b040c1d0c0a1b050102180a140f010504090c05250206070b060604052206240c0f05010e070e0601020319 66
    0x101d807400190401200d84500140c00008040c1d407098100b600025680c0c2c89035081d03043e0000948540d43e5140d15680e0200e03189400a50040500511a010007500d698401c008180c1758414944801e004600030021441c0034141000c540355260b103d000100710758921031241c0c24989040540012543c58559590102c8010446011200d0300c0c02c130000d25141c20581c010004154010a4003481c032102c800b000c11400c0301001200b041e64030503420300000000005a5a00d040c10449400c0901418001e050a84a0940404483c0c4d050180e0010520004403500200d05c0000103034030706104000c0102032401c01c3d6005c54918029000024140c0760001c01240e029641c2c5803e4801070310000d03007103000c40e0310150b035108034a20740012180c000078505000032134200748102c1216070022802c0300c0d5400c0c01e10941c4044480145040040e50402100200400064001e000e445981901c076801401c00b541807683c0820310160142007181590720400480e00460001410120175264a00301003a4003034030129 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 690485125 1250 690483875 690483877
    0x30a1b091710110703121103070e0d0c0f030b01090642200120072901150314070e0d0b010902131211190801020315010e0603040b010302060f 62
    0x11003103118600300300348403001450040240005174001d41d078070700060074031610b02c408942d94010145080e12080002030744c8a0301800e40500400000b5184984601c0d0580b226807410181e900903400d28540c6610030414801003029142c003411500d40c0401042e40303060306100c41c80c04100c5036500c240d5400b14415180b116203540c28072411218000d1030014090040c00101000074201314804016503005034024034902c1441200074070a80c1c0380740c04000200c040654030a6801c0064104d42158100307403104205030b0b0300f000b0240c030b20401c50a805010350501c1028014030a1641064007003518182513003003d4981030f010260094454100480d81d0320340c0e00c0109400600d0312001414001d440f500000318550281d000700000008044259803032510740110700c01d50005210080d21388260380103261454034040b01c00c010b092480000c07007a8000d80d00c0819900f6a042219140000e01108040080b03550700a40003e9130a0b074200c0d80c51340b95240966500f01d401d1410b000181c050f503000b1031021101d0300000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 690486375 1250 690485125 690485143
    0x30606021212180d05090a0e0f071d120c01030b0d0b0112060905010c0e1912060e010e0d0306030506151806010509030a0615050a06140304050c0a030503030a1b0917 72
    0x14059680080c6881c01c044c245d42c0c8a80d00c11070182d42803020004840c0b4504080ca0300078100c00003420100d441d09901102c00c07103200801c1d07070040b0320307410802e031415a111100343e001c00c2904000350241c0c0000c80009800c030781640080c0703401010b0000c4101c000882142045043d159006058901c0c43d2141c24508010700741600002c2c810340c0784ca41c0e41406135410120040712100121180740741681f000003007400d4200f9a1041489025500d141440000d685d6080210510038600000842c1c1a8400e103440c90000d1a0802c0c4c000300e41e07a580305006000e02440b0441d0710242d42c0750b03024403c410b03100100c0e01040034081003000b5003908a02060b2a80c0c03040044443c0204010201c641c5142c1c01c1c10590010500045050407010702e05000081c01d0521503041400c40d02c842d2900340c018019040c0344070460348010800c807110b00645003e02055680d45440c100035501400080d500d0345040c2c1d61485c22290b020b00c0c45017122051651081003541d100b07039404281d4400b01040e46040720702d00c04045c500030b146 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 690487625 1250 690486375 690486421
    0x130504050c03060f0105180d0f1a040317040c060c0344090a1421040501031503050601120201030b060a05190305040b0105092e06030606021212 63
    0x1406000300d80345044051800b505084a0f4113003001c0e04240150381e140f00d00128084200004011071080e403030001c0780c039024180241d0750301f504a105641c5e010001d240000c4217140c081e071280144000d040d442801b0510400690814035942d0826444400c84440b05110320000c10034418841000c1505c07402003024041c00307601c0d00c0070068400c03e00b84000422500e880802001c0082e4500b09502184014140a550b410015001c5401940c42d100b0155400c000d08000c0c910a40b03002118138500c0d50760003403200c000686400d4a0390705090004040d60716114000640703c044610078800300d640401e00504550103031441e00890b44140c03005038050600d09640b164045004100c001626400c20001c054035022400703103c120150a4030b0a030700300d500540300509441d5090005010b141844440650051420403030210900400c803a6100044075204d41c80c0c03e54150100c0800ca8640c040c011400070b00042e00180c5182d0040070030041e840d01901e221590100120800700381c03148031902c0020104900f0b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 690488875 1250 690487625 690487631
    0x30f0703090e1e090f1e0c150f250302010605010e010206060306010b0d060306110403060513170a050c0105041113060602300a09031707050a02010305070509030a11031005011a130504 80
    0xa86c2d05c0301c3c0820130003d240c4c1c89402aa03c0340d009915000d0780614122211698103400c00a00305442e0280382c1041a0318100480018458440c90390b41814551980d0300c02c0e400828114107020004004986080d000d078199840001403156a0f0350100300141520308400d40a034030b41c02c1e058070b0309010300042c0d031002d85080d1418003071124503209000200180ea008480511441c2c40b001080700021030b08400c007420000f04030f505600080c41180003440303154120b14046082c031224056041c2168403d80b800c841511f44500e02035002e04200c8914226809000710070024241b800d00e01035111b020308160b24510322492017603502d0042034464011604100e02d05225116451050060420a00c501042c0c03161741c10b0b040b00708110308920f01240e00300e03503011000c1d00d2000407a50064010f480007805550078040c091107445e4240c2c40400c003000c210384c002d450b425585071941781132601b410b016003400c500903402c000041c0103030a80020301004083c12102c0e150799901c1228078090152845400160348181 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 690490125 1250 690488875 690488893
    0x10c0c05061204050705010c05030712022a090c0a05040905060a152102090a0b0702010905100c0611031501180b1602031506010e0d0f05030f0703090e1e090f 69
    0x1201c090301c29485041101d400b06c0e201c200640344600f001a00404503401000741e0800110b801c286181c0564141c01121200c0903000d40c1d5400300b030901c2003940f00000d60825411400c0c5011100705401000d4001c2d41c61500484035002851403061340207807240740384c0f02d2008c42c9680e01c8060083c0014217407000b00b5120018204402443d5020201a200303082c00e107494406200c11582c4211018401c00420780c900c50303450b14222007519000000309030306000414900180036142c110700304440310030954882000c0300d42c0740352800844401e400d25160a000606c20000401240c44140340482000d00b0315001c0180303407810b803581030341d0709810181c503070b20010850300c805040d0b04441030103d0b48218242d0b40d40140d680d484040d8000b08407130403400980e24054200c03950400d03003600c0b0541802016420300611031611a20704d15070004401c40e003051030029804042c16440100800900b1702500c81c88024240303190b2003142044480d0303000341124001404074801417030401c80c020380c0c40030440076aa0410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 690491375 1250 690490125 690490147
    0x110d0207050c03011b02060108030f040e07030e010906051906030537031d0405100509070216030b01050f061912060e280b030604080a05040f0b1801110a02010c0c0506 73
    0x418a0681c080147c42400004070329500c0c040b0598440d0035258a00c00c3c10240742000b03c83d8162000b07045401032507a01c40304100070040c28081c03062903c1c0500d81c0401c05080851100c410780301081811021075240070014000104082401c1100c1c2e0461080304142410110214a50040719030181d004603030701c941d151040581100031000069402400202d4450014081c403042d20003c0303540c050b05441c01a400c1c4050700c0e1114a50b80c03c5000f40c4110b604512200407145829980e40c0c0042d110b24201200402c01031038803003000328140c1d205654450414004d40709a03010801c21180b20001e2098a20115005664a9100d18018440305099084500f01030904510148490303503860804011800741d483c8a0406004030444400e0290040140b551107840d009401d42002d400e04003004401c00c40001ca030301400240b20082c1c14601c0d1b155030340704240d01c0721100320488403032703080d060152113801c2c603c01e0075000c583c612000341c0a0800c07440800312880c011034501900d0f049a030740440c010600100c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 690492625 1250 690491375 690491411
    0x501150f06140306090f040510020d050a0b04060b030f150a0b030a0b040c14070510050c0d0c030b06071e05100221010506070f140703150f110d0207050c0301 69
    0x1d9100c2d803104640030740c03896108806440100c0e44550440740d2034000c103d104410610055209004109403070242c034109094100741d910203002c401d2200d480b0b07011322000310402e01c91440e24280c02c4a080050525006250b8058040100000c000180180019910340c20541c1030a4200b10001c10200b02162980d0403d035403500140c8a407602146002075488060404d481030207201e88060b01d918006200c00c4a032440107900a00c003ca07a640690302c43d00c80002030034003586000e49100d1610540701c41210231403504583c0450074100401d402d00c0d040080325280c24045600c00c903003000d10032a410007699020860303440c8001000300f2503c03c20101030040e114540c003824400b844035000c41020081990700c0c030b084003003c1c0203031640701e00100240c2d400546140201c00a941c4640d03002192600140c3e001c90810003554429034800070015000400f14001c0c0c0314201d8050070300740f420081e80000940c09000d5005090040316425070009950003400410408280311080080003400446040014074240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 690493875 1250 690492625 690492629
    0x906020d0920030c0411120423011e0507031503051b0f061b0a24060608070f0e01110a14060f13030c02012d020d020f10090501150f 58
    0xa1203001036241207100caa04a9042158040100100041c146440c20000202641009000082d504007e100c59042c0b8180580d40b203140111501584400d1001c81c08140000300c06131111981d02d041c0c0c0314001d01c1000c400c9801e00461801002a9550f0750710800c1d0003c0c0b42c01044034809803503c4400004010000880c030000150414401001d51202418095000002c1e8a071660018080c00059625200070101c0140700740660212210450369448115131a09410801032404004030f600d03a0b40028140240c100404130740ca403080c22440c1c40300700200100301c502e6151041003050389544c98540e11950b05900000800301c141c440400003031a05400b00c41403034180c90481d000b035000284040d010f0700c1b01b15208104007101041c80d000c4a56045500c440c020303200328180104605011515411016000c5000f0803900c00d8000d07800c503a89019240c51034081000045522030f020740c0d1200c01000c104005c405050900104401045d4982a07000d442049400c006000700341c1c07000200d40c51080d0b0341d44c00b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 690495125 1250 690493875 690493883
    0x122d080c1b1b0d0b06061612050a030c05072310021c060503030a1b0f0b04110102010f0e0d140405030f0a060507030506061207030f020316090807080604080d0906020d09 74
    0x1400030b0310a0078803000d0240e004010301040c01c03a00c0041c0c0e00341043d40051031490742240c0510300d40b40c2190303900031442c1188045030001a1010400c07000290f00f40c03044140610a45c1481410300d40f140d5581341d2900b480781d018090b40c1411041050601c4030420240207207030301000003951949002281303883c0003032410103c15151401c10b00c0c0080c0c1030a01004440c2d940540c0da50f10305a00707000720081c000c0385407151002c48034007200e000c840c400301d2041c49910340250f20030394150040c0420701c4002801c1d1098280580c1145142007070400526000081b0444414064101801403400d440b0704100907010b44c0d48001d425004004040c3e12150000c00c00c010464840c1200f0000c03234866120480803500308444503a0088810400c0c001d900c9200032000e6801130303080c1303000304072164180340084c04c0c2c0c1c2080e110070070355807640020085c080d030300712240201030200d00b001850f2861405503a80d69501002d480a414600005003a928820b45a0003400400e0f40101003555980e60701d103041801010b0841e01030b1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 690496375 1250 690495125 690495163
    0xb04150507240c1e08070c03141824190e0a030b010503070b0a090909020d15051e060f040222032f0307050405130c03122d080c1b 57
    0x9800e0340407022980ca0050a55100086540c40110568400010103000c7e018407c0b104192510204278000400103d14400100c070607142d4250144a4922003545440c40310030101070020440003c0002540c7e000c005849242511b0441024240c0d0b0802c0d0143c01c40e40c000c40e044902109014034211460b0481c0c1c0d080d011100d0071540d45140c103600b800381c5408880000c541c608204180b8a0540001c0b0610340000e003410305051503a6107440740d07054401d841840182c2c8920401144c12225000480101c45150691901c3c0c82c08400140c04440107030180c502c125030100e4800c403844000e1100c0c071000c0407014581d4485a80b00d00b06044010041516034040307103202c0d40d604006484903190074503983c0f000350080200324200410440541401081b40180e40c03074960b42800410021301c41c5000560040001c02c03118815410010031981004089004020018000d0b801140204801901c0f80b5106e240091090311490303100c0449118220b0a4007c00000c8200915040d81c04a80d0428070200d4888036 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 690497625 1250 690496375 690496397
    0x4140906030303090703080d1113240206040b0901060e07020105310f21090306150509040f1a0f09011d1203130501060f0608010b04150507240c 63
    0x240c2d881c40704841c185883e40200c01d003000051841d80182986411841c004681c03584880d128502c15048640904c80c04084040104188200c644080e00c40032800080320b40351400c002e001950764040070b0310003000d28014a0000302208020341c02031002d0001441c12690340d0402d00c0000740a0305060750000440006200840740013850440c2d5458402c10b1810b161810b0403040d19003144255003441d0a80b112243c4840100180030340702141c8403086a21340300d00503c0350039401c0100c1103a04202907040b00b504c41c03100500080d900e0000700f45d032280d4032040c541c500012526050b00d000c102d000701074900340b4160060014100003542c5c01842549600300030002c1c0c1580c00034040106031008080d00c5560001103500459600d0340c0c009542c0884514210307843d00d202a6520390860300d4540c4590541340d02c00005114455104080600600c0741200d0305080a05000d1414241c11060070070038244400081c10900300411118070344103114105920804450120480b5001b9190f454014400140c0448030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 690498875 1250 690497625 690497629
    0x41d010f030b0109050402011e0225050604031506030503042c04080f0703020a02060d15090902130b04090f2409050c0d031206062d02100507110304140906 68
    0x841003141c2d004070b65502c0c1a481c0c505090300034000075109034100204542e00014000c20511541046841503000b820f100006218844452000e65401c445204c900307481040107640300c42c07d41d02529001001ca41c501d03070b0481c25540040006520003001030001040005410b6503090302c0a5114031107406106103400ea0811007040101d04540080050f030080c05403500e801c101c200544049482401101c180910f075400054a54001100810403140c503100c040d9907181c80c40c1d01d6074000b80310720b0405000c440d4040e40080c140400c20a5940441607440c1d0259103070f0750341c94210b20801d90300145000826200c3d4244030a60881103888610481d04000024441000074420002959000b4003c0d00c5084140700030454140301c603a0b001e80c100160201ca19404030f07420301c1400000c0c0342e141c40e515100c03000c6011808190501c50310784c3d2844140d00b0f42c5500d1894006c600c1022a141c2050b00180940c0c5805050728807280d4549138002c64030001c600490000344a07140141054411101050380c0d03516282 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 690500125 1250 690498875 690498899
    0xa0e0109090c0b1912060b04140102011d1207062a021204050a050f0d02031509061b2b090807021c0c060c23011401050415050603090304030503041d01 66
    0xc071051131440c0d44856a4500d03104003d04031845401480220b8003681d100060282c40d0402d401c00300d10307800c881e81074600941e02441040d0009440c80300d400319445000b48160784a61845803440e0000e90b000a0702c000b0003010f903004d15280c00304c02141480041880d240c020303c0011142100c400741c0700e0704c0d015420020100c2d06950858100400420301c050030441400038140034422080e40040601c13401c1e000580e4240282c041e98000c00c0000c10b500d10344207614501d0080003a050601d101281081440700d803020300c0480700800c0312210303100c0300d0080c4100600724401104000c0e01c581494105083d08100743c1038010140c8a00844010350f4000c0150300c1154229000340c002401400c2095041000030300820030300704441d00444c82c01040c041140b104c0425407800152801c502d940d00d02d00d2004001d990421180908401d0318104817488401420a414940e24056248603420220001e810320b44c00300b0481e40075550260990391200e44d43d42d2806900c0e410036510003c00b411a00001c100c1e9295aa = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 690501375 1250 690500125 690500137
    0xc0a0e0906010821070f08040b19030204060c020f180702101508030909070507080f040e0f04050304090b0a0b0d1e15030b07030e33060a030b060a0e0109090c0b 70
    0x1d03007082181d01d00c0c5600103ca9100c541704a90080b914000314002c00c1c02c1d80040c000410000780781c5641d80c1c1e0f400b5160b0b009880340300f4020050601c107000034040c041c1c1c0001050451541503505800d0141120006280d008000400040052490f0204003580b0f17408204a00903412080d02400206000c4c000b4800140701801001c0c0a50300a0001000d9480c0c0418084e801120900b800d600c1d190240d15416481d510005061111550018040080c180f001444551008602c003210b00d82d4201035607499164459032250802d060b441b46101411035a601204800600382c0a240b1540c40c215480244094281e688100301d0b04c0100328156a080078a501840c100c80a410980800960441d1368205621303901a21a4041640c0d9218000b602c070b504000120500160f010410440f05454035103251074107000d41410501e0000383e041c410b070b640b00d0300761410030707030313911038801c031440e076a04004205880d0360b503404481818002c01c0000b41c03884041d449041241d0191a000081c4e039101e041d8034086c2d03c200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 690502625 1250 690501375 690501403
    0xf0f0e0f100507050f030103030f0f031401030809011709070e0f0103030f030c050d021c0c0302040e06101412060f0130020d090b0a1b02070603020a020c0a0e09060108 73
    0x1c40114004420309910056000905081c06400c0080840e2401c407281c109800480200d40f491080400094101605503000f9500e0325080c00b031564011203012685406200041001402003a081c2c082e80c09210304c41d660403440c041d022120b00e864402180c8d0380049100d00c4c07440c20010400300b00440400c500d060f050329055100c00d4140c0502800c101c0060840c1c20f000400c00100b0300191313517180e0150004149180740420b0741c0346040070b16a003e0f0200c94906440905061042204100d01c80c140604141c0c84141112200615032440b1015201005046c4940103002d0780091422000d82230002c1d020300500c0142d40700780c41c041c070b00300040da43d0228081c0b6100710f1181c5205402d00c42c030b00003052400803030005900941054010304246080d01c2403240b0450300040540208107031205580b08440084401081d08003010f0f40c8000043c0d190360b8a402a04201500016004040c81c02080041c3c12944042e15042c5882d40c0c958246111a500351600720280c0a02e80c000200403100290b064031190304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 690503875 1250 690502625 690502633
    0x30402030d08100b03040f03090b0c07090b0301111c06060c0c05120c040c110f070f061b1209060f080103030219020d0605010f03020114031009050a020d0f0f0e0f 71
    0xd10400b40c800d500010100c0f4281410010f012582c07141041c06103000741c5c8104140010b200051034060090425078010f83c030b010206010b00381500800103003040855130304490001c0c000207420042405004c0b10b41c1e0700701400300c00281050030102c602e1a5401807101e8814100200c1e61075000c00c0314400e03601400a0180c2200c81001c1c0468a4403642048a5031503080440300700e105008041401c0da04070850702d2000c01d04a582c811900c0d403080c80007021007000400a40103d60400b810422500410300482c5d0401007010400c900e05400400440a059007210071450700c00c0003210001c01c061258014000081c00341020740b580b05000e02003250681e80d040e00900200c204843d500444043d4490302a41c4c48040741880c08007151031480703882d0281c01d00303541c2842c0c5103046000141c030503136102e01c691114a0702041002100b42100f207040050314010807021400361680036098029000d52248031088625004045030305440b540d000102038504c05005001984c01c1c120f6054840003120282031840d04 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 690505125 1250 690503875 690503893
    0x61502070f050901090c1b0b090c06040e040b0711030705030706060e040c0311030a02041515050301140f131505040e15180a050a080403020112021c0b060412030917010203040203 78
    0x5003603080100c06c4000d0b8a40b5000b5100c0c0040c0780711155218900039598000c907c41070140c0d034441403054103000070083d0780240c0350604c1c0041c0c0385403200008001500706011003000c5254030f845165410362050880d811244c4500035420050b072258001d500c100d4401d0703d0305d840010f0005452032030b00e1180b07411000e6100f28501d5505c8012800d41d0b00e005440c0c1c140126071405005a49621440540c6002c0c0c0c066402601c1c100b101440750000c5500e0340c10180329080c001008104108202c0849000040d5030050b841600e0350f001c58140051240b601700c0300741c1010146481703518594000c41c200c17000ac45050001d86075221255484400c040403841007081841c1c0091004108104c501e4811074606d4104d900c1c030481c81c3c4880b41403280b424812181000e00040070819583e204985100030368860030110702d0103011042046c50545541c9240b0000d079103803c0e980c116607440708241e8006049404540050041d5803400408446c0180925442c000301500f5400740d804052003564403840d0b014008004220b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 690506375 1250 690505125 690505139
    0x190b121009020415170601091b11030f120f0109060b0708131d09010c0e0d031b05070609051e010e1207031a070206070206040201080105150904061502070f050901 71
    0x12281807810ba82181e1103503081c0c0301144041199800612054a10100c54460104800c0c20420107038041d00d0420300b40f01c903c8280308049a40581e00340d000741043e08200d1034003e0400d05500411500705009480030030340c101007113031030b9200c0c91142c4080f40b50750981d41c0c1c817060303400d003103d030603004802240321300384440e0000501000080096500c1100c0c80c910950795408240d0380203900c1507181c045800c42006000000000b402407200c05401810070448003124172010404051400300c029007040b9440044035120755030007111183d03041d080030a4030f10540e16244050a8410280716140c05807031b4103803496103115081100140c107035034140e68502d4074032402403c01607604060103001d20140540e00001000510142d0601d24081c3c649110b01c030103103452440603082c031100800702c0c1c0940d007000d0704110050307030701c146118152a03044542655031101400c446c040c0d8050301c81010307003091506001245444d0015855075801390154201d5020b1a203690080c7d05c00301c1280310f620303000204440103000078 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 690507625 1250 690506375 690506381
    0x90603250c0b180d030b0402040b0403050f1009050309010c110d0303240b0a0c1a0702010501140d030f030f020904051003052a0d030c0f06050a0605060a0c08031509190b1210 76
    0x1941b0000c102600701500d5112001071360b8816402111164421a065003410380c0501411501428041081290030165200c440d100d205a0a0403410445140d4040040003170f80300004401900c0a0515030700c003611890080c0040c1305812170100c1501c8800c442420000041c9803500555064000c07860500c001c80c10b0036104401202002c42e244001c649a90040401c0c20030301a101d0511640042415490421220340041d0420700042c060901c80c001007005c07a8200740c260500c1c020f036107400030b900d40055000000a01850103441d5001c1c4c10700003440b01d10b000f54008070060364000d5050f00e0803105921147d400c165403a410340094120880c682210720b1600b0340321400d40d00c0c000d08105400540c641e80702c4002c580d15400885000342c0d01da042c001080e1303040c1304d04000340506507022481d202c01c005018041c401101401420034000000050085d100301181c40b00f240c2002d44202d4450038a40020714402c80e100c0c034800c00c042e00c1c100f4508070074600704c1016156002a0700141c07103481007296159010b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 690508875 1250 690507625 690507641
    0x9060409111009120c1a0a08160e0d03020c090603070608070c020a091404031710030f02060705031b010e070521011b051b12090603250c0b180d03 64
    0x1840704403640002d1399141c000000e1100d900c144105640079043c400608050801c5103440b55a2000c2032140800060708840300b60f07044041120003503072000507200c00f15200d8841c80d0405030091010030084c01059000980c241e502d0b941210954690703541d0310245503807075a86104440020b1350040105000351b02817145004200e0020348030030540e81d110f0101c00b083d603c2400c9801c661700b0407a0200814140d00c501c0440304d40d00085660381d0641084200c9100c3c81c1d6240c0000f51110307100e45051350031940e9400c11206044d9201060700d86a0044221054140003010081d0549500b400c600745c0703910a010a0690580740d000b0802c1c2080e50074809001840c0c040109481c1d0381d03650381c1d001c0c1c65480c1130243c08029002c8181c5c2c1e6541e03a4403004070120100212020440d11154880c40f0003101510420041d40d030400c034246c440540340e903540790340d401d04403417001d00e5505c0030400c3e80c0302e00d50380550200c0300321141c1c0e00542c842d60a039103841003402c22206480c015020f09801c4401c0300d0720741078429009001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 690510125 1250 690508875 690508877
    0x18050607050a0e0d0c030b0f01080309130b15031909080f0313050601170d090f060f0504031e170703020c040c360e090705060901121406090604091110 66
    0x10700255440132840d404055102a00e40300c05441d8200100007100c507074640e0080031061203c0d055450170000c50f84d207001e41003c1078803d9142c2d505880d0880b80c2d9510240442d14004c10b81507500c81d030101551500e5000341c80d101d01c41c90312030030304007410303031480c01020806580100d8003031402c90112a01d15890b00050700e1503450703520151104000c82c600b080320b9070281460b14899829841064426850071402104907024400d080707404020b014000c036941d104903850b0381090504940c0d030b00c01c00c4542c1d12603504014150900502e071846105c041e03420050720305210f4100c4428403030700388040350868040d840d40240141d0001e11070b1030803410607402c094125100c0d81000b1112901c54041607502c80352000741190720384240004d002400030200d140380014035107030303540b000c0c2801c042101c1c0391142864010700d800b440d0001940e040c1030b4840e2900300401141c281c0200030142d542400349076068016141c4030302c1001410045440c0b444d01e4410326840c1544402071955501540e400d1003808912000c50720 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 690511375 1250 690510125 690510137
    0x7180510090e2512080c010e160303090608190b030f0d111b060d0c020c040c0e18010609050411091203120f061005032809020418050607050a 62
    0x26408510740039046040e00000081c20f0f10000c3c050140c120710030f070112007501c60511401c080008102c42d44240ca000e0b0703003080c07495583d1840b01c1000780c00750000c001091541c2c4245407940d4000d200c0070003100241c0b48070307940d203184440d81c1710b400301d50690080d03540d9110091031035003208100c030007a8020407030004094296800c000b00d551031103042012003007501001c00e01710103184001c200b05000351009450709004608820a102e8082441401410310002d602070381c550800303c8a500030010740340f10100c010301c10f100d081b0070304900034200180000e40601450550303a03011400e2200040142c1a1040b6176100b10305d1a162800f080041c0085100c2e008a0030001c03c880e21858542440d41e44805a9540c011552400c009a032500d0684000b090302181062401c1802217a554031700354000c4035101450320319200c0d1214008500078210740c1300c1201e140b4654248006202443c2e80000c600710380211401c100648549040314250003101c03100915a030410b00000f1400c0d070091020f400280114034001d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 690512625 1250 690511375 690511379
    0x2121030124030b06041d06040e0601050d08070f14150903030703020a3608010c080a0209040b0d0605070e040b0d06091a010b030f09031216050702060d0203010609060207180510 77
    0x219056174007a030444280306881e60184500c21404000c003a8000c1000e135800c00411400940c0e00d41c80c0d4506000712403080000414110500c02400141c0d600941c01061a074011560703850701e03640760158a01c500b01076020340159002c80320030403038415101b040004055031842e69403407012002584010040418020000f8440b403104004c200e00c04075050500c50040103800100400810100080d80203240d01d80c107104031410000d92000c07650740c001c8425480036803182e041030001006010307411301c12038002c489003d01c0c10a002442c5c008030b0042c811a22a0480e03401c2c1c131070600094800d400c90705a003101c55005034100140e0305a100007079070340c01003552500508012215244078002a40084c6c0000404024800c42600b015106500171b0f0301480114a880748040300d10404002c020603201c0660350302c8294000350341c010811a6030f0300d64018481c40c1d40c5c040090900009420038014113000410b11140864030500024008007030381d4002c03040203006201e040e02e000c0034080040540d10b00e45145580 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 690513875 1250 690512625 690512629
    0x30a080c0307060e0a030c06110d090b070e0d020a050d050c0a0f03030801050604060e0405090f030c07080c0f0117070210020d0203040b1f050d022121030124030b 71
    0x15101644400000d1680c0d400b003401c0507016110340851040e8a40c010400c504006904061a0860700d07a001d600403511544801d0b18403110b01560b03500d290b0b45400c18141c1c5040100321074642d4400c14868072100080c02030141030046003c0351500003900201e45401c14030240c030303041001030b01c9c1c00e11601c122040540d0360030120b821000306030b0013020840c0b518103052041503003010303c217409031005541c3d043c00e0925100008002c21343c43c20301d0324042c594600100c3c2e480346083c400d0a1a2003280806c0340da54125001da482c1d5942c0d614441c48000d0f001d050b00d213030000d140c0326200a18200c0e0580d541c0c0c011342200c50112003d220081c0008081d40301d80c9088105031146400a0300071140c0c0c1c03250041c0c80c0d1500d420304540002000303141c0f2441149605c2240d503c5100750b911b8000f52003040c2d41c1910404118030204202041d41244409141a17519040402610015100e00500b070800e004003101504103099003814002030040c881d42042080002081032100309504200c90254900414a00f000d140 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 690515125 1250 690513875 690513877
    0x91802090d0b0103170306090a0e0a0c0b0408010b04020c031b0109020a0e0f060d030f110a0c0905090f0a2f1f030c02070503191b06020a0303050906070c020906030a08 73
    0x41c0482d10003040d04010024003d081500d00c0403854031606a5240d890010001100300368020b14252445540301c00742414840104800030b0006e50001080202903100c2010300c0442d0898800c8580c2c540c03d111440130307103060034000d075150f0700000070045040c403c2d43c80384640141d9505031440b01c20b641c1c401866025980b0403c44000400c0c1000721400315081192550f0140b8500074903150043c03409940c1d1f4000a9848014105640841e25020300039451040f4402d060180c500301c06080e0509500f00070614420990140e805016035004841da402110726989031609041a4040e2110610003610055102c410742d99443da141529a0700100c0300d0f01c43c2c0040c001d80709800510810b1055012030340100c030b40511802106440c41d0004003082e600d000000790395402c95140811001801c849448100300c0d100078010030b544010388841ca0429100c0d02c002b940c0d420040c1c800e034002400c0c031020600c0501c0201d40b45000310f44903030380d41001d01181d400748854448091f2506401d8451a800340300400e121030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 690516375 1250 690515125 690515149
    0x2040b19090209091312081e041a010e042f030f010603050c030f120a0c021f090b0903030a030915020c010902190608160309060f140a05060109180209 66
    0xa0001070711402590f061150022000b407184801140092035640495140452400c12440c0e9181c540d8040d950212040e000c4080d8084e444050510701c400d00082204180300c01000042c0341c224404641c1c4e0b90380070000d1164050354050250002e1658011910411410803614000034154460000d000c81c0007003450031980d09144c40080e559501c0a0041140a200046000350200c00034800c200da1344401c02e0301d501d00c0140320054140d002480218a60003082d180191540041c5445026968000308106001d503681c1d00c0400500c1e0f5110101d01c01d02c02109482c0030140142c0103600b800c01c48001a030041c0303449274050780c2510b0805014070303102c0410300007010155618000441d92140a2041c0202110403400c0c418846440d11030030301c01c1507440094140d01a0074034000c5130307100c00c0101c0c0a074024585490003030002403c1c5500c103503949030184c0000754038030504422008948d0712000000308480c41030307410500141c1c03c900200804010902e035440c400307400721801842c15a0400000e0f0080740d4403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 690517625 1250 690516375 690516389
    0x30b0607150e1002040605120901200a02070b0f0910200309040f05060f09040c09020703110c1009090209011101020703080103050f150610030f0c0503091204030506010302040b19 78
    0x600100800b40e4010b0103031a012542202042d4105800c00310007500c0350040050100a0091003c0054050242500b100e0b4200d0401d030071007407460080c0541080a40d109000d40c6d00076100f180c10014645511034125448400e803481c459081c22160f5040100041d180400c0f00c08210140f00b80c81500511030109100d003010080080d5950012003080c4015a4100100510143d14120030410182c807661500c10340c2c0d45089424045558a0303107400c062645d1b02da080600d4691010410604140d088840a000e0441e580119035080b5452010008200010150180040d0442e2402c01907666640c004c2c1202e95030504000b040900780f80d80d0f950880e00550700580020302030300300403c148401401402949000a005000c0e0101480290001c660019001134010b070344040b032140e130481c426404807080d903a87c100180080000c468000f8402e400a6428014038011002c40c403200c4121141181e040303a60040180032280c1c40d540030030004002921006400440842c1d1806121041c00c0030a0058140c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 690518875 1250 690517625 690517631
    0xf01050103021813061502161512050c0405180402030703080c0307021201090c0f120305090d080c0703030206090109051506010302090d06020d05060a0b1b0f0d09030212061303030b060715 82
    0x1900d52450600706c0b07030355007032403c0d900041c0c0403048524482801c88180c03019542d01c2141c040e542c6070111800c0341c840c3d010080051030300007884010302c1000010702c100e403800c4455140d01d86540132180c4022505a500079456440b030603007000014144c001610820285000b601e05108450b00446c200c210613509a4441da59a040c64800b0004146003090140001410702d444040c140126407900824450b409024000c002c24400c91079929181c4544040d540700c4c0a0a0312981034801c1d9a0b96904580003c4000d030145000042c00e0744014400c21320f110703400000030300301d801c40b00381100f0380400c010f8071050406400304102d62031500e45070300b58804503210300c200507600d05031142030408459001c1d0415200320061502081008008426a501404040388004d08180d01c040c91720b18052480c5030714100c5004094880c003c041d0000380720703401c0303074000c2c0e0711060f118454242c070ba40c075918201d81c0020b9030b2410210440100c0c1c401d07880720307003606800b038645880c01c0d006460304201c2c0c181401c01d600c80603131 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 690520125 1250 690518875 690518879
    0x4031b06020409050a0501120813090f0b0915010c0b1005030706110f0c010e04051503060a0c11010b01020d0809010609050c09010e0f15090d0b0103050102070308010e0f0105010302181306 82
    0x40d4070135198009080d400402503941031544e00446d0032030100010b091b41d6800f1450010789040c4002c03200007442600410001188a071a07800041d25101781349901c5429000000341140090400465060105940301e914040c0a955021a034a802429056101f00f403001c002c542c030346041050101074040368070385174a40100c1e440a540b5124030840c01c4841908041c0345d202c80760b42c02c54483c600c40c0508540c04516542c030b03003200050003001415400d80c18401c080a020940200740e01c40952241155103801c01d626155140c14281d5002040341ca00590100354845412440b504482e50801c0d280380011651940d620111000d0b11400e6589003c1c44c400001c50066668101103902e600b80d0b0103588080d140d40300c0100150b041c80c2080b0315a40d1040b400160700c46c0658650b503120000d01da000d0300d9003506584a09045000b500250b01c00c6001c11141e40c00402e005640c03000c850320614400710031a409078200801140a034010001d40d184d0f2140d140e03401046c81c0e685840305d908c4402c0000340041c0d841c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 690521375 1250 690520125 690520139
    0xd05040b0705090120100c050a26040308130624091a10020a0b1326030103020f0d0210020f120a09050f0d150203061e090f04031b060204 60
    0x540a0407030024464100015485a41c0003540f080403400300c5208181960200d160003810004103a224020b0245804682d00b90190444013503c444103555032890004400840d10a0307045500913000706c1e03210038140009002038428425613901c0a0070304422100042c065a84009440060004c1e0590080182a1289116000403e034000b0021454180039100201c00180b4404007507008590192030307914042900c95008110341a20603510a03404030243ca8031481c01a000c46e4400070031281010000c3c9242a04c2100d503420070074560a0783e20b25880e5910399030070402d80e0509541c5041e08070000402400150303441c0000d200d1b00442503000707048406260982c041c01c100c6000b403400d0481000703020342d0b245594007040c218180e075010b884c104141c651000c0020400084e0714002081c50080e0307684003012405980107180588416101c4c407410300c440301940444088980b0702c2c40d400203036000c001010200f1700309074280c005000b81010f0030040b200d000340c9000510300e03c0c810740d401600010308000c24 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 690522625 1250 690521375 690521393
    0x80303010509160e120f03041e0b040806010909030306230103050a05090c0112020d020a090f0e070c030813230c100c08130519080c0d0201090909050705060d0504 71
    0x10710507107068688540e0203078064420401941524050740407881d5005c401501007203c07106030800d10b81240d844994942c8031b0403000382c98018040c440c0300c013010000384180305981605c06030f0f160780010b003180340c0c2805905401000c3c0e424040d01090380346c1600003405950041c90400c00f113590f08040e516240c12900160580e040501444015441c22042003041000460b401d0750b0041c00740b8016101c080c51111543c042e005a401950089100040801d44c0e41d8003c441201251900c002c004940c1d681c910900320300c844115103140101d000611040d001030710a8019550003039a0300300001890fa0681c807048040902c1400a40342140350052910308000c0030041d070b0040c1c4800311100b190104407004000d08050641000401a190103d2102007020f200301e41000a0b25000e0304801910a072a0f058055180d030604ca101128001e8512903229800c090b08250001343d0103840e0010f14034031700303002c000050050034000e64071406039401c007186a41e43e4100520140180744008512410117052071940 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 690523875 1250 690522625 690522631
    0xc1c021204030303054011060408071d01030b0105010302090315011e1a0906130305240a021e18060d090c0b1206060717070c09110a2c0a080303010509 66
    0xc03c5041d00001d825030f0001d22050800300586c41c4440c800016203103028a44030701d0340c41c00c091380120702140109494400242d820100c41087c0001d9030720768024079039000071040a01000c1c024044200050110354046d03001042c43c0030014086400010441e402e20400800a8200d60010b2200d48075071140d5480201c5900301a0903400118441d01a1564400b08103101c1c5640c07a600640d4003042d81c08600002038114401540c0000c1076950b110360400f8401141e070004010503121611090105030340312007520960700480710000010140300304141c21030307003141c000225040e840d45407e004140035495071005031000640c1c8a0f000300e162980c900d05801c0c2c40031207422907850110240640c3d00c0b5541401045508240152522030765075051b070078a60ba0541418000008000000580310304000c0b0f179007181421680303102c2041152144002c0c0c006200e00c1016000320001d010801c2c036903003e0f5160340c4000072200c8000088001c81e800b42010034400c806d03c1e880f0941d80c1d04084010441801c0503c4800d80c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 690525125 1250 690523875 690523921
    0x10207080c010203090d02010306050603090f011b080402090c0c01060e0103050111090d1b090e0f0601050102061902030c040801110c01270b10091b02010605060c1c02120403030305 79
    0x841c000e400c1d0000b5a82e00490810511039022407030382c3c40070340e4040e91089001e8070000e009255a40390084e0007603684c2c2c0c81c010810840750700e003034084070546403035142d50200d022060359951040d444603020444100d4016000007494641042035014032182441400001c1c150010001c28039891410071070f007110280c502082c0c11100c20800ea100030343d01c0e1100407010640c0070740c0c05285139401313113031680d0380710351542158059a10f0080116052200050000f0860340307140c04546203a030f02c4a0049840e4031050b203e490050f9610040710b02054107540107181c1c070021564915003041c0c0e503410380da0b00303440c5000411b090f20314000801c200031000a00900915242c0a821960054140202c00441e08184c030006003010800002240e403954016002c2801008102014084124072400303280502800e440c14002544c42d00e9000555420b105041c3ca1109000030042c02c03840070110120842003a01c01058411800b500a24903008203040b009400514002e640008d014501000b90005440c0d00d49001d02c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 690526375 1250 690525125 690525133
    0x130201020c04090503090d08040b030f01090506040b1005090301020d0c050403150c1b050102120f01051002061618080f010f050906060a031b0f0e0f010506030f1b2701020708 76
    0x6808104c0c00011100c6c161001d0324840c1c4402d18604148540d4016500018400c210002c180446d521207605030300e0607102d003060304002d2507e800003088211503da140315a080040002c40c4850b19004074003600d034201002c0d001502d002e40e08814242192903102d80700d00480c1000c20140140300000d001d004001c09802e000b08907a240000c0c016010607105008099000c1c001030843c020003500b03405852524202e0342958195042150750718002c54000d0155034007401000c1c0340c503014a4070000d00d19010740d40e001c60280300380c1d10305442120304884940301ca2200c00010040020040020854012240d203170038000203178004d180c6080d005444c40508a070301180d00c00b82c01d1220302d03501c001028040303d40c898554a0502c05941d070b2841c42c0f9074558410350301c003100043c0002d049680c003c2d91a1103030300701400c545801ea899204114450009903400691842c002001941949800710310101d010440d055450400c0c02d03a554049903503042c18007110311a10b0700310440c2e6046d44c04002c80d001404182000c5c1c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 690527625 1250 690526375 690526391
    0x504051c02070e0606070b150112090b0c07060603020a0303082a0307030e120c1f050408040b18060c0c1e06120a2003150d150e0f0303130201020c04 65
    0x707685401c2c0d80600780d185003400d00413600070341d00c80b01110149584080d0980e030600d8000c0004840244200c03183c0d000c21000828255407408911445038015400b08103141e007034642510424080d00500c0089412a55900d008400350360b07003400c504019880703507403022824603141c50b10000c420340100d00e040c482c07000d03c480048074110f82b01c01e90394001c5851400042403001d5683c1249020030204101240042c001b8100d01c103500d000c10a0032040c8061800071041c0320b030640c9050100e070350031103002e860100306000500100e2003441c01840b41240c060000356031882510009242d507070060185400c5548050081b901c07504080c000100d102003a0b0000600c001400030210780b140c46250301103440f0890380400146802c1b100d80c080402000c2c1c40b82c62104000700c1051101242d4425181007031201d01e4807a4503a1140b9241c0c05aa41888c0c1c0110104002c041d0500450060700b00e80307420041e00d00500181c1340700108200301442c07040b0361244040000b202240006401c0c44001291603000e1400d15100d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 690528875 1250 690527625 690527627
    0x110607120309050109120f080108060709181104091a010e091503012c060a0c0504060e0d1b170102070c0312170f0609130507090209180a0504051c 64
    0x4001840180c1d041c00b151034406840c01c540100b141c1900240444030051070303628040d520003008401c2907202d1300c41c11740300c0c0d0321044015035510302100c40800144207440c09200c1c2207000f02071983d030500d948031301142c0e51421221450707aa4120350801c076038030741c0d8904c407a04060429000c490580f0801b820710180340031101008c41c41c502d00050000003011100200f6401d540c03400d41c08114941c03003003401210040300420101c0c61842004110f840544a079401040c0030b450148036031a22042642c039224501860700109a0f130f8800da071038580d0b034444910103c0402007695a41c460141c250740060542c40175040c0800301108802284400c04168414025007000550710814001601c1d000009241404806503084038049000c5540d441119041000d020161611000e02802000e0032500c2d40a02d5507146640b44030746401081c041d01580c03181c00c08114015450740113204000d0701a0070083e000d05030441c0c50b400940195404142556103100300424010701b884041c02840c0d602c0c0e5a160f1007020150 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 690530125 1250 690528875 690528893
    0x4060e070e04150b040e040302070602071409180a0501090b0115120b060912060103060b0d0b07030b03070b0a02070f0608040c091a0a090b01091a0f07050c0d0f110607 73
    0x40780038015942c0701e60b0110001c2111401800034901c9a101550f981d841c1c0155900a030003c2d80c044025204068001c2040784c004079a2405a80441e030340908030b81d2244040110480000d4240741c4240b8491103481c00900050089065190044d00041030a079480d1410050681059110750103540f5110341c1000300350350248100190000441000c14903076140c0c0006401c1c0d200e01c2c04490703031240090070851441000441c03842d040728002c000c00c201c901c4941041c04904d408500380100380a10700e01c00100810300035480f00440d00006400c40302d1454441103200c255500800296001d81e02c007100070800d010064000782e003c0e200500d0314042c1414280d5800080c00000d00640c44541c2d242c6026841d145094441c0001040b07004118000c0c4075643c9104200821802124500182e4562004500c51000c0320307000c1c807072034500c1031554680900e800200c42d05070803102e0308507400c0c09200051501c603602c010408403040d02551b0080c645101c1450010f11603c2d40106090003224103100650113300c60380 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 690531375 1250 690530125 690530147
    0xf06070201110a0c060f141006050a080c0a021e010e0f160611030706060b0711090c03011202010e060a0819090305030606031302090103030e03010f02091c170f0904060e07 75
    0x2042403000d283c024542440a040d901554285482ca0035071f04040100500300c0181c06440a140040e9030303070f038944004558504c5030b0a410404141a03102050344080c0341d6000f012103850900c180d83d4200b40d0750320590400d0315213019030840e0340c0d1500b02604d01820188500c000b4a140c036401400c40c0740c039806d0820f4001913680304410900010840366642e00d803041c0b041310f6070154844d001f00069921141c030841190844d250a64509035004103806660a01201450045d000380718031701d08581c42c000300d5070000800090200d040144407141c08259031202000b504080800340c0314041d191802444244141e44d00d80360320040a03082c8244075012030307040b4040300e401031000d0724a00d40c1c950380c0b442060218044205c000b9000b2814000000505a024400d5410700b90100c000384040a1400004026030058110726544104421001c0034204991075555005511401409038444502c1903800c0d8681c01031380881109400c0020f07500f0203440e10f84540e40140c000400701880504084000034003020084d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 690532625 1250 690531375 690531377
    0x103050906040f1704240c020d15020c120d0c022103071b060504050c191503110d06051f17071b030e040e0607021009150e0f06070201110a 61
    0x4a003d050034840c842e0641c1020518281e1030b66544c80d50f070307074042c10800164200010802c81141d400c90303920f0300c620b080c0041c40340c001780f00803100c504607151546520300c1c2c5441c0810b400d50810080c4446402800015220034400240301c1c1c680b00410b5280042c0c42d0400c07201021500b284942c00d154181099141c1c04086031350b240d403600d954030808241c1e07146200091031651810b91200d21000c10130701d50041440b5500c51030a0390700701c19102091001c11240ca100200c040040d4140500400c90072101405601d83c41d4600850702c60a00303283d101c3d0039841a07080d0400903450f40400d1026007044416000301441010030100c03a0301c2c01000003080700000380070402480881c0c6022600d0f00e4030070061030f0455000200c001940e4030032842c015090000482129004034103040c01c01a4400001c034031184a41200d4010305008010040c540f80104400c074021111216004903041c0702800718855043d0508400e8000c001c1e940901900c1c1d0b1800f04003c0029045a04040c560742055201c4130035a4180d0401d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 690533875 1250 690532625 690532643
    0x403080c18060d02130902030610052101080708010b03190b1009021c05060d08070f21080a0b0a150c0f21140f0306010503040f1205090f010305090604 66
    0x100c0c01c00d11040d40e040c05400703a114101080c212401e031255802440c4026013405c0011406540d03040381e00680c0400c84205600441074403500c1300c003900800080020141c441c2040070714154540080c10f550100b03802c400c1c540d500485060001d064248542000721104400400320140c0480c01c0004000344104020648c50680c0d0104580812200312140900744c541c4c0e041d5103d101000d00515641c00a103050214541800d02207851828098454980607800108480c900380003511040b01c010205202155208907500070041014400c050015184280c2c0d1b94038012401c1091200054409210960740300385400c0d0340803c10780380500c2c0340099101c401e0502c05002081030804426820a1042c00b0307054000c41c10103a40c4022646200500c0400c040c0c9038010000d510004101c07060140503a00f65882408201042440d0f010340d005d5a0b200e031080b0615181c0d84110758460506182040040001c02d401080c0324100349845061800740203000e00c0c080140b4685040380031b50303404001d00054000c1c0c131 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 690535125 1250 690533875 690533887
    0x80f040f0503071403180108130b06060409061e0603021611010513140901080f0705130b100804020420040b030a02070c0806070216080307030f0905150c010c080403080c 74
    0x50502c180e03070b80d15400007030070306001c601500c426403a9440034546c00d0300c102101c2c0c0c5d002100e6010f105018055036481114002d164a41e1703840d588038080283c80198850000e00c400903180030036001d01c4020708541c500c0c070500d643e035200d214070500e40c4a4000751700741801400040a541a21300320004400e0704020300090b1031480b200140c81d1489510b51403103d25a02ea000400c41c1c1c0c1c44440420b915a50549141c0c83c5603903a4001c07940c9440030b5441c0003207160043c40c0100490b240840410141034210003000032804044800150108121140f45000c18220804c102c258039152040e0403141d01c080f131418102c03004400c0081c01c40e11680c0210441500b000c40810340000156040c0c407085075104200c05482d40e100c0c0760441d038a02040701d0342401482600b4504403402000ca400b80103da05001c0114103150312a03030241d4030710703081c0690300e81001022040090f142d81e4407074840784040001500d40741c1c1c6460280041d82134480c000c810740306020030541404002035000c0f51032070b841a03c80b1030f0252614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 690536375 1250 690535125 690535133
    0xd09050405090a0b1005041107020a170d03151203080708090c0a0902180301021b01111801051c020a09050a0b0406170a090206040e0f1f051e10030b10080f040f 70
    0x1e85c594000b1a00b081c0b03429807400d0001c0400c0c00500312140200d501d480350aa0341c030525448507508600c0c025940c0c00841500399080e00940040704d0b200c485c88020b04c00240c4403501380791003080d03810090300003544080501c0007003500f06014680090342c51010349142100c00d0b0124442c41032a1140344162680020b0894262104c42100c8524080040c000e56035074060700c1d03090000c1d16044003038074003e5103001a00e0300e4110136072003243c4039501c0c284500e821342102d0304019200340c0c00c1085411800b09120858069085591008195425680e150003007010b0070b107018861480180d4108440d04642040705108041e0850420740e000c4c2403020a003620f43d1b60f03d040301d50241c080365100a400000205004c1381040199421a106024585409800d50354520320300c0c049203424840042c01203070418052007103003001c42c040218061102d40e03d40340c82001d072004c26203800703001c091000003a51712904003040e4a0a44010511480a032030803e4035030604000700000210040d20050800c070040559100300 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 690537625 1250 690536375 690536401
    0xc170903010e031b0d05040311040b010512090708070501020f0c120f01020307020a02040b0603060f060a020a0f0b040215041406070309091401030b0604060303050d051012050d09050405090a0b 84
    0x910382d44410340340c0300d102004035800c0c80f140b144a90b6001d400358041460202e41710b4030a44e0100e07500010902c000c640384001780b0009102580d06181000b60030800000d8050109516a00680140c2d0051604602e060304890030880544c21076411500080d081031100301001030601c4032441c00b100c04040766030312403401510b040b110072141200ca50001c401c101850743c011a9800110340242c0b000e100000320201084410f10003101d030340d41e2100620032070940d1800c03c0d00c040c20f5460004c4c0126040802d654a5400d0098441c001c12580208050100021800c21000e400105804418000c0c2004c7c1020228146d10710000034a6002c0d4a020600100b414410b01081000f400701820400801d001a00441d0140c802400305841071149030b804581e444c01c1c40d00c40e00c011650513076562802c0520784510340018080c064106483c5465114001c1000c10044429000301407144008141042e54a04064184080c0d50300c8544614504410000644400b0030074071012070303115940100d02ea49101000c501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 690538875 1250 690537625 690537641
    0x30a1109030a06020d0615080a090212011107060c020303010503060c0d060f090218060f0406050f1209030304030f0c020f0103021e04080307060f050103170a0309051006150c17090301 80
    0x11600c11600b4420601030298002c1858a890440610216480d03070074002000688003042c800003521038000440c0207440340d224288041c401411000f000c0c083d0001c0500f515092070b850705520b04009645000c200f21449858070b00c04050010394150341c504000240c441c0c000600111840c5000511041c11201c20f41c402e90182c90066080c00346a500c416407000290000d8481c00071a403030143c0c2c81800303841c0540c1540c3c0b03800c20b03000c81913141a04104084840b43c000140803034410070706005400f907070000050542c0c800e2220000440d00d81c40d040c240140410004089803040c0009004000c0140e11941ea180000c000e080c240513907240030180b050300c100c0d88142d100801c00800071038007140f8204040003c102a0780940d009014810312150171404844080c8401030610042038000199250f040740504009030250400044010080d110107080962090f035000429a494070140045d1309103000890f98400c9526100c1c0340d101c112741c0d40302c101689200441000000101d04402c0c80d580c00d4001c050 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 690540125 1250 690538875 690538879
    0x50c0304030f1b06050609090109050d0e1c06021e0a080420030f1c0810061119060209040c02031830370f1e0b041511030a1109 56
    0x100c3c4400c00e0802000400003035607458811000900420312040303050040d005082e82110140c140004010300507100031500640041c2c100a090b100c5c85821003600800b154040d003d4200580e5070b141c1c04001c5a20741d0040511502e2035030003840045880c6a0010803142c0c483e41c044418401010700c5441952030030b42d40001356a140c815100500c54410300410203082130f886001070080038915000b070584810304100c60245144290201c1045818800c042450034406004155126040c1e03100c05212403500b820010380d2180c1e000514400641002e04c1804503141151020314101003c3e07184180c0e401d904008c2007449041a800029850300311040030000000c2d40d80d68a41e0482e1800e55450344454070b0141ca900e10941c6aa01501c1515100c1084a040703003040c0c003007110414180c0e032403411000400c482a200c801c00031000460f8000d5a00c04040e21a0290302c800c0000e1800785060904080100c0404209900f0306800d800c13107510000540c0d400501c400f0f0041029a032030003400026008540c3d001d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 690541375 1250 690540125 690540167
    0x9020705011413021c0f0c140a0501050c150406060815060a093c1107050106080d140904020915120f060901180f1e050109050c0304030f 60
    0x16040160551050881c01002d005140d000d5654501910721140d000078065000603c40002c01c890b01501c002150708075110784c04000d400d83c0e01d44c403040307020141c40c1c1124544070000d0720318600030b2134290f01120040c002481c000d45002c11030400107491754020304513840040d2014000c18104001d54010401514403002242c60b03003195660b04cd010300078240c80e001c0c001d0301d1800c00032415000034061066007401c08150350000c16600500032456a48650102001c114440d200030074aa04d24000c03c45c05031008101b07a501c1d001c05051044c03c440036a80f0068a6912013004d8000721a042074000b481c00358021807041c4c1750b02140340410041c0c400c0404d0b00c0c1e8420502180090b00c4034104010f88503010f80011440903e94032a04800d0501d04156441c50f8403200700001008aa00b42d040044410080c014000c10308030740604040003950358441c014060a088082111002c0702240b08031070041164101c18025400d04119840b11440301502c06020007101a81d0415524010b4005e202300c0c5000c0d00000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 690542625 1250 690541375 690541387
    0xf121b0302090a0803070f080a02031e071a090606040b0d0b0f090d0c0b0f13020a0801050a0c05040b0703080702070b1303021c030f030c020a0c030606050411041d040c0902 75
    0xc000350b000c011110700c9007800c6000894001c0c000400c0d1038802e6800005d480908840703441d0a0440d8004800860440c48200400c5011a04840003400c03d80390580700369803641d04a14241c9080d0b08041e202038001c01c411340401c0841400040c3d000d0f00180c0540c0c0005205071860b003c034414102c200d80c00307400c40300d0305000d10052044420f0351510445100007540c0c881c0051900846da00040e800d00500684922004a00300007000401340340c000e034001c913140b1003560305940441c004160300d51122801e49d5540041040410403400341100c144401c1c80c015290070300386103c121403800b48120103810032000ca000070f100103008002200240080034201d45c0c95480303030f005c220304100c01c50004900540900c46d807000841e0071241110302c01c80d0f05440e043c0c2071885680c1d0440c01821580d10200841c4114071744074001ca2515a8010080c600545010402c02d0400b002d00c02a602402003426070716204003c00c222215080c2c1c0e80d040d44d048450303500c0c40a030310745040c00510032300319400c0741c06a00d10000d4a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 690543875 1250 690542625 690542627
    0x80a1701121406040308270d020d021b15031b0d0c020c10050d0b0f0d060f0506091e060301150b070201080f011d06030f030406020a110a060f121b 64
    0x24090594402c8044030355054401c0080c1e526900240c3c0c000b00030842c1d10001c61401441c84000c3e000403424a40e802c51080c01c1101000d140424201a94015030401c5100915940d410700c40da4041c860407001e10180b000010010603c41c6e1081c840d0704032142404004110030b4210110500380802402e488292201e0100000000420400d07816801610881102810390b003000b042d607002801007038407614141032016040300080e00100b20003550080c0c0b82203000301260b0341c070f07060349002d503005145c0054050041d4035560101d034405000d05105154030000c1188088102103410032401d8030074544403907510b1b0800404c0c050a01c024030a080130000da81c010407032120300d002401da414000d9960b0165510307040c4412104400a025001e007907a04104078100803985403c42a401c040b02070119001d8034980c41e900d5046402c682c00c01d20040e08000101400d100340015a00c003071030740840725048003a01c0c100020384100c4215060340c043c0451407111040c03001c001d50040601c03004250b2051842480610 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 690545125 1250 690543875 690543899
    0x50a081f031520180301090203030d140c070b060105490c23040b040801020a171017100c1101150803070305090a170106030b0a090b04080a1701 63
    0x103111444a0303e80078803140000800d2150b0001a0801c00145151121441c8041d00c0103010b078040700e8240d9201c15032900140c90410080c80380508000b40000c411400c049150030a41014081d015a60030078000307180451200e52040d0382112007402c0c0f4964804c0150240c0d0410307540010f0311040600c5040042c507040c03600150300342070311240364220640da401000e40e92084440680b003020000b055040c004100c1d401c5e240e130300c0801c1d520300300b2801d041690300c140d401c0c03090340103801c800301a940115107914815044085024402540c10000c419840c0010303181500390a41c0c0b00755040c405c4c04064442c035841d400c0c44903903480d048408007071114900c10200070708010400c2101044541ca450820080242a20940016100050055854004540c03012940c41d000704038180d9215005510000745014020422898500e400001098403859801c3c04042500b00030480801d00342040d0205002400e00442c043d0b0150f44031a040e51501c0c521501107840580c3e4083c08001d03200000004103060716400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 690546375 1250 690545125 690545153
    0x100b0f03040b061c1205091909051b09130f090606080f03130b0c16060908060a0204271b0305011e0806010905091906050f090607050a081f03 62
    0x504070340c883c50140290b2070600480c80103142a8501c0c03c2d800640340807000c01c00107800d4070307010f414010410001160700d4003081001046900411080101d900c242c0a11a800381c2d83c02c00503d180300d0000540900d501c1079108030761007600c130f01c3c40071580200a54024403100010302030402c203020651800ca402400c0f90700071058140300f0000003981c60f4100108030f4003500d08142030130a00718a48100300d00c25400c01c490f400c1180c003a105203846d198000500c41c00003807003581d41e5041600d1900407803c0c00e010010b0680b03100240100018050102071050021480041c12041d8011905000b80384c4010816188141c4200504000410189a05400982c11307142c800c0008111081c0c86c006000c0142070a220b900c02940000c4010440558594400d0742d10004420a40d40d11441342d513600c01d10703007615003421a98166070b1024011290121840e50b980102d0341001080982004000a41503004807081c0c40204144c640000b80c54a10102042106074010455034100c652031740f074020108030000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 690547625 1250 690546375 690546383
    0x308070c090204060c14070806130606060f0e010e010e090c1e070b160905040f022a19061b2303041e06090c0906060306080106050a050405100b0f0304 66
    0x15000716140d40d0300c1c03080f50125041e64070341554901d081d64030f81c0300c0803500703a100c0001030065040000b441d5000b030105c82c0c86072031101c01d030a0301103040c2d207000d40484074940c000800300440c09584000180d017150101644082c00d00b005900c040781803004030707110301c1c0310103079560800540030600c0400901940902400ea208a0040b0030b113183c2020210700501541c40003900032040380000c503486010358806414101c400d80380411005807543d0115060f43d00201c00fa10b2042e40c00680a80d17566001c3c4040c1c90f681945401d841e003200c001d014955512020f0080c6003028501c403a0b405c07410856668800100b200440c48000d9000d039541901804038040c0030390510020703802440241034000d105d000c03a842940e0283c0080c0788080001243c0c0603e080d0008101d5946549100130f00114400d244a813004040d2014041030140c105040241a20078680c0484000e03810002d040c0941e81e1044000410b0f14816600045c55543d00d8080b040700302d203c0c0d80b08280e401400120800f860b20400000c51181d801 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 690548875 1250 690547625 690547643
    0xf091407050405150f06070501020f070209011d180a0212030a0206010f1d18012405040c08010915051216171009060e01061202040c020d080a02070303060f030807 71
    0x1450061105440c0c1c02c84000c07500307413001034000400d45040166400c100070040e085608101441c1d031144e0882c0d10424032a40040c00100d181e104506d000000701d80904901d1008946040b034003091810035040142030b903030403046607242c040340e00d1008108512903560010311680c00f038a0070b003140755140d904c10f00180b001400f40750008114a0200324548040740c0b8004000001c2c0828078001e4142c09501078800603001c07034541180c03441e101c42401880d01c1109619027600c3c0141d56031400e000f82c4005948194011410035111041c800d40202c03805045a1034041d011503100c010920088007101e142c4c01c003e40c071450341860403c8450001403005804040302058442080e154100d0f400c103080e9a1420000700d41c00180280c40d060000d4010a0a05100c0c17003001c81c1e000207000342c05003503030030ba50003164080b410780c42e40c0025450300d8014030088240a002801c0054030440c0020480c44004040c0d00402c0e40001d8202c0806200354409401402941040298540c0300e03e072440346944090802d94810b01 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 690550125 1250 690548875 690548879
    0xc03230412030504030f030207050106170102090f192606190e030403020a0501230a0c030215040b072619290d08040306050430050a120f091407 63
    0x1000740f140134000c507050303121340008440c0c555044000c1d6011301c0007124195240c1c00c00050412030b13080b0860700142203100141c0c40e01c0801c01403060703d61044081c00e20880c043c04409010a110440001c15101e8503998541c5003900752078084250305003004003401a1140c0c4040044000d541000340110040701803007406450803042c821030fa240683c3c000a5032120744c81c002000150700412482c44501c0d45810342c50060b810b8485041c0b165040034104902148105209004041d41400041000e5214070b80c1d48616051135140c04040e200001c0084042c480108541c01c0300d00040c081540c107070312030b20141c17805903d48a514440e030b058100080304011824480ca007070600648814031604d1142e00c02c00040b03450841c1c1d0411013560360b0b80b07009480c0c2503000c0102001082060003203034420b50007030b13260014418180c3c519107100c80403020300c0104803903414004454168418101c50800410380b0f000c1e00e89203405006103004049411102014a01d010207100400000441d074a14001d00013081d070384032035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 690551375 1250 690550125 690550127
    0x41a07020118050303030a0209040e010f0209010306060c08070f050325030905040e06070305060a05131d071d0421020a0c0801020a120e1f05060f220c03230412 70
    0x1c041c060f407641500140b001403001001a0b0260114220062011030401498042582141c4014404070000c1d07170001102021943c0500641c00140101d141c200d40d440c00319240c48006004840740248250304990170041480703c200295020a20321000044038250070313003005505840100c1c411000300382031200029441c0f900d8170801981c0c55405010301a0b9a86102084006000003004a588003825035804600c0f500d484274030740314400c0740301c1000501d000110200c06082d2030b0300203102170310740c001101840080c0c81041d0403520034140b01c07100e59594481d85006031203c0480a601118403640101382030304070b9400100780c19400d004000300b01c06107403501d00f034034241c1c401e14607142e012407070450316408800d20344d511039003003800c3c46015650061488142221500d814a0001c1103e54036030040c010581b51450100414040884500c010b03021034441c0801240038a500c2d404206a482201700001c80c020f030025940d040c0a42101e0808901000305000600d40a030303800d0ba101e02e00011482038203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 690552625 1250 690551375 690551417
    0x1050106050f03061005040902070b150a080703060507050f180907091508090a0b07020d09080d090314100c020a03020c03150c030a02040506030709090c090315020a05041a070201 78
    0x35448800320b00b45569590800d00c0306022824009100300300e4204400038405460348041d003e00c62250401d1001c5050040c41c100782d00e204070030700700e11803202c5203420060344a0004008041380d50020010480790342e42441501c0a0103130b8203800002400015620420469000c003900c84102c040340d052580d51a421821a1580c0980c0500d000d6031146010102c001400350000c00d074008034000407180d503080c0319aa82652150180c0f0000096800342c90034141c13054102020300007a00d00c180003010300070780044008083c500c1521001d010241c80700854401400705101448a04846090a200c0c4005a040081d0b403400906000e40040c01105c204861038a070100f00007010a20480a49e0004d450300c402c0e5004c154030280c14886410b034200030004007034650343c018522401440e180c80d012907140400f08000d80d06158040c008029080b0b0040c0000780f890b00407415540032040006842c2c03401d410b0b00b80c0e4144660f03045040b6590306140b02822800b985401450134501c04e0381c9030054109441c030b8141c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 690553875 1250 690552625 690552637
    0xf0504120b22110d060b0301060e06030d1107050103020d0f06181436010c05042c2403010213090606110a020f0f12070305191e0507260105010605 64
    0xa600f0041840c48980c6022201140081e01607500050300490a800107400c440b01a400611801040070030801c81b860f081c0203c3e0100306840c2803051100e003541d02010b48070065401a5414550b0204080b500340c94940c1c40b211640703640d07490270040c245d214040490b030701d98a0201c03107442a081501501505142c80c11031805900b40d03101d0803808044000c110b2414800681c00008501619000161520401d001e41103901d483c50b207800303070707920b080945030401c8060340400b2385192061180c00d54800003400204680c44074070950f0303840d041c848a5410b541c2480d50201c00365450340c00440d01d225201c4c210300310b282c01c841d00c1e81c10800903030303654031402e5420340003403243c0d904150440e82c6804094107080d4040c0d81c20b514000c265007110900c640004050340300c480e040416650018905200f004010031003c00da95400603c2a85e010600e80d581400c210304a140114115003101c03420b8080120400503000501210900c5012032a0a0540c412641925512406141d800c000000a60034011411501 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 690555125 1250 690553875 690553883
    0x1806100c0308061c02090115021203060904112103090f0102010504020607110607080c0a060c02010b0d02190b030403021609050f06090709090513020a0e13030f0504120b22 75
    0xba56944031410071002c04005003e40c1050740d0916880b400603500c80d906c40d80a0300c1c3c603d041140544010100030701d0300150300700c0c1210ba21002c100b400304a558041d0720550050f8030205c1c0129116660001c070701031854071024071020744503240cbc12000d680c602101078075844d60151202510703410036100490a0324420703075001c0c2d0803002c2040414082a40140324031034911026040394541911945c1e00f04241e07119031444266a0008503c7c10100501c50084201140b00c40c40203120844280000407031540c5041c03c001c1c40b5420080e00c2d001045810390000c0d00508240300000d40320f18050501940f5940c80c080180301c19011740b080861840c18a00c542401650701d03810f42c501a5580f1010301401d4040a020320080c803003007000c0006c500f4400d008441c0329600041540a6481261060202c019602d400503600f00e070850f010071a4020380174003040c250680620b00055201c070a204269598440c0750400c80f2050304050070802400350380460303180511144400c3d451400403404140301900c0440d44010 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 690556375 1250 690555125 690555137
    0xf0602060916060c080f0f07030809070b191701120b0f070801050d151a0301060b0f0d090c170d0f0e03120903010b04050109050403030605010f2c1806100c03 69
    0xf10081d41316001d0020414440c2c100c10f03260580404030861244c110380b111000d00300d40019240105540114269000002d00005042d000d007001c0c4903207401d020b504080d00d000e228503035039400140e21400813400e84d04913041e0461108e58607080f0722110b20807450f009480c400c2c040800700300c1801c40440014819001507486403500d07400c0c1420002056490b0344261040e07a1410300c1c01450003074600c0381c800c42e10000c810012803052108241070a43d030450380302c0c0313010a009010300300c010321149048070001c4c0803811000400490360714190500302c0700742e0440000e00c00c0b0030410441e0b00c0400650358545440f01e840c0c1140707581860100702c074000c464500e050707015000206000c00300380c501800303444040703401000071030018046008030b82216800d0b40a4541580c6550520050580510038000505000c0c60082080300810b1005048440211310110003069141200000303801400034600140000a20103181411448101c410040041e12124800c400c05c50f40c0d0f4039280d004c0c50400718000e6040e02d0794 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 690557625 1250 690556375 690556379
    0x2090a39080a140a05040201030b030c130b06040e07030203150d080a2d05090f0f0a151b0f111c06020309120c0619230403180f0602060916 61
    0x4540e140740c080c1c110885039488208044489100c000181c0c030039210300b000001c00e07240900005007070380c8040c00c080340280c110008031000f85d1038040710241c1c814030242d80421a0300a40001c6140b42c03089910094002c002c020500030390b16495001540119803400e46044140701010030000440c5400c01d004103a29020407e950b0707694094200d000180001107a071502c0510131400241d04949149124000a54009036001446ca49001aa01054030a9881c0b91403002100d0208000031090300030309410007020400d03c5101481180f501c200e43c49104090304a5009516028118244450044440090034000c00100d070038000207054480550500840e00458a0344409001f58030180004a90707000d045240701034040740400600508441c00001c29035403a08466810030b0219507840d01084c107050407419042c803204288250385171106500c01e0780098449150554144500344210314005448060000d100c0b04410070550448034240c098812030359030f0022882e142e44a098441c80107100015007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 690558875 1250 690557625 690557627
    0x3030606071b0f0609060212040807052b0309170a030f030c0c0203030705150903040323010f05090303010807080a05061302030a0b040c06030608160510050702090a39 73
    0x20100300d1140c04000310940946829500c0c507403c485800400104895080c1081280d904024081142030b6400009060505003207806440d5150303481014400d120440c00c500d0b0f5900903201e10002c01069080e030b442c034001d441c0b6010b40300c1c1041e8440d6203c05191041c40c000c148801141220b002da605a503a900000c0029405130000c01c0f03d81030080400c04428031650068800b0401403500501480062031455410f50640c0d0915030000e2070b00032250024042000080c00e08580080f2200401c000d044482d4001054240102522800c181d0003909100c11300010b0803000c001581a5010941030b03601440d04c81c03400d1940e50a56400042999126a00142e03c100604c0071181c0190320050a07518060151b0312541180803086c0d400791a013418a5004102058040c4105401840d0500c0548821803044250504030845403094601403901c040e50740c01741900c030700101e80704154010101c01007800c006403160024161000d000711040d5000600d45a5200310320000b0680e03180c0004444110540814 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 690560125 1250 690558875 690558893
    0x20a061803060e1f020c160e040f06111306080601020a0f021003110703080708070f080703050a0618140a0608031b0c040e0f060c25050a06060b18030303060607 70
    0x40040c0c11405164070301c0400e000b144c2c2071a60b039a006090096211741c02084164104010030300168012440d59000b0008450350100c805d912540124008184640500740440500138140c19036040c1340c0c001a154081c80885144034054408982e2804d01d1990303080700590756094002000f4143d284280100700062802180f400d64000b01440c01040c0f084c00300b1940c0485410803041100814500810015500d0380240721961104841c981013640a200e00406805c90314007070000000c040d15540010030f0700069801c141c0c000c007103040180100001400e00310b4018544014000701100c0040c01142e00d04038a40070303040555002101130b41c135014090100031101045110103c101e03004034125591540e555110f1811609510400b820502c11101c142c68280440207201c0c035403180041c40071084403d0304000800c464107018010021784601414140e01d07000e01000014215403c1100124490042c000500381c039811100003602110580c8bc10540c4900040b0740c01a04543c042c400701011074007043d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 690561375 1250 690560125 690560141
    0x90102041a090f09010308040305011b050f0307020f0313060306050f151c050a0203060907080702101104170c010906020f0a06050402011101090302061902030103021f2a020a06180306 80
    0x81c40d18920386080f2000c03602c031400c03d80c02034075a07180103e010010310400f07000302200800403138803404600b082c4401c09013107402105007180214070003000150701c2074020031002c0407c041c0c03001260f0303d807d0074014131455071040d8043c00d40001c1c10244005014145031102a040200003411405c0000b640c084900c0c4036084a07041c00c6200d01400500844c11031644100341c080d54600c1030150780c83c902082803000d035690107085002000018000c205013542e002c06c0c1103c00858075000403509843d0486102d0041c0100d0300070140e070f40c40703800c1050320b100800038942d1440c0800ba00ca083c41c1640d962026030710b50f22070000c19030041d00301c041640d000412030f034001d40c3c1c080e105041c0b03004400321b035610807030071528038200403005607010300144030946859110185030003050460662942d8119408a031700d01080c10565680c03c424980318244070b5000e08000d038800f14100d4100c2a0320610076100354404070704c448050303010300d180b10004139403d4840ea00d1240d4805e010310709800c0c4186980d642500030b0100d2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 690562625 1250 690561375 690561379
    0x3080d0e011b0c1b09021e1c1d060901060305010b0904080f0a050403050d020619061d0604110304060c09060314130206190302040f0b03090a1101020c120d08090102041a09 75
    0x1390941c40700314003010410034050096594010f0310b485402500c460022203521030009020001e010b001c0320104203441540504007014404183c4a081010b40c4102c2c404807850218203000b243c2c00c000340c110b4154405800c480c01900284140e10403c8180110041e0555000d01403200800c041c0b00000008401051000c1140c0b41003840c040e502e0711141e007044030042d01500160407000070320603034004100c41030680044000041025600e0015020ba110300f040100100e0209c1640000f40581d455900407035410a044e140c099484c501480c040d00140b0f080350411000c07614040303000c2034591003803180c1d49034400201c6640340161960300c0f43d41218801c1c2201260b00803404c01480100110503041c144140950303450250710b0b41cac01c140c02d8080032004c1ba082058048030601c00c02521180010785680328070707001000710a03c0f201c0c1800403400c10030080300d0180c0100004500728610200050039050754501c50791846266201c0007a1307107080c1d10031072180c003409600d002494482036040342e000b010243c2d80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 690563875 1250 690562625 690562643
    0x21906050f090a0f06050a030c02160603050408041205060108010c051801111e030a021009020a15050d0606050910030b010e19030c0b04030c0e0601080a05041a0103080d0e011b0c 78
    0x90342d1300e43c2c0002000e0307401680014801180601e1800c0d05402854100039550015181285969810b9a005003c602c00d41c410103840e80d0119040c4030406c411078000c0c0a04e00c43c61700800b000b50800c1503844000b0f1182d0320f400d62038400113110300c0e4401d80503104100c01054002c00f41c0c56040b0700441d07459604005010780c900900c081c015010081890205515812201950f20345891040107420084140324511440d400c29407204010fa0761040d0340e906171107446203c0113200903085811162409203840200c521450070502240c0903802501404a00c00d0444159109009000d0220256205214024045003101c0f010812924204480d01203880681d01c441042650b203454558296803a540840c904020000c0d0030f0003441009480603000d40344074003006000b401c3c0071000800f4458010030b24405103075180e011a0410040ca540d010210a0008034240e0a5859003006407840c0c0c1f0108050b4039039442d2000d0075103102c0041c05807800303015014420420b49409050300f5500c00c02101000c680100c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 690565125 1250 690563875 690563879
    0xf1e02030d05090c01030b061303080c1c0c0b0c0c1506010512011203090b120f0703060902073e040507030b031c17010819150612021906050f090a 64
    0xc954400d02c0d2280d0014030003054109074580000d01114081c0c484140510001c201001800300711100345412640d0041c0c48998800e151000241084100340d00b502400c1010000c0d0154194404c6100720b00342d0058401e200107032104000310b18244100e136038400c40c54210a04888500305202082507000c3c1c41810101e103005880000c00c00da0410036007007200034441c0040820f0505900c000002c01500401c0d0481c1e2038420103003e40940c161004080740c20344940d031400118031a10039080b400051000b440195201c62452034542c01048054003000900542805c216540801104856140d0410a2040b520160030703074051001900000700403038103041c0c4903080e4a440340c50030860b5a0000000400e1003506800750b0702d000b00740445400b140c2d0040e402510040c0305008000c90551102144141e0500d60510540f62030310400309000b9150714140d24005c80040c0c03944400b140f4040091003143c00f083c290103074607004040016103004030170020300d042c403841110440c81e0f4000c00801ba002881070b4840303a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 690566375 1250 690565125 690565147
    0x61d0105010e0d061d150a0207020a030b040317090d121a04051b040b030a0e0d080c0a11011e141302060d0b03061e06040903050901030c050c07080313060f1e0203 71
    0x407014240174154004441402540c00d0303d6110303a002031291030150319000c001d40024441964078000501b100c491038001c54101805802604028081c101c05000d49290250700a52280c0c43d2450300d80114080703001d400c0884c3c11030b200d032043c0418040d1003054075002290a000007082c000b846c5400300c40a08e108000340d8002200034000a1801c001910360301e1505c00a880f00307480312035920300090b90280501d004040c0d0805d103020f6000001c1c8080742c0e1502d44850342150f030303011201000b0318154a412241030074040c140e0740000301c0c081008010311041000d100704106120341280c0c1c10001150300c421450051400c0703001000c1d81902c1c40b401080110001c4c0c006070078484180c403800203442e000c9002c0d41040000d00c040903440b4000715000c00c03140a07151405002486522038007030415544185122080b80503105542c100b482c0c020441d2622502c401c541d40e036a5000690508070804114400580705220311183c03402404035942d0752440c1f4035036011651207003a0341da03001b101354082404011001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 690567625 1250 690566375 690566411
    0x2160206040f0519050a030f030521010807120b01050f192304090308010303030e0a140703053d140a1b0306050108061c080d061d0105010e0d06 63
    0x60701c460700c03408600924043c1041400d808210741e0241c2998804410821035941542200840e0740003008110701550910741110030340b0594207242c001402030380241a01040488200341a54514001c43d40c16a4445020318281248410010492050440180300e20300b411000ca514880c400b501d03454800322036048498604070740e90801d61032079400f042110104510505550b03c1824295410800c0d5201c0303460007401c45005000280505441d00700102c9180010032032443c05580001031805006503544080d911089a844207892a200d6000c507200e1080c2214030329060b108a07040784071b0358002400c5200c8070f00b111800ca40381d071840c0c0e11f07030000108801c86100d4a00c98108907400145030500c5802d4031589001e60b808209c20589442020301050340c224160907000001180c1000344402d01490844844941d44001483c0c52004180c0f9104102030b038101006071506080d80c80107002ea09110100800024443c03240051804136042d03100c0d00305080070001e010b00440c4045860300c400c035420008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 690568875 1250 690567625 690567629
    0x101d0609100f0b1e0616050307050105100f12260d1506091a070f0b0a0c030504080339040905010f03031e0203121302040b090601080a0216020604 64
    0x5074000045811011800788281200045100010400d50403020003107100032a41280c01c803914441c42051500d00e984920a607001d8000700c442e40c2943d401c440c5042c035141e8014140c1240c441d801c11002c210030041c0b0040d81e80139903005a1100c00203500d854008000c04014030016202c4804e401c0584141c81c40802160b100c203001c04c0c403456540c0754444d0302c01048030b0010f90504840b0000b14404d00141d5808510341c030071241000c6c154148502507058000d01407080e0a001090720031107115102c2000640030446200302003406041080711601d41007030f400e0769030441c1e004210410400c000f583d1140031400c030340000c44c65042e14010003e4203841e014a04520101740c0e416112011504001e0380450740503140c00341c8400341405c2103180c80c0d5a8058040741e078030681c01112100c01c0310004002d520030015204940d5412006800d181488010400e0940d030042042c3d015a003044082262400d00000040c0a400c044e03484400d280e81c0c5005000094214400e92245010318952103405a0360302c1002e800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 690570125 1250 690568875 690568891
    0x1f0f050702100309050c09040b1803040e041101110105091c030f0e160603022701050c0613021e090703020d060b04170c1518060f030f010620101d06 65
    0x1440c5095400c1c171520300728003426024410300c0c0d54010800000c001071340a54002c4070a19480d03141c0c0500c68541d505600850f0000000d0030003020400003800132000450010410a80343c40701c24202509401742130311400c44001855034000b0004e000494140e41140600035800d01e4000f502009034210201034522200710012a513020328103048842c02c0549941d0000d1840d400d0443c609203111039080040ba5000c007000081f034100c822448400d0f4015403c55141541c640b080d82c4c00ba06d0422910041c91040000682c0100c400311002a24001c88040e00e030403c003030041076402c807582c80700b404070040d50020b0007880310076407110f400044030754140740500041d2800c1304640000c1c0780c2d000403161800400c69801c0340315260404d01c1f451420308400869000c05c001440d07841d0345400210100e10284281040311100e01000002c10000082d50312515050362042c1c0c0d90303c0c0003100c60402c6011507258003004032445411120b80c880880206a01c0542c0d40d00c1c1e014418008180310901890900000300c1e4201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 690571375 1250 690570125 690570131
    0x80706110325050901020c0904050f06010801091704120b0c0c0a0305180d080a2d020a02011e0909050a09020429030a03050f1b1603111f0f0507021003 66
    0x41440311182e000328188608500d070140c24607a003000000c1d625541c50b03a840b030155034404089801d204050241d1008020504200c41031541c0d40ca00c4030703000f80f400302c90946210168050858400e441c005c04c0728121007200c0e40e0718100e1000c0380c0b20310319083c4028044044d4a101000f081c00d00c1d50341440100102d0340a41c0360303651a510750315001d080a840f222451480707040c442e40308000140604090325402e8a680c5081c0e81080880321310509109a4005106007142100750303074000700c66000400341c001324402e0380d82011801c0c0084032000c00449400d5201d011036003158052000301c02a6120b07550141700c0b8500401c0c04030468000c10304a0315030101094020720341c080c000105828410003d941000d0a0740101903042590320020024060310071400c228034030018140c00056514a00c080307810b40ca182c1580e101154108020010054a1004a68404890050044918014181400144002c8070800c0f01e8085000b0450342c03480108240b1027403010a00c00d02d40987c41d010550620602562000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 690572625 1250 690571375 690571411
    0x4030f03181e0c05090c0f0c030c070b03180f07090b151803061015030c020a020310020d0b030610030f17040e0411030606010905090c040e0a0b1216030807061103 71
    0xd0400010743c0c0e0051030145d03045109210842036140c003110240502180307455121b820010085096200d0611090180d01c1a00004210048440300840c010140404800c4614160007846500c41c0c04a11350f03441640c010030001c10456000d500626030208004001008020151000718103607088100c1c1c60900401c0202d03d441c1509041000ba90000b1004520303a01140c9012082c0e035450024014440400d9210400d4000b19030003042002e54442c0d00405030340d0300c1c2460200e80350082d00a204031510710b506242e2121007904011666074040c0d540e500c0901412415070300c5440c3e10300d840040448104220304215035103080700b100504041e0007030b60071041c883e04042c1021448400343c9241a40309030042002c0c05240c6ea004120b00e0226007060310715600595460302d08d001c440c041c660144031244100c0c0e04100800c4101c1d4005d00f2100012141d6185910742c50100507030382c841007003001c03c8240815400340046040f8002410a03148554070100d028141e43c000b00c10b503604142d440c400c804242c580c407 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 690573875 1250 690572625 690572633
    0x71701050103020a050d121b050d020a051c09051215280209011b14030d0f05130c140a1206020c0709051504180515010312030504030f03181e 62
    0x68010b040480303c280310211540c032841008100c6a198109018a450321421005200c80544034500c0e000400d4400c1401580002f03902d8011080007200c0318051001c0c0711103201421041781c22104060342c0c801c5101820082030081003075009000140c5480f030f1800c05c04c044040c1047c2140300d820105840d44a94908000d0302d406081c0b007800e0301c0c5411340140101c441d6079a003c02000440d0141605600d500c0b506400d200b0307058440300c400c02d10240000202d0840040058100703140f82e49810300b0400807030707803030300000f260300d0f50400c80040415035201420070070010000c99031403203264000c00e14080300e540c610070754403512443c1c00119580e039004155003902c075505000340001050311002c02c4c411458508411400300f01c2000450b4815a034500e800c989600300c001d00401c480f50b100b421541e84580b40308216030002c03002d1008441d5140c0541c2c803045024400e00a0034011545903d07918201c0c090008c0940103003008007015804c0c00c0112a24801040c1090a000c9245203020100f004401071410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 690575125 1250 690573875 690573889
    0xc05041b11060112081c0203070c020f030706020d050325091e050f13020904090c05090a0903050706090816112706060319020a030b0916021c0207170105010302 70
    0x10140c10182c00180040142040c0c0e02480d0341a598802001d40d62500b10546070310440582260302c40b4442e02c0407081003041600800501046402100e880c400040c01004055440186000e05001030f0408940000146d004d440995008000b800751000c1620a6842d010801010744001a00065500c0010490115480440b0751040a419100c080340c6050a01141c0d00d050503a00785c40c0541d074074801644240c0203031b60554000700002001804a0300f00e60508403e203451a0040318231400300c034804510400e4031403043c6102daa03890b840301e900782003054856000400a00c2d9081c3c51500042220021703d0038810464a2158850020340b5000c031003000a0200030084403200c1400a15080444000d8102d901c20440d0711050456045a80346d585184e0842440001c8410000417800440c00c86034481d0145c0214020360000ea030042c206075903142009c1325a030803035600d074070140c0c1113015000341d443d079190030f8001420280e00490348a60b5450060360140744080c0515041659154014021454842 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 690576375 1250 690575125 690575147
    0x110408030f13080d0c0206030717011811070b040f0f0b0a1a0a0b0712050f0f030703140f0f04061104080115060207060f080403031d1b12030a05070c05041b 68
    0x200411390703114048400b410301608698040d2060740c02000046a0700c2c482c102e21000d2035040d1041c1c0f512540e44d06d03066074400e5042c8520041090400320704181c0900d000301500c2071290400704100160300d56403600c00f0403001c01c0d401981c02240710804030001c202e10b45032882c0500361968001031f826980a040003450b02628000d18400d0f069810100030f09001c803c2074605260304849564101112004107866138820b101c140c540f4603801140c0305030424a41ca02845c42401315440030b20180101c07440c200c02e03540e4100c0c1d8140d81049264042030008c1c6501402300d82c005d00c550302c0041c40740c24100c1c0c084640c0d0032551084c4d03800c2c1c3d1036810841340300065488a500400c0180002c0c03d0b454101000a40310310500c20000341003141035130000b400d00d80700750018a801011142e0300d542c060802e00c800c58440b403280300b40c1030420010f100e480d8004d040482801121606901c055030400d00e14110031202c1d64041242554400c680d85c03004640742d076aa21514110300c41050400c0302c011128100540321807010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 690577625 1250 690576375 690576389
    0x6110c03070b0904020c010615080f090c0a0e06041d0106080c0f0102030324090103060203062d0f240919030302070b0d0e0d053a110408030f13 63
    0x3038074104441a600002e5650840c001c580150b1180c01b044045401040940c0c00b407294904502c680c00403103500061560300901035208039404980d11024059928080810020b400c00c40306c00007000b04400354070203030307401010040010032807001741e0010040d03040071828406090b03552038104012a6074108140c90301e6074410345030440c248580c0d400203512800020311044d000381c070304a01441140b84100401080600091069900c0c0d42c4908100d0000d400032501c07507000703040c0300840034401c0c80c0744a660005550310300344410352640c3c14400e11850482407001c0319000103024038084840e14100e0004c1004541600400303407182030045c00c0115100140c1c080105560b0245028804250701040340d00036031702d00114440ea25034500c1c0c00305c0024402d100714000729000b00207030b0940580c1d10000030510580c1c0900c44e004070030b620300c80c4468920016844511001140502d8012030105508100304080500900d2420a81d40e01e203c00d003194030102000c0d8480c00c000803500c0720007200c0f0990401800c25 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 690578875 1250 690577625 690577633
    0x1603200106050f04051909020303121e0105010804120f0e03010207050a290129031e010519172802130614012106080f01050c270d020a06110c03 63
    0x2c1010302c06259050701b42c94000341c0391158045015901c1c01c004440c004469440517100720705d80600d0450400802d0310076004103941c1c42000007600c3d8801c3c1441e5003da41c2050424042180005003950f890004580210521034050403501046d6000e00c05009524080e50140c64000c65528010a02c0c1140d40b010682c1c09001036044060040c40c012860f0564520211100d550520306801e1480060b030721140c2d9103000c20000412071032024014003070001814101c0b40030b6141e62500208403008488000d011403e0242d0384080041140c0780145c0404011034070b00380c07807000d45031000ca01d0701508010440041040c4070303041c0c0300450400da8020083c041960f00100840d9050070303005920008a001c2c820f0401c0240d03441410741641c494060400b410700f08004022959440d41002e48640d140d0341814402e51a120015001001d2001242c0c2095842d0a40c8079001244d12a07118500120312905030300540b454407660300503240c982002015201eaa01c03901302c2000c030f01041510303011081510314000c0d00 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 690580125 1250 690578875 690578881
    0x1090c0c080d0c0e09010308130e07020d030b0609040501150e0609010e0105090f101116030507030b04060e01020d0203220b150303070203010c030b10141603200106050f0405 76
    0x49441070b10745a0300d5003280401c010300d030120700300c448001d41d05405910100c684000002c1202038030090200214a240c8000500d55405001040074030850351480560032512070001c2c11442075000d51418580200191f04142d40c030008501203410036041140042a4a032444408175006880a002086c0403640c191410161a000038003101003004880d050000109840c000c5c2d6a462401025424016089000000c89184000c10300f11001e2002142402500d810080c5a604201ca48003500e23044801080214510368408082071001001950120b68481401e000d140e403e000403d0229100280940c0f01d0400b601e043d40703034152a100c00c001e41d040045402c4005040510701550000070182034410070781010300440c0c2113210740c8500a615501e401c003e02d02150f05a44841c581d2101a1072040d03c9080015003038403030200c908443c2102030307420700c2400c000d040c0441c4418015446854080c01844000f040304410855800d542002030751280024000e80c24005440c4801c04400c48040c0040e00f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 690581375 1250 690580125 690580133
    0x1103030408070b1914010906061404030b060d05030a020705010f032d0f0f060e0c03041505060105040323011b0c0212010920040506040632031501090c0c 67
    0x101c0b445400410310028080040c4145404100b00000d08610030424850640089007415505009018002900340750101c04190136211340540114891a144014a89810341d1030760440ca0714000c1244d5032000004196a001a2062026100011f22074005280c140d00348000508040007070194041014601540000c4c0c1451403007072400701041d079162003400d16205050b4040134003040505004451b08040030070054801d00d6104004851204c2c1c55103410381c4842d45c00d8038480c8415a00a488286601003010402d0010307448250000414100f00349856a25602e180581070740c500c01132040b0140d4561401100300c28080da44100044a413140d2800c0300c8240c0c050648540c420010340165141c078007014182500354040c40002d500488025000d15101d40d450305400e2041140074019800c1c0b80101d140340c1002d025841c1a24141c101c0b58684a0f074a80c1100b400780748450300907e41d164845000015620b040c84594842d0b8810b517802c03001d542c10100d001003034680710140c0038100008007407284085 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 690582625 1250 690581375 690581377
    0x15091b080c03070c0311030c0c040b03011803030510030b040f0201020c1c2604150e0102070e06010c05101109040506100c0807030905040218040b010207061409120f010c1103030408 79
    0x300785242013400c184e9499060880d840c00b0000071254280c800020a0b44100000103104c240000040303505105a4100c0c0c3c1c00c0c5400da44441e0712144e01081c040403a0b20009019070005940069204042c1c160f040c0d582d00c1d845102801924251030b884c51000010341035581c103103c0b004c10504145c903100900060112003203e1003450820161190b0a0b00d05030500100741e030950301e9a000340400070b40340c0710fa03194250b00310604140a07044002c6140300411710000c0d400441c10030100c0e404484000280d40c0c8900c0191000071220108484038000c0c00985004603040d072068039405103520380703d152a4000712003800206e0348083c14461180c0c1250300400b051b03940c000144503215034040c40f030340e0326000b9516003a50301c0d0129401469200b40046480d4500c1c00340c1c5181c445000d00210f030300b4009810780c0c0c001a601d0360301c1c5001d00800111640c182500c0300000038003c191041c40502807403804219030a03c0b900b81089040c0704540e6075180c46012020907404959000150031300301c06036185040564603031142e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 690583875 1250 690582625 690582631
    0x20c03072d0e06103c03050c030610030e0601082104030f12020a1403091302090108070e01090306050109020c0c0102060f04030305060f0306040b01060207120507031515091b080c03 79
    0x118030300704001300742500c1c822070841c10800620a680151400701009a86201e012007420b80790102614605140e6280301c5e014150007609541c0344a841d58441c48140441c40e5070b20f210850501da00c510310521303d020104a418020044035001e0285c0f140100b0810441440046040015076001e000600c0494420785140320800e0b44105c1c0c054408010030301c01da041210011002e089a003e000500c0210600440145080304003194141401501400c60760228001d14481c140054000c80000e5405402041c1036001920305062a2650a54a9039000140c0700c09800c80b83c881070700030a54990300e00c2d0800c20f5000601c1e09002030205841c1c40060030014184c0180090300301901d81c1c0101c2c070151102ccc1c00b40700c0902c1001e000d4079504e1400b41480c044540d8288600f00051140700e20020b55802c601c4c810f41d20840d8000060a00726156030ae800d100008000350240009640b20101d04815a41c8203949000b02217080d004910318648026040101d4070703101e07a83e018042e0100030026500c88400c2260342c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 690585125 1250 690583875 690583879
    0xc060a02190c03150b1009083c0106030c0b160305030a090b090d02060a06080a0807050c04020703090801050a02070b0a0e070504240807030209070807020c03072d0e06 73
    0x8000103182845000b900e00c0307900141110110388400ea043c40c506410865140d081519000c3c0d01d0315040b10116040c503e1482442000d07003055040004e1480c0074074129031aa1801182c60b85032100403018803610358191900b80c9c206a5540f00c0c10001c00900c02000401004003031007281c14640c0401141c0d45507401c90380010208180000040e05010a6a100703800d0300340c0107204d103c020b140c0300280350b0b0b607050408d40900252003110300107035503c507c9001e030030203a40301d120185c608101180c0d19514650060074048407503000380c0d01c404e860f603161071000c1c01c0204d00a54070040c0701703403624280c40c2c00c440c2d002e0315480009004010b0240130501c038480c01a084030364008001058000d40702038900f400e403035400c52503200341009205420302d0f44a896401c83c2d80072200d140d003205641e0b411013540d69005488029005a04000000d8159001d03103000ca40c007402c540156201c00f15984002810001e40c1d0b0080c1c842e4140340030418084801d207001480d80d8950a41a0011003814840e241d8141030340106003038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 690586375 1250 690585125 690585163
    0x204030c0605030a0216060609152405040e070c0c091103151f050414030a0f111206100e01140a030228030c061112030a200c0f0c060a02 60
    0xd000c408158111046c9800d8080d00e5802c580c1980740c030202802c03032403207240d10850030108482804207140d0030140c1140d07a883c050880c2040004845034429400001034014400700740000120b4001341c1140030b101c1e040726039861610030500c0c50521030043d144d170030480303407a071428500c0101044e103841143d8115400c0c800800040000c24001040c165100038010500f628081c401005607820038003500650700707010345d180002018003003030568039550300c8805018822100c1d8500c01080004000007601540641001ca00700700708030529142c00c1c01540c09240be2036091104100280028040f41c2c003403e03042c00d0345082c0359803080c0001c42003885400043e12550750064103800302d6111345541c0748a0003014039a41d003420f550703040c54140d210300c6104140209200c1e41040b2070f02000841c242d082c24000380310b080d007140c980c10f16010040204141410240158900064241e01820064500e2802c4400103154150200c000141840021540b40740540400c0c08180075040e000304240318240070380b00c412 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 690587625 1250 690586375 690586381
    0xb091e012306040e06011412061918050402011211030402040207080c120a030b1509130f0e0a0b0108030a0507110303070f060207020f010f09060302310906050a0b0a030c020c10021f0204030c060503 86
    0x81109100725620090606010002c1c401c2c1c0300bc110340109104034001d13216003088082c0c0c004c91505590706a030194581d1041000010010328155020f000c0d10742c014940310b41071130703c0f07034210510b000c03000c00520760302c03000114142c0101989402603440021043c1d40c90800d03135400d000c0d800580c2c042c10685d580308840104020002802c81e512441e42d0f134149284c1400710861035044540c6541002d1000d030780e1000c07448008181c003c4004116161600d5541e01d10385819140d4a88003404000740740b000d58140001c000e244041900d4507840d0120341e00410005039116214030405c003004200e20388040c14842001c03100c003441508a01c19800300c88135410096503901035140d136980c01c0c945241c80d928031074800b9803080080b04035551511095581510b4200301c600d44a80400c042e814103445036024030f0604018042307440f88650080000410035004869594a100b0002803c441c003c20840005901c1018a00100b0b10382c441011000b00c070000701186040d0850325414503070180c50040d43c050000c00804 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 690588875 1250 690587625 690587659
    0x160908150c0f040b131d0a0e101e06090c02060612210c0c032811060408070e07030b0f100c0614060315060a031b08030c010b091e012306040e0601141206 67
    0x541d000360352400340810207030030350a0400300c80449842c1d880e20309506d030420104003038441d8400d5400d80dc9840e00106180c1e90768004012015014503000f4015002d2074801554422441488422500c9450344891321480c84100d00d03442e0512030a0b6562183d0300c40315043c002c0206003142c02418103104e0040755881d00e9a814085403580c10007410507000707080001d00262000d004180141601d03604c40e0b05120b01e072180c09003241918800390305a6400f003110410442945410201c01100f8030542c209005005003513244c21003140c02e255035081a11030300c0010030405103002d100c1291118400403100c03629007440300c0890f0220086010043c01d1403c448130400c82d019941c4403d000400d43d40003141d82d1070b941700700164043c103007600ca0140a0965500451040030f43e400c41e0301100d11200181c0c4c0c186a290400b614405000c4042c0888d11908200310004180c466030010805407000d06041a0740381448000100582d10440807495980d42c00c0c0070303040154202d20589500b03d84200c81e440f10451222030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 690590125 1250 690588875 690588883
    0x109021201090b090f0309040207060b120703120306120f02010e03060a060807270c0509030304142b080306030c0907020105160908150c0f040b131d0a0e 67
    0x1020350301a424144403982400c0c1500658026407060b0424421502c403901c550f41e0721300010720107400d5908240040450742c10719601605d9814011080450710751000e038081040f0a08150b082003054204400034030500c124003000c5010300c526803070304001061521821407420381e00321200070003411407100124190380c0b25220004800304024162176490030a04808401071080d803003400f805016442c1c000800e030750004890103207040e030701c42c40400074664a0060320040c03c00000741000d007c4140100441d940701040540054020003000304140c10002c0100a0f200d184c01904600d07180300b80c0241e460044292954883d442c0d40402e240d9200d444400009003400850707400309420a450004200180358150815030150750140c130340311038910304848100d400907010302440c002540b11000300300f80458200c040c40d80c4001c110b4030b05818100d1294020711142d00c00d078400d503804200440c80400c4080c1650a40006010148071303240d841009040c001494180200381010890391019900c00c1040184 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 690591375 1250 690590125 690590141
    0x501020a1707022701061d190e09010e0f010209062b05040803070f030908090114040801061508010603020c0d0815040f0621020a03022809050103031d13050901 70
    0x2003154020110402032040c003030f01d000310344000e102c6880000056847c040c14594182c00301031455140b016000400380044403901c40c110b82c04080301c0761340014800c059040c4950080248400108500d010482d00b2440c1100d0340c8100640382e40304210780c0340350b40e54030011900800d1003150920020f2842d100c40e103602c0141c011051003007d003844100010042c00000440c41640c0c3c0342c4078880343d040b2056044046603072064004200e08000c000401c407641c0281800c1c1c9a02d0700c080d950f41c1c901510703400d40c00d00b940c005a122111441200030a045296000540300380501068a011420545e02c10315450340c90300c00700030601c1400040c10220316403d0400e80044503e450190040c060245069100d10042c40c2503c42d50352100e56881480c02807a40a1400c0c215054005084088050540e0208200560001941c0f08104480420451070004041202d0010720200c02c001440b0741c074500b00030b004203e8170304d0340350714004400540e155107036540e00002041c1a01c2c03440009984d6a09034020b0b00400d00d007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 690592625 1250 690591375 690591379
    0x6080912031003030306080c0d060b060405061c060b0c0d180306091a0c0903060406020f28080c0a08070e011103040806100e0601051207121d0706090501020a170702 72
    0x20800c4440e050010342c541c12030703110b60f90800505a450300301503115032214140903400011040303a00c1c00f0514a030001000070350000c101501e441d5a0301c000548650250342841c3d05190b069040040034003543c41440f00500c80071005034500081001100d803141400c0355401e05008820a2020903440d00140c104051540008100400882ea090203007000e00c5680c1940f410000002c001104020154107072210020054020b01780b03030310741d40e40795070294104000c1c5a890030810b000354042030070310500440d02c0410720301004d10f070013908003001001110000d2501802c408200000d0072a0fa43c84604d1a50140b071529126040c10700704e80040f5010300c00c01c8a003c110b44400f00e404034802e0b901050290060015104030307100d140d030f00d40b200c02c50144212101c41c08030324103010b10442c06410341445540038005240000b461505e0000390012200c043c262000030710410820745500340800c1000d800035101c0c41c202400041e103400c3c0001d6407441462801064202680c3d09a41010701c5a000e840e45a540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 690593875 1250 690592625 690592627
    0x6060a0c05120307030e01051b18060d02030c040905010902090a090b010909020a0306090506180c031e07080106080717190f1803020d031a090415140907060905090106080912 76
    0x5400000c001d070506c00100d44a6501e01408241c0403000980da41008450b100d407154102200b0740d40104a10030145020303500300008100740c45880c071540c4000c510030004a801203407034030708081242089a0058102d8010030f8070401c0380e0059660b600e003e4904549003000e01103640c038000c00040b14201c071540e00000032180041035030050285c164108505692014a080001da91740004210700d000c1500260320401d083d80c03012403044805031004542c030800040d080c0144001d604543d84001104840c0c1d180001c10400041c072900e54081043c540010861030001c0c50b082010520204061025040d07155101c0100215082819960814000c5080e0204104101d0005040380c0d13090b48080003088006024807880390700164000d114100c52a004541c0a001400301142404010100500300340d0300c00009102841590049003e90f84e030140f810b1a0072001401e200032107900c2c0c0038240e004507060085500c03007481075840f02c1440c941110050300d840c4110380c403540560383c1000c8001c11025100f0300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 690595125 1250 690593875 690593881
    0xa030f090305091801051302090a18050f010e040c060e030c0d051b0102030406051206040e06101404060605121e0f01030b0708090606011d03010f0902040b010806060a0c051203 77
    0xe006809010030642c2941d6855868041540001c040f1101b401010382c802495610070a9010043e4094001d00e00c010301282c50554680c80408000b000c0603c5c4150344507221000c2101608150b6201070040a2107901c801540c1443d070303100c00910056009980402c0451500c42000c0d41e0b0800c110401280090b040f4808074070325050560719100c10b00c0f0200d00c003070040c003085d0707500c2d506c000102d07030864542d5a2444c0c1070001886407100b01800180100d68483d071265490075078080300340329841c042c0c4100902081414509000007200810444240d80b00e41d01d030540420049401004a490505103000303502c02990b559404014464030212600c20403103403100c10040406413a07500300b0f040e64044c020201169480d04000c03102031354201c0d0040c0b03041d0400f4000c540554001c01c0300402c031280700a081100c00c500d03c1c01113400c455080d1808048261245d52500950404d446041d40d0310000b880e0203a01440d100d00403036500d01c0b82c10880d0040100d00015013050090502c0180200e030a01901181d03241 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 690596375 1250 690595125 690595127
    0x1512180b090709020d060503010b030307020d060e0a0213020a0206060a050a14130c0804061401060c0210021c02031b010b01023406120e0715390308150906060a030f0903 74
    0x6800c0c0500350027036103440e07403441d41407800105840c0150303401411a0100100b607582d40002d00216003c0f1360741440313030609440040e604d440c0c00c1102807040ca04010307201d94444100078070700a40034024a0080c208440d0510194403440a40401e840800c0d0252141403200000b1424002880e00042c480c84d00d48041c00c50b116520103d068056070003a281404003210030030030200315550a204440c04590f2a9107198010f00701100c04020051050064800b81c4441100d80c0c0c131030b000035000b4800181c00010f183c01e581116600070a200c0c107822002045840e0000c40045c1d42c62000482c110380225a81101959404c10300b88510818003405080c3e117001940ca80c0003912004500e600c00703586504042c41850b0740c03500001d03080102d59101101004058580c80e044d40e21501600000b148422031620f01180c041c207600540c281d0340d01c481c2d00e0307844a04190500a10740c09011300001e2000c000300803034a00e02e5a4070b8031841c0d0001c400315107059503407990f210250b00802900d0980200c250604468100341 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 690597625 1250 690596375 690596381
    0x1002040f031b050f040e010b09071e090e15061903050103110f0d02011b0624060f080a0b0109031a0a0c03020705030319060e011512180b090709020d 65
    0x4074482c008040d03140074408602000c0d02228090250000e1103180c1503001c6160540056201030200d10000540b0b6a408011440b0960200c4501c4040b90b20031400200d58a45800c1e40700c0900101e140c10000c2604010341c2d05040b500c00790901002c40480b0224058907500c02c0100c800d8a03c0c8065041001c12884a01402030442440b09442c5009004110b4a641c2000a0303026a12030700101050020344d810f80c015101111820500d40742d07071907607940d2100040d0441c812249044808500d10700310007101801c0b440c460910750040c80030084004256081c0796008805c1c140c100500950200e0500140c0c001240c0300c00059102070100000c0c0d034905003070f011050600900400b007000c01400340000f0710405400381e10550000418a40c4100700007020007059071140884503940c880041451a0b48100c0c51f0348480c0d081c3c01841c0c18450600c083c24003141c02c4950340c00c000983d20b40610000340b04080c500c06280641074007a21121956000030403d400500000b00500040c0d0411500c50046100800c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 690598875 1250 690597625 690597629
    0x30b18060a1b0f0f200f07180b10080c0d060e1806010501020d050d110304080a2c0d15020d020405010210050609130302031204030509010f111e1002040f 67
    0x1a01c10310035003006842d0720442c4050f150140b26202d003002c0d0510107108079055030b060908490341c8a00094210b01c103400902840c9120500d0a008021080c10460164860300c5185ca90301020f62921b49034802c80d803030b071009140f2001150f0802c012140c0c0d0701356004483d4491418007010692900b01c01007070000038044000c0c042c00c0d01e0310003040d800b0b0102d421031f81d80e440c0c20300039140136134012030001d0900707445180200944c0003082c00100d404480c11400020a4205a0b03041300e041c2400b00701c04080c0b65102c0000f04160711b548070392125000340b540050080720902000c030ba0266100103003075002d110700000c8400034a4401d071011540e40e04960060b400942040c000e440c0180540c1e45402045038a900030240100c1e001810600640c5441004a924803102c074021820740c0400d0240d070b034400e030081c6c4e5254803660207078450b16070391005000018400c070b04441455080c0050843e0b8440d90860000e000b406100b88100c00d10101c68a10036541d283c034850018988100c1d00001d000b14081a2500f41d42007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 690600125 1250 690598875 690598901
    0x506070f021210061212020f07090b120a03021e070315090204020c0f060108151005010e0118180e01020304050a020603220f030305100803090103110417060613020702010504030b18060a 81
    0x18415001b8404907101c440102c40c410f8642d001900a1040400c541e02c41c0c04041d00081c812140416480e03d16800c00410035801d40150b000440d07e56000c05094491702c110240c1c07000135001c1320b421661141604c040c00d00d60300702965511108482107440d1030b070403601000312143c1102c200e1803038640095035a040034000c4072294058221758190305180421010f001e01c0c0304803080310b10399082c100112041d034a0040994104145030031103c4085001400d001c0c0a400c0c011103004440780703d4980c0800b0f903205007428100c1030b8030420400010500105d0041c054075130442e04266240c83d540483e00c9482e82c0c0b607400d9010828510380d0038081200d50540b104480740702e0380307080c801c642da45140513078290541d125a0302c07181c0080000c41c05640c03090384809040c440d503100b801c0c105070711080c4500c131100050ba40c0d1006035014400b07100e43e40c9010400020784085808081d4038020450380000c0050003517100003494071540c20046000c0e001c00d1940004500022421030700d0610746181c3c240090308820350b00340 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 690601375 1250 690600125 690600143
    0x703052a1912020304081906140a05040303060b03190906021b061812030a05040507090207030c0c050901050a0e0603010204030b040c09150f0e060d14070f0506070f0212100612 77
    0x16402ca40080265012910100c016091000b20412489400000030741c040700c1d00d658a46086855101c00015240101491040002e581c035042c40d0150840d0015000503030f2840c814410400c06040301640307101e40050281d40807480300301c0d618181029026070080e030b85404d481ea000c100d01c40400096001d12512045d615064100e820000322506c1e107034841ca1544002a040000840d06080c40d0801e5400510680449280f42c0d61007800c1d0007241c1024034202c00054003003443e00240240ca01000002c1c0104880c002c01c1c0e03514041c00525803456500c00e082d1800f2507840001d94a603000c0d4152801103070080500c1d29149440c0c03400c240c8101c424003404080703501d04000103004480481540d000c1d034507415448140d00c1c0c10110082001c2000802c0c40d03501c200954028800030300a4103100081140500003850310398100044140c22004580203d80109014010200070032228800300481540680b840d81080c0d80c0180c00c0b60620b4480c4138544032a5040c2900098402c148060aa4820b80031784210 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 690602625 1250 690601375 690601403
    0x702011209020108041e061104050915010203040620250608041e060905070f171b01051e04080303150907020c10050904061e08030703052a19 62
    0x40d1046030081c0350040c0c000750158000138005041e100b81d00d441400082c00420304009159101010b6514800c42e0f604140300103d01005141010b0508941080080444110705058000002d6a90040b84102c004002c0682c190900e000442d4201b1039941c007240e03096502c005500c80c030100b00c0701c04030703162083c10142c2c25000003441441005850302031039110ba00350740c100c0d5210266030100c0e00c0402068402e69a100c901304009201008030307000500c242025514a245094114900c00e8401c60780308180d40c0100341c10b0320034104440e10011800c00d090070130a0b00e50010b10304410805e43c07501c14144101200180103d00084004061481084100c1000000b528048140406900241d0384100964044c0c0020304017850300d0030300b69002e40458904241807054000005d41036812941c0052260703025840703c101480548540c10000d03012600c0298030f010500d80e80245103118070102e01c0b41d0f1600f00346440d18090000e41800b1104125102111a006101c4c000d50702d044103428402c580299000d000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 690603875 1250 690602625 690602657
    0xc070303020c180a022104030305090c014808070606120f060c1b0f0c050604030c090b0406090c050903060f10030209131a04030f03051902181005070201 67
    0xc82c00c0ea002c500d07001d21003c0e8944494100c060740060f8008400c070b0b00180d400303a030311503a08130300d007441b850182da004609410a441706504000038002c8440c10889004038a80380300f9a14450340400d98030451038484241e00f90801189004400c1c0b605007103d1003096003240c00d11078402c003d044258003c0d0030800c4141e54680f0040c40d8102c91810040c41e0100000405000c5122940005049400b6091814084201c4405d00c07013620080d40048038101c0c45800c04e102072084951003040680000d5070400e10b09800c5442d244601c01c4948215042c00c0e444200b1100b040c0c0303494003d0001410b55280500460500c0100682107130040020300c0d002c2e1007054006058004074400076406088401844c003096815a02807140c03034000103004034114141001100c0010783c0e601c1c018001210b21114280c0181000d2900a04001070b81402d00b08060810090047d464a0b20040d60b4408080000040e0b51300c0d0040c44440383c1c0482c5c00c551030360151003400c01088142e08940185641d80c403d90703c1c0c20800310b171034032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 690605125 1250 690603875 690603889
    0x50f011505010912030e10051c05070e1003061e1e03080f0d090b090607090e0403020c310204090606020f0c0105090d0501050c0a03050603190b100305030c070303020c 73
    0x100e10341c0050710583c02000505a40b002040d4024001d260040d901310702c840101e440c000c9218115000120f0014050020b401040d12403081d000404c80c061180d0708265500501024018110a218440846d054ac0b10705000f940a280203202c8000100c840384814126101e65031814031800c00302d20344a00b02508008844205501602d038094503003420803100108020700c40d004844282d2800d80e0310500e07071010552400c0c0751031040784041d00415031454070002c0103180c070305940c0c000841281810705002c00a50041000010a2001d90b030b4584c0e070210188899401d90031079018500b81070f01040d4016001003407500200190f0b18400070900131903030759070070490750303203020a18076001a044460f45004641c0f2410043c03542c103400130500c1c090404661192400c40c0c105580540351034000240700c031090380c0c050084d241e11107011801b402c10100241c01244100040c0300c00100701c40d4100c07000940300c408031005400955046401c0b0380c1c07180d070001e1030181c1d03c0c2460700042e000b51140761015900c52915207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 690606375 1250 690605125 690605129
    0x8030913090b07081b07051b0121110403120314070903030507140102130e040510090b0f0603030f210907060203040e0a060918110603060a120206090d050f0115 70
    0x10081640c50b50307070f031101111521005001581c00d03c00000300700c904019880c0192021034002c0010f45098440c40e006d204044110030301d11418049100710035429054258100c03909140c05110104407031242c02030258052003103410083c0103003c80c0220f0603e441c0c1c180d01c2000d20b251004822401070726210810f03681c603503151000070005403040100d04002101621514241035000c0009800c1042d42c04000a440180e40c0001d00c404c0c1c0c031b6138100401e018003008029045142090708102c901480c0d1140440b4500090502c01c001f07402d1000300f0783c0c5031410012071340d2190f2125007464455221145420f09417090422081c441100c1c807000c10b1500c88040744503001c48a0a400840c074040c80d04090040119006001b040701036551640050302040c0340c00740e01d2006480c0e1464510b624100c1c5030105805081c1044a40152400d008000480d01c8030b0702c0030800d031081d103861014958031a100080041c400c20141e10342104124030510b0410000040d47d0440f005d207440244080441504c1c10a4005094 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 690607625 1250 690606375 690606383
    0x70513081f09020414011d0f0417090d2001032a0804080d050a45110d08040602120a080408070602190e0111033f010803091309 56
    0x1606990801c103201e648000100c503c0039001050340311051800f021402c038241d10008000005c040c50808502c0c03c0d07940198085840300c910100c6086c00d03121480d0001d8103401d43da644200c0050a120796549501140c0d4445510001e0002401100d9601402070001c1381c0d46580800d080640030308130b0070415489042d0504101c4e214002e1110010021141c0c0c0304050800d07928184100701c5043c3c0d400e0140119446851611004200c1d224040b0b100e2101070500a00080b00410780c0b0b03085442d00e800440318940504d1990410a001c0c0214101040260a1030389056444100c0900d48003c00800401800403101c494094610b280b9017020094510f1283c0c1c105400024444000980002d203210040d00304640100c10041c01e00003400c14a0980c02c0203a10303504003164011000100b01e41c0e00c030450080d038525002c06141089040003412002189004140010354140102c40b6680485011b031141c281060b00e104070442d59640c0f00d00c07502c075400814080d00a581d91150f8420301c00b62802041485644 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 690608875 1250 690607625 690607663
    0x1a0712093e040c12050907050a05100f080a1d0c01020d14030402101115011e180902190b03010315060b030f18010e0705120f0a06020a030f020307051308 67
    0x1001c01000001e01500f040b150078032885502d004060007441c4030307a0303119009000047c043c1501300b1040000360000d55008500c50450111508404c03580541c40700d020003040d042400080d11503400c18800740500ca0303945809020340c08081c0c0100440040c501030440ba0a80940f071140904020407640025010000550b0000802c046401420310b9448034064112501d01850801140321420f410013004c0201101c04219a100500a444a80e90a00503003115480c02c1c1c4012803401d08154801600e020042d0001c40c0d48001c01002d645a200c001c0000c002d0a80608000c0d03501c440071465076400030301080d10407400d091180e50182419220360006e45982845850071645c801540c20034146000307050401000401d840c1000c0710f4400d00a1421000400001d80007203414003041c8000042c03030103081c0445038040c5035075892402d8045034035814250052170140c1c0e240644041580940000c00b110203401d0b10010411040c0d40d03004015028151200c01c240c154180d4903e110f590b2440c1c002c00c030100480d8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 690610125 1250 690608875 690608993
    0x30a050a05012607032f09070e01210e0303070311040303140d090501020c01020903061302012102040b0313120f0207060318080705030a08131a071209 66
    0x104991020042450502c21a18071580307954417816070400600b000d5800780e400107954281000c0d446c8088074203402c25140c1d0106032405520040010b0740d0030b02d07102c1c1808a0401000540c4150030040460400c11883c01e12017014280d05440d941d0744121207920029107040440ca640d00760480803101103035050781e9101c2000030f0340700300c13849694400c07444071500ca0340d20380d407000c0012000c0c0080c3c41050f00c800300058460400310141070400400800e200c10401301c5000c1a40140c2c2c01182c101d8859124000107034401c0c100140d403e00900c141e80125802040100c1000854510882c0c444200b520800103903241040804059941c0c90390a1024005a0810107007804254070070340c03203422001e502d207410503126980c1e5194540150302204007612990800114001e110f82c1000350303036820500701300341e007158603080707450f40c440c0200040b4511004001280114203200e1145109044628190b04108000200c52504402c611070764484107409986115000c1804690009040384001e241c0c0d04a501e008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 690611375 1250 690610125 690610169
    0xc021018030605070c051c0e040b060f03130515070f170a0c0302040e010b04031b030309050103020f091e120705011b080705030301091413151505060a0203030a050a0501 74
    0x1103030041a03c0c08201c1700e11880001302e4000c001400355401c44030200c00c0c5c2c80c5003040001381503d00040213603011b1810003038184096120041207610f040d41c0403030f03502d807170707403102003640462603903501c07001d00541f1903440820302458040305407a014101a4558041a03181d4103000e461a509208884183e4174840380041c1d581300700d81e044400350382110b1400501d450344400d10845280000c3c0c1141c060100d0100b01842082070895906400c00ca0112108803401d28656004046540c24040c0e14101500804c824003075450010a0703e20320000248101c2d80c03018920f100d040c11440c104042441251a252030215807100030592905498042e540c01090f40c509420a0000d10f11400007201c240c5010880940410010b0010b18041c01c8040c0000c02d071b403054010310078200c2c0409080321260000702d00b000030015407024201d02880c07841002c0813a04201c5981994a102450b5107c05c1e040600008e00000407a40030009502c55040c01d10104211744a10300b003503040300c0e006d0040b00700038030b84401507050300c1c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 690612625 1250 690611375 690611381
    0x91802030a030c0c12050c1e0607060908070606090506040f0b030c01081f0b0a0216180e070806090c01031506020606061b070f03061a01050315011e0c0210180306 71
    0x414040c2d55015641c40d40d0358410701c89014a50740a80c6c584e000070342d1100d498540350130020810700d00c84a03c0316800c1d40601c00940c062046d468014480d5507142212402c1240400c281c0c1c3c0b40c180c0243c800c01809964450080103071230304980c86842149000103100020015120b01c070402c2002500a2503212414401903070004c40180881522010141d114031944222101c1103001c0c0002a0400344c48003c190030180c81c0580441d108040d020f075400c0309000902416047d08605800d000000c03c252403d184047d0a045554002c102280034150401034150b0300052503600344038080ea0200950620800c0207500c2c004039018980060304990040342192030100081c04840c00741d0078079112043d21049000340f0b07101840d40b0075404646188410400d110062040307120402d006620030a00000c148002005440018810340400c000b1084113041070340b0416100c07040c280001007a003052040034030050150100c4180c12489111f644040314101c621801c0c120090003450441c0300005400c0d0307510400a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 690613875 1250 690612625 690612647
    0x40b0606070609150c084c0902180316050105090613030320010b090a0e07080303040c0f050a06050304080318030a090807090e070513090813091802030a03 68
    0x1196164060b407000316011241c000c8040ca1851000185c00f00100e402414246004180069403038110042c50901e0104120301d50306007000c0c5140c0400002100c503484c0010044c60000e04c1c0c0c03d481c0f25800b2402612070703401407a91180804080d8010301c62042015a0340e000411f803601216a03010040060354081ca005c5c0c420900b00804480c106007110f04a003c2003d0319034400e071b0004800c05d01485c103008080e01029680e2911038001e12003400b500011541440d80508401306041d0307070308d40110f4082e106000d004007810500b001e0329604d0516041800e40c8900c1e40c003070309a0001c2c5100d0001460700d0400b074403130101c03102c40e191141155100e48600066410003040d04800318201d5850428100081c80104400c580c16214001c0c1d403800c00356000c0c6403161580015104c01d2a040040310307910300c001b0701441165421070309488103501a22405025088101005010b4100421490024105501c503e0107032940003808010410060b02c0082100c10245806034154104450000100b0f2041d08030000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 690615125 1250 690613875 690613883
    0xc060f150d1a06061213020103110909070c02030708010f09050c04020901020a060207020402040b280f05120a0b0a031208071404031211060c04081603170c10020a03020a0215040b060607 81
    0xc1008a0010300c0c4d000c10720119500322210114441c0a411503030940704070540501c80000ac241041ea554011070034404002c2c01200501c005041340c0421590100f04074409407843c0344c0248480140c050880000c0c054000c400c60740c900410b14000441c1c2032520136500309410590080215183e19140c1e00c009503c683c005a030065002c100208600078a00000c250f1400840040b29110095007121a50306482d201100204892542c682520650080580d165100540031103401600c40c2910007000700070607a1080d0b080024900d0000c240180c005000c2c1c013100c0b01c4d03250b194041e690346008581c800c0810545191224045c001031000c2410040100c5461030746060000600c6662a00245041001c030ba035410071403c001800d0100e003c09100f542a00c5020110b00002e0a00716505c81024040031059020764500c0458070060184041000c0ea0309845070303c40c11036540c5001000140a54018026140944203c121018441500b45242c0c0e04c80ca4118501d40d44d145c84150801c041d5501c10381d401d0b9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 690616375 1250 690615125 690615127
    0x90c17251502030c12030a0e0d08070f0e0405070509030d0503010f150e040f05012612130f0f0303030b0d0f02060f09090a0c030c0804050604020d02060c060f150d1a0606 74
    0x281300c0d800811091107011090303906681ca074500350103440d05071803030889000e1481d000200c80718081e54100401ba41c120106040040704031076400401c503814041d01429a500500341000d10105a4100004010307001045c1c05441031030000c0c0e5801d907094402131140c002e100321001410032500802c4c05004001c02e60030b103420500e074030b45840041c041e2100008044441c3d941d8400402610b00000585d18a513140d840c150288200843c0c40707240c803000380b00c0c0495150b030400148004c82041d02641e03440074145183c0042c02d801d4441c9400035100302c2500003100460f10340703168070703146207803100c070b6000c4640d4496400f140b030705455428055290007a07080750201c11380601081541f41da0310a02c0c5449401815000a04a4442c6100a05403107090021100344850842440085180412480e501c02e406031a440b01c414480e1000c50264443c0c0e07509190140503e60500c07100245000010f030064103c50400c0200000038010030158001e0010024503020f942c0701130070004080000d0f0302d07a01c000d00420301 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 690617625 1250 690616375 690616387
    0x91f09050610090f0b1809070312030c08071b060e070510030207060b011b0b100b03070c020f0111030406080a0e030705060108101401090b04090c1725150203 69
    0x10901e842000e50758494008031815060110101c64800c0181c0026603c0741030020040c8400130500c2c852038001520700c54035055000460008080028000541e4005030002c010740d50075100a0040c02541452000071760740b4004070740c61507c1983c40700b0800042510204074148265191401000003003c445040c2c0a00c00c400507259a5000a090143c221501c0c05680e035a0079240000840fa06424624140682264409011b0450410003c503c0381c6c020b050202a0b1100c0041c0030300c11400d07900c071150b10720000003082450366201c440003160074400e0b211083c450a69800540c1d40a08041980d4580c0c0d00900c070070050148603190003038021640c100009000d22103c5411800c2d030f0701805d000c1c1d81c1640301000401a00b90104507502601e5120300c010400402501c160741ea8100c010700c00d2441c0725482d075a88001d6551264002d10240c0d92140c01c0700c0e00c43d91748620b44a076066180c131303000419020f03140354118190710f0030060001208200b0b100d01881414000c00520030500009410114031040c442 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 690618875 1250 690617625 690617633
    0x3050a1d0916121b110304031e0506100b2706030702160e01061211090a0e07030b030f03030a0507020304033c12030c0522060201050c03091f09 63
    0x2406024803021034039036546100501c00503040d05910b02c0e055098910f808404403040d62110311110340d41e08141741003000a0078038103080d46140034a800150150921000d1088484150300c0c07401403070741c411401e0782c6059442000070001c83c1c00512425000039410000072000341031145c665040d000c041e81101100a0080000c1685600112803e40c0035078402c1101a44403044002e15100500510b540d1840540c10300340000c01081d808500801e006440380601e10030001b881c02911101040900310340146039442e03014000c04001a680c01d0042450b11600209a04001c12404080080d0400030b51950f1a00c00c2c080d0f0040100034034203400c41c0400e1202100081d02000d20b20781e110700302075208000e86600303070f02c40c03040c40940c0c2ca5901071314a41e00d2510001401c803080c44070440080341000102c1c0d40c9060b80a035458810703000404c10a01e00b601988195a6050041006480c581c0e0b0080005a44040d020302c0548810f840c180017aa101d80324582c8140405280502f001a0014000c56601c4c0f090350b07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 690620125 1250 690618875 690618889
    0x9011104090e150106050703031a030a050c0a2120130e1b0d1112030c030301030c140619030f020705060f060105040b1623030304030e0d03050a1d 64
    0x1111440c0d840c1c0c40b4121400908214601c2d60560302600f10250f03515043c0050020b02c520308000702172640340c92415940c508002200d442c008005030554002005c04d103042602c0700720101e401c500c6030a15a07030100708142003880c2c0d040345490043e12100d091440d520740c0003d0f46165200048152040b00b07110a040e118192a641c00724125500402e9098180304181c1c1800340503038004640d4801640d480702c1c43d90754600807082181e00022580c5a001c03a10001c00e0300c2681264420003e44000205810100000001981202e0007070b0020b0340090b07200d0b01c282101708140c049190740800300740000001000c0d03001d139025548845060000301f44074000702c8132099030000841607809800220400c45514907601006134800d2007480c1c01c525103418100b18110031b000c1c0d030040c0340c40001c10f911050304105c01c3c0040301140d00010b40d86225460854100d071996580100e83c00c5000030184904180141402c6002004195150701c440f400d081f80080100ca200704101d0030000010130802c0180d5242e101c0306 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 690621375 1250 690620125 690620129
    0x6010f1404150c1403070b04030f0c0b0c070c0f14060c010b0406090605040c08240a090f020a021002090a03030806180702100e15061c05030a1805010f0c080309011104 73
    0xa1039090070000c85041112284aa44c10701503c290000c020301c01c00961400701c400c0d48241c0c141002031400e10001303400c4503c0c5400c418002c044c1510300e01071209114012014000c028410305005070050784a00c5007072400e414074402c0c01407000900c0241030151400001808a0104050002410a800100050940e0b8241c1c1c0b00c4510030f42e4600f42400142881d00070417400d9030300e07030403c2521401c0a88030a40e000c07080700d1064080001070181d2078131654038154800c004000800c8140503038403280d000b600003940314112080c0544140300e000903045000b8020389290b80030092030101030501e1514240c6082c90010040da40c001e540300c06019000c0703000441c49000b551243e004048180e0b900f80307808120340e1406260081907020300c1d03070305d4141c1107400c81559011209a17442130f00c0011611030b040d411106d180005100e40004220000301c03650003050811184288034150410682d50350044d10100100611800016031104d02c40e00811502d000458111703412800001c0d80c0d00000302c1c1c0c00e282d84c10607 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 690622625 1250 690621375 690621377
    0x60f1b07060f0b010806090a0f0207080c03130501090f1e0b22050103090804030206180306071d01140d200a020627030307080907030b04030c1a06010f140415 69
    0x24040d02c9104100c14490b14004202c03e080c0121030303007000707000140302000007403510580e962150301c0d50801090340d130159214954004901d0362141c41d000c0300c041e140e41106002850300585000c0c002021344c86005000215440400b0510000d0b0501141114801002001d01d400d00032240c00040e104103000000c203c407202c1910103100320035107500442c0412025500084c1058100402000441d00000883e41140ea04881c9555a610950203584409604000141d81030080c5420802100e800182070f4034211280d4100700d460070f55000040d10358040e5003a01d81d03092034091150380c8043e00e2981c0400002e400c10420b8201c00039000f800c0b9502d55000c0449200140c0091003400524010b92102c1c1c400e180c4025101442c800994880390303540d000091103d020840c0660104030b00d400180b19103005190001042042403a00341070180c5001280d0104480b00060502a83c00007004510302c0d80c000c800587d202c050101044038100c1d20210024049080001b0030007001030398103038042e0720700311440107 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 690623875 1250 690622625 690622631
    0xb030f10050f011b02190e01090b0103020a09060c020a050301060f05010305100b2502041103090607030608060615041820130509090f0601260f060f1b0706 68
    0x140048200080c030541c03080b4040c881400c9a080302da81c02c19204000d03a036480c1d10f8408510450f000141c101c5480140c1c0c5079900c9802d50010845907460400103058580020b0305100e00241500114200d1044200e61000142c05180c180322403441030500d2003019000400003500c403503e9038002421501590700290400c0c580007010042540c042c05040d80c414034840a840441c4e180c28010311681c411809040303460315070241c01404404d0800b2584038002e170007801c10044150b40345502c0c640399005403002516441500c0000b025039109000348021f0341c015001070703c484c0d2541d00502100105035100c003c0c0c0c05d00706020104d02480c211a0300d10500403420404180845100b446000307140c0c0c0f00c859548043c0c1d040210101c0c41910002c00d5049640a07a00c0130700c6650342138038060030584500000c10302805203500008181a14014080e42c038406d015890b43c40050380c403841d81e500c22070011100c455800000c0015007040740e46074000c2c0c0c0100c0e13640c020325003401641003455482d400a442156840d503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 690625125 1250 690623875 690623881
    0x41505180d05030703110702030a11012105070e060c07060509130213030c050904110607060905010c09060e04140a150812190e090a2d0f0e010c270b030f 67
    0x30303050007542548038104030400d29040d80e5402007a1180c40cac0020103456800301d5501110f0316441420514042d95545035008940103660050601401d001d0380c105000802d8034120721014a800001c945551010f48018000a490410256501d0304005601548520030b49944002501580002c2c078405611100c180c2402e400c614005022010617040b050003618490100000924600e001290000044844948a828621340a070103081076100c000c0c5254204481059583e4200e2034000039200359859609003484542c042c00100d44d4100c054020b003420030004101409450351007415503d80c45903081c680c05485101d424586008007400c0202d8040014810a0b0364890601000c600c1a681c9003060300d030107102d000a07248100144c0074060541c0c0d20034a4000e0903d800807103d400814a400700840720082c000f40ca80103040c108854104282021001c1d9080e14041c4144210421940c039040d480c2e42110090604105e031541483c1480d82c40b8400200d540070100010790301c6940040f2048003646 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 690626375 1250 690625125 690625127
    0x20f040e01080109030c20120303070806041a040b0409051e06060102011a100c06050c04081005090703030804080d062606011a0d0b09090c0117041505180d050307 71
    0x4160b01546059140107008000039501c00000c821041e007000d5004d1004141d0030181200c0300281c01002d91142003600d007210a100c0110144d13110765010388521100e80c0d81d10081c08191808100c07d403103807441d0510f201209140a62048150800c06040040c0042c01540e0b81d602c0c005108210940403100140100100e201c10040303a6405002031000f40091502c20340b540b18101d40b00c0e440684610a60015482081d200703012100542d50090024003260400e90b2041195a11900810b11540a40c10114024250600565025024850041504030303c0c544040399503180150040781c551a041080b0390f000140303400360a010f08190b034040210a034480c105500c040d0300072030815115420002c0108001d01d0030080b501008010008c286035a0020066280c005002c0003010541c0042c03802e090120b482070001761070a040d1400e0705c410324404680c002e03450100344200d030024002115a0042440d00d0020b41100c2e4018840318050301c070070b055030400c090038070451a03032000002e440481001021 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 690627625 1250 690626375 690626399
    0x509070c050703030e01170403091e03120e120105100504050a090b010501050306010302091e0139141e0606100c08070c080607030c0212040503031e0904020f04 70
    0x60414246803142050580d1065241c04a0b44400b0b0240070003101c400109034001c040e140c402c030207901200800c624091030044c210200b00d018070034120b00c02c4030411301e401c071040c05210160b80e04442c080c034030141c1c10a41113406000c80c24505810146520903141860401d006040c0a03002c0c0380514000306052005000440b403008204440c56818003030304d0700204001600c204c1c1034920070f182007a82d80d52141c005030007a1280d01c52142d00000c201e141020300d510101000501c0c02c03000d81c1c41c905811080b6035481409a0203100803945000380400000c1c080a0300d040140d03080e48915502c041c2114544080c81c20880701545000007a207080383c03184402d2900b4030441d68408011140c1d145800c09240c1c0c02000104401402031450400140e00340600028050500041c600c080840d8000c4c504000c0040203071182c030740c40034090720800d0f15004400380c07440c040d24151000540154102503228005548203c02401c0701c0010600030420080c00d41c0310746c0020110a03403015035003507480303207013200801503 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 690628875 1250 690627625 690627631
    0x350d36091b0f0f12061e03051002130b091f0e180907030b04020607060e031309090f0602030a06420804081b0d09090510030302061f0f090203010509 65
    0x40200500c2c03500d040b1a0850310b4140e03503294a19000000d040c10ba41c01c00000e210300c1d004608002c600140600c0034400c80079155068038482c6041c0c5101c01c1c096000c1005a0040c0288103a0940300d81100b4409459400050312600e54024204603944ca0403640c40180d921078152100d00050780c06110240c20704010701400101c6005a80803100c915080320b100da2a0043c5010041604422002207000e542d00c0105a422903500305400f0401c4440c1c5940e83d641e00d0703000e804200102680d0074000078000a0703d2184156a41d0001072080f162007084c0e071400f0080d071008048039201039407020080744080d02c9800100f01d201c0131250210300e0080b13a540c2d214803400c20804500760044440d240401139030f404000d05802a078040300c2640c4918231000c0403903508030542c00c803c036188141c01052100aa000f4a03880c01c440c40300c5000c00481c1c640c3d110602150206000280151340080080381b1103405031001001d0b19214101d000c5a40754603401e20b00c0c408035440d446140542e80220041c012031506805140d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 690630125 1250 690628875 690628877
    0x906040f080c01020f10020705070e010b09011706060f0913050c0442020f120414060702010e12010603151406030f0a0305090406350d36091b 62
    0x582c0d00e60f1710059644d90700b4900200c445140c010400c1e10402c00100180e01c0a405401c10a000030341c1c6070f0403940700b240c008602039400200380314038001c00c0031842e0000c0d074080c00019029902d40f14021041c01c03c01d134030101d500c0b80c101c0303104c0204141000d11840f0b030f05c3c01240380d28015a0303282c0c0381941d41d0680805480b9462030420300c0c4034010407c1305141600740320311840f407003c001020f50002416801c01144404892030f81c040c1002c1e0314145604007000b0401d880c0800c4a99a0304494070040c0002d6004044000780401d03400c041b01412850500e1a40a600160a0010580307680f01d5980b800344200c4104038210030f94407440495402c105054a85501020580050001c0d4000e0b09032245e4881807200050144400054400e159845542020000d40115a02100340d56480401a0a00c0c3c000c100c0003800025003030307600c001594000c50445004011991a402d80404032091500c03100c0c00e888100a02d100b01c0901e03240b5144804035200010002c000e0000b940c0c9090014036104a01d2504440e8 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 690631375 1250 690630125 690630133
    0xc03050a0213030f0c030b0f01090c050a080a11040909050a14061308030720030c070f0b1b21040e0709051008092802011805031f020906040f080c0102 66
    0x4a03002c100031001c0d82100d80000c280d0411060600300107141009070307000644000e49440802c4804170b10200d40c3d6040380d800c642c00b0050b0b17040098040310540030b07051940000030300b240d0116242c2086034001c40c50107840003d0052800d603442000350101c13508040300f01ca0907040b002e54007003070140496101000c6207807880076101d00d01e021444643c102c00304c41d074001d09407071b80440071840c1c407482150400c213845e4034503c800039408440e10340b10f690ba8000c17040c0a941c0c3c0c0304c1d40d800070a4001c400d14041d42140c0603070440d00c0c01e04004942e0b0070009a595884c16509104440954561100b80c07100e1000e0325010701c0260b55141d041151180c07848000034a001c0a014000000b000540c40e02d0000c203642c5040b500c0c0001c0c8a8030b580c11400c1c2081c40010110f2210661100b00754410403111040703c403003a00c01d0300e4108072949005a401300141c105d22a02da8580c11508558048103c1580054607403080100018507040005001442c1c54100303400411882c0c5110740c0a006910042100300d540102c02d000030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 690632625 1250 690631375 690631387
    0x3609060e090a03050c03070b150324011226040e0a02040302100804020f09040602190e1e180108060105040b091302150405060d0203090105011a04030f0f05010c030c03050a02 76
    0x1030360340daa0900002c0c00c04c00009001d1210f840d040c41034074900390340004610913600380b00700142c50094901c1c00317151007801040034058410b0068000c0c146100c44107295045160300e4050000f1032401d00b08010349038821600010b04000d4160801c0018101061510b1515242812160f850800c00141a807041c075104100c1400581e58045030391503415018980760507195107510110b6400603011118582000012040c0003c1090307a801405507480d8441c00c114003140c0126003101c150701d10725440c40d0001002c0e40003032189206440b0906482c0000b400080c2c0d2000b80140380400408240d0203078405400443c010300191400e1f0040144d0444c046905482c14108420031811440342194020300c50098400c81c07040181100b82034030f00034040148000c3e03c413283c06004030060340c0100c50a1420307520f031000102d4440b0302c90100b680140340c001d00701401c09066980d000444851102c0c04d4860050070302c1d000300043c0090040d42c03a540d003169000300350261042e1014064507009401c03050750318018010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 690633875 1250 690632625 690632641
    0x506012c0405030708070c05040c0804052109090a02040806010f14011409040509071215231b1306030e012703030f0905010c020703030207050612073609060e 69
    0x10b5561058010088995400c03180c50504241030b070719408940c02032b00309001c0344441d507004050141714502400603501d0201c4244ea1b80c3c600015811103001058070140309040a80c1020340d14070340d01213404000113140a4540c150030385402c0003680803d81c221011032052050785065000c01c80b40354000c0c06d141c0c404030310303c1c0265003440c0034a04410340a01d0390b0300c00143d440c1e80308001030707001440e5801426650a669003040021130495508020f80359007084000703541034044541e4580030360506030034454280c442d01010729262040f030f40d450108400034810f40b0341c800e0401240340c0c0100fa041d1400034541c140560040d080d100e100b07001e1100300f6100740c0c00015241c0642c0b030414110b41d052400007030300303041c850f0b107078004000414015000e0340c40c00000698160b00000c0350405e0301c4c000e0302154071146c1d4030010032a9510030021009042d900c040d0108001074020091000c05264080b4002c0034060482d152000001c3d02070058198030545031070401081500e48654405005a110380300034501d000300c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 690635125 1250 690633875 690633877
    0x4120c030c090606050d090c030b07170f0708071b0c090c0e030f0c0103020d140c1308010c020a12020a1704050f0411071b0e01090204170c0a05010e030a0506012c040503 74
    0x21b590114039181d50030b150800030440041c0340650f500c071741540201e0509150052800291440c600140c82c0e0000c04506044071040e40e89114440315503d020b4aa6208007084602c4041c60840c0d01d040342c11071003100300003103a00d10503501908641000040b0808000303402030403103080c028864001d4108100321650310002048100c5120800e08001d80e540700c0042d0a18002c000039030b83c490035910504244008410708500410f0340ca80d44514294000d40c80369a001e080340c0d03000601d4005a4085028580002d1030b034800c4170301c202d40c0c0740140c603000103c83d150100324140800380704028840010382804285020850490035a8081c0d50801c54007101750b240d41ca141c807030548041c0401050100c94801a80c0c05854600035000c002c51200d00741d6921540c0c136003c0e4219008070b0080c03209410022084020015a0b12400e2a00410882030545804015290081c65104c0140c05004281c28400812800c01a06000b4481000d02c22010b02a84031203070144003000000804040c145414000802d070004 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 690636375 1250 690635125 690635137
    0x10e090a020307020304090f0e071e140d0813060807020307080708161a010f3005031b0c030d0c20040b040e0a020a091b050f04120c030c09060605 64
    0x20300180d8a49451400b640f0b9401507074070481c0406d00b40880ca85514403030307420204d144a103100407101174a4841082c3c00c0c0365178085c4284001003816203020040d01140000300d1101440143c09250154002c0d107076101260711502d180011180c4244c02004055405804554002c4a6201560802c400b03561455528451f0300400740041d400410054030703c40d184640144003661000510b10300680a213111410000e09108215000f400100d00242c0303070a82d03144440c0c401055510166146544441440058609090030340e20781c401480b440840206a40c1e4a42682122400410072a611942014074110702802c40704100010801e42070005001c88079034040030301e03508528424400c0d440e00464000c255074400c2641c002c0c10440486220100800d01a082500a60b40001c0c1640c0310302ca107a041d43e81d00308010300c0c82500800301c5d03d1031078441c102400100380c0402c0034500d0580e44041c00d0300b0f060350441e0255154450600100100200b20b07101038000c0081400030b201c100c0c60400c010b81140185 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 690637625 1250 690636375 690636391
    0x1b07090c140304140f10050702010504020609130902041a1c0201020304050126041a060d0302030a050a050417010203011707051c05010f0f020c010c050405090a1508030304030f0e010e09 81
    0x40301180c2006013160001ca5140c2035003044860300850140c100f561a01050003040f851407604012400b07a901c1801054400c0390040e200c90714100030042072080d9016240d125002c2d007983e07031101c0d10040e139940c052205800d1580610309080c90160f03003001400740a06260b052607060700d014410043c7d8000c002c3e035044807000d081c80411191049208400b850440e603000118141081c104410044c11065071201e001c0c0b0030080b40042d94420b01403051144410798054056030040c000115110304c2940207020b42c4803103217840c5041580d549244003440395a0f406a44059402000610101c41c0b610b0324550901c40c0c1d10b00500c221450310003c101041c10724003034408946444558a02400003d42104001c0c0542d040b0801001f01240c3d13a40000350480c920075102542807032440740d40e42d8826400d842c152070008100340d00503191070070440000e015618404445507440100014140000d20146201d980a40c030b40e02030194031508001d00b02074074501b440341440944c04900d500c5469002440f03078000c2e06 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 690638875 1250 690637625 690637627
    0x2031b07150c021b0603091510090905011b210b0409120c0c0801111218030309030405191413020903070b0405130506060304030f12021b07090c14 64
    0x954104900c1e4040d06146811207103040c0350399103020503070004610001c0441c4c8801c1004c0b0b01041340c2000100d04c0181c41c40c00c0c5540c80b403138404400c12100001c090304a0200f0042c052290340d583c841c00c059990b9641c05590300c2e503640b5031008101e01450300032200032603c3c0c81c045038030748074503d00080610f2801c406412516901c42184a003a201c99004030480c0ba0002d2040b54030341000040240b1980310307210202e40445000d480000c5505050050a071140188034040d070421180c00641e586242c00203041400007103d0103903e0340c0340001403008601a85203c1c000e15507131828807050245504040650780301400b510301c401c1240f000c940b0500a070100003202d4000b55809503102d101d010740552003106a040c06010400100003141c00c1c0108101c030801c4d03c2c0080c49107181c500d0442194022039800b600720a08100040c00031b0f101e8012035290a0b8541000d8094900030a4043d007281c2101c0d20300703c0c1c0c041c422000152061001c1250f40c004128515081c00100c11010009003801a682442048410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 690640125 1250 690638875 690638887
    0xa09110904050406020c010609021c1a0904030203040623040620071403061303090e0c0c061303020114040c05060706020405030307060212070e1804080d0603080c070902031b 76
    0x80210100e91200c5002801444941032030704101c0002d42c0a880030031525172a0110000c1c80103518003e98106d90410300303480c00101c8060325000041d0040d540d841c04260301061015605a40d20b02582e40180c2c001d030300640d06d55040201c0603041e480381ea0798207000d0491600700d040040c50762104507001d4803103510b8518515401c5600002d50500d2240c2e4900b12800351321804a1900b812008600228100f18100d031034684802c51400b41049403c0d0b8003a00040000e0014484510320025103904034010809580c60609080010750030700b2410340b040d21242c5090340c040c40915509004030344941030755805213810f6080643c0c1e4001235005034400c00c1e000b080c0100b503500602030154192030080c400a010b0700e5450005140c0b1400941c4980104c495404c42c80700415001403103100c0c0e4907a0b901c0054000a0b4003101880070036103102009104860342041004a10110308203802200021032242c44100d4581503440340c41401c008168107e442c29078418010000c05100da20100340050240104441c1c1d540 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 690641375 1250 690640125 690640151
    0x603061b0a030e160e06040c0e06090d02030a0507090c080705030f0a0c09050a090903200c01030906090f03080f011d041e0f1b0510051801090510091805060a09 70
    0x8004c080d030001107520340740012070507034040741503206e0501268200300c1c04080303d000395140d5004c019116000b400500c1000d0860600302d06c20034a83e0b0004040f91f03540d002c66550146002032a4100c1d000e96615900c3c40280300f508401000d8020142e400c0c5281146869410740414810086c0003441c12500c0d1290700310200e0161005101030a0b0181c041d81c0c0715502c2d0301e50340c009403001000450001d16650042c18000802c0d130b92042c0c0d0aa440400fa000140000004402071300e4000d10a0703a50a40c5c0c0d1001c0c60004240001560307200380b0941303ea900c05d2411000401040a059201140e4801001c0d00e158a5040040c06e0a60082e80b054007c10410f04a0088204c24040c0300001032106040b1405c074018040803689480c000d5507800d640021841d00c540a029a135158044c182000c12801d0101c1e041c00300c407102c0300f201c50003018902003009a944400040c10b040c002c4418802240e1440024880300c2ca0360741d804802203040800902550501c034000c10f201c01494850b2005003965007035040461 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 690642625 1250 690641375 690641383
    0xb04020904021504031a0c04060c0303050403030b04061d06010f020d0c0c0e011205010b0d08040e06180705120108151807090903090501020606030a031d1507030302030603061b0a030e 80
    0x1d0b610f6080242c2c940e0b80301d04d0075005c0c0550303207080c440710f42030403500140500058000722016039074107648002d20306400e0360313069029280280c422400c0c55290740d071030320650302e40707100d49801031130f00200c0500ad0854070091441010f4000d4016810803c2c0c00081000f095000030b8011000c6500385040384650f5050304180c540c0300c8403508002944410b220002449030203c160201a6501030b81c0200842c45c0c04208002d00030f800e82c2d00003800d501c4240402c00c01c48241c200f03140ea100300050448080b0400b4040c044000400403100d0001080c000315200d01221828200355000d050200018030b00f00e000404101e40c2c00e00c000b840000403c98110040b00c420b68140804401030140301800e11066801c0d25024003018428020b0301c2c0140b20b40c0002649500d00066031081c0e00d41c268860882003c02030740d00e01c0403203142c004080d80042d0051110903070034514a005000b8140299401a00d07410240d003014200360014064000d151000c10f032050003842500704503081a002810f0009502d01034100840c18 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 690643875 1250 690642625 690642649
    0x80c04260105010602210c19050309030a080a0e06030907051c1721070f0509041811030105160f0f032a08010906030809060f0405060403140c09040b0402090402 70
    0x1140d420240001004c0703030000b44100d44810310034003a51030b9414640391915075000703076039158603190700c10b2481201d241e0641d42400320311401802501e00d0200e561011903d004070f140b0080711551400103160003419441142540c410404980280ca94100a141159215040d004051080c01503006060807020f040c51009510707a03100000b00f200410701c180c2104103030080890301c1121b0a044c2600300c0e00400300c0302854490280c9844400c500c00104004840e1030304030a5416030410354400f0500c80b4201c03044d03001100c2c94481d841c44160300c6005e03c103160a40d403014002c010f001450495900301541c0010314202241d40514015201c00c40ca100c045024210641d20741d100202c6d400302440e0490080c25624140200545a405281e40e17039040000440713002e03210181c80064240140841407a2090092513105100c40c0740e181000d0300c1e0800940240c0c000c4d80f04035110105000d0030480401c003400f0750b100e0704800f15481007191906843c0c44a51500080c03000344218284170000d800c55507840340f9114 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 690645125 1250 690643875 690643949
    0x610050d0b0a170a1b03031704231e0607081f0504090803040209010e090705150f0301120c060903020a0b031801020a0e15031b0d0f1104030b07080c04 66
    0x1c07844544103512521164084001c0c0c4100910068100c2103168101180d011030b45d155942c0c023000032102420b10451a00a007003103582002610040e030610707a140510401c50302c0554060041c04102c800c124607019900010003203150009003c121103184c205410342e62200c007070700301c0d000488450100301c924580d950b00311035481403070502554148099140658469482501c03942156602c80f00064174420b0125608250f59008400500483c02d00d6000090000604e001860802d5081c032803954441c0c100f60845d0203104802000601030040e045680e20061103c0e003002c0200302d08540100c0c0f6448214001c21910050000220780003864510707502c020407140000842d25a943d50200070b00d0032070b030400c140c4e2154002da1f2440c21400e07106130407a8000d0310001d00e140411806031072040f069400a541d0ba2030103d03039031028600521f10501900c825050f22040e02a502d40c19440d2500e01144043c01c10310400c0640070130404029008422541503a000c2e103440c1801c41129078031a2420780e11148181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 690646375 1250 690645125 690645149
    0x40503090315072c210604030c020a140d060903050d0c050c0c2b051501030c03031407030906081f0e0610020d0203040509061302070b09060610050d0b0a 67
    0x30500842c04240e000700c499a0b541c0b1400c2c814141341d0210303103146800d0f91403c2c4410402803000c501c0c2c0b0381d00c0d401042c0000380c01c1e0034038500e20041c0b0904021040f0b6042e0040340401003080d0452030f00c00000c802801c000130048205081c100d0200360181041e110042409035141a00418076010f48d050320011120000c0600015100c90742c000c00030f81045c080301d111442620f50301c201600d0320a245400080389c1c500c07041d00c000c1e03c42071a200030b59845c1e80309403018010100780d05031024040402b50b000e1400b55035031a07a26451807900620035001004c007480d40d11810300c24a80001d6001207101d0031600a441e1222264407a0039200713421f06070060b410060031300c016030f00240305407641801500c0b840301100c0300c01c03940b2104007042e625280074101100058104220600492405c640d0f821341000001c0c0c406841d507481c07074402c40100d9002543c20b5034031580740010450501000c105543d0720402c2543c141c3c152085c0b07160060501e00038030b040000c2c042d03241c07103503000d040d02d0311240b0f80010150201c000e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 690647482 1107 690646375 690646393
    0xe01050f090d021002031c18031404090905010b09010504060b0f0c010623040e16060e04090f140622060506030c0306011508130302070e0405030903 65
    0x140c2c0e02030745282214015803144502000424403640040d59501c3c405d1510489501c0410b180c008114206550760101404004401030300941c1410580c03c0c00102c801042d030103014035003061031600d107094040001d024054004140c280ca0a48806080da41c82e04148015989107010300d070902c00c010040c04641c51040c1c0000d102d010705074000058007946811280310107a01c04a02d072000300543c00d5074451149810b11503814540c4082006080e0503400c000d0824443c41d881c4200800e000702a0a0701801d03031120380054060316444036080b46001460314180c08120380f910000803031842820300144010140740b00342c0c0661580e0030000300c100c003442c0d0b40d4000502001004d258150280c903141c401c1c2d0ba141005401d0290106101d40c40755a022480020b00f44c1f90010072034203180241c46122070210341c0110320701040d80d00c01203084a00303503aa8141140b442c412007081c3c9415114070042 = true := by decide +kernel

theorem cover : BRFrame.Cov 690467625 690647482 := by
  have h0 := BRFrame.cov_init 690467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 690467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 690467625 ≤ n) (h2 : n < 690647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
