-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2872
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:59:39.885983+00:00
-- url     : https://prove2.me/submissions/c96a0c63-7977-48bb-8479-248e2af9b4d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 516366906 ≤ n < 516546762 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 516368156 1250 516366906 516366943
    0xa031a1008030306060a1b0b28060f05101205010305030a030e030a0905010315050d0507080d02121222060c03050705070b0105120a0b010609030611030403020c12010e0f 74
    0x1101c042072900c03840140d40044d8012001c018400903103008480103c1824039030a00540b0400094807107032051041103e9501c100714004071001802021140800c0f24411343c2542041807501f41103500001070f1090140314814900544103000e001d1040c1c0081016800d640800d2045595034644a81c2e03d402c110800c0010031700740b0380340c507010910010540e000700301c69640d940803a52802005500500201d81003050707079003c07140c000c609922140c440e080038510400c000e00001d46002c410506181030314071408215080f100c1c141c0000d03000d0405030340165000003008030040e1240d08521041c02c07036400b08810040f252a07059410700c440c0d03a004800d80c540700e0b00c1c00d0100b50388800c000c0302c451040000c010b0186841c07400604c2141000d440b2260440a0042103c541252503202c56041b00002d074464030001d0b0726240c05200700113b5000d4a400301a11600b581d0650070949c0e00a5165a01212084d00540301e000742c0e0754012009400001c50108400251134401e500b80d9952171f0cc50305c001c4c0c0c90840000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 516369406 1250 516368156 516368159
    0x1709120d14011d0402040b03120f0702040b030f0714010c1a0708060105091e0d0c150e180a0506030703060c0207030c08060403021911030105010608090d1403070e0a031a10 75
    0x10f402481080c2802e00c1c0001d104815690360703003000018540016034680620074920302142910400008208862490303403165120101c610420043d2000b01c2c040501a803c01c1c02180c0700388000003020001d603000e0980c0c1848411071200100c51880e511200901015070700c503800b410030000e0480d290b01888050351966241d07592000156a94416401001e401000005186c07051040300310f0010084200107120284c1d050968980c1240241a6003200100302c103100004490250444030001c15054144ea102000714101b680941841c0b4004105072101512200010300d250380c00d010071000380d64041c07020055020b08800082d6140b01c40c1c04125030f0a510540301080039640003c4c1c0303520a40d81507008080142006400982000303c00c501210901182040100f160340d0a006441c00780c20960384050719443d00c40b2000d40f5060700c80c0c080300c040c401c0740e140204441c13908804030380d40113040e0704040a1050340a80494031841c0540e001900040c411000044c01d498421480c40c018030b00c0319030646046 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 516370656 1250 516369406 516369419
    0x31501080d0903210504240906030e0303040f050a02030708071e0f09020a050708040602060406050f13031112390307030806040b1e010906020d1709120d1401 69
    0x5800083c000d42c0c030b80d000c1d13641582600c035841d403007800c0a850702c18240740d51110790104030040029002070f40e0341d620001d045442e40c08150701c4010921803900344400101204110749074400980050020a840300c40601030200801054218030b42c0941111012590b030ba4900d5261492402580c010600c0140d40c1501d0b001c0d42c41201081c1c03103071103904e00e140500d004032001c001d41c041e101000c1030040900100c0d020402950181004004a4024000c50328140c6005030880380010320903440018000b00b44001c0c2c90400701c4916809a2505000800703003601c007455880c004d111200c0c5007031410001030b561511400240c444c00200840c2c01014000001b10b1405a448039107090842040e81c424044400032030321440c4000d030091000391000410760200c50105465000032660601303030350003100009c80596448641040103040f207201416100c948044014038580d011200c000b0060500c8006c140c1c45034051144a00c144030341154545e50300c000c01d500e00081c125444400b80608109000010f26 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 516371906 1250 516370656 516370667
    0x5031b100c0201091e050a0311091012020f031006060e030606121504060b04020d091407540e070513020c16180e0c03060c07050a02031501080d 63
    0x100b81d05856a4031a14140841c0082520300d42888101c10b400c4414000750b6030300d4004600020b103001e42c401c4112080c408060010290014020b0291184040d03000c01410560034a48a411503045440d8141c91074010006458030100b4a41500030030702d03207440041da15400c800041415031040e03050315541c9d91200100043e03a4402d500c41c032541e821000050b8a107011081c0070700d03840b521828001030400744e03031008203040742c004442d07402071140d84000040610a030644500c000f48400d500821916041000010030b2800400350f0503840180807604032074a103410011614000303100da801d5024140c29a00051482010405401d40c180c039240c000d200c84c2c680455844141c90011703029000c109c2c0c1c020141e42c000c0d0b1142501800740c1c080c84600461403080404000d0081c04a92a000710b0324401d009000704607a1011110559030303118901584540e1800b0501c1a40103e00d0b003242c1d91168410305019040801c004d43c001e42c14000c241455000b00c401c03481e0241607031110412514034030300d1041c040d41d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 516373156 1250 516371906 516371927
    0x110c0f01050105030f19170d0203060f04060f0614300f04050a0807020d0516081504050d1404120503030712090510020a1103030901022101030305030c0a030605031b10 73
    0x4460b00242d40131000300303000c1b17606c0201003485202d416501005142018119812841c40710880302d40010920400780340c007141c1008210400c0f01c003000401e1500441c054000414800c081c2801001d5026090b06132104d0b09950484601c0c03081034401c1c6080d01401d041032840c80256906c2c14684a0118010214001000340b149500c00024455001e01d0780707841c2d0482c3c00152080740e000021014003000104180720700010301d001d07602e2805840d402e0107040c60501d844403501141c0c0045c00d108001c01314000140460981c0d140e07080c405840010b03100b50902512a641081015900780c0c4a02d2080040000040d807081015554040303152500e61301e22010745171a800090098ae00004e0081c0c084001c44d8010b05428001d8100001a5045000711a0079a001111a1800d136540459000341901c1501d5000c03d5080c951081001c156055981c0500140800b901108003070201043c90020356010342d0224019050050840e000c2d10b004184104601c80c01084e454080d5048883c00202240a10210003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 516374406 1250 516373156 516373183
    0x204030b1b040323011503050d030c1215170705041d030304110604081e06010b0a0c060902191e06050f0912072d0506070f080d110c0f0105010503 64
    0x6292600c1c41e150b10742001301901120a000080c40008010001c00740700d1496a007510341c1d0040318842c0785040880c03c5c0011140da503000c0c035003440802d58089910103e4510204071300c150010f110048010f91086462254000d0030b0f000066046a5461070400035404088802c211024428041703440c440701001000d40414503916130050000c00d00261000c0222400540b01070607140c2482d0396009014035108100591041c0f080520428071217540050041d940940f0301e141c2414a001c1d502c4070000e00c0051481e0340507122954a00b41c2c1d504558074008072a0a01190060140c521500d4100c075641950050012540c42e50310031500040f00741c099401e480d00346002880e0981000a080c00303001c10016a04e01403043d6026641021449400c450141e05240748601e028045201600c1d40300101120b180d0091481190244004c40005030184c2d80851020b9024402070380b14280c5458030030181c0300b40072409100e080003080110341941c0000f0640c0c40d0a0400000f8446a40ea40040c5904d541c032285188 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 516375656 1250 516374406 516374461
    0x10501030c090e0711010501090618020306100c08040305120d0f05091906090203072d050904061a030d11010f0b0f06030c0c0f160e06090708060d06020d0204030b 71
    0x81204a01019460b644010117092114425000c07441c158210758007604002d0a20390b0340d0009106503841071700e00322041410641c2c01c40c03541c100240050b00e09040724507010200004841c1010400ca0120306803801980e0000c11602c904210031444841c135041003c2030300400b441c101a0010109590054030700415182c40130b4074003039181103195010b0146480c41a00e0164540c0c0c41c25006031002c12880004094040d581c0236120705c0e035240700130b80d030b16a00c4c3d03a0464001001c0003480300341d451440c5981c00940c401b1002606180c200c005001c03401008205980c540600504a250190442c2001c0c2c20798074004020030050350740d400c1c081c0407070f000c2150268002c022605094818200034000f107411200c941026810406128461454014203400843c45030700300751150301e003040d40500900058260040c580c552850180c0200e031240702e004003100c0c10480701d200820001e442d0f01301600070a50b0040010b66495001c40d402e90701945c81032008558800718000000d03c0e81c0c0010310002c1c802d1242c3d2002 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 516376906 1250 516375656 516375659
    0x50f011e030b012d080c281101050702070612110301050f01050c1009020319030f03050624030f0906040503040317090a15030606020f0c040e030706061d010501030c09 73
    0x4070700900880c0140b60612481086a40e101102400000c500401000015102c2481080b000b4800b100250292039040428131507030f080d0807070381c58240c00708184002c6091849038109500f1034203500641c8046c403a0b546880184280613901180c05015200300b0b03100ca40c0c9600a2542c0b14048500c3c0c06444503ca003070500c010320082c0351144a01c0841d8105140560400c5100c0d4001e5003088a0034007210b11860740d492210701181000d002c00642c600c0040c058a40c0c4185645001d8940540f0b40060010107540d00c0c001055541c0c2e502600803d0202c0e030040103c06184520880c0456000703413815150908900c0c0018601c030000500c40e0301c150790040295040038655a204500610000c3c1c252541000070f11100c0f29984403640350038000c011100400070012910400601100c00380d0300f00b4421500300c00f00e0000c5000001a0040d814401a02c3c00200303103070607503400b03070450080c1400200240e060000009550380c030080d0080440c004102c586501d070340d9a48c015000c6440c41a048808101d80450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 516378156 1250 516376906 516376967
    0xe010e06040305031314060301050d060902030106080f24090703030804030302040504020706020453010908040305060f1303032c100b01170402040c1215050f01 70
    0x1001091a00003408440c103058580d074500f41190000039000e101c4440c2c2c024200004401300e0341c031005140c0e0688040340f642d4108004510b0900071030002604103501c41d0481d108540f000d6120100a105080684a179030b45040c1d0042c0d1280e15624003d040c8d28884e84494061103507506c0081e020351100b200504141c3c2c034644d000e84205600038010f0b018541d09210001d0740307450750f000618101c0e104c2d400060f41c40303051003003100c1c4400c65500e2030544030302509400440000031803d10f03a601d4546503c41c2c14420700342d0300d591403180d8020300540c0b106d5080c0042041005000c1e00a41f0550340700302e06841603036440d40704001d4517040464291402082084030040071038042e0b8400d05614450140c94401111070048461503c01c44102001d8140e0100300d9040210242e840389050007002440c00000140f13040340030b840610b0001d040030348203d5a412800780020b000e080c083c0440d0150a80910140d24120301041aa28807441014000c00140d0700000f615071240558503e6a0080d81190030404000310 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 516379406 1250 516378156 516378167
    0x20103050603210405090708090721081602092401030507030e03280201231527221214040305030c160803040e04030302040b04180c020c010e01 63
    0x50070280c0500032032400d000281c004214680c07401200b440e40c1c0d60b840303141c0b0013030100d0604020003060400c4048070601c20820030114010044030f812181c200c501e200140002c8017441d40100c001040d0a1000a15822280240c3c5203400000c3c0200c03580700c403076600e4203ca84208807548004110911413080019060742c00f99120607003100407460002001c400341c0c0300e0649503520040c0701a900a064000461100e002c3d004035423040740140c4005d00170810200034140d1071107140e40040c046014910300041420790030110700084100000d000740700c1c00d001d18011108440880c5812000c00b00010002020034840c0d0b600c030824503e0300300c203290700f00c8215111b07600303500365841c0d0728001c00141500005c0841500000381c400365008030007540e5504c61244183c0e05e00030400b0007010b01d440e07081508103c41d02e000301c1510100d4101d01240c99281d515458120004c0c8036903001902840e402242c0850700b1150606800a48103103504200008203210700160b0341e441c106005c0b2400603100500304000e951003030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 516380656 1250 516379406 516379411
    0xc0503070c05070506210105120a020111100507090e0105100e0d022206210b041b05060f040303020c0a080d050a020f012a0c0b060904021906050a0e12070302010305 72
    0x203078151a0f0a585a00001d511a444402c8002c03c000380c00d49408074102c48014900c0c01802c0440349142d40c1000d00210b40d8948106003c00ba062040303807150200340c075a080c0030311500210f0b6014200494504044080c0c0144128068030340540c038080c00200c0c1c142462260251451013580f10702c4c249003414010000491047c020480e000310010008403900809803c804131510110076000c41c0982c10141d00c404ea01380400c507000c480d1204101d80002003040b80640e1600301da08800ca05003100092689600c0120903540099044800020500c0100402c0350141c03081c0c0e482a03080e204101c4108081040c1d041c8640a402d205810101031940d1a03400b810050402c1d00c154010303102075103001c1702c5090840d41c1000300008090320070300e0100291001682515540b1010b030600c072031414580d0b1a50300410400510340ca005502c03c101007410343d40c1d07031700308001107801540405c29030a45488004045800204d103880c046804030f030326a005d41c07600049459602c040000109540c9280d50011406090003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 516381906 1250 516380656 516380663
    0xf0306062015190b0d0218040201261603052401020705091303080105180106260403020c0406090e150703060f0602010606080c040602060f09240103150c0503070c 71
    0x32440c0318030500c50301000d141e100d020002c0b4000c1215040c007083c5000c0d02d90407113400e0321501000d90303940010f80d40d480c4104100c00c6c5850000c0900c0d074882c8016101515107450000d9401000e182507548044900c412a106409c078030b00100d0641c0c02004d094080c2c0b481030341c203644d0380503084002060748150200c10703d242c0134051044540d22640c0d04046856013a0659900480404070181d010a050304001c0883c0103050071b1b0b071070b00502441103050b205128010b020300d00c1003048005080c1c0b043c181d0b4407106801c00c41c0d140f580758010f04051030302954950000c1c0240c3d009a00b8890002840030880c0f040f4840e50245401800d150080a14527040804004181e031083c150b9402021441c0301c1c0514102014020070b03000000c078141049006064420700a00342104201c08100c240711599003c944181c0001c00015a1030194480d1000b46042c80100088118402c90400d407441d412402c40d2105412240130750081d020415545600c8410344071186004004601e00b0008500421b00c21002850700500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 516383156 1250 516381906 516381913
    0xc0e040f0f0608071401050403080d18290601080c071103100c080405010501050f0d120c12020d080a060308040b1803060703050406050a05040201140d0603210f03060620 74
    0x1c07030260000b190115000031000360b000b07010500210281114804403144242801c60410307103956038100662050346a1580c680d92542c02d00d500c00d0500c0d00c40215095400702555102c101c002074a00f0300901c0904d0411b2650310114007051455028600c07a82c007900e51645107901d0004a601c0302e559131030b0004c1c910380d01481800d1625620b68802d01c10404410f400340d0b40d00c80c043c2042e04206003510303c1038110030310810460030b652420b41d44042c1625a6507a1100350442d0b00c0640000c1603c4120a00d400a040342c0e90440010f00c0c05640800d0301c140e407100703e80700c120082d180c008010301190042d0000414104082000b401020054000350841d890036114411000700c0807030101e0b00345035060342c5c00d001007a161402d11007004400c2c040d103a07010038444410081c0389080d40008005a42241c0500e0030448002541c441610840d00600061504641000c901e40100a10b600c4108c0c0031103200400980080130340d1004034803a0280d01c04491441e07031003001161481559414104412461003258070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 516384406 1250 516383156 516383171
    0xc02030c03031216030b06070209060d06050a06080f030c0c04050c040b1c0605030c090606030604150e0402030609070e0601050a1e020604021c050a0b0c07050a050d0e040c0e040f 78
    0x58040004140c8012400354481c010b08000704105503c41349150340100b4541010041c5485844d030906850f6140d80490b541e1003e1307201c40000c5442c407820b010000d4081820101000040c01540c9c00c010200d410b9a822200c4414a907014180c49000341030071040941c02c403440c1403005180c0340c1c00958101c2400c90300319103441da551010720215801100c01c0385a02000903090070b501445031023814020901900500001c410400025182c7d0200800c0300e031080300c010010441a0715258010340030121248501034510b901c460402d801500c0455003280710303102310030000d262000d01190420858903503d0070540c268465400546454102d40441002c0024074084606200d03500c00500c81c081c0b2903600500782da0700b0180148080030106003440e034100488074140e40002080000c00d410340360f4214840e15110388412900543c94410a00060001c3c0701e942c00c40e009201c00402d8070301600c83d1a444a60380307030500300c3c1400140c46994800c2c5007c0307004030382c0c07001060030503412495000104450000d07600 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 516385656 1250 516384406 516384409
    0x3040b06040b0d030c12050a050d0f0b1206100621020d2901081810020c0f070602030d050114130b010309020907050a1107121707080301060c1a01150c02030c 69
    0x40c590011303800526440354110501c5503202d60310040d0305252400f5807034401c080d00d01806611445400741c00c0035660702e0f000700601c0b2031588281c1296100401c126440810b050140f80e072513000b40e81041a01300a030350300051031070003102c580c41d5030290381381551107541580c08590003d4000004521080c5d8540b103089448080e03400d5400c05041c84a1800c0d1105c028100c001008210000c18462031000d04003d0500100030000d001d03201030302006c030056540e03d840542c10f420071400441280715445541008590309070040003522700080e540c5402c0006a076650050213950303814509454220400d40c210f50104101500941e00b05541070501040303000c0741d6030204003064030443d1110700040d0041107107200360754804c2c0b101d0121103619000b8600103041c034606061841141c907000380700000785002a120304070031200780d40109400c1032a4640b60360b5621006490080c00c01001c4805840c3c0741c5829015005404006050754010f0945031004204c40d5400d95032110f0480017070303a243c0300d1000c20503901d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 516386906 1250 516385656 516385669
    0xb060a0c0b0c160f030201050a0e190213050703050906070e2214151206010e0708100803030114130219030203191b11070602190c090c021b01020a0803040b06040b 71
    0x845100e800d130313040c60b4038803810020708442c409054040440c3c10041403401c0170000040210070540d28078803c44031000c0b644001156070b100c20706071800b9681080c0c204421541c1651220744a12001403e0350041c0d0354621049907141c0b8454583e43d070200200c111006480016001d01444140780c5100081c0c60300c1c0d1010031039804a003240c2c004019420804440c5203030400500340480d03044441c1c01004c1a5040c400c6810002c000141400300300301c5424000b03081c514920800d00010801103090f42c0d03803540c607500360a401c2401080740390b0150307a80181e0314900d20254822201000300310801150f184188100c101c02940c8050800000440080181a502c208a2184e09a1410246d0008040b024a01800740c400c0140803607001d99508040340410042c2d40101c1d107564008030706001d03450051900c0c07400943d4500b036074010031500307494084150000398000031404d0492428141241c2d170300e400c450049a9944842d80c2c0100039007418808240000c405110341e80c0c011000800108940c5607000105d0782 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 516388156 1250 516386906 516386947
    0xb0a0204030f1101030f0216060218210c01050a02060f0403090503011a0f0303070f0f020301060f0b270d0305070212010903090e0f0f191d0a03030b060a0c0b0c 70
    0x1c243c0400ca103003115942c0c052007001e98850354014190300303110b150200006c0000402c0703000740036250000f9201c15807803081402d5150807000140460440403030200c4020141c40401416540380c802d04032800900e41c000c00556041c455154011300c3c01e031761007034290ba000c044041c00c102c6c1440305c0c500340030507aa80d081c000c0c88000006004040d004010003400c000c0340000c82035245000741c0007000010081958142c0d4151a030b6004400e62086d41414804603006200551180601140c3c1c0400031403a001c3c0f0400401881101c0c031140002003485420001821031240d41140c0c0c071100c1e010000000074080c40290084500040c5401410340340515041d080d90104031088001540b2080c00303001d29804800b401d0341041d040d40825a941c0b41c00420210b040d10007500070418412180c03040100342915130401c082d01203101249460380d0391130501c016602c02444008030042410b04d0340c0c420f010b0401a05403560140a580c8031312101d600c03074a4401d02c044020301107010100c4200f00103180c102d40340c280303441d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 516389406 1250 516388156 516388163
    0x102150a020901032003130c03050a030905030f0d08010519080706080601090902070510020c0a150203060a0801050906010306020c10021917060d1407120f0605090a0507030b0a0204030f 81
    0x160b945218400040486500c004189102c20048600403071070142d03403040da54482008481c0c40e115840906100d000c6256683c0300a182e803180000d010105a4820785400440b10194200c2d100e036041c00c25510f40310015018044001000240108031503d425003805580f444030250b00e5003500c0e1103203020b90420400340c105101099841c0c0034442c144d45e02240d100010b0041c00740c00c44c209442d59a9254a401d1042c2c24044196000700d10085401001d10464600c66403066581414400d00303c1c5100103900300f10f5200d48100c2d140710000404072018081e061080d034640d0040d00d9243e0841c2c0c0d440000b50004010396a040c0b080c0150805410b1083c4000c0014041d000d03114484078981c0800140014890004050502c0c0c030700003800b2807a2203980c2008203031a0b00c50856003000f0005c1c800c0c0c610f0004541d11401b8150b100782d606605008000c1c41038030b031903401002d0600180d940d010260340d4442c140e1030000d107560720190080005c05c0e0003220390341e00040980000b40c13509a40351144130300b035603c260b001e6 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 516390656 1250 516389406 516389411
    0x60f0e031b06010f1a030c092d030d0903081303120c05070605042616121103010e0312070309080c15070e030c0d061103010f081209060301060e0102150a 67
    0x2240c610000c1212a0040c1101640e10144e9428000e00c1103004c80050301c8594644404808612002e0440c420b1302c21421001c5d0510420b042c8016440c07546640507451007a040c410f242d8400b0b2030342408074000d03281c10b0f610703100c18684038a151740d800c080380d01c440002d0309401121400400040d1241101244140c1c140c5d503200940030060034030394200b40c0654002414000c00b00000c01500031411000782c1140c0d000e25110040210b0503841c1c0b400e02000641c2401710340300c48200401c003840e42c03400c00c980c40c070b0040114400c050480d0f82418200d81d0084548102da0340140141000c0240c00c95040790721800385c0c0340c08102640b20b07954120b1070b50030411028019800c030b002050f000804a0210980c404160301e0690311103400003011035182c3d0652203016009820a0031414180403a54000700f2a440c84001615507960f52204080c9051043d400350076064080c407a1000b04040141050b181030b10401000305145901c0c041e01980c4124580c1d103a01d0540c002c0d0340d0314007130306081c10070218411507580d00301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 516391906 1250 516390656 516390697
    0x10804061d060115020c0a0608060102010e0706020f01150e041b050a06080402100201140105131e09020a0905070504420908070e0109020a202103060d060f0e03 70
    0x80e1340780c24510361401030455001c80b42a01c2e0f41d0b515030310745404992450030303c007000351a1107004034050071101003412280c2c4544440012030541c0020800030005900e0020800100600c1c41ca141048092050300303040300c44140828041156889010442466440d007126055034a10100303651041507417144021800003c104001d40c00c21202e214002540752008000e50704940e20f1100929106020380d134011488041112030b40c1e440f0f40d0044d0000820200d40d6144600c1c019011805400032500480c05101c1800d400074195205000351801340405844450034a400c00d410303011450602d0410004a041c6c8040750071a0003010350341040240a5616517054641c01800058251141980700c0036455000580c1005030600b10881036040d070304440d8001da900d01c0b049208413210501303156180300000c016050443c05800024500c8801c11241411102040110103c03410601040f103640e9000010b13242c2c8040043c000354000d064102014000040c3c0303420106a4070f1441e0080c0e032001c0400780c4a20107 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 516393156 1250 516391906 516391919
    0xb040e0609100f030309090f2018031b03011b022e0507090306180317150a0602070f0e041509021309050703061805030a03150510051306050405060405010804061d0601 73
    0x210b1031510030a0f402441300243d28024201f05445541402c45002700106080c003500800c07100d52000400004c00315902440311650b000b1204101c2c4912a100c7d40c07a00c1401d00ca01080c041d1040b03c44407103038028090002100007104904100c0e0b00da2003844030780340d6000d204144018402c2d0b500500d1699110f0003002d04601c0c1844c200c0385c210303c0b81c03551030481c0c25030440000da102c07540384001c1c5a091950200ca0b16014a041040e4a24a1100f94842e031440d101103401940010b18804441a171407030350b01101d40c1ca003c4401150300a03540600450250303280d078008908070b500101106d034800f40802111403403c43c0000d044a0303012500701c805030031600c020400c0c00564090403006880070031046151944c0c80d130300d541d034038440c2e081080241500d4128550900380d41c48441c40003820050801400704207001c000408650181400000c05802c0880100f007043c490780c251004da43d80500014605414040151030160740244125041a01d0303103002082900d0003010004500301510050503194100342 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 516394406 1250 516393156 516393161
    0x3030609050112021c020d0308040b0f070c03030213090507020a050c06040b041710020a050403120c05031b072402100506030a060c0e030a050c03070b040e0609100f03030909 76
    0x10312424005081c00018440000251100c00c01194100c0f03c40700d504d0300c1d4160700000307504510400f9510140403100901450340002c11184103511481440c1d041c0e5448104103500c041c410f5803070100041d05265000f0001e4041d500502c0b444003104280041d2a40d00e481c010700340ca8040ba00c4a0043e000585140200b01c0c0c10400386a000340b0486942d42020b0420410031014080c5109005084c0005204101d200100740302120303036010302d403400b50354440080801600542c0130384412102e4032001184d04c0e141034441c901c0d5003070f82ca40c09000386191130b404102400c14980c2c03140c504540d5020f16000050304100c5901c880901e40a50a090400c05c2006440070b402c020300f2441034102d0074109000c0015682c0c01007641441e1560010300000d150b669041c3c222480c001d141e858941620a601051040c4031001803420641e810440407510143e450300c42120060140f4460000b0000038500403890318500000381990202d10f0520140c000c40e0342b401e030350552103600d41c010f8012840f283c0c401e0100b6581c90 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 516395656 1250 516394406 516394409
    0x10060603050c030a1503060504110f010203090306150415090c0f02030310230d0c140303070309031403070b01030803090105070e0f21013602010c0b0c070803070804030306 75
    0x1400d04000924101142429a210082a83c1106a92221011a5460141c07002c02c05107402040070040b500d440d00d02000d0042d1072002c40d0b881462000944200c40d803002044902c0000b0107030190600c0e80702e207003140c10700b101444901c0740c0c416254200c0a951203c8401204000d01420001081c1065035541c00b900f2901c8982c440011504100b041050403e0110203040c00c542010034807600880914080301c1c40403103503030016984541180d81640500c690030300300310280c917401010752010b9146442016505d00c03a0100080110f81c0746d4100700301248915404480e6106c07101d0990b8640040383d6500b5a805109070400c5601c614040207100148034240300e0381d40d02030002c1c104070840c0406580041c400200a000b41441081321440040c804000a000c545411810034028055806030102d1100d146070300e140200d40d5060401c49241408203008142e0306815010384038208021010b0300c4104a81c1c1e0004c12444a0007420000c00c4002280d2200841c49a0b00c4c0d035440340680e045c1841c004080d01d049 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 516396906 1250 516395656 516395669
    0x1510060c02010f0c060605060703050d05010f12110324070e0f090a021315020c010201180b010e07050702060301060c0b0a2903070306020f1e040b0313060e06091006 72
    0x14500310010303604681d485000c1d20082c280103c16080b10300d0100c001d4402900712503000071010840745c007055013041c06410022a5943c091006a89a400c03c0d00591424490040302c40c0d08172000502280d1500c40c1c1c01080d08000d07054550b4078004585c2801005c11324140c3c01200e41404007007060300360b8010007028004200700c901d4075166501c60002060444040c004000450b070025800d10b107000d1782440b0a0040500740845229203a28407000380d216074803000110301550030f28030300c84d0031004401d440c8000305d90b11440200d0540d0801d8070740314225074002d1400d81800f00402c02e040260307403107030050340c024071a42e592004003541034030703045207100e60140070781c543c10b401c0c214415220011101543e00001007a04d8408010344140c0000349806803592014007901c7c40051b284c45400010402070071402480c040010001e0002e00f1305c40e00a201e070f44540d513103451050020a4428900300e10302010b0750f004060100741e18030f07540021414410f095a070520203901141d50035856803101d006240c0103108 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 516398156 1250 516396906 516396917
    0xc06020303161b02030a060c03150f0b1608071b05030d080a180c030b06040b03030a17060406030615050906040c02120309010207120509012c0904060e151006 69
    0xc19454a00155054400380030601c80c000319030240c1422051040f80c01280c0080840717036208424105000101008046040080d042c125000048003d012080b07044500455500800c0b52600c0300d4001c20b60401e140c200c0440941c10615400700b07100c00c0150456070300030003441c250300158030404190540030350b1015000703800c0072034200c1c51680c001e01e9a0342d10036140700d004a64685009512115801c4d1544c0061060282e4131000c010300140c0001c0c46c1c4a88030a980c100700c20002c1d0307000c2594a014480c050300000d042c8071401318108001c171191303036000030014001047c043d4880e03179501c083d0340710340a043e025070303c0d600c0e4100468a410380660350420000c0c1c808001072018420000e4848000305900111400b00001280c40f00e0303401d504460f0b0190f0008581400b0303983c1031800410540c0800b60160000c6c110040d07209181c000500c0c50f0b100403ea90628168840507070080c0701b4002002401610072903030340ea4000c0d513504024452598120301c4401c4801092400c0b445404c40420300c2e030002e104000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 516399406 1250 516398156 516398161
    0x3080a0f090605072004020d090b011d070e030307060c030203041109090c040207051203011e270b0109080610052713060f1b0f0f09120203030d020a0504030c06020303 73
    0x150004115040c040e00403219170305843c00d00076200103d403441341046400510024136080c102e081ca9001c1c0c013000b44500c942903490b0b6a0b611015808484c3c007048210f00020420205007594018200c40051078009000d813410622540c41d40310480340c01651410100ea0004200410084280717000941300000311203421050922415003641c0d02201e8a00c00e000380d03400211031050100400c180040c0c40e00303800300f2950342d40c0c460101c00c0019034a041c030740d5a500080c2038045040c0b01080b40007080c624000070072074056005840c00c1c02c05003110440180c14030015800c0400c2d20602404064418210088a07020700d80c980814007803111586110a400c0d10701c1c2d2054924190094443d140d00704d100c081c0382804154540c204240101007070f510f1850006c2c5007920a0881400f0072404145400701ca4aa003004041d2002059814180f03001c100000121a0441031000030070321148580c0ca90300290840b400c01c4009802c1004990040004c076001c01c1003c101001045450b01a150141c030703261001c2c41c20350 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 516400656 1250 516399406 516399419
    0x90603140604030923060309010e0715050703203949030f0302090a270203010f090b12100f0b03010507080610091a0a020309060403080a0f09 62
    0xd01c14022040b401110080d454021000d01d41805d5442c10028030043e0740b0300704000041e009000324a040c0283d1300a0714000a1080d0411428a048810380c1d201d4900d00049a17070112009011a0301d035268030b41035a481040e034500104003400320b03032841540d640d440c1003140d02110311a01d102c21942c045c608841007100b525488003c4080035018205105044e1300003a940141c000d07150301141d0100551841c100038226403010034407114201c1c06600d5180301c000f50940110280c2c420350744d18070340151013284100040a42c14400004200240c44940c440c903605001290607a80700382c0c890161040d9a20f014808c00400d44900b40c400541250b07100080305100c0300c50b07500d0b130f81c190084203d4035a07074040030740c4181c41a1704003041489000b4000c00442c40d041130050901c11040e501680610445100100d07158051044001a6220b55141095811260364100c100364040c84d1003100314042401400a40e0f100d1502030005584600b00150310342c9205040145440711081c203800c00c105014100b080301 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 516401906 1250 516400656 516400667
    0x60d0912030509030c0a08030702030c120a03050717040b0705160f022e030506010c061811040c0e06031801110c010f1a060705070b0d020c010501050f0906090703140109060314060403 80
    0x80307c1e4080a2251203550312181a1700313602a0310642c4030315000e0000c0c15000d04502170014003641503607071410842038440f02c9040700ca070f0003a040d00c003110302e00540c0444c001c103c802e08050340c804081d10b000c40c41e1548844c2246000c4c0e42200c002c0302c612800c400124110b03c1c140d0380d50582c28010111403000120200340300710141c4680b5220200b03060b0350f000468045c0e44640780c07055403030307402000c140100182c40c0b103220310780c0c0d128075015500c4220a989548c810308c0c050107202c0302003000d43e0b1b503288015801800c100a641c406401040e900c841b62001d00ea40410a01420000c002e03e842110b4031100034441c2c0034299000043e00c40e2080d85030130303445103004103d1101e07006602d40030745155495000504e80039150841c00c0d008001c00b00e030301091035004104683c00400d0382409a00c028006c99986000f84401c111000030b280d81c1c07110b038000000c3d583c0c0c01c0a224856001c249440c0100303030400c0c244080c0c040312400703030007590509447d81418130510035100c0034900c211900301d00501e580c0c41c0c192030081a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 516403156 1250 516401906 516401923
    0x5030604051509101103010905100302011211070b070201050405100e19230706031503020303030c09061e181206010303113901021b0906060d0912030509030c 69
    0x10b2040442c000704108000400040d01842e02070303141000118500003c80109800034030401950a0038500015a0342c0441e0709200708995041c2c403020203050407004c041c009855403031160071004105011040100d00801c034680d000e500e01d6000003e06040c9410084d040c00c43c84c0c1940c17002c0030b0070100b503800380400000b038400000080d0070f0446444105440c2c445103200f50311480c214150818954441e80e403001040d00c1c8101c80b0030744c07020003d10051109888403e007861202a505400620004445000d80703001005001d100030401840d05040d54040340d458071050441941d800c20210b075910407142e8070007480c1008a0121100b51000210418607540d0b81c0701400000c00b0414070803c02101044200605030b8000140310701d501c0d0b0500128045491103c68200e2804800e0a03a120f01e8800d50000c1040421302c80103040b441c880303806800c10300c18400c001420403a00860100041a01001c05205401c240d038840c8408140c420351000f0001c0130303a60003501c4081c854104000800111600252944 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 516404406 1250 516403156 516403183
    0xa030602091c1113020c0307030806010905041401092706060317070210181d0a050c090105030c0901091d100f12062408030a1205060a120609020a08030c070503060405 73
    0x1400c4c440c8418880040d010340f107124079062002041034010182c000d004148503003001c3e030302c091074555140308000a07595500c51001d0820301040050100194907002480c485c40480e050f0382c03c50400c080c1000360314a2508041d51a283c1c0c1b2401801040a44400c1d00640712151038a141000003d4000a440b6110105076405012640c040b13401da0a07035010700740c002408901c4124400303401982003400015011140c1000752450240000c1d6805c0900094550015040e920203095981d800040e020300d9000c1c2615030306129030200000345150900b41c1c8508690030043c400d0801d1300344080c1c00c442c07030100f58010036a61108604148803c1e00319866440c0003e80044000c1840f4001c4501d500705400d1848034050160708040000c01c1400740040145120030042d03440c00318003400d006c12103048070703410b030f400c40c0c2c0c0a80107071401c025030001041c254110a0042800140e41c0320079030f0020300400c05550040c000380d00080f484886ca039206105040040a003034001d840700c0d241c43d68400f601c581d010318010 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 516405656 1250 516404406 516404419
    0xd020901060315090c0903061415010503100b0307030e0c010f080601230c030307090906053d02010b0f011b1e0b07050304120c0b240a030602091c11 65
    0x510b10310441100f030002821012800c00c4080142c5400078007401c018002a51820b0400442210b885216126a03109101142002201800b80401102d20740d002134990303414414a00b00c0030880d41454001540996050349002681030b8003000100d040c07106100445041c0013040c0c40d14070f5940d401c8110301c2d41c0500c1c2403030f01089140c18002400d010760101d10000c1409100820696134030400000298054481340e21200c00107a80c600c00b01e000c0d105903004143d00512525911900d103407940e0010f901c215114500c0942c0440e51101717664481142d881902c0041c0e44a541569550030320030000d42000b002840c0030205603654840380241e6000c90721004286003c910910342c07411401c0c813020001141c1c1b040c04a002d600700244014810303001036800740c41043c400c1c1081c00610340141600f082c1d41e0351010100c81c803a65551280016103000000b00284810110b0411440fa41c3d165140000386100e030400507100d108040c144400d07000200105184c902c0b14603c00b801041d2040c2c00c03d40c4551086908 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 516406906 1250 516405656 516405671
    0x90905070e090a0905030705060a0e06091b01030914060105010305010801180210051908040b0106030e0a0f021c0b0109060608060303041406090d060b030f0c06070f1707050d08060d0209010603 84
    0x884010321130301601601c20f00011444000b0031001140d010300408152130140890b200700c1800d45d0b100d00c02a00d41c0d5015601c0001126501d02901080d5048410141400203010905440d083c0f652100841050b005400c0b407001442a0741e0941b0034140900001c000812507044800d0304090600304048020b4403c40310f0b58100d880b0548a20102d0f081903c814241d03032000720341090080c0400e18240d5007210000c0300c2e6000401d00c523101c0d10a010000d44614010100d02c0c0c0c29813a580c8030044c4082d030580e040714060302d5150601008030411100740740b0800010040351b160071345100890300d141c0c02550401040d4402c3c85101e82e0000b0584081e50f0700142d681013403c80b00d8001070114030410780080d40240034840e10405000c00d0368056038090806505545132203404900c4540c4682107185080e900c00c03800d01a403004905c028400c40c03801c0d0f210b107404800e102071061502c072980c1c012007000ca40b950b00141d040001190b2183d4600e030070800a4502e80d00c4007525a00141c482181401000f04059030b41c3d00313 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 516408156 1250 516406906 516406921
    0x310060e130606110f01111b0a0c14010810030b1801020c010603060e1605090a0c030e031b07060203130611100c11150f040b25030c090905070e09 64
    0x21094031078400780000c0044a50b211000380c00030b020070030101d01d203014001402c881c1c1031043c0201ca85c840880341c1103d25090a40301c191079070300b540403042e44091041107092000503080c1d072a0a0050541d00324456055206d080004003540303001001e0008c21702c0030603420030008020030450b43d0480c001103641710402882d00b0545009000f000c0500b01150f007442c1001050100b80d901c500b1921800e903041d11802515108014941481c82c4103840e040030500001411551107030f44120003503041443c0100e0a079020380401803842d00304c3e294250380c1c910340700c0c4908000b01080208034000c0c000c40c006903050100003254036000b0a054802c0301c080c41803400f0360f1030004000b886103001380700120b01c007000302009020004010702c41040be10740d140d1190f0480d035000f40301e041303844c02e105900d21314040510b40e440356074200008401400c2e074018a64041d00c0c10b03481001c41b500f42404c000707059400083c510140700008100e014158026400c0300c2c941400d01115581c0981d42064444040d02c3d40c80107529100c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 516409406 1250 516408156 516408169
    0xb0406091b08060315130204050c180105090d0b010b04092d2d06080613051b03012003060a0504050c07120504050303180a0f06080a110409141603020310060e 69
    0x70780804100c1391a0108030300c0f002688071b140d29440c001c4e00c0400c1b1980d102110328890f441024001107080003510110480c5601c203500034041c3d00b0713002d029060450030f1a541c0340440f90702138100c8281308001190901600780303144100e07046400808060101d004101081c04048110400035600300c07a140e04945821042014024241d0860102e814428201c8100c50070000c0907140030b04845402100701107144840c1030700442d00d041342c022002d0a0020010500760001e10480d1460303e400d5502c401c925503141d15a00761003480c002090708156030f207140080c1007252074400c64112034800c61a003014001d54891100c140c031482c0790300648403068400500019691401a9803090350b1510000440e03401e002c401c421601041041555050070140e01c40060140b800785a010b02c000045515001601c901100d03040303000c00e103409600c0300d840c107512039006030300f07540b8080300d00745a220062090000a441c190070340b54560703038036240450460804800340202c2031071901c6120100140a03c2c011074555a60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 516410656 1250 516409406 516409423
    0x40e0a060506040e041505070e01180909050a11060307050f1b031c0b090c250219140d05030307030903030219030518150f04060b040608010b0406091b080603 69
    0x400382034907070780c0d13841e0b0038010300c0b008641c03c40b0900961501800025200d015140c0140590345400b400f60a11100440c0d5120440c4000402c90528101c00a807004d03643c496014860f02800107002d180c40705080240e542c070100510140226410005c020b900c40e48001983c114008044c5030654a00d03910201801d0300d001010b501c40755001c0065140404030035051005192220210244106a106400c2100440084072000e204d200200301c48010b0041604821a441400c07951154001c9800c0c0c010030b44c0506801403083d40c028240609002c40101c42c0030741854110201c4140c4420001641c0d22a100c2c00090598014140c42c2c3c10910f080502a40507140c403122000071408800a501c0c4000b07000c2c01054072007401031110a04007403c0b090000c2741100c0d018801c034508400c541c44035200440d440b0b070000c01c10b6600719518402c032007140d5120b018500041c44600008130308580300c8010001150001c0d4030000544d89071158400b0740c49480d0b90703c0003c076455400e007040103640d0f480c0800e0801d5900b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 516411906 1250 516410656 516410659
    0x15060d0609051b1e031e0108150a090c0e0703020403060510151b0314090d05011e0603030210050a020903060109060e0708070206060907140438040e0a0605 68
    0x30404045108103503a40082d204400741c84001c1c00c2103d4410024400c1c0c0302e4202c0c03580320f1003508001040340071600c1c001581c2000c40314a0301c0c40d41310207208034001181000c0e00b1440c00d40d0000c08030410005800c40310030b03800039000310040250344040d5543c0ca4504070030f07129030030721201d0f00d0f4006844203000ea4155001143c000c07100707001d28500b00000c0461103003140a4441ca0810140425401070720512450b11607c060010b80c16108203541c900b590580c019401e101c1c17090740b0402040c44a62503011003140801d00c43c20012841b6202002040004414189424215882c221040010980c0010b200680100c0000001840d4540d0480c010103440b815140c103400d4410000006210070180e03001108642c40c448800340b0a8030b60103030844108c038098a42000603841240410b4407403809550854100350142000d051078031401501148a0308150f02103121002011107021315098025200341901c10f6000000140c004d08042415890040b801030080d1a8420800514201002e0f0f02c2580508170 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 516413156 1250 516411906 516411911
    0x303022710050913050c04150806042703080c040b0403030c0b060109050612090f07060e010917070b0d02090310020403020f100813030c020d140706020d0815060d 71
    0x5200006465401515462030301803403209040c405007074401c0d403c2e07400c0c5030700050200485481074000c00019210283c02c1c181ea2000801000401b80078050205800150300c0e140da0b07007189440010401190700000306080071a41001590711207110503101d4800305949030a01001a4442e03404000050050350881b84010000007030100902d504001161007644c46820814050790f280c07001102d503c4914030800d80c002d1024454440e5210104d104070b03512041c5001151541048a01c405150290f150300c05400310744230115168040d6403080381c05001d003540c0015040100c120781c400b240d80c0e4103584940110b840c0082a101241840d903012140c40042c0281203800d003035644510600294000d02c4201d100d026601c410282a040c1141030b492002d116440e00c040c2955420009811801e02080840400041c03082d0440181e440e1040c07084042e004000d4007819610140d080c41c0f6020241c0c0001c0f00390b600c9644200c80c0141d20800c100d51000074176010080b01046d086c04140d4038010030310314809a60 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 516414406 1250 516413156 516413197
    0xb0c0a093302010c050414060706060314010c0503190e250e06100c08030a020708030406050f0603150c09130c020a05071715060307080d050d050f010b16030302 70
    0x201c28040318600c009010180040460741010181c1c00c03681d000d003004011400c10f0100b0460070465088400500c10003400b542e1a052940d921181103c03101c1d0000c907407180b6040f1032400d00900074490f4006429140c201340c1d1440c240300c100c0350702c00922306101d415615203070b980301d41c80c003042401800c0d074121080381c0e4045542070b600345c480001500d41c064061a4514400041c2503844c00b0f0f004a542c112003911601c02e60790454807502150b5000800d4544403075020001e01d400039410400031445107000745400905030401b1454809102c0014040d14840c0d0300c500650101e00c80645055500002c0000d8415541e25819004c0740720319071140b4881a4407894010707007100d4035802240310b88849105a00b0b031940c071512100d40044118141111001aa000b41a09010020041043d41c1c0100000f400c41c1d1485d541c545d126440d007214540030720000384000c034a903206102c846c01800e030040f49918500710190705042c0b0806c2c05008021446200404800101d010305000341d0440703a10a204404946001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 516415656 1250 516414406 516414449
    0x82109040504240912142a1006031b0305060a09061b020a02090c0a020705130908070f030905030114070f090806011409100f0312050f0d1d06040b0c0a09 67
    0x3403941010139a41d45d101c800d03004502a10840c02d42c036400320031552842c286558403c0c61010b00700b1486803403650344000800001c5600007001002d030000300704003002c98080e00b10310717002c041e400e045403100340c58032042c0405000142d00480c02e10b5006045c0400000d207078031a402d01001800c00201810312480703440c2c00960280e640804c228503481d0080e45d0940a5884200d41d035541841101d00920045c0c01c40303039084c0312628001050410080410401042400c015150500c066110724802c455225078100b10301d00b019007000128001f048114002c006070810081e000c0c1101200a18410820200d02c00c3c03014014010803460015104c0001100d48940c0c407124130724482a074051945100e0480c2000044a85801078450801e40c0c0250340f40c07103182403a556451480d6001441900300f4000144038580001c809038015140702114140040f99030741134180040b20100c20440d6200d61500310408120102d0082c544103504040c40f00703032465030354078040000c841002141c1c000150000c541c4070b0000e003070b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 516416906 1250 516415656 516415661
    0x1b03030222050f0d020f040b060702030724020c03121b0604060c020c1c03050a090b0d020a0f020102090d0308060a080703060504060608070f09110c01020d0608210904050424 76
    0x180e802c191410081200c503142000380304200c25400030341c0180402000b00700340c2040e0304a00301550010301403034107204d500c0d0300103800d140319908040e01e6001143c94001e005c2451000c06940d011181c0082d2941c1a18500440e4a418200c03202903075080300001c0c2c0343d59040710b010044068a41d41c00030b8331140d080500c0c10b18040c00190340c0900061280f1084080725107803c20040c05c5071102d1040b034a584039402d030703410340e0141c01044c011001e1200303100c00003902d0692000244851841100c005a58500c000e4000d000c1100040603202103a00c103006165490316050014a070040d058145420b02d60765075400905140c019400003c0580a55000041040f206400c03060140d48520801d20089803130b0720106656101034400c1020340133040c0010004404a6400380e03880401150000b85810340340d020117800c1e81d002000c402d0800c0e07034408003005001d1050007030311307500480303164021800b007058044400b0354020a1816131081d9901c0c40420300700000400c080903681584000920401540c4203030400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 516418156 1250 516416906 516416909
    0xf07060e072d17160306091e1e0204020c01020703090911092110090308041401060b0702190801090b0a0515130e120412060b0d031b03030222 62
    0x204941c1141d14424288036100e21421002a030340e6000d902e860072803280c090189550300d080c0c07140690b10210f01e1040c9180b0340e1501440c099800400c0114481ca003a10700705c2c01900c3e000381a00c90030f01800e800103020203e852409002020940e919400e24000140244507250180710150700c00034480c1c0400da040313820b232011244003138401c010940f0110b490014174030030214a264011000c1c42100d000500c401c0103201000c40000c2200d01080c4010614011500d440e074003a000b040c0c0100410003089442600c0441c9200c9690003880300615010401d01c580c02070002c020710030105074040c15441d146030103400000b402c1040080c031104031142401c8540c040160303081400d29042c1000101b454111118401c8074036000307841390404407500c100c1c210040c0038060080c070f2240070366010f4000d00048607000d84058007603007442c4002a041d0307290000c2140e1000c44554020004c48002c0300100760090540400310118410084c402c42141c9030440c02481101c280b5a01c4c1089880144500740741c2000c41d00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 516419406 1250 516418156 516418169
    0xe040902180a0c090902040b04120f0602070f1217060d02060705100209131506140909010303050901110c21071e06091217090a0914091608120f07060e07 67
    0x1580d21540e0681c1a8487c50003042c407440d10030403040046000d4602c04030310a41c000d104d1131800307540f20341c0d450382642e2040780c2c15100720700492004010301041c00c0d4008141100c40c20b000c217045058036001c0784813640c000c007128401c4803403226076410764441c036041307e00b25540700055403461320070f03116a50001c2d040861264002e60b0180010403080c1000d200c0c00456580900304000403518200c0d04803034400038040030020f0f90400b4040d032031321a11000c14580c061072282c0c8456455424820004100300e140d030845a80b10b40c85211921065128190600310f484034102c0756110302c080010045280010a500043d4102040c1100344200d00c1201d042c80c05a54241d40c03180007140d55001c2c50100d5403c0b210002c1c14a40d01c02c0b14200b020040070005091842d0b000e803008011350303030303410720101202d10707001140f0040440f840c10440515000d10403943e500c140076407120211418100c0d0b44d80c0e9088904003280e0b40c02d00001e5400e1900b00c4000030703603104070340c0203100740000402070346419282c070744a00c43c58 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 516420656 1250 516419406 516419417
    0x30f19020c060721050405060d20091507060b090117010f112205190302030d05030f040f0507030209130b01080706210b04050c180d030e040902180a0c 66
    0x80304514100e812141d030b890700f0045544c1608019007a00c0d850811002d0769400f404010000003c0c00d4595801501c0e00130800800040c40001990603a8034410801074403078031105040003d000255158000c200859880d54030342e50b100c0ba01d074640705006004010241c1d60002c3c1070000040c0c00c040224002d4050003c20000f8030541522900036003d40301070713030002403c8074000d0224440541d0305e42080c503020034600c54040012680c40010400040040c48902140e050030340b0144190304041200340c415503601d2604a223146012003100d81852000b42000340710600c0e0150078414400100204070185400900b181081d080c44440f00c00c000c02c02420403940007601c07400001380f24001280140c01c944464980e46840c1c07040d200c10f5035104001d00c16150f661030b9281c080c00c0f00e41e1a08e105007407086404d040b90390343e69503000c0048040c0c1c1103424480c51080e10309840b0350002035030020a1080c107d10a56002c80c1a0071346100090380340c3d0072805100d8410300040100b1090118039080070040c1e500e40e4450 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 516421906 1250 516420656 516420673
    0x2070614150d1109060103060f06020f011401030c170f03030a020d0b10050301050415090c020703021c021813051606090807050603180f01061410030b030c010e0102030f1902 76
    0x50241d8829202005040d14100054400d900d0402044c0d66500800526000440584079402c0c40d10050081d009500143c0c040b01b48500c03061000d108544002842c070300c800b80720350b2450340c410103000c2260145007117846440d4800c4150035030402804050140400c01e585e00ca1405502d458025008010581a400d0030402c12a8071420117080056148000342c3d5103a181d0303800e0009000103441d1040292031444d181807000120314003188240b8800c07045650140005510714010001d50341c0c141940800d84840301c400a4005946049100c7c409081c0412030201c20b03501c0c282c00b032062242941c0050002d004810f8844900102c602c071450a50b141500c0e825032540d100c203101c1b036550000b40505500414100041018245100b806509801310882140d2200041c091a03e081d120107500c0780e0810694941d070000b03249807032094440c0381400c43c5410400d00b4200d0700003a07030f10340e05903040c1030611000348183c040d164824802c5406611441807119650543d020405042518504580300180100d050307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 516423156 1250 516421906 516421909
    0x80901030614010903061a18060a0807060504050d0305040b1602130e060a0203100f170c01030b060a08060402220e160503070e011e02032d070303020d0207061415 71
    0x101c00d00c000d2010b13034504071064115551200200b01d0300b241c0b5028002c900c5051859640d41107000141c1481c0d4000503903450800307000340301c0043c819811041d07450f0000c282c248580c0d03034048140c40031240c049031480443c281c07509081d100361180d81c000c01d84c0b1030000200e0303d5803003030030041d180d80035482922940d03000c94201c0c4035001110303403e400d1b1003040e1700042c0101d00340b801150040c6030889050002c0002442d55803460130300400f501d62011804118041d45988500814080109210020b00781400301c0d1200e900064168400c0c244d008060003000004118607803220340c1030742c03600e401040f007944c0403000c042d040003141c0049208541000d2090400242e10b15a107031942c040e500550307102c0d03504680340c0a4041c2ea8008036144242e0400c5000c4040d126904c204014009213850705802950745c84441900d041c0c107440c40329103152101c1441c0e010008502e0707030010880c1c81c1103405150040e11950445a01e02c06403260100141c503041c02c0088446031b04400d10000c5000d8021304e0309120580d80000c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 516424406 1250 516423156 516423179
    0x801020901320c010b0a06020a030e030a080403030f030b060c01060503010609060311091509040c14150307030c0201021b010507090e060d080d0b03010906060612020418020906040906030809010306 86
    0x2080030b00c60001038492034003408401c10207095260304400000c40d4851120340030915400f01c5a100c100164084c1c8044024940c0015251030b52002c00e40183c0600021078a400c2030a20032440003e04008800c907032000c45500c26444040e001d5402042d041c3e80d500800c4003503000e044c441c0140da1103546044000158401144109412264003030180300c10344c82204208040004000c218250301c442c441c503400b0040d61503018882c46a0711890b120f90840341040718118400104a40440c05408503d81187c20340e240359055a40c0300e001450042105040c45400702d029002c0e95031003414074500c0071421512101c040d04181d1040c8131565801ca0075940e01d0001100300041039407810b07040500090050046481e0a0050204d444800300c007160f005e9052000c03070308550006105442d003036034a8106105036075010800c03914000060100794200703818001c56600710b19a02102d50603c80d80014224401d445440507500140300003001000616a42d08041c000b42d4010120280001d14001c0d0200c0d0980108 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 516425656 1250 516424406 516424457
    0x2070f05030618150705030406110a120b180a0c14130b03100308030f060913051005040f05030409020919080c090406110a0504090b0105040819080708040801020901 72
    0x20300515103a26002900f003540296546440c00074002e040c1c09a00b501d100001040c01000e050f500d090b0f43c0d00d011308011046429000700129480810410f00404590042c840010265604000a003e0700c1140009941500030380310b228070b9100ea00b00300400c200c5551b00a00c0c40400300d8540f8080c0100e003808440851040402807001030b2401c0c00284500c041a5001e564001d0b0303e10154115036442e0345401e60f46030400c60703103207032813807c1d0a0401000c1d007007807444d0036041409500303690680440f59030780075107070b07202c902c50b14515540da40002000e2001c01406804071641043c15030fa502c42d100c410304401395202d880224020010304502c802c0820300e02001e40202e40c05900030f00384050800c07041100200014100b599900d484010141c103510300b08008244402c02e603240d09503030301d29100c0c456081d41c0181c600141448070602c420404110040307010101d42c1c4101e1481c00d41281240f2f0001442d004002c40601440c0380481c010419620541c024040310f4401d0700e51110301e00117290402d13200c001c036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 516426906 1250 516425656 516425659
    0x11121204060507050c13020a02010608060105150c010207140d23030403270603020405030c06031003030536030606040e07050f03100e010b0909030a020303010608060303070512030702070f05 83
    0x30403040000c280715401900c5001d11510a03107000c0100c1c040002c4400028004a001043c0d002a074410b0241c4c091145800520103c000b6100755850b2000080c4d515040d200001081240000c3d01040b541c800e5044a45155010181038661040c0c01e046c80d036207100400503440440c5c1d41e078411584101e0b42e00410091002640c40d61891a5100d42d42143c03855510890075403860710341c01d608018010070802c4030000d400d00355801a1224034100030103140c03820120030745001d07400400c10b002001d514840000c00381c9405062081e40c0c0c10300000c608000d601c4174200080c02d0644c46204000402554060032414030307084045031182e480340010442203840034401c1228030b40c00280100325504240c1e0500d607036041c0c0207094480b0075842075000004e0715a07251006916940d900203170880d5180035426a600103c50000850801080700c2010f903681c0700602401c018031151100040e1a50760400449411650080c00d40303040b10018020040a80c0099070880b000d406a103c010034100121890314080303030310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 516428156 1250 516426906 516426943
    0xc1208090103020918190f02071707150203010806010906080d0f080c090909010b090c04180203060a090903030e0606190308090a0803030921030402031506040f091112 73
    0x89040054009510a01c0c0198004400306040c542c0010700039455446508040c00360039010b251003003030b04102c071f11000211014a00c1400300f0b03c085005412640f0703404e111400c40c1d076600e541a0824600f40c40d04901ca000001340000004500d11502040e218101c03001c141c410301443c0d45a07016039440e014811800030000d4a10740c003450070305114940154006c3c806c0c00c0b501740303410f0141022a103045002c0f1a00c3c0402da444d50381400e084c0c02e0518a44c0d0744030005041c000d050a083c41c0080b801140c0e07480300c082c1d405402102040c0699100022a4020700c0f0900301001405c4082c81c0113000b13040c0244e901c01650083c50700091040c14144e550419901c0d245024009440c103555541c200d680002400c190000d64940004c6000d02c0100004c500600303031000182b0104501c060311a000040380d00058049150a20601005840009440c0d5500071041c442545550f07800c0c0104000b0140450010201c5027041c40250074403100c42d050300315810054482e064854400004580d644051625030700010340c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 516429406 1250 516428156 516428167
    0x20115120210141b0616020d080603101d060c0f070602030a090812010e011509151e12060b030402060f070c0302030a0308010602011406010503160e09040f0c1208 71
    0x1d00001a400202d8403410011a51441c001c0440740c0d0742c01203032400c40d034828a5903038a028680300300319180e40046c02e20b8801d0350002500000940380c00d815210030050100d1440807401598043c0000d601b00e1f0342d880c40402034201c8800d21001d0603001c102c00a1310f64054440032030710000b541e10442d4a1183c1d061502840c0450030303540d07d00258001001c805805903628031050000d40080300030a1804416a8603902c1c550500e0b000510240c0113900a1301004000130a800002c0c2e0400484c0040301c00b081006288802c48403000e55841400102151b1700c4540750181404861f00540d041515501c1c0c408104085911213420fa00030703100c01d40300690702103014070107603041c034900c08020032004c0e200303040203882d603a41c039400302e0724100000c80d0440100301c0780401031020320390900c12505a241c0c2000c403e040da05280c0000381c918800500002a555040c51204041a00465090054032806084162580350900b0424030300c075001c807011220540e151400144a926028240303030840e800c50340031443c02c1e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 516430656 1250 516429406 516429409
    0x70f081b090114070605010e040b01080d0e0904080d24120b0103020d03140403030201050109050a05100e1b0c071a040f140a090509010c08090f030f03150d050d0201151202 75
    0xc088a200106410303038100310000000c4e45a001b254028020a0b00e40006410300f480c1895604505030850b44642c2c1c020b00c113000400354020408038509030252500b403d20307182c500348040c1c9442076a102c104940c2c10000c0102002200d0450004e03a804c00c0c008480e25a9151401c0b04104a6003080c040d040002d120f0050016141c4007200444c524401e00304201144514401e403656600154010750250759a040100504002801a158040001035003000145408000003603416028042c881c480011280062440c0d031100b401c4030700c7d500c2ca000002c1c1c0c86a111424103503450f001030180404a10f14595028900030100e02584c0580d00c40903648030300359040100b40c444699a0801c041e5002041072400160380c252807082c41c0c0505099400424100c072103c001038007014010700601d1281e2301140c0107420646000c015280724400c070301c840550300c0d00c607010259280360840e280c0c154802c1a15100c2c204100c1c2c000380d10303801541150001e10800600c40f080345070f502024400c0da840c90391380900d0079005 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 516431906 1250 516430656 516430667
    0x1140a0c0e01091806031e0b01090212070f18030f0c0503030a091701110309030310140303040303140903060c07030f020c0d150f05070513050a050d0b07020a0803070f081b0901 77
    0x228600f0b00c1c00042c3d0a60300d4580d0741d1384050103080140d81071091f0121301d09100804500b030f0302400049406620300f000543d840e070464080108204200400d5102d050101d40c4500a28422031048520403c001e42d142d0914506a6121400856106032a00c100080e42e040c0401950546102500d8022020b49000d041003142c244070040b5092556881d820b1801417a0010080d60041001c840150340307034070b0119814080312042e600880c141c2090211410420340d0b0010441c1d0175242d00d813404289555000c040600280103c04107182e00d8081e03542044029100d203005001c00c4d6000f50749070030505c0038540d0182c1e01c401081c0d030800e4200045102d0880440c0f41014105040c103502c0d400002c1004501c100390040b0743c02900c0100014030009219007807032411503460b001802c0c0c01c031403d284103481c04001a10040134942c0c010100c0b8101000103541b107009100c100c05a64020198650300d180a40000308480c05132040d003400300300e4440129540d44c028001203018110244c0e08280f9001c5624015580e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 516433156 1250 516431906 516431939
    0x11b020303040f15020301061e14180d080f09011b020a060c14060a0f0b15181c05012c0705060c010f0e0d0801120f0807020409020301140a0c0e0109 65
    0x1040442031011075200301c0ba62005500828040d03841c00c41c0480c200803008010010b02512740104444034030544100c400070012038150020500c9000f04021101003c1901512510805002d80b4000300e0200801c545850050041074070907656680742080041500d1419090400d010b508000d400d0401c0c0000e6003c0d02072600094050400d06d08556505170509140c03000c00c40740c0690450302d80d00c401154100398024252501812102204072014000070340c442c1e40146030040d01b0324000d14540c0c89281d00c41d0b0003240c217000342c40c4004244070303001402e00b1070180061402c800e03008180d2034114171185541041c803561991f04030307001e480f481d440c12040010366000410450165583e0b9801c07402c030034ac454460344c1c0e010080100500031240e800b0310043e1403900c0580c080d9500744000d004c080005004840b01a45207a4001042601e4000d035001103002000561002501586400031a20b641c901e000c603994031400943c007050000050001040301c0d0340c0b400c00d0955003c50740c4128184001d0600d55080c49 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 516434406 1250 516433156 516433163
    0x30304061802090916080a0b0c07030903120302090a09020316081510021e06070f050d090c0909110a06050d02030603190b04031e09030f02010c061a0102011b020303040f 74
    0x716101c41a40015541c140d00b13036550140340d4400a02d00c00c1d1000b140d08030303400a10111014000200c010344456250801c0140034100b401800110a820140903402c40c001558109003070703113248680010064001c1d849514441d00c134a076100000102c640315402124800c0c20b0762a003800d80d009114100350386080000d485001c44c828442007017041038484110707403001c00a055006081d5419455604100c00c0d00c0d07c405031401d500722804019103a60003105942c5a21514a0311503a01c0c240311140100400704181c00070190b0000300303000500903c0c1030700a1000a801414200401c032600b00803c00044940d1041c1c1d004650107100d81da0514001303074007440e8840406025901090850f00c0e20b40d1103190140002c1311648070131001d00091550100150000800c0b020422385449540800901182002e02c40141044030255410003107911880f020001c407540040305100541006078011004044065110b006601c0d0885440303686140101d07864081c1150f4000d140355030bd40b510b42c0036416003146e4094 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 516435656 1250 516434406 516434441
    0x5060a090c020d1814010c0507030506010608090d020d081503030408030d0212010e0402130f200a03180c030b040317150f01020309030d0e040b040204080f0c01090803030406 76
    0x48110060081c2a1556001e501034a5079004084000d001d91034050f2044041401c1c881003809200450642e500c00000c0034284600511060700e00180745c10080c1c0c00050007030203401c0000510603004625280541d01030002d44406411001080f41d0352490510141c00085525002c074000034040b10183e046524003805482c5480d44603c0b440d1701c0d50303000c1d242424005500058560303a80f42c07800b14181c0076141e115284102c3e4106034000a2507800c0032000c90b1021a520542034010204a0703000c10444030401d08019407452a040c10b101003504480d001101190400c1070070040100c48007104019294450043c503052030031512010032400000f0b01c201d05014840508100b10114182c640b44030340240078407007880f10140340901030b42074418040241558002d1100000765500400e103100303100020715084a0710a003100005000d800c41c1911590814800140071521a4011a40480d0300d02c41034212445a4030707840044034117074128400e800b40c40d0014000b00d80004d00c960490b140d01010b01210 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 516436906 1250 516435656 516435659
    0x20c060306030a1725050a02010e0d0b040f0606061404293405031b07260106051c030f05040306140603012a08041a041a010f0302011205060a 62
    0x80c10500e8410200c400108040031446050341080c11814150314103001217880884191a6500e07179550790325940080c10b000c07021120414684809203034400c01508014134107500c3c1058201444001c1504c142620007a08200010860318001d90154440910401005280c0382c51f000002c03e5021651954120302e40d10880c1850840307020402503c080402c17924a0310500740205041e00462040110b841070704032810800742c000c28000700588001d5603500340c85142800340c2852150400c6c40e90f40140d42c40415240d500c03410080c0000050100b026035000070020305441c3c004200e81c0c0d00181440c038a1800f0102c1314440003d1040358080305c0a103c5040190510740c4a03620202568500400c621341e0b21042800c2060320720b024041c849a150003201084038201c0c189503d071814120070b15002050101001c086030802144203100190403003a011100800d0415107048050f41d012200c80d840c034040c0c0e100022032807031492581d074021030394161114145c7e082c0c4034004a0181c00010400c50388103000e800c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 516438156 1250 516436906 516436913
    0x130501050f0f0c0f0c030c0105121314100e0606060403032601030311251208120f0103030f090501020a03030c0c0212060109150b07141006260607020c060306030a 71
    0xd03090600104000c3c040128100411503e1700c803d0000484c482c1d4030210240c0d80c1a6001400c941c0740106468044040380e03545014204d0742c1c0d44c0d1040041120803006403822030814003003140c001c0d8030f5641c441401951040301a131550784005880c6664800c0d410881040002e001741d4062003900e628444088003100350980141400d0800d0b40141e01041a1308602c0381e00310802c0c0204c62100111224111484040346407100d444a464010303202e04442d003422040078001002e003503c0b004d06001e4030240a0307260841400d05084001c1c4401c601140503c141407541d6801010b07201e0035624181c0c024804289151421009041d010f8041c2e020300c81150100b00c0940c80d41403101c41c80d54019002001554982840c182c100d4001c5c2c41c801044a040301c2d018000c004803001120900f07074110b0b03403d80072441040441818804400c80b5a90b940d0310707000340001c1e041d4040b80c0800010301c2e00500100750207400040d8603150081126100d005800041107401c6610345080a1a00f111014044425218030b90740c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 516439406 1250 516438156 516438187
    0x40f060608031b0d2a080d0e0c060304050c0103051e10060e030307030c060905010b0901090504120302030f041b0f0f090506011133070c020301050606130501050f 71
    0x4114415941000a40519007003094107036004034810030b0001d1400b080c0b450001000c41c2400190401040342c1c102102072405c01c50b5120801403a086108107035180d403540742d031400900b511003080200e4020409030103024601401600e05c01e60b004400303006015000303001140100030040001001c20500b014550300185070000c018460010a880d140c00c4504101c8040c1034591a0980c1500ca58801c2004000103072b84840b02c2003a06071700c20300100c1c10000c03903e021805001805c1c409a0029618000051a144241c00484c0228000d0b01040806c61140004605034442140c800407854031000200d40004c51100c4e41105885038840c00c0c151894823106098680003803680100a2482d42c1001400162603600c0f64580098bc03d003007800c01e28840788070f031588517000032800e10a00a0307410190f1034a080103402040d00c5503141210f488070f5140c960406440c24040507003d038020b6180400240d40c0303051450440d6088130300d100c0403045451074176004452aa100c10720400b81824280901e002e22106c02 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 516440656 1250 516439406 516439409
    0xa03080406031a03011b200a0f0615060503041104110a0504080106290d090813060206151c030c0501060f030219030309050907020c0d060c0914060a0503040f0606 71
    0x681c2d011601c20884246015070383d00d20f4007950b209914101084c0c22182460a451702082c4c0e04c0d04022085800c1e0481c030b400c1406a80c203409655005610742e0104000640322541061442090200807211a5115021880d0800d00a1034003159007040810003143c24010310202602c801800402c09910924000803950803500c985e601003030020400744500c05c3e0070300412001d44141c1559951002d0401d1000d080510700c0c2030302018a0070005203010640000790040700003990410021992440811101d511510592040030018040c680115244032440b000d0007040d00c900419050700c0184c604d44100c15140c500c0821018030480c0c60b003860004800b8003400c1c00a04100042c80e181503d14018440c078000a030528821501c8103039014000240c100501c80261881550f00c6980350750784207420f9240091000b201c6500108819420041028a4010902c18078070b0791f03038012101d43d54900070074002c10101940c40d403108040c800d400441e8440e101039540a070103000c0368500700c8501e44507241180ca15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 516441906 1250 516440656 516440669
    0x1110a0203010c09081e0615010207030803040302150601020309030d050a0e0a09060302040b18130c1e05011803031205040602130e04030305130f0b06120f010e010e06060a03060203060a030804 84
    0x301d04e007081849400e1015401c1406449420803800c2140900e160702c40100818109041058124143c840d034420409040550b40c400718156480c02c9c9403d019681e114038100c80f111844c0c403080055919403001c0300740d651443c00a8002c01a1007aa108140c486410131100e10041100e4074000940700d641c0e190708480202242e040018000e4294014002541d8078200f03a103019100b81310082e150340c2003103080c0c0703035201c10b04d44141d1010007214685041d401d0b07071551214006460142c0301d0001340044c0c01408040f25026280c0e800e12248000d40f12102d81300f0351002601140304050305243d503640030b40145501c244110001850805600040b00004080b90001c01c035825084041108040d01441801c6d0001041c0d02e0b0418841010340e00e01611500b80d00340100038a13001c40208655840b4402401080e01c5000d040c0d640041c070a007005030080103030300004e040b19824440321040c102c0c804110f45020b0640585400d560a0868407004007940c0041c4c0300070781202102c040080403c2d124809440136012 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 516443156 1250 516441906 516441917
    0x20903240a14010e090c27070906050f03131b080705011805010c030c05010203090a11090403200a0804030c06030506101b060f0c051905041401110a0203010c 69
    0x491200c1030110100003450601520b141c04000c415226000455a0458840c1070302c80260390b40f0100c0e0942480c0c0d609016036040100600a03c0d070700d000040020045084000c20013003290390705441110500058441c040102c0d1080103101080d01c1410021a4030a5000d40710ba03aa022075981c07052206403841c01c000c000c07a201040d00344000b0b4014419000107000074609000b120401c1d0f49031010014192192a0601103030908900c00c05000e172101161598021000310745a01e000c07018a5103c0d002c68404484c410407018000d03039145000a046030103640c140c0d0341c02c1d00e060003500c3c402004400c800d01c01d01d940d114039002e690005404100a0001d10f100d100c050310f07010300e004006001d80300080d180f46e00c10320501400360001c0d03600412024034803203200c08280114030641059001011151600145c0d5400d00810101c003e8128005001c03c201c80701e0214040c0510004c220b8050080d409020312080e2006011940c942c4034411000c040e09400040d201d41c10310f964002821500c184050502089 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 516444406 1250 516443156 516443203
    0xf0601080f07080102190518150307030f0213050904080c010606120f0e0a02090615180312040e190e010f05191e020705010605030f01020304020f01091401080406020903 74
    0x2006100030002030201c2c0d0000d50404840c4007170700901c035045114900400c20301040b11182324032400001c015011000c0d011b000c00403007445900d00f5075403041341d4a001290070308142000903010351007100c22884200c1c0c0c1400ca4241047c0801c40341d5038024006071102c28062018800d003e400380301d041c0c02021991168807480e40191041d00c16140d480c09c040c10101e00e0425030f01000b68010405200e0250704a480508035550000060318590542542c0645d982006ca21020071241c1480302c00b41c0054101e0480b401d100202604000350303c606e00840d020107252001081c5540038455803694040340250004c20140303800b1040a08441c001070080b84003503260000d128495810142d0b03150281032090081c000044601c0d16000641b10710304510b0303075030313070740041c0c60f00500c142035200d100038110040c01e8a01d14062041c0d154013030b4100350f4059100f815800c007001c00c15805410b444040342c0076206500c405450040c01991002001041681c034942c00700500a00c95070180440e00c44401c44031102503000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 516445656 1250 516444406 516444433
    0xd0504090510061205060a170a0c05060309190515070201150b190c08070803040b0403090e130807020a150f110c01020a0f0503130b0403020f032d0f060108 68
    0x40381d01402c03104014220b80020711003203602c203240c1d403a10b007400300000c0b40b141c9a12012946006090b840080d023801c01c00c2c607a400101300413849400070750040407008100e03030311882004420301c81030714400001d5110001d102c441150800c0849840c502860660352a1100c0b14102c100440c41241d01c40b0043c0d55500c2d040340038101130b8030b01c0307009000040b00032410000b407074907031184d0b1a0724140c40000b4071940040c804200022481243c2441da4001180c584a090520b0544007001040d14200c000c1000031002048003055485001e110341039a100d80c1300943d00644075540300e6488030400b0790308190320050118041c0034002c11024864050359841c62160701300d0b54010040c01801410503160303004508000d01d680c0e400950400010340100d950b0200040300e15103140f0f58403400e465407032420a038200006241c1c40301009402107900a0b20008048400c920130151101c2d49036650b500140400b6110390100e82d0a02d02c001c0c14040e502048a1000282030364007450000c00342d0006416a201201e48040d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 516446906 1250 516445656 516445661
    0x512120118050601020705210f0309031209151b0601080c01020c030705030a0b190501060203042d18090204020408030315031f0522050a14070501050711030307050d050409 75
    0x881c0d05201c4204158281072000035120b5446125042c810030008491842842d00994024407580600c0121444100c03a0844591641c0009144506c6402000c46101d10800581e0484141003801400c0c1581da004004d01d282403038224151011341d0161504c0b00d00440c0d142041800c0c0a04808002030800001c900002072401e055412610b00a800102c0100010303140010161041c683c030200091950751040c1d401d04207070350782c44d00c4100e840c0d00300f00c00082c0d10bd130003000804c2583d40822000d1112a92a02c1801e410041c0285006003945d0450f4100300b00c081001000031041a0160080b03401070240c1c0019091b03030455080041d440d0400800e100d4005911002404605419406021030a0003070000a1111240440c0c0f0b400e2551194006600809610708560b40c44c4014a01c0c0c40c00500c803030500c99a240380458040351001450000c1c0c1050640000d50241203c1c1d05030369491410140382d690000e0000d0446c41c03039416110522620000035818003044148450a07640c00e9250707031501984109 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 516448156 1250 516446906 516446939
    0xa120c09140d0203060a090204020c030a08040302160308031807090e0705090112200d02090405060405010c140901030f0209210c0402040605030403030203060a031506030312050105010e090405121201 87
    0x2c10105000301000584022801d03661001c400d902c0018600032500120f0007a11070441d011a0501000802c0801142c11140060240b0b00035030844009503681c1c50884c40000d028080540100d00070701c0000e0141280c0207240c03040c4e00407170056550312031750707110b804044c0d030401c0c1c20107c003d400c0090705022600340074150500404801c80d0202c1e00200d6a240c002c8401d00305420701e0240803030300a0004298682d00703600301000354003078151286454541041b0b41c5421003075900700c2c3c00b07500788040150f0030361003400400906240c2c04680c602d000c8440006400900001c0c50003084940c0a00c040100c0d0303034819101e081c01182a0541100c0101008503a50074107000002e02c5200e90b00c1444280a8240d200b000d803644035a00d4240140d5035192080000c407000b0203030348003d0044241003803405500541d5006003089a109484440100c40302904080c103940c1c0901072140014040e080140484c41c1080160ba0043d015800761081284107000b2235800d5408030103036908009a2200402603a074115076400c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 516449406 1250 516448156 516448159
    0xc1b030c011e0306051003051509060307060c030917030310081911030307050a050f01230a0903050f160311011e0c050412120e03060106140a120c0914 66
    0x4904149400030740300341062000542902c10902c040c0406500a5100da009000006c1540105a0040c0c04c0107029040c1241c00c2c0710142d00b081d6402201e400d001c1400c2c0c0c00340d080100541515810400125010390101074103804005003070300c0004001c0302e034070f100380720340098500030710750728500380c500b0004e01c09043e17025010b20390082440342ca49911803040e0320b04481c0e1012aa5900c42d5541d8002851400303410000b410b58020042c03101e080240024403843c40c2c4c0441c1c8000c0c0315543c0e6560400c60700e001160b591011350502d0000082a42096a000c3c2d00310070f110f4140b41c0d00b410240c0b004240b003504801c4403204908034015101d824160040c80021055451000030710009140000001007169880b41d00403a007910fa80696000500a105440c003500c40d0701c2a174220441d00e030411860304260300b0405400704d1030580180340035003400300e1070906890304c0303403907811b0440c05813100007941d6031248104800f005030b8103041142d20070160080300301951055850302c503103504007007403843c05011401e01c49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 516450656 1250 516449406 516449413
    0x705120f090d1713080c16030b0123060d140408090102103c090605060406080607050708210a3305090a15081c08060d02100c02060c1b03 60
    0x7101c00305200d4905540105038141c0b0361354002051030000114043c5e43c010780210b014502d070700c0c009100516441c00c00c8034000c540281d01d9990b039400c0c1c01c001008055400341e006c0c0c070202122903035090060090601885c0f40e440024030340d410f0170a10350380c028103483c100c482c0c22000801396940c0d86e04000c00c20b00a8041e107410804820200007445082c0682202640414005146501e03030642074841805101020607040c40030700030b05d01c2e08100a2000b11600b51042e450401c011030840000900c0314400d074955201c0911389070407902e4550454010300070307aa041c0c4011a2401d42c003045c560480d94000c0010082c042200f80194124030302c18040000c0c2c40307044c005144481f407070403600084030f9421180c042e91414031039115100801c0107051451140505003914400000324400c1c0000d80c3d9402e0080d403020704070a0141c0741e00442d040700003940c0155100c40000702c198094601481050161915804c01c141000125404039506420003690f00806030000407144070107402401d442316807030600f280503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 516451906 1250 516450656 516450677
    0xc0c0607051911101802010201060b1305010c08130303080402010305161e02030c0106170d030903080a0b030312070201020408010b0910090e1002040f03060f020903070e0705120f090d 80
    0x15080d074020011002c00f0040410300d5409850410301000c8441c007000c02c400d1003910000382001c8038294016074124019880c2000019810ba40b5030161007070041034683c541211440c100c01120b020746e0100080c1c0300342108008852182c0c45c901c41517001940302e522008414a40b900024003187d034020807180c09040b001c4840364580d030340403280130b107090321004403e06042e840b00801c900c2c5010b0450008210742ca00103001c1800d00e10014541100001001101c03a0007200c1d820032410750301460030043c0401c41120103d026404660807000d210350010741203030700b8000c030f041d0042140c0100b0358001d8090b0354005410b2041c48028000e280c00f6400039554100181050340c10b0403a503103190320515041581e01d40c41403100c0d20081c06400c88021419409549941c0c0364015102c0319640e038402103500c03d1424401c01001d003958001d1301c141c00d60090140101c0c40c503091500000400003420030007044000c03c50a03056016400c2c0180c0250081141300c140b900d803400c50586003a024900d00800d01074910342 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 516453156 1250 516451906 516451927
    0x212190e0616020f011103010e0702030406140d0e0124080c0310050a060302060706050906151c0512130503010f0513140309060a030c0305011a070204230c0c060705 72
    0x1000c94004052003041250500b4121049003040804111420103500784481c1401500c0200301440c1650840308400c005626000c4090b0380e24400d5202d08004203403c240c075402901c8001c0c003d011280c4c40440003041c01000c081050342102c0001c25a5288142040745001501c8140c040c2c1002505c8a08010301c0359048800c0020341e15040580e500f00d0035034543c400104003521a030484002980d0145c0b4072500c175030310b034906240903050403501c85100d031107040000303480014003040c0016205809440c00311444100c000d4203108844003034040d9568401c07004c10348103007400080108020a2111003ca0240e03007054205401c1d03a2007000044240d500304402d018100c00312404a040051380194000d407006c45000c9200e0641c0200042c1503480f00c40403440354040b50709a0030200c10b00440f40c0d030421aaa80b1800ea400740700d1400c81d0820b0000b1030130b0100d07000504060303004004569041811107000300b1101540c100111044400780102600850800000001040100d4000d58181001d0342000316215 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 516454406 1250 516453156 516453163
    0x315120a1106040306061d060406030f0b100e01060c05011103010f0e07020109021806010f0207080d1b02060f0a09060903150911030f1c03050c0f0304050f010212190e 73
    0x32800340c94110701c001915541d98545040300d0055500071000e0150700ea4034035880242d40c14035074080030a20718840001d039030380c64140b00b02d8059992200d402104034030b884c1c580c0503501c1401400e00340005920400894a6017405416900900b0701e1b6a40690030b059a02d80a030941e40547d400c0802c101041c001400f051509040c80c1b03040e10381551050000e562480001c07030160a000300082d400c001c441402c0c884030f04c110700c0c0e094840e403000c1e00e808020400c0c2c418101e079901824810588107810441e0241181da101340c00101500740e02c80c08514000b42035400161140d40039020101d00d0b000005580c01c0681d4220030070030002c0c211801c3c4280e2031440d44e1130701c1d202035132170210f100e21055a4406903801c0040003510003a0544000d01119071f4607c134500302a645070000c01340c0406441c803071080b400403903120707001e40c62041d14201c081d1410b001c1d0002c040e00d0903810180003100d2600418072205c038000001d101410001058247c1c0300c0c0141019461400700004003520342d104d0740e0a20318084403512002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 516455656 1250 516454406 516454423
    0xc030c050102070614040915031a161b0803060a0506040801150816060e15180f060a17060f0303070605060901050117070f0509190312020102070f080d020f0f031512 72
    0x6240425640ca48d03040603d0449050380005185901c44610365882e551042201442080c004e11a20090a4003400c02d85030314610f1038061040b80070351b41c01a0006500030f13001d160030500241c403803041030f074940380003032550f07003140e000380404da03554420071718030781d030384a201100100305890180c0220b103201d08510954802c0ea0040e40d05010220801c10701d20344400100c0d030719104d03d03002d80039103443c02541408200503074988454419643c81086444a00d003101c2214500480d985404241200307c03e040201e40381c0081103241c0c0041284000348044d103040c002407480fa03200303800005262400c076080200d03030300781a0402c60410858000c440c003826001e1040320b8020400d400d0112241c4074541048400d0305c1100201a01703c0c040007180000a9510740b80c2000360380c4210004858544400300483c02c0740900c0320082c02071407503510102e0102c0c5c030440040c81c6202c001c03840986002111710b0021510380c0103143c00842405c0000030065003c92155804080c2c2900712040d94101e031290106940d1050380 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 516456906 1250 516455656 516455669
    0x3309030c1e020117090c10180807051809010204030204050c04031e0b01030602090a0b0408010f051f050d11090403091401080408030610050717090111060108100f090c030c05010207061404 82
    0x84c08114031a100700000004640300038500038407007140c210024000c0c00200d5001e4480c6010718008100c6820100d01d01054074000392411107107040d0310748010745207100649104000d55081101002584035409010721600204040079078840c036600d055903001528141e500c3c07a440310302e84201d00189500181c0e90440750420405a20ba1048500040d000b03026640b1550310031000050025205da010b400118a001c81c1810811207640ca4002004070006c40c8120724600c1e5842c480705001c98941849880001c44c00341c481c4601030000d080200e00800d00035203003600441c00b000b40420080c4d41c0c1494005914a0030319010042c0d080c11743e80d02e0707030500000d003400348950000c100011480348600c09076040d0741d410161420a00003600151200c5034008030b42580003449094072020070603000110f0314100d4240100070a4030180c040388110080a4000c2c402005544030300c1c0e40c0020a011561110246020300b5002c00392911304000a4136161582d444070050110964130758018100302d80541d8116480c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 516458156 1250 516456906 516456947
    0x10308030402130b0907030e0c0a03080901050c03040e01030614160f0311070510020c01060b040e0106120e06040501050a0c110a0807030309050d0804031b3309030c1e0201 75
    0x110703d07002406401d0310400786030407003804010030210302d506800281e003150620055034044030a40c02030150014681c04040c208000c00c01043ea4070354402c1004104110881080c1c0e42483d864681820950800f0703441035070703400d460707040d807004440c07c1803c15a08913040d00b4900b41c6000b140303140982180b000603013a20a141d81c2d0803202070441880022a02c82541c0301b42a5005445900168802500103072480b0700d080d841c148000c90000d443c001103034141c99100b907160090361720300042264502004c00c3e401c2c0045440d01401b100000c4100000c600591280001180c4d034a02090b11030100c40303107140842c0c100000c04c001b00c010548040364035220550400c9507241c2c1c4840d141010750141c04840300007402440f83d04101d550b01c50380410058000c1d886035407032500f0100c10100a1660003030f15a005440aa81d4108242e4240d882805d0098800d285840440098072006801c0c000c680f041401940814194581d2504008200a03005000078910503249145001a00000d168642c1042020f40414 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 516459406 1250 516458156 516458179
    0xb040203031c14130b010b030a021e120a020421170a0206071106011a0c0f030a0c03090b13030210030e0d0903150c080a0908041d041a010308030402 65
    0x440600840b40680740900314600c0d000541a01c0400924504095601c00041c88011481407151854a99030454101240302410307420301c40074122a51010b07000c90040d690130460b01048501d43d03032120b40e01041164506031a07007100002c4409a003401084a0403a40c8100300900000684101000030b07103240a44101d5502c00b80c0c6813454000c0040c5040c9044800041540c4d06026800914240329a4003640d800462071002e10b0705c20fa80c2e101c00c0c006c1c1c6120082410100d1a040d81c26005050300f98581021114030b441d00090b141d040d40d01c1403480e00c1c0022400c41e40501815005088000107050340e5500318070302007c5c601c01c4000078a4500009208407091003449514500c80c0d0000010560407006543c40303644280805003000e5030503c41203800ca50303c2d0400c0c4940d0303c00c41c4201d0160400d06d8a9892442c2d0b103e8001d0703001071941ea1381c12142c400060001280e10003881c508241400044040c2e030101c0d0525041400b84000118514202ca924000c018800514004143c0c0d4000d035050b9504c56504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 516460656 1250 516459406 516459409
    0x601081b0904140a1b02060403080a0504030c0215031518040f14010e070e3d030b0c07051e21070f200f06220807080f10180b0402 57
    0x40040f03225406950601106100c19080c040d840180064042e42c0c0f0b46102410240040c0d03203030003080780d02030f001c9280080000d071030601070382004c0e922900c00d00d00a1740307590382a4002600c0d111002146162400003004004443c160001c40d41c66410048660040450b040c01203d00c0000004000400d0352501203000000c200c42c00d10f0440714900190000c0c0089002c45c1021941d0b15040d00c5450208000a40400c01d010301211180e549441e42c50300c01401500a0107040e0b4040c03207050100b45608240101c000003040302c0440081c080c24010580590b10103460070080d1400c0102c840c3d24540608007400e04544410000d0f00a0692072900c441c130300b04084100c082c4c0c4886c094068050212902d0125220410180042d10002581d100d00c0c41041d0100050500a1183c0d899450766000f000820801c00d600c1c4110001403017a085104a003149180c8a40e10b071401c0031007583c01840d4550100100c5041c2000c203002003003c0c9080d038070f02041400b4101c601c0d0b80c404a40520042c3c03000b03400343d000c078056 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 516461906 1250 516460656 516460661
    0x2a12040f031e21080606160b04050c0402070317090d09091104090603050a021e130b0409020d0f06050c0906030103021c0506010b040e100501020c0907031803030507080601081b0904 79
    0x41e0390001c2c441803040078a100710044041070403140900190542001440601d8410180d1f0f0821150f180c01c0c80030038025a40d0b41c0c2c4440300240c010303911417003000c52004199032036000403d01c19101f0384d00c03044c5403030380c1c082d58125401e406030000b002d1350001806490384070360140440c42129005840410301d01b50311301c09421103114540007161024240040481407180010710f1511040c401e8a000103500c2c41d1030604036541030b55181050740043e80340e41014a010f40b54100d8561f030200200006021841940005c04944120401712900b03034481c10500140606031240a91240e4a01003480c40c08807100006030b00d43c401400001e200702010340030003500449490240d0480340e40041140e495503141d003821119500030b4440c40e000c038490745001031022100c6c481500c080b40c206800904080824001304020a030004080d8020503907100d800060b103180c01c958161029009440000d01d60501a00042c400100102014140008101801620042c5041100c40c507000c021019454400d9400082e01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 516463156 1250 516461906 516461963
    0x8060628030b0711061e1b1303032102030f0f1f0f0503010609110901210f02071110170702030d0614010306050901292a12040f03 57
    0x2c0d22403281c20050381c00d07000030442c6150f00900c0c003101d0b42e50ba680d050055a07030305011030b20b01d00b4882c40c1c070102e14855a44181480960003200b240c60500b41044440300910665030b1040e000580240303c010a00400454040c21001c80a00254914940707603e258044140142410201c8084a00080e045125045c16004a5000e010243c40c01560390703403040e040d00c0014090790b8444d501c2d040c400540c1489500c0b5400400d012010071b0b6081001110055560031080000b00c050b11201e1842d800c0d9004451180c0390422600da0740c0180ca64a00d0b007405000c54882c88140390140400342482100282c000c4001a050844480405c500d6a2800c100308c0c118002d21440c0d0050505100012a60120030001000e02076001c0e42c0405c801561142000071682b07084c86116a0131030701d0301500307010003962411104101151070040746400e118159920400d00c41504071315080b02c01c8002060041030911080050405005103181024140086132020101c2840014465003c0815003621113940303039001e08 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 516464406 1250 516463156 516463163
    0xb0f010b0301081902130227040903090b0901050f07150b0906010203030f0c0d0914120301050907050708040f1404050117030d0b0f030d020607020c04020703210f0e0102070203070806062803 83
    0x54548c4030303107601d0020607244030b5544060003840c00350520542c1041c1c89442e4400341c05640f1000d0182c41c28044080e02d910204407141042002c02c80c43c542c65403610b000304000727449040c15101112405c0614000c441203800190301c03418001e4180959070782c1c004103490f0842d5000d0290079040e1140d81c00d00c2480d104038450001c0444c01c2c91000d03400d0094183c0000500b4003d0020380303000f140385041c40c1c11035110901545a00262a40c0400d54481c0f043c4040d2252070b208075455032420340c580b00d1003540f5060b960b104203103164050702d0240190601e80101401070014400c1d004030300c00c10f803d90030b850340986825050341c152b50710040882e41e9144111340b408040003078103031002c0d40d030038171002501c3c0d800865901d80540309416042e0b00e542818400c40740b101d901552142e80c0700d5201207000d04020300401400741e031144c0741c445010071400d4610541d1030440c0e0a90006a4421301031061500700221640002a142c01850400101d51201c0784c110f1100746908003d811000b84040980c0030b0901c0c00d40028 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 516465656 1250 516464406 516464411
    0x603020a0f030302060c0406080f071107270506010e010302071a0a0507020d0f02030301031401020d0e0f101104090b0a0b0d060518101503060506070b0f010b030108190213 75
    0x750088822400c40a503400780e070a45005907201001c8000c1c912852084400284403080040c500c00a1800060b801c0700c00e07860309030b00034420703007281c1850b1480c1500030007040500058100d02e00c0c89101201d285400358002c0c02e000300c2c40c00c100043c2c803028001c00702c9418150002030f0383c000c0002203542c0b0401c008000380802c980c1e00740001c00500500e003c440b841c01600c560060b444045010b00d00e032200c19070242d8011441c5a0035556516104454401e50380300941d001e100300013070320480c0d002c2c52042c01d68440081c1100d507980455a07281c01c2800a007081c50718a00103401500d20100c1d4111070584803150008140080c10702c010a9100402d40d03c0041c10b0000030034400341481d02608010200c2d03204940540c40500c001c0081504914140c4150000e0700b2840700802c032007403400c03a1490b4110030604000600a41c1c50700400d007154841c00342141d07500303158401c0000007102801d1f031902504050000d00d08541c104084c1659800302582c11030f8101500d6a00401195180600d2404242a10405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 516466906 1250 516465656 516465659
    0x1081503060f070905030313091d0f3d0c0203090901061106070e0f010e0a05060406080406110a1409031906020304142406062206030510030c15030603020a 68
    0xb11100c00c003080c1d800310300040c0d5a000005541c5800810741d00452203c01e1203200d80381c0b614141000600c08441140c803200c514200c440092202800b0745c402e0840346070054a03003005200074640342c4e041c0380c244898001c2d2a1441c4d000b05a90203000c03100c104200c0500000f039038515200300f41d2441c000d144200e50301090308400494032640c02010f80f041c0d101070b203040b121306880d402016204414000502d9402c800d1084040c061584603820b900d08103080a88100a080d4644d00031408540c4903801403000b06144800348020880e5910903500b40e9400182440d0800302c004400074a113695036100380e1503468010511600580e81032206d0864410310180d101d00b0283c2a01c3c103c0044c1d0011a410b80e088158030f8161041e100b00424405404409aa40003186c0800741e14a15050b00e00544075940001052220f45050304107080500104010111030303c23102483c0c00c00080031303208000d08010082450080400c0051880c040203c25610407200d0298400c0b0000c1c0200e004100a134406980005004070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 516468156 1250 516466906 516466921
    0x180106110106060f05070b13170901021605030c19050a090e0c041e0c03140f0603062805090f0a08041e05090402060f0705030c010c0f17060108150306 66
    0x490300022000c8002d20086a580405440701c41001010101041040107004009251003940c0d90784086146a00009100f03941c440e21040010380203800e01d414000a8660352541c2c040054405009102400c802d00a0804c0003194848201c180400d02915082d5892820310906d4240c21020300009000c20301403c0c0c1d500c80c950f003d0406050203040c07500490480f052141810b000e004603010314103090f0b45031280307070003180300040800140000c105a550f4400300c0c01c01d594142414000c0440403022500e504010741014101031000d0621409045002c880002010100c0454182c0c1810240c0008580e503a6801e040d01344842041c980303486018039056141044107203006001902c08021450303892203900740d8801c02041484c0291a80900761000180052070b040004046aa000f400034509201c0030b03540e42807540d00020700607007143e5100c8001a4001e0307131250584424904070720304014000350358801c11444c2d10002e40318a0401c03850900141d031468000c16801110030f00941202c4061810b02c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 516469406 1250 516468156 516468167
    0x7080a110d050d080612030a0f05091c0614060a030b0f04021f020a0b0c09030a0204180c03110108160c06111c020c06090d17070e0a0603020d1103090c010e180106 71
    0x10b6400b03100304000209040405000008d60f000c04105460340088055114002d81c0d05400001c0d51590040d113803401c03124002c01385170410412034420351010030200212203a60110400c020500c2c0c2c080e40710010204003007040c40e1814ae82152000741002e81a840c0d5001050030701441d42d0490000d001040c10843d40e4950014640001c5d9010700070091051301c84503000100751081440065050340007100003005850164012000b0403030001001007180b80c13a5840f4440b010203030344181c03469070501825001958000051980c44188400004003c0d4042d04001c1d0041101510141016030744414410400c03050a045035428020441c42c05030f60100c00d80001c001c0c0d488448205030f0340c00756002162107040c1c00108044a2800b540b00e11520034200c0310900410a0300030418400c1003180150a015030300d4200da00350140809590159480080c50782040a480b441c99149050346400c01c204680c1013030102d00b640c1041b400b403800600c41c000501c0000c166180b040d124409011114000091050304007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 516470656 1250 516469406 516469411
    0x30804060c050f01110403061d120408060105041e0b37080d0f11010b0a06080105030d18091a040f0b120601080337030203010f0807080a110d050d08 65
    0x40e4125601c204001d100f10307007a2181c004020382d0070902440107200040058010340403c15505003200d450483c4101d0803483e01030032180344a20464001820311102c4018400180903001c00d803418000407485194502d03403004140b21420407559110050519599401c5503d06d406080c07041348480860007203c00700e1600e5005506011081101000042c0b0302c6007c0307030b05040664107843d03081d900c69182005680400c02c0c02007001c40e9542c1e03142549060355400302c106014180d2a582d5203401c2d0b040005051903e050540c01c9402d0003e001e800ba80b142800b045c40f03a041d40c8000c1000300702060b46180ea0b0300310a066129959005050a00c018409047d03548502c07038603101142c107e038803132440b03144180d22258203000d07030142d07078008101e10300e00d49850700c4141201085c9100080059040050000c4410100240c1680029000001000114000301048010b0485080a80085864550241e5a40d44850710003000c01d03649400804083d9201c6420300303130994100040c3c03005140d21003401000c0d65401c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 516471906 1250 516470656 516470663
    0xf0b010303090503011401080303070f21020301061209021f170a020901080705030f1b090301020a022505010203091e06040f03030314040201020a1515260a080403080d06030804060c 79
    0x1d00c002c41b140005540d98140c100c465013405946580c0307aa54003101c0703100c00080200107108608030a1b008a914001c149440e031103060000585a50620800400120840364103865890030509010050f1740e030749880150401143c1c503508200b100f40741c01030b688041080c4250359803980d04001c03c4000b2038503400804103450241c1c0e40c0442941d0703105040d01c090006490b14594001e8010010300007001144e900c041900f0107040050900e40c40000080c26644070621010050b0400c140420a5510340500803400c614840d2b00380c0f415606010000f941d038003504807154450310f4486245145141000d0010840c0c25001c1e09055440761594034400340c10885101c220300080c94070050042401281c41c17814010b55050f4041d040f00450740e00c808400c5c0c001a80e58034026603840c3c029408402c00807881c030780105036901d20b03072241004a90100e0025662100f15018a40046003034400160040088038244c1e51302207019921b0308c10311203004c40101110b820050080e0710026003ca0015080118111660712 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 516473156 1250 516471906 516471911
    0x4060605030a05100c080f0a0203090a060c180510140d060306090b010f0603140601050901022815060f120503070c030803010e0a09080405040b04020d0501060503060909060f0a090f0b01030309050301 87
    0x34001170071038a80804440a89400d5107040c00702e0104400381d002035800c48041000ca07800c1c00c2d8a0740310401269141950103021400400081c00e940e1036110307681005042c22203030307c02c5152072004054007003181c4130140682042c0c0002c10b00070b9100340c1d9114601564111904002c03035040780c42e024040704801e00a044090b041c01d000041c50901c21300030801d454030803e205510319100c0030f00550786900000c5103141903001e805403920413040040c06e503c8030908c180c0d00094107061281011413004039801400c024036030601409111140a20f0380b41c00440d61a01120b8100d030045051850079405108070080c0150303c42c20002060003007640145041e102c221080d180c2c140ca030b030110030048a1280400a2040005200c2080b0902d4554004c85c0f55007070141c8050f02e0a1000403c100403107800f60042c50128901000b03200f4141410f007021540000200000c1115040c04648403a1a2000600303140b40507480c4c420340380030040c3e440700c6c6000040e07120312440c800c0c2d40c5030301c1c001c6e1844c0403c1c02010300079803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 516474406 1250 516473156 516473171
    0x20d20040e0a1109060c2e0b04021314061207051207050c0a0303050601050405030708010c030c050c120702060714060405010e0d05180f06030109020d0c0f050d0504060605030a0510 79
    0x4407584101030fa064900c158003458050b41c201840030540150a04103220302504003541002400380301c640c0c130301c01400c11800310008017107031060080701d00900c64030b4000c600c1405200c280400c0066110300b990704840c1c1d268140c29409000540070311511010300091060281071001007030704607000d4101c0d0705a40d10418112b54810f08111058090403d070114107a0015500a0100b07009a200c1c5070441c2c0180740061402c0c1e202d40c040f03440c02e1010345c403c00140c0e5668800c2c19500384d141c450230111010a2428034a4a41501c002030341da03d02ca85002d43d40354030000380c042c04550714a8225907015a10400d402c2070004a0b0b010701c2e49480d400c4806403069400e103050f44526032804a48400c81c1c0800307460300d038240303440700003004c0388140c03000d5803160417503020f20a00780a5954000558001c0c05410409a500e02c824440b01c0c0548507022100d0003030001c50f44460b40041d80243c1928030702c900c1404000b9441e541c0341030a00180070181e20075501740c000c100c0300f2001d101005c103480d050752280041c00d02201 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 516475656 1250 516474406 516474421
    0x2211060f07112e030e030c010c0c060c08060a0303030e01090f1a011502070605070507092c070308160f0c12020a1415180604140f040603080d020d20040e 67
    0x38180585102451041d49031100b52003400ba1780010342c003c18880c01c80b410a07a20829881c2144c00341c11143c2c02051202d03040c1000c00c59603000e0403244901d1460265140c1c2040008941c100b8450b000c0141810380311110215031503001d500c040709003178004c3c0c0394903007640184c203014a42012074102c2030380480c160b00000c034411416002540035038141e640101009450940f044a030341e08900c030101c409001c1c68100003031403005801240880da0018500c03807517884118000300c0f0012150000c0f400503404c5440100040b0b00c0305026588440f180c825050100800d03494048454200003100900003076800002007400512010044541c900c00d849612010717850b82540c1ca000044c0d03038601c03603001701241491421401600050100c1c0602400130640d0140f4a0001032220f8101d5048094000304411800e4118981308584c82e0411006860030081300741140c40e060500c0c440c40301c001e52440e40029070300481c0200c95008924003000c0303940559200c4020042e80d0790a900c1441521084c00c288000304680 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 516476906 1250 516475656 516475699
    0x2010c0f3c020112150f0807080706090303020606010c02010c0b070f170130141006091503080f0d0e01020309010c02060f0f0a0209060706060603052211060f0711 71
    0x8150140c552032114000b07a82a84003401d0320352424140c0c8008104c0020700d01034001c451202401d647e03800380103034a090502c180c1ca0400558003c4c4100580c0040c2000441c0e0080344c0e40b40c000b40d0a00c2c14592090b22400140c90740d42034008000e00410019081111495000040e03200780a00c980e90031815141d062901007035904203006456503d480f100443c101a81310001a010020041184032100e0300c043c1c5841e480510603608551568001c480000c1605036680b26900107801c40100400c108290350450312011072540c00002c01141d40000c595145490700b500383c44481110000a00211084000c11030203504290342040310f560074a01401441400411041d11401c91803806010070341c2c1d440340d481614a000303015101900e03400c20034000c6540343e0100505405008102c0820418038080c030060450f84001c01105014020745803911941d0f0b6401c42100e0040c2c3c100e0250042050751030300044852140f1030601d4108040091048200443c40d40d0401d14408200c0392030030101d00b5a00e5034801e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 516478156 1250 516476906 516477023
    0x307052a0609071d13030315030b01031a0103081c0f0e01091a010e070806010e28060206060303040303180b042421050a062c0a020901090302010c0f 65
    0x49244d2000c001900d00703c92200314a14040c000d02d030208801441c2180390110011541050340d69030040c00041c01800070300342403845044020f050740010f41d850741e01c0b0380c001801a500b00101072181c460012101344025081420450a4903e017040501c40850710a802400030b01c2044038100820001515070b10347c019001d5048410700c4d20307024107641c1c5501084481c00c1c030007000941480410a5207100300d0f11043d24095000904071703c00800d0043c2882c0403003000d10326500a00455104800300f0802e518040142c2d412280e250804084000d8840b030604072050198100400f8554003040010703c60105048103610102403c0c110500f540120b00300f01d50304003044a0400c08000c0303041680c00807050a901c0243d10400481002410584840c00c42080401122070540b100d035440e20700381c0d00c1101020003241c2109000b40308510345088a400600000034a200103414440d103031201c801403040201d038482d0355590041d0202d02d206151010028400c090501c080b801c298061442c01d80d14a00400050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 516479406 1250 516478156 516478199
    0x121140c09060409030801180e0706031d06010302210106090203090c1509010c020d02040b120d030f09020a0e101203020313090b130b04090219061707050307052a060907 74
    0x842d5030709019103c28035003091100d52310490780c1c54a03030103002d60040c002c050282c01a0307900401e6280c041c110f000000c00541e889201c95030400d800400050752034000040101100c0c405218030100e65043c0240180384542c40707100d001d400001000b800e03034004200022000d10865008a120725040c0d10443e45000c1c01000c28049038528004001501e0701d600300c00340e610710090021600780700507404244590001b9456400c1d9512030a0301940d12909400394201d4100c03a00b0701000241c41d550002403040d8054414403000c04a0341002c08c81d10a00094044060091550302c0c2040c46140e02d0000e582e58456224070700130075100207011442009501030304856280c003c0203c0c40c203203403900504004104403489940c1c480d680d031101c0c07001a12069481924080c0c0301840c4003806e454504003800035840c642602407000110400c1088244c1c104090700e401c103101e031505036200c0860680849040c404140351400c03035911041d00d40030b5690005582d52280b6100419580003643d1003800544040e560007614 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 516480656 1250 516479406 516479417
    0x3040e1012120309020604050414010e0c0a020307060908090a060804061413170c0a03030203040605060f1315261006210206090d0f14150121140c0906040903 69
    0x250350310f100f074100e0049a8001000030740f0b819600c0001a04541c80310070001c584c1c6410310f00420004180045039980500b88151561520f141100002d48074130404a0050a46030307034000c614280700c907410075074951040181114141c07940311040500049400c035801c0391071505010f1400c01291706210114027981c03140c00000075041459840c0d400c01e03500b840300022040400d00040703c40240070403c00c00301d0380c001e4400680c0c0b07040500300701003503a0006001c280200042c140c14a0b594603000e0021032a049100d9001410500707450748524503151a50096144210f24a14091026444ca84070402c46140741c04607a4029810400d1006480452051110241c40350101c1c00185081c3c051249c1c12500c001d002a2400120900003500c0120ba4070342030384e1102c41150494204101c9170582c4460603090300086c90020b01500720b030b4a422405002c1c0081c90300d4604115907000601051401c3c5141d440309a082c4070b2001c03031030300303c0d40c90b042c07001c0702da1048040c800469413030b0420740309080010b074055450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 516481906 1250 516480656 516480683
    0x20312042123192115061101090809090408120c03070e12072603031008150f160e090c03060307050a050a090e03040305010204180c030e280503040e1012 67
    0xd079020201e500d4503e941c03006059400340741000920946144203003c880103205c682c10082c0040c601c0940048688a903031400103c0000314034803005441400301d046548003c83e03a19454014454040e10318034264255848081c044145004400f0350b00c03404440d40c5494007000c02104200c4014030550342955907812104090248e00204000c5a00754004144d400b03404004201155107194411030303900301c000016070380601c800311003400321200700031b15245c001d0001e0508032a000d0042501804108407445540214890a402206200c01d80080213006d02e4035443c069120802581c412a0090b1085c0903d00001c5130a1804401d40070030381c3c40c0030b08468800340c141000100101007840c541c4a0343d02c0140000000200240002c0001e13210b174400040e94034042c420000152440700c8d480605041c03c050110400b00d400240b1192040c0c01010303400d00c41242c0c5205a032101200a401130094040000c0125481c10200f100a001e256400c0754a52469507030302504600b04c188185c020011400c80c0c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 516483156 1250 516481906 516481957
    0x40c0504050603011808070203010c1814040e030a080609180312091f020d0c0503010503030d0903050f0d1e141f0e04031e020d020312042123 62
    0x101e190300c1103014000183c040c1d10194034801041d038108088482020009084046003001e008440011206040c0f03190221184180d0951211a44c051019281601e0507126029503813a00300d54200000242520b41d100c00d40c10b0012b1030300d081140e01d10301401c0d491000c0380700c18018150783c929039030f03900c0061800c1010010700d00e0030009028140039a14802d290001801441400b542344805075121001130b942d00714921020187caa801020405001041c8010011510040100c0304000340f00800064145007628040d40c0f40d009690b00c00300a803402194022010074103030f01c61401d9103035590450381c0907440700040314280c0705548010b0a060202c00d0200c0c900703c4007010103442e242c8600e107440c4141500e508080d20824021142900000d00d048400781803200c4030700c9040b42d1010140301070a510b16140001039034030302c45e80c07012050300c546010008080c048000204800509050880c1d0a1910010070081c04041c0e1200803c545c442d01c54101c001c84054001280c5460b0640c1041c0700120b6031129 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 516484406 1250 516483156 516483161
    0x1201061e080108070611070e07080f1302100c14061603060b0a05070209040c050904061b0215070e0d0f080306010801090b1e3c09010311060912150f06030303040c0504 73
    0x100000c0c6c0362050a07004504803150400d02c920900465039200120319240e5460000d401b00035101c071301c41c0c0d070304070400c1009031712400d5040b00b01040d80d040801c040780c0c9918044290f100014000c400078040c40083c08845d0b403500748008004e080b0743d45d042c0181703501ea200c1002c403403044990b8040801c030100300d10401800c0102c4240d62103402218200b10166846001c00c1402c50110b408640e11781c1d5a441e00388146c601c3c029040c0d6414658070091604081280b100c001e0316074007410004c00d03c42c01d035480401503070b0303403a4004618650041d19010b04140529040c1007580090310b03864017040c00c4100104007400c1c603204925400300c0003040100c4440003110302c200c0c409a522480341c2c00c00c21000e070100000c0b489000600040d000d40490000410a6941125041c0c14448415120310850313801000070460606045c0d0800b001110869038410a0000103084000490700c0c004490046e00c4a000010841607201c51094408403641f42155072200209a1244808ca900a100307000b210014805420203a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 516485656 1250 516484406 516484427
    0xa03034a010c0516090c02030a200c060403201e040c0c1a04120c03080411030a051204060818061b0c0a0809030d0302040f1502031201061e0801080706 66
    0x1814590b00039074254540d1403c018003006841003049075441d041061100303034820301c040b46000303102540c100200303441d00030000e070802910110b1300000c000360f1111700c0e1424081c2c883d143e04010900769846640f460b004842c010141c041280700c0c3c0705402c11001c2410400c440022480044490001d10b0200340b04000081621072200000c10600210307640000707242c0c0341c05040c440341c420891754851810b440e0405a24110603035180c108030381e25444200282c3c201e01000d03002075004003100c01c0d4101101c04a07251016181002d402c1e845010200007695003001c00070b00a5541f29030310910f607580d907800751000c044007060412000d40d01c07110001d075080c04401107140020703218a821a142c201c6080f545442d1000050094400707100018000d083c074a01044440403208a9042c190305080c5458190b800c1d0b00da8500c200074625500b54136401205c0e04c2441115405810f0791460b08040d40c40340d000a05150b90a4010300d07140101c48451407141e4001c441e1a4125000b0100030080281482e4003181c248840 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 516486906 1250 516485656 516485659
    0x8090d0305091603030c060e0c0f120312040f05010c0207050618030a051e1b0d1e0804060305010305060f10050f1305070e131107200a03034a 62
    0x82c00c0e03420805806443c0020000c42c06039440000030816410100f0450380300a400020585c01581c5080860b141d200400001c504201c4054860118000815041d84a0036500c0c0c105250a4802c0000304441e0708072504a2a000e0340080003024591441030740d840400e070041c65444203007480850200c074161880101008400740036a410700a0503900c4600d451036107019102c140e000d0311040043c94000704a404048000c0d042d0814800d40e200c00801d0030000c02100141252078081c03c2e05550411134525400c4c16903120030195650b558407240103000b0305081c0411205401030f400803d0405c1018816603000da6070400c0c80d803064910304020002e10210365140d00b900642440300c1c0325101c40051283c00d2003010a6103034000c0104825003003101048460850400700740c0340005070703c000c035140d0f01603412a540c4222040c52590b0801d82c50280d59900e22180350740980340c01c80100405074003c1054103d607488038844000c0b0014002c1e80101400b00e110b1a0259507111601c0e080346001501c18840120300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 516488156 1250 516486906 516486913
    0x306040c0e0901081e010216060207020105040b04080607031109031005091f05070906020a03020c060a0905040c0309030e0604050f0906060f04120c050618150405061c050708090d030509 81
    0x100c01c0401e1081109a000180035041444280d100d0ba43c0e80c115205103900020003103142c51111803503414460101c00025042c55408190801164002c40480740070300030706141141c96580c0c0b146400e42c0d5040480d28140042d092072654040c4556002c01e40e034440c10001c024100c020020740002c402090f0041201046d40720b4030b902c01c0711800c030000e444601c845010740c2c0400c191400e040050310554041e070041c2c08660202c400d01010a502042e5200c60500440384107a84001c4500700303c4680e42c694120300da06c18a00303404032003a25010351040075503c0c0300351901211100030508200281c013442c1b06441d00320080012040062030039050f01c50740300d500105070509001000856121940158014540c00c04410511405010310040ca070f43c003c0c10201c8400e81f41c0080780c541c401c83d807001c0b2500310f40075400c4a000022905500c10696000d08405440d40da1a9103505a900e40142c230000350701c0340c615143c600480d00507403140c4c2d820751040307029900910300c040d084001100180170050542e2060700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 516489406 1250 516488156 516488177
    0x21c05160303110c030702030f030301050916030605041409120309070524160c0f0b1605010603061e060504053601060b04090f2f070b0c1b01110306040c 67
    0xf07001005020b01680000c011505e13407185105140c507180ea04000492a03600500042120f603a41c9100d1300e9126082c2c0c4541c01c0001420002507000d03100942240e5485828049040c5402a500664900c640071540440d518040320708942c020920013582d400700b094210170005e202d9414088449500320010340802140361440701480d01150300041d940854081025080c2d07070034450303250304840180500e41e40b03d01c82c0d5444d20b40001810b204080003000c605d4503c000d2a02400340070340c010781c0116040601444410480c02c1c0c00328000300e0b8842c0205a1b945400d00203e241c2c10729120b81d61048030040c004086600351950105020340090291340500250b1190302d0098000038004d08005104c2502599116401d150265060301c062001c0c42d00d9180c03130008a0f07440b014480200e515403c1880403e10702858020507103c415220701c3d00081e2203020488288007642c52414014508040b96aa920034200360b200c12a07801d943c0082c0100004802c107001248540ca415806001c0d0f9a6030b500300240802c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 516490656 1250 516489406 516489431
    0x6040c1e021603050601030c06021605120f06070e01120b0603040602030c07060c0201060e09010903020a0213020f040e151e01030203060604090905060613060608040f0311100c021c05160303 83
    0x1150b2580040392945c00100041007000101d01424028000a0000e080902e80e03443e142004d083e024410203104601045204141070001d118988017910240280d03409480c200101900c004140d041e2540090a0a4016581c0340c2c081c2c0b0030051101c20007402d031840c640711038030748902940001d0604800814100503880002c0c1880c483c484080c0c140d0380002c10b100d072801f0440000070900405004499040101c41c3d0002640030500d4501d5590458503800d840c0b2300c40c0d41c0302000380100808000b00090004000c640c0d00c20b60440684994001c082c69403c1109807030910076580103842410442882c80d1506c920658001d8002c2c55002c1005800c145c2000d0382c1d807d051098422102c0180c801d07801800600506044c060103510081100071400d1141a07e88000102900b80062000d01148405155102014072901002c01840c03031882c2100d003502c0c02e5130200302c014001c540c140340240c81201042e9980198010010310001400d0b10f401d1b09255000084040c081c84102040b810550340e80d801c135100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 516491906 1250 516490656 516490693
    0x12030204150c02180c0a03090305160c15020f070b03061903060b040b040b10030e0a02030604121706150c07050301060b040807050339180a0506040c1e02 67
    0x301c0c2015070741d0b0030710100c0c94018007480d031000c10180120040000d00f0004000d00b4002194002c070a00d241c0060544020304044400d8010882c4212a0901071024601408403100e001c1041e1404e074842070a0b80c100080301a40e643c0b8514074078035030346c1e000a41c0c01c01c030071100940510f5000e0070180c111510410b951001f54400030494004807103003640c0f01403040460501d803080d10b0060a00340c0d0100102c40602e0001241000341001c0760040544460b0000c60403c0f0610498415079805000c62340607090610300307900329215110504002a850100c1403044000c45c034440c90140002070014502200003181c1035210754001c0781c001809104856000815444c00d00c1001d0051030003412058959041c121040c0c24801300da4002442984001603190724020b080b103800d40020365900500000741c4400140204440c010111a03501100b4130080e0301c000c0c000c2d800034a02c540450007007000107035a80401c1100319403000c2e4074100000c5034a0b0a41d0385c194451724100751441c1c0d00c1c1c0110f841c44500248041c24 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 516493156 1250 516491906 516491939
    0x203060901150c0b181b0102300a020307050d09030c0308030601200c011b0c0b131203120e06040b040803091218040e03030c090409080c010c2f0a12030204 68
    0x40114080200da941c05c4410300c11404243d07180c104401c40f0301301e8000000d41d142c0091444d001d4150341c200c002e081e44940d0400c104083d0800c0b1078001d45800e0720034406034a80d005044242c41a01a1038a8a48014850490082500c2d8420b410140b000d04689411209400003495141401505403021840c22051103c4440303034a42c07140200461b00b03043c40010440b890740e0307000c84454103400548000007244a4601d109807400c00f050a03444000144190021100e19030100030707211709821540090540c07040d07078154040465502030144601562060742d440c20204d5000d051420f00e80c3c00710740089d030940011a00701c241d45c01268048804100003242c01d40c00b404100320b000d03002070510034650030140114080e01c2c502801540c154036280720b9100d03c1e40f05141d003d6110b02c1e540c55402007045606816100c815035800e0081002c000641c0c00504400d03d8013408850b00c01200c041c0a8a051100ba00ca2404001c000c0c00707015100110b9440d98400841c8003140814140c082c8804500340c2c40803284021b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 516494406 1250 516493156 516493171
    0x8190809120c030f0a0b060f0a0510020312010515030f181605030d030203010807060509033c01200342030d051c0605040509010e100203060901150c0b 66
    0x5074191201c1d0425203480c984ea034151440ea003100c0c4507080031440440b0044c1d4841c005239050f4110581c42c0000490140c0c02d6000b2540c4000f42410158a00e03a000010b003025054010200c1810390302e4204114062003141e0340c9042c0d50f1403c01c00030390600c644242580e04039003000341d640c69151202061506100805021407450140301e1000c111610f005c00410b120380442d41411407655040c890100c0d180c03100c90080d5014040d0001c0d55004c02d807020000b41c0301350300200b91801007000d1444142e410307020502c6107440c25512100c8110a050a06104000c2000c2101020580300000c0640a40035030f00020280c9003080200e041d20a01c105810320010204041d00b106400b1140c020352548046217101080180264840244010748540000c22212004030007560f0441005500d00c02001603c404d80260f07070010300f48000c0c0b2204041c150024100303d420602542c12440c200b40c0c1041c00ca0004480341503001c40508010030590388154a41cac00c54079001d161400c40d507821900c0d415007500042c2c40c480b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 516495656 1250 516494406 516494413
    0x10302040209130e1f0207030e120703240f1b0c020409020301060815010608010501080106080a021b1014131212050708100605160818120d030c090819080912 69
    0x2403174081d1117041140704030740081e003181041b40e2038034003d18043d410f842c0c1c02c0c05403d001503010207554081100e0f2004640c410541c0c2e41403017501018800b61500c1c9644011841c0c10201c50200c0c07810540181400c04100e0f801d030102c4518103076030071a12020808016604107035520b40640242c0c800380100700151046800074401d03442c0030304000b071103402c0581c841c40800c0342840060040303aa0041c1c1c00d40c1140d43d070b0700e081d41240c0c4426481c40028416080000843e02070051660030140003c107419417510b0031400c04000c7c4010601107114404001c54080400811500c107a10010305292419a0b910150b0304d40000e83c2a2003d11308401c491017a100764001c20815400c01c00311100862001001d84141d188c224209064844601c09000c9041d000500e0302c080840d01a0b04c075020b50070751040c0c0d444000c25840007000b50504e055100c4008e080d80c0c00020342003040b0120460300400c402c60455a1410080c0051506011183c000c42d007645002c46290200700704d036074900e130b039000c040000b500b080001a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 516496906 1250 516495656 516495673
    0x21303020901050603040b01120201030b030114011505040f171207081213020904111903260a0906031e0203010e160806100e150408030a080703020f03010302040209130e 74
    0x4010706500160312461246800300100030014456500642c11110320b4600c0c40c000d800b0a20040c0e010701038060543d0f0305586040c920a110003130100e0924126603000d9401d0b0300034190110211418880c80c0180e00f04002e03105810041080c0418003644402c13204420703980307010300c0440c3c2d24030107511449068a45510101d001102c80a1102e08140c0220f2a18032001c402c0307840d50f011489501c0010409480c5501c42d520060003603e0b06501ea0140c204d4007240f0005c080c1d103e00c0c2407001c0441c03202c4960020b400514008185040c44021514041007a0b181c80e00141e1400b10700f200031785641c940540d416103500c1009680c01c105c500245000c0e1400ea00483c000d0302c1d040d10082004184124540104000c20f03092110a84948851001000041c03902c014054068008110268105014030124940010340050b1500c0040041c000340f0071140c0d11740119886600b003c5041c0c0c01404c0200c00341941c200010401423925500a109503107000d0a40f20380020050015011a4841201e0780c0003500505030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 516498156 1250 516496906 516496909
    0x509030403031806201501090905070f030f1506180903080601080c030c07110306130b0708040308070e21010203060102210f0a0c080706140601081b0d06080102130302 73
    0x6510b16060400c460303488407440c200d001040c11070170155a000c41980510b107001c1500d4140541840414024000d22031540c0d1103485100400c51004140c03080d009259021681c15611100481240c3d00110f13509100304041e250070420580341501d030196599100310016580d447d4a00307500002400c92400201a4a0f606018007e460002c0800381004658410004032401031029282c00c0310b02821482e440b80040d140c8624100c00510242da0305201f1103007081000f18030151a00c510745e11030780d1245100d4031804403c1d14032910568008010500c0c3d88000b800070762048c0d0840d2180311004100210000b481e03801300006084502c401001c50350000108007103560100700c03001f55011211003c01e1403c4020a1040060051005e041481440000d452000d00d01c80d44264a046801400c60b40d0707114544e00c0c00b04001c00d07a00021401b0010f4080c00220f071580a00c2c0490322921016144014040283c0300b11402503002000318240c0c0360303840c0030100f0b00d11001d01c041c0c0504403290003054001810b600 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 516499406 1250 516498156 516498167
    0x906010e0d170d11031006050c01020906160c0812071b05060703030e070501140711010201020f0c010221061008071407060515190e0601030f18021e030c0919050903040303 75
    0x540e06080c1348100180490040120b60120131030705246032868482101420b0140a84949108140e01030700100f04000c0c2101c80801103c4414880c0650740c01e0581d6032510f0310b459207245049150106014482000402e004d82c49800c00e042c00f03100c000d0840c603181c000041583d0082c400c01c1d80000c5e52841006034890003081120060070703003420504200d07401c1040d81c2c41c0512441c00010f0100040c1b84081200d64002d406035903000c0348d0784c0710007a1201e4a140e5081d00035040001c50070a0030710604410900b14080d0380d281805160b002c0c042d0070002c203480000b5507c1071005024030042002d40010720b0707840c2c001c04014007025841845c01265a0500405040503a85030300c1605100d0114884085a590106045603044945040c2c0c0c10800380e50301801600200541d445040d245070030300d10b2100440c0804c03150751103618801c8a142840c00c0c48007152081d180744404e40366401d6131060424074428548258142d9101c0c0c001481c0e005c0244841d04503505503407007a506507803240d1010505104054100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 516500656 1250 516499406 516499421
    0x7090b042a020606040b2202130612051f0b0a170702010f0e0c030616210b040507080c03010b0702040207050a0b1801050c0406081f29090906010e0d170d 67
    0x4580602c401b01e00b243c00101a0070750607914140302c04441c40d90159081050701660580d6401d107000400325a5a0390010b08031142910a0301e42e1f1924040004021078460b1710f0385005a4150840c2d2007406007802d58424080d8040d0803810203010080390041c1c00800d80311501403103224a540003140c5840002c50355403d68580c50f881402540085400304a0ba8400040c5a5401661017000c4582d900d410300703007540c00e45e04100801a000031008450000e500d070b141c0104880e4981650700700312542d10700702e04903588082611081d460a10130801002401c411202800b01240010b0005180c4446030342e52510740168803a0483d9000c0c8640708011669440910304e4401007060402444685044a050704e01d510460181c9418451104045001001001c080301c0c0300742500020071074903d4403031030030799884034000703220501d0074048a0f1030032580c00440082e110741e540c003e0840c2ca05074403104010f5a000b00d030380c41c1d005d401180045c8403802003500121803500300320325499410b0b036542410a5000980307605 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 516501906 1250 516500656 516500659
    0x110306060c010f05042d05030702040b0a0815040314070f020907180e01091803090501080424051605130e220f02030d0c03081801020f040b0c0c0a030507090b042a020606 74
    0x282e606c10301040340441107030718007507048400251007059a8006140c0078841d8101a000340300fa1002c0000c940c50310708084e0f004900036103078090a100a04110714080c49004001444442c900c201c643c0182841c2480a40200700d508012440e1141c012110001c2034150b4071140340c07814070000401c1420b00d40d124001404101804034104108079480241c0384080c10701c80c041c10841e14400140500405040c41590070800c050b034113841c9038102c64240d010703100c181c400360320801c0000c11070303e400360103074044844c50310f80544942e0000b0315000880090100007810750742803100c02044c1c01541c90240c5603a60649105141b1041c0c5001c4134018145070056880c05402840904a050404a40c001ea046070f4040c070f2a0601207010340c990f009903070190048204446000101150201c2c81090b0040540039000c52081143e09014043c400c2000843c1d80780300c0039102d90400c9009200e030a0b05038012032407185001d4000304110f8003619100b0302c0982e002403803000c55000d00001c5050345905200340c5810540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 516503156 1250 516501906 516501983
    0x10309060b0d0c05090709060c0b0603013809010612180203010c08040606140d0b130b07020a170f0a0804030e060f0d150e18010b0a0f0302010909110306060c010f0504 73
    0x40423006486012041005400010f214001814942e000d400c02d88410a103800b01000394004062004503642c030608122820001c424000400c2d1304100c2c5042d4121203080d81d4030305080c071081c4000f000800c800300155120050b034181c0040907071000d0040f0398102d08103035660201d600d001c1c104002110200d420400d4042c00c00e001810aa568807400c80d5165900203604c0c04894940404108a40c0c804210040104400c3d070101b013406a0040344174089180603900c0444141a20180c41c119403064140246071140c05001485640307100c0c100c603651240c46400d00c480c001e1101000036295403c266150100e020700001c000d40040c3c004e01408480300d0448540903451418442c01c0980c803003000f040c03030a982605941c02e01d0450300940240f81d05440103409020755a444586000300c240ac43e02042e0301240c205800010360400b00d101da401d20814581032642181ca80c02c080114035804484c03c0311a075900c401c000d40345008144100c1c1c0c0198400c00e421110404496030f0600000e50043d06880c203c3e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 516504406 1250 516503156 516503159
    0x3010506030c061e0721030e030406030e0a0f0501020a121b0309032106150c0308010b180a080303061008070c030e0a090f0c0320041e030f05010f0b040b010e010309060b0d0c05090709 80
    0x8c2c00005d031410358086050100e91203a868280529282c664103000d010074215501c2c0205001c0190f004000000c00c56031a004240300100c091002d80324042c16103a0000350200c068072030310340310f5030008a00900c0307403a01c1c50400c042c50b00c604c80412080d81d607407031040d5a5100b0400081c000d82c041f44641c110541494000c001091f100500310403070503c5049614400004d0711a00d01d81100640383c4070200081038900100c3d110000395580e5042112640d000c0d400301c046c016202c0c3c8c05480d201d44181d002c1e0742c0f60500302c800c50b90102c0e141042000140c0d0080707141040410101c096005010010003802800682003c80c90b10042c266090031441c2c042040c2c1e0100f0006007003c071a01120140c0f0320500404c2e036240b031050362138105c0105507400680b2030140364004508202040d04030318002c0541d01024071512107034130104011641d4107042c860108501250404555000f90070006003a8000c520005400b03c0036000300f8a80c2e55484001c458a40300040203026501e00300d845c45801c210703607213025200c030ba = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 516505656 1250 516504406 516504431
    0x5161403270427141204030b100501080103050706030207061812020705010f0e010e1201240504110301060c03020a0c060e0301050108010c05030408070507090c0302040e0603010506030c061e072103 86
    0x543c50002d0107442190302c4492252421302c10018285c0719005041416a5107903281860050f001c001d403000c61510828060018440d84034240e1681603941240181c07800380d143c588158000d42c000201159026280c800d112000303061407154014107800350428a130b20007100e003002402d040c110b420031414840c0c2d2400c20752845901c201c1401c1915020308041802c40c0d050b10002d041001e900c510b1450030740c01c0c60309401503000c06010400300100c00442035060340d0740340c50820054420308403440c1001581072004211051040141c2d0720802d0190055455050300d075220113100366110b80140c0042480d008204095042c24030425006286480003000703400d00c0c80d00c00a11920016202400d000408200303d01404024002c0b500108160700040080a04100f00030b0080d421a10490040c40c3d4000009403a60906000d00d62081e5801405852190b100e00200056504404860510028150301640100c041c803070081c56017900850002c03c00300c88420b220030500442624050805003400d44a4520 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 516506906 1250 516505656 516505721
    0x5040b0105040903050c0105040c06080c040302030a0308040602091f0e030c0d08090105120f01090e010b2803080304050f0730080903010f0605040c051614032704 71
    0x19034100b1600840c030150503080844050165220000c2d055180c0402d001c1003100d0a02c074441111442c0e1202a2030799503001d2954400d0041d03201c0650590048101500064170642c40c0e107601c540300b00c600504000c2a04040780c45901c203050020803280500c54544040394010b5000070340c0391b0702100203100126211010906510030503000904849020030360100c540e0007402030b54150441c0c0042183c00d4500a9601d68169000303101c0c1440d9140780ca21030340300b10103040c09441c078401806030015050a0380305404400d601940600c0013001e400d0060080b0000e00090011409036000c2c3c0020280b03200311000c2181807034803d9120f040c0200300440c92400800b15030000545a265035412490020940d0821400310b10030038140603415440c00701020441d181d80d1b0302070000e032503040d82d040056400d0440183c416204008403285400440e900307140014040280314900035181c28180e03801c0c0b0400104054020b80741c1c2c10003042008041d14141458101840384100381c0d0398900320118003008400320000ca = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 516508156 1250 516506906 516506909
    0xa060f0b071e11090c0a050319020409060e100806010f030b090a0638030304140a052e020604030806120703020307081e0f0c0618041104150305040b01 66
    0x41141001c5924000c2c01000801521002002c0c58489415010b6152020401103605003941c416031000c004103041210720350984030103402d83c0e12031038510785070385035407490821349802c0c402c03a416000c1001046140c45c43c0100d400038000d103608601c1e58100070083c6144031005030072804c1182d0251004006103001d03840c414041f02c1c0c01c0f9034440c0e07058885034107103420300b110140040c2c003c40c1020308940f92000000e0800100ca01803081c01c0f00c4035482c10300c003c201301c1c8049200c2a81580140302c144820034143c0c03140e41c40c1040c01401e0391061b135a14004202038800c0700b2400003c00a06190395070101c0c80e5503140d000c10742d02d548090003144c503040d50040d2078484050000381c0181c02450041c490b0b03110802600000d150024102d40000c0c4eaa400c4040c0d0b0782d52094002a54252041034050302d94100040049240c4803100141000c0780081052040c00d820907058140c8494404201c183c031615544110300d21480c5990035181e82da400e0894071800f1034044904a402c1515080070080440c1442c8120350 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 516509406 1250 516508156 516508169
    0x20706050708070b130203010b031605010f030f051005101103072306041b0806040f060c02030d11090405090a020904172101031b0b18131b080a060f 65
    0x1030300c90740c040c28082a2405060300080000fa8581c05101009044000074010544210f000f03115290400c400e142d00d40b98401118065080ca56070141301c95170051720483c540700840c0c6000202108003d4028065480c1520004031f0085200030a0205080022510316241c1c81402c1c004003889801415607660b110b8114090288203420084401c1000049460190010003808076241400c040c1448810706401c240c90981140343c2c2c1100143d03800d00030a403144919040036049600743c1194a81e0006031a09003050030850000300205c0a24034503d01c00e034101e54200b41003054480d036800e01400b0823940301910310146070b4420040d030320059031260031280e80603500000c0303c02203840712500c10045d4001c407500c05c01c59503110388844410b07a40f182b041c0e40c101c9024140d01c0d0b100c8120411091420300b15401381e969456810002101e00103aa54051030f120f000c09007503a60500c0c12188808102c6800d8036510902c04410021031400384d604c50826078100d0f5104400300440c61412411041d6900544183c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 516510656 1250 516509406 516509417
    0x20304060e0415080f07050f03070e0f0a02040e010602070501030507080c0a0c02010203090a0b222414030705070b0a020a020703140102041d040302101103010501081f08030c0601050f01020706 84
    0x2550f034045402400c0102144022500b82180401c1040d44410141c050f03940140607016640906240010314401201d00014540314a52034110540c1d03051103000381031001c0140c0800c4002143c2c40144142e0f0f00812076680500699410b210006040d280d014211808014182c018000d002c003e004c00c84405456a0400702c244294510060381540102083d1507802801840000b502c1100c06d0024084d99503414012000e803404100914450012401003402103a04036644036440d009200756503043c2d001c10f0410303a41110098060400d41e900c2290b200c0001100410894200505250303066000480d0200c258106081100c0003543c42160344005410113002901c045414034080d4103e8016000306445c65480c016464a030301e44001003600d040300144100d0100140c2680700d40300381d0142c0380b41031030349034616440e00300111503500c000341c90242030100c040104071003c00003504002c0207020b480d0146480d07544814400d414008160321150252042e210181400d0381c1c0070032108151409400c28 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 516511906 1250 516510656 516510671
    0x16120f020d081f15030b012309130207020a32060d1509110a021c050d09030e1305220804090203130818041802030a020f0f060d050412020304060e04 65
    0x80041c2241e07010b0038a510142c51380014043d45030704021080c010a80b02d6a514080d00ca0185e00512000d18600305142c03004d12200b0460b15010000e00f2102050000141c01d0200c01d4000034031805040d03201c41d0305281c13501080781180785c031049500407034012041d51303a0200041c0008603006200b0400310740500c0d40c0d00d50f1a4010354802d09500742c090807150504120064261004012641c4264405009440b40c00f02010802c5410f2005c008840f2850342d0303503410003107800701c0380001e0540480100c1c14807003440c1501c0c86030b480e08140358240303030703030003180030070541800410f40280f68042070410103030191844240003c207030b9030300880b02141c9401200507542d95078240400310380e05031144001d042400018030b20a000300ca000c200b44002ca4100d078100010000c0d00301036625440d52038002501900402080d40142c13520288000448130041c16541400101d5000600c140c0e0060300c01c8483c4039030f1442400305000c25060f180c06070003024001103160605120000d416445180000d501c0340d42c44502 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 516513156 1250 516511906 516511951
    0xc0b0d05011d0f01170708120c16121514070c11040207020108040813081e100506030d0305040201091a0d0b0609090103060b1c05030306030f010c050403031416120f020d08 75
    0x818020100c1c2016110802c070141100111944140b028550034412074410302d02b107a03000e0303668500b01d8414911200040000303903a80c00210903c0c4115914040d551810f403500e8003c4130307004074801d1440d60703070721030b42288946003811b14040c0f65410381e800785205010303000041c3d8020134050b80040e004020140c4560001d0104001402e076500081c2490259404c0805054480c02c0a0804507071b039101034920a070003800e184411603038125041c6615502142598810758002e610143d00b20f401850700180043c2c440641d0080c041081c1c400c0d12004130300080e0b07448079031524420403007041800c88105183c200408000794600b081804003401150303442041030302c59030301c000b00b0f040700c0c0c190410480d940036020b040268480c2c10841d41940079001d801c10030100c154044c0700d00c1c0d4001d11241c6849080909545040b9940d446034003283c41c04840c1040940001c801c2401445071007441254095091350345008010024800080c0302015544005071404d020f40e00030300042d43c0062050540402a05a0303036 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 516514406 1250 516513156 516513163
    0x40e06030c060c031306210903090b040f05191d0723090f010906200a0204150312090b030402060a020c040e0708190507060305040c0b0d05011d0f0117 66
    0x505264000e10000c3e505012100c00310150110000c020056443d480e9a01c4041c0d40643c0340e81410b040390414011903061900440d4010030040b4081d2404880d40c545801d85102540c0c07003a004104910b04c016000c11040c600090340c01c071045001e80c040c0d10070501e0300400d60f1498662112014101c00044002580248a40c090910844148640010070107105e100014a940954001801641da40b103411500c0c0d4003030460b480454080303586942000c500381610280b03111011802c590b07140510114580503944034020881d000b400ba407401101107203549041c851039241c4210100501c107011804001c080d9001056940c0306806681042c1d445101480403400c1ca1180446070358018609107402e16140d500080318015114030100326214103148482c07c402000500c1d030010102c1d0b0003c134003448500d10a070030050f040f40c072030000c0d40142038455407002c80e9600040785090584e41d0b202c3c0100001ea00d4003040041a00b40610300c4031003800c05000c82442c00130140201b00c0f1042ea48103900e4000503041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 516515656 1250 516514406 516514423
    0x140a090902150f031008010e1209030f0a050105070810030f02060f040905040b01080601060507050a06150305030f180a0b0702090c0f040f050f060a0206130c0315020a02010c05040803040e0603 84
    0x40500030f554201c8081011115002926034a01002c2001070120342403c052081808969180d401030000780c600c00c8207d03402c0d902004503150103004100c00c0a20000040025141c020b200d840013060a1070b0104000f41010001007910709035a1b030075801013000c203117088103568402e5016a0b801d07a46284031840440e0b030f4401d40d84244241d40c83d04c030402c810700c20381d040024181c52225045d109181d981e007404a071113000d0300703101514a0308410920400280b456201c62094015000542c0c0b8003a40c0c0c1d1603041c2960881c04140880140001d815041011030312020303400e03200d0031504d004810b810070790800024080c4510086c0141d201f24045500c03240701500341c410100034040b00d00c0e43c803502c400394101d90004038420b050140d0a1401c0e03850203450818151100f0100c294010196907642c0725aa02c03c0061000064419542d588000b0010510070442c003c1444490140965180b040b084006d007103954002c880010044144014401d50f90040104c1c0e00300c801c10402140b01f5111540024100f8455 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 516516906 1250 516515656 516515689
    0x804060e031e070b07032c0f0f03040e0105030d1403071413060219120f0e130903200309040b0a1e0e01140904031202090a060206060a140a090902 64
    0x500400c8900703207040ba8001e0a0b21442120010901d03264030000342e003951038424102400001c001e84441c4200e07585564a000e040107031040700d08101304107020500341600440c06070402c0d00000340501240303010040d00c0703004040c16030080c80d5490305514028641961414a002081320000108007003d201e0668a44c81440e81e500180e994403113000d90741c0c6490003510515015001c0c16102000500c52554000081c5030440b00c1100800701d0382508841d0301801000d51803e002031100d02d0304d0745407600d01e07113200c0c00c070401000019114010304010b8104141d52041c0300c0120703601d01c2c08034040040032060b55602081500d000c00c20a44500c0002c01c1610250800c0f480c0c908418050026014000590001c80d64030944160107640c84420a050800c44071840030380041c40c910100c7c001134800d260a27545203000603401030070150500b0008246042c0b0b6408000164000c0050000ca40b4014551070700414000ea8a5403131084180b021800161081c408e0007425551003822030107544907044c800400060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 516518156 1250 516516906 516516937
    0x20607080703200310090204120201081e0108010b0406092906090402121618150309050f06040b060d2103060b030c1305040e1905120d0e16060804060e03 67
    0x207a00034a070f80300390400c840c0c840b42c0400003100021929aa44202c5003924205402c1da038082d01c0a80040d035007442c01800464004a50140c0d2a19483d04503101c14082c05140f0008100880318604020603144541c124920300307854095000c3c900a2113581c1500e29030704800036045500b4400c0000b8886006009805400600014180010703508841505100b800d038106117450003901c690086400541c1c5075541c000801c03810f8414090900c41c04250700e40c25a0501d00840e07001095a0b40c01e0a00f5031104080d030040e4401400e10040021a9420a501c2101603031002036001c095120103030382e030038502040ba038048807005035a43e440b4800c1d00000d021708411280b0303e030b403420074031910f10955204130110342032141c90013404030f01441c00303020721402264a58000c0800401200e2980c50303125135841c044031a40301d40c032061800460540040d0658a0030b12600040b180224488182410f801d200c2888982c100c0c000c05000c040c0c0c0103400c503030700180c11810014008403c604424a18415803038071181503503 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 516519406 1250 516518156 516518201
    0x1080a09020102011e0b0a080313140301020405130209030d21050c071b0611010c1706031c02010906050903040b0f13120f140f19020102010204050402030f1e07020607080703 76
    0x2600b0750446c2c0c8646200f079891091140e0395103d815100d0003620000441c1003540e00f401c001c2e20018000c2d008840c1d8004000600c1d20b6650400250400b1460200d2440d80c0c3d000301d440f45075032a06100500c00b0710b445081c0146e079108087c1e005408210740354054405e155482010942c404805400e48030300513848242d221581206c0001c01d200c500807407085000107401441d016100c5c41040c0212020030355281c542c1c242000802541c840700c071200809035030b018414209182800d2105a6509144542c00e800004400595007440815100010b00b0503c1d2640200401c1200c860303e0002c4640c1e000b08100641d8480118101c1105809025404200e206400c485200c3c20320a5001d07140001c0b51213407030740b40290080341e1407458440c2181100d0184a030055440c040746a00750001c1c01c44a980b0510005143c44e4070340c400501240c000b580d80c80b09010500041042d6600c0011400700c0020161030391240134039149000944e40c10b07004141e00200f01c0c14002103030341140607810000000c80480d80c80810301 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 516520656 1250 516519406 516519461
    0x100e28080102190e030d030506010203070b04081b030913050c040e100e09010b091f0b12160513090908070503071401180503342f01080a0902010201 65
    0xf5080030031015400b03102c040708141c2080c0640e1002d4503581000d0040c040c005080074040d030060030001c0c03565040d80000c018803800180d0f41b218040c40341d40f00e00122030f1110300385441c87e010701c1141c00c0501800d80c0100002506a075444080c14a00300020070041400d54480c8040411805140d2040049005860601c1400b61801544000351890210071403c16a10120554240c484005c84aa0042d502c2004120152107205e41c1140d820a12425a15096664200094690721665440409120355802e000740c03a8185903211a008015142150a206002c4918035a803666442161103055840c007030b40003080902020b44420710380200aa9885450038207000091210341e04103101c0703a511302500491381d244092280c07003140f0b420800543c10945d01d032004201c00c0040c0400c0854903103400c3da603078000081c102d03070f60141c051044100b003402d003040d03000310000e04540550903443c001080c02800701699020320580d03400481700d000424a0313045800141c3c0184800300c65900c00400d18500040720 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 516521906 1250 516520656 516520661
    0x30103021005030610030509010b06070605090f01050f1909080c03070611031909060204030506010f031b1505160203030a260424140412030b100e280801 67
    0x4803802a180010700414405048501c0d100803148184d000030f00100c0308881601c179500035a401400c98000084080041e0000f80194100b100f0480d1946c0d2210304202100c60107000301d401c40c43c108002448281090103130010400030081c007155204890743e2401c03514030101d8024060030780d001800c3d10382d9500364528103034903a4011401505d410b420160846180c010600441303210b01200b10341c0072461150700c817040340034090091741954510313024071000c00418800d10045000301100f5204030145842d5107801040c070320140d032441c01e900070f00301820030000301c0391600e0f10a8081c09240c400d45c0e91800d0849803c2650030580080e4040c4804941082c940b070b00540180c008452084c1d03508101450090100d030030a1084500a1110542500c00a0802a502c2058022240005000c1603440811001c80340714a02117070b0513501d800111040c01c00d03654051142c0501107105880312120704c59594009045c400c501e00109004404600150017804420f4040c42c14461078040d44a8001d1707650300d00d0501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 516523156 1250 516521906 516521909
    0xb0301080d09050f011b05060c0405090a090f02091807140a0506030c04060c05030403050d050315120c01080c12090f01051e150a0b070c03140f12030a0b12030301 71
    0x1201d105141690007000c0c011240e0b6011254001e200c4041e109451004482601d03403145113041809544200038005041400b10501c00c540280703440352110b240100300040c0c4080900702000075840c00840d500403840790407c140145c0d4056a2440458459403082c0c0151032484141041a025040c03021030713100d1001d03901025178541251f0083c0300540301c02c1001014071081d20804080340c000c11040103503900075003001d1324281c0180e0540307003001d82d02d03201c2a0400800705d50260000b403002040080b82c0b034080002550140099481c1a414842409050750f101c4002000f1170500042100003400d04004c107086811249032038154400504090140c2a6500c2c039800d007051095080a00140000a04500d65460540104009010b80e01c46100f43c900b10b00b01b02030081d801c500c0700840030600c3d0b482e090060159521442c2c885402070700c1c40c10410088815248001160f8000c006803c440304070004805149041c0b07800c01c19925103441c5c5406000b407101c2101c003904882e495100c8508280044040c50 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 516524406 1250 516523156 516523169
    0x11090a0e09100b0d3216120503040e09250602031c24031403090a03081c05040813080609030f1305031c02010e0a0c090203040204090204050c0c010f1b2105010b0301 72
    0x4d03001750b0142c03000c50302d40c0c155410071011513418400802520400388804034225014100390b9180940341c2c610500e5070b0000b01c48421056122500600d0300030303071100c00180c5202d140d144a41441d8109540251a441512040b40746c10801c0202c0a04004581e03000c441110f03c0d640d013100b5811130140450504071803504c003d9a001030480145035460101000300d40c1d42c040d00030600d040841c15030b902d00741e10342c001100e1410f50203035003031450101c0c030103500c1181d00450080392150346410305448000519071003608440102d030013901c00c3c04003009000041d141d003e00d03290a0207840d0b001100c036601d16030f03403942d20081e40741c81880c2c1000690036041c00c1440410a076a4000d211500000e00c109940380315a19004000c80401c010400201c60594051504540b006001182540840c2c001909445066036800700c0202c0004076000702203400d00c1f1b03150342e40780102018814050340a040303882c640f43c2c005070b400c240010006024580780301e24030000780c0c1104041041140396100c512004268009000c0c0d274 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 516525656 1250 516524406 516524483
    0x10e120303160e090618182b14030a200a030b0a1d160e04090813060804080412081902030405013c0c0611090a0e09100b0d 54
    0x3c215070b00f4061040c82c45100c0c05018035201c0352250350052241c440040c850b0a41c07901003010030300d10710002d00040c401900140341d502201d0710901c03040c50005081e4000c0701d041c0030010007540b0f07003c400041520381c0001030140c0042d88034486504030051401946111411980014075000050382550005649800680e001e28056480f0710b900e10746001800c0d10000308012a0000854400c504a24071002a50700d25001c0d0055000b1000f090540f0700381d000c11282200c0c04603448001643e01b001040040020340741000d01c07400d051300c7d002010301c514003c41500d09501090b400070300500a0849100100103038400c505071210305c10080d241d1300980280c070300041410010b1a031550403001480820104420344e0500c001c20607100e0a0380e01c00c030074080c1301406107881034040410f00e14400c8030301c602041500c0c1e5070303910000402c21030040d5103508405506404c1c803043c40305454000071030088115030b02c040082c41d605902c1c00100e03000300340d540c02000f080b41c3c00000750040c0c1b04031000c54a58104510309 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 516526906 1250 516525656 516525677
    0xb03092b1707020c09040816050601240c0210110a030e130504020609010315180f0617030d0e070e190b030d020c090408040302040c05121311010e12030316 68
    0x1e1060804103849080043c0d0010740d0b0242d0f80d250450b0540d40051090206500d07284400c0309540044484803010b41c0c2c580c0210004000613080c01128001c0c3d40c01c850015070380b8499140025141808040c8040d0003840045141d10003079008480031480c1000e95402c542141d111807400402c040c0c3c04281c458001c4000101605d507003240350003070034062a40200340c10f00b0603040a004500600f411041600c282c0a4800001030703a410f200c0000d03918404030398000c1024026004040309940b41d0390f000c00301e02c911807060081c0d42000402602c205004803800414061181e90903103140290a0700030300401c1008805000b8003400044003c041030b100d50307000b0710410f0081400c1507258034410a0541c0542c01118000c000c5261103c0119440362107070701c1d980c0c00d1648a070042000c4500d00718815000c104002038404038450101c84460740020044818007031801d4583d21000d258500707440a45c103110f0b02c00e220340c071039984083c4040c06c040f41c10003c494603072501c0d002607080da009006007070000c180c0701c000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 516528156 1250 516526906 516526937
    0x412170901080a022a010906060806040309121a18060702010506092701020f07050609030705070b03070e040e0d090b090a060c140601030f03110105040b010b03092b 72
    0x15514031100585803850169a05942640650b02c0341c030425580000140b20403446a01e4407031003d500c007002d14000500807101d8139100d42103e81075040000f5941c452810800000e40c8445400f00351190341c003030b6001b040124a800f034050300c410f842217503050f0050010408c6095000060b84501d0548400f29a1b180d110b401c0c0c16401c1b030b181a140e494120740f01200040d20000540a0645180c43c0c0c101c0007540c3e40001001c003801c980041e00010403050380098004c0034080108074558018130920003452a0003269500d00381d50385850b00c01c041c0011000303c005128a0b0280b8041d00310110094000c0c4401983d11003e9911284c1d031184a5010071681c602c046454001002039a40e0240b0241c54480d0040c10118190340314070070901c2c00c0705e100004980c00c0d1900340080c00401d00940c4112004400c0c1c1400b0300c0c2c060100110411040f54913854131041101241043c05128111080385c04110382c1d0742c6442000600708110800c1c03104407144850650811310f60080c00361030b4071007003030765480104000001 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 516529406 1250 516528156 516528203
    0xf01051219030f1d1f020a0602040b0403021009080309100c0f0303050f0106030209060d090c24020706050a05070b04020f060a080a0e030c100519051305010b0103050907170307080412 80
    0xc241c031742c0055505003203c60620300a040141015000d0040300c80e90782c2d265844900f682d006400060280202050070021402c1200c03103545487c1e818100031042c242815007041e960300170007002c07900c0744130b0382000c0220a5008100c2254026080025030180204504010340036100641e034016040c008400005003544c843d1098803220744008011503d0084801c152030058100200d0a582c000c2c491900000d98402644541e980040415401c804030b42e55a04081d040041c5607000605104c8100b240800d4642e100c81150110355110f01d06803030301d0302c4a0000c0740041c011509001d03000480020404142074002c903e503440781007988010310000440ca420940c4a0040607018002580010500d280d904070540196030b101c07444070494480700d0001c0417040b00380c840940b086144540389200310000d1160a00509240f204282414011420030b5009142d951180b4403034404a00014040299217860910403a0007664001c041c4584668540c40031031a5001d41c82c0007200c180c0500c0f060b03100c0724100c0f42c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 516530656 1250 516529406 516529457
    0x5090a230f06210709091a01230f0a05041a030d0e031c0c03140f0a030b010216030c2306070515070306142106010303020c04140f01051219030f 63
    0x3c406001214a010400c8002d409050800c491500201c0c03403400003454601d01e101c2c000c2141111030364155502c1d8080d95a2825550303030403802815241206d040540703504451a0489a05440014001508180c44440c8581c2c6d40800f41c1e040c00f03603a855041d0164031070b25850a5200460560b040400c00800442040452040610104070040781d1100401d0003194003042075086440c40b10b00e072400303504413084c0540c4541c1c640c00101b59528942201c5507030400084144110b5203410540c91030940d101d01d42640c1285c8210a81e1317900300b022006c4c9901086041d14007016018000607100e107080d00d070860312140030029400032203500000261410744240030b44400c451680342440d8400000703409105440400d107a040d2607030003194820407041a020004180218003942c05000d41d250780104008c1030f03841d09412645000b5141c1c0602c05441c4900c402c0c18110f810490341080030300300140308182840b10380041d104242c10071502e50000c2c0368028030300d4015040d5580c2c580c40700003543c4c03c0100c07080c581f2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 516531906 1250 516530656 516530719
    0x807050612161e020304030606320102070329073204080d2007050609040903030b0618090c031e06040e0d0c020a090605090a230f06 58
    0xc0011030540c1c00c4003100624100c44a2400043c00e03e12100c4000c60104050f1189005a0001400b0400e000d810b1150308040c143d02c03400506011007244891001c001c8203415441d4514004200c46016030082200e6801182d10282c00304071285100c94245180c503020404a9203803462000040e10070b071142c40043c00504400e4507140070a0080d1080101440c1540c031058007540d410400481d245c07104000128080003150707140c8110610403010190038920381002e81c0400c0d03105802c180441c2c0d803030340159050000b0581d00091014140d0404070b010303200001c44c0310b41048001601c86c12031039082c01085031480c0c0a42e038056807600c0c2d407800403540c3d10049605100b944a001004506444440b5056070030050041000c6424031940e0382250500007241c0601d00441d841c41c22820460a00715619402403004d014208540382ca0180800d1103158001c0c0040083d540d104600b811414642c0b03600c21281001d2410303200549000c0c074594a00110645900c2c0c41070f402c00507101c5d101c1100c030a00c040c000782e4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 516533156 1250 516531906 516531937
    0x203090604180f02070f030e010e0102100506131b18050906100c0623010e040b01060f0302070b01090209180103080a0f020c1002031c050105090c09040e0d0908070506 73
    0x1a204502030800c0503809940c8255465001103500d084150010740069801b40c520300300002100d141c003420402d40001218180201d0750f801c410107130780105011000765001e03800801c0d256240800603402415a00398100080d2a01990070481c00c0b4000c41e110300f15a0741d86071507113408908240c094804903640315583e804000e600c0002d141e8203000701081074951860501141400660b903078141540d119100350050701e0301118520b8480e0024803e880e005221909082c2c119007015240e251650005000341001d2103120000482c20354420343c1100d20454000803403900c0c958590190a003c0c0d480302d0407081c0b0400d50030901642100044820904036584404818038241c0e102c3c1c41622408400c4204200f54041d600c12002140c8684403440282c5882d6030166594201094034524410044482e078400d480c40e080043c000358640940070b5801001c520216612120386900103009000703811400e80250180041646509030405a50400d42d0b8010782a2050507481d041442194028840050406003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 516534406 1250 516533156 516533159
    0x906090819170903041202010c0b16030605090402090f0603124509060a080a0605010801141006051606140411060702010c020415030503040e04060c0906080f25021c0203090604 77
    0x381b090076020070007841814103c201c0704540d02c0d02e150856040760554101c890204d0400f00ca154580310b1180034200032030303c2c0125810960085001c68400900e030b5402c01c500e54020940e035940070485962014918551217545900c50f54042c80355800d42000c184014180e0060b000034680c0c800c0205000140113004c0c0014007650804201003640007130701194010600c41404144540d0034880c00d1000340c06000702017140e503d4540c100c0d00310390301091f10040501540003400030a185002406c01100d0f00d0b80750860300c4022002c40e07040340c0407940c00001c200368a4079000d21207517682a515644500d01030800c4c0c2d9803060241c01444010300c101d800003400138444100b0780d8014641940300340700c070b0a549012034200705d840b55039140c91a80680c1000a480c1d68041c20041040780130300035072020000381d10704204143d242c01000303072000300040c1c061010510342000060b450703118014641c04500e8200421080540710311400307034031261425440c90b01c00c81d2032464441c020740004205c54448102500080c50035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 516535656 1250 516534406 516534419
    0x20d0f08010302011d0112020708070c090905101a040507020c01080105091603091103030403300509041d120c06090607050901230a0e040e0c03030d090609081917090304 74
    0x494845e04401e041c403c040d0480d000e00d8001b8400f07002400c0c8155020b507034543d003900b481454600f066100350340c500e0508400500160700403c003400ca176011040049203107001400000c070f8850f00c0c04941030b0420300d008104201180d0004101b000701e1021f03207640a41d640c0300c80038031107019412a960408000e0341da0200041520942c000c81200e40175003203d4010140002c0001e0071984194000c5c2c0324040d412030381440310380e05458140510072182941240300c401e0040041e240e030280c040054401d6942d88030b410420000e100f1102280c007002c5013640c40000c2d05803005c1c040d80c0c1107418800b26900c240030004501d0940007400e913000c0c600c41c1c0c0f1400d05007104c9600448600c01020f0042071038071120120010007503600700140030100169100c442c0c0c82c1000e4030074003040b211036950448070b0b607003c032240480f151401310449054040f03180010038050200d090040241943d0702008010800010381c00282c034440402900480109a4540107070100c15a07802c07204070b200380d510040641080100300b004 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 516536906 1250 516535656 516535697
    0x30203090d0c0e04050606010206090307022d12010203011a131e030615060e0405060a0e090c0d0b0f010e160f1403100806070513030210030e060403020d0f0801030201 73
    0x41c81c490341c0c00d254001e443e2240c00c60288401e40702200c07260301c902e0503c4804c1da0107210352070703001e03007140011414144550009155118a5840303031041010600910000010001d020205002e014100542209800003024001d5009100302d032089038100100c0d050700d12800c4102c8440c0308241c04541905030130000c03040307101c1001aa11080700701464100200041650144810142c56042041c0b0643d240c4040a001510001c2c00284103e280404121442e9200101c0200f9209a0079680080781ea44180f210319005442500d80d030b000421f002840204160030518510811681c0c1c58140140d07a9000035800d0400b090700c440001d840100f03c442e10081c80340765410032403e40b40c54a402c52070310a00503403405501c20f5440c02620302102c4000e000c0c8007030030061150400032034604646002c200c00d055041042d090b00000703115400c85144da8200f24429046100fa89a0002c2500c40f641040d00e00a980c81040076107900100b135050046400751809900032a040700d0b01a19000c0341c0d4101c45c1780050b40c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 516538156 1250 516536906 516536929
    0x40623060a020309211e1b0f12010b0a081c05030601051603110f0706120b0f0414040506010b1c020a0c080c01021b030315061804090b061c03020309 65
    0x1c5110901940e0078541d82c0c1020390070810a040d511861107250103074941e040c1501005581e241c90341071b40b5024180307100000c00d50713401c01510141580302403400c0300007241043c01c05242a4803901a40000c80892410740c4a8202420211151100150707a44000758881c0a54101d0348070280c006000b120081d80288021540090149400c0c0d18010b061054040003118416096000595540b41c500a81108026030b40707940c164440100303013103443c1080040c08030300350910300e0b04003e0300c0715001405a2a503aa0b541a0348100900501c02a12050580364009101302d800303070750350f10600740005100c0013084110b54511341040c10384d01661500141c8180a5804030510f102044209007032a0f0200e01800c016008aa20039000035a84d40d00410524401c2c000280c0b2107a40368004106200e4000101c0e500000c0f60741c416a0141d80719640b982c48a0b4807007805840e015005400c0440c0007040024296046200720001c0303400415231044103500780c44024540d503000f00540c0c0100028549881c0441e0000da = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 516539406 1250 516538156 516538177
    0x3042421090203060c0703020606010e0a0b0a0909050a05070f0905100507050a060c1806110c042c0c01110303070818010902121608030316030b01050415020a0204062306 74
    0x90041c035035070109281881c00c40d03c400d120700c1d011601c00700305135041c01a01d4000d0404d02e0844140450303000012600301151150840340c03400042c58070301c068003951150005000c5150200a0b625220703020401030130049805200180c540d0f80300c1561140500f4a001c05c1c1c0d9000340520442c3c540b031002c29a0389030302a000a1750107110316241c01e00012151b001c0d448284481d944da52800203c5844d00d03042c2c440c0c4680004040c0702c558051002400d81c00281211100d60072031340814203540400301c0f400b43d03c00902050032500b002c85083c0403200000144912040000c0e82c1c1e000d010400707030030140d890b804207030340e00300014003200d02061690800c070b50100c03070110909000040c0c1519950028085000341c0c200081150440c00389a240c0d10001c80c0e020000785441000f071891450194540514042c2c1c80124600f4195120f400d2171199100720143e0b4041d00d00b080700040307401d0500601035035030f04540100b2445541865004102e03240c400e0b120f01a010f000002c40d504c500b14401c1008155000f540030391 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 516540656 1250 516539406 516539411
    0x3081c06030813090b040603030206040816020901037d0105010b3c070803040b060f1516021c060f140406090213020c03042421 56
    0x800880e0b018401040d6074030070249103d503114900b8407030f04280c0c3c240c4180700d803007203180040401c0030940208800e03034010b07481030301e0039600c200040000c003226451715000780d002156840007108018240054800b80810440e5480300c0590b00303076911598a1286450180340d041155800ca00c00d20174814498035a28140f45207804407000c114900a47c60740d40000751910449200f141101c50740038400e284c0900305a070001403034590001111100250b40442400000711280c5d0107507000e1745805441107014184001080e80c171807460506001d01d4005440c140c941803200c00105a4903c0e100b00780d0140403502501400c0a80f00315844100365801503c01c10240ca0f42030414140141c1d00c05100982c0c2d0340c11324003110348840840c10070b48101d030401c110662130640742104518224111081c41a0300560201002c96040104d2020404070822001001d030365900100c0c1441c0340030800700140040d00d4825031541211000d01d0015220411442c81c042c005c55028074800b00c66580a099034019640d094002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 516541906 1250 516540656 516540659
    0x91b031e0f1e080a09090f060f2d060c060e0726010209060313030906050304020d121101141e131407120804060f080603060a0b01030f020301080c01170103081c06 71
    0x50303000e10743c040d43e2a04c0c001141d0100500100386144500126401d0100c0e04103c140d05040c100e100c100aa030040d0142180034585002180e50b1946113110009401c406070300384956030700da024080c04044481204d586040c00008140302800141042c222a56411101d20045d40482e13601c540c19065100300e0084e5408101c0310303540386c4902000314020b0341c0740d00c12a0500c2e5101d080c01414035016030401010000208140300241c4e407403a031103030f000c80c3d001100741c0d520002c03551066401c41c0c0901700b80d220650030100c00700060001034130610700ca010704d02c821500c0b903250b07001d03c0c038100c0d50210b50401120b042c2c0f2a521020807013034100e411600e103130b804c101c07643c00340c03501401d07070500b0b103c00d60031102404005420b01850fa44290341e00c0c030701420703802c08443d1800c6c80d100007515600000c0905081580c0c4504c2d0020b01e82c801d030440c40c1e0080040344119602d58440680d03541f00c0180c81351079408200c1d841c015a200c04100944141243e40041e1b5003410084445400c50401a058281c0c41500f5141e080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 516543156 1250 516541906 516541913
    0x2030d06030812011e03030e0f130b030106090b030312060118091b030204031e032007080d080c120c0403081c0501051f050706091b031e0f1e 62
    0x84402031402080d005850b01e041c0c46001044030303c141c200d0300c0d84020180c91012064000e40717041003629494103284412400311800720f4010b440c0c500c00190710012194883d045801030380e2081c00c0c0c800c0e003a8000d1180c95290703815041070b160036000e1160582d20030090040e0b96a58a082240c000d00149070440f403200c07040c4400c01e0680c201d0707041075101700e03900d5000e07940d01c0c038154801a09000c25400e00350b05052035500c9400800304051410303408005420840e1080500c94891405a10440344c07110048014043c2010380c0c45030540035407509441107202c5400054080d030842803161030302032102da14005685694003141940904121441c4000f03000200c009a1103601030308410314241d15220300e90040c88140e0050320410b90050340100b5003101103656420f01405078038400d04190408581e02c034860301d07018000300070b600e0340603006030b80e203070440700741400000c0084048074040c41280c80041c00843c200c0818407240b0800910801d04d100003003000a03a90400f580c0d080038903034401404001e5544 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 516544406 1250 516543156 516543161
    0x70501020d111b1f1a04020a020106050901091a101211030f130c0902090f1203040305071a1209100f06080d031a040207240b1302030709030b0702030d 66
    0xe5040b41c44900416503190010f00e0207240c0d07016003030440c001d25004a0766500050440895054054600d464070a070030711618800f4811200d45902900441d692095510000d0003007d107030140c0ea12aa94050002448043c10300071011080e501c510010a4000380c0410019030f044001000024441140d43c0380b000740da00ca11502c600c00507018800c5649181c450854002004d0041ca1845000e1403481400c02246040b0f000c0c1c0151003110000503030b50218000028200b89990034500e48c406d44034a503810f4681c03c080050800c60f40314000702c900941d10744030f15000140000040743c1140340c00380f0100321182d1000c00010b4008207044140c2c0c5038420a45030f500309903400700c1c001000c965224402041110801c0041804514403450104808800c0310340300201440c25147c040c3c0700d10303004940c0009229625100805400c519a82c5500f85000d420f4505e0280c1803200e0714034800c20a9407280028201f407402100d2041195a80e09141d25003141e81d03c58825a025103254118030090020110302d03126803 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 516545656 1250 516544406 516544421
    0x10f0908190b0f0f060f030c27090f0c010315121b0801020901082d09010c0306051c30050301080606040b1c1712060118080a0602070501020d 62
    0x3040c0380c20741090a0a8000c0320010303091440418103402045502030301000e02c65040141220652510440715001034600010314005c02e07406035408444481045101c81c02040c519040426840c50360343e1810030648030a10b400c110b880c0c6801c412955045580300703500c43c614041e0b031b20406900c034548400c8103520b00218098111811400448500480c2100c0c0c00c1010040c05958001c1d4079100d01c41000900210303001e00603000b291040f00c50700080c008401521549480b54020000b66850240300c5130740a021384550756408280380c184041a00d090070f40002c0392250442c040c50320485c400703903107001071409941408003001417407100c1901002c4c0c0c612040c009144042c4c1e01c06851b941041e0b185070034084081c0202c1c1c421440c0502261440d00d0343d542c000221003815995481c1e0804505010b201d42240601e0f4a01c00b900004801ca11044d80700e80d82806400203a0b9000520700c00a00001e811581d075010b1051142d10420401002465940090002d284204005030400e08144124016070300c1c030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 516546762 1106 516545656 516545683
    0xb04030f1703040b0a200316090f1404062c13060c0305071101060b0f0d0204030c0b040303140708180303070b012918010f0908 56
    0x40c607080003282400d03085569030b03180600c1c08076220102121600001464003100f2100121141c040010082901d101c103403454642d401c080f419646000c4040040061110b00450035402c01c0551100600a0007180d1840280d050101b109580b50ba410902e44400003003046a03881200c168203404501c210341100c4490b40391054030080c068000301c00a0b00c40ca007044c4854210692551115216100c00e03078901c0790210300300316035500b6550305100d00c10780703942c0c28803101d502e00a641d00101030f5411178000040c0380541d660368071928100143c0c010303c6000c0380400c0070810300d030b0010810384110b44101903031781c40c042c2591f41d0a0300d1400341c03109010522278060080e161070340b010000c4481054005000ba4034941c2d48000c03208240780508036504000c0d40b40300c21855407182b03503805e4a09000078852815031b9640e00400441b900e042d02e070b04100800c2400900024012001c3c00704140107001c = true := by decide +kernel

theorem cover : BRFrame.Cov 516366906 516546762 := by
  have h0 := BRFrame.cov_init 516366906
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 516366906 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 516366906 ≤ n) (h2 : n < 516546762) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
