-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3657
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:18:00.063573+00:00
-- url     : https://prove2.me/submissions/b5d8530e-b38e-4c30-a79a-57b29166389b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 657553956 ≤ n < 657733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 657555206 1250 657553956 657553961
    0x702040231080c01030b0f090606160804050a090b0108010614130305010b1507171b1b010207060e03030301050f0f06030c0306041d0c04051b041e050604051804060f 72
    0x5406107801d0301e914801c004401e024081440480c9083c2414401c80e130b1100000b0701d00c014000d210038400c1c50002d01007a9962507010075148000100c582844207048503081aa90541017881207600c83c00c80104080380c1c100c071a0099403400320041c0c40304a1140d0a0440589007924a14200300d0007050622002c8441040302c00d090f00154028000080e141520f9002d01c600b044406034140c40e614410410301d000100c211184020842c1d1141816846003910302c006214000006820622032040c0174290000c0041d4502c021403008090702103c00c1c540d0340381425100703001881002030789500305000411003820311011aa2129070000c0c07090741c0302c042100004019400503109c0010301c600c048100300b41d6040611a0064900c1c0711a07806004a4100800340e40e52980c01d030440e0302031a00c0e0008200c50210b24001041000d0541900c01c0d1140d0700c504042c402e2143c0c046446000c4100380d540000d0324141074040398107450003d002c1401890917040044c1e0340c03000140c01200e44660703e00d81c60a46a5461 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 657556456 1250 657555206 657555277
    0x51903110a080103110904050d110c0a09230c04060c110907020604030e0603010e01060f11070b0c011109010c140715030e06180303071107080601080d0206180307020402 74
    0x6444040b60780d41941040701090300340300250340c00b80c11580b0600020070f8000803495804261440d00000c0c00d10942e00c00c506140740b138500e25402116006001c111140c0503040740d500c010b04510320740b1501a0740c104181c021802900c107155184410001404030760b02c141544a00507004d1403000c1a1040d0500c042041440c0031644000140c01c04001e110406a100d000c681040c2e5003116201c0c21541042c1041d6100c640601c2090240301d4118030714041c2502899100c4100f003035810a407607101d0b030f991140715003561140402a805528010f4189500030f100c00c1926510318046e929400e0024560380c0762481402078120108052143c084000740a2890000410110a059901245020320f00c1c101500c0e10201402c0c25415110360b44030301d40100c1d000010750354031003254a0000d007000c0c08a058503060000507000ba03c2e80b07000345e07400442c1c1d2400c0002c00010041280c1d0132a4003580c0e0707001d4042d1040066174020b840903001000b1010140c030f40f9802800302c004045000305079400d41c1312642903250404 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 657557706 1250 657556456 657556477
    0x60606220e041b080a0c180e0d09060f05190809030d020c07050111031206010311040e0c130e0f1f05041b020c0a1a030405010b0d06020c1c05190311 65
    0x8603250401003803c00003550300070880380300101029640c0d0350b81c520b143e000e180503000d105a00d44610100b003d030141c0007240795801900a0b20624414070f8801060121507004031400315100340c602d152440e00c50000c660341059160080c05403020515011100d2250203400034915100511070b03d1191030951000301500d04109006180c80f80c035050014200d5540300121680a401c24400c2025a410710f5400342d0f4407040074a40021014032800c00300140d8004c0e0f0b0010b41000500204020010003120024000c407120681d140351040d0f134038082007880034002c9031b00c0c00e415881b990100f2290150040da4101902c00602c0d441d00a50719070740400e0803651900814140030540104881c1100d406000c041407160080d600201c0e0a03081008411001300c200f1500f0f804000d000001500703100c429402550807d00003455040e0341e007201d04080c0007030340181404265500840845103241c00720b003c410020a4669200c26007880d41e11801020010702d0410307441c0605807030f9004190105003240007040b480310b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 657558956 1250 657557706 657557723
    0xa0207020d0c2d0308120c0f070b01030b1302060a11031b1606140414120102070b04051005010501080a0504020a0f1d010803130b1c14090609060606220e04 68
    0xa84000b0142c0c3c0389503c090307190b4801680d04003030000ca5480801c40d1a920f07860709059625840f41c040c807a40364802c14202c1c0c5101c0c800424084204002030344140d04990203000c00200c40c1d00d5034044910451403088000758086170820000346000c1c0210040701c541d04885042d01d0800c40d240b00640078002007098030310281c0d0031400140d02460001c1040390050002d514100004041907042d07282d4a11a50082244401d07454a9610055940e54201c41b507401c2410009d41d242c601074a001e1540c40000d03135045655024103c560388001150784111412241d0503075883e8026111411948000c0c00040e00580c0c2100c400c440c0418080c1c0c1070b0500c00010312640350040c00740c04071290381125100381a0801403046d08100040103503052400001020b60704242c4943c0c1e91011142c480300303170501c2d2a500390f030038040c1080800050310070300080784c0d0b02c1040300031300380e41080c0c0d0b03011509926079034216440b40c1e2040e001c0c00040003c100c405000380c00c52400381001c00d421a140c09494607242e4046404545501e03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 657560206 1250 657558956 657558989
    0xd0327030c05031507210914011d03122206110306030c2e0207080607090504050705161103010221151503011802040909050606010e01170a0207020d0c 66
    0x40401c0f021644a1665003088405e00740701a0041c40650056607600800610715600310020540d03a002403100c0341d002400d205041500101780d03010740306840c0503034000060403035410320311314000c0200c540c0c031004031404c0c12a6a0f03c0c440780803200211102e110351520820714018000031424032036642c00711031080d4065142d00c0c00d1000c251074400260324407805040e00700c401c2c11030580000304002030a815405028101e4410980482c64500641d0240000c2e100e0b42040c0444035400441c3c8406035481070341c06119035030f1103940948442c030440941506c10145d0b1441e04c8041001c0300105034100e00e00800162400c103190b0240c150780c51280600701000c4c4a0f24007409100c900d9131306950841e4100380d40b0000d150704e40c8402c5c103055000500c258282d01070110384241c0034070003560441d0b01825195404000c02c840038103000350750780c0342142d41340d010504ca08098442d5600070701d0b00f4560410010321559040e9540070503000650407010080740c011072004210310014101601490107807619900c54005035 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 657561456 1250 657560206 657560209
    0x2190606031e0209010b04030b0105040929040204110a0516030302160b0a0b01020105011503020c07180c080708010513180b09060a060504111206010c080c0114150d0327030c05 77
    0x1354040e404500ea1010411082002500b016012411100211070004070320186081143d03038181e280007110b40d10158803540d207808628100c1c01d2030040b802542c040003411801002035941e4810915079a02140c4207002e5866482072000c2d115039128071074a0054200201c83d16295104600481d0446460344150200801e215661103502e4482000b44020b0000d940340c071201c4d0345040084140d80c001c0640005d240d0a0a240410414008081601c2c5403035200f02d0a80030540144403000c040f100241c881c50220f401e491085c801d4a05a8400801e01070b034a141e00c01c00f020042c5101e000c0012000240009040420720280c0750511030045540948214070300303542d0a004136211340e001075100310b145c0700701001c0711020041076515442c8140c00c81c1e02c05071120702c0140c0300d00c1501407004185e024009255400070360f040d00404c590003082d0f25540c1031038541c01c44200f0300074645405103030401e20468021000c07d11a8050000c08014094074103a502007000440c1d108102580090320401c04a0a0401c0f29 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 657562706 1250 657561456 657561469
    0x12110a1202030408030c280302190c033513030206070f080c09031905010c0905011112160510020304020f0f0f0103020a02120309010e0f070602190606031e02 69
    0x803200c845045180d0f01e490fa8421340c20340009020560342c81303400b040d0078840307042c0042c0c011040844034a0f2051810b400c0c0200602030b51004440f258041044483d104200380250000061613515446240c2d958038408000009000a05103250b40800110303040740c9943c2c07034162020700421400415a007401c241d4100a442c06038007410020800003040c860001c01d552000c03d0680240500121964422045001901d070031400002c003004092200407810810505601411807402d85844c5c03441403a40d65801540c40c0415141c4141c2650003c1540ba5007104002d002000c11401401e0b01d115420565142d1078070b00181e0560085440ba40003080c4004c0d450a0f40c0381c2030b40f1510460700c00301420070f03110214622040c9051850b0603d60041004403011f030003804a140b00c0341c1c0c041046500d03031400082142c0a003c0c028800c024030b001d542d20303142542c400801c100050301c0c19034004090030681480c85150184240c002550010341da010301100062164291104d01d81002c210b1101c05082401000341 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 657563956 1250 657562706 657562727
    0xf08070207051c05160806070f03061e140a06080406020702041b0906020624012115150804050304030b040c120303020d0506010504060e0d08070f0309063c12110a 71
    0x24900c418a020040301800040d11a4440b008d8500042101088601540500b0705c2d0381040000c0d00c00e81e5420742495121540030002c1b030700080c841521004c0000300703020840b1541e0150300300140e241c1c000100842c030940c0007091000e2001d08005032040114100c5019855030303008090000d90310010030816164100724480d04402403141c10492204807005103d2580300c06c0307850a06101928008070340b0301c29110704d50340b2454503d10742407040140019005d0044007990142294014008000240041c03003002d00303d1145600c00e0007186003508540760440c0c0070100810407160135000050105200d010322101004d1903110303807000350700d60069410000542d440101200d0402c00f090004025140e80400c1e00c05070040b0903501c07050207880c2b034209040c2c0c80c80303007100c0034014825003d00a02050b9008906030308a0f040c83d0384480907450002d842c1e128049110000e510005074a5900d020300360040346010542643d00c0c100209543c0311146802d0a440385640382e01500c820114142a00542000070080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 657565206 1250 657563956 657563983
    0x612090f0109080324010f0c060b0a09090506090721080903030a0c050f0c010807030f111204051002030c1912060905010f06020625050c010e1f050402010f08070207051c05 75
    0x381d0317894a6900082803103200c101e1f42410000ca045c028814400994041d520145010b004410200e40b0b07050800003030700003160200c400f84039080c002041d090000c118802070710070000c0807880e071007140301c0c1041d400030660900b501e0300c601c100b0407440700ea0f8040000b0718802249480b10b010800755420400e08054000c0078004c4e054103e4a90028160b80c0700400d07541c4020a41000144185156220b10007031008001036540d0b5940011085c41080c4481000c034429403082d802c588400b000a01d030801a40402d4902c0c90301c52209000700d4035843d01c000301c2141450500e2919135521101c800d450300940e005a4000150341d552403005016044c21131090704054441400148050f0901205580042c92210355000b0103a00484200008038810402c03514840088402441002c142c0c45540e51194040c4081600c240f8005482200c440c42c0c6000d01c51146030142c50707420b10301080d40e0059525000007040c200860140c4c1c00c020440da0b85030500c2030034078081c210200540181c1c9150052400070245580c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 657566456 1250 657565206 657565261
    0xf010905040b06130612140607020a050309270f04060c050c07090908281206050915040216080309150603121303230c0f0612090f01090803 61
    0x44040303022000c200d500b1501c1543c011802c24011007540d40180281e41080f0340f03150f080074030581071185040002561f1604101601c0c84d54641802c10b99580d42044001080398205000c90080c520300610104225003800c00700d0f0341000811401120342d28021280c003501d41011030700f80014403100740314a444400035800c240d481e08001d45441660340340f8901c900101c00d502c80c070044040100c80c41c140c4e0420115428011080711a03140712064040100300403000080e5800031400042c2d4080c0220011500042e0200c03516032030340f03051100d00c4024060f0350703608140c0811441807860b0b459404504480e0003010040d481e808c156140e1420326403541d900003460251141803000d80d60b00440d229403030320b40059841e82c2d950402402c0791b086104540c03010b00240c500784400303010b400181144d400c0c40c100000540c0c1040c9204410440303500c59101c0001d4003c5400d029840d6805800e450840d0400c03200030886640704640800c160035580d2101d030803150302c2404424400409030000340c0c05a20034070102cac203 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 657567706 1250 657566456 657566461
    0xf020c101104260a050109080301090b01050403080703051e22091104210c0608180115050103092103090209220602180307060509011701081c170a050f010905 69
    0x1003107051025010200803030311002c00001e00f00c01d4204100310740c030b43d0702070024030454180342003040c1240c00900ca2280001d0500780940796561141c001c131415264004c1e9a1130401d18192411101600301c81c1a402c40f000f1907801e91013902d60300d41c001d0a1040105110880302d42c280034800058a5281e500034114903091440c1c503009425804203450644800c0c01d10005172000902e8150002c2400304000741c24100103040c08144940e01038040d910400c144025400005140c0c04c0361801c07554900404401c0c1c442d1644240000c0d807081d084a84003a02036142c10080c000c1001c1504210070b84650403801103913031180984e0031401c1250314254000140c500c031404603401c68024420448415000a0030355500041420300380700d9250107600e03180c80240444180c0d64554401808552203c0006c1d40401c1d03541403000fa41c10356595020f810b036424840039012481400982e0601b0316107d400c1e0105100d0094510040203601700c60040c0301c0d511070388010419040401c0c00c400e00c40c2041c0c1025804a050004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 657568956 1250 657567706 657567719
    0x71a240405011a0708130e062b0b070c02060d0f0606170f060406030b10090e0a020a051c0b2a0405090403120204091e0509060609040f03030f020c101104 67
    0x214500c0501001c903c554800c045d1404d880c8078811580391903848030842c01d002c901d020481c0310191040405940b0544010100448049480c00211040c0400c8101e42041c1e03000500d4421040d41001c2581400700d1110125400500c4541100400b403e0b11559201d04a10340101070003541e00525090505004034110180186820314001300b00850900e140004030307081f0784950b8452001035070081ca2440d02401d000400340c24486141c0b2490342c0550030720f00401c0000c2000306041030740d190300412000700f01d0b29202c28013030301c179840d14860300c1c84076910800440805c1071510b003180300300c06100143c101a410010788500b02c503c0016424111b540902c800e00c1243c90f111a00e641164160521800100480743e014000c0e1146810484543e400c2c003400010495031041482401011f100041c0110b80d604065a1b5490358203c69013070f0b100024201090103d0f0002b0803041c1c00790f00915002c6000401740081d50180d03444008104080e9110b02c9043c07035115494070500b501d801d8000400c40c41c0c54600795 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 657570206 1250 657568956 657568979
    0x60512070e0d02040207050a0228090e01090c06210c0503010905060307050a06200303060108280504030c050d0e0102061504020c12091801030503030a02071a24040501 73
    0x14034050501c015850422401e550310154a000164010429035036084c1c2ca180540e15031101420482c000c18012903003c605c1c10003040d64503ca0390841440040185c80c2006032030191043e0b0390361401c0d556803040d00c0700210390602c01c541c000e020b00761a0000b206071860030b0a402c580c02880d66035082440c207203100620a80c488100c0e41102c1d640c0304041401d80701c0c0030001c3d00303161700380c2d01c815806450f40e680041c039250000c07400d070f580218100729124500f6580140c90f480748411122140007400c000005000c205c1c00c552703031440040301210710a503600b12200c0728034202c03030082d603095010440468002003082000c1001480c010058a00701d08010390810001c0e507501c202030031050030080c00003c24002511554155007044040404880d140801128000501d80c04164018007400050401c1d06038442844011070480e5840001540f4550b80d00b81584000e402c0401e04840a98040c1650040546e401030594041d0351010504400703051145900b010034800303141c40a01542c04c000040040b00041c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 657571456 1250 657570206 657570211
    0x60e070626010303030e030d05011e080102091c0305040305010c0504050f041503150f060906060f02070f121718030f0a0b181606031e05060607020d0201050f070f0c060512 75
    0x45c02d012911400c1c44003003508500854607402811494540006950b49005480c014001e546c2c0410b5050f050b00c4000c118283c0c421004d009400a03041a02c03100024807852010271001d0080c0b0b000d60419459903030b0316007560544c1d03003850002030340840d040c440f03440e02e10f481c400140400c4404004005510055401c404000e101c0a00300c0c2000070f210280109030364009454603020002c00300042e941303d40c1d0400c0203004a0013003400080742903071081030060000801a00340d4070842c0014503005e1410300445042041070760215071302e0912604804d40d402e0084d0107800c10360310081c10040303030281100c10325251400c1c410400700c083d0711143c03000d0089680106104c0c0c100d55000b80010744a810861030300e1805604d51700020284540d058002201795060f445030401d500e0143c8485141c520b8201c000f029100c064404d540d02400800142006103416801058031500c103044c6681400382c94084841103400040055620802c1300c0070500803c841a84040003a00007402d2250906992001c1c044034103200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 657572706 1250 657571456 657571463
    0xd050d0806040b0d210801030b13020f310605010e0f0a150809010507020309060f0a0c150608070e0f0f0703090b040305040303031505030318010309060e0706260103 72
    0xa4020407015152a0000c0c407070300c840580390550701c0300b00f441d1201c680804503500c4120f0801c00051610303003074445d2010038102c0350065031100035501c8412004404162598080fa4006030728091015140c1ba48190844c1d0100b140310707184198401401d804500e000030080c111045441c0000c10b01203a81c0002c448883c110f019208624200e0040000c01c12554150308107021000304031119107891640228060300c1410303400005c0c415900c807150280e0740e80c050305007041c4d8441000c0c003070038200c1a0504081c16100c181450244421182034031402d821500030500e1130311964030344100348241c1501308214030051103070500d0903081d4941440085990740000e0034907448120300d030001c100340c24440d0b04480841500402d92031450f007058034020301030350b00500c41200400e06052229003052404818002205d0780600030318500101003241c90311940c40100c01a06042da075600c07250114025106000300061100001d085007818041d000c0c1c110350644201000141d1410340900d90054900c10f51070440c2d03403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 657573956 1250 657572706 657572717
    0x50d030f02040906030b061e01091505070615050a0f030b070804142407030504150e101e0b0a06122c0c010807020a05030403120306032306060d050d 65
    0x580140c00030748581d5110400c8582880c101009100062808601410048641e412a01c0c03e00744d21342c0e05015aa001180401e01d240810460807815140404400c212450aa458845203549108c00c03686000e14640b26050241014803003820604403250183c100c030f104034100c1519681e90302c0c551850042601c07082107100c0011804103c0f98084038540d81c0c2201050b2b5441c004030002c81480e024605c400c41402000b80340105203403d01034494540110340191041558002001030703500601484189500716211f00701d0041000c10b580c0c42024101e01348542c0030744540b030030f009100c010780300000517080c4140b00401c1d0400220b5000044102d1aa0a1210102b2480c403071250b101c0c10f6510142c1404004520187c0581c1c4210000c140d40000310360980f240e24241d00c4400c0200d0f40c2d0840d511009000794820002440494820480d1410b1100c89140101d45c2e50703143d51740c00f00d07941807940702c841500900d61115070220800380000e5901c80c2c0b0070b61306007800080c940c071095610080300c1d110005004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 657575206 1250 657573956 657573971
    0x20901030207140d3e1011030f0a06060203070609080d02070b1009180318150207030309060311070f1b0f09050108030c1e1011030a05090a050d03 64
    0xd000c0e030142c1e020581c00c2190031681c100320001d1541c55044804801c0001481e42080d1001d9002c8140501000b180048800c24001003401240a0403030350154020a80e220f03c1007071160a1901d0700400992101d41c12042e610b0741802003080c3e504034006040c40c031289062500034400d40e40e0020a0f50000c40d009070003c624440a4102500345e44a880e41c04a0414000201d0340103116404501c213014003440405604021769403000301702110a04218800d8002688130001c0c0071a01c21014041c0e9a03a0113540000c443d944c07111000f8106040c41b2043d0096000903000300245600100840000c01440c2000e0250b050103908801851042d08030041080403900e00e10401d010101010340500ca4004000404644c0c4a141d41c01c0654628400c20011600303080000c1403100010003036402e6404001c00030000a034100225180000340d00b90002d442d44105040004e4040903805000c0510400f62000ca03500d04008001c40700341c41004081c9840b503400b0420384400070b080000d02c0c0204092a1034002140e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 657576456 1250 657575206 657575209
    0x609072405040306060b0c0c03060403020318040b060729040c05151207020102040f08150103020d020102120f031e090a20150a020c09041a0403030e06070903050606041109040209 78
    0x2401030380c00240c1510703e420004581086e218004202c0d029004040700e548171081020199249000c403070080040c0c01c00e01090840c001c550035031032000078005101248100a45020504d1038100860542d07a008c5c1c42c001c0710080c036500000140c1c0a00902c5040e014900e050744403801c19192601c0b134980100307078001c0e050b5071600c40c1c4401d41d15642c050314030802c45410800c0009010f90098012840030002801c000038640320006000d45448a642a29a229a10315003c211464034043c01c03c0e81540103900450b0b001082190080454010181c1480d449007422015401120244500510140384010901c0014200000d0700b5041d0356000d090654404044600d01c446420b91907141074000001002c01064480c0c3c480180c2001700d55a07088038030108002040047c0078a05541c00b074a16069409401780b0405207181c0564001c1c041c0c10f01003046810070310842c2c500b81d011107100f800038000355828420010305001d45c1c1e4001800300d034203002e403020b05240d140c40e901c40c00c210144259800030b50740e88070307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 657577706 1250 657576456 657576467
    0x150405060304140d1808010606020a06020c010e030301090f05060f090a0504020f100507150b1f02010213080a02030f0133030501050c0a081e06010302180402030a0603030206090724 79
    0xb0302500030940e1380baa40100d8020305940c80303640c040154100401008140000d05114840464525900800b40150a510303007000079031100d180700380035548941105020400400086008200440c0300080884503d50310b60212035000c0d143c544640d100395000c0c00346a8403803e0440c0c02404034140020b10381c4451000039009400d80c001c15410051440034107403640c0d0020041c0c001d10b0700a6004040c44042c0001038070840300c40198599001d41e00f0350070b119008103a4503840c0300d411980c0c00018a0400c3c0d4681c8112084502c1e44115071540c0003022001c21406c0502c515100342182e6070080c01072002d5104074414178450700510060300140c014a9035840030540603010015600100200601e0411420242255116080c4080410625804900d40910120070f0005400e07950700d10241c1900c5900c0110065030020007510080054603501d00a9030303a6500c001d50150700c107614001107040c13071441e0103420105c00a004003882e8000903400c00c228407040410301c00e15004000c20406420028909656 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 657578956 1250 657577706 657577733
    0xb0d060503060c0903060a090f140705060301030f031206051c0204020d05070c0308090c10141c021e0c03090d081201030f11102304080a0b070905150405060304 70
    0x741449100103014403c40c05000408510100354140c41107543c0e1050440c041c1e40760540c000340070100308502ea801040701445440c0c80100b0a900340d6040907982d0000403000e80007070700261003420020460008150f00303b01c40c2c0c600f900c00c909060010360301d0071001640314008902c80040c4805480081c004554031641143c0700d020101804210074205410003c2c940601e080040740400e031240301003201c1071000101e846007080d004002502d0141d00d201c00b00d504c900e41c0148000c449000b44441c2e90160148030228240d45940307100103850345442c5a50141d8a01e0350f0003010000c98041021412000c80482119445802500c01d440c5514070740c17410813500c0c0305142141c07010000032000401046030484034401d8480c0144520100d054004082107854400c00c0300d0301020a05c1001e5103000c1280001d04e05e007200301d600042a0400e039032000050b040800c00036044480b80302c0305d030402480075000049540607220540d0100000c82500c22041c51611032400703418400e60010001030100a240c08032240c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 657580206 1250 657578956 657578959
    0xf120d02040308032a070f0809040603050609340509060a0b1303020301200d05040c080d0e03060c0c1510030f080703080c0a0918200307030b030d090b0d0605 69
    0x5a40c0d203000103069400042009414804201707260b0f89592028001040c5c4d5801900702c100406444d94950b00e0b003002d45d100100c529045520f440300040400c005102d035520030b19130f00f0090110881800e18942001c9075a4401011844005034138919000039000f0ba581962800d444007080c1d51030709000122410703403e80c44080d2010b0009105010307542581741100403a8401e42c000e00c20010091161b50340100b0700d65062609640070b100c48449001e00e0342080781c0240c0208030024549440380641820005003421346001301c1c1003070924401906042005a03440b1464054071400c2c07030050300c0c0360394891910003510f61030241f2102c04100c01d200462018001107900208074062203411b440d24103081e80120034142d001c0f822610004102c00b60503411034020a10740d80e030321310b00581807400c1000c03501e0102e02580c60441e550252104801e504000f01c1c04106204030035203440785454180141501d0407141e80074002d40280382c01c00c030000d4001520310250381d5100380054407061503007842da008000691085 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 657581456 1250 657580206 657580223
    0xe1017180f0703140a021c15020a0c0209060907020d0f0e0607031d0a0509130302010b104a01031b090906081209090705071b090e0f120d020403 63
    0x90007203040010303a0900701d030b102c0c0e1968080086540d6001e03031a140c200d8000781d000711641c2e003001191008015000e5010b441800705034003032500003194030100d8115440741404201c1c1d0503d806c00354500650360300e510001c100d9003180320f1b00d44000300940340c0405600c4a000c4c07010444010880034003031140d1060361a0b02404482d122025401c0c010824203038030300100444600550a8241410a00300030400e4420203801d01c0d20307640342e00107100e603190480d803801d81c2155600e21a40e05281d490002038102c03a600c41e501c051000364070410080780644115424064454007907040307110300c0e00b09980c04404500d80310089403079000560068001d4541103255403021030000412204858004141c2c20a44041c18410018261154211a6240e01e26000100d0780b0405104120081c5041e14002c0e03484101072034000d08080351541c4029007120003c0710502c403035000d09814444200d4034440c00c54820780350b000400c034240301c8050043c5c4502400100783d181a800051a920107074060301110001c580c000303847c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 657582706 1250 657581456 657581473
    0xa1d060c0d0207020a080319112b050915030a0b010f080f04022101150f0305060c090d05240a020a0f0f0201060810020c01060602010501181a061602010e101718 70
    0x40d1034a00046221000c509c0d04040c50100c20307800104614486184141290088252090500c0c40d102c114098410081c2c1004580d200ba02c44803540400700c50a942e0203516800d1560304103059419402030241080102c5920080c02540103500f2074000300d403a890031449843d24004604494020252002c60f04880048602d6000055005404003080010f10b1145991078083c003005441e003901c8080c1207584a480424910500440244041d0700300038402c08206505580301401c0c02a10a80b549500c100b20f1200031304621001c1801c0e03407007941c9100840c60076540303c4010b0710704a04500c5940c100105410b061071014000d500c144042c003000c800300c030781114600c00300704084c0d4810342282c081355007004800510103005005060507100301d06800b0107010450a8000d00421840040c110340040400100c02e00740ca6a000901454103a6140b0700d20700100c60001510103508846e03003602411207084501942540541040a0b42d0103020040025846a031000e0031b58241013000240c80b0b0061550 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 657583956 1250 657582706 657582727
    0xb09130c17071203020d020610120305160f080c100b090411030109150903120504050c060304050327040b0a0b040909050304080706050901180f1205010906050a1d060c0d0207020a0803 80
    0x1107046c40711410340d003140d1603569150b8441010942e18442c0a500c90303041031180001a0181c0c4c090004000c0e0000742040301d03440ea0b00c4121501c5442e08069404000000d0f03000b01414040c0400340c6034a816110a201e140c1003000401c00082000b000500510070700000d003921a50203401c00d800701c44e0090f000c44c0b1262414031540c8001c1c024085d0480200c1d0f003a40c1100740c0b0344880d0241920464100c00605214107074141804095800100200c80f45e0000308071101c00713036542304d40100301c0030782d600d114007a41500320003840129441c03c210f0520404038008100311a41746c0400b11025969480400f0a0b8802a072a009256014603040001140580000450040d03403141c068600d11209a035030364441c015810300e020041a1602841c050000c0c603071000e1017100c107200c01c8280018410400043c540c1c034562196801c64000752110400c45440310340103100004100d8100d80d011801401510582c00d02050116082c86410442d2069540103d0345105556030404004001c0c42204183c0350380741d10400 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 657585206 1250 657583956 657583963
    0x609081b0c100c0507150305010f1d0103060c140d0f0b0a1202010c0218070801050f0315060f0f09011806360e0708010b09130c1707120302 61
    0x300044085a00002010100400000c6030440daa5014040350071450701c612080b00e001003155000e950358451860006207202c0c5a0050480c1e0040690740060f40f5410030300c07800e4040d8115030000f12002c110940304c0b0018454054a2811a94000c20008140c60610700549680d00000000d541c02e041c0811744200f40c0103903130408002400c08810800c040c3c2c207150100249142c0c94001e880d80c1d000d0300c0c14034a0045d40181540a01580024031810016001100c1406920300440e14100042c5400c1c004020358241310740b40c01e0001c001200500445040190b4031800344000901e51842001030362006086911072000e40c1d4950342019021403a6580c640807010344081a071800c2801e414a4464001042145100b000301000f03520350f8103240e07101207030889000800036510790120542e0b81e140342c507000400c10801c0300000e21a45001081c0100e001007000004403000300704900a845114010000902c503440c6071090701d110500341003c032040f18000070314060301e82e0840110300402c042c2500078180c001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 657586456 1250 657585206 657585217
    0x31e01050405070504020f0706020307050d020d0e16060512040f06050103050607260612070e090d080a06060c030f170a1d07140f041806060e01080106080a0b040201030207060908 78
    0x9800303d65107181d449050000b01e20554a44030079211083c841100080c1c4240c00458003c07030303e0b140a504207a401440c0c00b0881c1d0007010702001541c3c0c0c41392020990b80045c0040114400861a400c010a150a6000c0c010788110003400400d81d903000005010032155540f9650140c1c0c008508000035a12440c01d5907503a6000d45005002c0f6a0306041c150114040200303d5000c5034880350a03180d00d40360a41804644040031401c21080c7c007442c9400309070038000c07180c043c3c840e42d8a4002040d03100b00000d80a402c2204c00b0b0880d4040601b89802449803d070802c401e61b9225a1610300040c002c0d6174040100c030304201c3d41440350070b20040c1034240700b404202600322114040c1200322904000403400081c50380d600b903d01c502c0344181a003900d85e018902c0c024119001c0d0b4a8080c0c008a00582031079145070704205c4411044841690307034003003405441c240d0700041d0f0141001c0d40081140c903041000b09a6502d0030740c0b60003000700c191a000541164807e8040e140c1081d40801d080c00201814601000c15070000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 657587706 1250 657586456 657586463
    0x1a0f07050309030f03180f120604080307030f0605030a0b131209090e0a020109091d070b0307081305070e07050c0105181209010c060902060408031305190b18031e010504 74
    0x140152454540c00200031100a52511b09002c00059224401d02c4240d000c82244160b200c1c01c923008181c4424801d001c4288114480c2c0340403075807803a000030302070100d40f051382c3c1e4121036514007038050081d40c400041902099030040290a8107a03103000540c400c01ca0700810090078052071100c580c44640c2c003c8211801d840480f101400701804034241c3e165504a910b5010340011a81c8401b00408010380d440b82c0c00b205c45240c910300c0321001e10301c506440c00303a0551140549003400020031041942c46482142c02c8010702c41804244081c50300c4032541c40c03e8900070580f003404404086900c6038002c4003140e45005081e0000e101070324003800d01080746540c1d0051900e160140d017550350400700c0da4404440d1101d130140c5070481a01402e45415005017010441207030003030f00c10000401d081e1300420141c2181c03100c0120302001d450414003480782e44800304140c050011503050041c0464240001030760007a9214140c07100c0740e0721a40c000a4901000d90581d1207540109880d40600c1c42070641205110b00e02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 657588956 1250 657587706 657587713
    0x1050a061103090d03030e0f0a0b09011806050a0b10110715020a0f0501060504180c051c030815060c0703060b0d0c060f0e1c0506060306040b011a0f0705030903 70
    0x20340300c00560384004504003050041e0402c1000840074a460203510400307502900d40081e00700724400269140601c207409203d00b50f40103071100c00c1000750080459034460f0704400217028185150b024407901d44041a40148202e88450000365a80d036143c1c480a0341d000e0082881c1101c2ca00010301400c01401c51501c000d0900540002054820080c042841d0703045941e401440b01c29140d484003c60f11101d48400c940954071680002125038603400b0350641c041004800d01c1084000746041c0c51480301390780c040c9020310804030310349110400d241403105165415091203030b5980c0c0c618601403240000f0400d5644d1048010030224518440002c40d101a64444c880400282c0c0c0680d003040700c004059400184101c0b8940d40034082c0510601ea504010a041d09101c018940caa10000300415070045000180d00e0360144c50b00103100080150a4000e1810f070081d04044c28642c90300070206005018000e104c10076100e4203001006918200c0d1042910342d44c3c01500e81e1424581a078487e4003280c08503100e4030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 657590206 1250 657588956 657588959
    0x20d0f062d05040b070c02040e0105010b19210b06070210020d0201060602300c070b070308010e150f0307030b0901090b0106083102030f28020d021509120601050a 71
    0x41042c8100c90082e6004050f1034040e540725042218005840c88080360417644550507040c0c44072007409114060320401c00919211244402501402da0303174041d40b1810092203546028035541c01850107107901d55500c0e004500c04004502242035441070030802074205948004a40301d155010615040c407400300ea0007070010555400d000c81c3c0d12042c8220164500c0c045205040e078164070400391600740c41c5204041c1d0f080c501d20444a40c00c05031550302055100c00c00080071000c055105c1c112601605070800c1c600400c5c1440300b6501014005c005034140141820315038015695010015103006641c01030700f075215442c20b000c03244d002e003000b0941181c4448180e800031a556005141c5688a100c520b807851680c100700341c0c07075005000254a80c1002c1e0b4682e1146460250700c00b4010403e154650800400386c044e840d80715100624001403030070840c3e4014080d1440141d40b0044841c120540450f140d54040d0b003014007400131449a0908582e11004802c1c1501c907040000c00c01504a42d02191509901c6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 657591456 1250 657590206 657590291
    0x11130311040b0a090209010c12050703020607050418090c120303060905090c0102060408070c0b07060c08070509153f0a0506061603020705100509041b0804020d0f06 72
    0xb00e11404005610580c00c0324240007a0643c2e40c0504190041450041d0030492240c94150305441e0703050905002403400914034060540402c000c0c1c0c3c2191061600c1c1d0b280500d001740c010b00d03100d031510308501c020ba259110102406424a81d4001400328001444008002491b024004201500c40c2e581b2050501000035550740c8007003080458600b041e0084c1201e960b950351041c00540c0140c5003200c1d200789410001c120901d461700a4062180700b410001004520040060402c000041c141c000300181048000b0007a114501600188240f6030722003521085035160b4900340c030101100340040300903681e80041d040d00403c24101c1c01c46000c007020090365100c0a9900307066410440303001da0045030400c002891160101c54082025010340706072150f6544841c0000d01640c0c20502c0400007500c0460124114900340c403e0f0820082260203031611000800406030801c500244043d104403050110a0140b0126010220007180e115030300b0040c0311001c40341e0f0b40804458200300c80c1c40c40e02407021b2540ba0b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 657592706 1250 657591456 657591461
    0x180b16051501030308040f0501060b270301090804171e160602061b0c012307020c1c0605071803030c0b060111121c29011706060a031113031104 63
    0x41c3c0b905669071804036a203681342c0c0305a401c185401110700b90b44e035403400207509101c00044e0680c14100c040c520507103811140c040c2da040e503080d489244640d2429504000064011080b50221100d015648424000092500b0f06000070207000c041c0307103c01c1100071840c40c440411a0341c680001084041850340c0c81d01000c0340d07113560841341d90b16000300745004800004c000340040d2502c46043c5001140c22601c4002c121024070f10301d6005140360020009011009805000d507440e1924240c0b103070300c00c281220250740c0e0142e500340c001420680d80e400202e0035091080603074210b080811401c1c1c071303142603032071030004c182010303c810540300b2a11040118000d988103500d15040da42c003160083c5400820400d00c181a13500203050340100c0d405501003c0161915809000000101543e000c1e00160120f8125202c80300008009810001103460503450f641150200d1a00900d0507a803003500d82210131402d070020304201c6a001c044d1100031800b84180d41c0c0440003a800d50b441100d000a4209448080c03000303 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 657593956 1250 657592706 657592709
    0xe0a0620090f0619030b0a06030207030c0206090d0b040302030a0216060c061104050a080106050406090b06161e080a030b120a0618024c180b16051501 66
    0xd10034040241d03440d1441d00380400320388094000c0ca068901400300c842c240c84d41180800c00d8004c00d840301091890b600d07259005400400d40ba00f415480d00c0096507004020b40d90100c0000c0c418000400c010304561201c1201d1001304e548a03081030068140f5040281d5290000002c0c04010320481103200304906089035103000300c9410785c482c81081b024076078400e80079014202c02c0700c040e007905000006640c0c2d03501c0220310003820100c000003892400d2400303003c29a03919400ca119014141441e881c09502e402040752089100c600c0c40244000151410182101c068640d1a02017140e49003134001b4031500e5070007003000d8900d644042140602d100c4c103100800c0030211100d082500001000e0020079216000500800e40c406000412541030354000b80031450f0346403009401c0682c031141254810b044000000c0c07203008043e07001641ca48413501d0004203198040911081180052081e510003040341910b4000e043c0514996488180b0f1034810301c0c15208030702c0140c803244501140100e820900180b603e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 657595206 1250 657593956 657594011
    0x3020f16060c060e0c0a0f0503060a02070b04080a0e0409030801060219080d0c05130b04030302100504080406050d0f0c021606170c0901090b07050106180509070519090e0a06 76
    0x4207003030701c41d01e44000800342c000c0084c895003c0c200300045d1a42c0d8060000000c0e20755120001d40c51030800c404e041c50940f00074041500343e8410010203020a9080c22490351050340880780325598000340b00100c4020311a041c1094200c0e0500150204250b04082c3d0141a00d40c603500f161481101100084508000200c0c00f81c4410000c21440c01d400140c0e8000215080c5107090840c60321120074281040300b04070390b01a07148400081800d000700750f0b0501442c40c40c144005014000c1e82000d464180c01380c80340348076110a12000065400541c00c3e02d030005526821414020040c030404c16401030340b14007262000703001c00303c503003040480c0d50390080051a14131150442d114106a48164201035903500c200d2450b414082d10710320001e0464048030003040040d204000114240b4070701410f07803031100b101d0214400c2942c28903007000110540000c7c61021240100c4450104d070b4a140041264030009800000350303503003071003a5207219420000b038070a0381c81c2c4154010040b080709030b00380c003040000034038118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 657596456 1250 657595206 657595217
    0x212040311071707080c01020d0e0f0a0b0c0d0201051f051002120403080a020601050f060316030b131e020903061501170f0405010f05010602030d050a0e010903020f1606 74
    0x16010030300c00c5820310110100281101e10542d100c2c2e41d03070390864035200b9400350f03140c4c00203105001381c0307105101c80c010404081c001000c40102c5a84043c1c90749948000003070058210380354813100e6a407120801c800610480310465a20000c120055072500f41d01c0200c44055804c08010451141610205607070742c90740500458101c5d820f11040006641a0f01244011407041c6d003241c0444034111801400114840c1e01c040347e031001c0412020303040402c1640310600c610106111400300307844407412640e01110064481480c1a41001b00342c00816403c0d1290f50465008124100040c19a900030500c03d00c90300e91b040503a0303a1401c500026845000c20581e055000403000c43d00b00c4500329403480385140c0c1410004803001902c0043c00e582c9030211080f04000100000b40401c2c04400c0c030a2020750b070a85201800b40e13604148020356a031013800c0344012150740d1600000d900c40c1d450b61281c115010440001d12001d841030400a507a8a000f0214480a0003820188625614100d824000300c40b51510754 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 657597706 1250 657596456 657596461
    0x3070f0f05040b2103130b030c04030803060a0305030417150c1b0a050d0f0e010f0504120c0803040e010320100c1103010c0203030718051f020703060f0911040212 71
    0x600c800341001c2c88a6540004010100d04c00048a01103015030b140d80b0380009640b140d948414801500c0c01540c0300380301d445c1d0204103020f403078010002100c040c0c07504075100c00d60f80d403a041c0c081a00286150702c090001c0c080882c01140c0803203400303a5222890300210481e07200a4114505045114058402038680d9104000384125002c25230303120b080004c0c1c03c1096818a40440d140d050802a1541d5003000258202c2e61404d152500301c0c0400302c04d20421300e41841003204d2011301401d144128020030600701030001942e01000600c0325844085c0c4209410303282c50b2542e420140324098400c2c0070840b502d0f4608031105280e40404124500c00356001402d40384c05051040081c1d6481a03c0d4000341d445100d0071000c06000d80b824007444070314848540c01940c0c0c910340b403280100140d54451044c0d441c240a214100040d41c0d40821441c0510512000496030420704402079140061030f6000400c11030918040b9404400998000341d00c0ca030141020321030300c440610403c400c9204074a0342035070350081c4201 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 657598956 1250 657597706 657597709
    0x70503070603050702101506030608190b13080f03220f0f060f1802030f031201210b0108010c0210020c06180106090e0303041b0b030f0903040e070c0203070f0f05 71
    0x303801003480e005558206c1042004c0c601507491219611401c982c920900f000101d615210b03810040080c18082c0c0b02c07058881c000c1da0500344000c1009082050a0f801140e82e607c02005034052095000d44001c3c1d440700f080e10100100e4200b103802c0c01001e007200e40607007c0340d2450715170803a51a511651b59014074903d592120070702d2960344002c0e01c220381e40b000d041c1c1d140880c034880c004c0c905841d8101c04038440840d2041500e055812180d40d1400d40081c0000c48100c4054540e490548001d0018000e0f0054003d00c6542070440c3c8500181007550080b000040c4103030198412002c2c001c0325400c0c1d846651003090b50200743e10a000ca40c070600d230f01c1400000d5418034032000c9003070044140000031900bd40c1c1e0b200401c040d103d100c0702031400ca8000206000170001c1110307000419503070310900c0391299803500041084a001c0101910313030355a1004006403442a0074003c5402805080310001000d00389824002c0c034407040003c04030301902c54141c0c0030403241010851041100c2180c400c00c40000e041c41c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 657600206 1250 657598956 657598961
    0x3106050412030503130812040b0612030702060d09061b08070903030e0904050703050d1d030c0609011229010315180b040204030f260a02031206013b03070503070603 72
    0x2400a00c00380519030034617002804410003010b00740b1141e01c1c03422541c04c0506001c1d516010280c000c0d4410030030b0b45484030030840084280c9040540440d8429198100c40001001811540900911041c9481030247d21040d010481400c411556590103400e9661824141c0d44a41c03a40000f0300401e44202140041d454203002030340c1d0081c850400e44076460727543d076205403515101840003004240030f9443c407001011100710011983c40c00300c0c02024078920301000b1420510854541e20f04000b101d60303102e800f01003c1d030891112441402c0c0310400b6004101c03403031b041d0369152059a50029041040e21000c09110680582c1924914008078284240c81226a0000d040c44075040c0d170000d800340000000300d00410403040351f290142a10000c403601d070714144030b02c4460070b01a00d00082014401c4140003580001696111020b01e8050b08454660b40010b07034881d250440c03810080ca0b807040120291710030321103035641906404614200d10741188010035031990f03140e00442d60568040c5078104041807094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 657601456 1250 657600206 657600211
    0x1205070302091f0303050408210307080c0708030c0904051602060c13080601080d1b050601050607060603080d1a0a120803151c02011404030305090907053106050412030503 75
    0xc1100015580840c83c0400b41d80144d500980100d00040b50401405000740055079601d49802d5800b944091802604201400040c04601c20410f101000549120f4170724100c80003c2d030004c90464880c80c0c1200083e110364003041c401030140e8101404145a4801200c40e040301209036005021b40740d8400701ca9600f140c005055481281e02180c400041d4401c007440441c0c0038040380c0000c1c081ca0089044003426100b010034195040e008000c00c104041000420341c141074940484015603144200d0038180c000d00555000030300301c0e010004880b409803009501503640d41c0064040440c1101040042206200151154204400c140a0350a0000356941c0045034802e40d400c2080604e08114804107401803044691060a0003021500700155a0020741096505151100c0c8600d1b0504541d0300074418024005254010000800842c0c81140264140c902c0e01025056440720400101c0502c081865403e202a0100f08407600214a4502c02c0c401c440640301100b000c0140d10b191580c080300e659100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 657602706 1250 657601456 657601471
    0x4050c16020118140306090313061206090609140f2206090506010803040603110f0f070204060515040f0503010903050a0f020705030604030512070309120c080409020309030310120507030209 83
    0x501d11910402e1603d00c25000343c18600e6a201d0fa4911400602d443c00502900520207a070042c04449041500070000c501940e84500c0c082d00b62a404019044c0074080700d03040564000d0a045c1b000c14100c0c0a9481114002d80784070714500c5503100d102c0ad21069110503a0148110300000600d084200303005c4c0304031018580309001c0012411495141d641c20304000b80c12002c2260400101007114903818012803101985800b00c552504000c0e001005403407280320324071042c024020440b0810b541d6180d108500821000e448030048442d5030f511005581c3c40b0f406617a10502e61214080f8080c1014800c480c000c40d81619a00c0c42c190f0707118016140e00c0d205105007401c5101e100c0000c00d082e1414003c09000b24426122542c03a4183c09000c110314481c01070031001003505d0a4940e8001c40c40d820b00000b003524050405a00240207801c2110007071040d40c00901205000000f400181c401c000001d600c1569008500307042c6640b928440070b2402c01030840500143c1c01034009002502e02180d856411002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 657603956 1250 657602706 657602717
    0x103060509061c06111e120412050c010516030c08061c02130c0507120c02010f0810090e0714090114101b031805030c150d0b03150a0b04050c160201 65
    0x1281c0c1c2d1241645d21122880240907004035210700d20fa2100c0b0b1880400c0e428040da414102402c402c0c1c000c0000710000c1c40030307002c00101c80c2e200c10f20600800c00c0704c80c000301c09002440146014400c1c4844403807c130042c0c4000a1608614150240c402c2d140c0c40c1c040c0344000d0602d403000b0f90300c4140395807c128500003a0b07481030740e40a40346031202c0c561041000000694070382c1500c9081904055649c6042e00200c03070140b00420040400507a8000c002e00b00030203003030400007065240e583c000505480250400722216103448980d0355980d000042510464400c1c2c04140c429403002c4050106050081c420126117080c40d036680400c0785003040c10100041c0c02e9140c081040541c00c64000e0145014110584c0072440b0320303540d801401001000d0002a05094004143c10b20064001c1a6103543c0d00d00c42c20301c01507000c504401c407400380ba08800b552541c0141290008560701e61100032120307040d01d0149030716183c802d440c074503810030f401080d1145680c2c48aa40c1802c209000102d07003820f0303442d022810800d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 657605206 1250 657603956 657604009
    0x4060513053013050f04022107031a01020d030e0f07080c1003150b070201020a02100e0405010609050f1e0910150306230f04050a02091e030703170403060f0b040b010306050906 77
    0xc446c0303008c441742c4c18140c0f8244602d801c2143c4003170122803100f020000205401002c4c0e8541b44d80004010b4442c006605d17000030000c0f0242c1840e8146100c6200628007402510000240c0180000c1c034091a100116003035561191000710076402c81d000603c19080f01d4050540411840c110240075282090040c01580c007100c40c140e000070100803038120b400010445040a40e0b1481c202031013640d01411290030080c2d945428980010b44c810054071400f031080300144401004007101000482d840840904402218101389803410b440703004600600382101e090754480e40c403091090150f24111a1030031000c01d040000201020303065400042c00c039420407420403112815031a184900707841260130250068441485408004001403000791098200003c840c005d400c44e6400320700306048940c00000c80d46070f404034294480540c06650310141031a4a001c00311180b03032005410030030060303200301d031304200003d068001541110550700a2035004541c0e000007a07024100b140080000c050328a10680044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 657606456 1250 657605206 657605227
    0x303120608060106031b081506090d1a061918020a03020909010816081605060307120c080402040b090f07050a0c17090114070b04060513053013050f0402 67
    0x2c00e03804000042c1c2d4038040784061081c103d01c00003003101d861510070703514140399012054200000352582d00c5a10000b0714181c503503541c010503402e140d03806010034041c11071542580b808814100ca426000e1046410402940045060404140d6600f00c0544280b1422012050002d421290141d010b041c4d0801c5900c205550b0151464000e00e4024001c0c0400c10501c07040142c0e10045074000e4029900c11b084503030300a0047e421001c03c1d03420540341c1c0d42c0c91341d4800d541161910b040020400d030103442c0440e1400e503150b225000d10310603802960144003450700e403000c3c00480042201d40c09802c1c285240413501d00c83c40f0740c0061813142001d14180c0d034106440d44031002d208a4000400504241c002090b040b0395800404140b0240c6403500030343d081000a0700d41048416000300014520307940c8000007400f14641e41a00303400c140d0050100c0700120781120500544d00444008004010505246c5100040081e41225041058040051202362074001800341304169511700c1540304e6024807502481 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 657607706 1250 657606456 657606463
    0x408030a020918040f05100c02061801060b130e06060708030609040201090f0f1a09010909020904021b06150405070c0f0f1209090c0c17090f10020d18050a0303120608 73
    0x990017552240f52256861504a14151110088490342820710842081e541e8012030090703030001000200b08010080d0303e0f031660050a03690030504410502040b5944031f0400c3e070300c230102540d0050a205000d81c4940e81002554041ca5000412a40f000c00c00900c190521541954000d803040c1041000b107515501c00541010880e0001802400c006400700401400c0c0c14610a00c8500b85c8081403400000c08002013600540340510450550006004c0a641e20340c0c0c3c0c100c5910101c4a0000e00b06e03486402c200036200c0906581404881010240ca240d0518141c4242402400346441d008a200b035180d4481c2648a560502500c2452103403139005d000c6410600c11900a00c03069a4105180d400d2034039040c200e91003001d001007000160b10440c4002090b0100341d6280c40001c620094880f60f00d00c0002d81c0c403046403d1103a0700841c168843c41c10961300002c090102c070b00c15454114404010300100052084030b03124466000780d40d8541080407901500702484001612200071407542d44441c5c1291a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 657608956 1250 657607706 657607711
    0x5090f0726011502190206040e04240e01050a140a0b010309080d020a0f0f0c080309030c010603030809070501080907090b061303030206011526070e040e15010e0408030a020918 77
    0x141450700c00b1031044020380c18000840b042401e01d05200c0d42044c00d0f00401c80234000e901806d40c40d1a0080f010030284900040751051580108880481d4200442c074003801400141414904039820100802c0b4aa511400f403420300360781000c46e1203061707505e01e001d40024001c000c40710b5040c15a201e96036070120b00342e24000c158a0314404409a901d05201c44000c10091840c59100e003040417102144840c0c42c3c0c0100510762240d0003012072500d94a554441c0340c00c41c8280d0080341420b41c40c00800108040d0000c07105ea10440607041603d940d55982c0c00103440000741155014090b4001000038401c200b0a9442481e05000290035541000c01c1803103841c1043e41030360003e40159100784010084d41d10745030a10705070540d80e8075082e03080d6194419a06414804000c500c0c12246c4040300151290f13110b50344c205204800100240144000f82880585a08101040c5088002d2120011030080c034100701c020b01035640a0349052440c0d490104c40c2d802034000744443c40d408400c40051150008007000c8150 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 657610206 1250 657608956 657608969
    0xc090e0c09071121042c421f0801050d170a180b03040b071d010c1407032609010f0806040f020a050a121a0904300905090f072601 57
    0x46819401b040d9004144010a40c04800c6da4500c180700c01d5030050b0001c036a1404c040d100c9404144000b070244e4110a5401d510243c0003510034141040341080d0000c42c0a0064041e120b0625036601c40051008051543c41d0251050000040340c1c500c080309000107145030000d500d010441c00c000300303204010442c400d910000d9110004005d000900503980300c040d4000d41e00d4240f0429803500385641d888190341904020341404072400b8108107000c899034480540c000c41d60b0a550b48242c81c0d1038818090402c1e240c0b10000d80c881c242184106039044030488107c0f030720503150109604501c40703044500b4040202501d400685030b1000441c0d0b00201e00151641080d0f0380c4070030361214420000249500314085d014000141400f09a021042050030700b102c00303c90540c0c21004503a03d17130920000600032200c0781131541100c810259855004046040200000359036070f4907180d5a55401c001410106454181c1101a0308020942d00c6006410241d80c4504400b80c0da0060300342e4449030040c80f80c09a2010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 657611456 1250 657610206 657610259
    0x604150b010309030e060901031b0c0c1403060c0a050d060e2d1801091a060a08030f250c0806180106030503160c090e0c0907112104 58
    0x18020a986009021031290207280c01c010054864800030700040c4040c50481c01100001080710341a4403e411420201d9402e07908600c0380074030404001c0c1821400c0c1e000307560400007008003259400000285481c0900c004000700a40c1d250b501c413044250f84282c0510741030040c20000310443d448240a004000d10710004842c540b480c01c1c0420003404070480103401780051144180500115210004940000f00c1d9071f60980d5003e000309281d4010828203801500341c07114100202d0140702c94083d824800c21060b500300810342d0351a1105c1d41c0c1d900032010100c200303074418412904059030200f5541600c9011540c540c95018007521482404d0f6032030340014840e0381015081220300314141ca040d0340701403001d03002080220f145445164803402007003000c0e000c0017203109848060003840e916560107000107401c1040300001614101e5a0350055002c1c0c5400380301c9100c000350403240500042040c5940c450058140040d1034644002c50461140320a10030482c02d000100d103c154540d807040001d40c250004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 657612706 1250 657611456 657611483
    0x11071e12091d13060b030c040e07080c0303030f010522020a11010c0518041d0f07080d0806090412030617030310050906030304030b1015031d1c120e0604 67
    0x442c1070080c0c00e4400c001e1094400d102804011412980d207072a04a1000101da10614002034140030000303034401c0e401400c00030a014035441c080303040f0045840340b00031540403580e071074141030700c030b0201b1641080380f0100e0000400c51030408501d4085413000300c400404105d0b0005501c081203810202840b4005007100241050401007440754822031513032030501a0030a02440500d0810300320340c4909a01664840c440e4050200807403000120b0f1000300b20540da07501010800321030b6945064891070310301e403003071000c881079a070b0040320502d0144c000585240817942e1552503031400c00b0131040441080655800001410808003141c0416072510040510765034202404a1007840c441500070f00d20176030200060010310759000040b83c003240d0313101f80003030203035039960310680c54201044d031001c1c84c809907110b0084200e0780d055104104c004030117000407a06050b08440b070b9035500c0000505902000c2d4460795642000c1c060660114903100300b070740c08520301c007200702c800d4102501550225800c1595004 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 657613956 1250 657612706 657612719
    0x40302060129090a0f061101060b13030303050615031e0c0a050a0c0501020408030f0417060c04050f030c10020616021c1b020a0609090e0111071e1209 66
    0x12003801800e4a252a40003480c0954856101080702c81005a41e50030000307803184076494402072180204002d038141842c082d07803144060980300504c0c00c088015440d2100100b00d8101c07a005461010b11055005000342d411550117400a102c080c1001d40d20014a2901090300e200c110001c51040080e00e91044042d10094405501004c004d490201441ea05100c03000c070385580402900c6445006d031903c00c12881c0141422030083c03243d50402200c5000010301d6907402c0044030f000344121040c0300c5a0010f45d06407030413410780304d45050754a40500c070f20810042100f482d00304054011003030010250307403d507003105000420b00d203031100d010750140c3c05c010104040200684400c080c08030741800030b130040c042c021102c000b120f03c1c129903440510240310605800b01e50a10b6800030390680c050040b800c282e89941c0068181200340c4144c54091342016001280f0700b00602403034014510110551b81070011554985085507090521140c202d8200700c0001c0c041000032034011440e41300d036194001c3d407901f400f2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 657615206 1250 657613956 657613963
    0x50129040e12030411130c03140106030c140912031204030e01171b07060e0f0111070519060e0a1101030b0906100c0312061d0115050d0e100e0105040302 67
    0x300052603034110a064140e41c5802c0b2084943c415400881c2c1c0340c2080c1880300140d900350018070052240c42c0342626a6005c0c54141c4d00191001030020000440c1d42c0c1d85030022400e40c1e02c481504d9001039901800f9181410001c0003802116000420300204800b94400d59031460304a04141e49180c1a10014042450b400c100103010751f09007883c20900344001d107203281d0049035002c3c1414801210050b4200602d007a03500c00e07240300507440181403101c0050701e140da82c3d55003010742c00c48905505c2d1000207401c640300c003401c861400b980040900b08a1206261403800c03540e40c1c600641d0090f49800c22440f034a5030911030b402003e449402e50840e000c0d00030000504590208540b207005080290070301040d41e44c0c0300b802d690001150b1801c1c4600347e010345000c4450400b1500f460920a013041c402103243c070300c085117850294490810721012a84e880030808a914884041c600108008001c1e0201090090b00300c3c00c442c040000844450410722038048040342c07841040343c02e250b55254140000c056052 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 657616456 1250 657615206 657615221
    0xb10020c0405011e03030c02060d02040303081509010602100b030708010618110406080a0905011d030c0f07150f0c0b1005030f011a0f010e060d1e0c02030a080405012904 74
    0x110300141035644c40b20342071054515540400f070f00f4460620007e20455442000b100c00001031140103644581e528507010700458816503c2d4128503030300140c80306c01800d10280c124101e405990040c00880300107081c0030001d10751001056014014a180030400c030200b406060000c0ca002501d41c10040346d004906012681d00800e10104424100b1041000710360021040750803403102500028072445918100d40142143c0003142441c103041840030b202002c020000d4045455020203580c0a40109134002d9190441b50141c00401c0c00c45d503030750a9240340b140c0c000703220b1032034542010001c2034080d0312100c0c848030085804a0300c800a80d80188010f00b030500500e070007030f10b01c03030028000f52405c1c504102404003501c41c030310b0150000c0c0d60300e62000c0e84156645c58041602400c40d650307a03080c60300304201030440b008802800c4140310740c0d1209a45490322580044480070760103542010181c55084510840140003910b0a41d01e404004100b8400c070030711002645980900a19491021400d100940e81c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 657617706 1250 657616456 657616469
    0x1707080705060415050d141801021329031005040605060c0d08092a010e030a0804181b0f03060501030902060d021e0a050c070f26010b10020c040501 65
    0x944401c02042c0c0320751090b03c0642c0c4020780400c1d040c411500f4221124041d2842c2a4241810003016130b140260f0034043d5809148c4442e000895a120310040609034455180c40c80e911a11440c0c08009030801026801031180509201d03e440b072042c01101c03413030754105480745401d0145520040215107050310600b40242019101c245c2010700640685460304456100d800a1180d0400010700c40c040911100303182020100c46042210901c3d2040481e40d4101800280071a40d103041d04400c5240015902c41c0ba55480082c452500f42001500c0e8500070b14106d5070300c000c1d9141c0c10703500900718100000003c0c800c2155141248032000d558010141c54580c1d0206060514204981000d40c41d000304490841d030142002681c2c072840c210325185001202c02d440c0300000300c04541c030b5007030701c2e4410010701041b13192000b10381c107054807681c0b00c1c00e40f940c441c4540b10048001082100d08803100c00540c100075054500006a0400030303d01180800c84a0380b0340070010707085102e11584500d014802c0c075015252 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 657618956 1250 657617706 657617713
    0xd0506100915080919082d0f0a0c0c0308120109020c031e041a0301090b0103051504050421050c070b04050d0f050c0d12030506030109020604050f0d0507170708 70
    0x9011040c51200394061102c00401903c100050300c0c415080040812030310800c0340942690800c1e09007400c075600402a450401002090041c0a0b041c502a40b00032081e00c42e04950f2404420401140499100e026402c003413044d408004d402103413503540b000d402940900251503803401c500c3e90704085603405800407086144140f015102028000040c0c0d0b0700c80040c5d1181000d030000b0401400c40500455002c6041d041d0140e081d24441409940903604071240701c5014081608154010760036a8411211601c0c51400c40002c2031907032401d50400ba40040c0034000c003001e86d98881034208103c81d0200205030210b07100040301180a4410032074a0020702042c280941003604183c0090300901c1e041b2406000c0c03189030401041801001d00413560300903001400600d13611002d140044040f075000303a03c00701180c60708000400d80c0c2818081e20240702c2c0d00400640c900707800e01040000100d22001c80c150844410303141100010410005200a49204142006a2801e400c0ca461504410f03400600c4d03281c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 657620206 1250 657618956 657618959
    0x350a06060504060c140303180f06010f06050a05070b10080f0601030f020d0f05100c0e0a03050d08180d0201090201110d09231306080105010b040303090306050c0c031206090711120d020903030d05061009 88
    0x10b10b42330f40305a504514103255140000181102c15000360704019010380c20350400d101106480c0d0040c54112118503068445c0c03984c180d1407481d2912000d2101818010451030780710018a401d49034411500e1056812040b8100c0544603146840c40c0c42c0e2440340b83e50b81e140031192010b90040c450004140f0212400e120b02400e5903116600c441d40005120148203074032000c0b540240d12070fa140c0c0366607808031084801641c09148028060101c3d80c005070b000c91100350b100d005090f004540781c4034a000e580c64080c3c5031454541c01c1032191001c808040d2440200c400ba1300341c580c1c3c6503145101d04604900000c14402d0130301e85183e0864906900524501d00100420030009400c001b2000890750403000004040d5541d900303a6016100d48242002c99000c00240c04001680b044a018010302040e00d2040c46a503c044c0255402c03041c2005200f0b15a0080290b50580c03200c9c03400402c04100e01c00405402c6c001000c020900d59008500020300f050784820800060317051440c021a4908070f80d281400c0d0340e5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 657621456 1250 657620206 657620219
    0x18030f020409020402041e09050106110a17090d0605150402120f04030309080a11010509010b06040311310c080411010f350a06060504060c140303180f0601 68
    0x5104802009000719194180c0b203041d03549513419100200010082da21103440f540c4540502441e160083c0d210480c580800892001e200d07440e802c0294420800401c02040b164541381862428010800f06070001003060110341e0f25440300030305d8194403808010403107040114040303242101c48640e250186105003c0c0001c0380c0c4095400d550481040d810000807602c950030120050320002c10003514005000404003049039000f00040d80e4500003a00030402500d4042202e804c0e0b44002e0b096552080701400140041902080c0000d01050000d0130b0305240281c080450401b07400900032050140300d103010b0301044a0f080e0203610820341c100d140401180ca0a942c0b001e4100d807501c401541005111615100d4040c01200e0702880303900c03c2d0f0700215a03507444c14400c5003141d0100446c102c80000e074a0200b486c0314000e000300d00a5845a40701c0c5801c00d800e003c0c003101c00b44d891003402d8075680b1540d20b0744403520310107200030741c014508140740070506c44400010601d0083c40041c0009164401d400400c0003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 657622706 1250 657621456 657621473
    0x30a0201080f192904140a020a0302090d05030a0f0509060313141b0312072105040f03050d09170c0103181a0601021c0f030c11030705010b011803 64
    0x20502c00c0c25503400039140d6059500440c400845903601c2145845008200f44141042403405048100c80e005950316020060006441d58005100951203c10010507072290054001d0041481a0b140c014200140710002460b185a0500b05132800e800010f0300a0740c80740e110324000010501d50030002d160130b0700b22000c00c1e41880003d244104620384080110100b00c588003e8815055444040300e0384d81c03001c200042540d01c00b141c0034911a11480c0c00c03800c0741075591000e9440b4180c100d207403a40e1030745031203c0d03000b600c2d103c2c40a0304040080800c000318240b4100d240a00c0914080d0000380f2440101c901c010b04592182d41052201600300c1000010055001820340341c4140d00786804248180e014800014580d880c0500500e951481903042800d400b0040406104080036800c55075500080703c40741a00780b01c6001190000382059049421050180e040b94401e400b4501d00400c0242c1c442508030b04503006003030112031903510355401c03410307560b4429030b00c10404000300d1240c9105850341c0e43e800c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 657623956 1250 657622706 657622711
    0x10c080114040b04020d05190e0d020a060e16061107050402160210020c0d0503190c050703060b010903060528020a170a02090d08040905130b071b05030f040f05030a020108 75
    0x100b10380340c54060003103880b1601928030313445107000300b44040d08043d00c140d00300c20030a94214010500d00b00d8041101d0100042e100d020803990b8000d02410303074054595401500d05000b0411003403258118000300d030140c0c0c40440000300013998604428400e141899418107590703521940c070441c018010016030b140240041100300340e0454040b03110f40c040610513410040c101600300e50101c2c420051109001002c0001e00100d0200d0030400d22540c0441415582d543d81d0490240041e481024103100003007003584001d24500381410603408a5513031b940c80806036081201e162400201420341c80b81d0038041030b10b8401d80706440b9081581052070303c16004100300303403403000d588684c01c07045e01003503180c00190b04443c05014041c1c940078022000382001c00720381c0c2c0248a2803103910306e454006200651402951581360794401005e072400e0301c849208894005842d40130f084043c915411000004004000910002c1f58112500c0d403950b00d0440d0103461140c041e8040781c040d41086c0a0b070b0380140c0c0d1054156a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 657625206 1250 657623956 657623959
    0x130f080d0e0f01120f15090c030e0105010303080c0a020106180c020115050303031f0315050405070f0305060727081609020c0601060c051204090f290112090b0414010c080114 76
    0x170300e82c0c2038070b00081c060851440b00d02c5001c0c409003008074062905401400ca41d501c2c644082c414148004106422070b603003403001600064950707010800c001e00c024000e007680c2403584000704010317403640c0d6a115030300e0f910500320050075503d00091041c00c0e020700071600694580c045000b4410314080103c1c0c0c403880300606842d078080e010401c24142d46c5030381241d50041e60304001005912200c46c03503a803004190542d4282c5035172151110006d4005010a03507441500e51000107040c6039100c2030030a0315107080081d480a00c0c8514003140903064000f1150084c01400450000c00b654001000d0080e4440000e4021201c2d40f03004010b070740d80e640b000150b03440c11180c2e54505034058100c5070804e40e00300b03100c0054030040350307000040004083c0101c2c1c016249584588000f0010040030000c0050744c1028030480941c0a410684010007035070080d218075095490394580400c2481480e9612000c600c0215012903200b0700310501c19981071402d2041100d01d01c8542001c0390700394103204002d0b40000391101a01d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 657626456 1250 657625206 657625211
    0x3070908060f136b24120c4305010204060e030607020307061e0f09020a06050702030604020913020306091501060504030515040c09090812070e0916090906080a0210080c0a05130f080d0e0f0112 84
    0x240010301d0419912144542400140ca8200f60a00c0d005013354043e1148000140440e00c450703050307107400b00d00c45008508503001540781960070394802c0060201a50200072000382e00c0300640c0e10f060680141c1d55000c042d0240092034048074070420950300c08a070000d50400409222450050718005451030f00250102c4010f00b10f82e648403003d02903055000d0307000b901030140c1807c2c80309440340066502c0410403440da1643d59a0b0b213034042100c26001e00d100c09005540640da411040070084000c854006014a0105c643c0f103403170b50654030648502c024211854100002e5a40151045403c034540000d1140f814054203980a800180d489001800303200900441700442c66446001c5c2045c400240303020b542c01d00115a44411458803404140c0c0180d00402540c2e00381ca40e0544168aa1032081d180c0305602400d00b14101d1b8100c6680d040a82d564140c2c51034030b9004a03404400070940002071521000a10402d2200c050082c00308403030000c10b5000e074100e040040790700c3c2e070840481d207051402d00c41c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 657627706 1250 657626456 657626527
    0x14030f040302120304150f020c0108060d0305280e010905060403020d0b090114011d0609071209030509060f03070908060f136b24120c 59
    0x2498103612840c0d100c007a142c01c07001075511b01190840c1c5071014820494081e12400700c01d0000569404504036000c83c1e1040ea0038a0040010b801ba1025101007a45032040f03c20851464a145403088001c41c007807004240c034003400c0000380d079000302810050142a00c0040c241851503001c18854440c40c0402031003144d84100240d5001d01c2540050240076104031030560fa96900c0d0503400308601000b5648100d5681c144c00a512801d0185041d809140a640d41900f020589181840140f03210340088003085010089035640b0742d00c82010303003101d20384149a603a81c1d0620703020160042501e0703445801103400000811a001e880603120550000d60042c4546004a41e440d1101c0d1b500040c1d11145503040c0c440540c0b10f00c90311001c03106106940d194500c01d51907428101450541c82c1d554404c2080c500d82850311444080c082c40b4103042d0290090100b000c806850100955140c690b101590310b0b09101103600040c02074041d01c0b1030b40004d1100c022a2500d0700380c0d06041c0d00003d00c1040d82c100803590100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 657628956 1250 657627706 657627739
    0x150f0b0d05030a0f051e1b1504020f0111060903030a061a0702010e061c0e0609010603230708031209010f02090d1b1203110f0c010f0c0302120307030914030f040302 72
    0x1100c00c03491106e45070381c2c000756a107944030005801500c0c160165031114031902031091800503000e102d2880901c241295659580c0c00c1140d139400c0c1c808558104140c0c22000d04142a003007162a01440c044009035480c1c2c0303480301000c01111000d40c070820401c88004030440e006030840b000c8811180d0203282117580c405410001c9542e40c4550602110070201100140000c1e8069a0101a202c06c44500f544e4194940c054800e00361381007030001800d03100035406c40505c03008400c241c00f030803603c003402904c4c3c2da103031740f000820304581051214044044640003000101c0d0800e11910b04030302141070045003440d00748004142c810b40b100b4001400790107035940400116000600c17003001040c9141d03640c4041c0846e80380c000c10000985c01c00f1802c3d0710a11400075110340c03022036140b04c400f1060303403501c02c81000c1c0502100e101050210a0782503004145610780c100300c0100c000c610400356610041002300d2285440070041d0101100035406800910002d0140c81c103130b50896003281c2e01281c00c1c00000c0c21050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 657630206 1250 657628956 657628967
    0x20108150f1201090b0a0b1012090501020705060f0108070f12050f0f0102130504020a081b090d0c0602150c03150a0b04060c12110c0904030309150f0b0d05030a0f 71
    0x5200300e502000c0035018014484054104109892084040e6001c5d510f80c00508400d072a40c04c0b0b0040e80c056003510440000e148140e04211511388000c0001c288100e42d620742e03030b00320380c01074000356000e0f00b103841041007aa080c4ac0c180303401017003050010b044032407415480000400c074134014201120341402039407043c000c08108103500e0f24004401d0b180095400014203000f588070620007240b0407945000090140f51903c203541c0c1c0c4140646451805559030041070822610000c4541d07084142030049003580d40311820340104031071150703c586c48c7c00c03400d0860103442c1211120070032090002c004e007001585404001500d0304040c09a20b060411004e0400003000350140d03821000c0d5118000c500082e5240e03004800101550040e000344d2079080d0000021103c54080e07040643c002d61040c1740c1806141007500800e03070b02501034580000c2c4000955100d2096a00c6844020f0009441b1305c0c0346034281a4511652048038404c6400118100b4199910b43d102e0003850031010074403580c0140e40d2065400341 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 657631456 1250 657630206 657630229
    0xf05030a0e150a1e0207020901120c1d0612010506010914010324090c050703020a0201121b1206120c0915050604061106010b12040f150f020417060402010815 69
    0x125070190189814a40900101040c0c0060b00484812248188004e14207108070380d4100e40191220341d1580c2000140401c150002c0c50032030f09400a018005212032a81c12240007480c40da5043c41c090f4180a410002e4105205c03030310201c507901d800c05000d0b0711785e08010b0200032140121000074004040b000160010300f01080f00d000307000140b0700d601c1c9108014810107003c1e512552810440c41d55950012500d5000c1c1030002005684140f40702c40140d030103102c0204211843c1d802c00700350ba00c010300a072061400c240c4405030104901407100d00d42e20b4a503001b1500500162041805010541c0c0c80d03060198a05200f00b180d80c81d95001100555514070007008040d15000d00b0480c0c1d1075a8880d8000d0003054160351080c1c2c01c0c0a04000410401040030840e6642c12064400c622151929161300082211458040b1443c1c0c2e00440b00c80742540060181c005407210340c0b000182c07100e14011407070003811115049920b580d0042c0c4e0400c0011303070700a20300310b03044448e410003c07031060107003030100b60b800c800e4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 657632706 1250 657631456 657631483
    0x4050f09070519020a15050c120c041508040303050c03070e0f18010f0e150f060d0f0c090e060607050d1d0d0b0117210903070f08010209030d0f05030a0e 67
    0x2c0003c008115000070b0f401c0c5107140301d15100c15110000c1e0746100c00b1203400b035078030004605e400c2102c81156025403c0f0660401e101ca0702151401d43d07a10060950480c05140540108240600308400d0503050312a055101c404504040d146291030200105001c02c205c0169108070280074001030fa50f22a403010103030b2000d241640107203550312282540380110061003851784400c0b4520001d80a502080782108407500050310030001b03240000100060b80d00481080d17040c0550303441443c204c1d03104a024100f6003082daa218500700505010783c140843c0c0000b8540c0b80180020400f10000580005110182c1d041501d01000d44444540714031001204958050fa4009000d806100c240b0907011070b0386048a204001c040350b00d90301c6440d11615289800600e01450b1403001040390ba04060500a1440c44001000c0e1540161141c4241030401039075000320045a6011500c1a01d9080c10004510300c40300c142025000301000040007800c522000f00b4200585440d1011030b100100108a0b41c18003451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 657633956 1250 657632706 657632737
    0x405150d021309052a070c0509100509160f1b060501090c020d0c08030406051008030d021308010b030c01110f030f09030114040b13080c03030403081b0f1b0c0a1202010e0604050f090705 81
    0x1c00c001c0d2b4141e603000c01d0007241e1140c002c8034041004690300352000c2030181050b48550b056000c40c0e07031058501205182d8600c80e81203d0840c104009446881340c076010f040c59180001e00080070407002445c0020b01d44005042c8543d42140001140b03004055950041c0d02c440301083c0c1d03070b44407100c0c1c0407047d038a0350102003544004102d4004c2d80450750090003100081100b00c400e1a0742e500e404030b080e60080380c3c000c0d4150300020109901035200b40000c0725558810340031a0709030800c0143c2107103150702c001441200c000011601110301c0c5002c0c05426100c041301c401b520260b080c0754a82103401d540242100c0e0010900303407442010031a020058400c58105030065135160301c0c1c103040142240c0070481e030902031140914402ca60a40310035050b01d082283c088c5440b82007042d0620708071800300e0444020307032640c8500c42c00080313299510700000002e083c040750b186c00410350f113200160134810744140951040d0000d210920081c0c03280d0b2007107201803108490059142c1c5801a096032144a1040381104200 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 657635206 1250 657633956 657633961
    0x30703150b0d1116120302210910021201090905161706060114070305090f030d0507050f03041203030b010e1c020f0904080405150d021309052a070c0509 67
    0x1600d90042d203000c042c8198103100110b414520141c561103000741a0016691619220000c2400142503806465190500519004401400740c0c2011a25200304240710390113801c011194030140310329100103548034002d60800180000c45034003660140107060240d40e4442c1d0030402d0040c200624241c0070022602049116281d4807546a1650500700801c6140310383c1000c0343c800e51040070a00342d01c010706e107030032428003c0a60301128244d0001c000564480c014007100c0c5e400d6a800e0180003407400042e1500c5071b1783c04562800c01d040100b40302940ca402c3c1c00500003003000c240e0080140c1052903051500060400c200801a24540c1f0020340641d045034100c5c92a42d0b5940d65189000341560007101c0d03082c0f185170314030100704028000321401440013000380000c21140c00d01c1110402c202d400010081d042403003400300c500032a0001e50300c28410a0035003104000510039440744076006448055110f82070044090450030081c0c02c1646400c07803a000003002c50034495088825009000014002c900d00d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 657636456 1250 657635206 657635219
    0x21504051c0309350d060e0c030402120d0212030c0c0d02070503011109130509100905010f060815041104020702040f09030f081521060a09050705150f03070315 70
    0x40103d10f01c00c6400c034160307058029103a500ca00c1d18071180204426030600d5004150030442084e009040d14500340f07519203402103800481207400d1481810440c907a0741d240e02c0e00717004101e00107500000300c011701d4020b84160514aa408104440350702c0242c07488540c0d90311080d01c44c400030320604622080302e009108e8429074a540c0400d034a4110384040700240403919200180c0b207824480c13400c9803135004403c0401800d01984980220790b20074450740c181e0358641d140207048000c6e40d0605100b168240d5450b03018022400040c4074401c00f401c00030005280442001035100c40c1840040c00240c03240c07600540c002003684e5103030101c1d01d440d54098010700070042406000006042500030490104581070910205640710b0b8078010f104d20445555440500ca000f0305101c24070503500300d101d40500d16105483c40c0c212040150038010080f00a00140c00c95490800c681040c4558102c1807199040c143c50f01140c003034040507100034a00c0791400540da901c90303c0b401c2d0014811200c2516046020140000d0780 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 657637706 1250 657636456 657636461
    0x30a0b040201030f1503020f010215070305161b03182105060703020c1e011103160905010206060604030b1005150d0c09031a0402040f061401030f0903021504051c03 72
    0xd58401e0b281400954003180140301034412050210b903170a210080104054a032000e88240d11309010b005503000c1445420403da0780c044200c0310701e00032a071104180070300702860429400c03420185141002144803522a044030f480d009000107000c0000e00c82c41d812280342500c11352001010240e06030381043d80c0580d131401c240741e42080165002d025a40000780c00fa03003e802140c144081402c0540301190042d00701c120b011944415040d03240d0b589200c1c100303075540c44100540c0252803036070750380b00b05846043d0014014a1142c10242c11900301c030050020030380b03a19060724192503019000c01d86507075a9804881c0e8100071640880e034881c40d02a6008010100c800017005c7c1c0c48401e007400d0002405805d8251558401e9201c0285404002400198409013000915400a01c000d00c04910854404072100586485070004840440c8e04451104c2c0740d81c040c8aa405455850902885a99029100a9101e030f944d20384080c1e0844e4030500150801c40c050005072030180c800001c040e4086404d030b400a00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 657638956 1250 657637706 657637711
    0x804060e070923010f0e0112060f051905070906080a1d150103030908060903030103030e0f1003020d0c031e0207081303060b0114070b061203070206031e060a0e150a05030a0b 76
    0x901240750000071070306140000b194410740e4880784008809900e004590303400c0721720b4071900b5149d03540e80f131084e00120303840340c05420f020340b8060415000008c595002e240c201c40c0050590410301040780c00401c24643c00042c02e035402010900d0010b0740d4a0440000300100c5164010106c1500852044400140502031168141e0f40a03903500d54420b9154016550303a00b2054410b1a1030340e0051004200080c482c2110480144003c1c1000c1001804131012500c0d0000c1c506006000c6034010614002c0c2d1304882c4145801254039140a0181c449000c09c81c2c00c502c50500524140950001070340828015840110340c03400e4082c2200000482e50303030420500400728411b196000440a101d01c0c5001200b400c1a00c00705500000d500501d91521020000b2950380180000d849020510284e005690740d50003861140b500300200e5004070410740a00008800b00801c15413203140144c000303000030940013801903270000094034401003546001e00040c036548200c0d4070550780344c0714143c0c4010800c0081d121460 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 657640206 1250 657638956 657639011
    0xd060806010b27010306031202010906240306180f08030a0b0108090c09040c08070303121d0a0f0c12050a0b060406150c06021e19030c0804060e0709 65
    0xc1440e6214005103900d4492000300d9041100045480a801561040c1a80214105050000398a96681e841089090704000c42802503507446d00c081d010b0207100d015214050340d14040440c0f404032a0310511403201014003014104075070710440e40300130745004a52003903450f41081d056000a00c03245042c03407041e0b01c11a90001c030030b400e14a941030f265004401d50380c06504100c000d003201220010600000d288000c1c0255020550590300103004441840001c0145000ea80c500001c40d594901d90001d0b100500050045400903045c03540790280007081c150a101d52000d5540c101580c01c3c18056520140c0e60051640074000b04400f40801500082c94801c441c8a00e9210042c0d03130b640c5c402c000807128940301e085002550400821710f0140700d0030ba0b004c405441081c0050134254407081d0044124050150754441a1000450074a100d001a50b6403600c0c0c113203460180030001d465200144803c001400c0240b8107500d910000300030420900000b40030382a003440c10840b4104098500c245081c00c8507500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 657641456 1250 657640206 657640213
    0x1809051516180501050403020609041b120506060f0a0f0c060c0e01030b040b060904020d5601080612100501050a090b100509010c060501030b16110601030213110d0608 73
    0x2c07198601e512514044a80c161902400d043c9140c091146c1a4013030000140c3c01a82d9048103c007024140311805112055a603843d01c0c0440c0c0c820064040354000390503184509428024014180510300071071b00c10b8001883c005455801c004801c0d245062030810090925040ca07000340c806607440903120041f0802680c051141c2e0249005120442d2042007840350030950410000200e82069002481000814240004d80e031850220b900c00074821010610300103074092101c6641030030702c4008512003130f80e0052000c13000c803e2030880ca0204100349a50340d0600101c200000c18a503030350010229050b68110642c3c5034000d40805890061109004a138455107403000080f4892809100e0b20281c900e0142500c06080000601560320341c100b1304070241004821004030000512500070030703000f90322845102e403203801e01d84440070a107168410307003000f000780004080045800004270281106e4050b110a41520040d810340b9001e480d14140200ca040c4000900c0f4800c118158800403c84101c5801d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 657642706 1250 657641456 657641477
    0xe072d2606031513020d080702030105011a0d1512062c03040b0304060b060d0501030519021c0303060b040e1803130e09010b090703051806011809051516 67
    0x15280d49030958000e41c00da8803805000f0303c0e0100035180182c00070010320400750f42441c02d85c00201c0c1d895444004503000080070a512045007000d020b1036001d030011031544100100088000807441c050007000c1d405803500c6901c0000c840c0c0b40714041501a0154030890940645142000d038042d104200d00100390300c1460803558426901a1880010f480d0000e003c0c1d4500342c6000b4180b0110341002c4e206a0b4400d55410885030705569210060559000603d4085455855810140d0a04000380c0948200c4bc0d060481c00005070384001c046903070380101c0d140010318100b0900b0110300502d09a00003411000b000180880d4440399081020310078031a000c0452080300801c10f01030f4503409180344c2c0342541c0340c6440c802d00203082210815684a1098800010145003441c000b07502c0c20016200000803036603c205012803e40340c3c0a5400690201400500301540340c00b00319001c42d1a00002c420b0050f075104c2e09001044428040c024104645241c80c0e8800d0415119400843c207003120000c02103a401102c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 657643956 1250 657642706 657642767
    0xc150207081b0c010e22112d03010302060a050a0e04020c0a1718210d0c031b0201020d03020c011d030c0615031903120f1505010203040e072d 62
    0x10b00c50b401c100290140c0d41124210100c5006070406c03540b018074141d118210040c0031000940540324000c910504055036156000008160340d6440b000464442ca0410040c005600c804003140c0c94800c0500e00b1940d00c80308074204072030351451211300301d0b403180c00040c0e0f1035a01000080ca94810070b001c1c840d0f203400d603000c0c081c0401d060300c00c0c08404000d80388044030800c0903180407091289540001c01641200008040310a400c1c00c00d0301001c40041194041c5400c01e065000c50700303005855010a61031a21103607500040e580303d013000704c00410140c00040c038a811080a400412030300c0c450b5108540320aca501c07503019440c3d4020203070b0040039110f00e000181081800060111070f2034009400b500143e00194007140020080e010b0030f800344200c0c0680303c00d01c68214403e001c021130700040d000614400c01e0542c8914005c2c142d126034110350081c4010310101d4a514006500190309040a0042e4090742c4500c02c0800c42101004c0c5070120003040140c2c0d016003000f802c0074110900141c86250700500070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 657645206 1250 657643956 657643967
    0x2120a2909070f051303060507140a0c060f020c0a140d1706100c050d080711010902060d0f06030807050a05070f08150c16030c02030613030c150207081b0c01 69
    0x542651000000010a2090b401034145541d503d4452400a250081080c0d01c60403545840d8001c8441540e140d040104d880d5028440c10290401048503d140000701c00c0f000304844501e0f80301404140d0780e541442d4409000703a04480d00f207076898040e202c00d4046418600003008a9030081c190501600d455540c81c10301c0b80c1c0742c0d04003400389604140340d1900c943c4180105848004102c0003882601045c0202080c0d00708030700b406550050351828040d29007484010424411441e501241d40c0c1400880401039540006032118050045800a0120718504071800507120b290310151403110000740000c00d1000c00300712070840601807402c036200c0c2503035a0110700e0569000c1c80b0b030a0300c9400c0810000c25030020702180a4108010103291400c0580080420481d504058011404500094000000c500b800e00030a0fa003d0b030400c045001101d0207403000342c1400d00340040104040e50070f00c401080c80400380e042d680601e400016090315082f0350381d46400040c2c40c501003001140306181e40c1d0b160302c3d8401c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 657646456 1250 657645206 657645281
    0x15060306030303010b0a051201080f100c0905040504060f020316080c031e060307031704030c1703040b070305271309122a06050403081003021e0402120a 67
    0x5001540f9581c80c1105d512196000300044204004040042301c1031030040e891001e010b0401c180150803a03003c1c20400901c7c1420810450082a082c200d690000580003d00001116002e0703e0104c0ca6607150700d0508010076000c1d0940c0b01c7c0d1440401404240c500319036020505036a5902d50105d00d440300341c2c00020f10b0004a0390400131030400c440c80b417000302030002c003585c02105c0a011188215169503503406040b4504101014022000c5003c005000ca0504d40200902001a18010444c0c043c44200d859100b21b010700c0003050000690fa0003010710031000c590450700300c2c4071492103030382030320003140c00002b51a1201889168056500e5100304003600c120a0000d80c800125400e140c00d01d0019a5030028a4001242d43c1c00c40200742d111004800b0360000c5440c1c420b4000040034541440d0191070310034080d0003000d2003001c9040600068580002031080300145042d800d180d51036000c0004c0c041d114400c0c00d6a100c1c2d000100b440b03816400750b0400201800000c800080c0d80030300104007a200c007880c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 657647706 1250 657646456 657646459
    0x1051017070b0d020d090302011e06120311120f030a0f0515091b0c0307031707020c2b061506020a031202031005030604030c02010906080f15060903070e15060306 71
    0x10480812814500b94001c180305840108094205428580480202d0725007210aa003d41d444405656410b620042e88101c40380301c0d0182000f10b60b06050042d15600c41861000b0b040c4020b04246654071401041004492102d0400d11580c031003424218070030640040e100700b02002e00b40314131504010014042d56104545000104822a0300031080110020b03018002d42950f1188003a0340341181c140c1001011802000c030021507581c030061070300410820b1038080c0e84030034043c2002882502c0ea40880e114405050844180c901c0c010300070f290b2120030041c0408001c62840d100000740c10080741c0c0d00181c055107000c0d03054103019540c80d002a40c40f0340800308000c000500c071030b41203a1038903d558041e5030410704041c41650029107d4003c02d03e442010342e4160003054404049404560f0320084410103051a4504107840b4180b83c8a401c003002000747c52441030082c4505e9059050b140c090036129500f000500303c40825540c0c1219903c0c039601940c0e400e0b100c0d440002030f01c2440c1001c030222070107030b40c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 657648956 1250 657647706 657647713
    0x1e0c0305091e15070b09160b03040503131205011a0f1306030204090c080f03040e0c09120d05120c0903030a050c0a020a03060b0102100b09071808060901051017 70
    0xa10a00b0494660400b603000400b101902c2c040054903116081d0b10300300c400e600d0150698034826401c26280302e80000f0030301c1500ea888841c2c0068500d610108250450b10340183c520344a807203a00d401411070041c0400010801008400002c01d01d0b0821400099107028200800203402280c55400010004c9070346e01c0d0f0802010441e000a5062601c500206000d10b404001a40c5480354006000d03940244000c1d20780c0344501c403049c03010401c207200c07801d46c00300b05400071458a4030340004070120740c00c024180c1078003400c0880c03541c0c1c440d11202e024491018110b0155401141005405047e0750401c21215400d107809000103611030014a080300c1e03224070003e00440c103180a0320342c204c0d0a540034125100310f5004441003440140c0301d450755540518491351004c00c0c0d80910b180020700c1d101104840003c2c0d5070600d18002220f8407085880741c2c00940d01c2c0b8000c50400d06d002100721100d40f40d070b800078403d407003800d04210404406500050041000b95110700c8003560315001d04007100c10030b1900034030a40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 657650206 1250 657648956 657648967
    0x31b02010f0f110625020304050d150e1e070f0b030a090c09050405010f051f05040b0609151b07060206150409050f01060302010e01050f04030b07020a050304061e0c0305 74
    0x80c081c0c854100704208618160300d5442da180c01c15800d00c50191800c0000000c83d1113103450080300d179000340303501880c00c3c8021418145400002180040301083c042d0040f02c800c4404003840000d508201240d184032402c64010641c807220a000001250f0200240c81c0900300011801c1c5a03000d11b92030031244051402400c64507021051030061402000c21148202c03007a40000d800c2d803082c01000e200307901070000059000701010b003c809403100240f2a04580b000782c007002013441c1e00020b901098990544000039840204804210944030b030040d29980025004066940c2000c001c0007000302c1e5219504130440d0000346884c1070354902c1140516800743e000240003c2010301c805900d1500a172000740041605074807501c0b018142143d5000107130a5944801c0e00780190f503008101144105000c0ca000c0f46891002816402a030080f03010041640b46040c0108115a100700129030000303401800b40da94980d512000540407124030010001d2500032101600301081c041c04841071002c4d01600d4407032515 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 657651456 1250 657650206 657650237
    0x618020415060801150228120f05030a0e03130b090316051503270d0206010609051e270403030e19120c0b09010f0608121903061d0103031b0201 63
    0x403005d0001c118214401d01c1d0030745400c41c01c0c2c0501d071042540da120041521103e90301f08003690701c0c400706203101072280083c112041c407a440700880e50310030300c060400568034820810003030a61250464500c6c00468210300820001d81d0070300117001c0403004038210f0320b1000c2051b40c43c60340d50040784112903004004460010000b11454002d6038401081c0141c0d2813070302013444110507002c0d40003914026961010328242d90712601084150301400150500788421442c01c030018169449500265034581490204000151a0500d0074484903a0100c15006645000491801c140c1000c4070207500090401407189401303500424a4007800c040018101181c9580707440354000f6076000e040311810401419002000b04045007011b5004285580c004a410518452100d058807002e801000441d000654500300c044107820480d09a41c0503c0b6240c0d100c00c07500c04080e070081440da8408640009010503038105071003007a503c141a030b446a25a0310200b05002039100d1020007420009000c10030000c90705e00031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 657652706 1250 657651456 657651479
    0xe090c0a0918030c0c0b040b0c0d020a05210409050112021926030d090501050a1103010b180604080f010501030210170a0b0f03070323120307080a02070618020415060801 74
    0x1424011864501c00304d50384c8030b444c2811f0f4040d80c440850003002213080728440c10f080c00aa064400244010603070035013251985a2905040064038501e0102101201000d4500304107403801094011820442d942c2e550020006004d5202e0040b413286824401c80660107180d126030340f0079580d24686010140401c9441040900c1c2c12260086880c032080c000b1010301c903428000c4602d05441400041200e003005040102aa5405041800e9920003407005100c1e0b03405803026138012a0043c504100c200003240c0210300180300381d410419607801442c4071403102101c150802d80c1280d1080d640369040e00c008513011074080011104582d2a0103e200201ea40d010b00d03034003d5280780c0030003400c0c89500c0000301d002a29001c120f46c811202d0590a80007103094400480d80200c1018113200686010005003d206240b0310000304042c0501c40420045115030903981c1c1500c0707515521034010460400e401001030581d2101a10407441a03082254429145007440c40c100304403850b1761607501c41c603424114103010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 657653956 1250 657652706 657652727
    0x6070c03030f1d0d05070515040c050901091413022101060506160b06010e0d1e1202030d050c090604060e1504060c06150f0b030405070e090c0a091803 66
    0x20540c90703604103881158507200f8210520a500a401d0800454030306440c20000b03441510414800309001d584041900462110404034608a07003c80c8c5a95619043ca0040c9150700180d820850708d000100314810f03154000100481049003006199031022200019000d81d020020b4000441131006803d4003060104003519030103950020a5064072440840c3c10740c3c0103986240701031000d10348003205201e4440022a0048020303c1c2c804403803420540401d0300083c852200900d65051203010381018040d00d0300c65020140d10281010389052070400081d0359410000f04080150b1070074020072906001402101d0501c00007401c110304091504a0950b24940701075401a003041d003d401483c040701c071810060024010648030b9403281d90301800c14400700c801400760882e00000740042030050268134200301d0220b840c610341503540c0366150718005050000903403041288800c22818494108400f01ea1603118070000e450103160b8650300d624440070382c0e034403241c004400102c420805012070b20880e18040b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 657655206 1250 657653956 657653963
    0x31e1519090e1006050d0b180709020a081f0807060e06070c03080715020405180405150901060602100203010f260f010903030b0405060a150c0f05030901091706070c 72
    0x2000c80d5501c060030320954041440c600c500781c110000c1502d50300f4051040002500041d5038641c0d1644080d50707810540e0384058088540940c0f411100c0450b1503041050b00b0181001840540d101c0d00120406490341c5020b64262180709100d12040000084804030380782152102c030020403a0703500d031242c242c50408816a001e074111804114910219200008000056208000180e40ea0030b450802401000c0c05807040c48109004010400c00743d682d004405086d06042200907e40344c541d403801b03a251050010058803a800304c0c5040000da4081944200c3c02c8406070b400781d402c1d461480e010001284000d0143c0100d2121409041c80004002c034581c1c0d074100c1107054a03400344007070109a036140801c1300c002502581c0d1034660f000209941405408c0510000f518180a18203103100080c1d00c480540c00b4840d00c502c09040e400c50194452072034004407540003017500d15051450304009880780c0c030420640380884d0038003000080b03200c12356403680d12101080d07001e0030040c2c48014044031014152201507 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 657656456 1250 657655206 657655249
    0xa060b0301090c0e1e071706010504050405150f030d050d0507090e0405012a020a15242c010303080c040b04091506090f17071703031e15 60
    0x10f40380801520240400c58070748201843c11940f004d900e16020748031000e218400c00b041c8502c941c0c002049110102d10305024648030755403180100c0301070045500c5943d00604000c1030102902c15144403050000707040d00d051111101606c28107641e50045c0d00750308000f031010030614425a40740c2d0301254000c0180c0c6051501c05076140c00e1180300c103006440c19621b903550b03081c10880c50302d80c4008103022008804030001d881080300c0d0001c1d403255000f20010303011103201c50885400101a9010186d4905418102842a008030844800d0615140030740d02e001c800440066000b020140080300001c1804030750a42c25a007195411621b401000c1c203a107003050b60a01011404a4a400c050700c050170f0443c4000442512164256495072465031260b014400c84020501c2003109441c0640240d82440d01801d40c11100e108203d4a0900b90f6884405209000d101c90000c0719400300c000c40c05212050000e81035580a110a401107000c1a507489500110720030344080f139800c00484c85418007101c1c1c000e9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 657657706 1250 657656456 657656471
    0x1b06020c0f060a1b050406050d06080102040807050a0e0f0402130209030601150f0c1101030c0e04050c070c1e0e04140a031808010509060c0c0709060f090e0f0a060b0301 74
    0x5441c052000000c440c0c00e4001500300500c040451042618400c0201d008610003201d06202424910880c01001c080040000702819046200d42040c8010f1030785500031942c40da582d03814a40c4030345407805503603c100d40400300040c0c540005694030f0702070080e5598480c016202c80c0d080221944041c0302c000e103c290280040b0416540501c8100e0013400480d96407215104a50340c02484041c0300d807030110a011035110180041955112040c2c4401001e080004915120490964013030000601e899802030524040000c000c138154080d00b046441071524280309034039a24081c4101090b40544a01c1c0c1e460200b0401140d031400c1d04c80b079081030061781c422103580e42c2d0740c01040c10014503c4054011402c0d8a030201d4032242c5484130349000f082020700030020313420300040080c1c032181d005d0201c070100385c030206001104140c203100d0103006002c480000c0001c01d94600e1402d80c090040d04c20350f001c0c54039001309111030300c0c40401c1008800f2842800707081800900c1c0e850700f004010058040d034066603125130 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 657658956 1250 657657706 657657727
    0x2131403191a07050304050a11030a02130f0b1002060a111b0a140f061807080712020f0108160810050d03120507020c0108010605030a0b060d0f0509010605011b0602 72
    0x5005034240c0a6a04800c04240c042c100b01c60041000d0300802c00c0040800800010076408240c0100c0654081603601c1c14101800c0083e107000c0c0d4001010398010342050400c20b1480d2150310501a0418480d401e10104041004010035480d82d03d41c4000560014400240c0c418920340c040c000046004034a642860405950101c10416403a9100c00903032143c040d5006010b41c110b203181e804038107580141000001c55858070345510000d420702034090071700706000d45464000e01c0f9200240801000302d80320240c0e502481c00c0c00d03103442c0c1400d03409007410251280c8035500c681881c52044608042041081d0000c0300c0c2151201c1c0010058010b50003902c0740410a5030b615020ba800d800e000b80c1e5024500c2c0c400b680440212040a40958103551003110a51b10304d0341c200402e90304440f140d00309943c1704d41c0c62640040c042e090b08a5695071000c0c00240304048845a64052441031141c104104a1039070341c481c07154200d40c500d0240c10701040410041009542411102800040c840c10300582403040c22035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 657660206 1250 657658956 657658993
    0x30c030a0207150b040536010207140d1101200a120203161e0c14010f0c09080d0206060f210307080403051b0105030705220e090f0102131403 62
    0x100e034625141c0344c0f4403611003468a805480d41001c240406403045255840f80d000b00c59021160400c101c0030848180c81107220290b0503105466040303610803c02c40340301403049454a0031800d280700410b02e411100480e02005100303614580714100c000c1c40c003d10241080b40921341221034850204103989841c04480b801500240d0b000d00d0070070218011138462002e01424000403a100e105070170442c07d0004026030b9120520103007080e00016090780350108611070b030340074220301c0c40180d8086090540342440ba41d803200980040f6030031901075421034600c2500072a1180c03425198954048440840c481842ca0180c581c8034540c12003104104100056071240c074207642011f6400c0e10600300100c0c080040c42024000641d201500400703191050800000282003030102605903401c020703000c19010f51010301c502c10417030702e1001c00d0b40410070b895964602506100c42150603008501541c90760801c040414001d4604540c1004411540d403801c0c804004000014920074540c144074907500ea40d405140d48 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 657661456 1250 657660206 657660233
    0x21c030509150f0301030206030606190507060e010c212007030e0604120b04061e0b010e040e0303130602040e070c0b070f170402210303090705030a08030c030a0207 72
    0x903190300703032030300c03081410003035000c0c0c41c5140010a24800c00914504032070180031241034a50441c0d0440e100e803280c0307022802c03900507040001818160140c00b00c403696000800340000f18404d400600c91003030f600014509880d8412100c90218102182003040d400c2400c1d51030038603071012400041c42503006600b000c883c1c41040f00070125a074000039410240341c0e01801504200d481694070300c1c545807900c850550811121807014241e4000c9402050402c80550800200200d41c0b003504804124250a60401805260102400300f01c1c00c1c611041641014001d828880d18150091400c5a655243c03686c00609400000c443c81c41d405c000200c0ca0401c0707058100d00507074160703442441608407407411031034400010300510b00f8060b00c505002c2d540b90b0700a0002c4400c040184020100da200e80c804205c0c08000c60794031400c40e800091611961140c008051403141143c0790444105554072070505469030301b00800540b42c0001040082c02ca4481d02000b140c110010003001440d00c0703040e031200c0311003007a070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 657662706 1250 657661456 657661463
    0x8091606090e0f241809010f0e06010605090d02030102120702030703081b220905181b01140705070b040e01091d03090103090c0512010b0a0e061c021c 66
    0x8034028803030035040324030850740502401c450900b6801d14141c07003156850408001204024090b03d001480d40310343c41580e905e000c00c641482a0382c2407003034409010303111014a15003680e181812030340700d040d00058040d04844054540d6480c081c0c0380e2040c4040000b080400360380640d020040c4028000016182d24480e202c254040c54a0319020b00e002040c0300c60150400c408070340566110102c031900382048440d07a00601442c20070001d0070313171056150850300b035020b11032840c9044100020f51500b104410710340103400d001e8602d4802d44044c0b555000b5030203540c440c005001c1440303082500e03d0740c5c0c0007000c06c503004000316028299940400102c1d940113030885041f214441004020202d0140136898004400c0b107200001c0d070031901000341d5a40034210070581010780b00e01d00c00d01071020107400f2a01401c005406080081030b0b01da0564040c0c50140d10550040c80c0446001601021004801e402600001e0114a012140c11402000c003c1a040143d0303001c004460440405450000c401446512 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 657663956 1250 657662706 657662717
    0x4180510091401051506071b08072c0c0f070b090a060b121c031107080a09050a0324020424030518210c160807230108091606 55
    0x240e41c034100782a5020324440c2c005070703030401050200d20030481d0200420948280c03009611850fa9060411031400d24483e2000c83d480040b4003c0b45011010a1040545000125024403e0840005001c130843c01d80342c81d10784890754a01180d4140806002840d41e190701c0c1d8902810309200740c0320031002c42c4099581505a0f4000e200390810890360340112141140102e41c40c001d1141e020764040d072a0020140410034518800c00110b0100d4060360114208401d443c40880d00c65045250222595110b9076482c3c0104901080c00550ba2400595400030740740e101326006002040030000c003056021900c03800040a401780804200c1c00a01e458a40d810220a60040007414011002404840000c0c2c4040c45808510259083c004370000c1c0e20444000d140001b0346427201207407102645d41c021110002c005000706000301d084800c00c1005032043c3c0d504c0384284c5540590711508600740c0d450f50307032080c00050f000c0b18102071658050034503c0d5000e4010019600406038031034040b030300c0091540101d004070700d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 657665206 1250 657663956 657663971
    0x111030a02130b040644060a0801180f08090607030509043b07030b182b0309050a061118090c0403123015031104180510 53
    0x2c1104140100030702c40f03101d0a03490319041c4200105103499008540c0c80401442280e1645240e4081580c81d02c1c4004140700c0410a10385004040541d0003a24918824140c0f400d000c500c89106208038207001807110104c45458032035941f03a910a00c44000300b510302c402e040c4101c0c0242d485980050802504c20360303510395079005100411003242c42200c04c210301c0c00c2c4011030704941d940001d0000e011807031816041602e0720310402d540038904042d9800c000c20340110502417000c40802040f442000e0741081040d5030601d0818400c07841004007800e200700d0f586a500000f641068000d0b071001181c140600c007520809081038803403038103031294402c41d1099500006540201705504040c4200b80c1001219403081c541440030302d115007130099000190a80c1041400340740900e008000041041d038410044416510407018412400030541c0c0008402c2070a14035030242030400034903500245d0758410881300c15015110144001050b58041c0f15030710141618092010440170400882c40d00300c040c00c0854100b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 657666456 1250 657665206 657665227
    0xe0714030a0905100516030e03040504060605090111061306110c0d0905010f0810050f0a17160602340f03050309182208070204180506010f0315020702030111030a02 72
    0x240a80a50301c40c0b581c505020300130b006c0700404003110013210303500d00800d102ca0f51500c090b085124130b0380300951284c030f0710700005115034001d0064401e480090f03c3e640140f0304034629076600d80e0070849600706c81c4a01c0902d1a00020203c2e40000e510040c0204c101d814501c0020240341b824000101c0500414502c180c200569079001102c10385c0741c603451030464034a051100b403081800c450750095078864641c041d415205600d07642803420081001c46a640303500c40b90800e0701a01c0b01a0480c0a2603130404801d004698140009803040c10806408240f01c132500040c00003004102911107610705180c0c11032000a0042d4141e1800300145008802035542ca403e41f20030403184050050f00e200c3e8484c4c04400300103c040c035413001403d88191191401003010001c1c40e150820f0302c80c002c00254480c1c9441494900294030920900c1010321401c100c44441c0d0321002c0403003082000f403000514004610032080c1c00065160090500c0d00d1000d4000b00310240542e50b880c0c0c5942040340c0c900340303140c0c0c00300e20030681 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 657667706 1250 657666456 657666463
    0xf0703060e030a0903020d05010902092a0c03030708071407061505100c080d09140d0201060602030c2a0a0b0c0105060a060e0105090f0312040e0c0307090e0714030a0905 74
    0x185007001c0700541c9082d0040c07201424641462102070f10502c180d2408030244202900002d440e80d5000b071651040f403074501d00003815402c0001c03021251031070000494242c02800c90888140c031890f00000c43c01c5a0303500c6412111603200503c80340401c402003442500a10000001e080d078903200c0d0001113600c006141031280041c1c500c0d40054465031035841c0100b95142c1024001c8000754110100a66420100d0b030304401804800313000034864050a007110502040209030010b050456500a12905954807030407a502e0041d8141240150040c155944014503500c0d0f581000b050911103045000c1c0c80040003490203012940a11007001000904414002c400c0c40781e40ea00030001c440540b150340c10600003d00000200b0091814003200140350f03001d65440d030314503203c60800101201e080c0010582e4101c01c86e0000d100380b40300d022543c000b0869051110003681c0c4512110303964031652600c0c040520b8403014020300380a003803140c0e000c0c3c03151a01103040000c40c41000009008a40900c461400d47d1a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 657668956 1250 657667706 657667721
    0x60b1306060302180405041703100f06050a1107030819020c030d03020c06010f300204060306061e1a0307120204080a0c15170a0f05090a02041401080604060218030f070306 75
    0x1700303514020411001840d202e400150002494220544a55640b00051101d0301150005d2000302000c1e0000992591707c01c00400910a43d561009400842650030580e0f660107804001c01e00c1d4001e01c410b403490500f030034000720948107a104441b030b4400c400011030b0a0002c20440c2c0f400081c2c0000e403c4064200c1004228010650300100447c440d20f800e24140e240500c024940c8420840e04806150300d0703002c5400a21170303c0d001842000616a6840c10310000c04052144840c4a80d20480f80391000d094440204101c0d181c0a01d00d24030102000740e19840c66200410a1007400700448010305c0000491010f480034149c810010415150035040c81d1503d242d4a80c000f40d1111003d45061074402d611401d00c5000000740c64410b40541c1f14007610b40d01402036001041107551900c0100071440f400002c2c0c40008a00943d010800781082c100e03c64440c11090280441ca5441070001c10006a030355030040c003051000e40044101c0307180c440700107410b08101c0502082c4660040b4414028041540701da82c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 657670206 1250 657668956 657668959
    0x9090109021315020c0d0303110c010c1202040501120e12041205100e150c0405040c030f050903090a0320060d0e0d0509010c020609040f06120302071a07060b130606030218 75
    0xc42c103043c8007400a5481014000300746c001c1d200c40940303508140c00f0f41c000310450b600b00311011386c0700d4500402003802404d1050881000440b29040c1541c103ca90b482120103880041c1e40da410002c15181d092006000c980341000020710400c136850030400c1481d00a000602004201030202c1c2100f418a5840c20a00000011415103056407494008100058007180380301e820942140540d203000c0804094001c65200ea900175040c2039041007078076410380c06041107203203100c820013454858070030107641d030f0003103408090b00425000400e2000c6100803007100c9096400c0000c0486c00014200441d0141d00f1640102c09596285c0494002405043c1700c40403128041b494010308081e074010000b000414501e002902a450010301c20071240c9481e084002c0f15280601d051128a82d5240041401d240140c0144e006015900c000720721503030740304413010058044080030703418451340c0e854010082c0901410f603075000e402d1345d041a02c1c50f40140180307002821541c0340181c480712688280342030302c9058140217 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 657671456 1250 657670206 657670229
    0x207050901050d030c140a060501120302070608090a08270d08040524040f150201051e070c050610060306050f090a050c12040c0617091e03090901090213 67
    0x50005444040d41a07044402c01c80341c803640c144081c1819180100754420160880c1240c291150300c007100003980c824550311401c070800c0310341e81e1070b03100802e00c19081c0e90040058128203400c004c02c0b031003680c12580042422040e20801c031050b5480c400143d2280f0340c17007810011540c04805896001030368142110000391141d12083c840b41d51401103900c201d0040720b206130500a03040c04a07a541d0000d0b08250a41445160307a50340c0c0f202555643c501e00f911982140790f154081c0d103400188180a254011741007a2504503501c4280018410b01d400c00038000d40400c5150f00c1c0311808584100a51805400e01c01e003402c1d101c17410b12030014103540a90304028000d001031050442c07103403030304024154411204000050b10740c4440c550b200b1503204240d0b03270380101221542403109120949488d4000c64150741ca03543e00821009078035a00040040320f254503150080e4500f40401c42740f00d0240340c5000e00d180256403410440c0c1d030026504503401e810103841ca55003c550602800b48051a004c06842144400c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 657672706 1250 657671456 657671459
    0x24060903030801170715050403080408060f01382b1b050702100309050318100c050a12110f060a140402030706050705012304060c0918020c0f0304180c0207 68
    0x3002e5890f42c4034421031b290f5424008901646501c01c0d4103460255921103119940c456643c0c802580d14030041d901c8240001008000081c6400d08007003c5649038200403009444020040030f04980b4494142020b1110f041000105012000b1305e0803012600c3c0384611480c101c01c00d9030402d000321140b007409444440324501c0c45069580d003081c20b80d141c89504442071415002d200104401a007000b0b20001c0c041e21010410821061039401c88902c0300c142a074120540001e20101160411000400a001a085001041d001c20001280070120000901b00344a0464441c18020715111750f4090344911500a002032040803035407805030301c03c281c0030303148124142e08080e00065103a422a22619041c42000900c58042102c00c3d001001c0241d0340000a02002c4400441c8000b080c0c0103c030201c611616100c2c031340c55403a008454030820348150780784112080c000f61015030000d502043c91071090307110700210002c111004000820142041481000c0d103458105980020344003c1c6140304295000300e0780 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 657673956 1250 657672706 657672749
    0x110d0c11060714122a0316090f05120f06070c0209010b03041a0703061a120f010608010b0f040f120b0f0603030304030c020d0c061d01050f070624060903030801 70
    0x243c6810130303c8801000850707210b10000180000c9030965140090413003000e010f001c505034a002d07501c26200459000d441e42c42200d0101c4200040b40a201d50010401c2e206000700e0070541c12050582844a0031507107511411544d4915116088400a0010f526043c0030811030820540c07040c010160070040300e003941485d5a90034400c03000c0204444100c0204000104201c1c40381e08030300010011070800380f400004d100102181540407074440d1882c0494039000c90050805024014101e481681e518015642071403605001c0754031154900010440911000c02d442600340e43c008002c0c00400a0038401c2e880c9850505168040140620100c1c0740301020000151800300480f5070295141c9440d2070b8039400761001603103101003042c0140c04559141c0380400d50742d82107039102551071414000c5103c941c0007031004603424800d10b20756003070100062180314000780280d0081c41076a5100c1c0c0d6105c45500d1003a84c0300140b8404d540c407c0c0006450030b00c081061507004940e05004d480c41c4540c0c110040550316 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 657675206 1250 657673956 657673997
    0x170303070309021507050303070305060f010804020f010e120d08060117040308040218070305040309050a26120a02010b130c32041d09011509110d0c110607 68
    0xe118606041d10342074608215a511841044561002c800320350f19400b03039041003581c170f0f002216008003003031134076011a1035880c107502038400341c0205955010041d691a0300f404032203110203801506000b06000310402c1542e91816018240c030b1000020030a02107213000040074030720050030f990305000001001041400d00c0c0c4640e51303882034150811000780c1d1505e101107240c08013020305541c00858404103012586515410250085009070348009034a5180c3c410804491a1881540c00003030b0071034044103140e0048142043d90100304416113010120b400304d8054183d2140c000d040050b556070382d2141981c6071528040402121041007000b01c03124448016000070445440ca244030003080311101240c4030340c0c550000c079521114804985450b41d03802d00300030712070703022420505503036590b0002607698805125840f0700c08030841d00e140ca450b1901d444e400081168410640c0c02180800085030402d880e8012004020041c0c0c0c2c070f03998104c0c060301425003001c40141400041100b20342c0806203102c90749 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 657676456 1250 657675206 657675211
    0x9050c12030d0c0c0c2c0702191b3f03120b1e2d0d0614070804210203030a230403180608010602120c100e0313170303 52
    0x1100b0014480141941c161040030310034074020084c2041010201e0306036000c0d1865940c1e8010790055481c11641702100d18140d0b00e0440348440168402003010b219a0040841c2d540c0c2d00f4058074a580ca00396940d004c83c40e11b41c101c0d80140b0300d9034900d801000c0d80d500f01003a0f080c5600c8000300e800f11045600001609070780994000240803c0705050078000161025070024010903001000c801300f901055164038645192005a144100b11349034480010341180d00c4000d484559204500d500f58004600300b0503090301c0400300369a0190f484d5110300c140a200c19846020f01c00a0700c91180e145080d241c841c2d6591071010000d07680c42200021b0030002c0303800000ba05d810074a02540860b1842d00116514600e501001030882141c0340481440305042e0003146c4524011401d4a0f100304103911180e0076650504280b00e501c0069100606444140c10018058254462040e068400882c03c1c60021801e585141d000e00906030000242d08480c202c0c05031400e4000e00e51b050716550303040320392058543c8a0100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 657677706 1250 657676456 657676477
    0x2061216140901140d140a360c080f0303180f0d050c010f0603060b0405060a060801060f1b06061502070614070507030f140d080610110106090204060309050c1203 71
    0x2104604c0c000035080030348441e80c0e0315842c2049402c0d00d0003c20070000c2c00540c1d017030490500d013203e4412034005510240286500b0b22080e41c13002d6440030200c0451126281c015074101400345004100c01c1c8061100481d29140d8800035038403801e2182600b500c080384038090381901e502800b12182155404144951400c24a090054940e209801814094203200e84107000c00c41c82d0040100800100b64000c100681e000e603801c02150b0f8560042c000d8490040c0106e4000c00c04090040215504c1200540c507480f01710300d04603412100307039404800d44030b414980c1100c070300b034480070240103080168084920401c05407008000ca64980840906081481910030544503400a18502400802c0050500175035103c00c940a0103c55420300029002c0110104031450003414004800d543c8207561260240ca0010212402c561502d90140d1720307030585110305e40c895501c3e168000740b11801840a00000c000d50b4030081003c8500f031130140e0400030180041031081b0a21140d074640240300006030b401ca1000f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 657678956 1250 657677706 657677717
    0xb2a030103150c09080111181021060f0b210112060b0a0305061819030f0309020111030a1206120807082115031b01081b0702061216140901 61
    0x3082c0c0c0d0101e134805001d401402c61503081c504100d002c0041000280f90351607444a001300046c195604106c9902e0f9a2000e0400003034464019542c4041e617042c09044403080c0c02d900007540360761075070b949900d03814580c440f50190070046042c01e4400014580e11659890002d032103409581410304a087d220300080002c0c01040e0307503042c7d02c8810f8440590f900090350300241100c0d110f14014043c081d030703545841d034000f405010300d80b10b10703803400717603000450203903030f501d40c07030b4a116110402000c400034108042d06034100040141c030a4440309080c0010700c1d0300003066a488219810390301c94042030781c00c55440281400d4200c5401008208140c1c00d0390040c035404101555200070040c0d00003205071000b1080642c040c082028040c110500c00c0d2030107034507803068041e40e08800c0c0300c0103020604410a0b000c82c2c0410b06035400600b000381103030704c814501040844003a00340040c503000306001e500550302980030f003445502400788420b0700a11001429500d441c1c8841000d000f0904003a0300d000d811882410300c007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 657680206 1250 657678956 657678971
    0x31905010b0a033c140c13090b030a080306030316060b0f0916050c120409152c090a050102030a0b04060b030108030f030a0605060a0c0c0504090b010e060103090b2a03010315 76
    0x1130315041110522184600f8442c10304020040c07200d554000b01c4008112005000c00060400d1a80200724000d0b100038081e200405131900d03031501550001b0b0140d03070305000800120f0701c41d8210301c1018003424041e44000485001440511405110508440e0700c60b81d04c58040282041c0c000342040e84100745450001e480d03500c140c01e070a241040490651380040000b00b00400c250300141e0181c01c07011081d01403000f02590707440103c40c1d01c404401c0c024a400320715080c48410000800d2000c0e13000004201240d000f0746040e00c40d9030881c0c2044d51480c2d4840d8840c55403403680d142500614001e4580d28030400c1c6554075000c6490ba40744510103040c201c00001100240c1c003502c65902030002441d025000ca50340b042c46510082007020b03e0701007201c07081421a4049001d04041c4201e04115030f02c003060b4190799081c07101101007840001e000504240e02c400c440400240b040410b94011003640709180d406c514400d0051100e40e0300b00842e40881d00b0301780010008190048403104425500f29000144103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 657681456 1250 657680206 657680321
    0x10c0e1201180f0201171302030616082e091a01080603031b0c1003020d0c02071203121104030b040314030606070209070e040e0d02070f060e06031905010b0a03 70
    0x391100346c00501e1140c01181003000c55010080301d459624400c50176038155079108007200361121071541461001484110000b807281e00081814203508203022490304044040d246040f415070b000350031610a06490b00b070b65126040c94003a828680380c1090070104928640000440da4031300039031118418425407100741041d0488240402c0600d50805401e10301080000140940694880d20001304018030f00030002940b60304c0820680165803501d040d0302c506802c01c3e2030450f5868000091040291b40d2021041c41131170790f65009000071482200803008a150604015000c44442072209503550002c01c01c020341580d03001c08440b000e80c1d04580040c0e5544909070b00702c40c1c1c021151400fa030010301d040392401c038001000542180c0c480391a0700302c43c0440d84559455800221038421800428195400369865151000c0959441815001d282100601100c1100142e0704282e00a038000c02c400100c08070140c3e03141c013a52402141200b034554508082148881001e0001810002941803980044021 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 657682706 1250 657681456 657681467
    0x60f0f100504020a080412080105060412151505190303200c030f0601050406061e030b060d060e0403030624120905060f2a0313060905010c0e1201180f0201 68
    0xe050042c000319204d00c40802c020304400016030b016980c0c01240702403450610300c00c10317465041e181c016064505003031070080111208064804102e46000c1c51260180101d010361041c1c00703800c0080c0c0a0078824500d07010502c0541041d600382100340710900401800440d41012400308915010910514026100c0079042d00f4240c804405980c14000c411001c01124800078025050b04e404480400ca9540c3d242c000303a915102c0500070181c9009203001f04001e49010354007402043c20050400e82c41c003180582298102c070050341000c502041c0c142d0510090541c03510902000d00741e4211170490b44084500f03150034444c03103c4401010400c0224900246503401d800982f0240c2e0300004a900b0b90814811100780c02400b102d010720419200075400d41c04504170340d10b420079203100500a40c51a210406d004044181c82c01095803156216120140025002d01c69602184000e40d03503080110081010001d0380b181e0340c8140c4136141e04014928010000284400c6440c9034001a0a4240055840140c44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 657683956 1250 657682706 657682709
    0x60e010c0f0f0b07051606240602060a06050d050c150f070b1518040b07090b0c010203090106091a09060d0507030b010e0702030a080f070908010218030f060f0f10 71
    0x641040440801812208038060345100f100011401d0f40c4800080ba4140180c55000c4000b00b070140ca034038089401b6601c40078011405420904000c00281c2110107800c00c694815030050348250108410b6005e030703114070805440210341444600c6555102c0c5941c0d62601c0f02e01601c916a03c1080f0302c00d01030090111103401412482c043c0c1c582c3c0302c078280302d102081d0440d000c15944950341242d800c0d915148210f5201001000034202c4180c8940d100c0000c5107600900c020b0501c40100404108109014064050400700b10005a41da143c50007680d42903a07142d520010845007042d00d0b0340008141070322580d800040550750548103030303500b900054009030071100142c502c1c05401c00200c248101d45a1103810394080c1d05035009940c5890200326035a200300e80905000801300f80100d20101d203c1414142c01c00101d02c4c0c0006081d03169000c56003242e20507481410300b51b40c01c4a4030102410103006610036104400041d011a140840020444440003000300003600007880001e00d512280d015080c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 657685206 1250 657683956 657683963
    0x4020325020c03011a01090e0a09151b0f02120a0e0d060e06010e01030f03050a210e0d0815100c0f05010603021203031312020f0a0b01050a08030307020304060e010c 72
    0x6540014110000e516610b20b100028003030350925001115420700030304038119120041c1d40e52051540b03404908426140041c280c0380c2c01c503841c0d880d0300300407900d8909008450b24052400240300060048030780c01074598801c10400b4080304d010381d40160b0742c01103100f081c0318449030003856039041603800c1260b088c0c540c480c0300c0790300641c6065000203000785a0b204c048003020000840b295643c071820b07650301002c42488000c2110030440e0700f14001901c40d6015049400e0203041c160802c2c00c3c03000c80303050348044e00e0098541140c0d540390940c6840324100325808098000342029400c80c2040802150354400640074a8000c90700e5280b81484d07940301d15000a21240c00103120600c2c3c4205107040c40c041c0280b0f1001ba03110700c06003070010041e0179020003181e018641c4070b11441444203159591240ca03842c0d2071008025400380103170340e0415000074066030454610802d640c6203070791b06010400012456036000503202d50320900400002c5900003089505842c40340c140b2003003012a07072004886502c40301c80d009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 657686456 1250 657685206 657685261
    0xe150903150a020d06082802040605040203040f052a2b03020309041b021515030709020405041802150c0102190c050c0603101e09020313110109050906040203 69
    0xc07408032200d41c0501103403200d201c814400d0580e24581b031a9a2036038440031404825280c809162000010f5911200072071015002040480c0e66100240c2240c00443c2e00366038900c480d515a40800c4010b01c40c800c400901034511014580c0320891041e80825001001c90103025242006070a0030007a500c00e03c0490950251012481150300d0003d443c0d40000302124001d42c07e092031420b0010012203003000028055008000383c409606e001d050400c4040c000410000d40280d01c0380e0107880c24400349002e05004400981d80390703c0c003010b0100b11141e00c0d4034140c0100704206520010b98841da0038509418000d1450340d12000c090010900a215800311012280150540904201d41042502c01464043c0c816140200003480078081d03d40b1080b11449080000ca240a20501051714600b0b40c000401c0d1700c554010944a0020388102d87c416201039400360801184002049400134500f0a405403e02e40848400d15003800301d150008040c5c0558862070300071000038419030340080c2c0312100b00d0140d01c81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 657687706 1250 657686456 657686461
    0x207060905070602010c231803010e0703110a05090426030406090b161215030c06020c1306050906061b0106062c09010302040902130504031701060e15090315 69
    0x8259550300603c00c000140d400d0490340402ca5001d0340b20005015094103a000707602001640d00540b0b84d020040420ba20f8016600055030394809204080c52820b4050007172150754190f00303012400d0034071010218441c1d440c0702030034016622401d1040d600070342d2150050304910b00a41c21100702c44c42c0d05100301c903401008404c01c0140691038101e402c03418014031411420b610313a074022001c01d40d4050130300000315000004412000c001e9510005076602c0c0c4062940c00c19483e0395a1131100403555000701c0059018440d80714407850802c0c011800341040c0310342001241e03c0c060114022040003081c00d4402c9030b0110b210500002011800802107903c54000c202032030b2100c40c0076107807107078034401180105410310b40682c94400c0080707040c94130300f402460000030f40c1c6160f00300000b50a103010201c0c0c00180201c0b0400050800e07024041c0507138880d1715210220071001c03850800101c070580c00381e02007101c1200d04010701d0b19001122404080c124031016501c000d03d80229160010f900d0320303d0b1500001408 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 657688956 1250 657687706 657687713
    0x50f030411010806030f06041b1a0c010b0109080a060207060905030d1a040e060606030405070f0b09150304081c02090d06050f060d150515041a0f03010c0c060b030102070609 76
    0x100741c00a1a00762258440d5440d44010b25540b24945018074400b0350104012401041207020361144600050303148984031610b4044004242210583d001d0564402083c62920810280a414171000e402e290402180740380070a44d41d619401f00c8001780031103900244140602c6610b1300628101074002c02181d95a00065000400030300714140c500440d81f0554000381403514081c014200211210780082c101901d80b60100b00d56548060720484140c4a00f402c0060070001144480b002018010b1003203403582d52400600c25803e00302a520460000704104000004040b107042d10740c0301c007100b513045854a62003081c260080c400c000c5899803095010f071050f020402e02d50042403049840440c02100e070b40703582040c0f04041409010040c00002124200b50f001c034034543c420340d485108035895201d401c84040108049a45006030020000b4500440c00e460b41001100080d140400341d000b00180109600c004040c0e00300184010840d6443e00c9900f1260764003501520000c9411403004c2150714064036 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 657690206 1250 657688956 657688973
    0x11070f20041a030105150a0b4816090213050913060f02040806010e070c1a07020f07050924031605090c040605090f030a12200610030f0201050f0304 65
    0x24030039801c000011b0081e4580c00300d20714400c10b001d44510101400c3c011a1095038118901050450070f4000e00e01481200c004441e040d888090300d42c8c198400950310b100c11a05000d03070301600b0f540c0c3c01071000340b50380c610303080c520700446141150040c1ca54178a050500c469443c0c5600482c1d10a030140180304608484c042c00303500c2c003440390f24200a02c04220300100c0c00c1c0e00840c41031000c1c60300485d0041150101c0609001c2d13102040349004241c1d404296510040e44a113584c200c6560170302a010410050b404002d0300d01d0b00700b140c400500d156450280003c9400030010100c03040c0d0340c0c106080c124040340124041d4030100c3c4c01425114005902c2c2c814800000d0a80706091003030301e00780d01007550b02da14882201e0075500d09503130380e500d0200c0d01c03800d018850101221090b0180304406441000c12001c0140c07000710801e0f55105605403400c41e054410b20301003064040c0c0250025414052061006200402201e070711502440c54054107000503111400b800247c04000340c400810002001b2a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 657691456 1250 657690206 657690251
    0x210090521130801110a0e0111030a02010b21061b04031721010305030706050c0403020d03030b09010f06081801021218060a140a051008030705060a11070f2004 70
    0x2a110b8141641d4000a500f6100342c201a902d04c08010031060a840d44265040c0c81e0448040c1030611048802c450280c2c9540d000745034000c010b0355200002c41007845e06280300754621560840d0070704c86100540040b500c0313080c0036124050644c540300b811542c3e040402c091f940119004041c1030000044080b8000c41b80e80001107280806843c0b01e00c40f1044400c0340d800a05881c0c00c030f0011410070040c1d640f200d00400b8003806545804c3c00c00d00c00000107903202880c3c0d9080702e00c01e66001c10981e800c1014418503000603000f0000b110b13030110080c03004a601008080e030100a002e5807080441c61008813034024420400c0180310200d1070010040380311f01c0c4100d013041261505007150078940d6030031110800c480e404981c81d01428000c102140d04e40d00da23504181c4d000605003c83d1004280c5d0f0b4140e451955100a00031140d5812801c1040811002c038455800d959030349003026032507c3c1c8241d94003030301c3c0120040010650304030440c0001240980c0448002e4561014004000c2d09000300b59a043c3c036110b8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 657692706 1250 657691456 657691477
    0x4092a1505032503021b03130801110a0c060204120c06140307050301150201060b1606050604020a0203251b0e0702070b040909083f070210090521 64
    0x24000d1a24688600d085903c10701d000805410310003180b850b80e40701e100050b094002015001d00c505012030740011042220b581034580216501d0031101d1403020b40d04c10301e9201d188640d2412402d0203260008000310b0b15480c9203803a001c0010b25181c40d1400c024003035500704503007107001180b000301006104036a00080d44c40c0d9480740c65084114284440142c030040300c003480000c4080c00100010f0000c48040c0100110038000858282e03141e0306d02030001d80007603074411041503402d400101404040c1c410503401110036581586003210611005c1d66a2003081c0c00b6034071074a91039000b680050101150100c2c429480308400c0070070700001441199240c664041e911448510901090b1028000281f080840e9803404a050405141490f10001820050010380d111803040064844c6d25020084440c0f00703040801d07241c1c1800d8070315042d0b048045020514840b03003450000c00e2100e00342e00003940f5002d814468202203440c1c1613a00e441400d103501208410102001c0101c140420b1108a0250001c45403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 657693956 1250 657692706 657692729
    0x9041508010c02210306010207030f0201030f1a040608010e07050f1804200f01090504020307030b06070f0c06020a03210f0510050306130f0b330f0406080c04092a 71
    0x10701e0b136225071005407122400360380030280c03c1000503e00002000b070349005040004041100748c0c0740340196003621a4010002080e01240c084600e02446500080e05c01c20000f040305000046040342d6a040602401e4814204407030090b08a40d070700209075105100e92005010b00b4106032800790000001503500a030004400740700d80c100c0d41080b010031042910140d41d241307a024a0842800003e51002e0b25940030582c070755000c1222a00e40c1c100030018144205100d0489117064204000c1d804010341014045410040e007810101e039101c0c6d0380c00d0001d0350403603405841ca203c0f0310b0700740000c0014007044400c003070500080048001485100034215070054096130740b81d503101e4400c83d190300c0f802a4001d01e6180f04060880c041032408141650243c0c941164035000c42012900030301d0b80f40303652000300901700300d540e0a1a160800c0108021055000d44d01400020309000d20345d51501030702d43c41c4900907580c0d250300c03000b44402111750301a4250f1505203002c4084480d20070118814090081c1c038201403 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 657695206 1250 657693956 657694003
    0x60304140d080a0516020a0b06011107080c03010e07050901140102010f1e0b0604060215060f090c0304030f090302060a03051b031e01050d080a14190305250509041508010c02 76
    0x445606288128602c1b0740c00307060400c5450b9a0070041410103011241000b550783d2810360358150420120740a4000c5030010803c24441d0010182915524960010740750450030040015480d46405181560180310506421000c02c20040b401003021a443c1425a810034a12405001c501c20802003130204851044c4902c00c6040240b21141c0304500c141001079000c191105842c1c03903e006103542000d802000801e00703180e1580010403a5405441c410040c4800100b403104060700a006842503040030700305101750900e0350300061801c1c001c51070f10f2030905446d10009414000c0c0e03070300c46040000e420316a0360780300c1c10481000740010006c2494141010003500010405140880c41c030030700f295000b40f0451230b021001800725151590701492800e0a8401c2c42008480003042d0400f00c42c03260640e5000540d0301e4150003803841942910b02d030345109106820300004003136000f811900e00410594001c030b008550b8400c60410f622481d03020b0890f9520303140d14201010b5003c0394030345444509410300d04486 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 657696456 1250 657695206 657695221
    0x601050a030e1f0e0c090a020d020f03070206091513030c0305090d03020106090605040b0a031704080319030507050c100b01020f0703060e0606011107060c08070f0309030302120414060304140d080a05 87
    0x101c1d03c0c82c0102d41d00c080c00100203039161041d48c00a1840314020f503000b50500400c403070140225002500c0c03c03000342e0031403001c0000c2c400040060810041520700d55114030306060900d41880d0000860250400864032044410706009500301c3d1106000a0148901e0358150b04009000705424041c5402c0c2034108076000455103050300a804840300000c1580c602c9a2455481c600881d481c1403100741c4252090000042a58091000d054054410344030400c0794640c1840c005c048450041c64142400340c00d1003d4000740d41c2c00144002c840000100c00107001c0c0c030010041c0d140604100c6071500c141b081640100400c02981c01610300311814000b20340032510b9120055888002030000514164400201003008500c00d0703034281805401044458644840c1d0b40750072464000c084401d8000c11981e680400c10550304228920a103014400018202800e200103c1b0003040b08402261081c00048081014020f40691001c01142c01c1c508680c0300f96900000984107103070850b40032010600d41400078401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 657697706 1250 657696456 657696463
    0x1080a0e1905061f0b0903070509150405010605070816050c121c050403020d3e090106021603022101020a02071806030b01090c090b0307350601050a030e1f0e 69
    0x3030340004c240c1100d04da070404403400b0094101d6801c240c1d040c455a00005466211441e800b40100c400620440c014010441807005903201030b0300100c20810f0812140021900100a503884842180d010b1851012030f030503d685014056424541d000c0705002d0b0281503941d00007151002e4400c508000b041d0b42e80c807110265014000c0d840040d410400382e0404000040c2c52042041050741c000c1d040000d1039142a19022107172559010100114101105588040c40c0c000d00c0c0900402191000303110031003141a10700b4000035203100c0240540204004004100c15a4640003d4152984000c64480d41c0c03101c4000e513558000e2049841402c040c0408280700700307060103600c090702c0d042041da5070680d1800035900000c00d4410b0181040041c045404a00504000000c5001d081d8a981c0c050165400340a4441040500306030a814101030f1a180b0703819560116815078009000d00340703241c07284050b1006401600500d0206060785c000d414181c40805070310501c002d20280152001c019a5845a050695 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 657698956 1250 657697706 657697741
    0x110f0102150405070f0b0a1d011b020411030c041e120b0910090503090406090e0a1101122903010905062805010b0a1e0e01080a0e190506 60
    0x180c02420610030400c80c01d104998100c0e214100315001e6990318050300709082d800b500301240306100043d072040c480fa4400744840c807602c0310f82d03000f1060501c0d80d800608840005050000300c0081d0f9140403045d581c440c0d00904000055140740b656030b01d8190360058850f0312a002d0f480d05640c070b01f54400710345402149020242d5130b0400e00034a0184c226228420000d00080c903000c410302c1005a00420320009000750640c0303611640041d45c4071000682000280d50180d049401a2443d000102d20a44800a4101c81c5d181c4c2000d040800c00032500f0040310614040303000c0e40b1141d0f091500b54110403036030b6040b4201161a4940e07001800101404042c01e0340d40c0720b0000340c40350b480070380410300c17094001c62025543c0c072103032681a880c0c010303540203c415110700740e02c80c00d0200008590880c0d11500055015a510007468141c95080e00c01742c0050314100d00e00040d0382c1089013075400070f08107468591202c100c0c894000b00b22000d07005d10301d02800c1c203e040984115144d0041d00b001c0348010810780c28405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 657700206 1250 657698956 657698959
    0x2912030904091109310609020d23211305060412110f090a470d020306040303020a14030a090510060f0e1b0a09060207140d0f020a0b0a0507110f 63
    0xc440090740c411000c6025605c0058445a0380c0b40c1c0c0074001a40d41c0d269051080d446011084090208017a120078800d045003910205030f009020122503200071a0715a0755482c1c452610341d41c4800072140005803417840d43d008113411000005010913504035099007202202d02c01c0800e000e40c0300d85d280134847e00c0380e940c0c07080035080344400b804074070110015040608070f05203410714204003420fa20207041003122000c0f546c250b006c1c107610340504c81103180c01050303c0d1800b081d1030071074840c0030650110390340345401440039003010307030220315045954440c00407080400c0303140a6044c2c80e070034a01b02400041034111402c503403600c039042c01441c0071682030268804070341a1996003019640f40204d52144510000e2043d0b00e50b91308282e14007402248403000d0403c0c03070100e030354100302c0701c0c02c0c803001a08d8035840360001714281e5071050f04040c01d43c1c0c0d1361068401031544002e00c3c0540c0360403071000c1403d034801038102030f022150110b0350301c207040d0b4044094565640900300d1031020741a8001480703003800040f252903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 657701456 1250 657700206 657700261
    0xd021e1201060f050d02391c140c010207050a060605090709050f0d0f080c0105011805090c060c16080607171e072c042912030904091109 60
    0x440800010341d018126550000310039001d07d00404a51f8400807080402032030078003d44001508075040b00f0051100880f007030b40d640c0c444e0f644840501505804190781e0180088100054001943c1000e4068400351030707010089410aa80f54030302007000e0840ca00502d40160507080009184c075201d0720426044500103482c94000a01e89014420710724421141920074000018102d000110700303900410061903144000035032541010303955030603101012644881e09052100f8058019404100101c0d407890440d50607039640040d001840c01e01403c00c544481c0707809034000c00201440f0102d20300e40301e40d005540b101c0c040d6805402c0e1810482043d01d030700c02c030001034400d4405400c0103008100c1d00003d8904001c8130fa100d41c88400c500803003c40b83e1f504a03d6010300c0303103075201d42014014007041210441c0c03d41c017040725901e0300e20540900340ca40188241019a02e00343e00041c1401120390b5044003420901c0441c10a0400c045002000081c0c0ba005100303690004403032006400c0c2d944040c45c0207d944 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 657702706 1250 657701456 657701467
    0x1050315040b0a050d110a081c08060f0315250206060f21010603051207022808010c0503060315010e040f020316030b0405010c090501020d03020d021e1201060f05 71
    0x60000030442c40070115000204948080740caa41c502034442d01551260042200600b03010302030200c3d004a41d072141d2603691204e680d1218013441c000f01031803080024a411000c9070758010004048000d20351004d501802402c0101107046c01c0300604c10322410f02042950200210780600303080da24541c0c1c05820058201c10045005840c0c00c1044138407020000f0842400343d4045007041003202014001d080c80c030b80d9541410030800406002c3c10310340e03a403c42d40460508041d600450071a155140460083c80c03428a0804004540c004030500070b410000000c03c41c1e1904104041d00302d92081d42c103644a40b08070081d081a02005070300e0a41600c100c07003c8645203464a9a4505030b40e000c0340412645070280e200300c0c5820201c14002031004601400f059003090400b07040030790844020301c80c0801008001c40c8180715990f00040c1d00030f50861189001070303454003540f25440c001e004005c0701d00481111038050b1a8a03092090282c051081003080e001c04907686c03440180c445408950300300c0c010a400b4800d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 657703956 1250 657702706 657702709
    0xd090b070302090a1523070212150c040b121f09061a040b0913021c06180b010e010e0d05010e03041a0301080a030f12110408010e0c1e0d210e01050315 66
    0x4582106d0040008842c200303406070740011801d0070039022038a210f03030195010070302c0350000d694044d0300700c154404410f03d054103026581248e4480d8012900525403c48040380c081c2d42400e6023107441004d00c0400030503254448402201400c541d106185039040300810341025600c04000b22400ca4981c1e8003418074058121040c00945410388003c42c10190b42400360001503004403040744201004030300d00103403007810709004803d04000034a0b40c05105103091104245c5036080010044c07000000d0810308403459012002889203422920000c003154289580e038005040004050000e440184500000001c80310203441e040740001d10030400181c0c000c03400d04007c00d0095911070380c910765610700450a1900c605030303001a10340350041202842d80010f802c10002000307100d4040e004411074054105007002600050034039848001000103000442111215a551005140c0301e89521280721411300b007222a400d03e0080700382102c140840e680c1e43c6203141d550b10600c102d9109600300c03002d00220346000b50 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 657705206 1250 657703956 657703997
    0x414010509091807030b0703020405130c090e1f0914060316030318031e0215070c030209060a05090118050a0504080a0f120e0307020a06090b0f0d090b070302090a15 72
    0x1041840f60040c0d02010000c245c114211910414182d04c1c056541c500d000b0911548003d000f811a404503c2c08207062581540020a8801c039405400034203c1b54460310b00d8621180480e506212900c2802000042e9203034058200c3d144103075131070900e001e0f503682c0d4005140c0c0b6030107103000031244401942000c0c000680100c605850311102240c407105c80546035529071482807514050b024031200c803400d10404502c0c1103105402c500b0310480081e81424926940d004038000b00d0b010007849140000005080c0380c4950f001d081c024075004000c4286941d58101d00503424400640e481d003c207080c02c1c0000c0403500e15000780b601403503000682914045000d001125140c1c0c58000c410708220f4140e086450240090007408030005001001e1a0788000910404c58031241991103a010300c4800481046120a4076066482c0d91034001c80f040d60710300d00601603400401010000a10308901038003441200750b8140e000c1e008505e010390b0720b10101c6840b90907040603444d14504160008031505015129941540b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 657706456 1250 657705206 657705241
    0x50903030403061a0904050c0a082802040b03030a09090608011a040209040b0301110c161406070f06020f032a03070c0524160306061205060d0204050c041401050909 72
    0x4ca00d000c0368080382000141d016209503001d0703840c0c0c0e01c10b5900c0b0900e8a840a4814001c001c11030041111444400040442c9209184141003a0f124009588150b49854004501070300c0f004094940e28000b8000c06014401240074000f6000d103000f4022400c49014401ca0101544020001c0c0303540d40004100300196101406481d005500c5910020300b6840c00d000e00502e0314180c3d851503448000c0410307014a040d01d05000340210511040c0c00f040f61005007c00c2c0300c0824000e45042c0e83e10f004038100124007c014401c01054180f0004640041402c800c0c041c500800040e03103149030321503020302400781c5100c069084919544040021524841c040c400306266540300c2c2041d29801c0100343d03800641c404014001d4100c540d0200200000d01d42c1050417a002c1324880e05003004214142030340280b00c009042800000380390385501040b4aa610280f0221400745c1c024000e01051134003101c7d003401c54009100392995603826440d02c20b4a0b42c043e10a031a980c02e005040300310f0b140d03120409180c119210 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 657707706 1250 657706456 657706481
    0x504030c050109050102030a0e03041415130b03040606090b030606040b04110304110f01090608041211031b010b030d050702101b0c06182403180303061505090303040306 74
    0x201580003403003e018410000d07000e074000503141c2c03070303c0e13200342042d5840340d956180745800810040c4004000e5030100030885200b80d0740e02c240b1207160400c1d003000b44282c280e00c450301c45100c000010710f55032060046104a225107801d01200340c0e0b540102083d1a541c010103607154210f0b50018209003010351000e0710010005002160040d9210050212039105a4080d9958051000034880900340032502030044c04003860a026031a292a9004043c120081c00040c03040407085042c2d0710700c03031044c800a0b2141817103000343e968a0f58030140b610000f0050342001003484d424107244908034a408101d004080e9125128189005825801c00261050044400e010b011000d50501200c0704d00000c8501c10741d11421245400314200a8017818400d400d41e40382c46988110b8009100391040c047e074102104000c501c1e90b038110704006c1400e070043c00110060709007650001c11018103256060300000126030a00181416072205003004030b4071445144e8800350551320801007007001a07120740c0301c02c03500c000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 657708956 1250 657707706 657707717
    0xc030a0f051b0304050f0d1707053c03040821041d01030b09060c0a0c2402121f05060304030e0a14031939060206160504050108010306050403 62
    0x740754458a02c40c4801a03220300040d0b00c04582804681048080da01d8407100031110740d06030100c00c0c2e550fa0000094074550042200001c100d020401c40200320300d02d611100414142e04c076440c5444040b03402c424203400341e400c8240c100c803207121a007400320032079090b1003050000d88851288000c0c4202c0014a02001c110494000c000000b094084480d85c60b902c0302d405400d51841c3e51640c180140b44c00c0c405019450550481000d202c48036103650b00720f40071454030341032040c401d44860400c5109405096101141121490b24403004681d4030b900070240c29054503c26400c0352200d07640f071140796550842901c20b8801002003442289000b00245034042e100385822448003500700049145445958041c41400175203220229941c135003808008505078002c0c0c10035110700310603105c072a52101013000c2c03000d044c200b0030380c0390200410304007270300602503101c0783c040410079600e01000355107800449a1a02c203000e42050171030300511400407102250016500d154051342541c40d804001d20001d0001c405000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 657710206 1250 657708956 657708967
    0x120f0a141303120f06030c0b0a120f180b0a0c1103030117070b04090b10050703090e090c121e0706090603020a0318030f0801091401030b130203030d0603020102070504020c030a0f05 79
    0x705801348142a51415501190207895841d04210741c0e10242c10180f45c0c1c4e0403e201c0302401c6c03640041942d48446a514002c03540f100ca1099920090280d584130869900c44107105005203c6410000340c080d650a00c02000781c80240d001c100e81c51500141452601c0d001000100420f0824402e03120060341044c0944480c0b50b940c0c400c038101c030752180c0d002c54207880d1104940d008030b00d010981404202c0550a20034504007003a5401810440d060050b0552101c5d880041401c10030100b01d88d40003144c3c082c1801ca01055842021a43c0300301800c1d00341203894003102035201c1040081982d43c204d07003040e155000c00d02d00380b038001c1d0080e41044860108250351a81200c4418640005d009440c1e40680c81e60451000000402001e981e8141c00c680c46060a044032020740c095507441c0c11b41140c3c1c00ca08003060319103e81c0b1145028900349540039600d84400702d1800303482420381d402081100d100340c003218921036841042c4801c1e030180d84480e0351070350400e100c402d2566000d200c407007410040303a03d0b20902d8075 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 657711456 1250 657710206 657710237
    0x3080402100201140106110d05030601121a1c02030d0c02010206160219120e012a02060d0207050304150e0a0302042a030204080609070e1b0906120f0a141303 69
    0x13426031042d8002110a00304074120b040178482c5500301d00091801c0742c61031800350b0010b044500301400c4040d8090761000c0950000003a80213640301e10b1001001c042007401c6481c20040005c6c03400d101030340b01c0c1c000c3c540211804d900591040c1c0d01e856040c0c0207401159110908042d403802c80a01c54429400b0726a00307070f00051581c0c030640c4601c0e48a41442c2c00c0ca60900b040080400304460802d60501c101d12000c0302015221981c21035100a10080541074030010b40b0114002d070140041040c165070010034040b01f08030000c40600190707001c0080505081d03020803011076840344803c10103508500c28800500141c241600502c6800203024089080c03140301d0210f0345240049482c00c680003940c003040601400e4424440c003a0411040d0000300a4035007060340401c42007202808207030050340314a082d014543c0b080016911950b40050216460380c031442100201c8500c200c0d400e07109200003000140f500c0d681481000c030a5614010303500079a5032120b00710480f0004400054040c0000d10740c051080c0d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 657712706 1250 657711456 657711491
    0xc05030f0d02070b0f090c041109030712021201050f060609042901090b120c0a0c06090302010b090f13020111250311060a080610091205070e011203080402100201 71
    0x1915030040c01a5100c900713090046825402800481031480d0920500c40b24884c000382d034940a080850b000035110030704131b080c0546449404000e64141c007412030001440b801002c680ca402c14000e07a40301c034110300c0620450b400c94504a90b6202c4e1402c4c800701042103401d0010160a032410042c000040042c4c411301c02e42c002d0803483c4098a0400c010040c0c0d030b00719591081d400c0004000403910b15080c180710222002c0c02c0c2500405065801102058124140d4846c2c10385000490304002c040000c07045606000b4040c1040280890207881c001000c9035401d815010344510a000412400b04a0a480c0c3d004640d100c0070408031510a00c00c5018591001400700741080250360010303aa03190441c618900b1403074907072403071140910030349060100300e2400d40c010503c6940140101c45400c04041070f29015105802d103078001c503103d44c00840d0300300e0070003a0000304c002c180d4075414082c5a00e42c5c3d039107181d100c80014081006000a140c0cc01050050415040da604403000b80e000100728003281d00d081c10344 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 657713956 1250 657712706 657712717
    0x6020631020301090f120c08030a05090a0b1801150810050402030304322b030c060908032505090105030c090907022b090e091509030403061a010905010c05030f 70
    0x144442071003056000c01c03089003150110160751f03090141440e85030382c40c0d102e45408010f062807282a100d8002461b60300060040d5103100368450000c5001d41017401d92102610300c3c00060001640c60301010104030740c014605501200c040800601c06d0410b2003038804050a0042c20407a05232009100204000c0c00d007103240058180749018468680900c40c4000e003081103060b078510f00a19118040707454400234151045100810081c8840b010941c45c9000c84142071040b5000e02010314058012080042200096002d070607020705200041900c101c144410480d03500c99000801d4007000040f072994040c60141d540200c3c001c208605080c5071501007002c01004552020041c1c01000d64400c101c1c00d041e82c00070005a42002e113550300c0a41c410003900c60300301e074010004200340f06070002d1108503040011102001e200300d503544841c14a82c011941d03d402a000483c0d480c0d0030300824101c0500c00081c40910080140d44400e0010302d460015100802180001e94250100300914804003001e54001c15 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 657715206 1250 657713956 657713963
    0xf0b100302132402070b040b032a0a0e01170702060a0b0607060f0c17060a21050723010206041205130306020301081b0d2402040905010b040f0602063102030109 70
    0x8503e0f0420100083c14203100d50010241e100d000c3c04144041c442007405c0d20750200056003511016001c001071041c81c0c20b803600d214024040300003048a0343e00d6009040c80e41e040003e0300d902400c01e00c4072040e6014284102c42140050340f00000040c6a00c2540c0c000d0200b41c0005801c1c0e51502a65480307940540e00340000078072010ba00d60385940e45895000826400601c00344085040909141d8005290620f5600c01e6944a00808403102c40100300601d08a41443e44042210203285d03445c102558144141082c1c0241103458818100781c55001007025807003540e2080007a400f201220b5015100fa0b04540058185022003060200000300c2910055002c1c0110f500188080c030100001121004503505000d8000ca84518425000840c601c42c000740485034103210f41504200807038a0030003801a0351007041e0950515000146400004c8000c0003518000d007240030b0226110082a40d0350f40040e50306900b06002c00c2c0484143c00007085468a011ba0148012644240aa0006030a40d801c00d507064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 657716456 1250 657715206 657715259
    0x9040902030f071707031509111207060e060a1b0507031502180103110a0324090605120c030a08030603010f0e0318010e060a0c0c05030706050d0f0b10030213 69
    0x51004c02c0d034002c009076001300428010554107003180d0364a000c1800d948001c800e1151500081000c01140301202000c4e40c40207410745090041003d85540d480d0f02034031a00c008614400c5280b076580c1400d00c05c80300b40807150740341c8060480f803542c144038100201c09010b4400f801000008000202c0c07111101692098800c00941c0b6140018682c80c120200e04074200d0605140400070f002c0501d29030f0680e644400c040c103001550303d0000c511404083c02006102d01d5022400b40c0c0414141c1081d84103402f608c400340c0d0365217424404120940d50700d503d4204842da05a000000d00c00002c4d940400460384000d000e8004101d42d01c600e188401030710000741c2d903811650004690207145103001c40508160714800d18080f40340341611000f040c510b12400328030a04200c01d03003421805014200341440001c20000d03003110320310b03903980800034070503007180012402e41d90424007130701a011700a0185520b025001400e000c040e02c2452410b40013540051400d08071000d0040c00000d41e814155102d020301c01041a40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 657717706 1250 657716456 657716459
    0x61303020105090307020907030b030703140a030e040216081803060103120e0301060e18010b0604030501151202010503011403150c030106090905010f090905120d06170c0f040209040902030f07 84
    0x80c0c25103000a010b0443c65005008820250b920a05025040417040c100040e1445124022900b001425080980807100c5040710120064001468000880c044e079240c0c4c040c2039682c01000309900c918071580380101c08070080c03600840c001d2030040070519080b2a00e503d1100c0f02c072020a0810000340d0090314000f581c164140440d40d0005203030055081c1c1203000304146828410718061080002d003101703200010710800004148030950025802d004002c0c00580c50307590303a150484c040c00803000140e8110410071000140340300c04101da00410b030383c161280b50941c0e003080109030715024180b0001c0d51512402170302208080c2c141d60700d60b015105064104c0d6481d070403c01c029000188540c020203080c0c0c540030040143c0c0414210030b5065070700113840460710a400e414024640013015480d030101d20f078005038183e60360210b5072010046500341424003034200e0902c55000d450b5207124440b01e8111180341c03881c0c0000d141960080607854401040002c90b5140d0b900802d00d03103502d20804504982c0310650 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 657718956 1250 657717706 657717713
    0x90914040b0609131707020d05010209040c09120b130605070809240c22090b0f0405061c14031b010f05090d080403090e130209100b16060902030613 65
    0x12164003034803d4602c003180782400c0c1d521038003001c0c0e5510702401003944a003500c00030440340801c42c1c840035002044410025500c0c28418000d501140b04544110310786800d503400207004d0340c2020101c1d90340003030004088946848118401c2c400601c281d2038407040328050400a80d0920035107001da02999a0040e482c030b0201c001c1441c1c00d102c42d009010450080c102030400c1100d00e02160390000d1004c0b599038440d10394018080d00d441c0101308111041505110109100340990700c00e6108440072154011801401000d101c00c4440982e0080c0d0002c0c901c4c01180b0000d840b221081200e0352189401140305844000001d0840c1c00c4030442400020b0844802000060309010386002c1d030129010800403410811110396581c1500b03100201032142c0d603000903013414011b004c981d0040450649403585845e0902d10000042c42e8880120312584d101070128500c40072219a41c0c00791000c00030b40c5481c1c00710103040040d0301c1113881003c444207a00e4101c2031005807400d21040c2d01405c2c80d03503800d0050030a00d24 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 657720206 1250 657718956 657718973
    0x603050a12091415070c06110c06040605040504020c0c040218041103150d150504080c16050303040504021c090b01230303090103020d1b08091b0312030709091404 71
    0x11000c000300040d02905000350060f0070010840c03803100f00d6550350307500113506480f02c95000d040e00c058807a00d81d00c140080c0880c0c0159064038001d00100c143ea120310040801c010706405107014210020344203200502aa007007560040c0707003202c04030b003c40f07224500317220005050741e00610340c00f003d00250404040940c1014000c1041c0480000300e502e05605c1c00d113882c201441c0000220b00d00c54801c0050314000d01090040650704440042024002460030341040309699103d04000c40c0701d446540c0408000c501e03031850310816114003c0c00b45140916090800003e90090204192580720a0030b802d11060300901c101010703031780710f803211201662411082900d411304541c1c00041d00d03448136402e940c166074044200c03000c14109090040e100c11040304050000d1818055040c1d510b1840510350260340e4100340b00038800d03000c440894442d1a034102c2200b80503203004800c00c7d01070344800c2c0c40d44180364802001c0c40e400b02c42c41c5131884d25581d840d06000103481c04001c0c07a0001c058440148401d001c290f8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 657721456 1250 657720206 657720233
    0x110306090613061e06020c090a0c0903060c030c1202030f1513021b010c141611030105070e0f030c090c07140607170c07020d02190b0a03020301050f030606060703210603050a 76
    0x1400a8485162031001140c0d0f54000100322703810983d0f4070420705801900070100d40026540003d410000d83d008050045c00406c2c2840d4448081805400005802d545078000c803841200070744403001464407000c1032602c803000d0b952a40b9034012810482e0700549038061018240c0c88400140701c0d41c1003d464088a421100014565010170130b00d9989041030902c10703401c4030100b103421140304108004904002c4103a01c42039110b540c1c503508003024001c030300f41d00041060301502c0c11564170004101d0b800403d0364a446c0070017040d40100102c00050701407411007000d4501c071802501018550b810304003846d030610f170049400c0c4000c903205840001c04d803400052050f45c0b02815455692401121360000f40d806248030500170b10402660212501030201c1800180080c6140c0000c1034480e00c0a100103400f030740090192074003ea000b540305844516002803184e00a40340505880e01e0b08185031003c032181000311500140d0003403061050114030305907102d0314008501610281c011480940b5116910742190b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 657722706 1250 657721456 657721469
    0x1021c0e0a061e12090228051f0507050705280f060e0d1401021b010e030708070b100302060409020a020f06060a06110a08041d0703110306090613061e 66
    0x444003d090603021118a19481d05024100144a010300032080d1000e0051007030001d4011152039110019102c113200c4600c60355003c80d1610000548070800d2207070040d032200154803680482c000300000b82d401803008041440c01501940d80d000d466001050f03009886c5090000b00d195000011100b5090100194001d4070b54170500b01c40721441d05600a20684c03002d868540b050502e0502c410400c808211880044e181c0c0d00000e544607040700001c4512032642480d1403a85500b04120819800b10220480b01001d5010401c2c40c1070000c0d580307691607088801001d981c016440c1d4103010025940e00c80150000785900000540da5000304000203003802c040102c1040d071035210070b003480b9681d540c501c1e40720241c2d515031401c0b050100000d80d00d146002c0d02200c018110341c400007000300d0011041c0809407480040301c001400203031030b102c0741201201c50503200703440010010300100701c0d44d150040b6040e81004005148040001416002d041240c1d07030365110403400720782210081640c0a00c40e140320018041c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 657723956 1250 657722706 657722717
    0x60d0c150c0506070801050f0f01110607020f0c1207060809030705010501260d120f0f0f0b040c02151302011110090209060f0a0b2227090206071101021c0e0a06 70
    0x14100200c8d0029064446681c8500c0000485102c0c0f64892184610071102500454801d42003110000e5110b00c15100480d00e00e000e2651001602d080290750040c0c0700c12a10001d100c1c0929042d0101e4050601500b5400307503000801112020903c2405480e018203902079086044000e02c52601080e030454800c181619044200c0e2800c202d0381000740e042e01800198400714142c0c05250b2a00014000065901d2440c0d1819110303a0443e6110740c000c40c1e050380c5c00d81e41007000950411003a0f96a4020700b010040c011a1200021290404d020703030140c1c1c0701c0c07040c10022182002501d12900b05140000c0c1400c100c1ea4552200b82507181652007150409410f0300d2000120340340ca004145a0702c40d074003450050460025550102211a803280440702405281040320380381c0382c1280161030340b10640500d000030a40c804030911980c1d584609849568020700d410710300090b9030784000c90b529183c40e035141540500214001031080d069601313551800d1950f0b82c1c041e8420000100700c100c0b680d54000310100203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 657725206 1250 657723956 657723959
    0xc051c14010b12130503070b040c0f0803070c09140a0905031c09060f050606071e08210a1a011b061109120c030a0f0c05061b0123060d0c150c0506070801 67
    0xc0d17000c0704503050741c0e07080211103007556541d040088481c280d0394001c1d003207503650440c000f074105c0f0044041d2170254468003421511540c1d42c26100203881100c0c0d0021000030100000c02c640400301c1d880305010398494400c3d00d04124070800341d402466005607140c0c4034240c40718a01d0003081114411301c502d003890700b001002281040004901d403806203403002401001c480840345604140c00144004140d40f003000f1603960114030300e0382035400100c1e64640c0e10354041c0c8000304000c42d8407401045150480c80c10005401440e103801105e002141510141800820040100104100e40107502481d5101c105250f130b20541041405045120801c1141da0358120190a40d09070345c0101fa180032907500156040080301c42418400c041c3e110660016500c07480004d8120a600c01d203100c1d80c05ca004010f00208a842c560610280d01d95071040c604144100c1c19600042480c9400d82814890034000c070080180b1a4440004400c440d42040c62407010540e24003859081060403c4184c0d4454845e1070f1565265 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 657726456 1250 657725206 657725213
    0xc0105070c2102040e0133081e06010911070201030c050d06080f0c0103090c0509061807030f0c1830060b1005070503040504020304081606090c090c051c14010b1213 72
    0x40d0010004945080c0b48810b000040e00300350790f42e103030150111100742d03202c05a40100384031509809d05039017190f40c0034080c0000783c00c01036485603c074202c0e1401561460a1280d50045000745800e417000014060280030540c032042282c49110081d1103440010100c81e465500c1c4503291889400e105030400d410301008000180a50801c4800c07108251680c0986884010000b0300b6503505c100e01c620f5482e00f032420015425415000a114110354020810095030f00341011282503411510b0080074003024541005591820040400d107211010740b0b01e00083c0380070482c80702031a00c3d40000d0310300540340d40304029036242005400c6e10f02c10450904624200c416580c05031039024512131184110703800300004041c0030900e0304440c00f4201211514506000c1890b104000300202401500c07401b222100c00319550080e0301c81c045c24200d0740d44505003412206030202030098181c3d0020190542c0ba05800c400c0024211034090103030140e0950151074540440c2e900041b040000c150300801640d004124022 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 657727706 1250 657726456 657726491
    0xb070f140f04120204060806130b0c03010302030d0c060618020403051e0d03050415050f0709050603130b10030f120e0102070b0301050913020307090c0e0603090c0105070c2102040e01 80
    0x7110843e420038241c2c1226400098011321045c0c1c0255014080c1004000411008000c4c0c042c1c65842840f0002d40e54841d90601c4485002c03d0000941551194120f0390702240140d0300040e5240c451040418115154040d044020000c0401120035503004070b014420440d00344000d4241098403a0038031011b44042407010f544001041402c01030664500118050200081c0075460100fa09e200600490800c9003206042d0ba1007200d445002600410022500b481d20305c0407680943e400304000491354550b6126081c0c0c141015000e060030300380ea1b990010020700c4031411040307040c1c003401c014040107145243c09081c85400ca040d8078119000003a0500c4140c180006607419071300180c505100d580c0c0e039440302201c0e119140300003a502d0712555500060340e81080c3c025442440041d0741c2d03003c9214642060004500058070380e9046504040d00f2403c0a522482c064001c41c1d020340350310340303000e6900c405282680380030485c905007101b0072800c0c031019400c1c5809140c0740054100000c022800c000b0105048 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 657728956 1250 657727706 657727709
    0x71a07091205011401141201090312020c030403021306030b0c0708040303030b03010f0f0606030b0f0f090403050f0a08010f05180f06030a1713050306100e070c0b070f140f04 76
    0x60040703400d001041030190950201d9050041e5400c025882c1d6194007100f200740c2d16070b0ba40240300390300102e4040440310301805140180ca600d6240c108841030070585010294210304042c01441c0300600000000d40d0321091500c02c0b2401407100069082d003582040c66206000a140b5802c3c5142001800c00089201003240c007203e80614000500d4884100000d001d03041c11440c9001181c2403064943c00a083d95102c1d07411200f182d02c1c1084400140ea00740041004800310540d488802c1004000e081e0414165150b0710a21130328060b89481c0310308034011295080664800000340800e001480b01c4030701d03555004060714007224400c07503109426032140e00d12480105540c845107038000100d501c607102000720428065019242d0040246014044e2103207422a00c1401c0e02d013001c0784000540c504010640c03d00070344030b40000340156414040d81d4124643d0140c100703010040b003644c144002c5a019242140556055542c8051f0040c03007160040c5a002000950740b820f43d02089604c2c07007012000103d40 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 657730206 1250 657728956 657728969
    0xb0906010e07050d061205070905070311090f04061d01030309172d01060e0f01090209011409010c02040e030d0c1b030e0a0b03010b1b0c0603010506072402071a0709 72
    0x41d80c52801031302c942c018080e2a40302d210300060000c18007040090105e4541e042d0f030f4440c1000c00c0795940b10070782101901d500b00000a0586c401708a03d250354104018100c401d00030240021844603501c0c0100303203004000140d4482d1074070b9020014001c25500c2100d500042400031450110216207229940c2c4904215070580540c031070b110180c0c0c08010b4107802400c2c070b0f03d28039402008220399030054074611010441c3d007c0552041100045458001d5100b030740c88810040c0d4580d2100d041a041c5040c0076805001c90390306000e2900c41c01d40041e603d500400c0004140200550b40300c00d40403d6100959898969010910100700030b00080000d11805030f100941d0589002030128102d1404036914041c542c0220f10540307400000894102c160300c0c0100341c8020207020f18008004140001d0b500c450b100689036034001000c02c0100311030300c0e1440c042c02813240603141d500580c0d45040d140d0021b014803444020705158011501c1e1092158079034400c89288003009025017180350000f4024040707221802400f = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 657731456 1250 657730206 657730217
    0x10f06051b010b06190e060c070b030a0b04020f07151a04020d230609010e0403141804060326030411040c050d0c09030b1810020a020a0b01120b0906010e07 68
    0x101c1031108250007280d94104080d2026a9441e50000014040040c030010031000c52455204040a400e04404452181c0001000b500030507041070384490403944050039880034540c07540f42c2c051312942e4500c01064821905010035039103001130300d88070680c4160505141800e0b03103080091004080c6030307120a5100c90382290b006076202d008030b07003001c0100502862400c40300d64000080300c04408902c001030244401b02d8200c50f060307a8490002c814080100d6000703001030722101031740d1617202c3e140b809010403e00c0d4011001044a40d60046801c90302c0c2030348207681c8807040c901103440c259171009141d540344400c5a0160724501e0035443c3c100110326801925070040ba520b416000905100d0016100da00c815071000b80085030a004008000507006d000590701d91300c0b0880801e000005c0460000740c2c8641c000094511400c460300d201e070003034002480a000790300659a034240040d00b030301f000e00e02070b0203412070035009241c8504080203441402428441c4560100340184110290403002c43d42c00285803810 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 657732706 1250 657731456 657731497
    0x80f090c15040b030a1505030a1a18160603050106140712141c15060c030c0212030c01021306020304030309090e15042108060a030f06060b040602070e010f0605 70
    0x5010207100b15403001003240f001006009a50b4043d4008a08962200034002891a200e000301522a5600000100300e0890801943c8280880305001c035031140c00a0801c1a00d6084004850f044c0984409046c002103800e580900096070940b1809004d0145454041a102403500180503244240705014006440b141140e00300c040c1f14090500c0c07000c0c40d04103401c0e21100c02c603050038805242c0c1c9002400c03003420000c1d81d40180c14040b03444030440d560b90f0703512800201291002d80b1040500601070f40c01004108904543c00c404000a08108881200040e40c9207038800310301c200c50501d504010b0454000b00000c10100354441581002d0750306807500041e03814079001c40b031440d0200709140304001c1085601004140b11301001400450b00c03402c046000785905691080f80d50190482e81580d0203103030440180040743c0304603081060a07110300000200b05484d2070040c80ca0703820542c000c10041c0e210038006c1c88148640003805005007003059403404294241803016086004000030541c54114600c0e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 657733812 1106 657732706 657732739
    0xf0a0605070302120702150c1015080c0d0314130906030b061801030c0611070302030a050303091b030d0302090f0904080c2a240406080403080f090c 65
    0x651010b42e419040d60800e41c010511230222072241c41c4116400c02d01c54805c6600e400507901e003681c50145071070b2080e894001080c4000340207180902030303000042e4008104e49410305540d000980c403085c880741503400d40c00f0230f5804240d40b103003400c1e00001446022200f0900512040d2880700c4074880c0c00358415034900382844001d1185150301e808211892041c4564030080840b5410f48408690303d8001034580500c440080e281500300005000c082242000851680030520340521601200d410000c0d0700c8500c034a031040c080c150001160141661440c02c01032994a00902424281c105801c00041d183c2190690402030300c110014109628031440781c84c1c004400d407840b143c84101c0c5503c28490480d4981c0481012881000503031002303004c0c0c01c0040c1001c0c141c9555400c6840c6044e007001052400c026218020300703842c0c01c0174400584c2001c559a0300c00d940076148403440286040 = true := by decide +kernel

theorem cover : BRFrame.Cov 657553956 657733812 := by
  have h0 := BRFrame.cov_init 657553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 657553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 657553956 ≤ n) (h2 : n < 657733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
