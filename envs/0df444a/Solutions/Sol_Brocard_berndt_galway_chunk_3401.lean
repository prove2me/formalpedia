-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3401
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:33:46.576021+00:00
-- url     : https://prove2.me/submissions/59589034-1d48-409a-805e-f0fee7ae1039

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 611510791 ≤ n < 611690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 611512041 1250 611510791 611510827
    0xd140a0803011509080105070806100504080601030b0a140c0901050a0c1b030b0a0b0306040f06150e0a050609040b0402040903021c09031203020a0207122d06054602 72
    0xf040c0052200c00300400c141005101b107074020811602c03605180c1e41c400c801c000702c001209980c003040003001d110008140c0303420841c0c1806103102d94000590380c500b815404084a40d101201c0343c0d40d90070801407004041c2200c0846400034820b28041ea03960141e14419501c0c1d0000b0b10009200102c1c20141c0000b230461226180d06481c45040540002c0d00c030303a0041001d50750071038411649904800702080c0013601041c41c1c5885035101d5070002c0750703816a1500f503001c12401980418080e0381220b040050100482c03081a03804441111036066504250b01c071200c00000003070009015a44d103200040516008005840303100044004001400c50f103801d00a104480c68402100c5900c1c000007001c2c0900c0c000d00070f035003c6285075801080c480c0e00e00841e461000c00c1c808001d617041000c104040301d020070450161400c403001040700240e40b0180789030a0b03007100d0b0000d103411b441038074803103420003201c141c034684280c0e840c80461062032190f603050040c101103020101048000d440002d850341c2440c948010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 611513291 1250 611512041 611512079
    0x9061306021507030621140706050c0c06040608070e031c020d020c04090f26030a021909030b0a1a090708011d0115030e0c03071707060c020d140a080301 67
    0x1480c10b071074a500c5410303025a80079008a05295025121410300212040c40410701d05004095955541c03440068203402d1081640041c0700160340080c1f00080c1c7e1000b00540c0c2076042096038034924140c50301200601101d405071907a010030001d1244501c19540410204203125040241442004001c44000c3e5883d840d075291103025010315a00f5031402e00d4030740714038010650841e51600b583c80e130f250703030780140342e00705800f50103081c0c2d00040101050080300015500c514207140e00166900c00c00c0c1803940c00700d9207141c17000c4100501100c1c140000b038041c1c904560401404c6501051034462070040d080ba00484c0601550440d0350a0100320161b075200e0112030403625462440181c0032000d02c00000c0715403090080741d800c44089210b4035007451083e40030100c142070802c182c4030f440d045180040c2c107103415a405903c000d116100003541034203080c858140100118201201030482d107a003c1640705010344805800114901c0c0d00c4003104000307010039001150301481450b034968441d80030000d10a15030034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 611514541 1250 611513291 611513323
    0x71a060109090509070b07020d050703030507020108090105060d060b060909100f080f0c0d020f060304060f060b0705100203061801080109050d050324012615031609020906130602 78
    0x10004142505104541c004c0d6044005405840d0512406651076030000d04100d80040340300c1c2c101d901140c002d0140038051442176039200d0f503c1180e03000041046002070608000d40e4541002d000e1140c2d181d03003120442d19808540400c142041c000040c0c1e4a0046501e8240c20002070000c104030740a85140c0002074401c0041d0078035926448810284d5500448044c0030300c1075000d0800c850641c900003400300e100903c024000504500390802186241e001603808075500c1d5110594035812032038a0103950083c0120714016030400c200b03504c41c25640c3c1105110f10400c2503001000c61490740b00e242412051900b0026130842135603444403024000d004c2041c0c15207880c002d03003078141c059900c902c049a005131441c0005401c04070074001c02d018081e501c48000e0341480780707082d03113050503802d2090b12031414a00280901071a18006000c01402d15041c0c0c40b13103100360044010048140c0140c0c120308190352105000603180c03940388000c0384082c842c0e0402d418240c807080500054266000980395400760f4408 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 611515791 1250 611514541 611514557
    0x70602100c030905030f0c010b040614030607020619090645030816030b10020a0201030b0307121506030204020d0504112d01181d010b0c1c05071a0601 66
    0x3440032400c0b9451540c000300304e500100030301d4540c840240081c003c2c42c1c140500000c1d2445031000010202c0b030040d485100501c0a000c034080407440c0521040740e0101e1303140080c04a515103022001004440c1c4010111056500c418000501060f030b402000c2240d5005d4400708200440030f0600341030151044800d000d10000a22110040f02d10110031043c1603258940480b00c3d101c00d003840c00180c01180e40d00e01010740c0d401040f240782d40c45282c4000c2083d0141c001d882074210a00004045e59a48841c040c0030703900680b0100300401e2640c41c00682c007600091180710034010644203801403c403560000e5800350000c00c11003106442c0e584007901852154151810480142091007900d0041001c03041403800d807000c00402082c5d50521b044101d1a05140219007141d82207031807510480c1c2500450341c2450241c001c6034400003400005400b5100130390095041000c2d0042160b911040c846c3c1da400c40b0744010035502402c1d4015030a40390000d910403651710085044800c20101c1480c116074160006040c4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 611517041 1250 611515791 611515811
    0x21203040314070f051309060f0e07060503040f020f1206090d080906040f0224220b0c070618080d020606030601050114070f020117250504060e01110f07060210 70
    0xf0441c045450110319000800d02d04420044640d01c001c480003102512024241e0005a03030384211208000c3d400b20015820b16400c3c046403402806401490501500300f045c000440d050461500c40c440d8119489650100d100000c5141a810465003282d184940b03003c6c040c04001c08144c4003c00c0080341d0b2288150307501e81500d560350b140151005010303418903614110160403c180c0c19144030001c4400888065280c1f00031b1001540511611880224010841c4400c0500c425480000f0040000080e00f08021005c1154582d1440d10540d81032010455644100c3e5480c3c40c0c00c00002c0c05014255015840307006400f03921540121007007440707030141c4000030a01d580966034011502090714442810300d01240e0f18111200e989d1201a4140315003c2e80c100c40003200740107070030320074030007a40c082c1003a00004582c0035000102c417039650240003007440203000310b540c0220200c9200c0024030300310884011003128103040c00a9914000d0700ca0107109401301c1c0d80e940004081d14240c0750507104104d28498 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 611518291 1250 611517041 611517043
    0x21050c090f04030f020c0d240902130b0a0b03040501020a020c010f091811070309150305160804060e030313020913120c050102090405040312051e0c16021203040314 72
    0x1040318040780a4a20314007060100303208a14582d40c0104900440c0d280c08111000668180c03002c0104541c10410610718400c41031003401c000303100810303007841880042c51130707800100944032404410024958034485d80c1c81ca59a44200f03d4000d0401c0307103405599080909200d8041d602c41c000d1480503200301d07940060785502c10320340c22441802540d203040c03103a404d248220510105007485100e00c1901c034801c0c401d56045480040030120300ca502d4000c0118034089041e0703d0442c903411820103162a020811013500c07000b00301c902c1007a4091400d08100d03a40c5141c168001c080b044411030140c8008010060410850205080500e000b120010138617940d004155174649090310b4002c081038031030861601141d0050040b1400d0920600025082502440104080f60011501540025120010b000140302c0ca40b090710740103a01c42d00c4540250f52200c1d02140b08d4400600850407400300002c80041000e18090352807a200d900502d240c0040c0081001103582c0d41190000b42c40c000d1120303103600f0380804 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 611519541 1250 611518291 611518309
    0x50d0f0902211c030e030406030501211e06090c08060915060a0e040f0f030201020301060f0c020315101205070602011401120b07030603150516020c030601030204090c21050c 76
    0xc1c464003c00c2001d007110211240c1c0c0e01c02e488140309040e11118407028100c8248040c1014100c5503500150b20745c075020784021183c50220b061040f54407086510300200783c1390070340360b801c540460881881180261a00200415280c07d0240103007100340000b040114010407040d000d8041481121081411007a050001a000750390455201c9110340040100701c880c04165a40140130b00d104600c1c000c05900c808240354105601140140d6001005102d50b681010074003001118628100e4010001079002caaa45c07080303980503800f19540c90001440450000071004040c006541d0301019081a03442e180b9901d60700c1c2d0080030059401c2c81601010248030020140c101d5180d54014003080300c01d901e54030725154029043c80200f5440e010040003243c00e003000002840c00c00400010a440e01070625080c400f0040d407a034045400c00180031a030395500082c0f44e81500d8041301c000a00c40c07028078008510b09003e900c0b080309182d8624610165040390414144114010016074180d40d50303e2041120b901 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 611520791 1250 611519541 611519599
    0xe06010503030a0c0212030c030706020a03151203080903040f03050c090601031506030506010c061d06061f030b04020915040603060b04060801031415010803040f090b060415050d0f0902 81
    0x42c0b1003041080946491b40c0400304e07029480c819240b4045514400da4159400054203440c281e800141780182d0300da1620540a03c1080c02c2c87d0300c8181400e01d1109499014880f101404102c2e4803000310b0070806007401120018168403c44801e8503544c2d180c40c80e11006c1c1004001d1142441c440011000e50180c00340030400c01c59194811011403c0800c10f600a05020b80000d04028249a68030b000881c47c4c825135100f00030f43c2c1390102402104611540c40c014009084900680004e9241c0d00c0c6c4510352100716940c1e203040d050109155001c0e101290081c002c036806540e21149807400380c1c401d041400001d105072041641c080c484d45880f00065105841588900ca0000300301c00f004001050b6003046200c1d00c0c01c04a0156010b8482c0c84882c00040202a00b01c03003d1500f001070304001a0350716190000041540b00d00c181321008041d0b002880d035001d02c0c0302d15940044030551b1401003030301c61001c403905080b0741d0303c04100503211514420700420b000fa50480c080c1003c0c1c3c4107140718000081c0d58840c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 611522041 1250 611520791 611520797
    0x606031406030a380103060b15092b0c06090f0806040807081b0d120608070e040206040e0702011a01021504140102070803250908030904150b07060e06010503030a 71
    0x240c01c940c1c1c5070074145002a03442580c100120111401d84d4a0b08207041100d43d100950300e400710350460510710212407044a2580c41100aa40c552000101c401c2c01c0d07602c6a1001c40310702074005110003150001280c0701424110b0107100c04503d00802030100c6807074041c3c80480e41d0b0040019100c44034200b007603840d4010700c001c551042d0000750005194034001c3c40001e1040e0825400c000c078001000f01e145401203401e60710b50f0820040000c460380c0c000c00154035180e450b0b50a0014528141c0355076101c00c3c85026000500102c00c00107010b43d101d85003141c0003000c00c42120b079005e25115100900030204900c205d000c00f00160500d0100b0742c800110f0786200003442611300302584450b40c40e280700c1e60f886448207295540a0040d00c1c04074840c800511b00c107110303032031a9400a14100d90103840543c1d81207220418070520781f80c02d002c603220000075500c203450203a80004020405d40515591180c080d400b41c000d804c40003500d01c041020071b41100d40030445107812900c161341c0300d608064481c0600d501482c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 611523291 1250 611522041 611522053
    0x3280c14072c1b0c0d020604050c06040f050904031b1a0a0905030a0c03091203080a060902030c1204080417031c0c0f140903010c0809070608070c060c170a060603140603 74
    0x5403032005100c0f401c55894420600e0010346500d16070904105640460150300000e041000f400f40603c404c43c2c1302601110079a00d810306140c4440002c440328001e00b4004c40c0038500044c1098060000c8202201034508803441e03810322744c0340c0740028131b10908103032803124050408a0540001c0d402244492a0700ca0013850030002c12072411109031405110076820801803440000300351490300211a0894000e5503084800e14082000d503068441c0790740a02d80c1e0700e00c1001085008000303602540c40411040320f05c0f1200351200d041403201402503811803940038403164528180980004014110b1494401e02c12181d2226211100120350041a8400200b95841c28183c1010722445d200c2203101c049004d82820444a94086421140c1001c00c0002089070700d401d22844510401c00000144014030b4900980c2c030307200314000c250307005441000b49040c2e10351280807011409000c0043caa44c00124980f41d080c0b80024100d0301900052281c01c0c040f900c3d0000000c00b5814185182d44122809001484 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 611524541 1250 611523291 611523301
    0xb07020a0905070207170d02060105060702150d0b06030a0504030201051026070b0a18080708030a0c050c0d0623060607020105031e04060c030b010203280c14072c 71
    0x10103002e00416400c114000c01c84045009040b84039108030403100c0c64020048030102c2c281c003a00d80300041c2c100a105e05d80901c181d00c01030395060f845426101c201c0750b0300340c1c03a0040c40304944080c109001d102a88541c010040100415440d0b100c14401c1d4041e500900091301c0e440540f062414080c0909444180c6001c0d00c0e000007205a400080392a0103c821900700d5990346102e0070941c3c00101c0e9000000d1441d00b645400f95681c1c011840c09007100d14082c000392803038414025580d03c41ca030400010301001c2c00e8800103000c000e1054141170103020b40f030020040d1191800d0001012200384502784008cd8140d5541c0e104050010184200400f402042c540b084507001940c654100904140300722400c01e04c0e0b0300030759100c0c40c0e00901944c4180b4010890402c2848060244e4200ca41d10a0440d401400100c2403070f07400c1d0495180700451014010f0310302503d08021104080a80c0010309490103c20030050740304400a0100e044803401a0901e00006001d440c00c5410450710000012111060703001c50 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 611525791 1250 611524541 611524559
    0x5060702090a02090f041b1106160e010c0b090a0303050a06050f13020922060e0f06150c0a23120a11190302010f0605060a120b0d08160c0b07020a 64
    0x440e2004008141c00c1d282c004180c001002c1d11007c401180582d000e038003c1e01e04880c0c0040c088141c203100070010340350314075105602461116114147d141000b50080c600c01259018071035031389100343c100b030740030f0310510f0302d01e1101e80ea4685009048001030f02c0d240004161003070300d02c1608150b85006125485900d40c8004000004034807c0e680c410840e400c210305880780d45c03401402d150101d40c50108001442d01c43c00c0d0001265020780c4410000c5c480da0042100382505908003542c00303101120b601d00d42c40140740d5a1400d0b8040d100002c4924822203400c0405c1c40744ca8208000200c2d6020b2604d103407203a031000b4071901c07041030a1601c1017110050295084482c01241000501d0444500304c40301d03000c10007100040d88803869002e8016135503400302d00c002680700b0f024002c09003209545c490301d88400107100402c01200e2040c9050326940d50803d0001565401d0103201005400c000100c0d200d03d030b4005500c50616450900311210649444002a102440b07400d61304803640041c43c054460b45814201 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 611527041 1250 611525791 611525797
    0x50406060509010503180307030c151406091801110d110408060609090c040c0f02061f060f0e03010501090c020d08190203180604060c031103060334120c05060702090a02 74
    0x3e06844504050b003804c54406c200087c0921a0180d40e441c02c0e40911803c2c410003c0552444c08102d03036040245d241044441100c11541280094854146980c0c40a40d0302540c0701d10107440003955400c04010302040e00e888800f402c0c10300c4a9a00401c00e4200c9003010b40258803840c46034440641007040069118905106c04a41c07042c440d0098548050040300001c0c200c620400b901408200d12414003001503504110055100a1a840100c8001b404002c0c40850f070320a48690000c0041c50404000818403511210301c0c12180a030090142c1d5031604405006044001912070051154160042a062180296074000d4140b610b0941e030800b0100f0050004e54002015903030249a55084c04650380303001c00c00140302d540141130024807001d0026005060350142207428048800610038803405a80c08a42c2901c595860112201d441c14864022000e010b1410780d505d02d1043c2c1c100001400782e10000c90480c003640710349450084541c80310100a81400358000c0690000f00302e00006207200382507402 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 611528291 1250 611527041 611527051
    0x603020c070e10150f11010902031c05091206010512030a0e010e010c0218010f080318040c021e060f0604020403120c020f132009011704080d020d15050406060509010503 74
    0x1d0801242c81d00f0008500d40080c9006600191940d11100c5e100c6510609844030510414000e0010b0400b60700026541c082c0c8070403044081700074940c022150b40c000c20460740e20090191102da07035050b1100c88140c41e4a0f092055502942640c1d0600b003003141c1c0403044078001c0b5410746410b800c0c00d89140045581400142109061102c040307031210259036000c42500804900c14603414003981012101d40c040f86641c4d07c210303c01ea100303015101d42e101c035407400c4151020050b00c000494409078070040f890074495510440540708400c50402d010200031030603510071450b12a124040b82c032034200b480300b24030035444054210360942c551114001c1c440c010707a018190000b407a041e1240c0380c1d1070003e17801e5140c1014913065540d0b03481c1e00040e000304c07071904000d25146024542d4200509200060400c014031220440802018800282007050400a4661100c4081411503c1d80c2081411000400d8a00400043d40c5a040c00000d100d1901b801840240c407000e075552800d00071200015a400d13040502 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 611529541 1250 611528291 611528311
    0x90c03350a020a0602040b13150210020f0d14041e030e10140a020304060e030606010c021302192f0706030b0105090303191403010e01030b04030314010312090603020c070e 75
    0x7814030b0100341c240c00500050324152510590320001c11092003802e13001270f4001e0b030606840e21a00031045401107141141004100703000360750b425411031030209501c41c0c1c03201c00086501e030605a06c0c45642003141607210382e214010f5400102c40c81c0c200b19568800d0800001d0024001c1c42024149003802d6183c403e50324424100078522410030041c1c1c1c131a0780c11000c0484010b034000b050420025500103005030100c0e40a5020b041caa0810300002890711800100c042c0c003410204440c851b013080c0c2d0b40d040b03d181100030400e1b40030500d110000140b40a20342040510400301c0385511460224080510742440f90044009118180c030701207087c0c02502d80766420b6170501c1402e00506849131014402440410a00130703903940032070740244010b4001c442d42d8002002c1d00fa800d000501c10191514005419250000343c4c0811a81d1107141c01c0b00a0005045880100044c03480000300300011616007042c4114280c075602090754035158220220300030303500e018415a10503441000203059282c01d8580204401c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 611530791 1250 611529541 611529553
    0x150203042d3512041115070804050a1d0a0b030705060f040e010b0a020d14220602010f020c0604020d030e030a05030d1a01050304020405071101090c03350a02 69
    0x30300d909441d907070002241c50481904020840c030480002d5410364a0400e14041e450522503600589481400c0040004180b62540408840203585451407001000c416110741c40e554101c070320703240100d078000740b007410b000b8501c0f0b6001088158800300d5400c04900c00050b0070a156990300b8001e8080d2040b440240e4041c001c0d8031020810380c65910041200384000108659220b20b03000b491401e45205a001000201d410f01403002d00c3d42d80400c00c0044029940f4144079000d000004031082485000701c82806d021200b401c454503180318a003201c040b100c03076400800c124401600d020043c1d11590910354003d8000000103070061520882d01c101960103441d000400c05050000701c0c1c549865040d05485503400070a4104c132050f0b550188502200a9036130000c006418580060706a000250000344182c1d26440040e60261150981e42515a40d0340700170300c8050110304089060000030b00090310042d40285a0701e0000f001c030030401e0b1400c1c64800079403415030007031207085140b0b400003548081180141 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 611532041 1250 611530791 611530793
    0xb1305060f1305090f0114070f0215040609020a050301022b0b030109050604060b030d08070809120a05040e060d08040312020a0204020721030e030405040b1305070507150203042d 78
    0x150400b600654840c01000550b4100403609070702d010300d5160211075681c1040c99640700c0e85d600c5009150010766a080015100e030081d001603090403055841444403243d2542040140a03480d048a01001d0003580c43c40050354581e42414280d00c503921511001940e0b80d054410f40ca40e0031216034480d09800c0400040085480000a0944418401c141c44a40c0306500b80028400a445914010b031002c5005104c0d4845126000d8107141c0300500200078801840005100c1a1003417042c1c00c11a110900503581d200c05000015120b50441c1c010300018450000000301c00341840c15a010445400041190500d131840d07071008104240008044214000c0d0480e800040e201c42c009400d0061107a42003203051040c0d000542c03401046d02940301d0415007070400c40710601360301104841c1500d00a480c041891600c080220b074800d104150071914a500e000d041028065000303025000f0b45d0b200c2c81401403103c1022880c1420f034001928080c10340c546988151032080e82c00240d21210b1084040400a21902 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 611533291 1250 611532041 611532049
    0xc2a031c0f05070309050f0703020f011b0203070f0614040506070204050408070b09010b120318040e03120c031807030503251202010902030d0c0f1203020408030301090912030b1305060f 81
    0x585203040800e46800d1105d0400005105903e5020560401403d0740e030715580005ea00c41248101c07803414850055408034141550b40d84900c10b81e5000b40c101c8005a580c2c21341d10000c1e03100e40c46000001520b2116100401d019003007101c1c22680e0061125040400c1c580810001707050284c800c940c0d5050401400001504c0c01a43d079106141e22000001c0100401c4140702c85d80180304070b0651079410412207400155580c4004100e1050103550001c4c41001d540051499403003a921003074a20348170907017004007090002c07006511175881070015001289445502c1ca65500351408010020b8009100317401140d03060070b00020340003051070442c2104010725140d5404031080c0c40b01000c0141d4440e05002c1c00d50a0800030840c6180140c030300a0401d0078030303403500244c449807030714020208829901904141c52103601520054080c00017520742d256034036909a0020f0040301000c842241c0c1c0802c4484c11309019210719400b418001c0c028151000550740403000a003c001c040785d9012003112035001d000e4075 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 611534541 1250 611533291 611533301
    0xf10050a03050f0105280506062b061a030a0213030c0905240f0d110a060215060d120807031d010606030509030406170403090302090c2a031c0f 63
    0x10007240502440328202a1013403d42d08001d0083e079541100c0318403002c11482c80c00c410041d4030002000001c981e10342d040064072a00c9420101a2004075046524181c4066500c6400000844442c00c00c01c2e10383d00c07824084001c90380031000d8240d920a100007014072607144c0041c070184010f4070303108060a40703035543c4610b01c103400d82100080703035950341c20846030000c2c2900c89032494030290381900800d14076100107605209042000c0740a44410407407030003000311003a180111040010700c214802c03600e40d04025640c14122240740c41d061a400085003080c240072610800146d042040c10301c0200c0a032400703175000d010140c2900e04142d03660343c400311080880851403603062141000130501a14211000701959005400301081d90003c1004001d031940241074940329010700c5074000b0950f40d880c10290790048903684003030b41201803401048070b40703000000108800d08142c11002c0f40002a0b4103140c2c000da01d00650b0014a500802c851503a00002c1c403070f041c0c1a02035400002c02c9c025851400c070002c2d80c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 611535791 1250 611534541 611534543
    0x60c0708070f0b2d01080736090213020307050d0c05130b0c0d0504050f040b060d060303050702011706030628110d1107030f030f0609020c0f010e0a0b0f10050a03 71
    0x40b40720350030307414180d1151080c0c144d1164507410f10041c80d4180555070b40c0301d58503449009049140e40010390107100d8441405001c140c4098800c01d074101c020031081c0041c0041000892041040c03541c2c6690258091090382d003c4d00f007548d200b0f41445242c80250008000b8402c420302845414041c92105540c0e4000200c040d083c0301034150707103640071080b00c42c0c0f92041c540c07280401d0140500c020b0206894042c0d50114000e402c40c0c2c003088030003042d40420194071800070030500fa24100780001c0103144e0040d00900c00c0c1c0e03200b80c3c0c82e514140b008a1117900806407d99415925420501c0800c100c10380c00d036003603101c0c00e642400e641c003076480002d0210122480c11460b10b500000100720611040914440c40d0030201d10046080e26000007540c0040103d8102081c840a141d030325284002c94900d90b40c016009441901011941c0b08002e215031540d50b8603045903010381e5824413540c080701507000302d003a17084107902142c4401503449840d0003864200c001070201c4900080040c0c001250303074550071000700071 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 611537041 1250 611535791 611535811
    0x180111060a0b0306070c05100b0f031b01020c0409020916110a030e0a060203070b0a02070309030c03051e1c030905030d060608090601061409010c05012903060108060c0708070f0b 78
    0x40c0340282d040c1801c20390000c00d0132043c00b69400c80c0001007100400d00031070003584080700145a2199100207044a03120740e96a9800d07100d02d0348034011141950b41c01c503190102c00d0702195004c0740c0b0342d0108425a03120085c0250030041c82d2010078008100084e00d40038011380c1d4282003030b4988001d1080d510f48100ca10051b07001800901d000141c40c01d202c0c0c0f4a40280c21148065494610b250704c4015051101822036520300b540020b20f031060611502a14000c2d5501c80b000300080741d900e06080d0b554411200c0003e6013407201148415003c100090341141c4481a0200e016032090101d100750000c080300041a0340502040003d082c00248a20032000035140340c1e252030300c1d0b6041c4100b2061900805800000c00d000804030f0b06206524803000303440900509291909030f00034145410740c05001c8810b41c03000c1c0c0e00c00b43d45501c00752140c003440740031b118041542294a242e80e6189c036181d071010151141c4464010030042d030008a883c40340141a1103000b03001c404030140350707560303542c00000b801c0b1402c2d005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 611538291 1250 611537041 611537051
    0x60411060d09080d021308060f040b34020f011b0507060b06030106081902120103082802010b03100510030f05070806040f060c0e090c0c0705031c0201060f0605180111060a 75
    0x1840c0118440e019100001c000d00c0c4c0c91500ea09e914000150161001d40680340c0f890014000c00468200b0a6031560070300364413500d1103180706003420745008501c258000760284010703402605905120704818484001ca4402c448048210305031030b2648170031410ba814603280c146409103512010025030081810741d503600c1040c6091400ca0380008001c2c145412281e004000c03d800408481c0c84c3c031030541e0703041004142d5844510000c411002241440550201c21551035844013a806500c2081d40000503000d03104071081b00109031b0110307401121400102c407600c5a092020840c68940015a941f01d2070032550780f00d03200d12003103151000c00c076070880f000c800c0391480b14100203d9006260421800707003440581d9140901c00907455210040150f0124040480c200d103c2460411203075004280141c02e0f0380b0081000c8042c000b00d81c0c0070801410156003070042c0016162200d00c20801140c2060355441d003056048107191401c61903401c801030400021540340c00c2d46800034401640188000707071001507 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 611539541 1250 611538291 611538307
    0x102121c0b0109081209010c020d0501060303090b040602060a150806010905060a1706060d050715080f101505090102070b04060806030c1e0906031903090611060411060d09080d02 78
    0x10781e0241e441460400c03010b54000c0007058000540c16400c0c02e0044030968640450000490380340240c004003075401134070710300050f0a100c1d043d84100240c0e070190395071007021615855281d460303103d0381c89031000580c0040001000508a139020f03101d000303810103c1c8005140e540728001c0c6004000c0e00121070581c3d070f8205214240c648010004010b0031030944842c00406551801c98960302c008103006c1c010480c20424004129080c840031025000313840320800c94200e00000101910b204644030440c14810402042c1e40e01044420141251420000070410202040c01254182c00c900c03090750641c881c4000110f08400c00301c000d031010b0301c407a036035022480c5400c508040c40e18191021260265000c03d8402254101440004000c1c81c01607031030413030b152191004245441c03a6103000d001c01d5541072544204040d805064041107a030240d69005058030488001a2076841c141c40c000c0c24040411000310301e900340f14018092030200482c4c0002c0402c2940c803440d18a51094072090070503907000450714 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 611540791 1250 611539541 611539597
    0xd03020f011a010906080a0e012c1519061a03040201120e1e030d05010e040302060108010c02060f040305090d080a1803172a06040605060f030d0e010212 67
    0x705541c41490540d1041e12580000038013074807005e018000800044200040080040360084024000c10b54000c0101e540c107880502c14411406c41a005849501081c1000c1c103030b400241c40702c0e101100340308803507640c68242ca03490140110640d810001a114040001d040302c030440d211040e55a540003c0c0da40340703010310004200c070510410091416103041486031884800294048150030040300e013080b00140e80388064a0340c050300c03044840c2d40b820316001040308081e218196015a00c241c080350880d07600c4503000360036503441a100100681c00b00700041c8108010852280e0090700a050051402d013503007000c5180d00ca2030110654140354000340001c4581d1780071044e400720a00b9000800c501070306581c0c0e450100032000144010190012608282303003440c000001401600e034003400c1540365100030b0071544848040b41c040e9180342c030740b03800115641450749424001410040160000707000c00c1405031400b200e0030358054110311070340000b061100b058000400c4480ca04c0003128070030800b0304042d8 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 611542041 1250 611540791 611540801
    0x1903050a031103070c06110f071d01080604080a1b1211060711031c060f120b0106050703020d121b03090b090a080a120f1415041b081003020d03020f01 66
    0x41020707030f104000c0071021402031201141501c01d20302c0c000c0b80c52140212a82d24141d04400c00e1942401000400a4444002c00d98105034021204054140303a0340e5002c04c584802c0c003210003821a005c208006445944034880104c200c9001c00201150503c0d10744030b4a07203200031109880c02050040001e1f1006840030440c01c6d920000328a0454900a516901d01d0381764000d131841040042d15105d1080c05000d010340051000d4400c505c4068090b40e500c480c80798045600c1001910021854000410145d2013171084408898040e00103015a10708203030120b503003180d4050035450b840e80e18001032100b82c80c02000c1a0803a1141d64012449400c0382c2030003e609040130308524000c1c0e201c21000b90000301400c080d1041240036003001c0d1040400d04405902400490210300150303850b02030645010b4800c1c1072200d028a000c40d441c0840000c0f040c050000712803001141041001c0d0551a000780c1c1c1380704051490b4400b156040c000701d025a030717034086809070169500c02c8015800416200d140c1c2c40c3d0911030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 611543291 1250 611542041 611542067
    0x3050f01061d060408010e03031014062d0a0201090b060f0904030804050f0a030c11030109020604170708011409060c130b0901051905040510050310060e1903050a03 72
    0x20001540d4542100a080c030005140c91141c003426030444410360b90f44881c1a58001c0003070034020f21908010020050300c03988203e44a2000341045000801d98440c01d081c86c000d441c2c409488140341c81d00402410312045940c0d074400e80d042629001840180350060b016094481d455000841d894400e440c00c000802e0008000d50300540300740c011a41d4568a07003801c540c000350503040040050325503003425828010600301544162240582010130540d00405c820a2540180c0440741000710240c1010b09a03620f204003c0d60140d020301090005800c86070240070300c1c00890b022078040e6940da4805909540324007c10a40075000c603410411050424042940c2c414052a1201d00d4019000043c0d03100c1902400344425144000c205d8401c030b80d02a001701e545000407805900e0346070009c035070001e0840e88103004d0680034041c1c5142c4030340341c24040c00c2a203000d400d4007118050b09a0501360220384c0548040001507226090f81c03a16004400b0302c400c0c080145001e4070150004a2440c140030f000e0703401e5a94 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 611544541 1250 611543291 611543311
    0x30606140f03030304080a05040e070905131a061c06091a03120d020306010c210e03010908340b10050906010f0809030c2a06251b0b03070305 62
    0x3406805a42c04021650b01075480003c054441d18403210854081c040d0744c21005400e803c0e0004d0011076a00415507004590b4205c03145c0c00d01d94000804103040c0c608500c810000c500646090484910b0310101a00d90915803100400105100c803850304169500d0794080b5076220340e600d010008541d040d09007030b40e8607035007079000301038002840c1007120041c451904a56900307039010001c60341e5603201d00f036003507020b94005080100400e0080f0042524001c3c24540c0c20100f4502d0000c1c0e95181010300a003a90640c200d05c81360704216142900d59880b0600c04080c2031060180c041c143c1141008081000382640a1940707402c0c01d262280180301da0040c144c000700d11644140d010003079183c0c1d00051500303120501c3c1c9014800c9450319000c1d64510f00801d0003c0c1424000d2481d0060340003400c6041a18002c1c0011b01806006468014442c09114050801d50440c1042500d018105100340e00b11120911600c12661080544071484107010025002440445400414442503641c1400303190f802000200d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 611545791 1250 611544541 611544559
    0x603010e1c0305060d06050403030c0315050a0b131a0406021002040b04210204050c0d05060a05062d0409090201021b060417030d050907031401060605090108061903060614 75
    0x1000609000e4000380101c01c01d510340e8002031254690302031000303081d544007206008a0400b854081e02604400c2d44c020002841c01200c920b0a14202c4d1900f403c482c40680980c0c00ca40c103040320309c0202c0d4011310402c003860401910008444641e10900790030803c1481172940c8403401c28200070708100c40b44112040550040c0424081d50340c08604607401c41da8070341c41d44400120341040c1c40e400241c41c200e0195000f8900310800809030803102c0101500000c1e88400c01165032a80200180b658580c000e5540141044c41f0b80c044254a20402c06a2070203403043d0188410012841c0301c045601603000009015211180a400c658040181e40594802d07080c030000c0074420000400c20600440c0308410003928202c031503100005040c0120f4400c0c13200060103010780e24010f003000303036141464481154843c0071078080a01220041c0b1032442654071598800b40342020070401101c0e0a40c01518055101106a00d0750f030b0070100c07003044100107510468001c0740852802c82012148000110001e0045d0509 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 611547041 1250 611545791 611545813
    0x1030215090307060f030b0310022a0a060506030a050d09090501080102090d110d020d26030f0a05040c0b0d0c020f010b031c1812050c062b0e070e0603010e 68
    0x491048181c607401d10f46140c118001708001c801a00995520703d42500906c01e00c0d851200c0103030000c10702d54052808030141030b8403030030003941c02c111103154030f20964000d02c40358000a541d64000c0ca40194004003200d0700810546c5070f160070120f9121440b00811840c01082010a10320f020b110700500000000b14100380d5904d010400807054000001e1000c000c4104c20105696020741c049040c40c1c0182003c2040b441300e252004000359031a070601403402c3c42d00302140051555a085074442c1c0e401c2c0040400540741d1a00d08005004082c0c81200e5000d181d06011030305069038005020f100103100c1010844000cc940b01a04001035002e42c070280d0b9040600703103c41e90f1800101030014000425103e04c82a4054a04a400000d0075941c80b1028281442c0080d800408010034a003aa001e0700c141d0305d0030104201000300340d00c1038860003000c02d0790300940000b00e2051000c0300c1401d03084842010510314071300c1d80d0140c00c2c010950000c0030110b03e820184040380c2001d11038542c0c900d01800003005030703003d1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 611548291 1250 611547041 611547043
    0x2011808030a081f0b0918011d090a1a06040c091a1312141006030f120e03030c0706021504030203120a020c030a090611071505070602040e0906010302150903 69
    0xa101885000c0c8040c40000c26110031307000300705a00c0700070030b44030030740c0900d84940f01e00c03149504c20040c051154656500380c8038560b2095903028101c604407807000c12a42c0016a04601602004214001c0d50140030084408200110b00c140300a419980410b1450325141080000b1a001210207000700840c21a061141c15818040b18245941c50f01c55039454180c803e04a0390303400c6458010680340610610390900b00041c051068000c240c103541a2084000740c003000c401115043c0c40047c200444c859210701c00302d030b0003442509203582a480c10a200401580100b0301d1030b840705195008951201c01c04002041e03040c040c1010303150300c41000300000d080a4400964a024030203052f400b14440c05d020940c001c0e1503604070b0381c4540900d010342e40c4806803114050046c1016100d850b0102d0003588a4003c0e03000d010400f10152451043c240280e071980603000c0303900f07400c02c4100301d496075420040072071540741c0c0181c130038418035500d40100410340c1544180503102c8208000c482800d041404a103400d0780d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 611549541 1250 611548291 611548297
    0x5071d03011805010207051207120e060915130e06130c02030d06062d02060f0c04030501050c04080c100804030c081b060103061a0a09051b0d02070201180803 69
    0x212200a04004010400080d00421404540c051100d5005082c1c80400c003045d006000c0c650302400c00c1d901e81c1d17030041c146501140300354000200324400352441c00d0445801842c1004600c10043d180e075040c801d40720045040740e416881652030f46440450840380c40003c040b9000043d140c0718030030751140e0505101144212804040001189490726018000140f0070000c0d22405e0800c04014081560f64240c06010b55400310120f440a4032140c0406000303400b4002500c7d50b103444c6900524559441400305100104c01070120202260300300710010201c0c6003405807a0194088040040e40c1c2d503d002e8440d4648095a0581402182d2101715000c595030460040c0d54804d41509008071986c0e5180b030b14450300c1c82801c4000038040d035070014410240030000f650f00c0c1a42e1207100200000300c40e092440340c8802c1c0307051059511080e20502480041c0e41794106c5134012070300581440c242000c11200441c20780000854550380341d070226040c1b0035903034090710010b41d074905200c01c050407606051186450748 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 611550791 1250 611549541 611549567
    0xd0207080118150506010c08030f100509072c03070603020d0b09091f021611090c03010f06034d03101221020c01092310050c0d080105130507 62
    0x3c0e55400024001d0790058503e43c0850354031036003950380d902d0104c003a00844102601c2550354851941d5022400341840000b1070300408842d25410110740b42002030010220306001c030b000300c140244800d058039440800c211009401c0303503200541c9031256140100101c3c0d40c42ea00c1c075441000000180210480301007200300c440000c0b140c400781220388290a403000780c8200701022482110490000c8280007403510743c2c04024400701e90f468215102c2d429809031a00007801034003101079403100200841760184d440041e100182c001528000c03810b1006a40846102d02000380c00303000e015400701020f07020500c00709643d2640e039a49a080d230810140c011400d0407503000799034411032000140801d000d001c4400c824a08030700c110b00000c5280340ca900a485500000e45140407910107900440d0200c002c088200300e82046200744519116070b40308000080c00e22000003070a0000c1085412203000c0c0c02c3c0038a08103213000f41c039245101d500d4281400080903050340070f102103078500b209000446a00c00c0c00d4540700 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 611552041 1250 611550791 611550833
    0x10b040603021503070c080409050402010e030a0b131506030506102103050319060f150c12050918010b0721020604020f060d0e06040302010e060903120a06080d0207080118 75
    0x103903580e60b6003924007080e03100c00038007d100c000c1800186110607030440e82c4180e20030798034460000002018195101000c01000b4540d041500c00103042c6504aa9000d110318012266041c24075000101e075800c4400356081a585a04400d08018140280c07080400040c90f81e1140141010381c40400d0390442c6541000003400c008000020034102c005c0b0f000f20303000e280842003003044510f590f0280000f141003c0d1048000d505070400100480314014290a0300c019040403a07404102140c0701c04680f26440320316004d030720171501d030a905980704410710128041c1c0019004241e03030b8007a90401c20982103440040c0c0300714a1407800d4003010f550b40816110f8001d941a42c0704a101c11040d400203807140502422100e11a00d0945400ca101500140d810b020394041d40082004da50142020b940380d02040356500d403203a00c20002070250074000c803002c51344200700710b01c0024910b85030b0001e203003040a00b0305540016445202c080c00f1180c420b00c148400703a8000741070030140d28055a01c4041000040180c0501 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 611553291 1250 611552041 611552047
    0x60702030a14030c09131a04060f2d03060504020a0b03070f11030903030d0204091104050d0f030302160b18030315060c070f030309030b060a0515031e0106050705010b0406030215 78
    0x150040740c0140c41103008000c2c500701200032071b078443d40700501e1040a0311056954072410b849083c01d00d48561003d40380c084102001c0d40e402d100c20a4040d141d0784042d02c0ca800c2103244164964130317401240102561007404080381c0e80c01c4ca0b00400030038004ca40c0040c18400d00400030300001c0350b00041e5100204845003010301a02100490050840c014070350b03215058080088c1603031125445034014010741d043c0e020104052084000400d000d40a00d00030680c220b0740f6a00010301107840c400c10380b03001d98400c0c9400340c40d0030801c0100c5600b03151483d408032400c410340000d0010808404241c00d0741e180840c0000d60452511520342c0300d140c2400042180200700024498030184000d103d000060041450b6010156a83e0324004000e44401d110545090302d241c0d0224400d4034102c54010112a402000f44034a075180860500c07150340041e1000d800e10b42e44e008041c4140c3d200300710450003051180c466584a4090303040850030f40300b040c80b0b02d521852900c501880181c4c1d49070103004850b0128104191 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 611554541 1250 611553291 611553301
    0x5241e090c03070b04060311040501020c010503130203070e040b07030b0102251508090f030c0304050112020d0c200f0d050318030c071a03133c05060702030a1403 71
    0x10900e0441c01003030340c041c011010046600039002d001402281c1c001c0c2e03010047e80842c40a041014020b5000d010f0068001038260742e00c540c440d0020316001780041c1c03544491821584d00003440d21080d907100c603000801b07210401c8140440c010345513510002c1405d0500c12402c0702c400007520f58000080624014034803000c041146207600035410701505407540032071103441e140b620151041900325070a481512805500c030314041404000c0d43c0c240640a0019400c042c03c010040d5000e400504103041500da080c07000c10244400d50141d2010742800b0384482c80d4081a8141180d201420f215000125a00031124103064010005218501c96410303d003198407615401710500740d40e0601000b8001e0303444003040c5612a080013084020840d00324041c0e00400550500c0390408078003045810682c3c40b0311030000540800c0401940d07170315410303110707070606551036a2260b2400f9401c510f09041c45800d885243c04001c000c000c000003a0000c0c0980011418207041c00b00040103003080d288505900305010000c15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 611555791 1250 611554541 611554543
    0x24170103021309060e0703020f060a0212210f0f0a090c0b09061209060907060801080307030e0f04020711030f011b0f0311030405060f01050f01050904020f0708040305241e09 76
    0x1043e2a40c002c0c010311801801c940355a59400460000b130344101041110325a41e1b20b0800100d501c0025960040c21042d0b119081d00d149581045242c002c1125018201041d4600701e1408103108042640c40001e05050001c65120f00308402031518269600d4110340740c01260305442c02404840494850507507480400c004070340c15000b5024495007112410303003404603038100843d01034400c18100080710321301580c40c1021240c0d0103080c4980301180d0410018400401e1003800205120b0f0707005000d031098a007024010400700d0340b06440964907080400a405150b2400b0301106102045100007407055403060b80d0841d6030340049001d0031040c0044543d0540c030080c020b4000c11482c1c1596543d460310780c9458101a07403140f404a52800300b04408000208462038400404408a00103030746040c186035108042c0002507200384450400c0140500030b210024414600910143d4490005032442c40317862040c1e55110040409944c1d0701490300010880c415083c1200740c2442000b800d03040c01710381c85400c100c07 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 611557041 1250 611555791 611555801
    0x80105010e060f0304020d0c0314061f03032006070f1b240b1804110307060813080c0303010602010b13140c0a0e1906020d1103030c0f040906241701030213 68
    0x402c02e81d002340d4000240483c20755115040e81e421000d64096565225900c1c0c044c4598110390b840300340c400c4d10180040391262b00248100002c0312594643d0500192040b4581b04088840e000010070150702101ca141d80107102c0d5550140c4d03203070106010940c903030754291a40403261407051003880009000b20002c844da042080c0d808400f400100c0c59115010201144180448054810701549212071246060002e000d6080390540d95800603162129006000c400c94100c009583e4801c040c8544140c0f034070103100450007000c03e5000060380e261103030180520b0490b040c459114046c80c0c05070320204149140030a075408200b4580a07655941100415103107401501e201c0f0b82c210404032820a50b480c4010051011350316242c00304c0f9100c800081007212010803c4100c131126400c18000b08403803a00701c03800740480b18056100c1502385516280c2c40d0007103807016441440032110181c43c901c901c901003e99018403032400d25002a201d9100f032001030f6141c6041c03100900840595403100600c44182d804 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 611558291 1250 611557041 611557043
    0x50d0606050918040c09020a0224090f070605091908250506090f0d0303060b0a020102030a05180c121906020c1207020319031709010c080105010e060f0304020d 70
    0x2004400d46a5200030042d070481242207000301e1140b8a0b040103540d9841469200700d030301500007210b260808080380080c6d0000c041c0b11040d48074200c0c0700103210303584c804808064a6000201c0c905031400800d01b40c5030032481085881603801000080c4911a4403e08a801c0c1d030209a4950b200002e1000c03810595840540c8060f90f540102c540b214002d8108640540159014441e0400c00c5502c41c02045000c0c411b20740b6a03580329003007840802035803e200508881150190400084039035464a1b0500c0e00c0e403200b0b00540040c2d60000c2001844025841403640000c2c0c281039038011107030a042900da071104008a10ba00c1686000c0480e100035900b042800340203203611580c903410075000d1030303c0c101035044480c20140078003840042c01e1701120352000741c9440c2c580040c020044c184042c07107440060700e01400103808006000500440c8980c4100441d4015030700e071000001d00502106008107182c8040c2c020030b0400a07481c100700c07a07035582c200079100c202100203041d903900e480301c3c40000c05480c98084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 611559541 1250 611558291 611558317
    0x30d1b1d031501080d030b0a0b120a060909350d020d0e0d05070302070e060105160302010b181f231c03110d0903080f03040201031d0105070f02161505 66
    0x10135558030110328245101c030142c50a2281100300390030041c07043c5d51800f807280c0080d4180030084455000d40219a0025103550000400f1070711140304105454074601c0544401d45160681c00c3c022611180c2d8603203036459503150354060744640c0340b150244c2c4946e02941c402e080e00411800d014249070380c402000d5413881d03001c641300100c0e00b4070041c01c1a00b0540c8180c02500030402c001440340200c00050781b00c0c00050b51150300d000d10302050008410701c0c0310401c2e000c540d40e07404503010640f140700034a8001012078050285900e406003100d145030f43c4085080800080c10502000180100e00c54101c0c010351140c0500401070380314002c22481c2281a80801034055900d07100c4082c981c00c0400241ea140c00c9a084d1441444140d03400e80b80d0b10b0113032100611442d41040303a926803085400255402c144145004a807020b0207107090180881441142c01260755658140804141c001890300e41035840c42c000703000d0401001e03440f01180c41c1c81d0b00c513544e1079001a0b40100c124038410422a106562070341 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 611560791 1250 611559541 611559583
    0x209010908160902031509190e03121b0f070b1504020901021e010917040e0f04080706053301090617040204111b01140121030e010504090608030d1b1d03 67
    0x40440c00145c88c581000400c207103490500c040c0c44901104441d401c902c120b4608155840f5106618059248400030b0000c0303075428449800d8458486c8010101c803030058124001c0b0307007031041c4580c82110200359907a21842c030400000220fa600860f0461200890394042030450a100c1d410341c1c050407000c1c1005288502e10400701e81c0c280d0404001e802501c020002100903550f82c150101c00301c80c01910040d04c0c03298148000c01c0080c038242c21299003c1e030b0508404505000780c04c2c008a41d4100e400000b4a401c4503141c100450356402140c0c0c1006240b14507014421000302030102c1c08100000c5c1c0f000e4010b545034092034004a100104840240e81c0e0ba0301d04041038248000314600900f40041079864281000000141d01092541c19200d2140da1545201440f52a81d0302625603240181d086410b000c400d1000040c0c50b52580302e14002010304a0145a1f101100034810080354040490b00302c03e41c0f0240700507a18581d010040302c1d290f0700e81060600958100b840000e140c0500602c002000008031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 611562041 1250 611560791 611560801
    0x32706050c2401030602070602041221031109040504080c3712030b030f0f0304061b050d110c0319260d090f060e010209010908160902031509 62
    0x40001064094181c41c00d4821a030200028440800c080020210111103800c0061000c50703110750040c0202e5105240062415540ea000c4c0d4040620603101900c1010200707800d4510500c0710580c01d802c104081c5402c2200c0803281031011100d02400c4901030040f6901c40c0090b042100c03003401c9a440d0840b603004c60304034600d0381401c00d40b0111071303026a0b62400004620042d8004d108400d40a500354000310050442d001d000b07084008007030000d501503052190052000e0110700501c89031550310520405180d442c0d05060001d08580d44219010b10440581100100420300c0400d080c1034920389807405191410b2800c1a1902d0030071030b0350302e05500d80a89129031903040443d00b00461050321070400d0b28980c502101c5015400121803a40309260002044030080c034002580c011009244603007400c0c1074404a03034032003c00b203900140c5034042030383d40025518015030308050108001d00c1c2500041034100c0b05503400790140c0c000c0f031042504054001c00403481910221301071003500306000c0c080c45194980 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 611563291 1250 611562041 611562047
    0x6080a060203010f15050a05180a06080108150c0403030309230601061d030604020f15180108090708030723010c120506010f0e0f030106180b10050313032706 69
    0x400e110307411041580e060009407005c8400c0c0351013240704150f207540741401070b90780040d54994403061420820003622501150103686091481c000b500096403515040c5d07041002e5645001402e1150003605050001042100c60001007158184d0344d15150102d0510198175040b601000002104004d02544c568013902e0000c00140c064129034290f510300000c5050703101041201d030640014a82c041d004440040d0140c00d220703c004100b804068080f103030055a103a21603010350490801c1517120705000c001d101d0705c2d6030300418054220050102521106180c5130300e00b543d900c2044002031040c1c4111040300e02d01d071490741e420310101c80200024050f01d48030b000001e145140f15240c1c03c0401d80b030400860301d5540b160180003048000c944800741e00d040b910003041080d90b5500403940e4159211038001c2103080710300001c8500e19005650203e64840301c0400c10003805030101c00300301000000c3c41005400400001211201600350421a40210380601d1002c40d5442403c81e034454688004000248180c2c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 611564541 1250 611563291 611563297
    0x3030b040c09031109070516230303090a1709060a0806011205190e030d06031209090c0e22020c070f050604030c05010503150306040c0302040e0c0a15020106080a0602 73
    0x4119000c10041d00d0041c1d060b6600741c00ca00010f80390b881d452001c1200c501303140700266044040750810130f082c6010400144000e1107000c3d811219081254990b500c1d08205e2184c1001150145001e181140f50030004036070f88400c10100074042c00e0403044030040c4460300b2000c50f0000403002d00302c16600d100c1c1880240c038800b030507901180062400b00b11000640b0441c030401c0d0086030500b11806600d045c4050b60f4001e0f0a1981040c0d60030302042001c0d0380b41c600c0a10a132001140720b00d00394422110790102c0548050303050b92140c501a4180000303c025154828110700803000201c0e07020340444d6020320400000080c603181300c00d100344002000d8002c02c5001910000b101e0784d000007010401c2d20b500a10001d07009600c4000c081c0900d10303109100560141000d5940481c0700145491540c2c54200040c0c9411401d65003a6550032401900b030056003828041d4202c0081000000c01c01500510080b40c03548410388141c03407a01d50202055015540300703401010062810500f11020400c1609110b40254 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 611565791 1250 611564541 611564561
    0x14030d051801090519020f091501081308030a091104090615050a030c0e04030c0b040f14060f0c0c010204170304061b0c0b1803010e010e0d18052103070303 68
    0x4101ca0040c2072524814022001c00030f90201c0505103000091400c58004100c0c0d11049a02c07040f191074034052521070000c414405ca1105281e44141440000003604140d8090070350500c200c0c0010302600480c54070300c116500032040083c006a01c1e80c460400d4444013078a00b414590040c00d01d80300d00140b110755005403041460140041c412035944208104014007144001001c1e000885410802c0c1d03500011003d03403043c041e0500c0d0000721013958038001e2000701120222101c0740740c0440402800304040c00c040a01c3c414000800715170420000700e85d00c10b03030001d0004105441c0018400c411001c2901501c005106861b02102001d580026058070f0360498001e4500240c0c40708901e2081000003030301c810203150400500300c40b20703042032050340c09580704440e143c1c03080e82c540140c070015440034400c0249031003100c00002002c51204003494204844080c281e4100404c4e00380401040c0180c00c5500b0843c0c0707080b03e980c201d49800211490704031440d8003c81081d4040403940070285901a00958400 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 611567041 1250 611565791 611565811
    0x30b06120105121908030603010b03030c0f160b0d0c111504020907090303092d03030206070e0a151808011b260a09150606090305060105151614030d05 66
    0xe02d03e0792101c140d542d02c0320502c0c1c00c0041c01505500c0c01040072030700150b80101c0098000b0039000242800700346142d008822000032944000240c00e00c00e401401788107800d031a000840c40c107103480c20060454a0150b6690b0b00000ca689021a010b075600072441c5001d004c141ca0700361a410035400a03c070590020448040c1d00a04102c40058010791040303026106595040e01c1d94407071142400c48034515024031b841c04010b0310f0540030030051589103460001c001036111783d005003058640340c2c400516200c00801e035207004240342c3c003041c00701c41005a1480c000c5a06442c0602c50840c01c1540082111019030060340a5483c1c4049800603034400760302072001d14901d854000a901d420311340d1079803e07527141030305036184a41c003030100303001a000b034000444841c081c600d82c100b54007440c0a00011265194040d00c041a8140403c00400c8018010385004080484000b810700300002d11503901d03885141000102c40b0304041055080020b81c680705e440c1149464100c0e41c403908490303600001000195441040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 611568291 1250 611567041 611567059
    0xa08070f05030a080313080c1005191a0f060d0203040302030918101502010e06012402010908090906030f010c0e04052401050c010b04050a140709030309030b0403030b06120105 77
    0x4900b0001545288543e010003000d1440d0344021014484c2c201c110360171503c04030b0402c9500d00b410001c008442010300c549000084c141071060350403290012288034180c200d41002c807032102d180a400f0650322158415207014000014940019500780b15403802000b40500c0442030006240e8000007509860310242c9003c01403008500e450321386030b50101c45000045100311001e018100145010481c030a02da8000810140b50403070125080c004241c020b215a010b84031081c0040000500e2804260100c600003004403402c6500c40314024495480f9250184c0c0e120404500143c504109840030800800001c02ca0307007180705c2000304400002941e45214604140103d111009030103a040c0d00a01282d44043e003d0480000558160f04091960000c075540c90300704800310f841e9070007511b100d4026032400140095110240e11103a01e40a440c8408000c0d5081c0f00341700280d0031032001c1040d40c1d040390140000c0e41e1a072608402528282c0d20486e00324102187c42c070500c00400059a040c0d4008480c0c03055 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 611569541 1250 611568291 611568299
    0x71415040906050913050a112101140a020c071e0e01030f030806060a0e19051c12140a1d060f0904050109050601020c0d020415080703060b01090506190309020a08070f 73
    0x145070303505c101c0050182d801000158002414220319a8400d410141c0071102030307e00518080e04504001e04100b0241c1d442395600c0b040480c2c850007a650000c45200d046041c201542105550b410190254030007210040c90341c00e1080810100e098003e1000f404601619a140c3c0b03090045004120421008900c0500104043c3d14042055805c0410181c0d43d0442c14051002004012500c8602c0311203404101c14004c15180c84402458204032010850f41014004038942081c103207110040301010800004108512070401c8400c40e414a05185420010820203a20500240040d000300a80c03040d40002d600c3c04000c110710161100e4041101c040044c0ea0781c0f21210030960368100e40090042c0c00c10740969015180c280200302081d40045c0c800034410b03142040c2e2024240c1e2942010313516600c0207008000b0004240a250390180c001c1c82c0800500b03140201040442c051012088400c0100c042030710281480b03544668006074000709504035403661007000d41d0300d41c1c00d1406516010342c0c6040d8081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 611570791 1250 611569541 611569561
    0x618120909040f0314160b06030c0f060a02250501030b031f02070507030204090303320a2301060509040f111e0c0a210c03020714150409060509 63
    0x1035410310003900040c5903903140c1c0d82d5141c144080d5003080b0305125156218015030036281024254070b040200114202c0324250070085100b4400a1034a8407940c04900c0080031600c0d0040c040b080c2943c00e4441d55203820710203505074104400200c0d8a100444c11042950402c20010f0b40036044500a032004c008185207202130640701c0003910141d210750b440072036041101781c6a0b0741c0188012401242034400880e01d0b680007030152052980103030006500d0303102a0100c00c6c071580e5070541940071f01d0010310913000d0600f004015014024011103225640c0d84055a0400701640d50401c003400389042c040d21980c54550140898000c0c01c880d40c000d500c0c0c040c100d4840b1060303102d15081001008102030514401554814101c030020030490304a45007404581b1004004100c0c40c6441c5200d8030360022a203003400c0c0c4600c07000a2081e240c2003000018a04100840d4000c07034041c00b40c1700703004c44091001800c01d01040e8141d640c80200030001a0015002608081c0799010344140c1e641283d1241c2151601e030841 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 611572041 1250 611570791 611570797
    0x62a020a1101050901091a0a080c16021c06180c0b0c100209040b0a2904120609060b13060801060803070c17070e040b2a07061a03061812 60
    0x81040c004441c18015030342c060303406448404014905414040d0b2100c00c890384030300013501115007002d00460103170030007600030321041d03440a0542e152600700000c1408440301d40c07040f6100640201c45030480f11090044107902000490340081050007080c1d0501400120306483c048251110f210406c00415050901001c0340d40840c4c000c0003c0901201c80d190b031000950103084903580c080e5440320324010030380b5880c205100501a10000500304800410a08040400042100c4405d403082000307201d10050b5181090009030071801c0019010118640000182400001103601c03030025036860020a141f50404015180e1140080c8816661070340a280d882c05070090060070700000b000140310780c05142c060342c0280042a801c8509550352403060300111401135030156110900c2c0c0c7d08002c000c52065100c00141d0034108000b00c4101600345040041e40204840144150303112103c495a6441c030450b00780344200000e0540d142420500a564131003558600c0110311800ba01100004428601e419 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 611573291 1250 611572041 611572043
    0x10b0306010e0118170a0b131a040201120f060506030c090a090b03060105090a1e0c02010506030a0206030105040b01052217030304030203250f0302030d0b0607020303090603040807062a020a 83
    0x119807958100110150710a503022520742061091707201b000003040884501c4c1e4003802900c01080c00c0d02241d401d0040403a02c40300c1416042400341801c1c000141d038880e401c4800711407502d2000510202d22003695025000c82c0d0300899000801009210b40c20910310000c0071301c0d410845400d2586a80c5240c14001e4030708511206505421072001004941000400a40d014502c0c51000450920020b8200025040559840100c540c0d17056062609502446000d801c514110000c040c024465400100f0510050181c50300407521030b07050440341c3e40030b201584d216280c000103658070302e007101d20a649984800e200f00420300c500031400b0b0400a0000c0110382c022038040d0701440c50515840030b0702c8407944406a04012a804195584010800071380142c04e04a11a40c0a190f5030a00401d44000783c2d000c14181600c00c1d8000c102c5440141c2d4000200e9403200003c1d140700d902c1f40d42d2401c003511a40100400601309504100701880040710002902c0c48241c4c050b00c0301c1c0c4003842224070480c0d40e20003c1c18 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 611574541 1250 611573291 611573327
    0x140a080705030c09072d080f15011101020903070e0f100e160c0f0b0a050105060412020f0307121401050c07020d02010e060d0c031b020a0215090406030b010b0306010e01 74
    0x700c2c0d01c0b2420113112165225980d0f05026810070480850301e01c00543c407840552509054000703280d1030719801942c4075001036641e8410007030303818858000c0c82034860041745a0b040c010307107030310030506000217405a0301301034001000d5508040d40c940c40a607074520102c802904080210000800e524011003031041615803908001c522595141c10124a8000480302e10b0140a9139900f4040001c440d0b01e5445203c0f4428014020641020141007042c3ea50680040e481644140414004204090559042e5580490700e0400b40b03008000483d00b0b10256400002e8440703809032812040c829041202c1c084c840004000300945c1c6d550810301511400ba880000f903102030a88000009984038800114039200000c101c5458500747d0001081154001e0301298080f035200d070f40c0c40846030300b81011413031410340c00c1c0080c0481000aa0020b02a901d1080754500e03040300104000700a5200c40d4040c2c400b0f154480b04204241d41c403001803824540040754100e000400c0c0300c101c0c0702c140d4490940300b0580c0440b05 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 611575791 1250 611574541 611574553
    0xf08070315140f0417030112021002071202060f0f03090f0c03060c040e1015020d020c0f0607030f030213061101150b1602010c05190308070810090e0102070507140a08070503 76
    0x28401d40001c80020740142c60103817403c0c0c1644613080c3e0603c0107500a02804088000203501031051207443c41529035410155040a02c0421460420010103000598101c8580317030780300c03188a01d11409000e0a143e07840703030410120800540c2d0b04006038940070f2806010865a008010700100759868004445040300c840050008004404403184000d8000742d001c0358840070152102c1405042000e082824001644480d418441182e010b00240d03071607040640b040d000f100001004524940309015000b400c1160341c21910450354401da065900c01a82c0c100a000090f9840034010061607801c6110140c1d946403098807001d049042c140e450490344118280f42c10040c0c034050000e0103401a00c4181d041c4460300c01a0000600203202c0284135040240340001c08003102d0a00130704404d0014808014040407000380003844c0460f00001c1c048400050340410174451007021540607000d2080001e00a100e642070224900c1c43d030344000202c0c2c050a99920b150715a0314100c1f160303928014401c5942640003d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 611577041 1250 611575791 611575801
    0x150a03061e0c08060a0503060906070c1b03061a01110a020f0f0d0803010e0c0c0c2403070e01031107021810051002010504030315030302060609040c0f0807031514 71
    0x10350068001942100038031006101000d0710101038844100715800001c2c80441004030fa450f158071001c2c0030304029401080381c1d2034560413080d6654400f802c0d800900c40c0301c1004404120404140081c0034103d1680500b20136902d00d8640058000c0502403041e40905040700c0540d54458540a001a504038000b030104c0d01d07880e000d00407255410b0b207035503400010001c100381180d11207402c9030b15080c0c8200c0b0029560b41c5842e00502107800d001d040fa5184c4d40042000441410000034126000d150480f03a00700740c50003c0720b407001141585400c42d1540203010040144203500008800303103000b420f0b2802d001802141e100540548110035009610490741039010081901000035239038004101c903407950310f4949650014128044040d034601c0184e450700e00b08000c1590501501d00001500801d41801e41d046560280d141d07580100f0180c0103950620020b0107000e502600c9100030040c1001e882141a1940c6001d52240000c0c04161611600d01e10701d02c0c1010031601c00d862250303402d44060545a110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 611578291 1250 611577041 611577053
    0xb07020d0f200d0b1311030a0f0218010b0d020a050405040e030c12030106140d200d06050409020607020906010c02040f060302011808061f09050a02090f042c01022a06150a03 76
    0x2c0710a0725828100700f2400ba1503281004203d41c0c040c040c0011009c3c1410620420440b08001e00d5880104100c0d840100601c11850094680c45128210090384134540f521048800d4000c84d4845640982000440059070b800400100300800c0050f05032503e001850380403601074403080c4038640004031040b02c408100d01806000d00041420360034007244c0005108002c0c1024140d260613581c00380e0000680061105440c460100100f07020b0310244201441500010500d01a103980a4080e0000c100002ca00768443c1c5139400c02140d0090080110710402c0c01075000400450000f03d011807003080001c0d4803080103120000413158144018500c5070384201500100ca0022120300008405042c030105400055000e010310840461000603181c20280c020800710200150507580034524007401c0000f0050b10004440d4440989004501c0c441701c8000c030a8028403403140d612070101c2040410390061a200d40c80c1400d00c1407034004940c5107031544c4140c41d400e08039100d003540e444050604200300081c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 611579541 1250 611578291 611578321
    0x1a01080403020c1c0f0b0718060c032604060c090503120d0e0a08030a15090209010801091d03070c090b1e010c020a08031b0d020f070b07020d0f200d0b 66
    0x4041c20980c441007083ea40c17108145107100d02e04584c03001d580c1080051a603400309405503440280d050341074966142103070143c4000030324034000e8108501c41c000340d480700b5498000b1601d0030103900e0601e1010706d0581003031300c014559140808009088500d00190034980010341d02060480a1046032a10303004d80c9208000f03046e04610482c40340031f0b02010b41e001c503100781c0103548204070b4a000441d01d04441d0096000e4200b1540191a000d4418000c1101c2c61f40d03c190700340e054400c2454006020110405026909107008251404501c40041c8540c100700c03c03944030400700d03451200d051100080100401022043c8410b1003a510f14107400a5056584940203034140c0e14000b42001e41c41a4490640e1800c66200d40018400b040f01101c651049160800803801d58986a201070a03240422489083c1c80700910721401c1c10040000c0354450a660f1016803845103264000304820000006103400e0351000d0640034110061a0b42c0e1110403907900300200750103000c036800b4120343c00550301c1440b940c1c0400c0e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 611580791 1250 611579541 611579569
    0x5090c0903330117064b010e09030304030c08130e1501210e0c060c07091505221d0f01050901020f03041502090409061a01080403020c 59
    0x4414184200c2500040410030401a10140101c030080902e20242d1242900e041c0d210032481c07a43c1c0d080d03c20886201103007141e003180d0080081000c40e06043c06190514a800b100b20a0a9070807421110742c0d4060101041c8007521081c01c40c2240c1d80e40c034503004480500c1224a088503070030801c00140028414017011118a00c03e82100742030000034031403105842c140c0d0700f03c1c0d25091218414171200320294040160821800d2070141000c00803080f007041003d41d10a0400c0c00030307840e11311a241d120000d00000c48003400c050100ba4440e80040d6486588030143e1044110301481c1c12500c202c0c07040c10700c5208003501c10240c00c0f0729071001c00d850b401c1448600d840648407541c1d9140110000e1201a020000702101c1103001014960300c07500b500c5003103071005400d1340820f03031040060310480c900c0007045d00e5005401c40c6d04014a1404014080c000c0c0c464441105e83c0300e46000441010024690b01000c002e004140407000d10524802c01556a9041030390080e025a00030103220902d8580381521412203 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 611582041 1250 611580791 611580793
    0xb13031205070804230f030c0d0201210506090a0b0102030412020103140108330403051b011407030f090309090b030a051b0f100f0503150d03030b090c0405090c0903 72
    0x815602c810802da0042d41100c2c4090b44e044813000c101c201d060401e05d50084040382c43c00211420100025600c40541c005140680c2d080f00d8501c065a0142c035420a40c030040c5e883c1c0982c0d0424101244000702011648940725070843c8000c10148401d52240c021461810380045281604124850025441a100481c1056196495603601140d0484070394020310f0110000c1c0304001d046c2c1c40c1004810203081218a52041e44200a0241181900700e140c02c0303905814103a07034030040000d16408044010b160728050f9820701884020940c034480e6840d115400c150741c10007440c450a2400c2c01035584202010300010010308050080350303100da07c070303481c0c1c410700500f01d5480c120107940305410202d034058041000032200014010a00303042816007000c0404441c20b519030150800040c00d94040000035a00b0031901000003034407031404941c0c0000e101d0008143c4009c0b2560342c58010058040900b200b405003858101041100031038000f0348094410050119031640c0e503c400164998100c05000780e41 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 611583291 1250 611582041 611582047
    0x230703051005100b0703030c2007050405090a020d030801080706080705090f030c04090b0105130b012709060b03040c080601081e070b0f130e010e040f02040b090a150b13031205 77
    0x904e540301002801040c5c4246c07404201000307000c001500c50700c0d01000e894150309aa00300c0240c0c104c0003280840036980215000121034030740c048258034019550000a4014185001903c203140d08843c016049035410401c03121802e85910702251503210555041000c56400c5c05180c0c540e00e48000c04881c609005011030790003112540000e400d440040d0703405c1d40c04168281c018001030800100c8200051161a000c3c00a030102500080200103001141d500402c441043d90800742080207001000301142c5505100346a2180260a416070060380e040b5403800c0e2001c00082c00c000046800c5040300e41000c0030b40400107600504280700b020f51a448605030082400202d0f10300c079114050b0402151417500715441d0b109405007082c1e5145c040e00f180304d0440c2104010405185080001c543c0035900000c04001882c284c404500500541e01105070700050b04810048407502a034000c81d40720100b100703000c04040d500c0720740341014130801c15007000184070303901c061001c0707440b0101904d80300020b031a00e586 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 611584541 1250 611583291 611583299
    0x50c15091c02040516080903090102060118060b040b09040509070e0c0a020f12040f061b060902030309090106050d0c1718031324261305030723070305100510 69
    0x48034804c580b116454040c0c54109203440354429611540001f00300000c40c42c0094880010707550b01c105104003019010b41d8010042820325940245004203900d003035032504c0342d031502410021a004640468000c2c0c2c548800141e08400000e503020468280340c8004030f01d03407146d030b2704020134ae40680c4101c0b003944100551243d0410381040a00c181c8032000120944135410641c0a40c02c01d0381c6a03000200300114114070490586442480c0c7c62415801b41e00041e521043d0300c08682180a0104d00a5000c21400300003d82d071a0002c1c02001c517880001d008012400800c2c0c020350f110090401e1800208900c1c400141513003c100001002a070003440032a402c2061407802e01d0042e200c0e40c0c0044450004038070f680410401c5030300440040c0607540c10028581030001a100e080200043c10140355044a80e020840c860054040c60a4058004c0c0a1383e90b01d0426092195810040800302110100d00c11002c407a0140d01203420b2090f2035000bc06002001410120700340500001b42c00005402c2c0c1a0350002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 611585791 1250 611584541 611584549
    0x5010f050c030c070303020f030a0503070305071e0e010908010c0203090d021801030c03050601060e06092b26210405010b0d050a0309081b0108130f0f050c15091c02 72
    0x120fa00320003401043e07254110714000342400700d401c4541846510900003580c82c181c01405980c0d0100092070005156540c42c1022200c107194084001c0308400c210a0000c207080d804103c5419031042038a843c007855564020107801c82d180483c1e0320300141c10610240140f494038120300301d00300703000500c00300b0030341c41803c0d40d04001c810aa1040f18101005030f0304108010041c0509801001e1a00b0030071403550380031b400b1030740b030344556401031780b003062176110024405268040300f01c0b443c0b66201c44414039514600e420b480071141454076032001c20107412a00c08847e85082141e03001a60000d044550409400d1066130740351004c0c00445c1c0a549030314400d041030321090301109540b0b0094009000088070f0b800c006d4403141450f040240c40d9040400390750418103615000c08001032080c60502d4440e540c50b004c0718503081c003c1c1d90080622009486500a001300008031420150291042d9080900c1c0d0004010002e144038a0403c2c2c0d400042c4403065840c40c0c5191150301004000d4190b54455007164005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 611587041 1250 611585791 611585797
    0xd14090d0c0f12060c090f18090b07030605150901020d350a051812070804052e03050106080c0c0a051507031808030a0c2109060b09040c05010f050c03 66
    0x51903102d01641002800d015450003928070b40507013420b01c20121b60070a800709140c10201d001d4808005001d07039071500f14000c81c0c0d2000b40c285030024002c0c051820003030070080140650748100d034030402010f00400e5149101c4011141e60a6058004055141d1041c4040e40c0401045500b8040d10025500c901c0204420600f662402700082c05502c0e207519192090504941000e4102d402000581101801d003040018000800c1942c503008141c03950701e50718085030796100795081950040c605405806860340e5003080b506a03028001c11064105086110481c2140c1c401d10070b410019803030038080b4840380202c10061075004ca0308419074818203401d0310740914001d805c24001d60710015070300401920b103602d0f2144c0e60000003c044141003003c0c3d2503d0b100c05e9404090420903007a56504260050710380039107144140e000c802401010600582d0054900400e440700040e92090306044d624210707071400c1f1402921850340b00d860800b00500f0b02004441c0e0f01444a40c20042c03107401c00c6903182c10b81c400c00103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 611588291 1250 611587041 611587049
    0x31309050c1c021e18010305060a080708060103062d1104030807110310090308061009031401091b050d0b060609041a1305070c0b071205180d14090d0c0f 67
    0x942c1c2d4140400c0c5070244e441e40b5240b150014202405441e0040c1c1ca900e40c00e0000c020240780c081040e454141c00101c0d820b80c507502448292003030342000600c0b00340208059040303e001e4130080100030507880010202014907035100f650180035024801200c20550b103c0c00180031480c4105013496102e5490240e10341c040202590103088101f551001480d003001400b496900680d4244070080080e07501400314a405030403184901d6075151418200703072041300f0040c01150044848400381028002d230f2030003000205416a010a07018900d29081e041408981c0704580001e0003080300f1040503114032100c54000b810042d40008200107065150742c85005240c400c5900d408260303d084010000c03c110702d100c000d90705c04002e0a0800b000401900032001084640e0403d80340200c641d510b0b0012540300ca8034514081c81507290409021400c0f51101ea100098070040b0122000c0241e441004c0c2d0f00c21007004003da20340c030000c0010b059031781801e69000d0b04451051043e0055903844211244c56010310b900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 611589541 1250 611588291 611588347
    0xf0609120804140c030a0f050309040207151505010807080a06080607021e012310080d030c0e0f0a1403031e130e15010c08070204051017031309050c 65
    0x205100c240280d82c02564220001d1600504c220780405001c0b9448043c1030f0405042c0c030320420a8481401000e004640d00340301c000f0001c5503034403080d150803200585007420150940d443c000c04103010108040030541910030586961600d030341d603140d08036a07031030000340b04503000780e143d03003002954030300030812140100240c4c0c0140005680c445017000343d50f001140a10f4041e810019041400380b503910141d119010b0000040c505603aa48201100000c0903912600c21441521590180c00380d06a120b4a5004900c1c0d540c04401d005400420030020701500a5036400034441c3c804219000e820800c03001000c81c00380680f41402c042c948a0808214601d008692507007001401400d14810040c8402c043c000b03001c600780d15420214459013844403020003181c1404202c020680c1802000c41c240c80c44680c0c006c0052100d8a030403407400000900c2449044a010001245494081c4010050329090001020189103080c0b90010700400b410f000781011020b50780802a003a90b030038080070400d100b030500e44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 611590791 1250 611589541 611589557
    0x105033a02060603010f060e0103022b08070204050f0925030f05011a09040515040f0b1303030605030321060609060d2c030306010c03030f1416030506010207030f060912 74
    0x40c3c107250a40701c00150140000d0700d0030b002840303d03080311010709040d660184d03100700d524080c0320080f2981e825442c0c550f100e5407020300f080c2020000d01000900e1082d100b554280103075102e50f034031081808010381d04d401007038101020040003a2081d042e06540e00d05525080010070740e494440030b000055050055500365110b00c548107640745c41c5115140600c4043d12480c040d8a840c3c1c41d0503848541840181504243d1480400c3c01d024086500490741d03a08004131041908040d409a4071201c0211030490210b410701000081c50303c1c003c000c0c0d138078035080f9a1380886010200b60502002900041c8501e52100050010350b006464040190080343c102c0480026103408600740d032a884900d03180501da03908800e1a1008813004040241e035000803080c2001c0704644554542903005e410502e1504025030314295003000140ba840700840c0c040c1c01810f00c4034440c088112000c4042e904100c852a016034003a9004000240e040d090310590940107080006183c1d001c3e640d100c04689141c642000010007807 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 611592041 1250 611590791 611590801
    0xd15021b06060a0302060f0c1e0d110105010b0702090c1e030121151503150b011b0b0105130207050304170f1c1d0604121a0105033a0206 60
    0x300702180d000001261400502440d540c002031240c03280309600c6544017070114444244200402c000100010307090b60a031b805c4141440313425640c01000011000188404030055070070030061003024141c1d038600a001e07103051415000c0c806804809420660803560401c04248803c01d4070072111401c00d541400550761307525002c1002e021080f0011044010702c1c5a10b42d000008084803d100403100b040500030888140c070803812181d40c40641e002410802190014199800240d80011030f062001d0300d0300c68440a04800b40b206209200c0300c01000c00c004a0014016031404d019121905040303110051b01d8800c07a030382c50508542259000903c600d01060b4440d02d090303020301040d004558103000034034500202003050074020700411104002d004095050f1044814041e4008525600141480307030b54583c2c1e600c096440c0380307006070141d4600b03121495401d091454401c5040c103ca200400030076100e07500840041c605102d0980345601246460001303040c410604a00c00c2102038681c000e40301c2c501d40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 611593291 1250 611592041 611592043
    0x140603250302060d0608100b01050d0504060b0d030201020a110304120f0203030f040f1701050603100e0703020604030515010b1c0b01031b0801090b01022b1103030114011404080c0d15021b 82
    0x1180d4110808a81028446c1230944d03444000d40320094140080450389480302d0400720024400325000c0d80e08201030070048028580c054009001e418219030b5042500c400075200c4507201d010310f0107001c20340c44540c5040000300e02c454950070580ca00003001c2d40c1c44d0a03e012102c0703072541d1050344140c6148081150410070108100b18548003001da07180240030620301741000035121511503145055855640b80c1e046102201003000c04d02865018104594581cac583c01d2140c1d40d405400641107601007004004034015500e501500d00000d800a020303078503020000200000b4040c0d078840541010380c1c40500c880401360001600c41084503903118000b8950400101a00b5190017004503410355022846c650b01540548810700d44198515a41d42c4a0181d260707130441c2e0400d848134900085200110002c9601203c200589000c000e00b40c86060345803a01000d002024001c5201c0c071a4250080b01101c005401c0440c046500c0d60f00c01e1120000c0744c1343d001a4401260050400c241150901d80344d00803100708 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 611594541 1250 611593291 611593303
    0x80c03060606091f050d02071109010f06020703110102121603020c09011802090f06030403090f05151b010608031c050901181e0506011206140603250302060d0608 71
    0x581903916603d442524030120300e900d240e2101e41c0703690440d540c4016032060b1182080e5800c1d405207680541d99104941884c00d040002e0300c40035440340c48060000507030520f40c00400d000b00d0751705402503c021071a541311213074079860140075241036006038200c00000e178104400030f0a409180c002540110551400d00034545034480d4481d900034602e0700c00503c004a001c2240d2080c400102d500966100a1100840c4403204c07500359868214001100340400c0580100d05001580c070803107a1b140c01e1643d110100440800210301c541c1c114102040200344882d11201300e019410341400001c65165594020603165a1181417021044d0007100c5640d411143c041c060907801ca04008000d201c0c80200194500c2c3c0780120007001071190003441c4100c1078110b030300b081541081d9001010f0307441660b5510324840a1000125044504901d0b094881c154154040c00d11801010003030010600c40d10501c50b411401d6841d00452281c0c683c0c030001c00801a5038060081035000c81d02d01c4082a92840c120b5040e140032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 611595791 1250 611594541 611594551
    0x20703020c0d050c0d150603060207021f0504140d052e060f0e0613090507061e0903110d06150305010b010f0806011b0b040b06090a060b0d0e0f0601080c0306 69
    0x50080d4041070089480043e000480340b408031102241c2403c5403808640e00e50546d640e19560307504041c070020034024258040c0500d58000d440402c8420f225802d03000d034004e51104100c0200b00305100c14440491301181e4100703560750151000a6642d482e485052400c0c0540c0410100741054035070810000384070000070121900c403904180015400c001c080190b0030390900603520300ca502c00c4000b608694503242c40e0241480c7c242e0003081410481d00784a500d65810b40503047c00f02c0d904041c0b0350300c030b05400b20007628094181e03079603099182c0c03c503a00c00c90b04030759010300c0340c2e0b0010401c041c103000301d1404e108070180510b0700c544000c502031961801c0c07425226140485414800403045403900282c114124907403008003480c0403c0d1804444060441c0d081492101520304a0b06504020400c0340b559020f5024a1301220401d041d03645030b0665000351001da001341303251140103004602080d0103507044821103000280580340315180c04440c6c136290100980c044406a807107004050b10900b81130008517005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 611597041 1250 611595791 611595799
    0x6040c060c02060304060209030a140304031b03120c050c040f0b030d09080d1211030a140603060709090f061d010f06020c06090105070201021002030106030f0501080727140a020703020c 81
    0x2501c22900014081e000040001c0c0c00c203600003608204503602440b200980d603a10040c1c0b44001010040034990320f030441c4c00704540707400f880804906884a6000c90300f0440f644044909001e29400008a81c49008910100c481d403103000b101e80c886640702c0c040c1760141060443c0008159168000301403030103c40b45900380501c008504107000039000807400b50310b14205400c242c01d110350302d151850024241000384200900000c814800340d19920f0f0042c050107a10001d8032881d940701c200406850314001d84034440130902c1c00d80100b11140e089d400c00200c02484000020306a943e038011200840e031544200c8419010b03000040c0712a0400d144200040c144a10003084441e55001c0030981c0b41c0b0960410905010700460b040c0c0440e8400c101040c10b05900000554032542d42e2032000e0040d00c10b4044030130185090500200d2180b0000504d40c0896842600b00e0000003580300c07808854003003102d040000c01c2d0b265800f440404280000441c01014004030040c2e0f280c0c500e0900034101080850000c0c4a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 611598291 1250 611597041 611597057
    0x1e04090c2309042102070b030c0c16052413030308010509100e04020d150606020c12010504020303040509130b0705190c020109090c050d1b08100e0a09030e040e06040c06 74
    0x110301112496a20751046100c644e80904407100168034005440d030050120b604000f0806c04415220030191101030084821142480f030051004c5d8403141c2c00f8014180c100c1f00800c20382c5034040c40211010301140f540f0720524542880a501e5040031401504158081281c01004020301e041800c0d4041d0300c10740c80c0c000d00b01940c0c14103100c010110005000a88540080881002845080800c02082d42c0c0000c4042000075030300d600182d01d81c18841849441004043c540201e4078506008491045034010051032409040c40204102e614000c2d00140c00790314403041c2440050081401c1c0c0d402106d130350b2074840c2caa00e40000924008000101383c582001400c082450041c0d8000c001078080d40d41da010040b442e10602907086605028080c404022b0310f06100e09101511109d446503132140c95a0395901c203255070394007000d00f036074a400d1181000c0380c0300c1000050f0079081c181d481411403500c01e1410740e244408000002d01a9003820f0380002c400c1c1c10500c140010400b016401000800c55401c002e50 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 611599541 1250 611598291 611598293
    0xf1d01030f06270501050916030b010905090f070e010f15080712020910050405030d0f080a0c120f05150f01020c0f1c030206040506151e04090c230904 66
    0x1460107800381c00078816601e070007a001d00c2d81c45203100781000c810207081c1250201403030b04009004c2c00741529088428014000481000509800150240c9801131240e0b89940d10b80001e090007010300500d0041c0e98001c0c2a400c2c49001002d120b00030060180b8403582861b54108045900c8841965005040c8a18007900c85022185c001d003480354090030504240700041030220b0404c1c0a8070070780c0c103800d6118a13880031a091498100c0050301c16540190202c51549016081c140c605038844040c080104400b00c0000e07144d030a03150403221032046245490b414051850314010262505090428102a101e0f0200710314401ea0410860108404480720802c1c17502540010f503c440b10a0401ca002d50390380d54442c1c2481d118645800e8207080c8401e034110001a050500a4551000fa1421200c41c0502c6000c9401005080885080c503c001028440e9003131a00301d0000e0210107101c0c142d5089900d5903200780201c2c000d20880c00041c03c0100b06100c0c680c2c0440d0400c114503581040340c074070034030300c41c01844 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 611600791 1250 611599541 611599553
    0x2101050301061203120b120106030b09060105010c0212010f060b1b0c09011a070209040501090506070905060306040e0f061501090501090e0a1107140c0a060807020a03080c0c01060f1d0103 82
    0xf2080715014140302c482501242103082c0a0201c2c841d099030049600f034500c0c0c918007c1540710344203c900414141100d600d40c40c030080c0c1c41d86404c1c4646400030b04020f01000142c6040603424003242000780000601034440b000c1c070f10945054dd40191011080850b4440301f101c10510381c0003070441d0001c06441050050000a1241038041c001e9640c2058002d0a010303901c030300001140da900c0d400514400040c903151070304502903c07800b4000c540c9800b030480030a48103409007951205803040281403900719a20320f000e020081848055840040c843e0b402518205501480202c2c02045400c0c0c4624900003c840054603080d50340d845903040202c0d1000c200020300c4d07400051a0002030051003c038904184d07031043e80c1d0900803420003030100240d5000381c0c54007440000d02c1650240341600e0318410142da07004142d58000301150b001c400f5800216801002070320941e000d0764007415209180b0300740303201e4085290844945801c0808041c0040b0424045003036080b1304801c42d50084141800300d9819913540b0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 611602041 1250 611600791 611600819
    0xc0e0d03080a051815150a0e04030c060f0c020a020405150306010b090406030206031f0b07020108161407080c0106080a24060314011a0105090604061d0402210105030106 74
    0x40701409a840c0045488400201c801c130941c00d00650803107a0a621060400105240a580046070120044803200c03d074104468400d04490005500072207a55541c0c13801e42d078030f0004040485603256101310300c0c0c94041c4a403080110103c4140d00502c0001224418031049035400780c400d2820108000d0308130441d940c00920941900d55031100f4a0315105100e020402034451904002e500500220412010440203048003005c501e0010305100459074a000d9003446118082c00070b800110480c00041100d0107000880c14003080e0361600c4400742f4880210380809420690040700d14040000ba08800907109002e600003401a2601900c8044800e0743c61600e440e078140c002450710240d03010700d40b88000b040da03c214001e507000105005007401000d0002d00130b10004440c070801540d13045114100303501c0341094600c01c2001405051405042000650f0396945440d10400c5583c0e100407071040c15256400a08645001c05c04407200051680b1503204410030142c1019000b40e1400c0803c01a0040000c04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 611603291 1250 611602041 611602051
    0xd11100305150634210509010c0c0503010c0e1f1b06110703050405010813031d0d060c020601031205031b0c0a200f0405090706210f0c0e0d0308 63
    0x80c190360352001400e081840041c044c4a0b4900d419035005401d601c3c0351162140001500c2051622a03000780400b1100d490905094040c0c00210180710203800f80d4040c02c041841030740602c0d040f0a415581d180040d00751402d101f54103000800c071022002c107604000c484201d00c56120340c1101030f01134811030002c00004841c0c200b000e1001c9081c202805218081c0e00c41c034100030072410503075901c1851b4280600240d01030b1213002d000443d65400510801c400440300207200343d141d80e400b80c2420902512000301c11000145503840224140000001850b5200d9183d0032236040c2c01902c1c91390b01d5400c0642030701030b2030030b031000c00e1200c100300b08020040c08200b035059030700d28071031721680f52a4141032851410380f02c114003c003134011591400b60407640d801d802c1035200307008030740340c2942100600c148000d0b61000e460308680741d8800c0c8410701046e03000341c004415505082d4400e40740700865a450a0945a458050710f001e41da07034040380c031401e40d0b003d00b6500c001501074032205460b00a0380d4005004080041c2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 611604541 1250 611603291 611603299
    0x302180403050c0f0303010f0b090f060c07080303190c1b02130b13060f0602010c020319140f0a0806011409190503010c11070609120809010e0d1110030515 68
    0x100050030140207400750f844440f41d00f401c50310f07111852640b2130768a074000c0c01140c1405c50f040ca4000740182031401210311412020b03107017107070b0f5010407000c0c0020b41d0000e2035072200b240103111b800304107104200040c511408030401060300f180800c2c08010111902202c10104100045e203099001005020100146540c1624a684c4040a40e4a400018810305855640c050001c82c01c0b50001d0400350040c1d410340f101011903202055881c1800c0c0e088030504407003900582c2050026403040b62b01528149901c5c2c1c040d040007902041c861782810010307409001003418050b00819482211070744111102c1e031001007030a140c0c00e0b424100f43d200301c20b4003d403084c1c5071045000c0134200e0740c1c8171031004411000f04000341c001c0c0100c1c000707148003400c4c500c03088015030806d2241e91000140140704a420b04121204071401072000140340e101d0b50110b0713200e4081a810300070840c1000d501c40e1198450340c00340c14080c400c80142e51408004015007043e14205d204100343c00d10b4140402d247c981d08031204102c90880d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 611605791 1250 611604541 611604589
    0x6141206070c060204050a08030c01240e100f0b210402010c0f050106051c060b06040339060509010f0905150d0f020a031b021b0418150f06050303040302 67
    0x80f4102c4040d2056070482c0341c05c0071201d500064120130010240801b2500e03000240305200d2045010500e43e40c0280d584102104c840400308580918a84444e0700022406011000c0e19101c1010103808112070740040c440500004001c00c030460100201c4204001e50b1410440d00d08041e00000e064081c00300000e02640c910181000410000350310441c018500a4840e49a80740890b1030f02c04040041c190035911030342000c05000140c81e1800403603040c0c80d0712820703000020ba03003c01c2c200300140c0b60350030411034036140c6820045205070b17401c0702c100100b1190355041e40e214074120004108a02d292110310603c035201000344940d40e2406810407080c2c007201e0342941c40707000c0b44003c039000d04880740156804a03c005051046c4540c1608130101c269488191240d0302d00030b400d0101d9036041c0007142e802044030180601d07000b5281c290050080030003c035050031158006e64403240411811107082004817543c03190b0103584200140121740c020001100a54100741c40c41d008900e88000340102420000204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 611607041 1250 611605791 611605793
    0x1050712030219111b100f02240712200307022b0e01020d081b0c15180106050f0f06070f030906021903020a0b18010f06141206070c 58
    0x396041e10305200c0f404481a10703100c003c1802618690040c0700518060140d011307044590520302000820507000505031144810740c03071000710f515070700c039440c02c42c218081e4500e025185403c0c841c6e0f10440500000c0c04c02c245090a42011341101891500203003202c2c103003440185d1100200c00d080c07607007400d00781010f592035407440400c0303081c410030b081111003200700540c110403e04010030f1400006022600e80303000c0440d00d5801640c0d14150891840001807049000035202804a1010500c0d564500305140c140144e1481c0746040565500f20080001841c004000c0c554803c1e044441c00c90340c01d8402041094200000705000844034442c550185101904984141e03d591007101c0300c440d000b032880361905856203402010f000c0d20f44078510043c481c0301030340307010030303c060104040c001c1d8540c000385040c1e84555140c00242c1d02c000c0c1400e0f80c0c03017240d8690324190b582c01c2c0144100c0325028800003414a00f0319414500c2c603c2e204840c0ba01543c810018030425030000100703203801c914507050500d048000f0b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 611608291 1250 611607041 611607047
    0xc02030c130b03070b07050106050a0b0d0f1d03091e060a1d06160b0a06150c020102010e030a090e0a0e03040515040b1201090f050c0d0e03040306090f2001050712 71
    0x31802c0401c2e00340c400e110000404140d06809008258411002400b04681d108204868007026000d681c0040c60208800c0a0b00f0259902c450001040001c0c0851822564111400c41c0c004031410141c40e0b03000080c41036510b02d4411151800050901e040781d081509001c0401d245008007a21203050002030312540f2080411000540c0700e4510041c042546c890101c2881e40d0360118681d400c480d00100080810781540d114020003007030790000400840d0f0f2107a8050100c0b075403502c1c4a001c3c0d040d9540d031040c89061203402d0005040405ea161228503015181444620a2940040c0a050010300d0310a25011000000c0100c2e012034004075000c402418400d14034085c1449941d00a40102d6400180241c0242c0c15290b0b10341203800d07500f02000424607200c002c0080d10011982d583e11401c0c1001020381c100e6003580485081c000c000c0071642090346aa48841c1111117040302901c902c10a19207040410101c8000388041003060100a00e0062040700060842c2c060404011b00204210070800342041c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 611609541 1250 611608291 611608301
    0x50f100e0f2404030311030c0d0509040b0904050313050f03030d1d07080c010909090f02210a05061b040f18020c030d0b030d03060609030b060301140a020d05070c02030c13 75
    0x20000d48400b50b42d01c070940000590f0051204034042061084030140514011095950501d0114054090340c5152801115103a01c03400301c85a0103555240000c000d502c801c40c026120742d04c9103006682c1c1d0852180910200e1409a0095105040c42200143d41340c030044140d940d654082d07040031401074840c0d5800e40803402000c4500443c0d10030003000003a0180005580034101400f80c0b5200545600c401d03080044d110040c0300680110071041c100f100600b04648640c031f9102c4400d00d8100b41d40101040b0505181d8078103025103040e0701480c00e0006020348807044501c07860202c40500d01d02803130301110550b02820381c070901a030140c01034822407a00545804a5520488240a0740d41e280f001c4500040200201000079010307206040c12580c506002c0d00c14030302036407130940b540c0c4010b501d5940e8030209854014412909952a00c0c80359140801d50b514080c0104690000540ca59440c41c0b94a030498400601c20020071a03121403000150301d02140c0a50501001d4903a404d224401c0e0304030401a103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 611610791 1250 611609541 611609569
    0x51f050f280e0702153403060f0e010f0902090d060506061306030e0d050a09090e0c0303040e0a180b070c140d05090406090605101d0d0c050f100e0f 65
    0x982c0325000c0140580d4081800a1440d054200c020200c1c0c0350840c0002a0461000516440304c065014500048045514241c2c1c0700c100c618020841c26160201b01d510702c409940000c544910000050020340c018604075005001414011400c00031400000b0301050203251004e0b0005030354901184042e15400100c3d0100580c1100340040c407a50b034000280241585144103c20f4040d02d140051960310032002c440440c1504c1e5a0b850905080c001d00c2401400b04560400041c0310b0302d0720b801071585040c4003500051461003110b4015140181411060700c1c00d4110112040017248000e0f00003480d11408144c000603140341010500046152100002c9010510b90b80c151042044281a06900c100244280f11041c1d03424040144e640c00d030b1006a441a000b90360f031000a890680c03c801d4842c1a14205110340040000c82e082e8000340030490b000904001919260042d8400f0308c807505201da0140d54454060750903891130710403410001d2681c2120040944a90001040000301d6658042000c4000b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 611612041 1250 611610791 611610809
    0x290a02210702160e06030105182104030b010321030908160f050a2003211608030f180f070b0c07080106090926031f0801051f050f28 58
    0x944130f03500c00a56503000c07100c0a2081d0709040004000c1008078143c00e844c151441c006024031010301540724a599400c9001180c2c1040600000011419618006000314041e07044440c0705c810162205040c407440585d04805e150034200e18400040c4034508a510106044e2600130200704145007a11403615008000350040c82410007030014041300c00340700d04010840010315580c2012a40a060300e56150010031300d80581200030901210054000501c07084a01e440344141588280d0b4904a054100b6039010200c50545410090042055403680340d11413104801001801088407055a80b180c1c03078015816070311408107208410350402c00c0800054803143c0024000e06031100920300080c14440015207035101c0e12100035404ca417100a164002808800f402c074907507500d0440180b44e20101c1c0c481c00108511845000917065000e202d5180280d186200e245045068075444104c2454650032051080c1c1944540000f1580e8940d507015503204c94800040f05451003445490b0203c8d041d501010760 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 611613291 1250 611612041 611612083
    0xf030b04020d0219021908040506180a140f01030603081c0f02270406060203040311030709091a07030608030a1b12050d051506070b040c03290a02210702 67
    0x144241201d030600d203443c01d1742120000c905030448001c43e800018800792902d081048284140d080410040045d00035014005c401c2101500c0070506101d42c075800076603044483c0c200e400291501451122001c4003d1806200542c25038032030804e103201e000082e40985031303031813050064032240b40c00c42030300700c0300d9404111340310303200c0300a000003042007940c0e1000819003541030080540f400e4071034201980c100754000c1d0305203825070703549442e0820a00031042d4584904000000d24100034003401c00024801d0707200310805409c40e4500e00c820f01e00a00303030300181802c0280070300c40380100000b81c0301c1410b0f040c0b500c0ea4504121131442c4001201100d00a80b011490180402d2581c0c1c1100041480241c0c1c65802c10160755142d02e0f210210900305521a07020b50204020f00104622000e1070340c01c54001d501c41c6424503920307510b4000901e6006252070b1b00c0c07401000c02d40240b000076400c0360342c812004002945003150580c02d801b4000c1c208804110001c0c40000810030701842000860300e400d98201340160 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 611614541 1250 611613291 611613307
    0x301051c050d05040e09010908040b16051c11151b070c0e060a080307030503010e0c0c060708060a0e0610030e03040b0703120e0a03090b0f0d110903010e0307030f030b04020d02 77
    0x2c3c60340507006800341c03040220080b42c400e07101403146e007961941148032581041d0500e05031404642c0503800ca0540031682c0008800401c42c240010010652600e035214141c005060b070242001c599517012507041d800407501040c0200e940e450850b846000580f101400c9903000f6501c8400380155840604092030100010600e800c0b84039582e0b002e88400c40d00e180e60560788403407407941c92058900080c00581e050004100038100300344074039000504184a9030400c021161118a01502180d000b80001c0c201000e0058074104032034028003800c0a0b40300741a8901e0400040740c2c3c40318001c41c0c590201541c58590a004403414400d032030280243d00401c80d030320411030030700130911202020b0010301c841c80d10820b4454040c0004506082070f516403111a4101d260101a90b115000b01c4810002110100040301c00c0340024424014149a07106880f40c0340c681042c2450700711204403004a4880d07004101400100340c000000c03054000300e6240c0031a01c0941d420100300070b8054110300780300050020507d64 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 611615791 1250 611614541 611614547
    0xf1b0d050f0f010f150f031806050a0e030406090b09060c06100602100515010f05131211030f12161e03031a060f070515131e080301051c050d 62
    0x5002c2c110301844251180d807281c3c510b007440b54440c41034800c030000240404042c1401406503090020071030800103103903503d13014074800c401c149000445115540c4e100700840312000c1e05c01c1c8a0308038868070095040c2070403c403024080076070601070000145000710b2001050755825003115944108101036a0315030a101503089105c0d00c1a00031103001d0300440c0d0000700d09031072a1184600c03c50840e603400b1264400400150380c80400e044a800c10414200190300c802e1103444414002003002814031021032a0f1800d00540380d5040002e514447d421a1611040002c00090301d00c7c18003201c4c40a055a8040c00c8000114491401078000d202c899124032032550040c80d070055844a9000391802d005056080d029100300b84000b42c051940505c0501009040300412405010410320440486110506030f00003910550000c9a20049060080034600b04010f00c4078044120032a001d80602000c5800d0360358400c540c0014003400340540060f548412202080030340f0741b03512a402200340c0d4050340c02c2d11802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 611617041 1250 611615791 611615821
    0x910051e060d1409060c0a1b03090807060203180604120813080106060509040f0e030a1101110c0109031107050d021201140403030b030c01080105100302030711010e060406060e0f1b0d05 81
    0x990344c103010f60000030381e00e0b083c44801c4901000840da503000303000d518264041c01402e41c0b000c064003040b00700720003c500c1c5802084584003800d19900219281c5420171841104440c0c00d08c1c01c3c9009080c107105c01c0280300143e42100c601c1640c032405850720388028000c000340042103988295829030030460002140c6811400801c112030095a003131141d181840c0e1800c0980301c480103d102c060340704001480406100300c40d1000f03200c043ca800440e074610144420b0300c0c260440c420034201c59564404134410103801924105050490b03502400b0018a0040085d61241d04e0041c00f80c041e102d01038490050080a50010300b0044494560b0314190815040081c001d00e00415210701a01c10081354190300d42c000c402c041d0485000401c0e111054200000440c040c1d00081d00907414403410038001050400b0a0003030141714201007006224524260401c10151004c582c000c1c00c4480c3c00e9020720bc00d04452007001c07a0303c0062084401034204419110707180034814a481c8512040c03514060007011003042c101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 611618291 1250 611617041 611617051
    0x901050f04270e07090b030316080d140f1303350603010612120306050306040f030206070c0203030d09020109120602040914160c05071d060910051e060d14 68
    0x4119040c2c4a810300d09002c50b00c200040203c1c603031103088100034100341c54022034855100030f81902d090401c0c5010a03a55840300c100102d410407000704812500c2045403166404515801080b050320f410031040c266088100544144211011803200400345406035403025032107290240f0b103000540344280c0c000e00c0119151030b80040c544000c0041201481d050140300e042d10b07038603402c0c100208911b42c2c8000c0004a0720901ca4103150b2101d07000151a5400e00c100da00c11401080001018201e07450020708120000f84814244a103010706034015072800401e550301c03400c201d223001030540c80c50300058a2200d55607015103144144c1051400412106c2c0e00607004482c00b040003403202003d500c06400c6044001c031485004000316400c01c100c01e920035207030384460030300407010f0711982c1c0d454240524403101c0581d0180071680049007448a80d043c84980c10360701920484207030b80741605020024000c040609000100043300007110a0745554040844160031040c103c104000142204c0b581002107040311 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 611619541 1250 611618291 611618339
    0x5030412050910080a0605101220090d060f020c03120606040308070209040611190f0f050318010e0a1110050c060414031209071e0e06060901050f04 65
    0x580000064062400d4600d5110000c0c40104824403c1d1011281c1820041c842c4a001d512880d000841da1190081541000002d6079800319401c000390780700d0181c40080510b540181c8503410020b40b8181d111042d00c1c64240126185918406541880720207841440d60f6074800d1880004c80590111002005280d100360420717143d00207940e44000c106050040384006411400c04211101c01032620035441540141b0482c00041d0382401800700c0040c540241d00d101140041c0104003a8015030001e1892824540a00d400c00400300750503c010218040604410501c400d1030b07000072100f0b10290401d01220503000d04030b880d055441d0600008203180080c881d4010000803410170883c600c81d00458060002c048018402512155506030501004030124009404148004002c04600f40545401041a6030080810310704012504002d010070a50510880381281d034200100c4044050040e400030040b192281c5501a500041e1030512a084404100a00000703000c1141c3c215160640c1000304294 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 611620791 1250 611619541 611619563
    0x30106170f0601080a08070807050d03020d05060405041a070e1203070c06020708030729040b16110a0b25050409050a48030203090d08100b070819050304 67
    0x1c55290307210318003805943c40f1034200c030a00f000030504070001090094070030160b2a242c17010644905090046200348076000a80024040585501c1400b40e2904140102d40410440c03c0955170441d54002d0043c02ca0b4082460a00080700d16000d505520f00d03120300648000c1c402c560b013440e0240c8907400310404076029904420007142c0170b0f2001803100709803030203a4002c6140510390f44a51b00400c110003a00d8001c1c100c000000d058200300c850704180103602c11201a0624101180d0b1841401a101c1000d07080000300300d4011644c0200003841c40250340c00c200940c5994071403000120300030004540080302001542200c0d2101544070004104580054030100599294a000e081c141d490703151428840b440a2003540300c024807201c2d803145500000841c4a04429804660700071480c156032a0750000c01d50120401c5403e400070720400d0002450b034a072003c1140b80c9002e140440c280305002e040f1640602285080410800300708031018014074825907404103440044c0142031f0390040700e00300d131100380ea9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 611622041 1250 611620791 611620813
    0xf0b1209010908071704150c0302070e1512010f090f03030e1204030809131a031605030303130501090206040e071b05100f0b09130c080604020d060203070e03010617 72
    0x62241c075421590090f8032929001094584004409003003243d202c10a070100310000d00144200c50071450714403d52600140c410007130070040e042015540c460b0300d00074501c0c010090b00381118603246105484c01c81d2401007078a1402c0c2c5545c01004c2c0001c01c03424452505000c0301c1401407100342d030741b1014401d9909204540c00c03550b40c00c1d250041301800003050542880180005008100035189080c00a8421201400000004000e4490a240e66907401032141c08111603420b09112116043d10703883d942c0180541f400021035524030000780300034028031392080390380c04124003034010005480d0002c0030962141d4481c480050034041c10343d945004a2546c44000781c1591061301c0180781940c02101601c208803203001158054840710701070071a01c1d41d4420007010f0300d69820040300e00446042c903204039445000c0c5408110700107140c00c5070806a010800b0440140e03604810304c0d0000394000805a00c9848079082a0340b410780002455905500740200030070342210b0041880b10714125242100d45031650 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 611623291 1250 611622041 611622043
    0xf27020a08010e0a06060f08130b0109020c15090a030f021f050106110f0c012001090b06040b0616021302070506040302061b04050f09070903080a050405100f020c09060a0f0b1209 78
    0x21906c40c40e00410040306520900c02c0c00781000a81c42203000036864003c9129540320110303440300760000300305240c0c04a1505842c08041151501c40340004d902b010b180c0c1020310b191662215030850003020071180e84661660360f40700340300e210040380d1b101a0314513002c408400010040c0c0303000d02030440050190408060300c18000508a96454500b334003600681441100441d940c514032901d80d203c4441580151046200074446c1000c15806625000900d007840010401900c2408580502c1038509000000400c00281d000505d103590444400d4250014440000c019000d00440035004e805154100802c3c1900031800d00d10956969100d140c0c0711190541405440c0101d004080e0000c0e40ca01c400305036805d10010280d00034103281880c41e545a982d40da11000340c0c0c044842c0b84001a00890100b1990034044039098100c25603090058501c0b0340301c007001f547c40c1c07541500c1c0c0d442203c808011603019120941024040c000e0202201c0c82c0d41e4440c0e40c5c010b010780c040043c0c2d41c40100240c00144807008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 611624541 1250 611623291 611623301
    0xf0e010801140d11060703050d0507020601050315091219180f0302060c010b040c09170d0e061606230901150501080a02120708041b0f27020a08010e0a 66
    0x10000c420642c4071034080140000050100f10861383c0060100c89100280c0c3c0707107805414000d1080e5180c070b40e50154462500306945000d48180b00359480100180100d5030003090021650030000c1c1c14810079511015000d01e020351010071480c1e02103001848004850034404480981442601d030000c1040b83c1c040c180018068070300c2160300c8840010414801841c08030000c080540580001141d0200140d001408541c018024000032031045201081040d00581040000c2c3d05a4cd001c1c16541c0306450014184000364001d141c41158001080d2100405030907145115a42100c0c081204580c0a103109405492400f281000d043c28440002c542c0c81d014012104a0704403c1c02c1483e11790300d084019594500c018107054000c6400307100c545d414a040f15070b075920541490769070300c004e801c1904081e03200c00d4010401110215950006002d5400003407119070455040d401e0207080e29051400380c0e90501d6001c40305450075400000d0245540358040d00f860b050724411807902c3d8030351311103007416800c0329 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 611625791 1250 611624541 611624549
    0xb0a170609090d110106090e030304021f0c020f190927081e0f130510031407201209010e010f0903171c090507060c0201080406020304060b030703030f0e010801 70
    0x640306000d103003043ca2041c21408039031011203002007180c60300e414004017624440d0700c0c0d500c42640301001b00000d62030309603100f4100d045041d118a2402c00d0b038041c0101456611030029000302c03140d51605240d41c5801030402d0240500081a00140c2d86070002d14001d000e0342d1441e43c6291b40c00940b405105203084e0700c000c0c0f800f41e21101113460b12500b1400400820804a649440548140b102100101c0319200030a034100e1103291660603242031030200103265016481003c1003504d0170700581d41c100b0400603143c0d0481600c0c1880c004000703d09219a03003003041100741640354003507882504401208400a400b050009032904100c01c211900116000c2c00c1c000d8007180051740302c00c4104046065016196004040c145a84d842c20311110030b601c032244030f80310400040710344e0b0b181003c003030050a02c0300b40c001c2d04091508401c1c070021600020903290007d080603048990010108042082c5980100715114025054a09003541e90401a04098801d0504c00100d031003005030b66040e600c030781c01042c1a5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 611627041 1250 611625791 611625793
    0x15150915010309121e080f0609151c0b07050a09060503130605010303020c01030501210b0a060f1d010b09011d12060a0f0e0705060f0309070b0a17060909 67
    0x36920314944101a000c40c9415505040e901d0b004407011a40740d441102e6a40480e84600d00f0300800da60105c80724a28488915040044900c20b00500c85416489079810807400c4030700000c2c13919900281c000803000441841d03400b0201c10364008041d4481a060850380f40500901070440c0c0d1211001d8910f0712400f1848000607082c8801445803078021000740d038002c15564425011640c60740d640c00204c51082c0c00a030050f038080c103807602d034641e410b0080d02d000d814460b0010f9070450148890f0814005400001005030300c4c0403001450f82135081e40502e004203990740025054a654040d0400d106011900e0800c449800a0001c100d01410404486040c43c06135075501c1810250122124000a003480541c0e0140300d07014040d00314001040900d0151128210004503c1b4036581160102c0d140c0d281d0080c001d4125900800c0241c2d50f90b030541c1c1e000d1349440149541d80c0e903980601070414010b43c010307041c07002000c9445001035034055a800d6003088041e0310381546448013010082c3d003000c226001045 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 611628291 1250 611627041 611627059
    0x60609010c0c0806010b0315010201111812010c0e01021b150a0c060609020d20090d020303041a07111f050c16031103061b03060d02130c021515 63
    0x850351007560141040e034040e00109010540f103909550400e074080e8880d00c0d410501100340681d01101030030f682080e078400d00007081001444207070b007800390007030700f181c1c05042850380c0300c0204030303140d485030002c41c458000004c1000b09400c100c06000c5404000500340148034450090781d290352040c0c00c0240d002002840044203d90160a101c1c2503030107050b4410030401700c1410800010410300445016001c0804090b0710351202c03072185030444d19046140240c00340c21200c484200400202100c4103071406071a95042d210301c60000c28518442c80e8000c0c11418150304486401e45082805800c3c081d2041d01403803025201441045a1f61084920b091020010741a44065490180303004100440c00f06090b80c50140d0004e0201860300d8540d842650700c075400b020440711a10302400703000c0c0d00c40403201500c5282500d00290144600008004d540580b4200c00d0210540d61f8044080d003000c1c01c030f081c0038030102442050080d102c00c1e075070340c40260b40311102c40811789040944a190310444070141510030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 611629541 1250 611628291 611628307
    0x4063002030a020c030a091e0303050904020a0207080a050304050901090e100b01030b10170109060f030f030302250c05010908030702010e0d120203041a0316030b180a140f0606 77
    0x9601c040c2c035450890383d08102d43d50000304140064400c14509803a1606020705d000042065802c0b40e10101e07400026511080c000030382c001e019079500100940d00181c540903002e9040e0700d00101504201c410b44a0343c58040d0400c04004014000e0b50401e80d003001860343da035a514000d84541c0482101242c100c840c0e140301d200c00d141c0c012112480c0514004c0740121541c00802c58040030202c190300022007021542105800e1060428010300301e0705c2c000c000d50382c071f0900810b078600554040200384410b0b100c1c01c0760905209030143d0b00c2c2c80c5503002c0c8010140c1d20a10414460201501d8121380110f5004c800164647c02440ca01c4201c408610103507240c00d18a44c0111800b020700c5030441d5120117401084400b003a580d000030008610160025030369281001491500c000040c202c28014090800c108482e20341c2e91820041804018200851246414000502145100c00d01d008401d03400d4000c004095a454001c840350103040462926131303456416040408010484219805c07490802103e5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 611630791 1250 611629541 611629637
    0xa0f02150a0504060b10030b09060d03021c02030403050106230f0102030d0915090503091305070f0f0201020d050c09040c080105151b03030a020306280308090111030403080406 77
    0x2540148a0751002031955032170400501031a094680020019690303000c11902c2d400d0540c0456000242121040c0f03c0c40c0095600943e0382c9501031100260300005078400364000d00800580d0081d5030301034001d00c20b207602c0f20700540c02201c0180308010441c26201d2000c4c0716081900c041151140c060b805185081d0448040340040c000c600c0d000c88940b66840b0122840d42050311841c80c41903c140c0186070b494502204200c0c40b00800c203807040503203151000b840000c507003009608000e041542005200300c3e0400e40142d009028000c00c0d2081d80e0f06041c2000b40c2c0300c52400c0100503015044404102001d0014000c035040c040134000e050700701c425810f400d089440d0b600b01410088410300c40c065880380710241a2411070f0025550400fa0725004421300c0300e54508003200901481500d92a0a001c50300b2440600007005c861101400c2ca000001e80d40446900c26000e06100d4050041100d9459907640341881c0d0b140c0c014030460b000110240680b40194801519030301e88410303c3e155140d20303400592188 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 611632041 1250 611630791 611630801
    0xb010f050c0d052a0c21300d050105011112091005090405040f12020316020607060b06120906061c142401090e0307020a0b030a060302040f0e01050f07090620010509030a0f02150a 78
    0x200c1f0314804420b8200c070310407a42c03801030405404681e80802c00b945030800141c58050004640412a0002504891226404070070384000036801c551800c03030000b08d0542a104c51040d44134031604542010100020703c07039607601c2195500c1c4503000b03007644a000c1c0d280c204e03124010b107081c2420302100d503440d803405450030001a284480c01228001100c3d01e07030340005586c580c0071841c42da001d451414100250000309100c0c1d00c0e0300020580310003401c8115400d201044001c21100180403c0c5a8040e01c10215410818007000103944501210560058101c0b561100e070300344200704080341003800307000406102000341c1d109582d02400004001e8141031801d10030ba00010220544a5524140000940e440d80603603230100c0034401c0c00043c04000901030360300355140109603041c807208407024030885c503a11540c80c80465406140840c50701c10380340700840e00e402405211450075828035060108840001c030040404003255111741e04400103c0500781d80f00c1d0201643c8011f034010300c0b000940c22440c15004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 611633291 1250 611632041 611632093
    0x606010e27010f1707050a05040e01141e0a0c0503040b07021f0219020105150d153303030203040320030a05010b010f050c0d052a0c21 59
    0x718080548007400d0300c495030099118201648603000104603a204030071410004541d002c014105c503505000120740000498820300d4069551a003044403c400c0079800704c1c8261a103048180300da07040c55a42d9440d0141801403000e5481380d08808210740c04881c0c0f142d2283c00a9941b10740c0d00715591500c604070300400c01413800055000d200071103424034102032540d0b0782a0311480c20058441000f081da010032122803040f64001e680c9080701740520b043c94024409039040048a86425080307007444c00b00a4000c9404042e4804d6042404420f044a09505d00c0020640c2901e48c0380e92100c060f1005003c80d0210b031202900bd03800400c014001320300c25011100b29a058640400e4000499102080c030b0007100074000e40d6143d6503030032140300e1517902c0200a0681109858001d080140440d011501c5c1c00c0c405080c14180000001d48490100009001e071000e01c400241c0d401303c0466001109440c1c2c4450300c0c2e007900c54a4003e02c1003141079450614521040040c03002015070410306540108002c480400d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 611634541 1250 611633291 611633329
    0xa2006031519080a0b010923180102040302061206030d0f0804030e0103110d1a30281502070503070624062003070b22020a0312110606010e 61
    0x3c28801c60401015214038400c400050b46585082d4401d01111210007a10740004054074010700d10a040c00b1403190000841c0c4240b410541320004800d00a1043d50b000940000c0046502d440b0180b01c80c0d0f4030f07482041c1c143c0680b030490349540000c844900341050880b010610510126011034450f0209201429040c100029140c81d0b880030004190012205107920036190805016028500101504003803000e80d204010700300790104001401225000c000324055200116a4a025041000c95100050b49074601c2a5047d03807084034400308442d0400395032201c0311141c8030391500042d00c05c544250760048061420084c040e91250081d02c201d00300304840c101400000642280d0840e8044014515601c403c00d00e4501500040600001003a0124040d0401e0101c2c0010800e0b010219503c420a454590903886c50703030002405510340440c0c003a40028800d03c0110810290001c83c0c801002c070754440c2c6403105000c424095480030111811030000324188191001c0b410500c080000750f1007064 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 611635791 1250 611634541 611634589
    0x203030d2304080901170c0a080901021b1b10120b0d080307030b010e1005040b0d0e0307120305240f12010507090f090203010b19110a20060315 63
    0x901d1201d6807010560b000d441402c030028003030b0165038000c4071440f0a51a418116203803450440c07000e000d02d000740c0c00c0d0310381800f0400c400a02403d0080d4110390078519850000303c13a41090101c2207a0710342d0416145040c0e40c8000040c0b01591820144048991140e0740d0740e0380301c01541c0001080544a840c1c401d0b80c003c10540b0b0b140000030031a001441c410400c1d40e0700002c0c10428500010241491190024001c0c1c0c9440322011303030140d00000b201c042d01e0039090f050f56100c540f009100000c1003410740310380701400040f400030204401f040032005a2085960203200350313200c614021001030307000005c598649000420440e0701d414584030001014000810000316400311585440c00d44074100c4200b00010401074090000200a0443c80040d000a110450a560611080316a0346c03003407102e006440c0c04003400310400540300b61884080ca280180a41d041003030a46002012a05c0c200c181e01058000c04184219504010045c0c92041d801040d403401c0f103510301006d2018542d0840342400c40d0204e03403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 611637041 1250 611635791 611635841
    0x20f190201031b11010b06040b0d02090a08030f1804020306130e0a080f07030201110f03130f060e06010f091802040908130b21041211030421060c0c0203030d 69
    0x10320140d100343c8440d01ea501c03203110410a12800c48017030106c014411607050000f4480c000f400c1302641c0d2a2409000d0050707a03080310070002203030400c55500011407403000107203002c106484000503102181000010828903030780001008240c0c0402c0f54165000705041070f1010442c080b5820401151480500392851030040d500c4d40921a400015920400c901c000380c00806c06609110340b07501d0740101080a41001e040303480c000d603944006040d20a03581003817265841403180032411312000c0b5034442010000025074204043c0c03901024072803203100641844000070302817401d01070f20184005034405101c001e603295081000034240030400352480c000511403458203540c41e0a003100a88404544076446011130030f0034078030a00003011600f10880408007030100040c40c5142a80390500c95003003281c4094000d100241c61030241d6400400031158910408144140280e001820a07024940500c40084600c0054540d00301d01480290145d0040280c18200801540003058003018000304103004160 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 611638291 1250 611637041 611637071
    0x308121b2d0703090b0f09090f1806010503101802100c110a3506070903140604030e010f09050a03060618110a03020708070f0b090d020f19020103 64
    0x401c52041c514540c0090745400075044041e084400c65032041441c0381c0109650700401660143c4204020303520b01042504110007500d0598011900140042c4a1460848450f0b11010030a641c00402008018400d80d8250004540c46040e604054000c040c02604806010010101d2148541c02c0d084400500b0700166248406c4024a00c0d440d51518407210947c10401040b1410f10b0b01c061084041d40b80c104250f04442e010700c1d5011190148140059000c00c00c860100c041c3c410030072240780104c07001c0000e560b4004442c031081c2d03401201c01c50705c80c10807060620707a110011303a000381c0030035000b00f4801020740c4a940079015400180c60041c1215070f039840410b100b03040381e8104807140360301c070385040c8003018500c9c07a0801001848241480105005011000240701d9451500704042d00010200705102205044800340ca0b0300c069228400d401c07a080c00c1c24850810f413440d59042c043c07840780340320700c1e480040c40107400c14018020700f000307075150a12031b080c5400070b0404038185903e07840724060380c140c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 611639541 1250 611638291 611638297
    0xf01030b10210f1b1706130b071215170313170313080105180a1101080709180605010f0807020c0f120f070603180b1302030f071409010f0308121b 64
    0x40710a01c1c0c0c240c60a140c860f5544040c41c8a030102580e101b503003003018410120394600e00044d00600381a440d916121811250b000500d00b820b014181403860300459481020100401c5450410b440701c09265002460382d1603201c2d00446900e079841010080c800c0c143d01409841e0620040c01c01c89140140c60f141c5885d012103d17521035031560359100c0c104107900180480784032080c80900007500e00b0146550700d6a480648081c0c0e001c0c10443e271280041c003142d0080e140c59001c0c0c040c0003ea0024400d45000c2440a03006a008880c0010428044410032601905850740200480e4025100701c0b042c0609109941040c000c501c1e9008100e80310015802205103d510803601d5803901500304c0b9814030030040c00381c50030152103803c9240602c0d10b234408200099045070b0009030b01e00300c01c101c0e005036000181c074040d4450a01000e9000b006000180d000040060b500130740c01c140c0d001030b4180c0e0390b9404841c0d6115988400340080c6810071004105e00d07421214141d008442440140c08640c4042644d90690 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 611640791 1250 611639541 611639573
    0x50403080313052b0f08040b180a0809030706050c03031612020705010525090603050c071703011a0f030402010c020415080c0a09060b090d06060b030f01030b10210f 72
    0xd001281c0c1041c00182c3c280048004d9007413400c0041202150309402020300340010005404608044041501500e00081500d0407103200d83c21505188a1400e06544903403210003824464070a4240c0000e00c0f074090001d9426420428000c1c60445d9208050246d120ba07802c44076a082010300c0b94001a00b0420f807004e051840d001e140002101c4c68512011480180c0407a11107100d254030689284641e0f80c03000f120001e952040c90045450307120b80c1c180100358015104010404d0340c01105042810180d0006141201c1980c0311004048914082c410000c3c894295040c01c0f2060810001e00507500a11a0711401417010f07000088407418444082d004000c01e0300000e0540d04003002d4148140780c80d030001e01c090b281d00c50040149074038180126211f4450700c48124000c110f03a640d1942808065440640140034000009603a4503100c01c030310300c0308502404115140b07039031080850090f0038129280c10580d003841004805541d0021510141910714010848003040c225058400044851240309580 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 611642041 1250 611640791 611640823
    0x40306060501030506090609180a200114070f06021b0f01020901031a0a06140d050f0601090909030c060b03030d06030506060126011e170f010606030b0105040308031305 74
    0x100d07081000040070758102a14644c414528541441215030314280075580080d000d036000752603103601091040c05d0100f0380c40042c1c000c1290405040c0c4c2d03030007c00c01d00e80760b0550903030f140c80c0c0c9400c440394016294003c2d10300281c15840032815071000a00281e004000d14600382040b1812000f403031420354a03000000184601d140d40104540d00e041d40c050080e0416680d110b96a103650395075090114901603240e1140004119440b459010079031255012184c4052940c48103010619201106d14a04038054490034001010b450340001c16607481d02c1941441903040c0d0310f08c024038181d80c403101c000d8918004110382c0b5000070011071980c10b0261040c24002c51080f0046e001d14503090700003400a030315141010f864142c2e0b80075503490b00f251714140181903500c0008007801c40741503190a2071968000b6001460400d1000032110b040c807200041404c440341d08030000780052a10b0300c00807000c0c1c0c0e502d000c0e1240451024442400020140310195902c01c2e4100c2e0304400580150316485d2500300d40320041105 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 611643291 1250 611642041 611642051
    0x10f0b1b010c020a050c010c200d02060a0f0f05070b070309080d090609060e01020a1704050705091302041d03041208070804030b011a03151e0a15031b09050112090602040306 76
    0x70024284107500e0030301b1013424418911501e43d148c0b0164030601034410803a040354a0b10100481e40c42032054103209070060400c0ea122140381c80c010303119200403005500414500d4000c0d40405101308121207540e130380440d030343c100d50700d074001c06902800803110120351400040c480c11081d550184904609540140c10120385184c4030700f80a000c4803002e807031508959004104a101c519004a80075481190f455404409540c56041c01420510250881d45d88541c13034509105000d429a041c801d00540212000c20143d005002c21260805070184e120805400522040040c80312400203190791034040c0303034254035100741d55540c40c215070b1003038000b1140c00c00c5410051042d0f90713505411005020b58844039504d1424410f014084c0c15402c040c0c9248a909950030310000360110716090ba80740c00010380045009500d884a0304900c1c0b80e2000b60310002890502004c07446110b4004419004d070954554011450070480116070f1100204042e1001c0c3c0d440300380c001c00151803440100015801800c0000ea = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 611644541 1250 611643291 611643293
    0xf1b05100204050a0b0c0601051c050709020a030e0c090705160b0f071103030f06130902181801060e0606071a04150c05120c090109030f0609021503010f0b1b010c020a 73
    0x4501c2080d08561112481031100b1b0500c039400090082c15184200c4040d4402001c5540e1641030b05e02440c0003d009000e0000300141d1886076401900001041b51010301071915242910380c0c1d60380c04110b4052f80400ca0f0808141b40e036020710002e0601d648241c0340340d02d03070010a4442405e150741c03e90300084608131200030041c51a500c1705404d401e459488024500c0c500388100d2003c5140c0018103618031404641f5080002d40310350f0303440740401c0c44d8003400004140a84064030300641800311019074106e80c1401c02096096410310400c0140c480f02614030301a85c480380140403961f0028441126940f10955003d80b461711500040d0340f08a00c2172003d05521042d100c0c418054900d080b1030710080c0081446202c00a002020040340d006040c010442d443d80c00120048448040503400030b00030300100d505800600c501500081c1c0e08134000d0b9904d03017014502030082c0c42944402d10412000500704c00060203014191402003003c120940000c030000c02e6007810343c0b030850f1440654800560310101c0584 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 611645791 1250 611644541 611644549
    0x60c0c010801121709060c010c021e010b062a0a0b010306060e1302010c02011b0c0302040c09030b18012a030e03090f0103050a09080c0a0b010e04030f1b0510020405 72
    0x1e805008905002071081c1d4103580c40e00c07440741c558070f2010350000340414490816144c42e001d40d903030984c1043c001c1c00305100304a40603464903804100030603007440802500414000c1402101407400020701854a00351180d0f000c3c1102c207410008040584240c140031070a02c40301003000c1d100450107100342c0701c002e500d18a00101200c00c0340d0f2000d05d110304120304010504061240001c81c4640a00701509030055034070048680203083e4266401c5c0200c03141c10036050044040801c81542c0c400d031010001101d079003c0540301d803c0c081c440148040e02040008040f48800340c1d610600f150706400200700404140016001701c1c030014000b1754400c8202030349802c0d26615002d118208407103032000e10710309800c08010642c51240421443d041c07540350404500210003540c49400c171103410040c0e458940c414030b1000b03501da00990307405945c1e1011038000442c81062954a25004540c941c403100300d01122a9411341f02c0a00c0c6200510305082e0000c080004a03006111000140c031144500507615800d02c0108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 611647041 1250 611645791 611645807
    0xb10030219140906150c0709020d15080609060402130e01050f09060601080f0705070c080703050705010801080304060c12020c0d030e2e03020c0a0c0b0409060b0313110f060c0c01 78
    0x4600c03c400a400b48200b60303d49003020040034082601017075840740d5081d036103880c00311103910030b02003244000307070214840d0f042d94032032260f54101903c503226841e0f491501d590b8a84080d41d5445441d007165001c14010710700f09501030401040c1c0e40001c60000c461048160071107170200c81000d82006e0780c0040050541c014041da640c010b809003003108441c24411a40070b88424000c02e02003d020002800c2c80510821a1300c1200810345101140d03400d5440e85012600c41030280b1565000c610030384008100c041d0b02100b0b0380c0c1650020359034025482d10684461024004041c1141c0c10360081000441c00d50721001881c080080c020380311000c0748001802406001d0400005c0c5560000e01001c0315107140c40d41c904201201105450096100d2080443c102e041060399400108a4070510720b000881000340005042100c1c1056402c004040d5a40320603030315480100c4190500d491009603480010b45215009030740c00c00d0281c00400045031081c042070300e961003803503158117070352180d1100b809941e80f28002c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 611648291 1250 611647041 611647079
    0x90302010c0818100c020c0d151d0d050d090803070e120d0203071b0e01030303050a060b250c0b1318020c071a13031a070207050d0b10030219 62
    0x3c511282c00741032030815110807400a1030340030710340c5030b014500d03907180b00300403950721060000c1003880a00d2040c40c000e0316800c009101c2e1200c25003840086450040324008007044094110041d0080740c41d40da00880706a40f00104020702640d071402c049000c0740030b0710080d5200b25055124212007415074020414208001c1501c8480c4e03a0087c10301c9901141c0c0072081d1004580d014444070100c080d021402403005426401600f15004d1302400001416410740047d4000d5290745400c01c40f594680c0301600b5584664807550019030180307900d060340e02e0000198401864043c521452070103454034419180303507011400b0802c441443c00302c00d100d05424101352601c49400042c04520f4031301341c0b854107501c498007849483c107003517040151305074102559800c87d1401c140c1c0c03101c00f003415900c9180030700c2000b0380d0710f07004002c421400c400548580c6c00002e60030117546c8004c104544041c0c0e55504c003166a01d006085950760030300341000000685a1000c41000c05220450841c480e504003044104200c0c203840c2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 611649541 1250 611648291 611648311
    0x307090203090d030207060e0109080a0801060e0a03140f010204170c03160e0c160602030702150f1605040503010c080714120112020301021201140a1a0a0f12090302010c08 75
    0x10501c601d1060005500f491841c09060140e00c2c0c1d4101c2c10300000400e1b400000042c29402d150089003000104001004036140c0341d1200001c9980700e100c00ca40b11083d2103070301c58014001c0390091021517803804600068140303a4040343d08036050640540d09981041d03000c0d0081c92015011100c0c41d900901c070180c03401d1025801001c05a80e4401c044085404900ca0343d0385004040005c5001c04c24100201d82c003030000d007080f113101540300e032415030b009500c1154180018014610920b0441c40c4040c0707200c0c081c401301c0c10308907119100c405040c0a400358246040d410320004120000d11b0307403001c1c0150f0f19061469240c0006a00c1c204002604034848072a0700c20001d070040107001d04071504100b100c0d040d251011000c00c8040d00f00e1005c68028030801d102d104800055600000700b5022001032120400825524504011b544680c01d060003142450750500b41340c400d102410328070307118030707038801d444d11151402d505000100b40c040d80445030b8031076003540140d445001400c006908070300482e802c864480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 611650791 1250 611649541 611649547
    0x80706091403031b0a061118010807020d030c03060305061e010e090a060f110d0e190b0121150b011404080327060a030b03010b0303090a030f0602130b0903070902 71
    0x400003c0e128840c16520560074214041c41c0c94520318200948034042c1c0d480300b410816400031100711050f41d08881d2580c20005007a1240700c9465210307900081c000c40321500204a0f1991417042600035000816040d010150344090000110340204815130103000103010b102800c00c412032080040c500140c00080d143c4904105200500000044085240c0c0c2c0140d0005040500c224907071000d032400950a59a501d00890031041c0c091003503002c6241840404200d400380c1e000c0d245001e0085000b044050a40031400c80100059050007264503840079802c0c07045e1403030f04007540e98481080f040159220743d8943d20000a0740c6540c203c800b07140002c40300c42035a8102840d000041e13580344110240620501307000e00c2c2c0e82d01810315401d5000d0031400e00038070158840d05007001c028014000d2a100c188a58240400640d2a040c040304440000c44081d203142080750840d110300200c9400c03400102d40031942003041e84c48401c4051020f0300a4000c4240b000c1d9206881e908040c901011600701000c0f0034410 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 611652041 1250 611650791 611650829
    0x80a060507050f0c1b010201180f0f1406150d080f0a020a020301020c030d05010b07020a0b03070212030420030d0503011509030c09051803070b010603020d090c08070609 74
    0x141414405500400108840d80c4003002280c840c0a50921441070410100b4604000c00000c5254841e07518248001c8807400b10001c012800e0301d44195010b0790301c8410034000d0300465030302220b9075035050141000b40c5102c08943c0d290044001e440303880c400190803080920036112010102c0380540c1000f10b170504c84440b00ca48541e0411b100d600c0224444410010b0086030141c024030820b4480c80d0004e00840d103030154200741c3e54581d40140610051549441c0012800905800945903004e401503c213582850800d1b82079101c40d800035241c441541708450080e407180c44004011403050703202e41000145081c0c0190404449030210307a00910a40090407011000c45e0b104040d281100c03107824284540b015102d07800e9400b10000d80000d04041651b410204640c1441d400240c040e03c10446101d0a0400c0c001010761203014824008101c00c0d4410010080e0300d01ca41c002c0d042d01c0317203c2d210000743c01c0d46a40c0c0300509402d0035071111059402c2000b00700411600425403100912041c01c20410009003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 611653291 1250 611652041 611652043
    0x1b0405091003021e011706040e1e0106090e07350a0b0c122706090730020d080f070309180c171806070503041506060837021306020708 59
    0x80b00d00309046d415106000610507980c94002e102100344802c15a80740d0510300ca480c00d54155910701d0141c881d070030b1480c0000c2800710380c465110907407040800703021968100a02c030340b02c1c0010b84051103c80750031408a552042c10952850102d00040c000401102e442803420a590000040603c0ca2482082c030682003804501c03032119071300185c05208214058a02110845007001000800c5d42511580f002c1000c21a00064684141e5404c080c14108009581d207002c8a6961001003503003040c00b0340a09440141018060030317032800e100d541c201c1d0601180681c03040e44ca402c103040680000d0724402c401c01c401b000072840d09070f41e488800030600c49840900000b501030416200740c0004038030b075040011a132241c0e00c0940b4031403c00c1c0310b0039588a818a0803000308140c20580c3d05507407c4100103c05c95200a46108100c101c9049803a1074000741e5514880040b21003403e0010088400b00d410240c0e007001100c0d00d00c100e4240b02000c01030301c0300c441104a10041940d5007000b025036025500900c4135a0b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 611654541 1250 611653291 611653307
    0x11060c07110114032a0c060108010e030f07060b031207050303150a080d0c140d08190203041a040507051513080724020f070b0c1c081b0405091003021e01 67
    0x10b00b14150341d440c175030105000d0008500901450425021a0304030440c000421410304803a9454002c0c00603189068580f6164850f14610711680c40341008944009201074124420012004060b2003148500c0300074005540d12900d000c640503000042001801103082410202601080d140c9605082c10a0f031020f036070b010718141e080140030304101c1e0401001110000540d40f845640140d510103c05030788003038130b559800c0d920205200040e02c0c284010074000d2003a41d10440c5c102445030b152125010340c400c110a03004c1d0095405000b80d560224007515208243c2d01801c40305c490315035503110302d100001383d4014182c0140382e90703401204082141d41c0210f03030300a81a2940704d050601c2c00310141400da01c2d0a10301c0c51a5842030081c4200003915039000b2021707115001905e01515001400c0498810a0110081c18000400d5410340411014404c0355150a518030700170f040a407a141e26000028000582112541309482d4000820302c2103082510304110107410b100c900748085050f620020382160 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 611655791 1250 611654541 611654551
    0xf07020a030e06160804091d0a2d0b040302030310050f0d0209250819020c0a0803100f0906080f070f032d0609020a080706020303010b03040311060c0711011403 70
    0x40c08100b40c01c40e803081d03e900101c0594082c100a1b43c1d40d40d0b13024081d003d030a05400c01c602e80040c02980408039071000c90070320305055100c030340d00e542c07402c8440660820403070041c85561074210307030007442002442c1c03403140746e008500a80086450340b40c0320014851289090b00238034080c0c000c0e02c0c443c4e5441d403240252090344643c120340380850343e038480a403540300d0028603001003841910030041414003a04030301442e0140c046400e0b00d925007000c40c4c081ca000c1c1d126070060820103501030024080810070030409035400a00008040c008244d54003110245a021600f0031a40355949220400071b096041040c06036040e1844058103805180031800c214403c5507200150440410100c0c24030404150120416403044188070000c4100003800c10310020008250b0480c081c51181801003070714140094464100c82c402c0d070085107540c3c2012110761094101030b00031001d01c0030441801c0c96088052200f10705c25220041059200c44150509030600900d00d0100c0341400900031002c0d0450b40710000310b95100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 611657041 1250 611655791 611655799
    0xc0102031c02190f030c1e0f180e0f100f0e04020609040609150b0301051c02030c0d03080a051501091e1a07020a08120304140a0213050f07020a030e 65
    0x15a1a1200c0001e8815141c40c2c9403890607041e0b8100703d02da0416054521080e217a82c04011213036a000303050740e1140e6980345188412241e0540c0d41d60b00c2e4400d6020150800c003900c1d142a8001d20b45003100b40010840c1c000700040950f0794104400304050341842c0b030b40407078002001c9480f00c0c42d00171070741170240c9903002d01071224000030002130954030307804226510b00720050010800f1030740d5110143c1c02011700413103d004070302c80840c0004041000c2e20640e416a40000c040c02104400c0c02d00d41f00d802c41000b60106e8150007404c620300c1c0070740d48802003904100c1c040e845e0f000851134000101c00803607400a0401c00b030711448135111220303641d0011002c0309441c0360001c0700800d030558190588625415900052680b240c0c2030f00c04000d4103956010b400418429109107407540d0301c500781d541c0c45070220340701110030300d806000003000b10b01e101240f400302d144c0070800d540c1c8204490300401c0707a2100c0010010700d1a41c4a00903c00c1d030003c404070075540310f01c591000d400802e440380d500a0503404489038a5202d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 611658291 1250 611657041 611657077
    0x6041a040c05030a0809033a1b03052203030212071407181a090c091206010602010c17060901180b0415080105010b07080405090a110310080f0c010203 66
    0x2089003440701580508401800c545050180b4940302d401680302c00c034103c1c001d0141c002c203901d807a40803e9031140a1024280e042c0302c4403208224500e00c200b030b007160440800c00800c0c0d0500c20861030000313841c9500e00a5861301d98a030140c6281d803800034100e8401c4001d0000404c020004a0342c085049060320b100400000d90703a074000d04118014200ca05d880544c203020f884400a8180031309100c2907652100c1e80c1c018803041d4400181004500c21200e502078010080308009500000e40700020070a030a0000c14201d442460b20020301c2c0740c90400d1b00402e02503036460303000c41611508040d003202040ca0710b89403040760703103080e4001c00c2034042d06108034027030008108141800413045030031030054a803015004200c0c070710880700090700f000010f1003440c0c0c0e80d5280c8000401d45040403802c40f10025001283c0394681841c0a041c844510b100504079440640e4400022144164440c0114018011402050f80d00c030302740952642171030000c1c1c4030201c2035480743c0b0582202e83d070003009451420440e4102440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 611659541 1250 611658291 611658293
    0xf020d030c0204050f0f0601030606232b0f0608100506011e05040e0106020c010c030f0203041208071b060e0904110907020715050f19020709051302030f06041a04 71
    0x103001c0c000a41c025489401d00d003c000282142c0ca044a01c07555200030342d01c2694540f0b84c019800c0303c000f030040f4400900100340e048000c601d200e44c12003d000101444501c3c022038840c0340c46122554404034800310301112000d40342c108080c0a605070010000000300709803031410480380d540b10a00c0701c411300c50540780c000080c0d072a8040d0140c4150940d522410030030f803c183c0c9400a10603402802008440c0e200c4c0c50010070218030004500c2c0c148041070315885040b80c065202600c0d04d500c040340304800c40c4010003001c00c4c5400e086150310402407040130395a4648a49240982101c0c0c00d0f821180950000345008102850384031200c04008030054a584120b501c50781400304000b00d015031010f070802c104030309000d6990780c005404c030101d030710b20381041c03d8a0140304d41c11203a40c811b00500e9041403a0911400c58004031020244081c1c007014012160380c659030303802072001d90b503080300c0034aa544603445404041d41020300c0507052820500c03002d001c062030f041e926403120195411600f0401e81c0041e000030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 611660791 1250 611659541 611659547
    0x40204091b09021e0a2307081303030e010f1d18070f0f030605180901021605010c11190f02030321040309050d0b1b1b0604050105060d0f020d03 63
    0x940d03071041c5400c05509a01d420b12480650311061300d44650300c442c000581180c08409054a00c800d100750780741d152846038800e24072880703a141000070380108820000000000c01c148018002812400d8014400d50f10310b0602400d1560b040707443da414031074030348002c10400d640311103541039491700030402c010191a250049401421000c2e400b41c245031340d000174010640e802004a4529031034030307618480110308190040741664903138810942c00074041c6103644030001d07006801d554065442c0700014201503100c083e8012606202c003064400c1c0e5907651105114a13030010031070b907144401400911640701c940035000c4402d00c1c4030790090f01c80000c2070f08a000b190340034030444a480c1b0500c0c403692407088800c0070300c400e10380041d242140444d0550340700260605080551300c5200707401ca44901d0b15585e42c181511205c141c1d095001d10081404c00200c1c580c00c0c41260a10f02003580c082c010302c1c8914080c0b900508540015001034400c060701a00000010b2424440c40c6074a036060765048040c5040345000d03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 611662041 1250 611660791 611660813
    0x12030705071d270c1c1b0b16030512070e0406080127050102221d040305090405041b03050303160519030c030b27010504111b070806040327050904020409 67
    0x181c1c000003171124440501080c02c03a02c00d020340104070a1108118100841c10000c1603407281c2c04482a0a006020000c4010811040c0440c020304025140080303e60000400c07000494101000c142200f01030601402d041c800e0401078110440200810240c4d640f21203d055841a030480320224454001c4003000420b4041d00d100b070110030f08084091008458805501005019030031200340d00c1c0440b00c050300e000c8481c0d03030700850f00b58413440e03e010064810320001c0d02004005640d083c4186d80315148500c0c52201c1400207501490103541c8900b00640e542e00d50344403c1500000b00842407003045042e01800140c7d80303211205003000115041d01e48003da0190048000710f40e03109942102c048020b95030701d03a0580100841c08401107240c3e0300d40080004481d2401c0d04c102000d40144103000f20119174140440210031a40110b400306135584000c00d00e0074034102c4040b400512221a101120503803205240040c0005d100c10a41250400002c83c0030a200200007034403460b1600e02c65400e0041c0000b013 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 611663291 1250 611662041 611662063
    0x240f040603230c030303010303090501110a0b01080f0c0909250f060c02040b01030c0e1c05010e0304030203071406070305031f2702030408030a02070212030705071d27 73
    0x1030641844103182d900e200e01100d0141c0980105803000d6443e2a0100440e810323242d064603654040c50400004540f044d80403e5104000c2c80340b04860004600f190448500030f1030208000c01c5920f40c00740322103041460310010a40a21481020b205140002042d1207038002100c0f0120440c1030601c0c0e0846150f61115031003d140c4405980e4080b0f13910340d21000c04a41c1500a03501880074900c070794011400c8440c401d510900103130700c0e0780310816070389040345d1100010480314034503141240745071702c9080c21503546240791800f582c800141081141414454040104080c001d1000a00c40c0d84c1c02082403441503500040400c000000007a000d41e8248841545181507440085c00d50340d113405030503450304c94a08111407034a020240b4250380034414001c50340b1441e1702c100c404e030868481d0b01491000c0e4108400c01c0340d015400340440940305504101070142c05000d0001410402d01e4409803243d01c0554142e1081100c6007941000f50520b180f00b4a900611010340c0010304592800070610705000132051 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 611664541 1250 611663291 611663303
    0x3040314031e120103150b0307141002060f04030c0314070c090506040905190f080f0403020906100e220e060f060a06092705071205240f040603 63
    0x325035400d25000001811071140c40491581d015907010030700d141e0a000380001001c80c506400018000505900c80c0c400c0301c0904818046500018100000d082001c250801812541d040034075401a14061000c40c21116050014040606100c004066038020040025050100100e1110200751056010b420300e5402c1414007629240d051408001400007480b40410460038130010070740700d140a216001d1803a9001c1e0080c1819509844150400c43d24441c050300d116100f40d031a0004100c440005041c15410070042070b964a00f98410005105806400c283c0101034000d12540825007288026911050444a03940000d00b8800813211503054040b180030814141311103d05c0840e000034489000380003081400b2000d40d1050148a0840640e11640c800034541d0300041190101045001c04424804620b4041c01280282d20b0400e0360f00a892840000ba07030820380301200c8105203d4181c015030b080072204001000ac51804142000d90700c1c8007403107241c98030100c95240c1d860341d02200007964010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 611665791 1250 611664541 611664563
    0x9050c1002151f03030c11040501080f01050c03060f092a04030c1202060f030a02040306290a03050c040209040e1b01090b07030f110c030f0d200d03050603030403 71
    0x30300025290048620712002d0741011070007003034590030800b0507030203603011070444100b40c149103840840e01801d0341407007030703485030104120b4044940f140e01620703000e051031034000c12103903100141e418210b500003010303c04048010b00610140741c0d80d9402c02041040100e079800c20a46a45203003002841d040200384841c4040d20054042c0420881c01503c00c480c0100c28240c4256a180d52005510604d424002d43c460010099800031074104005145c00084c0d400e4010b080c07d80b80c0c1e40308012504281d240b00725010444d00c50003d9a4480b408c0c051100c0c1c41500c1250040c0e140d0780d9815540c0c201900340c688529000704141d0074540700e88d4009450506160104c034401000c40d10b4034a84101541758140c00280514400310301040041d085400086d4507a0784c3c103c008003000022264210030704e201884074004c124041d08196001c11080d03a80031141c2c030140107038501414001e03128103075101c400001d100b4219191320004402180351381003018103080c0030a1560321003002030b056100d16003000b0031a80fa06 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 611667041 1250 611665791 611665819
    0x20607020303310518041b12030201091403130501032f07021807051e0d02031501030501050a0308030a020a03090f11100309120c080d18051e1009050c 66
    0x583c0110002c501d10041c0e00c02529581403000c11503040005180312950000402c0002c1c0c00303858a14400c40c081d04030300034015200d0841c46010f204200045d00181c0d1618800c000b44800c2d040ea03440d9101600c1c00031480c1c000081c0203084503814130701c21a07040c50b80d0340110940c103641142500e0401040c1b8461114488192025082d480c5c010503c16030142c4c1800c3c624000201e46040b969005040d02c1d121641003500c0030086120b0b00203030602001003601c0038400408003d405001450089514040c884446441d620005048900580c0858818a213094042020400d000300303c0350440c10802c0c0150b583d4031078601c1076001e001210030092000310607051500610544050028001504035038000a8a1b1076210450681d03a0144001c3d06101862900d006124018943d100d400d03480348004600300180c0342a40700840e11109a46010044144000c0d4100131041c04020354131003c80241c41405000000c0c00b940c0c50020440320b523040d80c0d4602603401884401c101000a081c0c000301501c01c0d52140b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 611668291 1250 611667041 611667097
    0x3030b060a051b030f070b100b0a0804020f0306060a1e0f060203070c0504050c03070804031e090e0c13150903051b130b100f03020405030109030e010f0813020607020303 74
    0x10380d281003e900d190603030200da0030001008581c100d12900e418141010b846480d001c114880c0a00361280c681800100054050a20000340800d0750716a25400568a81801840018101b45010702d00c40c0e08500300300001a030b03c080b140da00391b070700d0b80781d4004106036210150900101d050f007005002d40400c1c0000551680d0010043c0780080c80f54800c2c05440b0365a40600c001d8610079030344440c660405100080703405202e10308050f031040c003900e403200302d6940080c41c3c000140c444090300705c0003403455217081c0720040c22010030340d03003181c03c0c004411f2174200309a13503000760160a4011420260311440c918000daa2159210001654001c0141c0d890201340d02d0704001d122007000c000781e0207a0001c00c15558194600d02c22440e5400014100c194100d9201104454101030001110709156080c08042000e4809102c3c52020521940310500320800a900140070801c0000307280c800c00050400b0000700076022107803c0820740d0b041d40c4c01a140c01240c800070341180540c10343e0b0119580690740948541702 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 611669541 1250 611668291 611668297
    0x3180825030f030933050a1b21050703170703021c05063604021201050109021e090108010e0712090503030901181119090e0c013b030a0203030409150f050d03030903030b060a05 77
    0x140c00009c00c0214064990654550003030500180220707180c040c101b8000804079040f1a84404e062900500d480d440c2702450f0141d00a05400941d05039a81003000b0550525408205540640d040b1090115080203c15007a403980810b036000c2c8003440c00040340031902d6038090000d0074903445000f88085d685808401d002504a185048512078840c1c9100e80c2c403201003400c4600c03021040c0c2d5440c510340c0c03c00c440c0c01030121000d0300800030414035072100c10742040c10f849100e84491040d8055652814222074040c29100c002d079005240c82c0c00c3d0b001c20300004900710024160004c3c181c450781c9101c0c0501d40028a03440c1d050b48041c0000f4240729a1078000c00011130f40750f80d00b007002d03200c11002c2007001c1080511850800e940503403084000000d0b0f60901e03c0041c0c000400000101114002c0510713a0103c1d0030754200382e00c00b050a80d01c880700f45096200ea250300e0000350808001c01e91910f0b14200001e200809952405803e2641d51040482854402c0e0412490504040d240994405950100034003e80c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 611670791 1250 611669541 611669573
    0x1a1302090307141320070605041518142a030f03040b12060609120304210b1302030c04061203180825030f030933050a1b 53
    0x302402c14049040c2d86aa815039540d4540500601140302080031032400a00450681601d0a28100c00c040000311445c0010410984294004076207400d2914141c17034540105800c006065041c0102c25560900581e075119403540c01c0101c0540ea25240c1420310304001401001c1c074080030b29150389240180700e024141298103400ea003180c0701c0d0100d0f110187e4583c002c900400050140800216814155100119800030700c000c03c45407070400c0020000d0400e0a960b09510720742d070400f00d0108013052070aa011000d66040c0040e403050404a683d800303d0010000b450382c030203018850b48907802e544041119441c403e002030020000340340c0301c03080070b517079412070440450000789050300e1228210440c200071022690b0f240700410009410440e1965505000c0c00f04115444441c480040072505014032115424026281e005985040c03032005800001d8407800e480200b20004000000c120b4107000441c1000310070316006843c0c4100a20448001541c08442d081100100c0c2000081c029407a000500328 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 611672041 1250 611670791 611670793
    0x23120a021b01090b070f090f081c0e06070f03030b12030306040c09080d0507020d060618060501030209030a06020c030408100f0506030a03020a080d0b03030703110c0d020f041a13020903 81
    0x50140e00341414280d0307042c1d080050407000c008001c2080743e4000d0b584588a070300746c1d007005034960343c0b0b40107454210381c055800300d0307419803000301414480c02401c650740030700900324a415034400070108040390482c403840c600103041e00d071000650411700d40303e5808090307a60001403600340e09030840700034031b540c07a00241e41042c4180d15141c0c0c096030041c00707024a1412224490041c19031200d007424103440a03040030900303a80211150321102c1c0065601d1149602801304250a110707000d500704011421110f8130340059050503c100321b17810059400003803031011958004005650713580515022420f5000d2a0701c18940c0703224150714004905000d42010f42d013488940b81c20809503071190f003003550707a5042e00703006005a0441080c00010541d108010250540902d1010460341c198002091079580184d00c03e400044100404580d005003c1c0700c03050024200302c0d5050703007048851f000269503e8600c0065032059554904003804110005160708230700b00018140311102d5049100e55002c2d50054161900c2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 611673291 1250 611672041 611672077
    0x10b030709090b1501140d090b0c12162003031f0506043003110610300c0b0403050c011d010309050f121308060723120a02 54
    0x5455144290240240c015026600301c0d21000d135200d080d0a40e502c0741a04000e40c3c034401e08640702c2d100000704061083c20b08001200c00039410040382019014140f0b03184840c2c200b104402420070400116040b03240c5845005003115545010307070750020407401610301a8998004903850ba400403000e50b1240340001002691401081c412130803a030020300405500840a000510080c00c51094a04007005c1034055502e40c0001d0044080540000800c11400100390060340307440c0d07010038052a0b030440c0c103030034101380210b00344640b04c031880058007c0e10f4a04a9102c2a150450748411580c0065139040341d10607640039200c542c50681507201d80025980342c0300d405011051540702e000741055440410b00104028040032004402801000342c1c10745452180705d843c089a5002800700c04e0300c0f20032504920f40c1d5070001200d81411901140d024a405800c800300b08000750342c00452000809072044500041e6420a51381c0d9495030181903045021031039404100700c1c0000d4540e004111050f610420750075 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 611674541 1250 611673291 611673299
    0x606080604090c030f03121a0f101d0102121b070b0414011209061b02010c0201180b04081204050109030809061018020f030a0504030305010b0f0a121d010b0307 70
    0x1a544101c0d4014020b070f240c45010008a42007042001d409440b07807030304070b10344205030340c540d001e0355000b00d1150701d01c03500142020f540e481c102d042950f0000b400d80d090084c03548076a002030b080c1c0510010400090806110b94045680309024101c0030307164a02105855940f52000c0740c002001d0305c00307041c09074428480080f0306941044140c40c1210045c010122110000c0b000446450700c0300c2c602140015181c8801c6030005110780203807109016aa14195460441c090000f0f00f501c0c000250407096915140d9100c1802c8040e150b5001c60680080c1d0b03034070441d116031400c038110b4403469041000b010982424041007007010340060041c14060fa84220064954041b11500c030b003001e84000c1b0028604040c00c02181080300c00303010320304404840c0103052022010000c51143d000702c2c1d4080310a5a50f500b00001c158051045502420b0990303e041c0c101455030080c40850b00c140c08014003806001d590568501ca00e60300007a1114450107002e50141c2e010f41c7c0c4090280045085903131180c000d48030042 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 611675791 1250 611674541 611674549
    0x1050c0c18061809030f07060b04140a0b06070f0f02030304030c06020a1b05010c03030b13181208010b030c030a06030c061206080c01050a030b1903050a05010b030c0604030b091005070306060806 85
    0x9400f0300c035210017540c600403036001803900070783c0102e0040300c3d0140c8451a40301903030b9480c4140520440a10610350940c070744042c8900480e0b5107118403520940050100501142e00e8070b81c09100e50754440e6260400d070b166800000c0c0345d4002c40d40010b01c55030b0f0500012030b90a501113100d0546034815001c650b2488401c40c5401640c0115028290010300c0340e001c58800b180c403a41014901d010040d040241c0b07008900c0e4810305591729009030001c14071652130300e50100524485c8107401c0d41c0383e602d411390380c2d9410000c1102240c440504503501100000c00803c080380c1b0a80c4c80381d80115804680207500300c1d6100b5014144101007a003114102d490454005511080803139034000f12401690b40924000c0c0480c2e0542c0145201d00200350042490609000d03000c1889502d00c0c0598083d0b80100101201480c04c0c80c00d64040b01d183e030340623801c5100c480c500d90301d0300000d032020360703600003490034842e030b201c5811516117003510119410f0142008c0901441d1601a0b01c114252200746d0b071303400c100e562184240 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 611677041 1250 611675791 611675839
    0x180d12021207032a05100b120106030b0105130204050a0e091501030308011a1e040e13021f020c0d21050403020a0b0a0c0512030a0605010c050c01050c0c1806 69
    0x940820300d0704036080055207490101441504c550100307000c07140c2441e1501c910b0800c2c0d6201c036181c0c0c0340d9071b4500c0e01c44900e424800702c90071308801c000030f000082c110743d00c80d03c2400062241e940118003580109803000c07040c2d0141d401606002d8400411555165401e40c1e020307070103540000d001d014142c81e04100b2440c5444c0c45059a0f0552124850344c3d2038a402e608140c4d500802110a071a010700120b00341202c2c5003418003007034044048150701c8a0a207110004180b00c05403100e04543c1100d511800140c03201c06000302030030b2048010810360744c11420240c1c103003070403032004952041d0140802c0e4104800582c000742c15a50b8102d0403000100d81600a4410f8850740c04065070011404604001c20801c500041c488141e41d490503504044103684d850b403609000c100814000c000c04010440301d8003542c461200100300901c1c0a1111146030380f03510780c84803540a0403904100c00000d05410074641003211440f0b0f2140904a02440712611510794034054081d601c49104540c140c103c660456017000034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 611678291 1250 611677041 611677043
    0x140d1b05090c12010302090a0902270907061209030311030f01030606170a060209030f0304082406010f120213030b01050405010b03091903090906031505090120180d12021207 76
    0x5401d03c590175a02002003641c402464941c03865160704981006844020a01c4901030000f000c6c0511903489044042440e4401410030b00036a002441c00c01c4102e078042c44041c04940c3c86000000c0c03076809030600300d020b0900c114868403004800400d0007800566039403c24102d03801110100141034544002405050903103440d0b00d81e56100d00302c2c1d00c01045180d40100b00c04d0070010308540002d101085182d0540d00503074083c2c03003507030002c005038000c90200e031007800b224000c4030a0480d85840c0040000e0f02d12580c5524010400001980d4032213110780c41c0e41140c007802210320364011215507910705007070442c8090003141c0c06903040100004150711700c0c0b0107032801005a6400f9100002d60aa00c14400c03490b124000e804001e80f007100050768040e680700d444003440c000d4002a07488800c140800302a95009410f0505603032418a0544d44522958000b080300c00401032225640c0c2c002607c4010529054a0f00980c821000e549200030488180600105121280c0954010f8085018401681d00414070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 611679541 1250 611678291 611678317
    0x120a02030a1d030a080d060f030201450315050103020a0513060e0f1614030a0c0e1305011e0f09090302011806060810050c04140d1b05090c 61
    0x80303205050741c05082c2203802e1020324030342146100c106500080ca0b000304d1032002d5941644c0043c0d50405851a80905401b030012140900280da00e1980020710942c000269500d0502c4201412031440d00a94944d5401040503100c0040d600c100c01c803102214010352104440a40340c0111001d0010f4050240743c1c101c0b0f8006101ba2081880c0c00240401c8600046545040c2e81d0303654000b2440f41200442c0b54029a802d0700301040614010510350b00c4809401030706014401107150326844040c40708100c81c1c0c462003203030340803416250400c0705840b107215645545600030f041654103541d52107158032a40c100c1e00c000c0c82c1050030301300c08440424030901d50f004079403020000b0705007800603410582003896203a10038400014040614130300d600c44008204412140646c80340720804c40c01500700f0030f2030218091814104100c1c18521189002c5101302c0c45902e01c4c0d00080d4545800300e603240021104c02d039402500a240202c140170020000721524016144101003007004203c0141140c801d5417024242c0b15 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 611680791 1250 611679541 611679547
    0x80c18100308250c050a0b090306222a06090f090915050405070302040c110303010e13020d050309031204080a030c060605040e010504060507020f1f090c080c03120a0203 74
    0x20b20b407900103901043e40404001840350700c850800c4200700d03400d01c5290149500c004001c1c103180130044a03174510f911041d4608014882824540d4021034040d403c8000d64075407001c2c9110306120583e070050074650180c004240d410341400c0c03d01401084000660303c110710410303030507244c403026240400d95015201c40800b00f03c10911109506600044256009410300502101342640502c02d0300c2007150112441d800100d420030850400b4058180100c0c800c0c06d01c680b104100e80e80d201d941c0d0005200300203850301114003040082c500380070980c1c822500134104810303503030365414929a40d6200c168502d01920a070782b0b1080800700d903c015901030b10700c403001404600740d81e80c4080b10020080b0300b040d036080c0d5403000c0002c2c0d07a5403144500007440c104080085040c3ca0141400c40031640d00400d45429500520700420340070001080a04890100301d034103240c0c0c0482c2400d540000d0040810050000441c5000851044400280300c034580074101c0458000204511109007540540d416440c0035920074 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 611682041 1250 611680791 611680793
    0x20f0a0b0a0b09130210050918040f02030303180c1c0303020d0f0213080c2b030c0c03030903052a0d080d140f0c0c030a0c021306080c181003 62
    0x90020540c01c1100c82002140c50360304a00041d0284006031030040035441001503500c21428a60706d01c025a0225003406414203080c20041128201208600400d0503125800034080120045c0c16a10064020f4112a00c0b890b0411002070441407041000c04503100791000302c07103a8580715200074079207200d9114584401225641c01d8001e0b4203c0390752004601e480f0201a0a0001284050502601000c0c00714042c10700c1d040c2c0603801d109101c000d99000c0c403002c4803179000ca080e04e0304240f84030000b42020040c541748541000c49880033204001041075040540010034540e0001c0c0100a0f28041c0f000d50740d8070546800303c40c0080c11440c0c8070b2546407a04101490280c645611904241805612503514022034000302c4c404840c0c09008109410351602c06001d9500512804a58826101e0050502d0080c0351000141d9a019a42881c410040c07104000f40c01c5445202c07060b803c824203c10140a01e603240e44410391500c101004d9103000398501030180c0800c514405c2c0140c001c1318908030480c0d100e421 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 611683291 1250 611682041 611682053
    0xc020405130203060a0c0f0905150c070f030b0f0601081608100e0109051f2103030e1e060c0a09050904030221090114030c090405040c05030f0c03010606020f0a 70
    0x10082203005075240880911001da201407141c14410400403030f000500700e0404a000d0103000701c44006804008a0b610306000c2c0e91590720010b0807855094451644504003149030741d00d0804030750030089510900603c000200511580380700d026948040c0360074580d035603074401140c681b1070490321340301c2803010340760908490341c003a030b90040e00302c503403c4a6488401d4031107401000d004002c2e445511655510b008120310460702c4581c071444405080c0e807a400715845c1c603450301e1402c006202c0c6e4021081d40140381c0d600305806544200d000030342901c140d4450320a4010160500c10300300c0d090908601549001448401e11402214140800ca8032200f24081c1031000b40a2800002081102540f00301c408038000c070079051440550b0032000300f60040d03403a4580000100010810380c80340e41e07003000a005102c9000d4903035098801c41402940c00096550b504e080c02d0140000c242e110641501401402061b45100440e02c01d4581d401a80203100c443e0b612001241e07288000d0034061040d801950f444400910 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 611684541 1250 611683291 611683301
    0x906031e09051903270501050409180c0602010c080a0608030d020309031621021b120a08030c0d0b0901080a0b04081911013c0908070b0907090c0c0204 66
    0x10160049480780c3c2e40c5003d58100d0380050311070503000700741860a643d03c5050001d6100b02c01a00e260390000e074003803800d0006003141c001c40c010351400a480c1c5902c0b121030548105103102c2c042d0004070120060b951500060700800c008104034000401e800000740040440d4000e07641210a098011850042c0144444000307401c0500103a969010400c03025021003016941e054229001d8501e07002c5c8042091002070341c2d4280c903242c02d800d542202107131040c410b4900d1003000b076102040d281c85000c0024240c940d0b040c02c1010b5802010040040248140100325401419240075411020403c0521072010000e800c032091042c1c19240d4403524025001400654030550402d105010b000c0c1803450181d65180344024820181001800c404042c090600c000d010b403404041410340000c4ea90812040c040300403554035900164900c0a420403400c0d20350650f88590030841e00544d42e6916800103141c004000c4000b41d84c0c4070264490b2010109480c4520700c10442e0000243e100c0d03181102d02e42e030038040944 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 611685791 1250 611684541 611684543
    0x60b031c030b060f031e090111042606160210020909130c03201305090c0609060c030c07050a05030f3307020a14011104050402070c150f0906031e09 65
    0x240f818000e19161034184000340d8010809040360b0307001081a1440d0404090004203061550303070420b0025030180d05148101d034180c5030300340c1a0840d240f040c071402101c10213184c851241e2603c01c410801c01c0f1001c02031091350100c0d0307030f641c00e9842c2194011110011782c010b00000310383c071800160108542c9000c41031034111a512800020b0342d41566a20384020108036020164103180c903400100d0700394a01840e1021514921100c04c0150342400c405881e900e688050641340106d00000b258012561550250b400c0f04001d03400310381d0341e1900528519156881c0b07109482c06048a281c001c5024540803501d007000ea10a032000380551840e13800d83c40c1280c0101c6800031005d0034069030105c800c1c00300801032845042e03a0f40080603d03840300d29100c2c1035041d4401416030300e039242c4107150b00690702d0042220101c0303104845c0941c403aa9503041c0706078058080e5200801042d00030705800405900440300c00b0005440d9140c140106649200c20380948150282800d00f100c800001c10044d1115540080102 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 611687041 1250 611685791 611685799
    0x20319030603020312030a11040e040f03031e0b0f22020706090b07020c18060d0206031819170f030402130912120513020f090912070609060b031c030b 66
    0x440d55030f401003401c100d601e0781800c1c400034001040142100c1240650092040c0e030302c2c8941d2030a854060078298419014000030031000100d54042c0c203140c4030360004001601041c5200c4051050742c2c0c3d02800419202400c2c90164502034241801460031040d000070983c14550000d40300004410b030784009500011084890564500b1103101282e08600424829079103a002480c1c0d003070484041203d81542c000c2e1280c0c0000c1154100000d5448840561441ca981607414036205e4480c118024102a120381c00d07030b4482c0c8a1400442100504640448411030049a003840340001d0b02c20b0708181c9109070007041225490800205006007000f25550040700c2920303100103030051ba02c2c0c2d0ba40c44031a1014014600240c20f500c00d40f80c1c110705920655410031401c03000302c100c0342e4140c5c4c04188240030b1116402d01c1040540300203179002314148100e1070001141d0350f035665500600d203040002010040c9081c3c83c1301385094070701595828002010748540d64619044a02c2007086c0d101100036140c406580307500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 611688291 1250 611687041 611687051
    0x110909040321020d0515040c0e01031505120c19030b1306150605031008210309150703050f011d0f090102160f110607200409120e03010e070602031903 66
    0x14800180301421404605842c08615820075100d845503400b0841b188512032450001c0c04001e17503401400040700780c2e03000e00f0045402042c1282d403900c0c1c0c06244e440307580c1105811421404809010901c42510b51045a420280c0c00e0003132020341e0b800e0441e0000a040c2d80001010955401c0000c410382585445031002150980801d00320705100809076100d00d0200310048244041500b03442c0c0b040001e03003450300c014071440800169004690908d442181d182c00d8000000c120f2064080c4804000b600c1c0f965074003c0305090408004004290480f0441d1a1020440020404a0f81c0030208510744039940d841860540382d90240106189016114900a641c20803902050101d11003170754200718012944140c0342c2c2210b04215405840322611035110b0380301008003900040c0c808107120000d203055540005810728180208000b48100b00010340b00022a007090481309034000030714000004160f0003408400b202c0c02800c0d0341d60515020b4140560014440c000841180742440009c6000718980491 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 611689541 1250 611688291 611688347
    0x11030408030604270f0308060618040506011707091a16031808190510110a11010612080309070503030a170a0b1206100e010303090611010f02040b040503011109090403 73
    0x90802c1c4e10a41151503071600f988040034160001d030030070f0348400161003007480c1020800780207541816a2000510581d0781c0e0010807956440703003039030000c0320603c809090140c0c108600301400c02034072446810761005400010181c50180101943c0200043c00b11030500103405540036220081c4491485020a0030807100140601c41049075681130395881083e14074520300d50034600e0070841d40103140c40105003051030322886850304901f158481226494085802002e2500c4203001d04410780c00a264490790012100a003c400c00c002d40c0070744a54811600c030681d0390800d26489024212151000c0342101006110303401000b44415440002020002804450b1000041031090040360f591495032000c0c2c1080400584000d60401a1120811105103903266940041c59403040c0d004003010025040765180c02c00300250003640c0039100c4040c0940d00e03961940d0b2000715581051180d24030a42c00d080348a0140a0000100c132a20320001c0c25040140c0d65988090769902c0002c0360310700d000c10490203c04 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 611690647 1106 611689541 611689601
    0x14042304030807030e030f030601030b01030b06430c1202130e01020c0a1b0905060904110a030b04080405040501080d091a04030206040f0911030408030604 68
    0x2d40390781d6000070480291801c083c01c3d40d182d100200d10407410f600f13504c1c0518880c1500381c1c1c0c200803108928004400780c8004070849900300004106008109401984034034628840080901c00395849881581302c001082141c1e0040741341051510007000388221580c2c0003010403c07013030241d8040310740011300021000031000440641d9420860050399003901030780d00000c00030041d43d00c0722115040c490340e2aa80010762a020140150010903060a5803140e00d0290b1030142645400396601d54411940c1d8044209180c0c0c003103400e4200000083d0441e08940c4a24810054070351154640310501080d514107802920080d04200150340d50250b000e041082220040e44000104400b045206180d42c4615000039401c030000040209001c0520143c1004890018104001d00080811080c2c55030200303403402007154000300302049a40ca095046812038083c03000b5500c03c0018005605 = true := by decide +kernel

theorem cover : BRFrame.Cov 611510791 611690647 := by
  have h0 := BRFrame.cov_init 611510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 611510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 611510791 ≤ n) (h2 : n < 611690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
