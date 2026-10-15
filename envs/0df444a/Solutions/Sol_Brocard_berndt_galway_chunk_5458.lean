-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5458
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:55:55.767593+00:00
-- url     : https://prove2.me/submissions/e0fefae1-8053-4481-88cb-f605095905f1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 981474820 ≤ n < 981654676 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 981476070 1250 981474820 981474827
    0xf120108160303170c040b0a0806040e01020a0e09040f1a010306050a06120204090204110313140a03050702120a0c15080601020c130b03010902091e01091401120f0f0b1902090907 78
    0xb501700e8480321440e42440c2d200e4000c880f25070481c0142100085c000c4060040c0380c20148961307030040c54990021b624124101401030701c03040b500c40304c5602807c0c800d00001c051100b1054404100c070b03805204c00207503221610a01e9000318080c0010b55040341b0b0f000104100c1e8442c0c0c40b84030202c0b01c10b0415421000c0141c0c00300320051100000903a00241c0300c4966082d410300d5440214461143c1800312a14100c4504010924003020480c82c54580d000e08420f0000c650003100740e0790729507811280c02c4040c2858405090030640010b0008004000c82c600124800f050100b100720301c1180e699480e107060342c598004995850344c9102d03207900855065001d00e02c401d031759041481a0f01c006400412520400d90100710345082c1240d4180e006c03960400c4071804582d66000c0030f03004040d5807506002090715007103021710100c2c042c403403e88680e021a880c1010001c0c02c040c402c001e90303000002c0302c00c800e00030700f0305055004089174a2041403a11070030090700d40300b5a100341c035890341d00a0304042e219036070f200098 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 981477320 1250 981476070 981476117
    0x140403120c05031209070911070b010506030603030d0c03090b071707141c0b0a05010503040b0105102c0f0d030203180102011104080c180124050f120108160303 70
    0x41c2c66034003007040136141e0103042200340340c05160310034028807246160840003001c81b00c480c102c00c19540030401810300171070300c106d07011819540d088504035904d440b20390000b40766200d0704158801d01d41c2800c502e511400e406030b00c160720741ca020b40265850342d13031102400c441900020a40b035501e40e000c0400300780ba80e8440d44546024007207031280c143c5420184040700c42d60803030711001d0412464548410502505024003040018003003820a14103500303207a2b0f5008024141400348038040c40007050741c0010f041c802e1030244074000c207100808260131164010345a00c20541403c540c040c0d60621000041c6040c07070ba89181f0856059806581040c001429540d41c003020401294110341d224141141c3c0070230f40100802c010490900146000c2500605202c1c1c0c1003c0703000e0580310310400d0801040600170084100ca1084821541c0414000d03041d90b085c0ca1500448051491880300031440c0391401d08218101e82c140c0d0025011580080400361400780300c804140001800030b0111001c08022240c1524032 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 981478570 1250 981477320 981477323
    0x2070c0909050616033e090102070b0d090c03080705161a07020d0210051902070f05190b041202030f03191b080f180a0501021915020f0a140403120c 65
    0x32950b026026109032443d40361b80342c141d10104000841c25803410070800340041d0348180d840e695082400e400000707501d507142031041404183c1d000a07200906981079015825003a885400c4c00049502da0074a5620b581283c4000c842034840c0d1001514031862135a811001c4504400030b1168460140311603081076008144100d801c00d0300100c1c0640181c0c2d4084031845910810740c0ca4a031a80c0219628004c0d15050b61381807800e44d041031314107100604140040f8400c3d10780584400e540c0140344007511034007040a500518600902207000703e01000e222003040310b043d000b18111801c50080740b0380b490f12413160414020340c40d07502c03402d074002290080104913240a61030030544190a0191030303102095202d04010711881d40001441c0b60b10240701f0840044d150016903580245a0a01c00003170360350248203803812480400d14a0b5901000104080741040b070b04409001d54032420913000c001016000110941d000c20100f000122849210b80b055804803600302000e80500c5520725001d45074421100700 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 981479820 1250 981478570 981478577
    0x9060409061404030503040510061203030908130f0602010c0513091d010c080106030515010210020d1104090603020a1d0106031e0e0d0912030206010b0c030c0f0102070c0909050616 79
    0x4160141082c502e103501c03550082e15016980c3c545031400074100b038010002d14104610b420710500600707142c11000706400d0340c18140091410f9280c03e100480b030003100480c25100c83c142030003051072101c4000501c00c4450940013801100c0000109980c0c50103002c1480031140c072079000400403078511360001e8035441c003101c4a101d04c010070740014509603000c060180380424024001000f14951510500354012035140d00d0b100454480300000352109070180d190450103070042000c422000c2c01e42c0c06040324650313801c041d80c0d45654030200b64000c1c00152100f82d00c14085e0080c00141802522040150a60078203c1c0c01031a030f0815206600924503000d04a01c50b400505a010354103555100356001c03a081d1200800c03c484940000a0080147e5041000c034901380c40c44520001c1d0300019528103446030440c54544030040d03040c140f480d5009118a4074014070a209481c000594198001c0044500070032046400b961601c00d8a0282e44810b0402000b55104a0020729410841100040041407514 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 981481070 1250 981479820 981479831
    0x20408060c0901031b110c0909030a0e03011e050103060506010912030c06090b04050307020306181b0d02092502030a050708031009020a030f0e0f0c060309010f0203010b090102010b0f0906040906 85
    0x117401c03440a104e190181c00c0418403808000010040030060062068811501d85056150001c90310f6107030f0040a003c90107000342814206180c0e0360a401082141c0c482480c01c4008029400c0380902401081c4419076941d403500000c5506948210403400070b640c006180080420f840c2d030340803114a10400f500351225a81c40e4120400900c944070424000c83c003460040d51a1001401010304001c005089100098860400c10044200c046824284a00a8610048992090008210344a107421402544220140104054407200317600b840111049030342d00100417450b100040e130344c034400e140324280030440074440207002440c80d80082d64400300d100d02c4491500c0e5942ca55405a810a00520000c03a440314001b65420380b1a22800d050640c14070010a80c0086510045803074901001c00c030b600801300040010340d540002d401902034411820011580c81d039691181c51000d400c24034100f8015420040007418500d441c960550200c2002004c003c420748030041000b005024200088401075101c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 981482320 1250 981481070 981481091
    0x1303090503161e06140d02071208391602101d01030203150d080c0a03021b04140129040e06121b0d06181113020408060c090103 56
    0x2448810307075082650403480728440c1410000500141e00780000743c01c22940500400685170301c1303c00f03100c544d10516021070395001c8004190000c0e224104024010700c0ca040c0c4107250030383d4000070700d0780b09880302226525000d51000031003101074501c4201c41c018010307c01f45400b5400d100001000914400c01701c101c01079900b0350100c0e481212074155100450200d04000c00350402c517882c0d2140b41802440d086255241280c441d004415500c0c0c8060f000b65244800d01041244090031a810034403100220781380c118003894029924040900e540d60700581c08041c118040c00c05011340c4200d2928800d42d82026030030800304034200260a1450740003800c6008a03900c5000f6604004c1015082029401c03500d8074100b42440702c503403d07501c3d400c031050b8000c2c02c03a504502080019401441c0c81111000001c0740c0605010024011084800224141c810310400c200b201401c1c0e40700d1030700c4003522041d54169411902d00101d0181d4030070301402c3c0d000a0b0020b010000301c84014100c5c4a414100011300040a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 981483570 1250 981482320 981482323
    0x1a03071205180f0a050c031603112205010923040308061c060501050306010f080a030516120201020903100b0a2c01080307030921081b0f0a021906081303090503 70
    0x81c400b40f050f50404944902400014492180480803e800420354011140ca40c40b088440ea0f00c00589042140603103d6011b55440145c02100b8441440c0d400b1440c0d0000c0351359009003402e00c0303008a4075207071031041a283c1e642c1c07070b0480d4200605c40c1e41681d015a07e544003a034030200f00a10b003d6000c581c0d2010100c204002c0b096250b1994002d24001a0560600782030500c1c105d03040e000f0580f0956000810001120001210034084d681840e00e00d4464045030350368040c0d481126002014401d500d400001220750550103810005800c03401c940740c84014040410445180d80100e03900301506001c203100e0301407881816503d120003100030f074842d856800510310302010300381c01080e041d4000190420030b25501051980240050040e4020381c1030b0b041140c021f5542001000503c000c4000c1002ca45c91316240741c0780001054180c096070000d0200780000c0b80ca4070b09240040788202000319407240c41d0807020421600352000d5464064045d242e90b40004041c0c0c082040c02c40802180e840c0206950300c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 981484820 1250 981483570 981483583
    0x618012702121e0102091801290405211b03030406030e0a050a0501091b0b03060103050601020114190e060609150a0f03050c012a110a0905101a0307120518 68
    0x81d0f0005854895a0040062400d20040d8140303480d4100750040c003a0303400d80d030200d06071401c2043d04a00540805900081c05025076030207540e0001d04c0e108200c0006030002c088076030302c09425081d1621494100c03c0f03420200f5800c140c080c1c0691090005100f100e000343d00803040d0650380401c4920412aa030740b0207250020301002110143d444588100c100100c109071944203414441c40e41210a082082043c9a40001409541090784400105060380d000390b01000c0e2401a020003501c840c0b6002c2c202d64000e40044811645076460200549000b010200f200e5002d40001480c0c0b000c02e45940300d02c61741c0c143c20007401076070010419038006a0340f2458024003000310b03c41d0000d002c00c0c901e1840050a00d04a05003510b040c03070700542120345000c0c000e03680c40405039030024114003007400c0807010441e900000c2d008945802d24100501500000304801d00b000c03a02170080501c05803000c510706100301d001c00d440400c0825a80d406181e03001120750807155101c64030980304101460303580610f61400d203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 981486070 1250 981484820 981484873
    0x7050c15073804080d0c0c020301231303090b03041119060f1b0b07030f1a040c02010b0904060218060d020307121116060e061801270212 60
    0x500c1010003500307518002d59800c00d40403865030705072070346001d841da2125071240d0510300c1070f00790390303094041030441c018140305400a8005d4000c0054040030540200d03d40c4000500042c2a0004400501d1151160710554803c80c0c0c956140c0c070400d440e00b480b20401d60405001212461f0b20010284000d44404d00700054400d90300c01460010703440c10a0140001e94407107507017030400c807009a40e10801440800108805503010114480a603600c4200318004c100b0048044007036414400d003a00c801c250000d405585c800704a40c00c001c2c401046100340d00300c6400b032200c40e800254080000b008281c940d80a4103620840b1400300284145400c001640c036400380302d1803c15a54040288002c91740d2041d205040c000642c5c00402407000341c00d811404600070600d081481d4000c04501008000046e00800c0100c00d45104a88440c20525000e40080c0781d80d00c0e00c20015840e0518000741c1c4001e176500c8070700b8500c0d081102d0342c1018280c4c01b407140541d600c2c90300080c6c521511400d000d40312040d00c411a07102 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 981487320 1250 981486070 981486113
    0x111203070c0e06010903110105070203010b090709050102060f072c040501150e04090b1305210c06071e0c110a0306020d0e0105060315060307030b040b010f0b07050c1507 74
    0x41d070615114003a040400781c410340c1003003c0d0b40380600010794551000706104c1024207040d5101c0131144002400751840060b400c0d00150404180301200341c004014505407007090f02074880d00d580b0401104001e4200711140800034860324540c014210117414a0901094002507149200303900e08081b400340c03030b401e0740142c90405100c8602c2c2440fa034061110304041d0400c407028001e04c1029200c40441c040064461031800f218012003c0030042c040180282695020503602c020300007103e40c2a5864001840114075030091400050800344102d09030264424160440e245001070007408840041044004907003681c104804d090a603592401c8080003144610f10140c0c2c1c6032440d054000075a0648102c00030a6070420b010b11255580c08601d0707107003140d08480c22200c40c1c0e0780c4000182c94a0042d600c0640344114203014881070104500e900b5051300c14024021403501d60369214180d9034800d004c006003003500102103c10403450b00a81c0c4106145040000900f07100c0d41d9200d50744d40280100e6402040c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 981488570 1250 981487320 981487343
    0x180609150e2d150d12050906090d20010503101401050c061602010e03090d061518020c0c0f0f0910080f03130e0106080a020d1d0c12030903070311120307 67
    0x1001c00001e843c0403402a1145040d000d065a6601d00c1c0d6004c5511520501c00045020700d215158907027030340c0c01c00301c0052207404007038001c0c104012542503861800d440c030324450317441040c15401b8000f100d000368000b41001c16902e280c01e00320322000340c0650315a81000b0003003060702500341d4100031280c044e6403600d40e9183d148030140340c040d00711043c0624040c43c0d40c01c00d1111403926501c0000240d1400c2c1c2245d00442e41e030215840c1c540707a00301d05400c2204c507013408007071039440724501e81c0c0079020440c4118119401c200d01d40e82003140606028100780d0b408541d42c54003003034a081c64078110350410070100560f202103446036142c50520690900300095540f012031142d0000f6030301e5101c04018000e100c01200c1c0c03941000d40084c00094010b0415a1203900080d10b6949034403143e01840f04030b03110209014039044551542c949a84000304954030512091000c407101c0318000c000c540d61403178018002c0091038690f5a40c09800c1051403000c5500061240c000d0b8461907040c0002d20b2600d1080c20000388 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 981489820 1250 981488570 981488581
    0x70819020c0109180b042703180e040303182018070503042013140f3102030d0503091504020d17090406180609150e2d 52
    0x14201d540c0340058104440280200445010a9924030000c1c11007400801e14104481c04500902044800c80d0007540400110000c130500800c00e210110344259a0301000c0008910702d00401c61180c0107145100707904802090010b4020f0307210380d40c0f0803032082030510007010a4490320508400030203a8110341c00c040003d1240340c0750444852030348031100c49070140da5041100700103156000040000308030f02807011707402c010301c0401440b015001c08000c240c81c07448005141d40001601e0b07050b0417409103090b10800700e2001620014058800c42c0c2c0c3e588450a10700030b59800f100d04010800c801d5600001300b0b070313003000540c900b442501904902610f9240e03481c2002c64032a40b0780071050520401c5980403d081c400140d5a10912020403a04010503c1d00311030720400c0c0480d01c4c411754070034507801417402c1c50000b8148080c03000001d151110240170040559694906015074204107120084500c595000307100d109405071034035401552038940e640c000848203000010000350128100d420700c4030b9104225 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 981491070 1250 981489820 981489823
    0xa12020d1b0905180f0f1305010203010f030c0b0c250e0108010902101b0305031905040c06081308030406180f05060405010b060f030f0c09040618110708040b030402030307081902 78
    0x40f81d0204c403894a215482d101d2100c00004001810103c1c0f1514402e0202d094007004024401000303410400845d5296960311460840c1025844200d03502440d5060000300c4886290965400d0311040c8003800180b095038031b4021291001511a00f0480c00501000c41c80c80c0340360356140c2c0608109400003a45442034010001e0900c5000d04c40000c01821400701d24010560a28102d0050740c181000d5031207884504102d40620310242440c000345103048200001e000c00380d04817108032041e985524141b51590a12040c1500c00c00801604849041011900081e81c5034003071061800316840b06443c946e00e03950384103a1044a400162043d82c4101d040c40f082c0a000c1c403d030604d011003141d250386040381c0a0b1a040b40c5000c024414071480e42c1300d070300007942008450200c41003510001c004000c283c1c0c4401e6040c400455120b0091285864000b201d081c0180745401c03500c0142c2c200305c41c01d044c14a020180c84050307000510881c2c250109110b034200046c81040035044070050f0149040c03044118002c000e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 981492320 1250 981491070 981491089
    0x60501090f020903120309010f0e0d0801080f1b0d06060b131409061c020603100317042105010f0213060e031f0b01090b0c030c120a12020d1b0905 64
    0x14908544100f0802c021a82c1c00503400000d508420b8001d91203540703800e9111700501c210102c2c207000e0350400040030200345000c90b251003400c80390707128840c1d542d80b034003005039035a10b0000c40320040d580f124000c10404601503d8910100e00b0081c40b00201280641d01c640c00d0340d0180d03101c481c95000109802e80d140b1000c442d5413010b45010b1140804441c1c0b001c000440e150009040d150181e0303a0b602890030412085051300300340ca6009002256a07040406070a0201e43d024070054404004240280c6a041045806c603001c603214850039142800b4a401a5030a015010004030741941d07a85031140d01c074a80302c0c00030341110708480603034242923440c218000c1c012100103041c3c07610035000301c0041b03078038040c00c040c000500f0010480300160001c0300400581e100d403c01e402805c1c8000010800d1a2031b0324001005020382d248820903195854044020b01000b8029000b02402017203104900c15044021640584400c0781b42000220f04801c07030184050050b080400035400083d4601010304c01824407407020b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 981493570 1250 981492320 981492341
    0xd0f14070210080406091a150a0e070f090e0108030414030624030f34080d030b06071407050a0609030b16030b03030c1605040c051801120906050109 65
    0x4280340106560014460710030b88001c0c0301c00c0c4400f290104040c401603600c001c82c0140d2003401040b001241c003a050006c890115071055a42002c03082038091418096450300481344810180100d68071a0745041d1507122030804002e00300f00700b03000e000030700903115040366000f000c90074080c0d5525414a00d903020b00d02004502030b4041d5009c3e5043c0600c801c00006c00501d0605c480e901090400b01d0030300040c0c141056051006103c0c440c84410728114821031807035202540c0585052913010b120a106491065071074401c2c5082c0b0b4102c81c0e030022410b07003c0e4101c0910780000030041c034a0559266501c910780e0b1100e850302c450690010405001e0b90500700c140c1d00180442d400c105401500c2c0d84e40d1400100f00c014908501321071316100c440c420a0090300705268980c00282501d803901c602030000381d940e001402c0d000c0c2d011265001c0000c1e044c145480b52010950704d44d034481c1c1c585025211a003088421240f0010f0403c045c5400c84051595144551765003940b08001c080b5940d4902010802aa2a605034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 981494820 1250 981493570 981493607
    0x1106132001020a0f050705270a0504020d120e06030103034a040f0e060907060509010e0d030e0306070f030b2b0c1d01061803030801050118080d0f 64
    0x403020116a000a24282d40301d500500f45000c4a603240313412400c058041c0e00c020740000c10a044e80c4c03007510000204061b104c080c0e10010700b00341d0324000d05030140c45060310302941240319040c1c0d4102194105405046501305424401d404900c0c0001051440e44240e20581c00a88240c0c003100d83d010382d4006181100c280385510b1001c8480740c981071804d4100c07240c0d05018044002d10340d20166111504400c09440552008001c0326a0740c141080c0c0350340088032242c0c0c7c903018004002c20140d01070019624a1641a9030b8120310002000074030102551140c8140c0034072054118030317203143c1d4042000380d10501095641d01c6402c04400e038040c05940980381601e200e0003c022400c50581460440046c0c030170140880d1011500d6181807000500c1c8140c2c21007494503030720010000d541c400460340e4504944807507131640c10805480d0001401c60440303000080009004000401256220700301c89000c00556204488000c0e5951904500d041e009111a0012900f0700c00400c0f4481c0c0c00104e070354448441442c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 981496070 1250 981494820 981494873
    0x14040203030301120c050303040303020c1206010b04090f2c210d020310080321010501030203040b0c31080d08040b0601030f1407031505060c1002070201110613 70
    0x500180c0c0301c0c0814041c4c0b20f5a070340224020424004490001c1c8001c041c081c0a803940c880c1c0b80d082c025259940d284000d8050f10720503003020b25010000803801c0c100d603850900141030074108451380c0040c2500144050086032910003c03590706140480c001142e00c9034000441c2440341c030351039450070050908900c0002c0d00741c007032408404011440440b003030b41d140d00c440182d69907102c0b6903c030451401030300040d0b0320303100c00710b5221843d1a24a925003441c80e2003001c0c00040d80c1c5d880d07004409a01c011070303008140b054004003295040310245c1c050413200c00b038a040c0346141e180c544043d805d2445a070b0b29003008500d04807401c000c84035040c0040905203800b4a010980d628258a8902c8800005800c2d141016900c00002c1030515943e80f04400303034841d070350343c401c018281405c004000d01002e440c0c0070038001c0385110004083c6030a03800c840d40b0b05040d40140860300381c40c0c1030304002500180000c1c0d040c02002e4000035030040302400054820401600014181d01c4941040303044648407041151150360000e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 981497320 1250 981496070 981496073
    0x9010906030f140f06010603060303021603150509030f0f0414011103180102030d0e1605040608120904140403210504110f0111160512060c0909040f0f030c05011404 72
    0x180368600159401a48070003620018060349450520048001d88417400350303000110313025074541c2041088138021780c01c460880d201804800023080d071521000f85000c40d0003443c14010220740d000070380d210003210166810844449480c82c2d075039001000740c2164820000301800000840031620711588428600110040c210701a1140d4074400d00e1001c00d100520040c2c241d01c0f6a20800c2220410061801c050080c5814002c40607a9040c03007115021030301a8081c03010420b810144148030844583c0c03c010105d4104951030180a5031040a420382c1081d283c110308002d8440c1c580070540954441c0e91307101ca11145a4021030003028800345055051403e01d02804082540207904030000641242c00c0030f6041e1340000141e5101d4421081c80319280aa40881c2c0581020424510700700d4805403010008590003411407901c442c022a0090150315003400b1504903402c0500e500c2d940244603044803800301c4ac8070f4481100281d285e0208600007184203000e101002001e000d1a008107400d50403590319400d15 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 981498570 1250 981497320 981497333
    0x7062c070830030c0702040218040c020d140a05091c020913120305060612010e060f0303040b0f1c02070c031e020d060e15010b0a02010509070f150c0618020901090603 73
    0x420300640d8018000c00402e00c04d90000e002c803810760354001c1003190340301442c10311754040c041c8660800c3d1003549498643c3c1c0754180041104070705801c0940d141100b40c0c0007220480000e0f001140d40c00100503061054512907101c64071f1004046401d9540c6662001e203c1c41040342d84a0000d26245445410410002c0029000541c40004006030b0601040c0c0e540c0b00d8010448030702a00f02540050b503903103000015a001e85020050140381c090355140a1503245ca01415a2445984a8440c2080080004007900c028401c050030310a00349034912414481c1090000050760855a03082ea460300007103004204001d0010b212260012204041440160080c1c0024100e00c00c5044003406603038980c03550480f201c00030704c003480720001c100364080d00e5561900046942a00401140b00266103441c000c940d86032400034210040700c5071411402c445500f00303140c5103003401c01000410300b4089405003410000c1ca060040030360111160401a07003180c0d240c010841d10500681c0f144c450302e841c08c1d50a1010505 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 981499820 1250 981498570 981498643
    0x2130602070b040320060d0f0507031509240806090c01090501050d0c2003040801140f04081e04230a060c11150301080a060b1507062c0708 61
    0x8101d81d85c1c54038500d001c482c9004804522045590150001035800750702070031580502c0c500540d0040c1001181e441840950444111801013500070f020b800c003c1080e111160840720a84050810a89024555031005204182c968005030644e801a0f0100095000f0401400c0c4000e0001d10b031818104c1c4c0707000006049440303444400013150392200c10003808a402500403440a07200740340e003540e002d0035034980140ca0340c229001d0304e2802c0d401c04454115500d42e80312418000d6403070795400300d940e450790340e5510126401103221140604403c800d00310501c41070000740006043c0e50480b0070140c00e10b17540740a2040200c034049032091100721000d00100350b20000461105a0141d0a4108203c01000003000c00701c500b05900e401c501e0000010400d0b0b40041a003c48040c800d007410701c2400c1c6018200400f250300302c218529a90300a100c0e0b200400c3e215044804e03c0200445038001c0303d8070021510f41804140084c040d2079074025841040810020007014084840c00d4001446035200311414107078041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 981501070 1250 981499820 981499823
    0x312050f0c2d16031b11010521040f11100207210b070e130605132304030e1305010e060402070203030c0106030b011424030901090203070902130602070b0403 69
    0x10820301580040441d00d0280c071031a00b600903149a258036814441844000c21607004400185444c0094081640040035000c60300e9404588080045c00f110300444060300040100101e1106680d41101f284003451611401640a00f40300c5900c0501c50808071031040c1800d0406005040b449071600f6a6076010500c4010382d0b8580d003204500d1a01045c0001c0e540e4114040a8031840d0403502b40464540c02000d1107140c0e450075911019003070b1a000d9803000300c1c0c42a226143d0006110307401800040621b620a400a911202c0b1441c03400e51803c100c14040c14080354120b000c079403050b03241c249138a08007103d42105404800c05004039814081502850300024044034000ca401151220031940c1c02e005135000301099000030004c05a0341c1c00c100c40c03100c0c07080c0300f41044250640380b0305680d402c4c864a2018041c02c0c0e420110480d844c210101c0700c4035440149864001c1d545c82c034143d03005035814468071004103030000d40076072070340320b0400c103108a40111341c0210103541c006001005000030035030039581102d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 981502320 1250 981501070 981501097
    0xf05150a140604050301021c0b0a08030a0309030516060c1202041a13081009110d11010c05030412111f170403020c060304061b021b0603090c0d0312050f0c 68
    0xe41c00307000420341038080c2e500300e40c0d8154000710b5040c0d00700301143c80301e5200d502c15200611606034400305010b1905ea16002d1019203400c204000d181142c041c0e0004440300c0d201c7c0c545146080441862810741104e04c0800700c500903240c2c41d05a0b492584601c411441040400301140390a02d4030250456a04110901540942002c50038001c0012410081001810008240c0d004400e03030341d40840007130200080489005541c0c2860081c1800c005080005072070303000b400309082e51b02010064074031031006a0b04a990344020007011520b5407141d0001c144445c030071450882c0d02e2055404201d80140074010f2401e000107060000070b82d15600c0b4140c5a110301c0040141d500c15169820101d081c64203005405800c841d00106200c00c01c02940e100702428030141810340c00d03410240001300d03144c0c01040b4810090350450b0258100500e0810f00179030300318015408132520743d1009008030b60660400790003034010030105945600000d0460164580c02900346030109264502812003250700d0091500e100d603007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 981503570 1250 981502320 981502349
    0xe060a0309120521040f062301150504170a1202030a031b020c09100519031406010b0a03180203070b040317030106050315030c030616110c030c06070305070b01090f05150a 75
    0xd00c00c40c3c03c6c01e900d0350364020b50103005050000740140d490008603000e40400c45082000050000d95038241c0c0100d00030641c0e2511700c0c1030b01d8450030301084148810000344c14010786642c600001c1c508101d481302000706401558440203048400745c06c542a040003401d10700070003550821344960110300d0b45254602181d60082644425001c613892040320b0304280d8100c804c0046055600bc2c1001144080b20b205000e420301d4001030b010002c0e1990007c2c815808200014402109800c0c02a0071000700e2842c1070081c18a814006e80010f45844000da002c0710b1507900001d0140144030115040340618400d8644541c91075140c0f0000400300d01c00100400504078088a0101040d0340910141d080d1040007004c46245003020030880a903060900303100401300e02d81e0301e82c400c080140030601c103405540040c00b0340400150481401155448800210200142003145400240250040e82c0c0600f0000c6000541740350424006c00071600064151000d8650130400764842ea40c984c0108001d42d00c0040302e0003030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 981504820 1250 981503570 981503573
    0x20709180b131e08030a0b0d0309030201140c100b03010b1c171c0c02010507030e0606040917030c0a0e06161202101404021e100806010e060a030912052104 68
    0xd202d0443c0c0d080251018103003101c3c4003030240c107030b0103140203140c03008041050340c2d044002c210800c0d0030b0b400300801040c000f880800c0598001c4003000c00398245040c11a02d0301154034640b6007042c060702000324086a0342d90780781c481420240700b1280d0246050b41e48074034064400111076041440860010640d0155030740c20103402030356006480c040407100d0407000c9007401c03141c268005031841c0d501c131000561034035002500e664841e014101400c0690b00242c00035803500002c0c0030280010309015102c4c40381344c1168002c00c1040000a5200c0c00a450380345842c0c2c1c1c510400103007220f580c1038003d4807920b0300780031740044010000015068907a0281904100e0540e5443c16418124a4411055114600b1541d90210340040050074482da10807034910300e40710081105002c107051003101c01d075045542c041c40415440e000b12500340d000001410409207068040d8000340046c0c3c0280c1381040001c1d01c4800344810410094102440300d4038a086c0303541080c0601c8180070b00c62550031341c2c00000300d852202050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 981506070 1250 981504820 981504833
    0xc010204030605010801020a030b03010c0c0b04061d031c14060607021f0507060f05011d25031d010504020f1c0b010f030b010b03060a0e190507020709180b13 69
    0x20000c5500440c1486a585d440316254001d40101d05000d0109040a112a4103854180304c0c54804013616283c1105200071505c46101c020740003071048500d6581c0d00781e0901100303208072084a0b0444185c1c011503844440e407007440c0b0300f07030b035090385031080309040070880542d0700c0c902810319030700007000c0e980c40c1c0d19080f0314000121080442e12000b1091041090705596050f0302c040209801e602a280c140304440201240c40102c0317400348140306010003460701c140c2e220880e4410813900101c4101c0c2100412480c01d03551454141d540c01d500011980c1c4040d000200707071034520170321288101c41e8000c007c41c1c0f51540124035581c0402017a984a060429200d01610b26031114400031540c2007914400b2940c1c41d001040c04400090005a44c00600400005181625070084a124100250071006a10f00d0409160840c000c040e000005400d1803d0740c1c00f4040d1034520400344103405035402460410314004061040b00c0920302d030040304103051807018003c128412000d940000b4000e420352548022820540e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 981507320 1250 981506070 981506077
    0xa1202010f0f0204140a12030309050a06050f06010f030b03061f0b0712080603190807020f09040b0a06140105030c0313050f0a0501050c0301080d0c02220603170a020709020c0102 78
    0x35a042d1400c4080b04410358254040c009031000c9000070f1000c00c0d040020006500384c0d070b215004510b08008003844c0024400d4104e0301402e4440d1085901600040e80c0d40c40548030112588506030402104015180d80c1c411641c0a01400ca4201000004100300100b41c503044000c1c01400040b80d107940b004401011001c1e080006d0940c006000d403140343e40e01c1c0c920b4140410450060000c0c0c0da050100d0003901d0040b50018000207032031617a200e1410390b6a90403407580c01c8048281d902c210007807120030080d11580c4401e40f08074840e104068940c502200c9103000c407009034200c0244543c07140d08a9209036006812030303400040b9003008544982c1c03804024a08241250001803c40c00369042d1561182d20008000714018842c100034485035448040044150000b48140c680507407000d0752110a1500506660842c140042c003000740340c44413503920400101300b00250590301aa201010400e00200800802108440d107102c0d03440c001031700c0c3d002036a458180c000d0490030755000a00d007c0504095049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 981508570 1250 981507320 981507341
    0xd05181b0a080106060801030b100f090b06090a03030c02040e01110d020c010b0d140c030d0507080a020a060e0706030e010506010203070318120b07081f0b1c09050624030a120201 78
    0x80c80304c140c07594001030501000388030480d207000b1044080707400d18809140d0079058560704d0000c1081a45840c0342d02c00644464501c07503400400070032101ca250703140e40e082000514047d45440c0c82c001c4152040c0004c03211104000c000070b074034040040c0000d0045a0845000503800070b00540c69440410141d0f0041c011840a81e40c04609100042e08004020000083c02c4224600780c0e118607040105154903041c810032840e000038820010080040e8080014024038a600d104841c030510b140e54035401120002c03000c95610b540403841c1000845d505008400f0040300c020000d020500b80030300080e40d2070181d00c80040a01c06500f94060040ea003994542006002206d2130f2a20070b0b41d80d0500903000c24064a50340b000960a500151016a400700e5181c0f0301c0d01d00541d40c071100c62078220044c00d00e030030420389030482200e070b45d0101d4401c008500842111030700550144c00d03a230510b51040d00305102d22081600c071849110042104950300401c09070706240d00030700010851642c200c003c80c01440003005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 981509820 1250 981508570 981508573
    0x10f030b0616050c12010e031b010e12040906051504050d0215030705030103170c1509070807090204050f011107091d03030f2205030313030311030109020d05181b0a08 73
    0x180b01d028080d0024940e20078402c192401440f0840b40c10100c1e081e100e01000181e0160701c20803a414400711010042a212941c40c00000b40c41000c0c019200d00385070003070b40304000d00c51010605010120380c0b41301c0c0340d004100c21192400c220401d00d0103000715026070700c41c1d10700c00d501a0190030259165840030242110b081c110079943d82c90940405003140e00280403d803820180c5a04808210601c8812101c0c480040c00c0202034401c651040002110b10091050106001e0154001046041000f940001d080030f403401684590030b2030b041c08802c000209c0914100449641c2201c050200461844299080c01d14080748135030064500c0e4610756203058003102140702c00010401d04017201010390307004003e00015503205010750801e2160a074555032020308680c00410101340054800c0000012003442030901042040c0401c0c0007405541003640a0040300b03070001580784c0c1e80080c52042c168000c10710800350080035140f1445503070b80c1003d80c011140a0012445d56200350762070400e100e004245110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 981511070 1250 981509820 981509857
    0xf01230609120d08100f080a1b1707030b280209030106180e012012040c0e010b0d0507050a1d0103090b0a0b01121b0f0c060513140c010f030b06 63
    0x10008102000c05c90360036a10204014000c0f8224802450550403110003500615410b030240d240c485401c0302c030020162041800c4d480025801c80807003110b0100480d04009401200d181d070400c114400c1005060034500d40d0441d03450880c2d000c80c6842d0070000d0361003c8005171981042004640146401d0700034030050003031046000359502250700500c41c00b6076000c0c02400781041c0100b4540c0340c00c8122600d000101c4051140a481400d80100305500074042c0010700314240e540d4850206921003a0444551403000180820001001c0c0c051103400c10068549503241400c0c020008042444041a082d603100c0e18844510103070b84207070001a0010f0b0040e11140c46801d12400301401040045503441c00310f1b804181200d04080b051044000c20403661074560045520702c0400c5501b07080d0349030200244180b100c0c0c100082103151044031f01c0389103801c40d07000d10a0a142021403968801c1100ba090660081701001c102c0d0741d00c00c3c9005585185070801207902981c5400180c1680102d111b503000d040c401d01c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 981512320 1250 981511070 981511093
    0xf081e010306090212120412020402090904120801081f05070315090203010f0905010b09040b2e08011203120b1804080304030318050606062503080f0123060912 70
    0x3c0d40100d801c2071080714460740300039100d024103440703020340401e90342c089006100402c4940707101c0b1b00d0329904500c010700061030300082800160000750306640c25264080380200d0001103580001c00c01d030240520800400b02015600342269172100c40405902c4a82d031240c5c0451612030003a0401c4440d81e410034a44081991a65000f1009410901c0f6020652403007900010300d4041da880751a058911841c1060f00d018081d50902025001a080030f50304080da8821106049840c0140c90b06589141e040c0b110303020fa54180001d0180c50180c204d40c08418102d6043e40003e9009450701881103070007600407078611030580006500c00c0c1401c0c60f00d05031001210401080014200085100764840e440800c88500188420b000400d05940d0042c86544060b01181a5161800240c94259881101c090380c5030f403c181d8519100044100c1100429850018014170407201400d03503000d8420130b01c000071000503040065041e101511115030043c84009401e0500744c035001250507030700ba00d4008507a03013040007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 981513570 1250 981512320 981512333
    0x503120f13030b13110406080312070e0a08070929010c0512040e0906100e150a03080a020c01020d02062415040f030302120a351e06030105070f081e0103 67
    0xe00742c2292881420983d50030b1358601841f80e00c0940b00d41c800114241141c24542002a03000a0000c031305100310300d6101440e580d2043c1d010070103850031001800c6079525082000082c0c64901c0c07030840540510540320604401000740a1501120034038018803c0c0380c0740e0030080e04003111501c41588111001070085100410440c0d180d0003055404201c8074160b8842174000030156460140e08022040b40b00424002d190050340003030754103001094501d10507a84d40da9040158002481240541c1110484141075038050046d40328a40150010300320b41d1404400c107239080300c0040540980c410001100501355110191120320324110062030a5450341c803070f00c00d6202d83c151480201c00500c250100c0c0144402010151024420b5503210346100d07403500300080700c145e0028841140f00c0303200002543c29041034a140d40c0d000b41c81c90329001d0b2206000e80e046a045040c001c025500a07810700003400761003a13101c1204442e4003200c0c13401900d0747c3c542e04444095034100b80d85c203812021442001000b030044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 981514820 1250 981513570 981513601
    0x40605060f12030711030a02030601060f020708010603030e01120e10020717070303090507090204060504060804020d051507031521021f020c330a090b1204020a0503120f13030b 77
    0x505c6618507581c0e106003c05a4551109100a4158102c074004208403070103218032840c1c460017030040d0317040078ae282c00ca41c40c21142190300580004607038100179920703543c1042c828628510719076024004c090621611a41c2d45501000746080142d0008002041c09070014844944410120b0000d45d120f21750704000b0054a41c026040d01d841c05290b50004500b00c1c47d01c215030860f20b4030303143e10b4201464608141e8108400900698020304050880760000306c09004000c0081001c900810382d07070908000040442c1e4210011944500c040003050103441d107035402d0310180034502807004058040c81d102084007004144102c510030900c203440d00044c42d8010500380080541540c0003050415001c10502c001f0300f617200c00604074801e84a0075204005414010807091001341009500d090751a40218801d034812404050318001d0f00701800300310301e0140e41d10320050000710f004003501c4200d2030f648581c501c180c601141c0c09070760001c0d0400702404022860401150800d104180e80d00e00410000076400c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 981516070 1250 981514820 981514823
    0x21e070e090a0b06040504110414090d05130504020d0e0f102a0804032a020f0a0f090b03120d0b03011401060c0f1401110a0e030c0603040605060f120307 67
    0x40a8000092081000142c2c401c00d1680026041c10240c6841081c40024403010b0015510201102940c5400d926a0300071142200d40c08130344640b03103141020005040010015182080100030040100f020401070302c21425a801160300503501c8031036140c02001090400c1203a000d500580b800798014075004a00e58085881040080c403402d074254275440c40e031040710016030b102d0010032406000482d01c0740030368030780c030a101c0d0400b40c082045840c0d201441010703440024110613984540c0303408606040448031155102505e4002040e4100030031510300701c0c940c2c05044203d5954514041160740e00704000b07040310181e8a080c503034a54801d0300c0b5402130b00200307200300d01941c201032004c030201010a00c0541210760780d0f952400040030a641d02c07444000071007000c0d110b101d10901c40042c1a0421701c02c800d410050355920036600c161611024002c00c10f00e80c00c0a119812107446c4c420b40d5140c040449601c140d001070b0000b6266603160000d103141c15040003268011500000a80688900000400010303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 981517320 1250 981516070 981516089
    0xb040303030f05010e010e04030314010f0f0f1508040305040e0c25080a03020903150c0a0801080601081c0c150203093a021203160e01020c010f0f021e07 67
    0x701c0c001142e001d840c0203101d2842030381920801008564070040b82c0c10381003446440d01040886521210400c142000c2c1c101703003600004c1c00400c106042c19080294002c15a07100003102c0d2070303d00040d110103054112001d5040c407090600040800d84280c0480f1702401c0b0035000b044107810200707400c6840c0c0d00702c0c0c01c000c901104614002260f0f421016591107a81d98000207483c030780207400d1030440c041d400c1010555090301c01c2100d805131203610291340310703c1525154111500c0c2d0346540c8000f060307400185d0112250782c04c901c00502050b000400ca0103001c07100b0303560400c503103761148101c4000c1ba510402800709240d1032a59100c4160680045000c0e810a104541100c01c3c102042030502c100100d0051026081102070040050139042c00c00003401580140c0385492a03000010550341c3c0105c4803251881141544080c80c15003203c6010141c0c00c00b84001c1200c01280000600b0401c5c02803400f40c103204102d45110f110038420005001c20001c1250701c0c00c021524a9240d50b600c90345405560700b107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 981518570 1250 981517320 981517331
    0x50c090702010b09150f090a02030a0524013005090f011a040f09120309061a06091207080109031829030417070f0204060e24040b04060b04030303 64
    0x10944140114240c840008000584a4990b03403d208103802d0703005c95150300420000e007030441541e9440201071090b50161009640d914060314108102d410081411808ac0ba45d83ca1841c4043c000f880a120000d1080c00d00e1074151940c022070f0140e400c0300742c1d14040e0900714003600007000e009030307000302c1c2c001c00032078044403000f0107100382c10307800d8885250740c00b400081001030400d00d518003a0000b6031100130510300002c0c1000345488121492040d1444080400d0316500c041040100c2403082d03104405031007162882500407080040c074640f25004a040c854912510010701d10403007808140014034040b8020092040c191401404280e500c851040340d914a03048002260500c24503c80c206204000040720071000d800103d960365040500151205481d24021a0b042001c00c40201040c0340a1001c0031700d00040da104202c181ca1554002d103000d9010802445001209004d10383d000185a013400b421030458000810018241c42d25001d50190a11100048200038040100b098031b001e030703505218 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 981519820 1250 981518570 981518581
    0x50103030c0c060f1d04230403120902310c0c0512030c04030818060d0b120c090606090d080301060903140304060f030b06071a150306090714011704050c09 68
    0x10520011080c180115901740c1000c81c122840c0c0780c00c2d4a089100600020710b1461400c2d907a1000d461030780103500d80345a040b0600040c590000c444000543c8410070902041d1180d41c0800c07540002480c81c01013182050b180d40d8180005040e0a1b070381180f043c24108030402c207529008001c028170b05401d5905000312031410b0081c0b050746003203c0c450350642841c80e180c54a165a40c0500398040584030b000d03248500d002448940e0f5a20051055210441003c101c200c00d0400f0011407151200203404664000748c100c213525210425000c0d4005030880f08140c1703503082040801e20700703503050900802e203107400000440e04642110402043da802040c00544d090a00c1207816524411400741a0129904400113081c071403094100c8035081b000640010b0810009660701d100c251a100490362010f00d0032030800410030300b0f500c403600d64035000b10014505402c00f808a141c41c1d0005003e0614880003a1404902990142d04c03001204135894100440d0351406003400380c2c03103800e091042c0c0d10a080c050701241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 981521070 1250 981519820 981519827
    0xa0b1002010513110d0c080109020a0501030506010e04020f07020406080303150a080a02060a09051c1e0314160203060a05070f05030105061909080d02030d0c110316020112050103030c0c06 82
    0x28861500d00040c00c143e00815110600e90868503454158492490760004000842e800c40020003041050004100420030744100f00e02c101460b00214105490a020482c0b03581e8000c3c07468441c0d1800742e0f00160385030201e40b5250202c0c4165400650828148140094100350001c011482030031102c00c80003500040c4010807501219501c2885195408000c903100035140c15801018200c80c0380c00c00700e10302903540c400300390a90f6481140001c141c0c0c120300b0705000c3c01342e1742c0320031407014550b0320046003200a990743c003600f00d1401e140e043c40c9501000c140300d1070164080021401643d0021b084406c6071800d03402d1a00a082c0031a0074a00007030140c2407200c2c2c482d000c0c006603416180010405800c11106894443c2c980c0010380d8400100030200c800007400103014400003406807110790295a9403620444104161900759406504022010840e5016280b01005840400208643e4180d0041060004035030359848105a5503420b0319141c0004205504400e001c0d80d4103120f12584043c003995800140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 981522320 1250 981521070 981521081
    0x30b040230100b16060e0307021201020405060d0e070518090f010b0f010806150a020a0b0906060a030b09250e1b0a0f0203071407051f09050d0f0b0a0b100201 69
    0xb0241c18100150a018003192240541008107070341085500c8200e00d622554181d803240c1c0c09082058100080607401e50030502050b10035224100021b61610389041c02040c05482022895200181e40340032803001c0c982d090206000910008090490118100b141d990942c84141d80303034202403040d090783d000d0105040c028410500030083c44101c03d0141c6134015540002c00929095201450300c03034047e010803820001e05020714869000749407410851428009001010b04078030030950065040214690316083c3e40801da036401320301c608442e01d0384044189407010b034880f800803e02c1d03440264643c1200e80321511084450142c060400c9031030324011840060000d140445140c0d03410031444410314042c00d003003400c440c0700344103c1e8500b8005e9210204019029203403090b0603080303038004000d1498040502280b801c0108064007194101c00e802400310f2400c0d00c10580200c0c42c0e441c401007801020140318100c680c104034a4141c901e0701810020050a072210514800c00c10341d200c4600311841480b65 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 981523570 1250 981522320 981522331
    0x605130b0d02150d0e1c02010501050310020c0327010906030203040308010509090703170301060906020304081b12010e0606011b051b040b1002071a030c1603030b040230 74
    0x21900076180680a20001d088440b0480032154000c00c41d0b182003000364800c0c1c002c01c04250010b01b062202c032140311708560071070503061802c682c1004014403240c1d07404101001000441c54005a035009210106030640c06550084004109100d45411101440b082071900c03e081c01d980b80c188054031090142c080740426240500081d203520300501c090700b8000100380e0400e82c03c0040f22007035136072540e80c0740d01c18040710202e00781e03c18084010402c45403c84a41c2d000740000c1d001640c1850300708a041c41d540c130115800082a4140b00da0400c282d9200d580450119941c45402480720310110410260b035840d054a10a001071207062070148120700702c0c5405800349a104010b001001c3c103c8040b210544d080c800d01c1e5034416500e80f050040341e0354010000c5800d03d4150064804a480c003600104021680f041c600b1101c0010410011007004600c22140d80140701c20f00480800c0303090504600400c0c00312001ca42080c400a08070240341c3d0030811045290a6007a1030741c1b50039081ca0071580600009481 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 981524820 1250 981523570 981523579
    0x2091015140712022805010b0102010e0604110f060c2b12053103120b0916020f032a03120415021c0507020c0102010c022d030d0605130b 60
    0x40c507000901c0b400c000500c22080f0303204440380e6201001c41c2c2140c00d80780c0d00815060031601029181048070030b0148900c0306200340020400b000c1003d43c2d25484040082000740f48000100c07900c0e00541e500104c02c04403100c003900260304c079108515036640c0c403141c4101c002c440c2c0c0042e07480e1615540350f420005003c0021603807140f80412400401002501e0050700071001448132003801d98181441503407040c400d5241b0102c0c0b20300e40c0b58030704015040a0104c0d00740800d0a040010f50788481c1c892900894021000b403441036080e0388060310490400c0344507103070001c10f400001181e4000712141e5030041000308030026205002d55076403501c03907940c0c402d0324040701c04003620200080119502010314021560407200241c41d098501112980407654690b0f400d1006070784001380102c1ca941080942290368080c0000c00a0075110310b0007070f548034120118001c0c19803001100d19108001d001c607520380d42810b0411280c039099003c01401c05840d440c0222405166001540300a2075043d0081c001868030161 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 981526070 1250 981524820 981524827
    0x2214011b090b183001090308061005091002030405012a0318180609061707150c0804080a0b060a0303051c0b030d0e040605040608070e0601020a0209101514 68
    0x103489070840e41126040051a00e54a45021070f0f54030b8030340b151101c000100130320804030324408003608105004140d40380300581c9049007140001e42c20030003c9801041c100d606020f00700c0e03240022211840707480015074200c00180d451240c1182c002001c2c100790b50f001d80b80e001c2d200501d0260114912852910366680d2003490b402080424010b061103051120010301c140c0207203403220689000714020411000401c0e81c0c50f4003c0000304113611400c400303411100b840b260718907458144103581d00c20500800c4d00e0060462400580c06005800040c19075070f0140c400c580b183e94070071b01c660f25002080025903158891000040c054031300445610240c941c103803126800e141e0903013801d0003c80d40d04900e181c603a903960905100d6640e800c200110a40c11140d0340c107000e01c0328130001c0c80144e40300c1d588130070302039030403c1c600f844082c40120343e1405803424080c14a00310f542d08070040380790610b50b0101940013840321050214a0810003126410340b00c9220000c0c101c07041e4800101c0340a83c0c81135006c00012401d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 981527320 1250 981526070 981526079
    0x6050a022107020106050303120a1d0a030806040f061e08010513030c020a17011d0f030a03020915070f030806100c030f0908120901021204080c092214011b09 69
    0x1408190042d41901c000101607881e04042441c503400100b09800e0b89002c2000c201046440d8080d104860302da084012500080d00388030107554010700c00005040c80248000140662221341c440300111712841e6091014a41e140c01103940400280807884203c0d081040100f14030310b05010b40d0303002c0c40c00c582c0b00e07032580b2080d6102100d12441211040342d000880005c00204071400b840d048900040f00c2c000001c0c8160202200302045020025041442d003080403580d00000c0d010043c0e5620242c4e40c200940da0b00c88d81c5000a40041c040e007c4900038a402041203003d020344c0c450606402486601d41c070400e038540f03500308102400780f00d07108000a1703803101655000a11801001501000700e007050410161141103960820301d07080d13000b081c2c10f20080b400040c6503038104055038400c103440c08a189803c0c100705c8580e403200c04559081d40122800c00c003088044003609901094000e542ca12060000000e00c1e01c4107141c0304d0811103284a60908a0003000c402c100c81401000e0482c540b0707424100d46c07a1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 981528570 1250 981527320 981527377
    0x4050406051c230105180d0c0201090b09030724140906040306020906090307080609190809120a0507080a0c0806090d200f0303010f060906020a03030902120d090306050a02 75
    0xc14143e12141e014038110f011944000d0042a001c3c81080d07150b0350b81d2501065a181c5083e2559001c1810040743c40c04034030150360007190b0041a12500350650303a44148140c0800c1c541103040d88032808612060220500004120700d0b0049605d03140c0d5100860f01034003186030049406000001035000608001c2000014213590080401d8000540101c0c201055407000904242c002d0344864000e4101c0002c10a080100740410601c0c10702044002d02130141d1034807000018000c07450700600401080701c03052080b91080004100e41a030200031a0000e41d101c40e81140c41e445200c4080f140d0002d044008910084007184c1684184411002460700c0d0050003001c442c4600043d440d850080a24114030b0300c0b480040c40840e54034480c0300300640c3d80303526000d040840d4521303543c0b00348200010030742c045c05681e90201e60140780680604c0e002c00c522045000084d00d4440c00002c51105109180151409a402c000e0910840c1d010b0002001070b941c684159500741d120b0580c0903107030f9010300c40d50b1124140c039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 981529820 1250 981528570 981528593
    0x80c060c1e0304021815130c230702030d020102131d04030e01110a03210902180408040e0109091b05060d0203130602040b07050f07050108070f0e04050c04050406051c 73
    0x1c01251700d81003100f0365100a00e40a5800c4101700031401c40b000414240711491b12031005401c0c004200140010348010582814401202a01c1543c00c05124a5090100980e02981e0f00102501c121030140c2001034001d50006044105014864400046543c00c1040eaa8545c004040210b81c181e40d43d59001c0702c288400064586c1404804c410200d48120204000d0003268801e03106c0034035030300c0b403400d110f00d810581042040d0f06a06140c5060016143d034002000000442c0950103c41d0b152807030407038046d02440e0002c2c40112111000003400c0c500790b81040305030034041d03101c0858034240950301400c885036500903e908031078200001d0300310f458141e0041d54020024480003100c5025503035000f00740d0b44590300041107000d001c910754081c400300703100d55541070204030300038000c0c0340c54040060030040d001401d035001e100c20b5002c3c4180042c0100d0031118020001402002285090042e0f4a8507800a00aa600952510030702055504061500c041c0c1600faa00400c0a00003140e80e50f40c840c1032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 981531070 1250 981529820 981529823
    0x4030804060e0f030a03060602070b07051c17040605072303060d060605030d020106231e0f0a0e16020c0d060e030c070b0d050a020a0e060d06080a080c060c1e0304 71
    0x218148040c101c3c004184080e00c004080c503a0042076180c6024002880c1020340d802010851004108000011704009a020500c1060424002d441d84085505551280502c8800c2c40310040d110100801c008040d48028881c040540725210410880701598010320302000c13042d006107000b040403512600d0300502c0032001522503000402c42c20b446002180c2089103d0200e0390242c0e464a80070b00c86410482d48140d0b40e44c50700d1290010812040c000207d4940c2c541c0551100384181d0b080c4120740e500d48490350501541c000d0700d03441c1c1d15540c9421140d450384040360820b100420484062090510100e07000a140a00400f40007500341c164903030400401c200505400c1610040005480d103007024841c8000904004007200d80340c0328a081c04201380c0350001c0c020b00800b4410082c0e1445030360000c8000c440000242c1355140c031003072070050220090405400000d0244a0124614100804480100707501c0100c0020348480381c46c0c80740c1608090046107140c40700c44900003500410383c02814082c55005 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 981532320 1250 981531070 981531073
    0x1d0601090f0902091c12030b1302070606051c080306090411040e0609010c091d090115091505010e0d06202b060602250905041203060b2502030f01020f19020604030804060e 75
    0x4a270000fa00d0103e138001c280480300e80741c403128104264901051031002c0c4a80050030300c1d8100d4000e0f620040e1501c0002e000511a43e000e902040c184080e0300201040c140c0054001c000e044000c0e00301554a60f000c5650303520350740c02c100c610b5602c94800c1f00350f1800c83d00907490920400002410103540346100401e100129075849851201c0c40e1040c1c1442401080c940ca0700184162141803a020715400a4000c80e050280c42d4080791803a8440c11340d01c1400c1ca400c1f18002a41e4403540002414010501c100754180c4100854150700b0040034107000341e400b110135840ca181042c0a1440c007401d4034168414000560820303c51291007003547d2002c0d4494099411103a00343c507840d0003288003111420344094851050010100c0c030a15050300c00e82004d000308025140c00e210100310942501003e0b0009804074420041441303045450400188034030080c103070029510b410b50880c01031900e030000207100070300d0b4100b03013400b00043c1c0c000b09005018a4050355248a250340710340701ca00203094080e01c001a103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 981533570 1250 981532320 981532339
    0x1202030312100e0c040f0608060f060a0906091406030c0a031b11010e1506060a050409140f1003030203161a01030302010507181d0601090f0902091c12030b 68
    0x1c01081d1005500c200c96030240c140c015030425800c98000c08000348091590742040005001c205a802d02080403210342d8900240315a683c0d401281005040582c01c070307045a00803c0718600260232100f050305540080c2d503080400c542d905284940c0c072800c2541c00390020fa041002c40c0658007600c0040003a2000e17070502203908085450514400140440c16800007419200c15040a0304203004003a4602423800c014001c0c05162030a1003098100a02294483d501c00079100e040310380600107035402003241c2c203800c0200d08003001460480b07080480300411112840d9000a0003503020002400030b41c1d4140d80110b0030540c500f500e0003a80f07408000c080d1000024107007503400005450710120b010f14426030006c0307824202540060101c03400c030225540f46044040c0203003d41e03191010048295207544004503041e031500801170f90110001c1d0401c2500f96400312000c140c0f0540d607001024040c030140d404c0141a00201c10300d400646422200912107084d01d08000c4959101e41c101c0020300c580106074011 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 981534820 1250 981533570 981533587
    0x1203160b07170c09040e060f1503160b0c21121003140a0501150509060603071709010b0a0501030b0105030f0402060910030e01060506031b0d06030f0f0b0612030412020303 75
    0xc0c01c0b0741140d07519003480e40040c01006600341801421801c20b0401e005180c5418140c1c000504110024600310f6580340d4059281083e036410005200301411010704894059100c84042070356520000c1a014144201c0050483c1d14240100c203032907400301c0d41082810540c94000c00d00703002030098420040240c00030000720208080e0b032180800700b201030b0000c141d00b84c01890700601703403400024507100c501c850000801ca00c0d21201e2300c4d03590182e402c0726001c1c0d82c2e9860442c103940d076625407000380a079100b5041c1003000c070042c15400018411000c40d040c00c0c04d155030380300440c151080f203c40103001903014004a043d11401022054202d84010701c107606140344440869481c00701112140002a1202c0a2510411080c807075080540004d40c0c03414075515001c0c8080207070090900c0342201c1c0703680c00518550601c1300c5070b100b01e0207154800f40d4480d44104904002c01c0308100803000740c490040b0f44010075024544070030450210b040d41d1014505191900b100d1703460342d0342ca40c0416a0140002c208484 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 981536070 1250 981534820 981534857
    0x1205070b0703180b1f08161202030f0a030908071a041205011b0909050a05040f15140403050a0305060f030c0f0a0f08010c1d010806040c0c06050705091203160b07 71
    0x3071003114580717100c00c03004003071403012005000a680140100e0b00500840115001920059403d503070b1107804842205820384046840c0c100c035580c001c0410b0103540080340415511035805411642c0a504a8403559168504010007856104c568410f07036400704010401c00081d00f05803140c4500403070000400001511402c0040c40d20100c40400080c214082030010a50600c11940c01081c00401001285869a0340c00001d1068980c0500320000d14008890405600c0e003110044080c220b00c204864107052030701a01035081141d030b0102203820038000500b103040c8940c0c1001c01e108003e008003000308140090000c40d050282006401104540004c43c00030920000728000342000c400005a100c00341d10010107244403134450280d1090304510650b02c6a911400b000d4101e84120360004142801500541d01405c405c0c00040407a8200070411a079503400502410f4800030a6481703000b200b00035000c00391a44076545901c46500f01818100307011444001ca0954498800c0c284026101d50702c84810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 981537320 1250 981536070 981536093
    0x2010c05100b01180503030a050310120b0a0501061b08030a2405010228060f0209040c020105060103051b1210051306090c111e03190306031205070b070318 68
    0x214225031900b0039440306580c032102c0b4204400c2030901e070500840c01c1c0340000392a84607249410b010442e020001c031340140d20380b42c00c02004165028a000450140b807070a10388c2010119080c22855161000021384540036102c3d04a540d2000d85d80ea540c1078020340e41d244207070341001d050741c0201c99950312188840e40e441c103c0700b42d4400010307050a203480d2808000a16040d42c82c11107565419442c00740d0072860030300115030700115900850205a07034201521241c0203000d040581a4407504180d800c4000940652051703000c1c03402a41e0900c60b950b1162854840114492000c2c90b020500308034503960403041c001c03542c1e0030070b00e07240c1c4902c40c2a03600c000280c0b00200c0607020300c0d000c0e80d55850070003c41d00790388034201c2c4035107980c00c1c81c4280004846125450b00d540d070300b8042c60036641d016480080082402150700540000e4020f40c604010028000c0081103140022074046005104105100740500c0559552390303030000c0302d00e8841d543c80404802030704800b12800b0b681091616000001421000c40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 981538570 1250 981537320 981537343
    0x31103061c0c1e0e07050f0f0f0706050a0219020304060516061d0f010e01060b040e09100f0b040e030304260f04170d03060e0718030206030a14160c020d02010c05 71
    0x103a02c40c1420b00001c1e504c1c908010b410380c01400400c01142404620381c8003962403c080c00d000b1b0b291614100d00c039a220305e1007140340c018481c03494202005290b400c958060a00c400300d1845039a00a0841d020071380c1c1ea0310441c06030401160007484901c00c2c134801b501862103035511036840840d8081c030902c00001c0d080304284813002d05070045403c400c3e0050003441008491250386c0b000707016681c9402c845111030b05c00c2d8041c43c40200c5110300014490441040030340031400c80312004110440d003241403040141104901c07180b00e1030511300b47c0380c001c0b2000001d4038003c0d5004440144c078a078034503855001c1818440d011210910081c02020500020789020384018411000c00803410100c0c0039040d8180000c2c00c5140092518100050080c114848189a40301e01c05050000c120b601d014000d069031461640000e5000700d000003013050780b0616400030748806c2c0c040c164141c1c090300c64400146031407070704c05040d400045905180c2c0015140c00041080b03241e0041c1002158001e1607217950f03007800202480c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 981539820 1250 981538570 981538619
    0x12106020408030c2406060c1e0c1008190903020708060702100b09091b04090615050312040e06010507060f1a030705030a0c090c0509030a060c031103061c0c 69
    0xd05100704c130b8003031081c1a2071120703184c0c00241c0e002c17803a201c400c14004040e10a500508011031002890038013045031030807910107600e6480c96041d000c10b5041e0307110100100140945515000b514909010301d100c24001d1144803107a03040500caa000000003000710a100341c04521440c800040c0720341060103080e000e00e8a607801b91000580d400d04172000c0d5603420751911700540740c01040007400000420340310052949400800004100e580018026111451024004a1034086411181c0081c081000304a410036015180847c088511046641c040c81c0700b200d81007200b450003e1380c0d88d84100c00030005148199400210201da0302a650304440c0c2442c00a4ac080481008402d124a420402e1304d005150813001052810300d1942c80c00c800c0c05062007008403151326098444c21050140341960180c0f44c01808807204a0f600b400c140340035022207011032011a1503c1a205100303145441202e01c200c501410400315002c01c2c5a0b0044102c03000d500035540340c0d41f0302501003601d40700d0a00c40c1c58011038101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 981541070 1250 981539820 981539827
    0x10306151d040c0b07020f09040c0b0a120c082208040f0b0a2c011d030f1f0b0607230316020319030f0507051c2d020601210602040803 59
    0x180c00c0c00c0706115a0010138142c00103220000050351294040c0c07001d000156940c0009845a00d041129800d01d50411122154045080014a41c1c0400d290311000c1d203c010521034645130714015115000142c0b40d154901d030b10316031900800b10003143e00070000381c491700929180a0b41c42401002d110b01035000080900c000050700074a5940c80702031105611007030014250701d45e100c5051034000700301d10740d5014140030030f040202c11741c01000411024250300180030390701c1c070540300e18141d030b1030b080e140c800c1b40e1807080d100250861226040c89449210303140074080a241150300e440700300514014010560110075260074918103d8014030250170511402ca16039240c140e1184101814112030080d0007122241810b41c02011960100400980340024200f07642e49180c41d0038034508110507014900701040810031054803081d40406813842000f035120001a0030013054036043d000d500c580b4640401644040010310501e84495002e2a41d44000124582d0b10103043d51a4816608150f0044080da000030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 981542320 1250 981541070 981541073
    0x15120302070b222402060705090d08040b0c161703031801020705011b0306050f1c14190c05030303041a0606120c0d11070c0e06120f070f08011103010306151d04 70
    0x242907071070002040d400501111f1038112001012801401d08240c0704040d4218028244210102240c000d0f140705816640d50702c064018460340d400303000c28807880420100c81c00156105d80442407508840001000c5c4d0700d1500c4014400080e0040402d10040781c2d542004000001882445411004c2022420760560452204030280482c2c0341030b40900d015000712034551050f0380c0d030852403144034070340b0700b078503182305901c5060030018036002001398050b91185090030a07541506245905503039104001d00480c0e0350326117040c59200c0c001983c0c000c1410700d80c003002c4507001c03901c119506e9101a024142500341001c0000c500c0c880c41c03055483d4482c41c500000d030204a201c0300d0081c0030003a458041c05c145440001d90314000c80b5055841442080090600826015990340741042c8108100000700c034114150315000303e0700d030f10551154008094602c540003d2004040c0980e41001e0601070005065a1840d101c08001d49030040996440001210b0b0100c0c1e940003c050804112600d1103107900c461800703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 981543570 1250 981542320 981542369
    0x2060403030b0a0305150907210204051303021c110304031a071713030504090f1b030b030a03050705030c030408061b03130201120b0303030a15120302070b22 69
    0x502c8a182d01070492848244003250001540030740d009810420000603030b91b407400341d0b428542c65070010040c1040210010461042c52400c2c0c0244c640200c030200582e4450340200d400b02c4100307000c01405a04950b080c1140000498583c00d061200c034141441c0b1423054410003421366000b038008445c80c2405519001c2901e10002c0400da202c0810b05140d038210b89c081c001c035054120010680d004141200c000c20701014418403c1e1001085c0242061120720148e0139940c0140001240502ea000c40c068140158103109005541070404040c0190418400320380b0b0403103040d404450f068945100420410840440810041004042460140000d81810301e02c401150301015143d83d03c220301481402102d1124103000040e03107509003003120021680e03034801c0707000c1d106609009905020100410455600076004025801c00070410811440c0c0ca8136190300001804120213001070344a0001485804607040c01401a9200d1400315070840d00c07525a480b071070f007016400030940301203c50517a001c400e09 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 981544820 1250 981543570 981543581
    0x1806041e14010503070e0f07141c0f140615090d03030b100f12020307020c130506041503121b0b090a031d0d02280e0103020a08060106080408031e070206040303 70
    0x3c22006001c455241c505884500c20300503011500c50240000803880c62401004584035010707249007901e4407660b01c40b15140c1c4045010000b01d07115410245051200700d854410225035480513000c0d40081d8651405211580c403070204824400b140070009030600e41d484000d0104400d00ca40c0d0041441c00e01c800a00000d80f00c031102082c144090084130100e003540046400e0aa120300301401a141e03038490400b01d06d8849419901608052100c4089400301d403942c00c482c3c410310342501c0900100400da104150b00e100103110140040d071603400700c01c58842c8601c1c40380500d4014000c40540d00b603c01c0e11015500c25050b02c0b81e81c86540100802820150006240700c800207035a5495500800c100c004100b2011100c05c000b8070400001c0101900b000f10010200300d80c25403404c950103495200c09030545040303001e002c1a80b1951301c92000003001c107000100329059881c42d036140e8400d80c4566484000d90340010704461100380104102c554182228100d1a20524090740281214145030801600701da0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 981546070 1250 981544820 981544829
    0x3070c0605131e09050412030c050f0d09080405100203090306060405070815060f0d0902041406060d0b0d12020d090e130b041416080c040204051806041e1401 69
    0x601400900c251030840b1030700030212154094840114040c007003041c0a200910b8100740310b4a890074050000317224003040300043c0c44402c8d850402c4114220101034a1501680c0d000c40d202c40e104000060044060342c12086440384164401406c0170740742c000054030103991080d0b050040e44045490429442c041004d0368000c0015141041207090802c0c00600c2844000c15500c0c00c01c010150408507519004102d0365040d81040360962034030701600d03881010f00040401640b08078100068844c40020110045d8066180100828940402c8041000190980000c0d0552016060244002081c1c07010b00e4030341800741c940e02500103c0d00c2c1000183c60749816030130040c11140301c101080b040f200e951240a015a8000c41c600485507141c1c0342c100600c14980542141a014411001c150020650f03c030105a03042d14046d550031a510106001c200e008522540c0d52042c031100406140070030040703105410200140002c181813100c0c00c1c420304000c1c103101459400a944801e19030700c1995407000c0340d0150 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 981547320 1250 981546070 981546077
    0xf150c12040303021c0831020a0f1406040e0f09010f02030408040e182d0a0503070302060901110d0905031201030b330609190303020601090f092d02040e03070c06 71
    0x50403d260103224402c08854201f080c1c0004103008980d881d00310361407002d9503030b0040c0112407950f00c41c00f00c03c011001d1446850141e25419a04820307610b0440151400d40c0d00100b00d40c1e201d81c2d00d6030306d03d104002e00640040219562415001c041e01d01c540010b602c214020610240d980b0318003030f8210b104090040210340036860030324004030042d030042811018070400c0ae50100054a006595000d40b84560039602900e1007208400d20401c040800a04070050294080d1081c1d07545900c0050300341d8031218a01400c000042001090103c4551f1000d440240100203c03401d1400507900c2c074400b4031003a0803d0f0380c415680b00402c05103504603c28038000301001d090741406085184411450703909500002c40c4075400204523800c0b241c40707c0000d03034441c0384040000c0d45182d50f01e08019490316002e00941c2c0e05242054252044802c080c040d0442465000c2c6aa00c81c6800f04500d880314450031102000400c007000d110203000d42d0b80c501032071244415203800b65540c1c40c194540441d585525a1080c800d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 981548570 1250 981547320 981547337
    0x51603050307320a03110d0f0b0108070f1808150405120a2115170d1e031e020a11070510080a09020d0204180203010b0f150c12040303021c 61
    0x500040200f603085580000d5507658842c1c44581081d0f0141c44041c00f414010040800c102044121507084040050040c5404125540714103004580d0300c1422120714001c5032a080c0c5502215101da09102003814029074800440f58980702102e0410800c182c0000c3c0d4824a0f00600c001d1003000c1c46082d010030311840e000e910f050142032010b040007105406d90040e1941001d003214034499150007004004090b0035200c0c0c25262202001c00d07200c0720600c9444468807840d0765415000d07010b0b92010006c11100f10200031101503c0c10300714081d04040d0940c40324840020358048501c003041c009040140d505884105008815010f59450210a548110701c584444500c0e00b00040c0c004102c00e4010782c4021005c6000e42460010652403e4131a0f0002d41061508800000d121844805081c0240c400c40080c410f0300c01080401603004801c1c0316803917112191640705c4850100c440c0060450030203c406803081104a1240901c103034000e54410380260b0404071207001c80e800b07040e0080752405140d0505200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 981549820 1250 981548570 981548627
    0xc0a0c1d0a0c0f08060a0905091b030703020d08180a0f0801110301052409100e130504030e040e0f0a0c06080a1104030210030b090c190c020f040c051603050307 70
    0x321501081e1800c00f44410800800c113542c541e409051b010340301001c811b2299003403810b282c07981d81c1003402d80c6174405c840c55007031001c00b481c000c1181000c498008181c4100111580c5400382140c0c04045c0e4131182840191300d8078455103507410b0380c000404010300c0d800411480e0000540c00d50340f1032500d52044803000c00060040d544c0301c001c0c55117010011a00c00703422070001c44c40c0e080f451040b206c00780d52048907520480d216991110040e00b048006940c0441d640c1010180c20081e22019180200441c0c2d4500500b0307100c0c1031a03400303104581c50b20411121003502c85030b801c80c00d0210407441075400300350f10101400302d0b03500401000d801c807070103030030400ca1380e51228100071541c02a030100030722400741c6c0300510300a203120350000310000c4401801072046042c041c50101c1141d00c03c220302140c0c050900d03032030010680200740d68031440760050000301103485001c0130130000300071002d40203007480340603ca0740c4966250b07038560080140c4030351a803607641d042c4000701500100200c01080d242240f0480c02c0740c0c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 981551070 1250 981549820 981549827
    0xd1b0e0a0302100c0f080f0417010203102706080c1206040309090f0b040203090a0c06051303080306040221041e0203030703122403021e03120c0a0c1d0a0c 68
    0x60a03c40d2072812840010051426508818407002d026020010104800c0354007141d40005200311a0142c0308228940c0d043c0020380d00382d020403a0082602841d0101c10005c0182a0800041c02c8840002d502c4010002c0d14240088a80503040070b0300715031008610070142c0c104803051080d04d2590b80020096480c0542c0c00030302981180c042c001e010780e103a0517601c00c03e01c21500302044080c0000c0c010b540b280780c80128181e8900c0071802c04e40306284035040016116014008880b032241c06003c2d400c8003681580c55031806540040e003129003055080008406000010304154805c1c10300700000000c1e402d040c00c0101048100ca501d001d12960040944401a03a0003c02c0f6151a0340c581009541049001d05000c0105107900b64800c110040242c4040c0b014482c5a1a5040e05d10846410003100c1c00314208407001c5044c440c01c1031305544607200141400003a100600340000d000700880345401c11aa03541030b429150380e4022035043c0c102c1e0b204c46400303020b0002e0035680700421403420800703400b0291005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 981552320 1250 981551070 981551089
    0x60c03071a0c1b0703140a170f09060714070b130f0b181207081014130305070c091b120c0912021207030c080f07030203071a0d1b0e0a0302 61
    0x118401a0480c03c6012180428000d0a000f07640100c00c8000024000d070311039481c0e200038001140e40f02e500c601a082182030200543c1c8081240c0c0d81201d003025200c3e070522441d90702c242c1c41039400b14241071070804c500000b003040307002402e06502260740b030384102c88868000701e4007901701c01380c480c000c00001d001c02d81034142598685070360160042c0340b141ca66004a0b682c65142854140103010301003003c640c04e80300160f41050380707007902000c000d0a58601c5481540d10b50688440748000c070300054500c0480d03c5040075201783c0d4060b01048039420359503810a0101c41100e0703103001c5003510024801082940140394041d008401060500c40e12190003001405070490740124098500c02e0401070056440b44c807a5804000c05440031034039081c1c1c4a040106160311a41310303480780f1344a1014001404000401e83e1000c403940500203110301801c10700700d00c25040110031581c10444051001348032408250003100254003031480080c0856903c003600400032088020b28034000d5004c030301d0410050300c03400e40d130 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 981553570 1250 981552320 981552337
    0x30218010303050a05070f0609080a020708010b0d030f1403090d030509010911040c030b19030c06140a03330602060a091502072906011701081902040209060c03071a0c 73
    0x31660b0301e250340703011041e1015000e4081c080723034139003000320b0b00300030300c041c01000c40c80d40a8085680c20303590fa41003d42030300c441c83d654a8200f50202d0406000a004c0d000415026801c1d003804400024542c80340500c64200b100d80c0c00550707124211a0b060340303800d0f00c0307030f56001040e210080c00101c40d0b0380c84107100c82004982031801503569010002c403841c03207980021400b4500070504003400744c030403488405030040b134002510800421000010b28601480c140600303007146408650070030409000941c02407220700fa1846490102d0511003500c2a10313503503820306501f5a10710003601c690400c0710003807820000602846115151503030304030105050200000c0b41c1d01c40c46134090303501c8655250400014050342180c1e41d2041160110140b000311041a003032080000781d07146114182e01d0b907104030580c00c007840703510225003185000c142c00c3c400340c50304a0300d214000b4001505d4508580701051465000303100c0c86066800200300e00d001c000076180342801025000e10314028908000300c43e1581441945e50 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 981554820 1250 981553570 981553577
    0x50307080c0c0d0e03030c1906060f121b1d0406050604020f040506030c070b1303030509030702010909090c170309030606101e090f0b03041103280204060905010f030218010303050a 79
    0x801c4d10316a0307410000c8400b011140410743c2c1c120242c4100e5170410a811031007c80b501400c3c40c41c0491006080c0e5200b20803645456516070801301c5948400418270980c120308032804c0221400401c07400f1369600080340c407910400341c800c454075140c1801000c41e60040c046070700c124010890710b0401501d10050b00d0139500211030342d55407511029616012840349039401840101d500080141d81d4003040808030a09001e43c03018401c5982c0c00c05025101d1041000003404654503031000e21110540d584058603146c4174104000503607442c0d034649495004090720f001456440068110200c0c24103124254125009039103c21469045000250030f1108d501442c038103c200115101304114454844200100702c200c60000c030803600d03131500f83ca0561040f18280d921220032400ca040307500740007440d40c0b400b20300f80154190890025403425803c031178000c1c06a07400703602c4580c0400c1600092041c5030082c01c2c117405481c0803078554414011550071381110b00c20f4040c1900010400b00340c005044442c1001d1515 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 981556070 1250 981554820 981554837
    0x315080606130e070b0406090b040609090c030e060c03060a0506120a0209150a02030901030c1701140d0b18121c0203040204180605010905100f03110109050907050307080c0c0d 77
    0x70344001060710302c9401c9684d1007100300006100800314002d205440ca00e68684900c56210022180c162050b44601030004a03850000c00901c1040d5001030740340141460007082031b5410500c03183c580641a5094001204000288000c0b490304150150090400307449040c104403515001c4102888010074440341c0d0707a0001400c04117a0342e015009007103c40b05007442a21881ca0740e10081d03480d00000391160100b0b20b460040d0054a000e907950010401c00e0403150044c0e6800c2a048003005001080000d4000798421501e03c0082c8201c035401d03128504000e070310b1658071014800140745c06080072101e003021004200900242c400c0f2804448410003c1c83c0c050395a841d58030200d0000e100c0001107460b83d40d0031510f11340c10004c41f80c000b00c3c101c80b41108103011549581c182074041d101203116080351142114020400a03030a818007441071070341414029102c1c0e41d40c50106240c4030040701c84000180f000010444429081000580c1103000040c2c51030410103a0380d04540d4039105040f201c4140709120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 981557320 1250 981556070 981556099
    0x907020c030d021b0a03080706110f1c06090b03031909050604090f05070201181104142e2115020417122b0f090b06010315080606 57
    0xc20008840c00300203411100118040c09000303489000f07400300898401002641c503142d45c9002c0148500f0b594100c1c5800d8509800c698031400180031040c074080704c400e0184030b040c0541d41e014024003901040000e0441b901e03440e00359220308407201030700b00d102c01d1841c082042c60a03480001c15900480804100c001c0c00034181c41080c2c4014020740d1240d40d11503c00203000c00c0c8207070b0b00d030061100b1010060301070100d07882e94001031f400da641d03d0801c005441d07890000503010408140010402170005800010000e402c0822502d000200f04c42c0d03098010103c01c8646602d002404101402c0e99a074220002d0ba14102003103401c01025524000d00105060400102444048103e4074a0240130038030440d920b03559039410079040d6844440e0783d11940a0170414288821505040702d04841440303020348003d04d802d100003081c54200c800441315039070b45d0f010003800e00051841103800480c0148410b4a051405500040641d1240707149034503007000c800d03c20490304500284698218070100c2c4c00b6111241b00e0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 981558570 1250 981557320 981557323
    0x8090d0314180f010e2202070804060e01080c070812192f04080303071119030503062803080f120c1e13060318060c031506030c0e090702 60
    0x40d41e03180c000789000080328804284003402c00d991403207099856541c3c0b6025000103503401c000c50443d03542c01002204903e5990164405080050001c01d01700505024154a629803107410580285c404604503024072440c07503820288066210301c2c8040124585100c0c0e80da56101806000011401402d201c1c0c0071035a00152100354086e10503103803c04015462081c44a2074020b1441c0101e11800c07982c07040c4020213000c40e542144c09030b420800045166865001c0c0844980d9283d0a82441d0360054104000c1c00ca414102d4100845002c1e40c0e8a070b40300e0034200100600000054000c901244c01c90a00b070f100c1c10250103e40c402c41790041400ea0f111301a0740411051032050400c42203a4802180402820208001c050a40190402402004401d20400040c528031584c0815140030310300c42403c00c070040c401c0d0807003e80c0c0512441c6850f80200c050b500e180c2030721039034103014021903101d0148a10010450700540020401880c081c00585804180038209a8001c0c030030174040c544200c00500c10500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 981559820 1250 981558570 981558587
    0x2306031005060309060103231c35160c0b06270a0e0105040b160c12021c08070917070806240411030c1e0d060306060902040308090d03 59
    0xc0c06014141e41e4030704044c82603203e60003400704840c041c4c1b130b00500c454115405030310300c3c07207507800075009045480d4001c1c0a00d240b04070100c040c0080000c0c1040210000341c008504488001050034602d000712a0740c0300c0905d880c003008024060b6448594103e0301d900d98803147d4108025005032580406490b160003250459000101c0100041c4400e50300007141000500c1d030600c0380d1031942042250300c4661071800d0903030b40300356800b4112a1207000415004180840d81d04012020750400700b1503155903503200005523505001e4030001d40c100185017103207a61000313003d10a054403454840c1441c039025a002c0c00704030140c014070b04403060300c10350b0004066003004200064900c407412224076241c150381040041c0140350b40890441d00c15903d002e010704090040c0e005040004c0100741c00c5940350b8503550001c1e000821001710340000034800130011422800141020720452502044150540c1050700584156510884000f4030400007007001c5111039043d40c0000b1000c65a009600c0d03501d0500b01c81010 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 981561070 1250 981559820 981559829
    0x406050a0603080a1706040e0c060313050d0e09060909100e190803010f080d1d0d020d030224060f280e06040c0201090b0c0d0608070b030f0123060310 66
    0x2030001c0c207601482d800c0448040c40f42c900c405c68201661300c2805000641e04490881002e80d4061680030703070f85103449006558480d12402400342c05081235201c00b0b103000e04220600c0c0c0403c00d03c02403a1480e040041c1250b50041060b00c00745403074205107414960f508400f40356841c600380c0e1114280a00315081c0b050030121142c00c900c00701c88000170309248450768400c1c821030310245d44214000810f40404503060500b00c3c0c140d00c0c0e9100e909a03040152402c80d05007000164003012103c40c0900607503130a05502ca0040c06640140132540041200f43d882e110f000b0102800d0040342020022555107050036130a2050096600c40703020552011082500c64059281000c42404004041032003c0055580d40c8a4030080b076090059502c01c19083c0d02300e80c65690050a081110000115070064420081c03409918801000550650308e009260400c8510b07080104440c20000c24024101590b06549002d826201030210810044825680546841a81c51400761201200091050080d000d6000042 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 981562320 1250 981561070 981561083
    0x5040212040323040b0a090807030c0302100909020705010b03060907080c0607020103090512180d020f0f0f030a050115050109120b0c1306030e0d0e0a090b0402070611070b090c06030406050a0603 85
    0x494440709101c174180c00c1002024001524180c0000c1d080800042c014126500101d10799009420b5800340442130520703101c0c54041c04810800081e00f80031500c000c200060095000003805146030081504000002e00b20b203103250f000e00c0b814456103001041001d1200d60440302e1654a03200b170b10047c5e001e468004006486405000b0b007030203821807001d004021005003030380340c10034030054007040003000002c051010790440d4850b00149900e080c80d41135082c4001e0002c03d42808d500c40440000d14122100780201c6403a519007100440100040000001401c070900b848100c2d20b01b4820010078070182e005000e000c0e0400300c2d010440358030702c490440d96a4000e4070004010a61549030140c06003015030215000c0b0312410114110440c412842840050740040114421034580416580034040b150840e0b68420b03070030803018000801e50703c1115070200c407a4000c0c2c0d40b65009420318807058180288824003681003003107a80c1c400d41d180b000302c035030080d40490005010b4940d402c040008296580004040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 981563570 1250 981562320 981562327
    0x91d180618060c0a080c03100e0c18090c0313080904150816050109060c060209031b030f03071a04030e030a060e100b0a0303030e031c05070905040212040323 69
    0x20810740c0028226a04000b00e401c503031200e0440c0e800f140704003118a0000740d090800700384100420002150408401c0c0c2d40203807900e41340c42c07683c090700101303071040880a80300044040764148075101035024844c00300c0f2258160702c0c000a500c045031100621170302a0511108500003080154425a807084801900c02c00000c4180c0030400386000c1c5c01c0c00b40720381034841d02804070604c0480400c040c0a540041c0e4a410040b07141c8103040d594890146000c0b68a582c080c44101d81360341b001c2100540c0c80b100d0445459500d040e107401d160a1800c4078170700c880143c00400c142004110802c0c42a850031900380080303c415621401e04868030054821015418000c1051520520074030340c0101800203044404e40e8000c180b60309605c01111014043c0c9508460520310410109009510907841610580152850580c034003902000304c1d12107052007020f880c3d850003030005079035201c21180068202a10304600e060381e071a18601807140001c03c02030820118506148060300c04001002d034800500c65240d46 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 981564820 1250 981563570 981563581
    0x50f010804080d1127030c090a02040b0c0c1813020d060204080109030309051903090506180901061205150105220b0c0a060e063d06020607030c091d1806 67
    0x140398003000341910b80c07040f26051030454802d170f40c00701c41000c80014000e1035203110710b0003886034290005200845441e070038000040c3d000c4c1c0080041500b072081c6400b6181980c5109c0401c080b8200c0c00c0107805125004004100d00c03080031030014404990100d41840c2003200340d02d4a4000703403065410100c20b03942800c18502c10513806800c1243c1c403d00c2802614450100080003018a4044200250001d00061020492800c0c214010611401c00202420761b2400322408250001000ea00003c00164406142e54a4010520403550043e00c042c4820b2030203030740d03a00001d00c2d9002e03040386449041210400f801610307000d40e03000d10003000c000c81d980780c850300700b4504281c4601c2c4250381510a0713420103800c010074200210f0354038400e40307901c070102442800510b1004180b4a600c80085810082000d502484074045403407407008000342d5004111a01c4c1c0028000c0980d00c40714407103010701030484002e01c600001c0700301d40c40d05c1103168407080805549806502050700c141d01112280340c00717007509000c03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 981566070 1250 981564820 981564851
    0xc0f0d06051c020f0301020a020705010318020a0b070c0e130212101503050601120b07052101260d0e010309020f0a0b0406080112030215070c150209010e0109050f010804080d 76
    0x1c48038000c582c01c4044c42002000e060907031181c0b0340818010780000381c0c107000030342c02544420f420300b404084440381403165030701055200c40250400004040c01203100070030401c2848100e005004144e0030007030682402c03990100e507490304010007803061040d11001100c0080400844001e00c4500c501403041c20a07103042000813201c0c03800140e503103024140020074400c120b01c1240d1a04c0f40e2268400c115956001001c4555412060018001a00e00710000a05a220840040c060040701000701e80c94000d2000c40982904440300412403504080405560030313400528620038010b082c00d02003001c20040c4002003c00880e007000c00e5001802d900c1c04241000300c54090400c0d5011502c0300340701640c88054208080d035040780001d0050f402030040c007150400003402e0340c0d04138401c0d040c41e2103c4140307a511074130000c0030502c3c840442e903400f0888500030343c0d221414811044003802e08131078441c00d120116028040201010f4140300300d500101d410003043c00b003100c0ea01d0f19280e4041200440851180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 981567320 1250 981566070 981566119
    0x60f0c16050a050a0e0a021c1b0e01034203110a0608040c0b090609060a022d1b1f030204030c05042a030b060a02071a030c0f0d0605 58
    0x882c0a10702041020800f41044aa8141512913030040316402e9550601d683c0040d6001c814168800042c2998900c4d80d5804e0b401580c0d003c000e2101130340190000b54100401051488400c0707810107040c00d104090001e030040c0c030000124042c01c600700f030200250200b01c81503080342d4003a407440042c100000091112050030b0415245007282c0c4a01c2080d500d81d4201d42d00324046d20041c00c0300c203442e4000c000c0f4044400060108010107800b0781d041940b200c00003a100c1d0010303010000560805e046022100c5010703c0800183c4000036102551001d5105180c4c1d0344910001c1c0a10802c421030003e200c42d0f41d00c1c4800d07c8510455074040341110000e1038070080182d0802c6c84219012400f079080482d8918150156041c0d50380c07400740c01c4020350784088000c880b24652410001c14140da442e00400c00c0d41f04c100c02411a80d20940003000e0b018a84106040b54000c012241d1014000a0081c421007020710400c0710543c0100fa070340342d03482d00b0441d03080b00e000703140a6000750f5018080c0c000b141e1402003203c828 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 981568570 1250 981567320 981567329
    0x10519030f02040c2a022e050c28020a051e09090a050307051b1518010c232503022e0f030c020c010503010b1e030a020702130b01020c060f0c16 63
    0x441f044008400c45a00c001091010107003044c9602d4800820900e100c2e0000d807141e4010602107030600c400014450b2207800c00c01d41003074004040c02c0841825030500c00020001400d0945404100c04103510f00f00046400d890031952107500c2e050003080304030200300645690720340c10034180d075664246461f00c40c1e07030790302c07400c100e04d412a07181e02194045240284c001d0b031300341e10303c01c004502c0d014100c2a0460304101d02059a414410004401d0303000c80d0a5045071984055403080760744503184001c91041c034014000b400e0400c1c40c0741d100000f1100710b5030480203600b113a5043c2c0d1481142c0d81d1100301c1c101404a801c1a90700001c0d00b4042c01c91146900800d103041c00010b64070100081c46c00343e9403ca80320f0001c2c9a0302408a40200010090481c801c002448503448140c05400c0102c80d007414103101e0350050307900388042500411004c0540c90907a184d12020039003c031040207030401c0000040d40b54603031108802d101e00d03004140101071100c458101d032007010b0315600340e810910480302404a039410b14000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 981569820 1250 981568570 981568579
    0x703061a090a1e020a11060405011a06090f093103080c0903070e2d060405060a0305070315020f0d050f010f030804050f0a03080d05010519030f02040c2a02 68
    0x4158141c042e84685845040c41100c0041c485a0400ca820003079442044668104544410410707140c02c0b06011690246100d50004900c4000e82d062125650408000c214450402000b40344416699621a4080d44d0307001c0d500b1810583d00c020840f0740c0c5100c0c603050000f20010740180c3c041c08242460031010307643d20035180c0c032070141c807502102c4c081b50042c01038103501507202d003400f8080c124080700350a6000b1488020006008036111580f14540d00b24000c0b0415400900207000c0103240a0041075030111090ba0828640c078031f5034540c0350780c8807c80cac8005405402c06c000012408000c42d0104c071120142e031508255224000c0d09040010a0708442c1217800c0700c1524004200c0d042e1400c4c0e40012290440d4030741d41018108010400360512001900e50700212203a400000070b20240c014169816201c0000581e561400c0280000902040e1090180c211400414000505034819400c80700350143d030002880000d8003010303603454100f410030940700071800b40c0e21402904c0a010199030a4800d58 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 981571070 1250 981569820 981569839
    0x503030a0e0310090b0402091f0306060f06030c090e1e150103050108010b010c3503070e0d21120f020c010e0604020f1c0b0a02090418051207050703061a 67
    0x701c0309070480703c99600080070a171180e0041740151521f80318454009800414158440e00c58110766500c400700c590080b5510303921254100003030314150b130062005098508080c8061480c48100800d00300c010301408400304010800b14044005446140154140c50700c02501d135801d00b0381c0044861403c0e0b0304041e001900b060b002140c07405040c011842c2000044c2c40d504c075812880d550341c8100001500f01410036440c10800c00341c50b0102c8513004203c0c180050700c1c00e5942d082c030f808001d00810042c10b102c0d025070b071402c018000040c942c002c044244101112403441410007184100d50640b40320140b40030f12414050010240b074415070081030005003501c02040305020300b0700c68944030002110046c0d4007440725503a00c0a00e0400c5a000c40343d6424031500c0903010f605079582d42c3d0844801b61b903c010159404285034529052901c5a001e80a082c0c90110707500700402d50701c50f992090384495100d90300070081099820080100a00009103074410014851404070b08000d160a00340e40750030742d2140d10420b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 981572320 1250 981571070 981571093
    0x3041805130804090e0a0204050a050106110a03020d0509030c0a0305030d1d070611030c060403020109030e040516180305030705030d0b0904030807050702011205100501020f0102090f0d0c0503030a0e03 88
    0x380001c151003940240e081c1c0c1020319155201e0014001082e03040414042e1140000040e607c610a45200314a8164002415410110002c10060086011011952002d40d0080120360000b51017522000789103011680c0c1d81070702010a084c1591155000c0d00a88205004400c014001c0043d001c0315017040750401407401d40500da00c44202c0030444189880c0c0181c0400c0c0809403041508011031030003501101d01c0c1048020042c0d00d0408115400d40050350368030140030070580c0c800000c80141d1802c85d82400b160804800c0110481d011541c00b0050101414411810200601e01c8a00854000083c0e0f0b803a00308a080003501d9501500401040c140b0b0414100d02d2441c141c0e102ca40200e0301039440c60780f00e0ba11010305440f41c2e40000c0080c1c0c10b003d4540d80c04d103031031b4036107006142c480d204520320700c081249040000380c03911070b0540c1e403103c1c564014048001c1c5a202c14096402c0e048086401c0084421302d03003000702308080341e85c000d603415010000e105601640c104c1402d400c02e0000703800300c1e806a0b0a0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 981573570 1250 981572320 981572341
    0x6010201060506070b04050a0b090a0c0501030b010215180d094209150509090604060510080a0e0607091d0105100305150a1e05150f07050f03041805 65
    0x7603024965102d50b0610046000c50303c81507007554402e1207581140c003418200d454421b83d40034111889a002d92080d901101003005604e0b08030700402080c203060085e040c0100c0040d49819402146612480c03e100c0050f00d000001003604065090b21026608142c101d40303401002d280040c02607000c406a4591109001410b40035042c902110200000c0c6000895070200d1204840c03042100080242d52200495510159a20040c501c1000d4543c07035590342011080c040003801c002c0401d44224a000402c015540b641d00c055041d00d41070345404021b9030f44006e0002e0040103221600f0b4100d00c100402c0210f260b40100021058a4159104a9102d2205414035010540c24040e298004640d1101400407034000e4001a8108000c0c00c00301c41c140c68544080782c0e017458554400c44141c04401c0440000198200d511000b801c000e440704c049081c01e001e08054280704200c502055104001034810600400b801030700000fa8051050300c8e40d0b90342e1109000301440b00c00301d80b072620900d420f0200d403034240f0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 981574820 1250 981573570 981573581
    0x90a35060105092806060f0215011a1c02040e07023a0c06090809120304030503090f0105120c0d0c02010b0a15020109050601240c151503210806010201 66
    0xb0003014648140e95110001900c0e00819035001c040d40c001e00c0310a03036a03103964000d00028094954809441c81901e0320000c0ca07015640e00442800100a0010f111003209039145c2c0740c1e1f600e050500da903130703036124080380384801c104a4401030002ca101107804189500e4140d405409019a642110702c580407603400b01044c44074a0b0f00c40e05c115180c002e402c08100c103c492100000e03120360306049060613020b4440c1c20580300402c3c401c071112980094205c81900d40340c2c020041d04070402d0000d41c10581141d50f103d80c0c0c0e1164080319441145000100030141e80318104450918407815280c00407400c109801c04001c0e0010175401041505003080c0c405031034030500c600c010840d801411200c241e4a003094501306841c440192900715522001c035000811403c10045008016209a002020210b06626184801d40100100c1009640004040414042080c500c0e00b480e40c0039001400c1d0340c80150a41d130049040d0f000800448005580ba0600c1d201040d1030001203d258541e822a5510138004908851 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 981576070 1250 981574820 981574829
    0x310030212150601030b01090b13150908030702040b0d0203120415030c27091d011802030718090b04050604050606091905150406030c090615080c090a350601 69
    0x41402c0c0000e00158826080750340c00404c18100b0782503041c2c40703404800ca50351012007015224074046904018240d04a04501c42170320352860b19101090070b084841c4c2e200d00c24040701074030039500d640305440c035560360300c0003090140d500904a80340e51407403005d401540e42151040034140910b01442502c013602900441d8401c81c1d5680d02d048401c007034114455651680c0c0900340c2d00440d040c03403010440903410310685808919840000b103400403001840e0342950302281d41408901c00b07048100c001610b0000707040e000e81da540c003000d11410000b40d4540c002000c041c1d00c041c104502c0c48050205014021455902650140095032444e44e2848207205e00050180c0c1c0010841e02042061a680d001c1780d80066007100c201c00c115120b41510700001030030b84950341c00c186c0e03540c9042c420400035002c1900c1100010301340d40402400b40d00b40035270054840440100007214034000050500d5050ba1840103c0700074001c0300250010b0900b0302680d461380c84c1d06910b441d41d43c051996107030860381400011520b040341d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 981577320 1250 981576070 981576103
    0xf0307030f09050d021e0102040e07080703200403060e060108070603020a03020c0d0f02070e070807050906091008090106090504080708131706160509010f0e0609060310030212 77
    0x5864455049004007064840d29880940da00e0080c00000c4081c8030306044131440f82c1c000c0c18100380000e000382c004100c01408481c182e01c100300c1002100c0131804c000307900180c507041840c2d01c0c1e62000420340243c641414030320111071001c405440b5803444500030700140c0707000fa1020480e800c072600311a556180d007801089100d0780807940400040384a40c0042603510042d20b000b504000510407a24580400c0d50140401315600b0001440400c0d410480f5600402648291031058140410054031003040600503008116001034401c0254a483e41280c410107005030124411000c04500202a20780943e21445654208900050103800a0080710700840d0040c1280c3d18001075942c4144040d8800d81c0c001c141c0805441002030360707a101c0000504403120034400f07800c10f46402c8443d14011300181c001c0f8402d201c401e0040542c41d99110b885034a002c034450030451031424003940040e540f03005800c042540f1810010401c5000c960410000040342c1c800c0e40c601c500c0714007074001c154403080110032401e4403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 981578570 1250 981577320 981577327
    0x20a0207091d120906040f0b0307020f0d0807121e1509020c1504060e03180a05010306080d2001091b05010305040201080a05130b04050610080304050d060f0e010606020709050105060f 80
    0xe4080c0343d0002e0070700c418001e01071403800769642420304d1a0b107144c0c1e00045c48031401004000510345c0600c004c00003552108040c0040b001d250344081c002c2e00f0090161000c2210071018a01e01445a51084802c0d410701c000305095628580881c4001e441c1c412803083c51140440c1002404214034025200c920a01c0000b5081c03541c030131510740803074440c01001550465201c801447c29008240f00a16560040d1540b905030b0740640e41c240000c04e51154040c9042601e408000c00000601084210354100070b403178203c59007240d09610444107000c1150281302d552a2480180070049000140e107040c1d1007018103003a0380b982d2100190112001180e0281c04a403443c400074890f15241e0303008580c0f01003044070f50780e56109182c49451501d201100d085030b682d4031010034840030700940032484006103003003801149020b085c40c02254035103a04403c020591030321158003000e8500c0c1c81d0013075140c5035045030007084003030369461001317581d01164030441c503940c3e00e04000403507641480d008a0b26660441b0030120314 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 981579820 1250 981578570 981578593
    0x4050d0f08190b060d09030504060306081f020c100c0e0301110c0309150706060f03060506150d0902030a08210a09050a021c151505010c0f030c02060409020a0207091d 73
    0x64242a002e41d540808100050440e05c03d0901c07460151602030b9541a4a607801c098000e01141c005800103d165489043c1d810350041c031b07195005001d2862441c3c0580c4071584ea0b1030b098a8004d52181482110742054510003016030300c6040301c0d020490031802881a141c0300312110459124004010100d0b8004121040150602c443c40784920f55901c080d03030b442d00050f80c50341c404a0346542c200c50585580c0c903034100144000c0b4007485800c00c01c21070304d09806d02c03481d07070643d04d00e0b00ca401d0b69201c101d6203e540f80020355030244004141181c100035000e9841c854901003000c240c0c071420512003000520400320300c0b54810703803141200903640013000340a14031550b020407c0fa016080513000308030404090410001d54860100610003190080c0810302da040c2e12500d582080c0d0503085141000342c1c0101080c0030420200482e4540c1e60582005400d2101600216459119035040514480d0000450342c0c4d8141d800100c410441c7c80ca684104007040c01d0f809a40c04190386103003030603110f5000c0b448241 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 981581070 1250 981579820 981579871
    0x24060909040f031403131202190212030d0e06070f080f0622090f0b09162c15091503031b0c0d1109060d0f081804020304050d0f08 57
    0x1c409009003062102c5004c5010381d588150f000b21101c2d4861104031240d64200003c3c5c101a488200c103a0000d407414120480400c0661010491b010340b01d04894580d0b100078843c24411940c00c03108084043c004240d18107411aa01c603010340d1050f0000e004a001e561045102e0f41c01c50740103c0554000d4441070f02e403032040280b45c203a111400052428480748101018829201e142c21461040514108179122030400e80840e5100402c502c80542250b030080070070640700b00064050b101643d000510a561514008081c0c0301c5280354400142603000602064005074884c0e00321030303c3d0450780d00086944d459220500b101041d82c000307815600034866095003421800c04d801c18101d095041754040f00443d00005d0141c45844004d840b50051300e52544000e080c60103055601400640b80c06030150f0484e6200038000d10400c034042c003c0400825600b401100c40940354281010007030095460742000c0c100b2075120b5002078001c00110720f01c04150b00580340208621446502040d0344129000080560f81 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 981582320 1250 981581070 981581093
    0x504030302040906140907030501120303020f0f031e13030509090411130905070b0a0c020d0309050406170f0d05040603090809042f07150f02070b2406090904 69
    0x1101859000e01c40899810300f0707407103844020a204800036440400c0d91050108540014064400b0103081100511208054446545002c0e178180b8005035078404515000e41795010f541c0050104960010501a40c255503204034101002492410b1030152030701903061040400500004004c241c00b4050110b0030301c0d01d84401640b003400780409032109070341c1c0000103103400100000401d5003580c92400c101400b804001030400780c000210094a4406194000341109901780d0001348035958004191041620411130080200b5024200744902c0d601c0d10401100414014070104140c481ea040014540307400080107803001c41c15440345850182002c0044024040340302c004e9442c40c0b0308000c0088152164465503405661011820049141103840da0341d00c060550300c0c425950400344074100c00320b054841c00ca003882c4051200001c929286040d54000b9005a2034007400c1084000200064046088042a2204203860300220006403c81c1040064020140700c66000601040040e0003c1c0d05020300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 981583570 1250 981582320 981582323
    0x90e07021e0f0a140c012f030c0601030c03150207021f030905030c03090108010806011a1b011b08060d0c030b0c0712031e1406010e040f0207060b0915010207090504 72
    0x60303544000d0090380552404200c007000721032010340c01c89001681030045c041203890031303002d02e040101603030905410a05038003c0a10180303c040c6408000c0c9128004104403140b01a0f100150b4a156950b4280414011042c1c88280e81340490030003140c40000d0360388200c1d0035459008000380c2c0240d207104410002d800c81c40251100b40340e5141074110200e038081000c1c2510158030401507035208904000103115032810380c004030030b5912040050240b43e9100c8062855030140c0b042d115110704032a4440d060020020254035003a51a00d42e40c418040e81c162a042c0320348003561a481655101e0500f03210000240c52000b4200200b0030205000040110201ca80c124080e01d418600b850303410749540e40040c241e03c4d010b20100e940d56018034680c1c0b03800d4003c01955101d0703080401040c034400c3c64041403540001d00b02e60400004500ba010a951035510041010f103500350115100c3c0500d00c0c000e4001c2452001c00e511410351200040c0c84900c0d01ca0151000e0141a0b000d002c24601e0b2112880c05004090320 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 981584820 1250 981583570 981583573
    0x90902040b1605120f0405040b0a0501050a050c070f080a0303201e0403080f0705070902072003120a0e030c0a060203070b1308120f090a030e011209050601060801030201090e07021e 79
    0x4059801c0041134014002e0280c8039000c01d80e8079468042000101c1d40814030160084611076002c0145a0b04441a14645041da04155645001c032500741400c0010316002000191540b20010410100c001200385040e0f1007514204160840f40740b44003800c2d0512140380d41070030810402c4405081004802113070740e1140c0c02d48682019220394441405401c50540700040380740105e40d404c14081c00304002c80081603031000440c50b00301070b45c90b092100c0303541c154142d0300d000003120100c10b552020402a00c4000c206100252070b00c3e0220fa008081c0301c80325400ca4441c1c17082c882c1050301854908502c0c021036505400a525040795540c40c0c47d5035000c002e0003d00d80740c442c1d6003c40003051041d00100105408402d4404851400c03098a0207004800303041441e19600601390400000d070400407c128008003401d00240d01300c0100b4900e000b41000620003001c40c0503400c00014002e0304070102c90b060701c2c401d0700c03106c44083c1c440221552186049a0810069108042181720b41690441c80c2c4907045e0b42d00c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 981586070 1250 981584820 981584833
    0xa020f0c03100c0314010902131505030f07120c03020d0b0f0d11010c060207080910081b1c020c0c100f0905131d0601060306080106080303010504022206090501090902040b1605 77
    0x29419645c402d0242d00c00007000d6000500d00d010300e0122165000a00380c1d244c0d880780d030402e000100500600005140710345d2256014080b98240d0b0081a124051442e0180280007e041194000300030750000c4a00082840c102403640d0345a00d806845038403070410203050b045800300c1d95250180c1100d542c0d004181030009885421010460b1400100300c0c40b070050304429958145030050200c40580040302c0020400410144980c805480c0084091428220b800c0c0b52540700943c401045428911441c2d40d034144006040305041e0404200e1105903d8103c611070340310304018600f40c6004106c07018a03000500012000c2c08986070504030400e01c0220107900203128180d01380d41c8080101e2500008605a12410040110560501450001c1c0031460000d2244030b20b01030000ea030b00e01043c0240c600c61900855000b00004820321030b02003801c241201c0340880c0d941c41401034803200060007402c1c0010900c0f1004514007080380200e0341111030740e2001600c0c2021000c1045240262500100c6144c010360 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 981587320 1250 981586070 981586091
    0x50106270c1704080a0806090408091002030d02270909071208070204020307080a0501090c05040e04020d08070f0302010b0a14010f020f06072a0b040b0a0b0a0b0a020f0c03100c03 78
    0x441d420b6210381d00c2a20f96981d60100000042d0800400074809803198203050100f01c00190302c8815286818029a0681006900f0120036415801558910300c803180c03000c10115246240403101e40e2002900401d081d5101d2411810b203c0b445100300c03000281c03a44049020001078843c0b8071000549409895842c0c101260350380090180e0b84142c840c0d0000900d901c0500550008910580f8014030848808100d019442c502c040e05038040c4d0b1140080740c0c164040081c0c00c0d510366400e54240380b0707806080e466584210745482503100c88880000d45c01986410030300740450400400400c191601c40314428040c8102c00300448030380301d0314440b4074118041c100e0f401340c65070000c0001d54024511a10740c00c425521030142c10052034403140140500740000b40510000c074404141d03c640090f005500b01c40c80c1d0350fa5056000142c50300000c090b402640c140707030020388035046e98094030403e03550344e00703990007601c84000d4035035103403041d41c05141d05401000405007042c05d503901000291056040100d0100e452 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 981588570 1250 981587320 981587357
    0x1030615170a091a010503060609160509010219060203010e100f0302060a0302090907030507020c0402071a09150705120105190603180606031b080f0604110a080a0609050106270c 78
    0x8a08a04c800141c132600140a0b51a003030101e19801030059842019600e8003040403044084007281881c140000042c490000c3d9100b44801e225032105805200b0302080c0b245040e8009510034072541403500000000b045598103241009000c13500c020038640700c00750030b5800b00042c590040349050705044e070804c00000a901c8a01842d4400d1207145c81c005000c1c6040c07280030742482c0100200c40c3c815441002120001452141a0115000f01e444c130442c2e640c1c4c2e0a00e4407841e000124031800c6511480108002d03525034800300401c44100841c519904c4c0d40d0780c4a007884483d4003c001e07420114014070400b0b0002612a074400707001d43c5245214007001042a848031422200c030360b00141d48200d41610b10702d00502c4400180790090011400801800322000c242c00c1c2c0351507010304018603401401c440c091480c0c3d03e0780b241c0405802098152003042d10a440d01c400106400700b000c8800d5400d000b80014404941d0034038900000000d08000c51000382c0002d03650080c512540c419060099110800d0045481c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 981589820 1250 981588570 981588593
    0x130608220b0708010503010b012a1401152309060a05040c361223011d0106140d170406020f1005040807020d031e03020901030615170a09 60
    0x1c1c50301890341d082c91507004004110503000725009a0400c07580e49100e90b030100c00c1408200c90060007240c0341d804050b840084280c900c9000c1d000455440c02d008000300c0640c8821032595601c0d45c540d440700d90750b0304106a880e100c20320a42c1b400204000c80c24030703030400c1c000c21640880300524040c0f00540301c0000804030b92404001600081d845507007030a46912000f43d0452181071000c5141041801200071441c10400b4020780354140c001041043c1045442c1c00c00e0101c184180c00740e40c007a1501031005c98001e160289020003080725003503802c80381e24018810003003943d90030300042c46014031400501c040540b14827011a00540300c0600c00b6500100800680060105540a01301c4a5224030009181a010300ca00e05043c2e0718101c107100009191000b01e880241c3d05070f41c6100ba0960340d007005e40b440b80007684440003058501d50598031683c1c1c981e008102c0d0140c01d0b2000c00c25a074540e54826054074000c001400845c1c0301458190800307020b0711000f41e012881d1a400f042032021640e50400104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 981591070 1250 981589820 981589823
    0x307080709180c0b0706020d020d0b0f041509020f041205010203040c0b12061002031b0606030f010209100309150606080a05071e110c03060108060405010e0313060822 73
    0x100012020301401005028401c641560220440d182c003880c2e4551005000702407080c08001800040c030ba40406c402034054403003500000404540351440b104e06900078202c3c04180e18422503d412141342685010720844540040440481e1a10350030600031800a500544041d061000103200018802d8070140e0032401440c401d90002d0b8503820a413528407120205a04050b0081c0c41c2841840d9201644004156101404581d90540b410310000e080e07045101e9000c40c1d4413507040d000d02c450700125000440794040e40085e0b00702ea80860948000b24200d0213507030b08071540b0600c191400c50505200b50003001215004550f4107a864070b200302400c00b2500d2580c40721002c150000200850341055100715648014503080540782c004240c401c00158040d074516000602c01a2040700c40896000c20021981e034102034200c41242d40c4075030001f42d4a16046400701e0300780d0300f048965001000003100b07445010034440c41400031942014001c0d14141d20080c40301c02c400300c201a001d100c0c1c5046412035003445 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 981592320 1250 981591070 981591073
    0x30501021b030a020c011206090c09080c030307171b070e15010525170a08041415011502011b1d09010b0d0f060902190f14040b0901030b030708 63
    0x34a40940c4841200426040800554005100d25100320f074005c508001031aa00340f0342084e540650002c4034004001541208140519000320f03070101540005240f816907030b030780017210915400c520030155603200700e000080040142c0d80366400030014550146c403000b05804205140d160902200c03d14044240d407000346007054803800e000d8101441c02444012880a1904c54a46401c0c40c564402c02c0c184d125012120184402940c4c0901103807001300180160364261302030ba101c4907000000c1880b9070585094031030308034680705441d500e100040c11032401d04070320f0407a00e0241e20309403c52040e401641035410543d52608201c02081e8103801c2250b081c1041529075043d005150440050b0300b04d090b82d0a103008a080300014400304400c07100340c5400e22405031300402c201c150f0080c4903003d003d41ea40641c030781e2400420350390104c1c100300d1000d00780300c00c8a40e14009200144041207c0600d402c1c000300d46070160400041c05030300c003007030024608180103050204840c81c0003c0402e00c1d0130032681c041801e6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 981593570 1250 981592320 981592327
    0xd05012906030106081315110406090803070308310b0103120306240c0b1e0a0504021e04090b0a0509210a0503040c03060e0d0305070807021c0504080703050102 70
    0x80081035201030169906a031210304540c1064000b03014103a0142184440800f16450300c010054414400d0045000c0c0f52014420809100004103c4c5c1d04035001e050301081402e540440c2c4810000180c40440b034042c3c1d01c8003100c0d200c0546480626122901021841c1402c0c05404103100324014240c40261107601c06481542c03660501089000760110f4101c1003504000c410070501c0c0750b000c004d07810740121000c00705c0b003514000010394091040220042a003842c0d1f4081104585030307580c0c07640410700120b40c625560340c0c8120030441120700450740203502804003031200740615000c41c0d1030304001d41c008c3e2000810107004c0d116100368150031100b83c01d07000e840f0410803e0048041c040c0c0c4c6101c428502c200c088581044401d01c0480c000d51118804114012001078280304083d021400196080a0104000058904039035114100d40006e05d010030700305404903c05521904401c1c0c8109929806424140745240c4a50100880f505103181040024000400c0c01c15080c001e00e002140b040300010396 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 981594820 1250 981593570 981593621
    0x70e011823100c12200610050d0506040809040b030a2012030f0f0f0a0302070c0b120a0c27030c050d02010807030f1503050c010e2209020d0501 63
    0x1407091900c400a0003961800c148058154110b40d080c1800741d807101300324001c00d00c2c002003101e07101d1021900c50b8441000c3c8110004c0f50381c022503298016081d01c036584180c10f4481c01030027800d4001c000024a43d40c414000a0041013049001e0810150010000300300d03010401c00003450081c000e202a104154402e10600410401c40a01010b518054501814441d511005203459000d44408404000d40000790030034010308003411220740c606400b846540760300920300700400075080f1041c2100c070108201c5010610030307540001e560000841c242c41c812241d965071801c00c09007021010800a01c1606001640f210703500c61245242c5000c0200e11800b030740d2460070320b01c0c0020702c158130045c024880e00c0101005070340c6c4080348a03405039a605000c581400a080d9110040c18181c1d170942203000014000b104021000c11400c150590076a07a0b140d0345590f1200300001911807042e0740320842d003001d07088080340c3c0050b08010405030005100901800c804c2d00c400b420740c4e200c007104038491445541d0405 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 981596070 1250 981594820 981594869
    0x3050f090d020705130b03071e0b2503020109020306011e050f100c050f2a01080705090f151210060309020120210301051003090b070e0118 61
    0x80d40504524024050000051400703501c3e010540580d40c021420003086204010381d43c0c00c081101e040c00b07801c0701e03001d60b5511520b1100d000b818051b40070446881c24001081040e000586812410001d00f61004108900c1d00a040b4180000d048065540341c480500c05039501f400924001e0100880e01d00022200041901652405401c030a00c104004503604030241c46800025110820f24205071100040030f0030058541458022524414461068025007100c01618010610740ca40081c0350b0b11214204015500340008483d0080001d00511551482d0700d0f007110200d18400c00905000c4c0c13144080b540d038080c0c5034804aa051030560a20081c408414088034004000700070360b240c01c00c600202d9030700080041c42400d00201004000f8400c01302c1d202002d001070645121400207074105499095840f0200350400d1042e14807a98020441d160010702a00400103145e90210500d0125503850b4015242000078040040c1044520801d4488490086801c003024080c856004495480c200c028003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 981597320 1250 981596070 981596101
    0x50106080f1005040510051e01060c06051e0c0f040f03080c0f070b09040b01030f02120f161e02011805030306030105060a0311100201020910080f07030207080a080a060302040c0305 79
    0xb5041520340000c02c0007054001c14020f000c26064000032915072162100c0482036410500135540f001d00702e40001400c00c1d04000011041882041c0c10b200715038501d462a5042510154441c20002e0070000040f80210240001c2c0400640c40355000d083c20f80304c3d140400d450031703580c000711002000001c5100d1034082c104500c4c60460000c000401c00d640c1001d8007110540034600d0070384d000b580c491545030034681c0a40c10500c40c280c0d64401c21912000b48604030001c5240a4850382c2d06c580340ba0010880c1130555107240c40004646443e06003100944c907100c04000c1e507900351083c003155a2010b02580321500d0302c0d49010390f0390059005584a043c903c0400d800c407500508200e1240403404010000207a0604c0c0701c1008240c1102d103442940000e103000da0181c411250202e030f2110070382a00600b11600041420701070031004000da01ca5a668072026400c034485c0e100007620859060040b513640c603200d10b1110f80e010405507000b141c019600e0340440c054034021851000801d86980401c216581c0d01e0110 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 981598570 1250 981597320 981597343
    0x311031e09091b07111311070b010b0c0a08070c030219080d0806130905160b0c012009190806181b010f05070609080307020d021005060a05090a09050106080f 69
    0x40312030030f1903a59012500c03c0d524000c0c030b0114100700381010b5984060541104030707000700f0b0a00c030640344010144000e0b44101d204440c40090100003090b420355460039107814640301030040000c0c05407074072800844c1d00007201c1158000080e00c004401601d6410112841c4040d040e0140c01940c1482c405074105080d00f101a4200705600c0200111a5240f1000c41541c0c000500c002940706040c0c00d0550415041084041c5400500500001c3c6040c1e418001c0c00003052603c002c2000707460460880044800c41d03e0740d03011407501071103544518038091913241c1c03125071502d698142c1c0790b581c2e80e03a0714101036040307d40c607a072484018071180b94240c05004000400c00340400404543d0070410010300854102c000330810020041184000c03c00d4542c4030040250b00100515268581200020342d103070041c0e41c1e40b000500075240b036505201c030507001c1e141c00341c84003c2030700b01da5a061000380040d11b50010518425603899011060102d1400e1098401400b00b0101070305c031811088500520b0052000e12 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 981599820 1250 981598570 981598591
    0x702070e04020604060804060b030d20010b280812041409070917010e0f0d030b09130b04030c08070506010626240a09060303030f05010e040311031e0909 67
    0x1000300581d03c2c0c00071a402d85400b404c1210181c0c80f6800d19030024452981c4168140c03042600700080b141e0800c03511991381c3d1940b030604418181c50700b0541d090f2150281e181e07421103c08042c00200304d607104400c13a90f00c80040c05120003e540c81841074606652015800d21a010001e814807144010800380207600c0c50540d18202c950808190091003d0101d100c0e4a1850b400c0b0b11461400130020b410950052245030704071440c0058040446807a8a004001100402c1c50714000c90305070700380304280030310442002c1d0124066241c16244d60007010740080c4100d007009040801500042c0384040078241c1c0d076000710000c1204d0360402c0e20207004410389440c03984402140310380210700100302e42205907100c00d40d03030902c9102075001100c1401901200e0a40f41c4e01a0340c0764404182004158014401c032406640c0038400010040d5001c81201c60038000c10740c010840e4000180030238042c90000300c035918041e044078908450300307490703038028007954041d030b003200390002010b8040d45041003034160006040304 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 981601070 1250 981599820 981599849
    0x3020f0402071101030e0f100e10061503150f32030a030e030307060207201801210c0b040302030609061510050712030b130902010906030902040209030f0303070207 72
    0x11070700200f8144040c0030f0f604142d140e1540a8941700248100d180194621003140c0700c40315148080c0f00604522440d8021034800d0038100d0109c2086070007200119640c0509030000031034079a00071809480d0090782c60210511001c000a40b201100c10104000d08401c1e1108910142e0030300804c001c400f01400700600007100180248e4103030740c02f00e0b8002080c0d91506024095003440000b09046026407140906614404074000c01400900c1d84510642018120242c99980b1480c00700607000c1505000b0504185401c00140040114607200704520307455116804444111552400240f00d1039811250365104041020011420100405038002a0080107401d144c0b0384440c980b0900b1364030102051091021039050074480d4000d208032420036801806019010210074005000b920030703441c2e918020340c00840100c030032114911440d5015a0b05030748403201030f031829004602409110900307a0b885982082403001c0c5907010004c401032068030340081c40d16403401000180c1050200d170f01401d501600d1303d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 981602320 1250 981601070 981601073
    0x12030e040b1309020d050604030306030b090f06010b0318010e030a260c25050c1203130905070207050303191710230d0f20010903061a0d0c03020f040207 67
    0x3240c820a6800300c00b00028030210140005107408450101c00781c15030148030f00b0300c028180e0580210b0b041c0c90250515201c00d0304ca184550b0b03920900c031080e458036030b00814010300c1102619401582c0000100510700e510401d1808580e0071104070415080c080d03800015110f071966004045500d0440c40e651115000c240003500c2802001c10007003145405140025400b424003040c401c900c41440d00c080004501087c0501d8200d41e10f10260340340600c40c50007a2403031078600d0000401c9481400e014071001100ca450000090301400d00074060b4401d50140300070110b240c1c0c038204007610b403a2032403c020701d00820392007601070103895410000410042e0088104a050300300c12000500311081e402c920714641410320202000c24100d80c401546c0610305100560134415940c91000f04980100b5008020014141005400203c84c030401808601d42c1c20042011600f03aa00440c92031044212162822410034005601ca01f002070040380c032508051801d005600723048980800c0240d054408501d006041e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 981603570 1250 981602320 981602329
    0x50c0703062d0e06011a09010f0915020303160c20040f020a08091b010f050c010f02030c0a02010c39060f020d0f060317070602040f12030e040b 63
    0x103804041d010548502105004044820b400b02449404400304124209000c2d00304000e0140840c0364256842a04000720342107600300c084081d1419000f00407894811a0380040d00c1050201c0d0190781441041a400034403046100825840c21b0240d43c0034540d40e00d010424180704464045c502c0c020403480749440000100030303000d01c003e001da41c50110441c80c0b002c0303400103000e020000c0c000109140049240841a0341116629008170703e90015114546402c4c07080071400b105025a035400034240642d016040d034040d00007085070808032000420101c045d4030f140400c0c1e038401d03212985e80f00b00001d819221036074284030b0b00f82c629480c2d2418184a204084048030095240900700141c0e041035105808401c0c601110304110990103913003400141030b1540307500000d400000b0000a46070400d039078210401c003503105035800c1c3c980c40710301520251581c00c18100950030010040303130002c0e420000401c6003000c210307004000b0000c105140d412420303180740042030f00d055081c41c035002c3c41c1081c0a00199656 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 981604820 1250 981603570 981603583
    0x70303150302031f020c030a0f0305060906060f0a030209120c1315170a0506070509040f0e1209190f060f1107090c020a06020310030b0f070503040609060e031c0c050c 73
    0x3550f40103085013862103003601c1c00034030800c01880d601c3d220010b100034410350081c604900351507540d10100455038496003800521201100c0440e48500204000f030b0580755510082e041d44062031600604007604030f404240780008190882c601c941c000501c6107414900000030079070b41c511244081c06040324000d501c4211010381d01606114060140c10781484c40402c01440828030307042004c54526081006000d0400d40c01201c40c0e502980c00c1c018810b01c9643c3c540212541001600f00412040507410744030304507a040039440c81c3c0d200703800202e410710f07500c00303011240082d280c21103000c000035262190240940c445000c011060201c00905500d0300340001c2100801c0b0b424031040070454038882c15040341803041c0520010015440801800b0310100d44001450989214101203000c0362101d101c0c01496000c101c85140016400308000b4002910b0340d0030507402d1074816000490310054040d03906040d500017407041c549445100c08c00c1d001940241c011030300706681d036007441440d11181c0b80c3d0181e100d05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 981606070 1250 981604820 981604843
    0x70614071e03090807020301051f0603090b06150c0a03030507030b0a381b0f0102040e0a02070503190f090e0907050108150402190807020706050417070b03070507030315030203 77
    0x683d26520b070030130f000c0340c0d204454102d5402070003084140b80403400345031031440340c2c100d04060565a07100032070420b000744640f2280e40e402c16200c0302c1e6540c941040081418102004001481047c00880c90000d41080340684562094401107058600350400030216402c945032079101d16410002000b8072072803501c50440c2c0515100035201d0030082104c03c0c8c0b4110100d104243c1c16580002070400e11405a1802460480d42040507256160722403030116080c1e000d140280d50b0128442c0d000304d950030010b54002d2090b6840b07071094a0500d8030300303483c04c1d11000164850301e01040d0804440c0c4900e40d444132041000d0302445101c16207a0400080b0156100014080c80b0305201020300400d01ca0486614941c203205001071080d9601c02030030a110030f500ca0480940c002042d450004101054008107609050310b001b81d0700c00d420300f0715004680c555040048040302c014001c1c0c0c040424080c813084021440740c2030396222696910b0640c94010100c1d03400d801e280c2e000100c2c40e8010300050b1340209500c50190b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 981607320 1250 981606070 981606077
    0x41b1509270212010e0a110a055a0316030f0903170f01140d0c0302030109081911030712170a0518120a0c03180e04060b030a030c120311070614071e 65
    0x1030002003800c1c00d040526404100c220016650a403009885200180001c5843d4189030001d130300d0300301c0d808000c014480ac52040c004400340000340840100c0c04031a003e030a007514000c107038540036030401000c840450700150001003071a0103090303045030700c60440d940000032148195200c0d80f400441040d0343d0f08a0b09000d205000100d0b03a20240815140008060358008008010100003464071301499480403612003c19401003483c6100a80190140e4203410001c0b40507501d401120382d562002c000e42c080c2c0c05800c0c0a5020040055020940c0400744a0654403100003482d0030201042e20340d0024040008046610080c100f10f8002c802501b50340090b82181022441001d0302d240030707200203c0c140040020320207095000542c0784502210240680c5c042c59080100c080e0700f005254031050803600c0900411890700000c8000340e80c40008900c1c4102900d00003802d4a201c2c07500c1c200c10361112a007940d103241c5410040c0011090410b60301e8000e0480d00b052400c00c0010354402c031180400700c00e50301c01e1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 981608570 1250 981607320 981607327
    0xb030c031c0e0a0b0d0506120a0b04020d06020d1d0a0c0506030c090d050c0103050f330a2c040c2c041b1509270212010e0a110a05 57
    0x70140542009004140000c000c903421644070080700c00c05822500d0010009420000440c10a00304400e000040a00080161020b13601e1610303100002100a8403c80c0c000556040c084d0204a140c800361000488045020600c03d000380c42603580c600c040781c4848910740114224200080102141c04211041907130301903126034983c07081109034002c0c10001908050040b041104204000c0cc01c1011440300f600c0c1000b0945038001e604080d80c0040720388502107403451444441700f20383c03440178840d1004e400e102d203049040c90740041078900c08284d0003074025040e8000107024005c21910f8812800000556050542c07500e03894a54401d0700710300c6003481840380e0b0001030b81c59041d4004c4040101003040140915030600b0b1404580740030381069081c54404809902080b040712014491000c22050f030b5031030415506280084030002c0c54020340030220121410561a07078840350000c0c1c070484507010386802156240c81e101e924405401820100c081e443d14150062142d04141036070b01c034400070b181154a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 981609820 1250 981608570 981608623
    0x702010e0c090a02070507080d030509060105010c060902030f0d090608010806091e01020f030c120f01080c01030b030f121c0213150302070c0f061704050309040c1707030b040b030c03 80
    0x30305c1101d0000e0424042c100c03020601c014002020400d01a161b5010041d03a682d0004490300c400c8207009a600145040e800c400225240360405082c0d940020f0a031340080c0d010140e2246452030300b40c00707500072460080d010003c0941040d011401080c290019101c81d142103652184ca03240038100100360f29256048012030700340250305650307804018104003a034900344400030040326001000b520002002100004824800290101d4101c41550009151021040f030054000e008007481280c1c240c82162007800e07089004000304110050451202651031040c040c07030140c20f0700c1287c80b0007425030040103007582000c860003800b41203582002c0703440c4940c0020031003280030b84a031190103008025941004074008003051400000c0f0f4002d5201d2240e440d0880180b0b0860450882d0060082d800a20240155040941100823020107514080300641e0018020940c4080d003503d0b40c50020b0791b10303032184843e410148200d603440c284c01c5004014011040c8006030391410250307203c55101648581d40807 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 981611070 1250 981609820 981609841
    0xd0b0408131716050117040611070203100504060506090f010e1009020a030c1805010504150201061703120601051c0b0604050409081330230a0203060702010e0c09 71
    0x40030748509611200c2c0214034000850341d82c2815068051120304030030000400d50f019001ca916500140c9401c107000d907403243c03078500050060005000380030104011030001a9800e021040245582c94000100c42c20227060540803160000c0c1413900480c0080244400c44c8844040c41d4119003800d0310000d050713581c070031003501080d05690202c411103001285501d451034064002c2441544259a00e070f00284040107000010005031182c0ea01040c4100002c1c040d2a010254644d500007240c0000308407140d071561074056461642071490042e030004105204411040c0c02c400740c0182c000d10f041d9080c1044c10504c482003522281c2c0d903003007035540c40300007130341940b1240c00351001440028410400c1c03e40034285840f403a4421507804035810840d020209244101100400d1483c1d0b000e001c800f6803031820410890346501c401d0050f501181c290542010001080c8090b64460510401130600303035505106141c03601802400c0721040d6410f020f803142040200251300003d00c0d01c00c54070f10b00c02d51030b81500075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 981612320 1250 981611070 981611107
    0x1005060427031b03050702040c050307050703050d14071d0102060124032a02060603071a031009060311180702250e040305030106020d050909130624140d0b0408 70
    0x101440014106800d0034560031802801b1268000d030f50600440020241c122002c2c130040380e100c4003044050201401180c4600040c2084040c258400100c40d01e00340c4211070858000c44030030b030004420070042c81c4000700342c04190244000a0006081c0340d410a100034508801100424568501d400c400c0120b079442174000074000605800e1100807605101002e1312405442d101550240c400d00012540a040014103d0225007541e40486842c10600790000d601c0c0d480a05241240c01d40c2c6040841d9440c1c4030f110321380046d4421040b1507402c0090000303000103080f103a484101b01405107070030010410780200325904000194166113041e110460103c28102c01c0303070703081550200390300020002010b4000340198107030b419503022503a541c03010400403506403050112003500700001001280d1040080c00404610718403400021600c0c0c2d07409940c0000540300c04250303c030311a07070030b0008000800211311841c0e4000c0060303e01d0020702400c3d03160240e8030032000c3d0008001090004401c8890074000d0185c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 981613570 1250 981612320 981612347
    0x504050a180b042c0f03070212030c0f030403140c09041220060a050108070b04030b15030d0c06050c090904080d0b060a021b01081e1017100506042703 66
    0x3000f662809024507244ca500406003890498981c4d84030030350b002c000003200340090b00c0340300095280c41401e909120401d8501420300407644018882d6094041007070040352003d01c2880300031900e8030303e1070400845034440ca14009449170411755090790b0903100c40b02c40f00d921036040181c4034418444081d084403100303000502c0d54031401c8640686104194042400d0340280d01c011014005640c89030386a50f126500e6106101c5202010401040000d82803110140c0c49000131002507912522140400d05009000c2a401c000910118000d810001c00d4840d003031304031003441c4640f07040054078008680c1c140300c05030000c0d04000000c2024402c0210941005004040191045e030b01c8041410029507145844070f481150000300803404e0500d9486400c035076100d100f0400c040b0b071007a862081c41e01c09865024140d80004d0940301c0b00071481c00100303241c0000c280220f0006201c1000341c18400300c1151800340030301e4411401c1c15034064501300c0403c680007000c00c1c5649140542e98051600396207030804541c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 981614820 1250 981613570 981613579
    0x5151309080405100e09010906080607030510031e030914010c020402180604031401060e07090501031d010c02070501032022030b04081213031b03121d07060504050a180b 74
    0x141da01e0701794019480107802c0c1d8142c5501ca03807a600c51000304151200c600440019030720074000101418800d421554000c4103180d4222030550300d81d01c0d041c20a81030b013000e0b040b4013003081e003000e400c01d94081064001803d0418540c5070010082000804032640d0040180c4140e8000c1481c03494190310381ca02c650000380051003a03617115a03a1410494154500e000e05801e5482c00c0d40c0052403002c40c4409520074000c954ada4040380d0304100055008007401e06014140301c80325021030145900c24410540c140285070000e2502d5490803000501340c80b0320b400b1002644808440c42036100107008180d4180019540244d0f049925600c074100403000c2035807000e025180d0fa182030000f44918070b0020b001d04424021180030b82d564182820130000104c81004000035400d917000294041614102c084062091034440000050742c0300100588001c0d191080354a150107543c075180c050f0803c0702d10000e0040b400d00d281401c0c6044001840d9142601c01d42910075000d2400c00344402c021f40c031900e5200f60090 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 981616070 1250 981614820 981614839
    0x2001140108010902120c13020f1210150216140111100507031406030c060309120d0506180705030606031024080615030a0b0f030a03050d05151309080405 67
    0x181e0301a2484030001d074058100b00345640041da4020401300100040549141d41c4480c0141901c0c0082d4060740d1028a4081e00380801c00b01d1103c0c84400a0141c28004607608541d0b04000c03107c0c2104651900c88800d650012000002d4400300451440443e16010700d440d0044094a0061301e1070422001c41c00c200e800340c403000c00543c2920b9800940144d4031903030204080c0c13034000c03a00015400f055800d00d41c103a02080c0038078868a030810085038020f03525002e4894161444c1e00c1001c040d04511004010940c1300c0b0200543c508000b1080c002c81a08030304150018200000041c10310701c005061540030700b900000003100b2001c0d05200900400b045d5900c450001d45100d446200d042061a04200062114001c00c1040c81c00c1340c102a07400700d0800c0c088d03180d034848046060007070043c1a442c903084488800c114049907020303c50b50300258040d40756540c0d03810040d503400040307c100614005036032910908540c40c81e200c90194a0404035100030025003850746040c0300c41d003802140d00807580321066a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 981617320 1250 981616070 981616079
    0xd0b03070305010606030b4e070e090307080703030e0c0909010f050a0e0c0f04150b07060b10080f040501090b0c07020a0e010b03060603100305030a11100501050120011401 75
    0x544c0200211080d6031b4080040c04240020421500b03085e80310f040002c000d541034001042c0030f160711010042c44070b1524502e120b81451461454450313031f61428134140c00048003000130000045585238880c443c03402552514440d5a100d103064083d2803405800c05a4500001c0001a4200b04111500700000c088009620341050064044c120342d00c88944410300380008a248051503020b890002020b41d00506414204a014000351301c0452014030382c82a1031302c002c01c90b140b400d44140000341c0308800d0002c0d42d5810b01e05081d01995250722096004944220075591101c2d400f802c2daa1300240d00e071030710301001e0f00d90782031a80c05000b0341c94014011030004810701111810702001001403074400d6500d400107541d82c10080c40c103003109200b0441c840c0700800006600307251031170045074091540210030107815141d07225645150427000c065408654155400341348203401b000703030800b601201c4a00f884290306040008014a070003024203d810b0b0740c90301c04a06100c200390070112006050b900e21000d45c1da501c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 981618570 1250 981617320 981617323
    0x40c03051e01140601121a060403050c03240f0604022206021908040902090a0e010b13090207030f0e0a080a0b0a200a050a2609070602010e120d0b03070305 68
    0x81c01a00c010325840c01050460400708461800c0c415a0161521002d02d10381d40142c0d005170269600c091452802250540f000d596000060405180107400820f00402080185071030000502c1c020b050301c003004d082c00c0000c1d4420710078150f4407601c0d043c04042191100004100640600d000b1b42041000b0250280c1031400006c0503030f0102c44442d800c403004001c000f0004807801003914000b0b8a0310340204024003858035150001c15009a003d42034002150762902035600c083c1e402e8209440d05d0000240052014070940038a90141c04c81a8086182c020150b42c0640f85154100d0007400740494540902c03482e076940f400200c001e040f0141525003a030101d01c5d0400d0081801c851210343c01d0310380200c3c448001c03012050342604c070b0018404180751030030016043d41c680d0071440003d004c11000989441600c400d41e940c80c200001c044e010688982008402642031460640002086a140c02c0780f103028413000069001e058180d001800c0d503a5595024014050185603015680504c640c10000003007000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 981619820 1250 981618570 981618613
    0x120f090501150605090a031103070f03060c032324031605151e0c01110a0e01020c01180509090c030a121d10030c030e012c01140c03040c0305 62
    0x60007010b8608141d21000150b400d4007603450303003e420144e0000d041c00040d0b62083c66103d00d0300018120b9034003941e603140c001c00c11496074108442242e1104000740403903401d8014122485252442c4100b07040e0340c5442540f803054000c0c00869003441d03103101e42e16200e50300c5c00303502c5ea2aa40075003600d0074440c3d9a5042100100c0710720031a406020241490420752800500340c03144010601e0f0700e011501c07030000044026070400c461201e002e550303401f03010400340e040a00034080303a600c54a071907007401c81742c500290400e800013011a06015400035410207004413084940265181112440041d8449808503807400d50110051900341c840c0204810034010640303000c9005807100e580d001d00d40c000c40c0c1c20301c1e0341c60b071984180c1d2500304400116200c801c600907008000490182c3c80c00003203030030120f1841401d481501c401c1e0007206442c04654203100000c1a419001c0b0740001d0300a2104018800b191080700100920400c1c400e000400801d0810200744100d00045030084210b0b2131011782066000180c91 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 981621070 1250 981619820 981619841
    0x121b04120b01091404080711030303040b0103050c010206160c08190c0c1403030703050903010f1104061418150705060c031005121b0a0b3108070501120f090501 70
    0x59010700000c2c0030300c0d6500545060202507000c44089407660703620001941c2102c941141c461640c280b100c61151400c0024512403030150091049a502d1401d06900b40404099490f0440d0000410007418161004d03402d01055128135062041e103040b411b2003502d9015408c148003082c0309021004504d9644080c056040a00901c1038201d4250b440214080c0200c0d080e49880d05a002800000b011a001d0000f40c0080b4001030004102d00c2400700003034040714100e103e030f070800782d01c0414240001684104480552900030b88428985000310320540e00070031540341900d2090560f18002d03240312030020240e504ad5584a000ca403214182500b0891450708200c56089001c0a01130b00043c840c80c10a00394649090141d024028006204154038020340e040b9000a4000e5014080080c449010b0360003051100d6070403c0d58a0b030400101040d00500081070303010040212151018050b007200442c0d4401250003d0a000503071000e00307586071005c0d0050301c80001a5501c1e1600e00f03814020103410a0480a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 981622320 1250 981621070 981621083
    0x30c07260a0308150d05150403030e03040f03021201020f0d020a030b0a2304021c14100f0b130b0d09021810090b12030309030a03060e040206121b0412 66
    0x41991840c1a998000381c0710701600248245000c84c448101d031460300c00b400d807000381030500f18466580310140391501914200000c1c0704c0c60390070002803641c5486402404951072000c0d52929150513031081c024900c0c1e0002a126450324500e54490103025030440e03031500925400d2a80340ca400300314120080d00f1041c1106c0100b801e00410b0307500c41c130341780c5065000d5450921040358009510010b0103541c103181c851464006a00b08100201c1c0b8840d41d9860790b240d04044004660003449281c00050340c00c0107480801c40c0100340744244010000081c1e807000f62021000216124078884a0079158480c0a9101051440001860700c0702c50382143c1050b0900c0b4001d6601070101c126142002541410403900107a800340c3c142ea040c42000040e811140040100504000900b06007000743d906550050740d240003164030009110b01c20b590107000d19002401c0445e245581803074a0380200d8820f200d403160800c0c4485281d00010201074440000ba1a2100000201034985da120b0080511443c2000d00a6404 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 981623570 1250 981622320 981622379
    0x1c051005010e01090207141006050406050609060f030c16030804230c1002070807090b0a0905060d2306010e180a1214070f1505061c0311030c07 63
    0x560519000c0c080c121141e41070081e07141e0f840d0410b66002504003003011980300b6110030048000b01c10030402850b0417210b04030b0014490b490901000101c2d01580c0c0094000c82007070206604998030081a5039102115480d41a03890391b61011414042c4540407120b00c100070702064101c10305500c00300113885248104040034096489000030804a4451501d81c2d507550b00544a041c101e0401c448003483d02d44290045421450703d0b401c0950900840740c100d543d4080d62800f0410007464440d05030001072413400c20411550400c3c0000c6012155020720250540c4041c260040c0e10910b0100164029800c8500740d801550711050044444101034130850501c05e10848170804810001c0780c134440d01d6a01a0500c1d1603110014010f607000c032200e218800400c02c0c2030040c040403d8101001052007071182e1600c1c2c50321501c00721110100c40e030283c0850301812a800b401440c55040d44c2c0000c1400c1d070142020045101041407151444c0300e0801204e6040c02050310000c0c101c0c1081013483c000c0840002c2207281d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 981624820 1250 981623570 981623593
    0xa05120406060911070507060f02011d06160c151e0e0a02030c030f1906020c0a030c0501150b07150b060706050f06030a030207090b030109140f061f140607021c05 71
    0x4c0c0c0208140600f07290040a01003105074002c032081e5001522500001c03e440c0c4000340110300011000300168115004541008400e207000d001c09001e0a150703003002c0014116a84460f00341900001c10b40391a255141240e26100050304c01c401d03074602060b80248101c1900503901034940d00807801c200d02900c01d0703d01c4e038410f92501040748170340c4268140081c50305440107c1c90407500400244240d400c0c0e9402c2044c00603a040603c11010070078040d40711100100c90600d422401c43d401c0600c00141e01c071014030103104410021003210300480d00a04100180340c40d1643c60380043c80c0f408082a8801c2e07000031541c00700002034004a10a07204c403041a401541c41034103064642841440080c01a04500e4003400081c00341d5210580e2160702800015100d4034550303901d28520414103481200d40c2c022b400d4a240300c48100040355000b4490443c0144400050100309010030240c01f4240d50502969801540b81e2a00c1099130412900100360b010301c0c0304c4501002c902000700d60700c06c0c0c0da40d0250b01302200 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 981626070 1250 981624820 981624851
    0x211106070c02010c06060f0b040806010b040e01150e0301060909020909010c050304030c110d0807050c040908090f1302040b0a020724030504050c0901030302010b0a1a030103080a051204060609 84
    0x14894441522440400c1c0050342c011200f400c0701610403a0070540e40c03640400e140780742078042d1024200c0058070b6556641004170141c0b41410580c0300e12440340c010801800040000d90606045482105180541400d10030b402d0f9448010130b5007441d0150300c3c0000001d2130840039042208414000c5d80d0020356a1201c0031240e0a80e1800c1c030859000c0391003000414002846a00303141c0c0d2450107502103c2000c5280d10001d101c002c182102030f00c0f95000420054184034043c090001b508100701c83c20861401c0c280d854200602500741c2103072060104000c07001558807012800785a800f0240001c550b2961a05400346560b001065510014401e00201040c0c502c841c03440c2001c40810803000030800141c10b40e04030050000207008451034080d0110240390f640322021903501030341c030030340011800325031050a2000700086a03010f0540440e40e440805604000081102e0540f81c02c02a100d035908074010064485100305014503101c0b038a99020001886550303440a0180c5000400174010a00301d1120070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 981627320 1250 981626070 981626083
    0x2a0b0c03100906050a06140706020304030507120c05070302100504120c090b061e0d090506191113090b01091e030b010b0f0922060e0f06030607080708070c2111 70
    0x100e400c01744101c0e0502413a4000c410307400ca0060000c4030b55260050b00c0da02c0c00240e80043e40c00f00c0100f180495020200500c050b2007516a62892031702c0880b841194031a96945c0c41c0074131019010b000d52100d00761080e071265003104c015045511440300d52080314502420030220741c3c070030030504c1480c04024085501c1d04200700e4400d400c1e80c00101d207501440d4090885103520410311035803800da86054840019105111aa1140c44204243d07200030001c2c0f51200280c83d00404c4a0b0000301042200411000c015a030210580c0c4c24200001a080c0c10400103030340ca084650007070140c6007a02d1482c00344981c030300071030007095030b01c950361010850b41d955600c0ea0142c010100d05180641003070002009601303125200d201c03036040c01032003c0680d00065058038200c030842d402600a0800c0380c410440c4843c031103040039800c150180c0041000b0310385200001d0111b80058500020007903604085880c50744640888000740790030007122020704201003040c60036000402416400b1030010a4030350b0701501c001c03840 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 981628570 1250 981627320 981627329
    0x50409150501021e07031709040f0c02030708130b03280204050a0302060306010903140109050f031801081b0a080a15050303090120060405060103140105072a0b0c03100906 75
    0x4200601c25019910907001c2d82e6103003804944a260340020200e10301c00800250542d2090040d42e40e22300180c1071105a0b0b00c02d024003da000d05104042090a900000719040103810042140d00c0b039121280e45005c90300c25034005450780802000703008029024400d03201d05500140700a00c0b000100f205608241e001c0c074401d95510041a000400150501d9002540c1c4124149000101107440c3e0769507540308800090b99014a81d910808081004002c210b0b560707801654a00842c1021400007100781c5125800c12040d0400079984d011039034554030300b1740d42c0c0341c480c8001c0d000a4030380b212250000e0800d0b208540d00002c840c18140140308842d16105107505440c0d003c1d015501d8840380100550354020780c8201c0f44184404801d410012440900899028a2160380a040294503600300000707116a0107020004607450002404107da420110404018074a4004520880ca00c0e40c541513440c40311410240102040604120001ca444002544111404801c080006403a0070700f04044840c1d5005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 981629820 1250 981628570 981628573
    0x801050114100e01021522030201021c050c190c05240c070b0f060d0c0807141c0201031a040c020a03080c070309051c050f0105240303031506040f0605040915050102 72
    0x48000c03207061a06c5140c0c0c810f400c12139140c00c1011210a0400745100b83d0b10540050754007141022100d00c01d102446100c40040c4414000b50420f0081d03207959114541117030520340340c0c017000c180c3c000d80902c3d10341c55144d4101050b190340c1c85600344221300035000b00014200f15540c490001c6c0114a00d1380036a4086e642140040d11150b4800c20100f2240602404003a8440701804010000460b90a80c000c007410f40140600812490000006a46036541d0091480313040d01c403900064010000701c07001200d5409103804903410070801041034003480c00700d024076001810140420390058002420782c014511a07500c0310190703661f01c010180c1c140600d002c0180002d007608d201700300511307200c4541d0010721035100c1945100e800710341d541d0717103017201c00010b804c802d945480410030320306032410111008103a40781041d10706051400029403039100007000e1200800c0410055046d584810050f500640044160740c16101e450b00c1019103940c20600c110b200c4c09050401804080180180b031508480303042c2c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 981631070 1250 981629820 981629833
    0xf0c0b040b160302011506230301080a03030b01211b03051603091502031611011104090213081b040506040c0e221d15060102030f0708040801050114100e0102 69
    0x300d020082c900d403044260219900d48600c54844003d41c0b840b04003c012075180d0300e0401000b801041080c0203017400005a6a00620040203d400040b4152040e00e91502e00020411001c04c01070b40c07413811850089100700b4071110003031050221035000e6403200303040500714100c00c0c0110b102201512000c95031402c500c2d5812005a091500a80040342c85a01c1002602c14814000550300d00700e070002c0b00d500386000c0350102e0300d11307100b9041100155103034403000082c0000082e80e032001c000d5225500c604040f065001410b65404044400c18402900644050f9160341d4504401c91094896440e4103030b100c0c516120210301c05180a201e054266072054030380f401c0d0b103030b1f6900c20000c44070310f4480502c0030401448407641c0482000c1c46049003400a280c3e4201000b003041c01a980340004140000380d10116200a01595a0700001503894543c4e0740d4042542d10485071401090030700540e4031000c081e60a02001089540c101003001d20b901406841c048541c0386514402c44d01105108a00d46c09a046074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 981632320 1250 981631070 981631087
    0x51305040816020303040504020c061b0f071e0510050628050609010c05060a1d0609060a0b0411040b03070e09070509130902100c05012009060a031104030f0c0b040b 72
    0x11250305000a00040030303a070030700747d0310340104c0d050740d01c00d00903444981c01007010000b645d000d0742c2080c043c001900c1003603420891400002001c0307214860340580100c0d192084001800304040b100c280030780d802001d54288078088541c031030292405852180c45010041c682100e000301d612803c01f43c0000740c240e2880514503101c144402e80e0300212286040000e0029000082002000254081c41c1c03603030b40000d49644000700b1440c140d08842640d420b6a003000e010701c10070750b400041841d04480110340001c1c3e105403c5001500500d040705480c9000040405d0005040f003180c0003441c49001035445100c58002008200402070b402100c4590200d14280160f40303446c03c11903a05c080106143c800040c0c0088190001100d0700e40600403580054203481c0203104105080c09904040c08640d00700c50760004100340c60f1115030003590829400398001041c4805841d1090708075801e524000d0000315902e40c0c4078100898016821030043d12201a40c40001a0701d0b0244030449049561705403001d41000c128 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 981633570 1250 981632320 981632347
    0x1e22021f080c210603030906070b06030d0f020c010806131104090b06070804091a130506040c11070e100e09030c120405101803021324050d0b0702071a040513050408 72
    0x94843d5400d4441488608800c1c8c4801c8018500c050250b039504840f494500304141c07401041810840400c213490303684034812500050207000302e100908100350965203100c00700e00000844021010f01038205604082082c984078001e205072200321030180034890a45003480054480d0140040070b4040130001001500119804004041c1c0c2030803030400840e80e1000040e100348505403415200c1c0c2c0c1d40e01d0910005203450300c2511100c0c400d9080c01c100c0004d42140c1c29484000c2c83c851654917000e00320018070079550b1031410901800454100ca107660910001c1d040c1d032a084004180000d10a40982c07402e404043c10a1b2030171034600402c0c3d1910790700007500c101c540c59800e541030300a06181c10400301c01a80c4406484241c2c0f282c000380040c2030941d80a409905046414000c950291102824095074031004070038007405800003058001d07a15500000c80c40c00e0b685500035481810311801078040c01c01884000d20848030b088032030035800f49180794154115503055800130840c035030400045501402 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 981634820 1250 981633570 981633637
    0xd0201140c0a0804180f0504210e0a06090305160f090f0f0c0302030a0b0f0306132d02010807031517031615051e22021f080c 55
    0x111400b81c801041055403848407a41094002c0d10b840c170908110606043c125218a40d08011180d005101c603003840d841c2c50501c059505444900584d404181e00d1520707024124035040c5030005002160110b565100080c0918034a0200b10703168010001c403030001c7e03880c5090b0f01040c0c49a0000d4019010301c1c1c00741100c02001400c207203151ba580c030b13071007980e56202071071080b40d560204584001d6038030f18080c1e048804442e11480c4d007a109511801410700340c0d4400203031040d4440c4201241c0004d0300d070541041a003404101c030200b481304801c0d40301102d00d50901d000c2210300600c00c1e201c21820752560841501592040e26500703080c4a4000d400304031208203009903521b4a180c18003034901c3c014500101c01001036061760180c5010769440c2c041c144000040c40b0b00383d4040c2048840c400e0304401c1040a480050002d01298204000b0191080941041c1e094078240316a004109100c00045000c0240ea880c0a44200c180417540c00c6002a11008050040f82c0344081d842902841c2d8600300c100a810049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 981636070 1250 981634820 981634837
    0x6030b010c141507020106060503270a050f240609190204062606010f0e1f02010c020607080105060f032a04030c0603140c0703030e01020a18050d020114 67
    0x582039078002c01c5400105091000d106000380120908581c2520020b040107044041103a02d0410200000c6034440d0035a40c0012400c0030905c055460803280045410110040d404180100e80c0078400b089400100107000c2e22107038003540c01301e01e001102c0300802104c8683c180c0d060842c080000d0310900d005204c05030300258080032034003103121148041040ba0021f81101022451590194101103042800343c142000c0100010109180010009018000407840344052001c0c031002c04205030b55000c2c50781708000310301c400120030300c03096034009001c0d00034004030501601802020841d42c500c1036400a060356006851107190645131000c04103254001462210804407042c40075945d11080300c1c0130107503520788080d0f4a440300c0c11402e1254424000c0c0d40280c05240c0391849204801c8804000316a000500070740e2180c80342c440381001c0e40500304280664866510002d4150b220355001854100104014204003140c01d8494040c822040d900160180c080741c41c0d1000e09400001c541e00a080e503d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 981637320 1250 981636070 981636077
    0x9020a051c080d0b01140c0712080d02030406020d0e06070819150b1c020301050d030c02010e040f0e0106050d0f080c1c020123131e021c052506030b01 66
    0x1e204075122001c03603030452003410120548440c4840d0266a100c070780c1c004400e1002410600d800007510740c0780e80c2e980a912540203460710101c0e032034040c409074206440304181036032410b5642c0d00c1c0c9850304000950019400481e80f074903000c0410942403000840d02e2245800d03885d03002c210744660804480148045086011954980c0b0020341d00b100300c4402e282c0203241422519484078000181503040740e405090f50100c0e984103000401c090740c1c81c0f5900242e800e03010700f4550841195800100c5003021100401c03504a400c0100350f030b00e07005080e0b100150300c1030410000c22540f9122000c006030300c030038004064070f14010303480304c075012400403401480300188070390840d125011030015900c14208200748030780c0941d545100705812070110030301102031210580c4c821a41e51030443c2d40c1c5460754900d040c01a103142c180c50314400c10301140c1d03840300c0c05c1c0e240c0091103031031340d040380a40c91100c1e82010002102e2038000c0142e9201c19404001c1c414036030510100b000c6a896040100440c02440d16220182c1003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 981638570 1250 981637320 981637369
    0x8031306031d1f1b0804110a0b1204020f0105070f020f0d0209010b1207091d0a0e0109080c0708072d090c03090506011e0902131d040507050409020a05 66
    0xc0c003000300144241415402900c00c0305000d580c3c0750004550144041400042c074400414002c10740c0000c0c0242d0250703014141d600309505800100e0b02c0c414164009a030142c60004101007000000c3c0e00b11440707640300b120070083c01c004d0040111554018484001c00d140700c484903039401454503440c44088484084c1c16940343ca9510f0b0000350340e40c0f90a900203400803000042c0800751440489100c1e40c030005074289071044c14508061100481080c0003410b1004000501007402000316400c101c60b1501403400900c1429441d042418295215004e5582c1c0b81c80381010000c1e00318404254541102e40f1401c0c0311884980e04949401e035980d031503460710643d144030100410590182d00c24040c80007251741e80001d80c406146011840c0c000181c2204110a000c000d2009e084412006000140c07070503604050303100d07210030056040108c0150407080c0c14102541d800e000c06410b0751843e80c401c9000b10110f800d01d0342d0701c4040c4011a84403070310103900014403c000b4420380c00c100482c0c145241e903015003000c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 981639820 1250 981638570 981638621
    0xb060102073c0308030a150e060f030a0b0106051b0d090b070501140a05010e1503030919151707030903020715121b02010b0f03100c0908010c050406090803130603 71
    0x36080b0254204884a04002c000e1040003c49446a4011090718131041c0e8001410720300d2943c1051801440c0038407804d0ba03034850541d44d4505210220865500c00304143e0305584489020b030181c0c2006d03040d81e07190390b80d4032040d071103c0c14001200241010a42c079111842420a000031200e44c0c0440019100ca640b588180034105020520103031051000c0440000c84e5410404400c50460024042c0d0000020780090325201c0e079404401c403011a42e04460030700c62185403000c4c2204040042d8404c41c6098803a072003074401e480d006240e00d0032a5254081d000400c2d51480e60135400ca40078844060016400120705203d200301e102440e03540800c0130304000d0340d920501174210781598034504a80c4051420807514990711764090288845818044459100090104011990f1941004255078040d5120a80002c8140c002e006913405800000c00074041082244400740c01079000d48a03800c0001c0700802d0008031040c002c03007921905252400381d402000d01d0407030101d0243c10340e50f09815880d802c0d1150041c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 981641070 1250 981639820 981639929
    0x10e27090a080d1d0f0705190b0f19020a0c090903110123011202011b0609080304030f14040e0721022b0207150c0203070b0406090b06010207 62
    0x5011100042e0210314902d0001610b169113200800d50946948086151450064003007420820340d041520b010442c84110031036101300c2e91255000590b103210004610702001007401c01054640e0710101e005540e10070b10003080b40d68518411014000100078081401480029041801c00c0c034020b14040c544188e521403da42144c03101d06228402c043c1942003600c02c00a11005c1030300401c00c29610088070012a0000307007015501c040c5045022545d41f00044c10042c0f50740c803070902e054106084c0c40e00c0346031034a00a820364941800040c0070070145861525101c0d500b40c22034050366244d21449202d61540002590942942035440900c0320320042c0c1c2c1640c1d2940b610152455404c0b090700259110100d035110340301040c1511040f800c03e40108492000325140d0788458003a107000d408000b51004071000204d003940a01130009000c4849401404180411a006403404500a065110054032040016a65a07000d8032506020103420980812200901d1071242660342a000e484092625000b0851 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 981642320 1250 981641070 981641077
    0x7091a040504240e0921120403200105060d0209070e060c01060315020a0f05130513232e0306020c0304180608060103021c02040c0e010e27090a08 64
    0x600900f14220010018181c8008500004000d40810a86942404030f1066182c88118840c80e40c849240e1030462410356130740d422070707030f10a204001d2140740f802d0504e40142011100e440c1802e9901034060b07048034100c8103100300c0d80154401003c80380328a88035800d000149100130108003d00805050322405038603440010b2410403024400040c0f010704610b049070307100d0003030030f0003101280c03040c0040d808154102d880c000920100c0c0c14420f0f2100d16120000083c1a22900115008881d40741c09000050507500420342c0b00c1038030445640881d0510340f035100d0f0075000319240e401040e26031071054030b180009184041c00114031840303040550740304c2e00c440042e80c0c0a6416200554000142044800c485641c00300c031000030100e05000c800c1c503000300d00e0b50b51a0107010181c42080070700c11500508000310b4401c4601640a401840b581c21034000c05450005054138403404a494144407078802e00c0c0402d051a50f22907120b0012009a0080d016608a00b0f4000d01000c400d00c0360020400c003255042001c1c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 981643570 1250 981642320 981642341
    0x1110a110715031119261306020c070b1611010c030c11060706111305030a200f27181504050c0603100609150f0c0201090f1e08030307091a040504 64
    0x161000e141c4120f054041041001b07400c2c0c843d124070403040c04400d00c813203c0349a40c03540c0c02c01d07405078452592a111600700b9089501c003061140002030f204885c007000115403100300d801601c034140901d11a800644401c0d0846034020002000c441d03200e000503207001a0081c14140142090b07042c070740d15a58000071a804400c04c0062020081414484a0311400e40040500016409003c40d4440d84d03070381403900e00e00d10001c05000c0300f14405d01946500c80c90008002200010301c1d080d0b44004080341600080c0620741304000390a8040002600180c10105036802d107078138000200003806140394a90002080608201d400e401400c407180140d075a0390000e14007a80c1401042442c0750701e4984090402c03450b41d8072540c210b08000000050003a0000031081503072001d41407021b014a090310049841c01d20603002202d0694003c0760200d0b600000d14040a40780071030170b8a01003c55180e0f81000d560f03010484071000091a10141031081d02135032502808252010b035851414030340c0f03690003d400c1c0c4a80320003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 981644820 1250 981643570 981643577
    0x30c050919080706050f0a0f0c1e0c0602010b031009060b18010e01081c0c1506060302040503120403210e03071205010f150611030c01110a110715031119 67
    0x6080c001d0b00d605010f03410084c40b160410341e1070441000c0074440e16000d030355109424020180c0c0c803018018002d800e1814016841100100018046403042a00d01001c420607070b082143c1680c0810b5480c0148517541c2c58800040050245840307280d5510040c160010084031620b84402101116407200d405254881e40e254642101644c144114070303215040581c8201240e80c005203450039614071020110841800354949505008a0340c20320407200d42407c036101a645140200004d03555501d94080d03c15150101d081c0d43c00c0700d4078042e00c030180340124000a84504130b04000d010209264a0b24845900c0351401c00c0643e141140d40003c5c2000884d40c46600c00c120301c3d0b031a16041100031700c543e0b41c800828030310410172100f0003458050224907038007841c424080c003000b02c145922000c00c00c0d50100c2541c50003e00c0b0702d0380c101c030f2071002581241c042036012918071000140300c0c0d440429068203803088102000f0000c1e80081044000c1c1c2114003d1400c10340c401c1140b10352903d2503e043c60382da04456203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 981646070 1250 981644820 981644869
    0x150e13021b0a0f020405132015041827150c08040b06040f0f0e010606090b03071d0604090509011509180605060105090d030c03170115030c0509 63
    0x20390081d400e103144908541d65000080414000746000c3d2081d080d841e0152400602681e903d440368039600070b0360102901302e00c1b004c201895801c040911083d480c51040d10f41000f8107400401410450007103004102d01281e04d000490040400390380240c49124600490700f50b0105802c100840904074081d040d0307240030350405840d4401030340d80100441c0780003500c0c5c10160f500d07007900e0355030805d40094420b6120b83e45070f40e10f0341c81d0030a154122a1013812000020003000b10401e10f407034004c2a0034850304020640c9140c00195a01c6c6800907030384118a039032611064a1b50040c0e1103810321030a014001e61000040c0004103802d8460311900384107003106400043c1c403011200003800382d03074034542c4003040346d80c200010060b00302860310720f1010035688500042616101c3e000161000e00540e2111038100c5a03070b03c1c1120905600104030a0368034040d031a007282e054041d07000380000780d03024040c0d0040e600c0701b81746460a040c401d03800f0000e07140103480c08604004144001030004050100e03000940a08007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 981647320 1250 981646070 981646087
    0x50f0907091a030919150e100e03030f060d0803040605060a120b06011805010e0f060421141614241806040501200102090301022b15150e1302 62
    0x2c00032071400901e01700c0c2815140c8201d03030b20352140071113010b0351b0070f42182c451001a000729010843c0301501d124100c002d104030742c10404125034940003115124150500240414040e0410380c1c0306050080d00032581503e140c0c0c030b07526144082c140140ac42070300004079480010341319800c05803030400c291089000812500344a800103100d15103e9205494603482c440d010081681c1026241c00c141c481510b54070b0840340302c3c40c006140343c000d80d030100300c0710703036910540c1174644e040d080401d03c030644500040554065100d165641e40e0503282246821502c1e280010721242031400d0296404120083c1840c2002109401c20009003403035038030440080740b001c80d01b485110044c2011035014107040e90700354242454480020140059115a5030f9486800200300200380d5084d012a810700307002800035503480310300b054640c840c00c02c81011080c11899140030000030341c4c0140100c1c0196005101c0500300c040c140007056420704ca5544012050001070110340d50302da2122090032100018036600182c40c0d0456 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 981648570 1250 981647320 981647323
    0x5010503011424011407030203090901091104030b060f0a0303020616080c04090c05040305010513060f05060a06030e01022109010e06010f3b01050f0406050f0907091a0309 75
    0x4060300b05110748007020400004120748001a4040a0341e205a2001000d450005075058079214043c04800c01000600710185034000000305035600068030300c0c01d29682d031550034404503030701c001035a90134030341c100410404500390796003081e0050001016120350342d842d40c0003e1008403460340128056082203040015030041d01140c619000c80da0300b410340b09450810401c00c52807045000b0400d203580ea0b00c603502e000134030440507078000d154014004c0040d41403a8402c1c3c0803203c01d0101c03c0301c005050080306240c10860b07004290003114050225002c40e414050190068561589041d88565091007001007080d180181100c80e03808140e100b0801f405c080c0340c1d03c2e09495010400c070b03002e6485840100b01c84800c081900c0c04460700c210510315200e540c00100c510343c8581266030211200322030f01920104042201060495404442e03031140303284c0e46c80900060b01c410348a15a40001100210b22160030003141595010030203140549049449643c0000b291014001507a036216012003088080700f0b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 981649820 1250 981648570 981648581
    0xd0b0a060603020f19201b040227120109030504031205030702072c070203190801060e0f0607050106120606080c0901061d0303030c0d0f06030f0f050a0203010f0501050301 75
    0x1031601c2c0652429000005900e901e02c1a00ca417103054a4000010600310b03031281a500e0313031010400b1a22070031007075041c0240d99a0b02d6801c040c0c000d10100e02144084da8a000d10840c0c0152440d00b4602000030050184404c580e4000d0500341e4000c10046083c0c0d02d807207028411060b8043c0300f43c44550320380d0b085080c0b0904444404050405000c1c003007007804819038000612000320740c1603001a4003002d10340314030018170404c0301c02c03c0310140e82d41c44180040290044003a002c214140d40d0310200303800d07800004468a20081c070603440407910200b000d03840c0303080c0003c038043e1442020340f0b40f81c90080190340e05402c60302694416048500401d40300010803072580240d4008203072240c000c0c2060103018001800b000c0c0107200703d10070300180d580161b0240c1346041c01e01a0812000703007900d41f00e10b400b420041032135001d042c0170400a4a00040b4000050703031881100f040d80d8110141c0b503911b8000f565540218035001c001503425101702c421040042c1d400340940700745804044000700e12035240405042c00c0d140d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 981651070 1250 981649820 981649829
    0x41040617010b0301050a05120f010603060c020c0904110f03150106050403140123150a0312180e0a15090f0b121f0b010e0306040804031a010b04030206030606090d0b0a06 74
    0xb0b4081004100e6942c541455605452040340c4a54178402e400d155035203890305000d001c404030350030300c00c0c004180704007503001d941220255026a00c140804208210300c80c1022100100380d4141402414010f0800346011641040c0141c02c40e8481240c0110201803003d099101100103400040c051081100c071059843d00350400c0c90091100941444202c848c1c14000e6030041481c284403070024401117030f0318510b400c680c040078051040c0036403a07041c1340c0c1e00e02010962031000306036661300c81c0d00d21070402c1c2d203450b080f650b201441e19130540340c20f02d0241c0988016034900013111541c8038045901002441001524008d074403000540440c01011302c0a160390b00360140f0016001705290048079002c1c4605031640d61880b00c400540c0100301001a40c00141c1e074008160588524001c100c10002c0c610b0041054900030040800c020844a01211541c1d400340901510000b080c0310400c01810418040d5400c07600050030b131410100d402001c101e22103014441038841d034821405006400045104400291 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 981652320 1250 981651070 981651089
    0x20a182007030e041e05091b03072d06090303030f06080d0e0402040807061106091f1e0c0f032f0714060c03070207064104061701 57
    0x69640114004140601400030341480031051415002c1e07981c0e50705c13500350311442e0304805020303001c410404002084116954000740c81051010354510a44000785041d11100034003d00d00b032801e0100781e020114a003c0040b981000c000d04080c500341000c495030f0040c084c0d6079100890540b031801d00800f50f811820721207080c1d915014080c00a040701103590301c4000100d00380f0154001030640818004d01c030701d51055029004424010507165880410380c024945c20700c040340c10f1520b59080240c2c4039094920034229900b03580c00002c81007000c54128041e10700c945030700144e0722500a410b50041c3d59810b00682c0c0050780b80180c000900d500b61040100c403c1d15010b20240701c00c0010601e242c180c03400309062044500100d6400f0400c04081d01900c0c80003200415198541003c3c00000440d40003502e001e409402140004590144039090350810a640308903018088006010000c1180100310a41e104125008445110b030045550040004080c141c2d105092090800504050b40d181038104401320f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 981653570 1250 981652320 981652361
    0x1b0402030412050a020c12031b031201050d050f0a110909280206090a060302032d07052206110c030102041815031506050a0509070c120c020a18 63
    0x124002980b41000701d80c1c02d052003030b52440c107031109a00d44203030411655400032004124619010012000c0c103100c81c0d4400c001160304110414890300e03030040303081d0809401300190040150b464000380c00d41c02c081c0107009664074540702203c030030301344605d0481c140c40307000840413241307868200440c03119800b42d04040a841c0352440200e503004030072140503111a1448006051100b5581e0300300c2258841a8000d0107907142a87d00c00010b000b03500101d4041096214402854005035224540301990a22075240c447c0d40d0f580e501001d58098002c040c000100c0d4081100480708104c00040310000341120740c0f0b030030b03280344400c60300e640c03400c5003104559004e42d0040c401040307034064620500d8200400c5035004580d04142d185120041c11140c1e00241821084084e080d03107000941d4010303000d952058845111098541083c8107550900783d4040000510b01180d40c3c021403642e10190009a1081c603024811000c0782d0001100680180c004090703031140806041120b15281c4240b0703503860768a121040c030303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 981654676 1106 981653570 981653573
    0x1b020906152203020411030c040b03040f0f0605061c0c030602210103140c090402060d0f022b1506020d0305070c20030705010315061202090901081b04020304 69
    0x1750300c3d0603850603c10300004100c2e0300c10000d40a0712807503c1d29025201d16030b944003d109448040c8046041c02c0042c95455907000e001d03001d0380c808102c41c24000208590000c08030080c1081000c00c0003039200040425070b00f4411290014001a00d840008140d4010f04070450341d80c849941c100c2c8000f00410003008101c0c00b00180d4001150549000d200a101d5501e200380c2d030107075101405004860020351103420000c02680c401d9005410081d45e655014000281c0c9401c1c5a000c8400d5041c10360024420301c5802c08030000c0741c601c01c062034540840a901c4030b4201d5485010036407110002a01a400360110041d0103900904004a81d0600c1e840c1d41e2004088014a034070078000c1240008041d8403c0c0075100c0002c5030a840c0e540003e24040741034840743c0201c00381c03004450b000d02403440ca5981c0d204c810740c001d000e2900640b544400022028154040d040e07400d42c49180305006120 = true := by decide +kernel

theorem cover : BRFrame.Cov 981474820 981654676 := by
  have h0 := BRFrame.cov_init 981474820
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 981474820 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 981474820 ≤ n) (h2 : n < 981654676) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
