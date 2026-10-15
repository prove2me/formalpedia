-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5445
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:24.717056+00:00
-- url     : https://prove2.me/submissions/0124cbbf-9d6b-49db-97f8-7622b32ee37a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 979136690 ≤ n < 979316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 979137940 1250 979136690 979136707
    0xa0f05010c030c080a091a1207050703121401050117010b030a15080f1f0b060f0d1e0e01180c0b0f04080a0303320129070803040204110f 60
    0x104503189010960500103080d4000c000103139400c00505c030303000c510b072101d07001c9a040c03e2648480b9850070650348200c00301001000300900d1150312041d40180946844d1303a0380c41d0303a86002c039001e04000815103006420f00048403660349005019034141c51003a40c55a031000d0100000b4000b2803001c0c03007035551000c0100045203120a1940100b0b4240c0b2500d03c9140f0410b135144030107482c0519030104000260440b151800000251000f54410005d0108050007141c035200700140c018400c240004011603000104c11f4100801034001d1300c0803800144240110b191340342803c0f009480d2840c0070822075440d14610035001c0011403911040c464020041081082c24903420460f20760103440341360701400090100060000c4108001c5000b140320b56800b03c0c40c108880c10300d000c103000d0b141440c2d40e0240c110301800074200c004070304941119503502d45600c0210b00b0750750501030b03000241c50b4402e110b040001e42070244114500158011407003a101080340c00114807401c6d07100d01034484900d44c0f40c03008201041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 979139190 1250 979137940 979137947
    0x6010c0c1d1e180c03161e08030d05060a091a030d0318060902060906210106080c03040f020109180510050103020c0307060f02090d0f030201050603030901020a0609080c010504140c0a0f0501 83
    0x900405030700441e41d0a0b00c405000a00d001940550500c40900075201401f188440022100310780c008170704400f40d81820581d44a449010b10300404860b00d5a56000403041e9560942801c0140040c080c204400d12984040038851100403080b00d01030701c17030422002400f0b48a84242d41b850000700080300c84411f445c1c0e417000c010b003040c01000c3ea40000240521201a502e000007004806502d01003102d0003029510b11181c244416480300b03052200400410131a505620704032644a6405030000e0b4400c0503610040e100d04401c2d8114540c0700040c40d00c45a04081c00e40d10840c024030045e1014242296948011001d900c12440a906181c20510034000010460742007a62000340d40c4001600f00f44010004c5a414144140b003a520f18841c0c42d03d00003850380a00c101504001c0940c044c40c5072940c2400040e6441485407070003028aa03a580c80c510038060003109507442d000e02c5900901150405007440c44000f012a400308035680690628090a8580014a94101c031300d803000c004400740c41d007030054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 979140440 1250 979139190 979139221
    0xc3308041101021b09040c0b04082a06040308030a0e01050a0f06080106031a04030306150c0b0703050103080306060a0c2a06050703090b0f090406150210020403050a020906010c0c1d1e 80
    0x1142d081440c6a03000c5003200301c0002032702c0035261801c02403c6e888444181d070302e1820700d0355040384a81c085401d2180007544811003200c0545e40c1052116580c4e40307491400000406101481d1203081d46801c01b800350380c09084c1c110100801c000c00f02440080c0d1221302090881d951880300800100c1c4084c6006810740c41c0c0c4007065807242c000e04000800e10395560180c0c0760890300b00fa803a400103610101030010040c03580425500141d13589001c115035070441d0b40340740d40c6100240159114940100321100028802d00d8103001003680880d200c0030202d441e02c5081242016070000703540c0c80c0701c00c0d0400300c0e420384079000f0340302910340541ea0500154130701004111039034050003819070b90b981c082100302101e45130703402420000c16015803404091954241c0007070030701000c60a0500124010070007000441c50016030f01c02060f07012180003040d030716404010b84241d0900d0b00003d01b50001100000703000c240445c0d0240c2030510f170b100c1c0c88106a070f40545180030100d580c3e030802803100f030b00b00204040c90f4104900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 979141690 1250 979140440 979140443
    0xf08060c04030b07120c020a03080c09030a060216051b03070b07030c110d1b1701020414270c030603102c070b13050a0807030c3308041101021b0904 65
    0x1e405e400d40010300c010907103006000000269010148900400d0342c4240c6403035124481c2c003015814643d00c14002504c030090801c024107841d030085010200c1c41c414111039100d04e40c3c000e080301d802114105502d500100003c40c05407090003515400200c07800d0243c2100c11042d45982c42400d000080d0ba00c0c840d0703445482c0d03107413504a001820000d0025454400030b4115580c1d1201c141903882c582010f242611040754510412030b4014001000741c0c1204551528001d0b0301115401d000c40740f10a03031f00d0200414445c0d0862813903480300070320060400c00300007140151030a82c241c840c2c0c0751940740c1c454107130740b054101078003034860643c41007444803e441284080f03540c1e89010303240c085644920010840d0868910801030030103200c010007072850711101d04001810b004018100403441c5440f0031445a0607449401280c0440324845d00243c03030f6845000f4108045040a0342c64200081401050103100302d8007103e1100d0402072042c02580002550f00c020380d0b54000d5103541c4c1c60801c05210b447c1074090030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 979142940 1250 979141690 979141697
    0x30a05130b030108030d05090d0509060c030d0c0c0b0604090c051c0b0718080a0203033411130b0307061d030607080f01060c080d0b010203070c0b040f08060c04030b07 73
    0x420101d0100c0300541c001e1016070300450f2a070341c202c5008000c850002d420446c06900007101c2450082c0c0280540c0e0412100710340c2e40b600c544141c40d106003907102c1c00b19184402c0c1c0c40e100e1034001094104d0801070055014006a0342e0a98a5105100442d050f40c0b40180680107024420421481c040b0010030b221152901d00703d0780109c00b9035581014140c15115280413901032a00700c60381d0260368900354000d00c0c600d0028861106681c01294907840b0b01c00d01100e2042d04501e19040c0306900d04034080d0b8002c2101420f044654803410b020444041b110040f41c410011300030060030028080c01100803003800100500001841c0100a03241c140d006690000010389440d0005079a60b01400014400c4d04117899121403898041c904000e18401600418113108158005001082821060716102c016102d070000710f000018005070b14500901000030203d210f040408500803408502802c21150b19424501d005078541c100f232912040c040f50324202d0b00714180820808146d4400015801122505 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 979144190 1250 979142940 979142977
    0x6010b160b0a02250b0c0a170a05040b07050910030b011206030c0503190803013011040606030b0d1502090603010306020415031a1003020408030a020f0c0111030a05 72
    0x29114140080111211500d2a901246440c88013903510a08044206840e5a000b070390303001540c800045220107080103409500114481100380d008051a040b400c080c41d00c5102c90f450441e03081800340504403812110301c000e040110303505074010000d0f501444401006080c8000001c18114021300150380101e04000c0006441c001c80c4101d231141f43d018501500c00d1078681c03800d12052502d4440c68003ca000000400141e80380031802da42c0540381510305c05c007441c6040c080150049000d030540d0301c079890700042c09078441408100d146c24a0303411010b0255800c0c81842d5441c09c1c281c0494100252061304680c0003224a00010710304a4001c0e0031410f07000300142080b1400012401681003604106c50f4964001414442d003844d03c6108808001a854103202c0500d0043c200009075052065140c040d00d803070800f103070764903020740c0658025203060310481f81c46a0304c02500039610090116910414018100102131651080b038107042c00e640484021880c01087e07031000c842a50001d80c21811411405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 979145440 1250 979144190 979144193
    0x1b100c0305030f100f1d09030a1d302803030209060708070c03030e04060315050612010e1b041a0d030912030306090e010e0c040906150e0106080703060806010b16 71
    0xd02c0d40000d400100380c440da601c0b00c8580307242c1d5094400f40c407024640c0c1c0b041c840504100ea01a84100d4124400042da20042b1400c4000c1440d508004184680c40c1280c10104000103503e6100d4101e80f011050481d00c28480c0d03041d83e1000c1260380450324001c030b1410400e140200707000342c00070f00001c54090601464440280c4030540307035070000c010440e01d18844503010801d1540c01070030f8090210003210208091480c56035050800001c10a100c40e4080c1c032440012030faaa034080c25141e000800702d009125850160052940382c00c10b1a403540600b60000c001201d450405100c2c03120500e20341e00c07065102090303120401c4020903200c01d00b00d00300300c1c0c40007011854010500c04804002e1203a100811000d0030154100d007910b6001d0031031481d076803400020350710a0b04000fa6038681c140050b5400241e8040904003200680140b46551010714030780840020440d001550b40383c103c0e040d9554080741c41e02c480c141101a5443d038070507011640d00803401403000034407040060040340420b2640354200482e0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 979146690 1250 979145440 979145459
    0x7110a03080301030b0705180108040201200601090e0307080904200a1716120f090218040506090a0b0105010509010c0b09160b0f031f03051b100c0305030f10 69
    0x1950011034801c0ca02100400030441204056078000721142409410640d43c0c400350711154048080b40750420506a0120b03007903901503040d103070031a4140c49201d820074412418440e0b50390428441e4880c40d42c0b0301920901002e801000b40d6020640c08285a46041d20890800000c1c0c214070b0704c0060b505000c0e4464031130402c000340041400ba81540c42e0052002a139009130401200020002d400a500c1c203920b0140070f66001401c400d1010a0950000310b0540506580c80148200c04001b0f4004003982a004030b5945007415140c03207640b08a040302c20b0f0b903841c12001c54940410510041c242e4200b100140b06642c01600079086948041c54000034002040c1c40300d226000050b14a51465085280350300501412000c0340b001810000d1122480c0c10809040a0002d100c01041c2c400c0400d078580c0507800d203e8803108001e008541003000c40b0451a1865501c0400b404035004c03141c85500d50a00d42000180241c49181d4100c0d0562600c0f03086a403a2a010408400000c03c00107540c401c003400840e02104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 979147940 1250 979146690 979146709
    0x307120605040507050d030507170d090305070b15060a1d040204090b0a050907022a0315010e010e01060509010804050106030203120d1505090103151401061d01140306060711 76
    0x1180041020700b842d0070018184109604202c1c000c1001a18601c003190300001241c51444c0d201c01d03000b5400140140007d07850142460020310581003004000500d54440c1c064202c890282c03205c1652612516184841034521078402c5070484018029440b201d80504e40c81c10081ba0040361800751004094001001c0364859004002000d550b403450b180c032030804801d0078002d04001d4800008600b0004400b075694400640c0d600c09036104820204141c0c1c0000800308484403000d8203c0718041c06000c4c00d800030103000d001d0348240701c2d055000000c1c04079482034441d049401c151101c0b40b031300c6028001140c0a14004005503141d43d200c1d480040180c804105c84c4c500781503110040d5441d1814031102c80f0940324640b010300b83d0804078500c28081da41e9901070b0141143d80c800482c1100010300000100540494004003060b040700c003000180705504014a1508403007800c14030045003200f04010b490014455624502c1d42c1000d100051080c205000100503603400380c44500c280600c480002060003d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 979149190 1250 979147940 979147943
    0x30304120b100b07140c090403020c0f0109080304030c0e0903040f0306050c090307080d110303010305120724050a11121506091f0f0c1509140129040603021c02030712 73
    0x51760a60064030f104c40510182c2c0a4410803600119541410380380250b03141c3d440184140300318040c1071442c1c0c60f40e00a0b40c0d544002c04007181920f0729241e590130651f082c83c000b0701c80c50440030205000600200000300c2240c007a00e40c0005180d03001415a222a0014080207000c41103407034003001a4111581c08001c0c9100502802c00180f0112051031390060403c5040d00001216a03c18001031000074008036a640c00412803a582580b1110107082c01d8a02c0410241c0102c8400c06542c000b80c0c56103004d4101911030b250250080c80039031060a0501428071500c04000d04c074603100404624107808115004003011001000c1300d060100010009800080100c0284404041c0c3e22101c4861a00140b0031001c010003030274856035045c001e8403400400b1016080f01142944c2d114605010450b00040700c0304940d411400030028003040041c418015000704d5001481000c44c80e5100c4420302d001e0007604160395025010350910941030810703140003220401c08076413501400314003007114401d94500e904542d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 979150440 1250 979149190 979149203
    0x108191502210907050f06040504110f0c0f0d0504030305030a050402030111040933031101050d2f1606090609050105040c03061406150706090506010b18030304120b100b07 75
    0xc3c101040a1807500c402e0340c0c80f490164015005040c0d966a0300ba080e14210360040c2c80120701d48000102c0c03200300b44200e004990301ca00700840c0d00449204006202072204045008480d0103411441040d902d0740510301c4001e002a0003000020030240c1d8a4100a400510240011409810003416070354950040d421240d812070351490114045044440c4058826645901511841c20100d084103481046804068181c1105011894071640f20720b080703c051480f20041041446001c14041245a00c00c0c10b18150031040071010140c03100f5400103c0d05040345a40449200e105940e6138000a00410101983d03505c0c4d03101c101102048080c003d4901c11803103100359441c0c117400c61800350b04031518088502401d002d0542040503d0311607142010340c1181ca000c400e501c5401500e0060701134014000020f091b4080d803400000c0d0203a132103010f0042c40a5180781105140040030916540b4056445000c44230840149214089001d40f0030550b0407100c0d41450000380d540396065402c86a000003403c4908 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 979151690 1250 979150440 979150507
    0x607030209190b0f13050402070309080c0f091801021209030417010501060c030804050c1305060406051203090907142206080f2206110901080108191502 67
    0x1450206003811480521558001e0b00504094004a40780a00b0320000c0200c90001075035002081011441001802c0003001556100c010341f40c0100081072130b10582d001d43c852250b204105180102029070b44a40180c0b05800d90b903900c20b0b20004003a4206a80000d0b550700704048000d002c600310345144074111042c019a07465181c501e08027207104944001c08007030b0345443e0043c00790a5011802001d9244c05160504031911182012424141d40c40c411942c00074010360030750301c0880c0d29005544103200c115820880c903a074903001d0041c2e10340030301b40308440c4e03400403c030007281031a0122321076402902030318080e0b00d0825080b500030720700e1740551040090340201c00701c01c0c10703205407803464440500384500c1c1048203801c1c00d0341026079062016010b410000444000c0148000c002c6911480464110405000c80f00305000c1018a41c0e11039091140094003041c004581448000340d0b00c1d004046400c1102c100e100c154460125601805e22130300c640c1e5400b0032800052216a90442c208150000e045104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 979152940 1250 979151690 979151707
    0x9030102070614012702030c160303060e150105030103060c090807120605010b0a0e010c03030b06040b09031c0f030203070c1a07020f010b0a2d03080703030501060c0819020c0306070302 81
    0x254240591113042500811041204a4140409003a0685c06900405600d9481d499031400301c5000b20805c1805009001039440706241c0e2681081040302c0000c60060700c107480d901e404822004031701c80c406012032010001000040c0866020301c4507040d06e4a4951061a2030f213403843e0810040f43d0100200d5441c1080034070901c4618428140182204c00c2c10510b41101000050900c1500c1c50310103040c070080c1c249440c149070180d0442c85854100030310365960780343c541000425a0300005d480c50300074803403441d481080c50022080b0090031440350329800340c101c1084000318065070004221800304508410403d0025821620a6081404849900d021860010f000030f1820600000d0f10300c5583c1441c00c0035000f85c0700d0100040990b40c20b0007074560340341e042d895a0100300d283c803a2043c50701c2900c007a0010503c05c4420180000e90301ca55020f001c1a40da52208a94103100d15001800c00c1100300440740c032203600e102c40b0b00076449841c01900e40081c0140000b0b420000200d0faa480400d400050700760 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 979154190 1250 979152940 979152971
    0xe040b0402313c060201020414030304060905192423030601120e06100e070302090901120f050625140304060e0712080a080c090f04050705090301020706 67
    0x4105003500340105801850100780c41500540e000806048030103a040b0000800070f0500050408400c54140c000c045980d03c900900075485441049200219100348089614000c41140c0c11035000380d4a81402c1410b210400c6010041c5910b0629048105c1c1d200180007a0f1200500400c40c005104025042080b0440680800300500c6190b1064080b00d1aa160945201c415203030001d0b000c1ca0410940e52440704480d00514501c2e403010860320075403041143c600c5030301803c50705440500d13a80103000d440700c09041c0d09134020010703150344c06207031340d001400401c15150300c0414003402010800c803ea007003070f10f8007814680c00382c901440561044200300b0b02c00c0480302d0918821226841c2a240f4080d203201c01000d18000034100901d01500c030440092b01c000100100809000c18000803d1030181034a07041420703601101011000c100d19500060182030b0440558095010150440d05130b5010001040000d1038014003540c28480700340034001d46520244045c00b00a4410000040c00099050540 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 979155440 1250 979154190 979154257
    0x1403120106112a012f0703301b0209041101030c140405241606050c041214160803070b0a0902180402041503060b15030c18010e04050702012a09060e040b0402 69
    0x1004000c2c6462302c1c0360542501651004040c00c2140b42000a58004c000074030700705240c0a402961104980007844140082c10074110302d0b40c0c50988080003041301e0900c094414511440d510740c1c1009080c041000036050401d00341e010320f09800380d10b410342100a18441499040b0003058502c0e1010503003014200000ca20850b1341185800030700c24246468a03812411007003400200134403850704102c801d0140c9804000501e02d841c0e00b101214030701c3e500ca49800da540e402078002034810144600100d890b60b02e561041c40442500034100400700300d05900c0c1107030910b4003d03004a810640e1850a45205071140300300c1c8014500c40c8201241400700c14080002001018a032500a02d42c01c00901c00901810801c40301c026407004801c0e440480700d07800603900c1e4042026100d030094144810008669819800f0203400200c3d159017180320780b03204c901403c01c4112409180041201035409001701e500461540711030b144010030106921102c513001c00c0c00d0707820620242010b464048020440c0d0240390710017 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 979156690 1250 979155440 979155473
    0x3072c0a2309031b07050d050f060a0c050f18031b030f030a1b15020f04080d18090b2202191b1403120106112a012f0703 53
    0x2540007900307200881075140e10030850700c0001c4951030419115002c50078028100141001040010500b800b03041aa4a51022825204035401007d0001d8400b0300d480c4107409444440703540e080d04042d040002002c00340e2150fa1100c0d410010081100c01a81d010090503d1980b00b0003c0d00403100384503401d041c60a200402402100e41060100e04071540e4081040088003244a55000200d845802c1c02c00c180c0c90000c000c2d0061900000c2d0300440b04d1b020340024002c030380054040310041d01b001d0504459604a80368452080d0304015400c006105143d00100110f040040030003980800e840c6a1a40c0c840d4080403407541d6a070080740c1c45040c0d004a007030340c40456107282041802e48060005412111800060003080d4050040d84142c803400e040041e5005000501984000d03540c4664000c2c0420080e8000c61029204500260001044040410854502c80781c0d50040648810b00151200c2e12040f113042c0e00000c603a00036088a401c0340c0301c0391003007040702c4000e41203842c11410442c403001c0c0050403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 979157940 1250 979156690 979156751
    0x70906060221070c03060f090c0602010b0d0b071103030a1a27070c0f0507050307080a082d070803150109030302060712020c031c05060f03072c0a 64
    0x2d0541c0094004021100c100d03629010b60707803410140703821590700d00c0a40000c0c02c4c042c61308403065160060b9a0000a5660041c651405080d41c2d894040b42a26006c100c5141c100d1025000080094081c020481c0c2206882c00e10011007100010a01c0c6550801c440040c0c0700c3d81c41d40d0960314803c550040c055081c04064807182d8101203928042c0c99503c01c00303545110320b00c20103400903030304034821400060107a0340425200242946130400e039079908424001c0d98400c1c0140b100c0041c5906000844078621507002460307604000c0710300c00b00034a40d4a6003286104051801c0d98107a071003600400101201d6200700441a1641441180002c4001c40d94048505100810f0424001b081e0001000b03030384021a85441031070a18480241c1001c0d0160307845045040c80007140c3c40c0b07900c6500011010200d50302c2c041c00c01c040c0d5542c0c4208100c0620007030006805401080341808211007440130302c031180b00344001c2c2140307051134008404480c003411038503040c3c10350317a40100d10308542d502c003244614942d1400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 979159190 1250 979157940 979157953
    0xc041406120706091203020102040f140a0b040f031e02030d050c01050709030f0813090c050901020105061c0b07020f030a0305061f3002121e0903070204090302010b10020709060602 79
    0x141d002d40a146135000381101ea485507045601054404d4040740c0c081c080706046891025510780d5a4016100e0a4441911844c47c1e29004106040c13441d054170110b403040010059034500c0c0da240c80c07422100d86007000b42d40300d4480d2403020240e14100051072004845989059487c0c400038503980c01c50300b0250103001009a000c500700f000ca003011100504154011040580e51080c851511036614019800a20800c1c2014011421076411801074000e5002c02c5c2c00901c8241c5d240c0c3c0421501c0d070420301c0fa00d000ca042185000d00850032011a10b80d100e006030040f1809218144942d42c6150482e1690b107001940311000c009043c2403604240700b8070303021003500c0008a2030100c0050300951034001c0644a040d485002c018019500000f49006003856501c11541d50003100501060760713a0464800c2c03916003400700c40034100c00030030068a10031044000a1801d240565081102904002100f941159200c60804171141e60704500d401d003040e0b1030340040c2882850401408159181903101005540241 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 979160440 1250 979159190 979159199
    0xa0e161d1003091416121e1703040507091b08070806030304051e0f180c0304110301020d06030212070602070e0c041a041e03230c0414061207 62
    0x5a00508030400d045038034007003418885808030000c1180050203411180881c204030040c55020035140c1031611a44103a000caa0344680804213079040b4501c0003081d14541407124455171000010b0454803a100300e0b400c00c80141d03079000d90a09030b0070a58080e54103401008080112540e40d1017071100103d1a0382d00c02c030041104003005411404000c0081041c40142e800060990303a09004031000f03018003e105040c240c0c0710303009030b81c5c002d401c8511081c022440080000201d282c0740c0f88e1849044041844111a07a440740780740100f980010f042102c0030b150752659900150b07030038005460356640450740000c0d054a9401008800c1c2e401c80d10b001265040307100148400341d07001c2a445c0c10b542240c0064070407500c0c1d80c007038900b07070703214aa002080080c1500c40c0d25840f10041001002240c20030511110f00c075285010380c0078000300d6880000c144080c00440c0400481c02214401040c0d204075017075900310307090003001c18182c48001030b22100f45841501000748901d0031000f4400c0030710a0f180105074241c1030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 979161690 1250 979160440 979160477
    0xa050108060f040903110a030203091009080304170a060e100c0e0607171b06010f0803040f06180b1c050109020408060c0726030f090d0e0402090f0a0e16 67
    0x1680c03803901a0344c0b20188001894050b80c1e0341e1100f180020b044075004d607500c0c00c1c02916070700f11940d0240308041160861190030301c5a205c6a00b620b11a0001d54505850507008040c4a5080e0b10941d800340162001480400d50510500b446040684091309058104604001c111103030140d42c8418006001070560312078a034102079a0307101c0e600816215048001840340c019174058120f4000400701165030800381c40e5404aa4503048951901e889000c0c2c4e9143c0c41821b0311780c001d6005100c807802004e4810000d00d0703c0344c066080c0c0d000e0840c1c90009001d03120302003023640e9400101f4508a0040c000c00080101086200e1540100705031002103013440d050602151b241d030005081480130440125102080c001c851000807414000002d00f07811058103250391540c0740e00101d460343c00e038000c400c0000ea0040400b08109a0725031155481200030348110341008000d41106c5500c580220000d15902d0013a11003090f060050310b0840c06900e440d103401c240f404001c44c0f000907800c04105c40c005424022000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 979162940 1250 979161690 979161709
    0x1203070f031410060507020301090602180102060f0c09011d040606030204180e0606010c1a0f0a050702010c0c080d020f03250c03080f1e131110020c15040807060306050a05010806 78
    0x1000d20300545c1c1d51840d4000239004d06060800980164030000301600004e0821210001000c000c3e0260b9503160780d83c900c407140f42d0034119081c16090f80e003040300790710f40c0d80701e4004d00c0828030743c1f60304910800b05528080340850300150003200101ea40003e0500030300740410b4140040044126052000d40750707041101e602c2d070101420440c103200840b6855010000440d0492680c80c042500c0c05a00e440e25203040c0e502d9460076541d02040c2440c01000c500064418003880d880002142c0300c01d040702d0178a50325036240c0d900050048504030381c244810140f4451100080d400394130550680c85481141c2d008034403020401e90440700c180b000b5090100f00103a003124480358804540300c2c0662055840179801d00c20550b078521801a1b00e00ca0004100d408804403e0181350240030f204030780c1000803000b080c85007060031003080c00050381c0000d400f80000d00e80078149002d50048201b00c541803981e1404024034049450b00800c01280d02d0b00ba09004500b02000031000614003468188014102000499007864 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 979164190 1250 979162940 979162949
    0xf0603020103150b0403060c02010902030f0a0b060d0b06010809011b0c050c010206190b010c0b1f0e01270603121e02060606030105010c0501140c09120a030509010804051203070f031410 81
    0x3238880c080041d00314001c0d8071094000d90060300751103c50031102d0300592213031100d000031142007041c00013181d038078144500742e0005039600040b00101c0b51140801034409100080c40c83c1c0c1d8564a81c640d1004000309540000d50010054a40c502d290400f8603040b810030032285000340c110352001040003120b0a40551100304407081d10400a4250451001200c3d41003141c04e024008420100c28046a507413003444802d1811583c031200c1d5020764548109550404d000c2c410000702d80c0c0021201e00002e032040804400d501032804001400a0790b81e42c3c0d881e0881c00031242807000c00ca030701d821180610710380045c0c10383e41e081c140302030421482c2c0039000070014041801041d04000254081c802004401d6100360904410050001142c0c50314501c040704540c400000c050088521a070384c0310000c0d1002407442e42565050321880e080500c83d900450703a001e4003e000f9541846001d80800c11032a400e00218002c041c0b50fa41d1440340090940041c040d070303802d5010401118916070821801070402000381c0c0998 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 979165440 1250 979164190 979164203
    0xa0e0c0301031410020318160b030105100306080f0d11010b0306011424090a0501090506040b2209091406090d12020c0105091b061206040f020c010f0603020103150b0403 74
    0x6400400d00300d407800b403a04c60450600c0f8400414054407007034060081b803540d00c041084550301d174506140c0c0c41e80c800161041034034440c41403006200e6031030a911115102c2c4103a1400262103607a4112140c60030b141c0c0020346100e40c000100d0051000e41c481d80840e1300e2600d82000380304514186c400300b42d482505110350084103910380000780040d5150b00d2000c1045170020706061003004520100e00d000d0344005079561050035000c600090950161080c0c0040f01da00030803860416181004000c0c05078480308051200d000141200722000c42213001c0c02c0080d21031440001403000c01882c000749040079101703151a0366840141040380e00440040d4074860000e461a041072084448945200a0301400e0354809013542403808000d400c841c00502024151481d0694801000403441402080d00c00d860301d6541c81c000400004081d820940c2001e1242d1040400062070040000301d101e00b15003054207100e400d103856500400941d03a06000b407186604030a840b8200c05450001c10428900c41d078400104103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 979166690 1250 979165440 979165463
    0xf0409062106020f1207020c0910081c02120408030409111801030b010912050609011b090902160f030c050609060903070b090c090403051314010c141015050a0e0c030103 74
    0x22041400700b903c042181c1703464100350a00f04480b001c7e40b1402807103c0c03580030b80c3c0c21b1030026003003034944c2002400700c0300703801e002d00140101c07400e4031810098118440c1c405d40c4141c040c580a507c2d0550000c0c401040c491014540301d50906002c482501c601034024101000b041c0540940c0c0000b14080d10803020090800083c40b0319020010784103040e0b00d03071210b02e40361110f0444000703000000c58540d00c81c1c030f4440c0082185069440c2d4520300810001022800250090424000340b2030560003003405a045103e0890f000700e036986d42c004882281c40c000c60010b0080030f00c14080003000c01110782c2100d91000039106518010b49055a2402008009010102030700080388592a040c806040c01a102070108400c0d4509400c000e00030794442c4058843d20070502e480000c1a1812100031018408140e451810080c02c035107030010008404030200045001c1c0700154940d80c001485108188404103400300070310313480d000030422040f955500c00c1c055114544100f10011102804481c1500d5010103080c00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 979167940 1250 979166690 979166707
    0x10f0311042f0a1e2007080304090911030f0c1905030f0a0c06081501030525021b040b0d170c251403070e1302060f040906210602 57
    0xa5000b00486100c1d040c0404050801e0000004401800305aa0940f1484500c080e8444001503c1850024000002d101200809107100d000c1041c0d9903c0d03500d40c0b0845d01031035141c0b003843d070842c0e110b6480800c4c0c0700c3d03031513503280100014842030403000382045000c2c000e075825245086458960811080f4403460882d000c01c100380d03403102981c0010f01005021607411640c03040400790b03a18494801540c9038401d600380000d40d00d01c1504020310404c01c0d400c4140c401007034030b001900a00400b80c0f9200b00d4450b803c3c0c0352a1910401e1114400400540e40140569280c020150300d00c2080500440c3c0603a0900001011503111302e10307800c0e05035510a0322240001c884000e01c80c000e000c1e0240b4051b050040059902c458601d03010445940c4a11000010102e961004000c401c592803011350360705a049400200040b1000c0300c81280d218a00361180d980c0c040c2258002100340d4040d842c03260921a0105092105251620580c0c0150100001c2e10300ba0050200400c1d256180c0900024112900002c9004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 979169190 1250 979167940 979167971
    0x150b0102030c01020408010632011404030209191a0a0326031519080a0f0219060507050c032802060d050a020304060f0506240906120708010f031104 65
    0x4050700b07104402191542c5e1140b22260181605209502240840ca01d81340400c0e505200704644243e20f13a10f0300d001c0f42007420010b5880b010502c0880604100c02e01001025866000e101440351071380101c149181c0380006082c000f2a49a480c0401d40d80c12111452065070b04e44d8011001503941140c1c5000044d10384180805680080b111490040c4601200b48254070041e0f50401c0340ca09002c581d00e8052403928219801703200d10a10070b00a17243d001c401410007050b8002c0c40c11100900280954044400f4520701da040d000f565800b5a002403000600703c4240201840140f010302e01c00c074050b100c84040400d0030b800c4100d1a20401c800c0402c1211042c3c1195140000c4039000e252050050220f803400548100c02500308480075075055043c00200d8650400342d02ca130b184a00b1000b044044088074520103030540110040c0900340c444000c0018141031340d1100003402162044d410f0042c003501d000039000b894000103921003140c0914035031040c000101e10031110700980d0016940000e44000742e91803807 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 979170440 1250 979169190 979169197
    0x61410060c0203071a13081b01050315090702280506041202150a09030e030607080a0903120e06100f0b0304030e1c03030e1b030303010308161e030e040207150b010203 73
    0x10841317460f07001c10019044140300030b8820500e000540040c03181d514545552180740c0b007170301004032058201c20700d0390039806100a0758010030100920000105620042002c01e1819114500981d111603a034032513031007403002c401c428200d10400140071501c8a66545079681c0c0d015000500151048401c8400c0501c00c02109181e031008070f00c84071844c1017040104000b0040a402034000443c0f200000b046424001602d030300401d051380c9e8542981d0f0350401c01c1001003440e580210304016210005204003d00e6000d10240c661130b841c054501410404d01c00c40303038142070740d12580b1021440e031420400044103a060b0b80d401754140c1010541c0d4201000011080e0040203049080450300c403804200f4035505034030250001c803140f8120385010b02101062040a2119121a030341a80204010b0001804e11005003140361204013010780800059510306280c00c5000e4266240600c001c10600140b5901003900380c40d050007078500310702e018401d07115030391070102c2c50f25803d0304d0586030301c04500e10b0391082089 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 979171690 1250 979170440 979170449
    0x140a050d14160501080702030a08180106120c1d010b0a1d030d0c060501230420070503070201030609110a03200c03040509150d122109061410060c020307 67
    0x584042d035a05072400300d0444090b000d0720b80001c2101000840050002003210610621038840188030754408186400003050140000b000e9501c4100c0024035041c480c001e03a007164410300919544030b09180b1002c542c0c5d07070031801c40740254481e03600410600080100701c4141107410301c0c05946240c00e80100030035540881a6940e0984038004511001c1c40c0d03c000c480c140217100d02002d10032070742c0e60200f90040000085210349c100a24921103042464260b2010303031140c2040020130355107981c090060b00c2e160413500050740c1076040010790f081150303814400c920207401082410440305018140d034281b240906a01c0c003050503034640c614070a0b0800781b0304181801607104080b603650300007011920307141e400c01e00c204c9028004007800700e80070f480710905028042002502c0c00079003544540f601401024281c5840c070902c44290030f610107a10880c400901e00e072007031a1000c2668850341c609141200c3d500f541d0703816180e05c040240724000048581087c04c44400d498000e12004403800020b00f0801345500 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 979172940 1250 979171690 979171693
    0x2150d0902091305070522023907050306040c0b1e0a090905390412120825050c0f060a0e0d0c08030f040f050601030b10140a050d14 58
    0x4100200c421280d203d600d01c0d1246081c3c5000e59030390000c0c840902000c000700c1010000042c1c411410720700c998044c000400d841e01042e240d0507103218092141001b2040010041c100e4000c9555003048100030300d0009007010382c0140b90b0f0340703441e44a40311310740264051345882d40c00015072140d0010300307001c1607a03800180c540b0140d0740b075140040c0179100962502ca881d501030b040c440001d03a080100600000800c4241000e085141211008810b680e166a45d903091800002e220100b501e2010310090300d260392080c0c0400c043e001245901400c0040700922221240154000d41c1c0f40104020009180c0310125040c42a1122a022481414400c06550200503441403208002c06000c040d0055001061000e0a443c20641e00803021203443d01c0500d00603065170030800200702d1502c1460b0006e40d0082c011040c03981044c109a480a0607c0002c0c1c1c0241d0740030342060180b040c0c01260000d5131009141e01c0c0040e19680d0714103404283c100c90359115803403140d00001a0302060054064114014060400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 979174190 1250 979172940 979172959
    0xa200a1a071506092d0903020f03122e0605090102010f110403021002030313020904140607030b011b03120203100b130e071b0b040c0f08060603010b06030402150d0902 73
    0x101d020010522441030724042401c0050603210300d0130a668110061403205d803c0c034181c0241d80340241c0504070100d0202e08610a101015503103130402d0014000303904c50703a00f4000c21404d0800350301454020150041509100401c2219107025580c1e09020031a142810113030384402c042e10040c6d004142440f501c51085003800c00c0c0c40324480514008000390391007203035028020083e0303120803070792400b04a41c0c40a9007014403c405015103016050254024800d109900b01c00c0f0441006508042e07080d9207c3c000300791103940101c4a583c102d0141240e402c6e0041c00621a500c1c80d0b200203114514900a00882c280c1c004003060000c01c003202a4005891039070b0480f41d459201c1c1c5038050301c0d103d080c8107180d50b20260740e01081c0418840c401245a99680c2c07040040c540b9260b031902041800b01070411556041e20b0300001a41c040c0c45800b0900070042c01b4050a8546007841c249400d507105640e54600c0b9010400801c401641c42e40d60030340c000100d03808200c1c1c948082545140042504c224003135030080481 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 979175440 1250 979174190 979174223
    0x904150b060a0c06060f0509010e13080a0804020f03030c1f06210b070503130210030905060907140a03031b060209060706020304152f04030f050a200a1a07 68
    0x2140200b1944e101e07140420a0355510740c9030014140c018040c01d5407101c66900100642d51a09207681d400100c41c40c0008011a916503c440260b4010220a408118054200015464241d00d9514282e0701075000d0f52401d00d10f580c2250311041d00954845100100c00c0580c18a410305610060141c60b41008202c1440138006c07002c0c680b01d000740c81c01c483c0250103c0003e0221441401030f680503149000030030014544550030068030f09440030200c07040642d601740d0b01c00418820495180141101c0e4040d00784036007440c0c240b401900d8218096402074130340d80010070001c2e500c450303080d07807000e041c1d06544601c903910301e000e1000c4d1207650300e00ca6000c04040340d180c0500031181e00940c007031442000907038421000c0c40401c0d800e4848040c4200e204800081d0500d55040558114484407181c030000d80385425103070b56604000c040f202c801a10720341d010400010400c004014008004a40c8400000740c2410b250001284e4081c1401003400c143c5500c4903400b40c418160044da880d20358001018405005032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 979176690 1250 979175440 979175447
    0xc0a1e020a1b030c03080c0c0925020a0c0303140c010207030918090b04060203060f180103060b0d17070201030905100f060b040f030f05070b0304121d0904150b060a 72
    0x219402956002d01ea64400050115a507080100b00e03036202d1000030020b4510340f581009600050500c000c04e005411030850103650342d81596205030300100440c01c080d031a561550000350f800c128060b0035540461802e00100d01c81c00700901c00c0300c0d89841d0410940d414280ea50005005801081c0c1c2d82e5800403030f641c020160001442410394216100a0300e0208101c40c13040152428044003404142116002c41c0201e0f400c3d400175a800341c4c01034985209000e800010034104090800c070201d44035100c200510402081d402031041c05581200d0b55503030500320f601c80010030101c0e44074040030174174000382c08003c59010782c019046590b0824160b507908030981070507402900a850403240f07118500240172911603401c0043c1c0d0261045090b908102034110341d5244902d00f147c0c0310170340d01c91241160001e50307442010010352059118a085000000b9041c0010b8160003c0c150071080b20f00c0b102d000c00c242901c44501c00769210f5040504805030110821400004101a1450781c0e0051800124420303060b40 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 979177940 1250 979176690 979176703
    0x220609020a21051507080a05060109050a030507080c040b1302091302030a090309062c040204080303070203070605010e0f150d020301240b030112030507052505090f010605030c0a1e02 80
    0x5a044d0381301500a035111044424007141d584000c0380c10040482c1c400c141a910542e4050b0041c14413105180e1900b000070b0302d400441e801200e0540c000c100a02c80080c0902030003103808016034080c00389110366000114840303107640d49040025030105a580180e030b140940c030b407a2a8064501103543e401c002c800c401c00f821111a05602043c140200080c01340d03c030385803699041132046031494240103042c0e40c2c40c40c13a0a01c10f624035030068090102040540040c0000e501a400540040d0340c0c170700840c6072203030503102d0580c071602c520720f10b200810424084e82160780e640040c5c484d051074001c1200c040010b180003100040650550301c1d00c07012036007000d440c4024540700c4071040074011500d607640c003174200588801d02032140e0803015002d81200080c0168040d100807440f030403c1c0d41c4d8800040d41c1c40d0314118041800c089800c407030514208500d0810000305500011010f002404940c11700c07001a2003440023600108507040005507040d4080e105400040018410700d9a07550082e110560003580c901 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 979179190 1250 979177940 979177943
    0x9020405150303041505070b0a06080d02030c03030604021b0d110c0a081915050c04060917060105010e0a0308040e0406150311040f020903010509010c0206220609020a21 74
    0x14a0080481c031504101500c841a400c4010015031070207081c020703035000052a102c1c4074001c4c484244030303000c0003905000d442407042e84080c44c0003900b285860310b0300c0d00d00f103400c00700442590010404800c4112011041340e41c03040040d100569102003029140040d601010480d01e05c2d400340a40d2401c0c12070b84244080e500007441030481d106130484408000d42c01c0741e644200002684042e011045000c0c10460350b0502c80d000c0e003612082100900305480581d0001c0769002050701000800340417994020281c08054107035040700700c02c0707100301d0325010341c0e901818020903050111103c0305001c0d566401107070070007a55120321416103441e590b11541c0507210007510200c8010b410302038506031a030310b94141d002c100d94210780368948001c2a401440000c280c20180c000d0b1494007040081c03680d03207090044038050480c003800010042130240f002428903c0c0506114818404a1650f018102c02c5030b440b9803240b070b08144006000040c80c4002a188001603000e0745011000d0702c41190316020056100340942e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 979180440 1250 979179190 979179199
    0x80702010501090213030605060d02130501080d050403050c240705010204090509030901091707090e03070210020c010e010302180d0c08060115080403080603150a021e07020109062a060902 82
    0x2e0341c982418100340d014103443c01081c00401d5104001154131358116540202c8082c1c260b644840482c0c001c80d0340e542c20788842012083d290401003010060402c0b000c100041c0503d0000d007064116520503480c0c056080c103051050700748107241c0c000103000d00f1003000b0b04c0b8919074900781d40ea0790a141480c081d40061007058031080c5030400061a8500210488600e8041651865080c3c0d0600010300c81c000341e283c1503aa85842421030120340d0b0301c0c0511038091070310240c0c401503440d10708900c108283d483c0c0d142414400c5400820701c1c031070640d820000089001a003400c0258031104440b02240d40c2803c40050300d03900448480c1128180082c00064000762030240050710450b0381c94042d0918980008074003000000c1c142c00006010a01c560040c0d41c010500800f03903071140300d910709006011002902c1110131036500045100f883d019a862044171804007144040c10130356140c0010300488114400c003018850a191000301004150324216031008260b54542401c00e8030341000b02c01800314401c104d028 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 979181690 1250 979180440 979180451
    0x1a0a0e0115050609090a0e0a080d150f180e031306090b0a0219020d0204090b09070e01050a03021512010f0611150a0e0c060c10110703050f091c0308070201 68
    0x441d81141214030941e000600150724241c000000e0007015a00101119202656400c001030b41080c1800f801007081d0040281949030180810342004a80500d11900c1c0c088103419000c20000b00c0740001071007100e80d203604c031b0140e50800a55201c050581609401010f000005d00e00c4040002e110303511041d58807940d02c1c02c04103500d4190140302031256186020159022a014203010200e06c40c0c10080e951000e06401140f50690b804903080d503090b014101c0700c440d04282040100c01c4101b282d54001c1400030b03041e50544d450440810000c52032804080d0003071100c411100c410b41110411a42903091610001e039030b035a50b5401e480d45502040c091400040e00c0d6094032629010005000709141c0c2038003c0140407501d2304640341d07005010300020362110f405505101911030740c0740000f03060301c20850320180c80c6030802d0910040c11152070100007164030b0003c1c13080c00e010030351080907600c92080025110b40e907181403c0000d04194040c5c444100092103d100d5030080681c048042d0f4050341142d00288503 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 979182940 1250 979181690 979181711
    0x12181406090303010308040e040c0e090a02090a060b030a0506040b0a0f0312050c062a070f2d1b03020a1508060405070c06110f0f0304030801150c0f1a0a0e01 69
    0x312840f007840060070190041c001408560254851590050321801c0f1200c0c8559507601c0444542404035440b117040d030000380d20030055003004802d8583c0200800b60820206003801c0403416240005441e41c402255140000381e040d40700c1d1390002d09081c800030b000450890f910034200e08810700a0104032201d039001b0801d1700700d890007603050300c03410301841000d000c0c0340e6a0209594000c0d40340145403041c283c404800d1344200c0201c0c800401e0854080c41d100d50b469400d80c01d1103c00300303c40000a8407941407802e00c0e0ba07646250040e101ca6801d0307104020701e040070b40c01590701c80c254242c2c0e003000c1c6d40f0100d00400020854480c1001c100b0310400da480e17102140d0b460038204021618211840008501d59041d0340c4001b484940c0030320503250407206130340d08010000d19007182c281c02400e0f0341409000004140010305400c500514010190080310109150f609080104071801d00c0c0b10081c9400501c5035243c0403c10035101e6510070f2107506204490303902c1c2c040d0b1010085d0440b1031070f521080d442c0c140c5012 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 979184190 1250 979182940 979182943
    0x1b0109030f05070f0611130b0711090915010b0c060a060e13080d18021c150b03010f11091206010b0712020f2b1706011218140609 57
    0x5040c0c154885007100e116100081da001d6001c1c1100f160100c0c1c0d12a801c20001d003080c032906802c4c0051029050b264402c01480900c6414560082c00451b0740c1404080f0001b00d1601c032146082405480102080e200c0281d0145015104104440754090381c40020804040c8031010b0044101e8001c00c856454071102c519000711800d0740190140c50003100002420002d0035041e40c01c3d400d10a1892610700321610340c02c102100c825412141c130300701881d04071034254075168001b0b80c040c0b81e4440c400b0022807910f58070701031240d07d210f81c448040d5440d0111066555070a610500c403841d0344102c00c3c07041c1015425056031a5003c3c0c481c40d07200d441c8040b5600c0c8820070000b0154160b070300081c502460400e8685800542d82c0e14882c1038021442107441d9400c411406200e00000407060484c440e02560244c0c2c41140f502d641001c0c03d00c10041181d00c0007120800c42d610306608041c0c2802c000315140c00c5c000b00c2c03078040c000300000b0160b03140d00c031070044013001100b41d144c6076940010000d03141d0f55160207640a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 979185440 1250 979184190 979184201
    0x6070e061303060e15160908062e051e04380d0f0605070305010e061f02030405061c0b06070240020309010b030319081509010b1b01 58
    0x9070a90180c01c00078400686035034020340d80441c068048404201031400807100d045000c5900e8248480300030030381a28940c0040507a0083d14884014014a182241800d10074480c404051402c00585800c0d0b00365140610420f07501802c0060445000005900440904001c1e0f8032001401140f81101c1890030351b1060224141589098098400c1c400e90f00084122004440c103800e170788450540c2d1048001510301c801010001d110f071102041c0c9144c0290050229641640003e41101c0740100300202c580c0e8030103003900304410301c4180800301c0d01840000ca203180603940040b500603200140000fa6020811100c484002d6007141c00c0c0a02c0700c0c803000340081c0c4c0c002c80c9802504244c0001088000c28903a0b18030582104880390000003802003c440c06550350030501640016503400000d102e1904004c0c00340c5510414190700551074400002e040d002c0401005a0110801040300d000c1048840e0740784440c034408000810300f000070350311000064038585c03003524a049520740031001500e600c001030140 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 979186690 1250 979185440 979185457
    0x40b0a020105150f031011040e070f0807020a030e0607050f060c07020405011e0302060f070f2910090e0111070305030f07091406180405010e07200c0d030c120206070e06 74
    0x2400b5001743c508011801f400c0e1118000030050002d020204100c1917440d261449100e141c1d4442e0384a51604001030a074440c003078007100c2150800482200801c0d000b03402407581d807009452076075445a4900b061428510a44a8a40c0ca4050413080c030031004c0e4400080c0403001d008036001c0101d640d840341480340b51040c007144146940d102040820240c40d020015101c2001d040c4c801034030f04191603481c0c1c2001c8151352001c59007500381a0441441841c1d000201c01c118000130b80c60003d0303040c4102c0c2454510410311480c40a96100c0001050511080d000940304100c1c012103143c85072034529000c3c28a81040742e05000012000002401403072082210b0030440e01203620707240d540001c100c01d10a80b40d100c41001100d4151048207200342da10307244902802031500c1d0040e4032250500b8203000b00002c4451601c681000d00395492101c83c408042140b80038150300711101860030310285070580d500542150003405011541150300c040607004a907687c481e10b00b80d0340f00569061540d003004854000c1001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 979187940 1250 979186690 979186693
    0xf0f08070e13051c080f0a0902010c060c0201091a07020c0105031501030b060714010f05090c061b1c080a18080904110c030a02010e0f070326040b0a020105150f03 71
    0x403030140c81c00d03442c202650341d0040d0250b4002a0703000c001943c1004100f8040d00024403202c04125072a500101c0f055081003106c03500344200f80c4a900001c00c0c6091998019200315500c1e07521142c094000d6000d1307480107500c5003441c8075034200035400981140c0100c3d04040540105038046600b0b602c104100c91007160510054040400b000300110003c101900500c3d41100c0c04200c3d40d004034400355290800110910004100c443c02001800d0940320040e1140c4940da016120078085643d4401c151959454001c13402c0e0310300c0b411002558944a01035210707100c02c03543c001c2840340641d88160041e10a08501078103001c24841c4040e006103a00c0b0070b02e4081c2503e00d092000000c036103095000400e0410a181303085041c011007940c601c0c2554030005000d400350f0b40d0f54001841c20b5034180103102e00a090036002c0d000b001d00c1c5440341840440c080400035500c0403002030100704203003240706480280860b04818bd031600d100201c0a0700816064170001c80c43ca034640410340ba1860f11500760005108040c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 979189190 1250 979187940 979187969
    0x61506120e0c0a080f120324030c04090b0a0b01080103120807120c0306091406060a11150709050909010c02120f0403050a0318090b01020304050904080c070f0f0807 72
    0xe1036500801c09540000020300070801c2c0640640d843c1590480034140103005010309442800e6060f2170401c2114030803002c03800c20b1042141840f000700503080780100d00602418510301030340c00641000b00010460741d01520b420501c20038007051100c1c2510441d43c0384000c02080d101d2400554030050244001030450890f000e40d812104e1180780030743d82209290600c1910508010000001e50741c00f04440301c0007a40c1c44030204415152030080c40c80c046a2203c580c195810031401260b5544108007014050140c00c1982d800203820400200702e903003109100c42d081504040200400d180304c2489458803415240c804a2031482040c428041c480c180c54008003030303240004031422607036080030303c1c030000e207000c20710000010500c28044a24407610903540d040070b2600e4a00c3d101d00004460300324400300c0d841c0c110009810398000088606a90044901085a40d101d19029069101da02c01001e0613014100b40004c0400c1110340e4042900e00e02d400030600140c070f41e105180d580d046482400c80454016 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 979190440 1250 979189190 979189217
    0x2010e0309060a1808011b050405030a0b060d060e010b12030c0a03110a0804030516120b060405150d0b0a0c3e1c02100203010303210e1207061506 64
    0x14000c14601c00c3c02d0030003e482c41103c034401201c810301c0358808292a5156144641e4400301d405140020003040d040803400e150510010903607404002e1001000040040c0209816507511905d00d040c1e113034403c00a128903810010100c0c0a8462410450b02440704c00e00c1002510344040b050b204050f8040e8010240c214581d1411500074591100381095809140700c0103008c038840702c00600c06103004070010042180318640706030151031140d2218500300987d2a84800040481a00c0c0f03810503030488010900b034407491030b2240e40d04040c04025902855400d070880410021140c414420707409940304001c50040f1030407d54400101e8000b9845144100388000d1030121642b000404000000303050001075186100910b01d002d482008070058080e1074204c0108290703040210040c04100141c05600715455a94041c0c07991100c0340c21604402c940720220b0510b0a01c55200c11080380361001100c042e80304088900c0308135400100c09880013800c240c807450004504101e0b5000711603160380c4248003401c3c82c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 979191690 1250 979190440 979190449
    0x10e06011b02241e090306010e19060618050a2601020c150103120f14070f020a090c031112010302011107030c0b0a081005060d0b011404030303051602010e0309 70
    0x104a4200da00545005519420034180108084400c0c40d41000760b5031002481c0041c07140c03110712600c40131000800c00c50b200d100d03100803410134112803000142117010740781c4c142e40041c604003980e0461091450f1200c0001c400343d01c40b0300c0000d42e50711640c0100203161503805200e03c2403104d00070801c82803454030060300d10100d004000034060303803820300050805a0601c1203905000f111010302c045811024010f109100038072005200c0c107942c50920112600d172224014107030780200441c04002140c007049410038001d21114100030b22354000c106060040d10348842c1c400401d0140c400f00300081c503010f0301600e0903000c0030855141c80d0802c1800045d0341c1c40e41e4011580c40a4802141400f07000d0b1220010000342c0b22a000c9010f44409501c090b00c5038840200141031800082c003040c0707003007e03140d004c2180c0e2311011b0442d407a45051020218007030745102e005032011017024004000c0103600260000c145541540b1041c043c1451380340a0350303401d2491b0422826104a03840110540d0010420801203261 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 979192940 1250 979191690 979191737
    0x81c020102040e041101110307020d03030b030a02100206150f0901120c0b160b0a090b010312051e0705010c0206090d05070c26063601020909010603090b010e0601 71
    0x41840090326190700c4a007122440d0105440458540700c000101d9090f660300103110086418007079008504100054001500e41c1e5111000681450394401102685407030902070308030a290003412410382048062002596840101e80100d0000a0100703140d0b5a8a000c01202050580041400d0401d900b04900d40204070303144803049501d6205c00343c00040040388400075040401d03a44109041511842c1480030700e004005002e003000030300d402201c2e00010086000d00c0d054940201010198282201c400e80c1c141c826071b450100350010700d08144a00200f0b0302d0082070315034810030003800803401491099a480300c080e11120841d4000a1070018a203100380c002d004000e008500c40200386640d1482c040d0b68182e1503c803c0c0c04881c3c01c0e00c4070071041404125540c0c100c0e8017644c0c50300d50207040d00f03000c2c00032401c0e180c20140f0890184816002062003501641c21aa00040c040559540c4d60f0740080e00030918038000305e072044c0c41600001580e4810300f070a14418201030b145c000c066444040003004284 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 979194190 1250 979192940 979192993
    0x409050f06120c130f09150c17010302030a0b09030906070c1e08030f03090709020d0b120706020c0607020f040507080405060c03071d01030908040b0c0f030304020315040c120c061808 80
    0xe554440c003001081040707c020440710a96030001440e2420400000c040c1074084124162000103100100011303100040c0b0040900d070004800c10494980c131127241c0c110710804503220345c401d20118414090040885000046810501e010030032500b0321070201c0303400342c03442c81441709940040c01100e01d004a080e0055a00100c0300095440d6551a0001c0400301e81052242e07642080d070b030b00f44215090600d50350700486034442c0d000070300100e0f10b0044000d594030300f0104502d0003440041520000c54640e0803441a40f580000d1060000c1d26000000400d0b6206c100c5055403144200b00105041e151800d0031280144c80070364941201c0207640420882000f03460240d181095561420400801c407680080e002038441d41e0701d0190749010950000d0320b85581000c02601c50b8008000388001a5000500c4103601c0005800202040e0f6850500c07024600c0c0d030341d02030004100c2000c03800041040b038000b401d06030f880300c0e12462a0340c80385d400703c002c80400300c3c0111580c43d40603036160400b18110300031040140303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 979195440 1250 979194190 979194221
    0x20102070618050406031a0703091e1a0a0c0f0c0b07050703170f060f0301050f010317130801090605180a0602250804060f14070b0c0409050f06120c13 66
    0x250f4500204044650560040d1802031303038510440ca20030558011f50f030f000903044c5401e002d41c050315141c801c8000c218002d030103600b030b8030400180704101000f5121462040541c4140038a464503521502c090b0910485a00000301e031b01480c806054041c1007841c0803940c01c159007604d1079850001c01c1c2c80540c081c03c0190709010003203007122a0f102904507460706c071b890703041d4644400d41040c105011045a450b90301c0c520a034104420407001075a039008840c1180c1c2c0182c40030208404000d51407070544030321098812500e101c14004100400d05401680000740301d00d00402150395403041c00102d0540c020320940b215080091901e0110350990041d25401c1030070401000800c0101c84410041418a00204d402034400b0408004082d081a0f1041c510030441c1081d0800f034030300701d40e040a684103809c0004d0150350381c43c0100720044100010740300a0700100d0010416070a200b101d124034480111040c07071184144401c0b18001400101d5038880d0315501806044e47c10750404001d5028124523603540290 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 979196690 1250 979195440 979195487
    0x181107020306130c0503070e0615040b0f0a1205090604021003150602060103060522030c062c1621020319080c07080105010609090905150a140a05040201020706 70
    0x141e034040c0901402150300c0326884114500600c2d14020600302680158425048910b0420607601842d60641d400501103820b14003844401e04061080c2c0501d07080307455200c40c00310758402103100030401007118201c0c41d140d10304000a502510015100100e40460040d04003c0c04240103003410040040d0300c88403402c02062410071080d004890104c66800100164444401001803101c148509604203455025a40800200300b504409074841483d00804003d000000c0c28240034071540403001d08451010001100540400040080308010044030ba0070b008040040326080b04894401040355151104441800b8010010300c0c88400d513008d0603605070040d081d00d5940b6240101340840c0d89441507049503200c3d5100704c02545403030f00c20382005040d6894900148100740e0803903148411108001000b14400d40e0130725080c1c0c140b07541004528440798001d4140800318616400100c031000307001c40042c25668500300902e081c1c2d40c09450203800f42c0c00c07051091145c18800d040102000207813207c00f140303 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 979197940 1250 979196690 979196693
    0x50d0b1807052503090501120603200f040e0d120b03030a081014010e04020703021c020c120c0f0d0f0f03020303060a05060720190b0301050103060f181107 68
    0x210000c0740d04400182002501c0c0503040040c6211010580c40242c01800e410b2040c0d8014042d4140e500075a4113000340c0c83c0045203e1002504108045c1d1390051500c41d0310b031985a4481211041010303c00c2c403446a204d907152849c00d1a00ca0340710140c0d80b080c0141401000d034007080d01c024120b400c07200001510340c03004000c9500c040000702066007069440c0569498420400406412103410510340070b485820010300a0781d000844a00b080c204a5005030303104124a02a4640038400c1140781c0744424850401c05041e402042100c2ca42205803191382070131119a81040d12413210350840e542c40710b04480280c40700d051aa20f50781099100d01407100e4003104907202d000d2482e0184c40c04400580c0000100000d03400d000903200c0c0104020740e981410488540c0e15007076680d040c43c0d181480509500c3d007400c040e42e1402d44515a020910032141a100d403103100c904040c3d07000f40075150200307040000001c0d08280c0b10001108039614081c5941c1140c00c407a8042000d014281c2c00741d007a18409200400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 979199190 1250 979197940 979197979
    0x23061201150e180f0c0307090302060a0c0b130b0c040b070f060212190b01080702100515210705060301030f0f081c0b0a080d120513061b02010b030706050d0b 69
    0x81080018424000203803804e616210004600107003110000fa0003401480041a00303c1640c1040d00d41c112006030b2a0029100103e8000c00312510161801d640c0806020560150056044c400d500a0302021255514032161007030318459442030400c418810401c06c00070079410710304031801910845c0003510b000007030035240b640510113843e890412100441d00403403045451080b5403070881d00b0b080070750b03171403030700000207525118015445038107161070f41c000502c8006160608910704134024003814001c4022450407544907640b041e800114450001c012503035191400960b8122a805220a100060780b40d0714441880d105840071100a0018840110400004080309801c000031000c00210000030404100c13a03480603500c0b14401340c10004208554691210201e400141e006a0205054681c00e0b20481d070300c0b01d4110f01400350b610345201808901e010046150400c0300550080c895114038004040c0c0300c0701c0074440c00700410350800c01000c0b5940c103070304241002034004120115002c149807102 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 979200440 1250 979199190 979199209
    0xe1216022e121a0901091509021602010921080a02070906091406010e06180109090c0201021b06060907030506040f0e0d020d0306030c0e04081323061201150e 69
    0x2000441d614500c2840c40c1c82d003520038084400e8504001c4a205000391011900c980c0c018099040065103800c0b03010300d001290003680005054000003150350b039070403060100d0a0480400102d002558982d80040d04034501c049403031145180c105803524a5005076110000707940582801d00650040803030018803603240b44542c000900c0821004221194201403241c2860401450281880000203030200140c5815040e10750304081c034501608450260001070311031b0111a0700800c4001c0c14003140030030069040d009004903046040442c035007410002a4203440701402c60324560005550000601c03c580303c1e810050b00100301800020f00f825400310058151040e0303008440c1d29030320200382018901d034108080040484103180410406045990301500b450940c8101404c501840d0301003824002c200c6c04942074503a030f20540700034181d510702c41603e0525045140408103030046440e402c60782060740440c1c400082c44481c10426a00741010f910350345c040745039840c0130880d0040e01d02d0368544901144 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 979201690 1250 979200440 979200529
    0x1020f01060321030c08150d17040f050604081002031b070507030b1303020304090c14041403060601032711060a051c150b03041e060e121602 62
    0x7080f0210080000c0340c0601c004440108003090701d811003604810380e22035500c5822460a4a1036070820090350f001a152840c07001c030141010902030303801d42e0341d560114000e104883c5000c480081103030341c07201084802e0085205104040c0c000f0118500003160580c011a480440c1e0320101c00f1139802c5150680382d54204040403074103903010150030f0050002101d03115601c60b51a508040141d001ca98000b902d0780510b00c246d2502c42d84800c04140b80314060316980046107140019151541e50724501600300d0345082d50740c90301a00404011800d00d5109019214904100c0000d14040000d25105119070b14000c101c02e4681d50b00b00d055071042990f540004001d4200c0c0c55a8882d00d901c05621081c40544014000c410401e1400900d0f4100c048140b1551045411000d4280d4595542d400e20440010001c083c102611885100c1071301004400c2e88400c9100d2003480c120340b00440e84401c600118843c200c010f1803c002c41c5080640149420250b40c0302d20800c2001c1800c103003901c4d2020242d400042407a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 979202940 1250 979201690 979201703
    0x5031b0a02190b040b03090c0616030305160804080d0b060a0306030606080601080d111002040e010e132613030302011e110901200a23060411090601020f010603 70
    0x2040e00c15450009441c40c07101c035100352940e240c01c0c42c00038110010721031407044108002c4080001685044284020710b500000500789654802c103811a440d545556080f04401292400340071601441260f81104408800341d10b815803a178031140c48110175600280c0703080c0911a20340400031080d481d0b01d0081c2941d61016100401c00b02e007103241110686400350011007003a03218400400a07501c0009190140001604040c1040343c000e21001f400c02c10060304280c000750001600140c00b8603801f189038121003511604c2143e9845501025254400076038019001519044068504047d01c840002280e814110310398509038882c05051030b44000c42d40306801503503450500d1a0454801c0e45d0b400800c02011300101301000720100840f450b4080ea0007558100004810480c43e8295803400900c40e100d400300c103c0f180880580f42c815007240c90401c1840310354410040d1803542c0040010380c613009a40c030003109c80f1440300c258140329020b0030040c2420304610402c0349966140d6828400c443c0558012134 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 979204190 1250 979202940 979202953
    0x3060a030f150c08092811011107080a0606090902010e1018030f060b18041b03020603091f06030302210708030703020a14030f06010c0320031c020301050a030b0405031b 74
    0x20030503080c4000003c0c040d44001541d028039401e00c80c3c9100a200c407647c8092114110003020307004039003c00a071316600c000740c8200da0000c5214180050107460051207500e00b406100c1e21030940d001500c0030411700074080755080784180d100c1c0c03030007540c0c11401340890f2400d151032405050400c402494550320a850768001c5d100100140080c40c010102072460581300080c00301d034514002040840028405049440043c1250031120340c9206030364019500142803584a00386204004d8403081013003500380201c100e40c408880d1421460040f50b003104e800d038000c2c0c4052640000c101c054801001840c0f0345d03180e02046a04001215100654010905a54016101c182c0303400003400c4000c04130b14401c13000c1c0c0305104004002ca0001026076215100f031a01c0d0340001682d2405980e01203401c440c402482003c040c4620307095030000090282c1d15802c0013641c44a169464605040384000c3c010035401c00d640d80c0060000c14642e03840950058450340899107040303024010728015065410914440b0340101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 979205440 1250 979204190 979204201
    0x63c071b0c0302040f0603260415121523130c02030a021603020d03110f07092309030a08181006030b060f1e27180303060a030f150c08 59
    0x5e01c54102d5580b00c4010402046003191110504500c3c502060140303010110a100034005c45141a54020855212015454068203101508607401c0303a0b145a030f010301c1e0400c000c0c14102c81411141c00c07151100300d41700003481ca454040c84041c00d5070391010740100014030018120450352040007005400707503024503100c550350300c0300034140a902c2000b000b4441403003500b03001507621000001807540c0c0c5424043e800540c608451401d01e00020303002c1a01c0e0049044c000380d00d40e0030350041100c9032900144040d500030072105505d02c16109030358a80c650350003800b500c0d060700e010f071007619001811120071641c2e0200b88102d0a241c4012400c2100880b41c5a0340200104500ca0280940041c0204d0354080240f034440041449100081c184051880d5500000e1815803502501c114040f144114a8804030b40c50200440220406440d1000c1c81201c01c01071003000f610100c240d902580006003c0c502491950b1241d40c0e0f0308060403000d45840c46e00429030005081103204c2c0c0c08402c44561104076552400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 979206690 1250 979205440 979205449
    0x91225183602100507141f0f091b0602010e280f0c080c0f0f180a06030b010e06011b120c0c08031c0b062b140108063c071b0c0302 57
    0x401100c58142c2d000c0143d4280c0c0c103c51190070414903550b24000030302c084646050034050b2285801c05080100040b0000941d4000b04000d2b0007511070640080c0405168407003043d540d10a0b0843c20700d850740c2e00780340340d00e09100c1d04000d11034494040d008445c0c5024480e110356098140b80d9020b41e80030342c800714001209081c4000c081c0c1280310101d8401e0488092103010500203c100c04115422000315000550707004155032013003020b55009010b07140e4540c1c50710711030500b82c1c80554580d4003052030218980c0682e12604000700405900c502403059110040b6400d4401d84000c503c21128100b0404000c1550b030317010006420250316050380e40c5402c105130054502154407040040e4084c410070000c0d64508500f1000421056030309020001c130450b0010b0403500184010350045a0218103130700005074100c0006062802400c0a6010100700d0103c001300c007188500305402c40c0201c10841c0325260840480d80429544806c0e0390411003c2540402880c09120f1801841210410f042e9031090055040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 979207940 1250 979206690 979206713
    0x4050108011706160306090c0201050a050a0603080d020306041d0c011101050c0a180e0423241f08150901020c03091225183602100507 59
    0x1070549000d158042150b05090701c48000500d5094003051008450110500c40c0e0b00201c0200407106040282c0d91750081c0c028081e0000355140720b902801c3c9404a516001070f486000100ca170700dd2842894402c051541030080d402c01080541c0c447d03514404150341c03602442400441c03240510180085000050015204004140005035242e06d44420003a200010310304590361742526040c0f00c4181a1101401405080740703411505a4070707038503414030040058a8401d42e000010034241503800d40310000026541c0d00005d20081905980350860b400c0380340302c0003083c94021030490300c440d60303c0381ca004121000040a17440103100d40c2c000304110000d508012400f0381c02c01981c500962030003100c010815030340d0113640e01c0d5611401c1d551840e050590f0040024046c0290012568402c405c0c40350148095140d11303204003194642403010b029040d00e0303580700d09151303003108000c404480c0d811110400e1201481c954082145c42c01d030220a00541d07121f01c05003040130075039520702e940c0d0161882c10301c0250a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 979209190 1250 979207940 979207949
    0x1203090f08090915012304080a03021c05070b06010804152a020313270f050103031202070b181e01020309071203050706151206060e0705180d020303070510020405010801 74
    0x140340d001c40da004d6030307442200c241c40c0c042101c501d503804100c2440f56103001d02c25984520a1840b81c80109001c2540205010f19100496a060100400d80c058141c5940c0b04581000b010005001d000070007960003200810381282c05000082d100340240d115410441c0c0f8681c258140c114a12010400240f0210360100509944c4d4409075041100b8603180205041c03240c01780c410085060b03c3e031420010a0761089800043d401d040611000112000d840c0003841c1c213000540000d0300d02881c4051411030341c02116030884d0b004402c180d50360b84541400a4049041e003550115000f9034a060444d480541800032505600100041c0d0b83d060080000e0300e411b40d15440f0050b010307465042600031a401c901500d441940100011407040c051414007c00e005150b004030041c42440740c0c0c41c2060200c107500200c16901d6107080b030035480d1102101580e00e8060b40002c0350101581c02340d0345000342002030603550250b01c040c0071241046421f9030b5150400c8002d4844220036540401e080081e5a40020043d0050 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 979210440 1250 979209190 979209211
    0x1a0406050c180d050a0503160b0604060308190201152304052205011b08040605010605190c0602040504020f070507091109090709420c1203090f080909 66
    0x1001c11541e00700311940c07281c042849041c10b05030030414000180304030005130b075112090740c2d500c03000610400c50361940070509132740c80407000b400a030003824144034141c10b4940140c00c290511010703c0d000c6000383e04000121007103540f500c030500342d110000d48450b4003404025903400d14402c8209000018040c42e1203449214900300310500c02c40350040c0350202001c008031110004c0b10010340c14000c0c090407460020f07840c2030400700030401e81940e20040040c081d51107044240866661000100c41030b0080000e951040a44d030310b528103402e4040c029000c0540d00c40d02015051130754a00000c1e080780c000250080c0307441800104c210400c2428001c410103406007200c2089140d0403d2840401805910b1040d4001c0d858600843c01ca103009251001c000c0450691001040c00c0c0303122800c084001b00d54590428916508000d02c051035100f00080100000365104c03500c1c00c0641d00c5a0020311004403103072007803555454582000c10f83c044081104c05005050700307683c074000d14052110001c401462120f6a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 979211690 1250 979210440 979210447
    0x90f02090106020c0415060f080a0b09042f0a05011b050106240801030b060904210f030f0e030a052203050c01110613060518031201030615080322031a0406050c 70
    0x5523a003003040c102d81c80310103150100469888500140040c002680da00303601c01c00c0202044108541110380601c41120070180d1180b0704000c038040043e4441c0c904480d54803038140034003401154410440380100d031071141104e840011460701c419007103a03815040303003294500b201640a00c00d50903034005407404041d850f00000b030303600d0364499544045000d005240b14000e81000300f1b041c041d01e540d6041c3c007600c0d04e040d4000040c20014005c2c0c95004900b12190210b8205800044040c5440c030407400403008900240d80f0303140e00c0d11801c0380d0b40da101c0307074955000743d0340245424004513080400c0c20180d88135000a0220140782400500b40400040182c0c005610060400c01030325011410541e20650051010032a03485082c07190b109400e10f072094270340070710000ca519140301400b00786141c100d07405807404005081c0d40440004031181d1500426440740c2c8200541140a11481590301000740ca6030006002e032030312a031b64805034204004002e1003901024091000344103a91050a81200c041501c0c02e14 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 979212940 1250 979211690 979211699
    0x5090c070c06050901110d0f080901060608010e22080301091407050910050d0911120109030f0513050604080d020d02010b01020a02040e010f050f07090501020a0c0504090f02090106020c0415 83
    0x80c01e946000381410414003252181459000700108140802008241e034205810098001e0010446131245000141d00764080b0b40464418800c0100351002d42e512544c047e820060074461451018000c00d034102d1060f08020301c4252840d02c40001d0038860140d80d60780c0d501d01441c0c0002d9030380c43d602003032181c13071030318140800c198104045680310b001c150b81d011090101340d0400e40b09801411407601e44503092120351010055604000c0b041c5003c115115a0b41440e24441a400c81c2d10340c1c42e000300812044d864105816019a0281c032040002100d218116500e4602245580c0c120b503008410342d070701c581000071001b40c0504c100c1d002000148000c0001c0204200000d588901040d0080d0042d50740d5003400d200d6900a411016076528400c03002d101c4c50501c212740d088103010407076544000410300ca0700411070350310104880010a0300103880601042c20031040000070324552001b00c44d00b4450407101c00040e2a0280c081d8000c100c69000707009145150820300040c1c454482640070010541e00c070901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 979214190 1250 979212940 979212953
    0x71403030a1d04090803090a03020f0c06090d0c05100c060b030c1507060b031204050312040501200a12030c03110c070e0907030503070c03020a050108190f0f020d0605090c07 76
    0x10008042c1150b0351004801c0c0800300d4000c08242c0400740100200200f00003a04000180c0e000034288654200e60700c100040c1c5034242c030780700c40c0c800c041c2e40f041003040b501110340b0f0408040410a409452052003050303076400003c0d14005a00c0d4140c0104054158040901c5981c2c814450240402d4001e0300800d00c003000083c04060501c2244000e0310b00214100e030a02180354054048444080d04488105800c0d1201c0b41840d0064400e0760300c60300c102031000c10704254240c150303812208180c6543c003003411045203003024244080c03010401c40c1f00c4d441a030780104000042003003640801d9100041e0b54504ca0340300900b51040d181405071100002c000096005c000001d0100480c0c11840c40c40e803d07500d594034401d0505d089980090140d100102c5d07134106101701d202048003128402c40340c568045581c1c00042d207001e4000c0720703014040708514226001010064000744129000441c0000b0003542c07004440c812a0010854851a2641d554080c05142007503240c0c9074019250b1440740741040305070358484 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 979215440 1250 979214190 979214207
    0x904030801030821010b09150406090302210102071b0b0a020a020603150901090f050f090a15060521150609070c030e040c0807200d0804080403080309071403030a 71
    0x2003143c8000110b9464000d01600080c4903120513004003000e65a403001703902920b40000004074071519106074010304d039100c040c00702c9080707410540700e00d00c020f403541c0c003003140d92024903150850300d9512500240c0070810070320050415a00c500003c0f5941096002c03402020b0405410044d42c81a082020745103190300040e4507c61103604984a81e6a680d403900c01c481c21108031107030766801c240100c1c0041100e47c01a001990001c4139a04200059a10310710003139104141540c006800da0016485400440c6040529072a0b0b0072001c100441c92130754031808a001c2c2d500c54800b100040103117070743c045442c0e401409640309070035900c40c00707100504060001848a00c000780c400002c1c010380185100415024018410103d80c0044c07040064500d0404058900d40c0d0880380c1d04002045200800c01e10080c48402e2003829440c0c000501070940071190032381c1c030701c20301400640e140c1300d0510001000410100055109840000c0581610780c40c201407696422071301c8030154441e40041c00544581c96015049 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979216690 1250 979215440 979215443
    0x150106090e04051204080d0e09130807050c0901090209090a02130b0d2408062a0c1f020406180e2202040504060b030c01050f1b030d020307030c0905090403080103 71
    0x20306507542c603507180240c9006108121000000381c045000240c0c0d05012415003c02d12031fa48808502641e1b140070050140700403070701c0070380b40146030300c0e07100210b5031910142080601c10001c070f0740912000360014845580c240d1040308865000103481540c0d0500300300384c41d00180e9012041d810030205110384440480c04c1e0091401080002c11242c49c04001504804240c1c110700c1004416107a50205092906006000d00110f03845031201061300d40c003412034079001039150100740100b0000d26600d4405e003907000c14240f07800341c0b00b00f10882c2c040d80320384810004001441d480040c2e982e13241490150000c6020f900003040081114001c014041c20540340e142d1001d5101140c0c0c00241060390f480c0540140b140b8041d42052134a4204810001203030700480ca0480c0450841e100c0311080300045072903201b24031041d0741c04034050250100442031300d4102140e032002c15054074140300002124008903001114210000780d2140d01800c045608000445d005d41402c0d200580603140544003d409150117120 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 979217940 1250 979216690 979216709
    0xc020405041410111b1014040c0e0610050a0201060e09010912081608100b0309010504051009050705091305030a02150604020c031204020604180506100e10050f120c03070215010609 79
    0x246100c09600b400100c0102d5a1121b0406c8001c0c5101080d14694808560888481c4000700e80895070484030915144103010082800040c0071450f0001c0302d06030800350391a02959200c4801203800120f0709a01440b850100c0c00001d0311452504000e0b08411602d40440244021501480480b90a01c5110f030000d02c440c0c2080c102c43c1c0c171200040910500c065100141120000c0144081d480041d0080d5006900034011640b0350795198012008a0f030302c0c840010410b0f4020178040145040c41c55a2036407000c05490000d404442c9500d4041c00c1d54043e2440d0760041e00514034411490504103640781e04038006440445c02c000f082981c00e941c0f441030f0203140102005243c00502155282d004445c05003500c00160740a20b031544401c040501021340702c82d80324140000c0c86207501e52051900c0c02801500800742082c00200070419155030740a40d544400d040020080c103803000d8110780700c49025410040c0d00c00e980f442c10071002418940707110700c0710a010300c0000c0100016907121440c1d0043d0b601c842c8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 979219190 1250 979217940 979217977
    0x102180d03170712020a021c030c09090f02160c15050301050a0303030b0d050d09050109210b0a0f0212040203060912031501091d0117030703090603020a0c02040504141011 75
    0xf50709503040e61020041c0c00c802400007500d0440c075a800714105248014071440141341d0318070b13204140e0688104007a03400006d80395550800035042190424200d441610000514240d4400324458054889600a64402d10721840400001c0d59400b80100048400d1a0031800c40d4184000605d0160007844040d0825840314581c59095860b442d50003d2142c0c0315045640201251034054100c54440c4034050200b03102590006851425088514003039040407000c9000715174039500c103660000050480c05003035030358420610101d00031b4801401c010380002d004000c01e00d00303481010b107824001062088523400c0104a00003a00100003901d4201c0582c2d01407500c10300a00c0012a05400191302c40c00c25a518610700e01074150603680c03028107803000d00c1960381f0b84c150a00800c550301d00c110000200081c456020402c00f0520950290101c10710b10310740b81c02d0100c0c1a07000101600e03130581d0240c841c2c6061460020b05040300b008850000c0003006018400170488444c01d4840340244800ca00c0400c00f0744 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 979220440 1250 979219190 979219201
    0x31602011503031e0804080901230705070e090307050601030b070e0310020901261501030b03100c2601140307031a22050d0e06040b0c0102180d0317 65
    0x1e40008525503416180009030596a09004044e4142e0300e03041042d400b0691450342d402ca215000c51440349400514180c60b04903a20300454192368020320380e40000d84851300c403203883c845810007820028051001000003605103118400149006001c99580d640304000060004030f000c01d15a0440350480391105240c1e940302011340784c3c90707040c0700525494004c10400d183d84a11641c042c003207e41080e03960130844559140c605101c80381c1c0000d54180100c03081c0000e64480703100c00d00c141170901c0614010070600c04400200c2e11f001c0c106550b44c0005030302e405015901941c480300c40807000c040a0700165408070070f803401ca501d03440180206001c4400c41d000c84949030f181040103100079944400401409186d80280150040d01515a00c031810000340a003a1000c555410799a6840e4001c0080c00490380e609609840c845424440d4503040318003800700140e0900308401070440800c03260b002591b02c015051030b1000c01200c681109118900740400340002c00d60040b001915621545200c4409071200c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 979221690 1250 979220440 979220443
    0xa0501180b0a0e0309060f0315096103151208071e050723040926121e06060a050403120e030f06010819080c070f03140111031602 57
    0x10b040e02240c000d0b8001540074001803085002303620030b0540c01c0c0030701ca81c1090074081042c0c80900351551034492041d03804245801c20510340060054909289594401d0070a50713000c581449c210305105000c07a031340307898070f044c107c4503400f00d10210095140c1042604040300384912036032590302031150055041a4103c081001c43c03022240340c2070304803800c00c440340341e503044c0c00c0302c1100c008100b150316000d800e03400030710f10f20324550641801d01c0c1d411403c0504682c10050000408103070805481541003102d1940e1401c242280d00b03015407001400c2c141da14044500160b902d00750141202040c044182c64070303405010061100d0340c204000325515951101c000e50704459500070340c0c0000c0d180640f4003104102d5103400040760002440150b00380c50100110717600c616141d401c2486048150741000242003901c03c00400c01041d1540719404150504181081d91307482c10641d88c004107000500030b1014800d001c6074800c400c0c10b94800000a02c035440c0f05011110440c0030103440c0501d45031124010707101c035600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 979222940 1250 979221690 979221697
    0x303050d200f0a022404060c1701060503071107080d030203040c0315051b0a0c081b060a060914090325021309030f11060c130510020a0501180b0a0e03 66
    0x4005221510790354608462400d40c3e01869001e0003510a14074001c10400301c001c40c189100d06840301c403d40d26501e40d1244009441001240c0040051050782d421503403014081d814041d001c182d0b21652649090301016005110010047d0000d03884480104040400040d030614566401d10380540c4a4a076858030b14005140e03500010302115070301007400009000c07036004c1e42c8a4510b81c2d002c0c442c000c80c0c80840f050240f09001400e4006551100000082403042c402400c14481c102038100600741b0402c616070400750161029006240c036130302d0402c4010041d02519545c450401c0b80451281400d00040c1e80c2ca10409032082611040c00f000d87e040c00720714840d82c02480350003810340d4007003d051200041c020981c00000300d01241040201c2440b06204005204044513510020300c804d440390241645150410110b20404840441e00810b0369100e040071000c0d0110103070000d200f040b815203080307420340d8401c1c05159801d50000450501140d0580016500300e241c0c0c010010f0410300800c0c0d42c038203610 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 979224190 1250 979222940 979222991
    0x612010b0d0612060c020d0512041101050c30280509041a0a0803040f0909050307060603080a08011d060d05100221060301110901110c030d030221010303050d 69
    0x700480d8070360013402015001032156140e60380c281c8011004141c401d41e010701030044d901440c241c00c03e000a00058013220700302e80c42e9405041c5203042c8904040c5407803910742554805000b11120b0702c808050040d40c0340c2c44402c540c068441060038485c03040118048001c0810660000140002426401034017501c100c5441c10805801400b4036058800c1c80704000742c401c200316005010003031000403240008000e881c00e843c3d94441c41c5440034a0040e407200900750072181a221030200300003e8000400360310031000214482c0702200d4862052910240c0b640c0e205900280c1c4150b0b0b07150314900e04294034000a0713802502121074945020b81410021725101d29a5a0054414800216100c002c0b20a046440c42541f961064078090b40d110402e040c00d83c6d05401e40200c420350281700b620321941c01080300c0d8058810081c100d03403564056800180c41e001500045034042607000400003e1841482c0300807038880901006d00c2002c0d450b45d680107000b845000039001e011a0b0320f005030006050516491150709 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 979225440 1250 979224190 979224209
    0x50123090f0f1515041e0b0415050f040608160309020102190312060f0f0518040602091207180605030a023105090f0708061003080f04090207060605040b0612010b0d06 73
    0x1c1040e068207040d60311a0044510308299022010381b442c00d40000c00007503800d00e10249003054900071800c6800d04041245001b0710074103101070096a10102d018000912196541014604250f40f21504448211210100701400d0041c40c2c40940d070001040959551702000407117001e202ca00301158410081d41900300481e0070f24000080a07842151208141e9030002180213440355644200314103031207152494018401c002c1c0010340440c0003a07014240c4100050104102c08684903140ba0520341c043d04540c11a0340c00340d8510150100304d01ca8800602010303002404110790940000d569a6103120b600050b04185001080580042443d210a11000c2010500c00d80c20300e181d010780c8400742ca07111010140314015000410220010301c8030301500c0b441314200d040740c0c1503440c0c1e50071a1780410080d04d4030100401002980310660320003800f803240103404c0010000e0500042000742c4520040440c810141849100c051120580c4c042d811208109a00c50303031160801502c0014110036400b42622 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 979226690 1250 979225440 979225459
    0x106051e03060121270302060a0f06030b010303051e04141201020c0123070906050a230d0506030c090c090d0501061e150804170c10050123090f0f15 65
    0xb030422540041c00e50348418040284000b41180d917562280031078090180042c0e028038007041e1002e881d07a00030030041c051000c000c43c01989940b10348140c040203034800c800045000891001e542c11101e4074442c3d484254840d07515280c50184030344018240c082e503141c46140c2d2911105030303080c2c003581180c640d82da80740000d00002c5411300707448404008956200001092039800680c50901c22040882980d0031622180c0c01c00c0e03450b034012564610347d200c4115003d13000a202205204082c0f002e4040304694400c08a154500b520a041c209091092107500039001103040c4a480d921703d80c10b48800d2027041d64221011443d904100b4003400c101e500002c000313000d25212803980c1c5507641c000d405481841c0560444550f01030012941e08004550184c829018406c20f158020840350040c0b043c04160f0088400e00c810680d1540f0481d0003e03030082d802c41e4854140d014180e42d000300140344000080f609030302186400c01490b0800180104003000c8000110001000c040b4100c04c1400f002502074000c0e143e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 979227940 1250 979226690 979226747
    0x160f090b0a03031b0b13030e040b0a0b0a112a010314060411040e01090203040203060708060a090f020c0d0e15040f0e0402010c05030a0518091614040518040b0106051e030601 76
    0x74100c0c0728a20550000e9820023511086003002e0240c4c0514000c0504908480c80c50604c90706510340204030801c041014101c0f00d0000458104044070144040075404286007500118498100c0000c046180c141420080358005002007d0b0b180e5a200405032008507075400001001382c090f01c40d541040b4070341d0034a8070001c1140e810301d5000d1442a4030a07000c89c1d24070b40322060152000700c421207043c0c0c0d01140c0340c882408105000d401c022401c401300c1c507025091a40c01c4c01510300340658040010001058410b8000a61a000c0c00035900c0013811508140b03494100003a808204940c0d004040c0756030300d100301080031644580940501d003500308082e2070b11908500c400a01903480400d00c0203c611201c1c40390043c91621071001d5000f58001381007000c448107a04c000303a44107040600300050500041c00b0000d5545c542d4110142d46500358540070001d4905480e00000c44501a0414410024180a4881c1c3d07a0340000fa8802c3c2e0441e0f5000c0d841d242d50b5940c0041380c8200300703900894102c200414a001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 979229190 1250 979227940 979227961
    0x1101140405030d061a04124d09160c050307030c12090501080403030b0a17031b010501052409120a0501060501030c17060f03160f090b0a03031b0b 64
    0x1c1c00c800400140580ca03a907012403001e0f68050040c405c0c4844007000108000110090700c100083e10620303442400d035004684511300d54a4081205c02180c444800803101c090b01d080c200c07402101145501495030300c8071000300d003900c1c2c0c00501d0b40018400c155040003945008640c0441c02e107a2040860b5580c07807140c0b6008184840c00213007103a11900c201424400140078201f90001d40c5c070103075035a00150303869403422005089030805180c0c01125407140441c00e10302c90074201841d045848015562001d0400c2c43c21100c84098000440c2d507450400103214959030600c50481d50b508005841c1d50074141601d0041140c821741205541c0038802d003000c4404000c0205450301c0d100d01440013017001d1690f0710015825614101d1604c8001740032004400d0b080d01c0071909085d0092000b4081004502e01180804e141001c5c00001780c1040300c00840c104011015000c80001400340614140700c41d041040208050b01d1079400300609019551203412071581d69401e8041056030040c031581c07590308140ca00603 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 979230440 1250 979229190 979229197
    0xc011d030a020c010201050f040b13060e0a1401050c040308030c1303060615020106030206040519030605090f0d140d0509030910120609050603060f06011407120f031b110114040503 79
    0x41d025003c0d04a908680390b0041c0b0030301e4494001e48403080c8560b600c507903d20200311401020060410340b11146034005c0394041c4079403407014800c07070010300c5045002d08001943d080c0c2c0c40c88110302681003004102c06810b0f00010346c0c1c201c17540424650b45035240c0b03180c0d20740180100780600300e071003510701400010702407140c1145044407041169801d001d42850f400701c0c03c1e02c096000103500708038100301c20040380c1050100803401c400d0500082800035100d40c9d0390300584000f41c40e03802c0035502190280030190700600035268000c15a0034540c01880716034049617594003803401e002003250f5940000460028050007183e141e0b00005103a8114072811450240a42c0790341400407504a1038030301c1c0407a0200301480303494010a4014028212a41c0da14540c211500009001c0d5041001801346521808071540c064030f40075200c0c00b50344120304900b100061101610900344002c050401040b0000c0101d02d0940d020800e18030310300f074640000d1150f41c06001d015120003402d8061141002c1006004001c00907 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 979231690 1250 979230440 979230457
    0x718052d070323010317070203010908040f060512070c020d080d0e0d110c0405041719080a02090d031116060806090718090513020907030b1219080c011d03 68
    0x10416450a004900142100c100120034440c0c0d0f801c0050000c110795041e1244d000c0d04521200e440d081665000c00d0946031502012108e03910049400d0143d5040e20a03020090003c900d0030300c0c01e10352881550840310f5000780c5a03074140f102518084065464044501c0303011500302c1045940e5054401125009080d0f4991856003401080000a0100d209840d0b04003009410740c01803c52190074002c11004041c050021690f440d115445035144d40c04d0303180603020000b048408001801d942c541c015011130401404062514410810700f0000d0b5242d28540207041c2d00761078480102190354100d1071928601903040711421015400015a0070b03070113a407141c411201940c140b0b929443d00001665071449010b101410a90016400c3c4040d034550750125502c003030b00040f00c004180d01900860400c0c1c1094980000181d2203192170a40d605001d0181d1546805900050aa2b08050740705010307031100c0182c008040b240000381e803400740242500410f100203a41d4142040e0b13252013049081c0d40368002c007030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 979232940 1250 979231690 979231697
    0x120d0b0607050d0822080c010e0619140408040e100302060c0a020f030715051e040e0103052e110c01060816150207121506080303070e030718052d07 65
    0x954482855040340480e041707051060035030301c8140d03070344020503040002c00721090340d600d000941190104101082c00f2310040302c0c500a040c0c1f4540d081e001a20023414202207610020402e010018114008941c2223425011b002d10694031201c005040c1c8400e2648080d522000104054030618401308102242c0392007101e400720005101001e1548609240c0304402400e5411030380c00d05010700030f40003000c4206a00803080041050440800c0454205800560711000400014410072008110601c540269002054103e9283d55040060056418180d003411510b07440c0c41480007040c503055800c9044003030300074061507031100c151075510303003d41380084c88400c07284800240740107140c0d007144000d0210764054800c05080c103440100c40c00000c003044a00c3c00f00540c0d000c942007950700c42c030742c06080503c01440c2e036402c01e080010b02c800c1c480b0041a00c0fa0b0404003003040b0765a82d00401001e108104031010030342e95211300d1040d090504400180d41c02a42c00c0031202c00c41030109009a119050644 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 979234190 1250 979232940 979232957
    0x7090f060801090f0803090f100603140303660a0507030315150e03010b03030c0c0f0109080a0c150807020c010e040f0c120606030203040302120d0b0607050d 69
    0x24007a820f035103152401410b0130303022625403800300e1440c50080d54801489011030b0340d4110007520b8240780456131030882c044141d445100b0301c10032500f05011840001c07290015402c50030021140c9a11000150a0407034400d034144182142030441c00d8442c6110300715481105040b0038403640e0125004031140031044424900b128041001000c1e02580c1c01050a43c0c1c6003400e203195580d064000703000c294200c001c094080d820010340b00c0460103605501e45070a68a0302c000c20b6040c2c0602d42503c403d030381524802d070418230005440034000110f4410701d07c02281c103c1c404040c0400140c0d408685500702ea0b4441c007580310200b041c4850011441c0c104c1c0d00502c82d0000098803a8800c49120750281d4056006030000c4d100d4181d04e40c81600001a41c0e2401400001c0b80310321900d28000709c1d1060a4020701207052401222003d0103944140c1b00100314608041d45180b600b80c1d0700035151004514a4070310018045550f5000c00003c0e403001c808a400075001d59501c5840e401c00c5966248490311460006c0c00c843d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 979235440 1250 979234190 979234199
    0x60803070b0703060b0d051005040e010b0907020624120307080a0e010e0a030803070315060c1412031801060f090f150501022e05040c0e07090602070b0f0c07090f06 72
    0x280718130b07412150007084103814495000640d901a00c0054610310046034540e002140310303516846901d8a0120322030002800380e10300c00c03c0c02060040204140d00b0b5400001c104070003088100c00840100c01c003500031201c0c82016000184903c1c1d480380c5680c11510020030300f0020412840000c11040b040e0345c90f41c0010b020408011956040c0346030b10b44c1e810040c54081040014040400f03550009c00030b05000c54582e420002e42e420700c0740ca41d4440c000140502e00c0c04401c0c807801040a01540d402400605000174601c0b8480c0100e110203007102c8010308045640c140209001e51006010308028800d80c40074030707982e043c0040648840d00032119028a001e16103200e401208070010b04650042c3c000c0c001c18030358141c6d5001d0ba040111001d2020079801081d00c081000c17a0300c2070324851442514814881420050801200c140082888040c0003100b0000d202d030a0700043c0c0d80046580c0c402c00190355100c10441001d0900950304800994442d5000100354104150402d59003181791107000c00485940303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 979236690 1250 979235440 979235447
    0x80709020a05070807030e041103191503020f21010b0a12030905040209010507050601030b0417031e0403030906050f0a150b0d1a0d05010507080114220609060803070b07 74
    0xc041030180070400402004001907130302800f40442502030f050850b40d01030200b02003000d641d08242e1500c00200b0010800c140780780440d04901c40c98242d00b0042285041c000525240008240401b80c07280140000c07206036544d034103900d0303442000601041480b8919923500746000e0040611118030400c111000820ba00c0c40d81880d1440098050340c851060a2a20017884001c1d88041105030400900700448004135030308002040c02144210701207815072030982844030030744c000301d0714125400a0402c144080d0317a603480200d42e1462000c0aa094160b252454142c00802c8401030050400d404c06041003905030100100e030344282142d8105015024903141c04d24007006450165122240c800d200c4d1201d0030005611150303a641754406041070981850000a00c19aa403d4089809a460300c0402c608180d1010748140140b0800c14040c0c000751040700042d0301e040c0402c51640c4451400f50810542c02680c0c1c00590080000784010880d59407500b440030746a9010502c251400d50904001c100300030b22 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 979237940 1250 979236690 979236697
    0x80a050f12120411040e030408070306110f1206040207020d031808030c1b0a1e21030e0103020306030a0c0b0a081005010c12020a050d050c1515061303050d080108070902 74
    0xc55444102c441d0765030341d2030040d03108013a007402d900b082d03491560000e07501d81080140090312061000b8140711346145424029a552032012a2007640b0030301982d5410001701041c1c40071100f502d00c000610355076000114000b402174800103540070291042840c20305801c5483e113014001d00c94518191191600034007503070f1b442100600300450b0b02800e580880365040380359140060200034106070707160727a84003218507840c041c0c2200c1c0381c050490404200404001d840440d03c40717103881e00f003851341c41034039880140c00704010512007418140c001001a400365801e00c0860380042d480030b00c03001450380701c200d0001150007070003001010030207600215018080d03008101044a00581d01c03400302442d40e0351000800d40c9013169020652081c0201c51001a500703000240c42d11110340d6a0944400b14802580d00c2c24401e82103081d960340f2403005000006110714070084407030078283c40080e59003007610f02c0c1c080c8241090740082c0860140185d503a070720307079030140304141260750340c0c0704459400e41c0342c8680c10220f12 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 979239190 1250 979237940 979237957
    0x3120e060a1412010905010611070803190e030d0302030702010b01030504050d110a15410c0702120a0515070906140f031e0c0403110402090307080a050f12 68
    0x11041c030003105072620682150144582d448100e0b42401d22503c1a44005802a08404900d40c2c030758005011440d071041000c5004100d101c020244640303404156912031088004040d911405140c05600c0789018107a954840880174080386c0454191580090080d041a600c41c00154280400600c03590300c2401020b0003103030000f0251940541c2250241c94404504601144501403e18400049600810070f01e2604201030004100711640e10b42c800700c61807007061040140b429040c6004000e044106645008028800c2e11000507200c444c1c500340280106c540081d070258019115a501d040041807140c0303224400e008642140760a50780b00094407204a9010001805143c0c0c104260340c410b010106282d54450340070791410440c01e00b405000d41c0100c44400242e1580418450003081d001c8400741e00034006c94070a0704050640c1d9071848001c820350b40b92403180707402003200503440c3e4040c040c0c00d006000724401c807000703040d072440e1940d100c0c0f81d0b08000301e646000b541c0d05545d00e266030304115000c14 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 979240440 1250 979239190 979239199
    0x606040b030c060912030d060f440a11090901020a05030f060a12110102060108010e1b06131206060905040b0601050a020c0a0803040e0a02070206070f170d0603120e 72
    0x10403240042c08802e400c00d0a84c554002080500748407980b006000806222a40c00400b107a41810300898419911030340d400f88105425400c0385032a00c200381d0300c1c442011500000c0c4401e81246103030051002d00680c12042103035005403c25281001020f2190800c40320781070711040ca45a80b0304c80c5140c00c0b0301070b10a607a000b04500b00006441440c0c01c2010641c0003c0090110f0b400a031a486080300c0343d4400c1030102d07148058070384403076201e41c1c04010540c01040107400030301c014442010f8050300c900f0303859190001280d2881380c000c5190b4415003a10510030040c6414000d1682c1d66202454622480b0005d4a00519019000c5200000e0703005a510846d0000018905610340d040110740c03550102070a1421030060411608042c3c1d01c0c00c0300d42c4000c02400e00103544441c00c20003507c40440024204e0192140b0402c07002d40180c49940641c0c8410303411010081c1f041840e03003031a80b2a072502d40520300c2d140a000900c60000c848030b82c402d1301904d004100b440581101e1304400d0302e030800e0031417840794003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 979241690 1250 979240440 979240453
    0xe030a020a031206150c030e19060f1119151406060304081e0309101802101b0309090b0415090e0109150b040b031204030803180d020601080606040b03 66
    0x2c03d00039051200a1407070803100094640d607840b44403000422000203100041c004080b51010f060f8072220810404c0000c4640d5212200120052031180c5c902d44104024480c1280c40c0c0e102441c061281ca682c2d818400003a42d40022044100e0001c1506912080780c02c541c81c1401c005610245100300078013138002c1844d288250321071b04200040f07504024401c6030702c2d11040103070240c01141c1e400b45040250710a20003a0b1a4181048041d09080030345040c1c15207030386081c40f60440145d80c45122954140c040d02c40c0300a0a000f8017089403000003d0000d0310380702d885140e000c1d0406a01101340c03411100089010440105c8010400082c3d441410101d8083d801c0c8010034414400d05500011540242034000544601166105205080032184601484d030366a40e000e00d1505103030003491000b03001200606008000601310014500072800302502090011002800451b03902e080400001140d500310391040340040c03402542d0300024001c040403401171601080940c140323805503c2140b003008014114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 979242940 1250 979241690 979241693
    0x5030a020315060c0a022112071a09030a030f0b03030711010302041206020415140a180b16060e07061d04140108061605071e0f1203020c010e030a020a 66
    0xe5000602444a154421403801419070303554030080505860680207002c08a0701e80c0100f00750300c0c0c01f48840180720000081039001450010910200c403144c83c10390321741c444015050030001c10b00032400001008540805000e031400c400005081401e103595014010322554440140543d074200040b80d825a2090107a500007034101820b0313a084000600d0014145540c1d60460702c403141c10f000003520070710b500144c1486404490940c19090104900780040e0f852100441a1820b12070540c180302042841a00152000904100c040080040c1d0004d291180c28003401e1030141070440d5022150a803500c0385015003040089441e1040b208a0b0b1140b540c1240d03e491042c1d00750494811a03a8019a202500003501400400550107002400000d210514002d1a00c400c1c0509a0802d102441824041d050003d007014012515840420402070403482c41c915080f420301246080003070810f071151460748600c55050b0301901d0030026a400a121001914004d0f9861b84100d540440041e00808105e10 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 979244190 1250 979242940 979242961
    0x4090f0c1728060f09090c062a080d051003020a1a090d060e0f0307080f0a030b100201022205060304060b13020c010204140f131a0406080a02010f0f0503 67
    0x40e441801c044000006482d0940e124071580030b188084400e040c1d6910080c815906055120400351259900030826a10a92038440501080c0c0c80f4030360402c880340c0350300044e18001000884101c3c6035510180c03a13006940c503100d440c503082000700104542c5808006841c0030100e80521048039009020140800d0812040440d810807003442214000f07810032110840d07481e43c0c003032024600c4c020840000c41c5102e2208060070314640c52075816a0343c1c000d002c42400b050032241140d0b05084030704103c0340c3d10340403444180c1c003420341c3d01ea8443d800105820aa00da60f50190000c1085040034203000e45038010003031410310750300d225020301c03074010b4010310004000404561045030440e80060042c4618181800020241d910001c07034400d050350003140c1000710500d24150200411400c4400b44e91505045c000300d44620080d00005c01520b488603090070380e4001c0c01902ca514640080d0081c428a034841d500ba076031380c2e506108205e001804c0164840085442614644100d00040d40ca03035246450305171400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 979245440 1250 979244190 979244237
    0x1409070807030f092102120c0d0302091302270a14090a0e0a150b0609010c0b04080426070801140a0509100f050604050a020c0304300804090f0c 63
    0x1e0a0307035941d4081040031a040882030800070b24105000194030a02d041d00904040b09481d010303a0255048c0023000005c4404104900b4800041c074005860b03246450004609030302108a010b03000d807001800d0240c1e80e0140c4076904c00751082e101e40403c10702541c410322402d24910700c6040c290100c0b90340c85040170314010b5041d9801010580c0c0101e4110070700102d1b02e0802401c42012aa0414164840b40e2400010f006982140030121780141c100038031100003804109075800000c060313841c00d400040c1080340380c00544018100403107200c1880086455004ca01c5592418040c1c43c1c2c0c4103074140050201414010a009442c0016007942d07261603440c80900a00405070440659010381c0302200c02c503050501c0b030801d2500c800c22000c11241000010702c402c81d01c0240c18558100c1c0100320801400c0030000c12a012a4090004079203442c601c4a448125100042178004852921896000500241e180944180ca409141c01c01084041e0010030f030850380c055243d032010881c5044180c13002040090ba4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 979246690 1250 979245440 979245461
    0xa14060f15040803030708041101080601050313052b090e040c030f15052e03031e020703020d03020601060f0819021c0c0333090203040807050307050601140907080703 73
    0x150707400d042d22898010300715002268074400055113041080306002000200c0c0400000c2801d0090081c209140001d22601c4000c01d00f00c0c4843d600704141007080710030041e145242c2c05481c00c84680d900b5142d107810102c00c48a80c1e1600250500001066091143c1071003800344c2c0d0300090051820345940c0d00c0d2021144c20343c0d010b0314040394000c4603200040544c081c0d142300b844000038101c07406c441410545102d01544010b008082962542840000d0b0840d030003aa40f9108600380b03084000421004a10f07050103030300000d4106035615500d00425400003a2207042e16500d8850700603900c85894215100b81003103640305030791443c07a00089464100e6600401210007011700d0305c503488200a02c0b5505071200b00311620b0010766500e402d5500c8810113141102c50f4443c0b8010400400c601a00d541c202504900035244800d60000215080240d5042151081070344034060780d0300c4d0522403d140351109000d02c030f0204005064501500d2528240e00028403c05003a29149a26240c06030708034000e1989104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 979247940 1250 979246690 979246729
    0x150c030b0303041e0f0306051006030c120203060d15152c0403050d020c070806011527150513060c050303150103291f0c17040f0e0a14060f 61
    0x200401c8402c1d45c04c420001030350050300080b07083d0801074000d401080d0158050002c0514246001902c294490106059250440c86c00740e00c81d10340c040080c000480c030a200034050303101c0c220400f1107001584c0114204252071520495495903034101c18140215600803401c00000b04c00c2d8454504c0c503a40c44c0180c00a0003131400a05200004403440106e81c0301100758282503000e09402c12500e07004100303d070301400881d0300c0c42e40d20805c0030b4005021005a03884001c6690700341e501d00e405000aa25594000349078000b0b07a000b80c403140c440d000d00541d000c40424446a01c03081404910706000d50700f13629410351300c84011403650fa600c814415142e00a013a40ba410503440700e00580c02e204041c03520110741c40080d44103c0186401c80200507039601100420500c3d500d22034130f00c40300d43c0d0700042414000c1e5004240c50034005420b0520701d00b18442c0d900700038104900d844001c0348a039422005503110340600740e0301b004417500400c04200c3c240000c035800340e0710480ca8045245c0b00d0803c0145c0030864100000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 979249190 1250 979247940 979247999
    0x130b0f0909150907260705010201022119090c06030e071d100b040b0903011409070b0304030c0209040c0821090609011b0302060613091115070b04150c030b030304 71
    0x75400303001c0508000044464200c1c1c034988680303085e0500100001381800d00013185450714403004034001c100f04c4c0c400030250055083c0040c4100c3c13545503240b00f56600300c2108024001c11032400c40d5010500b402103500180c6000414010f41c400050702e00b06981000900030400c0c0d044503c140d171140d600814114101c901132100180c8401c14a01410140802c10000380d01e03210b50005040c21a10144611603841c00c99000b0310548107008a0808155821075551035a250f5590409403440d00110100a402c030212400f088203000b4010718480a071a03005007603034401c52603010a080070104805803445100010409c90b006031400d0300051503c10b074181070000d541800e0020004220000340c1c1d040d0b015810000400ca01e40c0b4050440c020303c0510402c00b088500e50546400ca002c5ca072101101d4000e400341c0c0007103010050500c0c1039514095001c00405400d2400d4a011190200c1c10080c090702c0302d00344118000d109010b03006048080c80060001c40c1064540580b0300e1040810350000003801d043c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 979250440 1250 979249190 979249199
    0x90607020103200307020f1b0943020c030d0806030f060a0b0f0a06080c0913180b13030c0b0703111204030e06030f070815130b0f0909150907 62
    0x2d603d0541246100c0c12598a070f2421981c00380c05c085c17400440249541206020101208a45903030340c1e040c0009aa480d6910307510f20360b00c110703481100c03400b1104205400d810000000c1d90003206070051400e11070400b00c898115801640c0c1c800c1c1c0c01005550542002c502510040e1180766101e40c020001011034200544070210b040c1804429103907051451307200d6007006400d0500c0e000100b4101c50070380d2a070414502c1d080000b0055000909500703100180061700d49025940d01c2a5404600749641042000c246102c5000c90f2419040718111003000310350703001450700324003a0840d0307c0e1540c0640718580080c12542c0c030320b0f901c0d0320300400c80341c141562084951070783c20118001e0700d652180f0344030021441c1454140a09240013890241d0f20401c02002040300300c05054120b913030070070b055040040151321020303c00c0a105c448000c0c081d4120707400c0f1200a03284007042d080100c0b41403050b540c0c403040318244c0d42070100c40304040b40c90103000da100451240c81300903021500c69219012100b030740c1259849 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 979251690 1250 979250440 979250471
    0x30c011d0d021c050f0606010503060904060e100e030304050c0411090f15030103300f0e1305070201090b060613120c05030d0801050907031518151e1a090607020103 72
    0xe18400d80740d45d842980180e0032000c0030044990000c0c02424224154608040080d40014000b00b0041c06039441d15a00b084002c0c04116074004190085010b225005014401c4d990b2070300221030940f0544125506001d05080c00d2140c0c2914026001303000340342001c103105000301c3c00b456013885900b14002116066169410302c1c00756028603c03030109001c00d88100780761040c1420200d0001c80c1c0e00c5200d00800c0800a403c0b01146000c115203051803201c26011a000403089801c3d240540703800c9092204001c0140e034103500c00d800052080900d0030042d00d500040c4002400307084410b0b101d00c111214180000c41c0010009503106120b910324884554035000032905112400f42e4510115800340c0c0140b0091802000841d030056252034100107010741c08005040c01070541c4107444d503440400e200d4105010503604848810b001e4614140115983e40e14202c500d40d919040182048116890200b0520782d8005c02c10b204c0202d0942c3c3d5130070080785808005141d48110001c9050503520028245900c59 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 979252940 1250 979251690 979251739
    0x90302100204290c0a0303050402030f06100501030e0c060d0b0d0503120a1b0917030c0f1c020a030e01080c0706050406091509032102090d080405030c011d0d02 70
    0x18483c1c08012407201c20090b10141103459846030480032000d11841914a00015100e800245c0620307011981e0740356400031908184240e003000d2914014502044a4500300341074201c01c0b04c20a98081100b4801c51300c405840e0303145001c0103944030004015004210966802501700c0c40c200501080d041d41540d43c9031031035548841c0303000d4010041901001160748952040119041264080d10680610b04070001e01c2e10800d8007856041c1801408030501401c020026100ea40c1e0307400d001c803840300c5018642c182c1d030350011034100341b85040700030744081c1c500d0301c00700356040e0040d455259103501402400054802a0f40142044800034052010030b012400a010b150301a0b03008981c0041c103c0ca460030200c4042e180c01e001e01c05600e0030030740350364006a88200f14214942030060180c020184503600000039100301001d00d540030151a8100041c048a440104203c0d10118101d07010b443c0c6100041d102e0440343c500780c00201d44112410859805d0401e42c442d0f22b41c1c0b00502c41c14008070b0700c0c0281d080070507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 979254190 1250 979252940 979252949
    0xc06010308490603020d020918011d0d090308250b04120305060321030903130806070306090c09031b0902160510062106090b040f0b0604110904090302100204 69
    0x1514855000000c0880c2c0368051100120b0302c030901560742141c0100e4425216544000e004881150014040003031040ca103881042c41c08000380a10001000d0300140021424101c04d414040c02c11080b1005010790715042c02c4aa0284102d4103200f400c42d01409146044001ca403038a070180010300e000141c1441e0202e110b244256203070940c145030b44400400310b9170002c1034103000e6444500e00015403800c0c4000c41c111402c50319800c603641e503070b0000c500b0300314014030030b8158021480d05404204603901107400b0388602c9440da010013107180c0c5d4400031400c0e50f42d0000745201080c0e00040500100300c00e02a114101307041e9101203200315030740e003210030b080307a11075a000303914005901610410040148010000085c1b940c109101103800c000c2900120030f0b03031001d11041d90940450a90800055420800c2000d81145000f00e640c980340c1400098420440411904844005c00080940c5040e00c02c035201c41c10100c40d01400c00c9620014000140000340c1c01340c3c15480b441a80f034002c88500e00082003c0c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 979255440 1250 979254190 979254277
    0xb130206070812100602060606130504090c0e0a05070f1202120901330b03090703080a080601120509061611120d0b0a1202060a090b03040506010e010b0c06010308 71
    0x1a54030b0070b1000803d040103400f400f4208031803102082030590004045411030b0f0100c1d10310355120700505040305002181c3d801a13400c141001c64500a0149140d8400100c4480c40035200545e030340d405005c012694126032000200d9004820401e00c01d200d01c03000d09000d40c088500600d003000000900111100485894071a80c0d12480c0e088800704e100203d1072103030b00308440b04421040055801c4a885451402007503c242800300c002440824108000001950031000713071540c501c0c51300d400906248049664601250070f400821403142a1032240070301c60000d00029040301d40359018080c5149100000c00d20421200080070140d495003072000341100584d5502080c0d80d0700440007144181c90001c02058031030702c00c00c06d081045120015800070391035811283c10b90346c2c402191003621465010380003940d00f40d4000c02003104000002a48505944601c01c002c5016031b41e400b415012403084010000c025008500100002070810001c0c10054080300e4002203043c01c4d04071260080d01d407040180368030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 979256690 1250 979255440 979255447
    0x512040c1701090b130203030906040b07060b1f142208011a030a080d0609050403030b04060b03011401031a0d0515070f0e0603090a06050109020a09050603130b1302060708 75
    0x441088016401184440500070f2280c080305403210110500c00400d0040b008041e8455141195000e0040b609a1080141050380300d81e01c0d00090852034100582c11100035140ca04008210f14000954030f80c184220002200c01007141802194420014422040c05c00c0c0280640600b0000400b00c55400943d0207000b001128a40303c409425188030030090300900c41c0480b152036481e14041001044d558206900540c0c52240b00e140900410031603210581d018509405c0c84201507054201c0b00b07550204072000e20180b41c42d101d090f51148804c3c4901c4448120b02c0f0300c8010154041d412030900203200e0810a41c000380410f0100310300000b5074070101c40a4010701c070f42840040d61142080d400804929103d44400e40e94000605110704000f50030b0b1080c1000b10014021481c108145900154004402d21840d41d5402540c2e019400c2900d1000c040b80f1030910100382c50524509403840707402c28040039a80c1400b1900c90b6020003d0242c422002c0e810306540b0b00c00540c850600030b000f010710031800f4507030703 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 979257940 1250 979256690 979256699
    0x30f0905010e213f190b1e15070c0303020d020d030e03040905090c041e1107080d11040e0412030501120b041e0501060b0406081003150c0512040c 64
    0x110521040f0700c60803908041c40300d03102006100010300305a015081d0f00100000355010550641c8a40c804181d442c0c60240007000146120360301580030f07140170090184038680300a02081a03003d4a50340800800c6510307200e9541e50b160510b040c41c1c0715403800f026145000425201e0001e04402a0419005a84101030000200f58104002c140384e0f41d0038a010481d00f40025600c684a11585c8980402e054070741c2c01040050400340402035038000014010068a8075a1902e070069008068004040b28501f444020401c02e2a00c00c450905038000c0c095851303c0200203504000b440d80001400c0400003d00002c00ca0080b58658030b80100d0041801640c8a14015401010707184140c001c05d000c034542d100604005074004209681040c0c2c0031007410044942014583da0101082001030425800c10800180c50200754005000703881030707617a0b14016540d4100402400c50100e100060225851101401441d00745034040c161720840c51503c145090407003c107080740d0500582d0140c0e80c86000760800c00c07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 979259190 1250 979257940 979257973
    0x30a1407021f021b06090c01111b300d0f02071a0a020a39030b04110301111c0506100f03020309100603080c0f120a0e0f03010c1d0402090a0303030f0905010e 69
    0x242076a150780100b41c41025040b607002b48446041e080b5019405428005105802100380c174028286011440e8400700d01d520103c07992400e94201407404541e800314600c01c15403001c100b040540e50703804081d116a80414441d1a50703507000b0310b00401140980c510200018000098800c4100807103a200105005820003700303500303040040140d00556451002c10019810740102039002d03030440400d891508d0304101081c0580588a05020034107000901d62070608038541c080c1e801041181030420070369843e001448464280038843c040851030310030050590314420340046501c80c04030411b403650740e10107004e40030645034036030400c9814140105080449d07110130041c1c408d8070f481c240c00400035401140003a00c0c29228040030401080700c2c0780001e031041e4807a900b501600220140080002050300c035001080c1c071044840b5a45400100441c010706864a0b000b07488508030300903c24071130039107155410b4004141100e8519034103600c646410000c16820b2044658100c0d521014140d4402e0100840 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 979260440 1250 979259190 979259207
    0x3408040e04110d0308072607020f15040f02091504090303230106140a021e0606030d0212040e1504091b1212140c03030a1407021f021b06090c01 63
    0xc0d02409000b200f180103c0d80c40f003922034000359035003030488600e04103440110424045c0b02c42c40c01440046400c0c01071103580020310440d04d14000d03080c0e5445400192102c1c00001e01614080c0904e51411000c07400b5203440000540c000b03090440e8004950310890200e003e4502c440020383c042581c1c3c10070307000c000501c420b08000d900800e00c2c203014a0340c140a80a848102c05036003030242110701084030f50010340204201084007941c00d03040003505103402d45590f5107600841d2298042e0140f0755401480d00e000042c0382c0c0032641303c4400345003490308004000d12a80401131034660000500413804010351158403520b100c0c14014251313080102c403189488000c00585a0010305da20480e190f0140116401883c1310180c0840e41c0b611000c0030816844041d064000c9426450240c0000000d1120251296104460200101c0350383c1c0896034a45030186e8485600060300100c0320842a10b4502c1040d082c0d001307100307000401d03500d81c0341500900006c9250040886410f44140e010052001c15983c126802 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 979261690 1250 979260440 979260473
    0x5030603070e01120b010e06150c0c0d06200c0604030807031d1b06040b0405040c0525020f1215100801090b010807241d040228053408040e04 62
    0x4003001d410000d001ca144035100105020080101040310100ad90052025080c0003030001c00009c0d0030300c142c0c1051402480c803003e190300710088070300c01040c3c000b00301001d45800c0840e11020b4175032981e0300d460079105094018207450405547d02c0140707800c004e540588441400500f401070007020600d04000c2108200d49148601c01e000500040001401400880e815100166008610800c1900f0280c4d851700410075880d0001c80c8904140040050a80d201054140201d0344410104000d034240b006071601c40041f80c0280c0c01240384180041a002120350304a00e101c0101f9801d290f6504500e03084908000c1c0c22184400c07018010010100d08000c071002902c4040410b00052218004488054240c4c18403c4203104000e080c81c4020344000030802c0500c1d1019105643d650300c103000e0036549a6441c400090035220248190308560b200d4000d40c1c015240c540c0340780e9041c000c03011003802c9803009480854404d00704101c84100180e9024054030040c1b00720700902c04a0b0805140000d00004400b48 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 979262940 1250 979261690 979261709
    0x309010e190303051e1b07090501030c1202010210020c0706020f07240c0c030b06210c0111010b0a08060105361305011505120114060105030603070e01120b01 69
    0x41c0000059404906103049991600381a03075210f10502400c0b4165454500305402001c0108806508085c0301d0012106429100d085e9000701d0f44440000e804c40303000380806440d00740d40c4001030101c4624195900d4005005004603409400d10f910804141d900000031039402e50004041009090307010002c030081503003134802030176041c0c1c1403110500d40e0317250b2104580b10318003002464185841c010003214110a41010203592502d40301d00b00f42840c0c82c0140c464500402c5040400b080300c8081c140511426a010350141440c20f40e18001105c42d941500141c1c6c15956031600c50b10203a5983c000300d1001402c03030340041e214540c504400c12900010704032160789418400a16042c10240c3301c415848024120680340e11103072543c0308030326645103003510024101d40c03a10544c04c41403100400490204d550454031010020b4bc41403505003600c1c1c42d40200700b201004540803d80d80e6010b800a10342c07040001e41101ca20554030202540c0146086c1c0c0070300b01017a0442c2454060010300600c09014006800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 979264190 1250 979262940 979262959
    0x100605130e1903090b0f070c080309010903020f0102070506190306051801091d010c021509070b030c090607020d0308061c030c0215040f06050903010c0305040c030f06021201080309010e 81
    0x102110348510300105000201440750100c00308141c050240f44c3c01510000105a403125aa540002040d43c000308007a01c0e00185107d0000d414800001110500d038810303075a40b5191403441d42408204448000140e040d030098160105240e2108800b4102c0300d9070742d8001c0c4110103541880a000c440075608014060000030400015001c0200d0070241100d8140c1000100d101600441d0702214441050240c942d5081c03501e0100c1e01a800202d0603030102210012250031389501c440980d88940b030344510405501c041c8000780300b481c0e11002614907074802a203145c0c50b003c400e500040046039900c0d02200880c00001c2071020904100380a0340c8400b04042c094050031842d900c000c1c02c00542d80348028424442000500074200801056500030094402e0080105807240800342c810b0304003000e0039000758078005090004078420301565001700e4100035040011400d54581403c9c00104141c00d541300f42e000c03c0361001c2d000c4404c07181402481c2c818041c50700c404840d40010a2a0000d03041e0610895080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 979265440 1250 979264190 979264211
    0x131d060604030803091e0102030f070801050a06032406020d230708071704060e010e100905211002041d04230f0f06040c0807061b03020c0310060513 65
    0x211816241c011401d42d40f00d0365803204440c5425145580c00300d806d40e003400c080c00d43c2c240c1500a14001c0d00e0f00c080b80140386c0e8404000300c0d0603403024807505030700544404041100b54041d40c080c465010794040404030312400001240680320440d80080c0050b4410b4030540001c2d41c0c842c030b03140800140d2505003881e10030047c6010308030340100f960151040000184503010011148107080d0324070040f0b10207076159076803400301405484040641d140481e00256078804149000c0780d41020408454690244180c24001031040c030f094944695001190214150020704c1820840c009000b1020440580d6880c1800781c05440da00051111501c0341407041c09010000b043c0560407421719034989035503203a40d280b58131311500e0082d186054003214000c00d09482c000f0b01011606a200d24041e00003448000c0d07450341042d40d900c540744642000101180400d03650241100d5084100e180a841280c00082e070560000b420840c0d48080c0b0360680359100e800300b1036401c00400590441744180c40811862100 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 979266690 1250 979265440 979265449
    0x12040303200706030f1d010507020106080c09040f03021e010b152b0f02040b0403060b09040323071202010e1e07050d020d0b010303020f160b1905040b131d06 69
    0x500440d010f051701c03030a220040111640c4644400740030b0062114400400d0440e040c0200303003d49400005509102d4045900600055071180e00e140140a18099603201c0d21001c42918201e8012070031030256041c10710086c0300c0800202e41103108400009424600c4408012224502090100e40c0382814083c0c0e86070205c200444805a040f10000412642d03200e0b080d60006041c9850407400c0300d07101080100d0202810750190007680c0c80794000b004103441100070801d5805c4102e0b0003c0004264403d441d0202c0c2030716144803440990030b1101410840b1942d00d04416007a06580840141c0d922502c00300c80b2501000804c091002d40080c02503095907103600c041d1150020b01441d4010310522440000b152074a0125650309504018101c0080d41c40e894025103504d0307401606681885150142840c6c02c01000224040b1650b05002e6880c005901a06a680307940b1148030000384401031000052411402004010741040a04554a818108403148003402201c1c40c01c40310400d0280d042010f9501d4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 979267940 1250 979266690 979266703
    0x181e04080327030c07090c09080607030b040f0e0f16060905190932010b030a05060d020406060e040609140711030c1b04050702060919050703051204030320 68
    0x19902440300c0148002e6640080c0c0301c10124448500344800a10380e2445000030850006483d80c01c141800008005c40c81101e038060740e805030400a82041e80442c80c2d00c1d01a070310080c10100050030100c0c10340d44210811040314070340d6034400219000392050a04146007401106011011400b001e281c403818280300501440070b5001b0103014000c14582c0c0f071203074244190300d800100075002c800d01070812075800309050000c01000c0200c04061030b030031151a02c5030700305105040c0c84d503a444003400c0da80c03a02003801c05000f01605590f0045200c003003541c050b88031406039202603c0c080d21810001100c842c20301046803100ea10460900f8039200942a14220002d082ca8111446140c281c07000c500c210b01c0d090640c03041c88803450040c0301d1784100c0d00d84052401c02d111100c050032a82003140b1f41d600f010507a26508100c4204245401c2220a0383c2d110040c013904940b0180642c085951040c0c4a99540346040b900e422409880400403c0c10010142e00010914000007211040b0441d20400100d00f552040b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 979269190 1250 979267940 979267951
    0x40513120c0b150102071205030a1b02090406110d0e01050115090302030705060a180905060a14030604260c1b030f0307120e10032702090c03070e181e040803 69
    0x803c1010300d00f065038401c001c0c130405400000c0707040e92200014680381da540d500100d090780102d00150204851400d001c0d01d00400c05802401c602016a0f4540c1c1d07100040078840203502c500742c4140300200240c3d0852040455056240b00009415410801c45140c0000ca8108580802c1b040c080c080c00141c50100c3c101c41103e105881082d1110039030312050320303043c421b03445031001c0f146c0300c0b0000510319a83d508468010302c0c068407180e0780700c1e803a082c2110003007445420844c0c25511050105001401c65080c3c1210b5080c00c42800000c1e80048089000aa20840200038660b20030100740d20300741400c900c059880342c0c01314001e203908528071400700e8490054102c09002e0b000d04c08400b100060050001c03441c0c101d0014070f400c055000319107000d4020810b00c400c10181c03443d41c0e4031468804000003001040c00d80c004103181425039a404421240f580018084410090245944130340c80c1c0303032140004100c0094181d11402440d04061441c000d211024000d10240803000c14000800c40190860713800c507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 979270440 1250 979269190 979269211
    0x18090902181312080609070503150d05010b0a03081b07050a091802040c0809060c180409050115170f0a08030402010f0c0b1305150c0f0309010b040513120c0b 69
    0xd03a5070000c60084400c040c0c40140c0320007503107143c41e4465507011840303d100311400c0310030f0074040d01c4440c81250f5034001110428420303001885c0185852400c241612090b43c420790010400030410404503000052079803007242d000c140450050300c8246404c81880f0300c484968001c001183c0b6240000d03540300d160b0710400e01401e554040403250500d840d400c2c060640d4001d802172003101d440c804000c120910842ea00c000e02c1c000c03c404034520000400c01c6aa03081c05201c9185500040c0d80d0400c030080001c000111070541da40d00090002c8200d82c1c55900003480c0c07412100c00d029590a0303400c1c2c14940040001141d582207825050b0008440320b0a43c0e0f00182c081c83c00c5001266290825140503c421740064a89842c503010401e18460b0500d10a59052040c01901d2003c1a10610b035160381314117940b406840701c41400306425684a4101031680300440900128034510311101207011140140c808040c0e10301280030040901281c1642e40c403603a003840c030b0140020380c125223303551005000727000250a03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 979271690 1250 979270440 979270489
    0xd0e15130c0f1e3305120403080a050610080c0d091b050111120403060b060c10020a020d02060c040603050c0d020c0a0614040c05060a09080f0d091d0406050a02040b0a18090902 77
    0x3203100354140c031b1800d4400400c07020507090504025040b08401c40d180310b2400d04103800a4201d00745203600e00150102500ca40015440344140b034900c0743c1002d1409141e40d0307591a010030104500c108542841103421000d00080750a08000511040c14030340303010842c3d030041400c0d90083c1034503400c440403a6005040001c000d80301c4400100c0e10301c00e41000201ca40b14184003140c2c01901907005003802c20054084078280a4490307400d90300c0d11000c4800d45191207003800200106406a00116801200c00403811318048440010340300303c3e08881141d511542c00030086004002c958458a821000a010785900c58a0f043e600c102044525000300d50103403a0106190800c14040e02051000e0a912800d4590940b600e00001d907484a00c0c03149000000c4010701d0000703e50321100980309006403100f0b450365103540c4d40c5c0c545030f01824001e0900b440300c0da420080040d0512850018003044a0155152492511040d5001208041075000701c50150714080c08c0c0700c011381c0c500c08902c200c640340c014010700 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 979272940 1250 979271690 979271789
    0x215010e0a0207060e0c04061d04110d0b0117061e04030c020a0b0711040506090105030a06020c1615030e0309030c1e090c0d0e15130c0f1e 61
    0x40d000d4990024001d03414041505d82221001c14540d0603400103940402c5966580e03c40b81d0308405003955650502029500401c010406000900c482d24a000d080c000c560031169403140c2070444c00364426008418002001c0c3c0603580d0502090f030304a000e440c894001d050203035105041021000d040241401821f207682801c64540701001070040c0b04034610241c0714161801c24092485030809841d1040385040300060480c03070044180e5041c2c82e0094000c008440003076860100030b507c4440070190034812100382c0014009540b5810300517109040b035040f104a0052005002c0d181220003032160394006002242c002d80380007030b00a004100848010103161040d20070050300b074600f4482680c06c40d1950040014a008810042c0001e543c6484100600c81d110010750340c03501510342c034000001c1c1c0c844011558481d42c030400c5c598114080d90342607102c1d507074480c60724088203d81c4c0d2007050301380300b019055804596610000001410540724050300d400d0700b8251000c20115241d180031184040718031401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 979274190 1250 979272940 979272961
    0x1150809033c0307020703060f090804030b090102040506160201120c02030a0c060f020307030903020d0905010801050d050319020601050a0f0b0322050d0201060302090a1b0e010c0b1006020c010215010e 88
    0x90340c4500c0b4503480d540e4100030900039240c52960100f41d030654141805a1010305070b600c201a61a5042044981490309540e80c42448203800f4000144a40d024080800d05030b684600070312010b480c0407807801c102c000da8030014141040c03100005a52501e0203451507612500070040300c0c2c00103020f141c00d00008001d49010720082004d240b070740780c0442c404402c000072940c061703222041e032074003c2d000c441c00358182420840d41c4100318011b0f280007130400030040115080ca075070610a442c0c400c07070680e401e012040e1054190403885000c80b00040e0700010041040d4140302414401401d168000c007490036007000c7e00b03000c0500c006003150380c003010409035030690241040c910044080d8000300b0b0700d002d60f501c0e0100034082c3c186400244d2043c0ba1a0000ca480c90b03074140b00d40e21600080701d00030100840b031070100b81c4594101403400c9052040102a6000040d46140482d00c1a2000d9489003001420128002e2521200003d0281550301c0101c46d818000d01441d1901c0c11240841241d040c00da4030107035080b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 979275440 1250 979274190 979274287
    0x7032d050c1b0303041a09072309040c140418021c0804030c0603050c04151101022209050105371a09030f1c05130308030115080903 58
    0x381c2008860b004038002500d4044001c6010398080c4003410100d0408000303403001c0103400d90300c07441c2c60740c00301404000890111030344c2802c00e08040c0310041240c40160220b801b01104450407102c1d403e0702001840080c05504440540b21000d071420004100c005010b58840075a400010303110302c400c0340c4244940d09048980400362588600c925031155581c0c40c1050044c419802110702190800000400061a05083e00d04642c6140b660341d1401c3d004802c01d45041c848000402c40c0d07950200302401404200c440640a010712078420114001d24154040c8101d80044c0c20661244c0041d100c0700c8240b08030001120072100c42589800100d030380c03c8116824150640d0f020301001c01d09680444103641c1c0020181c24950001d0381a10030381d05803004460703250918062005104e0100803003c2203243e12400203002259000c00e21889455181d480c0d071012070308241d004209420030ad15002c0c04040e030010040360000c003980010b508004c0c3d21203010300600407207403c01c070010303c81e0090040c07109194900c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 979276690 1250 979275440 979275457
    0x191a090d020a260a080307031e0c0909110906030412030e0105042904150c0c050a29090606100315090c0207063608011407032d050c 58
    0x1040052a51240c94003c0303a001000b4002111801c18141c80d210803010400c08a2168402c0c00c203071a640d240d10040d00102030350340e8081c40b90111105010703180e2101d0300c01d407012040301d0303103403881c0e80c1e4074002851042e0340f200300c609082d1880c140060032154a60074241c07a0440e520491141075500d0f0810308034020541c0e42c407200c00c075600b09001e200134440000302c801794403850f46000382100c200310700034800348003020343d8024045404001d6019500230564000880c80f02e1030715040000b480c5645501e8034004c0307040340030341c0d240e50b0700d1030034040010010803601c00c0701441e6001d2005031702d801c4050303a4546038002c0c82d00e80503041c0400c040d03401c0c81c403d50000c0c0504064859250117140c903410050001d09008001d0b001511030f20320003280719405410b400a0103144900384e020b90005080000c040c90040e01000c0400420f05000810220b00c280540c90040054400345400d1317140404e8000c056800c6400c4a0b040076000140c0403490030307000c03a4240c050103518240400c4c81e4407042141d4116200b810030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 979277940 1250 979276690 979276699
    0x312050d180204050c0306010f0f0e0a030b0f010e07020a0b1b030a060906091a040903020c0907050c0c0a080a060b060f0403050a020f03071d0604110c0c191a090d02 72
    0x241d18145004010926040b4000d803000c02460703503120170540303051000b0ba88403804910889400002c0a101e0300c8800c803d010549000101d9010308400311302c5600c3c19420071180007520300204049821980e00345401050303141481041814010790194032903100704070140075003034032f03400281c240c0c22520741c20400b90f15045100d56403440d20400940040442c0e01a9019050a003180007440300c81034042c9a81c0c0130041070088041e89141c108201c018440e108084096004a1b00c007030360f15a0758898034030f10a00b91511060f6690254042e1181040a4262514803031840703000c0c1440300040008000455030f600441c0010728010f0074001407624040c0c4020788424650000300441000004503034611b01a101b903070505042c024001c01c0685666041c05001074181030403905c1742031803000d00104ca8001e540500005081c07603450103400c8643e440480c440c01c40c0d60110200e00c41c00d0401e40d01c1c0350440303c0d0703400c4500001350610404500055a9103041c142c4844003245c455461b994400003400c40507401003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 979279190 1250 979277940 979277951
    0x20607030513151107090c09230301151a0715020c0115270203040b040b0a150e1f08030910050f0a02160b030919110301090b0a060b090a0312050d 64
    0x80080c9400303804e0601c41d07010300542a0000b8480340b03078020005682659110a04410704010f110f0691402ca58084800c070044001503400c41c1d2400e1052480f20403807000c09004e990704091007020902c603100040303102071404005510200704c1012203c04500c0301c4520142c0c1d40c00345061881d02404c140c0b0a94907000350320080c0001e45010040c1c154100000306441004920b045c1003070380d0124001103501414803081d40d800180022440c00500d540005040c00015a01c00148500326030028280c0007220200700d000c080c8402d950105120b181d8245194030036500440c02d01600b50f4880c025003000c14017a03503a21100d1070600c3c1c000c50a4850081003402041e483c0c0f641494000d50f1340005030355014024501035000319209110b541100c3c442c0c4025402094041100388d0b201e441c2d072000c030000396400b5240040e0f00250395400c0c0100003400740158004412424004042812243e513517010345c200c4d0008001071900d5031503180105c4102e82c1c00a6851081d0151135009031814802d4a0b007030350090f45800d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 979280440 1250 979279190 979279229
    0x105030412021c0909110c07030602070c170304030b3904030209090105010905100f0b031e2403010e1b0307081509070905040206090906120d0305090613020607030513 73
    0x2c0310881200c080c5c1405110141c503061844550384522030043c1040e40240030113002182d0f20341c00400c40317548100c05171001540d03281110070715498282150582c5410001e010010701614000356138101145281d0b0306410009141003410010000c0501c41031141c1d05400da43c4404040000d5500664016000f011649010503050b030090000b401000c03c0c09203410085520400d05e04104001c1c0c44d034081d1f990300710608040c2c0042058100412180034002c10800890281c602c00c25a540130301000e018512009510307000c0c402c6500e0216401600a030315060130302c4440c002c00240118403402c600344007209101400042402d124154100d012184203c100c84a06008000b1134148503065800c2500c086544485041003961010b403006540103406000d46030151400009050704801c0080900b003c0d5035054110070b0814080002090109a461003042104142804119848107424200e08600d080960001d60240100003000c0c003001b401107201c020075120380940341d018100456104444d41b13070700d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 979281690 1250 979280440 979280447
    0xf0705030c0d0e061215040615020c0f0a03151d0f06010b18010302090406030c0b22060203041215090b01060201150810020703030b040903050c12090105030412021c 72
    0x41c0441d4500348104102203425901c40d205210106000030121860320b642d41d5120380e030100740075040746a0444c00080c54a8640e9441c81910020b115031019800390070840701010b41031050001e40d130303801390600f940c00000568036a2215401d49520468855a2586000c0c8210050031101100b00800500030103043c0a00000116103503403079140000c803000c40e03817110462202d50142070704a18000440d0b02082d1071541c000d40240407222406040003500e6070340ca0315640f1441295038002d08041e580080c00c10021040e0110469801d846070711402c00061501400039030b03074485c9105d080d10010440e001c1800304100081d8428000304091001e00070031040d03052103040c5810030702c05d1070050742c6071405400529440f609008211451384016003000a41d4556020296000507400c41c1019502d421945d0166140d00c10701c0c110768040d84e200ca481e118000c004038501030f4507200076006c1e0716007400154496070780002202c3e440355005440324042c0001c408241c5c07804500d12a9040301002002d80d0628450341b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 979282940 1250 979281690 979281697
    0x5031c05221a0702010905011d030d0f020f0a0b0a05131428051f090602030c130605031b1c090b0604240302040e03040b03100815010b0904050603030f070503 69
    0xe0002c0c070040d14804640a0015910542e80000d0110715110002c110640c02201e1082c42e1005812086080c000d403440000d00b0905071034113610105001507003d44a1075410019040c200400500414030091141c07591200b4103001800c1600071a1160001159854004007044105a002c6c840c4540441e401001648910401700d803003c41d0700e0300d00d2b1202e40840440c101c20941e582c02c000540000e000e150462a0407409200c0c2c292004c41d2a4060480003da00b4070056206548000402d907e0b070030307101c040310710381d4106500a604101e4213106125a0b138080d05250542c500104005682d20b20460709140042e00c8482c03400365030245845001d0051042c0c02c00b5a80c882c2104880030003808907004003560442640c405610300b0304a41c88400c0c130050070141d211450300002c803000c03282415078411084000f64070446515644644800c0c0c1003211700f00812210b61027451b050101701c4e03130b5070420b114585140240c40569100d562118040f50752524144111503040c44000029179444a44c0d08005541e40e2 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 979284190 1250 979282940 979282949
    0x11e0e0103230a0f111809011502060c030405210a11010e15041a040f031101021e0d1b0302120a0e0c0108040501180606080c0a05031c0522 61
    0x34240903400070603840760b039403800500250350481001030321440d140307000400c1c0304014964079503030b90301500c440441003c0143c03185400e1031144213690041c28084c00301001041c1e01c15156a02d59140d540c003459004110030390b200343c83d0b22440e501d0f507441e801c200e40343c500442080c0c055010300a8000034400c051500404604081c0d0300ca2094003807030f0030b041c070f8225010700f04405005e07040350000000c1c03105245d14264200b03000d821080d0500c9402404150040020344003201c2d203403550313100e06d410140c0248031198001c0c110b00085003015400721010030240b841107000c41e084880054138016918140d402220192000c4041001c000c48a001c043d000303600c040c50391010564072800054280c0f5550154550801d88900504401c050384001903071300704400f074401c5903507540b0345868500110502d42028020780c098040495024606401e1380e00304112640501e01400c10404188015140082ca0805001c6155a40308880100c1301048503c5d01503001641040c0075249101c00491030851005000d8070b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 979285440 1250 979284190 979284197
    0x7060f09030642060e01030902030f0705150c0606150c0f07050a140d0f051c030506040b03010c080711010f060f0503070e01180c2d020115050d11011e0e01 68
    0x400100341060f64800802207607044030109a0050100600c5511138210000042c10046803d59003680002e0500000040440760759020010410070707803a048011802007501e50154a241660650585031103420042046015190780301d11814040c048a04031425114881c048c0c0f500c514405080c251901850b200d42d902c41c200e03590010400302c1c112442c0b000900f0006000c6070032203041e551402041200c214045c2e0f25409075203141840400d000100c0c0004d041155400905440d000c0c1c1008115110758003072034080d0380f400d00703d580000d4110032540c1c0c0000c07250a00a44043c10b43e02c0f41400340425000d051540c5040075800540c075119900c08105458084043c2d0306e14030740722001d003c080c02c800d100e10448400300e5001c0b4110345125901c03000b0798241524100210540044101c04080800078001442950340084140100c2d4203208041860519070001c600142c584000107417480300d0740e1400342419035400503081c4580c3c05042c0c030740c071403030a000600021010640310180809200404041c040f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 979286690 1250 979285440 979285511
    0x60105150f0313030306030b0702030a1704030206040f050712050309030f060f0408070c150e0f010906050f030915090a110616060f0603140304090b030c010207060f090306 75
    0x208590100707803440058100506411903580d44820051290031140680925955000200c042812070440c64030a401e6a002160b56596000004241c0c144101456030010209424080080d9000c00e0b20741d00079405c4000702c4100503850030030030b040030502d42c001100200078000301401c100000c00a440c4400301101074507030040b04410b4054981400701c0d244801c40000c600050005242035014104060140581c118510344480720340b4801e03901d1501e60001b0402402e1601510302d840712400b4503014081c60079000032840c10704054268007e8040301400c0c3c11700440084c0000804201040d1152820080403c40e0709150310a03684070082000300382c42c0d48a4950882e101070810724219886490810b600c0f0604400a45840008140d6900140200f50322404000007007940481c008a40b00c4039180a59610382c03808071505c00b2182c8903045180660001c20a407c8187e801103410350403140b07541840700128100d034104842c1001150130051403a0b01d000003643c002c0c0140308414a101e100c03003911100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 979287940 1250 979286690 979286719
    0x4230406110a02070816080c10021006090e0f12030703020c0c1005030f0708010f05012001060602031c050c090d080d020c07030b0112020a03170d1107020a050a0b0405060327060105 79
    0x1402e40303802201d5003a40a08c50803030031404c040b4040c441d0b1111910584207002e80340700001007610f4203030780550700e1541c4883c240e06034900d040c0314904d1002c3e11030340144003c0b4811166200f00b4000244220309140d40450050b810071400d1111280c058002030146124000d0880c016095400c08e4541007241e903174910000704194061301080d41a50345014a00954a1a01004541c1741c01103940366100384401981c5007074441024095030000d40210f40185481d803092442c8031154078846e0b9410b01d0742906000520001031941411601c54440640b40c0411400050814180900c80c4190303041039544001503440e00040040340384426039100d508c0280490741d8a050710a01c0e0802d460020394047d10683d020030020b80440381d0000f017909203640b803c1c145503a22000074203c60409031404158100020404114a08403624102a207402c40d82411850b042c0801d0a4542c0600c0c000d060040200002041548008402c1034041c01c41e110310f58402c610702c40c42c005440744002c0c4100c60054048039a02107 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 979289190 1250 979287940 979287973
    0x409050109062f090604030b090604200109140a03051f0507030506130504020406180603050f0d050d0209030a0230281121070504230406110a020708 65
    0x3036503d07500c120610b40c01d5029800c103c0300d40c4a55031095000d802000004006a1904c0c0103900c5039140001078417807807030b180c20803d40c0040000e9582a8100c11a50f02005a0b0f82003107407442a111012683c00c441d251000105da420285600f010741140700e0740100442011115201c3c400c15078034000c00f070180f6260200e05600b0345200b41d071020351160490380110101945d80c0c0c00b0b140d00c2030004001061243d5115000544003183c1809030710031944400003032080c00f00802100c0d103800700000042954640c1c15500a180703010351402c2403101a00007500320420382d000c001030800386400502d03100014000c040307040e0712141c6140385128000105600012204000300740300c070b201c0c4001c5010300f0304115043e0b10a482c0c59110074080f070701c1d00d88408240d00ca0307481d0707007118a140a0801940301d0154540c100a545484a1644480d20a50500e175442c594090b004902582402c141d0709030301071075142c074904600602403c0080c00f0802d0000704080300750545c001512412074000c4400da841000c00c003440103 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 979290440 1250 979289190 979289231
    0x1030507050f06030f040f0b0108030c0c0d0f140c04060b0909070f090b130305010906050912090109090b041d0d030b0f060a0c0f0803070c17190e0a05040905010906 72
    0x10303034000c1090000130b019000344005c0c0c1d41c0c01440380859500d001603070ba85101100c4800c0c0c0000c0d919500210b0312140c0040c0c100b201180381d29080320000000d012a5840007000800c0c220300800b0030104002459a028040002c4c0450100043c014040691503400d008150b030840300416202c1e255000c0400c1c07000e40a82140b120b4101d02d03070b1707401081c02e05000000c035082e40149803d843c0015503a90000124000f071007110b490b50300c21074021559080c4002038514004010340c5081104000300300c50369660381c0000041c411150701410129409032008005001000106401361914200c0000a01140400305510700340300d41d2a01d0070010240480248900c2c003052520154102d8003c20082d12194003a0384607124151290081004840d0307d561441c81315080be036150f0001c0383c81d00c90408100941c80e55043c03a09001d01103064241000e507555441203200302c082100034414080b2803502991280c100600207043c0140090108102614085000709107104080d1509890f0039500080049400c504 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 979291690 1250 979290440 979290469
    0x20103024902190e06040806150a1d0a09020d020d03081008210d1e0f0c030507050702010f120624090803070803150907020606040f02130308031e010b030103050705 72
    0x400c10902803103081540d03242c0c3c1301d26929600102c144030000d0703811420080f0301c0c0f2420520728030161191060041c041c0e440040e800c140d640c008008018214601401d824590003461110003196101490010134848400c0000186d000000040c2e42e0041c0750300000090701600200c242082c05964818495071a90301521910340340c029034a00241d28800d2080103000d4040c400344e800505090110100040308400744000c11902d1344504250402c50031510425a13050344600b0180040d01c0c016000a04601c40d044009040c0300c045640000725522510038100707501d071414020007034103880d01711006141c0380150301207101b020345003d0004401c0c4600800b908641410004609103201c40c2e483c41d065400c0200407440c100140c100c40c1c135181e558030003658091507064000c1e005609000c030070320064601e10101c00111a00410008192141d040c40010851b03402c4001541c5a032a442244440e510301006640d9980220600100e4002a10401181202c0c49101101d44965450b0140040d41040d07010 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 979292940 1250 979291690 979291717
    0x120a06120834060504080f041e0605031012150203100e0c040602030703080c19030203040203060f0f0a0c111b0a080610060305040201030e3c0a020103024902 69
    0x2c1050020745290401500a4420a0490700f0312995041c1514150440da00200398900311300707c044100020304403c50301400302c40c0b801c0307451403415503807010100006e0b204200c0d00401a046880c00d101480399045050004a0700a40d902e06010f41001d003480414000c0e080c1c40040d00010440007813841088078110742098020f5030901d000c2da01d00780c484010041291413448020820803040484400c0381c2043e1591503200142c40c0d080c02d00600d4a8044010700d41f500c0715103403100b0300140c070301e0309c07520a907000c80c80d014081906401c00c48200c071800e43c07120320407001e440748501d0341041c1141c0a04104450b00c007a1031841c0d41603600c114041c0c0c0d40c281a0fa21002c60104040e0910a5500c203400c42d692060043c1408140802c215a03014507006207001a80203507034001e02c00e070680303042607a00a48500402480305903001c604c520455140c050b0303110300030306065001840485001c40c2c0041110413001104030031181c000c060040aa21a6034400d0358501c8244a404c440a1079003244203442c10092141c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 979294190 1250 979292940 979293037
    0xa0206075c01180e0103030234140307050901080106090b0108070509010309241401150219110307121205040e041b090e0309040f0c0203120a061208 65
    0x800548802c00414003d00160005580c013040815a0804030345c0214829801800724035604420004140d141d9007901409002402440c000782c2141300c41041900c0c5e84404408010030b80c0e0f00000d260122175442550843c12002c00024141810340c4040e04441d0a580c0c240304d0454003c00441d0f03986011900b03075002c60018005c145403544a0f920200c10303030b441450901001c801d417540c1e80c41032801c0c04150111003525641aa184d0448003440f40e80104944e02280d40b001007200c034060340398843c00300302c02410a2006000c40038083d44a094022451018042d43c954640b0768a003041c41881800080d110310f01c114a20a90b100d2049003100c04503161103510007000e403102daa40c0c0900206801090b181c0300034060020641c0070284c071400e1446201e81c0300030b659480303142080c0b00640c0d00c10f040c20140f06142c0804101807030340100c111a100d5070701004000e803941c1c0700040e060003850903400515560b500328083d403080003000c2e4010301c80702080812034100004900d01c1944156458004580a4450907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 979295440 1250 979294190 979294373
    0xd0f0807030302270118060f080c0f1c1a0913050c0604080c01080a0504080901050c0a05070e07030b1e012d0c120206090a020607 57
    0x401401a00340310b4940035141c0381a4003010601d403840c0720082200c4001d0701c5600d4403a0b40c0c0003036505030901150f100c1100050b2503c2000b0701a41e400c120f280c0c0a0002180006070b45113864022a0714141c0c0c05e0803000e440e010b0809095881a2001915904d100d2900c030f50ba040350b500c000321113083c1117801048400160b5030414020750080c00d1a2084030180b2034030301c0c00c2d01140d903a14050001381c010800241031000f40400014507088004e024103011602d02070901c404944a1400c80300201c00a08100d80c2d6889400a240d01d0100410030184c01c50090140224034280215026070081c0e210340d03001e00c440d20f0040100102020075800811a0311140b00c084d4580b94058034600c0da418060f01c410035691194000d45810001249181c540043c0101d09100200442c0e001003400e280d01520013804030303213000032045a40d0482800083e00c101c01c042501010020040076448050380214000c00820050701001036280306000201440032a11498503000740340880516a031100044540641c5485035 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 979296690 1250 979295440 979295453
    0x4021c0302010212010b0c07090e0a0f0219091401051e130e16031205031501140d020d0603050d050708090f0301140112050c0a0e0f0c13170c0d0f 64
    0xa4040490555400f80820302040c408466994003c0071a118481e42c1c50300c03441c030540d0825680d5008880d9451402148000d4a0000a040d00c04e1580c01043d030180b400841c00020003c0000304500741d40c0c08444140824002019001501c050440c030880d00ca40d0b0362100c041007000030070742424140040890780b03100345c02d140034502020118844000040d41e0f280c0c5484460034000034030403418100212440410130440b428620f4061b04d1040d1402c0c9046013000081c5449040040424604103d08400306c011050705d82c6044139590400c0f05411503a40f4414100b190184c407680c030040d1064000c070a042c400107401482180c00395a8002c80040c5407040341810855400c240c04403103501503580c1c514068005208801c054060208841c80031084806413501a18000a07482080e01400c0c102c8000c0011214221b1560f8000f9008004078010307688995908450740101c1d020010700c09588074000034502c400d000e140403411500c00644151210441c240f00100d81e08560040c01000e0790140300c00440c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 979297940 1250 979296690 979296739
    0x909280b061b06061903020901030321050f0f09060907170c0a06093803090a17092107031b0f14040b010905031b01030603020d080c12030402 62
    0xd00030501400d21000082003103458054081d0819180d10003070074801c003803400007041c13044035130071403000b01a90313042d41d000c1840c800f0706200060500c1420016080aa04840d206800090280d08208464071b0000501e410300300060b038980603081000d07408074104000c042003051217010080010914945402065260032181340000c02d01402811546c01d101c2d620078030386a005040e00d56400382654100903140b080d00c948003e03540e420001da0b10118181c0c914860034600c40c2d410040701c158581e5550796582d820308600303c200401c13115610640404240c1c01001030004010107440c041500000c0e4460169051098004801142c3c800b09003080040c80b80c8104026070301302081300e001c0955075520401c0100c1c02d903030042e400c030110f040301e25080743c00d152013400e840348424030700360b1081454540426250075401031607810100a03200140545d90080d08080010b40d40070340180b040060b0760900340c0103504507150010b514003036a005005e51a812009490103540c0040061315611680240d40d40c40c0300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 979299190 1250 979297940 979297961
    0x3120e061b22061407020306160c0c06121125031403070903110d0b01090b030c130207050106050d110904032d021002040326070f0503090928 62
    0x120208150349554925110580721140901001c2c0c080c00c1c1410f102600303030304003410880c078009000c1c403184016903000030b0119000000411080b800031101001104c400b07814502c09070070060700c118000b400650001411061921114040060300303403602d9103404510855000801886030904082d054000700340404120b00d101c0c1c2403618002401482c14031440d001155284003040f2140410014008071641d01f49241a00304d68081100f4403650310307010740c2d40040c0118605580d6501583e10785890800507548640d100034a4803c0c04080030018801951014204a95650800310000f9050a0041c0041007940e4084c40c1458644440e000703101008070300520940030003c82c08681c14580340301070440b660310947c0d0090a075101e1800000a0b181800605030b03070985910400080000c1034494401c02200d400300185102051884a040320740340c010600d0180081548011500820000000400c0018010b4807601100c3e5102d80d1038034860a610b2024056642d00c010303000f440d8100316480790030001c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 979300440 1250 979299190 979299241
    0xa0306022107020601140909061303050915031008010509030f0d1d0a210e0409060608011401082a010f021e03070c0515070312060b031303120e06 64
    0x1040034000010201c0e00603121400960001c0c00140049009104044141c0700c042d11030000b5410708003080b5558130402040d448180d003010f92220205403007002264158240245030b03032070007169422034500f550300c165070994200020800020314520107000303030761040c0c1e0b42602560074102d92800c0c1007800e5108500800040303688003400007103d01c10160800100c0350180080101d840340e881d00700044000c11a8140394610300300400000b05501c007200682099094a010680c040c003450201c0141080f03030090140c41d401c0c0040c0306030291050005034100c620780c804803455074010b0b90582c84003400304004041a003030703c0c11103031170254000d07500002031a98510490700b07403903013010b695a00702520301400c62a94000241c0030b010b2100e00f40000001c4c10003101d65070315130000c100a80a2310322442200909003c0e4ac041191400ba480b540502d00411502d02c60079070301e140411900c03e4038180c242c400c901282030718041d440148060700c194143c0d00c02000042c8010b8a820415104d00c400364030b16032288 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 979301690 1250 979300440 979300477
    0x3120507020d0c03110904020a060c1502030c0304030f0f12022d090a0617071404090504150f021309021b03070627030f1b1a06030d030b0a030602 64
    0x589581e000d80074800d00400841c1107013400c40c9001032260480000c954483c080b0003052202581d135020301c0100f166184e00b000b004048192609107114400b031800d848440e440402044070b58a03104000f5449580701e942d0340151407540c40000d40e11940e49000c403038009219030b8002c03032900c20198000c0000d540784240715043c1c0c10b01409010102807400301020031102d00806c5a24150405140e04806800a810002c18980c14007500f04201079006054804114040c000307006000d180300220380181c182201d0610503072801e41000c44c10700c00c00d5520480c3c06c52401000c0c415404a510984440c40c0d0345003616488103240800c0d06000c2d4100d403080e0f40d0440c04c540545c0c0f249140c10401040c0d40303807040f9004108031032000e1090a4040070702e003400b0501801800d800700000d0340a62440d0310340c1c5442c10322524845801c6c5503a8088801c7c0000180007429070b2403144090048114210700c201c8044040340c05050340500c00b04c00366220592107503045030301c07403d0074000078800d034000c0d00d4081c5a49415000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 979302940 1250 979301690 979301693
    0xa0b0909010603150b0315040c0807030b0f010b16030e0102030c0304140a061b080d0b0a0905041b060c0b0606090a0b120903090120120a020706080604140103120507 72
    0x8400a06a88540103a0342d110010020082c2048804502d41014042000314992040100303850741e0348094164007491400000a0802c212600031801420075281162586512442d180315114020340750b50140641e24030002880081000807102c030210048540340e02083d1541c0c05031554011540103038154002400706104260040001d4802414410803462403000400c06001a5000703607080a420031200718200c0c680e203c40c440c03c0303421059000b011070343d9403056014038000401d000d18075907a006140c4140003840040e6504264046d90051650b03100400c182812004201e48521941e804a9417a0410070b001c548800941603103c4005000c451500301c4003800900c4584c0c4c00e42206072181c0c0302080c0511b00c803c91900607644a403011000307500e80078401001138005120320b0b8001804500d1080c0c124004401031007540108101203640c1602e8030a0100041e403203080c0c5015840024680c0b03400100320b4038003405140c0c240c02c420304c40d8005590854440080a145180312001440000c004020 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 979304190 1250 979302940 979302949
    0x1a060c0f01180213050702031e07170307030e0a02010e010c030908070f06023703051611010f0c0c03123b04020c0601230301020705010605010e0105130e0a0b 69
    0x35180e0349140c2d10186410907900c1000070003000300350501c1c6607500c0c01c010482e0b03041c2c0000440d10410b50444004a81c035241c848402e086110b0140c0040034002c41225140d44c280f108009940034000c00e49080c84880071094280c2c1d0f4602c3e420001074001391403440c1c8881254020700002012500034030300310310140d03200c150321850b1a00d00d910658825020900070801e2907030602c68051081c800ca90102c6035086000070506014100a19480031074020360001e004040c010402c032040c49680303080000740c80c50705040c03035848921243d21030350100d1024155040c07224802c0c061840d150780d21051590207181180c548194015076000403405002c0304039080d000d8000d0106000041080881d031400a86030204407000003040c607108500e0240f40140402042d1000100c1e1079410f6800c1851740c001241400381c01014481c030081c91907500740d40300066290a00c1010341140d01a14000c1e200c01070741080c4100111441d100d040c00b50040d070038640c1c0040c000801800c506603080721209101048040101c5c0008 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 979305440 1250 979304190 979304201
    0x1090f0b0405070b0f0405010e0f03191e0305160f08040b070314040302030c0f150d05090705090f01060f120204090f0507050a02032d0f0a030509011a060c0f01 70
    0x56800300354a50400007000030400c0848003410303080f02c42c0b42c1446050780d01070b6060700941c0540e41c10310106102c0101c2d01d031680001d0138440000182200c65213040341d60003c0c110a140401681d803040304031408800e0449000402040a41c5990750920f005644a40803921910b100001c90b01c9600307180d1070b80b008c1950000600042c040d82d0301010341d20501850040d1039002101d602038400c0c48107000030005a0740c04603520f51f191a0a84040100c1803603100010f491070181040c150040034003240b201640c65003940810712442e40782089881d52a00c55007000b16621013210a820071895150040c081240320355401d604400c42e6082000c5070340c0350f600d400c4090b80c000e90404081140e03130b640d68402000340c900440d500b1000c00c0c02c01e02e1078014039134402500c83c824a6440c89950101803080840c20400740d001d1101403505404160701c4245a450328030455120b50700c3c1100081c1820045180000103100d1041d604411f0004610b0044520041c0442a00488400e001601600441c41810102070194 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 979306690 1250 979305440 979305443
    0x20705031902070f0f03080c010b220609052802070206190813030f200106030c05130b100807051c231e06060705030c0102031509070c120201090f 64
    0x4080750511000d0007442c0c4041d560151906038200e072010012921140303800402d680c0c000300e109035940000c5071600d01618800851681066070081c0c3c25070014241840303076007003140c441c00c10702c4410b5655042c04c00351001070320496070840099444005140256005440c1595481409400c240e03061b00001d8254020399108a406a10644080149544103107020b41c400301c20420713503640c4400c903280100070355800100901401105250006040440404c038039041075010002d0140c19141d240040741c2d00c1c06803103418081c0300d580d00d807010030031002c0c0206024450094418640ba0140c50402c80d04124043c1041c410320000b088120100042d00b810428410007a18010581641a240154600c0e40311803410018903103030f505008a101d9480140c580215041094518544888000400718800c11100a00c50300c000180c0b204401c8041d0042c41c400d03111500840641e42103c1e040c00b000083c12207400f00040d003203442d10301c0001d14900c2846030380a524070000401c186075640349804505110300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 979307940 1250 979306690 979306717
    0x90909081308010507021509010e030c0109030f0f270909050a12030b130c020316120e040204050616060204090e03071203060509070e030a060501150e03011a040f02070503 75
    0x1d00e1904115a00004402000141d000b00942d2030040c8009407655100c80d04440700c19000404259110025002841011400e1b81929590060a1921170080044c400102e000ca40104140d400d000c3c0580d01003060700c2445e8540140c4c0019000c3c002402c4040815044075141e1224000306600000d4410210754902c0350004002560341030910140d107040100b2510105814040a0300250321440c2ca60314086d0345071074000c14001041d0304103a00314010302c3c0e82d00c2c2c00d00c85084004070500604551010690107503465900d6407a8420044c0001c0e8444c0e03012b120f030880010081200e07004041054820310900941d00142010b07160315815094940c142881c201c60391000c24450180a80000380754440c40d103a090400c1650f2404001c104054001800c801c184440e0000010180c1c40c180300080e0b81507440311007040300b0b40c5c58450b0741030304080368908040019000360b512500c60030148500d0807401004003140c11079401c0042040050b00011003035020300d035000e021040010303074100050030342c0d911403c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 979309190 1250 979307940 979307947
    0x525030c060506040605060f09060d020708030103031412010b221413050f0601110a0b0103031d180a0e070f0902070201080906010b0301030609030216060801080d05120c0a09090908 79
    0x18032a080d29400383c0028030452412a04004070f54644044844141c0748889481d121032007040001c4060092090591703c103400000e80c0f5003000240c00003181660710a031220100d03c1c80c40000e851160048003544046640348100511103c040c54020f072103100364011020340860100c40b01c8070017021441e07002c0780d01c6450310b120031410ba10b004100d00450b4490840208000d03c3c280301201400b40000d82803d05200c1c1e049440707060150140084120680c001e13a1000a65a403071600510f8000c0f09131120360201141248150389241c045030303442c004201d070030b04040140c0380d11035100001d00e0f40f842281074030b00c5444c4001030494022041d080090000040c01030302d0f903005000241c9081002810014140c1140d40103105050b030900940c2d0640303030031400010ba11006480c0580c94400c0c0118100c5180080e14800110103a000403082e05803074848080d0b40c04e442a0f00381c1074807980100703480c00b0041d55010f0001040e174000807011308403540b0146450035800340e499810318101ca09000081c3d52108001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 979310440 1250 979309190 979309193
    0x8090d12120f0b030a0b2205070e06010512040320060123100527090a060611030903070308030a020f12070306050f010c060e010615080402030d08060306070525030c 72
    0x1d20a000400741c41c02c03028000f08450900098680c850071000905140c900c0010804605243c20020148084c003c2c08403034654490070559a070f08140d05c5851003004020001402952080302511403003594030340c0040301c0e501d403550292203807054281c66032043c4508841c041c2c003120041107050700902c400d080c607a0f070300076240d0b24591113451000c204070b00491000d2202c00259500c502202d003001458012081c06001c0740070500d141e804d06507072045d400720460040c40a0511181e002d81e00300c9520342c44002d98100080107164076805038a001c254990044401000403400c040c1c001c503070003102c0ca1001072824480c1009500540c0090500031000c0300c0c020300700800c0580501c00d1402500003122215220102d0302c0009003181c412035801001035499441d2028551425002034000d0036450501035540c0008200003090b50b0405c5401781c0c0b0a1180d120704103e4180600801401000090041c01c05507440c00f10990f1650b03c100a0f01e08210103480342240311034090000305009034800d607119903d19005 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 979311690 1250 979310440 979310477
    0x3011104080c0f0123041208030601090e1509040204270309050102030f030a0b0f04181515053d0314060105030601120204210c17060408090d12 63
    0x10010706005071103290100883e603800c80040b441c3c020a2040c005491080001c0710031003030155502001d4a150f10703550060802c202c6001441c8158001e07030350403030803035510313201490b401401307403251071000700f03400000c51300d508111113516805070001c1c1011800361480700080d0070600c09886040400c00802e01c00f2030401d54080040c80050600344015400c003c14100030125030700c4007402e0050040d40d10150400103448003a424a61040020420400620402c04034a854100c0c035a080b964141081c0315070002800c24460155501d00801043d0001742c02e042c144403802c0c00900da0800e070350700c8244040202c55002d0482400494005d007140400c43d1484001a05a401c41c04070b1507a040040e03403c01119980c03010a41e98410402d00c0c10b043e10f130784103c00314402441141c100143e1a606621010074056a0004901c480e610900307031800c41c5070b55070420320050403286040c2741d2641c10210114011a050303001502e020a0f006010401100c0e040e56079040c00e041407020744002c1a01c000c800d180c81c0c1e01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 979312940 1250 979311690 979311703
    0x9010813030806120f07170c0612070c030c0524071e0810030618050f030c100b04020f0c06180d02120d060806010f032603040b04060b0301110408 64
    0x240315a108105100c5680c0107041d802c0010261801040040070102c1c50380360070820341d900c445c819030542c0c64081c0ca030207403802c06480c040040850343c415004181d016083c10012503003107001013a860541c40d29152012a010b6008480540801030380c1640340021503814400c0c20307500d20000005054450709907213500e4459400034491014010409610a003400ca00075183c0c140d0b03e5949002c2c58103940d191140059200c6540010340720780d2501c101c0311548a21141c480443c0740c0200100c800c60581c9035090b80d500d01c2841030540c12600a45825000c050310b035040092003030002400541003170034214942c5003913000681c11a040c1d0703002100748a80d42c1007040e00c60350891400d8014088815400501a554030021800013503007100028070141c0540e9640d1151000d842d0560603101503507900c0404d18100b040351300045d514450041481d4000e0328610402c0d590a0441c1501541540e5503512035600b161001001950340330f4030b0300389080c1259028402c08150311b00e403003282901e031820300c2c040038030f0030740d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 979314190 1250 979312940 979312951
    0x10306060801080c22060909050709020c0d08070c02090f04151b0c080d050702071509050114180a09060311031504080c0a08031305060a0506100c020102070b0f090108 73
    0x2040a005208a1001003003407811000192a00303d40030741c0032016026070305c508a8030080c01a103050300c086003a0200da080f00fa0181d00402c1100c105680300c1640e4022131042450081042d80015a1205400d02804856a124843d4101483e03624080d802042040408441c40407202101c41c08200405c04854400b90645a85200c20080c00b1560a08030b54554415644001030000340d070b1494041040e0707082250365204000605011a00300b14101965030031150140c0c000e0300c268a010603149922441d03c031400c0702d00c140e42c3c106110b0380807205001da980c0b00000c00da4800400a10201440e210404010020882c00e54001551861420004062030102e402a0f10035000420342269101101031100d40194200c000c0c01d84d0340c1402c03941c1501d4611951001407c2e84404005c0010214051075420a024001d030141da074641c4c0c82c00d62500485a00701da000e43d1040300c040650820394828141c1801e600d2060040724a015107030a162031094101101003500b12034002500c2d07105584c07010803240c100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 979315440 1250 979314190 979314197
    0xe0f070f0e0a050d02040905010c02010b09150d1106071202030c0708010b0a0e1e01080102030f06030604030c1205161203061d0609070e12061f060203120c041a040501030606 76
    0x9801c04002405400c0750311405201e210451002410365560b0390000c0c0b00c0310390000003004504013a21029000c0c10200621900c12111140091160245030600b01c5500c0b4005006100009140d580e11440402e400c400c0b5800400600030180014a1280308001184664005580b68408260b0052400c07401c1e80105010f6410007000c00c1541c2c80341c101d10000c0e9004207846119540d02d010050701415072180c9900008200d03040000381840b011340c000c5020380d800d0044000c00d0f58030402455510b0030295002000209440749150100300000c1007507418030020301d4201c2c42d001c1c40341000c00704480d08d0841941e251002495901c3c0560b054400d020042840c0da0448603494200400c509400d40001d104034015460760000a11091190b540008104070040050154a21300c400d01903885100712400030800b44e904a00d5904440901100c400f101c803a0b600551400d0320800070890b18610251010480407000d000102d14400c0d07000c10381180c1c8800905071601c0780e1800c1e00060648030746900c201d052 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 979316546 1106 979315440 979315457
    0xc10050c091e090f010303020a141614040f0506010f0e0102070515030f0604020c03091c0c171605011704020d02060c030a030f2a090e0f070f 62
    0x200c0192801c1490382c4e01c4400d4401c610310b0a0101401503801445c01e500040d407400e02c01c20040036072405a450221400040300c80250031900018030204840d143d2041c142868451000540d00302c480520040c24400000f9111000d0f0131000402c00121a10f2036075a07134000c201d0b000003002e01410000b09c000f040c50a50310b03550010384144140414040100b06d1500d024000e9804622100b8041d501d090424410054041031b400789a1215a80d0282c1000c0420802c01c01100241110f501d44c0e100580b02100150615100300d01070048003030500d10a10a603680201011030703001030020851440d403a03d000240c244104428000c0d8800000181210581e070080080e0070070751115102440000582003400c42540e9640d0000003221904003c00400d40000745407070304208004d410048071154030b42c41c6040300110100e60154504007103c09105025500883d0b03440e94244030305c3d05041e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 979136690 979316546 := by
  have h0 := BRFrame.cov_init 979136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 979136690 ≤ n) (h2 : n < 979316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
