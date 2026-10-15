-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4857
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:57:29.925456+00:00
-- url     : https://prove2.me/submissions/04898d8c-d9e3-4812-8506-710c77cb7798

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 873381294 ≤ n < 873561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 873382544 1250 873381294 873381367
    0x601140307030c110a050705191d0711121806070f0b0a0f020d0204081605030d27080a0b0c0a0e04020d020904060b040e0f13060b0406030c1706010b 65
    0x1195500300310000d031601c45c0510203104007040f01c040b0b40d5000f02d6004485840d502082e0fa10003a585885d5885140c003c074104c118101070f1034070001c1d69141d11540c0360a10300c2c03400381074405450a01002e407522000d500310014a018400c0d00c1c1d54105100708501751019800c1001b0303030303036000d040103068000a03142007201000901310000079005005203205580003076484011405100029421602503030205000c3c0f004951600c180800e07603074044070300c018000c201c00c00c0a50003d840600348000b06050303d00e0418603109001c030f1a01003140080441000500340441603080014200d0b06c050440070741c0d007904001500101c3c0e48400c064040f0041110016500d00703040c500d520091051040b01d9030043d040150001d19826000040d104850241c41c1080c11a03954910305400c44000f100c240d01c0383e541c1c030f42166001c24084c8d0b000c00c00241001d0b0002901584940b030700d40707400c03049502003070601141450000b10841e0500543c1d005001d080c07100c604107035411040f02c20b000201703a42c0301417182d03010b03140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 873383794 1250 873382544 873382547
    0x605240108060d1209080c151b01060302041a130e030d0c120e1c02070513091b151b020d08030903040b0a02011a09060904020105030a0902090c030405060601140307030c 74
    0x1003003400c4d481070203602c0f0200e080102070800f000a110300d4406000c0d082a80640307040c00c420b44001c0da480d1441d0107291015407074012101c3e0215650300c014541d0307140c50200041c1c0300c42c8603c1d01415550700c000c02d82c40042800b00300195402d81c0f000c1c401c5505001c51104917030400419515126145000810803081d2020b080303c1c40c00384c1c1030844c103050b81040c215045062001c03900c003e140020251103601f0702e001c0c800590f941e0901c1d2103100d800c0245c14400385c000d900c2591210207000d110380c58040c80312052075031140901c241c075040303015001900e141c0c8403c61604041c540b8a940c5598020100300095500000c0006604030400b900c49040040060104170051080341c0241806c00460b980340d80b1301d140c009001300704014012030400301941d03c1c0e48042c40c0460006124000007007141c4025500c030360044941e9000600345e4814191946120702c016501c403c907407403150648800c155201d01e0103090242c0f4101c00039082905120010607104c140c640100110b030743c40403d82c2404a40040140f00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 873385044 1250 873383794 873383809
    0x2090603011a040b04090b1f05030703080406031806090b0106081506070b0619090605010807031116030513060804060b0906031207030903120507050d020f0703060e01020c03030f04060524010806 85
    0x100400701c1c14502c00300315054480c1d04050280208565010102340c0d216014196224240d000107005000f00b03002c03c00246101ea081001c074150f0380031a554071116681c0c0c900042d91886031040310103a50410040c40110f174020f0f81254411000c0400c1142d680b1802d0200e5010b1040308405041010508001501c1e501da210280b2100107000ca658401aa85c030442074000303042138012280003813511008210118468041c1d40c0c410390442407403624100212400c91044458044200c0074070200340700e00c0100c2903682104400420864840703600740c0c54645000c60407240c00c0700040f885010041d040c004207441c0003d507505400004003103943d95109506056641c180c040d44010490303450988076860f030550040c0a0f2485074421021180301044d1040f0907a205e00b9808510422640708180030000300341d01307410010b12542150001403030410906445411944210b031031500f4081254180701c200000c034403030141d00c1608408550f1005a100756080300c15014014414100300126020038400e42e00e808 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 873386294 1250 873385044 873385061
    0x9060d0f0609022d06090f12100f021c02040e010e15030a121b03021b0a150206040c0608100e0414060103050f07080c0f09041a1302090603011a040b04 66
    0xd045610030a02c50310200105003860040b800c84e444c905002c4806400d180040e2454580000c0c00d042404081c98103221030000040c50b8000b051141c4003508a0030500c0d44940006010701e14000b50342e414901c11a62141048480d8510325a88104030420003500c04040c1a03040d0360540402e0441070300c0c0c3c045100c0d0038074a001c0c0c45036814001c400a40040001690045a41100f16203801c40310801c9000c0c00040c0a105080180142e080480d80106001c0300c46c4e650410300c0130040500c08865228001c000751032000100610169004c2e106010074400080c600304d004080c585070000d0b103842d080440d00c075202030901caa5441510408041001c016601203910104000e500032a40550381d00e0401039607030750004003a940140035084020640040110762060320020182c40100349030311a0052007443e0000520507182000401c64010320114546181802109400d826a900c4c0380c41d401000007001c0082d00491180e85800300200c803d0072171604500710240308803000a4170240010206000d4501c44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 873387544 1250 873386294 873386299
    0xe060112020f12060f0f010e130e06040b09030f090105030411040e06070e1e10111e1216200411070c06170a0213030c2309060d0f060902 60
    0x410140d0032210b000b07001c1c101807040107020500c00d865103001e00601c00494940a6003004004403181483d50060422102c99207001d000341040d071100c400d4040032100780e032001c07028070b0308040d0512041c000202c03e02500f000030301c8051072400f414514581c045218842c0d2003414402c0203c00070b414002e4070700c03004090110242051021a4035403401d0360303e6540807210740c1701060032031540c0d24050404800003c004d020054101c1042d214040411030003503291826201005220392070884d8500c002d10180c000e00c8450b411030070300e0300ba048600f0340c10103201075a4141c2500c801e020180369010380c035186c4051035420001202134036854903c0d010b0500800800f0503001420000180d410f5101c0200030000e25010700c2413108102d403101360480b50703106440e1601f40e10000c2d0b41c6c04903241c14140d5000304103842c1c0c8210812680d59070703a9100c0130401704c10743c440115070381981c0705201d540d81c07d00d0386108000400c6441c030225141020000f0704980703a480d805070103501024101002c014003a0320161905400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 873388794 1250 873387544 873387547
    0x41709060a081509010e10080106060e130917040312050702091501200c01140f040e0c04050d082703060718080f010606120b0d0f020d12051b0601030c0e06011202 71
    0x50314010320b0b4603241620447e00101d00c602000640b1300c0b040c858074040c1c4815075900d20740031007500c0401c408050700d42e000184803035841c41c40e40006a00958500d08500c04036151035190745c41c6040c1000300300141802c407000e05c0420000f0300016a10700c14102e81c40041655581c00381c480b000300403070b183c000c0b6003944829001000c084107518003000840c00c45800e0242e071046c0352001031803918541405184c07807010110005100900c15481d9401495910001440d03409040980c6e03040040d000702c1404005a8044200040007449808513030301c401c01480701e03540118040705103080466034544001781071604114400348a030f4001c00c2c05144040040040c03804a901d040030030303400d040c024005841440701041c2c01e0b00450000310031900034000400c100900d4030b00da4480c0c131f031114240710820b04012603200258000c0140011040c0f488009400da065594640790078401041d081c104e01102c0020701e96070b1040c0010000158180a100181c0e01c000c00c40c1d0740b068982400581d0111a00310300405900d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 873390044 1250 873388794 873388799
    0x30207050a031e1e200601060909050609090d0f050c150f09190f1703072a0f021c05031207030b010c0519050309040e06041709060a08150901 62
    0xf4041c03940d0351640c211996640c501c19071050290341c61650303200c0240031000d015255095082c001c2c0895000d00391210200c000a001143c100360404200341c000c0e2020506000081c0b0801070248285a4400701c150ba00b5100350400482c0203a039440c01c01010780410003120903210506200f4800e44031440034000c1164a1302c080c401c01058030283c00c40c1c111703005010840024280000c0002c0007982d07c00d181c01441450f0038039485801250b0100c07401074511415000400069074040001140700e20001d40d903000d85401541c510411000c144c80c408401d1a00c621003410106511030940001a941212800d002c12040e0340301604101301e0f50704c007421034000843c00c0354612400d018000c2c4944010f0780c042114080c400c005503900a42c4400c043c01c42d81c049041c0182c50004d10001140807802740b000c0f0382c184100c2000040c2600c4541c0ca51111603000f131070901080040d520310a20340f04c80f0001d00e29042c07801c203601143c2140545420071042184002c04a6102c400c0380c50304400110740541091043c0d81c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 873391294 1250 873390044 873390047
    0xc0109060905060702032106030102041809140309131806090b09070911040324020a0309030201050a050c07080a050415090303020c01020c01140f0904020414030610080c0907030207050a03 82
    0x210150358a00600f000500d00c6803000c4101c6010340e184001c88410011012494020982c0007072070650150350810011519143c04003a0905111003803c0129684459280007640c003908150320401d190f000740040407071540ca2400f05401a201d01400160b9003101e04012003910f102c0d41c1000c0c11031490300c0303500400c0c8944060176078428070b003c1084488250b6558601c0088038140301c1c50800001041c002031000030f0465001c0103190b06d02c0e01f02c3c41815410164000c04903401025181d01090361074801c0381c01c158083c080c0d10ba0080b02041c1c00c105034980401ea480c0c80c1e11410718001d00c5900d0006030b1b2030781039006000782c801030160021200581900c0c03c1c00900010401e0106801612440e010f1281d01d41c400564903910060607034031405140241c5510a9031030f00425100114480144105500d030303221340c4050001400c900b030a4180e034454550502d42880c1010701710a00c250b2416205002051001032220401d0208ae44d8075171161b038501030101c0c02400345a900a0142c091590100d0615 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 873392544 1250 873391294 873391301
    0x1a120103050309090c030c0a030504110415051011070501030c050c060c040306180210030b0411031608090a21090302040e161719080c07060201050a060909020d060b01050c010906 78
    0x1500107940507002c4e074803051102201400111995030b0110005c02103041c0c024426005103811510501049041c44d68182c005030944040e203452000d2010408400c001c18503012841d005040030604000080f0020084c2060300c5400030b005a605068449400c030401e2846041240d40b0981d10100b03030740c0c540c101b0350059000d503030091100340c6165003003c9680b02d074009080c40e42e87c0d801d80d0083c040b80601070b090700281c01a02000d0305413940315550b0051111041900c20055105242d518a10011882d401030f0280100401400005640e807000402d180060410385c2100d1a021360860140b000c400090800c403021400e0f908003e41142c1000d018901c17400d80021507041c00700b82e11284051103a2245a4400814440c1c06081050382c800f10303c8116031400c0d09038404081d0300850000f807612200c003400d20301c0d0816a42c001f10040c2e5540e8104901000c0910402e0040c004036242404089403e80006526480210028011594408d2152441d80c010400c9a01c032842c8a0000c0c0040d914904020008 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 873393794 1250 873392544 873392557
    0xf04080c01180501050a120f0c020c100c0f06022d070204050c03220c0b0f0d0c230a020a0203240a1503150207061b0e04060f1a1201030503 61
    0x1c030b03000e2901e01110300507600074031003503800681d51241403291204048500900140c50351400a980c1c0041100350b080354012840c41c1e03041500105424600b000621004884000b40315003044441b00a000000b103111140e061010780004001d6202c4048620791510104c4007114021082c400c0c4480328081000000506200d5000b1501040155980c0d1b1a4000500c01240c04000b005911441105080300d02a120036107a4054400c40308440d442d00d204086a03072000c09541c50b6607a01250120f1081158022803800071100d150001c030381001282000785c00a50f00c03007410241000860040c81081c82046801c440c0b6030028104d401c01442c10400c1082d05011a070741d68038016410700040d50100b0607014110b960421440c643c001c00c3c0c55a200c004180001c507404101403a020041c0002103045130048aa061071034071100d520201c80c00a0140034044903c0d0b540b8000c50400c00c04002c0814443c240000f2030342407a910a10100b00e00c0046039440c800c229000c4980f0404e200080709114000001e0681d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 873395044 1250 873393794 873393797
    0xa1a330a062c030717070515071202010c050a0c020f10030c0306050105130614070605160e1e041d0312010e091f0902060d140603100207260f04080c01 66
    0x75a0041d00701c0300680003502c141c40c81e007551108004000a070b801d01d10010300030030030301d00f0f0b200b40e90744841c005124901000038900322040c0206144081c4600b0006500340d2031110b0000304180207003108080c129000703100294083c0f0008041520940d100d0039521a0f030030302c000f00400a0041e007140e014005141d018200d00c0060314042c008502940290101d4191a44520b01d01b20315a1900714200c810980d5401045108003040c0311150008030036010781401501070703038103200810840080c0240145001800d0602c2088502440c010503441d10103490442c10050381c02082d40d1101e80c1c040d0306000040401c00300240700c0081e184014008002295040c0c94040199482c03503192060300c15543c10720402056050f5105c81e441d658600090380c03020540a00c06404c20303040050342e0040380101d0310074100061284403000100086481d05221807113008400d5801142081c14a45800116042c4c038806610601d1000d04411b04202d2801c06a0b4181c200d07519800795141d444001854486865045039030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 873396294 1250 873395044 873395087
    0xc010c11010605090a09030216030c090b090402060706200c1b0a0302060a18050406060809120309030702010c02060d0c0c05060108071404050709170a1a330a06 70
    0x101803801030141e202280c1005010070100d4640d079002400800b003102c421802e5100314541c002010034a01003120046001d82c01406500745056580020713200741550403880b030901502000016510303501039640151b00b003080014805500b02c0c030b0188032010748400f460f140c10003040c2d54408240025903160b040b180000044244079091091020080050000035481103040c40354042461040c054800e821015059800710342d035507030000c901110b01940065001a40e01000c21003001d40810840c042c00c20b41c03030b94a624620740141d54507103d00594000034100520445020103541c1c03654141c49101188250421800d86002009400c040604000b12503030700882000140821003c0382000c116a072400711766440f20780034000c010003050010040f0052005158000c14040e044030051132040c2403400080c524070103982408014143c5030300c030a0309602c0100041201d114148101c0c01c08280c000d20055181680140303200020000c07004090340c100b10440300000300507922511100c00c009401c001c18 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 873397544 1250 873396294 873396317
    0xb2a1605040b090402030a03260705071b03021509042004050123030106110a0f0303020d062709170c010c0807020c010207050f0a08030408010c0e0a12110402070204020c010c 76
    0xf040d407680840e0081c0d8550444162000464010001d100d202584d003604440180085c134100c02d540b03401034940100007100030514100300029004841198580c81450b05030b09427440e07000940308141c80150425085002c24405015240d0b50002101161030701c07241342401030304440c56800780d0014495a40014000d07100000c209030b6140b00d03520f00d40f2404180c40d00c0d684c201003054590b4441814035040900c21448090081a80401e0b0481c60500c640d50240c6e403604028913000644041e07400551080c403081d81e07201c18030311a4606188945c0700c407060101d00d070440e80c20035440f000a12282600c030500e00080c01225804103500124006c69a07480d040790988403420200d036601c0311559000d001d03902c2000d0601051500010a884c0c84100a02c0039640342d40f24068541160419803082070107030744400c0031b82519034100a0352502c0090503281c07403440600c0c02c0141c5028246110303001e814103044a4117010191510740480e581150040e0040d540e0301c2001c80050b000306400000071001410384941c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 873398794 1250 873397544 873397549
    0x504050309190f0b071e0c030201020705060a08040615080307210c082704020a0216270b0f06120f06090c0a08100302150417070b2a1605040b 62
    0x101400c1d9400f03444400c21440c14060380c0a12036100075015101844044110604101242242c4050034803d0610420f03052079440060302c3c080e900e411441c468a0f0900210402c65403001c0b04540c040c0d00440c001c43c1e0441240414444640c0b56000f03604030340000100e1a0500c04044c08902142d881c80001f00c40507403021030122807103c42440000c0401c0f800300280851010504152404218a0382d18241584840000503040b641b2089040380540c10a140000e200c18900310ba820041200c91032401143c050401011007449156800001107556003030000d507143c541c000d204a00d0761010f80044d07038905030229010b04043c4225180c0b4810611680092043c1c00c202740f02d1401000310b40419424643c143d80241c3d0b4400005103804200c0303590480c0000540c0d00c141d161041900c0c040259944c85060107042c440c940d1031010b40f0f03403180e4000d804c1040f12400b00c000300e91440810704c40b4940900c1488603040110075071214015941d1260404441001c2e45500182089450858041051a120170107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 873400044 1250 873398794 873398839
    0x603020403152018120d080f130b1e1b03130602090a09090210050703140d0f0c020d1115040f08070506070f030b030604170d0209040504050309 63
    0x108407900d180010b007101c0b80700f81c00000181030704028000d040100d4051038461904110b00c0005020740c03c8882c450f6170f0900001e6440b000368014040d00c1581410040034210755006403506c1c03c811000b20001c2d0340300c1240260340320215480104e101c014100003608000703d40480075200e1028410402142c141800503151014006404803600d0859a84100881108919100a03070348607408101d003000641e80c144c0102c014080010300041c62100301c0c0103001d03449081d500f000c02403050030030031400420740112080f0f0050590941d115a50180842c500003d860203440c000c807164141950385041ca038011640000501d4281c0d50302048400e00300702299900303403004012a84846a0780410046210442c20304042c41c0911450b9150814641e10381e40ba04108845000004030845488504998180141d216001c0210010409ca0500da02c90014080d078250308a1090800041d92040402c0c190301507410f103450040080019142506000303441c3d5000e81c411034400d0700a643d80044040751400c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 873401294 1250 873400044 873400049
    0x9061509060315050307080714010c0809220f09050f1f020c03120c03060a09090503090d0c0f1410090e0114030a0b0a14090601060516140f06090706030204 68
    0x240c845118524001040d0b006001821240310105150100420140c03420000c1c0801404108014882c840c68060300585540300ca482d6241004000c8101001203420101540c1440308110344c0000c0803001c0c13407a4550300c44071001d5060445810702c84494140006075200310403450268043d0f0b04464000801103490319900c94550042d01c000384000c01c0405481d6014040601a40044a243c0151101900f11030542200d0000c0400c070000200103c034148031800b072008200c4410244030000c1c055079a25100c1c096591902d005442900c0c401d01840740e0301d2804802401c4100d000003540c1d40307402c20b0001c106a0344035107a0086402820b903c0e0128480e522000c1140c12241c0700303034070b640d0800c05034140c00c400800700e5039810311650a1000200311400e00090250907924400a03030001c40c0b091500f4035000c0104035220036000b10004000301504001200c03442d421130111001e56801504c4e110b00315041041c0500c4143c851000741a03030b441400030b41c1c140103581c6001141e4085030b4640f0220143d11aa0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 873402544 1250 873401294 873401297
    0x3060102150610110a21020c0a05011d04150603140c090306060d05010609052d0403020d030902150304080a1b0302070314010e0d090501090b070c0e06240301090615 72
    0x811200100d03510412071302495072020000d603a07501c00315403a58004a0b1011090490803440706070004440d68042104410000f0181c4000d2015868500041c00300054000d2000c8540f5003050302c080690750f142e000404140d0081104040117840d0000100240440350040d402c69240360085100d5140c0d00040c0d6545100080007804280c0c0c5800912641c002c800c1001c5869640318840031030785094500540c2e101e0204c0c060503d207203c0c000303501040c4542a00c010740c151840c1e02c078203002c00f20b90701080c1101c140c40e9508000c11510b500d48007140f41c8001d4450700d01803000c0301000b44402c10002a00604101d04142c1d14905d884000d01e210180c4900000c100401507402f042042002801e1042c5600920815900001e420354101d510300b0304007014043d0300e40c0042d25901c410301066801c840248040c1c13400d0781b485401c0201079510b2603550038450088001000c6000009449503481a0f0a441002c011120303a0705860901d41e0fa1760020740080c051130040d942090300c0030900c8150f503105461100c415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 873403794 1250 873402544 873402559
    0x1121103221721012306070b0c2d220b04060807050904050f04150605030c04020c07050604030c090b0904050616031b09080708010c050711040b0409050102030601021506 74
    0x40c6000b4402d2503204002c0090525070a0341c080c901101c084000038000c00501420750316407811000502406503500030f849108650a001840106070004501ca50048800040c03030798031003494810f8002121402594844402040000c04540e101500502001103e500c4412041d6100700310b000c01c40c4c00340b4001c80080c11000e04c800c201c1d05201e07072000f0b41c104000b4100741d440c0c60002c0022a09640b800c680010700341c20183d0a02c8200a551041d0810424540a04000f06414200080d850300c03c0712641901c80da40220385003803002404d1040344028a00105043c1d911940da180c001804452445007009582ca4500143c0c03d508198140d81d1007668407030090310701903903a502c981d41114215050b010406540e00003003415040d0708800802c1041050310350a14851400325403c1c070b003070007a422a18060341407003440d0089540140a9804480c0d00402c4200c4140b8020f010138000c1000400895015050a40040034050194000c40c0203920030317400e5500b62404103001d03c8000000740e032180d1700a0710 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 873405044 1250 873403794 873403823
    0x1020a1205040606090603080910181208130608070e04020403030909020c120a120b030109050c130e10061d070e1207030b040501050f011706150112110322 68
    0x320307980030603801481098001400da44400306202281c1d0703941c004a0740d0502c00900250189022280306100039214034100d80440d5050b000603090100900c01c00781800c0c07401d000da40400c482c0f401550354100c10100312080c0da07540d5500c002d0007a4400c6e100d00300410328400ca000310358100341c02141c00342c98068440303414403071420248000070340c4036101d00700c0030b80103074001c4c5212550f0680003018031401d03664860600c1b660001680c8100c512540b0910311980c9889601c10014501140c0d000344003d04035451440b85180d17102e42006051241860201030040c030f5400c40ea10300e555402041920046154240044100781e480c407000002603170001c007c500c05500502152500d135840401440121094916550390f03595000c1484005a03000c0342e41d41d4580f41048074511407500d04034014442104a0f1304011035004c3ca19495540c054035602c1030a510140da10800d0340a42c607181072034042d035030003003000d100901902c060b9904142d46c1c6034003140d030b401c2c031140c020100e00c1000120301c2d40080c1c25420b8940c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 873406294 1250 873405044 873405077
    0x50a111606170c1804180606091a0d0b0603190309090507030c02070b16020d06051b03070f1224171209060a0e1c061103160f050c030c0c030f01020a 65
    0x21221200760303010791203043c1d8003150b80e500040e2000440c403c60003c2400c87c10301c82400d068a00032402028040e68a00c6505603d4be0780c01c0c4240981c0380c0001c03030040592646c00100c0c0c20259002c44042c001030f19800040d0815074081d44002c129550014100826200c4200c202e0a4a00d410080300c0181c2c4412001d1201044010007000c5150f05460070b50301e005000e50100303d94000b090001d480c419910741c1084031002c40d05402190005009030980c0c41c40c5080b10b0003034440c000c1e110101c0100459501a0380660702e06507c09076051403184e001452985448541d10f10440f00d600a05410b215142080004400009034901d02000c0204c0300504102c4c0200900850b0b41180c6020b20400130854501c15158440b0312001401c0d0301c911100740d0101798141001c006590342083d0441007205c04000b004008068803010422062003407400300a04440d8503001c607004c0c000c141c1111418000010340c9111482d0000b6070400d50041503003903a0700903a2580e546801c0740160700481340411090741d2561a4070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 873407544 1250 873406294 873406327
    0x9070c030f0320090a0e010501270b0c0f010b040501050109030b1e0702070303090f1410020c03060709030303060b03090a030f2312060d12050a111606170c 68
    0x80720740c9000180090300c0303100d0340382c441040075050b201c10700c001482ca070a41c02d1020300000900002686496a0b51500303000030440c144d0050386118400e9100d0b5540800d00d1180095802088000e142ca0b40f220b80010b400c0c3c1d225001c100d080c400359880c0540c1d0030910306103030007a24125903058484184642c5552150340350300c00010081c03202c803401880b00500801144180780d0180341e1650080c0f00703003411403a0152502a01e034120744820400301808101c040354030b00c1c00021017042540c040140c00c540403416443c01070601030940c4d05004240c200058154050b082e402100d01999007880207644d14181e207002844140c8240c44150010324100340428090260500011a1841c04909040003e58415199122510f00402203840000c81c0c140441e1054146034001034101c07111081c21065903904043c0308030310000340b824004c020540c40d07030950262041d0303655100d4810a460307410005001c0035071658a20300442020540318140722085000180300d0900c00c4682030b454601d0015400c6041600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 873408794 1250 873407544 873407567
    0x32705010f05090f03010606050c101a011b0f1401060905041101081806041212020c0a15020f0c01050108070b070c061407050d020106061101090201081b1e040302040b09070c03 77
    0x1480004c483c9030300303842c00d2080e90300800e119503549840301d8041c0302017410700c421012280c0c2584e0510203807a20111464585103c1c00e4024200000b03405842ca448014400351004054410304501c41e1190612900700104114800d402c0c00070032583e0707250055501120420f441c05483d00c40f288074200134550103400c40e26040380c0c3c0703004203078003112025161500c0e11404603801c858800c03142050b20701064003c2c050080c408990741c1c0c2942402c1400e9007241d528080b0103130241034060307400c60403082c910646d81224a801d078104041a82e42c1d030884900b40c081c0001380f06405080c412032000040c107034040000c1d20189a40207107004621450076400701d134110700c80280d49330455020400400010703000c002040c91496a40c001084c02c61070110090103002d40350b0021805a4145944e00c2c005030b07480080340342d010207140c49041c0d03c69044a80b0403050b020700c41080300041d042c181040701c0d07001004050822244211801d0059610040911101e50300656000c2e0200d482c0210314800240501207a00303d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 873410044 1250 873408794 873408799
    0x115060f1b0c051c0501050604062d05040207050a0c0806010e180c06181021110c0a030903051213090203040512030a0603020a080109030509060309070f03032705010f0509 75
    0x24030760f0701d8100149544540e9a513400000500b04104000c2000a01443d80d1049040314200095490305c9614521a40c0e0101002d10988068508a42d850480403500018000140c401c40d02c3d074483d450312550300c1103c86801d403101840b440000a1b00302000404074169a80841d28075015156800048400c20344001ea1110314050b5821040b02619030102905040f00c10005802c440d0b2840c2c070034000b512841c0c105280802402e070403051b004500307d9103100c01c5032050900c0013039000c03e580403c017298042c511040b415401020000428580e00c190104150383c040da041d10703a0912042c0002c007040c42842c0c0c1c2c241030715000020030855446507a01440d4841d01903400c0d606204c1401c0030313462507603008442801401d43da0782070a0055082919140c4081c141d0a4000c100c000402c0d1805480ca01030420b03207a00c600400400180c0ca180300f4001c110040c82081c04503041161a0710f009001664000040d41030a02d0580a2074540380400c00d5140854006131104030b4180b668a1044445a106144641c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 873411294 1250 873410044 873410063
    0x1a040e01171f0b06210f01210201030e0a1a0c0304120e01231803030f070b0709080a0b072c1014030f070f050309121c0e0115060f1b 58
    0x3d4140d110400203010345104040344d14549408070304651000c3d00081c00c4203052031034060050010496000e545010102034040c100c140d0320359880101d0140040d2104a800c2d8040c8085d10010030140e04100b802c0c01ca400390115140d903466482c0801c8501003283e02810b2004100c05d01040c1600074181c480c02c0d0381041c0361603004400c0482c070716104131000b02c1282205a00008100800c1c001c0ca034000c2c4402c0e1b104401131441e1000864003058207004a0801801a28801011a401c10300900d0407030000c10407c000e0f00c1c40320304142081e0400c7c0c81e0403074003103011410705d00c0e110448100705a0101d01003a00a04408081001c030005d1181c0b078101500d045003480083c2d10220220040e17040603500c201001e01c036071a0203192100d0f000f49000c2030440c1070b805000043c410322400c09000301d1900707015413068203425107a07480706c203001440b00c2c4e00c4c0030b0386200d99250228040714a036040d08000406043d0b1b02d60f60072850f65800c000c65030b03218a003c03440006401440640803032a0f0111032252094052000b05 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 873412544 1250 873411294 873411311
    0x8030c04080a2d0c090c020102091203030a05150619030b06220b03010e012312060f0907180e0106052805030a1106131a040e01171f 58
    0x85181c03036081d2105a42012401403250401101c40801c2c0194110100100c00c0320200c2d0341e90b0000e07041c013a008881c000f40e00d03001031108051003503040e6010010b008106841d00000a031a55440ba070003642c030301c410b0f941491f0025181c180000f0032078904c101c0141480e403a0445111040c00c16448550240c2d00f09a140c0b40004907654400001c3d00080b480300281030242d180b00500c0041d445c03083e50151001e4002070004000908803032101504440201c6d640d01c04a0000441164081e081c1d98807a84c1c0c07008440301c40084194001802a208600d000c2c90701c010380e1a183c4105035140c0341c034030804040c0324161400c42644001d64111101f0f88114034004248640c40d0300000703130220b01640c1c4503800c0307940c1e50320b035154209000a00c9000501c4190003030300c058101510707008400c20b0016400c501580300021003900c010900032002d4024041c080d0545242e00011902d603501e03500522070304100c1d041e444004621250901d400c0d503e2406644010320680c504d40c0d54102078444540341c1191540d076103c100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 873413794 1250 873412544 873412559
    0x2603071509050f0f100b04050106090b0a0513172e09021201050405010c0906090f030209070c240c030204150f0207170a2108010e06040605151908040c0308030c04 71
    0x1d83c4c8040c120714054007591040440c0031084860190f00313548102e040c0001000300c150001030380741c107031807407290303555555001d4130000c0d6000c0c4511446c5001c032400b0484001250020101c1d0b907401c0704400030a8441c00103140c41d8825980b5040340540c2c10010703100c160460004034550090008034809018801810796003a03407642107030412130b800e0700d6a9444010f6402c00c19480310144010b407845061048005003001005035680000e804020f005405520102c0c82050194507008515a4070407114400c0c01c8011207000843d540c020f400031019400e190791102510b0082c02a08c081d00c4004122030382440c0241411a80c15807a14032a8040d0701030303644013180caa40340705039031054003c04400920818050340342100300c124072104000302d680100030b41d11100d26406854030b4115004107105621541350000024010411540403903440180690380c6209400404050030081c110350002100040c2502c0b0155801c1e60200c4005100145e0413034144000f410440255400601c1a800d01d4201510b8a90 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 873415044 1250 873413794 873413803
    0x30e0f0310020c0f07060f0210020a110f010608013602040b030604030305061306150e03070b04060e090c0a050d09060f09080d0c030b1311070503042603071509050f 72
    0x100403103130b8200300303540d40e139004041108100500c2d840c5480c001101040e00c0081d1120352016500c03412980005d59504803511400d61180212908021f4480c90504417013102d00900f02c07072041e0301e05c550911070140705130006e40d16240c25036010302c0d01001e0300014046800c42300007424002240c3c842d5803038011010341d803402c004e6140310b07a12036100003c5605004040022200c40c2c10380c00960103007007031014841c086400f5030504203c8a140ad100e446c1c03448800c00207060a4175034020101100c004640002c560b64481e40d5004000020303185440c079911009819a1144500a40b00f8080b0302c04008601691400303500c03142c4414000c41c80000c0b0388644105100590f0013418007559020804030b81d6500034500742c032443c1c100002904080000080003000300302035000a40d401308240b9036031440c20f50a00080412035803e0b0b13503c1008d0f00d541300d07201d00301c0115095942d0024000e00100c6004101409c8001084462441e0400c03284480b03120b44c905d640c0701074a03132403100b100c441c050302c85e40c05914ae10400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 873416294 1250 873415044 873415057
    0x12050c0d090b0106122a0e060f090411040e040308070c02040507050403150b010f0e061902030a021e06040803090c0a08030c0f06010b0405091e070e01030b0d030e0f031002 75
    0x2c011401545042002880024082000c0440518000c03e11001c0f180c6006445820240c503045c480ca480f050b08802c1c5d441c400306002058010300000340d06044098060010131440340200c07002c0140c1d03061048071406501444c010702030102040000300740482e02501140d03622050b28070740090302c241c20743e01090a0360342c1035a0107404200b010805008201481a0040b045040e8074420802c02c01e8203000200910600d080c08410b002c40303541031804603107694040302c0e12204d02e80c030034460801c041c001c000e6403a841044120014000c0034801c03a803030410407c44882611160300106100c0c0c036103480d404011751002d414040a4031441003484500e03111607019000410064001d180c4075501c0441c96418800c2d0740f90200501d0b080000180801c0381f000d400d0381c054505c00d50f4001c030140d941c50412400700c11058080380059100c0004c03c034200e03a01c0b0740c48281c1c8800a90301403041101c0c2c0810700c0041c1c80c0c1e061000380810700c54400c50409080080f00320040b0b5000038222001013000030034000c02ca03484503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 873417544 1250 873416294 873416303
    0x4151d07060f1409032a0603011203180e060f040e06090703030815061c090506090309271812040f08071406121302060c0d09060f12050c0d09 62
    0x40e030b0300d81680d0822129110943c00707001c0989803600010000741c4407200103440d8540c5000d070074a64a00050090b29540700391401800065607561100601500e4800343c0714100c00107640c5212800070503d148402004039590030741590210303112401001900b00d243d0a1058106945072500340b00400e0800001c0d00412800780508105829130600822146005001c07160070352030321101801d180c6070041100c0245210080012503a00c1c0c01e600326000d804162740107071091180005103c0b01c060084003c0001120032140301c90b455454030801d440c015110002090381842a0303000030200b00d80310145c510b28054503020b640da41400701400c041a900541c00022920320b40f82000c0c040c0300001c10001c80588541884010790b2151300b00026158403540720954804080d240110342451568084064401e42c010140c540320b00354400101e56501c003a0000c03000207503180c0000641c182c0030b42d0101032018030702e42c1c640803081910701c9210090040171f003846a501504100d5110b00b14140d01c121001c05204 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 873418794 1250 873417544 873417557
    0x60a08151903031d031f051b03091507032c070f080a110a0806011a0403150f0513020306180c040c0e12030f070627030e04060b0304151d0706 62
    0xf100b203203010310b0500c201e8003402680030345d11b00c400025032a103009000402c101c40c003050300c0d66000d80e000e071740c04004650440d1217640032041c000c00943c04a545a100c03c8982000c0304240d0300e1042c00c0b000c4d22000c52110f08500c05070f84852208009415141c0408580b4208445d00070307a941c0100aa1086542c1c4600c0700c03904040744641c10028002a040794281048894a00b01418180e201d0f85400d41032090090b0a1506544101c01002e00303401c0e2801550440440c010451068030408068103581c5501000945000700140c807007160256222829a0098002c000c2030380c4071244041c070800e0031000390343d440c428420402d1450351079005a41c04000d0740d82d1007d15201c1c05000b40090b03180e031203c0c82d0f060f40d00f003071200e0152103030310740181d440190308400701007008201107130004508032032003100d0184004031910341801e058101c3d030041c9010b4020790b01003007099698080c0700001d000580d070003400c001d880180451108010f8101a0b00000c0409401080d4244aa0180e181944a40c88400030540 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 873420044 1250 873418794 873418817
    0x30615010f020a0809010c0f0b0106051305030a1101121d0a05061806071d13090b01091e020d11040f06030c0c12080702070f0906080606060a0815190303 67
    0x90000c1044241207071800145845200c541c0c65034160b0140620b2941041001c411000c14130170198402e160440c0c11414245144d40c4800f4010000c1c2c1c010400e480c010100704000041c541000282010100c0d0080c44407680519044011078500e55039034901c00d2001e8892600e01c02510341581564850000100180181641840c01e1820880020403030910b841c03d444d40003669290201d8007a46c0903910340b41c02807184032070180030011642d010400036040704103a03144900314401c44d802240824040d085c00007440c0ea0b100030010944800440304030b100c4107541200300a294150b0080c102840e24a2400701e107503040d074442c5030141d400c07075807051081d40211482003000a41607c86d40e01e001c105440d00e82c18000054840e11200015680c1070b0040040d4400001c2042e031090012030050101070008000d480d50700c14129002c1c0010740649002805214049502c0d843e2480485d451152291210181c82e40d92904c0c007180d1000740e280310f60704229001c030038500f07e089240c080c2d400f651280e11040c400c6113 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 873421294 1250 873420044 873420047
    0xf0a0504110c0d02030a091815080a0302010f02040b0a120b09040f0b070305152724100c02090c0c0303130303050603060108032b11220522020903061501 67
    0x180542e0300f8005541080001803200c0d036000110400341c4880c5008141e4a0040301410740060041030100c01d00001c0c0502d0100d00d015001c1070301e0040e940a80d009101c00e03108131444204903c16449a1041d2200400ca0100384070300848074070760340948040000601c128018080f503d240d0086404890304440c01d8141020820584080340d004030651504101c40d1404075107081288004440480c81981810320070407012420000c245602c644155580f0203c2c2426001981e1846440030042d20300350182d00301c2da81c0b038248020502a4031a1695844062149035024072402d00405004410b0300300e000c0048684203501040214020000030703010641c40490303070800500329180a42841c0c0309400000040040810000c151800fa0340320603491a6283c50300c001131140e2200032111031403440e01300b20b0400c040343c815201500b401c80101c0c400342c10900807162a54104a56402501c0e84004414505c010302c0601000900c41c01c01c482000510300100c40340000d150410880700304c039003240c0c2c1300b400c00440e5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 873422544 1250 873421294 873421303
    0x1032d021c0209010c03030906091b05030d020309030c06090303040306111809091e01090c0905010f05270402010c0f050f21070f0507050904080309060105010507030c020f0a0504110c 80
    0x201d401900714145109903000034040030f00042c1c09800c146e140c018042c1400160b41c041c90395682d02004101e00b03a00c1c141108203460703c4610600b40b2034018441c241d1011030010045400c1804001c01400580d4240c01c204491504248500c6405101c10300000c00040d60510844610459036000e081c3c484201c994240404e0203003819850040b12a1814003c1f903850010301d50000c00840203d0080c500030b0307802101d0050090001c041d180d015603a00c00264020f05610080c181c1d00361007020005181c681044c1702e00b83c0a51a035100000d0050440c004000c80e800740d407550414414500003000b04241d03200d20143e4245140d040c1c0701d41c1c00140c108400a0001c00201c541c00b41400c2d0913203003d40750100c0260b118090501c0241400840e191003a0070807100b441420054040113010062500305401d0030319154100329000c0322180326010001c40c8560060b000c3c2c0c0c810307c1d410303510112142050b9003442029407411030a039801281c502008122075441e4080c00d84510b4482c107007030307441d00031300f99480340340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 873423794 1250 873422544 873422587
    0x510020d0b18071d18180105040b0f0406020d1a03060a150b030c0408010507020a060b0108040c2306040801150e01050d03050c0c030714180f010501032d02 68
    0xd4080030502140742c0358640c40180d4002128100f40034100c0c103130455900080c0d16100d91a034010643d00b1074940c0000ca460b03000d0b00070b04801c0144c1440c490b03584011822280180c1c2d0162a0790080b000064842c0c550407165544248107410241c01c040c5c4050041050740c025240401164003031184004071400c00300103280d404a8214030a10150f11316000c540c40c2c0d018a809200e4000200000040d00039418500312401000135100800052501220080d200c050321039007181c8180c20907440b0700c801d41c414503545014503049400540c6440c07801040c141d20280d03880e0010741e5a100354458000b0b40e50ba003070181004029003000492024200d43c800007207620f09030041001290180d006000a1300c6a0200a50380c651608049c3c2c0d44100d010000c0307140039906203c250703041c40b807000040381000780026246000c5005460103000f642c0d0a4494040090342210080e0500d0048070041099603c66046154100c01c0948a91008080802250000700004944c2c00010340c0021300300c500389280a24013101c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 873425044 1250 873423794 873423799
    0x36031504061812024623150c030c0c011d0d0909050910020309030d020706061404020901020d0318061112060604060e0d1106070308040b0903090307030b040c030510020d0b 75
    0x90711040800319020700c1103803010308400c0d5100c920b910210800300d0412981c41d411140184214011003502200359100504980e814000d00e800c1d54020052003c070b09004000f02c5a05074156500c841c2b582e002604880c00824203076480e0010560070039030520100b0382012410707018100c64074002001521680483e800801d03200d280c10704000d08480c010804030000b0b4481d602c0540d07244c680d025102e10b18041e1080708400c2c0da01c001042300802010343d01010403549080d40412800103250100000c9006801125015801c111100380a0600c294007015203d0b0901d0342900710740c1d5280d03e4840803162807042c0c0300024080091112203000c0c0c09002c10b544988d04949641c94542409002400251a6084c80d03018152100900c0c003002030b8a41406a200d0300500016110b17807075030600801001c82903d00707031081c104e4000401c4900e0004403c6460754800500200705070391840d40c0b8000c98440003442516840e10451000c0f00080c0180074014075a480d180740580c0391881c803e1228115005c81c0030507031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 873426294 1250 873425044 873425083
    0xb210a02030c03070f0504022a070504110307121e021c061203120b030709141f08030a050d0b030d090e0a051b0307090503033603150406181202 63
    0x71044110440304006c0e07400c02d0f41c0150b200c01d07105480c99481e20001103024154548040c2c04007652a0007d080c5049032000c0b541400514110180900345210a503100e0340040d205954081040d00690001031300309071518040460403844074100c000302d030442144c0c8000c0d1001d09070042100c4200b1f00801000d0035002040360104602c65401421381102003003044849502d0b80c0904086540c21701241004041c1030405012404045002205c50303141160340400c0d0041c414440c018400c01682d804082d2260500154034080c1290b5042d40c01d41c10524004000548504982090751030a00c20380740314000d16100c2c0c5030160700f00004201481801840da084151910040001c070140c0310607400ca1b082d000e220130301c1d941d80704e500b4101d49a1441d40c0141d601417100003400c5400750310041c0e54427a250600307103075216859240c030301c8400745101d80c020f215030682c4a840306407010f58007099015041440340034009031100240c0700340c2c3c80e4803401c100291402d5103102c8a9804494051191400f036038040e15501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 873427544 1250 873426294 873426299
    0x180c100903050709060806160e0303030c0d05090c130b210703140d0503270105040804090c140403020f0112110d2304080d1d070302010e06130501030b210a02030c0307 73
    0x1c0d80d581e000240781c481402400307048da100c03d50098120004003800541901d80e42d00d002e0282e00c10651080403001c5030a480e00300080c940400c003158186a11900504421b21582c405141c03802030302d15414869488494a05a80d4030010700303024400030301044038085e1000f1803841c20054142c0d451000036062580110600c2e03540d46600004503079104004003806a48204020000d404810440f88411320070340c03801c82070100707110206010f002259040c810602404050840c1100c507004601c82c081d961000c203100030702c01880c081d00b00301d035480c506140040751280109054010355207650908801c1c080009500e002e480e0443c0159646800030015500c000242e04154245542001300085c00c000e4021440f01d0911504d50481c1c4c80c81e41c45078a400d5802500b0718030060710b5182e20302c4101d004c5007140c00c41102c182410400d0b1180401c101001c883c3c0c45180400550141c2245c1c010254011030041d8210880070705600c0740c110b084220380062102d0b41c0c2d240b0604d4980b01c010362101d846944541d008 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 873428794 1250 873427544 873427559
    0x50c0909060c03060d03090b0d0b031603200f130c0e010504080316060b0406030b2d13030203071e060e03031b0c03040f0806070f1403180c10090305070906 68
    0x303d0341c201400f52084070001500c0c1c1803ca40140c859005002500d0000404485404090700032855003d0700301c0651703120520200004c07268641c140700c0105a0450101c03c8240200d10b05040fa0003000060002d81d1240c140d0800140c1040421801e004060369a50341c0d080c005074070880c0504d10324401c1c20708902c0e040c1865102503590180d111010500640281801e0800001780c10211209402500c02e11503e612481c0411422008a61074485038080c102e1030110100c2d050100712542c400c1e03000800050301d486510440c40000003100303805501c810061400018540381c020000b4440c01c46e02000c6804640c54080c042c2e58200c0d68680c003e074000d10a0140000c0f075039406580d40070030001850340d01d20420901c50705501a983c8004155a88050b000070002c0010030068460036040c5d584403401441c2c0e4030203580d0001892607500340884184002862180c5008a407400d05040508542c2a2210400003606411514000c50700096000d1010002c012041060301c019100e1683d040c05034900f003142 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 873430044 1250 873428794 873428797
    0xb03070905090405070b04170105130308070f11070603020c0c0d080a050d1b0309031103070b2e080304080f0a05060f04140106080109150b1008150d050c0909060c 71
    0x1c00748140d00150101e002c0043c100640002441d035250020b0302c8130b0362015003900904980d483c00d00c0c6542410300007102071811385240000b455150b15000d2040c1ca40202c11200752000010002c148042600001e200d100200540c0c0002c00043d13502503541c2a40038040340c245403086010358001c01c0c41c101498002032208082d652244000d05e0110b45a032110007041000e820300d4560310b120748109140301041a941500214074482c0a912008040c044028484bc5da920034000c4c0506450245004a14102d141980308000e0000c801c2001980b42c000012101a1026540c082026580001070811640340c3c103025401d42c100004012348200b030354903202c1a444000c0100207424841c0c078240000d0801042a0600034086031103070003080020303168411240240b46800701910019240c5481468040650252105030307200a040304189a01c13a100540d400307000540180b4a402340d004815170203484640f501c1e10000c0c01040149484405917084c061041005858240c1c160400402c000000038800f0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 873431294 1250 873430044 873430049
    0xa0b0a0204031a130b1003080d050403020d080f060904080f0c0a050f070b03010e06011106010e04170a050d050402033d0203010b160c0b161106180909190b0f010b030709 74
    0x445c1803005940d40300d00200340402c1900020a00d02c0080795480b215a410707800b1500c03a9100c1d03005c444080304404001c0c1c3c0c42907000c90b03138103540d04422000036400782008144aa08035100d0603c1a08005c1940804500780d0465a80c030b0352903a01001014050090400c841e400f0410601c010b0080c180c03c10302e412845100500a00da1200c040c1e002090682c1d214590046140c1e800209a0f1580e584501e80d129000c407003541c00390344200144124a0f0400703c0e500c11140030020540f96585004040c0311002c028100081040e42c3c18085c1008418101d00301d481c09885000034106090098128425400c0b0b86450701400e28488a00c18001402002038080489030300013064030081070014440e2801c8804000c054001000c0c0c0180401d41c0031065aa058840c0d462a1048100d400449449002e01c042805218035103881d8091041200c161401c05070b1229030048001d50903103460700c812040c1030321240d0030700d502110b82c04080020020300901460220b03015001d401c65203495400c007418000c140c0465070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 873432544 1250 873431294 873431303
    0xb0a020a0f0501090c2c061903050f0715080115030b090a0221090705062b0603140a0c0b0c030706020f07050607030b03030d020307020115030501023004140a0b0a0204031a13 76
    0x6902041f12a80e4081010b80c039181040c0c0d00d41401e903140e2404a86036201081d10380c17141e20520502040e501110343c400c410b0b0b07580b10f40d40d2103041d80c60124600401e20741900c07810300341540d6914152aa48640090074401d0030722900140c0e44061120041411031881400d41000100d55001d024948501140702000c9030300c100d8950341c543c810007000981d11b0000b000590070b402220805030340c208140e600050100c03401070220048000c01c281c0340c00e490711070300480100010030825040c032991000402400c249425401100e0402031030f030351500102c1c1d0201d45c031075012a1001c100441003160400242c0c0c0d11040030302e0140500000030010036964052894400e048a401100180445200350320030301c41421152250030503a556420264001d40c400a40107420958802e10142d805100740962440c0c081d06240c003081ca0307901e41d221200c030001085200c018078001c100e00380c001b00e0803068081d0701500d9040d0300140d41c2c0d417a51405031140248030301100c2c0d080700903008001c145031000d8030030302071035411 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 873433794 1250 873432544 873432629
    0x7170703060915020d14060607030f0518040626030a0203030a110d0504111e01120f020906071104050a0603050d1206170604050c0d08040b0a020a0f0501090c 69
    0x4910f80307003034600b00044024903072600c082103445220215400600c0399440308040380b915030710349109114403841035210217000700d105481c080c00c11501c15001421a01030200f8403a480c4200c80000a017a99190350003611089460300564081008143e400c41c0c281c60241c00441c03a0542c40c1e08080d4490000800d40c00019a880c2e280f0460200f41d4011502c91069044080016161a16201c80284140e241d61400788013a110f4808401070400301100400d01c2c141c50300703804200b8801415026200128410344410340034041c3d03c01e03a88940d009401020b220383c45000390f503945035044c0000c5820091220041c142031603410004103102050036984d5002d545046040c600d0300c0c040c808060165540030105103000c0c0542e455011001280041c09140b0400984200c1c0300c5002c20444036244203507010b011200c0400041180c0c140650082080b5412801542d408203040e0300d9420202120020a0360180d443c0d0040788100046803009030060120480204010320210a07404081c41949508102c030f20803 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 873435044 1250 873433794 873433811
    0x9050c130b0d06030b160e060405031905100c260f041b05031f0f050705040b1e032418010504090503091302190503010302100f111e0717070306 63
    0x810b810080c041e42d0410752520441c1084d01c8a584480c020003c00340015441507c81c003030629080089801329007005000303100075107038000c4807a40509011012101d510840410031410403080c007841036000c0068488400c1359a44c071000950001551301c1444071402d51a0400008503440710b241500325030420502c800080000e20b021844142580000340c0c98415410034908075007810f62a400900350501060020043e0030040340c1c180c2d1019102c0f140841c0c0244800d20400c5c000d28080c040d5200150018490402941a441e040c2c1d4002d895142030003407000801c40031a8280d04003114001c1342034600301182c60007100074000400301801680d1240e0b4170340640b00180441001510080035004000f05042a4004440c01c025071103640240304c24401640075220050040e0150f0f412690060108200301e400b2001c00c849014040070860144070b01d140c21424100010880b90748400010340807002e05e21283e001c0189041019400310001d04964042043c44a00106064088a40c0071202040c0d406 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 873436294 1250 873435044 873435067
    0x3030106030b030109022215030203030708032502030d050c1603050c0a050601240c0b061003182d0302120c0106030f1118060d030f260109050c130b 65
    0x1c03100006e91700004014040d502e801e0703008405000c1900200041024660403d031380d144041d0030b0321002e50300d0381040c02840082801200190391040e1400100d0b050f080420049a02d84c0e10b8041e001e80044c0d0000c1034035489460749206980d00441d13080c24290406a4202000700642101e081c01003c1083c04152001141000c101c1e5441c41a44001900c40b43e684404090100c078000500f01e90000c1c16084514400900400450a4442d0400c003501b40c0c2d40d5074007040c400c10141980c825400c244d0768086403071280310b1400c09030032014850041d82d8041c60f00d180800c041d241c1c4c0d00451086007200345e0940000a40c0001d000b0301003e1030031301c5446c1c80d20306004140c0c3c018142d03a4400b41112440700104000c21856039020740b0340990881306003040764100c504040f072a450844c2c0c3c981d0064400004040403902400410b1403d004d18645032503ca25014241e513400307017454030801450403c002c010300003032440303002c1c0ca40e0004009056504110004c840400f1210320ba22650300342003c0041c101c5c4806 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 873437544 1250 873436294 873436301
    0xf110301020c1902040b0f011209080d020d0207030809120a031e020403050d14042607050319030201050f0f0f0c041505030403020d0c05030405060f0705100b03070e0903030106030b0301 81
    0x1d840d0040d0340c40741c01490190030f2000b0b02c00e1002c0f4850351400100c0203843c0f403d514241c00f0404103079290041a1500b498490040195407019185842d0a11a440c0200642d00041c4541b501844000d41c5450071454003806044000d8040c901c55080203809100205e030b190706444403882945400f280c0704500c0d50811101411240502c11010300004001c8244040003e11051150540c1d5601c2c7d8412211031b100b11890140780214155030780034408240c1001d175135040c4003001c0340c008026580a241e40d84002440c01e804098103003000c0c01c588410b903089c1a028070905500403900b61002c40740d031030b140021441c03c00780100a800d200e03000e040415810554002031358003421040314040811000c3c0040a0329540040301c0440040c854070070640680351041d42c8521250b036105000714145400c01c01040000c2c0c000d4944000221020f000301d401081c01000400c002c40750070007002807144142020b060510200da01b007146601c404605206400134008203d074110341527888d00142d98203107000002d014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 873438794 1250 873437544 873437557
    0x90c09042003100f050310020702040b03011d1005161b0816120201021608160609060609060b1201030318260c011b11060f0307080403080c070f11030102 67
    0x700546048800362052040214000c00d46240c102c00c280d5503401c8002654015030068907055040501d500380c080080c3c0e00a406101c0c40100007195041c0480003003421a00d02c50a80044c071011420b8000b900a014051001003c142c0700007400a07140034558182410124600b0004000191f10b86192002d000404d504d02e4661102d6000c0e40c07500106c12000715408010010b84481c0418001c2e0387c451401403080703c808180003210700402905c207441d16602074101540c22075050000000000c00640d0038424201e03594414440010300c03504040b000030498046411560408000f001702c0300c1d030145c102241604481c1c5c0351400210341041440c4900c03d50516921a508400c004070401a4901410890240259424048070050514840111040c14020302c0c1c001d61108050913200200724482218050000e000d004185400420010a035861748212000c100044000080c80205a130201c0ea150b042001100000d0601d01a501c07100c1a00722042002050081c0f4585040900e480a40681c3d01c1c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 873440044 1250 873438794 873438821
    0xe0303010e0a02041715070306142817060a0b010c0f020126070f0801062a050f03030a0c0905180a090210091d090d110312131a06090c0904 61
    0x418905e6a0060765909041da2401034900d05900001c800c036100344140c00464400c2c2100417220071205003480480e460600e503c0540060322181a600c112810740c00c00000c145020740e0403040c0c0d0702101c4d03441c140381024007101d801c03a08007020307140b490303070300000303030002150007600141800105200503904c40c19802620100c07403e0506a01c00c10207001c07001e0503c150400c1e155110048140b14007194007070000d014240c049070a44040d41e0b20803491910a501041611101070104080c2d61141c3d03103064107600d00c02150354000010400c0c80d10890069850404680c1000349296061000080b04a400002c001d40340c02d600b0b8000801015981c0c0103010059005420200030120007080248070340198062610044a10010345c80d5812804162070b1143c4007190240128021031402180c5001c040c1e024007010344400e0008c0311041c840b04441c90301840d094098600d07030216501e4901a038000c00800c40842000640811555440d14401c8503800180070940564603070816000074010203070442601d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 873441294 1250 873440044 873440069
    0xd050a030e011802120c0102030a03020a09170f0706020c0a0504020306031504050105070908061905040206040b12060f010302070b0f100906030507080f07120209040819020a12030e0303010e0a0204 86
    0x180062603c1503142a218003c0d100081c9809118404a980340c04503280f0380c2c01030388100528408a88680e000d000043d11900e40384621569499046454840303299207170342c1c25000702e01d0381310704018204031600051540380068080070703510b040002e40818251107800e02880d00000000c0c065581402410241c80019640c0c0c11182400d08020f0b00802c0d003201d110740490745c4444c02040d00030740024034034402d0b00e103640e40340030380744a04101402611000d0402c80e0403880620001c625400d40c034014009100058400c18241d1909030104a032860708110500e05044c41001031b517000c6440b1100440d808a50f500410350242c130f078016040794400c1c80342e100a030307054541003000c000c121000c581d880444407214203c032218048501203036121034061049400000800c401d0310010706007011002d6000c0d003d030380658140009400c82c541c20607103004c0480300603003013126907d040040408440c640144c4900d0108603140e08110b101350740f440180541154030a0190000d0149020b40c3c044030007070102d00d0020f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 873442544 1250 873441294 873441311
    0x80d0c0c12030f140f0904090212120904050709030305220f0801050108070b030f04060b01022805060a230402030c0301020705070f05090c030703020c010b090112020a170d050a030e01 80
    0x400151000c001c50b400900e05600c525500306890090b12140c8001001c446d1818040d501000007c240c0048120303000103801c424903140740410b1003c01c7c0e6144410410b0340d600c81d6958104811503030001c04140600c41205000c0c4003081e4050300350307001c0121030b140c100060310a03c0080c20101d80f8a500c415001407510f4404525010306400141c100c80000088803800c41c2c460b44590305c1800b08540d0880d0b2405400d00040118550303800014406906005403020724408a03245284081740d14450400c0c204051880b4082000800103198403203410342d42008604a201040400000b907000c103002039100200104c2c0555406000c100d000c180700500071517866800b441d04070b071110241d22900d102c1c00c0303e08200113003604103102c0944c841d0800e0300c806032855580343c01c10340003500003009003900740d1f41c0c4032407070459074840310211806410b0490700c0c030101c5a4207104000300c1c0e180d0780d007000303404282861809100c18000600c00e50100711724206151a8007807000114001c102a0784403104a600300a800b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 873443794 1250 873442544 873442547
    0x408010608010b121f020d0204090614040509190507080105040605010503061302060d1d0a0302011b0302040e28050f041a09060417280e0307080d0c0c1203 68
    0x420455035001c00074880c651003003042219881c010741c0840c1e4aa048040e410044010096040c440592804001402c0c840c040102c10308980058200840d00c650b290824054640d0300c07112071032084e0088900340941e1412480755a111100c0e030054107681580f600e402000c01030b0502211000c2d1454000030041031806040140190000303128090090203007002003a075080c43c199000c681c15801a00311072402d020180508001c003041849120040c0c00746880b40c1c11490103201010781c0f20b00a03800468220000b121610140803001c00c090145481000f040040c40520b0071982da01003040764101c4110b501c060040c2103a940c41c4644055150b144c0320402c803540710011101400341e0701650f0b40b03801201411101a04081c0b0a4404e0000c5a101000003400915a0106c1c0c0350402c0100c0a22030603c803540450b180028141080390300c04844200600b10384c00d40c01641c00031006c508030000e240712072600c40340c5515404038a05030381c00c01c4400700710142440360307990344400100071041d088201100785080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 873445044 1250 873443794 873443801
    0x100311030111030a06140d21050403120c110118090e1e0d0f080403020c0d051f061703070b0103110f0a0b1905040609091d0a0b010806101d0901060308040801 69
    0x2841107001c2418440e841c18140391240c50041a0702092001461303141980301004441840110388c00c0000030800400003c10b00448900482c040d038840000a0005160000079100c0100c01c2604001c8800c0d0110f4000c052940b1b800e08a03406900300140320503003001414140140c00800103003001d110404000c0700700700064036041040d03107541c0701c141d1091051811128910300780d8000d001688010004041854181c000c40d58140c85030007195601d614048440512689000c0c150043c0d681d501820080390341214a000050b0502030b0196240141c0b035925030159a1040c04050111040f0a0004a154403001e800000b954401080240e24a0f51600310f81c41661041c0307a001d8440d030072500d0303030640079001d6810345044c0c40c0c25807245482541420f00c020002c3c01c51003070003c403801c0900d0340701035581018071226003141d014042d24012503041542507881c0101c007900d2032195581c264000c101400b10307120040c1c0788182c00c4c641e0840741c0c2c480e01e203118094012500060701c801030008001518201c1540f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 873446294 1250 873445044 873445049
    0x3010803031b0f091905040c1706100c0f17070605190506030d210609060807140a0311031507050d06140d0605044403100311030111030a06 61
    0x450054981020b680e5100740204451145032141c18059801c0d54a009004215064880c03000498100e9940c0d00050a40d0324665001c1d021074a10440900105400f12445910481c00d41d00803048603102c0354010000e0709112006803403280741400103810800d1780d03503a20200e82c82c090304203610b0310307000e050240080005454000046c2d001d010310100107141402118422500200580101582c600003a9400941c40c3c1c01d804d10004941d0710480d402c0c0d800c1c8100c40161001480004845041c48081e5141c004541c100020000703142c00803034000e80d02e4000d00720950394080d00740910000410040382c0740c1042e00c0805100c41400d40c0800007580e1b8024081e0014070400c0b4418030136182e0b035598466045401300040b580001004004002080003908150707089803250116600c0a5002010418100702c0421500d50b00402014071084803071f45040710b0844000b13400d104501c0d50501035440c014120880c032000b0409100d00d10111002c2c2c0e400e521000d04007420350072846e41c0f85003e00c060002080d039070 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 873447544 1250 873446294 873446311
    0x20703051c210f14100e19021b060105060c030a0e0402040e090d0e18040b0403091706010f0b030603030304020f012f010e030c03070b090c060a0c03020c01050310031b09020301080303 80
    0xd138408085914812802e03003d100c81c000741540d018248a01c0419a0b82c0c000c00b50020104920200280032460b0b1000b07201448000381d0485407183c42c0303103c1034240030060348001d2041c2420700035803c4140d80407084600f00689820041164103c82001c600640903940c81040c940d81c5270410003a00d00001b18000b41030706000d980f1540481c50441c1005000f400d41b628a04031030b20711500040000d032800c412540c10034001e0428042e8150b0390320307a4403140d40c3d4244104020740c000d04010840740c0709207502600031b03200c040c00203170031803508002081c0c1e0f81c00010000783c8a00740c100324102059000b5110080360029205451003142c107541100d04000780c0580c0f9a48240d840e184080450f03070703004030580384941e244201440c5003030240e44610031007400203002c1c61914021120120b41c0703070740da1200070080f144031903d03058403d0f002d5003000780c144208449414180201082008032200202d52180240d942c00184501d80282c0c005240000301129004816064030000022608240004c042c40c82601d61 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 873448794 1250 873447544 873447551
    0xf14130318151215030611040302030a050d110607080627010f1d090c12010f0903030506040e0d2313060306081618020a0e030d180501020703051c210f 66
    0x1050001011604c2c50801c10311090054807040c40010142d400c8117a0000381080c586041507201c0d0006424081000070407645030340102071502c0142c1e0070411300c10064004001800881c030305510060125480284031501c600c002203070940a200d00010102e249070b19001909000e0368482000d03030010066401440490b03009030304041225089500d020303114240300409001000c4504081c0001e0640b5401040859505c0300b000f0303551902c0d00e2041103442d900035500401c81d1704100d0144000c03206050701d0320031580c0007400112811500030f213080300401c08070180c1c1d100d1002c503007064400e24060708416420001c0324003400214181e03d03402000548181100740c0350004c8000045880c000098420201c00b1081c2e002141c03440d211300d0b40a01402200d60400c00b8010a50200090405010700c201c01d0108121080524070f1540d01e1441001074102800200340546c115122941c0c0c3d094541ca010340c01c001501000e440c0d9910440700012a00390a4803003128001e080c840c010080c0005d2003070403000c14039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 873450044 1250 873448794 873448817
    0x3020d0909060f0b09060c010c0504031a04030807050f0702040908030a0509060f06061b25080c01050313061e061d012925060f1413031815 61
    0x101d204050846000c5100b41081c3ca290a0580c61541c00050001d079100c03a00340002c0443c500203010794003880c021655515940c0b800d600d000700301e81c01c00e00321002c0d0981040c0c040200181d00801758541020703c9e4200203848807500c0300c09244034882c020380250002d09058901d41040a0107025500a42c00e581c4103100c1951160020b0f85d42c0d080442e034a034105a07442022598508114004058001503900c1243d4040400502c40349013180d480301810032034030340542150b803188840b03441501038000a8050301c4240200300000300240405030441c0b011040e8403c1c90703010002c00b5806001d414111444c0540c91498400c0781000804892254a44080781044100d41d60040140c140b410380e42102415448641181e43d041401d080e500c01d01000c03038004003d41c2200c210b210418a03c02c42006401003030300c841c5480c203401a54400c080080306030b4180041c0000808641c081a0341c004601034181404500a003070403903404280310005145191a66004500d00c00c01c181c0c282d0b03e140140c0c891001621 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 873451294 1250 873450044 873450059
    0x1801020a05190503100b090604170c030c030706050403080d0207021203070605100612150e1003020a080c0a0506180411040e1509070318050114010815150d020103090c0303020d09 78
    0x30007210b000c0d12175140c0724014420584940d010b4071107402d0240041d81007580702d521540c040c2c1110124004580c0c44281d8a038080d2070104621504003105501800c0514a480030141ca03a020b40c0c00000e003c4500403070ba61800005a90540300100e800400900f91800b001040680720740c0081c50540b24542003c0015905440c2e91000c1800c4510545e111a0380020b16600752000748110704012200c1345000c000010392082010129003d21050310241b410207140d0700c10442c24040355400784109402000b5101c500380d8418580004485042e11030940c0c1d0802e000a03900701c0504106a00d90151800b5200b00044401c000a8410340e00c030556042855154620000341888448070810303480856034000030f182c1842038220211003007403c1c1404408c4c4c0140d680701d03829220304074400101c40400000411149804104000100d09087e071a204241460b078001c54010074800225400b0714403404d504803c42e4483d5100f525581e07046060ac52001381c07070707250017034803070a260314072200051080c0d00c0441c628 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 873452544 1250 873451294 873451297
    0x90308040b0912030f0c0c0d050c1608100b031603060f05091c0f0c050a0b0a05070804050a021027060323040b0903070c140301150605121801020a051905 67
    0x1d0540384965046617100c0c4401c3c112030000800d102500c038014442c1086000c1d0402000c416048541c44568075143c0840c01c281c5046050084140c0b44c08282d001008642400b103280c5071040400c0c0c0000c60440b4508000c24500141c15035801850003040300000180700090384044200303040f01105009903114078ad14a5905d0130080f0301c203100c044a201440c0074590080410408100141c00c00c0c0c1c40d03501071511000d007088100b6070300f40e88402d0700b4010026020001e104095001c83c1c1410b001540d420162a059560071020500030700903603100b000b00c24954003643c8041c0e86540c1002e4000007605400c038038440394405500c28400808c0c00d1a481c41c030021001d007101c107040340100c07c46030100d07961038654980f00070002d07050030780a000820680340440d11b074407481c2001d80000c5440340d409800c031200785400c46464041038800c80e541d10300e007440070070b6001d400c864204c000304142061680b076403031000384680428207900507031350320000c1c0c100d00a0b0340100c00b0b01078411340729060070600c40d11010141c426 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 873453794 1250 873452544 873452563
    0x60c0b2e1d090d08060a0f06020a0b010f080304030f030302120c0901021209011202160f080c2e050a060b40050105070f121d04060e0114040b04090308040b09 69
    0x454010020100f01d9920981030907078031000041c44104800e9440300201d604505540001006070014401c000034800107454032401444c4000d00081c003a0710744081c039a20b0b0301943c00028400615145100c0a01d48a41c041c1d420b40040e00c5040d07003a5081c03610b0910801e920482020340540102c9401d05400d07070b807030341c1950100d183c1a1150074500c0d0ba400300b070100070b6001030000c0305140500c801c2100458586901c08600c144201d112070365501c44003986ea440c001c100030128020272916100701002e240264060001011206804203854880c0081c0e42d0143c9a20b4001c0d510a1f800403820038035040340d919220310f02d540c20042a5040404001d0b0813002c10740f201c0d00342d507141d0070603171020422548107600a01c4a207006079400d6041001e40c0c2e40301d140d903414100c00800007404403260154100e11039a46d5151080c0221401c200702ca1516a40502109051186070a0f081848441045036112074101d40070041e80280100680281841c02503e4410700342c1d0195108004400042d040c0c0d2800a0080340 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 873455044 1250 873453794 873453811
    0xf0302041a1f03021309020301081606200a050d02060a0e0115060c021305090309011b02030a0308060d05010518070602070303022802040e061906060c0b2e1d 69
    0x1401002010b15850b8061a0b0340402d03a00300f1030180f28420018408001c0c042011003d40c2d00e5241444580c079210106008482058460400304160781d000329040c0480b075046c20540c2c2d19110085682070800082c180080c140c0c0c06071454040002e03502190803031248034004c82c200801c400711300c40d881c2200c07070b041070081c0c420f8040c000620506002c6c0700040394051000701068603160361075071060f094410030740340005c166102040c1544190b80000342c900040d40b00740000411801c15400080c0e035500c02880c0a828840d03614081102502c2c1c12550050a41c0c010000340494100301c003500c050794090102150b071901a80c1303804203071148081060000c903500740d4000c0c0701641c8041004448004079420182505c09069640c00042e2140d0094a500c02141006882689003042e8030101029020070309900d540e141c44800e0142e42e0300040782d169415044449440755a852252001c0140110024210b0130783e40d0000010305414001c41100030703205c6181c10440d07515003080f02e030101c50300b00b66030298 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 873456294 1250 873455044 873455059
    0x1104034b06090809030a0302100b0105030609060d141f050106110d08060a180b0f01030e0d081b0403200102070f2c010f0302090609100303110c09010f0302041a 70
    0x40100c1c0841d00450429401110058600040a00001d103800d50b413610440158015240c203002c1c1c007100784604e001510080c00d0032485c2d0315040001599600c0001e107503910889425444a040c060b2b038008204490300720f181100c580d0741c2d440074201030300503012000c0c4035600c0c203100001c42d1061040b48030158000540b0000c3c110302d0800401510000c000070310f0300c0d400201c640000505000c0850503540e07611614000001c20b101688140314000040421881c181410704040d61040d11b0006a490f441092502d07100c03086440d180e018410703503180c09006007000f540200d00441403020708030b03c101100034400180155030708104010383e284e880300d10031501205000202046540c0d600d03c071500400511030070130185010420700585e100c902c2a00a003040c40504a030920450500a40c003d800400482e6032071424507000110404001e6240002400c10500c80111300794004200120b845800006040700c215603100d2010401032030661005074459410400034822107a003814038030600071005420030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 873457544 1250 873456294 873456443
    0x8030304030c170301030b0a0c030902030304050d060902130c1b0f020411070c03150e070b0904111216030507050a0f08090f0106260f0709110403 64
    0xe941d002c00341c1c0419202d12040801c20307a0060007440003035010b544140401440d070f0801010103000c1340c445540040c2414030b0103000304050381d0b000054504a5000f2100c1002c0d19009240480c0581040a03000f500210980b003030040c0c607006900440d040b00c600d981d48000084050340b0044140116100c0070303203803080c072415030000340c2402e030071010002082c0341e401d500c2c1002940d960110250b0f02d51040d5208450680f6000000b034050180c44048000c8074010b022450038206041034502ca0503000030301c2079030b6400c0f600e03034800d00701400e4403003c403410030302c0841c01c0c1b402000070346005585200203000246030000113022603000c1c1066900700d00003581e502c041c400340450140c41440e005048482148118104484060310900800340501507140306442401846501c0400d100b02641e032407003950b00301c42c20503280c0340400078080c411510089404190203140c03404007251403250381c2002e4502e01f42d0440800c5490048102001c0381600e811225a220550f480700c5000c1c84050119030900700c0010448 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 873458794 1250 873457544 873457547
    0x211b0c060f02061e04020103020f030411030c220c021e01151a072301091a06270411040218150a0e04020322230111250503031806010504060803030403 66
    0x31641d00c86c0c418100149030009600c003090183d00100d408403541040021070505a04091041e0301d250b00040e00c10040b002c10038045040008000c17480c042e0f403030b90b44000700c002041c420400002003004500701c094a85d0300e991202406489001c03400030800001210000b030144005600c440518000c4c1d22050400c20183c1c0d0305c0c0790462800324459608029101c0059200301c00380300350f020a030b2150309180b80c4c1d0015800740d00381c0e540d4010100e07845221464192038035102e00700070b00c0702201d8250039654401d507164a050329054064851040d0000e2012440421070310209092403410001181d0524501c80b000c203641415209116129000506481032800b090602d50042e540041c40c0320401c6a2450b1141503c82d00c80c4004a0184c070180003044110f001e6440e070002c8110082e09030030081c081801180301e400c0306072066a41d903401daa44ca80740d807a0380340180440300c01085a8840709480d070320f04106006848507540d819034100c80c0d0103210000501403403d0321500c4122038141024500307656940d00c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 873460044 1250 873458794 873458851
    0xd0e1e0304030b070f1b170d060e090604050601030b070210050709080c150a030908070807051e0f0a1e1212060522021c0234211b0c060f0206 62
    0x800f198483c1c114040c0c02419520720780034001028184100140312840c0ae1100352001c08046c000b2a169049203080c440482c1c0049449415290000044425626010004ca00d440100c486d200d030410315003003c0c018040e5205c540c01e01103da20b20101c820a41454040043c00342800c482860324000800071101e0242c066001080594081c0521500b4400c4503100c09109512180040318070380c00408103402e844400107075504045513584018180044003101c06503944080040182044940c0411100100d0150540070070a90744440ba40d0268004401d018010f400c084904441c070350306010b4041014101440080383c543c0002c0007984030710015034076481c0254096407181008003102c20030341183c2c0d422070005165409610311071410307d0b10801c0741443c1080144440822908152120f180894413002d101806255110000394940c403960005940083c42d4200344103002d16100d15441c10b1041c1002e0003021a44036403252395045444140480c1c4980f02154000441501c1d40c182160210ba09030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 873461294 1250 873460044 873460097
    0x151f1404020739030506190b28060c0302120703030912052805030604150504180c0b122404020f0c0c01030e030d0e1e0304030b070f 58
    0x104014074221250300d85004400c0024200c0c0241c1d070b07a40045070300030801000020800c2401c04040c0c0c14140c1145e4560ba01c803a0702403c609a00c60106800001000036035105c0e0710003440c01440c080142c1180c40c00010303503c2c4445161075030305103420000140d0354040d4440510300e0368154044c050320710b400d4162821a0304450340a40c03c01d552342d0740c0603000525032011250490300c1d640383e681d222500e0702d5540c5c45500450b0880303150000507114110001303400509403500000100d81c04200c22151107645801800142d1005038014200802c1c00c1004d88040310341c4240c40e00900146070103e031900d004c0e80061099202a84441c0802400182d2401d11850008020144003100b41c42ca21071030800541a604004082c2e652141e00042884110104000140d210701e4282028000301c0308594005449000702c040f080100c1d902c171186142c95241c280041c180618150010017043d142160440c0d99907001380c0000c4503130505801c0411070840c0200c410680c1400d069450015180100e10b95038809400754 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 873462544 1250 873461294 873461299
    0xf03031b0c04090302030c07120c0e060103200d0f060501171008030a0906020118030906050f070c1d0901050f070518040608160f030b0411061b151f14 66
    0x4906075074582d1503004550610307001e0760040d5100c1c001d110340241070136803c0d4080106401600d00140c00102c501004034100e6074584e90303000c080d681d034a006038094040c01c1010000c0414810030103103e540384001400c44080c22207170402088115180b84004c4803403c2c01018045001d5468850219160160055002d0100100f011076269a27040742ca25581040c1c1600300810b00ba4902130015903424415560015002c1203401c1e040c600c582c03405000c008480c064032040000004014180a9030101103c0c481c3e540491160360b81d65403041310030f02003a00012040c038628800c601291701ca00050040a001c0d605604603908036440385038007030381c0e00da014040300c1850440a03074140103203644074400c48008041a40c0500550072090100803041c0307100e50491150070070b410300d041c0b02041038650304c258415480720b684200042d02d000051742c0c501801403100580e00c6141c0701c007414000046010080d00b000010181390395115030540754002c2e50528805012041040c004001005851420b9490400c02 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 873463794 1250 873462544 873462553
    0x4090b0d0b0f0c0c070801090201171b0915030c0d0e2a010306091406090703061802090109030503131805280e030a0314010e060a0603050a020d14040309050f03031b 72
    0x180041c55043c44121b0b0301c8143c29941d82e4640d40207551700200442410410b00c3c000d4031003443d0640c2c81e502852802d4107001c00c01b15010a0302c442c0790702d03002c002c0c05000000d94000740d141d140c000720004240e406011624000d0b824094440880030300002e0607100d200e0b04070b428011402d09000c0301240740780c450690504043c0c94140004600c80b81d0320031a038400010b80c40140300b40c501041805503a41c0003800c000e040610b0400b04004010200c0031614802c1c005942c013503551040d840c012102030b00913800181036804009a9929003040704c030b8995003255a5000c06204c0d000d21100e40004846003101c60040240b49a03c000010400840e40020f1180222a0010303e05c03078008502c601e140c01400c5030001083d6648861a2881900001103004203090744130070105140150100c0c008000ca440b90030309064403000400c00354007140d01a90914501d050081002298056002c240b80c441501d050300840e07100700c00441c0c06e08105651054001c0c01500131450007500070b0740556106030004596445019 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 873465044 1250 873463794 873463807
    0x803060d0807050a020909211309111809100909140105092401050a060c050f030703030b010e04090308011202010c02100203040614040503122d04090b0d0b0f0c 70
    0x6806808401d02600003446504e80c5481840403000c00070f803c0e00d4540e8051200720b0b40e900690004550241c10100e200c0e500c540b1420f504042800c2142c002c40c100b0b40c2850340c101d10351080d010140c40c03041c0d40f4843c0d01404500c107200344044100203940070003007502c4d07000c4180407842168105040c9284035018084240b000411311600715081619030100c1c1d41c104050015451941180e21007512026110001440d45028001880750030b0600c81d98052014140080e010300009022003005640c54505699855242e032800800030160141c0c80750108111580c2100c1c2802d040c0b00e11000c05905880d5640d241c0d007440e400d02043c0f445440c0882c1005481d8070710400503141d110385074103044250303002591942d00f8244080c00d000786229451002c0714042c841008182d0307000848000c52b051500d1b0150756000c5215100382c0d9842d80c900508080505c00c6c40d440c41c403401d00c800400c2210007486041002d09051000c201d003043c0001c002400d0307509040049503c0c10704140540d83c00c100010300c4180b030500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 873466294 1250 873465044 873465053
    0x30a05031e1906170712080c0f0304150813081b1b040b03060403050711010e19060e03030705030d0b010e09010306050915060612190213080d110a0803060d 68
    0x480072900d034900201040300d034103403092450080e14080d060300c00641194620126410b99240c4040c81140b1181d841c6c0c200b500140721164003151000310b850810b8072101c2c40c15420140d41c030381c00380c403490010103280c4c424100310512030b02d00140507450304405504400003a85651540e5040402c050391071130342404802c0010901000305254420701102c0000000559004100c120b9260703a42c624045c0e0020820400080c0d031000444000d00d0340960a1142d031000314004a03100c41000d06d40a4100b14a07500d166104104a00d1030401c60b90300e80da0303900f4081e612000b45512402030910042156209200501080082c0d03000040007000601d0b0814402c192500002c02c0c01c0c00a07031054550710b64032018010001010700507041d0307070242141ca440c51810700d240850940d06c60400c27107030582202007000c55030341394508035540403054807594155240c0c020b00d4464400a00184101d110500c0f5401d1a43c1401c1d0184002458081000c00602442280c40d01c803510f2036440184450780c441301d481d10707100004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 873467544 1250 873466294 873466351
    0x50c100207090614100804080f0c0106030606030b10090e07060531090f090f0209060103060503010c0306140315010e1f030c0504150807061101090816050d030509030a0503 75
    0x3d0540c0b45884d40062800820300041021800c00801086203540801c00072902400807a03800c1c0d1a02400d0a9a982c503880015004003c184c000610503801d00e40f0000c1400034000d980c078024100f4903074100425030344000307070700840e03045480c00356150300010001c0205600401c0906914403120040b211800300c00c0e5602c004007880351a1841e0b4440c0340c00b0050020380078178400d40000c04e25181e000c01514680d03032103a0160070408107000744145160000280c16902c00d4211500401001c2d000380640030941002801030060343c011a15a10041c1003c140309142c0003e103d02d6921500c48480d6441c1d08051004942520007005884c014402c601014070001700011401e0045000d01401c0040394103200400084c0e645100d000b0800c003070b41c25001d12120101040c1c420403510181883d410b00c7d00c0408100340504503841c00900001000f040012402100300c58a4a050744a08240c0d00e0605541d84160f040b40d1065036189c40e2a070040c01402c4065000d03100035a0072503468051200717010380c0c4582800c1d11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 873468794 1250 873467544 873467549
    0x501020c060c070e1314120d0f0e0105010303030b2b030804020a0b0a09030c06031a04050703180b010911032e170c040b0a050306060603150a08010e19050c1002070906 73
    0x8000901c8050b401d2000c0090f660f102c240c20240608180031001c9a41a942e008240c10040340580c0c0f036010450350201c503404002c031012100cac001d01c030660350703828068018402400214000c140d02601010b40e80000d06a01040c1c180c200015580000b407074908a07000c1034000c000700cde00701c61210000301d80d131469400581741882513659800314480c01e40c0780c0444c1507001eaa04c280c1c2410f05183c0310168104d49400f803926601030981e8001440da4907854100c004e03094440707100f41804807024003c018042d1500403d1b050f104864000d00c0302a50725032600c82d8a1004868414404006480c1c1190302c02c600b615406100c20311103101e99030f5544501050010701084804030489078000d505200c2e10741814084c400d40440221010001d03107203403002080c0c5614004040134820800080094001403440780b4541d110000548440056a1150b640070300030144000307007502d030740725030080380b102c5446ca64901050319502030040c2c401c0c110040c0070700046407031104000b0158007940401141503056403050500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 873470044 1250 873468794 873468811
    0xf011b0b090327040f0c08060d0602040b0403080d060b040609090504030905040e0a051e0a060e100c080a061a180409050f16080708250801110901180501020c060c070e 73
    0x5240d103d150030042281c441c5082481c20300d00f003844007095076400c02c20f00d6910680c103685002607041c01c1c0c9043d000901c520341003040341203c0418040107100e5410040c103442c500c8098108501c0380c4940900d00b15010f41c0c424000042c03041c080600400e80c258201c15042482420305814440c0c540c00040c06070b801d144080f00880d405429484140501007103501c0d44812003000300c40c001c540c1e55084a46450000c10050001511a03521a188000030400c200708211100020024081c1c0c1e8071009242031419501140c00e5401c02c180450108011a02d12045900c0103880030705c0c2002c2200290124012504400d604c80d60300c50021340818000e101038005000d1082c040d04104440c11426031802100e07070001c46840e409680180000f49000442d5202140c10701e03490486505807603110802250180c0107180c1a500380740ea69a0300005038000340c082d81c042600c030400d81540c143d801014110851083c0c0b801030b80082178580d554148680141556031006068540c460388641c010460f425040d2400f10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 873471294 1250 873470044 873470107
    0x1101020414150c032b05152b030915081509040203030d06151b02090a09050a0c23010f0c06051b070b040201180e040b180d0e0f011b0b0903 61
    0xc201444c0e0600001e0103500c800d000c20a0f41441101721447e00c1001c2840c0303000f0804800440c3c0040c02c1c028214040000303001203000c1c03151641c0b80003030a0b42203a1042640c990400750325a41d0b894000d240320f9114498000c04050f001c1040d400704400b088001d4800c4c1d806000801541c00c0030040f9020303283c0030f001100c0d010a2100e690903c01003400c1991407000700e229a040e10034100607a80c0049068002110780008074048403a42041800d0500450780100280000b0b0320000352641d03008540301012a0003401c21000c0f80d003c0c401501c0700011803510b400010392224013600016440c3d030010740c01c9030045014003440341c6c0340d60141070310b68070511003511094800030800c0119a80002c03188800350b207140620b1085480d2211221480c60b014100600364003018000802841c3c068a60f0445503545d0070480f942088090300240103540f4091445000b40084c184113195940140b034440d40340220300820f1a1009500d0301c1e01c4504400107409805140030410000328001d00000303c0185000d04403c07601d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 873472544 1250 873471294 873471337
    0x60f1c06030b06011704060b15031003020411040522110f25020306070c0302011415090c2d070206030c0a030e010902011706010e0406151101020414150c03 68
    0x1002e984401400f06040100d200d4004000b9031559030901c1d00180d00180204020303a5580000e00d00314540c2469480e4a031001c0b080100d80002c0c40749120031640203880400020032480c4e00c100203403060340140c1d900400c442c1c0c42e9161151480c1841c444209440b0b40c000f401c0301101b01c03031003120344c0000e200ea0580b0744045200605032510011038000c81c5100801500e91701c00c141e002c01d4446034020128070074400341c600410b051500030b4008038014808076100c0c0441f843c000b04402e0711844440040741c0109071000000703001842c0ca5007292294006003444a600045046030245d0084249810302a81041031007102c005884030b00180d0b0213240b03020700b4991100407144005080f150200300c40d8000f1f03810281c0d40070160f6045501c400c081d0780041c80401040d5070350700040e5400c400004465030481c0c6403000000e07200f0080312a05022410076580d0a0f48107002c5640310382030380140c0c004e50f561980c0506860006e03141440d00c8200c8a03001c0c142d82c60400609006140c15900301000e503000c6403a804408 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 873473794 1250 873472544 873472553
    0x201050d0e120d050a0c0c12021203040c030b0f0709230904080a2d120212010e01051801050901050105031332030a17060307090906090203010605030a0f02060f1c0603 73
    0x10280d0091144508000d50f0b09007080087c107400202001508010015201481543c420b110102c500502054241d03500d040a14007040100883d200c140da40c01151000318210074448501719002d401240d82e000342103420f121206084200640b40c81d40c0440d602d1517020130340d0300c0c1c0e88180c6100c3c03401350038000d44800ca0b16101070500c58070000c9040040716a08002500201c036040d114070f07044141d18103800326280040a60009118014482c00b00f62284000060709d09001108213068031800c1e00d10b4800f040801044071400e1100707004d65a070211101d001404154814006103074801d807883c012814040d656242e01e0810240317a400d4020030b2801e841400780015a40040c144e14072504001580380c803601032030081600c6101c202080300c0300c40000116000b42c0d030804c10500500b141080421680080b0314000c0c0050118043c220700035400c140300024240b0300400d860441c142c106001c2c0440320000e60030060260300107007100e421450309000e000c3c100c0f402c800000580031401e0748001005415400d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 873475044 1250 873473794 873473801
    0x101404030f09060504141c0b01030c171c0e060705071d0702060a090606050315191e0c0512010605031b030c09130219051306090509040201050d0e120d 66
    0x1078040c840d003580100a51588802204c044480e201204101c0c140c1100003d1285401c4014040054040000b007034203201a03915007e04891041c00c5414015a460016412503199102c4140702e903007008111392804040c00900e90119000c51030b004191b83c0703246001504617040048251501e40c44001c3c2840381c844010602e180c2200d01c00c128281510304a50700035580c4900a086000040c1c440c4c41503000c00082d9001400070704401001e581c036403511864850201ca004807068048000c4560001c2c0100c2e11398401c1c03098052100200c040c141010b19000c0f0060030307003110884208801004088000449107400c0ca02803e03145d40c03083c2d924240382025004c000c001505000d40a0300c00c0082c01840640c402c210b0352849805c1d81c00403e200340b0888100002e000d0076031900261424486002d2043d0303400002010507070800340503801032a440301811911050741c0d00816400c1205030010801540c007480c09003400490300c0001003860320506554604000d14041c40c07004c80080400c2c4541ca1f000b0b00d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 873476294 1250 873475044 873475067
    0x50a1e0f3f060b03040804120201170115030f0207050601120f1b060f021605011808150105100206090c150d090302010f20070f0302150915070302092110140403 70
    0x102d0f10b8114105911424003074407a5108450304829881e800c6002c590046020b06460007807195890641c2da5100d010410301142c03c0c0401c0c000034035050301112100014801d03903540eaa00700c0010b100301d07801e2007451540c039000488292030b011240d002c600d0000361611a07240d0100717100c0701b1030303015a45171500103407001061703003070100664121103040306140038602540c90803135500f441c020000441d5984020081821900102e403180034280982d1500208180c1d032034101c64017075812001900055030101d13100d00c01580ca1088580042c1d58907038035880c10410342002070103600001c514000d9603004101c101d0702e8000302100580d448000c40c4a030040144910100f40c44403e04800001100980401e480c0c8501c2c0c000401481c03a80d410303801494401c214030180b01050001021031403c0a40350203030350301da005031a00080c08200000903941407090094070000c080c013030a03103651040f21a0018031960b003400f035100001e20030305051000c140340d00d0140c10300300c02e41114900c000d820181002400c060244 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 873477544 1250 873476294 873476309
    0x1801090b0c0a2301021602030c01080c041214030703090e09030a0c0807060204030b154b030a0807060e061b0a170106050a1e0f3f06 58
    0x14800404076040115012428507804a03c0070318401d10301400010414605512581c1c541c4085000c460160780c054206010034002c9040b40e5a0310031341801120031020403200e61410800900040100c40f43d10380c046c04646211f074040d0207602c10000380d0549141c1003528190006681d0140c10001d021000603559004402c840245203400c0c4601c0303002d445654541401802c188000070441d05000159069501440c0d228200a0301810035008000844181ca69410b01c9030103e1501001c400202d50305541d0f4001d04408040c06020700800740640e09240c20042c103c9000c8905e400101d25a420700c6102c0b1298410502107071542214280343d4101e4054070381e62801548080284460080041040003600403140d440c02d42d1340c561030308103d54501e40509410b844201401c000f040042d00a0302400e43e0041c1c503690382c201030910038031003074aa640f858030301c4002c9402000c5100c200340c80340042c84894204000d4407110800d852114494204500c01030f00300c1c501800010120f946a94003601c0004c1460 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 873478794 1250 873477544 873477547
    0x20f031b090a050904020f03030318010c1713060e010c02010204060e06130506030c0706090f02130603080f0f1c060509010618090f09050d0f09080321100b1801090b 72
    0x444003090004416001d00f030322032003104000030115514508906514000a025262282407500040c5544e415400340e4072002c0d401c3c60075010b61184189412010440614040b0446485180c152003100801810a860341c0b62141d040c0c00350358109005603184264240d00043e661391620100603c000c080c00303000d42c4507600c00c200b0700c08071242c81c0c60300b1025550103e03255603407529000b0200e40d662041c40001001c5505100710030301408070748030400748002d00945050700c200c0d4212140004a490b2400f0040c0300c8001030184100c1044690060003420900010813480c20102c2c49140c2d02a031212281915010b031251410f00003421300507081d90041c00617040070004001800c60498215446010350310310035613180240083e94032180c2041820076000b2040c0e64851011070002059512807201c0d00000c80c1c0440000500450004110340691701b0403901003035000c0c10700c0da49800300c1c88060803a8009564208012038000c0301c1a0061107404151000007400504070b03800544145840e9028401a410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 873480044 1250 873478794 873478807
    0x207050117010b191b08030703060b16030e030304090608030405010f081513060b0d0e12070b0c03060411040b0c060a090f1101050f070b090c0f01050a030b0d06020f031b 74
    0x281003d640d80071860078000030004d0a2408100c682810007080e945000c41c085190f41d040c481d8480045004020698041c402d10b615001d2801840c4034000031080c01180840404020901c6001c3e043e4808070010180e07881c0654801005080e030b40960440800c940002400300190768010f41301d141009042e04060300c09192060304101d503009074150642c05400314102c5149410303c207034001000740c83c068480e252261004c180d088003c261130300f0f081400e1320503203031101d90880050003900d045a03403240c400700c4250341f29080c1204640001d013410f40c001e41c60704030020118800c240900003902c8141c5105032140303e0f4008040ca48040a8100c2c190103141411a201040c901007000040e9a0080e07512860700800c02c004813114401c4411704103003103402052840810065002090241400108480b505103400041000c0b005910741e0141c0451810001d607040c071030181d0130000c2800c1c0010199002c102280c2c4858099a00903203180282c01d00020410125141c40c061940d00604e02101550802d903 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 873481294 1250 873480044 873480059
    0x4030903030e0d080c03090414010b1605010906231f060c051f0902010201140601080f0a0207020402070309050117060a0611010b060c0f061305100c170403020705011701 74
    0x111503000240810408100c0c4480c103807a91440e8240166001c10800c0c0d45080800b001c0ba00c9030008888035100c1d50815500c0003900840f0341809050350000b680c414500030070108002810b280f80001140d4a549843c51800841c071944940c0d080000000000703201e200d00f40c45009601071380102012000d00c5041e00303041182e12402640b0042d0b0302c09040003065607130b050a106140c00c68079180c0010304080c00d0712001008215030421311205200382c0003844401c0d001c020781030103620215905400180040e00040c0030030103140585402902d10340c0014a0b1544640104040c0e03071014400307801080005004200650b4445211048000700d40c0300200c42c0e080c031000240c40310345148200c000300207a0104c148089027082d0702c10302c8136050040c407103075032511200c440d2510b40b07411341800007040c05000300051a01c081c203c000c040896014018100555641103050001e01c071402c10b1108100c2032840007400b031080c4c0d4140c180100e010390020150f0b035242000060403410744007201450310040361b00402c03400 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 873482544 1250 873481294 873481307
    0x120a0e0a0e04051f020c03250210121a0906060901090f03080912030307080f060a08070305100b012d030908120603010b10120c020c130209090a0605010c0f0c150909140403 75
    0x407222042403017005074035048c18001844208060360210700d501340c04104603000445016450309129051020144107007440200001603000590801d20002c0010441d10f090030041c0f004600506000e9002c0f61103c46550800a160700100c0d0150f000003030455052508000b60801c42e114440158a103240c051002000c60102a00c0701c15440e0f0000b003c40c0d05a81c0e4554000c3c0035041410490b007109583e420b00d6540c0342402007041e401c191500100000d07551094007410b0354002e80001d00dc604e0a0110a8030030001007000528003010b075603114030400180034100403c41901300000d211814105030701054219034240702103a100318510003da03490b80303800c04280201020784042c001419000c0748026030801d1060101e2682c0281090b0b89010302d51007643c040d01d1044400d0b40e01214540e100284e44d0304071103d501909004c0b03103e10749207000003502040c400b00300620072108003181c5503036509800c17039691800c0c03103141c04141540410701588480b44100403122114012000003402d05460113400e1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 873483794 1250 873482544 873482557
    0x5062a0d1407050d0c02040e030c01050f22030c08310501050301140d0206070f0302061e0717310b060406030b01060f020f0a031d0102120a0e0a0e04051f020c03 70
    0x2481005e994403401d655072540b0213411415901c080c0c030340c1c17980c0003521a4000d01c8211002142803000d000031070590345103500c0d041c501002c0520180711401c0561800c0d5000e4490b02e0341220300e408100040783d12124844017440240c108403042502c5010010b1140034002c2030b5811181c100441031004000c00748000309210704c42041030b0b4000318595603c2c00071130494400c445c4050030142201c500801015030009110f0b202d03014020201080c0d070401c0880c494041000c1d141b4078002001e00c403c000900286207401600040400400e200d00b4600711951280e101c000070010b10039006070a8028180410040842d81c800000c40f800c04c440341c259038808507040418001c0108208020902c000018001c109140c44410490100d42d511119442c2c0100031200c005d50181020048244261441d400090345d05114501021101c0c1098000d03041116071f0000c0141c103a610a007000d04c00980311307003800e13401d0b801103000e1000303800c984120311180c00441e40c050140c40404c0d8410060b94003541804002e4481 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 873485044 1250 873483794 873483797
    0x171b0c0a1e0305011508070b0906120601170c0309010b0d0f0b060105280f050a08040b13020604030c05041d071a0c150a051f05062a0d1407050d 63
    0x3800c511104161042660301d0b000100076610305900340081d928119040e00456141c00100e540c003d4580c00015107a010304100e594101c40c06021001c101c032100c44040d64040b03818940001c200040d0fa4454901003c10395110940a0000003072000c0e44400380100088200d080c2e480a83c165590303034076034002480380400600319940010201da003030383c402c404440307541100c820b0150340e40e00c149031060b100d034808011780b0780800c2038004c442c65560f000d8019282200700700d440305001036846072120700080300300601d02c03c4a100c411403154010ba03070310307800341c0007642c06540c103a412a030905040c04122400d074550141034138480740a02c5000c101c006419010346501c69003080c141080d440550b0028041e190108001e800303410340d4074070302040000a0b5807080b8000e0301e0522064480c808030617684195902841c51000d1a84070502c0f1a0030804024100e4441961704036580b1140c40406214101c1d004440c01600e42104070803a0301558004491104002e20b034070342c18a8258a035580540d00c2c030103000c8550 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 873486294 1250 873485044 873485069
    0x90314031e0c0d06121e0204060b0f03060a0f03050d1d040219530f100806010608062403010b120f07050a0c0c03171b0c0a 54
    0xc00701e01080000310012200714110100c541003442401e6159044104445810303482c25200058126a051425100070f4024500760024002044010128100f6031026a0400d44030900000e0482c1c2c118010220004128501074032410110204045022180e20000302c02c0140f1005102083c4045004680c030100c80c24256103800c100001c440d40c043e80a06141e03402440880d03c0200041c0817003091420354480d954170b035117032440b038000702408141000181c010f0740d07406020100508599450a40c00b8540e5001c050180712028a202c2d038169000c5a0910300d8076580c81c00e205c2c2d00b0b030105c100880039250b51409894550b061040040c16140d008010a104150083c0a003541031142c21040680c46880b0126559a607141c0201c3c0310103a00c1041d0000382001c1c448001603088032151a1540109003130b0750b0329440c01c046c00804981c5010000401e482c81200b41c140000080e0b01172014000101d0012581c07526600c102e03500e80c0050300d2000150b201900903000540f030326543ea00a88060b035040c0207006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 873487544 1250 873486294 873486301
    0x503120a0810180911010f020d1103090418021305040206090f0f0d05011b1806260906040308090c0901031721011410050426010504060c1209031403 65
    0x224104500c079400003094079460f41c850419803005030041e4048900602941c13a00303100d4003004581c1d141816000e18016000f05000c8126503100e2890780715061340200407241880710000024048825002181c2030b415012018002142042182c2c02c0107a81c044104200c10b280039008141907200c0c0c2035000b48242c43d0380182c04c1c0e147d6101c04402541247c00741c120039801c87c1614045000300f0081440204008103480c1001301c0b03d104292405415042c1e440d030906080c6030540544d0401c5007070f03000303070950349411075403654140c00d60844901c1420b100d001440705003000e01300604036039805450b0b41d40395001b100c00c40a05440701900141180d5000219000004d1a07460703071005401902104c40d4651081030038418030060a20040d81030321002d05840401c845a0020081c0000c05038505201003207041c401008a8aa503800001881054040b80346a02d40032011580c00c450303040310f044480b00d0307494a02851055012280100d1621400340410042015403070140201d000c15400044828001000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 873488794 1250 873487544 873487561
    0x506030706140f211503160308131508070e0f0f01110c10090305100905150c0d0203070f0e030102030601090b0309070e04030f020f120702010c030e030601060302040801060503120a08 80
    0x844e000c09081d45000080c1801401000203070003c2590076118903030000705620240c0c0780c04544525220607030004e010003140f80d0342d5030910f00e81003400b0700203c00582c40d03800555001044907004190b0103680d50801245440c81001d005000c52149450281182052000194640030340c071507620031090030008990100c1c42c0045183c05d68140c07110303407c90741c81044c20003056084501c040503030b0300c00c03415a47c1031a4403140400441d19410701c050208e40c08500040342c90014150100e0300000780980f098588046032813a04140c0c1c2c4162001400104607000d14249181e00024000c0c29030003c400951641c100200000c1101d09180a100e200e118004007040504208122882c02490090154181486c0508024007036013905003442002d80907013234003c0b07420700011400024005180d81c0072400c0440300c2c2c004442240c500f0000300d0030300180d541c62004954041088900801c140c1c0c5c0c01603034941c01d0044060070745010398031090103640b042c03280f01c038004040fa060380c400da0198031704040186c0d00d15a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 873490044 1250 873488794 873488797
    0x31c02090a0e0a200408060105040513170903030315091e07050a0c0203010c0207080f0f0601030f24050703060518010e04170705010203101d0712200d0506030706140f 73
    0x40d0076502e080d02c02002c035044d180400030b0011100c0390320588907680e80c1c49c41071000791031088410071400030750740c056030000580c640d000c12010020380e2802400c00c000e60001c03d00d03580c000d40d000e044080452051042d81e28240b00c0096010070b00d0507680410214540341c1400c0200041d108800384840407800360b000364442c00c5e0489150b0340050091010b0608080069150070050145001500890303105001c0310340c001aa401fa4000aa4003c210903032a58440440740800c6640031600c51059035a4941110320341d84503c8031600e102c180001d0503041041c009000c03100c01d80c1c0320a02130301404051102d00c038200d12000307044072101c1c0074825180d44d4503d4001049010030990210700035010858106120055001c3c0d0700c0781c0a80194004866201d034407030001d0303a41c06d03a0481e641c203854000045003d407044014110b2018411000304d5642c0040d600101401c064000104030310700302141213000a0554002c5903000102500588207031420003600030201151040c00c0024010700098102d42c0300314160 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 873491294 1250 873490044 873490061
    0x3050f1606180c210f0c0504380f1003051609080c0609010c02060703020105150a1202010f09051819020a020a03030b030c21100c0c02040b18010305031c02090a0e0a 72
    0x145400741592141b0340300740c2540441c001c29000b28504003202ea00401013010781251070030116040d141c070409001c00c480c401d603894404130f9003216101c2d049689548900e2012200c3d9505030714003041740c1c50076182905160421400031010045042d004000280c404101d4405907082a00c0881e03035408060010b9a0145030708900a400c02e10000d030120905906600c1a4014440c0c901d110034079890350380c1007101e00099401520715000e03a98403000d00640c01403083c011755031454101242d0496031140040d00b250f14142065600000a00c10071101015800b1904450308206104604210401400030b5560341d0601e402001e143d90758580c0702413075604106046002c1401040d00350441c03c101211040310f445003520500521a150a4120110303190081414140055440c3d800884e29a020031002c3c0c40e080c0c1d209078029007405507810241c10207128050203580294000c668804580c1c0c01d024101003036008000c03095106000d400084d82c1d4401d00281210002c0786104c44640b80c030b888002c01002c020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 873492544 1250 873491294 873491303
    0x30d050315014e0207411005060405130f06090602030c0415020601060509150c15090d0305040b060105030c0d06081c0201062103050f1606180c21 64
    0x29504075209021440024844a010b00030219201080204040c00d9000f0380d240100082c2c203603403101e0a00c81c602e240c800007900c441c0900000386c624500c0d658008040b40c2540c03070600d8001ca0350810108080e4052a50403076400c5d10300b0000c030728150441003403000e070f040002130401c1c01c4d1415040901003280c100201d0300360801011940c9003018411021a0f50141c4289600c010740301030240501800411424100d810700d0b242c0310300d04200042000b000c1614241c4107100e0710000e000801544100300110259168600304250041c14800b6a161619a90401410400d07045c0000c000004040c00065a000102824040d449440310484c0000300e000d050780010762182703000c10008007080d00043c05c81e8a1001c038040c01000180c8030030124280d500d6401442e5400ca04648407400d00101c018507000994041d03d003907820911094141c503c641c0c00300249000d5417511043d000140050782c8506001104904100141130390036a035040030030708607445028482003100003101242c0c0c2030703d1102600e450f0300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 873493794 1250 873492544 873492617
    0x2090d06050f0f090a03091e0308030903091206070c11040e060906060406090e120706090812010503100e340b03040605011215091a0c09030d05031501 66
    0x1000c6010a0030b104452030105071241c1c40115101d81c80c086034503016160580d480c1c4813031b681801c010f48518000c080e5072203003a0501c0140000451210809540a042201c0c051551180070904100a4074008494410b203230304080c1c2030100b00c6800003000e5132038550003107510003d10100000078006141d01528100396014110400c1030514020492622911040303408024068845c0d500c14202c1e42d0b0420020346139070000000c4c040070400399029105591091002080094069072100c0458015103210341daa80c41080051120f45000e1003400d041d000c424508100c41d0800c00c12203a41c60030200d003000314030402c00c0f503001c0081e106c038102a41809500241c0719103580c5c0e90b091550313850784100e40540308540707080000300709004500d0a09000310f4000362172001055400f0a038038003c0101020454034155000005103800d0b100c0307524184507191592040d5203c3e01d00e4010b041c00e040c00e00b5482c0d800c0040070420811000030ba1400180c1190083c40d0000741e01c14202c00c11481d03180c08845c1802200742 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 873495044 1250 873493794 873493801
    0x1003050709030b16030c03180b0405030f0a1101061a070809040b0a1404060f0e01050625030f081b0301090c0207031a04030906020d080a0b010513080304050411031902090d0605 77
    0x401c00301691503062255401c00426603103410032400c84041358003d804160b00001c0d11800b09c2c45101c1200d0b0030500074001d0740e285c000d1031f080540240d03001d001000e0119608c1c8881040d40e40d4288200030041030450345a80706240e2a028100803403080020040ca802c4010030a804180c541e9070000d1303450070014002d161801d881d0030b0070081c000c0c01d0142182c0f1684c1040303400315010b01201c0d0783e03004440001c1141589a42040100b0010360010540c0c115240c207001030f40340316410300510240e803090017926261511443e00344000c1c2251002440131414417290420f1102492294048030704503440468001581611000200c4c10720030654030103000c1850003a00c1184544a0711001c44c000c0f07100c0e44859690703640d00c1c401640c4442c49500410003184101000950082d81500840040101450001c0c035042142421143c10452900200071591002ca01403001e400c01e07110f5640b0000a107980395095261100e00f450004115006042c00d039a00864030f51610340781c1103034080007a54001814002443c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 873496294 1250 873495044 873495061
    0x2070f1202012004030c060305132406140907270e0609070c05100c271401021f0f0b0d0b09150c0702010f05090a060302040e06040b1003050709030b 65
    0x54801104400144103c03020015995038421541120b9211461901141c0342c02c03c240d004040013488400f03460000c01159000407041e602d00310307581c00c101c00b121685044041c1010100c5e1444c0e002704085800c00e2a00c0406a61406416580444c451600745020211140c2d5044800c900c17800c3c90403818080352022a40400180d407007441250280c41c8942140d4902c54115000140000003a001c1c1c1c0088155420b052003e0f0004014000d0900f0b1549400c00c0ba4203810028443d422402c00301c81c82008828400445c078481d00d1f4032a11400d20040110359404a15140c1c00f240c040c01d030b0104141d642c443c00040c01031b6500403052040c0001c00b408501c903491b0801212004c0111000841d6000d00c1d500e0401c0f4030396007604240651500940e00382409401c0d40195801103100d070300d140074042c0030701c0343c1000c5944103c2c00001030f0100b50360250b142c5162070f42c1c0c0300d280440548030303070b10031424110702c41400c0c2c860030140d0b51040341e24500802c003900c0361641520481e0540c0c001804072801c81c0708014804 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 873497544 1250 873496294 873496301
    0xa0e1b031c050702030f0705010903080706020f07032f032b06080a03020609060c03010b030a06171b060406051c1b2c0a05060705100f090213060e010902070f120201 72
    0x190094003a40e00c0b0800100e0555128807c5004035800308401240c00d0021845401c00f401d252441080010315004005984820f6a003040c402240018030b6020401d855200030784e010540884810441820b00600a11042d1607010302c59040d420410b142d5980382c521502d50001040c1d00d6a4104200b01007511006c46946076445190706038094407621010030007940c2c0010320b40f0301c07036030144010b80d05507424550282d02ca640046c28101d02541c803a500416040f60f4642e10040368001031004002c0e40102100c080588220f1070045840740310140801c005158014003212042d221554160344c490415803045001052190144c03030fa0341c4400c503c030030002c0b034000e80780100c8a082c1e43c5034004440101008842e0210060344010341103022440c0c00c011504082015003103151240c01070300c4201d0328402c02c4000320f4800855202c007682d103403001d80302981001452040481002d410503c03030107040c0078050400030418441c0d042025030000c0c102040c00704070230491458035440143d4060310200554000d019 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 873498794 1250 873497544 873497557
    0x15040f080d021c080705090d0c06030e15060906040b150a090927060213090504050c010807020a0507050904141005010503100903090e04030320030f0a0e1b031c05 71
    0xd0f02c80e407941591428001d034501c1c9007001541c1d07941000c40d0f540030422207030f0390004051903400080b4450712a00054661607003402402060790f000502d01102d0441070714020946080030b03100c3c1e102c8018070100d51100c9003440c0e84150203450105a15030040d000c84e03076403691603100c043c400c407001c00e000700000d610005c8035088a54020060000036620500f403580d42000701842003c0990360103103a40061440d401134101c100d030300100c03141071603568072003003050b2141201e003204c064000c000100307155a04412050380045861000707040c0e05000d507403070b40d580ba20701b0300440344100300b47d0380040c04003e42c0341d91100e403528120003615080500c601205018040a000f0207210b4040e0815054560309140b040c1c11183d5011342c3e0f0f11004510381124511a100b003d4410b90405886812020702804041b035a1018084603240c59592480c251040c030f60265405032240c4591803d00c1c5d03120031400d40024540d102020148121021203140c14002450690041e01d1255104180c1a20400745600480503204 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 873500044 1250 873498794 873498797
    0xf1a010602060f1b07061a0d0f021e1c0804270b0906011211040b0f0d05060d080405010e1809071a030c1e04030506040b06190e0615040f080d 62
    0x10944070802c0799074400b07540c140c0400d84d0500074807490001c501e603a003041d44e00482d1480107200e507140403030100308285d01d150426524100105600d400b1820410f110540010421880700c515610000001c1d100f40c00e12910248084200d0052009009040701160005d10410710220f00200c402029024481e0300d40d4204010240340000003000743c200841c04521850059540701e00300031004161400070442d0b041c100d1110b00341030101080c01c01101000340800500c4903071494039440b92020309003d8880051406014456410483d000104408103440c141c84007400c00d40c2c1035084800105429000556a00340c4000300241071280700398000c00d114044d01d01c0c540510850803840d6078140c020307100580ba040803408003007107101c0051608100e07032114440d00c01000792905642c4c0e1035207032519800392000da61314031f610424055507261800713002c0c80d002585004504c840d85456841c3d5485c58008200c00e0240199020b40000303070080d0003c1b0307806406090b40e4410300341d883d0540355680d1098040ca010 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 873501294 1250 873500044 873500071
    0x3140102130e0412080903160c0314030301080f0a080a0c020613030b10091104050415090524010c03120209011704060230010b090a030602181e01050301030f1a01060206 74
    0x7500640b040d280107121b20129070056103490440c1842c00483c4040300004d50702d9404138030f4003000041124410f065400381e284021600d0754101060a0705040c0c052082d045035a00004c003110010781000191540364440d410102c080080f24004600c0510031800c108001d24051003010040100480415020740313144188400344a4803940b400c01114001126680134440c180070821052031f00390464000c07901e003c01c40007500e941d603012100c10381d541612041c0038240280103c0c0001d0303e00b4aa003a8441209103001e408403031042d14003822151884840094545e0002112100c40c4d0042024904040d80c15003183d07100c1c641400c0c4803000307400542a0050600c01258100e00c6425290b40064201c403501012040da42d28043c1400c1d4a90f100c005015080f142020000010410a102502010480d06030850450527100104440ea41c200020b00b40c800c02082c1a10110742d03444800d8a041d0b95101000300000b60139401d026600380d01800c51248603402c000c0021a8042e0b0209001b4003078421015090f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 873502544 1250 873501294 873501323
    0x100614040509060906010c02090702101a010f08071e020f01050a090b0114030c040603060b01090501020304060914040b03012408071211010c0506070215010b040501050403140102130e04 81
    0x400180304074881c0759446103010000c9040d601c1e104600c44c2c0c0041c014103014041e002c495003c2045504112411409070b0000c01c0455041d8400d0b00941a00d080040209402c007074081c00060510107140015404000c04c0d0000110000c1c080c141c581155020300c20340c1d184030644000005d40d81c01d01c40c01010055400c14010840c803040c00d01641c45110344c8503a5034206a070078150019810b041b0000c040e0f40c148100400241c0503207451144a000e140260710104941500000160403241507a00c4141150b0013040104011a03001078140159030390f030407030002010b07491800100503242084402354154a0004445081c0c0f000c0d031400300b4900f038440c0d0018080756a0b83c0c00591505850322a11840d080b0080041002580075854115046c1d8141088850780c445515518505207007141d0305805a030105908083c444800e6131880d00420f1119445480c3c00e0520000a2480c0201d00c0001d201c2120010209030084003901502e2040c5007103a4130088803580c4048101c0c4a40782070300d098441c0301c07818407007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 873503794 1250 873502544 873502577
    0x90a0c180e010e0c010f0e04061401030507021b040b0a0b0c210a08060621041416050f01050f0f030a09110402030714160c12110118030609080c01051006 67
    0xb9103c03c5800b15014203d150a440c0c015191451035024540400c4805d0665045c0781e07466101f0f20380500140b644c0d0b5812880c0742c00c005011a10050410401e6500ca60300c03e044442e0300c42d001815000c01940c011402d40c0040380421030590464100499441c03011400040005c400100d00303960b1640413100e00100c0d2002c580010551040e110a040001c0282c800180f49050000041810391045141d5502c581c903461050101528151021550140c040d281b03692103041c2007000c00c1d0141707086040340c003081f444c01d80003c0a200318410724134180800070070b005902c80c0c140e10550f250f25100c00007460780da2508409180c01015017000807112940c00002d0016075041602c03e480c4a40c01940322208004841c4055600c1c80e04011000071a4519208040b00059800c0840c48011b021f100741118800c502441d1000c04210b042c840c207410441c084a000c40310b204e940250104498000070b002445407450f09042107588500300c0000019800d10050102c03111560302210300b282d0141d55581c40c03040c0d05070034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 873505044 1250 873503794 873503801
    0x40b1e040c2a031e08010b09120307110a0504150e0c070c080f0d05041401110705040e0106050f0319290702160807261006030b1905071205090a0c180e01 67
    0x4540c0005500c5c500602080f0515002000d1032a0020004050109071030324030382c5150301801c400c68076120341c0e81c00c030007660401440706400f0b41f0040350103001712040c40c0781441314a6180d00c10362800382b11260214950703456041c12610301c1a00402803120094a80040c0b941c1c603025011195a6445405840e086151140f030a90b42614940840d80380580303204401102c8940703d2410000980c000c15a0010340359445210722541000d0000c0045007185c5080d08004e040d0b1241500240250481159103c41d0f42c44011350410320b9510054400005911640503051034454806400040348c00c8018842e030785800088040c3d82700f03500f00c03000b61080d8840307852984038480c51042c00406c15800e4201c1c03440400303075140034440d00b0b80002140d410041d64140c0e403040d0340b000d0384261201090b541c140444050b001e904c4002d014000c000074485424614001480985440c1643c0e02c082c0d03a400105048060a0200035040b51308218000e610715120079403050500c3c90345115190700d600c0c003003c10003016410702 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 873506294 1250 873505044 873505097
    0x100608010b1204033e06060406080a021915030b040c020106150c05010e06010603060617040b0403080612010606050c0c0d020a05121c0c02040b1e040c2a03 68
    0xa001d41c2d521640e80030384083c40d032101503250700c03191071500200312240d1084444c000c5d41204025176003076042d421514200300020307046a0040c5d042c0070b0103021042000800c00b030200c2d8161241603281030040c0c0c0034102503080d07030040d60007094400100d071440e56050700034100c8048111010012514244016400c880d080c2c070038480c501d002c000c100d03030109000b04035007402c06004100106103210346888031401d15009805c01c10100307944000c01c1c002140e0000071121404202814034220f4240380e102c09501e4140240002d0802c2174483c0014404d450f501c9290107030285141c001d110090325140c01803d1074108000c03525441c45070400070780840c6071803002c1c800a0780e00a410b103020386003000c003402810800e0705d610908500c99286000c0b80045644821503071105103030390f02c40088031188100700030f481d1210302e201d100d0125a004051039030182c04695548042c21140020080d07107502040d20654a03540e5403e44266194030034a030030307005450740065081d119a8405040450741078548807002000c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 873507544 1250 873506294 873506317
    0x608041a060906010f05070f140d180b03040f0506070e0f030304050f060a0e03301206190506070c030b01050a0303081302032113080c0d08070f0605100608010b 70
    0x205040713500440340000040301034506a40741150f1382d111a8001c25006004031441400311a90740074654040c00408248200703407405071101c2c14000d00c0c1d003e440400740a8003265950002c00320b401c024030a03e40e6000d00d0380c07000640b034091400c00c1010f040c114a0081d01070194016502c0300250745800300407542030ba90b00a104c00381da60484824401d86030010b440400078020018074000099908010549989050b012401035504900c28040060b034845102003605180c18000d21120b01c0d004003440e0ba2103802519000410302c3c0c840002c1800060642c0815000000002d10005203c00d03107a448090380d004004400569903102d0a11031017030340c030788400340001d60082c0103c0d141d052103104410803140001c08407042d41d00e524000d02c088040840c11001200300004080c5400700d40411160020a081000b5000b0320b52110003041c250255403000034440c030740004090003001040c00408148030340048080099203032011030004055010b00900300403c0103000006008000b42080792a20b0000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 873508794 1250 873507544 873507559
    0x203090f0d090902090d1e060b0402190c02041b030903140412170405100302090f030c0105041a0d020304081b01021606020a1e030203011d09030f0309030708040608041a06 75
    0x3004003083c004d4200012a507440352244a0b1940420301581840c103d1010b4441e1010300d42c444c03031a1520888aa590a40740928014403801c10841034203482d50030b40d6242c80c28418101c489510002c0c004000c1030000145480000b80001039007036240e4041c165542c801d1300c0b00031003854035022050303480c001d51044020700c12031018990000f0302c5000c9003904105060032401d042c9611000054502d00120500e200020740c00b00d0000c85074540801c40110203602540540102043c402c002802403269000b000b000c40400e026800001e0074003c02c840507403011b400e0031500e03400d0918041c98503620140090b88101d03030b072100b1410030309018400c41e409058050700326541c042491b51044065007000303401600b40710a0501c0340c05414110744034020049070300d542c0103a90358105000c0f010320b02d1841a030400c40c44040000c11004540020403078003003410300c034091a140c2e6134401400e40345202d60b4900410042c404100002e034150064803442c0290320603100d0000119207542200302903241141c0d42e5074003031107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 873510044 1250 873508794 873508799
    0xf010c080f0906041701050a0525110705030615010f14030a1d0a060f1a0607150b19030506060607021f0315120210050f07171c0203090f0d09 62
    0x103086000b4070301a0009004582001c0d55907031401607048110b03076000150b9450b4010041080d42c64131030240e0140003802640000510000311007090101c0c84130041c28000020210142d01e141080701c2d20081000800710754a9181c60342c2c0b00c4202e141030100f6140451217103460340032500d001da0511a80c08202840703090465441d00d4404029116112410038109250202c18800704000e20880000c82c1c02000003095950615182c0c2d800c846142c2902030141c800b044400e1619038880003114002500b1040c0286640d07511482d80b00200101038402e40d00021840c00034040311281d4510600b22030158054803150707a140b2007400710350700c501d0b2002940080b00109030165122542c40b0803d00350054a0000340b01c10a80c801c2440f030401035044240200c40302c405503000c61810884c0c0b901019402d00d400c90906400010300005030142e075400a010108050446410700b8003c1c041c0c1c0e81005418000b00f9003603210904500003540242c4644603107009888400300095400243c03540c41c14610741e1018900352 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 873511294 1250 873510044 873510067
    0x606080f0f19080712020606100302030105010c140106050a170607080c0714160b18030a21030e1002040510020c060d020c0c06071b09140a090503070f0b060f010c08 72
    0x4540c0104440c600f038113102d141d001c1a40d40c0b020545251503034008042900700b0408000c904007484030350300c040500400050017141d80c01100301c1040355100700381c0c0e9482d0140c00f005602500b682c2d000f10b60019151100050080010001c12064006100c1516010389402d402152101c80031681031250810030002e070800541069030000c41e03813400700142d58044800c000c60005140d842d40c070940d0144000b081000041418618080010104800a0200c003002e030f5211052221a625010075440c0305d40d8440032002d001345c0104040e50074a000382c500c00201d240c400c4009410030b008060191070000f00049000b0300005000d003811100604190602049240400c0039501c5410a01068028a84601c210341c54150260500301d10034030300c00c0c1081d0790380c1e00c1400100c00700741e2100150500704049860500c0302c0803841368205021000104131100300c1d0070004d107188aa500700406110b40924401d05010208180c2c600500c000c4070303950646c1c55100011122010011005440d0040412003903203800c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 873512544 1250 873511294 873511333
    0x114040303050910051b0607090807080d0e12061e0a090f02130b19031412070f030903021201060905060301020c0c0909070302102a150c12090606080f0f 67
    0x1540c85117009480c10708004140c240100858140492a6106d1400d101c015500442d481c00580742d040f0041a00d01c2c600302400c4d03951329100d208070003440038055072881d05480302c0e03005030700901021080b114541052504d41c405034541000803026800c05c400820000302d100d00442c10111b0708103100181c0c90703200b9001c004c2038040120420342c0c210b50303511480045031600e2040c5814030038400d80c0d440e0160320318146004a500344a00c1800c19400100a010400040c881500c1c003d98101d80d81029620b054070381994101c105820203540002500128107000205401800aa603c820401d00454440c401414280d010b0202046020b0700a0311900c140c90800e044d0b2194081d4411088690050741da401140304d00798103048280c00038105c0038520010520141c80c0c011000c1c50072007440b5842d01c0c1900c41d042c8244403214444619901c0d14207405807544152203040040b40031541c00c1001d250030707103082c100421140c41001c00500031b004116600007000720310705090411000180605802001440c80c54 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 873513794 1250 873512544 873512569
    0xb060604080709090c06080c030c070318090f0b03010213030215040b0a120b031203160c0804090905060a18080a030e030304060902011e0e010302070302030403060906020901140403030509 82
    0x448400e0000180750401000010010510f0401c0001d0303004003401c04040c4425140c003d541030040a0042c071410380c0070541142e900504040c40a0386a45091908458803101003003088803d507444d12000c17a0900d0345501019a88407050070800050489900307042c00e0380641100e8500d1800350305010400f41c01d0042e0b150107010342c2d02410900d010b132103854a424a41043e4209000120001e1244003000310358440d078000c4107011030050102c1031001280401c544002004140480060114088000c1c02412440c03511036015030586c1c0c640da10303681444001d09408070300f9940c1d88640d00205200540c54400c92182201500f01c01d4001540d0780c0799007840350302107100e00c0d0406642e04007102e0112014005035000d1131140724045803a0301c05000040c0a040c410740d400e01c4240300030b5420120681c000c40f290100c0031003070901581b00c4d00181016801e6001d954800f81001d424001d0a40c01c00115a00422220a09894481115107008200e0181d4001e80c00014081402041519140c0c6028800c50a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 873515044 1250 873513794 873513799
    0xc02010212011d090a021302182d010c080a08041505090606011d100e0f130b1c0812060a031a220c0b07030c051209010e0d0f0b06 57
    0x180200310007109048101c00d07401207045451151408a2804010070f034076400a940c0c1e002440d480182e5000280b10788540d4070030310b800c0340e8002044810420340c1b4105d0440c62000400e1800044c641c0301d40000001e140e88055a04404815290000c940c0580a414000380e00141c9850600c003d08100f901c94041c003400541c0d22810380040c40750b007210301d4007850307110b00310750b1014054074200000058100720b50230801e8000350441403a0011591101d40386400900303c58641404000a9200483e44502040c403105800031185104030211043c681c00613a075484058503001100c0c02542c20708000950055401880e10004200f09200c498a19003116000314004042c441050b0f030765501c1c1c0340d00c0111700051510407841c100c10002e04580c92850704005412306d6080109546855036144500008c45c000c02e08400d601158030424944160300c12007501e903001c011907540d811041c804841c0c0390040314000303000030800e030182c0409051001003402580d0340450026002c0e441c0740d803213550040380140700f80e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 873516294 1250 873515044 873515047
    0x216090f0b03030a030e060c0a0e04050403030e010f0902090108030c0616031104060201091725050102070516150207151b0b010902071110090608040521040801050718090c020102 78
    0x2010b0381c00703000506150801d40c4001540c0e480741c05929040030002030000d10368203000e01c000c0b0b00c410b410521600209030100c030002a0340ea903902c2c05400900c070204806a15600c0e019070000c200c0b09983c41084107a0085400b1401e60ba03960054950340d104a0401c0f00c91a0040e502044407600143c0c11004a1902c0c1d0401042c1030423500985109500654400c0c80141c1d140c010f4078051003222001c0d403182c403698401081c5045031404070318a2008162070100e00d50101ea0306c501c01440030a5040c0c03400203a1203420340d101a042071400e901106018000d81804d013081ca5610a9498000181c0c003088414030b03001b03480d00d070780d106505a03003c0400c0e4110111260808085100003000059818041c004458006031910014107003030054034646090240544885820740000c56042041c0c0c20480e01e01e171400c0300e4a99034a00d011811f140081c2000000c803001042d081c0b8407105040080d20a582840000300119524000d00700d50451a21080c07445404c1d0700c0d04140031500c1140c1100c002c40520b0300016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 873517544 1250 873516294 873516311
    0x302011713050607080403080a1b0f17010b0a08070302090102070303030b0f04110c120408100c0c0f0507140f0a15021608011a1f1d06071a070216090f 66
    0xb60400c84111204000107091300208170030075800010f03407074200381d510000300030444140003840309a0011702840c8e01401a10f00b10070210501c682548010b5034040b9450111550b510000c087d90f81d044168424003207a218000502868402c0c400c0d5044028140e000300340c03aa28684050300142902c00c1030030b2300804400d0001495440ea8001d01501e01d11402016660741d040600c000d04141c01104803040c410010402004580400100b02d01c50b1003d0002c0040c111450720000d56580c1d08100008180c413001c12401c0d0103100e8081644000c55150004503501100098100002d41214200c220380c00000e0810500503907605038180055003516004551400320103500011424180380c2c080710150b0346880260422010b152084000104261142c50960301d841d03181d10380341642c20a00004010310200820081064184ae0030304020000d8905d540c3c91300207040c40c0b60028518419801c92182070004141c58610001e421001a203143c1800c0c1410380c02d00d40248007420300211504040c94a42104 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 873518794 1250 873517544 873517553
    0x27060609180f0a060f0605030c0a0c0512030610031407080901630303062c090c030309060904091a18010501052b050706090807090203010302011713 65
    0x418042e403000c100899841c034142d9141415120640c110100031145004100003060308141542d4102c500c290140303454041013202102d000155600140047c842c442c07620001401d0480154010305d4182c1300310000150202d0f081c1d0075240d8401e403034600d1680d40c40000380b01d144141c0002c3c0c1c0000b208400442c0d08861443c0380b082c2050340500103003880c0c080600c40e2001c1c110780300070034940d006600d1900f00b10030000002c40582c03001038020380040780d1080c503081d010144a50b000e1000340c000003189010b11402c0c144c0341c1d5106849030b110000103410b428007049420800007568505680002d000790315104120003808815007140e40caa6401030340314019140085e03004400d41242c1050000c600f909858a9000b0903203401d070200d01107009902d068018030254035103004078084440c81c1610270b0400761b0140084003c450841c58040c00304e0082d510701040ea203500074643c50031a52640c00b02c0340099164800d2404900c000e00c0001d0115001c01150389046402c80c1c10f243d801075991403401c1d14603480761039 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 873520044 1250 873518794 873518839
    0x60f030c2c1906091502070608041e142a01050d020904050a0207120e03152e05010201230402010c020d1202060a1d070303110705040e0c27060609 64
    0x10b50314001050303032405000d101c1d800240000244041003142d40000300409020b500d812a034001d407410401020001001e02c111040e480d2500e082e10310071071385858440c0c14407642000b100d4a080140c0d000301c070f2600c3d041d59000034041071804079640030700b41c8070240c540c015207035980460a8064002e8082c4017444965646110300392040d04c0041780542e50b23112603d0304084900d07864011030301b88140000e80441d2070f1000101146034403210b005180042c0c40b5400803450107112010000071514031040001c0d441c0c180009058201c840030b8009209498503642d400c4000000d240b41e619003c5a080001009580b28618108400b80080c0c1003d8042e0750366161044800c00007030030a405a0301c03240c14000380194a111f02c03506403102200b00c10f4561100956107846840ba8800a02001000480520040320500c02e070b03402404000c0041101080c0e0040880d215809400414070603030f82070034032901d50303640044070800d441c40c41c06035030300030740d40d110200480d540002813440c2d08295502c0c03c400010741000b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 873521294 1250 873520044 873520069
    0x70c1203120f0f09110312070507060302030703110a0c0201020613030816050c0601080a110f0108070309050f0d08090f070b0d15050402030a1a0a051813050313060f030c2c 75
    0x2d45d07a201c000c0f40035061501d080610110138100715010020382d000b1503000308000066030020b00d00940d0302d40300c40f072044014102070950280300100010b40349450541054a59203414400c2e0207550241d55a41ea0041c03116011503000b80114040d040001d80381c400031100814040c2240c1030003400c0c10120f200310f42c036000c000d80080d00264014150b074414031402d12103900b064a012110b6502c035003200e00000f00141030241003d030a1544401404080000074840d041685d0402c03800c03203405054801d0024410340007030f1407000e818019500c50350130020010900c0016260006035482c83d0824107901100100700d000e50762580c403210080c1c0400e0300d41d1240021030041604030303400300c0c1c0e000140703080e03120040e450b82c14907110325068481081151105034200510b000380c00c0c6048200e594010200c040b101d8030400003000e40c0000900140c5030000c0700455419141c055131001d0050758850700c00e03000c6845802d00318020820310320080a00c2c6a10000c4074200c00c034900d00380041c8101840116450390000c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 873522544 1250 873521294 873521303
    0x141302150d0912110c06160c0b0f0403110d1101050c0a0503040b0304140106050102120c010f0c081f050a050405040302030d0c05040801360c030f08070c1203120f0f09 73
    0x1c821a000182d485200f10384c0d072403a424013a0a0750b41c0042d0004072940308107044a0440107813005442c1c2030008403090000100f0034100015500d00c0314007408002da070300a00040f1141c80341407850683d14180b80420404081c0c0c44440404801c0e03440c4010740c0c01c0c1c0c01988020b0f1641c421014240000385c3d00f0f01c083c0c0f0041000d03032149500c90406240c1342c18482081c6009260f6a03240440800541c0c1c2e0016132841c100324050b2803241c0d5803200c8021180503280b08080c3c0120300c2d040c4424509140c0e8000a801e10541c88003500804a90b9264185840091184a1a40d00808034903060006140c6540080c2d0094800e0044038548000d4145250554035011612400304501040402c10305400b8052113200706400c814029220030f07044603540c050240c094061ba0b0050920803402c0412950342c0507100a960001c541c0f032070900d95440c1410740e076800344800f115011505540015050440d40500c1c22165058948051029200036001c005054480000e1001515800c030301d5200c910302d214641445015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 873523794 1250 873522544 873522563
    0x203030915070c0f18021c0506010309080c060717040b0a0f09020d150c0f090b0d0b0603040b0105040b120d030b150d051806070c06020a050409020418141302150d09 72
    0x10401022817400c81524400b50060042101c0d5140100b030100b1040032031811180010f00e030b00e841c2e004074001c200c508402024200000f03260f42c682c407000a01184034101a64400002100840403941224426a401011800c14201045441c151600301103148070444200195100540c1c00140c880082007400341c40c001c0f8052155031000e00c4901071540d400c2a00d0512221b078a40070034000308610020b109492510a020680032100e103041d411102d2500700050000c3c2d102c0c1420b0404140480c0203100c2d03103115034a071110310002410940c408a00041e0f8041c007803c64405001400c1e40034242c512451139000740c4c003000c1c6640d5020440c0280c8100100d8080c00640c0c5d103814102d0000c10700168070400d405520000401c200c1c16070040b100c90741a68880f00140c4c6903441a04203480c4e60059401c010344c028004180404c1c2e42d82e441c000001200c2c8001001d10004200c20307080030388254203888801050708929481c60150421040c200d035280300c8505600d00e44080519480300711840b00e10125070f08200e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 873525044 1250 873523794 873523799
    0x12060303030903021203090a0f17043215070c03050f030c010608070e04150f05010b070b0a09151d0d0c12020c09010e060d14030d0f090203030915070c0f 67
    0x1d04006010481018040b02495030600041050381c0d2103c40000400d00d540b000745213410403044002d80e0740c2b401d0240345400e03207940c2ca4906070161103520000c5400320345c0da105000c0c90982d02c5e04c100e4455010000d00140030311803284002400396481400c058070745803070f00800080080ca04003c50001e0b01c4001024688075000c003034810742510b4440d13101c035455130702480c4140700c0000400c00046c1c006a000c240c1c22040d501a0303a0711b030090102081603142461030a000041e85004000082c94454421140c40c5181da4450100d8011501221000b80411190184848000b5403550080307011b140d9149055106240c0d0034001491302840b5109540042c0c8800e81c11404c01c0b20303080d4401c11a2039a40040c020681d040d0000c00c004490521074050180d01c0c61001c6800c9886042050304559004020401d0080c405d42100755260312805604060030b1908a004c50310950909c209890140d008000c0c40c6070060344420450440f40e4400e1510312803500300004c1001540c50b03042c2c0c074020001594003074103591 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 873526294 1250 873525044 873525047
    0x18050601050103060e0114060307020a0f03051b03031902090418060605191203230a0c030f0e130c05040509010906030b06060a02061f0510030b09010b0708040e060112060303030903 79
    0x10f01544c050310384024041700500085500c105090100e1909494407900c9a4070820100e10700711031020040c1c80e01682e40f400b4018198010002c06070020b0844041228044200c00d866aa100444000c80d10540d81343d41c200700c6005a0300240031081c80144003084006803220144086004a0800c40c1c9a5613286d07020088d80c14110000103115007600420141c0c00d01c1e1100c00e21151136149030050410a00781d01c02c2122210002030200d030b00f112441c0298890b01100c101906124004806501046602c40340c4107410340301e80c02d440741260014200040702001103404c8005051217500c5101405010b02c000304258079090034440c0244480d82000c19480c6c51030410310010340028200600560041100b81d000a0b0000341c0140c10a040c0020004c03020350400101236401002d42109900c102030380e07074212405034150001ea0180074120f6000d511070740e940603502414810300000820441d4140b004104802c00642841c0d0701000c10305040020400d4240720f1012181c0c650004c4002c251303941c0300301d014903 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 873527544 1250 873526294 873526301
    0x2040f0c021c2307021504060e09061002030a0c080c190b090d0509061c15091401030309060503090705030d030501090c0e031f090c0f05030f011e05070318050601050103 74
    0x2407507050030203981044078000d4450805040f0061003222000500000b19102c289044080c50144081da40c0c9031600e440e030082101d02002c1125210b05280070200d00e440c90a1007078111050026001035240c2170780388006a44820010700d003681c42003000e02481007500d005000481220904142169603a400c03860020101c550103081407600364032031452840c0c2e064109045a100950072103005440b061852a840c0c4840c4107070105c0baa030395050144a4100041118280c02038540d50380092050f5042204400003241b424440a800243c89070f00c100a0f041c0120019034000050f01d080e00d0005844d80c01103071406200074645c01c0003a031b65200401000442d442203030881d060a15285050154800029a4494682c104402c0b4a552080c2c0345030414182e60010140b903921208181c141991050700d150b000740319106440c00b9010b840061040c1100c103204200020007080030a0000d001404081001410002d100c1e00c14566600e00c403615484a81d0303800d00540303100714024079013981010001000d070b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 873528794 1250 873527544 873527593
    0x50d0210020406021b0415030b060406050411030a180b09061008010902010e01031a120d030606020a0503120c090d0c050f03160b07060615050d140105030604030c02040f0c02 76
    0x1039900c10700c403e00801d0fa010032000440c84840400c00100d07650200010003c00300c58031b121203000b030b03070340c90010130001c032500f005104481c211020062079540b40144001c0c0c2e642c0d6840300060982c10800180d41c1c44203503002c9503002c0e2020b0074030f803d601059520005d4030001a11001010b0f8003d80401c488408103400c00f801805940f03000344040c000f15400a404030381c0500306241419118080101022500c600d1404003090041500103ca61558041520707200c0340f004200000c2d050620100d40a400001c5074646164000b0003141b40802000d02400e000748064180e00512108105008182c0e44011124140c00e0103041200e860520384401c0101c0300d00c0c1e11001502940054400070301d540742e145200c5044440281c0040c0d42ca02c03944c035164008204039000401d400481800c019542d541c0a000b4040520351100b0421418a6034001000340c103130f09202d820380c175611110009001070320414580034640e03c064408613075400809038800503120001a0b250050740071013400c00e07410f000800e40c1c411 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 873530044 1250 873528794 873528823
    0x5030604060f1d2215050105010203040f0e04031e0e0915030a111903050d08100e042307060e0a15080610090b030c280e011103120103050d02 62
    0xb2030903d440d40a410011980240040020030080024104080c1c0e19045200802452592072601c2e06440c1c1100402e11002d400c0a501e031805c1c002050650002044500760b6400802d041095072803d2300003490300800a004a0030001b00042400c82070101c1d00c0e031300460319910744890414031170050521030401c2c4d00070100300d1301c000c2030840c440031070b1008030715084c80c2074001d0341d2041310100303080c085001c075001c46216070710f100100c0b50300000380300000c551070b8165940766030340380096101d21400007510700c042d02403c0120450f07800400e000454554940e9031a0b407044800701c502c080031001c03850030092070360b00100110301629228941864000c8201010380710300a032140070f01842ca20010541803000300362030b00802d038014403085e10074007903440c0310003d29501c12000e43d6460b10000f48204e54112101490603103209091003c810f4252003100c00c0310920694a80a40600c80d000440c2c410070500400041c0b40402c2008105040300c0380c1d1440d010b180a00c00614002c2c001050003483e00021a01140 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 873531294 1250 873530044 873530069
    0x602120a021b1c0c06062c0109050105031c0c30022b0c0c031a06060c0a0b0a020f0f0c0c0102030c0c220e010516090602070302060f13060503060406 65
    0x20060f1841c1c0710500c49420062402c03880090301440e100c0010004c5400020000e903148659030810300c0783d0646000d004654400c0c0004a0340da0b11422030640d0b00a02038643c3c190881d071107100c40450200790b00b114588035071515260100c00d688404000c50302c5840a00001c080c8081c0226914401c0c00260f03842010610062201d00180d1148207281c03061480040e0001d01281603100e1070078032444850b48510b41088079080d031243c2e245045a400f40302e000807011903401e907070001826803518000351a843c84095010348a010010b540703c028490009001c509550303407c1c0820341c0740c268503002600c110301e0741048165845400003074680c0f03418154015541150b004205003089a031000c611403c85401c292081040309070383c4082c6100395004680c80901075440e1201c070303814805054010502aa488200c017603c0547c220900f25410702c001d0043c00c0c0541c5c014607081005003042c200801140c00c0d0800740f5808c115100190810309009940032100080c2c0200600c0600d10389072180c00300a00c610020764 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 873532544 1250 873531294 873531313
    0x90d240b0312040e040f0203010e0d0f02120a0807181823060a09090201140703021606090803040e0c2b050c041d040302010f11040306060806060d08070602120a021b 72
    0x302c2040002c00c001d06e0301d00d00300400d10840d10250010b0f0b050b05415000e991900b11034800007485040c403048408010712460f10148142d0780060119860101d1680d2109800d945800080e19540c05a05001010740d00c03182c00010a604111403550504103115004501080d45200000020f016071a1002c141703401c4a041c0600ca54404440300100d8814410210b00c1a6180c00141d0302d4600c0b000c40301c0daa04000060000c10590b0116501642c1e0052a40800c0119152501200c0c0f141a5000c1d4901a503c1040107001504c80052410f5102e918071144c07514180304256000c140c10781742c26038201340746400442590803416501425a01191101030142490b00e8404420742c2141545039410291440c2c40114040c10300c00e402c9181d2400202c9014070400801c0c080c8074040d03520a00c02951365502e4001c000c210601c0224200b80a04030051540e001a03519894048a641c05501d08440b901e038200800e03030501903c0700c0d40314890500640016100c50240800390030f034001703071078044c5025042141c08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 873533794 1250 873532544 873532559
    0x20d0b300c0a3b1503190302030309061806010306110c06190c080f34050405100f09030816050708161208090d240b031204 54
    0x4440040c000c10161001031040208007820034080d9030249412010411001c690000e1102e04090060814000d520101044a188607891110b400901c55401d1081c0c0100f10040043c0d03515812080340242941c04001689084009211440340100c015800100401601c41018890341d54440d905a00b5450000710b00300d02517499490501004114540d60358003004008036810656040380002011111981403400c5400d40010501c00a5030b119400d000b08845003030301c24000c5900032425103190942680380d0130103859600d0b442911100440c5040494403003528512148400d10b0a5191030381742c1c0c2c880c10502409001560480000d081c04030100309559116031010f070140840340c0244090b43c4400c006442440c509940c420003502d036100704200482c034520701058108060043c040c1e4800129a0740500c0030402c0f202004c041d2108000380b01c90b1245d400d02200070340c42c80303104000c0c40c5161a040521191410304490170343c1d8540c2c1e600c0d03540c2e1426090420102c402800c000b09010309041c0307403020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 873535044 1250 873533794 873533839
    0xd18060b010c0507031203060302060a1106280902030a020306070801080601230907090f0f290a1805180603010507030e030f07020a1208130b0a1403060f0310020d0b 72
    0x4000d1224400e0686c01c002c552080e44803401455000300300302e50b10742220400900400c8400c0c0307607200ca8000c030700108081c995030003c0b101511140c6040c01459420012621006003070440050341c00d40668050400166000d100d264400c119a850321328855040284071460032005070050044030202007070300c0c00c0300c940c07600d001340288604890100a5680d00c44048030306c624170b60b12400e0100031094000c11035213420240041a41c45000344a140c807000c0100c20101c1d180c40d0b41c0703204040341040011128003881441c48880d40700c0b1000c165070704140e903100825a1000000211f8200302d9421041c4035142c03500b030080f2070700818640350038000c12901c1c0c1c07055500c078840c220b00b500c142e10b00040ca480031503c6803100b1000400000200300e0140103030b400c200b415a8030114907840842c1c0e44e2103001c104030495400381e40040040350b036807211004424503104800d80c0050905980443d120340541419507040001d0600d100c10742d0030140e01c03020070a0030700c0140c03850300b0065807190855000b00d00c0d0144043c0b4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 873536294 1250 873535044 873535049
    0x30801090b0609040e0a0b07021506041107030c08070203070308030703051f290c030910030203092802040f0b0301060509041101230a0215010e0f0c09060d18060b010c0507 75
    0x4c4000034121000720b9920300d0b0004481d80281045480000c00c8003960300414280c004402c0410340c0016582c900f000c00003100d4201c9140001c840d4180404400306e80704049001c41c9520902d00540703049001c1d00080d140c0f803400d82c0300f11030300480001003100d001c0e80340c0242c0340c005540d00c02c0c00b6042d2243ca407134982800c405005d07003060307102c403400481500907042c9400d840703884000366450f5a854140b12015120b62043d0b00f0035000b81d40f16140d000700d00780310f1301c00c0fa03104e01441d00180c0076444941508001c4501e4542a00310b50321013100314100542d40354401c41c981c40d5980c8a00003281c2c0e0034641031500352003003648224804e426040c1040702003410a04011081c0c1c400b460b0591545020b6504060403c80d891400f07a41c2e043c01003842e414072034000030080d00600c41e00c0d40c1c525560782e9a0071900d56100701154004240d402c9200803c00005200c0007420348030340300402d880c0c10819184482c0c1c00312245412101c3c55035540040c61010303c6032a1155424409080c0b0301440030581359102c0682d01d64091 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 873537544 1250 873536294 873536299
    0x2040f0b10050a14070501200c0709090305090414010f0b07080304021c0519031e020a140f0a0c03120201022a0114010b0703020105070201150b0d14040f030801090b0609 74
    0xe00103460360711401840610982000411780c49034600d0811500034403403120042003440100762071100d034110380000e81d480342c00e440d0020440e59041c0390300c2a001c0d06403401c0403401d0060501c50b44e0001d40c0c03036019044007a00e81c442030303004030340c5000985031006e1074603032008816020401c261400700e0040b02c2240d500640540f548003015104444486070310362090005484c3e805a920030344402d203500591140c0341030207075030303211041903040801d41091400194900c0c0941c1c0103030201c03030011b000b242d0b103002c002a04c5d4003541c0c0340344840040c040c00d10140000c1103410600b4840103104200020044016916813480210300b00310a000d0340340c04550a644545013183c8981c4884000c2000941201ca481c0c604007409040d00d503500d559895040c2c1007124101c02550a00c00084d100034030522940c1c10700d01e150450a001c00d490800d4245050b408074800d80340168403400030f580c42842c05c90040d4003c0388950b8016070241d00e03505000703002d990f041c0c10400303019003001d2107041d20b607131040161080c84004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 873538794 1250 873537544 873537547
    0x40c0f0e0d0f02090408120c0a08011205150a0c0908011814101d01180809060d0608190308092b030b100e01020c0d050d1808070f0302040f0b1005 64
    0xca060040c0407034842d9400a41c45a4803000700010000141c0241000100711101c1044640f5800e048940c18000d00c841c0c48002039040c001008142d02c107a004003421030044055440340910941c4210035540100e13080c04d40f8036159601402138951001c100d40c010a8420000c0180c0e02c811040302d42c0c0700d0100040074042c3c0410401d6801400014402401c042d00000b07000c114959440308010044128840a180154602007241e061503030384440d030100440c0d01041c41c40c03400c000030317042044e150080c5296904031a83c8080c045644001044a12021103102d4450400110a45030041c2505030082c41c411541d0030500403440760005c4005280380d041d09224182c00401c240410460041103550030980c0e0011402400081194021103c8504c1407400c0c1c0c2a03a40c0000d0b52000d1120402c0c030208001d1036641308145032801540300700c18030f15104107440240c0107404c0d03070b40c03a1642c504103168004207249503003214200214a8140b00701e60700c0e0366071400107000e08580500022600e10303c1a01d00d5003032010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 873540044 1250 873538794 873538819
    0x16200402070b162a0201090510080a021b0f0c04060f180903051c050906010f080c120111031806060d03050915130b18030a02030d1805120c040c0f0e 65
    0x22643e240d10b016000c0020f04100030140b1000380e0308a404c00d801ea0110344440404101707400d19a0203058007170b1050326000c1058450320030740c100940c071001e216650b40d81036503100c01101c0c00500c420b501860703070754004100008440003000111000b40e8840400c111200b0000c200f6140b034043c1d80806180b0b0002e001500c1841418259002e2060702c0c001c0b101c3e82c030400d401c4540e00c195544080d000300180011103166a80b1420442c40c401c0d058000d020707a590248060840c01c0c0340c501024200d000d020000070a00102d112000b026541059807000700c0e5401c06d2a0310480c00504102903944681c088603001c0d5100c207030b41c801034a41c0c4201c4265031301451049a00d07540701c0f4070100c100e60b0204046c010182c500750307450950140d0750b04200100405031040e0002007030700d850f0006010f8044c0da002005401e00b8a8001800e4462207004042c0c000c0e40b90316060005219030316411402d07500c3c04910702416800400900300421241018091f03800c1c440c44018000542d9030100201c15480001d071142c21a200 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 873541294 1250 873540044 873540047
    0x906010605090112050703020307090e060612061302040b0c06072604050f1002040501080606090f100c020409060902030f0706050f090102030c01110913050412050f16200402070b16 79
    0x1c500410741c8420750810041c07100e00c82d4107a000310b01c20ad450f569600e808548030740e00c00c0800c8130191031039680100d0500c45400928801d040107a04a0401444030740c1e044c4e00c40e04820144d81240e0700c00c1d24407420110316240c00344010f00c11350f40c1c412401e241214200403011107103401c200180320403d000025800c002004c202c020070104a104900d84110703001c054071300c010100070758481c1c0200360004900502041d058100030007554510400106040e0068412400303020006111488400402c00314146100142c0ca1340c1c4201042c460041c1e1010170041d0b0640185841c004c0d070340c42c0750100b60340316842c10010247e03c40156000038680f08807180c0e0355521900101e185001764010480305500e09000a111402d1440041c0354503103040d00c0070f030b10b5450128940d0007215030454015210b01502c5140c4a840e5100f1002030030b1210213aa525410410303045c101000b480c4401900300d03403102032145059484212040c800400f46000c035030552400007103550b20883c04101900010070080182e03020034085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 873542544 1250 873541294 873541307
    0x61106010303051c020d0e1c03060b03060d0201090b121005060a0c031b050303010807080105071805151b0c0108180c0d030e0306041b06050c19080415020601180509060106050901 78
    0xc20700301c1c00078450142801c0d00d10b88c03030f00b2100b461004d640c840c0d03079401c15a45000c0d0146004851000c06981e040d650f688040c4100d19407012030803410400c81040100e00800e4030000382070050070b8010705564501d021300d840009121140c1209104103014810003080b0f65010001c060001d40c50324181d00c1a10607065244086609050010701600002c0000301c1d2064000030307030404641c2d040000f801240c581b0700040c0d44544a60480030000c0e500302e01c0c1840703641000c860b94084000d450048500d001000e024441c03421045480e020100d80140165014543e070244006030417807029000c01c41c0c00103514604650340ea601d480342c5801512840c0084040c18040c840d0303100b2402c00602594040c0c60f19140c00440f03100c02c1d440202d5605000300c00440c11501c240c040d90b00c0d2074490317030003000040000c100d440020717507043c1c1c022601e4030300400c400f01d500c1c1c10750742d560859103419400802d042c0d41040190f401c00340c0b990803414080d918180411078010000500a07046078614100541d50b4504000104c3d0b95 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 873543794 1250 873542544 873542557
    0x403080319060b07082203020307030b0714161b270b0409031107061b030516080d02091305060303041710020301030b0f0610080604021c06030606061106010303051c02 73
    0x260f640440c41106100000c0b006025542c00c600c01c2e01d403000200c103455480e803001404065050341c000c003005c0c00090512081d8503008001c1b418040d08040c005110b03840310f84d002e0003401020340c81d20030a0340c0402c024444000342200800c2a1044540c0c1044078a40e03000d400d0401070b40796100e11980500c03c08403950300c149050b2034040c00c24803a00b241c80c180030b0f15102d1340c80c000c50801d03c02c240c0c0005015100e501004038040990038404811052601d08603860703044001c05501030721280c01d12000296000008003a1244d403480090f0700c1d07a6005040100f118000700700413504c0e074248402c02c1501c0d07170003200310340643e800404400300032540e2400142c50400081300c00c10051b84000000700501407200050b500c140d1500e00d64020507654201440389a00c1601041c2000c0390555001c82e000f45040d8000d400c003180d06400041c1005040d903c00d9040d54880c1d48140c1c0d1060741c1d44401c1c05241d602c10010030700301d070480d0020802c0d540f451703400034080d1117501c152490001e65071510b841120b01a4040710032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 873545044 1250 873543794 873543809
    0x1602040b0a030b060a06020a0f0605180601030b071b08040608041a09010510150f0815030a0c050a0803070b06130603020d0317090f06181c050306040b0105040308031906 74
    0x1019180d1500f440c6020341a1307801c51082940b24000200a4030000d01e0f510040d40c003002003070001d4003643c2c900014100c0500032800174414048100c41c50482003058034000c6d80540041801030074500c401401142c0c000c000c003110a00030403400d42c00700d07810308201c40031103c0078903050350203643d03900b840001d40f035506121141c00c0d00c14805205240c0783c1500114081e01c030030041801c03070596810305603071000f80d0041d032040421104410300d02d01c513009052080e8007445000313404016044a800281c28000f001c0c1084610742944441409907041030050300c400345c2502d0f401589031a080340c8450360300250041542e40701e404640010310b51041c060308a00c004540c041c0c20402201d10b2454090034045495041542d1581d041001424181c40014004240060207005d8407040e2a0024418041e101445511310319100b2500500e80740d400c0c080729601c1c1019a641c0d004d480381041401c11041e903801c3d5a01d24100301e410301c028030114400c807040340d80204040d510b4440c80b035201c18901e00038008a5001c1034 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 873546294 1250 873545044 873545059
    0x1906060f1b0c0e0a0e0c01050703170703020c010914061803031504060b040801020d11090a0501050f07080301060804050f070e163014040c03021e1f030507080702031602040b 76
    0x42d0501c01e805c41441d000e9a00c0c15503080c600c0d83c80044030540500b800144c00a60000d41500d03181c1a00111150000038501d0302526100e6402c0c0030a081d62170040044601c420214504008414140314140d000502600c0084411316090900b940d24000940851030301420348520071566911940420001d00d02c440c4107580340c03940d0305e1040e4000c0d003100e02928101e03418071140aa400f903500d000c6810305480104444d0010382481c1c01105d40d604200ca0b0803094410801c00340012034000e070080c50003813400b41d0f683c0134145800e103809411314410101281c5c256100304000e0105070300419a150b80800d0f016000002d1000b1020200c0d40d8001c00040c10b640c198404010440c40e41290344090004101d1241c1030000058180030b82103d420101e81c090301c1a030f1000814401881c100866408661070401c444494840500000301200640e05c080c0b040042d80410180078140c050103026401007e03820440c1483c501800041c0d100d106010004008003a01c211900c2107540303542c013031151500b0281500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 873547544 1250 873546294 873546301
    0x60b0d0512130302091e07080103021302161505040507060c081917041103070501090302060d050c040306020c0106090c03091a190f1d06071b0c0b031906060f1b0c0e 72
    0x4c40c410181804d00c2e10106d1503a06c0003c00c290b0044170410304a907030140030880720548104a05000750400c121400070b1007034820140c40401e0321311030848200940ca050024150a01d840c1a51410b44143e00500501a00340301d500301044104055440340040c000c00d00c550895030f54001c6950f81468402013107074081d42e4042c4800d011a50310306240400003902216842070300c500055551184c14403000390302c900c3c02c000c14100000143c209a4000341c1c00d100785828240c50369140002e07a0400d64482556a5494404001c6d00300c4134000c82103102200e0508225405c0c003915807081d54051035141c1c2d030800d01c2000104501441400000c80966101c00d02040051903079408903001c0c0401c00900314282d5841c01092801d2072020542c6801609251141d0481300300706940c0c00040c912044080c0e418201c4c0d89400507042c60070400031803180e01210481c01d0301c070241c582c0c20002c481443d00079100700240382001074003060b004410403d060102080c41e0440c0c0036545400362003400c503500318404591032403060 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 873548794 1250 873547544 873547561
    0x203010f06090509031c020a2010060515161b03060b0f01052a01021303030302133002030f07080312010b1801320403060b0d051213030209 61
    0xc070041e100c07032071814400b0b0348580c1802503076801603410107503651300c4802d02003031040c0301350b80207108291440c200400282a000400c00000e4400500040d06e50442d001c6500300c2402d910985018140440b003501100300780003400d0025004030222150704440880c584400e004400c840c0c00640f0102214031100d403510392400e4009030042c0301d0340b54000d045000c1c0744603556000344190781c040c43c100c0c070501c800a003029503207460007103c0e1104020103542c00c015214440c001190310030003550081d200580d030b071940c0036060441ca036003a41c40803031080e418603450740c440c00e031541c4046500005140000c107500c600b400024107002001ca4a40410711410600040c0d00c0008400390500d0340740280c200c565a03aa03030324450601e100c1d082240740100300941c11030b0101d41c000c041c0f081c0a446d602e01032a020070981030301d03035406c1840404418080180842c3c00c00c01c00285004940881d50180c4140b030702c182040d91026616041e44080c4440388030046001003442c1c14203c800d60065800405030000350602581 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 873550044 1250 873548794 873548801
    0x20703060e0a11040b032a1807020d03140601140903010218150403210210050108010204050a0902040b031b0f03250201090c05090c0f0c0c0111060c0f0904090203010f 73
    0x1045818070300c128450310705494540314503000c0c820043c001c1d021f94400c16400607441d4246694040e8000c2010040c010310fa00d4020f080180d1030744140300d8145c3d07414a00800383c0361102c2880142c04050604000030003941103140d005810070800e0909100030302c03d805030050340d800b400e9001909507202180710b07038a04800441c03806000301c0964191181040046c80c100c21845140009045003542e48681414410801c1c51241d41452038410380300e840080e80007500aa6000b03034001d65590b034021800307200518003a0394010051841e910304510703007803801841c4e42240c04010003006550007400c02000b1400c0d83d490071200c0c645104104541e4a16090160340300c81408001c010700003429580195542030b00502c64102440c0e0402031130001d80d45440104180300c040149150070080041c00350700e856107041d1010740800200c1d84083e100c0c0c0c040007000100100d180b0000b07803005600040911451405080c100c0f2400410b80501954a40008010401403d526480207400d58a04002d00e22045074a60 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 873551294 1250 873550044 873550063
    0x22050405070c05060408031e0403020c0312040602070e060f12012a020331030302150f01060503010306110403150203150a15030203150303030702060a0c050f09010e01020703060e 78
    0x690800003600d0310701e42280c14005801c8028a181e01510110300400d21100241d54400108040c4035182d1100d22002d001300041520100c016170b011004996140c501400410340e540c042d10801d0b4201742c40d201d402560342a0500c034100c80f1000c60f1000c01c5840d01d481e17001e50b2258002408204851008442280c024020700042c00004410782600c17405040f141c005c04020b03810103900450070100c0086040000004000b010200640c404d608200a08030803018500118029000742c454440500307031120501100030004408695441c00500c0400d80000c190b905480e00945c000541c40e490b00e408685920564001038140d084240720403050980e281c0085100300607468100d01c405600f401800484e031131902070a800c2d0000d264022603424401da018507440080c1c10b40021004164030301185c00c503803064130081e0040c1c00203020003085000e58041c00c01c03103c0c10fa14010b40340228441d030004550159007603c41c1080240390000301103030f208101600186030412010417091800c0180c065507451441c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 873552544 1250 873551294 873551299
    0x40302150d27020415080106060504050102240c03040c0f260c010203161a07030504030f020c0f040207061b030e0118150c140f0301030209010503061e0a022205 70
    0x3502030141e110010400c06640002c0c0140010a0380455081202500d1000d884040c02d1201590010f881c5900b40148801040103448242d543ca0400c03000904002e0400789040303109212401828000c5103079070a4551012240740f003141c51342c5807464421040703241581302c2d100303803440c4403008241c1c251340703211005409404405181c00442450001a141c415800c400c40c00f5070014000c101ea00f424009854a05030f00c1040c001307020040307616400620f42416128500000e648a04110030180c01c1030358170424100c64001092650740b00d80003e840c00c0e00c5000803901075070300844c00100300305283c2c0254402d03c518000c0700d80b45043d40c92009004140d141a4000e0359070818055880e4541100d072007040050f0080da0144050100138003c00140a5403848c2c0c10030003182030b080112130076a24000d009040e500e00e06844d44c0c0d514500402c045540c0680080e44650850000e0100052400881000801010849810350341d25448104001e0103030b1141c0342540c05e0002019840d070812b0703d8060007524000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 873553794 1250 873552544 873552551
    0xc0905090108010e070605090a030803130326040f03050d0c0f0306091e1a1c050c0105160201080402120313090518100b030a021309110618010c08040302150d 69
    0x80710000c50980350032101000c01a0003000b800c6c04424490701c0180030407030000d40b18444140e0740365240301081e40219003402c080aa25201001010751040c1e82e21000d6030707100191082d0030000c1e000c10b440d0340000b810007000040450508402c140c021001d4442d101d050401c100411403060101900c8000768800403800a4034203c00420840c9140c4148071407101c4d102000d60902c804021030000808401d01d01c107801e426075103090100c0b40d640300d82404009007142960326004400d842c080b0b00c0c10000c1016107050203400e00180300340c90480f100503180784c0d40910f0126a192240e0002c11640c01c401c06401031140400500c0d00e114016000c1c1000032248800e5040005036141480310328290b130301c0c07100391880b900302d003044003a280000d411001040000409840383e8800a5000542641189074a00c40c0152584030000a000d070325a001015880b0030f6030b51030301d0000400a41d0a2514400060a041c00416090b1205000c1c1400580e00034650180c44101036001032200c1000c0c42d0042f40c034581c01d0504 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 873555044 1250 873553794 873553799
    0x1050105030f4c1b0c03080c0c0712060b010219061d010501080a1b03030206011e180f0b0a050609041d010f060f061e08070c0c03211b02040b0d05010c09050901 70
    0x7404c03141c0c0001c244039942d4a88502c842c0c0d81e02140c003014003400c501011030f002d2000110390342007842008000c1c044680c1420051203d031603e001640c01b405203a5055400a1305407410003440300d482c0b44861a03120a001076007800c01194001c1940c0c986d40302e9072840d031900f4008a48420000340d615a020b020f08404c449071780a58916010341403407404018016040500100107142282450048280051010000b015180c019521503101c00300d00100c24180c035030f4500e2646246620840300c44060a8171902c00680c00d25001c10603500c10f034403a85000d541e83c1c403a00410f0b56001c0242c00c21980704c45c40240540703c81d0f1140d2201405540c05148001302d91100f00103855400b0f031910103080900a604243e040e2440c88040c1e07100e4034001c12020500c21454070100000340e0310b8004401861052900d903103124039840c440c02da60580f22074420140869202d0940c3d0381c0400c1c440409985604a0b07010400c8a0050041018400e0040004100b90708100d40407030515000032418003a64000d0b10a141140c0c0e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 873556294 1250 873555044 873555071
    0x3120c180803040f170316050703020901090209240d020711090108030a02060a091a1e1506070209060105041d04060506010806010f0305090c060a1101050105030f4c 72
    0x2245211310100c1c0f0841c144204050380845141c6518291841d0603a401d00c5500001d0320f446940c00d400480c0c66401c4018240211f01d0080050f45c0540001c103002c60a180070100441d00c1d1041031052419244820b4080110060f0188201d440c4c001781e0545c00c3d5210740d0240f408045a80080a03010f100c3e14003100042000741c0000305542d111409603000706800d4503142145401842d4680e010340320072081d02e040f4103500f00788580043c0584503200303121a07005d200780f100c4028408003900355507081c4450148140190343d0a42511800d03901211038170481d869100050710345100f50362010302c007012070302100c04084502e164000d218a00034101846540c5d1203200444401c00120b50b55030114170094280b5800c00e100e0340c0a1f80c0d21440002c12030712003900b8200040ea503900003d105130b000450306100480290000c0c0152401000150000c007074001000b80d000e03844840702070492545802540c03008258140c040d117006020480039101040d21082580c000d8565045a404801100c1c103051800daa402c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 873557544 1250 873556294 873556297
    0x503220203030f03190207030210050a0b010c082a0d020706050304020105030a150803030a0207061529040504140106030b010c051b01020f06150a08030f0a030903120c180803 76
    0x1a401009985001c0e0641c6150f00103801c00f40c00c40300300800349900480d4800e403e00c01802d515001c4e4008052410000d07a60006036400104a035141c1420980e0601d0f00741d030011184c44d0340d01c0c0e0040c0341c079848540f5411190880ca0f0082207145625001180343c4207907501c040b81c0b007005004198251500c0644031300050b142c900c8266002400950100700068030121268420700000141404042015580300f024a1545d0000e407000520710340e0015080040040900c0350f8000380d20021094520b0502c0d051002e0762081d41e0305400c1074004185200b105130b070f4044204683c0a064024000c01c0b0b29246002c0b22010000309001d00c101091509686407025030003a01311505042d0302100800b1800110182c051502480805032410b500c90148003d1290a091009a104072184844001446e4060041240b10542c542c41400c55400030000301c40444d003800c04641d003144442c01c0104403601c4506e41240c0c070310300c84003400000d680380548000c040d80d4000362400c2d440c414010840a4261079402c03103920b9 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 873558794 1250 873557544 873557611
    0x1c020c10082d0604020a020309040501030c08160b030604020c120a0f17100314100e011406060313060b150703020c01030507021501052b0302010516110a0b04061b0503 73
    0x90301955001400f42d00e8190020240c80d022841500d00301140c0c0408907054900a8004888080f20800c00380b01040080120400980311044540f2030035162146a00580c4000b0305280c0c01181c00207400704030360304204005850b0713054003418141c2c2da41907000300078803243d145000c0d20700059078013100d885400710448805015147c00e84c0c001412502d140c1d10b1175030b440184040310095014021f20401400500c0c4200804021400000b080c50141c5100514410500900d42d40c400c1e40c007402070180c08030611502c10346403a44080e000030501a440c000074030800000784600000f550000e00e02040590208032242c03841400c1c0c8041c066519100e02c140c1e00c1d80740750102c000315a00f818004001510b001d141c412843c031003001c0600312074140c00c04019100000b1400640240c0c1d15102402a520404170075540036400300c0c0380c03c13003541042da050749440c1c0a100b01c002c3d10480d140c5010809006035a881345900540c01044000080d01803072001c1c0c21908201c0f003e14800f100310800114a0840601c007006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 873560044 1250 873558794 873558871
    0x8070f1a090c01031a0402040f0e0901362102010605090c2b0c020703150605090c0d0b09150a0b18011107050303070305030402091006021c020c1008 65
    0x2002c540340300118001e00390921100b40300501429001d04c191198030080000d00415080700180508103041c0b80c2c010303040a0a40040d60f032400b0400b0b105600b40210075125250340c0310078402452040c141d4020501c1d03812802030106240c0e00b14068400b42180055240c00320b40343c0091000c9030f42e40f020049001c4040f24920100c0a0801000352513100c1003505540c2d88400e0110cd00c845501d641a0340202c490314000500035a000c10000d105001d0250005040703043d28820038407d05081102051040b00c014110b0322181001040c0c1104400142c2c100c100b8030b49000e805440c09141541210b00c1e524001c807080b41c005c59041c0c0c00444c81c45e603030b00112015021004803284007201c10800445100076580f11100e118001e0050201c4c003650b0a20042070114002e9071001c1c1c49040a004102004802610303401e140d00d1032a1040201c540c000c1042c03001002d540300a58406503054400f641800710070034290354020202240c03010303801d801c005500c1c0901e0703203d00c0c0d022042141c45d004900c5908402010756 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 873561151 1107 873560044 873560053
    0x90a02090307170627151909050309011116140312030c131d0c09040b0a0e16051312060f1503120c0b0a0509030708070f1a09 55
    0x41c41590034038025003800003015130b00f60340e65001c0840300802d030462100050b0488813a284021031f00c400c4284c050040c580c41d840d00a40704e621603205a80400c4502041d414a0b000000394000410302401c0da02030300c0c504011401000ca5009081030b61316104064240b0a40740c0b40b00c01031409103440b02ea00710380b1442101110b88543e28190407640c02d500c550b80f01039031b2040c00c1149068024050002032030b681c4840c0310114024018003c9101d8011411381000103031b07403104501240c40780480034489420007560400c06c58080c800c2039090b510325503107464140034013460341d885403024034499400011600c51500c82c143c01d40d214040391a0700350f444950704009015688a42a0041d00c00e4903000b141c100c0340c1d03540c52a01c0d0801402c0f007982236a0750b5000410406c0c0c10000c403201c89821641d8030340c07600054036180580740d03c071400071502c9600c20210840741c0820030742c249008000310350250 = true := by decide +kernel

theorem cover : BRFrame.Cov 873381294 873561151 := by
  have h0 := BRFrame.cov_init 873381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 873381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 873381294 ≤ n) (h2 : n < 873561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
