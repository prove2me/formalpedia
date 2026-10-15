-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4925
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:10:41.482821+00:00
-- url     : https://prove2.me/submissions/c0fed20f-38fa-4088-be10-9bdfb607f474

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 885611510 ≤ n < 885791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 885612760 1250 885611510 885611557
    0x3005070c12170a090518070f020609030d0f020f0706050121121b020910080706031104150210020c0606090619090203060301090512220e011806030f06050a060803 71
    0x2c0b01410b044520b6241060b40155176000182d041c1c0a080400f401c8540c0100034003614540240400b4650b0100e400900043d1501170320303040d264001ca64000d50003d80751000302910441d0307903046410300c3c2008151141c8480d61814543c006140074010002e140104482d0b100c0200e004012566145034008181c13041d140756810115594946880c00401c2c004081c400e000050390750754070701ca1050440900e0a0001e03490880824034007489580303c82d00381840c0c0350030012681410000c89064614481442c5904c608101040340380c84030f000703040c40c9070300c0c400f1410420825010031030380d028031030455104109072a940100520410300026120b400302002204010411080c0c01541d440700d0010000589003d203921000e09100381c8170f11500170744c0d0000800c840107491107250b120020b0000c4c400720034502d0520480300b0400d401800340600c40c4100786d580d00000c18181d00140050340d40000021681c51a03031038464050305040e104850800e0900d5400300b00104000240d51070580010300321250039000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 885614010 1250 885612760 885612803
    0x9030237080d0203130b070e0a050405130b04030504050f010e0d0f1e0602030415020301051503041b060f020d0f0c140703020d0308220f3005070c12 65
    0x2200c088500c20340030b00c6490004a81480518030540c4400b002c5108500249844041140c0080114060002c490003126083e21000403030f000f079404c02c0c2c41c005000d4a5504180c0c150840041340100055040c0c0204802c15034850041c000300d030800e8a641d0b001100c0140103440300d007031031007a20381c02041e0400d0071004603940f00700881455002e0504400765440e449186c442845585200343d81d016000000e01c000c2101010005d010581248421412b550410300000c15600036026a113030b0100f8048003040900072807140302c00f80d14240c03040100710720f59240805072000c1a4110380700054000d050843d075805024150401000290350754464641038155120034009144400c41e0204c2e10450501100607103030040d001080324000e807504103040c6040349104004142d80c4040383c1380e41842076600700000700300703011a03401103500003811101d812951388542820442900120078070001144c0f50800d0310f030424014441d0900498140c0800c0d034980c034511604650100000b00f81182d0159851000d444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 885615260 1250 885614010 885614113
    0x504110c0f071805251809051b072f0907020f0d0f0504050312040f0b0a0807120b0a170f01060e060105071e0b0610080f16180801090302 60
    0x1102144c0d010502814045c1281001150007050049015480c00841c10b00700212014020700f4004010710561030401c0944d0900c1d41280281d243c50180070030710404001c0071810a00c3c0107a21ba6551400b4482d000445107114060400800e0007100c0c200c0c0402c0340544046811205009164000c1c0203120318034004494866200c01d10004015040c0004070385035406111100d2101c0018a100351154184068024a19100e6101d48070207030042024a40464125880a42c48401800c1c4000074810306040d440103401c81d12941030b804205814040f900c1c44070b030301082c2c91a0907030200b10384e0b40c3d000045516080740d0310f0380284000d402100c00012300c150b1160b001068483c0c0f081d18040301284203040c428440c2041003200b21500d0a001040064504080421403c1d500035441c102d806c50034945a90046c4003405450309003a00d140b03040301c0e5129402030444410312010318524a46a540d1060228001c00104500301c3c011b005184c99038140680000d5a180d100c050500d40c04443d201c0e02d400e001c042c0340c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 885616510 1250 885615260 885615271
    0xe060103120c021f0924031a1c050c1e0d02010c051902180106200f07080307060c0905090a0c02010b13021902011503020909070504110c0f071805 64
    0x1070700b50004010b031100c1d81c440e0030184d640311031602001030594015004c07007541c1d08501c880c03021030310110550458107001c81c01c104041c1d040010341210380d009003400c500d14a0000030f8000080b9030741c031107210500d51080c40c4000e02460507114500f410340c0810104003440030301014003000491079030440f85002c21580c1003241c4141003950421020ba0365860a0a00c169a682481c200b40e500c41c50035820004050307200f0842000103504958100750000e0a4200d0302004060328004002d81d4101141341008916078081c4807404035841d19946100e0a0b80d60351011404071a0320b81803011402c100d0380240050f90603610010300c446682e55a500941b03000b001c80205460441d03484620f41c1c07059031202c4006200e608014400507a464031801c0d4040c0d00e000120040000b16031400320700301108020f2a10490680b5412241c4140342d880341c101452031314003142c001c0c1e540b1900e401481c46080300280c0060005000031030644580300c0d100c4407555145e54040c803030f000480c400710704440c0c0790309801c0c0d0100d076100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 885617760 1250 885616510 885616517
    0xf030311030c15011505040620120c030703030f091a0a2307020615030d0c03020102071b050a06140f03180a060e16050f010e0a2102040f0e06010312 65
    0x40e0300780c41100c0c0b0300f00d000d202d01070822600300010300411503001703402244900d03a03080640c80d16107040c100615903031f181210004030341e20700042820381007001d2140d94074002014030f0164541d5030403940c10b6200e60014804501080c07400e80030b09100d44030342c0107240a080c0c01441001800c1400c840050f03201c0001000c2c91082c03551070a180c1c3c04101500c6d00d035141c503030a0300f90441e2145801e401c0680f030301a003c0d00c0c0d82000f00c02c842c2e103c5119900080d010500c11184d20385400c1d10b16081c030f8242c0c0a4021804000e103007003100c001200d1801a0441190119a0110340c003500e095504c84082d900e00c45604100d03070002c0f00070070200094401301c500464201c2c100d80040f4465011509080c1e040005401d4201e40c0c01d074440c01c007482c0b40003080203100d0040041c00008144079213401300041114198010160502c490b0441c540102c1d603840c7c0e42d0b0b10040140280f0924019607000601d50700c110441412485503280900c41045c01c0514400c41c18120504402083c0390390950f00c501030364423003880c03144040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 885619010 1250 885617760 885617767
    0x4050111161a1902030403020f0102010b030a030e180f0604060608090604061107021305040311070b1c0e0703110411030f0406110d020d05010305060609130602090316080c04060f0f03031103 83
    0x203d03001c1d9140d129107804940c00f442d2070710700f188100100000292207840c1160b0422200103829500030078403d51499050400102000480c0301007903200d9042900c102e1104081010000c61004005417148250022101000095115107064411200c2520711200300d60150000400180085c1d100d84100750017030710254200940c81d40003400c140d0800540b604015100c800740010960840e04000340c1c80c441002401d6218100303d502c2c02c15009800a1001d030100c40c1c24036440300038641d0310000706207052b4810703100035a44034105810301064a654050085d490703c1c109000b40d8802e134061301d000b905591402d8000380c49548071100a131101d10308010b401d01c0104800015900248001c0c00b01e00341421000c00c00d9031542c204503041080042c0841d01900680b410400d200012400100c0519841400141c85031055004280b07413000015038414849185c02c0c0120b1020f100086441c42d45004480c24445a902d030b42d40980200000d00c80c0c9000708800503c280002030080e010380f03012456040840c4d05 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 885620260 1250 885619010 885619027
    0x240405030406210c020d1e0e0910081203240105090105220f0918021c170f0301140409170f070618050d08090d1110050403020304050111161a 62
    0x441390b031841807001681c46001e0000103030f504020f00e4006040130710310009120031865005880c092450115902c0b4007103c4000980222000c00a6006440442d08036150500210b42008003a4030548449000c1c041405207640142c101c195030021010069403041e06240d807240c01520590844501d05e20b00400102034410200602240c0b90010681000d00568851030a00f18000711449001c240d40c6440340490000056160410260390340d0f440002c07250701c107030760f40d007890b0100c295504051405100000b44181e01d40161801a5041ea14440410030324003100304104411102010001030007407601c05647e00841d140301010349240c03518845100d207011a1580c1d00720840e50120031011207451004c1b4010140300040080410038011400c1680c070303a045c404400c556681080400408008140310402c103400380501200c1015022000144210300703003031401940380d4015008282c001340d8200d01802e0995000140c1503906510348840d00402c9044c40307200301c030144100700c4034000514108440072 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 885621510 1250 885620260 885620327
    0x120901020a09180e120306040e0a0b010501051606050a0207022e0305150603041a0106050f070206130305030a030b030c0d020a0b0d090c1202090a05090303191b02240405030406 77
    0x80175080741d60441556850070b1001c00080f9444442c01e04c680750b000d4201600003a2001c500d05054a4013420010744031041f9080300c3c980340164000040c0301609000622102034050340103008c00c0d41c42158103544d40c4603075071011410320302c15681908070162201d0314443c1f05070180e4009a000040034070502d183d040c000740803801950003038408490030031291070780c00d00c1c02e40a020b1044c0900194900036250541c0781c00c80724030902600401a01c12a000160b014644a640c0100c0c40115071002c01da03078541075080000750084c21034421080c000d01a846d14003c540c503005d0f60385291161700034510803420b410a51b85c000d07640c1104070061a61503849100d0710100d01c11688030030003003042c198802d20980103841440100740e030240001c03014504060500c52403600120640740c0c00440c28440c1054041e1803044103000d0315a222013803c510f202c0400c080032155010920039296601d4901c10317a40d00c8400e49680e1903005003201c0c0038165030028407080c42102d1040f0b40900700c8009150000350240072110014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 885622760 1250 885621510 885621523
    0x7060b06090319060608060606071704050a0306020904061418100e090a030201110702011b02010c02090c131703090d150614030105060f0109060e190b120901020a09180e 74
    0x1108055902103c40030402e150061101502216001d00180c0c2030110100780c0b140a581d40c01801040918040720410754041e06640052138020001c00060f0b607282072407802540190707506801141082c10100301e0125010488014040240c035421708444030000861034080054000480d10300c50750400103000e8407041905001d41400b5001d003030100d91903e401790071034200c01000d000050061140030701607a08001002d55002d8001000003803e0607500c01212840f1345030800a520422400901c40031501d400060451503250503450f84040b80c8034250a1500c0000c0c0c2d11100c415842080600c15500701071130304945051041074086030096914200001360b03016608070006610705205a01340303c1c07409004103500b190341500e420802c0c001040000780303482042c1c05498180820350484210640f24401408041080c10748450140c54541108265690109001401850510020501d420010300c21166042c802e0b8540b110b041d07140c01d50360301c070a142c60543c1034006075442c0c052811480060211 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 885624010 1250 885622760 885622783
    0x2e050c010f051510030606080c0319060321090506180a0b191704030f18051509010311040e0f04021305040b1902070305092107090f110c0307060b060903 67
    0x280e1a410031100130b0010b510105440701c000c0504045080241c16005280c1e683c12075803903003401e66250b6501680e4000202181d600407000d61a01d0303000400c1c000c2c0740401005481c80d089044c04400111802120035209a002d65503110008102e80c40d0080b001201c100440769002e802d4480385540c40c41d00503500d03000b0301038400d240d00f0840480041c42d035100d55a900d420303004c00050680b90415840081c10300f0845500740c41800141e000b025025040a540180100340061841e00e00101081c0c40555580081c1501400f0a041c4808100603c2c4004240c80035105200702c90080c0c0e594400c3c2c0c1010190019105030b802c00040000146612181e0003003600c80c5004e0380b481c600c6810498405840452a905402d03109441480440d0000e03500800b1600311100403103112030702da0344200c40302d00141c904c1c4801000368451424001820307502c82d0007515080c0100c10040203024111380c140106031284054450f00d54000300803520028406500c2000c1c4c00c000500464140074000700030074034100c60400c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 885625260 1250 885624010 885624031
    0x3150e010302040b0901060c060c1b06140a110f0702010c140c09060301020a02030406110c0a150305160e090a0e06090304170a02010e01140c070f03022e050c010f05 72
    0x50003507080038003540344c0920b0241e0740c9224962500c0002040c481136010010200307034480e44240007141c1302d1201c445082c90000c80318940c402c0189014001801c840c081c000c51075844200140083e6003920808a203000320720b00c440c0c40e02d402141d030122244d12421040f4188101c4519030030101c1c102404600903032402038011311a4020307200400c400d807c40208454400d80c010028412071550210581e801c032071150615011550030b00304100e090403a0781642a4011400f8040001c140009046c803560720700c11510100801e032161003080b070300c41d1845130480c03000c502c0602e6440f0281c109440b8040d4451b900348000154904540310b00c504044064509800c40d920100e418070030b80b0b44224010032003200c0c903001040c05001550001e804084890030390750622a0784000290320042c40b0b402c039140108050300f0344a4007500c0d610002011b14550105900903800c541d5000112420040b902c00320010051070200c0d2825510401c40389548610803116242d500c41000040b0424070780540d9000c0c003400c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 885626510 1250 885625260 885625289
    0x4090609050a06180c110d0e151303030e01210e0705062d07050a0501060f050306040309260a12080c0403030c121716080117060a0902010315 62
    0x505000d03150701a00c140d044614224003000144082160b1050764101c8204c0441c034681c6400c4250380245003441844268020312140c0c5070255482540c4d401c55030400c4030011001501740381c081300180542040901305900303044050010a00900340298840707014902940321828500081c0d0882c2d100700c0004032215101d404e10384c1c2c1c2503014040b110142100742c0303505050656031040c1421201401d90100c01e050800d4400d0780c0aa400403040b1090707150004202d403409001454158000c00946c45a2817109020300c1002c6031b1443c01086280c011901035846480690914400e800c00e01481c0d80380f2100840c5a0196055509060100721341e054002e005084480300c041c04043c2c100700001f021140005003c100a0002075000100c403e81341d60030117659540e20210400680301d0004484880c0e8038110300c4403c01001c403030200c2080e094404169105500d43e41d840c1c40301100c60306024a01049070b0841c10020f544207645a000c942c08600500d40424001c07601e502c1c00040c0444e41d0071048400e404034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 885627760 1250 885626510 885626519
    0x120313030c090e070e04020604050a0b03010f090c08062b0b0603060606040305060408180d060c020f07060207290c100b010e010c0609060b09090109020414040b2a040906 74
    0x2000034600801080b8410b002040c99000311944800080c020b08100b0594032000c6410b546944065030080c1c8005828400e08507190409001c180e0401d109240d840401804081901c070803a0040041c02ea02c10388035004075444074402c004018542203912a540b814038101c5070007016600c805e0001d180d00403081c0810074103002090500b4100d0080c4002e00800c41000104001540001d07110b522a800c4803e1649485000000880e128000c64640b070f84150300465007000c1c00450b44c00240811015000c40302ca10b1600c0810030740700d4030070340b1584026800410041080208544400c4034101070540c41900050309c0c0441c01c015608550b5400703c4071341c0f0002048403c45181d10803c6018042428103e03d00503a400000b00500503810009207030a8070744034608200021900314070003841000300624100d00d800da500c94002d080c0000142e100c1c50804268440084071583c03414020740c0c0000c00001103a0741c204480001c110745404011402c003240c0d8203581a0000100500081c03d070902002c0303415480d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 885629010 1250 885627760 885627773
    0x209180a0b0108100815070e0604030c1d01050f06090114040303320405220903030c170606160203030415020717010c09090c110102030f1608010803030606070212031303 74
    0x820040d40481340d10001d00001c04001448000c000c420500c040044d91282c00c21100070f0101c0000da504804085004000c1001d0303d966181a140d601448040b081c00300724202c01c0545085c4103203904595212a038074000e040460041c561100d0604080800c800031608a20190744554015000030320001807040c9002d1130b01c100d2901c0540d01c0350300f00605402c90740a00079244174030312615101d040b079048940820384110300340c514110841e540c00c100303415040c01c01074003800c0f040c00f0a100049060b07026101e80701500c1c0025002d000054006802c044511920040d001d0100c941079038188800e010000780c110b80117a40c031880101c15806810350350728024441e030501c044002d5074480c0742d0401c0b54081e12154810014030440d146030b0404102414503502c252903003801c50350f245600d540000300300300c601500e820405020b00d120f081e8000c2035040049040750809002e00940520f50010000700e01ba500d0040d0250003001e0009007003081402809044904d10f600c1004a4000d182802c002001800362 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 885630260 1250 885629010 885629027
    0x703030c0203130519030206220501050403030801030609230706020118110f011808011d06060603040f0501021209340905100e010b190c02010509040209180a0b01 71
    0x500c0c1c001141004482c040444a590316805405e01440242c03d003124420811940e610056030080c050564032010090f0160840300101c03842580c8020b6150000340c603503c240d00f00d8044036015540e0355641d03403c55803043c000c0e0409660603210025188007a0252296202003412110019401415000c0c0341201c06400c8d1410040c111111008141400c0003007a030390030040c40070540c122907410b44804c0703000040c0c2d840311f11007100d071280d0140588045034922055000c402015070500004031444070014105a80b000308480301a0008000d10208000a04144061900078800d40000d401d00e414001845504102201c2a42055011000052081907065001c510811809030785c5c40ba005003c104841000d40e091158880300c65451002925105200005402030034038811a1034195039260f108802e1a000455922000e11946000c80c03010703401609028039003036060311403c0c02c0400382c2c82044005d4010705109a004013401d42164507112411006500ca10b0040c50000303200321418000510310b08 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 885631510 1250 885630260 885630281
    0x170c0f0f160e0708040203150a0605031011192607110f03030c0c0c030d35130206070506010603020c010c0e0612040c0f0b07030e0409170a020c09010803070303 70
    0x3010350780d0078015140000002c0d0743c0703c0c80d40c0c20802401c0e251440401d14021034106148824800901800085a4650000c4048840840c1180c00b10344c113400b212403c5138024900912032172020083c0d56510b00d19a03d4181810750b8908111504031034403075260006c01c9000c0505c1641c0b800b88010030030415080940c42e006810050000c2056070742a000c0c1c0d54cc2c0784005070101d0007030071021500d000350b407100700701280c11002c002d0305841c2001c080180180c0216161000104c0c0b00b1150701c8aa84a8014003041c038005828a4081c86601d0700c0d40000c41e1000010b054082c1d80000c41000040c000c1842005418000c100a80e1300590b40d28000301c802e800c40c1d5041010004021113000b188405503a8601554001001aa8821042c0e2140d18101c2c1c007115403584900305540c0d610a001680c0140b4102500b8050b0107911080f40e0108404108000c64400e018010300c80300030000400300307841100000e0301d4403140d1801116840303140040012000701c0b00742d00500980d4000102c1000f01a41802680b1014 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 885632760 1250 885631510 885631543
    0x6060c03070b10140109050121020c060a0c08040c0b07080f0c0607020f030f1b0c1c1b060215091f09150c0818190b0a0606050405010c170c0f0f 63
    0x4005004c0020300b0400c8a2003140d04104502003030700300410200c0c0c1159030800b0a00411540c0c0c221142800741c03964021a0340d03180c020700d00152004151701800c041e80c4900e60046c4041c003c030303050064081964000c404113032601c4505100300040600e03d1002000075001d284001d00c041d1400a00091402c2014031406070750b81c01c1030104c40700190891007910002032a403001c45801c100c03200302d0309280c8110340c407015900c880c4034a42c01c144da1010346d030202000d42c0500c2107005424031131401205040c80d1481203400680c4910140c0500d0310f03410201c0e98000c800b860a454010000301c01d404031f05113042c40d803000f5013036941140104000184c45500401b503080351051010202d40a800340c42d10100901041c060003c1046485007101d090054102ca0300c800c80f502041c40c020340c148507800c48021074044002600d002c0c40030410a00a20940e0110703541656031040c2c0400980d143e9421404c80075908049001c02d00c00c1c95050f44090040340111007400380108001c1c01a91030440c0341440c2a01d060720704 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 885634010 1250 885632760 885632789
    0x14090c1002032b0f09080706050c0403030503061c060e030406110d0915030608030f0d050a0b060d0e3322060c05070b0a060513050c04060806060c03070b10 68
    0x80312201040801d10032880042040351003c18200005000081901c4590a2508800808016000000d80a0f46020f83c5042041e0380c0c0e000e025003081e210700c4c040035000c1981480040c0480c40c0c00841c01500740940e045100010a9070303651241503504103200c02a15070000700e0284200c903440003031078240003492030003403001c207902c3c20014004403414001e0140c00f0b1800c50300740101d1406a000300000307110f160100c9030740780001e14441d030b0b1300d07008405072480060030840400c5441d0698040c44c402050020200c81c80d000e125680d100c02030802c5402c03015035000b20041c403101c18001050001483c1200394179030240d1b401c441e01c800100c210083c00465101203c07041307003000d00076000c03050070342c207902a00004000c2c0100e401640c20340034140000f00f8500205040041c000c4151f002705040350740c10307160040d8081e480d050b440c00391001294850b003111028041000740503c84c41105400c20805828585440f011031350041c110390006106070345030321031001441441d003c10b1040000034525075550381c0b403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 885635260 1250 885634010 885634027
    0x609042906030c0f1005030709031b180c09091a06070501150e0702060604020a0527010f050a08190e03030c03070806060c060a0b010323060a09020310090c0314090c100203 75
    0xc0324101d03440d45d0041100220000d00170b54080c1450b080959004000800350041a030050074000b6a11300501d880340300000f640551040c0d09002d91010164a03031181c844d4542410106030003444e10340d0018810041e401b1400380310707480e800000c04001380540c0020550280b008074100007800a0752110302690418010403014550103d44150864811180560740300c0358507008417100d0088040301c540880c0000307d02101f03040c90480c1c03001c50207402c5c0c13030b00e5440c81030455013a18507002d400300440200d01c00c400001c2e160400729503494140c0f80c88900025109441826562a540007100d0089000e80700000b4802c400342c0150504d43d2201c01100c2e4245044c034984074844d01c03414080e0805d051140c17201410049a030007900100324101c400540760054545c0c2c0750f140346049200351074040c010802903c0c0411884954001c42c3d200e40456003550a1441c980107826008148511104007015514100e80889100040b0042d001e0310030305000b09012030980c81000a90b0b0020081081958010404d006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 885636510 1250 885635260 885635269
    0x30705070807020103090b0705030a0614030a0f0204060918110a051c0f050609010212100f03080a0201110f0a020c0904151a030d09080d0201090302060609042906030c0f 74
    0x148040c1c0d0200c986038840c070542c40107070068101d4010041004444008020320b040c1d118010f0752090010000c1484a03940d2418484904403140780c0f220740503084800c456002c5841002083d07201440070b0000520107a072182d00f00115095060312801c01c00c004109102800310340040089100c00c100d03152401946070000081c01e440c480d00c0c014280380c064981c0041404010134240c0c1e0031035081016250280350081409000f07511802d031445200d0400380215450350580780c021010b803101c5d040460038883c1991201030040c0c11031401c1b402159214800303e101c0b20078000c050b01004c00c5007220a62200c42c40c58029080045d00c841546c01074a0300700801c00402d80445500ca41440300b4200002c800d000d200620141c4030045003041c3c1c15101d000e05c0c0304030242c0d000207000103c1310400b0039121808802c80049082c0e419168004e0016803040c000b252a51920380c021941051107200040a940010500c82c4482511010700752105420003081005504090003d509900021121084441003400c0080c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 885637760 1250 885636510 885636517
    0x14030601090e030c120d0c0201140703020717041d07020105060f12030903010e030301080105182104272004120f0f05010e0c010801180b040213030303050105040e03030705 75
    0x512040d403900b8182100160620445401072a04800d03181d4040401ca0b00f100d0b240e0000c00783c078038560302c0c0c46000c2045e140b06200d030f680f5411000904e00125104c0c10812006508030040684461000c1e05401c41d1107401140288010009559507684074081420081e11100000381340c00c0c19a41031a080040d00c2e43c0e0040036240c03144007110940c003403c0002c6a140c2c42c50140030145a01580313400c0c00f19110b440d000001e03504940040000b0f011641c0d984003865080c0100700a00c504c0b40d0301c01c0c20021720144220300c001e0b00352100c15002c81d080c1950b616103c82a020440c04a40c103401900c810400702d40c17428021102c60300c012149001605400d842d6111807403003548107464124184000039410000720303490040c2c1040d000080002600e500b0b081c07450080c00c400110940030b100300c4605068035401500c0300c80c125003807820310840c009208034801000d05082a40795900660030007488101c83c170000d2950f00074502030343d4001299814003060000f15002d0304010015a4828000c01c011a640001103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 885639010 1250 885637760 885637769
    0x120c0e281b111204030609020f04021e0306010c08070303090c061b140c150409050a15060807020a020907120f0b2206051e093306040806010f0f14030601 67
    0x2007080724155030007400c080e07940c0180f084001e07001400200b07002d00c3c0d4110030301c0d141c000c0310504e100d08095030030002244101e090391605801c1c00e000b0b1207840d072154005158800810b0411003d12411643c0308102035100f85022008241d070340c1c1c01c05040c09905207044003d003110303041c4464030303000ca8500080d0a400d05c1c10001c2003120006203030401aa810301011240385d001503c00e6429410769070007040c1d1500540240c00e11185000d001480c115518051018404410051a40c0302820118100c4814200a00000a42c81030b00c240c24010303150300c01c425221380704903505e607a281c07003031000d41c00240d4014101e2034010a0408407082c20550300c036030606045866912000b0031840010b10300001401782030340869401452802c001e50410041100a800148120741401c43c503a5890888040e003002c01488901025142c0c1c1421800c0000e0b001e805e040c18002800c1c00d0400c0d80c0d0f25582440c01c0005d030040248951003520400c081c80074540c01c18080d1075a000c41c0031034100c500700403030b5075207405104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 885640260 1250 885639010 885639017
    0x5181c0b070810180e0d0e0310020f0301120302150a0608070e09030a0315091806180b061003020c0a0c0f05030d2c0613062007120c0e281b 61
    0x1130b140005030b02d560240f0400c500500955a41c1252600042d116200c400f80795802805042d0590350342c500d0750701c200c0306203072450780490341581d00b0005d03c195001d00300d8000714194814548405070744250f60412030f101d0342c0004400706415051540b80c900780100381d480380440d07000b59810b21840b0b0340c0200943c0c6140c80f440c9000503031060007101000000d441c0750700a03910326141814014007048114040d2521034040d01c814021415031480c6d91841044101d409800303402508003050040c50003035444044402c2515008d403c184100e03018070306050704564101c40303d080700c1e142000190382600110008000c00c801a100003400030f0350281c001c04c40c40080c111070605490007044000324103500c440e61054094119a25110b52441083c2030443d140604000303e0049280b505150b4541004000c02c019000081c0c080d0300d00d400c41c41d0544c106280d50031561000c0d1804d010903140311219001e44258075610f480d100041452440c1d082d4210401d5149503c14100209181c1403503d039684074600054921b17 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 885641510 1250 885640260 885640289
    0x61205040c0b07080a090b070218190e03030603070603051603090302210a1101060602031c02211f030f03200f010c030e060f010605181c0b070810 64
    0x50440c680441c150051041198041100401c3c00030000142150821544900b82200d0725602c8650a5004a500095001144401400c0000b040d102c0d469041000400e503108241c5140c00e680d81522100a8045155403000c800c02c0842e1400300004030041215040c104024202400301540d0b0401c420302d05c0c81455260800c07041014400c00c58550100f8403100d4881000c800030221803150340c41105014009001100c00c4084840306200c1c8000722000c5400644c80d105003000c0d614a4401440b12100300c0c03036800e0142010142d10308a000500140e041e00140d490b1030801c01050320030214030388281003144450310510001300075944040d061364060408802c500b90380003525030081410b0710015000d004100340440410b07415080070001520b2a1002d0110860302c4003095541c01e011100381300c00400f1400100140d0380038600400c0c1c40b100840e1036100301c02414000c900d001c00c00748003d400f05210b01c2c811b0418800304841d42900b0050518101409061240340e480344000b640c05480704018851 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 885642760 1250 885641510 885641513
    0x6150b07020a0b1e0f120f04020102012a0e06041a03220213020f280f0305041a061c03021b041401030201050306040204080a0c051008070f1b2a05040606120504 70
    0x1806d0366444c0c04940d03020701d00ca25010641c1c4d100014241c4080b4050741c00d041601c454400c00c2e00c1849000b02c0544008001007a0400c01241c10644c1d82c1c5285030000b03810080171030380303617484426840800d030400200795581c1006c403003070b0345503040044103449035800803d1440d0040c0e40c0d030071f41900c2c90314800501680301c0721610340d401c0b4284612001c00f1044083e1460318400d003a11004420007002c0e417505d81074048210301d5000d0302a9882120020010441c400c11280c0c0c0101e540342003500242c001e480c070315045c1001042c40b00380c01c01c003207026005640441c00751001842844940f2205500c191030074000c07074910506807180d5a1042c0070007814400044009030b0315450319416240100f001008a429000b002d04041800c1c8000d030080f0b5024851080034101d9881c01141d0132800340020360785810421300c08050450b4402e940046481c040000440800c020400618003c6103843e4200d00c0c00c49619295040928550401e80c000303170186040c403204109264120b502c030a10b4092114001c2520f0361036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 885644010 1250 885642760 885642787
    0x1110703030f14070c031101030e07170f07232b0809030d0302041805011a0904110f0d06080c030a080f0f040608150f0904060906150b07020a0b1e 64
    0x4091801c10f0391408158081400a00240003017103a00803200741040c80c20080045050b1602120016010351046404214201184415080702000b103410780309440120880b40c2e00345074127540b146200c0f030f6a20040a600d110164500d02c0e12040c100c80d0b00c0040c1e4503c00c1400314810791540410165058980141c0521240d01c044402d83c4000a06031034041400c110090001e4106020300c00d85407c209403440b10001746071040c107059800f210f5010761240c10720540345080d9880b010031240c0041e122000d007011224032501403c40f500146030101d813540e281c0980031003110406d80c0445203603405483e4100f4651004a4902d0b8566009002c181d5a15044060189a407040540240c9420303000600095801da000c0341440c01540300404042e00d075590754040190000c100c411550b88100500085400940c4a60150b504648168804a060010f007108450000810f40c085801c03442e0000c1c45908510344206100040c1201c000c1d89030030f107080ca10b0007000c004643c000000006a0004104060404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 885645260 1250 885644010 885644027
    0x7080103200a03120c0302100501050904080708070804091d070e071107031202070e010b0c030f0a0c1406010504230411030f030d0f0b01021506130605030303100303090501110703030f 80
    0x400542c0e541d075204007003800400e000c06845c0140e0044c002e1120391400f800d518091a030494800501c408450340791503ca65183d54000c550840d0111000c11914001178004409000148440100000c00e81643c07c02205014450410640540c0001700188420408210b031aa008112441e04a908000803440c091400405030400741c80070f0035000000c04050340c005915001d540f030308042504207990380c0c2d03882020b601886080c100203070818000e111074154042d01400c0c1300101031034080a59441c44c0c40344524051998a4100160003034070051080741424026100c00c0e43c50141c8080703540740d04070140407030001c016000500c91004820b2a141d01d68042220444e0003c009041d0f035541d60300303c04075100420071540c07402481c40c1000c0c0003138541c0d8004204d1030302c0c4400c8071001e41403a58607a002c0013000f40244090300c152a94a10700821191004c1015512681c0c10064010b11030f4114140038000c185181e12442c10010740c0000c400d4100070225199040740d2b4181040600c5a091880c1991580b1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 885646510 1250 885645260 885645263
    0xe070c1b120c14060a0e01210c0e0f0a121514100f050a05060a030f0204090c0c0203060f010b0715021213021503010f0e090a080c1507080103200a03 65
    0x400d0750900303024485464100c00c1150240b040601610300e80c10240122801801030340c0000c920fa6032600105540114028424140c4001c0e0000c01203401400c04002c4982c1400841d00099800c81410b03014103144044d00c014100c200d4010740010b10384001c2c00c003103040c04840200890171220b103d9494400030b401980790110040c203506c0d020324140c0100c8484207100d221f0692501204440052541007141c0344905444014100f1481c1c0041a40c06a001e8005900d01c8a8034990800c0300140b84041803140c12040001030762200c120b00000e004262034950090108010000c0391001002810300301c000b00c0e81e030a80d000040e144020018069000280144e14004011403003960412521030760b280c50560100740708480c0040007101001d81c460340c0f400300740500a44400964030030b22007415441292a0f001440c00c00b1540740805a988404054106a0000707001ea40214520300c0c042100c0e0030071300e50050051814400030740c59a104d503e8201881c070100710340c18421454040903512038440318405036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 885647760 1250 885646510 885646529
    0x1110c0c040e011b0807090e010b030604090f0c0902130b04050108180a231c0909090c050301060b131a070807060e072309090c090712180c0e070c1b 65
    0x405403c80240c8105c3c0c0441c0d4020005141ca40d001c200d00c1d055401850580c3e050040d643d00715030358801440010045000300342c844414844220380090028130750782c4080d00c4070702c5015856001090b1050004900740d00012a5080e0900090100f0f036401301d116075100c14080c080441102e6082e15050411088030f0020b01400d40e0f4010f0f19080c00d6014034121040f40b503c9040754200c46813565a050322141000f4483e00041d040300e0100322004041c1c1014040074012031281e002e180d0317a140001c0c2101c00992114840b0f490200d05034400c100d800d41c4450003403500886c4110320134421040b4070054441c4c603100900103600803c2ca90b0a001469003e21203e14650007102d1400b9140d09801c1072070442e59980c45c1c07140c0c0b10900325018070305010107035a01035102c820003001050110700400001c514010881c40c03c2100c01900005120901d0280b010116000a1035000b041d45c1420000d4603e82650043c840f03400c04641400b041562101d560000b603a00140951000c81c415281d51661076172030b60200119 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 885649010 1250 885647760 885647801
    0x150501060206010e0c03071e0207090501082404350c0a0203010f150e0a0e0d0c0309140f101103070b151f030b0d140105040501110c0c040e01 62
    0x341c0c00041e0203050304c0001030429040d07a1400321504052004860f031200046025900402c0c0e001061707500803511886005540c80b0540721540c4500700c400c26072140f800766000081c00701c28190801e6030200e4a0190300b51484043c5403135221400085085941e1401d0b5000b00c4680c419600ca0aa0040f0010078050380d000b645d07208034010b8540d44038210601a0f109520300741d06071342d200445104640b61541c503180100300045c0340c01c45071100d00038001e0101005944074401c5000a802c00c0c0309420485034240c030b42500904180c1802040240640c01c00030700c0c4600241242c01076070311b040784200c1108080310f0200b101146030307800b201d8022840d42c61441522020a080082142d0048214400d8442d1900540440110401c00a5002c19104d0306000c128920301c1c500d0304640302e030b04820381c4414042c1c00710380805c41c3d41d0f070f440800e9030f00d8032044080c595440c1e09000800000b80140b035004180e46031030340c2c02d1084081040d0303158031842940c0c500c41d80e612808008200f90070740011040384d490083c0c03902c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 885650260 1250 885649010 885649019
    0x7060f0c0507110301021305010302030c040807060809060a0c05041202030f070603020c0f03030f0601080405011803081f0b090423040b061002060c09150909070e240313150501 77
    0x4a034019480c1110b070346050f890400c0c1d02d402d05100340c80e024150940d010290070b2402c0015002940040c01c004107040c81000041502d9200700b0a180c0140710b540d568008070f20b040035881d421f02d0800340005062600380400380d01000e43c0700c016101514a080883d0408460900c0001e261031140d007060318440c0909040001c2c601e400d42d000d030038961010021f90304840c01006403e9100e100859940c02859540e10124031554400c0051580c000d1092000082043d03201a01c030000e840c0c00303d0b0031000a051002003082900d100c246040340c1d4a409a090f1740c140c0d09010004006003d10115540141d668008416100d1040c0301402140c001d401800b96040c1014100702103580e800b202c00d10b00601e03840741c0b40280f491000548501c1410054881c5090140880420056078011007800700c0309501031020000d503650342d900560065405407146000c5100060500200c1110a0b85221080400d10130381600b074054001103d60110300d4560600480c0114507100d0840c422202001d00c10500e40341c00400c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 885651510 1250 885650260 885650267
    0xe01060e0109060605070209150d050307060b0f0d020907030c1803051b03030a052710090603061202060d050a060b040b120a180201080a0b0607210203070b0c07060f0c 73
    0x905807510000b0601c20191900700c02d98940c481d8441c0203400002420015407000c40c4400d0070000004000c02101d1440d10715262603103140c10a5805984141d643d01c01e807801c070715110b01c51000c10481503c00014000076500019800c0c000100542c007450303214005000b0f09481900c0a01205042c0c40c1c14039245522418915500c004500305440c00c0c02c3c0b00601d41401e49000070940f00c00c07603c0c5541d414a408600d0311080d02c262541d500303c52400c4c1c1a103408061950f600b0b0b150307044c40346444d940e282c2803a15040c8000c041e25555480464031803003102800025890b04e80440d01804a5210041000c0d1510000740740102101e45c00040010030202d00810444010002440d501c0e225800303640490b100c0254040c11120843c90030b10f0384240c01c2141e0401940941d040d40d6021418001c006556030564002c100300350321240e0700b00c65000302e40700c224509030b500300048090032940d1b2009505100c2c4554509186403130142c90454105008207040c010801c050b003180c0748000492031b00344001001004040d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 885652760 1250 885651510 885651539
    0x1508010e07110a12020a06021810050414010507020a051c030f0810031101030f050a0f061703400509071d040c031103100518010e01180e0106 62
    0x34803019082004640c0e0140320700d80005007182c018000d411104020b64481070104c84244410040d030240c0c040309004034500c1e101420102242e10b64180c1e0b810740c06010061448004480324080c0001404240a0031520400c00c0c14064000e00301103644980e00d0002030034a610b103a120075800185100c05046540320006d10078881031213a01c6458690300f20580945880c0022680c0001c3c62403100c004102103a100d10a50400c410107040008074810a0016081078480c101d580d5141d03203445064500426200d13203c0c80c0004c02102c1800d4035585203c0802035100d10450080c030418012915014418400d038088030200c100313101040b5048490a0030496a00091920804e445400c40d400090809801400400c08102c04e202a42d4840c400d42c0c0c040100800d158503081041642d1388030100e081152000086003d02c0302d250000d0342a070f24203403c203c9102200b480301300c00b020b100c60040005100d055415815201e07040c4000c2098111f04042d0703c02854240b9204840f50300b040c40006a030341c10f0f41c0c0c11 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 885654010 1250 885652760 885652769
    0x200708070b0f010302010c060f021903060512031611031903020c01080601021603060e070f0b03010302041805030a05090609061b1c02031e04030f030203090f091e0709150801 76
    0x900c4459a50002c042002e41000d200c040c0c08030b00d10346203042c0010015031080c80c0e0b44c181070b0350040c24440800d14070007620100301d003102e010130350f24181444940b4145459505441c810380c015442c05044100d031001c0c0708107640004102048038030411419603800d0208100000c0c1c1c100140c0990121418000d640e0b200c0030b407100740825000170126440303510216402940c0400c2c1501c0828551031503442000409030159000b45c140194940841c803c40035010040040c070b0f400e21002c0e102d50541c0100803c90f40031080352951015a51444400248044195041c030000c0d0701307215840b1089003022130310901c16407802070740c0131b0800600400c0101e500f5a0085594010000300d80c801031080c005614200d032070440000160b48248100a250924240d0a05003480b081c3d0300b40341410b036240c0ea01d0600b40b0b00f0b00411005a0804242d8658505042c4c8a540f0300801c1111280d6007070a05642e620041165075004149003040600016551406150030740c0013040010320340c8801401c0500c005107500400e004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 885655260 1250 885654010 885654023
    0x40b0105010801032a05060c010213050306010303120b0a050d1b061b020d08041212121e0c031401080d1e02150910050124031505010320070807 63
    0x100300c0754400c07200355050700da2010001d9a44a1000911259a110803c81c440760080707511012550b071321150040c0c005986110005078545088501903281c0d8505904030a00940c002c100400100307a0000d0003c418100c1000f00007410280d00c0c0119211500940100703400c8001e04080c2c4007001840ca00c2c1041103260341300c3c031440c80c54a0b41000c0f01c0040310f04286002003c03409400c40058506100080c0e03419200c0c0c545540b4160352441c54601e4094800b00a641c42440003c00300c4106801902400c2c2040d2905800c12032107031040c00141048100324100f1070800c0c0d0703540d0b0f06201c0f10f00076402014405145442140c266954444541d1384006008000c0006002140a08402c81c0c551201c1524051270390007a00d4107000c8140c58521044d0014620801845030716000401c110991103124040e00c0790820355011642030390813032503040102103a01d508040c50b010902c00d000c1c98940d04a02642c0091801142d003025242840c01d000c0b882e11f0340822276100025048003084042802019464401ca2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 885656510 1250 885655260 885655283
    0x2209090f120212030610030605040c0c0516080a03140d14060103140f0103300e0f01081021050304121a0c1204151b0305090f0a0f03020a02090a020304 66
    0x707412a21801c48242111103d402800402c0603072400c52024520000f0034600002c409a4400001d800d5500c1244d900022404100c01ca0f07040c01014860248819000e125084078149072180540e9241c4101e00c0240400c003407014507640704820582118401591154140700c4803500200e007880850041d5210b9011174941001c00090040142c095441081c000c56406d6041e0f1070b64807480f03088090300d8001845903030410243c58480c43c030302c00b002426204655030045e00e4541d001c2030140100b800000941130084c03840401c402c0910a00311031040c0d9108130701c07401030081844041560035180210090981c0004030f40802c036001c50a070040c0040d4010800d01500c650244100075003d6020f69200b4000c5000300264141015020001d5030824070403c650141e00f03542c041c03042c3c01c4810302c2003005100043d0600c0b19588552500515801210490117040d1070705050708074503503d0704050380040198100301d8810003418002c2c0000046180c028060380c03402c1c940140113500a5000301e8003100c0a04404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 885657760 1250 885656510 885656543
    0x51005271003031d010311071104050705090f040c050f070b0a180804060c15020c0105040201020f1b1c0b090a03020f01060e13051606030b0405090a0302032209090f 72
    0x12940341c02140d426480344c3c030b000d43c81c4c2848940d46840303041c021410325441d024140112455038000b0643d45010302c40f08440c1108601c10003003910000f416540070008280140e280030350b100c1214018000f030440380004d010196a60560300d41c020041e12030036410000c2a140180070310b501d8030750301c9603c081900300680200050800080c0b24248800f42144100340010300900703003c2c4410140b158095510302c11198114546101a079200d8003500d44565120001d000455804011655884c07032510f0250801d100b07150386400d010204100c0f4544554002049140c01440449035400f403590408510a074514004101c2580c070302d10a142140148281e0b021810030315010b1281c202503034403070001c0c0d00290300d030580c00388884ca408020035103c5014a0020401d280980b16645000b072049031008280d105c004010001169001841c44182c0d400110040c4006640442140d010008200c5080001142c414441c0101141e1f90000b05105281603c40410700c8041107400d080c1174443c409200b007400341e8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 885659010 1250 885657760 885657781
    0x5010c0e0a0515030c0d06080102040b210405210903010609150e04150905010e010e060105010905030703020f09180d18090c091a070507030f170c0a0605100527 70
    0x80300a6035500f61090010030034040101d001404090900f41c000320703c19031a4240e2608a03482075100003202e0b8000108030060042c001c41035015004501d90f0516289082c1e25115120f41854511501901034140344048160801c420707910701c02c5000d0b00030000f9a4940030040003c00000d8118425241d4005c1c0018040321461080e80c450703540b1010181010300308000d014060301000404a4240d5200c20340c1400383c072024070540c8040415100100b01d035516010003d0251145500a1070103034000450500140e141ca40010350050010380395104a40e5031444086011018105012814080c6454440c01c4541c4a002c0344e01035808c49404c1204655034818503012038020b051080c0108628001c01c200c42050348051a00d44009890070340e00d010760f07a950f200d003451160f41044a1030301030080000709104402d0541440d42500c901454034240e40343d00f0041d61351140000080110b611000001c1c03241c55000603a2005202c05042e0014282d9100085412080080094000303009041c001411502e00c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 885660260 1250 885659010 885659029
    0xc08061602030406082206060510030e150a1e0501051008040f1b09060e100b03040f0b13060207060c02060f060d02060d0e0d0906020c06070b13030c05010c0e0a05 71
    0x501d400451a151500c603094a80c0c5c0c2d402045003095841c012080028101c0c0c44820100192240c6000141641400e04001c9400304030b6210104062400089102d0f200c40002e403840c14104041e041c586968949411501404950380c000700d09d10304901d20410094000d4120505072201210030081319a410401290704010442c1d000e0f0608100f40f445202040c45900b0302c4448042d2801c0034207840e1f0302c0394170040a403411544070000d10042d000800103220120200c1401802c1400d2415140d400c15031030300f04083c1030040d0043c141c0d001d80800300315071641c2801d0b00c0900b10b40c051025526804503003400030003800031031080005400703000d0004e051b59049102ca644031300703c001c00b500c031002003a800b84104c9401001a0030001c81e9a00c01b01c43c02260b042001d4000c14070282c0c3c421071018100701d8000e007410400c60105000b2002484001e001510000c4469400102c08403c4040d14126050449000009420162032540f078801e901c10721750790003074000b035032a88259145180c4d15a80c0c0c0074400100b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 885661510 1250 885660260 885660301
    0x160501080402100c050109120e1504080d1107051009050f03070501021002180939041406091005130e01080c090907030b0f0a0c03050603121c05040c0806 67
    0x15803034600044044d01800812401c140160000500d240b40b55540e06913a010401c5000d0114081038503024151905129101c6ea8801000d200b500f424542101166151024505c07442030100f42005c0b680405070400000c001802c00a04641c004c8240c1c7c0c4e00900400c8450058900903102018458410b0400140300d00850300d040e802000c0b01071030308000364000d401044082c100104080f003842c3c1d950351a0303a0b01c54046e00e030400080c0242005500c00c45030000c82181800000710102a44011a49029080e036080b20381614601e540080310320000ba545220344100300b58400c030f00380501d218142d44280984101c42c01c2c4080040c10380d481e0030f040b495400003403282c40d0180c0c1c0f10051401d000d08240c1000e6030048581e07801c486003280c03a50303600c20508104403030501d00c1503101c03400c00200d0340d042d00a08d0a0f00202e402d0400172800c10101280c0c542e500f105000f2464040040c02a110a0440010308211041002c04100a0809242c8564241c9580c85642d01e2032040070040b5041e840940c2e410740498 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 885662760 1250 885661510 885661519
    0x102031611030c060c03071202040e1f0e0f0402060706050a0902040b0414010b090612011707210b040305040b0a09030c0b13030605060f0904050312160f0311070c0305160501080402 79
    0x50345c420600040903880140084108255803007150845842d90010308003400000000540d00c0c82c2104103040d50b61085200d510050002550400c8882c070610211500300d12401011402c643c0c49001040d058414010001c0072a0b1400081001c84d070034581c002d2552520072030f8144003c004031410002aa1080d0061031201001031004008115065008040004000d000d090030308903480c0c400e000004099100800c089001c031040381401109220b0312003e001210801c14600190702c5184c002c0c0540c0c0d00b8014807030402f80021405050007013041e81c00600390f00b01c83d00e03a07a1510b16002001045103220407201039000c0c0720080b44102148043d1440e9040070f0541042140c95030b00c2e110082c1c00081c1903242c02114071800c84c0155140c4441061007180528000c681c0c512040c40c083c0c114040c02040103541c1035101583e611a00e610500c0e0110308411450042919500b4841c000c10340c0c422454010503940d40707040b000007000740200e203910025070300420040e40c42d599000191135580c411074000750300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 885664010 1250 885662760 885662773
    0x504031206150c2604061e0c030f180807060809060601020307080d0b060d06081005061c1b090c120b0a0605072402130b07320102031611030c 62
    0x410721401c14003901e50300984600ca8009841044148108544d1080020201c8002814002c85800c68401c9885052500b00c1c0300350000d2400d0700400b6901c540380c2c000c081200d8041d10200d413610995001078100448268184c125690320a407950f50481c0f8855207000c00c40441c0050f0940c4800b2900501c05d03003042e0065841c0c8407460303480c00d07145e500600c0c9220b00103a844c64844403d41f600c07805081070300d0404100081503422b10044524000c080c02250020506000030012140c07124078912455800b101d0034034129900b2458a400e1000141c82c1448044070b800d0000686118550061b0300112400d40b5004040030545820701c050700d01040b81182c0101d4480ca00f080400d22400060003054012110007281c04080045124050030118440300400d8011480da240307003c000c00001c004003d241a21172901d40d10313981d84105528628048018088000502416a054199115482280c14000f103559140480d508503080d02011800b01c001980145405401c00000088a603001c2001c2e0003800d0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 885665260 1250 885664010 885664049
    0x28110321090f0d0306090f0e0a0204021c18020f090103050c060a030f09062a0c1401091b1d0c0715020c0d091d010b0d0203150a03060504031206 63
    0x4000740a040c0d051160032050840d403a4180030003044512190f03404282c0a14090002040d07800140c600f204c103e2400c0c20690b4008000100c43d43c0b0f841d07064502603207669010400b860007145000403090114100102c1d4540b0114461018401034821100001064141000d00452060900000b0440d5010311801201407419030090122003405203008900c15005050a80c04e507510020b04850481e03d035000c1248403a481890a03450401000c1c401c020b141141500802c000300411000d81914400c03103c0d096a10b81c203400c000c3c03010740c02140d4854011914150007800929910400544c044409003d01c2038007014050380c2d0280e5045100a420030070980c0352201840c024050841001e982040481200001440b81444080304d5844a414407464455510400417a1400c0110400781a40041c0000c0320070505450094070a01801a2699544401c5000c0040b0000030507600036803003072001013000115080148124032990390591500c082641010681d00140144520b0580b04003142c0c1c03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 885666510 1250 885665260 885665317
    0x60f03030504230d050a21020d0513031712130803070522080114090d020703030c06060b03131103012c1f022208030702060a05281103 59
    0x126501c003e0802030741d4001e600000038a03d0303100b1810444031604600304281c207001c1e0024590300e220b070864410030512585050025224192202032a061050200303c1d6045190a40c4003540a0b50b44224451949040d1204583d242d403c245100c0e0b00c9400c07000009008601980301900c180c0b60b0096980c0c0c19604c42c480c00ba11182c20a044000161900c40345031241c411040020a0040c003a06c800004c014480c12a1070491003002003403460681d00038080c80c6001e95000036002c0440ba014a0114a10309084c40c0c4840505a168403198446001100380300c8082148440806130034440d0750074042d05410442458281d4800c0e0b01002c135068040b4901250301004c1080c1803002000c0350054950034260b01001c8020b44130038500d141415540071440714088440107609158110900f8070007269140313001152541c03442103140c000d00420b00803828204150080c015201d03008954500d28041c480110b004810102500c2d0b5048006010440c0501410002004680089400b06400ea0750003400300c1256 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 885667760 1250 885666510 885666539
    0x206160f0f1b0614060f0118032d030f030b0f09010302090604140a0209010207062c010c060f2c070506071e050d02062d0a0f0903020c04060f03030504 66
    0x4500800149400d08000707543c910407052a2100e1211403202c0f418000b043c080d0807021410414107000e0603840c420303606401e45541904881c2d10160b0000c001400c1c488500e0f10700206142100000d40101c0c0d40c20425030420a10044030f046594100811406402000540d80031ba40103d40c000484500610140c01c0c281c2c1d1850340700c900608045420101c0411810020b513045407424040c80e80454454107560741032294034000c0030685881040140390925500c8203030140180f9402d141c4441901c400d6903402107000b0380344c640e00b00b08200a6902460700039800340404030703a4a00212383c54521610010021051220149030f90700c02170556505200510003154058841958100d50410301c0e541e00300c1d00710700031a030450700c6a0040c19204d0b45001c40a4500b43d400781070411203800c4405440180c0346d500668544507400000500f41c80d0701d80120032801001d4211000e141541030180c01d006060300020b007221024410f580411003a5901d104d215000009400002c1c00100200400c01081020107200b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 885669010 1250 885667760 885667787
    0xd0914040906062c07050a02060705090d080301122d06021326010b030606100e0f0405070513050f0f060307210c020c03010501050f1306090c0206160f0f 67
    0x42d4064a035002140b0090b40000096038031111151104d80c51010321141c81e8010ba0340342880c50074000c600e80041d40b1240004c2c141c1040000c0400c1d90f49140e951550804082c640003100640d507561103591440145906103000d41d00c42c00040040013140c5002c40300b40b0541c0400d0150001c0b001d2035640d415001c0c0d0b0100b500d0241c0b08454803808102c881000703071081241e00c50074410610381c403036640e110b9003904d00d02c40c0380612903000141003000a07120084a191805c200b031404000c3c00040d03200003290840080c003015042403901081080142d0084d004014401e4051850340080f80d40700200005c0c400b0f4402c0094000705843c00000d03140c20448081d40d00700311641003108a0200542400a030307040142000c004082c0c651051003001601807240000c60003040e0300a02841d8101004640005501e01025015641d038000794040c1d01c00c280d200030044c0151440600c040d400e540c0b0029590b03030041d11a9041450190700090030207004c4c0d0f82e00000341203c0c1c6c59484045d00d18240585018820301e15 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 885670260 1250 885669010 885669023
    0x507050f0105010b071b1202210d08060a0b13090237030c0c0f150905030712090503070311010c03050f1303060f0204050306040b060d1b06020d09140409 67
    0x40d100e844020a002d0b040c040d0182130f101c02d4891105081a0340500308110030f5280342c500c4d2400500090401a03103d00029070144c87c0c4503032020b456010314a0300e0012520074241c40c025a540840955400003940c0c0c008e0404451044685e074403284503840506c541820107003801c80300e4000f00540c04280d000350114039000828452801d0b8020404542c41c00d604000c4041c00064090019400b03030184120000f552140c50071401c500c40c0341d52150030b003002c02d000180c104200820414510103041e00403a010551201c240c0c0d80350005031400030921101d51600002007101c2c40c1d000319490600203a0482101e403c00ca44400b50710b64071006640400d40084180e081150401007074411410802c004c1c90610001c0808120661850408000315a41070030007049041c0108020452554006100f5400c5504040401010303113030300c80020340602941500401c051482d1320700700c1000804c000c801c0304031061902030f034540c40c00c0c51000b201c020009008102c1e01410801000c41103007480d601200f5054070601 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 885671510 1250 885670260 885670273
    0x23040e010b0a0612060902041202370503120f0409090c09090b060a0b0c0d1214040317070c0b040f140313081002090603040f050309061810020706050901050705 70
    0x100402c0e440c101a401000c0421010509a800131405105017401480040001c5003014104a645291044001c0010b40b00ea141000140c0d45007041c52040c202c1003107528041c44109440d410150b40c1c5107032511803e80729008280001d5000c400c1760702100c4071411220707206850301e0f0820b1148402003c00740300543d13901155800c04140c602062042c3c41e10103003d200011458582042000240c040a0b08461220902400740382003607100022030f0182038901d03080c581d000c0d00704001d01038001c10b14030861001c02c110b850180010b058000141c0b0394888140c3d43c1900c45559111011340d0b40d40d20f4000010143c08c6000700103408106900d0a85041c0c41c85189024000803a0052140c5140c20200c68500505035000f0700300700c142d4007045550070040c254a029030400c107220300021981e000042c009080c484070b42081104001f07003441100d1071f5401c0100b0046c0c8402d00400c60b000340c24501a2068029040080720aa50030f00000c0c0c1c1000301c2d20a550341c00d25240100d001120503801c040011507042c42180c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 885672760 1250 885671510 885671531
    0x4030206071a06150f0c10090309031703090a0605130507060206010f080f030909090f0607030b1809100b0a1d06030622031b0f0b060a23040e01 63
    0x15001080703000c0c05481c0c403660404420300320200008010b80000d01ca11104100d1011090080c1c00f560a54607000741c80300e440c1c81c007140845041420701066007050601d459800010580c1122070142941c0c000d800c4915012401040e0a042e48020307504800b103680030a9201e000684a90065548a004901403461010603a0f07103c80c070f0320500d0780000b0056044440184500040911494000c0c1610002041642181c8140503102d104104440d801030003110000741500b4010820740f540780e101e8008803607541c6800000100200f41100b5907901c82e140045004030701c0c82c803150040f40035021810240c2594000b8440f140001c1170003440b0240c2158403200001121100c642444100084500c001011880d01000301800d101e03004085c144d146911882c40540010901c1c03003002d50701c0d81424001d4085000c1c1c841c8140c903003031603000245229031140a20042049102829000752015682c2c006055101c18110300021030050200c0c080d103072000142803651415030040b002a111b0400006075200d00c8 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 885674010 1250 885672760 885672769
    0xf04140406091d0f0a030504030b0405070b0703020f0d1d130b0a08011b0503070819110316030c081b090a0b0c16061b02060c070521010501091a15040302 67
    0x203c1c2c10107072440703a01c003500d010b03500103100d031092103102c0314054210445a6500903203203009a000143c00c1a00c060002000c10500704079210140028015854a5030201d01c1d0003981c0ea0500c041d441158001c154801c1c03640750196009014441c81c603020003c00440d001c0a11541c0ca9410803d23010494880041c1003d03074541c00404070261000c078001058015180b01022500d810340a01e50003080020010801101d82c01800b194004544803119144101840b03130403c05000c0000e0a9060001c0000500441c0c81ea007034454515100346841c00d101c1c510616506441d0100704582841c4c006039150580c410400101006202d400c500070129000103455011100c03180c0c12204a905055014110380c2484807003e03503031000244201d1900e0710396000750281040c0d2214803500d00074000c907000f0446030b00c1c00505200307441c081c2070f001e01000303800e09528905282200081400c980707194038210012a60321050300962031003d251407a00d03409501140d00f48218486401612041e0820510000c40160344 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 885675260 1250 885674010 885674021
    0x303090e130c0902070314030606070807170a03230124090e1e0a0902010509010813020d050606040c020c100e01090306090609020a06031a06090102010e300f0414040609 74
    0x802100103032201c5c2c40386000350002102d1000c0280c841002c0c020030200f5601d80b022540016030120900d5202d14192400700000c4e894030b0800100d080f008183d032003589038550302c442015840c4004402d2440128403035032074406420b000b1503c1c0410004042c6000c844082e007458a2a1903911300000010343d1664442c000d02d00030745100c2284a002c010600520411019031500050409810880060341d40d0010b881803150300301d003034140888100003a2520b901120b103030003080e0f00a4024040c00c03402c0d01e0001e48603032049400380d02c181c0c900301e0324091541c40010311890040003c0c046125007010030b0016560300e000141d0300c6040001490380440000c002e4061103004074420f81e0042503801c20cc0c0704000851a203900308070201841d05448810604015400005100c01035449aa0707560240700101e014054140713003107030148240c00c11041e1404e140c0071000307103d09190416890264030075846180b6032003001c3e0b100001c02b10078030091140c01440103034400f0304030004100040050b950704040090300d8 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 885676510 1250 885675260 885675269
    0xc0302010e060c241e0613020c011b08071704080906070c121106030705030a0510080d170601080622060e0412030b2b0c1706010911040303090e130c 65
    0x588900c4c900d4030f528031078511500121342e2416001c02c4405c488460940c100000d01480c85550300a09400c90405507a0444084110000c002e000c0d40f61126010054512062805000100100c00003800c41c2d101c0c606031808592070801c6061940c441d5210000383e43c0040e50350701d5000c03500f040100c0010f9138030075040c0c2c000d002c06a1300403100d01031424124408160a00c0346400340308200704210320301d503000c4112070f0306c100803100018a07525030360f82c032a066568a400c1000d55100b000c540003059904141c0d041462036504182c074485075035500044800090540341c10381c1082010721100c401c010425400c20700c0b01081c4500040301da68524860315890801e580c152442406580d200b6101035250084d21381380c040c1500d080700d42504180c1e44500e44200080310b030400c01b41d0221082c3c03c02034105116001082c080c4800144401da4586464403408288603200c0e00d00c0c80d2541c41e9030030f1403c42040e2401c407a0140c448101461411100d220b00e007a0041c440e12010740e410540c200090b031456150740280 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 885677760 1250 885676510 885676543
    0x90a03050708060a050c0909151002032d030f0703090c1205060702010b13090215131e0e0a020a0c0b010b03011e0b0a11070f0b070209070c0c0302010e060c 68
    0x11490a40340e6410543c020f401c502c141801d080c100a144050402110140002502c41e480c8550b6014030b400403034020564100d42c0a84203039400888a41c3c0000a01040708000c1b0240008024400f403451004945c0540190880000d03c0003e22002c0700c209e01c580c1c002007138107011510001301d50792141d0340c0c0c032141c21010a0079500030914050041c108034582c0d00549500080018100c070000007401140c003260ba442046403a4a9010110748907074803071410060404645a49275010803800340312040450040c043e0b1a20b000843d040304a004121010840d03680140304040ca496204e460006584980540800d01c2038040398003002074008c200c50f6009001084001b40c41e541081000400101080041400141204030a1001d182e0079011552a02d0140c203103109469413659085084c5a42603002002d01da490150014440c2800c03401010040d1080b65000d2899441c4541503608110300d800141441d20081400d00065004511203000c41c4001020f150511200c0302c01540381ca0042c0080a042 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 885679010 1250 885677760 885677773
    0xa0602070218071d121c02010e0303010e011a0f160f050a031e020a05060c0a090e01080d030f0c050d090602041710110403080a0e04110705010e1006140f06090a0305 72
    0x30080c100d003006407501c08640b1202c14140c45c142c0d49990307484841c0022031410000080b0201c00d03000b54052060b00d0617210680b522580e4400407928854024821030032241280f40070f061602e82d080044840c1920320780007460500700c0010080c0d14201400c8411900401603950340004542c0030402c10310b0291096032010f0b502c82c20060f001d00329016000011080d54808400b0900080021401a41c000c42801c0c0540d1100c04000f001c0310f00c00082e03840700d002030610500200b42e9807400709580501040f01c0e18280b140c00211224201280c5036401c900780081c40070701078420303411039541100c00300300e00440703025007010b072228046110140c030b50708840e8095024402d81010354809014a01c0100d40e03511400b801c20f41b03980c071460198400c4a0340d1100300040108420400d44d1143d2000b58050300c0805410788030062032504c0c2c2d00074100100d04541521501424507284241406500c3c00e6498030404021210482414810f1200c1410b400580c001403d220020450b218420140c0046000303030000c040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 885680260 1250 885679010 885679037
    0x210f08041e0803040b04140a0302040606020601150206070f030e07081002070b01050f0607020108040c0b571e01140117060f07020c030105010609090b01020309030a060207021807 78
    0x189001c140d01401c41504184010403004210105660072207031b500e544108411000000107142040c580c100a600ca07281140200b10a81c3c000344542c1a00c4100d01452403034140c0c034401340c0e80d0700e0301113a00b040095080c0440e00c0c10540300c1d411200000d4800f82c100c0f01c4407a101d0000c80c2c144601035505200c0c10f036000c2240ba080c00716019215004240c01e840b0700c11040d05550101c0c5151141c1d041c040e040c4403189002c2000c00002c1c8951320010041c494850f80c4480e51003c0140118444c3c400801100713002620715a080c520200f000f0300c0709070741c80035501d42845d0b0301c550840c04d80b07030030301080c5440b4000d000b4001200341200c029410070408002c0000f175030704180400e8a950000680280103801c002e03c1d41501035000020b07034103030000d00f81d64900d2541c0c2e032044401c80c51f00c480d124400c1e400d03509180c00041c00c40d8002d4110410385003142405c1c002c000305407004984d00d018580b00580d244e03000404050224000385e0040c081c1038005030103000040560080401c0d00341080d58041e00048104c0c2e961390 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 885681510 1250 885680260 885680309
    0x507301407141b0409170f0714010209130515091923070f0c0b0a060302060a030903140c25150e040c0914040c1b230601210f0804 57
    0x40c40c440703003181d0400240030240c0f501005071903101c0b06c80c41e41200000b60003800508290694108951084924000391f2001082034041c0d000300ca811806020a487c0940309060305004140c894210190907084101100040284118020f810325040e14420240f01d1051580c80c02294041d0300d10140070381c0000307100c002080300c4280040920041141404600f41d9030390388650148201c0340c0000d40d0003540d4455200d00070050165501c000c3d400f000010355102c106405800a00c80709000e0b171240401030300c5070030346c2c4407180c41641070303459031074000401e0504049080d911001e41d40c5440301e000c0346c1e9151900c180c0d5800c0c00603c080040440c4407140442000d01d01401180091030705894030845091a1000803807004d06d08041036407043da221513520010350700c0340c001409950341342c1318044500283c40c00d00e00c0444c00340f100000a803090680800c42201c5000a8641c126824241c08054401520003101c1c407451803c001200c4207080f03114410041082c400181c00508040c2000e1880b030566941d801 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 885682760 1250 885681510 885681553
    0x10905162d17090f070909080f030a1d06221a04050303100504060b0901080601181805010b03040b070f05090d060b03160f06030b04090f03050730140714 67
    0x78483c50f0300103021900050b00110703804c000c4414828000c50b90400914181d50140100400480c0540c0702204000071054250055070a403010744160095940c03401000a444000481e81c0000b502d000ea035030180048030255901c5070302405040c80c000490301903007440354411410f8605841951001c002c0c031800c0d0003403001c004c000303190898040020038900059000d2500031800300d141441080c50004141e6406050603210a00c1448102ca4045c0e44624000c01c0208141e419400f5144ca89400858012440811a8060394002801803020b41e901c080c21101010b5840000e02005000e002d41900354450540c1011000d108a0004c00c0d80f040780c100741031400900046200103101e440c0c90401001440ea038040303041e03820901e001326032114104046805002c010000810584040c1114010b0651013000750003801e2040754100d00003002c50303c0074600f00d1101390003a4026509400003103001030280c051401407101c002c5006040c142c00b40c40f007022041a00c00840c025130445c803842a61080b408210307 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 885684010 1250 885682760 885682771
    0x1b131d062d031203160e15180d15061e0306020702150a050a110d091a04080a060506010e011e080403030905032733090d06090b010905162d17 62
    0x40d40300d10b0014130000322003081f004241503462600203004400c0d01420004001c25840191411000310003902e055011465640c203041d902515080020404c60b580048503012085e55020111800781551150300007903000704000c9034810360301c49034a0401c2669401400e40041d040e1965a121240c84c04c019110041c040074014140d040f00c2c400a8685170864400c4050722500b10700e41e04004103118015086202c0c9130001010f6101c2c06a0940800c00e141d0403551141d04282d9418114050400054890400541200c0046c02c1c01468407480c040c85000d40c181d00c07500900e004166907040b0384483d0708590190303468040ea007801c560348601c80068000c078026008030555034001b21105102c185010301c0d04e5048284070a010200781d01c8084980c460980344220300c0140380340995541ca01c0e10760000c01d112842114a442c144c00005510342c0301e84116445401545501103d11001c004100e901880d00c1d1008601000c1e049455000d45040344c602c0c2040750aaa1100606003000740c00a12218000805 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 885685260 1250 885684010 885684017
    0x6090207080703030b01020f0f0604051b15031b070807051e03040e0402130e10060915051017150f03061b031b131d062d03120316 57
    0x40100068000070407202c5594051400050025440f00102d0800756413540c4400703a4450141c0d10403e0030004900300e4000c42c807603c1101ca07000d90305542d5411303050b0038100b52548000000c500c04811a0b400f001543d2200040c2500064a101d140749002d840d0040340080e24001d80105180e01000410045241100c040504111541c403003007506690380d00c99401012844c1c0356a10200701152500340c04004051840c105c18805021506115692400b00c2c415001049003090760000e1281042d1203484e00c0002d0013110104001d0034103040c0710710400c1d410420010014402c00380c140900d168400310b070250f40a410381c0f5003100003890401c01802074125690f071003900b005042c003890108880c283d803110078000080e95241e40c0e4640d0310200d0121030052600c556640000c0300010400d2001c20201501e81100398400003298580306a003002c58100e5120390028910b068054801060b85080c0303000010154010003045000c2d40883c0c1070105181040150540c08030900c09400c95802000350f21400525 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 885686510 1250 885685260 885685267
    0x30317060618040e0a0f02150408030d050606090d080a300506060d05090a021c0b07080a0b06070807020108010819060b0d06092103020a0e1504030c06050d060902 71
    0x10000c0e4070380c030034180060800c0144288105103500c440c1c021040040c12501500c40907400d07030614520740307a001c400407441381a03544910034449445100351815189414000e6080c0b102228440c801402d014040a03071140043c0320040c0c20b03503112a07004181e2031151a281d40c82d405105400f522080039064240c80045020641c052640c1c03000710050b101003614030010400391100310202e0304901c641c407458540c5a00780410071030340240c00140025240e2094071640c0210050390481208081003140c0280211200d40115990510070004140c01180042c07001810300c030300e440014281d50024404880d03890740461544299a0400d10fa20300401200001d00800000180040d01c01181c8250040c0003991b00c980f43c24260310390842c91154564001d404020b103035080e00340714441002b03051007028084c0c0e40d030040120540c800d00a81c0d2241c0220348401c10140d040c00104010310925044074810705006100010100c0e4070400030500034415a19016920b015100207101994180d070008201d00e401003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 885687760 1250 885686510 885686521
    0x6090c030624092111040c0e121009060f0e0f061f0306020d1d0141070c050c06090919060b1902100b06040303181806030317 55
    0x2080140c2c00c12480005a4000030342c925415624401c1c01c0e04002c84032640c445090403814210312440b0051400f41884c038100c068840100801e0b41c4502c1d0502c00050000c08501c074803801d0940026101c425038100381d403500c6000c00791110840e5100882a11500d4595001c403051651910881900403018005400a20b260840d61665054054803e1008450281c4020011104050280065a0300240039980d5040c02601c990143c244941494804804c885000d01c281c641440b036103446811301c40c5480810790008151071f51006042d800c41c10000c2203407904c0f20803808c1c898141c40c03182c102c42e00d60440e900d5040c10130520f00000304010a019850030040d1480958a0b58601c0e40e00404030b5000854454907216030f903000c1e140c0d030361040100180101e00c2030181c43c280000000d618010f0f40c210b600075000241c0640c10350b020341103040e411100402081c00817034810030303c0101507014001d807440840d03a1040c0c8503150101d0109051030361a5940428000c0581c8640c551440c0d4035070000100050031300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 885689010 1250 885687760 885687779
    0x712140103030f230a09090b0d050601060f021204092301030812131524050906060a1b0b0f010821180402120a0608060702060f060f060a0306090c0306 66
    0x940ca00441030001901d900c44404400e80d45074402e0490507000303035441c2c3c10b1003000941521b4031400745070145801c02112104c5400d010030000e80598125000f05003903480d110040e01d603000c0e61120b410450094120341245060640c00500017800c14400c001480e882c1920000784070030700d181d02080d014000e580100701062800059403600d803521500388005440d280005241c0c07a8a03180002e04200320142004458000f0354030103191902064044030504149a010040c16013180c0078007940401c080000c85c01c02d040044c050311086600d41800040ca11a20241e000d00c041520b90840b80c002940042008444002c800e4600604c2c01000030310f0140450045031400d034403040f400f00c0120002054085202e10921030743c01e2150300240c011913035841e03508054095200201c5120b0145800c0102c005103841000404a10030690b96020b403145448001d000c6130034580140828ad4410410b9001d408166070304402440c3c2043c4a03180014840c1c5010403031303002d5455001200b01803600d01442080f1003c032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 885690260 1250 885689010 885689027
    0x31009051518071505070f050618031c0902011116081902030a0f080d0e0109020f090103031b0809060a08180718020c01061203110708190b070e0306071214010303 71
    0x21600104c03500050b00751081701c507400340c0301014104000b100c0c0c0348402e2140c04229107024020700c1ca41c3c04035840542000c070f552403054209440c1a0b500c0a1000840b08641d5485041034510503d003401c00110000f0581780b91020440d0224415070800d034041107055403c20103903100c0040d0782405040720009400113525003460a501030000040030001c1002c00114100b01c613040c1200c0c10301001501c042c3d01c04940204600c05c3c0890080c0c0007400840c1c0305150071007090741204c3d032640c3e032010410b424000c000c0f409481d840b0200c44d0804184401d100a81e00c500142085e26215642d04506240c16540070400409107101d45000307400003c01846041c00140c100c210208041d40c0140e030ba030101e080c0c03050050406510009180c3c00038443c3c2010541e00c04041540700289500f254100d50b110018545c6824400f0b010304103c480407a80f860000300d02e20901307035200e43d0b103003018410556948042410000200e400500190449601d881d05c032246115484113020106402c2c2d40030760545c4d41c040c04004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 885691510 1250 885690260 885690269
    0xa03120608010603150b090f0105130f0614010905040e0c1003020405090705210106021902030c0312041a0405060d110d06062118060b0d171201140f060903100905151807 74
    0x42010240754140c0884cd040b040301d407988610200007299950803001c203002030442040d400549400000200ca00d418003a0249031801d8601602d00b040c190410410a0003d40c20260180743e0244030001c0c06580308031040e481035086071510303562050b20a80440c11038402e040b940c00e01182c9200103018590f40054109510302c3d10140c001c1c90b00304603000003880e092425440c0c942c144581006401080600c801600458400b000c038109044621032468103540540c1c05481d4020200744810002d114803500b000114610700101c443c500345a0036110000d40d615504441c4c0890002e407001c80340115203030000558107003402404c100b0310740e003a070100d070010010070005080070f44c496104130000e0b6a0100301d0500e980e4040c052802e00c01110000c48819080070509000d00002e083c00003d1060040c4461a104500105007041c1c4404813401c00030590048990590913101c0d41c14550840044ca120f00e9500320700840041140042d6203402e42796040005098400d01e6a100b0101c001c3c135140002d900d0240c2d1b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 885692760 1250 885691510 885691519
    0x90302071403160b0901120908090907022121090c010f0e0102030913020f0c01050405061006020c041a030102040605070c060e010c060903030920041d0a03120608010603150b090f0105 80
    0x201508030040b44d100647c840072058640c580301c1c10b00f01300900a030080c091a2415101c415444d43c0ea880e050740c543c02c00e540306540d5014440c0b80c0e4000100d03e1001800d909810180d42d680041c2d08072060010300c0d1007100c00c5403060b03006000880310780d82c20a0392a010790916140c418111820030b00001d480740603142200f801407406014038075420000340c055450340d59804c18595114000d03584228040d01080c2c070165214042c9801007111010122484000d440e40f90b0000c02c2d200340c841051000800c034500f9010007041d400880130790103a6080c0010402880716a40706515114a81031602169030154000c41c24408030f20001c2e400c0d42d0300082c0f0340201c03070380001001511051508054000e4991100c00074020344030445060b5644c0f81070b5449210000d0140d404008007070203c0c600144202c030800c003004081d03101c0c4812000091050604403001d14480001040140d5030300c0c01030342500d00e590011a11044441281046ca141610a800d0b800b1411640340c440e038142480071075a41101805690b014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 885694010 1250 885692760 885692767
    0x91b0f0309010603080c071e06051b0a050706020a0b1602060402010c05030d060609090b12120d15080304060f08040f0201111e03030601030e01110901030b0d06090302071403160b 78
    0x4901d0a40c048801990014040c175030f038440085116840304040c1c00341111101050010802e21a081039200c41524981c5e03d0301071510f001e400a80026002a545a41640c031544600b070300080c009110a500600e842c0e0000c142c12645c0d4640307400d42075401050f2002c000c11003861600c4199000441541140e0203003170500d4000218206241140300b20020281e060342480c400142d9690b00c0748104049668980c1c007001046001ca0800448540540548000b031f0702a034034680720241014010401c80300741d000001101c80240c1084078018003143d0210f070107034202090030001c0c0c4c0c2c2c0105000061103858507020013a4680b42e502d81e40002c210b80c00207030402c10b05040000d4070460420640181d0803400c0b043d0110f0b00c402c014110360700c0e4000c0f81da040c00282005981030746003005016403140c8181c402d500314200529040114010f01201c8a2580d10004110118000ca40d0920900d103040d80a54003801800b170601d42170405501200601c5801381c0e00102c03622036103404200c4100113a07048544032580d03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 885695260 1250 885694010 885694021
    0x3091e15030f0423060103110607050f0c19080d0f111b0a0501051e1620010818030a0e04020408030f070b130816050a12030b091b0f03 59
    0x30800e044a00c0e119000000020721507055020140c07107200b41e2089080503000700403c0381290000b203950201c096150311010051002505644603c8504100030f0b041d03a041038040d840e0f4030700d07010002001c0d96040d003005000d1070450030843e2003681c1c80d00b1110810200d05140900301c542d102c14010114041058840000c0703a070b1842121081a0208010121103040c4002250340c80c8010031040342a104080c00c0600280c654010000d81d503500d6aa10100407440342c150b08180016030110445007a1130700750305c0700d80d0000380c48403503a0f01d210704440100f081c000401d840094a582006406252100707003290a2140c401000000c54404410720703e02124141c03030110102d00039028540002030107002c0881c907000680c00c00406008c1c558042c56401c4007035240c140005090001c840006800b0000420640c18040c46d68020b50f5030320362080b421514040841d88a18012000c0f052030b00001a84900a0b403483e45807600701240c00020031480e410b02c582d19082c20104620900d54080720b4080c01100080 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 885696510 1250 885695260 885695269
    0xc0304080f22060809010c03111e1620090103080a03020d0908030a200a020d1110020f070203060a1109010f0c080708031b040f050616020d061b0203091e 67
    0x4600100824004035080d101d0b00054403542049941031701c070758a0f002030201814801c0c0078207014441c0c541c07070703440c07a051421008901842150541048210b006c02008804031207485d440c1001074090403904d1010300c551524100c071398036401400c901c203003030b0b0754014008500b030341007220440703a014103005035240843c19500b0090890698003030000308001c000c02c00c0e20180394010589800300c0c0076200c0b486012481c0c00c0e00300303030184403503c00c0140d01003020f01003818080e0005044406822045400302d003041460707001a030b800340038546440c100108900d411410104a096080032004100b441450850060f501c210b0042c00002810058240c038009034260048040c3c402c07158205409558500303007410b01c40a00c0c0c1c010b540614000351240001c0d818001041c00b6a0107941c2540c00d2a07100501c1d0900704401604040f90041484d030310b8100e4000160392701c94500022504c151004141c54031107807010784800030b00c8070415007550010010001c4550304d20722501c00e03c11490082001c20040000402e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 885697760 1250 885696510 885696547
    0x1030f0e0604080a030f0603081e0c030c030405010311030f0c0a050f070f0b0903070c0306020306060c19120c0f020409080f040e040b060d030f0e0f030109080904050c0304080f 77
    0x401035026103800d010a20404900414225070390b07403424410503600c803481800300c44680c84040c00280d01401b8045c0950b03190704500c0c40c071685016100c2e00b41890305000ea400c6078040b806d240001d901c0010308000c40d50701401010b819034582281a03003140750101c44102c0e40c040003040100c1c800300028409100901520640f1b9000341100d50007501c0740094038050302000c403820015130300388188100003908040000110b43e9596407025141c1c1e850740c55641e552002c0d40002d400a50b0003d8103115202c80d0070740130001100354040c41160141036405e182002421810785140010800424416a42c081383c80c0d00582d104c042d5042d640000d0201250500405900615081e04117618000400181030317000c91b845207015a0041203d0121501c52604100060807020802404105080c6030800002d000f01802203007000013030f003103c0c800114140000e0071203005407001c91300e0950100e17250100c0c2c03c1510800341d1010644a0b0340d8550304190b10b400303010f800754111700c5015072400241002c420141e0b9085 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 885699010 1250 885697760 885697781
    0x10090203030c2e0504020607122307120212040b0906070b040807060c1701050907200f010b0a08031603170109020d0c0206010e01150c05061f0905070e01030f 69
    0x103a4070340d0b2900c0f5102210304050480301d01c100d1480040810092512445124007a513401042d5900d4280300d581d030503168001808100050100d4486032038543c0680c0c421180241a04d5003030144d8036401481d0060030081d000340e039501154010f00c440207403031034980201c2c2d040c0d0f031508030303074a880f990080c00040349441000c500910401810f428802000b00300e00c06071511500c2220300340300c1107001c96011a5001d50b002c44600f03142280800410842c200042003c0e04880c0b503282c80c100b00c00d082c482d50f07000d60308058641c03262640405001d80140a082c418580110001c580b102c00b05450b080c1015070b64095503e512110200d8074085070109805014a03000b140721402c80846d4541c1e407000d10300006c2d009191800744640c2006841400070b031021a0190503141e00f80741cbc107031940c1d0074510070420300381c007029211080c007812241103030218101700a02449402210600135602d0300d54500030080320780315070240030310758207050038800180e400c0340c59803d848201b1300c0c00250311080e0324880b20184c800e1400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 885700260 1250 885699010 885699013
    0x160e180f0d05130b0a0c02040f0b10090815010807031209032f040b092814150a03080904020d182d0c0909022407121110090203030c 58
    0x1480004a0b030084007404102e48140101c201903681c0700001251071085100351000180481c440c40014501903000b940c000040302400079481e101c21020400b1030082060303040100e58511010003140c03004000031040c090745100145001c4d45801043c6d0303a5003056002c000c11840c2c0074986041d10b2841017203204000c40d00702814031309030100e003006481981001c2c002814641000301103000d55003450700030348040342c002070701004507981d071013603445904410166503030705240766010b6081420810703000d52070080300c41c507814950307d08014410484104115170241d00a280074002000071800b010181d4204a00c16940540d6440c0d41d00721407001072a004010040716201e10f2160007d00c001d00c0f1050b50441000002c4c0c426142421400c86170314604240020000c3d44c00000500a403400354000710b0025202820384811900300f8207080f9030141800030096126040420200e0034010792110300c0ca240c40076800d064000640000205443c0c29080f2407603c081d81d1940014021901c0401c00c440e88514007a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 885701510 1250 885700260 885700273
    0xb030601060801030314190c060b06070501050a060911180d06110c070f05150f07020d050d03050f040f030813061e0b090105181f06030c02160e180f 65
    0x10007400c002002e01003500007441d00d40180104503807080845e480d0b410300d002600d107c1803516004542c2090300500440390913444251403079403512410040c01d10315228030000300f80351600b419000c085030400d03030080d8001c60070001c07000c01e64031002040791505891100380091813035026021078803494090300c00400d11403030002151002d04604006e0000c031486982641c042039031340c84001038118080d0203404d901070740c248804d0303803006141c4005046010200080d10f0a20581c1d03000901001c0c8104820754560300020201b21000754907208a650006941c0c800c0d070340c581403944641c0c80d45014507400500b84540748010480d045458044400c489501400c01c2c01820f04203c01c800c0381101c204120900701d0300301041c07000715103045d000f03a905840e000b030310800c000100743d0004c1000f0b4a020340f0070b1220000030f8400d5140c40c0d03140f52a40c0c02810f820307140880c259281070b9000703162803000c0103110582c61504d20144000c04514643c16040004001c0100d10f040c40c2071200c17800c001a120064420f8403959 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 885702760 1250 885701510 885701519
    0x1009031425060207021e10120e0304091506030603050a0212011503060c02070501090e1501111b12151b040905010e010f080f06040303110702060d1506020307081c0b030601 75
    0x2074000306500d52003074500f01c8070301c00c641b01d420460044420246074010880590b6200241c4118a05060510300030b401203a00d01c2d0100d041d50469000e03801003a04545c85882c1c0f504480c41d82016000204091b02d030810444d480d5031169615980c403c980244560f050800440e00d0f00025000325078410614609042034079602c0c5031190080800728040e101500401d03070005101e6008214220840c0d900e0080d100d110382d0b0700c0c21010003c2c440582c07001c0c1030000211341c03642c4440b4100480003d64803000c42012991011004220f075400401c0c2011035a60300c00011100080e03604a40c1d56000728010052040c0030710040d500c0a0140195005a00c0d981e00e050000160049540c00c5541268602d508400300076440d24026904c03840c1420311420b481c0c1c0803801040c0001d00c280d000c1074420541011680c03c105141d40015941c4d804091a074030400e841d080c007054020380f0000703060010700c1940000c51901c00745540302c1c0c40768025100030b1440c414000c80d450f514010b0580004120103402410385080b0742c0c44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 885704010 1250 885702760 885702773
    0x2706011803061125210207050f120307050606010207140f13060902070f060506191707090e0f0d02060603100203040c030c0605030f1e01030803190c02010e1009031425 73
    0x1036036003d4822420075614051494203100340306017a01c5056000c0e02d101c604000c01d0140600c1c2c030081d000c1d0440b03001903030303990300340c0052019005481c4984068210360500c41c00080c034013551340c0c20058411706962840803082e0f031100c543d441007503001d4a002c8030307080034010034200408141e800618030600004020040080c60b841d5017100c68810502080381c3c2c1c9541090010075800301c0008461050100014010100300414402140d0b07a108200c6400948a0244200f80c8070aa03c00c6401940407010642ea01a010b0051000450886c4001c2c895483d009001030b5a41840c1240131105d50b0b400400f06040c00b80c80c508507800755030081041009260f030303404001c003075500840b0204200b500c6035010508030780e07020016203e40010390302103503566400d40d10f030031081e94005054000342581c1a4962000d02419000382e601c03801543d000002d2101c900382c00e140c10840f917005d01d80f0341c043c5050041d20000342c212654121524a4649a0351a480300c0c101008400c45208548240c00c2c101c4003944081000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 885705260 1250 885704010 885704077
    0x330c0a0303150e042a0f03031b030f03150e070c1703090715110105101505030108250807140f0d030c02010e0103090227060118030611 59
    0x403a5804100601d900c400024102c0c0441c0a41c140111000001c100407a41d040200c403a01c0200c040c2c0c07440340d5260f60110040b01a040c2d807040c0700031580c0160804c145908440f1100ca0f60100c40d214450242a50740c0042030400c9a2140170300703255948001e0001a000b0076101d5002d042402c12a80e1a402c1061003c1c1c0451a503800071540e20b0054400b40e076654984c101600e02030744440004101035802c14400c50316800c4414520000c012800c2c00d4425042ea0134007510f8080c0c491440103045a50400c1c1400d500d101510101c01c1c00c0c404c040004110307000b00020100301c500049800c4840e40e0035880082254074001d0303480b0800920031410013259560340d1000401890500710707920340c465400c07001030252842000b030029001c50104800980554010001c040c1030740014540000d00300020790006640b581051b0140d0542042100b261303601c092100b0003143c1202e000d0030080d0a810480b403594590301707107501000f40050b4851b6800e00d100d00403c0c040d1076018010114101940e118902842c65621 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 885706510 1250 885705260 885705263
    0x705150906090f07090207060b0607061a10021203070903140d121103060d05011b0315080a02031f060e070203070203010623150c03070b01061409330c0a 67
    0xa21400b0804510700040d64603828070024000d4007180303281c0101c1900075000504145d416540705c1c001400190780300001000d2042c8039040010b0205c80c12601014806940d18815006141d02161110780b10340005072524055501c3c0c009a96035070318a034040302e0030941a07000504141506a40004181020032034500000455451201040c404081101070f21118210a032122400304082015814072007031000b5000e000c1d10000c55030500b500401c50f0075400140c8000c00003036403001040041c0f900c03c8404401407003010010302c003179130850300003035143c101058510107501c400140c060f80408040d00f01d80001d001d0000c48044030700d018503007c1d480c1d1f40501d4040b03209510303303400031544021041030410002c0c0343d11b5a5560014003030040c40720800d040c5580b0702c070506040c48051540082000204000e5214a90324142c0c1d52401e9405021103101e00c08010200809115000751a00c0e07081401030895603000b04110b0080c80c0380c11038161040e003512503561400c030010b07031500219000942d804549 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 885707760 1250 885706510 885706513
    0x30e03042105011419061a07051c090f0806062d03070b120f011a070206070606090905060a0509151e070306080c12030a0c0503040e0a06090e031206011407051509 71
    0x360b0026414011036410b030240c00c807584031010703460a030301f40054041d01c3c407503129504035019401042000c0681700560351030103000681540e020310501006070b000074002c1c5400c1c0c00a01d03242c1030080c0040c0e400858070124000e082400070b141c00c070b0309412031180414000007900390742c4e80c1e68840079074101540c00b0710a4048101d01d0040132a0107011102c2034181224060195549030319001c1400340c1c8941e02c400400c2c4e80c0847c0a004000200b00c10b80f01c0c100041008080010389800280fa00a052000080c94180c0082c50403042103e19040410005115509049003551130b503600c041800048200040d048620660740c4200f122854065000409031090541200d88204200d03041141d41003514902407002d400a00000103002d024440c0d0420f25441242500c1c10f00f500d87c050203e2078041110240086034890b45c0c200662040b6114024800002c0d00203185020038002a000a500004e00f0312810051185d4003200340c03001200c107a6160310f51082c00d9940304524580070411310070003503804011030f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 885709010 1250 885707760 885707791
    0x7080403080a1d09040b0411060d020d090c0503030c060606070f0501050f040506060f06092110060e060a14090910091a0c0a020a060b010315081b01030e030421050114 73
    0x4c0c9003444001d880790741c2c0400c0c081100d541c0c0369113104030305030071125454110406000e82040c922240c0040e12004200d4880003445000e6424040b403454040d92225000350010031000360f04000c082807255100c1d9081e40c68590341c61980ca0f03c00d001d0403080c4c2c5c0150503940790000b0300554000070170090b8081d50049080b01d01039202d43c41002510102c00310700369070100b000c00c0120700c5410000b01c0c2030090701c00400b8448041e203200c440302c0d0070505103408940140d5904c110501816100c1e400c45500034005403000790500b81090024031380d02d0b103203401044c0f0a443c100b00290010794204684c00001089034024054030102e0b01c1c000c051f81a2a41010b0300c5442c10200240425090f1002d45030118a1a0b0041405038015100d000c01810040d80160405840300d440030013414103043c80c04020a880340080030425620b41d83c0c014010284109241010305040a00d60100b10000c1610140c03040c5000c0c0036141217000181500040035018020105c3d401c00a005d24000e98444c4124800c5140c1010780c1503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 885710260 1250 885709010 885709067
    0x1c0507030f0e0c090a091226010501050307050903010f0c030b130203070f0503040c080706050406120902030309102d11030310090c051b03030108010606090b030105010507080403080a 80
    0x941e10011941190b40c0d10602d020001844c009044542000f1950000510030481c0d45502c401d2940c01e12176003010510342000c00d45840802c6244504403100b88242140c1c1d5414200001c00324400a000482006000b2805c00304565080d48440d540c0c0c4500e1104004182c1c6920014000e095000305861081d100b540d0390a402100900807070b442004259201d442c001071804043e40e481e00003802c291407100c882440803c10074010070015000d08026107e41c1c0d201ca05d000d070000c11442c2079000c040c510606100d04000140c03800015140c006000715000c00300064403200440c0c12120030074401a00c000001c541c1a091017060101c01d4480241c0e5560b106c4000c0221a100c0e600d1100341c40510f0854501c080c100300b42c250075440785030001010301d4002c0c40e003e002c000c003104940180711041d10300d810020040000b40024800c080040c9114185a10460302d8008000302a010505c03a83e41800310006665081159200884019603031002c0c5880e159010420700904511190040c05078502c0844410324 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 885711510 1250 885710260 885710291
    0xf071a070f0807060906050a05012310030f0911040b0a1d070507050a0c060e0a03020901090b010201110408030a030507030219200106270606090b0f1c050703 69
    0x112910044004203141114503503500c030628449a1054400300b6090100f0750010f4490300454130014042c1e1400f01d401c0c100307400c2d40011503c040c0e000050050000000a14508112111440045080311000c800c444158002e4000e0000c6258036110310380340183c0312041280c0019601101c010a03074040000044100900c9031030380c1680156160544030550f400c0e03136940101889a400b0710702d40361842c01d00d0780d81d58901d0310742041e805045a0b03040d80300b441406103581c000c08500d8000c0040350a029141c0c41c0d40c011980019041c060b0902c604e881d803070751000b564002d4108081002c200500c0782d071346076501c02c14962281c02451581c0002418140802e070711500c203009031002c0e01400030582400b0003240200b65100482c0f500700c04110b907071004110114440a100b050f000b0700d400d080303040305400f89401c641080c0036900c43c94154246401c00a002c8154000c151106032509451480d036a0303540364030010340074003400c2038017504410080725200d510340c03840c0c11050294640b0f4406008882c00f501010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 885712760 1250 885711510 885711539
    0x21090510092904120606050904030818010501060c11030114090d030f020403150c0201060513060602010605030f06130c0308030435030c0a1403150310020c0a03050d021b0f07 76
    0x182d0807641d00744424040b0055101e801603409100b0200050030695680200e03031001e03c100d50a60201d65804100710501003c60482c00d9000c0f403d0000f00300729810481c0107491014058000b629007c0d610b5401d502c0c1c0e8a09501c11080d112001d00969002d20301050046c1d541c011240c1400002030810000302402d0b4418000c1c1ea080e20b50028482c280803041c2034000c40209a0007040700110740d2101d0300001c140c2c8980072405e056001580c0301144c15814040043d0039101c50b548100d0203a400300207600c040d03c03c042000c81e0012281900c03045003d00300d007400340c40b1b01c0542d00003a00d403183c000b007440200300302d88070300c0407440c013500710a0a102c01c03007150740401107041e440d2820b98100003003000410380c0f60024000e042e03000c01405c00c002d00602008044002e600102e640708258111714a0760a801d203000c015a01002185031415031421015284a81d1916190000107040c840c0200e141d03080010f0ba070301600c86072408006810500862001040d558601090b40032916005040b80821201046160ba = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 885714010 1250 885712760 885712829
    0x151008060d03030519060303020705010f09030b1f0e0a020a0906020f100b01110a0615050d17070f020306100501080903340804080a0309122109051009 66
    0x40c0800741c0640c0302500604001003203084c07009191035803281107405510440c0095070080e4024001e4605003030000d403c51100e01d00a00500448840c10000108041c000540c13000c01c5030744100c100c6211042d24050403507a9044890516428401c104035039841c0d42c09000f80000580c0c80c66110b503602c090682cbc40d02c01941c242c09882e0000c141516042c40d1680286421040615040424076410008a424807060500403642ea6448080b00c07480ca51203850030b10040c0a0840e040b40710342409603545648139040c00c1413141d10240c041680c600b03001014903541c00d0240c001d4291394183c07a0500001041b08402d005080c042070308035010071184800041900c44070360780c00c48d5602c260380c0920000165504000882d001c4804000301800006469201a100500c03031000140351808051034050030004498011402e05054100d051000c00c0d075001141c02c0c208001090034010944218040b20f0403691130b0041c42d00200030b100350200300c036809165002111001d81d640441d00c0074000b8074a141101000c2c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 885715260 1250 885714010 885714019
    0x405090a1521060b09090d030c0212031e090303160c05030c0102071b12030c02010c1a01060203120a0203040c0308030c04030519060c0903050709090c050915100806 72
    0x40c00c104030a6000e80c00d0340c1c481c07100030100309603035406004a00041a0b6505890809079801c0c008222413801a140c16440880d03134a0340074a01300440564640700d20000c181015101ea948281c6240244405804201c40650b802d07036914040707036610220607180c2d00c0e040c18203a000380011220400402940e01448400d80b080c0d1074580c07460012107412080d003000b6981800104814000c0c6402440205200752040040e001c1c40802004811031104603a8002036518040030420f2001a0f84070b1903901c161a424208110300301c0c554200944034001036809040251100800415010340000152041d11844c0081c0d40c4d0ae80d4901c4030840581c0003d0300d0041100c03640800610002d85140c0c0a1a0301654501170241016030f02d0700c0d03080c90100c4040d04403c0407900c4841d008140141c078020f51030790f0780c0c003814507e64452441d6100c5569102070310408140c80e6690f0304e810100a02c40f50a03c1c0140300003440081c00d400d000c05040300380280701c15528450340c912000000c51074054001c07203110340030007003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 885716510 1250 885715260 885715279
    0x706170601031a101707030b01180302150c0307020d0302030301140a05030a020f0d0503030123060c0607050c100f02040e0f04030203030411040615180801020c19020105070503041d07050405 83
    0x2001d04c0b840030340b415040000d01c4943d820300256109400c20b04e500c60302480d5804150406164005081c6403000388008405400c0c07020280301686030002c02c251950911014030780d4940000709680d081d8000c0c10340096102c1520200c138800e041d8000095410b0704d60100400010680480410010450fa4422150160016066407015260030b88001000c4003024005903c0800750350348503400c42d4026000843c12400d42c4600c00112684201c1980b10454156200c80c07a000411921700c0e0348180080010b000c2100010345c05903103d005000d00c000740840000240030f016000500300c80650441e0184420174000c4400013880c481c2c0000005001c6c68141d000b444c519103075600e511011240070444543c000e91103100000b00d1426104002036108a070741e66100460314200c00310507402d110b41d486440182e005004020380c031000490050342240f0700440b00814031030a803006880c41c0c0140c00c0c01401c2400041400210071010312203170568108ac00031001c01c0f50755480400c0c0d40c940107038003a45800080c0003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 885717760 1250 885716510 885716561
    0x2060f1f05042706140c090603060409170f091014190c0b0a1b09082d03040b04031505130204020903160b0d15060c02090a0b03070617060103 62
    0x582c061400f5101c1031041c04240d1a800c0c0e22000c003e0150101198a03980d900702e104850456070040503004505008064501840c000000e100c90201614840c45070b903490710b80900300304800f010405040300840c100c0d500d80e180c0004050480c0c1100a90710301400d061007500c245184502d5102c540a421000c40070304200041c45d014085414001500050050115400000c600d02482e818440c030384881000c601c103c2c040c1c00c580d0b10381083d09444002d101010106124120010a1540b41d511044041062201c0d00e5400aa00c10908004446040c080010003081c1c4107111001002503c0c00791550707200ca4940a00801c2c1203802c00c85d641c0a14681600307541e0018681500182410040181210380d031001c88a00d02079050117940c88081d8450380054100c040c0c8131180104030f03545040314a046040c034034100c0302174505019202c0082c070444004001804008182e402021010b0025007100e07051500d424014003180b0b40589001c07528100ca41c000b60856109000307880080c6000300c40c80c2030201d0103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 885719010 1250 885717760 885717769
    0xe07080303040b180c041a011205160f0314010602010b1f0f0c0224041805130b04050f15040c17070b0a0e03060415060b030f160309020d0302060f1f05 66
    0x204c85003203c0f0307401004a400c03140d50b039034040d22009151100070044c03a85100300001d44a45017402182d4030340d6040804001c1c1075000d007208022420405c0c140615180d400d401d080303004008402c0400ca40f07501c3c0d1000403602c03640c1548070448541d0140e0b02482c01401074130302030000c1c405411a410000362030364213010030b1621a620710803059101800040c002e295045a00716914441d8103000210103000c60200500a0400003001c00c03e00403040030003050070242c01a4441c0c0144040181804903810003213810000704000745a4007a90403802d8803042040c1d0341a001a00700240c5042c1c03007080300c8410200e40c108010041c00384141152009042d49490404a0b01158000e84e450341b0030b00501c00d5418001d9107050003980e1241e845141c009080e8400713540b0107811203101390440156108103000700828011007549140d002000d900d402c1c4c20031941042e04901034100c1500080d00f0110700582e100c209a00000c03074500951b44110398040c0b550b41c040c0170ba0446ccd059200714040c0e00131550020010b5050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 885720260 1250 885719010 885719041
    0x50f090a0f030c0c08011d010522200d060e0d1125170f1c080403350604050a0e0a020409110402130f0b040e04061a03100e07080303040b 60
    0x482e04e0040314041e03864940c142110ba00ba404013100d0f0b0310840b038045d10007000f232058550001090900c10881c42d028a42441c0d01c6c044440020f1030540000301c2c90054200d03041c2e00d8030a03440018618051032241c2c0c03a00c0d10140c17000002140c0d040c1700303480f0280c80e003502410507108125002d50041c00301000d4a100c080c060000002c007003844440340c40c000b080c0c2da55020001c4a0440c0f000340104400c10707290107501e10789200d080011015014050b114410305a03c50303101030300150903242c0320701a40c481c250341004150041508066252404200110749406075041c0c0e40f107804215401c10141da111000c01e01502d4110100c014141c10900c0e44000500e400c2d400280707058010204103020303510b018041000c03644446121503410100507010801c4507502c0c004030015200c1c5094450606203003082d05800001c0241c0003c241755190400380d251086160040110124000e04a0306c14210040500d0b004000c0303d071002d1254040d803040071030350800c0002141d00a6a0040d0108182c1e03440000e0681081c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 885721510 1250 885720260 885720263
    0x5040203060907030b0d0210230c03040e040c210b10031115040f0e090d0e090c0901020120090a05150306010806030a1a160309021003020c03070f0501050f090a0f030c 73
    0x10301c0c0d01851805030315000859a211101c5494286080c0c0c00e900126101e000c427009569402d000800081c10404804820f5a08544154103803107942d4613149001c0c80c030039041d034201c030320300703d981c2141d0040c100640c40c032201510f40500d19200c170300d40b1399503a49005101103001c094444543e14071503100506041030682030302e40400750280e08182d01c0701c4021070381c0c1d0320310b600c00d4144040010522180c442c00b4410b0420f080d2250a11400d50701d04070000c00d15034000240718124100c0c0200c2d5442d8181d000390001880c00b164024480c00765007820309034178a04c0c0c005400082c024007501310045031508290f0540a01210341c2da1030103045a803050011100a179005240c0754050042840c080005102c15500c0c41640c90040d968025600d02501c02c010008864600728041600740001d010140c0c45100c0700741540303000f038a801350392550700c0600c452943c0b0981c3d5000b00100315400100c0c0070f10006600031409040d400d41000c1898407403140b0940c2ea50101c05c0302030120380c420305111001a028041c0201ca05 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 885722760 1250 885721510 885721519
    0x3050606090d11041116022d1c0605102303060a050a060302120105160e0105120a180807060c0e0a0b0904060b0a0c0c05031f1a0402040303050c010605040203060907030b 74
    0x40803204009510b64003c0690000c50014881100c003c600d0300c44848040101804c8030f03008400039940088105100b008640c0e070041e50318489e1440b03540d010f0201629100e41029080c07002e4108030600d80301c020106e11410341c0b8900514030300b80e006003e0900081c1d54410003402070860b42c58002002008042c0038207040811381c0e40744000401605e840303541110240407400001b480c2c0c544400300c40304100c5041d180e4410007125481c184d0145c0c0c1c004040d0303190b0800009141800c2d82c0c1d10081c900c0100003004803200000c018014060030007140c20024039a41c3e2140906015050003e28240c0b111008018015401015004180107500108000d403c400e0802030001c1501d0782d42e240040090f500810103880080e00709a5050144000511600000c050640c01000e01240700d42000300b81018107010b4000e150740714040e081d07200440c1811641c01031001031046554a50f00d01c1c015100d94030407640042d26500b00f00740000c8030300d0a80b0a03240b090340c0c050030510207980c2d40c0c03900724024680f025020741e01 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 885724010 1250 885722760 885722771
    0xa170c070f080307030e0115060f0e120c1806060415031407080916030203031b0a0507081510030203120a121e240306110c010f050703050606090d1104 66
    0x4034800e0000d45440724002c0265580c0c1c0d090011000b82560501140855285e05041c604c598151000d10a681102c40e64035001c0440040c0c540203c030a002181c820b16844410240070400e000808507442c00800c03c2203c201d02d52100000100341201400ca520b01d5001d282400100030340c9505c0c00c3c008080500c24540000c0f20b414201c0d032194040700903201080045e00180400011000401103480c00d11030903041803400754a10350003c0e41e0b034407410b4044c4284400002d03503210120b8081201002003030384101940d02d13058030b48480325658072160b505501944045800b040c10000c001003680182d0790058094a15950490403d055950042921008004540002002d12102da101d40d10030511282d01d0b241e000c480c0042400d0554032480048100320295801100198155051090850b40e01943c080740c00342480c12481554082c1c00c2a40c030f0194200300c0400500d030b1141e0710007441408603403030801141c0c403040207000c06801000e0a90b6002602004644042004051968140c4400134004210b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 885725260 1250 885724010 885724013
    0xd031106070201060f05090f0a1508120a02010b010c0323040e090106080f0d09170715170711150a0609141e0603120c1009030c050c060a170c07 63
    0x60000d0031900880180d541e60000e00c400b814014401c402001c040b252894141440f002c03203021504007405007005181c3c3c552400c2d030401011030b22040140400020380351500304014024100d50711035401440154603100680c1015801600c0441c00c5507019a40c012280444400c0910306181700c48149114071018000010240c0f0518074403845607058400120700140740580b01d03480e008003803c2003c01030304461302141c0003c1c0d0080f621012590710750000140036052910181c01c1403007070340003800101a11074014031748036000303000a8041340443d1001d07802a40c900c1402c4880b104100b403070790483d4109814842d903501801880b05d41051949500180c625625007881d000c031141c0700822103610140e0420810b0101007142c1007105d01101030513079030840c42d014001030380310b032507801c0c000c1c2d010f4001140940ba04203041286420f078005908080150352001c0c11b015040500c8018100c44511032009410281d0600105854448249880d02c43c00c4113182e114180300e4200041481584681c180b1800c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 885726510 1250 885725260 885725263
    0xa030903090e090f1b0d03030908090d08030103050c01050f0a08280f0509061003030507030c02061b1b0913050c06030403030e060a020f04033005250c050d0311 70
    0x240500b40c801c0080c000f030304118580508042c00528840b85205c031016402c441c2d51605404200030940c18034001400d0400c0e480e00402502811498641090700c103032111080107400303001141078034000d8003281c0400c0b010700d0044805200300059084d5040c0c050000c140075600840711701d5004440030700400d2640b05164200d400620750104c2485069840310403440c072002d9980f1429410515010151510f80303410b0007800c41c0c0000b039100041c100100021684141841240c0050009600030f06155440b00b0f51015203010716100080300340240210301e02c00e0601c0c00b9001340e208e01c01070050403140d010b548600c03020b461a480c103102501c0501a0100100607641d400000b1445a880b0381c50005206003081c4007a442c0040040401080903c10080b00c141da100075000d44046940c040200031401148041038450765031740300843c0c40342951101800c0c1409400001401040b40ca6420300f40101209412050034200340070006814103003610030070302250a0000007002e0040c020b007880380d220b008034040715 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 885727760 1250 885726510 885726539
    0x250b071505040308060f18070f0216031101080106050711060903010605120d0818060a0b0103090204140a151a03040f0b090c0f0d03050315121014090a080a03090309 72
    0x40700069021004c010840c6032a909100250005861f401c004885902a03402c15200103484401072245901da4100b440b482004662849090307007c1e0340072807e50301d02c0c1500c6080a16080d05020404100c00070480c248500181c612440d0020300b1200c441e204c12040c4080e40c0d01000a158065480e2180440d080d100c9540308109584110020506121680e0000340b000c2005401000b611070006c0c2410340d4854006030b440e401c010a20000542e03610110016030052503003001c02500103050210250000c1030125449105d070050050034048001a462200e80d4004a17010302d58800d00c0c03d9030310039140200b06000d1903100703200702a04d254901c00b548a10041d4501250401b034140e002d481c003c840e074206017040341070b010700c155903003050400d00d6038025150340001008120340300403000c80400b241c0e5440e12881c8202c16810155014241d1354892040a00030780c00c00e018071b500c50040850211b480c000340007003c1e030781c020704880c1c02d0040c00007044001d1300004400b0381c20412400004514030712000080c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 885729010 1250 885727760 885727763
    0x809031b0709061707080607022802091e0a11120901020915030a0b090420210705120309030601030b0a020d060605030919050706120617060702250b07150504 69
    0x40310100c0303413801c00d14098070341e0800801030304000700b80305c145d41d000030f0421210065804420201916644803018002c01003201a600030b1544041c4178103540104258501c44c0c120010b961110b94035911302070191406c0100295940d83e0801902140c01004000150040104000036203001d8079400015461000c03032103d170204a200009100c10500303244600c0e019943d040c0c07080d081d5860145c986200c00d2241c0708645050090100b4020016520f028102c070040c0d00c01060f140031000c0202029583e66458014039000302d06640c0d1615021000000b07031141c800004009000700d030309690f038514a054000c1c201171702e0541c00340304801d20b500e02409208040c04266039044e07224074010803d5440c06882903000180c0160710503110002c9200803d100c1c0a4405504280201c0c40300c074003c1c10001e1401d41e02005034600a082c00d035511b0f030400318115000e030045a08403103030a01c2001d20301c10803d5994060880014600d98101704902002c0041d140c014040d5103107940f41d020102560082e41c508a40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 885730260 1250 885729010 885729029
    0x303020409051005011b170903150f150d020907030e190b0708180a02040b1329190e0c09091509010801150302120a0f031e0809031b070906 61
    0x1307002c5075138844654188001340310b07003890402500f0307280c1c1d040c40e9100c0c000c52880142e00160824103628100215000301446c1141019603285c45021500310382001d482d030700a64640242c100301249002a03a503c80b00b034008001903503a882d40b00041c0c009000c100d07142500c41c05601c1e0b01d0060214020a25a180d81c0034600e4952946003021000309008801080b0301d07100404c5c8102c803140c626000a48200490f816640056012001030004d10200c00300c0392a2403442e810081006084111089040345003c2c810013088019820310382004455050001004844014000304120300c0000c5080250418000f42b8200d146c80c1d000c0d00428103440781200c0c5020380f480e4641c591400b9041c42d614031801041503200030066518201010480515940700181c03103405640c11071480c00000b071068000083d0300850303040d00b1121924000d8000c01000c1c00304218685a291141c440034040e19107184180f0441c0d0255252405c206403407600d511010040600900c21008042555081c034416140a0103801d01d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 885731510 1250 885730260 885730291
    0x171e01061e0906210b0a031b0b09010f1d0a0b0c1e0d0503061f0f030f0b0d081c020d0e0f01090b0606030c091011011401050108070c030302040905 64
    0x1104880c48090141d128000c01c22441820048140c0c004031085030030038690b02d009014071a1003a008050400781007615489001c4410000c10408514148241422001c0c1103051040e81da040c6480c45014086480d030200c0c040d40001390701c042c0b01c0e80c0c4001c0340c85034040502a507081000c01060303201c500c40d0405140303540c00152034070100b8000c02c15194008183c6911407260000380c00340c552039000502c0c100d0148500070011680c0d40d9104031a1700b44000c1d02960503101c0310b5004e40010240c500c0c003040000800c0c58032100e15088407460044c40d15144001c0d0048400320a10b960303507403c583c4075003445800c0640304000b401c20300001d400140401240c090300400d0b1908484120750600320302110504a07689042006000511204202580294119401a202d90700c0580e1004031384100030040c0d038840c02845800d04c82c00e400106405481a40000800000c2510800642100b2081c0030341408102d4203000220f0b450310510300e01501600c24a00135042903a130b24425001c1c0e85e02074821410150011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 885732760 1250 885731510 885731537
    0x10c2024013809060f070602030609130f020105030621012304120305060a030501060b03010f0e0907030602130e0903070614011226070c0e16171e0106 66
    0x21030290348000d240e03040b010300341440e04565070072004004405030040100407806280c50743c1c0d0a804c3d600700701880da440b0780d502c0c000d61074040002d600883e2414411100f0801103000c82c8440d41c40200105d0380044031841b200741980055600f5040103004541c05140540e50580800c40118161518494200041104a01d01103643d0740302c3c2e10401ea01c04002001d40803c00402e61384401902d01001500f4001003680b94000403540c404021380000d002c0350b081100002d049201c0030003d41c101d50501c55040f110544a40021036910029203008903140d21a060074004504240e0062108540d01042040074030b540d0203107800300400844047e07413103030000705154090101d6405400140c0d00c482d42002d46a40c10141d030003d0388010300101820b000287c94100c1c4031003207050a038002c1001c84800c0035480c2c0c841444c0104040c2183d000e49442c071340d2600049402030080c00d4148212510b15100e0014001480c450395501c01c01c0144000750500507041d40c030444580e451803550107404540c4d03840c0e405c7d6600d0b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 885734010 1250 885732760 885732779
    0xd080601050f030a090f20090105060702101d0a0b250f030e1305160306050f0a1707030c06120501060e0918010b06030907031103010c202401 62
    0x91010303050050402a054900e44840c00f00ca50140d00900300154524103824042460601c0c4140100040e48803203844c145058291400f1a1078042164001050b030389410610a03d8092401e000350041c4d58815403c4c03003903004020017155007090800369544042c5400000700d8600240d070281c80700c100000341c1c10a01164401ca40300254180040318a5044001d9541e80400c036a902006000c010398000e0088070f03070f51521014070b804901c680c0d050000382032041c07544603000c80d18016500403924110000805062580c20a5040000181101081d500d44400d560300310400110901c41d07802903000100000f500841202c000e4051a540c000b01d080b215000002140d406812003000d010301d01c0c5000e4030f03655885010300d52041a40c44550103020345d007801030f80034012800382c241d4441d10104c00c0050f07a0b071001a0550459004424070380c00c0500201c00d15080f00c00500169000810782007510303030180600b690741503005040038221190b60041c0e0410455807507045611050320106a001000300492 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 885735260 1250 885734010 885734027
    0x518012615150405092d0a09050607110d031401060e0a030204020c0106030b18030406030903050c0d050c100e0303130318030812180604110d0209130311030c1515120d 73
    0x800025501c43c0110302c070b051b5151000700c0e5201ca2200d102143c00107064030b032240c118036843c641c44001c40e031203403c200707030041c041449082043c060b500c100d03400658002c0c030038003458bc02541030342401070407642032000480d0010800c1c0074003a0400c0900c1ca0000042c0c855100034200c1007580c3c400007480c5030031803400717400d0f0341000b030425100b1603d642008101c0c08c101004490423220907080c0044c030300d4024a000d071030034001d01031a9041750142a000c01d100303907040002000050310a809a40000c0e115101820841e40c00b400180302e00c0c0e00a000040c03d100041030080d0b6100d0190a280c203015600c0201c60206c0c00654100300d404a901052201d00b00081c400d230250001600c280030701d24015984440d0380e0300c0da0020400360103c3e9004c458020304d5111001c1380341117540c01a003500e01500e0300c000c000011a54a500481c001081010720006130071011040d0340c803001900015003c02a000188881410740181c0419440405403844800039500d511040441c0c0f48800054505141d80081c00360070b418 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 885736510 1250 885735260 885735271
    0x2f030310050a0510020705130b130603030305131127070c0303060b070b06130f240504060b0a05031b0a02010f0522141903051801261515040509 63
    0x4c0080b0302c2612281d0082504025200150303040254020142c0b02c90001e803221034881d0350440c80320030b01d4a04094a5410010a6038081d8a061106071182000c21101244c1c0c000d010f07000054001023920315107403450f03000c240355010310441c80540311a4003245c0702410081d91940046080387c1152410550503000d400300626000e2140c5007003000e5a142d414041c80000d10a501c07444000d8201901c9040903882503000c3c0c014624100207424513042c013a0f02c00c0c00745020201540101000000340c1e482c290251200350398601c5601c90420b0010341c07007910103401c0a8582c0000c40060440b52004003030102c00750003080328039400802d131040c000c20b0340c00484d940500120500c2d4100c410540302882c0e4400e00c4d00b20300e0b520016005a01c840c2e610503a08052442c65569410071a2200d40010326a000c805400810103c4065005181200d001520004418680358031032180040c1c2c45e008a00209401e10343c08604500c907941032404100000f680c8046d1054518084903010409001c1814070115070395016 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 885737760 1250 885736510 885736519
    0x702060f09030d08013303021308030a0903060e0c0f0d080c0a081207080c09010f030219030221040b0f15091006030f180609020102070f03050102040501030b0102010c2f030310050a05 80
    0x1082015400e0182c606d182215906254001403a548140040b40010000f00b14500c1540e1b110884050000c014440701d10050303442905190185075000030114003451142801004800110400c0c0300f405000404000241d65505041c1300807884504144407083d10984501d6020303030354070f00d1113441c4070401c10080d000c0381c1041003017020852603000b540211a60602c003424195824803260000702c4c00b034131032003a504407610180e40c04240d2243e0150050542c01c54030811079102c0360460500e2030010070080700c001c2c100c0301909004c141409062811142c0002408d049503283e030409201140000609840d0b200000c90114400c010069142c070820b01d1040f444101801810b02c48030603400c1d551520075010b840c0c02da80f22001030440e03008210303520081c1846001c8400d0540e980c24400d0007904107204075030200c2d080802484070b0f9841841007100740e5040c0d4a0b6001010000aa034130302003544901ea44240913400074074409803070030030000b56204205d18401000c10900348414000c002e202540143e025 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 885739010 1250 885737760 885737819
    0xa09090b012c070809030409021305120307082d03040f03120c08040221060a0905010c0806131a04140603010c02070620011d010b040501050a05060702060f09030d0801 73
    0x106140d55042d40c01451924080e14207071101801c90b81544a650b105610b4588000780c45540d844141c5c03210011140b00710b5154000346604240240c90b882694402452054100003041103000a01d0706400d20300c40240d21a4a102011241106903a10540382600d040114000354810580c0c44a002c1ea0707148000360041c0118a4400c0028003000f001502c02441298004414401408142120307002e07020f03301c1c1201c0b2107003864130503030008149500b001d540300c0d420070f40780400450180c000e45000d6036020302100d100d00401108000149100c0c07500702c0c128041e030504038080342e46c0c07405440c46a8060788a14030450400004042c00c4484581d540c07015900b00600400c090ba40001000d40c0b110388100e400521005d40d5800c1c0c0b030040502e40415500001d0720309540b031211105500800210500352402c010320398864082107420342c480d106055100008004200060074200060441e55041b0f5038980c0c1009140e00010741030084130031441c000901e80b100100401c20070340101c0001c1200b141e03100c416 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 885740260 1250 885739010 885739079
    0xb1221040602070e090a05070e180c0607030509010c060c05130806070c032d050d0b01080103020a0b0904021b16091a040b01050d0c09170f100b0a09090b01 68
    0x121034015104d0703541c5021182002036001c1009003e8803000a921000380d4540075110452070100e5002903445140c90720000c04050351068000441c41103500c03008045038200251a1b0b0202c1d16136120b0003100f4100060100c0100001d100740c015010303201b0a60b1100c9865034994070108143c140c0d00e50120a05502c03003424410300580100c506414a50946051100b803003600b1028a0269101c44030075640d4110b000c07615107181c1d480300c064219084d002d00240316141d034101c01110104c0d002c1c04080d5115441d1030080003030151441c0207025490015102608206a031030019001e5119550b0604a9411000c0d5201c40840b500110b400500b210140c1048080700380743e40f2041503090741c50f01901aa41e103c40c04000c41c0e01031020b40e01c0f020004030303040c400e502e00304a0040c04a03116106652950565501c482c445d40c1c004103245804461840080c40c07034002c000b81c25005050040455038000c21003e202045204071130203000d00c0103005580c020401c0d490211241c0c0030250001044121144110354400d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 885741510 1250 885740260 885740263
    0x1030b061314060c060c130503010b0102060f0717150405011a0f090d021f032f0d060519060801170307030804110d0302010b0a17120d0b1221040602 65
    0x400b40c074090806881410246008602d081c801d0200391502071007104204a0440c80d03800041c003a0510301c400c10304003947d4603001d25081c1e40303616011070b0160b000307140054001b40b07030812420303072011141c41c01d04441d810016040030419002e4902da920907042201c42d0704a814980551801407080d03d10044800040903500b03602c6c1e018002260701d40c0d400010b09800995144032110f1803242e001001c20082605a07143c400c0e0110038050005c000c24140840302902440b40980029580c6101c030b403074903005081030390b000105d5010614a980c820b655600104041d210064444179003800c1c0c01b46c40586500385800680070b800305900c01e8080715000002c1105004002c0191007009603d41005001c0b502d443c40d00035898001c44c40301c0c41d00410b2a50307071802031560541000400210a4500901d101c0d1103c02c030a041c0152280c00749615404a40c1800001012000918a250800f41d001881c6002500026101120360b0400e0450358031120180303911242c800360907440c3d8009810b0161a051134040041d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 885742760 1250 885741510 885741547
    0x4110307091202013b0603060303070303050406090f0506010e010f03030504030212010603172a070510051207030209032509090c0308030412021006140f220b01030b06 73
    0x40d000e4400e00c4250104590151880a00c5105c51442464600144090801d0b0032083c0c4581800c000e20811004151030800320100c03401140c018024518016160f141a0003418000e40704490302959588004086a003555501d6086441407015103030551405030f0b201000b0390182c02114010481c0002080003e4100c000c0b40c08496040d54216074440001d034515004000c554400b03015080028081c0c948240301030010b007440c100c1a00082c48024000d1b100d415803480c918504041544a400e0070310061070300c0d403003520707104215207002da1400301401e8035298114020781d50140400e0b00451000c00d24602445400001c100000d03800c000c2000c41c003c6004400b259205141020740e44005c03140920101d01ca112012b1030b000b01406035207091070301d0600b02500104c0078000050203508400f8056404600800b412100010344007000c06c070305041080350724010f40c240e441d800301c0a4a580100303420001d010080c1d011001d2000640d0111280c0050b050307581d00e140c401c3c4078102c100802c1c8022400700f40f84 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 885744010 1250 885742760 885742769
    0xf140f0c030402120c0904050f010c0207230a0b0d0912080412080c07050703110103050709081c1b0b011a1c110c120403030e0402120f090c041a0411030709 68
    0x3213044034908514241054074011841d07820170054810401801b10028543d03982680020081182c5410301008a841d410300f401904109100d04c20500104d40035290070654556000f000d03101e40036a5180b10b00c60a50101e4000108562a2003400090007200302030040c81c103ca40c100141e107803509a40715602d45024061180520003000041503403520040700f0361740950740c4441122030190f244d003071603120040540c02040c0000d08120000720000c1c8160080c00880354000018250713180086944042c2000c4040c0000801c050324101075803084503400d004501d5405400c031035015504003025945071250f04813020005c490b0800240000e00300d10229400103444c0c050000031142650401034400c0d106002c010561407207408005018040842c0c010070881c0d00c252103041e100c24609080c04103a010307030305d608400780700020001110280312000c0a580b00c686201901d00120308400041c0c212001c11003000120741b8021807034115410148508000e601d00229258150b240140c1c00078142c40b4103005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 885745260 1250 885744010 885744019
    0x30304020d050f0d12061a041208070602030c0c100506101d091918120e1306080c1305010305071a0c070e041e1e020f040f140f0c030402 60
    0x8598140002840010702296048090b40c0d020313400107400800089603410b08507a4549401c00004a8a10060504070b8a50301010601e0403d890108140559179141602740d4800070704004400010390148010b503c150740c0000c1282c0c132102440417003482c006540d03200c1c1c89603d10b00170501140340c0e10822211038901662904c00c46007401c2c0000d07403440c2c510b500d140503044076610007801003000020000b402c0c0c084501c2420001000b50808a03c110801d00e01d001d01540114140510303054420750146001e9580a000555041600ca0506c000c84946a1050001b80c03c0f00c02001003a00d0320030606240244103030418001075041d43c44084c0c41c1d042d544145008600009600605030691600346c1d14901c5031101501c08256032594031591180302150221a03180c00c00c812000005c1071141c0510030715070012000c45440742810604900000e0350502641e06c4000e00444410542d5036008001c1307070111450010171a01c100c1869000742c80381c05071034511510034400c204569000c80034152548190100c6 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 885746510 1250 885745260 885745279
    0x6110a020127080a081b160608070c0f05100b010309050d030b13050103030e0f0103021206190801090f0b180d140405030105090718020f04051201110315090709050303030402 76
    0x710100854040340d00c019014052070044500317100b65000a805201c48100d02c0420145c00c4840054580c0d00040c0200080b620700c900900c039082c4207407045a03016426040c0300b44404826114461007003005036084905138441c000e082c410b88003501409410032420b0a081c04070076400d598040d00d8800c03214510082650300c07030000c2115a540c1e4000d4000703400e1140b040126503103d00f0000d0a0540140a0390702030400495943d0055220703200700d0700c15213218050801e041d00c441d01008110344010380d40d2990104884008181b8103020710414086910414200103180e400c4d190113000700030700410520f040c800c01030703421080101c017003102c1604c481c151800308404d80d0701131600c170594011500120b07015864041007140c46078001454000352520580c902803130318913000c1814164400d03040384070900b200a1100300160305000c000c05240055950010450318130390541514650800c0b9102c07406001e000c8184070301820840e0f945500f0034280d24050200b10300344008a5624440640020701452054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 885747760 1250 885746510 885746567
    0x210c0f18070e060309010c08010b09030d0c050709060b04080606030123060d0c090b01020c060a0c03080c07052a0103051b07020307050a15020f15160212030a0606110a0201 75
    0x1502c0c04011000003c00440d200d0510400560007088648440300210b00644004544082403d0554640010040080140b58440c0008940148610804940f94810301c00c011a0814a9000320000b500c40c10340c00c9501c0b5131500107020b16014003d08540d000303914110404800702d100c5456082c001030ba0500100340da0711804049803911045d44000f4100c0700b408032000c604101281c0003e00902d80036400c554000802c0820000c8a2064000680c0403c05c02c06c900800207000352091540b02e00220035490600d980741d10343c98105071404100701140c88901b544a002003000541203003031001d0a280c200424a0700c244804083d041004503001c0e062008901c801c1156000c00004016220142580740700c699582361a420520304040044050b002d0103000c2e20070100e0029090150800c84020440c0c2a11410900c0c07000403004086401180240c1c032003803110701d20050045d8050f1b0b0420800149040c500440140411251584c00000d50000000080076131703844900f908a90000021804e08250030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 885749010 1250 885747760 885747767
    0x40b090a0203010606031b140a30050415060f0e0a0e0124080102033c0f07030c0219150207050610031b030b0c09010e210c0f1807 57
    0x82038002d5041d800c0000214805074117801080911074240c206068144100505440040261141009508041c000ba080103031062036105c02d540305055035086600c0b20030240d141186414030a01a4407512882440204407210f0760101d90140e400c1000c12819041c80c0701150100c3c12072141460010840c00460040159079000314180241000200480c010001e45007210000ca2020110340c031414600019145006000f16172007407209550401c02c2030603001100c01001089882c0c0d94184e85030001c4040760b003c41c036208d14001c1c02c2c100301c8080d45140240e001005d03555a007002c0d0045412030050a0840c008050301c515206502807038180c1c0040441c0881c00081c01221310180580c8150b105010103042101d8444003a24082c68144002603a2000843301075500c40c80003c101008075400103488000250141c1017040c01450444860803140780010b144501880c0c071808507140510b086000311800708100c1c194104103981042c0c4c80002440041d5201c0d400302d02000251707000380c0015104911 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 885750260 1250 885749010 885749023
    0xa061b0204050403141b010605060f030f1510050d0c05121602031c05010311010201020306010c060905010b1f08060a050a180e0706051b06010b0403060903030e0f010902040b060909040b09 82
    0x80c03034482c162071b00030003501d20310041380d81c0524801035441e0843c08126820801c0454507081364040180d86035440d2461101d80000c0010b2440c03032155404650030000c0d907504403010341d414401e592144d448601e041100ca00b102d05c42100f01d401d0020400c100c0c6c5003074110f40c0d44d07a90302007010181c00400003a60b4406908502c02c001100004c00d11142c40303031030760b4102035101d141680d00a9103241702e0400c07101d005900f00d201c21f50f00356001c101583c0c0e056000442980000b01032510520000c05e00c080c0440114103d0010500c000c5558032a06400480445e0300c00c8896620100c210781150b11f99281c60007040524034940541501141c411010b011a4070329034000c0d4070068129402c60704002d50341c040041080d04504503011811604403600e03220390000288a5040c0c4072000c42d054540341c0f0703540e84c5800401c0360210032000c0c1501c400218189035028020907448890f4400007140070b098034410442101c5060510360321510b0244110a0692100e40701640e0241c3c1c84080583d0a88800ca5010326280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 885751510 1250 885750260 885750287
    0x30b010e0a09020d0e0123010902070506060909030405030109033c030e0c0307030f02030601090209010527030a150e150c280306090b0105030402130b06041809020a061b0204050403 79
    0x45c01c03c1141e030a140096611280fa081c807047c19400540d88540002003684a480e8010301540e110402203842d900d003090030160400c954a04607464580d46130701081c2034540024060740400c9000c0e8001c00000d4040180c41c1500104015681003034000c1d055a5120050200064041550b52012078442c0003007007118560b40840141200c80d00d5035070303240c4118001e00090302240030f4040d580001032620440d0083c0c480745c1d801615891b003000c8251321684d0001e020000302060718610504036402d03d44061044a10300c50007210a41c08030149401750f50107883c194021040c2c0ca610041400c1014400ca0110581113020004080e64446190603d15035422102106800520100c850030070650b4240d4001e4049581107a01480b01a0001005642c0e501084170080c3d08001003540c60700a4502d0b660020988500c001d0540e4181520b0308403248400403c1d00442c01c40d01c0d03650300c0364420351a1410f00c10004002c14984103000c01e01203440b8403002883d00300d0017801180c569001c982054081c440c600c0c00398 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 885752760 1250 885751510 885751513
    0xc0c10021215090f1b18040b0a1202060d0603080307020601090608030a0e060d0615111506091f0b0a0c14061015020c0d03081e06010f051b0a08040303030b010e0a09020d0e 75
    0x202440c4076040048012020381b82e11880c9082c1c0d200140c0e0505100b90f104950400d4183e406440d0581c003800095440b104404031201e80e240408400a49084055070003030403140e00070b122540c1440300100490304c246c3c001100b15030042c400e80300e407150f101c0b001d510400c40c00e440d52525561201c0144010700b80e19027058900d07883c0c00d58208101580a180a141204030328212003540140b40c4817407038030315400c0c0c40701c0e03401010300b000094400310040380441104510303040b1041e2044c0d44590200e02c64100b815804000b42d01d0704991018000442c08807800c0d06c814201070030107810050304500808a45100c0d603902c010386900c803030f50102c0c001c3c801c0c144103203c06040303c3c01040b11071a0007030820b203046980c050440d09003d400022581c0c241d2103948900c50603119034091107680041981c80b42c021440754060301c25a2080c4d00740104c0103000380f250040c4540c0900351036500b10704d401340c2034070b488001c1c0c01c1c100309a01c01504081d0303841d403010008076017860400503034442c61508040d010f00000c4440030104e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 885754010 1250 885752760 885752767
    0xa0e0a0e04080304110607110f01020f013905090d050a150b03060a06030308181c0c030f110d0c050a14030301170c0a06080c0c10021215090f1b 63
    0x744282e02005521440c032441981d00705021850400050b80200d00d400350591514681100e02d604184041d40458101401180c2d40b8a038440340090035130f4041c0e1308058030702d54403012189910f8602c00b0924021192118450501d69044800904a01400034100e10424407500c1e06004d02c40140001605070b0b8020585c1046400d0704030007500981441c0c0c00780c2d030080c0300d0080090100c1c078a030b00c20b50090301d500d40e83e0041183c0360203100010580042d10034651b217024121310740d54030715005800c2044101050b2220012441103081c00b40803035041405100034450401d1490880000119017110707860b00e03a0400c0420070b00c00e0300300f4134646035120100501100d002d080b1200401800400b0314103e603400107025003041417695003661140e40c081111a01302d0003126050005078002c13905103034032008a83c44641442030341c640c40d528000d02c07040002c070500e50000d1050b0300c8420380001c0315404041c004008211001c4840451400c02c8000c021103c5072601d400428842102c2240c8141d4007074406545585 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 885755260 1250 885754010 885754013
    0x30307021807140c2a15180301061d1f0303031505040f150911030112020411130302090c031e07030204051018091e0c0e1c0221030a0e0a0e04 62
    0x50f20104009650304001c5c50740c02241e0802d085030501c005d10540540f14252040c8040800541074005100459800b0048850100c1d1034509200344da0013000c072004090b145000302441341c8444840500001e41d94240c54044800d1030045440100c1160740c5407600080000300fa2034102007000031a00040e41c40f60500e0348485800003c3d402424100d00c5092440b0340303441d601c180100c1104c03001e1043c660000390601c0100241400000009c2801d0300241011405a0255016200c03aa12030719100b442e0a581150610960030401046980b011161400c00c0c61420b0120706480f00300040125940e4964010000a1482d8881e4040c1e50003004003401b0460110368641b00500740030602100030360319901c5000c0000d00340c1c0d1a401654005a20a0030080c0400c515120120241c64020014000c1c41000003408120b1740350034060a240324050220030440ca00144100500030802c5403101003082100c0c12215100c0b171011044039443e01c1181455800003095102003980c2c410164064034040402d00100030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 885756510 1250 885755260 885755263
    0x120d021e090a08070f03060f0605032406060301180218030618011808040509070c08030a05070f020f0705041d0d020c10090b0405151204140c030307021807140c 70
    0x1001c008129001c0e10034036207401140c2d80d02c201500c540c81c1a1001c440c81000401c4466103c0340e030407035880502140f50358a807404070740781c95049110352104982805240300d44030745206040342c0010003101c085141d549040c0f20744020030641c05100102d10390004281c607444568040c405a070820290907110685040040e0101100d850840b00303256508004034404085044200100034541c001030f020304183c105800d00264074402466441401a00300b144808184004083d6100e01407144000c10b0a20b01182c4c000d02c107003000c0200d1020756014829104240001203600e90a841040e078002500143c28511145140c82c034981101090050b1024150115404142c1280b40c0034107540c852407420308240202c413080003c2c440d020141c0c900788014801843e100c641100c000396054046070034680c0007000b100c054101900c3c00c07244c41889540300580b01c10103000b4184400c81c101c003e5800d10200d034000c240550244004c0000c40d04401002403055401102080350450281e016952140c07240100769 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 885757760 1250 885756510 885756517
    0x3050a02070905130b0903120c0a1b2301230105010311040303090e0a020421030207050d08030612030c070e0702061602030d090206041d0a0e01020c120d021e 69
    0x4014010758002203400550380c0180c50144132498001034401c00951100c456400e4040c10303041a40c0810030040c090300f100205c0e014002d00d800300d00240c1c0c03aa5844d0010b481d01d40d40701107000d20b41010180e900040382140d020704516620038842c1010303400c001203510380100760300384078100155040714100d4164600d22450318140c45081c0c81c01c2010030200d0b0a403a24501551100900081680c00c051201c280b1015031207801010091015081c1a2161880317110b22400b00001110600c0d8030142406040d810080040100415181c5100544241e110750780ba074403008200c00d0207508d00141c9200b600c42d04104070303101c0d0381d50001035601c01512111801480e031020f5500000502c100001b060040388005d00c0b0b0000d22003160020361411015541c441c02800e4084401d980c010b40511000600c0a030440768480000c82800204005150000340c40c0c0c00c0300c001442c50aa40d03841485100000b01c0005405030900038104030040c0c0740d80c140442c0708045d1140751a485486182080c12085080072400a03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 885759010 1250 885757760 885757777
    0x3091503010306060f080616091d1509070c0818060c07030b0a0b1f0e090a060e1819060b03011104170f0d052116121a0f030114040305 59
    0x7070084d15500c81c0315110300407550188100e40d800c0100811082da070010300507030600055040c422865607460056a5500c20b01d40d420030052450042040080b4004804a00c99000104c03103a04281c144402d00401c4d84401010040c07907548001901000d03007066211702e828403280205620341c1c07860485006034588490b44011642100d042e000b2490b409218014809441805000720369180c03c80d17030f400150001c48040d40014420224040c1e0520340f81c41c2c08852054031340f00302c00b142051400301e2906030300d000140305030401f0b140000c00300301440c4040b40c0100d85280c1c841020707d036859103061481c001c106488400c1d916628014203402c01c03905040141c41201e000360311401ca1103407140300c0d10b074980ca03284030051095008880c61120b40c80c02680a070014440c1002d10445a00c00d0000b03820301414280e03000d42340c9120350701901d41d9007a4001810811055003540c18001a43c14400c0005c440c4101c0c8251032068400500358141030b01c095000030700c0c6000d14140126241006d06010785a039028008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 885760260 1250 885759010 885759023
    0x207060e06010b40150903030c020f1210150f1d18011e061e0509090a06141b070506150111010912080a0b010c0206070813030803251b05030915030103 66
    0xc5c40c109103001e020398030100c0360181c4904034018641d9003040044035208031500d5000748000f1003483c0a020410500c8002082c800c80040d000c04080e00d85846084207030320170403603015004020f0140070031a5614005040281c01c00b40b1b081c0c1c440d222644100d071400302100d00658a011485444941c66a840485c0c0c2208000304005240d00c454001c91507000e200095170b0840010002042a0308101204550041515050b12030ba03903401d03a180d500f03482d4246d07540e4659014007410b0002141600389040ba0b400c41e003c0540303140c9507190395a16200c01006015103040b4100c0c10849505034001d11402c006c03046804003c2001e0503140ca80003008401c206603200010741100001001d03c9510312034a40c400d03805854020380b6a04a60822111f54424402100e18850034005104a40321141f101c20185110f03449098480c500800c1541610310b8002d80001441900000501ca6503084103d03115188410b04540060b03400d9810480e01d18825007036200d821182e904e00d84081d0500c1c100c09141680d105c0d81 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 885761510 1250 885760260 885760289
    0x31b03190c0e0c09010509130f0204120b0903090109030b100e1603050c1312060207020907020d0e0a05010f05070201211a0d08042c0a0207060e06010b40 67
    0x2c00f6810070f00408000c00e0125000300410710380e51403e4891006999000b240101d10000c4010441c3d05a0b0006d03480829030349182d03c8880104580804403642c4480f0010045040440410000380011311034070016002d09036030004a0301e80400707541e1507400760411040010007402c01202142d4003a4186c40c0d4000040e02d02000315680c0b0094000b11181e010340703030860f601400d05007000c4661002080c0030847d101582044042c0050b11140030462007441d4a0700940200b05e107a4001074051200a407880348103060220092107a80e030000c840030511021881d2940d29614a8801aa0051941c210f290f09110b6944c0030480d032815030781c1126040e07101c2107001c280c0740c641d90b41c280040d03214a990020920041840140700c1c0c01c84034519525009803855011002284210b03444039030000c16914942c5890b0001094000d021041c001d0841c1c52100c44001d240d00d61628050240c94000d040ba6013000d0030100c603805802000c00f62111820032492280b08198049035022001010407620038111a60301d02c1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 885762760 1250 885761510 885761521
    0x120c0906021626100c050306030706030504150203060f030105011412030c100b010203120a05010f0b120601081518070320040306020901110307140f0705031b03190c0e 73
    0x82c010305044074500c489050445494661240015415032006070951181d0520441d101c116401401080c3d1000c0e01c030140c1d207090640603d03041000c035803c072405041c00c03d014007000500c540c0300700039080030685005880f602c581c1e0005003403943d46d03284150306600f000c00200305201422200c510f910001c9407a40042c54008014030303102d000d440f03c20b084070341150000410f111703580d401040503805d052065a15010601c0000003030001d06803404044980d030340c0014040080e502c0300ea40d018040310300045040040c640c0345080460b02c0205011704021142001c20f0408076a0255a010802d00404041d46c950a002c10066140001c0f0394034000a4109031001e4030f0808808400c0e801200c6035110b9900c0c1c1030540d1514030284d40030044880c104120b081c0c000892900c24000380c80701921a0140e41c2d24640c62442061030070084901c04400d90300210410040340e070b0006801c50040c0c080003001016141d5480000c0c0c10030f14015100c0c4d564840101e452000c1111030000d85050700c1b0340007030a08098680 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 885764010 1250 885762760 885762793
    0x7030c0c0218090c090a0e010b01050f07020f2b021305160c1722050a05010e21030403050303101d041b230102010e0102091f120c090602 60
    0x400201a400580000841c401020b40560140d40490484100e80e21010203401050508904540400000e9540c4420002ca50000e0050200c840301c246420350403d58000400f04603480b824000911440040405144544807400c0d01caa464206004079680301d03d0550000d1185812000101d100301c4440c0c111081100310362042c14000d0210b01200340003035021103020350740c0000c0e84409841c83e647c5400722002170700515005164220701101410071549a00d44552480c6102d500141c2c800c2c044901c090165036840741c1d905100740c00440d40c82d14150154156150040400c500c1c400341e50200040210522000100540c046c040600f01e501d202c070b540300102c40d000c0c009106ea180140c0104004140440d00307410500481c18401d15942e880716070f540b14848410320303940c0048000c8401380c100c200960341c0c081c0310f00c8244c4880719009601c4c2100d52000184006240241d05040c031001c4666070038203910a001c07110415001450801255541010103404080f5500c140f00043c41008540c1030708181 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 885765260 1250 885764010 885764027
    0x10b1b010e0d02010c121b1103071514090609060c0904060510030506090112051515100807030e160614070f060b1f120b1504090603210207030f020a0504090b07030c 72
    0x425001c03010380b0720740d4490423550410301d0284a60306200500203030011824045e00052488603a507000544660390103150040c1c1140242202c43d01e030810340401142c40780110300c0039031280307002c014035903075981210008001703080c250001504038601a250380407035074066200b54042c4c1d504480c482c6e126a030740c0c1a03015103070612020090041d00320040c410902c114540d407058011021603002c0c14945481008181480107103000f40340020564410300c141d058141c40b03210125078034180501045000380f004054207010a114450410030b8030303003440e0f08641c01d8809450f0f4481c0e011800201c02c00181c2042c00203401c5c0034440b180300b41851481d00841c00102201c84444c5101629461155080e580d0400000d2440c040f1080c0c10040203188040c0c21100d0b04010710160094a0000510609506042f00d9082ea00105903140c104201a030303c40d01500044c40034101c0c4d034401548010020350b480407912800e660340c001a002800d0a104e4400c1054411101c4e201d0303102030358200314281070030400700d40020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 885766510 1250 885765260 885765281
    0x13080403020d11030a23030c0606100908060f160c021e0625060506030a0201080103060207050705150a111204090f090b090f0c010206010b1b010e0d02010c12 69
    0x10020801080142408108800c1c0d01c2c0c01042000803203425100420b080c1502800c04030b44c00c4119494518601d54402203807240348400c2e00046081c40c2030050000d941d0784c03016010900c01e01b00008160a903511419100c0040e0074018103844050504855403c92580305444000021a20304c0e8a8010782d445040d4248899030001c0422096884c00084503002841100255420040c1044405e1400601c07180201011420501c00c040d04000350400c94102d400280c20603210b40c0182802c800582e0b80450b00906581c4c000a0040e51580e561134080d00c3c1c00d07442d40c00b0542003602844048010f0f1400800380c00c450885440c0c03c8806840542e20a440e0746071040549105642400240481c400c5588403074050070702c3c01c0c000221501c461b101c00e070316010704583e1843c0642c8841e22800400300c0c1800f17203580c802c400b030004007030b80e5041c280c0e2012640510080814200a48040b00710aa00c0135082020001147c2d000e954080e1410301303009010780000350a14010540d11504046800203e2080001c40b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 885767760 1250 885766510 885766523
    0x31b070507060e04051b2a0705011b020906220519051f1503021606061707051509180a060f050d170306030703080d060e0906070c240e010c020613 64
    0x12130411301c41b01025001b0304a0281e68012400010390450311804109846041400050410910b00f40005280104048800190b4804103c070040181c8a0425140c0c202804813001095186a2007000a10303400300a41000c03264200410f1103a5480b006020b9040d0b030100e000c09100c240d03a095031200d040300c2050b4440002c101c039400c04100c144200e9104042111241c50094540740008060b004da00584284c1035610300d548001c01c104000390010000804100c0d9405000894a4500000c6803100740841c540d41032800003400c061103943d02804100c0300c4032007038a030400700c0c10302030035100051407107006850300d10f03c00ea01c1c04100ca20b04150a80c141030342c0001d1f104104444030301160f4030390b04050300150b010322408034003000040800029110404418000150044c5002007452100c03030007030400d0045401440034440b846600860071404190448640340d034401905a84690180303c403c1a000120b113006150203400106400181d1010351950803611a500d07030380303d00c81c8003c0b880318009024 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 885769010 1250 885767760 885767791
    0x219050306100f02030c070f08010c260406110c0d09060212041217070f0b161205070203040b0a0c050c01080f0a050c070c060302030708010f051302031b070507060e0405 74
    0x28038401c52629085203c0c40c81520700b401072030609035190008680113800460106442408902001d200b01c1540c07200f5803a00c9a40240321b04104081441010b80b07203e00c03110043d0000d0184100c90f0050010329148440302d0b80e86003580d51490392602c240050080008090040005c0c11900c001180003010007000f44280c41c0514008407000c003901044011036882c0207141150b80c40e0340f031041c00f800c04035003e10001c0d603405440d8600050714907402440003c05002d1341c1c190b0705e4507941c05081100a286030032000900c0303899040f0180d103180a1b0390b0100c820701b040025507001259004903040ca10501c00d0088401003ea042c005507503200086a402a0906200000445024450300001e40140b40303120064039115003622440200d02068001001107500041880000d90707100300750304d00501003900503075420340c101070002d20180760f803444083d441500071010441c20b4400c181e151000358000e20443e5607511051400b1511000d480c49400007140075800c0c0746185003024080d10344580c1c92058141c04 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 885770260 1250 885769010 885769039
    0x203190204051804060b0d050f010f0c0912060902040c050c0c0307061713050304030317090c010e040911090103050a1403070201120c020a060f2f04030308070c0503030a0219050306 79
    0x103c0c254018419a005511038240880a8403026032102c0c00c0e070f02840107002d843c4a02d01c406400e5400c41c0c086058034a1a2800c80e222460340a40040c007a107482c1d046a0703003000d60701d040200150403103400213503200b49003159102030b0f0307030b00b00c4001c000000701031003a2190451001c081580751a40c9100700390115802210051b42d80c85a0380c0300e1940311646640d06100c00d60ba075150706281da0850340084004c12446e400c8001e98841910b5070030707840b44c0c40c2360080c41d0703880002c0c0008006503d0b80c9030960056840f5428602089000c207850384040d0006000b00c9155079590401d43e5440010803020340700010310340380007003894030040304681d140303a010703102c40d01d00481e001c01042c0200070120701d000440c003500001e880098000e0150490b40d0b400f20b500490507807414000044601208040c0e91340c030038900da09005020ba005004c0c3c40c212170309418208071aa83d018400c2c5c1d12400150f00090144c0400020404d03c580749034050003054880c0003021010310308003035007925103104c251402540701d005091f4510 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 885771510 1250 885770260 885770299
    0xf0f0b090f0d06180b0a051003390501030507020601030c1e031e06050726060303040803040605070308010e040b310311060a05040c060e04060302060a03020319020405 73
    0x400e802400b406507011030803142c5500c1d0498052618540a0444080d810310511461858158000d03203944403c02107030910840c4941340c03082610000b04000356012144508a80840c25044544040b1080e10b01c030740710038190350f00400c0c114001d050100f458240800da20a20000700241a09e5210644c80e42c0f9900f04501d10a118500008166280d145401e010000a501c01c0020220708d83d030074060010481d45180c21401d440340241a0801c11400341c0090704094160510400508414a100c10603a03c039000481c0c1180b04a8000400501c80001c2c00556180c1c40320040050500a43e42c0405503600c034400d8400b2018295000b0f801c100c03c402c0801c0781b151000400403241481100c0030f950700000c50158078110403281c0000c0c4c0120303055005107440b151b010b0010710f80c8003192400c10415031030250380b50b0040d6100307405a002044040c101400d095100c0f98840d00c0910b07001004030762034259400e40100a036004a81c54241801920710402d8503030f03094029a01641c0004100c40608c400012054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 885772760 1250 885771510 885771529
    0x100c08090a030e0301020d0c120b09090d08040c05060310030b0702010c0c1101020a150b030f010c020703030813060510060e0a0303050a0c08370815060d20040f0f0b09 73
    0x1307500d558201b0030541d044405105081c1510f900f5150901c6010280d022541124520345120703028141c0f040070015100740100b103164041c0001d0520f2095030701c80d4144541492100c0c1c00194102000105200c121748a402005084a21500100c3c110b81ea90074012030a1724007444008001c500040c02c061300041b090b1011b124506010f10444684041e180c842c1c00c0c0842e07903012201703e601c0d641e94030009142004e0052002406581000b4030400d500c80e04029620381c120710000d401c011030700c00071450009610b00a002100d0300610107121906200000b90a400500c2c41010045040252005010300f0310705807142c00c80340c1644031241056070a20003034030840450b080494070240104803104c1c001c164070b6050301c2201000089224010104000e040e80c584064020380d0520072070f001003201101200652428404060750000e07100c0300034000d080042d004c96058036a001c0403d0401d070a40c00b4101c4054400c03541e40d00c1c001840d00c1e40d6942100c0c006d500310f005520706200208018407490800c40b464 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 885774010 1250 885772760 885772787
    0x120f03020d0507050904061d010311010c050105151c0213050c0705030c0106031707120c06380d480f09050903030402010c0c05040c02100c08090a03 65
    0x5850141c40c000200c1c100c0302d04030b5081011400c013041008050919101d0400a080d503807603020ba6550965000e1020620f0511004080c80c44e141700301005a4030405040051540c403d000b03000b1400d01104210341c0c0e00307503030951354040c10740100d420011141e0b044040d1041a00540705141007080c4034012400380800510f0104c08071010000c10740007032030400c0140704042c0785034000a0003e00718502540710501205000705003403024000722021880320152581c4c4a4890f04000040850518000014215469000d0080b0247c441e241481624400c0390034000e1140c02220f81c00288076001308545d04a90350005042c42c500d12200b6029489504091a000c5000d400b468800c035131808107580c51440454008204400d11101c20400404640c0c20b0202074a1211b8041c8101d14104114030b6482c000200003a0400c01c27220011b80a00c042c5008020190501a2082c0001061540042d58030004800d4001e40b03c2e160040340320600c1d21070002180285003003400341c1141e82c583d0b1003c94090081580 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 885775260 1250 885774010 885774017
    0x70c0f020f03070815010e040c090903141204020a090c17090a0c08070905060a030305030429090d02060603030901092607141801060503060d140316050613120f 70
    0x29aa000c07035a08203d00002000240001d0490703c0011103003154601041e4800d202d1210107509000000d2880c00070081075601c1e400c0c0c00601e00083e410212940d000c0c1117036a40904000040c030b41c11707003502c0c2643c1a1085009a0704802640c3d40da020391000c503a50907480400181c66030364806190385440785216005000201120ba641c48d03551a01164421503a0016500f580030360030400c00311082d406083e91000041380d41d982d00910b140c03005403091000400040001c001d014051340c50040d0b01208040728000d020326061140b80002c00e49586181c02c011640152240000180d520700d0000200c400d00308040c0e40351801e96141c100348800100c100b80040d0500d1000d0303008481d100701c0800c6800014400e2004045e0020b00b44000d01669000c004c0840d001c10307100d00014802243c12074212500014140c0300c07200c0c01c080b2400c00a1580a0001e20365006005c0010603200c500c0303444040c002014001d20a9030095251b02240400441002c10002c10b41401e004600c0c050500604c1c1c2c44140340b07401d04 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 885776510 1250 885775260 885775279
    0x20f01020d0e060a0309020301020d02040e1501021b03010f1415041e050c070b040f0b09062a070503030f04032019110301050f040303150b1b03041508040b0f070c0f02 73
    0xc0c0083c0c2685c102f164241105540450b0070801c003154805119080424071030342d00608544440002d48681c0c03401c405a1044a003910074201c207032001d6110040039400c107002005003400b44001000080003d903064045039102400300fa00c01d14262048002d03800030310a000401c0840501100d016082c001c01e031800c0c44c20140458000300304110303009407147d07100d20794158414000d0301d8102c1c0c80d80701c05006ca0440c0c1c0d000e0001c10400c0010085d184003101307115007900307607103040917900c11102d8410210010110301011003031050700c0070840c1007940124230035161070404201d210007007901100d800c011650380742e0000d99248159804145c0c004422405030403903041d910095400b203803c0d41e4041d100c490b08000c0460801081c075603d4403800b07104010f0400503a4101e13140001c84240750160785030040c00f44400c0c100d04a00700304e0400465005042400304d0700380c0d40c041c0c0d04015040090865050b2a501001e00c0094000b000307540300140701e001c03e80c89a03500d011950b00d03002404114448100d07045000d40 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 885777760 1250 885776510 885776513
    0x40204090c0902040e010b030903071b050409080c100c05120618040803040b0a0e070b130f0806190b0918010f0e1f050106020d0c1a0a09020f01020d0e060a0309 70
    0x29298041e0540200c056512854802c240200e485d050f8019180d2007828000d10954400c088121411190886080a0102508030088030400d00651003180d10618048100c401c000b00c0d0009003020381048000d03070380320442c54510a0184d446200811000502c10010700120b1420140c00c00e070482e601412a203140036050325800c10386a404e0301d0680e40c403000842000b080214071504039600c42c0741401c00f409022505401c2e079996014038043c0a600003000301e5448546008080d040000700200740500340d500c0d989080003502e45406807048501c000c0320755034910304001a07000701c481c8140080d049140e903598680494105824100c00c500c400d540700c500200481c107090080301d88290307003c000340a034a042c00c40c001e0000c034200100440c200303050038010040c09030041155040529541001241c0c0c144914100705038a0050100d03445c00c414503428007142e10f1071544a01711040c03084d105001c555410702d005a039641042c0d52000005115000a940c49080000240c10303140c00742e040c00305000c1d889 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 885779010 1250 885777760 885777773
    0x2150a0225090506010c210507080d09140106030803070309110d08030601091d0c090613060e01030c03150b09030c09010b09090c1215010c0b0403110607030b010c0b04020409 76
    0x4686401c140d099600521402901c1e01c10076410140900f06a1201211603071204014206110455002e0505c0c041c2c0340175180c023480c00c5501d65a80321021907500e030b0146d0b103144001e002140342130f42c0300110308400d000224014494031046d2a0420002d0341966038440c0e0880291102e207a0881d9500c0d161502d46000c1d8841e0500020320522480e40d4544920342400018511843c1c0c2d8443c400241e1144e225101547d06a0340c00d40d080340ba076842080d40c8426032004075942e403254946804900001e0a40015503903445074124203c2c40e403d80e001d00082d20000d000f101542c0f01401321a17440140644100580f101c3e0710003c1010004c041d0035201440c2d100d400051a1850980c403600e00b603880011440d0b21031400d20050b949c06184240d4550400c6022081440c4045000b0124030230403da11445080984c002c1c110141220303880101c00c1c0700351400d0f1400501070580544050464410792000c1800e550081c0246520313030406030b6401701c018450b9100d400c200040600260b821594400c08040440c52 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 885780260 1250 885779010 885779053
    0x130605090106060e01020304030b06040b060c07170c0108011410020123060a05010206190b040b091e0a0e210c06070f021207170304020f030d031d060402150a02 70
    0xc280c800098868600302014020844400031181190000c00041c40000d00c410540b130b80219040d100083e628000d00080fa0151148051404040c03142c800001184541d801d000c2c181210300c4030a031079110a404d0010b44d411030080c064040101c0030292000a581010019841ca0015038400400e010402c0c904100350720040951403691400140204612030403e110305000034907007072009003218549032400fa80e800031081d400d0068a5250800e15510b81c0d1140c204c1284000014448d00c00c5040c11080c072180141100110135903e586c0d03800041d0702c02407505c9648d03100b0a0b0340005d040d058900010042550104502c034448441c0144020200901d04111080c82046140c8481841e440c1c0e102010b890007040900d086070600082044800068805018501c407a207521182912621648000b038580e9440d01c0105426101d01c072002d0341c0395a4560043ca6101c8458002862400212400c1c1910740e00121006500324450600c81194500c6c554001d048004452045e980e001a640b061180d0301030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 885781510 1250 885780260 885780271
    0x1811040801150828031827050702030f0a170c040f0905090d051b2505010207120b100f030819111203070504050a0803040306180f0b130605 61
    0x3950740001642c035000c2e80600c10007904440d0700400124040d10146010f4812009404001060a6483c0340070580104060b05112404440f420400c503160031030902020903003119080b06200c0820b00d614101e402d07104207030142255a01451078400041904501035000c031001000b040b041c05079189100c0e408040710f40c002d0b1501d0751180c0c0d80b580740a8184140725050703000744229030b25140c10710020500c00901500410106d041c00e54540e400c0c0f4003c030600c080b0781041042c0901581d02c100c60701c1280305820300840c402c001020303603210707031600c1c01282d60b00694000c240109510707a20031804a030640220940c85038180080814180c3c036405c001d6010a1f482c2e0049800450100c1d110040030500c009445c041402c6150426416442c1d410b581d50b80e0032603d95001c500ca000101040c103051080701104c1c040c00010300003c4802d6034450782550b0740d0340103120559269103007d084800016007020862070103038002c2020b110a00503501e0340c40781404084c21841c40301510204440004900d40240c52044c0c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 885782760 1250 885781510 885781513
    0x302070927060b0f032a040221090d1b060b0d050307140106090c0c03030911041d0c0303070b0a0c0203070f0f02011d150f0904140415110418110408 65
    0x19a40a0244804c03c0c0c0403c40f0350340710f40c100d42804c000340c0300390313030825209210581d1081c981c80c1c0c0103a010400074400c20580700d0f0120502c0030807030505071000c003106000301e45582c12900802179a420840d8081d10b404003a5982d25440d00310f50000c0b804075040101c01080082c00303e00640016510ba40c5160300070103080311018650b052224a11000b031058500408095406019405907814000d252110004004040c10380d503459035000e10104058268085e4405042040316043c001c4800901402e8900c010085120b030200c00000780c10044160f5191030b901c180d105540392203c1c62030b82c010346020032421045200610502d00801c424940c2810020f01440130710092065900004100500c3c042c44010307400140c0210300060f0f140e0944145200d031000404a4850280c0e1101130514032900b08119400380c1050980ca0a1240c0810900d0282c0c1c410305001141c80811100b80e0140c681e0385180310080f4806000030010112030309001450a215950001008480204025030503006600141120b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 885784010 1250 885782760 885782771
    0xe0111031908180a0b0f07020f070b0405040e07080c01110111030f01030506060406060509011b170301150305221e05011d161a070b070305061c030207092706 69
    0x10300e00c80e0140007410030f503001c000e0704d0742980d80d4542c0c0c903150354003800400c40c41c082e1500080c0744610a000340700201c1800b900340c0d5900b036640e0f9103580c403031780142c0110346c401e5151011040c8000400601e5000303e4003100c000d42a200c18460064403160400100c1c0413080d501c4001c0944c86501020007140318581008200d0003e50440c10181d16000e1f000381040d000701d2071b19030b051104030b40110079500021401d1800702030380c1d541c0aa22404141c050701c03000704001c031183c000d1907601d140b42018506a030680500881100200423049003a0351064400c0c0b4901d04c2c0c181d28085291895030010021540034030b04c0c0800c2042c0716242400702e0060003006481503590380c400004604810005032030400d5003200106604000800d0003074980310144200d122851048040304911019003055a410755000255410039252050018020305011507010b4420031a403d42c042e280c840740c0094270180394069004002c150b044c03d0140000307002910548a01160540344220fa041113030454151003032003602d01251 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 885785260 1250 885784010 885784021
    0x807060203090607110d0e06030a06030b150f09010b09012322050121020705071208030601170f0708060f0d03020a0b07090302060d0c1e021b0306070e0111031908 71
    0x89080c600b0b4107400c40d038001d5400180740f150300070701f00b00700b400e401c840303850703a83e10352a080c0c2005140c0b0303920041403c08403c08004032860603140310000080305a510128040c100800c104c6542000d0040310341d848018051150b081d403003202d0001001258090014151349888910780094001500188815001842d054610b0f0b010b140c42000030802824044851818a501e0110480381c15244268080d800300700c6a061040c1040183c00400c040ba00b503401030051810001541d5000b111900d01003801104040c002c91070650240d0701c58505140c807600c550b1039405049a00d440c0140c884c0d544440d09884ea032889507503115090400520940003040e01c038080f40f4040760100001844902401800070b4104003513182c1000300c440d2403011050004040c0302101080c0c070240f11540c1c20905180002c40c5240c0c0036600003c0208414010f0080c81259107a06030806948007412100000003804904200700d055014201d0118210b0190b002d0764100001c900000540c3d0741d401d01103100203503444082c0507 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 885786510 1250 885785260 885785267
    0x9040f14060c0a0e060702040606050301030501110306060d23090708070b070201170703020706090602090102060f04020112090c09020a0f090906030f35041503021204030c0807060203090607 83
    0x1503280c841202801403442c05580c21500360040b0000300e420b014a0b030b0300d15184d55031904121600281d00400400c02c09031100001002e43c1c20902084507103601e010f03c042550f8041c170040e20720841004080c14a06485213004e64060203010503130704510103a07440745555080740c43c00500d110f508950020034100340b5040401d440d02407194800101008100201e00160343e1280c40c1081c03102204074060702d1a169241d04070020f01c502d46011380010f280011440c1000100c0c0c0080a901000b41e007110710b1500c40c8102c90b4004074054070000d010840240c00201c1001160b088005d406010b04610180103030f8030042d090985e40010045000142802c0c01d0040f0a6000800ca9024010001d02040058199581c480c0c1003440da140103004002c1c5082c42003800c44800c0111198070720240360301c21504401c07584480007034200d0b0080c1318a0458100c0868100d5200e40700355440040d1000035510140c80b941c405441100b490b900948503404100103220103c0e043d070000b180a0800310000f481c407403620301b4004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 885787760 1250 885786510 885786533
    0xb041506030c12050603030901030504170705030a080105092e120b010306060f062f030a08010602190209013b04020a0f0b0d0e07230a0f0b0301140102030909040f 71
    0x241e41440c50701c001c5c4403041e14000140d550710365003030800284030b84a82c103181130383d42c1c10005c0e210704004000071950200100440a094007401c0303a1140720150f41c0713690411a032000c08442d10180202484803240800c4406541c1160080c0c00c5a4921074103a2140c00410707042500c1c41080d25000e054100401c00c0100f2403003240e0003840ca60704041c0140e820b00c0001091030941524020705203928020384800404c1c0d0000180000122104807a6a000003850242622100348504e40250084c1c000c80109a0519020034401b0341d0700508012540e030902c00c04108608107840780709815001c2d6040c000c8500d13402a819000f0600340c5813007440714030385803040241090765500701184151414004204882d0401c094a61507904d0440102d0610a00d10b0a08d00d0051230f44d1101d07900203042280383d51290300920030a1021034043e2240804543c4842d90880801b000f4031681000c0d0500300010800343e4410b04541c0e91003001441921316240003400015150901940c0540b0b15800745001101000304090b40c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 885789010 1250 885787760 885787787
    0xe06060411090d0305181f030b0301060e0109050f06030c0d02130f0203100e090a0f02280b040521120d15060801180903081801110a0f1403090c040b041506030c 70
    0x10140680c004007822802c80b06499005002e05448842710349441d6000e4100c003010302401e0ba9014495a03640000601901040e030340c1c10090001d0034003144007410301203510140b502c400b4000e4516012903900b031001810361480da10884070f40c4c644041010440900085004045168000c8002d508080070911805c4c0090055012580107001060014890303e040f1401a070301181d114084900c024985000030100c24103171803000352841c030003142000f0030502078801c0e40c200b0b0351251002e11003d03500c000c6c0c815840b00091019480302e408082072010120060a080f03c0e01c8202140d8409541d21f507000b0f0341c1c400e402030000300e821080140082c4120b0942ca01200b50403071400e108042694502a10300c40c40501a00348035603404030b00359090f04094000d849591a40206283e84801c42c0000828800354082c56100117003268044000d000d114000703903030090000f0809014203145200400004008504005810a440301004a140c0f1002141d40c0010400f540b00801c69400d001c074002c0401489030321 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 885790260 1250 885789010 885789019
    0x90209031204120818091f0b12011e0909060903030f05330d1a0f191e020304060b0a0f06090315090c081006090e06060411090d030518 59
    0x3080080d24002000c00d044543c0056019680c3d01d2100200300c08400000710040c0c214130800244600322a9005c0a90a840c80703041031111005e440350000c1c40c143c409c24240514404280d0300510400c02141450b0080205603192040c4e4540d0720610f09098a08483d400d54086607103850f40018103800d03000708500300da9072800412051501c060074030691148503e016502c0802000405085202c00c4201e0b600044000c18400c3c0e8a50b0b41c0c9030000c90509114092010b03120020b0109070001d02410a4600950381c0381e008400c0e207280f200000c0001c040020080b81c45c003410804125507201c852000710302981c018600800c0b01c2e0425010320a542107039a001100a000c042d0080103407a90001c3c450b000e42e58040c2c4d02561802c400075804001c3d01341c0601c080c04264500a002810040025110f10030003500c40701805010394828030f0341d0841d10110414181c030f030030020008003103103015400440b4242c9403034409070910f040d800125a02040804040b8082000090103000c3c5068075031200480d01c81c03c0700d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 885791366 1106 885790260 885790267
    0x80f0708040f06030c05190905040c0806010e030d0e0d062315040501210c15030213120c1814040b0f18030f07080d02040902090312 58
    0xc0344200710111000000f8009020380600c0c1010001520340740d0a20502c040010644016883c00b941049145100441c1d00da03039a01c50515822969a221411860000c0001d441001b00c0d032856071003688208600007078507034803c4000c0711104040c1c4180298003001c1ca01003000d8036901c440801d000c03080204140ca18100050410b01c82c02d604130804221122807010300080314800e01582c14085003039804259041c0d0001c0c00e29811034820002e01030900d55a9500501342407406105200094002604c507041071504104600508624101512003119545d18880321100038441d0388000c5210003c0043c0d04800c940c44001c4a400c945a507100c140b42510f03002145c140100c91011004140c07002084518020030a44032416000e44000c41ca801e2010840a03055004190103d580ca0410400010020400d002030401409522405a1640401c000701402c000030391b0f90b221201c010a2 = true := by decide +kernel

theorem cover : BRFrame.Cov 885611510 885791366 := by
  have h0 := BRFrame.cov_init 885611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 885611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 885611510 ≤ n) (h2 : n < 885791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
