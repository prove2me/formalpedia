-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2270
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:11:53.85183+00:00
-- url     : https://prove2.me/submissions/e2ba220b-04a6-455b-9b14-e22953d01351

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 408093525 ≤ n < 408273381 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 408094775 1250 408093525 408093529
    0xc040b060f13030624060212040e1f030309031208040209060127091d340306050708010302090a0c0f050a02010209041a15030919050c090c03010f0603051b09 69
    0x203049a202410302824018800c1c02e00715480b2807480324041e410001c090103686d914080c0e844000040c041861004103200411200303503504500382d03000c0008100c01000090180000c0f42180007904243e00048a40c0810f20801c03c210b0892a04400f031420b12150702d01d4170340d0004409a0005005904002c20f201c6008100460049042d1980c100c039044842415241d8400b00014a060340340c0e00b0600b00255140803440602041043c500e400132442c09500003915819840800c5086881c030410440551002000c2845403103654000d500540e00c41405514500403c880c42c41e0180c00b04811038600050388442a401c0000c0d4029864641015030302c600345441c00340e00a0181105480d08641041c96081184042441e200340f00213080716404030079200401141a035002c103ca80000300c1d03100d21040d912a0154604007401140310f0300403185c1c504100c601003074007400107076005e8694090100c014400a10134102402c0644410f180800c29072070000c564004c500d80202d6500707002040050001616 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 408096025 1250 408094775 408094807
    0x7030507120f0f1113050906150604080303160e03010e0d08280603060e06040b070c02040e100504060b010c02060d09050f070b030f2404051f0803040302030c040b060f 73
    0x55000030010000208505004e1520303040307940120b10a844298851517080d00603c9200d000c2c02d0342c0c5000b010710741c1d20000842c1c1903440a81105603c80800c0c000007900c2d0808100444c80303084602d8603a03c01c0340d100d84003c0c0000c03c44110951099041c02032503406034800240700000004a8600040d450710b1710701084111251650185c1180481a8241909070401c5c0d004401160300c6148104040410b003244562524820b030b4004003019200c80108000c00d105800348040caa000410010b06440030704502840c00350710240300c800480d101c00c20881400f644e4030901d00b544000b820000640040b950010782280700d0b01c11001d884c95683c24002d8140601080070140d03010841c421140425217510b610007140d0012100760f105a800200080d1020041d124260046903d9003032034420006100b0800010700001803103c49203e8103c1e000590030120b140340311b001040800040e60f078840c11030050604000040210034003890902a55160300d80756442180c0800b1451810301d901d41d440e454005100c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 408097275 1250 408096025 408096053
    0xe0705040509040b2203020f0d0c05031209160305010b130c020c13061509140a0b0a03020304052a0102160b03041707050a06050a0f050603060a0b0409151407020703050712 75
    0x50769464030700f4000309500014042d0440500b8009c4a00b619040380089a02c050501001402900240008400c62045001898000024500765003441d500e10030510f91314000da61083d145a034448680c0f138030f10309042d2045858000140c0e01401504440100139507584911180a070091701407480012003804154800307009070008001079103010320100402800146640259401c600d03d0051000540c5000b01e211030803160040703800c0b8285049a81c00794000e400003001580e840c01407060348582801d411a07158101e03110411480c02641030040028600b00c840c0410011090304210f0900000314108103807030303010364802241c000c01e42c540e20840c0c0880c026030000802e50701ca0303c02001c082110b075400191240445140420003004100b0862042c0c170816542240c0540004000c41e1600d0280d8000705601d40c000303030012034204620b0780c07800035034414601c401c0101a550350004414030b000d242065004085403004221306401e6898594641d070703061281d1444480d1050340b89080088090f06401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 408098525 1250 408097275 408097321
    0xf3908130510050108061008070609060c14070806150a030b040b040804170715030516030b040207020603041b050109060203030619080105042a060c02060d06120c0e0705040509040b 79
    0x40b595a448640b20350310002602c41c9030316104d50b02c7c0c0124620600249981c03c82d030075a51101c840c146400d605032200b00c28220150b8501c00045200542c3d040300f004200700400744040100707114a04a81d80c16418003406142c1441012542c0b001c0001c0344516039826003050300480400d0342d1b42c6032841c02160b50b10032a032024085a01410a0704a0000c02080f400119141d80038002403d08102508038100c400442d00400d500104000300e14003640309511040c55901d0203040145021040d400040503508211002c90b01200034402045585640988280042400382030009502d4184170010b9242c0c000104124000c112210800c00502442d6507004002e1030230300d008018500b080d09001162801c5040300014410020351400340c02c41c2042c50310700454011b40d44a0328091380c0b580c00c200c0c09034030401a1741c9055403030300700c0414221150702400c012103202d0700d10943d01d41d1505020b030740000002030050081c0103052100f008541c0310144282d6215600411052840c1e80d01e603030350111070340520f103195 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 408099775 1250 408098525 408098531
    0x40314031207180614160201030608010e07090f140c130306050c27210f06010608040614040b070e150d02120f1006050d0f3908130510 59
    0x48041c0d04a40190115041020550140b44c0c54502c16114801e000b4040002c1c04000c20501c80740321440104007804e644145000f0402c41e50b1072481e00d088d59044a240d24058000c2202007003281c04500c18034241e191700031010b01070101a00e070404e01040300200b00c41c0c4104000a8061310300c046100075800a180e01c0a020002030411410701c080301e403c5000c0510012451550300381c418110042c16841151000740442c20b8041007402c4500000d030283c0890380a4481c041d0705c0440d005c0d084c0300b00d80c0070b070441e5500d2604a1500e820000159801000c698030040b041c10107100204a0880b8040c0d031216081c10f058542c044480003040240680c58807490181c01c0100f0350703918400503a00145040000900000b170f2075212209d8036100c02c0d805884a1400c2503007aa82081128001d1018111071203204800190700103800b02d0000555445043c0e8442e0507114080d0602c540204101040c079008403107194204d1070120600c007803c507460103031030060b41d402c400d030a000c10030208114600300103a10003802c0c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 408101025 1250 408099775 408099781
    0x510080a0c030522060905010e010e1507350403080a0c0305091c050c0f0106050103060b03070e041806110304111005181521011a0403140312 62
    0x14200481510340c100100e08001a02080c42d00c640607140c00b407454001030740449403980c2d4080305180c000c01e40440d0304645824005001c1a0207100e684184100030001040131004046601c0c01d092035005c2504210f03402c03a09009030300307a021b24590190f0f084540090b40d0300003070f400361925031041d014050418010341c80401c01017552180341da81c080c0e12024414818014074172401c1c1d065680c00c40c0c020900d50702003508560141e03031408411503d800b00e404c0c024075240001c840b06041010348c00040d0805e0b9102d50f070070004c55030303d4410300d80181034101c002030a5003006000102000c10401d1010b1156489a07042c00160315540f09400c030300e81d4808001c014510880080440c5900111f900b03071001c0320800d8441c43d5070f0411206c00d81c90080350342d941ca40fa04d00c00307240d5108084201c0c500150001d030001c2c0003d50107400500101481e00e031440c00401030550b42d110f80d412030401600315000504901050040c404501020b6400762507100c000c400303800c00c2030340c0114614000e003480c8250f0704480d4424 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 408102275 1250 408101025 408101027
    0x22a0907030c110309240909100302090121060e070510030603060b03030f0703050304051501030320010c170a0f02131401030207030c060b030717030c0601050a03110603040c0510 78
    0x900e01d0b403032544404120300c42c824081070301c03030203505200d07034000d42519800c0204140e08002030020408200140e803c1504020103e099000121075512800030000c0e0103005502c0c3c804180c034010080780080d41c11220b10300703061079411847c130a401040c0740d0700ca101d0b1000070300040c04168003418010300410700444035050010b0107000d03148400e480b4940381c000000c0f242c1c10044202c031003184a001d030085c17038001c0e9950b044840303610062040c1c03454020141120504000023208900944c000d648c1c0280110101c90f0b80b14024150784815503007070380741c1450801a81e0f001005030300b00c9440c0c030503020501c1e92070040d01c00143c0003845110001c0c51002030358210b4074032980c40400642c0c0b11203450382da0301c0c900300d40150220f11a030355000d80880c03a0700810100258968001130030310031010b07094130031040e564450507511000b4a6070502e030703d40000c5003001c4a103404002c1d490040c00201c80c0107034168034544407140d42c0c0608038000d6020740d60001c000360500106d0b4803410010400039000b40035500301800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 408103525 1250 408102275 408102281
    0x18010f032702040e072601020405090a0c0806010905310509030c16050d02040b010203070b160f0206011d22060902040f0e07090b1203120403090e07022a090703 70
    0x741c201c0c4a01d01d060309404040c03000113865002e9039040e5401c00803c081c03200ba20110f1200c5170501c5c4050b507408000110340780c0c4031b007903c050086a4880c2c02181c080494000034040050051000781000591001080355a4031440c8001d181040d520b000801080c41201002c000310160304c892507110304000034000026030000040095080110654800181ca52500c1e400322903035100d5164480f4a20307120f08003618181d4803c03002e9500500460385031191070303030354261600c5045600760003150306080d8215100c1d4000c017002081d68202e2024008039810004002c1c80440e18030208044651034200007085054281105030b042018081100141d1038246400b90180000d140304074080ca04000b0588040341803802105080507030400500303009400c0c006040014140101e130964842032055081d44001000d1000b0000c075042004001c12628150a0140c00382031558401e0703c0d1100c400c1700b0008803c1e40803503076081c0381d00d01071240340c501c4007000f143c0c1d0b0315a0030355007520744d11501c1c480a00c0036a03034050b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 408104775 1250 408103525 408103601
    0xf070602070e01180b0109031e02030d0306031a040f021305011d01050117090705150d0501080c030a06050402011709060601110304050a05150c010c0f02100218010f03 73
    0x54201c8048545420003801d036200203109101400b00031030051000242250460743c003038001850400002540c0e41c0b0764415200c0020710200048541c0e078581c005605041c07018000d40b808904007442113a19541c1c5820802d40900b4114020140c180c02240c00c11115103429901c03150001c3c8800d0ba04035800d0100303402030200f0301c2a802000702d921520b002030340c0300c410918100c4a0513198000b8540e910415031654041c010300d805003d0291080c04640c41d515015030b000f2070165012140d40ba010300f0b035451002c03100180c111300b0b0958041c43c400703851035800080c0c1e040401d520240105170f41c0c0362032006071008420f6264400113542d0000030441c000703500003441d5104000907038985442807041d0440c103461b84220301031781d40c00c07020002091025040c0000020700a0030b00c1c01c0a00e01e410742c2e034607042e4210768848000600103902c0d51000c1d00d80690401c1045031003a4242821481d003074010b110b20b0b80c00d510404815040c080780380c034100c0c0014004e40c04100506a00d007044a110300075a084070500600b09 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 408106025 1250 408104775 408104777
    0x60b0310063605060a0207050109231c08160204141014012a0201170c07141905010501080f03040b12040c0f080307020a080d09030b180f0706 62
    0x100c00011818481d03580015402c140d01c808608500721a24800b003031400d14038030408420700b40480002c00c1e07210040100310342840c507406015490304040005004801c3c2d07600460341407a0201c0c0c50346501c0540c140340c01e4a071200700c50046013003090001496915214100241072030704080b60311002994145513110300a071084030208400300813018040e0003200f0544140701e5404d9140001c0c08901c81c8098200848401410405040c10500601c40700c0c0d2100c104500c1001060710841c40c00b1542c2004011000140c0e1402607111460301101c1102ca9001d06000038107482868100200c10480600101403107075100d0200c8100c00c0280d050071400303040700b8881d4841e584190040c81e04501004020741c1c090794100f200da146800d19200404200f404041d106841030007051400158040004114100070500440910713101c448130300402110800c26408800c0d00d1700712012101c0f40350b500254407015240c0c0441c2c82c8a40c0e03240e01060f090403208001c0340340610b2060800d10039062800181200c216406 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 408107275 1250 408106025 408106051
    0x1030b16110606010807090503070305030703030606080c0901120b09090106030c14010203220e090c1003020c0303070305071b0507030b150a030f0602211008011b0503040213060b03 79
    0xc00c80301121261514071a5001503000707074021480540c840c80c44260090000e1400c1d55070541c40d00e001900b030400607402242d0603032000640500300354050040030000d0185d41000c1995140c0382146091030b22800c11458104039680341020141c04c866404901a0103003d01040d5052900a2140e0b000300114081681d0300f0001d28000200000e2180c4040220780c4181c1c061400d00200000e802d03100d03500c011901c40d21032500d0402007805422401c04611901503079005002803041041880344102e03900000710101401044904041c110000449401c07030924038000072581d6072464200c880d1483e10747e040d594800030440d10020f1020004122050f6405980d03080b126445100f958046541d40c64100c540241c4402d000300042010050001c81640c0200070161034001c0c80c00d81e0031910720703030340101c080700c6d40054040c04a461043c3c1918406410020b000700807410907182410070740c04812008100300300c0004002011521014002048440300d26018008191103429220a90704216500307040c80314 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 408108525 1250 408107275 408107311
    0xb0c07080309130e0109051204061e0c08030a0e100906060909020a0312020c06120f1b0417070b0a080402130b01090e04081207180603110a03020a020f01020301030b 72
    0x700880b10304001c0100b2850b40c528811949001410700e243d164449550f0769103c4a01040c414000503c0c505a0110101c6e5902c0c00c100b800303040b08002000c103e1036002d0038010205000d03000f0031b0718200241c021079081c2d01d0303607100142100541301c10042602240a145550403180403035400c08030050348501030030310040d521007800c0c0044883e0640d01950148822404001007400a5182c902c0840c00d441078914005a01d004143c4c036503c40c1490720703507244400040003c20100e40c0e40d4581c1090494503c460f0544090a44004a008a003e40030710030f8050880510b1114040000c1d200801c0211803042e195010508007070412101120140e0040d5024960b6161080b0a449840100b4505071a56001582004000d80d0f01540082c8222050304042000c01c04850311855494440c02040e61891414450a08800c5c95081c031980a14140350804c01d11000058106040c1c0d6007102c0b152030700588900308054202e03d445403080068840d5480000080244220502010300c100d1141d8003001c00b100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 408109775 1250 408108525 408108539
    0x111909060611030702060a020304030c030c0e06012123191812120207050f01091407030b0105100504030804060509180906130c090c030906050a090c0b0d0f02040b0c07 73
    0xb908540342d485250000c000c50401407030b00c41c001d802c0c8070f0183d20440317080545a544640305140701303400c103540e47c045121040080d800307002011782d4408020302e00200b6581150b064010414103003070104441030341300d14100c0c0f414001c90103513402d40080c05080221609084244488172844400504035103402e00340c01c03040c516200c044816000703500401e0045000c1d40300c1c0c8101c81e10021080c8038a1226002c010b4840840c030104491180010700310300016054425191841d084403100d07500d00c510350410401040443c4a000040f41102d409a40c0c9403800b0700c28400c1110a8811600002c008007804100819041e521030080c103020b090558000c0c02d0200d0080c2021490710084894440c01d51188001840c0c22403846800201103104d01d86410120340c45807095003d5640812049000a42c0d03100c0740410700655008068001e00204002c02c615641c40d103030402800746600480c80180c40000c0c8284405611350b01c5800141200705086480716101c05008002d50f103c902e803400148219075021481c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 408111025 1250 408109775 408109787
    0x1d12010f02180f150a030f24090b030307060209030109060501031a01081204090b01030b040501060c0b011202100f020309090f01060807090e01061103070510021c0606080705071119090606 82
    0x1010000c0010101d400081c04c3c4020903403040c281501050f8488081140142d814051007041989852510701100c408090095041c4102da201412003800d04502000c50b4401104558050b6040070b00581e84a0030034001c2405003101003001018203140c0f20000003808040c10a0071400306440c10403120f07c0e60703940c203016a10254542c3c8400f01c114104410021125550b00003440583c06040c04140e212494000408444090740800041681c1804075410030410301c8034a0301510303454a0341510383c6095004256048650303100501403004080c03a40078124001c0040d51600c43e030042041085140810f0b04042e142028801c04c0c0114904c170700401d00160040a282c01070b544800c1d20400160b00c3c004088a24501c4040070010740d02040005a011420034844021105e0024401580d01d03e86119100844141c04018000c500d02d007003001d0005a600050b031680140d005c0c600107440b003466081843c04040c03081c485075440300641452030888082980030a08441741d20a040298075a03d140503504 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 408112275 1250 408111025 408111049
    0x3060509060a02070b070c150603060209031e0d0e01050408010903020304050f0d350408010501081504053307121508060c0a11060108100b060a1d12010f0218 69
    0xc4080c680e400103440074400c1318144104c901a88c3d16a0013113a104910b00704460300d40e0000c0d43d01940000382c000260408000140c00c0f8500100c80e00002e100ca880c0036904d54045000c3d46040240302c01105096a100314299000f80140078001c00c1081d10b9490040d5896205126160103014800310840403850030700750040e0800d0704038462118860342d901d40322022140241038041d400601d20410131681010001800c090481c0500010380b83d41400b82036480e0255000c8400c49440780ca8040000040c07020806082212401102a2140207803003034121150896a18403800c032071351801000501a0300610006070030204403000c0001c100440440c0070b10070f40e42e0241440c1c6a0150000c2004007038100c00401c1d000c00c2614001d00008582d0782c90710b003854002e0780043c0890f84003003000d030061000340c42078030b040c1001290346034500380340b640d8041c202c200307903012051b00c442a10030310500d6038035000000c0b015444610001c020080c141100c920003500550000d50000c4d0740c50309040704908044034207002c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 408113525 1250 408112275 408112283
    0x90906050307320a0b0702030c01050f072a03060905060c03042a051807142b0605040603080a090806010f06110a02060a12050f130b1b0f0d05060d2307030c03060509060a0207 76
    0x301d400155144d50001c8080951824403c4c13b02c400c01071038038103a40000d0006036200301c402141540c8282412482c001c0701403d00507288808009000000f40801030f032280102c121045141a41c9606007440414000c590142e50020600e58207082361400001c21307140b084210340c48045212260103c1803070140900440c03658425141d20a42020458000000700484901407002c503103180c43d800403806848460b40704841a442c040b412140036030b0000130990141c000368008000175850a903c09504034658440c00e000c2c4022406030407100340d420300248580076006840d942c1c1e070b451200d90007041c940d000e540b071124180ca41008503410090810140d4090020061102d075050707825211314804481c0903000c816021800f10034009541c0d00c41010b00800d0b00030004180d11210051045015a900100002d1040c4500810b020010700c941a0001e0301c00a2000800c0b00040001100c0f850039040782c201400e0040d070f80740000100001900703c0c038030499501054031760645404400744242d0260381c0c8010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 408114775 1250 408113525 408113527
    0x180a11040b0d06060312140315010f03020705010501060225030221070e0a05060a050f0a0306110f03010b0d1404030e090c0f0703090906050307320a0b0702030c01050f 73
    0x14851415410109120760000c16408280320580e0b98402111030703a5004551160071141180102c03500301104800d0300c0c001c10183c0f491071900264840846107c00401414004602c80030394245110754150f072003c5134031130020002e43d43c4a000281d9150f0f10401c03500311085566001c240030004210445085a5015102c0b0b01c0da801302c140340d0300c1500f04080c07502e6154810304070b0018140c00f11180e16400354a0301d24000615081010030700c5000c0f188d540000d40142848a00496507440e04401801204d0300a0400141400241a0303072400f441218000491802c000c400400c507000c025000b00314a048603881084041c0d20340603c10101c00b003c484c058042403085540000c80e0902080c40b03030f07200704650503241c507003005694080065003007840198001254058280020301d1584034103800750004070000c2000614002c010380d444940b42115070b0507460400310001c034040b621251030b407052500400402c3c01c40c0e141e0308071114a41144100b81d1191041c004c1c82c40065000303000b203c12011000e5002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 408116025 1250 408114775 408114803
    0xc06120c09060c0d030614090f19020904090305090a080c0d03031806050c09030708120a03090c170312060d0215130306061806140105040e1f0e180a 65
    0x34000c580180503029040300741003052003188071061102c0c0c04401070989000440d2402c03c0000114802035019440c05401e5000a220200144195003a0301280791441c150304100084001c03030181c0100740074640c2040c10440f900013010b070004080d00b1000b40c25150480075030703036030a0850b80c1c600c0040d613103c0c1c01100202c80d05c0042407103074122001040402808420320315172a0790f070104448080342c2a00c15428082000404d924080c85200c004002d80701c020326500c0c9a41500d040381c3e105092041c1c1c180b50b41c505009007040030462111000304880704030240e041040250300f5846e81e0040409480140034900000d40500e4810000c0ca00d594015052012003488c01801c5010340d40300d06c1301c0401d10001041d0000010b940c60080310040d000c01404c00000b1b248026110083d00d1240d00702441800351114800c50b03d9a04c4001c0c1c4044403000ca1a8032601c1d2111801c00714202154a40f00c40700d41c051520205900c130303c0c0086140100640354208003111000d120140d210f01140784001c001402c19450 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 408117275 1250 408116025 408116041
    0x101a030a090b070908010c11071202040b0907033602010c03110d0e0a0f03080717160b0f09060907030b190f05010528060309030311130302030c0612 65
    0x2640d404400d45400280a801e50380300d40100140807100600040d060b42424880e02200f030055400c0c80d0300e5801c001c0700b4040565036450b21342450b0700640c2d200d08140035942083d0340d1550415151104054071055003401c2c05940203000e000388201c2c0f60589842c0c004c07005c00d801090070810200c11031760344100c00403000f941c5c0116007030040e20406400b000649500e10080080610669000c60010340f5003143c1050b0700750500c049001e860b4090207000c0d084500810100745000121202c141d440741d42006202c1000280f15054050702c050000050006c00d021002c10850f01d0300039024032109045a43c1541e0b880c404940e840300704454080c0c15410080040000401201602e40c1280300b0800c45c1c8001140c10414001f110703c804240e4442c6a00c600c010015810010b1405120949400f550310360050300c8203850041c07420070320071181010303995120b030001c3c14404c0e8014a0700c0020b10460650780c1d15912645080350b0000c2c08140d01c40c0c01004c28240041c503016040307850f44038000e041010706030b80c0c01d14 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 408118525 1250 408117275 408117277
    0x503030112021201051302120d0801050402160503030a0203090106090b0f09090f0d05040e01080a0201020d0c0f08120f0601081521010e0f060c0f0904050a0f0f0b09101a 74
    0x203040360401c010b03910380550070f9001c1c003409111303004002000d81043c0c841d00402800398000d28100340903400204250300340303c0c0d0041445055520550f00569204c60345441011544091f0f07030003902901012051000c0e199541e0010340c00f5a490000038001682c95509000407603a0199180f540002020400300c00c0c1e040070042107a0100502c819104400c03000440c0340e0a12203044010000a1030018041c032000f0101ba002c18003422103040101002c00141d40041e503100801c502c40303c188203400d5a03080c104091180402400c03030f84035000c1a11038092007040044400280c2d241c1145e038007100700040855200f00242071240050070500300c102030442c0d0900c6070b00b010030043d001901c510202c0300381d80b00c4400d0040140341c0480300000c1c41000e03840107106d42804c1c1d015052000c40d8104009401c0c1c201051025203402d506e08503000201612003a440310000c1180e0642d2000050a046c1408080f0712035038484072004505449620b4903503240740010807a10480c2c02200108240004002800b0350828 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 408119775 1250 408118525 408118559
    0xa050d020a090c0309030909051501051c060b0403120e1c08070206160b0114150c0f070603051905010f060509060c0a0c0f06050a0815060f1306180305030301 69
    0xd00210812a110202c0d4426503a19403d0040440e0729003038090209540600e13040c0042080041c10845400c0414809030034164220364079040080200b07205240701010201c052140346102c2d070030019a680c074801c007086074229100a031810f892400d50408414020124191200c5006045500c24103028503007040200c60701c602540c5d140c1092001c0001a240c00e002806048910404109000c1c92030cc1d0001c401001600000442c5010b010360070056100d6540c04160728080d036118a803211051140a49812404847c03196607100780600090f485e5016800a03000c5c001c2d80c44541804000345403160282d64080c8180246c1c40004d4404110321489400030700701a0a0042c98145808030940c1054a00401c4100079554400c1e80c00082100c110101404030003400c660030658149400580d01a10301c800081c24140403a0b400742500c01c0701d6030741008a4a850b00070440407900c40702c0c0c1000f8084040818064140410070510014075200d1512081e801200d43c030200444ca13582c00c14041c40d003994528 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 408121025 1250 408119775 408119779
    0x21030610030c0e030610080f03251e060f0606180b160b09100b04111902160b0408010f0b130b01140a05071b08070605030603210301031109060a050d02 66
    0x701e0f054149036505000542c01405001c4180e0b0b90b850910b01082d090080100411880760310400845205540407000906044403180c04040d150140b41485c0440c491805c1c00c1340f5a01f2a248504010052680e1207941d402215013010401244c860006540480508000c074044403028402000000680700040c00c10036030144030101c1c145031558402c01210029901c10203940c121240d0015103045c01d100707021102a04441c10b0240710100d483d10460381c45822100d22020400402c803941c003e0081101c0d440740015a035015509541d500000110354215015a9440b5400c00c0f2001004004a02801100c024024006001044112035000090491840c014148105c2d101000c5401d030b100300142c4500c46051301c5e0541e842c00c1500e070404420001581c50703207180001410900200c1c030300041c554207450090411594a4840170006443d0050010f00310442d0b20500c00000b1402440d0009141201d1062a1415000859030204100c1c40070494200d9003068400c10100001d02d81410100501800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 408122275 1250 408121025 408121037
    0xa0b0408040b07052a0913050106030210023003240a0303080430050d0f02040303110d0206010303020d050d0b0306040605061512010302040c02031b21030610030c 71
    0x15030140c02c10903030421007081d90941c001c090756201c403203103903403500c520007480c01a000d005035031610000350202805130000d070b604000b81c011071040200942c0108040d5130010440e107107613144010002d583c3c0d5884148400c441040c1103c614030600c011406d40109140d905445045030b85114220f0009042d001c001a0394a00f0b094001109840f8903003880d0285000c1d0355074500d28503040c20078031840c6803d10124825041e4408001d035030034103202c4801803414494075001d650f40904c4400e901c00317825504818007109100090003c10160040400d030105041401982d20009980320140c0e21110309201c0a8007503004990141300d42e034070501c020810781c1071020000a985a55402003483c0c1182203408031015543c52051011030b140c130700a64404010380c113240f0380c0303802040c031100d00c0004410b1000902464842621001c0a030090054965400c40304607811012650900d140d6910007010a2020701702c0006074400008c01350000031240700340c0014001c00d105901c611822801410092124070400071 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 408123525 1250 408122275 408122279
    0x40c08040b040204270501050a0e1b01080604020702040f050f06120606012d201605191503020a0f03020c1f0e0f0c0a2c1308030702011a120a0b040804 66
    0xb811017203c210702e008000000302031030141114002c6900c85241412a54000c43c0080c1c02c503482c88c0311600c4c1c1110b003880c041d501a219940800c019004064009500030300300315182c010800c1d01d502c0148180c4402c00c410016480d020148400e0740035030ba4200300190030107400038016500880c0920701c4422884141803d1545c40b0118105411174002e44c0000110f241c0e0300e03000d1003010a151910680c0b0408090b05065810b031010052610451040034040d41c1c3c12918074543c0b21514100c070f00102007075a090590000c640c0401002940490150302c08038065040c071003000e41c4070748243c44518100d200149000390501c802a0202500c0c0070900d91816101e9001c62004038003404090300550b6400028a0404a00b6080055a0059821901c0c604c0030001a4441e00c0013085091460b40d83c101e5a8480581c0720b104880d089030500890181c00c400000090050a540c154000c203100e10010722030180e000c060608102c5454025242030029a018540b01004130350741a280c190428400d20b0300303a1503c0c1d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 408124775 1250 408123525 408123581
    0xb010305190c1e0203030702010c0e03030406080603030c011d070e0f0a0b13240b1312080f030f0109180201050f090d05010606080103050609030c0a060e0c09010311040c08040b040204 80
    0x11883c0c0c40c0540051308040244901c4503024092004441c0701418080d0081c001312000c6503890045110340c0b010000100082001d94400b4000c840390345041d20000c4c040e040014401c0469220821103503001d501c00d01000040b088071050200e0b028004031100d0f95425114420807a01400d54940050743c005903228084490306031a00c90b0020720700600103030418000b94059503440c0704038a07500203c0307518020030090004c00325500c01074080e03641c00380300300002403d05e0074851078600882480569116001050042d0740f995200d0003170494070504000c0c4440703030344030400060500440000034042502440100f1036400c02c0b401900d08000050800d45150525444203070a60351315900c08070206a09400500c10b01606101030760b13020746d148004500e003580350300440d55502c0420401400d0749644464901c070220b42030042800e030000040c10f100582d40c490038100080d0004148003441035140800d800041c2d030068042511070f60f00b042100045540c0c640078000505640071a608901910140800c41e00c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 408126025 1250 408124775 408124817
    0xc0a1413140a060518070f1412060901091406011d04020d090b09070f03080313060e2d1213030c061d0f10181206020d0b010305190c 58
    0x40342038454000907909107109040e00b114003c4d000303103004131202c490344040a030b04000f1858100120f481c120079040003950b8206ca004510b20050f002c04000082c4104034403642000c600d00660080340c0341d01650766034483c00c1003107841d0000e500340d5043c03080c0c002440b00d6005485403002c0440c105103400300c419101c0006012a030001c19a030240b01e139520308000c05d01c03840070702d003550210b00d00000340446030900e5082c081a80300c920005013451000030001d4520129032040c94a5a0f500460500000810103807a54449081c1c41c1103441c0d0a511036910420300c80031035010011052924080c0002c1080c0c0500300481e9070200d00350a2140c2c1908400100040c884403940000308865554824004641120800081914540b540c401c10084e9004240b41d5100ca50040300f842c01420540c0b05500c03502580d4081c00d0065000f034401e5035900c24207000303001a94006044401d2300c580b041098100010066007201d8059801050405804070900841e004c99485070003107800c9420b0081700d40404000100342 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 408127275 1250 408126025 408126041
    0xb0412060f0f02160c0b130909020625030806030127020604030c06090f0503030307050904020c0a02040e0c01080a02032a1204151805060c1614030307080106020c0a1413 74
    0x1340c030305020440002e204040e9074180161860b004214603004500044881c103c006024000603996916403280456880030101c550310380c50301d1582000118420401001001450030642c04140c424002415502d4103110304e0b14245c5025100a01d25540d2a001120200b0b10325003c1b80c02c4a0100000b00201d0003028031070340145101d986094034541001031a40c070040311a0b02c03441c040d44c01807007400b20107600f20303059600000f4261070058846501801c201d2a0030130581000c1d4220b072a00d03450150140000c601d02c80801800c1e2545107064540740160012444120b42c0d4004660391007504010102c038910b20510040030700d101c5c081c24661001c00e041c00144040e202268010540c0400c0490a0740d64020700ba151208240c1c102001c55440d20f449883d503a00405e80400c2c18030005540c0451b00d072844100400f039412a1452901e4200043c1b0729070303a58070980703803400130500c440c0c000141d003880002c11035400321003e00700c515510701d054400c0c550340f804090f450b175221021081d1000d06004034414201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 408128525 1250 408127275 408127297
    0x51503061b131e0b0403020f04020d1d010e010c0c020a0e250f0e0108090d1b0c090905060f1006050d1e142202090406091a070206010b0412060f0f02 65
    0x2400b83c294140285158680c40340c44240c00c1400200096038132100d5802c00c03d50f056402680c0c0e0031390340300000f00802d412050403084091911268004403415030080400f00d2410000308100030804805560000306244000e5021040701c20910034200b08683c01500400350792240160700c40c090030180300030b82d203018010001481c40034008403490303030004900c042e0b03020070f09001c0c0503820704101c090388400040d0f130050148400c503041a8103400d443c4100b801c50036003041403142980d450320f500c030024120f4030509841da84107200c08502c441081c40700160258000b03450713141d000b80c03802c403041e80c050300314128201ca40c83e03843d07a495002c41e2a00c10f000301c140544a00006480d0406a282651804081c00d003038160003014440b9040d0082d007195030004507070129100d404c1a80c892070480c001c2c080181004049044540311000c60300c10400c0220f0041100e5000d03107400fa07886080f045141d0045114144103007229100c940045803150b84070f500c4540041c00042145014281140c050364460001c2031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 408129775 1250 408128525 408128549
    0x2060a180e0708100e060108040203100609021e160b0c04030b07170f070e010c1104061205010e0c0108040b1005030706200c030706050a091a070501051503061b13 71
    0x2118003a40003c0f5140d0041c0c54103a0340c40c0690a00805042d80440104160306029048000c0380640d0ba0800c4002c041c2d820068040c0315503034a5003803c00186d00002c031985181200700780480b030003402100554032814000902e4090710720542e00c41c0c40e02100c000c0c2428205480030032020002c2204c21907003900c40c40d06038460381d500140d80d101075095000014000440c030340c155018400403503846000c841d6258002d1803c1c014610036070500c081c41c080c040011540c8a441c0c13113000251082c1071000c00f0b030f0190060008101c0c1c031643c40001d6850b449002d040380c1c00039024000040000e5125803801d90040083c1c20582580c54070740c008246405019002100400e4005100400c1c0400451040008140b000058001d842c46900400d07030301e0b075050140c1e8052240c04941014407502c161341d44401405041014042032800c0c0d00d60001d2903001c00025544c65090400003886a00c240180c00240c40e0041d0040030ba5598040c200d006842419046150310b11080040424a07005000540041d07d0100496 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 408131025 1250 408129775 408129781
    0x81e0a0518061620010203070905030f030c060105010c0510050718050a0b1911160501080a05041a15090901050916030c140d1401060603050a0608030702060a180e 71
    0x4510007001000076240c1a911a4003086204402642400d01e4001c80d410021103001d28400c0401803080740341140d1806600c044108401c1c1e6600003603080449409406440c0c0d031604001c1402d4a0340f00d60100e940080c1c0c400c40c0100501d51140f1581c9000031300510a562092042d8081d010030f40d44241c0b01c010010f0070702640640c0d100d41c10501031000340400c0710360f0366003140351803002000c900820795071140500b001d03200c0c120302c0e501076074080c100c0c20b027003009480e0118000c22981003a580c8a02845000a024000051401c0b14a2051a000d150801c100a00301040f095450b95100c200403d08440c03480648190450350321012291801034859600109a40c504101c85500d030850040d0f9100d20920320940401c0032843c10396404040d1102220704410002510011602c2c480c0040030040400c0e44201c0c489a854030194048019101640c0d014001130f228253740c0e000791896406403030360a4008000b401c00600d4000010200d848150522442850300003009810140312640300741c030386101440c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 408132275 1250 408131025 408131041
    0x3011e0b0a170a06080c09101208070b1b2a010c1115070f0e03012c0d020606030705010305040c03020a080a061b0912030c0c080f0712050d081e0a05 65
    0x50540e0150b0f545008015a51814031216540d640e02c5c1101409903c01c100801c003000006d008140c0a4110075890000304000c40c0b40142e9a035000300c1080e61718111240220f04007403124610300842d007a10801c45030408601641c075484440856164416109982c40ca0200c3d00400780180901100281c4031400000d005580c01401c00c041c104d05100820000c0702009041074014050241092541c0743c400c11161160300440d00400004000001651074080641007010b0300c1000c0c0c0426802e00016180200001402aa40c0e030601342d84195042d00408000d00041d40300b03612007580140510003e5140c141d90307401140d04056240c10515850f040403080c4010700038240108820120618083c20348845034410040c0200e07020b0107a10143c0d07050403c071101340f40c0b14244c0359504030b81200c040b80b02c203035030350101c103591340410b0806454601902c42c000030405881d880c15100943c101001e44075540c100001161002c40003026400201803038a01122404101151103218051035580010a8100140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 408133525 1250 408132275 408132317
    0x507050106150c1b0909060e0c0102011e0e030f030a09121803231b04060b0f0307050c121611120c0405180303093003011e0b0a 56
    0xc102e10b241d0002c070000d14180e00516015805401010241c1c0d00148241140869002a40315030030903400c0c15040c8051100640c06900c1003070f00c910460340b2144c0540010381c00d03104294110082112043c0c441000c021240d0401c0742003583d0b0405503450150101030800d41ca4100341e89032440196a552a036081003840242d081040f0000d060149000c1c98003426a0185441c03400000c02000750984102d15498041c40d04490100104050350702007021300486000c00d100c9d4110aa1103103051400002e2410b8982041b0b80a9450586645295994036081070710b05510003a9641c506224941005020b102010007a01e140c1a500039036851034021414100e905046480b1824491800d07082084c0411f2000108001b10440036500440c19556003107180418000c0304801081d00d0000004200050901044080c0e6100c00501c2c00710f00c800703444d010340390a40581206503840c03d108000501510020140381100c41d01c0c0b9103204c28603207485104002c0f45030032218a107008603001c85002c00803581a03034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 408134775 1250 408133525 408133529
    0x809211605070f0e09120d0f02040305060403030b030c010f02031206120f010609062c07020c060c100e0307020a0e0c040b0406020f071a07170d050708070215010e01051c120507050106 80
    0x102c001c00110131181000c0d0164031451f038800040507900c041c030403d20b02440d010750700216049001d50b602890a4100603000d02600c840c2c203442800f44041d2801d1a6004031941e20425220b81c2c0103505200300f000102200c1c140152440740e001803091011240c0305800c002a1200c038990400210381e003841c1020301000d40f40681c00c00c410820440c019442d6400b0b4036021010050003800c98841075807298541a401e0010000543e50000e40020342400c08000010b018041400140d10800c014203903034414680724058008001c0d400070400b60300700b202d0301801c284242c010000c001c40c503152a0351171501c851783d13500c01d03489480075030070a03030700613607006020702c40d0f20001e22821030545400c0c4941c203030018041c800c40b400189411311703104459550030802d40640d00302e41000c1e071080006040000c0083d001490460f081c10042c03113008010200c002c01d140c4424101d90398200001c0c2c0d01d0f420b140070089441fa0340e020442e602d50703c0030003110200300129032a0801400545070140e844000c0d081c61401d4402c59 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 408136025 1250 408134775 408134791
    0x306010501050a051c05010b091c020108061005040801020304060914060f16050f1b0607051614010e25090603121803050105070f0809211605070f0e 65
    0x45004000c5660002c1c00c940240031180751469594042010a1410405100d168000c25143c03000114003604080020030340e10104a5511401e444500d52071980001350321130081c00182c90b600031588505090a1100c5044101c1c200303c0e0805481c0d107126404ca8104407410340d2296101e5100d402400048880d110001a414020b0100c0c2d1400c1c450000d0039210161100900c2c42c01e22016401c003600c510f054509100700008495520140c0001c25081c0d40e8041e6200140c900940b00031444260141d0211030f074a10364020200d14100c059126460303440280701c145000740d5240c000d10f928066040c4502040545440c250400d1035149980301264210f540c2c0000e1401440d000c1c041c00842c4c1c200030600d0b450078861911802c141c6a200d0000141040e50340300070604c4d03082038117001410350003141003c0b81403025503800e8200d50303079965550760301c10300080e25000000101c0300e46011051013070000d00560032420f008951007105559424601a055808100c85c3d9010040c140314003220224000d410001d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 408137275 1250 408136025 408136033
    0x303503040b0414012a08011512050712020c0a200a0e090a0206030403020601180b090610050f0c07150809071403010f1b02010e010612170c010207030c03020c03 70
    0x4180d45000c407141000e0000350149819200c5030071007520035000b548a0070210010004034034080d078443e240c00001117803000c020900d18000480c241c206040c4560a5000716512034082c11841d000a0000b003102030101d0b0200503620114184a2140780014600008800000d2440c42e0860502641c107412260480303240c280010314422107039485000610a94040c0d00c040c1c0500d480fa401820b16246995000039000324000c01000305054001c1005412a90003000801004040d141100100d820f8224950b51240c10000458132505000b0002d07030300210343e41041d916000c1040d80a01300340d002030310810102d511032002407044450ba10b01d02c540040c05404e102c0b0580c1030030040d480e22045180565055806000184140360390b09401c4401c0c4031501280401a401d10f412442d695102c103e80c44401541c02d158070303140f400d40144100d40c02c440421004405030060340d503074441e401c81c40c0e118081082805124021540a00b0702c01004418800e8441001c0908280b8002c2e00b81009a11301601c00d0304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 408138525 1250 408137275 408137281
    0x6050a290607050d0207030b0717071818020c191a0903090a140f030f06070c02010215100f090603031409011107060203030108011104303503 62
    0x110544859025859240c411886102440100326180076109001e4841e1040200500060782c0110f0b00070243e0780142d903040503d556010081c0c441c0d03040d5042d600c1c0f40e00d43c400006245188142000c2503a4080c00d01c2110a0720b81d40c42003022100011020208650350004003141000020043c5a0000d10004404400c0341c403192545014251001d0715010300301c40e01d0380050341e01c031002c2c01142d040b664010f2808005603101c2e480746590782090003c1601403056003075030155500c0d000650700c0554103100003c0c449a91185422101c40355142422410b5211b8001541b4103130011120f680d20405c4d0100000801c20f20f031171144c00080c4200d900104000d894411b0a00100c1d50210382450258401e260300c030341d20320328070700121109030704950381141c00c5c0070b140c10204400e540400114103c0d80004024030000c0d00203c446017140c85180301d8001700000c000e11142e0400b014070308062052030143c061400906564681140401261010354920f411061480b26165840715503004c01ca8070500c08242145 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 408139775 1250 408138525 408138551
    0x30522080a02060a1b0605040c060e030c01031e0908030601031d0d0503040c1d071103090109120203010603050d02010504120806010e040906060510050304020f04050910051509040f06050a 82
    0x301c560703101034002d070720015421101d540036030543d203068690302500243c00521420181d006103810340f411561003a01c0d82c1c002070800d2081100d1203140400034090310340c20b0b94034001900102001c080c0022030350f0740314801500d143e6107442403a0f030460040c1c1c00140d0740d10b4024001401c407180c58a460f1003401e01c0060a1802e618005808903083c5410306040390341c2d44443c101100a408503a20261102078580401c1411071b00c1c501d00303540503403035688600407002904205c0c107407280542101071b400140440001c01070f410008005648241c006000080d0058483d10b4803820b1a00805450015039194801d01041082c00012158580820300d0101c2c0c00d4245440001d1400b21100e41d05031003244c9070808001400300b598044001414003c020090060850001501a80084030168468007441c19804481d05190080910072104140a00344000105113018010203000e004042c0c40003240501e00c681c5d444281c082c1d40941e00031030807010030f40c0807890140140c901c010607000406041c000600840 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 408141025 1250 408139775 408139783
    0xd020601060c11130c020d1d060a121b0f140403030f0f17072105040503120a0b040c110d030b0a05060a050906040b030f010e01030206070f14060403052208 68
    0x70f80e01c0644040c19000610000301820500c0007040c102c680b0b462a101001a00065500808a000c1c0c0b181680c81000c4c413400c3c0380d401561410142c000d002006450102440395580d0110950658400a14400529412041c9940d00d039801e0000c26002d11107642d10503004000402c0618140740b01e82e01c1c0500315500280744100c409400004d02c1001310843ea00c841c0a8556851850031241d000030080c6010203000b040407501e01c0181c51040016014013402003402c1c09020702c101e0f0090011484c01c0380401c003620307508100070244180d655031408000402c2d501c6004464054010f03540b07109030380c02e01c0100c481c100004480743c00c041c5460512804942d45941c50300e002246c41c202c40392500c84021000a480350b10034044100d0b40044002000300340d0b80209406540940900d00448540c0c1e0780381c0c001c85042032001e010280d4411401e02080e40050710004441d010b6522601403060980001c2c180c013840c054054a085000c0f80f80071644103041c8101c6107003e030041054940a070b141d0717480c2481050311 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 408142275 1250 408141025 408141047
    0xf24060e180405011d0f07090c020307050a05030a0e03070b032d0a0506040b01020a050a110a0905011e0803210402060405060c0a060c0e130c0e0a0305010c0e0607021804020f03100e0d02060106 84
    0x4600c3c2c49d48040d00710140248160303580281c111040c1c0c0d10b20015460400d84036070090503208045101389802d0480380c10001600e40503a200c04201d18515180c01440e40c401c007030610740c0300c40c8240711651030f1709134280e070660b599000300d884000100309410038800300016201100c2c0c40c0740c110740c0600f2003503020400c0010304c0120903400c011214101e000f0345010504841c0141c115180080c2084c00000c0d400d2543c944604c40d80c1d218211407101141c86004503900ea2142d00b042c2d00c0845020800824600c804000042e001840141140d2801e60794101181c22a040f80d0a414140e0300040400303c203010140c00342e880019203a01e0942040700c40c12001030729070401c6068040c40c0340d80c1c496a0b203240d240035003030b5511000c1e001020502d10780c0e0b07240381c604d02800b144840c420004840203c011440c1c04c00f401034400540c0c0c020301260180341c0c0c856052900b0840180166400b140d11001d00f0003589003070000607403040310900c02082050245041510701307a01000c4a20456000b4401040380951101c09814 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 408143525 1250 408142275 408142289
    0x60a0b0f0f12011812020f07090221040f14010c140708132601020301050108150a0504021617040e04080705010b03100f24060e180405011d0f07 63
    0x9040d40450702103900d10082c0b42000300710750b20300511150784002d42d80151484901c254141640282014812622542910381c500082d0340b00200034029141c441e0040c010b0009606003810303c01005003404c0456100030348094400240c1100d1180a205030904c3c06d41010b6005070003400340103081710000303151501403040418000b40c00b1440e14100103c0e0340898034550302c204003003000b0940390f44950108460f500d111175010101290f883c26485418003d0720f040f110141c40d0039000d50345141d10314640c178007840046a400b9240443c0494030340d03100d2002e8180d000a86c5030b01d90034110503191081440034147c06004402200340702c100920b1110203000c42c0e1140c0c1c40030110b0703180c1905107001d0703000d044002e034095454020100f003a40744802d03685c0a18409503000200b4001c01000303823241214000b010464241c1c500621b4030501c04140240303481101c148020382484c284c84c108080043c0c40840681e0b0849060351502d4442ca0030340501c0d441540701d42d41c20310103030801c600304003401590340c1d20611402c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 408144775 1250 408143525 408143539
    0x150f0a050609040b031c0206070c0f080702030312280b06030105060702060409020f090406090b01090614040b07060605180c1611040c0e1e0109031115040305030309060a0b0f 76
    0x102e40c40e250001011010042c0031602c1341030a0400820941c009030140744014400c1d07400040c2150f1103007025480d004c0d080308901c0d40c1040a6100c03120301f5803044c0b5003a1303050703c0304020180103001036014035481884100a4202c10444154180c24500d0030000c18501c010708043c404200d55907030301c044a0459004850141e540d003483e00c04100725000b164400b009841c400300e4801c1001d03022800422900e2400c5070104480b54488030208101c9001d03a10090005041c80400d010190107609201190100c8229007402d043d616030b01d50455a110040032200c00d5102e03070041110b4289140d5202001071045441074503481d1918445200c2e004025010511072011140002031004c3d0542113420100040c00a20050300c01c260017400c0040001110b03401101d00c02100342100f5400902004103010584d540048c581c40d5441d890790036468584041d6219941140c01d210700c0d15444010030040d4843e6014603124070b0f1108040381403000007031280040e5414040c1c0308001d03940e2481114850316040750b84d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 408146025 1250 408144775 408144787
    0x110708060a0504210512130b0f04060209040c0e1f021b0a0315090507050103020901020c24280509060d0e07090635190f0804090203150f0a0506 63
    0x41034403441d021302560300c500c0d00041401d00103680a4014000c95042e078810019a48a480e41c28183c510640300250a8150910206030154005001c09030028010315000d4101081c1c540040c084038074074240d000c0410f000301c4c0200c21504218140d07907000e0b441e10414038030700041600b01949900700c20000800c1c81d100c072854002599980c400d0b01c1d002d036420020010007004481449801003010403010b13600740c418607200003195846030086544840c010780c041c00c01c5001c0001404521600d0000d4000064110405203003008191f201a00100c0314244201d0103031001104941c4039980000f0320803040282c2002044c103c0d0b203a200846101000a4000040703544844206c0b034200520b5801080b8202e00740030001550504c2e2060b01a08100d02928aa0a40c0b80c1c0c08594042e0300081c480c1c041c0300d0781042c2040c0c0840b040c2429241d081c940110b41d6181c481b0181d981350509a4055001165101d80c048140846802c400400f001c5544043d20012042c0c00f80e9800200041d80c00d00c030300c0384141000100 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 408147275 1250 408146025 408146033
    0x60402090403021f05220804120606030b070507031b0803240a03200a21140d0903030e01020c0306180a200f3a02060a080106110708060a0504 62
    0x10301c0f08420103910100d81080c00340000344c0081d02003520983c208a82c46a40900800403031000e00042d1540440c03041c1c502843c01e0000040313003540c1503080d25811f545800001c042042140c0d41407055605903115640d4000601c0d000e880144880301004002ea1076215000005207240100ca8001010038001e4210300454600c680000011030300c40350300000241400800c200b03410703c40944003604040c15000c4851040d043c0a0025240d1140711a16032180340b500710f103807030342c0590b20b1400c1c0c0c050300c0002c824250500c0040d150110310300c070b0000050a1031100f041031507032005400e102e51000b44003500202e1814000280d0381c11000d0219102c40c0044c01c408a016442000b124241aa108080a00d11042031a601900c3c000c24003401e402101080a500810b00d80220300441e541c0320900c02c219100250480c0c00448080504c1d03116842c01c43c848080c001d40c1c0d035880039100d00481c507038a02400b0341c149580140480c00340107010700140d01c090401c1c07140c4240460070300d501c1001803030700051a0340c0b5420 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 408148525 1250 408147275 408147283
    0x30308180a020d1415010e01091e020a020c0604061101060f140f01020c0307181103040210050c0a0b01031b080f072d15080702190305031503010609200403030206040209040302 77
    0x13410389601ca10384504054280b0403101504aa0f441981e0300342c50707a03841148100b030380c080f0010018608400341a07190030046c81e80c007401c3d07040c04038411140050242c0001c070b4800da03c035401ca03402007817401850340090113007401441c001c3c08100d06c8100c3c07001c0c580041800051016007249114038810080d15610b81d108101b01685040d005080303a50322555030310b090391010029180c000d101c1c0c1c100192030081004101c103c034019940540024900b28100004449035000485c40c960a8010345000e5000b2a10001c4958042c6001c3c1e440e80c0c020780da1403071544070120460740c0004096004800302034003200340401e920086803000c0c201c06003a410710705012660803601c1c100030891a110142c003c03171032620b07190580c1b1a400031a260020b050710b9580040c0d030744001c5082c4c0c81d103541c200003020030700280c800c41c0915041004108400480401840080e00b9907034280c000910240d600d1030103010300060010740441704032020043c6031605055880c0291980360080c0046d00454200003c0350805100b00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 408149775 1250 408148525 408148553
    0x180204020c0a0c060f260f10050324101a0f0f03090705011d0d060b031c230705060103020f031507030b010905100e040e0c0402070c030308180a020d 65
    0x300810319100c0701c011703205403080c2081c00001000d000c40340841c001c0c002e120201c00303031807040c1c0801165203140c40850100d2004046484404c1440400520f5840402c800080041003007030004401000c9400600c0d0600003d2603105000310040080046003074014003442c445066000150b903d032422002100d141c40741c00c1c50440c00303d80c0001041903201000c207104040e41c00991350750184c400601144021038001c030701c1036640480350f600001c0010b0f40ca603011500b82c95000d801c0c3c074030307410311f070795042d80ca030319009850300c0c0072a65001595042c0071350703042d0b243d64800c034600501e82042c0b800e442d610b96801e8140802802004504800402d640c4c0030001310071000031a08501c1c405103885203000307010380180141ca5010502c098000b0446140c85013002c0080b00496403140c070000d4000702000050701c0e0b030555031416809081030700c1a89486a0009110490183c0c07003a410b080e20310b103030080802200424105200c1d2740079090f800000000b040030000303250100c8041c185200c0078102030041c50703500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 408151025 1250 408149775 408149783
    0x20d090902160c030f02040c050315010807030b030f060907122a030803011404050a0203090303060d08091e0f040605030304060c060219020a170306030c01140714060109060603180204020c0a 83
    0x440700041007112441d4081c617101d1095805000881044c90281e89500064500800d40e0904501d02105540300754031540c0d00240524020404c00780050201c2c0c00c10f00c07080040c2d43c0940000c01005071400080206200a2039443d800000504582d20b5982400444100c41a80d500e240c0026a47d83e10340401c80101840d00000304540e60f503920207904a00401c03100003540079a0401c40090710207045842507911a61440c4065851a690003080000c0c3c0c0d460150207d41c44142408500f007071703403154000060f990301c2c501c400c490800340f9541042801c09a031094944201d003882010301c41600d012041c1c6007100c4850400c0a005002d902d40391001c0d009603060103406d2807240c600e21404982c00140003085a00070b01d40804403091504104040c0d1008a440a4040c1d2080481030b03429445105c0b891040c4c42007a555a0a0071400d90318031001c1480c0729107541d1310b540010b006022800c014491100200720380d040411031058141041c41d40107681c940042d1107141d021480200302d50090001101103540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 408152275 1250 408151025 408151043
    0x14060d0b0a021e12060102060105090c0705010e100204030314191b0614041b03170a0e1e1005070308130224030a2405060a1701030f0b07020d09090216 66
    0x8200340d40001c0c0e4000c440002e040360071184c0803610a50000c19071034182c0310060910040f03079072045004c080070340c0000004c440702d65031207061103c406800c1c024101040101100903a4032481c500b401007004482034281040941d080104144040012075215105012810116543c11075804004103100000001509190516007138031501000c9400003031040b4800e41c032a0340c00c0e18004c07a41090f81072441c04010051582250028811404807019004580711032800407480108040800d4003510070504000080321001c081084d030389041c0c542d290314405a85071040c107003002900c00518159001c0e00d25200300202401e00410f640ba01894501c24010700700900c02004004420030754903a2003203454284251801569031160a8105180c0d442c00500290050b000d506080421041e40e01410348501031050902000a2002d00c0088890085000388a58811040a0300300f00c000c40800410400449d0000441c18402940220104c002d445c03240d5401600c402646001e01c40e00c81c103c200c05401c000d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 408153525 1250 408152275 408152317
    0x4110910440c1c020a0f050f130e010e25080c0405030a03020706081f030803061f05041e060804030c170d050a0c030203060a061101140403080a14060d0b0a02 69
    0x1c1003900400649006880f50000d0f01250110042280903035030900b00003c03050802c81460602c20703005010011444110541340c04041b00303165074191801e5104121007141500100001d680b142d80c51079202c3d03043c68200f8070514a00040e1000c04030046050000d0080181c0410703a5100d0b43c50598004d404050111100b00c901c908000c0d549000910810000421030700028142420076104031181c05d0710017084e440010b00390b94544103c0e0f003000380002c4d0400d5202105003070700740c403400420901c80590b40707c099440741031a910420080c400c8500c01a02810181c007044416071000605902c0340d05468504403c202c14500401030840c801d40141003d180801c020108040e50b40c8168014018080c040060851001c0150306030b0108a5076290b01010401d01005164002c9011108944e0150000a00100b51002c0540c01e904292425000a001c0700200409600a4031034001e159004007804130b440d00e80940060711400000500400b00e520200100b2000c80e416015a80c420105802d0300072300b02 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 408154775 1250 408153525 408153541
    0x1090f0f0e0a14190b090c0a0f0918020f0f040e030a090f120525080a0f140a0b060f12070602160608010605090d110411091044 56
    0x112840a05880741c10714284403018190000807100c8001c2106024000c1c4c484440d100c02c810140000c000224500400949060310ba4030010704001074201481000344150400003560f04484041e46c2d00b51000b50540801c0b0b0250f51160a4910760100c01c0300c083c020070302c290011801415120500d2b059510001c1009030036140c00080b1036066481c2c00784516151641d4030100080020b9628002e00250402401480c9e04452422800c1c10800d4050b00c41d05499603947d4101c1c5000118181178400501c3c1c044881c0400079a11407a441d13009042000345207040a81d116080000b801400e51441104031140c110743ca900c031000086a4200b017102620201a543d640103501d40c66451030b41c912807102d082000c54500c2c02441d5103410f0380c040c0c2c0e0702c141c1880c00d08028007039a00e14500041e03c07015004d52103800742d07540b5401142c51141d02108450b882d80c03c10000c0c0200d0000403400c8a0502c681100880983c00220001c0300803011440f04480c0414444070048584404403140300036104030102c104003400c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 408156025 1250 408154775 408154783
    0xa0203060109170a0b2a16230303090d09120c05010e040b0402120405060c19050901140a02010b01030e1506090c040807080102090906041e05041b09091205070b01090f0f0e 75
    0x300c41c9941140a14500b480a0b0f86c0700c038481d40044195032840380325a58003003841034a20300140d8000d82901200354810034420f600c0c60b0411541d00c00740761b000c01e0903022000d0f400b04901008090891200018003103d0fa0b42e400090958040e5504111070f4861003082660342d500301154062020b04110340d1011829000445642e04807420307150383c400d410103714002e840002321000040c009074882c1028104010891307140d40041c204a0400001880301c1c035580c1240707401802c0320105500001500150003001400356203040d100490903070401d01411221000e010202c56006e0001c0354610310a40e2911821811405039230082c100c90700c030724000810020700c150b0050044182c00c6032076144c2a602e920030041503030a5046468113020303003038007110810f03411038200a811500ca0120303903600100b842d41d0408064059071151020301d813146207038810701000e1a00000880003a1a00c00e28181c0705444180140e2030604c1803821043d80d44868042200c095407202083d40368411041c00510104c42c0e0342075031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 408157275 1250 408156025 408156061
    0x10f09031116050d0611070605131a01082d0312240f01081008120d110f162604150f121a0a0602150a0203060109170a0b 53
    0x50744503107501c07a48a450b0010800044490080242401d98140d5a981c03002e8110b90413540c0c0501c4051040304006001c41c065503108002515124050403490b0400303c402c4481980c0c00006540d08400510103000d0202c0d80220002c005103070b0307a10320b02e4103408141644a0310b0000004c1800041f13500d07501d10100c0b15500c0d014050078a016011505c460710810541180d4031201c0d0303400f5841c0342c060700c0c1c0e5500410387c8560004408418130079080d59150024148110120b0582404d080041c3d00d403614046032242002600d40c101c1382c903040401740e1108514611500c551310800540070400c1d9000c10101c61070307030110449000e01541c0042010140c1c007280303030014042e1103040e14080341401200d9100702082c0d845039180d03588105d80200d510282c403004285d521340a020008103004aa4a030392990807031480205101da00030300d45000f1920005040c14070146c030810700c03d4010001d00c0040c1ea8004140c1082e60040300c0020010303107421552510300b207419440244181410010007100ba9480005006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 408158525 1250 408157275 408157307
    0x4051618090e0f1002043b04060203160809151b040e150117040219030203010218041506020d08070314040302010b0a0803120c0f0c060c0c0c090423010f0903 69
    0x501c00d1004150784042c1d0143d030047c071141017081061415000c50404102c150340d61006940b140c0180e0860840401341400c580c2a14596000000c2c8907000b10181c0c2d034440c1e070b9891032902c1c110303d080c00c8454680b00c0d00c25030144d422400c030200105030800003160481c4a4030701e0b00030085640d0343d59182c11007215030342220250b121b600e00404040c2c0550207410003002400442c8031603078095585600700480d00c501c0d25178020700c5005828010005803403d1004042c41c1c62019400c11814428200700000d5402e050610401d111881c0303000c0042c1500028103031060310090070000c001781d039010000c40c0103103c3c08180e4a60328502e0400c0c40107154043d8001d1224840c00e4402d0700e4501c5e15004900c1e502e00ca0707140707500e840002c507100103450100c801016140e90110b5031182c0c1e00c0c041484841030b1410b44107035030741e1200c0c082c0003401c460b12030400c102a00003440190b6000e2104d10303050702c0b045043c05644110200c00c0b4010200d841c00ba0100303500040d02810071b203808010394607240c14018803000c0003200450f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 408159775 1250 408158525 408158533
    0x7020325030b0c03070e040c02030d0204030c05120c01051e3106020c01020a021e04020301030c09050a061d0a06050a170609010207121119061a04051618090e0f 70
    0x149043c402d520440c1d00c510f1203504d1b404003241d101c00a01008000000f00c1401314007042c081029080c040740000d000a60080815007009030804040207200e08a0864942040c0d1000c00810f0a50741c011090b200b05070700007030b0850302d48020001e0b208014400d21440d2034507030685d555105d1000341e4010000c4800205901e0400d0020b88411050340c2d1006031081150250b4803000c6801d005103458185010720303081d21446040171031290030118040e070f0420780044130380800f03080c414002090b003480f0300c66002000c0e45c1300380911440c001503480b00c06102c0060403400501400000d410070865005007004041c094290503c00703945d0030321300d1069526402403c03004d010700c50104410a00500036111899080f20a0344480300010100b42c4100b41d031155100c100b4040c0306010a0720107610741006168900407e40032554521120742c904030b68a1103e140d9100d207290200b800342070100a2900840031407030341020060420345551101440c517490703010150b024103010303a58182003004200350800c40a00d204403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 408161025 1250 408159775 408159781
    0x50106020c091005120304033002010204050f0609030f060a050a0606080c04060c0327030b01080115170f010905011506050c1f090213060315060b0403060207020325030b 74
    0x42000c00d019107460f5034003902c1c101d0610035850082150750246011104403071406540350b40d0007420010003401c1403291140540307242c00c00411245141c42d02200c80c0f00231807505007081d00042058013203100c05c500442700401e40300b03081d880402c1841691801d6404407025450080105409004121103079007401c0e007003403000100d031400380a05501511341a400d06082900307000c011600310717023403a205404014010482800c00b00f001d4040d00344c0b000a98400640132030460a201164079010b0348404c0881e8540494a8100f0903441500030554590164121021440c01d40e01454440440c0310340e0825403920718500100001580580558220b0b504054205c07540d460041d1824080c100c00d0039040d4001c05c00340d652403401d02c4800001000400c40010b80603081ea0007044480724601022483d4960b6004240240111a09881403240e000c803c1801441e04100c40010b0303030300407484000d02880d008904001150303414440e0010107451142045a041d1080090603640d4981d84002d0b551442c485000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 408162275 1250 408161025 408161029
    0xd05241903022b0b0f07051819151715030307030f1412041110020703110604030f0b0a0c02010902010e09070e060a0f080619030b070c080d050106020c 66
    0x81690580c0110203001519480c0da02031100c0042c0403521a0300c94844a901d20810010a0640c000514021005081075141400b07140000b0b00380030f881c00c4c06202003884580d48100021940741c1c2e00040940c0d1081010401c50a082e81d0707075a03250805048560040340c2c09401d16403104945041c00c540d11026000ca0711291210b48805120030a842e416420400202011130f0044002c04490780310b600e000260410740040000315508181031522000c407080341880103224854034840c80c1154201c0e100b00440c10144400b940d520310700d200040103204071480e074602c50b5485c0e030165402543c002d6800d0b2144849803408a1407072204071074020a0f14a058046841a07105200e503580080e0f040e100d560481404600300180f8800007422002000305618005449450b200d0180680c0c29094499282c0301c60601c43c06041090010242405024000c0261103c820303400540f40440390010390040c03254032a20001c48448941010280180c3c81c0064411a902c419500150480d4040c0d03003550003103418a02 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 408163525 1250 408162275 408162289
    0x20d0311070603290d0822170d03110a03110903011b1b0c0909210201020c0c0f0a0e1308040b090108010b03061806040e01090515060108010303081b0d0524 68
    0x4c00150032003900c460107000264000024801d091034920300321030404450480213039159094029100806003d4800503030300000300304031280c210341e0341401c0c07000c488030750103d0b18580a1941c030901095190f1924481108281c0204d460f6041c002c0c0003880803108000e20350180150310f246000008820182080d000c2c6241b03124070801030b600c444814856454000c00d8009440c41e5041614114102449410060420441e40d52034404503000561140d907448010b84c2020b040c20005401505440d00c48411039036261100c8040c0c40000c591142e041d00c412448824003616041c008058100018003c11100b400038050174928009036241e00040e81c0710340400c10b4a00007601d000d600903c604003000b02e215141340322190702c940007038400682d4a01c841912425284000d000340e800740c0013001c00d982c264107000721076a8030400c00c1c01c04030380d55490f6035402401c1c40c100820400c00d103540000d49000200348141160501100b04005005600780304818402400f041c06040e240c0031100242c1c0212410414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 408164775 1250 408163525 408163601
    0x2010f020d050301052103120603010b010906020c12070f0806100b07081207020102090402130f050d120309020d170a08071b0b04080403050303040305070303050a0612020d0311070603 80
    0x160b107603800c40c1d1031700e8103100d8800e060002c014000744550081e030303800540800141088400b01e00d040041c5003042024142102c15079100c05040101c160b20a200c03840d00098008181d4505507010082081c10581080c10840c0b95040b0300d92464407007000040178200091000e0040c101044400c00441e03580600030b20030310480f0001058108180700359000c205280184a50013275440c0005450325042c8400a4226400091503028480c64408284030000e210000c01d005840190346080c482000c545414408950502020b0101616180c0e000115241e4000c10b80b00d06a009502c501d402100c0d120120482c0c01c1444150300142803035000551043c07103200c0400c030140c02c21310080c041005507200c4071003000c8000d0082c0d4201400300000000038104000544c4158083c1d5540c644070711941c0b8008080e108040c0004907030500b40070051011120015110002c2130f8101c4d034002000c10780f841c043e6082d070030310268420f190255050008081e40c141c0c11945a038081402c440030305ea40007807099400802c070b02d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 408166025 1250 408164775 408164777
    0x131707050606031504080a120609060303020c030105010605030402060c121c0506030723040213060302040315050c0d180204090c1404051b1b01020a050a09171f0603170702010f020d 79
    0x10800300e4007041d00f80f00100781f182c6030b034540345100704c00c0e8000800c140c80700c50b07004403041543c2d42c3c0c003001030543c10b008440114030128000d0110b940b40280c010b00a00000d08082e00c51040011035100010b800c111a00c4811400500c8940301d14a150f840f607000004c0c1d944510740a810480010954600441d25074241c40d282500407800c604004540c0b90000740c2c1c80c91680d04950300708580d01e540391240e40c3ca000100342941d8050b070303180c0c298640b20300076a800004a400281c02e0106221070f00903004250740300791140d080000303441e0082c2d0081d420440011500030f5040713440c001031001841100e01d43d02c3c0650352050000c2e0280c0c00500188000c0304c000f00c401101500710000707540030008c2038400400b8a81c1c4036a000305450b0201400c014220783c402040c84000c1480010f0000d16a43c010709401d00800c4c60b49003202625180c4100300d9140c00b40390745182d40304107001d003803c00d4ec5441e552091012359041401804007a030078180c0b040075a400394405902241c0e00030b8880e50a1480003030f03400c0d00d1801c1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 408167275 1250 408166025 408166063
    0x270c0e0306190b0a090c0e03030415050a0c0f0516081f0902011107140a090207021e04020d1505030105090a23011d0102090a080303061813170705060603 67
    0x1400c03180c40360400c0702c4400d407901c1519090040c489070754050503000903100c685000038084540d2000506540071030344e06a0700a40042c0000c2150300302051519500146c0b908200f641c0300e8003000101e88600800700000e01020001c4181014007400166194121502030014440c0d99120503070140d0b00c80b140c0c500b2500544110040e4142a102034001c0600c00344181004521702c0c20807042503042c00040d410500c482354880042e58142e24084a04100070026100704500d40282034001c50740c64051000443d0341292943c070402c1e203586130356044502c00801290304210b05440f600080c450b445140c480c4c20322a60800d00422005c05002c501d400e807199008030680c07245540004850454a900c90b03040319155039640140e414401166000b0344e00c04080e40006036981c0a0340104104a04a600116502e03401801040803607180c4115019480e191184418110b682c0c4071203070144414169001401d0070542100c100541c1050009488410301c90302c1501c26a607600024581d0703810401d0510240031750 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 408168525 1250 408167275 408167281
    0x5041110020d030c052a01060b0c0f010b01051608131a040515090306060126040b0402011206060210020c03090d080301030309090b01050414040b0306070816050306031b010504270c0e0306 82
    0x4200000c6c150801c0040c0001c02d01039594041e20035250404241d060440c0c01032040403100c482d0a00c40e2000c482005d003072481c01c0809110b0440340c0c1d103004a100502500c8001500007800c0000c3ca6503000412400c80b4101c0440c4a032003c0c2c0c28103801c41c1c800e00b40030703118180f0020004140e0006513074440c0c4c0054010022071b42c03101b00443c0c07c0f41c0c190300711182e40b41a05500c020804507075004c1911aa010754081c0344075003090b00c001804c00b8034103800c132440c0614150b014882c0c81d0703002c2140200b118034580003607118811440d0241c154800c029071241d00012912509042120f41030246040746d01a40320000d45940d100d50030070648078203e802500041c81088180803880040640e219007400144c000a481105240440e00d04181984c0160110760281c00700000001025040800b800003031610030304608084000c00d64600c41d85500f0f20070005807190711071907648100280c9004115001d000301071f602650f041c00308056a201c0001c5074141c14640758050b807601030a05002070410260060215076 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 408169775 1250 408168525 408168577
    0xf0606100f120f021201050607050c10210f200a08130807030804020301050a0b1f02150c0406090e06030316060b060408061608090a030305041110020d030c05 69
    0x300d051a040400d2040314200354004407401d00c1030880c1e1007030341d11005a9500c6174502011a182050340081c0c03040344208103205c0080c0020484400c854030903951111078002030340055520006020410303240702c030800c0c0c183c0840328150300000c0c400215010104440c0402c4a07004129042852a42d04c40c0242040000070709403182240560100c07280526201d4411543e8504269600192041c1c0000ba18030f0309110540c5000c0c41a180c000c401c1c100100301840d414408115981d0310502896a051185040108014001d01c042021001c8144000d0703541c1c60051036001c031640241c014000018103001002c0790b03a858a00f0242c3c01000020002c0d4280400c2031080f0032103c1c001501200c4039601c9006410f00750f252040504042c000c203001614607441d004900107595000e040900080050748014400c550a012419404468051601107070320754407828010413021340c0c49101d030f80040b00c10b031500c1512540841c030148a00166034007032000090000049906000702200003c4c141e00004858240c0d03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 408171025 1250 408169775 408169787
    0xb120f0c0f03221a070e0402090f1e0a1e060305010f0e060a0b0a091409040b01030b07030902031507030f061401050703090806070e0a0f031e03030b0a0b0c0f060610 72
    0x10707007042031401c0e001400e42e44d54580b00d415003154045501d40078400b4007030250f400c6014401450f100391800c50610155000240b1042c4442140d075000d21112901640c00303030a002110b104050010b400340040c1360341c13800c070b14581c06000025a00c1c2d1250000e00824a20b209005690403030350509400b00c1c145007040b02e40d0901a8010f0845a44000454000100490a00c3c06004040510784500e803280c0c0c60301181c000268400d41c00a4820843c040030040000c03900003080303040d83e030003407510990b6603240d11041d03008084000029603d480b400c1103c0c0c0c40780d03800d031251034801c420710b98080c81001e100d2103080082c0d0300c450141c081d80540c081d08682031544a40e015060482c0a840c105074100d6070740c041142000c0040e11040002104891401c07441c2c1403e02c061002408000c81c4049614a1915004480400243c00400010300f100c0f00c241070610a4000d1200c10704024a460b640540d04c01f9020502c0e80702071003010450140060601c00e000b8080b440910541001e0308000310301031085000c40b10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 408172275 1250 408171025 408171061
    0x303040b06010c0c0e0a06320d0b0a05061e01020a08090114040b0703020f060903030a1a0306070e040522020409081c0b090c071e0303060b120f0c0f03 66
    0x4202e941102c40b404a60111444002881035500032117003410115882003d5880c160880700100c078030707043d9880d4050005601040042c00c2164104602d40071000040d5100803020340c084c00542010003840750090250f44070a0065000725a404444031000b4800c08500314a05603060158009040310408640690020a200a414508664000407110301c03012203821680080c420910045152420107404203c120100c2d0001d4009008030b2610f028119a01d11009010b0542140c039942140c1b51107843c071840d124403041c014260340c00c0b840e00000051503200300d00515886281440f01140c54007040c00d00f101d0484900807442c01d13600d056038080c0001b400c00a0030880314000108281020009030150311201e600d046100820b403603e4450400100100241007041c00990820440d400108480702c01b0403503116075440015503401c0d904081d002440168004a1004d41c002800c5070714201c145001840740441d11401191510707200024501c60003098120b0400c1e91003000070440c040c40d05509020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 408173525 1250 408172275 408172277
    0x609010819021c050105040c0b13090e03160302011a101205090a1407150504050a0314070e0114240322080a030606021903020d030b1815100e030303040b0601 69
    0x10510f900c1401c00d1481c80b64480181c1c0c00d80d5603001440200a00c40e8070070380c01440c02c030403500c1c1071241c90305940d0ba0701134080c4030b490189561075035400d542d05410b10039a00207100e00440031104d111107090182c080c21114400e01070850a10840e044a032511141311005c558417562041d844882d5500640020003015100b1030a9104e00b620741000a01000204d40140243e40040c0682c985005441189034011244900c14404107010038001521030390380d0102180d401290b01220340b4407034192030742000c0720794000302c2c40c40c0c882c04000300da07109800c40480d045140c103503031682c8410010101211284030300060580407020400c04507200d4140301b400200c2c98180030340c04440c40307412583d4240b602d030f00c01480e0708042a02d031307502000850780512842d44092035040c1c0ea0340480d4100e50b0001e4840c010400c000c002d060307407911a20070707175200c02080c082c80701100210355045090030900e00c01502040c0e42ca00348201c0b5240c1c07100300b880b4803c1055039502d00000d4001c1d4115111682d54421943c070081141e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 408174775 1250 408173525 408173539
    0x3010915090f0c0206091c2609011b110607030902031207050c040b100f0f0306050d0c050306060d08030a0507050c060f0f07022103150604090f05060901081902 70
    0x101c1c10714068031803450090203881c40010b4000c0184806404c1c808010000c40807500700d03da40d600d103041001d000c040346105619025291506942c89000d091085002c4425043c10a00070011001415442451302001c040d403140c4d507100441a040380d00030400d1034a50b41c1c035004080425181c1e40207801030303201240700405a60311030b0b0090203014419040a9015946030307210b642050020308051090100040d0141c0b0746006405200c3c0000e071480c800b04a004c01002203002c2e189492078072940c403400c040d1000511400b4201210b091500c000402801030314842d020714004a4020702d80f00b40c1c24542c01ea0700040c03860a5903a10006d60008020040406081c414200a02c00e145c5030148502c41c4500c0041c03da00d0704605122000300941040200040155031056894550f8050880030103010f0701d2a00482d1907503692500c2e40e106400f150b50f07080680104001c5000f01d013461513130304200c9403c550b01c6010081e5a40c0c01040144850080c41b5581903a0029941060020161107045d002d490003d400d403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 408176025 1250 408174775 408174779
    0x7050d200703171b1005060f0402030f0403080601110115050909030a0c1101090b0a08040b061005180409021207091407050a032013030209060d081207170a0f0e010603030503010915 79
    0x1040c00c02007003203c05d0034615507a10410a080c504030003003103020003080c3d904508500d00b80000007c8030b0780103040079060240324400035805038418401144213202c0b49000b440301c440f203a030f01c0122195a03401000d11034404403001403141e81000041c0e50540d4440e030f441d000c01200a85680000e16105117502c0d040003084000855404141802081c009846c1e90760310b0300900e002d083c0304d000d011000d840c07184641200c1d1462080710f503100d4190f89402d1108c0b1700611202d41e400f0300140041402e0300000790480103015000f88204404514441200d407a21409e2124000102c8000c011400031618480814070030720010306c455100360720480c2000981e00150071b00608810f03840c03455400560343c41d411040501c50a00460401d01c2c0d2075034010380706943d00ca6842560780e48110140c01040c08820740427039000300080e21148606900101703d4401414000241001015000a00000d013858051a070400340701c222103031814801c12045982503692541103908001186001e07000d401e2490100081070303000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 408177275 1250 408176025 408176077
    0x90a0605030c0f040e07020d0f09052205040807050f06061503270d030e03120f0403091d0a052206150f0b040602070b130e060607050d20070317 63
    0x303201500d0803074008045860304032002803070011041c02090403c001c50b0100c0427107a410041c0380056420889400032881d4940e0b003103445605800030b0344400d013400c00d41448141f03c550f00c02000420701900c255480340300002d288542e03c0c0d46c03d0781e5540d04490802100c10300107400801845d040082041d026038040e106640c460b226104072280c44031340303070030903100304030301503050300c0340f1455800100051410080102e6001999150081c00e80103210400400502098400d80d0b245018006044c001c1c4c00400c1148003200e040d01c0300312040040c1c14a890040340c00c05190520030407102050b6004881c0d1400c280d80d030600600700300500020442e48907880840d10280c070f03080034800382410080840d29940390480003031500d401ca078000307580800100040c190108e40e401907401642c201c166150241e80ba03680208110703106880b800340c07040c0140c54070171085950091919815040001601c0310b1040d10042070380d26040184070003000602c080314031740c0030303020030360003421150341e0782a00c1c034420710321107a1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 408178525 1250 408177275 408177277
    0x20120d05030a0504390807050105090d05251a071e03020f0d1110110a0e030a15020c0d080c180303040e010608011503021908041b0f031502090a0605030c0f 68
    0x2030070f014003042c50a584c03c9110151708000f464804020f2000500c1e0000103040c03807185098050107485441454014480104144030845004081604c40359540980b9007801c81d4242c0220761003646003aa000d510000d440c0103031100240c000c020001c5400545120000c11310b200441201580110b650312118034009009501c803030b41c415280c810b28120198003c07424030841c089411040f81c0b40101032600102c691085d11007240d0b142c00e00a06190202d40040d24000700d00100511031910100f40c01c840e40c1e000c0e00580300005242046030003002c8820000d80f24803004680b00744055001b40f0040000302d400b600181c00022001c0c081e0f0f40b074241c4401040702c03090300c02d0f00246c0110f098580100550082080c5442110805141c1142800da80c00f40c0502201c02c5c1c410410300304104940840d0500040f0742e0301504255404800a90359660740b149400086803a100544a2040003400b0f44207100550084030700301080102a081c640d401d04405880b00e03003007d001c85100040521810f031019068030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 408179775 1250 408178525 408178583
    0x5010509010b0307080d0507030507050c04020a050c0d03110316050403020301020a090501020607020d081611011b031805030301150527120a030f081320120d05030a0504 74
    0x30300200c0c00c11442d2080c0b44c0360200b00d9000b9800d40e48101c00b507410040d030100517250b002d94140b070000c0c3c2d18129404c000b85440c4144003d42c1c0e21902c000352842107107400c840203100850211055420706040484140d04035960b019a108501c101000000c07001818008161040303500c0b410402d0405031a500403d003240c00c00c2e080e91000c01c800c40b1082c000c542e01080b45030342c0600c052004008000c0c00a01c0140000c5000d05480030310226179040d6206a0702410482100e044148000c00c01c0d105400380b142000110300c1058400710385411051031016031450041c1900c190040011480d41e444d08800f10644a50403007400100142805400300f00ca000105584012005070b13500d00c8510f0009081081c070500b0901514410313401390040800180d086481c0031001d503034900f081c0ea101e0383c8070840040b103251000001003040309016030491244901d8031400c030725202e040e145411424048541666a445107102d8a00030800a00005443d800d2035080355501c5885010340110200040c402000414011 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 408181025 1250 408179775 408179791
    0x1b0301060f091422020d02150703020d090501050405031b2803031205060f0d02190e0108010617060114060904090b06100503060109051224040c12120e0d050105 70
    0x107a119418140c00c0119101d4006130b02c0c003210182040d10030300c01c80c0d418404640003802800403082d81410f5645115030400994002c00700c09a40b0700551500945501c14404a400410103440011a0300d520030b40c1036a06540c40070300286110404600900da581e4584170303881d0b600008020054043c1e1440c1d10403840002e40f07000c003000d541410b44c0b5001d001010040c5000d244541b0b0311041000035a0384038546000050706807040003c9100500100307091900046041c1c80000c1c500400241da0780c0c0d48041c0714100c0300090001c2221a132215509403507100071035480d220079030000006102040110150701850ba400800c11490401904d0102d0159917440340705441c0750104504000003070504030701713a0742c11654070f00d0402e107503160050000e010500280101405144c1100c0104203144041003102070f1160b00007418041c2200150706120051800c40c1c00711555009840005084041000c944c510707180d214595000c0031461000445500f1214104139030710240ea000100d0205000788550b5010f0002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 408182275 1250 408181025 408181031
    0x1c050702070612200a0816140d060314030702040506060301080d0513031514060906060d0b061b0109170408120c03071202250506040e0702150906041202010c021b0301060f09 76
    0x944c220140070144000d205d1400e5107c0c0c09420346000d035103c0c41c070702070083c5150503035611020031400d104005c00040d00003c0003c2042c040c00b141400c07001001d001b94a04c221400d10590769480184500c602007840384c1a429072044203c0c04200e805003001c1c00308120310826501d901a0340303440f4610780701d40d00101c1c2414a03544d102c0800d610415240f0702c5034045415203d801440c14241c010554510580fa19800312590301c50002d9190703134900381201c102c8028000030035900c2085194060082882c1581141c400004500c46450a002402a5800ca4001001400e10038140b095980f01c1a0b100380e1810806000410000c00021103100c155a800710aa50040030414140f44443c80703031107044e885152010600d15020449075076642c08460a652601340c100b15640c03254401645042601c4c03501b891000302c8142000041c0400049980c070a601440c400d051445890000381e0803a03854088440058100038681d10041621080410001c103016000240141c2d0b2512003140c2c0c02c0c116007200038001d403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 408183525 1250 408182275 408182287
    0x2040302130921051c020c0a0b07030204180204061e120c090801050a05010f050d050309040b0d0b2802041d0910020f030610180e0a090f06021c05070207061220 70
    0x240f8503a011214000d58170114a026544600242d4a5410000043c0001040ba001481c454408c1e01942c1c000e00d040320680c103042d041d54001d84082d40090103818002106001d00040594254101150015007902c5030741c44034065030040000340c202c0408900038444a1a4000781401b400d00ca040e11030086132100048950404400707904c10390b42940094440e085441004e008230382d010045401c0071404890004001d0742c4c0d51f000c00e00860309107102074034148000d01000100c0c14405085090800d030550300107081103080c0c103a01c040b070295000d02c5c0c0d0705101d00710780c070799031f00b4503420442c1d801810741e0044070722004030328400d08182d038000001045040701c003005029080c1410200d21211200c04e081121076404032000d03c02280d00c5c1c910400103904240004074071443c0c00e43d030100d005507130884580a403468032810400c000e5480040e048600b407490700d18084a481a9200d1140201816409040d00900d1b10070101ca43c08000340d2901c86543d41e516030f8039a0b01c100a81000030103561184010b481349 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 408184775 1250 408183525 408183547
    0x30412050a0507060e01090b09030106150c1b030f030e040f02031515030906061e0303040b0418060312031a030d112103040f1a10090b03010204030213092105 69
    0xfa480d9109105010504444544683e0032090388400d0303070020700e8050707102d2101000085c0036140540c003002e21060056181a401c3c4e5000121208150260200b84d00d9121030310071514800c0064440070304408c6204c2c4040c40068800c94100b6140c0c2070040000c05c03064811212542240d0013540c02882d180000c0c54000a6800e1040400402c0030004481c2d03415868200d180c0c548074600141001d104080340511300d21a09111680c42030400e8010302101c1d02c86032500300f20585070b48540103047c04d02c801e524030315100d042c01f4040d040c1502d9214080555108040c3e0040c0d014001c1810709444090441c007081c14207440800407065000c03200c0ea64050107182e02c0c03601c00c0c14451906110450f0b80341111040d402c140c5d0660480c4d0300309500c04000350151038182002c1c200006443d0122458520306028041c00c540200300410a68400c0002002000904010107080780300d5171000940042103102400740c1c1215035489048814010380d41807070540d000e00d8003211100903810f6040c000c502c0206641e003641c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 408186025 1250 408184775 408184783
    0x90303550309080a0f0203070b0106050a09291809041a060108010303020c0f1203280e010e040f0e0a05010f1d06040b04080f0708040e09030a09031202030412050a05 72
    0x8114981020000c440c2c050316800100c4c840d150b461070038001c9681c0c02106082c070800440780e946400c524103101658445000420540c010780e21b1100103455480003140040d0380c003070004c06104103410580ca0340c414086104d9032036000056081006000c5204030000e685801c80c0035403060784910301c1340c01d11140740c82c1c0b21210104080c0c600307410807440f00018000a81c00050005100d941181c1080c40305119100103007a2445518280e2006d02020480140200304203604004071043c1c5403003c000b2401c0c400d02124141e8230744002d140051002446152203040c203030302444892041c41c8020070120300c0c13136086e5442c281c500c080440e591381d5076504501c2201c18512580d07010500d01250310350801020007807a95100e0b0060000b80c000c10141000c2010401200c007110945125401020340301c09450070500740f650400c2c40340c60001400100000c01c031080110849400500a0311044002420b51700d444480407007190310304d801d510007004081100702d80b86d55029881403080004051982e05480d0403410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 408187275 1250 408186025 408186187
    0x200109050303010330030216210806041b030f020714030a111203010509060a08011107021e06041e083301030506070c0302150705030f010b090303 64
    0x101707540c10502c0024101e030f02109070b801e081c1c103890301503281e2110f840c3d46202d14500480c000d0840107030203a04c0113100d820039004142c200701900c81010581e02c0d1400c0c08103440d0f2a00550410a078a2040041e8040c001d03400f2051403c224100141001001c4c3c1d111000041040e840382982d070300200d0304015095111949aa0a0890300060309101c0c500c400d00000900041c041c0710310a52009001a040f601d46007283c80041091100921490203014214111a401404268082c240c04850112043d140c0e4071007207030105001e0181ca151a00e402212011800d4910000e04100e0a0140000c1d41c000304011035041040d08070320420708680d000c800b188a0420303d07071140d082c060701240104081b4401192295004496050042c100409450700303e00340701d000700a00007149072072410701950700c1d40318010311b2090700d52030450a4144d88a60035032200c0c0c054440c01e10303031681c02080206090800444000c0e030441c06035100c0002d181c080901181021b91001034001240355042c10780c07000c8543c082d0420300c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 408188525 1250 408187275 408187313
    0xb03062d0405012a020709050c0c0d0e15090f0609010c080406030c11010b0a030305180d060b01021e122b0c0201050105150426120301030b071e2001090503030103 71
    0x310502c101940b200c06c1880b038804455551400140e00c0703601039080320a0000b01d0f0f4251202c03c48030000c040e040e001ca00001c0c500410321968070b104000c1160b0308a85102c3c500a2041c000c15a1a10410041d03901001c581c504004481c0d00c480b0014490304064809095076407008201140a88001809410a540c2c0d150440c0c1c1401201c034000e0700c6240d00807080e29007614015982c0c4803121500d142c40000702441c0e41c0c00414188040007401420750003204603200036429991090b10314803000290480b10481040b00c0c0d00320030800b0141800450052882552020031039540109651405031803100100103c0055501c50055045480d070a100302409460708544841d600848414024058003072030049401c402e540700c500183c2e42d0407084081c1040701c100e00c2100c584c060001459000d6030004c1c841221a0070701c00011070002401034900041c0348415404d80354001d62003a9084404215440c20060008130003281c940c102482030003140e070340b2402040116a607503d1450b0000c40c1c00e4002040e04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 408189775 1250 408188525 408188591
    0x80c01020d0305010e06040c05130801151d01230411090406060201050c0714010e010924020a0c080a0c0c120c05060304050c120106050402120610030b03062d040501 72
    0x105c0305401c010b606603042002545c00065008160b0010344d003e109028a1000b001010400060420030540180c0702c0105181e900313102c440c0d91313140200f020302c05059072001001242c0f001407050031318120030150302c2c524a10000d060700e81480080380c00c440849040355030a240018210201e400e00d802401d00078911440208a10324001040c0390f080e003d242c00040c00700701e10601e60400344000b504040002ea8002008001401c480c0c588a0000798002c80301c0c2000380c0c011401e1004c0501d19109881015040e82c60309228551650344040482d40b0000c00d41c0240140303519010003103080814580040d00725440c40e07901100c444d00342000f00d104564043c5100d010100104000a403000c134404640003000d9841c001681500c1c0191070140c071094201d00d0f0130600c04100c6941412070f0302d400d01e01880e01521984500000340404600b0b031180080490b80641c03101c00401c502c49280044d8001c40d40c01e0514100031981100c400e49401c6d00d0594060399260f4555868410101c03282c00794101c07800c4094505 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 408191025 1250 408189775 408189779
    0xb040506090d080c0c0a051b010f05040302060d0e2407020f0a15021b010c0c020f0405040f20280b0c0a0303050a09050a0606060801060507080403020904060b0a080c01020d030501 78
    0x1c1164034000c0066038040303030108801d0300c0400200301314038100d6803000582303800e8041035082d40944400340891a001501504040b01503130301540413a070540c0c0c0c029040e0351404540502c44405081102411310f172070703c506800101d00410402030100205c0c1c0800c210a42c609080000900c1d1000110300002140c0240301c90b0000196440144505070711100d2015841b0000042590740e0300009006400c41175017409402d0300341d164424601c450941c403c482c4ae065403200c203010322040301c1003120020003108165440300007040c1e40d0402e265800780b151340c0300328021070504085003c11401c12004804a8803100359510400c0c800f48240c400340091000050401103100c10302a544c00c100e100103014107941c0e201182c0151a0b0750428a83d00c0d0b000011a00184840e2810710020300c010310031200054007040020540510500444102c130340c008108a06060664080001c4054003900495600f503a48002c1c64840d22460306020041c400c81c00036003040c0b81c6440000e8284008030800c0000c0602d05401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 408192275 1250 408191025 408191027
    0x4021306120b0402030304121b0609051e04060f0909020f040903052203080304030c0605010504061215060f0e0106080105091029040b090102070807030206031f0b070b040506090d 78
    0x10700704229040300b9075034480d4440d40003180c1544601d400c294980000e440702c00c2c040c4a107882d080e0152541d841003200341a583c400f0202c3d4050f0f203d0050a40c480240e070200c40c10311400e502244841c40d0001c20019945585a404404403030b0385a0014000390303151801c810070b40c501007601c1c0c0ea4062050310240714070061694021f002e4481e1000900030b514228185140080c1c080d100d0002555202c5a490303500e050604009e4010303092110300716801800c041c000300b410f09082c02060b0403901010802c02e40e04405030f0300c80701d005066503280301001d07685100000740c81d80702c1d507030440051500c50104881ca5042038070042c440382050304690b008922801c02d01c19000d20030300c10001180c00c20038494ac0c81c0050f013042450b8890014104680c00900420049000643c4a00400e61180240c08840200f40e6490f83c1d962522458030019511807000d2002480390002d41012290190b51110038201e00c0da00d82000c1c00d429000100150f1700100d2000c100000c00004101d001e80100081c3c2c0200b00042a01c24 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 408193525 1250 408192275 408192299
    0xc020f060c041205010603020904060e010510050f1005220524120a0209090412020f07051311040308041512020306100e010c0803090604030905010807021504020607060504050604021306 81
    0x1045440710401c40710f044003444020344c000d1000c1c5a00400c160b00c58141801c201000d0400c03d007820184c0d52811b030209010102000e02d110881d08064500007111480c0f0041040b12a54079400ba01484410040c0841d40d0480c40c01e1084010350382d85100340958100344c18058800000401c5e024441a01c591848100d00044107440f803100a0403aa5021691b07a901040702a0143c512615044040d1405000410082c0030750b0020b10320144d400c1355840c840b441a420354a408034401d05e508855060f02d030f011002c01c2900850060345130341310303024580b5035255a0780c032581d4031950010b0010301d82d42440e0300b0100e07400581c02800d41c07541501541542012000260a030292240c0442485031800d4a4000c60340603145401d0300d690007000e2039459140211055464000c200c5007200003400741c80000c501580282981d0b8007a50199008010501c807458410301c0d0460040c005a9020340240f200782c000440d28080ea130310491040e00540307690b06062044c014101001003066000c4c40c241082800744a403520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 408194775 1250 408193525 408193529
    0x112032703150905030a03060314030a0c110d171801030c210b0a0b0d05010803070b01030b0702070f09142202130e030a02030309160510050705010f0f0c020f060c04 72
    0x903007042c6000040c0c201640c010580c01000500714080403456108280e05a84200d003101c0c000c42050718802d09405405450380b01d0781082201140719140031401048a8202041340f0103405030035044000480d03243c18a6005040c88041225400003a000c1c085194640505203202002e007411b01c204000144040e00541c10540d0125a403913617240c003201c01030f500b038018688200000d000074291984a01d000d0305540e00c034146080b5002d00300b0b400080c000318000110341005030030100d84050350f400d640d50f0103018800544810114880c0000205003400c0600010000f021300300780014241c03c4940407440c2d0018010130501c050080c130100794481c0c440b84030000041c1a8100e074030705807201c288444a0003c0a19050b181e2540c400440c0d0400c1c1035400000850150700703003204440d800e15000112944120b294020282c0020814421188450044000d800d40b90311401c0041007030009240580100d55801403403807195500c0741d900b802c0660301408000794a5070513102603d10752a0076155120644254 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 408196025 1250 408194775 408194783
    0x806010c030e1f020f0604020d0b130b07050405030f06010b1b16080c090a02070804050105090f0907030507110f07140303040b070b010e090a0302070b0306040902090112032703 77
    0x4000c0180805115181825045a00521149490f045503601000c3c10325040040b034058410301d003400041010004042e4440c5034024015581406250303140c07034421402401d01c20120002108800004000f814018483e100c1035480b10b45652810381010304e014046080c021150b00b01000510801440c101110850460418400f1010342d4030040e9a141110540110b0342421007008017103042c1d0720100d40300c1a940750495101905d0340700d5285040c224843d400004000c03500030802007001d035002d0750141845e807000506031024030703c1040108008607012030707c22000954440402030b00c0c030f0704001c0c4181105030f42c6008180e052400f0040c19a00c808038000c0b100b2180d5914519a180c0da4100f08440103810709580b4251100c20b42d1a24006044081c015008901100300c0020160b44001540c60001c641540c000c4c8107042c504029145a42c0c00901405d4105841b01a02000b40c0c0722803005e1802070468240040a42e443c905005041c51400a44c80007007401e098010001c00f42002000030a507030f00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 408197275 1250 408196025 408196037
    0xa091502130b070b0a0c1d0d020a1205060703050114010206061c0c0807080c0f0306071d030a03120f020307021b01050d05010b070204060501050406051803010905011e06090c080601 79
    0x103400a00d0101003242d1010001c264002116000c008040844038003c0c4900c240a0104151188054680800e1000a00c1b404038245100110720318181d0100c0031071a002410303a1180c161588030100c040c84400809844560001c001d200341c003589807256500510312900400c0d0030202c0500000d40701c4c14090320261051038079038140b191504481e0721003401c280d0703c5490100c08550701c0a81c035440e890244107220407401041c580c4299800c110071710701d100d418018050440d503035418a00340c5010107402210803a55011038401c69194500300042d4104501039201d00b8500217035111070b002510840c102c1d080d4900e0040c800c0c04000c40e000105c40e40b842140583d122210f05400004031000e002d54078030001e1950400340001880003051000788112802580c1c02d000c00340d262801034030356200c1c521954001840420101c00d6281e0780c0c01c180030000307000800108605005880721030965001040d80035480f1b0f15140003002c00000d9104030002005d002c0c40900001c03c21000203407030030790002c06007414006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 408198525 1250 408197275 408197287
    0x9070237080702030c03012909012601110c0709050a020f030408180d0606060806090c09040e0304030204050f0601080a0b01080403030b01120501030506181204170a17030a050a091502 80
    0x502403203100c1444078094003c00c100d40c60003235000c40c01c0310341c0360070203551784580f00b181c041c0d9042010390f040c142c800320b080110b0a007641a030600303000003008415100555840b0045190000d40030003c3c8260410100180b0105041c43e403203038115a400350000d086a4410803160319031501c001d0aa80d4001e070405911515000100c007044e07003614900036116404511140740c0c0d0100440366010009884190b0b849060030354824041c0000c0b04010b0365920203084c428003081905160580014805c8c400f80416130303040990b2507000c2003d841007524100c3c04012400d040003a596400084641d0042d28400f050054603c030000107454100c002d003000e010191190920328070390b4000c1150600a030340000e01008950380d2400c240c5e8640030243d507044507a80074201341040d01c0400140808903000c56142852400b46815004070b030410200300301c142e590180012000c01700710f04005030100e0461301ea0f40c1301e5a911b80040c0c50401c03104002c1c15801309030314010f04c0c0008154103505104150841e8240142e4802e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 408199775 1250 408198525 408198529
    0x28060515090d060510170a050703140c040504050304330f0e06070302100e0312010e06041104090501030201030b0103020c030a0804050f0d0e0406080d2c09070237080702 74
    0x42d60080068071075400c240a110484907244444000c50f02c0d044c0c3c00f00035044d4901d490940703d10905c0750203003e95000500500104881c0304218699615540031a4600302c5264046003d0718000c42c0c007501d494201043c200042540780f9100d08001e0000d407a048407038001041030800c207803100e8090b0800c00c40c0031440040d0b182c0c06509050700f6050010445600c44c0c1280ca00250f482480401c982049070600c8046c1e014494000151240d0841112000c4903030380c00c1411001004000505140d072064481c4045280d10303100c00010700c0540188000071034036604500000d001d542554969074101481000300c848070403400300541d408120b0301e261485144d203541c20500c0c13600342541102105401840025650a9040400e40c0c00c43e6405460502c4070b10342e14107800352600c4809a02c078001c142025114400d0746404c100240700b60007d02c00038110b8011b68404a0400c1000300d0342000507a0001011103c1101c0310481400760501141d1003807094059403100d5090440d000000400c20340c0c0c0401c2c040119 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 408201025 1250 408199775 408199789
    0x70509060706050a0c0e0f0904050c04151d0f0601080603010603020603070c0309120f02060a05161515050109050409080904020f09090c030405120714062806051509 72
    0x4000010001500c1d1105414544020003050312901c0e025494041d040040328041c282d42d0310001d8006007146501e00d40d80050115485004000b1100341c0140c1e40f004c4401d540d10b204800141540340300c074061541c10107650a40d44508620081003004444d030802021480d02200765512502c2032816800720703100d15010a001d0119034000a40c0b0003808400c2100003a031020090b00910700943c2d40746801c0b543e58180320003400d242d8902400d55142d944044001d030030b0006c000d10121415140561400742540c0c00036150104091045410800b1440b100001ca0103901072860040e00c13020264085502d081d00290440085115aa006e00d0325408101d0500a101069910700c1d04058400c0d503075601d0114410446901c80c00c4158850301c00c1201141e01e40c0000c0c02503e124561000003000300b4694010000d000c0d0708940d074102c4080140c4000d56001003418000d4500603643c201c0303034807050088804280e103004a600014040c0c00e01d445010442a903034032513261105454440126687c2c03a111001c0303018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 408202275 1250 408201025 408201037
    0x30c0d0b031006140a050105180103181e030314060901030b070908030c01021b060403022107060e1c0f0212030c040e18160b1b1f09050f06010f0e0705 66
    0x50245082070008030b2445032101d10182c0d031000c442c07a80000340c1b240010b5030940a5811400c44400c03801803600020b501907408103036200803024200702824490303681c650f54540c40808504035640303003484140c1010b40500a003002c0200540d1585024070f854801b10303125060501c8090040048403010400c1c1a025824901c041c0801000781c3c0d65607801c40030824040d6220030041c69501e45200e4607040c600801140306805070798194003508042c211805150003403801840c0c1c2030464401000b1690015003540300369402c0900c10000380050544c480c410700d205210055021040c8291108110724072540460245c03400e0304203000ba6512501c1d00f00200d2501e02440c0c01204000400c282840303030243c104000c2d41d00303080c210401c840c43d90a88140b00d00b5000c0161141000d800418403155850650b1820761034551100c10048035001c4501801c4000300031f11210f110b00c1c10550303035a0035405002d814068980700102010040c210781d403400c404003058080c0c07803149042c15000307140880c117098401e40440d06 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 408203525 1250 408202275 408202303
    0xf04020913050103020a0603020a080705071a01150306080606010504060c0501021b030d0e010218060a030b04060b07050631030306030f140d0c03020d0311130b040302090c030c0d0b03 80
    0x644100a031881c80001c10007800700780e1084101000000d2164400d00880c0da885000e80e461044036150581c01340c1c1c0c5900f055800b11002900041007003a0300b5400c0000500a00d56000ca1640781c0004420242c21180c060300544c205410083c1009040d90f00034048a00722116850404500d0f055406c142c0d009000f009400d40362003020000c01801007200101404020381d803504100443c83e1981846802c0380300d404849100300ca19400200c11518254014002c600b6850a020032048030305400901220740315005142540c00108441d002d00c441000f105610003140c620010f001c0310043c5040c400040c503446070701c0c0c12104022400c0e0406120fa001030000b943c3c01406030100d0090b03032410700c0c00380030301e040640c602e88681d1898208007071007034441c0d01e1301d50380540140a10b880b403e14200c3c06000d940001c40b40e011400c01c500b44140c403000c10000000c000c280125500e170350a6104220395008050883c0607d0301c1c0c00e2050081460b844004c0340d00c2281c2a80303000502d60801404a410800300c80003c2c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 408204775 1250 408203525 408203539
    0xf020408060103031e0c032607180509010302090402040b0303130e0f090a1a18030f090a0f2301090506180301060b121b0c0a2009040807020f040209 65
    0x600c20304006241c034183c910030389528081c071501c80c4c0c4034004c8150840325072000900700078103000400c0c0154034a01d02201800340e11031801c1510290a1f01c818001d550140c00120800030301a4051002c492410240c0300483d1000c08039407645e000034441e480042d00c00b0344115618103070b40000703a400b04112941c000038203855482090391421070305403a5404940244400e4803038400150180c3c0007050070700720144d012440000c1302440690100b41c0d800001e009415075181442c00b5045020104050000b420050400703594940c0c518007400803800c03c50f40254004080030b40c0502030078040d400040c13420402000001e03e42b1141200403290100c1caa0b0064ed04804000b4540c401d840e443c64201c86a00010340080c0700e655501d54445403180300d81000051500c0303004010800745083d47c40c000d022140850202420300310500e81103400c1c0b040f02c1400f1140b010541c1c2c20782c1c151011801c04034042100c111100041d514098680c02e446218009001703100305210380402126030b5075507040d0307014882d0262080d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 408206025 1250 408204775 408204779
    0x51e1303030c060614030d030504020307081f0c020c031c0c0204050c03090f070b160f0c0f2d0306020306131506021c1b05030d050c04090e0c091501030f0204 69
    0x648000c0075034500740c0c0c0e482e003801c3c03000c192122845c82c1ca01c0003281c00340003031051103080c0c1e40460050001030000c80c1d0601650700c0005005004102c3d0800c11403079018148400d95400054004917081c02c08060255080300e9a044015500800c03c0d1513020740811003001e40c0c0e60030000445941c000b141c03000b0b40c0301d4507000502c01000d55000c0554402e078944030881e0320b81c01d00a07504540c0c4014a2080000d0800200700041d10030418010b910302c52486885410307614542da0b0303102c60100d04160010689001c0000c400c1045465240300400003607070410740102050107100c40780050100c0c50002401094000010900319140c0c901300494095405804010343c1843ca50004039121003441180010320413141ca0400304504084400c0c0c0340b12047c1c8842c00c24800c03498031200c0c081d030680400d03911401f05110b0200000c415005044c420041202c40729601c501b0411540104da40b007000703500d9164404000e961071034a83e95a03541c2c1200080141030391480d00d280041f809450404c01800c1e07154004100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 408207275 1250 408206025 408206027
    0x80d111b0913063c05041e02400b09070c08121924030b090f06070201050412050903060a050a02040b0d090506010506161e0219031110051e130303 64
    0x3440c0c0c0c3c00c00d64218990314040001c00c15000c0e0342c001ea0380600303007034810b40501f4109000e211110010a1000d0303c8420048400f000441420700c1107100465104048a00d0303222080002115403031900c61808208410071401021481c51000101048148002c070001c0b0700a0142550556455030306000325002c551414690f903c1c81c01d01042c0840c40550f007024603c06140c01e2544450811440b18240500300714a16181c11140b520051704010f030a014000c2a240c10b11024441207216001320340011480f41040d00e000c0244505134400001080700c01d02070110182e4022500303d411141840c40841d642d2102c0c12100c000784500da000c44580303040003ca150503000c02da0800d0906600601c180c84050781e0700c03003e2061a00c0307600c0782120b643c411150600002004c3d030008480e040c803c8512070340a4001640881c40c48512002c1003c040807201310704104001c0042036a80801d04141c4803001108042007014100c0d01503130040824030399085130100219615082038481480310f6500741d04074141e807414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 408208525 1250 408207275 408207341
    0x41b020c01030c050c0606150717070b07030b0d022b05100b061c0c09050d1505011401092105030708030f060a030b0604020d06080d111b091306 63
    0x580401d052580e6181950300420544172103540b0f21024000c44e03071f241820000303a048000e00d140e110100a1011801040c44003032250038901541d0031042d50317080242081c00000100a00520416080c172402c50384644450800c10f0341c02c0d5041c1c800c0d0000c140c02d800d07002d01c69014400000e0710b216950342c200080c804c2c0058450060314004504010015030f041c01e000484c4100381c503403121511001f003e026805010751006482e07d9842c60701c081c026840d0380010324540d083c010192003611074680c042242c14000d12503640140507070b9111b4a21216280006403075241103210b612205060940b103007000f209113800d41c06c0d0203540300040c0c3e81e80f803010b07142211058000303960b0803101d0380303000d0005403181c140350141a0640e80c210500c5030507079030348004201c080c3d40050b00310341e40540c1710240050300081c2008901948a480c0d01c9162003c07111b05807070741c502200110b00744132017803007601852140c5e2504034620750080c0b000000d02c0900122414840064002e1420041c3c940c4014400701c8445a5403917 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 408209775 1250 408208525 408208543
    0x1c02040b1614060a09110409020108040f110a09020d0c02010917070618061b0c20060c01090303060519030f02010818030a0807200c0f010c020a0e01031106030c04030201030902041b02 80
    0x1c1030f0b02079141d00005107c21541c4040c40240822170001c01b0a02251000c9040602a840350f00342c19640800540425040540c0303901152986401084400e560040d6002c6d020300480c06100130440316049854003540c0100309a990f103541d00001032100184020b64001504003010044103003040000b0307140c50f00c0144410031402514892040c010005035100e40f82e162042e641145811182d9102da4811803900411003411a0b0f12420402101e560000d0a02443c074181d402034400213212450a414004400b5000c900c01020012044080c000610305551a8282c1602880c0c4902c181c0c2e19005511241050300c18001c4580c400032036140e1500b42d20680301c920a4205a58100052005507184482c100c13140c0c206581030b411a40c0c04181c036040240f90108842c40c1403400c50f0a0b02a150042075205115070002c20248400300014020b001c58003a90844191301903800d00d140d031525a0322400a07004500000f410551030303110600941d680d030f802902d01c800000080c4040d144030b0220195851503aa = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 408211025 1250 408209775 408209783
    0x8040308251101032705160b070f06150e130c0e04050307060b03100c0203130b0424122a050301120305030c0c121c02040b1614060a09 59
    0x1841a55024840340c00d1800000380d0180c2c0700e40504070080019406008060103080d042102e0b9401d0441c0d04da50100d0304110940258040e00501141e0100035512141c10740046402d42000c0002c1400502c42c00d121074442d9810150000d0b010040892031b50408180390b10890150316440103016007a090b040c05181d040341300301c041103121552001a81c11317121080384c02804503041403012801107a0355030424a8a00350080540b901d01680305000343c101c80408142c4801030f031011a440011184080c0c041015021b01001d440c14140b606d000011203107500c80d641d00301071129280c00101030b8019040f4500e00040c0d042c0c1440316802d0b006a0615880a4008002007840340002207021113018404072030581d00700c4120000c0c1ca0107030303480070b40d40c550001d0b01100444030100410800c41c2e03000c2c003860785001c20740c510b00d80d03503200b40000b82070a103a0ba003e480000c603131041004001d0341c20400112000729503803140400256082d42010741e402290300c48800140d000d0310082145001003540302c40c0c40a881 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 408212275 1250 408211025 408211057
    0xa020c0301050403050301030b060a0b0d06090506330c01021206180103020a090c0c0605070e0916050a030b041506050310080c090c1b070e0a0c08061f0c08040308 71
    0x2110101801c0e29000d80b006000328000704014400710302036944c116480079003d040410901da681a165115902c59512240b5980da201000e20a03103030345009075500040c0881e103000005541141c0c410881100640341e01c01e154005c210303261350004003403c0e0b40200070050000c54031800c00310341c1c024503d0360448009200351140c02c0c404448611804c103090581e038020301114041400e10116a0050580c0c0c914030302030214590043e0009035560080900c1000320350348500040c110701007401402c080140008209901d0400f504090a600006541c80410a4a40401c1800003503000c83e0091404d5412214007103000300002c903241d5040402503010700d841c00d121182c42e0b035403000900e88900d98090883e41c014401c001080394040d43c80098901d00e074a252242d1120200d040d4118540440d41d0302125480001030200100d001c4a1302c1541b041c241c650070040c2c520f15101001403143c000038003110002c40ea410004002ca28440c200d107590995002c4013140d45c59440c0d04002200741c01480000c2080c0070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 408213525 1250 408212275 408212293
    0x3080304060617061006050904021c15060f170c04030206031816050a151110060801051503150a0f060b0c011505010503040f0f060c110d0f021015090504080a02 70
    0x740c00500d035031103080c003c5803030580f85d07050060468065000e00d5a07503901c190203000c240c0b40310b88503203076100c90041011400525100c84a8000210310400c1c0d11050074007546035513505800750028503040410440308031010b082c0d500c0855101060045801c00b82d08954003004020511210700c1a41d002841d0fa03404a524a040d0003c40e040e80d40d5207400b03155003148480d4010005494002c000700c52080c403074200b10141c909071880d000c0c50b1020fa01031040e20103868110422800f138080c800c4582200809084031039030030351003010955404074540000d04c40c207880d4000503060290340d4081081000d025809001940d90303000326528581120f92160b043d9403808441000d0f8403003019100701214410f858440c19aa62502c0e41d41c0384c02c41c02e490076120701d445260f2090000755070380b00d01c01e02205251540f00c44607030041020303882d020741c0e00071250a020407103581031180ca400003401c8550015000011903941c000c5106006444582c0e4042c555150515081c40100120100a80b0601600717601320f500e100303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 408214775 1250 408213525 408213569
    0x3070b0f010f0e180d08070906080412230c0a050f01061d040302010b03011404110a08060a0c0c0b010b03010611030405090112030c230c0d0b06010e0a030803040606 72
    0x1039028407400041008044040000e4808210080d91014039200019602038091080c0e03418103140d090b00100154058042040190300700f919000648018079015446103000d50365194051080800c0d031040c4095200280144038114060004010700c100301561500c106007552079607441010400c460700c0c0138503000c698030000c0500c550000c8803110802c03003c00400f0480c0c6d061400c24054800d03000c40d500c80a51070a691030900031580d002202c007440309514070b014188003584440d01110207102e02c0032000100450700b0005500f5400c581e00500000350900050b10030f58403094801c50040100d540072000094443b42c16020314100c034099224581c0e1062414030b56501c0780b0030350180c940d100d0b0701d40005009241c495060640d1080c13190418815000340350703c4100a12076019a420800c00012100c0d80318240309210f0f4851480b000c0c6e46140481030300d0f50b100c1e800b9407001045941004a44160074006544900700c1000031500405590350301d04090400c0000742010307000e07842c200c0b120411300c1c02d844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 408216025 1250 408214775 408214801
    0x209061927050f0103030305090f01060b041502160e1009142e1503020d14090c01030c05120408040506041202041508030702040515120f010608160e06130e03070b 71
    0xf0301e40011190010380c00e59400750010180a00101c9251080c950409020340d0240700b0000580f5013901e80d95280e92a1901c2d039543d049001c40f100702190032582c0112025102400c105041c2c68200b086802e69a0b1140301c1e8100056181e80400400d03070821040310683c08564a9142c081c41c00100000581e184104840c0c1240d0740c07012980d00e814a040c1c1c810007145480d12205814a2210701d000351510107440c11280c03d5912428003158a0780b1614240004030400700f040b0b41900900f03007402e110540d203c080103030607800361a80308902ca0407000002420030004104450150500510b1a42c0700d607203070300b180c20b001104980c00720300030713450080301d05560a000341c0c0c00c80440c0c10a0340107524141e46a404c2c0800360070050081e800b441d07034a1920f1016503445803213901c14480d0140040030008000c080041c2520390f40e90005a060b0000e2880300d522102d403002070300548008008000d07071502c0e200c0108940300c1d400f0b400d070900185090045800c8040200003482014050850301c440b40e110b610000d600c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 408217275 1250 408216025 408216031
    0x80702090c0f041502010906050103213e061603140f0703020c0f06010b090a1514071401090609200906120a0f03050408060901020f07020906192705 65
    0xc444103000030468131070282c1c000c41d5002c00d14400840c120255607510320580d003003a08222011500c41c07581c2d80c0c411403124080c800d010b91616140c401d0030302401e8400542008000004071319400c0d6240030342c189000302c660981c441c041e00101c4d211464005400210010303009103410019060441548148004440041c0505003010243e55151680c4c041030380294000740c41c0c504540a6030044040f20303001400381302e0092400c13201c4555904078003010422a9001504626140c402c200b070a011101c5c0d100125034002c0f00401406503403416a800c203500c4410601ca4502e0440d8242a8001c2c100318071600700f44c010a00c20255000703440203011071703031001102100c4803a802c002400f002503401d11305513110480001000c8240e030f1442d0300903141c080140304240b2060700030500005003001411803c0060651101000008504000000721024403901c20340802910800b4040f0124496a03a40001c43c402c07424902e080395002c6030740301ca00401250420300b018140d060304040500080e0028050030384 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 408218525 1250 408217275 408217297
    0x90102070b09181e0403120c090e0f0612011a0a06170f1806010e060f03120702040c091e030c0503070608060d080f030921040620010f09080702090c 65
    0x1551041402c0d02c1d030181500410014000c201c0b00754005000c01d0300c2c4d044030b020368026601d145400c840300f011039090390001c450150030881c6807041017011003806c0c2d48030394000c403c191800025455080008080031810b24a00300380e5480e0101c421602c9100d012110025801031310b040b0301c1c0d10360741c0c00c083ea109089410403c05d8190040b0000b40701c04400122283d2114151200d590413442ca03036107440c40d08800b60407034520701c64101d00340850b921b444548040994011401015401d01807040c440d07983c09030403002802513445610003c4107900458002d00549030003d041c19075080d40c440c0200700c0138814403040c0e50030888110007145501300070985c641902c039107803501462a00c81c0000d000700f42095420564551109001040c11040100c0082d405101c8410080020440c2da02050440903c903520740b9000707140400c410044243c00040700d207200340009003407103200101ea00c0d4079809040c25282d495100c61030100c4c07030700c2004405005045168025150200d0a0751080030303420242c4100e04c0204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 408219775 1250 408218525 408218539
    0x506160e0a2402120c0102030a06090e1e0c1008041a090d270e01030c14090a020a020106210c12020a050d0827091f05010f1404060302090102070b09 65
    0x80e0b9090710181406241100e481210014550540b0541058004100d00d4000340d40000c18000c01444500076200030b85601c28042023440342c0592a10340e180c0052415010b80012041c1c14446144d052103003a64601c006041d02c80c0d070308078840c80103059010441d030440e89400680e5215940030310450240c0d00c03454200004100125003c081034455452020342d0514060036018031000c0a802080c0e40e01c0140018142003e07194114a008800d9003015003120f00304176135a0003605915507581541c1134101028000040c1c0c5d030240200102d0241a0703a8000e0720301c0340304440755200442505542032070807902604d4101d0360785e038540300d1060184030790460180d03200e903480c541840140380c14480d005119114055070340c035007443c1c60003600350001112008843c0780032400305081c1904100489a6009101c1c400050388a0240c02d80c050780c22584e405000e0422070000c0012040c18043c076600c0814081d007140907500c4580d289402406548007181203801800303161800142c002c1c07034500b42c0f070740e80e0700c010b01d55 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 408221025 1250 408219775 408219809
    0x3110601060912051f050103050f06040b01060c02041b0e0414010503073c050922060507030f05190605150706050c091822210c0506160e0a 61
    0x245000300f50408299868082d1003542d405440760350f00380c000002c3c482030f4041342c1c175071650030601d051200b90a10612190401f500b0880040e9003901002d05440c1d403828803c940e1462400450300030b01c222161404c0c0340d804220700b10741c1c0c203800100918414004071814031280035001c5060710030315420721030150103a200307110920940c503482c0403d6010b88118604803000103020088404d140c2020070060b90f10030003010007840b650804884481d406036210190441c840c1100300280c011040303012002c3d00c0e00382d880e8040b51100780701c1d0f0003240c0e01466840c0140700310305011400e422545281003d4500140c0303000300000f0542400601c9241840d10001038a09000051f1540c401401c0b004104442e90403040089640c1350381c9003070501e102454000d101c02282d1818110030008802c0c507141452003246001140030000380900d20000c2204020084001c203104040c00640e5087d880302002000f600641c0c042140809015400b59444d0400765580d04110322144140704c458012030044095088070304000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 408222275 1250 408221025 408221039
    0x3120501090b01021c0c0b040308011a16020118051017061c11040b120109140606031908120103120206070f0c0201081b040f0e0c0903071e0b04060804031106010609 72
    0x9141310700d294141420706c201d0759035440001d94400c80e011008103189000500c11802400e00c508010300c10510340e140f8004040300039002c0c450081000030b0401000c8061680b444003003a08004c0245006003600c294a071510701b0150174250202000c007100b10561000031514503080040f180b0300030300c407400b005150031991503c0d4041e0003e8031460382c0003521070b104c4440c10f80f203240740f0006026840d000010605181e01e003002c46811801c0103c0d03100d80c05001403105981d004100782c8101400030f00d41e880c901505213010000344c012485c003648040082030001080c0b03c91251400200c1800c2d40c01e9924543e5a44002d4844021885003800050100c148030350065000b505001d400c01c103410083d22010f140f03240801070030340c081d4104642540e0303060010002c21100a500e96008080c182626041004000201c1c1d6101481e200340c000c84056443c04e07140503103404516401502441082075070b92522060027800c0900251401c80c0052025801c02d001e940000c101a8182d880a60761519440d29042d8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 408223525 1250 408222275 408222313
    0x60c05030903060406020307020c040b0603010b071502070501060e07030c12180609050f2407141b0303062b030e010201020f07050d0801050d170d110703120501090b0102 74
    0x50495291204206021459074108080e511480c850b03400542c6e0307450b003080020b0170001040380c224000c50602d59000c00681d5118140d90644100f1070324203807240398506041000708c44403001c070140780d8800a601010300c41c040d007220381610145981c0700001d8640310811000c0f01e01c01c401400005400350f1014008401c26004002c843d42500a04500c0741300303a4070790f6011650700200c216810b42c880c01c024070303c41134107001d41da040d040034880e109000c500350402c605035441c006004804100b41002c10842a0801c401511489010403074943c1030007190050107641c1e039000341d900381e1103000c1120245c0103000035582d418100c8250760f114010051915501560406200c007140303070555409200c03480206201101403c20f0300e00500080c040070074011030241130200c0682040740283c3c1503180100109034003005e0b52800b000c0000c80140d8481c803241d01c090040c8001741c4c44040e41c0c41c0016107d800d1640c404140b0b0528a0440c0b010440b50b6a0788007403600310760280214601582152940802d1806484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 408224775 1250 408223525 408223547
    0x40e070302131d0901060906050913020a03051603030e0603130b060420040509061002060412140a02010b03010b270a0f1d0d020706170603150901091a010302090106 72
    0x2000c03001d02e5440d41c10322074000c030500304090440050002000211502400380c4030040c00e0b445410840d0904040114000c81070061500b1000919445800f04545456820000464112060315642103621a130005511114403080d800101c0303a0a25a4051402c2d0003181d0160485004090041c8034990766010310b070340010481c1d036025903510002c8011101076000b2110894074061920354580c2000100b055420001c1d0482d40602d80d0118141d180c1500010354070740064002042d04003802420800301c8919184c0740c8411300441c1c02081c10081d003501500400c0e0001d0f001c800a00c1642d21a9060040c0c00003c4030442660203030403c0845185071403105882c0d0030221209010402408925001c1c0a9880e070181d41051800c1061007070303003600d90078020141d030940d851000d000c2c3c1d1440c14030001c002848441c0100da9541d10720010a0980ea000c0040000448144403290040d2514246090007098101000d85080c0000ca00340fa043c100b1850307466044e658010700348030f2240d081c80c800319003050040c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 408226025 1250 408224775 408224797
    0x140f041e050f1804050c03160f0e0c03040f06200301081902061c0b18040c06051303080a0e1305060319050d08070210141e04020904030e0303040e09030d050705040e070302 75
    0x200b145209162408e001c01207041068070702c011001c17860135400d18204103a9601c050a81c00780101030103c2c540001d41101d41064001807900b44044c100d0178440c1c020241604441103041004030f100c0e1110040d0405141218040f806481e2001c980041c2c0785104078100000070b511480c1008040ca001039040020041882c800c580050300c2542c1102140c1d00d4141040000e482e075441400300020420075200c1c4c54080e00c00b40c03800c61305002c4e544c0840618681325010082000c03401060b005081c03841030505205c000700c000c142030508a41e84208034000e02302662681d01034020402ca0711207024095007041d144650010080080c0c0d40525412540c111001e4a210114022810031020400c0b40e0b0040f1030070401103a03c029030ba410300a080c1c6030144050940c1d142c40500e03400030072025030342d0420000d500980500b0f041820228500c002411803003642c1107001c0d1a400e00c070a02c50004800030140101540070541000b2648030300c0d0041e00c0a005510560008090380000640c80e14481e80182200c4815 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 408227275 1250 408226025 408226033
    0xc15031a040c09050d3c060903031e050105090105030d0503011a0c0f0c01030c030c0c030c021c03050408160e1b070c060f031a0102030a140f041e050f180405 69
    0x40e440001c01091682c034003690075a40c0414103c00c403ca210b12070015440302c00307544101c080840d9500500103006d101014100760750b03c018140915000e41c1280101010303040c00c682d01010400404001858213018030340c040d118800001c516424000741c0b0501032101034907071078110381c601205140c880c1d1441d5900303c0d40c0f440c1404101d0015804010b989103c01030b00002d013040d0308250000400f25901d1103030300010981064034080300c25402540c9051450740510b4900c4080005001141c4428241413450840c0399100783d02205040e84a8003400944d88040261818428000030401807821a40a0040201043e0300841c1c3d0070079101d0070480d8080320300b509142c1046115114104908070305e501c00d40105081e0603901c51000c5e4140314401c029540d1486070f4101d802e1600000356a4051140c0340030600400d100390b02c02000c02d01091f107001d4042035240c955031303e44992149200c600700c2c601103100458903a030007198900d042c0030349003071214001d82642a80c025011914140d00006042910a401 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 408228525 1250 408227275 408227279
    0x21c05060d210e06030f04060f150b04180501050604050904051207110f01080f0106111906090312020903060c091903050c121b0d0507080106030c15031a040c09 70
    0x81c02c84401a241c080c0c2c80c16202c0450b03151500600981850741031944504010000c014505580150707031600079811143c00070329010301c014050b000b0300442440d071410702e10285d400640a41404020815204c00c40c0c5d042111070b41d0030f190041a02c40c02c0c025180d100805020500860410b8000703a54042e0158044410500340b21040d0605507004080030f80d003d525008020310f450910201d240c0001e032003032800d5031403881c0c02d0480e05491001805520100320912888980e480e004000584101404000c1402025a5031038420014101c000084020038408050704c6220b9601d4400d4400c64130b8054081d01c1c003950380c405c1c0000c0366482080d403940c1c04807046085910141c80750031880040c1d4410740c010710310380329450308112070074407810030310103ca40c00901078103103d20031501d11054001c404d60b00703500118100d25065041000d980c200000941c60090004240103555960508a4040076151604d000f07490504806540d0481c4400070040c070418184020341c00c00fa400a100b9a0760f5240c826100c507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 408229775 1250 408228525 408228533
    0xb0102070b030f06090108191103070906080303060306010f140907170414060a0c021216120f1205060108060d080409020a0507120c0b0708090102040e28021c05060d 72
    0x7810543c0d07203040089000c01001818104052014094070403040100750304100320781c51021155444030001d2411b02681130841d950b03242000072202501001c80280183ca859000040d540d40048408920a100f120000034000300c039030040600f628181c40030900002c8400e814032901d094040c105008008040c01400810302c003d01201b405240b04071005001989003503406880c00001070804207205207080f04a032403568000440301114083c14541546032201701d800c10034004a444806003000e100b10101258050340001405210700c07442e101c000e000620f10400100702d4000701d941ca070105030b0a401245040c07074880b5030700302e1340f0b440b850320f05207030a80f0b40c0c00ca60140d030040074460380410700214a9800708001d41c041d40d03030100d1443c034048800104545850701d0200c1c004d0000b1050120780004202411002e4045802501d00090100c0260270711468041d01000b030501402c1074090200c003440d4007800031b4000c9900440303074a038003c1c0000d10000c40c418001c040150025a0000485110034001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 408231025 1250 408229775 408229777
    0x90f06150a02210d0f0204150c15090f2a0605091306060e090108120301270908040303021005010806280c09170109030c14010b15270f01030b0102070b 66
    0x140c1c2185440d1601d8451308008801642c461034808102c1300e00500c0203100d03c540c10f16200000303829514004c01310302a1801c017240304890103100706c0d0384181496050f00a000c00140400407152107018000004104401b0101401ca2000d802d00040280c1070400c1100601c102d002c1c0010110080541c400b100d5034003001411182c044e440030010451482100100b850410f510074010321040c4060310b90414074104a51591105000300e240321682174452030078000315401080004040c44104001030190340c2000706240d041880300f1001031050003d61081d0001d54083c1604a0340007030000c3c074a82d142e41005404a00802c4140300350f142d612220600c12640034000c4030031801d01c9403a055032040c00c100d101d43d000040180c078030755168100401100000c0d84005c200700415005060b8040040400d8903060241c807905640e80c1e48010b0840d0800029002040208441008281052000741c1d1514200500755003405e1003e50144d403c001d07051695000381c004804001052040d502c0203500c0320150307082 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 408232275 1250 408231025 408231073
    0x70c090c17011712280c0609081207021902060c010e19030314040b0a09212c030a0f0309150309030f08250509030d0806090f06150a02 59
    0xf401c400241040c0c80c4082403001e20400324041110034500300c800b1181c59001c6181c08446110100034083d01800940315190b031444c06980200c0500649078a4203041c011a041100b00035101d032000380100b000d807800000c1250000f01c142d860215006c82903000c001d140d4010f400062125521806692241070050020107101c514149040051100341d0900030111418002030200c201c65080c02d2001203804140495888403003210003144c000307803500e002c01ca50480d0545504400f44500c4000926a07008000c0b0704031050560001d00459055000d01c009a04413004e550783c01da004055148003203a640140540a40d00a0900e80800d0350f4036100c41d40c201c08035072444d40010303641e00110010035602450f1144030508a18040354181005a0070101490a550300d41001c486c07143c060000071b07030182c810f031050100010191044000605c0000d8014641140c001d07201e510001d0004010000356501180907503000b030145906800003000e0016150b220350b54410546c850b02640000600c007802813039807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 408233525 1250 408232275 408232289
    0x2806090f0803070803011502120c03070b090c010e090a06030507081c050301060e060a030e06010b0c06090703120f02010e0703030f020c040e03190903020d080a090605070c090c1701 79
    0x41058900384011030050001d03000030540360010444100480c021009407410b4803820801000c2c42541c0d120f060b4074186080a55a004120200f12045036040120180108c10300905c030070f100302d035139100640d82c9441c0064400381c00720b080c40350036600c903080c025007840d0b00074615030000030503640b2078490925009042d84040c401d0741c01740304680a41c5806290114665003036040142c00c40d41441c02c060030450f00c000e0040e0042c0000f00c0e080304204d12940059550200000642d040b0b56117130701030041250b00202e0400413074411480405c0d80c83c407001444904607608003d40325145040c40310100d4032008500d10b0002150340350a441c2d5120001070010000440c80b90b200c1d20301d2001002c0010f4180594010210301c2a85050115105400d020045404108180b422590450342c44c0d08142c8000c01d1582010b500041000911030401080744c0003810500340544814000c607076a020101e40610405070b0050080035400d00c2080500386540115490780d01c60b05005120000d0190f11051f80384090703021070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 408234775 1250 408233525 408233537
    0x30e0a050604030219030e06030903130b0406020f030f0a0e120d020a0201030501080604030905040f0e010911011e09032310060302090903040e0c03071812110a0e04022806 75
    0xb108050b0104498140035440c101d8441d010391903070310098a200448400c0c42c0c01210000700181d030f609810f204464080c0035940d01403210684900c400c905a411070f0150360b003d44105000040000b1000064030f42120085013001e1802c4c05032030040f144844408103c0383c20400d50a01e51640c01420320a001080c01164014246072015000040980c0d00c10381c000d41c4503820080910000c242d001c001d250640b80141d0700491100140c07402c8a00606000c0e80c1a1800c0d4686030813002082006a041c8100d40800d80e20316244101003040c585280300b0744075113480030071811102080060005114141240c2c81081d02c0c4100c2c0004074070b12410308038454060540c07070b0340d038132402c0c1304501d000c00d012034014103180300030b60400d0300b00b5100c0203107901d0140a003c51242e0100c000782c003203071050189030354440901c080010810740e510b6100d0030050f58150103d481c46000d003401d2000341030402424040b10f02045003050940c546409020b4062442100d11f11581c51482d945051010200c81c034600500c0680d03507103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 408236025 1250 408234775 408234781
    0x20d05030a0e040501140909070f030b0412050306090a09020f130b0a14010203090409060b060a090905010e13030c0c0320130207020a030b13020904110102101e0c030e0a0506 76
    0x1c0c42c640b0621040351141d49040c0040c040c10808041582e442041a2414003080c0c8400c40c002d850440c3d950300c901d1080322034140120400c000380350200c0c001d034481c4410b24042d100d0f8400650780c07030200301d40040d00088105e000450306002070b001020310900203044062864460404a040001d0302030345485001c1e210390600c01c19051100503070000b40f070303c894a041c8032610400001c1d105d1042c20b260390b20858442c041349041c80700c9503004200c00c0c000280700c10f0b039540d00c40d4001343c5652a14846c6088841c580000024240b000d2543e451040140c22051034940d98507a07426650588002015613400c0800d1070b02000280781c42c04007a509541806682443c0c080b04000c10500e030390010f001424442c01030000d1401a1940d2510100b600d9002c00504110307501d01004012000c0403100c06075000261505220900c6050300f00100424000e80c2030315450000c0d40860415200b80c14140c5801c4201c04030340700c410702c1c0242d000040c00061450f0104881540180b100e180540d8941c041e20290408000c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 408237275 1250 408236025 408236027
    0xa0902030d030b030c061806070b06030609070e01062a030201062102090c0306031203101d25031d010b0301140c0a050d2315031f0906020403020d05030a 67
    0x5503103100501e18040c0028510f03840401c0d1100103820201c2e024120110f14100d00e4404000e4180c0c0071100070b00038944403003132402c0c40e02803814246e818901030b0040c440410b0034008081602070994100e543e050200764a403100840f00e0749404855180c4c3c810740d100001240501100b0700034000c1c0c0c02640082825410410780c0d20744c42010000c1c1e1070010b09000c58041c0143c1b03070b194016612a9100140c142c40b6550071010074100120000742d04103e40300001040001c029641460060311514148041110031000b00031000020645140c000c51034072000c40079002c9801009561070115502e000b00703c42c1c0000c201c0c01c00040e81d0900000381a51594410308060030309102d8a25140b170904041c17482c5003042c13864540a4411103112600708400003031028040d80c910380203603402d04040404c2c80c40b8440140500036030380006448010149580705409034051900198244c80c0741403100c007103000b170021001140010000342c081221510780a110000150303940308020307a03005004601942d6074082c480c80c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 408238525 1250 408237275 408237283
    0x2090702150a0c020619020403020a06030e0c040216060b040e16090f050601090303030507050f0d02030601020c01020610090513050303070206070305090111030403050304020a091104061b1205070312050a090203 92
    0x100c0401d40781448038140740d80d0000300c10b80c1003008880101c500d80d140105017001f9204a40020350851100c1000086180d070541c800421a2501400e646500c0360706020030040c1c1c82002d542c180c40c05000b0030b041e400300d40c00b03610450000304010b10029211245a041034240114a0301282070503080c20020020b168460040e03482110400008012034039000001a0101080c0e01010b010107560303c00092020340038204585104080e008081e4407003035901340000107940102e50050060081100c001d4155000280c0795015031042140c0c0c0355040d0a0504c40001408010302d0454010505102c920102d001480154014486a8042d007000e1410040c0074003030300e001a0026046a00d004603580d99180a0350507250060b92629043c0d5036030325940000f520f211f0064010500540c80e00919480e420382c010021310071224652900d1811800010403500a20349011002d40307034a041d140046540c61061000b400c100f0310904120340c80300d02c00140b190403110220380303145000360756000180661070104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 408239775 1250 408238525 408238531
    0xc05190518090a1d0a050303160e030304090b03010b0d0209010b0705070e1006080112050622051506042f07230601060905032b0e0306040602130b040b040e0a090209070215 75
    0x1d0005d00d52400240c3c1c55558a101c014503040090800c4040f0700c00c040d01c1082c5c0c0e0709450a00400322600d65495802c82c000a01015454a10039071a00302e841ca0716003041c4444000854000b08a20600e03032800d9001003403544811021a454010207402143c4511011406070080d200e10210304851400c014010f0144041a000049480c0f505c99030300000800000305103600c4820a00000000c0c041c444051000444490005047d030240c028081112502e54042500c00c90080718103212503a4000b521101d143d60510840d003491010024200042020400408649216591400a049503402110f2030000c1001c02040250006001000519401501c500c05490b0403400382030050034950b00c00c454046107004942e8600d64002c1c0122090780203a10a00740e403080601030307512500d02858039030001d500018000740c40740820840410744541c80760548003a1a0325441845c500780c02d0410070341d03148400400b05210103842d200c1c05001030b00c9105000c1d00600031038000b4019071322400100e8903407007002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 408241025 1250 408239775 408239831
    0x90d050c0303060f01300c140d20031f1d0f090f0a1103060a0606020a03081f120b0705090a05130f1401090c05190518090a 54
    0x502a4410059010086a4001070203e4007250b03c2d010f04e80058030765000004070004804071b40a03c0c0e05408200400c211050300d100f00c4100202da10018054980000c01da4408064200030300c1600ca0225940d40000309101040f03940e40c861101824803030b112a801100c0d41040d06404280b13544010814000d08005402110342c202e60a40b51480034007445800104040d60b00b10140e0085000300d4030038491030400c2c024140a41c1e810307003507904201144400541c1001c0c000d03c910301c00564440510310030642a0b4406a01601c0714541c2d6840490340e1080140a02c2010701100090b0000a80f9198405c001441c0324800c1000b00c21060074071003010700006022806014080040c66001c0d030302c1080000544e101210108942c54001c031607007006094030440180e1544c90128440d0100d541e05d42014120b40c90080e003807008800584e02181e01e40140c0990b801600000c0d40603924a038003d0f00584090740b820054103040c0002c007000150311000945080750724a58426001d9040180c214050010910b0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 408242275 1250 408241025 408241027
    0x201020301031a061206070f0e03190803150a090b100c080d020c01090624060306180209040b0a0308030105041d0604020f1801060909051f05040e03070501060e090d05 73
    0x50b60702c0e10250008500090f4070365500b40030004250f03640d0080540f04402080044401900c1d20380006030075041001d00030404178030388200340d40c058035001404000428500840c403804001070b45da80b5000e50005800c0c04040d0540c4501c80c030300342d2a0390110700010803100d8000315600d11030700c046c4a40088040000f0341000b121010560100303240c08202c807504001c0480041c0d40c1d0780d1110300b46005241b2510000c0207a4103103d1442520040c8142d00041c00b91441c0e00b1041c13142c0d641c03800303800f180d001c3d00c1506c04031491094071881b07141039540500001f8001a00104040300600c000424940c2203800844140802000600060400d07100305040b203c00340c640a061418089100f5955000042000b4406c0302c01c0c41c0848050344404461074021003000a00110342e50b1100e5024003822414081c4008042c41c0000003001c5040c00c10200084c02040b10f2641c07080750818040c00043c0901a40e42d804a01c400c200c0440007502c00d2280b075004050000555002e42000c809041c2012100e019200030008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 408243525 1250 408242275 408242279
    0xa030e032e060b032520010b03070b28090305060f180106082109090c040302040f0209090f040311071202040e0a08040b0d06030b0108060f01060306141207080d0507060c0201020301 79
    0x2103400102e45610004d17040404004804040850310300c1c20710740002c550000c00c0600c00040820541000a10410450076122081e07200e0f00500c40c203010b03000780c9940c510715842c180c115255017110300604881d440c1c034211140b0b640f20f450b02072603c2003d40e52155400b00030300c01c101c06a02c45020013002d03070010030001d06c012481c0c01302d2142d880641c2c090070105c80c1403000f00c09400704550400c0303460f12a0701601400c030510304800403c00d940c000e8842030b8092414051480514203561081350404d2600400d9802d15860f504401005804001c104400740180f41440300318200003001140001c081c0c00f1642094560b040c0b060100355145940c0105280d480700c06410001040030050740c00703403545440b0240e00c84103420703030340400f030412a800039000d48090b400101c0c03480800b095540c415001c07150300440c903990303503941103040700c05500c140d5040c0c2600c00c680405501c0e0012400c001142307814110340d1481e89a03468a404c10b62407400c0ca10201e00c002480c8070030001107001d001c102800d0f030300003141558 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 408244775 1250 408243525 408243541
    0x5030c01090905060d1a091501120f15050928031b0804030803010f2c0105190305010c020c01090e06030d03020912070e010f09020c0a030e032e060b03 66
    0x81da5004000c0c5a6481c0c0000507220341742c1e082250b007540d03041808440c04403442d00e406085004244e400d01139500034149003100540895250740d0480b0b2041204000807121516980035900d84030504907030302e0051042091150b100c600450380200042c202070141030101e015440150103280705240d0201440800890110390404040c04a65140c0c81003404400b105140201181c810740e040144520300200003c00c03d485501242c1c401da61904803000450300044903810b11a800d1079002082d40f040c0c070001400329052040c80c000480340c0a80c149450b6540760390f10079003961510000c11005901030312080320150b920400d408000c0c41c1c581007803011814044046a124410304084d94141034001520328080c2d11b5900049040f500400b0648105a0302c5901d070003c1c01c502072180d406031480344e14011071241031501c2111411500c110042440b1070256405a5100840311892581401a1241c1043c1580c3c010041104644007881e1145030f1065550050f017200c0c17685d0041d01001c1801e008200c0a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 408246025 1250 408244775 408244787
    0x3151d03041517040303090c120302160602011404080a0e1509090610440a0605030f0c0f03120a0806100f02100f0608010609090b061c0f0302030d0914010605030c01 72
    0x413a80503c0c0c08079400360541490f011031800ca90115400f080480d401c00141540410700c40c0c407c507540707100081c8447e5100d0007203003600c42030034601003124200c00205000a0388a401025003400a0421104c00a4400e00003401c2f0404544041e000660004906c0700030300e04444102da01c60380840c1c601c01a0382700e0030710003080d54095000f01000b542d0b0040140841000304016600600c0344404049240034194221000e03074034060310200c081c80c3c100100401d9610340400c051020307008a00003031403000c4030682003044610b401403541c1c1e0103008040d400040c1035400401840d0a0030355441e00607160034202c00f440301d01040c82c52404108402002440000c035404240301c8200c7c0304070780c13002c140720ba800811079008101c280c0c024022580b80510010700b50a02d900641c150341d0090200383c03201c1d0b88a0341800503e40301c040d01000d968903404007000010740c114000c0740240f40644110303420021110700400c01c544002405803038280ca541e56030400d408007400b400015200a40180030541c80c6400041c0c82 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 408247275 1250 408246025 408246031
    0x2040f0e130809010c0204050103030f0801090c0e0105211e0105030c0105040b0912011b170705030c0f0403050a03210903051c0908030a0617010b060403151d03041517 73
    0x1009600040542451784100d0300c1411141c2c0041042080e96504c2c640601003145241c00070300403038801800025402000d20803103141421540382c910794080311f00e00450300d036801900f9540200307400f110610058500c04164507c60f40c00c00382d8801140307851b881c500e18058016480148030340c3c0000240a00ca9034070000780e42c22514100101500c441c2c1541c0000c01070003442c0711043d0700d90318140c015410880f9036074440005c0001619100710040403140d40048950040300c95901048041021802411100c00145940c000c208412820503031039580d40c6050841d40c5c102980024941c2001174030f9030300842242c82030603004800c03c029551250b6400340903400741c10407603001140402150305804080c0d4002d03c0300585d010600d11b60764070301403200500a15042c020601910740410382482d230a041403003820303900400100101d04042c0345590381d5034112000c50204000075201c002c41540e4810080c680350340d0059400145032030b58140316100115042d81c031b4058003040451210901084001990340e90 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 408248525 1250 408247275 408247283
    0xe13091b031b080f1f1b021b0a21080c01060b0910181a09030f1c091202190e0a0b09090703020a090b03150c0705150601021c030e070902040f0e13 64
    0x40000030f520581070003014814002003401030000341b546c541c10b502203166440144c298840410072041481880100d415078090888050001c583c025a01050a80e01c40d202601c42c0600e41d1a00d401019070740d0030342c0c00c00d41c88074030100c41c0450034100d01d00e486000c1003d609098504102d980d481d001c40d90005046c00d125043d90080010008130640750400d041324002c40000d011a000b005010b91a190b0701c0a032290b1624034402c07a90461000d2030312441c0120104ea8206d40b01003030800c0d5039002c200741c0000340304414600c00344d203c000040e690285a0f4148c82101c000c03000182c0c160411090060707035a8010056400c581100009200580c3d6842861003a2109058001400d880c8032010038603004401000d404e00c070882c0c0041203806000074000300741a40c07040b0b040d5103100c081a512481e540b002603d0140c0940c010a80100c903c50b040c0071040101086441e01141b00b031490a4440d00701416a002001640e40025003804000884801040244040200c011080c0342039141c20351035145041d4014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 408249775 1250 408248525 408248563
    0xf0606060834030f18110406121209051203090a08030408250b040308070c06030c1205060406030209090d17060f010804080d05180606010e13091b031b080f 68
    0x2ca18203100358001151010a002d080103481d8240c1e102c000d1601c40100115030550090328030101a0800c0d000c0d010031100031094241341e007140380c0d665800740c0c0750400320513081101103040019a50750f0625505000e80219004c3e550300e46454044c01314000d5281c01880d040e038000c01040103c60400502118504200701058951220002c40c5c00e03c015410380c013075000801c01080120030300084000a00820303105416920000e56103500070303010350b40f144074410003180d074045605000c0c0e1100e8101590041000f800090079075101c0d80011043c903415503000207a41d21040401c40301c1c1e504003a2900c0903045265a108030352400d0320014450782c00b892a00c0c3e0401ca8460003082c02c00200c5401e0390030320200c041080c0715518dc24862036690f5070741d078445038074548200300108070594000c2c0ba961801d018080e0007848005800082800a410401411103001d203a034515401403000361520900a14400c12010200020360510346480c8030f440d07001036100303401c40c548001c04250000740c2c00140da66003d400e2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 408251025 1250 408249775 408249871
    0xd05070219050715020307050115240807080402030a0c0603230f0129030405031e07021315030b0c0901030b180703051302040e060601120204050306040b040f0f06060608 74
    0x700d040d8042c910006001d50b080902c2e0780c6414120b00ad1740c60030364002e0b0300704024040c40b10981d0f00100041103030b030002080311200440d0b192446590240e40c400e00190440d0100700f200c0d50f80e0300e00c0c40c005a1101000945d525540181e030720700344a015003001d1803014030019a06140c244000d003800c041c41403164801290319440c201300d65041003032084241104e41d05480e45064202140c595004011001041c40226582e461051130342c400d8a0580b5006408083c80f441c1a11081000b80b02100d1402018609040000700042856200714031810002c280130740c031a0130700e500140549001c0001c141c86801c038440220080c0100c1000140d00c16418680400c190f200d6500402d40e034001d4013000380d001424020030310300c001d0b800103c80d03005031002c4e40e0782d43c0d07814415404034040340a5805815410b41125000c02e0105207081110360704140205110800ea0038156140307520414104011190fa40d1140410028181c00c52012075115018001440c2c8410b00d210142071000300850320141440d03102a51 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 408252275 1250 408251025 408251027
    0x1407031403220503070b1006020c04090501023606032e050a03030807020c03061909020f0a0f061d0604030303090c05060315040509030f0702240d05070219050715 71
    0x14800440c01040c1d4000b00c5100d07141401c649a500084007900d0200f142c001040c000d41454959100300e80581d0b001e00f82d403c4a88080101030a20040d007550299020b0284202484022b61038180614103e5410349007868081c10300c012050001002c2c5e803241d51705008000b40344c0380fa00050442090000b103489100b4451007088060322805400c21a0812031503103006c004c058200071007030b0280003640c00303c8540105d1001003540d10300007142c200c0f26140c1d4001c6a5180c0e40c06942001e40781a02c010141032012284101080c0d12080fa0342c0101003400005004200680d048909103501241c0c1d0318400d8a610b5400c03021602a110301d120007000c066591126400f8000d01a004501030440104642d550382800e03c21031700007805480346c85105915120100703003135003400000c45000701485da40d401c0c1800d980e502008448007201d9004e0f90616403560400d40c9030154440201a200168680007810b030404103402440c291404d480e070303034010710340c01c45090118a0001d10b800c2210800c0e20304080f040740b9254 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 408253525 1250 408252275 408252301
    0x418030c05120712030e07150c062021010302011d0d0605040507080d0801030c0303030e0a0609120f081306110c030712020c1f030504030905100306061407031403 71
    0x10201c0d94400c0045a03010070082c031002c007124942c0c4e02c0da1301442030340448000f161300c8241300c1c400d594981245c3d01095a02c94018036003484030034010040026601503e104403e50000704244110301081c2c0010010904120808100080403000c50300d00040e6045a0003c1d2081480079003010043c44028100c101310713074a5010700307219194001c1050140e0309007494101d40d90302c558060b0f00000c0c043c11620007580c51040407007604890700854424011881d5032810780c014103c4c1004841c17540a255410b4010600354050303644c40074401c0c50501243d030106440100030003900408101004010001e000d1098041e41300f084540c0e400180000342a5202202043c040c428204611078a01020810702c02381b10031481076107058403854083e41e81662143d800c101c00010780100481040c02000c41c003160545c443e610055102d803183c01c00c846a90b0715080020004400c00102c403000985940381070105560066818859400302d5034402c0c00c0940aa801030240e850003900b02d400e10001200103200c000c5119 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 408254775 1250 408253525 408253543
    0x5040602061906031217072a060603050a050616050307020312151905030118030504030b1b0708090a05030d050d1a0a080307170301030b061c061505010306050418030c05 74
    0x6401601c243c2c58490003820710aa14884000311180000000d10b8150282c0c140000b080c501d81040d03280c4110b1810001814050b82000b81e809e250b642e00d0100024000700003908100740190b0007041d062402c45003500b1164400440142006414400d008070076800100b076030249003c3c0442d10503e0340e14869511100c1c44005850381d4031290b2a183c808000040740c215009445080e8028080f1105001d240540710321007890080004d0400c010030030104000017541604a510103142c4140013503c0003c404003600821002d4919240015018560749420701900c1f00505003034000e4022465492000350903402210150205240c0b11a0004184900c2d041140315018000f40815001a01c810200e030f0b803500841802c940c550102c00780410484008402c1d00d04170780d4030012082a541d125030501803250683d14810b80124020f41d007140005206000c1e001c0c07248208825020043d1074140018103a50017070b840f06008a20f4a403a800740d100c0200201c803800317600b505000c0c00c00300700b0786041c600c0d01620b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 408256025 1250 408254775 408254783
    0xd08042913031e110105060f0a2304050a050a0b0306010305120c0f070b09010914090c090112090b10050103020c06010b070c1e06140c0c120c0910030302010c0504060206190603 77
    0x15805080003e80c1012600007a420781e040200810b80d00c1c601405804844440b94981c00440c14038208101c01d216842c14841d408840035260000f055000030800340c9509039000c07004540c4500c00c1010441d200d2081c902041c3c0200c1c000c040552550f00c55075103d000c581c450307041405001624403104101044400d540c40c0d003100072030b10090b9480301d001601c1d80090301031900007241032100081001d10241800441a0020300500b1103440d844044900c0341d00c011038550501c009050020094541c40c400c08201ca8010022440c0ba841c00c00100700500301c5070713000141410320501181e464100001103ea0548220000311a660320884c2000d106240d4150f0150101c3c14601b8a6200403c901d400404202c039660f403919012554038205250460107424a8203c80303510010100b03202e458485114601c40385410180d070340070f0b402c21000c1040340030121503040360029800020810582d09220342110300352980303002d500b840d0030048020346482014101c6003d4103c0c40c100c0b0714030070110b540b104000b5944 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 408257275 1250 408256025 408256067
    0x1022b0c08130305060105010809120d110324120a02100e03060a0c09050a050105070f030e06070302032215050901031407020c150412030c050f0d0804291303 69
    0x1140d9002e0a48190340c00200e54038010080002210f5010300078050040c420500039221000b0400c420080795000040203065141d00c902d0f075400d2001d0010f0003107000b80c0d01c2a8007820941301114030f240300d02890030a02406102009840c400c5c0301400b180d00103141d641100d44507901c0300c1d9032404482d501d01c050001c5038507009100074045008499840304005040355201c0c11030460355101001050340c01c0d1310800d4041201001000001038170164107c1c1540e1090400e00d00f800c81e500c0221b4065008004200c0140e44000f074920b2518181e01000510701c0c040d00544140c460804011001111540405a091000c0801d400801d0307030294212070801d800300d104031030701ca01d4607a2000750346200d01001340d4010038580045d402c1174508002110150388085140c1c2d1300c0c10001c3e99088456000d51359041d5207074052041c0382c5021800a001e0004008959a100300043c00c013401c200e400c08841500c521b0400b40f001c03006103c0030101c4807001c0d80c003c40043c0b01d00b0440c5084d050503181011001c403134196501e5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 408258525 1250 408257275 408257287
    0x603060510031713090f060b160b0f0408041a2214011404151803030314091902060703022b0228110d0b010311040b01022b0c08 56
    0x2a200e1460401c036401510507090340f05009485400d40c0c410050344900e0310004040c14407111200741c102800b48102e01600054040d40c58680641e07a81001d000002c51961100741e61050100901035641c0004a1010b0110036042554800c240d0b0311a901c540186243c00d1034004600d5658601603c0f1a0600d0a254a00e40f441d0641500740f008500d00036601d0380800e404480e1419445001c41d00e82100d0105015440c05041102e04801541c01c2e00d850000c10800c1916030880c10b00f40b54120009610035100407a125040c0400c400e00c5180050800300c4641c4516100302c0305a020b140c1141003e034064031025034a003250308003203052001c9185080074151101c00514040b6900704050900c103039040c0d0a0340c40008001c2c103620480076100d900381e0b14000d0403903495004103841c0400034038401c0e8024010b201c801c02c650f450010101c000d0f8005e440155002c11007514a08090181150100092010700750b001c00d01766500c1220544443c0040b0f400300e81103032101e50103001d141c0c405021900501e60300c0d1165 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 408259775 1250 408258525 408258541
    0x150315050a050a020a020d140717040609080a050c010c11030307050d0e0d020a0b09180f040303140f040b0603100623040606050a050703020c09041a060306070e0d020406030605 77
    0x8020303075101c0c0d5824680000a05911107078401e450f000c200300c1d40074000308550300d902100c0005a00d0145044020108043d40020329502c5403c1d85010543d0b0281352103030f25104010380380010701d5010000e00d1308010744000002d4004608646032040908002a004c407131403c044800815148805815110005450051100c0013032818a043c150ba9036040c0741000d0b400621280ca90000780080d0080383c00d45040c0900301d2000b014000c1484041c2165800c00703a990105005400b00b510b400703418900c02e2080c48107050f414014414644080302c2407408034188801c00808040c0018006401130132884041ba1540e0340c28425400d070600305102c28490303542ca03146e615501b9004411040724000c3ca00c0c55040e4281041c1c0201c0c41101c00c1070701c0e07890a2041501c1c040c5c1c0c1562001b03004030214040e144210045985500416010701e00692070200c41e032003846202610401c003c0e11851080e4031100401403a0341d4080c541000a64050b0b0302895180e00a00c0071070094000791300010089814242000b100b0303 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 408261025 1250 408259775 408259781
    0x6180c091c26040e0901111b07050102030f092202030a060914060609060a020f010c120507031e0b0a0b0304031809110306060c0c030f010614030c0a09150315 69
    0x120b01500b1011280a100da00321107040c00d424480c208407400900041081100051215501180700e000208000c0c2d03003050402070580c058400046004100d403881d000f419820062080540001c0c00118034009014229000c036014074001c00d8400d1203680d02104c61080310304504a00300c1c10008082d0340b64200003000d0800b17040039024008156103003144e04052000410101030040c10050805d51030b140301c00c0c05004055000c411030700c09510555094451b007801c01d21900c0d602240c02e6558408d01da04c01d2440000b92540540b80404060624214400d40d07800d03c80481c000e418010300c0000d005507004040303044142590701401d032040001c000c00c0240340d0011001300d02c0f85401d200340d21031207844046280443d41045041214214140b0005e0118100303000200358160120080b40d1a81180c0790000e890000c010304075071800c0c2d440c0c034400c201c904a10050302c0743c031200c00c60260055641d1100810200580d41c41b407000300039105c084c00741c49942014003100266070003004580c0c45240d401030380006 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 408262275 1250 408261025 408261079
    0x3100c020f0c0109030807020f1c03020703120c02090f0901060308040f05031e100f1103070e030715020a0602030c041502010c02070902071e060608010f050f07020606180c09 76
    0xa5008041082e40ca940c420035860054991103440541007410503004c2c060640c030204803094010081c000042c00b8030188400c00132189219a000308600c0b4194603142d520040564074007400e21181005134401a0b64441c0c1c02d40d400501100c04148551750510003d0140c8102c1c0d0001c2d1010900080c046140040101c400041d070f40b050f411074a6000d4a0100849507000300110704a103600401c20f1410000050303001420003a0440e01c6c04174080c0d90b03171034009010394001d03281c1001040c0d62110116040c1814851303040200110400c4400c40d4405070000303515000d00120040036030754004002030b0310065030000e80b4043d09a0201c1108c0c107400c0c62030040e00030006c02c0c8001c07015101e0b810b0001800e074491f0086480d0103611020300380140241c8007407a64841a11039089403003d40700d038808640c011091060300c10318072100c2c20210b20360401d0202c00320100c1010f40b007582107400c00003c2001640b0380300120740c4545102d40004c4016030f21142100104d000e10300c1420340c41100c03040c5012002900d282c1c1010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 408263525 1250 408262275 408262303
    0x70203091914030303090303070f02011b02010c0306140607020d1a010605070c0e060d080922060320030d0f030e06040f0b0f010510030c0309060e07080601061701050f03100c02 77
    0x82c041003101c20595240411248200c003603004100290f105c61203001d41000c40190f034000810106d4002c0741c0d0041c1980000d2401c00140e54546e0710040050745070040200614607144080100025113000c1030031440740c1c2e01d0203400b5015244061040240c0f5050030000c15550081390000f40d40c583c40003e00c3c503840f1090035620f0b030044200219241d1031080c916801140e005003c134421030515905c42c1c640d50000f000c2c180e0311500c404540540020701c40503405001e07003864800107001e4114500010f10a009445180c002c0d180c5111000d0151000500182035001074145460000441c10713044000c3c00c181c0c10004424041d510a00041110f0480032a01c0a4030440c84480d46035100300001e020301e1401d2062940c0000d00d0520181c2e07541c040e6209498980a40c076001c5081d1889494002c02c0d1410349113203500c00d6010701d070108140c12042c800c8501401c40d07032030940088060343c00d40303580101040c0904c5103e0581c603403512440d5502000103061143c50050148051005600c003e512040302e406415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 408264775 1250 408263525 408263549
    0x1b0b130c03051e06070801051e1306090c02100b0a062111030a060e040525081b0f030604080304060209040204262503060b03071a070231050702030919 66
    0x101c071715000d0b0406905a500242203c01c0d00710714100301001700020315000c15003006150a07204205a2240140c4024101d038490103c0c1c0c0e808440c400034076100601890030446803500004054540e1040d2241c0700b00c0e407513440c1c94030b00c0f19580304d01c51392100c1144048840c254030300b451003e942080c40010b1032003242590300400c440c45c0d5038020030110354422a00140303150000588050b43c0300030b20b081a004561314140c040081034075102e00a00c2c000d04260b0719502c12084410320215840e01d4a407201c0210000d030090f0115090031365454006020286c0300510706900452072680649850341a40c00400d48110062200d4041e0200140322042c0070030440a6409119500e082c03c1250304074280224044c0c80d8203100082c03071529060014156041c946506000e000c600040c4151701c041c0601c52245014009650b4410303500c1007001b400208840400c13a40c04060104600e94100d43c0560030307168031210017140c9039883c1c80c8124154440c05415503030081c008000d1102944818030540c0582ea0840400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 408266025 1250 408264775 408264781
    0xb0409050c0913050709090e0d14090312030405010c170406111201060809010b0a05030a1e0803070503090c010f2015011205071403210d020301151b0b130c03051e06 72
    0x31070150340c3c3c03031200301e0031940c80070340c43c522014401c03400702b800000e06010080c00c00c1d850000207400d002c9100035010140c02d01100f84000d018087c4140f5034031080b2410105414101d9105140019400030000b4103626501e03845000184007050489091040c1030400c14010368503234401a00103603003912840e86661030290701300c40904003006104140c0f03c00030f0013007034202c206564000c6014000714058040c8207184400d000001c2142e000b0318000c4480c1d0322039a0300c030300c3c20700d044030300d481c403643c100710304102c59601e01d132000c5a080304255041c104206400740c4401c2943d40c0d201d19012038003942c400b48081080000801041e104150f015191191003540c201c199681c5035000c000080450303150f416005226a5150100059150b2180c00e6811401c0750500280503a5203003281c00903132186102044044401c6040f035031003a004050040c0340108060640159225280950360007030100c0c48458410361510b044c0041841070400450740300080300c80342c0c90790142184d00071080340240e401a00c281004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 408267275 1250 408266025 408266039
    0x51c1d0604020f04091502030403050a0807080f011a16060605151804020702120a0f02010e03060423030d0207051b01080103120c1106070f02010e0a0b0409050c0913050709 75
    0x1040d0003550003d18012401c1d20b0340c41008020545140d04641e000c1c4c8011300500340e0850f80c00614400c502070b488281e200ea5400c0400707040c0c4080242080100400c8800b00314a10700f0314588a030541d0710760403106d0810318000302c00c0001d51040e0803c542030340b2151071820302004251342190b81541d0050704c044071018a80404050075010321141a000d4a220b42020460341c1865405000d626000401000054114045490400d001030101740c2d4400e0196150000307558201d000700080d101c094000386032600d01615041d2401c030f004ca0070791000b4941184540c10403601002a210b0410703c250741103584104d18a0010b2382c4941084080981c00d1401090510941c0180c0405040300e8202403201070720340140300f003110058a682000c850900f0003d00c00041d03500c40401500c2264840e041184449810780005040e291800411502c00e42e24400107102001d658000e0b036046a41c0580302103034039128024100101c0c0104542c0d59003100001058900b00f040301d4100b82d010340d4854541c1d541c41070300c0b640 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 408268525 1250 408267275 408267283
    0x2030c09180702100213050d02010e0d291504050406060f081c05070228030c0b03180c030a0311030c060f1602210703140406210605010c030f051c1d 65
    0x103000c1803581c01c500810003481c1041d604230308000784149044c118060055000880e45c840c0b81d80251621501d902186680700000c62141015555500e10b035011132030b14a0344c4c3e1081480d8802118000e03034030740c000b140800109030005409003820307070b0445802c245c4070004184c0d28900e000d15481e01420180d000242580030740101c4610540203040594400003800103035a0301c03e4801154070342101d80359400004202510951700c050003d100910340c0e07030b080c001484921040c0040c07000549401044501c40c0e41d0f034001031203074244c030340c5410000c0419160381c101e20b05501078410f4024840c002c803401c100301082c0806555114550700700e003009840540d407600701d81e5241940d41040201c413401c03c2c00040380b06500040c207074581c46403404d0780b058240e220070041660880e0b444040442e0300c07801156542e012262440d041a40c0d0800c0812100d4500000244079100c03201019050043d440b000e580c02c2441039045400d408040c100c80d4401d0210380e00940001d00440c05c200b2aa8002d044828030b42007404a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 408269775 1250 408268525 408268537
    0xa02070606240f050d06261f0e07090516021e0a03050306041509021c09050726150103020f03061510050c0a0501060906050a03030203030a02030c091807021002 70
    0x2082c28070304080c0e94076055520300381600500090281c18007107991800458043d000250410050114503201c0003440810b207900c2003244100c2c0c1d45c00c89000c200405000500c80c85900400319808210309442d00036803401c0c8070040d0050182c103800c000030028849681101c11301881a95030848281c0500460202c054058980e1040541d0300a00180c0340031030710540207550040002040022a01d81c0d203181003030401a65400301100c15004188400e42c00c030304c125a114040e10b40301003408041090340d80d06032100018090034a00e1450303640c4a6603000d01042110020350542000c41b00c1c940d059110390b207610b90003480102d02c42c0d20301b16448a40c03410b001c80c07402d0140384074058a105400380e40c0100300b200f400c03500c01181081014440094421800c02218501c54041c100000e0010b00b850f15280c26280540c200900600c400e20f420030000b98008110303030303001001350801070701c80d200c1c3d00140c091031080d40c41e5940c1c4803a51402601021041548550090089130211244020680300000c245e020314 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 408271025 1250 408269775 408269819
    0x911071205030412030504020f0d0605040b06040209060409111b0307110117040b040512120f01120c09050613020a0e0102060709051c080d020f0a14090d0f06090b0a02070606 76
    0x42c113030400140a03800c95504148020002036a00841c08042480c4102c145030940e4400e4441033403106104424211a401007400c0c1c4095142280301c10100340140710754803500b80200d40c0c81e070020031001c42d03203001d6a035510300c4100c403600419104494075641e900825030940710000045040b0110f980290308130050880c0350000c82895558a48458030b038850000d20540c0d0b64021180c0b910440c44c0c21100402c1601c0410318849428100041d1a03c1c0004051b0058445030480c800442c000c01c810169200803148881c00100d00b554130100415480c1c001a00040c411900105483c80380c00e8100588031000d907402e03406c40da8941d0318903800715228542d0f4800d03540c110806a03240340c1203841c001c045804441c080c502c40c905d01003058845000300c0c0d203c602c01402029002c02d5981072143e109039403040341c0c1001d80e0041e0402000d0000107404002030b0f07100070041e0b190703030709504100007060708103000709900002c0d141a9442d19a01c200042e5000c6001100d403946000b80108245605071140742c840080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 408272275 1250 408271025 408271043
    0x30b0c031902030a091202030a1b0302120a090305030a030203222027041202070e01090c020a050d0f2a03030207030207410d0204021309110712050304 66
    0x74240303480003e40c80508895005070300d0b00c00e40004a0b00c500305207490700400782d009544e0340d00c0341e8000400d04820f8000388440d0f130340300441c0c44000c02d0380081d004980310a140b204565881d00480c00f51740342e40d043e600040060101192000f000d54250b0b01440c4100c841c03404402c011401c1980000c914001120014030b90b0b03118041e050100009940c05082229000d8950410f0301e2030310740e00a000e41c91250041030710015050801040040c0c00031030081d06080c1d400180136560a000e040007520505026402407075582e1004003100b0792003008040415034114042da984404030030401440c6000d100340e684041084030900c0200c030450031408a9082000500d8042000100d80d0200c003e540070f0031040d41144213508001c40c0c060071404030a80342c400c1a484096200303a2510150068a180d100c418110a0560301c4030412a1103070207000e50140c0e411580140e441242c81004081c4800c90b0300640710b801c2c9000c0a180700e0340305084c014007116004000c0b0400080d0010011075052204031001400d2041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 408273381 1106 408272275 408272311
    0x20406120b040f030903080a030b04060506040b0d1805060a050105010201050606030702190819020102040812090102030409020f04180b0a0501030b0a030308090c0316030b0c03 77
    0x81a1100030400494039240c1a403a2000100042c20810041100c441050310580b40039010310f03849034099407202e005043c014010401e00702902d014501e85403000c43c680c500b450139a01201c1c03540020710701e4a41d0f80e080702c8000c2c0c46454660003100c0d504400c0c583c005031051100c54403641c114400055198507120009094400182443c0d018240400503c9092a408620360a000480d00e0210762551540d00d045581d910400c40c2107000f1802d500c40324040103506400070422100b1070000c60301e446107800c0c4070300c902c3d01c1440d4950f0f000d031b40700308420441c03490325402811701246490314445c00e183d03650742c0c40300f034110012014101e02036881c907142d074140c0b51805c1c09034050b110a20b0100030041400f804100d100640d401702400b8801d8810001b106a01d0070041c07003414640140c19100c0a04000160750f600c101980002c4901c10030316000152403400e06000e880c401c130310514002c19040 = true := by decide +kernel

theorem cover : BRFrame.Cov 408093525 408273381 := by
  have h0 := BRFrame.cov_init 408093525
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408093525 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 408093525 ≤ n) (h2 : n < 408273381) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
