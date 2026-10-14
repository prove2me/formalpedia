-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2657
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:21:48.185118+00:00
-- url     : https://prove2.me/submissions/d3e27b90-78f6-495f-be3e-29addb8b31e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 477697841 ≤ n < 477877697 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 477699091 1250 477697841 477697877
    0x90506010509090901020408030d0b1206010f05061303120903031103030106170a153803040206031b130303080f0f0711070b0310051807051c0e0a050705040c02010c 72
    0x3000f0301c844059542032100140c9148240014407000e404441cac0014212908410810302d52520001c4080741e03440540107000807000f1854080c00e4600403210262030303043d0442d01e01100d03441c0b40c0004003020007040920719425007000240b4140e0303100e0344842c45034140180109549004c06d200e1500001c821140c03030940d030101c01e6049031b000400c40c6c4020441d8a28000491340d0301403983d00c4000001590043e06035201e2131082c00561112086540ca41c80389510315848029000c0504083d00c2070b00c00002140000000306200e4151580b8405c1031038407400503c0040074a0480d902c819404074210000050743c105010601da4880e0350380c0d41003500f017501e4047c0200c5500292011402e001e00c034034000840e00031107080207548202c0c605540c1c500c2160030034003400401003038096400c40e100442014420034540140c103550041c0d0014804070401002840481c014003c00030701c441240c000d02070307480d060160104614080c0c0b40152130901000080c000e08030b081301d1305004c001c00010540d410703071024610 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 477700341 1250 477699091 477699109
    0xa050901030f0b120f0c011b1707021e010e061603030903020304181a0d0203060703090201050405100c050f1b010c1506080706020c0a380f090a090506010509 69
    0x9802d03040000c040e001c600100761000446400100213070711041020724580403c002d17040b000c140a181c2540c2134007440c2d201d13640c0c24080d01d0004155000042c405600b000498050f2000103030000e0078540d1100e0b8914404100380848010b036400100c4800808409080c240200c2d104600f1010004500d1000c98900310000c2414160844c1140010000015259040c003000f480404406800041c0d82c035a02c060040e1558869413042d020702180d00d880310160742c000c19815409219030801262040070741c0300403210707071040e50403540d0b10401c01d50076a81041d41c8410326029240c400c0b011624040d080d80d450707e94420034491820051600b490b02000382d94803800071103103542c2c40355070b0114a55404003034060594240307403c4840103502507a0200700f0694104104030318900152581e4082c107091000c0c2918903507079210034903c80c8504030912054801c0300a618019540554009611082078107001e03441c684c00000c1041c40741c0b280355000700d01d60703602e031080e0b502038001616105c0c584903201e41402002c2c4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 477701591 1250 477700341 477700361
    0x3010b121305060901020a021606200118060207020310050f0a0c03020702031509070603110405090403260601031508100b0307030b1e071805040e010b040f020c0f030a05090103 77
    0x384000074060001102040603a000b0464140050b0315102011300c020301d070a80716201e07040701402d000020000700740c111008810b0000c3d04a00100c89a254018240c050903d403510f914002005102c480c0501000303038054414a8400c0b0305940214286040381000d4450903a41060650603080c041072910742d246c2d003c2800c2c41d0300c074100035050500703e4000904001c1401c20070210b50044008110440d00180484806050070382010480f0380b2100030000002d009600540e4042c1410f940881d041c1806222481082c0f80d6041403200b00320243c0d008915101c80c1501c20a01203801c040c400c84214911b402c004041d501540e00504031144642035039000f802c245413900350107000b0050040003041d8407500543c0700d0030000c0e5035881c001801204049803070304020484020441d0000b0501040c030011840141118030440c0c01080045404a99900412010910f0f035400392410700c03041622081900500f0800307000d641a224400700103510251039200b41000100003e07000c2010588540c003030341c0110150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 477702841 1250 477701591 477701611
    0xf082a010207150201110c151303080f06010c0501020d061a1c021b06040303020703180303020a030c020a0b0a0c020f0102030408030403080c0a12020606091510110c040903120c030203010b12 83
    0x34a400210400705500c401c0b8425040d2300983d911050100c45c00ba00e054210409000140344003200b40c82c0100901c4018109805912604000c03862a03841010621140e641140c000c650300c0758541030b840020400d40c400d20030321034104440090900d14003400e070f8100c140c481040c02e160300d181d02c583c50001d5005010b519040048040c1d02c04103030808101c4140f280b0b1007030f14016512a200c3c2009070034816480d80710b905d07100406806000103030340807503c030460543c1410b02e001e00ea00a44001a142000d540160501c0070001c6080c00c1d00a900c02140b44940307009840c0034110a80081c012a124171032070140c0889030740104010800100308400a1641881040640e5600e418503550002040501110040168854130504c203880c1790619009400903510590400b80c440002c01082040c0301a51291040c4110b00913580d0703005400f840000d1032003100400802c09012140b0b00600b080004656403101c080c03a10841040103400b920889040c1d40500410b5420100c0000085800b07120080004501c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 477704091 1250 477702841 477702851
    0xb0f060f1c0e1203040b0f060a1203030e0303090c09010803070b06270106120f05070807030c020115030c030507091a0f0609090708011d060d0b060102070f082a010207150201 76
    0xc400c3c00520142c9110915082d80c0c1e05090030002c40e02480501490000aa02c5080c0005551400b030204200c50b03100042c03070080203c1d8141a0020540b400c2611414000001040181032002c80c02030743c1c904003107801c030784181d0b01d4030249130f6603005a400041c05102c281010405a1403e001d03101d070441c00c80001483d821380080841c4101c903030203a1201010510356280f080c10302c0d009000e030f00500d05400b4001c00c420700d041d890061403100050540340c1459901d800d16900c56200303403c0000e014041c00134a8408642d02d1500072001d8110744000d80d0f1a0050060205114825018180311400c2d4400f1070701c213010b00f010420100a0071813400c15071100040000b61055120f4040b040d00c00c44a0f44c80b410348641c03501d03d10040203090f111140300045046d0302003214540c4e440060410407904219030710560741d600d0005170704c0c0c112940c1258a0310540c4100018414900180102007103070024968401240c0081205003d40c80c0200203c0c0941c011001c14041c01e00104640c2c0040e904520000c80c0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 477705341 1250 477704091 477704111
    0xa060b06190302090a0506090307050906010c061a09090f0606011b21030b040e030f090d02090405010209180f0f07050910021b030a030c0807050703060f0b0f060f1c 72
    0x10010390044541c0401d03008284150a403808696880c01010b090350187d1500307a5080c006920b45a0500605200d0049800401c0f2683d10612440f05030030381c840d40070026280c10200000d08003000400b20f621500091000600ac0c6c0000b140405981ca00c40b00148002e4032104015a41802d452750f140c2c080a06088401c8041303250300800e1400c00c2e82183d00c410035219150002400d468502031401d0042e4101400720304040d0703002040740d69251550440c00e4588d0345410000300b481c2c3d0300b487c0203540248000c092009000066006241c4084110f4024101050300b5800c203075034501c11900616500c43d028001179000000c60580c940c000550f160480c907228085000510410400b0700c108c006078822100410510b220b82c14182e80760404400034801a103155030020400c6010741e000800d0910f001c5040410004104501c001450740480144441d842040100c0010401c4d1411580319258014a0048605000e411a500302e031a0165040c035011603c8400c0a40032603420b001d401041d80d07084141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 477706591 1250 477705341 477705367
    0x605014e0914030a121802040222090903050f03100f0f031401060e0402060a05040305010606120b0406050906010c050a02090403050316050c0d032c0c0a090b030a060b06 74
    0x14040240a040c00074985095050121102285015528950340208024600b00d0380000c031040c00c03080b10b5080896451401003403650b20601d01e86000f9000ba001140030703401030f8201798145600a4400c0d0240c50115600c510300d1043d00d905500150209000300026501102d0305070045904c0154407806c0c01c9a0b035550000c81da00f9012540c401092042042003e0003080701d4040d180d60010f032441c0090203441c0c14554403841250000d00001d05c07480c000a0840d01d4a400748007038800660300310000f00426540d07500080c060703100e03400c5d502c1032280c5440d510100521b000d100e0003081d914094400c440d00c0d0341c0c402c0195030702d04d1103000030340b004c3c410019000c1c016680d021826105c0e51086c0d68a44d100e0416003c86200c0801a02c5410144081400000090200041e05451030391300c0c3d2501081c0070400c0c03410b081091440b00500c8200c3c0300c0d42051780d40d4940f00018407070100d0400f038070100c0313441d65100c00e000d0445170800700059050b0400302e0b180d004101c86820010364140024066032030904145040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 477707841 1250 477706591 477706727
    0xf0705120301090e06010806011e030803070201051602010903020c09151c06060812391f180809040b030a0606030204051b0316020c0d0c09060501 64
    0xc0d69148000001400340c501d86000b103400f001c0d00c1c513001302010750503d002c240d10b400c0c0500034078608400304140c00d07110455a801d84070045810040a139581d0401d500001e02070642200c82c42400a104078140400501c144600300300d4a03055030141090000c08d00801200030009014154141c030890040001551241c1442500c0801d200c1540400d00580c640038041daa0154419040c58102a6540c03d02c40b0803101120300f4064410610302a02904650018221148141c2c4608030550200ba4490300140060350107005007545648805541c50f040284040c0c4140506030103801c04942c0b001800202d010001d0300402500820101d1130f02c000101007403602c10042c8088d11810f88484081081d8100791083c2c64222000c0110404c4184803070210340030038072001e00038030014009142221039481c0b082c0300c03011508400070100b170008081410410f2035800c103405207180d4241351a50000b12580140c0c0ca03040518455100c00c51398803250300800a00c0da0310104144011a1460194099110b4030060 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 477709091 1250 477707841 477707863
    0x31906081b130501050a031203140c0304020a0902040b0417070905041a07080708041104061502010c0206090c030a02060304060b3d050318100504050319020c0f01050f0705 75
    0x8444081500310401800200102c0e00c8400c49203480300505c0b282d11000110780c01d881c1c10010755840b0007412300044008001e46451480d1b9119140c0502941b1042a07000f10b01540c02201c55042503512518040101d228520601c0c9045104020400c242407000b12954505001c0c401900d0f00740d50f81d06c811005031101110200c2e584140c6403503500e01020760142c3c1c1504528903207420291071400301070144c122140548007812001c20032110a605a0b11900000060400c0c1a40444480c4007400f01902a040100068007d80644800078100d41c60010700046617810040061941b04800d0b000c1c07015a52019200b5110300d500c44403c042540c43e09043d08030b000170300600c0755118a08035950394003c0d500300c0b0324180502c440a002c10f03d240b54071409494101d85458500508040455071440c07928280c2c3d02d0040d02e0600b84020407007403043c0800a4800d115811105c5c825013581e0312402c90b100c4d01d00340b40866002e2020840d040352035200d01d01420203003c0346c031421450541c47c0c3d21454a030000d1800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 477710341 1250 477709091 477709123
    0x11214070c020102071e090504050f120a030c021612080f0a17130f061e09150b10020714060903011b030b0d02030c041a0901030302010501030209010501050a020303190608 75
    0x741c0d14219641003140790002c01d030704800f001e0408441d1080085480e01c500c1200940c43e11800844e00307120041c0812401b0840220031540707400500700c44501e10360840d5030342d41c2c0464a020746d00301c1040c3c00452984c050406103554092402e051074180074140309a0303582039946183c107004a224412440c402003443c80c60341c0c3c807084900c002d8940c80500c4064004c0c841c206031b8042d200d118000469074403511071b1140c0d01a01c00f1540c14811031404006c61104240d030f444031814100030106203c005031266000d105000c83c14003024440c40103201130040907584010041c2d011900403c500c2c84000c4412140d1480101281e141403038880009003036a1700e41c104501103100d080104080c2581500c104141c118054540025540c42074000940f10b070710801d450384c0543c0d220404040501910320f0f0201506500601c05800c80d61207041c000d009080c00d000807801080030340004a03a81d0700070025110343c10300c541c1c02145196101c2200784424920444110359072911540c01003030441007444100068441d0030307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 477711591 1250 477710341 477710357
    0x5040f06080603070f05030a030309022209061413080c0a170d050f010b04051201060b070c080d0c080702040b0a1a0a021b010206070c1707060903031d0c01121407 71
    0x410941130004507888072800258060f01004643c0b804520320003070b15010b0500103000c41d1a40041011180c1c171781d40c10110600295403005031201a0b074040a0824000c000c05c0108504003070910824000649940b0702400640c840640007404240088c12884000015a0680303a00c0380c1d2141088060400444031146021444140c242c03681d00c20310385d00052145043c181c0703525010714403c4a100d03d0080500076418450074400c0c058094010b00010620702090b1541d910003400c0008107e4010b004400175402135062500c3c0051151002100c641d410500281c84c051655080100400524032550340204041d4000241e0816403018500d50b540034502c06039941ca0080002820b002c10600e18811100b40380b8107410f09a68001611540082c2908042d040030209042030401000ea07000f030100200c100052038420846541c1101144a200c1e8506101c1c9401910008081c411214444910b0754400d040410b0f166204201b40071030310504417000030b070345c140444102d01101c200b2112000803030840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 477712841 1250 477711591 477711601
    0x705040f0c0807022d07080a030c02130b011409011e0305160809031b030706060305160b0315010f110601230a0605040909060209090403030f06050a0b031605040f0608 73
    0x210b5a00c01010b20242121030340c00c001007200c8101d20a040e00343d25041140d41d201c0050200a00406840305504880e002c040604d07004050980ea5241280282400405441c550310580a10344075120140c545000742100600b4141440d0002c184460401a51803010700911110031009250184036070350114903032411000e810f2884c0142003038801004032240802440340703004400c0d901c200f04d840c440e903606807200c000707071a02e50302800f2310142000b840d04000004010340068240321613000d441e940300640c2d07582c642d03a040e94001200c5142950342d0f401d0100c0155032140822a80704007039410034400c405d070505c0f90305142c07030b809030460910302c05110f008e12540d8200d4100c80810038001c585d090856403c25400801c14002d41c451070000c280c030344181071704001c0c03280c059600004001e052a8040d00e07003400c00070003900c2d085080d222107030b02e400c401042c1410b0002c4403800b581c510343e0700a0f00e15219130300c1c2c03106a2610aa81d80341000810f010104115040c180c8150040c405592080714600f08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 477714091 1250 477712841 477712847
    0x92c0f0402121207140c100305011806080c04090201050409150305010b0303190c02060f1c15052d0301110d0b0315010e0424021b06060303040e090705040f0c 69
    0x11040740d01500e5101200320780c090340b0f85400329800740d60b000584600d40100f102d509850710490448080d8080300d516416081c0c16850b6000c1c034100e43d610101d90444450402000b0202d404a02030245980c019242c03c0c20141042d03045074001c144185003d1745025900c40c810000c0b522044078443e0314680e000e03810410b0000c00d018a681003a4114050340c0b9040a0580340c0c071110204244580501a01e4800b1005659525083e00c440614500d0859079030640845240800320000c0040b06506103400f683d4400540000f0b101c070309a401c0a010710f4128100d0030300740601c20013000340701e0b50a2241085400751b55207003809911501d988a950003a04ca0480960040580f00c00c0314041e4007a03803040c840d00841d5049000c0e000e0450310040c0a041550303e83d420072502c141c80c4606044516103440000e01b002480d55402080300d8400000d4090040303041d1030146440f41015182168107620601c8140042e1110b9100250001c40785d504030761880390340d60003181c1030340c40f51004400859624034451280c038ad0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 477715341 1250 477714091 477714109
    0x80307031701270204030203060708010306050907050303310f062601060c031106091e030705030d0e10150501030b18040605070c020319020a15092c0f0402 68
    0x2210301c1d000201e40c14210220041540140302c00d1104400e141405101c10f2154101da001c2d5030094250f507030f20302d00100c0141c0a45020300c81113031340030b01e440c0c000b41c986140030032000141d5800030b001d14540f8001e80da00c91400303074007007200b615034205a48600311116001d00c000340090058000c01c0c01c01d14a441340c0540005040300039035080e018080031825061080901050540e01c40741002c020504682c20112513980041ea00782c10140301e00c405018210034000f45045880300901080e00c01c00c11074040d0b136500c90041e400c00038504d9000340220058001c0d260030011701c0709000c50840c0c43e40062914204150790400c0380d81912440d50203800d203d0b0b541e040c0151240e14070103a4250300300e000e00d000281406900284041e0207a50740c1c2011504540c428002000341c5900103046940c1105850b041c88541e03600350900300d104180c070042c0010b8040c000344184942059030b8541785a102d10308220860170404980002c0100502082d070b58240c03015561066001d160103440640181c5414410320808407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 477716591 1250 477715341 477715367
    0xe0307030b0f090a0c05150f0c0601180e031818070e030c010e1e06090303070506010e071803080a050f0a0f020d05040f03080c0f01021b011a090a0c0905090108030703 73
    0x3e0030001c88200804c058010745021586c05039018091003022002004650150703440310900380c0350004680c82c01110029a06068580c0c00c0c500082c940e0138011414216a44220707109503d8205001c8481c0b4a040c005407080142409400c41521000f40401004504400c880e40f8011910000c010220b50070200041982d40d102030804d0024034880e400051510100c0c00d0280040301c0002803550140c1d101c01041d529510702c00380880e52a120b00e4500030b5161042400703101d201002c04400212050300c90480c1401c0d0642c8000f9402146086031201c030000d500100e00441030120400034480007078209402056034840b46d5903102e42c0d00c0b0110300001d0419201c2100c4400f000b034184010310003084485440c0080f682d000c000c2e181e1344c405400c1600e04000c602002020726510104108100d0f10b0500020b10780c84640c1402080f1107600c010300014002801144030344c00099680000c6c1140c81c4540c03100760000540d041c5483c04660b68030001d14504400d030855102d039000460520100364101001c88078903 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 477717841 1250 477716591 477716593
    0x140f030901140d09080d0606141201032a060306030209060301051014030f01060602150115091503090203070807080f0105011406090a0b0706090b180c100e0307030b0f09 74
    0x800d0808000914004074445604090100051461101c4885a114110081c3d2100040d03403100c90420580004140c03c0c49084081142c3e900a100d9600088007140c4600d40050b210f5612130f409c6840703032a03540d800c0c0d205a41c0602240e0340e1032011076451240030780041c04156000303d00755041d40f040c8454004003070300b928040da044c00d040c441400e0300403104c582a541c1e920340c6c05a0701c48009000a28203107030516190984e51802c1d00215007940d000c24603030019030842081603510b0b40d8030080c2d4440b0b00301001620001514541c401e0041c0da40c007030700b54200c000d028940460000c50680010703003400241e5110706195408040200440c0c07809100d03c0e4107001b20072008108641c50583c0c40100075481160840c031490b00080c40000c695100000b01020b410100e0ba0151103104500d0844d00824a680f8141ca907168242c0019010001a440c806211300c9880042d25001c0030001c00e001c0314511000101050001c15401c40c802c5490400107400114054010070945042109020080d01c8010f450003040b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 477719091 1250 477717841 477717847
    0x10504020a030b06062710020f07050105030709090519290d0f0b090105071404080d0c05010f020a0302030a0b0a030209010e04080f0304050c0a0e1b0d0902030a140f03 73
    0x5a40e0340070842080340e401c0502c10f00c00d951503000003070a600c500c502d005c400c2c1d060040080c3c01041d0300d403039144c0d03906416201543c2c4145c5a02081c2c0e51040b000450f01d40550121009000039403242001d0340d0800c590341020540c1c65100c204150a450301219121000707110803102e0060030a06004100d50312410914180e91a9591a01d16034080c3d00c00400c24050548003c0707040400018400500480d034003d90f4412540c10b003549031364041d080a548000c00501d1031ba158150006200c1c0031601260010b500070566028803020030303600c00f13001580649855589410740f20703010820303000030607111115030307801652807820980d103000310380340032400134060035000e1414001601c4280f00785046d55200c0c02019030640e15417903c0900c0e44070382003844030481c0000c801d000411000044001000c58125840c560382902d40311070343c4220404507092490000203010156403940104d00908042d540400c0110b034070b034800c1d00400e18200360a04115020480309421900a4005200c922210701640020310700e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 477720341 1250 477719091 477719093
    0x2070501180b37080601090b030a0e12131721030a020c070e01050306150306190b03061807060c03020303040809041e050901060f0317031e0f060f03010504 68
    0xe214180960303a00007100040640d81c910440c0c210181c1c46040914110103480c041c07202d03000d20401c400c10f4401050310391020070519030240d05403100707507030480b9142402c65032210101e02c0908841070241429000c0c40307580e450380c0105100103000354408280d07080c0000b807408588140e03002c4c0100625260f40c001c0911003914841380c0c2c280500344809003c0340d98880d01c036a44101c000781703c3c5014002484c07052440c0020078000c01040603040b00c01c210241d400c580d56001d11301604c1c1c9401c0d0101039158000e08000313480340304600525150043c10075000620242804040b034500072059811864514100c0e40e03036282442e0400c1000c1c041c05486c1307070140c40e0172002d95002c1d40d20b010141c8014080b0174080b40c1d00740c40351501c2e80604071813611540c3d41641c55010407102001080d00782c0f2600e80a5080410100f8208008400d0804580d44a03e4811903c4003400b040c1034290005131104a80d0080c08504180c1340b1902e520703030307400b900d000309a8140c075041480810801041c0224000e00a074101403c000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 477721591 1250 477720341 477720377
    0x180705040b060f0a12020c011a03011823060f010807120c05090a1e09020102100c050708070303020c03130e070e0108060f0f1005030603120f0d0b03010906090503030702070501 77
    0x940c00d14105a0031988031034400d1400c5d11055004030a03001424130100d95400c44030302c1504030343d020b50703aa074a04210040020303082c54280c0d5021090300e1040c042648880000504440c1c4000204882c1c40c98443c024007403c0b134a50504500351800e8206d00e00f1240103000c070306800d02141006120b40c8080d000107607015503806860708054824a8841d0350404c00040c4043c10030780041035015210926150780c183c0b1301e4204002000000c2c42680144180764418038054024482d1002d0684661200e07420710350320ba641d4076000d80c0510000c4040507000d02903200314200401c0600707140c43c008007640c0b010b00e04040401454840c014034141c104100384a8505840e40c01c814007030313040303601944c6006440000d540404e40000c0d40c84503107504403990b8144504040c0d800005103010750411001d0390f40f02c0301448800c0040d80a018034440d810360741001000c0c501d003000e9210750038544000e0000b040e0301145403240000c0768006402615107400000c20016269414016800548000d0804182102e4035803942 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 477722841 1250 477721591 477721597
    0x4051501121b111608120703090f080a11030708070302041a030604050a060e010b101112030c04091406010509100c0c030c061715040c03060f0f0e07030c080411010e09180705040b06 79
    0x90018007400080b10802d26100320002006003044251440754035544520052340c81c2c0cc2c1c510292607004110b18014030501e0040741032002c9407884001880240e044d0703000c0200410320002a075039a1070081c1446007854409000f001d10036400303100641010101403c2c103009071007030717005444a2640341905600c00c95075080c0d50311039520b507145454909030040c000b159142103842c4601c0070360f118000c000c00812100c070724014030036600101e13010f22101c0035400001804c03200c151103c80c0420818400f8450905018842c10340304103182c1b0342648859111348464144c684035030030650300016400b00601c00640c210746aa1101e480b020200300349450048c0e00700c25110f0001c00c85034840e82d00c8030f501c1034169100c0d4000c3c102604d4200d0240c01016a82d045040701c41c19103108040015100f46c000030342840c028411500d2f130755400e4031075560350f9680fa42e501e900c07464440c0485042c003550b25044a0691158407199102e0142c00c0c0b045803102d140c100c608d80c500304150703201074400c0c0e0410140b103c240c0c0710036081e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 477724091 1250 477722841 477722863
    0x30402100f0201151e060908030909130c030302010506101106011e09060f14031207021009120303060e01080f0a0b0903070f0605011404051501121b111608 68
    0x1001c00110300e1160101d024080e04d083c14240c1105809000caa642590440d41008182840344031344821350321001501c1c1d010140c0b050700c1070340c0c0017848a40c119003000c6080369884180b00c0160104e1754070507a030f80d4100916a07001a00140c1d5100c08211660a040407100003120203803c080441c0208600040d80e1071605018000d001d0004031075680140c06c2c4501c2c0034010300b8130b8100500c00180c880c0001d020240540c8215040c140c9407103900c80142c00c0109240302030080c030341c481c20705d0040507400b40200001c0c4040300350204090034400040021030b02d8503401d0801c0c07203941c01184091501100241985068008072040d8000035001907100900160000d05907900c00045d4026a0710548154194060b03200060101c3e61140c0c00441002040c0e44401c0c1070312950001c0c0d0360051180800c1c801211701c00c807a50040326148601440c81c5600480304040c1c000c0c0c610380d0100d107400c4604d5200c10003e0302d04070014086100508601200d1106002038224801824480c0c0603252801200c4c60781ca00c14201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 477725341 1250 477724091 477724097
    0xb07030902040b0d050a05010f0b240d0c0509100206010b07060917030412020f0307030f050d1e1e050402060406260f0601020c3a060504030302040503060a0203040210 73
    0x38020045440310b42010b580f8031801803404550300d105041290300d030b0039030580444440d441c002c064502c0c3d040d036202e00080310a014009200d2250740450038003c00b00b00f14100d03c5414018020760407954414041c1e40103040141e96644e480e08041301c01e2101c80d03085050080c095400c100014894101d280040d1919260044408140144541401c11001c0b02d490741143c000c5a00104000600c80045280400d000aa500700c42c00c130b1410500381600c5c0c2c0150303900117002404403071314090194800c070301034980708208010005843d0792207221040c0303c0000301000d011141e1115018191180e403030204801e0659108024001c0346002e80c000341c160b202d64082d000c04c1c45100305202c2c2901503c1040000840020002d0727104a00b01100d404884240c2260900d00611458a480300a0300345440003e5441c40c030403003080c101c1c2075401c1044072604141c2075000038050700e2000110204040340103090049029450041e82c0320f00780018903052400040c500125030340108140001602d40760b80d10507120361189 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 477726591 1250 477725341 477725351
    0x90408090613050d062405010503010302010815042f07020a05060f190507020f0d0321020f040b0c0601060519030b150d14060109061b0c080708060f130b0703 69
    0x6818245041810f0b0080d44d003041040b54000b0070802243e0000110140c40791504584030500c110000d501043d42c0555030001b0300c14001040194003400740641c00c05a4480440e40c40900380010400f1030b0600428240095185500740010041c0050009410030300240811307e011010b8000c1580354480d0700c0358900510f4005000c2c044080040182d80b0100c0d104100900350440d00d040003040d50300014426449200343d900c1040252606865001d410343d41600c5003180401d038840d00041005c1c118010801c5c40782c0801c003003410b0011240040016140c090390060b201c040055400c3d01d000c00c160089414030004011544241c50002c2006d480000c45103404550045410b020500c80c003440c110b0250903120204090f4002001c0790003209507200883c0340e06059503240d400450340c510280c8102408218080701010100c0000e404038600507000d01409011165582811032901d0001c2c0c1c0070030045d800c00010300131840b04040074160004c0580e00803110480164075040c0844d44054880000d040c0c2c0c40d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 477727841 1250 477726591 477726607
    0x601140c0a080708130f140a0e0402240c1606020f030f03040201021e0109020f1906181203051308071a2217060a09050d08190510090b0904080906 64
    0x1503086400340841080c0c2694181d58a000c110035051181c015005051f9540c030b002c4045e8206070144508a41c0c0c90b445490945c0c5864090044042500701d80000138290170942a400924480040001c40030810040c200800300050101548089401090443d00880d5811052440010a441c81e19400c20445030313036900c5500c0140c3c503164155001d10060041e80d00309618804041d0b015040b01c074001d8600707404480c0108100040c0540ca810f5500410044980034000a0304c200c4940e0304d14500c0d03d1403000b1680c4c54200524600c00c030b000c0c08600040d4002401ca00034016400d4460003406a00c00610440b07051410f4005070340740c882800000003901082c03140c070340d100d42e0300d8034080350507d01d07c03480a0703507101c0aa14504031405c11105820b842580d000c40c64080c094440c02d28910f8000c0050403910b111210100c070b8458000e002200120300700205640018002e03c01c640c00345a00301101c510441ca0103003e2800e0361141d28041d845200101c0400020400304030403103201c40d0045800584c1c403e24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 477729091 1250 477727841 477727853
    0xb0d030915030b03061303171909050c090a09030914090c030a3e2107021501140f03060423010608030301120c0e04030c03080403050d140601140c0a0807 67
    0xf5244440da25118240c14490043d1007424480d050600070784e252009240c0b05d104802070408251188002c05000030700f00c91358010a580f20074041407044081c2c90803000344070000707030800005075684004556a0010801019041000c010082c40c3d401d405c80300b0001101700041000742d000b0401c1e440001c000000400307000040c1d0009100c948407000d0110041101042e03806800b10050048a03146100d160b044407051902c015500c0b440c90b444052850b03020540075811500b00080c0c6110700358818441d88400d90080c0300c4415001e02882e28685007070740090410421010884581540a030308110281f0004c945210f141c01c0700303040603492200a15000a40e15401094070780d101740c005000110001c50a00c001030003508a1501410014580648800390048208400d44e0700801207001c65405000190007610065802802401c2c0303203041c0101e10310010262140c120084003d16109020000290b8201105111941c400c9a2150a103440c51140940d66202e290018003045000303d800010050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 477730341 1250 477729091 477729101
    0x36091005030d08010e150d14150f0901061403031b120706020904110c060f070507061a0120070b03181603050f011103060d020a08011e0b0d03091503 65
    0x40250445001c01c40c040c40040c18002c3c28000d00c00c001c00d0307590100d2005540001c201c004031100410130105001c5035030f07601c0300215510b08503403200d02070110ba0320f0074100304088043c411307884c040c0001c0705840c0a510150031950340f138110011410303100c0065a05605e00009a0f0b0303030021480c11072a04405c1407541c280c6040b00344494002c01d0303100000e402d0f0401c9041d030050300307500c01c080d1024080090300d44001203860041c0c01c52070110364051800181406141400349d82c2001d6a820018030307004494035030409a50340112180403401030304c40100c1c403130b50344410b54108090f18070303401999040981800c41d448080c42d2081981204012000c1460403200d42c042c1d68841992004480c0500508003103e50074160f0740c401641e850090700035580030b401060052501e0600140045441c41e580d4070200855660b80b61070aa800103240c00340491119030902c20036400011a0000c0034031640d80c500c0d810241c50f05c04a0a030300560b9401107190020b9000300e0340e2800c0d51138200b0125010324402200310000c1c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 477731591 1250 477730341 477730349
    0x21110109051c050606030c010206071b151a04050f0c0a020c0a031410051902031509040b0a0b0406050913050a060507120606050903070b0a020120360910 67
    0x856080c1501c0000010354040d0215502c283c3c00ea03803055441204164544202441007030250704108002082c89124075445804203500340c294000200290700d620031424000e01038901c3d50355030f42081d060b680d070b002d40035042318020480301482140303025110134075038420207480702404860102c1c803581d190f8024455200c0c6c0314805003c0290a035940d0030700b42505c510101240b4010700400140c2c1840c0742c142e008007481410600018820f00c00790750048802588010b200201315400b0340040d00090342c40441060040c1e01440104c0030a08000c00710000704c446800110b84100e14001d800c1006854030400c440c0c0c0701240c45116a0307900c51a0804a051086c0403400910061400040001260700128071407140309088004000407030b181e80080d84c9910803080d0856159105e013404001d64005140146003031034a40c800407840034010700cac080103080c1101c60014480c88d030100b04590860b02000c2c1d1029541941c032812060083c82c4081c501d0351040b41d0400d40c1c012280384000030b039019102c01000d0010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 477732841 1250 477731591 477731599
    0x2100912080403120203361f0906030204180f09080d09030f05042303010e1204290a031808190f030b01090501030207140706050c072111010905 63
    0x984050318004070036500500040340c0104010061a146900c0041078420000304485160203070000101e922000700240c0b600c610400c00c0c0c01d03a03e00c9240d1640d000c080c2e8168061666007102403800080540015002d8211004140c4184030800c9008408503042c049003c034088000741000d6000c903c0350203040d0251002d03000c0040000d12640b1480c941d80400c000a009996a550703501d407015007102e080c42140f056440000342c49650581c1d07401a180d1240094400400000710b5102d651201820040100005015800045802c108041d00c0d410b1058000110310340240c1c030103a585103100d015002d10507501e130416681d41101c10110780606000c3d20240d8110118a46410200032180ca480103011021400079164198901daa50700a02802116005c161280075030907003402d0045000b50040c00f001d450181c1c00e100c042d0113500082c810b020107818980d80c0c6d0f5903903030300c0f04145905d0040a5400074050565141c41c0703c0310901080401c600c003960000d000c19210300c08a0040300c4504080c0c01580d44 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 477734091 1250 477732841 477732869
    0x11130b03090a0c0f06090614040504020d15230a0608010b0c010b03012d090210050c0c040608030304020916020304051519030203090708060f0a1d03120403030501080604020d021009 79
    0x11390b10120201c008460650307441d050f02d0794403072104842d0280000b003000050f010070312050100c0c0c0b400e9000342c80401828603002660910546482040a00310380c070080744030100c88070038029881e0400043c101450291030040d200d03490a9001454400c0500c11014211000310b00d41e00460000c0d0402c10b0781d540020001c0c0f0946000c19031423650b07038421000e41004a01c140e43c00e4078100ca00750280100703d41c1c004100c20701c4c5010f802030a0ba0b1661005c12000024024500005240da490b0b00c140710107410704000842c1c40b46840d02c1403108496024009603100d4035580e110101c1c29a0000459003580c5c0140c41540300b02860152040c00b034052880c02044142503030000421417945540954461904407045a60203962111540c2c5c50b810f055400388400f85001001030407001a0341c11285071f446500145000c045a0f42c48898116000842e40d01907201c5140240014154140289405001180301030a42410a640010141044240001d0140c4130a121405d100b41c007c0078854000c0a4500c5c49243d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 477735341 1250 477734091 477734099
    0x120203010f050418030e10030b0a080a022d06090d050303090d031808040e04020a031a04060516081f050a030c051002011104140a030f140111130b03090a0c 68
    0xa81c0c0050350150b20b005070b00c1c0904021005181841900038642c1584448001d40c44c00c4060001c5a11088551001c2c0340d1686413444054030b41920910080041401a000058080c4104405001c5d00e412042c01c0c88019407501e02d10301d280408560300c03000d01f1136140e0365075100350380803400f070010100c405083c0340404010040c5941000c0f038461824a0741e9a41000359880d584044400c08090b0300000d449502c0074402070212003403408085400900062014848030380d20b41c8c59089001142c907031012086c424005001c20820a402403641042c50300405101e02d041c0302000402181e002071450f840104060600380c2103078602c204140c090f040c0548250b121944900340b0448055180c81014022080104031032846031061264011040b4142640e9103403d02c5d002c0c94007000e1191000140c0c0c040350601c0d000000900318085452b070244114102c03100301e44a081c49500f100c103200411403142c0d604000000c160650359882200350340c0505429038807621f86059252400a404400600f1b400090300089 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 477736591 1250 477735341 477735359
    0xf05150a030b041b020c090c0a0302030c09030a0c0314031801030f0b370501020319030e0a0f02120a11010c03171e070504050a0e0903071a1008011b0f12020301 70
    0x11121a5070b917000c0705c1d005400350040c04650402100c1c81640c201081c003103003021910a400868201542001c5642000e8036400003e042c04641d240459800345034600420070004148071400f0450035010285041c0080f0761001c2460700042c0b24454100755559a00d421500e45550018610303070740c058490968840800c210175104210f032100d0700c1400c07a40400402903481c1d441c0d007005c19101c040e4041d504148800744140340c81c40140076000149920340183c042082407c2003603182e00c6014248810743d401070b90040c000b00300d0800c100301c141c6400c60010800840c58891501030495421b203800400d41d44103050444403000150212800b40501005000000e50f0b1414042440702210f5810100c3da2240385094915104512450350004142c03107003003011288000599a1080011341500d00d00b111036a03841c40c0d01c1003520359000302210200180f00444400c500e0740400b9106200081001c0c0049850b812154039040c4215002c101d260b20310281e205109500780720b140d103d451015512541c581080d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 477737841 1250 477736591 477736631
    0x90c06031d0102041a09030a1a0103140d270305030d09020a0f060c080d02041203021e030702010c02060a11030706090303200d050a1508160f05150a030b04 68
    0x60342150392101500d5001c05018401c0b44c3c01c4540704c5440f00c0c109410001094030a400c051440f0340d06000391480b0350081100448015640711128581070038940c107614154140d0034103d4041c0380c0759070040c03d0f880340450b04041209400840002d00700c1e2410f403c0d40d2091401041d94100034401d00000c40d09042c2040b56400c8041c080344212240c1c1401c42c0c4899000008800310720410001402d80b02020001c030b0320050040200014109002d40f41c680c840b090f21080920550040f0010f038864141c43c0c0c0c01041c004202c00103c28040c024514080b0300742c00091018000003030103480b500001410744c807414080d1490414100b08031007501e440d03001d6824035400800400030b064000c00c2c1000001ca801c500c442c1c424100700c0d0501c4142c9424121000ea0003001400d004264104055681c0e0004c103079081c0c1408640000d01d220f1000b86005002c00d44600311761442a4001104005c07401030070301a44ea1501105200c0345202007080d519003c606070200c0140005000280d00701d850010a4034111080c4010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 477739091 1250 477737841 477737861
    0x4120609060e0607020709152115050105010518061303030908010c050306100503090a05070906080f0714011b06150312080c0904090218070509010f020318040f090c0603 74
    0x8000d0880942002525544103c1d90800142c02c082c0003445030108a80c02001100c072110100351003107844402070056800140c40d0050f10271703440900d4200f00103240d0400c01c54840070401c180074039403410001800e103000e1968243c101c0c01c820b030a150020348910003a85c2e20f080060000c184126581d0034041c1194802d40078000b015424060140b008502a1040300d0240d0005040001c5500c00614111503030b40001d4070384e80c0709008510490313000c66810802c040c0589251a0f00041081c500441c5c44e00e4aa00b09480e51040c1c0c0001c0700402c020f48014005840c541030a0074007140b149a0028041c9107180c41180c0181800c1c0f51205250406150941074020f892160180100e001c840301402d0715a070780103c1d04068501420814204107081076040004440e1000e0896140c018010307200740702d0180300b00d401070006580810000340070340e40a050015503500c1400514900f40d040d80591a80030300182d0554000c40c0c031822003a03ca0f54840d40001001d5070001c204460294031124000c01038540011 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 477740341 1250 477739091 477739103
    0x12010611100207030906050c0a050d020d030b01090e040f03020f030301030f0c0509060f10030902060c0607090f080a1211150702010b010e0609090601030b09100305071d0708060604120609 82
    0x1800340c4250614403c03200555015110110700d40e242035000c8419030b20000101074680948990742d80003620411002c0c01c81c1d505600035052544a911004048680382038000b070402014100400118110f1440e40f500035070082c282d0704044045081c140d03d44111352000704100d100010002052158844409441c54802c00000002a80d64400c000410300195a035640c0300c900303032104200c1d0340b03012420f50b844900682030208a40e011a0001039068010380c80d4054513800084c1040103669110709014041c2004100164005d402d20b4105550350004940052a8030011506201118002d001c080e01c414510340450741c40c01d500d4051410b030384100742c402401542c203081081d10a9801944007040141c0003904140c101600f0000300003000b130000d00f5040c10706580f02e48a501c06d40b1561000d500c24104404085103031841c51410a1500c0140e6005081c1140491910044c01c4040d001d0039800024a1074003600545442000800a201d50b034422400c03000914106001c010840d0445600319004039 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 477741591 1250 477740341 477740353
    0xa1a0a1202030f1305070f06080a0f020705030a12140a1e0b1e04061205031c050705030103020f0f040501080d020609030a0206010608041e08190c0c050d060212010611 73
    0x100c42401a40800d459240b07880781d10070001450b0240c120050280c042c0a1030031904401e50b2900306000c280000d82100c0e00141e070313520402c008001e407805030040002d0700e800110300d0b1030020b442d041d03101d0150510860030403441d540401c060600a410810750711500c5040f5640506000c5080401003c9102d0080e15000b2000d210030380d0460148124550080301030900b030400c0e060255201440700501c0440c6034002c0c1e80781404900740d8850042e03080f40718031920003140e4403602405403036078542c800419035a03898244010484115401010340341180c0d410b451841446038854005041c035500c0449450f04685040300010b40310000080c1000e003c01540c0035202581c0311490340130b4480c4103c000c11000b50f4004001040301d188956201c60340f2070b0050641040c0407904182d000fa544400391011769034260003040c8500c640c0c00f50301201a40c0101c90034400c00b025040d40c4c600707138805064410b4900c10a10fa40c0ea40082c0b0804e070701200c001c1d01c00707801184401d684442d070141c8400b407044980d0302148268 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 477742841 1250 477741591 477741617
    0x1050f0405040c120c0807021c02070e09010905060c0306130c0c060c1d15121b18010e0105070b22080c0d020606090106140a1b1a100303080a05060a1a0a 67
    0x20b50300e8a00810440e406880380702042840402c149c211018843c08521036102c002410311502c843c81d45c06003010a0000c5824548c9003400c9180001c041c002859209080052004650790310f030a440341042000008100052100310030ba035000701003a406090315081c5884540d515900c00781150042d4020b6100c6400c828015007407103190f404841d21101a940c08001220b415403c0c1401c1c1a445021644e00d5100d000020b4821112500030802e500030760314800c02440d8081d1f810007400c6a01120a10340f07241070030340340e4403204140540605280b00800350a51000610041511240c40940d004044246d88000380302c10107546010342021071006009080104840e80340c10203100e412114240d4550007035211000c040801984404042c1c17050022400005110b103020403092042580680850181001c3c0000d90f00010b80004245680038070800310306000194105e5025500710b009030320001002e503503001c00314059488640046601441c0d03584c0a501c0380c12103900a21940004c1d66805410a0328 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 477744091 1250 477742841 477742847
    0x110a151701090905101805030c0106180506061c0b1e03010f020306033408010f0f0e1002130b03010e0915150108070903080307050c1501080a0201050f0405040c120c 72
    0x2d030340000c213543c000800710845940c46400c105244403104261146062039541c0e150f2842c0e010030680000d5944545040202c220101c1e80c1c503403810f0800c4814012071804100190880c4969401440c410f075400ca160200c40f66035034090300b80420007402005110030b101c450f0030407000302c0b400b5140c483d40c02c01e03031020480d528500076a401020003030000d010344103031519110900100840d00e54015009001007601c194100075201000302204000040d81584c100c0c00d600540b020005040358040c01c00413043e20320440042c1c1e0003041ea40340c020061300c560b0501044440c0082c568071244a5810100000c6a8252661006402050007404440b401d00d07843c0c0b14100030b44822a040301c94201d48074080603055001d29503261b8403500e01c0c81c060194903100e9450504a030410303610800040c201103040c41d484a4100034001c50765120071040c00180d071404041c6951903158503402810031a011603501000280303e81600c0140030028000d12810620120042c5189c0c00304240004450a000001d150240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 477745341 1250 477744091 477744101
    0xb090c04030c121e0807060c081621060e061e09070f021905060105010f140f0a021006030b06280605090d050601080313080f0307110a15170109 63
    0xa8040d40a1410615121000300141210102613600c03260071000070700301200741941079030058807404905440c2c005d142009012282c2214048052001342e80a1002081707d4000d003c540e0f825500d000200300c0181c25401c2664070160308040302080c10007002207034120715187d1281c442c0400340d42c0741d00e24003a80800c0001a0020340310a540000c81000812101031040018034914100c0c0d004445e854001000780407207203640c0c01d000b0b4805401a0005010561f800003a18880549619011191504100140c2414442c05040007100e850002d441b44042d8000d03c0304410921032075808000b01e903601c1c1007120400c04120356003480350313150000c4020058035522119001d02c0c0301c4800d4107850380c00d0000c25142c6900c201c01e200d40c44040c0d48802c40008100300441400ba00000002c2c0d5100c0130b0390a80c04108080c030b40c2114138560441e01a1040000c03000068420694014000c00c082035503a40204a00d80c0d00ca40007922911b0701e0841c00588641c004003104504410510741060507030381c0e2500364007124 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 477746591 1250 477745341 477745343
    0x1060e0616020105070206040e13050f0312010e06030a0b04150605011b03080c370c053a02032101080d14120103031808060708010909240b090c0403 65
    0x24000d4010007000d03500c83c001910b005440038144034541a01c4660840c1c400704125903071004103103404e5544040040034417880c004907121a008604080c00c0354180c1c88145014092a4121415080060f0895404102182015400200344c503001c0c00d00781041040b04032140b000303001050414000250325440742d60808003000a40101c101c44041540e070842c0c0b0702c14091b0042440701300500050040040407608001107000d00c1f0a090b0440300c004050500c01101c1091100c2840314610703902021990105020b500000031200380d100003c1d400d005d1650a640b40f00c400c00545007984c541407d035a40002c01003590003014900a80c2d415100c2e02407401d202802d00a00700a038004103c1d002c0c2590054495400803283d15404900f0241e40c02e0603060303072082c00d030300540018900d0742c5e01c025203110b0a10358402030811440903012629155401604844041c803480b00603e0b9228a24001d021803056448040450800094a0985214243d0b0060102040824840c0300801701080403000c1c0340d401c5900722 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 477747841 1250 477746591 477746617
    0x1002211012140703080408010f0506060309030412082104140601031e05010b090f1911161a090304051513030303240f0e0601050a022503080c0601060e06 67
    0x211100b0364584000d5048010901c03014410b00001000254440000c1c00147c00101d00002d4141034141940b0107a45e800b030a4203001d604c0030800d01800079001700482d42074035040407280e41d205015203410b215a104a02400c00c1044004031150154441c10f200c0c01d0007107000740391200c4020816140d050b02e42d0028030004144000f140b000d556204841030405448902950000415401c4800850401c81e809c076a80060606910104005150200018105859001800c110a4020750784c0c407445407250b01d201300c3c0c4060b4600b000800b009803240c0c01001940884050800c0d50070103076802c40d5a5041030050620030340380c186184900078542001c0c3c0d00101c2040c00392101c0980f0710b44054000f03101d0420050b03041240316581c00c0130740e44607080e10001030800c607040d0700c6082e00e40504005014000b0304218104001042410140c035070010b1114070b2203850b0b08034611184046150030491215652005016440114440c10650004941d0604a90407900d8416103040c080d0704000c482d100304c406007060 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 477749091 1250 477747841 477747869
    0xf01080a0c0504180b0406150c0803060f1c0203060a090c0e04050313060e100c030c02042406021b0d08030403050309030f040801091208060d021210022110 68
    0x80c0c403600100c0c10303000e039820224540780d2604500070301d5a120303110003d642920b401181c000b6081c85d116000c000d111004e8014809180c0c0d80009040180c900340103041c000b40400403c0660b03841060740e00922600921031660340c0c80c17514203d44030754400017080c3c0c420b0141d00c00080e1008418007800303180790b910061752014030b030400e030b6219160000074000741d80d140700038001c0300c070b249400030009009800552a0b03614050a440100924031300303000c031208100416002c4000c00280c1200e07490981039412240802c03890340d580c00248180300146400001c0800391100050056004650318058214103e10304014580740801e02485118048000341070341d501b000003401080c81017014581101405040c2c900d81511040107101310b4106402130f005d0f41c0d6603810500b0800c200d00000d031041e410320b400c5c00035442c98990005840000f100c907000c1d0094a640900365210311040c01005440c40c0024000c5448103018042c501c0314201d642c60034420186480c0c00b081e0407081ca0010401100d81d03030002410 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 477750341 1250 477749091 477749101
    0x5040c0e01180e010906020a170a150b030702150115180e0f0a060f06121415010c0f0b010b0903300a1107060210060509040507140102030f0c010510050f0108 69
    0x2404041d601040d21355035a188000050500d00041c0b5840b00c941e0b540c1503503111001150221303131902034010345900e0300c4e140e1600b000140b00194a422240e440c0c82c504d480f661880810381c01c00464070030700c2003404102d800104203078502803035003c600c526590700c46501d203880c8205c0341d10540141c0200e01c8506000c0001844d100c002008a41c2d01412140c07021824270b60b104019260b007005c2d5009403000c41c60394003c82c50601c10703e110f080c20748101520410854144070040e1150600c055800324108514400458188910f8041d089070140c0c0c0844400c8856079a14900000c0740c0105284901c02e00910b1600e2080e0540010200c0140013004401d40d4030032400320b644101d541c0140c4110341808203410300d130150741d034061000c8070007014940c015105078040300511008a500301d4101d0741c0310784080030134480807a500090480c1552144850310038000b80700030040c0c0c994000c01c120040c50b0b00c0001800102c401040d000790380207031420210a28855161800c11800207915040d4600242910000a07 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 477751591 1250 477750341 477750389
    0x1e050f070f08040306060b03061f0e060904060314010b01020118030e21150402040f110d0c1b031d090708040b04150e0304140603010302060406050c07050a060305040c0e01 75
    0x206089110307060b128a01a940d039200e03c280c07001680406180800441084518127010b100051984100d12640d00c04e038001c9640640000070708411680504804074000d0b01540313540e4020070181d40c20200005189802c221141c3c080c080c07a5114034010750170032041c01120100c112160448070380c5034440c0807030411890244040c0c0074034107080750002101c415585000000a005003055280c1004106141c1e180c140188415580203441e00e0062610305050300031840e40c658140c1303076096030205004c905201030840407200220b480f1049688100380010110405400903220840703850440c40b400c11102f03d004c02c00648200032134440d0040740d280c0000030009030214851580c001e10440388500e02c90100007150085660503940012039500019060000920610720401c03010021901c10f03185606550100300f5600440c89a0400c1c0207010491302441c0105001c0c0308050702001c2e200c0701240c1da0301c3c04010080e08040d1015a4800c01040340400d2148401c0d05c00344c160703503541020303001303003000c80c0841 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 477752841 1250 477751591 477751613
    0x20d0914070f2d2303161a0c1f050106050a0c020d0312050c071109060d0308090c060307031416020d0e04020f030c0318150a11090a061e050f07 63
    0x1051411403111078005031a000d121031601804049540d015940310008442007281c0c0050030141c8240e06c40c40b210a02c1082e410784070070039030b541e0400b45903000d41c903e10303030007558024001452441c1c0901441c240001140c00707210200a403603800306000d5a6a2101c2c11703922482482c106600180040c040b40e000b60a00380320004140f80302c3c2c68804000c1141410010880320700783c0c1c0c09040d0000000301390090094206d80c520a50038211020384190030170f8000559800c609203c01018000e201002030307200c100902101ca607040c0301800155032460a070310000d00400c41441d100004405140c04103408140814600c1c0c0c0900e03240e00106035a0400300d01c29285000304400c03075980941c00b042412070a50f010005980622184001c031a01c9060107042c01d074100398007041c0316041d540600024200142d10031181500403081640001d81d2480b080f030840c1c107500c02c440301d19412000c443c00008a269112126000100001e242200700895a1904560911500c2207200740e00e031007840b8004c00719102c2421 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 477754091 1250 477752841 477752879
    0x6090215031308301504021204060b06070821180c060c0304120606030b0c031b091f0c020406080a170f040f0f090c03020c03070b060f0301020d0914070f 67
    0x2025070000061400000c001035100c40508500c044c440a2080c10042e035600403010b50805c072010740c145a0084084001c3e29001000500825101e049810441d16001d0484402c0c0790890307011a81c418080419007802c407071404e01c51040c030000100059003004242906954880140302030180d600460042100c5500041070302c01d514007007000001017802048a1880026103d0b182c007040d0286541041240e540004007884000001007040003860a202c8003200c0d6003500c0c46e1103040d100c00380d410205000d450710105016440c4041c1010055a681000c0c2c0c4503601882210140007a079200e6204680b01e0810607c01070088464810500200b815880540805000400100e05007a9100301c0f143c6c14401d141c1c0a41c222481519042c2f003040c03114010018900401c1c1825881c101d1110060360f5248200030000d004008088041021940ca151003082d040c50b0080c000d41d00d038001c41e440d000041c40c00103003c882d00c45480340103c2e4a4880400e0220444002d004040c105520f4002403078803511102c4d035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 477755341 1250 477754091 477754117
    0x906041a04093909020a020703120c0c060e0918030a08060409021c122613020405090d1d0f10020703020a03030815030c0303030601030c09030204050406090215031308 73
    0x81410301c01183d103000d16061150a00003012890f82c2642414154009420132a6507500412021005c960000f40007403c0341d81c0022003006003a03496404a40181c00c10340000c103021020003000900540c058ac00b440005400c40d84240240c070b41c840c400d4108620009880c3c12a0420302c00c00e1400b50040c105998044005000840c4900b003550002e400014065140300314a880d1031340000612012103108101808a8100603c42242c01c48031400305c0d03e02c03004c4404c040c2c214603000840000c16250090703903055010304203002070705201c0011070f194050307030388110000380001080e42401100361030481404c00d000703070514a440400d03205020403080107902c101e0951041103400070041e00c818404900440c025690021241000304400c0600c60003d80101c1c80b0f548a02040001c2d69004803c403034116109080c001a020180030042d500025640e0010354454503110810003405600e4101110441c07088a10b10055014004800418003040d140d0040003100c5c1e1241c400010150320040103c00c007003071 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 477756591 1250 477755341 477755363
    0x5060d0b0a06020307050601080d09030f050c12010209011b0b06091b070c0302010e1f0e030c0d050c04050c031303140708030702011508030705120d020c03040905060906041a0409 78
    0x22020a45078021a4492801a4400200c00042c1309080c0061800b510a90020702802d06006400401c0000240400380107821a0040101004410048200b544401510b54480c610782010703114000d4024810450110300000710710900e4142600c40603403101d600800e050b800e07480300e5060100848000304500000c1c02c98070580d00c0651400009000301a100d0224913120034114400184540c102070203542c087c1100002c2481d030030740c0c02c14101c1216883e610307060f1000340301100000e180103580081250803036110b540c140700303001011440061640d001c0d02c2c2489503480314130840607144021698a401e0740e8a40103c40b0000e4810b18480110300810b070210b50401940761600c4907240d100341c882c1d9000d83e40d10b08565803c81406512000100031400196051034969103501c2d440302c3c0c15142c800c1144000040782c0c3e4603108241e040c4c82d070445108003141d48594171541d204004010541d07000344140050710000e046440d06008049072807140d000c01407424040c40052002502800c00e040318000a54 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 477757841 1250 477756591 477756611
    0x2209030e011d060720280605040302030a02040b040b0a09050103110603060d0609030203040b0f070b010b1317190503180f01050406050a090b0a03230f07050d1416030c0e0a05060d 78
    0x80b105014064440302608004c1d00341c1b003090382c0420030362644603105002d001e02c41000541e8010911404190f01a2008205540100005401010520151548141c00550100e1801c04036401241a42d124200a8800b014180104460380c0000c44030a60710030180b20b40b9400240c0c881c3c214a420b58402e00403a0704168854009169981044030481040320012a1800c14045101100340c010701170840c4403468800d981e600980d07000f0304d034010301140c040e01c2e008016400000304a030130201c015901480d07148500615040740c90754440d40390304560b80691800c500310340c5415a029003413104161940b41c41d29240600595498101c0d51110051240c25540090400390b44001080a8002c941c2e001400001e0000c0081b10340810b029003491501c400c0c002c020905559645568004c0b00f076062a0380c4644c0340801c0f95019040505107040503549040a01801988114841f8004113072500c003403054106605040782c20f090181e5906a00581d00c00c0304104500340600142020403109101103040c40d85 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 477759091 1250 477757841 477757849
    0x3150c1e0304030c053a0507060f050f0f060d120315060f0201150e040f150c0e010917100b0103090203190c120308062209030e011d060720 61
    0x8200c400343d02284c10700002404001051210b40b0044466030300c5010b00e0902461080c4540480f0301d2100c12401042c4ca540c05003500800548502660001c1c5c103210b04e540c000c00d084054101980c0c1c02301500380f12030110710610b40c1120914800c010281181410508076241d58005614144000d82415640e081c880840c090343c4850350081c100544541c4849803030204000d00310b80c81d071114000401c00041d01071103528040c241941c0c01c181c00851b40c91524141d82401481e2600c2001d0320f035440b5240151315404550400c800700361501090700e40d010b64a50325522450410811902000c498209003551801900c03640e0002a10b91010700d0b0024010021368046450480742d8018901c0058020b20b1a008109100d043c2c2c1000d41681046414200040c2d5400307031080b00c020307106904c907540004262010b242c2c0c00d254600c02e803040c200240003001c26418060946211180000d0000f0305c80c0c0010080c2c0c140c80e40c0518400300020340324901cac0131105d458041e801c9001200000a241400c03e050105685e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 477760341 1250 477759091 477759097
    0x50c0d15020a09030b0412020f1933090b010608040302100e0f0d120f0b0a092d0b0301111305122b02010b0301060b1204051203070f03060503150c1e 65
    0x84100702d0f5428500a60201030b14110509d0520300e040c0d0303c0950300c1180729000305050310515610500385854003552020f101c83c1e0300742e1300c0000b00600d840300c00e850000038601d0f0011900c06000320340d031502c90390703ca120448902c0b10466000c1e000d80c0c041120504010303455030000302100d4200059500220a804006061290209003080040c3d41d51035003848210452040081502441204001800d000c40200c2e00b80f51441c41110103c9590300000b008000380904020590000000a0f18000074505204001000c10003242c60180d0b01e02500030b20320052000442d071028640100e80f002d81840d010401885d0085000f141c1c08600444544800e00d0001400c4a5030b0804403002d41d0081900f040c034001e08507219588094407070380c1041c1041010301c10400849040442c10360362050156120304000c4d14002010000007103e000000070840c5030790f44001503d20201c12542c080c000e40e682d030410190760300320790002080184107203804100c0301d03010280103001c1480711680c2114020002d500c101d40d150 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 477761591 1250 477760341 477760343
    0x61809010b06030c120114210a08070804090f050103022214070306060f02060c120604140405010b15040509010501110f0a050c01030c020d0246050c0d15020a09030b04 73
    0x4000801c0c1c0c03c800413407401449000d002640710b8141245503041c0040c0144d2824209903004e08c010506000a900041c4590440a41c0000046035140c005103004692a03029101d83d8022629040a0f120644454000c0504994006082181c10f184080b4001741d0300104251200100d603854841c4c2d4102a050701d43c0b1407240806441c0003401c140340030400341c090040049814119040780041007030501c950800c0e10356460f002c168000561303036480d01082c01444ca0101c1c4a00e4491024108410400c05400c012070036401940c00b1660039401b02e0382c828583c0107901611ba4171840748070051045501c00c0529003011403920088800d000600c01600d414031803040300580e025044506c89510760f50b0503010b43c402c1c818203480286445408420025100d104020461802c0903000402034840c0b0b050a40c6d11022540d0742100e0241d04800b0700c043c00550079130341003c960a000b480d4840902b450a12103100c8026085440002411200b41c151402036005072a40310605c064003c0100110b5503e480c128459 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 477762841 1250 477761591 477761611
    0x1003080d0605120708190b01060819020c060108160b0d021e0c07080d05090f1002120d29060412060f050c0304050f01050c0f1c02070507090b09061809010b0603 70
    0x80c83c100f1004038108106116001b100d4003203148060b002640340031301d440c1150940c2c540142d050702d03040e01240c00308294030400241e050000c102c01c00d40d00000306003541214003400c12640020a0703501c003113040943c41c0c4102a0650414881028000440d8004101c22030302c0c00e80c0c400144601d0340300642c040d0010038418207203620a6030f083c04203900c100042c40d03000c2900d05040d410403020500094214144442c03050060320140c41100b4490b0082202d288007030300b440d00540d03c0350140244070006203441400300e818041041411929040f501c01c0642c4580703006040c240c0b501d400c0000350004414028011500750740e8030751540c80034030385620440b0f008003d04440203030f0368182428161726000d2070103401180340c0d01d054140020f601b030500071154140401c82405450f01885d550700c451810f440501600100e000041400030481c01065a000352109184200020b543c02c200b4000744800c101d1b68150800c2105442c3c0c9040d0740b098030704a80c803c03002000802c0c1018110007040060f041900d080c3c2d00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 477764091 1250 477762841 477762853
    0x16060c0302010b0402180f031606031512031b050c1903201c02040902120a03080a140c090609130204080d03020c03031611070b04031a1003080d060512 66
    0x8150782070041d143c40e0302003120190f04100c3d000340f000c580b40d00c820071098410035500070403516980f02417020b040041300103c0100e03c032030b54402020780582140742ea12000060101c2000c030303541d80450300c0c42d42010707050340d00c1d5404030045a500c20002a801d00066415100e0b000482c402c6955010030030f00521114104190f03024550307c0d0210300c43c4552900b4400e000e441c01442c184075280c00e105007080100100d0449440707201030000c1801050b9a18019401411070585400440d00001c7d005036420f22075900d0706429903c0400500c1250070000c04040e1849000f004a05d036840c0075009007002440040115180c00e01c5080040d0701b040e41c640302400e85a40104041100700d42c180b03c1c4003440701003400c0c01c0d49007201d000001c945a03c4010104403a201d504142034050610545285480101e580111420651101c0c0c052109030020311088440c644034180074144005c02e10740c030781d000f0003003e080d444010b82161740e80503482d0046201d10740c907256034500001e40c036552600700301003041c45030f030103050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 477765341 1250 477764091 477764093
    0xc050a080d23060112060807030818060a0e091b1216051e0706021c0f060501030603112209141605060d05040206070f0302010e21070b0916060c 63
    0x341c03040009048a101c1c00304600c0c0300344403103601c0c026030b2042092170301032400b04040410f600141065001107203240728407503001c01081070030001032682e080380207107810b44000590200141d41c411461941c0005020381c7c2e00ca0320500380b0300300094221030314a621010560129050441c0c2d074100040c203014200c1d900c8184110080d42640210040f045440c0071850030902c040814031a2204820041c000e02001881005000680d07040c2d50060984181034040203400f100e00f100940400044800061310b42180068990700078440d6030116540030b2921004072500c602048416000000305e00341c411404a086070a10703031f65101d00b04005200d180460140c0d4140c454040c50f1000ca1060785003035000100e8180b1407030741c0d03010580707410012500010940f075a46201041d040d0148080c020300010030066083e04243d019040f1a112141e640b080307a181003440b518408004803800c0b004c1d044082c04000310700200307050401e52507000d2526021114126501421403920080b15030108000914082e43c41c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 477766591 1250 477765341 477765367
    0x7080d0e030909250f17040206040b03010807030606050a050a0501200d090602210702061e181e010813050a02060f0316080603070b09040f0f0209010e0108040503190c050a08 76
    0x44008a480c40e210421141104024151b03142c0d00017441506140a030010f400c640ea80401c49010b003c038040e15907180e5a6490040d5640c09040c00b04a8296040c02004100c90a21031517210032520020000c030507080c500001074800200307a81c500d8005255948400c1d41c5480200300c1604904000d039201e5100c28a400c0009090110240c00f41104945001484412103183d130706a58001787c0440c2c0c41d6590350024040300f070010746000807000300f01c0703004108003d607690092041020240155110000081c000d11000d4007011400703100f0340851070b80c1002c181c000b00450008000e00d44100304507001200e40381c000440c2604650005c440c036170400004c0103000402144081c01c203e006051014075402c002000a42324011760044a1404202040601955841c0e07000840c0150500d00c0030008a22a070a0302000b030351061202c0c80c046610610400e1603544941c01991240c3e4015000e142001c0000502c00701d0743d10b000307114208000c0c2c400102c07800701c7c1040c01640c2c3c0317141c850031003103660380c5c041010340c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 477767841 1250 477766591 477766651
    0x5130e0a05100b0f030a083105010f050c070b0313170d06080604080703080403120e0703030212070f020906030109140a020910121205040f0806061507080d0e030909 72
    0x3134000c05505018843c25100019802ca4195100804a44421001c61140381a085c026548844d400300e140880c00000000780409003603407030a03a07a2948043e030182c000e507014070411250455a90144c4c500f084031001050245810031104a4954001c0040d070300d901e07100030070844103504026000281c1c07280100340780c4110001005140c018103458a07007600c03400c001d070180c8200581440301d0303400001c0c10148074840403c603500c402c010411070360034102c0300d903030366605ca85c04220050b101741560082c0c641407a10030f440160303920200959102c08540d00f44428520050071594145d92510baa8800103106a1000c03113100d00c008000305640a682d0040120706007001e48140074180101505000280c160102c580c003054009691400341900f01004580701d1045e940102405c042c00c840c0461000b4000c01c00034000c500c01c480f98002101e03c0c01c2074145500c1487c10060840c10100640300401127560000d0310040040c100fa2410000b04030041280020112000e8100900444141a80400181030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 477769091 1250 477767841 477767861
    0x9060f050f04031d0f04090809150f0418020d18150c050307032c0a200a03120c08032809020f010309080c100b240405130e0a0510 57
    0x205080c0c2403580b809000c08a200034881c4400441c1c42085082c0d441711000703881145000303403042159118504064415801205907144104103104500c0401c1d03103500c2c1601c3d010a190709070750b0b00e00703490409401201a486000508600d80900500071000c0443c4030302090800504c400418003000c0b07140101c0d003130f540300d900022800e18002016030266030020540c1d90104ca2424005001900e11001141d49050b0300c0446090314040c0100101c02107000c00c17000a01740c8202036000c41a01043e02c0f1426004003c038407141c01c00009402080824401031120844048600b8202e05211050301d4603000741d8000c488500e22202070405500d0031185000481d2032400e4038107420800d03603d5944c0010328090310940140d0401d42c42340036000a2100440c02c40354804c00400460f80d40d40c1c1e00c0c654010280180c03128551041100590000d050780c0c030707129803034210400381085500c0d1034240030800688400301030f0640f62095407070b08034007601d03102041240c00c020301440c0100482943d04402c00240d42180d21 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 477770341 1250 477769091 477769111
    0xc18010b0a2a1704080a030806031c02010b0315010315051909080703110307030e040c1103070b0105010905180705030c040909060609241a0c061501080c03090319030f09060f05 77
    0x1007017403a03000709000c01c0099151418080640f2810700181c42d02c00348008080703032060407900b070000694056104405090b019402d0350f58068072212881a003800920015080e80d00041501000140e1544025404680c01305c03101401c40a80040c00101d8802c0d14044a81c8580022600181500880c2003080c0201c400001c41c9040d070107030b81c010520740d0a4184280170315240c08124a40328001c40e90a18100c1c0c07040c0c1100c0d10b81085003000e12610801b80301c2c46000c198200804a4030707003804e04004503001c80d80128943c9a490f1040b04481f56440100142c04c1c1c49030500020071244010300885512501440003c641c55040c52441011903401200310407070440d500c84004d611100120903001101c00b8908400219202130010610600c60380d131454100e4000c83c0100003000b914005041641076003030f61b402141d641c40140c20b0001d84400d5912455950050002452502003041840d009813058070340410940a0105141c0a0306c070b107410200c03089611042c540340130030440c1c402e5036840030282c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 477771591 1250 477770341 477770347
    0x2031005090c04090201020309060a0c06051005101209021020030307090506092b050606031b220e010b030f1903052104080406020c18010b0a2a17 64
    0x1001c0a03940d01d10a40d1414000d039150100042903a0090090300d501e00805071a09075212107100d00148110070b40c00c8110303242d620300300200388802400407411040d40c030094403c005c0b285d5044010780392400340c4810030b03941c6621809180016140c03030b02c2c15074610301c01f6180e45802c00038410030000382060108840c1e40c2a80281304020701030758401812800c40f02d05441050742c41d580c03040403812894686000c41a0006107134008160707801c40c0302205030742c1070060040c3c4829484500400d070f2225400c42030560351303800d003030742e800011300e000d16000c840706000326220029810603401242c1a18a0b5008442c0203954a00d100708403400c0510940340d0110604004d07000f000c24040300100e0500d81d5820140c100803011603400030070fa0710420070300314200d4a031681451901e80b61411044540c010300441c001401001c00d0031955042002404550240c4103c8031080b42e803c06140c0741054000b0950a0100070803e1403240f22103a030303481c0e0900a482d02c0d400407034500b121403d00c0c0350311104884060081070020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 477772841 1250 477771591 477771601
    0x318121a09060403080105130b0301110a02060a0603021503060d240606050f03010b0a230304171c020d090f120915051c02070506090703030e0a14090c040e07020a02031005 75
    0x2ca5406d064803c111810401d00c1041702014000b095090681c0c0d8040d0720b850b100009100c0c81300050031000c038060342143c08560324440d400041c1d0f051440300075001500d103006036407580b800c00c0141d40d008101600d03000c010391140c2c85079100013001c10600e6021a51901c44168560400d0140d20040c01442c1444c3c1e280071301001c03ca10b079610051140544c0d80d07001240c0704a1062051554200c60b01030161809032810388030300401e06690042d42e0891f5071807101105c821030b0b1500c44051704d014900804400e4114010701e01500b000e503200035001e561643e40c1e200414005034540c4803c200542c0201c484c070607000311008015211a01d00e4200740e80c5044d8054a1f19136131507000d800c54003c0c414003001704204a03440b0f03004401a009404006005000b041c00300108000c0025003038080702e009031307030380e80c00340000b10184900d45c1114000d402c0301620844100049003489603410b60000b0158104501d8550741e00c11201c0441d1003588c0350741c01600312074584400d40c6020032014201c404085000c200a0070b00d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 477774091 1250 477772841 477772847
    0x307090b060d1515080a0b0907022104050409050105090f0a050d0e06073003020901091e0801050721060e04020d0510050a200304050a0318121a09060403 67
    0x1038120040b9a1512802e6080c203401c0102c010720300900074556001104801103101070032000e000c691054100d45440042191450300501e030b640a1980c1c0d8010b81600c403541612400300d000342548021066004110000c0c0c16100c5206a07804a801000001000c2c00d100c1031990074466903100c81c43d91035000c4d19111010880100740002041c0d56400d0000c03007882c440c000700340d580c001e507000540800503207110313050b940034a409100e0624207038500c5003400b50105030094040340600e080d654000340b5008820b0041120000724072301441c030b190b80c80c42e82c01c944c5c0391022030a4450484070200000d44d5070b0294140c83d109400c4032221445000004d00c0001e0610f100640c072010001c201912800c8000701580622400b409443c89011180e00180003034506004903501511022490f81c45032020389a515013049402c10030f8030b00459000700a40b42e0820f0a40381240c0c0ca89601c031030146500e00c101030010b20805e60404909882c2d1044c03900f1140042400e00140000c6801448800c46e070f0018010040080d81c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 477775341 1250 477774091 477774097
    0xe04020612090106030f030e0102010e0f07170a0c06031401060908031905092e050f042922050d030c06021c0504051c02070e0103020f040f090308060307090b06 70
    0x448208810303003a0b55624400d40903001590014010540d013031034420a05901120814070355070203030000d101c03148000140c00d6480105d40700c5481560020302017440707003041000303580400140072801c4031003198068036031b4929240640d005502007587c51282e401c580051b40341d514010b00203420030244c01031900342d803240c80c1d00c01c404910014031701031815000924011001c0d20520b41c4080c29030384c0740d0580340d1003044108010030380600d4184440450008018420400c0354801c0c58004000c0741014139181c90b010f1405889018a90b2103001e1903c6005807011110242c0300101d08c004414194000b50503150b40d4102c0030743c2055000d80c030407150701d10202c4d03044032260364125440392006944840c3c803640111a0b80e60403d034800135074249401d01050202c00103032103000301d0141400030103521801c101660341c0c00840c402d100003805103030010400340c64100b004200031a006400130031040641c0c041440bc40741d00344403c40205400c07030705010040c00c1c00c00103480640500c900800c01180d07038000042c2140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 477776591 1250 477775341 477775357
    0x1b08030f03280c020127120e2806110604020f040e0a05030d0b01052a1507020d0e0a05010e12010902030601031a090616030c0207080d0203070c0e040206 67
    0x5400000031800c2c00300302d80c0440b85a14190840c4651000142503a280074004641c0f503140103608100c11200c4002c6410038140030414483c400d04020441940c900c45126109045030741031040054004109848650403198001d50304026158001103152041150003003613007010080184d9400d400c2e050346400141d00781c2240e0110f0755165508101400180500703081c4e0020802d9000348003a1034104000080a00ba1340c9120b01c40c207100c1400318600448441c01002c03c1a01c03020070303000138101403d80c20005010182804015101038080b0a100d81410b050262510801603009040080500d03900101001d1251400c5507100001854680000c01400200403698070810084290303000310582540010b40250340035007640d0b4070b503a503400e11403610303a6040d1486150205500c00a95075800215841d4030a1801009840c2d240b00c0c044000c800400c400c0300848150310400c44003142d0694100f1820b111400d46900856a914092801000c0b000036a406412100031030300034031005940d03510a48042c1c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 477777841 1250 477776591 477776617
    0x1b060c03190e0c060c070914060913210e120a0c0b09060706060905010612060e150f09040b0106030c020c0607030f090f0b040302090906060f0f04150f031b0803 70
    0x260b01100441800c0c41c14441886903c034500186104400d40302007080344c112910882d080000300c0d21000070141e80c0b10101d40599102d03080b03400103031113110b07204042204940a07180300d0301071542c842800354907400d95010840100d007010454540700d18002064000390101c0c0b03405052081e4150b501d4038040710850080014000b00491580466110700c0e0582d2040e81d000b086c2400915a94811403000781028082c13500001c2107002040300d000e240b40038000c200c1c0c1d00e03404149800c1d507d20000c090280101a9100e031301100c02c00c1d074071480383e031210f424174040d50040071401e445500d019030180c1140e03481c0c4210300c103640004003014132030b550300c2090340c51132901401c1c00c0c0c07170f601d08110007143e1081c2650440b0f004200900c0c004140121038038054000d8030301c20760340d060164030796022055449400b140c8156000d200300c40540507034181500a2050300384003400118505100b614011a0035409402881208a00e12020024440d01d204121030003000460040c003060700b001402c0b034892168450941607 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 477779091 1250 477777841 477777851
    0x1021201051e18010e010503030f09011404030602070501051609030b01030b04061506050d06050901081009021207170c04330e0a0e1501060c0b060303040b1b060c0319 73
    0x2402ca14400c5000ca8580041c508a03000d0009640707100f000c0c6083c00f81d8904e1805000001c6202d00f00042102c0004044060f4513003003440c07500046070b554a140000101000c070a02c000400035106001811540344607800104907403400002101a4803541c0101c1d90400c52421003c002254074900303210f06603900440503030100d80d40d505101e0040c203141200520100c0c003041c00010380030341c00405400d020407064014003d241d81c075010040030031828015080160044460340c0e840081c1544000c501c180302404a0410351091001a803c19082d41d0107076030010880e1010203086001400f203000200000c550030071030f0104510340071401d100100f120020040d6041c2e450903510821318070200081000300c841344801e2070025882c00c00303040c080074550076610503c031074180c1e1004a040f2480c1681c056698480c0f440f0000d449214095401919041c2c05001c108008100640c8040007450144e01801118111803078105400c2e02e000c07001041d802101c4414400d102c869042d080650404450700180450307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 477780341 1250 477779091 477779119
    0x100503090102070b01120b07090f0909020a15090501031808120a0906092111030d02070f02060f040f120506060103020304140708060a060603060503191b090b0f030102120105 76
    0x1c02445a8100500031058001c00050284020b000c0340c1e104500c00c4900c4a0b05441e010340664940510b0300411504070054401880801711a60100c44507a000400f41c1d41800d6031200c180c20320180b8800340d0000242516018026560180a0b06103020309588182600e81480d40741c108041c001c014a0308103d01608001c280b0780e40035600721082803600248104690f01241c03030404800b100e8555107201030701c065001300340b165000307090300469101140c024625081c04028000020360002030100c541c00012a0740c0780c09a01c410001c0d00c10b02d1844e90b510b40d521418250286032003401903226030b00c00b02181504c0000540045007040d0418001c0c00e0160b00d07911680740000d605522824484064800c1540001340c2410010b111f900500d1b04010801c59aa10790000b102600c0442c0980e60b00759206200540c2c9111149100c4070200d8040d9002d034510b2080032100c445043c4896012800040e2130303500c0540c19107003490020300072000440086140c81301ca103614a22800b0144100d0b4070072610704620348 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 477781591 1250 477780341 477780343
    0x4030908010203010e040b0c0c06010308031306140103020f060f1804060801020705161208070f03180303050c0d0804110906060f13030b100803040b090316092910050309 74
    0x18028001880096403a580c580c1d0300030580c001c003110107072040b04084000c81c0324080080100c841c0340718803001600081e170864486680d6070b0310140c4008200d0b0303c0340c0b0382d07100401d8062080d0b0700e62403ca40035418980d45540100510203031882036003803040c001041941e4809900d10304958107a40402e104001c40c1e4503400c00180141010790080244d540002050400c000300491025400c0180c420700c01035941e21040940c00c0701b0f140e194010688281001a00041085c000d80c1c0d0300031038443e01d0900c0702503100c0c620401004180303034000c502003000490100030035501807056a40100700c4c1d28002410340381580710824034809282983d4081ca209002142c12502d684044030030302d4000840040d900c07007111401800b4141e55210554000070000040b441e80c0140c03144100454203a44021807e0501b0b0030034080495110110242e414810b00e80c805428000a8031140c00408402400181e00801c0d01c1c9580f04041d00d0881c9201d000c1c0001c10215201d42c0c0307024900503040043d150903612079683c04c1c039007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 477782841 1250 477781591 477781607
    0xa030204020c06040219050d0303020f1308030a09080d0f1803080a0c06060504050c0702010f020c031f050708010510030c02070e09161a0904050c130f0807081b04050403 74
    0x65005800090410412100043d00901851095803011078a0290948a6199074440c1c040d40c2c1e0302610600980000c24803e4003d40b2951004105881c40d0844600c41040444d0302c541c0103101c0354001040f10031500e81c1140c0064014107103000600504038a550008003240c1003000c0ca0702c180082c0080102000700c0c1c640000c005140e200007040d07514140c0043c00742c15040d1005003150914107041002ca46804c2038003a05000e0314107509d00e507080003900d0380103607801c4a141a50100718860150300070710381e64042026202d8100c1e0240c030042803826040d130220035160020100c0d014071114030010062500e61407500540c0881c640b0b40002d0f00c0d010b2140480c10700d42e4560107a044562003000303200d0211008103450001c000411440800607a90764414151800c01c035424901e00301003030103000b0311400c282c2c001c44d503c4200d070481d00c2c1c50b18056009030030407421641c00c0740c80c40c0103da03002441080300402021000d40a00001080e062900c2c20844d41d40130000001c0d140607503110404141010300644036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 477784091 1250 477782841 477782843
    0x6070207050f01111606030b100207030203100e160603050a0606030b0904020111070b0c07060305092404110909010f0b0f031002091c060902130203221e0f050c0405160e0a03 76
    0x2200561715503a10f4000c01904041041c0381c405c0e1802c14205051600008401e0116540603016040c0c1f4840c026568004100030050b0702c00c43e00401d08490f207031a02c201c50380310141015807000602e501740381e9010000c54896400c00c205241c9040218003542d0740c0c620260303038030544c240ba141c20501019003006050034007681c485c5107440c82c0810210000e600115138007003911115501040030b660f03054805950f8492540444003d1031040001a00d001880064903500c2402100f040130b01c4120304021039103840003111800010395580d603a83c0700c034859038020191440c9049900d00b0812f951580020f45402c0d040c035003e2001c1d40e00180311411501c0340e80ba000341c0000411100510b0007880e04003c030160941d51022480f414075140c20807810016842903a0080081d98442c01064480f80d902c49400300c0c035104240c9404500381e428000100d02c060400e807040e840340c11001a404094070f405132500b41e00c0428284500e040508000c0313211103075003188500303100a150040151440102040c082001781d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 477785341 1250 477784091 477784123
    0x317040821090f01050c0d090804050a12140309011202030a0e061e0c0f0a0e030c060c0a0b010815060d03090306290301060e1b04230306070207050f0111 67
    0xc1c9603102001000c05a204210380c4040c3c2ea0303024a81e2922500f01c0301c0480d2001078000b4140807161801007940e00c2501906d220b10149458a40c49400144901e1010350100302d4602e024010b21042140c81d04c4c2803010351448100031428541c186002a080ba10342c115a042516400b2000804c08a00c03500528018076880c401d80d280c6092019505500f1101020311110003499030b80483e488101c0c030340032a4004000009042d0400020350000c0310703041c40402d001981403092a04001c034a5445400500c1442c40d000010880ca01842c80c4c040c080c1d0005030701c01840c6030400d0718160f1fa40440451280c1d403041d4101c4100c8a282134629081d182a07042c0e8202400191600c4400c070410480041c1962405190410a10050361050708050030b03680c00d8040c03803ca0010712000302d4034406501000003170074031206444508040c0c8075541c2d225000301c41044940768005041460619050a0203801e40180807440a41243c80c00d020100c0c01da4000d5a11300b60401803e1624074004040c103010310034440034000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 477786591 1250 477785341 477785377
    0x810020f13080d18080a080a02030c07090606030606030b090c0a14031e060904030909050c0408120301050f01110604080304081603110d170109090c030c030b0f0c030403170408 77
    0x2c00180e6609500402070000c503140215072107401c0c002c550000102d45d1101c0c010001c2d0b06040e0380d0381e20b681d04069905030940c801401030b058610317800d100301e03405030100200014401d890000d00505175030059014806051402421070010740398a07141c26485001c4002c410b0f6a6500e60b8011141500312000b85010721002000740200c081d400350700d03020070600368041c03411603865010800c052020191401404a501ca0707d042045c01d59a8015540c020300c0c00844a0500307a883c0e20741c2d401c122081d040018018400001030190b840e0034000700d0750850003071030450070030b4802d51159175480c0070180c000390414201100040070404e0f02411a591898a02c038810450581e618015000c03241c81c1c810402107004503626461824480c02c401e1680c80240404c403a056483d060303100000300803c40069031508601c12000c004201085540d81c015446000d0994080c900303117894600b001000340c403d25100d1801c01c03d010100c1d03481546081c01e81483c5904006917103032441c241c1d50b6845450801d000c072031504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 477787841 1250 477786591 477786599
    0x312040536010e0103020a0f0b0306091f030803090f120a0507021318020a060305130b060310050108060906010807060806190302090123030105011d0721050403180810020f13 76
    0xf5001c2603048920030784a419201341c5a0b4000d101211948c004c0d00d690301030504c009201c41c603100d0f5141350400c80c50740000399428800c4041d2070500c150f40d0001c0d20304070400000e10400c440c0800a4810004000001d070000103890341071183d40e44a02401841045000704401d0195514607a000c0c07108000701d20100078010148403000310300d10003070b081a44503801010000490134043c2c01074521500d038110094295240c296166546403d0213408544c241c451040c0b09141460548145406400004001c00d05403801d1140c0b0b03481c08105030003841c0c0d6900590000c005040d0060b0601d900003070102d801041085000850540150859102a60194404c030000920102203049400f6030400b00c1c500d24a10118101894262542841030b003542d924080504070200070902413440d00490700d454042882224040f01301c4c500d08009a181079800ea88034140b01c1019046980c2c0140031203800041100f1901e000c00302902d50b601e008103141480e400140441080900c9421a4040076443c0002280a034a03 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 477789091 1250 477787841 477787859
    0x1090303050703021501120605060102010c081906030602032e030206040b1c14010609170c01081906090b120a030e010f0c021503010314031213080409051302031204053601 75
    0x101f41002e8840030301d8072001c01d0880d441030082100074141a00c2c1e440032a210390f40000c4456001340525400141c0e680070210005480d400151701076200e0403504201882c10054100340c04031080010505d940303d01100300010703103880d019901101c038484030151715050b1240035800042804d02c1805155894181800c1502e0202445075040c1c2c1c0aa60707503650700d544c40c3d20980366142004800751866600000e8200c1e220b44c441c2e42602da01c820b41d4442c140b0320078540d004203000d40d03480741c009080700d035120380070506242400c038401c11542070644000d0003991403503280075004403c0f40c1e071220304000c50031181701c9005014859801150342d0180458065040890001010303030400e0100703c0d804007006440f50030315880081554203200e01c0013045030454450804881000401f05401c03601000b00744800604c2e45014030500e4821071007080100e40d900050302c1018146a4901c0c1b183c4420f0409002c207000ca500c038000d100540c10402228150300d8046070500050000b5000c0404407012481d00011a0b8210 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 477790341 1250 477789091 477789119
    0x3040b07110706050f0307170408070b0a0b01050904050711030f040e06030d140717191103030108071404061505070c141005160501020c1b030c01090303050703021501 73
    0xa40e15203100740104088103071114403a100b81c90008074203022504610700381d5402983c028802d410f003040c4001c6404a250302c0c24404039010703601503401052420034000b20742016030b40300c0d0044108000d41601c100000e4200e00030b02d000140503e0381c49000402c03890007150310b8819203400100b100d890301d004d003030241c09036480f42c0681140c144a01d0040740e52810300181d400390010064413146120032007400b4000766904400300580d02c0200400c0040c1802c05110002c0804000421400131a2603036648054207154105c00d403801543e00410040048003800f1482c50256030010000080b6202014000740c040d0000fa0011180d85400d80055064250444c0080c41000d20074010360541c1550399203048081e40d0b1808419030803040748110340d4041442500101252031081c2c0b001d10100c0d41644a0034220b802c45c0071011000d40c800a0010b0205640e40c1c44602500720480081c5006114030300020003460711484000d007400300100d048800c040c001c0c400c0481c4c1c02000d6005502c2907035545800c0058403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 477791591 1250 477790341 477790351
    0x1302040e0303040b042a170c0a0302150a03021207030b03070f0602031605010207050607050d0b1504060f09030605090607030e03120114150d050a180308040605040201030e0303040b 79
    0xe1816a040e00a2a804400e5038440e0703800c40040b2440382e40e5034807142481d501c85040c02d4517440d9140d40d03000c1c10400744101203000d81150086684a081c82080e900e03d0710589400d0b451281e96403c40030001681c500d28081211034001c034a4948802071884154042c0c094150b0100c1c8074003003101007201c240c2e416400a801c06074101c04075940655240e000141d90320341130040c540140c0040002022003048500700d410010302c55800140f074001c03a6100c160400d07900352036900010310002508030429403c0d02410686103400c58812070010240c202d03e050620452107890203114009823050000f03070280300700c1401160448414882483c12040150702c03410200c0d5138401103854080d100d91f520750008140c60301403840400030030190342040e200e003000d0861011282c1c1d014809041c000e108d8483c45d400303401c80d0641010089024149452031900340c9a0494a0480450304407080c000403c0d800b4828541140d04101c00280035159400128047d05290b03003039040ca80f10000c1888108150308036528032070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 477792841 1250 477791591 477791599
    0x102070b12070c0807080310050f01050a050909040f12030b011205130308040215040602010207051207020102070306021c0501080c0415050a05011d1c14010504210e091302 75
    0x480e120440903045008079041490045840700c00654864000c03106800110700445900341010541d58400f10b20b41d200302e0b081c0000210703200c003c000303500f00751407119194042400c00a0820707601050041150081c4041e1031310074420800840c050001464446a50540200040c00b918010400207000b4000380220680000e02c8401101000d40c010f101d070b40c0c0100032000400c4164151074904940e01c81c009001a42e00c490400b103031052000c0428001c200504140d000540c80d0b48040c10001e003410005d90743c1c0e0007199003c215040045c6e074003103802001e0340d501460060315400c85c04206030020a202000407212441d00c030003c82c404000141301d40e4410001c58081c4800c40b50b006070070380700300320500c642504541341a10034451980503050016404440c080c1c000d0322187d0076000150740a481c036003100c4444403424005410301c41108159402c1050840007404a4142941c99405080c0f048840e0310941421088a11146104048455034190020b200044a00744558403056220714800100d03c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 477794091 1250 477792841 477792853
    0xf0a030e010801031a193b03040b030c0910052511040f18080405010809010501050904030e031609060807080a020d02040902031e010219081005150d06140102 69
    0x1558410b040850503254031042000900004407030500210074042c0c11001e044510303450002c034000c0d56100d10990720800c100c0080c850643d4170a244081000005800c259203003040f003841022100008890403175209100350b0307036030baa5948120702160007403400ca981d2040700788580f4001e96030b1010140000c0090027403480c5400003010f2002c010b5010500005081c1e0460044c802160311302940f241400903a40007020030000c07148900300d40e510000d08400c07603c100d0003142c00d0003e5684424074951007130050000f04005e50504001a41c000c4009200070104002891501c0c25501d06000381d0704000c4881d0152002103481c1e80f0424080c001500510340c1c20310940800180c01f54000030b183c3d02d065000307401710220260a40a100180036501e40030398052040c80550155030345540e204000403210800011703103403404521100b03c08120203e0200401801409009141114032000412207a046841500da10a16003c051407401550a50000f1610f0560005083d246084619100540036401d07645 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 477795341 1250 477794091 477794117
    0x90c0c160f091a150d05040501060806220213022205030c0105090a090e010213150e040e0d030c09080a06140601080712020904020d1e0c080702030715060302030f0a03 73
    0x4110b4100701c4040d4003254114030111036130f00700741d014104000e081d8640e99250032201d441003c10707140103403001c50f82e07a95900400c2181a03801c0c85010703003101301c10184402c208040024406051001d50000c0d104003803500c020795809041e030b8100c410240c4501c64505510984d00c441800d61a11486581d0180c0100c091003110380d8851411240601c4c0000e05000340703a403c0002c05c000401c00d0b00f42c0c0c800199030802c001d088800344283d09800410101e1403046082d03203140c9008101000b80c03841c16004600308805008120380c045443d04103803241e8940000c090142290483c0d1101d0301f54800c45003406452001424001950441400303c003c401c1104626200c2c6001121307030040c01c171f03a00c500040c540d24a400403581550010280030000802c054109103d941514045410801308070001303011076980e0007081b420900074001c00c80540d04000d00c82e032906020103500c910515200604240b80208008100203d540c441405140c000d802c50b203488646000a540c2e40c00e9180c800c0d07020070600c1010031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 477796591 1250 477795341 477795359
    0xa2906030325080c0105040f0311010b010c11010201090209090f06160905120f06070507140c0319030320030403080117070504020304060b130209150711090c0c160f 72
    0x241a800c0121100114201c0c02d80c11003004500020003122061400c103e60303040400d0902030320f4015400340d400d558944206103809040b10f0180c084140580e41003010301c03071080c0c0e0400350590000350020500701c940003030340004038010240c4ca00000c0d488001c1509014242c500010089554030090007100d044e91210080d4440c40005114040300041c1030349000d00440c1040708115107070510210484100c0440d49903600d003001e408540301c50008a01044401c144012003000390003401b803450144c800d80800c4004a0f03281c0e4051100748200c2a92042c0c040c0405100350b1085101011400c610791940c050308462001d19402643c0540020303200304000b0400d0101c2c4180104010f4241c001429014508428000a500001c00c241c078a1a614070710400180c07198031081045c0200c990006130340f4000c0e20204411101c8038504402451802c1c0305100000324003c51008a0703490480313924611b6170701c2840c1c80381641314142c000030941c002d420b04010280b07041d1000320181c0384100108542d80b52514502 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 477797841 1250 477796591 477796597
    0x2040509010b07020102070f08011505061e0f0f2701020708061311040912020105091207020409080408120711010f0c1203060506040b0409060608060907030b01020a29060303 76
    0x1890303010400500400040070054020140c4600c10300642c2c100c103580d200000c20350042640071070b296035103504c145407001d82c2c006a6030028200c1280c059040c09507046001c40c10000180070700a44000c00030306030301380740100c00c02da5506810130803060355501c9032901403040d54605180d0010117610740b024503000b13960001c59000c040e02e01072070040980360b5400004400e4081d42a07829541c441210fa00c18441ea196401070281d15801032203c40e412140da201d000342140c900401e030101c0c64001e8440c1c200101001000ca0b1045901140c0228841d595030030403444e80c0c4519031102c49644034420b5901900100c000103040401c0c000c000c9242d407452a10010b5503e00802076201000400101410000400340903070140000032920f00000d4207915400032518070b600a4009007601c50700818104141d1016010703410141100340b521501d04e05061010501280340a0450300138151200d0038406241d02c201700b02c0d524903030004504410303040007454003034030f2521242c601c082c0d24110000141d0241000411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 477799091 1250 477797841 477797849
    0xc050c30010912050a0c0c1d0a0e120903100c0c050609010c141305120709060b0405010e010f0c061103090c0301050603100b0a080307031106010f0e04020103050c0d110c0f010204 78
    0x10000186010000403104c5500416151083c00b42d1580ca5101148100d10500054041d29004925668074010100c10520b0300920000c8920300f08080150001c0f404a1006094001d0749912034644280301d001a09158602c4c80c200d21603840c05008416490344503810040031070085007500c1050b01c40d480c02500381c860360b5601e1130100b4140250894035006060052003c410310003882d52a594443c000030700c0c14200c0320b0043c2d2040d40400340a0000050511030000248032403021140f1b010f250400190094403901c100e681400310031410f14450a0180500c203042c1c5a012208105004815440c3c2c1405e03001990008100c0c89441200165818144101401000010300820301c150851900001038810a081d158104400da02d0004441c002003016046440c071a4032800c81003650103a0991401e44164418101d904000000f000010000540290056028a8041201d585442c4e44a08521564864215041c600305009070480d1001c4050070202c40c000040d28510002c0089081c04e0b8080e40c09 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 477800341 1250 477799091 477799103
    0x309020d020f0301021b03090a09060e0402190f09020403060e06190506030c030609060f0c07170d020f0d050a0507090b09090601031401090606080115020c010c050c300109 75
    0xca000d07181035152801c0101e4003c2c0098601100040d1284079080025440031203a072000c07913181d440d8036104030702d02c0c0540503a000c20040549821b80741c01c3e1034080900068051504006d1407400c4526010810001d0400140c1c001843d40c1e031a05203100039441488192042440c00c040d4080415000c00c5c0d150040c559603441905145101c03285400410300501031950500c10100c0c039100a80b0700340241882000c40740083c2459103081032401c3c1c0c00c00d4005065035070360364082205a00007035008007100c03945e1120500198440000180c0742c0000c1c45040c00d1140140c101158031044140d59400c42131050700148403d110517182c1480030ba038441000e0156680c221f03400c0c8140d990a0401080055010405140c01b040c021039403442c5202034042a0404204640c070f60800344001d941102c512801444c0c09100c0c4051ba0480c140c00039201d04400780198100480e081e010010b00204100c458031000e001820401019406084144280b4500c1c800c00304074420620702c075106042c1071182c181401c1d0002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 477801591 1250 477800341 477800359
    0x50918060a0c110109080c060a021e0a09030b1311040b01020c0409081e04141801290309030a030e1b10050d060e0a15060f0c02040207050105130c06030902 68
    0x30650700c0141088010b040108411052042400242409411002c50044103559603070000340403200d08060009102150960040160003400740100003200c01c8400c1c000030030342e02d030842d071842210908290740c800f4088003c2c04041c00000240e41e001401054811102902203082560501050300c501c12405d80c00f6800c112445810b605194105026480c4103c141d94501a480348440841d01080303a00300500b100302060078451201c00c10720308004100211001141002030740449030b2a2030050050351a40041c01200900380460310551620000d03002c8c40c2d0b036407680751911034a5502d800202040d400642004021040000301080c00e25219108074113688040d904501803100c45251400b100040007010841681c0b0b00c070551150704080e02c245010302e446420048407900a6864402c0004844040110100802e9070004d10800d007460407400d10b03070702aaa590000900a0144e004003420030350800c810482180d0000c201c441c01a403080000c1488240c0321102181240c00e503903c000d40000e002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 477802841 1250 477801591 477801601
    0x90d021c0e0a03030c030809070b03160219030210060509090601060e0a090903030603110609030a0201030b04110d06081c320a0f1b020d0206090a030203120405091806 73
    0x11020944a146035814000c00e929801c20101d410a1410b620540002d0308011100e010140c0c800c040c90b41040821000300303819810802c2034100341c0b0002d040510211003200340c00154500910500e201884e080f400034005105504000c0e449450807102030385660702d030407c00b00e014034005140034040c1801c1d0008100b980e08003001a6445180075405030b40c008038183d40042c001c4014018004030621a07a000701d5464914034000b4490040f040030503225140c1070001088a4400155012200c0e80919020505040d1305001c00c0007132500e45100340322440d00041c0c46080781ca90750413610454a5141c1107131a0b049050b6038029414038017440f000300003030403c1101000040003c01d4841d018050300024240500d0201082d010342e4880040c0c10080b0344840c2c014640c00b50001d00c0c615030b9800a100b04541c10b8495400101c0310521100000d20500b804030b01c1c0f082c182c031003010b030703c1c0a103034064200c0d038000d68040c0c40744e000e9400c10f1241920441c15440003030041c454008207104c101210798028040c42d160317 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 477804091 1250 477802841 477802873
    0x9021804020705010605091003150501080d0e0f1e0a05011419050f03011403010c09050607030810050307061d011b03080a0906050a0207020411040b091302041a0c0105090d02 76
    0x20490b81034480e50b407540004140c542d04d4001e254028440310313010200041ca0361800050340e01040362a45249440c3c0300c010400500c0c04138030400b24034141c1c540071804160440008507100718866150f034001464540a1101503480000c2c80c10004040340d15100165030386004585140f0030000404c201d820500c46040301c0c0c0820145e01c203250300f0f1401c04608104503210003802c0e5820903400304c80040004071008826080c00e115918080500c1e10349918801d0400700030031464805c0f803400804201c4031a0008070304400b120301d501d0107001c1c0141550441d641d18000140200005103040c00507901103d084003c960082c0b9011702ca00b83d960401c9484500f00f0740301500e0703001c402440e116515494080d8540002e400344945032103034001a20040e11402540140000c07203000c2c101100f07a0300c404001c2408003189034011f540003660100d811280c000b10000300d9102034011f0394440100041401d45840301800c000c40500420030045000304520b0303468146035580c3d090310300403142c0580c02c03204401e190148 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 477805341 1250 477804091 477804097
    0x3020a121e0804031232030c091215010602100e070e04020d051c020d050c030d090f0c09050103030e0d022d03060c130f0b0d02070201030e03030f0f010902180402 71
    0x102440c00c00e03060580e682c4844003045040042d0354002440d000d0181c507010740646100207006c8584008492180380a006400703103110140910300e9800011689016955452208503440e061090035a80d02e02c0214409890f51242806218013500a03040450210304007403003024020380c00c02000741416864902440c50110000d4400d0740c02c81c0c4407407960000300350200114460040000011203042c000c50b08000c1c10400e81e495440e00304041009040301c114400001e0398205141c0f200000396034292450000212800c0480041040d901001e001410345601e0f03000e103040301d001e03450350000c0c10f040e00300300030b001c40e41144000d501c00040000c0c90101c0514494000281480c1041803054142050010385030075011220920b03444000034180c48050810380c00c11004000c1c402d02c25100c4d909044451099000d640d000540c010307404118601507a200e508150440d0140c41c007036a5490074981d00c0702140c80b000b1560104400515000060044001d2003203510700141c10511170b0101081c8c100f004080c0d4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 477806591 1250 477805341 477805343
    0x8070204050604020909090a0b01140102210c0f01060810021612140d06080d0804030c17040e07021b01020309011b0804030c0b03090f150103020111070b03070903020a121e 75
    0x80d60070f0102080c0758482c01c1e1b00354003500154004104122052030620841501600700801c1041c640503400b01590300068a6802110360b00725111030381c5102070364014140900140b84209103d01c0c030040302541c00641c0050151290081503078507070321540261341c040c1d2140d0502d20f0707041125200365602003101301030241524051840d0200e40040c0180e04003489420000810545d19900c0100b0048090b04000d90047d611a42c144000c452605482c040c080044441e8043d14401c076111039403000c4110b140844020b00101d01400c44203007026a4002e540b43c80c4da4010034660f00381003401381d40c80d600010560b401d10034141d42d0701c404510024400703856451030080440e4210300c10310021000402001e2058007030241c42c1c40c46a04d91901440052030040c11447c800703025081100020030304410aa9498107594080c20304403030303541c4244146031810302c8542c000343c1501c002000384901142d0101c0400300310780c000c4642081040d16100c088a00200382c05004080e50910b01800072442001450380b460f031 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 477807841 1250 477806591 477806599
    0xb03010b0301021309150509130303020c031b0d02011104050f0a05060a081f03020d02010806010e150c1e19020613032402030613051f09050a0c0c080702040506 70
    0x2180c9010042803da8001904504200c9100360342800701d43c14502c82d83c5100c150203046410091314100102d144200050440f0480030001c0c108603003414001d4040300c5a29060508696890302038031002100f00311000611020750240300c4c003402e05103105008141171503408a5441d4641071400003081714003418204825088851050001240c3e590800034194800305500c40541500d0b250350492034468070015801403010180e14280090b888246180c0c0d02c060342030030030321199262040185d40102e8421106a4014801d01c50403814804500103081a808101c085902072445000d03003c2c1805100c90362520309500c80c034680081e1890b80500490420700150004e89814803005000100c00b81c5078000395a81300301c0d40c0da4082111120980003000b614141e10031811800d120f800601200e03225502d00800d56180c10109843c100004e807041e050303c042c01c410350006136942152401a040494502180303528101d000702d0b110b80074a25a9042a50000c0c00d07074504481603003000010007000e4406500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 477809091 1250 477807841 477807851
    0x140a0e0601151704060506010206060d0b0c0a09180e011107020102060c09180a0e0d1713060e1009150501050a0312050f0313021f140f22150c150b0301 66
    0x103d290100303160f40c0514050341d004581850800c0002e884c05c000900240e02446100f00480c0125900000458020900f400707240d03034031240958100e0711a81150032144480615030021903c1030750641c0510341c20002d00000b0b110b90303100110b0103039084c0207d14010780560071480000d4013110070710300103103900301c4010034843c5e000c004072100901c4540125180c0d000e05070f60301d41d4114240c1d0108070b1280100b0b080d01e01011060b5505090740000d0702d02030008512403801403500c500704050764000c47c41d04000d9504039a4000854042c0340003509018a082d60001d080031891818441e942c05103905032403000d0640701d0700300e145940d000201141a1207a504025042c07000c6134210401780c0c021400750405030b43e8003039030764500c1c010498118a0245405640720b100200c5164240e0003201c41e0442900e1a03416981b40c102004201445119800c03242020301d02d46680c03425104420000c075030030b8420640e03101ca940c2090403429202d01c010340d2000740000c4004441c2c001d840c9402c1d0405440a00d0107000803030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 477810341 1250 477809091 477809117
    0xf0705011107140c030105010f05010804020307050907030209190501020d05071b0e061206010509061903022e1b2009070302030a0e030403120507170c01140a0e060115 73
    0x101d80149108035070401c5050a100c0f50321008000a00c01c043c0c0443c020840c65140105410101d4464404d13203050110440010b000d40d50144079441c0281000742c0714180c249041c1000800035442801100c0c403801d108805000a088a00201c105450040c1c0040120200f40300c4252030300e0700b013200d00301c4110002000740c01030100c40300301c5000208480200100b103414428100310400000364009107940e805071004001c03a503160401903801590589045400c10720000840e50074204e50740019410180d0340d070382000301364a0f01408403211b0006c04003038000035a0304d0504580b0070603454900203200703400c03c25020106103441c0d096542c1c1d8010000078242d8000f00c03400301c1c44c10a81143d0910120f0350103c20801c21850728082c03000c0d0780411001071860039041d5900e80c03100251443d800410004080390101c200181e414110002100300520b0503210f452001c10580604011440d82003600040b0010800030780050142000c00ca0941010b86000da0800c0d1700e08c03981c96120b648403403c02820000c004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 477811591 1250 477810341 477810371
    0x1080421050703080f040b0601120e01140406060501080405060a0b0a05101707020703030203040e150316080c060412060509010227100806090a0f0b1011010506090c0f070501 76
    0x1904011107615066168541c41c100504424401010805840c0c0500c08000001d074400c803900350700006c02d0810450b1034155505900003041031404407425503192000020b400310401700351314803c1d0f2061030140000303034803003004541c1710109480040180c1e1000c400306901d101944c00030080c08002803d42e003045562000020f0020280e58504c0c2c004c070341c40408030382000100c0006103910203440d00080203a1491594029540c0c8268411a25101034110224500400800301140c035640b008080b1800c181200704203d070f481c12030b481500c0c2a48141c110450150800c58240c2c0d08852491105034901010340e1039400190000800711507295508102046d00c045601011810070008806089890034500c418858011704000a031018485103000300103031980c2d0800c145074400300c5d080c0d0200c0c0440881d00c2c1d11000d0407020b810303698050400c0903150101d540c07041904041c001c0d1340009200c592140c03024070203260415a840002380004110641042100c00000d091072841440005109540c0018003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 477812841 1250 477811591 477811643
    0x9061b0c0b0f060409150b130e1e030c0a2109062a0204241a030612070503060408120a05040804050607050c3102030f13110d030201020406030c020f0309010804 70
    0x4420290394800c6d1040f01f034145120018501e0000140410602122003105682c9504c410a600b2480300030720030181e841002441a68916104a0100c5101e00d102d89040e2544074001e04448120b280d20b45100310f00c0794825807140e000c403102519510030710f002c1c098410a480d124418803c4201460260344030068940c0d109a0182c44a400d84000d10024002032151400c052984038003074864260031140d088650200c00c0701c2d0404000c4070301d043c40305e4408038050f04000c400e5100381e605004601c100320a01c240c40008119900740c0d0301c084503d0340d460300c80c0201200c205490203461280180414421800c150004269150103042103580380d4070300500065501541d07081c11000c1040001199203004041941074500e854600000c0d400c41c80c0070108000b5101004000115a46c4549030403014060124024051014080c0ca5803aa160960070040d020303502c140304003000685400c41d4a03504510114080120048007000f0b1443c10580c0001103942610191050316119510214111200f54854076 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 477814091 1250 477812841 477812873
    0xf031e0305060406090509030301060309140102040e04020a060810090e01020d0e0714030d1209151404020109120b041101110a0c05030709020f1b1009061b0c0b0f060409 74
    0x2041e1442c252042c00103a40c019401034180c00c6c141014000200b401005890550340700c0d00c0c00003107600050610180c042580c00e041091548000b6003c925070140c1c0110700d00c070340d0083e180c1418817076413901300700c82003078049800b120541d009034020701c01c40c4166000140c458100754005405d21603174007207a800300c81c000c441001180d44106000c0101c60500400c00c0c0812000307c02410410041c43d82c0074007407125040c00780350181c0d540c0d040001003000c0d003c440d511310800c0507401c220844001c40c07a52011042550142c0c00709403c000c0000702d01415054640c407039580034180003c0360f2525500d8611002d00c040310a41031110b4036991540840080089000080c041d0050752007042c40c010905003080c200e0b802c8100708500401200b82030395070b004204d4800410f294189070940c290410500d04200c200c401d003400d0310f0704100c805014492190041c0344500405e00100000000c0610301b40c030104c0c00202e00501002890b00000d501c6601c620710b207a40310030040c3c00401c4800450f580c4144038114050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477815341 1250 477814091 477814097
    0x605060f190504051509040f0c0f050d11120a0e0105010b0f0c1216061505010e060c250e0a050709030b090f0a0818010c02030c1e060d24120f031e 64
    0xa00001780c2c0c9007070b0040034030041c01d40c4010440270281d1070307006100041d031400c5141804070005d901400c5c80f0842e03203c024100034040a49864000c2d10900da000c815041e54180009418079481040802040c4950340c100d0f0740321414540790082c7d03500103020b035400c48169079a00340504030300c016001ca503500040600242200300f0010001c03152411004842c0c5912101e041002c2e2030005110700d0741c100d424040954002c94004c3c0c0c958003080d0440d8079015000031007802000e100110342c8040307041c168080054a1160514592583c1c550110380c044074030071151507000540c401b0342000490520005076030840204815524600112107003030b8981105414112907500300043c6107032100040041c040d18441c000d20340010448525000a55200020301d04c680c40b1750381611019590114010740825071840142a0945454040042e00000c0907103a500c408140500310709585a10780c00c0b520f00d41903451010b2b28920040c000d4889444002c1041c1d0700701c061081c0089001651300052030399030201142d0396 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 477816591 1250 477815341 477815347
    0x1030b061c0203041b051003110d1a010e1c11060d02070302240714160f05160b03010b19050904050f0106110a0b0c13030b0405100605060f1905040515 66
    0x4170745420040c0e5000c020004032030311014103002036524808030040d14a490700c0c02003000e40e10041d002240784901e2a030342180d10300d883d10760900ca803000c01c03003815146001d0321180582d18101c1c040c403900706404611102c49123441d0400000060740c5050704001038102a01c2075003000c000c85203c20480e4000700054000d6880000c00d003981c14491078003005d6601040003051a141011440980030717403c50301c4105000b40b030100385401d40b240b40d0544d01d00d02681000413800700c2a500e0a0040d2200030b12070f00840041007244000c141400c0f810b04581c12502011106403801000f10905620001100692001c100081000c08620740d42d9018050003090540c0c2c2c00040d40d45070000c045e000cfc072800840702100d034010350200d502082401c9402540314444444060f6180f100a582c06101d802c030b900024068284030003804248030002030581d0030000c00300e0040181ca6240c00411100b801405d0362010107a00c10070041441e400d00f000448001111410a60b0515880b84002181580500d124491441c1c2c04 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 477817841 1250 477816591 477816593
    0x91403070f0b07030b032d07031a090a02030a0b090106090f0b03010b120307031805041410050a150509040b03030c010209032404120507060f050405010f06060e01030b061c020304 78
    0x311180c01c060b0f1420704001c0000c8200c040ba40b903d4019016011f2040d002451444001c1d00040c0b0450031100c8105440485450340307400c0d444000350b001c41c148000f1250340014156240007031541c284030703002001401807900b00e917200b03034501c1c070014217040351035403203c000140c60201c0d0f0154174288080c4c4000403c3c8090780100b45800c44900542c0d452203005840f060344000790010088078a225014500740c5045201d25040c415071240d40d41c41660890300d4440344903050240542d040c6d00460490f440b002d0965951400c0000c0c041c400d0180d0710100e21070490441c11035008030020009000085e00c04a0780312403100c006401c3d60807128211341c0390b940005685e10289814401c11660080f08800e01c0c541314040c02161118404c020002000105000b0851991074003c500399041d10360300100030b11007060800c500f1806840142d03001c07655903003428410380008440d4000e03102038030036a40d550022081d0341c3c0d00450280444a04031500000d0801103859040d0b0549100c003990b809600d00540e50707040c1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 477819091 1250 477817841 477817853
    0x708130f0b0a0e240f09191a07030f110109050a0c08010b06030c190507080c01061401020607080a020901030f020c012a020a06150503060426040b0d091403070f 70
    0x200e949890312032100601d002d06075030f0304008039141c03103404803010769140c000c41c0f01405c40c24403a95110a501c0703000440082d51000c902d15100080c1c0f00f10083c122801c0d4402000744900740100007000703002c07490502c442200584995441052031003218008604a861911002c0c00d080f04400d0580d140c04030401e060003004400d00525100c0581561034070b15525002049200703900030090500800350788051102426849542690b0001d6003100c0199a10302c21800040c1c0241218401e5140c4002c18000c80c3c9070b550b00214880d807143c0724580f01d802242c1c2c2d0382121003009511100030641859552080b43c1440082e5201070716006030baa00000880300d0220300a450324410080300c0c2800ca000c0f445a10740b0007a80810182c40c0e5980c0a0000304001c81a28001501031280f81c10040d00751045104200500c600c0141d811668004590b00c19000c0c1246030444070140304030300480d5440d200400841408601030381c4450310a600514140500460040c611741c1103a102100640d81c3d608401c2c907120038062 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 477820341 1250 477819091 477819107
    0x31101030f2a2c0d02010905130204050906040207020d0303270515010504111206060f0703020a1a10030807170c06040c050405010f050f0a0b031807090506060708130f0b0a 75
    0xa1000030340724043c0740c0041508900f214900c030460180012010300d804590241c1c12550150038014401800e030fa8440030b4080080d08036114403441001c40e01c0229245040500c01c072100550003400d00341c1507116680341503025103180011003d007041c00000034100180120b410004c00c3e80304d90301503d050307a02034101400444041c1c010901c114948414005501444012160002a42c00307600010b5650200014081d02540c04680820580050000100355020a030452254440c0c0070f02e8030200c11184c0340c5010f0400848101809040310001800811060006892224400d56914601e8070300c3c1003070614a40c10442c0c0e9030b101544814184010080703000819005404140c13020070a0f0762411821401d07560b6644a960f004151050401c01d29032a581c4d83c442c05421100215940d905104806441c400f800708a1140c55004a00c00881d44803c41d00500340140d00051000e401c210941d294250254048040d000c40704014030400904109014280d400812100742071381c1c0c0b2496071501c0a04280c2c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 477821591 1250 477820341 477820367
    0x20901090b03090a1e051902030610051c0f020d0303150801020a080610050c0106030c1d1506030705120702030a0305010e0907140d0b1302030115031101030f2a 70
    0x1003402003002030a40002c075004c0303841e04405820603c8001600b00743c290200c201000d4098002d54061824500c0c140d00b0b010340b80761003038007142d0443d0f50306868100340400341d0042c6caa011a00c09141c040185910303586d4414a0302034054a036040806500142024210800403004039480307a120204106007808a000180f25000080d4981412160700504446000300305602c60380b441d48000341c440740300d030381a20f0211002c54020405180c8a00f020044c105d07103441468800211188140801c2814110710f90181003200903086903000e00000b00300494000a000c0400c0050601c074003e45550000006406122190091030765044038240c01002e40350143c0054540c0d4003c5414021500f000040389022500080c20054440b0350140008606410384440a4040b807004014806100310214038900c005208400802c421840c440c681240c0c080184800340a28003015401c01d0254005d820083c5110b408990004440c044095a0080d1034040c1780c0500c0c000a004201e004040e0f00b20108004070 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 477822841 1250 477821591 477821609
    0x12051b0127030215250201050f09030405060d091109041202010b0f0f12030f0a050315100f0c060914160f050d0f0804150c03080c0f0304320102090109 66
    0x10752555140a0360b501e040000601440088800240004104610309940320100c0300421550100c0e07010000e000e02800c0d6102030325085290081482c0c090000100c0c0d0071100050091428080d182c05044010024180705840030b484444042140d0b0b40e400d00036030b00ca00d208040000720f061800800070b00b1580503007000c6001d5458640d0044a60365070840308902c0a2084440d001601d001607002030550188401c0c610035484049480c0c0744461708078014610400d042003070315581d08001c204005035034480000b02c1c00411501021030000c81e03c5200c050f002c1307601603180854a003441c2e41d40c01c0c44043d46c4900a06864100c0a0f280b071480784c10806600040485148201181d407d0400180d0781c0f03400380f80c0003407640c08030581d03a40030070810b0010788004254560402c050044240c2c0e010380768041101e4100c00040d021030020300504110000d441c82200344000e16411a9a44d075a0130682650501c09000c2d2122000c0940074244852a500c00c085003e4000150b1211100710000d8111400d94121900b1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 477824091 1250 477822841 477822911
    0x290325080f011421010e1e0f070b09011b0b0106080a0e0f0c040f06030b01060215010807080a03030e01020d0606270e06240301030309210f12051b01 65
    0x580e5030010084a00c0030340c1c001318503074200140541d8018840c0d050082030900401c409201485000350b10709101c030388204143c4010a0324108843e449054501480031004801e019003602944580c1d4001c81d195100314444281004a40319284204c43c240d00c548001a140c0040000c0c84605000d2039140e02581030041900d040c040500b2078884400b04401401180d60f086603c9030511140c00a0000b16008640218156110381009480b07110151195001c40c0709035000141d8040005905000c036007004024000ba0442039504a010b0403200e14030055540d000d2281c002a80850b100b03613001041561a403050070650b2030298000741240040c0d40e00b20010705802005840902c00c201a8022003c80d120f140000301c000c0358000300d200e492584860804040008001c264010060070b0a9512111034440c4026503045103208031500c40c1c00c02010802c103e580d40c40014450214407420140500b80182440c44030540100e02292051084400d03a4498180826400c2d032151400c1071202d41d0080009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 477825341 1250 477824091 477824129
    0x5011e11090a151704060f0b180c09122d010e15061801141e3102070c18020a090b130911030a06290325080f01 49
    0x1c0108030b5032094100c0400c1c1441d0082072180b0624440b80940380c81e100001060926003003a800400460729000c10003480c02502c0501c525007007075082d5800c528200d680c0c03201d95079810f40c0512a0488034885411401407076054603010024030940039006019008041150343e1455488030426007084001c0003a45401c6480b03010307440125400c2c0200036100d4620740280c40d07400100390413551144402100000c0f0394004103510b50b003007041c035424002c100c4d1a40a98003500e2840340700102100811944100d9032a0079240740030001041d80b07680e07052481d50f0302042e98004080e40a0344d0011070125076007403440b80c00b40480c61104001d2a1b0031313205c1010171070a01d0054803020304a0301960083c1c440000b004a111480c008100c1018800360070100010310500b5485450010391f500300b95140714242d82056400306610080301c0307402c201c03420b010604004034244c488100c045581301400107451025042d024182d0000160524900c040c100d81e1182c0d10342c6480066034020343c00603008040c20600380d1003090703 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 477826591 1250 477825341 477825349
    0x10504060906050c100203010e010f0e01060f080a060305060108032205280801020a0c060b01080c190c050d1119050c1507020d080406030e0604050703110a0305011e1109 74
    0x20b40d5010f041855070f031107000c502c0901c1c00d100c4c4081c1584144c000000441d5078456414040d04031000b01c400d80315829200d107000381952509004240c0010070000180045a10990741180c000100b000700060158881c0c03541d5080c07080903001910650700002d41070300820744008031700c0c00d118500d40c07003200320f9402c1c01c000414802c010034000009400d215004501c62400d0610311005206100003150740e001e502030301411030b20303410109071402480e08100301820350185d00601d225030641349845103484014403003104182000000401005460129100022020010715000c1180c641702c1045502c5c003c62070524095241c2c52030005078a074041500001040007170b13407494203101164107042e0040c0d1044c0c8801d2a00034118080d40c840e0b001c04c160310070b120f02030008105a4010395024083c8581c2010344995a40c2d00f1741d4014240d900c480c808001080303202401e00c98030031005210f54a9140c1c0d03900c171282540e0b0500003135036070302c0034481141c1e0052126128140c0d044401d603100c1c80c2401ca410b8001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 477827841 1250 477826591 477826607
    0x6020910092d050d081308010f0b03160603110c070801021918091e0c0c02130c0806040b0307030b0a0e011d250f06210e030421020901081b01050406 65
    0x12a01501e194900941040424000c1e20026034006d01c80050342c60392140c01d14040e160900c1804109031230003400260354100445c0500305c9000d411200c519032031030b203c8202c0040481d01e8940200c150b0074041005a8101484214000d0030f0200001d6103801014803208010917a80d8100700602001c0c07024803c4240c84021910b007120014840080c070b458824407003004482d80c00d00c0a07500a8070300420401d40a820141c20f610f514002c0d102481c40c8240011844100c40341080d00601141074200060418a002d41042c02e00e10000b400792140140c0e03e60f121500704005640c8170381400c1c1c072241001c410000910414200b0410500c202d16400e0000c08256101c40420005500041c00b0181448017501064140d50040c817080240c00003862b1744440040012070550051243d0031030402c20106501f116000709094103071620069860145098010107540d0b803643d00402401811088090140e5680d82584c2e0090800703c0c050481500060f10044901c41071040c0c040c148642440203000096201d041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 477829091 1250 477827841 477827849
    0xe2d0a0f0b1c110a081803041a0403020621090c06030406020307020a081b060a020c0304061b021806010f0206070f031d0a031e111906020910092d 64
    0x240d5440032405441c4a54800380c041c0610314508042074804074280c00b0f0024203100d58140c1e40c00c2c3c916221003000000c902c0c2d0b148800c294551040c08103108156491411010f0b030210b205c8550b180540e0703a07010410a4000004401007400030707a030560070417046100f0850f40030b40020060450150f5030030020b40b460101a0016040c2c560200000f240c00303000300500c117100d64005403419190701180220304c0709600d41c0c0d018440a80203213008514030000c44d000b0b503030000c1ca041e07014600b421b0a180d01145c400c0321301000a40300c031300304420050260302e071000c1c0170f101440130b06050f050314584140003511050911103100300710b501082c10021507e42c03000340b00c0c11980c0030340b8000c56038811100705504201c100c2c14031000385001340020f4004050304180000c54030301d1a03400d13603180c80704d40c80c1013642c08117040c001d0303000c070360704216170030808441034800149425128500050031b10f2624030124a589600208400129030511000d11110b0307441118114411112888000340d0f16411612120104e52032103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 477830341 1250 477829091 477829109
    0x909050f060c03041403090406030b100608010f0b07032706170420030a0b0c030702060127051915090f09051c023f03091c0e2d0a0f 58
    0x80d1003101c07a0103000707e400204000f081401420748078144100e000318103480d151784e83d007801d01c0001281400303040401d049030070708604001c50501d0445012031551050804401f08078005102d000019151006400808400c081c000107450a008003d040810290100c02d80d06a80b00200030001340c03001d00402e81d03501c00001203400d13400d00502181c0f40010594004000303003101c004020000250402842c4208010b0303085440301e90342c039141e28050900c00e00c04110000c0d943d05080c0c0301c1100d00c0d040140c01c00600c418501c5020002d0f104101240c604074a150f4600745403000c1048020940c0c010001403844105007040898819a2195507851420408051510440b00ca0100e0b640c028449440d80241500440d044080072211107410203400480101d1b210f0b0300d1000c960003410b1081c3c00d1701c0c4644050310042260f00b0a81e582c4c103d150420440c030b517041281e1042d12202c940c03a43d0b40c42c5c11001d0740364501c6803490108801002c507403e4030840124014115014100107020b0410605070440c0c0480d4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 477831591 1250 477830341 477830363
    0x712060c0504051018050303070b1b07050a030e0d0c080114091c08060402040308040305060907060215130507180617010b0f0112020405040218031606080106140408070909050f060c0304 81
    0x5111514200915400580c7c140404102d030001d101c0c0c1c9002c401d100b03260400c9800c0c4000c45211954109010b4464040c0c1a40d00c9114001c00103801100003403c00e240090400c0d400200c260344185014040340c0040125075112000254010001c40d43e107604060b808018210b144030441502d400b0811031072007034080000c04004200d16448540c11107014681002410769116101d00f0a581d64000660341000c00b441007003000104a07101141e6215030300450103141d143d0b612585040300340d10304642815960390003013004c00a20028002803100c041d0102000206031b5610f0042211850300c04000c21700703c00d0f414102e40d514981d8442c82c0c0300f51004000d080013154161070700d02440c000d001e55044140c220f07200080c0d1880c4081102400c0346444800c80442e0307401c040d605020b208800c2548564000b003181034006004050040070300c20f803c50640d0085900f0155210032881c900729190740911040c550340ca4000e800d00000f80800e40100300104014040c1c0d041c1410f6082d01031100401c00303003500b08a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 477832841 1250 477831591 477831617
    0x60703200d1806020a1205060a12050c131a030c060d0507201506011706010e030a06023c0a0311040b03100e090a021c06020c0712060c05040510 63
    0xe03440361524a5042c841d5411400c903501e444002940320180400118417050402e0040f80018064148070701d0004c3d10381c41a4a24000d01030301448285281100d05004405540c00e4640301d0800c0840500300035880400d8119520955001c02000c543c4000d02941044006000940300c0c18101e60041c598014001101e6551202c00c5a074000e4074800070400d1001942c1c41101c8100c0092002655000c8007204502c58540c00010340d01c405001e4007190300030b07909a0000750705e9801050101140c0b080034064407082c520550360708e02268800007201c00000c044010401ca1440b1040d0a008040204100340092001c4026481803c0c05492030000c1010740f60400395400c140142c0648008102c00c0140d55224280301281c80d8108859000724041030b4032240004108250000b000262160013414681c5440001d40d100d1a5440d41441c041d20f09940800143c0c101181c2003100c81c005104500039005003049a19104003074034111030701c550400c00103000900c0700745c0d2002101c1c0e00b69001410001202941 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 477834091 1250 477832841 477832867
    0xe03070813031506030b06040b2101110708031e0f010306090201020a080a020c040f06050f060d0b210d080103031e120510030201110106030c0b0714070605090306070320 74
    0x9a03800c01001104583c4050b0040b101d250440b5061341d01c2108030b58015500d5034180b10460307890a0490741e10103501111003e02107040b0050410f132113050000072a03031075802c0d4440b034000d600507a400c5a0401c0300004004004290800040345100186403c0203541040000d143c02020103000140441e0f0765100707101d045a008018840c4900c0d8481e203180d840d0308140038003944805030b440c041409a411319500b00c641d450340d88683d01c250765005025001103620b0a05101061b04035800820a59036102c0849001d551078400f503400103002c3c0031364214460b500300d6525003403c2c4080200301c184034602c0010710010750040600a0725282642d5800003005001800311418441c650044405078a00403d0015448100b0000c0081c1c3c0e000fa00d8001500344104001c0d0308995841c40086d250012121b428401c40030f80400034203001c2d0049180c400e810041d0025541483c41e29031091010400014000c441418244203042c1c0c04045802d080280100c5801488030101910f1104041010009004194158 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 477835341 1250 477834091 477834127
    0x10312170a1b021c30050108121801050702040f0c182414040906090c03110c0d0e03150c040603240315020706050403080402040f0e030708 61
    0x460400311480e14241200750354018240d04521150480401a601e00a280002001c201c10b11488501100c000c00440d030881d0300c44400060000c007150f40002c49208068100083e404032000000002015450f01c010f0303901d80894150b66144111060004403040c8180b00550f0f001d145083c01d003555194030360700c005002041045845034100345001000c1c1d510a0740031034508607090700e018130501d02646803400040e014a044030f01c01030016080702c0500600e8464816802c1840940b0310b0f4508181e02c46e5074000940d03060f50001c0b200982e9491900310310541c507018050b0259600c5c00c41c14a4803ca200e01c16454155014039202444881000c0c903411b1b480400c5101c26464000031b5545034ad04200c4400c0107282d03c1803040740006414000c030440f00e21010180c5d20901c1c949568560502031071990f031480210000c85000c0300c1a03a081c02504041046801503621a6100b903031900c01030b1420f44100302c202d5003040c0e00c0ca2800f610308154000d88803c00021161251b8000206684a20070b200c01e0b4000a0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 477836591 1250 477835341 477835367
    0x90f02040b12040605010801020705211e03070306050409121805040c030203040b0609010509042405160306082d01021303031d0324040c05030303100306050618010312 73
    0x40004404a08042010803a4083c92040c030061240340d03a545100c6090f805032110140c4030750000c0d49641c000910303881840c92261000d110040c00c00003952050b201441c034810b481580c5100010400201650502c1100054082100d00b04194221512410700d80d40b402c03040300040c0f11018004908000c2c0380502c200050000820900c200c40e09140010060340040e5011600b01d100381e808100c440c5054040c07281600c0c2d0103003a074003555a032912a141c0c41d0300141030400c1703104281c19540b1300e11001406181d200c1c65400c500795142c40d40340c5400400700d40c1e60741e001036801c0d00500850504041050b000d807900c0c11206010359066031988140c0c034028424104800d08100c5e40000000800d41c015410b81e14204c4010246466850310209058a030300810340c140c008642a0002078207031460580e1351a410501900002c040c0c641c07150003280c42c0d54000d44581034001c14100b070810800c0f44030f0080540c000b0040c0e80600b00500c42201c5c0d10b00e9a08113000c024220100480c100c80309170b00c1041c1002c0c0803 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 477837841 1250 477836591 477836609
    0x6050c120c0304050312041a0f0c011b0816020601090b0a0506070c030c0e04020603072001060f050307081b2b030c0c1d04020f0a08030316170c04090f0204 68
    0x1ca518480c03039540c0e640f0510645000380501c800858020902c4010f6034102c0d241412119400c001d01090886e003070340500042102d0040a00c0300c2003d80c41c007481080c03501d5011603699888840e6100000d402c4060090454841d11034143c18400025030215407103045804000c000300e01d807008000090b644d4111b0390003e03030300104003207894800c0c8014002d03c10200c03406820400c900544581c03130300242d120103c0d0040e4101c0b0080000c6100e09100c0c60062104217075880a141c0110010031501d425181f065000c00011480707110240320b1803909111560003000c1100040101c8120700400d26003150b124000c02c0d1080001003802c06101843d0314214210000c40340741d20b4120071076031401610104140106a992246000307010400140d030074441d041440c0c030b418050000b992550300b004040d001e070f403103600e4010300e1802d000501014100051405140f00010038105804250402010350890041000412000e0b0041c007080402e8a01100c00b951100703000811050450300001010307108a078003141d05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 477839091 1250 477837841 477837847
    0x607020a0b1b180a05010f081b120703051503070303020c100504150f0f09030201080a2a0503241014040f14040b151b1504050303090c0d0b0106050c12 66
    0x20f0320000c4600303101e82c8501316194425261038000444040c251010488041000d040100d90b50003614540c2e10310030000d803803015151401c10ba0950041840c00d1b54508082510f440c1400080810110120f900d19000d900504005245440080d6100d43d05402e0074051181031005c00003151080c8212006001c152601140c0d035244050010020742150068200140c4540c01c00341456215a0120301102e405940e1a01c003a1141e24079003006146951300b6220281554140c03e0a1160b1510041084042516140e44034034147e4007400c5404021030039105402c11501511450b83d45500185111024910b440700082c19107640700c01540c030580e0440e002100d00d00740e0004260800c518030165410007524180304600c1c00105003c42038104480c00400d540c401c1c00100d080801c02d45e00d08154a583c80d0484030501c000c21401804200c003942e0946068200008000c440c60040041e000008400d55644400c44c0580e25180074145040c0260010024000380303005c040da1007040641000c0300f014071a40e41d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 477840341 1250 477839091 477839107
    0xf2505010e0a0309290a090312020a1502040305060c2d070201180602030904090611040e180f0a02101e02010606030f0b0d060c05040e0c040501030e0607020a0b1b 71
    0x182d01c2c040d100003207000a181c140302182034940601a20322101d9100884643c04105000a0003560080816070701080100ca00010100d4074100c18075080b61980e4000e040c0750102410001d00c1000399801a001040c0104000c00c0010350004140b680190454860b5488400340300d0038440c203800680d08420000441001000034810320002400200d200340c803003a031410240a20091401d10301e00c00d001c09030f04180f20041c4141050303040000220f100300c1000450200750009440d907608245c0210302c05910581c104518075807400200340d190340c0c20f10700400c80000805d00051392800d41038402030043d034500504240c21401100145201c5400c00041421007900c180000c0c024031040c8250f170006810f08070412501d0b05c07203100b0300b0002c42000d0301812110046031546005825000c6840040002c02c001c0011080181001c80c0d003d0346284d80e03a16541c514180004060351500c007061074158010310103024811b03400080c115480c90303200e810106c080d5034204150a40b01c5135505410540000015020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 477841591 1250 477840341 477840343
    0x1202210c01030506010c02010e0f04020f0d061502120327100c02071a030a1a032a060901171015020105011a0703080c0904060b1813020f2505010e 64
    0x600404002c2e6010080d641d11a801180d5540d91220064042050350440300d07210b00b031503002c1610122001c0e00152500e0451309070700007282d00802d00222132075507a010074064150558a2246149054401400309858100d0500c070b0b0752101401c0400601c0070713000c40803244070208611036803119451003039640c1c1d098402100c45c05031505260940040c0100c1d140424503845540b19444110f48072600c0c1b60171503482c540f00e07100130402c25808c4c40c424002413442c020345035070401c0344214030343c000030001805c0160843c0203403014104078070b285d101d800144034899940c1d9001001d06040c1c040d10003800081d0f20740041c6010007080640004601c540c40000d81540e003501500900d04072155215507203c80592000c03594410f01400340024006281030000c42c0c40411b811010f025007400050000072410307034410040207240c1c0210038038040c0e0503480c101c4040e207103010300840d15019205003055150100c512400401440784000380e900c866121126507110300c6221201034000c9500030000c20110350000c4180d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 477842841 1250 477841591 477841603
    0x80703021b03160e06030a050f1f0b060f0a03060806070c170712050309010b0310090302010b0f032a120f21040e04033f02040e01120221 60
    0x1c1022403121400d50103600700002c40558a800388290300d03000904200c0da01645107800f4006903898460289600007041050000040c00300b000002401c05600c44500e4018a41800c500e910700c032703807410308100e100c1e0311600200d6468440f062112030782d0b545841801d500400701504000c4a911600d13080102c0b0380c5d0408004850140510140004202030500101d1071388140744000b000f0140c00402c04d402140124040d40d0401c0110740082240100000801e20700840308014201c4107807101c4c411001e050302803040244080098a000c2201844100880c0c2c2d04c08503642050402e003006403502e0a0141402849400701000405803588903c20703624480c0d540740f800a4005160280350b10304141300b15801da400c12901c0d00010340c40e044c189443c1e070190407510010003e8003403000307281c01c481c0040401070386002e042d42498400c0d49010b02c000078144002c000301210101c150f204000030f000d005465080c290465012a00060800100c0d20115169800703041a41b41c40310007208008800c91808200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 477844091 1250 477842841 477842863
    0x215010905090f0c130902060c06041209060c020a0608070201020906030408090a0f060c17040806040b0708010b16060b01030b0a090c0201140105100c030e1c23060112060908070302 79
    0xc4410400c41d8156164403001c052131a5076010400c1d5414442d808119003155203001d00003041d0a003030046071034046042000413102103813400303451484060a1500003103400c0180c1500d00d080c40c0c82480c2039002c900c605880d409450248490a400107400b140302b50126006940c0141101c0d0322030400e85005044da4104c403400358440d000005000c00c0d4440c0500c0b0602c21034160703035101403038000c0b00e0712a203a4201d01c400707003052210410400401c4440e004c102c0640528811a101501e503c1c281c1c500400d1100180c20014440c80c3c1002414580d642e0350901035038480c1c004000260340c550850040e40100151110203801c12004c110010302c0030b65541c03004031510201d8001344030f103400300c02c04402c146c0303000d0040c1e56001002d031a490b99100d110380400940c0310320a090040502c01c1c00c0b4002003404400c0c1018485500442e05c92004003e0100c1d00700007024401010200c288000504544d100d031014000c1c0e0740c103109448800740500410350460141c23103800078116580e52419080080d02d910a03413017 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 477845341 1250 477844091 477844093
    0x6060c0b0108010509070b0a020721051b030a030e030c1005120c130e100b0f0703120902061905070818100e0a050105070602040e0903090306070e0a1203021501090509 73
    0x100b140040c0079a611498904010300440c074202503c42c0d0507500801116011072103142404606d941d00d111042c03201c5010150000c0402c03250707181c1300749007000c1d15005024140d550603408a26880c0000da401040764103041c454240104040420319282c1c01c0d503034546e44803481100d10101c5541190081410482900c1414425580c00c3c8500100f0700c1500300c0c503c0140c034941c0042100c4100c102030183c03c802159090640203540e40c80600240d00054088900c00c900000d00c00101034210461040e0f0400264041c045c00f00c3c150000b8105000d64a03540c80c4c8041d0000e289440e55200d6400c40d84102e81c400c00c0c450712040050b5101a4141d10030031071174050303802e584a070b0800b00e0041c0c00441040c20001d245030b4649007004011900c0381c22402e001c44000307400340000b1401e500390643e410310512032030006585919000b4109454208090161401d000302101c1e007542d00e40354644c2c1e01c019280c0c0e61241e42a420340501c0d0482c503000300403940c01d0401110900205040398290025405880b07080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 477846591 1250 477845341 477845363
    0x10e03070605041a06030a0209070318142112040c18090c051903080d090501021801020111031003121b050607090f0e150103090c0303020709051617100906060c 70
    0x3e1035130401d160b02500c0319940b551001d404a00185031449085600001600d00815490070504006032807207000710080ba03c054114501c080c0c0345004200b02d0481040c482812500841c03c84000303040c0744100013082d20503034a040c001806002000300008020885040f0000a6040c22080d900052940c5002250040544440000c07545020f500e010800720700200303912503407869551041680e5001c52607080c420741d03d81d0301d142c020900078070240240790f4090444100314240c5d030f00028212404410105002902401030000d09014460310b001907a502081e0315102008481c0c040e40e0740c04c100c1901a604903001c2443e04104103003ca0454001d06007130725101300503919050b00c3c43c100301440c055021080c012600082064055030008008188181070000d5008526112a11b114906420550151b13000d00d50402a4645510440d54400803018010219880b08000102801001150745010340100000305210f01d410444e04002414009010081303240e0302c08002c0d00305542c440e42954924480 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 477847841 1250 477846591 477846623
    0xf07060b03061008150402040e12031803070510020d15030503090a2427171605011d130609060612051b0f070b010f14010207030809040b03010e0307060504 68
    0x1480380b403402d454104c40074009002e170b5074090b41c07200301006006a0f41700b0340b00e500310004140d0a100515907500c0c0821410b60301c0c540511640f131502c84240e04116998030410044001c6a03000c41c8544002007884000340c2d640709202505c4000d0543d201e8005c0d0080144d4000108000002005164200007a114092000e0f52801411030024061a0b0b00c80314002d81c000b4107282c5449282c84142d01c0304050b103100159214035440300c00211154000e408510540810158103400030480b41180e642500c01d440012030408000070302e01120301a40c50580c3d0300c060b1000c1001d42c0d8100002c411032080d10700421280d6558000040174101d2403050714049081c0e1034500d01740f420303a0b02407544203680a1082041098a0151004140e030050300000441101881200005005070494900806105011079101c074186410401c0e40d081d0803a5203415580110010000035690000f541c050302001c840c001280c1c0c14207408a405402d520102a4031030100080030340401c4003650115010702c0c000c20340c00c5802441 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 477849091 1250 477847841 477847861
    0x3030f04180507080a090201090b0d0608150c0a210908030714040510050c030f070b061c03020c090901061701050708010f0f031101110a0b011e0b1804020f07060b0306 73
    0x2c00c0d01d8860019000000003201104d650304481c44191061504084060b95040c04c0503075504580c50601e080394484400300b00c400800c015171800710014140d43c4a1604103020b0900b030522400807001d041c401c52150440c1594228045003072894200d000c240444840d074034045440c0d5000700c0d0b074100480c02000755a44481201c40644041e22005040c845104d0311840c000d80325500842d450140611041050352850309041002e440081c1c03042003403c0f031a0410030301304a101c40000c102c00d200c0e04258480380f800f00f5800900c030301e40d55209449014041e00c414000c0303405050903803c0342c598401901c0002582d054154083c40c800c03c0940d651011356600c502158048040b144035105c400da4241d80b05001142440c0b00904a401050400d8000c1c2c0c92500200c40c00e050920000b0f541140b0308000412840268000360820042504d0000d0001400d14021411a00940c121812030070100e049151640c0c80320303070458065098403400c04c1e8443c90740c1d00e07024005c0e00072080403501a0084501190200e0700c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 477850341 1250 477849091 477849101
    0x218010603291509060d050103030e010e090a1e2a0306060909020f19121d0703150923010c08101e05040507030f05150d0f030e03030f0418 61
    0x4444228284624001080050b02c1c1c1c001191844500c00c100005844d07541c4600051288840c1004007140a614506001d428022100540d5044c0003091400a11958074616880d43c0403401e11030010b0840105120076005041c640c03c0f4100491900700c84140740d00c03102c5102e40e400101c2c01000601440c400c44114195030b00743c4030b03034008103000c414188450300e400c0d00278100c00465000d40f507050289220340c441c09000d842c0c81f0300b00803d80280704203c0d16415402241e05007406150b0048444c241c3d507110a54941d00f82c40003500310500c0b1000d0b20110781e1241c1200c40856008a007824200202c503c40d906000414102c000300c0d0b41ca8246070545050050541d24801c0c0b031002d419050241c80d0030030502d00d45a1991040e0301001c2c4205010501e030381c4a02c00d5a001d00300076640080c4c82c40c0300c11180d1003200c1d0041e00903519183c8050141c00700d507551080120039150700408074020390005140c1640c40210f03c10308150305004c0801c2080b50140490f020307104540514007550031006854184500701d0b5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 477851591 1250 477850341 477850391
    0x302030a03052b02031e0c09101809051008010e03030c0906120a0209151312030909051f2102040b0f0d0c090b090118180218010603 58
    0x6046480d80801090003040500303542c58448071044110600b0014401e125500c00c0d240b661180d0b4048180403d0090360180d04190900200802d50681820b100c03003504c5004089007070740b0805181c0d401141d8144503a41d50720001d815403403034140c070039107030341003030b0090202204c3e074140d81040e01b200000c1d090014064040181901000f9507d1130b15060400512a48101061030700400100f140d050026804031003584a40498080141c1303501104040020400d0b1440c0c0c6880604010b0200d82104d41e190500c450480e0716602c002034403420103107002d60300d0300e00707a6109843d140d203420302704000c030800300704090401851030a00d95110350300c1d002c0b81c0d2020f91100301000060000104000b0050900e80e003c0780c1008002440c0e00c28615030100002e44040d00d200c001c9803105005502000240f0f4640078041e00f00e4801c82d815480b9604100d06843c900c4c0e100706c500c1a0482d268520804c100704030901080303076141c001d014001d4015140303035000500c550038424580003d260031504010f0502c9106401840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 477852841 1250 477851591 477851593
    0x3210203120f07050f0c010b0a080307032a05030403150f06060e09190e0c030d0512040b04060f050408120703061202061b0a05160909030915030902130b0910030203 72
    0x16403160400701200e203800810f00400d0060030030006002d6883c400c081c100300402000041002d81a0307006020919001c3d610481c0b5550040c40341d000040c0c0c00c01030512205200300c60600207403801c8503c10a50360288040580b8078000000c02206000084494040188003a03000740a075581200c0325400320b40d441e11441d40000c103c046c3e40406850220802ca0b0480c109280c1108485102076a0700b040b9a03102c4801001588070200462807402c09010b5011110101d0400c1410038440b40000c580c2d440009000a00b8020890f00060402c1107030380c8200801501070004100d1860181340c004159444040050ba03203122850000706860f11130300030b890580e0002c0300781c01400c2d82d1035400e00056400494902d400441d100301e100c07040c031404100028586010361b00134440500030b20301d01103501082d40c03c2094100d04103075207240840d801c614000d08507000308580302c1040440b00d07030440090512140080d800300019502480901a03600306105403041102d5036400d94585022100c4c62000d544002501 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 477854091 1250 477852841 477852877
    0xd0e1e330406180503160506010f0602060105090702030408061005010809070f1401110a051c030b0a031101020a0b0f0612010b0d0b040219030602071403090d080a0509090103210203 79
    0x40c0250840a80410141d01c1c520042900f5a111303030440d0401c2e91660170030f120786a000b1003840020003c0038018102d0b00e0741020300302e080100003915140140501802502120042225903108004840040140714140d8116003040710443c42082c82c030303101d550300040e454000300346088000f04100d0112102038080c181c00d145441c0c2c201d0355010144406c141827045c1c80c0607001e03030980240310b5894090b106001910150381941240d0340700754041300c030307243c100b51600c01700d0401c0d0780300c0d092940c05aa803c1a0900200c0000e100101d20b006000710000705120001824005124240c048090140c0c2040b1000d04421030000805400c80c1d181c4051113070f2003508101450040360b41e0940294100d1300152064100d03c42071414801503c40aa0044641c4d86d40011044280582d0a1300842c5904c60070001d585000b14400c0000c2d82030b041c0c142c011303101520000b09a280700340124101c1d201d01101403d00d1b0a550707502d040100d800c13007102c84078000d00461305c14200c3d6000d1021044511404002044080d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 477855341 1250 477854091 477854093
    0x15030c06022a030c13020705070b030402030610060c030e0a09020a020f24010b03090a020904050309090f13020910090e0705100201020304021302131d07031b050d0e1e3304 75
    0x21017901900b0320340d07001070b800c000d002e01259043c051b0703102400c1d06011040e078074280f51050516202d001401412078000859007403118943c4405500171158040c50926441c000303190004160309180da00c0420810300c001128505070b5004174041e40e84107400c01c140d07202c24984980300200724400a030010540c650001c0184102c03000d540281d60006500350898800b01c940d54040703058000251400e03a00c9a0010a04218521b007100049612032b0b40f941d0456102d0400e619800741da6600c000009202e40c43c440000343c0e021300126141001014160307018001c10b8003c0707610f96200c030003174000d0a00507440d0040b203c40c00390050088902440c2d01800004000c7d46051100c0d00a41003a8844c5c0c04843c400000024030305420220072008102c80300f00502c0e54100310802804840201158012030040b41070701c0b0459030340240c141d9269084184010825000085c00c65082c0600300711503a085155041c0c00207402200040ca00c0700280d143c42e2498000035070000e039449054052000c11200180f0703800018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 477856591 1250 477855341 477855349
    0x6090603091a04050313050604240c0204060b0c070b030f0403050a0c05010212010806060406031716021f0f080c16050a21030b18040615030c06022a030c 67
    0x2501e0203002c0c0c2030003070350052000c55800d5550720640e400e032065480803e10072840240300c00400c00030f01c000c5075003600d060b107041c0054101e504500c429000c140c1a21840c9408680503105001c0b0050340108102320703403031310307019801c1660304440c1400000c1d100b001d1022400455243c1128001c018030001c41e0513681d11554200c84c1a0f00a5130130004101d10b0840f2900010001d0015020802801f241900742e581807a5801d032600500604085c866401c061003040491551620543c400b0403507101d20b0b5484240e08492102c0e0076000100035000280c0140d9041030b545504404010302010b95200188000b0452040b5000c1c0410380d0000c1070745608000c0001c041c40001c110607015840343d41559581c0200391a00c0e01120030a044190780700c2056441c940c003c40e4588580c0008a800711001c804080100c140300074802e0006100030a6660b4952140b160500001c01003401994080c1c01e240c0f0741602d44800035218155201c0d1500120381c40e0400c140307800103503041c900f44c8045c0a0001c005044040c0104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 477857841 1250 477856591 477856601
    0xa0b180c030414030309031e090d06020903031c0f240504091403030a06060906020106120b040203070e090109030806060301050102031903021306020601030b01060c05030406080c12070e010f05030106090603 90
    0x440d00f4054085508510480c2070001d10700c2900044065512400580385010050366407030441c51810703a0402c02d081c0241c0c0c400c0c944600ca1a0001001600d0f10b6616000c80d245200b41007610100048074030311358825112580220014500c649024020385508800a200c041e426040e40d4651700d0301c0b64010f224605082d070145009501400050071520600d00340d0904503070040d00d03c0c00031243c032400180001c81c0c2020842006040d980700821443c4e280c01c1070240509100b180007810400c0c2840418159502005100d01030205244200e4031410884181c03402000b10710390480105204400240c0c0a20700101545d0489106030003035842e00305400b100e0130910300c00b83e002c0414140e003403102e01c0b90402e642c1c5282000e000c3c0e5400030102c650642c100441c02c3c0744141d0000080141d4034a0f04000601d0110586007110001d08008800b03468105001000d8010700a10f90308610b151420041100d80c0208004408039082e243d448441e014100112550311003401804c010848650b0104020b610a501c2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 477859091 1250 477857841 477857843
    0x7080901050d110306010801081b190803030c0d06090204031a060411040f32011b0605040b150306060a1a130906180209010f0f0e180a0b180c0304 64
    0x1020746400003240c0c965044803c181c50110000310040104000355070420059405001c2c510b001340004404000203500140089980b94004d03074114403448010344108032160040c02c001000e480d240c2ca05410400090b8220641100c542d031705222002400c03400342e1003294143ca405c81605001a50f10321840e180a50014060f984c01c41c3d40c0b82030741c071010401c3c24040c001908841d000c3c1c0d00d405241c05002e40341c12010854242200e280a40c2044040420152031401501c00303007003030429502d1030720b0f5000d0b02d0182003502030030315400d04042008100c01d000c8894070403182890010804038800d018107584003000c03039006410070070005080c0720149411500350340c4140c4201c0c8491600510007052074441b420f603444500385175211a010b2040100c080c0d65001910300980d421820a002840003c207990148030310b10051001286031900e00c079200d000050030a100142c180f080301c0c0e008001405c01080d040791001c0100d85403209903590f6117001c29100800c40140c40c00346200784c5440d00c01590503400a40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 477860341 1250 477859091 477859097
    0x309050303070518030607050904060608060d061509021602090705122206110c070803070b0a05070318030c020415120803071b030804020f010323060f1509040b0d0807080901 76
    0x301c3c0190b43c0d01041403a2248400350354990300d2720100f0040c8000e46115400a406100c2201e040081540760005010f9045400c00c030041a6039111201030910020709400c5103140c0c40c00041c0010301c0c02c50401000110510a0703804d0181030380e40c041e0485540c081c1140f04030f000c40c03140300800ca2101041c1004c500c0c140c030040117a4060000e56032003208403180038400402100022900314603801c2d0070f01008000b8803410000d03610308007a9540e0f003c46810000c140f4040341e1340e1036021840c41c0e0300c69441417041c0591080a10341030103070340c2005081d00b031549204038402c0d401c2820141d4070158824004003283d1501041c01c80880507959245429000201724008025100e91009554501001d0009840e80251a91051030030140144660b052011041e9810325041c02400744803407600443c9100400e18035503171710000b52280000901c4030048000c2042d80a51003610341004a22884002c00e2415001c4400300312940c00442404100d4888000283c01c40d4401c0c802c020114043c10000c1c07901c600145 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 477861591 1250 477860341 477860377
    0x1505190e24060906090702120309070506041d0a0c050703031e060e1909030c031107170708190b01060c03030204050a030602120702070e1b0f0d0b1003090503030705 72
    0x81e1501400d0190340052200c41c644200500c40075080c00c0481c1a005130082c0c0d0307a91580e15100b200030b951040380c1e0b038682050034400030020b14114814000c00d0050540189016501c030781d04c168444042d40c4107461400301c2c0c0e0300840856840b8140b0310800100468588039242402010b0314240d00520720f10311806184943e40c40e1110158501e403181030050454110080102d05000208000c40f02c1400110300b1098508900c0c1000310f9000300b0101015985850011610402034008504007201c6030310213002071418451112100a000c81d0071810754080904580308510300d00705103002501d245001078400c00321100140f200d14490b1601c1c6080a02030b040140c0f800b42daa501042200e4070a030f0040e10392075070108501c80840c078803040076074100c0e80c2c920080980340d09101c4964541c090103402006050004140f00d00d00301008400ea4808620302004030382c566500b02c0112014043c0f2148480c8114086804854014043e20a43e10b6190700700f0025415a0b903040e40c00e0b079030f55000740c182d410000040c0c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 477862841 1250 477861591 477861613
    0x31416050d1d0a0c090606120209040e0105150f0306040b072f06010e24060a020a0605180d1706060a030b09090c24030a15030c03030801031505190e 65
    0xb15820541100a48000d1601e04001e0403d084915a15041082101d0403c401004103e47c003008102c40d110b800d510050351029020001001444030003034401540d400c0c2800c1002000300c0709040f41c108001500c0828060283c41d0400d911544100c400a241100850128002500c29a00c41500702c2819070252000380c0101701c842c89501c14141e082d8016400b040051040700c94000c00207801c5803951080384400c501c619940820740d041c000b48203001b14004100145680d20130000d440843d504900c0820090030088142d035445075080c01040200c0c41151916040140304040c00303c001501c0d5030b668203280e11003008100a82c0d000441d580101900c1e40000d040c01e0b5129202d16005440090081c41c4546048042c4440c510000c2c824804c286000c0c41e90a801c000c459040341d5001c501c4801c0050000f4480102460540ca075420207025015000c1001c0f0415400000c22411f8034015510301c1440029041c0380701c10707600d0403289031056001c40718140301c0c0710031319400c00c007540311100003940d41140139 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 477864091 1250 477862841 477862871
    0x1e0a03060807150906110a020904020406180f0e030a0c030e13061508061e1314010b030a0b0402091f020109050d0507021c050d0c05190b0403031416050d 67
    0x6207070059403c0440d035810388005035400240d8100105000d040400345001e030740800c07580310500008068040e000040000d803c40d5101c0c1c1c00381018102da0f00b5010b800b9048a6480d40051080f4204e0312035113450010800301100b0000f043e07031000d0060740e64220541c501a50225076184240141d2a00038951030560f000d948600d00841d405884000da030141640440c010040003840043e080f60f016580451603030038444c20b42d89000c6c102210607102503407075040c0d4200c01c1c001807071b1340c03084411040901e90000c03d003881000001d5016120304041480300941402c100401ca02c550342a2a070702c00b515140306144403c03120b4000c000300041c0d000001d5812016207516040c00e8100312080c001540024035181103242001c2c2d064610350364200c2400107401551340e0182d441051002c24010301842c910068200701c0100400300950780ca00030101c250b400c582c544001e462800340c900700e01090a00c0b11803d913000c200d6084900c250142d10401d055401d0801c000e40781d941c46038240b000406d403289000600029 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 477865341 1250 477864091 477864103
    0x60f03080f0405092d0c041a0f070803060a091406010c05030c0631080d020906041503050f0a0c02071e090e0601051002030c03030a110d0f090203070801021e0a030608 73
    0x5200101c4105c0700110310f0390004e081582c612042e44001c410911908101540a0720142c0e9240314030a0b0340f81600d108004c04900500084d058502c0b00050300e60100709525028500485003603d0314803645458800344001c1d03031076070300c8040d40307214210000031007a42c46900c00c1000c090040c010b403807905540050b05810403500701e4524025151460b2610402d4220b4203100b1450342200401030580c16003561020f103103120724006444802e4000c12050500d50b5450b007150014400c282001e84c01c0c8070411800b80143c10111128003600707901800241c210401070040000313410156018090840c1018030440800100480313900740000b1811780490900b0003403082d0001e2200d1180140381c20340c5400708004a22809003240e404540042c81060420200001503a4000d85840b50108156042006004590050707200146100741085d2110325000e13050707400840b81d14002e070f05681d01c080d02c6170451400d0344120b100d51040d010007211a55004100440070341800c1c1050b02d00803448654801c411440c1c45 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 477866591 1250 477865341 477865351
    0x110603070e040f0b12030c0705040b21010f0c0c0305121b0403060b0f030d02330f0a0f05060604050d0f0c061e0801060e0603181c03050a060f03080f040509 68
    0xda03688000b44d440d103018030115904a43c45d4000398540084001341607100c0c4003e00c2507034003a40c1c48218000c580c3e600c40381d0320080074038608004070034034030b81a0816001c1c02001c501801d1207841c0501700f0445920603582401129051f8440b240307000c080d440c0303c049100006010300c1c000b1011039100400c080003100104011401220003182b82c4881504000c0140e1862007024400d9101111850a0b80d40124104c00070800c07087d550540558010b00000901c0ca80364003a4281c010307151704000c9168045048a80180c600c440d08103c000000400c2c40d00702e9900f0780d41b0030b60000c02400100030300d00c0c08041000c1c11522032600e510301600d00b503458a00444923500500b01007a10303e42440820f120f070032246451503085140c100d0155140c58400303040d45400c0310f1003601660300040003c00d4034581140e201140904003049a20040c0c4404d54603c002d0869590782c40042d042c0408641844018010442921006008103459514554500c101c0350f000b041601900442440002a19511010264451 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 477867841 1250 477866591 477866621
    0x1b050604090e070509093a17090f06162706270504050a140c03090f07180b030a38070c0b070e0a0b04150c110603070e04 53
    0xb04420300400341c20424903420550140d03260004225041800003200c05e003030b000e0320184540d0400d075100301c58100c0c41c0e080d05c401c103030340d485848681010350300007500d00c92a15581d1103110207848a0a040303485480703c1c080c0c101980d0211000c03913152441c0000507103c1c6d000301d0500b034240c006e488588a06810741d01078031403031540014504100560700003403040010303000c1a2407480051180c128917095840705000b1680141d64450005e06c9a00c100e900c07400401940481901491a004c01000c1e49076100b10b071412058041c0b554141c080f03180c00500c1e1001d40d0240e0301c007449284100d20400c402442d228001952510580340710002080200e0f5041c5881c14002a02507a181465000032000c0c0d03103904510414800700e00104403d0307540c00703044c2456030396101350868100c1d22034040859500c0700c40440350342c0c086410100010054118070090084401d8014000c03d004000141035400c60124a005020040e05e814480454502540110b9005031a820b10760300e40307249a00803400712080100000c0b00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 477869091 1250 477867841 477867851
    0x1226090309030610060518010e13060302280e0408070b0c0901030c14120901060b27010c08031305100c02010c080108010b0a030f080403050f0a0318050a031b05060409 73
    0x24101403080c5544095210941300b8000d240c1007000b005413140000e0106030011404029107240e10030034134098003e0700144900450641c0b080760358010f10300c92000703d101c0d1906082c100c042080381403a4a01e01403904890b04642c91401d007000040350f500403c1141c042d2001c1001da40002c110940c2140900039401055444214440000d800c80b001c4040c140700b4407d109a03000c1c0c6003424081152505400120442d03910b0f01c1d54003034140540002e030001032040002240c1c0c04010390a00342d5613840c070b9200750240e03008000a000151131500e403e0704080c128001c00c0001600c01a14281d5801281c0e20030812540b61000c14440d41c0102d400e5691540300507512900b0300c0840507030007151103000d42500d038020440070764071000040d0031221521005118421201005c010b200240d0309403401540c02030140c8102050103100251921020141100440d18031000d080d48220f016020030141d55010308030740d828a0441c2c5602c54810500326040b030402404c0b01c4081403584580029100415456101241c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 477870341 1250 477869091 477869107
    0x302070b040b042c131704080312090a02180108010c2c03030f2101060c0206031306090f0302061006031e0b0a0f0b03061c12260903 58
    0x1040544680c40150403000074070003070002e5202030080314101d60110901090503020001070211210001d5990204030040c0d004004140401c00888080d65116190300031000303940b81404031080c0501c6c0600861a4001d2116220549000310341d03942090400c1c084808803c2d0b1940040c080040300c0d13040700c4e031040b19280100410b01003406040c03800e110ba4106100140c45010f0745005110011402c400380003900840d02d121a1414002c4400386420310031003c1c0e54103501031852000c00b249550b0250201c11032000010507070300c100d281c184e0407940241414510344403e51006203020880784180d5003035903a41007400c0040c40c40060700d1556032194029100914002d1100044020707180c0c00780b4141810400d40a1051105903030340085083e0041d400201c1da81400013007485c21580da00030b402c00640c3c44802142d01e143c0c0201542c8034542c215108215550001480322040e40f40f0200244003050800044000342d008015118040c1c0905402140010809018103816402680c40714051f401c0007401342 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 477871591 1250 477870341 477870343
    0xc0f05070e0a140601051b030c0c0a1d0106030f0b180603010b180a050c0405060a0e030106090624050d090c030c0e04020a1403010b0607060c020c040b0d0b0406020708070b040302 78
    0x2d60006505100b00141c804420309908807000003404a03040000004505d0780c9900440810824040d092040301d841c3d50007002e890741c1d50303942100d000b880b9104245000800710004249503035445c1400381900715907441c100040c1e01030f008200c8103000c000d4440074420b90790740b030f140d800c0e20b040c1501103503c0b075a40c10310350240b608540310380701118000d2203d2000c40004018450081d43c20a619050010f010f0b40d681c0c0c1a01203d011b00d80040740d00441c0000c1005c03820f58000f060100500085008100d000d60b51072501c0e080320194460f08035aa1420901c0c1059001500c141c87c2280115061061802d1016005074049906101041b114160180d00a10502c050001e2200241540171482070160410b5000100c03062214403408140420310000c0f4103003900d003034000044cc0c01c80600030603210040e51070424017820b5644109001442250115491894240641c1c404800040c0203a900c030261600c60460100006100303550480c0c08001c03800005146100801c2002c1c025880d83c80941480c0c9002 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 477872841 1250 477871591 477871619
    0x70203030a0f02090f01050d180f050708061003150603020303040b0d06050f09180f0a08071407061e0215010e010e0901050402010504091a040501060513080a210c0f0507 74
    0x307481c1c1910501442c94141c9a500405d82d03040400d00b030032034840d440040344002400c0e40c3e00d41034120a41441c030304010000c40310804c1d071005215505503020340d9111840f282d540c410458040700a00030356441000421042a000700100340e983c04081401e984a0f0007003861540540d1010800c03c000042004440d0b14078800c4601526044419564200080c00052003803813003d0111901c0844800480407500c004000d22002c01c0d54030b100323841640c001e9081000098014890960388860b96030189910110301003200d00aa65040d216411981c143c140e400085e240c0180b000c84c190712402e88138110300610501c06600800c5403801c1c520030b641c1801907422558201501041413a81010700f4800182e1b048801d40b400d6400740d103400502854a05101031000000c5c074a07842e0414500400030a0440d407000c01801c1000d202c015012a803039481c0002030f5115840840038040701301c203090346075506041241607074150303900e85400c070020fa0450b00c41404580c0300301c41c1114558008881042801100085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 477874091 1250 477872841 477872861
    0xf051008011109060901030b0a0909050102280f110f0f070302030c0a1202090402130c1e0c022803050d0c260732011e0e0d050a0215070203030a 63
    0x82c02c0c01d0515403408100c4a0080361146414035444140c001c125403130b10707030001008040e984070078801e102c106c0c14028001d5000121001c01c821120f0481ca040a07540d5620300c0c0c100502d543c500b244004009000c81c6c00c803442a007040d8150250202c100c0007a2000c001003100d8001a1001e8452240703188101480c1500c41c4000318044d111840c000c01100c02c480861241c4103406079010503081d80e0321308c0040d40071a400704640500e140340c00d0144440301e0344800000318040710700105441907510114107075a50796150200035800070f00c0b140075120132650300d172460810004003c41d07c409161255a020b060182500742e440c0050010091340060001e24052400e60520700d1501c290710a901c60074003035040c410000090102902840e60b41c10540541e00c0504072490100e4211148101c4200c906010700102100907811140e41811010b03a0400c601c10007003080750f0030004000720999000c05035030a40142441d0815400b845020a86a03507003000141d1150086a0140d5a20f2415650303240813541c400d40 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 477875341 1250 477874091 477874121
    0x609090507032f040e07031a010e03030f0d090b0702160603020412110d0c1202040605030d052a01050115030e010c0207050f0609040c020304060f020609060103150f05100801 76
    0x8450b0200001c1c43d0307640c0c2d41d6034009800d914010356140340b07030125910a560085030008129410400d4865056000b107003404c21501d00321528540300001100c00c05201c0c04025815002000401a130b800c0410080c1110004040c0129a02d810750b100c020805204450501c0907800c00b4132000000340310400100c000c0d11a600b400c50409092045851619000700001080c46410441c422419030311049a84071084e8010780d00080346840e4540e000035400e083c0400c900030343c100742000c94a40303404542843c04c3c50403580c2d1a41007402c00079041c614401c14895000a43d55050030680c1418400c1c001e881c043c0c1202040f00b40b0306503d4000007005c48200d19240f44544c1d2600602e403004075400f11ba103c0403102c08a07182001c1c400103d0005800f4840c0c244201e61291074404008400e50b000320141040b1403594441e01c4140c00807010507600e404088442003100d030081001400001e06081e514400c40300349030302c0001c504032200440d03001c4a01c01e441d120305902c0c04001c1042054001d000d122030000d240c0d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 477876591 1250 477875341 477875351
    0x509031e07060f050d050405030c070602070b19110105130b150a15031d240108070603020f0708031e010510080a05062409090f01081c0e0a060909050703 67
    0x241401e44946860042c0000c0001105040700d042c0e110b441990380300c4000600c1001a414140f074151b94075440190384042c00d004803000020004e00218418007115440c0300554508000c06007284a007022809503075040c420a0304140403020400d114031441140b210440c000e041140d82810210001c0c000d2100a0800140c01e64403c642c90701210102241c40c108980b02c0c44400441043d1b01030230601d000e0310210010301d02d15104030700000515440304103000d50050341054151800c0c40d01d031002401903060540c005c08040000300e101c1c1d401854504000b5206600b0070040f0303901c005286e8001c0d42e1300c01c5d40e428034400300e031041503141000324010311003201c959104541d0030300c018111040081220f01c0f45a40c81307001425075291a0010841d50800819440580e03039541041c0c0c599420050b110b034040d0100d04000741840001e056a5030681c0d007100b0017400c414200c09596403400b0a160800307410002d00c0840491180c075410392032006003203146c82e10200c65041c509808100c8800505040416081c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 477877697 1106 477876591 477876643
    0xc02090604241404061a0a030f02070503090102010e01050907091d06010b0307020105060f0915150c100b0a15050f040e0a0603020f0d08180d06020a050903 68
    0xc1c0f1030303002c1e45001d840240400c0381c0d8540210031002070019500011030384c0120152481242e42d20340440d0585060355070700207a8210320000c13149540003003401e40b000d68080c000c1500601d04200204442e10b400540d599131814188210210f0581d01d02c00e0003620300d20383d00c0d01582c40040a044414a5035500314a00d41ea5004492280041d41b070800456044e29081c1426100c40c0002400c10b004c40e11103450240d00303070500300302c40d80c2e01480404800d007801180001500c0646408005005412820108001a9401d546003184140c84103141030100c90200e085100e400384040ca04280c484089542041e410b100f10341040d840d1420b074408000b95940e00c1d402c84010340b4401c4c1d8070320214446060a000b0720542c00e070300041c00310300184041482d0f8a00610081d42031312000b8124849220300341c07910001c80c1e104240072000110300160203000b50508000e038a2224200c200640380c50780c41 = true := by decide +kernel

theorem cover : BRFrame.Cov 477697841 477877697 := by
  have h0 := BRFrame.cov_init 477697841
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477697841 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 477697841 ≤ n) (h2 : n < 477877697) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
