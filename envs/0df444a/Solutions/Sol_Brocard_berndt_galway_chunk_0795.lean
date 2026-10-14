-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0795
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:51:09.976497+00:00
-- url     : https://prove2.me/submissions/bba2e9ef-9fb9-4eba-90a1-07c99f6fac42

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 142805755 ≤ n < 142985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 142807005 1250 142805755 142805759
    0x1603060b062a0f01150603060e0403080c160c060c260316050c060f040c06020703080901051606050907060e0906030a020d1509081201060e030706050a020109050115140307080604030f09 81
    0x240110030405e1a1148108400d603e040301c05030803294240c0c4540621050401000040b071740028105500640e1178220658607614101495000300d01da81c001850500d0b00c203008112a90f02000554440c1d100e0403010035020703890700307829044a2401e00d040004650400c00290000c1280d0310030b550710025070504504010b8110100d07428118110780d9444100030b50010003007400760780c221410061030140050040c0d6402c45d16071061901ca0b141091b0b06200f0002036000d0146000c01100d00404d0700804100014100500e80c0742e1661020b00c103440029403240303d10803652a0018040d8015030b030040c01000344551f954240a40c51007287c034203075010280d42c4000c1c1c00340c203a2401002001032156078080d555054902041c2c0000f20181c0024080001c405046140741d2000030314402580c0042c01d125071030382d500002c203c0c090403980c0700c02010f5500349400301c0ea1101c0c2d0010814280c131000d00022100344850418180e903140f10388a41501076002402040110340204280c41c0c1c661081e140c008412a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 142808255 1250 142807005 142807033
    0x9060301181127010e031b090702030f03240d051f0c0f0804061d1c05070308010603050a180b040201180810020309010209031603060b062a 61
    0x1820036801012020015441035860300102d1081c02c00340865946a54101080104500e20056051500346203440440c80344620f40d038021203a4008502c03008044543e80210614000f0300c030040c403d0b026002c0da1013200400da11350700210a850b2504000103419065070b07215124404485840f4006140c074608034604203040303446000c118501280110300621102c8420000038041d245091a9031000500e44480e82c1e040796441a4482c80d030511625002c200e945417410301e0001030a05e031507040c450b101e01d8059501003081c04288088401c51030300504d00c407451a80000c1d0354612a8041c003c001031004c1005104583c000c0e440700d41c1100c143c0d000001e039011045003003107015109d40819202d030743d4171500b003204569010590011040f00c01c0001d00c543c5143c00c034801e6a5148121021843d0b0342c0210002d607030f6060035170560306100401822580082598102c00008555a0100743c605500b000b40d5440d0070704001d002c440b0041c40c41d4241d0b002e03040e25941700034948500c2003021803d601507211081c41d0380b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 142809505 1250 142808255 142808257
    0xb010819021e16050c09010311041a031b0f0607050718020c06010f05120d1407080c07060c020108090102030c040302040c02010b040501060e030d020f0a020f0114040b0307091413020f0906 82
    0x4403d110710303002e6214060604500d40685425014452092100103200040c403580d80e5110514040e90003184500200104881a02c5031001103905480f543c00c000c03000008950141403090340980e00d0060304c0c0c1c00e04040c045caa104d00240070701164407004081100301000c40c11001080c405200040c20180c07040101d40c20b100302a4820441404944424010b524180c0c115000922100000305507010a45e00080d07c0140c0d50342040700506000b14160003800014030484019070312410960f03103601d49070b14014098486903001a400161840c0004451000510032280589000b01456041520b10f508200107450229102400c40d5240e00d0b1400300c0da111405014080c0125403649000082d00f2800c0c5454880892910011580701c00c0303410516410214001160a07010707261020310700510401aa00711030b43c0308180400da1000140081d00400200140d40100d61503070300c861080303560f0240c400c011a0784c42c08a5911941200d0b104016102503070090a041041029107414041400c0019500e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 142810755 1250 142809505 142809517
    0xa0f05070306020a020c04060902130b090a05090406020c0609030c0c0f0d05010507110d030603030509060f0f03010312030606081e0403030f0c0c0204200d0b0103060306020c030d0b010819021e 84
    0x7603484034006c100785d45000d010740300c05000640c2d011400e00c2030444040704e15103050710501c080031800051160590b240d1000050143c00c02808000c070a0a00303162402c029400403d40c2c40e000c1c003e50010030146500813013110400d4000400034844000e9560400014400c0c281c20140d109464541941c0054000c2c01801d1140d81c042e02c45c1c00c0e1101500180c6070a20b40307180385180400d840c010301032001982000c10388507401815520f0070745a0204115140d000c1c4100300c0c406135112400310002080242402104242050640c1c09101955a800040d5921401a030700401c1c000c1150380341401d4010096001c5a0090003071401180c415040210341d000c80e00c40c074003031000262a1110b1300065082a0003641141140a017891241d2607001aa40729107001d10300100301801d803201e801944503031190b0400c00c00b542d041f500442d42c0310440100544e40754844030501000a04003583c10360550f005a8411348103158600c0780f41c0362401042c06010003940704840088202180d0040303c55040002d03005455 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 142812005 1250 142810755 142810757
    0x42d05060f130e0c030601061b0f0503070b010612020306010f0813060608030a0306080d02060106111005070e0414040b071112070302010519020405150c25260a0f05070306020a 77
    0x5402d0f201d00c4115403c0845464205019502001c010071000780e01684042c0000d50401c07031480c18465130b140200c0c40c43c041ca107010f410341c80301180040502c40c150704214103c403840e860b004010030785080f49500b680021501c5070b0200d041d2001d0000c406000d2810140c0c0199607020700a6000c1c060b0f540c070b81c1100c00c980c01c072041c541c0c804200806c1040c1c03d40300d64000b1340342020060020170300c0c200d8000d65aa00500501041084222035111841d00801480d0002d440d04c000501091a14260042c41054004d030010b114500f465000d05410100c2c1445602441e00500307054119540e54000380c50008005000d411548291002d00c880c0c080c0280281a41620960010845040032044c1310310628030001d840310427910420040005950311a90800c42d100c080564585414900c0061800d205200291501c61098400c4440c4001d82d10b61108041c0e50070303201c2c111503800c00304442030040b0000510450b9594040610440441d55030482060b5651203141282c1c441501d1342e46840a80e001201900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 142813255 1250 142812005 142812011
    0x20306011808030d14100501050705070305030412170a020703060b210c0103051b0405040c1704030309060e1908030a0605030d021c1115060609030307080702042d05060f13 75
    0x2a0382c00505001c5c01d60b80c035600000200090800078000029102c0510500d410702c08000b0f602800c0203024030032400156040300036240c03650341d5158401194459000b040f102a034840b100080c0611410040d9104180564001c20003a801d41c0c0e10000140030a9031541c0d440b004001c154410080020451140c026105018000e50354071000090300340d4001a0180d9451103d03e03104c96008203810041d03908407942240e01081403c0308440a550005440c003d840c007443c4034804100074541c064102e800114403968040020f034290700c1000351915181030340030013400b149004910202d24598065a04185d29100008a895a4800180c82c0017240600c601c056002a040e109210070424804410b2001c04e080004001400348422500c1c1c2e01d50004c001d6090002c00c010030480c0d01c0d04d0007511103506019003165600c0344c0600b4445d10310381010008900c1141801c040e079aa080c0d020403a42c0752030400000c025402811114040040d190003492603820518031800314900307070303181c031002c14010380404000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 142814505 1250 142813255 142813267
    0x1c0302030405090a0506010c110103060909031e0509030c040e1525051e0309010e03030106020115050a061b03140d0203150d03050a0c03020708030304050705010906030c1202030601180803 82
    0x40020f9500c0104a216420329100412020b44d820030201240030740e000c4001c8107200d244600503001440d0079048002010710700081441055001150340c40200d15a0440344e19450115204035010310035241e00701e425820560040c03010f41000c1c0c0044009650640603941c29180b41c0d850519404c504561003032541c80e8034114240d151901200a0040700c200e450490300d40f5484500c82c050440c2030707804202c039103000040000c03850203081d400304440880300810b0320741d203503136802d00207010300081105042043d030352aa001581e4a030001d00c07102120302c55260f100e9428030010320031103620b444403030070340500400c03d0094403603a04c101c0c000c0444407058080103881e41441c4484803c001840000503000b02f042226090209400c003042e01d03003da41c185041081c0c4621440c0032070821740e40b58000803046c030000c01030100304170000c2035043c1500c40a0340c1d00c00c0840c0e9650812020b44000030342403030102d800901c054040e01600d400540e445070044c1880140c1145440103100d007002180d01100c0aa00f001c511 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 142815755 1250 142814505 142814509
    0x1120f020a08041709010e090a0209030105090c03010b0a05030d200f0a11060909010902030c040315060e0705040b251a07030b0d0b060f2704050d03020403201c0302030405 75
    0x44d107074030b0108101c80750802c0e141c4400a402500c0d000c034090300c90402d0000050614034a50102d86d40064051b00034031480c10b001504565406422804611039400c01087c07442d1030804a88000c100c41c0010001d0021000c4d00742d0945103500c4990300c00c41491100090359075142c60410141c034034405204010544082182400d5450701010401140300e14020001d00c1c80a030f45160070541919000000140d5a48034403048012511499000809044d00034050031180000b40d480302044640300303044440e0704d683e40300040b0380700d00c0b85006003602ca417028000b0455900b14410084c180c01014540d080601d101510740c4003100c1d0b802d0743c21a0b00400c040c410003070070640c0350040003080281518103900b0313030070700303548140060000405190054102c4540c0c5226036554140f2100440410801400c03030b00e0a4541e05054200301311401d5645100d100b03a0341c1d43c420310900c00c84d0304503a040543c1464880700c1c40796036410901e8003c4070035400101240110711110784840b409103624030903002540e4032494202 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 142817005 1250 142815755 142815773
    0x19050102060a060b0304060e100908030114090103021c050c2806050a17040804090203090f01050106020a08040302010f0905060f0d0e030405061608070b01060806091f0501120f020a0804 81
    0xb0066414608200041088410100a40b03030002d510540118041c1c88407000c01d8034024444230100c400c24203000c00c00d02444200d5000790b040c1c807200b151403207822103d8014020001028403000350003a0407031442c0d40c0700415080d14034021034441c00176641c0f5243c00500241d04110070390707160340340040000d003811601060000c60f039000341500d082441c10990000400340000c080c00703043c1b21300341c5000800541044103810896020745030350a0110745a042880390b030760366200c0e00c01c04101c66602c0c0100124006000080b003081d546c0e800300002d840c26085900450307500700b5103903110080c045c0201d40841c5d03540d9800040c25407070b0100002142c90310880009117068401a140000c0e054004004c20b00060711080104c504401003000300d122040014074000701980319400b006411125a107002103540b0f640020b00780c1c021141100c1c1448182c0310303441700342c0c0001d4014a280d00341c03115242e001c00141d40140e00d1004040e501034800141c00b106034007404140d90240180100080411040000b0045189 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 142818255 1250 142817005 142817011
    0x3030f0f0605062b1104060809060f04020d020409140f010b06090603010303030510180c090603050f01030209130818120703050318210105190e190507051905010206 72
    0x503000740001d03803034140410301d184900286524140c80c4005051125544950341d06550b103100c14041001350801c0c1003142203504103001d18070010725542c01090340c0b810001803040c0114040100d620383c0ea1656400c00802c0f48810300201e030000c0e118080040411f04105075601a0075112000c0c0c010b100a415000382142d01500c001c0d0312890041c44015900e031141415641503aa040c1000a4983c07a01140f0368041d00c9070b5170140000c0108160079821118a03a0401c03105210a500e81e81a0703540c031040258184c500880700c5080b581c10200040000d0324281c7c82890308030f5012180600540030340d03103030030303209900400075483e1404c0b601d00341a02030304121642c0350b40c052401d80581501030650756010345900c190003142107003c00401d8215241e45d20010402803a00702072041c0c0014118420b2020701801013111454400984c4900c1c101040e00c0c2400b4000e1a800400301038420302c0e2005030000c080d14140c41d07040e140c902c6265400314440c1c548818580201b90605040c820341440c1a0009113009001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 142819505 1250 142818255 142818281
    0x606020307080d0902030c03060103030507030905010c11041a0a0b090a05010c0b010e090c060c060612070513020706021603080114041b260a061d04020a0e090111030403030f 76
    0x7000280003080c0d50205640036400341050104403050580000307840c0120224215034940035540c00041099040360090281502c651a1002c1e526520360040d1035808045a018000c1403810400107051f2425922082e68507030150f06000c000119000440c9100c0e15a411140e0b0203000018106000d1410b00740c160b004140900c2c3c8940f148003281d42d420b040c0d41042c441c61110051280209045030003e0040d620307810700140c05142c480d10300e02c030761a5517100d0946141e03000385100c0e2506295418042810400d40f01d010b081e01c0344501680013454020341c0a0074064541ca50b080c8244501c8860109020380d0a0b0300070741c0d80c0c502d1035041c0407240d02c440c000d001115101e10f182c0020340201903209031400d00029424100300c4030029010202c11140480f000500c600701501104004d0360f110036a21141c107071400500e585000e030f030728040030007110601178402940c80005d924040103d000000d8070568440091000801e00100800a01c2c0181d0010f41c0c0840200c4d4446404008414207403207061148054 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 142820755 1250 142819505 142819507
    0xf020106080c01091502010e03070c0302100806011e030e070e010e2212050918070207060306030506060d03020a050d0c0201030b04140a050a09020a120c08031c090f0b04060e0106060203 81
    0x21000280c6104d0345403140c0c08103501c401008880b018000c0d44265070b004078520549076180701700e01c2c111000a00702e000032031007090b001c00300c07410540c805c07104a4825401030319a081d00e1425194850700d0403034500c1c0442c0405d41c441e01041004a000d002c00c1c00100380b03000b010b041a50524000c540006801480c01c88a0402c0e0403100c104c0b103299007100038190307402c008528503412180348121182c2c45504451900076008007010382803d030740140c101d44500c00c0da50941d030240d03880b14800c600f610054480586150303c10b4011039082c3c500907940407526807190040310651042a9140303800c0c442401014004560006140c0d400d658050007107561070181141d041101901030081150510805400211520768810010709010450f0780001140d07030f0000c0644255036130320302c0708114010410000b220098104500001d056400000303482800d2071181003c0310b00c00010a07d40700a015aa0f000d4424500c8a40780303c0c003140034050f038280a41e008050104d01c00c0c51022030582942c0b015032040b02103602c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 142822005 1250 142820755 142820773
    0xc0a0504060c11120a12034803020405010206010f080318190e01090c0306231306080c010f0e0a0608041104020f0c010e0a0209011509150f02010608 65
    0x6440012036040d544103007070280049402d4200940030031030511049821400b11907000e980b004000030005980d903c640f0f502c41c0c0711400c14030110191005202044000030b04c0c0349400380103000c0e0020366070098180850340d10b20000c8007102c0780b00388107040071000302095001400b8031441d41c0c140101809016001e152140300c07498070034116500c0c0310300103801624076000540211140d8070503500c0381741c002e002d00c8840b5040c1d4503000c0144441c0401e1181d24001c0f464107110020303da01030700070f0030308458102c02101844004c03500201c80c10890f030f000340d56102c445407401c040e10400c43d01c1598050300d03840c001015500044400900700140c002c07810f00900c80c103007580c107a51760341d04c1da0790b0030640d40d0500d0112525204d52412003108a00c00311200ea1040c00810030009020b5244080c00d00081e100000703000b200081c1d82c01ca9241c032407449000e034219071960014040040f00c81000c01801c1c07480c0c50581076441d80d500d09031144801c41e21003000003401188811420642c24014030000d04100c1300036203607100d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 142823255 1250 142822005 142822007
    0x7140f0a1203200a1206030c060f03051302030303040f0609081b0607020604120e040605060a020303060108010f031e0302030d050405030d061a180d08040e0f0f070c0b0907030f1401050c0a 82
    0x401120f00c03e030200301c5c407040b4002c1c0e201c038544c01990066078021149071803641c807030001400c041201d44d80c038400a481c203800070b0320f000c1002c6c500308030060700a0080c600d9a01d881c1c581c03940f41e503081c540035900245c44002a10001d105c500080804503103100e0a004010311455005052a102070895011984064103000110702008641100d0341d2890900700c03031884108020a010704030a522180d031100d404070701e18a0807038010000758460740c400d0381d030403050340e8a42c1c0101e010aa402c2c080906141d40b45050b094014141104003107900b0700070300449040114250801c070076158200d40899103a040402c2901c1a0807142c0608005031100320002084089031040c0c0c50807900a10b0944940d40c2c0481d1001030243d1514a078295126811040c46569030743c0382c000100000000741e402c04401d011000c0002e5188120f07445181c0a000b86660300201003080c3d071a0701d104001701034410b09050144440000c00944a07c01000a0602c50b142000503410054841d9085500c01090b042e0004403c00c00d00120b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 142824505 1250 142823255 142823257
    0x60f0e0906011101060f050102240c0a03270201020f0102090f060a110f060403090b070b0a0b041d0f060f0601050406031a09070e190b07140f0a120320 66
    0x11800540315441181e480d0030040307a031100c0c00c0d800d0030099440c1c4032000c92100f000c14800b10580d00b0a03021206420507014045040d4076482c80220540500700c00411460802680140600a95450b0200307d4203803c2c3e43d106a240f076140e84101031100d14208a400310350b014801c042e8556444002181803000d100c010078003810403665a10710690713000130407140c100d000f415185000301e4044212201e03039230041d202558484064809401142031104005140e400c1b403412940403c0d88010605216142c118039240581300092250790301540340c00011000c008404500d0885900003801048074040d02a0380d141030040141c0b583c4481440401081116600141245d044401e00e240020741d05140d03064009981280d0500154050100024403030101e038040760072100d110003217481001d903000901003500550b14511906254001c1440000c0124514090100f5000c6400c8196100003070481005424142c0a0208a860503101c296075a1065803504c20004520301e039500504038040100a080d4007 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 142825755 1250 142824505 142824527
    0xe0a02190f0909050a063e0f0d0609020a020309090105030106050303041a0706110c0d020615040c020703050607050301240203030a0207021c030504080f010204150c03170f04020a060f 80
    0x1030a40c0b0f4040b60340c01c0000400462201d66000a810492550301c50742c010600090241d40301e05840d2503e41d210f40902030858854031071191340000d1b52500c480d501c0c0c04107464004a103801a201d5a50600140101c0140000c10110f06a07a0140d0f81c0e0b04501c20402407c3c08060f007289000340c1c03500300700f4041074a0000488040d2408135018454601c105441c0d00d850b4070403a2402041c6c0f0b410303c171980114100104c05070001c0065030094801016941404a940c0c034400c48418101c101c40d46010906418550b0200382d1300e10052040c2d8412035280d07100d4601d803140940b52a000240c000004000da4070388400e400b28030b140f106400040070094003038004c3d901d00000d0300740c0c090154009420011503481110f9001d515001040428000c1c20750309018000b500103106400090180003d1520204018400c03602991940808640030b50f001035000c42d01d50351152422428092501402420500ba4070b10f0b0611070804030407241010b00d024410b0144c4404264803082c00d003c20088050707211908045000704c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 142827005 1250 142825755 142825769
    0xc0512090a080304090b0f0907020d05030c0403080408280b0103082803150501020f100e070f0305010903031802091803190c050106050a0b0a1407060e0a02190f 70
    0xd211820100061500601c079805240c1030b1100160000f0300c810300c1d4100182c030304c02c12a60403694003e510213004681500f21450030050300b140051001941c050302c042c54020307040c1c3c103d00d42400e45a640309400c076406600400d030154420703080400390948820481455803504441525042c1855503036404020060100418200c004034181025141d0201620801d00c0c924400000c025100d10000e0024008141e02d442440501a13002c0b40d03950000a561195900c00402403030705258450f001c000401c0121101602809803081c0051110310010340d00d8050340c00394000151990007072030090f080b5041d02d13135999111132142074441e016a80d0110140e900c0041c803041ca03044501e4021aa40c118421100884203528100e914203a0703150344040d100d49620f204a00030040c80ba140c20800c11151094818259071034801c21461440f244180034075402461a074070002d0030440503660303940946080310040c0741140d00207070b940342c15460240750b000108981c9920108205080c18004200d0320000c5c05400303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 142828255 1250 142827005 142827007
    0x1006060801141507060507030e0705010504090914060f16030b130c03060816030b090105150607140307060f2004090e0a02090c03010e0c03070801062609070501030c0c0512 75
    0x4900b900c43c240785040500b90440d545a03a15000d280003401064151801e400080c40d1042c4004d0741000003980400361441612250705280c44c0450510251440c00e9048940e2040150b80503c1c86408200c0310307010780036054a00540e894031107415203515410300302c02c2c0101070502c80c45900f25250071803186098602d2110201e9288072000f01607001c0c0000d0b03400410184100400c21352014421480300c002d40348140900c545a0300c40c00d0545007600c40680750141481ca19105032400d0b403030600b00412495105124446a20303483e5540c070390951f00843c41c2a0341154689400c0760812a49105507000c0c040307a104d02c00180c03c403c00c81307124107000d14060070900a50350b541900340080c0410040429981c010180041454621040c1401e50020320822240f0703500f441c00f01d222407800c001524800d40c0e1541e102c80c210381c03030301c0b20485600d90504600c0000c1101c42e155000c6000b000b1010a00c601e440c00c0080c40d115160500050807540088248001c211201810000107240420030265500c54042d07a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 142829505 1250 142828255 142828289
    0x7050310020301210503070c06020705010201060e09070b07150f0c030c0305090a060222090e06010b1c02130306020304051e0703030c060b010207050d0c09050109020306030d0f121d1006060801 84
    0x20521b10f00c00c5000182400d00000c50020761a980040c08106440c402c7e8024012143cac1c54658030040c0500340c5281c00341e81c0014006000e40d444103400307014424091220305030381d4aa0000646c2c201d0302210090004a80c071010090a0300c2d8250081407030252003403800b00020701d04121501d40b80d43d1410f0b0700400d01c0707400040000c1c11100f0491380031404100d0140000943c1d50741e180000062085510058045c0100d0000042002101058404808a80c5c1a0007030200d00714650000a52000c800881880425000840030801d2032000c0c42c030581c0f2507001001e6054180141d040c0145400b925001694000030050001941c441c14101400b6841400400c4004d03140740140e0605010f07422454000c0c450a94030700030721850ac44003404072203003044104101c1c1d8982c00054140d00c022500300303801d0780c1f1102d00b040c64144100f0351403c80722280d103800442703422a0300740f032406d465005940c08078818100c580034014900c14030114044130030504041210b00c1c079000028100030414442c1d468007642030016 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 142830755 1250 142829505 142829513
    0xf0e060d1e11180103050f010e0715031e0b090108010e0d0e120a03080406050f070504060804020a1a0706050112050a030c14100c030b1e100e040203090705031002030121 74
    0x403410300b5402c000d0001444607400398045600d60b10034403007604c5602c243e03c1c250a001c5810710500e002039101e000903010060030b20a450000303146600c0a0010103503110a120710315100d00712101c45d0f4040d40c0304041824500b0204101c20b0703010680040781564500461081b20040002d2039080b40c84540c14122500e10180c030000c3c800d600a040d201038140280980c071030030103074000b180da8840d03072062104004a4072404183c43c0c0c3c409003180c1803800700303808100a201441c0609440b5030f100e44020034a400711a11082c45003020300c41c0d42820400f42001044880402c01140140e40c05084105508495030030300e512090b60352241600050b0034070040045100034040000f4283c0354103c90382007118031050349000314a001304859001d110002e0324181005905181202195102c10010303001400f2500c01c6504001e9402ca42407918000d00081301a08005510ba500107584140d55440192a00c2132424080c036051a10081714949210b01c100014810040070081e5040400404101503010140500d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 142832005 1250 142830755 142830773
    0x1718010b030607200601030215030a15091b0507020604030605060a150c0606050f0907031802190302010e0d05060c03130803040605011517011802040f0f0e060d1e 71
    0x60310341d00340c0282c00c2000640d58000495280c91800c4000d000c0e58248034419042d114002804000d50120240998440e4800c0240c0071303540003400c001001032500c540c004070394030010665010400884c1c440e068400340d0341469148110400f0103080c403502d41407081c0d0019152388100e0000030485035440c0003003107403500c803001d0542c060600e0110a1886100741c0d08054405044110201e03611401c1490220b81c2c0e00305642e6180340040050b00720061a251168142c0280c84041c0708014094080d100060150f6614a8400c1e0340c0300352407114066050460000414050aa140550050301c085e1034040c0000e9002070717455404005075100503101e8982c0c0c800d800304d0030190440580b0055010041c08107101c85540f10170704980100880a4a10034072039015038400313400740d491701000c142c40e100410100102c40702c01c40e1401c6528400502e055182c0307401041c00700f100e40200c80c0010648009009004246c090550040d03070807550212000003554404004100841e820000c00c030206051100304110a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 142833255 1250 142832005 142832021
    0x50405130c1b030e1509010e0d06150308040311040c1211070c08030c011a060912150c040e1b040b13030507090209010810050f0603040c03170304050d171801 69
    0x4410072900021410002c00b02040031301c0c09807284402c420b010400c0082402160342910042c0c45400c0e1180c3c803030040159006102c2419150a621001c02c544464207288004000d58460400540c9842c114200903200300380d101c42e590300580c82c007420101180d4000007803e0b041404031201250f04110858209154028000c3c02801060740038030219841c000031002d84020710007100200300280c4808280101c0d41c20324006582c100704108031240c45410031001e030103d50308090080711003507544c103c503008801170225a0121200c80114051000300e0f071004030582c0001a83c2c0b51740800c43c8030150001da06210314861441c21420018001400e001200103070401503070082c040e01e80d107a59520b0b90b94013a60052403001d0014904200007111059024582401c3e45d00c045d0000003c92003000c14006954000742064030916104840080062a01c4001354042810714002d02e84030b040038038050303141000316001c1806004010b0b0301c56400a200e81d0070316600c041904984021402ca04a601d40149408 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 142834505 1250 142833255 142833287
    0x30103260d02120603010908040510030207080c011b090f060f030e07060908150907060c0203160303090521060a0510050303130e01050d05030702010327050a050d050405130c 76
    0xc581801072041a502601c0d180540c0440f025440d03551004060072107131080001401c040c02440f0610007410882a1a240d513202400c00614040c000d49801790340e42c001200d00409691a205525001d060302d020300402c41c002400d203070505904041c800c0307068086900820003040707102c848144c4024800d070070410508840c0703815a21596111980240b210301c003802110303014440c4503007021012200c0592035101d40650005015407034101342c000c503003500741030400740c5c0e251045010b101c180c0c0701d5404000c3d000318420745604a041e440c080501600c220b00c20a01489111110032212408101080c00c2e0340c021000c0303030b001400303545800c0c4000c0d01c001d845d0403058041c030000c603081d6208038500286000740c9403070001e0030b400c0343c0c0da6200300401d03030b00c070b03440010b140790818003a51005500903044030b8810768496510880500c602c000d051000340c402001543c490f0300031140c0105010b4103002c80101403006181180c03034207050a020482d811407a480390403115684041034200107200382e140034006514 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 142835755 1250 142834505 142834507
    0x3060d06091208160e0315040609082b020315010f120e1b12031606020f03040501050403170105030c220501080313080a020907081b0316080108011103010326 69
    0x360300c0c010121a401c5460b1202040d00740c44131a0f45a01610260502200050090041e40c08140344405441e102900850700300381c407003440c0710001d6695009021140340305005000207e02c2100c8491445584848a44902d481001400500581c40545c090403c1c407e013094000c0381010041200c041d40d12401100c012031801c20030300040080030a201d10303400f8004076040300c14001901042009078003414070709115841041204001d00f00505c2c0d400c82103010354030043c1403d4000041c5519a401101c045a01f650745038100410944c016501c480c2440820764060103070b40c144404079680d107480b0584a84a210310b10800384414400051204140700e0b0042c0a009550350b030156180e0342d4010005030f0600401149001c070310344000095840b50710f0340041c48200c241c0c581480907101c110015042581c1000c0121f00e00c084000c0f21030007107000d20700300303c07000b142100300110040030541c040e000001280d0412001090282640003030300d056903040403e02d08a0700310002c03014070210390317480745941c0070304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 142837005 1250 142835755 142835783
    0xf03010c050c010b030d0903030f0e030d090503100b0f0607020411040609080607050c12160204060609050112050103020d031404030606030809130231180b0a061403060d0609 76
    0x507011001d0480e10a0b0b0308003d125844800c000c05841d1203c0c00c5008000442003c001c00c0840e00c00c141d403643da0030300303802c040d000c265485c4080b03800e000207100884042464440f0070419410100030700c03803020b00145400c008100042d00081d114411380302c100d622800000c1a40001e540d03d680c010041a03d180b501155256904c00001c1c1010a440c03141103114001c0c6c20000d2001030007402210030222202028015603005074a1450281d04a0300c103141c42100d40c4140e00005841c1c5226601c09007215841d0401c1c1c1da45410001414907120ba800038210706e04010041005803503c0e075161510950505003a020100030134104078030ba0103150300251086042000c00828405480b00401c1c1d0010181e8220b04102c50506c00b20080c0e01c943c8020580b40640c140480124450041420151a0016480e640151703a92515048006d100e4000d080c2e000e0741e10319020314a031a0001000c40200080e051180c659102c11003ca0b881e400002c001c6801003501e882e0b450100b00d00381d800701b601780d50702c400007000841c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 142838255 1250 142837005 142837007
    0x10204090f06030204050609040c15051207020114060307120605060103141810181104062d14010f0c05032b051f0b071509210c0309030f020f03010c 65
    0x8606840164005c0b0b24240202ea0300b13040051140d8883d07030300100e03160581490002030705985020381140e0740c104007041c00724200400364520880e00800c10b9034004980c0300da03140381c50048424040d100a200740e00801c810090703e030f0881480ca41c6240c0107980010356640e4107006901900b81e00800c01003110482d02000510f00203468030304150344010041301e03110000c01c0082c208a822030608595091200451900040c2d20021207074051100030380041292a030301c0036440d102d82d07081d18444030348990060003418010f0500d189036008149100017a81018103120003e4070001c1051125001c101e40682c280341401003c00c02c54000b001500c01c1088940703000c1e449100d02003203001906c0038031030520001c954000d803005a441410440941d0020880340b8041c84200b081e48035210440d449103445070b850040103164401d83c4070090058210380c9440488600d50605e0088408094050020400060b00460351002c903143c1a2039002d45800d001d10240c0c000510312442c0036a80540c1076080030b4100d11f00d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 142839505 1250 142838255 142838261
    0x9031905040e0a05190b030c040f14060d0c0510111002040512070e060d02030c10050a090914040f081317070602010219180e101818080903010204090f 66
    0x242c0303031085481810b032034040a9030241d620589016000350002c82c110b0f618894554007000449100038203c585006001c00442c0544400c030741b02441d107560741c2030400b55821405e001158444412102c150341d00b4002c0d07076414120841400740302d024850703105031411224001d0513803c4a030780620084fd8006454040b0307650103507006000d1031340152241803800c4049080010300c4410f075103a00707031081c42d175507200c1081c069501c144401c00d9926200b541c00340403098940861100d01080e01d5500c00d961407114110142000b00b940d408824001c0c54049800000042c2c81c403240d030842d502441c203014561042c10410aa80202400441e2144d68002c000031302c50f044144484501c03034440181c404082e60b40105034200e002d00c4c0e0404100f0342000c07001d144031510443e9109000a075030340c00a10121348826000e02260405c076084408141d0066041c000d500783c1408810801c21074000a000124052a001d440d1701d000c190020004180801c030006142e41c2901a10090728215004111122040c01c0c21005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 142840755 1250 142839505 142839509
    0x80711060a15051c122703030206060d0c0e06040e16050102070906050a0e0901060b0d020703180602251203170f0417030a1803052208070303080903190504 68
    0x202d0800281c00042504080910004c0d00000400701e100409068950030f2070710802d030310244c04200880b0003071045050340d908980051202c0f04511500c01d4150714010703141600c058081442a401110030b00e0001e00528a698155200c3c04420740b5240c0b00d40380403401420724000741c80c14501030b508050040f4601c20101c2421a2000d81c201c1d2855581c0d44000405c60345280281500891800300c28000400c60194098000c6441c00c00040c040b6034840560380d0b6600401403500c1d01580006e03d2000340740c1e0006010383c0c010b9400c1c21a080707091500c04041c0d91000384000000b600e1701100711400401d000e8140d024000c0c644885c0058011400f413a0041c08142c40982c040100121640810780c038007110300c14035200396407040e1105000d00c0e038940c0302841a00000d15840010380c07180040c2000f24082a603103005070b407007034441d00d4580f038081c0d403900c602c80035030007101d0308e102007940c030400825000117080340880380c042c1410b00c210786400050038154454020095540645c818261024a51280080c41 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 142842005 1250 142840755 142840781
    0x60604060c0f0b0f1e01140105030402060f070c0311040c0504030f0c05040509070603060905060607150f11071103060402061b0106080d02030a0809070602070312051303060f0606020c0a06080711060a 87
    0x5d4069002c040b1140000400e0042d20b100c0420480702d1903055028a00564000340010056420a02c030010300d0790207548602400c5503400402201007040054210300354031106c41c2102c1c244202c003100d00d001483c41c00355120284c66000c107040100c003030003000003860300584000350080c000b91030460300140c0c3c0c0d000c1d41d00c13039000000d00d06a0700084d582990301c2190300503600101a06c0c58030b6000d8030f03440c2d00c18141e00c0c05080c401d99203035121501c10f4068440c540040080011180e210485418070b1410b184102c1501406600801c04000041c2d8a00e000c540d110041215224040080d03400d1450040000380c025401d0ba1085c49122440d143d0000082c200d60b0100b651080e44c9070382c44104054583e038030383c400ca001590106009000180d4082d1812101580d10314205081940c0b03803050452100050b442a82c03a5692655190002882400b698010304103a000a1002580f1000410000b214600c81c240800c5508804034809620400503200d443c8004000c8410034245665814001c1c00e402c85a40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 142843255 1250 142842005 142842031
    0x7021c02190611030403020916050f030f1005010810090e03040302040f020d0c090b03040305072a05090106020d0503190b120c1809150c04050d03110c09060604060c0f0b0f 75
    0x208200f60010440702626405000700760301d600c0302c100850004801c1c12861003484001e024181c1c143c51000c02551003010101620501030030f09207901641008150003a904000c0040c081020b140286d0100c20129981e050001508002081e002c40c01e40c081c1d604000e60050901e01904a00200c5401404901940c24010420b01d04624826610516103118100c0c41c44418000038020900030000b0b051031502030f03014408061660480a0020000181c40d400b45200410042c0020b080020865014240c3c40c001002d101504210160180c00300809061820b03e00aa407200042007a0b000079a5440e006030801c143c42074011920394031240740f010800e004280c8100b00034407080481c50014042c030b101101419600e4001020640d1510300100f150143c2035041100043c0c50712641c4d0b21004c0940280d5900c0c1b055003403010140e090006203c1d601e44503e003208240005ea40c3c1d480110b9080f03030700c0350601e8030082c03003546086008080040350103000c00c000b9508100001c0a0b040b0924407030080c501c414 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 142844505 1250 142843255 142843277
    0x50901050405061003020708041a03041406010602100b03070902120906060a050f0906030a0c0b0a03050906010b0a080702070504150e090f030d1e0609020c0d03020405030307021c021906 81
    0x301c4116503003120754540c00030140d403460841c80d000b030b4018021140145806490551900e5820b062032850762a03295032101c00204020901c0319080020340c0c00d05514004e4007695140040003551019003901c00d1019581d140d0104906507010425000100101c0780c080d504c0e500000c0c90706070361103011142d1124a020360340009081d8030306001005d00780c4d000103200006508031141400080700f03000300075030f0701740c8120002000821900081a4001c1084107e9030766101100e0303a00074203482010707040c0b0700385a2198005100540d030400948038028454034101417142c1d10709204074a0a0300075440756030014070b0041c2c0ca1900c2180d24020109403030701c181c44e03040503813192428907540c1d08003420401840d4009001c0800004104d810a15a000d110410200c1180707840e0325002c1101ca00da031210541980c00600301c80494003d101901e2040c2c01d0703040c1182024034110120b5140e20911400a02c54907480c1d103820700c440301c96000c0000b420b401500000b050800d801040b40500c03001d00450300803807569408 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 142845755 1250 142844505 142844509
    0xf050309030a03020d0b090c031012021302070302071e0611030702010c110303041d0702010c080112060f06150c0308010504091e0f0b040c0e0a02030c18060f040303080105090105 78
    0x85900400340140114505098030360210000d4024044401459468050308002581d131000e01c42e000c0c1414032180c6c3d50b00e003450385000c0d00344a656407081d0071060942000c0c50240e81e4400410012580b02180540d07201c00c07624040b402d01c149900708601059030041000c5032640782081ca40e0030340301e136502c450184d00304d00021181e59005540c402070006000b4114180015622910302c00041d0018080b42d007015103034420028100c204002040742200f280301041606035090081445088080c1800220340d414441d0090486410140180c945900c6400c81d0070a00f00e6a88400000d040c601c3c180e401100d60b0b290000c1068451180507400070740784100105140ca030a00c075045c007440e03201c26032030034558145480b5184846500400c1e241c0350b85042c0c541010036214070f803451195100d00122881c1c5810a07162800c40e07000503000c001d00610600812888007408400c0f0303490f91804034200c800f0000030740005980c03407049002c1c4000404020a0000405402c00c5005041c2d6800b2101c10a143ea21002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 142847005 1250 142845755 142845757
    0x6090c09060a0e0a0510030b040518151003080d05091501080a0b041b030804080d0e130e161721070308071101020f0a020d020d0905060d140109020304030f05 69
    0x4041603100c00200900b002c0c0c58060000900c00703040142507081c203580d070380000400d4040758000c16404652941c010080519181c8101c9030b0044d1000c0c0d10b1a20300070040700c1c0a964680c0440040d060010010218803007400c3c04006c81c000355070062820b60760310000010782000d040141c504180324030408502140003176801c2484d60680e06814001c0000769041e40b00c1900003e0081e0050329000700c10421300c61081c00c0201648040c6010b490402d50f92858200c0d50782c60810104081e804201d05000e80c20300030340d0350310b01700092512511804201c080c03110107000e00f070900d5504d500ea81754502c00300005a002c0c040b2070400d4014001006d841d40079440000001403105001140050709108200450003c5c1c09200c8050b00003c031440c02a000c4034218140600b20303441544001d013521400318803071000302e81c1084030743c41c3d12003544040c0c064000d06a42c003034111255170140344e1040802251116603c002d5500655074405a11074500155a562044000a5200743c80a8001551481c8031821702d6000380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 142848255 1250 142847005 142847017
    0x61302120616180513150602031c020918070816050f0a140c0102121b09090127060906050a2301080705090d050607180b04030f0c030c0303050306090c 66
    0x410042d504001d88800702e40c100d110540c4800b00c0c070110140410030703441d045202000606429400107003a151445a41d0034031090764428070441d802005a03220003100300340e07641c0b24204441c101580315899030300052080342c400490741d89117135407207400c0052090380054000d009210109078001c60b500d400000301c4452191400044400d072040240041c801c0c40742c1d019009000d00011006d040100000000c0d007a030380125551410082d0315001c0c0038000080c40700d01020b452200070510314050240000c29007006052080c00c01441810703101441c02d02c079542101d0450302c01074808005940d26000700c4002000c080c008c083c080d900f00306021500414096140c07100c220011740c1600884000e03401160503050080c41c40301001400c0c0450685610380016134000c0304c1c440c1001d4031080c82d1905008020400011140b4bc510700710400c01c008504654080340c00307694104613540600340721420404040d26040d070000f8030702c402c2900d001040c590301c0800740d402040c0480346609251981c00000c1e006008070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 142849505 1250 142848255 142848271
    0x30e040c03020f03040803180303010e07090f03050c090a020d150806181b0117240102030f0a030b0d050601150201050c03060915131104051815090a06080613021206 72
    0x1040405d02198544000d5603001c8404001c1c121440703440503280e4110741081c0d100c01d210390300d002c05102150782c216004202500d14484020086490360720f84a41c0d440705490003d0107800f03007002261513040c182d01180d0b40c8001d240380600480307030014140404108075225540d894018207007c0f4401190180e4202442c108000c014003904901210780420342954582240c103015080c070b10310303800407080c41e102c074499010304000030a0700c540b00d41a030310a806284403180c11074000301300204155401c041940e2028100d4507002603e4034802e00030030102202d490b0082c0c85441080300004110105010044c0311180643c000e101c10384403c0d800d0080e45c00144e503030341e921802040025078050aa0040012880802401d400d03500320440251012105070020f60780034170400050505c11400c204400305c14038124070300841d0181c6801760b410003441d05e900d01c106128a4035000890584082c0d41c010300080c2003818190750b83e50504c0a82d90303824100c290000c030f000e001d0804d0b81015490010a61074420940 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 142850755 1250 142849505 142849507
    0x60f060c02062d0306240a050d02090604031b09060305030406030b03031b07140102070e070302070f06020301090203250807030209041d030c071e03081b0a030e040c03020f 75
    0x4640c01c200300c64200c030310f000e100300e0358070b00d881040d00600d5003203452600c860022140c3d49081a400380b0048088606c0310900c809400703401a80302440c080100e5840c0d02843c5001c546589003089610080e201749011036502c0040820f0200c140003c1c100018126000d1000b003104065950203803400b03541300c40c48081c0c2541c2081c081085018080e8210351049040101960300e0800e00f2540ca4188040700c0e894a4100e80c0004001c2c00804800464580c02400c240001e210742d502c0e005024400d110001c2c514410941c0115400c0100b10040d401c1086e115031180056442c1d60b144c3e05510025001110303405681900d21100307060540e0115440c4041c1110703070b038071000d45540701d01e02900a540030003021a0004c0d40c5102d1400009401d2450b20259402400a1540c0d40d10340c0f2106841c206083d005560502c2c1c0420034070114164030034040e01142d5000222507111680c1c2c10101c49d2507103540006241070300441d2540d030300700341e8445084862401301300d600304413071a98510100e04a0250110619200b00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 142852005 1250 142850755 142850777
    0x18050706080a09150903080a140a090f080304120806060703021009020f03010204090923071202040f0507030207020a0608011d1305150403030614090f09010608010606020709060f06 79
    0x1c41001026441980c2d50300c0416240e049507a180000000400003420f030360742d510b0300e80e0304142d407014181d900000c0c5554248075500d40d5444c84142d50f400a0711121000d543c0d91228001c201c0543c400003c1150402c05c0e1a8032883c0138201080424403a80000c0c2c000b0301000c4c0002c0303d0785030101c00d80c2c90040c1c05600034140d100c1208540001080310038010780c0d1100c944000d41c609030350f090000380041c06c000e20000c03401c0c5034a4039040722440c592070101400702c0f16280c1c1c0c00140d0000000c08030212160540c0f218240e2000c1e00104008101e44201c0071010b9040108000b20a6055002801c0a610940781800080e5035080100c0f4190300170b02801c024107403400140d0319052440190303540c2001a0003000d083e00640caa998034a031070b954464880ca0041d07004200403d16405101c0c00004142c514012449511420001001d5481c000e180360400e000000c04901101c01c02d43c0720601614024000304000c40d200d078006903940f080b0b0b201c4da0900600301400030552100c081c1818040703171026100d00c0c040c01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 142853255 1250 142852005 142852007
    0x60203040b1c0905120a031a150a030e03070b010302010e0301050103051011040806070819020915250b061513050609010c0b07051b0a02030c010e0d0f060e0118050706 73
    0x600166410b1040d02d0f19200410b01298043c0320b061254040f2161407139541c0300c003890143c1503a404003c88001c1030001403154940703031034440c00c81c250764071903c40d102c0e40c4140c440700a80041280031034500680c0301c082812404c11a0a00206068a0003600c1e2030b854054038008050981c1c5090100902c2c030f8000d034090700320003c0181c0003403580a4000350560b0819403140e85d401c0c9014000c40310840081d041d90180150030488081d4031200144508081d49084c0114011410103104230003040d1b8202d1000a45055002c04030f440740d01c0e41c0d9402c0e550100340094038200030504c86010b68415100e080c519031003429003101c0b80100d8a14443c0142001d851900d008100a11a000700340d280341800081c080c0e4100080c241c03040c06101c1d034825107031545c8840440d07104444281c0c1f1003d00c01d8480d4018a007032400341c0c1d800075030ba80740c84a0910301041e1010107400420b14803100c800f401050398001e00030350402c214140d04800000d5a20383c0003000b41d072106a08600035001c0940028040b0b41003480140300003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 142854505 1250 142853255 142853287
    0x50415030201200109110411041203080709050d1401050c0a0801030b0603011103100603060609030b04060e0f0304141305010f0e040620090301050c13050613030b0903030f01060203040b 81
    0x3c212002000d200c80030100601500351000c1040486525503000b0707403c140c91901c0d00c560701601c030504401c10304050a2503a000303003d203404c08000c0c081c0030b00000000c000c0b6100d0354480c0301900e805804034104100178900100305043c90440da4030a07500b8000024814290201500d015158655560b40b0a0b4a15100d250094401400240e01952a00401c00369486000011405000360141d16540c044c90440000c3c2240c985400810030803110142c100b0204160414403604107401c1080003600b00120410507203080b44200d426522400040750020318680d055441c00081c0c0310585480d9a1084918200c1c030071680c003400b0340c50340144c000c0420300400c12880d00781c40d882849007100203050910b203074180c144142d00180c4141e20003400181741809040038040d640d0403031a0000d0361400d003064050302d01981805406141d001d6070001c03807900548128001160011500401110302d2810f1881040b40c490340100ca002c10180e010300000030301c1c284000200c50454802d05030f100d06000740f618840d084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 142855755 1250 142854505 142854527
    0x12060901110316121d07080705030703120503060f0901060509040e06070203340c0306230109090c0f2402030f0f0315030d02070f0e090c040c0c06050a09030306050415030201 76
    0x4469865041245c0c19005201c1805c03000c2c404c80042c17609034a4030710a42d00d060060b13027001d4002d4100300b6041000540140b1040b410843c24102591a0703134807200880d8001e5110019035a10100110001503541e03044001069451402d0b2028001e10301800f2076140d03a20f0064440000591003008145980401060f81a124122445c01086c0c3c01c1d035060310011070b10100440903036000400c03a0040081250314855101b50400f084030004d0f1034440100c610140080503c25225810345500e00c11040110081a120140090105810506490307280081000c6d01d44420108030403940d60f0022031003400041900c100d00b42d00c110803441d0503000312400d0141c0d000034011005010800c0001909030b54180080d038441181903000700381072490030307101801c0c09480703a20443c4001801410300a0f1282d011450b0410300000752404100310400002c1252022000f03000503154618100c18025400840d07040071a06901966083c00340984480070070048403038070003440042d040c0f5941e0400055025802140c0c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 142857005 1250 142855755 142855787
    0x201080c07060c03020d05090105060918070902030903091212071b0b0304030c020301200316050c030714070b0301050d02040b030f0f01020301090c02070806070302130512060901110316 81
    0xc1040740e03a81d10b5100303941c807051800c004650081002c040c00055031207a01d6101c98880700a10260610740c010031120303680a4203450702c01384074082c0e81c2c0c9400340070001c5e5030061003502070465407031815000307641c3c0729000340ca4414464060340c3c40388940180001540071840c40d0421040d803805555030f03906104107110840c49080c207a404807001038010150b00146101d90301a803a8850f2440480c410142141d5807608103114400649580c1c030000c01c10030341500e51060b1070000d41e44000903080710039901400713055081c0d901403000055282c20880c0343e03100012070751401c5c402c95202c140c071140c080019001c24051035402c500c038030101801521b46904000b10606014056a02c0100c0d120b410a0801c4040304241c01300f03039000001048032043c54868000380d011144040c09006017803840864030b40f10060121800c1640200760414490300c141e403498001c200c014040401c002e130340340695440300e80454841516500c0c090030000206003c1046904c0b61030701a20084020003003a200b51040320010442c81 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 142858255 1250 142857005 142857007
    0x72303070210020406020a110406060f030b0409051c0801080312070e0a05030706050c15010b0a08250c03020c04090201020c04020a050706020705030c0d0c020108280603030503090d090806040201080c 87
    0x1800e2030102d84010b00240110b54003400055115082945c804654030240c03e0050349030180400120b035018002344403070812803601042c02c145890018003d000131100191940c02409680764016500c5403d0311402c910755126942d0507030369000c0f140d880340245080c81c1c038190701d040c00041d940d511440b9035461f0413000409000c5201d88a8020078680710090b04410b000c01c4000401145484e41040f18032541502207040b829290305000707d4600b103015400042091001c4d038000700e9441d034186081c070000b078821149010010861003000501c83d0716111015009401084c031003030800d04160207810121b40d01030700148003c2c030302082440300a520416440c1c0c1040b40512082c00092040e000401b080d5005900540d110185200f26508060b01180844240718003c590303000180d13000b48116610201c412030b08000615036000c4200c8102406000080c1c2c1c1e45404804010107400a0255005c8c1640f10112008210109030659203611f80c0d0017070224603070107800094010344c881e2010f6a807282d1416816 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 142859505 1250 142858255 142858273
    0x501030308150a030213021201091a060304110111030706050a05040c06020f060412030b0603040501060311030312010902031506030a090606050d02030a11011b0b061005180d2301060305060723030702 87
    0x1004203030781c00b8ac00514440307485601c132818540b10b40400303040304802201c00a00c1c6d030401390307030305518501d00b40c0b181c1d810b104802c042010071301c0d4140140c517449500620300b840245400c1280100500c4102c4044414007400349002c1009480003400301c2d901540d00b0000d11158903140c452000f090006400d81b02019241d10b90803103240c07600c401442c0100d1142c0c00108940b41103151020303d800001b0b184a0103a4800d00950100a0300011741038110394148000613540e840304c0000801850015001c5138000500000348040011281e100c01c14140c01010300304070030340e2038138100a00301001c0d18010b0b5155020a8104011803c0300890030300d941030504281d40d540401c81d40949110002c4a829100c1800719020040b450910010b00e1000d40a14941180b500209c540c0601c520103100e1071003400380c115566540c0403c41e00300050f24000380201040144007813000289030192101d4001103400d0700506000c1407141d0301500030f9408226544000039089044000000d5071500010a5041140b06000360 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 142860755 1250 142859505 142859527
    0x30b03030d1406041d03040306020d060e0708060a0902030603031206040b0a1e0806010501050d020a0309060e0318060a091509030609031706030a030f140702040f0501030308150a03021302 82
    0xd05180101100200b011480e00c00c080004039410320081711411002441049013032000401101c0699901510041c0c4550346808914010502da0304041c911060201c01d101c01c00c1d03041010280b007840c4c2111815075060310b1303e05560a0340800c1c0c0d04540c16034011310404080c05080c0b15410f034004c80280000815280718000122614030951014800e0110046808002d01d11441c0c0c0d07001601540300180070b10351520000800511a4401107001e196020883c7d03100300340f00303411001c003464000394103000e00544507008a89035400800c0d00c6424008801c8452881c0c00d011054450240303c40e260b072150140342100c0303801000d4100b031000b4104820380c0c4000c0005074035880340d0704034180299a501c101d2101c4181000003880046e082078031a920600683c00040e03031021445860a200b841e00726149400001c0301c40e40e9000300c1034002e502c2030030070400c070740d03000411f80c0064102e9000303550311800394070703924200000c450261030700e16003080d0303e51018000b50529890984d1005a5044014601064042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 142862005 1250 142860755 142860761
    0x30d020703030903020f0f0d0822030e0f090114040b0111010903081501110d0f20030904050c1303020405040f0219080c04020406021506180c0403020a090b01020a03030b03030d 77
    0x30114046660303202d00900345641000315007100701c528001440c66841e00612203584a003440030300b06c00c21625000184088002c64060f910801d4400d801b0361108110b840e002d040240302010043c0146e100040510b818a440313007855040b030340019103c081e90b20b0b04209000107440060304940c1405071036409901d00580034804d05100c240260b55400307803400c01e030200642c070004001c020307410044c000008508100f80400c00a0100031142800000309141c04400d0341d800c07d01e52091b001c07600b0401c03c1200081310100c0142600d890464041219a0700c403a011032850003070765402800c82502e00300074001030619500454001c1d008407040a0052007030742c000f603010140000d070111400384200b41080300c0c1c10104481d841c04601214103500301400c0050082d07440a80809a45410008c0e4022407400c4d01c4000410145a0141d8150180e61410790101d1405901c10f02c81240100700540c40041c084649208001049130141d0181a8541d595102180982040500140e26000411410744042010701c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 142863255 1250 142862005 142862017
    0x4021005072a050d0308160306050307080709050703060305030712020102040308030a0c0e03010b030a0308060a091104060e010f051602041401062115031416090519091106070203030d02 81
    0x3015146804650100561042c0c4164001d070b0080300d035010300800090308446540c0d4004c2e01ca030034119400300e01c200220007400aa50109801d80601640440c00c0b106c0420100b060b5003101c030013400740307031602c6c41e040301120300f00c0c40081c0054005000c03000c00580c800101501e100300c0c6100241c01c1544a03140d04510368015116040c14941e07132048002115000324400c820904128020801e075511031001c6134441400e5a1b00404003c080c000140f04c0380d84a5120b40c0c068098500100204245880d40320003d40c4a8099603000c034074903c41c10a0113603c01c00381c82840f4407003551058107103a04507400c4dc18503824084105ea00c50b440d0130102e04181c002140c05c40c000d241650303805803000e42480c0245400100920030f07030034050403c45447c007060120078220049079030003c2d008600c603002041a9060281070300360700d02c55109072000016200311a4200c50b005004010030b0350300903010000d041044804624005040403042c1100e60081c0c035240e009000c60038005003d40b4500b030070a41809040360301903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 142864505 1250 142863255 142863293
    0x115021f0e1b01020d03050403120209150309030c070e16030b060702030f03091009150c021305040b04020f03030a120b0607050a44070c1511060c0901080402100507 72
    0x3080160102e90f038100028040d442c2a424100b02c00d0825450090000288100300d403503a54001500702165140c20441c440340c0c43c0b105000d6516404c0140d525501d9601025407583d003441803001c041581c0106014850140303020325240d90340710503182400ea0140010058640e0300c070205000d50409a1010700c01e0707801c82d030684800303913644d440e43c402002046503400f0103120400032210014441103000048400120099050050482416100140822412900400840741000c00f448200020510050700640c801c41da1074a403000c031003051590b03d018599000340092041b00e10004003000c0c0b940304400c6584050003542c44c244075a180e007464104800b4003107071340d1444201018511480012a038906d03440b5603200744a1030300036108a03241c0c0000004080040c200008401080200303050102000340044102c22400717001d40500984919902500700710710703004203400113200b2a9000c0c203c0d05901170507100d0401a4890760244501c2420403206c89042c00810005a8041400c00424503890070030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 142865755 1250 142864505 142864543
    0x20c09061816020f01060b04030807051e030301050a1d0f04051207080c0111070804090b0f040903030506180702070608060a091407021009020d0f0f0c090b03060115021f0e 75
    0x14442c4001e10f800500180804a80d142840901c142e07040d4000b120112600700310b00c0354444515003020380c28451401e040c520310040591407209141e20110207103049a800719050070003580d503401d5900d940251004041c0b00c568017200010300e500c1d03500740c00701d4100307005104441c1c002014016503180d42d0302c1004203549d030310380204a11101030801d014507240d60821210b030900b08003041da030386181801580a00c2d4840c07622400344d1400b5440b20340740c00040e072400500500200f102424040d00508003a0b800b107000c2e05481008241303000710349070151700440e042d81c0100221403074500c0c221030005015181980c000c59000703001406505500071014029103900013400303141000d0001a24003c4040c5440b20142c1c10651781d9030143c0d4500350075402e41a0030046001da10301c0d252605105104c105140246540d80460300483d215040c1c1d0310100c081360717043c0c04898250b40c0310800d8a030203003004d0042c034005038001c4da040c03100c180c4190b0400e00c0819200c0c50201d195000f0b03001c95814815221403107040154 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 142867005 1250 142865755 142865791
    0xe04030c1e021e032109041401050910080c1c0206131d01030305120402030a05010c0302030604060b09060405100c050609100f050906010b130f03060509010501080607020c090618 78
    0x103000b0001011112000070f410045404600101e43c4400e07044c1c400c00e155801c48000c1081404120b000c581c25604010810004950f00102102c40c14000303009042c0100700314070001b0a01040c0048080036101082e00030301ea5031545a080200381c3e600d11680305c05846410b0380f100e0058035001c010301071110789405502102410281182030b142d0901000700540d091304c100400200340c00004469500c00d5410340c44072240e0710340c000b02e031520320600304c010140d42ca0500c0584100d40c0c154040c5008060403203040c8402c44d0303500481411070195105980c0d006804200c02c004600d40500400c1e00200f041c10700c180107030320300d8840c0c504103070003100e280b4459004038250a0003201c0d24402e800010f0100181000740d410101c0d91a56a16014003810503006000541003000b424031404650082c00056441d02c01540c50380740c80c07009810140c0c1c2d4500203600b000d00124402c1804102036202d0050360b4014601a8100c000700002c0c2400070b41480d410000075a40442d10100f041c00c03080c4286005104002c03010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 142868255 1250 142867005 142867009
    0xf03080a08090a0f061512052518050604200309060a06030f030807091502010e160b070f061104080a150c0c2402040f031401020a0503010e04030c1e02 66
    0x5800206401401c0d048501c107a0b000420344010580c00f140c100c3c20014030405464804041c2c8809604103a15825035180040304200000030000001c1e6400d40d4889d0b4103665002c910102105103004003000d98424505c2100f00034000c1e4451070388890010008034656149010000c032070106001c20211b069800010080c004004000300c03038020381c445c00100422841e64407020003000e824140101004121008245150700c034510080151840e00b200c030146944d00d10001e0b00800d0340341ca0f103814070b0244003032040c2400c2e00c10368a0f10441701003e01440c9010419920b1001d81c40c0b4405080318441e9482407198aa4180701c4042c101900140d0000d2580002c5414a030350703950390b400d1100d004c55080241100480d5800340307200890652020990b0b401d440751400400341140e05030b5808040d00d04c00701d0700013020310700d80c0f4071071085030f00540408840d0303c0a40b00b91803d0f0321481c240c070004a0030030001009074140d4aa186503002c0d000f498008140c40507a0f999000c4001203260302008071805034100001e41c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 142869505 1250 142868255 142868267
    0x90f03020f151306020702040e01150302090a1a09040501060b1c0e0601080c06090409050a0309050a0f06080c09030a05160513061203110f06041a0f040f02190f03080a 73
    0x903005502c0426501d00c0d00400c42c42107041440f00041c4515000300f21101151500d030030441018010380001c4c452103054062146d455040f61106a1190a003800480d00600e854801c44458200b050410034102c113000003848074410000d072003112190f503194030000d01c40c00990041e1601802e5050200080c1207084100d205035801810010034642050b001040350003000035500051090a8880701d4a17480200b00044c002c0000340d002400030700a0311804404c241d88154240d06a500440745030204030703183d40014415002d41c3c0540004591a180410320002c8904054440140d0003801c0b610012851798859040c09002c0c0040c07000e0840c0414284558a007551180c00400407500c400c00c049440c1c800c50041010100d00003a05100c8281281c0c01c2c44181800300a01400307103002240e0b800e0400b813505200114400058102600c0008042020741218050160146c1d801594464044903075400700074100a10245c025031540c00d80704001500c1c0d0303e00150100841c010ba00b0b140d140c0b602808040d0803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 142870755 1250 142869505 142869523
    0x406050415031a010807090b0408060a0c3006030510060906052d030a05031215010305070509010819090606140906060d020a0e1c030e060f0a12090f03020f 68
    0x289400c007800407580c0703c40c1d8502003080c00802d18008096440d0b1540550f00e954080d00904010720300060007140c00b181c000303000e40c05000c518a0030421041742000850354005454a180d005182c0380c515880c40c0e041d00c201140c0e140b00421000200c80340d5942c0c941d031034140741081100300a42c403000104004451403140d0002490191100c19084011503003006c0c0304040c035840700c400496400e013480b0245e201001307101c0f14aa4072030304a07581c54070109403c0c0c00885c02195140303040c1741c00c035500c40c406501c04c1c00741a01810003a00d6160500300b00d0001960070700001000d9409060b032050711640000c4403801041242401280005074960610400318080c883d001002e03401041d9450a0094a80310b400886490b074003070501c010b84424010008807140e80d16820002c3c0e000e09000078503201170312910041d0030700510a80760036078034408070014003c05000313a9800c2c91140900f402242151402050100b150f07405080d00003901c0025981d0703082c2c08014a00d01540141e2002c60031203080d1104014203c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 142872005 1250 142870755 142870757
    0xb071b0e090607110c120c090106120608030f030402100315060521060603060607050106080607030b0907090303120f180303020a140702030703021e130c0207050405040209041b0306020406050415 85
    0x813800324012803580c07400f0168089020310451602c4c0c0628820a029a00144200800464182d651018018065a0309900c100c04191809800080e646000412100d001d0754040d501411661183c081000d944840e00101040c5074543c00411110103000c5210800303400540c4a840e222142c4c450310010104500c03003501352005140b414401c4540d5000180e0b98045000c82c1c8003961058145003031070240119a202400ca4403409050103002601604042005107054452180c00e5032042d40c1102d00324079030312000c0d010900315034007032092840c2500081107242424802103517031520201000081c00c0c07582c0c000c0e800290b02107401c4c00b0310761348810390300c2441c100b46d0010341c1041c006400007a20b8505c9131000900c42c1c6600701e040304100c0c80f42d681407559410000c220034814102030140c14050a0b1500350314005000d2510042800d24051041a00854000e80501a55503035551600010600400d40c8000103013203420000005443e070000300054400703a521541c48a00d071140b00b1b00681801d800f070300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 142873255 1250 142872005 142872017
    0x90f010c020316080703020f0706030b100203090d11180a05060a050307061202031e161103120103120509090703140c030601080f0606040503010c020f16030b010b071b0e090607 77
    0x24112880f5072958420007500304c60660b81e1035425103816841c020414146240da8080c2100015561b5007651144400510945076040e1016200a00f283c50380b041d45c2e2895030280c0c0d155601e80102e03070490800c502c80c01c8060078480c2c1401882c480481c0401007120303400800364030b40c8104845820241a07402c01400c040d0700400e41c26060075405000c20083c0710070450402e0707002c00000c650717182220ba681482c0b0b019844410207400c000f84429501b5010000000109000d02651000c20600008842082442104968080e42940c0c0c846520700c05a00e14001080300502501c03803503650340180c03a0f0044000d41c400007071101e01d00c070011164420003400c2c0e0501003c11300801c681d81e600880783c258000d0ad41c58142c500340c0d40d5000092003600950308815010340c0b17002050a9016000a040c80250240f2401c441c41894491006440c000d00f500000b403040c4d040500400c03548a40002a00c0d13014455943c6d1070301407003411391541d110001907014190280918051028080342808225008a0b5a281c60 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 142874505 1250 142873255 142873267
    0x3130e040807080702060904092102030301270e03030106090815011202040207050a1e060e060402010c14010609140106030e0d1d0a03200a06030e060105010302031806090f010c0203 79
    0x1441d190b0190003009458031000040c1078045569420481e241c10100800c01c2210014504080c090a0201070400b1900101400c2225074079000005490489240446020003510803a801101e0a0807a148258040ba1a0240c0e26903801d0240041c1d8042d0940e5a140040b05250685071850096003e10501141c58031500500c58240041c0030801025010b550242e600e90180c03410300e00e00a400b88025100c80c00411240740340704d92016052100d1030241a0a019510b800081c1d1a11074400b660000d000c1189c200040b0b00245000302142160780301c002c00064003558442c40001924a5815050040c0003a0b0005100c4590940314845070340381007800401404031b00000c0034000b000d41616095031082951003405990340d40070008030246503c02e2042e8010007094203203d1640ea10311400e144200c42070382000c2400351080c401c000e0050b08000c020500707a4a8034005400942c000780c00c90759404185803c116801c9010042940a0f000a030001c18415210001c05421190040a5141190001c01c10 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 142875755 1250 142874505 142874513
    0x1620031903090302060c0c09071d0102061e0c0d05100303032403020919020d05010311091608180a030e040b01030209130b0d05100b130c0f0804020112090503130e04 72
    0x16000d4a605403450b0341d03030702e19180f02ca510300120b0501d100e42c407980740c404109d000799210f414004055942100307030f00190102030059856600c200d807a48080741082060300302040e031380000103400404850f041840d1000c6605444161501140e82000329103040320108100b550501c502031003a80108203030313100720004400c0c01000b04e0b501c1c07001038401c440100204104504200c0c49210091400300115036030444d80180b440600000d2100381c402c0124101c51890700d0034103402c0e680c41000a200010500e5190500c15180a40040c1040d83d03000e00d4204035446541d010000690202d00980700c11a403403400d4000c0105542c01581343d036040500601c400b09140c3c803a04100c4c0402e40402c0b40c082420205000450403e030400700000c0d1280c0304002094214101582c0040e00c1c2c110309a910b040c41d24504000f8100361144442c144000803040300076007500b98894035049400034414505142c95201c282c000005854802505613080d81000492001561503054080b0040602859020213840c142d11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 142877005 1250 142875755 142875767
    0x1703010e010621090206040803040306090c080f030a0503090a020604030302011d010c02070b0c0102160b04050705030105060d020d02010e090108012a08060621040b0601030b0a03020f01051620031903 87
    0x340003c2d20640315000710003156241400da038050304600c002c45e0740305c6903039003400030240690020944030003101c40c3d0045141400072660380c3c03035003522000440c03920b04424411034255200408150050052980c1d450059403500014001980654008581c41d1601c7c1e190130028001c40c540740074280e1420302e000d08a0343d004904034040340c0540d0000340c0c6880b0644115406403052800d0b01071812400e020240410095001c5103010f54040c4003141e0401d61108141401ca6000ba11070a6200580c200320400514103590600308080c810b02d001e1400207d460080b070400d0f0001e80181016944910944c2c283c18505c180090a07141600ca007100013540c0c01c0d9010b040541c016001d02c1c0116400034070001070f1701170030300c911414056080c00c011b210b00e006d00380400d80311800d0b11114000782c140390110b030340c9150070b0301d2030801d0320b800411480b40701040a0043d80c1c164460050302d042c0c022106030701000f10f9414403110041260140d901d1002201e11000c0505258032000c401c4d150420401444000c81d6103c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 142878255 1250 142877005 142877057
    0x30403110f010b03120c011503120212030601080f190c03051605040302060a0f02031603180608150105180916080610090b090406030506132d02040b0105071703010e0106 74
    0x98903190790300c5d0962141b6001d0494450070107600500c02d00c0c00401c0120200c0d20490b580c40990036241540c0c0c400500c01c0940c4420303a1554001400003001c194180d503540c10413030308501300c80f071804d1900030103100d0101030310078070000d08000c290384104102c1c50400b0031886014500040c0740041c9800c0c1984d0008100f4001c03c0c01c00300030420b80303550860700e19000700308852108050410030701450440c0c5c87d0040c071454aa640450081c4d101030000540c503402086180e0061901c3d06c40701a007904405e004507183d0f088648641e1102e0070461070b40e4002d4071002c0005004805002d2080301111005d4009044d07100c01a000b140102d003c1065024460f42c0b02d8070b00d50a507003244407201e0352600c0340350028005e8013564102030024011503007030101020b04000c44c07070300c0c0c684541c0718610620841d00000c0300208080451060041d0740340e80710001841d080d44100030130b68050408900780043ca858000107d40320309846038651a000005008128510300044d004040c1d500d003e10410404400c03100c00c1c203904c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 142879505 1250 142878255 142878283
    0x3040609060905030c0d02010b0d030c1202030912031206060a080406110415020d03150807050402130e0c040e13021005031e0702032203170c01020c0102030403110f010b03 75
    0x10362122010460036410800c4010740200441c2d0f280c0184092094880d0288004100590b1a010355444a4202044d050f181260907468002c20800240c64541800300d020342d148046000030041c0010301e690350040380b40d6504011008548030504040852a0140040c003c40e01c9054188401c55200c0d81c0304022540c05075002e000428030701c1006400001900498008948000c04e404025010a40c000350942070740d96555018050f5020400c56043c0c03901041c014050584c22090341840181003d40051001040745a40c03540183e5a0b040310054000042d034050301c01c46c80001b070811601915034007540d0400c82034009101c0c1e40103a0380c001520004403040c48014003401000080b83c4803428410440c00c00503c14000400789095500252282c1c4444110a00014184421203200c880b5801c1710040d25442350030300c2600302c0e01c1d804601c10f81d048040350f03030490341d020405074071020401c0c00a1402244240c44030f08030040d85409250400ca40ea1072503420980c0f51100f80309950750001890b21043c419 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 142880755 1250 142879505 142879511
    0x60301030c120804030807030c0b060a0b0a03020901020f0304080d090b03060a030b070509090108160b130506090d06021809010b0a270905090a0201020607020d0c020103020d0f1a090a020f030406 85
    0x41c503d0001c209008640c0043d00c0e00b5000305260301810b400c081e5030310600340300341505661a43da40e010006406003038051500100c0042c000508040d020f54014900e50300305004562050b0b18000c105490360740aa048092140c0024084604890b0400035a00141c0b100700d00403070540c0740c5540410400100792001030000d1106001040c40c82e030040007111a16180542021001d6071a0414181d65082049038101c0f09581000e00251380d01594082e1070f0015011514001440d00d400d0400a09800441c100f41e848004600407070f0006040d0300c0101841091204038220100d02d007810040300c200140d014032000d1508001c6040150303400040c40040c141fa40c4080103c4046103600c098900800741c101d180114500000d101d03a55100141200d40075100b40e00300e40c1d0a40d42d00d64100c2e01c0e010030b40504000b00e00d1203201d180066000f03801404845910540005c3c148a00880b2401590340c07101c1d241040105441d0b140c401c0781414030308154000c0341d95005514104110001107a584001800544002c2da = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 142882005 1250 142880755 142880789
    0xe061e0d020f0402030a051b090108010512070806070e01090b09030a0209180f0703120e01140a0201230405010c0201021c150b04030506150103050f06041e110c0606060301030c 77
    0x1482a02600e0b0802c4058011034aa15107172016100a21040d0303480c10b6503030700d40190303000f09104070f2040700c1901d601a900d039003007640b0f0001401414440c1c11400301e4980100c903004640071360100022407041ca83c80d580c504440c40804005015190310340c00001010208101c1c60300340c0c0d10300241d10301c10b2542c182c8001480307070380b042800004094406203100480c0101c01c03148031028800a200010b503801440e90040c00c652003002600d500c0624207910340455407000c9000304100601001e000f800056000209905100000c000201da030b0300300c600c142070740d400c1c400d100c2805000d115886801d150750000710b28000c0307201c4038107403040342c84c4c219107529580f560404134049a40b55402402848034045090b10f6a88170b20707015444040440d0101d542040504450301c03158841d001c0c40303001d13111090803844542c48603400e11012304400400309802d00058240100c107800c1d81e11803030034034040e040040703901d030846e2046203800d00c83d0142610b840fa400a200600100d0f1741000c0c0710045950b00210111821 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 142883255 1250 142882005 142882009
    0xc110102122d0310120305070812010611010501230a090606020a14060105010c021c020a06020c0a1a03070e011407030915111b03120408070e061e0d02 66
    0x1911038074107104800e2010440641008a1000e807009039601e001c51807a000600c01c086080600089841c00c0e540708201c0800c01640d80c56407074403c090713800b1b40b81480c40d03d400c1d500e5408160740004041d0040c0301c04400104081ca520140200781424080c0090100d5450035071040c05d0b0100007403600902100002d056210fa43c0c1d40000364000703001110f801d200304c2d80d0b107070703006510740b004184141c44581127a442e1907195980450b1050513204140c590202c401d1890302072181c002c1c03d10700300c410b51003450f003d008003680d02c1501081c000c100310b071300070310410b140d240070f02541010b40e500000340c6080038504001d0027189401600d0380141286014180300c0505401207800c03180140c82c0414120000810406142d40003651500f550051490b60750018010074084559046040c1d01d8100e81e0803d0620100c0384e032001d031024902650080403a800c884130300c41041310300c6c1d1103680300e5452a80309540400010f0403442a0030340c0100110343c18108c17292000e0540c0d0500f03500b21002440340d040910210119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 142884505 1250 142883255 142883263
    0xb01020309030f03180d0503040905070306213e0102031308010204030204110906030a0515100809070503010b100c0309091113050307120b0603030903030703090f0b030103030c110102 80
    0x3030400207003110500f400800c1e04540302d62100415042c40b14150b00a4000c0e42880d503005640150320200851a0503e4051910020600940110201a00c40b0341c001030860307510000d400840a0201075040b07000f01450721031485035001594041000c211815200086245c401140c1c0c0c220300000700750145001c8800413811442944c8a00305072110035803010440e40c80560203402542e1084d282003210083d65001ca0000f80156151107902c0481040043e4044003260440703504900054081400030820f100000c1041c2c800e9076140e4001040b103400c101c0500400c0103880010300c415002000000d940d400425032500030078030b8a13010711100011f0704080511442c3d1020081941d100300b003002805850300b200b0542d00c600b582d10540c401c14a0301103010716000c5170362b408559151900b0400541155a0095050401010740b07515002c20f01c42c0d0466614248020401b40b4403aa58491070182012111400311481d81c001040b07003c814401400000c0d0815051803410f034200000a0001ca46c42e80100d10f0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 142885755 1250 142884505 142884517
    0x105030408090406030506010f09050f0c0a2003130b09100c0f0501051302091503030d0f020d0903030b0a060302040e0a0f2a110303061305060303161209081606030b010203 75
    0x1144ca884000402e210000c28024141e44500d00044c2400e80d94071910360075104e041e901d205041d10441e012403c48807100c4021b051000d1181001c40c7c0c0c5811054104200301c1c44032100490b00d4000280d0071400400d20700f107140191070f103841050306101c02c00c8007003a070b0000003c80b660288080710240c40140701c0991000d0340182c0c3d100009002528048484c0d01c4100b00e50101240140340ea0000310b4035080018815814507080a0000c60070090850307400c002a110440905840d503600300300060ba45ca600d1300404440c20301984002c11507070104401e011161101d68442d81c20184140004c0c440081079030442604600e2010002ca412103400c0c0c050070042000c0b41d100c2c0c44107114012214501c1404101c140c6004135903403259901001c01802c01174403480100c802c560701c0300d0660700710710301080235074810354110402404032405c0c119256242907043c031180360113840d1071442c000000c6c141c540c8118a80040c149000260101248412001c9403800e0300d07000710030070f254541540b1081640b00f082603403c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 142887005 1250 142885755 142885759
    0xe0118080a1701090f140402090402090a150b091206070507060b0a0b0d0b010f0201090503040302060f1204060e06060a0b090906060f1209010c09061d0102010f1103070206060a080309010503040809 86
    0x596503802d010b10040c0082d40440038042c3c101801103044032481b000b000d102c0c0e84c010b000e04145549550801000741e00040070b0750030b2036555820310041c184101300c1c810041c02980040365038602d1098200101c1751101f8040b0011507008004001095902900b80c031250b9911100104000d25840c00045104a442c0c0104d0f0001c4004100300d41c030191140c0040c00003400a8990341c51b01840c9140032401d0740c80084002c0c0c07203540704000400c01414041b00a0002143d242c0c102802d01b07005280d04100c1441c190341c2a101580c44001814880005001064000004071200c1c0001c03450421108010302510703512503c030b09403210015806403a500210303203010140c111110380d500d6210044640d0f80e0030941e4661201d41c42e2200000c01e05000765401030035900c480d1241c0d20200d00003c4070060010400400714115500d5081c0c0740701584c0d560261a420700c40d408181d070384915042e0700007490180003d200c148200020801000007030b60204c103c801f20b81c020b2a005e80d581c0c0d03c90400d6845403103165280e42d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 142888255 1250 142887005 142887047
    0x160c0504090605040303050f27010905060112060606031b0c020d0215130821070f0f2a0f0902090402071b18051005040e150705030a0e0118080a 63
    0x401004865840113200b0351207a1804c000a0704c5000408008900c1240d010041102c19a01074000c84009200136540d0200f4000115400c4601c0d9207036810a0384c00c0e8002c3d9a100c0c0749105000c204042070103000b0250850b4070781000003424500101446404c061007100620070017201240941d1034410400005a4000c0c01060b003d07200309185400c10392040c4000d002c0c501c014000407860311004558076400010b051340d4080501a808128941c545c0580800c071100c000c1d4000070780009004020707050b00d0a0051442c80c41041e041228a00b44540124201d83c81894030a02072103409107041e42c41d010340389010030045e144c0d0450804280244200b10000e802e40c0384201113403c00d840b00711080302c15201220035520b0300345214008103003620b10a80310700c507044800704010305c40307400c10794801511a80214120b5000714041c80062008400c16039400c00007403030020070406003098500400c0c6104283c2c1e0001c02800c6202c000c414840c2d115000700030682c1e000001c4250400e40b142e00070071b090703202044803d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 142889505 1250 142888255 142888271
    0x13140702030a091205030301090203100306180c0501081e0910020c070f0b180d030905090f041b06050d020a0513170c120d0309050f0f0703150c0203160c0504 69
    0x281d0307280c104240000c0010149a80801e0514080321441030150313000d0019030841c0d0070052101d000e0340009001540c0300c00107250000118080703028903501d0240c02594450300b10441d0070b284000f2000c0382c214606008030380050007107000100c1c18014003850300d07a00d1004a52168030f6aa400d02d1350512008581d1400850001100c820101d01d1804a030140b0781c06844580e13462407c000c0b01e002d9008401522000302d8204c0400e82004800c000940e813091600701e034065281c40005016a0060710500c0c5507000070b204000070810000c41500052403204c41582101e850003100820503c03500e514401038a0f004110080d465000b5000e03a40204100e558581c103058580d04080c0c409000076200300e56602c15131180617064105000301350204c04001d0042e020390740340c100e400c1d0043c240c00c0104440b54443c250031001c4d0540c0600c5500d03001c200a0b40a05041807a45c100303200740310660b03000d0140341843c0203000401603400004845024035440000d58802501d4208451005c02d10b600c000c1e04941403440c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 142890755 1250 142889505 142889507
    0xf0a0f060b1c0b0310020904060e15030d1b03050c010e06130c090b15031005060c0c010201050603011109090403120903030507030c0e0f01030902040612030203071205090a05131407 79
    0x35201c0d0a11108204641005494104041e83c0c8403607980398041d005551103c07014484c0e9001071248002c0a4408a8282d968200045021104a0341c3c3d28980b5240801340244e49410700c0456100965403030003400103404010840a025250310f0014184440060310620b40042034000d500180d10800684081c0d00e00b040a8a007c00c44060040790410070385140483c00a105201e51090088060700c1d1104803000032069a1a903813001d0010301700400b9400303000a0f550b03100c4000b000e0781f140c0e0602504040329200d0000e070940b94040d201078402d07410503280c454505203010543d030328050111445c5207140c0301d5060966240a03c20a005c40084c2441343c141e00b4150950441400380c0c943c4c2ea001c000c100760760b260456482502070803c4c0d5010001c0c042c044159032103070700900021400103000040c1c99a8a448404482c1d009500850140c0c0000c1540c1d014014035100140e004003660030030700e15261120b00010407095450083c40d02c505040311031a00540d03010340c00504018040500c40700d041c204210 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 142892005 1250 142890755 142890757
    0x50124090e2a01090807060f030c120f020904060605120a0c120213060e10021005090f030c010c0201050106110303010312110607032f1c0b0a06030507030506040e03030f0a0f060b 78
    0x2c00380440c900031800074003940d0028040080721200e6580034210b130346819085024024070240780c401c00c00072940192800d00a44241c4480c0700140c80016500c0c05a0424442a02d40a921410a0000600408410700088082180c1c0b02d44101000219001c201c0c50644114400c1015041c4441c400b182e503520b01c030180c00b171010650b130341900d81204801c401c00401001c84e08110517400142c109008911b1091a06e030000ea030440404010741c0d0000e10701000c824a160444a80411580e4660001074402602031203148c2c050021071500f41d5420203015400c40c0d40b480107106c01064441907003884002c19118034401204e01d850341041d00c0f10b600704050014040c1490050940e0141c1e410341e034402041c501c102c6401c4009000a0080d4141100900c0700456403550310150040c407070f2207400c130111075034400c080500034000d00d403000186414541c10044c00c448000b400240218036210303807801d8407840003041d240e016105151050395942c408114801404804c070031b4403480c1c0d080800200e0344c202104 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 142893255 1250 142892005 142892083
    0x6090d140405151e0406091a0702060712031d062e0608040501020906040e0609010608070c0b06030703020a03080a1206060e06090a080106141203070f021c0c09020304050124090e 78
    0x41c0c0b008c1440301c0c24610310001b8883d10300c00a41c0040200700c410000b031404682e1140c24101800c002506d00c881504070b0340b11030a0f001003c0042d4001d401008220000d0090907288400c107008410041c1414400d00310385803096008490520010100050400009404482c0c00090107000e441d104c0d43e45411100490304e023640d0389171003041d1410012403858403a6200520a0b030850f034400c03509008549038415059405404035404d401010808400b60f00c400264500071031054400307560b604480c20005240d003040d1880030aa0038140203080001076840700c5910040c02c41261102d40c0c2d40e20800005200343d0b90350748a10380950a2900000e4910760722003013a41034800542d00031a001290221072516840707070090040010541191250243c1000001c10b00038842142d0444c1008000351240340c1c86801c02d60000031180c0e000420041000800e010317200155103105000550500300c04140200d000076405050b02290307844888a03000e40f4104046040c2080e110785c1e0f02c141c1c1003890418070b4403003008 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 142894505 1250 142893255 142893269
    0x18121c0507170c090307030803070e0909030309120d0e0d0306090c110a060c0c0605090a0c0e0403090611010207020604080303060f0a080705012006090d140405151e040609 75
    0x604101d000c1c8185602c0c075a444214082d5079500c00100386416040903511a4040c41005000700c005045c1d14020341c00398101d134440e445030361460400c2000e8410011301030314464106000340041d500d0000b1b2031f540304143c503560303640c1c6850445440500600c009410104075104050303065800300d405504c00700666100e10000d000300c4403014010390b034080300309110311400e61003020280d0100b22a680810b001e01320500d84401070ba031403515268165001078a801030340341c100310030315003c20017610f8001e002000c400481c0c2440d464075803805800704005216500600c0045a00441e40031030079030403184107a9009020984603601c480120317035030390800c031142030081d01e480d000b110b40c0d45043d4500404a41c040d400a0003444c0c02c2c44011140b07600750034254100801d032501420350a10081c490350b48903a000c1c10082c070b081444264018181808801c0e0010750103000c0200f0300040e00c44007480c407a030601c011901e84c1c2e51100d0540e400002d400d00f40c0d0207861085c6c003180c04508144e002950204803102 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 142895755 1250 142894505 142894511
    0x2010c151b050405060d02070c030c03080a08011205030304020118051e04110705030313060f0c08040b0a050108071e03170309161d04020f03011107020102010e0708030318121c 77
    0x101290a903a01e1243d070082d141e100c1e005100e003c1d0407500c0d0f03400600380d462040c0a40d195080c0e40c0d548803015150a50400c5481d590041400b040c0c05070300003600c9004080c81801d10924005035218140c503840b0242c80a410402d00902c0c00071101c1c0c0103007084c00141400f41851441010400c0004903c09103002d009108038282928622140c0425050303502241c0c02002440c40c54403103000c2c0d86c840c080340d040c040f951240c407040711004903142c51203021070b03e0002d6141e09166150505c2c145040f410000d08001e1b01d140340100500401c000001c0000c16501c80c249107080c10100b590b24150290a941d00082c40245000500380190764480040d60140c42e80c60101c0e02040c80b440c240200e081214011a4100ca201084c42c1b02d4031040100542e4000d800608075900524003000460b0030368a00001c075624240d000111a4215642442091700e8003c07403130003408015040c003c22948912019010410f00c400c10040d1f00441e810a2240e00f05050007990103969a0300c0c90100c0390030200440b9035100074646 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 142897005 1250 142895755 142895801
    0x163e040b1002120c0109020402190f031e0e1005041b090504031d0609090108010614060315060304080d0e0d030c0e0307170c031e06010f1404050402010c15 68
    0x104280c09072a03209458010b0549010200211441500202a854520340d03c1c0c0d00e1040150f1a0f40c40144034200c107018030643c00510740d08015105200303d4100c0700406141c0002c24094010f081c09000c0041400613001c101c007503200f09180e2034110b49000664010b4034043c01e11003048211082092040566001b20740625034070040c0030100d820407200600850703076003290380c4406107141d804801c16500090041d403c2c090020089001244260800da100c2d07035440c50144420721200c1d201010800d0100c44d8070707280d454540d82400d4a802a081800d024010101c045000c01c0034030010b8401301030500c48104030248604843c10781e130b2041c40e21124040383c9406200d150881c41003055508500d0061f00620f4000e03e4000e2100b02c3d5440b8807180c90860207a50703100c00081e9014001d00400441c0d55208460391510700ba0701070304088060740a21340d95040386008000c00452020791364800101120005000da485000585000814201c000c24240071064269199800c0d9405541ca8844041c54601055 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 142898255 1250 142897005 142897009
    0x20c060c0f0d0539030c0708010509031c09060209030a080711092502030f0d02030103060b03030319020306030a0b0408070501240b0d0e010e03070611163e040b 70
    0x80300e440c592a41313200d0700728111008980905001ca4602d41d80000300c804100401c81014255000940100c0194128200802840b0024010184c018031098050b61a144500400b1020340844610840c4056200c400b08030074482035906031021480c6c054282ea2103a580d501c4d04014607804200d0031108042c1d080b0000784a810034210091250700c0403510146044514088000304114142a201c00c610040006e400d00010071001303001007504541e80940c99504514003c000d42d440540781501070b41c000c0c001c220340c0004040c040317017044181c3e020040e0360f61039900c04a801c100c01c501e8082e0444102d4803d1004114180000300700c0b00740140001c0010021495003c140001002410a44580001e0090006000302c50080c50b905041100020b1100018107140b802e490348450048441c0c0c1001c80c0c241d09000c56800b400c0141e00c0381300425850054921105040b0200c04903016090030301ca60010356001c020040d0712b4410303615624007100321002142c7e50700c0303126440d5003402e401181860700c050494 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 142899505 1250 142898255 142898257
    0x140c040e030726030c16050706020c15071109040609051507030e0616030c09121118010e0103060905032208010f051509040528061d0c0907020c060c0f0d05 68
    0xd1003061403e41d14540b141152041d20342c005a00500d1920303484600840022010400c07000142455000b0b0061401d00c602084888100e4a040c1c09115404104902c0003d0031031503101405401200c0300304182d16941000002851265002041ca00c01d80914030310b10f0490740200d52088200b683e00344030f18503003a502551959020380c0c24002400003120041e0045002e900054101f240d03524100e0711103aa10603c840e1003040401090314400300c50340e01000c0a050604a1010110201c1c0405200f03500d800280c180c4c01e94140f0018200643d00c0007107a0810a00b801140e010245040032010008103841846006000a2060f4a169841c0c0020346e007100d8154000c2c60300c07414610b10078600790304d5400d00340440150000e0048a41d4040c0c42002040d080c402c6030240d034a0203a40300c011440a06900d03010b03044a0032440f05007a01035100e10344100140000440046201058400e0459030b10340201c01e078079184540c002e007548010041204d01d444c400c00074400d4081464a07045510b0003100e0841038030b007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 142900755 1250 142899505 142899563
    0x3012606040b0c1c06140307030c141f08010503010e010b0102061b0f03071806030e2a03030726040509010b09030a1a060108070516140c040e0307 64
    0x140e8024100203404529403001c0d655006203000b6140703290078040785091008010b1818901c107190303900d2105124401c101d900c0c05e41c40040c240c00400c1c006007151038031700707204455205104d03141081c960780d0501501c490302d08640005c40b24010441c207090898010701001004d0042da0b000390f1038a840300340c40c0c441c140515a50050180c0282900d503c9074203000c1c2008030b4001802000b1541080003508140703420005505c50400e0f60785a085500c8050901c2207201c600da4050010941003040c011600703003011440388141c3c04407030400d2113138003c0c40e0b032250b10750203100100640c10302002c2206024402d14540521211140b0055101c00601c0c455036524a40102d01800350028243c000500503031001400421000e40020301f264002c028554070312034424402c41000c100b000c1c0442c14054256000564503404c00082c1c1401ca0600500002d0b5031406841d1060140c0030080d458940c0c0711184045c05810401d2402400c1400400520701d0603659980c003682c0f04450b06011680c2c07050f20b0f20480f91400304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 142902005 1250 142900755 142900829
    0x8040b0c0f04060302091203030403270509070507030306080f0d02010e0d020309220207060618050403020316020103060f08060f1005030a080a0318050708010f0207021807020715050301 81
    0x1003003d08104007140203400150b00035820102c40b503040300e0401d104202070b511a0384641d40c1e1901000401200d0040b40381000d00440b04000805414460360b52840b4485500075800c1c6825520b6180070f090480241c04158050002f078050b41e2581001c900740440c1c001c0c100c5c02c0503002400200b1030110029030b80c0c80f0045101c0e0040e0020b005620b00c0c1d1802c04201c1c20304400c03200c4948079070f1640564040c1245e00c12501110b9141e075840c03040018014000181110360b40d404000c10452901d524040c0d01c900c517030384030508141000c0300704038116070095002030090304005404941c800d4480745c40c255611411b86400c1c02440008000980c808141105541500d03005005040980c0103a40c07014045e401c58104403003030544880c0c4010f80e101d003494910b40300600420042861170b280c0b00c0082c1c21903800305007000910340100403010141c3c441c030300c0d070002d262001c0100209940d50000202d0900c0da203a00680e60741d140c40200390034900d60140155059480b42400301007241050070058100c441e00b03a480d02 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 142903255 1250 142902005 142902007
    0x10b041e051e150406020c0a080109050a3201020c01151802031e090703020a0527040f15090c0e012405040b0c010e060c03010302060403120c06020a08040b0c0f 70
    0xb5540e00e80d804196580c0d60809094080e1102c4680c080d0b4000d600a60413040040e4002d0740c1c0c0151360b25040000900416100008000e012800c0e26140d0f20351044003000341030385198041000c2104503110b4031074050a0005100d603400c4843d40d1806010b0350044412108542c217040808010b03c0e003804184d800ca4800145051003030800f406c4550294100034080300c01d1011f03619402d400d50040340350091080d0200d10141000c0c50841c030421031f02d0700d15904880d0144c0018408080c8104d2100c1c4c5001e1a481d100f00080601e42e15490503800301660100c008203081c01091260301100340179008000700318400c3e20044499500d407804900c9100091180070b9902c00e1030928003000c038071849030404551400f4944103140940b1440c601c1d5269100d000c8440382690742e20030b1000301d80c0050081c40c0d00501828501c034030310751450300080c0f528011408082d2001c0ea4841e101059540107060350440313258401c0040d5100c04080c1c2e07000d040074004444c2510042c1d110030004855091031011a050038080c91001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 142904505 1250 142903255 142903279
    0x30f0703020115090b010828060305031e0f042102040914060f0c0a0c1b0f1403030c1203090a0b010b031501080609071103091e030d03060302030d030207060b09010b041e05 75
    0x188102d05e01d030b200081e118008d4591149071115103809008040c50041005665400c2c0300d141d8601e1141c044803030b170700071088140405401e40c0b451500321011a008400d466032050099551400200b0500000030340c0945080c99110070042154844101c0c065a0003d03600195502040f0f52031001c8100c03040594414200701c03c6000e103000b0303a220804507000b45083d48640411028100c1440c0e155001484120060001040504070706020080d0600e42a4091420f01000360755042d03076003c1c0c141000701d0074400400040e140d1442000040c2e075a0f41c00c000070303850f81e503500c0380d645e1606c0c0e0090316a00c81c03210b038202c0c41518550281181502455002d419201c89582d101c20854007a51040030300c1c0a13500080200c2241e03951400040300c4044a44400184c80d212150700301440c00b023031085058180350820b401040982e401003040f000f10f00703c0c0d0801680d641160328001c0f00502c00300542d0340e03105089000102d01032202c1c4000c1d006441c00040340220017101e240c5510a8451b491083e00d92000b060251 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 142905755 1250 142904505 142904521
    0x8040309150207180f0903031a030c0310200a031a041e0c09030f11030c030f0303040b0a02040b19090b070c03140114010312091d0703050702030f0703020115090b0108 73
    0xb10180543c2c1400000516007a03190303145042d1b031140b20043c0c00003904c071440f403501621380f03640c44121000114020103d498500001c40d84410791402d1500703000c1c0d6501340d804554140c0c001d036000b1036a24420295a0b41400307402c0513000302000344904283c800b101041131140d0400713204142841815510f039400480220000d04040e140107101ea0f0f04000048200000003081e150b110a40d161244203200b0700340c0c1502d41403615000104001d144241e0003030008264040e000300840342c2203034200c0328015440c0e480c0c506c03003070181c825903110000c011000640c5410300c00e801009004000b44590341c1141d882d035644803002982c056810043c0c02901903100400c00991094a4800c03104010000441c80141800101c5a03100d0264416200c000c0c8291380c4404803644852281c0240419401103a80d9444040c41c41205010080503041495500c20205110078000c00541c0c10b8148803c110755551440c5180081c041c01c00a00030145462600c0008180300c5028054540301950607500d079004c42d501c11359 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 142907005 1250 142905755 142905779
    0x2101401050319030905030d11010f140f0603071d0403080601020d020316060b06071214030408091c1b0f0b07020d02060d020d050a05160906020705010e0301020c01050708040309150207 81
    0x400300e06201c0172040000383da031400d0007911113096183e25007903806600c01100d00c1c00e58032198002c624181c43c11004040d0310001580c55030300104074440456903503541d0700101c0d10340540c1e60801941c3c1880650008400c1180800b07051040b0f102e0755440100b038032a64016030351030300011810000358000f0b0001d01014084214400032042c040e0b5001304054102c0e9020884503488a1030a50b84200501d002d004500e8018540c49594098038034514914901034803241b0450190301102e520503654000d0700c1500030068903034042c0403500b048100000343e1982c0011901101c9911071000407440f0a407001030022071003001d481c032164015100c1645081207900f0415154020042908800d5080c44031352050350251044234070411603110000780d1424034215048102110b480403004000c0c0c840340a0060603404200d0238100c0f902802c15640d050714900002b4003a00070400301c0040d940c0382c23004015000b80d100003810301450090f22a46125a2640c28941c0598610800c0c031026071703c0103800b0400a020740f4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 142908255 1250 142907005 142907053
    0x10c020a050d2303010303050408120307080c0705031e0a02010b0607080307050912070801020901121e0b0f06030a20070305040b1b030705070302120106051f0c050607021014010503 79
    0xc04880b07403036042416200413500281c00c1603002400c0400c00380320740c51040203011000001c4151840c19442e10007801064290000c01080240304082010410017000b00260358a150020035542000341f00c1e564601001c1d0000c82c2c0c503400540c24580900043c0c10311a0444100035040250a49581d41d40d013030070345882e03200748512074019070340605401c0a0f08040c0040c8000e08400400542c0c2c4000c3c4c000010300c3d1031100ca5840d00e403e854030088000e25415451a1226004042d10114112854200203540d440c90841c540d50400000420040c0000c89a40184214461780300102c45007424400c040500d4007a40d080107011500410040c011a24100082c1001210420301000000a14480181103400501040356246e005140601c00c500d0508042078510600340020011285000b00044103c816484040500e00c0742d240305d0803502d4424100c24502c40d4200f01181c20301d0401c2c4074029500e68101c0b000e5154989440300031307440c0b000e514900d5070480314000d00622908103205450030120f9048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 142909505 1250 142908255 142908287
    0x14040204021602100201050702070f06050703080a06091503050105011e0e040807020a06121a0319020d0206031003050c04150b03180610030203011107030903030c060609140405010c020a050d 83
    0xb01503034100598032070404040140d29540046114102010064605106c50b08424581400541e00f88401648501039403640741d0145418540c0351a0011040020040c0340c1110a42078100b0000d400c4201c502e4103004200e80c4540000c0100c0ea03a01d00515281c51840e81c1103404c40281c0d9101041801010b00702240c21600443d0a40d242905507400280c84500d182e11030004030b401c011170050410380f60312900c80001c21409402e80444c0403031000a44a10032075024040300742070700b0010400d54888407103900030598042e01880d62424040014982d2200910003141d26129a10b0a6206802c0502613055103080d82e8030b03602201800c245108905800081c00802200840c403e1000c01c480c081002c540241c2d1040030f05145a4154010701d0309440c030400002ca01441c0801c20100001e51004445003220381510303200301f91800c0c516025000d840c00707500c040c0406044c02c00740940304104100084c0038500c41c0c0b000f00211102c0d807a0a0341c41e9480c4c40c82c040c001c1c1e001907446c41072803406581001c410b8489 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 142910755 1250 142909505 142909537
    0x151d06040b0a210b031603030212280503010f0b04030804030f03020a050129030f10051306060e0126070b0309030408011b0212030c090114092806031404020402 70
    0x7240f0140514a6120340900000d516680021002c1c2000e01210000507100c6503e00e0300e450450302c0280d41c2d59000014104480c400003984500c3c180941c03a0828010880c1e100030b40702051440c4010080d410070f005640c0e001e10401e800007034031211f00c1e00710340849601444140c182407440d1100342d83d036900801c0a40641c0035102c01c84000600a1155031051405c0d803881c07081c09921000e01002d144050348000e030007a44641032010120000180c0b1040030900120003044d103070303550183c4d40d214041c02800145103c2c2482c1c4045500b40b1a03000f0706041e9a0410180c0f05074070b2482400c680700014180c41c2001d50b1b04801401c3c03248408810003035511000101c116440d250740c0e810b0b61402c40f54403505000202840c00202051540d041c003044285c022241c40342425410b00d50342402c203910454907814148006401c080c01402c03507460545900f5100104500d4182c2240303141c02c2420318844500d60a054009400481c0c2d03103000e40300301d140d9081131201c134421640e200d41c20703c4001e600940f4806c1c01d64403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 142912005 1250 142910755 142910777
    0x10e040f02031918020315130203060903120a0902010f0f1103070803010302030d030227190b071407140d05011b020a030807020109030f050d15151d06040b0a 69
    0x1105000442c0110f0f20000070041c41a40100084119904020015480d00808901201503580050803080c5100d00f81001425500c0e070006080740f801d41d00e10000d402d80559010880c0850001c4041c0403045110354040c81c659030365107400e104440901c03c4c002e010030504658079111922078201c451082c241400d12800464030312071801d1440e00149400c8403a110000018411405c00780650509401e00b420154208900b841040a4030383c1815011a11001b103400001d80955400e8148000001000038244059444d01403404180d8080d04d0b017550f01660006880c00070b034000182c0c0100325030680c4038000e510b0807181c040084400702c10405441e213640740d003241c00650901c41c0c480d044c1d110041d002807085440c03500e4090180507009084d0019640340c17031412408a5041607102d501c0d41d10b43c0c50595a2254000302c80c4006181204031442d08400d040408903807600700b0400d214510030943c880d0450114540e4000710000c0000c4041900030500313000400143d09500007400c448003550400c1c40b2815 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 142913255 1250 142912005 142912031
    0xf0f070c060e282003031902160e070f18180605090a02090a0807030f0b040807050111090109080c03101d150109140421110a0b090d0206070905010e04 66
    0x4850110844040ca201c001004200d100545440e2101c4e0102c0c00441516241c40000d403a03000d041643c1c0403007000c0c030b00718005e0396109020b8031b440f0010a120307191003680c560b80c4131075107d94100c403c2c60200300080d0007070702d100380214500088026184244501d01d030500611420010044600080d00c0e500c0f44408100395480380ca4052203520100801a02c601c50441080060f100540c40080c95801c000c074140301255401c1d02811b4140c1d04081042c1c4107443d14a42503040d44201c15001d00309501c2c03d107982c030148600e2001044034070400d03aa105403054035400d01c541c8414035180c815038103521041402141d2443e54006101d41d031090034800d81c400c0c54001841c0c1c02c02a50700b0741c0500c0f40e0107900c01444040c0079445a02030800002030503000510b041e5503481c1680b9401101621360707210390b05c401100030384181002d48401032007a0075a207504229103802c80304550107640030368140c0240300c10024201d10005800b8841c46066841c0d5205519003001507804182c10404e0a0b001615003483c58020 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 142914505 1250 142913255 142913293
    0x1503010807060e01173c0601090f0f0308030408040902031005100306051e151902010f090803040b0a0605030a0302010203090c0d0503030c0a050d0204060e030d081504050a09060c02060f0f070c060e 86
    0xf0070601504a1031f4503000c0c0004020001c1a00320423080031700c044040c0841030000c0f0048003900c1c0c0c1702190540c0c0c0e40fa1428103200301d0040e0361003c105a4000020081c08d41140c1003010300b00c460558148039401c07040481541550b502d4011903802074000d051107585c5003c119402000700b500034002e00c900d10f030340303000007841a4018500318107211310700044040040d509108a4419100070407003042100007a903188415807001030805402482c0c0710012480b010003e40c8a500102002030403100032408918010b4080d40044800111038020f40b24a91228240b98900c2c0800e654490040c62556550442141641c2c215001e40c1003001014403202d01c40640c031b8030044c4040c0c1040d89034110000c01c42420036151a0041100c00d08009404040c411740d50030b40800100390f103504680c003085c0340c0d0b0341d400d1460040c00401c5001c2c2c886414509035015039a000f061640c040d600003481c00103542d80703686100c144901c040d14410009682143d05a01182281c0c2c0302c450000e82610a50f815001080420204 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 142915755 1250 142914505 142914601
    0xc0105042108070f0809071e060809160b031509040305070b0a2706090206040e0f010603020406080408071103060403050d0f05041101030b1503010807060e0117 70
    0x1540301c1c44007120601201c0d004000c0281e00440c5400380d09850800c200a0403940c1c100003803810b0108140108542c01c009000b180040d020720307041860016180d13800d10b200945030388620004078005070b0110744007201c00305944410b00040c5d403013003190500e4010104201d60004254010701e82080c504040d01e540c481d08428040d90181c1d641645a914a05120520402c064480018540313001400d501c80050095405c5200315201903130500030b00386082c0034016142080e002940683c00140100e44181580011401522201514401680c880740245d0480c891070060802046135400001c0000c1e00010003480d00714452100000c0e01c05148001c24070340441030300c0450108401040101d1030442e24400d00034110f80b00c020900c818201030729028000080220301904040e01d074816210151904640e03000c02c1020b450003d0795030341e903a80e00b86844006600840c070015410030350076421507201d032414000c0c4070000b01180070103444490811080c2c2d07007480608480c000031a0a040c001d03a03410306485c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 142917005 1250 142915755 142915763
    0x910030606030812070302031510090b120a06080304210f08120f0a09020105031305150403020307020109232e0201020d0501060f020d0f02280309060509240c010504 72
    0xa104e0414101c2c00c0700300e61004008100b050f00c103000b0801c8441d20320b0000101560240e1f240321140400400c100d4a0300015081403000400c00240d404c404200c80711211321581c84e070b22040040a880c1c0210603101c0c0726170720480000070401d6040265060500200c442214401c6500b1b0285682a41c0e841429811100001407424405410828001440c0440b0744d84a03101d244200422511540081c005000250a200030100002558800c01404014948103032100300742e021446d1a0926000f5500c1e80130140880c00108400000074907442007000c038102d40803003a4100071841500700c1c140072820700c104030f2800f14040c0354504004402e112004040d50713062140d001503501c281a0205000352001030b440402044400f601e0030300559408034040c040b00d600c40c90007440500b5010000ca00d007010391101002c0f44000796803400803950815001000d020b2003505d690420b40e07a1410140e42902400201a402103540303a5540d00d8041c441200e000c809484100203810300030840702c4c00e400c540080303030122 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 142918255 1250 142917005 142917007
    0x4030b090a0b01290d090c030f03020d0e0904060b030705090c07050615060703110a020a0b0415021c050c010603061b120905070e07050c2a1e09100306060308 69
    0x40602c040414001d0140410344407403001a18400b80b8062040e0f40c0210f0003c20200101e40f1003450b41c0c0c50382061400c01d4010801c4100b05840e8280b04070198061401103004d4850710f540c14000500860078520245001003220100f60359540b150700c00b400d2510901945130040800c08210303079842d0301013030380140d00020342103458102c2271a010b0315092003e009460415440b402240c50756840c2d03030445c3c00c00c81d454680106004010189203103007000c4100c0003503102d04204804a00324a00d8001750046400c10301d900c21082d21004801e98071351200420b841c2e21a000c0703496422100740110000d00318204c00d90300000e1f11581c0c0703880303400885000e14111760407049580d0505003c80d5101080c03207044503800400f040461816560180d03101c0c006e100c1c400000241000003440b050040060302c83da0403503002034500c85141c2c91990200b04200320700c002040c80c0100c11640c801d08210f407040c00441040d40750207000e810558100001c010005040c080e40c00003a14003c0300182107402030301c00852007074402c2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 142919505 1250 142918255 142918273
    0x1403150901060807050108060d0809060409021c050703051005040507200703031701060c0215070b0f040201031a091f0b0a031a010822210905030609010c02071a04030b09 74
    0x182090420317409141001404024801180d41d24012107000c00d9000003440d981e0201800820040c0c040d5912030118980301250b1503c0705040c64842d800c108008401c1003045540d55001907080b5041a1607140c041c840700e1400303100b5802c00c1da0200c1c0c0c0001903814aa04094292818503840c800845030007807454110a104204042d00301c6030000c00c141c9100b1140540e9030500200611841440a010340301d42c20714801004001da2070b00c2110500d94100e044c1d285039281c800b00e5401c08100950f802c80c000f91034038000340c0d0076045030300154520410007840e104250300c3e04e80e00c000d8002240751404042d15032000b000a11a4043d10040011504030344001c140d405400c90342c48007600f00b0300445818440c80c00c040000030900d25095048154100c1d4081d04100321030b0900d084186090301000b4054440444c0d140209508165108101c85e01101102d00e150344500c60b83d0300f6076403e0501080540d1068209014102810100e9090807500c40c1d0300768203044d640d4886100018064a00c500c1e59002203441c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 142920755 1250 142919505 142919519
    0x1b030e030d090819030c02040606051201170309041a0307181a0a0302010f0917100501090b0904030f11010218041503080a0f050702030a08090108090d09140315090106 73
    0x900200c881e601e0404441091800842a85074075900010310020382c48840b0350810980201c0341c40c09800d4018104118003610750344003902c1580030030440400e650b40d40000141001c2408402c8003c42d480c00c0146040c00b00c100f0610000d401608440d650802e09541c504c0311585080002000410010b800c402d030002c100400c000c119a203481062060414500c4102e0003511111024002c0b43e5080c42c1c10000341685060455030112550011003c44007942c007080d0b0039a1000aa40500d545030290401003641e850000e1170480303c801100ea40c000d40d81400141c040b03405403d50704c010185a040c0703100c2d0080001c1c2c43e85d00320392103040d0040780741020004641081c10030b84a500104100506030f0b0f0340c028156102d12046004e400740100801c130f260f00701d20300c0c40f07403003282a0f440c101e501030101c440140e41403a11201c607030042c01500380082d814500048110200080e80c404600050b03c0301a565410b090244880700c0b5015450758051203011b49102c409100c05140034400d2080b0b000004c0c0544c10100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 142922005 1250 142920755 142920763
    0x902011101060e0c0d022a07051806120703060f0203010f06020f0a060b0109030818240a1211070b091608060609131205030601260f06011b030e03 64
    0x291001260b24000c000e1180801a2540c10f4120f01c00801031074442001e80d20120191041c2c0382501c42c0070049451010240703800183d0040d0007140701040d60310b40c44d02d51040c00080f0444040c00c1001558407400700f01c0a003007181911425821a609072014107803030362a1202a0f0380c80200340103002c0e60020042001907003511144000d01010701c0a00444950710b0111f5030307180c071841740c05080107984c0e80c480c0003140e0250059400969200051946034540f0790341d40403042c2e4076a04181c4c0032304008492a010602c1c01c440034410303521440645424440b603003004031010780e815402da00305941e554038040c00203882032000d40807c51141c41209250314020203da0709040440070005005103180005108000010030f0080c3c3c001001c0d541c10415940c1c8000031042020780c1580504409150b010101c55254000c004504c50030007a00d86480c3d4980c0102c6035207168a1a0410a2401341090042448480c200010359004101454400015031000e01d409803a4068045e0171800300e00d04180120403410284 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 142923255 1250 142922005 142922027
    0x6030804060e1008060d11031f0912030902010f030924090501110906161b08030a0306081506040504110a0603060503120a0e28060818010527150a090201 67
    0x211301a51507082032000b040700008605802000004409480402520104035050f4172140980e8130300c01c0740400451605c020f142c20030040d070300351300c0e03040301d02801a002c1d00691082581c10fa44e040c0000c0309042007180101034420040700d1650912405c1c022482301d5a80300500b0420840c00050304914a10703105003101d11001100090007000d00c0550f03a00c0c0c0d03949003601c0020600000d20b180314030091400200e10440e0700040c03080503410f0040461800d9000014003800c10316911700308507043c2c9441c405039603504840724074507481e5003100000c1c1050a064020f00c2c2c00520880c0480803a0850200041c000401c0d60040b100190f62001e00b04664a1f0030042411940d40700200c01d89062841c0400407d803900c45111540904809103101e10902002e84110119000d02c4002e255415198500140110b40a8800740c013000d41c0c018404510100612507a0700944900440c03e0941000c0105000031103089040c0d10320900500000242d40c08250403800d1140f42824000585101c851001401c03c0741c0a03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 142924505 1250 142923255 142923257
    0x30b03100c0806060702010e09090102190c02090106120b03010908301b07050a060c0905031f0f0b03150f0f01060c03080c090d0506091e07170106030804060e10 70
    0x88101c81103074021444035040300003a5a1266075216500059076860300300451150481d9207201000501d190641c09829100061005851080501c0c1c504903102c10400d00040e42c0404e031340d0010000c1784e024503820b01004841a4000c00c03d24400400039086a06000c400e81d2211400248820303105110403040e0780706040f00d070140004040d002d040301c04403d00105640e1441482d6115510b0020a03a0103030342965500c0811210010780134a402406050201d04002c04186030f070402040350310b40414403525504c2c1d04111703c00500d443c2e81030751010b0030450030b031280b020341d1b1002d4014491701c00f4400c1210f8075207003e0304108207080c8024603040309440142403805507810f80c801030108951040341008030503007518040c00c1d03946400702a04010f11445003415030280c04440342c0c20410401043c910300c500313400419201e01d1503041056404074041240c0b46580c07500188000d200f6450307014210000c40110000000e80b06490b56030740059940550016000304c1c0d45650401c107180340056020f40502d5003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 142925755 1250 142924505 142924511
    0x90b130302030405060306010c0b0103080702010e060a0507111302070303050105151e22150e0108060d02090912040605030a0605040207020112050405010e060a020d0608060903040e07090b0307030b0310 88
    0x115103009480380a10300405101e100b000012941c0740e131041c038290704019040144e800f213a5a4900d8020001c2d07000c0c0701d0403404212921403800d01d6103825002d4454803a50340d00c85521b001e0240d544c50760111954007040703620807819264268020300038405404045d100380c60004440d410141007044402d200114600d00482c204111341c026101c6801a0503045500241280c50385a140d5000382d410304440039040100c0d81c408000244103c1000044030380c0e95a80d22211034032035021004450500007154555040004a000c00c030050a03d135240c81c1e441108401039405103115104c098105500030791101000550110511148403510301c100002000112421482c090590380081c264005410320080302c41e5446c1c0000b4203101080d0410075445031400207880d49442e145d061000250407400d0000c002c01c0c0380c480042242140040c400e801407825800171801c040c642900044110f0b0018008010040b90100009851030800b020310300903450b6841c08a42c95064106061805616000c0c103041181 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 142927005 1250 142925755 142925791
    0x120616170907030b13120c03080a0605060a0e042702030d2d0302161211030c0a0209041a0906061203090a06050c0111040e0a0e0318040b0f030a0303090b 67
    0x3200294002c11243d0000148210b0380c0c0d01921114007040015006e001c06108000000089603c6142d903444280f1a844d48060f03521a0500c40040303600600485800070400c102e0081b00500600c0c403041602c000810119007001c4aa00c12404c0f5561103a2032200f000161035042c0442c50709001003240c0440500c4e02d520755000080b0009070319008101030001e0b0003102191075450307a120786c0407648580c0040d420415210958030305040401050760040c070003c0e44584401284080200456100801840081c070803030700940c003007040e400000b07402140c5042601d49100c1e650003a110b40c1c644610f8041c00076040b1450200706008181d00d841c0d0b0341c94500d81007045030526603a58000954250b032010714100d9101c50300c0401041c010303c0c0d91124210511000700780011401040004607201d441000000d0103603140840459680313000383c19210611034940440300c002c9003000c0c1d00c0802c0e6280001c0203450202d603000082170510f580c0c64425400a501c82d240c0505004e040124690821412664264900c07 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 142928255 1250 142927005 142927021
    0x1002060906040b060f0603180f1207060b040e100c020c2704030504090612021201091203020f07060203010308090f0a0b040303050d0b0a06020706080703090b010e040212061617 77
    0x2101c002d00052000c850a4003007901600c4004441803a1007000d0040360380c0381002100303c00051744001a08002d441444403d0420744000b0900c502039100c0c14120358108074813a80c4050250140004036504680e40d076846034800082008000318041602100050400029100a090210350700c1800d00400c4c8480c1c0315007000c1417048002c1c0720b500030580124410388681c0381c215024815640176404881c04c00602061600d281600280c0151003200c041001c520100062420f03145110f0000d001c622a20b00b054000a010790014140340810a4a10307241c0305682e03a81000700d80003a0000d66505001254050860030032102c54800a14101c8500c5411850540180722038400d60000404004022410400158858202400c41d010051407800145c0d114403009581d50514407680c030010398444081411940a4850a0b11641c0c0010840f40300707038204260003a0300c00000e0001c030b8000d10503507460480410103104850040441e4070007010810151740f80203101810343c0442c2243c19a034201400401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 142929505 1250 142928255 142928263
    0x50c03010e04031413050a05090c030f04030c06090c06080912160602090a08031309060608150607060603060204150206010b072303030118110702010e1311040902040510020609 77
    0x1121402181d0300103075200d01d01118210380c1020381000601c00415000c00c404144401c0f0011307544165000031075590b5036410406041c1c001c0d1480500300c203041000c0350342c1c8143e440c0400d601c5402402c00080c01c00d0141c1da400f0840b000e802c41940d8002111100748941d035030000701541c200428200400f95912a00070845a510450340382860b0120b149020b8001c002150301500e1090b10000c0403004200c1e41c03601d0060301d03540441040000c0490810010818003014420300d000e441165032810300710b940d0510948030400003a000107074400818040b84000541d68002d80d000703548907420260701e80d0b00c0c120b4408003d050764840c210039508203400501c00c407455082500e00c9036800c0386035082041000d0369000045881040e030840c0c2c07400000f0000c2105d81941d807034401584d400c5081000403a0465401c02440d001d6044020300040d4140d18101c400e2034110340844860080100009450340042a00720017644203600244005030081001c0000b4a05860403018940a1b80080d200c40d00e444030a281d21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 142930755 1250 142929505 142929509
    0x70c12030f0603020301020309010912020a051915021303030f02071d06150304110901050d050a03110f0a14120f042c0406050411010504050d03050d020c01140a0f050c0301 75
    0x405994075a00c201041c0503801501c01150007600856881c00c150505074081e00803402e0039540e10310720080030300e030892000800c214803c6e00329016010f4148068940c0e4814400010152a220b038070388030482c1005286e10060155500c1d45241006281c80d615000d00580d5150000c1c0c0b096410001c0b0420802c0313042c5d0701c00e4407038405024411005654003000212908003040700e100351160701104000c100040ca00b1000716410301210b000781e03282ea0325001c0080e8103440800c02042904004002c80010703014074103a81200d9004d2094071003503030b00c07240b034030b0704d00b000d000000c0d100c1c000f00001701c058000342804182914424401c0b4180ba014022262181500c1948220000620084180c001c0880e0340907200c1070302c5506040d05807650401d402c0c070601411f0184c40030303030302600c54000002c001d40c012800c94080714805000c11164803c0c03074400b550160040301c0921341c110f40800520208240a100e100003440c038803d200c800c00d041c90b1507101b00310340802c8850380d10715113080144100c00d00c6643c10340b41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 142932005 1250 142930755 142930757
    0x160e0409020307090204030b010608010b04031a04060f0e030d0f05100510090306050106031b020a0314070501060509010807030506010f050310051314030406030b06070c17030c06090d0305070c12 85
    0x19804410344040b910f8800258803400e1240d00c0403030040108000c080703a480c103e800756a03a40ca5540d803509040400c6114612008002942d0060703030300f641e0b003032a2100690040c0201c9c400154400d003a011070066070228421a4415040040e0000b4210100e104244210031b5002d400c0180e85003511105950581c54011503100365882c0206020041c421000580074543c0510b09000303a5955110180c06003540d00e158401010100110401c0c00d480000d15261542c2c06030780e9800c0004c8031800b0788005600191040e80c0f55501c5810109498030341d40550341c0203206650051600e6450b50902900f0024181c00c40b5429103003030002006a42c0c3d00060880c08449502000903140d1a012620b50289100c124000c02481400101d05072855021014108031443c2e92030034404003081c03a0400c1b07824414290014024583d0307601c240900b10032040640c01d240280004c6a142200b4007000500d441c2003100d038500c0950001d2000c241e41070f854081c494100400717040c056180340c401d0340c07940d80707100203c8800c2c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 142933255 1250 142932005 142932011
    0x150115050702032a120c0f06130302120c010305070206040b06010f0915030903020607140708030c1b01020301061805090a0e010f06090207020a0617040f03260f160e04 73
    0x81c007550b40c240942c6482001124800c102c101402050b240b00c0c0a04208991080703401c103c500c3c00114000c180d1011448006081c04113a03240390703081103d25041807e0004c0460328000b408030068440000030121100301d0001002488507000005080d164020208021500000700340b1000841c0014101e412240c00d090104051000003011102104c003544107042141240d0180882c068141e03028402e154060343c00e445a80e95020001d42d44010901c480d0b0101c1c40c030400c504c0d0041900721010303540210790781455902c0c201c10380401d03242040f00300080b0003051758000010000c03a904070109264543d0800c1c1e110b00010b01c0c10002601c42c81001340310402554075400c200380321080c21341c42400c00385410031701041890344812110f0005c0d04013900407030162a00082c04a036441c05005610541082a1440c00055586556038103900700e41c12001c900740840c48a12888040406c40381c01c0d940c90543c1d072207403214a03040e01e01c0780710418003820fa41c91080000100d40d8085500a1a08000f070000366404 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 142934505 1250 142933255 142933267
    0x408160f180f0b041e0c03020301060203040501140c01020307050309010b0301050c120a110c0f0115080d0c0503131203020d0e010225090603080c0f0d0903030305070318030201050915011505 83
    0x8500503205010f401d560040c03421098501c2c903144103203c0040b922050004003d185600182039007244400c0c003030b000169000b800100960340c8640181003c84174011090307401c103008038100070b003642c00a8079030320f000c030f4404810041020000d129090310301038118020302160801d01e0610080788904043c01030045078450014441c0c0b40d80750021004148120f40056495030719648041d01d039400c03c00d00c03003c5035007071480341c0e100b0010028420b07090300c081030058000d50181c0d10050350070748a000d000311018041401814903070041e142c0c071500140f40441d100e07a0700801e54039000381012010b03080b46040c80010500c0700c0050f680050f0949121218030941552000a440d81e0141504030764000d800d030354100030020080001404c040c2c000060601d08030703441e6403040305000e9112a4510407030760000344008003c002291090f00496001a210700b80010b02c0314100114081500d0f81c01e1044e40981c3d1500140441c003075080010001030045400382c4005941006400a00c41c840300380300034100400410f41c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 142935755 1250 142934505 142934531
    0x203060303070209010303020f010b0f10030903090e010602030415030507080c0306030a0f06020a09150c060c120213140612010b07110a030311060609010308030f09070801020408160f18 81
    0x45650303050b0001c00c2c1c0d01681d0781d07c0c54000c1d41c400c0701000c14040d65003481c200312100d00b041c0107291b00c1c02ca0300420300b14840344030440c1100200782c000c030240d040010100000510200701c50a403070103014964051a66141071407013600d03072181c210a0314410585031000300f01045900c4600c007600400e0300c50b0700590340d4403480002890315280340c0010b0300509140717810070200485a070040014502c1900c4480045036140407680703420507203514540224021100303800000310644d100c0c4440e0700e5903040c6012030308820b116190407030b0000344104522071181041804003040c0140151001c4000b00c1e14117103003121a00c087c1100d180e043c0300302c06400b40c000c1444010059244108500f9940c00350000b4101c40c0c0d00e04009020101e116800303030080c09808082a4030b41004a00c150690f44c010078010319540380c180e00620340344401400607850740100d681c0800d84210a00003070001b00300102c0244102010f50441c075001c0340d0203034000032032460800c1c1c00304a00d03000545108650138901400103482124001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 142937005 1250 142935755 142935757
    0x40303140105010516051f06090e0601180216080a0f0305090c0a06030b06070f0b010311060304030c030e010e0306011401030b060a0c02130b0406090920010212090307030501050f01052707030203060303 88
    0x4001c0000d4010751010882150740790700c10720890b40700032010f0100d81c02c08047d10341c07520b00c00e00030003400c1103703540c9611520216400a04062401c04503070402e1030100d03119052250020703202c000016419071302c40c00107584c1c10b020f031941050940c0c02a0541a11800000724101070b03502c6400d0a0544421454450366502010340740b603643c0103481034413071100390b14105400c00b109010444d8600085103040b20581820429680b113658180c607001241412901e003600c180d904090310a04110201c10b04526070344007408203900074500c0c41c14140b441c1c511a4009001d03121700c240e40a004500501003100c1140d80560020403681d01a00c240780280e0f41d00528402808202038030075000b50405600044881541c0d0000302c91600446994000001c2610341c0c20241c500c6840d03280c0103900c004503d10006864a000340100c05c0000c0444055075903070303500c0f9400e4842c02c450103880404000010007050401c0d0714207411000c55540510103c0c4010000d146008030f000e0031071010160b02100064207914108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 142938255 1250 142937005 142937023
    0x3090d050f01020c010204030212120702120f0d031b020a0807140a0f0f23070506091908010b030f0d021216020d0606030204181106030c040e070804030314010501051605 74
    0x707009554513510416024041c0d406444124001d15611941b15003404001c590041942d4143c1e42d401e1502c0d009400700540b0100c583c2c0d24650a01402110712000003042000e64500001610045580b00702d0140c0d003030314801c01c9078415081d9040030001381c0005a45804680010b0381c020b1a00c0c60200301010381e545003100191006240c00042549842030150711481910314512829014140c0b001215050100b1101102018400d500c400300a01203442c0c80d801603c0559006410780b00700c9000000d0642d9508801e90003031446964840300d220050406224a240c1070401c00b000701800700c0100e034002d584030b015046c00868400042003984101681c07100e52000c0b5074002384905107210842c140310006000740d2200720700c540d01d00310341c4141050030101c8081485070840c0c40059427030615014002c0720f51006200c050b405c4010840483c4c1d00b02d151112030702038507166403080c1071460035180160489510307086086e038200144004001c1c0ea85d001f021121f12032507820244c0c0520901c1d21380180781400d00c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 142939505 1250 142938255 142938283
    0x2041a0d0e07031a180c010804020301020d1a0f0904020a090b0f042a0f02071e0506070503120a05013005060901020901030b122a06030411040507090803090d05 70
    0x10100106204030510540d0030411040c8021503ea15050004403c05444140c6410f85c0c3d0002148401598003035410258418005800980303000050400c6904483c8002003110b813034900074014100c0707400c0000032111415003d481030340303580c10280c00003044041e80e4480c05040c00d4a4513160001034549415507482c20201800600a02c241104d40c0003414591507101c103a141e041414040f00c8074810010110051800d0300035007a0142003800c1c40fa0040548014a00c0e81c400380d0f50002803035210311009040c070303034052000365494a102003044c080c00c41d00075002100c0941424014400d82c0641401004141d2540c20000740c1f01c1060170340c440e6032501d0401e004d0304a0080404008652406400502c11190240d0303081080440c101c0c100617584c034151048401c4c0d680a100c941c940404264403c2c01c0c091440b049900b584081c401c00110300c0c0d8400c541c2101c51154000602c0d0450900703010f00754006c1818280f20480310f080c904d540340c3c4c13801481e55451007801f11150f042d060113403d1081003491001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 142940755 1250 142939505 142939513
    0x50c060d0f050907180b120a060e0618070b0703020f0d020d020c190e0c130b0a030501080f120f07050115080d05040b0f0f0d09060506030601050402041a0d0e 69
    0x60008080010074a804202100905090001e500090042000d20a803040c0c0048945440f004981200007004466484c80c0c101e11080301300c1100380800c0107103805191040401044547c5460852420710380b000e0410590030348000700c1081182c5012405e079003900c0d07040302c078142c6070755803410202c1c5020010710700043c581c0207141c0407421007036004c18107526204c80d079001c4524500100c8180608030768030021f0941d0604904009104a5618600c41500b144202e80c0450030b00c0121b1416002d03404140d40000005400060328200c055010701900703004180c0c0c1009003001001500e815a02d80c040c0440c0d1020340500041c44085202b0340009403181d1a421900070070200c2840280034a040c5150b0040030400d200c3c541050505c1d43c442c00844080d81c4101a0a5080c11542e41070001c0540041c0740160364580284101c441194141c484c42c0c00c4030303008070404240ba05169007454205101a00010b01070341c0104801d02c11490b4511290056147d207209499a4075400f80a450003041d00c84a16402402 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 142942005 1250 142940755 142940767
    0x20f0304060f3c020307020303120601091802190f05030a150803040f14060918070903170a1403010803090d020312030c0703030c090f15020705031c030b041404020d050c06 75
    0x500070100382418002d1028103a561107407400207a9172800f80b920001d41c107610801015040e4407031509429040030060401502d065218114240700404074801c684241d940841c0c0315182c6800d5201e6103048451905000d02d10706003903400101544002018001081d8603009000100303804c02142a0080078044256625223850b40d01562641900307100300c0941062100785108540780c45811208002401481140190540d24803043c0010f4024400020701203002070000200355000624005559001022952040030401c0500300c1c0001540300300003401e00f0710040c00302484c000b0448405643c2201c3c01007502c2182e10000e4070b80b0280e60840e420461022060002c02c0c041c0c04081c000741880380d1421700415915040440d030010b240d11030a003c2c544810300c01c100750410b0840701400ca8202c1d04c160b42540d91508082881c00c5142882403c0391001010065074081d41032154a82141c0c0444046c0440409100303111402c8a01410281c0310345580d02401c010000d003040b440003807100151416449039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 142943255 1250 142942005 142942067
    0x90a17040501030b19181b0e100201050403020304050d050109050d0201090b0f041203020a02101508010f05010509390304020a120f110a0308030103050a12020f0304060f 74
    0x1030020301c11540841c0c10580500140d240c00680c020b041a0503210650045143c05078803400260440c05d083d003195562038001080e007480282c4000c42d00c1c203544800b880420382e0001d0240250300c0d10507100031640742600b440300080d4040212022100200e43c0c1c08400740c023505082d40113020354000248203108030002c0b01081c0780c0640102d40d81a018002d040584c0d03488040c4020801411a0010030909803034003190006802070b405081c0300c0d1007610490752144451024017013281e066406e60791090007400000c2103282003d00402405c18001101400a545098041071026102401c03030006503190118044858900045640094403441c002c9040d42c060200480c02035881079400340d005140c80000499003900000174080b100380d009940d0b2610458640712216070100e8011000d0344181d030f040c40000400d11384030145000e10b0040020380540c08840c0340c00d40c1d2091084007013100b5504030010802445001100b80d400f00c84aa00b0501d45132072805d070044a6212044401032038403072840007807402c0c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 142944505 1250 142943255 142943257
    0xc03030a050f0903070b070f090e0423031602090c0c070b0307020106060504080a020409021306030803090f010c120f02040f030302031b01060b18030c041b0206100f0905090a17 77
    0x8403101440001581c030341a19440d00c0348903403400030f005001d1b00c4012441c0c05100314540c1b00e90865925060010680350883d040f4800310664041e40c000b952031072134000140000b654a59405400c074010b5150001c10690307028035243d00003020744a071820000064091680c101111030023400740099036403040e11950015056041078a600d8015032800f0000b00d00c060003501110f0984103104000e0034003a489500300400ba080c1d02c0c101f00d0700120060400c030f03030b10742c00350207000701440c8544001a182d00e400e5200c6451300007402d01444450f0b040041340c00115400101500d44c00c07206000105060114090130006071140b507105442004c6941c0000040c03507030120280000d41e450b83e5000402c1080e80d082d082c2620b4880c0240b8180380002c00449911410040400d42e8a150240940f024001404001400c6031950b071600700f5140e00e45444d100c0030b60740c1444240c0d1301c110300c42a5a0505030810301818640c447d54000e580501d541d540c0840d503000e01c20050f11084a91140d440118001000e85840032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 142945755 1250 142944505 142944511
    0x3010506040e0a0b18030301060815030a03090b03071701060504050f0405010b0a050c012712030606021c0201110a090e090a0f020d051f0606021e0c010305040c0b070f030e01020c0a03060e030c03030a05 88
    0xb21445822f09009519010486800c0b00e5010303614200b52074180300c41056103500207403404007031050003010300348180002c48090740288a603448440c0c44130700d044140110700c0707595404c0c940b140c2c0c43e290060010850f41403c0e170303204842900d04603440c4da10f81a01d107401803103a00160990740c080508007202d0b07080c03c80040324050784540c6007810102c085040c180c09641240c0900005608054072144001c0450115001c0034143ca100100d44405042c1d0b0445140d44011f141400080743d419060009001d04c500c07242c0c00040c0c04005141c0500036841d0030000702c521010003889410b108200301c05109041110400700c3c0c244003446800c0f200e2011014008100314802c0001602440480660b0748540001c0d0311b0117203886034050301c960014840118000c040060046400f00c03d66075020900c0c0c9080300c00380071034074824031600c0e4000d0305074200a444002c0c140005411940000c0c54070680e41c03038400910003103d60001000c92181e08140301d4074118020f880030700e600741c4000f008100c004201a000540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 142947005 1250 142945755 142945771
    0x15043201020327060103021201060b0d052a120c120a0911011403061014030c07020310020304113705041b051c151403010506040e0a0b180303010608 65
    0x111070030051801c0f52501e00380d084074040c1d000307680100050700b852140d00244200c040300020300f040d00c82c0f0b04040301c0e0f004078110b03144403503a550800c0020354250f48100324800503941c411441d100e201041d00102c0c40b540103445460501324001c00c039111245001d8803c0e100c28911a00094130700101d6020041c10a10320980da0389800389604041075018106a44154070212112482c4ad500c050520010801c4d05909078104001c400b0100d944041d00700145010310300d00440c040d9115407030700403d854843d0050340c03414030a2040003804006514401c06004100d0309a954124400f0404005868101210382c7c0700c0951818100c0c40294541001c01c01c8243c1d2800c4408000e41d01c48418410781003202c410481020643c01c00c9203c00398800c003020440a41910840451841803400e00c1c662440075039845106045101c1030f24000ea0700c0c0a0051076880001501d040000c05800708031980c3c1d03101410401781000304040d001c00d00b0304605070780600e40300c0160011640d0f256503a00d0007d0144500b121408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 142948255 1250 142947005 142947031
    0x7030f060b0306010203040b031003050f24070806101202030112020a0b070210181a0304051c090504020d2301080f0c011d0316080708010608150432010203 68
    0x10812140070000d4034041c05069005500b464201511070301c49070b001030030140e0f80c1c0d07450450000c0010001c014200841240741d0140030740c2d0b0b41140384100700d1080d040100309500c010104106c8013540c0885041e90001c02103411401200500005a550000c010500741265000000100b4202aa0a10714820b14403c2d54000282541c074016020703240038001c0025442a199618030003002e104d400c600002c40a01440b15034640d54440c459400329246690300329403000d0201c02c000912100740700305c014910011910b80c0c12207854500003030100d6014024684216404959030b803140700903601a01c1c03074014440402c41c01107850301800f0340c1075000b44135542e850320454512240540e000318421000301d0068403042c40d181d10010008400800b000e0034250988500307103003c01e200b03550f60b9203100140384441c0030303260250900c946582905c0c5107800c08030243d401003554540d544240c0104a9002e40c01c04190440840300c13402030105c0c112050100742038106c00481d000480d000660045008000e06181e00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 142949505 1250 142948255 142948259
    0xc0b070201052e03020613080a0f030906080403081b0d06140901050621220b07030501060e010c1103121b07050405130f031101020a0225080d0c0809040507030f06 71
    0x16140303d0000b100721585221030307810030001424143d001e0403004e442210f032250410f0b2074041551800c40883c1c01610041100304540c000e258004000b075002d03051078545910355103440d85014060320400740144018444500e0750700e60440d00b00003030340c040c0092100c040c8030b80755440380d030041804070181d566403055005070000030781460244111240c0010b80412001410781002000c1480d0b04014a020081403c01c03403403d2440300c0603103002104c1d500c100030419150900310001812100140c01c0301c0240302c4d00c20100c0d8020f0781c000603010340e107079070080b062468819503002081c02c0141c5000030049003040828044450743c2c0844000341c44051102c22242d85a40d6071040200750b138001c0c0c40d4032a00c1400c40e4900300128125806a600003030090800a040728101c502460899100212890068119890119101c100c00544c984600391240040b0700060070030700000d48614150700540180070042c4d003403204200b6130b202030700c4868000810403c403515041d0000b030090003c04200211407440d040c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 142950755 1250 142949505 142949551
    0x2304050618120901090e010603020c100b030a0605040c0b0f0304060e0307030507020f0a030b01121515051207090203100e1e01050105090105040306020721020304061409010c0b07020105 81
    0x604005070312240145441441c110105095500400c1c26a040014414000c1001c40558114130b000b0105513a00682e6000070360740341401e04845211100060f42440b180741a550b800040d24900d680d041000059980c13698509245504020b5000701d18907600410180080500e0f400654410303800341c001488203082c00700003682c4034410340c0002400304071b05000c10405424020706880384071001424550005499803110086417000741c3c0030301c000701c60240b540c408005100d4103c40e9028154001804240a6481c200012141601600c0e010b20750468446900900c104030500017001c002c0d8085540f820310301c4601d48503d0081c068070010b41212008a0600d1107201d81c44041c48583e00c40c03034440e03642403a0045560340e0110414a042040038000480402d000e1f100408800c0d114106150162041950f40007191009180305400c2d500140030400c41541c020310a0321502250400c001d40c0c0d00400c2d001030702c654803d810058a80d280c0c2c1c104001e00d02d44c0542c00355000350000c3c50040450080c8a00f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 142952005 1250 142950755 142950781
    0x120e100305040503030403140c0a12090b1c0203090a0b0411010801080a02090103060f09380c070b061c0f140f0c0d030219050102030708060f090708040623040506 71
    0x1500800704da0003000080d002c40d00c1904040840075000744040d1802e070501d01928a450081c2005442c43c0c4d001c041d4144a40350041001c000915021146605140000d2042c1220060850131101184c0c0c002000800360a814000c4240705030b0700980826039400c140c1001301c4041c0e0a0006070b80466002c0001040d09200028485d0b0400d038024030007142c3d6801d40c0d40d0600030700401110070b002651281c61010000e449180000340c43c2010250341c48141d0700d072000c2d000d07500c1c0c6940700c29010142900e080c403106100c1201125045074120b910403045885880114082501441e012011090094602001c00032901c0700071f49094083d04050050b221070003000703a00c441c51460240d81540c40045520801d08004140d501d800d406801a2103515040074440100003100b940b007152207940c004104203601b82c004003010b400402c00d13104042c8200103a40400c1111a018041d201404a5000050b0400007550072010b00391304d40d050340040e6114090b4004608220580d4104c429004502c001144155424 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 142953255 1250 142952005 142952011
    0x90703060e0402010c0303151d0615040e04020a0b04090203100503031918030c0608010905070201020a140304111c11060307020a0201121b0906020d0e010504051c120e100305 76
    0x448141002c1d1102d80c019502400401021424036841c0d4a95140d99441c50001c2401082800d00d41c10161607204200d144442000380158801c05803041481c2500004406603819182c0204003000e050b00e0300d000040b03110310154050705c1145000680804c00d03000130b0300914042c484600c003440030a0388030740405480f80101d19400c11004584c41d040300b6003600c00c196014031050700d111031080082d2a6106d00c041c4100540188000c218140d00401924950348509035001c2520300c000c40c02c0c0b184008000700800c0301407805c0421802d01201050a0000b05000200c011500030180c503100d002403112000880c102c1601034443d5200c09d100c081c1036081c2201140d210b0b0150307602500b1485e00a50043d10100b0b0144207001034980d45000112105025450100e8110100d442c0c0b100020b00e8520024a0100c2d00b010040400c081826800c03001d0360400705442c1540c00843e540c0c1141c4001800040d840e4120140250610940310707845c8080c643c11071404c04150106551078074545105840903826501d0035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 142954505 1250 142953255 142953269
    0x6040b060315010c080d0e06090312040b2203021b01050702030c0103180f0b01031106070c050103050916090510051008010626040c08011b0206010311030c030a08030609070306 77
    0x40002030340b0340c600074080d940d5002050410301d009802907102c00041c2e0300b0001001c69a00d5a80c41405407041d001c000040c4d10420341001146401400c4500d6036100700e01410051100c904030340400c0c042400002e00288a09902444014180b260305000307580300300d040b403002905441035007140802d500c0fa00403a40c1c40783d009002400721100090044000f4406c445004440309a08460100040e42600100780358a0081e480c4030119411070800a81d178000800c109441001c0070080500001e6132501e02804442d82400c0000c0d46a9411400c1801c02125030f113107a4402c0003460001c22100c0b101d03132006006a06825107000019151000d0020000440b00300c0404070700b00c0001040214820398115403500e5042d04104e09640502c011030003036440554003121076001e4450140100310782442104e1180c00b00c2c072680014440c0c0100c01944803001800050901000e0403454a40c6850802031034840c1c0c2d1010701203541d60f119078144803041e50800c0d42d0180c032689091001c906124404d000e8038040d1590 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 142955755 1250 142954505 142954507
    0x90308031e061504050d051509030702040b0108061011030c03040b1c020405060409090f120e01031a0f010e030102190906140f09041a030304080309010207050a0e01060804050f07140906040b06 84
    0x17814200910301005180495142c8501e1507100461b40100705c2c03050051030410020340d1501075510406c815141905010740c10004001c042010130740d202030702c45010b001c0e641005a80c000b0000e00603030451250140308402331000041c00648032407a000242400783c141c600c03541d000224101d81c0d1050f840349105866201c032060100b072001510f10360182c0035142c441c3e00c605840d40134642c1c07a00c501c081d03400c0c0400301007912204540e00a5825025550b1180d58001441032401c0b9800c00041e20f044c6c2c0b04268504100344070581d1401914250704a50010403015542081124540402041d50b00036004201c0000c1d0020003c56200025005032180040d6205031350f410403c890092000400d128250b16000c19144105070a0b07513101030005101034903540026550361001c80b00007a00d010b40300e070300090107652180d10030000c2d103d82112890640c1e60302c1c501200a40c03500d0400d185001c0d465400c01c0340340c0c011900f000a003021802c5c1407444a010940c0c0c054000d6607400d0422080314016a80c00b900110 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 142957005 1250 142955755 142955759
    0x152101140a0b0c010213090209010825050702010c080d0509160b04090506061903060f0b13152304030204051e06101b080301090501290703090308031e061504 69
    0x859010b0148803060500040c11b041d0410300d10001003403554000010254005032103c22940d200c0d0b2440d91010b00000001100a0f210302402d0400c200c0d05c0c601c1c402c00c8004500c0908580c81011241040f41d0420419503ca210f071254403001040207403040d040a2080c0303050058004034003020841180c0310003420f907082078907001c10103014090060030141d202400700300c0c1c0786191140940c0410042810b1741d0001c0c0c20b504241c03c60f1104045138111070000c0000340146c0100071310b040250030a4508100500107184481441a40c2d1850040c2c61920403844692103014014250000391086a0085909111700d407225402003208404400d0341c03000508504e40000ca59041082038011406440e141041601010380000100320940c80b104980c80280000104185030807405801d0150410b00d0607003010310440800e418506110b081c0b6401c030014003003106028140290110001550402c001302d52f00e18001d12801d21400030842814003440e03403a00880d0700341c00c1c40c03034038060742c01034100d82545864 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 142958255 1250 142957005 142957019
    0x2060f0112030e030109030905040e16031218121106160f0309090e100c05040b03070c0f0b04240b0307061206081e07050f06090d02152101140a 63
    0x8401c5410036400d0003100552400380f9102449030404d540d0080c3d0320142050308080810040d540e6083c4a902c09074000c0880d0171055104000308070490b54420722102c0e01d80d00d1510184c030701c5a002d00342e084141d5500341001a00440310159125640cac030414807802c024460000b003003250f008445410701d4051010b88d1103000100061800800d45002e07052034a131003956040c0d440b040d1011090012640d800c00b0041e4028100c041c0510f410308406401d19078101400d124003a801e50000034411170400501c1c0c529203050103641450b40c200c0680043d45074603249002d0508080300b0801c00311108000c0104010224107070003c0c23103500c00608005000c1c062203403400740111000300030b041c000900c1d00c0d40c4160000e40e1000410045503c0211400500c90303082d100b00103075080210742c3d803019004544440401a056440d8401c403081d108086807a500030140034000718500d0740303032090104c0c8602d100065040c45050703001c0185070307400c3c03420030000003076a00d40208881a60000501342c0e049070a01c04180904 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 142959505 1250 142958255 142958279
    0x31802040911060307110f03030403023706091505040c14040e0d0c0b010e010608070f020307020d0605090f2406190f09050f13030e0f040204031b0602060f01 69
    0x16000d1482c0142110b90000020750a5205803010000315098094a10303480301e003840407034081c0c644c03c00690300314a00b640b0081c0d1521860740d420101e1000f00c600903402c01c4046c207184803007915041c13000c403060b0850345401d8000340500d180960b03943c0407003002031203511018080c49204c0d9600c80c00e48095180703030071400c4159520110030107a019455204445000340b082004803000b0030181c1c2d400401108500346441004410780010480e524000c0c01400942c4e008202c1a800c00328030716200c1030f0702c54035050490960040e00c40c02540716050351002818802310f03070400b6000b01c0d0204140c82c1700c00d84030582c2550300d0740c0c40c01030301e00081d9400710540b8400c1c50303400210f03a01100182c820282c40441c00ba1607203400c02070760801035070765245000c14404000e242c4211a400f402a10310082c0e075041601d4400e0105c0d00c00f26000b81041101000701d00c2e42c1d110341509240407003010b031040d51200d0712840d000c0d180d0701d0031803002d5620040c03010300020a030f40b000817154010400b555500d15541d0030b04140d9545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 142960755 1250 142959505 142959521
    0x709060609231f110109081e0703021207020109030b100609090606080408180607030206070e041e05150d0804030204201603020c1e010e01020304060f120f060315060603180204 77
    0x9001c529000a00f08034130070300a450300704c2d20038400c0c03542d1400a00102c2925203484600003a80c03000901000300000d8000034102034101c0e41d103a8481d1218014030040340c801c1c40075040240030003505004d01c0180540c240c43c080c180d86075612901103498945000c07504482541c0705940005002d5408140803584620041104036550008010b40e4800b0a0204840350b02c1044104c1c01a40400304019106a211a240030028401c680a0028076664001d0120007821004035041f0b05544201107001c40014441100b884100508551140ca050b0306040c2d500b9080b07888181c1c080e0f418800d4540c0c9004100456200c04896001481c1c1007039030791a4030200078041c000381141540b28854003000543c0d0b980c3c4400b0f50705101d2542c0701c800c0301031080c001414aa81c0c4e2403010305641c0305200074001583c003c036030210460558601224041a01c80e90030001d0111424100c40c0189000000310600c29403590710a6004a51442808400da540e0700480c21101ca0064492007070b00200000e00043c9441c0e040459 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 142962005 1250 142960755 142960757
    0x50f040b030c090301020c0607080c03040309050f0d0c080706090815040f03030e03161406010b03060f0d0b04060c020d050a0509010809150c031005030102090906040b030709060609231f 81
    0x82803034401d0000c130307003240e00440194050f64800010400b003a948030f218154031060300307010107003541096a00074200c1404c40c0607540c032070310500c1041c1007162620768034100c08907003040e0a07512469440b01c525444a032240a01d000150780040f001ca0540c40010390200165040141a0ce441e07803540c54021045c0c0000804604264441d840c807415041d080000d0000b1040005400300c50100c2c51401140d04a440740c1910140d80041c1c00412503401818150380e800042a9400810341003c24001501c04030320710380080881030b906081c0414000194040f0200d4202c980845414940c05a020380301800385140d04400101c08124005095100e6031f500c1d904403110204980340c2010400c002216204d0895111000086c04400c200d40420144209401014198021403034011554003090000000418050040b07484481c00451914104810b10082002d8003017008880d40355000100403c04030b215400c214404c4500180b011062950b040f4204680249a0f01400d152550802801c10f12050090 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 142963255 1250 142962005 142962007
    0xe1213090501081006060806030709180c0e0f060a0305030304150b0607140111040b0904090309030b0a0902041a0102060f060303041d0402030d0c0816081324050f040b030c 75
    0x12000094001c5501a04034240a8030190201d104420200c60269000301d00308114103042c002c03240c5001c941c51095030705200300030424009154180807c10882da00041c58581600c400182e46800c030040d190140b000d040140c07405480e61800c0010100090001600715002000414006900100c04c00c00c1410452804103d500b40c000028089801210040d111002e910311a5030782c0147c28412480310281341400d80f8141820a1034000c0903004425400740070701d40c0e80a220301410b0003910300c80300440c1c0c0051a41e85034a80080e592019042c4840224003035800c14140038080048060f4040310b185c4107038010007055a81e95907128000001504464060104200104501210240e1075014090050b1100028200340c0f050610740381c0e8181800003045200c02840c0000303a0f400040f1001000c04461880c000f50160400080764440d010420542c410300311000030309003d540760103030150180e28440030310003401c92805a401c0c6c401c1201e0102c0500d0200020f0103510681000307185c11901c20b01e001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 142964505 1250 142963255 142963259
    0xc060501140108090607020a02040f0b1c0b060607172209020408100207020607080310050a030b07030c0c0302100c0c020904050c031009120503070302130e0106120e1213 74
    0x54122002a0030254400c1e40d0148035401a507000488580c100c80000010140e5140541000351a2894000700a11542c1c850f0310300d49811410350400c500f01100100210505001280a0a030300c041003501203c2280c10b200c006800351504034141c1e5080e83d000aa2201032100c1140804c0315a8015202000e10702240d02114a5412250030302030040c09040400580d07450070488240d240800709001c40c0100c2c2e004000c071301e0040c0c580302d041d501d000d40d02c01c0789651640c6590140200c640b80580015802c8004031000005010441c1c08160040f246a1002c0001000d0788074100c42c1400d22002c0600541e112039000595484580d1203248200100d00c0c108061400f141d0001d01058400e0311b003600c0c3e076030080030000707020300c3d00b030184480c4003800aa04106424490355802034001042d500b20050140c04000114094066011640312899070300040c200706482c0c1d15200400c00b400e000d00340000d248210319800d00c0e050b600c0b0b480c0b0050010301c01000382c50806403400078503512400e00d90049403480400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 142965755 1250 142964505 142964513
    0x504020f0411210a140408040302190b1602040b01050306090114010e030a05010203060108013f060c0914120a1e051b090f0411040908090a060905130204050a060e010c 73
    0x100e40281484840b43d29120b0500030444c4040d124000700529451113082d09120000301390800f01e40c100c9905450441015201c402e110701c503500a036001ca2618034000404c034141d01801a10210045c0c400c40d0100507101c010300046a041c001200e07010f8210a03d600107100c140203440e40c1a190940500d07020910403d90000b19041131f1303203064104c9903690003005210540d0380010a0501600c900201e080903800c01b88010148010503042208003410580c1310003043c800c1e03c22030300300c4071a00603900340001543c0400091401d40d051240000d0400140c25151640c900b1010b14014800014010400b21009440c1e01a0008202c451410850b1746c0010240000360148010781c200c04000389181c02c030310031180501007680c9000f8a08145a5044130400001039022407c0307601120094400050281c803500c1d01a620344509010325034403a103c1040001c01c542c0c084030b03c0c0e080d9002070700d100301d484042101f141d00ba4040d0b40a495031008001d2014495184500c5011044010501d02043e081e12a41c607 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 142967005 1250 142965755 142965787
    0xe01020d021314011704141608060a050604050112020111030405040501080601090c26090a060f0608010605060f1903060e010b0705010e06071d03030f030f06010f030504020f0411 78
    0x1149420071681040b00f0020719596080f030400000382070034035541c0a0354140681c0d01501005000401d620740c030301d5140001840070000c89001811280c07028152940b240545030b60b03080111740d4404054200320000d001d40c00e05020b41b60480c1c042006076030700d400300340d801500c1c5062440701d030000b24070090000103207907a220f008103402054080c028142c0340d4186007a58041d03078004548030341480740c1802540866800947e8110f01050b0042c0c503802c41d52a0708120b40d042002d960070160445090295984540109030700c00801c40d030f0904001c10100ba03540d000c1c0a03090140f03015030b0552407001e0100c1c070700302c4c14040d200045100072480c001610685407003200b02c03102000e81180440001c040384007402c00c08248120080005050028066403600040040c84250f054855074000e0840411032040340d00d040060f01e90309064116141d4917403619101103180d10a049500e180010b200002a08001e4003038882c050056230060104403501c1304400521004e480140f140c0a0024410400c0d403100d120028 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 142968255 1250 142967005 142967017
    0x3010522020a0e09150f09060619020c030f060108250305070801020306090a0e100f140108060601080c040b032202180411040608100504020a0509180d03140a0e01020d02 74
    0x2403100c0a110140c0c10038030550a900502c9503130034908120741c80317040d5580c0140350313902810210385500e1281e0360034020500c50b01501156845010455203115485500400d5951409506030708682061840240b1159500d8082c403c4001540014041025643c5403000e0250068030010004070103590300c4c1d99103894840160720014483e540402400164076003c550140c101003051018011994a42c41a58403901c00001414a040d42e860051140290b242c00c1b102250726101e85400c3c03107603034074281c8986032003045642d140013a40c20f00c00178645140070401c1d501031b95000305885003160b072580102004211900c1048001c2042c80e101c080047ea01e4004c07840202032081c0b00307a6450b09051a1807000328135000ca0261140f0300f041002d100c14680014003400403101200d002c5102d40310303400481c4180300b180e00415008158001004400c521100444c045036801c00d04030b521b03403402084203e04071040003a5600c2c00a44401c0460000f0390250015020b9604241c00146000721150761002268000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 142969505 1250 142968255 142968257
    0x90d140a0302010c0e0f3102040e07080c072919060f080a0b0a090c030b15060a09030209040203101a030c040203070203030106110f0706050315100503010522020a 71
    0x500c5410042550a000310352071200303070703060004901019600080405204404a501581000c4004190303610081b42001c1e000c981240607030b51a0030b810309a880694040c0c0a9101c80178000c0b40400c4803144030740a8544035142d503100e01d6080030402d550300381680304881841303808942c03685455104962010b02d264054800801da441800d1030000110301942c0d4268020002e4010300c0400700050f14001c9050703150b060388100160071a6944c0b200c02d42c014441010054003c0c1ca0000c0d02004104400a88500030f1007090ba440e13000d2440003040080c64422800300c0800078040c0741040006050907092150003d00c000c0030303034140130040d103a00c1d41210006281303c1e00e10400044045c2480c02c0620110410b05802d0b0340562552034032081c0659280b01c184900010810041d80c1101827050620a184e509404042030350b03042c6a4030500240300d50400e48035a0111110b010b408881c510f051220441c002280e5201e981c19a0728180c1080aa01400a0144030281081c14141c2c4e00c2c0302e10b480102000302903 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 142970755 1250 142969505 142969513
    0xb0403120e10030902040c0207030206030c1e0f0c100509030d0207060b0d0606061206080601060c020613060504090b0d03020a11011718010c02070b160807050d120c051e090d14 77
    0x4ea004020545845580501c29500b00c50000c0c800740c3c0703801e01100e50109941a20035643d0411b00344104a0161401043c0396203040030848840c4021b0420003007208010b20802c441c000200032841c1001c50f2000d46686d4070591040208140900103070b0080c00c001409901c000551403900b6001c28a4594120401c03103145070f1741e01c02402103980044040188000145082007101e04010301c16907941018001c900500c511000d1500c00c6584400885000911115505210550f14580581160880c1c0110740c2e146d82440100405402c004101600160f0182e0040054072280c1e00e40c000f41d00c0441c06990b04104078030300c0d4501d0b01d825003550680911082c58006400b0011855410b08403107451040e50b0840d082044c041140d2044501036400d011032504848107000c2840c54021518811032034014458041c80350090466130b009402100c00c180300000900c45003204110854040c880c0340007188142904004029003007101c00044c01040e04040c04a140b1003081c2d85918030911180000e00d0040c0e84 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 142972005 1250 142970755 142970771
    0xc10090201050405270901090206070611040b04030602131a1801030f06030503030f06010206040201080403050a020102190e0a061817120705030a0f0e0607030809010b0a09240b0403120e1003 83
    0x6100c02e007141d4006c0501000300540b040d9030740014807510803d00058036440d142d5001d44010313500700040b0750080a2b42000d01c2d90303580c2d41c0c1c60214003940241590421100780c3c84000641d14038064008050020300c00c03403042c54503408420f858010700e4a51842d90400d540c4046a4a0884e0580b00d108043c501a100444d100d141500e40c055580380020405c50440d0006400e110050342c0000072660080d41c181000c80e00c404038203104034020b0082c448070a008218001c10301041c01c1d000a00000140c20a640d000d00081e1102e0f000d03540b105910825003001004480100304804ca0080080300346034440d02601c54450095a9901d4240c000080642d615000021a400c0c01c82e0421960310078900300d0304124506a102d640041c51034000d0400103428002c54900044e0044400c0d0710800c1c504d0320080805181e5511882c2143c0201000780100135401c041c41d414421582d12036011104881070200c001e49030a0444da503c07940350090303045441c02d02c08080101c0355580d94030303981520000340b1030340d0028a0039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 142973255 1250 142972005 142972069
    0x10e09010f020a4e09050a030e011209030e06090411070305030f010906060207060f021009080d060e062b120302250b06010522030804090b01050c10090201050405 71
    0x3c85105140d05100103a1480c941180c2d2410301801c1c12130010100e800c03024421004104050506034000800c0c0c0c2c05071054050405400113512181d0100030b07a501d28000040c0580b940c101c0e038002c14041c010400b00b0303840e1400d070f1070a80300400910b0406440414800c0340300034010ba06803c140400ca021400100402030114000d690003030040007030340410320105240c210040d4850006018980c20040789902c3da14020380200107800b5080c46101c410002e110890421182e1900007211100c0081d040240000d603440e400714080e4001c0b84010201c00e1001c04088505403101d240e10f590719600b4807018000000700700c9020345182c00520a44025075954000aa07401c03812234181c00c489803401c0580344541c04500b002c008540d11200a003000d41d0f03100720710000281e040c580140f60040d0048142c0020080240900103001191000041030040400520054030f550003a81c141e4411540545030440081c05a0740002141c0c038018144585480e03120404101145105000c28100703042c0401c0f881050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 142974505 1250 142973255 142973297
    0x6090506040b0a03031e14070302100b0625050f2e02030103120e04020409061202090a09031202130506030703020a09080607050412060209060319060e01050603010e09010f020a 77
    0x4140c08841118a0b182156000307004000354a25206c01289444404c6030458002c0515051084200d5411a203801a07807030025503d187d0003051aa03c0d5013491344406480c1410002c1d55402c045100c540a89500c03108000700d41b00d1248002a5501e00c1520450900c0039401d1101c0803015051a00b0340800310b02904841e000640903512800095104000410214000b091a00744161040c9000d4007060302c070800150281c010ba412038030080e07241c00030005520000007c070100d81032080e1000070090341d5030705103442114007900d8080c0100d80041e00d4250401216070090032008008105484220344910200f4819001100c04901090780024154641381e0010740c4040206940340040c541440d01d502c0040003409144180c42042c1e400729070210410006e0780541d03228040207090107071685024403030b81e40142c19180038140b60511f011404105420318041041c14ac0da0058405032a59103042a2040c80380d4006120f003405550f42d4007017a0b90202180010644800c10f40c0c1c440b001c0b8001c2c40351074a08 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 142975755 1250 142974505 142974521
    0x12070e01051908040201020f010e010b01030f0917030907091a01110c031e070306050a020712020105010b120a0902090a020d060b040f05010f0203040f03121101090f0209190609050604 80
    0x140a014000d8180042c000040560a10007628050240b900d40b880181c3c40c1446502c640e180070350810200e140e0058056100000c1c2c1d0345c00341c0c3c05200001c40582c040c0101e444080010749a40100c100f03840052007110010b682001021003265101580d840c2c5400c22100200b6080880c0103015034a0462980e21001110522600802400721988000000780d03440300d5100c160304003c451100c0300800728605001c0d20700215000107084c8a10301d4400403440096210220840300741035803000114a40d48148103c5041e40d18043c0070515000031030000d407088410003490030512548601c280720040e21071f0444280229880003000d0f8907203a4100c14102510029001100c0f44503050004000c0c0b481c0c0521014225003080c00d01d400601000b01c000c90461103960042c1c41d071109407503c0001005105010744601c45900da4403001c400c0d2018081c54242da58481d00070b01110340c0c2d6100000545880c01026410505182a6160301d001648e0041c00b41c401540c40200515030382c81c10412a41018066104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 142977005 1250 142975755 142975757
    0x40c0201020c060f073e061b07140a030c0209060f0108042009070525031d040605041e06080d09060503070e061b10061214010207060212070e01 63
    0x7041402c425a1281d88000007080400d150700c010b80403419060240c0210050f616803a1035900c0b481040300e40c140c90f1541650000c48086002501c2200304902c0440c109003d9103260546114495001d400010300c0e800c072040c01d0350180e01c2034804801183c0e003000f0a002c4203102e034072107020758051401008080703c80108500d0040c5000d00c491403503a07030300c0300c02240e00541c885031365603410ba40d203011100e00448501120350003255400a1264041d001006010100c2d1095900010748411704685245009400e800030082046140f50241e0200d80310214420064050000a103c9a4450024081c0c0780055a41c0c0c00111b905002100001124007a12000d455003000411010b844000003e003d5036040c8900c00c2004030210110b50003500c0b030b6a1800320504010305081c1c60303014200c022098440d40070180b0700f0318410420054081041801284104d600b16000421000003030b8690100325850003d0b0100595401c220071000200d503071002d0b0060350b142500d2600b69181400b0301074014400f800d4018 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 142978255 1250 142977005 142977007
    0x4030305070909110a1b02040c0c050615010c200303030a0b1305041e060605030d050d0e0609030a0f020c130605010f020c0d021c02040e030d0c0c0c060f1403070905040c020102 77
    0x70840454001100c5900280d03186c0248107800c515940340903c2000c0304c00035440350a2482120605a0280c070034001d0701d000700255003441d1074016800ca000d442048ac000d02041284d01b0040c041014285400215006d01207800d0349102e915000a003140d004a421340d680d15501c0d40c04c55401d00306181c0007003a0340c2d5025410480750030300c3c5e10703016008059100350284200300150750a040065980006e0001c100c0030707007154024a00380c00e01914035040191090703d2649445009503ea031000102d42d40191000400f45141070030608040300c101e140c8084c02c4065102d40321104403140c58102c1e80f03401d09080c000000800c503080070b00040c412094a22041e00310b612102000e1015960340042c00b116075030440b107404068600c415000303200030040b400a94894070300009010720244c080003d1081402080c020011320090020039511541c0041024050440d215002c2c00421301502110662200a0401a0000c500f5580f4211203078030031500c1c08002600c42404100608045c05484182030303082c0007c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 142979505 1250 142978255 142978271
    0x90c02070b040308040b07081605010203181518070f0305030406020606090403120f09060203040b01030c05010c08040b0d060b070501060e060409120807030b1819140a090203070e04030305070909 85
    0x4031304c00f4041c0c0d0290384010400040c1210400c050071040300d40e580c0d114402c025500505080050007504102da92405602e140580b0344010400424120240d20b4021190549a1684140e507150f605000342c0c0d500c01e920812102007002d1072148411001188030314020b5544508210380281420009485580105001003d000c00207800c800388071a00f860221000a07128521003880c409050b08001c040c01c103e00c00014042840300102c50305058038010020140e485564800440c1e0684900750080e00554041c0000d02810204c9401403401c0c1c4034107440480e030192640001c480d9948402412520382e0742d07070340c0204554400b69824036442602240d041003124055115070301c50070241c02580e800c0015403400142018001c0d44010207a06000c3d014441000000f80c040d0001744060b201581c40103141c0380341c1003001119004c0d01e4a541940d00c0035020517100c0e1804180030300484203040342d0600500310302040e04e01e000c181252003540603a0340403c490400722000b6042000303540009141c113040c2080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 142980755 1250 142979505 142979513
    0xe1509151003110312031306050c1e031f060512010e010b04030303020703031e0c020606030d09050d0c0302040c030609050718050609040b060f0405090c07170304020d0c090c02070b0403 81
    0x101c1d40449820103001001c4001070b20009050401d10b00c06010586008014803c100d0000b0900d003410a119000810964071380d24243c46150207040c0c2c0464071181c0c950032400243d0f1030440615040741d1041000c101a96001900040e01001c5401550003d8000302e0118490241c00891030b0060030307000d02c2e21085506110500b0401e115601010f414144c00140b01c408040c0700c0c1d40400c003001c00d07513031400308920225501c0304050714100f00300078014407402c0c0c00710303026107808181ca41801c1d505899640b81d66241800707106c25810004402c0d180741c50038010000c0540c80e0742c083e81104c1201c0356800100982001c030702c9000c503040a0908010002c83d000c10801c002c0c0c10b40b0250b01554011038900e5100c01242c0006006810318039040340c0c1010001c990f040d181150712002e070083e174408545404003941d03050b000c85424020407801802811a5261212210640700e004580290002d0301c400c011010326220714101c0707a40c5a00806020b40eaa0030030072042c0b541030210708081c01e555402e03103240c9441c58035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 142982005 1250 142980755 142980781
    0x804020607060c1209031229090603150f040309080c1e060405060f030403030b01080c2a030a0809160810020c03040f1202041a03031c0e150915 63
    0xc0082c01c00da5907500303010382d6501031142a0030100c0300c603c0501c001c10240c0b400414081040150102c0f250810606d542c40c4000402d050022030541000d04100042250800000540c0540910303018051170400c3c141c0040190401c038822070300c1031a0f04c020741c00d10345030041003201079501c11002a0800041122103070b454144980a104030075003410114074501002550f20301c030744c0d401140d100d1000507403100315103801e41c003452042c2c0c001e803810000380710f40c10010f480303c9004940130582020304000d24891002001140740c200414905010b60300540c6ca5401c500d9544200d03e4840441e100b0410003115240c10044400c050005040106100d440c0421032595682401c542184442e00400d14010110003041030720014004100741040c481c0e52041c58a5401640350340c164003650900c0d40c078400d042c7c8102080e1640e218054021840c2ca507400c00b06140814881383c102c0071140e01c0d1048403441210811115040c850000000344441c14071040301450200c81594600002c904103041000c5644020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 142983255 1250 142982005 142982017
    0x31209150708040f050c0307080106030c0509040f03141b010b0406052209050c030706090618050a0b090d0c0603020408010b0d020306040323031005210712150c020c03070608040206 79
    0x3049074203207801310300d8030606104103014a1030b014400c098001640d031405401c190b046034081d0304040f07030a517100e00a0281c00241140c001c3d1241160088130b50001c0e209280142c0109055140b00f800c0808030101910075100c40040c90645030344640f038040320340c985442444000c1c03004a5100e01d254100d0240e181c820a00403c110300f2083e130f10240c038424400c09000c561a1400c00500340d8112549610001c0c1c43c451982c00343d403001600c0c120385074020f441c40b800e59000b520ba0042064038442e20f400103000082e40501e8666810517802c410001c00a420703a00f84401074041510090303250f5080c070000700d00315003611240d1445003010b502900c0250b100030551a400a03014541711021070160202440c50460041c4c88400d421000010000900740c4204400181c0c0c208492100c47c00500d69a07109403500b03860310000903600036030010012110030303006520341288641490188440c100490f08100d13028150640302581040c00b00326043d02d403c0c801d482c05001e103030070131030b01c035041c190041000d038041d10b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 142984505 1250 142983255 142983263
    0x80a0809060f1503070b031317030601021c05090d03020c15030c0403060b01050c0a050d1205090706111f09030e030f030901050306010c060c110d090501120213050303120915070804 79
    0x22166410213031400d00c0b11101070070600c0341c020750b40e003889842180003003000341082c0d442042070b07000c0000390306d2902c040304d0080805a0090907081590305002d882041c0108800c0c082c4002003020701d81c580c450301d58410041d8003a80250110429075014059200e04404120078042020020481645802401c0c1c40503645c200200003290103008005842034410765540300614414000c1e544100000020485400f06042d52880201c240408040041e82c0c01540c0804080c0c000480030b110291048a110342c110120404849000c8484c031000d9410070042c0c2d1881d016161522103900500d1b030081982c14ad003803002d50003043e08800607815583c403402603082d150b0400100201003483c81c1c1c0b09054001d5425000001040700c000c000001804452001240c101360340030b2170748804c0742d680c00313000c44c001180d4041c1c48804142c5005000b01c0029401000150601c070f07550f11010406840410280800021048201444c1d05040f140c1c036182042c00c0380102c0b0030100c1d0808021180f64040c61a5403c00e41c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 142985611 1106 142984505 142984531
    0xf0807080106050d03051b0c0a090e01060b09060a0c022704020906040204120816140303011a030106090504051801020f0a03060e13030f1803080a0809060f 68
    0x131180080c0105400f4400310b031a402c40071054061841c0300b034082d10715001811000a80c904000c0e0490380c50b0b16034034015440e00441c05d2040001a0a4071200d1601702a482400a092442550746060070404107071010011901d43c000000c1010300140b001054020401c00315945e221012503083e4400c881c42d00101d103003811319200311001e0ba00c040d036a10942d01c200d5112210f665108441001040002d000e808002c030b050502844400b40d40c401c040e603900c2d45400180030240501c208100c03003031700c010401000381940080261085503426a004101d81d40c503021452203180f10a00640010350000800790a40384410000300f000c00780f582c404101464032880e4030589050121181c80d84140a05903040121f4001e02002c440d2041625011908104145108084422582c02280c00e600c02040c4e003410319410030700041c3d110042400914403071400d02d51018075200040c00341080b00d14 = true := by decide +kernel

theorem cover : BRFrame.Cov 142805755 142985611 := by
  have h0 := BRFrame.cov_init 142805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 142805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 142805755 ≤ n) (h2 : n < 142985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
