-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0719
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:19:52.354085+00:00
-- url     : https://prove2.me/submissions/f7da0e63-71d0-4a48-b610-9b57d6038f5d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 129136690 ≤ n < 129316546 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 129137940 1250 129136690 129136723
    0x702060d0209060f070507060801050f01020601060e030f070803070210091202040c110a03031e0608120a110d02010b0a05040506011b0602040906060206011d01060f050c160e1801050702 81
    0x107200352907540d40c00071158081022520b494030b40c06541441c6540360350a010322000312741594004035140c40c14000c240050001680280707840da0030a1780c2128a03c1c0020790094141c07040000348080100305100d290040d040740f038020341c1c41e114180108240c0b800030756400000d121005006210b80c1003c68100015550144d0f4042207035002041c086654030a40c1107034070014000d0012103020180d00d03801c4600c10400d0015102250203000c1100012210780e4420484107074443c80c2010240595540580998802c0313080100c07031042d101405a040c03054a0381800c0042c1d640300c0401600d46080603054014000c1524100002d107031800000e85007000c2420441034042c0b036046207808002040d01201c010701110f1000b8400b907951684065607604080c0600303101e048a11800500d401c2e50f00c405141201e1165507250341011030100140c459034089144103015000e0b01d150b24100d0070001038402d00400c0041c6854180340750402040c1083d5545500c2d41a85034100018801190360010364015800c95202 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 129139190 1250 129137940 129137947
    0x100509040309030f030507060216030306050f011b020303120c0d0c020a020907081b130e160c080a121e0b01170105190801050906061003060e010303030e101a010f050702060d02 77
    0xd003a101800707107d0f40100b0342c500004410071004203000c0c0c5d0110b014071a81b0184182038440c010004003550444139140011202014400c00203403d080784e500c0507001805681c80d01c41140e0390384204a6048411031200800041da81c07100305c5d410300c81c0900c40341c4284090302500e6002d5000880c81c5034041e101204101910300400c46060242030702101c140f0040c00e5156807a00050440008650144109000040c5d4400016034030307032034000110050300701c50b6200c401880700ba94804003035070400e81c1480308004121128080b0f0b8041071090500c041041c161641541c0d480c1d8500340f050381c0300440380c0307170400c802a0790403190718003500000c0e03042d103030b04480d401449000c0c103401107060b0f0080d5108104542c00d007010b00c01c041c240801c03464007450050f20096803030102c0180550075140240b0a150441d2806401000401e01c6548003046c64071200d0240c07021000384000308400d581881462101c84132021522800355a000740811004040c50700788a800c000b81c40d000241e103409040b40d0f2040458002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 129140440 1250 129139190 129139193
    0x50f0f1203190b0a0e01090605090411090c07081602150c07050111100f2004061d01031416110708060a0f15060905030705090f0403030905010b060d05100509040309030f 74
    0xf5005405150006070101100301d40e03d0303240b010020400e125041304186050300105a9042c021012071043d5005507000d840c1e031f24a181404081c0e20014036040010714144080340001d0b50000051000c1c04c0448806400d010071070040040e0076100008104200e00200301a12010501081c800221031003400d041c2c20394040700c10141c0c1805841c4004054450ce0410b0400320450705500018030324035441d0359598401542101115244503030300601006c5881e907482040034004241034882100c5062402256100030a01c000440180a45461001d454155080450030742c0c420650030624440000405005240c440300c940c031244050280c43c0341580303800c04040d4084d019000a02000039400c01010025a0303604010310b4400140181031003401003076030015182c58030688050040041c06031500c420344403660240c004001056040300c03a0354861501403880e9590740042c0103981c1d02e00c90040340502d40f04030302400d190710541055102c0c00c803900601c80429400040101030701c0d8000104c20484405 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 129141690 1250 129140440 129140491
    0x13020d0f15020c031801020d050403060c0302121302010f02011b08090f070803070516030206030c090d06020a02010c080108060c0403020105070507090207060f1a0f061b0109050f0f1203 81
    0x920807040c1040e00004020104040000080003600a404070702480c40c029800126140d0740c400b800000001d20901051000c0360566001000710141814010724010012881401c246000c50341c0c20600800803481b002596003004d102c1e29034029510080210f448401c003d58114402510b0741c004025541c07001450200701000304800e800c1d45441114001e035901d141a07a40d80e400340c1012610340c05104000440300822044410959034000c000904555a4081e4038231a03420050079107510030443c174480404200309100400400758503a002080c00010740e50050b0803150b040c2d0000c031241d48820100a418840001542e0659909103041655030501d4180f03a031900c110381c1c220401d100d00c00580e02c0200500790340509080f85034010280704140c3c032010303124050710513900300c0c0c2d403c0005005800c0461401da80142403c1c80f103604000d04c00020102401d00b140e02340c8000300e4142c0e100d40c850840400040001080e102a0540105035002501d600e03c0090301000d0510480800c5000500500250 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 129142940 1250 129141690 129141713
    0x30d0f020c120d09060503070e01050d02090a03121103070f03030903110f03070b15030706050d1e020d050c0f0d05131203090b06010203041d09031315030513020d0f 72
    0x4140701009181d40b41c03400d07160f0710b0020207480810001c400020706140250181d911805190b1115803103540c44400664286d4065074409109a0f801c100d4107815a9500d81c201d03000d135005400c2a02c07000136445020b003015070b4035903122400b0390040c002e40d40024115030700d02c0c5026a1514001c220701284d4034003a95000403c0d01002d44902900381351140116000002c0e14540780146c940c110b80b921200708548059208284843e0144c000d0b003c02d1112a000e40001c1403003c048030030002e65a002e000c3d452050000e00101c400da5160000340500840020b030050036000301c6132440d42482c1420207203401510784036090708042070949070b400040310341b01c10540c400c00081e0003002c411010342d071140c00180100401c20080703508400d003801107481944000300303031019a026100220f103203040040d40c55008401c0103040607224401040961712190702580c2280052071190514146d40f01d03d09005070550f10020010308a041007075400c4005644c91102401c82d646d0008900c2ca6403080b00c0c20000750004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 129144190 1250 129142940 129142963
    0x3206040b0a030b042910023a0905060d11160b0402040c0f140c121c0b0409030c020909010605100e011b0b0c031012060623030d0f02 58
    0x100031034040c2030140c143d04203003510202240c00700000604800303c40603910f0340f0880315050f98111800c0340440d00380750072604a0700407a801103441c6003400c00c034000d404090304040540c19040c1c05c403000082c62440307000141119000e0174402545070900d00803d820f40140f045040c04e03d900c4207124049031840300c0459000748210b9601000c41a8a8240410541d1094a0403405903181000300d06086101b102c1220403c44240e4480b0310f4600154003001103500503500e801054040c424080201d00e444100816031041340380042400c0d103a100d20008211452022943e00881c1404803060000e035010501d0b46070355504450f2807882d900e484111a005107070342d8000741d8001e6440c02c010200c4940204402440340b40981c0c40760003400070b64220310103403000c9010003800b1140407004590a01c6111010b1903001c1d00590307583c909560f9400350071101282450060710032035540c0300f05005003229150101c020380b2500c0e80c074113603901a60010a94408081d69100308000044174604090b9100b4000c400032170 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 129145440 1250 129144190 129144209
    0x8120304141b011b020f01030b061b06010302010207090606080714070b0c0414011403130f080a0c0c0b09130509010b04051801290f12030a03050709320604 68
    0x6042071915141c402d03036840a408540104059852041507107003d405560b80a80340001200400c00190090310b1860202d503445181800704070260182d1b1362080d40a80f01e86c1008201720f52450002909144042c0c10031060141800024450980c04c40b114a4000402e0302d4440c820541107120121503008441c1d0082c110484441400109a080b5000d041681c01d03119000450140031401942c8103041181d000000c0d0400340001034000410769580392805018043c0c2000e1034015a803200c0d2140d04c8a012003000c00c1c01650380c1024000038800b404040e1807a0882c1078030340001080020060b40416070b003040d1359600c43e00002c14440e001c0d0071404056802620030700c40307030a00741a901107141402211000f29880d1222001c1c4001c250b4000038072244110f40008804503460052141d5107110101b115000041c042c02c0745400d0300104014261041144e4002600b802d01c40001812580700d64050300e6006100400803203040341000100c007401402404900045042c0808580179026551007507803003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 129146690 1250 129145440 129145453
    0x50a031b0615030c0603060e0406020c0a080318010b040902031c02010b040903030b120606060d051012050307020a1707140f10020a03030f110415020c040c1701050402040812030414 79
    0x1403040c0a2801602c0c4100d9481c030f04541c03103100440c00c035401fa21614001c0c03140a00481c002c00c00035801080c400002005403440d4039620384614080d40c0c0705a03641c2c03104100035409031006003020f2066901c2c140b4201d0341400718240c1170700001d03911528280310422107548240d4110806000b5403103525145d2010f0b2041c4002c0e9120f05000c0c1c01400d5100c0e00074054a20300251140040c00819501c0c07040000030440c90414015544527001810300400341502e072440410049900000503407800313401e600c69402503584217581d1041c054943d10640c09080c009001030604220448003080c42c03400e4a010700380300c00385000700c040040c99a04032a5215074114514502110745607501142c0b07100f41a0190304e040c03000c1000d03107a9203011150300040008628506100c1800750b01c10310703083e5480111a500c111101d180c2c03040300040c2101c1c00740403241c1c0400c0003201040d00e9592201c01d03850042008640440c242071414a0443c4c817500030310041d040c809800000141002400070310800c0c101c81c0241214071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 129147940 1250 129146690 129146711
    0x10e03060c0c0105150303071b0305070b030105030c010c170705070302062107021902060a0201141005010e09190905030403080a050a030b0616030f110609010504060513050a031b06 79
    0x1280d1203030b144241d5a508040c00100701c2c2000c030500c84004071014001b1454032075503448405100b00b42210f0310580d21901d20000000c110100210b801505170014155500c2d4075200800d450012038071b8100f8144540200904085410300c80c554214004102c249a0796500d586452400d00d1020f8100030350040003c0795202c10009000440e0302d450000c0750441840da1100e40c82030b40c0d00c031103042d422410210809207040050800401030800b0141c039000201c0c14020070002c0102104017240d4030391484481007001c1007c2c5d83d110005c102281c03c03d9444425606160310741c60f544190711065031101540320700324a1308201c401c0048400843d041040e40b81c4440c12480d00410a078010054840043e0500800300002d14090044550001c10b11800040644540d030b03007034684074080b00b03d030003c0c0141b03129950540c0101303000103440f4080350000001e180c609441c05604a40c4050308140d00d0b0000c80e2410300000c0c00005030404c0c0c06815080c08200c0e00486003929a0b440400b443c000e003038a040094505 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 129149190 1250 129147940 129147961
    0x30c0604090207020a170c010521091506060f0313020604050d06090b10081e010204080115031e0b01060302090301020702040e060417030903120901020702040203070203030712050105011d010e0306 86
    0x441032088410910469407402e0b0480c6c00022594030f04901d41000380d600070740c1e6024200409076070341d0b800c5001d0001000e44040c14000b0302c007110750b00ba0341d4000150701c150b82c1107180d000b01c0e404101121018104640d048021509010040880c2a04bd80c0c20540001359560681a6401088020304110203d0203502d07248028103050f000880b104044c1c8404106100f0042d44140141d945880061400042c12194601d440341c050103013103081c1d5420000800c1c3c850003070080840c02c0d08250583c9a44900c1d520785281d580703043e40c40f5100300309140c010400014124480c1581114100d15000da201d108060002e80284aa100c00a6010f0702e8481030440842011904070f02c514052081510a5640c04040039800d01c400c60341e1080e15041003100710125035096115a4001c6050000103080c9442ca60104080743c2c003e840380405a40302104201a01742d002000088411060406001c4d551400001800c031002c032006035484024009a0b81d2180d0744200c4000b500781000808603061030401d10001e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 129150440 1250 129149190 129149197
    0x11040314032209050a110d02030403350c030106140310121109160e1c120306180204120308040809030615120c030705011b05070f1d10090b030c06040902 67
    0x1c00e0001d04200008014800e0b9204d06c80c403000341041100d00d080c00e5080100c1c02907000800440602c2070b0701c0c5841001503522000700c200441c061100404001581c040d2001d0311000814501c4000030400c01031240c00d80c0411041d08410703454004a4482c1c40e0009422100070468220000940320044a2000e01455186040c050002520400d040e9100d00003000e406403410bc1030400480c40c03401365040c090038140b95100c2d044903050b40350b0151401958560205080c0342c45001c00094464000380403800c3c001c40400a42000640c003103103031a141801d0010b48044034031028060040080000c2d0a0040000c2225140030b4000c040d0b488503d0140a9034401c400da50076050f0040013a0701e42c0210b0030f9000100c604c00140000c0c0100b461310b01e4a401121207400400c00c030521034402040d14000580108450f030090003010b4450802d03241444000900224070700359509440300030b41c007404540d00d18010400d00741e989040c408140300501801191509103545030b00340c3c0129001400186808003903000c2c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 129151690 1250 129150440 129150449
    0xf0105040c05011103090d021002101e060b040f0b0d0b04141009060302061204110a030302060106021005010b1905090a08060f06090402030303071b0210080406050a110403140322 78
    0x50b5400b40e2002d1384115500d018405010750070407600074104000d807034418181c2c24030711801d10480d0340040c24a000d20003541c3d2034a42210003000022509100c80401340215006854203400b41c90801d86812409882004035100c0e00360a19000a100c84002035960000d416030310307014000384898130024010302d1580340105d5002c1c140c901003100210310202c281c064042103135002000181803029241060007010000b46c01224041c800c00c07604002d40d19103002d1400294007a070041d20256150000190400b403d0b010040e48080c689001880b0204070401510b2048880b801c0c0d8007202c403040d0905858510440b02d54691040400c00c00251070b11000600c503100b6003205004231806d407208400e110002c4019030b00203501d03400910002d220310380301d042c003041780c401142060840c400441e00803540702041c41c070141e070009402d4810002403001c24020035030000e221840400030b052140014403080c1c0a9070000400e4488071401d019001c01e420815500040301545c009000f00e20092a03c0701a0007041c0f18 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 129152940 1250 129151690 129151697
    0x1503011214031303020609040b0409080301080106050916030b3c060c0d080406021204060f182102010f0e06090d14030705090d050604060e0c040b0303040e07020f0105040c0501 77
    0x400c1c0c01e079540441983d5000b07028002e0303403803d14196820051560021002e031504159a184c0c1681300340c0d914010000f102c0d000740380c281d40c5c0b5410070780d4072801e40c0d12603004140100715020610600030880c007502540789400e8500050000c050200044d100b00e598100a20410720060051500201e52400d45840b05404115611040c0700581407201c1da0296024480f010781110b112401150301a612003a4001c0c40b8110061420110102c000c078182c50a4400362621030b540d0014081601c40c038030601064041500c145854000c80d0303652080d000e03480010880d6185034000020424900035001310401d43c085032018440000902c2c8803650b204002c40e1f40d0620380c819603000303200d40d501881c00b4182d11002c0046c1d46141d075807000e50541d226440f485a140d0081d071005c4144010540510240c0c3c00f030783c441d03440070400040302080075280c05902c9540346d101e00e180154040459600104840403a00e00621203240c90340c401200380d040600c3c200ca107801550034107040008120b42200b0b180251032090b203 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 129154190 1250 129152940 129152963
    0x150e1008070e220b0102100906020307090905040f03140c0304090b0f010f080a111213020411090f041109030a0318090b0303090d05120a080907050904030c0b0615030112 74
    0x7810080202a0003a80c00d15404100f028140900c1d11608914003a41040c0125220002c003c4105002c66000d010103442441e4007006012816a203c1c00640082110150500850030262280203406040e068010f042c01455a030b45c0c4000350a1005a45041d62007c003565141c070364070448903000d0050070710854815445012000350641c020130b0710500c03030398080c2e132809003e07034810745900010b000000301c0551207181884131700704038101c040056102d4641c41c481346c1100d0445105200588003403100c00d100107102444500d540f03448605500c071084400702c40c04145048481a80c000d030340704418810340c142c000c00084d4010305410070344449038141c102c40740705a841d036101c0041045803008d010650780f40d00104401ca42600c1c0914030f40d00540c0c040e0050f1201041c400060301e55541c090784c0740c00c000ca0030690130001c0d00354007440010000d11f0159080f014514095030010000302d0006c1c002040b02981d4030228074252960032503242e52048544a143d92540c60758180156004040011282d160100307 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 129155440 1250 129154190 129154217
    0x60528050105070302061308161208070201021e0702132c0a0309120201171302041802031203040614130605180c060c0111030a060e01080a020901150e100807 69
    0x100b080300d000e103801d07601801d440e071186010310007403110103d82504d68038414040c036030030000350314000c0e00301e940f040e01041c3c124040700034041c1c11301900400d1002564814050300c400100801d072582c40c06482d403105666140d110740f00007400503640d82451000180780201c3c031052810705064840d50000d04007002c82140308800b0704280e6036001c60100800182d400c0d0000c01402d41510a421803452050400405213004540d000803d1103003241e6284e2500b045000080039810b0a1003810032280d5202c46549854080d034011076900c400e41c0310b203040039070f50000c009001d200040e4410580b00040d15000303411420542d05107200100b07000c0c4269050303464480807440b5952001500d510240b03c080c06403043c58603500c10004540c0090700070007030b40d541300c110032021080400004c52086040d0500002c449062880c01c076280501600601080e611868844015036100c2a007913046544201c001300400e41407440032145480f4400300345401080c030030410403003203402c64a150300c02c1c0d805607030b130006200d0310 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 129156690 1250 129155440 129155447
    0xa0506010b040f03060c0c0203101d060c0405150d020a0315050d0c0e090a0507030f03170108031c110304060501092f1308030f0307020c010c150902040605280501 71
    0x442c45401d0180303d003088204001407080c0c201483c20105801c01a50340d602d40c1d00420b08011402e0090040141d070340c000d1601010210750741510401d0388200404940c58840c1d12800746202e680211407040e4030b08144680d980c3d00480449550402594080d5103070840c488010b00907100741c20301c8064541d0307842e20200e602d041c1100620380d16900100d00003d0280307058000001284081c1010003617020f120041d101142081080d00f0086110700014640551f9600b80100018500d0901e060f0098000d1b0040040304400010395940b1010010900328046600207a50018003c6022000320f02d04c0100800043c04001c0c1c0c05641241d825800900c03010741180c4115040b25842410102d4054400055159103003004028003608000072620008640e2104011851908031441010a09000004101090f40e05003c5c21007560750070b0804d040c44038a256282d1601000350340201405070742e01c00c40d54066507203580250303008000180c80f600740b2145c00e220310854501c154680b03c61070411803c0002c0c05512 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 129157940 1250 129156690 129156697
    0xf0606090a1413080405061b01050906062407120507140c06040e130c03051e010b060301032604090c02070806040f15060b030c090424140a09020406020a0506010b 71
    0x140b000b08085681e222860840d4484074a0420303100d6500a01c008122500c410000b803010640980040d4229101214111b00f581d07801060f00c001c0746c1118080c0079aa844420110000200201c1284850802c0da80402e40c80d02810724050300504c400007023404541c0d0440c004010396405009801c20030100031202969441103840c009030080c204000801a01020400a9401000ca085292541440c0e911404180303140303a0015200c0d40c0200e403501c00710f503543e01590620b05070b00d030300288420414600000c003680014840030b03101c0f40319018408500005c0002034111114940302d000e4270755840e158540010480542550094031442e0b0010500c440c0011340244520343c03042100c0e450804660310031a81301e03a4001d05070b841d6900c400d40462941905e901851041c8541219951600d2140042201f52030100f261100d81140081005104501d0002c501040d03c0034450303100019903018000c6066010390340d01094880381b020401007521a404101c1c84120340c000c00481d440d03030b6211a00c0784074611 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 129159190 1250 129157940 129157961
    0xb07080c0307030e0c04020a020321070e060903010e15010503070e13030c0f0b0f040c060305040308040209150a0b0a0906050c030409051024021009020105030f060d050f0606090a 78
    0x400c00c0c000105070501c02d8014040b42440b0a007500c45030041a0041000e0380c1028040700007503000031034460010286001f441140008044840016003000a0040c000050101c0c0c05070048ea00011080700503102504040900c3c2120003c480e42d00f5058010010b80510a0107840c0c82801800c2000030304407071156666004001072200701e00c00588595040d103e12019240c12108150032116031404070b01e007100c1643c07180c140256000d00324601481d14040243c400d8110350185032034181400301080e8490f949552042e4103945404054441c0101a02c0c074031800c040e8280c1c041403c0d2070108000a201000d0702844560340ca840c10b440d82c03641320541d400c0c02800440d60050f0305c1803008100294042e0802d0390000c04580f8480c03009a00e0b420030800b1841c0e800420740b032001c43e013440f400c1115410050f603d41c4c0340091000f00b000c00f00581c0000c00034072001d0a44c0c403107824082d02040150703466084045065034030a04848016024044030750b00c4071800c5510754803c400d944c1c0051014100703401242000f1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 129160440 1250 129159190 129159211
    0x90f0b0102070509061f03050106030b10080604090206090301060803071110170403090504020c030c060a02040b0403110a1d01061b03080f1005060a0e0f0f0d080c0a0515040b0708 78
    0xb82c24402400700c0020000d00c800c2d880540c0740c411044003000d619800880001c560b0340800d0f070b98140031000e030030b8411140d2000d01400034a40840c0d0010b52150038140c101c1c204640200f2102068000100c007401101e03074480c0c5c10b52a080e40041c0305600040180452807003a0700034154221500b08000200191400800100365403401150b25440301d410650743c440c0c803038107010000c107490380301240032604180c10300c0c1400d030f00025104044040400141d036000c00000707800c0d0310740b80c01c0001e80c0002c1d019503c03006001150303044c2d0390780380c80d81c856404001500104003074558003221400180c420640c2032182c4d50210f0400303400a000c01458140100910f078150300d80112a81702c0d071040c10a6520003e00040a0302415038012440782d079508003c100010981c0d507001c0c0002d0341748080240c0440c1c00035146100c0c00c80400350885035282c800c107080031140c001c604651605200000c803420485403a40c0281b07035009111628000c5c0700079841450141e4003482000800e652042e4044e5002d070001e44450915 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 129161690 1250 129160440 129160453
    0x71403060903031306020705070b040320010203040504020f04030b2a1810020f0d020318030619090309030605090a15140f060f0a030b161803060b0607080310090f0b0102 74
    0x313508050f910590f400c2c4103080c0140341018988850f4101107054010b00809400090104140110360130001100340008440c0c074108040040041d540c0d216a20a440c041e90300424000802489541500c001310b0b0801c00c50401031500701c41c000102c04031032044804042160316441c407507403801310582e411210300c6511046c40740364000400802d01e51038103e0000310300c54002d4080b260001070040001c40c070f240d600116203405d4282001000b0300d03056103055009500010070060790b10600c0e480c1d07810b10240143c000070145403a0400310b6541e0b01a800251000d1706240500c8028040052000040d5000b542c0380140e45a04107140d8080c2ca1191002218501c84540450f410202120b5600d4000600819a00c4a91010f0700840c011540c0d035070040d248112200104801103164999060034900d41d40307000740407136100410151303040f100c502014100b55661215001c40c4c0d15108112000d10340c000d441d6030385034507145d501d84070000070074002c00004904204103010340791b00d14044e070240d008050b000b4004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 129162940 1250 129161690 129161701
    0x2010216080a11040f020712020706030c050706020a030b0d080904060b030f0a0b0a05220501140a15031e02030402040c09050a050405041704060f020c01020a080904051801050907140306090303 84
    0x22002c0000f800320360040c0e68150704520305025200404000e407041c04911107428224601074240b12a6612440c280b41c00e00c400004140c0d0300c8012901081c0d84000010703120380c1e240300110018840c0702811500000241e840e18248440c8202415981d40704840c14000c4984070b02d0fa8810030b0205699650100704110080b41035400c2d203401c22a100030000e0440c4010b01e80d114009047c0f200b1b245480e050050f02d074211001103d00ca4041d007405082c01030030000541e40c0031404100d07007440360300c0781984140c1d510300f00050749803007500052803546d10080d140694540b25080c4200942c01614100e10032840c02003503032080d9016003a21000c50f039000b00590742040c071308414000527100052003114190700c100000510304d031b2803101a00c00b500c0741d650355641c03400765110003030b15040c440020a0305540c00800e01d8800140040101d4200c042c0688000c14141c0380c61081c0300e02d41520281d410029400e02c010042031960001d00c40c0b08813105401c90078804070200050540b038030016a90010507420030400600c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 129164190 1250 129162940 129162953
    0x1e06090325030e10120f020910050d11070309092405060a020a08031003020307090504024c1803110108040f0c03030804112709030d020f030402010216080a 68
    0x20180c080d041c0212a80d0f903a20015074850340c02d1001c1d44c082450840341d00c420103050300c502c44500d91507020451801c0d243e50300040309001e04448090401c04002641d111000ca5600081d8200909441441d01e40b48540b4015040600d5070003606401480c00080d80403852803041c406242c5948401040788039402c1400b84106684141000c80942c45152400000100d02c140114450600c643c042c002d114110b2040604110840d40301d0969503050205000c0960380703031017403100500414002400d980010702180c080c1040700100710b440e1141e1440050822400015908203000e0a41da100d41408071641d180c0c3c0001140342c00007810b801001e080c0000254080d10b074150308036014162082c400c0d521035035100b0304d28503940c0049001a076200c090104200320700f80026401d050459140b41c0090155a1801140d40050004090144a0301c0481d82c0b81006204a407410f0790003107030941d40c0d100345004d05500c07584207072030890041c070403514403000042c41e40f0116020b9030403c602820b1030f4051600d410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 129165440 1250 129164190 129164257
    0x405100e0a06081e0601050105041a070201030603060f051f08060406020d021b010603120503090307030e060903031605100912030c022a0906040204050607060f020c1e060903 76
    0x1264031035602d64010411580030886060b00c1240303401c074030741510020902c0c541400f5043c0d0110341800b0b01400140f1802c5024802d840f0700401c20a4542d0300c4044500040303000d00f2299101604647c503013018081a24000d402c494490311a078485421045e400307902c55032400c0340500c941c60507504142c000c100029450b80003442d0413034101d00d01501b40480400c5480111078211185103880e03640320401c10070803200700500e1f510410f05051490440c0b5000b2240742e03d80c4510f00e0010108409410000007940c1d4541c1a208c04a10280481392038801031601c0180301d202c00c3c0f00c1911035118120000743d42c0c903441e0042005a40d03115403000c6c4007034255601900589402e04400055000e020790000d101401404400148102406001388c00c149901c2071180d0b01c1000740105004500401040c40141c0754181120450b80e070082000030380c1e2500d4103621009001d0480356404034000c038000c2040d00b070102c48441e0f00d465480d4003510000e407580781e80d4955038403a03e0030085140136810a16034408a000007807 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 129166690 1250 129165440 129165451
    0x70c030516080f03010305160515090a090608010c0801080f0c011d040507030b0f010c0809130b0306070203030108060915011422020d0c0203030112230706031a0405100e 74
    0x20320346884450340c071a10203030050064501115801301c01003060081c2000003c82100d11000710009990130500420078010000c01c3c1e840c500800022000400d07242e074010040100710929081181e00c0d203800455010700301c070f160400b0000c0d0031107001003014000800c4058203103010400410f80c5103126001900e10f0b000ca14182046212100410003640d143c46c09550321410f055a0001101480282000444120300f010a41003020b40c1c845000050b900d40112299031038200c034840900204058501d0190899185440c0c050199000740b00c80d20381c0000c003640c166051076082e20865034508403500e0391070100d0260900a022017100401c9225048500026140c0c4080c2c12840c459043c000c0f20606829040811002c081d400141c85001c44c007035100b681c00a14141c80610316551410508008029110030081d100704d64200c0b48500255040200ca40c424207030409540280383e031200f01500604a807645444064000c1c0c5841050703240610a142c030a00e101d81c00360a1040c1000c20704d68906100408 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 129167940 1250 129166690 129166717
    0xe030301210515040b04020a0e0405060415020403051906060b0304201f0f020c010c0302060c0c010e060f04020a05100519200604020a080106060c0f0201021c0509040b09070c0305 78
    0x40f0068604280340307181e4400c9004400c883c1241c1854810f00603843d401c1d9001040342d03d40401030200045d40070030129002500100102e04850310082044000d201da94402001449002422030044040c4841414018040d880c100429a600e80030031350548070455008000c00b204d602e0064503c80c0400001c0050040a0607600703c1c11100544a00d40c4110790b01c03100d0100351814003500f001c07941080b40d020b9284007840d110740341d042290340103540c50308080e001f14040319004c94150a50f0000b5800600200d41d41000c65030541090440015003201c251400d03805100700080101d07aa007003c442004204840f80d5400d171030460b0120205980c0c2c640311402c64200710041e602020040341269500c0034030b500c524040e145508003841040180381040d80051031a9051020801c00c3d01d400102070180c058214812091802003840100d003003072400c0000c00e14410941c02000034065000001c5e1280c0081a0740402042501c44200300b1628011211000003031a402060f41c002071090001d03040c40c4c6024171 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 129169190 1250 129167940 129167953
    0x60f060513050a0c030e0d1409280801060311060703120608070509130c030813081501060e01090503071e080102030f24030607030507050c0115090e0303012105 70
    0x100060300c01458841081c0741e1a45801c00e2000ca01400c4c45000c13007100e6103040420200140210150311201c4021a410034481d96418020780c002d0000c0454103034071b00050054145c501c21721902b21840400c249074220f656001c08010403c8101440b0740c409880e0000c445042d0340c03580d030301005140d621004d0214100454907000e1105562513000e510301824181c4e0107072020b98140030500440c6c40009080d0700c41c2d01000c59098001c41c4000903200c040d03075040540710760391f0080c10700b070524095000e40c0411041e00c01c01208034819540316544c0c2d810380302c032903884011a07040da500459806006004090b495000181c2c01c10940c2030700300e100480c2c2120781e061081c40d1940c0303d226070b089801c111004080300701010200481d109407981070903100c0c0c12034120710031000d42c490042603a03050020154424143e1311408126030f40c1c001c00c1600d0000344150028045000f001c8121500346203a80700b0b0820280c10724445a031040c501200340c034161036880e406848048a800c0c80d0110900c01d260042da003901456 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 129170440 1250 129169190 129169199
    0x90d02030a0c05010e010512010902161401091514010b0d09060908120108060f010605031305010c020f0d050a080402100c0203030409060e07092106060f0306051005010e030307060f06 80
    0x18040815680c1c000c02c0e90110140c541400504080c0d80101200e041203400c02020a10000100d162419a481100010385401701c1444044400c208aa005800c0c0781400f06400f2040f44150809103500b07204050ba01d041041280c031903801e4035040c0c00d03540340c4140031600500548001c4c01c0034040806082e04081541c600b00d44541040b156802000e494071400020b50500c20042030500d2401000104020807143c0b07000300303401044c5401030041008100000000c2108040360f01d042a4203c1d070854000c21441050b10400795031003400d000644103a01903251542c140c0ba000780c0a4544144203625940c4490792250300300b11900022899101c00e01c000c200c10301016850400103407000e4501084000340c502e041841e40450302a009000038200180c00c90b0030310006003840d810f61910000048800d071680c10614004028107065001109107850f0700794000140b15842d000740c2e0141010501c1c000650b0340b20001100c100340d84440380c0b90198030401064001030165800b40480e02d05082c000a080ca07202c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 129171690 1250 129170440 129170443
    0x70909020a050408070f050306041b0b04090b130203100512070803030c1e07021008041401020a0201090c080607080613020c0601060e03060f0f13020103021c1b0206040302070902090d0203 82
    0x100308200010000f00e02401640c41c20003400e0041d00c000c440303130101e045ca01000617a8407100188010140c511000b0321085030011230101e103002d4800d000545440d6501c03601030000420341f4000d1f152295a0f01c02803018149428030807640901c0950301d80c03001031410315060000d210394155001c4410b20812800207118441400030b5801215819801c03541d540a0705c0c40f140c00781d1850040541c507420100440070050381c0d1003030002c1c07940c0014100300301646d81700c0c24002c51030070504001c0c0c02c055000203030a80d02c00b5410b5001c880303003603c100103e10007652600c8900707946078000c0b07c1c14004201004080340c002d103440c0ca00194040c4514074003510f0030541d18071040c2000400e030302030000300d560300c4802552454103214807503101d0b00a02114000707203000101d10a204002411310076440ea4500084425648aa011504154041d4114202e400c1e880000000200003070340100d000c80e181000410822807011a4160140c2d030907500410700c01d420004800005d5201002503a8405150390410f030060301c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 129172940 1250 129171690 129171697
    0x1d0405090607080a14130201030902090f010f0b090a091d01060f0501030f0e1e0a02040207150507110307111f090609050312120a06031b03020114070506070807090902 73
    0x140000035103030500b4a410301074180000500341102282c140001c20000e6908541c54030760001010107584248017190006800a00d02c079200a5040f0701c0550400140000303000f070b484c3c103c0e0354140418643d81c0e034480d0341c081c086c0601445154400c80c42a0300704403800583e000b200700c400781c22845c0e50300a030980700e4240c21035129900442c0b10b0914014100044d42e010301c18003000c1030400405001a103458001c80780c031060313100c0000280c00e002c805034040c2c4c40800c01c030140b00340e0360140c421940d4210740d040c10320041090314a16481181081d000501481c407031807150741e1102d0b08500642c205400e0f036407100c0907150a5841d00c1d80091114040e0004040340c2e42c6c0c030402c4200203850341c513001803d08100502240c805c2d04198040c0c3c1c400d4200e02d0b0400c40c60011121317090b80c03004002945031074112500c4040c04032540050301c070101100c40d840c038078096041d411045074800d880f0f00f40101c0c090502d4640714062081e002d442c5c0d80010002510030b90180085c2a4080c0c128545600380d191034000c0e01c1d08036003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 129174190 1250 129172940 129172951
    0x5040b0d0204081902090601050301210503190201060302190501121109060a050a0809071217120108031801090e0a050907050910080118120f020a08040603050915060f011d0405 77
    0x144e5450007a000e41c1016850960002c60a10304245590706220140100d947c0311055100d134032402451200c140700090081c1d03490400d0345801440200090341000707020304030501050303100325886100c503003a03000d50007540d508a5030180c40300d4407013420b6400400c0013008140441c02e070741041040302205540d1814001d01c280c1d03505403034054607034162440091200e00001c001140c0c0d68403180c8140300c035052109982d0041d691002c080c00a1114802090086004000d07094058510030800400c4064011014040e41c45032150601c04441c0340300011907ea000b03910500701c0188010300894825222508126400440003040300c032659602e00124450400131619016030102c514001c1c05204828000c680c201c0039a02410880b0001075120712501c0c2404600f2801030007401d03290b80160a0081c040081c200e5008000320340c4030382c0d5a91018014080c2241c611046014008228031124110700304540a005d02074000c108144014005541c10f40307800740700c0d1603030f40010407113803205582e51300443e80b150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 129175440 1250 129174190 129174223
    0x32007051504090f1413050f010603140f01060614090105070c260f0d050702030708070e0709050306040c0e070e210105010803070302100b0d0b0411090a06050105040b0d020408 77
    0x961800c00c400f001c44d1120350000c0220350901c0c0c2d01e00300e6080c4040805800c03203e0454111102610340c070f8818545404c0c901103014075401c0103400428018650b00441c860b60600c030517240c040380060b286500300d4003140503880200f5440c54004441a4000001d005102d030181800d52804440e40c03207080010b00140d00081282c4502e0068800c1400c02c081031201020400f03000b032224022081406480d030004901c08801c008001c141142550340800c035060040c0042010b8504450305c440c442000752030119040e13808641d030190000f900c1d04000a80130302c595001b00440102d50308294000040720800351206082200380d0001000c0d42da40c4001c0303040200b44a482812011000701100b03800e48038142e004403c0e9800074040354004c07a070013080058110a60340800200b0070004e20010325600103005e00a0074509000707040100b001503128078005409001c4485140b5030f40c1c1c040c142810303113449028050000c1d42c10301041080c00030020140040105011000d414951100c10140c0343c800040c2508581 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 129176690 1250 129175440 129175447
    0x140306010c231020030603011503030c020f010809060f071116140315130606030f121103030c070b100909050303100603050f0c07030c08042702070320070515 69
    0x2a21410041c0d400d000342c5004080c01180d0280780100503141308442c0525440398000001909a80e003944030880c0707204a84a0100c8013a22400e005169082d041d03400c070301550200241c200198010101c031407148154070010314461b5212014002d109902804241c20301a0301c2c0300540c2d0508062040d46050313144d80f1304401181d450540900a4420071000781d901070b4110914401c80581104803841d402074011260083c000c64900c0c124001301031a50005d444590160400301c1080b0008007040014841652034000d45a07000c1c2c212512444142c0e111400c202003003100c100000d401e00b40c00c1c0d0b8020491102d00e40305c07171750700c050080569180801c22606038000000300721003400580520300c0a8291850208694030f881c0301c0902c44581c000e416280360b2440420f0072000c161203000000500d80c1d205440d15107565a03007580701503944002c1956040d80030030211107031101003144240d030000c0341c042d070702c80b194031245101e59251007010441b03613462405502c40108076034588940315407016440d501800d94 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 129177940 1250 129176690 129176753
    0x120201031a04241509030f050f0106030f060c0201051603091e06061d0606040b160f26090901030303051b040b040f090c02151504050c0301080d090303140306010c 71
    0x6005100d030b0450315009420888901c07410780d012101100380ca47c440e1900eaa0b480036410310a191815891405840b9030a260012042010f1400c41d03401c0c6510510f07040c400b10860003400d031f0030383d4800c41c0c030000b00d100d582c100000301c0c0741700341c000180d01402210780420081010740c6007078110505040542d6415224a410042c0c10000124841d130b90084d00b02400050400c03a0000e40a4803491082c510001e102081c0021210340003e02c25030034580c071140c204600080303890001c1c02c03046000201044071141c0c07015518031b24400011070305580c41c02040402c80e86c2c01c41c0d50a9005000c06400344555025162140c4503144604005002402c50038a141e9183da2030711480c020aa85260400249282003d800120880c0c0001d01d641c6901000c0031784960b540d0b02c07002680c1070490040ca80550143c01e04050288943c000c50080d8160764102081d14540c00c07000000740c80c01c250f10700c0300800080164900e42200b050080c00756400c50014500100c0f40485a158160f9100e450362003810743c440140503601 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 129179190 1250 129177940 129178001
    0x3140f041203021c082d070c020301051e040204020c030405090702010f0615051206060c070e01080706081603020306030309090103111009060905010c08250b01080601120201031a04 79
    0x40344481c88003805900f040184c4003c3c03007020b0252141d102d02d841c0600159a8000004813040145007203090f5082615241100411025601c40241e00035464440032559080c141080c041c1807191a24526880d611990700b0702000758004820300b034141c0010311010a81b40e54100c42c0e54014074041d40041740101d902c0c101d4038111902c941c04201100342c42c2549154013508103007640e002d1182009a42c07620358445001c07902e03600c103456581001e80150200415080e144494840c142c41031f040840d00e80300c1c0c50b001c044d20800703010784d40145490806054002c01520030340045502c51405800d8034141040d0750f0100c2d12260342a0021113000800d102110303040c3c00e0001007070780a44018038045902d1407414401034814910742c0034681c10049134640b402d00348030050084548203060440550034403100d150214034580d942d90022240c201d03509000140810700014214180e13208006e03000075045e2a6030043d40280700341c92004415000301100810503966034400d40c1c00198030710303002d0b40f007101502c684c04 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 129180440 1250 129179190 129179203
    0x31a0411060405010c0b0703061a0a170402010507081c1a120606060d0b010e030d030204180c0f050304060905060106120b03210a090305010f020904060801020a0c03140f04120302 78
    0x500910062000300a035a070701a55580c45c45810842c00c2285460310107048001e0403080d0022107240c3c000c440c400600303942b500300a0180d40900d644144200c9200004082c60010690340640011030502c81800480c5207040185100540440300c2c401160403403072a4803d482c203000b440c2c03103d40c07100d00310500b070b5061281c2c103401d080407184080e00551500b84000341d018003400d116900c015a03914a0807805900824100301c4805004003110206021f042d0010301a5019004517500b054960111640826103030260100064680d114141c249002c00d204440b241c02c0104160350154480481c480800c4081c40594081c240070703500c0c0a03050301c451951400307907a01083e62900943c40b065420101c10902c0340d0504001040f90f55403507035006c0380b81d02103440312410341000d1b019510b00116403400400380e41c001c26108009503402c1c4042030b680c2059500300d0060054401c0402c40c841007580000e4480d428070011980102c4460b41001840c0e6007078038103500103800130038491400309581d4090607010000c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 129181690 1250 129180440 129180473
    0x10b0906011b170702040207080306151315030b0d0b040b0601110303011403030c07061706010c050c010809100606030207060e01060303020d0807021903080f01090c0903140304031a04 80
    0x2d820007a03a03980d0011000c00440002511100c22070120746603420010301215109a0020300c195111012400c10303003125801640e18520030490103440c80c00f204400c006442c0503aa800f00016081c1e4505208140e5460032000c58000701583d4055a41c020354030400070341f1105005074610038107840d0500d02252106800b034a02c42c1031181c2107800750341c82c502c0002103d06483e4006c40a07403804d0f072500c010034658010703900b045a050099840200341140d11110000250f1364a124000d0241c031403400644211421143c09080358100b5048090300d54040c40d13006030066481002c462051440b002014111400c075001000040e40000d03800342800241c2c0202010440315000800c0f2451540d034010750341d500310100c014240060171f000907031418000c1c00440c4048811441c200c4034050345140042000300100c4400000007104000407466454900c104068000c403a250b0074200c500f16100c5100c40d1005000342c0c50148030402020002911007450070700d10890554000e112403c2c1403501c4440c0d1960b2101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 129182940 1250 129181690 129181697
    0x90610050319060e030904021b06070305040b0403030504030e030f07180b0a260102040306020a031b022508100b10030b06040611241e040f0b0903040f08010b090601 72
    0xa03450342c0da42000300740318038540e000784009103003880c40071310600314040c900b4480e61041c40420300e034910346900c00320400c074410810141c0d0b142e5580c00354240c04407502038401030042002c820004001078060340c001604140070b400c10010a00040c800a45010a2004d101070030b80c102c0001044000c1c0e089050003d14108010140481d4a880012071807442c0350b881150b004800c00555900e811141804140050820200070355031aa02e0b420080045c3d40041d50340030019141c05218400c600d0005048412408294080d0044500c02c0928101d84211000c54100401544400007456801044a0781090110071004118805100c08001d002001059510185800c1640c440c41956030502150155841e50908034492403078001154545502c6052640f85581c1e0855404601c45650542c58882d007108441082c2d01484810003521909003650000c155120030000840010820600f2079880103000c01100c0c20311341d442c0c466800410350344d40200c4080e55034107102031442c180054559071041082c02c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 129184190 1250 129182940 129182953
    0x10207120908150f04080a09030804030b01180506150901110f0d020607091d040314160b0a0605031b0d02150910050315040e01020f0f0c07060c080304080c0a02090906100503 76
    0x203505002440004000801010380020b410644902400982340910307004607032640c403140c8030b14202c00c01d00428081c41c00701441c04110090310880b07c3c0100c5e4407401d4040c0c40d00c502a9147c04070142c0c560050007900b410301070000e004458110003040500e07410314070b40006151861144601a0034180d01803d800704000003100203100801214040e5005a03d80c0340014140750b4a40c00c1c02c44200c120306030a40046107000940400007505180c484121134040c03206a0102d8440362544000c032001d0744510358240e00008c00c02281e003a03032868441c800c180083c041441d00e103040d03400507a40202c400e4000c8a010404642100a400c1116141001c00c002d81451031550500001420450820b401c18a12036601c03000b81a4035560290140c843d42003a80c4156600e81080c0c00e05118550440e81140040b1304c0b03426000607000c0d21400c050301c2400d0304119a60300d940c5664554000681c012904105035104000100700161101c0c2c8410344641c030202d010700894201040c20703121001460780454480e91001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 129185440 1250 129184190 129184201
    0x60a06030225030509060c03090f0a05030d0507110301051603140708040b1b040605040824010515040e040f050d080106050f0c12040807051309080301090b010201020712090815 77
    0x82c03031842e00710903511a1940350300b003890110303202e104202c403450300035201042c654440f01c4000040d125010f403c40301c0c0a504280501480b1808409220790b0750325522401500c0300484c050310041034898082c1c1241e02c0880030b0303140400d0070b446041c0c8580c014400c4034101044c0080e0301d84142881012038800652841c104960010f02d054405000641100600b10100b41722049801c0b070031112003407242030940c03507964170007000d421600284035000c201e014803d129100b240b114200d20b499904201c0c280d0750141d08203410702070141c0c5620504603d28008000200d242d140d0041c0162007180714001a01800d140c5143c802d0421443c609070074203201c013250042c000260004250b07a20505208043d40d128070074030114030f02c0e0852108106813220000074020034415000714810301500c1e010760b11aa41710800500715812034041d103201400e030701c20500050003070103556008414000c805200250400380c2503200da8040c90358508103080499941700d002c001e17040b03061081b07005c14540154003000d18600b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 129186690 1250 129185440 129185467
    0xe04050d050f09062a01052a03070e030a15050106120207021e06041a0a17010b090f01140d0b0a05030d14090406030b04061509020c100e1f05060a060302 67
    0x40310000e138070030040814a107014103c2c00d00c80316840100c13068105004a4031002043c000e14055480c0b55a400b000b000905c054036040c880700c84a5884426a245513503070300c1408807101118444456494001c413094080840c40b0440301e10750803000c5210015182d498200060407403415120081119070042c007540c40981c2d04c0184007148a10900400c012603c0001c0c00100188996000110140c1261068040404020020f454612140d44035136019402940d44400009800d20402250001c10410001c02c0e0510308018800c5510604101c0300300c0d95420780c08440e13900b110900600565641d8a4044586898640200101000d07000361102501c0c4803001406110000d04803002c2041c00100380000d52680e030b210b00015030708000e0f81c0c186810b161130410080d10b0311f201c6514640781c041c0710100b011711180c0300700c2c1c1c00001d2803c018a4890703965034900010b4101040000200c2c052202050704075030b0150007499030700900c88030010306413a0440402c50428160313004141014418466003070b01341c1d003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 129187940 1250 129186690 129186697
    0x903010c0e100e01030e2a0f09010b0913020a080a0b0a08070b0f0403020406060f0305010603150509070210110705070b040e010308070f020301110301260319090f0e04050d050f 77
    0x840e45050f480554141c03005901400a030921107009101d00c029071035680c0e09440b1071607420700c00084080b403140743c150104045001100c0c59683d01c0300780c01c00104584288040108243c0c04041e260040794995958080120380182e4040004a038190081045c03180d0700c0c1c41544000801214120381c1182015840b43c0ea9102d0340c01090400391000480707144240c250810786008650041051080c0c42c2c9910004040020703002c01d0702c021038240400466007a004e405020400e20442444080c0907141c00e003000054040a45400d0540c050b080e03081d40c0c958034034003d900c201901740340305650f0741809141061411040d94446039a86100b44400c0c03089003401c030b51071390441c0d0b084107000b44c84480e076003088071a030300805500943c55845d041100d03180c02c920401031412940c045a181c00410840001c2500700c3e480d1240c0d0054540040014034009a80c10003605c4d01c452151511082454403401005204201c5070850011118801c0802080183c2004103650014452828608080120a0b0a01c1e02e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 129189190 1250 129187940 129187969
    0x30f0603061e0106030b01030605130207031b08070b07030f0c020304170f060414030d09110a050609010f0305071808060405010b0307060906030504030c0b0f0106030b18010311030304030f080903010c0e 88
    0x146c42d004400c4250303102e50000d002420000b800c50207112100d010b00c000035840034508801181030f070001c408103c40c0c207030940110340384c114601c2440c0c82120341c0e641aa1a400411075024942d03980c03011020030b000340c401d803540d0003a2500110b559a003003040081411060130300f840030301d6000c3c541402c40380f0360220341c10380c00135400b000140f001c0c81b000705424154080c1e06c0314041100c2c5481030420501000d5040141c10740700545010361704580b5401481110320444904034040341340d81c3c608090302442580029489451480d2060074203540b440400e8a8402941c0301e55050b5100c08140000c1c89001c4c4034054441c03000700c0c02045203620344200a03155140500c1003009150f51000040c05240c005d002492216610009075140c41c40c0c854400c040d132044c20b005c0d0380d002a181000e8030a06080110451000400070724070300c611070f841e541d2551120074801500f9500750005010000001e0070b504011400c1c18841d03000d0a4071294403009060844044046510070088004c4205a942d141c0403006076059 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 129190440 1250 129189190 129189197
    0x30702010905270f0619030305090904140109060518010b10120b0a06020102071109060121091e0b0c0405060d0b04090c0b040302090c09030613060b06030f0603061e0106 74
    0x96940d0b0301080d01007500303901c004640a031088200302d240c102c44903500d44a031178100c3d1042407130345129403142030580f01070000a0101d00f0801100b1168a0603150040d80140b05000c85220840d942103d2829070b42ca20b00c00b00e50301a10380b001c1c068440380005c000c1403242050340082010002d01000074001c0094901c02d4030074014400b0800502c44090b42000011440c0a00f0043d81d0680c0c0740750080c001c0d44441425a8a1507a00811410a141017186d681c080e81050f0b54841034000c44880c883c5454003860548070036a6a200050ba0020b0803906a61441c120f2003203260044084d1800c0405091a000f0400741c040c0004000600c0325681c2e20b020359128030b81000001510000d0b50303000c20020100b5904c00b03030290103002000211003007004028004d403807013520044095240c0c071014040328020801802d5150700030000040c4090901154640524052400032441c000e00d000031134611f0f442611580d180086400400c915030401b00240b0350000c06e00c1d48030300120226240c2d0208001d2040c096a800c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 129191690 1250 129190440 129190459
    0xe040f0b090619120c060f0f0905130207060c0801051009030201021903031808030108010f0e1b010215040503130b0a020703140718020a03060501020d020c0405070c050a03020a14030702010905 84
    0x140140584100a820350040c4d00d00307046002d00b401000358015104a80014121031012100e15200e4048400300b94425240d01c0009801d050810034aa0176840c00709034525828003d00740851924003a551140c0d42580b1440d4055060400f0b00c2941086540d4110074400846002c00040c4d90004401d00c0e40c0c00642d1211140351020301c0c08401915070391030501ca125200005070014400400000c504890550008104400c0c1000000301601c443c00a20512504803240c000920076003c2058090014144199402415912100700c203410301600c2c10b0f591540086290900115502c400801501c4c40360042402d2080d00e2000944d29042e6002c0240170040b114084d0811400c01c00549024200d03400b40c00440303100d9601208001d402c03100030180000d0030000e00003055400454904172400d00d85d4050407005525074203200c05020040c00450420031030080e0754000c510140104d04a4a100740e0141054904030300300041c210403500c002140c250810440070b070050b0f800c00c029104580055401d43c0c00c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 129192940 1250 129191690 129191719
    0x1060512040c03080304060b0103060501020a0f080304051204060e030d08060d0222020a0804110901080d030b061e0a080f060604090905191214030c0306010c0f050d0e040f0b0906 78
    0x24402c481e90004000d031201105203c01c02c003490f0065015103801780d03010031106654134012a03980c04c0c2c03080301501145c92a05c002c40411014001964410302071001c552203501d20b0030204505070300a41c0181d00051001c100b600240c902844201c43e160880d2800081b0b508000c40060b200b00d85010000f842002c0d4281c868082510041140c3c0460184c070301d0864491412880180c40d0400444040741d1a544034000d4010350315011181906035882c50004040d5010003850942c020401d09428580c04a401c1c01807c2140031034400e901c843e0100450702c03e03201c51100341c01a2400101600344420800b2003410132003c2c3d2202070544003291700410b00030a000b1810700f0000c1c1406645032a0548001e5901d090005100c0c110340b0394404241141c0d0380384450388200200c040c050101382c440d114010400c00119041e584200c0035000f9850096001012154060340c0782490000658000c3c3c021403d80180310f0030f94907081c8590540d00c01c184900303009031108200043e0705608010001c5200b242c3c11001e109 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 129194190 1250 129192940 129192953
    0xf1e161e080105070507050f0304060e010c060b0a0609060809070302030309010c020409020a080a02090108010b03030922050a15090e0715050705060f060906010c0f020111031e0c070e0106051204 85
    0x1050701d80700821541c00c0c021001003855005813025201e40c1718650a105480000004860481d0a00e80d035144001032142c0046501c020510410782c0c07880d46030b140d1140075079604240c0c0401411144c40b00038040e4640100a40741c240001d0030281c0d07a4100050420150b140030086a03185c40b02417070150303400d61007480003a0081041c4000a0340040802801055a040018100b02c44d03c1c0200d5030407055a07030760428542070701e01d9080c0043c1c040e00140f00201e51401c106800d01c00d40d1340d0000100440010401510046a80440380c00d0f0303144cd1520364400c011181c50003420042e00e2448010303ca074519210b107155680e0310a114000241d08910800c0d40060b01c100207031203085900c074003680e0172828070030341100c00c02400380d071050711a8003010080780701c540c040c001504d202c542c031414003046801d15800545d00040000d030312988078041003000d03005074a0501c803c00620001550010740308d030402d000803031400c251504580523103035800006200040d0480155404600c00403508411580c451902e00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 129195440 1250 129194190 129194249
    0x20604051002310806090a03090513060e10050a050a03051b03030c070303020d090e010e150f100207180e03040b0306040207020a09050708161418030f1e16 68
    0x3002c19183c01503040310805508402d040302c2245044030070f10f03120002c103e601e500081d0001400700701070080030030040c14000c0d0f0b821241700c01c03684001a20303a039801e128845510708a90300701c645016050203002c07132304d41500040003910068403c24803441c211b54565940d59072002a00d07412071b80040c160001694104100c84138011440d00340c8880559900d000b9641c2c08034400d8400c081a581c400200c0c110140d002403034101d8007580a030480c01d44950215003140c901040a254004046202003405612449040388817800c05500074075840303180021a400110445a10320300c02801c0c030011300e5402d5800000d031025500201c98580e580d80320540010024450540004d402c41d411503000505207007150301091044070182c607054450f540760391400c0d243e000142882c10204000d9114140043c90b403101424520324800a8000e6102c548000030b0f1a2051081d4410080c0d80b003945134828a00c03041003401c0b0800c5003e8000c18490b070050750009102929070250005c0c245d946c5c5140010040000001d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 129196690 1250 129195440 129195487
    0x20d02150a0210050901050601050a030c031410050102120a170711070b0a110703051009020105041805041209080a030c051c0809010b060909070503090703140d0f020604051002 77
    0x3a00d5039080a180042d4858040703071000441e8518100c0000c5c801d82060184600c210016903c036440c03c41800c3e030036030040c00620380702c804065858018600101046181c1e5008281c50200107000c6490580028035181c80e403010340d501c4250038000c44403040d0b000986080141c1202c01c0340304059031102400c481c2015148198034203031240c1440001c900010100810003550284e5909a0311110941e1042ea02c03005440014219400500d404811034615800101070354414541316103819661070b01106d0308032943d4420400b01e6a40c001b070204101220014184034409070804480e011b203806a081e0311020907590180a014031a0115810454148800310504014505501011014910051140c401150300c01400e40c6408541d062500d0a40103030740301d8010003401c401d202d9039262000c81c3d041d0000ba044040d90310800c100403000a041540100401c03540070024401c015021500900c03c50740788078010705540080c01407001054020404c4601405901c2001da510f50f0904e04101081340c90105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 129197940 1250 129196690 129196729
    0x10509041509080a09360207020d12030b010c080a0f03090803041109010603140604090f140309090109051302010e01120c0206040b010801050601023f03040209090613020d02 76
    0x144100034420380507010381c80c895560006800c1d03ca1682906400840258202e4a2410006d0058601c55200c1c00807201010301800340c108442070340400c0030351902032000c070b46440d11810a003140301d41c54814103000400034604070f0015005601d42009500c200c520150410075131104d40d883c01800780e003010300301581c40100c00381d407861305082075980040045002072113005520000a0700c1d600c240940a030501240c0041c0e03240351140720811004240500e02180e801c40306000070400318034441010050100101c020315564a122000c001c0d21201c160080c3c3c010624100c28494400c03001140180542d80c28207046070065405401a5004041c98024000290400100c070000c10b60204141d405148685100e07811a41c85001c410309981c411102580103a1050a03084c0500a00783c0c3c4c0c00c0d0a002580d5110620002054030215110300054a103000c11380c03000044c0070442c101004950351001304900902903904081c9040011000060406032103480d1450300e550030f42d070b41c20307074542c01e800300c00003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 129199190 1250 129197940 129197951
    0x8090307151401090c0512060a05030604120e060708030103061e060b070b0a021207051605010501060c020315012702040801020d05040b071d0103020a020c0d05011b0201140105090415 80
    0x101c2402900e554401c0380341c140c404100004c0c19141a010384103518040340c4400d42014110359144000107001402d0590004442c0b0001403551414428280120301400300d003111211950009081c80030152040350107100e04000d540d001ca01c41c6002d980c15a903114801298080c0e20105003c5503460203c00300240301d1030220000b8500c0019401000998460300501e0116920345c0404400c0f4022a14030400710001f403030000e000b00e44204000d180382c9154005e0482806016100d0300e003118002d820080c0421142e030300c1c41080d8541001090300c2c010700c2844500700c942c10211490401141e00d8185d1980f09804501018030100f29015039002d402c190f4000c644a81421008030050b01e010b039025220b112491011440780b504c2078501841c001001e400c024140443c2c83d004400a610118112086009610040e803031507884403a0703844602d0091002007003900d031000801013003111414054095a14000c009010001011581c504591080b55441403079912400c0c03c03030b07038540110066a001403401 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 129200440 1250 129199190 129199223
    0xc07090e0f0d0306080d030603050309010c080d09230616030b010306050612011409070503040f0204180c052b020409080f040e0108010b0f180402150417010e011b08090307 75
    0x1648510210f5454008842c000c0d0301c030146c02c2e4103c03241c1c6d00016056400401c404002940140d100d0882d242c840d202c40b624040b440c607240c0080701d10644045501c02d500000120f14410b01c11001c2d03c4911110010b0a0107003803890b0310703003601d034001031703080b8245611408103c1e4960300940c0440014000940210303640c003440ca20380f400c1c070030090003075400e0740c01410100081c2d03040c401ca00500c46c942c203850709451a122a1104425504410802c9900ca52190301c441c14401403410400d199920a0050b8100c1c5800d2408202c9082c4065041d410800c40502c120000e40d0f09405d41c22521940540380042e0500310b41c10640098410304042c81100a4005000503002c9000c0e601d060403242c0345c000822000c03490030100a001d0030000c003441c1d03000d0503070b089031800b9904000c106900310748010101d903500c1030b02d440020038540088d0b0041e011054203040c6128400800e0042508a09400000f000b540287c2c8a200c0e00c0d10950603006010049584001041001c04004a41169401c10011311288140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 129201690 1250 129200440 129200447
    0xd030804110a080c030106060c03020a1104090c0305010203160201050702150c041509091113090e010f06140103050604060e0f0403030b041503123915200c07090e0f0d 73
    0x1070b40e00c40d02947c40d03d0310000d0030f94402e0b540c41d040c46074158081c211950703003070300c0703c9507010250f403c0c0f1a809590baa00311000540350740300303400045105500244c0ca0703203005204007a5000c00200400e09590412040024456010491128502c20b58a0340034054032000421189800703260446410440000690300c142c5801107203002c11212a00400d0001700381c00c291150240c0200d070310621002c514500300348074459803038004503444001d260002844061207000542520b04c65031042c4409203600e541c0c11581e50b41800351503070181c0156800c0c401e451810081c1084004d00034410200703a0040c40100e82094469003007060305070001030080c04a003034140c07000e2222118502c4111503884c500c0c0c0100051a00603c25002c501e000e810404c5c0440c91003464803401205115042103806104005140000d140003aa2003003c1c40303030000025641c018809010700c458400d1242600c2880140550504a1800a0b07000c0c2918240040071400c0342d19010078601d44240f01d2001c640314040c400c00e0000141d403 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 129202940 1250 129201690 129201703
    0x30a050f0a0912050f0904090b0a0e0f0303060d08130308210f041104090606120203060c041802250303090b060a1409060a170601050a06030b0d030804110a08 69
    0xd40c0310401603919201940740480e40d00042c010b0010340260f901c0d0410500a80c0907000c0401605c0907680b9082c04c100c0041c044401310034089036801120018040d19a446201d80c0c1ea000705160000d028412030740c0c26256603800000e000510500031281060208000803040c0c40542100c164030701d10042d22464414800c3e040510082d1400d500641d0681e1019241d20901c0e01030110f0000d2114079898a885004404280c4622603400544544005002510b24805e40d4001d10500301c00b15404421841058140340c005000142000380071310050046140b10086906d43d00900c6900607550800c814501c100c3c01d01000f69140c0600c030703a0f54510145501074201d004218411208401036686030000c00880301ea45010342d28103c46101d0a948850a0503004035401400080035600301903500c1e50b0721400d40c62602e18801b09034001c40d0042085041c11603680014040904060040c071031200046080d6507000000541000001d40205042c0f019505034035614140203000b80400fa601c5801c0181d9945 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 129204190 1250 129202940 129202951
    0x1032a060503040b220201080a021b01090606060e100e1f0507020a051504090f0e031611040c0806040506011e050c070b04080d120609060909050c010809100c050f030a05 74
    0x141350000107152818040b4000500600145100c10400a150011a075010f001803909004513070800c501009a11070042d40808d9440f001c00100c0c0610b0b41d03141120540e41c0f6540002e0610001d1005810295070b12108080088801d1900e40c4101c0030200018002680c07410f10880b1900d140400603002d654420005c01440303000350741c910a00c0e5940d905200c0642070340000e10603400340031b11090090f8042c9070440e500c00040441d0205891114040d91415a4042c0004848240c2001184020030010300c060320749c1c1160858041014122509028040c81c1d4014402407003a5900d90009200384e0145426804550034080300d403400700c6102c0001b50050f404031711501d0251045000003d07441d00824221416503110401901e00ca00d0507500580e9160785c402e50004a07262540b40202c0c3e82c4440b4490b100042014034004105032010381400c038245011400302a04103d0450300700451290b00046c0c40085070040380e40010070841002e0100c5003402034a0401116202c00400c1c05601c00306070300624040e0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 129205440 1250 129204190 129204203
    0x12030b0405060d020a0611011401062003040509150310050f0603100603050a0f03200d030c02032b1517010507020d1218050a06061509080601032a06050304 68
    0x152501d008001c2943c0000714001e510820240e418022248504104005c4503070460020448092030803850003400802d0b080403001644403d009011600d02c01640288100d046c4040d502e06030070040824580030009090166450544030400e00b00d8408110f004120380b8501d404000505150044040b4880c0076280b00d4030034400c440f02044150a0307031048004403540680200b50a07900c030b6441001c24491050150140045200d60b42044c4405080041007203c4100160482840c0342202070100d0b4050001d0800310b51040c020b074011110340c0001c1d04d013103508100811807494455481000903114543e00940304505164001400d40e034004582003041040800a0255580340d17802242e40c0c2892071000d100040034800030851640f4030344d00000c10881c1450018a411942e5298989803d4148200b1210b0943d80c1d4001c10101c500500c1805c0b403030b5402d103481e5040740d2811681503174450341804060514014501c01c21414507113100c6170201014015603010003039980c0c42c0068207541080b02d00b075805 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 129206690 1250 129205440 129205451
    0x1404090e0c01030b030c01020712061b02010b040f051611010e16050f010f080a0b030a0614060906012c06070c03080406020c010504120311010f06090c020f0d0f0809030712030b04 78
    0x16442d011821703606240048c1e0041590510305420f802c2054080403058495550307502c0c000b03808515003560102e26036000e8002091000071201880121040d4000ea080b5640c50102403190914404207004c24cc1e41851a01103148040724481d28010300e00b0340e5001886201d062040d020074480e07200140211a230480303100e100003941ca130040d9094100c2048190000300040c0005030f40141c10b5000344501c205c09001c4401540759503403044c0441d826031026034444800c010400c42d1b60f243c0500d01030f80c020802e191100c2801c0d070511401220b8101c00c101c0d2000d0500c400701c91442c03070b1150b900742d0f46816000700000c0c49641c1d0700d00708245154850f000e440d0060003461045a03103540100c0468086800e0a0140c1040c0040d81d181107130a480b1901b80941e0395521040118442d000c5030141c50003410320448002040091284060718014041804010350b412042106484941040c0700302c01d04116420a100c2c10f80e140c100b01d40c118402c4010060107141802604101c1640c5940045403210003981c08002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 129207940 1250 129206690 129206711
    0x501080402040203040203012d1a010c030c03020a02031207051911040b0d05030310030c0f0803091e1f02011409060f04020d0b0403030b120307050a0303020a09080a0b0402040506120d1404090e0c0103 87
    0x81e2b02050000f1180403134404070640001038414110341c50028000c0c810780e03100386441e80c00a07080890790b0541c20300c01380010490005100d014882c04c1120f2003440c140100306032160340d9140b440c0000c80207080c4034690b50400c105094a842c00319103d002d40c402d003606d9407480c04a02c03006e042400c40c001600c1c1c155081c0c2d070104500041c07041140554194400860900c244502088404c01001000c000d00007546100505070ba1128003c1c00d811054800c807030b01071001003090003402c44091001d40d44141c85610203110483c003003c515183c10101c540050b408503651750020400c00b601c0c00000503c00185402084103244c0e05600018280c00211348030402c0b000c0040e4170990703900540700c002d00940c2005d80c3e0100000d01a6000302000307400d0b410a0b44070660b41c1c990003805d1110100b021f41e95582c00314200302c03c40c68540714065000130300310b48040900d5414050705d55540941d50f90766007880701001101030014489c0c2c0955005090000c41031000044091895884413070018089000c24107003407003c803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 129209190 1250 129207940 129207971
    0x513020408100903091205071503020c030a2d05090409050111030f060108160816030b18090c06030c0711010c020406170d02030f0f03040602040801050f010f0f0501080402040203040203012d 83
    0x644147c0c00030300903c2c0d12400e02384081c5c00030446e00c81d02c1c42459070030080c02200705e0040c0043e1403450f0490302c400b10803884090044002102c043c42080001d4049542c00380c4240d008000d84405c00c005840000301080d982ca8214010950100b11052001011040014002410403807e20401081e84c03071010a494000c11740c001603e02001752000318502c0720004403d040f080c2590140b4034510318012814070446000b0941d040d8665012030200804c110803c10821020801000443d400f980d9003481d42c176121500500d1030007003200041040034111581d10542c0c5c450702c500141c450f0000c0c02041103a40d685103111200e004070743d0020042c01160003810030240044155010b41c10086602d85c94410010307211240383e40300520444100f40d0070710010800791024030815208041c1540d900700c0650505013070400d01441e69100da0704002c0c8211080c001a6840007003560020380c103580250320ba0b156403001038003600c5560218482a0b07016011181d60454500003031500380044d0004200c14120303114110f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 129210440 1250 129209190 129209219
    0xc010f0b100503070e06211003050c01050706141311040902100e0a120c050a09020a020c0d020f0d0503090f0402040f1215020c030301051309030207051302040810090309 74
    0x1a9101e400102034444150095006641c00061850200a8120203034001003440d0840b1051440c09800c41c1c40f988004a80301c00302541000c241c004500c0e4261450351084e5445000030300603810000080b68050030024640c002c0325030741d003104406401507e0046070b4101d0044100f1802d42e07030100c40440444060416118600302140c024262140d03020780c0c02030030740780c03005010903140d04610550390010f01a002d40c0020390780705c0c3c410022004800c5c60442001482c0525400448025104000722900c85400058107042d1010a40d111080c112882c000a4038001c071100d501e80e04450404a01804c0000110042c58420f4044a0b11007282e4560400d2204078062801010040800410103102e146e44480c13081035240d2140000c4a402252800d1100503030b044050301c58126800800107005030701c1c0c00072020510120081040102c0305041d10000c0d40c0e60094460070b070044446001c12910f80304d03150102e0303001c2c201100454408c02001d101c1c040c01010074240540000d0100400815405940c1c03200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 129211690 1250 129210440 129210461
    0x5102406051206091b03040f020f0307060c110f040c030f0f0902030604020d081c09020102071d0f060a1505040306050a0204080a030f05040e07020a02010f050c030a030207080c01060b0c010f 83
    0x24080b240e507501003404440400603062480084c0320903a510070306980c51000710f115030f120b82d02d00300c0c0030081c0b841032006a0350700064003882600703c8001030201c280c3c00159011541c2c0c0003199850b00b88000e02c08104050004c255640d0414205a282642c00d905500312400c12060007008000c421104901c100c11240c1c0358500a40c91342051000c50054034241000600d442c1c00340b060f140c40c1400d0a40320f50410340c0c5000c0113406003a25142508255a0140010b01c0117009008a007207000900d8242d04a00700c50040006031840b0703080700450f0441d2100c3c3d1002c0050128508009004102c1820240840d0014070080321024105800915030f0542802941c007280c480600900c000344003980c0a0b80c0310000080003504020302803000003004210040828003581294014110280e030500004101810940700b60f018080b04014680d41381708000101c8100c4450303843c0040c0c0780e0001e480c109903184201c04420640d5803c020011450030030450040071a140104005c105429441c1c2e140c005071842c0e40300f03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 129212940 1250 129211690 129211717
    0x8100807060f210213210308070c050c030303010b12130503040315090818130902030c010507021201140915010e0c0f1204060c0e040509030409090510240605 69
    0x308080d241d0003411100f0716032040451250144500d2002101283c0004000700e074070680542e4100190a001c2c040201c042c16030043e100c0ea41c00b180c3c0c40c090916400602103d0420001c24443e0341804014088404006c200806403652560b41d006142d2554111844160640004030003194140c500310400100380c50f88500a1403c1a00d1626440c0145028a0503000301079150003c100009203010b00611000742c80c284c20b00300340444441440140d041c0b200e81d0048281c03500c00604003507680021030b403244603824680300b5960740d0244085450620100c400d801c5c50740c24000e04222020910030528455243c100031036200302c0708040040b07107607a0280f040d070b1180c1c1d6207000811003200d04031000704000d22052802d070780740a11040d0b1041e469002120192081a6107142c1c222440c4c4d4080f15080400200f29014001400c12100042d1641b1841c411000d5403070713540c10640c00700042808000e8400c40340b66030030003011645003000b00088132082604400d01c0401c000100700701d07000f102510520036103241d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 129214190 1250 129212940 129212957
    0x20c060f06011103070b0a020f0715020307030506010c110603180a0f0515040b0105040203060d02030303040c050913200f1801050a060306180e0c031f050c07020d0b0604090b01060810080706 83
    0x41711f41d0000d5128642c100032400e0304200990104001d4045081d4a030402040142d03240750004000b4201c5101502003810040c0580b00c0d0300c003051800e01c02991814044844030340d40e0711580041c0c04540c00650001035036005e8414040140b040761340c1007424050150342520907440d400e040260304218100e4000b48605c0c0e00c8001440107060941c055035014001500c40301070480541c001a01e036400880d402c50300300c40d4026050003181032544445405c20703400c0c160701d1115091550b41d2908020003100c0310f80032110440418180d40d86440c4107524120000d030890128068107441c008200909000d164094034652a0008286109100c2d0302e0407602c02c500b15956410007500030402520341141c8010795486030480c00481e41d5802d00040e00b04100e0a000603880d1041200070394240d40d0300410036882003109200c0040541c41e001030011000d540002588800e80d21940054002c0102c81c1c005481982c0120011410710380116115005680110016003115070303030300c4026a20151030080c03100080703519 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 129215440 1250 129214190 129214201
    0x810180c12030504030807050619021e09040204090615180e0705070507030c0602010c11070803030118060905040b0f090604082d0c03130605091c0501020c060f06011103070b 76
    0x480071000181c1c40b07440c15510b00366903034a8681840c1c01c6080140c440d90411014071101c2124090f2440e408070314001c05504084000604280e602550415080b0f071140c0010140d026940e540c3c111030250645000411050382c0f1502c552002c54050201c0502081ca001c4c03000300291410000e010403221840c514200c50381c2d40d5617048a4170340141c1e0b801c9655106a59010002490780e8828201510003940001940345956a00501a200c0407040150a400100042c8501d420200480e415200c41203400c600801641c041c50000341051740c801c0200e203161800b48000c01010200041c0074a008001d28411030702c0da020265122441a5001841c2d01001c120040f000007480c0000401070720744400c040d5140b6811144945d0035841042c1084007030b000000c0c42c03411104240c1d8403030094802842c182d4140310040021a14042110901d03001d12481020f0b1003080250940480d01d4078000e10007a10814200003005101d250310a41d102e0b0302080400c1d00d8200448000816103885035040140c40070305403a0f9 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 129216690 1250 129215440 129215459
    0xb01050702040903030c14250204090b01031b0504150509070908030a0207060e030610180b040608070e0709060e0f060c010f150602010b01200a021f02010c03050402010e10050409060810180c 83
    0xe8401281c00075101c0606d40041080cd28800e03000f140500030080c60b030005a1004007441c42d580c0c0107a8800c914081105c2c00c11881d442548003071702c0b4140e03540865601c81000c151115900e41d40105130a201c0010320124003940405e8078021036149844182c1000070441c201034032240d00719101c0c503601801740010425040751400780555500f114000003240c162402c081420749103503410074911680500700c1004802000c204590b403289003450080ca03081c1c01c08400409034250b0048541c892001000744209607541c0004030784580c1442c1008105a0550310000f070003600d40c1184440c04042b10741c034001507040c0180034005104c1c00507034400c10781c00c60310041041000b10706180114244250803981c801616022501441a4100940d1050491380c10380700a09440411300301c241058145024000180d801101c0200c0c820800c0382c0448401c41c19100c211140d001e41c0e0300905605040100000c1c01d900041815040625020010301c480004903c1d0640750180c0340c41d004108081d624400c0100045 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 129217940 1250 129216690 129216757
    0xb060717040b13051002030903060106050706110a030b031606090504050a0b2d100801030b0702160b0403050c0307030b040b0403111002040503060711060a0b01050702040903030c14 79
    0x10301000490034251518141d4110f90030122185001400c504000d011038038051440b4600c0e25858402945490351890110fa151360061048200f4000003091202c20008107800000c142c03030f211b000f01511440c000c04000c0140014103142c50003801480a0909200d10181300ca5068684503240d40c07207105c0c07404050000800e40101036100309540c1c0c0310300c01d40f0b9544069444030b91600c0a25265420081c16044180c2c0ca60704100c11480ba0389840c0e0380c90100d98100b0107890460b82c00800b1070702290b40740380c2c040e030034803010703070303648500068441c40115411907084054002d4a000d101282c0e03a01d56810107255845540c3e010143c140c1400e400080d000034245007200743d0144c480c1c0b0b170403107001c0200100301d450310f147c016130781e445990040b8050207241070800c0303025401101c07450400e01240e10540f0b0980c6030349020b4003a613403454540b100d0b900c2e140d000d00d003100c001c568060810404600300f800c004005010450855000807803601003000100c50a00581300c040941e003407005100d07168461100b800c110f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 129219190 1250 129217940 129217973
    0xb10090e012d060e011b02090720010617070b040e0c07050f150a0506031f02160206030901020d0612030e040902040b040f05010303080703090804140d0f150506040b0607 74
    0x1100d401c0c02e0b110102c0c0140c6100080050380c4805688050302d500150051084500b900c1c40c000400f01e107403015944030020030740c0011440c1403c0030350666143d01240310381414000003078558281440012039030803648407000e1107014101940e054589580055103e0300c02c0d4403504a1845000b000300b0300c2842e55500402141e4442e5044400428250040e00d041c07d01c01d02d9080ba0854200b810480b00425901415511880442c054848850540301c200c540000d0100c64810380359020907005a109030424540c84003580041521303440e407510b0300502d4040e501c05001034500c1418035100080141c51034201e4696140d043e103481800c01140000e2200a1035804400d99205849110340c0712981c0712031141741d018072407201000c5034640c1541006044090b010704858109850410140003040045d81a1401c1d01c2d00042008a6600762038002295098a40005854044200000003c01c1030424041540202c0700e14180540d40da80010081142d01a000048d0418010800a40021007034900c3c4200d0b407 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 129220440 1250 129219190 129219239
    0x311101106130501140103050d030504110d0803040c080d080403050c15090a1101020c06070602090a09180605010608011503050603010e010e0309090a05010506040b18030d030b10090e01 81
    0x402810303061520109450400044021595100500c2020701030002403004032207210856500d03581e246a655000504003604140d5901c000c2020044a545c0e040c2025100a011303004003120383c10403980c2c0350300a0380d003140d20b41060500003c40d48e901240000107492940ca0b000807540c0c036a203080c1e0b010303481010b01e00344c03500039005042c171450000050140180308080007825480320070303e01485401d00000a445c1558001082450203540d064100c2d625554800c00150300d8091300303000b08107910216000220b050f810803204a12200b0a0910902a18000c1c5000e020a9903102e6040e00c07010402c2c05601d4014803020758101e51540a038105580150000e40009110ba418100050841e41d054100e6402c50304005100310f480d2500c2e03a0165000784451108124951404001a17002c0c4160321803121301d0800490740d03011100b2446034603000060060305903450002c040740b00800410388100224031425000900c81071942c403d1421405032030144510304016424240f04085d50400c04689500d00f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 129221690 1250 129220440 129220457
    0xb0f0f030c0915030d051908161b0f03171e0f130b0103081b030f19020312010f050901080c01080a112a071a070f0201031d061f031110 59
    0x140d02c040145e90080040e0340d0341c0b43c0d140c5d084900342904001e65003034817204212132031041c48450324144030310015440d43c0e0b0030030741d201c08100d111000550314001d80140c00d10150004403410b15400c20342c0360700110071000b005c1800e5612280b145080f00c0d0a0702401c0d40c04131aa0001034034168401c1e20361500320f844180316403222401c40e41c0d080102c0c03409030401c0381c2a110104c0c0b0307220004c605140c025202401440510308240d240070350300d01c0c41c0c001d0840c40046130752582c120f014900e000740100c138034201840124003030355a1960007903084a400751060743e0080081600001c0c7e03101c004610410308440507922030071a80c5500e251040584200040c2050f903c008100200403491402007252540603103101069180d0107c00d200c40c200039107640b060403003960190001403e14181002c40c4c142c264800d841010404407400103e0060400b81da03030301500030030030b030000c0e201500c0020268410901403041841560741720500320070010701c030f120040c045030100d0001403041c5000e00640094001030300e0403800 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 129222940 1250 129221690 129221731
    0xa090605090d050a050a0201021b0f04090602160c050a0e04110d03050f0a08041e0b0403030f180b06040f151206090606060804030f0201050403080118060902030a0b0f0f030c09 77
    0x505481c481c4c1141c450b4800520380c1c00f1541c0601030380c04c003a11541c3c4e890000e6100b18001c68034602c03030b004c0e40612440d03940c50950200801c69041e2022000c9604e040380d40c160b1140351501d03007100e190050038480c031803001d000204585c0d100c10b080d103d50341c82030503d64420100c1041c00301e18002c900c030450912005010b000c07554600701c4040c080c001e45541d1088800e0605051007030032000d111185a071803c10200141011481c3c0540d410b80003545441d00042400d8450100c0c0300400208594900002d4034010b07070b0081c0800c40d481c15001c1c83c412a41080349c0b44c419001e003c2110794604254004403400c043c02c218600505003040c000381d016020111f591010703566004202ca80a40002010452403020b02082c50343c82550840a034bd407e000070007550800b41c401400210051103141000480c410044100006980155004001424081d0b4a0b4144405800042d0050b4080c1c94012a401100c6510b00c1c0341c644600e61403504044c2c0500b1280001e08140000c5083c010002c84001c03007945c04065 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 129224190 1250 129222940 129222943
    0xf0a05160c2105070b0603030c030a200601030303060602010b0906100c050106051206040b0c0901020304090c05070609110f030109020901090203070507171206090402150307030e12090301110a090605090d05 90
    0xc0e210341c49940703c0f82e54140c5440d0000c04000007800c0c49000f98000e021011500800200f200c480c5507241c1401480b410000200c2c480b482d2050019440500800d8000030806405400c0042651083e400070308c1859020014801004011684e059000b0200619244001e00850b15400340900960010420545500109550317400183c41d011b445e60001007040140002a608580c2111448004500d00780700070000030340d00d010f180250a070702980c90642d40360340c5028000b01e480580d070003d414006601c0a0030b0001030600c4d01c0618a000f0000d110351203040307180604c181c080c030035401003207500140d00f072218800003904002d01c0701c41030050401000010600c06c0704180d010b1007019049c250349d8040981100c1518a016007828040c8010f1001d010050b501c0001030841d440a810802d9100d44d04d54800710042c1c02e0084d44004e80f40641e007003607051140c45000524a20340305800a208400c101081c001c464402c05113214000b5003502400d010703491180d0000c1856850040c0254030400c150384486 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 129225440 1250 129224190 129224243
    0x303030c0d0c08040807060203130f05010c2006151504090504030207091413060216060e1e070b0d0609020a02060a1b09061b1a0f0a05160c 61
    0xc1251a0109840c40e1610706030103200c18850b8580340554072424250303034906440c0100d610007059107030044006240e0081002c503a11180790407848000004065042c4103009103401c54803500080c0e200000c5100551048a00c1d03296400a5030042c8a50340d1402150543d01c000e50246941c480d040488081c0c01c10300f00030103000a040400000501030400d45006850502c1c264001e00c04d46003131940000b80d00c003d801c4042c0c3e1041c2c03e6608400c1d43c002c8d0340342560003440340c0c44100d207040301c10317030b00110511407250b0120000f94000700482d02e00c24040440143c007800181c002141e0f81d40081001e00c01c01640300b01030104c8480003030011611980362041d160036a000b48a014006920034001c2045c800c3d441d00649074013072460f0300c0328848011020720040c590b072882d000312018001c2c640e224a4a040054000c020301d00e802003181c4a2041280c003100801d5582503540c200410940c8020610204003441080d011310055540c451503140103401c15038a40315483c505407065450b59968000400c12004070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 129226690 1250 129225440 129225451
    0x30c0f09030c190f240c020f0a0b0a11060405210f0711131e0c09050306090a020102060c03070f0e060d0e010b13090c03060b060408030c010903030e0c0a0303031109030303 75
    0x140c520500b00003450607a02410740c0b00d10704180e2035201c40c041c0440041032070854641da0341b500e000000d401e40003058030702075540415034108003070440014a048038107015004181d40d5540b400006806890501e42e10201030701d0103082d0303030440d1140384101c145e80036212202c403207040b040ca03041c015a8020700100340c018a800b640c1c20000740c145003080e49030510003011204e102c003804215440e808130000803c4010440d0000c01180e44210524603640540b00080003050010300b01e8034a0f140c0782d0207581e1103012142c4201d015105a0003c40c1942c4640d0042e40e1003402a44e0310410f0140354810121403014840c03482c04d400003030030070849080300c519004038400301880000100f5444502ca040c0700041e0445003542540303d1411001900007a02403040c2e9040b290802404200d503044500040c01a01c1035502608541c0b000007141c0c0403194040d0800040d041c040c0c1c60030030a2180303140c040c649521540c050507071311102850040c03000900035031020081203103000040e814841040d01082c550b03442603c8 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 129227940 1250 129226690 129226729
    0x30c030a03062103120605060c030904060609030f031407050f070e060406080705060d150801060f0b04030b28060b12070f1209050a060203010902070506010902030c0f09030c 76
    0x229245015018042c01008280c41c3c41040903288050b02c21007071015003014024100105465082c40d0702d90310b90001006414018421581c9001d203c0895a0340c1d0310012116000354105540010350310f0284200070102d03600910340034648265a6011101c242c1a900c0900b602203052040c440840c0040000c2000029840000c142080c20055003504d880070041200d886a0f08284003800903100100e0284101d60068a034161101e028100440182080b4908030080c80c800280008100314150484021903000162990300c5ca51035110401982c0f0842c000600061003400100b00400d5007004805602c043c2101c40c2030400c11080283c90a84072180c1c4050803855011910855101c40543d8840d0004280d08080300c5a44042e480902a000104520b10045a5450007581400014800b0301211584907030110b5a96843d408074100030b4111540542e071500c50b5400104503840c50344203ca000b448042e4480d420622101c098450661000c0211038140c0070300104001c0b070351030781d01217000311540504 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 129229190 1250 129227940 129227947
    0x906080a03050712051b0f010e010b0607020d050a05010e070e0a0b1f090506030703090510061a13080303010608160804051f0b030303070c05150411040504060b0a03050318061c1805030c03 82
    0x840c823420355244040d02a100d924000b0006c01964804040368942e40c1c4c15680b0288445d52418514244200d483c001b070255401d207074845d10f948402203042d20550b110760b031408080d512034000060031500d0008269030404029401c1c0c10000c8194621140b80e84e0072031800e0300c0c4507522140441d80e1504280c0301000481e0700c542c1d1810800805000e010b0104400000c1045444c1c50f01d020f50411b5213071038a10114504001a03103003074400400f03240c600900814000c4a03aa545d41c0d02000303024a03000c542c03200c1e40c0221f1903048289284510652802290028010700c803446400a00d214040010301c41c0d600019550300304849191803e0028602c00d00c81a103c40c60000101d0030550b04196801840810001c0c0b003004110002d852800c045250200c1a140011107540d0f03072070903800070030310301c00c0d0140c0c401341d85a0004104100000100305188210507405600044841809901d004001c2410303803400710b0b581040e4181d5103075480031040d4044551600720b6003145444a509607881001520130a41000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 129230440 1250 129229190 129229213
    0x3060619090503100905060103030f0512090c0a09020c15150904110a0b030c0301030f03030b0405040b070207060905030c04020708040b030408040305060f0103020108070f270906080a03050712051b 86
    0x84c441403120034114039007405051300729510191141c605000c001c0500c40c0c1c01440d06503140c814020f03501c44c204400c10900d01801c0409859580308420070b15107110781811080070804000300d0007519103040f5541c00409800e000e40304807081505008210203464901c400040020750307500185180580d00440c101102c19444005010510060303400849401d07104106010207226000c0c100c0c0d0460360000c03503181305007030380b403070100c01400048c010107600c1400c2030140401c0c420000381560080c00d8940803284c40d01d0b80c0b0350054410f01114802c1c940c0c180c0102d0104001d0742060b0300100740a82c0300300300c8140b901c0d403101058900c0303800a40301902c0590000c075051040080c10001d81e40c0100300e21901c0e40300341d80340d580002c1600d00c000f89004200440050001d0801340290709012071090012810400c091044480c00c52115035841082c10060610400060180d0f0128000f01c0b2030341c0656030185401c0305521030403405a8204203001c00c0080800c00cbc0071022622020980c000801d0101500c42521003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 129231690 1250 129230440 129230443
    0x90503012f07020d0602030103050f060901180b090715020d0e0406180b0d061a0405060901031205070809090703140603120d0e0f0d09170d050a0503060619090503 71
    0xc100784110320020600c0c20040100c15a586840c0381d026000341c599440001d0702c04514205102d04000b0a0780d400400040b08000000c505c050070035079804100c504030303941e680074a42a510248450303a200020342d45004040341c0c040128035030001d403640460b060030b80e9030b03451030000072500350303040d0010b81210b80c031b0072003156200c8680031106404950500829040102d915448503440c0940250b4a680f0440111a500c441101b120950341243c0204803505d01100007204010001085622492412000410b24a040d04603c2d059a42100320100034441e0320400fa9440d0740040d80580e0440c4e000d000c0d0f02140d55454191505c03c15440d64046014100400301c5560060003902c0e0904c641c220406110814240e14107807660030502c0000030449400612401d400c10043c1c0b0090146402001d8444510079000800c2e1002c46140c02084030741000c50724481d94464820040d0400000c0c810030200b1081841040038640111005104604c0e11144501c111010010b0302070850200b911070310100f046140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 129232940 1250 129231690 129231701
    0x120a050612070e070c030e091f08010e0606010c0503041e030b0903090d08251a0702122d03040f031e0903080c070e0a0603060c1b021012020a09050301 66
    0x14004002c00040f0f04148030442c1e142c400034000001c10003040001030905104d50300d420a81c0c9000303481c5082c3c03030070000410945102c19102c2c400e04540e982d800045c01903030500c114141d03000110094030080d100c42c00119000c1700307190700580d181d2100380004507040d4000d142402d03106280b150044095071661030f080780d54070001810858035810520201000b51a080c3d07980007003503840580c199865030b0758040c001c1000d915124003041a0003080d0618200410081503000780420100030440b5035072001412a40c2d69181d4400e40c1460b01c2c103010b404441c1c05000300031003181302605070503520402e0403c20440e4640003110180d80302c1c074121160906140e00251407400700141c0c100c2c407212024502070007030001641171100408210303001039000c050f05024011080540031070320760510f2a050002141010b052103000a449242c60807000c00c081038002c04401003090351070b015184050316107408000081e1315991810043c00401c0c0d9582803c280301d48020032040550b134030350f240c2460914061500311407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 129234190 1250 129232940 129232969
    0x100507270e0601030b0f0f061b01020915030613020304020609060a0203130f0501020c06131203050705010b0108150f010c1407090b06040b030f0901020f1c05070815010f020102120a0506 81
    0x10f24051709a14a510381c9008200002c1c0c0685055400c0614440401e03814417410703076a03005003241e01103104050a01900181200c00c0105c0740301130402c0007004900c49601c81911150303800819455155030004158000c0e42e8440d0004084905002010001c40d6069000c0c8140400507000040d00d019072143c5001414054400349034503040c0c40307081ca40040d41d00d100081d0303184d00c614400305060000c00410308610019042c02c01010030002c0407480c020307180341c00c546800c98042d42010300c2c2c880203512900c44a44102da4408403050381000020a000950524030030711340c10800b121200d1000701e40704030080380600704840007d001c824078040d502004c036020310009511600c0c0800040101104560940390426181c002c40d00194454505450091184890b810040b4102140d210801f016180741c0d0094408403c1c0103002c0c903622044101e642c0a01294502d0840c104861074010302d5226110280910b0780354000189008000d01c90007210340412540b054156803203000304070190800341c00320951007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 129235440 1250 129234190 129234197
    0x3060e010507054806010602030c0c0d02030a0219051219110a0f090507031404030c060b0303040f030602040302120318010309021f030b01080c0705100507270e0601 72
    0x5003400380000380540300f213071981070b090040d0300309048401d08880c41c1190420086102145181480120340052909038006a1003030700415000050050002c0708852402c4582d201518080d8509010004440483c01d003d0341c03d4440e120701000182ca420301c078161224001c000402e60355140004010070030460303034024595500142a1b07a15040d800c020b204e0340d00d650000030320502e4440240842c580e01403a900250200101ca0000244d80800341e0100f4010040b941e42840468655004107200e0401aa401400034558a0720203001c038105900c054103000000302642d1400c0d0ba517004901844041d5082640d9091f4006420400c525001c4291b040110048001d94200f2103e1840c1c3c40c0d4a0748a105000d05040d1038100349011595605006408007180105140060001000c01002040b0f101300b4a400310741c4e0800441c0b00b00382498151000c40364840000d000b032000700030407a0003a0034082c1c40e000a01c000d0000a2000c2300070b80756800180c4800c5055143c800d447c1c4400c440300c080020b010107050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 129236690 1250 129235440 129235451
    0x10606030207051e0a050604110a120f03120f0c1d0103050c0301030b0c0f030f1b03010f1a040f0303020f2104060f110f010b030c1512071101021303060e01 68
    0x150001c600e130600b100701e29110b4041d05004030140760802910043c020168052181004100620742c60300401c4003405170b44c69039100d070b03c485080c16950960000035082542c000911000288101000344480403041c00120340201c1d6120500300342c030070425a5402280e05d00c4200c6d000d0100c41c55000c03100101c2440c0500c02070400401d000040d1006000140080c0700c9600002ca40c8042d46088540c0e07100500b8601ba03803850b2601c8120f440c00d03010744602c0c4070300442c0c0c020f0300203000d031540641e0305851500c144c0000306850a640c1424000c401180c1e0340d280881808005410040700c0c404c0780066010b81c015040c2c040602d5405424400c50341c07421800b0307405a0350102840c25641017900c040c1c03100fa007012005880003041c1911010011207000c0d03c3d500c07414400050301e070410341100700d00361010b4007140c005221100405c280d800822a4440c9002024007550300700740742c2c1170f800540140d40c0d801c103245c0a00d5194031003401c1ea40129800c00104020b0b0200300700700300b840e108020f04400500001c000d03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 129237940 1250 129236690 129236693
    0x40f02122b0c1b0f0b03010510020703030509240301030602070c1a0711060d051005010f020a05030a0f140706050f0a14010902130504021801020c010801062a120207030203010606030207 81
    0x1004012000d070240e0f590601c41c0088080e1890b140f0040c108600404002c40e548a8901171168000d0203640d01603d850300110783d040d40009205401c3d650706413101c3e8100000f0000b401040d1158520b107800a42000c50b000c8007200c41c50004501850103008090b030303101050b090207a00031901c1c2c0d202811680d203101d01a806085039001b40d079032140d03000d028030302134680c064002400c5000b180c528031449441c2c07605022140401c110b456003140da080c1c8421184111000059888400c10400075140e50820031251800345c5c415401c041010005040c81c0c04441400391801885400090085403465541d10522142058030034400e503021184840900c8500180480f80680c000d040c0b1403e6841078000c5005c03500c0d070941c00900310281c10301410864868070701d050083d0000400c042100e02500501c0d0f120703d5194800c4001505840c42c603101e07000340340891607258000c03605a0b011040d052641c00d1107000082c5030b9035503400380300c01c855004010250071401014212413850307200c2c00c01c0c1841040682c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 129239190 1250 129237940 129237947
    0x102060f040308040303050a0f050a0903080a06050a03110303040810020408070b03070c120203091801090b150a0c0305070c060224160309020307090603080304031e05030609040f02122b 81
    0x1a401036044c50b012486481f18a42c440181a21a001c00d0049c0d0078041044903808031640803142590007503407100f0303090311034090745030440d010b80c006c140d00020344150500102c3d031014003090101002508407031410f90b4030b090441c00e22031807d0b4001c41242d00018100704505081001c88041c01c24400036a07e103041c1560302400d08240040c2c0101441551500900c0c614024819102c134207a000d42082100810180321211486090081e415000d01e410404c1d1a030b8101042002c16580d166035a080c504184d43d40c0641d082404200110200702040002000061080088000800315a00102404e00030110000d04007600d904803c40b040d00c45e030702040301201c028203a8214901e4103040005c1c480c403540c0046800e101540e084090034900780310f000010005501c00841c85940a55150000824904501d100c2e031851103101500044081c4040f401e64a86002d0154006101c1c11303955003218019404180c402503c03a1803140300e90804403070541250140e0100c9a0011410400405460b07403035031019 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 129240440 1250 129239190 129239207
    0xb07230c01170901061e21020d02010507080409090b150904110418140609071403030406080a0e0a120f05070507060807020a201203031e0a020702060d0b0102060f0403 73
    0xd001c04810b01c0301003161036100b03500c10405040e85242c1d0351400c4280b61007280010030b0a10403804c074075a0502d40100328045c2c0c141c840700400d900402c4c0500303144036038004660300d80140c0d10a07078070b12404003c0025056850305c6480340c0c00d48140b003400c10925094101154000001401d140100b8a080c100800142c10310300101c10b0345422140014007050f240480100c9004040d4009c0c0307091140d081042c13003140000b030700c141310389c01403001c8400b15a200c1d0700032008001c5440440b0b8140d4001d100c203005090080c0030880d40080154000203451365814100d6107080c44d0307a0020b503941a0750002d100c0f4156848164198800000e0810500e4054a980e40302e50b143e81c103110799020801720070b0101c0c084034070a10490200325081384001c0c502c0f0144c41c00c51565034040c910410311a8a103c6080c028008012064031300c6500000d070758440702410700a000c03c2d2007000904440045a0070800721005950f800081c0c100c0900172000080c09407130881c0003a290440c00350039491050340e100704010000b40e00207203c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 129241690 1250 129240440 129240467
    0xa120507020d260c210a02041401020304060831030903030801140603040609030507020a031a0a061412030906040b22120f0303060f030b071701060e060f040b07230c01 73
    0x700d80d201d001c2003185180182c0c0702403c41d000ca417481e092000201494000d0300584d403c005810191070240c0b401a81d4a00c5913101d1400410020720005540700e850070340034104452000304a460b001d00741e501002180c208400200c0c0030500300304051051541c0400d05134050181c0c01421000c0134889000104a4080248020807098803480e04004251060003a03664480c1d024280318181616031800d85403c0c1607090940c004800d00c1c10004030100c17201d000358001c83e00c60104642900c0343c1802444005001d80709268031a10041000314400e8664000400040c800900c03165120407582c80340c01c0315500116001c40150b444000700b441660300014541508075440805040101850300c3c00760701800455008000f148d45801000051203c1004401d20804241c0e175600e4405004040440d070144080c01642c000591425268665080640007400d01100c0402c03050304250f035418071441940d1141004440f00b5000121166050010080d05000c05000034003801100074402c000030b0405080500 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 129242940 1250 129241690 129241711
    0xa0209030307110a1d19020f0301060309020a081006050a050607020f13060504060303080609070c1e05030d0e010c020708030f091e030d020609070f1401050a120507020d26 75
    0x20102003503651030035480000c02a4044038003040021603d4025045d404446419150b0301c0b400c3c0f4104010360910888001800d0070164030b06503400d000048000b070105200c101d8024076120004680e40318100202d41c42b9881046000c252141040b003440040f000c0303580618002c1105214540059030b0740c0c90b48004c000030aa500c418800240c080752000b0300784d14cc6c00907402902d007207008010315610030051071003400151460031494071441405c0f20100c0640d94080c2c411161030910700d04400040d101500220300032001c803030030410704410080c1259142c0900b4001030b991802c001c52010303010300c10007009100e000040d60801c000805580e5a51240d10301e071070f1184804110203040d502d12505080bd01580250460f4442c1c00462006980c440094030340300201d1007441800500012503038a00400d41d4040a421880c64141d01c0c0152110340200301d20b041400b40010000200e6810340c820780303100e020386900400810802c0351000c5c0160203000c03503910403c01e007a014a19090717140401d035a007000003041d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 129244190 1250 129242940 129242963
    0x172a10171f0b070807231c022a0a05060c0d05030417190305010510090b0702041d030d060b04080613020406050402120627070522030303140a0209030307 67
    0x1aa5800c400e2250382000c2c100b020701140080a00513042d01034600544110f0003425548407455900c02d444000312203400050303101000004441c0710500110781c51000c140100c6403500010b000d40d9507000c46400081135002e40c001c00055403407400c002640c0c010f041c207072000ca182c02c40e500e24940c0c50341303000d042c0d94051110000108041040d03118a2046440d1103815164886103038010300d415688081d9685c400107070078000080313420303d0103001206481401d91210b070100e918100d8503d2880c0c001c401c090703130f01075907408c404020036840d410000b400c1d18500c4082c40d5a40b0784108280d003101c801c0e410146400c401404203008041d4000341070f031f8219070403503500881141103100007005004103400c101d0f00700d40040b41c9409011b480b026054021581290000303d00d9507402407441c0028400c450081406480c0000f00f0002030080000300b0700103020b10381d00841e0100c000c880e4041550705900480c0080d40d00c11010920f8840d60f000590000f40011095191249a034002a5a0701550802420304040354 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 129245440 1250 129244190 129244231
    0x20316020105070c09050a0f020a0e0423090d08070c0209060f03071701021b0109020f0d050c0402040303080405010c03050c03011802090406140312090a172a1017 71
    0xc2c402d0380c0a96a2000040340c06544480c180340140c1001c4e600380d41400c1c04d06113072106040c500d0080d0380014801e6914480c04036202c0080001a096050a01981054000c42a4400310094092901c10b0240bc0c004200404d900c0c20002d0607440f0040459081100d91198000140c2ea140d2030b41d600500c00300e0b140801c189407000080d0070042c2e1980002c0300340040603410090400190003904d10407201c0b1003c1c1d01c001485e544c0b02d030b003a140703034100007580102442419011b038900841410149400740080300d02800c10400803504a030301c45d800a0b0086440c100400c41000024000d20120440b03515040c1300074103180101c1003aa00060003280f4a004a0080c0340c078640301c503039040d90310005c0700030400e02415581d484400300302040520810702030700130500d00340050f030082011a6044107016110241c42858602e08200c00800195011414003c8008000503d0a40c040c0c00e050f85904103d1044c005088504221290602c540c4403400d01180c00640001280780710305166120701408024510007108 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 129246690 1250 129245440 129245447
    0xf0301210b010b0c0c030115050f0909030406050a090803030403030f0f0e07091a03160303030e0d090603020a09151106100302130b030f060a0510141003110f0f0c070603020a0203160201 81
    0x40004141c3c06d9032a12069902d0003203501e0f0341500b140c80644052908021000a2041e29071045594013600c2e8400c00081202030311480041214070b41c10f00c3e04603c40d03519480c032241980d00542c3c0640c0003d0720b900c20890f02c0140ca1040e0b000d00c40c1000020130041c1054990181c4a0015100720071905a40300c0c0071031317100180002908542c0340c000702542c0c184c4000d05013030b204c034825500040d00001c1ca00030800174600f00004410402c11590b44aa4020038504103046010358070800d842c0e000c000803a2030002c0c10b1030344980300f040c1806003a115070b001150b0618880786031900080c1800c00003402024201302507250700300c0c1e10140e80240e507404034030058803e000c646460040881c6d1403081c45004100202030b101d540c40f1a029214002c03071920324580d83c50041c452602c16042c0b03a94030032900040b0401d940e000b5030000b110040509022170500400a0b9003640e5500000350000400a000621220807a0248020b101030000c0382411418a103007454001e42c3c0340151282000c820b40030b4601001503a00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 129247940 1250 129246690 129246703
    0xf010e030d0c140d080c16170a0e060901120e01061205100501050a0e0a020d06090e01060618060c120207030510020403030f0905010815060403080f0301210b010b0c 72
    0x1405012a0829240010001c1541201003016030311030060700f010300031a940200e0300b111203540680d141703249510342008403030895106480b040100c42c8004021400155803108441e04801011445a121000094044d00d840e54685d02da0b44507620130801034a2603078110348410001d1444100000c0c0111040741641d0041415401100302ca01819046a04112000a030708401038240a814070081e60b07902c06106601400313000321202030310760030b00060000c2010b07800790000c2e140c0140041201c40c0d50f41d810100b29a038490b6022440e94550b0030901c200341c0c01c808926449900001d0601e11203151660040082c03003848230080071841d0105000720300b10301c03c0107414007450b045015214824034290518009601901c0101c011805014820030964000c021100840b03c044c0c44090990f40c2e4a08140801c100c18070230640e21640a00c008030224007070201416403420000d400c50307030340e50410f004901c8607104d54044800e007c0036601490f00040c0148000360442e4502140f29407a0740c508990b1904146 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 129249190 1250 129247940 129247967
    0xb0a0201021b011e05010305070308091807020304051908031803030706020301060314060d03020c011101110c01050f010e10030b100e310506010320030a06020a080709080604020f01 79
    0x1d03501c442c60660b001e01035201010008040307814010081d003803030a07241520401d01c8090481d8000040c200003081425000703082003c40140701d24501043c141034411100800d881c0c0c0310040e40081010f00207810403c0c0e0850b20212000e0700b5207a41da1400c04015900d21452440e902c4104c0400e0101c6900e0310704005070341d051603210b80c0540d22580c407500300034020010300100c2e1044e0404c0c800800d07484d0030070783c044104094240d406460789030b9030007005548115100c0350705e441541d41c03410122100b0a40a0183c07126a01010010600341840d6113074001009068010a0040402a05222441d050382d07000e003003140e901040d9a41181d5030780198421440702580302e160214100c0c002c10040500d0303401e80f4a428146041801c403000c0115250400c0b0344002c0d0740007842c0381e0041006002081a4099072407030844003072090180002003030003080c100b1040c140308451583d00411810003141d0000c0c03001d5400403181c5003084225103418003166035802d000d403010740525050380795000507901c1020020f0882 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 129250440 1250 129249190 129249217
    0xb060f12060a090302011d19020a0f0b07060c020d050d0e070e1515130506030405010902030a1a07050304080a0e03010b03010c090602070b070b0105010f03021207090e1f0b0a020102 79
    0x9142c0004100c2c00f501d0104012401540781000d84440c0c46044158484540b10711070042c01c0301c1a4010741c0c1240e241905c0001c0e070740320240d09400107204502d803040c003000c1c141284441d0b46484040c60001e058900300b21100055401c1020204840d42d80070050720400344000c48080f520459000c030b006e081017016040b0a00104c05002008003910b002000035540301c0c0103403107070701301c91a1205030462540592600c20000040510381000b05140182c091030b009802540009a140007540c0003130300d4030f01103860403130361010350b8841d880d00032041100140e80700c0414100300b841c1d85825624800c0602c207411907201401246001089140c60075406100d698102500800000107180c101400340c1c0c841d4818140180b0134801c021402c2d4042c1c1007555411b941c484000038459007400c005454062020f50100100f5909104034909a4502045c15001d042151111241d150800003c4c0c2050200100b401142c818500e00707504040100c61a048210b514010304191240c9a0080403406071040700950000b5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 129251690 1250 129250440 129250453
    0xf10090504050c030702060f070f0e1801030b090708010b011b2105031501030b150a1701030c05040e0606130b03030d0207050622080324030d020106030308060d0b060f12 74
    0x8050040c3c02103018032282d4007102d503580d8a52030307140207503038003114400e000941361001c01040314014501050107100c01000310302014002449c40d803403400240c0c4281e80e0f05601e44140074921609000100203040840000d1000c550080d0020305500481102c41858a200010340400d002e2144181e840070800e000d04403a4480070385800910f141c0017520521170110601411401640c002d100e03a03005000080c004050050401a4420854204820250074030008522840700c001025804501852240c0c1c1c41c044400e0411042c0800c4604000c0c420a8540c03040c024082107503902030308901c6061003200b0100c0e02e20307144800309055000b6002c41c0e00c4814008115501044004100f185c810f2a522440070421000b420301164140c42d2214040d207655020000309054440c18a000043c802e50800152991040d16010900d00940300100e400140d540380403c3c03041603402000c043c2c00c44402c840d645400c4030551a00040818003521283c41200c480fa0310745034640300e50f8510040e0000c090141c07100b = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 129252940 1250 129251690 129251701
    0x40b060d060b13050703051515031b040b0c060c030106081605040801110301031202030702130b040902130b010f050c0d030209040e030c0a0506070807050d05060f041113140f1009050405 81
    0x184c041540d049010a040c5000030b07081e04003510703098110000041c8460710f109030701c01183c032489e032000e010403087d10800341500043e101104001d10003000904a066078501c0e40c0343d03500d4101a000340c11044240010001000700d180e1015949411607100325644180c5443c00c802502c0070320499100d05440c1d420250407004091401c0301a5040b40d000c0d1307204810f4a0074950080b6224403a010009501803041112011120556802580b40c80c5024200060310441070300001c0f52403245000c0180c0c582e454030244015942e000018201640807414001e0030041c11801c03a544980070712840c00c003015804600a0390f241d60741d400096030340504d402500d13540d040c04070700a07803202031629050701ca030303c90381c0041222103200d589103d00c10b1982c1d98072035003450510710050707000d0f140c05041c0b035078400c0d018102444a40d54612401c040f422103c005240c2d1040f5040800d6600c600d160300044050035400b1400142e80c8a00c24003001c03178101201c185121034102e0105803040000da80003103030810b2400b0304102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 129254190 1250 129252940 129252979
    0xf1107091d01020906031306060503060f0901240504360201091d01030605040f0507060e04060902190e06120c09040b04020a0905060c1203090307120206040b060d060b 73
    0x1800006a20320001001e0404900c80c0e0a03442840a03994004c40d0820004585400b0880090302e881d1041c0c0010501b0b80e43c0314000f83c6410415181c048000b0003940c00d01c10581400d00c90009007180c1c2804211100c4d100b6100d904c00da014521900740541c1d10381c02010401105060a10740d152152040340a00c05501d820000641e02001e00c1240400c01c4003501040c0000031172544942a5400f208800d9941e09550300d51000e007502038070840e20240c58108890000e1010321000015001d2aa6600003420b102420003081c1c03195075010307028151041110102d80708485141013210b2800d8203014900008a901040d40f9100704028038045030107070000d00c103000e8072850003410107240484007442103640c29400c100807403086044e10320225450520811090800a01403d10b000c107200640f0521000354401180302da1046071480c2c05604001810001c20620b100b40f0360421001d840200310f141703002e584100c221000a01118400d82068165604002e8150040d072003080024104e50204800a43c0e0f90307 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 129255440 1250 129254190 129254201
    0x2031216091802121f0506072d081207030c0c2001020f03120a0b0f030a0b0c091c1406040804170c100203120603190b04080c07080a03030e010b010509010f110709 71
    0x20f00c03891800c10000a07107240c44030039101d013a500627000d40c03490b03100085140d0680015220740d40d408602c560f50b01022644400190100e010680070b1508240b40401008003204c0c0c40520340010b0000029200b40170811800d444105400070609802d450400040140d01d40b0301c00001c513840d075100001c2d4a080c80158141580d006814a410501c454044401008843c8a5000d5001d800d940880003030404508000d944580000032020420301d44412507001c2448035000708140b8031003da4060302001000520040c145000580c440580014102682d07030b844c0a06c00c43c804c14096800800041d0310b1010305004189001d42c001b0445242801c0440001c2d4403603f0008d0000807190301000001c1d040e08011504241c034028003000c002d91706a450303030344500c046009001070300c000c4024050800011001c01242c2c019015000040c0780c4103d051400409031018050481c01c0713641800050815a6003050070384150283c00d0034101c081802c104821100e451307640d41c21440e54031035218005922040c5030b204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 129256690 1250 129255440 129255481
    0x6050a0f03050105130f020d020d02060408010209031c0f08070212040f14030a12032301091b020309010f050702061c0608070f0f030209090f06070203121609180212 72
    0x344065541c020b0300c0b09181d04032800203003110031b40440c0d120040c5409294480c55520041c040591031b071142d000310f1100e8210f50400b20040e0340c0000c01e1074a0340703001c1020b20070040b0320080b042800a00400000c250b03103000148c4070b040c031641c1004107220034000d120440d40c0d4643c400c0c090307450b56075905141003098280e00c2009544405020344980074140881c07041c0500d40c00c24141034a4094a40c81100280704c0c00e14100790319000b844091106006001d050f44c0209030781a0085055420329400c64041600c02c0c01b407000390b602c04c00c8105900c2c3d800018400b8000c441d404d0a540350011400840c4041c801c01203a45c0c40d51140411042589416a010206a0ba4110211500e06444080e2a41415414010350042c29002c0b1010401803500c42036443d0b12500c0d0606407200f25024100c0940391090554034000503800104034600d10381d040070100c562141d90314030004603c010330403014000790124010807005840010310405d030350252350111100b14005014031146880c21000c0e030346000800d00034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 129257940 1250 129256690 129256693
    0x30601170a1b050702010c080906070501020c1c110a0f0611070507061b1a0a09020904030c02010e06041d0406060807080f120f030c09130f0207050705090c070201030203060406050a0f0305 82
    0x120402c16900c103d054400030756041e122007034541019215110981c004044c12607015204100d0340c0300194084c001350504d81c900900910910a1600000d84129691414481000300044c04140242d41c00070b4080d01d091307002052800040310354240340014120f402c100c2a04003900180c40c50400c440000c1c1300040714001e43e100c00b02c0200c50603a2400303180c40c850b005403844091a80210808828039811f03908218180b0700012182e00700d034081030080301d00b10b4042e404600c00d61108030a558110590b180505800c440803480d00741480c031541346500d00440c200d0040c0385044005410800e02d907000b8005010010115084281e44a240990324100c0070b150880b240101600741040c6041c49050300c80c81514604003e00b5642c400000e01155040380402641c4030f403580d06180c0306c02e038040c850702000c8081c039080540d50302c000e410410320782030b5903074000b40c0580c98010401c030710000b03000b05403071019030f0918000d44c3d40d4648500140c0900916000f5076807101c00c0780380c00608000503420761000c884c401d00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 129259190 1250 129257940 129257981
    0x9030807080c0606120d08060a0f0617100609060813020a081e010204060207060c051219031d030d180b0903030403020d08040314032e05030c2202030601170a 69
    0xf403007820b086841c505c0c541a03010203840c5080714041c00140d94000320103080601c80355078801e440001024a580700c0c90104045000d110980c400e07807600d0340d038440384241407a18041d140a42c014400c0e580d51080d001080b000c2404038007911134025083c540c0d070350010800e0340d03515280c560688d120382d260150341c10081810803a0354070340d50041c02a036040b24002d4010307014140c681340e001d40d0440d030711403000c45990003034161450307140340440050031255525074045032410b00c035804007500311402c10f040c0c0011b40040e681c00c6184030200208540c10101b086002151030320440701403c0b81040c0680c401004404608104558884000040e600c15802582101c18403d80480d0079520440c06070380207030000d4a00c44003041020000310086801c0095510303214044105001218801185c4da2102840c259440d5010001031804000d25620414200c6400002c00510b032541c414030048031801c500180e40210001c1c049a001e404100d003000c0a41400c492149001c07411080100380340440351a06a8045 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 129260440 1250 129259190 129259201
    0x6020405100801030812190f0c0e03031216020a0203060a05040c0f18021303051c0306090c02060a0c020a05060403050915040e13320d0c020d080a09030807080c06 71
    0x30360440f030480350020003080c9842000408000d25600080000b2198449040c030203441c2003c601c00c1c80f01c0c922011100249205203290014090820841858801da205001281200d4609000781e5080032140950344480c4180000036030500c4410500650300d40100010041380500d9a00310503c0307188070b05803000b040d07500e07090047ca00b40068010001a00102d000040f55581c0e00c5d4001c020304801a02154034050762580c80d6442c0c600d65651404044d140000000f0100790180164005400f00e64020b01210041180007907503814003c087c045542c2e01d902078007111a000b4419070704990741040c2600c0c21031902d810086d013203070300c0701c403c0b41e02541c0113107405002115034070141c07003e851181040c0d5656859103034102105801003042626001600b9208005104814040322030704040d0300c04400c255211088028101080b400d005c2007030042c8800c1d10401a5107112503100000e501002c042d80310078072154100e450105540009281d4400041c5810a0001c4030340038000e09640c480450780b0540c0d81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 129261690 1250 129260440 129260447
    0x2415010302040b07081602040203041a1501021b0409050106061e0e0f12011e0c1211032716031202011413050c060711090708040b07080703020706090602040510 70
    0x2c81c440c98560200034810349001900c240010710144100074001e02d509189074001a0481c2c1c4140da044855424154004000400407520b29901c5038060000018040003400040e4036180c0c55410058a1000440821016500c643c07040c00115009002000540d40381c84014003040c80c00c452000400003101140402c442c4501040840000c01500c9088002201070905c5030341304d0b40000c1c48450b5500c4000c2c41e01000010f04040403c4038981303001080751092500d0144c01c44098030f40081d03003103050400c03c290a8804c1c0045903040003c002c40b01c007640380420501300c02e401e01d050544040e4007826424110401c001402c0e08180ca02403080620000450035059080300d8901d82051140c075440c03400110301d00191003101e91150b01900949540d100140006100c90748400750440713500e10840c0c480c20841c10800a95940240b407802e0180e1582030540794410703803e80052071001007084040009901e10b220740c050310ba1141d8001b005000700e030b01c0c1d40350440c0650894044c840c0605000b00307662004512 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 129262940 1250 129261690 129261697
    0x709020a050f031315020a091d04110102071203020a0b010b0c0705040b0a090f061e060e100c080c0a11041a09061c050a03090603110a112415010302 65
    0x5103516102d24102c069200c0072a190401440302051070324680c080e401103488940091002d00c00d02c5c100603902c2c150910040e01f04a03658029074104031090610000ca4151100000c2e042500501c402286a01c00130041f0719281d9603800003484240d4184120b81016000502c10340064421111312030703145e0301c441d40640240641c051000c100c1d031201e03901304481d0800e40c0c014840d107440a4011510341d519065000140c90340c90306000110341c6d50b94802c01c500380e1054401e4200c4410041c5000c0a58a0018020040c0b100b01c11003074841d580c0342e58401039060240000c0702103240c0c070103c4140c4503280005516250400d07202c06035591555040d285220b0f02d418070625802541c0c01e640e5803040800a014801424401445139810140301148110441c003480f10400c81c0c0b078407410040c108841c00340390041004a855003c00706241c04c03c0c551008900350034080e81c251120380c0c90040c00c11001c000d040c40c58503040d6034064140350f110300d108c0c0c00403050381d0315400e100302101d41c0740c2013000308000011001c038070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 129264190 1250 129262940 129262957
    0xd0308040501110307020c01080601051306051b03131802091804020f090105030a080304260a02010b040207030e040f1d0d170c03011707050312030118090507120501020d0c03090203070902 82
    0xc01034100306c1050743c01008272680107981850003d09103083c10307900c540305540e160441c0c404101c001c074054986040740d040c403400c0501c21601442c00c3c12600d1545090180603401817050108050000c00c8000c030b140d80c11340d419182d0050a402c4604c0034444e0f00039020100796030903130081700e0004c241d00d080c3c1003d07503015040707440c00b400404400303440d82c0b0b0304140f81c0c1020f00201c1d6442c0400640040242d0340240100b200c182c0d07006140da40c0c1c03081c80f101908641c075004c66240640d0045c024040400d8200c0000e1340c441c2000c0e200412101d00c3d0503410002800c00c004c1038255115145601c80050500140c00003003001540c40d180d05a66282440e942038680c00c03160000400303000c00040c0002e10100050000c402c01c0602101c100a444000007424008481c42405610345d01000400c1084c22200510522080c1d8840c10446c01036203440d030a40b1340390079024502041d10444140c0342004400d50450304200c820701810002d08820b950000e0150240103000d0388a84200080131404240c02c0c422200c500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 129265440 1250 129264190 129264193
    0x5010c2c0310180b01060816020705010e010c03020a0c09050a11030f0c090a1a03040c1202100e0d080705031801080f0103030e0f040507111204050d0602030a0207020d030804050111030702 82
    0x44408a0050b8080d01c0d55400f1140120300c038001c660005040540030302c0c003901c0d581e140c006142c94484404134825012451407001c541c00040c04202c9070740c022020f444406401c0c81c04000d403511a00341a0310304200d035400200f03120600c840c0018200302d41c0e404a40181240c90f0144565800c0d030851121030b0009503001e40116240e03001207407040ca000d00090440c0304010f0560400a41e40341054000b6500303100c80c5640c45500007040208101441c1c2a0034090046c8166411405070546c020414130901c0210201c00d20602c144000f055580702040e01500c194080b005940d0707240030381361480c0c41e50090644c0c1d44020b0094462418036600940d4003601c0b4809488070000268a161421070386003020542c4075401c441d81c2a003d124a403154000d01380714100316120400000190424549480d18400040c15918810720051010381c0d84d82c0c50709008240c10210160300c3e9141c00250100070700c180307176000358811010038200042542040d015441107008030002c01200c64040c0c80103410744021141480107 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 129266690 1250 129265440 129265453
    0x708030c130e01061206120b1b0c010903050c0d020114040f02040b090903030f16020706030e1915061d043c020306090d020c0d06020705010c2c03 64
    0x11240d444014010007206285850503956540201032800c107420f801010014a502800e881d540c0c40b1350217000000d01c6100202c064045858441102441001e4204100c040c0c0414065251022010640d49500f1000008001c00201480c000d4034a50100780401d5450144c0d02130422411300621414035500c0d07490802c418103580c0d0b660748940d89800354030101d80c0540c3d1b542000d0345949440040511405242000b1980c034241500940c0200e140184040c3e42e56000160300c0300603c0d03022405a0444055080201c0d244070100142401c02c500300703c8112101619070840400d00026820403a01e00100310070800c40203403214105222254030000400004181a01090000e151154028000b4001c00c945045d4409000506184940b07481401414004e444810300158901030020540100802c001400301c40024003020f0340b60303003050029a00c1681c06050680901c8a070b601100c0f03041d50301c45c008009008442c04003412400c6034481104c080d01d48003548005450455100c50722104005009150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 129267940 1250 129266690 129266701
    0x1090303111603060b031c05090402070314030f0403090e0601020703030503090322050a080c0a050409081b0706121401050402031f0f080114070801030b10030b13060f02070803 77
    0x841c400101404400c41c4500144400c085020310365140c0030314420840418205181001c16181a1900c20382e070f40041c0717250441e500c004c0d0308a000c1710005071060b18091b866040d141400c3e0788002017207000580000700001000209550740d000c26100710300c242c88400445817104040e01e180d0800b1901c45002d07a00040c024004a030041c400385503c081c54130112807a2807200000030911076442c1c05045000c410f40c500034000e41c03400000c902c018100403001054105014400a0340c0c800103841124080e983d500e800344103105159003180c140c002d546461861548111a800e5582d8405104140014041d6401300002c60458000c003040c00c95100c0300b000c51030342400c1c1044020b5001030b211101004003540b0f03e10a10144d140e00000810500c002131941c607160507281403e6980340d0b0b2680940e900c3c05002c004225410408090543e9081140b4a0301540c2c0d03100071000c03615403500042c00860401c0f04002d040c18800054650044c8282c000740000c442021811050b406040001007000c40d007440042c2 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 129269190 1250 129267940 129267947
    0x80609040c05030a0f0204060b071a1b0a020708011b020303150a0f03050115170703081c020301081b01020d0e130935041404050402011709030c06100501090303 70
    0x40e0064019801148031664400009207084030a034401c564000c070800707000c3c0c25407815200311001401c10f600d58501d448010766908203035114030103840340540352840104424284282600b01c548552000080d6200000103000c3d588030914401d02c0110360800f5003000c2201449a803000d510301050700218110b445018989850910040c5600c1d0041800d06000610201000c001002503003c1e0b800011240c01c4240360380c0440e01d0307a4004440709022075000c2d0203116000030740801241d40000b0041d03210303d0610030325800c0c00d1000c0480d035501130011002013000500841c0d42c0600402102e254000390103076200598855018246400200c0c0009440c2e001c1418815140c03000e880720428001080b0146075075200d10700301d21140341d031400d903024501140c078008440502403420203510740260401d450404109150564034400b24001c0b034950b804202164007602d6010300c1600000743c1903941c0d140602d08240c1e0386c1c1050a82da000341c411080400d890712400da9600040d02c0f01a03441072281425500d095 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 129270440 1250 129269190 129269209
    0x10180f020f09010f030b0a050402010c0b09070506030103060509010b040c050301170a050a0303050603070f0e160e030703080306030c06031e090307080307020c0114090d020f040e0303010e04021903030806 89
    0x2039030812265001c205a50741c403440301501070240700902d40400ba04600702445480c10082c40000b510349402c0501016070703084a1260000b40d03000004140f02d6070344400641c1007205541c46660803410100002c0200125a04910b200700b11500003007040d001004100001d40d446000107102060b402c20040c032803409900f01ea0440100c5a03011544410fa082c0c0c0d0b410f00d081c410071000e50010341e4500c02c0c00000e1a050048400a015641d2402201410030345a010000800740000c00070040d0000c40e113600502424a5000500008003a540e650355203080030002ca600480b00070380f10f8056440c02e150213141090030745e80a00c240d047d51030720404403900007603040c1c0c0f4040d14420581c4010320a40c4000b0b60040700440c0b06401c25809808011101c04c00034091910003119400c0c24401403240020741e44800c284032603016011030300341c4488240d010124004040c008105285070000000201d0000c1c49241014043c501c02e8a00700c0320b2a50341c1410300c0303040450f400000c000403851004074800d840c088014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 129271690 1250 129270440 129270443
    0x11e0c030b03061003050c060415030203070c050a03020d0306050117160e030a03030b0906010f0e040f0b0a0920040602100207050319020d090801110403080d0e12040810180f 76
    0x340403605100020301d4008101c80003c0130300702c49441401007180074006404ca5020a0320031a06050401020500448051440804056002c000518214450304501c421240c101e0140d0310710030998280291500b500007070308804079041035000600c551140b10701c00140d02e1080b10b54030041c0c8548142c0c241780c800c1300070820208010500c42e50702a5809008144005100e80c030000b500c130b04400c007805401e6400403d0306043c0700c400c0041c00d441d2500490410300e941421200018648513828020300103040c0c0340401c0340c21010b40000841d20004a501605684480c0d00310121b9500e4900109501c501c101c0c050340b801070300040150246029660040c0c200070388620152420030140d2a03c208c103954401c0c900b040180d114280d416003054000140d00041c010f1500203000391896103113021501d01c12484002c111341c80008204004202650056400c030a4840c00c0c0c3d00303000030080c0d11181a82180c0504a19401207200c035508682c1c8a10500280140c2e00640c5090910961280005030000703400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 129272940 1250 129271690 129271697
    0x20f16211109010b030403080601020c060d0c0c060e0d03060b0a020d050304080d020a0c1b080d12020409150302100e01022e1b0e0915040c0519020102180102011e0c 72
    0x40c100740595a031510749001c2c20042624584078609803d00400349480680a81c3c1550400906d000051700c840c0111030500220210200780303842c0d0b842003100c090843d46070142c45075151041180c0c44482c045000040c041c680d44c0c09215242d207500c180022441141000f40140c4d10000c03040032818051409964414015010301c1e04111186025109982c440c11b07282c80080c0d4400b8103041000003980c0c2030003411b005c1c00c5000c1c3e1320500340b40483c0c0c3d440c12034440440911400b112554400e007035580407a405010342283c14081c03030380c0844441c0d0310f0100d00c0c0401c03440351480042803014580300d03160040a11505900601401c961784221920901c0f1042e044104820108003151030034a003030150071900c2c13074203080455860300540c1008244c40281202144101450f00034050760f455214101c1072224011075000070300d5040c0c82c0c000c1d5031521130b4042444080d80d080d0043c0001c15019805400b902500c04d02d03565a05580000481c2201c08400d040448a20001511144450356501c8150302071018103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 129274190 1250 129272940 129272963
    0xc07061107080705070501031812051c14090609030f0d05060402190207030308060d0c1406040305120405130e060a090624090b0103060e04080a02070506030106020f1621 74
    0x4460b01e01542c420351007a43c1c0b540c4480b00802003964036114102c0030f0700c1d05104507034036252155201400c1c1b2134050803000400c840415076401c1d201c618500b00d80d04d030429040405c0300d1070492441c2c01c07004004a0721000d0502034000040d0510402004a407603c45805507040c2c81c060408208074010a0040c7c452070f0032950078042001c494601c0d40a15844051903001826007038554500100340728402004d80b40a0b032006020240080c0060440009950004d66800e072040f03160b10108846004503840508180329181007018007020708001401039810545011886269480c040000d5607040c000e040041c2d48039100003624140181d0184a48070b2107000003248020b0008441c0003122900e031070301190125030034010030042180f4072401046403400e08050040c1d61421070107090b020700051014018490004500e40e07524820302c0007001401c001450140c9a50311810003d540e03040ba4044003200c2c0c030075540d400f83c1ca5641851000700700c40304400050810490340201da82050000e0f01c040303d0703150294 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 129275440 1250 129274190 129274193
    0x5030d0e0c1201020c0316080c1f0b01030c1d0a0b0a090801061d070c1707030503060f0904020a06120209060301060e180f040803060105071502030108150c07061107 72
    0x6006002400140310300400c01800ea040c2085042c1402e6501425140e20401c0307900c0c507070100441074070340141d1410070641c1005854107050206205da1100c01c2c0c020f0140d254003c40801d620013100c0c0624120038410404000406d00540458090001d240e000c41c12941e108a840408101e0820784510080c0c021600c4664070300c07070f081280d0458000381021408103281800200c41c2442141c1c007d08100490f9140d104010301c22042c3c0c0f000151080042001056100c03040c08503192050380450000340c0e040356075440e40c0c10000d1103a0019104144070340742c00c200d044018540600060b00594000b448003415525000c010307503016002c020307d00030064003808210340ca642da08000e10b0082c00301c5c0c0c643d04001351601042259010005142c59070010f20041400449044030100c540d0140e441181c2643d20340f100b10051b07403540100d40b001400851200c0880045000315000366040300d0084044501c0f4980c0e0100c0070400502c1100c4a04810301c080c8451404210707940c0144414a0606040e6890010203 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 129276690 1250 129275440 129275467
    0x3060609010c0b0f0108121206122103060405011203020705060306190e180d080712020903190605060109050306060f150403061b030513030309060b1315050d0c0e040503 74
    0x1c0301d80b030070303400b0400c0010400c1c01e03000d00c01d0b14a4072209190342823400710403400c621040310300036001a020344880c00c007050441508102596641c03101c00c0b034002d8402c0490030420319a034001c80e0a540a41d00b42000080c800c04c60104203070400b40d140d009851498181401c1c440c240c1c00051000e0b40c42202c807080d031034000480302c1d41311000d00300c0754040780414030704240c2103211035043e01c00080d4190b110358900d884050384400307070387d803c0403891038510142d6840c000c0f52806805071145641c9d2500440b41c1e07211fa07405044c104107203a1442880188026036842c001550815510700c5004d41580259000070807a00d0b104d00c1a81c051a00101070a50f00d004216034000c441e04950022542c07e43d8a150b01941031840c000e40110700311003441c05022615180345803440070880310344028103040c0c54083e40d100308034a03034100320751249016018520006002411401504e01100d8105040703082c0b000c0414141003680607118030300e402c0540ca501b42d5151010700042180010802d558a01050052000100d107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 129277940 1250 129276690 129276713
    0x712051009081902012003010e010b0a2c1906090501030506060c2a031b120c1201060306050a11070206030a020403150902011115150619021612050303060609010c 71
    0x312980002106d10500010115032400030351000750842060004200100303c1c00040e03810350349011041c1e81c59480c2200b05558800340c0c41d01d0b00301ca840351403040404042c0d000d031101c00c0c5014111406401140a01c112100c11200b40c000c010018031030780d07414005940281c00454004070f002e0720b040d19000d80c0700c40da11700b80322441c6c4c2529000c20403010480541c0300180114907a41d03104401034101340c404c2e02c1d451480c02c65001c010340d0054040c070512002a81003448440e80f018009043d1620712901c1c4c595150007030503507010882d4958a4500400c150007007074403c03c26840981040d01d4a442d0058081100c103410003041c3c0c402641d02008080300082d0b105c62a00030004a50401140061884c4000b5166454507107441880d03510a60746146c0800407501c0c0e481e0050324040f04202c0741c800c4c81c00071940510980080d96102524800459801580020038510324031822109100440c0c54017040b4400464400c00034050754801e202144807032403c680281700002e41414046030102c06a81d41618402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 129279190 1250 129277940 129277987
    0x5060c06010e09030a0e090702030910050c01060f0b040308070519060204030204050105090f0406022203050607111c050a2d08070c0c03060504110312090102071205100908 75
    0x300020010004840940000d41d0080007002c0079500301180101c0050000750007081c100e00c10141a4082010356001384225040c080d0090414a041c084402c07000c0d100350300a00c03050783d407507103402000582400740b404d4a4043d02c0303082803654505480c42e02c4d600d074183c010540a9602d0302484401d003600705035038849048a43d206010140e1214590300420086444c1648010300900031803080196201611b9400c45d4400e50100d00140c5405400110072110300d041c500500c550707415800c0c040240800082d000384a034403180e8a42a0224000704290344550443c0307a00c550f64403010000940c03060148000c1c003070031841440c00308000160040000b52502010071075100e00d4000407588010f650b40203000d564001003905109510a03480c0e545c00060101c01d04c005468541e5600200d01007149541010a21510040840300b020503018002155980404032460140c45221400101c01c4505e200048038590040b02030040d001b6960035140280040550440b00700d0020080003105036030720400c000501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 129280440 1250 129279190 129279193
    0x8030a0801050f01030501050121180624030201090b03190603031d0f0105090d0f0204050405061008070b041503060b0a050405011704020d020636101d0d020a05060c 72
    0x55250509101021103d40c54090425042000601c40e41c0d0300a04582881580e0011200855400f0410344009000384103204e00b41741755a006c1142031201c0380d00004140c882a00260042825200c035418604186105c02404100030040c10450305040601541e0702c0171100d903402c109194411051003c443c2181c000310301050850f4140a0311000c0703841030000059080e964503a00c0700080001030014054002828414248085564200070030103903070604881e0702030818055403c140c9441515004211013009298185260002c0c001c030740016204119080d51400c50300d03160808281d950b600e070283d41c5030010f00d615000c00081080d00500100b950010990311603440c2c40c203202c0010844a6078103407044a0010b4101407101503942c7c102040c41c0c032941180c042d540c5e001070b0365240d07080d9a1000103000c040d00b00300c03038148540000d124501c42d10740c201b282c071054483c14000e42501d081115a110601410010702c40d5070380e9040030300024008a0008001006207640c40e000108207900c210820b04c03c5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 129281690 1250 129280440 129280457
    0xb04060f060308031f06080109021c090f020319080304120e150409060504020c072d120b0c070507050121020309010e01060f06080406150b280201060e010b0904020408030a 75
    0x40707410000c10301104c1400d0009190001b0328020740104016418022607120603030011701c2909204c10ba100686500e031841d03d0502180186080100107080c041506a01a00549101d03034103c070075075601d0500301a40580102e055460302c0e11003992210761440c400050003640400c100e0566515191a00300800340d44101d13940d40e0a1100d420709642c816485180200d0050100010084020507190255100d00340f080e071000b003640c1b00200c2100c1d900c003190758520310001c5001c20450b00e400040d0b02058040c005e170f02c0803900c881004003494451031001620b50b4100b080c1c28013241d0321030070380c0742c103040d01443d040110300300302035a0402260f10640700c00450343c6d036a5209a41018086c0241c0000303000d60090703039001c2c074a4000040e110180042009102556580c0b102515503280100c0d4400b51140541403a2244400b4034410044054200d803020044060390705460002e105020f00c0b001d41d0040426409070340d103000a2448182c10840200d42d001e5001c1c00046249c0008001505c240382d02543c40700302 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 129282940 1250 129281690 129281701
    0x203100b10170412021606050a0207151d12031c0b0108060603010e1f030303200405060406030e010212130b0603010c0f1206030519020f03060103020d0b04060f06030803 74
    0x340c107a0116904144030000340885840c425491445900a8208074100205041c3c0d01c0300300e0401031101400007055200103030108406602c000640341265550f0200c680c3c2c240c8405640c0e0b09c540c06420840300013104243e070b030007449400c2080c082201c84080c0c00640c2d0b804034841500c0c25170b0000c9010800c40c1a41030321401310507906000302044000c007800c2c07104207810300d0b002248851105008840240129601007952a1055054096051440082185055160f1400401900b12035a200000d13001820845001d0701542084030100e9074014680c510307091a00700140c001c0c001c0ca11105900f55400d00601c0307100c058840401b071203603403503913400c808208180c5894118004054480740c041c0c0e1510801112040c1c02078030100c800709a90030841c003a00c01a00005c4003900d02500010480c3c0115110100500c1c3c5000c01669800d10849907003c03055480001d050b1342d50360910000c0c1d84214490200c0700800d0700380a006030001c0c0200c0001c5000210074289074240c0b252540b0464226000004100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 129284190 1250 129282940 129282949
    0xc2907110a0b03010927050a0f0c12060204080c09190c05160c05011101020306030a0b25120b0f09060405060d0b01060203030717060a170a050f060105010201060b0a020d0507020406030203100b 84
    0x340d811901d00c01500c901c2051f46507182e0703d41c1c10100041c501c188410b0b00005101146080e44003c00061040001080e16850080081e40040c410a030042c499880740c0c003440c2c500007607814402d80b5109104038a40ea0104d0100f405011f824400d0410b03c1020044045140d0405850748507440c0034010003600285400001030a220001c015400c042c0d105009201040ea40841c4010000390082c840c04440e4881c1c02005081e1501e4406800c100d401490f48130640c103400c20445d007122802001d08001d0604070400340480e240300302d40850f91002111001854518040d031041d60041c50280c02034118208584c0d840c044c030b030000e80260300035a002008000c4925132101c01034201c800c0700001040a41400004141622040d001c0c0d1035514601e0301110310305410070024502c1e0550010225005407003d0701929032520130030301815005500f054008120107820104a03103036170f01984d00803c0c240c84510000c032940c0d04140c02c1282c2c402c0d220480000580e900704000c2c20f00e1100d0403000100d4416610400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 129285440 1250 129284190 129284231
    0x2190e06030114091b030a05011a04061e0302160c0806010504110a030e0f1e060105101704110901090209120d05160501020706090c2907110a0b030109 66
    0x944a05000c0005215a001403c204aa00f00c01540d00da11151205070206402407403185815a1442d00802084040e1f80c0a0b040f00d4102e0301040013444503640310f81d0391121a4402c034010782000c07441d06440039103000030038455460000b01d10b14006080400480c44400c1900040c0f00545081c5100801444415010701085004110889040241451404106821b8004d80240c0e209140d95040601c00341541402028807044c3d03094180c442c4801441d800305448809031081100c2ca2068000126050074017035144601a0003c2c2c840c020400941c00810b240710000030021220038001030070000090700c0d40c9481038041d00a1380005a201e5003003409110100442c3c07103962a580d80901c140e104410740040803264410030340380c543d0f0032000550038803e01a11544d4030081c0510300d091051002d00c240d000e00318040c0c0c1c418070401004036810f40c03002c01d41600d0030041980c1c60700c41001280c00043c501ca00c0c1500c0d0305005403180c55516a41c1c03940080a030000d1384038422180e12242038244c20035400006 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 129286690 1250 129285440 129285467
    0x3240506040204030f0312060506031f0902030c090d170f0a020f0106050109060c021810080f01020909070e010309050f011a19060c0507030c03121101140a1d010219 72
    0x441c03c141c41c50300d42e114500b00c10f000160074809025504809901d50740c0015000c1d00000e401560303213003484020305d221b69800b0401e01b81140c280480c04961944540212406a40b41044090a140c2d181c0100b2032048140b4000b140c0903e05c40400c5640c1d820350300c0181140e18041007005817a03001c4070b0406424000f4660410300e0720391401005114903a0030001c02400c0e2001c51030708014001c01803000c6120385421751b282145a010440c2000703039851032041048240e403c12400d07265280403d004042c240e000d110709140c4e10000380d500044440344102403000841317005160128211744240c880c1810580d850404c071126944484030346205204880c95900c0000c402e4034030034854070400d0b40d4401e240b11240184000c000707008503003c05001007041844040c642080c1c4848503a50350b0718100c6d500c0500b51410002048060740c0d4941002d00c1072050b4103030f6400800e60100540e99141050f4010410300d211900001c030a4404582c03e000c0910142c550219445080d188100035241c000d000710003103004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 129287940 1250 129286690 129286699
    0x50904020f28090b1002070e09030c030c06100f12060513020d05060f070c05030301090c0207081209090c0703020c0f0a1205030d050c090a0b0d0603080a1d012a0c03240506 75
    0x10f000c00d617580d0008018080324030704c518a1800351610105942140300d80f000669141c840410f1039500c1d240041a080c1c0104c030880d240320441e0b0f5541c5c400c10b11000452203480502c0c0207445c08900424280c3e08001d40c00000b10303100d401c03206680d5000031480760024400790341a070f01ca002003001c2083d5001c4a981c000754281460034004206030b540903942c1c4014080c0a5000342c072080340025007402001094054520102500c503000c0350f900079480541c0180000c0c0388200f44080c00304a003084800202c8030b0b1560194041d20440107a0418080030840c0c400c410b50304240c800600040d00e28012000c911101d00c03d9029599a2070b0400b240000c1d41c4025009215800c02003003603480540d50204040100c0d8051940613840d0315440040a00074941540301600d280307400522800150307400005000c2940070904d00944400800004491005048016548020a01c0c085041c0c5e205074095640344a8030070000c3d030351031b40c1e241d0703a42022011a030304a18018440c640008000500d040c003440ba8825002e84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 129289190 1250 129287940 129287959
    0x904110f031209011103070203060106110625051309020309030408011a0d03120207170408190b07120609060b0c07090507050a030c120501170c01050301050904020f28090b 75
    0x3a200c542ca2084005440c103004030130719408441e680610590341c60b1600102036828075139503904060061030800e42e003100e46004050008140c00218080c0340c410b011104104ca00400e21a1001d4400368000c120141c0c441201c5100065100c2d0701d80001c44c03060211704080d6072140d1401d02c1d05c80c02e42320080d42a0509038561500800d46403181c944110b0340607054030b4505c00343c94030841004024800ca030340192421608080d07803519104c0c410020012070700c5060880d10940700c0b001a603d48052400b00041c10421002c0103e0900c51280b4002c1a480080781c800280084c5e8400440301104d90f10382c407005990f000490340303131a000e400340802d00c0281600d032002c0c801c030304d0040070080c11071041818035001d041d03944026060940c803503d2042607501500102300025612102200481500c86051a0880c4107050455505502c11002d8070b048680107020540035440799420032500000c40c03503206400880000048a46800381c424424850201d00f00301c1d5640340c200111801a03442000090b805040d010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 129290440 1250 129289190 129289213
    0x8030d0606030905031e0c16030311030a0e10050c010905010914030f04090207060f050f0405100204180b03010e030307181202060a0c05011b021f060b270904110f03 72
    0xc0100c6540600050301c114000c041c0e4407207519a4003400400c41c44a114202c0089480008da680c02c0095a00945600984111503001030359240f1032030a070303d000510000c88442030740c03d00c608180c802c540582400c1c0c0c10061820107545c215003d012068559a440715101000e0085010420b6528a095005145403180c00c82c240c02f103074402ca2103a00d80e032585c00034107602801030641c0300403091040b007a4140214140b4151034052280152025100c5004941040075112158400c6608403107a0180da800c6801840e561000101181c4405540654071902c00f001c1e0120148000e5100c1d8610783c4841c000380c1e002c8951303034024107501d0300b00c1003101301e0400c1c500300980e85180c20f85100007110314100c1f10444140c0b401c1409001d20004c1207902e10468800c424045402094000c82d1580160101d10102c52585c01c902c00d680561085071460581003121110080144c4c198440b90644103029650300501d007008680a268200c82c15113015801c1400c1c1c0a8501d4683c203101304484045000340b2001284 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 129291690 1250 129290440 129290443
    0x9060624020a11040f0f0203060102010c0509030a02150c0106080d020c040504020108060609190b090301050f040f080703030e0703081c0b06040b0c0a0203060a0203060306090a0b010317090a08030d0606030905 91
    0x8030300000d461544002c0109040b130f0b649402401c2280e50081082c084600340c0c5030004040d41050340d0701805942001c1502400390b10400c140d580059004006016104a0350240a4031248002040402240030400d01c070310030b6000d0090740300504060004010251143c07500a0030600700c0d10440c0c0c4114209424800981c3c7d0118103581c206c80201d0304c0c41d03074403081c40d030004000709000c4800112841201c14006a41307444032001e001000c206500a10480c3daa0f014200301c940340c21038008203442001c5840401041c05030001c3c0002c1d9102c1c1c00c0001d00c00e01c80c9080f0703526080d0141e01c111030040c400030b07050f40da2441501c03601c040358624807400d0100b0030222001071200e0055006a00300c07881c3c0030880241d078031801c0041045180d00541564404e0600c2000f04019510444205010348560f1021942d1490009014198146c1182d0400650b90841e41e1707507003503024601c02c1441040d20a10030031980740d55402e000c0c2c2c000c010110045039640526075882081d0380b881e50214091514140038180801c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 129292940 1250 129291690 129291703
    0x70f0605120a05070e0a0801060f05090c0a0e0105130b0301030201030e0316081c230603190602090f0909010603051c05040e04030309080c03120f090a0f020f040906062402 75
    0xb03040d80201d020b6440071022100b098221035600d0b480308012a00051500040d4400c0043c1c54103c0703120b150741c41d02c490510003a004240d0b012110804208040c804d5140b098500391490101458640c0c0303000344001c001402e41495401c84021240d0002c010411980c05220383ca0008040c0e4000e1410310b802c81c00c0c58400755003003820240680070700141d40c96442000051401c84443c2d42a0b08000e803441221680c400c0954115810100307240460201d0071034503000540441d0500d000c00e4041c220021507848401a4000c00d040a401501d1442c81000503601c040080303110701900000040c085146040031860404500d00c022170003c600d0800c0f003c2d0b00d074040c0444e029035078200100d07007040e280c0346422801084900d80203860080e000c500702c1108000400249400419820703807a0030ba490b220070b401c410360016900c048055100710400f2001030911034003090850b0008001400c1c8040c05804101175a94100e030495511381e5030107003800380c0d80d07514003280e030301041402d0b40d006e42841607400032f5520740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 129294190 1250 129292940 129292951
    0x70201053108130902030105040605040b03071e0504060608091c0c080c10060b120c0a0804110a090c021e0304080601230414240307120f080705070f060512 68
    0x7403400d058205101000c0c003155001c00303a2082c8001c60700c0d40d07481400001d410038003510f8496420f01000203064074040c05000c0c904500240a44485850608000b5a06005452030503419641d81400596959240310748401400c403a201c914042c1b0309104080d081000b0104a8103102c00743d0b401680703489500c00c02018440d6400a1b01d1540d6160008825140a03802294102554185600030409080a201a01d1032540000c951141515010b800c1e80c140d014941d8a20009803401c800039010030a042141003000201400c0f0f010610744901c45182640c5003d1480809640314000410f904403160700c0e00121180c407031010310304160400340c0c45519030030107100790300c0c104000740482c0036104041c42d00d02c100c0107030040040041d0a2200c9d100074648404440014044005074001380c4441100c0402201042005010784401030030803401030000c1c3d0705080203403030f14801000c1100001d07114600504409004d280140944c0d490036401000c84e0000741c020504015080c8000010106003018054001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 129295440 1250 129294190 129294271
    0x112060303051b0703050601080c0907030608031602040213030303020c28110a150c032a06020f120c0c120a0203090f01050903010504121e0905100e1807020105 70
    0x900c50b6000c0c0e5480c4c41056003000d0041d0055200005d1101c1000403401c420300740540e41070f03000740d540500c1981212994800c84480c2e4000f0072042140c1c004c1c0c10340d40c078100c600c01000141040c10f80c4020018240003500103c0100364005002c55036a0030401030003802c0001d09020340000302d088403043c11810130328000142484210661000c03150703122003103c03005e000310800107418038042e43d600400c9610480740c1913003c643c0424400b10520324880c007100b000c1c07030381580c01c9101d800e00d996150020f500035102d112001c041800b50190540100001038018442070190940318540342d204541003181141e40140f08420402800d00000d40120a07a809688122020891480703100016036080c403170f1041c2243d05510384002c00c41080342c03500c00b12010b86050355600040480f0844450b0703100403500c0b0b110b000702e004040c00300000d2501201400240441b403034403c03010303103c842c0856a85c900301860440f0100d1100304120501b6424801d45a0241c0e04103008001ca04080c48841798094141d400c04080 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 129296690 1250 129295440 129295477
    0x60702090c070803090309010305060411190e0a0621051311300105150a1802041a03010303030b06070c06080601030b100c020a0f0e0105010810080a0b0402011206030305 74
    0x31003511505039540b1581103410703aa5a03160100d03a041c1c40394800064280071914100119000b0b04207842519400804049602e00c5c2c21131480c6074041c088070000c140320400203100040d40780e9842d1840028010100d64a030b081a00d034041d00d500c003c50280c2c00101c500c2516141c10070104101603500461560380182c00014a80c1000010801504007203d004102c0500703071b00c4104d0791156080307610740648250300c0200642d0f01d4002c40c609203c421103211641c0410543c5043c007503403081034a41e21810341c105400602d82a41e92105c0380003a1105101c0c6044d00170044010010b040c2c240c0502d24400104482d101e20300b144035910602d45905600944081004090019400f80d0290b03000403901400100060341000f44240014107154a40310220301840407840002040d100400c2800e09540d02c40750661200d80c24400115500c1c030005003110201c6403140000240300d0800d015000340d05004190b4070089140500016140541a00c03030b00c030700903203050000c0002c0b0340c4c0401625050709400401120 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 129297940 1250 129296690 129296701
    0xf0c01140c070618051e1f0e040c09030203060a021909030305040905041a01080c0a092f0d0608010507030c110c010f03020717030109140f0402010f0c05010c0e030c03010b06070209 79
    0x81800041d000280c0200d6600209811042c03245811b905c0e5020032503d4034191406100104004880c0c0980b410200b82007000000700b928250b0044c51030000289002404a9901d0300024540743c81074410f01905c5a000a01c484104c40c42e0003200c0c2100d038941094101c2614680c0e00400d10701c11031103401d03c2c255440700403408012021100f64640c1040704001107003543c4841405854460350645540b00d0035484000203441203007405520b24025403a10000744414240321602c4910301244469200350808204480f0b245e14103100706c03405004010300005040c40c02c5c11024003107e0641210310184508250300c0760324208009111080a6400c0c03034080082c460a100c107038003a001d61003006004203c007125007100140190040e40c1280c5030b082c000d11007080d000700c06034902c82007035441c02e000c86c4031030f8005000740d4002e220fa010b1a603500d1400c480c0612581c0c403561308640d4003202420010b80410f801100528080211103050b68044008100700401440011524800e102c0000e002d0501140010f6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 129299190 1250 129297940 129297977
    0x6022a0a0b160912030e0907090e0402060304051f0b0f0a080307031409040c1809060503030406030b18010305010c0809010e030d11090301150e010b0f0304020409140f0c01140c0706 79
    0x20b00600500e104600c404d001441c002e00744a042c0501d290080d0185400100e40901c101000d404985454130500f60548494091044991000304160f411f80700700405100380340c2e4901445289440008030000d10258804104a20080e6001119104038034201c400c1c0074000011048030820390780b501780310025182001c07840005005a0f503059a0252a00c07540c0d0a4042d00a030905c1034681c412020a0001520703008110b0844a40e800f9840e010750080c04140500c9019903c802c074442001048981d580086454100102c0801d030800c452694643c0c1d800d4040743d4020002d5504004824001c0c04030003150456581d5038090484080203003604d4200c42c2d8500100784084891804002d4001c2c01540c40000c44444501154419441082c00c3c03007000040340809441035522804c42800c0131841c1d500c9580800002d8001240c041e20402d401c2c1c01918041d90040200000340421000601007000c20030700050800782081412080400b030421103c81454030105540050b214141440b10129500c4038080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 129300440 1250 129299190 129299207
    0x106080a050a2306210106030b0a0e030909070203070c12140c01080a1503080c010501210c031203020c01092307050a03080c0f0f0c040c0c050d050d020706022a0a0b16 73
    0x1050041c1d5110100c5c00c64803810b401400540b40120390350803040e260303c0300000844004081c1561540c1042c08445007501c3e1005d80150444842e01c1124180b80e00e5482e12168482d10b907000326080845c84030010100300a1080071089012524060010b8600369800070340303038110003400e085602e551400d52848034003500d2440c4002d16040640075031501413841da458000d241c01e0241031003070450900054440140c100c146040580d0054240c1545855556103c49000e10803c0345020726800340550159600c09104240319680200d28006141c1070000d0303111442c05140140c10f00641040c0414081516254031100c1107a502c060880d6403404c0a614403814107150310300a4086002d001d5454440203000280300e40c284808807803c0123802c0b04c400d81510134540c0148003c1054101c01003103c5154024405440c1440d201d01015207020100c1c3c0c0c5407801c90780040b04951089030325401d0641903016205c05031a50740702c007000a01316030f001522169038181e4024442c84215441c03904011640d841103110 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 129301690 1250 129300440 129300469
    0x3060b030a050303092d030f03060a050301020703020d09050f0306010e0408071506050f0409150906020c0f060109050105040209090a0b03150c0a033e120106080a050a2306 75
    0x183ea4403400c24500706602d4000c40d8200b862100f041c41441d08a41e21000001310401d00f084008514041c0c8a041c07c1140e508002c03d240d91102c1f00c403a001403d601d0a0004004c0c2d5480383d40a070805005a140c09400303111250003060245802440400301c6840c0000d41c2411740392114007050082e90395251451041c400d141c802880c4035503410803140486040c0c1c000d00140e0300c080319002a4002060300384011a41d8400010f4640070701c3c03441624a00702c603a0301000c4401d015010142c503240b030241d4413070728245000200e011940e102c000100500101d601c242400f50000322803c1d4540201ca4000038841e080103802515466075070744804441e5030f410040e0201040700c903c0c2d042028a41100c1e0701e51160851942000802d040030080140c07030300c9040c003d50403084880407080c2520707050002e50500c0340c40c01c4003590707031000204500b0183c802e501c89104d00038180760307981c5440d07480c01407220020345a001d40300e0b1801508117a040003001101800408030965403602e0300c0d105580e4800010303140182c0160 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 129302940 1250 129301690 129301693
    0x1303200607080304030e0301230702100606020f010e070b0703181a0d05070201090b13080f0f030403140406020c01050913050408091903020a050603040c0f12020a14010903060b030a05 80
    0x1200300400103414050f510481c0a52640412801d100081c14282d074841a139020704d1841010000300742080aa51158104003144100d030109042015880c0c02c4035100d80022000d680f2001e541403d0308002d000b52455902882c000d40380a038904000c0c0d04850192090040912403030003014002d83d4428000c0d100141040301c00402052851186c080a03640900e11241e10303142404000303a036040c014000c401046502c8092100385681e001c15030325074007102c0349080fa04024208608498101280040e080ea501c442c44103940c0d1741054500689160661b03d84c1c1185240d06010800619402003035250704500c082c02c00300c1e603540800d0006400340300d14946030081649000140403e000901d0050300f20080c1c10350310710090420b40c10340c1c03c04440907440001d5010217800740c00d104c241401340103190010300c0b8000880015803200910000d44032039401484034814100e403542d043d4070f0b200388000c0041c1500350b41040125101d800091014103603000103001c140e00d076402c03140e0b02e8a04004481d9401d42140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 129304190 1250 129302940 129302947
    0x15060c05100b1f031a09190e0307060e0d0905030714090c090907020106060306080c03060c0a0201090b041407150f0c02190b09040b040605031f06120302010f0501080313032006 77
    0x280042182d4a20004d240c202142da40b07a01e03042a42c034087c090707001c140361203a040200030500400307080440c2002c2c040d030106000440004401d40148102504040003401c140d09150740000c10300d0206900042c401d50113400301b00128000900010030140c402e5440c08003654903811000c80d0340c4140221950040040300c01c00c8403032603040d80460240e45103940e084c06002d03031750a0b000745d07600740840a00c2e9160f0010400b08519600707a40c010b0801501900011601e88000d440d942d03c8200100c130262083e00904401280a031014410304010b00072030355900c441d1861000c0014a10007250700520103000d0405000d40555880c405081400d030075054000c00c20036240c3c02c3c0c5085a400c6064198003071414102c103840c241c40d0500410b81620320245c010080001d510125010030b51809082c84000c6990b1a0f02280c0c110038682c003035500500a40022512192040e00c2200326401640190104d4009001d80e500a211403074800c0b049a0f000819809002c8484801d00041d00000500b1a8000b0001 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 129305440 1250 129304190 129304249
    0x3040b040b130501030605060d09060e0f0601060305090703030f0c060608191b290408030406080411030d05090618040612020a060503040f120c050f0115060c05100b 72
    0x19000b8607401140501d00c642950759100158180c070100c3c001e0315880300c0c00740940c880396081c3d94070010100703000c1c400c007041420401466134100056411001d042d5004100180407154050142541144103040113024482c5542c500504c10f4000c07441c41010440010108804e2009039081540038004000941703d007030010a8883e00181c0c0c0200044440740e8500c3d41c0c41c01014100d500b8942141c4a582103540c4100d0080044500806180c2501d40c230900280408103540104002400150500d5100c100d81418281842038a02d42501c4445200740e0090b03072103e4031541d11005644091a050303400d5900c0760840844220170810b1003003400e81080c5000c80c0019101c20f1080e0340d000007030080d10f8010310141c542d0005c880a02c01110041c01c21808855104001102000c2c80e506d0b00740146008900362207203a0715142401045140015107a448840d8880d001410305a0840180340c141003085440d08140d8590361030f80e0181390b0054015a17201d0f5a03080a4540840e44030000e40e0020f8071034802c2403103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 129306690 1250 129305440 129305459
    0x306090706090803040f052103030f010e06042d020903011b08070f050415050405030105151003020405010e0409061d150703020f09040c031e020306090603010902012003040b04 77
    0x20744100c0380000c21600000503114004812901a1807205a501c8416414001440210500710010000305c01c801803c002040d1000e10241d4000c5403c0c1300042c445503d095100145203402500e20b0744034502e03041d4101e009520030703205881559440d145588a1000315800d01000317024080c4915019401e115040d078100b107160180072010151902c1f03030500d40d140c642d0116901301900200c500810000c000038060001410381450390046685402894a0303240c4001c01e007542c10680f44880c2046044802e92030a1521500036104140350f480c0450815181200007000700c03903010f0381280115a503411070700c188503946d007007059804c040f100700e2a08852101d1105079100344c0f00542d11400d001060206002521a008469a0124182c0d070f6604040071304007040b0091041688100526544006200f1100c90146442004203a400f0006840b440c0c0703030090159000e002005a0700c0307039142100c5100140c2e0092070404036440e00c3c0800c0542e500306e010005266110304d42105200d10004580016000b50703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 129307940 1250 129306690 129306703
    0xc010204081c0228020303130e100618031b030602030403080702060f06060306010f020f010c0f0201060e07090b0a030b0613090b010f02070902090316030c080d091a030c09030609 78
    0x5600e90303074400b0000c281040f40c8440c0c40c001c40c0010503141c0d0042d00c04100301c10385030030100c500040a1301d00e09181c040c4407070702c0e2020951018040860080411101d8214010031000078100303030400216540352980040c80000c21070000078007880e003241d48a46d540710003483d080065503008804550340d0a050a000d0038002c1c0c1240c00c0340c014440d140c0040c14402681c0300c40c900850000d4803030360031a1600317001036071080302d010b1903141141b141045a02d0120030034055000401d8884d25102c440c404042002405c0d19104e07005480100884010710130f02651198603501140d100010480d1904078a41040303020b0310511150340c0d8049404503c0014605681529204440b40c40400f0410344420000549400c1d0301d400001c40580c202000c100300070400c40d0020300803002c0040941da40814154204920710800c0c1d0400ea905000c0c84030140461030040207061800800b40c2030442080e403070041215803c017144041c0c55283c038000710105444038601000d940c3c1c221001400d54000386414417009540c1c4030b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 129309190 1250 129307940 129307963
    0x50111010e0f03091c0201090506070303020702211605100c030908010609060f090c020a02011818050f01050603011208090a0e0f0a110c0723030d020c0102011b021c03020c01020408 79
    0x71480c1145d90102103507807201174641c1a15101400d0307140c10104040fa42042005805042c0c0070460b284c01642c60040401c040c8a44820a21900409084591030f00030b0045840d840d04c044443c0a00082d5604c82c2c6e1200d41305154540403140070070a140c2103509940f581e00c03443c801e40c28481c0101d008032054010720103591031080d460094a80d90315000003540c0d414442c131805608002116405944140d0512950701503860850307408580c0c400c40140740240180068a20340e90310703c02c3c8005114205509401004229003c1e070841d41421410000c0c0c01c0c052400030410703500050400c030140ca40c1c501800040000082c00380d01d80c5030419003002030050484589003407a203052030140704001d0940c01e883d10b1040f044000c00d040b82c01c0030000000203040c00400511040d0403420503956030f5041204401c1d05e50303c0d601620608400c100060f00759844006901c0c500105c01141c105119030000780741c132607240b085041c0c0d42c240401140a174020b00c18503180c0c00040d4000038011440c5580000c0840705e14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 129310440 1250 129309190 129309199
    0xc070e0106080702010c03050c09010e0f0a0305033106030c03111b01150b09130605030f0a050f0316081602041802010e06070506060607050c04020a030b010e030f07050111010e0f0309 80
    0x1d40c1c403011411942304450510700b0340014040d036019544030b400c0070500a00003a1050400346510340004042d050650302c101d641e9400040c00e040a10a140c00a64035007250190791008080c14100201e5003164030300070001050b82c1e51403503900181c8280c00c102d400d00b00000c6410b5440c0222034074030302003c04030300402d145582800c8c400d82840070402c4842044841c01114076042551040411000700c4c80654425015911510007040e030790703014482c07042c4464a8a001744517000d5203203441c1c0e007031104418881d000d5820600071810411081310900e0441503002e44c205507525681c01843e9000d201c0b165000c0d400500d024003900d5131085a5400d410024000d880303041c01d9102c2c0c00300704a0723603103d190360080c000d070003000104800d41025005001218421002d5401502e02880403500302c1c2c01455031040002c0d140d0748104000e58000d09140c10311315064029140c1d08442461043c4d072401248102c40c1003000c210300c03011086c50290f101c2c00320700980006680c801e0f80c50b90070950b566000200c095114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 129311690 1250 129310440 129310451
    0x301150e04140106020d0809030306010c020109081009151a12011b0807020c0a050a0311060418020d1116021c061109010212040e04060c051c09060b03030702150c070e010608070201 79
    0x14503016907c00c91080c840030008529507030340c4000458401c01e5413103040f4140090a0002300f4000f0040c00400001c0c43c0d4002e00055403440b0781440c041c810f40110344010b0b16880c042c82416509142090301010392811b55a180c031096107000e50310300402d02510310b070030941801880e580740a036010030f515002e0341c03041d030803117699900c508100503003494184222a403207100d030a000c00000394462841035011400070310040c1070603614001c860302c6808a9124402003940010030101d01041c5204800800501500c4c15081085081d01c00c1a0700030807820203407186104102c1000759240401220b04160303400310041c414142d01c00519241d41d00403000c81070140c040e1800c100c03403410a48007501e0465001000b060050707100e9403154402048103c0c0414100641041b416001e1507455108020610741150005021452800e2a9046420b00300c0c9491090700104610000750345c0703025015070444c0d48014004c0c3d4408064550a14248640e40942e002040800c00010352a0300142e0f02e0340700c1c072030b503400a210 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 129312940 1250 129311690 129311713
    0x40501050105011409311e0b0904020906130c0302041406030412050c0307080f03090706052b091202150705040e010b070c0b0c072301050301150e0414010602 69
    0x311240e035441104c05010301030124090900c0d04c66210724090818440612a0040d10012810520103c01003107241c1526507050410300c00c0301d115031241c00380c840c110030018035045000090640c440504040d1003060302202041e4269540542c1005001540701d0400100c5c640300c0c0d0241c0650058410252900e098482e03210003418204201c9101302c0e40401c001354254020b190590300d541006038110414070061001100080ba0f00006162400c0d4210210b501d9240c160b890074900003041c2c0100080000c20300600c0c21040500030080468015044103041c007800c4085900002c08080c9005050341ca1444048180c590b008949203441e44903103c0040c0055481e9601507030729105510619521000c40d034010880840038102030b01856101d03940c11441c15a035049141c4241c6c0260740c3c007900940184504204e10000d10440080d2414900012002160181c0010704140414440c40c941c07608070021540186100703261418038048d008004100c000a9191000d0b4480801d01803040907114031703040483d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 129314190 1250 129312940 129312947
    0xc080607031d030a05270901170c0102010605030319180b03070f18050d110d0809030f010908090103110c030d0b0103051e1b0d050a09020f0909060406180b04030804050105010501 78
    0x110b0341c2039070303480d0545000100c0b548030b90b072280d203042006c02c81751032002c80d0141595040c0e40e06000381205491410041e50078100d081c186400c0e800481d0540e85044400c0100b80c80100c155000041d044405070035005040c0d2040d100000c100310440903501d40f150300460940710081c003842c000d1440c1d5aa44035010343d900f40a40f00c1e85a6654420702c2421091780070046807814000c0001c04600c02d502c81d05c0c0f480605008504010440507040300e80c06000f2810340d081e420308104c1d043c07181418400a02075451551945082c031b10810540c130b810151181d15900b08221880100d691501541c01103940e6032810910810040006203400e0b80040d040102207281400d1a18801c1c07040015640005141e440d080800700741c40e44900b248401a0005024203940c40d1524462a031091100c86404602281e0a00c10801c22181041416104001c030300140440c1c0440014155130086d0b11442c001140102110014820701c145c082c01800c20031844100000c06500039104c0d8000e501c00da00911050b6200d20041d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 129315440 1250 129314190 129314197
    0xf0705010c11040207062405011107060c08220305010c1b11010e0f19030b0105010206010b04091518090b010e0c0d1d0d020a050d0302030c070303090c080607031d03 72
    0xa041600c0040d1000d4141c90184d00504503039104050026150300120b14106031101d06146440100c00030030b0040000f543c110800d040c00340c03880c07406015860305203003014240a800070000b03800c03054041404004200503400c03114090004520321500780380c4d02e03d040350180c205041f5590020310040d0b0070714241e03400c14449030945a070141201403444004401112000380d0280c1e810341c0404541c02210b04ea465450207030380325001d0b445025460a0560400040010044c0e00450443d409980100031180e40c1c00b0a071416544400b1010442080c103004c04030340c103041d58101d03940c42c0500b03112600b83c5000d05d5100e800302c94421a50700764640ea0703d6400c1c03040180c0460300c104081c1020810040908410307400a00c14203a404601c41d0040c6102d40d40f189804036980304070780581d0010368034030188403040110001a607080e140c00d51641c60141c03e02052070041140040c01c1c1910f0b004401e04010500119030301500320482180e107a07142120004004d414031070f158600c14407482030342c40010003020044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 129316546 1106 129315440 129315443
    0x1b09090201200606090714030106051803010e1b01030906020301080f060c13060c050328090b07020a06050702030a0602030f04060c02010b0f062a0f0705010c 69
    0x140c911102500a41852802c0203040802c5001c0011810350004040d6084106a20703546400d4648001c00d090308100c008000c400410600d0307204019103910029458841054a640000c2c1400c88050610b600c1181c0c11003240c2800105c42420a44624101803400240315034441c3c80350b00498000382c002d00d41c0303608040c1014681c8081081103540102a2074521071401c041051040d600400a01c107031001e1046030381e45031081c880103006440140e0a074088489204222031100c80150a030388690001251410300b01240c2d9112510030340d95056405480010100c1c00d0085c16111500070142c200e034144100d6446030002880c900246005212a64003455107003010300d81001607540400194045a00d4944511001d0352035a0f030040a4a9060792620380e9011060101801d030103c0e1107424070f510b10080d450851285000543e01c52500004003540c5910303840b8001158440c4207440e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 129136690 129316546 := by
  have h0 := BRFrame.cov_init 129136690
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129136690 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 129136690 ≤ n) (h2 : n < 129316546) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
