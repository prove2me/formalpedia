-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0224
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:34:04.00793+00:00
-- url     : https://prove2.me/submissions/30e13602-5d79-4506-836b-6a0ca54eec29

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 40107918 ≤ n < 40287774 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 40109168 1250 40107918 40107923
    0x190c0507030905030105010509010302061b010c0903051002130302010f030f0606120c0f020316060e06070503040312020301080c100509040f0606030b010e091f030609050c0a080318060d06050a030f 86
    0xc20405583d50304250a880d42400b0b00340d0480038050040005040420107890f2403481805d01003025640440c12a0031508407180210003d003100d0303410001d000090110460b84808040c0c1580b80203550002545c1d15a26440001c3c100030203424051f9045210360310002c5240c4101030280b0806030f407a00c00038a500889484010380e203107490607030403219000d28280c2d401002640c0241d41024000c3d810760081d01c409010982d0784a4644a01c0e0682c0703502401880e110b01c4c1d85440703e54680c101410001c040100c1607507100b819500c1000140240741c000600c081245da41110a0f0203070000c0e18100310340a001d916582c6030080e0502c59480c02460442c1c100c00141d500340d940401450480c24011246a003007440b001c1d400402c240d001c01c4071244401208200712060160326000c1356a01e940300b00803142800c00607641c0da003103041072150502d04503595400030408807004500700400740040304090071910140901c10240050101490000c9810140007404002c040103002590790600c0e0f1800101d04004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 40110418 1250 40109168 40109177
    0x80d020a0e03010203060109140a050a1d01050904030816140a030c0e060703050d09060e0d030e070e0106020303180f0a060605030c0409081803100606020d080a021908190c050703 78
    0x25a2210b04051003500c0c8101c80594411000614040c5d4250040c50600341d41500450300d66008a401c1e01d50b07112201c02441c1090a054140b000d00c2c244031102e12042c0c210074401e810780c4081c0000300ba808081580c1004d02d04500f03c04142100d10305840400010b409007a4030040403a01c0b000298043d4042484c420b02604e030341070310a20020802020340b00301c00c0c0c01030110708240080603049181ea4425481e8074850900040e8440c80400c1c1d840c0303404010b0022400094881c070300c0c0500740d0014085c0900034860340c00381c0d110550500c40e020307489020080c4075140b00603601840300920401004541d00040c00707402503507541d45240c18494003512490003810b003c4d11503003e510101d07041134819409030941250505003440702c0b5040107100380c04d00351011a8103206014808840011034880d40005100a40080c0400d0361246070240103081c3c01043c4164640c418400030014000d00c00500340364010380c0c5803070300c0d00da540c180c00c20211380841c03000c49100500d08041c122210b0b03000001040a20300a486 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 40111668 1250 40110418 40110437
    0x901090c2c0613090213050c030a0c0212090409060b0a06050a02070e090a02090702010603021503040302010515030705040c02070e070215010f0602070b070f021008061005090d0305070f080d020a 85
    0x101c4001d107000e9940682002000702d400c55910b4291303100158940c401003003160480240840f01c41500d909461310803840000006201452205108140f854450750002d041b01c070442081c0c000c40c6e03010320300c410b80c0290740f81c0b1500c1003008503aa0103031030001c0c00209400d19490f143c04006203d600045c64480241c07007190f20104840e00300c161500d10030307000da40007011141e0360780d42440000d0710b02608200942d07481b03100c0440141e44100c00c111008da001490f25442c1d04c0c1a090007070a41c4e2001d400c41d03451f100e542810f5413240e2404a945003e0f20407d46010038900c4a64034200d15140d5554008036045481409101c42c1039070210303820346003149078031240701c60384d8030b40e14410802403140c8aa0300160344141401c00c5821700c42009801c285015030388140c90255560042180c140550540f040018924000c00019240c1550403c503000c0701c1d8580603040c20a440080f9140803c00304000d010700c44c0103d641000c101008030f441404541c046860b644500b0602000c00c0650050090403004c610b2414 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 40112918 1250 40111668 40111739
    0x27020f120c010306120507030210051603050909071d040e0705150c060105090f19020408030c071e080307110d080c0604031227030905030307080403020f0301020708040e0901090c 78
    0x505d01e42c64a07000b40180c003a203881c42d170810409043c500ca0302014010240040840c0e0440d940c0d056000a00a0312a51380e1170070340c0c0c010001e14820003030640c814030180d184801c1c00958103020b141410303034085c0d0b000154401048202885c0c035619901043e88043e48000f02c0112142410150107960512000c440c26643c030341040240c86141100e64404220300c150000700c1740c0010794a02515100f400d13400520f441c2e00c540c80d040c110f0b48030b08041e40c1190f0140e0005c010f580c0400308512140d11100d000d111005043c18a41c503224800c039640905042964464815241d68401c6a0b21006174044811980c030340e4908c070801d03124201240c00b40c0200e120613400302910b44144c002d00f60451400c4d81402a5025075640c1481c42c032998100075010400555800b1442c0d45041000b400c04a000f80c560948991941c81000107080382c45046901990040c8254400100008103940c1552104032403007100307607244a4064018451950082d2024000420001f940c000080b00c05400c00c1c1c0740406800c0390070141703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 40114168 1250 40112918 40112939
    0x605030f030a050702010314010303080403020d0503070203090103090602040b0319061211010f0c02031b042306060d180b04051006060912020102100c02010606110127020f120c010306 80
    0x85614020790810403a80c00340b40d2041c8000d20351144141400100b500039407011200500382608201c012a0b09075082c00180343e010848448095914a0100d1461603c040025140e00495079280d040c5a00c401c6860b08104041d01504e0148c1404880e242e26440c4c03d40d6403810380c4c0c092000140c8010300e01440410405c006510b01c8201da82c10410b004640b034945c4004640f141c081041101c10842605814001607809114a948102814421210b0303003009508005c1124030192a05518003c40c40007244081c0b8400449507000781d00b120b80c0c94860030400040740151200114160f1841d84d0030440c030007000141c24149000c1c034007504c22255007220220b4044115001070003010040796620108022904803403244d0208140b040c41074602a8100740c8004041e82d440721500710150751191005d014240d80010a0301520440c04000c1c000452510012104440c26012074900c80c030a24920304299280c14482e10407003000a000720389603550500945844119502c043c60000742400740005008048 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 40115418 1250 40114168 40114183
    0x1506020a080909090102160302030a09050a080a03030e190503070308011d150103020f040e040b06151602012007170c090c030718060903020310020408030304061d0304060909060503 79
    0x1c0780c4024641500801003001c0300b10001d00c0c600e901e40d0204030302240c0001d0129034901683c07007600110345812020401500101031900103d00540a180080064080014200420036058100000c25031283c581a50401c0a40040740d801d8840304003500081060000003404903074020b0391102d100d41d0301e50300c1e065074078401800c0250307107501284003050880111503240300c0d00c2003050400628150280c2a40d0182c1c5d080340e4400602c500581003044140440e0846440d403003d0300320390b44010b66240703400e01c82c500d01801c9044c020b540e01e81c2c1154070031039025245882070203844030003090b80a40701d50091541c4400c0c9008800e40284141410000240000381e80200d44078002d260407160741c0d80254805032508002c00c50020030542180a4076818002152240135000310354620040a040d40185890007200045180c80030f4410002000030340400710990b500568040c0c404540e55100c90b0044c20380c04d105006031449804001000503445070031415804c1143c000c008103003c1c4a40d0b40c4101500c0c0d405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 40116668 1250 40115418 40115423
    0x140103030c03030e0316050109020a050616060c05070c0905060a0603060803070809040f0e1506060301030b0c030703060906060e03070e0105010207171009060c02011803090510050f0c011506020a 85
    0xc0e0181c0c1c00e00001e000c1c1c4c20802c4072040180171241840500d18a0200c0340c0e11504044d20940d640d00b00d06002d6040c4901194050181070b140c091410342d80c040e03c01603110341100701405650b0755003040701b401485401140c4e0000d4000303540e61500e548540c642c3c00245016a182c3e4414400101e000880c1da004e401014100c039403440207142400f40780d03141c80c085640203003001c991041d0303280d003900030304000380c17060346101d40300d4a00500c5403840e00243d13143c0f0143c0107440070b8072507002440104002450080c1046c3d0020000c4149510790301c5414050b0050011a00b000c003006082200214582e07600104a01d0260012002c032652280c0c0c0d040140c02c003180a00800f40180c00840f030901030241c0107a003401d810115481182c0050702c0504845007201c031101000c4801035164048403001030f509001d50058588828040c03801070311a44c1d0701401105a61040c14001d445081411544601034400e88541c1d024542c0b5050f80d17506890000c60080c90000d00500b400d65902002281d04c2d07200003490301c1c40c0c0b07a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 40117918 1250 40116668 40116677
    0x9060f011a090307090603020315100303111906050613021306030b060c011418030a0c020906130e0303010501022806021303080a0903020420030604051e01080a0614010303 75
    0x90a00d048120764205148a04044070010480080240c03810001c030801009407900c00550309055104160800d0104c140303184046004009001c0036509031780d014030440b0791504050850807501081c01d401d1400031000d0840051141c0d80311000d00005801c0603120340022a4410a1501a010108203e000d0042d4075400e59403d0542402454044d5003c0d940b291802021581080b60100b4514252048454460421107a810900010801200c00514849801000385051252029000b03145400910b8060311a070042e90100760113840307140c46a44084401c010501c030310f003150501c0303695031342c400c1c42403d0040c4209803030700c5050010201d0200701d50b51400c0101c0142c0c00262142ca020f5005800004228030f0704100010000e805d03a0002c20f050002034460500c4145180100821642c0c08000d40030720041101c1c41e01460b00340041146d910400499001481342c54640c40310204034400c03002e03184894134550010400260006a402280b44202c6040c044502080c2019200803028032000380803c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 40119168 1250 40117918 40117921
    0x120402030d14091c02060a02011b0504030302060609071211120a0501120b0603030f121905130204151505071103010b06030a09051002030c0405010e06030127020f07061409060f 77
    0x103140104e4042e0341030081080340210240e081e0001182c582c070042c500c0e00540e546509000540d0002c180b6040304652909002d82032500e940c0380030f0340301c401c010081889012013000003100749009850310208480d64020820400700d1b105090301c0150f1003111210704418400300040d80080c101d007d001d05a4104220a24054105541e800c02d580c002500183d07041c041445440f81030f004074400303011000c000110340c081c1d9042081c00c03038401100c404401300d5030070704003420003110100d4490380901481c0d0645000442c94182c442d40741a85605802011250106201c210103042d8007600de4540c1d21700542844480004071001c040c02c07aa020400d5681000c400c1c00054040c050f0f81d4015420310f17020b64191014000e105070074504984c01101c1c26850400041000c2c80346581c01001d54200220595115240d54102001820411011031046c02c1d1041d0b43c406120100c1e00503015601c903800d042c000243c030341c42d151034004050300604144000450305040021803005000841500035850504400401e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 40120418 1250 40119168 40119187
    0x20105010b07210c06051005120106140127030605010e090304080c09070203070b0408130608060a0504020a02070305030301030f06050c0a08180106171c081005010509010c08120402030d14 82
    0x24180451003c01031100c150f8008011a20318000d051003004440c2c00b658441d0b060004015804142400390f41e880c0c0e2500c04240441200784a4942d40f4040c00d0a203000a00c1300002940b050b4507aa0140a0f409180c0400010801010b6041075058444240304e03166036994060842c1d540340194800c04040f07902c103904e000d040e8100300c244036410034a0740c4107036854244036440b1580c9803101918212079542000440c8044150b0b1108a00c0103002585402c4240f0700b412400070301e0022890050600c035941c00101c103401c00d030080109900440e8004240c944942e960700700540b0f00041c1d004107071155800e210024502e0001e540845800550980341d002c956140c94070158082c41407149038039201c1d9600c000c0812681d8400c101800b076944039000410600b00d06500d54030300c2c0a140c004000a00080c0c106010540380d55116075001e65a00303180c5640c44e03180d0400101d07400346a1503000b901c02400010310a15540782d00c00707220f205e03600942c1126445211044220340d580402c241141c4103d00a0140401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 40121668 1250 40120418 40120463
    0x30f0a03090c03020616030201050a0b1f020304030c0603090507060302071505040606080304030602090a050d0807031107090c020109060e0304121103100203070804060501050a05010804030318050706090501020105010b07 96
    0x801c0e0144596024258890307010940075803120050303c5d80100c1001d100c8003090b509024250748191408020300c003580c1c0c01ca0100d51509207480368030048500011064220701d1003001610011600b15500e500955a00e8034017900800c607982c03055426005004001c29003500078000c65090603440400340c01d004211030401802040003030002ca80042d1280000149030707108002510295000f041d005035901d084104004903007040c0d9220500801e1803400708404100c1070000d40d4005030700340c00c3c05d1000e4004031142030f0030710255030811074009142241484565a055101c12090b40c841d440c00c00202d024400310070ba4034000e07442001090a24111084001921600640600440035003203c20850062040c04141e800481c4d0320704c0080c41400810081c800c00380911401001d040d20041c1c022810b10000810034800100040d0a040e142c00c007000030520749035591f0601d690044161819292902002041000c1d0380c801c903070056082000115142da203440840300301d035174071600010180031458000710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 40122918 1250 40121668 40121681
    0xa0b06131827170309030d06050f18070309050703031229040903020307060c0c020901060903051207020d020a03050d11061603091a1009050f090601140609030307050f0d02030f0a03 79
    0x26000443c0602e0043c02d8207140000d1401020020040c41c3c5074218040e105003285c00c40e170302c00c900c941840404c083c4103880e2052002421646155071007500c0d0b0303038070000380e020b000c1000000b4940d21079007e00001341a0300c04c0c0c4401440801a10034801801924118600c54416444030601c11040e14060b01040c0b815500841006100380103603801e200f4103446190458882c143c0c2c0c071010682400c089421498400c04003809888541084082035045498040d81c42010074041d88201c00002260ba0540d40c0c0c000c04801400c2c3d0040c45c0c801c5060710303403511030349554101e005600440c2403081303205040c100200d032840c4502c0c0310030036043c01550030000032000381115550a40312201342c030341000c10b841c4803140b006100e1140f05d0459103a640c078080400701141c80013044100303224180741c240840c460340414414112492a07a4000080603148001403662241400300b95141c4000905081001404240d09541c1d249034015152a41d00b8a002a42c90f40b151507218090540c0400101c0c031402e001e0350100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 40124168 1250 40122918 40122923
    0xc11030d0807081f150e0303070b011e08010906140703060503250509090a020f0406060c1b08030a08010806010e0103021807020a061409010b01090503070e0a0b06131827 74
    0x8001007960324001452035142d4100302c001d030202010007205146c0050504814030b009034000d40c82c0c80419203500030b19400601038080302062642903040d051030741400034405002e04c60000c22420042e440c020000b0906001044511111b00c8002402d085c041c5c4100421244003402802d0702d403142c00c452104621001d0140704106803000780114003519074080030391142c031000c8000c0101500b07070b004002d0200b165808051245d4202403083c00391591107035901d480c1c02e40c0301c1820520110091020540300c0c0751508030050703920004c00d40419203648150b60604031000e03c0c003521490303621812514001402400b0194026a800d0508844041d40110455100b50f1604c16102c164003d5541c0e4002d03a5061283c8001c40c1d41d21800388000e248003881100e0b20304600342030440141c0c7c540360110b625401144a0702c2141b001d02c00c00500c80c03181a402c00c44c44680c0c010310043e40c80300000b11608003e080c900500104840341d100040c1014501d01c260072001905821640140c4104131200700c05030000e0404 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 40125418 1250 40124168 40124191
    0xc09051903051f05010803030c090f0102070302030d0c0212030313030503041e03120b10020c010e0301020d020f030403080a1e05071e120e0a020f040506011e0c11030d080708 76
    0x10070000e000c41269400541034000003001c3e20300703141c01595010b03080007029800030401d0201041c44141103891020054520110840d200f40050742004215070000e501801ba201c00100318951243c0b40d03140d0180f08456040440c40b001424654031300048415600000711100ba41d4003290080000e954010710a4000681c0c00360810300c0d000404200d07050840109105035148060411030b0700800ca0040003d6070380c0b40902e401c02000968a28415102d981400700d5005450780f961829011141d844001a1040d50b0b503a16164420103a94400c07202640000e11400c04a62601c100f40907592030040703618210210090403540c3e220040c003001d401042800881d08058085a442c07844443c214204c41e03d480c10a00101007000381030b00e4402a50405540000c0b1000c0b006a481d00e0001801d4401034400240303a540307900c0165001210b400d251110421000c10610240d540a940500690f2080c01c1e8888101e00c0380f014191b036561414000004940c2070000100c2c0b0381c4c0310380314050b841400d0919 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 40126668 1250 40125418 40125469
    0x30405030c1002030f0a09030c1202070803030c070203070e070909051e0405010504110d0510150b070c060f140a030b0f0604030606031704030c0909050307020a091401090c0905 77
    0x1d9061801e00060055000c1940110801560840800d01e080e48110811000d102140ca00d95000301000c0441e800100000c01c0000d01c103001501c2080722070050f16560701100c0d074034103064410164640040c40102e20070700c01c000c07000c1404088101d41c10b020b00c58649800c000d45082a1001010f00001028076005588006181d40840d500c00103a9000b03a0081000084500b41130815004208134015000d0150341c1083c107040004000052005010300f20180025000c0d141048030744103020310780d0280708444004070341c41040c0142e0386603890403501543c46003a080148644d0076100744880d00100110040e013030001c603006a00a41064201c1c8a006200d115120300c5400086c1c10368105810940f1110b0b1788100030b004014120300380c80f0b80110a9080e2500b014074563700c043d007503096402580442c540f41c00b1a0400c0047c02c0042e48c21a543c0107040c6410141c0324111600240304150124864a000c14000518813001e1311903090300b1810f5580c5d11000c94180001c0c4403044144024500c41c40701e0581c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 40127918 1250 40126668 40126687
    0x50a0602070303021305061801120b0a03030f020105063a0209010f03170906030402011110020301141e0303031611030315130e06040213020c010c09080d030504050304090203040503 79
    0x10051050a10940300145c890781560391100401030703640c02030b50180100304020f01440c50701c01c9000b0250070003441c2c0701241c4520115500003500d812115280c1004134a8008000c2580081c4401c8520580c0d07802004107549071010045800340409409130000712030500c0300c40c0364035140d507514003072202d1103010080c90b09241c1c0822200da00c02d0380400c0c0e00c00d0120304144200441f40c2032040010b42400c43d9941040c0d016400141ca5110140009060011007a55184020350900c9441c69072207030f00400315120340c0c6d58107011000c44026080940310301e400c00c450360390500d0201c00700001210050f00035425071703036010303600d1600c80740c45a00601845000c0010440c0385804100441c0f00f200860481c0e0410102c1d207003802230044003481c9c000010303820014807a01e00280003c081e980a03404503a80c1000c1d05020070840000d03c01e40f10200740c25402c00900140086c0c0050f0988103c4082108a4100c2203110904901b2200c0c00d4030002c001d504100000c200030f00c055006503800902610642c0d151000c1c80 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 40129168 1250 40127918 40127921
    0x7030203090909030c0f03180405100e0c0a080c03040506010e06030a02120106060306050a080604030c1a100503070512031c0605130902040f0c0c031202040504060308040e0c0408060c07050a06 84
    0x722000303100c40d40001804481244244810241481b0000096080c0311220400c0c141107902c0c0d4a07902d00455841c40002c035111a4001c82000400c4043c0000d011410407595105c0782d680300f03e00c0140481d44200200300c0e4405580d0489110350703040000b8004d80d03403d00018003076103c8041c0a00c1e40c5031180004180150b40c94024036901055051b000085940c50240c1c082c050380d28940c4100d00c035441c00c40007042000c1d0007090300341c1c0c0103500d0b01c0d0426000300d440c03400c00c0c030694500c0b0340d90203003540050403c92000100182001958011000c8a604030350310820032000d22103628600551350014000800d45682c400356990b80d5008441d00840c0300c60b101c501250150416840c0c14000d15182d403030380d80c15814075104941110350100e0052046200c0200d0250813550115401010410000250142400740c2c0d0b0540b0080d0400400901c444e60b600c3c105140c1c2508a401840d010500d00c60104840a02c04002c54040704e2040c4090300c01036840480300c0d082500030704000e90b00350150076001e00c00202c07203 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 40130418 1250 40129168 40129171
    0x1050d1505040501150e0906060f010215060310050a021b0d0507030e150705030d0c0c02010504030b06010905040606020a021804120f111f0f0b03061315090f031805090105010302070302030909 84
    0xa1a60301c89052901003182880d049014248a00402b0f00740145006a40c2c0402c01d8101d44205000e0041c0945950011074030b007201740002c288085141c101405002080e9130010000c0d0703c4902100c412503410341104586502030480140040384082005c0710000b4084c07000200c8088000700390640700c0486c4288800b6503840300104442035003000407603298000c694800d960307110b251307880c152501ca4019400039106c1d100f28000903111000c5d1000080003607200d480c0041c05003a0190040c44078a94034000030390b541144003405c0784a0028100e030745101c40420070400e4441c98203d400001407441ea03610999848490101d07030340c00c010750728814441c0240300300700a03800c0320400300d0310240e00700d4040c8404c001c444400402c001c4c241d00f8050404030942d00024055000754095400c500b41091500d0030b1941448002c02c040c4210741811035003424440b0341a00c10202c203000e030b10748440002e00340d030702d08444c8800c03070140381d900404000040c45654426405410300320b20900499140c0300d044000601100c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 40131668 1250 40130418 40130429
    0x40f0b09090d080705030601080f060303070203070f060e060906030606070201050d0e0a030908060907060806130e0703060b18010b090a120b04051c05091c1208010e01050d150504050115 81
    0x40800b4441c03801d0f80c42082c5903409800b0340351040c00d40c100640001c0242c5000341591301c403440c4040104001742e8043c001c80d10324590040490306c1c210f039980e00002d90403080340b00c0d07a03010031001c84602400341000b004403102c200006000e02d00d5551804208001c541004c10207a0401405020700340007802035205e40403180340f908000f071498000c1460000d01d44505a044254560011411b100d400c0400040100648850341814010f95403182c0105e1403080502003884141c9040c0351a844480a000c40c050b030a490091500307000307000f4107038184800515150f00343e141c5129480300400182e506203010301582400100782e160000d07034078480d001d40008008410341c0c8844421082c402000b80030007402000000d03265501c6a03e064251000d0715a01481241c2d41c000c201c03c10982082e41480034494480580c803290050845071105030041c0304074024050442045078080022909180080d10b070200607038810304609142c1c031084144000782601070800c50b40c43d03403a0342c440d1480c25900c00b0752034090b00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 40132918 1250 40131668 40131673
    0x6030f06110f181e0105030411010509040204090f0b0303040803031609120624050d080c01020714030a020d140d0b0409080c010f06051002030708070c05030a060f1b0e040f0b0909 78
    0x2030002c0c0403c071310104d140040e0414440496200d01840c1d0b00802503a5100350444c01c5c000c502400c41d00103940c540304030600d19a02910014002c44c3c82c031000c2d4407074400944c0000c01003182d00241c10905a46c4d2046010300c42c095402400010a904060742c034031610175005290608a050341c1d94035580c00c0320303201c003001c65200c1e484e21503448581d0310055202c183c5d4025200306280d898506400701d02c81d00d60211001c0c000c0d000008094020400940444040d03603400803280c020540050b070116125045000b01c00b0050103001800503c051103000041d0740e000e01e000b62940703024800720041c0d00030280241240d8016448a030110085051540605109416640045004d110392443d030700884000e500140c0c0b29a0641c5107900c0c4d1581d00009491025510111459955401d4204440308841a42c8140d902d4410743c1d6107442000500e805caa404900d40b81d00c00c6c0100c0c060300302c11459001d07829410b400000c03208268100c035864580c00442460b480d4400000341401c5000100d079200c001150544420f9 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 40134168 1250 40132918 40132957
    0x306010b03190204141c1112150a0603021f021203130f0b1b071e0312050103050a0210020318100504090603060e0d090612021e070b07080a06030f06110f 67
    0x1c1c10065802c8140c205909080c81c6034451039912141c1d00e840c82c1000703138068000ca003001308d0b00110070072000c8401195040039a28a1038080d0300b0390040e20300ca020490003803c40040d5100c2aa100300000c8280030b0303440e00900390b006078841d0040c0045d04000e00c904514201c047e00c00f400710b000080000c0c0c00310300403011200c0b68501402452061259071003070901c000e81c10803a600220b0300181c2968609042442e4004000c1d1890404888910711100d89804440c50710000004100c400108030310721610a8075000e4480194003c1641c030780c060591013144104254110360030717a2414800361001004503040c03003800c0a848020b03501c2100c0c01c542044504079130b24242004e5401c0108200e0020754042d04d0841802800c00400504021a812612035800d401040c071001641004030601010400600203070749410280c01d013094030003010b88801c008510500045443c0d40b0301030050b402542c1d082501100021a9541c440d40100030003407454444010502600c0350556a0f840203103004101d240d490100f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 40135418 1250 40134168 40134209
    0xb0403030c020601080d1b0215030709030512030106020615040e0d0203070c0902030106050d09061b020a0204060f0f03020d0c0801061706060103060303080606030411040518011a0306010b03190204 86
    0x80c600d044c5c01001003988038407070b0802141d9006441c2e1011800018540b900d8411501c04644104100c544403042014080208040c0f903034044100320403203000e1012160410b1304a158142c4511080c001c410058011000141f00e244e4a1051456400005440054030864440400741001408a034140058000280b144240240000d00c07601800c0d0300d070b20031403465140031b20182c058842c3c0d0b1840000340f0740b100f0031030040c400c1a5010707401030380010f0708110405945c0a0001d4584580c072400301d100d140703009408500640103e0342c0c4401e580c0c0f0030103503400050543d02000003460040808503030b170aa04a80c0890161000e001d0740005040c108080c000a0308454055803d000c2c000b030440e41010f00d4080e0800101380d10410160300241c041d900c1079900c1e01e580c2481d46500500c042c1050300070b8180000c0c0300b40c614290310b800c100807111074000c1190301e41200b031664404640e00119a0315a0201c0300500c019079150340115040801c40d0035804114490050040980e0443d51110382d946400d410361149 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 40136668 1250 40135418 40135423
    0x1e0d08010504020c0316030302090312040303030f140106180312050304030206091207020d060b090408090406081903200d0203040e070305100e090703020d0506090c10020c010c0f0b0403030c02 84
    0x5440704035825420052400d11541d543d000d24886d406030b072034290440605041c0654129500c0b1103001e000e4540740d504411003072000d41d10510049001070314005c0900340e10b00d00c500c151400f004002007913203c07a03440e0060032202001041800311024800f844000002148043d4018200826031225500ca1620b0305010b13003400c0d00140390b04c0c541d400c2855220600082001250000799040392032100c040240d04140e4001c11b000304105403c40c65107000d10007404025400741002140882d02484501e4443c00c915132941d1510901007801280d9189030030000e070107540d8040147e0554480aa006002040128980300e8040780d040c0c0543c00c00102130200b160b0040501e40d201059040a00103420000d404100000c03081c03080c29804008400810310491040c003e4000440c0c004040340b00d078040d64200503850340d405681500c013910458040c074415090030329000f1220480c54000d001ca0b403a08000642e0b250170708440c200d88140424000d1000a183c010f80786000d10b0007558000760140e04254041e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 40137918 1250 40136668 40136671
    0x100506011106040305030a090515061c0203031b0109050601090510090902100309030e03070b0d1802010801030f21020303100608061e041b020a12030501030209070f021e0d08 76
    0x604000c840c0c240030007080000512a0380141d8140381a40d50703651951a000300400702008000c100e8083c0041003c01c0004580d280e9000f507004440082c400785918007105a0482c12020081d050b800610140d85049488002c0a205240a02c000308544120347d48460030410300f604001c0303d40340c0d59424001d0210010510358050003800800b00600441d035000500c801a40200e09000c0640765480c04d13003014401d010b61010502c024049914480e120540306075290000007481d6a91803901075403c482400380521105c20a40684800310b069003580c0703c0306002c10b10700f0f0782510801d102000d071801030040e03c4810549a82540d000d075441e8240902142e0072004298090f5041151101c11320038540d0f03500035048404412032901d000317150044004503025005803a04102800303405620441c0d1990003195a039690b6115029a00340034040c0e04090b42155428080a50442010070005c2d0fc3c1502a558010a020560040720742001c0c11460480038420050000c10558110410b0b82100c1500480b096 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 40139168 1250 40137918 40137931
    0x120f1401030f03030e010b01080a020304050a1b030204110a091a0f0a080f150906060d1b0201020a181d0702030904060b18012a081204080414040903020a0213060b0304051005 76
    0x7d01541030100002810188054580d5540711341c00000704081180410041d886103038845d1400b012820003006003603191600307100590040b400e241520102003c524222400400c99880e01c190250403c465096000000b040c2c00003e10400c000948500c0305280103002c1010382907071080410720700302aa0043c20b040140880c000351034000d017402c0040d9591a0b40652080307056502503168080780b050a0007074200010154403181411140d040e402d41d0640040601c88401e40303a0400890203140c001d00540c07070900c510120b4214a40c44d100710071b840050703400e401455510403a42021a017100040884000384d2180c012400001608040c0e66455031030000d074510242082d89560604500e51040c00b101100840d40031441e00c00110b0400086206450026016040381a120325203481c00000650041c010b520000e8400180c4054626241c012000090341c164090143e01005a081c0302d20b0f6900c0c803a41c502e216803980c2c00841e11120f010080c601c104e00600003001e911404072103581c111003020741007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 40140418 1250 40139168 40139171
    0x1f0e090c040f02030405070b0c01020f0c0c030105060d030203030403031a040e0a02010e01030908030103020d080c030c0a0c050604081f0b060c010605090604050603120a02010906020403050a031707120f1401030f03030e01 96
    0x10000401c0300821041d088034000c451846d5504a2700e02120300a10444004801c00c00d004140010800c02c0001c6445807610240c00800c45521260100800c81e04001c00003030040e801000001d0009200e90414591203100c0c3c0c103aa000c8040c110300160030340d400030680d221103901c000008800d41d0b92040e40c2d40070502083c00e0800c440226615010418401400040e01403241201d060b0100003072102251114100401a00c0d15041c042c0c3d40c90352a20341102c010784030364603174960200301460701200325070413102c41c84001c044480700d41a04116490250b070340080410b0b6140905050303522070400411426084000010340d4604140811102150107803690b03002c2c0d85003100b0000340c0d4900040c3c011000c501d0740222a190054004101e000d0010440e008013a9170011400000308400081c00c8100d607846038a544800c2d01c802031b0301c03e0341794808541d100c00184440f20300c40240007140d0320544410600540105445400c0d140242d141c010aa00844117400400e1035070302450b138184154401c1e1503100c0d00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 40141668 1250 40140418 40140421
    0x5060303040b070c0b0708040305071a0306040c090e0a230106050403031404050604090614040c020712020d0602030c04080d0507020603010302090a14090d0e010201141f0e090c040f0203 81
    0x12950300d0141e4014511099030024401042c0103055070490000c0003082440c0e070780ca03440c620307001c00c45400074401281c1903c46c1c5003010032904224140d4010300030706407125508640d074150420ac082d00884207800280f20002c0c0340031520041100b1400d100315007128002c2125150110701204004c0300ca05003200c8020b0000044c0429588030003228200c03070701403400000e0050300c000142210710030b540c8003640c0104000f0b0300207000049500300f601161000710109090200e458148025500304200ca440181c00c542028070508600c12a004109800985005c0341e80c016599814200c0c0c0c0103661000d01c001d4041010003c02c0f200b0096490808842d1408505000495010922602060000034441d64882c400101159200d6001880300b50700594802c116050203420117480301410080e0b200040d643c4801d00c441075005016244250040a844245036600c0a050510109904170030f4076001202040001d002000d54071581c0c064406003001c0d01403611108208401c03110003265503800d0303500500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 40142918 1250 40141668 40141681
    0x50306130c03020a0f09052103120907060e10170a0608010207060f0608030403050a110f030307030f0206011d0a020313080d05010503071d06010e030111040303020a0b09120403080a2a02011205 84
    0x152420f0301907201000234684c0491824060700f50b004c6e00748043c1c03601c118031701081410440010b00f10101e490584825220890100601c0240c0f41c000341c030000881c602c00c8002100d2844e00015a50015080200080280e00c071a9094266801210b0940b4059152009001d0318038980c460707400203001200040d403400785186e451a464078a400c0018103101142c41200c2c00c6621074036015002030303d000381070304da1f40c044500c0d015100d209403103804001441040700102e440e0350550000c401c4102e080c440c6007032039a00ca45081001c1c0d480201407205010340e000e0000b0004041070040c102185203ca80400c0325810801032501c0d103401680800507070428641c0d403052001440710725030f411501c28680074201070640e1000c603000d00407110690300c0c0e2074800a00001816400f08054078094414820b41a0341d0700d074840210340c1c401d102c0c031800202038400c0204200090484e002805003110a050010f80c0c400d02501140c4407644030901d50503d402082c0c1440219a840b0300d4401c08a06180b004012905010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 40144168 1250 40142918 40142929
    0x270102010b04241728020a090c03060806010b160507030215030a0b0d02060d05090c090a060e09010207240603080307110607020d020d0e010504030506070f02070603060b0a050306130c03020a0f0905 86
    0x160155080b45c106a26440f89076115410116825009401003080f03950b902c841c000200440051140040d00d007031000b2905a1020449a040740d000a034003606180f0611100003044610b80011141c9100d607490010058030340c1290040c810b032101000e82e4885c54240d48410554000c020500d1103003c040c5802030051781e40780c0c1030b1071140d00d0b0884005429502c10b841549007035402000717070f50b10218000c00c02c198801c081d003180381901c918100801035911003d00403800e0303014110300104400907000300c03128001c5050004d2102d20480e420041035085c0d69803910079544d8000d445950001d240f102e410200860204052500001e032440248005507091000035162400c1040e400e08100c95a9016420f41e07200f50150b50207590002d0540398142044000a0a58120211010003502070030200180c00340c0a846100e00311400741c0030841c50512104411030380c50313200903d2a0381c01800702c80b000310000e40ba40b040c07103c403082580b401603030b644610070040e08020301d40c03085804006d032140381400b103074403003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 40145418 1250 40144168 40144183
    0xc060f080a0b060705100b190308070311031b0c0f1210021e0d090203060609010e01050d020411070c140a05150703020102040e070206061302270102010b042417 70
    0x140140007640032824000520f01c0c0c4140f03180609039105d550308065001c0519846001c030b40f80112042e0321202d981240040c415125840090081b08092003a2000f0070b000c2c281c1710310b8081c420341c196844d0541c03015000703145824454010074580e121881400320f41c18401048155510100c86002400900042140e9502c02c51a04903e020b600815420a40360110802000f41040c20315070300d07240c001d800d8035480100700c8440b0991183c42090042103d0b8103007141c415059602440b401c00c2682c0c01d00c4140000d1490f142c50032a0090b913110070a03c00d81c00300b10302910140784202c0181601034640f500c04041c2c084944c0380e4505c0b035540303c1010422903440c0341c3d0001840320280c421035194462410305038024026076000721101c210020400011660104a40d48900c5085403591890201c0d01d90300000c034020641400090003100c005214050031206120005080510011922210701340110b001d540035156081c505045044200364041c5110070200e015118081c22046030984010b501e540c2e4a0700c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 40146668 1250 40145418 40145431
    0xf061212030612080d0b0f18101203030b010801060f020709050402060c010504030801031b06090314120408010903021504051504060b040915051e011815080a0c060f08 73
    0x89036100005403500980001d070040820040d000c1c030941c02410701d41440d5114650041d0000c1c50b0131401d40c66450a800560308a90002d0042030a103000e00c01f4003492944087c18000e00c3c02c0c1600c0d80003407044445000010f000e0710030361700494020b41003c0058001041a0070070001e12003860f04c4150041c2c0d000402d20100d1b480c01c0e101041644690011442521034465894851750804c0704001c01d15410801d158103da102d541102c810311a1030f001d00c1033524480c080d080000d120000c041001c6011071390f84126204a020545400159004000c102607225502c00e2040e41d4441680505154051000560800035146000300e00e2806030b5031140c40c0c21305020030081c0752000c04003003024000c081d8066228540c0c042c0c0100480c11060a084402c00c25050704800b586080c0000a40490752144145004200c0c1d40e00f00960799080284c1d87c0c000c0e980004100781440c3e500c80442a50410302c00d00d5100030020301014151001540c01c14112003401038104030180407071000c03000001a0700080e1541d1111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 40147918 1250 40146668 40146683
    0x9080f120f090a1d091002030408121503010c030c0e060c07050603040503070b04080301030605010b07110603060609031c090e0c0a0507060e030d0e07060903020904060e0703120504090f0612 83
    0x140c01c2c000241c450507141c02c0340c80311100d802c00001040e42082101402840c3c207034200d0320900e03a4a0680c4c0281c0c0b1048a0003848280103200c480146403041a0403900071010204d000b40e031064aa01280c06c440f8a401d18000280d16054528009900940c17082c621140a0791000d240c60f076104ca150360783d40c02c6807284a01811000000405200060007a5101d442e80058240c019007014100316056400c01e000998680c0e107004000116481c0ca00112070708140e2010000f40f08540050402c03006820081585410450820000d00c080d41c0074003c030034440810940e0141a4200c4180007072403007055801c072298841d03290061084101d002001d548005401d840c109580b402d10f072030003a01030003092000300c01c0d51202142130140e05a0b15009003d00000c006c0c00c035440b480d030b00c5004640801e09484040e401803000720118010600d03603049002407150410485020075500d0b920040c5414a59113034000144001c01d05120850080c014400c6005902c0b0092003214140320207003400100b100001000310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 40149168 1250 40147918 40147927
    0x801150c0215040810020a020c0109030f020103110408070303050c0d02010e150910020a020606040e03090d03080903130e04050c01170601030203070212040f090f05070e0d030207120309080f120f 85
    0x42c050308115009814200103603070408a0ba502e411010b5000014000094020001158404c0d446035040004480d04900d00350303a1a8200e40040d0700502044900e40b030207000400001c40c10031070070011540194842d42c0d50650380c41c44100b8003414000095071500c00c5904150003c14010400500035501c0c000c04a4256101c0e1a210032161800d000036815802c01800400da5030032054002c03d115102e200140c030284a40d220f164200782d10f0740315201c0d100e9803040f582040c02340400d101e905496400b821030002c6904d09072280d0580c50410400d41c5c80070701c541441804010804c50113008101064400307082c8850101d031080b20900004500800490405034080000f800c002e03c02c0008180b04800701030856a1a500e950043c4071201140c00b07241901801d00c100351403542124030500d03100c0c002940e40e02200242d10010824840041d1071b041c0c0840c03203408804250442041c9804006a100e40c0702c0c000828034040040f402d103620260740c01402c1d0450108030b400800c03204111610140c2412130315a99 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 40150418 1250 40149168 40149199
    0x21f0201021908221515080a050102130b0a09030305090418150c0806030607030902120102030106030524150c0708240c07030e0607020d0b160801150c02 67
    0x9014032a1440300d26032021800480d074580140c503860064140d99180c4e80c415043e40001e110a80c1219002820701100311002c001d00c0009074400d42e0805105401c08480c140d854006519102441c42c0a543c00c1e5800070350305880411095201d0000c141049001d410010111000f0b0040c001600c070150a101c000030700c0722030b60380e1107900808180d0100300000340040340c54104524043d0900b50340541d541d141010522100c2d014070369491044000800400d20fa5a640c84110301810007400c08130303000903450142180a010a0024601034071040d07400040354603100e000c012041e10700c030410103065440007100184a84418401292010710800001c0da109401042c540ca00009644026454061031000e03c41500308205c008040645040c1082015161541040c101d0301c58020f0040220702c24039800140b6003007000140018900040c1180182c00741da481d0030030b07404000c40c0c455205507030000300390001c0f43e00803076110701614910030b01d0b59600280c1d407405091801e407000e010303100c0d22003c10850380 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 40151668 1250 40150418 40150421
    0x3062310030809041a13050702010f0207020a0b1303170d11040b07021e0a03050a0501060501020705090f0403020c0d0807030206070e151303050f0607030506060a091512020406090918021f0201 84
    0x154a019144119411040b1503080090006a2303200005500b41401c18148480c603009a880d0700390000c081203001441d101003c0b200364804150074600c8408103000101041c80150320140e074607a0b030040070340e070f03051181d841c0e00c00c8804500012086041c01d001c2400410502d90a44528a6064480217045001c1c1c0c15074920583d0b21003815580202c02c1c91307021080210200300f9500040c4204003d002a0341c0f00c0006a850b61818007402d5005aa0b48000a010104090f82030313800500a00598040268200100e806807440034029500340100050b282c041560400c034203984030f001484d101c5405543c1e0000203240300040c00280c201c100d0003048100c040400415010011a8007038201c8401498480ca01901c50030111058408a843e00d40040c416081c80b10450307049000030f070f42e500d40d91070420001c241101581046441007041040c01d0741038510340c910045c4083d1205881c1c044030585809040000e44044900c4040c2d40101c0504250068950201101c245000d03040b0401003466807075802c17030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 40152918 1250 40151668 40151711
    0x40e010e04050a050105090304060306050405280e0d2001060605040603020a050c240a09020303030606160b09011a0109140402030718091424010807090306231003080904 74
    0xb0859403a2901f4002c90b07040c000004e204842c01500c042c0280d40c0c0d42d008110484500301c03441c20655001480d0000c16510008070042c00d0602e0300d03000a511521000705919080120b00084003044006802d4548203882e5550524021031900090010509042d0024a0f6010398450b84080c141c0200b1040701c0b541c0140e080d2092005064115a94038003c1d00645190769006049645502d000d400842c0c2182d8041c0542c00780180c020300154590f40f507501c140000c5034014a442001450b81c0059140012020f11030a802100c5540c000f0585241c1502683c4482c50071006007030500481d40300400030280ca5941d0320300302d401c00300c0d001600ca0740c81b807005460030035403001070404212804e540461080007550110141000c48100c0d40303c1c50351401988a9481c420007243c129600030240c1c0c4050542c803810940740d016480385090f1072f810781d50742d81761001c0d0ba400701550390034910301c1c02e1030920886c40d600c0343c030740d2010203482d837850007501c1c6482c0c61000c4e1080c0f00440c6d002c0c1d07840c0d2010511841d0a020610b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 40154168 1250 40152918 40152923
    0xa05100314070801110706060b0403050703020d02130207060c030501050103091509061e0c030c140d0515030f070306110a140a020a170c0c0402030105060a0c1109010f0e01050105040e010e04050a 85
    0xd1017400c115040e0100c0319400a10201d03072a40c501030001ca04044285c064a058941c03000c002c04405080d0303020402c0d000030303156080380d01040030048901451028000341c004244180c201149042c640303800079056480c144c02040c1050301d0300c0c188801151940c0d008c1200c00008400002ea06041805e00401a040700c08149080940107003090560340100c2d8030480e130b03070021607170300704140b503d0020308031010f8900c194416072090301402110340003605540800d400401101060018420650209040513a01103c0181070341000d481001848a5401100380f00700000c0310042c5042e05050002d0104110000401c3c40b00b080462503c0c5d1250007000b0f25014550060740a000350b81890b840c025481c1c1c4416104c90b40f80c0a00d01c20a0101e04150090341c0c161000104860b06244518a08482041d04514162108600900701c0c004680701c850125020384403454442e02400d0170301800c0c5c03c0d950010790102e81005400c2100b00a141d04205d005810342c1d00070102c045540d256424014605250000007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 40155418 1250 40154168 40154171
    0x2030d0207080607080f060f0307030c062001020f1903110d0504030f08041509020d06060305030901020d020a050309040e030c1c260a050403050c0106030602040303080a05100314070801 81
    0x216515400007075400c2200c5100d8215046030362086011203000b0320a5501044404902010540600d440b25409400004c040c08448580d070396030f11400d00310b03406a0b0000000c43d1584c0d4009210032000081c0b0420340075910000e61034031b14215800c0b4694860070741c980d105138903066045408588242c008003554052816070300d49420381801414010981514200c02003185071029203490790041200e41c0c803507904008003135500d4549860700006403440c82c008991010a459184001500c07510440d40514020070003103131251011000a031604280b03d00075825580030001c130800040c000001c40d081c1d08400e840110b0641c0400d80340501d9402800d054200c1401824132800c05050360308600c1e941c15803240d0740c8403c50543d16060b401440c20100b4840601c00d2000b0002d00902d40310341103140c1052092902c1890014181d07a001e084452036001140d02c2c1d070300040c0400c145944011b446030481c101c080c04000c1270a0038685a0401c1c103881c40f000386507141102040c1061201480400014040e0800 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 40156668 1250 40155418 40155433
    0xf070303030c0f0206090a0201081b0f0a0e1504050f011e0c020901120b0a0b06040518040b0601091508042108040212010c120f090f030815040b0f06030402040204030203 74
    0x5000c0e000d041e000b450800050015039622150300d20018100c0d0041c108100641007a804c1034004580b1080014201070151105000808800042c0c4c0e0060001680c07020b022601c441081100a2150002d420400c5c810414440f07404152402d210071074040701c40448400d1814100880142c0311011501a6040d01c00461229414282d0b000806507404610031500140140c0c0c0310060106c400105840c0a4007034003059000900301001030703002c0040c0107402000c2a080580d1640002c00098040120020104824042c80101300c0300e40c9545402510908013045000d051059002480008a16500130000d0400105046c802c21042c441e080841d078540302c01107584ca03a20040c0440c00c1c00d650403070248814000601c4038200c10b00c200c00d182003040e0b41d42c0200c2d4031101d41a01c094007507603690a42e0b00b583c640c1c40500040c1d8400c08600c6641c407030b8440b8181c038500030b84c100d10b680c101d115005001303508100fa04c0c000f44d43d801e0403200031040c080b9052510380d14ae81c00410000e0045820080d018410140f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 40157918 1250 40156668 40156673
    0x6050a090209040b01033303140706030e01060510030c09090e010b090603010b03030909040c180f0e01110415050702030d0c12020a0c12020d052b0206090309040504050f0703 76
    0x1c0007881d06000585041c0300c0306140100445c00c0b41d950246800094070b08202d8004450280da0900226030403070306540d00c030203032a41c80d4031024030320282e0b00c2d42480c1d0002800700515501400b0704180c610045008000c82480c2c43d020407200b80040042c181010f584100c043c10882c0292074002c0600003080b020048001a440e09a00800c024140d1074800d01e4598009886880d050040141c00903019001c0c1d03040074007a0b42442640d80000e4000c848034041c648000c541090494092084444070207004100581d0410b0880304503900d007a0341e6035150341003490307402c803014140742207a003181c2045004080c542030201b01102c450180003c001d40c140281c0004c103070329980c084003105120340121003c03804c810f04814166034524041c080201001d0b10010300b08101c40716025500070080c0040c02c43c0c298449555a41c504251049801c904684482d681074102c40004101940c0903844900040c040c40c1414012241d0343c0c001c8944491080c2e481d003000400b004014440b9030440701c0b50324122006683c0701e1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 40159168 1250 40157918 40157921
    0xc10060b0901020705040515040b0109080a0507091404020a0e071103040e01050a0b03100e07030902131d0708070b0706020c0307030504051903150509070510020601092307050d06050a09 81
    0x300007040c018440e034100030a85290500c1940d0150300b240000b0f8030b40002200c2800007030708588a4060501c010707803900268246041c81044030300303071103080034100240c10034030001d04641000d00d401e050302001404001c01622260b8034801640c5034203d1a201650302d2030030442d6107419481040090340004a00020381c41904400b041c161003080310703000280d6807140d10300d05107800102c07041c4084901c007190410160380b505405da500081603140124400e210364010400c10307030858a02c1401203540b90301340c03c0000c01412069202e01c3d10003001d000600d150204280d560402d80c01442e5803604d002800e08104a5168100c55944038840c0c1582d80740e98541c02c0c0641240c00502c04e07180140e4038a441d50074a0804450300f1400c1c0e03070344001d05000c0f04170202510001450001c3c0180030f14800d1b04d0021403070341d907940d24400801455500500841d8105416001034a4000400200e0f046000d103e102c816041d452520b41c1c000081d141c0181c403004041040409050154002500b01c0c1e028400030500315041e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 40160418 1250 40159168 40159177
    0x220f0905040b010801050c04031119180507081611030706060b030f0a020f03010b03040606031509061116080f07060513021002070f0512030421030906020a0201020a03050c10060b 78
    0x1d8110030419a0744d40c1d4005090f00d03011035400400c94820003080c030000764180c400501c03d03903001d08240607072119081900314080d200e400c05007900300c55000c40d503c001068000c0651003281c40c5000c140d40d00344260400e4401c0c401d0501c1e0700038009140780620300b9640410070b4135078075078005000380b10585d5100c0d513020003a8030560303800e13001c1e8840c540040d21072600d50003150385030921040d21610750780c6082c5000e0025080a4000c8584681701d40c0e00202081704d551400c5581c0015000020345407159103000e0f0f080740e002527801c101000091000349514480200440080d6400108a030b1382c8190321001c0c840103100300007000348407074500300c240044512503899004480b8400c0e07400801010341400c0c103a13035407801da02c11350b08042c607400d0703041c00181080d9a03002c003910203540489041503100c50b4031450303000302c81e84a141039011150509051507400303e0740100600013130010380980c100a400003900e9603c0703808040c1c00e1200000e901c090b84c010412070780700080d1b400501001242c0e140d580d0104260700 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 40161668 1250 40160418 40160423
    0x5070507031107050d0b06010201181119082d070915050910061b020301050f0609060a14010e0f040507020d0305070908030301090b030102070507030c0312050a05220f090504 76
    0x70445202c0300b02d200020f1030002c0d240c00034404900400195500c0c1458500180750904554036000115002d917003100102001c18403541001034900412010300405525601d602b901003e50608200110303071000c221075118114905c01c00c016203505010b06014a90103000502040c8181080010700030201d5201c0e0120908210640151035919010007500900c00c0e10003003d026000788042100a0098043c101d241d1050084071f840380a5a40000342103030004c44000c00340039444010090682741c955107031036010b501100d501d10000e040402c103842540c8001040c9041c450340d5030304010f03030340da96668840d44400001c01c203014070b241400c0e00030744480d410000d2002003800c05010442c490f0241f0134000594494000441c00c580c40c10340310b2806030040c03816280e0503550801c5400045007081c0109009180240e5403049501d1840ca0800c0d0400550041034041040602003403070550303403140031103004840096412900410440807001c412941d648042c00d00a04510005200c002a42105108a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 40162918 1250 40161668 40161677
    0x2010207090b01020c0f2715010903050a0807020609060c011a0f011d27010611060408070803060f090112050f010b091902042303010c02120301150e040507050703 71
    0x654601032a8160b484919680d070250700121000441c5003000f02100442010083c20711010f801150600003504d200702481d010500c050b4010884444400074801c000c1040070710f400783c0c4003451512a25181c0389a45801012410005080810340d82c40c1000c0d941d5590005080640d00e13400350120500803c5c03210324a9101c4500000b016120381b41c4541508a200f5060f112034000c0e41d91000e00440c42c07070100d44104d41c440550808211008240e01c5080700803465042e4135141135051030806400440480e600744202e604c50303010040020516002e0740c0c03074254440d46c0ba036280d8071a1000103488064840c4010303000040540005040303210300c62415842c60050003615165514800c4090984000086840d0096540340c007041c070f4081100000300c10010100401070625494410806807041f000c1a1501e20b88001c2030305040340e1400b8800c03000c000e0501c1c0000c0c07a03107460310045d03c54940014811402121190041e0640943c0100d400e4190410000c1c0700f00250b1400320300140290300410810f50005d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 40164168 1250 40162918 40162933
    0x3110c030d1e0804020f0f060d050106091a04031109070e0d030306050f03060907060e01050d06030506070809010209090105040209010207030602070b09060c0304050307060903170403110d030b010905120a080705010504020102 98
    0xb140680b2003030b0b02958014189207551018070052010304c071404400c15400031410032500380050030324070810340a000030350b03070715038000b480d201d0128414a05d03080d0489003084100803c1001540901d240bc3d4114030071f0790b10a0255589040c1501c102c10190091500114088002c20070103505520010a84004a6911001c82160418103580e840101c50562466001c0e100610006004a0301807511500524003030f40341031003200341c840654506500458a550280003413010700d41e04589456800b05144008500f0b00302c5003000961030390018443d5a01441c0d000902d02084d074400c0c480003000c0c5030411015951101c042ca800302c40c01404488400c1035000302ca000c80d0a0300040e104417800350350002e00071800d000300c0d512290300074440100101e040c070594020200030b00c030194000764840d5010352070f00354090103954565403d102a0340c0b040c50406107000440101c580c1c0004101e030590340c0a0351484041c42c84c4003a00380c03400f40a4100070340307501c402242280800c6015000148514400e03820303140c10 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 40165418 1250 40164168 40164227
    0x1e0f0a060f080705090a0b030715080601050306010c030c02010306170601051003050105010807030b060910120b030f07230909030a09060302090f09070201060b0c010b03011a09010303110c030d 84
    0x1c41c440340c0900703035494111000811940c9024500c154002c2022480043c45444520019242c0101c1d42d0251488406000d0300000054000b04003a900200a003421440c5140a40c00200356600e441001014004401518070942e4800d0344500003a01d032000c003054217079444100d1a0341c9c441c0244180c0380b042071000f1100c41c015109004560403620180c40d00f81240e02d81240c20790150015244030740d04150705010050b4142d070340c242040143c003000d440d89400c4a4071083c981c41501d005040c01c0780258009030725041340b0300c00014480c08441200541d10010021806032650440c6402c41c0c40394044078407410300070b0504c0007000030400390406440303c106103592501c081e01070b0b0044020b071a6009100000480550402166469001c0d031107200000f500342d00c403500b040541c0c1002c5800f012981d5101402e0420782401d104103503903207070960011121203094000182c1d41b6501400700404200c00c1191501e0846020840c010780508001c05641e0a00c81c400e100a06190b00e500d1041101580c1c0f80d5403403034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 40166668 1250 40165418 40165439
    0x30b040515090f3708070206070b061905090a0b030106080d0503011706060105040312110115050411070b040609020a08030301080114070c0201020703031d0603010803070b010b0309060f1e0f0a06 85
    0x2d080313440321019030b130743d0f1501d103040c0c800300c03a10034041e10f60141c00c0008400603500c00d0000e156180c418613180e015424441d092221101c40608151050f00e007068090100340c1e10040c406900c07107403509020400c1160007010a000d0482c43e40220203510a484036421002d41150266042ea90000701c03003444110003480710b40d5117010036146c1902041e410041800858600780290301c00480b04e0502c416080c032181c0c1c1c4142126918403400c0d070012111082072001c4d16042c0240a205a55608107904103003e60b2a407200701c00c8040c10041c842560342c1c17800c0086403904d0125000600c050810703a5102d694403400b20b4080c10384018404c0804030002c0001e80c409000d044040b6a1940683c000d01c0b4003400c40d0307001d60f000f13a10308000d0900881d400080364003542d6207000545c047c1844d08040c5071180c4061500d40500344040c3c00854070130720207104214210000059a030351050131030320368a2264075014100c01300c0441501001da040e003030590800c159006815142c03805180e1401080205075582c005452 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 40167918 1250 40166668 40166713
    0x1803210a05091c050c010203120103120903080309011506020a0c090b04090218061008010605070308040602040807080f070b071a0c0904110c1b060a210c0c03090501030204030b01030b040515090f 85
    0x49ea1032002c400500100e4541c01654801e03e1a41c100148c1d0f003622600d4071496a00210f56021050391210400c0015039203419060b001000180010300084046075204603a80c6094050b82e20b40b25a034143c14185942c49400180c0c0303030f540107072525110a81c1c0c648580c44804040b5861401007084503900810740c4c0c49030400c24121041c2e9a159410000196400c850f2004c0191068500340c1c1c00b80404186040d051150600900981c402070010214032548942050051340c05114007140510010022a01040941c0600d800b0600007180d0faa4a4540e00d003100d0281800e11908980742180240c05a4030300750040040c00840c0f401ca0302e251031a07181902e850142048030755001802404602205400799003211250744298820780d41d0081c4820701807003215842004c640000e00600502014560042d4980001d08428230301549054150303140e0503e03900043c07100a084104280024051182c2071040074056101442c101c52a410983d0750070783d45145900b4200158003aa88452980e03026201214 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 40169168 1250 40167918 40167937
    0x50c07031b020a0b03040f06060b04061202030f01060c050a06051512010b01120b030f06090105040c0f06020c060a0203210a0b01020c0a0905060604080102030a021803210a05091c050c010203 83
    0x4810f03142031120141d02e540024100b01c1d0018601003880d800240e080c0036102c0a45a1000c019072107c0c0307004002040700600035103240301c4a10400a000b02c0f00b40303c8000c01d0541d440c42c2820481e1440b00c0c0b4240380381031261100034141a1400c82488a604001c41c00d04e046140d04681c0300b038000da0f09448260803217074010b0390580814030341400a40c40c4115504500034048004040e14a000301c14800b02d030603c0340441e040c54260755602c00308000c01044a1640303026019202c0743c841d505082107406913071203c41601c002c1c4a154041950201203100b001102d421084c0754032603032040064044800140b15090381c00311000760400c3c699020b19440025004202007004113260340c0c26240c41081c070003c00c4040c00c4c0c0394021100304000b0910107424001140141944400103139210810114000e4a110f403c0d0054131940040004041050488208008003804031841c103a5425000e80190f03107510680c00100e4200c8103800304903d41c15071801ca10b80742c0e51300030015600740b80c02c40401283c40e17208042c0b01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 40170418 1250 40169168 40169179
    0x9050301020a0f030e0712060504031709061f120c090e190204020d023105011419090801180516030b040323070b060a080102040b040b07020310050c07031b02 69
    0xc500f152031283d04441c2e1144d0344d41d016100c4d000c0e200c0414050360082d07a80203964017511070051000b01540100c1d40e40b00454002003001407070420254058030fa40c0040c107001e920681041c3c40d0441c28516011801c000d01d0080000c0ca035014181c600001038420703520412600c00c1c50000f98819204000c515102c484030341c024110f5420305240d00700402500a02643c1d079645500b8046180b85c00c95142c0e05001501102459841c8041160080d12080000e5000a0704020503841114045800c206c2903612440f141e04400d440c1d0080c20804850600d0b266100f40013039030030b100b40c211383da020f824444070206000f20142c601c020040700c1001d00f104407500c4002c02d2120a500042e02003441940d0340b00300300805880c011031913880381e01c0040aa80120105590621010082c090280340050412000700b000c44000d40c24103260080e00880e0340614440c1c00c01d03811000a40c1d808540c0c0500200c811303964114410466410f0035165041190440703481103000c14008000004a5024001d03c083e5007130b030003000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 40171668 1250 40170418 40170437
    0xb040501030e01020405060307120506010f0807050901020f07171902030706050a030603060504080a030b03060603030405010309031103030906061921060e0703080c0111090d1b080d02030301050109050301020a 91
    0x441c01070032607011111540d54240300c081100d41d5040300450240340541d80e00b584014600b0080003c0310000ba281038140b06400390f250004980110031030b41d01140d5803c03c00d44a400c0103006074148412041c0c0b080e0680140c2e5008140c001c180f2901404c6c0100102c22151640c52034191101440b007c054040d5040e0300031002000028422030080c01c4a014915010520560b42c1d0703900c10503658240d0701160965408a14a400a5418811031b110950214010300c9141002004203440344614020681019102c04130681454028040d8816203038008003105c1e640d107001803d064940341c054a00314400e007108460070741c0090007840304074180e9070340101c454080e0103012840e285508141e40104d070071644894800ca52003030140030510003180100b0a0075621004030084900f11085886859182002881505101c0d05c41040041005030b100e811400c060360903440d9031402442c59840291103102d00e4240843c0e055000c009175040315000e0300c0f02c5011548801c00c05081c1e005440c100d03030014000c40d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 40172918 1250 40171668 40171679
    0xb01050904051c020a0210030902180c09090405030405180103050607200a050a0302010b06040b07080304030c14010603030e040507050910030f0c020102130e010b03041b0509091e070b04 81
    0x41019400521910440700901800a4401c0404099a00f0302c0056041203988005500740f10b44111110b0480c2d05d0100050712003a030028803817403170f5850752142304000e110000c1c1101441c0e8003241c40711800140b007400646414a441981c980c4a0b004250043c900029103054501c51440e4860503a075000c00030f0003c0703548040c0101c9601c1842e01502c0304100c603011a01d09105018040c0c88000782c0900064007500969040c00390a40d2000302030369000301030400c020414818510250740041b94002400382c0c2d2500c03642000c84240601d0500604200303400c9a50030f1003d6015400581204c1c825122400c031400f04d241084112102222403001045040060b8080303464944483c9520440500340000c40c051003a00140485000000f0800941e5000507925080c00000e04030500902c04c2e0761034014198140304140d1854000500001d050303d40c3d07061100d401c1c10061550101500c0094030310001407401500d070076902c01410208d8181c03030b00c0e02206024001808101e4000340c1750800c0b582071800d40f522 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 40174168 1250 40172918 40172929
    0x6010e07050c0a02060f030a110a1407051e07140402182403010b1c02071212020d0f06060e030f06180f01060b130e04020108180f07060807110105040b0105 68
    0x4070b04a200d503005142c8404016552031010f807841441a58803141c50f490314401d45000c480c50174024030503140007400074526003a03002e1000b50008d0350766240303191a05040d18086240800c2042c41914040c42e5850741c505155000a20004845008000d04c480b030554506000803031080300b6441a00004903444801c00342412120948820025046c01200d440d94121840f03c07a003003a0130140c00b203030740041d0000b00b6902d03009144a0b4601042c0c02185060169524403009140300301d161024000c1202c20340100e54060360545402661a04040c4a01d140b4412410000c10440c001ca00c04100c41072030800c7e02d421b0009120b4130306140314000306440d8440101c2c2055901203507200404600c95491100e0200d102801084001c000c0307514013945030442c038a410400c10344140c1041d02506c0001e07080001503a8880641500030300c0307039000c1c4c405151044d0840d509014240c0130143c000d100c0d4240000384203901c4075005200e0b000507950402000142c0355000d0030780d0010f03503000e0030815024005000c0780c07a22 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 40175418 1250 40174168 40174177
    0x4030b0412120f02030108010e0c030303040b0705040906141509090c09220e0c010f0905060a1b030c03080108070302061222030f08100e0a0b0319080c010b0306010e0705 74
    0x94100b4076800c4001040324010b8070b00d03240039801125000300041001c4030090080b036580c0d07a00a406442c0d000600c1010236500d000050000d004190904003140c0128040c10071a00604000001441030350744502149010b84541c100301400703041d80601c61401100d4042c00e54295020040c02c0d62402e84807080307403101c641c2003442004e80c01011010443c0d0900300c00d681442052044100200349a826418454180f500a91050b814414820400c86429601c88000400d4410490f103554403078590790011502c8110402d10074200b1030302541e000d003e15800100c603200c0f02c3c0c4030380d907220442c0e80c8980880340c40300c2c0346100080d0056002d002c02c43d610680e80b00070aa2000c00c3c14210b20305c861001101d510200323079040d41600402d034002041c0040c1c42d441108568445010520141c00502d420500f03401000024829030300341c0d0b554000d0030102c0e40d00340501c0301a610f0a603000741541460b03052000c119803000e00d520703800e5031a080d9896000c1c140031612071704a900380d09010506588010007541c25600 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 40176668 1250 40175418 40175453
    0x3030209041401180203040206030f1b0a0e0907090b070b0a0f1b020d080f0610090e010b09040f0608030909040606050402030a0203040b09010905030a0f1101050717070504030b04 78
    0x40038000d035452615180300325005682d9890030000b00703514004d0700120082000c02c1c0c07080c80a004000308009038803040103d0381c2120302c07041075054503070701c584c5130b004501c80c02035800b200704800141902d80540e10030240311503000700304c2e0011215202c9007801d5800304460320540c3e41402c400d1000701c3c04598040c0035598000d442040210b00c49200081c0c8008031103000c1200742940040000740d115450b0b0420101c0303202622828941c02c5400d104200007600a402441036114040c845074842203e8481c6103181c004220206202c2c040c0d5865020780381941c0c10140215018515000e18264224041e00400301210f9844015500e845422800d010501000400584e000d940b0340710b0000715600c031440114481c1700a40e06c0140c4a041620744400814006052045168105141080820004403c607000e81400d8140000c600c1410041607684031030182030002107518100c01c03c850260822000310813042c2d20307580e40c001176840301e0042e03c0383e00803800050519001c0e200060300081c0d106610f00780d03400313 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 40177918 1250 40176668 40176671
    0x1520070305060117120c060912030c0306060708130e01052d01030c020a0b010305030405130213060302210903030601080106180b1c050411090901090f0816020303040816150215040303 80
    0x42202d200c01003e9400007006c0c4d00958840d40c20009507000c2808549000c0d0408050399140d8140544440101d010103840306204010015107102002031050850345503403010940c0514080d80c0701c050f407040030001d100d0280901e101540004442c001c000c080b000000e02600c4541d490040c1794011801407030003900504c25031040340284000701c2c0b07003154200d00940c401c0c0021680c650519052002070800d00c182c030411540180081400e82c00269444000d0307840318500103890301150340272101001d20110601a480c0c0302201485600a80440210b03c80c0c042030b2160078060340c1c3e0380300460307000188880c00105071000d403500f4401c107150500102840c6501ca0107656201c42e80c1803c840c1159000d03202244c96912341446007226040c4130116a51140d10780000704640341d4039803640408850035400007010110b00203507584400c030621036038194890f0090226900d031500d540c54140da07400f83c980e40700e070011003690001440b0306450b41d0a03110020f040d4084c0400c0206000c404210f010080d00490a15 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 40179168 1250 40177918 40177933
    0x108040f02010c1a010807051203160224070b06060306100e01051b0f01060906050d26070b07020105011401140307021f0b0f0a03020105070f0302071520070305060117 73
    0x41344804501584e50300750143c2c2240303516000c001e902c0d08490b64800d070f0007072500c06640200704502105551050f0701e04641c40d503901c0b1103480000c0d541c441c103241100c4040c0e0a4502e440010703140c003025107c4644605105404c13a11084c040107498001200d90f07560002c00b041e03200f102180b0915000c0716400040c10200e042485043c03008602a03148044501a503001030f84200410000340030300c5008012030380d03082104070300704030200705c105641030341c040c1451b48400820040415101c501311103e0725000f120980310695807401054485042d160345006608250010902c0c0307141907c88e2484c008161104070400c50031036800401d40d080200301c44103500660b030710950b00b6403c64400340c0c13200050740030024110079807504114202c80700c0003445014414105084c001030344c0120498540e150042d0200002461624040b807810310240c00244026400c10319020840381c1040111003460052242035110b000c0c811085992482d035484058019801a8010080303a07500300800701960041400380d9040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 40180418 1250 40179168 40179173
    0x103020d1110080411180601031503021201020a0801170303040210031803080702010608071202222909061f02010e0613170f0711180901050f0705090108040f02010c 72
    0x5214070300c0d411002084204003044100220000f809500391022031b64070800d003414420318186800000d254906050f0b41e40741034206585403200040003168014202200040c1c6415503601035000203000030081030440001113488014500d414585400c40e1004605503a255001c108a04040034900c4050540c4c0c0c6064141003045200c500000500a480300e410071f00b4101f200038215000740d40f28118a4004c9142880b209071305540c055021078045684030301c4c203c1d52400b92104a4608260b004816180002a240c3c140c41d00981150605001c00c01e0030140c80700a0a01501010890ba06603001405040004900081c43c10100304155184000214091024032080c5040000c1d1424410500500404400c02001c038030902c1000c1c180c10b00365400c007200d07401d0901c4940901180101140c1801031102040e8480c0302c0038900200251180d55900c2c10700d001014020320b41664000c20054200c3c0008002c240288210b0f020400181e640d80701d1a607598481844596100c0300403810003a401c03625601 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 40181668 1250 40180418 40180429
    0x50c030c0c01020d050c0604020d1a0f09010614060313060617151015030908120c070203120a210605041d0c010f050403060b030a050d0507020a09050c030103020d11 72
    0x4482004200400194650710006841c1580d900004c4041110400240c96640e501140d039540059068401000c400a035250000d10709a210449503002c205c5502002002d0110750031850007424a01c00800150f5102c05803e0882894400902d41042041000c80c5034401940611001d1074000c04d00064196140d06503201e9001030207a58501543c055000805041000307a240e0703070440111101a00298582104024555031500f01d90080c1561039080030248040101210018481803502840030314043d0b481800642004409900030702c104031804d44090039440845010100d0b90b140c0c103c401d50084400c201c50f00784121170f40d03032442d10b03141c0c002000e4a507400364024104901169168032600200c5240c5402a4070203c10304100158900c0c604407500901204c0a40e40c100700046102ca010382c010074604072220f08000c0bc01e00c10031984001c40381c1c0c00406003440a2003126400f5425503a102c0400640d881640c200d820f070b5000f080100010314000b0710011906100e5124440c0c28072007a0001070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 40182918 1250 40181668 40181677
    0x30e060c0904050c0406020a0206070807050115170c0616020307050d061d01050609040b1e010906090e0309130510030804090501031e0b0711030f04090f05090d05070209040201050c03 80
    0x112100200798540e01d440c0902440d030340001e107042c0d10341c10031b840d0050080d0362302c0826002078042ca000042820602000600300c8800700d80101c028001075181d0100c00580d85624411140c00c03a048580c3d5004100012a8440d0180b40c010502030528144020003003d640074070b03800b01c0c4d051203001000909921582c854609850042e50001000c0342d0040e030050401c60488511101a49013400300580f50755000001a089038002002c00020380c0c4a410180441d03e07203003081048214820300000c3c00c00220340101040e100b00400a0207442e000010080c0d0341c1c011900d204c0d034030541d16901105840e516070302050f40072216158800c9140d0b036030f8980c81d0700c2da4010340101a04e5500c400060003488014031415400051541c10603030800e0040d00c134010034000c060315107000c00020a08900c14500100203545450000c40609940c0fa0782d43c810000043c0710328005104068140000500c00c0ca1011807180540c01170350715024586502c5030300708500d686c0c004108906102c01486a220076003070800242 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 40184168 1250 40182918 40182931
    0xe06041e05070e0105010207210813030b150f0d0305040506070813080102090901060503041109090c03010f0b030f0a080d020a03020415030e161406070f02040510061202120c0307030e06 81
    0x982d0f55410300c000281080c420360042c020700c01c0000e040d10f0072407503039070041c410541d000701c030581c0c0302c040b8184990201360960307002134150030a10080c00141e6030841c0c60311007002e004079110300611000d4414880303403007903040c4c020f808100d041c04200f0076414040000d10460703116801c0e107840c00c1713242c0342070341d2810035250083c8001c0ea50108003824141030009000d801b4120600b000d60451500356a22682e103400b5504403801001182c005c980c1d01039003000f510a403410010000e110042d0131a400c20010051445124884c2c8511030030700d032205501062030300c0c00580009001d0b00d01440307440c0c070002a44c01040048205982044000b85c50010400c80c807a00c058141d03408100618a1000b591802c0042c90440c018502420810010b403403400100016594082c0e895640307807015030500a00300111400c000c0d40050038a0100507980300601e4080040c7c68142d264400070444031140c920890180078014003400071008041810b0750020300c051035212000e80340200c2c0100130000f142d0304140d0241d411 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 40185418 1250 40184168 40184189
    0xa021503010603050108070b09060c011b05070b06060712110c1305010305150601050915090402040f18050702031e09030d030b040b0103021207030908070c12030305060102010e06041e0507 82
    0x14840c4583c1030113160f00401c0e00800078010705003403501201c5c1034420425510301c90326001510030823685080d00181160a10840c021450701000000a440c9520524045529104000c0000e20600d44ae50a40d0442600298070180c0c071199110140c540c080c100c03102c40002e100700f01d4140030315502c07483c0c4400c08030002440440c00d0f502d9032030807914044004030006034511204042112a0343d01000f80c8400e40d0044410106560700d00750180c03000d00c01c81c0006c2d50094000140450315980c1d102500044980c800c0c16034903003018440c0094100c40c4161480705c0140c0003000305510b500b607204119942c0325001d40005240401100000785401c0b04089140c02098454200c0c1100d858103220780580c2520a09007503150604480006070030362001043c1c02d05250340c802440051106e10425903105c00e6200a10380e02071500c03500715811040d17081004400080c1050005040c0c1c3d4418041c946688922000610035a140e640d030707010754204a5002c0121101002d1861404a40204500401007400c1c521 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 40186668 1250 40185418 40185421
    0xb0403020a020a06030e120d0e010f06050a1512020f120703090b0601051321080d020301050a09090b0a0902010302131e06030c12020904060e010303170a0b010f0806030a021503 77
    0x43c4003089110358086001d0501d004805503051101007003092050011241c1c041d031f28000103540e03400400b00d02c03070600a150f00e001c003041c01800c0c865001c0c605a81040302c0240540d40d4440c0d000d0304085480035100001030240440c070006207001e4000e010000d00c00000e40b0300700448100c0500307003640c00701c5072000002d84840c015014083e58841058104000b8608940303421415036058070321580328451b0f02d1140c00491001560928100150a0041d0340a040c040d9102d001c484002d020303400a0262601ca0b102a40c00000e22031803601c6a0780b02035620800030b0609503a122480c82c0242880302c42681416000c014840c2801941a006000360450a1041c40301c10800c5503204e03481102d0340c200c00c0a0600d0185c0044071183c0041a03403607410402036000d030b0303070b5054403021401034078190380704c03407128243c0030008000c0641000202c0451030303c0040d50398290791500c020781c0c1501c103540a002e0210704084a0440e030a849151150742c880c502a04484c10b00045501003030b085200c040381494103010120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 40187918 1250 40186668 40186673
    0xb030a05040605060301060803120a0603120207030506060d1205090d0204152c0402100207030501050c030906151c020a0b07030e130c0e06090111010c080108100504080a1b0b0403020a 80
    0x3c5140d070019410340003000340b07a0400b41e1590b0b0b00d215010880001c22049000584400c0941e080f55000d580d001c0c980c814614090200650361310310b1404100c816001300000500720b41451280440f10f141c1000a19015840d8004c0a69032070384403140c911341201a2015520258407140190f040b504200d840d02da0342103107011076814900000500104204944030940e6450759a41b0355000e0b00140c0440e9022903402c0e11210580c50901c60394030081c03440d420b1400704107800b194840a18800c4440c07500b0385a855541c0401c03002c0c0010b801a14903031000d94a80108100b80708030710341d000301ca440a058010300580f40ca4034440240c001400440c002072184046407800d0030507680100108001310000d01c4130085c84240a010b040d180403201c0d004503008180b403400ba0f0310412000301d002d83c100e4020049108000780c0100b00807400d0203031481501c2250b2182c600d100442c13003010b11641e001011181010001501201c001030208680021040d20103a03150200d2664641240224400e4000f80040f21292 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 40189168 1250 40187918 40187921
    0x3010b18030601060f140928080d050a0e01050a120506040605030102161101081009050a180b0609090703031b08071502090a050901030503030a09030207080f030c0f06130311070b030a050406 83
    0x441441e1100c00302880030307400986448c50214000c4000c0c0c800c00044c24502c12100c800c01c01958004007107840341101c080f03800c913000001406524810b5803103580038040c90b001034859200307c10b88500010300d04900c2411041e810750026030064001080803032440c1d601d00010703099030040000c0031018120207503136004202e500899012100028201116140b40c1a5032845981003107200340d6000c90348890024006a180d5800038404804880b5041d114007568107102c007850000303d0f0440d0040d0440f4022401c407400000d03020040303a5040d603480c40580e181c00068280c080e103a42d01211a054203000c01d200003141049000c4c0454621800140c0b03454040c8100411045d0380c0d8421806004644018804100c010003225440781c01c503c070100390320b0501e14040707250030129800b400741406880c03402009014003200a0038000d00050407500c8281c0320240c06900e0740400e45101c05140c140c0c0d00c030440081c1c0500c043c8030385514040c0940384429139445410142e540112203913000d5584c0c7e40c041000300040d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 40190418 1250 40189168 40189187
    0x9020408070e0402030d05030702070302150703080c090310150e01030b1504060303052209020301080706031109010207060807050c010c050a02010e0f0d050903160b0901021e0303010b18030601060f 86
    0x2e0000000c428200b54000c01e4403030010b4589401080f90000000310b889000b004650002e5030701a160100300700c24504140707019080030b24110b000459820104000034022401e94010b684010081e00c540414194041e0080011505605030101d40c0c0900060b50307041007503114000c0d40034400d004007600e03203800c01d00048005a010f051099240190500100340d00c6010380380901840240f4042d07042c1c40e00204104d00000e58010300c0002d000100202e0204004102c0c1d01c00ca42c0c070394609000c103c100200000850282074100b40c01a4000e440c00c01080d0300c01c544042e044202d5013045841c0020285c440d500b550b40c118111008210009100300502e582417240112104401e006811146110002c0303544400e04a4406020010f0215402c9400c0e6011300c1014070400030381080d58602640d034071314190203801c2920280c0c058020402400d04141c5003106490400040030701541c59a801d101000307900c0d81113001c10440b07104044000169549007001500c6c060320b03051f10f540003910002c2c50020442d108 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 40191668 1250 40190418 40190429
    0x190c0516080f0307030906030506060d1a1507080711120a030206041a07120b03010e0a060b0a1d060904110301090c08010507030204080613050f03040b0903010501051c020918070902040807 82
    0xf00300001c0002c45e07409102c5000f503811900d000328454841c240040e09500401d4195803100e8a030620b0700c00210a8150302801310101500e40b15008802003040c140706010300d0384042e011074401c00a01c0001a8102d001000408009001c1d21610205a000c1c2c0d260000e44941100076a00031014042402080301c90300c041002800c06c41001860011401031068000c48180d66909403191400348a030b545c20f401c00c5013001c000c6400c0b928004c13100d04059002c1c10003090400d000e8244801d002c105414208100c000c4103850f4014007485031541801d02040020082050304e01c000080703035403402c2d03640038080c454980c0c0c0a00156155141040809800c441018080b00281407040008120400020419039441111001c15540b450740608105047c0a000034141c501c5020000d0301080ca4002c41c8080c2140c68401d5000700141ea0b00c840030301c40d203040710070038100c80c0d84030301d003128001441c10103103c1d84e1081d104007000c950050b1000b15186840c181e0b4210080241d0042010306c950181003040100900 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 40192918 1250 40191668 40191673
    0xc0206010510020a06270302011a0414040b060d0209040b0402010e1e0105031e07020307060c0503040b0c07060902040509030909060301050105010f320a030506040c05190c0516080f 79
    0xc01c01019581d4400104d006100d140c889500070581c07100342c02c11a244500c3c51801003440c400500d4024028245480369449120034400b140e1800e040a20540c007440f00c8250915180b03403501d88404026940003840280e02c00000c3c0b040c5401a11400031071402684203c0c41c83c01203060503c0054450b4101051090140703140b4249103003115801000c2110b002400e0070302070364a44a01c00d58900445020310312104a060300f805204840748e001004041302c5000d2182040400c04140d01200c10f8441501c015140c5d01d0404081045802e4010080205500c00c0d00c0c0021000e600ba07000c00c1c1640c0c1d046403445107d4101040d511928244038a4090f40301808500800c015070601001034000700e40b5a00500820240c001c0c1800b4604a02c80c142450100406598121400c41046601d80307600c0390800c00f00107810300012130054102805a40802c00b4144c60780d0b81000c6503840c803801c40f074401000390700c10040740103420804140d003448401c0003000c201c01141440c50030141c0340c0d840c001e0030004000c140d9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 40194168 1250 40192918 40192939
    0xc0303160b0a151208070f030f110d050306060a0e04090305041701090b04030f2303041202010b010e0f01170a050f09070b03060d0c170a030f030902061909030c090c02060105 76
    0x440f15040e0103c241c9001805199040f0103d0a0410840c094030000400703461161440400781a0010440c0080d02a2950b801c42c140030080103494461429600d5a40456000d0011985916099003d000148010300d03003028440f90b442c001238141e0b20130220036804a0360018040c0124040032510001c80e801200082c8501d150942e602150008002d00260402c030641c0c8020101c01d01c0b58110107a4082e00711151413240421680700301d0182d10550302260807403a00c40400b00428018024841c1e902416141c0303140015280050007070996080c40110f0402c411107121321503a8034491025800381c1c042c0038000030030b1711b000b1800f5540311314054804070751540701e8401000b0941100c01120303480a000d480d2000d03a0030461400240f250610b8004603482030703a00035048098140003441c1c0c109035001ea03599030f210218000041c1c003110232214029400107000c01c10240440c40407003680034290103e00d88007030069683d0300ca48004603465000028680e45525000141c184d041090302e0247c002205d000b00c08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 40195418 1250 40194168 40194191
    0x1020703020703020f01090e070807080609010617040c170102090a050301020405060d0e0a06020d09031d01021005040813030f06110307050304020f030c060d0c032301170c0303160b0a 80
    0x16110b080c4402031207001402c41801c41a44a004043d000b44a000c404040c0b44c10412000741c000142100c18000140c1070344001515031a00c031000c076040359550b032100c842c42000c1c441d107004c4011004009a446503910034000031000d212548010b07a02c410400010303103035844c02d002c20906584580c09148280c1c01400103220f10398880040306c40840943c4400900504002c00c0b1905100380d4001c054100b40c80441c41d04c4680d03440707411425640f4804d58a440c0041c00c5c80e4503e12442c0000015603005078400c1403104150f26090f8400c9401c1809090f049041448030910b01c00820000e401c1100c415003404070380340410840c0c1c00f031080300c0031a009500d8194a0191401080d42c0001400640300308c2041c043d1640c01d440500448601002c050039055440200009840181001900c07441c0000c3c81c06009100d00c1482d80b2820b99569284c80f03440c0111792902c00100c84095404040d01194000c0c07081480032542e081004140b0100c61103e010070f6a115401e000060441c02058488000d0403c0350b0440c6 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 40196668 1250 40195418 40195423
    0x902010801050613120302190c090509070609060c0302010e16030203060708090d030f020717180102190201050c070b0d05071707090513020d11040905010b070c0303030c050702031507020606030102070302 89
    0x20341780e1100c1e02d0030034041607090492a00803003500d49244e90341c0070618941071003800d6000c0400c0e40c40081040c003540d182e00c0d00c0a41d8810192240000003614203600b070080500c1040f000c480c940c068400840c0d10080c6040d00340c2040c100b1503100c0400d8621403001c100b10f05040c09aa5881101e070b051421517880e044022039115032207001500100359503140300c15005080d039070540e2025508440d498201503001c405602d01d540c40140011f0703030380c100460307074031050361000030140d04019510b000e440c03d84203598010758143d0480b03031060425000700c035800718107440c0420140c07198848810001c2840d051091018123601070540c08124103030b4020042004207900452068100c910070385003410741594201d4464001d02400146450050421701c403000300b066040054026582034540821459903900c40c107203014412310b100204418610700c0200042030180d84001c3c0646140c0c28150b00d01030b090750001c1c2c1130016000011200c00014400d21103410fa0401c0b504ae0301c504294002c601e001e1080d2006035 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 40197918 1250 40196668 40196707
    0x200f12130b09010323040c05030c060738070906080103020108060118080304030f021302070308190204030204050405010c0e0108072708031308101401090e150a09020108010506 77
    0x5039500000280c400c000c3e40302c0d502c402d10640402201d0100d0001214009040c24810388094482504820340801e8510700860400d40c0118000d012030302c0c054032030751403114040b0340c1c09456041e00480040344100034070400d01500ca0b03c0d12500d42c00e9191502c41e10107415003485070044030810251400500050b60019240d503004042420005205041c005126040d42010340007444a0f000119001040014200950403051300c2158003100c68a0508840d408a0142c00d0000e0005410000840c461240704401c890149280400252401c0d40360340128007034801c1a01d049403180e549044107c001c03940005144202182460144000c0c10a110010210b00046407880c0d041040401d80300181031541c0c885500030240d16082e030741c803944a0f0102c4a000040d500c500c07841c9011380b04212003984903902c5250b5182810b51020a011b0342014000b0300184400304011106114160302481c00032800341032144107140c04000403a28480500c001441c2c5030381031f4031803070040748248000801c1001007121403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 40199168 1250 40197918 40197929
    0x2011202030414070b0702180c090118230405132d0f0305030702060709061d03010f06030819020604020f010c0213050106080f06010f0909020307200f1213 68
    0xd40c60741c58605001908204010040d90f05114030080040c201c005000038001440c021220049803e642521111640604136a802c0c0e110303070200b00c2101c25600503440807251044185c5100d9140c1d407100526141c2216109034842034a14182e801c4403603117014003440d9800042505991040c0d160384e40c500340d041d0450060915181007203852029100e0158800b8514a900203e0300f052083e00d60901600c15841a04c2000c010300440c0009294140174151480c1280d6a5a03298030100d000042e01d020602c501381c0c0f00ca40c0c555281e0742d86144c0380740280140b0001e5030003040c4c1142d4404850700c104c00228000101001990005030800c07015030f40d10040f0b14074841003800c2c05c800040144c8000f82d403518001c446e551071186402d00116809078010b10040c4114030042030700c42d050700ca6000541361480501803c400003443c100043c0b0003800c094003d5a00101d56080070909084000580b40d202101103480c0c1c0e00560140d040d2901a0204100c00c19048110480003440c1144140c030a0030300c41e1440c01071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 40200418 1250 40199168 40199171
    0x120314070818030f030f070207081906020904020c0c0102060a2c01020906030a0c0305010e040b1f0911030613020717030916080a020f030d02100902120102071203050c0304020112 78
    0x1410700c04a101d4124500c004030b0060301c0e0345034400c0b000500240c200b90f41c000c41c0c03032a5407400240c03003500001ea1003095503081b000420100c00708485180600c0c6540004855a42c2c09008201154a45001400090348080050a90842504002071030048010f04651a181c1081c0341e20075964507050220342c2100d00d106030180a4007040b0412b034064840c00c600160484000010402c400009600c0200d0440f16070b541848581d9030f5250044445605840c06000650101d001c40d0140b5201503c0340810819441c03420000e030790b90846d850491300c018000da005000d000041000c2803401502903482e00c03100d140e0850030180f00e5201c0801c01f042c00c0000ca040c41c0000000300b4070403042040b03130414a9131b85590b200703801d940340c80b400364032004423420490080c1d21040c00d080c40c42c40c000c00d0411501c5460707802408056944202d06001d03001800d400e0741c11159101950105c07010a0004003d0710780901d122036207000020303000504840300103102c03220040b400e00034880140c0e4040080c000104000700c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 40201668 1250 40200418 40200421
    0x230040303050d0b190905010b030103120804030905030f03070c0504090302120703031404060209011b020f04091707120f11030904051f03050705040b090105032e0f06031203140708 79
    0x2590000d201e099000c56001705225240c00c151084900c108007a2407a1303e4007800581d984019a4140703000a0000401211070000f01c655807034443c141c4903031300602a240030500720f55a1400f00b4208a22211412a41d030400165902032103081b880b11401010242e4003048200040d4800944603c2002c0741009000000250b0009051090300607114000210640c1003081c1868a0080700a6220b0f42440f808a04001d40468862070702110f0f941d17500e80c01a1040494803404c0d02000006c1c190030008540c4000c0d204481e01c4000580c1d0040d100451048500300058800c0c0100500481c5002c3e01000402030404111040d1007808401d032102c5010998002c5140e855181d4100f10643c0400c0c401801c04161000c0007041c01000500401180d40c141ea0400014100c0d50500c0040c2e4000d009458165000400b1741a1038200014400f4a803400e824245080719880c08400e800c1d20220b0300781c0003215883d082c091041c4000c2021510031054241010003202c0b050300203c0c05403600003404281801086d80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 40202918 1250 40201668 40201687
    0x6290307140a0314010e04110402030903040b0c06090f030c120a0908010c03051f080a080306030a020d0c05030709020403210210020d090b01050a06080114010e0a06023004030305 78
    0x111210880400900712074582904a000800030055040e101c1e40d015904000011201c002d400103500454112125200040001003480080d62000d00001041e10041000159a40224000d80103084042300546041e0801c0301e42140792080b0b0040c4241c039a0002c00440d60740101c00039221500c840100038143d00d41104050988010a050340f003011503500f04100208019450b5001500c41c5208080403021300007092800051005223014000142d4003a04400002c02c010f0809140d0090009003155000c02d40c65001c42c0340301c82c13501c00445179a5003c2d042440145000c0c07142c2e001804540d903045050074550303260078420001c10f4450100b02c541c00c1404100d194802d00070700c3c0801d46071000556640441580c48001050204d100340c44800b4110300100d49458007035800d80440b500b40d82c0b8407260b030b401c200e54040354000800e26107051111602c030340407440d112100d068005002a401809030307040c81501000b11a4850090b82249115641401c00e002c44048251000d807905490215140c41d95034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 40204168 1250 40202918 40202927
    0x60b0301081b150301080a061505010203120603010209121c0201051027021308100b060f0a0509090a05070e0306090601170f15070f0206070f03020702031005150406290307 75
    0x780c3c83c1c1680d90030000c00410030840008000207014407880042040303240070101302443ca002401410b005030410004e41e250001059040c0780c01c400020001490300c901c030000200340003807041c1c4084180c1c00280c802d245030300c15903c003c00350800c240000d10543c034041c00103034645812130040c0f00c440b11401080e0728680d107983c500c40c3d42c04a07075128110754483d01b014000030023080d1031060000601c42c403842c500d030b031070344a01031076203900d101030035542c14544964110031141d0840c00c0100100541440102c5607651100b01c1c83e4060301c0008000a403906212200800700030035058054001c0d800383c414081401c500140d4541150344001181400409425165040541c0ba00c3c9440303152041c29500380800f0302203000c0a003d1980380d22100d120422124090340ca03120704407510008101a106902d030918001e070020b001c4940b0050a071030810310313000c10250890300241c072224003041c2d1000070303452141014840c1344058a954518000304c0f06000f806080c1014481d04030501c41c410120100d81064050b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 40205418 1250 40204168 40204189
    0x1120c030207200312091008070c05070303121404020d0209060d0b1509060109030c181d010603030306090e0705040e031209100c0f0c0611040b040902030109060b0301081b 75
    0x1d04103450b1903030302e400004084803002180030300c24021440413150840c2008110342e0186c0d0003802e0302141c05410304055508440040200301401b44080340000003800500480300079510a88601c800c60805010a0084401710400d035940003202405200c00341e5148810540110360450f50b0194660f1045c020490b00c2c0d60b104001000c1d0400c0b0800d000d4800017071070307142111000031381d015030349a521140111541780c0d0611001c1c0c4020300b0070301c0501c040d000080303d641404050380740c00b0980161a0b445010f01840d40000c3c000607075034036181401003543c14003c0314010002761000f0f1041d01e95100e41151107500c03038460301d803250355030742840303201804103100780c8040a403006e504038440e20300b22070404d03214181c010000d0010780c540080c41e443c8900400c00c400c0301322241d540d00943d400040d0b0b5503000900b42403869403004c0000307100000f06030750904024009801c94100258985d4540740c0150141e80c03d07608030314640701e020700051014140000f01040b0420242e88070034615115440484c21345c025 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 40206668 1250 40205418 40205423
    0x403031433011b080301080c0102030310030b0903090a09050601030f02180904020a0918050c0604030b0112020a030b160314060906150f04030809030c1816030f0c0207030506070e01120c030207 84
    0x101083c0c0c0180315012001e9412030340c242c404d5940c04080000120f86a110031200c00141500b8040c0500110308a00e4070650f010314110103c03440d01d9111400581214000c0e4050500d00da15a8100121540c1c540921642c000c40e07413109504080c800d0b00e00c2c1d44800d0381116400d004502910018042d95203840c540001000195000c02070144041030071807540e049000c00352000d20440201032603508186040340c0480350403500d030005070f03400e01a00d4820204080d8051740e1150008001001280600c90458010742d45042d5003d5403610340303100903041c1c0b00c1c008a03031320050601004110b81ca80b5907004595001c20120b034881c0d55401b4130180c81580d80100710101450100108002c0100500c9600404002e5000c804884540d03440108000241d4162000d0341d10a51450000c18880c8015116000d030904407030a0100b40b07000d400b00382504032104460b0500059222840030800d020f0180306460300312910b886e00f00d2005005500191802e04403400c00224075503a0003c500c40d09201c0e5040c0e500c12236 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 40207918 1250 40206668 40206707
    0xd0216080c010c09060804050a0311100c0206090c01020102030412081003080a030501170309100305060402040302090903211b0a051c05090d0509090a050601030b0306040303143301 79
    0x140c0001c101d9000b840400016404103c94041c08510903002c0d42c9034a01c99075100009291103240c640c1c0c100d0380215501c040b54541e100380490380184001502903100072001a50007491246490b00003185070401d05240c03d030641e4410410322000c80d100060b0f000102d200c2e0b0406480c5609da0030620364070001d40e41e0001e400a0004144038000316496001381d8125964500265003c640d81e00300d20385c503407182950259002250400c0e4046544c043d0308080ea20950081006003030a50302d070042142d4003030842d0700c20071503000001d1a480800105d00c0c01c5460415041d1240d00500d071511410301d1198001c0f00348454428041642005144184c0884040044880308402200c0200d81d56102901007580c00f01c101e03001c0c011180070214414001c0c1c408400008080380c0e502e8581604940003840c024110302d04054603084600307420b403010802140203d1090360009407034078020340d4214103820b0141040341000040301c410003030381909090301c03540400c2c103598000c418500c030701c016660189500384802d030a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 40209168 1250 40207918 40207927
    0x5060102150406020a0f14070f02040b030307060501051c050a030e030304030606171c051b0a050f03120619090203100f09020702120a0803010b0a02150f04050c01080c0d021608 77
    0xb00080c4c0103009240e500d6100e2810410b403081c0c007505e02405460703800c5c03110281401401c0c08110407000040c1002e0020f00001103280f82000030071304561105000b0b580072616180100050300300041d094118045510007601142840e45c1c565403500e500890217400c01100d20358503c1c1941e0140f0840b8011503024608120391aa02e200320380f0f11443c90380c5484514007071030b10907140e14000c40500306001d0034207030744041c6406001151107001010b400360b0591503105164081002030300800582142154840055890741d0124007411260000102140d00950510b04201d4603203010307001d49170548205002c0507132640e482117546803100c19113600c401c5600410700c80010781c601d40c60b802481510f00a0394042c410341c2c40548502e5031000f80e01d40003860b480041004220740e00e5104042c010406c0d80d8810b941500d0b0f40402c191890300710980c2c10844a02281040c402008000c005000c0c2207402801e00c10701d03624000d0b01e50001406103130b44961107d6000100c0320031040d0065401141654420760080d140e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 40210418 1250 40209168 40209173
    0x9041202190c06020d02010501031104020a0509060708130b070c03060e0c191715010611032b05090f0a06020901091d07082401030b0a05040504062715050601021504 72
    0x5120b40703100c0d10000d800340d420b10381803151041c0245c1d81030ba43c000c10041c50b0384008000380310080d80110051001c12405102d81d01642d035070708004010180c040c1803503a1b06c9619a501c194060300682c0d00600035400d08220000004404040306c0d030403240c110000007400070542c004c440c00c1180401d800ca903c550b100c60b901079400003084406e0280d03905015032511090303020300c0444d42d42c4510701c690302014491000400255201d04032030050701608000307030384c02c0c01003003100d0a60311503550480c407503002602100c049442080d8407481d80e100d5100001000822500740705640c480902e10f0028090540010b51803069034000d80300240146440107a04040c92401c0c06074424940007541e88070300299500000c170f1142401c42c2c40303084030008825481102007803c1070041d40281009552a50000398003200015540d4544c4901d80c41503014a0010032220110807038800c84a280c0c00c00c000d800300c10405100003240241c140c00308400daa5000000d2280c640c240180c0c5420b0401208010f044001c81c2000f04 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 40211668 1250 40210418 40210433
    0x708010315020405011e0302040b03090714010f050d1d07080307050c0306090d08070201060e09160e010f0306090606050405040804060e09010605030703021303210e09060904120219 79
    0x490307020300240e1800c001c40025441c1030b03200703a00c40c0c0c900080700991084a5040c1044142184007080d0400501e400d0b5203004001103504200c5498581d90071101003044610700d40e400900f83d4030001d10380150120403d00c40600b160007007031700c3c020040703036540002c1522503241c2441c6100590204101c030358803507544503456a03e900c0b200c01102c10340640d1402211509000580e04c0c01541c1003006010702c84c0d001a0200c400700c000600c90000c5640b10400021040d21858460703005084000c040c004050b0440c40b0308594901c1c6038048224662450010040c90017460240c00550360f100c103000c168461541030400142c903440d00525840380c0307070009010030022000014000c86d005516551103403004d00b03003000b441038400d1040c3c90214030104006595540311b0341c001c10360802241415000d00d5102e03103500801160140c00700c0083c142d0000303412000f9800210307003070081400300c8450070146481c1d808209001c03c00b0f4801450800040760b24150305000740648105e0268905900f040e03948142840b01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 40212918 1250 40211668 40211671
    0x270a080f030a060b0c1e0a030c14010204030c0609031a090606010c05010b03030d05011e0803070305070501150305100f15030f03090306050a0504020a06020105071d15040e0a0e03040e0f10030b0708 86
    0x110343d14284445100380800200d240e5407c60303099218800044542d4641114450781d100e00d2640301d550811000c00000c81100701e0b400540502d542d08841c03541949040d41070008010f942851041c0c50b00e08000d0132040000d13030344d680f290b020f282c600c900604503e02907000d0a40c012101c1d074907000101e403916802c80190f1025040b030300298110b06001595002043c101c4150f8003038035601d9081085100b010034055801400d809110f1000050088a000e0103a01c9081c5140c00071a160b8020301e10540088445010744803a0204280c070420152841c00001c40d4250018803004285000d050126000c2c907000702a08402140c00c540c060003149001e004847c01070908450491007181c3c0514041a560310510034684224000e40700d40d218000080f440d151801d240d00311446c0c1c07244006410b10002c80203a8050700081512140064440c200989034006a0f08004810b0455a005000410005a01c041240d4222402e415001c980e51074403d0200013200782c80c0c1000c0e104001c88024010500d0384500d005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 40214168 1250 40212918 40212943
    0x51e010b010c12050708070b070c0c0812040504090302010b09040602070302240f06060f0c01060302030609160b0306010306050d0803070905010513050f060c06270a080f030a060b0c 79
    0xc00000c5611401501c0c80002c2d204003900410960764040409070080c2e0044c51950b008105107810300c00117544840c08a44215441c0001892601001c0c1c01c10280c0300b803003006801144046c00c219940d140c0c600c00b20b030082d071061501c1980c07900340e5203081c18003e500800340070350007810070089840c003402d003400a035018a03c00c5005101308001001c1c00321020052100000014520303811035119481d01c10702c0c43e08040c1000e54030170b4041058988841c000d1004003e282d0340b034030010035a40d16500405060000080450009400140c8414051031040320300344140c1c2e4809c52034a440e900e52000480081541c1d400164005c4d00d0f00150605014450b0091481200180e54015a0035266001120140039100c140103011032030500500c09440d210005078510303400546a2070502c800504400c6c940071040d981d442e6840011201420a0412007201d008100030031f8000303102540042d9201c42661244020210809501001181c8100c4168202200408280120036103503003086145507100c0d89106083c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 40215418 1250 40214168 40214171
    0x60711190611120f030720070f03140a0807020d03090812030414010c020c0d020d02150c120c0304060f020a0f0302060108250302040203040f060609020d0506121e0307051e01 76
    0xc40800c1d0701a0701311021450788402c00c0c0d041d625110429100c541001082405159841c8090b0880a40422002008048240080d202e951641c200305040d1440d01e03800b646140c2058218001040f020411103190a6054410b14144001403c04071841c0c1e030903410400f0399003d4480d00b080301c9502d0b60701460080b40038031100c001c00700200300c010f400c0740c414000c0d582c05a040b0382419609481e090052a034582d001508070034240600ea800500b8910103008022094071000c12400b04016040000b1221210004041481d01c020b00d00c03155a81e00032071080004202541d041001014401c1c4035403007196030700c0308900842da03400385000794561009004040c168441c0760411191018003110b1401d82f501703a42e10041c0702c1400c54007484080e50000f401500c00b081044004000180c20b40721f85402468440c00046c0c580c00381c50190710607210098070482c842c42d00240b64108008012800010f5280c6075060500000d10000e100707811401600001b9009000c1c2061280c0548100c503400050342142e10300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 40216668 1250 40215418 40215433
    0x303021216020601270603050a0c120c0302091803031006021b0d060209010c050d030203100603110306040b1903050106050910060f0f03060506040801141005060711190611 75
    0x11503140c00d4181e1030760000590110b40104082c100051070b6002000e04865000c1281c1100c00c900c02c10348090f644100d845a02585070701c0240490140940007500421b030303c0c684020450b4641d40c040c141c1a000207885080e20701d0216005800b08a880c5600c00c0004090f00d403a4900851b40203030040e801d20441001d4040d100100c6102c255a92a10005200080081c07010030210b446078002900140e0304035052100816005012460803c003032080c0c041103039000360390b9282002d05001815201d61048040c103007404020301400034110107582d40b1403000c0c0d41c00101000b40d0700001d000c406089044508141c4040008000d20a040d04400103a81d0161500d4040362179170700c510b014189440c401d600000c2c030344158480c5131903c00c0801c518604640d2901280140c1c83e040010020f9100d0340c465a0903a550346448480d5500c1144044d5124602403c00d10b032003807418001c6461072198900c000e000b810781c2000c2c10020398a0f10a2502100080d000d601c0e89291500d5000e000d8004034200000303684103524 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 40217918 1250 40216668 40216681
    0x4170d09030e04050603072612030414010605041104030204050709030b0a060501030e0318240f09010e0102070f06050a0314090a1e020d08030406021c05011d0408040b09030a0b0403030212 82
    0x1f51001115441103200f42c03c410301c0031a249985550071404400350203022400941400454060340c001d40c0030302c0c450001c3c0550302c600c00e1301b102c01da603100c180218103210400340c1484a61041d1000c4075015940440c60303503250300c8101d0701507406400091000e0f032084c0501905000d150700c044107840e02038904100314101041c00960b280124a01c0c4c414014203d600684141003407a049048008450007604021303a2140214a0360703000380101945010000c1411042ca607841000e40754580404c0c00600050390803c15038001145075801094248080060300b001220b00c00d50003501c0081005104016a0070000d55654440e02c121030706580b5120244220300a0b901c0c140c0d00c20700c52590003450640c1c6d00d81265980182904000c0042d54030650030b1044071080288505507280e1070380101e10010b060b41c1020201781c501011560b5920070307204c1c0d0b08204030004e0003003800c0b9410342e40101002c1d5155249100064902050b503000146810315000c10701c02010f4241e000b502c14050204c5d04004c0c25607900 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 40219168 1250 40217918 40217923
    0x30210111204170c0a0506100b0909071107051207050405010506030903070f060e03070506010e011a0d0b0307080706020610170a02040f02210f070504080604170d09030e04050603 78
    0x1d540301c01d4011100c030108001a40c20440340d0f4032028103442c99401d0500c40c210003824295200710540f501d0b08003a0401a40c894204040c80240040c0d982241c108104600818200c0c940185401c05010700820288483d110130800a801030900401c3c080125034a01d0005860b45500c2c400d60740240e09140000c0ba1914014050320320407040c18004600340115600c56890622048009031030503075590b100c403521107030140020040d05000310700500055241c030b080002c10800c140d00c1945036880849004c5e200d88a078100b103642d101d06400c4082580c921003c0001c0c01c100081d8450161485500342c0026066004100310744039036042002c01542c95038801402581105041841010b030704114051801444c1c00d80c000c0c26100c80501c00103082c40c0c10b4045107115500303560102d54651818604006080200c079407041d501600c0340c80d001d420a450031410746e40d00c02003c0c000801d920140c2d40c04c0250102482c0030394101600698080c003080070030b81005404540c0483c00e10303000d03504100002e4544d0500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 40220418 1250 40219168 40219177
    0xb010504110703031a0a090207050c0301110714030f0c0708060106030c05030403030c09030c080109050609070303020606060d0e030307030204031a09030a0302090628081e0105090a0b040903021011 86
    0x1e407001d80c9050100e540480090081c1281c0b0004060360b4001c900c0306440f00010b0b50098005007030016500d001e1410300529000000301458400c0c0e0410f0b50048240f18040241c9014a501c03016000c00c4030342c11081d050035806120010711b0b6030000480c5044c80d0b02d00000303c40040301c070030038151607059885000c21819285428429000701d1010400305001a10035030108450b0402490040151901d03562400c01d501c00340d80c005561691924424000d10900303019450b00f0140f2000200400c0307286940c041d480c0d0200a04040c1710740c00102d808219404540c001700032000b001807d41c1d9491a00f41005402500301e808192074008004c11911000011800c405005a8010004500b4000803480440c003035444852040e42100081c04400c0240741c50207030a01040c1189031072049025105140145103500003000b6010000720b0002603200140c00ba40c131181540d0f0f0564001c42a42d542c131b0024005000548480d83d0018907090141c0e081c5035000c0b402c0c0c0c0c1c4040380c22005101f00d2424955250b0107028 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 40221668 1250 40220418 40220441
    0x1704020603011a07020d030e0312031303030b03120309151305100b0f040f02180307060c020108071b05070807080c15070609020310060503010b0a14090702011107030302070b010504 79
    0x303003000140020007481190107002c000c03d0785100c0c6802c0035580032910401c03c03510304801003100c10500740c0e41c41c50203000164502031044405800e502d003109211822040440029041c16540e1000007840e031410710416580101c3ca041c000e540e07003841c90301141d8501442641c6205620210040341d50fa080c10410714000d05e4102c0001d0041000c6540950000c1c401007049550080c5100d40401c0c00e40c50b58001c1082c6004480030040c1c461202000158101d0b0189290350b02ca030701f0101c020711569401c40201345140780c083ca490011039403505000e4509062091642c007480c5615200e034410400d0000d03100c1c040c1c2e4500d4041d86c2d1040e9a6845580e076503400c6010895100910180b014082d01d5100080d040c5240915004203032002182c010030700309202074480070000c0307031030314000e0265040c01d01807207030101d40544400d407010745000c00380f010415407a0403141c4030341050781c0030465030b03807007500300c0d0f104100e21244031551450305103009070083d840000101c50103048c8000001e05441c1038480c2d801001c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 40222918 1250 40221668 40221679
    0xe060306071107080a03081006180b0d090804080604030e0402041d090703060c0513060921020d08030a090b0901051303050c0f0607090303110c010518040b040504080703170402 77
    0x31203000c400d6503944600b100600c142c0c0f01d40340380010030b0081005014400c41c040e80340c1c55050b041010030034000d80d10721340240d0107205000030303c04130618081824004540301e030000c6907164004010400080c0c0b030f0202c0060040c0c02d0100b0f0100340c5e4800850030a000f50b01c2030b116500102c4200c4d050006038041c51040d540300700d8801daa4040c2c08000000aa80d00c0784003c000d0300d0840c1d0303e9a840078201c6101036034000001c1d1003c101c2007040f10072800d500707001d0010b0741080c08001d80341000c2800400446645185030540d40c40e203040841d00c6000050b9007103540079421075100d150010340580100618101902d40019071004900c802d241841000d002c0c002088038540860025103003940e159100b411003582901c2100192913100f88180005401030b1056a6190111490b40c1001007200c0401111400706800540b00d110042e0f80004c100c503040700401708000402c0c00054006401405c03041c0640d03401c941800100010492000b0048c0803185c400d8a035945030300c0500840c0c80070108101c03402034014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 40224168 1250 40222918 40222921
    0xa0e090103020901050f01020f01020406090608010801110d0908070b070503070315140603040503071a0610030b0a05010e12010f05040515010303080a05040c0b0c28050a060e0102040b120603070e060306 88
    0xc6c00e00c258443c0c04614180101c90b44140300b0200103003240d02544c04500041c0d0320f01c600740405030744445858018203c81000b4405880980003442c92482030782d07003000806a82c1c091a40411440030300703880900350800d281d9011481c1c18a400b4140350300840d0310f603001901d800c94003031043d864250301205440340c00400010151400d4284520f550000d44103881910050100c0000140200d02850156411044c0a596420700d41b040c000304490302041030b0181424940204170948420b055030084480c2440c0460444002030302040194941040703c0c2c800b94205280c044440e8060380059015500c5007046035190003025020018104007800010006030403100031480c00009500a55002401003000300091540e4072890006607000c400500039940241c508151044851303100c0150417a4803001c0306d90088140d0742d455440c0c50280000404480d6070710100c020740b82c0f0035415203025249050341543d560b41001c1199810384412036010b0701c81c0c86607003000b0071040c10000d620f03401601d001c0d0051050b07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 40225418 1250 40224168 40224179
    0x91e03301d040b0a1707090f0b030c09040201120612021005041203180b0301060305041103011b05070602160804090608010b0a03060c030e01050a0b09010b070c03120e03120a0e090103020901 83
    0x10300350100c54961301500c1444089208441710811451800300a0000e0400e07034900061a000c0d01c0306601518240c5103850400b0445884c0801c10324042a82204e08020607981d600c010790b101c9181d0101981c807603142500200d001e94024201e802c0d05402251071011808460004403003611941c0100c012210041d11010002070055051411115181d01074081c17141c0c454043c0d002c01e800981c00000013a850305c040c00184410089440030702c200c1580288110250400d1003c885c0c001c2d41907080030400009007400c180701003071741034420114100019510402050a252006070094060002568034200c000a00c1d0001446005911540a03080d45030180c81c5407620b000030b01400b2541001c0c5921051041000142841060b10440358400002218054102449207640c6e0580107400e20b40b0040103540045003000707105100300c4e94042c410900540c0b610340122264415170480d41c0d0140300b039110b407c1c12402d5440180811100f69074841030551042010043d81c003400380700c06500f04c01140c00500a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 40226668 1250 40225418 40225421
    0x408120307050d050408032203140d0603051e07060201020a0914010302070203010c0504141210022805070b060915040f0204050d0b01030303050115091e03301d04 71
    0x80c001e1450400e03a0610110b0300011040da40100d60840303c044000040003002e020314549886240240e1b00d100007980b00c96034014100c0041c1d10600c030b154203030208499080745001c2d003148000d180d000090306c0d03008501082844000715001c282602c140503814011800b980f051095030404004c07642d818861300e190000c60150f882101c00c2e00744c1095001c10600c40543c80900400c00200781c2666642d5589103400100c0c1c000c02c1c05848540c1c401d40200103443c0140200007504154160f42c0c510040c1e4883c5000741e4011912031841040465100065113540901d82002c06003a440340981e0001c102a5908401c07c4000f041c1107175642c0c010100101c5252aa040c65802403a0108a4100051510340c44400080e907011100c4c0c17007122030b44c80b40d60040c020550b05025590041c2035021103480821402607024040b1a00c0d8002c5900d1407510203c0904410040105000190340000f2084000c2c0c04017040c0001d8040c5020444031140a00b400c9070b46d5062081a4035001e80030b000d820b81000340d403011304000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 40227918 1250 40226668 40226671
    0x1d041e032a0602030f0910020a05030114030f0703030203071101030504230c0307030c030204240306050901020f03040b070906021c0e130e0a12030b090103060f24140604081203 77
    0x8a005403114030302000901c0b51000b10300545520007100d41030718040528600c1c015505e0f00c90b02100740180605195190010243e03030569542a400480041c041c002191500d00c41c884031412621508400109168012000b401d0b21801a1010791014142900560a5034400d4030000e0010060780d4030000c00c3d11010000e024620b03000d0081c0c03103002070030390002880c0400302d030800d035614106581c04100b18549489010b5504610700c025a00078801c2c4014104400010710001e084136440d503000503981d100a50455810704a507222242c1c0300c1c2010701340f0003071030f4200300d500d000801c21b00a80815a140002110841c8009030080c0c1044408030390710449400d13195241e45500300d00c03412620100c00c0010300550640d0580303400204601403460504042a0981e40300ba072080c5441c09000d0f05213502c1d03604285041d00c1c0c0000c0003081c60b05003114820700038003c0011009903c2c0121800301003200c0f0640390f240450f003d1082410383d044240c4104041841503110321f8000d44d01c88103400c90840c08032000386 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 40229168 1250 40227918 40227977
    0x212150f04061502060a0b0a05190b12090609010902060901050702030c060301030f0c091b03090318030b07030605010503060a030201080403090f030303050f22020114041d041e03 78
    0x5086112400420256182c54220b88111418100d141083d20703130400040b5401000c0440a1000f000600d0110b44803a0b124003500b40641c64034140e144800d401c1c2003201000303040381c004041c1e07100004801001c01c09416182000300307005403800b0400d40101405000c42040d0010515803410491900664071a070141e407049826024080400003a541c07231704040d60017180070303c914154152191500700c140890301d0f005419654034000004040c4011b05060203150070081c1030000308026a42400d4800c3c0c03400b0b0fa506288403840260200c1006200307102c0030b000e880c01d0380303060000da51110010745d03141c001111800d8108028540c2040558480c0041941040c0039007030040f6020b40390081222074440c1500140c002c207442d481032240b084800348130720b035009182c401440481040c29107080c0380d80c15400da002c0c0c1004415080e4401c01040318080350001d1400c0311042d52007184505803040d548074112000d440c04001280014010810300d210303d03080c0c903407641e1030440a0207200da0b0741071090b8001079070 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 40230418 1250 40229168 40229179
    0x30e091005060f0d05010e01060207030201051c0f0f06080c0d080322050a05120c3a0206160e060a051608030103051c020714090c07020a0e0403030e01021215 69
    0x14240d02c5050041c80c4956034100f015030ba4103840d00c0f402041d2501030744612030341d41201004204141c1d01003590304c103503a070918042c3d1342d506628174100180704902082440d20b41c54140380b500c05e40c0300c95220540b00c01d40c1c6002070188560302e540700c948404852100c02e4119801c0900038000900c154011580900407100f4403524804015850086440307550341110543d020392000c038103100003045401c5080c0070130b107107a0b480c0540d031f2100d15031510420010b003902850195540c1006480303888401a40f22101800c200040c0d518003402991082c003518003d801c5110210480003040c0708079400c0150400180c10185041380c1170720201c42e2035100c01141c0c003000180000c840f00143c002c20055000354012401041c3c0d0764882814104012481c2c02c034502954441d807030030030001071444115035465001f22240c6900d581ca41020f80c00501c0b4041000f54001005400417880450000c51140910300035641000718500c0c096410b07080b44110312081c20444024000515040c1d150480c0d010011030207440c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 40231668 1250 40230418 40230451
    0xa1b1112030711010501050604050f090604110a091703030103020a030305160813080d020a0b130c051002010e1e0a0b2502011a0d0f120207080303070806010f0c030e09 73
    0x100401241c0058860304006042030001400101e0240a142e003d04802c40700249040e14002c0010050040c007091b07280175078034045c001502d6644581c0301201c0741240c00d00481c1c2c1d030784201e48000d018040900485134094001c0442a00001d800429641a00d0703005d091005002c0c10358606441a030451401550740c00800041100083c9410001d00b03585200c46003203141c84e0382000c00407824036036460070150440d400f1001040118596030080b0fa0011071100e01207203445c82d98100540501c520703400264010803408521800140e055101004850000d005d03600441c415140020b004070410303110900342e5124840354408110101100d45c1c010b03d24901044040000d82d4030410740e41031014038000940d569841c40342e011091445010303804d00e000c54507003501d070301295180003c0e07004180014168400c440c0c03142110a0003004128040c0c1040002c481c0c6034500303000000c01021003120745600041000141001303540c09001c81408041d0302d0f44508030001000301c14004100340c0105050350a015031030b03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 40232918 1250 40231668 40231693
    0x2312090708030706060510020312040213060e0907090e030a0c0605070509030f06040c05040e070b07080c03030405010603050d08090303070806190f0311030d020604080a0302041a090301050a1b11 85
    0x40c01c50f0b0340f081c400850300a01e08810003d488410a400500395081000301041034030404066036070084c1e040b1951888160520750b95002131426400650520346134005001c22842c00043c0841290781205042c480b500c208a40c491301e9008074280d5001141c124641d6400044440c7c001c158020001e00d40030742404049400649048510003000c034040e00302c44140010b2001d054030340000b03400e050750248120030002218582e150f80b9489070441003480864010b007081140c60807280c3e0341c02c3c03510840380c40c0e04260600c0fa00803e201c1c0f2048031907104110b00c3c8000140640310303242c0700701c803a05c0140d41980d40700201900c1da0300000300129171101d04070448101510414041501800d1030b40e4408540354254039000700c0717510070308080f02d10070b6000780c58500500c0e50004045900c40e40c859034494407541080c0c0c0c00d030060300603900b054148a17940c40d148201410b54801401001108800900072515050721107011280384000007e00b9a050b01c59000750b03940107a405c00c1111415000711a0b4031702858 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 40234168 1250 40232918 40232923
    0x3110304060c0906080613021602090c03150f060405040903120e07180212060d14030409020c16140d020621070212090603010e0405010213152312090708 67
    0x1103404660040d69140707406222984120100007401c424104081c881c2420400100d1001c8882c00b610941500040c40c00d8041413460301c80c0c0c042c281c1c090406505810004203183c0c0301d4004940704a01c2840c150500600c0c1e29120406001e51a4040d000078075050408040c8000381409100a43c14030014560720900c0014921500e41c0e1809550007400307840f41406583c0308084508081301c5d40b554018068452a0b1f05107100d4aa002078040303401c1c400c101f11303d144c0401e070540c0e4004901014080868000b840310078a80003000000d08000540c0d90501480d000e049030f440300e50246c07200444c4040d030343e01002d00348000032002280c002041a810000781444c0212544d006446113011036070b0000c24001896010407807640811b91360007100c1d0809011001080741c0f07010511070140d519180d031002c074090110030b6044455800b0f1140000b005d00362118181e1004803842e0381c40c080041c08000302c03e1540f04d60606160402511101030500d48030f84800341440f5a5400362001c03801d805140c8c0c0020706107504 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 40235418 1250 40234168 40234171
    0x5040504050c0919090b03060405100203091f020703030501120b060105090f06030112020102070b1801031a03010f050114060705060a0207050f0f06091002030702030313060b061c0c03060501020a060b01031103 91
    0x2a03142e44004c660600344400706440c1c0702c0e640745000e94051010300000501c00314a440010014410041c0c880e41c510f9041031400b26588036840900500400040980b090794004000302030290300c4c10700203641e030b960400403031110302070014100440c2400440c110358490001030441050051030b07014500900300008403540e00a912807440107503681400c5045580502002d00107289000115041c090011090b907204550f001c003550400d9920102c0b0130541031020644541044080c0003001000070448202c03005040c00e025032000b142c420750312059145803100c21240700355441809840c160301d500d522140603411102085440d4000d0480031080a49d00300620b5101c4075085c001010303141882c4881d0307810503030302101030a2400d004000f00000c0a0300081100c1d08003400310030300c080c0d001103401c006000300b201c060510741c4031000140c06200e4000c5105480e6003541c500104000800c04107006400700c1d5038070320a103809a0442282a80400d0450f401220180e0b410b0401203420103030014001b105500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 40236668 1250 40235418 40235449
    0x604081506060c100902012105070e060a1b080424030b06030114090901090510020901030b041b080c070c2310090b0705010204080a0302010605030d0201090305040504050c09 76
    0x1086200a010300080101240c0080055507958503121800041c07071345440da031100c050b84242d100c8041c00c007107910a903411041e100c201c003000100d0341c0c41e02008001402082d56984000b4003620071060003803038000e00315044c03165686c8079803840030400d00503c1001001c0b1181550102d00601c00041c42c00c035001203085c0c031a0481d8a80110010100074060111107000302001e004050a00043c13040e10399820802085500c12120041c0b036556000515024000c640c10050590243c080070400040c501c0d00500386000098030203001810810b0f0a100444400380781c05c0f99199141c498801c8250300640200d03400c91441031080e840c1208548030003d11142551001d007010051403009006083c050003040c404c0142140c03078441c09a4001c10081c50240c15014040004400080c2c084c1000300135030440740104101c070f0546020003045d0501900030440c0f4070a540c00303400303461200c07420b403881803213525142c2d6410f880e103030700301070400301400000c2c0002810542c4100c401c101e110314a1f03541182b40e603174041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 40237918 1250 40236668 40236673
    0x1091e06060306050913171c090308060a050301090c05012d050322020a03080a02030706090b060301050c120115030b090f0405010e0a0213020706060f030302031306050702060901140405060408 84
    0x24074000521a0150300145800d0006c50b6803400000041c038071034001c2c070307500c0444800d1580b02c1d04004480d80c1e060321540200040b4524114811080607000f043d554441c8400712224400c00750754105040c262403440200402c0017414041c01d010560207148542c12406080314000d112034000406035401200340c107204408180c0c04000c1008400c4981300c1100603003883c1100b103000070b180c3e80c040f0f014480d0034040141a100081a691503842c170070800d40d807005400081c10b00030440e840c20b080e894104152030013400782d405d000000d41029514022a0b901e244205409840b07070386020f1200007114a40e1040ac4200f58880d50488105c0e0b941d5480140100a10700700c4100c00d003400d01e4a6402c440128006004a422404c005005070340e62424610f8503000548001d40d513001d0a01d8150000d083e10340203220038984000c00032052603400006480813a07559005011459190030040d642c80c06442402075002804000da846903500c1203807408100798a64250900707282c0c030390002400304d8225401405859 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 40239168 1250 40237918 40237931
    0x50a0804170c030a081b09030a060b040f1503050c09070912021f02010b030c010906020d08040503070506010605030708090705090103060207110301060b0c0105010b03041a101805060f0108010b0301091e060603 91
    0x8002c2110900290040f60106e140340410240c086a22040703090b5010b4845136441d0120110764070b0703a410003500002000001c1040b034540d031902c200500b03880e0000f83e54610444a40d0b02d000d0400446150140e4850344400d500145409200111207501b01c80403a002420f00040e00d001d0740c0e100401d40f451080e6600086103491640082c03629000315062902e0401c80c0201e004c0008a801107184e150807803a82ca0540e071141d80d1030412034990f20441c08020250700c5101c0002400d07542c0b00c40038500499076540e40e201d40f502d480246c50303a1128940074040d070000d40c240040001a116a004185044c4140307801c0c1045001d520000e401c403591944182241600020400302401003031081901424600d1085411401c154541106200c0110301c403414100011000c542c16034035428035a4010050310203034203542511038105d04043d0400751416402881080003109142d0b0003054a07606a68120f8070b0343d81540c0c40c00a009029000c407104132990400310f1441180c1200050042c3c80142030241c8011560 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 40240418 1250 40239168 40239181
    0xa0504030e010305040803062701060203071505010311121e03040612051302040908040b03070302070c050301050f060f04390206010308090f010e0613090c050a0804170c030a08 77
    0x4600c1c12040315410149080104000108111b09480c2c022100703076694501c0309a000ca03100d844441100f08000190803403800003408660000080c9000752041d60300f0042c0c026020400c00540c0c00c01c3c00000d04c2c1c401000e20200043c00c080701080c980c90100006c0352805403551610780303415401c0c5e09001000c4d8200141c14000580c100d8031519095210400c100b00e646081503d10009802002c0001d201d15180c0385014240100142030b2005072940340b000310317a40e0824000140c025401004100d950b40c00301076000a080c90107205032071280203da543c400482d9030720020401c1d00040505843d502942e102401c20918000ea05003002078914542016030001e0554248900304040300c2285045622400051001400740c1090799015642500e01c00c100b020300100685007010311408813074000102161300940c6500e0b074a0390a007240e514100c2040000e40c0c800040390288500304088020a4658010030006078110340040074025808034064241041610040c3c1180c3c0641c001800040c07000003070000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 40241668 1250 40240418 40240427
    0x2010e12070303020d0c02150904090b0a0b19030503030a0f0f09050f0c0307050112051510030b040606030b060405120309040212010806070206010627030204110a030b0613030f14060a050403 83
    0x42e400c00c6050612010303043d1f6001410040000300d816503488800b050b461035070b8a03141c001c1000188d015009059616162110200030071800190512949403404202c01031041e10a654041d80d8001d0f020b91310350754907002c41c0b40c044d1010f010512001c0766030f900700040e102454414050f92502c41d1010784000690075449624000c4480c6005111ba00504000c00180c1e80200e640850000c1c4200080395565441d40f04208141d024503180f90840030340c0141c1d45581742d0503030103072210381700441e01000030f5510340e00124104c3d100d40624030340105007000140b001c0d182c4013101d00304041c00e90007182c1c40c041491010400341d8000341040703e010612f8100601600000b40505a03020071944010101585000e03001820003499181524010142f0303a0251010700300d0f03840d001c005c2c6070080e00c14000740d81110a001d440d6030181851200080c81c1c40400700b405c0c546401101e185a11b00382e49034040a083d41c80380c0039003044144080f524098a0200d44005000500c103541c40b60040a40c0046c1d50701c2d20b41000b41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 40242918 1250 40241668 40241683
    0x606030b0f030d091e0e04030806030105070315170f12070b01060e060f0a02210c010b010c020a0306020f071b03112d030c0d0501060611070303020d03020702010e1207030302 76
    0xa02c00e4105a4140001da0742c0b156640c011241e49201c0540014088007012149184642148005101c8001088141034004400d58020079044d00200b1413580c591780e086040301d50152280000c00c0590004100d410b4015000d03214002100b800d449415003c0c4004502d051405c1c81490000d84011860005011884816038010911414421049009003001800794403c40101c511800c2000c2041c4403d60701c20040034038066420441c030307a941c800c5c4485505040c0c1107180000c64540c20400e03240029486003080c113801c07960140420700c850b800d568924020750001e004600c25084140417150100c1d050340c94008048405a0081502600354103154880b003051007440f50103800b4009a45540e80304444100140f04800146690b0715240340000900f0000c4180c3e00300d6014021100010030b002c0c2c19403126044900c15210b090003407200191090f12091b1510010b000358000e41402c0750000e010b6001403101c80d20500d80b040c9400c80382800280c0c584503080c00c0301c0946d400040b06204140e010000348 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 40244168 1250 40242918 40242949
    0x2060c0a170114010906141c0b030105070201050a060f0501051605010b09040c05010207050a14090601030f0f0b10020d05040b09150c1015080a020d050a060504030206041703100b030907090606030b 86
    0x30303194200c030b95100425445140b2040d030103c60411100074230424143c0c007814805800400034020303402c14010090281406585071000035250101c0002c20090310741403282141e030180c644906000c50581b0700009048243d41c103a4039035486078108401a42d036010800d100e1803080c280c40410b28201400249486010b411040c0220513106080c08040100030201100d540100e480102c41d58413100128040e00100c61031140c3c040c10160050803c86d800c5e0480001250180d80c092965081104126924a0703d00d2203400487d408000078021400844010f100891014141100c40c10346180090000d510450f644010343d0040d9003031081008440c010300d010401003ca0101a141c28108041d03119400a1002407080b00e0844841c01001780600842e2241504600300f0021483c1c01d06019480386000c9030300b00e03440c0e1240d4594240004044007664000c45a070703220f200c05107050440045165001500a1095100d4030f940040c4004480c000d02024010036a00400c0040400040c0a03a07500494640c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 40245418 1250 40244168 40244177
    0x9090b0a050702160306020c0705040f02040302040b100503180c10030c0f0c022112040b07050f0a0309030605040f0c0f05190b030f06010c05060a1b0201050702060c0a170114010906 79
    0x4d505800041540b07095a8020400595590700000380d1490304000c1e5000341e401900f0010000c14201386640584200c0f0b0080d00c0a0040880e43e00401c03c0b0a030890080707001064061000c140211406c915206860903800f0031264855103c40010b85182030911100700020703100c0111484559005003080f1240701541490100c1d200d10340d000400490503100c0c603210001c034545800900620410120b881240498480b990352500d5020209095000f50800e98841c8642d540401e01d03264000740110640b80c15982d05450503055079180405050060419141c003940008010007141c0c2c2d442540000300b104c400ca561406281006110080044a0040d8904212a00100b0420302c0701c4040340c1e403240c60250103140381d45d90b04005850740d00d41c0800c007404510600301000302010080d4826a01c03a0500c0826049008070403c003242070700e07003c607080b90050f0860004500147c0e552005802c01d008507040c004d2080c601d622405c24025001da00025000400b940041a1543c02c01141d1001d40720a00c5c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 40246668 1250 40245418 40245433
    0xd14120313151e0e10020f0a032301140409050f0c030609030702010c510605130c0e0402070b0f01050d031d060904020d020304020405010b0a091a0409090b0a050702 72
    0x4150783c503071010307208030301d4540d2560074002044100340300a810b02e003041d00c001c54031820b60401000040c2c0115907048080307031420070f014035001c103c3c0c00011094080070540b09c0090307003424143c00305c0720300091074560000d40715141200002c001340711446a004424009000e05250b50b41014605071002c3d1810003240c0041040c1c070003603603101c203075030038501d400080051003400e05080391b040382d0a024005120071a20040c01085020351090104a04030004001d9031021104010110884d00b1070b01ca000d60107007100c0184c1e48160503540081c2901c206a00b49800480c030440c011800343da00116046401340c180a0400400c07035a07410000d405002c0c00d688454a1110550b07010b44215401d00c003800c44020070605209065850904480d54004007400540d00c03010603a5070030000e500240c1c0c00300e10a9007481c0012840061002c15102160816a11030001504d00904e0251020240d401c10480384010800452191024016410041e01c12402d140c00d40c0350601d4410120794000d008001107410111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 40247918 1250 40246668 40246691
    0x4150605070209060319030f09150c0b0403090314030d1404020f01180305070e07120905030a05070309030b0f01170a0b040201051c0e0607020115050d1412031315 71
    0x10a07286200c2e41070742c2914280d00d5500000c2e10f40013581c00840b5103200940486820103038044960a004038298585039841a201d00e0107200c100e004011600000c3d414601c4032022609407607c9940003030280c244030f20800d450f51a02044a00d0406200429070300010b540d664000052189007560644071801020a040c15400115030030b0ba81d0354040d040105400c0c40d654602c580d87d614400a650200c1140d00e2150781e4400c43c82d0199044a102002c2000c444214100b810f09010320108258000e01031480d051000c90242c650f904991300a504118002e103021001400d030f0520180150a11620440d103985016800010519003e18620036074204143ca800095800d509450308035031709007030064440310803120b4200002981c84a15000d00d081c45540f400c0c1200c003003201b034040d079085c2e0300034002040c45801e56034004049100c2e040d0088010403005001c624a05020076804145100781d0324000b1540e45560341c1500f0a49000c2454030382c2d1040d0310100483ea00003003952925190040c0144216107 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 40249168 1250 40247918 40247927
    0x4170d05100810061a0a120e0c0901051c030f05070c0b0c121206150f0307030b01020708070605031503030f0307080106080105090c090409030201150803030a05070905031209040207120e041506 84
    0x17800c18220360100403d4100d585805503a035040e03050074014041180d619240c04040d036401c40d200300c803800f5540d80400801c07a8141100150201e02c2408900209540903a800305c03a5a016404000200481444100006242d042c201c20040809502c4141c4580f080002c0500701202c144409242c8402080740c0101005105241a40302008550271010112403000c030080920911450340c140300e03400010007034419056070240c803503040282d0840e800640c603416083c1c1d81e02c85500880c070100b01d09000003481414000c401050142014058905100006a5a50981d04240c4d070100102e04041c0c0140b00440d44503850a004083c129011002030801c861000510310800386c08900541d2a0b01262040c103000b500183c0200c041403440f2400241d644200ea0740300c1e001902c0e5040014101004109498800d14541c029603a004003d40680a101600468554010b4405c40c3d04a5003c1c41003101044401e00582a015050b446000301d5001c40c0003040f04948400a0014540c0d0012106200c0035510 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 40250418 1250 40249168 40249199
    0x30d11040f090506010c02040e060901050f060f2202071203050c09090f040314030108070501080c03060a0b0a09080102030709050f030a05120f0d0c020a02030f06070804170d0510081006 81
    0xb07458000a454075100012912003201c0040690000e0424141d403402030b400041c55440b404985000f04030984410070710b001026015204242d1000503480310b0416071400704a270983c1c6903802c10030003a408049a1003074050386c001090940b1007010030100d84c501c1b5601806004d0303000941e0710409103403c0c8018001071040750060080720f80c1501800000c0c5c10580203501002901e001000d02079101d40e5030304143c0f9582d0304180111400100000d0200c0e003d00c0c10325060b05e0099034018480c203402c500b81800b150b80350f04580e00319820024040d80c0050085028070042d4014000d50b44d0340300300c0601304010b21502d0f19024040c24041d5001c07140310004560086407102c000764414070243c0d680d066088690703426014801d807915900740703000411212540c0008004011a100780c00356034ad591000c106480e00c1e203504a454a000c02c0445002600003600c1007414080c21380318418031781c00c001c9110902d8040303400881f50046079140d468014032a54404001000c80295080000c0c080981003903030350900c0c210b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 40251668 1250 40250418 40250429
    0x106020d0503070509040905030309120c07060807120c0c1103160e100b0309060a0e06010b0406030507050d0903020f070b0a0e0f0f09130b060604060816140c030d11040f 74
    0x1c0102c04140301c2442a0110360140d103004000b48407601041c03c10030b07140e074819500c0c1c80092195201c00076135581000d003560100d0000300d000e0200b01c0c0c82d041050320071010003807410b420084420880502c0040c94840c40b600000c7d40c2ea80c2c11180b820a00d00001c1c086c0c0c1842080780300382c2c480c120000c616601c0d00c4111040d9101215040d034151a003403000d01d0f8400d40ca42045102000200401894010020300603100724000081440003517070b40b85400e41c54140a000d0b02403c03490070030007401014080e410031604180341e45007661501e121008503d0440d4000c400490058105860382c41c582d0404000d80000380500006c0e103407a0842400300504948920079200b13001f81e180c50004201a618528061402e1030041d00c404414a8000f040c80c1407002c402e80110f81c0685610b011681c507041c1901070318192140c0b40c550000784d442d042d00b803241c2c1b850010702c03810130401d1201d072101ca03000c5041e01500728484c01d00015900ca070721144030501952520040f20101c0c51013403108003c4205520521001c0b681c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 40252918 1250 40251668 40251677
    0x1080c1c09080c0a110901051c0602090a0306020406030c0f0503070e011110050c07031d0d032f010e010e0a0203070e07020f010203010f080c0102060c0906090307050d050604020a0b030106020d 84
    0xc4181c03a0000150040c090940f02c40d0085044c0d840030322041c0d240038100034804841443c1e2130ba803600204802006011504040c10415200e40301c005102d56000340405040200707188091540c07641c5140c2641d101d034012100103500c6401212059400c01c01107600c003061801c00307a007107162800008282a00440c1c3c241e04000c0d00000d960040c12090060f100540e2408506108134a403520100c052503012100c201c00003441d001c107925225280c1a401d900d5400001c006060a125907181200c0d444c5051000000407910080c1a4001007008600c41717020400c1c0e4800810841c1c03501a07402c1c2110281d40c0c1200d0b054100441c1e003c010b94000c1a0181983c100000040094841c0c00d0120711304108180d000c12250b10002c00070400c5582003a04e101210103d204031000e0100c03e40049880c0e07041a030f45659089401e1002d100c640c40d10b900a060100300142c101ea01840d610800500000d4040b801998542c0050003848158105010a03402400003040c0766440c551602c80300964500c1040c03891b50810 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 40254168 1250 40252918 40252931
    0x30606040908070605010e19050106020d0309030e0909060703150806010312050c0a031e050a121a030304030f050d081506160f060e010b040e031b0705120102070201080c1c 75
    0x401224290f98016821980401c030942e100d40001c1d10307004041d910820b086101200000da1450350b4084d00d410b841c09a0301034900d00d8520103080e0050050790904900f448105000c8443c0d40d11017140c400e00c1041c400000704464142142c001d41207410a003015803030b0b801c0d540c03810b01202c0c41c000303140d80c112540440e80c10807024203c82c040b1201c1c01070b25900d0301c3c0c900405608000b495440303000390131103441400041081c891448025030361803240c81642ea000c19041d15401c58214183e40c040e03014042880300100180e02c0b2000081d003035a100790400c444000c60001e440091020030000e44181840e03e081c10401810f2014a6040742c038170101805100b00301c001400003e070301c9504038044070039500603e070602d06482450120701070640040180229840c2880c030b1112485c0134004d401c054010b038000b95181011000f50300700e42c405240040d005074030036003900203216201d01564040b080c03441000142c40b4140d610006040c03040241110741c10080500c81444010b940c49a030f0320681c821320740c00040c0c6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 40255418 1250 40254168 40254173
    0x1317090402130807030b070306080a0b0c04150302042301090b0315040617010f060612050421020a050c0105132603030709090501050d0305030c0a050403061e05060f0306060409 77
    0x81e10902c502061000007004000071040000160707041907a01c15008159a40c4e9000b400300c08540a80c81899441d030702410f40003000c100c603483c02ca60008060038034145070503102d86c2c40c907580d240340084400009900040800524500d045140c80b00a10881950040c641c0000000c29407000b500404154580000c007050702c01c1d00c00c00094050b0f01c00608144909640d444440510098288407001194207103a90100f08403039034070901055518680740e500103038042d46009c03c02071400502c1185c601c480464088103004d0300290303400000308183d0003040284000e14000d0b090280c400d003000d050040602c0341082422000d00d02c0d200f603e00300040007070501900c03402c210a514a000c0d0050300341c0400400d02044070760142200e01034442d115424402c0781d07a42c0080c803031404020800500055401e00105030305c140010010700a00d05c181c60068203003510382d1036071400c032824a400b01c0920a0760389022460405d050080d2513124400b1200d82d07041445010100e600d400d0010101032282d9500c81c0c10604 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 40256668 1250 40255418 40255421
    0x90e1b030c090405010b0d150303120c1803050d0908070506070303020f0913150e01030b0703090507030c060504090f05190e01090b0a060603060503030708190903050109110913170904 80
    0x101c100030f00074089541d4070b4410200030360090f100c10070094100803000c0400012101c0c4c001c101c0307070300d581e4406800d03681040e28001050071225610030404088607201d00544000f41f4640a50702501c0a8400305d82d003030300054030982040d8050806900b01c0c56080200346d4405040d01e00443c1c0608015903a000c11384445801c0d80b085052269005440d00c5c401c0706101030703950241c01c0303111000354072104950300d58810b00e0350504244002400600031000240009100f038005c1d480003442070084801d020f450751f9410340250525049500001da020034108801266402084242d503005003081000342413204810740c00c130795840b814014664861503a10607008013540400001d41d040581c0c0c44c450304215440d4005001d0034407031080003900706a03010a441c90044101da04030b5a1100f004d0340340c201000e40440c001d80c0c045c00200c0c144050340d440080030501c02e004081016200e800c1002c00721580208100700d02c80098810483c20321000d01480000b15207003022180302c1d58080d0102d80750b40c104e400040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 40257918 1250 40256668 40256677
    0x40f12050c010f0f1a0d080d0e120d050f0f070f090b0a1205090303060904060c0905090c07030807020d021b190e04050c040203041703090c0a060c03090e1b030c 70
    0x1c20540c60501d108150044130350004045600048003807000c0c582c1420307140c00c0e007000f607400c1c0c0c0d03402001119200300042c1c9010090003014000f000103c1c41d0701c2d000140500707011007241514490100004d55000a504a110321a84182201d0050380203003032400035003004600041500c82808203103411002c540c4c0c0140143d200806440741d055540784c600075001018050041c0d20804054103110104240c0d050100a0b00d10039080070341020380329910707901c60740c0140c41c404e81c280c003d0102418010030780703446a4488520072500b494030203994200619004103c100c000700680210b42060748010710247e80414048071f0b01640500c16859903a4545c001038840380600c1c09103501460658000907440d1001031520700c0b503801902900c201c102c001c000d00060b44021500202100c140108490b1507040e100b0103160807a104004482004070400085100541190400c07404102207201c4401019404590340d0701401c000c5c0c031200c03020b0400713440121809044900c0c1040c070074008000a07210ba180c02003500d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 40259168 1250 40257918 40257937
    0x31b030c03050c071707030506180a02190e010b03010510030c080c0a0318240515100201140114030f01020c0c0405060d05070e241f030b03031201060806010206040f1205 74
    0xb600d217014010400c50341c034000c5220882d00782c00341d0000101c0c0c14003040d1440b02d55004410184c12400c00d16400c01c807034640d85521800120032840000b00f000d413162040107000c0c01800000c66620b5040c00d0400520031840c0300350500700760604140c42c1303120b035001b00d880f0b03001b00210320320766101c00c2110010380141202040e20411840444109400d12610684083e040d40e00c041200451700c801c0b162480903035908031030781d8004024010182c42035060034004581a103001d480001044c0c214884d4587c0454030a910440d90080031815078001c5e450709000320406503040c2d10003149050311290007592600d180200d500d1003030359954001411364a64401e4099440e502405a42899481d540b9074500c0d180199010400c003000003880300360141c1d1704000188102001031003288204035011040411f025031503e984200b58450b2600040c03130300c1c200060440e84202c00d200c1c42c1e0660500c0b500812080c4001c1000c0d0440d4007000c03c0c0004150214090740c02c080d04544510300380d640f48501a5010f1180c0c5011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 40260418 1250 40259168 40259189
    0x1203161104020c060f042315040c080a06060305010c020304030c090b010507120804030206060d020d0b060312070803011a0f0a080402030c0a0905061201110901050d090c0e0103031b030c03050c07 85
    0x400c0002501c16031941d00c540d100d8000c503c5c012070442d1403200f103900d400700b0541041d0b01200f840e1200c8030681207230541c0248a24040b558a40d20303000403504086981c0e008075803498039a8010310804c030080c020040891810701c011401d003031441c2c40391001c25046202e0b80813850b5035144014680d034031071012115034a8000d640010758502c600001020b100040303609130b0040c040c500100301107151840c1c40f608002d80040c414400101d0b5a12840040903019043c5c6616200b100440c1d4512004500500710090003080b40e10389039803500418044103950395a218913064410801c058195885105541203640c80c0c3c41d1008180c0e45500c0403928240c00c04891a40c42001e116001a5039209500814032455081d60000d0181d80b43e50300350b80c01d0b124144900742c821074040c800702010354072510240c4140400d00001080340f5101c0d0300d40b903000b1075540d0000c00000980da0018000c0c1908440801c0303800c080ea60881150240c0c0352030003811109040d9000f010000000f500842c2017800b040820041d12a2510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 40261668 1250 40260418 40260421
    0xb0405010e040b01090209010f08270a0605100f12030309060203010905010837020d0b04080306090c04030c0902090409050106090605010f050301050d080f04030b01090b1203161104020c06 82
    0x1c20a10000d0100d80488034900500c0012403c1c085500a0722078900040e11844541e01c0326000546195030000d145080860220000720000e140c0690700070702d140b900e0300244c5445c034032904000064960090500355145500c03202044107402e41c0103910100e034030130105181d6500203882c045000e4a0307480e8018000f580040002b09030780f0b041d5803005040740c00321802c0356000c0600c0e180c0c80301003081100c40b001035170103400001d09281c195074002c040854030003440b8805885d019030b00e03030084c55429102034030f19a101104020312401d01c161115000b81c2c0b18440581403030303e16a01c03101054480d008201d03e080c0c000c200d030075498607503401210005a00000900c001507c580b04000180701610440780001c8072400340a03040e5001d00c00310307810b80303a020700700341d0010b9060345910105a1119028440e0f210701000004041010001e03464040c1c400800007041018404040004000154000d41031076002000f100c60449050000c000015500c018494040b4040f200094001e000f8111040624000c880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 40262918 1250 40261668 40261679
    0x902040f050f030d080109020a14070501060501080f0f0a0f090f110301050601050702030a020d111f0216060206070804050c06040b090406080a021c0c03140c0a09020306030c0d060b040501 82
    0x248110151881540da020400e040c80c41019500c41040c0702c6100882e00100040c0131f0200190000e1103004150f00f441001c10b51b0303c544281c110343c0491030a231240e03551400d0038040d940c0d100796255084070f803040d0303c4000ccd4100015048007404010b0082c0d00641c6d40c403038100c900510541c002c0070300d1981143d12010404104d0030b100600c80c3c60540d07140d100c0d519120000c0c0003903028000307607400f06402400514841c1c1c1c9640c02e100c3c42000c1d0040c02c0e07a41140300720500c03201d9035800c00c251a5072820502840030800030350b00080d26000ca00442180c66592844040c880300b5070000c0c1903580a8824a0a11259220790400e181841c100030100c030341000c000203001c00c10012000c02068583c400ba01d08000e090740e02c14a0640f0f9000c01c8400a40c040100d24900c0540c8924070400c0715064007400580210555aa440d80545800381c41e004200d500034200c00c0e802407901c0b1074031a0041022030340a62440c50a240002d84850481d002a84901510110f03c400c1c000c16500101d40c4420161003000a96100c1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 40264168 1250 40262918 40262939
    0x20705120d0801050105180103020304051002040b04080601090908070b0613020f09010905030a030e13020f0703080105040f05250212040e090d05070305040509130203070b0d15030b040219090204 85
    0x101d49100c04079288400014142d44110101c500a00034003040d030703405080060044020790320141c800d03100d40c4030301d0300d0501e0700400620040c00145440b030342259546282094040c24584144d11000d0b09900e009140030100e10501c0403100413076400311820741655644000a8104042c00c1c45003a080b80c80854203441c2045142d000b07256100e03090700c4e03441d10715542c1d8041540d51503814070010000344161081c0c10341d908040c407000c10950954003000d810703c10034929540f40ea40020909400140c0c242004210500b440c0c4500c0d0301c0150014000d0040345400b00800000340c00c1480c00111101c18002c039464030344e2080c4850702040314030041c559900c45da2004400c8041c04180c54520450090440d00c1d01c03401e016800326040c3c107074141c036054107140c80e017010002e175a1001444c242c4613032101014000188d400340800000703400510500d1381c5403100b0741c0c111030484004490301600c1c0b02c2c6560081c40030440c04201140e1041c0d0446100d0740c1030800f200b04820b003849076406120000d00206001c181071702e51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 40265418 1250 40264168 40264183
    0x903020c040e0f030a0f0908031c0605060702030615030c030106120c0609060f05070204020f0a082202030a02090604180309081005010b0901030b0f100e040501050603070f030c02070512 81
    0x4407010721003084600b444549034403014061000e154000c005400c0d00500404030003c80b4003583c10a103101d20b41e105e840c01d08580c800381c59403420b01085102018924410321800000d0041640c9140c00c0c60700d5540800c0d40c428003e002d00c1d03441c5003901401107155504105100b00a4030250090100c03d945810ae9180000d085a044840100c000000305040303200d540c03494122079130f40e9a10400740001c5d85060b105503124500a07600075400b0400c0407182001100101480c403165510b0b0001890007078050358880c40a80540b40d081603034040c003100543d9002038548007643d0120b0b1001500d840e044002002009811120000681c58900c2e090070f060300880d01038111502d100684034010f200e010101c0c110742e003d0140d0807c0c1001440310701d0b000d500c00d03449480080340261501c840451040002120704401c0008607000510b81c0c0900c80050419028607401080203482440c1103080c000f001400c5840c08009413000c06030b5075008030030101e01c01c01c0712100808001c5d200c0e1025a9004079042e0f182c281 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 40266668 1250 40265418 40265443
    0x8031605071d040b0a020a0c0b041b0b0a02010606020c01020703170408070605031e0402011710180209030106050a080d0c0f210305181e0c040219020d1d060a0c0501090302 75
    0x1404d0019401008070b000300c644a10017070742e03607665030800f03582d821034140000342c401d503030b908032204107811601c40340c1d50b1480c060840242001c3d101c2102440007030944403070b43c0204045410124014840c0d0741c00040350400d580c1c3c07003c815101d203200044180440d004981c0806150300c100e41001034883e400c400114051801c000d04c550b5205500191034100d000c013620003d000940c1c00d5034411171201c4d5605c1d4280c1004071080700d28942c1da612502c0d444106e00c60307482492502e0b07000480c0452484c007481000e00811040d1502d00c411880c000f9801d81f2203480218500501c0021420941041081043c11103940ea2085a03048034004040702007149120b04c0303070343e003002c030b45400c0100303c180c80e44500540c41c005a541c014151070240032503030520300000800c071240c144035810707501c0556500c07400903204030411140180340001d4283c40007894404880b0501040c030038600c15096103d000a41e0301c50a40340c003035030929919110b01c01c0848455600600c041d046510344900c403000c050b070110740100c2020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 40267918 1250 40266668 40266683
    0x130501090e0610030c0e0909060106020708060c0405090c0f07030903020405060303071104150504061404050c0a020622020409030c0501050105060909040209070309020303040602060108010c0908031605071d04 91
    0x41d2115460055080c00361011076102d48404003a218043c4a43c0040c9100c106524280c0c03101c0d20280c0c041a06088103030b4400c280d0390414001400201d41c10032506000300350620080149007001403401149100701d001d6035001d00660400580c0c1c0003d404200c0f40400036a6035031640d11880d03814010109000c0b4081240300710305000111b1400d150000954524581041780c0c100700d6440302080000800e1030502c0c62401103620390780041c040e51180708840051034030364890308504400324104011107000030100c0010302d0080c401c2c4503c0c40d13400039416510503000056040030050303204c08540c2240c000301009500900381040681010340c00040e00c40601e118000900c030b0341c1d80f140308001181c001c01410079008001e02002902501c0c0003080359030840064280051080ba4640100b030860b40a9001140980d0040004104200f8240b20b030f28001402850440015824000c000d80c80c1e11421b0f00480250292804d80e000f0722038203001030001803030461005c110b2548605042e03004e4000440d010340e55203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 40269168 1250 40267918 40267937
    0xf06050a06050306041a120604060b01020706080106080403020a0c0618060201020301080a020103090602040503070305031305010305060105030106030903030b030601060306090e06040201080f040606080a03031a0f03060106030b030111130501 105
    0x5082000c22002a40c1690301c99908690b10001404001c0104540040814070000e040380302645880c400040c00140b00f8003d8081ea181a0500ca0b06407854129654115032000204002131584002c0081c191000da10300002c41e80c0b9141422450b0803004007026208003035481002400e181c024000240d03810341e0031000345c2c01c0c40e5030f41d1050707080380424885c2c0713130741500312880c198015880b03540b03c20b40e124404c440040c00d0544550100e4507282d01c42d0802c85e0725600001c1d040700d000010800820040100f440c0c14040c40c50101c00003001030006100d03180030305855240d41001c142c003d070043c42c0c40820140032036140d50713907418004014203040c1c810000094601003c900c840c002c00710384244980d4041c3c48801c0035890f4901207001c03210300107005580b425555403010880700c50500440d4942400ba03a40416a452903442480a4086110780d00e8803400e036160611240c0d1b1004a540c504481e02405e00240c071003164008640034104448559650210004da1300015243c1094000c0c00c0e074500713aa552400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 40270418 1250 40269168 40269179
    0x20f01080f060f190e1b19030e010f110d0c030204050a0620070308071a07020a120908070e0a060e0c0906030a0930020312060904020d05030403060f06 66
    0x8152040d40d0180c5035030440030008080c0d090a40d182022050081c103003590b42d10075403d04c2145404107800000781e2082e11030500401e4444c1c22075082c8200243e078100c03844c0c06610106610031513201c80c42901030540380c0c132081080358001e50000000010210702406080c0703120606220076400886d540110070300c1c00707100e218050310a1003a103064400c042c0222242c40c0c1410703030560311402000500300a164010380c2c1e41d0013040041c08108000d51142d81d280d078484099241806040c501e5002140b110b5a0030004c1000941d400140d03100c41d1900511441070f402546d090803202d044541d00503c40c0c52003901c1c4c0000d100455019100d1265185010400803603403100c41e2003c0e800320a0303800c200042c0f02071160f03031404c2c42e00c50000c5412806403200043c440c6c03002c3c1d0717800500f95071503039840d81156462001e4040c03c50003028240c010161b248095841d20300442004002400c01401c06030160166000050854545401500a4a8002d000c50b80c5442c0d1b00d02d01440608542100456a1030611500152 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 40271668 1250 40270418 40270427
    0xd03020705070b030414030a02010902040b0907020a03030f020c0a03080a140402010c0b0a14040f0501060b0405060403110a050627010f0c06020309010f020a09032d03051c020412020f01 81
    0x14076440006410240d00c1d1480c09006a0006403043ea498001850002e081220420040007c50280d070004619040180100005c40d000e01210700e008003d18010000d00c03607030201e0f80a0000c0d80c14100050708052050500c002802040301c3d44500e8401c0002031024550481102441203069034070900c03078085a09070b1130440301d0094070001d0118404500d080300181c000e02515902010481000414040d14681034100030f0003a64217590758500740d00c504080c0642030150380702070882e8a414a160038942000f20722240f0480c4009050207e0410f0707402202c0e5500da1044004103c0105001d44819500c5181d0018000c03043c00c1031030541da07045c90400c255004803824028218030b40c66005000e42030307403079080280d44020881016950703103020141d440111403000c0e00c1410155900c0100942c1140751806c002d803594488800d00400c1042c0041e1802440f000300401c199140ca45581c0b54840e41c640760680350780d010501504030b030001c0781c0414100085490003285034001c5803940c5050b14200300558 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 40272918 1250 40271668 40271677
    0xd1205010801060e060607050f07121202060105010203160f06050106210608031614070b030a11030108030a03391d090601030b0a03020a0e01060f09080316170c010902030d0302 77
    0x241c00b03404c004005031007440c0c84406099081e00407003d4803ca001c00c1012142802103e03046501180ba0b41e4541406000301104540855200d6000801f2903504000002c0d5933400342890308040025040800c01c1000035240c1d4800107103038006018081135850b04406401a0400000c5a410108810340c244085100d80141401c40e41d03200d000c2c0d480c0c0021105072990a1407020419101c44840d81040050b42c103007006440024401760340c17070a48900b4800c91100680e5000c4462104180040c00180082c940100c1203804402035070400107861403143c0300e5104540210400441306046400001c607000d4a4034402c035040c1c00e035507640c1c0b031503044d8141c0f0303e4410007034005440d50700300d011000000c0895000303900035a0a500300901d94040290340f68005401c5000302e820a80c08441941c004001054108805512400c42402c0c01e80c2060300340f400c103950ba8050025041032081c0c074450034609211119503000041c050b02d5222a50340c00201c40003a01801c01c00c10124000c0c8176040c1c4040d4807d01c00e1003582e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 40274168 1250 40272918 40272929
    0x6060311160602030c040b070b04020406080d05030f0403020c19030605060612041506050409060209040b0f060304031407060e06040b01060905180901020c0f1506100905090403020f0d120501080106 86
    0xc100703805254440200a41008000300004201008086000d2030003402a040f13440c81140365800d5481c1030300c140002d0700c610745d00c501c0d84d550110b045070704060b03007010540b5804909440709460303580d16410128500b0b2015032410b50820040c2602e218003040c241b0400d0705036801201e040c049515a0005d02030980718040b00724170480f01a0010034009010f448000b400b0a090010102e01d0b03d4841340002d007120740e442e604940c465800911240b542c1090300a206015030221003612142202e08007040041c4401800102040302002c40c904040140a007511116034200e00d003008604002c1c00b0f116a2100151001c4d81d22004c0e80c40002942480740130050142e440143c82160084040344400009040190036890155001e01824039070300020000781010501000c020985610023145030104c44d10040c0509008580c0a4900c2030450742108000c41291016078070403103984d03501d090490502070400003802d220b0052102420416600c400d60b1694080071b940c0030043d030f03603851000b142224800d1080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 40275418 1250 40274168 40274197
    0x10e0606060403060c02070302031605040f09080306061303080f040608090706050f0904090212010902150901020604120e040c12150302031009080d06060203071106030405061602100e0106060311 85
    0x24000920030b03802000301017901c1c0c012204030350340f80e50000b401d101076100085000340b90007000300010729040c05404400101f00500308894a043c1d100d4846520006010074044c1c0d00c0002d90039030201030b0520745401990041c15032900ca05482d540500075501501c14000060f400001080d44030300003007002c40032030b600340e1119480e06920001c4500c20f03170060365200c0e48c0640e8440302440175807508503060003003590101c0006040c0b00c552042111302c3c1c680e140e075144912001e114410031079030005003107030f0019000b15102030548000b0030101c1e001203105403211340080c148801c44000d20b0f00900b042e44942038400c4240880341c0316941c0303089082c016220103580f40d84450b1640e082d4510700d80c0100ea086006500e088d02c2c0c941c4089445003503a00796800840164400a2018144030403103962140030342d07045440034134600b000e8039225903407400900a1501c0304e4030700d020300200a00820881c0d0504014040a01104180000c0d2500030300242c45100003103402c0c0811000c250521100b1a03140c20701c05002c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 40276668 1250 40275418 40275427
    0x1050405130b091204090e010608070f030b040f0515100b07080301180605030f0d0201110906030f0a020c0706080411030d051c0f0e010b0a1e030807060f11030405010e060606 76
    0xb00c0490815010704110b566000d001001244c5a89200c0100080e001c04400412540780303600c3c1581c2110426030004e80507030000102844030a90743c00c02c10301102e411280c0100c2d40d444908251112014121b0001e0451280010001c008074040510300d01c01c0b206d01021041c1c0d10794812071385200e0b01c2446c0005101d450300f00014092804100400e00440c0c00d84900007030600e40341c401103071404450440d000400e511104a00782010b509020300425020322460180c01d00741c00c4400306d441c901000d003211281085150000c3c0a02c1c04e02e50659419840100c02c645c0703640e98941e005401c0d000305850030f860126030300307e006603542000619408180300d01d83c1d619103070051104040c4010371410fa011101c1e10b481d40c1003444c3c400300318040c0003489c0401c500001440e21000c4100040748003168882c2502d080d545010302c804602c2014044c003241d07000404180c0d90820351510070b000705040c000d13050515190018030303440121070710091481a40b0a8000b04241707220b0070b41c03d955842c2d08032101544484100f2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 40277918 1250 40276668 40276673
    0xb0d060902101e1d0a03030804060513080418111602030c03030a020303040f030908060703060513090203190206040306150302100e03120d0e0105010e0907091a04180c03030806090105040513 83
    0x41c2405028980c1c042c0314240484000005402c441300c5a000b51f0026408501340300070711155116880d00040101c142d4504018240d90b0a801800355209841e9110003510100149010075040f05010700315010032241d48562029000c42240401c80050b40a88148040c14980341400002c603494610302c0c0d001075055a84595403005516500001242000184080000c0e4071600b04034550090065850115009003010140300401400303030100b501e401d00b031440789809601c0208080f00303000920101002c07400018004100350307108640c00109030f10f00c0c000000c4040c4486158480580344200d45613600b105d00c03480c044881044038114a907043d0844c050720030b0744050300e500414068100140c0842c1c0103094401c0242112001da001c0780702c51401c90100310090344140304c4000981064003040100440081c00013410b107480d40e0300c45010b41c1d516140108042e5071031080004039035201846001943e00c03841c2c0105a00c0301516054003a5881c3c50000c81c1a02c1d003405114800c20b12840c042ca140322694 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 40279168 1250 40277918 40277927
    0xb0d090201090306050a020d0c020309010921020d0602070302160b0d2307020c0f12120901090305070609060806150702100509040903080f010e0709090b03010b0d060902101e 76
    0x44012030500286003000000504c460048902c11810b0240043e12080080e001405a51415813060210340040044180c985e800c088600295030302e1404081000e0b800d0310120004a506220280d440a028040c080420507650018400c01c0c1c42030b42601c002000341281c0d07800c3c2544600600004280a010101004415500035a000d0018040c170a099059801d88880e482400b903e40344010703008640350350211304140001401d880421f503a00000340740042c081c1d0b603e6021020600140306000038a011083e0b00c9014070101454004054a00d8281c0d5542c02a00ba0040d52003118045000703c40020083c0c50b0101c41420f0300e41c0b004501610702211a407c021000100354644010712105218990040e1100d214020b1001d20a840744012814102003500032008141c0c0b003520299549001c101005520110034421070701902c0001c680c900300310001a01400701040841d80028422541c141802000d4000c078030240e000380e034201c40c42c1000d40c0c1c0c00c17565140c141c1e0303002190200030b80081c64103e108 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 40280418 1250 40279168 40279181
    0x20307031106090a08030d050601050c07060305090703050d02060709080a020603010302010c0c0305061501020f0105010303020a26190e0103150501110a02061b0d021903080702010b040912030b0303040b0d 89
    0x14802840c160301d407400107506013402d0300003030300303035400850001301d0501d240c4281d40e04081c00b400d0203810106429841c96480807135005003410581c80f030001c035140d000c0c20040000a160f0100540d0700a118220f802555070078110f600000143c4140000115410042420038000c0c1e00501410700c0c5a013503030019070b02c04402010880e00b10401600c0040030130014411140070340c19158030a24007164420009103000410800003820380d241c040104002600050005d410316848154200090440c0700185c4180380051075480411344000b0f2410401c581c0ca4610920400d0181c9400300003440c004011021174240c0e190001505461001c140229801003a00004005044007241d00030001907011500c1074210061080300c104007111400388020301844041d0341d14406100414205d22601030281c807003000340b0300c0078090140440104000f030f031003900800c100302c001400602210400d890240d40c2c05004a180704d002a21780007003e00546404411030341181da00709089414401034411a9008102 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 40281668 1250 40280418 40280453
    0x2060c0717180a08030405041a03070311010507050303040b04020a090c080a0f0f0e07090b1206010501030504030507050a030c061b080c09041401031b0b040803070b06040e0316140a02030703 83
    0x410102e2800e19a4802010101505002c8040c4d901d452070207051000b0384d0241c0c400b1561000800707000304c0aa0310700061840403642c001c42c072000d07500d241c0c80c0142c3d0244618100903205000000400061002c8440c005000341d1007650944e203000d40d112050300845505034580c0b80001c20b05070100c1d54041d00d5412449020401010000e407044641100c64101c41e14040c0c036800c03541000034200080030300d912880d014094281d98900d4140c03090315000e03880d02e505001b0356041c180d584010909151080003500c94003a48030b0125200c400150502030300002c001002211058248040704c071814140c0c80b10f51442c800300b91207103038030350b2110995401140c021460858025584406844501ca0301002141c025030042c20500300380c1c00c002410030b8441e840b0740c100024250080004001030507000044400850308098404040d07240d440004001d484900011501840045007540040740c1c410071401c43d6a11900d1020218114902c600e030310340000540c040d500d508004401c101180007110508040034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 40282918 1250 40281668 40281697
    0x806130b061c05100f050d1209050405070305161107050d050102070506070801171f02030907030c140406090608070e071b060b01020606010e150703050903010906050702060c0717 78
    0x151400301c1c840b07410018001408aa00c82003440348002844000c0d0001d485294803114420781040c01050608408a0004140c5402806465a4188200983c1c80503100040041c890b50400038401005400d00fa00c0f482c9022182c8480d01d81c0303040c010034074154403c107040042d04856103407101b001004441d03180d00350b8465408014143c0029414004944114080e844101c0b0301d5040003010342410074241003064903940210080307541c4442d0828003400c030100c2014050307034942d110190b0b9404c084259000800c07040c0140c10211340800c0d01c00049440007020344040107400e0340c50f08840c095803078074421107446400c40e100074802c0e451895400c641c4800e040c1080c030394411f074440b440006410b800d282a142a6900c8940d44402d40c0d042c40180d800400034600380030010703030b250b0000f030343d45802d0301c0000c034150740026090003014042c806035076040340000c0c0204020441c0d803c284c40685400c4a616005016220001d0b2a0303000742400c0c0c50301d194006083d50000ca01070790b00c05a10340e0201e030a400007038 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 40284168 1250 40282918 40282927
    0x115060e1030090b01030b010617041e020d021002010b1e060307080403020a0b04030801061205090606060a0c050303041406010b03040f0809010c020907020a051b01021015030c030803090d0806130b06 87
    0x641080010b0717008502c204c2c0807540962600900401504581c07100130343e09031003203052002080d15034104000c0d45004840703003044241c4030310000d08524076508000b500041ca003142e51101e40e4065015208006050312045a0803503d114951f4a021200283c640d11210500104034050b2040183c0355025110340102c030305d00d0015460f402c200c81c000301d0b400ca00245044006201c096844140201401010b603002e20060816826154651324000c0c5024000c89011620101117441800c1c034010341078200050701d940342414104042041d03001c0590007410310540e0000600041e01400700c034816604690049070105072550343c0005a4421501039041007130012440000d0313510200340c2c6004041c0b54005201d400014541039042401c888010710b60704034010341800c50380e60041540d54028040b0100090616034036000c40c08a00b0850304080c28002001d034001c010031800500543c01200c81c102207502e150640b41046408200803182c460f00682c0071503040b8240d40d00d54010300701d025401000365040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 40285418 1250 40284168 40284173
    0x50702030307080306031902030d0c06020d0204080304051c020102060a0b0d0b0c1b070b090d0c080109080703020c0306010f0b070c05040e0c1801080a140115060e103009 74
    0x450b0008841620020700c00000d000e00ca10342080750b50b5210080d149640c000c0801500002d40b5500c2c21141402881910109031041141c0c6034110344903a40f42900454443e034840c0d0071a6a030f90028021140903c482806654903029910b80120035564140d0007040d482c0d880c1d010000c007501814850030b81016040c51001c0008290584091043e10030748000d540380d0105100c90362043d06007480d016541e8021107410301810180d40203c4500b4101525030030714402c40f1340392039203a41400b1741c029005540b90001200030800180d00401342035009500320356603402000c081644031007003803040d10780c28900c0c103404200c030120450203800d02078041e120032401c0c80c0c1c0d40c0012405403449400804e02c26081658070044916200003800b900352001001c81e01158145100c880da60713120b100d4041c4c240e40c003a12003296441000d400011301118100c9881c0080d0340e8810000d041c00403404003141c410701100c0d4500e0f003191b11828840b44c20504030b01e089070080b030203c10001410501414030300b11040d11465080c01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 40286668 1250 40285418 40285423
    0x90304180f090f1a040b0a02070c030b01080705090702010b0d121e081006030501030b040618050a030305010e0f1e0702100203010b040501020f0f0d030c0e03060f010503010b0105120c0a05070203 85
    0x4502d805002820101c0c0c140f8540001000d40f140405084203007840140404541c04414a651014420794016a294250b00300701a542160f03500c0100724031880c1c40040340450010903948110b4a0544001c00e0f281c82c2c1c140300b070307090310f0781e48804540105a03004040085a104941e2a10500860401c18808a40c590a20707a00003d1055000007103004801442030810303d40c02c580008100300e103810031203035055644111148a01130805011079072100682d149001107580b10180c41070f80001107901020300e41c5170181c082d200910a0b15501500c490000e10a43e2014400f10721601c0c4400302084500003a404507800e65902400c8141180300c0c030060040361a0443c4020341c040d02c4484d030010f40f2035260100080c0703000100c1d00280e42035000540414000f070070000711030408078040d0902041d0000d03048001c440d1701d52902201036140c800c142c1800040704601c19480c0c141ca01c150000d0045504035001542c1c01e20888400d80d0b5040d60120001e11007292060183c1600390a030b1500b42e251a403584c00192 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 40287774 1106 40286668 40286681
    0x1090909050a08032206050f0105010906050919050a030c0e010605040b0d050604110d050f090f0312060d020301062409050603040206070201030e0601091505030303090304180f 77
    0x3507034141111500b010001060705e08141e56945424444082c00050f65107440043c2c5104c00801c1d254410200030041c3c4050340c8a0f03510309200385c000c3c48090301741c0c00c000160180c90075901088640e5070794980b20040d801068031150980c00d11004280d800d10691144051180c10002004940212000e46a400344003490001301513840b000420064440e1501070b031030013400001c6058102002e40c1c4010700804e0748905d00d42899440400966407402d4102500309180c2c000d0207919203040826460b15440365019001c903130241780340d5005c01d09581198110700101ea10070910300c2e5942d400b00b0b0700340c4c403242000e103002c0754041e240c040458080c0c48094030190194034001580015a402600880c22810f841e43c102c424560b0344412980080043c00b003400300c900360030b0f01c0c0040c491a001003580d000e80e001102842c40c00d40783c0b00903148189842000200556200d0f820b08200e03142511540 = true := by decide +kernel

theorem cover : BRFrame.Cov 40107918 40287774 := by
  have h0 := BRFrame.cov_init 40107918
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 40107918 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 40107918 ≤ n) (h2 : n < 40287774) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
