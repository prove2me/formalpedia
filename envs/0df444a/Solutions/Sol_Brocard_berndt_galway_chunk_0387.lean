-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0387
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:33:06.364662+00:00
-- url     : https://prove2.me/submissions/431d5210-1c3d-46c9-b489-fca79ad0b7cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 69424462 ≤ n < 69604318 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 69425712 1250 69424462 69424477
    0x2607060e030304140d02040504080316030b01050906070c090c08070210020a08040b040c08010c02030405030115080d140d050103030c06051b0a1d060403050c011206140f03150c04060f050f 82
    0x50100303444604142e01c49242045d883e54000e0420310180c5000d082c00b01e4180d000b982d0380d0100010511b480c0702c42c00d00c00d109200103d0070507960503150a840c20100509500481415500c00440a2000034580704602c190030a031446038503030002e0361400401c0603041c07001e40a41003140d207004108820080b580300f810158421780c0480c0a007240c0d115828141050341e510703000081da079841c100d07105440da0b070008054401c452044000707100c603203124a0401080011031195100560151020844440c00340042c2c0c009000b44004090130415920b03075250a4030000c2c0e02c1903000c20401e110102c140505c0340240c42e40085041030500701e8070190128580140303c2c80c03450004100c82500c8601200880026142220100410aa440c0d41d140d041044d25104030000090200345020010f004190050040713004685080b04e420a50117864428031920000c1001016814000d054241c5034214500080c03900407450038180d10345443c01d0450103030003014404103a40900c00d0500c06d03080c0c512510300840d000d2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 69426962 1250 69425712 69425729
    0x4030b1e060901060305040f0506271b12120d0b010e030109050a020609010c0b0f06031e070303180902181002070305030f090d0b0106080916210206042607060e030304 73
    0x1103540d2824182e48001032150f00600c0d03800ad003824800c245003024244080075a40d154861f2800087c612400e5690381103a0074284206aa1031001d03415140000d40440c1c0a100003064800d4900084030703c0c0800e6200b1500310683d55038503416001c095038406010407000905a008112404084d00ca150341c1d0880340300002e101d14400100846164400d5813561310b400d81c040b20704107103424100071800d030300c081c02c0f0ba003240284202c074035440c6090807030282150810f0703403500500420340c19502c040b240201c241c1d2503003205d00d05400000815410741c1c030042c481d0521003040b8901ca020700d00100002c5000081c1c01d8400c6500c03000052010031400302c1101c6000c0301d1150620380d90202000424582e400030440988590341c294000a6015040a0000d114a2005069030040d48282e551841c90019601480305070b840c001d011041081c1020705d00300c1c200340c001000d190600307a680030300f200400302f01c5070f0701051030304400c1c9410152a010001100903090030b0a001c1071564103034002c6580c0e03008600c100043c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 69428212 1250 69426962 69426971
    0xd090303020904021b10091a06030a150b031b0a05040905010902030106031a0a15060507050f1f0f1a0d0602091306031a090706050c01020c0304030b1e0609010603 71
    0x4050007641196070402001d40107540321305070f0351010352480502040e4440c1d24010100428409483c87c8941450340d640006081c0450b80180e140c03042c0814001c252980510503040180c0110302d44900070b10308a4032a403008982c01c180d00042c1030030040c004a400d11144085d010b21170a543c1c1c3d604541d000d446041c0e030f00040308001802c0090141c03007603400107501940303042404070900503040310000040c0b455060140701c544422507888216481c1010307143d0701c1c15480c10140080d511800c010303c1e0301c1c0c0c040c00c112008550748600c1141009a00e072010300710040c2c078618000350450103000d161704125014004100c509002d010031400c1c441c00d0b050b00c1c0d108811007401c0004001060f810f90700e640201504440c510184407100200400b03083c00156030503000840c1c0796286200e0358502c40d115460301c43c0038040c8580350110990f001e410058108220307540a1204600603401000944011402485424180d0903c02c14410039004401e4500807640020f60070056a51140500c0754112841c9241c0001c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 69429462 1250 69428212 69428231
    0xb060d030309060501120215040612180501060803191d0607021518090a0e1005071106101a030c0f1c1814010902011e090f03080d1104050102030d 64
    0x400610702582c009020502d0803002050100da5100050903140c400e83c0c058006032107a0002c285140214412280028080386078035840c1d15031500300d501d0600d08051644416179581e83c4d45800d403a050781006095620200d5070031420107241802800030402e80c00d12035130000340d0000b6980c05496552006010744400905c801c1151a4040160003e01014502a0319040c800c859800b0400603c0b810610401d90704e400324079081c4041c4079110480880f00010038003100c03501245000383c0b10040600050180144070103111340e0052040c039110303483c05480181824100341c0d006211120046404d402e081050040105400581d8219500388501004003921984200d694020f5103000b2072400c0103003424800c100748080b07a800d9828000c9840780003040c06a030080c1e50054200c400c8403401078000746d601e010889040120808116001a461400c20b1a180c0c403071904201c070900f580d004131852000010800405100e5201d42108102460403041c903140c9403000003940da010700c405002e5069541c12582 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 69430712 1250 69429462 69429467
    0x91a03090715020d03060b12070c051606020606090a110d0f06050a180c0305130807020f03060702030c0105061c060e010b2206170303010308030a090602120105011b0b060d03 76
    0x203401080d80402118001c42c111800079180c0d15156801804170742130030400700700d0210a81c20b44400d451881400141503946010403650440d1035803003983c1c00c0c0903030140024440c0ea00c601400c054442c9070024965401d1401c107000181d00014414400c60f440c00e61500c2e40400341008032030f186c22501f18042074502c1803082110080480f41e1006500c41406980004d1240b8043c00040028038211403c200c0c803c0b84943c15001d4480c120741d4000405085a11003000a42d080040c6c00a82e00181103503003410802000b0034035002094075880d0150340041100100c8250900442c0d91000080d500380c5000c00c031061004440c9001c850008001c551681c91820214009601180700c40b00010040300070203401010462109444181000c1c016082c103401041d600310400049640d00c8000004516580c41c5031540301c40b40d0000341003800300d82d03202e6a040010840c030780090000b42c03414400c000110351412001422022001012144c86904030340c42a000c0b031017592440e64403003800d840c0e01e00e1461103480c04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 69431962 1250 69430712 69430723
    0x30c030a0e060103120807030b060a05130f0603051006090b030a0e0114040c0603060f121403070b0a06050405160c031d09040c050307120f020d060204030503190e01091a0309 76
    0x1c8010300c01e40d000041400781c1813a4055036144a61140c40349a243d94030101c090311030420b042034001008004c2c40c40c00c944220010451b0583d80e0705400100e545942040541607403544c8010f001039141c1e014030119038141c003042c034010003503800d00c5032160340b8080703100340c83c0c0c080185541d070b020380e4910340410850401e4000e44079560100c0000903151506142c007000b1070480f4042e0300f002924040f80462004090b15a14081d102002c043c4080d040c00c0b5a600c10303000603a580c10649502080c0010700008400d001550f0140020110114005007000d042c40201c490040c89a0801100c100320120400c1c0c00c8038500c1100381e014544000b0030b0401106200c10341c41500385594100b4040810801448803840d064804d48108805561046a5601040300c405031040005410382c2100b070146001881d04105c0c42c0304007440f50b800541016544e880b12401c0d034014031030103002e940c3c00003c10400198080c04840f02903000b404d109522a0900c1c0c00e0480c54408101001c0c01c0780c10020100c0c00b049000c100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 69433212 1250 69431962 69431981
    0x150602061506072307050f1f09050603041103011a090a05060f0d03020c030114010b03070f020705120607020706180b16020a03030c0c08030406051c0e0106080c0a050d08030c030a 78
    0xc000b249401300c4c91080314202c1202c8103031200d00501c000030a0303d191040700c904d5400c81c01401d0800d10107150481800082ca102002414031807641340000329900d4040145200c4d50007200159285c1000406040c00d6a804e007005048416881005a500d40d4a02440c15041401e62a00244654038400450109000501c440354840c074851001800c255000900039001c05090303000f80412401c1800e441740c804400c5c02040c41d050000e00009240b103200705909400e5401c2803049030a09a07551000c12210102d6506c4001039810640420680a4040000d81c00505007482c00c580c282c540001940d200d001a802014002140050079050000c041d45030b200000707030014040d040003a40c0b03150180020440040403541450312810010307000b80301200b030301c0841d859516060710304018410413890b0340c020302c040b10540990301c1e000d41c01101c000b4031074407004e080c0c100c3c028120507484004019004d012603201610911201d0312840003d40014141ca400c031445052091700d90700c0302c42409011f000c20b00c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 69434462 1250 69433212 69433223
    0x130503010f0605040e030703050f0a0323010314060103030906050f0715150b070804030303052a09040b04060b0403020d0f0501050406020910080907030213020d02040b090415060206150607 82
    0x30740048580c0c090354080001c4403000c0360100441c4501030545512401010805000700d5824071041d40413088440c005e01c45104a031600003412030b85403150707083c0070110048003c0d40602d000010300401c0500651405130b4240c01c0000c210962650f40c00510b0b1014600030035007041004581e000038040c2040c10382d080c1341ea0040c200902013103081c01503002441301d0340c4a910700d49900e22000440d40035010444d241150840402440c040c1540c409130080c10000c1c00702c0140004505d94010342da0004141040c0045200c01000d55400d0344030b041000b83c0310005401803066203000410425903d8403012901100e6060301c0070340215040d82017600400803c048050107039400c05040104201e400c1e4002c05080c80b08841c520800d13014000103c40d01720003100c060610381d110074010700c007502d40900720001c1c0066800c1c0142c030745600c110041d4182c0e08142c0c482d0303444044c00f04082d249031416003d481c00850b0240c8040c003540346040b000071340c2c1da640504032404241036009103031000d0b200c140071100b010fa0400d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 69435712 1250 69434462 69434471
    0x6050a090906080a0c0506070b04020603040c03020306040609030305063a080c01021c020708070312021605070f080303040c1502070b040605120f071202030a09120801031401020a0c030513050301 85
    0x404403151603540001307003250a00b018440109240c0341035019500700680040b80c003607031555658288400d0b640040d0096038004400c0c0d00001c0182e0703080200e83d2040380705000120742d40c810740c82d001d000d1b180b000d00454441c040806444d0300740c0d40100d0300c94460030101c44941c2d2000c1c140c284100d01c3c20b00100f5014000010000d000410010150002c01003030380c51155810f019102d148190003280142d000c01000750104000c10004240301d8909a841a84031040c01071038034036040e0107034168090f6204e01f02c6030380c1c2002c0300402c0400c102c0c1107510000d100d100d000e14510326069403940c002d20b01902034803004000202045004034420401c00300680340e80f40c0c1c044d40e0346860f9070000c1c2072508035001d19005c5030700782400202d06542c82d80440d401941b05880c2d002c62407446903130800c00381d0801007508100940d10007182c00030441a06250944e29200d444010302541141003807081c4800e601c1e2124150703030040103200e080c20b034445801c0181c1e98040c0740c00c0b525503040c07030a00d642001942c0d0140340d241d03007403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 69436962 1250 69435712 69435719
    0x301030803010e011401050a031e06230d03020705121009060f05060d020303030114040209030d05120702030c060105010c1505180712020603062806020a110103090b0106050a090906 79
    0x30000660503540c003080b0707280c0c55030f0f41d40b0651495440d400c0500c3c0c0c006241030224074805070094100d401c1c7c0d07086203101c176010001c01c1c04a030803c07944903a00c9111054403501000e0001d5403110b01c0700000c4076007039801e88481186a100650b40e62240d114003070059485e2800d80346810300501440d002600006024407480e246410810b0251482d1585065120f00e4440407075002c0ca001c20309041700700c3d4090041e50840c0c0c038001000b1034007084000b00680181d000c2010085581c0c0c2408a20707580942c2d902c4032900c540a8111040e40740400911420556104110b1401070240025405046a1003440d0192945c242442c107100a040d29010080c107080c1880140501601015095900c1c031000c4021a0700d82c60340d80960321404008068080c0d0040d504202055103401c00c482e000c000d820480813114103a01c26002039007500c90307896000c1f0700107030030004000c020059036803d44084c01d2024a401c0c08203a0107600c880300c2d101c0307046c4980001c1c018001200c400280c09040800021b114a000402c40c60b5074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 69438212 1250 69436962 69436973
    0xf12070903120c11010c15020309160b0c0c010903080412080c0109030309050d021605060703020a05060a02090f0a0b090907020f01140402040c02010e0a140a02040f1d0607020a0201031808030103 85
    0xa02c0108139403c1d00f440c1550400b9503c200c0608200c55001400d0000301040e001d991340003940040c1503107030706000358105054000000341d658001030480100b40382e40c0700f4025201034140150315028a04200ca520001c0001c07861f89070603682662a452074400010482c1d1421401d1392082108030400c0f942008400c20134560541e0204501a00860a4954520030028100d803111581f003a003a040503000790081c0000e08000001e05600da1082c012034511a5082c3c4a09142840448030780390459000a100e010714140f0f41d070b641001a4095807800d01d4507051003000308e554001e402001c1d0040003e6000503181c00d10070880784401d5540d13200200705880d00c40070170420202040707030107900031402c1c58150803a062052040d2122803406c04090100d5200c82d9494810084d4500e0180440d44a40036449000d6a00c81c41140d8100075000c0000444100d050411509481100c02c2d00c03000750440300030090995008581c2d180090b82c240303000613611480b007020305444260b62402810500b000300c004000c206 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 69439462 1250 69438212 69438227
    0x605130201030608010b0307090e0309060c06150f06250b0a0207030e0603010e0106140c0712050d0c02032503060504051f05040507060804050102090d0312060b0f1207090312 76
    0x5000ba60309000190f21411000d0a95188001c01034142e84010005c00c5104090351200c00e00c2041c01055a103421101d9000074100e03000f614040380550807544c02d01440c4c034042802e0f400500010780c0c403008808502c0317002400d18066824101481e401c0103c070b68005c07280182c0d2440e403c981c440750f0b4442d181041900c02009401c40c500407404104030301941ca825203000307025607040703810b4840c82c1001e90f802c150080340c00300902d580031050f0000501081ca01b142052202c0e0019021107402c60300740300b0803820321602d0904006242d4040c00014100c8102603203000c10b0710034080c0740700302d558a640c44d41014014032030300352540040c08403803601092000b04400480c1111041070600290307074003d4103409190301181d0301a01c00401561240c1000c02c51103009864055010f4011400181820140c03000703d0b0402210350011000100350810101134003100f81f03e000081e240503250a0b003000004101802180324a920b40c40340d40d51580d00082205105501400195501408504416661603400390011 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 69440712 1250 69439462 69439501
    0x18060705100b040f02030f0c07150203010603090b1e0604050c0705010f02040e0f010602060411010509190905070509090613090c090f060b03150f010306080d020a0b16090308090406030605 82
    0x3c1d41440c200c2c003006030050096038000d85000440350300d5034460b03060950060307208140854801408602201c0a10303440d101460090030540c03004035080d00c1301c1c5400344038000001d0140080c0100402480d00340d03000d503101da41d40407000707032000980c9458008001e240b6018090f0f0086c142d41c05c003420920810b030140c01400460f00340c62440481a2211140070385100800d00518006a02000004020a031f0749621603140c2081030511500d8040d00304045100d03031040074a0080030303807401c4c1030400810310944a80d95001034540350141c142100390f0b002480072131025010304d22a03a40c4290300107401c5065841082c9040c0c1c8100e0300d0031001e40d903141100c0600b1403242c0c1c0c0900946001000281584100704a9200340140c0c83c81c01d1821241d082004000182440d140d41010b54030280440c02040c100402003c55450360020113640d9010700d002c040ca600000e040c2100f00d5410310110703042d072b50030400d940160b81e4403110740340c0c849104c80045002401140e02c043c240c0c50404090001203a03038080c000581 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 69441962 1250 69440712 69440719
    0x519060609060b040503060403080709030b0103230606010c03050304023d0305130b0405100c0507020f0307060915030b1306050315010e060415120b0105011707020318060705100b 78
    0x90302d943eaa4401100e003d140f0903650103401060003d400a03102d0310f07445601c1340b95070401c4d031642c50302c80e2540b4845a101341c1046407420105840c90300c049030026029011300c080000140308a280060008010506d00440101444408000b00341155100a015040300d40c41305a6040d044c41c0e2301000c0c2c0b1030700b40104200000000d52a2400c005944030b40603030361043c480403820601400c080d64400c10401402071041e01d141c01420680030182d0748a000740c5032058070303e0383d485d5100c100300d004000402c41f021040303034840c0d4040d64003000201e80003100e000440d00e2252a40d1886843c01c041500501000f80c0c802d1707884a83e900c0d00d41c00074803040e40481c05031807040c0c0c1111100810235a402e18004028020601c403081c0c40c6c0001102c81c0380c82d4100105c0e80801c0e107592001255541e80d404020307806132070704607560280300c401072200f5640501c80301142c0d0996681c0e84c0c440c2c180004041e484c0e00c0740d0444640c51480140040a03641c481004880406502c2002c4403800e04091410100030205d01412620 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 69443212 1250 69441962 69441971
    0x140c0a1401060b03270d09060e0603090c0603091606050d05010e0f060f040f02040902180105070f080a031b0801030501050105011805040c020705060c0a12050f03040303090519060609 80
    0x81114148500c40507070f06040f100c20f245803240c1c846030300c0d40c15401d49000012000620308242500c2c0a2202605410041d107030003c14900b045009000d0301c010503405030007140c1c10701c1005902e80f000100620f052405884455032a01c9841642e070800080c0c2d030220280c042488400100503074480e00401400400c11010400c598075a01078190100d400d42e4031481800e03200012a03028a003420340810858002000003841030780c92015130043e81c1059104500099012802c0e0740301504070000a6a544800d19000d40740114070350380e400c004546101d02030300040c0302140300d408480c080c0d40103085000605c1221040d503140041c000300990b500b40011079140d42060300004655005408160600c0e0182084143c058200020b001c02480c04183d802e0071032180d20030008030394840c00020402c00039410041d100500140c1050550084010900310030002d040107000620241002030701c1e00254946408074100045007004c0d4540040808174070f22040b05820480200115640910102d5190a00a00 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 69444462 1250 69443212 69443243
    0x130302010305070c030f0e060c07060c14010b0603010303050c070b070b070207081b120312040305120106080106050417010603060e0f06010506090102070e1f090c080f25140c0a 77
    0x4c501c00a0160000c1c007050382c85222020070342c0140b01c92a0440b1001d881107080055070760401e03103444900e82c819004035070901482c00c2409001a508981c84042d0030080c4081c0d901040072070420310051002404100c408150501c4141c030500022006144010015846510900302007040e09000d8600320b01520810000088a00d408aa01043c0c1070921031070b01940e00c1288144060342c01441088000d90108011140c01c1c4080710300740c0c40c003c5000e40d48258403040890b44070411442c2c1a04180d051000200c0100030340361b44003084900f511143c1020440d079400c0d05c421280900000c3d00001c0c01c0034144250861407000000d007201c1d900700d1042c115681c9036030340d4040c46268459801c2e80c5005030001c8005110342c8100d001150340020b2180c0320034490b43c032113801e0402d058840b9040103c05070703100c3c11400b140700c0d8400c010f280c2100e03011082d048203050003a203100421201451606a001c100e00b1401006800b502340c41000000022246503103030500c0303030b01c01d80310940c50780c044401841c1c200703c0b40d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 69445712 1250 69444462 69444467
    0xd0f030b0a05030304050607020d0f0515150604150c231203060f0904020a15050a030606020105090c011107050a15020106080f0a0b060d02060a080106020606030c0607120302090613030201030507 85
    0x810441c1c03400fa0140d460142841d0901180340d01241c000c0c0c7e00008004120000240c22507600100d0a0140015040140048902d46800c2001520807001c030880d8420000d8280e42d21403c50302141d914001003071507654881825549401042009003040e15000c0020340b88a100ca2140140621820159110403050f84200405404140c44080c7c0250071095168031500303043c1415508240010547d00780f007640e48084040d803440c4018840005040800c3e2400d199426000d0080501403500080c4140e2802d0703000140c3c1d408110303454504004410b50190f80c4c013071086c00540003520740908090203080d1610b40d1081c1c100e000804042c015842c00c0c0c80046c01680104080c0800304501003c0c0c042024152a0500010000b070541588000610070550040c0c1d1040c005140401031921504040d6140100203410124024100340c000d40250000b6103d41d0344000840d070a082e84a260826a04140f5200b2002030048840c0150031810001c1d9860000d007542034141c045034401d80c0c0c10311842da5086e404 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 69446962 1250 69445712 69445729
    0xd06270e031602060313021002030c100504030507020904150207140c0907170705040e090c0a050102060106020a170903031c150e01180b0405070c050601081b09090a050d0f030b 77
    0x8103005803410614600614040b0000c5400c52260400e440030350806c0d0300015000c803034a520071405640001003c826100c018400741078109040030041059140c00e480113000c40c851400d001344150704510028003000000041c42c8502c0681240840d120502071402c442c0000c0d01100e061400d00c11003c4070f401a20b090b1030b0385803040f0082d030f031407100d1021501d0945200100140c18017061080900000c00c0003246140c1c1070b441900090b0007028105880b03428424900000d40246046400203001807100503000031300d40c880700c0d512000707107403110766860010300d1075000e48100103505000020300080d81d43d051495102c0c0356a1803140400103481c01c620307a06035040c483e100f214400000c101c01040246001502d0302c00c2c0c005540c10119a81010340c4c001012164100d4882c8085040401e0740781c1840301c1000201e0140150314018054004e035000c90500c11007114003150b00c500d4174200010341e4a00240480f40707806510170116124110700303240150810701c6810101001900c1d05108000501d001c035203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 69448212 1250 69446962 69446977
    0x10b03010b070f151401090e0a030203030718030203060f16020a030c0303020706150906080c040902031005090a05030f090909011a1c020901030606090507180501050d06270e03 77
    0x4424601941c60361000e15000800000343d6083c0c0310450512034001d00c85c003440d80c1c0d801440e02c035410310b0760400d24030f2804c803280b00506403c56440013a28000081d00042120b4010b641410401d480e19424018044205003d4000a4060054505010b0240c450881142c042c540004401c08039400448040380c3e03544a0000150001c0c40c41c5003008040703802980146000c0f8090340c2c02040b071010401c40a40300654a034040030081d03541381001c0042d901c050000500f2070b201100e09010b100550340010303035149800450004c40030f5840000c61207103141080a140142d603c00181c070303202d400240d4416103035002291450f020320016000100841d4041c82050010600e200e0a6000b10040300240300c1c11403205510300480f400340c0c0d41c4081c0075981c0c1c80d00d0f6600840c407402d0045401414041c4240a840003c1d00e0003091002415442041480314806141540c000713180c81a101c8140b6410703840901070715031040001c030356517001e03031810915070244c0300c10540d0328103a0034880c9008407921160341c3c2c0700d0120b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 69449462 1250 69448212 69448229
    0x6090403050a0f09080303041b051801090216020d0c050108070807021f18060f0b0405060303040e13120c0201020c2b0501020909010f0311090601090302060a17090c030105010b0301 79
    0x40c80302c816000d1011a4444800b620f04800c2c0c16841d5540d07945564016501079812400030199440c413180c250070f8003c0a014240c5114103e42d40744043c0d030161301810301901020076004641b40c028209985020081580c0040910080b5210341c100300c900c900d403901500740091001000258018020a07680c0d020b0441c56004006190409c401102c00c0500514080400c07900c842c10221820002080c804074540610800158070f512500058121074101c0821409181030030100b10a641d0044251012241e030a810158696203441645041b100c124000420120b4203120a000c0b0541c85544c44903454400c0e022541c0c4140703640d0801030f2044030152130030700c1da2152400f4008c480e143c0b001244542e074481e00015040200c1480090b94254090300198480105407500f002400b0054181c000717580025101c0000f40e0070150300003441c0601900019009000c00a17800244900c102e904560300c00c03000700c0303a104500b0321000c840d8075800300040a5101e50b0804001060103914103007224100c4003920f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 69450712 1250 69449462 69449467
    0x1208030703050a09080f0a03060806090a030c0330050a0b130b06070b0106030e101103060904080d110a0e060301080c0d020109030501020d0203010f090e0607031802031e060609040305 80
    0x34441100a800d00410003404507850311010400903030302c40b02400e41e007668462115141c50784c4090040417034aa40c0e0140b095540000144092100b0202d22290a990186021500041c031800c0c140c0d02001100c003032300d2498001109885614030003040303102230100305250030b00403500ca0030380c080251921024800e0f0b2120000c0803484080410340c0c4584c0c40c0c81e0002e4040c50070000175845001e03480c20244c2c4000c001c01c4c0c40341185841d0050a12000d204040e040108201031140d15800a500d400300070865409803100348040740601503280280c9200401c02030050203444444054107150360405841030f4081a19005410344625050301641d05035000c1000811680382c811040103040c658002c0d0603814041101d5011004c61030a0004260f000e094141c09a80c0754900040610b03840e0fa9036112064103480c0610710039007024007103101034102c900d0380f0300410021211004100b9a9060010003540744c030030025444d480c5c1260316402e0040340304803405d8031036036503511040c46030702c010840780240000c0c000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 69451962 1250 69450712 69450721
    0x2706020a1b0c0918170c06060901060c03050f090319030216031703061906030b13020304110f03030910030504020f0a0501021c05040e010e04050f16032009070c0b01120803 75
    0x8641c07100100c5241c1e24149196034003aa1200b103a109400d461703012500e00f0018500c021000308008450300550709072001041585440001000c3d000049401020031400048164031801ca074000d86802c0c03440101680c00301103000340a5061428001005c4016006a49070000c0a81c080300b045000c0b290011031031000350486914400c56940001c1c0590b9001d0040400b540c188040310b0ba080c40504102c0c3ca00145542d82d804c20802e0350800f14007040c00e0907004004102c00506180700801280c4000d8441c0b80701c0702048c400003030541c010311903155003101055034041503031341d8150440d50003540283e6080014036444020310050030020301556001d0b900c180c0000e51403405a44031402c1e0300c405454041d00b03154503002c01260010342a0301100703000280005002c2401014002644800300c00d100905541c4880c0c210b5560000c018440600f4000003207602c40d026416090840007241c100034942d203203074a0090f10117044d26451950035210801d041f0004161090b64408408000e500150b05909580d80c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 69453212 1250 69451962 69451979
    0x70305010605041205071d1503060601090608040f150605011211030103031805031b01080603060702190212060108010e1218060d0b04050f06130912032706020a1b0c 72
    0x14401c8100c440f0700c52120000ba0111000034134440100302005290300c10300704015050700311030052024610940181081c010700340e0300101c00de0f08880ca1424030300075680e1139050407040c1ca914040d0180044e02c0c107811900c0b814130705a01c00d50503100240c0300d20b81c06614485441048810386000f18084010800050002c01c3c05860f400c3c48240d400005c200e2250780799000b107800c054130788800400c034103036040a030002c943c2c01c1443d80380c0c091019001440303180b910480080d92801e010381500e0205200c0e525003029501e80c0c0102e000000c0c0700208880b51541d55984140c000d00c145840c44107240120b802200044100d070341140d166415145207040700c4d00c50345d010090164848008040150780c1c500c201b041a031164000d091080303500d004240d1039460220144016405040200860030345440300003000030350747c40d034501400301c2d080c500002c0380c4900b01c0340d124040d03420b00450083d550846000c4d008010340c540060518100c103580300c01e502c0c5a6500107000d0060402c400030051104000e05002442 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 69454462 1250 69453212 69453239
    0x30b07080603030d06081b0108060a0302120a02030105090d020d0c0b151210050711070302030619090b0108030702130204080d0f020c04140405060723070204061a0703030507030501060504 82
    0x40c1c00a098074900b05000120000f100d10a9100c1c07043d50300300300a01d43d40341848651211680f1003e080081e00c510300000010312100040c00002e200342c02d00c003820740008004101c10140c20740e0140003001031742008904155100c2400000c003005208a0350361118180c8100912500e007580000b0f548003548542c04601039545c02c0d90f0966030800410752000c1d2942208010343c424051455500060500b040c1c003008140749689410000250310800041005850014906500c50140300000f00e4107029210702c48081d0041200160840807200700125070300e40080300801d8051b100f1241481000c0b64600707074105900640c41040380c075412480c039590a41c1d004103101080c051241c03040c0c88905e021100000e0898071091382c29603032403901078100300c2001800c124040d00f1a001e0b06001710407450041d41c00340b601e0800d0841ca0400396000c145101103458035001132010f0009101d4510b034808007100c4811607038101190907400241807070040340c10603000b403040605955140d42c90307070315050034042c1840720030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 69455712 1250 69454462 69454471
    0x20a050621040203120304030e010f0516080d0213060207080c03070e1303020a0c08010209240304140f0a11010f030b06040611100203070315060e1e06070f03020f070e01030b0708 78
    0x502400c140c19000417815801188910300c6170701c0761031b090200840014100c0d8030301005401488000c110300410030500c61000c1c20450ba008158981d01d0403010314400190141070350300795100400f543d01045072600814040141d13401c41c030480300b02c403441e101007580c0d814035031085103500040d51020a51420101c1000080c00703010b40100e40c00c460345541c90681c441c0559005c02e045960201d2401c00b40d2800a41e0401c0f04d403000d01d12084c1c0d04250301c15122031444041c000030159240448126040c0c5070500800541c01c4a07002a10ba078006c00317091801101d240d4140041c0082c00304d031a00032780680244540d0f000c00314060b0503140dc02d8180041542c081c1e06c90122407642d0301c183e40e42c21900c0c034945d0002b144155400d0303a0100362405075184032101382c1c120790004400c0c841d4540040b00c80c2d840d4842d9001d02c01a20782c60014140c00f2040100718503110740d010103070000c900d0359440e209054000480540d4901004129003555a0b0f480d81d002c40c001b020b010050400710014082182c0c20301c0380c0781c2c20740c00c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 69456962 1250 69455712 69455719
    0x20f01080c07020915011202030c030c0a02070306020a0503041a070906030c0302040909140601081506010525060608070603060501020327031e01050703330909060207020a0506210402 80
    0xc0503003d80010b5052041112201c1d02c0004015070100c2c41d50f40300c0c101103400206200103505506006112900d00e010040c2440c111080c0450640704441c42005800010350304a5421176880780500c20003829a80104e0703054880b6080e0b078403111091080c0003002e03881445240c1e203515045041042c02ca02400d09103400c3c800b0581c091101064902c240e1054000f01c0b0701c950704400c140044810218200001640541c0603074109902c445036440007508065841102443d140340c1d40c1c41000807100c1e00f80340d0450400d03901d11500650740c0c100811944041d0940d00d17120125583d0560b00c41d03080741900c14a007e400d00503002402a04500344c4070080c0d4035a83c2023165403603c05400b241c00401d1800700c0340f800208140c0d0154a04415000080c8106500204245014400286681c16421045010b8080d05000115161401c0d11704102040c40c100600140b00c414003070300100c0d080660103900a02c1041e80301e8000941e0001d16032409008407840303060592907015041000d101c0c5000e42c450f0081060380c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 69458212 1250 69456962 69456967
    0x201030b01030219020705090708060306010b0d0212010b1e0406050f030604060504020a050a03060f121514090c0906040209010e061b0102161202070305070b0a0309080a08010810020304020f01080c 86
    0x4401079044134000c0d40881c80c0e000b40030440c0752400f00718559a0250821041c00600c000f80030030303a10086209815640e003003000c03075070765403204050070000c2c40b540c02d211000040c07102c004110004000c00400100f040f407115122030034040e081c0e0b40c0803413280b4898000419070802c46841007042e00c101841c0d0240e0018070000e1015510008035050fa03100005070000204001000d4035815018814500078081c00710f1040480d904015002c6d040002d1800060003400e60000000d081040c80d401850f42414902549011800d11030f2641e551503610040750741c070400240380020b04c41d040c58030980c3c0f1148816990400c04108600602081780d00c14146440340e1400903411030406503090000303207000c0c00d40070303582e180c840100d040c283c0d03a04424802540440d00001d85c10404103400290b12030541d00018003803980c03116049030580040c100705c00014214080491000141604849203504031031054080d691050640480034049120441c0e0003580300d503c00301d520425511034178105501c00b808144840c03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 69459462 1250 69458212 69458227
    0x6140601032c160326040f062f03030a1a0d020d0314070305030f010506090f04050703060f090504030f0212160206040e0901060311030f06040f1a0a0f05070c020d0201030b010302 78
    0x10300f07018080d003095a140c060003620031030703c040c8954a4100b19003442082d509241c1002203440d85000507100d02c104100340403554200c45030709007030030300700b02c1a440b109030800c14840c504840d1241c000f00c84100c5d801d4500801c04034005424410452044c4000f08219a20300466080015030203141034150200300c59080010f140d582040f000300f6445c0d001c0d4503810b499162103c104060070758140c0086001c2c180078011a9610f440e95072401f06401fa00702e402196590741c40e10704800902e01584014614507411800044020881c2d200c40e00682c00380e0740301c0103038051400040e40d48000703c003010002e140040081761492820683d4440b0007030710060020f0b06e0255114281c000c0408265641d9540365500e003010810805840070381b010609064001d08080c000b9018007940b0380341c0c0107101800070102d08103200c0402504180020440585581300501824032a1004005024074038011228901d00008900284d000b003805224090303000f4800c0d10088490360044018020380700340241899005e00404 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 69460712 1250 69459462 69459493
    0xa0207150c14070911120402040e01020d06030b0a0f0902151315030c080f010b0912030d180311120a030b0102010603051e16050603040b07020a0b010306140601032c 72
    0x34040ba00014001c180c218148400760702100d680d145141c0c1012401c012000b00405c543c5140c0b130348250110340018061038040700c51030185c400d1002c140c46252401002104001c401905540642c40c00b220800230303803241c6a242e130112a217054000c0d50010440c04000d098800c010001c001e4005150300803010f00da038035207084248a142490440210b501c0d141d01d0102d541d800260320781e0091a40c06030921551610303011540b81d12074001c0c1180940800c010200c804181001102c502c200c6665003009480408082012040c0d10481c0880006900c2440707074114280c00904100855100c145d4a4546511010b003500180007512415041d5500e8a0000021900921050329000c0c0c0e9901405d031100707035007480c0c2402c05000786854980000b03861030031301182e2150710980e035005600c80303060703420b9464001d0b069261a100b00c80081400c190800080204407081d0402c6810002d03800900442d504c0340c5005501b0345d600d4056400e184000c001003441404c2c88000b401d00640d0708901501e10203104903c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 69461962 1250 69460712 69460733
    0x71701140c030405010c02070501320403140d020c011d0102011409030301150912030f05070b042f090f19020f13080d090e0406060b0a080108010b060a0207150c 70
    0x1101403501d808010403007400781c20301034210b00080d24409422000d0410001820344030f0316448801011081d0750703548c0c03050000790601c00411aa01c2c0c10458445030740c2d107840d44050a0145202207240101c0c1c003001d800c20300001e15458690340585a62444507950640040a2401d0b0001c660440d9251a402c00c0c8200008440c18090381c504030107950b50350b04145008404081d0500d0380001c000c1e11207410480214240b00300a40c141d030500c1c0c1124582c8900004443e54020b03800c5c0980101d00c4141413000f00140002c0b2040c07101e2101300c21248082e80c81082c0d400500103080c4080c1c010385c0d07a000094050141c070b009030340d0245030900801d9003050036032040812a007050b01d004481440004030b0083d281511183e040c010481c0500800700e110301401c000704160210301c40c12040105504c040390800041d900881c2c0900850341e801900c170001d00000800d940003e01c1080d840354079048016a02d8103007002162503842c01030f0003d0409514014101c00403050400d40b40d8100103003c10100c0000304034495 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 69463212 1250 69461962 69461971
    0x190f02061c0f06080d0203040b030c040b0a1806030204140904170a0809010501170a1509060207050303060118120f02030f011401140405011a090f190905060406030507170114 76
    0x100040d00c02c02c89441c0900722156600001c05079440448640040341d4000226010340300c07031050a5840352510001201c05020319002210604008984509210740c012141124607420540005a0542d9010250101c1c40349000d59001850f031034141205604160100380e030010301c0307010031289170b01650500d0501034015500c5080007070000b005124035220b00b4000e080c090180d800c520b0b5400883e110b10380d6a94031141400038030080080703006080031081640136282085d00408195910482440c205071240d2041314514007040845021401e9014104005d5044d1041d01c050144071018680307501040031140802245d1501c1402d071490341d0904213008107403010100b403040c0c5c6101d5040655203990507495182e010f0050740303464010002020602c00380502d0700d0f038011a4a5840c0742c040c000c10302000e004010160400e8800c171a03d140080300308604402c4031a42c0100300103d456107002c000941361180b00282807035125100c00c5c0f141d814030b4414646980d0401000054081344440caa12080c80c0889 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 69464462 1250 69463212 69463267
    0x90106031a060306030c0112090c15030e0109150e0a060e01050103020a150509010e010c02040e1b041407140c0a05030a111507050f1209010902040608190f0206 70
    0x807a804805a11a1880458503400c442d440e05510748030740840e941303a03070804034603041100015007900540183da110321120342e0080224102c00740c86d140da2a071154980c000d5080001e18003818025000c006200b5181a03562010441d041c181e00b8090841c0036000d0203e01100e075000d40120710700001c407648218400900508004903413589980100f04410002da484030a04e6900103041040c810b80c02011280031b1002420f0101d642038901d0300485008088a4009410610700003520651300c40004545115040e07000c2c0f0510704160039002e00c410303500011800f0300440d802c2d00114200c2406001035140890851110300c0c2454409102c081c54480c1c101130564407500002043d201c0356510601340b2100114880003404040c54480640c00703008002007003901004000304803480500c0d94041200c00144035800007108904208800714000d000c4000c04920551525800082c109000701e1105c0c0003080128081051499540f1080b10203a1107032000c90f8880410002c84094061102e07510b80300d4103e40c2e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 69465712 1250 69464462 69464471
    0x601060f02070e10050102160f090504060f05090a050105070c03050414011103040b0705070501030908030a1d030c01051501170f06010e040203040803060103051b0a0e0316030308040b1b0304081809010603 89
    0x3002a08003000d448c02080352103c4d140c41884100582c000700d00842c1c05040000030550340d10300f458001001001d00003044a42400c0c20b05c001c0400000750100e01e6800f6000030001e036203507072038181d904940d008c1c0c1c010301250041c0400c000b0315401490b0134030a044181040000d0715554188c082c19940a0b03001040030500101c3c5080500400f0000c10300584801e0074100184141501c8080c0345003c000c0040c0565907c9440407071881c44640b4251510a080000702e90f11026645040c44c040c1c282160310005103c4003201e840b11940c0b1812600d812000c00300c4d0809125111060b400000c1c1600415036810301030320601d240786c1515140b0080d8450b074040c1d005e0946908100000606440018000403030000d184844182a078462078212560480e0324100b10f00c4503c10031000c039041110400044880355080d100020501d0340107075280b0320540c03007144080000d661302814403c40e107500c00c820b160340c284103000044c0054a0040106814824000c506420f80349840005c1d42103002604603000282c1c4a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 69466962 1250 69465712 69465719
    0x50d02060106030213030809010e060c0a02090f0402010c030c0503040506040f14041505061305100503040b070c0f080309010207060606020708010b040207111909180309080a03020601060f02070e10 86
    0x1440041c1c098082c03480d003546090f604141d800e0aa01c02800007402a0b5000216103039140c1c0071314140703a00114003030001a1076100681c607080d01c441103040240c1c05121002e000a40e1204940c018a205541c1611085d1103222242c400f19603914201310200c4251000f000b02041c1c030741c0c601010300700400d513840d882c505980c1085000300f80304808040f083e004a0401350300540c000c00410005040e101c003500c4168841042d05d00420034503413603610440c0c001c030b1086003010340203901c60015441580200312840c00781d216000d08548584401030003030700701001003040000198101004642007442e1038005410207080e0341712001200e940768041c8026070700c00306d030030089545d0a00410700100c2c412113045080940307685a44a40c000400141b6106900356118007108440381800c0c5c4000e0a001382d401c1081510b26100c01082100044082c3e0200300c1c017a2000440e44000100d81c045c550f490345c041d00c2c0d00c2c0d02e000d400f0740e540f110031940304095002c1c02c10045450074007005128450b0508152014a6501c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 69468212 1250 69466962 69466967
    0x1c1802040c080403080c1303060204030c03030f2303130b130203190809040207020a0f1409010906050f0d051c0c0605090106050a03150b100c0c170d110109080403050d 73
    0x200d0741c400000d10140d2001c120100c0d40022040c1c3d48118140d0380103076500004c4201903074000403500001c11040c030114004c03040c8504601c403901568466150004042480d580642d5400b01603491542d4050f005a420041c20f0003040203150000300310b1405807c03400540d51244503c070012039201031403081041e980e60135890304106014502d0344d0480a0304440083da00c030140944944400030b4001c5800240140c2152100d0b0304070001000084400c18040d5100e07003000344912a01d41450780710354410303800410410f002e8170846040310f000a0840c00040d80300d0040c40f40f00700c0140c800343c546020f101c22100e59442c01340d4103030020072869030751100144514034100040300e0380984829210380c90542c1c10701807500c464a0305000c0d60780048007044542d080c0300619020300b0b4141182508140345254405010b60020061440307584510044402c003902d4648000c00b255a600c40300303030b403a40254184054503001d1626103003d40300c1c450010608106545568106138000d42c07084406134410160498800d5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 69469462 1250 69468212 69468221
    0x30f020d200307050405010318060501060206010e060103020405090103020d020a090c02031209011a01050d0204081203071101050403020d030b030a050304080303040b01140d02121c02010605030d03201c180204 91
    0x640c801c14a0304600305940c0091190103980a905c1c14156950081480c1646420002e08000e9001505000b65070f10b0300d02c000d4644a0a2003001444150040840e07801c1d80a4001c1c0d41c01d0782c10143c9108500d0b0703e07503000c1001e00005854140d0300191060f8002c14450a180500720742202560000c6076510f403c1c54511480d032a00900d613808a904d40112119510050340c41911030400910f4081d45503216042c04000912840e88004d485101d01c41003900100c0640c000303103106221944560742d80c1c5402c242000c0c2038403030032940180160080340c0a07078040d0f4000c2e0b0202100a8004c0c044074a40701e102d0395800e1941d1322980200006a0000c4100810010021811030140203558074140b003221500010444031080c0706402403003285140c41c081400c01003041210501c0080744000450044004c001078000c080700e002c0d031030207030003013440384070080d40a17002d40020310f040b015000c500980f0f01c0c514811b06810864068030383c1442c024030300c40000e0240c001c030210403080d6220140d0b4500288100403c84 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 69470712 1250 69469462 69469511
    0x31701030b0a0c0e10050306100903051e1c030605010e0102010c17070e030f1506030d02030703080c090301050709230f0607020114070c330f0e18011d0c07030f030f020d 74
    0x8a22b9401c02d000192020540e440041c17030304501c544110080c481010306010442416103034981e090300082e103a1303950541112080f942c013030f255143c0e00c01641004a00780d400d5010f809000c100340c0501561100c00c840e148aa0041041c81c268031412101800a410000701c481620301943c000c42405d40307800303007490b02c0caa00400103d00518001c00168400b035200d010311080901400b90500c00a01c848180300229100240018020021407820113000741c403201e10b40c028181c2e5007000c28540c1c2a400d444400c264030b20b600040100c2420320500c0100301c1503501c0303101d00b24100400b00d401c0498240608010f003541d54495201c0c1a202410b103011070311200c0c010100786c502800c03000c81c50003103015180803420a0701a685004450120041c0082d035200f07152081c1540c106442418a100c1c0c0c40600700c00505035000b095008001441c691070009815006031540c000b0070101700315486c0040e0254030400e0080c107042c1030201d0b0701103000d210481281c2180c950890050340301e02d003480214800c0d51441030388 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 69471962 1250 69470712 69470717
    0x80408010608010207030206130615060206071106072a050304081c0201020f040b070501060f06050c060f0108150a0b03071409060109031e110303030702010207031701030b0a0c0e1005030610 83
    0x41c02c0c55906c0082d90f8200140c4640d000040a503d40418065250010001c0550784d0380740c14041c56940500a5580c0710031a040d00010f000c2403d0300c20440c5000c10550f01a070480e84d582c0a01c020048840282140a00030301c1d03140c0640c001c0880d000441c2400a0b10003030081c6c501a114251441c2e0201030503595200040d0116403040203600003150000c0c0954041d00d00c0010a07984444032803501c3c50041c181900480d0480115201c0041c9196202005041e1882040d0603103071715407100c01e40c20b000e28900303000c0e0844d141c20807105480c506407000f0049520610700d11300442c061003007501080c1440e84ca6009940d0382e07665040140340c0c5040000304035030000000c4c60b000c0041480c41d00d940070000340d0b2005803000e4244080c0900f0500807041030200180c40020281c0356203080900d00a8000c2d0300c003485c11400315001c448016030141d0446015412280c010328143c41c542da881d2030450040c080c800d8090103010f01d02d01018219240e20905920a5507641c81d00d950700d08010003041008516034408108 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 69473212 1250 69471962 69471967
    0x40b0418050c0a1e180b0d0606050f03011401050111031615050702030306010c1e02210c1e10090e04200d2004020909130b0c030609070807020c0d0804080106080102 72
    0x681031a210701e0100c400801d0480d1700007101070f50440c00303051700000c060351144400902d602401f02d1680080120b131000c4822401606070300c81494280c4407400240d014031000480100071075400340740d660000910b45c1007030300c0c038182c0c0d130445041c0003941420040d0391030a13039903401c010304502902c507a0ba004030b0980015400d41c031f401c0c030000301880700d082001800703c403000f200e1603040d50001213015200d070742c0286002a24a15400b00c0a134a5120680a203c0c40c400c4942803286401d05018200c401c10303051071071501d94950b0308240205180c007903480a040150101d40010020a1000c084d03011b1885002018034407001c60302e00710300c4003070305021051241c01c1c0c0219120005e500801581c01c0040c8003610442180c00d140001740c001c0c01141001c94208901008201e212250031049054103481801e0748001501ca940e1100700c03500088903c83c1d00084c004010401250060085942c001500d00c102c0b90094010300105041540300ba01c1122072080c0498188a5102e0a0180744040e210b540021070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 69474462 1250 69473212 69473249
    0x5010b061207140409020a030207050c0105070c1a04090203090a050f060709090906060e070c05010e0c0a03060b12030d0c020f0c0a0b031008030a053105040b0418050c0a 74
    0x806020b40b41e141800307550145094614040800c0e80d00500b40c240d021515401425130140c00396006650407210b5002c0c90351300413036640c0154203031200c03544c102d01000d43c1d09081508410119000b041c101c0c10192042c071001845039640c0c00110303c50710440c8090400d50000346131051a00140c1070318044503070880703420450300701d07846020682226036000c40495005000d0030040c008207801e4000003035101e0150304101303035103801502e07000120303104400821010510f901c6c004c0e1500c140700c2590f54061340440040002c502c0540110100e034900500b44050103202490a0740746a004646d03d2280035110050940503540600086055640101c094420a81a080001c000e00c2c42c80c050038064600c0800442c0c0c0d28500006403401506144c42181d548a12014018000b031f001044009128000c1d00004401140340580d910080d0030202c0a80518a0400e002c202c05030466101d400e810a03541c020703a02610b40c0342070740c5000303540c01600902500129035092101a82e9140c0000741000242d14400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 69475712 1250 69474462 69474487
    0x12030927140f06010309030306030204050411100e030a021e090414070503070308030f041e03050304120e0f1309020d0f03020105010605070803070309030c051b0a170c060901090506031305010b06 85
    0x203030f00c407100b440c0c009405000c2e850700764020592a0030280d005807500c010041001600d2420481d40718003240c4411a2490040e03007181c403109608105609500442110401814144542c0300052441e1030040288403103c0c02040485d8421502699040305400c105007610310140541d801800068014101e41030442d2210207a42c40040e120b815052100c000203030900c09424611903491502e81c2d4562410100d40c00c0c000d0440e002a90140d440060f400000300d070303041c002d50070540802d501600b802000700030f140400c8500105144104002516400c4072001642c3e01d500c8050500d00c24414103181e40302a0800900310340050b04084140242000800d0108500c101601e5010344c5510b404a00303042d052030103e90308050008000c040c2d2151000d1050380d1070b1503614a840306401a84e034610355a84e100380480700c4002c040c0341c2c1000c0350814101d1146505000004101002041c11320a58213541e56010405a501c00c0340c0303841000400c0421801003000a024031414540c0448080d803c207a410b41d40d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 69476962 1250 69475712 69475741
    0x10c030e1902090408070804030b06030105012c0403090801020a02010207050f120706020c0309090c07020f031c05030a061502030406091a030705030718081e010905071203092714 78
    0x2e4030401c3d12400040410280008444c0c0302035111110342c0d2129135030310b00210005002c1e10800e10a508290012800003d19030f00140d01c01b4403141c4480600c0d141800303074444c40710090030580c00c101200c0d8001c240c1040900081c003c0c01070660005035200054100103003031102081c92460142c104054640c80c0e00c2030b44041da0190782e004040160f40721900d03811103140d0300c6031146a641200b2480104650500c146014044440c000c2d01c07c410b100519000b010744880c840c2400360418280c0b03405031118240b00f607000d56804211701e1000120b85484119050980c40c602c01d00380010380c4001414420a50322000803030040078420090000380d06138020041040c00010b008608010b00400002c0066201d0060f016004031040743d02000e640e02c030b0950350f4945a04840140e00104246000349902d1014410f8100c91908103024010203424000d110145041e0038000740d00308001c41401103030051740182c0b820303200c1e60b03000120784981a0b207100d090203645120b51440e0441c0380710402c2056082c195000b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 69478212 1250 69476962 69477013
    0xf0f050609100e0a0e010e0603070b03070e0a05030604060c020d0207051c030507150209031b0a260d080609070302090a0603050a020f040b0301060e0d030c150617010c030e 75
    0x642d40407082e036040c000c81d040b485085405521011304400001e010034101e0010703050740d26484d001201e6540d5081810382d641014490f00c45030f04410800a0300c0382d0320034105c551825000801100710941e071a00040e20708042920300ba50030303070340e2420020140c0780c040043c6410200140081d0038003d14040000e004004071010074152040b4840300c850406215904a8114551100f45420041c002c00d580d50020f4000782d07a43c9010b48903a0a01e023901240c005088021030300000d010460780c0307040c03400704104007203c265007003901001c00c101d4001c4080c0500500070581280e913500400392420608100f00740c1005013454061510421040c441612070503110700075105d0714103001c00d40c3d4607544001c8009108580c52680d8000010a021407010301c048001e504032892550b41602c034011140420103061501100100821161440c00380020a600c13036984113001a80320001d0303501d40d103d20722250f442a210004001c2d075595032400c0b14081e010310032a40540480310003445170407c02881c2001c000003140 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 69479462 1250 69478212 69478219
    0xa03020a03050f09060d06090506040209090a0e010209060c0606040612030818120408011a06030609040f020402090603070e010f0906200717070306061a0703120b03070b040f0f050609 80
    0x200754085000f4002200c01400c4040d04440e81d820030011460001c01c203034040c1041240c20100451680e04c6c041c0250f8900c910010f0904040c1d88079101d0900080604003900f0342d05540130321401d0340543d214006003141d502c400d0301500700303850500308000c100d40c0290030034801c1c0c2c40034400340b401080d400364241ea840483c0c0b1403c1c100c0000415003a9240264403901c085101200040c040792942064004492102030340d14048000c00c034000800c940c50000302d0b0215041242c400000d004901000e0b0005030b25800074000501d012003200208015600c2102e400c0045580d4002c64809560302100d4500b5003070a510b0500101d60600c0d200501030310340b02d00f841c0c2c0000d8503220114161002840503e009000455605681100071400991560b0080c4800c1c0c6495140200000340c41345421a02c050744801b008001c1d20703000d01d96800b61070480c079045044003515a1610401d0070f03900c08001c010007405c554416680c03140c0c90201c0c01e100c0d09400c5d4101d11400500340324108065103414054800404c02207 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 69480712 1250 69479462 69479467
    0x81801020d120903110712060b09090a0f030e0a0f0e13020f040c12090605010e07020d020c0402220b0c01150807051507060f020310050d0c050f0301140108010506090601020a03020a0305 81
    0x10304080300d412041c0d0310141406d00404000250390704105000400e40c0303120301ea080c030540d43c0b098200720416a0880306180d59411000c201000600400b5455244600c2805c04000f100c920f4400308002411a4002214003241070301c0c2130084140703c0003816840040328044c101c05085c2daa0104801035880c2c2c044038001c7da1203415401440d40a1a012001d2103070344030b01008000b6041c00d2090140c40c0070700c038960554540e840402c54851002ca014410484141c00500c1c01000740002d22000754415580307200365820000c0b00020074103030381540700020310540c0c1c0d03000c0e121075540942c2e41c21035000c104015a5000040c004003c410404101c00e01240d80842d0318001030400122920018498054001c00042c80d0030140c0044100583c06940140c40000c01d240d501a10b030002c0c40704015208001500620344c0483c00c11a40c90b25031105034094a004d070011410f103010f0000501251800e810000645c0d440700108165420003188440e03100409100800307210009031406501c80000030030240801000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 69481962 1250 69480712 69480731
    0x34a0c131a0d0503040e0f09060705090a0302060a020604151514011b030314010b0f1801140c03070605090c13020d020912060702100209030c040e010e0109081801020d12 74
    0x15444401c40e28100980108418015450701580f254000e01544c0c03500720040c2c022907800c0c01e512440c4c510598a04004001e25250244142c540d9041125041d0380701c0c0c0349400100042c0c44080140000891507001840c46d41818038058844401d400b00f06d011091502401e9000220822a26070407560200c0360b50707010842c02c0004a8019001e1400c0c00f003440401046c4404041c0d140d4000150129410007500c82030743c80b10f100d00707084e115080103529402e00910030444181c072100c10198100700705043c680340390114030810022540021011080507000803a4660511400b0701403aa800000c84014021a140310303800902506100710380714001c82e42c0802e0001000d003880d0f045841440000303210540192004c2c48403956139604407000b03001401040160320741da04041c02921110300001703000d4070460381c6d00c40a12004168101c20741d02c5039925803d44e00300d41d08003841040b00450259411307a580310300d404e5401b282c400030001c4042c115403003502c40040181d80142c42d40caa044802e20b01050f291803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 69483212 1250 69481962 69481991
    0x3061401020c040b0d080f071e081b0a240f060b0f0a0c1a01061704050d050c100e21040609030803040f020901182406034a0c13 56
    0x505c3c401c002c0c0403c00001e21880c000c0d000760080c1a91030f1094581c6041440e45084010048840c0c01009180310400c6c040042c0111440b243c040904a419049401d04000750719048052521410102a11100784400041078138103030081c007080c0740800c1c0b0240150f6240c41c0307d148081c422068010306503c004540c942c505882001030f845040d803c40f0f483c0300c1c015000395034802e05640a11a110102d4074007a2900c00b644140301c0e04500c1a0b4020004e0070b81054203100c1030307a45900c10000c60344c0c1801031a44030039401d003640c4512101d2591403401031a002d039401d04081856580e4508454440509102c00c2202d04d9101601c130050f00c0d4480b100f241c0301c0d22185080001800741c0d41c0c000b0b52102e00e20002040e81081d50780542e9141480f2072048c080c41155030090b54009480d248008001c00090f50240035890098024840c0c0603204050f103a01c0c0c240c0544070041c08034007520407140300d4640d0034452080d8080c0301130f01100301e0800c4001e080403205001c0003419809540075645110cc3d19100501c02044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 69484462 1250 69483212 69483229
    0x90109080109060510050d050a0206030705090a030f0b0c12150607050604110109050a030215070503040812070507090212070e06090307121e020105031519030f0303061401020c040b 79
    0x402200910404503a0303d04400a404e040390051000b81d14864005001d1a1013010041a15082006032003544071719001d00c0001d5000070306120500004108070009502c8540903c0b004501900d145c0e20b001c19a4a41640d1046019050241f100014040c0c001038034260740019400c0811502c01500005907240419024041c4000140460051508100611044801030300081d2801da82d55911252100e0070041220050701010307422555054001c06902c025100910150f800748044900f80f40d550182d10703140c52a03100f101b10200201052034010041d08005240142070b01402c207504000380400030342c01c0000300412a400f0001068034188098036104122201c5160141c1598502034503903030b99901d03902403103400320780410380910142d5008861100114240e94141d48461841d2a50202c0100c0c024401d40000c2d882a60311040780310318800004828021441007074a05546006410054103c44090f03001c503004403030f00f00c0d060f1a0b5aa012549030442082243c0005080201001161140 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 69485712 1250 69484462 69484469
    0x120309031a1021020105070f0203010908070b0705071e0201090b0c0f120304020a031b120311010b010903020f010c150221010f05060301150215071d060903060408090109 74
    0x1c841101c1c0d0a210079100c011414860401d403521407003201d076a45012001c55106580c0306450031080d500580042d071055004001050158181c0808442e640e00068219412041300310f40c20380c0005804000c1180c000c0700294481c040d801d00ba07041028a8407111195a00751001e80408260304c015141168041c4801d2000342034851807680d00c403900e24080da50350703219091840d0140e100702c42e603040603920307070300110391081d40d028065201191440e03032011505040380c803248101a1100c0c0000c580009032460001d40d050082d55489002840750485508441180b0030180c1000320f075000500140c0c036042914035000c4020710308140684c3c1c40d03081c419028200041302d04640ca00000b01045c001135900d42194082001510080490341d0f034004143c1540710f1440f4098200360240700400c41500d841d070004410890070300590324030164440c81f981c0c00550444440001c40c118110440c0801c55070801e0140300c403019616149000c545c100081e40d100001403000b4540c0000095009069100b4544a0000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 69486962 1250 69485712 69485723
    0x1503020108101503091b03050d110318010509030a06020c06060108090c01080402010f09050d0b0a06060809061609030501020d14090c010c120e030a030314060a0501050706051b0412050f0a050712030903 88
    0x401c7d44a25246072106140b81e10440020502401c4807185000803084900381000400c00082c01021781b0010344981e00180071960b414090648441b02198081c00180110040750000e00150703d0480c0025040031000b80259a076503200c0054070719166000300909070031030f0f02400c05842c1081041c10866101e80103410190b001011110301c07404000500c8603403409411408814000c440e1185011680880d0450707000c0c1055010300301203950311803503410221210b045441c10007005a01c076101c00f0f0030385c0d0104081c00480d03a81e40d4582400d007102e80c841e40350058a000003a001031603020380000c0480120450282c842600d403255014004d00a20100c00181000f400340c50395a41d05c2d0802800810926020749050560740000400030b250a039410415150161a12410602a0b49540b001080f008010b0707442c042d902d00014099214010260009200c8400058034074001d519105003050402e4031400320581c8070203d0314002401c007007503040503540010310209a081c074504040741d00f0505540050701 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 69488212 1250 69486962 69487013
    0x1b030b0a0b041d130201020a0f0201021005010e06030d0203040f060503090c091303020d0c0c0b0a03110d0603020111010203011208280309020909120301150e04150302010810150309 79
    0x641d0703c098031000281600d52400901260b40d00c80e692219405400d2000340160030003c25030f40010324032400316044c1030041c8121100401079190301e40031100c081c2c01040a01000104108480c0f07820402c401480019102560030985801c0e0720740031094040c0142070600a02100003070b0724903000c0014102d485002041c0b8201030410403282c440010034010194014040d0780c0005621600400c0803e40c040e0b80030400001241c60101f1150560704009400c00802d9160040510b08629041c06029030b24488100000c109140d44005080c41d801c162403003001d03074014001040b015810b00ea50414140d081100305507616500c000170403000b01941070010311b0300185515600d60a600d544000c500601c01e5a031003102c2d071182054240e03101c000c45030b409201c10003000107100d8500444111a5444003600300a0003145600340010180da14511000c03c0b4189000d90800a641c1e112a9454010b9011150346146505200030500411501c80108007810780ba020044c040101e91083ca240e4109200e84c00d01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 69489462 1250 69488212 69488219
    0x21060e01090c050118060807030c110d080702070e060312070305040f0b040e010e040b040201030e0703020306130501050115020a03140d0207060605030106091a0409030e030a0501020c101b030b0a0b04 87
    0x950b00055002c3c1c180015500100000c50303024002c1060309a482c00e89a01c021030f69503480840180c01380b0398130882000368250444c0301c6a001081000f004007002d4848140d18a4202c0000f440c0c50102d07032281c0c4200e026a024000292008200e481d440c1c01c0103040d0650b9a515410300303035614851a07000c00b54418920200080c4150348070701920940d04d61841d0488140d0742c07040c20030301d0090250380183c540b800344000308006601aa100c10301d65129079040ea641244d40780c000909000742112900842445035900004000b0300b84142805400c0e1158019841200f00c1d01c020b680781d03c01ea8005090001c152220307017034006c941d03050f24030b07140302460103540d1001c4a01e400c3c40a4501446039600030340c20000d0108000489000c1d1581034545074602000e6000440100f20181c048442d042d070070702580c091510500d0303c0034052840340901070310000d170740e400c2c0c0d2007142450580e16290380070b40b007031407c5020b44c1d40341c0031b0048001e5071014900e80803440e02c5000001805400301c1d03034040c0022220018000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 69490712 1250 69489462 69489473
    0x3041a09010c020c010e0f012f01020d1503030f1101020d050106020a1202240c07120206040b0709030c0306050601090f0810180b040b15030307140c040621060e0109 72
    0x401629680b603003500c100418404c01541d001c01503c1903030754040d654861805030740d48168a8030716010840c66141c5003545c0301000c40d0707000403d00c030380407081369400003a8800f0758605030041c2040c40c000c40002080e101d10750744000b4881c1c14030013140410480c1803603a500031000250107a030105103a180041103296580c2201035691090000c2c100c400318500c050721002d150012412107080040451002084080d1206903456420020403901c104175041c00054040b680d0382820203a0800f0540080115060a050500c3c003031030000d1610007001078181c02400040c881c500d41100700c0b940000c001c1002c0d1548801a0303450001500441800a5007803400503000b500000e81000310b640c000c008202d0210803511102c000c0d4403000d03000d032441c4800340203e00003d03143c201c03880d8040c80d103009621503050103900083c00c5174000c060990301041d5084000000d1041882240004a070440c1c040004034070700001002c1c1e50095001d041034501002c50644184019a0016078001440c900200040c00081c07815 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 69491962 1250 69490712 69490721
    0x20c01110904050912030c0a0306031203090c09020a14070204091506060e0a0807060e031002030103050c100507050601090b1206240612060405070302040302190305010c05071703041a0901 82
    0x80d02e00c110f091102060100d43d011459a40c240c001200c000e00d10365070030701000c895602080c0f01c02c04140d92818004045803170211038450011581d0f801140c02c2c2c0041c106072015166682000701c0303652040003440c6006401250343c0c42c0054152030821b031165224000900200f06140002c2e0005180a00c5d03401c0c840d1040e440541034800648616480704100418025070450034001c0ca1220351000c1010311100c0d00940c085584000014201c03010440c1072542a0141c0c0c00a0340110340560144400e8046460088030f8010762220618003e82007813403e4450654828040c403816030040d03603c0709001460b0300d070b0b2081ca40761160a40103c0e50103041940604003101050707060710401281204c510780c1c2500d041c10450b1030300103c200000049032107090400000740401b43c68042030690030040000181c42d4444510300081e24070840001c55031031400e200742542c10707501126041040403c0f4910008800a01d1100c0ba0544208000d4490340ca528003800350707290f4444034403d001380b40801c011650805420 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 69493212 1250 69491962 69491977
    0x11403090c0a4e050d0f030902010c171303032a1a04151103010302180c030a050702070906090b0f060f07060b1302040e01151403060d060f051603050f011406070501020c0111 76
    0x54a100144800c40f00300c08071230078103000a001071485003c02c0046420440340c04416240440d000b842c00c0307001c0d005400d40c150140d1040300800c2c03411484660301100248140035650f0010b208420b140e0580c0c1d5510204540e14003105030f100080c50115050151851841301e0301514111308002d0300b25402010001d94000348805c070302c9180040102c19202c60701510403809080c2c0c0e001d03030a0454640201c0c00b0301030074001704400110302c00c0000000b45045540240001441503440c0003071100301d800240700d004c441c0b4102540c004c0504001010f0030010b24011204825040400004c03030740a8a00090b51440000c0c07034032103c0500108010483c09802d105080c129102c05d10384506010a8140584a10181490b00080e8000a000151160402d1408400158030401c40000e0340d890031118441112000e0ba18030408030004400903000380d8140c41401c0e08186111560f521962400c1407031010702d02d40d0359000d402108041203510070400250166210342c00c4500081c0710764440640880103a030003c08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 69494462 1250 69493212 69493217
    0xc041e0605040204120305031f09020d0b10120f0603060203010e160e0303030610021e0304081905060109020a050f040e1603020a020601050f011403090c0a4e050d 71
    0x2400516882c00d482124110b1305c001c5001c100380201a2015211a000101a40c1490110100e05107c8241d03c1c0b021001074800140300517290702d02c040007a011540c120501d00e00030203805a039121460341006c0d80050740300c09007901050394107140703000e18081d101e1607200406590021001041500140c140544905d61007400d55000d00c02c0201c04544046d0301d00c0c01e403a09a001080810349a04101c20384010341903407401282c182c102c10440f145403400f4080d003c02003c0d00046428880100f046c403c092035102a211810740c0103109469071a01c5100c10700c18100c405030b00160294601e4010b8003038030a14680424002d859a075500101020000c080710300c0005422400009101c4c1c1d4081c0c402d13101b0f0070303015500a24140c0c0c2050288102101c00040c4581402032500041d0208032078800154131501b804009030905070000414044480c210350004491000348456065200c041e4070011680c00700c10074510703c800c0c080000480c09246282c825070341c641c4200d58010050210002e2500540c00569 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 69495712 1250 69494462 69494471
    0x100503190308060a1a071718030c0a1a03090c061308060c0304050606040905010b0301091a0105040203010315020d020f04060c020117090c0111010f150602100b0d030c050c041e 77
    0x104104440c440d80c09170022021540007400c03180030481c8044d055180c17103801085104c2c0c0c810410401960400c030095000b642d02c80c000b168040c07c0510414010440c240c59a407481401e00b014003c00b81d512502040744001e002c03000a0050344100012401c0e5440070b081e5a9a4000c1da804410f01420fa5001d150050321442c0082840d0400c84012244110307001809802a5142e000400000e0103a02800b5140c5640303504080302595400e12440861a00c100030300c480106124449154214050f031003544524811f02c0100b0105020034182c1c44039412014006a0303035004185103100038018002104651303440490040303050358028181c01c601038001d803507401141c640c144040c1150b110448803205140c00c641d18950721940a480101c010000c200700128050044452250481c3c07440101c41d10650852801004596014030002660713021110061240e5081240442e4101d9040840141041441c1c0120800d100081c09003800e12200148140200035804491800c8013500ca015600c08a240 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 69496962 1250 69495712 69495721
    0x3120712030c0804030f1d21010501080303091c110a060c0216051f12090807020108070e010e2808031309020913200d02030f09010b03060609100503190308 68
    0x803190580316540c0741c2d807116a4111500e074203c07441420122a01410f44903400d802c5400c2d6264921400101ca04130320032320001040c010b01c2c1c0d00303480c011380c002039503900100b00340a04c485000c2208403001c102c0a0000c001d04202034001c4956455030a00700e04180203100d40081040320940207200c6440d810307070860741d1a9055100c0300119a50034403c155120b92040300b203e40440c400b60f58003331f90f00564208182d44040c2c40c1d035280c09451060b802144d020030005210802c41d82c00882c2d998105c040761405440c40080f02d07001910116240201a02c0307900414100b0f071100c5070a0f482c0703032003890780d40101e192190f41e2080c0c8a607482c1c10a01460401d007810704800314003544103100391400010020a510300400180094200610481500150000030080314150100c940001007070500a10b1400603030700d14045145c0d100c0300e00c1c060318450059041c00040c00d0340da42c1c00141c1507040007044580324125142c03480d8000c00346074a98407080d0107015030741c60141c903801d86030324041c42d0740e00a441d84005a031b117 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 69498212 1250 69496962 69496967
    0xf01020f06040b37050603010209030304090506031e03040605030c19020604120c05070905040503040f0e0a0f02041d061201090803010305070e0702030f13030f0f110402160206070203120712030c 85
    0x84c5480c8010910403840340d041009000e40c000c5900b00c2406400149010042c1c00441c0c1158400d40016081540300c5092000a007010800c803079010341030510740305801030f8040703600b034507071003588511000c10a022001c560728030840c00c200c40490310101d410340106d0040c2580a5162002220b040e11814265075107517001c0d0340201d80f0303155144d40c410040c1c2840c60034102c60500428001c0c3c000c0d00d10340300c280710100c0c00700d408506d4000584138240c0c060500345011030100040e109442d010f070044034018081007103656600510300c0481900540f0f000700390341e1a040030505450001c605e28481f5800e00c02d404060102104c01035040c0c90180c015150196140e5120303c41d608000d40c0d5000041c3c1c410400c0c0915541c0c440f02a148101070030000155440e0749859003849040e0303c1d07900740c41802480740802d0401080c0c10100b90320a1050f6401d40c14000394100d101810103142c54041c1c0900340003da008119a014031026510b44124000d864603076003503081a601c0c0c410310010074800703c4e182c82c1700050303020f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 69499462 1250 69498212 69498271
    0x1060809190c0e0903040e01120206030f0414010c0c0308090312181606080603011409030301090207020607230d02010e030f0a030f0e01020a030b0105040e060f01020f06040b 76
    0x18000d001400c54074480700324100140c07900d000c159500c907031000000c121028280707090b60259200f440110740722810000a0015504103921080c456041c41045a0068440c2c4050b2584102e001082400940e120b0403d440300902d02031441700c02c3c2d441e250b04140340726042121a59914000d59504c40c0c03507030b07807101d9007940c1780308a040041005001c1000951247e00076105151008410425140f01c0800f0a060100d010080e4110b003001c02c0e041c004224460400b403040000507010200c0158040c104021110789074801070044415440d000254041076489039822144001e40c80604031044150038450400000720710590f250b4603001ea1200304416a105000380100441200055450424503060040480e4061880f00b000d160310fa11310307481140d019218100d000b0302070350005a80d443c0034a400138225018500d10b44c0c140320090000f4032a62642110300d039481042138038641c480c0034800300141e150400c40c40003c2c0681c8600d80810040010b0508113900804030404072115010302c4076076504140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 69500712 1250 69499462 69499471
    0x70b0903030d05090a0b090601180213060e01030e1f0615020303011806080105041203110406050306040c050903031b010615051206040e0a050105040b090303040309060e04020d0e0f06010608 83
    0x141d0081c40b50b800021059400603401c0104041100d052454070b0b80d81d01796004084450007255080780c001040300b010303880d1281d000c500e501c250840c5403401e00c90720981e03041d00c140100f03420080100c1c007021081c0d0007075008120115400c4100c606280718801190448001180108070080c20a034000400390b02c016101b10034501250091819030382441455101d00b00d401c404604203d031107800000711918288160b5020b28010b18a41340561003250340030b8155680c0001d4200303200010003003006440c0e4040f066a0300040f084401240300710070050104d82d83d008151589506000020b651030000804481b4400d406489000a00807541d5079100c41d00e00000c43c404c5400403c80802a160501c40c88140c0d40f03901c040010130014043c030940c0c030b5552802c0d008120841d41c2c0d030b40d50030510092115446c2038a9016a480d00114650303c0e040d540200054a144518001e02600907803104096039070f501a1172030080000410001710001e07100e05640c44410041c000d100740511000070a80c24410750040b4842c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 69501962 1250 69500712 69500719
    0x50f0d020c0306041511030403020105040b1510050c01061e090b04050705070803060a18020d141b030405070e0c120703060605190309061104060207060207030f0308060d020a0611070b09 81
    0x40c4c1d83c81d9103440d1586102000884001c42e0742e00c0c41d000e0f10080c0c02000d180124013a1340002070a2030940780c4500b07020f1001d0720b11f003078003c05a04040280d64034052044110a082e1400e070307480c2c4103c09441c901408080c1c00c0240741c0b8079600248101513098003002003c1700e400b5001801075009003c00c3c00100c507000e46018001a2080280002040741180156086880074007448111603444d9032000342124200845c0104a800040950341040c9034000c0e2580008201112809800e01003118800907802581d452448080480046d00340541171091100802c0d241d03188d400140b40a011450082e8003485100300c852140c040446c0310603100780302d84420340d51203441e41032410300d944c01040142100800d072041056220307138110300051054020718a84006904229403074900308100a0704210454022504541c0460000c0010960103150f8805154141c03c040e110743d1100700105148040e121006500705004000c0000d4030341d80000d42107041086070303055618103034484560400343e1044034031081c0e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 69503212 1250 69501962 69501973
    0x31303140a08070c0807060c02061b03060901060311190203040303080a180312060902040f0302040b121c090b03040b10062f0a0c0306150506030402210309060403050f0d020c03 77
    0x895600030b4030383c44d203401d00030101141055074607542c40f000d8a000c0350461005030060800e01a10041c1554139000250ba140001c0d41146841c00218840920500c0340004254441022942070070b4030078111401c5c4280d900b0034048155801c08040d41d030760b100b440300718009000701001030055042c0c0e10480c41200101d01021b207042042d6103040350f030a040e25030309000d15a50b910703000a0200c90380c80180010440622150611071640c01008201c0e021040743e540101c00340c0003408150704c0049403240614080c44200c5d201c05200c142e08076401d10654021010f02c1000105200500c68003e08541c4103a8002201c2954507407985401c445034054604444103e03101c617450040d00e1400041c1e0070303010b4907540301140e250160381c0e00d83d103e89204a42c0140d80e143c2e5502c891001100d4102d0a1001411007600c12030b103542000e5001c941d6911921000f8003101601440862190405008540701103c0080c806030f03c450b10780c1401c640301e101000b5404d81620400034800380c4140045520016220028003030320 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 69504462 1250 69503212 69503221
    0x108040f081908090c0d0201090603020d060302040905030310060e06070201110c061606050105060711040b0d050d050a020f0c1012150308030402030c040e1b060f031303140a08 77
    0x822803503454008a0352071400b03100300c0c9140700300d600036018810429550b01505080143d5010f00f0030b615080c9a900403040102e2031000750340c000b28a8001c0303608074640140e0701c02078811004001c2c5100e4000a51280c1004c1e20b901c107000b4000b02030341c024240c040c0e00c0480326649a100380c50710f50b41d08540c2034000106000c1c000256000350100c458071001d60080c0e80e031050a8500142da50791207005889035074850006040140a0306d4461b95015040c04d8034000d24081158032820040c2000640b01845980c59001803405501d525005201442c2e2040c11250b000e42c030182c02502035040081d90744014402d0b443c90404801000900c401d400d10080d2100c4903c80143d0800c50303140384403480b0014011348440c0d11001c00700b020f4100000440c001c2049545030b0070980304041c102000360240c01e10540c10140c422000034404201111003400d8a0301c3d96100d00c0115002c684180a0780310481503102004c0100119403242e4054000f505100f0340d10b001042100c04254140c50098089110001d080300e000034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 69505712 1250 69504462 69504473
    0x901060e011107090504050d0f08060d0204020703020c030d080a0f060e07050c160303020d03050903130509071b050f0f061608060a1e050102070906080604110105070807080406120b010804 82
    0x10b60500b8424081e564543c1c0c403108901d00740e5001b070f10200c03070036400301202117165540702c1c103c1082c4014605e004940c504142e400101000c5183c90040c0c452070b80083c0a0040500070440c0012100700a01640c216003c01071016103041c0080301c8540d030381828201581160304031445028280d50780d4182009a6855034a400c40d0796406c61820740540e803158a9000c80c1001720a440100110310035030040c00403021480008040d120060120303884c03580b01b80520042c507030300103071200140d84080d40d06003090ba90344901242c00d1a49216a100c6841d003d1548106008020801403804481081114801c070040006240c0ea0001290a124039091030301c07800a019100312103103604080002c0088031000d1b2124820340807851b81c02240c81c48010044410882941c041c040c0c40b0051012081c01c1104500c0c014550703071a440000d0006080ca0444c1d0880c00301030b07004005580080341c104602549440407840e0100311076115016000201d1640008031012980b1402440c8240b6810380d0703003010070749455455 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 69506962 1250 69505712 69505727
    0x60803040b0d020d0e0303131101080105030a03030906021e07060c17040b0c0712020a051203011a03060402070f0c08121303061815060317031b0f04030b040b0103030e0901060e01 78
    0x600c1e5500d41c176a1494110a142000034502a00040540340e0360b605051912034000b484032010b1505104810004010390303603000ca8141000e9403d4240464030f130316586448402481140c07580e50700c0541b500225082441e4510103481003501c580c0081002e403c2505094030004051600c0e0102103428400082c0028032500240313410200c250044c50134a1113594901c1921541642d0a0005a001c18181d000b40034040280c168100781003000c01d441c55040ca04000c06030160107401c2d1100740e030700101040c4140c0702ca50480b410144c1140b080440c8801e0303031070107004a901c0c1d441034a00c135200d6070366130f0b0b40e08100483c00c030750361490a560080401403941e96000c019154110b42c100c484504000030038041404034051006c588007a520000b80ca600710300c0d002c103c0c1c50014001601854007441004503240030b1488129101004803d165101c90603070340e404000703200707540001700507900d00b800340405c1062080300309040e20b100e0f0b102c0c00518003080043c0300f0010024032030b00000442504030f2440c594026103c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 69508212 1250 69506962 69506977
    0xc120105100c0618150903050306010c050c03030c0303010e0a060b090409150e030d0c0503060a0302010e030709020c0309100c0f0602030a090b040c0302181033020c04060803040b0d02 80
    0x2032aa5403140c0c5070310b8080450b030030b80030241264052040c3c990204000c5044170f900100c500981003000744010344000f03109000c020704040c103000d010149101801070801c00001036240080c102d035075a1503540d00241e161740081c8506102c144224003c43c440031014015031060714a00203009041018800401001e494826000e441c81c00c55030041803140c022a004007489103601d00011651550318406003800c413041200c00e24104402413050120035995035480c44110398091a09900e840c01c0e48000130b05050459216a06440c070000d54074001d000701001a2010f00411140700d111003c0034801520100f14000004065501c8149504001030880d40070356003207131103d840010318554907030721040140010344007691a64880301c010030071482d00f1405200c3e1004408074010040c200b29031020080601c038021102d101903800904000d143c042c8024002d851034240d03a09203401d115400c00f940314003900143d41d0045080106c0402c032fa00000048804030360800c203c440c6440400707a0207000941060030b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 69509462 1250 69508212 69508217
    0x10f02060c090d11040504030c050d0903020f040f24090b01050304030c140c10050c2806020f07020a0905040203060604020307050d0504020a030c0303200601180b0307050a06090e0c12010510 83
    0x40d10003c40c0c2d240c5200d5984503612980342e9110002715401e003103240c40c51034824402000200c2c401800142c40e180d10b0040c00806c1503802055060303a071b480074000b8201c0c48005152031041c40020300400c2e207111744030030100c1c0d610f0708003000303040d04001c011075103480122406404610400340c45400503104900c0d4520030250f110a85403454035a1000030000700f016940381000840200300060a0710060019002e010b581c100b000396044030581148002c0000807034007604c401c0c0e01141600b0141240d00032508403650082c441a00d907629240d07480001d00381590164041d105500025441c1e08051003201d004814a4032050709050065030741c030340500002041280c10180c180c20000004032501074010141d84a51070f400c1120080c4500c0d40d8180c2c60f498000c140d164030500041009140b2804d184260f090a09008510300b00c0c1c15010928000040d031109800501e110400904070b68806450780544810160b9919a03480c1d40c0910300d41c6001c2c114142c0f044240b00001000940303480886001c25a0960 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 69510712 1250 69509462 69509483
    0x60608060411093403060e060d08031b07060501031a09031605160905090f070302130c0509090f0711060103050c09180706090f1502100b15030411010f02060c090d 71
    0x740541301010600410214505800007600c00540500031100541036002000c0d06602c0c0440004110940314240a000c2030b0303000001c103150000800700301141c0210300c41001c0c1d5960807032501c10001c101c00d00c4240c5a98100400c0f000104a4491400303010f101d0000055080c2450095041404040c1d03207411640f500c80c20651820080c03000e5540002403115640010302031412201c0740d41044084e07070f0030b50b10390b0300046000c0c00181e45d40600703900441e26070072000070340d200c0c40e200c01e03511440f0f071200382607010181c0e100300601c1c0080a02a54451000342d6a2424501d2020344200c0c2d440303400303000007001c03034207c517080300c101d8186030f102650300104801c1c40804485183c001c240c1003809503000000000c090b0b40c014420700c005c0381000d800620200e165a160401742080080d00d654880c0c200045071526844e41005a0740d42600e02c1d8860b540f801241941c03401c203450700c0c03060241c0b800030041c0461010707401002d8103400801e03000e02c180f40c8018041d10302a00c207420003218904c5804122030000e0031 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 69511962 1250 69510712 69510751
    0xf08060a230409110405070504152a050105070e0406050a0504091a0f060a060903030206060111030c0706210903020a0b07030f090308071d0102030708070804080a0f06060806041109 79
    0x1580104007a00d8007613000d0915a00d2400b00317200544000070700b546c003441800c001c04c011140c10500c0808501c10103184ca400c5d840004440c11340c01d40900c004041046d0806010705080c0301c0e0640c051800b41d000f54640c0b00ca545c0007001032100361051440b030700758441c0041d0002c000038205038001801b074510840c140c07980d844000000a0f1180c600380c41c2e2a200341110400c0000505060060300d014000074180b0204040c03469500a40e140c4000b001c4a040200d00d0780590762802c0204160340c0e0f003c658105580e030840d1901401001b200d00d00604400a030100a81e0421100742ea1050500103038042d4060610031925071a0401d03140c002070b040204240d50f420180d141d900c810301c104014103200390303100076190030010070041060b00d14043e900c800c40070120300c6c418a40c1e0004111607045174005080b5031115818280b514943c02160f202c1c80e51401003d05a1b0200008020303508003c41c031aa01c01c101150301da001d0903581e042c040b1001409400b0303d08161b680c91074401c8020303520046618100800404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 69513212 1250 69511962 69511969
    0x602031e011211010e0d20040f14010f21030e030607030203070e030c01020726070e060310021e0702040e10020a030c03050408090613090510060f08060a23 68
    0xc0036840111842c03800014541001040800c43c0340000092030022807604141c80042d07034034a80d151005080c04000c002c4503030401d00c001d070a03492510009004000c25080e1101d00307805455100f5560030551090b01c000f203100140701d41482c2c10360b20041e41c40960400b05017641490f950800d24242e05201c0c0d0103410381210b607000c0140610440e26030350050b860f828150401750a9844a0743c4451003030700100b080c1089030360f00151070703030864008490002c808901c2240032141899010780e0351946000745103000c1111000581d506004000503002c8441040d058420741080307000b0b4a44c0c0002c0b2014400c610300507503580700003401020380001d01c00291a03516001040c9411103100c1c00d904055004108038074401c1c0c2602c51410040413904080c0402e04d0310f540c4184e11441500c0401c0c0c441d001c00301c0c900a200d08108044000340a0340c034810401070401210307508440116204a00020f484130408012090ac9011103d02411024009030411810f082c101c0b08841c0c10200804080110703450002903594 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 69514462 1250 69513212 69513271
    0xb0105040b1303030e010503041a0c0f450f040e03030f0106080903090306041202010608070605120711100c23090a17060408030703060e07020f0706030e0a060203 71
    0x881003003142d9800c9186140207094007102e1001c3c1c1d4180102413080001060b01003484200380f00c0c400090b81e0300360761401400d064034003410810f064601004281c0d03060f400c5030040446025901203140402200358189074071085905c004c0c402c1c2c503c0e01c400703000810a050400300e000441000510104607629074050340340c5107400032200c007088203080b48010403500750001c0c1c82075040220880918074000300c1401107940c8a00c0944010031b4000c44048102d1010700c02c2d8400c0d4080c0010005840105e5500c5038000c040d50800c07100320312201c8040700421380c000d010f4591220410801c0002e84001000c441c034030402401c101c10340f00c041c8940903030503084240c550009008801c0540e03090ba03031101e41d00400d015480850382c0000800d42c2c10340c9112112014001511940f1070340c809046c5a40c0d5a5400c0c0c1140a840e603a0b200825520040d41032014060700401d611888000000c00c0b10b0640340e56400841c01d41701520241c2480d5044002207501080b19074000390780c003005a01701c1e00d651800c0d000800b4040c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 69515712 1250 69514462 69514477
    0x702040903020d030f020f091306090c0c050c03010b0901051c0605070504030515070504030f0510020a081510050306100e030714090f04080324030f01020a030608060108060a0b0105040b 81
    0x142c129100040440707415100ea0745010903403030400c42c00c0000704c68540c40180b00300d0809520072140c0356048095209c107600700b41d000d8010a03506014229054002400800d1000c4040f0750b03a0152120724817003424148a0b240240b1001401c1d071499920303100520040b19060301d410b000910041d280c00f00070034802c0c080c0c0c83c0103000c260341d0a030b587c41c95420014240482c03000d07910142001039040c41042503100090301d0039690085070000013080c05103400c518111860240b034800341e00110b004627505070803a480300c0c03140303425407441d40c0c54032200000c00401c45203508030070011800a00108801e41040446e080c00c0080506107030061191060000f4a0041140d2002c0c402d80344a001c00d401500388503140d84c0d00000726031032005550a055448407202c0c003004141602e00304001e0407156021400410f23220414002506590100c0341c5a482a800f0b5032140860720b010074100711000407141c0f400035003181201c02100c0503094546072104110003a00b101842070b810850241b00215001c48008000d2809 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 69516962 1250 69515712 69515717
    0x204091b06050c12032e0626040308090a0b010b090102010e120405060702013614090408030406090506101d010303050a03150b040e01180908120c0702040903 69
    0x409180305510480d86865005603007003020a101c61040707810001040280040541c00391926950342200c1300360001c40000300d240120340c200401c03c034003021504400044e030310079907190b01102d1420b40b0984140c022050307901c501000b11600041c04644181d01c41e54003c5c100c0020b032000d00c1090340310207207540d101b81c214255080d000a091080c40d0f80921130901820b0058014041c3c038041c400000c0440d0280d489220f006000c00969482168802d65007808a030342c8e40038100c4218001c10014443c207045184003901414004000481c90403840d00ba40c240540c0f0090042206a840c0c3e51503691030741001d081100c0c02916041101d000803010702c009485072102174200c4105600e0411040141030000004010903110070300140007080d030200c00c88001c1170f020300340407500040000841304000e40581c025550307460040340218181504030782c40341c100e8000801d041000280c6040d01c2c000c643c4070740001002c0082c200300040d0309001034100c01e0b51241007417003524100388281d00490250303071035641d04500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 69518212 1250 69516962 69516983
    0x160f03030b040e010f0c032d02120112050c0102010204080c010c0f02090903190801120212070e0109020714070e04020d03030e010516030c09030804090f1107080301060f030905060c03070c020409 85
    0x2021059124007000001c15180610140d1000041e1a1f84010321000c80f194041020159230320003600d540440301c0040d05110903550660b5a00c00c0484001090501160140110391003034030250f205009443c1900c000401a03e180c0070024010354400c3c840d0841100d8400e0044034100142e61070f00000e9214088520103980d030380740c92115a2000a107151021028814820018800390004401020500354191035110704c2001004441e131415090360701c21300711081444004980e9880c01c0d005080d0301403040794065800710802e006c8946403c2c840c0640382800085d01d0009000d40741880c90604001d0080c1030004844240314416800e42d9021143e843c4003400c600c0c01140c04a80c18828008240d21078904080c00909507039445d28a88218403c154469440f0060660302c0b1042d54841070103c074000258035922852443c20106a070000d20036440400d100102c0a428140240160101d86512130007030130301903642103840d00c04c80e0406403030101008280c501180c0144c440b4880c00600c02e010f4001440c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 69519462 1250 69518212 69518231
    0x2030306090c0a020a02040b0d060e0304081e030304030318080d0b09070c0b0406050a061d070e010801080703021903060e06090601051804060506190905061005160f03030b040e01 78
    0x22800140a80000500c1040326640244e4080742e40c0d4811981260080b0f048115400016050981040050b0009190110729004d0b82070000080080b02e544005480700c507c903641c41e464070040c003044a120103800810008000910903441808c4c04c1007004100b1105070410340f14000d040e0032841c11940c42680da00c2040c9a03d107402044294440514075010390000b021340d80300d40c410000130f03000400d000c3c2c0b02c030041080711480b508010050944040b0b440c0c0c0c0401008504a0485026515003011880b00190711515501c0b072500c2d241030350000070050082603d158240820510840810044507500c12404000102280609840d00c407038038008106600f000e0690604040040c1c0c0003900c20014050390b80792150510400b10351041d08107000041c0c0e5516600800e024131403e0030b440c034064801031b0303020850551343e070f102d40d002d020b040d90f204014050041069466228160111490900755204000092020010740c488148a0315003c2581e205040104080c0c485180c40074480b0703519a041d40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 69520712 1250 69519462 69519469
    0x70c0201170408160528020901050f09010b0c010b06070f031e090e04210804051b010c060b040608160302040b06040302090c07030309020d0f030e0a060e010c0303060f0602030306 78
    0x40c1c0c0c0300e4000e11004038160030165034002007441841303400f1885a00c11841801440018010002c00380d8500703036100ca1990440b02c02040b00e4400f54001c0b84a41806000820740e824090103581c2c14080141c28514131f6400d1000441e4030350032040d90449a50340301c00300c4848580350080907210042c400c846a49040788a85005044000c80c4030b4020240750346070311030440c1c103039101d555441110600d00c14108192528100f8001c220b140c4224038981c203125581145c410350703000e64a04d00c11170054003520100e0000f0a01202c080c2d150300e5040380010104446100400c103241d00c1040000801003000400f144e0390040c0c241084041c1442c0950408081030420560900d03011701e10484604031000c900d068110341c00200c070842e01800502034458003040d00404c040c02a440b9000668000309208184000c0f0b00c0e0050311503440b25400c400180c0c4200c9455402e0801d915802c060700d5071034803203058054140f80115036114904006030101601c0340c100050803015155070310082d0009602a556078580f00007807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 69521962 1250 69520712 69520727
    0x6090602010507030509031b0109020303032d04080702060a030b0d0309140306090717070b030411040609020702010e1002100509070f05100203040504020d020d0f051b0c150408040e070c0201 83
    0x1d98013403508010030000d80007804030442d01c03440c0107011110a0f0303209503540d80c3d0040211500080d0580f10010034881d400500188500915105400c8526100c440001c2500401400d460090910720207016030b0005141030741c0603000c01002842c1c0000c030310181e940061010503903c10181c000c01c04c4650140104407091030079498000e0242d000781003904000c40701a5403840c1d20310030200d1807040c000403208100f009001c990014030280c1d00d0300c0d46034206410310002d046803014420713100d10f1030000006a00f61036402600c181e60380503100d1843d1002500c042c041c3e412030305007800007103004d42003050f0161203486c03140324000c0c1d590030000c0c00702509051804594841541001c0e01c205900c42042240c40d03400000c031410303138405540158032900e4030034200c00a0b0190707000c201c609508218400303103007604540c0903c0c811020303096240070f0085050500f031060b00c943d0b00026025080103d203100200060065240c004c0d1044142900e41079503101d5038079540300c080e038210001803c00103c20040d9030b41f2154 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 69523212 1250 69521962 69521971
    0x403120b150403020d3e01090e0f180f060a05060f0d061503060c03020903100605060706110d0c02150108120306090414060c09180402010c020114090406060906020105 73
    0x1500420740c480741800c80c520340100c0c0710080c40b0759030300f02468040106076041b081e8240f01c0b2000022045d040078141c0203035401320b0407807030507541000c00b1001c4956103d41014403c940b220817441d03009413203a1101381c41d001c9004000c2007034007080702a1f2042070ac90030000e0714002c03810200078251904002c491481590400342c5524456514540c0001140ea1001e0301f184015a0180c0d0005884c40d00070948034a841c1c0aa2001d814589490000094079030103400800000c04214242d900107070b2000c00120484846002e610b410910034410341e03001640640c050fa44900000402604042d44000c20100303466078086003030010380200440491601e18013110601512400d03015010b4044807a80c1e100050000402c1648107200801c003040a006c401c0c012981c414100e041aa04d1614104058611075448100020700030130341101c4c1094900d440307100160199505030f507072003100051034004440c41c1900482c0103070075000c200813141c1107941e02d1003840001c2c016510346c00201c624010b17010b401c5550090 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 69524462 1250 69523212 69523219
    0x509010c0e010f140304060501080c03011b1d0910030201020f010c020303070f0c1a1005061804110d060e04110409170a02030408120304050c12150606120403120b 71
    0x125203421036801940080e0301d00020302e4100c0c90400426011285a074041c0e04103820460000701b4002403007003039005981a940c0950845102c2c07461541814205c403108200c3c04a8907040e4404280c6603403003145803034080318020703241e00f00d440c2030440007410f6500300740d40e11019400440810070441d60180b202c4a542e100030b50081107000c0e11518040d440344002072400301041140c0840d851014016840000603a400046106200d81031840c80c05d01d03000f054034400c020280e81c0500246625221040340c0c1c801c21100c04d6103071048402410310000e05194034443d4540c260920040f03d00d0745041c071071040245a030354401d020a08141c203185d41c45081e141107050085043c003d8180100b51b10807a5200700650303031111a982d400d800003003203003180038070b8100002501070004c0c278150071000100614083c074010000c0c1e401d80f000c5082040b01050364641c3c06e41980d00315900100110480d4005681d00c0400541140c1c904480c42c06204a804412202100460780f29a00441158018400c5418201003a07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 69525712 1250 69524462 69524471
    0x3110d03080103080a03020c0609061b0408032a1015050105090603040f140706091a0a090b0c0106050d030503070305061c0602030a060f0b03011a03070507081b030f0d050901 76
    0xc0d1402002110705000c09800150b000501ca203170503100e5811a14001e0940e02030780c14034104203c00da5211b12098461101010780030440d19140c150b030204480441d04501c0c000c510706080d800d072020989041c400090300003d0101c0510103030f071000f48110000c500b0307074a8001503191600424401e500c10303150804c074100902800b10750415124481140d4016070801800440d91420786005661082c0d140400030743c1c0d0042c5007000800d03035041040c81050783c11528045000207000e512450441c011001c8010000741c40c0e02e403c10980c40110003c00e0300310403100020503940e0710303a008901a01c980440440001d1070000802c030b0415030500c1641e800c00b008603150540b0240c030030050007516140c81b00140280ba80040880d54400c45036201000800c2051340380750300103560342c1540045410921642460b2844d005044a1100905003100d220741d0880d16001c1c00c201d00ba0321a054950410345401c1401020407a6940e40c9503000c002a010305240f0f071401c1940d079030308440840207480c405400c50320182c2c1403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 69526962 1250 69525712 69525739
    0x106020a0215030a1d01020a080105030c060405010f050d29030a15020a1803050a05060907031205031f0f141509010e0607080d0b0f0102060601020a02090a0b0909070311 74
    0x2540542412440c42075400340e03c0391102035090005000f4955548000304181410140320702c4c06401802d03c5102584490a0740d07a40d03041455100c90480c1a01544a0b2081005101130340c02840403000c1900b491402504042c80c0d60b08007c1182c0c1e024055640800300458003c1c1030305222020400071500660290012240d03980d55407918135100c1d12007203461034001c240101e0061282400c0340c4510081002000b400d6501d051150f19030403158001e40d4103006284c0020a40200083d24104032540b1084100c0070f0030304100c0407191500080d04203a514140301c050030003103082100c27480010f03005c903107111324000385840300c01580d181c1c02445203405800e4643c4521108000a415943c1c81c5600380ad04041c550b01c0700d0002481c600c2031050040c400d80d00800c4018040940f40c0c02880100c01c01c2d1001c1130030105500069030f5420089500c5401a4446400a40142416015a030700620161000f00701d60303030347c100062034001c01210080042da0120600b04140101d803861040440000d44580108012 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 69528212 1250 69526962 69526969
    0x501080c030a0632010e0c120105040b15070b0601090501020f030f0d021207030f1a130b0303090d050a02030d2f070504020301031a0c160b06030f030406050a080106020a02 75
    0xc2441c409000039030740d00303410302c00700c002884030901d000951104044002d1a00040e5440224280031b0805034500c100c00140c82e0705140000c44a01c42151700500303c480e03190104010180c015074018a81100f10400d0fa075220182230400b40100c00d10800c102d9400c0d1500900044c2810a079521460440d0b03c40718070703040700d90804000c580e003480003480c101d80d0303c0c0d68508041010784100f494420072140803001b007180503503043d0302400c0460785a9030180410100666007511110100250fa54800c03280e241d5051041003a900c45400c0c010301905581c00d0041c00b1002907040340b40898282c2e401d03080164403504615050001e00c10040c07507070030074908c110b01c0c0c5841400320300c2554005030029486107904220030030080181d44010b02c0001c5c01903540350b171030f071031710844652100843c1ca000031042408520049414402e5a403540d0a00b0301d100c050486a0302d03041a070304c07006800b09800d8040c0700d0001e80d50150038002000a401d0b26150950340308042d0100400c0c02e50146e100c00c08540151102c080141c0c1c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 69529462 1250 69528212 69528223
    0x507020f0d090e04051c11010606030903080a050717010f0501120218120f010f020901030c0905011b0212010f0902100903021008090c03010501140f040501120204021308030706020d0501080c03 84
    0x10160702c10f0712900d50310f81ca42103240c000703c40b9011052002d1506080d0046500080d545480d02c0c00c04020300c841c03035488205030103491300e0210080101e11241300080000e0030603801746600c0f07a65881e1840c040f45a001c80c005005e0821380006101600c0c0100900907541c109a081400e041c00500443c60421000680c80b9000300104840380701d001d151668403040641005904807103026140204203140c180d40c000070007075100c180384c05d0110b400c4c5581480414091078542d000c483d81a141d5000c14045183d40452031059010b00300c0e4002c05640c2050341d41c0c4030920030004100c00040c00059107802d1401000075030044498541d00700701c03039080280016191074403281c2c0c03003140740d0034441030325120558114200803822200790b070103601e440000151801320342c68a0403c0038003520401207501e0070500388026150b00340190390342518240100e600605059004007408051450319044080d143e501150541c0e108210903110240c011030310710b03401911403003074500508100000f04490f16180001c41d4480b07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 69530712 1250 69529462 69529469
    0xc1209031902121501050f0d030e09060d15020703030e07030c05010c030c02030d09090c0908030906090307150801050405061e01031a0d03030f0501050d020d0b06030a080403060507020f0d09 83
    0x1c0541400c4021502c80180c00a800e2040f901540c140003034804000c0b049603424465140301e821a0030107000306041000302d003c0d2035505641ca00344440a45014400750b24001303012241c100140c5405140802c038854101c00307190203e100c2c05a6200d9803410010f0586201901c5070700960041401000041c907550704403801c4031001c2c03c080d11481c075130b814165810031100c0400b03501030144c2800c1243c542c1d8815072420681e103110500308110500c40d1402c855405850240d00c3c9030f0303407082000210360318000c1c0c080c22008000a00f21071034544c988060304d0441003500780e0b20020030701090050001d8940b030b016407681700348141c0340d18078001411011502c041c040e9000c480e05040d81e40040494100b001c8408041181002c0c0205a01200502e002001407003060141d540c20b41c50000045003501d0500700d140c1e045c1d500100642e241300e00703640310b0400612025146550611489592900051003080074000440c00b42d500003805d8603048202a04041082022802c0b43c0c02000c44c020207290400c0b200803d9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 69531962 1250 69530712 69530743
    0x61205070c08040801020307030c020c0109060507020d1e0c060c03050a0806030a120509030606030105040b010302120c090106090504051501120f09020d0b0402010f08040222020913020c120903 84
    0x50303444241065030095410385025001200014001c80d24000540046008003080e40d000c11420b906444100d850f03030002c8184030f0000702c800d802088420300c00c101600c00b5500040030481680c0c116507540000514041541b4440c2041c0360320f000030302002c14162b40043c4180d08010083e25001c4c4c0d80100300e88540c401407014083c240011920603141004481c80170741e070143d0b11038a020302c0118050095004144201d100e445602d00180c0b4a007411301865004030380c840140390050b400c5a003040078000c500a188451071080d50000d15180d80c54601c080d0003405541c88482e03d003410700082c881544c2e0028010000c41c401900038500031303603025098000005841c9070000b407203e03410a090001e440e00950103548600c086101000303112040303041501883c0700b41c8a00302e403050b070910140c464030700c1243c0195000c00c000441544501c00c08039468100f0b6942c080040c5081202400201002c00b02510003441c40d6021a180c4100b000c20441c900d010007142d143c035420100342c240040d03075820410501022 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 69533212 1250 69531962 69531971
    0x2180103020a0507050a230c0303030c0c160609180203100504110c010207081b0601121e02090901090501050a0b03071a120a050402030c04052a1614010c090612 70
    0x8002c1d21030425102190f500000391440c461203420b00101c01044c2c00d90f00705032041e160f50801803000001600c6541c503032001d0091811969040422845034100c0440c0d00d030b0340e000e42c00500080c240c0050003440508040e84943d03168038206840344d08442ca40000c41040c0c01e01c1001401070000c485008441150811100899a200d2030642001c0038001c20601103451b6002044440c2000400d42c05040c0000fa81341b0041c10121082c442c0c01c2c0d4415080c0708510448135001c064401040300f5040ca2098160300c0503807100c00d8141d51340440d0003500c04640c2280c10780d541d0280c00040280038064070390405804c41e82802514050000603480c3c1c540c038400c0e2802c400c100e2000001c42e4914100340c0301c2e850303000340c405001032408a40e28030140a003117404903c07a000d50102d40b0320340e10300351261038000d1a028120030992108003c60320311403000310b200f650380c07508240810341c840380607080807400a43c03241c8141e0940d40c0f0a0703040ca5003540c000b00809000d10841d032034140080c0da070000180030750b400c40850218 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 69534462 1250 69533212 69533227
    0xc0108040f11151602040e01091e0507170109020a080601050109060305190606090305010b030303040c0504150302060c0d02070e011a03070903020a063f0209031c0f09090218010302 79
    0x2c03030f50340850110340428030f000b00300c40b0708510b0082044100306009590502082d0a00301c016400c84440c0300004016018108188040c481c42c40d00c21040340b84100304440c2007503220220300d01c1003076803034000700c000303a4444c4500d00c21802c040702f980c4014665040100500d504000000c1e1030f1803054000c0b002050303911000580c07100c0300a2017401e84115801400c02170180c5440b4000c0c00c070745880c001503415608000c0880303000c4c10000116031007150003012038505203040504100103400a00d00020610030351500100250b91094010080c189030302d00100f1039610400c0002e400c005807a804400c244400000401c513001d0b1020b0300303464007070740c00c0121580c994072920251452281500013940101d42c0480114032207401c401c0c00c005030b210034003042c4d0740790099003d082d12010341034080707543c203c0c0d0f02e21802c0403003802500503040c219001010341300c44040140d00c0048801d255100b14000a0f9522003031000d054000302c8080c0031345102042076140000f01c1d412140d0002600800c141016030014802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 69535712 1250 69534462 69534469
    0xe0406150c03090510020a051204050d080906120a061401080103110103022d04170d230d1107020406050603090a021905090a0c02010b0f030709090204090c08060103050c0108040f11 79
    0x3500340201701002000b03000c50001d40d41c1014580450b0203200d03030010040403814080550b07044401c000c20625801e49169680410340d080007050341d40025051040003401211601501d114070031022000070120302d071004194084e0a51404c06040c030044038014808030f000748298240d0b1400a0802582e03550070510544110306403000c480005c444202e03481400061403100800c115190a0070300d40002c88900b802c00c0c0c884401c0c40c400004540350703080d0100c260100304d00b100b0041320703400d001900304080c500501c4242c0b201e0003410100203400080c040b0031803400d40300b00c201600c0e0644503541140f408440c05c6642e0403007128040e12070716a1004042e04000c1c2102084042c1c2030280c504059400e0a0700d04002500c4807007021000344d401d007807180d111818040c20b0203140d104000c00070000310f80b0b884883c0c401442c8201c010398010303884100f600003003100080c8030001050b070306000748999895400c2060030701c1d41100e10366041100c100d00340400710701c2e1003158000d00c9410500c1e0850805029000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 69536962 1250 69535712 69535727
    0x190b01020303010e06150a08060118081507020106090f02121e01120510090308040c15050f0d06050d031101061d010b0a17070309020a080708060c0a05040b030c0304030e0406150c03 79
    0x154001841d002500f1031100394400c0d00e9901800003038880c44e024296424210b010320bc400c3c0152030180d8044142c50f5000308500300550740104a5000008400e40c0314000710060b10300c070950341120203400103031910450121482c0d090380952034582c0250046a00717411414a0101807141108041c00080020103101c420b000f94580100789102c20441c24885180140410500300d4096682c00c0105100045c49540d80c0310480c011412951080c0c50042c0c1c5031040fa84a0308000362443c0b000d69a0314001c10350b41c86c2e01029008a601a4a0300c01c90b43e080020300c20b003590342507040a4030011000540000c06403000c0f500c0350544c3d424008090300c0329941e81d0708460a61004d002c030f8410000380c0c01070080e540c3c1c042d402041214000d0b0b03041e10b100e07611060400e9407050f01e03114208250340940c1c001990000c0e11005020b182d1041d140040c500f59990710380200581007607a900c080294000244010542c0150400310350306001e4400b44610742c81c107401040181305d88100d810500500307411010425114990 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 69538212 1250 69536962 69536989
    0x50405030703110f010807050f0a02010603082802030c030d0f0b0406030602130b030906040609080c060c09010914090103020609040e12071205130b0a26190b01020303010e06 76
    0x840700c28642d03a082002910520f4210180144159550002c155115406440c4200401e07110146442c03e12500c600d410346c0305809500031950f0755076010002078001d0008082601c00d41441320004444504002c10036036a488144081d90700400c0356161024012059401240080138005041184166440f01511010038481d90081c5414008000c01c40c030b40e80a090720514500a5002903929a5105502440252941e4183d544560006400900c16800070081a48510300301414414002402c03480d0410590b0349141d25000846c5403545d550303004000c00001c1031000301d41e08803030307000002281740e000042c003001e4044d60f400030f0710400756112500702d00b602c450306c1d004031020f69458102e00e1032541c1004c00119809400c041c114a03400d4440e4050b1601080f80500d80b602c4640b4207020360031f030b80e031000f520f03402403001950000e50022800b0101400154910104003140e1420b60209041880742c1040c0c0c0445920b4440c05c0300c541d0741d0000a49056508240e00a150f03916030100084021000e0764 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 69539462 1250 69538212 69538219
    0x12170408030a020a0c0501020706170a02221505040509070f03020c0f03030f06040504080d090f021002060708010801060b0d0b040609320402060904050415060602030703090b03010803031303050405 86
    0x1018002d5030742c0002c00f0300120b030043d038001500e1501d44004a0701c5150921a00d0005031044406011640e600e43c0b000d5000b11a0100040c034041d55169000005020b16804040702c6144903410001d08600c1e0381c1406a0303e000b8030301079241c50306160008204940103030004c001c2140205c05022942e003c0d5044683c05240d540c2102c002e030810301c1c48942c0e281d208a0303102c0c084c00c40301c1003c52041d0400340190703401940e0101c255801c01d02d6002000c0010083e1450075100c10054003007220150700e582550b00c02c4802c403a13000d040c2614048034082e06900040c3d001000d181e1400201f0400c00490310282d0340e030b403c0091808038850302c0c0840000c0140c8129000012820f1805500840c11429142e91400c0011500c030510441c5804034415240d03524101c1c2c01075004481040001031514081d4040e80d8032622a849450420075110b402e101150003542164015038400600c0509064001c2c02280c010240102a07a15640c10800510348a01014011242800c03c10681c1c1c02014040c6041d90094440a07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 69540712 1250 69539462 69539467
    0xd03061a2b02041706010305070308030c09090a02040e1303020601090b06040f080105010510030b03070e07050d09081c0203060d02010c0510020c031b030a0e0609030705030109050a02030d091217040803 88
    0xc4007900000d40c06886803010b03240c6220030f0050103502c0451068102c03a0001c025045d00c52568031846004d920003807104101d5007041000780d005640354440c20380520340002005850b1414500b01d41030000010702080010b41e1446e1070341002a0340001d04d2b0741590302c401404174550740c0361b40224469003c0e41c2c22500e0450141c00e0049209030055106504940c000c58000e10000000107094044520b0910007076010b411546040c809806410030356038200c501480d0041c0ba10070303401c0d1010100c1d200035004683c00c5100059848000074901e0203203070401b05002085140d4100b00d40000c50503022100000d043c090500c0300801403140c2886144034000c010790003903660f0480309005644070f0340102413860f030b0511018481444404000305440340d54065460700844028130710208030072500041d44c1254180f03d5041c000c40d150302e081c01a010141d2107400200621225841018284081440c5a10402078110b07000c004181409081036406030b0032091400e03104058000600d85031155802c905d0292200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 69541962 1250 69540712 69540787
    0x1e2c0717010b010305160c03050a050c0d0c0501270f02010302090a030f050d050a20070504090804030b0606030f1302030328080109060b0708090d120801080d03061a 72
    0x103402c01c00000b00c01366010070250396400e00b280084441c0c2940f4074005000e2050447c0045d01510040c5040760150405c6030805403921400da00e49402907003e82c001402c62024141084024015241080032107071400e6100d01019214908819000b04e014208880c1340120b101564040c1e41281c280c514007400038140740b92a4104a404a220040c04607418458039a015540c0c921410a907458a0802c0e500c00444002c10b048003c4030300c81c2c03490500341c80e000388140007e140c0d455203d000c005612800e00301c5d46036450350910508405005010901420040041203842e0b5140142c0716801138021380b03288030007402400401e00c1d600500c024081c0071407642100101e00090a000000d0446aa0b6074101c026038031001c2c80d80075503507248100079174100c050201e000010110b00207000c483c1005019001021240d807542940351120854480106401c80014031140c0f0013030103041d0514030241400d0120303074907041d4242070848244c01038008039440420b00c0e003050030310030072280c48034440c0301d0030800741048 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 69543212 1250 69541962 69542009
    0x90b061c1d0f060108010b1e2e090503030703020d081008060712050601020114060d0237060c030509040e0a021002011e09081204050316061e2c07 64
    0x3986451a415100f41e0000080c84030050040c1c00b50041c010f021000020020403482000c41c4068040b1580300940425012004403c41c041820303828448070a498207418051015108504a4000742c2c0213400412025000c070f1380008000b450741180c0d103040e4040d9594080c50b145804016049051f0500454041c44880b50780000c990b1500325048408000c2529810011780c200c0b4200e1400594a0481c0d8002074400d2516040c1c483c4454005012800081c0d403540350b20480804c030301e444140c0078003040001c6007070030300030700c603020141c003040c141803900000d251409480c0d402a1700603948103e40f1120307203001e000010b005983d140759014280c40c1404441001c06406040780410840c040744111075100c100030a1030040310750f02600000c68906d090071001c45483c070950700520070b4813607210410010106522024030094000d00512000414100910000b0300382080131644145640c21b190f1410001101c040c0d85040800ea0720340848202910f001846040c00700b03e50265010501004541d1035000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 69544462 1250 69543212 69543223
    0x5010207170c070504020906091201060806060102030a08010b030a09020405040b01061407080403060b06070c0e34030c0905040609020304110406030812063007090b061c1d 75
    0x14401c1c1d641044403100211000c0351801140e0703408100d644103840410190820758010014068040d012a01d80419603021483c107103a040c0740c2031203680d901c903c100a02403092003055042142440070354541403d004c0c0060883d64103014900346064000302040e540c00c06079001348803569015100f442340c0c1ca0f25007040c901250003442828041681c003a010051402e20000f2240b4403076000c4000c505060864843c030000345181c01c542030b0420010400d8502040f0500303070303c1d00142200309a41040340b500110008400300c02c0d411210150700d000a0081020b1300c403c81c0950048d0003403600050b1000c1e00b240031180450319501898000d45801d40205103458150010340c0701e0303401860040c040840c1c036400e01084509500c070180a6034814040c0d4100e40c60a45440350704441e00501c01100c5044180340d92a08028882c8001c24000c80a82c1c00726a0280601040c070041400a40c20081503028030701041083c072800c0402a4419803c10710064840c0d07242d48400d0010a84400768000300c00c0c03111102c0d980e50b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 69545712 1250 69544462 69544477
    0x4090903120c05090d060902040e120403112e14030a0e070b030c0703050d1b0507050105070207140d05010608030a20060403091205010e0114180307020901030308060109080a050102 79
    0x71818401c00100040c0500110f407402240034200248014040e02da1400403c02e11100326405a142e15251030380001c104401c2041001d040c3c101643d9502c0c52a04904007490090960301a48110302d01315070740b158605040c0c003074007070100c070704245282c000304210760b281b0040840a6800e88040b040c044400c0702036000600d5804800103c410041d1180c14000c9103002c215180c52103020200100307c0041d11038005440000c49002d0080703440b0005480f504103403500c9a6180700024004200042440003d001d481c2e008a001d0019160040c280004d214000f0b022692081c026401c011500c030403c4025441600200742d254141c030303100c00c4102e07001881c4500035101211641c5451084518000c0e0200b200c50290364140c89100c1c0c3c0601d010404800700b200380700c050301c09540c0c07060f2000350381100380190505036000007441c3e08189070100140020440c642000c00c080e40c414001d8100684a00c0c54150540b0741504003002c03550358000040721014902c2c3c0005c05a0300803210034100b04401500a0080b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 69546962 1250 69545712 69545747
    0x20d05010e0106060e12030708090d0f050601031b090b0f092d04230607030f110307090509010603090b062112070c05040207030e0111011d1c030c020a0b0c04090903 72
    0x40d44110b01b156540c90066002c0a8031aa01c00c000c03c0c6110328202d01040e0803103207c2c1c180070300d1042c295120301e404c0a0307090344140c0d80c10300b0311000b0080c2c4114008440001d8085454100600c0c20b410340411401408410303a103004000b410042540f8110114148103181e51078681000c4600e0202c800852440058400b1100040b541407030700b24a603c0076036145030358031f0660001c054694076040c00300e0103000e0700e030009a1100c5c3d882e00d2800380c000f070b8400114401c1d01c0589606403620b1600e0240124410142c0c00901018a040c0c0d101002031400000c6a03002041240c424102544100a103d00002030b000da00328a48036011604000104007070140204601684107a403c8544e103c040c0400d031300c1020801000280c4141d030000341580222500084550709100026100004c41c1010306442c62021410714250300404100d00c160002c004c003845d1074582d501c5c00f840228804000a07599000b91880204201c2c0010000343c0c4080725001524000d18801c030060001480f942030180c030406400000052 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 69548212 1250 69546962 69546979
    0xc031a04051303080712060602010203090717030906180315070809150c032a1308030a1e021504060219020c0102060a0b04020c010207050304051305060a03020d05010e0106060e 77
    0x49031920784500c80c0b0034000c40348803540d9856903540845240d580140b2103014000c4003000b840300d001340c51042001a050b950001070f030702d0506c140b0306440c144181e846a01030304040f041d401e81908002c820746010710003c3c0c4126881342980c0321b100c851040240280c0382c0501c1040d00300c000c00c0119151087c050500c0341c94220083e101c2e01d21244c3c650040088071010107002c04086809600448001d59000a01041e003494101c03e000c0c041180b09440386d2a4503208502107464400c08410b400010020079021000754079090642d003001d050340d0070703104a2071140c2d140c00b07090089aa0090019803600004c078010300003e8685132410390003e4115460005102101c10044400f29000240c1940d20940503001048959100304107503000c1d0030385001c0c1540140c0c0a00c6122080340c800d0010f0f115041c4100007440d100d03810413042c01485800c1d211580310440c103140c02c1c4491a10b64004030002e8030740550340303c2520f42541c20054090310080c3d580108640c603109001640305d0380710040e040d400350120350141 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 69549462 1250 69548212 69548261
    0xf090b04080303010311120a0c0504111810050c0105041a090f120309010905030d140f04030f0e0406050d0605040212010207031d010212030103060e011503030c0f030509040c03 77
    0x1090300a600a48550b68800c000500200f041c0020540d86520300a2104000355080b1040c41d0912850a07002c40d4840750800081c8020710302800340f1403039880242c2446007820000c44140041d004688005400707200c03240000016a40b00784120f070180204803009021034100f9140000958080107d003a605409820210b4801240030910200c8000ca1000a12507010164411541c0380d001905064030740d03503100ca1030400154140068145800d0804000401c801500e450f8241c00030002c2070301c4110500c0004010000f40c002054000d08403013441d001c0950780c2c81c000410024095604480c0d881130001e01c9002c10405c150700090f00c114420341d020801008119070041c20b0b4003501600078049169032021f041404030305036070b00d8140e040501c111052602401c0641c2c1e415842a00700303a4140f51216040000c3e410f09000d9009120441242d03605c016107151001800d40203081001007410507048a5401814400e42c01d440000e60010401c0001c640c0b21780015008000e03200a00320025010b20760b10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 69550712 1250 69549462 69549479
    0x70e01081905031c020408010609050a0e01200706060513021e181309020409030801080d090510050a0c0c121505010b090108180102130e1803040b0705010902030d0f09 73
    0x120401d0382d00600540c1400603843e03d50380c050070350b07079418580303a0703800d01000a40c0442405048004c3c48a09000295400c0c2441d4641c182c64060344203400c560704080c9a002d030042042c2d000400400002c2101e0b888480911301040584074550000f580005500c803081105030003a4000c1a0f507804a0072555050381c00000108110300450002190403044d101f0342c1e04107404c00094241125205550000b1070039400e07400030341198800708060300060082d800510215004000704912550b40b4185054441c1c5000005011002a06050f108021000c14404920782c040e00e1525071156000030002c0025445171004070546070030350820b42c0c2e41c44c0c4801c01c40302c0003212031041d01d040c1ea00550305646050340d010010748840b0805003100340569012041c1c4c408400d0f080c0301800b505090045e8061741d003841c141180c1c001d540702034400458005130301040004964004100c13000c036455207841e151604050f0410900400d40c03044040d415020b05c07050030280036401204082031041c5074807054005078445101 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 69551962 1250 69550712 69550753
    0x80105090706120207020d050303040b0f010b0717090d0f03050d060e040f02060903031201120209060108060306060f060403020904050705040e0a05061909060c020a03112b11070e0108 80
    0x70358003c00c5420304000346080f02c54005008150020f0b0810702d24030101d5941501e55130007210207442e402040010700c40c41d04c0f0b04680c03003801001a001042d0900042d9114005044c00c0719032085500040025080700c1510364088801105800551350401c241e21814040d007554001a40f00301140d291080100e007440a2280c61400750b1b0b00483e81418100300c0d9420310500d58480303544141c0c1071106020802c074800c9021030403400381003c00140c603d5008248184101104041d155a05200c1c04204001a5850001e12658841c40c2140e40d031820695010200c0c01d20b200d40c3d08040e4101c44030b5004c000501000050301800c0b60b905076410001a20304040c402e40b1f0b50380f0349400500c0f6400c080e002c03a1402d085003501034540d161964000a610015a4a5404890841c0404000b41c3c02424030b0340149500680d046c0ca6140081014100c0003611480c2d440600500d1183c000c8040311054907109401e00c00c0f509a41c2d103131084800c07644055115072105100510900c6460001d110b07200603101d600c03441040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 69553212 1250 69551962 69551969
    0x31204031e020309060703090e010f03110108190f06180614010c050601030803070207050d060c030507030203010f060302071406040f11061215011206151403060a03200301090c0801050907 82
    0x14504111340c01e410030000b0391241609804110001001191490071004003500800d00d07500a5a10149580f40c1444240e0211031000d040c030001d070040000b02e4685480e00074002c400d101000914008840c040f80c0100115082001186c2514182c000d4000c129444034041c0c4244007901c40c000c140c01401150456102800141590418401040041c1007803003e560844201c0c015a00752a4690001c034000041d00001515003039210810824a56054030505401610a2501350314640c1400c400072006501c900c0b4100402d41d000034085c0074800d03c10428001f0344801030030780781d0909003420001e40c0c04240c0d402c1683c04031800c0c910840e10f85086021100d5840f0190104800d5540302c007800c046070343d541c0541d141403110404104101c2842485a600074043c4241e60b50341c0c03250189801031603100000e5942c2100c0e48104244106135450320000d104a039031001c44a91407a40c0421400e4084500d1420340341c0560030203080100704202115070000759140c0030000c2200c0e98510480355603d400a10 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 69554462 1250 69553212 69553217
    0x71e03020a0812070b1308030a020d050a0626011401080c100c02030703032105090d030b04020702060702060a1707020a030314040c0e0726011d07020c06030612031204031e 75
    0x20003c0060141045140c1c03018030303c1d8046c3e9400800345c407546c001d0b44c41102d00a05044e0300107100300700e402e841d12549821401c24001003001500b0b2000c4402d48406c0500301140301c041d18030000e00044001d410685040a00b070205035019651001c1807079035403840c054151f1040410101c58400203200b504d000a4083d002002040300b1490364805583c1210035441c001e0424003c0c44080000c1c28031130281038012414800108418225000c00038222200210924403484c0100450390140e6261000c0d1041650108d6246603103912401083c1c80c81c0c985904643e0003000e407002000642a0003044080c0c0260003914103026025030307542d20f503034001822075000b00031161125050040d1022408410b80c4024070303042c02c49000083c40444030459254100d02c0b0406003550006000000c0c004200500403c804010000a42400580a074171694040c0c85140907040110000300107950f983c4c3d005c581200d40d0b03003d4941e140c81d0003403407006001003100c085e00418488010700c8042204525000b20790722042c0e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 69555712 1250 69554462 69554467
    0x30a05040b03041e050c09060f0a03060b0f120304030201021203010b07030c02062a070b040303050301170c040504060c0e0a05030307030809010b09090f0d0302041202040b03071e03020a0812 83
    0x10000462a82000d0020b0300d034101c901e485001c0d8010f010358810b200f10300900041c06480c481ea410802c0d8035100500c2035001d883d10849c44802900c40d8078130041566440700d004100c40e004000442e07854030142c1c200560045a500d9007415000f0084001c02c01c0d68001c2e800c0d180d841d05820b000100c42c0c8420720030310300d034024204450310101e80300b0040981e00ca0f100404840c9406404c84110400c8829000d8203200c0c4000e00d05409802c900421400004003040c000c41800c1a10350384014204d80414800c50b00c05d50032100041283c000180804c82d01401c00410400103824141230800040000016131800b10720020640c11407880c00d203690400312a8010002e52030a81a036034229a00600980885a00d648500d01e0026655901d0003191092400c4002000d9440500c16441c0c9071520b03201c40501854410001071050700c1106100c401d010b6010b4401007206584e040111b898024075500555070704502c0030000c83c118064400300401c45c0c1c000c503100c00215031038128007520b51002021105001108 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 69556962 1250 69555712 69555719
    0x605010507150b0a08010b0103050f060a031205090a0b0301090e0109080a0c080c010e010203040201021006030b16020f0f030a09080303060604090518031222050c010809010608011508010608030a0504 87
    0x10002c206148186111003c0340f01c840000102e00c000d901c90300200c0850f5140e80c0c0d90384141d41c1c1880368550107011449440da450400c0000701d4280461400003030a415114581e198119004038102c1da10524041c0c40c000b04071f95540d80003000c941080c01840c1c110390600d03c07000d5180e5070502401d8816030300420700526003039903c0c0080d183c0305e1b1034034022100c07076800b8407540d0b002e0b010070710402d500f02d441c200000d680c914051000a060041d04018030208501d068000d1021420102044e507108120705c000c00e40c02d01190340c081c1d1034620740c58010390840c4a5071000000380680803000e0448009580c41d002011601e402c1c03119100d0004031115600b095041c0f0041000c2c500c05d41005820160101d882c543d625040b01c409801c0d40d00c41564400781c08103800900110040100140f0640c25040000d0344d007a8145a98ac15100c607542000c007810042104c0114003400c1080d44244010100e8a0081203003010301856a410f0141e18481c0036a00c2d444c001c0000b43d18a800303c03c490101c50207a56642c80c1504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 69558212 1250 69556962 69556973
    0x60b0c1b01020708070e0f01060c0507090203061216050f0a06022503020603010608071403010e06090a0626010f06050112090c12060506040f060810052e0602100605010507 75
    0x358501080c1c110300c92140300040c0c00605015100262803600c030510540e2411210344810f00c0c8040e0b01142c00c00c0401404000401c0e408140002581d9000e400982d481c2c850400103039144e4052503110106000745201c04150102e039912810480d0019126150041551400c00001180c0ea2190f403000d600310410030602041c001c0c400900685441808583d000c3e01c17074010030250342098010388045100c100030700c45a40d4100da070940c0244107201c015407556061a941c4001c00da00500781e640074000503008564644900c2e0812006004d22000b0054040501e0041e100840e034100e180d071029500c0c0c50484041d82c0e030540a0402030f6103043e10b5036080c3e418040b1122000b001c4081090310b2540286901045500c1044031181c0070030f00800c004251400c10000304400c51b0a54040c0c18045440c11100704034400e404103440c0c011029200c00000c03030b03030754001c140a60000b040700400a020000005488605100c0041303070150341842d030071203101c010741341980e00840e11b0b10300805022900600c458400502c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 69559462 1250 69558212 69558253
    0xe01020a1709072c0c0a0c060b040b130c030b06090d0b09010213060503011d0609070302070c0305030f070b090601030b180c0307080304080c0f0f040e1207030201020409060b0c 77
    0x941640844443e00e9a4032a0302c42c003104146580e5009000f00c0e4a0050440800000700f40c000c401c030000f8034541545850701801d80040400020401381d00c0e0300c51109950380390380c4200444070000d040980b0701400601900014000140e02d9000b107071903e0480d80c1c00381001820340b024501e000c0c00301c0d0400b0160303440381d1107030381c0009081e032201d036400b040f400c16950b0007a00444004c003415180c154a0f03505120041945500104007401641003407000c000084d0b640700c1209810010038100141c1ea0000b600740741d10701e18440d810140c800d04c000208507080790b01c800c004007200d6020b20804510750301c1d200c191036150182880302810b0360801c140413440d00807200b20301207034446c0040219400004403002180c207020103940140e1903500081001c00c00f61070700340440c15aa0800301d509034100c1e04090700165110400307550140c000e603511403810074090020441450700f03c1148419945480051074001c1c0030f940a0301800380d407241882000903103841d05400f610615034014018028000da00326a00c4040e8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 69560712 1250 69559462 69559471
    0x111040806060108130606030f1101110d180302040207050c090c1c020a0509190f080d0207141804080903120708030f04110d0c03050105060105270a050901180e01020a17 74
    0x100094800c080c0003500e5841804010340c807942c0b90090f12743c042d00308820545101da102c541446420401d8082e603200110b0802c1050056040491314000750410f03440d4128020740000750058030014003041440000125101200804c440c07941083c1d50b4148010b07044c5c02400c150580141e4022440742c50150540c0241035006003501c1c0803420640d118000510118020b044d113400c101d5089020b110b1904503540c01000303014028010a080c040142c002580e030f1500f403040124404030b10760f4580155507401030000c095158201e07011402d003090704100d445540a030b64014460300c28880c907100301050b407900381c0b03120b0381d00302c501c090440ea00c0c2c010320142c5c800001c004072540109682a41c00603501c41c2810380b409405240d40010007411480d080d03085410180016051203002d009000b04014800b01244058468480b664600d1124030080340095002d500a168460152000031034480030800c0781003a04150310000748400355074040228200c0c49000c1100000503d801000c502301001d004105400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 69561962 1250 69560712 69560731
    0x4060e040f02030112060b030106050a0314030c0105090d2303060904020a081009050c040e120714030a0e010314042001090305060408090a080309060d0b010c150b030111040806060108 80
    0x7440c0e010041c0700499000740c1014102d21501c900352810301810384110369090805a000b00034003800c01f400101414424800201030b10225109450040400d0050b1040b2a8898000348001c1c10907440c915291100440020005050204103050002000c0900703001c2e000d0080701c603071075512040c0610110500003441640c00c070800c040006120b0b40100807080c00c104041c50000b9840c480e910342182401070306168103111b1420a26103c40d12000480c2d200d0035000141d0440e9650f0707110b45041e04401d00c01c0803440c20680400720715035905540006c0711546040c003d0364104200c00807501c0400b00c1d20b400b5100078100c0500000b030407041d290381120303038182c03030f00d0505105c2d03692941c03640c55a1922104035402c031414100800c00d00b2140c01d2019000740a000c1040c003940c1400e03696404103030303207025014a000304652140e025000ea40d00503071022519942002031406100c05454000c0040c141c500d003420300941ca0003821440307810401e8250f9007540c840c0005446c0e075880302801182c2c0702c0c1d0041c0c0107150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 69563212 1250 69561962 69561971
    0x60801061d10030c1211090904031101051302040c0206090706050c010b030618010c111504030c05030a031515120207021912030f050f12040c0906060206090c01050f04060e04 76
    0x1041d0b66000d02251600c403160b600415045601140106106040510070040a0410001c41c000c1d458440a07120303207030001c1e81c80c83c00c0e594403400e00302c0e03e018852903120030952900052180c1c0200c2a60701c090520300030369050007005000c031012660794804890100312034101ea981440f1151040c0011b00402807004008105660120002400c5c5041521240724943c0b0400c45040c840c1070a00418515035503d04200b0003c50f0740c50740716902c414211130001c003141000b80002c2c0400d8000c449034104150401c0480b41c503002030b200c02600604c111041510114400840003422042c00940244c2004031036999a16411180b8a5400030790000801260701100001510f0202c078074103042c1c48020070001c08800414007103410007400286103da418000c024041248011008251003142c00e4010300c080701211b43e582c1d03810320311014441c0780c0140b0101c1d82080701c00507a00d540081c0d000c4c050280c00b13040d101401040d20040d10640708107080d41020721020301007040030b00e02440d400998400080c00100c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 69564462 1250 69563212 69563267
    0x70801061d0a18020417030901020d030905010f0c02060702010e0d0c06020d062103120603080708070302010603170a08011d0117010603020d0803090c09010311040209120a05070501080702030406080106 88
    0x4605100f40e14410741e243d80820100001c0c003683d81c0b0030281c1007100000c2d62401d25400c0000303495040e408411414113481c0c84600080003400d511098014084260411140100300c1c8000d4440c0700039110340e00190b08101400120b00b1020800010000c003540301d04020401c10703078500c3c000e500503000000000e41d44e4480010781300d9103040d2030034400310500c0c00b000c00e030905444c0142c800c1a0000085410502d41081440060381344012074080030b401c03614007500d640107441c4c02c07030241100b41c000801e1031b020302c04071903580038040c0060030302c45880340c60355074050780c990810f0080701c0000c59000c0f44103000107004218580c0c03414850104181c0740000416810f0302ca4011518030b8554079401c0303c04800000070842181ca0a0008020303064080300c1031209945542c4401070304031000d640c4a441380c0d034000740b0b507a0155281c0c50a40d0000c030380b10040d14000b0b0000c0c180306403100528811180800e0724240003610a40c4007004540565805071611501039003012000c40340c100480800704040c40c20f540d0110b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 69565712 1250 69564462 69564479
    0x16021501060f020d020c010806040f0f0903030506100302120609061516110907170601170c0c0105060d080d050402060702030a050c0406060e01021f060e070507020405070801061d0a 79
    0x40c0a80181e440b1100c8003075000d1030081ca8001500e0780f00046400003515a03038240e0340304242c0c9030030130300442c1c0119050141034002001040c2d05200819140d180042000403d45c140d04031510038001100c2404500300520002e5007a84151a040c1c0e0300c000511000801030b1901c40c280b103811503806080f4011060b10170801ca403150740004151170264204504107020010402548043c441c4140c4000702c1c41d0400d01c2c0040d184039881d64002114480c10400039503203902c1001c01c111402d902c454061098101054507040720f502c034224901c0154204400074803035044c240c080140349640301469601d0302070f40f200550001d000107002268403400400107100503980402c01a200680610003509102000342c00300001c440d41584294188554101c074401c031031380c01182417078540c01d1404880c1c003441c4003102c03400018551a0811156660000d00303010740190b01c28041c0014500c00e0f00e0800140d00c03810000d5a01d08000d200c2c0e007000440d0400b0f43c2550142e40951103a50305c2c406031104010340e0300c1d540320 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 69566962 1250 69565712 69565753
    0x150402040f110703020c1306050108041401020f0a0909050a020306090c070201170705030906060307081e0313030506090c010504030c050d03020c060a0c1b14090907080106060f11010c02061602 84
    0xb613005a0003291441514a8146402c0c3c28462116200b003204915081c00a0120580200050000d03107a041a80c40c80c20301c04c0d012075080c0c10b034040c6076a603104082500900000301c00e0086040c00c0d490480014503010706407007241d014081c028010840313a44d4002e1f00030300700c3e4002030b4224101711954200c43c25081c40151041d0150205846070340c0c5038900100c504d0719210005050b44d11a505c400410003c1810101d1381503c6c03808406030900594810b10402031079403280414403403166401110010a10501042c284e000b8404941074480800d0201c004444034027030360001030308a070030a681c100150300c0d01e2400c4200c1d0610034010f642c45108024002465a0070200d002c0011404285d01d0030100044d40c1c29000c3c00900000b0000300190904101d6021080004841801030080310302080c1c102e001000f0007001000500002d208071a02c56400074100c110300000f400c040f9500c003036155403952060162083c100c08079402040c0b00d40e01c00180d02e02c100c09922002d001d5002d140c200c0c6c2e4460180f28603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 69568212 1250 69566962 69566977
    0x61c06090606110c0409150b0a0f150f08010302010504050108041505010807050102011d100b0d0c080102090103050a0209090a02091315030b0606040e010e06041407030e0d02150402040f11 82
    0x4030302e02044a03030b5004500b080c01111074030f8480d503e0044110005a418001f003011009010310010b03014130141701007620020190001c400003001c02400040001401818034001080380e5285100c0400320300701514042020300009000c17038028171003031000d9485408580d0303229008100500c0c0050720f2000040481da0f00785c101440d1b85c0c01c81c0340148602c0d6024001c1d00c090f0301258015000494900c0790144d101c3d01241502106181c0700e0207100700a50321034120512250704803076106815075440d40420700075802006242e000c82e083c000042c044a01e140b0903189500809848074109546001c02c0400940c4040500c80c2e22030031080440d60100074038070072450924415454059410304505140110020041005118a00800041c00304405902c03240d81100c14005500206444100006e0082c11590401c02943c0900500708049194150021030740c4514180507204002c3c42007800304d844004032603419034203560000201d001410194455002e10f06034150005003590710520803010f0343c0c0303e0203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 69569462 1250 69568212 69568217
    0x20d0903020a020a080d050d0c0207080f0102070506060d02100806030304090911310b032406010801080609070b070807020607081201090b0907080907090e030406020714061c06090606 80
    0x102c001c1c21400d215032004090300a000040400e111800c82c000c00d18400c03501071070302450715074804454031402048280090501c04059800752000d0768540c500039040700b60107680da07100e02000b04106007001c55044d4011600600109001e120030501680c2d000740140c2440d80520041000144114035442054002840384080412001a500401c401070b542c546420020326803245c8100103421031804104000819400041480c8002c100000c0c1030401001c08041c100c4880c0322815400311411015510030082600c3d01d40d61031b603d03400710036a50300c011240b9582c2036210200034400a52807a0103000e030188500b808a242403004d0340410340310740103c40c04552034036010411100c0800c5a914180c09046004810000c48180100007510b100000c2c250a080c01507402c04156441d0040c4000b0002c2d140b045000c2c0180ba0b401c000565036507200b440790f40700602071050042181c2003a6007501b442d014000300302c9400c01403405003c806854881620450b0a550388100203a0255a03000740c500801040c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 69570712 1250 69569462 69569473
    0x70308090705100c050105090c1c0302010204050a090c020d020105160c0507050a1707080307030c0b1503070b1c150330080a1803091406070213051503190206070303020d090302 77
    0x514205e401c2d940007503c0d000301904912104c400315240d81503801000300040c009112160f025060903070092085030007403908200841c4004c035141641d50400e58450380564221754822110744402c038203e640913516040a091102c140c042c03540d110f0090126410302407010340b81140e43e41c1000800d4129141d0150011402403107820840340d0007403114100a00e8030030059440d0025950300207000100500c0028803a000c8030000c28401d402c164101080504080c0840707202c80e03141c00f401d031040d81156034450f2410f0408001c404110046000d58204011085404039825080d9680e2810350000b500c004000710300444523601c0c0051800040c001400715a480d00800760922002150641c0c00240b2010030481d948100d850010340d0020000f01211410320400040c50b98510020b04c00e403040c84c4000e0740c842c000c3c14102c44d20394403c1e40070302c0c050000217114120300c4008100745501c501c040340312201c681940780140c80244c14035000815255210f4a001440d000c00800d1400c12035082141c03d50047e03110 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 69571962 1250 69570712 69570737
    0x1090605160504120b100503011409060c042103030207050607030e0c040c0e0405090309060403030509120d1215050a03050a020406300203010b0603011d060406050607030809070510 79
    0x10304040c0c1c5000c11191800030301d42420310404807840e0f000580000d0900e100100050010b02d240d050260242130000c0c000e01880c440e14a40e00c1c0d0b56a000d03502c44181d4081c0c0c1010550192010040b281110b080c45c2c5a44240310b6601800080e105a0300015030525030204404000114144844e510828098030002041d4603031002151a1100200c3c1440c021443c1c2240602500d40115118003004011100841e0a80c0c035000c1080c21805001c2005400000200f001b10030190400003a10280205841c1c4081801c0e8080c8900d0b581c603522103802d8081003a100c2c0f4401302d003071141c000780f0800d40e411511911050351000450305103004c5070f1041d0f446400c01c07080c030411890240611001000902d0312071503400003041000c0351a41e03010017080302e01c241418202085480039040680c0134800180100c4c0c4035a998805008541101c0c1c03484248004010000340d158a02840784005495001d80820308002103603600f628080d501900f0301c000352280c640001840c0d520490102036441d0030f6982c1d5a4210361 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 69573212 1250 69571962 69571981
    0xb0420120f0c04090b030708030c1b0406030305041a0c07030b0601021c021e0106030b070306080d0201110d05090f010908090a05090c03130804090c0314280c050c01090605 75
    0x80207031002045980c45030601142c403810800792000d4980c000b0001545001100001c0e150101660200680d8007010860507001c1801080e9040c1c0c4405520308103070100840d500b003104a9180d80402808108140b0003440f01c40f00014a11150149814400c1e240c10f0119400a140a01592044901c240000104502543d0503c8060a00180000d850f840c0303156143c0301079216040481a0f00c018104041140d00c1c480c001d421180040d500030031082c0c04d50402c00802809480f60b030103090400d1103050740c490100c0f88140f00b2201c105a0008a16007002c0e40ba1031010040c2502400c0102284074400d07000c24103080a01c10040c0a9108007503055035103000c1014001d65403000d5116902c1500c100d420000318410113812a580080c2d0459100385140300c42c5071007900da0040e9000404280c0c5401841410b0035015889610ac811066481017030b00d580c0e1002c0803150b81004844900c80000c90b000030509503025410030f00c500c10302801c0c003034107140070301001b142101c0304030600f59034041e00c6200f0303c0102030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 69574462 1250 69573212 69573247
    0xc2d030b12060402010806040209090906060a060215060105070204060e0a140a020405060403060c03180c0302011205070c031d280b0306010f0c0c0b030106020a03091e090b0420 77
    0x44055410304a16207400104603110280144084d0501000a00040b843e80c0c0d15811030300c0902c4014010310240c201003142c10750320001202c00f1802040400c00108510b80005010892585140c41c3c808190340c3c0c00f80111104c1d0402e000484c0c02a031280c8000c220840c58030100e0707120f070303080c90000100701c5002e000030380710b2a5001d011102ea0b144100001e203c252102c0d000c444c1540e0300000301154140300c9160480c02415459021a09401c2e0191104e040107044081c18088900076601d9201c251400e0450341c003225020764207030010a05038200140000e002d8404002c0540e0300c0100c003004a0312617404280019000b22039048011450004541d0030f07507440002102070500680e05a0841ca010310001c0c2a81c80d5640d81441404503580104003000442c1c07280402070400240000d0700c81d652080d010795a616034050480108100d080041100003484c28040342c0c00d04106007544c81c0c03a160204050041c108141d0807500030f501c0c0d6080314588110304422400b0b8201e0001d00a80d51600840510b0084 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 69575712 1250 69574462 69574481
    0x20c01050a1a0108060f0925080f010302010f11010507020309010207090b090606130305010603060902041b05090d080f0a020d18030f06020307110f0115050a050a06030c2d03 76
    0x151605280c040c00b180540202d80100e6001e003030110140e142c41c000580000c0c036803010b295002211000f0881c640c0c6840c1020580000200d41c0c2c2142c0300340458058640900440308140c0c1011039100410142d842a5001d1078400c080707040c1105240f010030001403d64404450075070140e880010001c00c10350741004080000c0c002c01c54108028107103000007518620016103e1071240070007280d403018495219100300300540d0300000820070390b50380b8541032001e0980c800050741b290f0701d070883d81c850315903505428100304415a41d0381c030300d480c0d07804c000c0103101c40a0100c19910b00e6414000c018001d0f000400415040d0f00ea41c0041c5950300c4072100040042c0180e515422000284003001c0002540510400c094a940280090703200d41c2c80d50411265030314072101450251155040c1190000c030706511240d0b1840004e084400308540b40e105110480966105198000d0000641086458070a074031000e926890b504e0700b424035016403400c10104e24070074132802c043e6042c1c1c0380742443c4458251041c0180c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 69576962 1250 69575712 69575731
    0x70f05010e0117060d0212030703120b0d0c0603020c030904060b03160513300303060905060406050d2901031209090b0f040b06160501060e011a0a0f05040306050a020c0105 75
    0x801c14491450f18202c2005003510b401205404900011941e03458140c103840030b07442041b6074494401782401088404400422403103149480c003082c54505148864810941d0007500e01c80f00140350900c118025803180c2001d146500040c00000c12960f514020f040091040c051020b86900f00545050038111403a141c4105104040142c440f24450049040d0200da83c421044007100c02d0502e00c140082004280c000319155051512004140e0164881c9054680c03040c0200318559a0f54140801c607102406140d070b2062840750303504006a00c440010700398507807910340c001d03b1a141c00c030176a01101013a0000c4a204651441030203400b9800807480c4000d100344141441104040d102054140303002e04112405552510030303740d4107413030750011a8400440704150101341115810298000c00d0700d800303078180380501e100001800c07000400c0c0d548080825465070918000d5525010340305a010140c2c1d050500006200000c040345040c4120b44c40381142c084096a40c0040d00111030840b000240040340 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 69578212 1250 69576962 69576977
    0xf0d050a15060602061602150a02031006110a0605150301050711010b04050f0c0a03140108010f053103020118110f0907020d120e0a030309030807080402030a03080604020c070f05010e01 81
    0x300741d400030302031b50001034449015000042048040b8100f81d0b01c07204a214014040060120111840d4011031080c2400c6c00040c4a164a4040890b40f800700001072582035030200c0017100206005134401a00501041015468000c040c00480d0030340700102c5014000c94040c07400d034039020800b0b01403d0017aa03402c8404000e0741c6010650b143d41414003a003100501e203008901082b465009038403200c8140180c1c1d031500015a5140f030124040e00104201c1c515150428000c00c820f41c0c101805d84280041421000d04246c8010800240322440b40380b0540840d902c546644800d0114041240711650003203440e900d00c2d0b61040c0c14402e04086c0301c00900c0c02000c3e88010010f590390301190f45981c001c0d40f4688119004549180034001d400f031115402c0c000d000380d850383c004141d0543d000d841c82c030313100e0340766042c0e1682e42c43d00a444d4410200c90107034040c0c010310b101c1c0000a2141ca455503000c94000c0c0014102500c4000f2a441c2a02c2a00842840c00b44040f00b4081e560b04080d440c140e000c4240703402c2e030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 69579462 1250 69578212 69578219
    0x20108090712030302070f050f062a0403080f0d09081b1b1c05100906050f0c040e07051204060506030f0a0c0e04030507051204050a1406070f020f0d050a1506 69
    0x48030502d109078007600b055400b040d04403c21044203501c00d50305400c1011142c410341c0c041c0c0c003691100b41c01d480c1041c0a030084207400340000010206900c02c0c0900b514054101361641c0c0b82c200fa10350050f4054417814404001080c05c0b03e41c5480307401a420301a2080e551501d020444c4803400709070b034000b01040b40c0d020144911040740d04500c3d1480f0b98009a4454049000e1170410b0382c2c80254171000100240104600c0305001f04450340411a050b0151703800744026101d200854100e402c0650b10f006903105e00b00801d100c018041c81300c8541120381481c04501c0d0000b00d102c0b10305040d00a880442e02e00340c480e0180800d03450100301c0d5131a4048290040d2442da002c81d80e410700b40060038450b028044038030342c0001d030605004605440400b0740050581e41d4452341c070488650030754020302540748258258600450700300d03110303052565103041c050404d0b80f0741a041d8682c020216907212040fa8095407400c06091075440310010070081c0b901c900000c0c04164402e1030805410158140e000103c50725103a07041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 69580712 1250 69579462 69579479
    0x1050a0e01030f03030b15070b040b07080f0708090c040204080a020a0503031606090203010b040c0503090f030a0504030b150301060f03020103140412050f162d0305041815030303090201080907 84
    0x350303643c1c2c0d03050400041c1c40b0351400200d000e00b00c4950610140d07003000718901090199a00c40c0502c0380d03106072000307442030ba18243c1c1030300c0303d2905440c050341f46111240000c23400d602440c02d89410500304401c89000b0740340c0c900094103a901070381203000c030b54102c807059904504048205101902c812400b45080c4250310b0035a0140403107070a0050b14080d111a240000e43d102075108820004010b0000e200c910749481c000392490b0b00a850000c41c0b403046900c2a034007100040706640e6019596901c2d9131501d0b1558030750191185025102110310280315000180c660303403d02c41c000003008100e808580003840c3d070002508032046e2440c1400065488000c00002601c0103080c80c80e281d17000e080071600d0303d2400d10000079a0044a54100c004441e509224061103650109040351242030b540700004002d15451499082c0d60120700200411703030038001032206281c44043c40c80d0b4000f58100c001015803841c1200c010001c0c0c0381c2d1054010944d60030401c001d550307001210f04e0b03010115100034803009280034541c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 69581962 1250 69580712 69580733
    0x309011d042a020601081c11060a05010302090702070602030d090318060201050912030108030a03050403170f01180b0d0b1308030a020c0721030309020105040b120f070309030206011403010204080d0801050a0e0103 93
    0x501f4420b04c0d131810b92004c96400f4151001c400341929080b1005490030f48a82402010300707010503031142c058000051040707440042c40d4170a0b242954003860070440046480c8014240700c0c1c2c011030610810141003000180724039000401840301e41d00124440c1441d001c20b42c2001c01003100050300c81d204100501607084000704481004401c0c0c60006140d542d18101120041e05036142e0f000e040322040141300c2c00744140080c0a050b01c241c102d081d010412004810340460f004116010f1300f2481040a00c0041540c11540d554440f2418904c29441d8507240c0c0c47c080c80d40d008440c08501140d001c500203048010400c4900c024003000c40d084c148485103034000c0c1080760985c0714000e041644462400085901c42c0090358001c1444c17900d082c0e2910f00c00e5454200300750080741c5150446c00c007100020820751180c0940b42e407980d099005082540d0800245240303a503070414000350150b40030800013400312400c000041a00c4115900d16020f941020104400c0f0b603e0b41c0e10030f0280000d6880144081212020b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 69583212 1250 69581962 69581983
    0x81609051201060b0c0a0b010501300b0d2909060a020f0702100503060301050a0b0d020d0212060106110f010903080606030703110a02030a090e090309011d042a02060108 74
    0x5811841045000100b409444a60414943c0e0070000c680b0030181000016180380c036510490039541140e0f00c031401102d0090a55040030f0800021a8600f66503002c44100c0c1e802800300072101144940000e004103030240342900d0120392400c0010300501d02c0c2d000f0510169804140748909803c10304060000550341e95014102694407940007404c1001142244210f03141e65034040e01940443e002800080c009803c11140c0c54020f5003024002441074403503101d45014003900404889480d045a028007103050000b18040b608801c0c200400b508640080190600a100c140c2c2e031b0340c0a02c0140c40310142000603001104d20781f40c0c103129000001a4015800541c001707400d07104203880755205042140946401018241003c00c00035a031a0b180da400310040080b000c4a4580c0c11403076036201900d645542c802c960841e0180c0061150100c10740c810304d04222600c154401d84600001c41400003011103024146640101500403203961a0400c4c2041c0c07658508200c0c00680390300d41c586420301e07440e00300049 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 69584462 1250 69583212 69583219
    0x60603030304080a0528080a0b040c020d030c0e041107030f0e030a020913060603121103040b030406020310030602040e01051203130501110a170a020f06040309030209040204061d060108160905 84
    0x40c10500421130506c0b4205032814401610f007111072007030760141840b101038900300c48544c00c00d55108013604140c0142d08240541d90f0003004486540341d0101d005001c44030a120420002c200700310029a50b40c080c0144118101e4040b40e5103d40394a0060001006101c5d0314040c0243d40815600907074002c01e0b06049c540d010b50304038060b030751400c41c00c90014044100c01000e070b5142034008411b2003a15003a84012083c542c8450300c41520320040c8595074000c521941c0405070003000000c0c0003825540186410402e034031813000003103850342c0d200c41c182d8119800100c030070441b2500400c09841c00300d031440e8200040034051032601c043c6546070300c5416034900480b4140b0004510f03c3e042520100605039140f0b801020040c2d1102c501180d0200960164030b04000521489590951581020810502855141c0c0312440160700d907a09000030044000c000b41e0780301d030741c6510000e8007606204002c45521403000b00c415041c83c02030009004100054040c0d9070f000c014241d050041500603c50034146d46c8100d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 69585712 1250 69584462 69584467
    0x609010e150c190e21010501120215090f1e040606030b0603060d020f0301020a0801140103020f03010603050408160b040b3904050a0b1201060206060a0306090f050d0e03060603030304080a05 83
    0x3d04180d4900b2852000d4503006400c440d1400c42500040600c01144a501c1c4004d000c80e1741c0e10301031190886010310340031794000b00120341070341c10803106402094900000b501c04100300d03c4d0040020f60b40307a902c2518010010104c1503200300380c50903110300005080f090600304942007804022421600005090500554009007003c0c25542c031038800d000d58000c000e000b590f9409140c1001041007400784079800140108c5210203c040d0b00a0007950017000c200010f80342103070b10380001200541806442661040307400c000c200d0040c00c5540841c6043ca0103a000c442c05401e0902e0720340308000004088400c91820001030583c0c2d0b002810044a0130441c3e40a001c00030303171100009120342d100759032119900c007410150000e81100040d014248242429812020710381c0d941d40c06030b0710385404881044d80140c0c5028107200050a0b9848108c20a01a40440f00008801e0341c1d81c0745400d054400c481c0204034400c03200100740c41d04004147d0f0104095014508505007503440803400c1c040d0008000500c00301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 69586962 1250 69585712 69585757
    0xf0c02090619150305060d050c28090203070206070c0209010501030f0f0501120b0f01060e060d021207030b040606020102040815180a0f060e0d0909110c0609010e150c 73
    0x40030304003000038004100c0c0d001841e030795483c443c1c50303904010b0780b9401190130440000c4c2076180501d2030081d02030300304018041d503c03202010480400fa43d4050845544441c1e11802400034a0405a6001c1d04101e034005070389040059001e40361100042c600000c000200550034010386580b0a01c2341198020f003170200d4580441c0116034043e040c40d04226504078602000002e4008020020f0300c403040c01100851225180c00f074242c07914401c01d01940c0040340c0d40d400341e076010b8185000241080e0714181c0c00181003200360714404810803401d0762101c001944a090100b050314003803142c44002c003030301d000071480e180c81d00418035103c0d0b400d45a01d00c4841c04120000b0040008907450101442103002611055452860310380d080c01e80c0c0160954241d07182c00c001040c0405d001400e000d070b9402640341d50140914154544014208050002c02940001e00400c040ba2a0400407103004992450005c11080e201003007452800e0101021510b411401b0420702c4510800308003250080b84075000304040c10f840 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 69588212 1250 69586962 69586969
    0x207060f02120d0510170309060a0e060d0b010206090a1502090a0b0c07032f042c240c0d020d0b0d0807020a09110f03060307050319050d0f0c020906 65
    0x81000c00900c1034040003650351690302c0e1952025204080010010448686420400d01c07100680800c207030407a4010080b0234038518054001d03140303025071450034090001403280483e0035138000c960020082c6450b00303203d02c0150303010301c80350b0f6102c5100c0009020028864803039041c0c1d440a501013280e8160700040c2c1803102e4a074801000054003a605c03000b5038407082c000c00e2680d1042184016940c01d400d81d1009604101024a0185002e41034003a650008021404105c010a15882c1c4030090f904c000030303c8001862000c00c030311202203540c1c0140c0999401148a170380c81088440000b0a140d1455082108a050520654000103260f0b040142c45980c81c814001c0204210310310540d000070b10107a071608103c001c400904907584203075029684d03155141d01601c00d03219a075020581101040c401030128101c0d5001555000d07070010308807802140d171803010a0510703110320310f0401d102c00855210350900408000e038520814151170101020842141c00504d52500494000c1c441e582031004030360380e40e8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 69589462 1250 69588212 69588223
    0x30a05070e0a210516061d010906050d0902090702070e0c0705120c030f0301232202070203120a050c0607080402031e1c030b0a120b0408071a100e01150207060f02 71
    0x95011003250010b2901d05c0d040c0300b02c412148218800104002008081d00321818101000e880d4181c4403101010704116080d1003940142c018141d446980344203400160351500c807410301030341460b000b40c4445410620304c8040008010450b5000b00d60410001002510000d0341303400c0d5480440002c0d456000c2414000d0561003914100c080c8072801000100b2001c00c00890000c8040a104000f110780001c10280116171b420b070041031210b522841507421040c0c0c9540c00601e8514802003d43d80e0706800c600740e0b031406411610408000940100d001c03071442e0300c100300c096008605820310340075518141d40040d56940841a6450543c01c45035044603004404009152504001e5040071442c1c0b11000e200270003d0200402880c403c6803501c600040c00d1240700000040c00780c02103024036240d0384544450b01079030f0090340e00f2621400c074444920f800309030003540640681c204c584460040d9151511a480040068108400704a08200802c070030b140c0001e00602161007608024001c4c03006000e0980c00c09 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 69590712 1250 69589462 69589529
    0x3030305180d08011521050a0603061a0a0807030b0403030f14071e0f09050f01050903030a0509040f020301060203071b150207091a06040b0c0a1502030a05070e0a 71
    0xd12860b01180000358000340014103880350b202d10940c84035041c2504072000140c4d03400850320820b4160310600b124240760411a4811644080810010703130300e954490071502280c0024854045078901904c052601c22803840040c45502c004048a03401c68403290b5400c40c0c05000101815610b040d0701e420884503410403e0304411001c0310350400d00d0b2681c4041c00361300c0303c405152038003e03881030807165490255190740f01414072170b624000600e00340404e20a0005000300c0103070621105000c14241903504000070440143d090381e0700c03074480300380100340001c0c0d4281d1040790742c0c03c0340140010f001c8207900009481803d50465840003501c0900981d41c802808680c01c0f039030307406000040e05070005800082050071120000d608201c1c85040b2031500810b04030340414664064808c01c410000c00481c0e81c040c00329441e81d802998081c00c41d80d542d00420300c032042400c0c01c000781c010080103021852481450750080d40703820950300184400300059034101b894000c042c5075100c0d07084020780c003018031010113009 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 69591962 1250 69590712 69590761
    0x11428030210031407030203090d0507080403050601080a06060524090a03060c051b01060501050a12020c06100303020c01020601030b01230402070c1a0901200c041b090f0b0403030305 80
    0x78034a02c080003005030041034050003e60590402103017001e8460b1003101e20070f00d0880040c10b20204159403c4820b03501668040c0e0348000144400b001003039051241034000c001400080c2040705240c41c10307400340c4035164005480360b0b0020304403808043c0d244090054400440e4141d603600c03400710001030b05642841d0006000c807803405142586980e00700b00101800194070200d03801043c0c0d850300c00c038240c89550048070b002800c140610055540030f8103580c2d03140d061000000d4104503030940250703d4100111000c0c140002280303020020305805008000700c0200a201400c655030568554185001040c0700d83e00606100c111050380c04d18440d43c1c640d100140c0100f040d9668407640c20200c101200f1405103907814191846020404584402212402441030310b82d6414810042504a074166482e04114400e000e080c10805145e5243d104001c00e01500d082d00b0f1149450b600c90082c80303507503240c11203070341c2e60071400c1c0505c2090042000c2d10220317980b6190100c0c039a076446001c88a0250058000d980 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 69593212 1250 69591962 69591979
    0x1203070503062b030305060a0b0906160c03050a0807060c020105100512071208030108010c0206070f030f230f07020307030c14070f080303010e220f0201022509050114280302 76
    0x2010750541207140542000c0300c0708c0040b0f6803a5006c504661150341d064503800754081104000c0c0ca01601114042140030310480c0a25568a80f501d6081c050072205c2161a0030000485404000c1e19101d03004641c50148003c1206240c03203080c007072241038107000c0c4500c00e12441d400c80941b844200516800790000c480c11260314480780c600825180c0080c06803d00e25400c0c0b50300c00c4a500e02c00203059120b051740d50b40d0340e1468094442c2c1900284001003041c8056510340016284500c0f00b5215006100303807202d0341c4d01079803802200070000181b0107020801150801c0207040046540009106691900301c0700c0407900c00085089685481c109a00800703001c0c400201c00030302c5480100242d81241c1d901c421100c215560070516004045102680b104c034990480c070200041050705a1048200344180112030002c403440c04450556000034007a1801208800410b100d0507415000d0140109052000c000381141d900c1e001600e44000c0502800400080030350381000c80b0118840c0d00f0003160007900701030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 69594462 1250 69593212 69593299
    0x12030d020c0a05010c03050408270a0e0405010b01021605061809010308040f052d01030603080c0a02030c030703020d150605190806150901060309030201020c030c06060102120307050306 81
    0x40c0c03036006001d8191055481e1178a071201c824060f015151080d684828800d11b40075440d80200f2030092901807152801c25101a0740792940c50f40f001d880c020301f01002040d9240d182c24a4024299201c0c00c000303904540002d00203d02d60250300100c4008e41308100d8070103445906004050003203154041c0e106070b00031070030f2000200380401c040041c000d68000c2100d00350041e03151410711541c0400c801305d00c049628000410110402d082443c0b20103603505140c08148180d59461b040a01d800c0787c1d00c15036540c0c20410105046250400040c43c5000b816005007e140d881c6400003484140d46800241170320212940034807218215a00410241400801041ea800c400354604141c0a1150050159910038030300030502c003070600c448401c547d0100030100c2010f80e00303040046004d00340820080707040d503400707003d64006000c0c00c0c006040554101d2000f8092880e245000900c0c251946405c189401c40c20418054035607400304c11268030030300a0380d01d410b045881d490070143e5100b05514007002c60150a252a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 69595712 1250 69594462 69594487
    0x30705060c0306130b061e0706050703021c0501051507140f07030c27020c03071515060f0e0f180f0105040515030a06111209210301120212030d02 64
    0x11400381e00260342c6031001150501c041303011a0b03203200041d94444420f0040c2c0b00400940c0c01041e03442c4040000350760900d074041e44e0f03e40586100344d0300000030a801080b021061811800c1c1e041c040045103401740130342d5262a003c0343c02ca0290400d020510b900001e00102403044501c9075401400c500f008807104100401417290312500540803c6030f1071009198001180d901240340015141a00e5204404804d45004924001e6100341c0c0c1440841c0030501c24031000c642c04d90032800d11201280f101181202684801e442c65041c25080381d42400b0303140c1c486a9070954402c8000e940400c0c10380369281c40081850000c0d10289407c0765114010003408204080c1c4184005071a040380c1c07007694244815200d03c24804851800d0303110943d050f0340301c01d15200100c2d680d030300040d040500c031021480c580750176400c0d8000040401c07901c0d50f03681c0d40224405054100c0c00c10310924a8400085060708550401c03080340c0c120508030b800644102000b9042100c8004103000b1160038002d0310030115550700c20030005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 69596962 1250 69595712 69595717
    0xc030e091f240e0303091009050607210201061802030a09200f01020c01051e0c0304030c1802040b070f050c06030a090209130305040b071a13330b03030705060c 70
    0x560000e0700c0c2840030110b2070040760040c2e80b58900501550802107050140401c2e00d00c403140700c00410100200001c1c050b100c0300c0040002c0b9004140400d0300d84291114160b107505ca540800e421a8540310b810040c0b03080b00821440001c488100169a07034030b5104140b00034240b8220043d10782e80d40300d14a0000170441038001846000143c2d4601581078460f4010380c1c882070f440f00581c0c0403603403c015591850544400411102c1c03800340e10070b4141042e074a14a49541c10641040381e1160806a00b130060010000b4030b0013441e500258107514242c02d01c1080b9802c2e008032003000b0914000f080310f540c01c00c0740c2800080d01081003c3c0c0000e0f1030349050305441014182007a801d038000c00c100c030080b07001d00d00c5091455001e2601030b11a240740a1800c9086072180c0d0000f8400e442c0a00c5591001c40441602003036503000d80900d40b140c15403103040c0d00b4500300340909516895418902c09000f040940c01e0524901c03808480310400003034104940c40401c1c2148549030004000f4000c08040008000e00c0b00d01 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 69598212 1250 69596962 69596999
    0x1d0a021005250b090d0e0d02010201061805010e0a0606050910050909100611010b0901030b100306020c060109060605090a141305040b090d02070602070302060a090801020a020109120c030e091f 84
    0x21010034036200c8200603911a5111321750100051382d04180200749042c0051003c0241e441803000180081ea102d2004c400300c04002c0d84441c150b900c0c0c1004000c910b00031069150411100707201001480d151410140c804d10841100e03e020f03d91980031100b5240c040d50a5801e101800f41c01080c25141240e48102c5440c00d600400020482202e0300e00c4070000c6c1403003290b4130420042c007072003810707401c51b1607524004000411100e81d2410400011000a416002901d60b1074218002400a03505005c641c1c425100702d80c12032410014103201182e440d590700541c400c02c807105494032510088251010911107005020950b2090341804140300800112a07d041d1080a10405a852020880301c040b41c0307071080c3c1d00c104801607000c0c0e002800540317000f0008000c6100c150424041142c1c1e202c410b9803e913001107a6105c003607552100b24030700b80141824641e07060446454800c030280595900039009202c0c0320b2019001b140c4410010769410003440c03021900d000901c5400070402c0d03855001501c04a40da00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 69599462 1250 69598212 69598223
    0x3012c0a140705090d02040f021605060402010806090910050c04050d0809030c010912110d0b010305010506100f0212030903040b040b03041b0f14030115080a02041d0a02100525 77
    0x400240b00381d0310600a0340c204410080c03240b6100841e54003040040d11002c050708102c541e0070801d840740b0000803028504c2c064440c0010300600c1c43c0c03900014189a800a000754010501c580410083d010085540040b43c0e9528000103003540701c503120901c1c903000e5501b0607501300e00402c0181040c41007041c00780139030400c210215181d0f07079400401103408040038424840e07001d580e40360080015044001000152401a01c0c050540302640c8401c4e1544400380c0c01030302c05954074000e004840c10014440c402c514140d0810207080a4880340003565000c00581d80e20880ba00400450f031009000d204072001042a604016151500ea01459409510680e81103441c0b181c034031010302c1c0e020306080c1040100d5201ca81d42c000050b1404404000c14002012a01d500d9540c17411035000501807842e106003e003076a58000d020141140c41800121540400024071000714012411501200002d100403a16810b46141c5070241c801031064401c1c0c0103401c03000c08007a16550b6004030050364004841e0003e800748 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 69600712 1250 69599462 69599501
    0xf06020f16060c030503041703010b030601021506100e0d02040507031d0a02010816110a05010e0c030606030c012d05030a110c0a1403070f050a03090501090b03012c0a 73
    0x60700c15681d841018030800c40401c0c10b907641038010901400c00303568440c2c0244007140c92514104400121588241c22107007400b40040148a12540e04200c0054030941c1d4240620700e6007494000200c0c3c15100e03550380c008000913511030340d1180d1643d80414504a034064003e001c1d80c10040c401034043c1c035900c0c00101c008400d644223030060910001d01c02c02d500342c060311219072944406405441824050100d2420320150b4668059003140c104078204940c1c2c05203000280050a0000c41030411203202002c0e44294440003c0c08800e50303021031002d920340402d00305021094607520004202444000c80d141c07011801d503080e018a50b401c81c0040d4480d05100f5420401d041100503100c80d07a02488100180550240803000002203903c140c41030b240c4091400c8a082c20307090742d0341d00380c80320072400111001c0c1c209040020400d0340100811003d0442420203104403802d185420120340414400c0d0743c4e10340a07003403a1032041c50185548004d20020604e001c2424582840d824000c0c00c1d0000f00307813902c40c008 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 69601962 1250 69600712 69600733
    0x30f0c0c040507081b1602060a08010e0a0209060409090203010e03070b04031e0518010e19031a070f050306040f1d0d030c090b0f0d0501061706010e0120070f06020f 72
    0x51500284034508a4a040302c4a1740034411048403900981c1031404c1e190f0000f5852009691240040c062010482d41e0741d44441d81800c9003081050b5000d400800e0040c01844250225665801510181c403060080010041e089000103405040047d24000c4240030024011003402081c501d564070641c00f80c0c56404641a01100d04081e50250300031000008909104e810b081d4081661072a4482c2d50501d00342981d100c034540003480f81c400220101030b021b0080d41003041000643c18014282026000812810b0701d003c0d000500440c90b513031071480c1088030000000310a40d4959000700f800713440c2d4101c20007500ca1200b00b18107800410141c01c3c0301c244103000c0044642c40c072900501d0b68010031540d5080720700e803404030f0f0700025420809020f030000a0a00c0080e480c00c4252241e42c4c024010f03076440c103e00403a00c2000d41d403211006000203040000ca500301d161a640c2140310310840030445101c06966600404185041c2011900200d401d004507160000e41554006000a01244e0b15410358010907070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 69603212 1250 69601962 69601967
    0x5040b161b02010e0d06020406121a06071e050a03030605120a020a06050d06030803160f09050a0e090a0515060307060305040b0604020c030d020418050604150b03060102030f0c0c040507 81
    0x8094070401101680c0042100055204d0803100880312000341c42644541c50381d96510080e44c0207504800009544d0700d40b52030580c60140150300c00804101602804084a400420028400c04002900b0110036400c90a5060007500606000941103020344681d00c050f8500140900b4042c0320706480303801201514403070040046880d0741d04681c01803a000d066480d0940540b06030308520807041d121640d80070b0020105440030025071246e140d0000701c06005140c5180074111a8458010000700400c0030300502c50b54071659400001e990340d54500544c0790b0340308e8110501c1c0c00c2c041c85004100e40100041c2407580d05620840501550302201503896013a11507004a00b25801100c014148032018004100300d8103043d4010034654540c801900d15200b0404601c038245c1c0e0040d4008a40f801007100d030325076409010300c03415811510480702440342038074440d80410882828001c90440303401c000b01180e034981c000c1044038405400022041c0e02c4196201c08503860310304002141e8000c80c01c040c000b507003407032 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 69604318 1106 69603212 69603227
    0x30c0c020d0f05061e070e1f02010f18082502030607020607090f0501020303150103060807180f0204061205041a0c0714030a12050402060403020405040b16 68
    0xa11920f02546440b40c020155000410003a032101d419420100d641398200c012440e240c5506c081e07500000e498103070b0030f41b0402400d4002040010045d40c040d005400352088802c0100200701400040c00e803c0280440020300145040210044a95084107903201341480d100c10340b041044554046460070a05641c0840561b1241080280e21a8031241103005001d010052020840c50180007035644e0101500000804090b8451100c659100c3e50040d40204200000c58915560b0b4a2210b81c1402604030349440301c2d4107211084203111000c0c021501214095074403902d0a0080f1000400101800341c000c0380e412903c400c1d11180a20201e00c00c90203070014020140e42c60490b860400c1303149600400214194109001006941c1e0b002000e04000703480400b4041116503840c80052040c0c4916000254030510748000d20007405010701002d440741c01500071807013007890324220a0b038020 = true := by decide +kernel

theorem cover : BRFrame.Cov 69424462 69604318 := by
  have h0 := BRFrame.cov_init 69424462
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 69424462 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 69424462 ≤ n) (h2 : n < 69604318) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
