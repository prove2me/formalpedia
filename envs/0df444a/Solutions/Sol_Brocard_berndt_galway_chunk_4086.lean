-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:01.665985+00:00
-- url     : https://prove2.me/submissions/9243d7b5-04b2-4fd9-b6a0-c3ddf6951d2a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 734712230 ≤ n < 734892086 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 734713480 1250 734712230 734712263
    0x10e010e1e041103151f05030a0f0201030f061d0615160f0f1a16031a0d020109050402070b1801230c1201090e07050a30050a050a030806040504 63
    0xd500e6001110f405002c4411840d41200a865100411580c0441c051a4039810b0400b0400780205a00240300c00e0f405488514103036254038000c40400130000c0c1c145a1101004035920841d980000c0041c00c2c07071044004142900310100b00c3d890005d45450384034118103859020360030081e9044560700c00d0324011040b607403000d9035030f120340243d101c1c0e6050301c050b0a48410180843c8205070082085800d0182020552400b0b40b0040a0315690340310110805181168140795502903410340c000944045405060034a080d10040b40c11001c070f5005590454008540303001003290044005004450341115a60712111a041840c01c0710b511001c8141c02c00740003000e4824601c81c90800640240c0d90381845840e040903008441035180c0b00781e00a846056491401544010042c1b15020103003804407950540b5502d03286440440040541640880e14042002c050f07410225103c7c2c5564554000150b03a110a502e062468603692608000c0c0d010401c842c000450914040c8141485558400c6980c050000d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 734714730 1250 734713480 734713493
    0x3170a0c05070b060a05090c070b0702060103080d020309070b0a0e180609010608180105070804020306061807030b011b05030406090f03031b0312110c0d0504080a0303020c07030b010e010e1e04 84
    0x181c903080d00321040c0e22011805403901f01c94540310741c80c0d6501c0703e0356540b00c501e0410b64291008008004641110b0010b10010ba040c200712035030f541c3c8001d005130301e98884ca4100e5081c030040c0e51211802650002d250980c06401c1101914003000c00c5690f40c0d400d42c44444008d0b00340e001103074440d41c800220001842010300560b48550021514060078000d0003054607140d084071000e452100129444004000851a007001b10399441181629000740f4440940e003080203410019201c013040c151201c0503407002d64401c080303035804550741807100200c1e0021800c045840394454004d08000809401001c10002242d0010500701c03541a611400c001902c1180150351f03801d03101007202040312020150b0b8044105000d00c404106042002c156910744c00740c0c1c070a00c1c2042e9007880c002070000c10b01c41089005408a5580e013250b070141800360b61802288685814200ca40d00000e100c00200b000128564003840002c90585044059445081e15031a4aa041518844d0703400c4401d00b01c0c0400050002e80d0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 734715980 1250 734714730 734714753
    0xf0e060414010c05210712020c030a020411270103050603150115050702270601020a02090609060105190302031605030c030601110106120f05010c030e070b0c0312010303170a0c0507 79
    0x42c0040d9610b8144500170207514180707038000c00c0a1800045010410700c000605000c150600030300003444403917040c2c004640c9a0705101800f0f0311856a0700d1844007580e4680c0d0454203507e0140b44038075105280c6584114005100018071400a850040010528200000e00ea41d44480c4001c805185038a000340f0b00c1ca841981001e00c804008051011400507100d50342c0f103622081c0e46403445407582e984c40c1c28240003120014800760440d0300002c00c0c58090380b0f0b00c1c0305075600000c090b10592843c4d80ca650060b1860300c605181c84481c400d8448601d04040d078594041d6014000b9601440a0151150700445a44c041170711000603110003007010924543c007d648500f0300840000021402d00c2d6039520403030f0400a0b055040d00c10303c42c1250520104002840b996844501c28142004080040c00b8096903d00c064001d5007592100021141e62868080098501d103502941d801003103036840340750082c60120540c00528440408002040b800030150060144071600c0e07545c0d050400426480300321031030741c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 734717230 1250 734715980 734715983
    0x2d010e0f07080a02180a0305030702040b15040b0d0e0d0801150c0809062a1f09080306010f03060302091510080f060105070c030f0f02120601030803131e030f0e060414010c 75
    0x5420a007445c1039803a400358180c0214040d1000e075072584428010b0009a440c5070902c90300c00d90707038006503c4550b41100f05580640ea030b010001ba844074545e0050400a2071190901d05c0180700b0691051811070780501d9080c180c40300c0d0127680940c144c6405003520840e45c5504010401071041c0a0300925040507405007000484c60704c4941c660091100d120540ba400200c031a4155030840305801014501c4092000ca070315509110800640800b6101c0300c12600000d00f07804c0c100071040544a80740c520980100b0061038005014840d0346c204010f600001c0340982c2d811a00514042140c820102c1c082e40c0928440c4240c040d001005948500046a507503010a60460b01d80d5980040480450b0800581645040c45044c8901950811340100100e07446015015445035102e04014030000341800c1c1640c1e0440f26604407078070500f1007841c4c01118045810340b000d0f000225a9110401d1591000701d0340d000800300d44800c4040c0148605110003403085d80500c0340644002e040032041940715401201615 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 734718480 1250 734717230 734717257
    0x70f030902061c05090d0e090718091103151e010e01120203090a020a0803040602101109120105070801091515021f0204030302070608011206052d010e0f07080a02 71
    0x2d8440620b22442c10201582c0c0900e51360301c00402c800500e00700600d92410045081c80340384d01c0081800503c4c0c1110040c070b0042081141050035010086103140c4001621101000340184c2e4138044181002d6041150307495000790403108130750840d003000c20030494200c2c1160001202041480d00640d0300302c9010500b0b50400240c155880c100c1d405070310286000d034260f040a0081c1c446640100105c042103500503100d640c004000812645400181d2107a24031410340c0d0200d242d090030300c141c588a0055040c05a0088d010031240c40302c1d0141035115620480351f07521180041e0740c0754084901140c880d440c0c03162400ca03e445091148064038081001c580790244100e038410004198001e249030040905c0f40d0740c41e5000f050520070940c0500541015041c145030914056250014619403e1007400028007482d99440c0850701d010303080d01508121b0101108940b05240480c4002002e200003440b0310701d402122540855040001508120302540482e074500015445600211000b944140f0000860303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 734719730 1250 734718480 734718487
    0x7020a061b06050711030a0305011403030c03030a11040e0916080c10120b0414071103030c04061209020307060914060a0509013501090c081b0a0203040e100f0e070f03090206 76
    0x5e11030410081c14501c95968001c13600c0e51420640020350b4580d01450fa00c130313800c1449030180400000003500c2d8071001c402d10100f1207048012030b200782881079401ca00300c00e00c000400c01c1280c6400054443c40c051080322004240c0366a122155119184034984ea80d00c040150500310204d8800c03e41001c0c1c0c05440305001854007101400074084540f0150700754036480e801c104002060f07400401900104000310040c500c1c40c030b004a0221960311650241005010300c4180d03803181c41006901c540f010a502800f100e50140c0c47e060044d2494910703104020904210140001450401505607449510b40e525030f141809001d100569654214200c0019071412028808a28041521a031041c1144400000405d541080c0344002620120582d103010310507402c041c810b4842c1705600251002c1d4219902d19180e01c0d1010302281103118076888013000000b40800c0c0072460107080c405004032a914040880f40a03520300750000c222130200c840b0780101783c100e0b2035024414060740103804200e1006298915 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 734720980 1250 734719730 734719757
    0x110a120c02060d06030f0b09010b010e0d1a150418020906010e0625110301090b0a0203090f0714030606090f0402040b0a080d020c0a0f030f120c020d0807020a061b060507 74
    0x11254545e009a4102141e4210711062002c1d0341005e6401c400366500038001ca441640000e03005081c40b840c00c602551880d00b201081c440a0000c00a581030030f00000e140e141080d8403400216101d0401252203103140c06c101a1800800b144101d01e019800380060b68030b69280c40040d560705651014040d0440802c01a107031242e07080007038a85000307a40c0030203c001c240341400d100143c610b1481d1000e000b68507051542d00840c080034015a4401c004802c0540d50741d60748030003641801c5460407010224170a001d00880c822ba2400c00b2403143e0301081c2c085458a556000c200801006c1c10346402441086040c00725002d8106600007006640003d4100491942d488003003516003150402c2c0c240058208502081c00b03072070f000124400070010042c01c0c0074910b0a680b50f03510100d503110001868011846c500c1060f2034000d1004071000d54005001030442115801c02207a254004c10080f442030700000c802041e071074050314020442c881400328600c05414a951904002c1401400174024040035054900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 734722230 1250 734720980 734721007
    0x908150915070c03080609010605120402030304120f061a09180102070215031e06010e09040c052214010f0905061305090d0801080105160f0e040609020a110a120c0206 73
    0x50080220350f80e844506103180c00e0003045000c0c0600810300c030b14425001040426880800d580030000031a42210302034650340b002928510407580101c0180e4080c148210a100c4481603c0440c503000701800d004441c00403044201e041044144e841c3e01c1101d0101040c001003d280000f070700c15171140c00045c40c101d415000908036481c046190120b0480000400144500d24031310480c000d0800804160a8100240040c0820084854060040118400190512030a030121100404c03000e415200f1841d12000321016180000c400c00a807a400e0000000d06142034582e07240c1202e10f0400d02c05410713800d0041c1c1d0400b81c41d001c0d200650240040c2e210000901541c03003614050070050006160040362901301604009050b030290750f90380d16040810141031840e608035000c501940c9420144518000c3c0300307454800641f0f5a1907080707441c1020104401d0181c1c3c0c004c040400751900e42580c0204102513180e596110600c00501c8104a0b09010458074080d401181e00544020149418002e0600440 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 734723480 1250 734722230 734722273
    0x4060e01050112260d090c030606090903020f0703080f0a0509031f0c0c11041d0a050109020f0904020d060b04024f050d1a0a09021009081509 62
    0x24120310b416681003808014460300c4150180690001c12450551188101011340c0940c0e1602c00e001c5848030100e604015020040b07601a60748003074104200c644030340c1040e0080c040c00d182240944500904064900000030f450011268404442407502e411400c0d0030350706401075405e0030240601445071780701640c1c06000c010041c50420b20007103006448100d910b010395618500344800d00408524000105054107510305c0100d9041d140401c80400c40e5071410034061400d00020118010b180080b82005410b4220803d0700b402140c2c2644041c40340c0b0108106070009640080d072107802c021203900024035582002c6c00b0041e000304018101080382c024904c0e40d03510017280010740e0b092507883e4484410707109240105509200030304107131031070301c103620b51241081030146511840307160855904002e02a018021b0b0416a000d000082e4100084401d01918078120b04a105103005491b01151500c225001c10448030600c0003800300141c0c0d180400100100030705a200f00340521803001c1145030084524 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 734724730 1250 734723480 734723489
    0x315020c01140412051c02090d0f030e030114010e0f1f0305030309060c04050d06050a090f14060a05070e0108060d050708030d050c0f0304080d2004091508120304060e010501 76
    0x10722580c0340c9031809036840003907425130b02c0600505203c0f036419002c6402540150042c44d46005949248620000d00c0041900c0c40041075240801d0b200c1080550007200b5050307100f01079000303100d85040c00030440c145110900442d11511042c00002d0500214a0315440d0000490718201c2406074850700d01041130000e83d0815982c6520010500c02d8102c800c00c48c0c1c507840f56000d9030380c3c0e041504000003d030309500180e0000d4220350300e03400441d0f646407495100d290995407180800d00724200c0d80c0f404c0c9400c007038008590780990281000186d2810703650b0040a110360f400d0394980c3c0e420055840151850f0101421044c2c00540103c4074400081c0b041100d1005880d03104001e540700e91100c81c400341555070041001220450a1080754014404481a6500b15501a8209458540c0c24416400404400d100b0300907903114080c0d600c0003441240001c10941c2e90145052214070020341c1c14902c40d811a111b0703c06268009a15800c400714041c0107150803074850040442d08007282046a820744400b80c11 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 734725980 1250 734724730 734724761
    0x171906030b0c0702091b0319020f0a09080105103f030c0203060c09030a14210a020c0f10031e020a0332061302090402130504060e010308040315020c01 66
    0x310142540b528200103540a120f5024070718549011031b000c41d106000180541700546044508001100e2864054a034012005410756440e80d20140004240340c21505c683c42041d460b0002051106451407581400c0d00c0c6544200741e400c0c074800044c030260b143d106d440301800c1031415000c400542041035008075494042e507920140110300d8010503007445806450500426000c00200b0440d4501142201c07655803c0490b800c210f002d1104a02e080c503410b01c040d910755143d41540a81051001009000003e0240d804c84101c0c0203000113101400c10f800040b594080001080e100d0251b1003a005011418443c600d4800300800c8035104a0603a003001075094042620f44030182a18050f2070720f5290a40c0b2070000d94813144481d00d218030010b4002412203400f070010b032080200d054130035404503107000e00c01078400c566800041901a81c50300e014020b652080c1e040c4600064030080c14004103040e07079040307082685441c1c0f0b1680d0301501d1241c881c140070881074081c41014203404080c400d0900201c248038 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734727230 1250 734725980 734725987
    0xa0509010b040503012a1808060f042607110a0f03060b010e1509010c140d090f050a03030215040309090f05070e011b02011b170c010c171906030b0c 65
    0x40405003500c2090b40175899a0240305140c8054843d203400e040411b40207800c24816020307480400b0318290b121900403d10300d220b20014450400c02c02c1603204d1141c0d015401a0307900302d007101524110460045000c0c40a050207220a00201e21100710000d540d0000925110072540c6e2084103903865000c541c400d5603025038400c01c14a103542c2003070420690b08012a4419255941c554221031a8012400550304000c00c8030035240c00c00241c0102002581d60401c01c4860303488041000800780c02860090080903400443e001545007010425403060780d0b41500a0105100a00512900948002e00690810082c0c50340028031000f0341c407a4240c0c0f20f4502c0d10208040c50b101d203014100c0310242603001d0400070f07044010756000c01c0c900300c0110300ca982440c2c00340e0301d580c01a038048990301d030000d000742080a584012031410b10102e001807020300c1083e4028051907100c100c0c2519000360301c01940e50980c4158000402c0d44070014800300075101c445800041c22070300e80d102c07600d580c03c040340e42003030440000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 734728480 1250 734727230 734727239
    0x905010906090506180409050a0b0f270708010213080705030d0c082b02090102010c18180f0f05161409090c19031a030c06040306091a10090f050609040206090a0509010b04 75
    0x5aa4ac154410703e901907403003580c20032f6900c3d594003a8417140000308864243e00000e40130002405408028440b0358000d544800c4807840d03441325254544100c598920a0704400a0310707050126803524504025180c025902c1e00790780355510198000c1d40343c550300c0083d0048845d0480091650141503840303101740140c560b60004006421242c420000c0000c0c043d0803c50560845c2c00c000c441d00c180d40c42503125400355034101c2e090300043d0103070741c03040050a824400d0100200780c140d405140700703040b400c0401d101c4003c0b178442038076122103041c600001d4100400841650b400d1a41e44030b80c00c1350364100160320b0b000380e5501640b0b2100144050708006600c1d800c00c003a0000c260203040394101c2049001d071480d0350245001404ca0b110740d100c010466521024560305101c2c070000600c1d00000e90130502807003403500e11820303900c010705401152400c528080d0185441d1400e4800c651244201610f10b009607101c80e0200b161640200708040c0d440354404401241c00c3c0c880d0b030403080c0208078035103500c0d450ba41803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 734729730 1250 734728480 734728493
    0x519030c21030b031603030e030312040b091216030c0c03060219030b0f010207030f02150d050702060a0207030e220f0e190f0605060612090d0905010906090506180409050a 75
    0x14008103078401d80c018040c40c0f11100f2041503900441f070345428070303807940c2d04000f001c281540180413070419444107100400c4103012203440054483d09108080c2e642000800c4255a400c1c0141010141800c00c80040080004d00501107100e03024004c1c046000d0103640c0f1fa0b140782c1668450f940d001480c0c06d00c101400049030301030081e001c06c9a012180d98070b081c03a43e280002d41d20b0101e0300c805007100d071081c46044150348807281603039880703008128243d586d006038107540c03009000d0580d510401480369400244c5400642d1003664645070341541d03824000c4880c03c04201d01c041c03241d041180d0801441003d1040c41c0090721440030025103180c0c1c0170402e85000264581400074041464903c00d00c81c0300740c0e100080468090035200380c1d000100080c203450740030118000d4000c0d091603200b00715261702030010481c000100c107032a0020726581c10101c40d80710f00c011140c20352203100f104041860381e4018441840e01c1030207003c1001c028030124001d01661400202503a42d007003002e45240d0840078040052000c1d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 734730980 1250 734729730 734729741
    0x60513020901060e031f0608030403051f061202010c21110c0307060e19030609060207060e1b0409060f05040f0213140604020918010e06040b0a030519030c2103 70
    0xd5800d01c903010340203072401709132141460321903800540003101c0314120000316a4086070180c058002142e495507168035100c0d90350980d4070300074031240d4090500780d03003c0095402170f017054440d203185c1040051050760044d00c5075006c0c220300b16516900a0f1550f10340c8000c2c0308034500340b02101c0d580c9245e0200c55003116805c1180d002d04050080e04829028081c0541040e50b00556030340c04d8400d24250b0b0800d103111180c003c8281c10007010780d400c1403150414030243c0d80141c80f030345008580c200b1146401c000484e40d95404992210260200201a04100c0c6455400107124501a050100e0700c61a18419141200c6c0308880840ea00164000c42d01c044d4100030340f071000b4120080c003041020400e04e4140000500c00180040d00c9548c0003c0d0485c8907031a001072080c650200f02180d0b10f607950710b9448841d8600c0040344c0003405607192084040386480d0101c3d210f000c890300071026105024414040c110b07910450b090650601903c1400e40b0b000138409420018a1841c4009400d07003138203d540300406803034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 734732230 1250 734730980 734730989
    0x90803100611070509090a06020a0216090209010804121803081908040b0105060a1e02100b04180209040507050907030504020109090b10080a1d010b090109181509060513020901 77
    0x400c0400b5000040006421064900450300148907695440c4c10314600502d49200610950000c1070300c8900c15000074050000d1310656613070441540e01d4510032070403400f82001c840e000031800404940414210066110981e00d00c0c07070850a40100c490522011130344651045840440c005920f886050608070b20750b010110615004049040c02c0c1c540607440310040c041c0d144113120001d4041d1041d40503000c0415841c000c032048001c00300c103165010b0f45812001c91210155400c00102c90014502486103581c5d415000d2000c0c041c1d12141d0b000e00c0b00d802c00043c0125454420024041503d0360391500152189455a03408101441c0604c001000041e0300c1c0e015500040c1014184030481e81c8140b01044190460b1805c48103595407040d481c030281c400b80350400b065010034100303014030107810b412031313540101e003075900001d26603035882c0c034100310b41b54682e034001195800d600300400030b00a141c0081c1015000003010403500b140d500c40b102241d906440d41140743c0c080900d1001141419000c0c0c0b070040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 734733480 1250 734732230 734732237
    0x2040b0f0706061d0c0913050a0507080903030106020709090c0803070b2406030408030a09140d1106100308160b011409060d1212061d0405150606040302010302090f040908031006 78
    0x52200f9102aa00813014004810850020584080036110100c080f042285010383c1032145042c10141940140415548800050a92400102d44110010481c2d0490b4001d600614134185010700050051428100450b1030060951000079078200801c0680300c01401280d42503018205014103020120b1243c000383c1c40c0d03c2100040403c0f90b6a44404d907a40907402101300b41d500da03a494502c400410b401c1c5002003200d410307000c0302046001c00259020660406803034040c803e0207441041683c8050888022210402d281806d2000600759005403584800103861032001c9101130703507003c1543c40c00f40c10091102100000f000e4141c5490002160003200c00c0d034013940800f52946410703a004141440707080c10300c09229156031b10f600069101c00010140348254503c80d034903c001c007450401098800742c03a00d1140e99400daa00f01c0007071300d0103809000c0c0142410720f000e1a507401500a50030503142160b1090401808250315207460052a04091144a08580d42d103820040d405181c0303c0340d00702d030080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 734734730 1250 734733480 734733509
    0x12040f1e06050a0e01050702090103050709110c06070f020a050303190f0c09061d030105090d0206161e030e01021b0709150e10150504050a1205060a0f02040b0f070606 73
    0x10075000400c803215030815180c801680f22132100140c03054400c9200c001d41211100d0b00010901ca0040303074000584440480910071003440180a0307265015a12401c82d1942000011415540c00748500f90000c100500644010a0a507164142960011a090404441da8081c15110251325100d208100d4100300400c0194901980e4001c03c2008070340551014010711501c0c410300c84030f20803074100c240b0b01d006000f40110301c3d182d014680c445507507140350f802500c5100d0100b250300114035403000c02c1c1895541c1d0f0310078501100b4104014110950b00100c1410740c1d5400001400c50203000030500b610200036140740100c002080103103081071503885214040c2c07900c00a240e908001e01f000e4401c03245001400105902c401481c90100c000691004141140351541410460b030454080c0c001c860f0304443d0b84200b82c1d6100b0408800c1c1988000080c8160000800107002d0758413640114450f40b015000141040d80702d43c2400744613488806000c0c410070f00468030404000142c09800c000c4c2c182446460203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 734735980 1250 734734730 734734739
    0xe0f040c020c10020f0709020909090a02010f0311070c0608040c09060513020f0910080108010501271802191a0c0c0105070f17040305010b011e030e12040f1e 69
    0x440d24031111a0754441c8480360f444a4902c2e208002c1d480c50f00f041c1a083e2020716643d07100c40002980701e0180607001e0003080001480300c480105e00b02c406240c041c0c6401000f40038241c0c00b00c3c002c007034000004880c03d2040c070100700030402d440790303480152080761a90078850900b41440c9880d00d072964890106182402010301c03003512000701512040c1141000941c4407806424041d58600402d515550807200500703203004419030055030503040714a014006c0007140d0302c50000c0d0102040030446011800e40b400c0c40902500000d078846d1f03402d03100c08682c07100080e0060b07001940c03c40c8030901400f1420b403203100a01c8103100e5922400012883c0400d494608002c01061175160503003510068180000411650240308081c0140c1716010307070002c0e24001d500c0809142a6a64106000c19100c56181c2506401c1c0c0f54000e010503c500e4080d03c501202070360a102e001c0307025101f4115822414002c680701008541c500c0c00c080c0014281d60307480c101809003080c01030301c0c02c00070303900030303104445a6441d0420 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 734737230 1250 734735980 734735983
    0x30708041406103f080d0509010209211b18070809070f0e01030204050403020f030d020a09050409020a141804050f010b0603071202030a3806120a0e011103070e0f040c02 74
    0x460814600160400784004d030078298030502030f000c03442011741e05003001c0101c80c11043d801012104011030b410541510400321100301c116880b00702e04000d500004000c03490759200721141c08240c100410f89204142400007510f20030800b0b0f40c60364040703081842444441c084c14070000c0e000d40010404e142d000307407500f03402e00046503042c44040c5c00b0b19a904089000d0610900c1228507524003c070403a80e461f44220b04140c000d5100281010001b507203243c0100b800e207014020303690f840e90010080e02144c0d0419940a4681c030500c140d45500200c110318041c10b010984c404944614000c901030305802c00c500c52850300350780000e151a4400c0900700200140550030288804040141140040c0c595842d14958002042245800310000c90058114030700300e480124a207586628208e0000b9018a006041c0300c140d0040110304424000c4000000c1d10b00e00081e40002e0f0700340c039104008907141e00c04499000281d801568604006244007440002c9414982e202944885083e0f81c2000070b5592290002e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 734738480 1250 734737230 734737319
    0x52202010507140a05070816090b010c1b050312091305060d110d0c03050319020706020a14161814071b1106180f0a060503070804140610 60
    0x41403d14800450040c1410401c013000320a903201044440f00f544405d0f8031659544140c8840c60328042c02e14000c20348140c51b025400e4680700607140da00706a8025903480d182075018040307503503220440380f2000609030360402c141422611002c11a80e9140c45a40a020541104421990041c2e0a08041c0110b540381c0d82c44048075070b500124164640313560500010340020075504054440e8442c02004014040081b0081c42584000825080d05ca0f00d02034040c0c0e1203080034410100560000d0210708040b030700c41c4659051909104e02a907440c0d0400100b80d415152480c1c0083c01012800c900f550081c0350700c0e100d080307082451000d5005003850304905c001e2041c40b02c0090076951284064884041060600003200e1080c4000c01c0c5070f844580c07e0745210004080240c40921406c020610401e013400c22818031b070142c40140d56a2880c581d1102e0003601c2c89000681b0403907810000d454042c0c00118240b05103408ac110000840c50800d140024006034205400000003080ca8040c50188040d488190305 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 734739730 1250 734738480 734738483
    0x6030a0b07031a060f04031401150612240603020a210c021b1c0302100509030307180e070e0a080316020f19030303110d0509010c02060f1902030c0706090501052202010507 75
    0xb540044800200d0712402b6040e000643c422080e114200401c00c00d1b040003803030b440140522410401c0700d11049070289104c841403030300511006900b00900c0b803a48a50028112100785041180301b4520300c4525400003001d41c5110b540c040d545110300c45140c0d07410302180b5140c2106c2840c4129482c1941c0000700c00c3c0f400340c0601c90390b081c40080d411003054024805e005d07503d00029002c10803843d20007844c0d0f0312a442203a005001404c808042006050f80c41c241d0010303248141c0034450150303030340082a12144071b140d2364036600445000000503801c804000604444250401910605002c1d03c180960a03104458091003240a02241107070349100c0ca01c400d0880303170185400f0840b510342c184044071a01c1071095940c0140c3c102002c201c1c0300c080541242441c54815400c513400c82d40c4000c101d0046800c2500c8007482007010700304000e039460f0030b07802441c0c0001007002641e180100903a0764500b11458018115a580d444908124000c94811042c0010f104601501d400c500da69600003006031107403640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 734740980 1250 734739730 734739743
    0x1208070206070f0e06340809270c0a0f09080316291005040504030c06111c0c020610050f0405041502030702030d1b1706030a0b07031a060f0403 63
    0x80881040e84200600d404204c00940f003690386249846c00790208107008900703070140000c440408840300d105503034810000d54009070304030b00306009401003001204640f03c0c0c50b600304040c009001307110b440640049000305000c1c0c820f203565560180000e00042041211141405013407001007000c000c0100880746010381201c3c4202041002e40b500d040b04040342c05400060b080007101120b90703441d03025040c5002e405001643c9203229510020803090f21821200200000c41c40b8101000048550f04240103c0001014250400d00a145803005034051841d00007004c41e22291030024494040c040960402d00b90300e0343c00403580c145004078414815552405020310754075000074007400700314114410903418451041d941ca00345071000940c3d070b80028603509980351922150712740d150900d02840985601765121800d440d004500000301c0040001c040319014040d50054000154143c04070310b1003603490343c6000070150f00392141e011401c91880d914502400c020081e160040d03801070140ca040760783c00300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 734742230 1250 734740980 734740997
    0x18040501122603460501090612140f06040804230603190603020a060e0306010b27040f0c030608100212010b07210323040f1502160c03120807020607 65
    0x580d400419044c2030302c038000300442c101008030705682d40007004081c3d000c0030300611031a600c4050850803036046100b00c0e10f811512800500010b001c891440005910f050207840804c4500100c09007000e6048030110b8400d0302c001000e21040031207541d012000180d080312204c5801f15000841d00502c4082c107140164401200b4001c131400c91508280c02555020f0301c80300100b41d90b02806002110003850a500c2401408000300c1c042a001042d00d812445400ca40c2d8a01c855014560f40300403001d0404c590404d45070b014061910703945004018a03520160340c0000d030540303082c0d521800c10048042c004a01401044104d9030032000384842c905641d00200312594034500303441c010042c1140040c1000640c0391411100c0310160b0540c0c0089060301080c4c0644110140394606880b181000300d50040000495001e40030116440c480301d507548141c600b0005242c111280201c181d03040c102d80c002c0351004101342d0140200410707030a403c5200103a0b414603005a080481029440d00c00c020300260400c000310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 734743480 1250 734742230 734742271
    0x20f06070e0a08071d01060819110423090702030f091009080d0e09132004020d09060b041a0a0e04030309210e100903060218040501122603 61
    0x242c1d440b0062902000302c0c0c103101c4e5580d164100e044085542507100203034890000039014010141e1621030140e0419101600d1804003202000300b0308203d2585c03d021050001041e070035491644401c1030094560090540490541000490b06008043c6001c540082c40180c03180c40d5181d0554210710340498507028540c0c031541040703403500003543c0404201e224140703c0c103010b1034020031024800070050362030060903904c0103d100411010b4500081c80c01710051001c0b020758080740c24010030111300400141c5043d400002c0350b42071701d01d0031100341d9045035581c0c2e86000c1c62406224801203c05000308044894040400095008400e8421100142d103480006801c0600c00d50180a0199216501154141c5001d684040700705c591190400401c00c01558198145402401840a505030b540e4000400d403e41c0d594001a41180d441d00fa10703554003131084060b0703540360f00a090103003400b003500c41c039150801d08082d41881408042a03181200202c0d82250120300801102e07488091454182c0902002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 734744730 1250 734743480 734743489
    0x40516142d0712020d0f11010b03011e0501293103110a080d0c0f06050c070c090b1818010c05090a06020102030c07020d0f0507090b10020f06070e 64
    0x14140c49403102400c056445008500704010305a0503001d03140f2494011a0740700d050760b4450b44400c9440110342101d01c1c20002078464120791800985c008004103100162201107400e40d1212442469000340d01d00c000301303169400780b00d072500500e200107181c071100240341c14545070700704804130f4500340c0080001d8406050134041c3d10924210a405041d0701194a0441c83c0c0144000c1800215006003a00072140e11a1030111440c0e02924204030240c20080c01c4802d040d1603040c00b01b0000c80d943e54500d0080c10104200d481028414020020a41da5805051400b26480f01d01d41e004603504038605120f1901c02e40350b0034101010146811180e039442e40f1f6422103c4120b03040c108480102d0340c01e107204140d902d540203000c3c00000009507081c80b035041d20b070201030b4241d0204480c43d9194a0050000c0009803802c1c1194040c450b00410003c0001c220a881d4503003001c04d25000041943d40f614901c0d441820218100050501944058000301c1456114107071101e4002e03000804001c006454080147d49 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 734745980 1250 734744730 734744767
    0x9070c1a0f0702010e06012907050601050906120a1101090905070c0209060a0303141e030708060a09050103080304060f15091b2a15020403060b04051614 67
    0xc004511581410640100d02140c06007141c81d01030308540680840d441078014090042550902c4001e004283c1c2441c828400410381c0010345034051540c4564088991076500050141a000c0c5020384819070405081c0020501c0203010700b4010440400b0042c40700c0030209038818105e0748000381c48040107000d00129040c1c100c84e0011008280340c402440300c0160000048a8898800d407002c40340b80d82c0c0d001c00c0103880c48036403002030b0104112684000d4032881c0c04000304425003daa21841ca030041e90039040c00aa00110740810100c1c1030b40d001e0080602c0d100300c003c00209a43d80b07040c440c960441c1e075540603d000140005082c03d0711000400030b80410b07504a00802d49060099180c2c8070398500c1c044011301140c81d50b00c20002d49469580404070710566044415040012a110030039102c02c640c0e1225140c9158162a40030f940311800c0321060b0180000e20045001c1e140c08981c0203142000c001c00c03101c001d05141514108441e041031413a8218032581302d40001849455260203042c070700c102d81d021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 734747230 1250 734745980 734745983
    0x1e06010e1e04060b040b180402070c060c0b060402030423070902030a0b2d09190914010c080114010f0e13020715200304060b030d0503310209070c 64
    0x32a030110310700082248409503903850111402d2103104e03580c0c0620486445075026100300d01408202a51422500d01802084140d028200520f0403425845810819003160009c2c400607809040c0303001485140110141c101408840452a5040940d54024002c02c081e0203100210095088040c100c44144421030050200e180190341d00c1c40c00c24000b00081c07084400031885843d04070007502c0034403800d40c100707012081c1340d11600c402d5001040401107407030001450070038807040382440442c01018901512a001c1d1081c1c0101d181ca181320100d003401e54000c02501810424814010429841310340c003101c41104080c00c2c00a50300b171860307008403410f08042040c01d8100e44009444020003441c0e6004081035801b50b02000c0c040540352100d5425101d2103100d01a038056080040314254081400031604284140000212400c000c3e000c00e0a1100030302c10840499008001c0043c804001c40d1f11a0010114850750003c4681e02e00c04042d4082c0e840c1c001a0107403141ca030002d84600c1c001c000e03c40d40750b03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 734748480 1250 734747230 734747239
    0x50f010e0306090f1908031b071b050f0301020c0601210501020309030406030c02030f0a0e04090204090b0703051303050d0c090531140f04030e10021506091e06010e 72
    0x38985510f12555814400849200300c1c80707410505103482a0b10f046011140381d2108059145858400384886054400c10802115030004c03c0236200040b141c0504c07611a070ba80701d0040a00714a40000c0048680d200e110441c00b030303401000810300900022952905480c0c852011107104020940e04140107000141d004286610000c1401081c505c000060012550f40b550f0074000b80b440c91100700d03203c0c00b0b20703850100780c508107001600d00a4041d0310740341038142d005040041d4998050300081c0c00d9902924043c0d801002d0041888645607050182940c082c5401030000d40744c4100d542c1c010301500c40c0c0041000800d40c2c0d40740506165100d0600f0704003c10008011801200c82100c000d5660343d2a811b4081100780c000041d510141640e0040ca4040d45031151601c2e5107a98480115400401c0208100e0802c50680c11aa103980e5a0707040040707180e2000c0d8024110b8010f00800c0801842d000f0b4071700b40c4200d03c107804104401c0d5020000354000900a580e07003a280d1180700040c2c0d801020f5000c1d0f0b5a00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 734749730 1250 734748480 734748493
    0xb09030f040608010e0c13060e01051908190b01051204020a050a0803030910110d0b0102071e0e06040905190c050307030609060c030501030203030405040c090f15021e07050f010e03 79
    0x1440c1d840f80d01d96050b13038060ba1228200d41c441081c10001c0e4400c074900c03840585144c080400403e405900108510141810300c50b182070514007510300e8041000c1c01e14004103106406104006a0150320601c1c44a900401040b600002c000083c2c00d5008001d1021004800200007408544550402070018070014209054454880c10850f449030000c032000700e02c6100e90303c0c02e450310310020300a0380358030324a9445e440e280880349100603000e024911401415407065140004006400080850510309022000a025410040f01114020010b0942481542408000000300705c0103d4030304400c01210303010000c40803240c0380000800c106070b442280c0c140505440001881820342080300310380e01c194010421580d0400058084400a00001c5c0d0540c1c414002804541403c1c0d11150250540382085418150396007070361400501d40b904040c1905801c8600c1d02c040030f0b010091010b030303219000031a007058060400392a80e680030a00c40c8500c01d46091041c2c2e26207901a010683c2d00e40b1000c0c060f1000f = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 734750980 1250 734749730 734749739
    0x90e1e01050f1807020c100c0c0510032414011e0c02150c0d030c080f040b09010e1207030f14070b060f06130e011401090b0901021207050d12020301030f0b09030f04 72
    0x444120480440d4068001c0e4280201014801c1ca83c0a880341c1e48270711542082802c00d070070b104404103108150b0b4185523035642c0f84003540501910426110800000340d001545c28001040c00b00b03001811410305119102c0f844041c1c4544416040b030365402d01c0d18046140140c43c0c0002128400703143c041d00865000010041c203c48008a400700150282c2d490500000d00180c00441e83c001045079060000142c44c000305000980d024031080d0480c0300d200001ca0b10708904058641000d060b8030440030508000609403042640001411031036807014280030480043d9030410b52003d10840000a12500aa070000380c25030b03540815104171a03c01400c89516021041c1880ea9814810b01402d032840f03201100001d00817002188105580c001a515919190f103484640003098101244035410350081c054000709107000d034000740c030350580560002c1c00581a1500c1c06003603241c12840d40c005960040006201164501c1041c860141c2e1002c0580710b1a0b032004040e038210b01032038280c200c07950800940042c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 734752230 1250 734750980 734750983
    0x10203011a031302011d030d0c120302040e04150f020703030504060e0304180207061b081f140d050a06110d0e01050f13031707090e1e01050f180702 65
    0x14160780420190800780c0d40c151191010070b00040381d241080500f01d200e24001540308109034130103211240340503006a502c410001e070516880c1101c0348001201180c0c45818030140e00000041003105040841c5024109400350406013401427010b041e030140c0790354008200c00710740d11410001c02402421034855407146002006040e00b601c0c1614220b040c00c880074414000803080300d0813140004a0005a46411000352001c0d42003440c040e11403c0da600210248041d090500e9a021141503803000214640044026000c440313840380c000ea800d000010900100c40400f1603190788a030704480524803103040d454918508010403400078040c80c1047ea801d0480544440544002000244148041004a1556400c9400481e540c8441d003858401144d03411401140601c04103001e45041c4c070b030080c039a20a03200743e2502a1010710004038032000c1046941c4017010f0054006000e42d10b42c6001c0382e0003001d10350002406002c1c0e14850001c210100317110341e840e600f5540c070314807416a580080e8a45124003a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 734753480 1250 734752230 734752237
    0x306070503071701181b0f0e03030408010c030209031504050c0103091b0f0504110304020d02091b0309030301051021051911040303021e071809150504150614042c0102 73
    0xb00e07561420045907500c2500d0106d12652040e80a90380d5002c00c0b02d044404840c440d02c060180c03900340c00100000700f03d440f0207000ea0031261190351000b5030344100c410b041c18900600042d0421034040b40500340b10000708041000c0200704000d203408210345e092030518103843c0140d4603d2410102c10f1500000c0c00d0b5002c20103141c00c5810885007005075249103d01f001d00c1c0c4c0f1080b80c00a6010703400310701e00720040c074003241d82c1d03508501c001040306503903623240d02c481c906079006862580d901d5001100402031403410000d100703007030300303080c58000076050b1803e1010340c62065120607442015103c6d000208007c200d10401103000c100c1030414062902c0a4036881181c0d485404154010300482d000d60303990a007400f0f090340384a9455401081541d1a240c03100148000300c5240800d001e450304402d4021491512006ca001507250a00250b103040a1800030b0198806030030301308019007072100c1040b100401710581850104103680101e01c40400031b8021045180c180c481241200302940185564803056000c0d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 734754730 1250 734753480 734753519
    0x20f0f040c08070f021605040c02070e18070b040803030f041b060c11030705030703290405100c110309010804080c0604120e190308070201140c031e04050306070503071701 75
    0x51040c0306104441c201d031200301b2112181c41d4890301d40740030065030034142c4c0010300c101030510540306c100761100707507101d00298280c03100d88100c0d22070154640340788020301c2200700915181000900e024a80014035499000051881d07000320308490025080c4051400c4100810341d00c00c40b0a098540c80b54009030800320400e000b40c51022488004000c1424006114400d58500400400702540755580340c03504001c1d001106d10800014000f43e0baa6800005002030241c3d01c00c1024203c1107102d0076040013110b03d0803020f1070410105c030440741c0d03080360040100c8042c2c56081c60003e80a5449003440c90652103035104e071000c18843c0381d0821040c0110600c030580803c00555a030b80501c0c40c175404014a41909034103401803015003010400014074035000070500d4178410b050071030040e903949807040120340244030080001d402c001000f0302d00c1100640350a1180c00850320150403c0d050401180c0c0d91180109036006120340000402c04040c0510f400441c41d0380341b0403d429807076031a0200c007682e40b01300300c0c2d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 734755980 1250 734754730 734754737
    0x6030204021605070e04030c151b0e1f05160309121424190e010f020307090e04211b11120102030f06091003020a0902041707060903020f0f040c0807 65
    0x40071034000e4100070708034015034144d0b4803e4500d4110327454070303d502c3e10b03641100c241c4182c0d51003000c40d10038410f003036012902c0d12035101d060310340101d1400c1c014850b030403c0d5124040050018145040c6410ae0145c03404082024458219200d0902d0142c68030131707a170b800400c1c81050ba549141e0802400e0603803c0142501c2e0001d44803002e682c3c3c0d0710800030020302c080c003024040d0340200140300242d01c0b131540b007c90404d440000c00e41728100c10750030703084841540c05812141d03000010400c10540100d4148020000381c026840360b441c281e1200c0803500f143d8909550000c104840c0100383e24804d41c035055400481d0499110048054600107032100303008000d0501a014200c0c0554208006100b0340f480f030a009200d0a140742d44810800007002d800400100d12000319007800320141c1c44c2c0050a1000d44038038100140e0310b60a0208480f051b400c610400100c9900100c001d10070168041a200300f102e505903a100c04c402183c000081014014070780494110703103015030051050b9803050b0305501603081d684 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 734757230 1250 734755980 734755993
    0xf0b090a0b04080c040f1b0f0e10051602150c0303040c300302030d06080c090a09020a14040603020d050a0201030f06050d08090d0503220806010303080a0f06030204021605 75
    0x1d05550600542c031540c2031541110f12021007034102500290403554104000203142c0704450120300615a080d103400c000150101400c0600c030303420518194003144201e4592142603200c1e20010503070700c070b069000942001504054400c5446289504000300700889225496a04d0b41901c02d680c1d070030484090301c0c41d200d4440c00044020403030085051030061500c0c0f0340c004140712071a5889031400c4510480031840104044030604580340f141340007400504c800b40c048510700b0b030100003402c013001c2d001080e003515040190b030040e07540e0880d110480b41c40c501044c2d00010341c00c00280041280d90310180d04003484a1500c0104480452601c0005201340c81c1000344448031080c3d1000c4800034003034560031400040303c0750041408070014103550140203042d0903501c51540d071481e00f103400001c444d669103400e40041030010b08043c2a800060104c1000400466141d918010f00300d4a0203800f4030810b130b44d14a8603d500c0c40481c2c01c041d0207560003038025583c6e2140030070300d0a82c103410400151010300698 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 734758480 1250 734757230 734757239
    0x6091929041239030e060c071d0f010608101508011d040506130609050106060c03090b0a021203060d050a03090914090d0f02030d060f151112090102070f0b090a 70
    0x10003038101450040440180c0741c0016031100701c46050240420313801e0100411130b1074020f6481c0b100a0071000801d00c00380000500c0d1401e900d0010078480e0b00e060f0b40300d40c001c1c100110b00c0044140c0c00d0451307840d440c01451544840d80f61819405d120b4100c0e0500a05004d540f070506074004031014122942e40c8000a0b01c1c40d6894518554645c1c143c900400c103030030010100f44000300071040d480c00c0c50701801000032000865580c490840f109644040b0100d0742040e030103005c0c10741050707800d001061070382c0481e0b2038100c01c1c1000948540d001c1c481d48201950100c040360341500c88c1a00721840542c00400c640310280d450078003611900c594170030700c00a1800d100f0a5010400c5602c859401844201d004110700310b090002070b6002000c003144072045100500c8811010755250045030014400000c1c1c08074810306140303040b501610700036581ea040c440c1c42070400e02442d00001e0600013041e01505003a41351424180101d0420f04958408014005540b00c08915582c82e04010101c03100111038a05100d03544 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 734759730 1250 734758480 734758517
    0x1e05070317090a06050a060e09010b100c0b1f031b08100e03030c030a2706150e0609040318080105011e0807090216020405150102060919290412 63
    0xc5600550941003030151100003444e54005035080071072543c010500710b456540d040e07480201281e4450f101ea44418100d01141060701840c2c200c80394602c1d1600041442d600d0b030f04800840070f4003442015400f511041e0070407840c0740310180910360010010f404140710f1403400f0210725250041018034010f00040c0040310500e40f01d4000c03100552400740d804d6a403003080100380f581000306028140c0c3e4403071160020800c000c100c8010ba090076189107000b004d8503070401c603003101c071120003180d00c8080f201b105203c12201800e066a01400480d81403c00d03584600e412107031250035510190f5034002899021402c1c00b0b043d00407a044c0c0308104107804007600308004011400026100d50342030364101c5a000c0c800780b120b07034008217140702c09007c500900c1000355010600721031040724200360620741005080e51b03560381031180d1600300c02410020841183e05004100c02c02d106904010300440d24a0b0440c030459501008003492174061501020091405091600a081000a1800000c0c200200d0209400f00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 734760980 1250 734759730 734759777
    0xc41031006110a060b0a081213060801121101020c120106031106070c06051615020d0f05070f0c02030a0b090c01020f010606020a0303091a0709080d05090f101e050703 73
    0xd00d9801489112843d849040c01800071100254211001d0708000c52142d8081204090b84096252029927800f0410b64030401c40c4500e40003030040181da080104128086190300c1d1020a0704020768031103080e00040140c7c0780101c0300301c40d01d0300702d009001e04ca080c0b40d006601030402c0381d000f910901c2c2c40d00c1c02c1c042000320601c81e807003005009007003c85050000620400241540a90484680348603040585859215140e55100500c00b6600040c0207a10320020b8045d20b9805681010113002c242452400648185034118180e070400c08020800c80565400304155103031150040b00390300d000c1c2401016641c4505007080741c40e001d0702c10540780f003540c07030014450042201d1440d03028241c0c070704103a0781c21000380500390015103034101b4580d1800e01d009402411103000340d0b180d40301d02914515102c1c1290a0604071700b0204240241842440c072991540171801e9105001264000300324840343c0300c00d481400c1002c0d400e1070b030000d032110341c000f000d900017008050050080c1c4641c41c60304401d60412042c900b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 734762230 1250 734760980 734761007
    0xf060e091e10030b04210309050a03030f020d1e0c050403030c02090627151804230303041b171009171305040f0c41031006 54
    0x460001807154040901216103800001120030406030300d43e2038035030000c004400e650a4034845402c10101018034420074250805803d103003418881c0350f480d902c1d41601d0701004a80a0249600d8803040310900c02aa411201021100a410003806140d1001103061a1519070599450b6141290408069002e03500f55011a03600d6078a0b04113143c1c566091141080002d41041c4d001b00b0307030000302040c442c0320b8803e03000c0d1030313410320b68003c5a0b2500c1120001d50500d1040258081c01e03c6444414040903003074500d560094202c15003030201003444240e06c0310b07200700c1144104036000c0030061204000c0d081c550000c03501e54550910032283d88a54000c80004001382c030400703044d885035103e603024200d182c10080e01d00c0d002d0381003540c0000d03094031440d41507404900041154002003000380030381c3c682481f500d0540c034062407040003107952010001d00080703003000300690320001034950600244a03103800c0601024200c042030f445d81081e00090702c1245c0081d9400346d40c031010b1403000300d440c920880c04c90601c60b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 734763480 1250 734762230 734762251
    0x105030d270e01141210200301060f0e100e042004080303040c050406061d0a05150909090c06040b1c09030c0b090a170a180609031a100501030e0102130f060e09 70
    0x50402c1c141034018030720085922121031001f80545021143c040155000b000b69803164804212001001002c9140900d0041d2280c800341c901c004060350300c910310540e901d00c01c2c2c40003d41090980780484002d80901c04e030f9020f88600050210b0410400310245009038441c6402c1c2035255110f1041100b030b80d8141c05000d0001d0101c440c01c02110700e485203190215070003e061001015201c8000c2605c140d981200030241e02400540341c140350070808a8607601601a201070410300c09004005405440342c2c3c0309000b4003041c082070749091800c40c0c00c0d0f014a9042d08030000c209818141c90050200d04034103909843c901503240000c0c1c0c00903008280012240d6202541558865901c0c12560060f08484142c02c20465070041908015001c03000c800702504003078030b42d00303011495894880309000380790707041071842c80d480400e02c081080c034a820b200075103200742004170303c031240c440045009001c0c4000d0a440c0080082002460066036140c00065a045030b0b00d6401c0341800900b4403841000030346010002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 734764730 1250 734763480 734763493
    0x3030615111506300d09050a06050307020f0105091b0105070c051203070203030d15212409030903020112140114180405010506180105030d270e011412 66
    0x108500702c805182c0c40a401022424003081030141c03056108041100f0301c98004605409031040d207401c005116006619243c4a0125410032001c2455400380340b1450041c40346c0407000c1003015009000020002c40000000c204510744420700c555a56071032400200701002c554034840095205104030f0303541c1900a800580d149141070107100904101c5100c642182c0410321803100107070380c14401004070310140302d0080707040b408000301003030041580d5020140410030b928460900195032402561490707084040c0710500e142035000004946680702c1070b02c01c2940742a828101305074100c0d1900f820750307000707070382d400c8192600040c00400c40c1c041c500d06040850341c05c801004422000072140303400540c05030180020307904803003035050b46c1401910704982c40c1c1d44400400111303003840c8085061780282502175090f035514000200703484903d84c1070031000b00110354248030001680807070f10503c251424608000110340c3c0383c950040318003081c014006500d03a400d907603280c0e500e09601003422681240b4050280d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 734765980 1250 734764730 734764753
    0x118080c010c08040b0f12090105010819020102071a030a0e060709051915110c030105040b15030a05100603032705330403030e03010e07091d0a0303061511 68
    0x80c03a030034900b403c5880e01410807000c40c00c184010080e02c45241d0042e120340d1582d030801143e00325808000c2400e1101da16241c010841c0341d000288005c01c2c0ea018012004e04000907000403030410030030340c2000c008051040c0c814249845000000d621035503541c081081403d014111564480b0401e48441c2c0008200311030500c4103290241507050b5865050081802d900c0d600c00350080d041d54415141d20216149150f11030b0000400d0100311081b0308200c00800940c42c1560354102180409010f0700c002e01701c00d004450042d142040300c00404c98002c0100c48900b05904032000140145004c22000103240d0700c1e54038111200a0034081d007443c4e00c2e5407000000c5007420f09004c03005194070381c00c0050510030450800c1c030f040304040c41c00c0c8910003a110f641d0342c0d80c00c6050107082602ea040f00075029a01d8140d20040b010004a162415907158480204480b41005240b14186401c4004c028060280354441402c05030140c0c0820115081c01007000343d81365880d2420780b0720390b2141040c0102070b000801d4564 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 734767230 1250 734765980 734765987
    0x180f09060402010f110a0c1410050a0206220b01140f0108090a17040f0617060105070b0412090302040f0203010608010b130b032511100b03030706021b1006050118080c01 74
    0x5d2080e58a201243c503581782c80d844140c003201541c6e0144030205204a0a840c1030b04001c40b14040c03150701400e000385040c88282000b0740d40d05004005841024012a01241c0c10101040d00b40c0099046540c00da080d58450207407041240e0f403008100d01c9010315000c801c490f540102a0f86115030214809490031401940b0f4801c40c00c00c2e44c40150150364010440401d01c1c8035010100d0015060b40d41d58071400100102001200d0400540820f0500c01c0610451b00003a425450880e0721640c8200d2600001d445c4800c2a00c4a21450b00020b5215080c840c607580001c0d81d41e4060350483c0d006540d10141d990780c3c1e090385011071003003810120042a01203424009290810000d64201403201c0140080881090501c95102c0410344140005000d025040030928420001102c403482c40c0c140802c500100040000d64a22407000010001600811014044108600c1004c0301d0843d6100340c1710700c82d545140312001807125000d12404961042c18500c0601c0103903401d5010385440c0030081000f04003450054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 734768480 1250 734767230 734767247
    0x40c050f0c010e071203080a1a1e0d06050f10060f03050921070b0108030c071a0904020f0a08010b090603061207270e120403031805180f09060402010f 66
    0x1520543d2510750010080c241040904028018900c000d1034000403840c00400548000e440150720302c0c10007550303d141d00244520380c1c0700b9010841c0c2c1000f4003c0c8035040c3e09001e940200080e584241e400d8022401c0c0985904000d20802000202c11142e03a680c1c0702103481d09585005500004941c28072101045000703a02c40d80d00600e10800301e407041c00081809440b074458028654205400206e14181080310040b4058054015440914184200c0301101a6100e0841c03081c03402e101c648002c1d0403660401c88040300c1c40b890000e001503542c0c9140280100321907000030314010004001000010380700710b0541c10f5420911004058a1854442c039017000740c4c0e103016400f542c01d140501600000c8409100800340b0300e19800450150341260301036100011681070029221160700942e4640c242d940c00c40b0121401d50b54981000e401c55001d0400002c180c107101d401132500607010001c14289006480005803080800314154003c659504240d00d071189070540c0d0081c082041c03000d010404130b0241007907 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 734769730 1250 734768480 734768497
    0x703030f0236060a2c010e10031b1e0504030209040b1e090d14070c1e08010c0207090c030e0601050f1519021501150507020609030307050c0f040c050f 66
    0x40d048060042e0006665034071640b034007070100e010b11010883c441e4070f005c1c504200e003c00c6450071241d08200b40002c0c0503411004482807050100e500011000b0f8001d5108090010f0340a1580074403a42841c0040c041d5140c05103282c90040240321980c10880c410000c84083d40d602900f20303256a1696610001845000f5000004802500400000c8500010141441181044000c1440342660100a08040300380400b10a01c0c0c0002c010550100700104a00c1d4111002c400d1041d001d106112009c0c0340300940c9030403842c4203500741035540314101d03800140e50040d586031290400000e424420305408603445114045001d400c100010800fa2900128480c41e00902506844440004815082c12940540c400d03420f07413041c89040c1b08080d0b41c1000181c0071001c240b0040325980d410051122500b414644600c03082003000106030b000c41d20342714191046020050110b0b511400d06203055a103941004030b0f2240222903400100080e0b2601e4000d9180c03460541e00c4907407802141842c3e104190740000350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 734770980 1250 734769730 734769817
    0xa15170724050f210f07030c0c0803061804060f0b010c031d15070c0f152003040b07061a0a181808070311100507082701050702030703030f02 62
    0x5500704405a81c3e81e030030090720350703198807001504d84040390003c518000390602040511f023896488c060703130300800c142c444260411000c9850346d80344070000c1c690f423070075803806005a02903c00b440200000382d041400a40c050b03900034091520a0401140c00c0190300b5006000215600e00441b89a080d0b0000020400d4020f0b00f03000004d000a100408240e104910468014070035444c01c000e900d42c0641d0100c050700c0c0704460031581c060300e40d000514451507100c00314841d060450480001000400460340240701c0752407480d85481490802000401c141e0b5851b00900920600030562440d0651451040e185d9840050081fa151055014000c0c450341b43c4001001c1800d600080c0440c8144007d00301852086d902c100151910716180c41c24607040d00000101e035400d24041c000300c40e400c41c12260744400465004000c824407812004030074000ca01c088041940b07003400303100420b507002c80104400d5001e40c0f028001800c0d014414012440b410802d1a85c88200b420b4002e20005158000010441c0d81d45 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 734772230 1250 734770980 734770987
    0x90f0f0a06080615010909140c030a1e0b03060906072a0203030d0605010f090f361a060c120a14030106080103060509061b030a15170724050f 62
    0x116035524103c01625221803a640a01820f012580c0c802c0030480901403956041c000b444901c06074488448014041d0020004c003c4002007800110f40e02a0304241020001e0024641e01c2d0f2032050020508035010300e01a000c1c1c00009803280c82c1c001101e600401d0740395640c0c484000142511600300c02161406640a2030007556400560740800141c01682e04c00000012018039200c00035010640700e4621506000084008000d00c000e0043c00404480c0368a55084100000d0080200203e00c0b403038078204442d03a4500d0700c031070000c0181d201d06544904840c0805048400c501003000c0f1780200000030b1620350003c06a607034480c01e00f82c06441543c0040c05c2c0311306201915900e440c4a43c009030884000960481c004000b8490b0601645420041001c090545030614621302c010f101c0075160b45800700c15001000c5010b20407164000821114203c1e0706007405521100c1c40e80c94543c0c0c03404028054800c1c15404502b20f1005d096401c010440007100e168138070306044003942d141d0403c103c1003140e4001807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 734773480 1250 734772230 734772239
    0x6141807030b061c36020604050613050102010e0a021c110907050a08060105160b06012604021207060807180f0801091203020a0f080901020d0c1d090f0f0a06 69
    0x442c082e2486185540d07009501010303a203825011240050302c00c120b41e0507511890000c2c1703810902c466170700c40d080c445400343c0100c5a0001c1030311445560702c000e0300642e0004103045240035003150b40096910981c0280b105907a1030710f5040e40c0d10036004002c0d6100d1090602070004810000b201900144074900500c6545600d200137a1440c1084406201092001032400300322580031216075400348003420400d0824242c000078120a0b041c000000701082100c82c0401c0c52a80181040440441d200001c08407000310425402d0348004144c170220b0042d00500945005600f0100d0300c80103840c0380e0f030b540004035942c01c00226403018403038205200d03070001c90402050802c07500c00703c10060031200002042400c100e1030a010f021b982d520380340080601c140800340c59280e20421410545500b1f10f81466140c80380500b0900900c10464002e007075514000390341c0d400c59004401174440d02800c0801540404200c02401141d5801b1514100304147c02c000103005490381d039104c036410246403000060084d40f035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 734774730 1250 734773480 734773489
    0x9180715091818050604050c010c03080103120e100c06230f0c0702090109050610020d020c12071206090c14030705100c06090c0f0b0f0304020d020105070c0306050a06141807030b 78
    0x14640f0035155500302504200510404000c07000800780c0038641405d400020f500c1c024004041030200410b40082d07140b84100180c400c0c0b514039043c0c0030090100010b04200c880203403441d40b10100c01c8420a048c810700d01c3e0b4071040e55024281c65600790300c0c01362056940c03004107200e02d10014075980b00a40b00348940c101580310386940d2400382c80d294000033100d0a2070010800e454024180c3c0c0d9045501c0890500c2c1800d9000c90131218402081d86e01c0360f01800080092800d103070803a00030149520a0221031002c0c420340d60002d240207401207845000d0a0748481c880d20301003161560f15901944003640800c00d50520520003136820926103056403004100380d80710406e031010030005984034011080e041c01110040020803000b000c2c060106843c016407103030310204501006002921418090003600f05590190003203c0b07400390f1100442c255282c40b03292a07401003a0903900308180c113141003008502c858903189000c00300107005040164903020a0403072281800f00038001d80815895601d06261601c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 734775980 1250 734774730 734774771
    0x803250602030c1b0a020a0e06010c0f0804050f03070e0403180b030a1a0102010b18040206130608011e0305030d110d0e06090d0f090b18091807150918 66
    0x110300c80683e113043e40703615680000510010b05840750007170300b06a001030f030f901c20b182c00403038031000e50b498010780e204001a5071750014a50042d0032001514006e40410440c5001403040d00e000f12008003881942c2c03424503075941080d00031807001581c1c44010801081c0104002e201e000720000710b15226688842d0f1401d4a078100303650216003152a12102001401c0f900c04202c4031141c288020041c01880d02c002810524840d03124440704500035000c03906640380c440c1240c2000791003580300d00c42265207050040900d07100b482501592200d10303070031400c22600c40480d202102d030890010f40c1014041c180e0140242415030351454a8882000000510305107402402e10000e1a1005000c843ca41405d10078140070250f1000010004440600304010f81c100c0c1c080341c20b81e4125981d091300c1c0e030000c00e98030312111301c41401d03180d01c2111401040013081180030051210400601581c4413995502000e6a000200304034010105102400c02d0000c9025960a0340c803c4500d01800709004504000790500b030790 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 734777230 1250 734775980 734775991
    0x9030d020c032a0c0d1e1b120305120604090b01080307140d08070503130501140105130606020c15040e010902090a1505090d030c0b070203130f080325060203 69
    0x400100e0f140700e140c402d0141860f007500d01d150410920b140d00ca114291600340c504245403103900d8075a0094107106082d034820225091024030000140805d0401a00c031074a0500f8031510101c46141c0401d9070a00030046c00c4040790305071a0340b070400407108644424804014003140e00160b80b900c2020100b106100c455000340f03081005140e480a0700e003400200c0d60030480d01d0070b2441d40213110766008180c0c0a81c02030782c0152149070280e240c0c1c4135a00d0207041d220304a42c1c05001907080000200c00d580984000700e0489404407211807412400090010566803584140390140c1c1050315401d00c01d050402112000d40d50446043d4542500d81d0080c4166003c20b8104504859010035030810508010300e4400140104540000d860303c44508010300d00e2203403182c0316004002c00c04045d020540a01d140b180840d40c0100700780b8003403038807110095694225400b80040b917040c810300010103442e88081c0a0030388400303234081c624100e1b124035161003205401400c6d100c94a490101000400d015101460041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 734778480 1250 734777230 734777233
    0xa020408160b0304110a03050111042c060609010c06050a0204081e03030c1e181014030414071208090a0906050f13020c010c0e0907050301030302031209030d020c 71
    0x950404200d285030124100010000e0003961600344840b04509003036079403140d801000c0e041d20a20701008176400043d240c1c0024510760034600304215141c840f80203002602d00c0706081c603ca182da004206800c5004031580070f4003402040010410a092990003800c1c165818101001e8114450b92060100c070021922252080d03408138041c01052001c0c01007c5070080c0100c450000421349402d090784a1002030b041c06c82d04c150016603060311010300000d801101e202c2c008100e858480802800c01400710518029108503a40c22034240c68a00511045c0c1b03414041c000b5250a65607a0f60303408520200844561480c0c0c0304903c00098850405403000318080e00c034100c01525014a40180603442041d500b0005445e030078000180103d4480543d00303d0f80703a0f002c807031002c00e405c035600d4144028410800b12204a500301040592000d0b00511040b40c000740958480485503a4100229003030f000030b00000b00181c00400980704503c00003c030f0f85030040f02e800d043e40d15008588800d58103c0e800408803140a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 734779730 1250 734778480 734778487
    0x40f11130615020706020d0f02070506030705030604060504020f070602071103070f0602060901050118020a03060f06090314030a020303180c03030d06180c051c0209060c07170312130201050904050a02 87
    0xa2060302c002ea501e1440203030006020803424048065107484203503200b8800c00c1040b40c0c1b02c0e000c041c0b007000340800502c000b030030003aa2410400d100600300c0d40101d61aa014a01380b0f140020182403c0c400c03a13040700c001caa00360b801c1c010300d651001c0195001e0f200c00e440602049803190020f0b5810b220741c0c8000e04140101000f62460804041d04002c002000105203074940380c010071400402c0d004c0d40066040003100141c0c0c81144600990052030550046140707641c904c0c501107800e03a04560f03a8000e8a025140d2035480c0460700301403039501d115102031440107070020300119000d5a0250301d200c0c01e0396101001c0c2c4140c540c07209e002c02d1035a001810b484561585840c41000010100380c9400c001c0c80404009108107003454070098513910a2503001208034010000310343da100c91907415114041030040c11030ba5203c255217112035a4640c02c1c0605030080310051200000010000201c43c0000c40010348511540c0d190100c60001d416044d40607030500c0401c000d0b413001c595440c425107100b00c0707042c040141c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 734780980 1250 734779730 734779739
    0x80604090314210a0c0801060507080c01051005011d03070b2a01020315040b15130905010b090a050121020d091e0c050a180b150403080703080c040b03040f111306 71
    0x146440c0252003400d03485d2402168818851b4400081c5064440380d081c0b540c6c2d160b5152401002510400418882c554070b030100b440362094902007140304503a02642d44071103580c200c00c0700503031500102c00001c0d070513888010100000c140c0e0101405040001e00b043d00c03120f221024070072410f03201300c02440c2c240741d50000400013040716403280d01d0302180f01030710208094940080415106001034035012000c64000c21018403e1040c40501405000095018011541d440000f603120744c000c0b40b00d06224141022021461b944507503551040001e04d000340c0c04a40310907a0515000758004000045041d13101d0010801050a01d40e481e80303000001011507012614904040004048a4101c01e00c01d0064100802408600c5003058045a1160100144d543d07400d200040603000c103d08481004000410000f090060741c41c040c10031103002c1e80751054150f0f038101404001c2d100301c3c0103105064100340042408903100c0403c002c0d5051042c000002c02c40d000c01c0004400503460b44608450613100c200500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 734782230 1250 734780980 734781037
    0x20a170604061104140906210c041b05220909030804110405130816020a0b0a030c03061d100306051807050d0c170304030c0e061c0201080604090314 65
    0x4401c240f02002990419041542103518400300c0b2058521505804021801d40d9403050704189401326940740c440c0101d85200a071589810b4003500680c821441c00d00602000300d04034058428411043e61201e24013002d191700388907101c0c1d0307400e10640391002e400300215800c2403a1042d40c652a009840b41c001910f068070b03004c080c41020828641c001d50501c0288503094805000000860f81c0c0300820940300c00541030707903000e0070700d08000103507004144a4002034000070705d40091040d40f0195a00f0302003070b081101d01f40d0983d030700340c81901404904840c8007100071480d0210345070058041d4440581155032500e0343e00540d4810307220043c103261480c000c04e1078200d08120b514018030041c5c980119496190700d030324458019030b206a04d401c3d100003002c42803401c01401281e014592185000e845241c8800c55100354800881e10140100786a411048000b184c00506040840c0c0c140e40381c400d243d407450709020203403000c0102201402104c40c02c042590801501a08c800c08107800c1003003001d1407000401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 734783480 1250 734782230 734782241
    0x30a09061d0607120f020307081905010302030c0108191109010905010216050f01050705010f0209101b060f02070503040e151c0204020913020706050f01060525020a17060406 76
    0x4216222815a1a008441c0402d4159000a16040403102241d2103400500074081c5401540404c3d07100104002d2910303007210110340500200410303a00181000c98110048903428007000c4d600d580032481850b4158410362039140d000c068008c80d005402c1e40c10000c981940c03003c2c2c0d4205142c0d040480c01da8001e5a01120060080c1401d10060610040c29944c10103020700b81e01810380520610015054140d008074210b5104a03442030080008900076000c490094004c210303540c1c854456042c440d0030f6180b14101001e50070000c4000281003001e10760301d00b030003410b00c10b21036900150203200050114000384007510040005000224103840e00091350070104001e00c0000340324042c0281f8070180300990000d40c0c03010030390684005a6440441001400c0d88004c003050308251800052102c040010a800090141604072401c0000d640c1711041641c1e07a00844110b401d0311100c5808044a045c0444140405540060004905585c0b41c81e019080c0803441040300b0348030340c0712400307210400070644583c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 734784730 1250 734783480 734783501
    0x290c0307172514030c0f0906030a0f060f03030816091208030916150c110607080a0207151b0f0506040507080d020c1309031403151305040b070c0c0b030a0906 69
    0x3562450b0303c2154051400050968250721501003407100e45d41c0105000c60303a880000404440d241e10b02140072101a20007508825240e07404d140f8001200b00103803000c00103aa91580710004030b03a07a444049001c2503a40d12072141081107141002480e03406a0303c4500760303540144505a6a8500f0031412450418006c2c441004540841d10420000990307921103019800c0500e00000b551000b420241d0403c042616072507484003000546174100003002d001498852080d40175a42090f41d120341e816404c1d0700e08004030012820018152018000000000241511548014a0800643c0c41c4e19282200071035003110958064541802140c0041000c4207041e13045100803d101e00713120b008285181c040c02111480c441c2c0310304141e410140141c1ca01c1e050700366100c16842c0c030b9103404880c0c24201a580030500c2d01072680c800141c140350440d402050300c100c0c2c104096018944a041007219002c4d840d01041d118001960380100380f00c0380762002540107644040e40865201d030142002d201b01d0f00080360 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 734785980 1250 734784730 734784737
    0x60c152909040c0506070503040b180102010c0e09060409020114070501150b03130305030601110a0c06030c1412090a0507060f1b0506190b090112290c03071725 70
    0x204000a901010903c0c240c076001d4800c1070701c0713003c0f5190582c41c41c0151303007001040c01c6000c87c254075400120b41500c0d00000b0241d009010201120406481070604460200e820200c000c0c000348c13040c2481d1b00145001807040c50000c211942110101a064012110840b032507510303009406150200d0406140140000024039440c50070401d00b190024002c0c500000c0a02c40301200042c15070b0701a10b03a0b404002c54030402e50703800900d11320f00351846401d40e0007a4408a8504003061018502c46c000710340714105245940c2d841d1031810688240b41d0000207040144500c078812114001890500ca4040200865160020a80c200b9100035107015440c0c00040440701c2d0080e080b00100d10001100f64000c8080c2200d40d1501081c08100750190507500710958000c81904000141c048580344881c082c03e00540080501070f8601c40a900ca041000d4004241d07144100042989140c144006640081c07050812180e4100c4048518800d0141100c0781400d5000e040d6404010f48400b4219002e060a03a00c1d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 734787230 1250 734785980 734785999
    0x27010807020316030918150611190c1a0c0c010507020d031d0316090f02071a060a0509010611060c0301080d0810170a060b060306060301060c1529 64
    0x41000303559001c0e180c1102c0108840f00500310505025142400140020004004502100c1003010707000e4002c4060a9050007031815001a100e40304442a40d9800c2d80a0701501840c90092000000c55140401c29141d0304a080310014846214141d50001040010410358071040070580b1a401d0022110310035041c0501001801c00603520301d070f4410b1045605042002140c40d8601c0d8003083c1c0607100701501c2d058480d00d004c18121a4030b00d209181141c400003c20312080a2000e0080141c1c0201c9100411030039000301d03403041608003c0501540070340b0103002c1c202641d549400182c1c0d52002a071040300410b07407200c1d01900d0064103021050348413040c030680328030315403401c200150b8800ba0702d27030034400708201c00c0c01107044c1081103001e03400180b608110813100c0d900b54120480d1500040f0100301c42c0d02d45040355103152410041c05991084200910403415a0318018040d1462a45488203c846008803140f0041260711881900c8941c000116030151110b08814031140d800d0018480610401008 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 734788480 1250 734787230 734787241
    0x705010f12020307020106170312061005030712230f0609090709020d09082b050108061602010e060f0a0e07080604022704050d0906110d110f0102270108 67
    0x10084101c40082450010380e20350326580308a00420094001002034002d40c0d00200f440040003000d021802649002145280c03100d0081007625a0003501140100d00144002100940100088110700520a10214091982c641c02000745c0e0840001c186008108406100912940e451080d80c00b14066039a50720a0906c40080e07503603184988161340c0703015000900154140b2a58021001d903d5105030001d44a541107100c1440c0b02d4000e8804805040ca5a60b520040030a207000b403c0c1200c0f00c0b40058100da071a201900c00079021340f000d00b0000d42d0740310310040100b036000b008000c0c41840ea22400c545a1b00f00030070002c0a035034801070100625400214207000000e00494101c0d0095411030710743c80d52181c000721103600d0706862204c07440c2070100c0c1d0040109011010034622442c1c0c4450f075030181c015458074420f94000c0a00110100e2660025040021041c00740000482030f111580880304403040100302c85083e40c1c0700c0c2c45042404594074a0780c2111100d99641c40011490900708181540b400 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 734789730 1250 734788480 734788487
    0x190b01051c0506010c0c0f0608130f0f081204152d05070c0b01030c060806041406121f0b1003020708370302071a060102070506071a16020705010f 64
    0x1250010140030b0b95440441c155a000c0e11900940c5070780001001c0300180c2c1d40755005004a03c3d44108008a00c08000049014600c0004400b0480d4022114145040c0e40e0b125043d0385010400c0480e5030507400c115414044c85810806441184070b0801091001280400c4205807030b000d4001007100880c905100305150806440704280384e002000010701c90b40ca2180482d20130b0761044000c0e112480e0790300084184000800b00205607003e640340c2800d0b5031a10024081141c4106030024000150130300464000d14014003581c800a10050440d40c80f80da0541174120841d084800000004d40d40c0d0100003294189110407105c81405400c08605010700d94446140d18442c100b11205060407140891140510114226120b105080ca00e030035804038408000c0c0080d030044a0903a00c880044400019124244107164032898041e03000d45440780c9400e040c40060742103c0e10071a004144e0300401c0341603200924070544120079128113401c0100710b50038040e040003e582c1045041042c2208040e407200d81 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 734790980 1250 734789730 734789767
    0x60b0a090e1506040e040b070c12050d0f0e010c0e0a060509150403380103020307090c1101050403020321060d030507020103090b100503070e010e070305091203190b0105 74
    0x12520418650340d0740c0c0304101030350720302d002102a8000c002083c045400350b0310a102038842c51140c0214003046d296800203507a250801907006103101c0d284c41d010300005105101500c1c0700307040d1600102d252200c0e882c0780010b462841042e111503070341d0741d05860001c075400b10421142500503540c6050403400c0100c003c00620400100d00d00802081812601068603502206c000316004007550b42d0600c14900e0341d07100e0280075041103440b1580c5103040070b2842d4104808504880d8001c0082c000c55203003e8401d0040d02c0c441c44036200344148044c400f40c090710203000311071080303100b64061a503401254442605808000c010700701001215420400759846c0d4031840e842c40383d01403d1140d141c1c4590310040b4090400900c0040c50401c80000703000d1044806022401030340ca044041e01c1c1d030035071103a91300004008244035a1501000200100700c0060082d44015003203400001034800d05500e9500c00b4030030394029500e12080700000c0442880c130410500c40c520fa410824a0716514010303007911907a0300c500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 734792230 1250 734790980 734790989
    0xc03090206220b030703020a1218020411160503041e0e040b06061903093804050111180901060305040b19060801060611010b010e0d0f0201050904051306060b0a09 71
    0x1412582002c401080c1d0b40201d07401000c20b140110350b00c0c5400000203010b0340284003000c002c00d40348202c1e03c000d542c950040304020310354600514861066502000054540301c01c02030f04080c0104101503030035220302400b20038503024400540da103614260200341c19404000b441c00b04180203100034031007010703080881034001d500210007054a40700c500001d00d5521503d07440b224120031740c000d08461a50140c02c610b00480c000c900d4440d4403200030b981d1422028000070022028007482210b00300060101e4a1260494050400011254001010941158001340d520310800d0008036281d5902c4c0740100e011805840f1618050049007019520680c011002424600d000a103290a919500c2000e5000328010206980280103d60f551070010300034400c0d5204a0740103500b820500100c0d0b5000b0085864611070140072150781c200c09803100d940714142190100d0400c0000c00205c4c2c090fa90b180900760081542e94001d242c01c00c41c1c5c1c5450340c221a100d600a62030884103000c4103490640040643d07003240e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 734793480 1250 734792230 734792257
    0x402090a060804051507030c08090d14071e0309170712030302090414010b0a031407020c010f0e06041701150605030a0e0f0304080f0d0525050c1806040c03090206 71
    0xa40fa0741c9403d90414105812203803424050400304154546c2c180c200d10004009605c7e4000340d5154184226202c00d6081c40e4800401c4580f50803a01c0020400014015075000c0d030440b9044141082032448a40c2e0340700c1e015000214424010f21000c40e42d040920788082c0480c1c000c010711840d111001c1c00e1001036010103414103502207001100da4549422421301846c5600d001a50b81d0f843c0c00905c03055820010b41000000c1c03402102900c14000c44180754041c4209400030024818004011030300440d03a28031400070000c0c40e0441200c107444003000740000d40b04c055040500a8a0300300320300e01f19a0310039000ca8003007200300c6003002250b800004481e00003c41640105400d080c645400b807910051580e050498480028006038200005c0b846004054660003954070420070040708603140d014604284c0c1d00d0307800f4800c101c41d000100c0c02c81003410710320030420b80e059000c1c0d200020307868540d81d00140104020302010480240307060320030080705604c5030404000700343c0d40f5004120580950415901c52 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 734794730 1250 734793480 734793497
    0x4050312030c0c1c020d0c0c0e0403091a1e0a0e19030f05060411031f020d0f05090109050105070306031a0a0204080a05070e0f0c22091104140402090a06 67
    0x18511004100c81078100d440044501c10010894504c1854000030f03a50b9005000701c04580b140c0394490b8926040040d00b01d41c85c640d44a0504050040034400540200d00b0b0104000b00015100c2112101100000b03038074020f80e85440b11152024128074501800c3d4a507088200045120076800041d441c0b501c29090360554030301a0354900d589a5074a0541010b4240d40c0161042c0041000000342141b245104031501031090080b0824159110140f14210031512501a0b900da4000c00903805440703c00c60007200840c3c03102082070300707030215174007652100f4241e51902c04840600c182400b17a0741e00900140f504104080c0346841d4035803821180c80d2210741c0c0040b2000421110001c1e501070320013034034001d001c4d561004801d140895032a10030b44113560030016100000380c000c2e000c0001d20b40c03180c542101ca035460007045e0004805404c10443c1d807403800d00c06135071010661100303a100c0c010171600d05110507a92141045100240c4108036641030340705500400601d199074840751011400c440c01030802d03034803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 734795980 1250 734794730 734794741
    0x206070e060d111b0601080706110109060509101109010212130e010605040f090917070f0b0c0d0501050f1503070c020d1101110a0308060f12010906200405031203 71
    0x441c4502c1c641808140d04245881050360b0f0000002c1140d48a00b0307075241588840d0b10112038459400b4410400d440d00402d1040108602455002c00c4241d10140001074400456881a08680040d108010030f6400b00c108059140d215200b10540c03801e0300780b03441d0704004200c0300013581e694003010f01c0c02610b0300105441c0f282c600303000740d604d02410244103400c0c52503841d00c000900e182c100d8401c3c029005648100042d02c0102842520ba01c0c540100c0b004045c103c3c41c1400004940c0f0060301221601511481400031411120b10300d0b0140c00c11850607990b500e002540c0000b51041030704110f11400102c148140940e0f6451584030900026403134071501da42e80c04100796174201c0846006508080341041d03200402c02c003c0c87c4d0050070308098890038402c0f031000c1c00883c0c0e030345108bd01c0100401d4004003c07845500e4001303401d40355011b008008036454801603001600303441d00c00404541d800d4075581c04580424590849020056001c400f03903080614203400260b4502c5086034440040724000040b07030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 734797230 1250 734795980 734795989
    0x3050108010c18170307060e0a0c0b0c0304121b182004050904080d02030403030c0909020a1d0319060c0306150215062b0507050402040b07080d150e1501050a0206070e 73
    0x80125402c26401c0204040c50408e09440381d190050031a05500140d40219607002100d0540d4004a16200150308260078048034070303c1c9188032201980c030161a03c038140950914a60340c400034003c0d8581c51503040020244860944100c981c401161105811822001845a00030348044840440d0004481c1e00d8504060805101c0c000c1e10f40700242c00001007005040e01170300b01c054901030741c2e40d031021300b0b070758072a070b550100d02902410b4400680c0f03440f00c2019074146580c0d1814050402002d403141c500c1a4501c00c0300d1a4201e42c012200396448001e00e0b02c69a4041c4a41002002d4003829503144800901d0000c0d100d802c000125180f07924140d01080d8540c84140c1c3c010648101011078640250710b85010000c20342d03105404407a00d01c940600814681480c1c020f480c1250f107994980da04011076a0340b0480d040d00000c41200702a540c03030f90b001d0344100240ca0f00d40000c01025440c0348950401030184080ca1408640079418020b08022014040b680080d481e0f40c05803151030303c01b810b409941d0008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 734798480 1250 734797230 734797237
    0x30408031503060405061f051c06020c07060305011a030c0a0302032208071b06020a02090603010f110a030501090213051905060c031803151603180303050108010c181703 74
    0x70340c1520aa8080200f000b5000503480d0244000e02e50190000b9034600c80000d510540d07000d2260000f010445038003030305140703070030542205114083c09810001911440c83c40c090b001c1c1c0c00200069114401000468024969035069006500e071692842c40c1c03140601a6074807440318050101980000000c0380000301304000c0b100030311029170000c41009141415461500880c40503034000450243c900030300c00a100029040381d0300c54001d0012400c1e1a02001140d0000034040c5800d9500c62242c080761070668814140d0b41281080515200e5481110040031240141c01c8281403920401000c1503009916462800f155401c50340b0190980d803645941669150302d07481a9000030000c1941e002c940c4012002c3c0001010b421500c0c6250070b021b10802d5920b241071401002d4034404080411049101170040f8503041001e070038041011691405080b10310300c00b82c1c60a800003941c600040c4440c1c1020300483d00420b04030310386844c01049184d0035030a090401c0c851040001c241d0000c2e91a200e4060066 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 734799730 1250 734798480 734798521
    0xe181314070605090f0103200c0316050d02060928020d02091611190311030f2b05042d0204230f24040209030d020c131103040803 57
    0x1900d190658922020b0f000340c0295044520812020f0400c0300c0c29482403050781c2c4032000c4180c02d01106d081c02421418a41d00c200c2611006020403c10101c1d003890490110b12101e1003200200040d0362101300003410058003404e407800d21742202547d0b94824510401044c80700d950b1084010901c403252000607a8505141c03c025001610101000b44c1a00c6110154a00d00c03480e482d00c506004220075815210342c203180c00303e101d800b088945040824480e01092442001410449180c088041d1a00c050394100c0343c1f02c010040180420044045a44c5014507003081001c80e051010741000da4034074814204040785520098203070904071038030700a515061030190782c02810401c45074011860000e48140014102c0c02c0445001c0013150500c48145101c605c83c0c00f81880619401c10a1221032202007940c10030940c1c410b03000d120500141d030301413013404604c521039001403494a41c00810b02c209940000d4461100d0b500d040f0803058101c004070201d9078031640c4841d80c99034076581c010301e100d0700400e072852 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 734800980 1250 734799730 734799733
    0x50912041806120b012c0f060a03020303030406060f0b1c05040813140a0512030d0b0a05041a01082a070606080102071a060307150e03120a09060e181314 67
    0xd900d803c0c03001c2c502049040c0c072408081803601c0c40b840b0140e51000c842454a00c01080380c6c0c01c0002c1c1001c1303012090290041e4004200000243c0e0380d40020340303950404d45082e100c0c00c0d522042081124070b80d50200004280355070030641440d0141c84140c00c01d41503d103040502070b0b01d0b6800130b030800400b0800c039100500c07014a48840d007515000d4640408034814641030103030403c0c407000701e4a072a00045035003900040d14011498902c041003400c001e0a041a803840d0018008413004c115992980070301c007009919004d03404240d00307450000400108010b4090303124622a402c21100e040840341c541100313010302d45003d40d5510391528080c0018000e0398131181c4294404074541e0100110048614181900180d032009980c40e80c40030191100034900c506003203031050411410004c0d00031803048c801200700070290380700404c402440c45c0f21503001c41e0404001038590740301440345079040781c00c41160f00030503500c01d1414007030340c1401302c0480000b80c20806441c18100c0a8420801403020103045506d8480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 734802230 1250 734800980 734801009
    0x507150f020a02010c020708070e16090b0304080c0d08060105040b0f070c030f021806061902010222050112090b0f090f1207020405160f0e0d0c18050912041806 70
    0x4200a000303001d9502558014094400006008d907000624001035881580c503c1510713403100c80d060240480c103034092900b40b00c0ca01e80300084603000c1c0300c0550f110340c2c081c000e02c581c0c402c480303107078030342072440b0707d00c413141407042d080180611642d101050701d05407030100c21f641e503441c06c0803403070034900f40540740e401011074040540c04800c00004100c1002440d10035900c0007002e1400040d0780ca40b12030101c0d10070740c0041062080704d12624000d54182002e1246000042c50018542501010418844400e0300460381c1d89000300507559210140c00180c0610607001c01c031907035290742c03240200480600281e68110004000c01c00451060101c81402009001161009a4050b1007000641c008120692190b440e0000007600401281d2081c1c15421aa99600e550017898403400e8800d024600e071a1504440849403403400a01c01e10041400741601c124064003d43c2d407403414806903000141120000d0704080b294046010449041d101981c0c0c3d074a0020141e103082c541036800070300095002140400307000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 734803480 1250 734802230 734802247
    0x3180602070507050303070f02040c1223161d01090e0a0f05060105040b1c0216050a020906010507120e010314010e160206070e010c0f0f080315100507150f02 69
    0x50340100121445541954412503076903003015168066030f60090119225058020014a490b500101506a55091260034116030200e00710407640c24005041c04180c045042c01a00c0504850b002c1e0310803110442960982583c0e04010034031940c2038612511800e00c41e001c8107039603003d080450080c2c084410b4200311340c81e0002ca0710000c2d01c1c908400400713107403802c0c0114007503501c06c008032000d458415604524041d4081c201d804c6c4040b003584000b40c8640d083c0308403d03000440c0705803001c0c1c26019500502c0d1511140c010048040e02c0940114148402045003c0c0082c0d1030408480c2c8901d02800c0815140c801200140c1c007030108001407241441002c400417515200200c2c641d800f4420b111220b10008918444c244c0e07a90405859001c0401d2908000144030340c420100c02400754450144114841e820b40c1e910100403080301012590044088100940340d0003030714844050080803907400035907e11032a00034280f84180d01018050149140380f00890400b560020b007000d140e820011996078040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 734804730 1250 734803480 734803493
    0x1e09061c02040b0c0a0618020105071506180c0206060a03020a1710050a09050c0a0f150309020315190912080405160f0503010e1b0111100903090f12050607050a0318 72
    0xe17000c42d55a8030300a00c89801c1040801704045165040c0c580a2400d0540d40f00c00b0101a4070704513540f45540c0320389010602082900100c4101c02000001081219070804003030b080000050905004540c041810005a510b1140400860310088550000c006951601c181000710701389405c03003950304000511080d0034940d800881c1c003034016409c0c1c601c0465840c080003036420243c4103a492146a002092001c6030f0031540d152403800c0b09050001c1c5600f91940880d00b00038032800d4082c0124440010840c20855034900d0680c0702101e480104144405991401c44c80d54003403503800e0400030400300260030410204550044900800c01c654911965100c1d420408481801214001d500703040d80280d10400000b081e141c503061512019810294503801103034003222400840350b15128045510018001c503100f0013404501a42c0d944030041c0c10680042c03e22802c42d8031000c449620900c0c0c1101260000c0b80454101c001841c0469a8228401d0304a000d0b00c80480529484140000c640c0c0c1006138 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 734805980 1250 734804730 734804743
    0x20d0b0c0d0612051e071a0405090711030313060e1e0d03090209130305040b0a0504051801050102103b0118050a080d02040e0108031e09061c02040b0c 66
    0x145403802d1001648601c62454180c0b10014010516882181d14081d442281c0d0a0701d429808021301316800745948410322107608205103600343d02c0200010f4180290b04000d451264401241e00307000c03840c014144040340d46c170b02c07000705401c52908a00000208100f11604001c0b100c07540003084540442041c2c01c0745040c03001e010740746c0c0e610340310303c1680b8422603000340100e030481a0000c00c2c44401d5500c6165005e880802680c0840801008020104022920801400d0400410380c4d0b4982c5890600040c00340001038209000c0c60031402d171004000c207a13400079441c40302c0d003800c0e400443c41d100c0301400c07080160140310401010740c00e50760380d030a0002c850380340a6400e807210b40001d10118403040000b4065403a40c1e10041d0180c2c0002c5510300100d03240000511100410000051a15965070100a4854802c0c1c00c100455040002c480e20412503011626aa070040e2806240c40d01c0408000200d6500c20b90f00423084003498400503108441d001d80c10382e4020310110b440a03550300319103c0015211034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 734807230 1250 734805980 734805997
    0x80c1c030b0316050d02060306030a020a060f180f06051c06141315150504080d11150906060d110a0f15050f07020108060d0c0e16020f0c0d020d0b0c 65
    0x2c01c0380121640360b240c0d0b0f48070f18111407001d400301010200540a200141d4802132049802d881103080c5140183c4034420359000500b055911542e202c114520b00603e400c0800850f4094445140001d01c01c9400780c4103000c04a804508040b55125141c0329011114540000a40b00c0203140010000318204070800d0303d04030101c00c4440591050b0311500c0c0e0021240034a500103005065440705000300d10416080d0404603400e03060a5060554421140d454441504880d90014044d0f100420081104100e114001c1d20b429100302c01d28035082d9881c030b607180380080100d84609c0c0040002400c3c0304121100303444001002d48640182511100c072407695072650b200f0341d4006910007070540403181c45601500c904404130348540f03141030000e4004484903103018008a9101c0240780b002000130b002c03d48030304020301d5440a4000c2500d044a0600100070544c1c0c03481080d0b4100010704c80e910700000c2076806880c0c40c100c4e81d13000c0030300766400422a50301d11a00000c010410340c2052100380f00346170002d0321030354 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 734808480 1250 734807230 734807233
    0xc270f01051201020408061b04090e100e03070b041511031005180f060103090809030f0a02040507030b0303040312050912071404090f020904031103071103010501120f080c1c030b03 79
    0xb07080350310005080f441303180701c2d042884c0c02482c0030845490401c244d8584c030742c550780c142d241030a481da0150421201d603001251050381c040c06e0048583c00d41d500844100514203800f541c1080035513250080c0078200100f00802071541e00f110042800600d901c15020415001d0401e5103d240c092036800b040c80d442c2c06200e01c1507442001344010000c45500303d03407203080f10b40c5600c0026115000150090013090300220781040062010b10496102084410003002551004100d01c402e240140000c5642c003a1002c1c0c101410708622241d185c03000802c54040302e6029603200d0307001050780b41c11100f600403c150310380d01500c18a0610510080065608140c0d680303024402d049520301d40c02c0008035282000010a03800c62170b0204005032906900b071543c0180241032668a011a180701d03113055601c0b005013102c3c4000e685030720320000d00b4244176180c054003612548107c2c0364040e0b04c2d0380d19110030441000344000d0300018141a510001e2200f14540840c01109000c100300d9103002038050030b85111a24000d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 734809730 1250 734808480 734808499
    0x80c041d030a0e0f09091507031107030314151c020607050a0b010806010803130b090d020402030106050d060f060519030b060406110c01080613020706090f0f15020a020c270f0105 78
    0x258074181c2c8071140100c950340c0041501202d0303903c2c040c04c41c00f0004c010302c0270300d40e855103648554810310700200a0284650b5001a180045659000400001170b20403d03030145510211641c0d40c94008a11400400d05c40316484050568400200c0d00d2003811002801401015640d004010b00c03451981d06a071552400e0743c40aa1300c481c140c590340d010300c01060542c80d02600782040841080c00c014205140080c044807072030b098603004202a6442a405100001c00c0000c0c00803d0003101d1281e00050110505280f444915001c4020803502490130540d40303800c440d544440d07940d40039030312403005554060410784e21581e0380c0d00081e0500c4d1241701190f689006401160000b98071032007000e03210340401003100704030381c1084281d0b100a402c5090119039543d0303680034040204803469404890203100d02039500d480c601c0d0745000c031000380262445101660049c07000c09045500415400b010a8083d1011f024122014031802280741400b284a8041c2e0b0190b824001e00c4401707681034074140c030720603110901c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 734810980 1250 734809730 734809759
    0x4230a0b041e02120f040c0506092403090d0503011208092214090105060d1202030409090c03030215130602211303031a0a180b12030d0b0a080c041d030a0e 68
    0x8017410126001015071001c1a010300c11841c2481c081c060b80980907202c00d00b00c3d01c1e0504000089801c07688a150540b10100400910000c200400403075140e5618000b81554500704183e2071801c0c0110008001031400304404002e40c4844002c54030817010960591014074910010300000c0011384009a00d0004000c0007554480d014000e540c080e4070050000c0e2110160740d101d500008150010560441c00100000580b0b5082c6003e01812030307000c0e603080c0c24064554a0044e2800c0e4030108001c50038003960007048603080706031700c0b40038074180c000c03601580c1c0d281c0d0740081c29140c0e04003440d90a08200e005003071009048030541003505051098030708010003220a04040c2c440408280c20b690301414001050191a4135608500c400c2c1140d20008903590201d00c000500d000c01e00105140380e40d1010032a00026070141c01048120042929011546820000ca403500d950080156030700a81c0c8401001d500c51100c50701c0300c540703441041c05484e01d8200b00003000b4180c0605007106407282d02c02003440304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 734812230 1250 734810980 734811001
    0x1150314010b031305071d0f07020d09061407020a12050106270b030c031f0606050f091e120304030639140307080604230a0b041e0212 59
    0x41c160360380308601d43e003559a5401041d10448002d481160140207401c0300003840c4855030441441d0408144820080d40307044036880030b200c00b004050404660045c0320700410b0b0390300112820103480742841c014800c00480804610390340b20b2110000d400070070400300010403000f03001c120341603240329400900c115070307850158044104400c0c02e01f02c11800c0c116070a440c05003040d8840c45030b04902800360350101d0314010020381418001d6601340071118001500001e02d078640c4c4940070280c01740303003842805c3c440b0300700c0c0f43c803064011060580c1c0286c0c0201c405411550100490300c074144801484c4400c452071041e100b40e00d07908a44012a185414054500d0400c0820042c0b4414940040c2ca4101388210b081d00b1139402520b18400c80c000d001110300ca0743c07450800d00005501c00c0e0b685031102c0510b401c141c07003030108607159030f008004c490038010804141100080c0d01d40d50400180d02000c280000d0745400200108080d03400103100d044101102c007401610f540140810a542c284605074940d5070350300300c0c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 734813480 1250 734812230 734812271
    0x608010c09060f260a0203040507061404090504240e0c0f1c080f03040b0709061b08030709080712020120151801050f1501180e070c0b011503 62
    0x80114038a9050f840042d480740e03482c0c0f05070000e4051004618407000c1d40304072030590159100e002d000d0b0000104400c0c0001008044000c107014640750380307440c80c2540c081c6414002c9004407960fa9842e02d0100b42481120001200310384001c100c07a000403039078601c1880050888581c208540d0281c8050451f9520303200d020742040440c0588910042107000700da24002c126a16001c42d01204248041d402003000302c8069032103107104101d48030940c1030554018024001c076501400809c45940c442c881e07031105501080502030350103805c0c3c03522a11100c0d41034450f22201c0c0c206420600c074450000886555a000b480c90003030003030302e0b402006c00030010903020301d846600a10401e036101c060307030107125402e500c11035034021400070443c0325820811041030b080d030304241c612201050000d02403101c0e402c01490044200d0000342040c60740d001d110b00680d081c0646510510080000180c0010446801140c0b40d0401d10780c001002e42e040d6850304100d0740c0c001c841340510000240350407081401d004034120b41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 734814730 1250 734813480 734813489
    0x812030a140f042013021b0a0303090203010f060b070b04020406050612010e07050403020d0b0a0f09140c030c0d02041a041b081b0415200a02041103011d04061e0608010c09 75
    0x41c022001d05e41101c040a0762007040388803a184007842c0d048181013000d025002000d442907901041d1400240101425101000401c08405141c840b0401ca4503501004860032554420044041e60351140005402403800b540100d81050000842c4929003182d261168180c41c071035607414406840d40f500486190055010080d0004c40070843d00d0040344100030b10982c0214001d00c0030410007140384061342039611981045032032105000303945682102c1400040300c03418040d0010801d4449902c0000d54040300410040e01940c0d941a01c3c00050f80194034000c001400508203025103e0000032210081c00c04014020010317107043d02084c0b051940d0b058030f54091055000003070400d8140404042d45c401c41d144480b06000000080210242c085140090400b5104010b0100344640c0d00511080d125688500302103100c04200600010700701d040c40920820151550b003049a40324034100d0002c100208100c078030301c1807801c0302a09443d0260000302c1500e40d081c000b480200c90303054060780c104503140034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 734815980 1250 734814730 734814739
    0x4140d021e0a050c1210020a171302090a0f1d060f07020703081b011b0302040f24110307051009140a150e0109020603090109060e070812030a140f0420 66
    0x180b013a21458044462102c1c40030540c1038803012002d84088100300c2e1b00052180011030303442d041d1250f014900340380155120700200c9203140c0f5902e196000403000c0b00000c1c15400c0c0c1e91354407500c0380c103044c0c1240c0c050050301009480000c41003114440fa6651503404582c074940040d02c04000170b0603070388041001400c683e40481e01e1030603d4001c0c00d81e00000058120400546e42d40d40c000c407500010303005080032106006440060307645007002c00036501e02255801214038202001c81d0f006440705100c070b40112010044c64405400751140412500314860190050898400c00d00d20f1001101035a10040c0c44034810100c0105200c098480346403551030000c0c019112800e01070b140506d80e1b44a40104800c09203d600000340218143e0001d080c41d002600c102c4100da41d03400000b420460380e44580c01c10551504010702c82030b4500707192259102040e5602c103032010404004560322084076000020504180c1c0528000d43c9041e03040144645c0b0304407825152100140e52002000f00c1204140030702207000340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 734817230 1250 734815980 734815993
    0x127030b04061d03030a02180d0c0306061202150c0717070f052b02150a09090606090506071205130b190302040f05010810030b190e011a040504140d021e0a05 69
    0x6d202c10025085442000c000007481c618a4000b507803120002020a4491159418001d081d8285201100c02d590004491140ca101101e4003503516950402c603919880c41c2c06581e120420000f003820096107500254040202007880032111030003144900c1078a01c00d84a40fa401c1d65200c040141c07010403140d01e84031005103044179213004819081810b0740f01e030014002d00c0d032601050415058030780c00058088001803402006020484584c002c1c80000e001901d4007400c10750500d00000c0c014031551800400b004044c01076464614051b6050352820320595292441e0169110883d01080d40b0103030310005c191146c41c1c81ca039011406072095a0581e11307540c144988203421f00c40191981e60002d416201c803e4044800000020685910113204440140b0341d801412020001c1405942c1d1501e0b8180050b41400c1c0458407485210103050b000d07034801c0318040392507111401c014210314420002c0d0001802110180101032b600050b100000d80c1d0182c04183d805400c010100b43c0707410703480e403001345181c0248 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 734818480 1250 734817230 734817241
    0x141606022b0c0807020d08160606080f060c0d110712031419230403181712090409060606020303010501170c030103060903180e07080c03090a020127030b04061d0303 72
    0x100c3c00b038001c080c80603010800040c00c0d91103620058218110f25481408511001c004004050180700e00414604004010a03102184191b4481800900c0c0f07103030000010414040c100e825412100b820041c50110a58890301400d0003146001a58100c601290801141c81101400860340318800e4001c40c0c0369013400c0f01800340000c064604504081c5800050b0205d10001e50600d03805680901c1c03198032807990f1100f264140440c0ba0175168031907181c1404113808118015008218121400c06041c091690740c840c480000d0004d203071800000d80130703504d0300c0d00c0800d4240d000401075040c1d91003601d41d0144d1040700564001c14410072604110f244409000400000300140c21080c0007510078109280040071440068110307103207940c481345858a0708403d00c050700ea0051072440e080880310f400245580380c041e808036076403103070341c20000e0401041018500320000e00701d03c04110000c207142184030503992420050b0310b141302510140d449500d041c505400740d0594207004980c4043d41400b6609590301c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 734819730 1250 734818480 734818493
    0x305060306103b07030c080c04060305040f12080603010e0f031806040513050402011209031e05040f06030f0e030a090e040206041805091509030403141606022b0c 71
    0x11440e01c00f00380b420340040403502140580040b18000c02c0003441c0d482ca803a080300c0040c150f0b19190549802e101c541c0050184001a1004903825a8050306001c204d585441c6000b03503000306000d0010303242e5a0403180c1e502c2a00e41c41440207003d06400c4000788403001c0d681c0d504c1601d8525400900b00560300401607102112641c4c115030792000c00041066003003564030004103d10400d0515a0b045c3c6982e00c80c00c0104660700700c4480603070303840b4405003006820810303a0060302d0f1082a5800c103030518100452075020500c180210340c05844045142401e1a80d10000038015000140e1848412820b0510206020b90008103a8199440c0390b5544808645018000700c82d003040a40107903001001003201044a20f10b01400b0000c05001900019480c900743c0758450603d150000741081c01e407000e00034081013413000425942078030b80040c1c00d0100c3d030312825480d17481c04445507203904c007421251000150f11764010031004528440766205817614150080c40601c4051000301c174001013183c00c03980b00003203000c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 734820980 1250 734819730 734819759
    0x3030412061d0106030305072d030c021302041d0a0c080c0318010213180905060106050c0c151c020313031103070f0b0612030c03090603100f08030a030506030610 71
    0xc405044880c00b540301142c542c2580c0e040c0d00241c011403000a002020425030090291411210305d140f08450a00307041d400950720020b0030060b003008401040341c41136586551400d003a9030a445002c65495503141c0034950740108460100000b81c80c840c002903803450300d5026090445440ea65a04425651280110403640019203005043d8980d203101100002003403008000e60b425544210040354036100110a04245a02422208904003003072080001d071700060250558000b41440c540340d00a1406841c542030b13041014542c0007180583d0801e00485d258010014460511000075510910561140507807000747c487c0e00e0701c04080c04080700401c2c80342e22804040000d80c0c007940c4c0780102544440030441e040c55425250603c1c5030341400207620301a1102caa03ca543c000166080142c1410003d840f406a0b01c043d80c0211400000110880040300592001d0a01d580d0b40203002c5440380780441d602e0700305c5640c8802207454040030902910700025001c1c451104010700422040c1090500c144400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 734822230 1250 734820980 734821001
    0x12090f01060e0906040b10080f1c020d080f1b070c051008160c0303110a0806010f0906120e0102090358140a1206121e0807121701050303041206 63
    0x194910004148408140181c61940489c00002c0409440032044440c00454801286065602544080380341c6500145110ba11001c8203400400903900c3e110382400d0304a04503012581113000180c2d02040122021085081c1d95003903402d1b9101d6008080f082d95080741c20340340140344c126222901c10b4114841c10103491018800e24020580e03c1d804660110560000c0c0344070004110004100601540d010b5001e01d8119940d29095403107924280c0098880102544000c1810b901c4451644000301d0940441340c0c6080d000c0e08482c85d50395851a6440c42105401c0903018074100480410f91001c003607000700702381e20f0f0302c1580190207200c5007100d442c0b000004500038090020a1014480805031040900f00107203450711400d0180c440c1c2c2c403025003201d6103a00711901c8003203001c0200000c149200030440c0814802c281d510300e6691507081075541806001001040801e014407151181075001e41c03a400c8902e0400c0503000e5a980f2241010741740d005a00815035110001d030f40d1600414601e0b0400816003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 734823480 1250 734822230 734822251
    0x10e04030201110a0225181d060f101406030c1303020a0b0c011521060b060708120601030506010203180d020a30020d0303050c12090f01060e0906040b 66
    0xf05108503000c0c001d504962501e01c05130300400310319031854440410841c408001820720090031810a08050190011000c800d40001d40e640311112510111a0400107445002c01c01ca4880f8646411800c1c14900d085900b0106000c15040002d2055281d0f504a00d12180c018191402c5907100f40500c920380d005070700c241440c003122143c00000b507143d0fa910500900480490345913100700392036403203003520002c841c0c18101804403031040040b10210b00481c091070521100074180010701c0d041c4400545000c51030706178090b0300022200100080140144106012a4103041c581c0e9a080019811074a00300d81d500d015800c20044107201c4094100c20040e1458010b100c0300080030150046010000d5a411a981d56050061301032a11801c50f280315051480016104d81048440c0d0b0100d0003145018030b0050a05442c1c0d0046191241c285060780e14603203000c100760210b40307884a1925074a1201000c078007041d5181000200b00e00350004100d0b849032a10500504a94603140e03241081d030f100090890101 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 734824730 1250 734823480 734823491
    0x509010c020a0602010501090c02030301140904052e0f0c090b0c160311040501121a2502010b09010603291503040c090c050309100c0e060705030d14010509010e04030201 74
    0x1030b500e00d845000902566800092a90f041a01c000c00b104c441d44c12910030355005100400003c4107217141c500e0781d4002610b0840d0b5903140da2a1680c5070800504007400c1100382418040004010b0103030001d02946960b070f013484010250f8503800d044504040000c1c00144505c8428080c0340744450082400c0384842c821280101061500300e194404160000c0307584504c42e1003441e00c1d03850203010702809064510011845d01a06944180840e144240d0b07221000c0d10082c0052075041c8060800100d140c0003d40c0450544440c900003030080c018142000e1194002c1d500120b030071442440349a00e07800c0c040d01009d020780088a42e0503d040c10b68408250f02490b0301c00441381901d0054003440c0560b116210401c01035003000b5440301134601c002200410060284104500310200041042d032050312550000b9540c0c01440c0d04031a003038030201d580b03a0040c600203020010064000700070510030500e00000c00841080d20714441c0c12580070703c00e00740d0004100d40140a1200c0c1c444c4074a4101d842130000141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 734825980 1250 734824730 734824733
    0x4050114010c03120f0605040b09010e01060309080d061206060b030603070b09030703020d0b0a05060d0201081f0f0b0703110c0a0e0709090501090605010e030a0b01170328111c0509010c 81
    0x517900981103185065031190b01c200418181400342a407040d0702141d4410466041c1000d040c003040b0148103034000c150725040d48406100442040b034182031703503031901401415150341480c0d41920400d54201c421524042d40003904035420010b9038001c00005001c0d01c505ea10784129610745400002600b5450b00030b2807000001030f45e5005e60b40d0001441580021140c0c54400005012920b0081c080d9008840d0501d40c0e400507a0300c08043c560021007015110105154007440c050460841d401083d0800312500c0c01003122003603040079001485c031035500c1c510801000080342d038440c140803c20540160542c03030180000c103004450340e580144240382c2049596980c9080c0015100d0070780c0030410080c4c0c0c0f20380034401c55a0111602004282c107800a05104480d6510104240c005104006103152030040741c0c515807500340103c48903085d41c140b080a01400b600c0040c880e1480b0320a50001084901142000c03c0030045103c0c814244580e809204201c5010f0050b20160301c013091050410900541000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 734827230 1250 734825980 734826017
    0xf02030f0408011e0c050906030405011404051b1507022e030207060b040b1f141201170d050d0c051c05040318080606040b010201090203150403020c04050114010c03 72
    0x100801c024000403e02d081c1e8001e04d60080401c4015034483c15052030003c14141350803c0c11140300080030303540d85d9520399960a01038018001c41283d1f4000281d00350901081c804000395881c2c41411541c5202d041400b1402084900c40015a100303e040009205010141c90311a450403400641002143c06014511040781a41401c0030b1309800403c0d030105107001400700a00c105aa03042c0305880c10000c5003060350000d031000c1e0b41e92986454041d00540f08044003441401c807015006019080d041d01c500a00b1200c54800009000b110780c0b060b14100850142e1100083e0051700000588590f440c0c9001742c50100082c09031a006102440010450441d0300c886028404001c15101c3d20005510700b45480c008150080e50b00e0300c000040c101c3d42c4140601725002c80c0d0b4540040084600181d040e0368000181d0141c0045c0130043e6040c0a10074190300c074840683d5502d40308612076401d1300d002e5440b220410045460a02810010003c0706500000550040010300c0b4094002e0800302070300c1d040c410100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 734828480 1250 734827230 734827237
    0xb160b0a090f0c0e36030d0f0b040b04050103080d02090307120b090609010618051b0c1c0216092307020114090109080a08070309080d090b1e070f02030f 67
    0x1100c003c60070b110204051640e11040319003100c05c1a4244400c1800030f8100c6401c0e0260300808080d69010500c18918400d081085440c007160f000c805004141008080030020700c2511301960245003480019400c918103440390761305807644144130600306450030390070100a4102c3d140c156058031420a0116104040510807007080d4801e0b0500c0909107002c03071040d070611601420425043c1e0600c8414807a003910703d48000da01110340f03800080c25a8a60b082d1b140c01e40043e1901043e44640040d58000d07030030000ca00810442030310034009003130f51a002400c90b600c415a00d0b00c840c07030218510f024040d90810b07801c030144a002c161100c00290500780302203403141da0700759070020150f9941c00540023180c01840503240d0041508008028803040394454105600c83c06041d20108110134000400c65030181e404140307070342e0b0030568440d00c2d075001032030b041d0080c030306a84156030f0b01e42c503500010549030030794207078152068000301000c5190701c03200426146042d01c10301260a41c0802c2c0051080000000040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 734829730 1250 734828480 734828483
    0x100b1206073e010b040510151b050c1005040f0308030402031c11010c14070b0702071205100f05090a060b010201180b04020f060310060f1106100f0b160b0a090f 70
    0x11181d4201c0c8042d505003110701c00d2814070f0080342010b08000c075885508010608980b511100340c2612031810300105c1e101c203c0040700501014200c0d00e140240400000d00c189607030410f0b904c00340116181d403070a84042c010741c8500100100b0020040c0000340f001400355400c14409400c407051482180d0032009110f03540003403080081c030001e103002054202400b4078900d4a515080803407040d40400c0c1090000d1050010107442c44814a0104103242c1c03017088101c4c014000304a040f460105545403040e100c05041d040b80d59014185070700804250140d2151601441841d40146202e00c80c0c1d6031068050300300806000e056550310f02003400c010101c03102c0b50403a80c0c482c40c0000c0b500d01e4188104009113031400301071402a0b50030310170401011404403800c002e82da03c6091000d26640d0017541107500a2003006190500d01404041c00041b000b8088041d0607240c65684207a5815220078800c0d121b03020350040c1405003a408018a40402d40b010340c038503041500300102013401c00c0c454480f022002e080400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 734830980 1250 734829730 734829827
    0x4090b041406060105210907050a030308011a0a050912010b060c0c12010c0c1e020a03050616050c030d0f0605040203040305030403022b0e0a17100b120607 68
    0x24040c0140420300c0b007141c1c0080c2c2400e00d1070420308410880e415101c81d84003601ca074030050f136001c100c00c01410407150700100300040000b040a0f03120300c0d000305540800e1254030a600700031148080444400d000f60703881c1c165140c1e51a428040c20108010707200403401c80d048201d560781c1030b0790009521040010124020400d00824000c0090814440c142c078401d0500034281c5d1425500c5010b2a038040c03d50003d039a04080040d040180745002001c1c44449071000030742c81070302c3c0040001005004960303d4402c000002004640404902040d95580b003140d20300442074004000131790401d8540c0d44120319218031710714005074840d1a2004502240d00a642c01d4020030b001100704002c2627030402142001d03029a8907415940103000c0304c49414000c8080c0304206100d0407041014058407003282541c010410468010800c00d2003101891701c4103011f009800f001801d02c5003889450800000325680121100c006101c680c0d10328104580581c0c03a203015000e004410031140074240004213079a000500c0149 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 734832230 1250 734830980 734831003
    0x1203240909020a08150408070501020d0f0b01020f0a022d0a080304150912140a0c0303030b0f1905060333011b0209041209031b03020102070e0112020f04090b04 70
    0x10000c04880c903504c1080990311909040c080701c0c903a808004d030010f91200f0b090b9200d44007890907070701901402c860311103500e281c5100340c900f50080307401a42042c403007a000d42d10128200545581c40700001100a90004c0d0028145ca205042d1003442c0300a00c407565114000380e858080024a40e080e00d503010a41680c404601440442008914081e541c112410551807892412040300d05412089102a0200301c54180104079648180000410607510035a00c1d000e1948a00d0b019000700f1a04203410f0181c0b5400c0001c0d01907041c13102044001030503010f140d140c111710300820803200741e0000700b02c0b081c2c8007110880801c100e680d615030250f60022005145032201841e0000400c25151500e5140d42c80380d58081c0d840c09600c400c0009504103802c5900581d10f85521034003560310081990004045410b450030003058003000032030110989100341e0950781040da8512840c4001c000a0150140d0200b480201500526085400d0300394240090808520b5800c6911807408200c811981640c4411049 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 734833480 1250 734832230 734832233
    0x170307260f01050a0602120d1e0f0506010e0a030f0f1205091507020913080405120f0c04020322020103111b07170316050a0501090f12020a1203240909 66
    0x740240c0d80503280c203444070700c2c40d00c0c40e00d90001d41d50356444d0080030060380005208032000010350000c04682e820003901502c05420020302400800203210003010380ca00d800086003d5621429600041510040040060508603251045140000c190450701002c510f1403000029114101240c41420107464450f1165018000d001104002a56240380700304100401d000507500e4899181d080b105d900c0c1c9000b08113020385080010785c0319a4101c141d10880550340721015a9000403030b07021a030200000c1e110015644400d010907800169507603070080140c451464020510310004025035801403501054000440080c0d05c4107900844117429440c09454a102074403008201d2003005206801e4131400d03183c41c00c01130076113a000e008042c0d0030003a040094841032003002c0245418068000c0020000500d080c50405164032003507000703c0c0d44940912400c3c030b240f4004119080c90a4112141c0213903d40251000c6000b0281094518035103a054440c4124040508200c01d028043ca80c1000520011a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 734834730 1250 734833480 734833501
    0x301140705072a0311030a020a090b030118050705150d060609170a0c0b1803070608040212030301050603010e070c060e211810110a080414010201050417030726 70
    0x1901d048100c019400c2600500d0b040d0300d903c01904032a0404c0001c88140d030480002420200c010801035808101d56202090300d03107007503100a1403e0b0081f00208690030807205c42c1140703481307010b40180003900f11000070031103030900800b20194660074040140c03402c10303d125000101c07030b201d03004100051510352003804001070f00d80d40c82043c0050b0030300500d2000110354500384580814001c8166000d00070480d0040b09084640c01d01956400070107950b50030362030341c0d00204402001c6800340c1c4038200d0f13a03000c0c002821000c01128140c650242a051460b82807150076001c01001170710f00713010031403030800d0000414500d00c1100c404200300b00180c010000c08581c0342140d0454400e182518500401c4226911503425218030f2112200780c40e403240134100203c0586164064920300070882c042c030811783c420001c080c402001a074a515104242d14011040124200e400c104d8004141b0007480310340004842149002d160700c2100ba251015892510380b800380011a0415040001200404180204484d1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 734835980 1250 734834730 734834753
    0xc1a010b09010f082406040b030108010f060b0c0615010c0204050424270f080c01050109060e011202010e190602061501080402010206131b03030507050c04061d06030114070507 77
    0x5141800f111700300019a40030300c2c402103144100701721504100c4110707a2a20025a0001d0400000c19500c030b6a4039005140079044175221210103900d08100481c3d0309480303409440610720400b00a2006070380c0c8000c4408154100e40500d4188001180b8550059489004052041d40718103940e8031540c14000500311005104100051464204101d02c1082d000d01c403802c01c221030008038002c10001460818401041c0c002c2c02c05803402c100000c008241d10300541000303040318041d4004201c501d5441c810490641c03028000e0ba402111020005c001540c440c0030f00482012000300b514a10300d01c450220941040254840d60160704401c0402460ba071034151865030052003820442811714055000035258000102546402d80c11300c6030f07020601c031003020841b40c54007501d2a4690141d8903400e01500030341101e0300031105807090759074002083c00c2c01d024480440d0300c000054286490103034000d0300e040c0401840243c043d0b50b10036024040c2102d9841a82c0a00300743c5c0c40b442e0f912911800c00614000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 734837230 1250 734835980 734836007
    0xc03030e010e1212031f0e01030b06061201050d031404180e030310180e010c090e07021204050409020616060b090705190c02040b03060a1e0911010c1a010b0901 70
    0x5844862400c0f501c000704405070001c140030000c0c4d82e07030364650a40c0000303001c0f04000700030b542440c100c0104000f1140e214442c1684c0c0204003074159a52694100910ba00c01c11070301140004c00500104210b080611036420b0300c1e0700c03074200800e40707041c02c4100b003005400951014016081d0201c040400401e10700c80c100e05142d0020183d4690300c0d159500112000c4a4490f03408443c009058040060701e00307038802e80c070382c0c0c194078000e110105c1c00d4030000708413108500803520328520b004086800d5500008a508200c80200c050606003031900e01000001d110000060380c1100b003c008031003008010111101106115040019030f0f00f45503c1071214204000740560180202084520003014600c5510500b40b1001e1401104041a900c04034020f8165803059a03007600c20031043c0107100c0b000e50000c175035507045410b5100040b00c103103800030159504040081c028220b030502101d0700354411076400300700e0f40c0a001100008408010840714102c000d81c80151100d00200e03d0314078640e441807000d1f2002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 734838480 1250 734837230 734837239
    0x101a0d0b0a0b0a03080a0842030a051b0117090a050c22270605060102060714034201020111040e1303110f0f010e030a0f050a05070c03030e010e 63
    0x15411340d075544c00a8400d2840324400d0021a80010b41c0000c05441c60300a800f00c10480e61070008481e5840411a200894101c000c1d41d400050204a40c00c0000d0790700d1442d60080700030400340443d108041070b20314812007114100801c3c840c0740584260a42e100c0c9000c0d400c0c0d100200921140c030700b0024100020201046d1081d400c1e8a02e1030340705210f1042c0008241411000051180034400c0c8809403031780a00040c0d500104681d0740d00f0107001c00c80c0d0105100351800e8003a00e00b140c0d60311400b261180400030180110400a0010401c2060010f100031004902e141d111140d240c01401c03445052840c52401104130029905a2049543d0a0080c92032000c007000d05281030a00300000032004550013807194000c0006c800b041014144100d2560695400540a464003c1051180240c076142d01c0003009541d5804c111054164210003c100c0f88c407021280c0c0c45102c1600a40d0080301c1951200040d9010840d0900c507490214001031340300402184603864404001444000140c174810200da1b030750b84038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 734839730 1250 734838480 734838499
    0xa030507050a270b01030915050403080108190303020c0c09010b0c0f06010e3709052a010507030c021507110901150e01091205010e1b03101a0d0b0a0b 66
    0x509a02c1c3c5a1001081c0d220b040104551056031300413002449481c0010705007025402c0c2d01501e03003186503c801c0c02140640c0d03c18805a88030304082d030b5141d80030001085800d41000d00c050100344280d015104292040b815982881940e01c0040c1e1280e20a0b00b04210502000841c1e500b02c280800c0720101c15901c40000e041590314120134101240c00043c10b480c5e5852441c00e1000c20880c0807008034407290001749061240a0404004500400280c0c0302142c581c0301b85a01410904407800c00c4045800700c61040010b1880340ea001160b860300540340480c00d0040704090000140e45100e03210009d81c118604c0b1a03150480e5090401503000d1541d18207000c0d00d003600046c0030402809981020520b1039082030340d00054541c2c0101c90441c00c07a4003070704940580e0030102042083c19000303440401500c40c11564804060b0ba5008070403c281c1c590301d075056014141c02c00070210300743c004291014010224460070038041700854480320f001e4104407041490311040001c1d0320100d201d0500d40c0c42007038070800c41 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 734840980 1250 734839730 734839769
    0x30109020c0f0a021c080d0501060f0e010e060304030e13020c01140a09030c02010f020c0301110705121206040b01030f0c02010e0f0a17130f03060b0a0b120a0506040b0a030507050a 79
    0x100c03048240d01c645c0300441d01c42c0c1884180700d12642240c0c1410600340c410801913a44450051030007d000014000050a132503040c00550f04c5003000461428004000c0c61440d141c0c0d903000c0e1009a600070307417160481c81d99480445081d1051020b4000742c2c00304400404c021000e007504d43d100c4040141000341007403400c00240d0100c0d9028030300510144e820708001941e00814007059107400e07000401c00e0751560801c14454403c03155040504941407003001128050000c9040c0050300d8056548060880c1540e00300203070703181c0b82c1034100d042400d8041c100016002001811300040d100d0b108022409070303464a40c070114102c01044035190b119540ca01509002039566100103001c00f4410010301a0a008185110300d00c419180079400be00180c0c20320700c111603603490b0010103031038218122403107041044170020700e84001d64219a90308600369003c407901d0381c3c0d00c0c01020042c0809080c0030b8009603598243c0b10300e0b4580d80441e80180d40540c00428110345840d0030000742200e507400a00c1900c0040d0520324 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 734842230 1250 734840980 734840989
    0x703023319030b03011b0c14010c023012090c010e1323040f060b04090f1b03140f120a020a02240403060203060102060604140c090109080102030109020c0f0a02 70
    0x1c86500280c074000c104865035400003405450640e2950800d03030702442c1a0040c040d08880d20040d0b0500c2401303902d107168075502007107003250022250342e400350700b244200081c0f034803a22200c1c485d68403041c81c1204200c40741c01d2048905801400300212440510302c05e1201d49d0303030104602e01d07c220007403030030074405209200415001c1020082d0b001c0070544880400309038916402040176074004041078a0124a001c1c141b2005200715600d00b6603401d880d01140c0c100c0307810903000da503144079004110040e01c1259076481220340300d50b14000d12021010554040002092220008850800b40c0d0080c042040f8039034210303003455440d03003603c02c202c5400c001804403903030041101ea5006404941034503902d080701600c0d00c0102800c0042d58030301d4000040110401c0391590141d40202001e07030071140155101014001126109035225400045c1240011942000c2c08004c044802040c0341c064400ca5441c24034509a03042a040310707a1301600481d038080028070401c18102c0b483c1e6404001c0000013202e80124 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 734843480 1250 734842230 734842267
    0xc03120c02030f070507030209070e0901080c09011205101e2f09150c010504230a080f090a09090b130809090c0c0d0305070e010207060e04050907030233 67
    0x103c140400c04621403040c08800e0000100854020b402c504181c9450a40142042018495148502078010010402c50400102c820688501520082c040d90034694030b204500c459000803590386c8074044c020b81c089082805210410761305c021a10080030f50200520302038a00122100f5880b0305201d42820002002e040b10a10580304000710396600c00801000c601800750590000c195507000240090b070000d015840244602d004600303180f0702e000b404442c2c0e68400b483c204c03a0040395010b0001d01002ca606000100702c40c0031170a40340c6140c5030b100d001160003400c1c3d6510401c450350b40ca511842c00d00c001b0051803588141d1418060310307988016030300c507185401400c40c2c1c0390160030f0100001e414282004e041328003600c0407008642c80504e19010040281104a40103070020b0040700040c07045500028400c016100319480d8009505140701c140300007001c0003803e1425901c2001e81c000056241c00d07500e090845400c8842024601c0465070881e0002c07008983c0e501001c0d4204403041c9112030740b0061 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 734844730 1250 734843480 734843497
    0x9020901030912050918040305090405090f070806090c03010608031801030f06080c010f0813020d0c240f18140a09020c01090303240302101e0c03120c0203 68
    0x1629408594012801840b58020080c50400806048001c842e000005411000d4040310040401420380c14482d048060070340c1c0c0100030401c180003c0344245000c1c2c1019134004503100444103500c400650305450040031754410010364008005020710b10005010181d40c40d40709a0092100a150151290352403040190f01061820610b1030382415030b201e40c1260441c500e860304140105501c2d56045030310750180c44113450110341c4031071500b1500d0b80035288092142d46190f011800000346c940a2120710030b154201200c40c400c2c0c8840100b0303c10b01000c07064007112640d8404d035003910441e41021f4005e101d80d01558091060f603803c68103260f01244009801e40e645035500d120040700d2080821083c0c01d5a07000500b9a900102c0e00c0e00b2000c074154040e400240c01303030354140f00800c01c1d05086102d408011880403012808a2410b20260408020801c2014107501d4400c4821540705041c3c21441d518039441f0300010a9401a1402e2617401800c40288014114080040c40100b41000e50340c0d00c1003541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 734845980 1250 734844730 734844749
    0x5030d0e010c1a190b04290a090e060405060711100b01121a01020c18040f0807060c0804020f040e1b0a080a12030501081227030f0c0406060e060301 65
    0xc40c48200003401c051140244440c0c0300300c6105040404c13420030701800604d10703e808940f420b4256005803800340190700300c01c0604800148a18140e031210031081c41c10000458000300c80d003400103991250303407045504106100000d410309041501d002410640f002d0729080401500b4041d050b98003a011400b400d0701c288103400020032144810042e550b20200452204085180017040c4107240e020196002c0007007801d9017686c24442c01c000800c50b65945e03010f00130403c0302813a800540094503260341c080b2a1400790008500342006944d401094503152904900090000d1040c001141400303c00000c610340c0840e010711241003400480ba99071690440311b410110701001c4014002d445c0c00358110003070708400e015112990f62074207048424002c0340f40384000081c5000300000300144040f900f2000c0c0b030500d182c0d05107800180172508001c52500d4541e200040c4030944120500e82e0200b18013018810f62602410581e104901040211052a031140c8244080c2c800740b46031a603585421a03054a40100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 734847230 1250 734845980 734845997
    0x601050901030e0316030207051002100c05130801091a040807200a0f0509160203070303020a0e0604090902040c020303162d201903050705010e070603020901020705030d0e01 76
    0x40b0094002103603002182d000025049011490030a140c02c6182d0098088807941e43d42d410a0004054052006c000140c111a503610041005a040a204002c40d4a041400c000840e600c0030b1000310303203501c0143c080e90341303e0014041051710f5841e03070b400002d144a216030030b15181d218040745107e4842c0003440d002800308006065490900e40c0c05a042d0003502c888030040d1030f0040a00c1d0001a4003c4500c100d84c40c0c00000d0090031035048000c210b14245d805581007880594081d80690003580d0014140301c0c48004d90500340d1111006440200303642c074400305881e4454010f00c0111107040c0b5034030301190001c008204018023403215030703440d204403450700da502c4600b9481c50744c1d80e40c100e400e842d502c0700350300c0c610322a070031070f8001c9000754000414583c0c02050340041c10f030f0f240d940389010128903000c8145042900460b001c1c20140402071b009200208009082c200041c0c1056050b400035408603501052113001c1d568108946000b51a0940040101d460040c4010301702403030020341a0304000d000c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 734848480 1250 734847230 734847247
    0x25120206040302191a07020f0a0b251a061c1112010b0307060908070b071e050a0b10060e060f04090b030a05060c03010314030a120e030702091f120b060105 68
    0x3001310000805520103804451191420719581680c4100f406902c07401c8130b40e1401e070705450078203000e80c100c0da01507178041d02e000a030310a0b021840c004010155448480c4034407101c013140c400c4103250542e4101c10b1510380a80350007401c021030600ca880b41103c200e8001c3e4034210000d2944a0400070b0040222003107021005007100b61405025100d151075014001c0240004010350012105015124514140c1e07103c81d440f06d41c1b85410340030f900005411601e01c032001547c03035007001c01210821400f48080d00c2c6808069122800b0385c8a0503100241c0c0942c10781c03401c020702640702c1c2900403404011149507141c5220081705e0910f9000e0307401750161450380c4001405040d0380800501501030389c0b06041e51420b103410004901075400921059a29656590340d92100c181c0100442d03220b45c0050b104c8071890343c0c0a18801c401040c44c003440740c482388001c00110025a80303001c0c030a032003100001c080c185400d00e00c800801001c6002d83c010b442c898400710000c40080e606401c6150302c00d8080c603003c3c1d121000c5 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 734849730 1250 734848480 734848519
    0x1c090b09010938030103032309152703011107030c110a030b0112020f060a02060f07050c0708030315040b0109030f020a0b0403032609030901030f02090325120206040302 74
    0x50102c0b0040076403088080080d04540c03c06503048901a8442c40d4106c0454907160900508509501881003010000d105003441c1c81071846a80c000d021403694140905907625029400000880305000381c0c0c4c001240a1518003402403015510100b1049400d03c0e031107646c00341262001900041480c10004c0e8050055159206020010b41d0004080c20540d692154002030a0f10300090aa020f8014021000c00600304002120b00506240d40105541c2d82d800b15a85500580a00410200001001101803d42d0104400806002c4000c00b5517580d0a1240d4034808401d20707154180e016908052440c003440e80c11007040d80c1240e41212020042d416688002480b8940540091001200108011080c51b03800050300381000440c06100044070141e100d006d030405412254004150300410420085503c0382d0024070030649190005800e24100c10002401e105001010504081c040584100c542c0180310b201c2000780065000c90094202030f4001ca0458030607404007a0041070000140e8038654036 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 734850980 1250 734849730 734849789
    0x61012050603030f120f0a05040807030507020103090b1f0f080d1103040b070c090509010e070b210103140610140d110a0308042c04020f121c090b090109 67
    0x703070701c6803617443d40c0c45030b942d00070880c068580001c40100b40d0005502d0b2091485a607010702e80110340c0c2c90409003140d5046410358032000c0102e04150700c0c3d80400e00000d4001035101e018501100d1544240a441e0741c0f441c10903034181d441f00501c1e100c802420803074660086230009504805141c59064003000300b401500e14401e43d4071040342c2c0000080d9501c20301c10100074420603140d080c0001d100c5d03516213480060a0302c0c4242c900300b1103500030b9101004002580700c01040c407450340c091102c00c0400100c19140100400341c0c001d0301c400e180c01503d82c2000c00140207040d8440c108480d5044640d05008441e1403080f0303221700b51070180755076902500c10b10031070540054081d0310080c03040036502d4603498404510f030050300c5000c242003a145003003c6080d844841c7c0481c00c0000800d0791945903245d400300a211054100ca00c2c2d00030860388184110402d040c0800c000c5401d0054009400c0c8e08040c130020103030511580030380450001442040003e030307401040b03030341124580d0349100d01080d00d45a840b40000c9 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 734852230 1250 734850980 734850997
    0x10c0c0b1903020702100806310c1e05030a090203060c03040b1f03020d140607030f06080a050309130902060403030216060905180705040807081b03120f0d061a03040b06101205060303 80
    0x5405009d01e03076400328100d400702e40c9200c10701c01170142d101d5001b403d5421484c200905040c40c60b031000703003da90511420140d644141010b20101d10b1021940120742000c9059620045110300002000240081d049080b904246a060150a02500b801c10000d2141d4140070080c41341d00c100107600203002d1079400a81e040315109054501a05020001030010101044d803020780d1400d244001801550200301402d180350041d01951500c8401001c0003100705944c80c0520105503070b11506000340c0c6421002d840690b100340c004140005012180c01024001030f40705030b0400100c4502032110f615105048910031402e20422010703515001416181401540c0100c20244a11000010003101c0041c41400001b2203160724000e0b440150181074841e040c2001c2002211001c00210305011040380040a04800344240001c070365885804141c0c1540c8c28150031700c40c0d85004028002400103010080e60003010031100044031440314140a06444007018006c01c81c82d03502d000182c1e080e1024411240040d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 734853480 1250 734852230 734852269
    0x30b011502100e0606030616270801060f0e130812151e120304051c0804180929191508031b010b030a060902010c0c0b1903020702100806 60
    0x488003100851303a800c4101e070b0301c81c401d01c980000704212800c600e2035041c400202d035541805080403c941a44285281d211140424011100020b9a00400e00c6458060130040c50031500803450607040301100d00c0081c0c06400c1c0041e52204410014030300d2021918041241061844180e40e03030846001c07644481907150340c004851540315940102e2031025080400b0302100c60402d0700c00d09a07146d40ea240100d014140d000184000e0324055044079110300c2408512488859242c03030307114031102280745582500111820b8598a46200b08a600c03041002240c080c01d1804d841c40031841c00182840d03a0192013240752103115600d445005035140c200da800400e808403100342080e543c0c00266665805910f803070700b1140144004102d50841800b444040e120010010424220140c403041d0042c5040c882c1241448820765000b000602c505007020000c0500e405841d849102c421142c01030b0112500e03842d400c2510400c20715005a032071090812900d12649003440299070b40f000411310064010b410003440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 734854730 1250 734853480 734853491
    0x50f040207050f0321130b100b0a02010b12011514030c06030108030703030507020d050d0225030903020a0617150f031b01090e090d080601020304120b010806010f030b01150210 77
    0x2440000700802c0740003041031205c10001182c8113840d994000a50b0520055601c01098a0118030080310007a0443c2c0b10810511083c0d5842d016500c03250b0041109a001d42d44510042c1c10030324000003810400040c100003804044070b00c000c8104105820b000742e4020b05400f036984015a201040742640200d00030b000d0a40d6940c50300d90b0782e03549030410705046002a0030003002a2526102107100c03040c505540d143c0ca403c0c507654000010294000c0035161742d540310207484540d40603122000c1451018000d032103161205003540107009a100ba59004071041c09032608103050001d0700002c455521400c02c140c00c0007001d002000040e50070304008655a45445190221101814070301ca10394038481007600d0304800c440ea03072841c18090940803108408290065009016a0b60086581c0c980c014070502c1607a00e0305840740880884014411416a0b041c8403003001404a154104040c2e805040c28907a01c001251543c0c5c0c620b940d0000c14090007100403441c00001c0ea5082c000c000c0d2109d420102d603401c1c0a03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 734855980 1250 734854730 734854753
    0x201231b0304090207030215130b150607020d11090106030e031b0c0423090601270608030d020703090902030c1605010209060f03070807031a0d080d0203150a0602010c09050f04020705 80
    0x10b4825880fa223103070000700d0110100340100d02c00400c2c44800d0303500c802c0f03414881e900c0c030a43d040e1503655104083c4d00080100900d20060392441079483d81c1c103105070003442e03e0050301070500c000e40f40160055001c1c50b01c0c003a50b9100d5403030004142c814070b41907110550000001c0303030071003801c02c40302c80325054020f8100321241c0e01407032458203088403041e03180c041c0c007032150340314015282d8a13402842142c480340f414080000502900b02040d1404580c0b001b8045950b40d9030700c1c682072031035025441901810354049482410140e0050480d80180390080f0300354107500701840540384903c18271a03150002c540e200d03480410401d00790150f8034a060024401030300c0e015010507114040d0300403558000010109400901d1781da0282c0700e81501340d034840703030040510190981449418060b5400a03a894102804261400e611030b0000310f11900881c9442008180d00303501f8421022080e40100d0156410f03c1c690065030780d800340c400c40c21900211800401d1041d0040441d000780304182000d007403401454141c3c0b0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 734857230 1250 734855980 734855983
    0x120c030402011b0b070c020d0c080c01230901050c0f0a0309030606120c090b0112050a1b090308032413060609050a1a0a02010221040201231b03040902070302 69
    0x14400c50007070b2102c01d251a169410142e600b40715850040070010201d01140e4218810400d00b00803c0c80500034141d4194151501d80045405601100060344940200002560311045035586503141a50030f107442440400303e064903006400d0600e04001c00455007488944040044601c00d0000c1000d0328802001070400030b010010030301050381d102e03042c00e80000741140f80441141c1c4058004540721541414440c01c0f101406180004504120310105405296040c5200360b40c064400c0d82d9000070105c0000d51010302703260104503a0021b0007282401000450701020442c4d03486640000e140845500307468020000980c00f141064002d5a080503281d120f8030140d2214058540e00e84030001007958600810503401800c1c0503c007c040d001c20300085002241c18080d00b80220306000250509403d4214001c0e80d6099000d00401107603640180f10030345d600305110710941c55904a254004617042c0c08095190301ca2004050300401d5104900d610b582c0050055401400d900803040d951901c6a00f0000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 734858480 1250 734857230 734857237
    0xa0213091a0714030601080a09021906050c070b04152a03020a06290405091002030c07122a140f070e010909020a03230d26042105120c 59
    0xc0040f8078000c10b40300c1040e0015040d80d10440c0140d5a90140d41c2d031300c038500c2009d48108241240c02c90940346403013a8003200b120280c0040e180c4e031399400d41c440f0000607805140000940c00000385035400c000070b100d0301d240049a004001f011382800c03110b0780c460f03400c0c40300031284840212620401da441e542c8101640410100001805050207000440b604900c02001d0800c2041ca10b4001060700441040342c2051341046a001100c0019600a1020b02c007002069910480d000c0d0100b890008005081107120640e00001314160300d86903100d04c00c0452103c101460b1031400c0709100ca0300721038120421a000e0700c400c4110081e002134481d0b582d80d0900296940e4005d016511104e000d207800400c0c10449031184040c2540c0007480c11544a145445a52404040024030701c600c6d1822900192010020050115040c04580d1408403030b816203029200c4840c407141c40a00304451110510010500503d001007100507181039042c0f030803400600a43d2a40700d4542114038042900c1c041091004000024 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 734859730 1250 734858480 734858491
    0x20a02060610050901030f0f050c070c1d0a0504061b09050117040f1209030501022209180204020f1209010b010221040e040c0519030606090e0a0213091a 67
    0xc45030192181802c10040048008010001502c20300000b00c19601c03a0300102841c204660380060f5046042c203076203060302c03400c03140d801c500300300000c143d001c1210030800403000389a0400c4160030a80104a500306207031001e04103840c0f540d1143c01040c01d10900394841c68501841c18030840480042980150072210a4030802c0d010440041d80c243e221752201840368411030348400a0110300791996140300c00b0141e515010070130040b038100e0100001d10248010594151080c854280044050341000008280b42d001011114280307005c1041c2d594a80d112004819411100540c5940c990001c04130103000c0c090802c24980c80c0b002c24010000c0703040d40511003246082c0e00f40d52690742007040100b40e11b80310812003410040200410010103070071941c981d421a2041900014095650300000d0809081210542200d0100042002044854402d100c01800c080c08148500d20044101c0d07034441680301e1000e030103048949110a0f41000c4c6a001d418170941c460b024400d0b0606400c040351800204460 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 734860980 1250 734859730 734859733
    0x8060f0103051605012f030301120611090d031409041d010f0203060a0e09030405060c061510020c0d020d0b010303021c0512011205070306110c0c04020c0607050c10050406020a02 78
    0x1551103404144840c01c0140c03031060315075048a03055036102e038125034208603048031035030018020541b10102c00d2000b14000c000c042c01c200340c0b845590815000305d4210001180c1d40c490f0410080f892500c564824030f00154060074420030610a500e40e0280740c0c81203000a551151400f40042c903049586030450f2a0603561500800150005500f81401c0388001da942c1503010311303866010090320440c00491940600c603003064a05260f512800320311181c05c00d00002101e43c100d0010003100f650b00361001010350300c048a80700c07100342440002a4882d0743d0440040d0007440d20490500a41d20780c3d900903c076055114240041540c0e5a0400945803c50810566801c00300e41c603101d11094800c1003915921161002c07481e03842e902c1c010100100d20400b041c12200c1d4001e81100001041d5580304a80c040c581024503543e440e0b00c7d80d54054140101c1b070a130584160701c10b0141e500100da002404079406901e504105945d0300c0710001041c540a41d03a0340441230b45051400b0041040038640180c00d50020980 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 734862230 1250 734860980 734860993
    0x21803060c0a02010522080307050706050a020a032d0218101e08150108040213140106090506130902090111070902090f040b15030604060f14100206100303030b0a08060f010305 77
    0x11b0f0000b9940c00c2c0c00c0318842d03012401d400d94101250041d0000c5800c0b100a05081341307040b4455a40409507403040301d4807140340380d011031007054040c0c05014004a01880c0c40d1049a80c0b4860040c0c6584c2020000c1d42410a9a01040840b09140910400d60000720020a000c00c0143c945200900160f01c0c0e0600a480b041c0510407111140c0c000e079000b0380104910700075543c040403070b18011196241c00038016a840461038042c0b00e2004c0440c450f41844552400e43e0b02d00560400700043c1011540da0b0129019000030070140c0c0307150b9502450041900c0764182c0c007580d1980c0b01030040362168803280c06643d990003407842c0044e49040036801030440400580348902c000d2a40b1081008943e140311405401c03540c1813815040103480d00004642c408401030000815946401700d810400300d01750060f80004540124654041c13804241020312240750344028006840c0c449032a001c80241e40c4401804c2c10303180c0d03440c4540362342e0b5010800054140e4400300e4100d8942408046400c02e0207101c251641e02a48 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 734863480 1250 734862230 734862241
    0x150307031b0e0105130b03040606300b04051608031216050702010c15020703091a0c1905011d01050a061403121810020a03020f1b04021803060c0a020105 67
    0x8001500c2400950380b280070110848200540d4281c2c0911300c071000c1409802404641c940e030700c1d005140184e000702c2d00007500a0030b240740b542d015900352451840700c5403810701c0464207800700481400c0740340d8020382006c00f0351100c2c9801858843c0321540000589071490001c24138020000140c03150101c0e2000c45501522401c0004105030040080200080c404010002c0075500a181070080d01d880b800203065020501c401c014100c1e04080000c4000941c3d440c420001c0040c041503110014001052040c0303041d4058040565482501e6050345000030f0711851002400000c1d0302c40b07a40d08050351500c0346602504c0d00410b0081030304842043d1501c2c40c0440c08290700855a2242c0c110407000390042210031051020108290454540c2c25a00328801d113112519032141c8840404001c0250003c107060005480e029046c0041d03051030fa04154400400f200a0300c90f00d06040e5500c19040d140165210805600d50908420b06400680c00d0304c15901404080000d03031300100411142c9500070091038580 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 734864730 1250 734863480 734863511
    0xc06041b050907050307180305030d0c090f080a0308151801080d020706120905010914011e0c14090607060c02030c0d17010302040b030a0f23030304020102060403080a090215030703 79
    0x50f603403d00042d40030700010380141d004540da00d030254448510412030542c1e070b6032614510b07031242c0e01d403801c0d490300d5102000c042da80040d0481c0103025401d0049103c4da05001f050b0703a44004500024040103c1080400c54501a1100f034444240c4007410350250a107180d04903000d400700030705c211282c0b40b1a842c1000b2030648041042d40540d192592003100c103a0740805c00c2c1010381100c4d10195400e5580d1034049002030610070100310011590400801d07500240702452030b0003144d8001c0741c000b041c2402812804a540030511143c0d406d0040c00160b282d8242c100459500c1c002c0510040160f450b00c48040500e80d0008054080c84140c00119000b17090300c00b00495210354103a005190401e01500140010310300758006609010000d0100d0302c2d912010344541c82a80c030f001e0015122510541c1c520b60f81200704050b010040c20380c43d0b009502d5404d144e80000e6995200030000b800b085444008a1122622500030303018550b002407031901c1042e20340350170f210103a0080c0c03400340102e0300d04400c0f040408030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 734865980 1250 734864730 734864749
    0x6030f03090b0a0926060421050705150c04170c09060109030308041101021c0306081e060a0506030705151c0908030a05090705041107050f03030c04090e030c06041b05 73
    0xf02550398200041c0341c43da40303810b01d900040d0b40d903510100708901480c030708000b006040c1c4641c0c01410000d110503046041050b070646404000410004100700501c049800056070f008174594010780c000300740c0d4501803a091180103540000b07002c07a11800d11500b00b80300003d9590025031007140d403002c15854140041d12891420310000300411560310000c0c022501c49000e2201900041c0142c60000c0728074006610105443c100301c4c40425900d1009102d41078042003100300040c941c4441c24402511010070740e0761604020007840c40c454441c400540700da10305101c42401004d0291212030a2140d0450100045d0016014003aa00400d0101c0d0105c094042c0103940119400000e11841c2d512070a0740340c0094000107105001e68410f0080c0002c80f900c07940300380300b13020b00101107482d210765040c0340c141c3c00d101d540c00f000d802c0c5501c140207100c500d80d000005c403421942c0c1e604000590a610003905801c0d8003c0c01c901040c0d5008ac00d08000c14000c11070400c40403d06441800511580c440301048001c80 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 734867230 1250 734865980 734865997
    0x304030e0f031e030d0c020a03181a160c060c2d021302070506010311040f0b06220308211b07030c02030f0a060e0d0801030f0209100906030f03090b 65
    0x244024a03072503c0961000045040001943c03d407803415401241c0700c411341c0c0c058071100d401684000ca41c2c00500d03510060060041444152842c401407814103942000c881e601d160740000000020000ca00040001e440024280e00942c03c166065440d030029200d08032042e019103101c41c3c021601e24040110401440c0951f41105a5103820640360302030083d85003401c4180c0c4181c82d401c0000c1804150f00f00000c9000710b00c1404402c1205610070284001d0b0350680c0c600203022802c0c0640c5860350781c0c525042c0c1d440300c0140c904400b036034842c02d444d8591071740c843e0b40003070300d031038400544c520801c000c03c030004540b0204d204a4074103913101c10080f0b100000c0c0b0500081c103041401c0c0301c1000000e00c150751401125000804441105809a50860910a4440084810300c0c5e0720f00c0d070181104e40a11031014141e00d40d040c541255891521041420180e015000348070311f15a000051405004148036009081c0305c00d82004102c0e02ca203803917041d40c5402d100c25004110361300c6000800c10050011256002d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 734868480 1250 734867230 734867233
    0x309030f010b1807170a0c030f020a09180603170d0e0712110a0b0c0a0b06010c02300d120b0d030c0f080f0706050a05090304060207030311210304030e0f03 68
    0x88500d00082000f0030007400440800201603001101901800442c0d03009007103c54001603400c0d004040074007100c4008400c01000360043c4182143e0a400c0303d0701c0c0c801c88584040c440303040b0070500d0755030005091580000b402100313480c03140559004044050030055078010002c00100d000a99100d46d03d5055100b0210103102144100e00081d02c00c00d80d4000d10724cc0039140c1c1220580783e10240c0c0181e00880040742d4158445100e500901c50b0f004c03003554020740282480301954409401055924807131011845080d46100500c02a030000c40110480a032a21000d891208100000040040302880300c0c5042c2642000d540010361326100074803910442c1c1c50346640c03050030f441e550b402c82100041c04081c0c407540010300410b50880d0752800289a9244500c2c000a1240b806021910856a016226a02c81e90060100380405d07500010b111082d01e0700340c2003031541d001034030715228a4210840c03a81600304840008070b02e5200c400c07102642c0900c0c03207038440b40546071181c41480b84841030440000e915 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 734869730 1250 734868480 734868499
    0x501090b0618011e0306141504020901121805070621020405210f030f0904110901020a0818030d0306060e1207050111010f050907030b07030e1b0d0b090309030f010b 72
    0x6207401014204d002555010454103102e5881c1c490004480c24218000c8401c10010200000410741103141c1800b00400c9600b1418010070b0000207100c44802c1d030b000b1156540d034552410741629001128950158010129000e441e2100e00090903414010070354240480081f400384c12007a26402594182e0b00081c0500302450400e51000e8910f0b056116121628010442c14500142c002d0006141c1d40070f014502c1c0e031740c40180205100c101c83c00d80c42d8610a4020610121310180e80c00724400c11502c0c0c115066640302d2082c84e030b0040301c229030b4445c2940d1511070000301e44006c41e0107402440031145161035040307800202d02d05002083d08400300600c1d85400405c03080c4025070041400321554030b5039900006500030641103030411500d06450404155100a10420800582082c46988894188ac0c2808841e841252480c0c0d900168146842108458240c64a540e101d80d406d04220903040a940c20341801c2241055407a94800480c20703000e070250000c1c142c0d00d0141405803805103040031300038108 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 734870980 1250 734869730 734869739
    0x907080108060c07230705030f030f0318030d0207030806040608190308071403100302030f0a21030b060a08010f15021b0a05150903010c26061c0501090b061801 70
    0x2d0768001441120005d1805045401c3c446242c1200244030112400400700300381000c042601d0107900c1110f040096104000200b5140720050540707820412010040c00040040300351b60381540103064280e9519803010486c04141a1f2007441140a0b0000307580c00c102c559140c42c030054440c2030181605408284108030400041d200e1310704a07a000300c551030090b241c1c1c05656078a4030160f00940300411481c245072010300c1545030920503850070303013034100c020702940307556075202400301c940e07040069000408042c4511541d8026001001240c40c020015613440da032006000e41804001c2c080c012500d90005408103000c0100203603400755401540040812091299040d0126507499100540107109004001000c1d1034100d034409034a441e22004e41c1e03d0307446a205140c00c654854402104202d4a4204903402201e4011900818031003030010b90300954903d0f01041c09601840c0e0310804071000c68140106224040d80100080c0f0310035101d0b030b1419101c543c200f10100b0a28100e260885192100421 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 734872230 1250 734870980 734871001
    0x40f0e0c090718060e04050a020a090603152607060f0e06220f030b060301090f0b07031e0902010e0603040b062b03030c080a091104023402090708010806 67
    0x65200c0d03030500d03006810f070300020390b403c6240001e54400d0001c241c290044803901d1811780501640454000d404505000c8102001080900a44510424181e03600c059008804100d0891800303410440e8144040700b079030050b4004502c90508612145000e000b40110307529114103140c51103d017042da103101607031844408000040c0d1007020100c0e0040903000c0648075841116070314600501c52000751848940ca50304180b03850202c0180303d0761083e4900901301000652525074000320325000350320440700d03a440f00c8054006114201180c00b50b51200f00d00c0d0030341410742d0f41024426030310030f03603034591103006100510100d4081a10000c0249000360002892070a213071003034000f0741c55106810f0000b40554509203c1c42c4441410030b5000035120744101b0111504002c40c00e1700441d1f24003003005903007000c3c1c48091001d00b03040e08075440b4030b400185640c540c00c45002c3c020014034a218001305203160b5810040c0038452841001ca004402202c0001ca420b400344100300c2c101c9440307a0241100b956800003c0307 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 734873480 1250 734872230 734872249
    0x510050f0307050a0602011b0e0d08030c0c01050a0c0905040510090c0525110909121308010f0501090506010503041104020d0e06100612270503040b070503030402040f0e0c 75
    0x441e01445403140c0011a580c43c001c030711000b00303030307039000011444c0726804e43c0080400d90035108010320525100700f008a4940f402a10b40c0c00f40c0000c4041e8994a80305420302442c4100500c1c0d410a600704400c1c07200e19059680400941c032491f880c3d02a0282d920b0007400241c9504a80c0b9062400f0801d0040040d40c0c0036400c40305020103a17240191a00829484150280005a90300000c520914030408100f0681c000030f059014000c86003400c040c54200420ba55916840003920a2103170041038440d03104210400c148007600c10074009012141d81d5550290040c00c1c00d02c0345041280c20000401c0c52540039600716806190070030050311403012281e05100c06503010710541c99506540d07944140c41c8072824070685008400d202c0c0e20b01540d6103080001401d00c880010341c2c0a2452800d01c4500000c0d205186900310540d03038601590400c1c0c003078103126041d40555888a800c031900012400100640070004500c600d00c00c5030304000740402d144c034071011200040944400399015a1480c2c10615068414 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 734874730 1250 734873480 734873509
    0x306060d02040513090501051803190908070603090510020406020312060f0a030803150f210f060115020d14090405150402132c0f101d0118051005 64
    0x50b1410fa614800700c1c0405405a00300d4035929556030010082081c2801107070340020b030078010f118448400d16842c585900c40d00145802c030740c03404200006032500900425001303101c08400c0d116001c0d030318500a000707800b810300200e035a401085441074602304548251019280d03613a009600b00300d00d0303100d038412280c1c024247d1030703204641249110b40d07036440c51078036000b5512511071030f43c4904100001c0e0b10104440c1240380c3c81200c2903086040e040d1504502d12940b001d000d1410114507500c0d1203418140252400518660b0140310004225045021000006107401c0d500300c0f10250822082180d1510b0240841c03209000d080180382114070785504001d07004040b00b00407000b10602d22001408a0f03110302103000002049840c1040070181c03049014004000c81c203a0807211001180d900c119a543c002c1c84018090001c0b17022504000c2030036220400381009086081000002c0029204541400d10803900049444c1c08580e1030400e0712b00400380a131103038094080c90b86082608018201080c21070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 734875980 1250 734874730 734874757
    0x1060f02010b0303070c031a040809040b0a030609030c05060702070b04060e0103020c15101d0703021b0304031b0b071a0901020c01110403032c060702060702121020030606 75
    0x700c2640e02413004100130b5108445444065180d898511404904840e00035002c04660040001040c01c050413140d04000440c1c0020f1b034100c001c00024514409604017070300780d0345440303440010503030040c0c000345480d4040c10498126a4680c07104070703619000f80c010340310060340c207200401c000350181040d1031048105040c00b6042408183c01c070380c5081d03004c11031142d010a4503410f1103001203603044604e000c1d051000d07140041c01da07074000d8003151800c0500040708040e0300242d1841880440388440008605042c242c1e41c4d559924200408043ca0009030305180c440000400540e00c0c07186000c5404c11903104c44075030070540c908d002c0d04074620ba00800317a41c846c3d5002c0080f01c07001e400a114101c0062070380800a600c890540c14010004030200e08003143e140a20500d07898031130072810b039040b9403600441d025503541c545480480c49a01858900a40040031100400d5054002043c104006805510100040c4104000a0902c4840c1441212204208001084544c104080200343c3e5410180 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 734877230 1250 734875980 734875991
    0x515040321030b03100c080108121204020316081501141c170a08011502010903052205040e0303040506070801051c0204090b010f14100f05070609020a09020a09091401060f0201 77
    0x100400c0c2090452805ca45c203c40e03603018140342440d003100509026000103001000c10728050014401184548440094441a01e200190440d03038200800400030b03540740c500d0a611076030382c40000c1c0da4500c507040158160401c0c100204421400c0698200c04850040c03e0700028800080000c1d00d20340c2208003950507816044441074a5400b10000b0016000d20740d40c1c480e0325601d04052644c000958060301000c690401410001080d84042550b8400c24142182e40303c40885811035180305100da4849a0010705101d5442c4a000e00440658811402030044c0c42031aa1002d1084404090074090903034040c000007040302c080801c88160b9030100388007070130000d84440d068030348a8801a00b6803141c003426881d13140030b00005030b0b12003050100d101c007512440d4942a5a000c06403040640030312040800c00041109414071030300e070300710744107c540152526007080c0e19800c00d0800395006007070200210781e03022400510b650544c440c8000040c0d04000810499003845000c80d00011042c0a4104664070755 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 734878480 1250 734877230 734877251
    0x2c060d230c03030a09060e0d0201080f100801112109031605030c0106090912050c1e01180501150f03020f09061807020321070206150a0305100204051504032103 70
    0xf04020615440d09445010700c003440c2c03160081c82d400302c41403140e000b00340b00303061800140d800450385a04540070000544590352820400004d50307000350300102456080c1030200841c1d50709c01001300843d6801002c2c501562000a6403021661010740c0c803525141d01c100403c1203000c0e103480340500b500c0d10480540749041c1c0101400d43c2503030f4442e0401010b280e911103404d030400046980d81402d0141900301f007400d2100c00420240c031020811407030003100354040b0006c5440082036020905074441304071807084040c001c8c10010700030700b996415101c903071154030404070701003c030840e40030120b075030080210361a1261b440510607142e01c00b4200740e0f00100b0914020a44010354401c07640704141660055488800001c0e200400c0c4111403007418080ea80c1310107103c4d12540c0407983c2544001c48021010f0080f038140e01040342420246d01c00b804501402200b00180a126001407088400464160f014004041e8510445108500c00200107802d00315001e65800030404481da00840281800181d00404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 734879730 1250 734878480 734878483
    0x60307091e0e010e0706020f03090f0d0f060f0c02010b030309060f160302030a1206121704080f07091406012001020405090a090501050108010e0c0105030901062c060d230c03 76
    0x450403000500d0751260b0a0f0b022080003000b282000789907e10060603940d460f02c45140e02c900c41d980003540180201e10020b04140c9a0b0001c1c0704070503910112552207207681d0f0600000410030714028189150505d030386115240d105018000503008020301852401c039a200802c040d0303602c8030041c02805a002e10200306075035040003041c0c201170f0082e000f55540700f078007850041546000b2034951000b03a103000024014030816014006200354040e10760604504c06a900b2020b901682d0b120382020312610030010312034240030400c0e00440e20400010b110080c80803000f1354200c40c04035000c070f00180d4072039114182102400712044a036004040014503043d02d640105482d104219250030072240ca0703200040400000748159130060200000800043d1400503202d92144600c0680b40d040040101c04141007039400e5200800402074908030410400804442c2070440d80c0c0402900c162640907800603416007080042c2025442e071011103128107001c15040c03490241880f011500c0c0f6071044c100d45000380d4a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 734880980 1250 734879730 734879741
    0x30b030f0d0c060605090408090d02040b090108070e090a120c03030e06070305061306081002090f040515030f0c060307051b060103140d0509060d18080f0a090e060307091e 75
    0x1c0d50340c00302d1a03846070400105803800e0b41d008a00414004042102180d5210305440c00300d40210b40088031450540001400341241c3c00003154410354030f038000114140d00154400850f0410f4072039aa0b01d035560740c00c03d03407030306140c4401a003001065071120760101d104040046045110b402c000500414106c9035502d4040c0880748a80800e50780d0301400014a0007100c000c4510b410b81342c06100840c10302841c0d548130080443c40c1c074602c0e0b80208000e00c4550300c030b01903030001c120040e004101d80c3c07400d41104280300903000e0040e4007a028002c0d102c103001a020410004621000c0e101c00e180d9125218100c405030b03c560100d803250080602d440c0b150f410140101030003507014111850711050410388127030804c4003d00756413003401800c0000f212191164015140c0d44400d07860b000a100403000d000602020800b4002080920000f440303104045528000d00b4400c000c3e43d880f060065120703a0300301c030014000d641e0164107600c0302e1410801000d26410040c003050364055021029801440010243c80 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 734882230 1250 734880980 734881003
    0x1030e1002120a1a0102070e060112050c18090f040f0f051b01030605180103020904020a03120f03421a1803030a0c110103060e041110020d0906030b030f 67
    0x90200240480d0b80124080c070007140c495114405102e019400011f0743d2003e051040c814160207aa00049079a800307464007045004143c2c4084c0040d01e80035010850310381c0420300196280e091b240042c1178505104003500d200c0c03c8024902c288548070740d140c0318444070761890200c070031a0050500200040c4117000d84a80c03e450301040c0d141d05c0c0560320025054840540015014100212503003044002d260b107103504503501910022819112400451001d1055030800380904442d80004041c036503010342800b803200110790b000c1040d21240d00580312407811020a444221031064600056406a155004180c0c0003028180c104541e41300c1242d150302150004001d4100000b04041300c00d1195910075070400801140510310300350b0755074400b90843c40c610394041c0005036035644d502e07003d90003a405000545070303210303014400b0325161400741c1c6088914608940580303200300d00300e84902c0c00010141c0d0050f0103074940f071149a0420004074010a001100300c0c3c1e051041c015001c3d01d481040c822104e862 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 734883480 1250 734882230 734882257
    0xf08130914010806150103090c08060c0a110c09070305090c09100603200318030d0213050f10020615010201140a150b0c0307020907022401080c04150501030e1002 71
    0xa0303803104400001031805070720460443d00240100105c1406000092040c11801d0900140c0d2245500b054100d500745034000c8550b912450040c002d42170f0400b03020701811070450762006075400c084603550780c8441e405001c0f5600002c0e500082040c06001c5d03007104d540004a401140e00340483c0d040016180141036515089200c0790082c14070002d641400b480c028401c0d0700301c028448056421100481d4071004240c1c00400400035500568401c0c140115517081c2c040360b00954a440800710100039a4040c0e1080c584502804c600012480c00c00280d44130010840c2c0c0c020b00071a039111a1260050b0301a4100181155620038242a4010070140901e0240c03050150000c0c3c5544404100b0005e4a075541005801744000c1c171040c92140d400008441c01c1a40c16146031441b074407503400603440d00d40b4074100704a84002e9106d016120440fa012014100c841c0380c0102c07440e5003081c40c14041190701020440302c1d4604540c4040c003495007c0d4000b00d0050303018208071440c1100d000e40c602c0480c2c00c44256030381130 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 734884730 1250 734883480 734883491
    0x40b04150b1b0a0b040f030c060c03052508060f0402070b090c100c11012a1a070c0305032212081605090102030a080c0d060b070c140d0f081309 63
    0x24003142e500440180c00e4190002d003c607841c15111a92200d1000388010880c2507400042d42c101442000ca2011182d4850001c4c070800c60040c1000d00034140440d8060502d5040b1440381d5482d83c501445c12150249540722202e0b142c54100130311582022260140d50850b40130000403000034800d0315020310414246000c1c00070404041d080086071a030b13804420042004031041c0c3c40101b041c02c0316134084e980090a0500c610401045050304040f803000a040205503200405014400c211060986500351500100110f5503103150640f05400e0854018001a00500002d031000c1c030b00450001010b11600e001c030889000c60b990310b14090701c1e000b80d40c8000501d27040610074507804400a0b0707040da201d2420000d06003144900000d40c0c0f40541354804003040402c4c00414201c0a046080b980c402814680c280102511110b4001d40c079403002a00300c032200781c40308001918082a560800c010080144108506c0b061525081c4c0207001e07650302510b000d0390810286204000c605007000040c040d4902c042071 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 734885980 1250 734884730 734884747
    0x18050d0b04060b0a0503030d0f140702060906070f0903032303100806100311040b0d02060a05040e01050301270c05180612010b0a091109090a02031b0711040b04150b 72
    0x341c6400c2c03c586070044503c01001d11450394040145c0f010031050100008600300d00c0303114103018186214180c003031203902c00c040c00600b5a0128105200c2e940100407240241c81e9100c084408050044684002031400401400002d2080750f03604400d007602c000700781030300400b80c60501c100e9000f42c0741100d40d0401a00c0420001c0c0c814405039500c0104d40c4803405c0024910340322081d0360481e914030948070b21744d201c0c40b003122035490101c125103098000c0e001d26260015000058019031160080305c0181b003107400002060714050140c0220b05005441059031000818883c4020000b4550101c6101d68452000718481c0c4802810b801d18405004600c001e0742440d40c01d000105260000c281c4503a41091200d040c5500d420144208451040100141565801e0710801b0f140c0110300c451584140301d07106010744081142c020310300a20603c915420070308140701c0c40544c54403c02d180180881d1020030400c00600e000e50001c070004034090b001280907420400150401d1402d9006144411804102c804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 734887230 1250 734885980 734885993
    0x80702061f0e2706010b120901090c0e1f030f12021f090b0703181712130b010e0108150705040306181502090a0306020f0c030a1d010507030f18050d0b04 67
    0x11640f1000e0300c0500a83d50410f034841225214402e00012100b048401103503054001f5400710709030980103d076050403036481c0c2101200540040e20740c60b450b4581d641d11103000c0303640612508112035102081070300407005580c544151301030550551056001c1c401803100d01da640f0400080302c04d22810000114801c041c41c0c81c0e0708000d000382200c02098074141c8016461298000500c2a20b900203034004d17440c1610640c107601510615800c4a1864000024009840b500001905070103204aa040815a884001a01e0000b609209030b18940c0d0000d032422048018903444c01e9001016071800030320749500c0742c85440c00ea41c11021024500c1500d41452010300150001c0080760055442c03040d0301d031621031400103490172030700d010145c00341d0760005e0590010f03c6030004030b503e82c2d45844141e0340c482c00e08020207001403ca84a06c0c0d800308404828041e00780d8890702c101e907901a41a05d42001041c00e094040380c440060341128050f4030b0346c0d49000f0a02d84e45008540810314441c6003c10394600d0310344cd106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 734888480 1250 734887230 734887291
    0x30e03010c05121b04090f020705060106031b0c050114330d0803090106030219081902100c0f1709040e010e031c0207060f0b10080702061f0e 62
    0x4402c000c0c052040c103410203002c42c401034120b51203100f880d0411100d810316075050310966000c0250107140c0203080c0000c0710300781c010348910f5018005a800603079960b07400b90280c0d1000031580504d8521401c500b01032034061245840c4042c025800001c91000d0a1410482070006030ba0780d8100ca0303c8003604440400042500c104080d0710745150140c41c40c4440042101d02131148401031070714402200041e424030f03095003c40f00554000f0801850600001485040342900c2c2c0117600341401540001c0c0031080d40100035180f0b250340584900b40d0040311540c12104040902012942d880700151720601146441c40c08150068840c06100c0d9251407440400040381c0c203000f48415a641071505001c1ca0090100070386010101e1a00070a1803c0420b514000c020312650034010710040c0341c60b100c0342c00807149a100310303254113040d100c88150b600b0044042c0d408210460b104c600503031019000501c00340c040440c00140c2080c00c020340c4049612003050101c0c1602c01c80e003200740d036525181040e03d580c03a0f16202c1c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 734889730 1250 734888480 734888501
    0x50a1d09070c0203190201230d02160b07140d020711030109110120060109112715070f1101120e0d170403020c0d020a080607090608151e0a12030e0301 66
    0x101584111546c006809601a0100700f0680c4400952400d205038998089802501003c0070866840c501020b00c0c0c0001c40d81200d0590300c80350321100203410b680c0100020100289040183c90404c103a0351200c0340a9440041c0c2112a8603248003440708a80b0240212985d40f4411401c0d21801640000014500070f0b011802002152402c0480a042c1c42d0100f521030544001941c04102030500c22403140381403046860380348541d80510f540340801001c1e02841c410125046811288141d2160210341050144550140600508140f007900191100c2c000040300d030b10604050240c4211051440102c0764680980b01840d00240c00c0c14403032603446171020b210004940d05031191810507480081d560703d40c00c54013600500c1c258003507405558076021742a0007040c0b00c2c0c044900310300d0882c0c002012400d55204500100d6030840204081d400d03225102e081d0500d0160078141c0769808541110262001c031131405400000003903000c22580c2c0042c1c034a803440d60180d11a1110498044181421940e90440 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 734890980 1250 734889730 734889763
    0x50a06050301150b09040e0a0b010e09060c0f0a110115141008070903031b0204020301060f02010f02160b15120307030e01050909070e03100501060c1b0501050a1d09070c0203 76
    0x105000030341844c426103061200984000401d5201609114034181141001400074950100001042d020210a55210708009400d40e40152900d000c0c841b0f0901410b1405090008180300750715003240300c0c1070000110342403c0004180c60042c41d107040d1452100d50032a01d0300e034080214800a07800c01e01d1402ca1000c0c032525052220785011803004000f0130300d81c000102001844802622580180c903070003182c0b2a0020f204660343d586d506ca024201e0a00c400041d0059420141b0800d0615014825250311040303032281000300d18840d6480742c80300c40f0700410003d00ba5462400740e40107900c900e4034094a4000300c40055680b400503040241000700e80d5002c8030b04010007008948601d132140600650000040d0910907003d00692001070b041c10b40f02c048020b00145414000035105501c020380c059210b000c0d000c200c0d000400300d800010751104034042c040c0803620030841040c21078070418007a00b5000d15840320080c1ba120311000030320302d0002510144006401200080c0a511341401001140c0d007a000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 734892086 1106 734890980 734891021
    0x118022b0605182401090b0a080307050c09010e0610050706021c1e0207200105070605010602070905010801051005010f111c1112040506180301050a06050301 69
    0x20000420b44107404403800d0340390014198070000c3c0c1c4c04990710403c0340c2c24510300102515031a20000d4100c451130b01d001a42c1d8000784060301c000c40c07280c0040c060308980f44041100a000c181c0200245002541c14005180c0d01e103e074108001101c1e0514688580450404000070302628880700010324480b4030f011204209a8030055a0300720351203c0c0d18040308000320140813030042c03074002044040e12034103004c0d407055540204515a20f0500d80380d46440896500c00c0305580342a071008026a000c0007040c051104640074617405441804000c10a52a01d4588203103510990b129403414490b0340b82542c0011845070b418000002c0b80c800031900c403207004001c5459114060003003000000c04503849418810808140e4010160344806081d05090030281008070550003100d010414041006020072191028000c0d46c0c8100316030080000c010b0324040a05013502c03c842c1c41d4100b400180e4 = true := by decide +kernel

theorem cover : BRFrame.Cov 734712230 734892086 := by
  have h0 := BRFrame.cov_init 734712230
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734712230 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 734712230 ≤ n) (h2 : n < 734892086) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
