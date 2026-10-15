-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3966
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:11:19.634506+00:00
-- url     : https://prove2.me/submissions/abc73a84-5066-4d4e-8121-8013a5fe193e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 713129496 ≤ n < 713309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 713130746 1250 713129496 713129509
    0x30b06060a020319030605030604050a062d0b190605030415020405060f0f090d06020d05070207060c06091403030c1e04050d0204020c0106051201200c070509090f0d080603010506030c 80
    0x440609400541c1e0320342c2c80720803c030028246c07604800d40c5805034209100070320000040c20450517000304410412000040c000942e010383d40c1540082810090101c04d0341c09406620841000c0c801400b045c01070847c521801c02c1000050b000071021400120901082c42503501680c07162401c3c1c80421840e103401d180006003180281d0300c008408101c001204e8003920090420340d0171608000e0048180c940e00352802601a41003c20803001c02e510701800290381c103100003a0349040707699a86600d294002e8903220035001c0c060012040e10b0448100403100b061800c01c2004610514401100d15290031400b02403241c0c40003400d0400c14201800e000074840341d518a5408080c0d1981240c00503562030600c1d00c0365000d0720b40c3e94440d0303920202e800f8142e01e98140640045442c0030280009080c0c0814101d069615401510f6100281c0c0e030014005000e503090008885400c41c0c1c090048403155081d8107000b502d000700d0090b0030b00000754243c080c88441c3c2000d0164a400080403005055030f0446540032401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 713131996 1250 713130746 713130757
    0x6060607030c0b0c0f040b0301080136050a020a140a0602011e051e0a0b0a1208091915170903070201300f05060a0b0403051f0222030b06060a0203 64
    0x2443c02c5080206000c01c610000b2288902c42c41442c9685407a51481407051a8009200e41d00c110350a140d60302c850f150072003000003254829007005102c2c46055044013440a075508500b15554807601e80801d001d6600ca41e8501c000f8010090014803102c2400244590240b640d80010250381c14503004404841c1d0381c1e442c01016202d00100011250384d81d201000c540b50400700e004501c004c2203420300100c0750301c5410044c221442070f50185516a5a103c0c090814525210003900f00c3c20240500c08040c680034150100c00c0390400030400502c1c0c0c5031403200000840c10803a00c0086040d111030707103c0040b00140c410394000c490101a508006454001900c031244112605400511980311080310000318401460a0350107400200464491804a1350082009880d201e204038129080001c4400e0110304170750680e41e00c0006480c0040c00140c1484c0c0d440d044104e88280301d80c080c0b28500708030141403490140c00d04003103520f5041a1440c1040e8480c100040c1000d405058100400b24030241c0000480320f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 713133246 1250 713131996 713132003
    0x403020a050604080606220507110f030a0c060e0102040e0a0915020405010f030c091706040b10050607082d1903022a190c08060a02040f030f020103060b0f0a0206060607030c 76
    0x81d40b8104040301138290707c054042400b01c00740350006002e038a41c2c2c09901407510354000c05c100d034486404000b50366502d004200c42c0c180000c2440229030001440340d0030035140c12403500300260810361218481c0e03400c002c086a8a446003540d03078004200740305240c5104504082806821441d01c0d0502000800d0a2800d09541013810344501048062601c940c0707030f40c0d00a05d1000060300454601440254442c0c4c402d8505a4501001e800820035400312801c9920480c2c1c001021145407103141d94031038099421502c60000b200040140c0d81c4d03054400c06c8041803075070030b07200351460f61103040160b42002c00013982018020184148a00c281203400129041160701e10402141d08841d0020015860854480070607140b01c2084414501041480c55080c02610318400680300d80383d9600c00301904a006511032042c16040c807100800115072040d82004e44140189130200c0c1150311090042050b51110502d0482d031100041d41e10442941440707415001031080b65032074036001c4c9540740106588901c42c8041d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 713134496 1250 713133246 713133259
    0x3020103180203060106110606030c0a030f06060b07151410170321070f020a020303040902030720070f1d0103080a020f070806150d120f030b0a08030403020a050604080606 75
    0xe180c0215640100010700354000c04a811568540d80014980d070f01c0c480d100c1606202c0c64000c6180307450003082908807143d016011520107031454440b0484c0803070340714055621a0b900d50700801c0000800004100c541c6c001d0450b5110700c1011425030040b2880c0e040444460a01d5009010f102204c508c0d240c011140c802d505c11320ba43c0601240b01e8294810008500c00428506d415805041c00310410a841504a40c4681c049030042480c1a40c4a000c4164001c1d4150000c000501c0b1b445019030140d078002586150500403a8104650b0003800b1650400500d601e81c4208002c01500a008409a0180c0b44210046000c2070680140103c0e448041c04024150440030401000a074800c00203549405a0300048a846956620300191146016500a4900c4104041611580c1008407003030340342e0741d484008001044c0b40c0b00c004544458500b1a850b0401d0b81343d602a460f1a62a44850400341882d0310146940b10325601c10808042c1a550013680a90f806001c20000f0746c00c080b440d1507010348283c1d005d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 713135746 1250 713134496 713134511
    0x80114010b0d0b03070905100602060417070f05030a0903140304030c05040234050105011a030615160c090c020a05060c0f0405090108032703070512281709090103020103 74
    0xb8003015240040202d40c241c4280d400000e201130305034016074000c00070701000501180e00c42c882241c45d60000c6801a150440d800c00c0300c5d10106042000b4030009000b003c4208558070191750303c508640c4440030010000700d11000520a00010458038216181d810b8001c40c0f62620350750361541040b485218191040d030307000c2070100d18405000d080803540107000485418654a84420001c000404002694039610344400031070180c0100100c01807001c4000d0002d0305680d11035081180300401444c0c03030249460240002185010942d41c981c0300e2602c00d005e01305055007800c0106c030845821510880440d44505040004614080744580c1c101d111032030415175841501c584e518591003140e01c031039000324203800001501640400a4201c00d0075072595605180c02c21603800669a28011003070703a040e04002d1003080f29103071900310741d101654070906803101c1d4144244800c1107012108450000354070064000d00401c0b59032581c094101d02e244c83c8080c284030002d004a01d421005000081c14541d840c1807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 713136996 1250 713135746 713135767
    0x50915060315040e1f0908040b09030a020301230903031b16170703030f0605130b0d060e060f0109230718080c1e0d02040903091703090a080114010b 65
    0x154140007076015206001c41e0103400c500980d1450b110b044a205107030410700c80a17510080703001d6401000e4000024a04007401d009214500b0b521002409a052140002d8040103881c00e0107800c103e0f1400001404e8018044e012000c0725180080c1066201d400410401254030003000e1f411440e241c0a40c011900d50791182c20031020300c0f181860190040c1209204688500740c1007008023410380c42594140325022240449100384c7d15540503070707548140d0946210702501c50b00c0d0b10107501964020209810000305840742c03021140c0c24504000c0c1500301d0410803c2002e03202c100540140340e01c0c03204004107000701d031960460b00c1f640c0310141c21460944000c1030b2410b124100801c080c0125254036198a6070310b14050369140208007907075000f8092000b80211964200c98407030700c0d81c0c01c0074040032601d26042d403c0200506a2803000c03014000d0903070020030501068035120300720003850002980e4a40c0710b0002c0001c20b211070751142040fa810f11038008541d00c05024501d045484007040c0a031625008034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 713138246 1250 713136996 713137021
    0xe12040503033c040603270210020c040f1a030609061303170708060a140d1b0305100b0913050c010e040204170c0a0e102705040b0609010509150603 65
    0x4043d106035180000a001e5000003410060049580d161400c200807145170810080c400c41c500142c0f011403040e4940d000250078544c01d071000c0b00015105840c3e913a42410000f80442d0342c02507001414641d40d02c102c1c181001c44142012a40c44118002e18291801120aa5846200810103459a0201061001098040c240b05800403d070360340202d0003403800d420000c05201085074158407462402c4070004034484207400116031048080c0c10f10784105c2070b07526400c106042c400c07080d840035280b1200010100300c0030f0103200c0c500200c8203004540c1e05d13480301c100104e442014000c081040100804140040c030300154000c3c0707000c82030801e2000865090000b40c0280a142d205101648000500e88002080800c0c542c144005c21104100042c0e210b00c4180c040840807541120400d03110710043c4000d92001000c3d10b5011042900080a0080c408454041c1c901c00d0343e080b06c151500d402480700314609151040d002d80403da441b031841d494600d044100700c441c03021200b80103003c00400f096036280b542d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 713139496 1250 713138246 713138317
    0x10e061822050f0129130f081501060311120402040b1c170a0509014409010e190809030106030b041502031306020f13090e1204050303 59
    0x948034422140855500720015000032203110751100116400496946920108424150f07007100c1d400c14010b8403078260711010340c003c840000300b015207064001080d450514500010301030030701c0900003901c1d0841e0101c12441d410b0b00480305141c00c1c400220784020048044d5007402c2c4500348900e0f4181c403a8008500148182d102242e00a02e03801c80186d0300455211905c2c034054440c5000002140304680003010601540d5000c40c00103408000c14001d43d0b20407030007200e0302c042c0c00106d00814000d8801c00c8001c65011a00f0954400b40b80f065070200380d00d0015011f5108241a0090080c1014528000d490f01d030410302d2100030210f403002d00000d006080301a9404000007030020070540d912403c107265200c03021201141d40c131034074161380419110b840c000e682c01011210001d203401c1140380d8407507000c1d4009110b042c04d620f000307000c00b540e03400b2088040b0740100842840011407080001c2481d0074a800c500080c0b07842d0600300b00c01c01c09524000100c41c42e40601442031000a00d02c0d006540300000e41 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 713140746 1250 713139496 713139529
    0x1505030408070c0306020c0705060702100c081b0c0f1c061505030604050a05190f030c082b0b0f01020604140a150b030706080105010206060d0602040b0a09090506010e0618 75
    0x1848001c410003180364010074101f204e4208895642d035850080107514415040001d4002003240b003009165409410401806840343c41c00e2800c2090610814600f00d40c690b100c6062940800f402c0e18581c107140c40c040484102c2914005181d00002200314544104010000d000990310120120034582154891014001c0101902c00034200344c01c040d80c0c0c4628811064a05010302c0000b000484074a0703814050469020b150f41f504020305403402e0352403d21031a0181e40f010170070025004107544003120101c000354035040c42c03544402c0c0f5002e03110480e203017440d02c203000e15018150b00c071551782c00040b40d5600a500140000c0d90014810b103046c18000070f0741000b02900001c00c1c610702c40000c0c9400c04829100160222911213942d02401c8072804800e21030703140960000c0c3d011a116040c248541c0c5081d0f405070b0001b504e85035482c1ca041e025544480e40c0000054040c103018401088107000c0c40c2d03000f600074a0681481500800000c0f801e2156048801241d403409601c00b01ca6154154501e6010a8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 713141996 1250 713140746 713140763
    0xf030b0303041d0a020909010303080c250b01060302041a0d0f020406021b030601050105030f0709030b090f01061712071b0608090c150a0e1810060216150503040807 72
    0x9850f0000c400003500e8054010300302d00031800044d9068054802daa035551001001c8225503480d5031810f80e030108000e0080046244100a50045201004003071004a808052070046085203803e04610107a01030f0007100400d03004000c100000f4858904809104125100c01a036404c40407609100030224803404914007030001c14006032072030b00400e09551003201c64075880c071412502000c140d1074503024040d40b0b011070400e0011980403510090800c1d03000240341021480603480e0f440e1a6800c40049542c0d0200381c1c008601c2d010b0a2100b8059280100300c111204000c42c0c83c006001c5440f0302c040300890300c136100007003182024402d1600c0c180d000c00709201180907200780c48100c010a88481107440d054940b041c01002070403820000c00d100b0010006414240c1042e8292030100c50725050701520a03400a501c50a101301010702a4115000e0f80d422000d2100f0180340207000703410800380551b0485424100e940400c400400c11100710048021031500541d00e66651414599600a000025140700c5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 713143246 1250 713141996 713141999
    0xb0321041d0105030601060309020102071a12010e071b0c0b07241d0a0b0f0c1e0c011404120c03030e030a0e0307090207020d230307080403020a0b09100f030b030304 72
    0x1007101a1603410b9580581c26155960780780d4030140c0591720f15500080c010783c03042c882006500c1070200340d0002007200304915440e1a8a202c48004080000c0c1c0091048520041c1400741d207582201008506a000080c150304403d000c1c0c4400260300c445101d0121100d03030000ea0902006030103031150092400744c8682101d00204e01c04240001d01c640e01e02004510802e82ca160f0790b00f4030005209031215804500004642d4400074100c1030101c0182040301c0b80041403124640681e600a02c1e40b1110b21050780140c0c41d00001c254250940d10003800210038151500d040c800410a81001070721211840c0c180802d007200241317000c80c0100441c51142416000101d5294a640c0c4e201c0264050b1031001c03012602019201c0c0000c000300d02c01c2e43c400030b500003607500708400003809005828020344031100d111100c1d6429594118216840044211015000002c0502c2140313803030034405010f86010314409082540c002e0103d001d94000803000350500000350521024070b442600300c01f50090015065a8445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 713144496 1250 713143246 713143289
    0x4021c050a022d0d140a08030f0f060a0603020a020703061d06010807060507020d1b06050301090e011a040f110f0408010b0301020717160812060f03010b032104 70
    0x1070081200c100d100302024030410126034080088500c2d2803110302a81886840e00030304028000321015011502c0403080c04942c948000d081c400d4081d4280038140c00c0b41e492800030940c40b52020020039481d43c91440c035040c042c0340d4654061640076a44c00b410010307541e003100c1c0300503441c101c0e480d44010300c01d0341081c0860b0740041c0c9520200c00324414090494001e0f90700c82424984405080c020540010341c1403098030007610380140012489402403925101405014a440080784a0b9400c035a002c5840013004211500e05489582c80c4140f132280200b0803400f50b0b45030b212036000d074024007500c29a21800c0e0740c107694800360300800c1004840300c0d9181da11100c41501f041980c00a1040a056528141c611000c6003810300803904e0866000c9204010581c245840548a030403001170501d00003a84400203002a8561004146560440008071018a448030030400701d001c540c0c40d414005c0e41031240200b01624001420052041041d0f18500f149510000e868a240070320380c44540c05041078488080356 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 713145746 1250 713144496 713144503
    0x80a05040e150f0d050613020d0804060f09080106081942110a0804050312010909060c03150b0c0a050a0f02040c11030301030b070e06130602071215020304021c05 71
    0x380c14290381100001c40f09404112100c03101c0800584030b80c0024000468249028500c0c0c080d0030320043c03100c0455900c40c2c5940045400c40c3d0010004285c840030040360301e03600505400c009106d1000248046410407041686400d02070208100818030045144204a40c0c94444880c00c0c0c180d8009009070089a00900005140840207011050418154065614107800380300400d00044203854a40030a6030003c890032900204141d0360b50000744040c065880c40d69003550f00a00c210400848c51000f40e0500f50304564100c0b0100c000d051500e55202215074a07012031404030f170f815140071a20746c00c04040d124101070b02e0020042c200d00030026120b04209010302201030701c0d8008c0e2810040e210607890296403000080d1001d110350b03481803004100184052010b241d1001c0907140c00c101d046003000c0400d840340c00410b07001c1003c10020000340300003503040029000408160072000c0f0002d115445031407004034480038440b002d540000001e0250345070000030070980f42c1343c2c0302c048407010342c2410030f0303500e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 713146996 1250 713145746 713145781
    0xc0c061e030a0b0a0812030c07020414010b0706150e180c030d200c011e0c0f0303050415060b070b0a0605060301081e010c09061d030303070e0109080d020a080a05040e 73
    0x1040041400c040303508040012201a86c5681001091840d2a4403070040041c1d04a548101d034820b0312182c1a074484654001e946001b8650384034801c0e1912624540301c400d640d4000e21813080503101d000100070a0f21a80c0005400104203055100176400080c0002c2c02e08100c101030b0740d0103204a64144080e0b40d8024010071918050398204030007041ca003149282c4039843c1400d80d5002400844a0011142c82152100e0200c521420419078101c1941d0315110740045826080e4003203580c030700c2000207201c600207403c5454659410104a15400d159100403240920540500055162000214203048035807025000d000700820440c0caa60350303044541d503038440e404e41c0300401c0c4c2403440350219800c1c01401002488406502c5440c05141011002c403401500101c45c44c080802490312201252801d0006501a10b1306540300c001d82c0e007091001504803820340d81b024080d03a2140070140740c600e074045605400d699001c40c000759074111141040f201401141c0000014940036030034000320f150300304405030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 713148246 1250 713146996 713146999
    0xd090305070b070201050406080a0e1b100207052d030f010c1106010f030609050102090d0c06030b03070e040b0711010c020303062106070320040314120c0c061e030a0b 73
    0x800e0a602c4403007002c031501030380000a011078000d12090103402e000c0c0e8426076118610714400102440481582441c1051040d901e1018414466000c01e075410000160004402c43e8001000c050f8544000300782d40090303200c065907100c1001c0c0c18070200c0c603403448000802490003d0842cac210405545455000b80140d4401c9008503000300c0007124140b40108105040b1200c4611324001075256407281405402c1040f012100b030f5501304400401540c880059001c062301030511301001605040000d0100d50380c5040103071083e80982810030462000001ca50790203544000440400c1e283c01c0d0061b40c545410554400155083c0595110400c0c1c0c004007075881400200d0701150003505010400c1e90301d0343c008000a1391500080b00180300ca030b0081e04661243c220306021100540c41510002045401c150000c54030b000030002e0903180d0542c100421050030040f030400c40d142c0140105c045640c0d002c1c0c0c1c0354030390081c900881c0201c561045000e0380e81d1000580d107401641c0346801c5034900014500c2d030071540d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 713149496 1250 713148246 713148253
    0x15090f06011d01230609060403060f0f0609020c0a0807030c0203120c1005090c15090409050f010e03090d06051513020d0507212415020c0f0108060907030e0d090305 72
    0x241322507440d4010f034541c921459450020074000c000d10a1603441003e200703030808070400c4004005040303840f8059040c4000c40c00081d07084490006101038880d141e000ea81320a006211000404001155a403001540801f10a44d145224602034513001c0f80301901035454018464a03446450a410080800405c50303420b841c0b45040c840d04d007001315081500d020600d544120300300d6525041480c050030702000506404c0d4142083c0c14001416074012100441d004d0300500e0340030021b01c6d400d0281a4034064040040c41c00c101c1090042040c441c03040c6000b5110f5522880807400301c4444c00d980f0240480050304440c0c0c0e4041d034400c11400303944000a5500c41e80d1501c2c0c0003c5089102d50811a50120024101090914004481030140c264a038490b45c280e86910103244401406c0d06549005001546800e0380400081d00040d0411a02d42c95083c0641d480700041c070b01c80ea038400880b90b4003001c12100c0b0615500c2c5c11800f00d008000048a40c50244034100302152100d4000c00890708588c400d500f20f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 713150746 1250 713149496 713149499
    0xd0c210516060503011715010b09091e130309080d050c0d090302031b0301060f060306051c0c03021e090403031508010e030915120a02130b030915090f06011d01 70
    0x5800314034400303108001c0002c030b0904c014400e45000362903007840760344804211030b04494861030400d403c047c00e81c0990500000001d44c0c0515040002440740d03c003207006101030022500e2131403010300c140c00610940b0014402c4113021b0416008411017000707040e1002c00c54809200c40000605150310000300003106105000700c140101e407145002c08240c0e58040c0140c6140c084c560b402003c1c0400c00c400c040c0d03265486810100f54030b8034848003c00101000d43e404908545090f045c407058a00d80c0080710216400303030360490081084000040d00700ca606880aa158059202103410240781c9180380d950311810200a100c14594107030807090360301010718030140c1e0301541c5440850032140b1844007100c4e0380d041440070982902c0c00342c120b00814100c4501c91407900500140b0b20160480c01c4a4034001a039000c80e02c000007040c501e055001400c00c0792131061460820001859030380d0940c0c01071403281d079843c4001030703800d1000303003c1c0e4003204044004640e80ca58480f64503070484048040607848a80c140b100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 713151996 1250 713150746 713150773
    0xe190e0f1c020106030203030d140610020a020d030e06031009180f0b0903070c0e0a06050402040b0304021023030a0b010315060c21020f0d030b030c0d0c2105 69
    0xc5000059800380014a01c0c425112112940c00e0070340d800500075556109000009078030240000d0110800e0303250009000074090b00381d54082040640054028040020080041c50700000d001a040e80c04617410380300381505180445080400d401d0140d00208048184404002035400d003c0c151407100e102404650390500501d040300400ca080900f1a005220095012907851404140c000b91310038103480c0703080d016407940d1040c00010b0303104803030140c90242040003220b414402c14020340f40072102986498a8000548003d010152019104000e11002e130105540290400b00c11188a0148a41c0d01030103040400e00c0c0d0f4108170345200b425400c04034140700e150721a202c1c0c0c0ba00d9125440b4104410380c03d28100f110300c2220880100c0d0404401c08a211103545d0007074003600810595802022074008102e215802d107008180000107150401001e0442a6004210300c0c900440950303090b4078050807414565650440350740311000c0b0082c40038a122000c1805801020554064001c03507421011509 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 713153246 1250 713151996 713152003
    0x4061503031d032404110907020a0501060e04020105071e02030106080d0318050604080d020c1009120f09051c0f062f0307110c1e100504050a06050903070e190e 70
    0x21000244c0c040f0f0b400b526001c01d40d11070f40701c5070440e0144c0e008021404542c40802c0b10f0a405881200c09640103505d135204026090203060040c0c820781020036558142540040c1142c0030304440245003a0707480110061140205001000c1c41e0340040090290076900c83c03102d5101c88001030130b0742c002410036070822000042d001c8070300086075203e0010320720740ea070700e031103039203480d0032020710103a04940070403000303240b44410400c0d4401c1c4e0228000002c1e021003d441c2824400d90030110703500c03e101100317014000e0160450202c41c00c580c0152117400c801c02e4801201032a1080c1600014201c0d0104c140c82e00a011070755200f070345080c6001c4414100e408500c2d000c0d00c104400d8101c6078174200784c10400036032500e20a080c2c82000c40a40021070b032541c0d1068000650700315176104a10340e41101003108280030302c0c01a03003120307010449003495440c00781414017181060707086002d0b0400b48000010741c0201604c00300080c80c01820b000d9044225400d0100081000c0c5158400324281c00d82000c1d0348158242010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 713154496 1250 713153246 713153263
    0xa0e220b091006030b15040306020307111b01140c07170601080f07140612070c111c0b041b090516030209030a0b060f060c1606090302010203030f04061503031d03 71
    0x15140700120303180a508401a080e110880f681040480002d016121b41c050301400103548280b5025880b4a00030900170080e0703000310f81d0710318540e01c100080380701c0e0a40440320b00d844080c2840e204040401e2885150010701c202c0e03850344558410300d100040d03810198504a003107d84110309558150342c0e07079450790380d84040800146009404c80801000b41d000500315903040302c580601000c5c241003094586120701d0600700c0751503021508420f4200c08010f14644da001d840c0383e0441d80062401c0840c440407070407543c42c19000303180c00d207000c000c9030074048607a036a1003505c407001300d035616400d4070713075000c2409080706a4900b4100d01070503010f0000d240c0203000340c84042c040a001046000015101c1181a410140c4000d80003110750088031041e4894000401d10150800c1c01043c2c03c451318014501c1403101a071241d410405010410700050f80d012080b6a0040c81040034809a030b2a107041c903000600d400c50044411101c00240003040540003200b052416121102007002203154000703158440084 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 713155746 1250 713154496 713154511
    0xe010c080613051506120702060601050f16020d020d0c0e010806071e090906081b06130e1e0f07021005070906050c01020706110705060109060602120a0e220b09 70
    0xc207000c00c025042d00e5440303a81d1082d007400780000d5841080700880c0e400d40c4a0400032000c003c807401003202840d0104a1190440c13801c0ca8060b1400c02c0c1920039071610300646a54400340340071a140b8005543e40d030001c9040c0300d40c004060104940813894030741c00041d0b29201e01507440c0039aa000040005010990a118110035141d082c0040d4194a917203110320011001d036014041e00d0b050108250030b0074030070400a01003520060505540340300e20003100b4450014600e11452042261b8108984203210a4040300c0350f40c1092883d40d12940c411120750186c101154030300000346020869030382d803249030f011700034003264080e2500600032031443c20594074112580d201180c0d08403401c121f02032042e4001d205003043d030400142442007a950700c1c0103803103031000741c640e60f0b85021a00c030090010078066135004201001041100601c0c20b50003039101d94114140c803d00c030030b012584186050107450391407081c08006080d81040c9034801e440c82100034050608038a1549011000a12800c1608545004000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 713156996 1250 713155746 713155759
    0x30702180408121f030c05030c06070804090513050a0507031202031603140c0708030d140925080105070305040302070f051f0207080303070903020f09130b0604110d0e010c0806 77
    0x1450340000102000c0545445120580780c8135103842c2d41c0005203148040c0d031180c07401c181098509070415140040003081240701d00010401100019034810482e812241c000304081143d940e00b0400c0b0b812014001006807139030060080d16000c00102060300402e49100340644800241ca10804036a240500e280c240703203111420380d01c000170a00800d24890143d6880524070301c2c00400110031414690765510002c40356201107240303210001b21740980704000503180341001c10713458491111a5039074046a60518034112180c90041503404602800014000031402400542000c100080082c8000c49080e0018065540007185507803803554000200c0b500100500140104184141c054221022400c82948180303030703001070280c0d01400554415034039900e941041515500511503480c180341308451040468004101b80c14000460314214650007a00f042c5250741c0c0c0c000400c0090000c00d032131003071030000450345e00c040340a1138100c0d090806400b0001e0110600d0300e141615054000d4600591292 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 713158246 1250 713156996 713157007
    0xf0d091d1b0c0f0a0512030c0a030e030d0504151a030307080c03070b070207060908011103010603020703110610290a050c0a12050a030c0c0305040b0702030703080309030702180408 79
    0x1c000c0e08030240150340480d4482d140400c1c0c4851285850700303096103120303160010100d01c001d025040c0107542e140e03846840450315515003410304511510a6242d8a02810f54481c1551114003080060341e80c0498000003c00003400d150808803520120325200c804136a090103000784001c0d584405204203180050011414248540c1c0c0301405600000e03c104110311003030000340042210446141c2c0511000e03005030481c1414141c001300980a81e412940d020303030504891002c031001d20811a41120007074500181c48041d10718003213030040058590340704144100d6041c412040f0500244c0012600c080030101000d5010a141c000c03290201980700728011070511540f20028040e03c000d0502e04448000e4842235400c0d82d440f2100c5121103000307140012004a09081c003e50948100f06840440e420304040070075880e90006e00301c0c4650301940c0e029160100e628421501e04000f0100a1030307001814030b84034a44108803c3c0d60b0b03080700000b40d00c10300e5004c85031147c1c402c103000d0681c0595080a001840d18 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 713159496 1250 713158246 713158261
    0xd0c02060301060f140a050c0f0106060c030c02011814180c030402091b192025090501090b030d0504060e04180b0a150f0e1909050f0d091d 61
    0xc004404d0000e000391003886036526a820030060030418000e445554850802c1d11460b850285442d420008c160b02d025004d10060343c001d034004881c01e0b0706140240020080d440100c1300741403040014080c5580c2c0402c0811200800d401c0f5031044241503442050a580040d080b0101a60a0303030310a45429081011402506151407900c1d8064548440310042c060030348c070704c0720b03080e88044091402d50700405d510100c01c81d030000240b54a400f0b150058151428000c40482d190050913004c2c99a020016065038001d01e6407001e010000c00b0004801c01141d070b990100c984c040c202a00e007141c800e010f200c01d40361a40d80100241c89c20748a290b656141c6000b9080140001080711a1824255600d050504400204402103480c0720342200c0a022175515805224483c40000540101c0d2081d00b26010034024070005004c6035a1003841c8403891082884160003c000a141c1400080c025002d20071150207600d40000b000c3c00c420342150759400c03c03507a560403003049c001003407000340744001e03240001308544 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 713160746 1250 713159496 713159507
    0x90c06020f12190e0933030c040519090b04020a0801050c0412170313020415060f081e0108030a0e030102030c0d0e07050402130f050603060117100306020703030e0d0c0206030106 78
    0x1d094504008810030000320015500170411614084401c1c0034a403103401d50381940c2d41503507144140d451100c10701108000000d8454000c0c8960600841c2e0762030000c1d030035402c0700c4c241c0f8413810100da0040103544140e040809035018100c80990281c044980c0004100c5414802c052240032051525401c0500340174984007900501300040d02d850307404180c1d0502e0b24012138019401042e50300d01c0440c00d00c81d1841888140c86440c2c05054582580110401c0080c0e0400d902254509040c607040c04160784d4028812280d0889918140d007a5188c5800070071502c00001c0180541c800300d444500340500039008050030b17031100b143d8071b1441e0300c0d0038459256103000b1a000f4865649030348080e50301c0c00352520041806c03070700602c00003200c2d41c40c806010007403210900c00700c001903c010b40740f00303185141100000c0c0084ca190004400c181d0201000290b4001040780500003450380f01205642d1b0b48224100280a0f00c1004014500360003000c44140e00103000d0003011003a56805884181141e1070140b06403030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 713161996 1250 713160746 713160787
    0x1003030e01120f02040b0a0f08011401050c0a1a070809060c041a270109050409020d02060307050d02120105010f0c03170604060f0308131703040e0712090c06020f12 72
    0x1980343c00094122103080d001501c090041d46088544844880d08000c0c541550500f04805200c0064014860101c01180350544003400b03090480d0b907141441e004501e8244071a60180091843d110076000403440d4800c2c46028083e50390f20b2807020348407081100d89440742514080404103040208025a00b2041d80340b0315101010713003070b8900703000701c501205212400c0b080114000500341c035105001c0b5a049001800035000a1b42c040210031000c1d13000c0b8103000c0300340c00040d11178040400004e040a2290040780c22104841800f907490b8449143c1038020400207000e128003182c40507841d1706486109817042140550941d84001c50303061014001407900d000076003007a41258888101107401d00c450a08100194415070166580f8003501c0c203007600602d05a0071544010418482d407180c0c2500000c1650161500e20881c4d56203500c8010041d113048122500044030305092100940a1103182025001155642d4090390041c041101102c0d850700d144510314820030405018030003803d88120702040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 713163246 1250 713161996 713162027
    0x141c0b04020c010510060807031521020307030804091d1f2309100b0a140d0f061b1803030804020f0a030b310201050d0902060c070302091003030e01 65
    0x510b000302c030040b45429984101c3d078085010010942c01c004013a031012005501c44841c3c9400c2080d0103c15050010314002ca12400d4008454a03400f43c40c41008805101301141e40101141c010030364918020751550401e20500c0780c0701d85040000d94003000d810781c01e26007950614018114541d50601c59510100303600c01103050096444c0b240d42c02c4c40c04500391a10f10195640c00c5500c0c0c80c034040710528902560012040301d014185046510b094a482c03050001751902c0f103404034400c10442c0c0204002d0340d10ba080107042c40c60528429020b1103010b510018080003140e40403a131254030306105490520700c2e010201c00b41a440d135401c00200b40315001d055003040c4010300314000d4400040c0020220503103a0010780c2d410000d6418040380c42103080441d090101c0d003a4640040d00119040105401111038001c4d041c02000911145c03003c0300c0740d00c0105c69980c01488030f5140c0746045001503490090f400201e000e0041c0d1400300710318902c00901340c000c80380d140d650780160101020044130044851041074 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 713164496 1250 713163246 713163251
    0x9050f09150c0406110c030d0e0a09060f05011d060d09030e01030501030b060402091c03090609060c170a0e040603030203040609090504050606060a0216031b1205250902030c0307141c0b04 82
    0x5400541e0280048c10031003a0554030001501c160904025248585600001600c4c1c0b070020104181c0343c80c81c00c0c4008546007400e201a040c5030503003081d41085212a04564807403030001e0080c4080d0039030f51259503414000d81d902d03a41a0403490041d41201d6081c0000b1705140e407600d00043c280d140c26001080e182c14060003080d9001c80c0000a0f540c40300c3d00c0d00d03080380400c60440d0188000d5520001c841c000b84154601000c10144c1501d83c800c240f0712090030241806000036249040340e020310b508500c040d0380640b0800c80e6907031701e0070000d4403500326018260000d58414000650f01c801030083c0c9018581010281c011f0f0313100d20040081e2035100307100700000c2d03005101040341c241c800440c5150085001d10f9410b005001d00c1840450100a10741092400c140c04000007000b00f00d000490034021041c96100f03c2090702d800002c03014203002c030350040411a00000410640843c43e801079030140f2115103901c00e41c00c0410358003001c2800b51010704101c000f008144614046400e8000c00009039001c0c0c1300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 713165746 1250 713164496 713164513
    0x1d01120e0f0304090e010b090f1f051c050118080d180215031614180319060608060a021c020d0f0507080916060e010503040c09050f09150c040611 64
    0x329819038006078040a0410783ea0101c005c5040c400780030760440840c08a40d030a21900c0c1c98146600340b8440501078400c003a0ba5440c000001116403140c0901500b00200150390380000c214100c0d01082e4025000c50b9a03500308440e02884803812540c01c0210342e40708582d5404c184080064100404403120600c5000781c400000c0c0c0096164a504a050300c420411041e94a1508011743c20600b00120148400c220409141c0300c0310808a4040e5803641e400c0d48903400c2d0b603624042c0020b02d0b00c501c01950b40f080b44e0f0050080010400e141d40644100c1e440706094440951300c3e401c44504034050903400000300d1031142c25010b0710400319030042007001050480068050420200207040703500c21100040030a4a101c240005880100203281540742500d01c214006806c00000506040080f13504505101021000c5010003400b0325401026203581d0390200700780c0c60189050080344800766003200c0e0600031007100000030800f03604168450104d1040c80c914151030710008071000c1050946400c1c1d40d020311a103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 713166996 1250 713165746 713165773
    0x15020d0507170106020303060d11040f020c010f05130b0f0a0603051207150b100e04090b0f0f0702010207031d030c0a0906060e0406030c1203020f0d08071d01120e 71
    0x39050141d221a0b80741c941c81d03056040450352461043c0c00580540d40140108181030342c40f0003121a41c02c1d4001c00504403103460002050103001c0c0841e07915010350010035540800c1d901580718180310b882c1120103000ca9111b0007840560381d00742c1031018169000540003c0d910407000f00c07810790030040d41c060004480b6904d8946a05210480d000710800c9000000c540090104006041c0300c0105149400c02643c0e000070005150341c40000c51550602151510b545c42e00c4d40d50b51b210001042d0020400342107450402c071003915035002150081c0c26809440c0105601620501c00d881c9801d5040d260441140d0761000443d00c08482d00b204130303915210f4041c4910b540d071034108902c0000c0901000c0468002e0610a018110121401c900e5000b6841c04d4020004501d24094810403140c0c10b900500204003141003c030301307110310080100403a1161040000a003940140464810341e529036880d540001e21982c1c80e2800d92030080c2c1c50b4001a59941f940d40c043c0361a520141209009030308541c2011401170 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 713168246 1250 713166996 713167001
    0x50310051b070b04210903060b06040b1206100f090e0414031902010c0e01020a0204020904110f04030201020c0a060f110f190606050d050a030c02040f0f02031017030715020d 76
    0x201d031800c1c83d4205210400c9468011003400c0350004680c2e5118611545000342004400c0c8000780c003464950b410035456464260484011705103446c0760130383d03c0c2e010805982404005a841034042c0748030911220b2058400c001e4880c0880e1980d031003100e181c1c80c08110304010b140140c000d07540540e0090081e246500304000914000c44600e80c90700400086038006070840d80100118000d201240300301c0d1503941ea01040400c41140d044034010b032140700440100300103080b50890a2140840041c941424510040141040383e100f41d00301e604048212080c0080c01c2e6091080b640421406140340d900d442c083c00103200e402d40840c08840c14113500b08205850140b9200c0d1030a0584141c0140c003081c0480750003628050300c802d4845c81c45c405c2e940d0b601c40e651210300d0440501040303600c000401c11540c0d107030480442842801402d1000a8001d0701c08030080d4420b48020911900d010000a4000e40c40000c844482e007a07400603505003440798444882d11010003038000c407140e6082003400c00c0910140b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 713169496 1250 713168246 713168257
    0x5070807060b011e0806040c0e010f050c0a08040e09012f070321060e0f0108210c010609060504150f1206090c0e040b0912090f0d0b0703051609050310051b 68
    0x159280d001754204103080c04100c807501c003000c44c10809030050000142e40c00000f001100d240b90b1900d00e960f400c00d20040f40c181495030074010f11000d00080c0008103041c024484034010305041008102904441e4090560b5403551481c0200350320042d1001d0048815280107424a10300a0811504040e1038408a0030403a030f4080b04002d64a5565800717000040c03106050984c014403040031441d007541031154065480c0304c0344107244600c41c0c0b03802501c1075140c1c6140035114060011130003408103036103619004002e06054010b55001307514003103100c201841c100f82038800f2144212045e6844c1820720849840003100c091040d1080b548030300e1648005800c8005d494010045070b605010241401d09d031440d9a054050042901e5520030220401514908022108032034403c80703800340482d0150f40401c2110807164005001d9001c0d40042003002500740c1c21091082c800703000600ca031403c0c0a0016541c1d41454018587c0603404038100c40c1c0050441d82c85280c0254108003040f400005540100802d541714 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 713170746 1250 713169496 713169557
    0xd140901050106120e071203021e100c0c150506010e060d0b011808151003120201060302040e07060203120c130602151e070309060b10050c0d05070807060b01 69
    0x1141c00401a15901ca00150075441890b00140200240e0b41801a540c0c9003c0c01a14089421400322204140c0200101c0510941800340e60720880340303880c260fa45400040d108050b1031400c140c542c0710598410180305000c10350168840181c2c0012200380002000001c0409041c090b4002c00072940b55540000741084071500e2034041007190030f81e0001442515a00c5080400070742d0102c1c1400f00001c04140482d14001c2451030881d15502e1812416441034160b02c040c0550110005803c50681d064000c08107590082d035040c41900421980b85a40d0135140c03186800681090002d4000509422a0641c00440d0204003a0500f01151884010310030316504c500f01517031228080741114030b000b000e607990004003081000a001c00c04401c900384008010111010180c1e1008a44100022503010030003511002d4103000e001c09110b10060702d150300c107803442203d5124450000207094851011205c0300e0340d0140340175003400c2c0b0720f41d5102c0140905101c5e403810300c9100448080d9404070303d6044d6000200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 713171996 1250 713170746 713170751
    0x30a2708090a0e10090903030f060e1b03090c0103021305090c13080105010e1302031c0e0312030c090d060b0d0332160f0c0803130603050403140d140901 67
    0x4560811920b800c1561201d0840b034a09400c1180100d84040c248003110039142002c28050031a1030220300134850700680603100e078500840851044000d0011510405208034031000c1009010132404081c0402c48541d685a408011a580742e5403103030700a04403a55030707101c810000680342e000241038000c0c129a9021034140200e5801280c044442e60000245843c00c020099941013401000e140e100c02481d0b03d41d0702d40e88083c0003086403420024000741c0d41e124011035007104106840189103c40c4014072900ca4480c0c2e9070030034940b01d60f40040302c1c0109240c4109a207043c01c808103004690001d2541a1503090340c1e40700080c01900c546401e00b07059403280d50355400c110305000da50105031190302141e5051110014000320346049801c121541c624a4040d1894007040610709114403003a031000c01003c3e25103102c00001d481d203000000d002541d505024420456483d0001101100c40032240030b400201851103074014403140d10010030311184401e4001c90304c0091072a450000c0c04041d66540c040e81e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 713173246 1250 713171996 713172007
    0x2100c030e0901172107230d020f012a0f02150a0603020414040c051e060409020c06130b060907050405030105180d031a060c1e0109020a0f0b030a2708 66
    0x15090008a2034042250384460405d0b50040f41d0028900404000812103c0c124500304003c3c0910400c42180000e84003c880f07613924068002034655028500480840d8200300315640042d42401c03898800345035000400100c14008542100d007081d410340104154050317807400c0702681354906840380c4113800f508004a0090314610501c01114000840b1207002c2140009000001d80d040d240b0340c0440c1c00844400b0107a41c600b520301072110855486c0c4560020380007a0015001881d9000342c5200100d40b03003510000d07036440c0322900d280c0d40d050000504647c80d1000158592a040c1c207182c2d000300c1da503c0e1142c1000e0f20790000c242143d205588500980143e8841c0c4010004100301141e00d019051509001c1e050320084610640100d6400c0940b2400004c68100c0c1c0302d910401840040784109030700062121a15041640281034108007a4020340e81000045000c0394140c021306d0441d40062025031031980c8504101d0004d0003000300d000c640140302810603000c0b07809110038a41c050300a05c4440c1e5204d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 713174496 1250 713173246 713173289
    0x10f0e0609060a05070f11011e17071b050105010f05040b0307121b06020f06100609141206190f02030408030a09030c0b0a0608070806061008040302030405182202100c030e0901 77
    0xe120b0940031118070310031400c0240c9100d600c0f030420001d130918600032901b503403120700303013a0b4444001130000b00c2d080ccc40c0030810f40140081508128103c0e40000e10303800605844a05200c2900d2041d00c11070340650100d0000c02c103000c1f610400072610ba024441d008190308000203205a0b01c0d07c99072022005901c00250724049260031300c0403a4012008400407a10646024006030008142c0d10902440d0144d2484660381d0380c84d807404032600d8442d900c056446030326040c0c45802d07420729020644002c540c40d00510022a903014400c0702c1c043c1d500a9041415035603004890000b82503000b4080301081000c54038000080c020380301841c0511030032400490501d0802007840e24001141e4024101c90b0b1040b81403017150b44a284034540d9038061440c2c0343e2925500c50905078030b184520752150390000d80701ca50316203000c10100004ca026000d04041507085051780303400c0c010501c1f00808044d500144404201140074002c0c0d20040d2264402d0400ca001c0d2410903000030903d10090f8844102c5640303400c02070401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 713175746 1250 713174496 713174507
    0x10050a0308190e0919020c1219030905151906090b03100902060d09170706020417010212011412010509030d050702070812030c04050618010f0e0609060a05070f1101 72
    0x81c44862601000450401c00002c8130808050250700210943c02c2403011100442d80444800180c642c048500103c00c0e48040385c500c0d40451480040c20810902030001e4500c28084c01d40a07641000c001c00202441c0c070b02500c2d04243c06015050014944101400d2310b00e918061130000b800348000001d0700c89590700c241401d040600c244010070f24940a0094016a55202680c00003181003000180d240e25500c1c4c006030102c2c0021b00003280c24004a4000f081000a8000f80291480340504042c00c3c07650040c41403c2c0d00541d61203100c3c1da0035020050103024000100300c03401d20130042c85071102019210300c603401c44078140c808001c141c00c001600d8981190714060150060401d02c02840c0d201d140410b50342d01c800ea10400b1082c07407000000421900c03010602500d005e004000c00f01613640b614000c1040c04000b201000c10f000c98030155401c2250b6000d81c01080c0341002c0075060760300d064100381c10803040c1d0384401c02c013401303109d000e00081d8017060030003001c00d100611503001c8449011130340700003422 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 713176996 1250 713175746 713175787
    0x30703061809060b061315090e040f0303152105070909080c1902090a1802120a060e0105010f060c050106032f04053c0c0a030e03090f0910050a0308 65
    0x245c508100858503014000701030300c202d4034061800701c0300d000050021200590580e100144c0b0070b407000b082c4801c0c8041403800d480f8952280e00d00f04400e5800c0b82215045076214403c00311252406012040c514943c0040030b00c0c0d05100300103581882da15000c400341150030140c4140d619032401f0a4031111174204009400381340340009290b0082070301d680d0000b140c0000003810641c030300d81c4a200b022f03c1c0d0120360540041c603c0d4000d101010100c04a000703075580d01c0d05000103441842c244001410442c4040c0f264906035184404960784d0070341030503402e407100801030311304540641da507100c0040031440c24840090103003400c800b4080c181a5440c00040e03a400e403180c41c00d105030310f42002d020824081d2121700c003908a511300d031880400c3c0788044480c4c0e601800c1e03458040c51503401c8100f102c2c2501d031100070320301c500311f0b510100100100c40748102c0d50b134061640384981002d01d600f0700440610302040d5107940502c090602461179519180450a106480e174422a69080c001c6241e80300300080f00c5a00e103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 713178246 1250 713176996 713176999
    0xb010e0406030b061e03030a0e0306100503030306040c0e1302040509070e0d0f050f161a03010e010303030b03030c01020d0f0b1806060a0c0f200a0812030703061809060b 74
    0xc0001e0070b5895495902101811880c803800c1800c40c44500140b500001c0f280c8400e000341541e8440e0341880018040c1002008018420300480000403480101b1510718026680050000c0d403c590b03c890a10000348041c00c14801803102001d04020640e940201c802100e554403036000d82c48502c3d020906c903110401030b1840d010711603942ca020440340c8500f00360314003030b03504000405698000c50a103241051041c11640c3c5c0903000b035540d035048400072102d10b4022102803800701d407010851180d02c600c150100380103c40b04000c0180041010900c650017401d00003034010182c0c1e02e8031000c0028242240c1c010b00200b40056128614049103410a02c6283e42511341a02d10100092641840012142c1c00504a9108900108080500a1003a01c031040801d621005200a160460030041c41d02c617000005015001500e04c40c1c0c42840c280b10902d00700702e40100000b0007605204060300e1902e40c100408a4040665480000a03c0c8500f1102d00d00301d080320081c00125407609007004026180c1140906 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 713179496 1250 713178246 713178251
    0x409050c1e1215060904020d0e101802061e040806071d010e1003110c070305190506072105150109090204050631170105090a02010806101707030b010e04 67
    0x10b0384031110820680d0720802e0100b0900b600000307480040c035a4021041c00503040341c400b10f0382040c40809603008550780b81ca280c00303d07034902404d040110190707444520800c0348035141e40c070b1080c01414250040c00e221150214051007060b041d552030301c541e801ca980070b04d1499022005000d00640c00c6070324490501e07068520569075a0f481800030348072085402e842070007842002840412184039511442200e0b500c00407203035444282d412529581d50581c0400e68480c0900b640600210032800c00c1c44032850703400fa000d01300c00e948052040c1c0381031001e01c400381c1c1440b46100288114001d00d01c600e82c4907486a804e012048044103000500607080754214014483c0304000921250380c3d41410390704d842020a5242d451221040c030380c66041001042001c00d60050302601103099907c0010710a500102c55000300615a07560700384696031904900040e01041565010400ca03040450400301d9010090800001014017000500d0703a129040310b408000a80d10045002c596071b20424500018101b00c806 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 713180746 1250 713179496 713179507
    0x20d05071710060f0f02070803040602010e070e060f060a02010e0303040303050a0c090503120d200301030219030c090203090313030c171518070803040801020315120a06020309030409050c1e 83
    0x742c42c0c020304d84211003c0c072560101c0c500350688200545800f8000d400305617030321030b540c440010340078044510246003117015a80022980311041c03295144100c0d0000c000280000c440d0060084c0390340a40344000c00c55480e18505000c1c6602040154082c52203641c0000d69890540d2446040f5064406003000300a402d000420003039500040c000f40f103058400ca070590b80d00601010170001e000d1141c5900103608030003200c100b00c60116003d941201c2c000e0700d0322840311184c605007a0450105001c02403040d04203070401d202c1015260b0103158030180c0306e801c130792070010300600b4603541c1c010507401100ca80340050381c02c3c4411181320740fa909400e03058034002e00007841e462090010301c1500400e8049060100c42e030748030001c00b0410a0300d004091070025240e03902e44962049010b54821a01c00441e0181d1102000540c1040e034200c009403a880009400301107110342c2c82e02c01030f5002400425285c031013440081200c2002e0b11400340681e250340c036044c2e07843c1c0e410f070114203105616820088404005202 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 713181996 1250 713180746 713180759
    0x130b0604020304240e0f0105011502030703170a0b1f110f0309040b0102150108010c1b02060324130504060e2404030903080a031505040204050a09020c01020d05071710 73
    0x3913020060048102210354950601e2410010030030000300c445188200c0300d0144c88030300d044d8405410f03204c2c0045c4c102004891400700b039a40f48a000c40c01000108181e0400800e4000e484240d50022090fa0700458051032143c0054001e180c5451400c901d15103008110315225044030b80010b11000300c4018003494080c01c90003546900618410f240a50740b01c03158680306030b1080c8030b0030b01c03d419106030103006940c66002d118001c01a801d2000003140314407080000659503034000440540d070040c00c242c80d554810707243c8542d0984114402c511108036a04944540c0d541000000b44802c02c1c40d0300055a05e0706040100585403003551444668000008207100820341001107500d07012241c0603101107448511303084413511419403003e0460170011030714801c0310360702d078112040d61500e140301d00c1111512801000128440c9201e6035600c41180002000740e0381050300a85441842d1800043c140011045035a05981084802c0c0001030700482c4080341d0100074a40300d175004103601200400b04c03401e118 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 713183246 1250 713181996 713182013
    0xc120403060b19181e05041a090c06040b0d06090608280c063509100e0d110a061a1f050405060325020f072306090315130b0604020304 59
    0x130200c041881d15004024038400200c04a101c03402d0110508000919290a10b02d0700d299000f08510002c2e0f08460104a21100003d8050306042c0000c1900740341030b180103a0280a54401030380100e410780c8841c00007030100840d01c942401408050013424037618080e040034201d00424114148a0801100300c0c8045050688088284c41071401d05c0c2c142c441812880342d2150504920440c030030904a1194000c0d1a004003885005140d004100c0300661f200100b140d060740e50103c0c00c40511f9000841400400344a580742000c0355a050040e125031310625241c00c010f861240800142c9032004048410181c00e007240810031605144201411003058024010003902c220310031184101c001201180b00d07011000320603c0340555240042da8402c43d20f010181d02e070383c0102181c004c5800744201c0042d8907030503031200e41c42003c0244400d008074500034003005410b0300520300c400c0d003512520b03001050070401d001030b00740101c4001075280d0342c2c1002c0e03280c035940c4040d00515460041d8014410b200c00600c800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 713184496 1250 713183246 713183279
    0x171306091811160609020f010e01081f170d0207170c0609120307031205060a05010c021003020c16080705010504030f03080411043207050703050c120403060b19 70
    0x111000c01c2c002585414040c00303000341845090342042c40d045103820404503621088126100780c4005000d070405500540e82c0c002d104840c1404076001d800000d034140003c052000c110154082400069501e035005446030351203062214085512403c54520700d140c04000010081ca94030b4135030040d541404103260780300e02400d011103004244c0450001000e6a0341d803d4404840080d00480b0b40300d12031414000e0401d462101e030200001c0c43d01001c070b002410028179400039201c060b142c6400008059083c01403510302c0ea1f8010080660a01100d064001c050108802d1885120b02c004441e6050107031182c1417500d95402141806001c000800c0020f8107800203881c00c80d050708010361b980e691400c2408010300d01c1c54240f54080c1c40e000a00507105d2400408040f502141040d07804103544a800080c03001c10181c0d2400013095092222400092050008116106415059801c2c10301550000641d41d001a001124245d8403580d004c0c0581c284840f030081d91302040340d02d4030381d103900d04211350960441c0c5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 713185746 1250 713184496 713184539
    0x20f2a160e130f08030a15140d021906080103030207081c0f020c1002160e090a02060f040807030b0a1a221b09030b0702010605011e030917130609 64
    0x70306002540025503940740080042d003080c40101c981c14140b814144d282d00480e43c0240061900403290003000b588180c46080c1c400c0307900012000c035444410007000409159040360300030151310304d4030700c9803444806120042000c1c1e1250341c515415494003904001d0303550032104e1076904c1000708559001c0c103000400c07111452401c0521071352940d07003402c90414104010958201414624168805500250b10540106030604040046850f0303801e143e8544001d4a00c145954400020540035103030010003084210a0001030b18a003654a541d0542004401d03803060ba4060140b0341007041031030003800351011f008020f0300410440d0540000050521250707a80d054460f464450104040b0090340d0f009100b0342c104c242c146403014107009401040c030a0f07203020450b901c4800d4070204010380c0c014001c040039524140c448210304140443c03000703503400c1004502804c0544800d40c45001ca1103d4600e0034400c2c485001f16692001001440205501d2135403140040001c030450400c805149240203400d00000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 713186996 1250 713185746 713185769
    0x80c240f070b0c0a0806101116210c0302041107170307031802010f12060e0a050601030b0619051612020114100608013c050a05010806130f020f2a16 65
    0x30001c044408c048002403070310f901c0c441d1031412076a4106909002e02103603200300e100456000702038441e40309400410b9004103c0401c0c80b8060006140c90340023141c140b01c500c0035140c00c14203117446114070050000441e1481d080700109212101d0340c03501400c1860008441407008813002d643c0028054070325100c2203c00c100da9500c8281c0718011680205c0b0040600561080c01070418020b00b1004010035144e00d40800d10304951a6180e0a01c40c003594500301352511003030705080000806850540c0400907a00840940402039000102e00101085518415500000380b510341c409004080c110060701403001107450b0081040035540c0451507605442011b03280449584021880c0e00703c055002c011440008030100d440c0c2040d5100d01d000000301c2c0e03011500407030741e56500c00c015500c0c3c01041c1c4c0c0d05074100b9a18942e00400300a25044074801d01c3da00d9000516061515180100b2a0043c0540c0940c03100c0b1000f007480915003c010803107030060404040c02e4001440307009050024950300c1913014401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 713188246 1250 713186996 713187019
    0x1302010e100e09060108010305150703060b071212180602070f0c030b16031a0d0c0803160506102d180e010510080c240f070b0c0a0806 59
    0x9115140118840d00d01900e403201c00345525501510b4902480c01050080d110640015044e40c0304265990480741c05c480500b000055000c030740d84c08004010080c409054460b8400100025488001e124881c00b40106074110005104001d0142004848803240e5506107001c61146242001103614215031290006039034011031b01d84084035100d20807001e040300d40594400010f00104810712442603121850194000d0402e0606034112180e040080c40d0043c4e07800c11504650528048003142240280741407104607656240030b500e16481055030010070301e01180040700300141009103c2d04a040030704e40d54011030a100403103030740000d01d0004084400c0b4404684c031010304000400c03409402030400b0003e0080307840445002801c0b640c107207040e076903103800c00140d50315260383c9405e41030380c4c80000940030103210342d01001f80c05010845860310060ba09241142d00314140401400740484231045035440c0c81c81e84c1801c0c142da21000308008429803082044411096100402d103500c03000858400380f085 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 713189496 1250 713188246 713188249
    0x31104050f04200405013507020a210f0804110f0d0804030305090a080109120f140318151306021b030c07090605030d0503041103010b130c0306090e03031302 69
    0x2000c1d100420940f0800e0240c1002840c10414020b105866003030b01c40721500840100b001c50f41000c13105020054080c1c2c01c28200001d2101d11703107280c104009104540d4030010b00d4030b8100301e84c004100000e0002e28541158440d842e001580392800e0746190410540034500741d1144140c11b19010f5a1500c034540c02402004223135244044800c010360811035490b10356499150140140d884650400c1c230400c0c0e00f1000141042050084904085c0d01c01403201f100201601c0982b444e40122008500740105002042078907440f41d400b85111b00740d845015070807a103e000049040a03162005c1c003602d00140d108200131005070481c07044901d580200010f03558030310f0032282416101004c00d1440c641c00001420b0054900000c3d9800075140205402c0140554403420903941f07036400c450030804903606000043c003207141d08510828082c0c026001080200b007120000b0641c66400c0d04c0f4000c1d890795070395803c0185505205850191102400c10055807850070041c940c0c034040240704440f000100c2c2c641c2d0046 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 713190746 1250 713189496 713189501
    0x140702070f0b0304031b0b190c0f030504153e07031d040c0804120801080d05160209011d070203070c092c011d0d1707170705120601031104050f04 64
    0x1011030440301b12950300c206191041303e0b9542a11100b8081805003a0314060101e10310829102a2240c0c0b01c000008480700320030340c007400c0f000b0026920161014003980325055180282d002e011104107443e07a403000324603500000a078003080588089a046040d030048101014101d8140e281c00d824845240902001c030100b032515400340041c0c001d81442d412004094201042c81e0296100303941c001c0300303442106001c86240c03000b44940c0420b1b900213081406018054401881d48041c40c00406810100c1364011a40104c4207a01512800e0707184840e800c010050790003031580201651001c0c51816500347c0311018480303c2400b50601a50fa0f4056503118072040f0f4940c1400030469950250000c000080d14500a10b84031111080300b00301d003010001d26020100e15050304400d961201100b85d0355006101c040d01704000c0c581e8060200248070ac40d400f0716004001846070f2080e650b06075a46d002441003d101e030b40d01a1081e0306050402c0d0220349014580c0058609959055464076a48452080024007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 713191996 1250 713190746 713190767
    0x30f06020706020f03010312030507021b030307020301020a020312011e0302010f0e04050103080d0f1119050f1303110d0b070e0f0a03060b0a0e041e0321140702070f0b030403 76
    0x5aa100085040d180411034005c1c6040f40e01034801104030000007841039081e031b40d00310394140050301700c03256100d5004201c2c3e2800142d00000b401f103034100702603580031a08980c0034138040400b580c0007180c07910b118620f0034081c60141420b0902820005414500d8100c00100c50100a041c4503d042050308024400c401c2810345040052040c0800d5030749003045607655001d00b0ba400307202030804246c14040020b9005030320141c040c4554041c68a82d80201981c07008181080380d004101701002030b0712680d6190300207442d24041001c00c18590a103140350441c00d142101031821300421804240c500410b01e4602c207140d0001803401c06070504080100000c2e24400210081c0754440c0f08000c2c048140061a4003810b040171069424512283c0c54025500309030030229001001260114840501c003144000c1001525100703050250184901424124406078000c1f40d1907441c0c1c0d079440b0045c0c40c01d020402030f55004291800038203882c5091241c038504203003d90040c500c594400001060030188101020f55 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 713193246 1250 713191996 713192003
    0x602031306180615080307120c020306040c1e0302010c0308060f0d061a0f03120f04030c090f06060513090e0a0b011e080c10080402120313051f020601030f060207 71
    0x1064402c201c0c0000041003400e1030656102e8901944581e044404c48000000e50f203e8400460520705150394100d1040609500c0c4002c02c84904602c4005032410400213018900c1280c0301c19445081800b0080074040014a20108422075038040002d40d03040340b01e8400485d0189001012580d131300300841d07800365011219075048120040b0b01d60510230a42c0c090607200c915060300c0a106881901040404007090b002c1e160300d604080564251b081c0080c2c01040c0c0c203000c841100303080c00e03500c3e141c04890206990010f081c807522001800c4030924a8840c550180c011402e04506102031000002800e0009009091407217559841c03080b004402040729400b000da001004005075a1185810030804502c58103409042d508403502190b81030000c6003130412404064213505420b4100d0340201c49103580504241e800100c402c001c40f0a16038240001c21350300020040c0c4d400c00034a004140803540b070b0074000207896a001c403058806c0940e07000c290700781169048880020842c0e42e5061190080c890360740d004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 713194496 1250 713193246 713193251
    0x17100e070e01020f0705010906050c0115091409120409020c07050d060b090708070c06052203021c03060f091116051b0301020705101e020310141206040602031306 71
    0xc001503109105680c21803081e400d44205101e000c4c08503641e4209030245501251302e4480c00c2c484603208002034038049400d0800070401086000d008900c1b082c03940c11400850b52148480d02072203025011054003c0034034030051084034400c2c041c8480501950003006007481d000591000900d100700f21a5000c1c182c004c0006c074400e0641d00e0710384c0c01002611842ca018601035000280c401c0d001d020118442c0344140ca6000d100c260360707507811000b48001865410501440e152110f03174040000118095144642c000341310101e54400c1c00c0c9503e18110f0469030406003001c100344500505560b0100449260310030200b40d140a031003644419000d03581c81c001e0074104030306d0480c3c14071000048005030840c81024a0845001e01c405044c281c2c45018000f40098ac8680900c0f070f000301d01540040c0d91200440e0840340b102aa8070040800d82e48240d0b407144940301022030500280070306249441040030102d61140100351002400c1d82c80b2000280041e00c0f4a40c0800092500d059030301c00c41c20310070740c085000c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 713195746 1250 713194496 713194501
    0x180304030c0b03011508090a02010c030c05160e0c0703020a1103191113091110110708070f08010b011202130e010305210c071412030f0403061b17100e 66
    0x1019003500248900d510741440c1440c80d031441c0b4041c6c1c6440703000e83d0821018142c184281c3d00191803540c0100c0b0220f0400140d0303001400821001c0c444c05440c0c08001d6200303507840b45000f4034000018006041041152001c201c880000390700012040b040c26404680d060780c1038a104002400c008410617a410714400341c1d0449402c11121080350503000340102c0d2440d810f1098155000300f210700100300101020300e040340820345403910701c6004100072507d00c2e2090b4405010110941001000d41c0000716540c0b280740d041c04000240000000074000f004020084034604100082459028584410f14941d000a954800c0030b0340c0781c1500b010707004900d02410156501e00d41107940f00d504014402e8240d4003484001c4042c08020100c0d440e0075006401495003508080980c2c88014001c007805510182c0c2d40c498201e202018800b403c8890007920742c041c3c46910b14180041035818240c402841050307145841c0c580603400000c0300c1a1110782a090248a5941402c2c040758040e2607042225000421000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 713196996 1250 713195746 713195759
    0x4030203070c0e100302060c01111c050c030906043908010513080a0e03010f06090e0d140d0b01111b040b0d1a0705070b0c0d060b0c06180304030c 64
    0x1822900d00c541e21070142d45030b80b85803e94601c1c80c140d840429020310001c0c10130141c60004007078280d65001c10000941c2c9c4c80340030030042c1541d00180c0c000305134562006800c480915240b00e041d6229100300c55052852604c030030955202c02000740002c0c0507804d000000d18211030710001801400c3c4880c0c0242c440e0380100401c099003d201841180150760901c000580c0c03c94400c0243c5144a0b4094442802c2100b40c03401034800c545c0b503040315601341d03680e042e10bc40c19604031b010b08001003141da02d0002e83d42503c203803a0b40c2403c010360204004c0c0300b01d40c050700904000074812105e5228621800250f1009182d004803540190791806034500c0c40b031006001e01071000e002a22510010840d01000303000490380500ca0400c5402030003401801201e6168400544c0e10403815600010364a000742c6080003641e1241e4881c407040c0c1c2c203550800c00c003107a50856005188100d02c084c00c01c4c1d0051f1814040e001c50150ba59a80c000c0102120000100506414000030416035001e15441016410407a841c0d24 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 713198246 1250 713196996 713197003
    0x120610170a090c08010e0714060d050c0a0311030412140910182309100f030308010810020313020f0a090c05071203060e04080711040501060c020a0602010e070302190806040302 77
    0x141d043d50400c01003400018004014403a044d1a20544c00c05480000e14048244c8802807144a9080c0c10075000c218261024040c1d00c81c5910803c0c200b0f0b07103030351500c1c2c890700d00070119003515400303c0b0031010810511001c0b80b42c18610f842c031203085142c00701000c03084140306280c6006203c072854002e243c0c03401000e00d8a4107c51000241c901c0c111440382400d030307500b040c2c80f00c0c2d402c03045403071010a20050801c02d040c18000784043d8840c0c52075180072415035482c1c0d0b90005c801403c1e801a0002601c1a0050010480074440c1c0c200300201c1078025401c50600d41e5221310ad00e4190007009203d400d20034148016512a10036500042c88420410003102c0d0300044050243d80c41103000301d900c5e01a00300303030780d800030302a01c20001920a503060f031484960340d030742d1122038591240c1420b03a48040300e00e03c00040707696240520360113040d0a0b81e81880980d01441404203140c038032b03002403080d6410203010606240000400604032030701103c6241421800040d08000011980c00c107001c0b501415042005040d00003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 713199496 1250 713198246 713198261
    0x23070210050316020d050708030c0c0f06070e0f0f102a050c030321070507050d0306030201030509120f220312110d05040b220e0603070b120610170a 65
    0xc0c0c954003d000004104076203c0309404035030004a2428040500410144000703103501441039102c5600d0b252002c01d103a0b10f081200744244015911200070060b05aa0004010055000c1a1451104e955001002070f611105a8400500405100707900b0b4500702d200c1c0f00b1864010782800c0506541d1061809500342209001c1d01c01d440c14490311700882690f04000040301c0c91008071290784400c0780104200105042000307400c40c1c0030404240320306404a1000e00000740300442c1514006869481c602c0007401380e42005000303028940042441d4200c0b24038130305c00c581200030303403108043e580ca40503450244010418811000d8a11310840b0100800c030044120882911903526106200350040708100e5a074004000d00400040080c001041805e001c2c5001d011b04103010340712821a001c80a08180141c1d0840e44030310b032202c0c100c60605c000e5042c1403008102522864910a2130311340e10000c1d41170203d40143c451805607081aa507654400d1046580901a21002c01001d02504010450502828a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 713200746 1250 713199496 713199511
    0x90f01060605092b050c0102240703180c08010501260a02010e04021303050606151303020d150c020c0a1406030c070611070f110d022404050a0303110f0c01230702100503 74
    0x23000006030001c6200009000307020940001e9442e05d03984c40d407045005e00403920200c80720301233800310900041d0321084654003401901d8000105580741107159190300b01b10003880a0211904010281c13445808211282490340a00b050010b9041d0300300401c00910407202c140c11a200c860303001100300280410000d010b10710032100da10707503070002407082d031100d21446022118021004c0420001800c1c141402a225401020302c0b14001801402480580d4415a001001030300136140c1200c1c05d02e40400e00001801d01440001000c561800225050b0b100c0030302032802c081000310b540c10400015400c28070b065400c910300c1589440c02482c0030301004544590403078543c101446002a1402d081403100780a42d001080000403081d0819101c440301c50100744c00c1c0c5410b40c1004040349680300c0f1003015000314801da0354040f039040c0035203000b0708015131070b02c00c03404a800495480105a80c0503000656080058440c9013407140c020641f0085440356510080d0020b50b440d6850240039000b001a5109864 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 713201996 1250 713200746 713200753
    0x90608190b1507060b090601140d0e010b0a15080109420815090604110121050106020f100605060a050d0213030f050609120a201203090f01060605092b050c0102 70
    0x300c250040d90056009015074000c0c800c01d000c009040601600803850901740c1600010b007120dc07850102d420844070783c0140055120414141c5040c2d94000c080c41d00404e1404010005505805414038001e0342d407408120301542d81c0040f10449000d000ca040c0c483c06e08030b80941132440e9031a1101e07a00c903441031040745030580c69680029088000441e0302486258007082c0c400008000f40019640c0d0108180c082e40051015202400c01160504c03c89018005a13001001100c0c074807946149451301c1c134000c1c034032840c1c00e000d802c02a685a08041d1101c520cc18101541c4942d402c2100200034051415203800700090540c000052080c10354620316001e0240d0143c405954994904270f544013a0540c18103401d090422a082c490740c45904038014802c0b2510341d109804280d070b80070500c2c003041c091284118140010901c1418841000250503e10302d45000b84146840c00d0703009803050044130780c0d0034000c3d403000804c0c4086800b0b50507442d0900d2a0303200c1d00100480a4240b0540d02d1501891740c502501c03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 713203246 1250 713201996 713202001
    0x905090f090f0c010207050d14060702030408121204020609010507240e0303040c09150b030901050a0b010c050c010c080417160f050616060902060c0d090608190b1507060b09 76
    0x24404075510f0040700c010b03002880d6807841c000620800c4411400140c4074001c11290429000009211150144159a0045864506100361203050075121480d01013070306801c00c810611081c2811900340c1c0640c0442c7d100c0d84602c0c81c280143d806109a83c00105030b0030102c4c80640da2010940c100c000c8007114036104000901d0202c452030759912081c2c60150060481c41d0702080350242c6604520700284503443d481c0d0045503142d00d80f10040c0c10698070819141d45950801580c0d40e021320419110308024030706280041e40c0754840c10340700c000030301c0c013107040200030b5503000c090003280f1040341c0003404200342041c1540d058005190700c0f131007001d5a0040c0104c030800002600481103103208183d62006000174a060f0300140041d00c22118058101d9285403a60a041c000d65503c01c06001070f400c4681c0544540d81034450b006241c2d18094125009120240042c04007044d0485201d40010007045c0f80024000d20341d000250010001d0700a400c0d034a070001800004100b681d80240c1c205a00580f0006584e8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 713204496 1250 713203246 713203273
    0x3020c0d0302250f030302070314010b090a020a170408130e060a05011110050c030114010c0803060609040b06370c021909020d0506130e0613030905090f09 68
    0x1039a008003400590001410040d074107a407a00001d804200115200c020aa540528200a1907640d00070350150f049481c0401c00e014041a0030b00c00c52003010000c0000185240020301a100080d050340c03d0300b54042001c00d4500e000b490141001810094040520700d4036180140269200c0003c010303000e02d000c0400034100c42240e4415010701c2004040305c0200d400c0800464044040c1c0706078030428071a00301c02c0d010707129040c41245d00480c05440d02c25600d60510480440781c2402a07500c2d0b04000c4580d50820100c0d00d00015250030900446840c4c3d614030035000050041c0a04070f1240d85c0c403007c00030380b4030356503412250151404000b185200c0004000091003543d010030107001c3c400481c4a01c1c42d1200140b5200c1d0b110100c066038611040006a103c07100c0b1700490f0072142011000710f5a80050150503d003070a40c0900120003000c0a000d40d0740ba0403030700b603241c6902800e41c16503602d800c0d44510030036000d150388d079016010282caa20524680301c2001148504142c40c55045c1d4003900c101400300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 713205746 1250 713204496 713204509
    0x2090607080a030e0c01091a252003030403060e010f0c080610020601140111070b0d0609141e13020d050102090406051c03080604110a0305040b220807020d05060406050403020c 77
    0x2816416196403541c7e510301100020182c1e0790a00500784441e08000440c044990b91b801c2030000580d8810381c03640030003d071426108440d502080800e40240281c50b0480642c0c000049406807a803201e03000c140d1409c1c9502c51805050340700340b503401d6039081c24244012668408261407051034116600f4540065107001a6200d43c030a00504c1c0084102d450400c1c0c0c1303540545440c2c8078180b468801c0f0341540e0394510700205141c10007000500081d44400041144076140e009140102840c3c0c11145507030309101000d03040c00206260216000c844c20302c0001c490130001e601402d40c1c05d170054501c070744c0d00e005403a00301d00030f601004d00c652141d40382030340102e0300341080d610300042e01ca240c1c2140550600ba544003540c1d021401481583e110352507155110213800144058410960b41c2d440c00b040505103454901005480100448815000d176070391340b004885d2031010249903d0704000d41035940c801500200c0c0442c0104080600750b441520305001c00c000051f480f031031180d40240d080d00d50224448040100 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 713206996 1250 713205746 713205763
    0x1e15021f1802040203060d050d05070302011b050307110111040f1503020a052203020d05010f05010b16060e0a0602040b1206010c03080141010e0613120602090607080a030e 75
    0x70000d100c0200005040070303401135800420090020f155802d42c0c2d0b0ba494540380000f8030050014801055441c1010340901034280d0700c003e001a1080380404400d001400c0b80402007580d401c10080301e60030b0a0100b000c0d400f545d000c90065105590f610b803504415203003e800c3c1c0c80b40b80009010029200300c50b501c03a20076a0310044441d61164900005103030304012900a8a1889840b103601c0403001005030341d40441e4040791031081d0004900300b51001005001c40328164400e00140d401005104000c102d5001c0f80007510f40e120bc4006042c52020312285e140c031a08210007025148001000b2504540d504040d140040481700240740503513030f800044a01d01200c1c800100030450941c01030160004d030780c0284c0c04000900940306600720310302907400304d400c100c3e078036100354a00480007007401540d00c4110482c0c403a5050f12120324003c0c880714003003050000761103031032800d03520001441d042080c0d5130122180100000c00781c0341c450f440780c1400a020b40c480080308000c40e02c0e140c9400007190004c1034070302 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 713208246 1250 713206996 713207021
    0x3060c090f0f0b030609150904111008010303080a020c01020d05150a06020703170a2304061b1a0c0d061e0e0613021e0d0b010206011d011e15021f 64
    0x90841d1100014001912030162840360403000161003048103888c0d80070098422401a5018602060700c0d02c144600d0802d540029402c10100c940180003003604400c4241c0c00107040c01006079281680b0702c2c41030080c0216010917601a091409001400c40403021140d00142c04484078566140da03442e084e41e03100341ca444002d002c559102020a800d02d12600905940386503802d05003403c00c2100c00c003100b070fa1030840407151128070105043c0f00e020340c00141e09100508807000d580091045454400e8003420342450607800c0740000000030601c80b82ea034240c03500c0c3d07000d2440a0010700c2d01e41e84c0c0b00301d1055861511010f54005841d0001d0b500240c0a031040c092040035181c80c044641c2c0529501c0a9400b02d081c80d0441c500210300070b1125080b0030001c0070b400c0c1c0008400152100108002030030001d060348001c3c602104200c0c2030201d10f0130403a080781110920174160040380c40d41024a01c010b500359105000d0092420040500d80d071b008250807085c180d02045000d802000201c1050451300046103c2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 713209496 1250 713208246 713208269
    0x40606081303052107120b1203070b0703061203111207030c021302040506040b0d0507030510150e0a0e06190f050103051909030909050609011d1003060c090f0f 70
    0x4400329005000030700750080e03d40c1240c0b13400034a51401107440001591480c001408140c20741c90a07034141d02c80e1210040c000c03540141040803842e1000d0ba01c0c05070705006019000c090300480c40490082d40201e00401c8a80c14007140102d003414058032300c440c0d80d140030b0300c28040d92401540d460a00022164108c0e89a112401c8803044c0da02404020505030140c00466542008003243d5940d8800242c002080c0c40c540c0c107030b07942855800700c400b5a00060300d58010b02d82070009000081422a2800041d201081c20b1a51103c1d0245002c50f103800044c42925003100d0009408151907202900c980e100b602c0035507031500404190101c295411141e0301c912069004240e200340700c650311a8101c0394203c4c0f817401840200d86041c001900845d1440d00d8201d0103d11103000800011415004082c1d001c3d80c100d84044041d0324164050303442c44001038503580e00444610000d92540d18244603200a541c000008112411581c840500481e040f0b000301880b22062000002d12107146d080800252007071244d0f103 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 713210746 1250 713209496 713209531
    0x619060e04080c010e03030c070c0b0901140f09040c0f02190201141305031c0207121203180501091b230f1216030b0c090d12020a050f0c04060608 64
    0x38010035401003d4a00701554a900a0442156080010718000e0f8042d0030050b594104078900241b2511540d800f206422006014020640ea0054684804104803100a40d541c0c0103007891070f82c141c421214000e82c00351810bc2059003c079441910f101c0c90000a4088561340212840841c1d6085c091390002400154041d820400440400700075050f2082d0310400e60302c2081d180d20000381405072080c0344070f0020311840640901541d041080500078185c40c0250f1502d1b1300e0702d884607039003412003111040c14140c0f50b1042c04503501400c14100802d940260007040401141d01d051500d42010320345101035440c0360100403a45001580e15103212407009242254500d9a10061048108410707061651102410001104800003800604103185a107800359042034110302d409800100081d2454440880900c01c040da01c0d29070302cbc107041040ea04400c400d90301c900c554000b2441d11480440040243c007940c43d081c80d01c0c003000149156010f5044409000054940004a0305010200d540400e01d80c0346803075 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 713211996 1250 713210746 713210753
    0xe0f0612150109120b0a05060a0f0b0304110d0c06030b100e0409020a0f0603020408010f060b03070e21241003030507030504091103150f010905011206050a080619060e04 74
    0x322041c1ea5481810403869981d580d4400312a148070143c41540c425030310800300035040a40b0300c2560780c007036003c07980b004100d414002804603004980c0124012000000045800d101c2401031201a104000b4006e800040711842c080000103541c1c800d19000ca400d00c0c2d40304005242000581d406410a07607500720504450030304020103031141c150142c1c2c10098400300420f542c00000400d00141100d0b40300542c0d5549007401c2a821503c80480c2c100307003103103013410505c0a0080813040f41d801030700a145c41040404488000b52802c00c81c810ba4020000031809030b0340001034041201c1c0301c083d0505048090703040120002d821608c10450f400700b80000345035420300000340a41c000e88840c9003e45011420700d0744581d512001c64032002804441c200d0044100002c41400201201501c20140e4550240d0303c1c440d000a45503100a009250611813854041d954a00d810307441f000c01020010b08240415a9484449031200710580e69480160300300f2074500381081240c09644202d030300950b204074060703980b0346 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 713213246 1250 713211996 713212021
    0x1212040804090c05180102160b0319151a0f07121106070914150a11100f060303090f0305120d14070f020714090109090212010c0e0f0612 60
    0x2002110184020702010403a041144a1400d50f0740460316501c1d91014010400c006040000340c030181154408000715100d102c0d03501c070040c01c03900341da40000e0b04c036101c1d05a140d0440c225000302c0403440340f0b00003113811500026144030b411500600e410b511004201c00c0c90980c0c0d032040c0ca84024001404111400c002642294481d84280b1585088025807502c1d0030980d0510005403480e200140301780701300744a20001207203a1000e961080750061a8109410320071002c0d4041c0c0c030401d8041c01a028024841c121050040c0399901c4108002005070b001d451122030014186400140e00190001c2c50224403402d441c2d800d0710a0325045801044c214010f022910500d034044d248428102d40c9452000082901c110342090149480740c5540c0c4048021510080c60302c60b180c0c0c008840c5030300d10104010585c8a100c03500381500d0b0781c1e50303022034240c03130b00c1c0082442e0710f16049040300c0c60361178011080400c50740815500440002121030040d031143c4101000703a00d0060000100c1e01c0c0030514082804a041203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 713214496 1250 713213246 713213251
    0xa03080f030915041203060b1305090601140403080c0c060a090b0702060f0a0306091107021809030705250e0106210605030a0b15010207030507152a050601081212 71
    0x101e0440d4607200b4880f02c0881801410381313089a121800d500a1110140c141c000e010103070450014050070b012890b55000f010788043d1261500442840010400c5039128000c1004066141c01186542c2c5070f8a140203603030350307016002c481654064005a40840d107401c004540302c00d1203640e0b5041000d1300301400d8004542c0071000c1241e05ca0f0080262203c1c40c01c1940c041c00b000078898800242d01d601d406458003d440d4403820840c0c64170001c0000e0070040e50303410034004082044c1405c030031041da2014191450740c440d400002c0c12612460072483c00e044003c00b0600070000188005a50043d03613400a034182d00400c0c041d48021400c041340d00e941010308450300c03207801d85c0500f0010600558400209051141c05502500c0d038403035903003c1101c00b80c04050f400e03106150a03c01000b4170f40ca15104d447d260651400785424078a59001011102c9220700018800301100300c115500306000f261070212001c071444411221030140500010340480d0226299554a1042c8000c0e031606c0300d510041117144100 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 713215746 1250 713214496 713214511
    0x50304051c18031b05040b151c06030b04050c090c1204030915020a2a0b07052812020129041103040c080f07180e0a02032a0a03080f03 59
    0x5100c1c1000350b03100703108540c0000c0d40a80d004c0e03428032004081042d0304c0d500e107420140c05542420030803200ca440f4420840540554074506035100c142e603110489003c0e4111542e030034502c0c10000c0c040140444041c3c45800f031441030b822540e0311a0003106000d16000102d410700c0e1040428030504080c604805071351a88984245003011510b520340b041c04c034240c07180021120050b0301c0000c1c200c042060310795202c0c090103030204031016144810048041619030b54080c1d11110140030558000b0800e0400115a10b42d0b55002a90301d0b000c403250111000303480c14001542d211511040c0103c0550041c4074074544008501c462036014480c0d03103141840342c0b54072030340756800c555503c82e610a1600c00c44040d50065206511412049181c0f1190340e2821036012002c3c425a00112130802c0114051441d0034040d5060080100d02101e0000341d650504204540103501070261000b00c00800054807828646110f00c1003c000c0d080390360f0000d1146159803800300800c00340342000b81200c5c10440c500510b521000c0c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 713216996 1250 713215746 713215757
    0x9090f030307261f0f0807032603070201090303050c120601180f0b0414150307120b120d02010e16030b04050708033013060b01140a0503010e07050304051c 68
    0x2001180080044001c503010b4000d81310040410f245000444482402000c00c22050041e40782040c02246e1036032000d1000070081c00304400410b000c03042a880351101f6407661040701c0d890380b50081002c1d02a00120303204800181c9444001003101c09624103a0301d400c0c0360681076400d19607074900150f500c020607030044c028108605000142e0034500d1060280581050750105440d6450807080c80c41850318600c0d00c0340f150b0000c1c2c0c480c06810000342e007507075071200583c0741c95280c0f07000f5002002c004000a40e00d440e041460044682c445820010781d1318506425a070080082c0f50702044910f481d00144940d41034080c662403004c01c04500c00200c866000340c01441640c0c00d443d0746104861a542c8880b4005508500c105813080d0328091a0701142d40e10740014818555524150a5995800c21400401006030b0b607946c40000032640306007030940703071079200307060a50b620300101201400c00c0d00240310701ca00169800c80090900c900c01d1040d01d00075035000d0b0080044004a226501170010301a03507813400c004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 713218246 1250 713216996 713217047
    0x1c1b0f080106090312110f070305011a1206070e0402040e07022d0c0108150414040b090303060603040204200d0207051002090603130f0c0f030b0f0108030f13050604030501060509090f030307 83
    0x10052041c2c1c0d00541c0b040d00005810b081d06600405d53307000c04140284030398410b50a15a9000000c51004c0d03021585203010b940c607000100008000780a0764001851202180040051880d0001817081404015a4002103803160300e9890380c000c6504025555429006400310f982e0b19402841c10503041812020340a8007a0360020225044991400c0b441c544480071800b03000602c05101d480f01d4010402001451840c07400c000415542d00c40644001c1c01a9915008100c020f4611100e00c1804512009200c0d602c840c07000b402c07406034100074003c1e54240078945803803070240031510840303a885101801e0f031030440d61144e101d041804055402503424103808400c4000140c00c001c07407500602501910421000c0c29820a4480c4280007080110440c94200050001c810001b0541d16089090b1500a503103e150300c09524405889602c0550000d0011501004000040d04008252401074410030301d00d80d1078046856584103540542e24003604200041f0b4040d42c0b0907008a580310444818400089 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 713219496 1250 713218246 713218273
    0x9060405091e0f01032019060e010e09060a141c03020615040c080105041e0912030509150402090a090b100f05010903081c1b0f08010609031211 63
    0x80e030701160511944845080520b0788003100c1940260000c0c80c00660854035030540da5020002c41104040340c082518592204030190303100590000c03000c2030390000b03254259071254040e141d502600d900f00c1c00b15481c2d0725070030f0250405107411031180400600c40300110b807500c2c0d42c0484440441040c00d8100220401d141a0360040d0201082e249109034003d1a0500c1c0c500e442c903115058028840d485107043c40500019640e014412a040d0b03030044400148485802a59614103640c0c000d280c00f01074109000141400140d1080321041c2c082910180050b5503201c04207503c139405002182491f20724a4082405814410000c99102498007030028603002580ca0350218180c007100d030181e142191000c240002c4000940c1d8000410f02804c0090080e410f42e91804c00030300607400c540a6402800750302d00d07124078450b00010348411411400c0300c180c1504420061803902488202c0c0c011401c0300e000016603074840c54a0380c5c200da403c03400655011094841c21105400e001c00f000d0b405120355501725001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 713220746 1250 713219496 713219509
    0xd050a0204082a0406050607030e0103060503071805070807080a090503040902071b0b160605060f0603070f02060705030601090b071a130b0108010212130c0909080406030f09020109090209060405 85
    0x545203510350f088203030092004144030984001d4001402541404810050354031005c003503c06150f13160a2142044d100078004800908065100903070501c035050303000071440207a5408030804c084000003440b6555840b0b00c15180341134150788071000503815000045503a4442c0d4015400644100c050740d140a5844c10103009a801100081c2e07901c42a10007a1240c4031100d01e04c07000149608402641482812041c44641c078800340b4010307110715220000a1041e82c1d58486504904000804590b280d0525100092101c24442c000401512420010070358280c01001a01e10503481651002e44030703410135001070a07075001144100d8a640b40640c903446070b015440d46a42c864a800080e0741c20409450410a0b070b10a4182e100b20100c2c0d204114403c5100f120304005a403090080e180c50311120b0300352601c480304010641c8041c40891628200100700450a0010811120345640c1800a00c003120f003000c08448000500a0220b8040c0300304000740e803031607009020503d100501c0700d0b0070541e45001040f003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 713221996 1250 713220746 713220763
    0x519290f030106110c0415090b030102090405010902091318030f050c1f11070c15020703050d05070c060807081b0d0f0203100e01030506010501120e0115030b0601020109080d050a020408 81
    0x305a080130700140340c500422540c4a07540080344c0a101c1429001d42c0600000c0840c01600300301925903510090341c0c0ca00b50116030102a028004100a40e5540403200081d0450030125204141003080c94504290318042c071100d54240c6812a40300c06110b650a0790a03071281001441402818041d080f800c1400f8410341c0d0365403280f05270141841400f09046001c45e0984080c07a5040e020500200380820f00700c52680066a00407007104602e2800d080d0241c1c90303c021a84003d145203c0c1444010f455503000d000b60951500c03c03059101070a403a020152a4484102c9440e00007600c13540000d48028025081c0c510703090382c028001440c1c800300c85514825100f846008043d81a00002409160010308852000422410807034604d01c0d41140d6815448400c1841001d04108004d41044981c140f036030720007001d40e01c80c0c0d0000c00000c00d800115044e048500c0c030060f035a910700480004c0c202d50042c0075000c121548802c50500c0d080c0c6c4c0802c468000c140190841160039401d00001c52644000c0110a0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 713223246 1250 713221996 713222009
    0x90213090c0603061e03150212040305070c0608070c020f0f030a0807050f0a03051b070528080f03040918061409060601020106051305131b0519290f0301 67
    0x80030703418504081d0548582e41c0c0328010100b240c0380310100e2003107840b0f40c440580394000030448803c581e242401e0301034046d815a41d000180458140b10816030080d00030b1010380d04c12044050440d81d83c0201392503815045503400302054901040500501e003103104098039540c02001001340103200e1010134582441414105d0720500b000031100c09001d810000c040c1c0881081000340010317891a03400074242c5c09502c07500e1010841c06400d000c0071000602c0544040c201c0909080110b1882e10b00700000006125000c0f000d003030a82101103180b140116141e000c400a00d00150300e82441c00040500415820710040022000d54054200240041c0910209500c2e003444103045070401c210040e00b0120301900d941d055a00d8001e00300300341d0711a6130000000d10840900010a6500c0050030200b002900070010440076401582e0030300c0090f800780c44010344030203440300c00070403440c1c40241008031850302401200a46c2144080f0441208a401041248030801010300342801d0195509658000b80c0042 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 713224496 1250 713223246 713223263
    0x506070c2103030e0a111003020c10020d0e0d09120311010e0114010b0405030a06052d0106020c0603090312060d08180108060121020a02010e0a12030b10050a0309021309 74
    0xd155141c09030070540d00044000d080e0017102503444041d1500c0100e0401c0c0200d45900c22042070500a40c15100325031821020b803250b4640c1c9281c018020f40c00703d00e82141030f0b8a841e441240c07114000841841c200140d859102c641400d05042107000040e001d4110308110040c1540c610400b4280680c800380d06181c0000319043c5440300c5515412030341600a00003c03c020322040107a0b641c00207059036201d800160020303d644035140070029030010003020b00e540720300c2810088901a0044c40a0381250943d500381e491548403281005010b10090312004101d0340706000401101c001c250049801c24001000002d41c40803d50342c030004c1d508607c02611184552000701082c0796040410541c0c1710b1400d103054200152109a20b19811142140d81c60100360301003088400c1074000d5100c94003950b000300860340c5d15031a910380180540e884e0f0b024000081e081000030040380c10628149602400c40c1e1300e69900f0140d103180214014050214240e90008240c654107010130550310400c0045405080760 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 713225746 1250 713224496 713224559
    0x60e040209190311030a030203030703050a1b08090f0a2d02091e070c33020c210403030906080717190b030d091a0f12011814010506070c 60
    0x500065450f4130950094000108400029031301004403036112020303050010300e03901c4224001004040c0c54040b1035911050944041c1c081d42c0088225118074408011211203c0b81003903d00d44818071440e005041c81418014012448600d1090207002c001810690940790b100d40c0005d00c442100351010000e6208210000c18a100e2064142e03a01c18424100764105600c07507038034804103031000004c1c60002c1d9980c5050740c0f84198030005000c5044107140702591a440b20980701c03515020311844885000c0c00150403215000800303400d91f070440350180c40301aa4245410341c00c0d5603080e001031501d001c0051101c0c0b252410442c02000900410ca0030741c001402900009420741224641b290f103074460343c0031904980c201540a00207a00383c60300c0c0c1c0200c248454110f94004510700400002041c00b000c08120040303040c10b818002d5040300e0044446000c1e40c1030b403456800c06c4420043d083c0655074107000041c0701a01341480105610f901c0b030a008044c0c0f07590b0741004451591500905031141a40000d03 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 713226996 1250 713225746 713225753
    0x110c07061709010b06040e040312230121030f020c0307030807030e120c012706020109020306100b0a05090d1502031512100902132a02060f01060e0402091903 69
    0x42d8003410060013000070b0f80c021000110b01d801148030700d850710b40d2891300080403d8423800a1110440f0020300621201c60007000c0300390031001a080341980914071400020310500c4c01544408030302080480f800e03c1d404c142e1000c07907072034281084000541c030844030100e42c252010000e01004500509070751303895040381e28004144004181625110b90b100000d4010044004584400300d62801d09020b5207802c40d9180c400381c0410076a000c54042030040b5400110540c041d0003851000e4070840503201c0d80d80ea40400789a01030348a0213003e8881038180300c1e18401070701a40c01080720b004010180348500010b0394460392204a12132070703916074940200500841d40d51262000070250300486000e0191b030b969601c0c0d540c5d64024250080400354403064484259191440010f42c0482c1e824000d00030158075800c120b501c0259402c01c4451402d8200c0c0150b9070134030105416000f0800e20041e010140d1805908070f1742ea02d1002285035019500308502900d41d560029507101000c62180b00f01d903031518504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 713228246 1250 713226996 713227037
    0x90d0f031b0c060f050319050a09081209070b161b0801091a13020105030a1109030d210504050d0c0c0b0a180815070311090a030501020d0e07060909110c0706 69
    0xa00713000a1003028000d0180ca00080c105d81d03241d410303c0050026041d41d8498030342e4064810741002400001c030008580090840341e90310346208650b40012158a2a5a0a0315485902c00d030392038595801d504508510008404920510715204101c1e850581d80c0d0315441010308466001c0e0b030403901c000000c1e1034080c114051b03e10a551260703803840342031040b516a40001e00b50b844020101c1d003010b0f90340c1d41c945204c6252070303090385c2c1440c4c0d0181c01c554403241c104101910542d90480c0d201e20003003c8500382014200c0320301807284999072185c054030150602c0c4400307450039191188100c0d4402074a0201040c010015009403c650b115660340c070b1165492002c0e2010f030007400e50802c891540082c4101d0212514503040c540e0801460300d40020120f211443c20061030080265842d03005d48040000400e000741500a030255410094040103620703540c1103110f41e00c00da50304c41c16001c111203000070408600359074040304031016201c02d034a1810440c9150130f03042c84544e40000003c9403071000076110300c02c3d814 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 713229496 1250 713228246 713228267
    0x30403170a020d0e0a03110607080408030d060504110f0a02011d071d1006050f040b0a030b180103020102332802030603030426070e1506090d0f031b0c06 67
    0xd00301030b5041c40112004c603d1402a1b400068070301000414003180350b8a0b00703000c40380040e4001c60029181c0741c5071150030b9140c0c1d01151a9090682c100340d0049502e00c0d151040002c2c00201290b618605150750503080156002135490105556031503684400e440d01040780390404441c4080030300681c9003495446c0c150410005041e401c4010f5074820040390302c5400c4040ca003500c00905100c0d890318000304132800d148c410b40d00312000c0d0303000210f440c1c8540c2c4d4040c5c01c420b580607421142026440720880310401c01c41c400340b0000c1c1c0140e22400100b10003004032150500280c0c0007500480c40c1401c0180380845500e0280c0784140070703880035621840c016035500304d450401c0c0ca04102c15407070340c244040040d541c1d0049009001c1c014140340c5182000b001c0744c1088001d0607800304203592810340c0d112030040492000f01c1d440340c14041758807103c4840c0e192820456605c03810041c0780881c1c0010703d0311140349900c4100011010301a0404c2c1034502c1c941c406c1c00c8032410703a02c540340101741c642c101840104039040c0b4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 713230746 1250 713229496 713229523
    0xc061a1206221b030b0601080603010902180601030609051e070507030e0918060f06030d0c0b0103080c0a0b24040c0e150f0a05040311060a120905030403170a02 70
    0x5105000b2400c07401000042c01c00e6030304031007809840241c1001d00b0511410b1005804036150f4040020030040c0040c0424424282601c0e00510359889a05060a07100c0c0c40100030b510804503860702e80080307121358040b5089003040c500081d0391900c0e0070060080b1035055820320039903024008030603400c0910045195000c04e01303140160074210144c1c0c0282000071803400c0c05100e20810310000c0c40c0c0c003140c030615030000d0300e20004550080c10a0300600d504064266421070190040c1150103003032900640a1032800c0b5444080703c0681c0c0c0c03031a100c19078150014090b03031040e4000c200b553300105d210110315500035050074282818841d056030382c0740c0040e010461101d00981c2090103095809070800d00e14841040140d68023220740750103160078178140c46080b550440018000c0f47d0030200a500c540900180e030701c035413200c2241504540c02c1185c00d006040101e00040c098101c003400f50445900010b0071240325104507800c1035100d45d40c2a030743d0215902c1070250000e0114107141180d50400c40c0d440d241a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 713231996 1250 713230746 713230753
    0x50c0402070804141801060e31320f010f05090c0307171608010b0921071503051e060306060f120303090604121b0b070c061a12 56
    0x41c2d950a80c150003a8803400b80000380c551281d001c00e03125030380c50080d00006810210b060350703112407002d000050741c2d0350420b010f12510221500c2c2c410300042d10b2003407001d01c0c60701c25109142d0070310001c01428003100b0f80c00003410b800706000e10303074210b245c07203054080540394180f560792404204c0c4900d0040140d0190f620764202000c1000310303480344001d141c2c110091504040c4e0740c0d40d8015054840a00c00b00000600702c080004004604141c0b03220b010003010b03241e40310101d80c1d9a40d45504418014000c84c03942c44081d030400f0b020f01c824800d103444089a50801511403c030f6844088800028180d0a034a011980360010041c102401010f00048452115062813090800d080840c0e5101c200508203402581c647c0c1c0d83d1541c03907403018803444901c2c1c0304c10304491340ca140008065031078200c20b0794116082d0720301d8510110b816000700203030118111018035038619002c181d01c03000304008018000310203201d044201a80450300718024542014121641c12020908010503c1000c80700309254042c00e40 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 713233246 1250 713231996 713232007
    0x90507080f0303070f170402040c0e0d0b01150507051513080f0711010c0320070803270a030b280905160506040f15030605060307030e1203090d08070e04090609050c0402 74
    0x4480c00400b0fa0400d0701949c000a140c503031041c0546813002c03c203403688c2d0700c0910540724404000b60290058140d07001e0801d1780c07180d0701903408195a01e0081000017051034101d80600100c0004050704070b90b00146003000d01450103029120720900b81e00150f4031030303403000b03001501c1d0091103d8004021010311007803801140e04000d503200101040300045002c1007050740c44210781440602040884054003220341aa075864072200c0403900006141c0c0d403020742d0580b0300b800740401e528000403c80704998100704e88140c0c558a048011a115840503110351050071a8481780c8015100b5200d010082485207004191508603254410900c036001e500091003108208414070400c3c0f192030644080302c02640d1212440d81d41c12a040e0080c00440c1c1145400100110400a10760381c90307004500c80c01d811100340d44035640700b10184540c5100444103131900743d211074410102c203481030050b00c0d840f418074680000050300d81800a0151005c0b8402550200d856007013680a0203001e11400c003e41c2c500320750451410 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 713234496 1250 713233246 713233277
    0x60c0b06010305090c04111e09010c0602030907031217010905070903021c020904031707093c0801021e03010312080705071506060e040908030604090507080f0303070f 73
    0x8000a080504158650011070301010003040081c0d01744a00810034009421401a0b0f140749411410b004803101252540c071800103402541200d10030701060303540340780c1441039440b82d102135400605180c269100b28040040450541d00c40200440c405030741d03040c000410b00c01c543c5071034601a00280f82281c40c10003841002c43d0016058021260305558000c0a44500ca491980000038050040d4008180b401040b04240d80801d81e03d4010406d020007109030340701c030441120a01801d0040c074004412060b6600c4030b000300070361000c0024600f550a40303a103600901b101402840c483e03110031074036034010130102c0c0450640114694410103c99105046600d103884c0c812104400c01e21600030301c0118404500c40c135100340d04441405800580d10201d845175100d00c4001440c0b18421100051a40e0320385035060300c2d05016508203540c114804a0540c0c55900400000344070094048500d8423070088005107110040c04104400081c0c0c030042c40d124036050038080d00f00302044000d04104581c04105684070b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 713235746 1250 713234496 713234513
    0x408060f070e10121d102904090f200103050603071707080a030504030c0504021611061b070e0916090c09031a0a110c1e15041b060c 58
    0xc20804480d0410422409038090310a422000b130703507844180c202160f03141c0c00300c0110b0240704003606020844210800610050f01128240305404c084100b02451030760f10314003448501018408001c0000481950740e5840492440d00500101c41000910b14840700303030b452044c00b24801c14000c1c241841145003080000303480349014021304101f80d0f441c6040a02c41081040604041c0c14908c04031812640c0c21308001e40a034225210441d41d039541010042014203160003a40c8031400800d1000220364890b030741d0042104150605150082405d00c800d420b00c441803910320302d1040190000d0311040d41851030302d4103052070003440820164800940101c01d03102c01d00054003128500c4c0070001e28000c0f418000c03100c100283d4000b600149034441804002c032041319400e80100b0720190200031917400541051414052034680040980017003513407100c070341d403d40d88080781c028411060f514804604003484a08140030b035400d8843c540d0310b24155004070720550500c0085d10301400c5c15100c521140e0340f0f0001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 713236996 1250 713235746 713235767
    0xa050604181e1b0b04050a091a210114041e030807050904090b07030e071a220e04050615090f07031d061e0105060a0806150d0504080408060f07 63
    0x2d00150107900200744511800a600c64480a80421021a03662030001c0100d40150040d284505001700300010f000c0182c2c410b02050140a114581c0c0c02581042003090030303e403090000b1800c2120340d40120031b00e107084c0724055408801d614405a0303828903003043c0c490f204a5040010b103030b000040d040e0300400c1e041985554440410300d000c0d95102400d1020901901ca2890004c0c86500c424040c8240c6640580180401225220485903240e9803090070030144440f1142400490344c0401c061070078959060302203d0600c042200299820366a00320354860410b04881c290781c5c0340c00403400d101e2680031220000340b4050040f40d4a400c5070400c1c01a107040e160003d0300d0030061558a9604500e0a00751801030900c660360328055401d2450100400300c3c0c0c89c1041c01002031703000881f070700200f143d240c910300303941c92000c490791080c0c00c640d19031003030082d00d484e1610f4220110400b40700c0760002400601035184954030030030001da161890100d850740b811f01c0150401c200750306914104811a540500c1604 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 713238246 1250 713236996 713237033
    0xe0a0f0e0a0207020405160e030a08030a0221040606030b0a0507090e27010b0a080a0c060f110319030f0b10123803061e041a0a05060418 60
    0x30340c548031032040707000910640e50005d4105040004005800c0b417806140c1d084400903848400c9086402e07030070540c6070940700d00010301c0d200090001c02c3c000c0d400c550141a0001c05000c80010318142c81140100c1114221021540c0c141c98460a00400c00481100c42c0c0140d94808203001d1030501510103402c1c43c24602a188042c44280c0006010b01541c03602d410540681100c903543c031780d5084085901030b0903640e50750743c0245010031000072070700d00014800425941198a05038506e0a241c0101d6860398544204002c01901c2c0d062700403803072420300c002e10010341e01e0300b00c2182e11194008043c094540041c0c045402e9860440440ca09480e0380341ca0240e640300b02d107452000c10032014180c0000b4074281c02c098251290130742510f09064050021a05400b0039282001c0d0003d0027102003580d910401c8500110a410a50003040340030070301031b4183d802c54030070181108560107180da5550301e0181140c08130b03802520b80f030900c4450704061107210118002141c008150041d0380c0c17502d09a141d400d04002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 713239496 1250 713238246 713238269
    0xe01050f0109030602070605090f0f0a080a0e0a0605030916081c03180602030103150504080a03230415060602030c0a0b15090f011503140c09040e0709020a0e0a0f 71
    0xd103030982c800c0410001459201030110740342c0715141002d02c01420b00f1203a916661042c0344d0814907100e40021018a0ba0300f051006000762005680e41d902c0c0c6400c02800c100501050155039400e555840c60701c1030250030a956401e8030f0f49030225400345004105480610070071081d01050000510104108800400c80d600089900c0543e0030101c004150001d0410840d1441c0c001c1d001c10054960000d60490740141400b1901280140c410350494a0640d401800301d41c080050903e658081d4000c4421040f00c0c1000b1803004034800da03240540c41c01190100d41c01d460190700412090307071038031503c070260405100844c28001040440d640d6140c03c0140684444400301c00503a1100a06420305a0004043c00c1e14600e41011001130210043c280141800f1920114003590001c0c400e1207041203054076540500f956803a0003801c40c440754401d042c030a03003007510b502c4c3c0d004100400700542001461fa4610059540c4c031580c000604031800d21114903c40d40c0c04031420130050606251a10580301d0300c0355132 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 713240746 1250 713239496 713239519
    0xb13140a0302040e0c03010c0207060806102024010e0714030a020f1b030301060f0503060d240903080108120403050607030c09031707020f090402010c11010302210105190e0105 77
    0xa461170b0845010b4070303130391640c01c2140010643e03901156000454000703840314403007a2111010040586115480c80740011490220300500300e107055104400a010300055030304404000302d0b1040000a6020504106051140108180120712294903484211850220300c94280e400c04e460340351101804d240b40b466004a80080030303800d40350480301c0c5208130b1210400d00c41a8008055200d8009108180128422020032000c8c20f0165041f6807080100602c64200080c2507070f11102c0810003080b03a0000d1b2004200c200b030380c079102032040038405c50013500c41110540c50318400a1a0408506444d6042e00703040c0003c01c00030340300041d0b1a070403484034100445d1110003014101d403819102e0344090524200034a40000000c504401000300e0f50090320400101c1c0c0209082c010200b800303036402030015114907400c2000c250026820000d5003014034000d81361100c0c44814181581101c40c00c00c4400c5811001042a803412010200c001c50321603103209100b61410601d582c130381da07052041038002c00e0b10004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 713241996 1250 713240746 713240771
    0x9090f0a11190f090b01020706020304032402030f0109050903070c030b071e05041e080a03180b0c011a01030c020a140307060c0804060c110d140c03040b13140a030204 73
    0x1010801200641e000345043d5980ea80030603014030900c6404205480c00f080c28465520111b866000d132250b98004500d02071031940d80c204040d1002b40c0b0000030b05198542400c5210441c0001e60007212100840c50040d418028001d08440024040c1403169004000310000104402039200c02c5a0700080300058942e580c8030142c1e0f220810b070380c10b80d83c4100b9502e078005100e9001000b40c42903c04440e01c5101b0a6005410440209c081e0700130400560310041b004000a441480c01400c590500b0340251201c1e070361428800001d82007010b0f00030300c603511a66001884c4100800304d0310220000d207000d00561200c20006500e410440d58003402c02c0030344030395400094204004941489601c008200002c070010135004000307601c280c0381250078600300942c00142d80c2c0306203070340181e40260b140605814111040182d81c4c000c1b1aa651044081c010b00c081c424500051001d003001f051076500c0300c1e685140c40c43d40c1585801e00c3e40c21800300e01801c004480099100c000d884008c1d250b0664001940081601 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 713243246 1250 713241996 713242009
    0xa0e0f0a09021605032d030622110a11060a050c0a231206010f02010507022a06071101200309010507080c01061e06050306060f071a041109090f0a11 65
    0x1c002804c2d0f4440050800800d00131425011024001c080480c420010510304003256440300341c0c0d2040c0d11401030581d840c8249102c415002100011900000740c81040d4000f08225800503064840402c1c0a28588551554140131882d031101c1d07020020032080c9450220340245004d003003803201c20440200003c102c0c0c4541c0702420690b68285801041e202d00c50320000108201045410ba8006203034044800c125500501816010320800d8003d482d070680088011100606940d00c094819008241d005500b515520018a80c56000385c01d0000a112118005020022036001981030000101031002a600020041c4d56800740c0c24605507a07240514106010140141c1003858615441d041c80041e85d100c1700383e103403e00e41181d5441300301c1a0341e0390b1b9000e580c540001c41d40c840e0002d00801902160001d1078004010071841243c040800d51000c04524418a0084030110b85414a2003004a018640146000c1c0d1080d40c00005041c40365000c047c4648814030140014104031302c044010714540d6801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 713244496 1250 713243246 713243287
    0x1d030a030510090e1c0e01090302041a090a020d0e07120305090a090c020604031e2a0c17010f061206050a29190305071e0e0703020a0e0f0a0902 63
    0x2803205120341480320811580350740170400c1040e6507504604101c5452805040d543d00c1d4100142c5502440071302e1902400007030880c1308a1030810304680d800c00b0000f0b5442003001401081a8540142c0340c600c145c00b4441159015840c16619600180c010450f10350b20041104039190f00d8030300346031900e04803400f003100007080e90452020309043c0380c00615000e03070004400348640e002342e84800e60f4138080b04080b01195000c0400707000240959515044040f03111640710306400da2003400800314045ca480b11803408c0d4890301b01524090806601044041c1c0074000c07089500544d400402c48103140c5000310410f181c0c040130060085444000103442800307154000e101004540c880002107031000c4c07144441c1c00071000031152250307514400c2454148071022010040c1c0344d12000800d5214140040140035103d0031050380706004e00b8540204d003d0b800101000d0007514a9100543c461417280713409401c0e007011840b01e60003400301064601e60365942d00901002c45200d0080140c0c2d41c000c1350603504441c81c13038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 713245746 1250 713244496 713244509
    0x219032f0a0c05010e0f06071a010e0106120515040504150513060e0606150f040f0b0c0d0f0819060b0301140307080f15070c0203070f091d030a030510 66
    0x4205150121201040007000d0340d105204118060307031100015a1801c2d4900e55094000c0010a1500d2030f500300381d00201909401a5006c80c20841914000c1c0d11110090304030001641140300100a0950400e0540180c51901e61082c40a458000f030042c01190444007002c1c89641c83d00302250500444004001603140c10000501c03691800d5087c0c0b020f61141400121000da280100d00c501120780420310600480d40184000400c8000d0501c040c1d60340c2040c03407a011102810000002d010f003c5000400c0201030301c1c030f806600c842c1407988040c10103041d80724000038440d2044a0400d07240d4000c10555000d59510008540034042d1925180205200d40007286201d50000001c551050a03440740490460210202c41d03c00b51201030705500d03120407030143c4100d0303840110301c42d980002c49064260b20440614000c4400440c1d500000e1600840c2c2c2d010740c0040c40740b11010720501c0c0c000d02441d0760440e4540c01020780c1c010b482240950324450040400100b556400105681210586038074006100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 713246996 1250 713245746 713245817
    0x120b09270703060606120b030a020105070309080f010f0c050a141605060906010503190309050913020405180105070c080306041a031605100305040b0619090c05070c06021903 76
    0x1200e15020001300350600416000c0313400700201c0201009103008800880708060b0140034a5041da5005603115001108101e081c402640004200100208003480d00011004004203610303003240d2284c001c072056201340c40100242003000800c4540c102c400071844444805a0907903d181a01001c0202c250b044001000d900a1030140015500300182c951f0503140210195600000705000300c200044028000038082a5420810401803400d07004a560140721400130503013240303869001504840085800803d226000f100c1400d641d43c1c00d00c1000d0707001800341011008049262922604ca010061400e8840e80e10744800c1002000507103100c4c60b000d14060102d0b01d0030455100305046413800ea00039103010303c1d402100254268441e004231409103070003044910710b944918051045164004410351540091048000b50405d500d100c0c404000c502603903000d0310f403002d510300140b0207609a409182194050700d5001701d11000e881e17180c0c203450380c1810701001044041e4440400540304c6500400c0f0030f030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 713248246 1250 713246996 713246999
    0xa030f060b0c0303040f210e03390a0909080a0e0a05030c1512010602070303021002040b040b0c0c100908060a0501030506070f111504030f080c180a030c090b01120b092707 75
    0x25004020909118011401d0350000640808000c90012414501056650301014135544250b0758200039446c208001d810b0b648be0f552079200c1002503034214041224600c00c0065500d031902d030b110720195540c50003254040b42c00c504d09030010359a0603a980c0102d114902c551852a40f5408140484801500c11101c450b503c1da034440010b0740718103ea100035405170003040340a90940086208580542c1c040b407075454202811300052004640000c000d8000501c150a082421591081d0000800545544c0c801c0001402d100c2514240301018001540c0c3d541000d0062000038004510564410000d18280e2506135905000f00d480c1f101c901d007800120f01038404841c00326051600490b02c41c1e0300984420061628140301100c1c011400c07160140bc1c45400c1c41003010007076041740c01c130b0102100100044901900d03529a800b9403c41580040040c5a035008210701e0765821161200702d040304031034104104002100480d003140402001e030005840b40b440e1204002c00c0c40c3c521016228004c00880740000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 713249496 1250 713248246 713248313
    0x11103030a151d0610230703030e06010f051306080d0c1a07030c0e0904050601030b090f0f010603050f03030c180a030803130b0919081305060a030f060b0c0303040f 72
    0x10201135400a004c5d2100c030203424181030144851450380203c42d40041008951031544d0245070304008022010581c6460282180d60000c2003558040d080020703e840c945450507040250340a011081c6180e868106801008000d00c0482e0100c001d80f80d42c04d0400c45225185045907821203030a4218160086403020b109103030358160302c02400d40320591128490307240e05204104800c0d80496000b04694044001400040ca01e2450641c0242e000003c0300c0a00700324a0220f41017192401c158200b0341e40d80c110400621808100c81d0100c80900c101039071840c1046020b8103030b50720070362034405d1150409a11030016a280d00a03500c00860b001504e0039120305010003a40b20154003940c0540c0d42c4200400400ca0301480828000c00c0c0d940040021603103074001ea03039848010741041601c006046074600c40020030b078640c1d000a203c40041a0340004101c40580000d03001c480f055008000c010505011118050500108990300142c1000c94104d081074545130114020421a030b440340c40c00320142006c40310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 713250746 1250 713249496 713249549
    0x50403060f11070201030c030e1e1c0f030c2a050106050406052b020d030203030702070e0123150c01020a1b02030a0b1506030c0a0e011103030a15 64
    0x2a80d100d0501440380821030045401a200c0100d210100580d0401004005602a031b121f901e038082c65040c04100f10ba9000d40035820011b0109000b44120600d54811369142014403102c1c3d031021002103d031640c2c90100070000d10100000480206060b915400d898069025402d201010201401c5402254004800d50311948400c504115425130a0071404a04c0740381501a440907600082c1c030280d0300c14072804100c612540c01010403421003080b0001800940c0f03803600c04080c1640203800030341e030b02e04101e68002d1030410140d04c50060001c010005101c1c60308840081085511483e15076076840b001000003c0c0200300c003500403144810001044802640c0c1900036107110741d1039460781d11000f2600d090524080500c00b43c02941508540701a50005003a40000c1e50440c9124050070030340d850010216401e03138410341b03481e40d1036080070540f4102268803401b820100b450030f00c0d22603640c6c0903009225540e4040a8008481c0e580c40d0317103141550212903c81c140007400c046614070340c6144001c001088 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 713251996 1250 713250746 713250749
    0x20a1211010b010c0809220c080609010602070b1902011d010c030606170c0f0c030307050d11070308010902030903090a0e0103020301140903180f130b030d02160909020616030504 78
    0x665081c4280b825080d80652101128950844c400601d4041d0b070314100070064038001a003480b154103810a68804110754410510b10341a543c442c0c60380d45c1401c03400c004901030141c2c0704c2e2045610500d01030000c210440141c4840d41010301402c5003c2900602c03d81c050420b02c041074110b90304c42841041e050005400c02a81146161410440e1603140c1c48121010b020f051460040c000716900371551070145a802864084c02da4403d9508015101400c0c2e411360740285c41080000f40c000c2107101c0f500940d4412403205c107680000b109c2c90710b5032036a0050152340051198080c2a680440000e01148040c0700311000387c103000300505c2e1050344802c01002040b8080c04141d00a41c680f0540a018003101484035010380a11402141440003942c6028000004a013610340c004003520110443d684036400d02010300c5031a81408900d080c0c14400341480c050281c40b50780c0840d0300072204010304446509030b80c0c0c207440300740c080490302c2103140c0003181552150180c006054600480600c0900d03a00c00013400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 713253246 1250 713251996 713252027
    0x607020d050f0606130b0619020102090a0605090a1203021f0b030a06140c07050a1202030906041203030b01260405070803030c250c0b180402040902090111060106020616020a12 77
    0x8181402c100b204074121115403458503000b41040008164020700d03000e48e1090140184005445c045028000c28a0200503922890100d040801c420300b2901e4003821b20000703003440840c1c5018018503924020754861018140302c14107282c101151080d00701c41c0e008502240c10280032a5005401458464001d05040443c80c4240f9510300100c1c100c9a803460403600d1054000006002a03001a260700307951100108940080d44030401800e9199155500900000c1640c1646402603440c1414044c082d2000b41c0c5000741001290b803100c46110707400c10f030302c180107007101c1c4040680782e519894981d141c00e446070842e0085c0d101c04010030140352054802820001204051070440200f5581684842c00c510032000340f2800e8a00c0c0b00340044039020010705000303000070b0140160002c103100420100e80c019000042c0f110380000340e2090950b0090a86150070b043e04004101c01c0d0300d070000c001d468600c00b6100040e0080000d5520703070600d00c03c101e0712146c00c1d044450380c22003042600e406400e071856550402c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 713254496 1250 713253246 713253259
    0x14030702091b0912030d0603060b040f200f0f032d060d0b1306091401140411090702030c0f060711013b0601030605060108240607020d050f0606 63
    0x581c40d8440280c15091640b100149241002180c0040041e183d41c24441d072003083c881400225400c100170b024420086000312400036220503050b007408181d6009802c084419410310401c0010440fa4015a6848101c1c0c008240d0b19444000040c80751840742c013091800e03804010062003403080c0725038101c030080003058404d49150548511041c011f903001310f91040e071110200e00310b4030104291070075a80d444103071030b40851075031001c595038072003203801351103080c2c9440d1a007054034071803090244140007880028251082c4a0300d015910300702e1480d00401e4142c05a50b10350049032816001f00280c070040c0710070303a00383ca41000885e0b428980c0c03188204d40f0100090381c0485100584141803050341508800c500c071520302c00c0300c56005c400307110808249191906048030092031000c1030500c440b9002e148110004603079820301c0c0340010b00c510f8010f020403070310602c05a850302849070400b80141070381c107060380c1164503641c15000054050070400809483c60085808160208030007140341849500d044520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 713255746 1250 713254496 713254501
    0x4020c1615020d02120327010501140402070f1e0816020109090905210d0207030914032b030f060608070201050f070905060f0403060608030c190b04030c020d1403070209 74
    0x890340c03644003c00c3e05016030072000d0441e0822a08400559001402e454089071141003180311544a080750121264165500d42c01030048900b14803040d20622011a000d40c2001e2180e110307040e80e003003041001803044000149038014555600f807a050555000040d064984955810306403030f6010844040f40016800d0308041280b5002e80306a06806030404d00425482104a03504c19103c0010207000c1c01c0c620040c41900742d80c0c0590300040040c24820f964916446241c90000385001c111411924030070780001c134412440d0742c1c500541c3c40e94402c20030020b48218211a13400c0c0c008280d407071144452a030400c1404070b02c0c1608002c0d10360042c505907000300710325580d250070320b040c165041d1459800105c100804111600d8a0000340850019010304189402c1c2d03030f40e94030340c1142c2e100c2e0703c41001d681001c108100c040d9028030015100c030400c142040c44110b107540d5a1030021070020801000c0c02126020039080d134441440411890798885008103e4005c02070046681c1c1c8c100c450220300c120b404000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 713256996 1250 713255746 713255789
    0x306060221071a04051015061b020a03020909010209030c0a062102040902130503160510030c021501090c080f010e070507050c0306010602010f0b0604150e01110d081e091b04020c16 79
    0x181e0030304031342050340c0d400801c9e010400700c00d503042c0706a00280c5c0c3c403601541c008405a950464102e000b1050f1900060ba25080b0005040c00d1841c0300c0c2020f44509c900c4441001202d4000503040e081d0550a510001c096a100c1e21a030024003954200300c242510101d14510305160a00c40303802564030442c1140e00c1c002e041b424040000c402d500603240c000c501050300017902c5007c1d8028804e80c82590041d03801d0b0181249415440c40c01c240c1c412062a501c90720a0b000c01e075085460680c010442c02d003d00c220f90304001940380d204001420070020880c1c0002e14600340070782840b4004007124002c0940e6465690345500901a240000e190541c041c079290480c5114503104044508680c45622058000c841400d020349078000360075510350601010381006180c010090040c0303400a40715840b4a141401c103100d008104014035030104807500c44803030605c0504400040c040b079885010720950034200c04000041406400b0380100d1007440d00c125039990750380700c0c1440d003e401910032040c2d84080c050721481 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 713258246 1250 713256996 713257031
    0x9020a090e070e060c0705090f070e12071a04030210030b0f1c17070c0905040b0a2309071d19021303030503101d070306060221071a040510 61
    0x40b104800b2a40307100c000700c940e00701403003d40580d01d10701c01520501d075600d80100d41c001004840742544c2c01101c10401c2042c941241e40b4401000081d40c0d240b94050300e90701100d0b690030740d60240c1d0410342d12031150618641c004800b100c01443d40034012160b5030038081c00149c0540341e180300661107610a04092051410800c1c0303ca00e150b1012240690f1540203a140c4200b088600e12444001f4030b003c200c410f0200e000d1040c481c001b4516510700241a152a080110311944050320089405050128400c00304000101e003060041c001c01414806440d90140300703141c196941d202d0056040000f10f0561b038041d1a9103414418408a42c11107941881c1228150480c41240305420300c1d0a20303030300c080c004244510040c40d40840d1354942e4502c40394603001d80c03c03a030b042507800715070030130102c1030030808080d5040c098900109400e0004000140c4503000da4809941e2100109405034804180d070000e111500700c6040c001401d940c2850454145401d009895100b4200d055031500d003003450b6001160703101c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 713259496 1250 713258246 713258251
    0xd15030807052119030e0102070c0f030302010c030203012301021c03091713120501060f09020901031d070b070201030b040c0509011d030715020a020301050f100803120a0203061909020a090e 83
    0x82d0f4061302e00030307490000350003d1203c089102c03032540d400e2045c140052451018440513041c1d0034903030100103180d0b160080c203496043e03140304100750061004000e6448000c041403c030008000c034210107001c0a05c0102d240840104060a041c2d00c03694240f410b880d09980034900042c0202c954580001214900034a80c2c03081c861801c801543c041e10070014060926400340c4001e105000201b01c1541d10030904043d807649400050303c03da80051001425a014410080340c031101030035a4a900100400c09625840a4032031112540e00c00610380d01160300c00d03403010248140c014010803a8501101006141d0b0b0895190140416100000c81890741c0c8245500084144014000c0074080d04000d00c4025000c584058201544550300e00500142d0b000c2c010a4465110b80380898003503c0d041c485c40102804a13800b8007410341041040080403c0001980342d0b111130f800e074003d0398a4440700041742c05262440c4000d005680015004103100341c20b07030001d049c1d10003580c0e5113202c001e40380c404804030001c05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 713260746 1250 713259496 713259517
    0x7260a0c050c1506030f010c2f06010302040507090902040e0106111b150712021b01051e07020d051009030f1407060e01110c07031b06050d150308070521 67
    0xa09042a03440b08400f42a50340650054195420303105000395583c252403c6014160124200700142c007038102450164012500c04a407420074001305082c415502d403001800040c0c0242c0e101c1c00002e02460003244940300170103000c402103554a41e1010780b061880404c3c092240002d1088285c2c08003200c0015800c1502e10702410300c40c03c800311010400409a00c4101070000080d41404000b0206541c0c0004120400b0700c0c0d000351a125801204a2400681c1800304ae4103000c4203208c80201d4201c0c80414400105104004aa40c4c040743c2c0005074a600040b4402049441400c65610008029400255600e442a106c101121020aa0958900380582080c807100f0200b032040e1000f01b02075811101b04d9481c072030000075007094020444442988041d4100403540d0141ca4108204103030f40c1d050030704e401c0e140e200d107000050604100901500c504010b000105448880000c001d82d0510803c00003903030301020302a50303880d2038613003681c440e03505502550104d002a8401c40e05030707511008403041c0a28 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 713261996 1250 713260746 713260753
    0x90204030c0b18060406030b130204080c04050606090409030c110409020f0105031f080c1908030703050f04090203010603060503160509061309140708070b0a020a020907260a0c050c 79
    0xc001d04140940c1001c140243d048018503030002190b00c41a000f0006031803556004a1030404d40300034803031100440102058040d104100c2003000101c00b00300c0d092201c40840f00441c00b91541d4000840d01d01815900a90051803c48902c0c101030300305014495440c0b145080744182c084010401080300c1c0c0304000a500301c428000031030041e43c0319100941d400565020303061500d0101c0b44014020072501d81241103680c2c001144009640b620120003240140e00039030f070002d400c1c10140c100d902d90003602c1d00101408070203e800620318100d282520007a080100b0110740701c0d80c0da400000d0103004244240303406805500c0e140c00086034008105404c1e200040d14641d040e44036038050203000020410b5040c80b2a41e1150040c00042039600710480e00d1417907000400d401d0341805030761401e1244940c094100f03030b42c082241804c880e03000305d0013404003070701140e1000103031751202c1088d214961030102801c00b091101540c1e80503041c9a0400601600100004001c040d0481c10103450070302c01e00010702c98692 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 713263246 1250 713261996 713261999
    0x2003090109033008060301110306030a030c05070b0324030114150f120604050d0206151005090603041202010c020c130203090c0310021801050a08150f03031210090204030c 75
    0x801c44106020f0000007400c46a100007030400706004000c420382014000150401c0600c0011319003401400040f1440030102451410008002503484a4a071001028403000307070b031490103000e42802444007d040303049090380c0c0d80c40d0041c03041201801400599000d103c2030a2100e074241014440c121010500352100842d40d19a2100c440b034141c101c0c02601d510041c0c0d0000c0c0f58058a4081081c0840c00c100e42c0180803d003003920702242400b201d0865a41103500050400c200445901c03080c8480c0d00042d596101d071a0030b8000111a248600700005030800c20001c20701041002e68442900c2010066000b00403604c20128100c0c0c50f070181212165000070003550030540015540d00964100030445d00300d503411107401020030b040401e11080400d6141d8085803070b40700c680201d1f94015201c0000d03c2c1461a14840c1240540900c4000d840c608088030209141c141755124032054200c1c503000242225100ca614014a20340d01c481144c051303c003000803820020b030380010341c000c0e9025241d10000070407429 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 713264496 1250 713263246 713263253
    0xa0603150f020906221406031504090605090f01060f0b2b050f041203020906030a09170c28030203120709121118070807030c1e200309010903 62
    0xc040503050281d81c40d038200000f031200c1d981d0310014208100054104890415480311402c0009029400580500d180d14440030f4581d40f9681100d07440000311000c02c8500241c180844d0081c180034000030005440c00c030134800030440006008030b0418404000b841103030b440e402c1c0c804100781c040c07203001209002481040d1000103182c0c070207484081440345005a10503014528825544c0955061810702000030903c401d0240d00d1a0b0040c440301d10741030a5182503580004a20b16100c02031500741c500b641e034128181004504030300d14018546480c9400e454081e03401140e521610300a03441006090a00a01002e018060070545c150315003640180d0b040c110203e410380401200244803070300b04840640b010803030510700c0d64800001800707100601a000400010300c11403643c0708000070b40e080603040c20040400d038094400d075804903a5107400b280d289c90318070382074039501c81400d185030441e000c80c41d10050090380010302c2c4016480b14401c62161654418140342c4034031400c0c1a490018038880010b0011 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 713265746 1250 713264496 713264501
    0x10141813050307080a05090114040e0c0c0c0d05030a030b0d0c05090c04090507030b0906010329060702090a05040501061e03260a08010e070e0303090f010318030c0b0a060315 76
    0x1070003501039030b24042681e07490480c660b00440f214030201c0c0c400700d101042c5503440b9a01c02ea0b417a0b85010b6480c03921342081e01c00100344000030001da88850000600c6030341e0100a01400610603030241007012040c9407890407540720f81002c0f10803030000b40b810441c20b21034a0914a4000890b800403907081c011801c0400f403041c0c41c4401000240070080801001030104d04c00e00c41c5510507074003035400107215498202004014000940800c0c1090b09042034049440010501034448003034002a4400c6071143c1004203031503000301c040c060b5104036100100005100d85401c458442c5219000800c01030380c544014401515210080c0d04850061a00610002c1c1d5050110040380040c00c40c246070b02e820258003006582e011640c55030000f000140104103074100000900e810071550704001492412400c0426a0390082c0d04005104140984010050344d002c2d034401383c0514201c401d0010b06d00304504000c0c0c00f11000c010100c41404080d000180c003003559100d40c40650f41d202c80428200701994540101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 713266996 1250 713265746 713265781
    0x60b19140a05100203031015081302010e040c080402181b090d08190206060102030c1b0a17060f0f15040b0a180606020f0c0315180105101418 62
    0x40004400101141a6031000d0003c40505840e0b8000d43d03072483d10100900c0c030000c1300e610002160380c400ea80154040d4000340ca0a6004007403240c005030180b030500040b40c2c0d04030200d00c0076400915041541e6032641d40420038a00c564002e80b100c03000d02c05400c200015968007110b2400c0d000b10700131100308560302e5900c001c05849400800d0813400009c03c0e12580902d030700013007608281000c1c9201c40055190103000c5a54010024000fa50a001806160545400b00602d0304d0450b100c40c8058508107075102a1038601074805540b05403000f1084241e60350791100305640020001110b04c00007030341da40220084030300c1101d0510f80d8401c611600d1080c403000d80300b60011680c1c807100000000c6007070041c41289103030030142048081131282c5061000790070003098012900240d0003c521801d91520000b4041000800d10410240190303200030b11036580304200c0d9105000340d400e20040c0001106001c08060070ba550300c040c608511500c0c0c0c420890100b2456441d0203211075140000741c3d40e10f410030108203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 713268246 1250 713266996 713266999
    0xa1d0603040b1005060d0207050c09070f0302130b0316120605010c0b070309240b0306010f0323161406071a0c12040b0117071809080c100504060b1914 66
    0x1030b0b025101c0000820a41106c441c070b404140c0c0c00f040c0c01c002e10504102c04e0088480648461005061800008003c1c2c2c80d590b031400f06064000400340d0324000c2c0d0300107a000400c1c55010603a101d041c080d0302d05e842800ca407000c0381c2c00030b0200100b44da28040588107441c101d0794140c480140c1300701540c1d0391080ca054014016400d16546004140c04200841c6064503e90030400d196040b111740249001d0880314030300e0480c1e0190740203100600c000003043c0b07120801d60350444d44000b42c0d1025001c070b10b1640039440240030818000c0e192040052811240048146c412a2841c000308031024420f00c9654001c582019016104030b62310400720501c112105900880111011407070020034541806c524003050303a08482901a180041006080714408001d2071aa0301019000040c90048036840c0d1945c3c4000042c01c031a41d8100800410100c4401ca503a4403024600740e030a1046007664140007842d0444050f2421070070f201105040b803030000c50303500700e040303000f0049080035060154888903540c1100303031207 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 713269496 1250 713268246 713268271
    0x723071b0609052b06050f0907080c130e070915051f030e240a060503060403050a082a0913110403060b0409240b0a050a06050307031508030a1d0603040b 67
    0x100c1c22501461204c0440900404010442e401c2c41c01d840d00a110008010030580d4101ca0000e01c840c0e0000f254a01e84807a04846c49080c000d072070034201000b458140c0d8180344074400c1e03400010b245085a0400b2903580e03940304154510560b14002c0c0f0564402d2507901d4201c0c50008202603d159000380d201c185103840300c808072030908162040c139000a000205825a81080c608100601c450031400760b070b406000103401404880c101568064440e000e5195242e01f8031400300000b6015110b00c0001440b503060544000240a185900c68090340e0300040703419000c2d00510700314620b804007600500c0410581404400e00e001d1441d21903100804010b010309501507181e03161800130400030f140850045100381049828400b000d07402004860090003440c2c002d4805a004101aaa65028020454005051089d926900c0302c800310000c2042d4002400c00560000000c43c0c06403000029155801058864105010700003d1403540c805004035101d5004404200250018100100045c1c2164000082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 713270746 1250 713269496 713269549
    0xc03030203040c0b0d060e2a0d020c1501090e0c100e0a030501110a02060a1a090711070f0f0605120703091e11011412010504050723071b060905 63
    0x64613519808420a1480e140d120402480507000751042c181c1c000200760a8010b00c0201c0d00419203210362140c480e80840b610100d5000b00c56802501192003619000c0700b030304d40c14403084842a0312000280038210900b0f281101612b0750081c002800c0c2d9600c00010103a4801b280328ae20101c0d18070f484600107a800000d852400000640c0901230110544401300f40241c80740c0c0b02c3d1030001c2c90000f0040032515041e00f40788039441c468403807401c40500b038001a1402d1b1100d80d00c40c0c80c1651507105801c0d14005510402200040c02e20301c0004510680e00e44420301d2000315503940007194980110300301c0c640d008070590302165103940a944200070003846104105e128075100080c034541849514001d49000c1407500076940340350707072258180c40300030003070810785081414070188606103a00500a80b0300072640c60b00030800090013202c1c000c810942141c40c05012500d01c401e035000680003080201c542545a0354201000070103d003c0604ae2400f56880c102441c0c901b604010340156610084680b040e40c1001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 713271996 1250 713270746 713270759
    0x160b0103201521161e0f03090816050a150225020d05240a0e1c0e0a170d0203070f080a09031a041704060e0d0c120b041a06010c03030203040c 62
    0x58621070900e104907200c04041c07044020309164102004840c1c48081103d0100c2000d8101e86c4034071a02c016840c00040c031403014603108509101f100c01180c14003180b003902c00d003003100014003800050702c580394a514000003003000303400340d010300400f00300710382c40340f07685001c0703045aa081040c04c41d07000900021503020b06c2d448032410040a02a85180798109100310700d03445d040c0c850307082c2c1c01c07004001d41082601d424040360381d1a00e24895602252254003640d14440d9031003a1044080504018a54081aa500c0841800080107c000a1a02e00801121500c030341d0020007070303410440d00502d650004543d05d0740c40708020760180303082c2000e0015905021003ca500708100104003804c1000301e8889082c10304146c602840c20312075003041584100700900c0940e41c454182405401d06030b0390003500d03050030325000c01200c1131900610200c0e10640301100501c42e81d10525801140241035590002d40c08030000c2581c2241103c030240030421030b04040f00003078443d90066a100340203030440100030351a0740 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 713273246 1250 713271996 713272057
    0x60f190b0a080a0501050f101d0a18060b070b010605030a0e1914070320010e03032a0304120b070216081e060f010317160b01032015 58
    0x166607400100110304101e101d1009120349405408111080c004030a41c2c0c2c000103034290700100c2c0100400c050980389000303405070825000703603290300105040c100b6a180c01948040346448480c3e000b0396810304800144501d0040100d0b0f04807600851462196130814009550710341c006800e00240a0313035000c01240142c001c0c4414038401ca8a0251407000711007609107001541c1c0360780e81000040e0401041000081c0b09d80842c1d0181075002492410b40c5120761005840c0780003000d4040b505400000303640901e0041d010505d031503007148500781000b581090584e5644d213008034042d0303103900003091403550b01242401c3c40d4154001c9a500c1100d0741400541c0d02690824610380c01106980d00400c600e007592415900c068080818840c0240b0a9203005500e400c0700d21070601c809081058664000d0111420320f2040f68202d0482c3e8050003819030030740c540328450f1002440280ca040ba610174960b003101c2248002e1140b504401080030040403c07031854850107034450211800030404141c01c00e6400300105 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 713274496 1250 713273246 713273257
    0x60501030804060807031b0f17010b091c1e02040b06190206130b0105090a02072010030506030c1201020d2301080c030a080a05040b0301032603060f190b 67
    0x40d62072940701c900d03044000d45100c1001e08020149410000f4840c032214002a188120241038580550000c60b58a0251800c000009070f541403402d0301800410000040c0009040602064034028034030345407000030000404005000400d0034840034140320620030714400107942d441c0001c3c0300203800e2001c0000615541c0c48103481900713518200d18001101d94041c0003840e808080001d42d044061403030340d0f03000c08085c01401410700c14042100820600c401550503a0b90041e4007208140740c01c042c605003005000710391009a480707183e203a2107050300b040c4a4010701c3e0185401034020b140c00680c2804000b0308400328415410351b50350a0101c600c0842c524014076002d600445084000d404094280f00c440d44016003100010341d01a00c01505161000118854080c0c1c2041100b0345030009440100c4091080b0b44c440c1200c08808400070060011071485e071200340300c0300011030f0b203801201040399040303003c1118917644c40000b40460742c03540e041104000301a8542011143e07003840c0ca40d9036009058114 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 713275746 1250 713274496 713274503
    0x1216031110020a11120405130f02162d0c05010309110a0902071704030320100603030908060a0501060e0609040608010606030b130e030304060c170103062f04060503070c06050103 78
    0x41c1c0f80000366130600748040c042d40c0e03020301c1c0c00714070302410301c3c0209450040210315503803c0b82da03c480c01c000c1001030394182d8610110b10905072104501509040e0140401107803a41c81c0c030780c0724050403400101e205d1040020a9030048040c100240b82400650080600e80e80a55411170440c016011036620601904007a000038000142c0340c40306030a107030360407500d060395440240f042044144007085d008964506420b04540d4284920f11045052a05001030313590001c14003420400c012041540180504050b503c0a00c203c41c00355440008480940f4828420840401c017007507900707034090611200070300035000043d1002c03850f642c0e903080a60071503602d644000c001960740c41580c0014500810340040340744890605006621008190588030302c001f802c003d0505981d0414280c0041c002c241c0b002662208a1270380d0959030707490a049025010500e0b40702d2a4194006101c181c480e402c40e1014940131403007424a050a0500c0790580301584064000b0080c040c551490b0800510fa03800340a019610 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 713276996 1250 713275746 713275757
    0x50924010801060902120c03060114030403090e090a0201090608270c10301404030201090620030412091505040f050a061d0f1801081216031110020a 65
    0x751085150846051303422002c4040e004128861001c800b80750360781c0d005844107a00594a4030380400581d90465903090081c0c2800c008000c00c0f05143c2c012100c00210740300500c540704c103542c0e0000002c0c0c60300c1c0ea03210001d0100b09400c80910a07107210b1035510790b000000d040705040708140045500e4603a8503030321202e90664818510042981003039a8030143c0c00c089402c200d100d81c442143c4001c0207958112400036034141c0d40b43d030100b400c04550403e1401c4468490480080c0c20f1909000740600306c0d101c01514090708103a8a40648129808a040490b510501403801c586881c0e803200000d40002c03802c8000c02800141c046904003401814490501d07050301d07002c0d070340e83c03401d580c0828501003940803d10803411450b007009155001030500c4070310b41b00b4210701c40d10501c0380b8000646201d84001e4054104181e00d446800c2c181c1581003240c1a50700d1070080391104100d40c8840d410324840d852182015014048441000a000d80c000d0780c500404403003030300c00c1041340e411264100d0b0002c15400d00000c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 713278246 1250 713276996 713276999
    0x7080a02150f040b0f090414040311190f08040321031109010507030c060e0601061206090504031e0e10170a150b07080714011b030b030604030305092401 67
    0x1820031401c0700c844048292140c245025030b04401068081c0c0e2040186061001070a00786008000c4200d07003440f00010001c00c0440f01d85440d200c0c81c0401182c048000c103241c0940920405c40c0002c0354038141c10074006400d0060010fa0b0342100d4003a040c0e2045594200910010001a008a5040d2031882100d070b8180d0000606420007030540358000e4004d00d694008014140b43c0e640c3c40001c40d2141c40e01400c1c42e0300c084a031840c00c68002d02040d2196003580c040d240c000700302c00b5844600385c4801442a4070910a0941300d0384601c003100c509940080c0814280708000200c00c1401034a600c880c0400d00305190746142c0b0074041090303c10203003502000a20020080c3d20b2a5074011507030703500000c803d2000c120640310281d108074130740910300610a0004000c03441d003041000040484480756401014201e1186950413954042d04007226200d41d43e4043c00c11105d1014800d1140c0343c1d80c0700004000300303802c0e00d45403800e400402002d00514454003805042440c004802040600700905003100b031074056 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 713279496 1250 713278246 713278249
    0xd031b0311060f060319050a1b0627090b06160503030712091203020f0417030414150d0209010e0d12110d0206010e0a0e07030b0601201504020402090307080a02 70
    0x2c1c014040c0110071006030501646440003e0141c9040d800c0c0182c0c1009803100742031082c601001c18a0082070000100f0303601c808032402820040864516450307d5421031625000031001080d01000c401c0103a8182008018202043e0005400307100058000c138a4016461030103204c3d004001d00980d4540c1c0000280000150f001040020411100310104881803041d0703126019000341c1d034808020141c0202d85941c0c006441000c4400074000300300704100c01c41c04410340a0f03c942241c8100380d01d602c1c08820b031022500344500780206003041900da9601e800300c0300c0e22920003034128510b500e0400c00404400411034640800a4000c14003c0c0d20b48100c4007501c0c0c0f402011003054044c05071840e0043c40410031403940018109042d039005090800983e40c2d01040a00289014000c1c5409031040500002c11b0101400905006100070b1361944c01d200a0901301c814015618504030030540d0200090140c403021011074a908684000d001600d01003501d00040e00e4040b068100c54420f802042941e8110f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 713280746 1250 713279496 713279503
    0x60714011a100c06051f060903050607171b090907050c06090c01020d050309010b0306012405210712110a031b05160f050319030f060f050d031b0311 65
    0x45104460900b0b1542d07044000030501c00c0c0005004080790b8070780b000300351060414418400341180d901c161303d20256072504000d103407541c1440305030745a02400c404075080c94404c500c1402c0e0120104804600d40e01c2d5059191110b40c00e08a000c00f18210510081d0180d95545038418022000c9560b03003601d0f203110303988080c2020400361080c1c0295200400e44c4607581d8001c00e9060400c42c85007403440d00c0f90381e68000c09000d4950884031551502900700041070f003c106200d80148000103684519a40d5080d04080d2020b2003903d010300d0700402d04501d032041040c00780519079407282c4240391004091350940d4440086d1060003035100442403002c5003040315181d0500c100481602d101c8403411502d41e1a6502806e50321600c80030000440c0380b851a1018000d140311a2070796070b60700c00300702c0750b442c0040704540603003616404040000030b08154044880c00540c0c06031000b0340b80c4030602d0320142441c0a04000d500d4001315030460920008170068280361050300180501c4030700a0300c0b480c103290503c01c1190306 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 713281996 1250 713280746 713280791
    0x10e01050c01142d0f01090b0a0e040302010e1009051905030d0c0504050112110921100204090501050306060a06050a020a0804080f0d0c0803040308130b1f0b040b030c0906071401 78
    0x10340820401c01c0005004082c0920fa0455007c1d80001903102000b1740071841d100040e130400c14107000084c050008040c1d0544c41020b03000341c81000c4d20b04600c05c040302982620a108000f4049900c88038181da81841c1071072404c01d01610502c1241d203880744203841310040eaa090b82410b0046039001c20208401c1d41c00011082042c90060710812883d8451840d4991306e0156010315406007540d02046c4085908811001d1505020700084500c81c2c0c0d840d14115010754028001c00303107400d04002c00001c10307050011f191401000018a018074590806600721007a4100341404002c52150a02034408034040400810140c50700e1000350031000c50701b41d007a134030304106444610f040001f01040c01010a982c001a60380055252914000c243c5821045812005442c8000b805182070807080c0b003c8180000858080f80b0f01088405140d1580c0b850200d609010f10b00c00c040b480c002c2000050b481c00941d038000c12900360700401c0c00d410500300361604811500c5944060f001c030381d0742e6807900220030030301580441c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 713283246 1250 713281996 713282071
    0xd0b09010516021c0203070c12110409051905070b07030203030a0617030409050a060315090506090d0507320322030c1e0504050a0b120606010e01050c0114 68
    0x100c1501c0380c80c0e0001d40d10080c40c102c2499601c04c1c4040105860b10910850304019040099156280d0f1a00c2440382805907081040301c5818100c20940100d0400b0b02400c030034550004c014107443e00703850441c0d81c0c150400c1401283d8500590b14041100700085024001c018083c0c0e0055841c0d2404541142c100c50254001c40c07440b4008071810b00031294000220b5081d6070340c40340041201d40759105008050013480e04000d048840ca10548581034015600ca0b0701414081d0301190f1007500c42c0042240c6a4040320030b088000b0300108800c20108160340c0d580b07091560260701c8841035116001c030302501c150707603401d4000e4541c10000303045011108441b50150300030149204001401e140d03540302e075070083d0940b283d461421054010000340745800741c1801c0c020100500700b400701d4a4903003007040c01802c0c507600081c45005500c406082c070100000b055807141c041a102c101d4030716181401540c803030300f22007035102442d07403551003001d4030301440851a0701512208500d1500034403040a003201c43e20318403582c0c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 713284496 1250 713283246 713283271
    0x9100b03060f0105010507050c03070b0c0114010609170a050d031b08060108010612330b0412032007080705011115011a0d23090303040c05100507020d0b090105 70
    0x98400e4054880b60304452090030055a10342e00f0786400c1b801c2c0342d40002c000c1e501d8010700b04005080d846602c003d190380460032000304a941400091070b0440c98003806640000350120800303022510980c8801e00c5011141402c0b100030324003aa4407245010341c0c040c50100042c0d15011000d8030b0f05403c049a034055420b900704040039142070400240780c0d040501c1007104008080b40c01c1c5010821581c014000000c9000701050b08180418002c10540c00040c0c04440702d02c5800c20005140c40f000d404c0d01c0a8035009280311509032101d880c01c0350204001c0c924001c1a8840d004510144c5004020480062640f107000d80032151814001410390b0b01c105052040d550440100c1141c802640c00e07105054170100403500d0a020840d12410b800e901603036003801ca003035103010b06c2012207030480704601c0206c3c1e02c8001031f00150740c0d8041c55030b0b0700e07030000b0b03a00201010588041848285085010317003680002a02e80682059100e40000d60010219103042d28070aa549080c8103030302c0020b020305540040c141c1001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 713285746 1250 713284496 713284501
    0x21303151d0f06431b08070209150a030501060302010f03051e1b0c100c0309120309060f0908090f04062603040801050106050301080c0f01050d0b12030309100b0306 72
    0x8654031510010290900780d840300400c0344007220003082c24203011019888440b01c08130780b42c90804e0a07a824003240d0780400c0d180f0001e40d90b10314001c001c00048584c81008181010581e40c21702c120180c002d08241803000000600ba030103a03e640995200460151001180180c654000074140c84042804c00003050300b80f0003040300700c0307448803c10603c030b8000b079042818a940b4510070450b55110708255044050001414481802c0001004000a1842300d42003251080b0100203404591100c0401400d0101c15000d000034a806a84484d0425005004c04200e090642c0c00c11000c8503114603040b0303050200411441c80c00d040c030305c024403094002601c041054130b00f008217281d03620758500c030f08030aa01030b2210700440c15102031041e01c0c024640070009101d5561150b1000c1e000e50001d02a2002e07c0c82007081480306032510168680c511141030312850329010b200d0304202c000d0150503d0b031641180e02c0050551340808204003d604c6031100d01c02034421710418600d00c40030f032480f080310a84a90f102c80e05 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 713286996 1250 713285746 713285773
    0x60c2a09180807150e030c0a0309150221220602100b090a020d0f0906140912030c030a090f1b050f09010902031003140c2b06021303151d 60
    0x441d070010350013916844200c038400101c000908400c0c04807000b14000480d003002000000204d000c0054460b48030202c070652200841260b5900c022402001a4000d1503030f0340400c4440115204419250f521b1240b60403074040026042c0b185140030003861030061401003010f1581404211611800c1032014000b150010001441c1004080c02c2a4001ea60004003546803050769030000b40300740309107001406180d01c81d04140c0002d01c1c0d403140029110500d440000c030704010202d41c5110308103050000506540300d58400744442d07040100388201a41e86d0710075420104218509140c2002e12822010113110b030703030400c0391254228980c0800e005e004443e00e8105a0307582c54810354190f03a012600145c981c0c0e03400d40e00343c3d81c04d880b590001d001c4c130001e034241c50141c1c000818603a0704040c040e18601d1005c06a4400f84924020002d4070341006c02801c1d010300000340580d00100002c04000f503552441c0c2d5100d40750403203548038139401001003d41e100c242d100350502d8240701c06d49031005a00a0303e824840c142 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 713288246 1250 713286996 713287013
    0x3091b10170c09190303091a0301120317150102070f0501080a05060a21050105070c03210608070b090a0f050310020c030d091103061609060c2a0918 65
    0x1607005003111a440003481d50103009003074034007650000b080c0d4020000e1010030840702040b9400164006001c08001088070f620301c2c4003401e03039019446040c5145030302e8820406041160500210200400206800d6004e003141c54424000c81c0807550040800e080a0000380c60800154090107002c107542e6000c1003d40c2c0c01c4125158400e00b500c00115042c1d42d100300140d00481786422180f40010301000003000d40364000301c0c841019109000800c21a02c4070b0a050703540c10f08a04009001410301189524100035180700c44ca40000c0c15103000c260340da115043c89080a0007a0000c4402200c0450345040a1030100c00100007403031143d015110407403c00000c06d48980c1d1443c2e0301945241c0001c1c2200d0418000c00484203180d0807642c1c10490029646400034903c040039551074030030b109450224032240c1d8a200300d0307000d11b4000c0e01c0b8400150701d01001a50400070004040c1c5903040c01ea040317a2040400880b00c010304c180e01004410300c0c02c0c01c104051040310801510b0546000d8003120813000100c424 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 713289496 1250 713288246 713288267
    0x215040503030a200f0c070f03030503071d2209060c020d02070510081f09020d02212701180b010503060106021902040b060c1b0f030f0309010315080303091b10 70
    0x16156550703d601480c49407905030305038003e680042c02301c04000305160340040694050a807a50740c1c1400d1041340c84001401d0b4a00141c05c90b405480380d84250302007981c18001808800b116240072a4201d02500c440c0100c8840744900000b5070010419981030a42c1846290068503048a441450034041013005000420017000c1e0007402d08100f400e2807124406004001c01050108829541c0e0105e0520890194110700c00d000e44241614407034602c0322170111000c52241c00c07008074035010000b840d2004207118440d02800c00b6255a1007840041d044030608075400500d006055980040d45804141403400405030300c40e40454129840c95a9045414078507040180d80440e4049051035840000075613030f06c5442c0e210317461445001624408814006281d6400f2001182d54481800100003403548034884d800c0d1502c000d400802c071340c00980d0301039481900108403034003202154a4440003000d18542c0242c0b0680581c2c2d20555498075200002e42c116440c502007070714141c0040d500341031301a20300d5146 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 713290746 1250 713289496 713289517
    0xb030a0c0e06010507051002090a09020a0e06130f170c061305010e012d020d0212120406140a140109110702040e100f0204230913030215040503030a20 66
    0x1e9011511980c42102920501c54001040c0d840380c501a4204000a60000f5201401742c801c4920000d509030701e601c2075483c0d00965886028400040d00300300700e060741c004545d800b0a041c1c1110007043d6895483c40e40c0300a42482c0d9003564020070b07034620f010302d4035920303614451051004200000b140d03000c0072103080c1200c0303003030911608101c03242005940a000c1105001c20004180c10b001100100d04071000c2d000004940982d40489410309089841d103c0c2203103036220480003000442e444080d405c81040d4400d001e10400182e0f00003e0386d0544400b60250744018010b0b4544c1810b104144501d0b48180c01060703450000c1002c500180e01000143c013a819000c0d10840ea1044001410082442150602030048404020710041440624025003082c0038502070070a001c5028a18140c00314400454018005c101c40071594403105c0d004142c1042400407801c40c05089941c9042d8111070151500461107000a113441c5d15041c0f003420201c5440e0070300030000450481d003040f1420700e03520442d03040d1400c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 713291996 1250 713290746 713290769
    0xf090108100915141608160e0402040308070503040f05030a0f121e0f03051501081303110604141b0108070c1403030718090506101d0a0314010b030a0c 66
    0x60700f44000e201180c03481024040d810301e508005004880e161840c0b040d0141d042c200001803490381e0172524400e0464065144504684003409000e0007a6403800e08010018405403500341ca80d0384010083d0403000046510394000700c1c0a11041038501ca90788090305043c1d0061a00d5240d589a8400e8030061510107040f0054041d406080700c2d110303a191441c051500501c4101d200e88440300141001c891040d1400040c4c038200124410420100101820700016501c168086e00d91304c410310b592074a5614101c0078000f088403561401001485550309c9a4040c201c40304001d203a000c00d0354202000030541008100d000303045005507030380001086411082a1070141d081221600c0c000b0a440c450442e0158244804070030000600c0d4401c2c0c0307031040d40b484140700703044842e5260325482c2581e2054581c10340c000c10400ea00340d07070140f240740303091080345903088048607145041011407003d0941d0342003034440003101510022070441c03d004d1384400002c01d90040400c19038a48a21242c0d245a02a1500525 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 713293246 1250 713291996 713292011
    0x5311b2303060d0203010c09182901170106020304090e0d141303020a141f020c060f0405062a03040303170408040312091a0f07033005060f09010810 65
    0x4851580c0d03c8071855025000b00208a281c80c0080d04c0c15126200365021401030104078001d44103c0e01601609450322842c02082d506038030a5100302c5180d1441c8281007104034900c1e51181100d04e05064000e00c2c15030083c3d5a940d05040300c620650b00714180c0106694800c10b2a0848c07140e21500200c2e00c420003903125501c504200c090007000c0140d0b980040c0d8402400381000c0351804199a400404800468100c400540020000718400140700c0c140300168100816000300c0b4200800205000c002c11007000d03151988640c00100e2641000509507240200c280340b40031042200b002409030f1007002401103081a186a0380105000318280c2012300c1c490f140c2021400b0008001c0668003e10f90101c408a0701c800d030070724001d00c10381c41132082e408203850800410724201d00b804c7c00c840122a012000c90714100651b1000e480c5514049625034001082ca1001e600303092003900a00c40c0e4200f544c2c804074550401c5410403c5410074800d00b2440385020100400600c800000c41b041021038035003012a0f0707907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 713294496 1250 713293246 713293249
    0x106170a02091203040e1e0a05090a0c03050c0315130602090a0b072001030c051204050a0c0602010618050c040303080a0f02030c070201031a0102060105311b230306 72
    0x24020401a10f4100c041541004034101022019109135030018445003140d584441c0d825800f0320503c0c1e00e00140303882c6200884c030381c40c01c15003095034049144001c481580800f40c1d00e40c01e18405a60040c0d41540049003450200d00e014803250000c1041c8000300f200c2810321030045c2c00140f600800081c51180d002858411030344442030540000c094040e800b9840d503125013407082800e80054588581c1010b61b02c00d90f90ba41d8001e200e6a8a540d07003640e01e480c00c1c4001d5071210607600d00080d0055502d0720881c00508006601020603402070000781d070003c24068640300c1c1c0c0001220800c02c8501c00f01d4100380800c80d060081c5020740782141d416103000c00c11078644da2107140062481c00300100740103000000b0170404028000003012034902c02c1ea02000b4a034600342080220310410f540b10750040e000703000104014944a030031000254901c5c09220224088603802003250310744080f0b010105500d5517414480d0000c41540548842c5081c00c10250078405020405a50b54000070b030500d1001c80400421141d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 713295746 1250 713294496 713294501
    0x30e06160c08180a0b0a02070302040b030c150c070f0305060703150803030421181a09040203040c0314031603030c1b05060a05011a0d0f090c0f0312080106170a 70
    0xa190030000d91a9070301d015450000d40f1807202c0045038001c82901c500051214032442c04c03103900004990140c2030300ea0469007040046c011898000d94103100d03181003540c6541d0391841140c40d80607041e4900b0b40e11100000100d051032110380c01000d030007070360580403c0414030118021341d00c45a03501e00050b4401c1d408a0040403081d581d00030000600c00030042000f00440b01c3c0e1420f000c41464170110b80c1c140b05102d01210b20780821034148078601580b0f5410004c915011562140c22030b00900040e09007848200441c003280c00886e015981250385100400912210308901c907085c1e82188007541c90100c42c0b006882803902031480c010201944c40100030005440380307c640303160308602c02005074a1841824055a82e11068513580841c40c9040c000044000b07112a1030700b21200340341e40481c140354041500700d009240301c90041552646450400002503140600c020151150540813600325041d800c02d0145082520140b5042c0200ca80041c4032183e0064000041a00c2500610000c4d58803109042c01 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 713296996 1250 713295746 713295767
    0x30609111b0a1a0907093b0115140907051213120f0809010204061b020a050402030103050d0207061409040506180a0b01030b0f0f09101a1801030e0616 66
    0xf040e1601c403061000401d07092024001c80710a82181c80403074890441800711345414104045140e8607080001c442000e1030f1890202803001c0b0070700200901e00c50061829107516503110b40503102407030018045e2148a601d00c440d008005e4074104010310b01100d001d049803040c05203c04103c1c10090001d41c203030000c581d510480700d034040040001490152000b41c482680481c10001140da500c0000750745810500c01d03542103a181e03030ba41002170100890000c4480e03d0381081640c001c3c2103400c01050f140c03650300044d8021072080c0020030f001041e007070000f4117102c00782e04803a040000003900d19003095008020f071a5034070001c590001c0c1e5a2940000598402c50124007080c114480c5001c001c2e60300c015a0001d861120203880501029118004029248040451056000744400e022040e6070130300c9000c0541c4001e01c07185140b1050340fa050514044001c180441c19660b20014600f0301901c4580140703d02d0540a08090201c43e02d8812007503102d410041c80c1502c015483c8100b011950701c1120300e1708 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 713298246 1250 713296996 713297003
    0x11404061d07050705420402010e0103020703050c0115030210050901080105090a090f03030c02011404212016050111060c160f0f0b070504031a0406060e1501030609111b0a 75
    0x81c886181410801d050190056400c245e140c1c6c0301c1441d801e18505d00c1c8000d00c19a4160b40702030386070100c500198000c0d0003800060781045001c0c000c0c814400c03024030883c00464807681c10744a03010300e940b0410018680300141401040700a00c000549660004031060568000321100c504907503074091801c0041c1504040a40140c0d801001c0b00c061581503806041400c40c240d009000510040b102802c0c101390949000b401c05001c650034242d0340c0ea1841c550fa84d00080c03894401e00041c1b5044030000c3c4038611882200150304500c000f50241d012141d10003000b01000e0030300c1440c1101d0300503510707100c0c24014158003400c00002010081d401a138100314500f01d612510110038049181042440481c29800840354545408041002d40e4017940565080301c1d441000c40d5074503010440d01815401015100315040c1e6114500481c0300c0544051540c031038524087c0702001c8004002c0010281d03852076001c010441e1038000700303140da035034140308840741d941190003014050301c54000c20601d060254040503 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 713299496 1250 713298246 713298283
    0xf030a140d0f1505130603050c040b0d020a0b1201060f0519050d0e1506040516030b0a091d060a02250809100225060c030f090b03011404061d07050705 66
    0x2c80c030100b000702c3e00e48140d5609951000c0d04640050248045a206001c058800c0e0b00c060203011040c5895040a42e4034840030b00002a44001d540c040340c00180503400c040813010b40804c00545c0e00b034005030302c1e600610a0785003010641300c400d41c01800380c1c41415178055850500280c4041580e020303000310740d0f001c121f00c141006001c0c05510a16240c60310095005c91a2100c0d001013031440c50640111170107958207503c24010040d046006600414209011503048840b03150000380d5491a4030990030b07000503d422030b40040d1810940c840c10038000130002102144184040300c80c03d107100e43c1540032069034002c581c00c1d1001509004102d0700500001c43c1d403081d005081c0285044c0e01041070b418600b110841081c45844506d080510f0800074010070000400240e100d4010030300c06d543c28120400641000391a150300c8170090441684260006144a186609840f18030304140c4103500003840301d0044264458200325220002c1c91000d06030104205011501d0030521205200038031090314560709a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 713300746 1250 713299496 713299511
    0x1060f060908060c18100c050a03030903020607230f040306020409060e100806040803060609100e01110102192f0607120b0307150c060504140f030a140d0f 68
    0x184203031002d019055043c000c030300110b0900ca58120a40c0d840300014030000c00002035840901040b180103c00c04001c2145140005e00403480c1400300212a50180d40c000c5455030560801a2900e2005005c50082150b5010082440b0400a05c0f0020901050a06641e241c103001c805803030f10b000f03540003d000300b840000c0c00034034055a58051803ca4100d06014080d5680b002d040f1004c1c00030704d100c0d503407846d0007100018001541482c0255440301e40201081e0404540c84c020032950b0600001034030115403c0000920a0341e000302410100c00d00f0304000707501e03102c1004440480124880460011b110220b4040201446084e444e000341c1c03031820544190707550381c4000c0c45a6450081d80e002002c40c004000030120500c1c030b070080e200070103005401059410b00d0426008850700b030290307049080007007100050001448138050140224002e00d000c04142c0c030b2100c81c2a0030114076010501c8550320400c88110351681281070b03040e00440d005022074070707174244a540c80040c145071081d12902c103162030007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 713301996 1250 713300746 713300759
    0x3020a08010614062b060306290303090a0311031504060609050705040806240a080615040516080405011506020a1209060c1e06060b07030210050408071401060f 70
    0x82c00701d8030152900c10182006005214040c4101e001c02c000b031007000290110480d0443d00703561403001c07072500000354251307803501c81604031500301c0540001c079803440301842c03260820348071102c40024046000d0340c5131aa1140006071281114800201080d80c01c1036510590340c2e0030301c664400500c400b151005503107018a80300780145143d001d02c021051901d030204040500c40c0c3e050710142c0b01c00c00300034041c50f11001072022a06c0383d1900c4020204499140c5140c444d00c0d016003090083c2007620040010341401003003030b04010b210f24401c0e8022440c043c20094626042c2e0740102250b00503003401000b90700e450401a0150503503c40c0e801d00b0080c10300c0000758480c1e001940104860059000303401c90448078404039801a00352007120700044041949801007000c0e05003420f20b6643c0c441300c129281400755100c00075110103510158030300c64042107001c01d00d40c06000c001c403082100301003003100e407410307030b030b0303100d42d5004154018082d044a00c0001c1c0d1903540950004010f8100c66081039682a41da08 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 713303246 1250 713301996 713302001
    0xe030a090801110405060a1107030219060306050f060f0c190b0412212c031b0105010b070f020105090301110a0f02150105010c0201180920031b0903010603020a0801 72
    0x2184114562802143c0d80e400f900c0c1c04140d80c103489008050502d0183c500d08112555098042510343c02c1c040c4610000060340c890030008080b0140507a5041000c3c54060003404030780c580c1d800396010f00c0e4034454446081da65981207503165a05800b0890700c0c0d03698954810311344203000e5070910885611078600c4040c040040400c52003a40300310090014401100d9007220001404045106000240ca808034084080d9030010006200d803e0900380e58580c801c942d0700382d45650b615000e185074000103054124188000e2180c0040c42e000802400a9450101480c41030300c9014809017804800e00d4440046a11940460b0b002581c024000c0c010700302c007070b0b2100c2c5950348201151404111003803600d9094600100b50f01c241180c1c40507090115070b10745001940c2180915104904100c00000c2d690040a0f441d40c0803000b0b04110880060303c0c1c0b0710004000308038091141013809014082c41081164010341c0024801100342c04030300340e2991200c8021a01400d215040203510135103403400483c1101056 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 713304496 1250 713303246 713303249
    0xf17090c040507050703020604020411120c0c12070b07030f18030807180e0606070222060302041404022206121407090b06030f0919030201020d060f050f130e030a09 72
    0x101e60420007612001c3e010b851301c0c400e8203001405a00940b0014001d4900350313004c1a40002d0841400d8900700c0300c00301d01c0300c01c00012108046408808952a1003043e820004c800d540609055214904417090721552039880c1c000b4621001c241c0c03607c4000310320149680007a002c45d4200c0075290310b03422607841c000d40503034001c45050001480d414107c1c41031800c411010320481c2d50b000c000c13140c0d82e01c8000078048107501c0088140e80110420b503240c0341d02410b00c64103503020000c0e51400555141940b04100c15a402c00d01502281410a0b050001580e141040400200246200b060342660480c101402a000d140c0c411003c0310031f0000c1d1501880310200309891003541c460140c804040d2030700f041d0b508440d40108025009070052000920030200c42d0180c41e0410510000c0b5404220380740416400600c56090490060f5008619121003003514040d40c805044030b5506201d08904041c085002c25034086001c61140301480100c0442d061260f00868480640c10143c0c0d0303a5000d2850003404043c0103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 713305746 1250 713304496 713304499
    0x130b1305130b040c050f1803010b030a0c030c05060708030a02180604060309030e04050903041214161706070e010c1a010b120a051b2a06190e0a030f17090c 68
    0x40c802c11394062031050040340d840c150784941b000e003443d4040d118810498000300c030040d0550750b10b52a409840d0b408102c0200000c0c45450510841c81c1140f41c505059049548000d001c1c41043c002100090b0261098940c8903901c0500161640d120040c10700441c0e02c400e102681040c0e00140c0818407030b5250704640c08084c02500e600f14090910300500003266800c861407100c0b90024081445400d4816a4054009000d40a0030740c100140da0320346424007110101c06000b09075400c00400001c05a882c03000f0360b401291000d883d880c41c0c450406002c00c0450b00c0c0c000c5c10044003444000c2040980200c2c048031040c9a44c25440a41c0c41d40079240d12584078080c0d14045549040000d1500a03550180a2040c0003018a21103401c84004a1010300d4000c0740004004101c08400071440080d44030940c0c0c41411010010012800c10780024020f82c40c04850300f0902e503080c4841000f0410001030a15071140c0e140c034107400c20304c6c503006044401403034030408101460880b8050080c0c140e40041e404050550 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 713306996 1250 713305746 713305751
    0x608090a0c260f030306060f0d060f14010302070c0513020c01020f0705191a04060e030d090c090b030c27010603020c0c0f30101401060203130b1305130b04 68
    0x4103901207940c0d8444190031001131384100b00280c0c890405101400e500075410b0001030501c500d24240005540041c1c01c118043c11020108010780690b0a4604240d1503003030900310300e00b24094840f00441025805018021003142000d41107030383c040d5041b91541d4038600001c548850300190510450f03401f08806968510400414100c59444512010303001a0f001ca070322010341c54910500300310b9920003001540c0540e038402c1d809040c800180004e145035006c921002414856600d030003440e2280a4100c030501070301d00b11a0a01507240043d03004d098403004c442e0342d61701000c800c02216891031440d8484102505000c00051403a4040e00684522820401601c4048060710309001e50350750444c0c565075201c100c444110344144d4070000741c1a81c4d038410028028050340c8084005207091202c120100e03071160303a06c03c2e2a560b80b45180001d0f001d001544044c610701141075040c170482c0318481c02140c202c0c40000840610540a05501800510016003510001d01c01c01050030b00600c4a105002d01070350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 713308246 1250 713306996 713307059
    0xa11160201110a051605011817070510050a17070f0509130e0303250c080d270203101802190807030c0801050703090519020d08041e0e0408040608090a0c 67
    0x103000b482a815041001310f40d81e0059490200b20340c1072784001c403150180b0f078043c102021030640c641c158001580c04164071007568805400760028501100b00d10070703400a50440043c000d10583c0010300714203210706031801c5070b1540640000111419500c8083c90f0703241c3d18101e50b40d28017040110285100d000211001d1000703141c101c0070701c134400e00b906403000c00065008200400040c4580050090441d10b40070009080c003112520750207070340c0c03101c2e0f80d00100d00641c4607000461404100704070429840c02c1c01808442803024412007288101d960080c07148a00c3d80d914400d24007801034000003003062001301c40040da502e040003100c0c094a409440542d500b000001113025000b4081c44000035400801003188240000b00306912860102003264000f5444010320040354440e0054400707800801406070000604039a1914140e00541c0010300c0d1400d0001008041380e007402c10760b022503905d400e20070401e80c3d602c084a4242442e55000604040321084089a907d07540c80152501d241d0b12a404030100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 713309352 1106 713308246 713308249
    0x209040305072f0406090e0607030902031c12060909030e22060306061508070507121205072724020c1e03060a11160201110a051605 58
    0x1c10410381100c49260030712030032001b04460101003052064422403030342c56246c0107188000341a03451030308405544060007501c12900303050090341c0003003c2502019018100000580c183c0a2078aa404560700700c09124174940c4507010749440440c141c0840c108501a140d407042010080800b54502030200c0341d601494018502c640070208026040c000c500f19441c00da4204c600c100a0410144003189030441d08803600d0f5a003102512030100013081d000d559000c0303500280903505240c242004420380c1d00c0300034450407000018125060114580101d000040c041c00b0b140020104401941d00d60784030b810101c030105100e4015242045a14400100200b240501500c070502050b6803400c00791a043c0320356580241050070400c0590104d010316201070068040c1c04522038107011100041d6801100c00c0c0c00e90340075103400ca0352180aa4a483c5849a00c2c3c1200201030048850703000c03505 = true := by decide +kernel

theorem cover : BRFrame.Cov 713129496 713309352 := by
  have h0 := BRFrame.cov_init 713129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 713129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 713129496 ≤ n) (h2 : n < 713309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
