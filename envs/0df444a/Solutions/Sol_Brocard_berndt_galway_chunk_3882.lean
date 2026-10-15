-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3882
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:56:56.315995+00:00
-- url     : https://prove2.me/submissions/3dab2e32-816d-4112-a675-3f0a8ee76d35

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 698021582 ≤ n < 698201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 698022832 1250 698021582 698021609
    0x10618200c1e01021e1308011b0f09060503071d0901120c15080402010c2d030314060135100815090a021005070222060b161b 55
    0x41c54a40d559040032803021030081c03108508481ca000c414001c5a602416082064030800c00000c485d90007500400303070120490400382c802003a400024817a1000c1203015a00c4a54080140d803801703065810244810010401c00b0401802490b030090112908480d0070319041743d08a0b80007020900440c1c4004915034000c2100300009141d10044098120030360194440c3d144043e03403816101204004c603440040410b900030001400741d0700030b186500d002c038042e1811442000580e604032003145005000c01c020006d210703560400f4550306206034003001c51300c0c030200100c60600e0400030f4640707025805145c00d00c2441d9a56520b58013001c8030201100300d42c4d18406c400b64200013103004941c001074082c90419100b520203c04003070000c5203203103009112100140407c064a90240181201041920302c00c1c00000c02c000c90060702e40701c40405032110a0480c04105c540688624015138046078091001c6c1c44042c000e409070101c904a1a0a0385540500c0c18007031368200d2110090364080c0c0c0ea012200c0440345 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 698024082 1250 698022832 698022847
    0x7230d03050304020d060c020f010c09050a0302210f0109060b0f01140f09090a0e0f0a150c03090b0f04140f12090a121b0b07210513060c120201061820 66
    0x9c1d02c45200c004080c0284200e8144200448007a0316520400354000e0302c1400410241c1404d0510021250b603900c0c41c0c0c0c00103600814a24582240c2d8070044546a644000d080140034881c4078511030008116045110f107070343c102c002000302c5d43e5210400106400001e0b2104454100400c603105400c000d40540e9952601c04160070061030307100600c084501a061903180314102c049602c10170725a002040300c86950810f000d010042c030f0961034850070b1650318030b19103011409441425105a4031856460301c90714003468240323000d50103611407240b10b07813000500042d40c50340424525071040c504560913413210040400142440c0c1315901281007400c0c00602071040c00a0301d07024004245010210704001a61007100101c2031003085400740411110205405560700c01c0c0000582611740c0b0b1500c5810306500c04000e001c0c0c5111a8008004241c1c120030000810030421210307000c3c800305000800529242c450b0364050101c200003000031066460082445c0134403000144961940642c402c50386540e00e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 698025332 1250 698024082 698024087
    0x52d070b0d05010905220c0911180114070206090a030f080406141e03130b010f05130b03061803070b0c0a110d050d020f0f0c07230d03050304020d060c 66
    0x42801201002d003440004140ea40490181c14003407801d0183e040303480e50441c0a01d40c6c0200c680e040032901c40c8804040010350002a01070a00c0e00c41080c45100c0d940d03410540042c501ca201d01030120b0600109608090851103804160750100d40c0603205641c1d1002401c0c001202c1e01c020b500002c0c00e4904806014003805400c002600540e003080d2581071903a02c000114208034000c00343c1d10340704801e0f020450038100000c00055504407204c1d003558000e041e029520000ba900090704140b00c1260301c407800b0445071402e0310078001001180f4004208138001d02011989814000f80310750409031001074150a5880708000b2070342010b070004400042c03414800c06544807030380318109010000b6410902102200d00100d030608100c030943c0c5074503103010406048000039420403900c40102031070612032aa95a06d003074006007030f031031003040182c00102c2c00d211101510701010705c0d082440c010042c10f58200da4907085e1200c1d4900781c00d4108203899a03258400221160f059030b0008104030b00700090402150b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 698026582 1250 698025332 698025337
    0x8010501050d021b1e060108060402030604120e04090305090102010c080c090904020a08010e100501270c0903050a0b010608071110110906070c05090106110705040c110303100e060a03052d070b 84
    0x2c0b941e105880462340d0b0340314036998034041a10042e40c180c1102012800150303c0720206500b0014a081000200d100c07040050f00700d840b06801600840d80000d010740f855a420b00c61a102c1541e641071401c46130030b012004600ca40a508030140c041e4030003501240940d41c41050f01c1d0010002c490090004001c888491500c41005a03520520a400c083c00032910310802e5031383c0403e10711041c0b5940d40a10944450b007025002000146d8140b0400c030f180480402c400380140441540580f400c00099450010001c18218005200d0745c2000005d410506e00f40c813010070384014001c1054808078861615141445048c46100021a4802c0d4009141070400543c13048000031150210707071b10300d44c6a0780c0c0c0000fa86c0e148840b550485440d080024184060719041d84610210720383d611340380312450082c2e50300f03078a1640107660030198081410410401c090020514079071028098484121b9907145950381c3d90344001c030011038048280b405404810307226104544011100c01c03c0d0442e0341480e0340305401201076 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 698027832 1250 698026582 698026633
    0xf030f041a0301050325050a06090e0a022502180a0c02060912070611130b0d20030c1606020f09040e01020a020a021306181b08010501050d021b 63
    0x241c03540141d85541480c000240c1e07040781d602401601c2c800d049051040d494042408000d58a1904220b010801d41c581c030385080c0c054965501c84d0101103080403051402e600004003480c0106004100800000c030078403034a440413103c4403224003c141d80c24400500030046449000c0312220641080007040000f0350003004a41d04180c00740c03041c60f00c0d440d20064948401e06c41981802c1410400301002881d6940090101c2c4494561103007422004400041000c0041d4048010b5403004070b400d5688000d548240105c04202c0c05507088084080603800c80702c0d00004000882c00c1c5000309044910148031544000440d62203001150307076514404001003117411068815003c2d03454401c6050072000c05108440d10005103030010916101c00d45d08012107502e0084120911546812001405054400d10070040d150960f4011a0031440460b188510303403241500081086880001080566023001c1118001c4000c00310150352070000521402c003c8444850001c0148900b000a01508803510303d00040c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 698029082 1250 698027832 698027849
    0x10f020a0509180f0c0706141003020117040c0303050c0a020a24170c030702030714060f0a02070c050103020309031b0114130812060d1217072d020f030f04 68
    0xe090501542d8903040000701c035080110b604c0e10002c01c0e68082d2010140420710b128850118540113a4000c40c080b600043d03c10800402c624001071045607009101405104007140d186c05c0645810344441d24140710710301c0040c0034818002903030380d4040001d2009e4030384503401805a50712590b0340c0070518201074a032062620051098900240750620502c0552078040e40b070704041940380c49400c5000d0700c0ba0710280100080d03110402c6860002240100002c1d101803032000940b03480d142c0114007106202004141701110780c410000710002810481104c010b0303410a280050300c0380d4030040854a944582c0904459074200c4580302d403d41d181c150040800101060260503040d214944040324214034083c000706010402e000e1050200c01114807030703500400040010303204803079684888101d540c091034858002030b00d805480380049103240689410a811b803a12203141d00c8031144204071100d142080091340c41042c10f1300c0148503c20800c9005111642041e60340d2501a03554181c00750b03200344900c020 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 698030332 1250 698029082 698029099
    0x9080307051b011d1002071a04080712080a0c030207091103011e08060a090201050d11091e150903011506090312030b0603070e032b0305090726010f020a0509 69
    0x901e5110307002c0b10a4280302806104640c2c1e101c1130400400c0c00400c0e1036882107204482d00016007082c25040401200b201d582d4407a03903541801c492500f04201a002410144031806884000034045421609a61018609402c80d03a01c40c0c6400c03401d0081e1580704111642c10f201983c00440000c030011412183c2c07030101602407008040220007d42007601c668070b03540d000000002c0f600003858114030032607441494040c2c034261407100d2070070898041c0c4504201c0d002001c00d0303444840c1804251900d0f980b0711202d01994509010303000810b00a2518610404802d01151000e015102500440d40e140c400408203040903807981c500038044409440241e400150f0000c0196000d8041d102c0d20345601c1e0058499495603036682d030103544440584006540521800c880d00b80d290104981800e0001d1850310024411207203c080102540c0000d0149141d541241c102000315412440c4610004400c135110100b000a80c400e00600409405541040c0c050000580d02402c591000040c8009042242c001c1ca = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 698031582 1250 698030332 698030383
    0x10e1905060c0c010b06041805070e0f0d02190905060a060302030103030f0f0c0209042004060503030403120c0b01080c040f020a0f030f0209030109080d060510050901050a0908030705 80
    0xa10424181405082a040640850a0220742c6802018128040000031070808069004190594002e60095504400020361940d000a05010f0b60b500b00710b96103012002c001c5540002403030030750b003143c5442c031a800c52007440c0115102c10059405402d1440f00b0301d841250b4417681100540342c00c680d5140301c2c0300689000b140f49400303031090780d040c2d0b5096a50031070825818101900c03141c0d6000c03c9a42072008072900e107030040c0e4400c46020b106910612000f06d0800420380c1484800300d40034001d0f4440da0402105209680300003084c1e40841350050381c0d00c07509890000044c0c0b288081410b01810b003400e4400041541140010400d02010040d030b420048207407580d01c500224010600c609001a080400c804040d9209030001d010118002c1c40040c500341d1900c00090844e0035112084494000101d0042340c404c1440c440c1c48004c02082d24109120104000010102cbc451060f80da8103001c0081181181c06108400c0003001d85160011290381d11001e003011a0b940ba0040b52603101c4182c20882d14 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 698032832 1250 698031582 698031613
    0x1e0e0a150f050708270306090708070b070b0a0504030512040b1e16140415030516020706020a0311100c0c02040e07050d0b0415020301030c0306050a112a0d02010e 71
    0x21803c00d0740041c42c003401c0541c009a0180100461141c2c405d040d500d00044540c0b0f0b42e002d001040c0240800c10044c07088901d85100c00703041250560000d15955030034844a008111440d484551040010100081a0360340d482c090b41c1c58003d15507038121005000c0100000c204000d404a8010b0004111146402d8100c540da041c0350001242d18400300000001808002401150301c00d09003002031460794101a1903407401c140c154950440600065220400d001101092001c1e900d081543d51015045443c245030010f9510014000010708000d017640480c0400c3c8010300c0b0384100042c4211040c042421611001009400301d050246e10a92071f011003060311490002d08102152800713421504002560380310302d03030350710002001541c0401101160249000384c500c002c502031031244106452007404c5041003c1151030080004a1031440d25030306404003848801a102d0705008025081a4542ca5071659032300405071802000e000d101d40c00c0790305410354064003d090314070008021100d002e80070035042d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 698034082 1250 698032832 698032837
    0x70c09050c1602010c030309082101050901080c06070302250612060e0106030b0a08061f0603020c070b0a0e04050106052212030e03120406030606090905071e0e0a150f05 74
    0x2c0c085040e55414980055020f00140480f09001e0305002031200c0441e1030b144c1003079104214006100440e000002c0c040800808458003520b0180d44003a85581810482c40ea078031381300040c8070b11441c00850705108141c420072800b0300c0445801d00a01d48100301c4400103440c816070f4041c00000c07520b401010552a10288200b504503a240815544d85920341403042d00201144000da5403c0000720001051100007000458010444619007000c4041018211100300b20590444170406004111000b4075010006800b000e4814900810342c3e5024010826241d100c0d001204503005800e090000544a401601a180041c400020350b0180380d0408225580250180550201d00a900c85131070080380c03240c5902559103101034103c40449140020b50031454101d0b50100c0c00203510391600303000580c0c0c840d1340d41000b4200c030107041c0164202240060845a181c3c59001025495041015072182c0b051034907603040400030b800c0d090215220100c1150311846040d0120100c0c54105030303171002511035002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 698035332 1250 698034082 698034097
    0x807030c0f0806041e1401030209071128050f0609010c0c0201200102040512010e1b06071401110d200a09030602030604020d180c050f0a29070c09050c 66
    0xc0c0c0010b1560b52000308001450200c460003150b024010700840d5a0103540301e009400c140c41c40e5540300540c9140704000e601580140004104415a0381c031075440c15001030190920fa02112119002c244007200d0b11100201c140400790062090a00351605100e01240c000d009400c604024808400da10409881100b04008000c0c00a4900a01c81c1c0c1d00d00681c0c40c1d00642001d11600140c0350070350301c0c0005110001d210040325600d0350346200c8150301003020032140340070541d100440305840400300c001800b07900920402900042407030380700521001c82940700e80302c021480300b6000c4d110950840c2400080480c5600f5030480ca0860300e01c103580c0c0d00084190b0300b250896030345c0d025100d400c0d5603a10010790409040e03503401c950280030400e400d84081c003038500e8080d030503850b20500501e10f081c070766600801c03580101e0107001e1a00d80440c4c1901c0740700174182a41c030ba40c1da04030f14330f1241c0c2a40005070095400a2201706502180b407001b04154024094101c1d0541402031000352140c2029141e140308554 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 698036582 1250 698035332 698035337
    0xf020c1305100b0a0f4e0b010c1b0905010f051908071a1c1e05010e070c0f05070b030403092102040c022a1215040201030b03030f04060807030c0f 64
    0x24001c4402c00c0c4980f000e040030f04000c6403001010310b110b00d0507002c86c2030b900d4034200300e1402d0a490b540020014003c40c41d05061035107028010041c0b5003001030701c5d44040100140038046048181c64000c035400c1d80b4040188405070080100c0c1d0303500c101c0e014008945004a45c8100040200300380c0310310310148840e050360f030814060001d4034a01120b10b01c0350505161044d03900c01c810701420070f08001101203044041d08101e004207405003000c0f02407202031110003000099900d84001130060280845480fa07103d10242810345882c089030800c8450080500d2004109226842c40420b070f2000e5040654000e034030a8607030b50480b544410819684480c41594a04404c04c0b0251820140c68103030418600c082c1c0e28010740340d82d404c00c4030076080003040398101200380c80030583d0900e000f824020540380e0154000d102400c1c61904c60701004800c900d020b403010b8100f507200c00024400390703410300407074082842841940790381d0350340c0e071a001e800c0c0141100d052002c44d25100789a0079681c01803c40c2c01e900f52059 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 698037832 1250 698036582 698036597
    0x414010e0f07090812031005010809060711010b0411070605010806090613111c0b01120b0103060c03020c100608060114060703080c040f06020c040c140301060f020c1305100b0a 77
    0x1501c810340c0035900104040d04001001e4400109000103200300040c00105000c120341d20b01d89881c0703002011190394081e60401008030100807942c480802c0c85a0417035824900303003016030044010640942410415140e01925208050f112841043c0042103603910807a000c2c4440e0782d031130711895143c9070b08555a12584d0440c0d4001382c2c1318903030290185030300c6128005008070300e80100003080c1c0c09000d07103c1c0b071000c161580307400c9414042c42503600c0b40181060550004c00800c56610340e01c001c00f040c4401841203856600841d40341d406034040c2c6030440d21034000ca90043c0020f61044002d00f1491180820300d015510021a010484000c080e42000018040740e107000019507085443e1034008010a80e070510a10010850300301c44e90440c002025190f0051076071004880402080350300050042e01030080300d40c04400c0400521703050742c1c1107502d0344c10711002c01c001401c016820402103413103a6600c01c03078410b41d81000d1400384d40654018003002076103920b810380b05e694144c000d20842482c5404140344 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 698039082 1250 698037832 698037841
    0x18140408120a14011202030f0304230a080303100e0f0402010e01050a1404061701121109150a03080408011d030301120c081c080c07020625050a0c050414010e 69
    0x3841441c98000c40d01200c0014860342d40d002d441010f02007078202803040c1c1000741c41e00c010341c6000c000c090040b01841d40030b945420f241c21000e02400e0030b62038001c0b5102043da44511103e54031320f02c03c0030080c02c5030021340e80c1d00c0c501ba103000001c003803030340c000c51054a402d0404107484165082085104560686901c0c0d0f003200034500544843c1c21480d00441000462040151680c44c0340024100030308240d1a9800482c044407400700c0700381c90503008050403180c1e10030804c0110b28286e0003410031403404c1e100303d14140c0f5242404a0825811040702e03401840700b10000003003000710360041049403050002041105400c807090f00302004810041d1110368428001440210348840e01c00340583e215801c1c4980e583d5584a0090400800f5144915034940d04007540d448c40350003407a200d5104002451242c0341800d19400a085400740f40380e0f64110482c260b00807400b03540d01c0c4005e485c0554100c1d00301c4045510768607000c250080c1038060280201d0a1040e082030500d042c4400506848d050350480580b82d44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 698040332 1250 698039082 698039107
    0x61e02030f1204080c0f06061e0307030323070c181811060c0f0610061e0525060f060b07020a05100c02100804032d030c120618140408 59
    0x1010307005880c1504100044541c1c41c604014075861b00c008800a00100d03e802820404009000004051440e80a5800040a5601180b84415642d05040c00d10070742a84003c030700c2e002071130070b0003402c07010000081e4501840049003100b030803a00380746080035008040c4240e40054520b0820501d400f520552000d000180f484041d0b0410181c02030043e50030b0400011070b003450f10210724003080054010b007050246020105d058000501603d04023500000b01c13041d28046c054140c040401c003002000304285804207c3c41a1301c5000300d0318078410b4640b014039420040001c014144405c2142817a1481c0000d10b00102d00941d54819001020001c01d41d10b04428050700d24514460341c0c0030009820005401070740c9991030301c1c4c44486507590701c40c0a03281614014107a5200c0007030f08000701155411204804004c10208503614050b0319000c00d01454100c010ba804414a40d15500000e040c0040410314044222002c20300901e1902c0903c40205690041a103074038055070043d0258500b0040c3c85410301 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 698041582 1250 698040332 698040367
    0x50306040f140d030504120203070302060c030912040617060411160503160503030a0e0610090c11010509012a0509010f0504210201110f21040f061e02030f 68
    0xb4040c1c48110780740001c1008540c00c140800d141180030940d11000d00c42401580300980e200040c280c00190328082c041d4402a40e90740004060300c914190000005a006200340003140c0c000c1c070030398010394940b511224080c0401c4104140f60044d01489000a0764078038080c054250398180b1207170011b01c1c00001103a41e04d8001100035041e901352004004100403100b840201070015800303000516101d0504000110541e1882000301e4150b42c810300a1000025408980310100c0d0360480d000102c03120b5040701501d055250445e20f040551804040120380d01040d0400c840003804410201c4005031215448459040e030f907425980000d03c1130001c0c5005501892140c500b03121a07091071400d01e0364031040d5100b000c85a8103060341510322004903a00b15600700d0960b07450010362402802203c0c1c0400681642c43c0302846824001c1c03a03803081e040a0810510085402a01c64007030138610064450700007074004114141d12100e05800441d906020b944040103031407004100c0c40d407541c81c1a0b10201d8000e80324 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 698042832 1250 698041582 698041613
    0x4009020a0e03060a0e0f010213050607061e0515030f0a12140705010b0a061e031d0a0c0e0c0a020c06071502310806010314010b0a0b121005030604 64
    0x70001004003a54007000564824030b050113010071714418208001c0e0a100360340e02000c01c981e006010b48840f07044622015000e0f50b40036a045502c2e0390b41c40c20002c000d000d0390b442c65101d07044010740d034a030054600d8000c1485907400b95103148001c9030341d0040c5555428041092051034011084907c000b1b0000024a05800d80901c0c1409109100c003411007a01c0d407150750112010381d5202212000ea003041c03140040200f220317040152440c50b5140c130101984200b07142940826584403282801801e070f240e00c0b01d00d01c030150022503190303100c00d250003501c200c2d040c0a850b0000340071a0003e09602058002c48049500300c0d8040c1c64805425400d21241d60008131040b1055603018032009960800707807016000811070504810000c00300907180c18403e41e418406030107201003060f0184034200c800100340303044951040c01030f0707000068540140d00621040d40299408001d100300062001401c00140150700c00a00e42e400c000d45808500c00002080c41c450640c0603044240004d011445564030503286 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 698044082 1250 698042832 698042837
    0xf080a020f030a12020f0c010504061d151c050105061c0c020a0b07050d060f14060304020f0a0803030a05090d0c0b060411030c040311090f0f040510024009020a 70
    0x70f4080e0341e41e40800108400c00c0c843c01a80407411411014904101107030940c1d9007801c0c0035181a04000d80149203020306501a40464240c1c580c010303040d110314810384106a0300b21402d039140c0f500b03a118a81c01d05e0312906208032142c100000409c031444c0132011258848000c41c9507404aa07541d60b0381c0c50180003420448000d5004508886011800d510982442206e44d9a10941d44d9220900600100e49594001a4003451846410700440c40d1025040d0003001041310110789907903507440060300c44440012019089064031600080c910800800b450060217845070901655551402c0c199550800e00070b11000100745002580119280c101d400350811805031021501441081d00060540d02c255000480100002010424009002034490003100b045078846c902e0300705441c1980587c6c6d0058400f1a0103002d4401282c20000c3c204240285c0c003aa441c000e6448001726810131120080003070740c03681d12140745413501140c1c50031b0315080d03076103000c510280c05085402d00c01940020f420489181c0203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 698045332 1250 698044082 698044093
    0x307200a0b0703050a1b120f06080706020d0923091801052701140f0702031b0706090b0903060a0b0f280f0605090d02010c06090b040203070f080a020f03 67
    0x401e0301110901c0c4282040d4078082001d0070100401d40c1201d6170128020781480c046550250001d41c00241c2400c405c200c1c5201140200b840040725004040b40d6214507032a00c039050b0001109500891020020b100b43e03104d8106043ea280045003620350300c03400004004010072258045442e01424068010310741c01030902c100311102c0c5699007180d000b95074032030962400100c0c00000503000d8001b200d41c800000300030310185007501d01d40307914001c0c0034181800c064050000100790a1003081540c220b0781507030444d0080c0705802c1c05165103440381402580005040c40e4008030391000806c2c2203490381d110150042842c1c0d650030010a005102d88500e0719848a8a0f080035041d694030030044c40c2ea541848400208200d02050440c0c0d1542c0165020003e1a01150404c1003903a4000003902c0c040302c419602d40d4280000b620040380d800c642c000005180354034100c2000180001680c505101d10700c250304403805503898110302c0c2c803c3e03075480c4120341d8180c0c40403081d40300509010369401d4201c84040d0032902e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 698046582 1250 698045332 698045353
    0x3060c0f031b120406061505160f15020a0e060c0a0f0c09020714010b04060510140f040e070216050607081308010c022410090c27051203030720 63
    0x500a600c4404001c000103d95030500050050900c9410300034038a69a4500000c07034034080140507802450350840310b07461400c50010510069034421765230240e118a60740510707003044144400941240c0c0d40e0000166410b000b990050814000315149594440c00418100c90740740e4548202c13000040d811a1268030000c0e002440310018009404624030a1051050700d06103507000c1401c54858851091245091242c200b00e60b4a030402200000301c3c05280c2500280d55280d0000e80a1207807980504011100040011744c800070b041303507a0300802d00c2d0f40c05d59a144110070b031f40501540c441d004035640400100f1505001410b42001005100a0380400001d03565461910600710795451010001503002001020400308400c1801d0042e40c00c65039101c04141800c41e000741403030002e40a0503001550750040b208080b40640090411000825041011b980b91201d0708000a9002e00c600c9002308175841398803200200100a03644108441e54542c0b52022010301c4568008149011809040c0640315200 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 698047832 1250 698046582 698046631
    0xc0f1211160e130b0615070206070c14180c0c0a080301090b18070c06050604090f03050912010204080a1112070f15020606010c02010e0f0306010e040b0603060c0f03 72
    0x4480c54180300701c1e001495140c8840007090400040001004120a0201d40b00080c188110a50001e0040c1c03510440c2c03007031072096545c061088134801703540a140843e90000300300141d64010103031041030b4100d201c54400d9409004050350102d0910b06500580b90005842940c1c1d0b030042e250f140b200300102c2d000c1c0001622101c0080e4000c0c8c100104154844100410714100000c100c60060b0701c0d100f00a0952400050082c501b10340494010a0a074603040411529500c03500b28036601a0070030421401449c040c43d0103081c940c030109804e402540b4808040c1c0040d203061099074200c030101c101030043c0f464160380e922013900300c02c3c40081d40000300318a1204c40f10310070003490026244031005a007456040c90108040f0503440c40c1106e04551000d002c014050b40d003c0c100e03140082c0e082c00c0c5800d09007100c10000d561400c1d494802c60b090710840c03000080141010008070302580c003030003403510540c4a180501da141c0380c04568080010004101c440d01544000d0b00840c1c3c0000104104405020b942458 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 698049082 1250 698047832 698047843
    0xc09090f060718030209040204110a02010507031505011407020d05030d0b040f0615080a0204051206041e0b04170f03010308120f060109031b03020402160b01060c0f1211 74
    0x108654044111018000c10400509401c84014248240c010040e04443c4044180900000b400768070008041402c44d121604041480c80e0058402c5403070303204240d8002d00900080b42c4400000c0d041010b51050b100304205e03c44203441c2c041c0e40700392003490213219511055005440413600400e002c2c0241011860520243c600d000c41a000810902880ca04100550707501c42400c86080d494003008101104200c40c43c01108605418003582595030018000b0090242d03510140d04048540c010f41181c820100d130591080e403156941184110444d0081603084007203d500418840f032210201d0003262003000204044071001d00b60501d030001480007061250404e134001c540002003c22102a15120b040082d40c4c42603c0e0103046410b0b1500c100020728150320707440003130107079042c1c00343c0783c94600c0016102e40090350300503109640d241c007900d41c0184000413901003a60340c00180000861010300c11044503900380d40016194001d015680c1b5401200001c14100005000207001040c1c00782005104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 698050332 1250 698049082 698049091
    0x9090c060307111606050a0e1311130b04030b1b0408011503050d03051b0d020906070c05031911010302030a0e070611070504050603030403080a050f030906011809020102060115020c09 80
    0x54103d540c0d80070b078040a00e4000301110640c5100c030340050900030940d010003640c055460500d0b01e1100540001e021800305280300d0b5401080030b00b040200320100708020000c0060341031088132948100d07a52024180a07000b11700000b01041c000a0100e40e1403503640c1590208142010701862a2030b5803072030500e01b161342440e140c840400e00c010040080c45400c0c07140200900482c1030601c11844c1c121102090503141250703c84040c4000b2417500840c00309641079034800c60025040607039444c01421300780351043c4103101d810320a00ca21810b60400d00801300c200484140c0c040500003c00181b14015006900020158a44140d5404e032803265103404115040052100d80c40d0000403688980f85181010700c2d941105001e58109001d20041351800000c0701d0889070415101ca03206c1e00d52800c120f071288580340c140207c400022061140c40c00d00450014100c1d9802e03004a0355010030313801840c080ea04040400707805a0400001000008401c040c222305c00289803041e1607000842000103514071074140c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 698051582 1250 698050332 698050337
    0x2817010f0c0201091a10030605190c1d04050a1812080915010308030702070e011404060e0c09090702240103050d08090706030e0709020d090515090c09090c060307 71
    0x890240c040819208030070700e180840c4003d002038100d640740e00030065641612942c881e04800300142c0002c20a071541805198040e00c240131505240c041a821a01c3c02881c41620910b000e1032051511701640078081c0800002c1049410b282c46001000014031004080c2600542c441e05004200c44500258510052203000c100c6c905008030303a0020701c00c03440102003039003581c4098901c403140050710100c241100d034408081ba6496407040c070100d0a1103000e80c400e041c5c078154840003040ea07110181d5040886107060740d040010725078801e0b00c1e1a81c15004c1d41d54440d42d00d020842142141008022a9404102801151500310200400c41c0c041c5c0300500503241c0030003010006004002c0305221a45028549240405490400d140d5460300c0d14058401c031801d05550b40d20305c0b014810140041ca004104640045490301d008102c0040074080d401c50894042c005c100045242c1c07215100320b1809422400000c240c40e900400170312882c0038001d000300c4618440c0780500c032401d41e10030780158421042c6030b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 698052832 1250 698051582 698051591
    0x1807090b0f27010f080c0f06070501090b1605040605040b0d06470f1303051c0e010c050c0d0f0b0c2106061204021903050105010611010b281701 63
    0x801e152980e403901038204c594605041ca00800604000040c0a11002030864105030710040c14000104a0300c0f0b0110001e045500b4040c03154144012106280e100b50003042412140c0d58030b00310119428400c9015074004100140018008600d4941c0a8100c0701100000003904a442d00102c10551580710790414100062025210010071741c244026403070b20041c90300d6840380b69038a20b2251070340a105030700010a40301141402c030810030400c10000558029007030b5181c3c41e484c1e80c01103c50b610003040e41d10114903903025148035548a0f6119034400c641002c080d180f070655010420607022407640041d602504c60424000c0810400702034240220031280c000c0b645e4640178803140864404010340700d50702180b204104001912281d0855400c03048200e500c0270190340300d100280300441c1100300d00880404183c0c0100c01c02c80305602c218181e5419803111403050160703014540c01d03a8460f01a003601304401c9425900300d5100c00040021410000c0c400d00805070301c0c0c141e81c07070082480c0983c45035569100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 698054082 1250 698052832 698052889
    0x12120f0b01030c182d0605090915150a05040f0f09050121060903050706050f060909030c07210206070302030d050c0711130f061d1807090b0f 62
    0x1886154140d02c000e044c02802022648603030340c5030a40900c121048013194050b103a0110a40072035903030010304044440307600c0c6a200c2600030040d82001048500620700040071071400300340e05444086621005150012a02c1d91864149083d0403860219003405803c0c8804141001c210070b40704054120194410030749440d188a1400399407041c0c2c095000380c41c982d100303102c244503440d1030038a0040d02300c3c8c40441d0094951800310303050300ca0400040d240a25080900c000030032001845802828125444500703a203c0088c0c094580c480c13501031041542c0400c0040006078406201035070301021040d030040780aa8260041044c80d40100003c80040e0400907283e11501fa09200e0341c1c2d006131629848034104a40f5a941d041d814804e40c564901c922120151a818084550000300c0c1c052031610090022959070107892000035103002d80c071245410054005940d03140c143c203400040c940d0b25002488410702d0865070b00010121080b2081d04a40d0305403d01c6030548503003c03920111201e2002018803840c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 698055332 1250 698054082 698054087
    0x50d0e010e220f1811010c021809060a050114010c050c0d08030a06060804200406050406151e08040f17130e091507050f040905042301021612120f0b01 66
    0x2014030341030403c5883c010010815100040c40d44961079440340c40c540c8080782c0c007801a1341ca150126002944940a009400d400f0607564582038080d00102c0d04654840d203880d45540140c3c0c07001d0051060401c990644d185403907103c3d5500103103242c0288150b5103d02d4180c1c01081030140b00b51801c0c0c0740120b0000500c0325600007031084c04000d005a2a081c09207050a9407524100c044424101d103c01c504040a005180d40b6640450000c4c50014810070409550341c022190040f221081c1c0c8000c10030084010450101000702218030100c3c6135100500f5569030f03a2040405440c0314026200c0810009145c000322032a04000c2220719040100300100506e0008804c080300d900504025050308519523403803000480a031001d401252a042598542100002640e2540543d034410b00499041005100034040c1c5203120005211000c00f01e42e200b010321100b003909130300c0744210342d1685104080b101004102460304107001507610b407501481100018020409950400c60f03407129181d03035480e09840759038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 698056582 1250 698055332 698055341
    0x8030a02061014010f18060e1e150a020a0501240617190b0a1509210b130209040c1e031502031003021507030e0d050d0e010e22 56
    0x181d201080d02d807140c2c01c019440c10101d008854590520414118400403030b40201108040c10031791003410b200950340d907040100840580b10321203004520b4110340b1110050710000f10743d89241d0180499401142e071900c011041c2d8040c0c107070381c0c045000f21206130300019001e005030b0304820562031003014440c800045d080d0303e031071031a4006014004c000c00121440443c01000717030740c001d4650320b01103003034002c1c14103150190461228042e4400015a0041900408a00c4800c201400759072003046494035122044185050140003850800e551803080c400112600f80043e8809021130144800009036404208824401c0d142103500b000c0c48201400028840760405044000c24108030340014515124001501e07a6200d8003200c481c1c0010006582840100c019001123030302602802d17035610f400d09032840f1504944403c40005100c4500c0868a1408100560019401001034840100c000400391000004020410b043c498001490849941c44240c0083d28031400030340c01107500c0407030b5116001c0300c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 698057832 1250 698056582 698056591
    0x3090b2d01060e090720070e06030609150402010210051326041e0f03050615040606050405061b01050a02070227040803040c0b0406030f0c020106061d040e030408030a0206 75
    0x22041880100701099200c0c110301490341041d071341c0f050141c5868a049403802840d02e041d40c40041c603e804500c201600085020403200c150942c030b10b40380c40d1041015100da101740c400c80d00c503600200034480c840034034401342500a4030500445801d4161350020b43c042d00c5040f603040d04010045551300092080000070342e8105411442290101e08040c034503140d25001d5400f0303900701c4001c10342c1d0070b445c0403c880030282d0282000120031400103a0300e14059541d05001c4404402141c1c0c0c0b6000b003005030501e8000c04040c1c40700c648509041034101f109110044e00007a01140000b1440b42030109440c8003841340f03a0041c41c0c5144003507510000b034014461700c0c200625210980c40444d602c00c459031010b00107102d401560041d42c450b507030380f601d00700b030684c40c8100e82000b410301e0400a8002005034040e4804c94040047d00301c103000da070080400c240d0072101644070b00380124031910b220800103074014418443e003a01c02040041d803010f18290803480c582140e08550031540c000560744503465010464260312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 698059082 1250 698057832 698057911
    0x30906020105060a061407231c080108030403060b0402190306140d05071a0d050f10240f0201020c030408031b030a39030206040327120303090b 63
    0x2507072419000800c4010380490340030f42c101010400c6000c21010444042d0388a9004000800550b119a00c0c649c0b10300480300d0f01c80703842d844000c052400c02e01940341e440c122040072005c1c43c14640f03152144805030046001c110780c0305500300414104500b00c4880c03c0198980b5640000300c0c035050801001c014100e104034a841694090340342d400103480020b100042c1c5888104105c1c13a6020600446102e0140b450a0200c02c0c0c1003100304810450070094040c8240314140810041d1a070362403c803002d9001c0d06d00b110b11194460740c40309940742c2c05000ca00300641aa440011300d01301000301940c1c00c46d0001c0d04207203a25080007900c0c1c090b04210b429440003640c00c4001840c541940340001500c0a90303480341c2050803d003a14a07040000a1303440205450740c0c0380d20211345109820b03242c000e46400c0202d4084002c1544454441011b0100f0051a4041030545014007682410840d000005103003e071403c03010107482e50100c0d0300281000311094000c1c0150101c02507002d202ca000d059145001016003203c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 698060332 1250 698059082 698059099
    0x14070c080702100306031e030206011502030a08090705030a061b030e070320040c03050a0510140616230d031e1d010219030f06081509011803090602010506 68
    0x10840d08400c440c516581110900000400d001d02a005040c0c1c130b91002e06035040000c40314003004400045030305218803980c00d555541ea00c41410803080724005054400581c800e00c16981298003641034207800404400c101c811030750f501d00004e4a00001c1e48030444040b61116005201c002d0480c0b02c081548817103040074082c4141c4010710690340d22030f500c07000d4a1040200702d10030010000d02c0b03040a202c013025009002d0350070980c0015003d0034054420b04451441e1200044a5440309a44030341a03c0c440e6549400300c1a07100100012034100070b034410300001010890710b000a0131004219034008404040f03068200d0945081c50912400c00e83c04002d06050805010078411b2242c1003060b071401c0c0030710004000d03031441c007021034a12021810400b41e42c070000b06190a2101d510301d8003170040740795505010b50030701089180e00b5142c440c4210202d03039024041e4118100c540d01e411030b601c030070840000a2640c0c001a862915003d4080c0d0035000f051032078006002c0a0750a0040304c0d40320105544420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 698061582 1250 698060332 698060357
    0xf010b0406050619080a1b3f0902030309040e071d04030e100224152403070513060c02120d0c0321330305032215031407 53
    0xb203402d00b4000402003000400006c0d02e40452540000c208505d82d90a1207400c492810703002d846841d0229604030418811003500761f0400b44600c09000c0c4851264000204803001c41c255000360201c900c040360b050009214642c0b0b15141c5105860609000d50000e108051400358415040700b900c200401c601c1d200341c02003001007600300d03000843c3c6a02c103841c002034a03014206e0490074007940700c91008807050004240241c1d41c011141c3c01d401842c44a00301101841d80208014100795008036114004003066613001007446d51174046c60380000319040440c507084003010100103003c815000b40020842d0131500343d095017040e50792900100083c034000c100181000d100900041d51240c4020704128041ca61300c03200d6122050425220022054203204140e01031980505c0d201182c01c0c00302c210380b205042121070079400c050010803240c018000d5850880c000000303c0022030b280080e2000004080d6001842d5030408055480303104690f03400080b145060303542c800c2070340c3c8007510610408c4030b04403254 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 698062832 1250 698061582 698061607
    0xd0f060608060c091507060912030f06030f0b040f0b010807150503060306060f04110406051b071206090501060e0705070201020c22021b07170105010911040b0901020a050f010b04060506 81
    0x126642102142c580180e100d0f0550391042502c5600d000802c0310f2304040790b0104000d1202042080b4820035101032000f030341034503030060448005210203411103a610400101103090a4250b0750010700588810b80c041c419509d505800c40007c0c1c2c000703841d550160b242008074010789801d80141c0b00c0301380b51180c030f10708001002996075200603002c3ca00c6810b0307681c0810410758982d8402549416141d01103034070303256500340c05003950300085041c00c0328052510803400d001002180d06000d8810f000c1c0e07603101420041c0c072124028203003410300301d03003640da2000040380e100e01d04126030303114501c00c1d81c07100d036161581d100090a150a441850b40981e11000d0710700501164100a085d9820309402d0040c0c546814440c03030b4a0703002110922140d030b030003145008100c0350a80c141505500c44013000038407040c5d9907015040121440400da4400021050000344400900741c0c00528205905104450840b440c81e10f0326820070704152001d400982d52400501c0903400e141c010200200303811900142455651040b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 698064082 1250 698062832 698062837
    0x702010302031504060f08120c0715030f0908070311210a050415020c091803030103170910081e06090f04030212071a01231005090d0f060608060c 64
    0x90515401000265140425100310004040010000c1c0302669807500c04049950080c000c000c1e00d8012602d102061044400c101e451140c4140c008003002807a0484a445150071100385404241e1144019040e10302d4a010380420b140c0111221030340c17041c0501c2e0140128000c0c0070486160b40048884d00a0000050080e0340e00d20301980ea040c0d6580c001142c100c44911464005208051120104100b078981c000b03142c3c5110305094500081c03c0c0c40744810980c003030b201c03038030b841080d54030400c01400000d940480c601007d840d44c400045c108801c039400180b84403086140c500000700100100084103081181c2150711000100e02c0c00e60740e082c0b10000c604014801044030000e8003400f0049020944200410545140f078402100e45984403480c042c500b40f03003104405008190702800105003807443c00c4a04182515070180d082c803540c041428860404e00540b400000d0107820700185101c2d4a4120250603600d20030060041e044640e8a46001255071341d4200c5e40890b48600d080000500c0000f08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 698065332 1250 698064082 698064097
    0xd0c110c0a06030209011809050105030f06090c01050d021c090c050f0105040509150a0602030901170603060a0c0e120708060114210c10080906090319050f04050409081801050906 78
    0x901517603441540c001030b20204440070b2085203000d6058000191200d4592245050316000c609450070440101e4500e541c81c00e00381c81310140d54101d45100125580640d0041403084820803001d401d0001d60b40c48141c0210041d45003010751916491080104100081c40c60301620702155044500c010441c00240240281c1c00780a000b60b4003a40031403400629810081c0400d00c005050094594840b50025101d8202c07044e00ca0214000840c000d10000d0414440351144a0240040c1b0701d07903442071031440107400b040d9040000d100024007480713000c3d190b08020341604614274004006952406201a18040c0140d01c050410008544042c0c4a03a85a440b80902086c0b062540c0c1d05014000c00e0041c03c1c6500d1800890303000724100c40384900d05401c0520b1030311981801d001e41d152740d650706921a8581c8034426549201106904280c0e000f0340c001c2015200142c10701031182c0c101a120301c08107046940000c0142c0e01d0300c20210b10a281c43c80d0010b900800084217107420313420200c04c8408111640a00030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 698066582 1250 698065332 698065337
    0x15030521030c160609170703030608122505190203160602030304080a1b0f120c030509061e0f07141902040c02010f14011d0f01090b0a0b0d0c110c0a06 66
    0x70840c011300c1300f00e402030308030b8030380111110110044d400700400507a0f000c1300c41203010904109000480c8900481c2d107100d510706a444092030038005506001c000b0f82d850b106028804142d00d240c1d004108108070904407402c115603140100180da004241c50a0842c0322111528030050000788003041d4003000340c0e1f41041e44601d40b030313440302c0000350151158006000c5051300e10907108014024803042c50102000d4038001d000c0805441038080003110709060b88900900402c00c104442030150034000c004102d0065030b8888020444c48a406890059104440901c0048404244d034024003030700c0d007140100e400100004048200781000180301c081503c00003c3c2c0f00300d9403541100e2607a4000e400c84062884001c80400c2001189888110581428021400c44d03030303d2030080c0301032203c8051519020b0952100050400ea103803070350b0400941000122140c01220700710000440c00c1d030300c0c005004d9111004c02c022541b03000d1000010400503010181038040d510080760044107440f0704028030305651161 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 698067832 1250 698066582 698066617
    0x501080c150c01050a05011a1303020114121905060d0f0303020a030f05100f06030b0603042006030405010204050f0607120807350f01081203070315030521030c 70
    0x9a40c25242d0048088104403542410100324490600b0b91003039040c0c6030201400c0b00c07100c1d404a40722865001d6003030780384280c00c1840410300166010f0b44030740401d800d10758440c41c58030001550b50440c3c40d1040e03405c8000402e24031690150030135280142e0380e00c4007081c1c50354000d040c0191030701740440481e40c40280038198001580034045200c2e070808100c00606100900c12401c001c0500c24408280344907000c081c0205400110300ca0b480783c020f4460206000b010641143c460341c540410100701b11100341800040f101c0b4010310382c0c660201551040d40101c000603261440c0c81c0a102008440f002424410401000502c0c0043c91100c000090700803030b8034040d2001e40d9100419a020301e421001c50400319004002d412080900540c0c416110604580401040d164600702000d0080e00380100c583c00e400090041803000c802c40e010719480741c40780c6404030340040e482c030850031800180c0d001a00c8136045403044410503001e5548990365409046c0010303240d4540688120014011a40101e0001402 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 698069082 1250 698067832 698067859
    0x5071a160305130e010b07020a06030507140f09031603051b10081003020a091a061317010f0603150b18070e0d060c08090f0a0b0a050c1606020d0e010501080c 69
    0x41d001d0300e0701411144079041a0f45d41c40b2000a800d80d040a80c2c201c1c0303e0f441848010400c2442409000c1c081c0c0610303100c104032140007401c0e005483d080100700d0320802500303000e050020341e410014511024001c2180c00c01e000d00307504207030f418010785d51100c049a040c2c5c0b8103081d000b41c03505031843c0300d03085d0a450a0025616254440d0101322030961000c0d50200300d0803004100c402d0303686e01030110b8140c0203e500c50110148424040d03c1e000b50451045003a080103800c025a21740d480c0441d007114034138400043c2d500182c810007403c50f00a6001540c0c00320607240005042000340c4100a001c030422103090001c10040c0c2c4400c3c0e0a42001405a4100b11011043c2d1415890302e2501c81b01141c5e0100c4188010311500744014090f09040f11800000d100f41c3d1501c2ca190340012624906903034100011007040c1d610b6038101c00c0a01800b03010b0803a007580c05c01c100c0c0d001c01380001d100070700184184c90140e540c01c41c51064406460b600b002d144410391500004100308440040c0f0a0b0b09880c0c150340d40f0201024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 698070332 1250 698069082 698069107
    0x302030a0b041e080a03060914060907120c020102130909020a0b0a0c061802180106050304080f07021f18050a05040b010507080409060f060305040323041205071a160305 74
    0x81030034405116460321080c43c000c101003400a0042c40c000c6980c1080300301c0d90740e8404000e41c0d0b0310046000c186103030000400c260382446000164011883d003058621410b960007000d0480d184080e001700144d502080c080101c65050021000425103818280312420080d0001442d851252142900074600092000205402040b07004130b20f580001040000320325115540c42d102d103000500700e01c1106902034001043c0000807006058403050707a105400d5603100e0303403441c8041e400203400301034160050101d180181e41c3c03202d032120b155845e03158442d04605100c401400074441c11030b0518908103401c00c14403040d1580f511150888500b12004610040c0300070050710071388901d80024150a20004004c54141e200307400c04003c480f802c05030507050550300e5504074111131058078000c000540090000e0320745170907018200070307034514074814510b4150b030750500d03203e540752417081140c02e17401a8108000112101c0307101c60410440c103080b04d04e081600d0b80c80201075049542c00038144600420054218034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 698071582 1250 698070332 698070353
    0x1f02010b13020405100503130f05070515070b060108010501020a0303111e03100911070209180106081605040b060910051c0f0c180b090d120f0f05040302030a0b04 71
    0x1002511000808507810520400b942c01406518040c085125034424545d01c10004c580c40707144020340340030001d04580d9a00d492000b02400035105481400400709065a070440c00c0c441e004001000c039a511101031a11141c01d5000070255414054040010080c598020441512541e41450000ba0000f49407400f40310341d0003100308140c42002c0e2424410b05001c10b150045005204212510368100d6442410000b5502014242050000f090255000504203000520340003881c031184a440901c6000909007107429270b900c50b1203507030f10544540b600420b2158400002d4001035401340040c2040c400071034158840c0700501c034098403000911240c50341c419000e444800025000b00c0c80c000c1e20017000d02001c1d003000202196a82d00d086081c407040ca000e030060165043e5451b0b9030b008110720b4170342e203542280c00c80520030342c11460122440001071903020b5200b40c65043c07030301c52210140c810100100715810403684075003803003030412044c4050f81c3c0c0015100c000b550300c20750141c1c0341c0d640c918003d45101c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 698072832 1250 698071582 698071601
    0x306040227183d0f0c030209090906040f0b090109020d06020901090602160e07180311040b01031407080910020d050106020c0604030c0902090a0503010218011805010c0b0402061605160902091f0201 86
    0x40e2405050840ca154543c0081c44103290494034a49c9644504411586031042510010820300e1405101c00000e0560034400340e0040385000006080c6c403072500407614800301c1c041c0c100c5402d64001380c0d16082d50f82140602000c0d210500c014990101e951100048183c0d0502500785c0c1c400080c0c0c0000c4015208809101003005018240d0400658038500090708400003c000d91149052000381e0705154480c0c8100c01d61526900d14280c00e40e1540007003aa19800003034100d40c0303d802070041d150044011070004100040d150400010198544203000381042c1031510a18400c80041004001042a88031100255040c100e001030b500c0640c1c00010b071810b03515501154044d400030484040d001030950721082c01302e200307072600300c186102c3c1c04000e11000c0c00c03406118041140c11043c400407034081c04117198800d102501032450400c1d060440c0464006505086031958096001442c01c0e0081c4c0c10400014400b030750095050003034410016917104640c0c140c01c0c0a6420380024524000d2003500b180440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 698074082 1250 698072832 698072861
    0x6080408030621010c090e07020c0f130e031201060e061e070210020c0a09020a270905012705040b040b040f17041a07020306040227183d 60
    0x600508100d0f00d03020702248000000444c40520340000c80203d1095414414841035018040007441d040401c0240d42e1600125a0440740300754103001405030f1441000702c40c0040300c00461722551050603c1030b0442c0c0c140c010204211017240e6a641c1600c50f0419107035800b0005d9600281404e082071060360130300454070081d501202c03420303141c051b842d00415801a611016a0381100c803946421043e01640b00340c103030100000b0300c41c0e080ba200c2c403a22140382c1c0c550600c000100f19100360b5039101200650350b00b81c0240c580c070a0000b020a510406e68440040c0320381c200b031001e010310b240036100c05440520040c07010300900c46480003e010000f1100075983d24603030111440442005540c085a041c1d04140246561654441c0311580f240c21030034140d030443c0341d00500600d259901c81e0300b44040c0d00030300c1d40a41c03140440e4950240000604060051080c032024042510207810550aa86040c1a00700360a80040c0b402c030990b07904c8041d85c030041d8180c010a401010341040b0207401c140042c0000300c1860003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 698075332 1250 698074082 698074129
    0x30f020d020301051906050a2a05030903060a0e070506280305090c01030e03042903090604110d02030703020108071206080a054308030a0810060504060804080306 71
    0x20030003655000d10706076402581e00940300241005180e21611250080c0400300301305000c0048400d00c00e084040301c81425411100101103d0180101d450540340c1d0115020341000c14401d406040411416502a0004005001c810960b40c025900e407103640c010701d8001d803000203d03a416824000039001440f40c001d009110b2075a01900000c0041205940c0e050f020b0140c1402100158070034060081241c00d800069442d05260401aa20801010110491700140700d0260708658004802540c07141340c80a001c4e0000346800c1c03a154420340035108409105000000303801740562000a03410007a04d50a0078012241e80301d000c0e0a65520302209501c00d00c00303023030000c0031500440218620314110300c204100c0d07a0000e40382004407154121841c12070820704540c854a100c00004c5600b86c020881e40c1c101c269811a20388040701d00f1544034401b100045072215080c130002d0740c00c10a140c1c0c002d15003494001d0925042c0354000f065070b240508050034108001c800b0070700301d95030344000d12104214012200d4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 698076582 1250 698075332 698075347
    0x8030a0c0207060509090a0e0a1703090106060c0b0403080613020403031e0203090d08091807020d09150509040b040f02030130020105090d05011d0703020901081912030f02 75
    0x4019000d0180020010b025210300050094010001e0340d10880e0000c0185002e540c0d076501000062503030004000052040464082c0400c16144800389a0349201c1078265891400c80c601c6420b48549500100c100300c01c0210f19000300f074201160310b401a85c14071f440b41e00d580f204000a000c0030a0003240180d11403002900000300754001503440c0c0c80b0582c5502880780780200d0801a41c03a030045018a5800c08545000b04c00019018802000080b800500c0b103520002c16011000404d0001c403a10005680301c40c0b500300840740c0080e03c00001f00380c13450280000118080000b001c9008200d101401940c8401448000740c1c0d964000c03404840b4100021034a07584d40c0c5c002185c2144000b01901030b01442240041c20340c04011450100c8a40c041e1500c078a084450340903c0741c01d4101c903030180ca00c0e5586900c004031085c0c3c40600c400d4105108401009098210f0042140514042e4403000140d840b040d0f65056190700814540541e0303801c10800f13080c005020800343d014010070304210700e03030501c00100e04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 698077832 1250 698076582 698076601
    0x10c1b0f06090f050a42090e090f120a1b0b040b1303170402180c0417070f1a0c01090b0f0f06180a140112060e06070e040c03090803 58
    0xb104548100c11070b010495594024080a1007890003120070514031400e102010005100c0103840c1c41c22042a00307a0180505154100f08011001700c0c0310000e10040010171401d10700306105500980810007400c85100310b600550b81d03840c0e140159000721407010403810308444c0106001d0001950150005420348680d18004500440c1210211951301010022400130322200e0503680a050345610340035024000c02200c001d5598004108a038400451081f40c00d00413031241d0094056001e02002c142c9031030505a0000861500ca00c010310240d00ca02000c000e00c1e512081190701320744248140120144956241c04e000c0e20030301340c11104540c20440388004201600000340e00c00c1c920840b407030126469660007a80005800d5481c0f1394829055014041c10800100c240e80c1c00248107130001071240800d04154128070000da2202c4080741c100b1003a10240001d40c015104500544800703400e40346003208000d4264140e034440c05004650f00e481d2039035424000d52180c40c00175048408192640303000c0428 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 698079082 1250 698077832 698077847
    0xf0901030c0806130506010e0c19020105040204240b0c070312080601030b0402031303080621030c0c01020706120e0106050a031104110412060e07031e20010c1b0f06 72
    0x50202500c107030300004004804d044042c2401943c048081e02031070b440c000d295224890060000040803104000318801c0000082043d80b81900daa0008585d42c44c1c24010881155101c01c200709000c41802405860340045122040584072201012500c911070080614504622604014031044203019405903030707a089044148a00c1782646e003808864104c00a100580c04150b84800072103081600807400240a80562640448050101305401604503102d40003040b2000d0a205a9080080e5410201000b4400303500206801e00041c0045442c0000080800040140791240d0b60340c4e844014000344029009500184001000f4000454076800c001054502c5a00d440e441289001c03110b5100b00c1c60745090320100d50030240c01c1d0b50329040c1a11440f02800080803041094010260040001011209006100e19181b1445002d111084c9002d0006001c0b965400c030420316003100072903032607a12140461070954400003903ca940c6c552642c991003a189604080c0c4c03980c8001131f002c103a0a521951 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 698080332 1250 698079082 698079089
    0xc1203071e0c0902180d031101051006140906030613060905041104140606030720240a02040b0318012a0f0809070504020702060f160201121a0f0f0901030c 68
    0x15581003582c3e0700c82c030f0b580483c4106682d052001d49081480f041c20700e440408141ca15000742000f980c0100d86100003821124122104040e00b160401c00740a9244d02c0442c1e84611f0b1044c2e115145400036200025a041c00010409442a00074400b08807c010316030704604000e202410702445a030425140441c843c02c04c03042d50368015845e20412141481130a40d00070b0140d800548807a166480b0701c401100d2052400d120f03010080c100705444103124504105500b64284032842c459110403600d15040c43c0c540010300001c2186006000510682461804503034000f4011407a00c1042c042890b03a06000d82054691144094840654040c9003004070300c245001d1030341603807400e10b007444444059581810a80d1048056440320130107009e1401c09500404001740020581401c1950701c0032032040560042c1c20070030070662a14006011560448100850f032605500c0034880d445032070303001c0d140e2150b601d0142c0e4032400005a18400d99244c0011440d146003000d8203035a2590303101d051040082c1010310 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 698081582 1250 698080332 698080343
    0x30c0e190c08010329010905060301060605030106080a020927180f0705100905131406060307120b0a05040e010501030210080403021e010f0207051f06080c1203071e 72
    0x520a4004446210340c1a548525482d00030841c1d08603103a100d00794809941d02c58060010f00e290030b0071003807042c003007034001d0514034004655850190700741401d40d2840d5000d081800024070040c48029000040310341c0c45001031400585402540700020201c080c004900d03d40411444402c1122031100000b091040c0304041d07184032a017640255043d65443c80c043c1100c03581c1c01004040c44545001c96001d90000031914000b582643c40c0c200280314802800c101968181e500e0f18180344001038484a035078000e0003110a517095141c0050013401c811044502404e650b42e58105044071643c984440c20301030580500304001c010068000c0074000c102c20301050344200301c10304140c400c5a114200a80c0709562650152512a00c1d00d02c0ca10900d8a4101229009540764210700f076500c4810701c0036003d82da000780c00034440c01982c4810741c52051107203001d50010508202007032040e031350000b600800c0d95009a403842846048001010f0560081800043c10034a5003201003001d8882014211203550290 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 698082832 1250 698081582 698081611
    0x703020a140a0503030a020307031409040c08160206010e01140d06020310030c05090103030f121b0309060c021b1207261005060108070e0d0f0c0612060e0103061104030c0e 75
    0xf20f0030940d403030241c00034600051b88100801c40009100c0c80001c0b555240604695007014003140c0083c09032040b02d0b0350107001868000800200c840e015850000c60801400600419418008500d100c000140242044a411030050400c03d480389020761580c107410580441d181e05083c2108111248617200694000c50510408a07452800400c0a070490ba8540c0b2210019041c0c01011b680d00381d01e0702c00240100b56500c100401c100312021038925806004d41e00003c1c001440d107020000c0f21b00f81d016050455001000b160046003040801d040d05003001c03286561041f101200d50384c5003a04941044040139410b4070784440c401d02c03518607583e104445000f0383c0d9a02c043c2010f0041240e60464040d4001840c0e503003c2580325004228a8410b240c0283c42c0c400c01c1404c0da140c0c540d010311b070f00c441121808509070040020316805a5808003c004544061082c1c0386400c0000e40681010b001c00350060380e59480c0305022281d0601102c0045621509200742d0564400305020350310400c0390700c0d00526000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 698084082 1250 698082832 698082839
    0x20705011d040914060109090311062802130b0409051b07060510050907080103050105010f050a090507031b050a0306050103051e0424050603070e070504060507050703020a140a 77
    0x140248581d940c0309104008607450141c04020141c1002001035404940c1d403081843e02a20a00c400e902910a41d03c01044544442ca40140034070384030760345840c540c2c0092061080c072052034541c1c0000c003d41a56001c0c803040901c240e020013881101418888110120000201c45030030001a0040f20648401000540c2e10a480e0f0242c0b40380329202c4880502081003840e000517000d6102a030008409040c0d0041140ca40c404510a100190f41c0c00d400305c0d1038600100304100090042c640946404001c0c1781c65540340102249400f0001c0c02503240706915080051407291190b030104030b589160000b80c0c0d108404142026000ba4817508010001909264022415500902a0a005030141b25081114008850601c03800c10400350086401c80040034240c11880840a0f0f80c030070151203140005044e040810425140c0700d1954000001642030100b0405002e03040b4058074215003540c1081513231103055141c4142440320070340000350301c1545403c000c0b40340800451010302c5280103482c0601081d45 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 698085332 1250 698084082 698084087
    0x150203040506190921050f010c020a11031606050301090c05090a0902161401020d0e010c020c0d0507030506010b090f0d110d0201030204170109120f09171005011502070501 75
    0x140e07001e020380040b02040742c020002482c0040f5244500907182011080707032560180040740d42c540201e030700d00d002c40e42005014802d0a024a0400710f100138000c0100d00c1804102a4480022170700140c00109016240d0a01c0d8906001101b04880c5000342090815141e40c0c010307000350801c6c000e2101e031901d0b01489060146c017071800c880510500402c513000440c075210001000c3d42c05000141782c08810700c00507200298081600c0c40c1c13040350600002d602c03032001464010440c0c0b81000a24500da0502080441c1941c001c1500d003c000000e07074201c0002c10385400c04e9403034112140d00003016849181d00001392410080040e180c01f41c803c8840100313100340e0303204004492516403005004100070340c186030320390324120743c0d4141c04910605015041c1940d034194433020001044040c0e07085c0c1d4480320308408101e50a6461b14a0b10b80b141049a9140210303040140401c486d40035100303214186100505903000c040011540c0244044801d000540e11590a05109a922070144015110b40400481c0a60 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 698086582 1250 698085332 698085337
    0xd0206040b06090c2b1a0a0b2a1e0d020723041e06050d080406050901031b091e0305100b0109050a141503190b04061e150203 55
    0x41d0011030340401511500d040150801020b04440748030704081142081108000c45400c031000c0e60590202c401401402c0c000b01a148170310106d240c1c0103520078a4a09580d241030350350090701c612150264460034084080c0205109803406600d440d42c00720381b403000c4003030300103103c00d00b414540c604e5a0500c050019801d035170340c940184507009030304032000c140030000001c8034542c40300e07810600703a01034000e0000201f001c90302c0781282885c07011040c207a5a8020300349800380c500180750036a07030314410704107a4498028600543c02100c04000000840300b6040c1c3c400c0c1c0080e0700d07901c100c00d18038411448001024240411a00c9042440707408901500d070f0f0303003128813800000c50350481c000d081c1040c22130b100c403402003100c08417a5040c00124100801d5a03281d10102c1c1e006800105090310906200004120132002409540b1607060010000c00081d0408a0800505481c68000104104000c000000c0181c0011b03000340c2d8070302d0380a085036102529244040011108cd0f0700d1880d00000d074140c01281c6070b2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 698087832 1250 698086582 698086591
    0xf02030d0e010e04270302030301030c060903080d0c0323040c06031a01210203070206090705040c0c11040b130902121612030c120c1a060a091508031b0d0206 69
    0x14080384290350f0700c0e0606030040855641c500c0105e003041083c540742a075041d880c804040d00103034000310041c420400400282005000c1c0b0f800c00603a03141c03840d80c1d080183d10500b0030f0000c800381c50303205850308a8003a400030004280b0b25803440040440305070000020036070480303043d5042801302c41c000030401d01a108a1411440c2c001c8801c240160081c015143c0e003900507400c821801080c094003074242c8082c40a140246143d601078480380c100000e0316490044182c10451165240001c0328100d90340000403203070030a90241c40c4c000782031441130014008001c04030407079400201c00140c90219041da90320203c0d04c24821900d84166480802c00103a17030b929285411411142a00c105100c52114882080203903840b034600900f40c4151a41d90a850829208681000c41e614818000070082d01001c0e503039501e00782c540c0140c2c092600c00300081c020320755403050201e00c1340d5801d651020054074000c68409010310400b00e07a0b40d0f105445100720281c240a208507020b0040c102d081c010b0a10219005005 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 698089082 1250 698087832 698087837
    0xa03050c061506160c0e0903121501050a030b04150305030301082806050c37030e0c10020c150d050108120403080a03061d0609010602150a270f02030d0e01 68
    0xc111500e114200c0f40e4a14002c142c83c42e404544c00010522000c2c8082803150418101950f143c0022400c10303100b40d40c020b811503200c40ac0600c51400e05903446400c0d2245071006240101d0704000110229000340011207122072145084c81004c010f001c0000010b40c1250f00c1c00e0220341e042d10703813103111000c005101002100403c01495980c8041040c4e074100306e030018a8070341002c3c507104000c1c82031124a84850360002c204412103001e64400398003084986400022401d0034400c1009040080741c603a80704211403442548120782c0c2d2100c0502c01c10890710304440140c0004061400048141d6194000c1c50002012a0503d80089214207010804011115003082090300b0320307045070388880007a00040f4004040565403a00000c000900c4461000200701c60040030720f00d4180f01061100f40c1320160051403d5620070a603001c03200b0042d03803816600c2155914002a240a4800105440030700c09030002170b0550804105801e01060f41802100c0c507200720200c43e0790b00c00008090b10032442d2303050709501 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 698090332 1250 698089082 698089087
    0x30c140a0504090c05160b07020d112509090803100506040810020a05160f060b01020d090b0d0906020f0a120527281e0c030311030c0a03050c061506 65
    0xe1142c4a8200e038503000c0c440c3c1407140c00d0855003210301b45100d00740e00c0252880790794802404034454040c003006418044500e04100b60000045009503114960000089a0b80340051024000c0c10764030a840c1c00b0744000318081c081c40c010f5080c540700a410640da16101c0701c01c1080c00141515010044034102c80030740b000341039078100312039519000f90800d4458905001c020068612421500103580040d03138440c8003c076504588509000088400c82c1e000c1c0313419544100411a41d0940103003021044a05c0f681d02959030b2242e01c404203003d489510002803c650010480300042ca0210b000742030300c51030903070b0349078824070360484050107460041d11040f886000d000e020401c40e8403519055210a80080d08448000060700e01b103d281810101000c07401c00a98482c8804001e540590309401ca80101174007410302141781c23030f0200031425034840202804031b160b8080498003414000d40710028914016121a40c0013070078007034030030360001d103086400340211800204029916a40c51414000190032a130 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 698091582 1250 698090332 698090339
    0x3160c060f14090a0f0b070e1c0510050c0412050109020301021b0d020703121b020d05100f02070503030c0a0c0b01080709061e030210210e0d111f060b0307030c140a0504 74
    0x104d0404003e02000e0808c0a20b98900e142c54560501002c00d07030000045600110609003861418a15074504680c05142400c0034040d0601031101a0303016180c070700045240b90055860818018116154000c0d015400881d83d0320041d100c0d607142c2c1980800340825034026036043c410490711000c0d076003c020540e00700c3d56500c44407103201e4030750740c403007049550b8010900b440356800140700619403c104842940c04400c01012100841c0590034102d2540e4006500700304207075445540380d000081400b08109400324104c2481ea200e11001c0300b4068020300c00a000e543c443c04800d0301c401060050813082410a0f4000607804046008880c80c801c01c00d025160307503400e503800c00084038003034208442000242c13440c40c1007020340302950400015400200051622001c1c1c110381c1802960020b14060003e00003070142e0b0714078085001042d00c254075014000e031f100821003400c0101070035044102c2840020040082c2503400d5400003000c50301030b44030f80100b440d20355480d045c548550410800014814031041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 698092832 1250 698091582 698091593
    0x12011d0109090c031a06040e030a02030924030c0409051003021e031011071104050618090a140c1e01020304030f080c0102070804061b020603160c060f14090a0f 70
    0x8602c1c0a214402d407454030341d600e890781c54184490f80d0480903414070440a0141e18605440b401e446c88240f40040c3d130903c405200040c0d182c0c06000e02072800b4072100800148070b04240c0100f10f201032502241c181d101c0c244044807506a401030f00581c1c10340392410001c500504100c0b14a103049982c020101c2400071810114908800a6405d034a038043c41340600d28450810f50303002d8001c600840c2481140c5036038140c1408140e4607082141c05009a1412092214980390070040c109981052640340300d003629800c14072850040003880107016540b0181201c14003200224446801c904100d403442c4c001d10b091040749261441585440f13001d03920400c0104000781c062443d01419900604040d401c04468461480c26a07000440880d16110000b50900c055500070300c081c49504211030800c8540c4030703e035010505c1480b014000c0900111940a0341c0c4070140306500354030496510180c144011340302252903801401c550b60040518040e0100040d200000016590340d003a60011500384000714a40c858 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 698094082 1250 698092832 698092841
    0xb0f0a0e13050a15090e0d1b0c030f02091b03130f0501061d0a020a020c0103110c0718060b0306100507030c05030a0f080109021306050a20010212011d0109 68
    0x1a03504144140800014800c251003a0b0344036060300d807008280030f0220b101c0200d118540e50403100c6010703c0d1200315040002d00047c3c034420081d45040a04044201c8030000d5220304d0000c50052591124082c040208a501401410308620a83d58040c1c43e46030f03d08603208600c540744041d8441d0701c05100140305044c640701c0704000107000e4030720951124016113030f19003526943d40002c0b080c00100030402c0703071800c085845503a0002080e04214140300080c10000d46400100350b44074109901e4002551446958804660b035a003034030000ca94110791748603140c0c681c10703d2008980a115181003000620600c10701c0482c0c0c4525402030488001000000701600c454000600036410804040310a41c0000c204000811800e82c0c1034403807202e040c100850003061070805810503202c0c035006120408944100b11858420b81d881400d00a03110a003542044070000240410809030845122010600c510103600420000c5076400d2500d507640e0b02c504107039400b0000c01c0488070003003858100412489032186e10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 698095332 1250 698094082 698094107
    0x140709061205121617071b14060a140c06010906050102120313060608070308220303210b04091a0a0504020901170703080a020f070f2603090409120201060b0f0a 70
    0x1c2e0304580310754a0b207480508441104005e980060000703040c0c0103200000200345403417145018a881c01c1800c0500c1c44617035841c0814031500416022a01f8050742c0d01070190f22038801c00b2400d0b40f5403904000c10703941d641c40030f003803040c0c008291410034045543d500c00700310359000800c250442440c540f580b48258200c511410030556215035101408100c03030500340843d00c000c502940003a519036044940c51070340e920350407440410440c1d0f0704008100180c0c114013103c03480d001c0c440c6207889508d032200108024040c82103c541e8018505203c2c1002c01c00444420340c25484401503c04041c0e40ea001807000f00c0c0d0081d50301940c05030982c0010010030041500f10151031b6002030544001d2a5030350f41b60b034200d41042e410381025810103000c09110090070014103000b084071000710000c1ca0328002e00c01910390071141045000c001c400c0c0940780090010421103130a03141c003400401c2424094101510404401c502c00801542003520000d6100c1000080d11502248640103602d4500076601c1616000d4030b100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 698096582 1250 698095332 698095357
    0xd271215020f12060303070b0105040b0f33030f040807050102040b040603090b160e0f12070b0c15010f120f15060906060314070c03020a14070906120512 67
    0x900c0403a020400d400680080d0180d03106036a01d400345004a0440101c00070400e50090740300f48100400300c4d4000da0750134111142503c0004481e01070a02040483e015800d445400400101d201c40c4080120400840300942040600d401888202161035040c4410b45080c0d0400c2110307000710380840c4e0010010281103119000052505a50350101c3c906900164040b50100382d0303c0b4009030501c804100543d50240310540280314003c104040502140844001c3c1809210703414071040142d196403c01c2c180304101c0004507440c4a640700c10400680d8010140c0601c00d018403044080101442030b00b01e416522000e001c05030b20b608000c98025804a4201e068800a2035011808080b42c0158800c1058010700032011440c6410608610140d039000e501040805151111038218041d1092101d6003281180c5840c107000c550343e043c228945050040d01508d03500440391801102d03100001c02800300c174400c40040c881c44d03945480c2d0090b8611b2040003d009504400226600c10300464000c0c180c1d20240c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 698097832 1250 698096582 698096603
    0x2071208180f030315011b1b03020d14330705090904030c0506011203140a020c09130201023f041a03060f060910030507030f0207050d2712 61
    0x3500d96890900450420302d01a00008184820850035000744207a82e1000c1c01d2114030101a18070010803400450400b80c120380f101c074242c50000080b850010300954005142820001040c2002080410320b29038040c100d2050314800259003088100d045d1502c0c030b2019480c04c00902c0000d40c0502044010305074010441d04111011050742d038400040d028601940d12100031407030500c2c04616185041e00406000d03080c00c24142c00007a40541500082466070b008580c5906003078000345d181104040401d0740c00798034181080b04100c004c481c003604a40c004d80c2221156000b0100c10880040c503492141402881d0041d409101013502c02d28a5419200101c4107241a5031501c50701190314440e640782c1e80c4d0308800030501c00c0520780100c820a004a049070280c1c42d1000e0300c400100c0251f040c40e00201815150400102501e02a0744048142440f8140a641e1040f4500d005074807540000303074410100e541e00c074803c0e203018030114000c405002c10400d01400603007003048600008002c8502141c200c80c81 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 698099082 1250 698097832 698097871
    0x30807030b0f0a0806070f0207080c120a020306010b0c070b03071409120706020109051006050612130b100e090c01020d0c150f051602010c14074202071208 68
    0x10194042c008144c104054078580c20607010040102100d8032203001194000082400403041c0840c0c0850b200c0000c5640f4242410301241042c100710b03000c0e1002e503041c0102800014103042210042034044041d006aa0655443d04208156400203076600300004082800c2503e4001d2504c0060004000040120f44004d0400300910303c1c00e100c070b800081c0140d4660304c0c03070300801508100c90380250403000d1060240d50f0903c00030070024019212400308480a0340c01048800003c1d2802464058204180624a2134600324802c044103142c81902c1ca61000c4e400000e510703c40c007191180250074140e01419402400c0007003102c1450800a080d500942c00d030320440d0040c007441c450f00c42e4500043c040030a140c5440d08181d4000c3c264000d401065904144d5200c4c1015030000203090030f00c0d82041801e80b00d50090070948401c41046c50711001141c5289000103540690b607400c0c0c0e000003c0404110340402c00e1400007420307409100001004080a202003054480c020030455610150008000313104028 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 698100332 1250 698099082 698099089
    0xc12030f0809190809040f090206070201140d0e0304030b0c030403090e06030c091317070b0703110702060d0902130905030f0d02161110090803030f07050903030f04090b0409030807030b0f 82
    0xb0a11040311130510000b18a60300d420f003030080600c1520b43c003c0812008140381c0200e50030f8484c10344000d04200000001c4c03d1000c0d131794000c1d107031b01020307140003013100070225034007140d0b29030050100b81c411045400c0041c01030002002103c1c81142c4c51341c2d450760340f1440c0401040050402520131685405418540f5403541c40d00c5428910406040c881d81100072400d04000058082034040441d08010402030007003ca80c0104440350410160b00e400180b00c207404880e990b550040c110000e62001d80001c2c0d18070354210323a03000008030340c1c000c803030880030104046960780032a01e1038003000b80650818042d58028100400241040d110144c401628110712000d07052400184210103c503101c900b00040111818044c406140d105483c0c1040000b550030601c0d01036880c04000d0091000c03581400004141c2481031081d94166000a400c40c0e4980901c100062010b0b0014001c2c1d00005140441e0f02001d0b2070640904585940c0580f1100f9158540304000c4000c5c18000d003981c4d805c003424030719020803070301c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 698101582 1250 698100332 698100373
    0x20415031505030d1d030a0b04060207050606030f2a0a080a0b01050405061c031e02070e0c0702150a0c05030a0e0405070801060905010c1b080a0c12030f0809 69
    0x92195400082840708120050581d00d001d07080103001e94086408004620b40259403c50100176910b01781c441d040102c3c0000780382c80280200141100520400e1200700403c41d005828064400e800b40c481c142e450354280765446030400c0019540b5407040b006800c0c0b50300d041d1441d080708003500c03196501040c10440813518140082e40020309544c0102d201c0018800c8084809002d040207c1e4244200d01b090300000d01c161350684c000603604076400740c00307104050169805801c41409000c4440c642c08101102030346170080c42c818160a40d10100019150091041c1110381a41d4003c103141549083d4500b104101d4218854200a00c82494801c5c0040380c1d04001a0800305401d50b42c42c41e00c0000441804152030340500510242703e46100144850307900440c445040d9075080c81c0c008042c1e00d036800d02020f10010204414034030400090040380000000c5000000c075401104085680b6640c0d100411064141980140010b40060049400706109070080394000d000e510450300481d9029980c1348a24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 698102832 1250 698101582 698101619
    0xb01110a11210f2a0f12030903010507020607020f03030c0301060e0d06020d0510120507030b07030906050406240b0a0305180327041109060c1510050a0f060c060f0204 73
    0x341c0c40420303139441d00ca202d402c2040f00c00300200102080c01460101241d400081c1c06600e1744144e110740c2040861403410415213074541e00040c000e1015042a460180d21030714140e0b0040014051141242880c40c000400c43e40540d03442202c00340345a281c20011920b1032100704042d03074001215012100031801c1400a4000e41d4013001d000034043c200310046040390140d42d4801240200d19031050000f00c0c1002c41d544044a8010400c1400c03550703140302c00c6004016002000345220300e018280b00600c01240d00108000320703910541c50b00f02c052141d0000502e02c4c180320ba16003000e000c104100403180700e41c2140303130080000c444c0d511030524803224080c115084070032a003801222003505640c6240c0301d5401500141010341d403c01c52081108140c000030310071a20760a004510001c0c284d41c011004000492408240c1d0910403201e00300f03024080c1c9182001c0c0300f0703144910001c40b00803400c070140000010803554561284a816840340c0c1e0b9002c080c040070b141c5804581c0e401d110000e511107120461200d40b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 698104082 1250 698102832 698102863
    0x180501020301060e0d150f0b190e0f060d030e03030702130c031113121406070f03050c030114010e03150c040f092c030f07060b01110a1121 61
    0x769070500d4001803c01c2035042da1144140d0440c10800d010a5001007820b00b090003290340862a12840e49410024201014144e5008082255941d43c1009040204815a500049860015211800041070920040d1504c41c1d01200d06401000000d0290400c21741030f50b03000c1c05407824000704e50005003100c907903c191071502c1074552040c482a16814811652004424920203040082d1503122000889081c00b52141c001c4081000209000103c4810701040003a001161298500361500804030854030040340b01003130404c00031036905006102901d06a981140c04641c61802c801d00440c2d400d1003050b866605030107103061400030240e449408c184924040385602e076030f6138a410a4100000000c1d4420540146840020307120700c089405005401d107580d071800c030206014414081c0c214800d01c040228201c10000d98102048460703004994241801d80769809607105850211b5110140c404000708107240040d90b03013005161010030a40f0016003655260204912038446901c0c00854211000790b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 698105332 1250 698104082 698104087
    0x100c1a01050103150e180705030f0307030206100315090212010f15060507080d02130e0703060e0c090109090c03151701051f060309060e010515130b0d080a0318050102 73
    0x1882d605406503c1408100340341c180285480d0203410300410308094a1910000700403000c034445900d0070400c400150200a090700c1401c5026000c3c1d99903a0f04c8440210050301942d000103914041e11103e081c11282c0008501098200d0006200002c0000e10412070380402c1503c030300c04881c0c5092040c1202e04008200c0061100000d80710c2d100c05590603070040c020001d003000000005030b1007105890000640020258880511440d0f80c0920096038002c50a4626440200450765516070000b400b120b44205038140b1545030b0301c200d108a80b180b52500c170f0100c0c3d440c1000b0800383c0340380da008000c0d005092800040013600010031080528241d4482d01d01c04c001743c0e100c415880b00030321a041d00071606a101c481d499000030000384141c0701d24811314042c9039903124050144461900100000c2414900810461512094060422a82c07880381d070300480035880600c0d8220501e105080900c00010b0800c1411003041c0d0f104240342d0702c2107450108040d03c40412003030800240003a01040361140d000580c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 698106582 1250 698105332 698105339
    0x81b0c07080c031911060405090a02040e13030f0c0c05060a020106080d09120308040507030b070c0c0605040f120c120b041202060421020115081b040b010e100c1a01 72
    0x42c9402e5440c403800b44a908584e0081c4a9a45a4040306101a901c2010040c94201440c000380345809030b54002504040400c081000d080d243d9401030080da062056607807425265190380d800c081e0712100c00200400e07100c6030201c030410301845151b1141440b80700c582440c95210000306240342c102041010160f911481d081c85070a4041c000092850304914241e044546018100c0021450000d00602404000c8001c24107201c02484498007a581290b120451400c01745001007000c6241481641d14181980e004642c0301e10400031034040b90201110b00080909182610108070010f8008556500c080e0f03500040b03201c0f52031000c1072183d010340403425261030303d41800900d100766480e07041c0454101d04104000600c0528a62442c0006140404404c0780d00e45000d80c0180301011005026101075200042c10307500026540e80500410700e030005299643c030003404165801a1105c0340420078802d20390400f410140c005400c1d0b04001d250002d06501c15480700541031622805086401c00101c0061 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 698107832 1250 698106582 698106599
    0x7060309020109050d1109040317070c0b090703241506050a090803030408040b07030203071b090e010509030711010207090609091a090c1e120703120c12081b0c07 71
    0x2078000b0308082e245c061100c0e10036590b92076007001c007299040c401c107003100225082c10300c140444c00005500d003031008030b503041062001d000101c044070101c8a00c40c448001404603d0049110320480358003901c00140b10101c0f1041c10087da0300000400d11040e550919030088094049403503004080c0703519041e44e0f030070100350b00800209194200840316071003001440001131300c0d0f0044a041300d040c821110303150219890101e05602c41d000c40a00040c000520042d220640740461000b240c240910800c18030902034100b60a07107004071038420194105001e102c010a00340d151024020105105440090362240701000403a0305035008807102039a221010400c0007411a40e100b1068684000141140790030405075a651800c80081c902132401c0840c1f5040c0900c403507500d1944060300400c8012504040768106664031050b100a540c0114290b0349010414010705914584030340001140c0e0b007814041790700341c4c2e1000001d00800040245038030810145050030000c1c185540310440544005460211781 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 698109082 1250 698107832 698107847
    0xf2f09040203240303070302061302010512090606010807020a030219020a030b010f061412130c081b10090b04123e2b0203070e070206160e060d0209040b03070603090201 74
    0x1524000c5d803041110307002094000034000e074040b80454170110300718042d10040302d0900421115207540310000060040c0310001158881c400c40003a40c2c0c04840e50354110f03049988101100016000d03800c1207000e045c040708424031520300c03280003a00704000d0941e03959a81c42059002d82c003491944413040414403003a50301001c50b910b04d22000340014144900c0305401540302e0307030186c44507510b2500308074140104480540c2000007001c0b41001e90307080c0303640070200345140c00700d00290701e11403140c00d4050001140110640810366948990060900c0d0801146c208410b141c400d0a441e15400340c0c00d2a080700032512802c1c001d2a481c00d400c03104410b12403008a0708110550540383c400e41c041250f00f0101e09204284410003104c50702415419101800400c0c02c0c030842d500b00c19444113136281080030306500010071600665205ca44200504000c01049440e204200044e6610040c200a003002d40d401b240c000d8001964000c2c400164103042400082c5440c07500d038000310101e52117440315015585c10180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 698110332 1250 698109082 698109151
    0x1030c08030a1e030e012d11071e050d0908060f07020d030c1205180f0a0b0c0a1e110d0207080a0f030513090501090f2f09040203 57
    0x35030402d4030b03001c005001c100780420b0092401e520390307003200a058825000180c482148000030018541c6040114000034420041d18a94010070260b5070112480782c441d950f010045c48804a08100c115070f200072824040903281c2180242d0403624001081c024030010003608055100c6008041c900400507003413280c018901c410011b4104100203000b0703008500710038000d0a0f864009203100e03004000ba82c0d40d2244040d140b902528180400c0004099241e4401840d2802070480d10582c01d002aa941d980039000c0740102502120004542000c4100d07028000d005c43c14104442c10107849100d19020082072581c3c540081c0c0b80c42c00074002d21006000840e03411000e440940260741c1080c185652350500154000c111001402002003407610503070643d80b0310342142e50120000c65581c000003025090a0058040c090b25082000089085520030309608000700450120440e02d15041c401d04111030700750741440f0f44400c10240c441d82d81c2d40d02c004e40c8100084026241055441078a10410041100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 698111582 1250 698110332 698110349
    0x7110d030524010215090f100b010311071101050d14151207061b050313090204030b06042a03021c051e07051902192f150706150e01030c 60
    0xa241a00c00e0760302050038105145c0c03144081e021501c54000641c9461034200c00c42c01c540c020647c0c810800e40072a0882d07101500c092340d05020f00007a000010701580708006000f0503a00900e80d642910394007a4026041884100f403001a0151900c200684121400c907089440c3c0142c10903410f010b880c10109410322544018000c14400e402d0050181003400031008c0044415007c012041c10024100110303021883c010f502c0307442e005c5d6070701c0310b601c0030390000e010444000f205000016142d040500c26030001e00300d804000d030b0580680e2101c100140354440842c20400d03808011080010180802038565401c1c0b103840001c5901e1b020080074502c6495410b180c000c0c6480c40c09110142c0e41c00010388900b00740307201030181131161802003646451070b03482c0304400704c003a000b80150900c42c800240401e0040c0b8001c0448519002c1c2c103900010650300c0c406070360f00c840a00036a8407241c20080103032001c5480744600080c04141d48503283c3d042c00c40d650010010300e002000501c104024020100b00030701c5581d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 698112832 1250 698111582 698111641
    0x90c0117070203160c0f08060714160312060b1804051b031603200d0c02010603020604090b0105040b0325031a2205101e080d0807110d0305 61
    0x100c100a44031320540301d0300c0d8450381c4d941c0046800c0c07000e0050004000d0030014002a1039595842d01d007a20780c20121007400101c2d05103e21202011203640c126514845e00500540507814980c0c0c0c00d42c0c1101e182c800c40302060740e40e04408188802590020400d581c1c0200240c1c900044030703010041654001086080700c501d020802d03510f898140130559400640700c0c640e030361040c1001d2a0450051643c08624131007450040140d000d41055940240b14124400201344160520090180d090703400d20703c00250006000c0004000f41c05983c0d11980810405240081c40d10750f4641e81358110350402d645081500080d03055600721350001c01c59405101ca074908051080030020140b01e8900440c030043d90b40915200300144040ca86500451915002c082100700140e003001c4444107019100390052402c89070f040e5041050801000798032404940f16a4000d100642e00301fa421940088064442401d000c510300402e000038909002c0484640c4850b82c0000b841e25201d40711549110304541c140c807620300038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 698114082 1250 698112832 698112841
    0x81314030c1c0b09190f020f010c0506060645030d080a0506131515051e0d02040506040e07090603090f120e0307090902090a060f1806090203090c0117 66
    0x2044500c1246400c49920783c520398600051504000000e08400c19909501c2900c2003040014040108001c0c001d50318824038850010046d1207401c181e034000382440e8003030400120140390607070080c2001c910949400e6240c43c4008001d1880e00300c46080c102c004000070b40351404108414140b003110543c00c40c01040507140018019100d104050310100c81a0380710800201c403521102404621a0f44044c001c00072103c01c844854074400d00b90049807480c00b000f400103112a4468002d4801c0c40058044c500e0036250303100d040310042c3d03004a4011228a07000d001c000b44a0b030b20900640010114800030103c1890a180c006081950f16001a42818039001c0b02c1004158020070712220280d0002e003401e0302ca62042c400340d8080b40c14070402a40b41c4200c42011425803500e8001e10f070f42074420344020b110364907000e80350f8080e2055401410001e14100c4800c00c2501c030842160000041150000110700f500d40311600140c0e0b00c02c407954030080e0302c1039050f060156808200b40c00c0468000d00569080d040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 698115332 1250 698114082 698114119
    0x2210408060f011a0d060302060d0516020d17040c0b04170601050103061203080a0b1201090515070c020121050a06080c0a060509060a031107050109051c020a030c081314030c 76
    0x107222990844c43c14011441d070f900b0454030341c8410060b603002000940c0343c24007400301e80040e05084905041450303003c1c650b0800c890001540108041c1540ca410813007001c030311001038055000510946a0031042c4000142c00c000c4c0c5001040544011904484001d40b1000721a203003c0c8103a119504240c0b51000c01c0100814a19010076403d515160100c6c05444540c1382401a200411441d41c2c014180304060419440540c045081c0512402c240e500411481816410484044620001148076041502d0043d0310a00c1c0400001172100c40141071007003006446802c0711700452784401210380c0c0b00018004000c0400c80050b041c0c1c42241c9151035141006030042050041d00401e42c084c0901040c0500b2a5029030850744a03541340241072071f1120b1039802c0541c060080e42c00241c4007070150440d50324039429000c00c1400d4802c01c81d0002e00f00c001642e42c04981c82c0d64a1601618222414003010340b800250070074480051902603d0760151004000c201414241000f81a0f80304440450701000a0750 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 698116582 1250 698115332 698115359
    0x1009060203040e0a020d051f05040204141c0b04031d030303042616110a0e01080a08091206070c0312140109050603030c06070206070905060909040f0302210408060f01 73
    0xb2103c000c00c0300140c4490b024030019000d0078190400d1a8104010001d00e015186042c61000d80c812010104280d039601c1400101d1003240254903000c2844100c08185042c0240d82c40641c56920040000940d065190010100000d580440005040131100e1441c15054074100800c114200c001c0d503e54105507940044e0208001e298032080a0f4000b00e00c0960307803200741504c041e000c18000c0b241400425141092480d690041921720803c131031027003c101c40c0324140c90745050303809100c000c0c203071006540c851070440c1c0c2042021640c4440304820441da000300c1803242038024002500c402c110414186400b6020300d00700050607048910344502c40e11100010540f00f411100b00701e41c006441d480e200007082c00d510400c280ca069501c0380c0014850f00342c3d80000c00c188990b8040d03a40070002070b00c91041007002c1c41040307081507101c2d01d0800447c01050440b4003580707980303200c1e004039900e4450308030610201c00e580b44001c0ea11040081410070031440d0a1000d1940320f040155803442943c10b150311083c100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 698117832 1250 698116582 698116589
    0x7080a0c020721050115030804170705060f0306040b3010021b070f05010c0303150503060a06090510060206040f0303150e16081522110702100906020304 67
    0x1946416a03004454000e0180e8005009508000d0460110700e05580c60f0000003020221000d42c070f0f160703181c920102c4100805d03050303076030000b08a0320f441d1904012040c031081d484e003032030b034507001d040b1002030039a49801c0240444102d1403981526407411408120480e600c410390340d4060740300d034020030728020045038001c9603030f024581c00801c010f50a28049460081080201c100051001030040d03002e0080b00c0b800301c03114035200c0c2114059521040c44000242d418464580812220280300b00081e010b038000032140c0c0310b041d54030f0306a075a403200042d1528109851a41125230750360b0041c05505901d0003030a82c842004604407034180c0c50300c440207643e080003c102030442c006407444181003601c02d03000140c202507000b003108410f07034458090810b0403200395010010304250001c0c80ea1060b00803440c86100f10921810340c0403428642003484010a440c8242054024921006509520561050030450100f1010454503400f0f288103100030441c1030b10700c0d00140704d89104208440e03036000041f50f098 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 698119082 1250 698117832 698117851
    0x90c0c0b160207150207080717030307050d2c0d08040c0e1308070b06010e01020615151606090c0e01030b0402041107060c1110060e010b0c07030f15050a050708 70
    0xc0484000c040f410b01c3c032242c0000032801c0c411403c070702c0300d5907000600c0425541070005665040d0796800ca00000c4888e010300302c0d29141c00030700c001201d803030042028002c10b80744220042915000050140c1e0540078008a219202100420040c00580100100d5144003510f040c2355009080944500559603000e00c200081079950307100240c0350a207609846c500f0250701c640f8491700c480c0b00f480d025000e4941114428005001900300f401990f1000910b5801100c903a40b400000030084d6050050f0b4407410800500c0091080100a509100400c8401c280c180555030001b031884407443c00340e28102d85940800b544400303040050001c00d1141021703d03007150f811079000070410000c0c407502c1e8080c003403000007a284502c2c000d81d080309290410b0914406404040075105010703040000f001c11034030140030f42c0801464140041c8403c8212000800080c440003080f034240c03690f40d5640c42c4280e03040d29001c8551070a0089100c40340c5002e401000e0300048401818406e9240c005401040075400074400e841 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 698120332 1250 698119082 698119111
    0xc0708071a16060b21010f05130b040c0807030308061201150b180904050a030e090106020a02010c0501140c0703030b100e011206180207030e030105090303060120010c09090c0c0b 78
    0x4016655121340300b0201e018042040050001c803c08940d0203040703140700c00c15420300380b655002c2c03401f0740f060902c80c0b0388504c01d0100586061701c3d0310780c080400400840b141e01e500320020440c1c00c81040300d0300c015842641c2d407002500d4446c1c00e0012990070341003c8a96a0b062545044400146240b14001d681c031340c409950319000710003441d148242500480582001c0b010090105004010498501d254083e8468500e48800c0500340030361090f00b4440c8400503000103001c00010f41c0b240f180f4402d0540075200225628508549a03400c074101900c0241c845840028840c0804d501405060311800b41120b2125688044450180c00d4100d40c4005c0f034104549009919108200c40d405180a0003030901c22210380c45913070030840c1c02507111010580201e070008000c0850b5141c1402640e20506140000d1401d6849400042d1055002d08044241e0009000c440303501c000d009208194540c42c2030340c0c03a420900d01d00200e500840d090401703040d0401c000c1c80290004200c483e4140d80d00211107400200c0d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 698121582 1250 698120332 698120377
    0x40f0e100b270c090402040303030501150816050f091009080d090812030c0d05040605060a0503010624050c0a0b010f1401020601140a0e0c04051c050a020402130b0c0708071a 76
    0x140b0754030604d02507a174054400700e000b009140e41984030506032544c1910f4079080d0000c1e40000d13101104100d418403649020310003401d001601c07443c0a402000b402c100d00034100f161074000030355200c0d8017a20f1100003410280081081c030004210340e43c45c5450303500f001c451490420703400c030307403110f481c2d140d140c08200c4000003190307203440c1080403585019092801046075003030510b4181c0c040c2405070740d0180f084082c101c0c082040d03d03041c81075104a0705074107003112066007900030100d910000b6013903010034400c040c040185064030070700000c0d407054030401c409020766051509403881c00c4419044030f0300703040c010062080181d0700015840d0640e4020425021000011800110a21415049503920b00d82090602c225814848050426114210f80001c62040c1010400f0a03c0200d4000030707100b6440707040d2410250800d40c3c001c04c0c4082114100110781071f01c038040e00a040d4000c026451071176103d28001c1041d020181710f0400544201c4245c40000340401c2000c40d940d0040600c1c06a070240c000030f03060b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 698122832 1250 698121582 698121601
    0x2040536031801110a03090e0106020705060d11040e04030f030c171f15020f0c1002030409110f030c0a0f030e0d051c050702030a0e09010303090b0702040f0e100b27 72
    0x4254540101700c0369409420300d4018013003102480388029210016001141c0180007151040955002402850a15003281c01c0313a0050408044941c1a60208020100b004003080702020311881c0070f5220407003078022140d8020704a8105842c03003001c0004503045d08c1340c142c0050159540060f03d80040d00c5440c40c3c695850900c4900c2a84207640c0051502c030600c0b045500841c915420070b05043c10390340d039585503c09100a48501008810043c0c20802090162040d0340e4010b094000c801d10700541402100b640c0015554000e0391400e050b0403001c25850300407540203b600c58a102507142c14022003040c4030702d96580389507240b40142881004206c100d111101c0c0300f007030043c500c5142401e0007030f4141502c01075120f6001c10501000507804403c0c02d1440c1c1800c0c10114126a0300d0355a5820031441e001107084542c1000c0740482c0d00a4481c040034002a002c1d0180c2051112408050b064000b059070102c41111808905c3d5401800030811580c5540c00451500b800085241000011940d0310f0404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 698124082 1250 698122832 698122847
    0x207030e04021902060a020406090b0d061203051803010b06031b070f0f12030b01080703091b03080405040606020705030606010e12030c15091c030b0301020702040536031801 76
    0x10303540051021580000c28000c0000f07810412a42d502540c0c059183d01d80c42c50306034865801514042402d010040001138001d40052500318988000004d6280d2035140010b5400d00c0d1034800d0340010303c081151a84030031020104885c024045001b00304800046001c55010701000742400680c1808444550458220b1001c48100300e9110b8003908003100c80b45010f08500c1034065090f10285000103210203018064401c8070350000301615040300f140c3d55088210b000d0440d01740304588111040c81515034480c01650300d0005144100e110540b124200818401100c049603c4001154402c400400c0b10791000708406400290031f107041c4170013104440c0401d001a4492250404500c00003444504010380843c4500c00e00701403040b4141207031130310743c000b540d6110030900c404056402442c0b807041c541e000b6804400d1213003001d00090305010482d00000c0441d48102e4040b80382800c501d9403030b0251f041c08005402c00782907880c90744611910130003010f9039a0045445240d20349a170341000408980c0074004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 698125332 1250 698124082 698124107
    0xd020418051606110d1e050d0c0207031707030c060e0316050a05060610050307030f0f02040b0c12160605062d0f100522050406170615090109020703 65
    0x71250b888030325406202205102d4850240000c05000545400240106140c4181c41c2d259682c0380102c41d02214154940a11502c00030603c903003002030450000e00b5000d04001550b242d000307488a680f07141480f81c261780ca00b8000d200000c80c108040310000c2e4102407286201c07600000009880d01d03440c040c00340f561190621100b01002210409410000d0000f282d400291140301035500c1c981f1074005000c880310500c450340000c00c6040c00040c0b07981e4405d030b02504017420595004258801c1d005c101500300e0384150804c0c5503903507001070a541003201c100045000d55452800051424418003043c0d030580d001a10300500d41a265400300390300c2e0b92584040b0507032034500b502113101d154081d0a001d003400c58104e5114001d0305008034040307503880c1410f21503001c0c0381152619450402404e00240c1249000c1c400034606256030790000c201c0d40c41d540300b2031000e84516074009200c0c10b082804a0301c1c2040003030070003a00441500c1c50075082d45410300194112580b00c103015846130040d250075110f0034040034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 698126582 1250 698125332 698125343
    0x9150e0f011403060f0f062103040603140108030703050a0c02090a1a0114030a090501090503070f150504030906030b0d06110414041514150a022a0d020418 68
    0xa040c0a010500015000c1c101c40310600b020b9040d60500c03003859201d4108072240000700c0350610000341c5100d4500c0084c0e0b44520000c2160000c0c480c4003500d41c072480d01d07901c1002c045900108040c8031241d01841100c1070303244031070203010f00c1e5032614803403903070700d100e140030007001c01902048900030140204100d102c0c0950007040e0380c0c498680f5604400050512041803440d6900a040c1d05200e5401030b030490800482c280d403468615030340d840d80c00000d07103280c0c0402c86207596034181c00c4000c164240040d01045204100c25030103190681001d203088181d900c6403072000742c9400107200000742c000307440c48200c840300c0c20301282d080e1002c80001c04240e90b80da80035245c641842081d41c001c0d40c05400400580742c45261003a0b0082c0000140000c4a01c59103005000d820345480511112084900c5038481c188000e285400005440c4014209900b24540000c0940e00418800c042030380c029104048201d0907500d00c8444020701400500c0c0e400c01c0000183c015030b0745880c1d1040b82019140407000d11600314 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 698127832 1250 698126582 698126609
    0x30c2106020a031a040207052107060f0507080106020f0d0c03030b0d0f050f070b04030b061f080907150203030a051b0a0203040315051303260406150b0c070915 70
    0x7400503029000210390b801d002d131104442e40c800d40c58030344256040300b90084014044241d182d28001628100d2441c61a0900c206000c89800900c10303000d01c002e940764a003401700380c5080122018015101c180c0045096420504248001540028804034170312a9807034120200f8605003810790062510032600341e004142d00241c401404000c04141f10040c0c440e02c11108001c00c10100d450712038003903000e5440b00710006c2100700045078040200c0303600014001c100f41c5035082c1100c5222803030351000c0310040c00b0072800710800080140c2441a600100f40319200d82950340c0e00910700035141d02c0300a041e52092130792000480d00500a40850790300c684400c041482da500000c90020f540c0b40c20500c000c80c2d405610f6405400c4a5205010380c40c020030403600b820034a02181d075010303a20114030401d1405038000c80c90020034800a103c82481c010b5000d07600c0014119000041151940d640d074101c40d11540e0b08000041c030003400000c0702003c0702d501e01d07000548141013400f001111002580320f0b02c0c484015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 698129082 1250 698127832 698127847
    0xb031308030c090405070827070303031e0c090806010e040201051606090212030c070f150507080904110c06090109031218170306010908010b01050d020f0c0a200406030c210602 77
    0x2031958019002384924640310740c82a8103c3d0140d54100340381c0940d0340c002c8001000024006e42041d030294a21500741407821181650980844540045003000100340200811094205001c100c0c0900010b180c40070803840d05400207061440f03403402c2003e0b0318204007240400d2240c44d40c0000d100380d030700522602201c02910305241c0e50b6003112084140038010316030009900008120031200b103d4404054050305000c680301a00c03036400c141c400365003c0d01e04000d03400242d61280305e502821207070b0b40300058039440c080100e175140c80300092200156030314180101c80030a800019005d0040920440814000300082407486072948003400104407886207903200c091410303180c0240d4450002070769403054655444110718240d8080d4103042d4042101000049a0302c0c0840c0c00034400300c248084071924108100c007440740b60842510083d50001001c1c55070000c00c021391580e10440b280112002d012160440e165000d004c04940f00c0c0884400000700482021000101c00e17000a98128500310741f140390 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 698130332 1250 698129082 698129087
    0x4020f041401080615010804020a06110f01020c0d090e2503141515070c0e06040e030a0f0f111f0e030409050f07051801180504061e0b031308030c09040507 68
    0x1054403000307500a41c201c0d000101c6c1d4840c3d408180b01d9038004200304911490a1019a0119055030220f401400742101c510740d0910700340001d008401000c001042c0620b01040f009207204001d0b0020f040c14490001801003c0d0040c0d020700c10081c807400f0300307804400030701c2105031b00420b0a0318085d0a600140c0c4c08204034422910284910540d050f1209000c1580d49810305d450791082010040c400304403030f82d06022940200ca40103070b104902410002e150340c10786110502d55001048440300040d114140c0310011035110364290348190513400c0848211039860625515210b00c0300310501c16010560154000512540248290864440030703a5901c60312510040080d21089a8080d041175000c000700b50380d144100101d80c50759903541034803000456110011200c1840d64005000100c0d94030402168035a95032103003500034100f101c0c04110f00c201609030700383d41c400146c1c00448100d10500801000f101e021289109060344186400d54035941c109600c43c02d80603118800707400c0b910309004c0011094 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 698131582 1250 698130332 698130343
    0xe03031608032203020d030c0c08030103060509010606030e0a06051f080709050f06010e10021f0f0506030f06010e0c12101805090c120709021819030b04020f04140108 73
    0x4500c00314403ca0440e05500051001450341d0000d0041c0d01005640442034030035408403505001528004403425010b458000d02900281c1003560810381e00e60074040700400c248901300c014201410140301c440610084240c880c011014050807954540c800a00804a030300c3c02030b2099031004450b40b60f03040c0c440e81d00a507254014050103544901e02404039038503203013420055215643c1651006030a83c402d00c2404410b00740000030740e06510401c4109031041080048010b41103c2c1541c00152400752042c9010907158042c11b018002e1304011001d1a103c44045201815107424402003200c1d0f480e41c9010261500c0b84006031041e480c60f000c00c0c005092a00c0749024100c0d050703001080403800700c04988400304c9900340d0b90014940c0c022044a0402e007442c03216100305000600c190742c241035440e01050f0a0340c2c45020345a10340e1f64000e90400e91441c04860110741400780558400380f807410740e511282d01041c0500040c0c45222840040344450390340c0e800844008000664214280d65a06005a50317171 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 698132832 1250 698131582 698131591
    0x10308040828240c1206060e09010b0912030705100f0b0f040e0a05011b0f09140405061215040b090307020906090406060512030705010c03020a0f0e0303160803 70
    0x60048200e054080105018410140b2001103100c084001059448007580890540040305200e03603141c004031922001d100f00d2914501c1038176003517003090369240400e0172100c3d190001d60610201c107503c10070544030412601d0640724600e03d6070782d03502050000110150704004042000f0305c00099240104440400c43c03c0c0c2017100d4040503c12036111047e10b905903900f50b10801c4d0400c103d10b41030051403900c0e4100760745050030038094801030740541e00c03010f0942d00c0c2c1d01514a20009a082c13260800c0d9030240f035400d5629840d03d00300181078109003c000c81009000140c2d03205039110b4010540d290349081d601c81d488408001224241d40890800300c802c2d07007013268107580210b2160002070800741c010013260b5481c1e47c01041c61003641da40130100240708e2000b401c1074400c1070f96184045100c0d00d400b45501030320046a0300a5032551046c0c900b01d400e42d10383d0500030302014018072500b03031903503007080c1c00c0c8200340800e00b00008a42001c0c0d010074918042d000403502103100401d4000240180300c80150f004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 698134082 1250 698132832 698132849
    0x503030310141507033920010c170d0606020d0212090a050918030703090801050603010603350a0c1103070e0103140f0a06140f07050d1e020301030804 66
    0x801c2030100708030480060000030300b0b09040401c08200024400d0901c40003203025121002c00341400032441080500340c00c1100f44070380c5200e017401410b1000c600551580400047e41a040c21034400000801d000110388000b00b1604000040c01d8070480345a0030f0343d0200e24080d1003004101d0717542d035000303564940c4e01c0b0b082405130080c007100c010104000012101e2414018220710391262038001401701d0804010210445001c040005030010501030000b880d0042c0a03649100020341418910f23800c45c1c4026080510036803414800308000780c00c0c3c40d118000301d00c41e001d48c003c900101100605401c4007a0300300d04d00d002000503151800070f41216031500c403280a1012081c4c1072180e00c0038180c1e105000d02031002c083d202d081c01040050806103603080101c075101d0654104855400b02c80e458541c0b80401207841c079032540103480362507200bda1081d51100300131140c51424201140c02800c1e44c810f41d400d4031041501c40c9060042750900341b2010f1a882e40b8087c0031552907070749040c201d15030303040f90007910b08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 698135332 1250 698134082 698134109
    0x50708030903091818071a0d0912031e230a0209120f1002030912030613060b03010e0c07120e011701080c01022416110d11010b030d0212030a060503030310 68
    0x4008000801e0410744041f49455030801c2d859006000c00c81c0c0200540041150302d40c04c03a000007841440c0e01210440d01614003258691004402440e0340014024099400e4a020400441d040400c1c0070f040010740d0360b40349807030180c40b014003a02c00380c41410840b07600001141030500c042c04001840c4041c04190030159507a840711045400c0c00ea200a587e450748580c0900c540030b04c4603601c10011500540002c1c00c0b40c0b0703000c1107041c80c901914046e0f0301c1009001d402000400c11042c00d00c0505c1c0e03005541030301692421001d07030768070852110046515420401c28420302c42e1903074001e04040e48030501c5540342c20030715a5070b011070940e58144064202c1c0180030b4421240c02c0f12007081c00d004050394000480e1202e995a40030b80352070a04c0d1000003c81004442c0c030040500107010b0000f002003004a5139900103124540703022a0035030301c0c58808e5600903404034600301e0409601040c1c002029170a002071950326181c44da4110b000d4207140e0015949400000244840c6403106046141150b429811030340 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 698136582 1250 698135332 698135371
    0x21020901090212180a0f06060501021b13091103010e0303060415030b130318141807090501050c01020702060f0c0106050a0b0403291e10060507080309030918 69
    0x2e90255498080408560002041c0016a00c404045045101904072980100107886984004a5401d4141c0b25995140b406018a50f81400b19120142140e0960300154140c180420540405000c0c52040c1c503545010190810211036600b5012103c0140248810195103108a88030f40c41683c1c118851407914040c007400b113000ea40c1030401c5940001c8105426a0f480c8014126144800422810410031501e00380a41901c0031107000034140f03034024220402c080c20107110489540100c204000503100d8200603500d0343c07000a5805444080c6040740e1034000035800c950180c0100d030380007903000c078012403146a540f00c86005404000c80c15402404081d54500070301496840c54094014800810001070004c00e60b00300391038400d180280c80140c40e800c1c0c5050440b000c1e02084d580b142c01211904c00b003030011740030501416088440c0d80c01d2002028504403002d4181c0c8581e100041c0300c0740e000310000e281e0640034402e8660300a4082c0400c241441c0c400000f41180004480c240820940155111f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 698137832 1250 698136582 698136599
    0x21111912050f0f090102070614091905210405030a1109010b1903020705030d05070f02010f0b030601090e03070807060203010914090a081308030408031206060c0a0b0a0621020901 78
    0x154041e1201070700b5810103843e02c40302d00805a1005146119540d02004181c0001d01503220300481c2c0c00c0a0007120010b401e003401c40b80c0c10310080a000320b07900c00c044010480800d00105d1010014074405160405015100103040180c0c05594000e039031501440c41d20078144508000140301071007003255282c0d0142c0e01c81030940a0b50007801c009400b4850740800c80300c0450302036801040b419024004030f07410202c05210100940303408861000000b0341200c0003501729902400340003e41d041c840c2d024000d001c0b0510101e40e60765014031500b14080e0311100d24000c600702c10b00481c1c003000d07082890f01e41d0f030b18040e0030140c001c1d500038410602000d00e030800b00100c2042c0d548110303009600a00c060420001d40340c5031148550004c2400382101c41d0080c1d0001500c900800040000b045c0400107035440e02001c1d0001e94a000300103110601401041060100f8148042001d0040992241000e100f50f00ca00c40310000078003241e0480040480c81d1035103555401c02d10f23024a58030354400c45a5203066a21070010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 698139082 1250 698137832 698137841
    0x206060114180607020d0609020f0103020a021513140a0203070608090c0424170118021005030c040e0c120714160203120304030c1b050121111912 64
    0x22480325106020312184a682d121421002140040c00c00f0300708040b6400007052442404011600340303517900a060110704001c1602502e034682401c0c21418a54401000703915281601c110b5041c1c4c000c00c000044a0b44818000f04204503001254503003402e0440c1c0342e442d52182c0301c00e4148d2007803042e0b0100089541c4600c020f1445406050090724210ba145401d00003d0308503140035000800c0c41e0103a041c0c0c221480c60746240240042441c182800b4021103500c1c0c2120090f0743c4040351110685030f5000076881c1c0ca03007c3e40ac10390361407a00356039030342ea00c45100082c1d000300d03000500f00201000a01c82c1d42c81010f8054000d079513401000c4840c680310420103039201e00f5a03440340c0070700d58028490360905414180030000300324000344c00c2c1d44c00f0004500e008072103584120b4080380841c1b41e0815003010321086080690200012014005200b13080400103404054503155804681e242d000e1500c80c44082130308903107260081821855101d1802c4e419841c0c0c3c1000564411001071104000800519140d006 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 698140332 1250 698139082 698139107
    0x7080c0303090f0c190e13140a202808010c080126070612060902070c0e07020a050c2106010603020a1119060e03162001050712082d010602060601 64
    0x214612140e140184180c00240010b2000341c0c4905d07d0040c00380400d0710301c90750100c8820b400c809000010007910300300e2481e04030742109400300e210f041c020036040d03122014140d0300d1b0004103c043d4413410081225440c10381258000411650818181421484c1c01c101d000381692507080020041960020403149011984a19481d49500102d020400680034003030080250002c82404034855480310550004e80e4401c1e84216100c49010000b0081c81e03540402c1180c01140b5440900f648000035100c1ea640d40000c207a03036902c10709040e440120481c0e886154003540e2805901651003540c0d6466029009401101b45c4401240b894420040c0100001c1100c40d240c0042c00b07040030504039103484c0d020003000d1a007000d07540c510003008040254800700041340c10b680d1050141c10b03007481442d2500011b81403130f00c482c18103208091085e0b000149139290002c0722020203140100d007543c0c484440b01c0d0a1008610000c4054116400c0d05080c03258035142141601d1598085508645403071004440150700c440 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 698141582 1250 698140332 698140369
    0x81f08061503030307080c1b01020f03060319050601060503100503150f09120d050702210409180b061905120a050d0c0b0a2d02070308010b04050a0b07080c0303090f0c 73
    0x40095a41041e1f071000e031403203903080302034154a5958450618226030194400940c0444040200300191404000100151060b01103032040d41e421542c038640d45407010b0003103d00380710001c40064607402100c00c0c01e0008000040486d5401041340f900200740c1034098900054001c02d038000034410b0500065640360721100c4003413862801c4415806140245000b030680f02c2140501c044112040c4002e0104540c400d0002003666503440c640043c06c4c0c100c98009502454202e040c8001c080440c0c103c03807001d644a5001e440308181c00a00d0f060078130682c501908400ea0104125060340c8000c44001004c01c2c6503446071048421489255000360b9140320000700040c05240d8181c0000c01c0804c0c50b0b001460b0044203001c80c02003c11086681c9000140400c081e45030700b5602080e108103059004003c607005020b0341e09020f15082c2040c0114a000c0517600509100080c0007030a0300800482a04444c8001d0404080d01d4981c201114115220183e0b60901c49c2e87c0d108170351641005203000320300f030b01c5c06242030b0303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 698142832 1250 698141582 698141597
    0xf071205031b04150c0c030210080108060912220905100e09010b060f1e043203070b0703090902030103060b0a06050307020613020d020d03091802070f0201081f08061503030307 77
    0xf440c00c6130b1220000c0d1782280c50025610000005031900d00c5804103895281e21001c0c030325030500d01002c1c9844d0004202c012964050704004036640c02c003104842d110702e2801030380d0b00ca190110b5641300d1180e03ca548030020340f42ca1700381040420810190754000b81c41407000c581d080c0d072b2180f21a60382aa800f9644c400c1d4400d02c104a90400140507100405403018000e084908016184902105030342203580030000440d120003000040494624070440707140c6000ca40380b01c4200303520f001b00f0742c0c4e4a42030050309120344001442d40181801202403400915510000795036030340c1c407031034914080c002402c003147c0a00c0c141480401d42d240160180c1341f11303100070f9004114659170b402c516003c0301c000000903600070000075482d0000d83c480300030070424103002e038450f51040c5107030102d80e03904240b210040800e16031050020300c000030001c49100710750360340901c0c02545540310141e43c0e40c0b06540d155800d003003204041c0400520700d08003140d500e104454242c56040b45598075024180c4a1004803400c400007141d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 698144082 1250 698142832 698142869
    0x50c03010e0613050702030723120c0f07080c0405010803030f06042a0c0201110c010c06050702160f06090605030f06210f01091104061a0f071205031b04 67
    0x2840680c0890020b10701e01d8034080f50300c01d403011608260780d0540140c00014040050214856607034075241d02058003c4481e082c220701150f110b6140c02c0381440b98400000f03120880d1f44080140c1e020201d44c1c50261000d0596030b20200f9540c20036460128052420310f400003d500720003001740c2c0d00c58075860000021680c4d508040100030b0810181d0001d440c0704480c140e00e003040c010b0340340e005000415103862034034802600014000c4000d00310548413661201d401a001e80e680100c202400326402100820140c031030781c07800e900340961860f41c2041c21860321b80015480301c0b664104400c4800c15162104440d460b00011a041d100490b1100110140403000c640107003440285040c0c485480e85020070544003945003103082580b0410103540e07503912502c445050007112221a00c500c04c0854040120f140340c50f90000c569a5101c20b104d003030120203e001480e034407445e03040720b8089910944882011241c0d100c00390003604169402d05185001b48039100481304a141200c040d101c00e06041100402c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 698145332 1250 698144082 698144099
    0x11a121603030f0215040b0901110930030a050301090b0a0303271e030302121207080c090a0e0a0f092411130e09071410030e1b13050c0301 61
    0x112100054114400e2076441702020204000c000c1c01180b00d103d0100b01070070700101c2c3d00d00b560350309140500441c1c020890403007182d89084646480341200c440816039142d110b00d40150030b400404011820340400143c0000540c0c0c40f03001141a07a00940040080c1c07a10b41090211034143d030b001c0140440c0640d40c1d03120341c03c440d17074101000802c5160044005551600c1c4c0742140d0442010440c844044451020300c10550144811004800c0a0580703a050082c130240184c04c441b00034125005010415000c5249440300c00109e034070842d005800550010707901c00500209000440c1c103060201d140681841400c081401003041080c2c02c800080d010f6010107038900e090071421007104007005d07a180c1303049070144400d0025241070b040f400c0082c13421500d021980c1c616280c0c01401c1e07481d690422a01070068141e0703210b80007440b08084d240900e41102040083c1d00900696020306e06a2150384900c845035413504042c58104441a81c03a9101844a2820807003641c1e8142e4108a6202091005105200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 698146582 1250 698145332 698145347
    0x10507030815040f0c0e1e040e030c01051006110c131505120c01020106240503062701061206031e0c0b0a0e04110309031b0708011a12160303 62
    0x10038070180b01c9854040000101101c01458441903000d4564081c007203001d401c42250b010703107030056490304a4000442280021204079011242c40303950380d01168190300000300203030b980b40101040200310508114103e855514214800d00e400a0b04524450f20f02071004150540d8400e40a8005240070001c03034408009000458190381140440e0000016a0f550301510489a55034080240c070408403070500081c01d4400070b80042084c04250324410300c041500b096000d90b410235134a485034a9445020009002406c1a10401c07000840964080304c41c0011210f42812070300e061f1200c0c8559031460019034141c1e44640b00141a008445800b1008038800c403520141080c0b1403608a80c3c45525140406000e812403954000050300008076001a0300342b0b440342058840242c42d0f800c1c218944805002e80d02c0c462380c00900340030a40d00d05508040300042100001a0800900030302c215103550b01d03040c00c05244208628072400e00210704a0319408042180903c50519041c00c40304542152415103417403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 698147832 1250 698146582 698146591
    0x30a05091f0e0105060d02060403110609090108160824041109011e050d12030c030e1b0f0a152714030c09070f1412091509010501050105070308 63
    0x14040d4041400101d101c0096403185218030160000306500c80d00089400c4400003003886018150b0006083c0140e07890809580442ea030002e42c5582c1822004041070781800703440d544a400100c5040049028200440ca0106d00046100e40c100480d07511903c0c5641c035401d441c4141401c002c0410b2120b1420441c546455010f4041c1d240c2c0060000d44d000894013100f42688142c1c500c030001c001141c1881001d110b54001004100da17541780b03400701500e4010300145d41418240600d0340e907421003050346000e0f4004080301140171040d80c2070300015030030010105003066001c0e4895550ba845030282407800b888030700240c2e490607141c80c1041072001c0e8261003041c282d58940c40602030807025402480085002c5901420020581d0302e07900c024070003414580001a0050761080d02400104542150300c1544200110300071f11341003490801c41c9001f00700501c1501c080ca04e1186a0b0810844050b4000840c40b50b103d4100f00702d981c8503611811014221042809094005030080100f000030030310070914550030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 698149082 1250 698147832 698147851
    0x60507030b150c0c03030708030618271c020607020c121b06070605010303030c170708061c020a081510031e11030f0c1201060b1617042403060308030a05 67
    0x10b4003184c500080c40e6410401007200e90344000400c10105061084c51b03800b10307071b2045201c2d60306402c1001c910301000b00c2d09524110011f069108400e080c070740c02c0007002c0d425609000401c1d0542032900c00207446900c00c1303501d2805841101104030160034103c514540d82c0b0004030203068610f0340311f80c450031124801a0a507500c01d00600009010230b2161283c14000d51083d200051484101040502040c810340040c55030118900304111880c0d400a48a136848041140c5003030910303804111854901d00b802d840a0341080020078045903601001036175043c07415000781964842e07980c048a646064105000c020300148110501d000b0001c40002048546442001055142c241c5140802c0c40c10006040741e100c5c2d507000340106441410078800907c8000d588400a103da02c1c00d00760f2401141c425252015140d0a058421000f401519640f120032045003004059440da40c45402080350a66000048002c900418604c01c82c036009208040c00c4941c0500c3c194156a07d4041c1f80b8003c0100800140341e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 698150332 1250 698149082 698149093
    0x13030909051b0c21090108060111071205010e0f030a02030406181205100c05032223032701080a0e070b3001030b040b100b030a020403060507030b150c 66
    0x2e04681c054101c0b070020750000d204094103d030881c40d02000200c0040030315402001a0402660300c071000c1c590141c800e0a00c1d01c3c4180362a400c41e407801e501517000b94030480b00e15200c5010040190422202584108200c40300f40591400d0645c0300c0c410540c601c005030340200410007100d030107181c012420000c440031440105940300c074414180c1d04030301d404413100d8208050f4100014054490214038420924017070b411490460b00c0c80100c5043d001410029a542c03c005a040040d40ea982c13501100035880810012551141d0282d031701e402c4423801c0d003a11102d00000358142903140c100c94201040c1691031000340c1e203410411b48020304800322109154007903060302040500044000f4502003112a03580708060303900c107152040c4464885250342c0041c101780010004207401d212403d8000d1341003079008075651a110500050511142d1186280ca0340100402c407412080790f02070b10480f80220000d01050f42c501c8070450480d4894442580d104500050708040d40c0c1d407007404ac159868410f000c454 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 698151582 1250 698150332 698150371
    0x4050f0303090d1226160c0b1909080c0705030709020f0315030c1e01031409100e160f0512030c0a150b1503010302151c020a030b0d030807081303090905 67
    0x4a0100121800e020f0802200034410114000b1010030012400c030300d4402444180c995030f00c44410f4006c1c09c0c40d80301040307041550a8008503940724024490340704a09941c8c2d000d60341d44241e00e810007403040503c00d0003810b00c0040e10510b28000c03110303608040c8040a155a0786e2031032401c00c2c202240c100c95010300c01c1404440302c545484031014980b5200c0030010300c50300c0c500800101512029020110007280341d80c00e003e8504130000c8c001c207007013030701e0798010034140c0c605005c0350b1401c03d4038142ea140001c01b49000046031880a0100c00a4035001c3d102a018403200074006079491180c0d50803409603078441e890710004281c4803041c00488003940c403008100700c1c44100014a03d14607498055218002c00001002185000c1c42800c400c9560041818240440071044004012450610280ca56000a040044030341700703601030740441c40006d01c0319003405880d040081201a0454400c0041145078001c111340c0c85c541c1001a00c0650705a0361303584403d0500540901628001c0c0000b10b11b40c1c8400d0024 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 698152832 1250 698151582 698151617
    0x8030115110a030e0901090908040e040219031a0f131113021c36020a0909050a0309050306060f060c070506030112050601050103050613020304050709020c0304050f0303090d12 77
    0x2d100c050096480641400c900410000e4603401a8407020000d0302d040790500016081c1d005440445002c244540041c0e611400880d00050b120b480121040c240c1c000302008000c0844140310760841b42c1c0d084403c00303965140d05a00006c8043e50840071880f10306400200003010070700f000d646014060602e080b50206112480180d07002000d48090721182c040d14450a0545842a0074010101c15075040840d00b0480520300114a00400c07001d050070a0504242035494099104004040e481c40400c101e01150414544807460058110002004c20500007060f140c0003d6440c0503140091440c180d0034541c40400003a075018000514090140c40000900b903601c090245000380102d07200c0a07800000c0d86032031410484160001418580341105122039030700da004940780c640b0074007600180d8a4031903040031860700030903030320032828240009050b660381d58000c000382007195030a1b17890f076101044170020182c5034021200c0c060340000480c501e01c0007090074100851010303e080e0515480340340310340070714 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 698154082 1250 698152832 698152843
    0x20d022416050c1e09070e03120403060b1e04020d1b02070f06030513080705030c0d030b03010e03070b0f1e0a021201090c17091608010b09010e040803011511 69
    0x2990380c1440d0041e0000d001c001d1100d0b10612030115003500c501d10011004c800d0b01034070600414040c01502d80041c9800740948056225000001c0840d181c282e200c41000340305a02501045408030304008490f8a036040040e003244000911941c20080510318100b440000e4100e4003450a0303041c0c40705001040d0075048002400210040c3d409040203500300003201000b950f060303200c101010b1070542006165114841c00450b9a640115850354a8915040c82855070007110311100d1107014038100540c28940680c00307190112801d400130711401d40305030380c03182d101d004685000d45000030b4070001070760301c50004407a15031285101d01e0a00c04d6410343d81610030009000c42d0b0789500103900003021003e40300403489050041024000c140002d04040f00010001c04d404494004c6c3d08501d007011a00d03464003842480c0d445042489100c502c150f0300c00302c013400307021740030300441c080c0819400104035940480358840c0302e10b420268080c507692070a10f00710040d0b103400024400700b00c10040c80c81d05c40c203000d115 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 698155332 1250 698154082 698154097
    0xd0605013207021f1b0b040201140403150c03061205060a0905151f050909190303020f070812060307120b06012604051b1003021b01092d020d0224 64
    0x59081c50300800300005d8405a01c580079004248020782800c1d00083d042d0b480302d58456820f280801511032a041100c01034003540e00001e040ca108407010380d4002401d68060803000c421560b00f4007803965a041c1540c421401804040c019801400004200216681004551501c10003c0380c40c1a040d102c860b14042c45e040e40c54220710b10320507991400e858551082000940800c407200021800c00e50040d580d2004944101a04942e14030f021100341406541528540018107944540e00d507121b15000c10103500001494024410740c50200b001820000781c45e10650b5001040300221071101d448003006800014991070411181c14108104401c1803400300101800190b002509400c0c00e260540c00c08503d640b07598408102c000d00c0c0b886960700c0e020034817402c0c0202c0c00c1c01603503803c0354178031140794909030b079200c140940c00c0c80c0381001001212000c1031960a0000407a40c21584203010103542c0121214010354042c50b84d88104000d490503118805807522060012107102c2b42c00d12510040703400418 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 698156582 1250 698155332 698155369
    0x50106080d120c080708060d0c081f061a25060e010e0109030e120c102a030c1104020702090901061715070827030d060501320702 57
    0x421001c03081d800c40030032000410050310510082003001c200a046420090036401007000c03040204240f40c90750010001e0803038001d0722456009072107680c102c0d6141e00104100301e071805449480f010200407442a2410344546213107810200080f1100c0c000c0c1c0d600f0640c41000c18078136401c540302a445c00c0b0820741d4200c910409020030500c0903948020308490302d042c20320740180d04000d250300000340d010b031400036401d104844010903424000300585c40c100c00700f014a9040780780050032940c110b4212883e1a5540200000700e0100c0b101072052490380300000e01c00034003003a520b821800c00110803441c0b00c3c40d40034002d040107050034515000113204c10f105403024901340e5034030201485180d104101c1c070f902c8180200000c00c100e0b00070700345010060034020091020009580d0110300030300303094000b02c50741c070494800c02d510f400d00503800b150f00e0b42e01c000c003500e6800c2e181030340004072035000e6580581001d409100860f8948110041e58900c10703402d0107003000307182d010001c0c9401a6610280d10a100480c030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 698157832 1250 698156582 698156593
    0x1508040204060e06010c1b080102040b07050105100f03061d030a0306090506030712330203070f09081b01110f03041a04050919150602060402010e10050904050c0705010608 75
    0x18018002101c08a400c0f03160303440d408508010081c1d03000400f50480c0da070b002101e05500c6030900c821030344c400102c2d00304003410f5000280c0000c02c415440080c2500e10300490003000b01c0d0b200e903034008281c0085442010152001240c040001c2402070b4040408050020000c5205503174900d42642954000305000340480d40d103020070b104407a550310076164094003d034010150035003001c0c0d40680700001000700401a203401c1c0b6884640314281c1d0b40f038403101c9442d91414001d03c0d0381c0e8074120001c0c0d007084072202d00080000411b0402988200c21242c215007000303010300303104416882c503a0151014101c0c41818000d901044080480c1c0401072104144c184a01460315075007020070001404080340c00c1c0744e0300031070b09001c00c1c0205da9600240d60f8020900b1460b0314492011706a04c81d01030210070170401c14610881030000b800d29004900580702c1c0307100b6070726041c0004c0b6803810004551080c4016400152080c4200045400d10f46d00c0107800103540c00d00303581031286654030503080d00c2080d0014507098011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 698159082 1250 698157832 698157841
    0x1017030304051c020a021c0204020f0d0b0628020c09180c0f0f0112090f11013e030906070c060809210702041508060117010b031c091508 60
    0x140201104040c00f40128018012091402550f4000f0510080d20912994044000340499003000144c00340d8040c000b5074aa440640d0389031019044504075450071403d080520140349000d804840407410468041c0f141441c410300f06441c8840c000360000c1c207602c100c458519940c0d41d10403426100b00003a11003581c036050104013890811140e982118041d801d0508500001ea45101030858521421b1900c0402d1180e50709a4001402c0705900c041c0074504603103610320610155100b4080100000e0320b5454204007080c0b0300d840c280c5d0966248000c0303040003c070f506400c40301342c10b544e5105111690031030b420141c2c4100081e025a1141008807601001c0090400807250003031900e41c1d201221002070201d650450100103120720900e0840c2180c590001918011955240d0110314a80000810038101c0c58132514555070340c1c1002e000701d200f22001c50840304401041406a103000d84ca01070081d2040c00c404041d1000d0302c01c6030a82640c240041c082012540300000c11f804856211540e0303641100381003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 698160332 1250 698159082 698159093
    0x1050d02031504092d051005451911011103030a02090a0f0e191e20040f0311012c01080c04080619020f0c0a1103060402181017030304 59
    0x80704149885280011759000c0215074080703500c040071442c155001c9401c1c2d803807625000488042c0c00c4400810f100105491000b07081c4401c0e01001c0302c04131081600c0060040c1301c6140d48503100d9406d8011808c1070540d00300060071204116420f041d041c1017071000c561550100b607085070001c17107407200a10350100d4960024981080720000510404d4038030054a41401d1055100da10000d0000c11242c40c1c8440240c959010795200003050300d0088810704c0d5095800d4509030152900360f40d285000c07500400d1050010501008031350848941881008420389190344000081c205142880c0c180000c440d0070152150025003010130030803031812180c0550344200c002508a24010f030031280240801d110038400400c0c000303040c5410880d400e14640c010200114907101a02c1080c00d001410180440c020300010130000e00c4014940c421190202600c0e003070780c280765480008880180d88000145421340000f000410305503001010003200700c006548a1021030710060f04600062a03951000042005020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 698161582 1250 698160332 698160383
    0x80712020a0b070f140a0c17010c02030c070303110309060f0c07081c030e10020a0201140606070305160602040503030f0408190c210605180d030b01050d0203150409 72
    0x40401035604080c016183d488030a401d0b03100c002e00c96864410603801c034030f0041000c14240c0f47e2050000c08403c2d00c80194445200302c02610004a41c00c0083c10722401e400442980c11075503520307006103070321444c54070100d0b62070120001501a90004001411540d15140b004003196a91603901c6a0344110340f803d0f03185040c45917400304000da0401c01440742c10010b9a52070103d40303071080c640400c01000914009042090266415080c0303132000609076101601074002d40001c59040712841003955803030060006900c10b4910040004100708605084440c0071020001c0b024021640181420b45410229107160700c010410126031b0300220b030811165200300308486e07800e6110003c00890400300d07a154100d000030703070144a034950440f0056040348000031140a4003240c00010901260400c600300890466032641902143d00a0b1403400044500a00800004007010380d60a450300300100c1c0d806000f90009041c00000390514815071840d555140250f180f1180246410392886210301c00405041 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 698162832 1250 698161582 698161589
    0x80f030c0a0f083c090606040c08010302030a12020304030c030b0402040b01030219030b190f060f11280b0f10080c03072303190501050705090325080712020a 69
    0x8904002003244c0f9507144a4400071042038008500540540d56540703001940460660a0a849100082041241c4001106401a003003981c081241c060206001c03a2815003d00020750560701841c0070707400041e04070440c42156440d0740306590034a038881c1d5664080851075071081c2d07440c0c66003909000c150b1a00303102c3c86e00f0f0441c09090461504606404000ba04120030004130300703040d540d043d04c00007511461507001941c540a84860780280e2600000c0c0c01c900704074003d5400042540a105e0b513428014800c0341d545036400c40007451000c0240d81e892213054140c08100e03905460346200321000415580b02180502a50300c0040560b2424505003003905516900550040d0301c208051002501d000c0341040564a40f4071504074006001d080003203049003156089a050b2082450480d080102400c5116040d4858002400f842e01d564000b220680114180554585c01c030041c2700d83c480e491900d0070100c90601859601c50075503901c0c034450403c0ca16600009020b04440410001c51411038071a802a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 698164082 1250 698162832 698162837
    0x4030210050105211204080303040b09031c05060d080a0215090106051c0f0f0b0a050f04380a0c030e0102030c0405120f011b080a0c080c07080f030c0a0f 67
    0x650315010000744401c0001344200c407007600a8070100004d40c8140074030901c03511000101560f03559690071044d0b481d403040750180e40020748a8040340280031701000300d441c01c0c172009a0506e03914000400000040c08054202544161001c0c10b660001e00500c0103000c1c07401580d0040c1c004101c0380c035000300b26008010030b444010f07454032038140407950719075001c481402980048544020b44c0c40c40c0c5481d070403c403030f2009842146920044030400c900b8040c15885850701d04002e01803900c440c440ca150184040d03034018031100b140140965240700b141c3c0e0400c0f441d000c0340c0340c1d10b20131105100141c0c90440155030f40303d48075440300140c02c5210307011f000d04420400e400b4021490340c40d080726010028007841c040d06200d500044191044560100a0f91040e246424000c00c1190000c0e0700b00f07414a030380c0d558513001040a6000191104d01c1c4d510642c50082802e450fa02140d681345e21101e80b10707a2001c1001c90b0902d0041c000500b40f244580c014620480181003581e40d9000e000b04094000340511520908 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 698165332 1250 698164082 698164091
    0x61d1801152c0c0a410712260106361205070f06030c031103060d02010e011b080301032d0305090103020c0114010906060201060b160203071a0304030210 67
    0x164551480300903621043e04080c240e221070703240307104442d05510000500100308048510341c42c1d0f0f850142c0c24500d50700c804d180c0300040304022486982c0174007400c0005405020b00030102a29070780141d8400200d45260f140e0034030507250f0100e030030a0406007030304110300150f110724440502c030510f001c0241d41601041035138000e4030050a08070821801600407402c0104c420107802e810010104515000781110300d07020f9a20f40d4843c48010002c1004441719400a81080301c01080f100c0094101c03405580c0c05008010611484e0b001501c1c8075140101d1141040402e243d80401104011440007500b440f51a0160f07680d450f5042494182c200c0c80e085c0d0b40d00c194094081aa0701ca5550249100a0345c51700740a5190340e250340c0144c000b405a85074171400c550030300c1902e540000e4060300207416941e8000c000c0043d41e8036070f0f90032802c8441d0783c002c0c5a804d21007040150080105030302c89984c0395100804990300d29484008035080c545c004400c45998078400300c2448109038040c880d4400961500700c0c10070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 698166582 1250 698165332 698165399
    0x10121a010618091d100e1603050c150f0a02060906090303011d06040609020c01050402040e03270406210c05150a080709091b030b04061d180115 63
    0x4440311620720528805560b00c04264003890b840340f144501c12200d05045c0d0b2515169401c2680203018000030800450040100d110b100d0b001c00300c0030038162078002c001003900501040174400c2980600011900002042c001e0383d103844403c80080026440c581e0240c00700b42060303a0294541000549940455041880140640ba1003103454200000c0d2007580d1802580f00c1a010030000c00094014a081da4000101e040341c0b241c05400c10342c0524803d031400c1004011301a5a03c0d22800780701c2c40c500d885e48058a001c0c10180307400511070307028000200002507041d6680061400c40c8807189d011310103108400c00701801c1c403052000c40d8000782403d80f641055034011840ba59541e10400016409000303450003c10f81780d83c031a00d0000081c085c1c00b4010483e004071401100400301c0307136444000009082582e500c507103044c54064001203a251001a0815182c900d41c1203402c4c10008000503490000c0200c40c64031418240180401d52035691040003100d41000110800301c14003400b0741d40d011a9042160 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 698167832 1250 698166582 698166617
    0x5010c020102040e0109061d0c1204110f1206060f031612031407020907030f0e0f071715040609020310020d050a0c0f0807120b06070605011e0303140310121a0106 71
    0x4541c180c00101023516260359041511840f03008141c00a40e01c0d03800c0ca010041002694010101c91080848005003070300c80c084d04001e080711111403928a0b9800c90340101c0c0a0b03041c8242c41d0604845c0003026038041c0c03405840c5142c00241542e121040c01414180c608042c103810400c2031020320070060b8490320b48035a613008a1a0184050310103410159141080c4000500e25804150701c031032020240c0c0c482c48540b000d9942c1d03c0c0810b008154080d001c1000d1514080030004055403103d0050101444a40c1d0b981c07603d0009101001099801d8095140f40030310700040e5100910610301059030000b000d0801100754000c482c0c1483c1c1d80c1c000d002d6a00c0740b106031260482c860756400f903110b00d0000c100f82c00359941c6102512190b041c070768202c54040341700030802002c1e13044541a40c0f1200c04c00001002e00441010f400a100c0c4005804121080090800442da4100460340f191075111810701e10f6a54108089031b8a8080c80300f941d5541c10242204105502d84a50720300500d61032030050344e85900160384 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 698169082 1250 698167832 698167859
    0x306051f060930120903050c040e1c110303010e0114151606020c0316021003110a120b0a090c110304140f030f01050403050c0c22020d0905010c020102040e010906 71
    0x843c41d06111481501400210007448064182d48611600c010100700300000c4c08840c0140001c803021300950b081c22503d402c042c4120456000c04400800140c0310118040d403208005500c0e07101044407844026a40d880d04200850003002c00f50f074070101d10b40c0340c00a00301014103903980ca0344c0720b94003010b5a0101590840103690203540320309641c4100725254170340b40c4028171400070800703014000403030b00c92001c071905410106c225009440c21075400440040c110100c1310390080e5108109402d00c49003c80501c21440080c222288410001d5040541d0300015808666644015907190700d50300c2608400303511151050402851000640c2040e0803c203049600c03640503d4254094040024001030356541002040c0001b81c1d1040200f0030360404d0700b4018050780c00500740c134100d8807904c46e00034a58100311402681c042e0121302c01c0c0c071110007543d900401075405881d414040946a448c4540419001c0c4210801110282c00043e9103d02d041405603204605030300c8404814901501048146181c500b03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 698170332 1250 698169082 698169119
    0x406050901020a06050106030f0e0c09010e0406020d1109041d0c040f290307170613030c05150a0e190204092a0611030304150e03040306051f0609 64
    0x2041511040d214004034946000d20b003000d8580d43c02c0400010704940c0551004c0030440fa121414042c161100342000d0f6501c04040c0eaa0b508224900c0c01000460300c100100c2d9000352140d40c1c05490310015802c1d034010b0f60402c03000c0301186a030004505a07a842c1621480c0c00c1071800c05954009903004c02c40703446e2102026600c60b030141c3d44071011106070400030340c41880346451514004d01c482c600142404030b00d0a101400c14064032400b5070119114003090228000e6140c807600034a103681d1008503240034070401110071002e00c1840c4000d4400184140000910031103100400350303482c41c22442001c20348451740c141c42c0641d04000315145003030065010203101990161004a034440e014580074101d290314034100e0f410041c40300581c2c4094103540609400b03d170183d54902018000c0b24400d82e443c2e11096a0051520510490543c0000100d401c004a51208034054074205592078070740f001524011902410340002188000482c0c210a10419002d0251490000c510b903003030076200c5124211540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 698171582 1250 698170332 698170337
    0x10506010e0f040e0f031819090908120405150a1e11040b0a03020924030415020f0f0c060f070c240c121a060702091806010602070e16050406 62
    0x140042c507440c0ea401420100f5620340c102c416180450540f13503140d4004048000403a00c005d040b09440d46400850603100520400d84091070340e00d4004032034010103000208035818601403010125141c0400c0c4181e01c03940c080c0014000c504484501400041c000400e02d402c07007882c0ca5490f51900c0000d80488105590300c1c00009807140c600315095070790307000300c0c1d005501044000071a02e2241d645034001d00460a801d4803000014a84004a088441848c2c405402100010b00015010520000741c4045845804600514080810062040701d030b00c1103c0500809400041d4034204002c00c10100b035001051020203a16800c090500500c440010f00300600000100400048004038845500a180b44c2005040080082481c4060010101c11342110001440c0015903000c14005100c84002c0300c0307004114500d0810550700b0010b104801031305007540c1e000c04080c00c032100c80040208138068000d84c1c000344090b518140c4113500b41c141c010541d0300b05890103030b03109115a8008054506503110350 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 698172832 1250 698171582 698171599
    0x7021e1c0c020a05090c0a090b0f1602121e0f0609030a050d0e0307120f0e060d3602030601060f0e01080405190605010510051608070807060204060201020a0809010506010e 75
    0xb4000100c4011454001c40da018038a9414411020508401041da200e00790b110803d41aa41d400b5490507800340060b5604c440600b000140e0b540c107040340c1c080009030310043c11124408000c1c90712500d004842e001440b07241201c41041c8100304002c120b05000a4a080c009110600d070a001041d26800358101040031300c503000c1140e11642c4c0881c1c01981d41015620b045940701e4145041c00d403064913003e0440700c041076000c6050f13030318144036500d1480b41810103488035181160804610004000c0e40d01020b204150603100340c030b4582030800100d983e045400c8210031800380305004041c1049810392012003884038020544403045d0304a01007440011017404c105046603140d060640c10a0402c0541040303001c540e015080402c002540940c1c143da006071006681c812071100700356003c0c491440b501c0e41000650702840006045000148405403041030041d0400072f01d0350301c000503038009400840c0940d4000c038000080d40d034011201540062054024001030800da8006440c2008685000c2c1c0140d403035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 698174082 1250 698172832 698172857
    0xe07140a0909050304170303190c08071d060c030d14100e06060708070302060106020d0c0302060c031503030403030f030b010e0d020906010e060424080c041202150307021e1c 76
    0x501c10b0320000c06c2020300001c142d0a102c81456283c0d8800c0b2016101e140c04040d18000445180c031448411750290344601090f51110700301a60030322901500d1036141c180c19843c900a546520b0302808041125000854980800c001c00708191082aa4000941c07500b403401c04c2090000f64180d24100e4500626156850311a04003051944c07050080140040b0300000c0c0c4481015400144941210131581c02c0e070301c2c00740300c11404440d0a1880d150140060340f00d400400c810464030001140c0001903d00483d48039020000440e0544e04540e000f9408503102d892000400c0341c00d4080e04074055024a003030394035091018002000c01025003c06400303040b6140004501340d000d880c240054520042c540350f29940d4511488031509218055140b819090342c80c1c1a203081d010b40551401007034031b030320503905003814110b91041c03100c050141031364010381e03007400004641d40c0c0d03d00031070103a9065406800c0f9038801007880031450700220559a4258064142c1d0140d22400a100c40607100003860500d84a248 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 698175332 1250 698174082 698174093
    0x6181306091b120213180204050a0e0d05070b0a0c1e23180d0c050d0507030f0803150a030804060e0a17010b030d031505010e03100608010e07140a0909 66
    0xd5600b54509158010070208a243d4031110115906108072409503c242d43c1250b0482a10342c02500b000300340240500075401403800d50400c0d981305100040010b9205801041d90340382120100354503011820001e014800d000080401c41e502142c90303a81071100b040c48010040c030030b195000c419141419284003041a1901c20141c17a50036204003464118020a1034000c001d00c2e5101c1d12880721904000302d401c05181c10601c1c415150141c218503110016840d10050110120404c40210307218000d040c804030014880c1c0b080d000200e4050740c2000d85928000c4004042080c812101d1442190400300420014150908481c00d503911480c100401e40e0521001c02c0c003174071041c0c100d2aa030903800d00543d80f035030f04c055008403000a4103d00700c402884102c071041e811501c91414500340f0303064840c4180010b5019100650440e070b40941100c18280c10340740d641c0201e03a41c0e50402081a515101003455841080180300d02904252041d140c07030032009400101400c01a104a202c81a190a945001d204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 698176582 1250 698175332 698175353
    0x1110910050c01150603180206040512030d05040f02042a050d0f06120302010507051201030b0c0712030506090714090d0f3509180612150618130609 65
    0x100b00100a02071181c0c0c10310001040070f030a0081000003450140880300314440e0001a0f050182c014240d2803034141040d0a225180802446020082c44108401e0000103032609c503607407095020b0b02140440c80e00d01d10400080c1c03030406051600b81008145010010900c20280b440420f48038240a5544c41c0e41c02c008502900c440c61527484030901e00800041ca0b1a0502c044a09161190f0700801455881c200706507950b004071030300804150010f10041c0000340080c00c0464220340c00102d03503410309030540c2e2040c0c95410300414600000c1d80b50418404941004008580c2000f901c1c00e00341e4002000c424050202d00502400901c149084150034061041c0c1c04000f10003560451107200c201d540312103a0104840c0c1026804510141c2480c0c040540540c0300c2c2a960b805400070041c4a03440c50504130b05641c400c01900080d8011410b40602101141c1008807101190300c0040640c61403400300104070442e20001300702002c0001e120100a081e404060440c030405500c00d000240390603490500340481c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 698177832 1250 698176582 698176597
    0x4050702070503150103260d05060414090f0d08060d1b03120f1d0a1404060503010c0309060b030309031c051210080115030201020c0103020c0c06031609080111091005 73
    0x140a401d6a1054425204c11400e050307a0050a00ca01c2c4c3c0f0480168414030a1000641c8000b6100c0912036403843d400c035a00708135000b0500800100f141c4a03412881d00150000741d40f81c20095100c00d44101c0c0c01a401d01c10100c10480b00d0130400c1040c948240441d01e0130816403002040000ca40801c009106840050f040145410900c216650041aa8040c00ba04001074040000c60340b90031007060046058604040500c0015201c2c0302c1c2c080c40d061042d6602c881c0000655807044c1c54071004905a142407180148000342c6641c0070600c00914200a02241c1004010900a4008014a00c110b4500207050500d400440302002113400c000001100e00d4041d8411544203250b0032418089440e0000a005095940c0c54000f008a550801d801456001b0f05220080c09600f0001061400c1e6003c0d80c040c1007200002010b89510600c10400182240d0040354a00d801c241010003c61031281c5c4800074101800c2504002c00c000c5c150151058918060300d2400c0d80708244401201700707510310400a55144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 698179082 1250 698177832 698177839
    0x1e01090b0a08010305061302210321100b0304080f0a02030c01020a0c0209060303360a0905071713150f05040f06050c0f030130030504180c050306040507020705 70
    0x4400901c4801440c503502880103882a10984002c03d60fa280340713000c0003803001e5008010b0340501004864240d0001c0c80f54000150a00003481420288400026a07510400082c1d013204800e21b40514244035003072043d00054030b0341005004210005a5000891b00010501c20400f6241c441031041240396210700221520154004102c24050a41111408040380d208494000055903104181982d0b4014000b454074080c03c0064803c0740010402661a40c59100c605c0031480100c00802044820700203a0015a609698004000000d0707070040d2840756600b40c140c030141d55401c000c920000c40800000e40504070540c000e058003075a103959072050941c684195018000c5260a00300740080304244041950880e09142c0010306078a442002c442d510206240003034196400c0c01040c6120101040c8462034480e80000d0656404824002800c0c00303e120303036107423561141445c1c52001002540c3c031003440150304201c00e0080c4980c1100507650301440651b000542a580d4146c200e01c0c0c411290f0080f0f03003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 698180332 1250 698179082 698179087
    0x182d061a07020109090b130b03030c0f1006060207030f031b0618051002090d170d02030c04030302010b010305060d141606030b04060e0402180907051e0108090a021e01090b 75
    0x903a2011100500714040c002d0b20b0f42c8400581c0c4110000a40b5031400f00103604c110b820840a03042c68660380888541440075088a082c1b09001e81180d19020302d10214840c15405151000c00b00000d9000300c02c06043c00e840646080703072442c2d0700d854120004000c010280251407210a020000c040f0700303c8006500f00006024090764440b5880c90191031420a40d0540200b03404440140ca4034000ca0700c25140190030f110f820708a40c3c0360760012884003002000340105c1040528551801400913501540d1401d00d03881d640c0b861483d002c2d08480030303003000c40d0500d42082c04000b00740e69014225aa01600813084005c400080842c440c00c062203803141506003844040085880b03030345503101c840d8040043e2001c000c035035104c020307404404104940007540310034001e02101d8001d00700c18295803c0001402220f22203502c9100103110290028555a0503070410320320451070750f91114240b41c101d0109805041c0c490030079004291034441400807095442409211508182d2280122800620001c074910380c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 698181582 1250 698180332 698180369
    0xc060703022817092d060903010213060306080601062307060f14010518010812070302070e0c0d230a151d0604200a082e182d06 56
    0x55078011521050241c11400610001c8100345d0000300301c284d00025000d14039803102020002c003644048407141d0155000e102201c1c01c0c15000b061a07018007510f481c0030440c80d041450b030910700b00c41680090300b0026010b11061401902c076900c280c040882e80103041d07840b5094242a0b01500b0f58949080c1c141d4a0030621402e00c2d03041014050584000720fa21300e02a500600c0c4100380c200007030103003000507004989150206805080100f4403e4400d0054500d040d64945022407815000c0b03a180d602c12400140071210768185104561030b0b01d0070103a0600011440c0d2041c0c032400c0000034119118242c0d1945002118000441c44038020800346482c8401c0d0300001034560001c1805a46e424005c60414420909030010f2120f403180662510740314508103000304d03a04851141003e4046400001c0307511820f0642e02000000b40c50480c00000e0903810030b450304100b44802c0c584400d9022540b840c00002c2490702c91900d888020101405450603a041201c058020060075203501c04820b650f18a140c45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 698182832 1250 698181582 698181623
    0x206070c0f0504060b04050f040b0604030f020f06041203140d0e01230103021804230f0c01230c030c0d0f11070609050d050a0b07020f0c0607030228 65
    0x1e0760320860a9410042d03450382400162000c034001c0c0380d4040740510080c1b00a0030440705031308035130074005c00c003050700442200403e006a0064000391284c0014200460070341c01e1011102400146c00d940d0345142626000c060342e0101d545613001001c000c41d4101c585510000c1c441070320514901d0140030040c403050041c14a008100c018a10051614114400d5103002506868981220340140c8026403266003040b4254101a000f00103c0e4180260b0a0410000b0a4003102d05c5030117100748002c2c04480c2040100303500d000540d04070f8904009200c4041c210300070013100341c2c001c0f154038074401549403d1840da555040d4002d161a6015501c1000e00004009600c5544140800030a4441c010000710b069000c54542642c2c8c01030304007040f444c0300c0401c482e08103401418a11801003003618103508190783e40f001940d00980c1c04600603840080b0300014984c0a00000c20030301ca044070400d00c0d0144d2070380d0217500c1d88010382200c41a80b406003000c405030385417400582002075001003214101403401c00007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 698184082 1250 698182832 698182853
    0x5061620090a020a0f23030c0715110a1101020915040303080703050c040302150702190f12150c11030a0210050c03060a090f0b09010f0611060c0a0c030c020607 70
    0x2400d2041c01024045038000c503440c0700f2101140c02c190390310800a1040c000076107030752241c040c0c4d61002d075480c041c003240c03184040c501460241e0640080d4540e90411400c10a04030640b13412006016464544481c1d180400c150850b40c110289042c02000a030090300018024001c0c03000389608800211a542c5613050f180f002841901e100e0748411925172100c2400320200c4500305d402d0060203000b0842031002d4500b0080c100b070381d41c0c07030309071210f140c00e120b0707404282c642c111031103002a90400c400741404215024503440000e0843c116420000051076218800300400224407052025900c2e140e01c41041e00c2020100c14903000c00d81100d0f030303c412401d0025601c480051002032503d103400d0210b21030481031011030b806190002c0c56060194100b48114000381890020700c001039965466201607910b4071101103001f010071030302c2203150519020010b441c0096052040d6019004007003000740c07250000b8180d81c0205001c0c03811000c1724100e8a0141c402508000000e9441000450342d81c00b0080c8a200 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 698185332 1250 698184082 698184143
    0x2c120d0216030c050906060d0c030902121204031e05030408100501090608060612010b0337021f0909090609020102010615050d0209040906090503131e050616 69
    0x216007268001101d8418800380c02c0c00300610344065004100100d117082084660041313001403030300d441d0940b0850048121004011000f0210b44c40d0b80241003035180000704130707445003010b0000d40305070000c0c58030782c11651041c3e000040c1040411990185800c0e030700320001c0020380e030203000c83c0e540b07540714004681e44401500180030300e40d05203800420140503a01a11040b00e0070b078030040a040d25100c0c20043e80000a0303121031030342d41d61440440c0e40c5903010054000004171034a20800600e9804001c0003244220000789000d00048400440058584281c0c280040396985191051029591000c803405081e0750702c120200c070300f0580f00e0010300105030300c4480014800d8001300145540c50b100c40707101c40170070394452020800500c66810b038548a500108100680100001104d15160781c41004865841c04e080d141071340b020501c495180d80440c00c10014003081c03000100c01c1c0c000c0c0c80d60319030041c0c002c0c0644c90181030046040090140c88a016000c00d17507100b490100c03020850906403c65105000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 698186582 1250 698185332 698185337
    0x20601090605040c090501050306031006120510022811070b030906060315130201030e0d02160f050a050f0d060e0105190216140a06090503040e06102c120d 68
    0x41e000140c6103401c3c41080c400c1c00c066101c114840e46440300644440d08010000e40d0140030b0380e05c10700c085000314403c1102400d0f40e0003030603a171204141001490850702a05800000e80f04102031130709070041e0800b801c803400112003a5a90010303c03000c1101e00c80c26064020030580300d180b101143c80308110000c1d5100b07901d41c5044849903074501042554420840f039910b1683d260180207d50403000c40791814001034010b05002c100c0801c5000450715004000031050b00603000b441c1d00800c181c02c0718911a0043c040c003284030003c0c9007006c0000d00403400620840340b0039906082c03820307403a40360b10000203007464002c5010804060960403590190004965088208010071500c41d011203241c8241c079665150006050130100003aa11112400440741e800000ca201d1104d400001882d14052050060702c5000a9074599103010034941c50313242c0c05011a489060404140424154000c4410096071b200121041d0b0166500e040c1c07401c2100c451500c0d0b5003013007103100401c0410000180042e5200c0c1c039035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 698187832 1250 698186582 698186591
    0x252c0a09110f1023070f1406010602030904051e10032108010302040903030e0303180d050f0a080c04210510141812070620130614040e0702060109 64
    0x4800c1101c03404410b40002d40c401c1d01c481071400401d100f0b61000c418120030b040b0380d81203804809203048103900000c100710354802480d525502000b01040100c90b0950120000301100d50515001a4803406000005402039540b00000790003500d500e0109503800d510041000e6035400c0c0002e02c40000c0c80c0700d0005507a69103494000c0c00507401d1290ac0500005010b940b007103601d9003150f08200203842c00701002d81c10181c54160505884005000070742c0500281c07442910201000712000b0706000000d00b450081c00424441181c042528070201c4400c2071652411112583d41d12045605a026540200c0005503d1407040005040c51850b070600700c5000700200c0300040075a88850064907020f252002c080300045000c14140c0c3c04c0c28841d4403002610754190350b007021900d4040c030025040381e402540c10030f440780e8100b1900350700c82c40103118a00040e624545403160440c0038031030030403103441020204031651901d16411751003a0141c4000d4980401c3e8204641480c420003503843c0b400780141c000c0750340780 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 698189082 1250 698187832 698187863
    0x20709091a1503030403110f0918120a050714011103011203090e060303090105030408070b0411091311010c03020c040603081e0a080105090403031508060702252c0a09 73
    0x80d0000d0b40200200400a5103024156610f200300c8103d0900c8580e00008018000d50060352030034101441411701c0c203064150b1586d184c0c1007a05c0c150100400b0242d40c10200428841e150b8880101c0d1107a0707802034110b18928810400a500500e50260704a802c6400400003103080c0c900c15214a5043d402980d41e1407a094035404204005034080c0d9906604d544200560310041d4051005181d10500a4a859041102d2503c4251200030110f608075440300c03c040e10070060b46007140025800c03040740d140c2034104050a40d908401c070030b05005040d05122500c120350080501c20000c80d0044800540203112a66583c80d1a00441e003140c80c034034419400c031000101c02d0211801c2a1500c101490b42c928205900e00070074131031113800141c015001c060f111044069645c5c07215000000a03c00d14000380a40d1400d100b00070b081894980c400078103c603400e00c040c050b800102154a0550354002d64050740b80c0c0d1500c2c010100c590200c2c144840c40000a01086092a4282d02010a240c00f8682000200c2e08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 698190332 1250 698189082 698189101
    0xa03082115040c0908070303180f090603060e0613140a05100501091b05040e07030b060a17010f030b0a051f0305070303140a080a0506010e03030c0105060a080d020a0f0201020709091a 80
    0x100b170080c0c4807141e1006108101080c41078140969545046004019050701c80781201c4060000e45c129031402a00c82c40100100700c264425101740761101e00240030700e401c1542c6042c00c101e03240440542800348042d102c40d40740f00144001d0780d42e82d0384001101d105607e81c1d15110040c01003481020420b6141c5041e045106040c015403000d00422036884074078287c10b0100085084d01c2c003805500030180d84056a045580310705000303044114860301e5400d15202000400c3d845101c05803c0500000d400345000c00002d2041000315810084074400440c0755030ba1101c42d40f00c2e80c80c514600d4560f040301d5440000a00602003030071410f490180e91804c1700c020414980c00c59500c83c1c90a400006007040f400202034658951080c0c3c1c02a005142c085c0386481580c001030f01d103030003142d11f0401c140d45d16070034040c81f4070b400410b01000341100000713008d142044000280d00c0380e800210240071024002072001c2168800d00100b000780000b414108584032650a24070041603e40905030300300f800e00c9020607008e90 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 698191582 1250 698190332 698190347
    0xe0606011103122d1005152d1204030e010c0f031d040203093901140405060301060f02150405061305120a0e030d030603020a03082115040c 61
    0x60890003546000c0c1520340c5080451001030040010034984840c0c4c50001c1618034074904003001c21404907120341032805001e1402911a4041c91007442c080391fa250b4251003010654280c82e2100000c583c40301c904096101101448004860030000300252102d45000031400b1540118007a944103e14001004015103002207085006482d01c66203044500000c1c0c428404250780d054418650040c000a0001103400d0b6041035a07080895000b10001d10a600410341c0ba00511000503da000c1c20980098003000100203241380d0141040707a814504d200c2d850040c0d04850081c00c02500340c944c0d075a5141030043c413281610030000d0044c002d80c0001c1010b44010300d28903004540101c042c010607101e2401c215000d1a940d00b0498150183c01080c54909403054050324094249489101c18030303400c8400c050608916140907028946440400c0c405a15007441700c00c1640c3d880200a560303520501c900980b202003c10210ba007244c0320001b00442c60540e280780201003038059405104041008506a8080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 698192832 1250 698191582 698191607
    0x3081c0c050313020f040903120e1203010b0906040b0a03050406180c05040b04140a05090d0221160b070c0615060c08090d1a1b03060f0f0a0801020a030e060601 70
    0x540500100d81110341e62070b540c4280c43e00c001e0170700300544103030400700d41902c4511000342e020500c4020301d100380200d40d000d00300c6c14510010180c07800e43ca0341544901c40703000c18000d92008503401319820000c0d480310000c07a070181900070003864403900d0340d01e0024040c0c082228115011403c00706030069140000304a962041e40c4400c00c4401301d41001c09100007400081009644aa2201100e0700c00e19034505105019001c501c1001c19240f4144103001d1410011004450440d40074240008540e07801d038450444603885091960340d070b01d0610b68808503d030b20030742d000740c800c60340e481c180001140c1003c04110030a203c0c3c0004e005003400e200f0f180140039618841d210106000d180594005510207005220052008060b11107200d110340354484204101c40e142c42c450591042170084c0e0045c0e202c040020441c0c9401100d145240007004122884900c0a00342c0c000c2030350840c03201e6141d4900300d91030080d0a400c0001c5440301d051000080280c51841c2b010b401c03501460004c60140c1d44a0100607808 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 698194082 1250 698192832 698192837
    0x315030510050a0b0a09090c060e0604091a0918010507030b03100b060c070e0a0f0c0915021e100e07060c020607080702041a04050f0402100309050c03030403081c0c 72
    0x2280040981c20003800c00104141039955860b5561149540c03a116200090f11000d580080c00d0219440c124046c0900c03600b01308240010203080c842d00e03507a410704a409407040b094010a800003540040c006c880c9803601460761040c640410440400d040700d07051148008003000074481d60322221402d400300c6030303d00c2d42c041d09904a2407003210b0040b41504010881640540000c0c50f26200daa00d050074213030b103a0000001d564485040c010401c900c1c2c090500030031030f5020104504000c00c500604200c82c1c0c3d00c580029042815100c25001e03000740230080100b844c00e010b1a806c4109803102a4507040c20240d411801460003103001d0041d84002516002d4a180d85c5514a446082d41c0821905030030820f000c49080c141000024010b1710749000d001b060390381d204c021170159105d00003040256030004007480ea4100b5900f08000c003680d105460103034800064140060801540e00f0300740e00344500524450380500c80020000100548080200281b000118091031070080c1035140741c0c107039940d807000b0200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 698195332 1250 698194082 698194093
    0x1603022808150105040b0a1110020306011418041a030616110f0c090c04091a010809011b0e04020904050108031905031513090213050f0a06120b090a020d0803040303150305 75
    0x11800b13140140305c83e444d1402c080c1c12a23140c102e501460201c1d9440040a401d40210030700005507080802d8151179208100b56a0a0010001c21590110094103000748115196484980e201250a00840115a016064030030034075040441001d401c16440b84000002c0d0314850f4050414004501200707910364101c0580041c1c08c03080e04002110030050704d60700003d07100b0000020000031910403884407503006016020001d61001c00540701e0340300280912156410554071a80c00c25550302900004416030030280c09840040703000c42c001317000340701d4401d410610b010000b254095000000e084401061783d4011449030030302c8812655400203072140001149100420038141ca80f1100c05021a01d0321940040c2800c210b8000400305400d82c2030050711a60303524148542d10549800c19680a44ca14000744000f0b882d1546001c100145907001411920305000819547c01080c003070700e00c01a8006101640c01002ca050078042c0c2d51041d941180845e140808075420400b0303400c0c034101140d411002405 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 698196582 1250 698195332 698195339
    0x3030207050636030f010b100c1104240801021b070e130602120f04020f0f0a05090a0e010203010618060806090c030a1b05040302030c0d0b160302280815010504 70
    0x2404141c1806031001c100f40b011150f644961410000ca403030440c11800042038003030103401841081000c15206d84d00700610b07511220007003400c0c07c01001c00b614042e078002800284d084140004004a03011120360b408030f1170400503011074150098580c4c1d1015000081d00358101850325a82c5e41240c2c42103040b90011100011800350a000300284024010400586841e48000404c03260f00000c641001100b00304600703110540c1005007041d100b0034000e603040c1c44034882c803c0c002003044001c0d2150f40c0c0b048107002e00140705140d180c2c109100d4440d1340c80080d500ca50f118400030f0500f261039440103003440440103000070520301c5061240d008007000340c020895920b801041010380c0c9d000a000300481c0b80c030382c150280750301648403000c05c42a0040c0c0e40c150702d943c15481054104400100c48901c1480c80c42409808603e05500440d00202070680e0b10010245100c8180e010740181e080589202d540040880001e0003100030000c9003404954a42000d9030702c041c1c41c00900600c20790b449001500911050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 698197832 1250 698196582 698196637
    0x302100b0306240316080c010914190306060b0a1706130c0203071407081510060c030918091703160822080a0306050303030405100b0105160b01030302070506 69
    0x30010078000095141c0f940f555080424035001000740d05c0204030012103030800665105018187c0c5c0c4c00b0003440e000b00708a18041100030105465011188520840d898601207009060440b40041d580940184282a65100304490765000b1255500110760003603002c002011954204502c1410001e013816110f424000100d001410b260000806511041101902003803214940103624403100000700825428104800e06001c1c0d40803d02c420480d4050034020f41d000201c0058059928030b1501c41003002c000d04045822517800d9002e040c0c042c60f0286042c88908098001c9244103004516080904404814102d1944800c41e1000e00f500d040590038103486108004050700314210f4020703591100034844401800c4487c40004032010346001a8004035180c1501a00c401800210003030343c11480c03da00c070140c880c4130000700700d13144d01c0d560481029183e005500780e84034050800c049a1406a26281021000400b800160050311079141300203a6440d21000b02c030360000d801400501c181e21882100c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 698199082 1250 698197832 698197861
    0x506010908060a1a13050105042906130b0414030c010801031e06110d0f06290a17070c150b011209020402090d0507140603010605040b0c0c03030f070302100b0306 71
    0x106540e01c4d103d0742d09864554078500707640010a0300120008981d4036200410046030490340201e036042c00b6400c802444107007440100300a00b0b0302911240e60300d20010081d040c400c0c90320340111041860110b0f010071460495610500d20200c180c044030402c0905100544a000b000d11000345072000c10074504c80750074104802c3c1141c1c5440b07180302041e0024003003070b00e0755550000380390241d4150f07640c04000c801840300e00501e401000c0b40c512000d0402c82da43e1035051160041001198101c00008203641c4007032141320b078490040c0c02a45601418105a40d008200780007501b01504c02c1c1d000c00380c0701e10740900144180d02c228a0b05844411816105042c0c1030081c0640c018280e074071030750a002000700c030b40350003004120840c0308401428031607081c00b032000010305507103021030300451044c0018440e0300c3c1c101c403c403004da940f640c80140e1a145410700c02450421085455601800302044218030081450060144e0394826020b42d46185a810b00c0a0b003250340a4481e940c0c9a4054800f04800100d46070303c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 698200332 1250 698199082 698199101
    0xe0d020d090f170a0b0901020703030f020a050a0c03050c190311120d0e0a050a060203090d05030f0c0322030504080717150606130807050f01030c020c01030e03160501020d0506010908060a 82
    0x140c2d9503821341d43c0c40e42ca1010104440301503140e500010020205607051280f40e000004021085003007446050008242d402810b01d0241808082000e07401418080d00130307a1580d84158049660116815a00c580044403951084003c5905a1140c0d5030820022501d103d80c10196040c0c5400c0ca2045851032028103002000091180108441d00d000316809000001d00d0a00035400540d507410180e440070724058070b80a03c201044002d1080c0b041c07101c13441c0c120360b4122400107806926034903520318142c5240380e41140940e043c2402404402019003160203442203c6429058400081c1d580000c54034400c0066000f0100c0d03080118540040003903d0443da40001014100c28100145c1c55400b4004003c281c00030f41703050f40604010407032032400e00700100384c882003840c2c1481500c208076806540d07402c0b05c056040c1407544404040304000410400d49241c1c4011410b02030204000d030800900030762111508401e180d00700b40008505500410100e0b04480b0114010001c0380d8034612071740c00034840400c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 698201438 1106 698200332 698200379
    0xc0901030b15041b020d08060102010608102a0509040f060e0a0b010e0d060501080f06060603012304060e0601020d0e0609090c09040e0d020d090f 64
    0x10700140c00c56000740000c81c80b216802d000030068490103040c20160040440c03c0501c0b10340c0041c00d03415070603840d00c40b09920388800c0c0c012070076201c4a010f05400307a03000d0902543e109841d40c0c8507004080302103161600b14020101c2000c0510081c1150b0000500b02161041c3c1501d071a20032400007207e1003404014503407500190b001241d1004104d102d001d80d41d43c642c003840e40d005200c1d400110b2402804680860250301d0003000405081c042e1250070b10034142068407071031002440ea40190340003800682503030f18010f440c0340030001c82003905222441d4825138840e00d80f01d9000d103002400070588084103600d00500020724001d8050300765400c002c0580e584503a1500d0304822161500f20aa400d08005d80d6002030300f62071442241d40603a00b0500e40ac01081d6407103c0450b0035001c283d059429582100c041000899190007180034903050005501010409156416108004c220a01 = true := by decide +kernel

theorem cover : BRFrame.Cov 698021582 698201438 := by
  have h0 := BRFrame.cov_init 698021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 698021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 698021582 ≤ n) (h2 : n < 698201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
