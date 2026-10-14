-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:33:15.724217+00:00
-- url     : https://prove2.me/submissions/57e32b53-91fb-4bb4-ba25-3e1c3ad325f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 8453244 ≤ n < 8633100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 8454494 1250 8453244 8453273
    0x4030c05100f06080c04050f0c130b0408030301060318021e06070c0305010605010206010608070207060c0c0e0f01080709020406080406090309050904030e01120207020f0121060801020711061204 85
    0x10a88802041030760900082d2551818245070403940d0389000c1200e070805208201035a0022201807000f03041a03080c100380c1401c082c0c00340ca104000080c2d00e030401e8890480b100c0c001c007a8500000e4a40795608400c5880b60400d1007648042420416504203800210741d507039404590081a03c10180011012041400d1410b10495049501040708202165413076a0078001035220f03030000300300300d8140070009061940680c0700343c052003031070780901205503008500e01060310303074600e448030308544503080007503a4200d00c1d4400f08003601210103002e0340b104030310051410798586104450000303a1b0303140460124400d80c0b041d1000209860301140015039950000c040c110300903c0c010744040d440d50300003488800143d8086000c5180350180303a00310f58011050043c0400f12040450070700880790045001801041510303410461401250142c02150b01280b1031501056141004516100e1001034001c0d0710507241560022a00114232415180490072070f401100740382d0703031407549031204c1c1c0d581c041400c80c01c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 8455744 1250 8454494 8454503
    0x503030714010209130605040b0301050c070b09120703020109050705010807050f091302120108010c0507020a0306020309010e010e34060507030e031501060e030d050405010507080c0a0807021003020c0604030c 91
    0xc000380c00050303a444045c01c0184049500c00074600d032130320702004100c400c000b0213140682d0400e020480002d00000981e07015540149801c0782c0c40d5604000310741030540003924140c0b1042c010500e00145581540010780d820b02c220308440e40562a4001921102c404684c00c00008500b0464032048a00c40400380c026002d0141071b100210f030f081c00d410030a1b81c000d44100010480560010418400c003400760742d50640700b0341001c2c1d15106d51500417400d5402d45001c0605083e070000003151400a0951000010980c035000800030016007144a41e100c132491440407001020741c190301d0080ca48092848103000141541c945000c40c546901036607660081d0f0425001c3c0901e420126495490611050040001c82daa6900300c0d5810001c001d000356000200e00b0340240d000d40316070f0a0650f009403c480982e4401d080076500c0d60200c2c03620b174081c0d119403482c0e03c1d040d000c0d503040d9000b000800409800c080c2d108864074a00038a0b00d6108a08034003407051085240d520100104003c280900318914066014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 8456994 1250 8455744 8455747
    0x60606090a050a1512020406090b09060d05040b071d09010e0903040306050408040609080318010e0f030304030f140f0604030c020607060509160807030308010e220803040201080a0605030307140102 86
    0x102c0001825968441e441020510100c00d00c01c00050303444000840381d03103240c9070114285820281c00074a000002c0c0110484d0103400905251940c0d0781600f5604a8080c00d1818800c07450140790140078003034155140c401003400114180c480d43c031050741c0e000704010041c02c2d1a000c0d03880c1007921403400802404141d9640000c05c000300118289000b024410780c0501c400341c0d504e51400304014a25441c2d9409050190400d001101841101c0910451158401d181c1200040e0000b400102c03c010a168134583c1444001000000c01048000148916014440d100719401180c1c0c081d94079406c14054030740340303500940000b0b40028041c1d52480e580e1340c0050221400e00c04a55911011201c05555441c1d40b90300103100c80544101040d21034014248040103003060700d1039030b81d002d801c0c81c1c018015000841c04100014128200d4a041d83e03800a802002a0303100800c075040001070781d070041d14160700050106000500310340d20f42c00f42c1011a50003400451034500141ca070700d01055071001040915540 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 8458244 1250 8456994 8456999
    0x2010b100c080d091e020102060f01080307060506010e0a0602010608190b0403030906021201030b0f01050402190e030a08040308070c0503060606030109020715050705131505030c070602120109050a0c020f060606090a 94
    0x81ea004861351005c0048181041485000280c642400241002c0c0d4100c41c1c500144036540012081e02e6000360710003004a0a52510340040e215004d6500106030460a55840000c1055054010208075101e8100340d0f00c540c0441c030109108422142c402524041865002c20b00003071103940020040b50082c94010309110341c0107a10700d07500702c0c2a401030b6540d10400c0d05001e510300c1c13143c002c240100300c11a4110f1616401c006552192040c1c1c5812005000c0360450100441c0c90500408501542c0300070700560317864481c40d0049060308a980c066810001007c0301240905000030924021500141040c0c156071034040a03001039072010000302d90400700e007415000002442c0c000d041c0030b11030300e88a19494202015803100720b10f0300c03a03200100345416800110342d001d8001d011a0341018500620603625070a6062000180c400c070781d0304088060b00040000707034a1a003548042e00601c0d07104000c2c06440400380040b41da8441080c4000866004807021800318500400184418000581544803156 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 8459494 1250 8458244 8458253
    0xa03110c040f050a0c020a0b0105010f0e09090f120405031005060d0c1401020f010207020a0e04020607050303070507060605030c010909150803030a020309010b011d0603041a040309030302010b100c080d09 89
    0xc1100782018000c5441e0014000f0011980c0176903019120203100402c500b1000b078036039510000061260905105080070f000466030b00c14065001908400380c41c810360b0b410031401c0265100f0540c14800e6041c06030701200600010840111004c842008009014400c59103071008010440a0104c1380d0101c3c50714031400009040d000210010206840105064160100064100b070b03c2c0c08680e4603164810003041c001070b952101c001080e5401514614a555990700c042070702403003042d8010b440d912010080141c03c41d44807008210703080c45900300744560359584052594913a9550401c9010540d000c00c00d10000c4401c2d84101100000610340300f1406a84062081c116482a50a9042c5940010801c41c201c01c090094456802c8203182140c0c10349503100307040e40880410b0360003e00c1060f00201103002d00031400a48d03001c03901441141443c5091618025004c40c241380f2086025500308100014180780445240094010b1900c801e161400d45613a0039031940c0c0103001048885e0b6030780500d0000310703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 8460744 1250 8459494 8459501
    0xa0e030a060c030c03090f0b0402010201090c03060504020307170c040f021b01020d110408030409180c080303060901090c050a1b0803040c1404020304020607080a0903210305060904050a03110c04 85
    0xc1c003540340003503000c0c2030503001419168030040c2c0c0402d150a0640c2900015030848426a107980c1100a0300c001b0b4589100403405030034402009410b86180e07120120901069a1010b4080c5100300c044641d80f170390b2041e943c810404600340c1c1c840f49810010b010909820540c0001c2c00440305100c00503d80807034900b42c8035103400440485503080e0340c04152002444c07110302c201c01d010f410001c8100c1c105880d0001d610354038480d9020300342019840322081c4422281c2d0141c0c41c1c507007c2e484001e00034080e0703d407040b0300e41e280c000f140c905200b05004000020034012034400d40100c40550f40d2482d10b0705e00221015113001c20311000104014039085a0680460f103081d018502071840790003d111b09514024000b124280e00c62080b03886a4410000e020050751418100e0f0311a03030303105032090749521401c5802c4d200d242060b800500786078240e64000c5010902c118081854207a2902c04100d06d48075074003130100604e001c840080103513000201210204c1c1c02000080b40301c52180088402c06070081010901342c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 8461994 1250 8460744 8460763
    0x2030c03030d060905130209072001020703050a0f0807021207020102030712030b120102090306010302040b030c040603060b031b060a030518030406051903180209060102030f0c06100b041a0a0e03 85
    0x64541d140c3d402d01c8204414040e8580181c0100c0b011170b0403c140342c000565200d805401c11080c060002d031010a00c001c8040f8600010124000031034859103941030141444e4042c21072440001c03041200742413454060141540918010b0b4001c02c0c8c5880b0b50f100d81441035000d0f51040e0305600c0180b0100c00092111003542045c0060740d0740c0400c005407040140243c04500255084151740148261411600c0000b111811a501141e01003490011035002c01d0402c9403800c1083e410030300b400f0010090107410307040a40f09020030b0701150003445200c0c0111504105080446034008010810149110b100b0f030441600500e070103460403003001c1c500c0c98407840c65109a10080102d5408210504107281460610701b0030701081c1002c0c05800b070038000b6009001c000d0039009100301c50640102e10035910070002c0d0b45000011400d407aa444003a41b45607580c070f8408a511240500003510007180a031101e10a9030101c41d440070780100c00d580b2503827600c41d494202c1c05801c410000400311407427a40e135003003024111 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 8463244 1250 8461994 8462017
    0x10e0109050609030a020c100903080309070311040e1203040302071205070303030c050306010c2a0f080706050a050f09010e0607030c0506010f0503100e070e040c06080708070c0204050402030c0303 86
    0x1410050341c40d040c0e0400400400380d1500e82c10078044120050f402007000904134104035a5104091341c880b80c2510002c2d550380001e808c261001c410081c50003400503034101501c0c01180605103c0e2110720400050f50614038080c995a000050081d024030301a03000780d90014464016208903e0b123301c888510b10060001c141c402e64000c0c0410010306400d44140c5621895503d0054550301e04240040d2042542650047c007a00c1e4070b01c0030310310b86543ea104c182144550302c18460141d9688842004030000c3d10300035041d0790301491100088050007141221640c400540f652070408440c1d0016003c0c80d000525030358107001c100103000790140e880c403008000703403403107070b2201013080703000d42003452a0150507000460b007180864030074000c90341d0014045080d00200000840e03c11288051702d400c101d03066200c0c0c43c0000800c0144803c0242c01e4000c1000d0314415a580c1040c0e5035410012950403c0981d041d0f00410030000c42d00b4094205a000302c0e41c018005000ca800100020022a00d990711141c1000d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 8464494 1250 8463244 8463251
    0x4061b020a1502030112030509030109060c1110020403050a1e0803011212020106060e100509030a03050405010f0309020f04022a0309101e030b150d0213050603040f140c03010e01 78
    0x308102d030030018403000c0034141e2070441c00d542c1401003000b15843c06510240500c8004204040240d409420088500e5030000c401e020300040c3c510060090540241b04800d207001d40e00014200d00081d1090720200c9400c03400412070031080d134840d00c011100b50585481c80c901c0c95a1000b0205050704011802000480a56040d4203a1030404e1401c3c084174070701600869041c004104002903000d0301c01144554111018840407007150400e4030319100700c4403200d4160243c09001014075401001620403507a0a8130352000c01400c20000300c0032070712140c600030b6001d0b44101c0c403411907083c280d000e8080940c2080502c1c41c142030303034031480f1b0540c0e074885040016035000091640c05070a000c0c0802030f4a84581c05d1000402d540c8000c003002c000380f404194002c05540d00189080b9554000100a03032010030188e56684803c0550007501a50040c2c048040c02c030800b0344001000d0501e0000c40b44140d0b00a50604610016a500d1640c49000d078010601c280c0716041e0001a1a5001c0c854100541480030001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 8465744 1250 8464494 8464513
    0x1030b0403030e0f060103030f0203070b16020f15010b0708040902070c0302100c0803040b06010c1a0f15030a0f0501060b1605070801020f0a030e0304030b01060305060102060a0605060f0304061b02 86
    0x103060b28000c1d0f4809166420582540300340890014a041c10359605040a20449045400480c598000d035803002c4c04500d0044240b140b0100d40320000c2c2d240b0900c9038261104e140c04801045d64a4105400b44c0d48e184c0c0c1088010004108088042c020040c81181d100745402da55030400c909903008440c00340d0f000000707220b0400c01c51030510001030220015061544d400b4490b612824071070b0200802c090020004000041c4450b80b1030002840c0982e402070b14802210503018050400450460f60a00b000280001059203a8002c42618240ba0340080c0123010105240d607800e101a2800c1c14210317415074a032140410000f5003e00503000448089443c03a80c000d00c05d0404519040c450303404003501d83d2042020145142601e0112120280c0034100414a4a403040015245119039030024100b00113040001c940d040e410342100380220001d900711102500ea81c804002100d031a03128050340710108010321307228046000c0146900c83d010301c40002d88040303915848800c2d20040e0903010010703081456074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 8466994 1250 8465744 8465747
    0x603160e06010e0907020c010e0f040c1e1803030309061e090302070902090f06070f05010203040303060e15060d0b06040807030b011d09060612010209031506010905010c050d030b03070e01030b0403 86
    0x3405000c00403140904c0038105003601a48a401d118841410810390b40c0d0b0006098a1309007101801501c060020415080d40c0c84008041402807a1050300d01e600c41c4c44000546842220396140400c0201e02441b622071540ea010ba004060341242211b03e26161081c101d400b15500c61100d04403244400003144210003440d0082c2081e001e40c002e0030540344140408000d40c1c4468145441c40c00b002d1b02c00a0341c84056003000700b1308510060004010f5800002040205545500404112800c0920b0480d00b41c4582c0710b01d05110361052405a0404c2d42070005030344c0114039070400500c0307040207404249004d88a0b114142006041c1d00180e030311508400040000460642e0204411a0101d40c401c201d0300b001d421864880ba00074000f14030912801000105030382083d4101c80000100034101c03032070f40307007419014200035100311003444c0428565800016154010040009441c0e4844050300300c080c0b148600743d000704114091a6014403658002140180b084441036021f03501400d045401e0f4500341c6070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 8468244 1250 8466994 8467007
    0x5010906081302040b060717120f061818030301170d0804080403020f040b1e0102010b0409020d06090c030822051519050d09140105060301050106170603160e0601 71
    0x400c404110341072082240b010401d106404003103504644c0490034031007003030010300d090148510240444032010f16170319407107210000a05a00340b025248480e01c4c0e41c1c0941105031302c0001c03107180d074002c032074007140c101c1c41c065404a0b140c1c044141c4110000d001c6c03043c62280d2564000b42c02c84003140202c800c6410100030204000d94640c0e01a02d80328004e0700c1c00d60307100c25041c044c9100080c000e03d804c94010402c1d94541e084000a0103014110b00c0012100400d4a81c0340c44119040d503026502c3d1400300011810280124605160064003144c1d400400780d8400004003015801500c80807000c90f0040002449c020003442c5a4005a104202000c45680080b903a4001035200701c0c41440d80c0e142d40c030344030f84c504003c0d100c3c00c0907410151300e007800407104261780d14032403221360150161a1410035400c0101c40000351a11580c0e84000300301075996603051500700c0f8001e02a480101d03000c012124213800c540300c8066806035001c3c007a2a40f510a06c1c09150759004e954100d207003120b082000300001942e2021 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 8469494 1250 8468244 8468249
    0xa08030d020c1005040c09020a030209060c0c10020610031707060e030301030b010e060d030516080f07031202040e0f070203070b04030c03170106140d1103010806040308010902040509010e090f07030507050109 91
    0x103c10040d50801d80d40341d01e8111590701c9a059081d0700840c010041c0c9009038141c41c07684070040d280507a00d0450380d00440d01e900014414511070424002c00d4120944000780341d0744034030080039201c50140c0c01c0d40c03501c0c0d015049c8114030099400040154900003650340c00380c2c040b44101d0200440d240e504600c3c1114007200e05030014100541070400b005400d070740741d44540303105c9030301170500703ea9801480266210480309018054039100002580300d5540714408010481c0601a03901c0d80c605c07a0b07003400103130b0070f0748940e204034420a283c04c404100010620041d0319041007150044030701c2c203051a40c0c0e050803128101d6054001c40e103018120028103420911800c04400340d05141c550940c101403020341141264038100411002c08250100a200303da80503420211000700215180e694800c02140d40d84c00c21501100080c003443d00024215030a4000d55041d141e00404038807841c1c2c2820562418000010402051071240c0d0a546010407800c1c08503001075806030000e0103026003880c00141c80d03480d043c1d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 8470744 1250 8469494 8469523
    0x902040e0906070509090f040501200414010203030c0702011803060e060f060f0307030b07050c060f0105030708070e0604020904110a0215060a0509010b030408040f060f020c0405070f030504020a08030d020c 90
    0x400c0b1480c117039521000c40c240c0c07107001e2050b00c0032203071101d0502d0350051500300c0900c41d09600ca400c0c903003840131001010700225212102c40a52003e2506c0c012a01c0c1e01040e41c05000d80041809034000540c02003000001151069100e8904250f0740e03203c0742c003500c5079240184c000e90045003e00c00c41101c0100d03450f80c00041030359a00040310703039000442e81c2c481483c40050241d842110101e083d46200d03a04582505180c94100d40c2c80e4100b60915131200002031040074400e10881d000041e282c0741c04210b800c00c17900841c29840040d991070081c0703c040e51090000d11b81c4980d450b146a12140109c00140001415590041c0400ca2034150352800060021304180d11851058000700715a82d00c2d440e41c1ca0641c3c20001445459454071300d012812406290403011703003600501c40c041038141d4804415020401107900b281e985030301c1d41007800101c0e08240c078030000040c812890524668040e806c43e03070300708e440500b10705035040d41c60000b0350650304240040803000703800040b644c81d070101c10400c4803031007802e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 8471994 1250 8470744 8470747
    0x2010f0302160b090102041d01050a0503120403030f02070b0c060901050708060f04020c0c0a030318090903050f07050c03120702040b06040605190905033f04060c0503040902040e09060705 82
    0x207440005020302c5042200070161680d401c00140c03c08801e40540e401480c1d001c501c14041f012941d0040d0743c040090003030500840000c60001254a000210400d0002e21500c0309460241141c6085070702000b00781800066100702540021800c1d9480000d000c1032000c070000d070501c0e04162031040e09640d40036100308100845141844041d0740c0e201021400c001044400598402c803080885090040d120401c50744866030305c000105068101c000581078440013140160310b19142c501d050300700c5004040150014609001c4107000d50480d000402005001d40c040b10024142000000c0c54801c00c09001003143d10003003447c20460815002c1c81e0304404084444500702420188000c149000d4040c5034140c2a000700c0030700e11490302544402001c0c20000c0c0a4540c243d9103070404051403c190b800d1445200011020045e400c4100401d002525201d03580907480c180c6400b0003100c17034410245068440c3d000030080000c01216920040000f450007040200841c44c01c0c403002414890003c004ca81072110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 8473244 1250 8471994 8472007
    0x20d020c010e04060902030c09011704080d0903110109060609060501051801050a0c0506040303090b060904030e09060604080708060105030f030a0c17090904111309050705090903091c02010f0302 85
    0x2008540108026000e2070a901e102402e4000140078050651100c44614070020501a01894040042c918090281c80f51382020407404010680204200c2e40600315600510000007040d800c0e41002c0c14440c0285040706a180c0320403a0542180d982031004c5524640e0384404000280300ea01030030f8010002400d00609065401076640c140c1c24192074500d0410070009000709c11680100b03440240107800030111111882e2901e805001032074880c13429180305840c04002002458025100740c4a29455500d000000002000340456400058490355200c4820301010840300d4003080000d004080361801440301d940343c2004d040c00e08003449821030300c94200704034580d480381e000040d401c151075201c030000804101031596030f117035802185089076103c0a030f02d0a120a200c404800c1c05840d080454008412403203844210080340c122060060440c0c004600821861a03c40d0150303134041c0301c02e820740785442d10b541e00041a244a1001044084008d02c0040c03083d942c3c0700708110b4105150303040441c503191 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 8474494 1250 8473244 8473247
    0x80a0c0e031507140a08040201021002090d030f030f090506010302150c120a02010f14100503010204080709050901020706090b0108010c090b040306020901020708070f03140606010c03120b090103030816020d 90
    0x165000d0401d1500140801043c071440c410b40c4008500042a108240c40d050880b030700a107419410b680990042c441c050820401840314401c0300c502080050008a0303100095178143c07061140d010364202816650a01c408410b4000d0050b0400c4a02c520040c0281e58114810841482c0c00181010400303241804501c0c0000c000140c0995851030700c2501d20303100c05c6800b04c2240500703115940e5141350350801c440f4100811060301854082d011111a2074075803511101418201e008910503581c0e170b98881402000101ea1641c0500c0e00040c0810026281c980551280c1c015030b5203150007241c04088690040002d11028425800c1c580510710b401c1d00c40c0c6141c1101041203004034080a020a03500046100e1641c0c001c0200800a025600550b019965140c040c0e21040f0b29503c025514074400051a0010341404101c0906c1070034143c4807009000b5068404540c00c40070302c030b502410f10303076610841240c5036946615207009510075070381c0800b1491720420304412000170b078603017805560050b400c00740340a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 8475744 1250 8474494 8474503
    0x2010e0309060909040804090c030209030c0409080d0f020706050c0301030b0703051003020108060607050708030c010b0f0a1a0f0c100f0b01020604140709050901020a03050708040305090d03030905010507080a0c0e03 94
    0x540040301d501c002c07a05d8505100c00c541c8240d900c80002d292500d03001f20700302c07500b40d0050035003048121705075440e04807000203000658a045000414540b010040b5807480380d202d41c804403a144407650010f003403a030f2554030074044a00641d040c0c901804080010000c004409403a194031a03154035050045003001240708070104440d000003418040381744000791a94403450140d0b4090f039008011182007507940c41040c0d441e5030202009100d2942051144801410004a81c0e42600c0c1d02500f0111400e2074228144141160307049640c8500c40c0821280c00038501e518041d040c0e4608840182000c150078a001c5400c580191a005c1021030404510200036a00450302580c0940c11105000854070074141560520540e5000b440d0321300e1401e001d0044104055026141c00c044a8404010b02e46074500300342d0700c0e80b0045500070001801085032400e01d0504140250f0b4503403180c1804228030303017141d485500b034500858500d0f001903440c0c800c00c444a00c0c14003540c0c10788101d0b41007628030b5120704000320ba03c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 8476994 1250 8475744 8475757
    0x50c0f030109110c160311030a0302030301120303020c06040303050709150c06090203070909051c0e0a03080c100c0c060510050609011d0a03051b0405160305100e130302010e030906 79
    0x65a51540f07255007100b85041210041c18000054400790a13484000c00400f5850f40015a54445400b8290780c40c0d00b0700050a042d140d40540046046a107401e400040311040c607d011070400d902400500e0643c0e0302080001d0040d4440d440200b224a40400e00400c0d0650680c0500324039101030171040c1001d600951050203045d0000c6020074401042c0c008249802d107507070b0000168a140c0b05024041c850080b440080502031507440500740800031004071901e24040c10600e90141d8080c0d030400c00690003800901d880301301034050324200d0640f08500001c81e401d54404c68007180382249140100080c0f441080d61080c2600d6440e824135040601213a06401003101d01414001219411014640c840c030031590011001481030450944901e0800d1b103441903008001d8680071324a07111203041c58540107052144d0128041e2038005025000100c0c05008098070a00341518451004a0f441d10442030341440b03100a0b641d003a13240000c5180003400c69010742e0841d0120342041c003002c0c3c401d60300c00301102c54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 8478244 1250 8476994 8477009
    0x15010f08010302190b0a02070602010b04090b060603070207080d080612010507200703020402030a021207030513080f0d1b110601030209060d02180702060402090601020a0c0605130b04080106050301050c0f0301 91
    0x2488810710039481d8401010b805c4002031100204030503103415800030303400b4203035400c550080c0708103030001d01400241da107544001415015501c0c006182070601e0302c041e542c01080f40c41260b43c865170720341d541820000b5204286001440c88400c002081c00d08070184105240014020011490010402044807002e42c60650441e030b0b107400f0440b03600e00d04100150295400400c00c5549040c100b810000030b41c0401080b203030a00100c40003c060300e000b40f04042c0b00c0c1d01c600c2c08181b840c56559550507415031080345907051010040c40500356030352080c8116071226002080140c044500203c0c050010030031422580c1142c0c1c030800040c0300588540800a07003120701a541242c0e2010144009980c14640c008101c411110302c40c01c1000072503000556901031402a04c8009003900c910004a0700d0324081c1d1000341039118100400c01010f0301c29001000070319211010010215200d0034800e116900ca03500a00560791503040c14481c81c5000e10504d6000f500c0d6200091a184118240c040f10b0700051080300b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 8479494 1250 8478244 8478259
    0x909060403080a0b062506050c040e0402090a02041509030b090f03041a070f03090e07090b07020d0203010b030a03031406010504050a090207060603020901090509010608010507021e15040b15010f08010302 89
    0x16140d44421041c0c1340d004d400441d0b0a12800031024906c0222407500074141d59950421003c50404034844c01103400380d03001e840850865a03120f4090000d080005012525040ea0800c00051002d03240c04240240c1e81c0701d076448000c1c552442c10055035544000c0c0010829070440a49440351010002c110b808468042402c0b0440da00310050307030b0300c03107008000700a0100d04000700040101035000e4080c206540310b40d40ea108140c0c446443c220b50308090b0780507101da992803c012040242c0307407440341c5403001c92008001080554800340401c1c04d0005c068000c802198072a8041c0f22407941d00d07019075a100f0400c0c1780542c245442e03c00090300c11005480340e041c01550000350042445103030340003440555000f919180300c650752105404000c100443e40f6480d254608440403e030301c9018020709000300c0c8035600070415014200000e00540307011018400803445102c001c0c01c1400c4000c94034600c11380c010402d5500500d000018011110001c5501c0341c1000715240d0024005a044201d19041d0781d0103030b9914 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 8480744 1250 8479494 8479511
    0x80d0c061506020307060e0102030105010807110109020a090c02061f06050c010e0106030c0302030105070c0201050910020102090d0602071a01060206010303110a0f0c050102070b040b030408070219090501050909060403080a 97
    0x10003000e940d510400204070007900456a240c00200400405210310790411540ba8025a024200e0000703010b06400501004003082040344980001d01d03101a25100004c0c0060746c0d98001899411503a0050808a440390380055030103030140103039584a441c916a9203070380c2880ccc0c00401c807a040c144c0264010f00c1750120760245a80425803013850311850020080082c140c503800d04e0700100c4072521003244a0360a03c80000d00c400e224854021140360706031921410302d120b850810145050990b104000c665007800300003a41e03a030b0020350680d403c4c0515001071341c5014500300140a800b030300b18004282102d04004010b95a80000c00d181181d4052910940300e50b0160303c002d04041042802419044640014901b8008088030000440e5426000c8030300b030361781da103004460740e005034030a1482405091000502007684000145142c51000703003901c500c51140c1c1e5840e1090052500300c110a50350320390041c012401c1280d00d07203811070100c0300200100c0c50107a600070004803004180141c900e4030f501a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 8481994 1250 8480744 8480753
    0x5132702070203070b031305120d050a02270402070f080702040608060c0f0711180106020606040c0c02060a020114090304030201090b0c06130206040503010204060315240305060a0509040f050606030304080d0c 91
    0x180c0c02c7c15075000081c2c1d0180318021444400c00e030009014408824a020b001c81c40d200214422034211403199604580d07404035550707115005044c420304480e04141c0030003009002808040381e00c0c0c10184280301e15500e0388014010f0000b2a12a034000703503000c0c1e12134400c7c0080c1460200543e078071441d41c80c800956985152914000300702c10f0031460f07908039091003142503940d49400309440c141c0d58242e003224100d40c1c030394081005549201c1450300108100700e10b0f020140c1007440007400414001c0c0004504442e0003001505040821240c0c50100c0d000460309204640c1d0011901d8011f141c901c3c4070905104240c0001c6455140180c21a01144112000c090844d22010300390f80081600078005c54546985107000f402520342034041a00c801000300c404202001d00c00f0b4901004620180c4070b010404000c44168020180500441d500210042000416942d017441c4c45d80b14522400e0400013000e90f62034500d1800302e0141c080c900c01c0d04203100c1130020035400140b520301059913203030036080d0000c503040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 8483244 1250 8481994 8482021
    0x5030c07060f020a020105061305070c020423040c03030806040501030305031f03080a030606030e150f07020709060609052d0402160602070f05070e0106080106030b0105132702070203070b03 83
    0xb604020b00224075010f82d20340660240c0d21443c0305981a9001864030300303095040364811603030380001c503100d00c2550001d41040d6008001c03140c4620b02500b08026080d04003686a442214110b6100300103000c00d004056005086c5500070905460a0003254150b60b000303815400020311a00b086007401040102812080d080800110341001c400c9541d8490308400601030051360251201107800c282c3c89107010000001d604441461180c42e601281d00c41c580030586448000c0e1001d405c6100f1a05c000c03c00d0343d5035220b00b0005191a446d080c1c1320a00c0e2400344043c01e1021100f0030501c281045452038003540c3c9200625407034104480040e074940090300d800c3c0c18449140005820f13580b01065410412008049583d440d602440444610300c1da901d00640c00342d24240158000211128010004e0500940201c1d050352030504042e405c08080c081598881700b11644510000600040b1030220300c010326102850002c200601945005d0721500465a81c03840381c0b1800a07446d03c0000051018900c1d8a0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 8484494 1250 8483244 8483261
    0x31e06010504033009150203070b04020105070212060a0606120506010909050705070b040501050f0c03040807020d03090e07030c0905010207080703120e030709020301030506070e01020606010e01050f0a110106120305030c0706 98
    0x61100181204561000b007440c403503405818041c1409503c0d0703d11087c000401c1d58842039104150411aa40390340c01141c068018000c101d802c40f00f051003c0da0344036424400a44034110710200068110f00e0508d005094142070004034404d41d181c0700620bd00f80c0d0b403209110040d07070703e602400b003100d03150721104844903c031341400078110b0350911003803004201041d04a24003404030000c1c1480b10303492301d500e581060720050702c00074641e40c01000018014281002c0c00f1060a0103410200600d6958070400500e4250031105074001035900c04101c01d1a1f504074028401801082c4014a50203044c00d910380e82d2058207002c054000c00c41d1103500c0e21140d200c2d6400c00c61113400542550380c8945d5a4079801e000c0e420030f01003140c040c0101f0f00081d500e24418011810142e030b05900030042a15600c0040d03078a010a10702d034038100300e801c000c2c14802c4042d8000401c400459540c0d500c14090400d1511801c44616800803071100f0041030b005030111390b1003029290004a560303c52641c1d109a481e05000074401d43c0b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 8485744 1250 8484494 8484563
    0x70810080a03031401060e0a030b04021f030209040509060c040306021c020a020d0201060504050402090106030207060902030f0705031002030108150c0c060f07030b0a05010f03020f09030105010b031e0601050403 92
    0x49488010598160131000c889404103060070701c166203031482550740344000450b20b0340010961004001107034194403c0342e0044d0010b400140d0280e42d401c404942e8110019403080803030380020f2104130b41d0420717114265110000070003920050034100c03010001c074800d611000c0d1500d6004a101d00403a503408107030082c80207a0840031540c0340ea000310081d465510301d2201c007000d0f5103860380011b11810070703000f000d2090350f0082441c20760381e0030410b0540007500320385415980d0554039010540140c6007009050407201a80d0700400c4043e1800741007610b07003807140c820303d414103005100401228100181d00c0844d080c040c3d20340c42a5a940e950f0090041c024030007011840e114030070078090840d040c1282c035030140150380d9007405055000070034020310011300d214550000d034035180c1e14001203120364050b04da040202d4521601e00580c480000f070965170207810103100e42c0d500001380b0508881144070300c02c034001d150003400a1440e0020000e09280120320002e8906d140856540c0802d007605102c10b240c007141e4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 8486994 1250 8485744 8485753
    0x108090c040c0e09040302150c070f08030c090d0606090b010516020108060303070b15010f1803030e0a0b030903041509080703080a050f1305011101060b03011e0302030709020c06010609080607081008 87
    0x46c18000e54961002480c01c01d050800c0010840300d5400c9401c480b0465045050840215416940c401c01580000c0c1050b45007201070110013065036460004500c000c0c01810080707651350a10750200c003242c4110f02c942d41401410411001d50a401d020000c0c002502408c05240343e0f41c0718808242184110100100108070580c2081032106840c9c54182c40b40100b07984034407800300006019078030708811300302c98600360340400010400240315402e15102d12202828041d1481c0c1d44180e00c5042e0b40007521031407150341001c282440900100511885000007515144204600d0300100d01d441c1c42460002910515000401411050040b022618266104400c0503681c0408984c8496444403901500d400030b14140e0040d07030240414040d40080d2011006202c0c80c50740382121a06c1000717100125003143c05103c61001016941c2440320030010700906201580d61140d10020504044050b00084244440b0b40720a01c540e074400186594802042d05000c2c17140d866624208000d030341184d00101c3c95210b0f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 8488244 1250 8486994 8487001
    0x703060f0513061e0608010b03012601020c010c020102071b0302060f0a0309021002010c021510090f09020907020a030801090c35010f050102010f0204080a1b050301020a030504050c0108090c040c0e09 87
    0x2809513004045805030341d120043c598a0709003003140e5100138072070711484001c2940800f90340003040340c011031403400480005141a80c03100340b0a0035106031400e0030700940d42c04501310051003010b01000c00c6607031510744070704002e9081d580015018045d01e522190450804541400c15900a500148000380c000b04140c44070342d10b04400a02030300300f2540d4600140a07068a040c07103034031508441c600a0340012132407180f9a0801170031170014401c21400454070f0ba103900c101e41c05600c1e455400d5005038001c1c0c4c080d050844803410040c042080c180c1c0039200303640ca8006202d1240d5440000030600c0a002c0c00300d8000c1c00802e0f4500245102c4074160007010b100d1090000844d100e10b0100c00e011218280c00a0041c68100000b11b0100d00591180740d5040d0840c140c01c40c00204145220320900480800781e1000c20348880101f8220f03040034010102082d503910621091150410001301021000d1030030078520716000c9851500e402591114038002e80c6c80c3d103151010700b8025003171060040c1000d05014420b01c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 8489494 1250 8488244 8488289
    0x3130803040f050c040903021c05040509150102060c0703050304080313051e0d0206040506060f0a0306050a02040302040617100f06090e15060a0317030406060902160b0703060f051306 80
    0x250800210342c5481072040c03500d89402d09000d5120f07111f80580180070402d0100c00b609000007100e113026030800400300000324080c0d0380d441c50a07000702050302004518116040000e4641400074141100206e400c3c0282000a503002d02140c1d44a41d0028060b52a901c4103014000c0303c0003800e00061040c0541c03041d440303008030342d440b406101d4412807040b0303059031825280c141d0f00c800c0103640282c415080840014024281260060700a040c0035109201d12603480e140c140c100c62064554119081c3c000030f0401c2540b809000352400b91109540e41c2082820000c54240d449600c4691841c400e42c58445010780c030040e6038003090061130185414001c0d0125180001d03160611550807200500d1100007107a803500b00364800c2c00650343e0000c41c242103000744802c2c1c000e05810080c8119600c1b5162500442c00300210700180c0104011903551441c000514503006451803c02800142050b2400d00e00708003003508034003000210350080d80d945030542801340900c0046e201070f40180317140f0b00c03280b040c200584 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 8490744 1250 8489494 8489513
    0x1020c011418060c070201020a020306040506011404020f09090406060513091505090307081312050607030e010c020a021909020703050d0c0201020403020d030f11072304050103050a03050313080304 86
    0x7038003445011051540d8051041a414500344041d404a500140008680282d901d0040131542d0050040b036803410301c5640040c0c54200110307400c0b11a6007040004000b0079011154a2038200c604407015818503e840009405a010380c0101512650a40300400d050103860fa004a0180c0800381100008100005561000d8000e00c4400c481003c00004c1544001a151040e14095840d850166150513442d8071020800d4103c4203500c2e0000c808090b0008000903451603041a051150014110038503000c1000750460356111003005041c1d061055000d0a0756001c914a10340942c11900c50380f6240310b440700802009099005210301074400201c010505030000080d1000701340c400400d04c82c1540c40030b0220b00380d0042e480000e4110801c1410100000e0041c50b00c1544856a0310744030b0004a200000d1034a007110983c480c0d441000382c40d0020305112984c2148014440c016136081c000c0754516510941c0d680c8100314043d04002008c4086500d8801c03e04c1e10340f04d11074100441c1c503240d045c2801c101451 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 8491994 1250 8490744 8490761
    0x9040f0204091407230307030506010b210106081806040506070c03020a0b0f01030c060201110a0809010b0901090b030d020105010b0a050a050f070606090c030b010c0204050702101a01030b01020601030818010e0301020c01 96
    0x4d4005d400a031036803450005407403420b0320790041c0034028992030440c03c00b4041c0c0000d000300c048121444c110f017003841a2a08810300070142903483c1191424241d90102c5444400c4e050005507400010411010920000e55144c00528915040c0903580241c2002ca0a1516464005003000511024041054403c80b03042d41a02d0007218211140e40d500d10003a401c940e4101d81c00013003030034140f01c6003c41c24010380000c0da0118410b000425904d12440000d0400a4241c000801e21175442c01034612604040007080c0403c0c0b01d41c002082a0b50415074203041c10302038118404104075001030103961b1035100c0c40645003820741c982c0d1301d641c403240a0318015000e0050380c0135007498140b41400390780780700b40300f400340c01074640c4184c5440c210b0307008030b8083c0000340c01c00600240551080c042500ca80c4500c2e48184126a146000111282c5041c2c200040590380035004042c110f6018900510104030540c0c1121445042d6407055086c0240d0040165020140c00100b21790551001c40c0e100d440703500c19040880c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 8493244 1250 8491994 8492039
    0xf0905010c1b0c0b0306060c0d02150c04030b04020f0103020702090c0409110a0e10020c030d030905060702010b01050d05040303060e010902070302070b0414040915050118060509040f0204091407 85
    0x710b941144103802d260700100d2002d4182200d86004010800140006640140b0050840ca240002e1201d03054a050800319030140164001d00b4806281c18000512a4002d201902ca0758502441c3d0b840d9100d81c0540036002a1103070100b501c807030040340c0c02681190b01c12540684a0321803490100809000754015100e00d03081c150401301e2503c12044a44110340662056072220410300a1090912806040c040168070540c802c00e40c0341c403419a420012101b03800074558011948900a02d0f0050902e400a0f0210303041d681001101401a038020058079030201500340f000585a0741d81c28120090320304c56001c0f101280880001042d4205036400910306c0600903001c84c0c09141d500e00d4828824803441c803034619144800ca5021a85203020340181c0341c0280200000360785900060a6401110b400ba8480154031120110000d802c14107402001d0007820100c6180110f464551034420504a0b1f03d40001e104a645900301c0b410414548120031030a11002d0031941450f464201462103400705101400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 8494494 1250 8493244 8493257
    0x50703030c12020c01091404060e0901090611070302060613110403110906030606010503010b07030203040504020c0708070806070804020d050a060903050c010b0603241c0302030909010504020712050d0f0905010c 92
    0x500315000203845010808107a466502c580c0c80e01005080c0381f801c0c0e80c0c05a07449034840f200002e01000d00003485001d00c00186c00000c0d0020300340b070f1960880e14209024a5440313010b2100c9008a40c002c507486620001c192004988007061120f40d41c000c2c07440c1c02220303401150124001c0140495944001001003083e54102641d840720700416545060413100c1d5400141c081005001d10310f45a000b03054454424012a82850303210300008069800240d11041241e000c104104200c100c104040c0000b0060400541844d050003240107050310070046c8081e00681d521104903040080400c0101c40700c0c0d8200ba0301b0814101140780080c803035800050048429820800c140005103002c1048034003e8081c00c0c40350880246001d46141e8102c107101141d540038040012020511040106070742c1024841c1c1c0c0550398483c4240200080f09030183c000340e01482c414040a03000a280451500c05614035081507511940000d9190024001203c41944c445060101d40d0b8100101500709007030220b9aa107030034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 8495744 1250 8494494 8494523
    0x20a0b0c030f070509010e030106080a060617030a030b01090b0a090e06010318020904021804031206060801030f020906150403050a020f040216060903021606020d030506060903030f0f07050703030c 86
    0x500340d001c152849082c4100300c0000c1140140550300070300d24950181003280844079840d0000703017100d04591040c20703240c22008000c400c004c03c07031251201070100381e80c032011000503900d5180d03070b0790045207420720034980d4494000106a0060450500529080c40096942c03150000002c0035890144585020072607400041403441d8000d010704c060f4001c02d45050481c0c54810780800260300b10103441642c02c80d000b2190321200e034032803c412074402c81c02a1101818004c0c0900d02d042140d00d5948038000700710142d0010f20000b00484415000300390100c40508980d02e48070001040f032501c41450b03171038002002134004108200891040c0405008490242c0c20b001c50200b84030076442540c41540502500820100000b8481c6c0c0c0042c0070703d8024411121007504001500030903040a8002c000542c0c0310710140a100c5602d0b0160984c4038038103440c924104001c1e030002c60b0340ea0052403801c4402600101d09213031010b070081d094a2109800c201151001d40c2c0d2400e02500030324080b0b00030b644054482042 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 8496994 1250 8495744 8495761
    0x90102011a03030904180b010806040519020a09020304110306190f050c0301030807050106050d030306081605031f0b06040611151005090402060d0c02010501050a060309050c0607050715020a0b 84
    0x200c00407180580603528100f0f8480401c001405100404240031545621000114100c030b0207150180080e100280400c0c18641490352502c40c416240c0707442030301420001001611019804d600725043c01401603100e40341c918084100f20780d009403868040c8104070401034901042d0b8020100040414030402c02200610242c20907100c0844103040d240d6004c100400018031110000d1040728091400003405d19118400104205074030b1b8010742c0002d0711900c0901c9601e206000f21440745000200c012003091034200800d80300c07070303a1540b00d030815903a03a05407001d00c95040d08031000d2050010801d590341c82e11914041c051800000c034500c81e03442070320325400d20380f420445154020141d2007040e0103024608800c10003107580c028400c81c0c02070700c2403002c0c2404100c0c50007007800e0340e040f0303400100e07442d81007600380004038245502110806052641c00400f19402045075080040d0a0314844e6907940c0c0d0303040151802da00c581c806188030b2150040d00b0318180e8041482903136a03100b0a02401180c441c1e617803 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 8498244 1250 8496994 8497031
    0x60403020c011409031c020304030501021305040509011e0b0312071202010606020a0317060114120a0506100c060513020613090b04020708090d02011107030c05030c0102031303030507151109010201 86
    0x140c0d02d4040c0d0100d40d240d031b80c285900405d000100c5a901c100ca2406480350395403030036a04240c00c107410204420b4410b20841c60940182d690010070f241c000c02c600e03c250240e8800714512068904142641c0759400744031030324280042401d040070141455500c96080c9050100074078152070003001546081000b00e0028808243e6103261f82c0c00d59100c0216005030028401c80c1c96000d8101070500c45401000312801c000c00025007543c03005400800311500d0000042070075241d00034100c500c070324003150951034407641100d40d12002c1900710000140030783d2402900a114850180c3c080d5010b5070200b1105400e00f40180da180c00c1c0c9000c0302050218154107010b0000360302606a0092920406124a514605210024144003401403401c5d544404140c20400d0405031075803c281c6241c2660340b414042030a04000c0c6030700e02c1c4020301c02585800d890305e120000007078482c04000c1c100140040c004061114a000e6600703d051502307810051050002c0d49021140c1c00b0403840c6002d9424181040d60744800040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 8499494 1250 8498244 8498257
    0x6170303041a04151a0a03030513090c0518030703051914030403030f0302130506040602151312120b090f040b0702060103081b0109060501030804050a08010209060403030503060f03060403020c0114 86
    0x80420311903c503244c64090326020f9210354582155038411030059031100e040800039030194440c2944c480b480307884090303007a6044e040091828106034060644513400f008880c150510741c1c6081c550b9110400000381424000e50002d00b0300c1c82100040041500981200c03014544160340018500358481400e42d00c038002c03480060045412003031149500780c000d070020402c80e5212042d90401c151540300080090300142c01c20300c016800f60098110f141240c050141d00810307280c0541c840344c42c480d52039034610f100c201d19002c01c000c4110b0740a46800580c4c0c008440700d0710001d00c1c01c5102e142c1941e440c05804421281524180348160102c0c8865002194243c144ca41000c04c85213043c0e21800244900116018185003544d40c0c4d03510400880c010307100d0070740a1403061007550f580d186402c00b0803100050395005100c02c0d0748100840d454541d0f409007110103c80c3d1501b4170369107a0b076031580000c4000229100503601400380008100030158041403040101c1000d0701d440154021062074209075000d0f29 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 8500744 1250 8499494 8499503
    0x12010c020c09040204090f0506070e01020c0a0501111207060902090a0c0c0219050a08010e010b01090605040509060103020f03070e0103110a0c02060d0621050c04020c0a0b040606170303041a04 84
    0x129401e52580c2094191070307920500240010802444075903400c940407a0b4940141e40c6504140140150b00358020748203080011309100404a880d44a40058183e050a1003042d0500503000303541e0352017034130901c000c2e103000041070007454071441c91b41002d00107400b98030012445100ca94001030f403038a03054880c00001a0141d41d903050700382316950900180115003101034804007543c560004003592803084800c050700c050b9001240740e902500b5920709689144003c079041c0b1500074130034042e5a5001c0180e8046034011188480685c17a20f0300168000d20484280b00e503800380004c204140141c2008040da02c1c41d01c20ba80400106881e01c00c1d106442c01703511440000104140d40c1000907142c0034018000c4130300d840f000060f00b96030300c04c60b011016041c0c00007040340219200403482842800d2040d10b003d0901a03506529004441c55925115402180010b080344407940c0072506014107035011901408920914014680c00d521240b0342d203803c21541128178001c2c0c5072480c0356400080801d5400340341d01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 8501994 1250 8500744 8500753
    0x309030c06060418150e0f0c04060501080412050f0409090605040b010605040f060302030417040608010602061015030e0f0d0c02090604090c1203052203020306160203030a0c020a02030106090b12010c02 88
    0xf0317984d14070000441c1d12048401c540c40e000c020400c0042800005055203c03034004001c4c80e008001031105940d1640c0c0040e06115500040001259004c205143d0a0005203049560340c500c800812000d40240d400c008110352a00ca61134003085010f0f80318501850003400307110f1040c0c0e81c0b850111000d114034000d032104002880000c1040c0780c003940249d504140301d8402c40c202801d14019103142a040396000e0700c00283c00400400525030140426500301c901003010f00022420640103090004c01124200201a0741e000038030680b140c02d00c50075010b0002c04003039035444103500c1030003040040e031401c0680c407941c1c0100100c1c48601d400d2240c43c0354154000070701c41307902e40380044081090a100390140c017480000c1114036000c0488001c8604050820b20018036641d0850060518120004142c100c90300321240c04c08258980005c1940d178007000b802004a8440e240a008905002541d034000f5059800e0500104590506810003588070b407049d40c0704441c03100310545550076201e81c020b070030015801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 8503244 1250 8501994 8502041
    0xa08060a0305120702040b0d0803040c080102070302030915160302060106020f010e060708040201050f030103050304060f08090c0f0301020c160303020c010914090604060302030d0305071220030a110309030c060604 93
    0xc0c04009081e40c680000c0000545480742d20118207054070b00030084a030828000b040000708015210848044c040de94001c604010107503a02075a6441509400ea10403000e1030200c111101c41d030780444402c0c0000725100d080c1d191070b0f0300c0c010755508020b01070100076014060600450f40014030407036a442e0421f8000305002d403030320902a41c1c010380c0a40181d040001c03c0125010305030701c8030001d5008600c200c00855440d8644400209840440f6030f6a40810a10382c043c841c0c00704c0000b81510b6001c2080b120140c0440213070000900a214501c50b126403402000215032040680540340c3c021a030084d0203661000b45004011180c486480c0030b00d0790040806101000300f828510900e5a00003c094000101c031926500040d00d07042c56890140000390b00d490805c0003055210f503500150500d030600511207001c08121150018411440c05900c1c00d401200140d88000690083d10890045000300d079900c0c00c10143c120f4403a40f010544546900c2144045400c904203031240030300000e0104d13100180200d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 8504494 1250 8503244 8503273
    0x807060c09050d030903110105030c07020103110d0e07031407180c02010f0e01090318060e041104050a06050d11030f0c07060b190e01080601050303030c0a02010915020a08060a0305 79
    0x1940010640401541400110b03894542560400243e0b02946815000601c6c0d45058818440c40d00c0c0e03080d040000c2403051201c1d10b4540e0055691250b42424081a02ca141c10080c25007409804d1126030358608140b0b0140580201240343c4040e07074014400c07000d8040201c21141e5460407588283e41183d04d0b88054807280c1682c640c030040c101c886510001c6009031074024220252008030070804066503480c46130750101070f04070748400080c984150f085000d0034580600948011158079a841c00b5a8581140003040d000400448015010007010391f02010348400e401449504001c10f103814140c80c0c41c2181540340c8010b003d0300d10900003e60301c41c1669072900074130005504a001c08503602d90302c64850500716501c19002030300c40149011807126444c80c2c00d41c500341c80c42c3c06034090955604104014001c03620040212039000c0d06044c140741e40c9400100080b40100182c901c0501000502882069212681e40060110298035510340325503481d60f004105001450380b00091450340812400e28106 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 8505744 1250 8504494 8504501
    0x30c01140405090c090102060615040902070305040b0304030305090f010509060106050c0f07060509040606051905070c0906030803040b0702060906041401021315090b040f1211031b0103050106020307080706 90
    0x140111900d14142a0b880340801e04024040c1c074400c03000c20b004248940656410400070303901040494014000c00b04004416206208034051103403000e40015805050500800c110f40c020080400c0300b07581c0b0310701800c005004101c25100c4c90031500800002100880b014090349018a0b030340009800035901e4075405650b6544003905990050141181c1040050b00600c4050010a0241c8542e5503031040d880030042101c0c40d40e0064000c2c8031083c0981d21a204650300d1005001e203a5051003036440c0e071681004e0006031200e9002c0105103082007408010000014043d5000d2441114199080c2e1100241a41c95003412035003481c0e01d5101c0c0c00040d021410962070007840484c404001854011003a4410001c4819508401103170045a440c480d5800d41c0540c0d040b00038000c1180d8182464104601580c0b8004144a000b41c60b4041404160a01003000d2230070490440007401c8404141305d00c0c07000c40100e0004079405021078504400080d44d0b500100440b481070b07901c01c07a224541001035454400a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 8506994 1250 8505744 8505767
    0x807050616050607020607140a0207090507050915071a0103240b030d0203031e07020a0609050106050402070b06041a03100905120c03030906060415050f0301110d0b0909010209030c01 80
    0x18140c00c004001e010682c1400b24901602083c0d02400b03107413600c940050301c3e4040702d0181130114442003169086c1c1d1b81c4c0c003240c2282503e0210f48045510345909c0d608070341500030b0010b9282d000e010620207040c00f1420000900003584599041d6103c10041c6e003142a03402800d1102030401145407080c90301602c1980c4004410400d1400000f46241501c00842d00d4080000d2250002d40d00000c248101c45460b0108c1510302401e0079444107451400110094603800800001804541c54985520811a0a40200c006000d026100b1500c5007468102443c0510040c0c665a000e00d18014110111003a80404101c0030400a4020810300e441c00341150010f0001c0402500e06020324104994246411070080c560180200700464590500074250350500304060001c0c1d1180f03240805010644407940340b00422210111903070000308001602003405044542c0c1005c01800300043c00c0091030085a200142c0d90506580029447d510558800c1c200d1103446049030b0b0603803115000103003542c41172005944 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 8508244 1250 8506994 8507017
    0xf0201050d11040801060302090c0c07030b0414011a010e04050105010503011205010b060301030b040c090b0f04020a050d0f06061b0206031506120403121407170601050c03040b120106080108070506 86
    0x20301c02d03250140e00d00d443d00150000200e0b6515110200190302d400b51106401125102036140313420000510156103441c00d200c000d0000c000c00000070240084829019035902c040c0b0020b000e19203a0175200400215181c44080c0410541c05005109051910429060300c030706840c1d061840e404c0c18598080618014000c07242e0b5074941455464076200d04000c0c3d402588202085030850805290540d0074915941020311308038940f002440d0f181d81d8070034081c0100841610700503501c543c0c00c107080f2245e124481601c20000d00b4400b00c0b14105100e0b43c0104221081d40d5502d1039071182088041c02c8050b10090080d510100a02c0490f02480d80e000031640e22180c010917484c50811102044884290100c80a50104108030108100405c0c240075022002080440b06001071070912000b0340714256458400c003601e5081400909180d0003213007125880c00f480c0301107940781d0340d41d80e49696055020411a041000c4200c0c000102140241a4039060b6a01000580100c40c141001d2000581101c03200701d4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 8509494 1250 8508244 8508251
    0x703020d030e0309030f01091707050705040c03140709050406081207060f02040503070303030b0a0b090904030c06111201080c010302040602070e06041805010902030c03030901090909021206090601080f03070f0201050d 95
    0x1035103517130b0411044890381003400002c074480c04681454054202c09a400c41002e80080104c03100040002c01c0010549100b16400140b0322344854044008050242c8141c1300031050005000006401010310401c9441c200c0701030044a07150000e90f91141200da0002d0104181403011100141c6160080034040c031003d880113090550f1500000c2c0303003090075482a03001c00d40da090780c40c00c641840c4040794043c0c4880d480d400c0c580000000800c02c1d070b28006101508124084100e6010410036401800000c41000a0540c85500101c40780d11410004c0c13250728a10302c20006041c00c2c1d54040d000707840868440d42c0107003180510b4170440021001d80200382a92041c1d440031030310030a860255040a029018000018641c04680306141c502403420202501c07940c81440a01082d03079100c01c070070b02900c0040001281100c014804100448000350050584d402528200204560300041640c101c4004204540c003200d500c0c00c8942c0c40e032282c802c000e0001e009100390303540035501501c000c240400e03c1d00f2000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 8510744 1250 8509494 8509507
    0xf0705070b03100806010605042304020406030209120106050916030608030f191706060a091d0601090b0301050603041101020c04090506061306080703060c0c0b0a060f0603020703020d030e03 83
    0x440c2019040d80124840d0384020041c4004282c6010707400c806440d182c0b00070b20301c5504114003c1d003203020300c0c0f22300d0199240c104c131800b0b05800700c2c01c241011041c02030015502d507070321810041c0194018100160140904003188202c201050052204490026102c01c0141e10b61800c172a60b9030754007426107814142c42c1c550016440b9030400007071480146a098041e150300c0003035104114035a1010a030010812035030000c40e243d1070480c42d100d802003421542541d079240445c9c0180d48061459100454100407016003540100300410294868603090ba40c0ca81c2d01d5859100904281c0002c0c000d02c1e0b0004010301c00280040c20406400b11820014011034000007082c40c0014152004007004a035a03810030400e1020505141d0300508240c0c244540230712038142000881c030f80c0e41c2c0d2140b001410f01c1e13450f54484210b1a0103101c1642c8400c2c0c104088400300d03d090302d00f5030094070302c0b07104070118000726140010300681320b4425100703082c1e41a4080c1081d01440c81e02140034041e2500351095900040064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 8511994 1250 8510744 8510753
    0x60c02030f0604050a06050108010218011206030203031c140103110105030601090509070f020105070311091c0803040b06010807110307021002030d020d050f060a0302030307030305070504050d050124050a0b0f07 92
    0x281031140b48503200820140005d85804015101706138007924079a801806003112120314515441f003840400c2c070340800c0d2259401c0307820010f040f0075030001c2e40502000516003d4241c11040d07491b2040d01007072041c0811103907050b084400d200244809014900078400c444c0d52513100c1c100540e08000141343c034006164a0300c0000b07032000802d803580c20109203011081240542c0a004071507000c400344c00e0070031107800b1402c20f00003140715661411b8481d0a86141c05003041c1d08444d6901d154903003106a8607102d1506282c0a800c0a1040c2d52443c08154100c0002d00103e1140b20014554003143e005142420065800d0120040241c604001503000610030541810751038806011a900352280101d02ea08107032084441c2d2807005020305002e40316883c1b040c00540c800200300caa03415410b20b00000c06648400d411103032402103400c9254088001d600000600605406c0858a0b000d800028840364621401d16a1420075030b01c102c60f001004842c04000c0011070310003500306010524038007031815046659 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 8513244 1250 8511994 8512003
    0x1090f110a020d030b0102010c02030409110412050f01051f0504050403090306020310030308060a080304170a02030d0f0305060108042301090501050a0e06070c0312021809040303061406030f01060c02030f 89
    0x7210300141d00180804401d564140a0750044030020700080090071440c480080d00d034421800356030110364864203c58038540103042124002c2140d40b86ca1402c0b802c0d546031040d15040c0c42d03c204c660940c01c00d07001c60748101d4129111100e40100c116400e00301c1c0e181070240b1003e004000c00a50a220440c0b8000021030301c140000c51050005d004440c040a04500d40a4049040a41658011380c81d4090074010301c2d00001c120f400390344903800307800e21858901500600d80026640d009401d40215415001c1c0d05410a000c142c01c0c01440d101031005660b003400449148030207c030041c03e07003000f152460300b03280d25501c1000b08a00150300007040355a0251112030a50300c003641c0c10007450b5505c4440201d450020710400b9080903081c03401840625036510020072014000c2c034544e1410354005507580c102016207070460140c84024040601c28609030501400414480c419914140c0c003400420a03540340100071a480380212400d01d081c2d903400d060701101d03a185000e82c03c03070f0140314900c24908402002c10 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 8514494 1250 8513244 8513257
    0x90301060608010503160510080405210a030501060c05070302060a02011d0c0406080a03050301090506010e030f010b0a080102071a1305030f0702100908060708040201050f040e01140f01050301090f11 87
    0x310b0340012549080203062078441611103400281610300c4050040356140a02d0440d044018035090805803160b041c000d00f401c03035101e14040340070030b811840302c0241d44440250030b080c681e9030ac0411240c1c0e078608055a404500c0030340100a80c001c00018001031a0801c05802040d503c0e01c00000c0c410700f40e916000c0c9120074030744106407070341c4490b001c0030035071a0074080e04002d4604180a050003805070790b40a040d80c001070161600e52030b1038400054040c0d2107065807201d100760060444103100e1182414500034002c21002300d0040020f0000421250014001c4519a84d44030303a200703410001d0000303001c0c11000040c200300010030203010500081070042016014040c0140040c1e5a01d0846104000d4a5400e00000d03d05004412200f0800c1407808141c05501c070f121810144d0b05a030342e170310040780d03d84584007100d60360300c030080b902041d510009801541a103142c3c039145800c0b10b5400040000304940c800c80703e030004104000500a0005a4102c0b0000d000301d200c0100701e032400b414050301aa007061 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 8515744 1250 8514494 8514497
    0x703111606050c010506010504030b010902030c120a0b04140c07150603020414070201060614040b1803060702150939040906050a0513050d030213031205030420090115050903010606 79
    0x4901c0656143e03081c465641c00c0803090030039500d02882c503035400a51100501c10405d9456020001a004078040c0044880c1100e44910b8981a8030b07000ca001e0000b0039101240d207000e94540564001c82811814400703008400340d0b412241020f031541ea96004502c0d140c02c20100c800c0d2142ca0005c0140c80e079016101d080f08a213044100700c3d00d0440402421201141d001e181001292a0710424004030003003220f003603545018046690300119601d1a00b800620a103c0d9010320409081041d42a07010ad00710b03c1c034040d280e42115403500c52081c0c80380d468a54581462481001010100420b2001d111581881d203200c12900c82c0901c2e03083c0010b04a83c1d04140a40d8600e440c1c5003001070024840c401c1590140f0200f00c0d040c001728031a22400c0e51a000741c104882032590020700c06050846c40329000005560021840a0002d0402070040c4950800e4400301c071784608083ca101c10320500c0c84050505034001620700f4009a02c2e210301111441e2111201c030051007000c1244d0080b948080c0142c5010348140d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 8516994 1250 8515744 8515747
    0x103120f030c0e0607030203070c08030c0f01020f03150102070905070806010e0303070b0103030513050616030806030d0c0b13080a020703230309040b0f030d0806040b0108010605070311160605 84
    0x10540240c040e88040c5090400c240c5401890182c603a0407850b18260428256016078139010146401d0307145106055020341802011040017036800000030040031104034050680e145606c4228180c2d09030b000340000d54290510900004143c000e07003100710348400c0c4051044814031581c590a0204440090f101000011001c40400c4a42e50f04841e603588400c4040c1c0c011807401416460303054032580180401020801c0010300103440c1240240f9117005014010200c035501d500d055440c0780c104210f190210013054168000a1303640ca00821480c3c0c00709039503112204803800c190340305040040d0082490041000392050503004c146588040c09003015160001e1045e1400c50170407800b440c90b207a003c0708070b020510300400760b00d600200030b46140e01419507021811410040005641804020742c0700e405110341134411000e16070040200d406640217403400c1029000503401114090310034010300003c5a410480840007900c20286880e105d00710b0070603141e45001102e102040b1000c1e691018000500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 8518244 1250 8516994 8517023
    0x60306041407080f060f030d1206090606080105030601050904170906070807141204060f051c050f07030605030105040305030c090109050406080703020301150509061504080a0f05010b030d05031303030b06030103 92
    0x1d010b40c2020f000c81b9600d0103142c0d5a40081c1c1d49400d43c0b600c070000c102c0f4580150034031080c9a04090082e1907109000c0c00000e4035800018080c1000b4441da9100e403040d4000011141881550640a9900080c0d100c5104162074151640c07940310704005c58102c0c104122140c0403451010190414520500040c01e5620840c00050300d40b0035601441c140c0c020080104201c8030750004240e1104450781c0c140b441d15400b019041c14030f128421000101c0083c00c0504022070f2422401203e0300c600007544081152980320402d01d8201ca60880e8024081402040400c400922a030050115a101454120a843c0d19200840d09a40f402e0b440441254403000c000d00841c07a00703000341032400e0307070341c9400a14113441e150001c3c94840c0302500b5140100143c010180c01042d44000b1100031b0180c240895080700e00c6450440c540482403031050380c141d4a4001490b205140100b000080c2d114107990b0982107490b4070001190301e191302a0110181540c0d2511611140c032404c010b1402103010707500c2000d10700c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 8519494 1250 8518244 8518261
    0xd020a03030f110f070809091e060102011e090302030d11090a08030a08060120100b040e01051005010806030f010c09031203140703050c04030203070e07030b03070303020d050d0b06030405010f0606050f0906030604140708 96
    0x1903000d002cac1c07815a410480c420030301e51846a01d546003a1560740c00850392800d503080580c2180b02e0942080200e80c00d00754a03e405c641c0e400e00400000710305440c0504625074500708651280134a9443e140000c80910200b4030a6105080300448501c199010f03038001043c00c08071500c0c000c0000310200e1510f45401410b100351506104094100a1843c000c0c006c624080c5200103220007280101410321000c03001051a07610704000b4001a0704c001c100810415030031401c00381c800c6405210448004080000b0300010301c3c40390059095031403903403110202d9a102c03010241c2c06080300419031440c4240501c03000025070f030200440d80080602200765211420285001025aa00c0d10202c0380240e00903e4100300090740080c140044c4040c901c2e0141c4c8601039101484040d0400c4244030f076014401100f40410f006040d84a001115140e24003003010315a0307a01c0039039080c0602403003840742c403c05010803074031400c00500455101000038000140c901140800d40d00346a01500c401c00040c1c0f27803108002c0e049 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 8520744 1250 8519494 8519551
    0x5100605010903020f0d030c0515160306030b160201020904060f030b01090207020a0e1905090309100206061309060209030604030c0b0601050906070305070c03050d020a03030f110f07080909 83
    0x100350070300e040c2c480e2078255000304110207070300c10780b0300d0059503500e0101c0140751045400704011540f02c4142d4210300801c10051040300c0095590b00900c400b00c030344c0341c52941c0c081d1007944100c0f9400b107000340081c4c0d55014500c400e00c0c540035020084d035408111207060b41d6071324801c0c00e0180081016405a0340e04604103d014214141c002c0012a4070400281c000340c0d4a201a0404403200c40d2011415569900c94178001188203ca1500784031b4142410310288603c0440a01080802510a010040d6400e07004a070f03607510556286800548c1c00b10981c03840340050b0401c50704940a010054030f07000c0c650004c80d1801d0320484094000400d60303111a1b0070860f10010b802e40103102440e1450410708044001141c500c96840700a040c080001080020007050013001001150001c09550320194030007806500d42520041c1200043c2c50500312094a0707402d44504d13100550781803111414450444a000c801e039020071002d4030941c009100341d0400d035803031400c014420803040380e510080352100390001140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 8521994 1250 8520744 8520749
    0x21040906051207051012020d050105030c010309020a1202061309060305070605031e18010c050307031808030c070c0803030103050c090f04020904060b041404050c030d0207080607120b0409051006 85
    0xa18102c1101d07190400000394034819503108031596071410f4240641074400080c0400711450590012070f4080c1000f00503440079049840c182e00380c0321507030180c40044003220200f000003984a04420b0050282c280441840c800c850b1000c3c00e21403401001d03890054104c0302c15071080c490302d40c58142c240100103082c80000000c1c01242001d80c2182041850300c80c007010998005c08040188200040c040740c0c0d504460707905407402074000c1000c1e8400900c0180b4580c003c941003030119042503810004103110441c16440c840e0010851400c5483d190b0150126031300401c0c0a45040141400108000c00207200540c001c0d8071840050035440034850610100e46030040401100c20004010080980c68400c41164000d51001c80000c00261100000d0002e0040ba84081d00e80c0c2081004c0004000e000111405046011812296091801b040480e50f40040e40a81c52840e00300e00301140c800703400b07030b2f03204503000000c0320000c500141510042004c45181880c180c0d25907000c2c05a11961403040d1060401 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 8523244 1250 8521994 8521999
    0xa0305010c0e100206130c0302040207060504110307060504050f04060f171b030606010e03010e0304090501030b01080a12030c020a02060a0206100503010203130b1009050f07020606010512010501030b032104090605 93
    0x8010040f4000039403140300042900354001d460581190400039024040700c05140e008004540328106401c000d8010f20b411202101c0099050b92888046c2ca00001c820089502d03503036500e4941800e22007405415000c20000b2900a9203a0b140843e004000b00c52100c0030b000c2e404080c50903446500d0181380b400074003410088517001c1c2d280403030b00c1644006c41e00c243c4c00b00b02800c0c02c0c80b45500c100c0100f401410541d003020fa0301d000219000c1091495604407a0490b4000c44c030920300c82c1d0b2210802a11800b8103c001440d010120f2404900c0c0c80c06500856032a4805005032038540300103402064282d40729600b03030070043e0001010080d4007080030400305c0152206070021405d5142a071060030301000300c91009031030443d07100001a910b00644440384060715840c1000e102d9401c00702d0004114100a54a0f00098013480340054620351041098a40035400d001c01d20540d0703480e0400640040108484054042c02010092262103d107403545004010b02d40702141d645924180100c0203d0311960002803 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 8524494 1250 8523244 8523259
    0x2040501170702101109030f03030603030703110307290a090b01060c11030715090902120a0e0307020d0506010603060509010803030106030203071e020102040510030b09040803150a0305010c0e 84
    0x28a07603000858800d01c80424912a100d40c540b108243d29000f81000882001c0d41000004594103003e0405844131401c1035044038404525101119143d02080310b0080d0550310920001000c6841000c6012014004806807440c0502c40d4031440e0340b41e4101014030915001c1d9440c079211100c1d44140c4070340d0200c1030210401c0f8001c40c2e40e0340e40b01841010720820007003000c14440c1c0e00170311104440034601d0b074400408507890a540c40301c40c05014150400c1001c00700c1c40e00300e00007641d0b41807030086401e580400d071108503140d507620050b0f600401c1c0256810460384000d1092000580b58003174401d0030180201e00525142d85414002415581c213078002c917000710b4010004010440c000425a13054075a1824056241d0380c416100b00d60030151500c03691007601e0005040062140c042d4001c01c1900c405840b0040d4068807281f059042d035030104d0485402181c403034002004a1242c00296411070034050481808404060019007400ea898000380c4450350f580c480900f00d2030700f002580c16920b00954124 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 8525744 1250 8524494 8524499
    0x1050601080103060203060a210203070b120a020a090e0a050f0a0b130e010b060706050f060405060102150c09060c030301080601090b0604060c0f020603010b12010501020304050f06070204090203060f040302100204 93
    0x1c0554106110003814682c0100115078982d5a0815001c00fa0980072220032500301500c0c55000d0302c6d802c100c010fa0003400b45c2c4402196900844044406201d00b0780203050203603e588032440000d621001031074080001407040450306e4100c100035507004020041001c501800c00a00c50ba056407405030014a00e2450011000d072652113030220541320000c46400000d542031501101c0c1d002d4841c4004079640540d000400900300021584103034002c0d089214415426540d24091008403003060350041e001d6807020320810000940815101d91220150600e98184090207000c6083d0340c1010010a103da00040010b0004d004100b107801e00410094070148508800d84010a80520039402608100285080c10900f4002424402000c00d64041d0203246e45e580d548071445c41d941c00c10501440700c900310100000c0c0941c4000305440c1503450050254016949a80400034554406039040340c000b0b8460686c040569828014140700e0704406150f6a618a09861b0080c10418070003c0090b0852050105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 8526994 1250 8525744 8525747
    0x3030610030b04060503060f04210801030210020705090a140c030c0403020904030e1801050f030708072601020a020102120a06030b04080a03020d060312020c0301020424050408010608010b09060301050601 89
    0x3a1540e5814140000c0e180602400304000e4001a00910b405200e88000c0c424216056050b0500c190301640c08881c92060f000c003400d151401e10012030700003032036010040c4050726140b40b00015001c2030340111182c0d00e5131000810001035007218036103205a0307200600043e00c420481010350040905c00414514038000b050074906005a00020340a50141c600007000c041c060480903030704000041c8600d05116600c2501d0404500902400c0e0141c01600d8a400240c00d001030a201511724410190540343d04010744800c801c120603020751010b0444082c506c00445d420b100800c0311b2030f415800503076205040700c20b041c0c0f8110041c0034550071520700003040000c580402c50141d0002c0d40300c580682e40d00d9441c10110003900580405070081803410748008100140e580101e02d08280507000d07142d801c1c5035501094200d005602c00c805c00c101d01442d54126100041008401c2d012150a0440c20552102546030840d10903403c60b144580d5110555107440c078001c6165548008110024040d61504100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 8528244 1250 8526994 8527009
    0xe0d02160e0c070f020d050106090f0c0c030e040f140c0304060e03070302030901050d02070b15040509010908040302041d0708070603050109060302060702040b040f0f0603060509030301080a08090613060513050102030306 96
    0x600084c40c41c0c2180300840d50f501c1602d04607150840700a00107203440388540002000c2c2032640c000f2443c40c00c0241c00541d0b000d400403032100e0744c160f10b0380030034100c5600901003d8500442c41d00001c43d0348015544400810284460180a181890903260720b41071800c102103403183c0040724000c0d072080c0030f02c2c4000382c2e00008030740c2c06000c00c0c03a181d611010360304213280283c0110880202072510b49820400c851030488515600d038901168240117039102c03580560b00b00d0348690b001030038582c2c040000b4005400c041d0880041568000c200301501c030b003449004e0342808030f5070b0403c02c10344d08069400c20ad029071600606004d055101c200300070a81c41d40d0b00090712480740c0c0c44000e0040341c588030641803d0b41e036a88442c1c44ca82ea0607500b1300c007180704030070b40c003008000901003242d0140c40c000100e140d090f00041507038144c0345600d00400301007156466017500c642100c0c1e200c0358400002c100740f03a41a080a0024001070030151502911259107c6040010095942003203045500901c104201d594070200c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 8529494 1250 8528244 8528257
    0x30109030305152b110d0503070506160903060b0f040c0c110f060301140103091403041d0405060103030c170403210c030206070c0c0510020303100f03080316030e0d02160e0c 76
    0x60148403035000901e45a1283c44071050300d9944250086d00720002d1080c048003d01103180f140d4140c0d8160745d44c038420f000c2d000c0d400082940c00507009007002e000080705035008050341d20004020f6249a007850740054250348036889050000344e01c0584540403c9440481d5484228003100c0701000349034040003142c400d01052165489900880301c440c442a40280e102c801d50300e401c0401d01c250207501010741d039500d612a200d6958000c1c04d00384000c40080b010340300309018561200c050b00250340382d030b01c2c1200c1131004010141d601da040201400c505840d018002c2c0011031140e4002012171506000000e00c800004410b030b13040c801c844008100003035012803465440401c9080c999041112818240d05440440e0011900400002c1070104611b4001024512401060100035001030b01d4803280040d00b80c140c03000400556050002c19000c4c500c8006540001055250000d10a25035005c80c2c2e29260038414600056000701c039040040785110100a0040e01d4452072010047c203181c0400a228482e50 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 8530744 1250 8529494 8529559
    0x3010e060d11031c090b030c0d02030424050709090c0816090305060406020405032803030207021206070f02011505090402150705030c0105010f05040501150e03070503010903030515 79
    0x700711001000441c10641140c00005421519070600070885400f1030003202c5040710102d211401e00003810700c6040d085920030010801c0090501880341e40f02e034041c2d000a0001c0300c0000c3d034010400c02001d9070013207000600005000100d00c5042c00007000d4981c4c455500401d0b6418200021060400e41018080382c012b005103511140c50070504004942020090b00000c00c9405400284030501103140c000d0410359904030155524a140407240c12500306036880344134440d20b40da008010129002e5405014158000b501c0d42034040c0b00098014240101103c1c42004200e0021110500b540d0900c07954045025a00c0708940702e5050900144411100410091003161004a00c1c0c00c612900015510502d0b48802180e07162846121841c0c0a8a024069000c464421600000d00f92800d4005c2038103d84000780d024004148048040764013540f42c042c1140c040c840d1503000202d503102440b8014105020740c1c1c0004d010300340000b030080c030001c0c19030302240304031003103025800c5145a081b24880d5a0044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 8531994 1250 8530744 8530759
    0x31c140624070506040b010f08060a11091003020703020c06040b04180905010c090303020609070b090405060a0308040b040501030e03030103030203041206060e0112060e010623060708031510030203010e06 89
    0x22032141d5203074401c0c8038222140003034007248802c00c004000a106000310700c0b0b2030400440d80e0b2103007000301c07040c0c000b4031460003940d00c04000328503041c1e150b0b44440c0f58a039803110000c0c640000d20003c02d030640400032050300000d40c001615000d0590510651400c603500300c5a40d4900343c5401c4000ca080d000c0d50050f28030008444041c0500084160300000e903c0e41e02600a01000407001c0014110810301c1c4410350140c0544000901035140100300d10068400c0490101e042c66514000c0c40f004140043c6565041070b84880d012001c0b490784400f070402403000700c040c1c030fa0711420b020006042d40c00005002c2440d80c002c0c0014400a0b4000c000c4d50f0540303a107100c3d80300400d5014148103019000c1e0b030b400344a00400c80d030000701d411106641108030860103460f05000961442581c03c1c01c0700c0740380c456914020702240402142207034000c00301420b0380c0e004001904205d01500c0345c281d503038003e440c22440e0300342c0710f00205914203000b141c42021441e10b0034110300715890683c1180d2401e400400d4644101c91 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 8533244 1250 8531994 8532019
    0x7050c010e0c060f0f0d0e070e01080a03090303031a040905010e010c02010603021c08040b0403060b010f0e0a0b03130b010b032208040302010804150e06040209010504060501050702040f0605060a02031c1406 90
    0x1050020b441b90103038220710a1100e100080ca880351030b005d250049500c50400c00c4008540701000103076008541e98190f0f1010303401440e640b0210000c14007029501c0000171a04401026552a401100070b00390280c00005044400c55070200d0071200540103407825a4140a02000540e4540d103203903621801184107816450750516101d1401c1c801d80e00510000a004103000c010b0103680c0e4004400c0da002138841d0174201d610030304155070900444c0111039104080ca44244048081d117006517820148003d802c1c08202038650b81c1c0a00d68100360400c40c0100d10120401c9480c400250000302010b030500c01c0d1403a041915210400b0500c181e00000e0f040c0200103000c50100500c4c04907142086400140c00c00c40035002c25141911a4825a401d0b44076040c5000040785618003440781038122a4140c54062070422a642400f016150f80c1e017207500300c1c682d5008001040c4d00d400c80144400d41496000d56503511402150fa02480c2c480380d021410b5500d840c400b02c44546104040607000b800c129080500340c203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 8534494 1250 8533244 8533267
    0x109030b060a08030a0201060302040c050306030303060d0312091103070501090605030c03060a0b030906040b010e090a0b040204090204060f06020d0201050105100c02030c0a09150503030307021c0c020907050c010e0c060f 96
    0x46442c3c1c84840c00c2e20000501040a0b6410351045003aa44201e034140940c0402030400ca406000584000342e040d041000402c0300f41c0740c103184107110144242040c0c0204500440c0600883d510f01c50709542e002c1c2e9000050b0907a1400780322980140c54242001b8501030308107200103041d800000c2840304108000408500c0c10340c0ca004440004080d840056903991810903401ba8489a068600300d9500402e0070010031860601d04140340306a0b40070000700100d00b400c0d256030354610406001a07170400c3d40c03103d60a0251b225400b801e8098440c141c681180c40d4940500240342a010307201020447e4903003401445155602030320b85682400318901001149603900020b41084080b184055026030600320001c1d81c9032032034004560340c01c10308102e01120f0313680c1c006241e16031104650701001038100c5030741c221140200080e030409007100d901e844004500568042001e03444107903003840100b0300101e0182c80030142401880c54034a03000b0013802c0c901407820302244c07441c0a550121500c450f0049600280306 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 8535744 1250 8534494 8534509
    0x150b21070c02060301090606020618030a0e04060305120702100201090515060105190905030f06010f0b130b0301030b0f011202030c01050a03020d0906061d010f090c0504090c030606030e0a020109030b06 88
    0x7a00200400c4c0e80b541c0da010010001d100603c1010701501035040090030851100d40040f0000704114091450158214411502c15000503201c0760301076030f1150040040f0300300b08080b141c5d220080c40703044e503102030a00400003040b6a5040820842e030401100100280000c20b03500501c41d4059043c1000c3e85814006907002d010b4401c0624504400c0e0300b494181540c0201c4440c21a841034090b110240c07012514251100380900860041c081c050320104109480742c0c000700303030009065410140385629031580000d0f035030003a4020785213041c4d1001440303010401120b0290040c04503030318240c0108130310b0b0301094581c4503625a42e41804808190860251f019404a039010000c3c058100049001880c18030024655801010a26929451401610a128803640b03050741c001c004071561091a06518002500b000318024080100174800020340c1c420074042c0d28804071040d180410903d081c64001001c0352501c41958001e0780c010b80c820350240c2d0300b10b0903c0d002d494106020492581d14040416400d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 8536994 1250 8535744 8535767
    0x5070c02031014090a0b0f0c0705030c070501030501050d12031a030114090111030601080c090604090203040b0412020102090d0209090708190b060d030f0804030e090109150b2107 78
    0x1800b034900348030071503034107644402c412442d01400d040040c0c50340b41006541e40314004009028100007404507151602000e0059070040c1c801421602d48565569240d00303503001201c0c2c4c881164403102d001d020759030700b5000f050301401c3d0544140703225048170349031140c04005002004040c541e641007108140007000100c140305181c0940244084080e1800030921400203d96040c0c240d40303002c000222420000c0c00f140d010b07540594804501d91a42e070340500301d544c84103240544c40141008001601d4085001440c8a035010301540300c030340e1410b03050585d595146c84121008591040202510a07a0745203016030050b50155105600c554a80310300d0352810035260088030262045d4040c0c5500380461a4420800c984507103001c5103103440d5441400301d8074642510043c04942d00650007070000384500110b0b60312601038508050100d0040e000724040d01000e0300511891904c803080155a03066243c0044010301000c0410b528001402c25840c84101c0750b0911300103007038940320100b80d4003440b0304400b1f40e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 8538244 1250 8536994 8536999
    0x1206030210020f1603120f0201090b0711010b010c050613080913150608100e0703181401060503030f0f0a02030c01020a030c0e030307120e01090801020c0304031a04051005070c02 78
    0x441c403001c0e001035664610301000e10228841e101d1405050110650142d04917640300c070f80d0700c00324a60140c041e1083d0320304e003111000710b42da9410644045a20320048034011000d9440e40e8107181710510246081d102c0c1d80030303107a041c402c5000690001070707400038183da441400d038821010035038014507080300c0354802c0c1c241140d40420303500102e141c2c605281d802154994000511031741308503640c95043e10002800c40300451007d00d205010021010b502d10015488111858001124031100c6441c1d8074071080b4003803c0e18030030a240900f403400350b0244038007406041e08500960900c507580203041100d1040348085013140d0004a807912144e4001c1041d26408241100255240c0e044540c005004202140d04580080c180f8120103c19090100480713003080d40100b1403544034030031007005030344408050804a0400c841c41c10006001c0d14203101030b0040c8510071018640d07403491400c0c42c03c408042d049000a01e0325908041c0000140c0c00260b030704031000030301c202003107980e908a415180b00560010194 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 8539494 1250 8538244 8538259
    0x140c0307050f120f060a06020a0609030c060c0207170708030304080d0e030a030203060312030601050d05150a08010603120206010617040503040302060403080a020106061b02091504020c07090c03020a08060112060302 94
    0x4040c3c60385000450720801d83c81051800c55a103601c10420345c0f12481c883c00c0050f07000206003001003a95604040809030283c03e2104180d152682d03000225950b10140c40b005800c0090240140240030034079400c45003484005002c4c60342400784103034a03440094002091510001510304962071107070881c1c10103440c5103003529140c0760607500240183d0320443d0380074800d009000106403007088187c00c0c1d0340240c006941d050308101011180400801c0007030403400300c200740400c008540e40d5800c1481b002a150440010038000d20794174003c031180b00304a110005540101c001403115507440001c044140c4000381c08062682c503182000c50a61155030006034000e0302c00103000c03080c450740500402856100781c0c020012030b070380d40d503003101d600410710700c1c500809078510101005072400c038580f50307041075074000040c00f8007051000081c101c1c1d02181c02400990407000040002048501c00d5036140b244508056140c01c1e25103a009040080081660341800b140c8070641c2c1c00b0550662000d0050741c1d0150815 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 8540744 1250 8539494 8539507
    0x1060803030103050c031605041802030607020307020102010b090f0f0403030e0304030311061303050414060c010c0201060501020f0307030801030312150303020106150908030d050c1c06030213140c0307050f 90
    0x1500c0c0d5009020642e510322402c03403200c215040018108100c004c40c3c0c0b1840344042d0a050800015080d0b09200c914110446201c102c09030b1340922441c0d010303002c585c00540ea40e42d028170001e801d48130074500031885100a62300b005041c00c100011503501404030005c0e507207560380703524003980104078078007a8a48030300c4040703404410981c22840070045000084100d072001d41c0ca03400c807003200c444801310040000d1801d10041040072003403910b00c1d5148100034034550a100e4015085400c5910000b00c041c0141c0d12511b00304401d503010301c2207242c1500d209020714580019030700d01611400041c400102000b5104911408425103075000c100c0080c40c0c1116103151555a04009019180c0381c00355846445115014003038081c020030500c42106d1454024506210041e5070000040600414422408504024900d1b0845040d10500048120301c0000240281107006000300501d0682031301010038503054400410101c41508141c3c0944680306442d80c0e651082c0088489016081380000f40d5038000c103d8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 8541994 1250 8540744 8540759
    0x21e010507170304060608011a041d24010608040308062e11010f020403020a0320060408030403030e060306060d0908090a03050705090a110706090602040506030f04060e010b0109050f040e0106 84
    0x2140130328092041441041d4540c0115400c071485460740c1c0d80e03d003108162000d12800d00b41c0002c1404c000410340c1e40c8644450209084c01c0c00d85060502c441202100602070071503408001c421301502c103920b8041d166103800c0c2d40c06054441d002e8151403082500c0b490041c91030107906082449c40420241400030a90400b201515004162100d86c1ea503500740044042d00c6d0045109681c201c03a0010615a540351658481080f0240100c462208148402c195900c1d01d403140c000900c01041c00c40d00440c1d03641d04d03600340102041020040203104c1e40080092100c181d58000a41d800b81040c4080010002003a01d0803000c50301c180110755410014194001003440b01c0461310501f16201a5071000c0e16a41e02a100c01c219501300032000c0350707004180030740d4020075460b81c0b00c0c18440e44108c00051500761550700081141d041282c60428420402c000c00040011070f000b040b40c1060580c000b80107503001c1500280c511601406000d01840b001001603a0580d10340d0016108040080c0c001c010554a6000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 8543244 1250 8541994 8541997
    0x3040f060302190807050702010503090705030303011e050a030f0818030d0f031103010b12180a06050901140402060301050d02040902040c0305011502030309060f090a05150613050103021e01050717 86
    0x4810912000302c00c05800d03401340c0402c070311400071a0f03502898203240340d00540c0c16810182c02d040403480f8000380807401c0c2d103080005502900384c200302d07001442c6030950090034800090300540e000750000c040400018100c84d480b207200c95844408591918066004c025039500b0310080c40740e152040350700e0000d41540100103120109800d680502502ca43c0064401c00c920007841049518107003004a24400e0401054540d0420a52070386d80362034001c241800c6103031550b10b520549880c7d544000380325824400344034070183d9050024550003149801d4000684500052140c10700508400002408540d52980701020061380104200031010101c50700800405e400d001300032004894000c2e1030b50303240c00082502c4c82050140010600750792500b50510440300060300614442c40380c210288005541030020505032503101d681c1e5029450b00c50304001a010800c884404098603080c01440943c4620b90b11a01e00120340d04400301c40744070000101c50b24403844c040036226400318488550410320380d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 8544494 1250 8543244 8543257
    0x60c1505010611011103010b0708030402150406050307110f0c010e0301020d051503010605060f0301060c0312090b0a0b040204060206060d0c030c0602010c03050c0412030804081b01050103050f0705010c0803060303040f060302 98
    0xf00070846001d0000c0b60b1000c2c3e100030f00030340c0003400381800060005244003000310303070081c4003902c40c4284103a54905c003400303a00300e50031801c00310b1008020060034a40c003030002040e060b01c8000030306000d41141481503c900540d8100c0e410000303000550030464409404031007401d402d43c00c0421192a04902281052803407030030a62203075003451800241c524090302511440840d0385400c603d980d2805500f40c0710031203020b20072000e0025400410700030b1506482030a14190141007504c03c0e510b881e043c603004840c002d852440c41a407040c007040c0f0100b9070005846a008000b079640b404003444d41d050038149a01d203a0300050140c4072106001c00c4c00c035410b40020100c0401c544007446240c4446000d00d546010342c0c064000e2002e0710701070b080f020134400d070703034079504640129041840c25041e8000d100c40c0440c0c588511640340e460314010400c0260400030340c01014070141c0980406410000000c09550086401800d5a8408404075005580900441d8001d2100c00e803a0300105540302c5001c0c01030741010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 8545744 1250 8544494 8544527
    0x120010204080d0e0f04020901120504030c150f060f0605040306020f0f0f0a02010501090504020f1011030c010608070902070b0115050c01092f03060112030c0b090c130b0a060c15050106 81
    0x195161105c6041078002d82d0a0b03918161114071040408030071901c001c0500402c10713001c1203200d00e0144041030051440003031510452034041510920420103400f5540e250348032040c0400102810480305502809440c107880e4820400740c2e403004001da4003112400380c40303003642080500151400d1410382c101c00400ca0032080f90024000c0c0d80c1e172020a102200c03c01c55001e504101410520031040c5443c0c1c4456a00b0082418540e079490f008040303840c55038002400c4400669034444041c081d5000c2000410000c2003203c10130f41c41e01129940e180c1982030f040c49040701c081208825580c0240c061000e46925844d804001c001032015810700300601442001c0c80f0041c3c4109680c5122001034130711520424040103001010345904c0c001013a401c00c0004201902041400f00090700024122040301e401000008001c024100e54101040741c1c424096030f0a50602c2d01c0c06901032280e17202e8645003000c440c00e034105422005039171b003032000343d00c040311300c4480c0b54519100001c00c400360400e288000d60001e0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 8546994 1250 8545744 8545759
    0x816020f18010f0f05030307020108061c060c020c0906030d0e01020a050102070302062202010807050a05040801020301030503090301230c07030903080d0f1503020105071112030c0d030b010e0120010204080d0e 91
    0x5131884140149050701400d0303010340040100c1d50155010342042504080080d148400070480d00035684603100420b4000c94500d601c820007248215410800c2d14100e401c21120b8026505102000a82d01ca1110440300103200841c3d0300510305030300a020b50018150000001e565071204d600c0d00940320f001c11100d03282d601e114146259660821010000c21081c0c1c1038682210303e8403003132020384e0039410661000e01000001c110101e5520402e001031030003148a0303001140c60310502c0040600b514168108420101c1200700365a040304440d03600d498001400c0c1c1041c3c0e55880c00390a0482302e0031602d40000e45000c40c001443d90441d80564803e401284641c08200102500c10303003007042d1548180300203400180c040c080762000c1090703007e00e1050ba44004100d2940e04524000850540d0003000008060f500107044840b02290035010302d100c1d02c0402d18040a080074100006400c6034008841c6c209050303005441e03602524001d50448000d800e150044500200c01510300900d225829580240160031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 8548244 1250 8546994 8546999
    0x403020d0503040b04060506040b04060906080c0f030a1101030b040203010608040309050604152d02030706050f041a0901060503010e0d09080d0804121809050405060709030816020f18010f 82
    0x1c51829a40215031051450303080f40c40c1c6403154006041c025000c954416a41c0710184030990700c40c41100014100c0c0700c1e000c07501d180360a20050426040790429070040c041980710a220b5600860b40645d069800f007040750903030000500480081401421864000c7d00c004004100c058220000c548500c6c440d03541e21410f01d444509020640c0982e00c01d0034590a05211481d140d00d0180e4a1000340c032415a56200c59204081e8004042840b03003245c80000d03800c00a215802e01501d0301419500c81c0d01848071441a0070955101e202e8401243c900641100300c0102041c081e40080d0802c200130300d8010001d02c10701c50702d00e010b1511040d1000d109000303e00319070b8000800c210f0201d000382c03800546d0780320003100b55219100d440107103000c03002d104208030682e07021850300e8009207007001c040c01c02d2030000103184c641740c5062450100003a003404113005d080103042000030202c104903649114055807442d4a0b00765440410f0242031100d45165000c2c40751001c500701184041c410328101c5801e041c1a6440c00e5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 8549494 1250 8548244 8548247
    0x702040c022b020f06100512010e0a1518080406171614130803071e02030601061206050607060c020613080301050d08041211010207080309090115020c060309060403020d 74
    0x76000b40302c0400c1034426901020640c1000035441c001e1850b60055941c00d140502109050820480b0040e40600b4450818441070801111255103100d0940c020810004c43d0b2999643d00e4007600002800c562030050b212844c2c0300c0703a402081210183c42e407041c001c4001440c181d03c0e5a00640115030001d6050700035160a910200000d60295448400721110b071100c00e41c0860740200e0722034200c0b010060402a03002140340c1160003100a001800156448602d0b41c42c06240000941640000e44e901c148110b80250750040b41c8a4111006400c1c180c0102c010600000e02920765544540d80c4118041104030512030290003a0461172284c1c1d0940e065640c1c1c5285401c207241c18291701074100041400140803e040c4580f0a0750128058445d1900b055035500081d40d0f0215150801c9a100c0c4507070b440300712030b96010091300018111002c05075007030080c0400030440700784c8140708420300307040003841c580d0225000b40016014840e010f0120b035500e151950b41c65a80d0201501c3c2100184a444c0332206080e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 8550744 1250 8549494 8549503
    0x902030105060f060f070602070f0302010e0607050f120604060f0308090a050406080618010b09070e041a011b0807060203100e0a060308030c0a140406021b040e0a0b1005040603080702040c02 83
    0x400081c04c5c517003000e9180e0583d820444048821990800a02c804201801701204a55200340d00204031000c0c01d0020904002000d40780b641408014042182c4548500043d01d4021801045c1c0183c0b80e503e11001401038041c5600440c1282d14009000c414002004000c007611074040e1002500c03255624144000c880f950302c9a164941c20440200d540804201c05140d0075030302c03407400412251080c81c0090294101036520201203050902c10080609082c001d50f5600c0642171b40f206568440040080c000000030f2a07500d10f0540994403140812403130340c00740d0341450380184045481c2d15041051000c481e1490091006010615002401961481c012007040da540b080c6c4150468550500f4254140c20500105090215a0035003003030022515000d0030050005074010440f15015140d81c2015034484c403201802035080c00303003080c51000000341138507003140d0051001c412035540d40e0b9000c2d1048040e0300003551160815000209200c401c3d8050305005008030740811000c20003d1090b41d0300c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 8551994 1250 8550744 8550769
    0x91502061603140109090209060f010207050d06110a0e1305060d0602030406020903010c030203070306060207030b070c0302030d09050a02040b090709140103020405030102070c0e0106020f1209010504051003090203010506 96
    0x5a20000c0065146120761840c03452148050801090942e19600340341c0460b9000d804c01481c0f6556000c1e80415880e0495031160001c0080d80e501c122a508040000c4d100c09282c081d50380684400981641002040c4d4084c0021442c1d1641c082d49507407080c64024206400240a948554011079100700804981d10030240030b5200200a201c0c202c5e0a81d4605000e504004c1003500c103e6800d02142d10551800e004113071062903180c1e00140d4030701c0c2c0b01701e01500300d0f041e640006e0210740c0140c0f0300780009071561403041c0d0801401e00306000721106a260481c50340c4500d01404140c135051a8554040107c0014050380c0580b0071a0180540c00c00b410a04c030303110a04440302000118096400c00004040c03d20b510b05205061402510b80754407400031030309991102c0411212100740100c2007142c00011490a405019184050012185030800a9640315050041c0004095000418800741ea0003502110018500588508114042824040c0092040c103206038000c3d401c0200140e128505030181020 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 8553244 1250 8551994 8551997
    0x10b09040b060c0a030903060e0f070b180307060206010608070305090a060b040f020f0904050603030903100c0207050901080105090106080304180902030102041703030106020f06040b070813020402030c09010915 92
    0x814104004220140160340d100c980c210804005408040c5028004120306a000340c0342c81b01820300e540781c06003c6910f080103886aa403c1076208040700c4201080c40c4c02110356000340e8544422031540d5141c0350302481c02c806681071041c1d02d4001480c90700492918122a51911040c43e265140d5a00307505480d42198107424a4210701c107898006010b41c6d01c00844071a01420000d0a40c0020005800320b0b800088a1120548013081c0c0f0015413409000f400d03801700341036010f10304120300c400100c2d40d5042d0b4000310f541c00c540c940d140c00e00110310030401c58004050050842c102940e48a8925000301416600e9150550801001050341c08000017101c04035000404121201100558540010030f00100200ea041d5003c11001031941441840410b4800620014507070341d516064002e86000c083d4014004643c000c9410400030540c071440b034541c054214208240280e035880c601e00414642c80000946c0580b000c07003072180d0102500c0162070040b800303803924800d06884849100c1c1d240007140384e800 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 8554494 1250 8553244 8553247
    0x9030b06010809100e030403061109060702010503090a0f03050703020d030902030601051302040f080304050a0801110d0903030207050a03050408070e0402031b060403060603080306010f030209090106110f0303160206090303010b 99
    0x1000c41d48140300c942d5100d800740c000d503800c40380304550f198143c03011207000c4e0070070754004a803d1041c03000d1440341c8441c0d1088416000e150041140203d00940240a0081d050200102c00144c0c1c100092002840140d80700c20750b00c4400b04940b801528079009139005400501c252421068182d00910410302c1035900100200250303031070b002c10400003075400a4441140c5400f0f200000d03040b00074043c03d02c040c00c3c4040c007071034036107040006218102801d5801013522768140303419401c6000e002c508450009200703140100700f1011904058000c0d21980c10020010711450000805042d84a009481070760800400e69030a50740c0e45110040380c44051b90701950641000041450211030603003422035403a40545100e007090398907207440703048842c01c1c2d005a519040020403c0303502c0da1702114010103283d90703040460900390035402240807903005014100603c0f00c280030300c8000e0f40c0c04011003095440a03800312640c0b07185c0f110b4141c1118024045640151180c50041212401d001c825030b03043c1d07080a40d006 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 8555744 1250 8554494 8554501
    0x5090601051003090516030203060c040f0312140307031a0f0310020d061a030f0a0603050a24020d0b0306060105030610030c05090604060e01080a020f070305090a050307061e09030b 79
    0x180c814440802d003400e0607590000080010428410020034120b8601c05c1a0120301d9170062509009006149801c3d5000070402444034100016040d400d0b650442850345d00709551a00565030415000c5035600d02507008000c10080c240c0c1904030f4541e10190048924040e90503009110418180702c410383d506070440e9040740041c003c1a4068520340d0340c500c6000c60354507a05c2c4e42c18290805050400600d4000000c10000100f003e0204103400201007142007044a00e5511850340b48d44458400038a80c0d06d00c144001141d4002d01008500510201c0c801c540e188010b00e140c0d8000c02d179a02d5221f02a0058800082c050b6001c0c01c29203200785c40c007420444440303400c80c008600404881e1750180038800c0078010406a80c40e1040508090b006d03584404a2400e141e0380058142c0c10700510043e0218010000030310f0840f1103a0503510f0440d8182006a10382c0c00c00070010301c80d40c2c49600110340501c03030240e0000b807076648008483c9201c201140001e0201d12010300459555115002c007502c81c1600d0f4011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 8556994 1250 8555744 8555749
    0x20c0a0318050402070807030908070b0d0f0605150d0b04061d04031101050c0c1623010c0215030f0f040206030c0c1501090615050301140409020d06020304060f0b03010509060105 78
    0x580c04510301c408681206a921a40050f00701e0b000320030203640b6000042042d004042d001801e030000380c0085c5000b0300c01e80f4900f20220314544035842070302017400d89890b0010001c07001030700600c1c06014000e000810054015070400c07a81d4120200441c2d195007401d280d4155410b280c0725000135030303070000b400751508507044490429501d0090300840400401442d0f03054a008284111402000e20b8104503a840380c503840d00300d240c491300d001048020104d28200700301100c0311800c080390204c06010702d5a514040742c001a2210500340101941245581c0190705141555400440c403410803981c0000d02500c807042e081341d040804881c0290450030801c04540700540400240c40809140300c12900c903401806407907520303040280c3c880c040303264a03100107001c01204030140c1c46200e119850304d6811580f41851a50342072070b9011720b490080d65a081e50900f9916200800c40059030410f00666684c1490b00d4414014038401d68808180ca141051517074702071a040c043c00e80076481d4640105441c0c0d00b08000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 8558244 1250 8556994 8557007
    0x10905072705010b07060e1f0614060307021506010c05061602010507050f0403110a0306020711010201050a15140109080307030801140a0302060d05061216050312070c0308070204060f08010e0106060201020c0a03 92
    0x31f49603082c460f0740780c1c0801031403801129445502c81000041913452a101d903404403107146440c0e4030b10840007130040000312540000c0392203038114000b480d41d0846e1121001079441002080d00549140115010412034104034985008030307903407513070081200b652840c6044800740515801c0650489003008100003040d441d03500000d888100400101c03019549540d914120b9100a1049a428025045403080ea680a200c2c403548060b0303120080c40340c10b0b072101c05220600010301400d030700d1486101c000400e5034410f01840001c1c14000088940d80c0000c0e04010380000307002d20440c010f07800e00461101243c00c18040c034004596001e000d2904119402081102821008294070340040c5840c1a00100003410001c81c136a00d2250180e5030300c114100b00516043c50030141048400550412440c000141801c0101044a40041c0055100c041d14400500527003600c3d4820524900341c5140810307400c0041d484461983c68000082000c03603a00c1005a007030f03024214904515400020310038012900030b10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 8559494 1250 8558244 8558261
    0x30b0a020417010f05010801051e0c04050d030215010b040605070b06031c03061d04020f01050307030905030711010806030604050c01030b040b09040812010e0906010501030905010905072705010b0706 87
    0x1101500702525000c0c0340040b500000c6407018280e4441c40074007460201c904c1014050f08001d402413005e441c1040c00b1110501c08007129003620081c40c8000380482d249941581c020b44401007000003824003030f080013540c4051785801030840361450000024070103290401c032801c4840030f850f00f1b801d0540644400b0300b400d0006000d141c06018286001d66540c281d1420074002d08826240003c1d1281803854402103c10713044a1000c20203480e000340805656400b681c010101000d10701190341c1e982c0c086d0124003910841900074450310010544400b00300d4042442c5000107400e0741c0300e50b89641e070081016950a02a5000f4000703030419603006010754800e0f0003104031098058030204d204802540440d80503d0701300c134240c0b0348030404201c1c14101e5411803140c50040914000d1203140d0704001d4002602c0b100107102e814149541c8006980070044290000d035482504130068400701d80d5902400c40603a400c00c006842803030700200600b0b403800403034864141650784080055007401d0151f41ca0000902049 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 8560744 1250 8559494 8559511
    0x20a030c050a02090901020c010e010b1e03070f030f060507030203040f120504080303011e050118051e0303070c090b01030603111014041202010e0d031b29090705030703020a030b 78
    0x10140d01c1d001d81c84d903c008034013403080d00d00016503034031060a0080c00c44a40300c0f41d4120b039904142942001d5507402d9030440c1540c22200341c900d0b507101e02c0800a89040c146901152414421b036400200748512840441400d502840003400709591b107110480c01c0b8030003254014086040300030110301095040e8140d1440d00c0b2030742011450680c440008a1443e04240d0204001c0d100031101407031440042c015400c000c00c02803c0001503e8202035103075802c0d030500d00440740280e445e58250101d81e80c0d450729801c100711700641543d65400c21420108010246805442c1c0b600d800c10b14100c045511a01c00c000459410055071000b040b0b0040070081c420500703031940c004004002c000701002d1429580104018804003400105d203010340d200140030412005516841084134444800100390889140703c080407032507030039680710030f0b0310714001060b546a16003120418080040c0d0b10381201c0100840d6001e05848400c881e051a55a401c1603621f140c5800000c0d001b0707070083c10800c0041d880034650740d00820b52 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 8561994 1250 8560744 8560753
    0x201080a091e05070f0803090105180102011e0203090622030c0f020907110c01030c050a050c120301090b01080105030d0c1b0e070503010509070807050319020c0d0804020a0e0403020a030c05 83
    0x191800b59500c01c600c0a042d512508641d000700283d104550040004022000c0550305241012001034040e009a440701c02c040c82000110080c1e5038800c0d4440c0b8200232203800152148003914032144025002107456020720320602010550303080d10880c1e40600e009180c1c1d11403041c0801c40e40c0032100009210300444a81c401038003268010f94950f10071901c00c03401d5030390b040c0d800b00841182900c0c0c40c1c40140140d040c03500e050001c0c505598044126204082c9606180d90381e403002544c0580f50003500c45c040d01440748044000304583d00c084c0c0103160340c003c4c07d990341300c0e003640c80d08101619285480b0b10940030a40030020302d0001500c1012210480b00792150310481140d80307219501d10b1070340498084002400000050000d0725008024071307040340080ca040b0703841f494842d402034020b11025000d81c40c10703900c6e5412005402029012110b40d41354030021780c0c0c0189195030000d040c04a0640e070413442401e04003000702d00a90045095440ba54050b802031101e4130301e0b520281c1d00301d10005000d40740c030700a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 8563244 1250 8561994 8562023
    0x9031715010c030201111902060f0903040e04030c02040c02010506120115060f1209030309020108070e010207030b06030106080304090c030c0219080d060503010207030804050708010e0703061a030d090608130201080a09 95
    0x342da8018102c004051b80d41d203087d404014030300074100340000304501003142d410400c0c010355507000020340342528007078242c0d60b103c0e48840c2403d99950f140e0142c020b5010341455803103007869506400090089000b03030f81003c041209444000d0a90f00c03140c003041c0b40c00c40100b0702040080d01c00d0700240304402c0729082c0031219800e80300301001130313859042c0242d02003501e902501c0210f5034804c50065000c0d282e450002038503020b101c0011d48884d080c0c0f10260000c006a0046003407944d00b90312080007494541e00b00c940d5507585107a52000b03841064110004a40740c84280700700d5a00100302041101c50510103d080302c00d00f276a60b410540c000f410540c45e0300e81d40e92004203985d20244020b0403d0f85c040e445000c80e0b4a024a0010320b824004d0300450340c107906001341080002d40c001448029241d110002151028110341c0d402c0c402200e01c00c0060b85485910f81021119401c08008400d4502c2d6a40d1400c8a5072481c00c0d690f40d01c0300d0350340001d00041c10380001928001d120b86c4000705082c030400f00d1004003403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 8564494 1250 8563244 8563271
    0x608100e1c02120307050c100212060618010305040204020904091a0c0307050a0c05070509040521090f13090b01030b07030e060106050307050a021c05040f090603080901080a091509031715010c030201 87
    0x5503034903614235001d50004100201c4100b40100f103901060486d40381e480c083c06586071090140016182605058554001c90115651501030341c1c8010300c060820032203082c03581408207000e035440c0351043c00843e904000c14400858402240d01c2940c9940320b051808419140407203440750400c9003a1868020b0690104240e41d503188d143d402207006e903000317203041c9025843c0c081c442c801668030380c0b40000c02044003040350b484216034441011411a0100301c4646a01400c0c0d014002c40310004100d409104004070402c49080b220600908141e542002044508400305030740303040030300907140491001d1001900d00c51254004000d620a14410b840c02c08140d0078009040084e040510b402241010030300b88084111500304100400c1d07200803e0041c0303491b6803100e1029120b44140503040212000014409403c19080880480d6000f01c201000401c809603440003001544401c90009505a61380740240d180400300c60b00507007503481c00d044000c21202c01511b240788045402c80a6548610803084420b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 8565744 1250 8564494 8564503
    0x6120c020309151603030203070807021501050d020402130f1805060a0b09030f0d0503060301200301032a0303050a0e01081603150f090c02010c0207030b010b09040608100e1c02120307050c 82
    0x18461b0b00c0140c0c607424590809400c2500c000c02c8a0110f5001e0b6002404001d501290103046031030560300644405943e002040c081d20800c503842407410b41142d000917422902003050000c44d180780007440d15140c6d440c200f00041c0c1d0800e894403a840421020144001503c0200920b00010b0080454520461040d403181c1002140741d807030b0300490404000c10000381801e00643d079000c54150aa1400c022064044200c180018080504030714400c0d0140814024000500400000c41981d120100342d03807440d000348503501c10540c1c08000761074510f0300c4020354000da0850b4003410041da03440c00c00c0c0b070100c2822801460b000c07882d1451010b10180000b02c884d0505058405846400302c082002001f4000190a40b15034030301100c01c41d40a17210400214281c2204c041c150f80219220680d0b03800700300b0011b80903060302d0b085202640038011111b107505c14180d224800c602001c01c140e44568007103006038440000b001c400000540c110702989882d0b081030500860744440705040c9a4240000c181c00035141 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 8566994 1250 8565744 8565787
    0x105070f0b10120305180607050601080105150d030c0308060402040504090c0812090a090c0905151306020102040510050c010908070311010501210303020306030106091506120c02030915 81
    0x485061405102031442c061441c200a0310408032200500c040315500108544100d0141c3d0b4a00c00d40c000e442c1c1803e90b100801c6550f07294001c4100d4055584030300449008001c20313110001000350100c64500107041007200300410b1501611500300b07031301441d00c00756414031f4018001030340075600b0400030545950314071403004001e004500c40503549082c0f255a82c03900aa070940f400d10300d001408007040b96655a40780100362807070075201241c100c80c0c0c007a05580c1c0d50415046103034031060024406d60407400c00e80103000045d9134850305080c4180e5480082c0d00f01c0c4501d00801d90080b140311902c001140c0610018082e03084004000244013007680c0301d1a101c3e41001d50120005103110002181040703003401528054030712500d5504542c080c103010565a101100d00090038145c000c400101f803680e0a510290003000c0c1d0b01824403090f51403418408131010380c0e0181c2c0021908148299086200d075210b400d001100b141c00862070700b811901049002e040e1038038000091607040107c0072a015500755000300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 8568244 1250 8566994 8567003
    0x1201050a0c080a0501050a1206020c010507030902040b0109060207050d020f030102030903091807020307030804060e0d050c010f06050d1e1203061d0f07080a02070c08030903060f0c03150105070f 85
    0x4124070150801000340401a003901501c42c2000c0c01841607036070b03c17100c0104840107038600d0010384265240c44800f034040e1a00d1410294a850104064580c04d0f420200540340308450401c80f10b82d401c00151101c1c00c0b80d000741401a4460f507000d20031414044080d02d030150008151300344920f200380c0000e082e80d00445d101e00298201080d1801d03642001001001e41c0512914035048511700030900940d02c0c00b800c1009000c0081480c003042c140300295000d8543c183c0d00300240c429910394158080c00650104007603030490342c40d1000488824a5034860b007016500000d2031015001c28a03103038589031041c08101c03500d0080301c00d2203c42c0080c50003042000356000340d441c0810814034080d610035504240600100503d4048400c02081c1c1c0c1d150705d0b01503072184243c102180d680d22103604c41c2c1d0090003200001090700503132803000308441e40e00001404c00417a0440403203002c0d544101c41101103034400e035400c1c41100341c24030201d100040300c4116101840341c1854031905000c1030b1f44500303004800c940c00558 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 8569494 1250 8568244 8568251
    0x60f0603060608030304080f030c04050405040c030302160e04020f03030f030f010503070504050411090711031309060812070303020703020c0405040b0601020c040e0c0108060a0909050f0c01020109020d08091201050a 94
    0x80241d5801050028603d10020310306500d0143c495098520442855100324600000044c200c50058420344028002c054410006803a00b03260a0f403d4012500099000d81701e00380c2c40c0b5031030603a030018034010398065902860098889900748500003502442c0154140000e01c8481c1d1401e116030003861140005031004082540342506160901d01640c00c00c5010b02d0400040001142d94212003e0030210305a408416664070740c50102d5049041d40100307041d50000080e1341c0140c01000c0060019a41401070800c44940e07504042d5503615103594002082c13540a02c41580801d001e40d01801e100f602070b0055070441072400e40010f0458404075800c641038000641442450350f0304122849009409850802410075a40b02d0290341d105510007413810001400001001900d03450b0501e401400031100500185a103072802c0c1e44c90324004001e4400602c078540c020051984140078500215801402044000c001511100c210b5801503031b0407604085880e40d40c1c692407200f4410310b4860b044800002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 8570744 1250 8569494 8569499
    0x12020403081215090705030606030406110c0d0e09010302090601050d0b0306071d03070501120b0102150c04030308100e0a050a020c07061d041e0504030c080a08060a05030d02070e0703020403060f06 86
    0x25003421200800300fa0140040c2030801440d503400804a1b40c010b1000c036900e0751699114546140038250180440b12010404079405a0303000d00060300341003800440e151911003034a81c40c00e01c030360010240710107948041c0c1c6102140d440d5000d6030040050f0403002c6800300703486000002003480e2080c19280200010000d10381034400e1a8150002900103c1c12805483c07028600342c0002c3c034082c0600e2003401d290390b41d0070a080c00baa0080000d90800c004152002d0740c00c0c075043c00390385044d800c030744010303030100d00d145c4001800006445a504183c4080080640c05030b160100b2090050800400c4400c01c603074200300110410504015450082a150340c0c5c0c0940400d1845142981a02c6146014011424071300c0500c064641030121300100312880c54001125651410100d414000d07524019004910005440c50b0159101320030603c645000e6410940c01c0d981c580500d607440c0da036002d00d80c0c0103801c8201e0078040c070100520841c0d000080c503e000350034191281c0f0317507404580e1242c2c84011080c3d641c0104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 8571994 1250 8570744 8570761
    0x60a03140c12030a09050112090501060e01030210080c0a0305040303090203150a0f0603020a0b0304030e060c01050f01060f050306010806030c100806090709030c0308070303090606060201020705010e07050f01120204030812 97
    0xd16031182c503140065030620108900280c0303c400d26004660501c001c105000e60b048a2a50200000765003060003800159601c042620205600780410383c001c2072004000c05410340216940c901403905076801c5880c14548400480003020301500481c10551220f03402c0c00542d6041200701d00402e10180c2403649401c05031f400c2c504941510303c80280c480c0c1415410070150791180c04840882e50100c84403680d81d42c4030b10701116000540d0303419690080b000f06008070000d105501040c0b04034500541078242e80d8840d603013a503030320300101e199200081c0100f00042c51540704200c80d07600800007030202c4001d0070713004d4009541c6840c3c415980300094a40740c1009468900580700c3ea403c51a14248180540e080d41c490790305140303030b601000d050240000b071402e04052103030f40704010703080e08581d08010240c2c940c03030000c2c040e40c03052806452a40c24000c40740300300709011910703808071600180f071410324954920043d1685500600c000c0481ea42c00d000000100300d000008040c0d070340c1c4850305400c1c5031912a21 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 8573244 1250 8571994 8572009
    0x50105090601090b1c02030c0c010507020307151d10090605010b04081c0e0307030803040203061014040c03020c1009030807050a0905040b0f0d0501020405011b0b0403030203060a03140c 81
    0x16885200c0c140280503150b600400300a06880c0d040034a19516850421288060202510711804852000013084180c503842400750540c0c5140303600034401501c03040800c03aa2405038590150030118120031080c5032910642c131200b080b0002407452100012030240c09420980c00264107030a0581f144021010041240304a9004d0b04401c40760908280c20052120f645034016260200b60783c1549600405441c050501803130050340080840740703281c2d202e1812080310380041c0c404078020300c59140030550016128000805884c66040b00442e141524003c10001e01641b40a140c140b55007000300072068007081c40032504200f040d6a0101d0084094500200345a200034a00020403100f0301590ad0381311750100e080b40407182d04030f6000c01d4603007078440003540a000d8040075070760149010790740000f00f010640142c8110b1b00240c80d034180d05030003220f980710049409800140828413000c00100003902a6003d550481c030003800c1002455166510f0200c0010074505410060f4400300100c24249030109 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 8574494 1250 8573244 8573249
    0x1a07050309010c0903050c010507050f0304030807060e0303090c09060a090e16050105030c09101101290a0308090409060204030203030703020c030607111903030e0706030209040b01020102030105030601030807051603050c040501 99
    0x30302610130134550340360705444861000205040080c00101403040c02810040c1c42d00005500064a64599580c0ba100205038880d000c1192034070b080100c000a015004400c1d640300302c081001030711550710342c5001c024031280300a05140d0700140c09003003c103000c21203105440301030114600800c0b0f00c211904a0400120300303548601d04001e801c008008580d5a880300b500c3c8680301c16600079092402180c000d03070b84072a41044251284d0304c7d108085d41d0800400801da440c02c0c1000300c1208041c4540c40030300070000810700002c0c140301c20800040140e800d02e9070141240340c5c082c0200500340343c0c40b64002421a40b28280681c0160320500030010b017403a05000441d00a003050912010321800890307040e48030354100311040c0a00d140c594001050501a4000e1880032010b007003070b20301890300c406c0098020b4126501031800f862500c03030307400030550052003124141c92004009091603880e42d40c900791558001c0c4000c6806000d40028191120125401400554494405400303201500c0e010300045443c141e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 8575744 1250 8574494 8574497
    0x62304050103030c1403040b07050c010f0219030e0a0807081506010305250e040203010603060e0a020c0705060a0201090b0403030501180606050901050c0715020604030810050603060d1a07050309010c 87
    0x3401000040c2c4c200c07180c8045142e000b1868010b21000500490660003164003591008070001443c0c4100030000c501c080401c00c09032265100c4110441040f60344d070a600504121a08640c0800004a4000c0c503d1801514000381000e0352542c59580c0242069100e13401494998840d0b0360909450140d44980b80d4810004c1c0b070200701c00d00d00300d00c0c2800e07440240d9140f0b028071300008a955012511402190782154030180c404e652344d594518000300104124840c00591480c40008108008407a008440800c036446006155550070702d41001318540c040c0071030303000303544d85c0d40980c900140340c490000c0d1141c0e000c2c0c0c400068641c94080380321081c90b000f515000a0621b060780c2801010f82082c19156906401e1810548480c125860790340b61000542003065180110502a0352a660000380d080c8140d03c81d0351a8000ba4562805c4048100a14010294018000e10001d1200e0410404201203e4042c0c00e82c0c1031b00342d030b070b020300499101000d8800c01c0c001440082000b408240c24000d2a0b02c000d41c5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 8576994 1250 8575744 8575751
    0xa0c06081006050306010c0f0b01051005030c03010608060307080105010b030601030605010201090201090905060117010305010f0c020a0f0201050313060e070602160303080406020d021903020a030506100c060e10062304 95
    0x710000006403510301501d028001c01001082c0c00703920810248150542c08000c0361039542082c2450505200701340300c0c0c140b02c1c200403950052000d2040040d00d016000c1c80b0a024150390a1001c10341e1000002041d507609842440c40016851a090041c24003d01d14808100c0e503a007000070004050b91130f00d4200c1415a8141100100182d0b4001130744001c40d020b0342c0340041d16440c0e500040303c00001c4940407014211000d400401448010f61040c84203208280c82080040c5420b44141e807602e00402024200c03a441e190310301c003d94000c034002d56126600c0d0412080940305a56050100c0c0e0980c0f91041c00c650041d0f40611515404024203040002c440c121016002d20b150b40040c00d00d50f008200030b02c0c20360081103460150180d0340641d42c0300c070740e81c041c030800711401101c1c003c2c001d4000a004000080c140b0000c500d49003004103085450820179650154860819220040604001d1100f0300c1e81e80b0802c0307502030340c104851082c54003812511075040108000380c100b072400c52002c0e9440e688628075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 8578244 1250 8576994 8577001
    0x40b0a110a06020324030303041104110a0201060503010c09050306010e040317010e04050609030f0906070501020702061903140103030804020d030e041805071703160503040803070f02041508030306040e0f07080a0c0608 95
    0x1b00041520360156020030000402e0841601003009040807140c02807802001040102c061601908090261681a40204186d4030103850450300d07101244030305a0590000c0c80184241142c11b19405d42c001e0090a0503468000f24440c200529a001d9105040c0d98203910b0501003007002c02d00000750803001c070400441c240907418080400030f00c100b50758284030700800950201004800e4054551250300140202e4450070600f510521003000e100c490700000b49022807003944c1c05a411401810ba9425076201400707175540b642405442c03000c8143c20b40034413400703004000c00b5990758004c803090111010f90f203641b40d085528246143c8140741d0880c80781d80c0c07150340d01c070f441c0305500206550038500e860309501e04d41842800d05500358452a04010010300000607804248404244140076152083d981000000011444040f5103131442c0210080d41c1c00800c0070422614013a00f01d10072694091041d01c444e110410062460000f190b80180c600340c00922425041c0301c418103400e03006051070301b0302081915 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 8579494 1250 8578244 8578249
    0x31e060e01090506180c04061502061003030512190504050304090c020102070b2205010510030c06020105040218060402090405130209060108070806100909021b12070206040b0a110a06020324 83
    0x208000c1c0174100b20b0004000312080c820040001d1000703403102400420186031600c2030550040c1100c103010700548281001305240ca4080c102010480750903076101400c0841d140c3c030340c2c84402d0010b401010011140041c1c0c907881851803117190700540c0b181c0000c40da50707807902c1c02100070344900c0c0c4584400e59105001c020003190481c074045503c000d60104444101003000345206410501d82c901030103a6107401d081041004055841c002581c0c060a50048103d681d04422802c0e1f500440d0000d400040e02c2d0090031454081700c007003d412600050025062001700d0021400300d90044a11804020040b41d41d141503080448031a90861000c1c41d00c1515440c140d2009048085c0250809004114902c10442300500c110380305005802541c01c295034500701d00096031565240c0701e2002d003807030040c8014000c6a000500c220340c20756901401503400e1a24115882500e60000c00824090204050000d002c1a10a000c00200c00c2c0c85640010b0b00c0b414019112038072214000010141045100008242070707 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 8580744 1250 8579494 8579503
    0x705060604090816050d02060a0606020d080402010504051309020901121a060112050403051908090a06020903010e0303040c091505010c060504021807090e06030610060c0606031e060e010905 83
    0x40041e6000b0a01104500d0020030034810038100440e426001c010020400001084080c00c0d109141d086819640b01d21800d241241c0043c4100405a1300030800c000c0b5647c05049055480350050500758105680c940118401c900d024030302c0303160349548140d07002c114600304580300e025261402c00813840a402c1c0d40c0740d8a0f4900d038a0001201045400002115684141c2c60000018070184091080d13040514002e8516005090091090107034100040340c01d038400d00c007440c41080c40b4401840104181d031686070083d030213040002e405540300c00e06140d0700c0c042040114041c5102d5101150054503110085048603070012405000c1c0d00700620401a503a48500d0304480a90000400201034560303100156842618488008060b2048010040d00d170b500a0700c0d1008999541c101802c3c41d540d0f5004054442d42d0407642e01c502d20401d8001842103d104403045110f0071321a00000410640b25116100c41c0c0701c0ca110801505400d0341c0e801002c01801303024036108014000003c0c441084240d46242c0c45 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 8581994 1250 8580744 8580751
    0xd0e100c0203120406090501022107020c0a050f06040305030c06180105040308070516020405010e070e09040210080403180b0703030f050402090103080f09061201030b07050703050403110109080d0201050402040f02070506 96
    0x80140f420007007028083d00d80d1284001e1a4454001c560380d070000b0040b000c0c600c25500c40600d10681e0500040c403070302d001103a6014188801090f5518050030b2000b0005501031071640542c00c10030510021000840800007001c8143c191002009140b50005120130300121600001985904100601000980025299400000d1400c0650b140c0b800a003105250a00010002c0d522a040c8000000c000316040051f40c002c80c050790305c002c01120070744140484080182d078000d410405d440608048248280e00b015040351182c5020052401284040000540f594125104a8000103542e8042503014812518140c0100f6024071541c0341940000e5694170051001a00b15000001e001001f00c04280c100e4203c3c100050030f40c1e0302d605d00281c844012190034001100c04d42c1c251004114035902400540303c0b1a40d1542c1e95600d05030441c2e6410500308008a062230512850a00219080000f4000840c0005041d030000580f89030600411003a10910801460082d10411141001c02c0012520315803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 8583244 1250 8581994 8582017
    0xd0509060304060912080601030b0d030206011403150103150f0c02030a030e010f060603050405010c0c02090c0a02191a0f070c0201030b03070f0e0103052404020103050402010908030d0e100c0203 85
    0x1c803030b80c90b820f21a0140c10500802810701d0300409100000300c0d080101980155000e030703002c003c005210380611010440340c0384080c003d43e0005004100882600308660440c13040a4152103651000a003c0084002c00780c000700d03001c0f060341042c58507800482c800e003078150060103c284904201004065140d200e82a0080c003055103d8915040c284001d4110100d095483d52003040f425036252002001000207490440e055403c0010080c41d00c2d105072500f81c80e5640040070084961104020b81003194005141803003940241c418000c1500d00b102e03810500103000703040015042d4581078a1504040004141d9600f01324072409004c00c10794082040da91095083c01c000400d11203503000030b46005129409800d088586003004500d1184011103a81240d03c02e100322013605024218130f200c5011404441000c0008441c0001c0141d807082d08125007150042c1444143d0b1500c40b040c41e811076102440d4107c14540341c030740301e20101d1010041c2e182c00e0955450104060f0a20080003500d070f01c5030011003103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 8584494 1250 8583244 8583247
    0x9010801053001020903150402060909090a02030601060c0201020d031b0c1b0303030605010f0302070206070b0c07150501212a080709060e01050108040b010b1c021204050f0d050906 79
    0x1c14000e120000c0349802802d50301c00300060080500501039441180080d0290007203a0344002d0312020b0051807402190300038041ba09040b0008188104003200800903850380c45203c60f01c4000d600c1c103004d40c9018219540ea42c2114400070b00000e40740c11200c84040007014600703a26052180012030740ca070440d1a0500d01115000300034109841ca0f6002c1208080203050504000820550507600030350840d0400c2e21400301c40594182d0980c200d006810b006134200340e0401000c00003074100698194800b90320450b07241010003d4071402d50980382d82d0120300d41c65594200502c440c100603000360f45600391480491031030300805e80c2d03200c62090540c18101107200407800c0d1903d0643c2d000f400d141c080c0080e042110b0100d0390711a810000341410f80720b25181c00000c01c001082c654072900b80144030b241c2140360b12140ea482c2c1a1120625400140302e0f000d2503442129555080c079030740c0000d104a400080601550741002e0400b0303400d0100001060310b45038028451102c845070003500f5038036407034005c50701070b03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 8585744 1250 8584494 8584519
    0x10020715020c031501060306080303150f040906020a0e09010f05011b14030d09030e0907021f0f0204080709110a08040308060d0c03080a030c0e01020304031b08030c07140102030901080105 82
    0xd030700d00b861200b80d0b240c0c180a150012030340020381c500280d0403918140d4080c0940c65850f0111a200d22060302c5078842050603c005803040c0c10551150005580c01510010360300d900780e00c400c422600034000c0f840000f8a4400442c4451424900d824090044803480903034041c94034002030983c6510f4a004030144240000c1c41041c00101c90442c00220b83c4001a00e0341c3d1100d0307280740c0000b454080c03800c402041060340e0100d800e0824a10075882604290014440114800c81c58655104092020344005490306a52010106640042c000625550005288050038580e982d17054a090b803c69054114050142c001c0c441d5111b89074580254250910910300d0705d0b0b200100c0c200b0140c418000d080c9015401c1c0010400c24440000c1100c00401c1e50108900c490b540d80454034502d10354292030040c1d1043c041072010494410b0620184503500b400b401016690301c0003d41903030881143c8501e5604445402c01c04482c481c3d801580e4071000b403024520b02403480d40040d00071007042c001d403401201d0050340b2 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 8586994 1250 8585744 8585747
    0x70b16021e06040b0c0708070302060912010b040c0207050906060307050403020d030507020d0b0702010507020a020604170307060903030203100b040f0905070c0605090d0215090c0409150e0601031110020715 90
    0x12840c1007070141800e0354503a01d600c60710342c450344034614102d614865200000340d6071a0203e42d86081d01d5008040d00e1526103820108610034140095480c8255a552040001a81c8074420f041c04800c2c1500501a60b602d48030070030200071070061400740076800c20000c00c0b021903408012102581e90403240740584108500f002c95250042ca00025005804203180c8001e02c040301c0d12091240015500034401540e4170102280c8804a490000b034220100f40010b004441104c1e60f031280b4560107004490402116484d8441074800c184001d90110f58008103100401080e01c603590701811480b65a0381c13501c2d240c802d120491200c1846601203040d603074404101103c0c0b00d03802c0380c0461600404148418204154140c0e203d0b0105580380e0003500c07560140c0800340e004d00807501d1082d90f1100107003a0107000c8038240405003240003021075803144102d00f40c814052040c800c024511007500c000344407541c118504440030480d04600380e40305000d4640d03c0811036600103200410755110043c0c40b007949804500 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 8588244 1250 8586994 8587039
    0x15040908040b030708010e0105031c08060f061b070614040905060411031006030e0d02031b0705060703080603010501120b06130b1302030906060406030f03080c1e0a02070b1602 77
    0xb14140810010500450b03d5000840314140c4d04140c2d0507418607642d0380300305a5208240c08401301c1c2c440d040302c95092014007848049138801005008543c54905040000c0c08650010803040c0a1180c9410103065414041042e80d000c4c12082c14a1440480000c08100b440d0140348200c26816071114009409519150400c801d00c481c01103540b6128144114203126411081c010600000d01d0004000000000020080320840c4550061032400d88600c1b440416444c80120240c220301c038020300050a51030310fa008020703090190b0b80b100d4590410904042c07e468069101d50f41441d004448000840c4d0307060b0609802410032580e406c5990f0540580c41c014020412099034007511034007601643c000079800541c81210400c007942c90568070007080100711401800086c00446212100a00013401450030341d40000c0c0d4000303200e0804030001070078684440c0364822100b005c2c0c4080340f140409a010000040500a4030100a0606059101c1c4040c01823403020302a2240c50801c0c0782c11003031049030a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 8589494 1250 8588244 8588249
    0x8070501020d0207150f1509020304020a051503090708060103030504180e10020c01050f0c090603040317010603060315051501050d020904020c16080703020303030a0209031501031104141504090804 86
    0x20255110310082c180302c11645200700a09085c14101001d03d0300d8601c1c036124407200300310680484986e007420041403034000e400040c0201c2e004070746414081903668030b40891002029610354801d07528501801001c2c1815450fa200d005d0581c4000018000a50002e050f00c044d00ca01280c0d050881c001d0203024070281c03500c2860f682d014001c0042c2c80010b1415600103050181843c0c00901c51034aa100c808141140225070b651900a0b003400000355900c6c02034000e40d0440e0103454803c08103052040c04004007076080c0c1c0954042582d070603080081208041d4150024036aa1100308400c0c50486000c08030782501250031410400c0000c0c4641401c0e5945d8152118668060700031500d80380294a41d590381c2640e9807512410302001c0e600014680400900342e402d49501801845c2980c0301e82c0304050194015641c1654140140186109241c01000546000318001d0140c100301103040c9080c0b1003101e4490841011004040c0d041000c90308803a200c003648001c060b600026407602c2030030b2050340e5000f1038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 8590744 1250 8589494 8589517
    0x30c090403020105090f030702031203090a0803010803030708011203120c02030c100501080c030d0504050904020a0905132009010b03040507030b0c03060109150c020f03160303170105030c0307030807050102 90
    0x64103020038154158040c07846686900212441c40e005810700704d40c1c0f4012004000e505501030040001c1200c0c1440c095508000b210045904d182c1940d580c8642c00e41003600840300984c00401001102540000d00364014104103942180c03408054400800c84900281c0d500c044588034401d03c1001e40c42002100c00242c0000195a02510f101001d0000b0b0542072051017028403594484200b81c1c030b0045074040b042d01041e101e103480c10b8580011b100c030040c00144141e81c8403d01c040005000d081134000c8600c60052410340c042d0800d294034210907051250000100004480d0b0f00c00000d9841e100503036815905001d41e20b0340c50740d0300d52405501c0d00c0410b4100074000044001444070040880000d50b0050744241ca0300000c0549550108407905210041400080c1184800030058200510010300c048405010740d030344c1c40c246c00801d0842050b251310807000a06038203010390800c207130b031001540503120407806400d604060800281e07482e442e81c000079000030702c00648103041150950403100381a079507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 8591994 1250 8590744 8590759
    0xc03060609090603280b070905061c02070212010c0f030b030a0f05030702030307050703050706030908090405060f040204150806030111030705161a010501020d1701150302090303030112020a06140d0b030c 89
    0x185c0c2d10032070b0108001c2012140010000c011030f502c80d02602c4a40c056480280c00c8508000c010f070b030400040c881448640508540c2080041c000d42c881c140b554850f401c151002165480c2c900d00d005101c0385007501004109440d11081e4205070b5008129a026141c2105407071590101508219007107105d03180000b580744c0301c00520f1604000c0045919000c880c02501561044d50f560741c4150151116040002c0003031100300901c500d01d01d030641c00f0b1500144003600c8031542c410550003140c12a803064018200520721340c43c03d03440c1d4613030203105142d103c10240c2c0240b080b81c1c1c144a10024a01010340f031007081c0071020610b20500522149881c6070940c0040c2c050344164901c490122603a0420301a4500600a48031083d544600840344510401c00003600040282e18210b03010044440c1480b0100825800704540d400e250380800c0a03601800100c081c42c41c0d17090745841005404403a0b40c0c451024841004000c1d0340104046040d01c02824412001141c0b4441e01c20010341000c3c100d10403d03030700050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 8593244 1250 8591994 8592043
    0xc0203041707030c08060601020309010309030516030203030a06060e090103060504020d06090c090e0a0c050603070903060218040b0a0305060105090a09060f0c11161502160303020c090c03060609090603 88
    0x24001000c0d012240034404d403202c25903d503200d06448001c11030740b081c05a4020884000154803d50002ca443c034040d1a00c0d604201c0100ea03100030040458105500681c8080140704403030826110b0310008080c1810030b0440300301c0f140045072403600d0511010b040b6070303030781d000007415500c0d2401e4040c182c5502040800c0052842e2400c9040c410b490f001d10940e981c81e201c0003202c84100000d051701000e402078260010b580c5030208001141c0e200514034400c001031000b0000025280303002400e0000010030003074103040c8515050004980c136041103144078243c41c0320200040703030021a0182c1512025036001c01c03d50b4540030540058080c4003002004039203441400c5000320f0007540305150002c025035925124880c081c0504d0f5a400c01d102281a004030514001c010840ea80c0710120a03e81c064010385204074050200d24050384480d600a0300560803485200c42d0518040c0c0c05540d10600492919003181000740c08691580516031015000f020710501059003603808000340b0b101980c8588480c410882c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 8594494 1250 8593244 8593289
    0x60203090304150f0e09010503031206012c030f030430020d0302010b0f06040f090203040203010f09120201060602070b03060616120e040b060315090a14181006050a090c020304 77
    0x21300d440f12150004406120111191519604075412900c00900441c2131403c40226110702e1100546064113010000c01183c0c002050000e204c00b00d0a0005400b90003150301034289401d0840040300485590000c100900510011000b40d403c844102e145010500f41201d800e620b0081607204c0c065404501a4020310806505400140140e40c056400e40980700e00301c001d10a50b80140e0180c20034499a42400f808181c036140d002e9a44180020008260000080b42c401c04662504105440100b120100c4540759a0240103038001010281700400c0d62510704242e01c1d50b01e0002803d01c921071480058a01c0940c2c8031148001c01c401d8001104c0c4034100c07100312018009803030b4078800314000c078149042c42005150110a070303442080c4142401c5051303400003041000c1c840c8010f00c0c0d22a0b00e660303014000c4d20311140d11602842070300e2041c0d03003030f0030340d8a6210414906000d1642c9011002d04101c014002e40e1035021503a03007240c403099004100c5e010440741c10b9046001c0c5400c1100e400a0222900b040309 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 8595744 1250 8594494 8594507
    0x10e0106030e0a05030f0706020405060c010203010e090c0904110d060c09090b01020705031011070b0405033402010503190e01020d0e030a17070309050303040507050102010b10020a06020309030415 86
    0x3a40a91401c2140034940d5540c2d54a4024803440600300c3e030014010941483e5861006098207449408014076140d04c03400021015004541c24000607035010005015021409400507008030030000101000701740c007000560394510007000140314985203803500e00310707407220409039815079031000c41840501e20284008055405034890005c8840c00e28102d012603500100701101540c80103000740c10480c00254100016080c1c4c00700c030301d0b1001d008201540110b00c0c0072110f18010780c03280000e555190024840c009030071608504281103080d10034000d050700b2084100303062007a5428200142c507039a80b0125201c28201e84040704400e6410030451101041c410b50003030240240400c0308210b141c000090b065500d0040480420100310010b07584406801c0c0d00041135441041480d0202d41e2000c26922241150401d17a0102c6030b03540004414030140d030702030003002c940c500300342c0301d1880303d80c0510300080d80c0e80d0040780007420f01c41d400004a041820107000301c0b4050102c2000301c406034072007810b009011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 8596994 1250 8595744 8595749
    0x20307020d0801050103091104020901110703050102071a0105011e0203040504060b04030501050c040503190203070f03030503061212071e05060103030807020d03050106140904200a02011802100804080c0303010e01 93
    0xb1101070001ca1158000e10805c0308003074000840b1100e1200d080d007804002d44c4241000e505100305441070080d00507080100ca406548120300250b10344032540381c07510050a0030041e68880b00325450040c01181d0744902500c2d01c52114030041040032041035030503411403007140c020941050610402107060200240248203c0e80700700020032071383d5115441011540a82d00600d44d0640103000403440c0f8020100b511200240000c0c2554805030380c44c0401d01c4048010380c4210301144020003001a103261988201c1e40c00c641182c080d140981c3c0303113100f030b14007403080600c010000c044410402c4500d079200981c08035150780c88411608a944c407404c01800c0c0301300403148240140315840c0501d09040c032070700405040f03400325121614001421a100c4080303801030707010145c00c5a9070300e01c401c442140c0f8803242440000d54030311a50340c58171007620081c02c0d51141346409014240c0801c8540050b00d402c2000520400c50386400c0030151920f1502410300d214106d40d461152001000110f2400d40d0b214000f0704 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 8598244 1250 8596994 8596997
    0x40303112b0c0905010c0c090f051e01030206040b22030503070209130c030807080c070902040503010b0402120a020318011b170405060109020901020f120403050c0a080a030309060b04020307020d 85
    0x7615107840d5104041e02c00c604560380003d01040420000e0b5401100d80c0400302d4401e410721215540c84250031170807103030310300561b00e0070580342d00a00c003007454010b0200c040c84541c0410102103605540118001d071055100d98240c01000103603082e4200880c040c503001000d68044030705041b0fa0759040c440da907508850f000f40d10074086940402c1c4242d02640c4d800d03a5a951200d0303002505440c40e103445081d6045400700755183c000412600000c480248103035800741ca1080c1006803128186400d15003100c0e1050819070241344100300030140e1318685507081e54080852000560303659100c4000b40701501d07006045182030f41c2408402e001151410783c046400c031800350b460002400780240c4403601014283c0307026005400140c01400108615001010201e506004482d608180d1039031591903c0c0e81c40d0107043c0d500d513001c50b0603c100442888140000501101e4240215051903506615a02491001800c1c540e0700c0342c000d020007105800030484c0e900300034030441d201e1803c86006500c030020f09900c00c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 8599494 1250 8598244 8598307
    0x103060b0f090108070e040309080f07090608010e0a0204090c0302090c030f0601030c0503040f0302120a09030c0501030b0604060828050702060601110703020909030c0625051204080304030311 84
    0x881905282c04480d041300c00c100000e00925142c102c6006840d04054010f6003040b42854007c81d0600040180306000c40c9030300001c10310f41d80b03450b10b420701319505070304041c00603410904400c614030710020b00b900748550102d80020700300d944c0e450445884085584002c0d0443d5124041180500352035000e10320800d0b00314418182c0e503030b4200045089a4a194040b03011038010310124000c91041c40c0b15043e514428011140301c0c007042280c0310304a800800300c090000e240039105004000040100c0001410203003020700c0030360302040000b04d403401113001d02401c02c01c030000040d200c1d4040e4880103040000d108083e4800f5684d42d0f01e140c000c2d050494605015110310f9001c6403041d40b10380d1001c50f0a80c0e480026100c1035045600b000010325014107503000130710081c0310340007805000b440308a014a80c5ca1018241da160410f01c0b07290b030098a069032200344001445800d482c1e4013154507040d8070691040c40c4560765030700c0307242c1600104650f1024811042c0d01054100320407119083c0488a030b460110b001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 8600744 1250 8599494 8599519
    0x3030f02010b01080c130302040e01021308070506030705030c0d0603110909072303010603150509150103020904080306030f0d0320030c090d02010c0b2701020703091509030206030103060b 82
    0x281d00b03a50707104041c107000a4004000801022128000d41480ba070721120b00f0420aa6075000101030361642c420340d4420b40d500017480d0403090a50929100240b0140016006183c900000160701e804014061810b000d400000210001d2074841207402485d0600020007003151a800c10644085102e114580241141004036030010400076061085696036440742c0200c00e0125440241c280d214000a5010740d241e5402000248403443c00021040105800103164600205010b02e00318400d1080905290314100500168992848580e8040d4119400607500d84580d00482d2601d071003030603e51560302440412075000c51745030300300101800480c4c141604084004400324880d22060711040d041d1002086841805c1c18036299a02d840c070f0050400302445070070380c0c9503146c42c3d039001c0b10b01003444840f40c0e4500c20010702445040040582c003c000f1400d1001e80da40160400700300340115113002e1106c40034000031701d00c8ac44464000e154050451074403960341c0d151180180804c034403214428000e09041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 8601994 1250 8600744 8600747
    0x30203060907050a050c0304170118030c02060a090308070303050115030606170402041104030b0a05010e09061302060c0a0c090b0303070b0403030207031404081506010503090c01081f060903030f 85
    0x2500d01414005004000507124203030140c030b0940c00010550240481404410740b140c074144041c00050010182c10055084882100da0849110004003404005008000000300e54400210109135905907041951003010b0300050b9404011580020030a0a002902c03604055150701300c0f6040b6a0310174010404651007070b800340c080d1107240c0118400214403a1565151408034445207070414000703800060701e070790090038141450340160400e4070b1407074009040c130816440600c40c1c64010400c42c2c0c02030001d401c0024505803100340c090042d085400c00c10045c4800d654458045a0b503000c0584200e824200e59880c143c95065402d00c0342c00d040034907000d000a42400d002c0101d5000d1548680d04211590ba5035070160001d42040b082542042240c02c280913040b05000021b20103400740d1070040c02000c094015003146908001c1000c0d040040600501c4040c520020b01203079002001d09007101246d641104451034001c0c0d403a0f1081c1607013001d0800203121500089070005a80c06599000000501c5040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 8603244 1250 8601994 8601997
    0x10501021009080f031003030f0302030c040b0d0608011d120703050a050a02010b0d06060312032009030c04020a0305100b0406080112020d05010e1b030105010b0a03151e0302040c0302 80
    0x102409a00300d488441c408801c030707a00c0160254442d5090f1424100889604021a00121021403c6c00040181482031642011402003102c2842c5029403451a100a0803a86070041d403142039014140230589640112480d08580050042107000b00061105088440c2d441030000c0c0d01211f55001c0c05408035000f9500c04101c6480c0380c0c042e283d0f41d01c1c219080340121202e80c8200009404c40d541e80e0703c00f0a46a6446607000400d45c013440c40450080d0650900c6000d201d00014180181460404c14460400303e031464070400c0d6060400c0380c1e4542e04c2d4440840c0c1483c41240d0070a50292001409089a54050780080e001d02407500b820380b0007a4455241d9621480b440c083d840c041001d00004020b00b1140b004d924424600c058101128406207564880c03e60f03141c4c0000b141683c204419050805072010100300c0559401c070000c0c0b01e154501a5100818400da10300b1008160711589290b004401500f42030000300f4400b1400c016030600b82c8045504070070720b40130484c411030400301c41d5203460788a0300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 8604494 1250 8603244 8603249
    0x6050a0b0306011b050f0109030e010507030905090901060315020310060c0305043005010c1119020409080906070b01090506040207031704030201061706060a060302070c0b070204060b031501020d020601 88
    0x30320840c41e5440d02401034403025501800c02d0f0b881c10307205840c83d00040080c48003069284098001003a01e40e101c2c038001c0d00f06002580098108a014051800030a52000c10001110410740c1e01010b641c441a82c414050005500040c02c43e00d2503a0b10004020b096500035481361000b134240c850b106071104021203480d8000c0d0380250018906000900c09c403080c002c1c0c0c0d9484c0c3d00d88410031120401d082c03c01802d130707016000c100fa03c1e036940d00c250b0280c01c2c9401c0080d0b08555040b80c8081c00300c03080c1c041103240d603e00035500060302603541ca901b00420084030400f1116a00d40042403142c840600e4035102c40c02c2d0101f40605044e141c203050201d120742c10310340259600c3c690f05888008030320000c0c80c000901d641300240309904641d2241e600003903020418403403142410b42ca10241c151441c1ca5418002e0440040c2d00003800c040c0b04000b02c002003845c0c0305e1003030141c8858042d07407907803011b840c00041c016041079000300002840000c02e2148400c100495035564203000e0b000d550b0340039180c403401d030307240c1c4000d1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 8605744 1250 8604494 8604509
    0x3050105061c151b0e01030c0503090709050a060308070b040c05041506050c1002030106030c08010503032b02130905040308090f1914060106080105010801080d05040b0901020109050a1506050a 84
    0xe110900015055010400500c03c50001c0040c641079186611655a124007280f2804070f503030f0307088440080d41c0c1400b0316044601030782025451400c04158031503442105d071051040055a039030109007100201c2d080480215000030b5119291206030030022036102066800315804c00006900181a00349802802c0846400d0460f40030680e140ca082603031164068841107c0710f00422181d000005042d102440c0a00803e94001550084c655800703840b41a040c2c01c440e2095105100002e03a2603004403400550481c01c138010400e003000340306400064011091001164080c1070702c00704282086a109038032450081d035079a440c544034440c1d41e548444070381d9140381c2c894002c0c0804440031841031011415540c4900d44801c001085242042d040840a8010100207205517004004070b42c2e0109000380906101c001510720042c41000240c00d80c40b543c4030b840e0030428003054080c0e817a8001c0d07012008040d00304007603030b00046d0280780a030990020401c2e0001c090303103030400125050500b1034250040c0d8064 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 8606994 1250 8605744 8605789
    0x10807030c1202010e0901080c030c060f040515041212120902150a0509040513030201050906070c0b060109080303090115090209031216080c0102031501110c040914010905070305010506 81
    0x34001e0444074810302c210241d0500c403101c3d203020425103461402c24000c00009010b03100c035040c9041018149000003c0582c440e4105101c82071070340e10f4140c00c4038221681254451081040442e4010076401786a00118295000b000f40005000e46201e6000c3c40b015569110810038a00c50345440841c0c24248000e5000407101c2c1b0030646074042c10005003402d4036039041003070400c82c40300d00003406d440040301d4041d200000450218209502401056000510500509814034120f0401402c001345c0802c0075080030b54100c045416a401280d980c0d01801101d070580c0e41e82c5c0b07040c1c45002d010309101e541303103200205e0401c400544d00c60a882030300c030800c00c010054100900c040820708220b800c16035910b07035082e00743d140c10000110584010511860100009a02e0346008030481300032190010700d031814840d0b107000740b0308a50030224024401c11030442e00050f540f00c1e00e0a01b1801e50030340d40b50f03141c5590310300b04082e4184500000d841003141c0c0f140c4000e021540d07502d030511803640c10849841100e40762 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 8608244 1250 8606994 8606999
    0xc060f0f07030507110a0807150501150509060d0c020d02060702061909110a06020a0c080304030803010e07020a0c1d010807080307020105070302010e01060b0706050708040302030a030903020c120d0206010807030c 93
    0xc80d411107500107081e4030742030001e2940718100505060180d00115447d000001da000b04101f40300100c4500340d01014010401503141040d184809000d440d44030003000300c0019600c80c5640c900d41035074614102000c0400800e842103201075680c049030418600948100c4000481845c4009a002c0c416148200b0040320100900180406411200b1044426505901905106132608a8541c3c01803c13164024881c00e5110300707040506401030342080c0c40d103401c1044240b02003200380007200c0c1140c1040250410039035441000f2404d207440070134000c0409416200000b0100400034010415400d40c110940150b682c1d602c00543e00d040074407402e040307508140200740c0998002c4c00038100c218003034000425000c41403201d1070b08681640c0c01c120104170001c01e0400a0050034400c2680c049070350b040100c0e150806e5100a0750340c0c0989804101016101c4c582c05007014424030000c51421005031000070566105d2950549032512929894010320031280006203035600083d44500712600000c3c00a140ca0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 8609494 1250 8608244 8608247
    0x506030f1009030207050301050a1409030705070605030402060910110c0604050a0303050714191509020108010504050a0204030b010b0306040c1b03140405030303040501090203070b0901120b01020c0d080c060f0f07 93
    0x8840300c019819070044c00c0d1700250740d8030203001d001e04c00d100c564400210849109501c40d000320001d0040220341d44140500c0e000200001254001d540c0b060a150f51a80d840d031000035a00c0c07154242030340e00040f600c50600d00e90782c0c1014250303440d90402400d0300c52120080040c0f007980e000da8030440b80c2c480203207001000428003603c01052014000d919120880030840c23003184c9000038940c41080c20b001d442c8902c0081c800c1080c10a04d0900c0c09540c01d100c00d8807990002031610606010b81403103540d9860229480212950440b001036612881c01c03404c07503a5444000c0d40381e401c2244e43e9806181890880718035644954001d4090072030710450380b585000c80ba2422079a1349505482d08020080c20440030070f443e80c081024508c11803040c8000f1035004000c1c8107150a21100387e0040381c10713550034001c051042ea0018402c0b025030030000c40005540b0305070380040340741c81d00405a40e5000503c15000702c0510044c840200200c002d0035044503510b0f01e545c4000814008119480316591090705c0106403080d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 8610744 1250 8609494 8609501
    0xb010c2001032405030d050301080c011101060f080109060b03070501020304090504020406030c0b090109060e010e010c0611031e01060c1205030604060f0807030b090a0c0510020304030602040902030106030506030f10 94
    0x100c10300d8005482c8406079a412208102034a1845207403580740e00070011031900f04505002da510342d1400f2401c43d40350241145ea80c0041c04070407418890806013241020409611890081c82000380f1941a180c1c0c5000082c0200040f41080d034a860405a20300342505001030250220344040c1d00840c6060300d0401c0c403000404000c2c4c003c0303034000e450310000000318125034107800140c4960082542e640c103684001400c101103542c01071044c45564080d032422a0303001000c0319150242800c0000d8552401c1c07905c0402000d0b88210030030003100100c00d20081300740e1003800300308034a8444841e020740c0c0d880c1d460550303c08241d0500100000308a41040303145920400195800460150000c10021340700d010800071031099821060b1580d1002c4410400d0001e070000b256003040842000d0b003803020f07164031480000f0055000741d90048440144206000b403082040b5030013176400020464455444401035400382d070082c410301c8000790a1001064881c0ba000c9440039001c0c40380e178020030381c503038244011202a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 8611994 1250 8610744 8610803
    0xf0109030b0a0209041d06060307050109050d02031e010603030906020a05070306020c0c0901030b0717010305060402090c04090507020102070b06010e090a0f020403081b0d020f03120c09030a060504060b010c 90
    0xb15400340124409600e450250712100400b242545030100c800703d43c1c03c3d24081000702420320070fa221420421441e608404035409555060361801040d030407500110345826140400c0380b02689010041403550081980818241c0b44030355200f0714103e0b502c840499982200241c00707401d5130842002000000d81980c020300300030381c550040d5000b038502c0c2e200042d15941c09070f009580d00058101000280f1f541300e03c04030221078018415000c15415510390581d02d200050009000d045400080340e44402104181c0300185443d8005002034035007110001d010350850801215040c0003000460aa5070040e130601c41c0005015110011300c0d03a656960341c000d0b100071401102119070800c0044003084c4a070008062a40740c01004000c480701d000c03003041c5040310010211045401103d05003840903000b20482b00d000d04400c0e0145296260040410313582d1107065070702c560610420824604001c425080700b449980140d07400c010060f9007000547c0d205001c088010300200b03040003800d081c020285202c10700d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 8613244 1250 8611994 8612011
    0x60f0109030c091a04050f0a060b0a08011502010b09090705010807110a060b01030f0c0507050601080102030601020604030804020117190e03090312070501061a120603190b0615180a050f0109030b 85
    0x113203844150081400c80d0390944680035401d82131030411425103400d01401000346240c003495894034588040081c5022818001c2c4001c004003070b0310399158540300350441031220100802c143d0640c180304d15071070b035250028820301e0f010581000001da1f0f00790242170b070700704240010000303801f00c24415652a0020400418058103140c2d81d0300d0021f802c003200d031080d4494600581c561542c0e034022400c0c00c0340340c00c0d0140d1001030140e00401c00c001c0d4070b136030116880e90000d038941031440c000e80301c520041c2c44030b00500000c00514482070003000941400d0400000016084940404c03d001d8222071003516442a0101d5a401da807082950b068200a00001070507120f000d1400003611584508800140003e0071070071a804200c08100413186406072280940c01c03910880041806444003c5081d200c103c3d110b0002d400c4141d95800070355a5150600100c807061041d14003261380b00c00303103020340d84101c050800d2180646206240403500f810422010041000d050b140e0103c036034a165070302c00f030141d0000c09814 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 8614494 1250 8613244 8613281
    0xe01020708030c070f0e06060a0507080c06040b190506010e01050c070e0a0b031203010303090909030c05010c050301061403040203100c1b0317060609180901020906030f060f0109030c09 81
    0x2001c900a01c058580c201d4075102900300180f81102e502d40c2c501c0030b43c21130354400718800d051107000d56172441203c81c9061030382450750711011035090100b42c5010307109070f0103c0c0b4000d01c0708000c10002040b280600c81c0401030884100c80300c00c0740300c4000f19402155154003190040e4442501c56001d0000341c40a48003034411103c201c1c0d240d0400f1030700b180090750a004403d844001c0b000e90351a0a0181078100e00e40800300c3c604561460700c0082142e4105d01c035540c0500e076503c104000f0705204040f0298000e400c00002e00c0f0343c00c504000100140d10034407034180019125490b00c0b251640c0d44003101d010b83e40043c020006054041e100d40c0042c25000c01403001d00c852454000234201d03401512a480d64003a495403144928140d0258100c0000182101c0c0701c0c0d01c0403c000411581c0340c01c002d0700c1c40c90b80c0c1c03824440c44c0d9a44014644c020b1141d00341e0242e22603004402c100303011182150242c8200030550f08071061a1074400191000e40040c04010301031100d1400c148803002c010340c00700c01c41c03001448021 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 8615744 1250 8614494 8614499
    0xa02090d080712020f10020a0c020607030806030105131106160512040303030c03060b0a08060613080a06110f04030308060d0606030503090405011401020309010e060c060f070e040b090402010e010207 87
    0x200c800084030821114404041040030a20241e42c84042c1904110f0010340510030307480c0459a04d03080200541485940e022400f041291b1090001880700ca6000c1c10990f41c500060401070000720044072098132a42c202070000d5486184180380611055002c4011983e2000b03400400c4044e4210308418100400c00c000302c080880e608010340b80060f03c44c480416601c1d819030a00500f642d04c00c001410a01d41460780c200302f0300d0b2444085a440750410705c0c1c01d021700d855100000c1c0745440380180c03440500765100c102282a09001c82c01c041c0c503a100d10b40c208141c1025002c40c90441c0280790861104190620080010a00402c1c455a1202d001003d041c0d9010507660b4440031902150025212940301084040071030401d442014098a841305240700c0320004200000c0d6644500385030941000700da0041d64032103032904001c0d11310411070f1000b51606450081d041a18103031084400b4800240c1c0701c3c145122070706080c4109202c540001c0c003807100d565076540040d0b030940c8545902504610402500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 8616994 1250 8615744 8615749
    0xc24020301150e010201050709050d0303060e0901020c06010806010509041b12080304030e03120d0c05090301090807020a09050c030a0207020105070209010915090e030405040b030a0b0c0d0501170c090a0209 90
    0x1140a000c544a62514440c640300c4001e0101c0f0340304502d90306682c9040b081c480910b8209010340c0c200c2d002101c0d0b2600d0002503250860261449a00401c81c2c1c41c4281e041c04654030041d00a05007601c0300700110740b0140c0c1c1c1c0e008000d0342c42d4028420710303800052102c08100495201c1d0020174840201c80d003100c03491542c401c0f00d1888180500015140018040144000c065110341001c0003003900300c0062100d030075454280701303403403146001c1c44081541e64a0160501030286040e1059860000d008110806080c10041c8041e4002c001c01c82c444c46078004042900820384c4540c9003d003811180c11821980d07031070400c40003988031010603414080103003c0c940040e56406501c601a002200300030594100d6540ca41444100c60f410248020381080d00942c400301000007902c08503402224082941d0140001003814002082c2d40a40100121400c0101e0703d03540d42c0040403030540d456410030040c0e0f80e03030b0a401c4065002250401c0203030060b40d0f48024505c1e11402c071035000821210018908242c8800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 8618244 1250 8616994 8616997
    0x7080304030804140c010806060901020a02060304060e0115030503190311070c0609081902091b2106010c020321040b0a030504060e0304030b070804080d0203070503090c0a060c2402 79
    0x241207002032169410002000030321402d0140c40d03100f010007485a074418a001824203000184524001c06002c214a14070344e20800c08107100d80d4028008a50f6400d00f0300748540580b820001059441d0309140d02802e07500782501800e42140d400c98084e5040020b00140300b2510a150107100080607107400007881c52a54180080500610034620405d04a141c003001810881c2e0035032005002c1d4100411010303000c480c5614000c3ca03654111403140c00c640d03c02c1400110081450607005002c0780100c2c100a041550401c2c81c054500540c403d1403056895400443e80303080101d20003500340d0020b500301090701c5550000540c000824102c032605042d2106142880f0f80c00c00d054040009443c0e80030301c42803080c6072055820340c50078040510b00d4141161111500400301507c800304001c01400000c05204505043d6000000c40d02d130159503d00f00a03100414079001034420811314007802aa003041840e110010f9012541e060b01c1e03040642540381c80340700b201e40f401424024883c4802c1405c4076030740103910 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 8619494 1250 8618244 8618251
    0x312060e01090902040b01020102030c160525030b06030606010f05030a0f020a03020403060510140d05030c07060305090c0a030c050105130503011517010507051c09021207080d05130501050a0203070803 88
    0x6000507003d0b8042c0100816103140c1078101d8196441001803201c07203103004040b207070405d4040b00c82c00d10a052a01e0164034000244211091602c0103101c0001000d001d546031804803800766440e041242c544100f05900c810054a07450701140a1000d09a28140640003441e0b00882c40700c0c001450500391000340d01607900032000240040e42c00241030080182520400c4e8019890000c01d0700e90070f05091032041590124070820344560031422003e010000e00304202e41104080c90281c502176580c8013000b5015000a80d0b0100700c03802404608440c46c14a155003030300b125040310b081c120300c62604c1c00644066002600380441200c000d140440c0d20b840c00d0240300002350003401c003001e03281e00c0c0c0982c071000094112070b249426414001030000c4107074400240d03016500d0000303192000c0d610340f1101500900c0f2141d0002e411009901a40b9121100422614101c0700240180c0c0c0c031981070018103e03010700c1001030900c82607404100034041944140c01502c2602c01500450303141407174a8844550381d80084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 8620744 1250 8619494 8619509
    0x2a05040602010f0207050c010305090709020705070f23120c04060b0a090605040e0601030b010e04050406050114030703171b03160507050114030703091b030f0b060d0b040312060e01 79
    0x6080058540c244030340829000868402c50034400035990303540d1110351380310381981015221800b0500c8950248840001805041011543c41d11117180c01501d85031603100b001120740c2165000031310341300d00f2102c5041b580d450021100030300303103c00c08202e001c0c0d2030544040484e01c210745400c040d5440300c0c0b01d101c000e08903070441c254541c8000321000344405104d8021804022003030008000114911000e0b90300072009007000f040f465141001241c0d00940d10300542d600c10704041c10300c414004c403030748546d0507604409024000740d2000000d15039280c0d2184002001c400180c0998140e51503040040c01c102e01f054080d941364100c0940039145150060103200d00c3e8514030b52564000c0020800544004120a0034800400703041484440c6041c08018040303024551aa403030801000602d42c144480e5210000b50040340e40e40340d040c018200100b0301c01c21a11601004049110f42c9071145002c1c6080350b000000000e0350b519507504072400c81c000354010385c050751610000700350144101c0420b400303031900 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 8621994 1250 8620744 8620747
    0x903030203060306060604030308070e01020102070602040b09030c01140706020c0f03040e0f1e060105070507080111130f050913030c020406030f030215060102030d020f04080a0b0103170c0607032a05 87
    0x182c0c0c201424010003919407486482d00f0441080040e80021080381d0140c41824111041145080141e001e03210b0030100800036440094003040d00495100075202800c8180c01b212024400200152800601c9640700c03002050305000b00000a440d54008111300300b02c41080d222040506035940b032444d0440e412603602034260b0700400c0782c110401b03c0e040d940300c050b201c17032868624800310b2400015200500114100300d00000e00005000c0204402c01c02040c01e44001c1086403030300e40c0524644d4000d403e02c0e5104030440f4000007514203250007944150703175000304030102c640c44a44081c0060400841e00324140440307079a1500c0541d03201e00c03490303000b0f5001c3c1a5020034108280340007403c0ca60031800b005032803056076090044a9070b00100717035081c4002500780140e4030341c4d042411499a0142c1e600443d851700c20303e044001000b07007180741d05048901c100e255108004520000002a0080c1e0b94140c01c00c0e405000020700940c0310b5080030300ca00b0309400f003c2d48182d21440a000708400606090008245d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 8623244 1250 8621994 8622001
    0xf040201110a1a090a0b040303050601020106080a050712140303070203030f0906070215070c2411071104050604020702030114040b060307030503030408030403170907091b0507150f0903030203 84
    0x2003054401c600c205548001e4140000542c0d00c0c00c1c62030100000b50f8580c68145400545900d000b0801c0403203003500034003104060318207442c2c000d018200c01c854642c015420410f000422601c005a0140e000303a00c1400740100d1800c3c9901c0c1c00500611040c1680c0a101c2c600c035001c8181800d00080d8080e86050b8041c41c0c4d00e24058580409604010303126150795440907003000010740e80032452500000d43c142d1100750039103500710201c440d800d2014020740160317103011502c10289000014140341f8000c2e100280104070350800301c0a414090650064603840c060340780c0c040d131440e00350b1107994014001880142000c0803500401d0840b0340c821f103d000d841c102641400709102c0c41015182d40304400300c1c0204a200e04690b01c003a00ca000c09040145905408404102010b01515520325170702c1058030488801d00e0600c1e1860390301c519920510300d02074500801c0a40310300304030f9401d100001c03d0f610703211328020103950382500c400f001100d00ea03842a80d4803411080050180580c3c1511030096401507201d05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 8624494 1250 8623244 8623247
    0x90d21020d09051c050f0d02061608010303080a05040201090306020301090515040c020304031103010b1203071202060c030103030c03030b04020f040905060901080a02100903022d03070812090a0e0f040201 89
    0x2400c00590500101c20003c0202e65100b10034120180c82d9000c100001140394513000d0b15000e00480c6254940c00303034000800c03200c3c0d400a0204c2c8203a20b86503543c0c02c2c00c05140b0007540e0550080c0000780007d04140000740054041c2d81041c1e42240c13040c90440e100c1036072a2503450803038000384c00c2402181d80707a100344400410b082ca00501110401c80b01044543e8600101940e280700300c0c0310081c940600d0590559050b40d003036001c0ca101a1300600502c0304052501e0301c89407a41e0041808403204101800310040c0b0318170005280b8810641f0950a0b80366900f10388040d00e02c0c5501e84821002c2644034281090303103448600142840c0d500000b0015161030a0503120425210001d00940c0100729140040290640000781d0403010744d01030ba9288844c1d412104129031020032600b0107504046299202c0800721400c2940b0a6141c45645400003404900001c040e01c8480c24400e000803684101d17004805076240c04000c0142e01401010613900d10750713800090764020400c0301e08a1035186220108019035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 8625744 1250 8624494 8624503
    0x5010b1b0c010914040213060e030607030204080706080a2405030d020105060d0807020d0602071505010e040302070314010204090e0c041103041a0711010912021204120602090d2102 79
    0x3420800034042a18006000910140440c4a00c440d0b0707114800c0c003020a40c0b0b4590458041e03505891400c0d6079991621400f401994120000c80d0087c4030702c800044640384603200b941d080e2032700d140c003038800c141c9401c0c0304541c042e1010f030145240c030f65980642c6010308480220000e07103c2102850900c090f107400e0815080501034030180b010740e410030003044203640d1403100305000968002c075503644900306400850b084100440000301301c1031002849405001c081081c907207c9442e0248107026030b80c1ca488a803140c446007514000c1c00b507408040c0074070004408004600c0e584003140d00040c2040d60754000303c0e095521030070440040e500812401101407c10b401442e15540e040e4090a26504150740c80e4504168081d000280608a40b40480e5402d841a80b4000300c0c3c0c10355100a0010311102d04102030000bd0341a00b20b07000d48a0340c40b80c14000c40f034007019a8222130707a500b0f081034291784a8548501a502c40e0902c540d03c414001001d82c00250321041403552076074501c5070040c10403603000019252 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 8626994 1250 8625744 8625787
    0x309020f240c0114070305040204050c0708071101030b0d0b04050d0e0a06050703090513020d15180207060b0303041806050901050a03021002010915020702030601170606120a0605010b 80
    0x7030742030303560318048549000e45468190003200082a0349011603001d040c014400307100c0400d060100b120900001d25819040180035a008840c100900c1d12040924030280c803030340c10001c009034020b1040383c012a1004460046840d01810081346140b4150005525090702d001c2c1113440010000510081c407108001c0ca4400c101d42c1d0400084003118a00000c1311024103218103000c01c0400603102c42010b10890541008000251884130341c280c00340e1414020f0f412010080c002285002c0a120701220a00d41c03d00450750308111020714480400c105801942c022581600e034180c4030082c091f11500d003007005000805032154016101d9013002c100d0400c0e40c00641c400c62282c1150300040c02030360b490bc1c0c000000c884c0d0403210700025150000d8141e01404440302d001d4540c003519078031110f410381c0c42d40060880034400c6094070550380e21101d041001818072041248581d008400181803805c003000c8040c4001d07501400c490314994a070340d640303050751400d030429107030041d01041303101070380d42c189880717140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 8628244 1250 8626994 8626999
    0xc030903021c0b130f080304060204090507050a0e090601050a050c03040e010303020d08090a02010f120e060103061506050301030b0402040e030705030c030a03050106170403030506040b1503041a090303040201030b040f0c0309020f 100
    0x1c6060310f851703161182d441014094850200080881c00700b1005a0442c1c00500d00007030180b00d00d141c400e41c09070058200d2490300300840d03000417040c2c0903807034003400c07451050303030141c40e410f040c0038043c04101c071303181c000e070b00c02440030f10003080007150303141540020038000c41c440c0c1d009107118004150018080c00b0042d01280a0b03621a5500c0d80041c1e802c03030518800245245002c98000c8404038219000d00400c80c0d000140c0d00481002005020264100015603040149080c2c0b4003556854122140c5c4000d2002801e030540b0340c3c0114006190a42164071981c0e0184101c038100066500c45074251340c000450171a50341c3c00050390711020380d0980551401031401c1e0500c0c4104d11510300900c4c2700311a00410007020556100700240e0710359580d51240301d543c8000b40202c00390002550341521203610030307501660004020002251b600d02f010f604180b240d03180501542c03e5803200d034010350280210814055220780c0310140ca1a20039114030484552856503039000c102c00759907005021442e0010a403032030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 8629494 1250 8628244 8628271
    0xc08070b1b0c120304020a1e03051209130e07030b0106080108070b0403051b030f030f07050705030c01051206040204030b0c091008070207030b1801021b06010807030b070c030903021c0b 81
    0xb8101a0102e030070390f55191210b6025a907940d561000840c07401540d000340c50340c0103420440e00380c00b881c148144001e59210740102e17403030103058007a004118003c000015502030382100072200080c0e0390382c01c62005c510000b411602d583d51280e94040000c0d409070030070340c000f5080a00400214104002e181c0040c524003095505c0c081c00c58403000d8450520140500295040750760f030102ea602c1c1006600603001c442c0c4103a0342c40c0c003061a1158500d900c01c0e00f017910b0310301c42d441c4042030928000c2101c20584105840d001d1609200f00c00041d00500e0003803003294000c0c1d00340000000b040920001d503101302a845052540d031081c2000300564924848144410800060100030009800242200a498004060036400d60f00e5802414100c2608020004c055001107515180d41d1130818660b07a034804c40c0c10961f01181c0c1c0383c5001c16602d01051001610080b14680429030b00b80c0122140c244080c002c3c600004100d46a4020034145400504001c90041c10391405005011610000c0d603044120b00d500d14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 8630744 1250 8629494 8629507
    0x5040605061b070305030301140301240e04030e030d0f260a0b0a0302040c03050601020714010215150d0b0901060b09090103080a0c0515040c0e0f010905070c08070b1b 73
    0xc1c00500401c2810950030300c1d4840c58414000c01040000000d41c1e10030100c9a6a6848a0240340c0321035107070b034030390307010358200115149546112181c04680410110020402070f1419034401604a0090010703420700100c1c1d9180d010b42d407010f001c0401601c0c015114140241100307200202500c01a41c03a00c4450140d0b41c80206500c007000a1013504008100e40110f5010005000a942084541c1c00254802d240040000050360582c008034843d20b400d0f003d442000d5505c0c20130b444d00c00780c0c0300400c1d030040e0003841c00c2034a050014080d0f40e8010b010310031846698610140812003104813400140d94210a140801c560742c01d00b4024440a06050000c0700d00345007002002c110320101c1808020a03c0d180822400d0205100300c5207448a150003004480225039a403a50855103802510706591003406030300c0c04540c050300d001e980b0740101c0d880340c00c200a0ba0f20b00341d0304500070180030740040c00700300b200884000400e4a800142c12450f0240103414181c0c01c081140d0b425040b00d4510320844401c060240c0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 8631994 1250 8630744 8630749
    0x803061509030c011110020403060f0e0a0803060d030c14070f0603060f1208090a0e19050603030d0506060c03040902090f03010c081506071502070303050906150d02130203070206040c05040605 84
    0x180c0703030f100700e0070f0800c00f00300003950282e10701b03003038802e08035a6500703102103400424041031350011110440a00800c00100040e102110744900d1480c40c0984050f908101142d258146003454044007400b03482d20707020014081da1861003902c20f01c2c070210010741c000c5505000c20300c0f41585d998010415410300300480c601d021605544012544185c0e408590b02510203c20302c60100101d43c02c1e03c0b4000e000510082c0c65002c0304004903020340d0641c040210303400744410125514864a40102002402942490308610068020b4600100116004003013805158805d00040028201802c51581301580f200001018040369044c4204064400d130704001d82019120740040100c0e070440000151680c0b00e1b40880b0100303c09215000004042c8048200b141140480981c041e01c0118840d46d0705000d0b0b40c540541d040d550340c81c180d84d442d2501516510340c0b4031500e040d001007032400d80701a004c1c000c07200c46041c2ca001240c000716000d10268004604110070442502c9100d030241004403001c01c41907061102 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 8633100 1106 8631994 8632003
    0xb0c030c01150308090415150201020d051e0106080c091005091003060e06060903150103050a02010f02010e0606040203070201020c0a050309150702100f0903050a080306150903 77
    0x40914110300c465110045031342050f41c4506000c44e81d800c0000412490b411000941c0b5204000031f00310201e42c000044003580c3e5000140c80c2c0c060403c010042d44d1004011810130f81d0203030f400484040b8401e140c83c9c1503450a2500310300a40e102d507408109889500d15065101840c0700200350110fa21000400e0007510507500c4030b80070900c0b408140c003602c94074001c0c00d41d06405000001d14a040c1840600070301c41c4003d0446101c00810000070b40c07540000e80007540c55803c240280c2c002d40d60050740c001c00300400707803000b006030580c01400151182d2000c0c0c17a50344a1a000004208418803d40655181d078141c2c0c429035200c2d05003440d1981d6680d003c4110540592802842a03011440d1082519400f0781c0203003000b01e042d85110000c581c03c240d50054082400344007580403011400401107a00301798130860849a4034249072007000709501b41900d0301e03651140108445c40b40c603200400d = true := by decide +kernel

theorem cover : BRFrame.Cov 8453244 8633100 := by
  have h0 := BRFrame.cov_init 8453244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 8453244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 8453244 ≤ n) (h2 : n < 8633100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
