-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3249
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:05:56.009422+00:00
-- url     : https://prove2.me/submissions/99546a01-ff26-4b9b-80ad-301c8d1fa1e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 584172661 ≤ n < 584352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 584173911 1250 584172661 584172671
    0x2060405121513020f03120f0a0504180902090f0103030206010b160609080d1113030f0302150a140109050f07050309010b1201020c2806180b15030c010e0f04 69
    0xd0145442d0020410300c070824180d10b03004010b0baa00084041690861007151040c01750603a074010180d84a2102501400d1910101301c0b841d03a02c4401c10044c504000d483c108681415580c0800343c200c01001588510242d403070742c900d1821072601e09211944100f0f8525406055419520001e68400050040c54499040020a00c04140070728000c00b00e0349901c600c0900075840c0600c3e012120350440040030305080d05000d02ca41c5c400b801b031401d988006151008043d01e00f0301d5910b0794a00c03000c88440560640c050010382c4c84104c0550720400344280d10426002c114100b050508804c00a0140e2205901520300810703c400c0308456046507810000a2400700d8607602c6450340c030781c0100740c2c0c035410315403107403910038003000410064018104452102d010307910a0101a0000034400e007404900005201d543c8000300300284982c2c2c4440a22880e101c5200c406512550701c0c07044e440350030756a4003038401154205603924078082022490400d400c2c60140880c03402100410f00141403108500e11070340c0c4070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 584175161 1250 584173911 584173939
    0x602010b0a06090b1b0f071809020102120f0c060c0406090b03040f0b1b0a0c0b090a02010c0620040303050c0c0418060504110319030f09180509160803040806100302060405 75
    0x34005036080c2c4c58041050303806c40c0301340e0001c4a03a02c0d00c4611942c25210302d01e00b4032101d801c0c907500c16080c0d0541c041e0081c003910201c0394480047c552025107000d41030841848610240030b41008a5031242001c3c902d5581e441d07081a03806494110280e01a1740030440c10001c00c00080d0450b02883d10050348042030200c1a1500302c20182c0410500002800d60480460443c0001e58008400b20340035020344800c0046494001d1103a03152000c0704400380c082001a040d520004001d6444205180c5401242054111540e59185101d600c0350b8816000600c0101315542c509034103100b80c14440b002114100b220100b200070b200040311211202030a01991100020103101c140800d03500c1080340103041d210001044480443c07841e4024005400203102e145440d05040d008402040c1590902c158000f0105d00e038000c0a0040d040c010704021450007408030207030030318a0440c9044043c018003000b85450b2820160034914101e0000d003041300b9861881c40400141e140d4108447c20b440e4140c070110080010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 584176411 1250 584175161 584175187
    0xc040b0d0608010e07051203041d0a0f05070c0b070905100e150301030803040b011d13050f0618013b120c031806031501030e07120503040602010b0a06090b 68
    0x25074446191542820b2401d101103201140b505c06480d4111041043ca0700000122130740ca01a601600d001c0020101d20001a095010b140a51046610b007000c60440b45060002081e904240c45400200c0c1e9404004000c0000c18109654410200e04d880ca19580c03400340025682c0e55001901018480b55002e10f103165240c0d0074006141d214000c1c8482d6403135960740b03003008107644110340580e0003503040000810b03400c45078242d926040c24403c1c00d844a5403201c402c19030356030600035412038080c840c00104168001d401d1250b40d101d0203101c010b811590042c1e42c912401d4031130314562041400220b08984184085003113401d031344500c82d0206440343d2100b00c44040d140044e80d10502042d08004034105800300000002000802d0000c1e4106900c2c0c4010018071031300c2d0000741c51510409071504e2204800c1d5100ea445a2619001d07102218034044c0d9032614000031100600050f1080d0700006800c0c4071268090141a814a1080c3c1d298103102c0d01e00100102070400c82d01609204034000110324000a00e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 584177661 1250 584176411 584176421
    0x609030f0305062421130215030108030403020108100509070c03030507030902010801090509030f0403121209020f100504050607030512010f0302031209014505030a1e0605010815060303030c040b0d 86
    0x154060303000c4403074108281c502c00c8086c0411030480c49200a542d10b10720300c00050090781e041b1100c690083d41454203660064440b454024030f000204030301e40c40002202d41d541000140618010f440305490042e160400030305941c002420401818140458840140d0740142e9a50445511030b10000b06602c4e0500c1190a40c8074805c8410101240864080280501042e44c0410b10b41e49450f074050000c0301c04006016281c4900c8040d620206824504486090a076000c05090440346810f5161584510000700242c002090075030001d00c01041c00401c403074031425103501506c448810480044c0c95640000c1da1281c180901c5845400041a0001540d00400d000034411b00232003541c5856404039100040d51002c4103194004000e6686480c2071195030100c2c4400c261075000c0c0c003811501d003c0d5140ca00b01c82d1903d13251203c4030090700031940c01090291190702d020b0103100300a01540d440081d540154810301401142c8650020001e0103030501da410200c0b03045849a0b80c40a49810158201400410b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 584178911 1250 584177661 584177707
    0x1121070218040309080d03050f0c072d050f0f0606191805040b06150a0c081b010c27030209041511090415050f09130609030f03050624 59
    0x400d600c000e202c1015080056030085d1203688080f00d01640724003074100c00703903a802ea69480200340c680d4081000c4050740c0004251203800361303c410303a444c610068903483d00a429030300c54894502c040400010003009200380448041090014520300e8164100d5544039100500080c1c03082c60494400751000711248054002000e03154580c40c20907208016040141a084034200c0e40c1c0a64200020218542440c42815032181445000e00b4540650b0342520041c0c0001740030340b03403200140006100c02c480c10110040300421500041200300d807225010b4982d0154407001d82205c0428900400c1c4401c40b880e0300340480b5011036030842d403030f100c905203503070100904401300c2ca095040100406201002d1801410b000d0340c00e89080003031550052900b1202406800382540c00400040400310600d085020240c2140000344080c0388401103076034031003c9441071402100030031101c4070004c0c0d90315094071890f41e2000d0182d070b600489e10040c0c1c0780000440030700c0c010300340010804035100300d001b5121548402c0ca0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 584180161 1250 584178911 584178949
    0x1a090d060e0607030e150103021e040513030f170f040c080102180f0a0b0f0901030b0607050105060f01111e0f03130e09120d09050a1a0711210702 64
    0x110403845a060740310002103c1c080301007400c080e0f00300300f00840016161004242181c0c0b85c00f04c1d90842d401c01070550342d240c480801000000b110710b01d059a862142900070100c9180c04c0c0c0c103480b25840e024221840c1c02810106110b00780f000706050100960b1811703800001d611001c90030340ea071882d100b204004150020300742d81d0310114102100c20403401c4600b2181c0803c0301c0c178028140440003080006c2138140610400f40e1010301c1101d0448030910003402d002d1030141800f14445580c1c00c08100340750414035050384c0c1d0381c1d1500e06010181c2401d5802d660303806028609915403440d01703851103944048050f105180e141d110400c2a1000e01c040c4034030f00014114805403995504000c0031695016054012080c00c00c0d10311001c6018051700080060415240b0a03034203040a41b0000a6801403d80f1041600c0351700513600710800050b503072440043c0c1c85008603901589401e24401c000e000c10200e540711056503204401d4200d549024108000d003643c0030100356a40c0b80c2840c804250100481080700d01c070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 584181411 1250 584180161 584180171
    0x80c070909150f0e0a03110a050a05060103201c24140903090916110d08090d030905031603030204050a09020705060c0301150e040213080c030f071a090d06 68
    0x2001203006000110031842d00c003d1002103e03110300c00f0100e400840c1d45604a41c440c0f40582d0005c0d00440768445448101816117900d90301e039450b0181011010142103a0942000005004005e00c00c041100040002100240c600010347e0120303103079024504000300340c0c9024000f5841001003800750403c07501000a070000e26509080314a02c0030f02200c01c10662a5100600040e13641a4000f083d03644c10311000741088015101c824048a007414800f84080810240e03940b5a544a002001240c0c020748869542010520303103220528148242200072504146c100404c5802151001098545d002d60f04041410031007424078040e80280320f10340c0029000903454500240c0c0030303116030241c1005030040c0d0036980559030300410001284000d00413078400340c500c092a060b816110341c0c403001e007010010340010b1070175490100c03403515030403203074400c844941c803c0641d1f4000b801c041c400040c480140d40010284030b414521240126806012155045040400c0302d13807880d542d01c02959041c2e0703080201000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 584182661 1250 584181411 584181413
    0x7030b04051e240c04030f03023a021c20241b18010512040b0106110706091202042703080c03070e010c1b0b030103170313080c070909 59
    0xd01c3d1940f040b4100000d180940e1803220383c1500712503207442083d4040c0918545070039035907036070f0000036002c0c4240e085200e0f12038042c074580c540a445001003030301d8a030540345d204004444042e00407003082c0d60302d0440d0414039516800340341c40c820511246a00f0305003c40006013400042d14000d41041c0c4a844034800c0c441d5070041c2c4041c1c4d07030060f080c0401000110303407540d582c941e100b00b103272003583d045e200452020045c098502c441c0480da0542031105151007032529503001c0d80590000002da90aa410304000d070300400c243c035044280211591486401780000624015003e0182521445404007901e4000c800800f15502c1c0c0d80003011907001c0440e200051130b1078511044000311001805c802083d5008041804c804000c0162413040c0e80c1d65898485a000740d000450300454003001c1100c4d02c0c280c541d2840307042c842c9104402c02130304084241d180c41e0b41c55400d00301140790580314a92000441081880100c00a00b1400101e01e600585802d47e141c000400d210b1a00c54070754801c49034140390003041d078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 584183911 1250 584182661 584182663
    0x20111120108070b0301121202120301030602090f190e10090509031c110a031d03040b0a0201230408220b090f030c0108060f0a030503031611070807030b04051e 70
    0x5050b6400c02003240c030050f0702d0b8411544207100c00e000340390200d856010b80358001103204100048144651041c1c9800c079203541c00901030754100381c20840394250046421102c3d030801a0a0100b0514200c07180c1c82c0810154100e01c00074980740c01000c0e40320001800040c1122030b104849402400c5948081140b03107040440282c90350014603403800281085040d070301c0c000d001401070000d08032880429903d0002180010b800a00540c81c0b1100b002807001200f02102e5000d06c0a84000c240c8501001d5441540c2d000003800c550300c42400b03d21220608640101c0140d00041141c0d02680c0003070000d9a0b2400031101c101c090b10740d16a41c461039215581e000c0742e84518840030b0940c2e5541034a201440303260f00410584c4402c0c08400441c00969000000313543c0345050070030390f410040c010300228107081c0c407500e946045500c1280d514084403094001c0c03031041d0f0b80c010312203070321221039034054150203081a0b40c482e1155018407002c1d0005c1800c10106e0248041480703c40c000c00c80c50354a400c85020b01e0020a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 584185161 1250 584183911 584183947
    0xf07020a0812040e07030b030717010606050c03040e040f0c1d1312030209040b040609090b06061207140d0c0e0a090608031c0b0d030e1003020403030203070204090201020111 76
    0x1240203121034500000c154030005031042140000541035400c03d802c1443c0ba03805400d00030507032010151545203600e02e035101440400090240085c1070002c496050341200d00359541c80d44440d08000c4104107480c0780c0c0c0c0c00441520705035500703444d6411480e141ca04050800340444000606030720440c0500017015200c12030b000000000402284800f40e0310100c1d1541c07504581d00000d8941074414012850840c400e600811000100071700002d0078a6100020400300d4a0300d410013100142e48104000c144016844240d512803000c5a41c01d140284482e030220301d945010300600c081c420868406090306030168160f074003504c082c100402c842c442403000200140c01035034000b4050400e4660201d030a03107627401032030160740d10707000114906821b19140101401210550502d0035590b911109815038503013140281240c029a1980a2466103500f000503111040111200345407041004200080d00070003a0340095804650000d80308000d4001030340902100b01d41d01d80420400600301185890325001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 584186411 1250 584185161 584185163
    0x1201090207031205070806091b070c0f08070506040303081506311d0402041b0815040207020d03031d01060b0a0930051504080414010801180b0301020f0f07 68
    0x240300e20003c4440d1061084840c01c0d2807403400142d82000140721030804407031803a00030b815a041c8403411110303d09038a180742c00000f01151214034100c0104500070421066101800c5001c0c0a0050300703261800250760380c03045100082c1403200c5000090344c01d01a0004898000b00e01134000d950b10614a46044802c0c540c80300300203060768001032991210030341c80250303005450002d440082080041d04400b81116030081080ba4480d807034014480c0c090000039505410040c42d03444c0c0410a00306464021140d034202e110482c01140b060040401580e01e500e20011016058100000d038008014110812100300c0d8007924040d608040002030555050802480514441d42d150207040361240b00c4004090100c90b481c0013100700100782d040000446040c3e400035688544100c1e2045034007036080c07041040045406a540302c1c40421b040044900303400000900b00c2c0c09290011141d814190b140c04040c0100c1c0500c100c2942d906622034294509504803143c01c1404414151912881541841280c6c44000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 584187661 1250 584186411 584186417
    0x2040f0303050918091e0a05030c011b080907060e042009010306090203090c15161b0803281101020304150b030307051c0c0206070c0e0c04060905040e0102120109020703 74
    0xb00104e0904070f403551090107041080041c008411100103840d00307840d04c18401026a002d1802c041c00040c000300002d00380c42c08010000714540040c0c255402c04548420080820305c0b0414041140a010218029042e10304504258050072048400700303005081c802d940f62844070501070007950780d10300346c4050040c14409aa0520102d503c2e00405800e0b40815544d1030741580c02076900e03103c7c078074004061401202e110444c45040191550820403100d03202d4030300381d400c0c4510141504600c0c05000804029000410085180c82680710100314900c000c0c1a10000c01055104a50b030074900c189c042c4644034410000940d100e06150600c0700340f00c14010038100b5000d141615042080c00c2c080143c802c0182c110000d80070301c00d0004003641400c481c006402c4104440040f031480140e55500281c1091802282004003407820008042500b150241920700941000d1004000d100d6000c60508117881c426a07011516494200035103000e4010707440700202c4000810004203201000742d018100b40c41c0030f55 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 584188911 1250 584187661 584187679
    0x142106010c05073c030204050609070f0e04110a0206010918050304030f05070312051c0b03030a11030f070f170a080103020f0325060206010806091c020102040f03030509 74
    0x401514200da80355401400ca0304451020088400c1989448803d482d10040100000001c815040d0b01c40a41094407058000c02130307010700950403d8800c0036031101058032445440d08122001521030024006c0400800403503411140f0161595085050145010031001d5140c0d003402c0806526071400740600c00c1424a4201d508440c01e401da2202480580c1000c0134514050542e03c88103c1200a00c0060b20f031403080301030000007c0c1d900320050328954099920b89460303441040c02e5100000c072181140c00d901c0d0414486413902d5901100700c80d241c2056003840d0340104030b08691241180610010150900c3c004100d032424024050701800b41035109580b1074031014620800d40080f40030788105480055034120042c4010708080d0303011503040000500707c940d000d6146140144803400078280510b0803652020420074540c0400040380900400c10142c4210328260060b503070754417403040001c0b006950301800500c0c80c900039030488000d1315050040d42c01841d03d90902404991008010501401c221 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 584190161 1250 584188911 584188921
    0x130318030308060d050c0a0e0708160207060e040b09072304120f110307030819030618090212030309010911120c040c0509040f1d0a03020a02101421 65
    0x1024120050301d516031224403142e140c182c00d01c00c41e0000004111400e1080001c50007007a0741d044030507001800303440f56503006da01e00001e00403c2100082e100d900b08600211080c074161381c010801d074059a4040c504424160402c500090240802c41145900144218140030791164480224000b11103001c008155404006041000d588110b1240003410185400c1c0000000d009668000030f9602039071210b0204808500020b00b40035071b0790b00844070482c00042c0c0c00784d08800455489400c40b45030508200c15441c2111607000140c3c401361009181d69a10500d6085544900140d241c03d0303821001c070380e00c030b24092404a0081ca401401911107a503400d0201301075141c0342c0112030b00407803140040e100c510060001d11016003600f041580a20109100683c81c4c1d88840c4030702e1600e400f8100c404604858004890700c140d56405411008a070020004200820340014003050500d50645200103034001280c412108070310b0a522030740301c85000269481e04410000021000540707900001c003110380b91 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 584191411 1250 584190161 584190197
    0x420090f0d030207050d020406030615090b040603050c06031f0611010501170d081021020405060405011d0c0f0706020901020106080d140c070503070e0115051612171303 74
    0x1110760003001640482014030842c2030541520807501c1c40a00b000c20116103d0365100245d540c81d004446011021140812009125000380102404c01741c40400007103086403100384d1100207000701140103950010200764400100540c1c00c1c90410b2580b10b008a0585429000f001050300410300030542d0300385400400c4034060b070016402d610210200500c4074905035002604d03104030081a1001408401100155480c00d424403d12403008101c01240028414810482102d0b00501202d010301e180000602586c056200f4806050741e6500710254640d46846e1800044d10840c10000c2d140700340829014200011500506080d080980080c450705899442d440ea48090040303e00c4001451800c41050000100d001460304601140a880b003043d210408030b45130201c140d000031088011007004209841403462811720000052800900c0c000010000c21300081503034801034a5409181100103e06010f041d4503a449003420811607207074030700300d44443e072282c00b1024294003080b14030300700c55070f8254 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 584192661 1250 584191411 584191429
    0xe01080105130201030f061a070512041202010507080906040308030105031504031e142814070305090607020a030b0a0e1504060b0d170a031b0206070503060420090f 72
    0x1519841c2c1058140e400440140200c4640381c1c10141d61843d000c5805220f8041d000e0f140c4c1165440c0581d200c510345441d03403820010a0398030441c0036062005200300b001c0100164205502440d000340c480c5800c0c2409080d41c485c1c0305030303141d01c6503000500000708100000070b54100c0788200c0c01d55010960600c0702c100c0c0ba500c2101c00400166004e4000d030000d00342c410100c0f01011040c41c01d41d90108006241c03813007a40c04034140020381d641c0b6641c00e0400d803041c428003c581a80601e01000003801080d4021024000c00200500340980422244813646501c001d40c1c082da600105000401503485c107002076202001c3da0140030380c600749140c09800d0600083c540a4408100403010034642e21078a660300142002030f00c00381d005560320700e900b011a2051a0810401600c07240203542e031200c1d00c90103000c45da40501800003a8a070b9000c4004000d40209900b80d0280450801c581c1d80e42c2c03060300240c01000c5054801382e1480012030000210b044101c0038100851042d180030203100e14040c20419250 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 584193911 1250 584192661 584192671
    0x5040b151c24081204090c05120a0c0906050a0903020f0301090b040507050301060f03050a20270109020906071202030715050f07140a030216080a08010e01080105 71
    0x80500c00034580140c000d88001c107800401d501692019020121181c41034403800d01e240a44140b1820240d108001d21031865001005540000c11035140003081000090185101d01c14501d50f41c0c40d00d41c0301c0c40d801801140c081d0191184030312421300d004c1c1007120003040031014080008042d588089080ba000f5011a41070300216200c03000c0140c0345a00b08202d00b814285050703015529100040000380342e03800140e01139441100501030071782c208001c1c142110030941c002e410041c8030311003c03c0031032404980b941506400280c1e003007a820003000c0b0032415001e0000240c5c1c00484540042014000c0117803150f034080c410740e40340c07a25a40e8801c1081e040e4080c907200d1540c00101000b42d03000040c81002c507844101c4960040d24100541a00d0340c002084285090b1030049413140b00300179900d80d03c8070740701d0b40c00003003410990080d4050018802e0580110100e100c24581d0001c0e01901081c0d81d180e820b014198030408555aa045001000342103140a22511500c1c0c603540740003048150341805011702c91 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 584195161 1250 584193911 584193919
    0x109140402192f0a080c071d0108060601090e0c0c010e030a0306090b10050f0307020c0604030c1701052710091406070e01141b060109020a0f080603071707080f060103020a05040b 78
    0x2403941d4a601740680c0c0044112a06489511700002e410301c00d202c4003543d52030165030000003d600d404011400d00d5401091181088036200050010b80a03030001c1d1a009640320380d209032160041c0740803c1c01401c08244240d4188000302c0d04410703c1d40e054102109451081c8800d00041020006010700550000c10b4540441d40601859032665031343c1000c2c6a00000d680b044405a030901030208081354001d810954101c0c40d021000d004d803003181c0ea206243c80071000003c02040c68003540302d200e9404c643e07101400c0250101c03507000c0040810031002d080c003030081c4001c00559209241c031980c0d488206c940b80800d40150000141054010040d218070b6001c1a100d941500700d0103c4606226401078040d045000301c0940751414100c01002003034041c1400540050341e0f403203d400042e0100303200024141c05c006029080240503100801d40c0000c4510380065540c42d220000312550402900d50402c00740f1f8400c031b090000c1e1085001a5040c100d80c000e8501803a00e545410501c07060322500c0e5030709504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 584196411 1250 584195161 584195173
    0xf070501020f0d11120d06170a15050613020c06041103060708070509041e060603200712031b020a020f090f0f0402030c0d0503030f0a06050109140402192f 68
    0x7019002e08061444240c0300020380b8002605c007030007141583c021003000c00c20107a4410082c4020040902043d0b0141c201030000c081c0c0d942c0e259129050040020300b001010b54403100819110b03100d655040c0c01801c0f252406540311a0302c1760001d961011b040303505440d80003041e40254950b05001ca4014000c0c0e40c41d40e900041c40c0c2d074081083e0b0315030f807010840716007150f03641c050b201d04515180d01805500c41000c070041040c9241c03c10040a030355400825401c0c1241703010265062900070b20442d2601390303204401004910f190310080e401800301c0c0980c010300d240703010200d6044540c0450480c01c09442210590380107581003003400213200c800c55444c4400b03511440400e0360044251070300e80d440f078401000c8030701c0040c1d03140100d10080c00d0b101085031303550300110602c14130341c01070b01040380c0c441100034080082619240000381154242d10455101c40c0d81c4d0080298203485940403185e8408400010a21071044a40000d00e02c4056441d02c030105030303030400c140c108040c01c4070071418040310105c02401 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 584197661 1250 584196411 584196433
    0xe061e1503100b0f220b07080c0c100221090415090c020c09060f310b030307050c01260f04110306061e010302130f050a08060705160f0209090f070501020f 68
    0x411181e01c2c1032511944505c000090070000d1100209a038503c24144d558a4050405d200d82c54039070b50b03a450510409410200d5258a6030004050842103101c00803c2d41c4018480c0c40c04440344030315080c55806c1401c0c12241080403211300c0364a01110076040d0200090034000408981300e140081d080c0da801440751700401d11503d003c07800420412001001e60990300da90005840700f1021650b43c0e060403848003507040031900b1852140f00b9280e40701b60040d529000c031907510281c80d09820282d8034144141212140c0d40400b14078003d0103042c0c042408e07c0c2c414100080d004004040c100c4003103e11355103a4550b40b10506012403203900030b2001800d5900903104c4046007903452605024804d04165090104201c004a4002108000c10311070300d44018041c01c1c40c003444103803007294111020a92100c1c09000794154060f0880e0b0840d02019204039003501b42d85080040007080c150040e51111400c414031905d0b41002c2132604104039509c045450165480d001607031105e204015036016600440302440c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 584198911 1250 584197661 584197687
    0x15040807081513021843021603030f093f02100509061606060f12031407021503040c05012a0f020409020a08030307080a02040e061e1503100b0f 63
    0x1c0d4201c0d18446204200184c80b81c81080c1c402c0c04541e00c400009013048440d900741d01200e51b80c030b2055501d803014003421600c0c21903294460701544801000c0101544041551510844810380544465040902c400035480100c401030600718610f80700c00001032030135490a000d1110b1451100ea4090310113035a103100000150f07490742188140e2504994104400b85441c0c091801c040d401500c00d40000811505100c02a40b4074a0503810540710446086034601c042604618880350392440080700960352001440402c03100003c5028040035418003005010810041403000026280f0130390341e611503110100941c60117080d02c580411300d0390902c0718110700442e00c181a118481400640040f0f002902035000c10b00300d100d194408030380d40d0004000d20640545c8140d14a804c006403040c20340c14181411031080300c1000141403988030303501d03403d449141100d4030190071008100c0100043c80207014002d81e07550580c02143d2200c10543c2880001c5034003070341c4c10240c504400841d0440d5050a40b1283e8070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 584200161 1250 584198911 584198959
    0x50304082121091204180b010201020c10050402130207151a060a141210031a07080c16080307020304051c08041701060b1c0e0105070e1504080708151302 67
    0x64403e8054000b507101050a014000d100804400400c4101e071582540803800b01c4d0440f410542c11a40100458403032800d0001d10349041b0116500d000455445a100240140d20709a000c18070b09030000c2150703400d100b05030007d0309482c0340d00101404145403d030315808002d650034600c9548100c003440041c0d211131054240d1140c072201c1401c1c2c240f5200070707104c01900358501181c4040060315010710910420004a040421504e000c03031032414a4100088060304464004000c0b0208480129101d103104460f0480c400c200e503089501107640b420011002522940240245030003034884540030510b00fa000401004416041400301b4240750500e40808016550301007001c03410341d242c10002c1050390141d8010943c50302e03204440d590a611515802c000c2d5090400341c0b000991414041008158208942c1d842d6840121039801c0704400038150600940100e400544084c86044c402140f00200050f002d1003030480703000200350703035034a07988644104400d0170030080d08034404803501001e001c284009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 584201411 1250 584200161 584200171
    0x60114030a1d070b040501090608010503031b03070609110a05030a1505070504081b01030b030610090c03020409060815090706050a0c031e09030b091203150d050304082121 75
    0x12580b11410550409498401d00c0e82290b161a000003904201c01c2d17800c0781c0100024202424540540d40c90540040e4480c0101d0640d6500100c4445040300d16400601c11290681da00450402a203000381c20f0100302d080d00d000702c907406400205000710729403400040c1e05581d10360040034948c10001885603c40a000083c1c101414007000b400046400036042c42124581042c407810a11100b1100c000141520080c2a9040c029044081070090310352340d100c280c000780c030900c079030110b414509140110000c0c4500d40c0109031083c03421001203020400490000001032841414086548070300c0746040d102c869610448002c141d007003091040305801601208905402070404848240d5502d40440134100340c400c522000a10407081442007041d140714654000501000a08a10000c00020122444042c0c50b440c0040c2030807100341e0581c0d80c2d0007400f022180d403010580345c40da640c4200480c0c0e9072071903100070000e030b042481040035820b401c0c40039107022400410601d05c4031000394000aa4040b80a00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 584202661 1250 584201411 584201441
    0xb0d051b010e0901090f290d02060f0a03020309011d0714210a031e0507080702030a02210d030b13022d090a141807021c17060114030a 59
    0x400d03860643d600790006000b40a840c1d03020402c8070380c00806c04211203035000016040c18540020800415820100190100c010742e0208a2000e00d400000c0d118009d41002500400c000a551322601e80e054000d14080e158210080c000800078040184550400342c50040c001e40c0070070002c200e1105040c4101c020050050818050700802140384003040d0038070f500d05c000d01c0d4442c0c40e1080c2010381c015810300241180c1c100441500c02c400b000144184140b00020703110400101d502410741d82e0a21590800a500074074aa800030040b124400c1c5a41c1d401d18501c811740a1180d80b0244c00f07000b4001e13004c0f60308009041c06c140030504d110f00402900406c0b5203a41001c0000320311070b06060341585c1ca040401e10200c0d80c64441d1414000c00c40c030350b403840d004044801000c10404031540c40340303113a03041c40303840c607000401c03840e42d400001300d02e0244030900031803c1d000c095101c00e4442e9003044142101d4000007801c1c54180d0f940000644a844840480695a503001c0001480e0340703400f6031005800b000244 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 584203911 1250 584202661 584202677
    0x6060a0503060f192c070807150201110328050c0d050a0b041401081b03031603050c010510090b06070b0402100e0d05150115091232010b0d051b01 64
    0x200e2080c210380b01132400d940c5004402d0f212018440c81010700001703994140005008050800d0f44040e25000148070b41089030074401085101d660003034201c1c2113031032550558a5124642210160041c20700d10580040c201d1014000c00c0004655014042c8100c0c0c10550840ca42545101903074001c0000501d40c10815566444c143c40b03e54840c042c15031503018001c3e0700740403541043c51007424141c0c08002080c050303503c441d100c20f00c2d17100841038443d4905451000c1c04444c05e81d003400d9035648500303410a01994a00402c10038482c507104c942e1000c0c2d4405a20810040c0009801d10449200340103000d002034000c0e030001001890012440781c032101140c90448846840c410200300e0706080103c0454150f0090003144186403a079203910381c0180002000e0f0704142c9400da038094402c08a034018054100810207010707050003c910300c141405840981c4070f08190588c602c52507800900400a00d20719400c0042c1c01016181480d600d01c07409801c03402a00b00300b205030700401221428540340c181400400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 584205161 1250 584203911 584203951
    0x13180e010905150901020406020606090703090c1205010c05030f19020d1103160207180e010b06030c07030305010e101214030307020a05010e061003030f02010905010c090806060a0503060f 82
    0x80c05084555403003403000700031405843d040310a407954014805200c1da8410b10042000980c001003003a049442a105c03101e258542c000e040f00581030030321018010801000c400119191284000703142103014500030000048072010031922484169203804035800c0d0392012500890144140c070300100d144043c01441c000c40010600e0603181002c81130041e1010200400c251103201c41102ca8103040340b440980707001030902d04038a41c0000b01c01c0307258020345c2d605c141c26001d0f44401d6010500c1100000d00c0720b9113903d4009a00411a0311000044001a08200000480084020b92140138038110326200c4403082c00c00245040c041810b030b00541c0c002071194041e1240c00400d000840c018041c40d03014050360740041c1006403e60b1100300c1e00c1d03042035021604001e440118a1140800d0302e50510700810001180c1404901500c0009805000e0754078201c040810366820030700c00f03011600710f001a241c250f590b240070021955828400c050301500614001044141c1100300c0d144c0c0012003c1e08a00c101c145 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 584206411 1250 584205161 584205163
    0x1f030c0e0a0603020a03060504020705070e1005091306140c090d150203010906030c0b0702010f050a17070f020f19020d05100204030804030b0a020307121509110a0807020313180e 78
    0x15640042c0c04254001400042c403030b81409181c01a00741031300d0551403c00c0c0c99076441c0d91217105104080c64070140d0b102092080b2248a01140107001c01007000803642440360804071103c103403e4003120521714003c0307640807028213032a100788071b00038508411341045a05400e002007003800e180c048038404100380b10500c40c070000d48091030203403007096400140780741145405040041c440c1c00c5145070050910090780141e1348051010151b006a00c0c2403034a03141000c8058454141e84a080c480c0c003405e1901700030784103501a107410b000020036401c68100d803c060103441e84400390090207400f003aa11071400d0001d0300323028284c05001480b800441c1c2034202000503d10490f08550002c0320240d4001a0800500101c034081c03a402008045085103541070600c406080b0b01c20340410b5040840e00c400c0c6407003041590a9070b8034014450000e00740320014070030100e00c1a650040c441400801c2210010420a520000a80b0100301a04260b04080b50514001584d01501088160011501c480408140d518 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 584207661 1250 584206411 584206429
    0x9031b170a02040b19090207060612030e0f0f030303011502070806100906050114090409020102120703090f24140d090f02012d03050606090306010f141f030c0e 70
    0x1009401400429101d40b04000c1641c02e040b020510610103444400101030040c0318640448000010050f40c03030300c191070103001a02e5241d220b49a1880c0d50802c06045c190091140c0083d200c0840303010010401d103d08010036000b000440b950940c0c400c1c80103100240c003140400400300080c1c011642c5159490644526010b81220311302c1c40080c0e110010806d40712107018030006041c090038100c040340c814078007901090040c0102c00380f0035501d481c02002564000d000e00118107000e40c030859034410417402c001d0075a6000d4895803142541c02d05001907500317040a800c1d42040d543c4868081c3c4090003010844101903c47d09444456a00300b01c0400318061500c1404159842101c0380700d200c501500014204202c201042501c000c1c41c20850600010103a00b0034160041c40c1c1400a481c3d1103590200303115029540405030544540000031030210001191402101c0400003d4001c100c1a10300740000040c4d131600000d40e528008001080f420b020b90003940303541081e441c24504a000800000307034468 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 584208911 1250 584207661 584207699
    0xc0b0a020c1e09010602030a090e0105060a0e040603020901090e07080106030803130309150c1101020106140d050703060e06180307030509091504050f16050c060103022404090203220309031b 83
    0x6400021a61400350300031000710018081180d2b030116640c900070204005114070810300b000c225031720a0150703080daa5540414051a00035011a85541c1c60341180d01c014668600001c030300d880782030030014030f60005010300c030282ca90101d85c5500f0354540400000030320380b02c50f02c11000c0c00951135012403a402116899070354080b90341c0d030f0105d0f02c081e14100014401c40104183e41103904041d03040c4070081884200201001c001e8940c00125180b90420908041480d0801000300d030500d4a03e1302068400540b1b540030305015600c1d926200c61721544c00b07a0320b00c105000100800d2040c469140d00d407070580401c9038414000d25120300514040302c0000d0031280219aa110400722200034006025200c4603644c50f40f150b1401d01d036142c140c802c0b0107103030740d1101440000c2c031480508181c5483ca0071410b80483e44120000103a40d03c032030315408140c01075001183c42400f40d0440794030341b040c8200c0701725900802d103400d82c8030140100d0650300c482c4140d5030702c400c00211054030500f0000c1c54105010144080c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 584210161 1250 584208911 584208913
    0x203011d130b060d050a06410709050a17191509230a05010506100503150f1801060813020609040b030f0d09030c050315150f0414040c0b0a020c1e09010602 68
    0x1e0040c40d6070f00e5422035600e1002d00d1041c203103003900b023488001140b121040c0205407604007035aa50741000c807010304242d004103070081c0d600940081c0c050714800f1610020306c810020f4544881e45145281e52620030f25038003403d0844441c583c074503840b0803030b4407440c40c15008688100c00200d480342040c2203629944000c1070903074454080c1c041448420701c41c9542001c4115002810081c5020004011307000240184903108007280c603c2035a0360f1650001c0c2c11010000e8a003214244c072440d00b100c0540c000b4415140070071040c4000640400f1000120704c00365900030035040c00d1030800400e0200030701070502100e0f050310601410b2016680204044a0b0f146540e59940d07005600314505004040501d40c022802503000c0b88086090100c030000c1035900c48040ca8608521000000000315002841c03541c3c10342240c50801426849241001c48901c03480c000d01400c940c1039038841c0d030700b5040d00c6820280d00050b08980c070100c0042c504808800c4000d07210343c0485046280d0440010304940c020f911080c05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 584211411 1250 584210161 584210171
    0x10603120c050c1e011b05190303063f1401061406030f012108040312022104120f020402120601080c04080a020f04140108010203011d130b060d050a06 66
    0x3004810082c003500e4800c00da40072580302000a030440b904901800c4c01c54107010030740201e03004098400c10740c203003140e0308482210401d0b80c45528001010800703401c2600042c3c01d100e00071415100500b003108504507011007059800d03c0110a1003844003030030720328541e4a07003c8040c48002c518170100c5580100740c1d81c800040c13910304d080084525420128031842c018102801040300c914104d0800c241180c116400d180d2104040d0441c83c046140b6040004000030f0000c103002c0140008020100c485020903003c0742c0c820210480000170410031440035070304642c2c08000c140806058541e41040141c4a000c0e240b4000c40c450740003406031b030848802401e80d101040100007440d13a03c0400395802c0910b880e403c82c90582030400003922900c0c0080041d0142420640202e590340f280c0d48003800d0394420720156440c03540c4078007a040c040e41c02803107420301d042110303001440c00b900c01d51106d50041c03100c80183c002503406544c07611003203e03000780410360180d5204100c1001c51000c1c092504803074070603680012 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 584212661 1250 584211411 584211413
    0xc03020c12091905090f0402061608045d060e0606010c1a070c05010921051201091805151e07020a0308040c1a091011060a02090102010603120c 63
    0x1003c440c0381c412202c0a140944200515201e466401c0c0d04242084445801a0307142d002007400c912404503019036000d04928030f18240203544001d0400d403074070f41030039201080050410601c081640d092031220070784204112000d4005100b404240385504403101030300480c43c0c05908104040521068034007d446000c000d07040c0c0c0b011b01846521007800d00741007000480c152503000c02100c81000fa9210b211245002c0b86184e4041c000a18810354040024002c048080c03a020b00c0d010740100c4500040b004c0605030403200c6028a041c1e451794134411502c202180c1c030304071404020b05032014211150344190420040801c60502114808440315004203c0d0f80c2003103004d81c40103ca8a0b880c03048030302c00403002d03c10181d501084270008290185810050b584071401c02c0c030444010f650140e402c20050022600000402d08054084564111038520b40c07005038000954800325001d05007021030700503000058100c140c075806000009410300c0005002500c0b035a4901711070302c90160042c007095903c542c40e8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 584213911 1250 584212661 584212669
    0xe13052a07050c2706130509010c0e040b010e010c17040308031902190302090a0509070e0f06032208120f1807050a06031d120304020111011b030c03020c1209 69
    0x70010070a40f64101d1121804c4202081c3e41d80c003404003481c003101d22000c5145591420f140f00d5400320000c00810079818807445450080512150880105048d000166a146428410644c0860040e101c25001d040600c004548003175080008440b1040c00c0340240c40b6050010000d4000f4610695000ea903d00b4130303910500480000d01e1b00d080030700b401040f2100c1d5980391060100810111401d0150b01c4131981000503200e40c0407900201d411070314890400c40a1a403084070450f01c0e0038151001c11200c04000c040c451184001c480d1560100e040042024141c403100c14698901c50107450b400381080042c480d46881700b00107644d80901c00e624401800315140d8000042c0070100c0b1200f0061101d00e1070540813802e80612071055606040e034a80b003101151035480b180f401c00382c00d158180e54040180c8806061940c0050300c01b6400604110040310040c0d00c14420108040c000543e4492071002e080d80c1240503150007a450420036400380100003101c2c43c204003016a01d0300b5210341d103032200c10601c188 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 584215161 1250 584213911 584213923
    0x30609050706090b030103030c08090409060f150b04080a120212030406150618060e030f010e0307030e030303010b0d0b04060e07110d050a0801050613030c030602040302040c0e13052a0705 82
    0x50312250101700300400009800c0704041e14516441000700e51140d049200040c003c100c203d0014140a080003250700d110030180d8046030240c50700d0784143c46500d07220341c02101e080c06140682800c640c018160b0001280c00384040c0d030302c408010710448a0503c2d107542c1e8013500743c10540f000c65509407521521483c00d150b035540480a80b03021305e064040c0e140c492052190a0b83c013072280c4400e20082008013115502c2c184910904403c44100070b00c4400e00e0503c8403036030390b48501d1040d00012000e500d070341198a004400c590481d01840e8085040c95115013000c030007066685203007a4050390790300c4005406294030321306170302c01c50468407000740c2561b41d00c0402d0300744520303c000c003020000c0c20081e111105800032092415590305071502e5481e1240004d11800085254001038640079004c90004100031258000700305803032081d2000d015101c03034030205642101c003102a4980c070010702c581c0864084255401180d120200b410340d0b1180303a0030104140b5201da00024881806900000c007103003401402c0201c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 584216411 1250 584215161 584215169
    0xb040b0702030c100f200106080f010b040902011d012f1c02070308070213020c03030a060803040612230a0b120705032e02130303081b1606020403060905070609 70
    0x4200c100c54500c0308000c109a0900c20045c040c80940c1a0300e522144540948940904d0b604000b0000325842e0502c45541d504458040c004a40c2400100507042c20b042c01030741e1141d90306840e20740304440000c88500340c0c800181340c1d09040000213445086822540c4c4103801510350481070107801d694440110380d090118003c060000c040000f07103020b042030790001e80a802c0300c2d004103201d038803203c151000600100510f02042d00b4203002140c0903803d00d002100442c0105002c50040116640c5e0301c65664a030300a51080d00c0208003034003492800d80010380c1040015014040311071f1841008210440c10b000c0056903c9074000d42d444121080314100081c01c40c0111660314010440d06240038006070380d641681d010f040850f900c0d150001856421807007e1146051422029034a0f400e0b102d04c000700340c40240c8416070015002401061260503d070700c03d1040305080105903441c10100e034a005a611090420440e070003a170070040000454024030410300c4183c458005041c0451408500408415007600 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 584217661 1250 584216411 584216419
    0xa080909070905130902060c060f0702060f15060c010b04050a06090b150304031b0609030806040c18060f170408031503062211060d050405160b070b0a060b040b0702030c 74
    0x40c0c01d1009980f5444088a1040112004545c084940c40491203030302941c0d100c940b03035114007001e00c40c400c008404458442c07685035003101d14039500e90030303814411002070310515041482580705003143c0c01c12000421194458070000700318110950007203821500c0465049154aa45800c1405103e0840c042e6a054442c05c4428188030340e41050b001b5080d11010300000d040c488002e4800c0309040c0141510034856400040420898449040c0a443c51a044072481d10503482c0c922400740cd58000c414032a559450900405200390808000b40e41c144500c4000b0380a02070294003c40c507510008201d140708521031268151a030404800c1140038080340390146102e40c0140c0b04201c2040703aa128499003011400a04001d12041c0e41410074842c0c6800280a404c018005205032441c01c0c1c5030001402148070714100d84000c002460205080c582d1801200003100b001c00041e0046101100a140c200d0703100c40002440554420b40b54445500c20b500559841c1030100300002580307400d2100301d1494a06075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 584218911 1250 584217661 584217677
    0xf060105040e011a0405100806040b040b0f091b5b2102030c0c0f010e10090c050a08070e0108030901050f0703090e1005031c08010b16050a08090907 65
    0x501d0111300500304010b0151369224000380350f81c40314620700b03001400355400b56445410b15040c00c1d06040d9040f181914a40700103c0451002244450324510520b00c82029214600d0070340f07200e008207141c2120b000d500041c0b03074002d6084203010800d8040340301124105019030085c91030085120038404501c0358600c94000784041c883c0516120314008000036440c007400740080d90032a81401c0440545155890340c0301004000c0b4500e1000000e201851020007159070469201a0072400c0e208140380a8800350416403806580d5070325604106e2070280b140703210204498459012031442c10b01035011026603401044100642c000c0c60741105d01601ca00806503240c41a0000060034501c81c0e0060709040142c001541003d0600c54a106400b0700f070248860304031410b000b400c50014a10500655200e405040e0f50141e1500c0ccc95a00d020030041076480e4041203a180c42901d0b0b8051b00300180085c54001c01111f240b000035010300c0110021031169414645505a0406020758588003d00d01e600b44110a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 584220161 1250 584218911 584218931
    0xc04020c011e021e2113020f04060302130f180305120705090904030c050c180a0c050301051c1e06050415020306011d0114070c03120807050405040c0c050f060105040e01 74
    0x35844c08241c0501380d2a260b0740c840705d08005801c1c2c1d071607114130480034080800a2181c00400e0403003080e90303e4000c64405580401c10b030100402c170750991000039800303801e481a04003103400d40e4000403c152032960f4001551901300e100c400b07005040c0b00c4200c001032000108801c849031480081608441586441c0d818010154040f50000c00003a00c003030300b40882000180104002044419140800603000307105070000b0a0640301040d2090b03a403002c2482c10800458a800e1044066134100d03200200b0a0264801c803d01c810340c1c03c107403180140c9004c4024050180f450701d80c00e2640e04601c0c810100060a840c0600306041c0301c2c1d00c1c10090700031030303030041060080ca60791191800c1003032002e884100300700e0342d640001600e003a001051400304400d4089011010b2001c130022031802c0720700a03a01421005035192007129283e4046070381c980400c0d41400305200609050744494040301c4203003048130b0300742d90135141c05103062005e01800b40546d002c18014007441c00c0500481c507040c1c4ac660300a002c81004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 584221411 1250 584220161 584220187
    0x13150e06340b0c07020607060f1a040207050a021e0315062b15022703100b09010b03040203070512030a0906020609030f2203051b0d0b070c02030c04020c011e02 70
    0x102070001c0c1411940030038044c0c1959200411200d410394441000c01c110b80070003800700040d0694003520303444c10044c03080320f42d0705040c580216601140d0280160421240fa45d08001242d103032501414201c1e02a025114a1078070301300710f680e840c0500090320320506d242c80c83c1009403d84055040b00b0901c4a80d0715001041c003844501003040650000d00f482c0f810081d450301d0002070007400400c0041c0031841050100c003c0b40c009100340380c084181e040e105d101c11103804400c15110144803150b00040540c00400c0083c00170405140c020b0310050a41d0701c143c0e40c540c00504142644d60311600190800508003452540041b940700040910307002810740c0b0b20742003880310386034001d90995502c80c04000440f2a00c08806500782e0308001842450700d0700a603100e0424650321845004110078100429040015610344174070405146a40141203118a0b40c1e600011200202d41e0703102281c061140d089401780c01d941d07d001800b0180910000003481075082404020101071140700c40101d00d10400c080311119034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 584222661 1250 584221411 584221433
    0xf030a061203080a09031701060f1e0c12030612060f0c0309110402071118010608090c0303090d0602070f05010e01181208060d0b0106021507030213150e0634 69
    0x7002d913600140d090320764217098070b5141844881c01e0420418900104050317402c80d004142940c2070b6500d4101455a095101904111580c40c50020901e00c0071305000080403401200b21030301c01840c0101e030b45a03507245a20058458085c08031b80150301c82082540f0056035124041e0124661f01d03044c024003407030b61100420710317021302000d5000b41e800050503010303c1110780b54022050006008007042034074100310030182440c20301440780025030000206200c1d0600040150380d00384002d0141d454060100200001612100b0044620036001d011010101e4464003402e0007450145c0c0012480c42c2594000354212000c02c08d07060000c104003616500420016030031404100d42e41d09041d00c2d40d40300d040c0040d100c001d401d60000c0051103a01e00214200d0b9010402c1e4014410300c545910b441d44520a0550503401010030381000302403204010000405030075016042c144581c10b2108941c1180000701d01c190303000c090759070303601c03040351106811008251842e2450280303802c486481401c89a62007001b182c2c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 584223911 1250 584222661 584222671
    0x5070e0301091709060403020a15020607172805040f03090816030b060d0203061311090105180c0c1519020f040e04151a011202040f0b03040809060f030a06120308 71
    0x1440484d102d1255112182124003854006000c654229034894611540c5000c201220006000340d00c04540c00c1c9002c1c0d8080e00c0c8082c8282c1000c504c541d24542c28120300300380d03d031203540c001000361450300c2846500c2c85094000e60080c40c81501c180602e06000e03110f00c00755400000140d018103139801001c40b40c071028a0542c0d40c00090000380743c81d6000001c1010444200107541401064240000001d1160641004a100e01440040071000030304100314481c00744156600480800d200e18044120300010b140c3c0891021b180508000001280350704c0c240240403007500b14825803081c801071945142420203001c04a90080d4038003409c08030105402c1c021841101a8162028081020440380e07080301701402c0712410003000014402507000d20b04400e00f03260140030484c03550345110440c94034022101920040c03110b80401d646080c000c403506500040007035803030070003d02c800f9010780d65803401440300348103e6030324035240c0c14038000050403680c3d66401526604281c1340100c00090b041400701c4d80c86 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 584225161 1250 584223911 584223953
    0x210a060b0303070c1d0c031501050a0207180606020105090105040c1502010209090f0103030e030a0533040b0709080a1709060d0e1f09200d060f05070e030109 69
    0x81110001203461401000d100402030b0b01940c102081c5003840d011480e1017a180c07078441c01c0803038071030f109007650314403099076a1840c0d144001d440d6070303d95005800903d00c20704d10341b0486520554541c0d403c1e8111042d00b11a4107116201c40301040358507030901030203400105440003000f050410781d0700c4c00c8001d640391141c4a0851046582c00805500039070545a18250251445c0e40510307018119070042c0702d0902044000c00e41c0340c04000300508001860461455005009021a40754560003c41c0f2038803e4121000c1d02500c4e00c120403002941e10b00160003a84a03000e0740c085400c00103005000c10070740750410315299011403000030101d162616045440c0c4420482c142d0344001c80408644a0300c1140500341105003070603201071480400180081c450180000c03120070000a240d5202c095513104540901089030f681c402428410012420b02d401000090600b44d8a00350395075800c003912410401403214907a1a820004c0160300003182d4882190110001c00844030f0555135090b010b070915001c9000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 584226411 1250 584225161 584225171
    0x8091501051c08250303060806060a091107050a110a0e0c0d02030c2803151818050d03150b04031a0601090503010906051803070209010902030907030b15210a06 70
    0x5010114046540b40b04403d268402903130801c000a0207140c0c0309510440002e45071903000901050301140700e038001c280080409094502d40514840500500408080e01d00401c110000008030200800500d145c820312014404105040400005104c05e07848091400c19180c10810483c82e8881294240c1c6600d4400685a031101000350b4194000c1000801051040412250101d00c000f42e0b01c424101c0a59000c0c0704111b150340542d4811046072107082d10340540207034405d860003081e40110100a00d181c034504440c5505480d002e182683c0032007e540803940c0c9151f0104140c0860350060054885e00610b2803a20340386a4851007040c01c64640300e4001e0090001049540e03200313004480041400400a01850559007000c42c020700b0b05541d034156603440b0355011000c4010110548107004d800803d5228140c3c645101c0310301035400140480c0e400c0c0200003010002a18880a080c041c002c1d548850304001802c1041c094102c1c803640c00184210003180429580500c0060100400b642c07003540818 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 584227661 1250 584226411 584226413
    0x501110303181e010f0b030304140105070204240608060d020603060108130b07050a0e0f01210906060906140405040b061908100203060114090a03030c021305040308091501051c 77
    0x81400003a0b03000f45110780d00f0040c07195002e581500109240040301e441000301c0740e03825041541e0f030b1156100e0b020443d400000010003d60040003e061161700150010803240d505581d040c0122164410210b00306c8201c4506016456000501561209054440a05000e4143c00040300780c000107218604000b00c620020ba4407100444c130340c100c0b4690001c1c14401d98280001c0c00f408903044051142c2c00207890440c03a02070780c9468004000441c0d03060311203210003c20340c0702501040c0454440a103810341c0356603800c80080c01c9071107020010404a00e00203161401c006a11000c0540c03211000e2190381000213000c00f003084c002d4440c2d04034000711f444007940d18051581c581701c0c00c00e56000b42a54082c1c1015165911120740065226100c242d891080e2021062040b40f5640034902c4580d8204130214028000a4003400d014440e10380000c0620300610b1742001c06006880d400c803402c0700080c244905000b244102008802058029401840c503598140000b0603102d04001b40142061014081160 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 584228911 1250 584227661 584227663
    0x12080f07050f0a0501060501020d080f07030b01021e010b09010e0f060915130504050c03060c191e09031b1d070e10081f0e04170f16050106050111030318 67
    0x78112442c50a80e220107a15042a070f0082c1014840c1e0f038094000d582d031014600d485080360500c50720168600301015120403101302c0041543d02002815449044030f0460342c200014581e9140e03001220000c10f203603d140050110f00d40c410703448851003140c036078180b00e0008940b080080c2c3c88403003510442d400c0e81e201c04c200e04804000d60799903604910204145428502c064004074803403801a000c0b0341345102c400741450b0351502c086620791404001440800340e42d010201b10340d810b1401a1a22101040160004034000c0d00300030031090205507150703000c00402c14840ea26408d441040f10a801a25203409203250901da8200c0d10140714141b12400140d40d01d0186817140141c030130240080035001454bc1001e03141040503a600c880908506811013540300101a038001230342d081c5501d0030615100c9589410b02040f503910440340b884d1091201c03960800785500589620000c0034046504c0769210f0815908454a03908298104200c4038000301d00c620b0300204480c0c00503a01c82e11a150086014049 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 584230161 1250 584228911 584228923
    0x11d0c010e0411040b0d060b03310605090303070f030209060904050a09050a0302031b010507270e0a020901120e1f140c1207030b090703110c0d0306030c12080f0705 72
    0x1500d07800d401324004c0307025030320030002d040319048510341080ba03903407a0210031149020845007409803030a1503d218800310810f10306140001104103c680340c0840c0c568030201a80d000302c40300342c1c0b980c1c408000c000e1074680c070402031f0014000320700f41189000d0003140841d805124211200d0b01075910384001c203411011507400302c41825003000c10703203003070208602d4001d49992260038542c00440b000340e10b075480000e043c804c03140903030020348038040e00704aa404285002d60011240c41c1d00001081c80c0041c825460800d504d02c03c2c04c00e0b00c001662514110300141904210208100c02c2038030f8044003010503980000c4c240c5401c890744401c2600e902e445140000500707101c10b440465071a14006000c0d0100050014111440c1034070210100d541d69900e00314101c070760419010303521103502408185e44c1402584901c1d0907024154009141041c000d10043c0340c603920000a01c006682c8840800501c04802c84520103030200c030350070000084031519140c03c0780c09282000f601d2624006101e004000d010094 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 584231411 1250 584230161 584230181
    0x120c11030f030f010603110901030c1101092301051b03091903031e0c020705010818120325020303012124060b04180c02010e0a080408011d0c010e04 65
    0x1101d5507118040d2040c452074005071400801044000004650a4028041e40d64207540d20201e03113040058250045001d000920f034200d05124980c3d41106200f50300f8080c010300640901600340c1003920107410409240590407502c60107074503040500c407190b0390b002138451408545400054494644002c0b031810800c192591545801243c2080303020150190401440d00d804a19540080030400440740c0c00d58108500350300060300310400078804c5600804095400820244094841c40158000b0b546041464502c2c41c090710004400c000b07491117003d91800d518400800c001d07040c2c001d5080082e5490206025502680d500c440042044070344021003080c03d03e070850a42d00c2440c00360820741191001038541203416600b00300010980c010354104640880d4804030002c401d29030243c1d422001401d400d0015821035480e0807040300401c030200800614540a01d00c050350740c51034a41c0031400c440601e8a1a01100e4006440d0703100c24201003801c10603a442130030400f4040700311900040080c2450b0701 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 584232661 1250 584231411 584231413
    0x1505030607030e070f050d0f03030b060a030e0609010216140102070c06030506120309031b03070905040317070e0a0314010b0901092310031e0807030e011806120c11 72
    0x81000055040c0c004144000c03d80050301e121300d44501d00d40c0b81d6079910340a80c40d00602640c84200c00103440c01c491048aa00038070303000030300400c1310340045c078194050b5110b6400651544528000c040d401d103c0740d0341140e98240214079207e80c4800700b4480034a0600040c1c400c070b0a001d1044403050082d012074030742551080300d051103940c5030f850150003001d056030001c0c0102080800c02416000c00001c545041c0710040091011007402414400801c680c840426018080c110000402150b00e0090324000c0c0e02c65142c05001d00000195400440402480300b806c10004481c1103000e038440c040300c072040e00e8004002426074011110742d1809000c202422607001081c1e800001344c10340300ca9000e44c07298056501d42950500c130710100400c0c1d800050b20220815509080e0410006180009045800d203401c07400703841246c0c0329110400c5a401c04201030b80032402c5e00804148643c0e01c20301c820445802800c2c06110310303040440091041031014480300002c2c1d42c42c540b221403a4018081e0111100c01c43c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 584233911 1250 584232661 584232673
    0xf010806010b03090115090608190803010b0a170403050a0809010203070c0602090d050703050d110105090304121b06090f091b0e031603080d06050109060e04331403010b090109150503 80
    0x14100d0000c252340d01c5060080c2c080e21034008002420f0401d00044550000c001070b0440c0d08000d015040c03580507050000c140500000e02400c0c481c8c1600a042c402e5029444054445e40b1241c030180c0120301c001c0005249034410410800d8440d00300c2c0d451800c158021030010380b00c1d20204081010004900740250003803140b01800002c0050010303000c5401203c955a400c00f000c0c90300802800d996055800e6400c50700140f20900c00d040c041f24284c01c010f405034090301103c000b8a641102c0d00e552076000480000c50504003880180c140c824204028141ca80e81007080030400500a02034426043d44030b02004402040709a540da41007029015480c1c0e15480303070600503507900d40480c19501031003d420020b401c0400008141d8090040307042254580c0c0c1b1800035100b504420080146030340a2070710141150240c0030080e1010000740f0002d5441070304101140075041400e1084c8680c8180741c00740c4240c1c14100c40ea0381503224240d5481c1100c0f808132010440b80b1180c1100d004034241a00501d42521581d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 584235161 1250 584233911 584233919
    0xc080c07061206060e132901021218041a18190603030f05031911090301050114010e040b03010f0207030816020c18190204060207030b0f010806010b03090115 69
    0x46480340031660540c4401e010031440714800310039514076102e6440072622030b0140d8000c40c100044a014880310000c00060803200305d8625100d84e091035054500c0340d8020403e00300303555804000b94941e078182000b401d42401c8000e002d13588030070441c4461600461b1185011709901002e4541e010011100505aa40030301c0d5a50f401803070480c0c01c494a80801004145480d1a11428806c0b542aa505175071200c41c0303100804c0c002c0ea0164001342c02c01c00c0c92407603880503050300342d0b80380300d40302c132070700c001c4075220341d00c034a0700041609465044e00503a0240c50070402040c2c0c01ea8008480e054184004e5402148041d6001c000900400a00b64a0a81c50b400040c0300c808041d8042d088901c50b4001c00400d40520b048003004030fa0741c00d0180c0509400000c5501d50b02d04580304820762a5001c5c002c2c46041c1644542d05440c00181c1e007040e4030410140c0d200c6a000c2c02001003c090b115802409010122030703562612801c00e542d0341040c03064091010000000c6550000290012030408034250700e0a0f034180d5071 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 584236411 1250 584235161 584235163
    0x909050c0d0506061810050405152a07090b040209030d0c1b0e0f060409021206160219110102030f13060e10020c041d01050906060102070b0408100c0c080c 68
    0x141000402240340c180081c8582c541881176407800c0c481c500410642c0c00e14070703050000803c18a210503003408024000011995070f15007413580791010040d21a40c84000d000800341c54100400d0104040031641c00500d90000380c000398a030202c40da84500803d0072003607400410002d1007806060754050003245203030040349400c80c5a0200442c45198000c0c50001083c240e0f00c480c2d502400f840d0710074020000811485280981603a4200314010000501c0c16290350029413034a00440344880550040800c00c40e9004011681002c2240d0900180078030703001440a0202904850200030720158441c020120710703134403c006660000c1c0c1003840d11959004040998108101144140340010b50307070000411090400004030000d040701c07600146041c401402c104000350041142000032450324508450b0030410901401e4010190000a03000c1401c10000090600e07149070400c000700e16007000108801c03040002c070004544140c010000c0c201c0315050045805004084001e481075801003014820820 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 584237661 1250 584236411 584236417
    0x13110616053004140405060406080609062d0f04110603010305030d29090c1c09060c090e0c0a03090f0b24030d11010e06100e060307030b160909050c 65
    0x101448150100b1850746000010a104601508881140b034458280e618105030b00300d107412500003000411400d1f02c3d0480c80f031610500300c0d44014640d000c1028850b000e00079105400b401c01003a0f0340e1800d00c01001d400d130104060090811000f6580041c001028009003152401089400078903d60b030300d503500c0c10495500d030070948822042c1c510b001110358121000b08502041808466080c14462070074004014410500401f01450000100403040d21030310b802030a4061343e00c4024001440403400d080c031a0840f1503540074401070000c840e03414001e401206540079032103210501502d03a6403494038000c84c0034000d40007000746810b01003124a4100218501424481d08482003400208000042502482c1622924813901500089096000c20f407003000082d5404d44500d0004c6040b103c29800130346010400c8134012080d110119040c06102701d02440703035070070003412001007200c64219140c0c130b41d00520240c003d501d01c17126050340441740782c000c02a11008203c1c01008000500e8200395101c0385034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 584238911 1250 584237661 584237713
    0xe12030a2d0f090803010f090609052509051c1b14012f0d17060913151409010e010216111908151311061605 48
    0x14204000c41c4851000d4007901c01640c4071180900460040325580c80c0020541d02d007405618503212060341000c01e0480008600030322501c0c6603648540d26140420080f1040703904203146841c2040b05100ca403c045910002c6818411540c5001d0204a140c05032100002c0703602c0540c0261181c2a500311400c031607031481c25403a000c0c1c0082000740324441b015a600c9070003802149500001a0002d50722075100d1103003160298040e080d640d40380c8a019080001305d06c00c1c075008002d590321001c3c3c1c04d400300d030344000004194407031200103101c035082c0080012100d19000340341000c2200c1c1d009551040c00918103210369200c0c110b034010481040c54002a045004044981040541c200703921440442014400c0341c00c00d90300054500c3c02d000741503032100c00d49080c90403010351107210342441291201500c0c192000800e0298010110b0401e09504100e103810010540a49052003240402c0070410200542010f00e81c1111101da440d8440196001d80600c1c0302000740040c807507001e80c0e0340141c0c442c52902c020781c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 584240161 1250 584238911 584238931
    0x910140f0a05040f060c03022206021c051c0b060c07030b060607051c0309050706050904060b040e0a0b1512150402071e02042013050405011d0a0e1203 66
    0x980c1c0d50416030819201d003a180100584403c403014000302e075042d07008800341c06181c50017520703003a084105007801007200000a5030007080c0450800c00560100291585111619001505c42c0b05c2c81001030410f01130203144210301041800c044000003000e501c0300440503401482a91180050580300742d0703805040c081100e50007180000f1a40500c0c2c0b031410f59400343d0b440002840b4543e5804010860000b02c43d170401c0c24561200d01c260005201030000c40c01070b050554038980c031800300604100940c0c1480d0320000450500f000b0611901107483c02e562780c0814000004115040d007100030a44031011482c140415010205800040e03402d8142103d0080300d24540f41c01080d551401000200d2086980048ca00c074001d0b201714154000c566507000d071241c0018400203410a100c50b8154490068183c004660070000807018140c1c80306002280280c14281d9081009606009810001d2070b2800d1004c000c282941001840c401c282c1e401c080000507800081d9840b510511485440ca0f42083d02c0881c45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 584241411 1250 584240161 584240191
    0x1205030609091f0b0406050a03050f15040818010c061b170906061017040b06041a0a05061e04060915020d0206131a07050408280b091014 60
    0x9810340010f00302d40c1d54031403900e03070282c82200400100d008104401d1413640003600c8605c0040c240c0e99031a5040021401840030b05141100c4c0d083c070600380001e681410048503174400500012414031420b407031046100451611800c96040010307507407188044030090109040c402c420b403041c00c4203449c000c110f40c0d1640b1660070b2940d42e0b603182d07008110100d80080e92030380303d10b00060952400010b0b40d41c3c01c1e0b00d0784c00c024403000c0c0b014081c40003002040310160707104440c600a0060f82d092610480000d160305c05845520790015500048078003070288211441510040345803140c42c182c00e04e0354800316018a0b040c940e00d964030f4202a0209030381e80300e01c2e00d8100130499440e142c0c900101d40d6540d4105554040c1030f00350744540b18000e040110341c00036a40f010b02a684d810300741850364020740c000c18548e140ea6460f00c2c0303005065031401440020b00300c01c640409201f4070680080810313407420707035a0062040601c0c2c8d83c0e221440d03103003210380005000c449003012121401d408090007102d01440c150750030150 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 584242661 1250 584241411 584241421
    0x30405190821010302151e0a02070501110c010807120b21070b031302010f11010c02160f0803190e09010e04060b0f0102060a0b0f0411030604230a0e07031205030609 72
    0xb0445000d10020303400c0742d000c420103150340095100800058030780030074003003030612110b00d4202c580d040404054003503071007210188440e40c1c201e1909907010705580002c200c60400600001e00030000036064030180203a840d648510f42d5210b420000818a001d0503949100407a0b03c00070b541215000b03520032850142d5400840c0724802a8200c03441050a1003286400c0300469004407010808400500200200a00e000324900000c0c042d03015450710a0740101603980490b0500c10b041c0c11a98450008100241d008100c541808820346e4107114460b0f0620070f12040141c01581c108035010300301644000028004540442c140301c1041c0030b01d00500d810410903007a0410b01030500300c609005405644050002040d0b150184c122400b410000792a210083c1e0140001c281a11039074502907410060201c00c11509040c284505101d12206c4002040c41c0a400c0030116001d44020b4a02d03080d0584600f5041249c81c42041014001d41d8407000c2800c800d0050100203016170010f84280b4426250140410 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 584243911 1250 584242661 584242717
    0x30612150509010506010c110d240605030d0e2403180c0f0a211502340201050f040305160503010c0f210603021810080f0c060304051908 60
    0x380c071484041e101e03002c2d40c07801600e4180c0401429008070b54045000111100040c0d8680d90f00c06242a030360f00884407105003601e02b1000d403011604072074000c0d84420b00b00d01c219540700c040fa00703070f0040c15540d4058001d11b07658104031b0700d0300140210500e26800400d011000b80c0d208281141040e8110544d030300c070200141007010000721203005551040c800c0d09c060124500c40304803a0b00307480501c0c00034500314000b5552030f42500c0c0c480314001415a80461011404071011000303c014052004203000803171441c00740380003000761014019040003000b180e0a044900c12104440207550070074211128202c4407c60205500300078001e84d4025400c008225200c0360207080d02e600140c0d00d079190f15008001e1005078510200703540140c040c00340d0322504000050307101d000b12000402d000d4480c148062906650b00d55151180781e110402c66404200b0006242c1001708040c040c40501b2100c0136500d0b1250f007805807030601890002241c80d441c0024201c204031588008020601071103186800d03120a180d01c02c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 584245161 1250 584243911 584243921
    0x408120403030203040e07020102160302010204050a050d0c12080c03040f0f061d0f0420032205030f030406061d070306090e030f16050709091e02030d080703061215050901 75
    0x4015920501080c45500700e100040781d40031f13003039200060402442e400e03540d5803540b900c003050700581d50000c0e0511080c28168900c0c1e001e0103058915090b0014503544000904103a48207440c2c1c40628040c40070100202c0f202110b000d12004801c070f0f51038689840c03217102942d410344144060300a48860015025004504e0f001c0f10b60f140c021244400300d040000c3c00021400c05107504c1e80070f95284040c50854607014441d1300c0821101d20f107e500ca02e803c028030002c0c00228001c0700c0140701030040711800100c001007115510f42d10640f00a4580c0c0b034901d4280094504c9800c4000650480b07101ca0380500d00c012111442804150390900519a4501d800c00841d10b90080f1814160010030641180c8119000144807140c0000b60300c02d07086001c0e0f102c060402a10707420110446880780300c0c01c3c05104c001404003c11a805c01c070700400c408400c0c3c1c0020340c1e0f181c40418907000e02c000d00000440d01c50285d40400b0041c840d80008489442c020318110452200103041b0440862030b100c04103030b0b445014498 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 584246411 1250 584245161 584245163
    0x90627170c0307170a060c09080a03050309060622020703050d0c080603060f152101181403180f0d0203010e0102070302010e0604080f07140a1a06090c03010902090a0b030702030408120403 82
    0x103030103005c601d62513440143c002d104513141801417450000403500810000a0031030b5000b540c4890b00d07820190041810032402030841c0d4421b00548105100d0182030101d0a45628241c03840141e683d40c040c54240c489010304401404190712b050641812550410b03000b503c200b108400b698420ba80c0c42d24458094002542c804001800c004a0840c0da030400000f810b9200140c425000403c0740b0580450382541c2003500d0f07810040b02d041d4145000c2161001c0e00c42400c404642c0a18100701100c104c04c1008100640301606c2a100040000070b0381e00c4500d50b140c40315401078024840c1c440100d0f40f080c088d5014a030220015842d16045841c5c0340004a40e00b4080d80e40058107526021203c08640d442c0d4004d66025150303201c034200700880380e00c0100068000e0a1150805119088005084070180c00008104c00e0051a05008200c0759405100c02ca07030546805180058071480f09401142c880c08094018411502c030000502c01001e800001806c125507104080341c1060240203218981405917107c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 584247661 1250 584246411 584246413
    0x3060903032708030a0f09082206050301060e3102090a09021606020a0203120f0103140303070e2103071a100e060d140a14060601090627170c030717 65
    0x1011454480e900e4102d030b407080982090200301c640154440704002c0c1e0002400700038402c1518081c034450305149c0c03014402400303907003001419585000710207031000044c4002c01e4462180115041100740c40b030515204244ca1004620600401801b403c2d00250300040740b842c480c400c0c1c1440000c000c0590b00071100c2034604000c6040c000212644c0b58000b94004141d010154001449040391552084500510ae10306211901015515600b404815070401000c103400703d0b0820420081c0c959004104016540ca003a15002201000d0000c10b4001103601841c14400b1302001410505211080c181e286440700d8446081e20591100c5000c03415050140c4a1580700c01c25110015400d0f21b803000615106a01903481d40701c540e800100001d04060006804132407191750180e042c07082800400c081c41c0d10030420f090403203d050412001900b03048600c1e61113132000080401a030b001c50740032400e038002400b031540303034050030b1120416507034944800c02c6819000b0f02c1003000005004100b08038510324242410 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 584248911 1250 584247661 584247667
    0x61f21020f041206020405060c060103030305240f1906030203010311090702060a0b0316060c06060e130f171c1a0f09070c050d030c02010b0603010f0b1303060903032708 74
    0x3254400303c4107240041a110a41d0134400010715403508801052030141550292403036605501c5d014040b948050034a07036603005200f540c00d89a14600b02d510b03480b1202214103c3c3c14a42a10010302040f50110780d40e440c0b60090040010380c280c06401a5040c0c91083c41c003d24104184020301c5005041140c03a200103a0119000c501c00d8042030b0b10246c1103800c040e00303665108900c401c0410340c8101e243d000c0030008145100c040144a05807281001030300d51101d908089007041c00c910940358005500180000441201c140c00704080e0080510b0801050010380391030b4103221003280c40c140100f2040d10507940c20700941b085503400e548880c442030940106502d90f1605010309014002070300030242e100703202d030050040b03010540410056802092903500401e0482480200074250385002596a024840500060110f07200d83e1196405840c1502540741e1202800011081220015070024080341d162802e10028140e00d0f80045a40301c0d01c41c01c2e408100140340200d400d01070403541d009400c8220034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 584250161 1250 584248911 584248919
    0xe0a02271f030804030c0512010b100e03031204080304030f0e06040902070305120f0907050307150e18040507031e15020c01020409020f0a080115020309010305061f21020f04 76
    0x70712441141c103104240805200d60310b075900d492195100341c01c01d82d03903800059000c0140e031400404c0c0006c9100342000038440600004013061142040889001c03e121000481e2140c9440800a4500749109041040c1c49411b1034181004541d105407010340000c0c850019800b5003502440c14559071040240c4014a82803034024420002d40004d041241048001c100305410f00c0b0440010701d010b008404c004240900308076051510342212680020302036000403404000d4040c048402c00a08500da0030030300c00c004803090001e4480658001038805048003c0c06000611900003056019248200706040394106800c1c0d90106da50b0450a00501071001400c040e600b903c400e4014140c801e0340c12001500740707a214a655826a00100310080c4c0e1800b02040c02c001c0c0c6c0d50f00c00080307401006501041c2000420f0808000d449100304507440b8140340d2203401148040c0c445802552114844107204c400704842e000000784400ae2421072800314000c0c01c0c0442c00c01426910854105050401307d40b45454a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 584251411 1250 584250161 584250181
    0x20d2f090103110d0b0a050a0e270a120210090510090809040f0b040501050904020913030c02060d0f0606080c04030303050c0408120301210c060518040e0a0227 70
    0x4030160507410191036804140d01604040003410b80301d80d03080710201e45e0050860a0050444e0f03d544411300c00c0d44040020840c0c5110080a1900702d500150686050b008004c580b5601c5c6c20211044021885115000001d0050b03405681d104a00540e00b510003803000c42d04c0341c006681c1540c01c084c103290051860018200c07a80c0d40607401261151450701c0c00e100006001034102e98000001d00d400d40d07203404c0c541c411460304c0d10501c2c0c00340200300c454401702e04154000c1029440300400c00c005808480c45081c007414014821852101d41c000c101d240d40b00186550200075010480500d2141e5080903008540d00d401060745c0703442001c00900301401c5c10314603101100601000f800e5403803805000c02000c2281c803400c0c014a10880c1ba000c00303041da030794903064a64034103901c21041d1208100d64000660002001c1140460464455142540c0c03240d81c1008031403803800364080c045034410301d4180602242800410500e07042c5000f00c601644c00d4020400700c8075031140c80032040d8070141c240030020b07110101d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 584252661 1250 584251411 584251417
    0x6090801050f0c130e010b09030105180307030c15020a11011b0807181503140708040807020603060105130f090b040216060c0216060314090a0308010308090f0303040306020d2f 77
    0x13405115064103a90340c005d46100103002e8008007280100007444501504003400f5051308600c00c003840e142003241c08400c460f2a03000e0100d0042c01c10584882e0030041c040c048400c100f01e0ba292031001c40d034030b002c09030009d4542d0380f08050b48202d82d424107007003000119a00107030221170841511140c92a6442210880340b00040e85e2591840900805002c194071031103124100d410300742c0c0c1d100003507441c8080c1e41c44805450010609020802c41d030003080005031008064940c02070b416981d203502c03a120000140c07100e004084040f0f0700c400703441c01d000031210600280c43c400c840c5903c804102540e460010700c0141d105100400c00ba0a04c000c0702400000c220354426440c4807030503c10f55002c5c08440680c1080c0109550145001907210740c0820095070090308150382000c82c80c80240391039102136402030072048051001415107140810000300360b0710341e0300e560062244018185c0e6921900d80c1303012002034100300001901640340030640c1c1203e465021908a0140080300d4035100901c1c4009400341c0c3d58 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 584253911 1250 584252661 584252677
    0xf071b050a02042018010e0a061b03090e07031b17011406040503030d1b050403021806030c031006230918010f02072907090501030e0102071b06090801050f0c 69
    0x440342410000c681d50a10701070322056000240c020008250351000400401f4512003c5204483d141010804030760000c01c3c4a03400c0745107000762407000b03600382020380e01c81c02180d00000318160354001700305038294141c0c00034030020300406001c2c0745141e44d00c1080301c0003020501c04012100d090300050150f018240850038410400501c032520b8291038a01189c21500308101501240d9180c1d000e84050455801c6a10110840e61030034604241c0380d900040d0400d0700400141942c049036502191864034144190441032001504440e250040020030030b00400446c071030a150491820025040c5400309400950f800f00001c0800800f1780741c0c01c419180140140208001565a07000c050035280e8050028000d51801048820301c000c2420f950028814624240c0b20032800340c3d50100708070306030040c81e450207450082ca0300041039808814441e0080c8640f0350094065501010900802c80c1d400608405032032840da20340301d41c180e8500550b400d0382c40a4844080202480e0000307189902c20304050300e008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 584255161 1250 584253911 584253941
    0x906091211030f070e0f09060408090f0a0b0a020f120c0c13060e0103080c0d0e0616110405040615080f0c04111b030a0e061216090e0f071b050a0204 65
    0x5400e5aa065078034064180d400f0400509074082041080c05081d6451b591100d4810003805043c60207980310000c5200740074032544902c40015520b4095110101c488001c0c0034606480e0f65a0030f1100c101079910704d003440c0c0d001c081d8410028504400c5a1050569118400c607900506005d1400340420401088006403680d4107a51200c00080056140e100030b802103000d02100c659859004c00194107041510b43c607541070002d0044e94480686542041354111203462000b442c20f40a140340455943da02c10241907485810030b0280805d008036503014409a038040b01c0710416440c2d4884080b034590948454002654014001c0581c0a00342500460b20204424103410301d0607010700e040c5002c280740e135030201c44542c2c00800c09159480d00205000c01ca00f50454409041605c03c41006070100e8000340300900c07801100c41030114050092009001174100e8050000c120700d030805080c11154422141140010b03014030710302c012403c0c03500480c6502e9400001800181d04503400740800f81c00058a44115 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 584256411 1250 584255161 584255173
    0x61a031b0a05120619151715030f0d02120310150309050c04020906030a180804060309030e120c0d020f06040909060b040c05041401030b090412090609121103 69
    0x321418500204041c1c840da80b40c080e1a101007070a040e82c40000208014001c0361920840e82220310154181421500e00003150b4086140c0f0003801c5039081d4604034411407940160060094486030000c04401401c4150200d40c0c05a03608030203c1d540d003d8011109026030403600b030303134800142c00c0e100440d8004000030100c00819035500340c80b01c00c0300ca20080440041d940d2401101005000d203c400071098080780d0a40c208a00c4100184e5284000390610b44402c5c0c0e01d00c43c1c40c45040b422403485100300d4100e201d45031950360b1484040c01404894404500065402c0c2009d03d1380d140402c495035480c5d14080041242c41100c1042c0301602079040e0301683d114061035400301d603950b1440e00034000303040c03c0c4d44085081401880c05000780d40066500d54032950513340505100da45c86002e4408603400202c0310241e20981c035005030024034800070402d070081010420001071210b240006c6e801c000c500d546807070106956100442c1c0c0c2d520707240500310350307003280c00c0c14940461001280d20080902c000c00b0740b04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 584257661 1250 584256411 584256451
    0x9030c0212010c030b04020f0f160c0f0f05100c0b040515150f0303071a1e01031101080f1537030309080307020306010b031314060603010609061a03 65
    0x340d4030461005020380e443e0800603d075a640740c010000340c03060988040d814411034011080e05401422500e098166010441520b6440d60503c0100020b4002002c200216102d14150181c0022809210500070344103c00203140d0500e01901c0244640d2a9502c0080d02c1041d902c08117290000340041d0b500f03100b200001c407049014241258003840381c0e407412242500c1c1d01d07400e01103400801c1c10454840d410900011b03020601c5007850310f01000c2e0100980c122030b40c0f03241c480c801880350300181005071100e2100110801070302510b06039425409880312002c40c2e039000503409141d8000c82da04c0781034080031048103070035042422204002c10300d242d00300f9202408080f490400004c4058214007080c28a031801c03c1410742000d0440e002e40034070720103189880c0c0c141e00031030f985800610036020310b0305c40000050116213605107104005580050304826900d60050b16595400096440510a51070214002005103071882405c048400e14603031178000b1140c41700f602065400042095400c04080c00c1008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 584258911 1250 584257661 584257669
    0x3010b070206071a06010201061d04031b0c0605091503062b0219050a1a0301061206150f08160e0f040921030f0501060203030a0e010b03012309031c09030c02 69
    0xc0414452801858024a070417000282999004c1d4441149400104981c2203803a40b100d401c1e5030300c90340508050040d03110500389440781a427000700141c108000d0a0010a64561000044c0100340c0d08071541c090409101030101a00e02c400d070340f400d43c0000c4ca40e0511002a82e5000316804804003552071509082d0325401107194001f442220030790130f0110100c00e10891410000c10707170180001e1403c500c19410b0400c2904150300c0103000b14000c0c40038040902000b9a1240c0010018003c1100242c0c10070742c2c08400076004170317890701c403a80210b00d80c080041c01b02600500518280c03001139980c100341401080a10281030882c5017529007240e128010040441c1c03c0004401801070740499404507064a070034014115481d44101d0701c0410304060042020550001c191703a00402c64080014458520b4000c4500420500d40016059424103015004620491480007442010100c4004141c3c0e07603030640a8580c8605179070340500b4414841045030100c51039000300006442400c0114031442542c0000f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 584260161 1250 584258911 584258933
    0x9170a060510080a033006290a2f0d0f1e08040c0e010303020708010c0513030311010f0507020304180c32070605340c0c120305130e0c03010b07020607 66
    0x20942c1544401023002808882d600904400700b41e000d00c5000e00703200481800903849401c10444c00c000a50702d40410620b0015011000004411071095450500d0104030791078640d410f1140020030b0a81c0b40c5440c0302401080c1c940900048c160010406075500c6000b540d6110340031f00196003440350341c1004149a40c0303585045018501940040841c02e1505021500b5101060741e14810002c041c0034003001e0400724078021068030f03030600f00341155442c000b45040c0188004400e12540324104801d000743d40b078001c0010000c0d20428141d80a51624004000c4240c0d2400c914040000b0101c106030000c1c0f404040f40508075101c0e0402d0500142040d081c20046504440703c1a645d10759190309200c4819000d40502e40145000360034003800154000c410155040001400000c0c401e0a880031001c10100111450203030041c0d90b01064000e0f00e50070010a00c0d0015030881355034041c0d01c8008144041d03d00700c954030030b00140240c1840d682c01e0406202003600034120490700700b00107016442c0021948149 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 584261411 1250 584260161 584260247
    0x1a03070609180b09061302390f070e09030706020a0201060e16120f15030b0426030a09020409120809060105100c110109170a060510080a03 61
    0x900d4030007030b04041207202441510701440082d0342c50f00150541c0780d19690080e9600800c00c8070350500341a00d9040402c06489112100c500e40d011800101441115101004094224000540c40e03800c10b007990300d0b56503580c105040c03081603100e5541000440c8031461080d92290f04c0c03038183d90900800e0358030b41c02a0f0308030a00440140c0d454010510500c4803901206a0242d560f10019401103c40c5801400c5180c1610f0821070598640d090069450707903a8102110300c00c0d1a0018000c0c0d1550b034103001004c0981a202101c3c4500c0380c0c0320200c01000400c13810301c03040100141d414a1605d4150021004000d4030a040360059224882d04011a15902080e4481031042d00d9400082c501a0b00c5541007050580150744280c000480c2c03155060741c05a00c4807885a8000e480c090400041e10041e20152003d038464516550071010400c0391000220b00007500c50702c82c0000340f205072200701c4000000c066500909809030702c40c140c3c050110340700d0024824030901e0300480c4588665103562030030382081d540e41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 584262661 1250 584261411 584261417
    0xf14060103030e03061506030a0b120d020606040515011b0510020301090509011d100b06070b01060f0314071407060f15050a0515031308090d06050a0b01020a03121a030706 75
    0x80740c0200f0707041c24401e0036845940c15030355185503510080014543d0101800e0301d040f0b950b58021b41d608a841c1c608204456110810448010b5103100f00000c0d035401c42101c01c2c1d0300850420740460500d0351303004125082c44c00141c41d03d03004900c01c04d07403e5039283c8001000340c40e94420240558840d46462000318080c0030440000701e0a850132800140c04c0d500700b100380720208c802b0607440301d1014101040c111810000401d022540c0c04010000401c00c5c0140980540440300360000059000d41000382d4280361405610b050049a89000d10500d074001c08a07204408140c80940568a41e21400004c00580c3c0c4103940004032184d1904880f0308071485001000e800354561142486145880c001100c000c0c1011158107001c0d048015a001e540e00010300000b001c0784540403c1d200b0441c2d0601601c0101c1c402134810085420749041c000040d0200307440c03070980f10307190803509002e55201141c04031030141c0503260b4030b03070000852080c00c000301005a03400035941080d5086181c25602440181c004020551b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 584263911 1250 584262661 584262677
    0xd1401170d0206011809080d060e04140705090103080906070c03081c020c070b0a1704240b030607050d110403050a0303050106020f15190e0706021e07030f1406010303 73
    0x4541c9400d444042180a551251004000090180703040e0890000c000c800032030850030300c4c0344c00d08460050020181034181007042c04181280454441c0d07214902803880c0d49030b140300d03106d00303141c580c0d0450081036040f140c44001400410400740040c40d02c1d82003e89251f103045442d40300c8203000c400c5500121240342d4000341d250701e10b4041c0000c00c81c091000b11000c40c076092034208050350360704042c4105400e01e20040760118409014910b0500007441c0310300640c0041c9820f1034074952000c0c1160441c4407040a082c50500140346a104512012001800500c42d645600000359040d4020307c0720441300c03540710042c0200f40d54848014000440c446c400800d00c2c80340510300036080e20016040407045500c01c88038558030a800150b01142500e070041954a01d0300d410042c5042e100488003258461820320041160302180001c1040488840e039003501c2042407542d805508519800b0306d54401ca0303001010520114910407101c407113652042c5110f42c0906901c000d4141441000d074419000300f1820 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 584265161 1250 584263911 584263949
    0x3051012050120182e050403031d06030402091510120c0806090408030901020d020f07020a0e011208030a0212070801060f08040803011502010e1605040f061203050d1401 74
    0x900d1461001100f10031202d030401e4041012101181101844c041c0f04921401801d5210505000f10500748404c0d42031081d03011205010140c540e81c402d20044001030201805d0f502e510900450b80f00007118000e001e14a0754540b5000c02003005000f800c03019010120a480804658030203504507002c98003034565048202219544030b003110305200c4da42c4280314500c1c080104580d600c008095200c2da011607069143d80340c6214042c024043d00110040f0a4400112000c049402c04003401c00e480c4200c0e00303540b03601e40b51130314032064040030711401803111103100f280d20000348400081c40d4491043c80380141003c1c0d80009511201505507046408101404018041c1369880310443c103140407181040c1c045810300e56602980c42c40140f01c3e18100c910603c3e00120139520039008400007507540c0d01150580481700c4e2020705035162903c40d562084c0e14140c101c600d81c0c9403134082d8034205c0f045590300c0319448416803800d481562110858403140741d41c0300d1000e952100609e501c036000e004003150070b074000885 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 584266411 1250 584265161 584265191
    0x90a03090f05030d0f09050301050414061b0a1407060606052a0606010804020d0209161b021804030507060f02130b07020f01180506040e100f06020d030510120501 71
    0x20355001001c0e4003110950a109a80b4001462000044a0b2034030040c0d00c0c258100440b0380745502d411071a03165081000b480f05000b004c03000300307100c1e5a040d025a1020b4403020312078110800641c0346081380c00d5050100b0003100c4e003d203c400d82c5200030f80180d6841d00d0300d075550303501c111009600070101081012890030803103080841c812902c400700c035401807560980d011b9001c0d0341c0c00d03000302a1810424400000760447d02d03200302c03081c0d41550140c0005503d003040b030096040345422603100710010f420480b0304001e111000040c04103540e00170305002c00c0c81183d41d001030801c83d0014030035418000e0411007d000116035100e601c43c14148100d0043c0c583e01c1518030305001a402e640040740b00d030310a02081c005039542d1000e00015070001d080c044545422144000c0713030b03808103030b004951140d004140080c103280c082810324032551040103a07030005525603820703030711624103030181e0001a442181e25061081c080d500045d04203082c0b50a0301140d0780e031101444401e50341d5440449659440751055202119 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 584267661 1250 584266411 584266427
    0x10e150f042105161a030a0b09090a03021605011205090111130609050402070206162303040806010b04292701030506040b370f03050705030a0c0b03090f06090a03 71
    0x5207542c8a14044d40750000072681e05410004d180654000000821a8404140d201d0202020061b0914a1618100140039220381c0c00305002d502502925907a48508911000803800395001612182c212845a00ca140d006010080000c4203e660f281ca4004180308003e02401c2ea07003003e0b58058464505000c001000080c155000d07034080c50041c4950001aa103038403d40d10011000342d00049141c04509140d8428101d00d6244d500000c0500c10201e10003801000500688100804035000e80c0d0381c0c2c05040e28144103078801d201c44429038501c800075480040c0c20030948610800380841c1000280d00302d0321243d4044d26010781c10300041d480c42d903003607581500407641c1c090401c40d420407950315507201061014003991522400c1039900b141040c16000714685603448101d1006070619200d8940008804004aa0206444621540720700040510700044c040c001c00d680400c1d400300c0503141c00845240307500007030310010031130062800714002c0311410000d85105259a10052030181d44604011301402 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 584268911 1250 584267661 584267683
    0x108070f080c0907030c170c21090a080a020703020306070c05010509072601020f0708030117120a0804052e0f0b0a0b0a110607021b010e150f042105 65
    0x107009928905402c0c1e8507075060350b41c080000e040c0803d10150301b6004503071400e072110300340c00c5543c0301c0020f00001c3c9030304101070800b4801196441d0b800ca4103440318042101c1c8115030b440056441036601100007018074000d0840f102c510300444441079203039400a818103008072001000101000c0c801030912000b401860b4101440710003400d00641000d802d0041d142c02101101c621340c0c211343c070040700703040d00758103d0780d55041c110700081e02d404d154504646181c0c02882054a0400d8520074030402c0d4101045000c1c0114002c90040e2401c81444002e071001a00200155901d001e031841035505e140d05402c071050b042a0f003140d4400c0f840d1000036004111900c2c504a00c00080c60b0002d00f009985030010090199112403014a07101c003400c000c101c0c1c01d64408426800d40d405001d003801809900003d40d0321926608490440c1c082c403144004555420350002c0c46644811006980203054410707030000c22070fa4115907507a074170300750301c900c031101840110780344499a100311034040b00140481840904001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 584270161 1250 584268911 584268913
    0x81206010e030a0206131806051f0e0907050c01090b0417070c0b090604080d0302030a061409060904021f080916300f032607051605010906050108070f08 67
    0x2203168103001c01d036143c008030f10090040c030000071130000414036850350400401000149003159071041e510340002d4041c5119040c00341e802e04038602c80c03000d04c0d00b1481d568035066a640d0400c0350552010425503160260410090080c20440402450401c2c00b07800c0c4140d000312052042802c05240c41a01da00c161032003c00b01c000c0030b112075000030b0001c54001c81181e001001050703c401c00c1d40000780c01c0d84156445405503100f84140e003007240c6d8040c0c000d9441000350360820080155180c44048111500c048aa548030000400140781d510300515925009030001d0303c00311000d00002e9240303400b464599440008110100100300d9400403c000c024000d80705d079604001d010f89070200030b554a02e111280300c12094541003642c002400720585244c0d003039030040c801003000310280c00d014144c01030201d856402e02c4004400d200500c006491524000c0405540f05440c00c0040c800e4a03540c46030350b0b101280c4035500da24400300464807500882e4040d00052000c0c22a5615100c104400020706034420a12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 584271411 1250 584270161 584270177
    0x50d02010203070e0618190603060603090c030206030703061a040f080f1504141e0105102702090a0b0301150305010f0611030d0510060e040902062d0708120601 70
    0x81e80900240780c04a400c0e45d1507501c40d840184906690342e84105010307001030b0528000c81c80c00004e0082101100c400351402c10201d0b032521011410750b12400006010b0320000780c1e013003006042a00085038450580c1c54001401038948030116442c406922110401160220b024015010300c04080f90052040c20002e045000c580c140640e114100f0302041001c03400402d001070b007400341040036081202d4000040e214540030b480d01c5000b06100e484206809507180030001110b225641c0c1d84c0c001980c0d40244402405620503c0007500e000200d00b5900100f5000e00c24038155072a40e40c10300001c2e242c880000c80c0c80398100303840c00c01d01941c0c00e8411410142050010031407110750b0761140c0240e0f42d40d4903000880d030184460309440c42c4248803c1c16445417a10040001c240c10310140d08040c1d0f409580ca030b201c110a0300080206a8030130760000b9501140130842000d601602c1560b118074401010480719290348100b60b06c0c900d070340000b02c007981d0460700007403407540140c02500d28a9014000342481c0c0c503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 584272661 1250 584271411 584271421
    0xd06050105091305090304090e150f06130c1407050307170f030402060a11030a021e0327010e0d0b07180b0a03111b030c0d05190c02060702090a09050d02010203 70
    0x5404800c0f10001da2015603c40124410100a10032900900a9038000344102c04480c40810744c0c60039110001203074120480081804001c01488603030250400400c584885020410b0840080030b81000610078406000f03400d8200000300c00c0a0002a070243c00035648800d098144213036250005103070a0042c0e0410003400f841c40040c4025a41c1140c1c054031050b07120200c4220a8800c0810160b040240d880301060035052980d0000d8586a2000035000e40c034010041d03500c98694a0050070305240c21034420608071340611009504081c0c0b0362205241000600100c0000700d42d03d00e50203078055981803e610704000e00c5c190040d043c0045d10180121810009240002c10301c5513010720390140040503100d250010b0300201003010387d501c00121442101c19040c083c06002d5590b4020303000300c4100e000761202c0090990140d000c0c0c9422041003004184042d00488048070001300700b03681243d10010911030800581c50b03018065200c1d0504c403800040c401c01d2030601d9407800b20a00c400100310783c01001088 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 584273911 1250 584272661 584272669
    0xc15010612050613021216030b030c0108060a030606170c0f0901050103021e2b0903080403080405030c031305041401061d040b0409121e0203092806050d0605010509 72
    0x1d08400c46401c00010790f40c0301e20700010002803d4800c100c2d455030000c01c1ca2040c0080c6c203403505015400000600e050040045d50030f5017178801961106a01d40c0016079485c880d0350081d610136500410040c100344509032259500011a0215007168006a551400d40c92250768100514106078000301d45c620160903080c13002503550041400790604064012942c1d40a5441d0054640c010382da150701300c161240b004400011503100014090044074880b404807007aa45401d100c0c45002e140c25035205050341d03840b62810b542444010703008a8441c44104070850040005001030b041e80c07006540500042e41c030301002c004c140d460144140c5001d850300c0c00108070058100308052082183c0080c44043d51100800082c000c2205400315a0480c0c18000918200001001d071001c800b500e50300e540340b144121055000e48401691610310250780108207032201481c2c03d035168401402c106c0c03502c001d105100d19803e00340301400d80c41440401c10118041c0c100000b24003682001e17103400e01c3c6c494200000f00b0001 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 584275161 1250 584273911 584273927
    0xa0f12030537030c0c050601032a031101080903031509060a1a0304060510030f0609080706090b01030c0b09090a110405060708040306050610051207230c150106 70
    0x9041c0700c0009008650151500d0b6007540c2c8081c071507901d00030303180c000910408950300c41ca10140007070700e48400164880d004080c0f00c0d41c0b00e9080700040c400340c0e0a50b91105480c480e1004d05851002003e010415000c2c5501803040155110310030680221441100140042c030000e00214840d400600c00c00804210400c01c0d41c9a0110845040605403501070125180b4001d0b80c000509650130000141800c10303c0303400550203288036820402840d81c604081d0005024036010040c016107070f001080c0301150050700420300321405845140d1401c0100c2e07964000710369445c4002c4802110800c010402d0180128000c0020300c0d285400c3c61500b0f441c42c0000b00c88a2009205001070380e520591020100091000c1c1d9002e840060f00045c3e8420040c100b401058000313100072200941081c001481d603040c048003071004110b16894590403d256140d070031040c40c400070541e800308010a100d00038000c01050484268200000e8590303179880c0c44414080c180528150b02c080008405801088201da1040303030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 584276411 1250 584275161 584275163
    0x5010f02062406280c0308010605030c0d090b0609060402042d0807080714061c0b191509050f030307020904080c0a0303060611060f0a0c020a060e0c0a0f12 68
    0x44014281c007041c0b0081002c414500d0315800810204842941800c21004402840140e0074802c10086825908071000100c0960040000f000c0c5401084454054030145400c4500c113900c003402c00b652660300c5012151003210640c2c0000302003007804018208040001e8121106440543c50a8140a030100211003045114420160904031240014100343d0040000c0d01c0c0c244165000955520045550350040f0b000340d442c107203451800d20005142c881d0031500724246440000240001e482c0d419401010b80000054000a00b0704400300c0c00070685103040701038000d100307000300c003041100e000810b03820458010502036942051204010703075000045d20f105a030704480c1140903540d94075201919004e0300301201d0f150310400035020301b05901030304508203403030250b86d0300c1c04100101e08005603195000c1d175a070748024501c080465a0000c1c0f94000300da0301a0346004980c070908440e9900f1781258000352400b03034150032881c60b131212482e2030004213000308224505550003a0414000c03049225a403a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 584277661 1250 584276411 584276431
    0x307081204290115051b1c02030414010e13090501051b040302030a021903050a080403121b02040c030905031309051803091003140a0f06080102130519030209180705010f0206 76
    0x4505402d0320403c110384100511000302886c110504130b040395a000c0300280c007540d1681c11a02c00381e0041c070000c185d504850301c2c00d84461406940c0740c0151008400350016135000b5800f0400c0226868043c00750401c407503c43c0b800052a8a00b0a801a052741c409040a00c070501d020401000569800940003442c2c1c0e030110350894481d90510309000006840c0d9000a01c54098000c948007408040409041203d006040a0300806a6080216030040300c00103940e00030b0002400b0400941003a600503020001c060400107010000c586031545150003a03c0b044800911410b01408404040e004030760700f04c07004048170105440141181034803800303000d80c40b90084254404e1451301d43d110360444650b0700c1c0e400880c41000d00340303d10000040c00d000c00c0701b070b80d015003840000690801e0501c02c807041071140c026400d010604020401030b002e92844060070301c2d9510300d000400584e84003071149000e9011028460341d44203400a149050003a582d020030f040c051a80750a030b0100390086013960b80704800c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 584278911 1250 584277661 584277689
    0x50105011d130e0d02010f0f0621050f03040e10090507050a0305040c030803070c0302060105090601051c020c0d0203040801050609071e0c080f070c0807030c031403070812042901 78
    0x503000400c400403c1008900c04d8180800c0c1254040d881003070700c001c8030b61082c450345c06840170810036140c151240728800e01007200362503481c03000000c250503950700c87e200760741148a8612115107181c10a41004818000035000c0c002010000c0030745e000101003450f018417803450007540c054000d00070748103040d0915858500043c20800001030141c00f42d540140c085480f070401d0744c2d0007030803218039241c114051312400c0004a40c514208240910500f01651424030300801458a08500114940fa0003400c1e6028001c40328160000e209540781945590300079030720341d480c1810060035502d0160001d4001c003449418055002d50100d030034513041100b500c62481d506840402102d140d26280c001506155011680b0346003504250700400a041c0218800c080064903001480c1d00c03503025104c0248202c0029a0420006005100000703104a41d203060b60f040c00059240d880c0c441e03201ca1540b50002c1901c100308800c01c01014190302d0050408003c141101c40b1402c250b07048500e040c000d41802a260f8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 584280161 1250 584278911 584278939
    0x6061002010f05040b190b03030d0c0306031a1608150409110a0303110708060f060f1206130606140a05061614060f010b030708060f181603050105011d 66
    0x350000d0b4514000c0080401c110303d001d0400c1056014140d4580680b502d4424000940003014000c180c00c40000601852810500c00c402500402d1011030040a03d034681e000003000c24415078203c0000c5500108542882c50410101c24007000303e44902c0040c048008280f050100d880c00992000e2003056074000f940d87c5860510300320003156404015401101d03200e01004240d44a0b40b20030003401c1c050111507115884482007a03d80380215540e680e00401c1200180b240c0c5402d41d0210fa204001420740c4040c07032111026207003001000c840010402045042c0340040140a20400c1c00420004542c1003219102c0f10010704102130520402c0e01c1000f0105848130180c040701c0140a500c1d80c030490b401e40f510704685c401500e4000403510b0308010b8000f40300005408041070122481001955110b41c070a13a0341c0810800d412030344200e004e820006e40038402e42003954030f107030341d6026110700200c24038280440c4200909582d0b05800c968104450b0158a10000800380300950f039001040302c40000304035407 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 584281411 1250 584280161 584280163
    0xb130311070e132a06120c05070b061f03020702010e0f090f0415020408011b050a1205101d0411010e0a060806030a1e051504120e010e0405010617160206061002 70
    0xa100111070441200004c8800308558804e8124100d91345038880200003460380c5e2400e01142c20941580c00491000c001100008440c10459a8004401003403002800c0400c00203008189100b603e040c00f00b580052003000b55030b006001c3c0700074184101d400c1e980760903581000c200f1000740501594a00b120403000b0508102c041d074880180c4040d0aa0115101c1da6113100c210701130046c0c0d410380f4007203169410200303c1c018410300880c0c1410b400d9880d1004150000c11b840c100414004102941016074080040390860003070b0030009400318018031030062400c09042c040d0b154110f5418180c14481410081c0090b0740715121020100d400b0f0381045e120559031500031a00703050f0114030080ca00e0141c12340c004000e85d810078101041901900807152070400a002e0403030b5030716041d10042d01500002c1050600144070308200d400f90441071404c01070500307800000ca002d40d0400e030845804545000804840e410f5504440340e40107880d4000c40c1c9108105907000f035201c2c0d1015050902404180354103400c0680 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 584282661 1250 584281411 584281433
    0x1506180d0303290a0806010f120305071e050615090c13180c0801170c100e09191113090506180103050606010f0c03080105060a0c0b130311070e13 64
    0x1509011280d505460101d0f01d1030b010032040440c0707100f4000c45a01141039400040d501c0e068036a4040d10700e80c102e041100d00704554003002000c41c100301007007003018002641d440740e81e03146c2d600082144d00810380328503145042041c02400c892402415100d02a19a0f0b03400303803e140c0140b200c0c0241035440ca0300c00034102916840340c103c1e80300f80c0e0302c295180741e00110682c448424110f460307454034820303625941500d40c04481032100c4101548500030850041c0352080c1020310040050a1002000e0304030008124080e9007241e0804e19110300c01840a2808414010700765001503001185d890242903004805508020740031304d540c5156140001204ca85a100306140301c41c0445030304012035a03692800340d5454808170751182c00950150a0903100074000c640f01020980c3c551142851070f82414180245504240d01807420800004a01c0c4c0208020240d4640a404d619a101000d1025400c02502d102c5a903000c0d0b25296020302000c01052001c0031000790000c003494800d015601c40c9044c8558012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 584283911 1250 584282661 584282681
    0x30106030506090f060709060c1209081e190c090510050d05030c07060905010210150b07050307020427030c0501091a071e0e041e02121506180d0303 65
    0x100c510402c1c08461480003604244c1d07280c00d20100c0700f80395140d1104540528a6200b0000460403130b58150780002d60080324554a070000d4904809015a280c14143c0742c0b04642800c03c40020180d00720400442c0180400c00014000445200201c0502c6d030761844003000910440860365580e00c041165506c50344015070041c03800030044244c01107103090254581c0e11115a4003020301c0f900400180182c0a86005400c44005030098010071203902e004030003900c01074161044441c1c1d410000301c4e855841074081c1882500940086840d84102c1c410300044492400c1c8003070342c840304052010064000d8074040e00c07069070b15181640440145290181c050410341c000141040c18041c2d000c0d600c41380c08280b10f8032813241c45d80c40030303042142c1102c1d154080c2c0b80803c40300d00040700d42c3c01548080c00c0c1034012404132014003e00303140300b4038888007020880c2c02c4024402c41c0d150901d414410400c1044135520403682c0200d6505140040300440030013003821680075a802000d2410b041d40c06e140c061391242c4509 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 584285161 1250 584283911 584283913
    0xc0d0203160f090f090b04151d031e131205162c060a090902060f0406030c0f0908060a0506041d0d020d081b1b011119110c040b0301060305 61
    0x9454081009802e2014020f0340f0075079141462845800ca61801008140c54100400d501c0f141c403a44c46450305d000304021541c1b0740da0340ba4040141910b800840d03403040e00340c815025507250340c042906505102500f40140f41d441070140300e007040107a000310614007101c01c400f411704070300c03c064540303d0708051303072a8104901203144040004050355000695101440c0d000c030100b1101c04105455140703807005503013407600080600383c140201a4240e10aa4106000401480c2800400c241c40500c5602c180c0000c00040e032074a07030001d881d54021243d9440540d075400d0034030000381400c98880ea5800f004080d43d008a03251004a505501c49500c40021200c030b149603040300b4541805400da0341c4481c4581c20b0700600c140b4515108240c85102504d014054003010414000600c03401200daa4024290000d81000d8000e441100b0b20400d00c00c0650148010040035140c1d20b682030701881480018244200740082c0b0803840c8546d06c40421031800e080421500011114904d20101e07004240a42004010b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 584286411 1250 584285161 584285203
    0x30301090917031009060b16020f031203190b01050f0d050a0e0a03020c10030b0a030b0402010e0307090902030c0d2a0f03060911060f0406030e01021303111005030105030c0d0203 78
    0x100302c08513001041914824a014401c0d00c0d640c250603107032881206900140007405001c54401483c000e00c615180500003001c40718a100169003d0225070b0042c2c41c1440791006002d020b0303031804030034010000c844409090050900014080641085c448c1e90800c1846950341d0001031285800395010010700300e9043c0031101c03076208070b01c1d0103503440841200c224401c549801c20300e4840c0c2c0c03190250101c00d1001903c00412945541d951000300c7c580a001241440503a41e0141442d031802c0003540010030241c000483c03c00044d00500d0b041814101d001070062451801e6100071440c0300d0f41c5060f10740b101c2100a031041e86e48101c84403403200a9081488014500c013000002d010681d0481c190040c0a40010702000c4814401c103c028861041007410071841803204005d9103019078008020690148000361810030301c00b030441c840c0b20f05500202c03880c1c14104c11a544a00b410000c1840c40105403c003680382d54103000c0000d0b900c14050000310300c0f4000c00c500d00800c5403003e02102c2074000c460411014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 584287661 1250 584286411 584286421
    0x7030f030203270a050402030a0204091b030e011b08070e060307050a020717062206020a08040516050901150c08281e0c1b0e1501020601030503030109091703 69
    0x34aa500280307002d0440f514680f514240001003181c80000300c3c1c8014203448840c0e2400c401d100c0a03400081000408641c2400002007041d0240651b40510100080d080841402003070040c04440410394050300d00e07898880962643d8a0524203d0304075006070038040c1c00d540c6c41c4141103403449502c503040e6804c100c0c08014060315a03084006003c14282c50380035208000c0d00d42c1d0054101c01c0044003c14500c1d42f0880c04100019008000301c9030702c243d14001c8102201d61034480d00281ea209250b00400101c0c072408000c01d2050038801070140030031048503844060315000015041d0b06043c0140c282d54040041c14504003030086900c801c034194084c1e00c4075280d04420030a0603010030980c0c400c1c0d080c108840481042648a031f6003d60244600811683c030000e07403c402101c50103482c07407088821141c240c0409404c0700300352248200810078501091050302e0401071020000081c50211030655108900510029a0210030740381075075441400000d44030708a003854100e00f03082007600710780520000180300c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 584288911 1250 584287661 584287663
    0x31e110d06051e091513050d0503010f120c05041a19080c0111060a0b0117040f0318030b01031502070b131b26012301170109170c07030f0302 62
    0x1920603001c80602d204180380303ea200c803082c48012a0710050580150300c0300c0c0312000c0824802d580203d070115100c0c1001e201e0341d50301ca20b4000c030440c0303d5012038800b00c010407030850001c050304042c00201a0050200c0d046a440c018100c1c1c1500a25100d983c03940032560f00c26044000c1099a2480200030004103040c1030745c0d0460030a07580c0100042409000107144c80e40d4010841c03920104071110080955580c1c82d1600c400400c80119803d04201d240e1200c426451421600c581c001c600500d0000e03044145481c001d420f0701c60350100b80c00503807a030141c1000854041e07011a411641c00064443e4001c2c0c0840c0810000e1040d08001002210f00009000b000c0d000c0c0c805460246124000001400d14a2030807413038010128400d1031601d0b00c640c66801c04500a4500300f400003514203002080f60481e80042a980c2080c01406054810425004000880341d0b4004108191424402001500105d8944201407152880141a603074030000750280501070402110000b183c002409080c2c082c0c80f49002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 584290161 1250 584288911 584288921
    0xd020f07020f010807020721020603090105090607020d050405012a0c090c02010b09130201020f0706020c03122d040b0406031b0e031e0106090203040f02010f0801031e110d06 76
    0x180e00614000312030035a0b80d40903c107003a0146105030024842546001640c0ea20345424403107010700e0780070081080c40162030350f4001d50301850395000042110300c1e0003200a40b0b0010020252011076000702c81d040c1c2e00e5a046400c4405440342840c00405c134081ca60424001a0a650401000d200c0781a0b420014003c070418102c0543d20f0000040c1720704c815042e000c034282d40003100c0b8154017000c0740011419007032504006080403072060041c1c40404002c004e446042100f103031301030f0015030801c1858246600d030a025000208610310105401c01650100e1145545404640081c0c1074043c80c68642e140c551600544008014036521182d6032501c520006000d00045440c04120701d08020700002094012084000368103800303801000300f002ca4010300815400217002070952550b0712034001c1201e445500095116600800355007011210501c001055070100c1c128400030800424010700008001358203c9072500000d0740c0c109200e42c050701303249010f100c3c80c079031044c0d020762062003032400c000f555040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 584291411 1250 584290161 584290163
    0x828090e310c030210030b1f0c060e010b030c0d080904020f0c1209040f020c0c130608010603110102070e01080a11060405220e010605090a05130c030b010906090923030d020f07 77
    0x40e000007961707181002d50a8410390081d195000b0b1845160705030344071250b0f062900c90b0b045443c14880c0c2e070040307480d6041285e0b00d108411b00c06944414814034181010803214202007016907080a2174a120b80320801180034907901e080c4143d8000130300c1450440038009541c500400c44040d83d44003031605031002020b6010000c0f5074060760600041681d00580c51007502c1c808052400940818280380041108100c2c4044641d8080e030394481000c9074402003481100007643c40b900d2011031200c403420002e4904082ca0380f05071890002c0d03c005002c60380b40071604094155019280064042e041c0000410501554201c0d5800c150a00f60048410a06041c3c0b5184035220a43c00c11103228100550340c2a40c2550003040c3d00b00c040c64010615000d40c69014a5120150751021080441c455071148030802c2c840d030058600e64450001030025001500c1500300904128000f008821508d83d40c01c0c0107240905861035031290003007880e282d145424021070395a0f00d2813034021540d07800018551420f9400c0040 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 584292661 1250 584291411 584291419
    0x30d0b01030b06040b09150c01060b0304051504050a11041b02030714031303030e0a0f060c052a0111070503011e1b080112050a0828090e310c0302 64
    0xc850401c6040c408122803d9400b01174909180410381402d00078580d20100042d211170400b0058041e20181c00c1c8102c50150020030301181d40d074140b03818a9454540f03824000c6001111140920001610000d07a070350907561700240c1c10841c4414000010000c3c8070f44007207811031404421a03118070070b502000803c2110300c200104140e204030001071655a002d158400e11142051000a00c0070901540107501e0075003004145140306500c07841c00d01d940e4900c82e4405808130750648262030401105100091040401c010000901c0315007950000821a05c44001b6041c40001900040009030511000b009001c02800a100b03009018059030881000701d618044618617020038102040c2d40a882c224403000c0d11743d45c4840c0c690030949029090381e1900c400303c03440e2150341c000000107180070b8058030348405154503000340c01083c0039501c05003e905070803680400102940c117000180000d81c030f8a801641e560181104000c810640b2a84451002010000f0000382c3d46010104070f000090f04007078900c2a6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 584293911 1250 584292661 584292671
    0x71d0603011418070e041806020c0729040603020a030e060702100e01020301050f100903170315061c051807030804080c06190f170405010b010f0c05030405041a03030d0b0103 76
    0x40f003a81d080340c10540e008000603000001050003450643c02c110030002660301168501c00080c0e440804a07440302580460b41c0d0060101000003541c01011315108403d4000c0700f014a2050f0703598404584128020042410790116016444503c00e40c002154507602404550550401101c00f039503903805101802c10b07150501800f80010607041c000d03641210005401d400c6051112810400c00344001d2186000704521900000007003901c81c002c076010080c950a000d81d890030f2001d0040303420844807440501803c0d01b04865281c1d40342c1010600c5000400f16000121a161011340f0303007070303079140030344110343c0348034442c00481440805402001120b01410840e41107085030b20034005540120005403021030b98115400903400d0080100300d10b1051302345405e000f02261034151000700e4038183c0b800d07192a9910341880b407295030850300000050406040c608200305590383d4103903482c801c500850340141c3d203c59001d41d19201c01d034031481240030000d003529280d015a4800d403000b4940b07600c2e5240024140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 584295161 1250 584293911 584293939
    0x9080118050c06090402070506012d030807061104050301060602010e0613120c031e1101061e170f060708100e0103020108010320060d06030524071d06030114 69
    0x6200c140a90592200c05414102400300401103035412000c0d00a40154080104030002042445890701030034003103210380900c600003008860340040341c41282d50300b65152007092020a00000903500340035030140b03002c216102165031064040c000c1c0d900458056003041d00100c3d0301741d019000046403560305022a0019954079909000044691102400d080c40056200b8090f40c442c042030780e00c032070281c105081d200c100000c040c02140c50028a4000013140200c401e0337102e20080c0100350007421045800740c020908107940e01410071740c922400040c080620b6011200c91020f1140802c240384c882c0a031401c40c80d040d030000c0c0201c2030860b80c03400e800070501000308000c42050961410303aa01a0368095040e802c41d0745050b140d0440c421110b000c443c504424440a94842c4004d00100100d0000424810300c4d51408528010110b40c05a41044042d9035038507403003080143c00f652080c010700c1c0500380d00c000f09a6940c0d8000c000c602607500510000300100e541c484a868400c02c45030b098440790303000b0b010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 584296411 1250 584295161 584295191
    0x3010b0d090b070f120c050a05031021050114071d0103060519080d09030f0204021809091e0a120806060d0e070f050909070504050c2101062003090618060a090801 71
    0x1c04890751006c60070901950802c127115402843e40301900a00d001076841c0c032540740071648034039140c9220324802440d003540c08100084c0201905e189440d00310960030304001d400980382d5540146603406600e00801c800ea000d80c880c1c0c1080009043c0500140c03010340114258030306000c070b00c0c01019182d214651003d041380380305420f05812281c210f51280101600341d401c00002c0d5009280c014800c82c1041007222440e51902c0b08580241f05e0100107110810307101600d900441c0580303980b04503030703000545c0800c080342c11502c980c40342e291545841400c60f504c1c200014024050505046803041c40c110268040e804000340301d609030382d4100070320b01003d5510810008107640071034200c0b0141c0c00099040045040540250390410389400b885402d100e011104c0e001e510102560280780c0d000340b8401007280c1c1e500484c0301d1810b80c034f03140415817541c0207229582c1c0e628890b160100d030150b6000900d106484562854011031848018421903484c9050500240301a0749400750213015460070001c00f040c888 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 584297661 1250 584296411 584296421
    0x2114070f0f08030a05030408070210021501050103201e0403121202090f120f030a03140f010e28020720040513081806070302070311060f03010b0d090b070f12 69
    0x203500040d803134010841c0040b81d40d0341010300200d075000b400f032240c0c80040ea03410194041000c507581c020107403408070444041100d001a8042c6041c980360210380c00c0703c40008280d10340d151691110140d6102959101519403031450603c9202104003c00c0102c200722801c0c0c4440005c0d01d4540e508010f110b40100100101e01c40e04617402e501100d0fa100104243c00c00741d8603010410b20310410350308040402c14007141146d1180ca41e040c000f1340e4901c107540b000d510300e40f54940c000911b180e10701180d40c14202e8100859002500250050340160754514469480040d10444d07200301c0701d0207644400d100d14040800d440e4510b034040209054003060301d42414070b84101803140c800c401c140c158801282c2c031088070b958002d03121441c00e081107802c6070719685c855a00410201d032182c3c1c0104100d51131070419001c85003070300070700921a02042107211088001001960b05544004003400e95442440040b10014448408002d100140d0b0408210b120342d0450701c4008801c4090315089405410080e0781c0701124 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 584298911 1250 584297661 584297669
    0x40b10061b06060306020a0504080f0a0b2205030a03510e01080303010302030717071419060203031602010e030a230f0304060e06060a2114070f0f 64
    0xa00d240350320440009022a400d40070501448000a506440b0b0310746000b642c0c80001e80784040342001500b0030100800700100790080c4001c01c041c01451907140d030388158406010300407040f4501d4000b00f155500d181035101c0c0604942c070908903a40c40000c00005806011141440d0806498500a2488100010752802c0e44035004201c0002902168502003000e441c541d054416442150f14022402c09000c039501d5000e400312500843e2250b00d9441014544009070300301e80c5000d0895102c0e0301403000001070303150549a40061641c240208034007c5106000e021166580d08a5510400240c10f40c0200085014031500d20182c0c55801c50114241e00f0380b1840b983d01c0c0c01d03a030700404c4420a1280b1070f6081c60420045807964291044c4143d16800346500f110026809a040c00000e2104106079841180380d5103204102500311803901400282c292417081c42070143c070202c0408802c10112680400b00040ea030700061346590000742c0458190b54580d41c1c0501c51019081c1400421030781080384a25080b5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 584300161 1250 584298911 584298917
    0xe1612200a02010b06030a0e1216241812050705031c06050a080d0201050f04240f020c010504050f03131203090b0a03090b0c0c0a03050918010806040b1006 68
    0xa20440c0c40c140e400000d6075801c5541e200381c031403880d986100046028480070180403400075101c403805801c1a11400e80ca00c0d001c0400c102d4044001450000c03006030b070742c1004064004440101c020786120750201c040d5502540b1340f424149201154100d09404e06005290450102c003454030240c0b031320b109582e0050040e40c400c2c07013404284140c2c1da0f4a00c1c0e000b01e60300300c0414080d60710008a03c171440700c0d4010f000c01d071308800410700317002c2d03824410140d02000c0408003000d242002d4503100340806040c4108120f00054001000c20341c1e00c140c0110780d06142c6020704541d03d0070880d5802d070003080c0581e8200c036607008901401c030301020b0020584103003144990100c04114900401c038110b03564910002c60a00100c8400090482c0c048805484030030500d8030b000c501e40344940707045060040001c1011108e6038041c04003c480e02000141c61007016410709000c4d945100746000511466030700c5d24503e181110290010610000110300340c4c0c0075a20510308010252500c072940711000d6070500540c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 584301411 1250 584300161 584300201
    0x1a06010306180207020f030303091c020303060f06211005030c0409080a0807020a050106150e040c0822020a08010e0d02060f040f0602120c0a090812120c040e1612 71
    0x104042e194000c2084a100820301e1840c4503911010034150b4208682d40c08003900010f500d10a2903225400e01c0308102d909201031403a5282440004070044480600d41c0c0c0030f500301086804c0200c90000c0b45890a540c83d4403130b20014134109000600c1d0742058000d145c002e0140009103035441c1803500400b0003481d84070240a0a0030160042264850b400070500011880350402c101c01203034083c030818000d07048031208050445e500641c09070030415013100da40c3c0510b01d0002e0280005901403441c41c0c108501600c8400c0940c09026007000064118001035800505040e0000da0f2210541c07201c000300801c0780c29110200810242a1b884d200115914042d05210341d0000b400030714000201c4004a2281100500340300c035000d954902d035402100e907240640f600161034110345422201400c000c10200004042807403039409885c106c1d0295107145500151501c010403051540780d4182c40c041c00c01c2c1000c410480c940002c0502d5160401c401f05000f090076520202c00070030319030046208100050291440c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 584302661 1250 584301411 584301449
    0x50a030b01050f030a1b0504050702060f04140a0c080a020a05151917090604023111070b0415050a05040515070203132d0509010b251a06010306 63
    0x101403c0d003c500168076004041c2c20400191171714000c00c100c26449401c04d80603e0501085c84100e403400b9002c80d06540c40b0300100441c2c000302c003c0c070b103601652000502c511304800503403003440c000c12060020210409800b02040066000507030042d200d00031124000c80726512030500c0665121100d103001182c0e010050301030001403245002d850201646130100c10308203207280c0403030110000c0c0c440904c20340008040c44154078080000980300d00780040307403480020f051705144060140c0000003030011511055540c0209008a082e0380c02a03820040e14080c510380b0b441e0202e11036981da00110010303440c000210710201507501c50311b842203038440300400072541000349080c4004c50044c42c01c000c6100c10441c7c004021000440c140040044040182c032082945100c1080d6075003091900c44030740c80500301044030b990741705482411181840b014540c0c803d002e03028050300c01894204c00210a83c0e003e0020100300320016a205080e00d8040f050040d500c1e501c0044054034100c0c07040c00b840301d80b6948600 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 584303911 1250 584302661 584302669
    0xc060a0b092e030c090b0117060d0f17040303080f090d0f121127100905060706061d040203010c0c0b150409290f071e120f060807050a030b0105 63
    0x200301c0802040b0b82c101c080d5881d5039002600302c0641004141c140c55900e8080c0c1c03941c100c1c04410341000165150b0a09241103008038800790707036061015201c400c46031552801d00412220b90996941c02074107456440d516030070042c00407081903901100134141d010004005003004281420b1480042c0e5980410426031501190500c20304882d0314115a50307200b000c0848011b520007815189075241c103d036282d2240c91742d642e2495040d0b0001500900c80701c60b512118075400b9000c0d81c1940c800700c810a454102504101c0011310b201d07002030b4208001020300c0f08101401e2440c1c07502c00c038805ca000b4040742e0010f20040312000d00c440401402c1d003c9500210742c1d41200c25200e4445010003070300018115184d9140c60700d404002e000c004a00d682c0d10070900718645880d034041640988007618a19860400c03800091100402c2d034517013a2429040d5114008151080d0f0484610301000c04040c400c0d004103082c070000a00c0a4811049903200d4410000344a0921341940c074100d070381003440140e03c0c0e0b10b4030040c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 584305161 1250 584303911 584303971
    0x7020607080c0d141c0e0a032a021807120507020106140123030c12010e011703030103080f07020d140706110705030303150d020a090504170304050a03120e030c060a0b09 74
    0x170390b49081d121045807030104420001680c1c114046c3c0c1d00c80324601d401074000420300600240750716079080c80e800c1010240e103501500132903001c075500c04107625540f0340e031003181c00e00503907403403a001c8500308014000000c0e41500a50162400300440c0b101c08041440150b07040900d40d0740e0010a180c0b40b01c11404c501480d50007469010404520f028a0b011881402d440c2c0903100360000b80a19002400501902c820718aa0b4440c144d08071000b5031441d4190713143e0100034041d0f00c503131510883c40020190115201c1c0b00422105a52040b0b501010008a20140307807105564011100095195900c0c03030140200024000200c0d24090050352554841c00d00201456214900590b003040c000d481190058907140001e500406102c1c1d0001040d06292034200d0041d980c03e410300354002428814400030841c0894100c0880b54182806202000d440358000c0c00b4200140c9458468013020421960280e40841c0d46845081c405070b00308450b00d0f80400b0004e0070201950704c0b0809011405414510160305400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 584306411 1250 584305161 584305207
    0x60315020a08041205160b010f0b040303090b07150e010b0103050f070e0f041d1606030b0918010608010e0c0901080708060711011e0b130603020619030207020607080c0d14 75
    0x2040d40342010450041e80d0550700780301c0c221106014000104516027041407140003034090001c1c00c601c3c051464500402c01c0c0c5190041640c0d40350001160020040c691405a0b000c3c9030300482400702c46c400c1030341140240344904005000c0303030902001a21811804074514495803050f00d48205d4802c110051081e032041c071520454010380d0b95201e00c24400501071003203410086101c000c088040f11b69044000c0741d00b0a61114090600b060000d20883d65014640342d13002c64484072400d054001c80d501c0c1d5024000796030000403903502e03210080075002c801081c820421842a114040390742d90f1010243d640311102c0c41560701c0b0b60000e03400300386064443c68421801024000000c01c01d4101c50070b07101d1060405561100d0482e544d0049881c41c0e04004440e0fa40d040a01c1c201002481d00d56000300e44c451080d58010403521140500340b2044500a034159484a90007810442e1511414549121594021a4001c450b4412080600205482590014808407102c0c811500b08010b450058101d1024810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 584307661 1250 584306411 584306417
    0x60f040b0a0b010e030f010501080d05040e0a090f120f17100e10080d09030210080907060e010203070c0b180a030503070803060f060d060f060e030a02270109060315020a080412 77
    0x20344e11286903010410101a0101c4100010301d6500d000341271440e0150001080d018400c003800100011801c800149500c034458413004141e141152500b69890030b65040000c20039182d00b4090281258000390b65085820310b5207410310b810700b900c10403244114089520313442d05c16414001703110942c00c01042035044604a0344801110ba00c0d00081030030000048944000200413100400642c035003020301d4403002e003041c20400c419040460034141c07521201c1c01903000340301c00701d071507407580307034820411100c850f40c109007030302d00031511405c241c800b6901c9003441640315000000381c03080c2d900e4209034000480368840e00441c83c060041d5507005141d00000e1400340c0c440441c0850400503120391000300400681d5040024450381021141340099203681c0041c400c100e0040f80c4486941c0780091802141c5404030b4a008a511042021a030f41211402045900c482ca21000050395a0346800041c1503e104001c0c241850000c980c01c00128000d4144100001c0c034071101140114100030343d4199000c000345 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 584308911 1250 584307661 584307677
    0x6030e0601260d05030f072f070b040602010504060b0111031210090c02101a06120901110417060c0a05030f0402040e1b1f021e0f1c02060f040b0a0b01 66
    0x74031034504007000e0390b040c0401300b00000100503200c003c1014a035880403084c100380e84921408480c2d51074030f9040312100716900a02199414214208000c40c4d401040c040400c1607840c0d4603424028060142640d003203031840d08141d1601c003e5070217000b20114000c0340900440c10803030035480902c0d10040161030700c84a003a4504c008940f0100d1400759648040580d0018581242c0c40418801128082c200c6130700741100d01045d11819030780746402c4409100704400381c10750b140c84c1c0184031401400d0b41d503044080c4150001700010300d40c0768030700904441d000c1401034580558900c00364905902c200300703204002036410000120500081c281d150f410500203040000c00306103111a40f4507100e0311540c1075000c8421102f142c0c0f0289000001880c506481e48090740030540d008030003a598190710070b1040428071580500a000050810131605100400c0d0100c5000325041d80d40008022405c4110400502595001401c03e010179150180076660020200740e15590f80d01e42c0100038614905c41c1c44c1004011 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 584310161 1250 584308911 584308979
    0x31b1401050720060709050609061b0a170f0307050f070501140a0b010504152706030212090c0d06020a0210090803070207051002070603050c3106030e0601 68
    0x9200740d0744034030a42d8076201c1104000402d006503d0a101800c0c0b103a07580881d04110080707502c001c1401c2220002c3c0c43e00c9841e80e40007400610a03018500b0034074031100c5a844084000400002c0800c404c42c001c030198480d0b60121520300416220352200286204410008910103520038030050003420b034150221070600115969250030748026401c6114404281c10074001c81100a1051034030f9020b00342000d9240900c0d000400701482007500d100024085e1886140402d00c2c1c0c498402074071803003103c1070b04004580313440001c2c0c0213401280805001c64100303000070314001000a4100440c0c5002030111400ca8990f9032174001070b40c0101045000c41c080c0941c0003c4600c41c0d4090f410b481c61098080036124a80410000e1928071544d00440c4a40c0740c00806407555500403810105441481c500800c0076580d0300b103a0034080c07081c05074010054804010f001c940082d665a022a03140803004034103089a601c084c22070560b818040340c0822908040f00412090310701c103100c55080c9840d103c2c041803c0707543c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 584311411 1250 584310161 584310163
    0xd0204140625140105240109060804140a0f0303050a230f0a02040b04061110110d152303010b01080702280c0e0106090905190b01110105071713031b14 66
    0x940f580d00c80107507584e104004041100c5000d61001c03c0a08c0c1403220f0514100c801000510003900c09010b4010300c0400d10502c800500c107244900740c004100395241c002a1800400030314003102c440c40690b1402e801b02c0c000450080d00d050000c000002c1110080d00c5201751407600c001c000c0e007500030315a401c03c07002a180e40e02d0000f4000600d000d0310717000030842c441e0109604008045140782c0c01d43d40341c140348006e00701c10503080c1c07070418a441c0c0c1d001030a4014252015103c805d544c100c0700100480b03040030704040a80d0911060400c078150001c0c4094a040c00064541d00020340340a00582c0120b000441c050081b0303614481c0d07840000d54407034006d848540b24034407500e440d508a920801018401401000d070406034039030040c0152807003000207142c856901d00e07080c5105007901121395280c0c40103969503031041c4140da030b0310490300008201c2420f10140140c448241c440c240820341400d10001503c942030044041101d0b40c040e196800303201d0780c60404c960303262181071049405408401e500007038000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 584312661 1250 584311411 584311421
    0xe0909070305071202091008030301060518041a041503050d052215110a0f021c02120105010906051519050f0a091a0a1e050702060d02041406251401 65
    0x10000480344120f00501801c03546c010640380507059003080400c2400000070403641150b10502e09580c40e11290140450032040d20100590b009050050010401500e52156220140304035020402c20001c9681c2107050041c6105c003801e0b83d040032032123420050040d4024120440c640440305006640030070f480701010a2038202d160303000400324050343d10380c0d003000c070408c12104060300910440da00d5a503905000150000b00030300810b14244001c03200d0842c08003202c00181d00a00940b901d03e14031094a008140c00d100e5044014101a000686810407007220f0040c0312120b08110b252040c001859401c5091488a540410604001c500130f17110321400685200003d07559805001890400c034030b000c1350011010b425240808000a44400390001c0d15802c84039403000400780c0c950b1414005907024003c0d036002075017103c0001204042c1c070313000390b006106840e840360030940002050414001e490189081729101240c0760303440c0240c1c3e82c90505030801154850403000414034000c43d80d05007591 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 584313911 1250 584312661 584312669
    0x17100806090a030f0c0b040303020711030f0c040f06061209030903051902030d080c0d1a030709051b0f0d0f091e03120c0e012a0c0f080d0e090907030507 67
    0x28024100080c200740c1d00c035480301034003681c4d8036010864059076252400c0348500508020141640002d6207010050389000740c20303400c100142560110b11646088907280c1900f142d40a104604c0d21120f4803154650b4400c3d10305440c0c0d60390781d2075004c00d51940e5100042c00205415001e01004030000000101c00f0000901c404040b4030b2100b03090480c0f48149403800c043c903130600d000d000c1d2680403c0020609042500c0540c12183d5021424150045089024920206081e5054007801c0008520045e040d04000e004c0c0d84540d10541e04415403100b0f0940e540174046910389444010882c5114400f040c2e04030098100f2842e40008030800c1d01d076107440c01c454a421075038011100c40f4002c1700034180c10485000300b50710341c06414060b8a0302d11070010044d201c0741e400e06060003090008000f0030001560001164a5003060194601882d8146007180007050321440e248034100500129600d44003041c210310003015a20780180d800d8002080110700d000c01040400c15200300c40000000c1030701000a02c0080c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 584315161 1250 584313911 584313913
    0xf020d0c030c0504090b0601030f060f06020f060a0e0307150b1e042313080909041b08070e0406091a0106080726040201050a020f01020d0606030e0105071710080609 72
    0x181e181d0b2422290b0544a0b510640c0720302d140518040100d40802c0d2025407000c002d1800044d404103021510000300056000055844241c40000c100250005450060038200c03104543c165514203084905407100c1140218507604284400d10005a80e40664081220740c0680030551010103408982803c044225004018000f10507108032f9090a201b003444048030304056481c2100c20f03203030440404174060310300c0c0c28001800c0128002d11920509548480a00410030066400d050a1140309074103441e90703080b0b141d5402c400000b69401c0008000003210410858440d142d0350720b0b2112030040c5890042a10f0350f410b4498903061100401c0c078400e000c0d01143e01c41c060241400f42000b4651001d00c00920782c00d8007902e0512200f80c60b007104941d4011342c2441d005070303503580000e030407410107508c8081c1c000658004076000e0415013454000100f44e44132a9420844585030150140c02d0312015100540031905400504144180d0b40c40400d600061028101e26504c0c0d4500b0501c0c940f450859000000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 584316411 1250 584315161 584315183
    0x17070e090a200f060a020102040909050303160c1a0a060308120a1a0d1518061e02180d080f0a031d0f060a020a030b0a03050d090f150c0f020d 62
    0x108111054a00b038103104400081800160400100c1c3c08000c8520009108881c0070450815092007501190007405141c0d009018541151425990329001a164180400205170034511014851000f04c94901e4001501c000070041c4504101c001c000d000d041d50624507203810004c000f25450f4802010f000d06d0403003804000d0f00d0854000f90403508400c42d440c00300c00f460342e4406115560450401d48045e004020301c401c480700180c03580014042540c01040f50701c918814034090244076400401c035100e2515038003080d00c034502821400c0788685544d8080e800c9414007549094200407041110303291245003d60b20706140b10314040d0060f00580d080d0f50020b510740e00d600c2c07014409070402841040c1e2a50082c120100e480040c2034a41d400202940a5a540416141c040c14801e0b0441c2c4283d10000e03103202c404540368101251582078080d4008045411100d000600c40c05a284010413030310303102240d5001402c1040200e8a80c00c0070340c410b9074a48013042800d000750f6100000d0704c0c4a80c1c0320307000d07001d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 584317661 1250 584316411 584316413
    0x408130603060f0603020f0d0516020c0d020a170a151508010b060906030a18080a020c0315011511011107030f0203040605121e0106030b0a17030417070e090a 69
    0x2000200d812680030075060a404114000807050306030291103a41c00e02507120711550142401c14000c0280660045052000f441552040142c43c003181241c2603096541e515030803070034001242039881d0025044021f0041c03c00c00306902c424114031900d40f00040e00d02a480c5a29001d10070101e1024250071aa80c50250564600e20601040014000d0000920840480400041031401130644880c040d17100003000803000c002c0c0f80c1c0803a020010344852000c6031800c500780204a42c0008200c1000751059440b40040352070000744905000e000a03500e481142e0800048240f2141c54001c8403003441503514095020302028001e00c24194803000341c49850320014280100080d22041c946410354000b04002c1c00401d0f40700d4209d80307008100380364a003400d0f1a03100141001c00080c0001e040d021411000102d1600c1d41a004504ca0a1088414800c0d00c0d8a420800c00000005400003006074801c000030010307070200c0c1110080c88260102a5100c82d5943e0100c007480d40c00440b08540f1340d0300074903003880c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 584318911 1250 584317661 584317687
    0x409140d11161a031906091b1e0e13050a0905071a0a080705120a0605010809010605060304110102151801200d1a0310060801050f040201050708071a0408 67
    0x24407865140550305584030302e0602c0d4800283d5401c01c03101c07044507000000030034802994070185040700202c1001c0024540c2c92588000800000f1502180e03410f01d80d00f000c1800307109600281c00c0041b041c25032164514a04001d440c0d400510034095000741c60040301c048040c0240c49010721031912464040f03289980d902c1c1081c10303c0410b070007928104102c412405810780106055034035490307450410804984800c90255a140904102e441c084e4040004110080b10640c0040044800c00e80b50743e410390325800402c03808e98540303000c2c081c2c00507001d20005011440198820304105010300503610305500e45a85400c030340904650b039402c08c280000c842c0e0120042403046082440750700441048418004241c61014030030040e58030040d6407a0b003070240100c048802c400000f040c0003000c072000440079024650242413140710f00c1143c0d51030840042c4420650440f0350388200d9059603940c0c07034070a80b982c0e400c8080d0070881c3c040d0307803001c1494680c0c0b0407001d080071001e0069000e0f900840e16070a04500c88 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 584320161 1250 584318911 584318923
    0x6030d020d0203040611030d09231c05030a0b060403140c040219080613020307020f0f03030c030f090c04020d09020f010908030405060a030f1119030b0f0409140d11 72
    0x108552101d5403407555a03a020003600e054420501d030048441d10400030072451401038201001100d4036000500c4100140c00708079103100010f030020740c5454800c001425890301141d07072518903981d060040c1c070b51199201e00d0086901165540c4005091342083c40400c0080d0042c0c0c200b1501e041d1001a07011307149070204080e851195044901390b181c100314541d180700317080d02500020240028400410003503038400981034801c00b0446400c41d101c1c5000100250ba40d4200030723030005140542400180c4166010040344d1040c4100c01c0080d02c1c54441c8410104180c400402107131060103500f1085c03481d50765034001024490b0030002c002c181c505050040040501180400c68140100c58200f002504800b1041e00c0450303604444040d01c81e40d04c40810344c05800c2450354019413500c2e1a182c0e094485803040602116800e456a10f1031900c50000c05038111350f4180002e99000300c680610100c58070f0280c015500040c230943c14091400358280c02186805552420745001c07406060141c00400010801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 584321411 1250 584320161 584320183
    0x10c0206011211010305181b0a0b04030c060c0206040f0b0a03051806060405071205270d0804020607062306030f2406011806020318010c150b150409050603 68
    0xa041007a0103503555494440f00ca0206241c140b503103d0001480031500d00c0c1c0312016101d1850141c500f9400050362844541c5201d03030322a4410702a91a012403801900015a0300352a031101000c5403180c1402d00680710b10540f81b0007240d00010402c404600d5209100b07030840144251101c203502c4034110040581a42e20042005003080113894211034425000a82d03150403040c07e94000916032a20102240c0e41c06801d1480180700707050500340a0503d44a403010501c0d100c0000010000c242075900d40344e00c40156101000000f18180003180262500c42e005107070082c0300360b40000e000c0b840386840d000b440c01c1b150449440c0c000c0b402c1c10001c071810240109804501e80001400d840d149080d82041c6044595208001d01c2c8281800150aa40100601e002550700071a0f12512244c3d00c98000307680e27520074501040e41e5074035850100c41d41d500504640e020b10340d2200f03c1d4003480c5200d0005030000c10815100e80d91206415200002c1451110001c002501e0f45101c08101413905a003814904024548 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 584322661 1250 584321411 584321429
    0x40b010509030c15040503030403080c0111040501020a08030c280e1c03050702180c13050319150b04020f1b24040311100605040b0f010807050f1605010c020601 70
    0x140030340c40d0750104005142c3d050031101d105503e41034030381510480c02260000c0c2e03094030000070040140040303400503154011545000b40306544800c0d03429011070040d445001d015034020006040091380000145a01c2801d0903c1d00c0d003000c008086440c000542d100e50406404040010480e00a80c482c1c0303a6003205500303540c000340e8404914901e1201d810b59103005810024080b48550440d582c803401c43c80c0000802d4161400c40c140480d40c01202d901414410384c18480c010741c0058076081c04500ca0048905003040c1140503e040e840300c0703031301d60b0011604002d465517503500c4074403a41d1144040c4c580031000703005680c1c0307445420b14004040b2041c000705203050345c400e801c941104800f001040401c02c04003107501d017240e1141d25054546008c020010b01e0580a01d605002001031164444003c80e02d0840c0c007480b02e8a01601030009040d6551003443c0000d60010000f8042030181000701100416680d0252030729100c00004064600c000e1421a11030f516030500740a885d90412106000d4500c0c21 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 584323911 1250 584322661 584322667
    0x103140105070f2a0b0708090a080703050c01022110140906060a02070b030106031b0302120402040b010c02060c0105072a12090b070b04030909090506010909020d20040b0105 76
    0x1070203040000240c1094040004040c4400040c55248180d40c203140c032034a10240701c00741c13a03151003064400115400000101500c001803405000003541e194501c0d00f001010b4548000f5850448156100300480f1080b90b4081149221079000300641441155030b407405d0001908113240c850b4501d022a5000242e07529202016a1041d03684034070003900041e080b40c4040d541c403032003042a810300300c00d40d01c240842440400005480c40d010340008045689180e1901c0c0c010740b02c0ca9007a0102d0058442d08150314030f15800060050906a00608900405040c10011202203600140c540e41c0b00c0714141803ea51034030240a0002d41003401c41244110314174070080c42196400c0c10700100e6000540142005411408201c50740f402a030f03c84000c2c1c159504102d5a035103080c2005c500010094a0032000208452030005010b4254403501642640c0314010b0601e6034038013a03100c0040c2c6003062041c0d0f446000d43c1c40c2c0c000003440c0c2000510200e4081c2c0d1a0524640d0450f0421040790854540941401010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 584325161 1250 584323911 584323921
    0xf030703141006023301060905041103070221090312070b01051c0b07030b0a0b09011119150b0301020c1b0f0d080c1e0106050301060b04030b04022707080103140105 72
    0x1203640048a40c5540400c2440d0fa04248851000b0b1710042d0352910540300c0b00000f10302c05500140300382c250384d000c2d501400401914282c0031480c0c80100c0c0c1040050b008484101b5440300c400c500b100e1074451724481d140c203003140140080d0424426034a003000f5044001142c2d0100729a10462900415003142c01e41a20031024248a015508004005220000d0200020909406980410301c4040c0142402a10544820385c66007968003d01500e40403a103040384104011400240c4880002940c1c05c40080f10702c00c40d40c88090030a400c80100314410b44450780702c01c485e1400d00c058507014040030001c0c00d44050381d01c0b0351074400c1145200b0b42d0007110f0f03820308404140c841140d41d182c4940d00025495070f8409904171242003016020904e052100d09125484241405400c2001a00c0c0d04900030060700743d8481e1108454415840001c3c098000000000d025140030054007000118084080024281d81c40480c1c00000341120b10f507021614a00040c0148515054003209080f43c0200801040c102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 584326411 1250 584325161 584325163
    0xe0a0b0a080c0a09081902031c0909021b03070f1401020702030c012f06011a07120c0f0813060905010e0109140f0d05010e0111040b040306110f03070314100602 70
    0x1c100380c400402c0060018a070328031034008078004021110070341d4010700c03822240f64490b000c5500e09030704c00e100711400002c940c0b220360000c0d03175072502d241c6410201c9480c10080001070341042c082060302c0004001d146690303402c240004e0a10900c54030300b4200c0b405991400700d9615001c109103007826881401a42c0c0140c6001400103000e4009081c03507050404450703030100e0303c143d511030303d1385078442c6903401165081400140c080c1661094640304450b052412055a010301a203040034000700c607081610850303140152440c1902c1400346103908140340c403036140e40d14243e000d450001d0a1124045040001982c00740f03041c8040d00c0c0902e4004c1141182800081c9030388058003440d401c0c44c404c010050f8044d507444107075803485031025001e281a2902c1e41400c500820680e0030715126942482036071388000c500d803000c0fa420350b000080781e2401c041c155140e990007070514540e2040425820001e4000209039103014501c5443e1540d0082a0446034072505e0701040b070080c080307503110500140e0902803190 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 584327661 1250 584326411 584326427
    0x40503030a02090a03150c0e1009090f1104080c1509090610200114071e030203070912110f150d0b0d060c0f020d0906080f060301090605070e0a0b0a 65
    0x1c40d0a0268807000c0c0d5200140e04183d040d0f0000b4001c0d12545602071a4441d030750002c9801d822030b5150344180b4490801800040c050140d82c2100044050720180074001590380311070440c1c41440b200140c4000e484a2130000c1e03a003e07070025a0550f0042c0c401000515040904c592807080e08006c080c20684000086118200054440b03231052115050040c4500d10401d902d03d802141408100150142d00d4400d600915540c1180c1e44500721031000291000e00410b50244038032503a81e8410503620210302d00310000c0d0005010241040601c00c40040c0c03900c00c1b11f480c44c043c02d019100498482000c48108180d5544405540d0b01401642c0c030310b6500c0355640d0003a03a0b190f60ba01480440e030f0320f088000260340f620007540014449031070200c080300280d42c0507007030404001d440d07000ca82403210607860070380e600400c41c4a20b100040d0445c00140c1d85802910740542c000c18040c0000c6200c03001c0d5039804050343c0e03007150448001600016144814541441c0071401000700c0b80005180c00c1c060301c0c006103404 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 584328911 1250 584327661 584327671
    0x110306040c12060f05090f0f040803040507080703060c0806031b010c030207030b161218020d050c0a03200d12050702060d0e010f290906120115030302120304050303 72
    0xa03540d044501c45140290800300d14805004010060181c40702c41c580c41d50441801841c0c001c805100006414070500703901070340035000c0401102e80da640c40d0b686074142c1c1e030300003441280c680c000d841c00083c00c00820012079024500c00d101c082100c40d08800010b2400a004145034425403000007030f40146046194074580804c07081c41c1c40c0c44207040508060b45451415880108080310290802410001c0c050803444110061381c1c0b17045a1208440c1228140c40b0400160401c01584034000001490207403404498903200d1001c0c0c81403038860a0008407401c1c2c05600c01d6a40e08a1844908124201d08100c0b80c404441112031106a42840c2ca50b10850950061000c05001d400503080c000d56443c0c1c8140c8411300078262043c4803d54445103ca806043e803815000806800e1580c00180344441605080ea40d1f00b401080510312039402c0100009450058602508640c401001d1700e0512020301444582c40211004d4a500500e1890005e02c0c045000038421300c00d40c028400c0c000052404411a5004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 584330161 1250 584328911 584328919
    0x3308010c0e331b071404060b0711090a0906090b0a0617100c020a020d08070b013204020c01061212020109030504060302070309180903080603070803040e090309150d0e01110306 77
    0x3e001e800c081c00443d041500c07000e0f042d82c8500c020000c0c0f103001001007202e00f400103607018003c0383d0b40c921812a5500a2001c010000308005030081c1550030721030178641c1c0c0b0144104002c078003109651590f008940b0b0f101c030b050360814250320070081d0700390081c01984014515854a0001c0f0340f0700c2d22200340c5440c40c2c00740b80d61110352603800030384a4520801c800c0d8170540c0c00034210082c1071000e1508c041c040c5d01115003291030340810400007071198038803040c84860007940c540003e03c4555815001380380401d0312101580c403c2d824072102440000034407540b4007a000c10001c031180113000d41003000706000c4804480b0210380c1016900700001e0780c8501500d0440c1e00b1401d002d80c882202d40342c19280c00301141c02000f000e5000d002c4608010700c050b04003074026406a110018147c5174030003415140c42440c050003600c0c1c6d004200405c104200e603804503611681e100d00b0783c0c0c02c1255002c0005c1406100c0001804101000b0840c081e241405110f00d41c01440900700801400c0041c3c1a600c415010041486100d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 584331411 1250 584330161 584330167
    0xa050f1509060321040602070503030f0906030424020a030506060c03041e0312050a18030209061311070c170a030807050d090515011401033308010c0e33 67
    0x750b48082103038003084c1c1c001d280702c141c02021a0680045030b400500c5605c0042c170900d03030b00240324140482110710500e0610303881440c1c007072004140b115962002e04210f03880101282c0110800c1e444291001400702c05280160b40e0342c07200303d0014103940700940040e01c00c120410150514074000000c80d0125030754103100c03d1100c072000000c0c40307515901c0c0d4000350009180007040413286601a0003001001507d45510300c1401c1c5440190010620500000f500722054101140b068a0190076108400e48580f80200c2c1d5002100149074140d00a050111005110150140040124401c841204040340c600800551107035413001040004090402c40070300100140000307221400f43c010348101034200302207404482c03030090b045060400921400c40e1300d40b043f0f02c0351782c0d40750700ca801500b000c0075060f9500c0000c80030001c2101c6c1040007000e4480451070403444000f403c001c0a0050424808190306c070003078005006400d000200c44034801000b541a01002d03201c0080c0c00f03807070046004101801025171 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 584332661 1250 584331411 584331421
    0x203010e0a05040f12050403031106160e0625051540030e0a090905120c0a05101e020301050310050a0605181605040602340e0a050f1509 60
    0x134000c01000c00c045d0030010b00d80c04404086070840b0042040324070071380d2440002e0301c0034258141c8a040988854010f8054018600d000b54407800c40f642a41100520703181c0342c0007501c10103000300d80c0303220701440a0644141c0720109018081c0490b0820a1203940c0000841c9811f0001e0a90000220069444081d01c043c0d0f84408000c03002d4a801070350502071180110501a08000d4508040d80040f00d104072060300004c11081c240703001300c0780705642c410010440e90900d01e0422103550072130664904e4601c1450745502c0031500c10002c1040e45001200c001606994041c880083d0740e110b84000d04141d401000104a980c0300083c10480281d01900005800c3c1c075070a80042c00303072070650300140d8060303c0010320000a5a2203680c0c40d0080c00216504081c0c1c11002d0000c7d211030041c8d1148e9805600002e02401215440c21401c00d145070b03c40c82c1c06a80402600c00d001907841107500140c00b007014810800c0000841c034401e40d030700600c04004070110342c507000c00c10310001d0310107941c802d0241d403150b070100d6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 584333911 1250 584332661 584332673
    0x30f0d110403110301050702030a2a02300c01121d0105010b0a030b0405070e12030409020415020f06010e19060e0103081c05010501050702151b1f0203010e0a0504 71
    0x1000d0311104a1203585642e02e0400c2059610b008076040e100394a020040b84000b40000104c2e4070302c5003151281c07124505489461600c1d503600d6044100c1883c6103500400050750b450400044407061081d0041c402682071041c58045210300c3d05025036580f0508640131a81e8000000380000c10115101040b00d449246d0020030744520110003a00310741c01c01c0f0000c100c900140015110500c803030f039810020040b1060820080c0d0307500362070031004034840c426205010f04020800d02c2c2c00e02c02140440345819174400c10002242c2c40313036000380c0310060361440098900382d06100814008081c28010030300307035040c040100a23220b00076142920a02c00d01d07816a11044441d0802d07401071041414843c1c5540e542d04012065a0240901024202c130145003601031064510401c8c2c180e48040e9601404e01c1d400c0e030309015501d1754035081d6028000003400800319541210740702c1c0501c280603401401540800b510301282e030007000c40801206034010710042c04400180b02d480303907114880341c0700415a0380b0786003802 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 584335161 1250 584333911 584333921
    0x306040b151801060e040501050a030f030507050d0c11061c0203090c0406090b0f09090d1b02041d0709110d0b1c030c1a01060f0e03070f03030306080705010e0102030f0d 74
    0x61900700258225440040da402c00c6114100c0d5002d4a5101c80703200010704100803079000340100750380400300050078008103030715078803d008940c030a0505610740701e225101d0526104500303423180c001400d45d040c400304218502112506601c2c0c20381e44a030800250b45507140072035219a00c1c07101c1666001c000640110020400c986070034401500400440e61128021005841444a0580910502c501000079420310641551099260f04007410503078139110400c0780e0700c0741c1c88001500041c50400c5030380b000d0380d2684100c0003c2520340b035201c110425010785850404c081a032205141c0e619000c0c50680548042003151458401150001503203468000001c00302d915904070740b0f104d01003030076602003015044800030452a002d00e50303900b9054503810364a03081041c24010080004c0780310100100c520300400d41c6c903861690060989100710384580c981c910034030f4140d0082d0002030302c0e0041088038841c1444440003406080c60542a010754401c0040d43c2c0c1d01c10a0b500e00341b0b86030009420b000c110815440 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 584336411 1250 584335161 584335201
    0x60304020d06330f1203051617030a0b01140c070308070f0606060c2013051b0c101404020f0108041103010603060c0806030d090b0c030903030705010903020f06060306040b 75
    0x10941d07402d0f0031103a4041d400240c0d002d8001140125500411400c00b03020401d003050b0790503684c0e545440c903001680c1c540b420201e01d0848a080e00c184d00e00000050f1140514401c68141d400064912840c0000419800000000c2d000d808010091036051900c042440d00643e81c01001d40d035650f50451509641c080d44912029100904c0c0140c08a0450f41c01a0940503241c0240600815050103041600c5903100010a6551209000c10700f03002102880e080b8070f5005c1c0d0364102240c03a50301c80040c0a40382d640100b01c1c582c2140c1050349880641d1060703101d5a419406d055070944818078159002c00c040c000e407051424140f204100c005000c00c184000c2042d03020344003034024002d690340c0307160400203070511050313120104440728001032481c1000a0740203580c070740a90b2070307105c51490f04004091550140780003a10500040041484070f407001c1005002d441d01c503000000d5261801d0030001e04244004610b00342d203030045420300c42c8680c0d0002e100d94001f0340020642c245912078000e040410346901c3c0b1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 584337661 1250 584336411 584336471
    0x31f0503192a08101b0f020307050f030d111e07050f0d0c020a080102031306020d020405150403050705030d02060a05070c02180103060e01091e06110c010209010e060304020d06 77
    0x200745001d021850080021519450121001220604400c2090740d52600405108214240c030140c1c400e4406d106015110b896401a24981a015250203040c800301101c42ca005500c00620000901454800c1401030650b60100900740b488516880c2547ca40100c5441d4007220041654002c1c081e0a001c00c180207070010003151241018198040c1c1500d06244050703109a182410020740e4450600840344a0f6800f600406900021341d41c60000030340040c1000e8407030580c00e1002086548910f0007001002000c92151070702c07a491803520619110003138019901a8000300001200c49800180389a00090a83e20109603031740c0e084001c40701c01c2031480c00a5406105140c262140ca10400c00044c181c078041c11062112842c2205202e09032040707200002c0c00f280c0e00b400d1030b8200760602e501d44c0d19410720505000ca451000c0d080c086000341c01c107011801c0e140e5400140f844141d0b0300300f50b01c4102e00c481900c1103030852826030002402c005180c50082d021980791000180d200803412012614140307001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 584338911 1250 584337661 584337713
    0x7180303090e1003020916021002130f0b16030c1e0b191b03270c06020105060a030b181c030207030207120b190608070902031f050319 59
    0x1060040201e40c103403040880d5050000081035003643c0ca2024482640e030080d0a0100d580c0380c0d480d62947c0d103c1402c1d8010110b009841c50404403a0b80e90004220a501a4041001060030407650034000d44441c2c0c000025120204500c008411081040e400400c1e05401c02c0e1314040024105a69410090741c199890704150446d224200000711003014025204217088102e0343c645551304400301d81d404210742190251500d941d403100d81c443c2d08030080e400400011003c801002040403980130004000071030302802e01c00c109020391642481800c0e44144101c0340344420702d02d1511135260014014040030513254050044980d200010000580c104941103031107103942c216a44002d0080d045103108030018081c03510002101c0c260390340340004981d0040104d41c8039444121101441554194024070341d56101c3c107000410290134400706006100d840d0700941d403441d141d0b0801d486100c02c02d02800c1c050b045c16205026584000840c0c560326031214124034130721b00c601d040c1a4404030b646070269013402c4030a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 584340161 1250 584338911 584338913
    0x90602040e07030b0312030c070f05010c0825090510020a1b14030a1502221e06050a0f03020309010b120106030c05010219031b0206070c05130b010c0605071803 70
    0x1508180b032180803540c0c1c0401400020104240d03d500c58144a8900c60b1800e0010035007010001d0018200180b042001e00011510b0390340301401d4600000500b4082003d60701040107201010580080e440c1c5002680703071039198402c40140101206025540c000c0000d1a0340300c544a008000e0800346980140f0312400c24400015500d003000c03803c0c06401d1646001c180b030f41c1034505000418003196948140103040c1c800c80032248000a42214580640301710a02041040c004048a8800041c144001020100305150810001c20342d8103a484102041070800045021a03800314a1100c102d2440c600036036203459001c03106000d0110680d00d00e03400240c01340c203640380e00015407060f812a44126003042d60150b07214010382e02d584009007101c4d4009104481c45000030f10034090340541602e14044a800064982c0200750342e03401c14041281c40300c810300c170107003c549080082c103100313590091014098200f2810008001540b00034004054640b1003000c50304260051000f83c040da40b803070103201440c42d0383e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 584341411 1250 584340161 584340179
    0xa080613030207060903020d0b060f1e2121040f09020d050a11070b060411030f070305060f0a09181202030d060f05090f04061103070e0111010e190609060204 69
    0x1000d03412805403058920000391603018074000b0b012642c0041c030645aa030110380b121000070700002d25559209070048140e403556500c0000d0800c0f4410700c060040c50b000229010f001d980281012a042c1810007200010b103c05000202425444190007408480050f60540701017a0f0140707400a000300c0700da80c100801c4401903680a0108502145800c1c051034480000c0803085505c00c0d40c60250b168010410a000b15100902407a00050b015200258010640d0513041003504250340c0103101e0440b600c14040000d41c540115a00802d04a400400038103810001901c3c1101c0c5118000155403140c0320300d050441506c4440755400d401520f48403030f80907010002512980305080c04074205207800320100e0500707070381c03c014000e13030f1006450b280d802e0b120350741c600a00c0180103004540ca2a1514011492941b11002950246c0420b8135100300e50746503440050904d0f28260011001c40e0b03d0f00780a502940d100061202e8071500c2c01180d544e00690504103d805072a115501400e442d00010b03001442000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 584342661 1250 584341411 584341441
    0x30e120a1403062d03030304030306090c0f0206150f03070f0303120207030e130209130609110f04052709031c1503020405060d020a031103011d070b090a0806 69
    0x40c0c80c0ea500c004203000001807501c5020644007143c011500c00c1501d0f80d440c6441c540301c080b820444c0e0312040ca40202e4030000389903500440301100020303140c5008010400720390090190741541400c0410384401c2c82800207540c0d0078001c0c030301c1504e16001e981d403220343d8640150035030b035400c0e024013510ba80540303600c4520720710086403000b06c0000d18100c01a4480c9855031080d01c4082e075165560404100040b002c114212a0b41c25115202d07541c20041d241c00e980c0d0b2003a8100c1e0b00030442d840815401e2424441c00d040705e01c030014003800311004003c0000303224103403021a001d075641219071104544a403c6403062030402d07504040d201900b21414092642c5000015003400c41c02d60001e441c14282488550f025035003401c0ba10000744100007004d000501c0c1c04e8011552042020b0948820040b850700000c4a203c6035a20070f0760403000b01c00c036858031410300b8001d401540d01d2810fa841124502039211300d6684a1612681242c0103001c140d525865480d2200713400240340d040e007211060b0601c7c80041c0c0c07102c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 584343911 1250 584342661 584342677
    0xa030f1209050703050309030d090303020a080d0e01050901060312020a03080402060a0c02090c0d15030f030e01020f0d05070c050405010f03030809012a0801050907050a05090d0c06021e011401090b01030e12 90
    0x1c409e40503074545140c8079102090a8940c168040d12120100d40d0f2840c0c040c0c1c01601020a8042d16451801441c80c000d00c1890302c60030380701c8004242c1c180b841c2403550845078801010740440d00040300010200350410300044c1c00907410740705640ea909103400c0071682c2900c103190007940402018107204110600c9405450307045440d0a00308000e004c0c0c050f40c0a2080340901c00104404004280d000c0401d0044455500784001801036a0100c02c500310400e00300a84103c101c804030304041404070500440c2c8181c14003900c015102009a035040922000d22810188801003c00c04250700213803038001c0a400000c82611800d03815540f802c40c00d0300d0084120130ba08650ac0004499000010b403a15001c00968011809515002d19200d1341d918226100e5102c1c0032844d402000141c103032030018480c042d060300140007075030140c00703514191846031901144071480030410381e0400d404c107518043c5100d4030743d04452540400007030410549006038040c008080c41040340e03014030b14501038402200001040c0340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 584345161 1250 584343911 584343913
    0x5060a11070605040501080402270a0204030b090a0c0302150f070807110d0c060c080705100c0207090e03030721050a0e010b0108010305060f0c1e041401020a030f120905070305030903 80
    0x80e20b90300110b6a0340998851103000803049404980581404103c5240d41d076240540703030b00114400e84030245808000c0c0c48029041c0c1d800079040040c05180b0000e07942241034100503000111540c1c9900c240c0f20420300010f441000b2900789031351090090004c40c1c0010818280d01500d0342014240f0081c20b4002d070109555450740303503914030aa49050940315032604c0c0d1000c503900c0441d0801030111030070b01c4100c40442d8034180030007401000c5030b000c1221002c40c0c04030f031074085050884010000e0070102141e01000049090181c0108151800f10541e5440b00d03140c507100c41690200c0ca91080044a40c0102c6503000b46050103000142e00b094002d002c0040c0d00038024841a03560700011910140b003440042c1140d0003150208500d070070301c60801034020b401c0b100307420f0420b2021003548001440c07001030190881e0002408202d8071030518408442c070744090029000170040e0352406001183c2801100703003000803880c1886000b210950010079400e4000d41100e8100c4e840e494100d03607035881444040e100e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 584346411 1250 584345161 584345173
    0xd0323100f0b09010c1103070506030a0504020a0f152a0507050102070501110a1502070203060703060602100204140d031209050a0b0109110a05090a05040c0c0b0a020a091e05060a11 79
    0x2103500340c4119060f03a18113079220b4207460900c1c0c0b00d910369641140b5000c0c0d894001c081c2c00192030b1341d80c840558060411103034000f410713081c00d00c1040720881960380303c008038442070300040221144040405030b80c0129410010001161305892005092130b4041040080102901c1c00040c010005080c10945100303808455200d62a64010b44801040b2044850380360f025005183c002841c860b5082c404441040000d41000304560010f81803050407640040003958803c010440154100000c9052298582085103440e0a150402c42c8410b41c584105000302c203135007040030806214a03c03009403140e40101c10460284030746006030b10b40030b85410030b682d15040310002081e000580d100d0102c5500742c8a4000d41362800c07407007096a20750441c0085640c0900700e414001015182da000d1000c0e41207466a504e076403440540381072182000d0160105580724418081004d680b900b008c450070694110074101c0440152041036208400c90b207400c92900301001040c402203031a00900b8503d1190110340665603 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 584347661 1250 584346411 584346419
    0xc080a1b0b0910020c1e191401050f040b04020409020a0906090c18060827190302060f0106020c01111c2a0c0e06060c01060b0d0e010b030d0323100f 65
    0x205a015000450250350044206c0c1d0920014582e850a50203105d00182c41d000c0142e4201c1d0159500740701815508024480f03107007803e01c034003071140d984d204200500d041071b141416200c42011000c000c00007402242e8500c0f14030250340d28070480100030020340300c05216036902d425810025100c9490303103034080717400b01c1074480d21075828584c0001551420303540d44480355561110f0802d0b0301c0e006251400d098020400140c100385080c4005071161004003005c8030440c449150082c07905100800c080005a810001030003225808a117003803642e5000d18242400300e50020310a070800c15203002004078a824407022103210354112004034203008600000020b0f040f506c1c120040303084488600100068901c45003071040105d11088036405c04400f610150030400280403031401c641c1213030440c041f84940810080118200350141d03e60b00f1554100034808000020042540c52100c01d00480c14580c946c1c0801444c0b00304680903c4681044080d0301515041441c040031110f44507000d50341c10010501e8002c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 584348911 1250 584347661 584347693
    0x714010b19080a1106160b0601120e0601030b0702190506092518060b0d0b0f040b03060402090702010b100806040623100905060f031005040b010c080a1b0b09 69
    0x5030032100d4540142c51a202c4603500da40001d40d01903c00780e401102030120450300b2499070101c6c20b42c1c03840303030290b41581e08005001524800c108807480200c80d0410103464131410020071342d2811079900c090407158544400e0000c1c0d0414113000c0c016610000b076038a100342803100028220b4050f40340c0500351019001030300d46842c2021441c00716891914403c2000b0000c8050000d5031403070810115000280240e00c03452030510583c00407420741196601c500c0e54060031710b00b2008901068004540030014044001d0110391120f8005002070b226982000029140a000b900b180240c590018030032880e203106c0000c081c2c0300c50300c182c4505000e24505000440c81d10410506181062079480301d56010b039410b801007003a1a4140c00c114410001840350004c1e080d21048050915002d98404071502d07031502c840c81c0c0f40000c0d010340c4118400c505112125041ea40c00c03228607040d540e0004801c5644820b2680203850a800b01c000802164080d0b840400500c00030b403640314041e2807500141d40e80a0005d000c81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 584350161 1250 584348911 584348959
    0x4090e070311100f0e1c03020c0a0501020c0d06050c09030102031317130e0711120a0e1905062115180408030a0e0708190b070305010f05040207080714010b 68
    0x118003013007048111221603030088400000c001c3c00105a03074070031081e1100e40041060310400450260340018202c06091500e01e8010000c0c0500b132000340f0000c01031000084c2c0481c1541e60161a0079035880200300240c1c1c8041c215a0340c010003600035540c90515121500008100c11001e44845d403007480d071000b131605002e0072100e40e50343c1810f401c1c45541c20075290b140304100c0504804180720203041c0800300030a09000c41c50003c50704c0000181c030340024078809400c01400341034445c4550006501030056481c1d990340c02c403e940040d20400d03100d50b00c09041c262220280d900f41d4103d100c0b500304005107104d503940c41c650b0131001910a030800c0404032202004249041e2401407081c1010f100183e40e000c002d0340300c14403000000c3c0c212126a565500028100184080c004500b94040c0d170240060112021510760410380c0c61804105540c9492180480c900d12401801d1146070002032100a02c20003500380c880c6a900040c011400244120400c0d00030035440740344030700820302104a01c10f221850040313 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 584351411 1250 584350161 584350189
    0x1c020610140f04021303050d0f140a230c0307020a0e07020c130612050309090705130b0901030605061b01270f17030a020a08060405041a040201020304090e070311 71
    0x211114074800ca004120b05800c000ca070060b00640d091012400203003056410800541c00342000e0100590b0340d01000b070003169800303000380c140300603907103140d60340714020301111202c00c035074070b020480a5180c05005145003c148160704c4c4c008004150010030703440103c002c0000300d100702ea01400303007503031220114445a0b00b218100c0141c4c0000e0b014943b00d051680c0c0038000c081c06e030b0500150f80d5449008054500c80c502205403080d60000c2000102c1d4100040d100e50060702c0342c10a2401c0070300541801c0040c0d401409141c19100b404103290303200707901a801c07941c05060018140c4d91203407810214240d06c803d00500350302466081000940081d101509086d040c0035040e00902241c585a882d440b00802d00824201e801e62607450700b46400b00320000c0035501501e0000c0001d665542a404c2c010f08010015158070f100758500750038000025290204418154005c41c3c010001c2d94441c001070b42940611392000403003d007083c0440c3c552035800f182440c2a24400c50400007921106009c0c48803498404007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 584352517 1106 584351411 584351429
    0x40608102711130608120c0a170309010b0f010f110304030f141005070c15140901020909100f030212010e03071a07230a020a02031c020610 61
    0x4003c410400c0d51100c00c1c408035041c54101d90b203a030789908030030b060208001848540d8003810704c1036004280d04141210f80244046008070181d0340101c40c0d041695103090700544280c500035804171510f00041e540c040705950110400e45000b561007401d00c0b00c502c010311000001510500000c10268411124060703030140000c0703910318101040c1239910400e4240810050741c01e5000c00c1c02d2800310f8002c1c01c00101b480304001c4000050074250090350001d40440d0070040c0c211015001460b0080301940e88422039600c420210b0082195801070007041c0c0741c424004c1000d854800162001800c02000004906444e01c00a6240d80c0c0110340c100c4550b26071644510610a5521800b903100c9460700b081e2a1800c094070b0545a442c07091000d8001a003000300d000e49100c0e01c2000840070b0581c0c081c00702c0c2c210000d841b1a080142501c502480c0c0148503100c00969402d00708441e090072100c500c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 584172661 584352517 := by
  have h0 := BRFrame.cov_init 584172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 584172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 584172661 ≤ n) (h2 : n < 584352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
