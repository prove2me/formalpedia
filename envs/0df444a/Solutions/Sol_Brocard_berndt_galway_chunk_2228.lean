-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2228
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:03:45.959763+00:00
-- url     : https://prove2.me/submissions/7bee613b-4ffb-465d-a0d3-c0c4ae46e561

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 400539568 ≤ n < 400719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 400540818 1250 400539568 400539571
    0x21902070e131712160e0907090b16020a12050c040504050a081612030608060709060203040b07060b040509032d030105011209060905070518160c030c060908030105090f09060c0307090806 82
    0x44c0549500c42d101c56004103500f81080f07105024202c2c203802c0c04045540071911709c04035150340c50720310f03103422681c901c01d1071540300ca00019600c420b0b0b00c1c4011569410381240b00c6040c6110344201d4081c410a0414071007940c0701181c0251140d040b504080011a0266008103850414009580000901c1da0b98001203208030717103a0300000903615007040c09040303410407119411804505180e900309282010080d500d2003903003da06201e45010070410200035072034004442441c4010000e1003189841c041050f40e0f504441d2810801e04006802854281d035000640401c440742c1030401032842c0c0c00e00005440181e230101500c070459075502c5080c400b00d0032a106e0661490f1240d000b500e030051502c0300300700e1500303020218221024404000d04c8400f100d21411512a18042c0c00c00c01498540da04040d9503c010303400015282034185502d581c10400b5100045060b280c0803a550002a201c01e0b034081d0700381008403164012548002c000c0dc5903068014042c590001113450400700064441c59040c0c12303c0e40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 400542068 1250 400540818 400540831
    0xe0307030f08040f030f110111030f01230f0a170a030201320c0f0309010b042901031104081509150907030f06020d021902070e131712 59
    0x40412084209603000c0d645085410482c6080d42c0d1508160701c46101d00b9522104c000e0600c4068604078841c1c44c02401e051126104800007000115240c00400074076500803549015000800781c0042604407102200d44200c452071078004e0514800c00c8140408442c1c1104c4265000b001c1010000d50049820803e540101d42d800250840301658075029080d50001c10340c1d000b150003c0031900ba080c03107440050b800c80000d100e80c0304806071200583d0007140d21601d12428141ca0000081150900e01500500319030f2409480030400705905c2281d019800308031410241c69042002d074502c032590704c01d801508032040c01c1503460303161590301c00c40c103840c2c04412541d89410202120402038140428011a1052444c22040c82c404e803402c07400d02512248035010041683c5040d08810060003d1039060340d2040004140856440d03600010340d200c00c03007840c141903006100b01c0b000480c04060410742940074056243d10724020599a960b00c03140c010b192007944010490070700000780c0c822003403a01c483c018031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 400543318 1250 400542068 400542073
    0xa0b0406170105120a03142809060504060522050301061e050901030f1506090908091002010c021f09020603040803040b09120d0209030a0b01030b010f120203070b070203100e 76
    0x340040200000d03120305a01540c442c8940b40301c0010718220218a10860f958580303003c3c260340d81f0f501e00310a120300520b11541c024141400034080140403160704a6130528460b1100b40903143d580c00100e03494440d0303000c1c034400100240b00c03035030300240a0b445141414082041d00a442034581010900311410796201c071140105c6112203240192010a140380a8075068506845030b604584903407011340301d404402418000300700e0038142c4080e665444140a8005203105000186060401081d56000300c0c0007140b0a501e560740301107103180140b05200001c0d0450f00684011036550701070348402c0d44001d02c46500c01d6150b104d82c000698680005512440c07041c02d906884c0c0c01c090810104072003000303010602540c420526032003007004440076a070f4030b00701c00c1d04056901d0b80e42c0070110342008a440c034020810070480d0000b200b04448080b01d94107079a0400c6000d0450795440782c50711403c8021004c0070303405821003503040c4284e241280003800c4190014080729032a03569482d80c1000c8410340c01800c81d440c1c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 400544568 1250 400543318 400543337
    0x60406050a0e07030c0b030601140304110906270a02040f080d140f1602060d0f0c02011a06090909070e07110105070e0f12100c080609060324060a0b0406 67
    0x80c1d04078820942000104401000303c1030641d5a01031100c141409040361411010000903603076807288519110030780d0f1455041c0d48900b0039160255890780c002a000344110017a000244840c2418030585640500001ea41c4409554041500a0081d0080e01104904c0c0e020840030809015040900e0000c0c134072100100703543c0302440c10041c4044c11910a500100200b0050891000d00280035103030504100304410749000c2c1248000341c80d6124030101a503145052500210021031a0f9100b5051002c5580081c02100721646403260003500c04c1c01080ea100e101030103000080d0a019640e5035000b12200100e900c496219180c10040383ca003100c64000068160f0644c040b010000e010300c0e500440c1034141234648071100303400503031074031804200140200145c4040c65a03207c0100000400c590b800380003000311101d01e020052902e1402c0703d10901034050034001c13803c1400c0c005a8012260644000000c1c0800100038202543d5000f411890b401000c04030081100980360001740001c0c621903c1e18a502c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 400545818 1250 400544568 400544581
    0x270a030c05090a050405120d0219020109030e03070b07060509033a0209090109020a020a02190509010b0f0313032604060b0d2301090c0e0106080a0203091504110306040605 75
    0xc80b800103040c00d4025084c00c0c1800000f0303d001901b03040c042d50400846498036240c40d40c1d20f0082c020141c030384d04180c00b960300031b084550f01903001c0007425000e40c0d201d00c8404806010b16540c1c225511440310b0f800c40800442740407075916400680c110b010704040d84c1c0751a0352500c0d042034801d2080300703041d0940410300310910024145807000341041c0c10954150f040003e46000980324050504c104a031560300080e0382c03071a85100780600555103a00521030300140c0c961240c04407200038a80660b034040c81e4a9800442c1e00300990042e240c150300b40c02c41917444c0da0749122104c4180000500c080f4103005220b00c0d8903100e00280078403d62211101d030813039416482d107401d14100365030b045c0354000c3c0100742030301d00f8501140082c242207140f90243c540740540344850500841c01890410320191206210003004a40c1c80c0c90f402529048a603190344088298546201e038204902c0241e41400341a4071040c81030742640221108a54814040e4400502000100c404a800c046003102c0450741c003690751040181 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 400547068 1250 400545818 400545829
    0x51014191b0b0103170c01051513060302030304050402090a1d0f0a090210081f08030d050106090617220c0807080304031a0c190e090c030c270a030c05 66
    0x2401c814507110055480042d00c5011100e6030601000c0e2050800509810304400c25604440365401c03008003c10143c038020711060070794030f460230900303100d1000c020440ae1020240d004800907290003c01461505140c001080003d600c111029038101c01c04c2c0c1c000141ca0910100d0a142d0701003401c661200502d0840303030801841030000c28960031103250141d12000360f100c1c0710f0070640c800042e080204c1340382c940c00d1003000100801c2c2c9a280380110000408102083e0200c0a40a05d03030b4416001d10007139072141d00c01d56038101c0502420000420140040106401ca80020b68124125021200c005d10540c461026800c89a800c2510f85100701c030320070440d00c0c1e01008802d009110000c081e45c106411a524004015100018030030f0a03002e030004075519102c4d110498010b400030117140684504480390241c030026250b17041e94400d1038414005800c0c07a5641088030700ca00c1c441c5116030714011440c66003044046c4444c40c42600180aa04250700c26140c2480f108003840c060394807058150310344420080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 400548318 1250 400547068 400547087
    0x31104110c030a0c05030c010905030d11091507150609020318010c050d0f0605030d0206040317010b0403030c05070f121e0506130503090402040902090f0d0b0105101419 74
    0x201003003030030060344580d403a000c81a2496143e01385001c141c0f41e071050605506d18010041103043d15481c0084001c20890008000c02c0d41da10284020700c02c280c2621119401400b0301d915580d0800b198011500301d04180750b009207001c92084c62407114487c01512414100c17081a080040c403e6800018005400481d1001004030710f000e00090081d0b009550008020f40141d601441e40b413034403000c01c608225260381001e4090000a42200c880801c900c1cac001b9502c510507101030340410400f400030b0428503e010740311810381d01c04251403460146150b4041b100110b503038000344c40a000d125800304600980307814190007440d1845400c1c913041010b04000c4409951880c1c20b00c605004003e41c03000188007c6400c82d841042c001c8403100500c481e05040d07095201e42c428a039441480000d020624921590140904007400d030b4004103250200c40c02d010303003e042c00a001d4082504c0500402c003602e0070010001e500100c9140600041c00301042940e841d800c400703526a030120440c004981c0c00c0e544651540b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 400549568 1250 400548318 400548341
    0x150f132109051e1309080f070f0308010f0f150201020c120a0228060b0111010c02010c030501061b1202010f1503050c1801120602070803071706041a04050601090e01031104 75
    0x8155001201d030010f40707091303104002c2c102c800da116500764041c030080109940020250842484e914640c515103554002e2a06800b10081020a00049041c220724100310040e10000c21304080340b02d041c01d00d1029001c80200d1400110b41d0200241d036400c180c18085005c03041004442030f45c6820469902a040c03c034606042c000d0010100400c0c040c0c54413000c041c2030781a40040000410b4020100121405804401d60b090b4039803d02c1c00c8010b505605501400381c1451a50b0200702607626a50f040362103c0411411801e018420261540402c903500c1005e8020f0380b4600000503034441c441c0380e990943d03022003409501c001d10030708c040040c132000b071001c100000000c88110384a0200005120607105040c0640804a03869800a90400060b41d0480700c0040d001561641c4034904014010400b4641140700710803101070f81c000c40c00c1800c0c0b1340154000c2c50350034081e40c0e003000707418014031000f03001c000d140074100600c009001500c034280c19000c034040c5000e5100c3d03086e07429900c01404107036843c89685 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 400550818 1250 400549568 400549609
    0xe0c040509151801060b0f03041122050709080a030314010f0302010c0803152e03290a050d1a011413020703090305010c0c0302150f13210905 62
    0x2442e0401c00c100d042c6591000c0960692076003807103000324150052035140c00045000d00000f0340c14051083e80d40285100d54802c0b43d941075000b68070014005903420391504280c070596000c0c2c84954501807900010307031081441c070f480400365a40780440d9280100344113003a00800e6403165000c510701e405407032841c0940700d8a420003807080c0c650b500090600c00a4400035181003008404203040d65200007480c480390718001c0504020441001c214420420700074519041300c1c0001940c110418024081c0c0103030b14041125021031800c1541c403c52484960b983c155034045030450000c12180c3e9556240400c040c05142d400c03440740210056241451410f07000181c1c15044000f98030b890750703104602e9681c00d20100342c1c05625117a080c5415036600b4501e40009150f03508001c102c0d811300d58081210701c0150f01035400c80d000c01149851800a04001340e480007092101500001e544d102c82c107022440003403242030844c1c4072110020f420150307210f00501d101c2c00180092400c02c401d02e42915400341d840f030569071 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 400552068 1250 400550818 400550833
    0x27050111030a0c27120c050d080d0b0a0b2205030a08130f1203050a020a060627060f090c180306050612030a02060601030e0f0703060506121504170d0e0c040509 70
    0x7400f28180652258a071500181707400c100c00c010241c1c10310001080040c0c507001c07442c0034600c0c01c202d640d0894a10810a580380c1200201c20b490901180c008481034a40031500e001012400f00600c059800c0e1551060440f0100001d04c90301c1c200a42140c1900450f4103540755003050781c3e48804007080d0341c401c01c4030200c07020b814012144074602440c0e00581c1810410383c0c0e00400c0344d090b402c0801d140c0c0d0142910b494540e0004074416403801c04403c0980b40c009581691544e080d43c01e040381c0d482d004d08070050441c00c8003442b480d60f407a403011456550508000301c80142c2c00540e6117800d183c5070403c5425544130802d000300360400b03000c00c0c0c40b004520030266080442c1c0c20402540e444000308002d0400da1200c4a20352104414400d08011038407420a03140825103a00740b80003c0e203030a94400e40680d880400003041c8920114050404400350b80d034400c4039440d9920380082c02036981034950341c600010840110107800314400d0b13103504200040a803110819210030030080b10001441c804c010b8100c0d49 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 400553318 1250 400552068 400552127
    0x4170f0f25171810090608010911090d03021509070311040506060a032004091a0307080d080714030f0f09010b0a0b0c15270127050111030a0c 62
    0x10b9280c070044072000c01a07111100c200b0300300601c08240d0700041d0000d204215020341d01d40d101e0b0300c0d02d0a0b103c6503122082c041e603072001c2c100103c030281c0166401815080c0b0000825281035460050018042d204850403402c200c1511542d4510035608500ca690192008004100d802a000000349200300c40c10441d62400d100494003612452038080c0c10503a49840c84082c203880958504420701030020b00d0b0352615101c0c0360b100003c1200c01c008a451070301034841c421031403030001054416a1489800b1384802040c460701641c070303a80302030110b0050190105501100c000d505c40514401c10603030a4110550070840c1985510f26070141800c05540d05001e81400c20751075101580048854a0b000c00c0e94500e0491000342c00c200c8a41c90959018600c0014001c40c5940d4000300801160750440c0d01c2ea5842c014091107080741c07440f100e08040071034580040200300c588080c008942c2401200042181c1a881e107403001543d1044a40c458410380d07800c40c20188541c8180b0041c141c05054504030030744401d10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 400554568 1250 400553318 400553333
    0x12f0718051b1c110417030f04030312021c1b0309080a0c060b0a03031724040b1210021312080f1c0c050712021504170f0f25 55
    0x5008004003080c000780120441d01001d0000c4080700c6000420001413081c507011880c1035206104800050041c3d0500a208240210441f040c916400d55218035040c0780d640d0940c3c0e4400851140340259a00b80715502c55020309085410000f40c0c00350b00010b402c0040c01d41350501c40c8060500d4410146064400000a1040021a0b81980050815000a20443c60410050054407100d00d8015000200000c10950880da85004d59003410241020b00d45d11707003001440350343e00e07400315488a05400401501d54205540041d041d1a4041c101f0307440c0600c8491102d04d03000d0340080c038600895000070640400100d01d01b040300a0074041140c09010100381c1c680b41d0450241130500060690009031440d0340362520b2f07240411010b141d05042c08500d50012020b09250000001502da016210000215a03480403c400041d80c040309070307030301040d280c0313850740c5072a82840c01c007001d8600c90801c0301441d1503107280088d005841d10b022482e541c0e090140820036582c0700c06825240107200c1400400c0009401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 400555818 1250 400554568 400554601
    0xc08090d1206180605030c0d0312050726090d090b0906031005130e1504030f0e040213140f03030304170c0c04060602010f0e060106020705012f071805 66
    0x592a20071041808114403100074841507110101021200722020350180154010004540080301503c04040036001442103c20032003034002c1c0010312941801141451960040340c00c40918a4042035032034000c8401d14030001c1d0504102207151145080100b40c0c0d50030030200b0445405480d10720311040c079002081205004406402e482400040009041103002c1e05052000f0240240411104030498007018024584400040707040d0044082c0340c8410300341e04044a00072a071582d20049242a0b5030000c0721078529944000707034056000c0040b01000d40c82085c1d03950152500c030007100f420302600010408041281d12000b4080e410074010400406c9076440812980c00344a80c4181d612107070342c0360442c10000c007484090b03880340c40e00d50007140c010750562040100c800c00392003c02c50714508601240e5924024420040103900c507400070311065218031207211150034800342c0f081c03a0107100b10580005c0b40702c2800075882c40d4410310042010710b40b18440106c11140f10305081215003408103c21b0781d4200f2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 400557068 1250 400555818 400555843
    0x40b0108030429130b04060e0f1c1a09070806160509060708090d1a0603070302060d020a05040302091e0a0209010903030c02060d0915060e0c030601110a081306030c0809 74
    0x40044420000081c924100e510401135941003552003a1641c1004c02c03e50490f020340d074005060748044054034208884641c094130001050500648034014001c4140c001c1d100c421180914142c808900034030540c2c005d1402050b1000103040c52a041c140000c0c903045000340b07000c0201140d07515681550b5000000c488840105403106580c2e40c0541c20041000d20490004070b8001420955400900c20b080c000c0e00d0a4420224803901640c070f41c0b008060b42c03001c940c08080c0d03100b841000f2036900500c240d4014400d004017414203508061f920b4000520704041103506e5082c01c5240d102072018100007c4800303038410480d08007141450004c0300020f1160701c083c0801401e0180200c00c3c0820f44d90f519003a00c1c0032030412181803050b1030b0f1031300c2d00c4200c84800910b62090300c2d05040020407125070740d840480c4145071301035003641035503a95030044600e407030b100601011500402e8410008126141c004107490780014404c0100149007060041c211000740701180c041000c01c02c14808044000f1808020040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 400558318 1250 400557068 400557119
    0x10801112505030c06040501050106030c0309030806130609060803090102010b010216052403070c050c030705031018020603010b090a1401120c03021b1c050702060f070c0506030a0203040b01080304 86
    0x101e92611030300c0c520603060041c02c0d500ca108200030030440c054101c0340c1603860a03501405070030b81140c802e50a079411004003c0200d00032900041b0642080390003a031080005040c0802d910f595248100100c07000307504844a1500001140025541c09000d80703100d445080c401400c255422000e07103003800a5900817544646620420f4000503902c1510bc0e101200344646400d949041c114806021503082c42c000301e60a02421086d5040c0346000b041030802c0302d030054082c000c2064038146900c010035022072150704d160290320041c2d0250301d03118051400b0b04901c0310450b986920010030040700d00c00b2544140154806100e200045036808010b032600d42e449000081140d0302007030b0f0150042d0041050343e90205000d01190303070003130000041000103000060b0150440d1711100c0f60031542031045078406500b02c2802c210b0010406a002c1c005d001190103a410752285a84030300005070a40d0003603400c1300200750088148018068400342040c01001081c005502d41850500c030b025205810850624511 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 400559568 1250 400558318 400558387
    0x5060d0c060c020303070c060f080624030c0c0a05102406080612190312020306010516080c06070c02041803081303020c10032702061e09150301080111 66
    0x44d20100280c84181c6d9005200d01c01c2039880f0840213004880c40101440010a101c01044440c201030002c800c10110000081c2e41c1d10905006200b4681e0000d400320003a0802000641ca10940901540c42d245208001500046a446181070141c415100000007003000c3d840000116007000a00c403012102c0b0b5050141c0c2c26951140001d030740a54801c3c080145004400100711450200c9016118461094480d1040840f05050700d80c100c0c0000c566040c0499810040c80140c441d003c02c011050603c64507199140c2076511403868109070042e07480401049104215608616003030040e001820a036090b040800021501c0003011340c500a4561303140800c00306107082c2071520074092142548006440704030b801c012000004c0080c8003000a04600c006601d03d900e40b5075960005501c2902d8000304031070700b40700d1256884250340048000c0300c0c034007490402c9840000e44a94083c03101503154011815100c3d0315148056003503c1c1c41e140c8540b01c0700420084801806000e03081e0b00c1c40441d964913440100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 400560818 1250 400559568 400559573
    0x6090b0702090621010203090d03091e080c010e060109061509051306080717060601140a050a030b0324070e010804060b030a1a15060a08041518050705030105060d0c060c 74
    0x180c0b001d003040680d00e0181d801300114051415001180030308100011181c80361031091040f002ca803401e5100610201044c40c0d55180d03d007003444c005020710b008040301860407050301c00c000e0860303580e000c0c42100c50b0043c030010070196034103215004c01070503280c400101203412418000c100101900500f0b00c04c400c1c01446540c1030000c5c7c2e2108018094010440d590f840d2130300c003000c05484d076452510701c039031181e0000100c1d1035125044800589111114290418a100209a6840c0c100407042030415540c0d0040c00c0041d94100402d41e603915201c200852064800302c0e81c0405220028824400c0c0485241d0128250f68064959540940c110000040c1404000000ba007810041c0d00b002d8008944944203010050000c00228001c0090114240820410805005580c0200c0b415200403521000004012502c008461001c6401c07028002800d400d15610800c02d0500c121000e0303d655000403401e111500b002d10429030003100c03c40d61044000c0d0300d0f65401d100e102c001d00036802040040c140c00c104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 400562068 1250 400560818 400560829
    0x1c050a1404080d05030f0c0f0403080f13030308071805030d120615110c1804140a0507080304180e0a030f09050904080304061a0303030a0c02070e070503070906090b07020906 76
    0x500907100550758080d40b1450f00401a1700244c44800c180b9003000045561060384500b12801152140c0c032050401c0e103107031912981c0c1c1e00181c503400e00c01d05041042c0c0003e0300301c1c110740001440c03181d240d50006007000c40009041d01081e4081801c1c40c10003175414130440d5000106004106180c3c600a08030000070101031016000e60b80c028007071122040c07030514032030b1f422000c034610030310090003250f080e01e0180f001c0207802c80c030300032101c10b0100d031000101e8003080c042810840326150b030380d04984502c5100d0351603510313029450380904655040031609001c0c10515a00d40040000b10840c10700c151030010308080d031944c001950050134081101442940c0a00400b030400090100800702c007020310f0700c1d042281b4141c0c0110ba048603400d280040458094100c03034005036082c000500214107503034801c043c20008003a603e1050042d80301d00180000c25410007071900f441084540e03112a00c1c3c0c00d1160001d410361105421417408e1000301d86091110e190b03013000f43c456154046907191001e480c1e4001148 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 400563318 1250 400562068 400562077
    0x20c0d020d1734020d050307170a030b030610060305040311030415080903034804030c24030203150315040b100f0b0d110414031c050a14 60
    0x30700b03214034840507402074024500500041010001000c119410848441c0700d40824124010407404440600c0e6015007800184051507a115a08483c50000c0c103031540c000e1600424025254031078001180340c02c1075418003440d242c00d007054000703020ba0300b848083d6600340042c601a500030140c3d50400241814481c0414000301844a401d1726036454480d40074075540f084166031200810224000f2580e0f040000040303034440c0e04c55842e01d408650076050584041403100c000d412980408035032000706000090714007403800d417802c0d814070383d10391452404240c2d03902c4940c014040b03203541000111302c0848010140c17141c2103070752030016a81d030744030340001012500640076150103120300c4d00c545003400d8182980d14092809410121415651800344410b0b84036140a401688200c2c403c0c10000b00c00950080c001c910a2a100466540042024003075280c000e42e000c0007408042c0401000181010300c801d0b01060310300034040d08000c0c0d4188000d0014440e00c0000401c00191004440b0074201180075076 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 400564568 1250 400563318 400563323
    0x30c0b0a1409030306100e010203071119060e03060c0408150a090b01030803090c033f12011406030f0609060a03170d06050d050a35070308060f01020c0d020d 69
    0x71001e410501e508a640c1d4008a071264050300d41405030b1a0031a014001201e0400c070160300440c58a01c003541c80c48248140410000e41200a010f2200c0540505881d50b102408440c0d07242401d00c1c1c031890400d8584036019001428600042006000c4050007060300300c00320a0720b414898480c0c580114020043c075030381d000606100385d060008810041407200030b5006101d0802110491414513081540b0340c040102c074421034429110329004101d003ca14954010701c03401305c50b2580940b00e412a440550721007004c4203204405440113200307240440c03084801c04002500c505045281000c54000c1854010709a0b52251a00000140300342d40e0b014200c502441c2e000c08101c4034820354591101881d0068915500a141496004902ca050185250301c810f038001009081805103a04ca607200b1100304031200420f05402c0310382203030880c403a03200c0812403042e13228aa48d548840b0708004200b07081c0905040e105803c070007581d400580e0700044003403194104a41c003c1aa03c503c0c80051014291071100 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 400565818 1250 400564568 400564601
    0x30910020a030914070e0a0e0708070b04060207080d0534051e16030b090a0f0c0f06051303060b04020c1005010e1b030a0b0402090603090105061c030c0b0a 68
    0x48036000c0307030325421201c6600d12920b9a0240c0042081c00356403648054020503c140c1c5040f40042c801f06541d0b0080e00305581c1d80420359052030748501126040010a41042018050004040012541c10008071009001e040e002c1c1989041c0701000038110720800494100c8484101c90480105414085a4078244a403108070784903000b0301d00c0c00c2c40e201c5c21032001e440802d07220030394070020100010800e8940007002e284d82003902429642c0e00c880f00607019043c000030b846021003000c0041d0041100303900440c007800341114111f10b402c1007440751034074a4100500300101401130390034814113b8021810740e6400000450007241010120300240a450681c42152040107912214800650b00140c10380c0c0c1200101d0f5900d40d1115040b1a481003900130401310124204001502c15400340e0140d41000002807002d841d04001800040b1150030995261078665501c0f818080a40352000389204410409001c2003015035075030300e02901201c000c9401400da0038001001901c505020781c45034030301c12200000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 400567068 1250 400565818 400565827
    0x7020c01140f03240d0206030a0c091503090b0c16060e2a030106060f0206040b06011e200c0105070b0c070f0b07021204140d02040f05011e0b07020a060503091002 71
    0x115101c08950701002c01504020800341004c0c505101d10703110306258006e070660745141c03100050500106074075044a070408c140c034400440c00350260071156031a442d8568001c04c4d00c0c40c90b818090010031029004014100040004040c400c01c2e008042d0302803904a90000740030003001d5481ea04295510040203440c0b0104030011404413410040b050380038405034020866503484074001d07510010000108005a03000e44009030010b208018201c1d40074a06241805d4558180601e075030410704004610f1012528510318007000083e1651044841e0742c6410041c0900304c600b000207800d6109030103018001c044010300040c010b00b841e4084421a47d44401c050000c1502400c1a000c1010141c5032407005004d0601c4120410022105490940d010031801900b80140b14080040e01180d0710000c981144d103544103030b21800c00751300c11903008100c5810b03800d02440c0741d00310b05040b598441e0005155003205000d00405604e5403100346059030040c3c18860f5890302c0d03d0303801514049003034968181c01400002e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 400568318 1250 400567068 400567081
    0x5130503062802041d15040212071e0f0e030a0212031306090e06130e161a03040506010e07090b03040c030308090d140f1303050309011707020c01140f03 67
    0x3003020140542c000d01c5408041510412030099200301c0c0305601c50481c09200c3e5901c020919880c2907081961000d41080c0e07610401c0c042010303600a04011110042c00350104004142c106011840c04181040c0490010f86e020038041d103000b51305241b000030005c5441c28808540c4082003075002480c0c005100c5040c502443cac0e801c0e03030b980d403004c45e07003015280202c000044e819001c1c0110506880f810055401103a50351424400309110740d0080544c404e868100005151100f440303000ca10001c44e0190314840c4d0f041c1079101c900d0208001100c00448020410407010440114000341518141c2c180441c441d11114800c4032403202e40e4108135991103001040c4010000344030200c4003100d10a484600003640c0b40444140c44d040d0f8002048042060780803404103100050b80105480e0001c0c0f4540c608044000240c910810142c0e00b04580d950b0001888001c00d40e007007a08010210f460490f1107055103132801000303440d12680c22143d414410b031a8000030b0300311a0801580d00480342c100b1401d44030b00c2c045 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 400569568 1250 400568318 400568341
    0x303020904110d15050303070f0b150402191112032703040603020309070b041203031508010e0f060f28110c010f0c1d01180803030916050108011202010513050306 71
    0x9000e620280407a4000840341404412340c0c13003040d000801c40d000031403161a243c0e01c0140081c503461041c1c01ca8500b1102550300d610180121004450400c440400b6040001d011006c40d1100074421303038401d04899440340a00001c903540f00c40181c4d106524881600f8442c40039810440d07819600d401b0106000c204158140d01031417040007003108070f4800300d907280440d9070548524018111400b440c20101c0c400b04e40660807121104000c04c084800043c0c0d9011214215914840308020f144c00034038210406150401c1040d401034958004900b050034400028003081d10403c14030901174040c5181e10070911025484841101d030546034803640c0d00000c400b514000c0c07503086500f00d1514500003042e000c441c8a402c02a0020190449008100c030041005458540020010001701d900f015000304801c8410f101944c061880072005140344c02c1c191201d44100c403c6034000c141040b440790f004003d0307031002500c10b0080580a09004d0340d6451034402072240703035480350041030301846503d040c88240c03240b1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 400570818 1250 400569568 400569581
    0xc092205030f121b0304020907052b06060e0609030a030c030e0910030311010501150c0206072a090b0a0e04050c090403081602031602011404081207022b0303020904110d 74
    0x800c40d0508030074001e032910151350000380d90280d041001c2c038000070052405480189107003940f50158041d10b84040780d400c443c1c44d05856000d841c06440c0d80040003141d4000c04803890070b81084a140d8100409800820b070740b02416040a0100490381054406150298900008041e07006d44085c03024134001007800303110744d078510048001400310b120328500d490041c031130181030350b10101a4507142107981204490070303d2055002d90740424100a0301002415a00e08030201c80d40030700d240c000d80c20710001903130320207806c1d03038001c29640d402d15205006655910340c001040d20038904407082180c40711304040b441e08070740300c2d5a40e4018100b9028041030642007000c0c1846182e5010400c0c03e543c00800d0308907124040c0c20f1882d4040c881459411005600625800b4a0a10400d181e641499070740c412003480c0c01003641d0722941c100ea00180d51003e60500178140081a0520215110002c0b0252032144120f510740b0b00c003070308050740418203856507074a94100844140031040400e84035041c10480c4d0000300f01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 400572068 1250 400570818 400570831
    0xd02130e04052406030709110c0109060b1f0c030302070314030712051608010b0919061d040c121e0e010b0301060501020a120f09050a14030c092205030f12 68
    0x1e103940d80c08543c508520b034580c1324000c081e01800c280740c9014a0100a0a00c0d180a200e210000740480710480c1030921802c200503000301804100703081400180704040c0d401e42121001b03e0480c0d030455045c030740c200380d00b1f9072819418680141c3d283c0345410704940010448000300010f00002003070100e40e581c80340d01c4590b403943e01d910801454880380102c0000b105e4450700d000108940d032004112004291014001a4902501910b07400940301c0b01e00c0200e00041d04844013048440b161003802c83c09280f103c2c0707040401503404100854001c01c018004081600104160544603004c8081c141c904244402e00c0f0411000e050041c4c10442c04158064510074582031300135131a041c0001581c2d0300c0001c0c40c1c200355410681d00001041c04a004460554001c4903200a100c030b408800a11030702c0301c0311450002e012240100800e83d501d0790816007841300d000c0300284200e000c081032100219143d09400500b8043c0348900400c1030040c5059070550107142100503008a000c6030042d5200c0403066403074070405 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 400573318 1250 400572068 400572103
    0xd05030118110423060315090c0c03040e070908062710110702130917070c120c0503010f050705031302130c05041508010303050904180c150f0c0203030d02130e0405 72
    0x103400707070117201c0540004c481e2000a09100240402c06092194000e038202884031105031500c2c14514010b072869000da031100c0c040407162001c0200c02c3d980b201d00c20f00640307441c030041c0c2903501b841d08c0800310055080c14010588111940394403c0c0d00e07030400c1184007241c9200310a0000e20ba0041340c070b0352107070084107080e0701410f4110100c15001c1024864071401650290100418140c0c941c85070754a44c05c055030031105103003410801325042c02c28400c1880c010748510480100503003810241800c0d00c551914900e100f6003084180a00300c5d8104003500d501c23405010031031003002e207140000b44815114404407070302245803035003d140d229402002001924002c2d0101e8000c0d0355036440c2141c11f540b091101400044040c0080000c9140ca038101510035031074a83c003050b29100586904a40c58807a500101002000d2032400605903009004054815800e040c284015802134010035107e00c155045540120341c00503400c000322180d880030f40040c000c090350b410110302d05031800703c1e9039041038080f10103843c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 400574568 1250 400573318 400573379
    0x340140102030f0706090c030507080a020414070207060e06040308030907090b01020f06190b03010e0a020a08011e0509031b0706080f01050117060303040510020a0605090d050301181104 81
    0xc0d400042120801500082254544549601c908000304a034000888480801d10310000c041281003020f00050b00b42d60002d00303400c0126104000440301d07000203013900041c00b0380c104802c0d42d801164010171140503045c4000901200d0001030303c103118980004080510110900c0900103001682005840907014100204d00601006995074500440780440d203920000001d0801000c104030054001c003000d001085240450f00040e0035070301c6501c40072a07607511000d02102940b508489280041000340c00800c010751070b01a4004002c030041c2890700499440304d010810300d80302042102d216403842e03280031b0080d030f400b40707150350700e803000d41c450940020314071300200c1e82064000c03203590304842c8161249100b00c40b1300b140c0310340e618200034030790b517410700085c04001140d407607502007105042800d41c06802c540c1041e103005802c0b0364000c6d004420f5988a01800b00d04c4035004000c036815240d41c8810368441280d030034104400707402c408054070440318011500003050040e03da410082c261001e942882403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 400575818 1250 400574568 400574609
    0xc02010e10060b0a03020c0a0f03170a0b0105090f03070305070b030f010e01060801140109090213090e071d090c060403030309060515010203040902160b0c2107020340 73
    0x642c0c04038040c204006804100c0105880c0c042e6004256400000c0d0969102029503118941156010b1070194086203412450254002280e0680b5912080401003040440c80d0701d0300003496030281c1e40c003550140c2400325034240304e40d4042140c08000c540c0401201c440540301e640d0000b00b6003090b601c2c56004151040089041100060b445046c0c513266960200039a190141c80318220041c615441d06200b20240040780301004c0c0c0c0001c04100602c0a001c0109a1501102030116840511070b001076400c054014018160038600301180441200c40c0b4844030b84868044030f0030201500487c0c0e41c4440000b40000405415070402307103120380100030411a50340c03a0110462520b4050b104540181c004100500c0b401501d98050448a140212098503d000b1951403240c106815920020001d40202e0482c83c03101c014008455004180d00b000c40d024141003030b0280d032f00d01800d1550451000d24098000c42000b031100c4d801044010754545134072003081960300c0481021240900300d0750200f4114801613 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 400577068 1250 400575818 400575821
    0x3050a0e0109063e2d0615011e0302040f050909100504170a2006040f02010807030b0307030c052805100302160303050414070305100c020703021215070c0b0402220c02010e10 76
    0x4c0001d04002410099441d6844a070306c0b1800c205029052080c0c0b079000000d080485140181c0000141e2030050f54cc2e403c0c485c8800060010342e0205200e020001c08114182a01142c410076800c8041d00c0483c894659203000f41c958440c02d00c11040c58800441c0d112580e03540309441c41c20942c8051042103a444000040d03d81710765040701d024040080c03040c00140103512407030b00715600514038a000505003502c180000d00b049015031080c1c9000d4614141404113240112011004240118005016040c01c94110303408a406200f2039204003070350030030002030500a40459881c3c004d1b6010141c0810181c0c60060001c01003500c3c1600c1d041169001c82c049048001804400d890308907000b46150416a444c490181411103115011400350107800801610303032408100c070b200410405403004507110380c0440750503200105060108a40f00003001c021415180e03880d40c0281e019a02c02031400904150801c8100a1001c959010341ca0141448030706903065200d01082602c03482a6a501d041d854103075070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 400578318 1250 400577068 400577143
    0xf0b030606090703180b09060106050909150604090908030a05060102030a050d0207020307031208091c0e1c02090c04030203010f020c06012c0403050a0e0109063e 71
    0x5805a000e0004118a03240025070340c0e80c000c0d55460301080031420380080ca44079208000d41290014031030018880d02241c14004540580100d02c1c0c49820401721200080d02c00744041c01c4901d10089500010703505444071411070703025104034682070010781d003180f504850540c41212081e81ca0340ca484041251903200bc030840752440707000d54a5a0800e045000540002e500190040764188038107000000001d08003800000c00c111180c4410000e850503410441c213200754405104851440d0500c00c0d51515003040c041c1440c42c0c3d0507070751804550141d1342150042e06c4031903c003941c4405a41d0810041d443c81900600a9920a80017031014480040c41001a03010780d2004070165044180140881584c0340c0040d001038203542c0000140a43e1071114030810700c021f40b400e900003040010900c280c560001610320b10340704203280082d03116241234802030210510401d03000030f071003000a07010803001200550703030100c0c07600104c0c0341da10b9583c250720281e540d403035020900c6200c50185d0480001042c0c241645 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 400579568 1250 400578318 400578341
    0xf0108010501030209040603061103250c08031807080c030c0109030c050d08160c0f0605070f03031d01150501080f0f041217070804020913030e0d0c15020307060f 71
    0x44056401e0000640107134010407060364106996401c00404161540518040e0740d10580c00d1039620f0802c40f11a42200071011000c01142a040203054201a4407504060b074141d00040c42645a445074510a0308185080004040c14820605c001c038405001007480c40c0890401c40440380a40805001941c0e140c000c1e00c0050000741040b0341c1000b01c0c4c1040d0948103683c91040100c10300d0803120003a50110740016032008e039811545c0e05018001840c2c1c118150010b400582000ea08041d665078610410300e0100340d000b410180c81d24140541c0080029000030b6600e05039009018420104881d030206902901c6114005030140020410040303254803c640200804c000718240c503a202d413500f44440102c0040b69003001803c440c214451887c020615006890700c1d0b60700795842c1020300411003040409440002106190341500c40000e03000076034242803400980c0c90119030320850400b40100081e50f8030800d030040f41e020103f088143c0c003000400080f032080313804200340c00000985004a820081a1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 400580818 1250 400579568 400579577
    0x503060901111b030f28110a020d05070803071a0705031608060f0406080606011e0e01140d05010b0a0305090304050a060e0f1036051926010b0f01 64
    0x19400f0401c03180c8024003483c0f02c3c084a00e449150381106289500103e00c1c89000355994080c001d0b1026101c0303000749070004520701030604000010300c035900d62003070100091240010001c010b003042000d1114100911542003900d44070212801c1001000d04a0003074a0f22000b518000156154041c0044c1ca00508840c0c203440801e0003100421b80310010054070180d4007550780e8408030320310760302e602400780940501009403666007403409c00500000030702c14000c0c603014101c801114860360300190a01c03180c0302c00d2030100c918001e111448d0702c0d20308c11815240101d505141c00803811a802c2c2000300300b0305005035420401c982c0c480b100f0365200d010341c0c01021b41c0494204420041d95104941040310349500616880150b40d030301000601c0070b81c5003c0c0480204882000c2a1403605582015104403800c48081003004100c4a01c0881500094020503108000403040606a240c048642d40094121050a1080184140038020030054a40b131100388641c00e100740350708142031036506841e500c0b20686a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 400582068 1250 400580818 400580827
    0x40b041109060307050d0f1b03110f13210c060206191113151701080303130f06140f181c0c15060501080c03090a0b040f060c0207050306090111 63
    0x8200580d8006000c1350104801400308a06070301036407180413500005040001a020451105c1504840c0070003600414546440c1c00c0115031001c072000c4551480c01245125034030300175040000c3c02e20a81303400165500c0ca4031802d107800410001e440310f000030302a400307988410f0398503034049992b0b000c1107a00a04c130748440460040e01c1c11458000000c400b030721888240c203000c1015603510181e0116030204800380201039540820030f8122a00520010411300c0d00b160541c18680202d94074400070340164603490b03100c04404213201d906001214290b5008005000d84450703d80c0b0848408402e458234154190950302244031034441481ca01c0c0c0d11805000640328031a280d112541042101101d403c050010b200410f200050328040341c1514808400b1002502600740400117080103c02418040c000c0e4041040c0f0034800000039481d00e6503a8004220a8165034600c0c002d220b110b181e10008200341c0c2042031039250303d600414043d06940f020703806ca4041d9500c0d140c22038241c440d03105600f801d4039001c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 400583318 1250 400582068 400582087
    0x7030302100b010e10030527070308030402030102131706070e090f0601110a060204171204090c1206030308061305100608060d1202070f090b061c0603081602040b0411 73
    0x10000100800c05040c04d000c28407031880070403c8220418101c600003540ca0701048205d55104a251b502068074404008820601420041c0d407200640006805210080b001800310755007501103454590b1001c862500c026900c000b4942c1c1d1001100141c000e074028000060301703a9100c0d8400c419441001850728295403240d4140e40000007002d4841410811425801103082604003e4030441c90301c11040103907594038180550100d404006205c05680d001103a0440d080c084410a9400b40c503007a58001824981a181c140c40201e01c56405082a0b814140000281a00100000e2194074150380d1404100b2050b2042c1048500440f0410b0980305610340900080d8401e90b00140e00802c0641003018004094852841c690250901480140d102c1d0006100ca9102606410001c20424134180314010b08200050b40500912605c0c0c507406010842e814041020360b00504002c0d034101203a01c1e512800004c0d20700414114040c180d01540c00c0400f082014101480342450150b5140c0f10281010040c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 400584568 1250 400583318 400583321
    0xe0d17040b0423010e030c060f010f030816020a030b01081506100f03020f030f1f060504121b0e0105040b091933050406140f10032003180703030210 65
    0x40e00e0450000038943d420400000900c140c005c00b0125070003c0d9160315503004194545000108801c00002e0080010007080075860341240569a220b5500342d21400f0388111039600321840a000b9500c0504294008180080164014107a030303e110b00355003103440d81c4000f0b490350000594007141c01c03010701c026810265100d903885000c03c84032440c0c050310b00014403841c0f51943e0025501440405402400c0c400991200000b4910100d98a503200412070728169001e0500c2c0154458407580040c0140003104000040324514a0b00c140000f06919450701d890301a032484000b4050b0307501581c946480d64104d4a412110b01d031280c100c040031100000f5204010714040c2c010407110034824244001040090442490990040400702c280b11302c8051612040006803111540301110743d1040ea8209901500c0700c0e108210045000da68000c040804024102d00500445100203607800e0401112900741807184011402036440900e407840c004032914105440303826a110050259002041843c200c8145 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 400585818 1250 400584568 400584593
    0x609050403090b180a080615031609180602030405010b0103060605040803160609080f0304021503040f02240d050610030605090103060902060706020408030d0e0613140c040e0d17040b04 81
    0xb13892581d0320125107001c00d080c222690018041a0800b10420907103c3c540192140420b0f021030040c80c4600003d0382c42801d902990090504841d26510b040070348001c00200704074041e5008500715928502420458000d000207140f15001a007080d4000440d180700c2e600341c8050704d1554000d54601034502d00004103a28541104603040b035101d04111011a00f400080c0010013014560380e5900c3c40c1500c108003c03011000313003c4403114814030520001c05c4668000c151465410f07140061039181e400c851004144680d01514450f0100151b10210682d07560042801100261004410700e00100b10a4080c0c4045000311604090020010000b04001d0f41040004500240026103481c109468902c00c1c0c1c2d0007078000e5034403644002124500d14080c0d10441d0074283c0c440c17000c2d22481c10284817504c106925950301800b4200980001c000700310301440041101070b0000c0042050320030346132842d80c60700070241240c0c0200303145582031807411885000c2d8910460303100e040d115856961340d8907160450f41 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 400587068 1250 400585818 400585837
    0xb0a0f060e0307080a030f02010c03051006050702120601080c0108100614130902030a0606110a030504050f19030f0c14010e01120905060c04050301060909020f01030c1112030a0609050403090b 84
    0x14450300081c04d6001882085030090007641ca4520300246903001a081d14196250242094909000c200c10288800c9101007680c1040c13400c640d0303590040c000682c0012100701506075902402c07000040110000502001400d020380b1910030a9690f5a03e89050f22410302c11031000c241100c00850340804140001d000501610100180c01c54490440d07508980040311a402c03855a5841c061050716003103a255004400c0110041c2005002c9170b4004207140600e1180398010400540582e40740da1710b407900c1c1c00901041c50b4010b81416a80c0c00c114240c114000e4050743e04821140740814400030008000d4003095040c0c440d010f519200d840119141d2034000c0d4150000d03595507001b90700142041c00014010081c41080580b901d051004260840d40740b5880202014901640b0000607205d000c107003c1e000c0001d080009030110300501c103a41d8400a09460761580c09042c5200103004c5140010b10b000d8090500104550b50300e41301202c08903402514090007003100c48608005224400c4000c050442 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 400588318 1250 400587068 400587073
    0x309220c2607141c1d120a03110d1a0105041203121b030e010605040b030c04091106190810051c0c210623040f030507020607080d0b0a0f060e03 63
    0xc400c040988594001040c0350802218000c013007164240d4500415244030310600c414540390300410f284543c2d902181e03c5d180003005020480c507c07040d000307906c190a816041c0282944d40c10003101e6200003810025160400f1110180c48009154800d1050398260744058801e88103d94640e141070b10700300041503074981110340b0745c1c941c0200c411140562001890341524041500003080e030b12a400d5440d00e4100700e0103140341c00741500300d950b40010321401604040d180040d50b9007281c1403c0d550491142940c41c0c201d40b001a0505074001c03250802c1401c20001d6803000c10035203c56110001680052054540c4501c0c0f01641004540b00070318100c8043d41314005000f41940c3e148048900760201000d080017010701c2d90b020342c3c00d00c0740038018288001d0320151600410b01c5000540f03910741401a0010300400228004942054090011507400a0700200031540302c540034070305a41d02d40d001400020100f820726001c201a42032101400040c0c2e0b9440002d80c0c1c4003400c182044941400228607240c0c1031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 400589568 1250 400588318 400588337
    0x12090e07030b031603032003031021050d020a0308090105010b0706150302030f0f07242111040305010f060b030a0213180c17010f05010e030309220c2607 67
    0x829540c0c809001540b007500c50032250300e0040c0034001000000c0c20b015010388c00400400c0750765041c200c000c03400e840700b1a58016440c2c0e04c0311100000721813402801007041c450141002c00203500007414503045846a91520711580d80c42e840d8034261103080c420702490074803d010040c00140309400102e902c0c0041c00f0070f00245a03507500024544122144010165000b1200b41981490140300300c401400104035180340145440d40c036419564000028402046800440fa0400b03400740315031f0302650a1260740511841007501610321656100d0f00c400c071000e41c640070f2100c1c074484040c0510411100c1b21041c0c10b04581c0c1e01e50f10315001c0d50220000180e60541c180f000700d0345814106406503480030f03a40c030000d500100c0b1103000d09030750203281e030180e49a442000100703c20000000305106880b420b183c40b80007200d1180100f803450142001070b40e40310b803494a48000c41e11500e1091385001e0140d1605205c0302c03400920070f947c0f442d001d1035041c100c1d20200c2c4224003030f0101401c80c0740c1c02107418034204110 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 400590818 1250 400589568 400589593
    0x40305120106030c030f0216030507080c010e070f150804110d050601080c0306090a050a061a0607060e1002041a0306220e0c01320c030f040312090e07030b03 69
    0xa80300342c11a9010030756801d4200c60895040c441c2105001210404501c0d19551070030001d5058011400101000000103070101002141c00948905034201c00003401071241c10803030262644010300030092401401100094910021280f2101a00b034030303201c0d41f02e40c0d29039803034242030704268069094100c1c00011001c07001403401c000a80c0200201405000d08000720000c0604141c400b40907040b00ea0300000d0038030041100402c007640d030940d0001c000121440441c02c3d0b05210b5061181140d4807520124100060203056003003c1800703103c038002d4800301d107402d2103285c049000b14001c3c200b0706590100900711a0f80c144000b1030f00700c04024004a00c034130712a1111480960901107501509460789010302e0b140a040114004040007400d0510742071008610010107a01000c0d00c510b0480919500f0302c01c0d19102ca002c035480b003242401a02c0c1d844d01034024400d801e034010b210464100e0510b4481c0e10425200700d81ca038050741d52010b5405c8598481d0310781100035004c06149154140241c4202209 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 400592068 1250 400590818 400590847
    0x10612110903070b0d110418050a0917130b0f040b1b0a0c080105100513021303122d020a15060f150f020a0201091e05040f02120c0c06010e040305 64
    0x40c40720b00c0101d80c2d141c02804081065810b80b02002c40c07031480500c01480402c1c0c111094400d03948d0000400205035031050703800f90152080d10b8014084400858074000c60305d02d02c83c002c0c400c0c04625a00c0c0312140d55902601040c51060603800309820320180014410040f12000400f03000703849850010124001c940400d082520700c020490301086e0700001001020402c0c090642c0c0b100e0b81c2c102d214046458800400c1030454070300c00c03031020b0503400110321010940c64114a005180c02c00e40c0440e841c041c0c5074000e17040035a140411840c0c41c1c1d000c44280070791030440e22003c2c09000315034041d1910a0751a660301840e0741c18000c840c13554a41307420340860601d8451603080f00608168a0360340070010000c2e4090002903e04940c0c504641160140c030000d40d804c0300140040380d00c0c0d02030720140c02c0550f9000d01c41c1c0000b80c0d00059030290070044d15241001c000c0e00901031110340c1140300f0f680d0b501d5102e40b044540c400e504a480030798010400401800004081c0383d980140070b8100341b0301d0400c3d294183d04 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 400593318 1250 400592068 400592083
    0x150e031c0203071a07020705092203050c102c21090a080d08040b06040f020d0608010c112d0a0b190207050a061a06071110030203010612110903 63
    0x4005902c046400800d100e4a4150607078140d203000c400200310f060114000b520782d152030040c2c0e80181448030114110f45140c500016403a8248050545603a24900e401410359029034500d041d10f00c42c10414004c001c485100b80145100301000d0700130442c580748114050041d0300d005c0d01d40705010340b07060041c0707400c8030308040610728000392492640c41801004200c02d03110650844040c9034420801220410b400001243e040341d000352051243c1c0e50b032040090064103e095043ea18907002040101100d441600003205441c1c0c2000203000b1050075802c115044000720038952000e6002041c00c01001000743c10851000000c100342110070420600d580c1d01d01042810103d80c0301c4d06031410001d01c40d1420b82140c01441e130213a0309601c2c01406440f050303030316182020094000c96031851107030b064080500c00d0341d01e03480d800f900725500c0301100d0130f0951040601b03a401c81c1c040c1c101c04070f010550318428800c6a05941d800c1d207918949540d00e40d801d0004085807115080c0407003040046c00c8042d0303803c20014 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 400594568 1250 400593318 400593373
    0x20a021911090f040c0b180d060b060d02032401050706020d11071202060912090906180103120206070507020d03111203270109030503011e0e04060c0f09150e03 70
    0xb66500d0500349080c0e031402010341d2200358088400d07c10202030381e40003a115401424100c030010071141b6242032007401040c40c600c2443d400100010106c045480741d8014510401144501c0d84040081e12000e002328013284824900180003017044800140b06580a41000c0031004400600e1107103814526600b917006040541d00c02a04540c100c401036410480e180d44515007101414000800b03160b402d0060050403000c5104c0c60070b0f440041c01d217490711403030300e0100000c411000c1e1003540d503820141081c80a04103800014002c070400038020b54000d4088407085a0b002d8003d44000d0410b840403140310140c40c0307030f030515400396186540c1100755902c0a140102d0258510303025402e0301da200c1c000000300007824800d01da41080c8000c0c001c280c00c04144c034110b4144078030f08096502000045249140c1d01d82121030300c2191003040c0424017a103a0710800707810125480b6011110000002038820444900c01c0a00c5001e8104a070841e01d1711500c3d400c0c044007000340403120340410362405000c0015001b540da = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 400595818 1250 400594568 400594591
    0xe0105010902181f0c050f060703141501091505070501050702060a1505032e060605090108060910061d0315041218090209010c08031513020a02191109 66
    0x3d41440d011599420040c05000300d500b821134401c9101c0340e03100709000c90070203014030003032440c1401401418003074148511012410f445540c03809800c003030018182ca401101d401c1d60900d000514100c0d8400e0741d038010b420161201d0800919001c3c8150380f8100d0204540c0800c0014021400000c1d0b0902401d800788000f500500070710724002542104940c01102580200446c40714200080c1d2000306000010805c200d184880071a4980101260750314130007040e044c82c40c0351060010307a995010019002c501c1e000d90300c1c9540c540b24041008403180064550000078403400f1820403006001d84039548004d50140300394580c40503c480020300f800c00c070845542da011002010007081050088032200c0e020440d042c2002094140700705000f01020f075000d400c9440c1d9001412120983c020020842c0c3c00307522200c8180d580c07801e0b0068008070141da020342c40c084c0800480310301d0b50343ca480c020742d00c0d0403102e5070081909145039401c1074180402c000702501e440354440d400341800c0c0c03110400180f203003051150 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 400597068 1250 400595818 400595827
    0xa05040b070b0f0a141f0f081c08071d031e010b10020a03080f040f02060a1e021b28060c050d0306031109091203130507080303070807050d0e0105010902 67
    0x83c061458a0040c4044019131502850b61aa5420036480e16000540152501640b516569211082c41c5103600000e15000001000103401c1c07400191600f16005059403044000c0f00d0441c059038003003420380f40800070920118103020078980746011084000e00040455071403c03131400c10141d20714440314106105035140c00d6450b040c4c0c108005284400d0210b4070003130460301010746004151100c086d00400541000b000403e0901072504c41580503540c00522442d0350b00007070301c0041c0030303400070b42d0344450340e003c044484d10140c1d4000300d942440c3c0c0c2d005203001030b2848400001c00016020212403034540c1d4070b04003441c019410300321082030003810003511954003d50060400c180703000380e101510303020903040c450301303000081356006c2c20040c03d08281c0b00310714261200b2091a0030441c10618056400d1008004c00407801c840e140c0e03003902c55000e0010b84401f070b9211081980c07a07210440d8400003003800d02d404a040315200310000d010031403003d00d00003810300002d820182540c00aa2191b07850a4004c00e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 400598318 1250 400597068 400597081
    0x6060504080105010b0403170a02010204090518010c0c051e010f06060f090902090607020105030603031b010606090602010203040818060412050312060405070e01030e030714033109020a05040b070b 86
    0x200d0f030790241502404490406165682c1d44c42c4d181c62551403800e60010124407244103a0003501030b900a0310400d40b003485249804410b00407241d100c031040188560a00b560340c80c1150050303690315030345034000000c2c010310402510841a00180c04000e20001d65035000c120260f10154880c8102414040e5540040c1c0101c20400034034200c400e40080041a104200702c0060350348140c00c9a031515420b08215413660b981c040040c0c1103000d250000c082201c40e210400c010020107500c484262046c80d20758900d0b141e1a0a4224200d0004a6004003a90703c04c02003400e800621003c2010803050051149140a0b140c1555403124002107600b200c040d4004a90099104ca52102c016400242580c0400440c42e00360001040c079803110000905150352040d044000f4242441120400c40c0c009000f41c6100608a00c500da4a5100344e81605984804260700d0740d40581c1d044002e00700300c04440c10540500e06105403034000f540b040c4d03065003d0010800001402c2421040a0049280500040102480c0031b6 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 400599568 1250 400598318 400598321
    0x304060506091311041d0c0907030c020a0215130602030a02010f0b0f010804020a08150604050703141f0905151e010f141201081b010e0a12060f060605040801 69
    0x10700260b00c00c854480c1044450074055080022407500f003480ba80c200803c03900030600500000c10401c00c1d248407410b02c10402c18000440882c0204180c642607201e42d1803074811800c4030300805004005030000d100c1c00003d890901c00c46a80301e251007011300c0c40d040c210186540d40344c1d10345d440480581c0002c50840780c002d8083c425000440c00c004800d000390b041c5c1000180c41c030516a0301050500c0b070b045000c501035498444800000d402c0c00000c07500384011012481341121800c0307811601c118100320001e441d041c441d001d0080f20500507540700701e207a1518211101100032103903800480710401c41000596894034060140140302c0c0b02500303601028810103000b40700d0000c1409c0c6410114000c01403856076406108c0c8501085035240851060300e000d2419030180c4201407801100c0401c800021664110204410515441d1440e016403040102c0005499408600c0070050341715080d039208101c2c4040f4044001003151050b54005214480003084004032209500103000042c0c01040610030503009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 400600818 1250 400599568 400599571
    0x209060319180206072604060302090f0d05070b0706090c0603061e1503020a0306050306041112010b0a060503040302101b0906020708120f071205090a0e071e140c0303040605 76
    0x2240b1610008208030b801288080c03041510050080700c40d1151141803807503a01c1502003400c0c40303461240d640c680d2400010060b400c498619407203400580c0c1016041e1900201100d0b40503030100240c062a40b4083c0d2041c031a0308400c000380c2d0510f0701c1c1da02c0d46000031400c03a918000740071903440010f030843c01c01030803c07008040c89018a0100c0041d16003404143d045141d43d8610340006c2c600980e686082039412000361403154016905172140c002840b04020783c4602c84180c100040d17817400c2c2c03510360a01c2c0c0c4ca800d031088444000c0c0c006c03c0d8444184841c900c10b20040d64024080d004035003281e030b0000a003d0441d2480c48802c1c10300c50300b00070503800740e0b50f11980150081801b407009110690810140d6a00c3e401100c107002c0c1d41c0d9800094040c59000c000041d42c400307a170045550103240f105114050402c2e804540c0c3c00c1d1040e00c2ca06001701d50b200091850714001c440c1c80e40c86940d0700d10400c4410f207484c2030625544082c0b0000e11081d8080301d200c64028050208003030080c603102c0c00c00f03150060641d0390 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 400602068 1250 400600818 400600841
    0x717040806160c2607150c23040b03040812040507080c0a05180618010b040603140403050d110c01020408100c0206010608070833122e0209060319 64
    0x251000300b5001c104100003510034202c0d22804213001181140c03000c8400d00c56508010210b24200d040401c60404c0303540031180c11960364680c2003017034000d49a81004850189854080007100344000e00c9a00e40c100c008e190301034485c0310700c94a0000009075103000752104882c112071980c00004207000d191420b00c0380054850003a1087c008207070400000034403100c0521090140201030700d00040c46d9641d2011141000d00801c06038100784e58503808680280d5000c2d019010100b810003d400c3c1104001c40842031086800d551000c1c240922441b4103c054010040c030109001d90074040148107800a1000704010a070f280000c0107506090628101034904001610003550002030041204079000030646602c11910328183c01e00755544410408140800c2c004034081c50b90680101c00d8414080a01510b40c0704101c1e06498a1600503a05940e0741403c034051080c03000d4a1003000342c22103182e484c00741c561581da01c0d000d400c0000c17400104030141c00032079174441100d0801c0440d83e1441c102d841060031201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 400603318 1250 400602068 400602077
    0x924050f0f0309070e011802030c0912060708070c15020a090803041214010204030b071404080d121406280816050913050d0e0409020904061b051c02071704080616 71
    0x40c1f6003c6006140b1a6015140c0c074000c1d00000024400140c2c54115180c560002b400c001042c810001c126549580840780da0010403200000700b00c00f28091030340544101c0d071204003140d98110303000c1c2c1d15000e5089101d9410911030075420200c2c0e009410f00180000e00003d000424100f1b8143c184011860600d05403402c80303900c100000c5c404900d05c034070326583c0822f80f8103110958450500180005114951000c02d440c0584001c480b0303015440600c1030110f02404400b4014544086042d0300e00043c203550481d400382d510040512240100e0044240e25003165114400c01079407402414201681c02d9000403a8260100041c006031510240c5103400c2841411220003241d045d07540c0325900c000e880502c000b4001036060542856031107800441c402540070304580850b0034a464900040c0030241101e01c1d55410300c00d8000e500d18450401d440c0d07003c81050510741d0000e45c58103000c0007980f14071400c0c1c5042c1c0e640c2000407013a204450040005000200041080380350150018644a906610000411 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 400604568 1250 400603318 400603321
    0x70b01081c14031f0308040603020706050a020a0c240203160f0810090207020d021003090b1b04090507020c03061807060306050108040b0907170a0b01060924050f0f0309070e 76
    0x251001c0a83e036005010302101040b10010030714507003c51680368801008850700160110302c043c2e05801500e50148660400c0c45103032034990741603040c1d0080c0000c0e200000c0d084000807002c22580071801c2c80300c0101d03051220704080881d585030b060b45d004603181c4120b1100c5212041c0c0865120303801c59080d041615000309641040c0076000c0d14200700e4800c10800680110f190000d41d03031001c140c140103e500034901d0800c060f0301400500a0445002c0c02c1e42e10300b0000002601d83c0b00c90060006500c1d0001c0340040c0ba16041c2103200c2d0040002900c440110f2040f000210b8154808002d4940118011490112100c1d0b000709450300e002a5074110004150401401700016600810040e411030341c40300140b05190740b42103100d4940000e641c032018040804500305c1103140e0001c200001d4050007862591070aa0300c9010580304203a00d0310840b51f8054109400c01480711150090548500451410501d032205491840180740c00c00d11b9140020b010000078003141c8a820810640201482801081103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 400605818 1250 400604568 400604597
    0x120c14011a090721020a20010515060a0207030803040609050a2f0109050f040e01021c0506030c010c0209090a080307051c0b0604051c15060302010f0c050607030c0203070b01081c 78
    0x300d041c1c1c0301083c000c05030082881b07130110f8014403002c0c034140300310120007030903415a0001038083c0005461503084a445c071800080c05013005070440e0071000082d001031400c0e900d076940704c0c8202c2e8030050041d42c0540c1e48021003c0060410f210201c0c886000d82001580c01c4000c1d80115a101140d081683d55140c03114045c40700c0780d0708801450704440080303c0070100720000801040c007034090711500962039440002e01154841d8401441108001c0ca51403c002e01e584003c281036441e001d454856001c1040403c20100501e00443d18607801300f010400d0300e018901c1c40e6a42c00240e0000d480c0c41001c200e02058658a102e481c11040d0400c00c3e210700140485901800425820302c9140182d41c001e00c0130284044e44038603161114550258420001c82507181c00d46000001071a81e404103e000620713450044011f80d220b00510054550010007604c0d0076150184c05900414885480d141540170600c40600801e4407020228001c1030b0000290050402005440d4041c9000e8400300303040c8400e02610468 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 400607068 1250 400605818 400605857
    0x180109020108060621071e020105040236040503030612011404060c09050306090307140a0c12020a03020916180605031602070302030313090501090603120c14011a0907 73
    0x40244040c0c13144c950b510100c8401141960040404843d103000b02070500542030750040300d51207000d403100740120307460880100403402d0300c100f503034065802406120440060082d60550784100760021a5404034031804403031041980e40111003d071181e400c00700800100e403e100042c010650940700007080010315a200360442088050406010300da40e503400031003414004c41c440d40c040c1c04002c08460507860091000340c0c2d02d0780184400c403054400c07070b9214070305044001101503802c2d0344044418201400c205080018154208080e81d0110b001f55001002d03895400107580940d0404204216249080e8000f412402d42c4030078600502100700390030010503a100040d00c1c2c101070034480368280107000342c00c201d140c410140c0000c2e606010004490040780103480181c401ca400c01c85085c0302c07980c1d0314080c003422582075110240405080a0a0032000c511642206ea541032048900c00b0701156100c1c0d00f542100d1002190381e10b150150301e0740120600e0840403680c0d10003014a00901d80342c522120250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 400608318 1250 400607068 400607071
    0x100506040b0714160e0910050f0406110f04060c11030c0f060c070f08160509060612040c17030702181303140c03030c09130e06010b160204020d0203180109020108 71
    0x10301070080007a00300880c2e1010304c00c10100000c240340d902d07402620340107007051500b4240c80c003051600c120681e200001070f080c000c00d4400c0c0c001001040c40e695403500c0748006000001000140e0000c1000f40d10115250040a000503140e030b43d441c082121454544014561b00c9584c00f14865400641d00b091030340d4605911258501c4103482194070b0301d0741240d29900e04203450b000400b41ca0110400814100300002d111301c1003a00e00c07140644040c1d529030074405482c40594090341c018100b04070040d074200212403030a800c940b00b1100275400750b98075501034103489490060f404c9984c000142c0303c015450711001e816105c0e006800007d80c42d00b003101c165555802d91140043c00e0001d2007a10200c2c030820300e010348031003510487c1502c1d81d9250034210031030030b035200d410914450364181c00501100400c3d8881e12a8520154008005690900700700b08815003001c0c41400f501141d104081006031640d0000d0000701140400260716030801c1e41280d00c80400c40030805210f41e24200340b0740090707a40500303601d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 400609568 1250 400608318 400608323
    0xd020a0b0601120e030d0b090f01240e0a0915080c0a050405041a0a0b1c17030c0d0e010501080606180705090f060a080912120606180a0b03100506040b07 67
    0x1c2040c9110b08850001130022078000340740764080400d500320790818030380025102d60000c80300c051300c50f5100c80b90810603440c2030085041154035403600e1080d00d1040e0801c11034580e4941050444100b00e400080c0303030000b0581056034020740340e00309285020214021f20002d000c914000e0b151201d0400046900c0c40014400e040c81161250082414031a04415111050b41e80440c0340e04c003031034045002000b50080c0000719004503400503c24600344c03d5079030200d02e0341c1d078012000c042c1c0380c03800c800000d03641e0006403202900ca082001708000094003440b07490321811044001080542c9090010f500f0400c0047c0b00034003502444008500f10540c2c0c201150344400e4078100307035071104031410106a65000d2542a20380043e0005030500b41c01d50490a03041c070443d800822181011040148040c840c0a03c21300b04410384601008604c1500d0600e010300b00c1502d1300c1c240c40ca0f00503042800914180f0b0a40c0c407010030000000306104000d10b84d4020900a404280c400d2450f0a20701004c48001c0e100c0c10002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 400610818 1250 400609568 400609577
    0x6040603240e0c01052a0a0b100506071e020411070302060103140a030f050a090e09060610030b01020c12030c070f0e100506190905210c090121030908100c020d020a0b0601 75
    0x3201b060301d002100c0c5101400702160040c242a1402c601c040d8826201b042071500820390014241c0703000380c01c541c903050303100c1502c2c2c03501c002180081c2101c1c07840c1c08040343e019454000e400803442181020f015464040e9004001c5035146080081000011b002155601c3c0c012020311408607401403c280b1942095181c9642c1da000110300480e24040740c0c2c0c00845c1c440303603800c00f4800320410000e1740f00e006890485502c2c5004030105020303421211000541400f60f04001c020f51018034008105020396440756056034504600c21003910304058898100c0f00040f0110740d018040c80010780c400701e900c6481002e541d410360b070602000820a000f90403072281003181c1900c0319501c0e980304040c4100248005411144945d81d200c04079071329100b51076000125803182e942181c00d1441c2c4004414121001d40402e403c954011803880c1220784500741064003031240d5001c0000320160100070303800f041c1a10a034001007990380150000d041829107461030045510008040011070091040d4582206003400d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 400612068 1250 400610818 400610857
    0x506030a080313080f040b04091401060801090207021305040302031e090102072102040c0801140f0a031101021c09210507091d0f070519080601050906040603240e0c0105 74
    0x409084a1203000e50000320301704040380016008811038007820030340e40440b40c1801a46a83c0c0844155031341c0901c294400205020010800440e1a80c0181445400175100a803c91803100302e290a58009603811001603100041d47d1403401810400c0d840d1009205240c1441c1c9441030000030b60341c84403801506e842d482c1c3c102e100300c00070b0703202c26003500800d41c0a081403000721079002d0082c2ca41d107004d214080381c440c09500c08149a113400740301d600d42800e000301220403c60070b40d00ca0f9481915081c00c4a4154800d100d84900b42c82c2c510340c030030981d941007a030b13510040c0e600708003400d8401c2006000b200d4200c5691411000002c0d40420124191202e1810010b82e140d0b0224102c0c1400d17071141c02d20250341c004c12100000070b040c00b14100307055800c1030382c560f0000c080680468001c001c451260080640140300144030314030f0248d072070b181c000718020008100e043c0c0b6502d418240304103450007100b9603840d0010301224036400d801042c030403070442c80241085480246c0042d01c070b8440c00b013550032003006189 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 400613318 1250 400612068 400612073
    0x50a050306011d12160506070221010b060720060f030718171c1b0b04061119120e070506030604020d0204120606150e0603370506030a080313 62
    0x624001d40160000c0110011070f02280c4034a17250344034090300881040c000180401c0906080c000c44060310343c0900080c41d40d91519602000300c54001003a4a407a5407907a10300490303940c03071501a2400c28007400d889400608800780e0380d40303210121074115000c0c0c0010321041c40c01c807440030141c1e60300400c1d0382000c400041c60400844190180c3d42c0100b22032280500b80354481020008000500d1003a4080820240c1d80d48001a98580e030510a0105841343d40d000034400621421507040d04a4803032030340841c038107902e0700741034646030400003130710040b0300249015400e03c80c0e2010070201c44e1401c4100030080090004480b43c0c480301c890003614080c45001000c43c03055100c81e4110b545c0c414520b54115181d540340c0084107029407400c5020f81d0913078203000300400c0511410707080020766940c0d9162082c0369405002030029980008012041441400e00115928040c3c5280e0050960105903050a890021011102190700c05070056000c0c0d40054070100c001607146080300d42169806007007802030f02262 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 400614568 1250 400613318 400613357
    0xa030c0504090c09150509130c0b0a11010212060310090519020d08040f0510020304060206070309030c0501091b080a0b0a05060a03060e03040e010801020a0801030809030106030206031e07050a05030601 88
    0x5030301007080b01c0d29005c1411040c8082c0390b03000e010b030358085401404a417142c61031001850003614002d81240c1007030a00300030303030503a00c0c0081c24401082c2c00d299020b030b44411441c5003260801d2540302d81c0e04404d5010401580707000c1c042d01c5012082d08800304100c40003505c03250381e101020080d05036410035110503003041d586c0c1c8201105885070f015107180d07511502c030b200c05c65280c450307481420b02603e00800141040b900104c103941c191940b603401003c3c0d6584040c0110040c25981c03405906215101806401090007800340d40c0405006d50b8201c210030407003007140a41502c06500600042d080030a2000014200914841c0c003e80c034007401280940b81c000004d52801421382c0700070484d41c0391a80c214484080800617004403890b801c900d642681e6144401420303885040380d488006071025005100042c243c0018010b0114040c000003000d946070f83c04500300e940f080c0d45007545400c50000202d00e401030a402caa51061603441d205040041e5010064220701000e0095410700c20210700d20716121499 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 400615818 1250 400614568 400614593
    0x16030b0105011110111c060303090b120402010c0309081006060f0c0b0c21010e010302040f0501050d02120102041a09030705030307020a1a2703060a0501060c030c1401090302030d0b0a030c050409 85
    0x90041c3d40b41c1701c3c066000d400020100c48c4811000304103d00c600043d002c00050540e0044601c101e400c5045988560044400f100020005c8003807050105000c01c4004040241c14102c2c403a06400140301c504141d406021400000c030090100718102e01018005014810740c1a00803021005650319068904030b024039038909100628111521170000003450b03c400030200381200d0080d031382008034071a03c03920b00d03044c0c0c3d10034000c113600140c40c400b088005040c0000361410b0b00e43c00d40c000505040e00c500e1015400c000000001c40740c03042c0410458103070b1400340719100c0108011002945040d55650100300301603440c0c03185461010444154508001d01001102c0c021443d0301103429403840e00110035200c1c00c0400851901078170a100c0041c035060181c1c81298141c9a0544400480496941d0110b070084040842265101903050044010203801d0051a403818840e0700a1a00d5524481841c01155001c0021501c612000c83d010404a5511144202940c07401c0c1c82c00315404200d42045d040e150070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 400617068 1250 400615818 400615837
    0x5120309010c0306080c030718230f06010c02060306010806042a0806090f0714040506030a1a0306070206010b0901020721150c0905100516060f0b030f03090103051816030b010501111011 81
    0xb040500ac0c4180103410007032849070180400c0f161094881c01c00440d40390541c030000035000941000030600540c000d28902d03a02100090001c5402c0212001d107442018030101d01c60303c04568049644000c0d90003004a6900c42002d4441851a19101901d00450007016022100b405060740100010782c03103079400c4801030072015000d02d5490030040307030b284000c0880038140311014083d070f048812a45804501c0d503000d0611940100801e03401c01021f00b00941c00600b005056115408000415000164417151548540c800210200c0001c0c10420a03a40c0001c0925090790b207040414042140c100604205560007a90091b0341055900001d98503841061084003440b00403107089010803919410010401001700d000f40045510b10341416550780804100c02c1141c0c0080c0121a07a41d48a540020380c011b0455004100d243c40240e0494140541e0841104003c1c0180d1070601c1403100c040c0400e0b005000c00e19001e100c590001144540304c000d0580c664200980340ca0401030224942025114030b0782 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 400618318 1250 400617068 400617101
    0x20105070501110306130e07140d0b0a05060102010c091a03130605150a0609060c060b04020906030130111e04020a05280804060905120309010c0306080c030718 70
    0xb0700f403010956444d00103c1e0781d2842160414000d040c80740c5c040c02402007080c034050003440c140f8204140c441d02c00380003d40181d08466032198240201d20040000c501400000500180c1d0341004d00009003912200d9003101e00340f0400072400c0040c140d07010117600701150740008081d103a48030380411101d096600740c0041c00039801c0c94140b100c2c900c3d01d0f0b0411030380d0310700407220507444550303400b42940d00f91650b20540022501d141c144201040990300000454080180700619000c0008009030b01c0f81c00030b0300b103c45180e0b001c00d5400b100d0000303050056031036009408a2114004942d49400c01002c001d080c5601a00300484400c0c1c000d01070840d400c1a8090041c015034450000b9080188103400a6401001c1103034480941110700068030000b104e861103d9440325141d80d82c540b40d05020701019481200c0511500340341000e41c074080c001440c0503030551b00020a06000c0054020107031152900607900a802c500a1502c0642d40001c20a0071507050360340303455005001d1344405005209140440d05e208 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 400619568 1250 400618318 400618331
    0xf06120712140601080f160804050f031c0b04020f0301150207032003010f05013015061d09190c15200a020a180f06080f0706030b060301090504020105070501 69
    0x20b01070798003002c0c4500000e03600c01c101995008000141c100c4262400080c10311850001540d242c4281129507003c0d0007041121700805e40394040d1480c40d0300240d0342450345d210b07601c4020020085c0780140307980410f04580c203504004075003140382c0b103520040c41000540035085854884d40c50084c4107410040d60000c82a08440e441600c840780c1d600c142c610094071075440d246007421500154030840303050303d400380102500c00c00e03074601c482d540b0002c0c0e520088800100c40e800c000082c1522015846544c1403900c0412030906e04000c00d0444071a18198200e240fa6400c1009889500010081d07805404841c1e00c210300d11b458180781e1103d0480d5000146041400300d00c00b41c034203810850100f804440384031400d54541d042c0c99101d8076080c00b503900941c0300454035010006140c4101894048a40d00701c0005034100a040b80c010486010707500059090300710500c1d00344000b00a2040174002c250740e041c00d0007100a07010000d8035610050003141c0545070341e00701240c15a4403503001d80703820a03070050081110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 400620818 1250 400619568 400619591
    0xe03060108061f0e0610021c0c12083711070b01080f0705100e0409061d07050619020109020d0c080613080d1a13020c07050f06120712 59
    0x84490440f518040036000002401c0c104200c40500b40465040c400c2164460326514100035094104140e068114851104030340f210000e01c504034003010b4180d031102d108142540c0303864a80c00d91168000c100b8420f10f401000300116003a440700d103648800c0c21440d0083d440e01540032040401e0705809080303440c0307882c11600e2406012001032149a000e030071404101d0380e0b251041c5560345007409415506400c40c9004108908100d00848001111401d04240d220610380104048072110b01058a00b192140c411101c40e4102c44d0f00300864141c0c1c100a03100031403d280214843e480b4080d00486d140c40c0b130f041101d041500c00e40c040c034141c9038002c0c150b003130000076400e0461207225207000f10402e0740210004076490385d0902c0781102e140360b0320070011428101124002001041c00744511844030000c1c1500070116511039944100d0000356020041e219000e120080d490a0f2954000901410b079821202026640b07010a50751441000c5041d21481c0d5503004040700c0444140480381690741c102200d43c0300 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 400622068 1250 400620818 400620823
    0x12070b180a080705060a0e03070302040515100806010c030e030a02060403080c0622020d050c03070909050708010501051804061104180e060f1303090503030f040807090603050303070f0e03060108 85
    0xe00d40000c961031010a51503241040e1600254458164003031000c000140d80305000e801c4c03420101c0c4001b826100d4007580e07034000c20309451088680000385000c207402d400580c0b0300900102000749851030a1081403404500180c104142a80013409120316200300100320341c1e00704001c00d10168040c04081c3c0f102e40c0c0f842c2042840c1c0190301464410300a0000188c000c02040500c40099100b0407129124207400340c091000084948100707894500840803070102a45007044208001c0a94010001f003003170860030700a090607500d070403802d4680d041400400050341ea043c5115104000400541e007180c541c1e240c01002400c1e003c5020000c10b40104000800202045404001c003880000c20300413007074076200d61790f141c800032030303501c041182c002c000324100002c441d0403804050301c2800c18025080d115000030f031664000100380b02c1c00d008002010300c00b1030700a010321401080e859809021990455481a8480c007005140b54100000030b940602c042d171260b600050012400b40c10350f2041d5841c0e840594 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 400623318 1250 400622068 400622107
    0x705030c03340c090f0e1507031406100807110a0305090406050d020915010c020301020c0109290106050f1b0a0302061e2a0c01150611060612070b 64
    0x9105414038050103010842150580d511a440070a04443c1d0b0b040c0341c01c0c01300500c0d01c40a0714485665030080c000d40407408000250440004c1d9480341941e1400550003001c0d00c0701e1707042044404540340107000c0035444070381d15540c0d00381007820802030b5a40e555004690002440011020300e1245e104201c0506070414000d010301e0781c0680301800455150801e00440c087e0051000350070080e14030008004805402401030420300516142d041203207070f41c0019003039811800601e0b4282c0d5440c19001e04100c11010551440c0d0900c00d684402921103941c60481110144299002c1c02800250ba560180d001d008030351400a0443c18004003035120f0302c0da182c0c0c4001c13440044000d80325690102340c0c080b12011040c910441d00743d130080410f681c2d80540080b030000500c0c0e58403042040c0208800c0410b107840191081001fa40000a012114050200e000c000b0580c4044103120102c10444603508020480d00ea1004081d118032043c608135a00c000c1c9007609a51106600c1c040206440d002c0348007900105 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 400624568 1250 400623318 400623367
    0x150308030f010603020a1e140409060509010e040332030106170c03010b0d0902030a060e030a091a040302040509100f0b19081507030b0607030806040c030903080c0705030c03 76
    0x5845070b80f0f4050a0b000ca105885000300851103c9204c0c0c0c8450303413414294404012070b440e000c1002035049a940d0703407603041500402500d81d1034600c14000c3d420042041130041000503d4503034a402d1984014254909206c0030f455280c3c0071880640309190400038100c00d05490f00c80c03041e56513070364103002890200340481011182c4030100100e1220548403040d6416a441c12800a16040314103a00000500c001001241c150144559050102d440c610504400c4c4000d00702071aa00c1500c42001004011140c10034287d60804001503c0e0f146042c105031000c0d0b0b5030681d800101a114115020300e45815206510740039070401d06400500b03840b82d001104803000950307919190b404440c500d152290514040e003e4940e002030103e1035005d00c0a810290890820304000441001410202d40540d000c50b00c1900850414000e02c80e40c1c2c1801d00c2184100f0000f85030410440d0345903680206000c801030b080011410000c66000140401402201c10032030400044a940d51140b000542c0583e520f41c601d03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 400625818 1250 400624568 400624591
    0x40f12020405060a06080c0c0f010504030513061803150f050907050418020d0b06010c12170705070f0209091518070501020303040b0c0307030b062b06050105090d030315030803 77
    0xb069050500304130160594072161110704081c3d842c9000742e03181c1c1d008501c141038544246540c010041d070b020b00c280350095000382d46040d601c1d0308840c00c04aa06015500003801c106c01c95080300800c203420400041540d61048440b0050044002164003400d600c3e404019110b02d80380600500c020005070210489106a80500251342101058504280f1481021b0b410480315135481740040c4000c0e0300740768003007414182480101080c1c0c4600c00070280e0122101d0102d42c080484440500607040300d958000d40c0d510303095180003c20b41d03902d48204e0200e0350081c068003a0b1700c0401d0f8042e40a00400411140d4042c07203000500d0541040c481c10000107888401c00e0040c090041425407011003203034460707500312100b080c180c1c4031340c58034340300a51004206804050740d40055904136545e800040c12228618405116003c03060014000d207503060440b00c2060380c0ca04a400c001590f08641030310316800c01110139449404c1141000d60150901c0010032040202d09040403081014900c051409800c0d078a10 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 400627068 1250 400625818 400625821
    0x6010201020c06160c12050a090f08030a0e0105040506161406090a1103101d25031104020702100f080a06060e0f031f020d0f021905070602040f12020405 67
    0x5908030302c161449500036412040006640710440708000003511000d181800801c9007130b4030303071107140d0380174008100008600242949169904c41150000b030210015010800d52030094280da4a103d171030311040511201e0101c00e5810b0b809a0b0a84000b460054000da6035400c440c1401c20700590104c41c211105040c850b1840d00019001483c54840c0491a0060029000540720038595080301054143e161043c2d11503d0000c1c902801204006148045503a141d401c2d100d04680c20305588030b8a0032500001198807140d02ca01ba0003075423003109e8200a440b00702642010104020f8400d0344006034103c0036022000000c0365100502c0303110f240503981e90340c3c4140c0703981e040c0500b5620030744601d10005080c1010b0740c20310300d00520851483c22000f01112104055030451000c946035002e04144070590105003202084d00c0c2c2e000b16901044070f50411031429040564604140f08003400d200c2c20404007103407041c20407056a04407070152042844803642c0c641c2d20b032040064051488002c0307016509020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 400628318 1250 400627068 400627081
    0x1e03150e06060f030c0d0c110615061e070c08030331060c030e060f070e01021f150801020c06010f090b150306030312040503070203120a140901140d0b09 67
    0x344003805000020180d510b801d0081c802458550405020300d078601c4004c220301d901c0c0c102180305842108080f6280d0030580384282c103081e41480c0c4c0040c07601c03039194840801071600c2d0752100b00f111000c1c00009c461440044050400904a004600c1d000b803440074100b002141003400040175602c140c9903480002d0000b0a902d0b0700b800c0c0055000d590364202c50007204400e00041c040c0e000035100c0140c524001407001c02103410603180a40a0304c5082486241c6014070600d5580319240c440014002e0008100c00c00350000350707002c00106480010340321543c6000d9040c0c443e48a0114074003d00b601ea0095440c0c07500d89250b10b864600a12a2240c840074680002844d510706020306c038480d901c000e0550040e01d546e800d02500e540d0006000700c0e0725020070408008604204104a40900d010b44025a1140c00600c181460040441100e4a0300203041c050b1410303a41d4072424a03102c140a0a082d2600c411b410001030f298040c28207501c003542480400c030034000241d258418441c6000881d2100c0b181e8a030130 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 400629568 1250 400628318 400628339
    0x1020706050403031b02130603060609020a02150618010602010209090a090302100504060612060f0f02030f011206020706020d050702010606031803050c10060308030403081b09101e0315 81
    0x61080c0404101d007840100b001c01e00650b182c02446020940726450408990300148000b5604059028000d0359400c3c00e100703219042c46600301900c40a801103180142e1100c0c080e68900640c0149110601c00a000800303903240c4048210303610a000c441c544003175840d558003a01075001090051300139149000040d01c819210700540890300e41517005461411141e08440000c0e0400500c00d0f644030352030700c40001d103540400480d85c00090064000080951a603001a01a610204410001c1074014000e002d0710a07010420b070f604440a80a031410002003d2074560003901541d00040d041c81d101094120600c003458008501c0b031451030380200300c0503444034010303002c44031001510b0b1840030483e02e0704000280244000d0100e00c500b001102c00e401000b4841e50f0503201541c0040b20040800300a2201b09500a2401508078002c5120f002c800740303a001d003001c034a00071420340900c03d090b00d180c14880c8901826a0441a00b411403080285616940d4080c0c050a6568020701f07880c00b00820024159004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 400630818 1250 400629568 400629583
    0xf080c03070906200f0a0510020903031b150f2e05012106030309030317070c0f1509080a02210a030b06041203080f0903161b030b0103050303040506060102 68
    0x15110000003d0503c0400c40e0b5030516440388291075030910400c801d41810800040c0710a40000c401007940b00103501e4854204010425400012401031003030701000e690101c140c1d00c0a11000f148100b01d03210b060070041c07038050001c0408450340f580c07c0c00d010004100d8200d56210705000081e1f1182521005255201e00c28800041c0e070748200900804e100c6903104400f282401146174140c44003d403898001c02d0100d0340141d01c1100860322540c410010180c01000c071107001d030200c40c404001ca03c1e1149018191002501c0b0041000704881104000c00500a4035500c01c0d01041c1410003481c2d00900d000001d9070310060040002d44581c0c891124000c000c140d5650480c00809031290030292012810b401802c4000c2d025030340200280030101d008030501d400151140e01980e00e0894074104248410411038024040315a143c00420060b40e40300d03580b0740500c461550007a6603880c4c6080544240c0000303081604020319500c40c00c07000006008002002c1d5009c0d0b4040e2090f527010b621403500580e41c4202 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 400632068 1250 400630818 400630831
    0x7030b0f15100c0209180105010b18060703020607050304080705060405100b03010c0c1b0b0d0203061f0e190906060210050a050603190501020d0f140c090d021e0603070f080c03 77
    0xc90b040d2101c010705180031a203800c016844008030241b41312084090a50b2000d030000703120341401040265070143c0c1082058082c9070143d540790b01d444043c0d10001d4640000400480c103000000020400b0401c4840480d1240d5030003800fa640ca42c1042c0c6885512030020300c64041c40d0900b8004408503524061140410390310882d101ea40c883d50150390342200c2041d80e40310341041601d0f4003000003446c03040c0800401e1a44806003006a5900e000c004001c1080140340642254091f06082545c1c0c0d6500b1441c840e0510504442c00582030f41d90b14901c610242554000c51181414101d00081041d0000348240388030b180079800703004075541d1880c51021520b084600c15415444206407040907081010110303034017070003040050b00d0240e680c1d84400995010085004207150342e403400600921290401c0350300050028030051034244020005030791048070080c00f074802d00112100042804d150107041400c074201900d6940c4907d40a00301a2008180002441c0810421400241c215049a0840c0d11401 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 400633318 1250 400632068 400632077
    0x8060a0f03020405150d0c15080f01170109080d021b0f06011a19050702090f0108061902090a06050403170406020318030a05070b0415050403120e010207030b0f1510 72
    0x51440e000c0001610000c1c01c040c41751007901400700000c0d1500002d6461060013000740c1140c19190404036106181903001900400514800780161540d00031800d074111080f11400705481e9083c52000f500400c11210028a40080010f20f640410856000381c40c150340f030300c40c0625400d102c1001e020345442d00c48260714000d0300010f005102c1145880d01d903500b01c070050301c562400c0c50000c1421300c2e80101c484210201041020034000e00f1854202062984140300c03034003000c00c80d4902408207a90342e1000e0303e03407400610891900b12418050340c3c160741d0003000041c2103060450b9a120040c0c03c44e4001c6c0015115500902c7c46440c02110344000c9808980c21940207500d00740610f03034074804a01c0b9000003640c0c03600500f034562010610801040300030300300c8102c40315511450401c03203441d010680d0401c0c03000d0000c01d01041011a04a01e0316046041d11402d000d0701d00c0c1c010b00c0040b401d02105400080c1542c4440040c0b00361055000002c134496010ba82108a240c0481c504021883c4001e504c1c3c3c00008 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 400634568 1250 400633318 400633349
    0x605041107030f050d020406030219051207080c1215041103040305030a02130302041a0405070306081e0c0904420e1002070623010e0403033908060a 65
    0x80c80341d41d500d030300000a440c11504011401041741c06036070250344070000103500424000884100d40001401070503890810924040500c808880303c48801032240c1d040c00182000500c1200081c400c64030500540e21004007607103000c019545c1c1c2c49000407103075402180b4013080200c40b601030030700700d901694040e200d0a0035548c07800303101001303940040b03040348001140c0d40f0000b0050f21903000e002d0120040400703140d001e003110f2091104030380d0000c003020101802c000003005180000300b0325280c1c1c4413040d038868800e0361003002d88a14003040c400303501c0e805c81100000c100512405005207070403094070258003040b00050b030400d030310480001c1e020240030302088c002c80011030010b80d06c00c40d83e40758100c0a80f200480701c50703545022a08540003d41d8041d44070381010549051407240608543c140d003500e80555410040c40c1040204020002400d00d42e44070000b20303040031680044c44080d903a40c210b2203a9001c1d210310544038001d0341d0128002003142c003404104980740c013940e04019500f200509850a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 400635818 1250 400634568 400634573
    0x12070302120702031509010b01110d09091508160626060616080319180803060904060b060d1a01020c010e04110d050a0903080a0e0a0303050c090405090c040605041107 73
    0x10750103602e0803070745480f0302903190040410b40c8108501c103c81010001900c02000c400261481d100c800f4030190075000b1a800c09541038010140405850107650b00080c42e6050036410091294150002e46861080f41101241070240d07119503130a646950b075441680b0b80082c2155420b001d40c0c5110a1901c44284000a2140c03c1c01c10203852009681030b9003040c00d80050b140c906030380d071081c2c498240c00c100060364091091418000d41140f030020203102180900d8a86a1034031901010b80481d105045040110f014010b040d040094480c0e0010f01b0705a5851454050030f00912499070304005400c0e0f1a61011000d600218441e0342054040c0c603902c40c0b07100400c041200400c0200404801c0b0181800036a25064440c825103114241003000000d00007114240a040300030028010706520381014900403041001060520043c0d504d41800b094075151a0f5070b0b4021402500c4d44103402924003010002e2003140000d044081c00d00a56003040a42d4581050005607030700c2c102e4035884d00c0000c0016030300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 400637068 1250 400635818 400635853
    0x90c09052422021c02040501030b0a080304050118080d081815060103020d060b070f020f0307230a080102120f060f030307080a0c05031318180b0405030f07060e12070302 74
    0x1040398074407001413501e004034201c0d400e648890191450901c0e0b01103000d00207540c040c8210f900d002011603d07080c480c0d150044480c0c0d42d204600869041000b2a10303d070b148074241c0d103d5000038118100a8070301901c0380035401811540100c441c075030301172118801009141d6001c61005c003041c0c501e4500035502d0b80c40c0801940607500c5100c010038481d5481c1c10000700d880c03801f00a00030b00c41c8145451846503005004020700d10301c0c050146403023900403000411407004401101d8480384291000c0700c06060340400020694019580100c00d02d5000242030340006e0080440c1901c544404c0c51a014540c642d1b5062000700c0d00303107007045a0558001c202c048040b85241024000300c1c2d0880c6040255241c1030b5999501355000310340514200c0740304281c18420303004540b0354814500d00041c3c04100c1100c80f501003084a03801018060100e5031110041405d004050089501d410b16840076180d4408042c0340038001003403c1d5065005c0b9000c0c043c0c0041010080c0021604425050390007806451a20b0300c0950 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 400638318 1250 400637068 400637119
    0xa120905210c0a0b010e01080102091c0317040602120c0408030a08040606030c0e090105061005120a0b06181804021008090c10090503060709051012090c090524 70
    0x1c01c2140500c90000d048408000010b0164494101910381c5e51504540507400c2c071040c0c00c01c585a90060200c140c4640711605c1f03407000380200f00080790381c0301880e050076aa12a003d90760101e0388901070007000107000140d002004200344160445150ba6513030b41c40324400d801140920302042d0400c20000410a105200003078000d070041c400090201e41d00d0b03440c0c404088060b80440200f6072500d00b00300301c201d02071285950100c170641d15900a5182c11400918500c5404020f0200036500004501007102991284800001c06003601e0f42d070b0742104200c0c0d005c2c15a1220003600c00c4003403000900d8242c200e5424140203a0b40901845030946040d681922180030080000e4124446e05d841880195070313210710030b040380c041e640365061460700317000605041c018002d0101c41400300720f907030400050311040c144d08401c1a192610100300002310001c14090140310030702501d80ca0148002203941c850720342c0400e00984086c4160160340d034000c04030f5031412203403400709a40502c44c1c102c644a15170f014490780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 400639568 1250 400638318 400638373
    0x30109020d0e0303041101090603200d181b090908040306050712090c1409100902252d0f11180a150f0807050d0203010b12030a120905 59
    0x20460102c2039034101d01d0f5400440c4d060b81c80442d1560079840b21750b044000d4034080c0220703280a0001903c20000f841107c1007540140e004040000303584030401c401d903440307406254200d504000506101c0d080003094040000a4517005408100c80019105064802c60031150380c410400f604140c55904d86c0402010000c00140611404d0000c2d210140306602c50280303c82e21500064984074208a03400203d4032044e00c02038015040003080c000c24200c602d80d400110741e60310401698401c0340d88082c40039406001c414007100071000800d01e00304100f8054888116000d5001002c00c04204814171032400200000642340785c03000050740c07011032200300c20b400d11140003030443d84864030300c0b00072041c1c102d2003181c0302140c040d901c20441003007440414016000381300d20b9890340b10944c2010103582c1c50344114820140328a20143c00b040c110740703080d00308960b000c40c010046a540e0090b9000030b51207501c000c11650000c3c40e0008005001c00907031082040d00c41d0024024140000f09100c0c07008011241d8401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 400640818 1250 400639568 400639571
    0x30d18031e05160e01090b010c020409050712050f0d03110703140403150203040515160806030c0405041401110a080a0506130203070203210103170f0d020409230903030109020d 77
    0x1c1c0780890300c1002002c43c5140040040c2d1a0719241400c04000c0300c03010307000b581348281000640c8140c1d1b80d1091412149580454002800d1940b5190503071900202d0f41c4a64060384807111a030045c041e01041c0c3c1116129600c060b205d92000011044040351941480707011981424440c16011a100311100180c0000c0c2d400740303e240a85940f00c4140383c041800a0041d026000410003081103804e110041075040034014011035030404071000c40074824410348080c104012000020000d07a010403600f145201c02400810060070103040526645003403a641c8010b5600303100600c002281c0c00000c2b40c155500381c0d40c80c5101303a00c80309281c002514025004690003040c86000285100b0b680c0b000394012642078000710b9031754200d041010941054003a030699000300400040001c01d040740c008890340c82d50b240f80c0c9660f4440c208105c0741d560049804000b141480464040740152840e401801f4000c244405070900c8d5044d8529000014011a241190398006100400516040350054200410090030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 400642068 1250 400640818 400640873
    0x90b07050111040b040303030e0109080414010e0d0b041217040b060303191e0509240c07030f02010e030d0e0103050c0d1a01091a0901120204081b030d1803 68
    0x90718285500300360440809104009406c00825400d481001d0346481600005d0061070400c1c0c4540045018921803659914007500f810a607581c405c007807640d501e0038000e02c040032415550800011101007201c00721121126010b901010314082d021609803041c00e020403919569682d91740d016030800c051310090f0144818080061600150420f04140d090706585a0b9030300140505208410408030100c0000c1c01030811045960341c483c1c01d0007020000500200d20014140031101c202c1510580751500c08500881d000881003080342d104981c0000c2c000d80e52140c2a0001c41c04140e103440c500580c4c4808100c20041c01000f40d4066000380e54014451034401d810100540480010b44092003440e42d20383c4161125503580350380100d9800003410b04401400e200007400e00c0b50300f450b0702c6600315280c148032340324065010110b03158041b10040c10031743c0b0550301c4500e02100b0b042c2d102910f02c441203109000c0c890900510a1095000c242c60800301c5103c0000c0e0343c031b1500c4102008a8150404024500035203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 400643318 1250 400642068 400642091
    0x182106060f011e0206090706050f090402070305040b0d050f0c09100c240b040608010204050a03081602040f0507120516054503030703270911090112060501090b070501 73
    0x48550074003609401420451801031b02c05030812038244c1080051101c1442000c0d0300001c070b40240d5800800a840042e607554240c03c0607540c7e03014640c0060030411002515040b48400c9401850048003041c0001040d51101e411400160282c0f1003c0758200401034141c3c400c02d4418901d10700c007503003d0b440d084001010804484c0c940448860203154294891f4820341071810144102c40c014802800210b040c03600b008002011401c0a11000d810302c280421280140040b045c454041d555000b00108411248585008041c103811a042400304d03010b43c400030091181030140a11800c039044000c1910500050196000d42081808a600ca842001419202d54009600030744240072502c0072180d01c850804140d0031b13501030320a0719000fa0424410f00d40007a81001c2d01001440018405405035090020403540700c13030071584903141403410540c0356210040140020803e0b070b0406c0e60340d403540b10f080c1c0d60303100d00b610703100d00c60640043c141c450700300903c0c00d215000d4980e2520450001c01d0012904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 400644568 1250 400643318 400643357
    0x207031e0c020a05090f24041505090604050c45150f0a030203130204110d1401030503040302060f070f120f02150103110307030602182106060f01 64
    0x480021010401e50100e001c1076190a110741e200600c801c40f00041d00c1e24150160600e0058041d150711f007603017054040d40c3c82000c00c2424542c04148080c004000d10800c2d46002e0110b20039a114107401181c3c0d00300460100e0800b40030381440f40321240c0860346810820000d0030141a5402820081d049544182400c41d080c1e54001100000310020b17a5041f00c0801020010b03444c1410301e00001e8001c040081c00a603c0601d82502d030303120740c0c0307040c01a203d5540c1004201c01284440009500a00e842c041d01d403402500c0024080e155441c843c00c0085085140f24900608000c0c0809445a0b00134802000189821030090030760240c04031131a03040401690300c03546642c400c4202205c1c003500780c440000005500c080d1038512981d941c0300034250140002c05442c10701e1030600014200c15010900d142081c0c90400c411802103038807000865803142050555069030840031a80f511400c0044c010940c10000b920001c031510420a01a0149455490411003a10380349a03807241030040b00000380d2040da03041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 400645818 1250 400644568 400644617
    0x20c0405041b080316110111100e060105010201060605090d060b12030a08130f020d0611040602010f0e03041d0406182301110d050a0b031204080105011203050d020703 73
    0x4115009150119121a0014010b540c024146a80c018070124105407443c185c001400c83c1c206411441054131a0012240002c4403a034040703203840764030040c50002d4880e5221104400d107c500380d503603503604c0f41d0049081e100548a0030002030800d1201c20010710f00340308001042807041c031000035506202d2000c14a030400d9000400c00a4001003483c20202d030f042100268002c210307002c4240010020360364655084415100a4020302100d500c580421040b40d000c08d055000483c900ba45595a90070000e010344201141c94140c1400c0c6030712010022070020a98007070303400441910b00711602e103408080c240d6100074401d440250f210300c0720b65040900014a2558540540c00888a14101d40c14001c89440880c00c071640d01c0c3c0c9840e0b0b032440400d0000f01580c511440a41e03001ca095110f003142c481c040c005c41d502040e41070086840d4050741d0f017040c80060080b01d070b04070020b0000e42e03640d07800100c00421203180130f404030b103080140c0e82200d08640d00802165100e410051900d55008008075080200c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 400647068 1250 400645818 400645823
    0x5030c0d0f1215030c1e06081009021c06290304031704050309151209070602060106111501080c13050c0f0d090605040320060108100c1b0507030c050409030e10020c040504 75
    0x1210035030808406a0710f40610140205003230035009810110300111040e0010311501423100c0d8089224454419140c050780c0300c441d080b400601a04da00c56804001c4869a114980d110036040c3c1906c0107088101403e503803090341c040d150040402c00c0d5032000101c2480082044030f01b03000400015882d9903e001a0204038400310b650f95460b0111070408980c0458003514103491350b4409401000b649a0000d41b103815501d00c0d1414004800c001c070285840d02e050710040080c2c00c0710500003c07808000000328801010421103840b01140b00c15a10300b001c0b5401903600f64219070701002440b070440c04407402000400c0002d50001210100c0d80c840780c0445d6820f540880c001102c1121410401c0854581101c031400010064841d0f5454480d840740d442c104240c100c43e10584510318a28954000c00c004101c0c03122200800081d6125850701c66207600860100312501c280d1101d01181d00e0404e03108500074240c3c1a118070358448130340020840000d01d075603030050440c410180e9a8600e51214010903000c0c61 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 400648318 1250 400647068 400647089
    0x20a030c03030504090605030c1302090406080a0f030f05180906010c050607020a05161d04050102040f030b040201030606090b030f04050f0f07140405060105040e0a0f0905030c0d0f1215030c 83
    0x1401c05c1868016990b00e640051311a50000c11b0045c2c4981d19100e040740801028900141d4421518010030080c0443d54868007050285031521b0b000d0101c061110f20500b846a60b402c0815001b032142030b80d142c0281c880c0d03401107464800010344203013040303244585c100308141006030800110b69140d91805404491040040e007011328a0b00800078104454000381c050350aa5000c918240035600710300c085010a1000381c500b0760400704d400d00070290704070b034041d100c0e42506040301380d01c0c1d041580209406403001c0b80002d1415030002040ea03c103019410030384d808604247d141d501c451404000302e01010384156528042c0004260b541e002c20000e00d461041e02c1406000403e00e00071140040001071003e06008604100800c940340e03901130100c40c150703074540710030740310948940c4c4942004110555528451514088852050042c0040a031001070301d003000300c0b01101c03903810003261f01da01e03040c40590124001078825050aa805d80008030013a031111200031081e9500e84509a4000d4a42d0158003141d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 400649568 1250 400648318 400648327
    0x51302210d030c140906071713090203010312030e010f05090d2007151e0804050d020a050607030b01020c0613080618100c022d0106060c050613020a030c030305 70
    0x1028000481001d4450804106820000f0000b43c0442400541c038134a4050004c0e0205460750b814042d2011190400006403440050030b00400040d40621082d001c000d41484000800d056540220381c1601d500c120040350324080c190058002c0c00c90f07400e89824654940c0c02510100107184039503845401501e008040c000c2c90507101512031510308441281ca0910b40549150b00340000071803400b07c03050b07070041814120b401502100c4000804096502e241071035014086660b80c09050540202d019030f00307580c82c4081011050340e481c9400701008040d504090005031032603009900126107000c060040d2140c031211000000c010341c0c0b0800c11202d111180c09000e12015a040000e20f52110384040d20704d01000507a80300d10b9682003031029617a2007640312060403200354070030f00008400100644400c41c80142ca0103000142e1035840140410035032038003a002a0583c4034440c20030b01c00e81c1010280101d07840303500c100b01050760300c040281d130004044140000002c01c80000d40004500941e01c0a858 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 400650818 1250 400649568 400649629
    0x210415050727030c0e06030a0503030a0204050f0405271005090a1a090303041203110a020c041505061801090b03190506010c20040e0d020a1203051009051302 69
    0x52000041e401ca104002c0d40010f000244054407081d05580714a003031500740ba0348000000c0d28100c60303413600074501e002c04800c0c044120701540142c8141c0300d007141e00300b018412030024482140c80441e01e0740e01d03070748400b0080c01d8800e1a8a560003c294103c000b519038205820300e0000a41c2d00640b002040f59011340c400d68280105240040e81d4120b41c5811403043e07003010269203035680005440035010344403d0601c411614001d520140c043c41e454110180c480701000c5003c0d45810030754110354000c034144601818030550b2a4021070a40710020030700740c00c141e1071494450000c85907070b9a85042c484600d00224041501401661103084014622140c200c203201401040e28405041941400711030245c0740001145480c41310702404442032030382c4d20200d11400140280904a4002d10349004400143c3c04056010810680e068016900d1500302641110304808590382200c01a103203e01100c018002d030300030f0b50407082d0404c082c45008074080c0c03816000502082d8001201e86a45540c02e0810500e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 400652068 1250 400650818 400650857
    0x100c050c0d0e15120c0d09020901120b01061e050f12010e01140307260a02100309170a0504030209040c0308040b03010501020d0206040305340b0105152104150507 71
    0x80d043d100a40450420280401d0a21010000303401c10200c032401054403074040449038003c035070898006250300c0995070f44124420084041e848103641005401001040b41401061003004142d080d2482040b08412001f08a61035004103039000d403000c1082042d00e1070801d82240803406040e03c4406510127500d082c0d07170f8a0800c8007550005004c0c0d080200d0070000c2d00246845040414003400018a40105102c0e000d802c25218080082d4003502003c030303181d0f03801da1503030000b600c2c60712511b9920180416126940c00728090a0100d9000a000300810700c01800c0410f041500030b4812444120300035241e50360700100340c22a402a9828032000b1004004642e810000004000b52070300140006003000e440003045031045039040c0b00180001e0140400107a682e0300051701e0480034180080080c51203103007945583d8400e01c9006c0c4124181d0291a03116040c941c115034030030301500111030340101d0128005a40320401401500c841c40c0742e04052154880d5806218490451607a81351a048074040f070003074 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 400653318 1250 400652068 400652089
    0x7080105060f011103090301060b13050f0321130b0a030b090f0c0c07031403040305060108150f070903020414010306050705040b0304140a05030a0207080d0f02100c050c0d0e 76
    0x2a0304100520407a0b8990084400c4900030038030b04516400c031041c03900c1c2e04c0c5200e071082060701580380520001d00c05403c03001801e10036030a004c0307403042a03135100c1c100488941010a0598550001503690303aa42d0504040762180310b854100203401d1591441d1004001c40056001603c94140060010905039140c4106c6024070b108a030412614104004918004640100700700020b403400120b18880d003e04000344001540c0c05504504202116544181c5941081c84100e41e18400c1c8000400c80810104a411400c0340d00404100b150360b903203201550445024009205200380b900e008805a19180076040a00403001f04040255145140420488800800509c1004001d000910000701218200c0b40c100e038002c000401a41000c03e8010300b410490341d0020018407002800c0c41c941a00800d8a1040301d82c0e00d010303038617181c0a145050351041d03a030000000040e040300ca0a81c554881991056010b2911031900b5801c26a10120051070804041c0d000404a200050700d140c041c07602d40d9415 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 400654568 1250 400653318 400653329
    0x12050405041103220804120602090a0b1603030b041401060206070f02010b0f011202220806011d01120507083703080601051b030d0c110a050c06070611041707 69
    0x15491841c0280400010128040130926a003100409550074429824142c0e0050142c42c50500341c0c610740b51411750001d41c04a0304032401010403c0c800100c00003000155080034440000d507021118013642c08900403c46032404903403060341c07404082d00c02d00c400300d0701a000e4113042d001000c19007045400684081a800e0850301168101404041c454a50242410b4980d0017030906e02281410040604064040c01e0051110b20340b40c00b40300c0e039050521094800403910344109580e00c1c2e07600e4411550503031825020a9444880c82d074010000190707118030f401c000c28026002e0b200402d4503141e4040c14807820b030203803403445090440815442c0c4c3d2444488082e0003244440381501201d036507005000188000c0159041c0000402d0100a074218451744142c8400f03540181c80c4c2d10980e071b000d81002041e08442460020b040c01c0c2051070000c10000e4400a000c0d00301c4001c06001809104004940d03001050440e01c00b612000f10010b44283c3c80003030b0000c2c01055520f010785000e0034000914189159005 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 400655818 1250 400654568 400654601
    0xd0e060105010212070606050303070c0512010209091503151501020106050d12080702120418060b1303021003020c0114092b080414031c18051b0d1205040504 69
    0x100a280c2c3c002450045014261360510b0f12100070f810300c8030003030005a100381c0d05404006180c1c0d041103060b29171001601c00807503d1403a1030b850101858200e020b030761402034003e004000490488101e01e035400ba00c8540042c100c0c2c2c204c4901c3d0344841c02c040d00c10303181c800c43c100172185181709941c0c0a0103050b01502041d01c4900c2450b80c643c035101c51111801e1800002d110394000441d62041c0309100d0308204075144803d0385c1c0d0720703581d0b091000c9041c442964031000241c5007110200303040c20680f040340c440000d0000e41e02c140c10b0942c0c003000446004e0002407414554200928420f40e40c3c01c0c040d0710042d0800b4140e6524929048940343e09108280014110520340440424110701100c503a0303280310300f19842c00d47c100b640c0d00d241041e2a8120220480d040384000310306e40001048600c5a011040c801d82c4083c8a03100e00b60003061580d610381c1c00010141d0700003803403010180e40000004500200001c016080d6400c49841c1c0800e00c1c00300b00d41440004500040900c03140c1080c2c010346d10f1119102c106d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 400657068 1250 400655818 400655821
    0xf02070503121f0e091203010311040e160b0405030f0f190c050a150f0f0f0c0606030209070c0506090a20041b02010e0111030105220204030f06020d0e06 67
    0x200d85407a4418800389682c080715590205101001003c141e104501c07900203040ca503d03880e11109920040200ca0107211482070b81d4800b078040f04544140d030304a1354003880510001d010482000003400c86c04019800c6403080d4403409645000000b01100201020304c6402e036600d0619003030504000c60380b0141001d951000c01303e0400f0000c0050b489065001101c4104e900c00c001c1c0c41d10466958082d0300c034990082c2d4040c4041071100758032005a1000e0703001c2d25a10021400900180c450701e20501507034022805490700a5509030251a4a6600c24882c0358005082c0e61203500144c5803100036104e2100155010024508010007045040d810010300d400a080b0b00c0720b40e640361820811110414081c3c18400d00007080540c81d1600520421040440c0101a1200d803210080c001c1c0301a00f0008100e600349502d0915515060302107034103072000039014010802c8104078160f0310200c07140300100915801c00000010842c00701c22440228460500540c0e2144000f42000a861210148800c0c0e071b0050340 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 400658318 1250 400657068 400657073
    0x50705281505040807021c061104080f0a02090a0f0b13020c1905030301171c020c030705010305010e01140112091b0e07020a03030b0a0801050103110111030f180d06020d0f0f0207 78
    0x40d200403e50455561480da521310345001d07007d110140d0300600c61801c000d405100b00042270f01410585d1300c00001c5620704480e4900440e034921038940302a403c21010b5022442d892150b400c103181440c200d1030003060001e8881e011501175044910380f440307007a60100e417118101c2d6090007002c903004050000e001d41911a500c940e91a403006104003e99582c0115004030042d50a11a981c21065540d44000c0c01030103400010b91140c0c075241c04140300340280000483c1da0360203845002d060320799080d52032a103682042160720100da1180d043e20f041c483c018100e8400039880d40110320205120301e000b0310403004020030045880c2078a030403403c02d544105040020f07487d13000a9882c031880e050320b40070480b001034030082408815250840a9103509000c004404d000030760b0481142000c00707a071040d410322107000515860340900742e08055031610800806c3d20380312101c900c0b403c8a003401821103100f040146e442e0012a4440b03070b094161a42c5034500888150468811848a982500002d514086065 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 400659568 1250 400658318 400658333
    0x304140105030411060c0f101806180b010f050108011202010c0204052508060f010f0903151103070c03020d08101a09060a02100b04060b0a05070528150504 68
    0x68115042080202c0020b040c01041c08030300b1012400584a0303030b551851078075203603103c140e03800b00444c151107260540d0035014600d100303006240410944090044200380c0d607603006805032015001e900408030a03400b0214000005441c020003e15401c80710061400d40094013014050340b00d0620080c0c0c46400e540543d802c031459a1000b0b6045400141581d604150f40c812044a01c1b00382d03100342801003c4071200340c0c000040c18064801100c414800791109001112401c00c0b0f1081003000034501036003040062464440c5039100105410041062644100d007055130303820440749500016013801c9680103050b0140300403501c1c1d005d81e203407072400391910098092a520f0030b4440c122030030103804040800ea120305401d031649220010b019a03513038080800020740e41e40b11141e04540035803801d100c024151030180f10309011500c8282185050580440c0c050720b8a070003149007030300d05004503140070160047c00100d000a00000c1105619180c1843c00c01003010003200283c00c007103d2402051002141305e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 400660818 1250 400659568 400659599
    0x9130b090903032409161e050c0118211e08011403010509030a180e01081e0a1101050c100915140c031303050403080f19081509061c05100c020304 64
    0xc0c106c8402051400211101014400301c540d19071411000300f20000da0040c000c0814100301c0000340558103084803a4601c0106006d030040c013000c04100d2815001981507007a012810590900d41c4140e00440108080b0b10b9401c21140c000134032440040c013091140584450321010180c00130005481c4c6030142e9966441a010400203120b045002c03801800b601d100c0d048040c00c00d04886030101c2d699a403101c0d43d04c1c100e4403c2c0d03044811100d1440c1d00340500004401070126008400d000d010300c01100107440a91011581550600505601c41d0203030b500b0380103103c411071064079460302c180914000441260606100350360307540e0404091004088402c000d50b0f8002401c2212003102c005079240c103480300d2060b640024a00d20002c103c02a0f16001030020301000203c80046403009050403000316000c200c01c0fa02c1100d00d002e03c00035980c00341019200241e0145000c0c1c0852309106103100c0b072005401144100f1100e6030300840c1070b0b10064141d40503404080000c0c0c0015800c1c507007059595080e0508 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 400662068 1250 400660818 400660831
    0xc010f050a0b1315050d051006080a03090b0a090e09060403080a151701021b070521150a0f0603050a0c060806031c120f0f0506010e0609130b090903032409 68
    0x704c4200c1c80310040d03c90b104c0800100f400904084964190385012600c03410740c1c01340d00b80040c0c40e195000a9031f100100343c5840b120380c190b440300e14190400e04040754542117400d4140c00c0240c500b00108501c00c0e080010740c0a15043e00c010034103850140740003400528002d019403444c5081c448107950480302c05148000f80c50920010880080b0b2640d0800d0080c0200c0c1d054481c1102c80c40303c5e15103240c2d0003007501c4042d218151000e05041c1030180c000b20415410b082e03144c00d0755120550840709862040b52041c3c120001031404500ca50a55482d201074940c2c07a0029200b60700305040c00b60400400c1c16065004107168203000c0071511300040065101c810100b10f54003442c00148244001030303c111014401d80080c84010000f840540f5800d100601d001c8041e82d400303034034000c0411140e41c019005100604401401d0074603040a000030b008408908044d022103a60f282d071000c82d40c83d40c50792031040c4036258550081d038503403400c20b82c0c0380351071880c5802c041d180c0300031000d2044c41500c2d00c0300215071010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 400663318 1250 400662068 400662071
    0x1707050103051b0a081b03040c120f12090f0509090d11030c06100312030b090c0f040305150402090a020304051902010e100302370807140c010f050a0b13 67
    0x903294240c0101e4010300c024403058043d000624499641e80041406005200c1d01e41c40c50702900401003601d14510050b41e01604403070b9070941c100081300410700002c500b14030070b0704103081096581d0303140c020003841e043e42c6101244400c041071200060188080c0b00804046410100c41c2c148110065118141e01d0709103c20082c202c0030044032107408004541c060903210040712428640383c842c1c2c0c81c401c08180070880391034844c80e0591070350501c02d0080d8210307180c0080a040040d2141c4110440c5a8080a80300c018281e0901001000c141d041c0403400d0b030100f5440901000b441c2520420141c103038001c1590780343d00d00c1801404085200010075540c5640c420078002e2840082d800140c8000000a40d00c0b58070091481e10755004c0755041e000f400d000144068030102c0034045043c1c00103101e04258203100c841c0e681288196449102d240020380281d2141008440495400140c2000ea4084942190540e4488801c030400e500e50b031140d0382d4000c07403101040081c9042240062213540d0a0751a111296 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 400664568 1250 400663318 400663321
    0x100903120e011704030e0907020115060807031d1608071406031909230c010e0603180f0d0f0e0607060504030908010f05270a031d040c0206090106170705010305 70
    0x1a406a40c0103034441c50043c0c5003003428031342880c004010004034441180911814800314400c0ea00501030721088003000c40d981c40d20141000c8007120840f100411480405440b106e107110303905091a07000f0720840799403001d00a085140034454154003041e5200d01c020b40d0007044200490307140f4034034902003a5411901141d40f03807103941c400150003100b40075419405141a0755042001000d0708014412881c510442c061081c003443c0068542c1d500443c032074086000f0904481491514100459010001d1000030311601e449811940c40d205401407440c0d01c0f5481104014046600700092241601e1245011888000d0520114446014a40c801032085442c2c5010404241c01054494043d1480b80001c002145910307100350080c3c00240c41c400100c182c0c080180307030142c4449503081420154000101201d90066800b258489690107070001c081201c40c422a42544c2d030b9020300044c079074095000b070049042081c402400c40700030760b01108820320b000c04003160b40980403499404840c82400c000456 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 400665818 1250 400664568 400664597
    0x3070b0f040609020a0603020a090b0307090509091c080915070f030b03071505120a06080a02090a27121e050d02070f0c030b07030b06070b091606090510090312 70
    0x83d1078940e070002c0d03100600b043c000c9079a0350705902601d040881c69480610381a620508090b044c4810b840607000039180d8a0144650b0808921551300140d500381143d402d65515030b12052150b0348402076a0000340400c6c00d218554408021040c401c440346d205151542c105071a0290403140c4044000040c903480d040d00005d160740034480100145001c0724405044100720a0080040e84030302051009a08200082100d19a0a2103a0710035602c102d8024013140f10a5000c0240b40070001f803c40303041e241c43d4104010b50007041c00c2101c1c03000506580000405409180040c54500c80344084020032001100072841c981c44400400059206800d24079507503442405500c010b0710400c107010b408120000109402c00040118007812680100d44070091a201c103001201960010009a5404242400300b107000c00c6042400b10341009141c412106007400700c503e04000640d081c1e100e4404101c1c0400104a50300b805810240c00120902d0b0645015045542c0e080c03a950004604800b00304422888604 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 400667068 1250 400665818 400665821
    0x1080402131506050319050103050a0b102111030c090a0c020316050a02030f0d05180604050904050607020c060a230c03120108070e0c12040201020309060c0606090903070b0f0406 78
    0xd02c5100301c0700d110036585944001e0807541c0280c441148003000c841006800c4085442030f581a41d502002800c20240c1c56158541d0501c8060155500140700c0c44000a80c6083c10580d0380c0d40d40741e00c2c00c0f500c1c280192400c1850500c0107241046019030800c60100d07141d03030f41e6848103641c0400b20700360004e420180000124a10300501325608000c4112920000a100f40020864004c0e8030807002c580700c110740e091034651192280070b5450040340c0144900920743c4074401c000707240c5074001707840c2a0405541e000060700400c400d0b07505641540198040c451195818400c0311115802a6409841c00c90641c40082c5070703000540c10045d0080490501a401003000c004a410801e546c0048030b80340c400424032445500000e03c6640400d1282541c000707101c0e42e002005901c600c843e91505418070f00195400131800c0d0005104904501042298900941e2140003600a045c1c07890000d000c2071406c9c03070521000388805001c0e00c4650b4810300c00e8000113460074059503805a0066040507644d201c5291400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 400668318 1250 400667068 400667081
    0xc140927010b120601180606050a030e030d09061b0e010f080603010b03061f0806150609042c1e03041e030506070e0103050612060a02130305031914090108040213 71
    0x50780b02d1102c3d59000043c000015070541650100410003001c15485404542211403910500012840038002410a1406940300c142c51242c40d0054901c1c000c4071000002c101c0b181c0103400c40e500e95071500040c02d050b2940c8031440e80c0307407100e00b0080142d080c03140028051030b00822601080100c1000010300d552002e40050300b00c410050200d495500741800340b4410000440c0740d000311014500000101003200103607840c028010003a03250b4690541005100d1658010310030705c2c0c2c1241d00d82c0c1016901ca11001c440b1181e03513158010b00810403964045141c10a15083c08005080d840c18408580c000b00110441d4121455035048128001d241425912005495400034000b80644400c200b81a82c00060000c5205026a4104920342e14034081201640b02d04000403026405600042d002d0356456004120303065928504400c004c0c1e603507882c90714582c8000c0b0038200c40001c54040c02412500201c281a20175015100d00342071900d41d100003030900038001e1010784544105543c0600d81111507000c00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 400669568 1250 400668318 400668341
    0x1407110603070c030f0c0b010303050c03090a1412150f04050f01020a0c0204050606070c0905070e0a0b09010f091404050a091401061404110d0b18040c14092701 70
    0x594072440c140102600410706500154007050542c200101034902c1945160300117607200b80310456130307400e5482c00c81c0e040d00104081520b41c84200320080e907695595010b1802407441ca405400e80c84849001e00681181151120401e03600140d03081040644981030070307034000c024280d410069521030070f100745032486681404881d9440010820b40792f41d4480315201e070781c900998040c85552100800d1244a00c02c80901500c038980c0c0c8907090140d00140d4200a400a540d8544404503c03882d80000c2c0c9072024540c80b000c4250000902d645840d48c01012240c071040c1c042c01d1941c0590b2504d0b603c940c441003415100b6100d9030741ca100152103040d0f81d034840402250031000741001c01d01e42c03c030a28001c00540c00340210b0b8000b5894061420301c0d00380100d020011040c0025414008040d11401c06000040d00807544411102010386020240da00414800c60156444090ba5841c11203641a1440c0d1581124069a2684200010307004400d081c20060051030145841400a18007034034010300e600c5622 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 400670818 1250 400669568 400669579
    0x12901020705060d0f1505010203030403030c2304080705030d0207440606060315011407050102031611160605030402011404080106030302190b0705032d180706140711 73
    0x125134021460f4021400d034207900008006000400c01d52051506080c4034580c01640200b00150000c1e02c40d4002c0850610035050090184008000403064800c1a00c00c040c41603c01040801c044401002a400141011341c0546070311b848054000b0f40701d000c1409411032654a200029045095042d1444803180c481980300b01c1884501180340c4403510306581060303c0b44115400b01da114607151084a014060740303010003e2141c180401500c030001080b00d811403895042c000c000c081042800214481c07072049081d240c00d1040c454018005042000c0700c100150b10082c0c0c0b4405000100204600751481402c00315165034891004a0b1050410340f120142800041030005140405403c601c2c1568440e400b554801005840004120f0507007c4000c1e040303110040c0480c1e040d0740100010340d000240c0110182c122082c08801900840302c041814410310b01d040c0811050251004080c00394240100103000068603003407004241c0120350301840d807002d000260200401415100d00745042801602 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 400672068 1250 400670818 400670827
    0xe011401090c02070e1e0a090b0f071b08090d0309150816030b061608040501031d0705010e030a1a07080c071115070c0e040c050d03080c03070507061e0e01290102070506 74
    0x60030042c220708c1104841c3d600200021610303d02c6010403c40c42400300b0307603071043c03580c5c9518115040d00c584a08140c90b100e03800c200701c032602c0e1100c800700d80c1403034000c2c2c95800c8214500ac19541040c1065a116001c100d03040c400d100d0b101400c9903049920b03500615011541d0720892001807038038451208410b44140781c4002200803c945d0b00060801c407030007601d00b041180c100710300441e120785d11039400703284580000c4000e1007a03601841440820b94400b0302103400d1100503550b9119040039440d00040e0481680c01000802c5a1240d0030b903130b000165440c46410b0015a541d80241c0d840102c080d14860b461400e00c2402c142801003d85469542224900d074a9581e290940e5401c00c9050360146c0341e40c00780b03910104050070607490301a840c9901d56a003001550b2038488041441e00702410000801204004946c081386035405890114000d001c03038040d28031000c480030021100105050416641485001001a00243c40c010b41d88141010640c03140410000100e040081c19004590301400100c1d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 400673318 1250 400672068 400672081
    0xa030903020105070504050a030b07020c060c0304052e1d2d04090f0f080d06080c040b010f2a0b070c050c090c040303110a060e011401090c02070e1e 65
    0x80202a406000303400801c940c1e00e41d5007089560380b0640c0a03942d0481d020f200c00f00001200154016800f040724411f07035004141e12000510030398014503d000d91544041828003852a04c000c1000d90340010f24800305940850030024042c0e4a5407072000010b00800d54026403003075052130350040c011440180712559a02440c170603200781038659807440303041a126000b16031240c1018890500041e81007401d140c003c03940d41e0b0720034070701101d110740454811800384062850001c4901510018203240c20240150b106c0e0b1206010440b000c41c0005410091803001c07400711590000700000c842c100348c1c1c40304e9030841044202140016007240000704104081e10401030090751100d1807810380380c4600c0035507050344070b15401c1040c288026690403451801c01c00c41080003a020b9021510803a01c141c0a80388035181c7da80300c0314212103003400080601c1e51147c005480030400038000b64003410007650100304d0701841000003948c175246800303011080c0c840b89001c10318402c1c05241030003014000082111151801d00c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 400674568 1250 400673318 400673321
    0x20402030711010e0606031e010e0321061905011407080d06030c120c091e05090601050103060b190804020a0f0303050a030e031204061802090a0b030708190f020a08030a03 75
    0x54102e1505540790040c1480700c59400305581d401900f00800510b81b6001c8005481d08421080c801d103201e5640e111100d5060440500c090300140e2210100b110b4013542c1c046201080d0306000782003600c00c0d505031464a00d540580309404007a81c00c213103003a0101e94298040e0032154480e41130003038100d240100d031108054040703400440c1500c0c420140e10107616a40c0544400620052034000c0c0510000c090070320940c4480c0d0700c810300c024004070541140c168840c0c1180100c035010381c0e4082c200e4001d840107110550305801048002c0c400d00c02103502e000d03c0b41c0f50b61541c2e80070740d8a14000f00140705e8041019035640c1004500504407003450009420b03904d2501819542c80b440e1008042405c0c00c140e150841c50120035035600d02420114201e8a036115610325000300409803004401000440743c035809070701c8018a29200b00781006001440d110040201460201c0b240d12100e41c0e90700c200d94500c60b0030610901408200d03804030309180103420034070002d02c5c602d1454000d0a10740c4030210300c0049540c2d05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 400675818 1250 400674568 400674587
    0xb0604120507090e150403030b01120911030d020d080103020906010903120509040c0914091f0e0105120109032c22141005130204080604140d0203040e010b070c030204020307 76
    0x422402c200244400300300c07036151448040044003841240c3d0000e000304e400b13904104000d0340145000c2c0c083d20b0be240d00300707021203021800c1500e010500145281e800d040030804000300c41000d00041050074100c61008200140c1400024002c0c03122001017905a4066681c40b8099a44416220780480c0c0c0c3c50310041c0b0640100490b980f1072400c000c0355102e824011650030701a29040484080480480003d100200002601d075181100c04114501b410094051516026241062100066514200c20800f01c0b00000b8031440a6034545040f4a000035000285c0d02c0440301d00801c50a0000d4580507040000c084010320746401c0900c3d44965140c140902c41b1110046650400810031003214110030408090200d524000300d182d20a400c2c0b103185041d00d2a5803035007080d83c0c07016103010384070b2505030b01300b100c1550120380114000c03020303500030107050100d4050540c091000398182460003614203000c200612841c2c4e0308541c0092008144006030001001650b0041c0c41503580b401c0581009190040d03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 400677068 1250 400675818 400675829
    0x1d0a032708210f09061806030106170c0c15040302150a0209041803020d0c0624030302060108030f041401020102070f0c1806080a08090307120b07110604030207090b0604120507 77
    0x40c1c1065110b0422820020703541c03044041e185060034482c00d402480075950000c0d01d0700925078110700465009540c0c02c0000c6010740925601d40300711500340c2d2580c48000b8005841648a100180308110070a41c0010300116601d007012180c003400d0b1a1424141c2c14440c682240c90b8403060900204482d000d00350300103002c11702094808004200e201681d402c8646166000180141c0184ca0381e00a0144580a5014480c0c01024002070078030881303210b141c0140003101c0d0028200d0401c07004006058062000c04d00510419018510f050074020300780050348241d005007400724042d101c402c44140d2007507064031201c560001e0304180310038076800c049a00d000944101030324083d01c3c03410018600d00600a20044501d01c100800d070940c216502d00030b182e040b000020303030184031701140081c40035050481c50075a00d00511240b0001d040002d030042a295060b603248015912500c00c1c40002a800101d400c00c59000030340015043c8007280c005105485994050707508600c001c8800030900c03802261403000c560 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 400678318 1250 400677068 400677103
    0x30a020c120319111506100e0108010501031a1806100f081315150f060306080714120709020d05071707030c030e0d02010b09060906090103200603130203011d0a032708 73
    0x547d0500111821101581040d0004111a00405c1594020b821044640010034844c039900e10016020400d4151803248005210b174104007400302d1414280505003003d00d0301d18117584500760012020300000b102a16442d40422031724000d13010300c00300d60003130a9800c108a2040c00300b1001e403074204050103400d01508903c1c0502c0c50000642c41d000b40311300b80446d408480600945854501c03080d031110350310790703940d500700b00c10241c071080ea00c0c010300c600c5014110390440182c40310643c3c20510300701c070001003c800c18044940400100c07400120220740c1e008006250104100080903411800341c51403500750074041c41b80d4100d00101d982c040d0405c0c45009029076100300c0c5642e8120820205903003d442c1c0b980c0000b1880c005001003803900d410400c1c41505c071200034181c80401d902081c81a44100d40c24980b2001d02200310302140303020f01034481c0d941d4440c8003d8681440f0100069182c0c84200740040503c20000c448000c80c060015810076a481d02d01d144415080e03842042c1512415102040642e00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 400679568 1250 400678318 400678339
    0x30305030c120112030f021f051005120a1e020607060506121c020f121b070f1d1315020901020712030917010203010f0308091c05030a020c120319111506 67
    0x24400190444014010b5030923503001944480d40d00e000b0b1201600d00d51040750300c044040340a490380207001411880003c000c040707407010f0f4140304d201c141e8086010b40386c8421000c18100583e41e02070940300706a8101d9000102502c84600080c0392030502591501503016150950200032980030941e01c02c0d100075025200d41d2540c86184a8071035082c032414000343d0300c06010017200300b040c0206105003d901304045442c80f9454448192111f0107a0307120201c0380030900c9042d07403024250512183c12507011040c24000c110304c2d95808210b0b07941c00d03440e2101d90f64007059250280c2e2003009440002d000c9800344c10700841c07050400824140180c02000c0d1304100c0d504a90748443d40500c02c0b20304031284444205442400c680e03c00c0d40540c8410340d555841400d801c684001c2080401c0700c80d150310301c91402155145180d50000e41040703884140903202c0c0b10b05008032540b9103404400c99044518141111070800c00040b03050b43c07240b90601001105114000d40c00b521500d06622560240c0001c803002c0448 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 400680818 1250 400679568 400679597
    0xb0a06020f0c19031205040b180103140f0406150e01090203221e03050421021e0d020906030102070b090604030e0d1a0702030d0c02010501030b01120b01030305030c12011203 76
    0x1240302c031500fa03002c1c0d03d6071502c0800204000d6a0348901c1c00d28280b40a41c0703826503520700d0340c1598105018000e540190000019259a014800c404407180114090701d5245000c40108524980003000502080d03203900741d0980c01020700005c0d0001c3c012075403207104296101c1c500b4000a40040f941101101c0f0b01d00003ca4440304142101d20b141c41d84042c00810745061240c2ca0b1442d070015240441c14000c05000209051112400c2e090b0910400441e404010318507004000320009162a03880c6203000c4617452481e903072074507951a4200b40c7c040c0d6418065440b4403000ca40240b04541d005040c0018050034007000d0f04011603818010b60003503681c0091004140700308102403003507100040c0b4460310f401075030207038050440d00c06500400600542c6d090001c207a500f1030903107001c012040011317555100144100000c031280640500122030f062480301a4030340d81c4074140541800090244100480010041c04040342206c500172200300c042c6125583d5070344010050890602e04801040a0f240c20a41 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 400682068 1250 400680818 400680829
    0x1050f09030f181c26040f050409320c06180d0201020f0f160e132a090e21040512030f030903040f060203130510030b0a06020f0c 57
    0x121107446412860412902c0f00b10002c0c540c102d8032150090045100e040f910031030024142240350180075681500303421095140b50f44184100c1440f00e0310001d0000f400712058403540141a01d1050300c0c0028188a24180b00d20801c0310005801c3c090b1041c40524490700a69032002e10300402060f0449402c03030300c05020442c05010300703203040540d4003407400c8481c40d5207008190f6030012030041c010366140e584c01d440104d04111000b58403540d1607100d40c10003222820036401401c000e003c80140c8800b282064056108a070741e0f02440540019021020f05c036080340c60501030513251a42620714154141d540200300c02600500007241c4684c000d03d04012061502140340c540300310b100010040c681810300041054005440e600c49115100500c4070300c225a4002000314080da034a1001580c95514203544146201e2140d040003045402c2488a5490705503460843c0c81502d100326859241d560040c60102d005143e0400301a038070208540c40001c0c070940100307134041c16042d0041521001c04200042c840d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 400683318 1250 400682068 400682077
    0x60207060318020904021809030c0d0809100e100614010329120a080d02031f030b04170c0109060915021804110903030c0115060804050c010e01030f090501050f0903 72
    0x90b5603010a890080052410600d005d6000d0310080650451318a641c0d02110319107400c035a820004d0b0b000280000e11120204140050320402345445400c501d007900c070103911901d15600d040103050711901d80000300714090050001140007a8000c2101c1c0e65149002000c40060390709203800b0031300d8007074480c80c0400300c00c6121907280001507107445a4000101808105004841070440c2400f40c2d40d20440001c10390300c001c16203d0909600981c50381001d44181c5809412050030205000c0300550410000d50010001c0750300c40e0304100f4106401903606038481c0c452045011118040d4a040b0b03802041240303a0f800100000d000b40301090210360b030010200200c0c0b051500030604031a0030014408140b82540008500000c3c0c9100c49040c016503c01107451030300030341c150100d141d458820032607020800c20001002000d40d881e1089190501e901c1d03003525941d420650314100040462441c501303900a801040f5060440b00c4100045a02390034194001d040680e45000090710007404141c0104000040d203 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 400684568 1250 400683318 400683341
    0x103150e0c1912060e06070305160c030e0907080f060301020307090b0913020403120305090604080a0c11030f010e01050105060a0207050105070611030106120e070f0b0702040603080c070602070603 86
    0x4100384801c0e0001c0007106808110007845050030703140c0c04a4894146046260b1007881180c0c045402c4245200103410300c60010a09000c1615140400c1142080e5030003c60200c80f590500c40e15800307050504071018400f540c5070030b030000b03c88018041c081e5480003003c1d00c10944020040c417980c41d8001094241c3c03006a807850000341d04c203801403081400c00d0b0300900c40d408004004198986000b02d00745c2c01d90304168401d8030301b031002e483c10030306032a0980131341d0350b02042c8400604a01d01d456540e00d107141c000c0b03c402008210f0031060389000c21101c0201310310480c100070f044460160b00624400e000e0003001b074a0b441035500341000050b25043c4001511140143c50b005486111701300070044650350042d00082d01c15540311549103141d108114005c5010b420a0307510b14548400c2003060809481c4a0540040942d120480403c0800408080d4078240d84410300d4a59945000f40000303005001682c201078800100000d0400c03a10000140c600c003180c1c0302d50242c41410307555000030340c200c490b02c00f240c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 400685818 1250 400684568 400684573
    0xa02010e07030809011d040603050a031409010903060207021804050d14070b2a0703090510050c0a0b13020301140117030403080d09060231050a05130c110d080103150e 73
    0x84c0314640c05140d0850007886441c611052101043c00014290780d00c5d640103489035080409050113255105d40c51641e00350309800d0b43d61800e0050300000344400d007c1d100141500ba4040742d00803c40d924000c80220503141c144d080a46030034142405901e0b00290b00503c0d02280168042d21001c04903d025620f46903089a114580c550f5a0b01c035840401c000c000300c59a43c0b02c0141d114400a41403040686092070080e50795141043c00c00301402440703041025641c007488418081482034000c00100c0d020000c1d84400c00e4007958a45920907071043c803000f14000e5055007000510514803115040060403680000070100155003000e0986441744198000500740703000c100160941c2c4d451640051a07014403c000c010310b0600804000e03c07852840c0c0c103004028080d0803224581c0c1c81c0c0c85a4200b0f02406048900903402440d040004000407283c0340c007445001c3c0c44c0c07022a404540203015001001003604142c4000401ca03100040100500340000c640c0030178040080200301029126664030108003000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 400687068 1250 400685818 400685827
    0x60a0e0a020a0306080d0306060806040216060b01050d090609021302070b0708060d060203010e07200a110a090c02032110060804020a090e010621080f0d090206030c0a02010e070308 79
    0xa50380003035070160040b80181a101c801c0041c48007410864400c45158035500054581c0c00c2207401000b8070b001411340c40c4070350b00601001c0464080c41034078030401540104002448003405d00165014052403411a0f011440c0c00400c0003404940d402048004e4821901d81401c5002d10a9080880c051601c004e400201c4d40e400050b00d0320b006644150300f01c0c400500e003503030000caa903444005a0f030090b000030740728825130000d11200c00d03003050f54103414100481900480850689104d69284100d10740641104486005520301d80c83d403000040152004c1007040c0001c96840c40c0c065540d80c45150491800f0902400707a006080300c41e000d80f8064161522559445403800004898258014006907805000d21744000388031059440740b0714035600c0b410004113001d46000c44041c240e4141d1112035803804680140c00340000c9808003111001000180070549034803040002500030484400000d401c008000f0601c401d600c0643c0150807050344070b134002d101080060f00c2141e01c1e41118480200039040a01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 400688318 1250 400687068 400687081
    0x12021303021e06070f0b060306010302061909150207050907093f050607090501020f0c090c0408030406080a0e0f0c0103020a02010b03060c03090d0516020d0303020c0d17060a0e 77
    0x6202c080030000d5140c80c144144600c0001c1c69940c03085100300c510a4a0842c00b100300000304039802e40c4104118040c2c400d640c5145c01145580c414100310040700e401c080c44000c6007a0040f20f58074060405100165182d40143e44003070b41c1d581080c02454400e045c0000001c041c030b0b11404004054468110444018040070000c20041071480c806614241c03508080c000d40c0b40d0145041e00950a0146004102c14140800050030620f4190803813411504804c0e051000d00b00001501540540141c0e04081c0681c0c0b2001b06d8422030050f03400c0f40990303000000700091640d62000109002d40303a059000c000300744040300615512038030034001060301c0d0043c4c5684c0b010340d8000d03406042d0760501c50001140023219000000d003807000403581c000d4602004420300c2106d90081050002c10901410715030b10b0040f1403c881550b100d203115000703100701a01040300c400c251098066032074007440c82c41285d0756603110b048080c142d8000f07100407150a50282d0006041480e0002140003101c488241c6204d4030780f9401c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 400689568 1250 400688318 400688329
    0x5060910060c030c201311070209060a08060711070605040501021507030b040204030804141206181204060c02010311250c030c0e04110102060106050306130b1f1202130302 75
    0x10324060307040c4980414140c004c28425602c003001005405c020800681030307142080102050030118440c00b80c80c007000c4002400c4680304a0f0140e0342c040301c040b2020b0f03581000041d088645a00104100d0240500303008c060f81d04250310050011704402942e21382e0391110011182da004600c02c103401a0700ca5000240000020824590042000d00d80441c44541c440c010030280da1296200701c541000001d07081160054440021620007011945c251000034401c402a6881401505002c0c0e91620300801074480b400030445051801c071030348201c50b240e0b691004060103810b185c2c0010307800b00382404da00520016030a81100c001400c1c88003406517801c80c17050b441c030006080c5c0c00d0440b403542a88001001080c600040c000083c0281c80b829425454903241c95014207148503011411342d030124006002c01fa400c07a050301c5d40b00d00280c4400c50320a80e4400c11304041d240c0c2e5400141c08c804814401d01603a100d04107040700350002c9031a008850800001000100d00c519061200b40e036503400342c1840140b405 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 400690818 1250 400689568 400689587
    0x7110607081323150f16090b0d0b060f0d0b04050618091f0603150c02070909140a080403150b06120606070b010b032e05040b1203040e040c05030f061f030f0501050a0506091006 77
    0x1002400240998000041211684045100c01c44814007123a000c40c10501d9000348004ec100980b005d1045040c42d0b03000c10349200c9041541002e8406010001d51600010844480318803000100c0101030007504070220001c0205020a940d091440348003580c842020740290030046d00f0990084c040e007443c06203940c004004048d4100d590904000c9007840703810040040c0c150440c007c0070000d41c0c491562802d45003034100815551000b5042c4210409203660b4041030740c5000c004010350544e5a0b48040018100c0d1080f1a00141030641100011614000c260051441440001d458001c84281c4588074810303008040e5500f021645c0e81703e420701541c00c1070303007140e21150340103072180502031464400d183c25904203801c540c2c0252204410031050042480004004101c240c002d000108940c10303525440320802426505407106150303540f000380a0114164001b10b41011400701e070105d0903e0058003030706064915004050501c004258545030010016010300e4480342108100391038000280d524001 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 400692068 1250 400690818 400690837
    0x18030f02030702120706110a0803060103050a06090504050105090c0d0f020d0606080f0a060b0f130b0a050616061a0303070314040e07110607081323150f16090b 70
    0x1c103002510050321500304010070300701031078042d05002e130815400030456a030741a110901580106460004035610703404590300050286404900c0395140c82005c1d02a219641c40101030768a00010401031103010360149000700300307a8081e14100310101c010010380015212014154010a1403a0401480c14200081c0e040c0d00c03c00300031070325030350b40c2001c40c0c14241401e1f200c040070740100340030b8000c0100d94800c1c001d05036400c840d01c1c40d011900c90b000c100c40414030041c041000c0d6540465620b03e5403040c10711802000c0051109644880100626015211200040b12400d04060b4040310990380c14091501b002c3c4003034000e5061074810344044a000c80d40c04154040300d8000c00010800c0c601c0c496220303108402545800ba440700d0804045490250300030702031402c0224500a00c039240c030b140362001c02c0e03090b0003040d01807a060401103140489156808401ca240c450b81d04080f80001c0100314140c410150032000200741d0303980703480d259540201404280c3c005410f41609120218090000c2d15807040c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 400693318 1250 400692068 400692073
    0xb03060f0402041d0a060b030a09140609010b01090803032809290f060a0b0f0c100e100603020f01050d2c070504061202010507020312210105030118030f02 68
    0x402001107012644140c005440f0b50706021400c403030001d01c0d15546034004d070951904000d11403078028000c1c0b2501019160200c803503206c132001c105000c1c815030f0010805a0b94403e4521504186040d00c4c000d03c1c4041d002e501140c42194009240400401074911038500114101c1e00207890a520f0706105540400040d10340d581d41241c00041002401c000480801d100b28001080d0600c214148070b208005080200d03805824080244a85900c01800100e8468960894544e85900074a5003a4010010000102d1080000c654240c00c1c00d030700701c0409014181d050326100e001d04030480080d2000383c00041c2d08240d020300501a0744d40303d08001c008450100e840090304d222035001c440c010324000d805482c8000108650315005100c1440718100910b0100c504115840c6002481c804c00c01d09030070007034148400032490074255242072000c08107001544480e503a540800e0360000f01c014442010802e144440c0c0f4001150a04052260b503241c0d40c1d0010401014001e04d603030444908000421520450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 400694568 1250 400693318 400693339
    0xb0706090c0f080606041107030f05090301020d1b030605030a0b0106050d0e0d02060402010906091d09251a0414042f0309011b050d0b0105042102090105010305100b0306 74
    0x71220307454440e002d800040013424140c24000200800d46135a4001140020410400000003139003140c626910700b480307401c209e515038142100290090203990300082a080c180b000002d50030500351004402c0090f80e440401296854006050355820b040c800181030307500d810f0040c0300440c0564003038018074461407004103022001034400c0f400c141d40c0d0505103015038400300071b1000f19038101e580c0c140500a40e18000072010718102e00c50290882da024001c400a1401d0081110300c2d80c144010f003681d15001000041c000210307940c0502040c02c2c0d03c9100384020b26040d640c0c42058080c0d08036011070380a80da0455025074514101f02c020204000d64003008d600303076a030b05118500030243c3c41c03801c100c0b8201a1610703031900700c0406094900912526240004148010420310b4010301130761003507102aa030015407c044000161018490707600b01201642080d82100500303007130031380c86801407407099903180400c5c1d03600e50064066940a588113020012580c4042c071000d40c50078080e6034004401040a1641e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 400695818 1250 400694568 400694579
    0x30c130b070503030a0509060603120f0d15150905060702040f0b1c06050c03040203030f03090708030f040305010b010e01140a03150306060e0c0c19030210050109051501090b0706090c 80
    0x1030380314101c11200c0f034101004202c050449403040550040f5080c015255030302e003450019440300e0b4913110300180c1c01c002150b03d2650220f01c0781603420364507501804029030046001881a6040c00c3d114000c0e840d030f50281c003032640f50b1107081b60404884000c0e140a01b4254213500b0403000c0c002c4007502c45802d558924502c0d41c1079440e91048200b10050720004140101e05040490582e000102004400d030420001d110068400004070341222803c1c142285c0c0301d03129000500e09180c410340c0318071041d110104100e5442070048004100700c070b1080e0000c009a41110006650340100c078000d00e408503c81c1c18240103800003000040850f90708500e000281c44158424508200c1002d030400d41e03032603039200070a1104141008c050b81d0003030040c00019060000f981030742652040c2081d90842d10010b03c035001010103000300511a102c140d454818441980c403241560000c0404a8808103042c09000d007000b0554014400e0300305617032081400c02c1c90f09034030303440c2d40002d041104002ca0305503d454070000349 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 400697068 1250 400695818 400695839
    0x90a09020a171c09060e0301050609040308040c0b07030503061c020d020907270503060f0c160f0b1f0b131406040b070803040c05060309210d140f09010203040503030c13 74
    0x403d840315448000260f420a02d00030300b100800803005019a14000c180a082d035104082d10794800e5140c44e1004455a031803410035403c0ba12980170458140021524504040e001405184115000e503540c840d4182d003100810811503000b04042d4004050250341c00140c2402038600b6800841410b002a03102500110028614481d814601d61090035000c240b107245018807919400240581704584103050840d00380c0e00034455a9650102030340c02c06c50079030412880340b541d0000e158002e080f0481c02d281c46443c0b44813008010581e45d480c0c4540d41e502040669100c000c0c2c0d0b2040b10b9444051903c0d13814000c2011285005412107a80050140f000080c002004001004e03198400c500107031300c80c1403e150203000c10030a900800d200d0307242403082081041000640714203d4a00700c0340310044209100c510405031243c20900e070381103400d1403850054a01f403d595075004081d031400444c12981d441e21114204e0000752001001c5800c01c101003402400e20070098000320802c3c8120148440c1e0b1542c03080d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 400698318 1250 400697068 400697113
    0x30b011e110f0309030319090504020f0304061401120816050303130507080109030f0e010306090f0e100c0e011409030a0b010e070c08160807081305090a09020a17 71
    0x400092081894080e515020300c42c0880c041e414000a504046040340069107138001c0039000c480c1d40300301d100040c00c0b26200c3c426402c002d14002c3d02c11580c8000c0c0110708140750307008503000d4070070504080c043e14a21480c06100d90403500c1c0310410008880855846d0303d0300c0c1e407103540047c46e1410504203841c040745c4240000c0d4086c900803144102200c00a1900c10f0419103a03620071481a4036082d11940403035008030784942062031920701202080c034508016002000940c0103242c040d8580032134294441c8882e8003610461b030380c1a044650000c848201b0505451910f0444130016421224009055000d42140e00740103024001c01401c20448901081c0341c00a40d42090320f40d0703803d40f00100314800c50024070b10f4005e661031070610070034401912380c9005407280f202603e195075079190705031042c13150311415503012075070108600f0380c1d425128901c0008103038680205441401c6050120300c80140318070480612070b038043c2c25221403d02d07044206044401c5003000c00d92901407546ea40034030601186811 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 400699568 1250 400698318 400698377
    0xb0405040f061502031c0509192415140f120a0b190b0910031101050405130f11030f07030207020607050102030a0617010e150705070b0a0f1802010f030b01 68
    0x551b2606180280c0364522003004600011035031500d801e00261020210b034008a05030026034503038500e1814a00074035803489aa017200c01041940440805a441d16001855540380c070390039496880b80c0740c241000000154699071036100c00c41c10030002c428281000e0300410020300406a072000c800c140c541d90152142181c5990a25400c030401c203400a41078030940562100a5510301c4140c5002d9a031400b13101d4175400064540c085c0c1c1c0042d0059680b08101300d60181c50040c20803840040f000c42c45c0300150101a07180c10046042405446906400038181c0340310300340c0c41c00000990780f11408250001c5d40600020713030f0070039400c00c200004074000740002d6028100710b14000807000d1912050743d0500c07040c81c1c05410244d05003500340c00201000034400e4140056400c20742143e880c2c041e03007a14a4421040020510700310b8100b041410300082c0d10642c4200c0315854184440c105001406100d0a50340c0402408a102c00d8400c040c0544250310031080b004040c10f10b01448584103514125200c03000d000f0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 400700818 1250 400699568 400699573
    0x1121a010b03040b0705040b18120f2416050906131701051b0a0813050d05040906080a03051206010905040614040b030c030604170706020d0e0d08010b0405040f061502 73
    0x380004c0001324981035901001500d802c3e41018103141c5c41011501c690301102114a043c040015440d607146407000c042c04104004880650b039540346100c5d01c8038100c1e02c1418914410704003011410702800c910f42e105449200001e9008503614a00751216003103111025003054003030194440109003040544013030000d02c8407038121105548010381c2075440060a105000e41004450315041a681c816680800403509042c4603954a813541400502c012540240c81485590565258141c0050003002a106003403414407030b494442e8141681d030000c00400400107070b0100100101e25885048542d008101450300035401c03541c450002d41600c0064120184550401c011070010f45000d108400c0b08480c113402400d60303c5258070002c2d49400c001003001d403071070344400480c02440550000303c03141c00d640000c0854442200f0108034000b407144003201c8040e84103c200c0c000707286004001190403a60070514045c130301030400c801d200c080e00100060718507094035000d01041101480b022030890800c160300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 400702068 1250 400700818 400700821
    0x112170409090b0a0903140705030d090c0e0c1c0b0105091f030c0e0f01081e011d0603011407051c09080a080f0403080708180a0f061a01020601121a010b03 68
    0x9080f442c10002070700b03034000e0603c0c1505140000750003100d031201581603070a50355180c88641c10032078294400c0381c0c46080d0503480d01d1884801c0000c5550769900b66400007413032070b03c1a0b489050b510741038811b51104803400000c01205c4129101c580d08003000800c0185401424850428081401e9014070030780070003034203445012425881d50521030819050300c1440d100b410074100c87c0103d0040ba2030311007854100800302000585c81149103004a0003c1d1040c94001620b6a40795150f140840c4145036107001c0f41c0c60000812514901401608140150114002181d85589405640c1c560000102101c80076090403400081c0c4218820840d00e2406861410b540d000114030052504100030a255141000c200910011a5100c840c045d40035902d404c1850140c1c4a00109002d40508400c9007a0b017481242d10f40d9040107a00c0c003560901505c80c40b0b041c807a1603d041e00100c4c0e0b2602001c092401603000100402c4102c18a50422404900542c032075050b000700000140c2100c00242c0010004080000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 400703318 1250 400702068 400702073
    0x40309081f0c050f0f031314070f06080c09040902010e1801090b010203190e01030b0901060f020115150806060c030f041a090a140f030106140a08060f011217040909 72
    0x88000c1072502d840c05a10781085240007092138000c075040ca0300c400601000003080400010b1040b22060b0b0480600a408543e641402d65251075500564810045110001441030300130000c55015520111803241000101e01c107120080c100d00b88160b04000c4128200e180c980c403481d8a4800d4104050945066507041071042c40c01d07215000406030440d4000c0002034000d03041395220762034603111850400c03610044c0400403000b82c440003400d207a00100c0c01000040f019040002c010202c0b210b0740080c0f00b54483c0e480322511a81c07461160a82400808040040441c03103545000e901860091180d400c1207070011940345590040c20901450000004091040c0c11031012801c1d01e0501c2c61f0201031800b044100401d921003a03510a5006075840011352280a95415190808400026008002c5a5500e2022401380b004118149000d8440c100000c9000d03c000b0034040d00c5501744020500c0c6a07480d05800824040f007814060740c40b41c40c0c2032400301c22051031fa00200300800316034602080065460 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 400704568 1250 400703318 400703321
    0x1090b24070218040302281a06101d060a05160f14011541040b040501080604030e0a09050f0f0c180f040603050703060f1b020312040309081f 62
    0x4030b902d050f504540e6810080001d038002406596806408501000c1d02d90718100354014102842c1c0080141301d003030256043e4440204843c038803988044400d03420740c1600d640c05031603c0c0d200340240b80c0381c2c0c00007403000c07807841c00c0a000600000c0744502c0d24038070349042e5807480c1c04039280d034200445003518449204414032030000411884041c2c001e000b08900001150b001541c012140700340081da584d06c0980c00c80910450b250311300c52070301a101759400600c0c0c0010140c6903071032941c0580d10646c80e080406010307040c0f500c1858103071a103c00003001e0607242d54800b038070407561041101e5032004d00c02c0d2011400400b6801410300403080300d28040040e081c850443c690409009140c50301000040c084c5000040c188100402d5500c02035440f0049041d0b11008117020706031540000c1c0051140e01400010460964400541c081c1c1c0032a0801000b50006d17035100414800d070000b540183c0c030611203410142000c40001343c20920a0800e04465503070b800c030942c200040c46070040b41148280942001c0c00080f0b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 400705818 1250 400704568 400704589
    0x6050a020415050a08130206070506070206070306060311040315180623090a030c080c01180203010b1801031106071a06040506040b01090b0c190c06111501090b240702 73
    0xb6040150406003c0c0740002c14110008010001d94240fa0540c0320035501c0e40c4084450803600002902d0b0140340110002e9500e2800341c881c800044d26140000651510038802c660720061f02000003442c19280da11041c103402409034501584599a841d001c00b40600a6030007007841d03104400c0419140180d1080070038820a88480c100c0185907a02048a18000440c40035a100d505003092200034460f410310b07427424002c1c941d840609600c1c0040d60b00c41e901c115100071a486101700c0003400749140c2081844852991a07500d150188900c1c0c1c0144001081440c1c03030449071102600c100e003003c5042e2580c0c50b011640c086083e0160a000090181030304050242c0c6510110076035007440010106000200001c01ca80b0a04024403c0031801d443c05200c1402150007110a909140ca1407200500b810b4280070b125104400102e00e40b00c803100f000f0600880c103070044000c5c40740c002d00e070307a86848034003000750400031f10441c0d000180e494002c00400e00284c0402c000d0f80d004c500d15440d91041d10511861504 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 400707068 1250 400705818 400705859
    0xa0e0a0b07090e060a0504090f0203161e0e070507030210061805102405040509011401090f050306040f050c0a0b19050309030304060b181603062c06010c06050a0204 72
    0x3030503c00c02c00140c841d85484001c5405c150360010f1b2607411401c10160140d540100203505000e00380540c484001c403090b54501b175601514100038000032020340c3c00403402141c8a0030480100c100c0000300c4580c0100094403003c1c1c003034019603c1a910f50a0110b0840311141c200d0b0004c403c0c1c050944118180c588070742c544c0201301048a400c143d0070003404040d00e0b0048000d0041d8020354900d18691030f4800d0341990000c000160012519503180c401840000d809011014001400c100300040c01611025444048500c080c01034901e81d1166140c414080840b19401d6500d48501050b00c11240c49841d002c00080400005840c1c81d41d0f51030400b0404031954410400411a0030700601c50460004001c42e40c10940c80f0000045e0110042d011901c810394040d500045075800204110403440c3c9080d104581032141c0d901007080b15100d0158841541c4175844008c0351804640c04070300500c5450301c045030000c0d0141860100c0c1c0d416030f9039442c1901c004481c80018a40c011030104464a4402d581c00d2582d078 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 400708318 1250 400707068 400707089
    0x606080603010212011a090a03060e0d020d090524030f180106030201090504020d060e0f0f06010f0203030f04170c01060305070b09010c08030712050f1b0c03120a0e0a0b0709 76
    0x325840a01104c01d4018081c0c0840c68005041c01d100c02a0b10b40d007113862101000d448400400e0303603802d05400800d842900b0191a024071050050803602c04141c00185466940318212442d00b0803050014a50a4508d5040c0444100710f100f680482c414002d507105c0c0f00c51011100c25480c3c19120410114103500911001d40e0401e0010310051303800041c200d0170756009440041e1200d203150402c502804255218a851102c82c40603c24001c0000c47c20034403881c5900c1d55a1032544039140119400202c40041c3d8006070814800f198903a441c2d02c1115030818042c1c00304180903101c684140c18103030701048000c0042d83d541c0204000300f003401d00c0031f0b0300141140702c4c4403070814102400103040404020001040c0c1440000003a0207103000b002404068181448108010f107040915084040f0f02a150b48000291000c0500ba900c2658001c84400c4c2d03803010702650030501c207061a8100b01501504c0700154a80703402c4181d07007840e0b00304a803042150059006000301c2c148420043d0409030990448411403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 400709568 1250 400708318 400708327
    0x122a03050c1806040905040c170316060e0106030c060f09150903021002030c100203060f031b011206052806090518060102010914010b040e0a02090406090c15020106060806030102 78
    0x41051000d440b0b1082004a9070008542c580c000501e06206a402c2906007038541030600040c8000f80c11408151124030b58a08001800c11801c10340c2c1e40501120200702d0f500514205000400f83d070440740d0380d5407580d0000b0030702c80d4070380d6101e403188006500004009100d51800342042341d4800300d80c038010030400004c0b06c50301803e0180200f84503490301001c0d001d03050081c00042d4943c4200701300c07014905d0032019600e8509032044458065031041c1c0344c02e4450f1114001c07440441c640410b12008003100060800c40c1c10a4071001524003002c2404011261030780c9400008031034644926484030750041e4000c0c984488034043c1030b1800400180c11a10810120440900c419103d41c0100020b60003824600c88003503903900700407805040300340c00c01332480e151240c0d000d0008005400c420b80109040760700f0b02c0030710b107000b0500e03640e0000200e0203540400b071000407801254903503116040c014003030340221900c152282610031070850b12416420050703660b80000c0141785e512140035608000304600a40c6070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 400710818 1250 400709568 400709581
    0xd050403050601050d0512030f0403090503010524060d0207060b04060f030c0501050f360103023112050a1e021e03031b030d05060a050901060f122a0305 67
    0xc42c0d0050140b540644805012841844010003003000d0034089515580d9407850700341800d1200010995084001c103960600c08103141c43c040c082d44d8402c00d44280d206900000300010850140c24414160303170032413001c00c50714403525410700003804141d00801000c692220b8260901040b603501c4c1e4415400340520038414030004400c00030b100100d0f2005d1074401e855000880c5409018481c14410045003c00c1c885d2401340f0032160020140f2103079400c80c101c28240040801034059104030b03007070808000000c00102d590450000320642600761070b660020491606c0f5581905e00c401c40042c1a00e443e40102489020030000a4180300704a071f80340405003a031040c83d40480d20a92182100c142c4605407040a034045403810000e4940c80148000315214042140350000c0d03c0c1c2d4024800510f1030b9080c20000703402402d10811070b004451020b00314400b181c1c6045011220f141d64031100d0401c00540c0903d0305003039400c901a43c03108140d10960b410303021116550365060640e000300441c043c1410b00f03081118 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 400712068 1250 400710818 400710823
    0x712140105120a170a02030412050a1a0106020d1d1c110612060609040912050408070504020901090b0309010f050f070e09040c05040b0118080c150705030f090607170c0d05040305 78
    0x103c40004002c4c454548160070401e9046006541102c441320b100c0020f590700303010001813601c045900551102680d100d55003042403a090090055001681c4505034510403d44110090502c441c1c4c02809402c004600100140c0a0085031900100c8541c00880c00001d000c030525142080c950201c0e80e40d85402d002c003045006418004103040d00c0742d46d010404082c20780360340e003240e06890b42c003100d000114180c40c2c0b405405038109008169040c401ca42010489050130300c00c403110248161a4106c092740782c0b100b2180603074801001003d082d500c918030100b0407065401940d00172140b543c0d1000003072401c2d520041c407604e0101c05903032242d03007490148008035100340b5540054401c181c502051820321100140ca0f080900d0b401e000310981c4004000501c02c4000c03075101a070307050460346601e44840d02100310403140941034ac064000d0304204413901d080d4034820020411008041c040c42d081501d42d48407811071280041110400100000320a10f440d841801034009102c01030401605040c156240d072030307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 400713318 1250 400712068 400712093
    0x30c08060405100509030c0a380103020907170903040e0c0a0816030221040501050106080c0f2b050403201c03020f19090b1801080712140105120a 64
    0x401c0c1e00d544d58082103801509100b1644c0000360307001190180c03400340ca030038800c060943e98581a0000c4620109100070b45042918002141d01004c0f103802d42d0840d001c00c072680300301508650500c405211241e464011041c8800c0c49615414051510b07503180c00c25030320300a9802044500075403000c00c258038a441e0402000b6820000601ca40343c05070b80031520a0340203108505000e5401184a4018500d03103410030b95071486603101d8002445143d0703a4003001d07240300000f901c101036031803401e014103200c02d00341002918a01800b4070825070000703c0c80000e40c040030300c0c41ca6030707030281d9890310300b0042459007000581039015802c11142d8490148070100903100c00710010154400c0708030076100e0b00850b01c20f0301982c1120b000310341059030b00d444890aa8400b036491200e10740210300bc84000080d45c0e80030340183c841d528090810b1814000e0300e03400450380075400800c000144044280c0e40f80300341c7c2c210720070307030000020080080b00c0720350400c400c2215400305d681034140c8552101c000c0c0400244500c0b03c0c031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 400714568 1250 400713318 400713343
    0x1104080a03110709240b040506030711070518090705030c031f2403060c0201020a0e10020a0813320607110409120305151f0302040b04060207030c08060405 68
    0x1441e5000c2c14419160624400d54004030000742420190320605052001c05612086020304401c00c29a80305040046030065101e820381c010341c00d00c0000d4241c0d00a000480f010345403d025688a1500c0b02d00051345800c0009494807000300d49010044110380401c41e00024000840007880c0189190f00082c0d5a9441680882e09043e07a60f8100d00505403c0d170000c84d01319030400742c40f00c80c500d0300c2c001c0050002403d2200307640032410054140c14460061081780c041d10030039a07441040d034070014207104554070401c802000314842d4844000c0071821501c0608018003454031184102e528101d241405200d5083c04605c80d440d09400004000d00060700c0c00250346000c0d40c1203901c40c2011300f04840040e8040004942240c1030429500400a8403164104450940d403401c0245458105840c041e4000c0c0070f909039080000481c044101294058846e10301c0d00312440e015140540f40d0700d401c50340e500161f02000140e441032105004000d40e8031001c03c05410010010141803616440b07050b40c0d2955903e00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 400715818 1250 400714568 400714577
    0xf090913021e031e120406020a03080112030936051006080903030f0702071a030103170c0705040506031204030b0f09030a021507120c0e010e0a03050a080d15030b0a1104080a03 77
    0x4c07a40c0c1850070704c125655044100035281d1101c1e81c0700000f9481e0101004118001851740002144821403405984400380d01581c801e8007880c1440400300d0a01d59070443e0751280b9040c040065103610004101e8a41040130318004143c80c2048100d2005490040d007001c414080da800c104584080008241c9520503001d0007202300b65114980c0c20380c10601190040e130aa4900d40b20103414402d061401103049034030610a201d03100d40701c0300c0c00b264240200c00e00d50100350440c000030810740c9016004540c0264000382079444107a518041113480d075109074011604400090701708003e4000c4482810ba10240c0e0704080c516058190100944030340350840d10425120540d004284602e104001c8100021062a0100201c0080c8013000d0311400c040e66040e8005100c038240d00120f418211581c200301d0303502c503008110580455580307400c0b5030021100640c2c896507410b0510302e5650400c040900a601845070400d0500f855000349064400c0383e0240c9403070382c1c07080000308020070000514031321a9801d40781 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 400717068 1250 400715818 400715863
    0x40605070f1a010602150f04050309010f030612060504050f030918040c05060307020c031b0d03080c2b050f1e0a0f0c030b03010b040509030f0f090913021e03 69
    0x74001030b68803207201000307071210310b820011841d035800061310890f142c5581c20112003039440300241d201c0c0d600211001401e54100340b02c403001d42d500400414100800c5401c021400a4942042c042c1130309084009944072a110024002404018040c140a854160300914544442480428140f070380d2118098001d010715400202404032045d41c000c003a00303000341084d581c0c0c10001402136980075501c11440c8a0b010308022071038505103650f00e0341401c09018109400c00c00154030186c5061000130708401601030200400a405042083d000c0e14100910448054110002d00c11808441c0e0081080380da080600c8107000148480c0304003050078050955101c4803641d110140480030300503214200782c0342d6050818501d80c690300750b004180e00002c20b800030051a1141c2d0304003c2540d07016120140203230010030402808071600e130b004041455604100c2442c0112240c081905820111076410000070810701900c1145000d02d2038800c03540c0000720940422100c8000251148480014007442c29400304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 400718318 1250 400717068 400717073
    0x507021003060e07110c0f150d0f020406180f03170702040f0614131a06091207060507030e040203070806012109050303090610081b04020d020d0b09010b040605070f 72
    0x400c0003000d0300344803d1400242c00d1444c000340001c2010b448216050052000c0c1450300d0a1902141c242c07154001c1c03d0720b41d003070380d8512400210382c082e1208a100d40e17282c01a141c200c0130940002c0c4004d2605694010704417101c0250503514401a400403413203583c0101f010008600140022040b1303a101c0a0510b03a00e030603d10014000b030500c1c40f80c44402c1400e000c400103e00c2c4000c1296040b4000c140d8075140798920468010b0100c8040741e00c6901441404001100182080d4000d00000c0c2006003d0800c600f5980b00d5451420303015900420009030300041d031400300b542c084e5001ca0b40b01c00580b800d50460034407540203048400020010b9041120b00310f85101c4089684410742d450002c03809003044040310320b0410755140d0303104981e20720b01485840041480c500b03041050100321007610025050781c88594072000070080703a90300340d0fa0b0300940038030021001c10114402003e00d501e0250001564822140600c03a2501c0140d0000141842c14031080094907042011500020b0744503402044040c10391 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 400719424 1106 400718318 400718321
    0x22503030b010e0d0605180a0501021c02040e150a0b0f04080f190b0403050706140601110d0e0105071a070f0813020105040b0a11030a0906120c0507021003 68
    0x2e500384c9001c140a03030300898102c050f003d401e544c120100d484c11850210041400d44d280c0c0d5000590707410130482408601c0d808000a0400e600b440c4c0b45c04443c1c0d1040754010500400b0b810924250362195444842010150a04485040c0c9400050303540380d07411b411a02625455200303180288903800b20014856002201c00d410f191002c004c196a9103002c034602500440034000c01b40003180020304280140481400348540001c0c01d8a031200006121501591100c5000c1d0046645041015030040e00e00c089030200b800c045a89040500e044a0850140c00d00304901c50025000c0c80842c51340178810100c0804541c0d69844e09840f600b01100429014003802804100100010403142120070090411048075007441c0300c480c07a440c00c2e182c1c250740c040c41e644000100300f08000d1100d6501304100d0704050b451114100962900e4000140c828458403402a02c90304000e00071000c0c4c03a220307 = true := by decide +kernel

theorem cover : BRFrame.Cov 400539568 400719424 := by
  have h0 := BRFrame.cov_init 400539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 400539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 400539568 ≤ n) (h2 : n < 400719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
