-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2286
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:14:39.935717+00:00
-- url     : https://prove2.me/submissions/9408aa3d-5532-41ce-8388-fa754754599a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 410971223 ≤ n < 411151079 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 410972473 1250 410971223 410971237
    0x50a03051e06010507031110060501021005060901090c02120705070e07020d05040e060d14010c0f2109050307151505120c1309080c030909060a0807060e0607050a03180b 74
    0x20802071404284958041d10103481c10701d1103807a180341e6400a141d0303070a0400003640140d0b40f85946424042c0025a014000582d0840c2185da0030030031441c05d5000245c8008062040c02d01d05035a6120800d2403602c03d02910110550060b20740d942c4403800d00e4029900c54031482031607c240d003680c010480aa102140c0700b0b580e0405603941c207041a05000c1107800c0204094110780d80400384d031080702d0018010076150080c0b86500c0c0c2c0005080e40b4400c4002d45040c05140c2920300b00184004801035000c04411560b85001081c04001258070303044c500146188189034014003199681c0356081d9200c0343c9904036a45c0059210f0524030321a0760307141130040c0078000c0c2d21030a1854007c0c000c410301c241001400764020110649000c00e002d180740d21107801d680d0128200048c20b410001c0c5240312030405881c02c07900040305888070009280750964181d29039045008145c1048141101105150340781001d5038070b07181e0410191140c008282c034010f000d600101c2c42403a03036070342807800005034400c04009075080c2c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 410973723 1250 410972473 410972521
    0x13020f01050c0d0302090135010b040b0414060f120108010609111602010e040f0204090e0708100506010513140102010c0503130b0c0705060c03090f0a0309060309060e0607050a0305 79
    0x81d1641c400094021b90401d804407410440000e80905680104d0400d1005003500c4404084240c5960515200c507101c051f000440350980070081084603c0e02401140d08880780d4010f0b0446540079640060034900c991541c500c00303a0340124849419207007142242c1e048030969002044120b54404004064501d4900a68201201400a08000100320803550322952051500b0703c0c2c40303861034000404440c6102c234292a600d9012a0a1000c0c2c2000e108281d03a2032007220003080000c0c80c1c8075425035114404021014184d807103c0109503280d0044080e03c04484003142650707030f41d9807520700d0410080036544e540d900641c02d12040a81c054002c0c07003164000c9001c10800e2030a1030301c90301c9207030030110043c01c20307aa0b03507200304100c030b000c03400511076a401403400440f4030380d4034203100d81407501e80f00142500c10541d401040c1d50300e0000e9042b6624808460036030401041042c0389080c4800140b680c64800c1055024000070450304a902030b006000c4c4540c151400c0080b80c030341381451011100c010b0907400c8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 410974973 1250 410973723 410973733
    0x60f170406020a030603060c09050a0e060603041b090914150c1918030f0b1b09040b060904060303030507180f09110d060b0d05091c052113020f01050c 66
    0x300320241c004203e0300038542000b0a10035542d03981c1c0b0007103031000080d090025414100034001b5242148401005044011140074a420540f000800700c0c44007600041200c1544c5c0c2a201a0842141209005001c445c0d0104580100c6080940c5007035a21004131500d4040c1d212400b0404c030540d240343c2d00850b0760b040751300e0801d00010749500d0900c40580828060000f20190302ca02010004000c00c0503502c2240820071880c010301c0c052084034400f8081c440700a00f60080c0402665a0100342ca4900008940128242c0140800f0920030700c611081c450300030341480b0011060540641100340104026600c110645840038200360000c01d042c0524004031283c42e60401a91026421054440c01d0202c2182d2400c0d80b401203c0c022102590b1241070341035000f15060b510460184540c59003d0308090140c16400c84100130310b148128810a0380003031200c00300d007211011120440740c2c400300c0c28003a260007182c140a102c110540b400d20800b244035a00c0c03805000d516510035825101c440819000030300d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 410976223 1250 410974973 410974981
    0x90c03030503100f03050705030c030a120c020d12110f010209010503060607060e070e041a07020c0909070915051005130e09010902090a020d05010915030312110f04060f17 75
    0x110240c1c40a0010030070000d00401c0801c2c2d880130520404025032042006010091502e0f0505003080500c0017600e11035040002ca2201080c01e04200b0300b8014414600410117240510000d03504070240342c4058010302e0780440148002c1e0b04100301110a04090044070740b0500b00251403420303407003034881c2240094400d00200c0c1e01820103001500e01203100e00000318000041c112003502d0039034103902c611240d545035020712040c0580c00300c505442c0749900180300000c1c581400301039503441c0191100785c0100c400c9800680c6c00402440514003900203400300f440f10490418100600d143d0074040ca600c280b01012114444a003c0c1007200c01060300007031000c1b0980d2030444105280f04004042c06015500da80001d4016960b4400041c032a414041d00140c0320b9103002c40410032650140c0010107160b1410380c40d8814000340340340000441e075141c5002d49415036480c401c00b024140180014405070f0010445e03040a91504015000751100c65580749259642100304507a101e0040c2c2064003c40e651070045 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 410977473 1250 410976223 410976227
    0x3030403082d06151309060603020301050603160c290903070b130602160812062d0d060501060207081006061407060b0d03080105120105191503240c03090c0303 70
    0x503e5010a00500041020301d40710300341004d5a120300704c03c1c1c0469041000c14405401c9a100f034801800b201d16045082d03604101c00301d0307060f100c0600f1019594202d0b401c4401340510401400f8509075111000e42e81542d00d2500303841504140c0100c07130180042540014000d107000000352010541c201c44108080e4855000b01c0780a40494502515040d40801c03204000c041940c694101c0380d881228027959030800020344908602c4090401449170301c60340d01d0742680d80000e00050f01c1030182e6402d0100b01148000c0003070050702200b00020282c900f440d00018203283c010a5a4044404c90340139501e045d505240a682100c040313005802c0403030942d10309941c2004d070200203442d901c0e100b00e400003015811080001e54022501307004400140514006010324103107690b80b50841c524500003802182060355031000c0300200381d000c648407580d90382c141020301400b0a07941c000464001c1d000821014039036500e40764190400c0d5500103114100418040028400e00c07a124402c3c0c0c202c0e02d0800403a0560b501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 410978723 1250 410977473 410977561
    0x22050d030e070b1215270c04050d060e0c0a03030f0e01030e012c01090b150d0b0a0c1d0904150608010e01020d0e030f040b030a14090303040308 63
    0x72460315440741030800300e14900c0d118002c102039103199500e82c0b00c61030034003c0f0461110201200501071031058aa48a4440c528001a044040c0c45a404100d60340c43c50396a0301240078680c01260702480f40324002040c0006a400036607090450310903070343c000790111700b404041d0a040c44014005114136103240821072284800111010051401003a003008206201d820b548042c030001400210f000c07000107030041c01e96005850011a0b82c000e20030b81c0c440b600e80c00e000c050001c3c6007480803000d5800c0c6c0c50107070369000c1982d60020b601032000411400d003280324100400c04051100081030345048038100b2074010300c075103201c4d0704002080001917540d140e03182d1589d0591300105d46182526a40e0100e1840428058440758844101c00180c60b440324001020960741d0280c0100314981007000300300003a203541c100300d40556001c00c0b0b00319641e0312070410a400506081510840070b40144050140011007c00298081c5010760780c0c2c1891034550304910302180c41404544600c2d50144403610200f0000090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 410979973 1250 410978723 410978741
    0x14030c30010b0901031b0e0705160c05040212220b010504020904090209070c0b22020d051c051209010608100e0f0d03020304200a05151c0522050d03 65
    0x8155403054402044404030f0a810481d450308029404030003c0707100500b10310040a280c0107084e00c50038500f00c00341a034807844511500041800d0043c200b40315a91101100800000e00115910b4141c040c15502004080d20f6401404050407110b00c20810380201903500c0e5600551800c25030791030403041000940c40030001b1030300715442d00300074405a513a0104040c41642c442d12510701e1412541380c503003940030008000e500ca900f024012804601c40324881d0ba043d0a1707042c3e410403500701007420840c5c5080c8200d40c1d0340f2440b2410320681a10710f03078444060a138110307103138200e01b1440d160b140c40b45083e0740711401441c1c200d81c840e0750400c0000340382e600071000300350080040c1e074491001800e003c1c2c02c180c00c12a6200120360000300340401c010302d210f0351064a500044c11000c0c820101300c00030360711051a11800340310340c90180c0b0f6000010510f400300c0c1c9140302c031030b01900240d9504c42ca5400c064981259210f0680aa408000500d0240c0d0030110b05014ac3c404040d16461000c904140d0003410110 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 410981223 1250 410979973 410980069
    0x1020a1403150409051c05030103050a0b06031204140103110901080403031a03060108010c080f0c0406031a0607050705040501080a02150307300615020d12110414030c 73
    0x42011026601c3c0c62090096080c00f41018007000081d030551010007420160018041001c10001003006ca50081450000542c0c04158818191100c030002460143c0e44c2003882c01c0300324005070014603042100c5125400950030f890500030884a101022214042c400c5040e000c0b41c103400010300004d11985c800c882c8420085048912026040003107032416900346c000e1403a0ba0740d00c151806403150084060703640148181003d200e02e1500c9c1e00710030780381d000b584502420300d620f8010046007052142d41c201d40388000540460f40b07400f90343c10729558840c0f9520a640c066441c04001281280011035841140341c2c0140000c40d09052140d452111944002d1292041000215020f001c400b060741d2420640d840c0028000c0e0001407401c042001c0783c286600914182c0703510040200c42c0340e004a031192030009203060150b038440d2040c0c40c00029001c905a907499041c0c00050110b0310741d518541031707416070780e00b0340480304c02c00b0401e000d021481550b408610415094411448600c013801c0d250051010380301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 410982473 1250 410981223 410981251
    0x6051c26130308040e0c070f06050a06030f031707030c051602060915190c020f04090203010b12010e070b030603070e070e150a0219020618011407121101020a1403 71
    0x30782615031840c00c55070000c40d05600001401c00000003600e20b4035410020400303070b541c0380c60481e58505d0305082654000400513600c680c0000c540c80c915030b102c00c00444e0001d5010b5401801403900916205007007428003441070070400859030340c2d407007840780043d920300c40d483e114a400000d0700221641300300c0400c220303400341c000c0003100749549071107000c11020490180c000340c40d154407000c1503c550f60710121b80720801c01c61009107005a59081100303030140100b91400035514030f607400481c0c003400803210196001031480301d020741c0155055012800061000c4c0590306959102d0815141c00d1001b9503600f98180e00c40e58050080c00c00c524404c40d048500b505002c6480d04291020501001d42c6001c280c04004002c070b10042d0350341d01846084e4004a150a2a0403400610f81c0043c01c00e004055003081c0758a51420202000e9000305643c0403000c3c40840455151842803030038545041440c0c00300c400140c852240d41d24a05414003ea90481e000780d15007110400d0b0b59908038a41d904000e155046010790 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 410983723 1250 410982473 410982487
    0x60a0b0915040603080c010b011e0203041205010e0105280608100e160b0a0806270c1b060702010b1f0302030a0f020a030e3a0203120a06051c26 63
    0x64440109041d0074030900205800030400300142c24003c102b0001540005071003030040001e0ba000c001c4900384c03007901c250300307028a001e400c01c240100490741c60054150b203400c0505c501c030781e4101c842504400744041c0d482400003070829801d095908070320514000c0e41c00289080b6a114040d0001d00c0c24603000740859450600750b9000242c0103d0b00c2d0322005680c1d8000440304050b42d809481140d201c901515035000b032181e50072403c0204018072017103022000041001c2804440c500d0111560328000300383c0001071082c0c40c0075490301c1e043c0c1640c00c81301541c03901e20003c0700f90900014004c949240000d10806150103100c00354082e610040030302864035a240410002d040e50b9101802702c0c482c2a640000340e0f2a81502e01074a0800451501c5000d82040c0c032580c002c800200404035804c0640c0d01460502c0b091402081e8510f00070040d40807000d0031030701c04210b83e0b045998400e03421580200c40040d8408084a028000500601809804801c6d90303006002401402c0b80381e0310790034403c04c141c1132070054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 410984973 1250 410983723 410983733
    0x10c0b010e09070f0e16020f07060806030c03010e1e0718020304110306090d0c0f0b010e040501060911030f100905090c15251104050117060a0b0915040603 68
    0x100907008a42651081c005102c0616410495580a4041c418001c00254140442080c1c1001d00404401135480000300050281d0b04c280180c52840300d14000702c0303041c1a1141c070b000c0c0403640c085607994000e0cc541c040c01110742ca014060103100d00c94080282c10301440d811800103201d04440b42001051195107030001c0c0c035900801703e42181d0241d0120060300c0b41401c0c03402c032030000107036001c281c07082d031001c4180100300c0341c0865002c40d51616800c020f201030701d4500d88021070501c001405040c1c210094000a03011001d0050184558420381c000c001080d1030b00b94182c1119051081c43e40b03460f0b01440044e5108482980003500030f910005d05c2a81c081c0e0f03940800040d2001117802c01c203150052004103805040034042c5032190354152130341c2410709008510032146d0b10840c0d01d44010003d038038400b04007400001c2e901c1100103c4068402d200ca036840f00c01d055403044280748034206522500c4005072040c5581c0c890000000701c000c01103000b6482d0780251140b450400914a60701c00c0e03940d140040014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 410986223 1250 410984973 410984993
    0x5030c090a03060509010b0108010302090105060c010b0406030317090a170a031e06050a08064501023402040506040e0714190303140a030b0337020f0f010c 68
    0x14400c03840800c2c13525106800e03500f0340d00c0714018281400424401840140d50b0407001c0c40c15a08140c0380da03070b00c0301410078440d80900101151180c00c6441e100b008000c0c19405001b203441090b1a0b65401425200c500900303948018140010b030400308000c4070040c8103031803403000b000a107942d4540401d00074555211405100e20144c00360340e4040d07660300100b00c01c0c2408841d440c000c01c1141d000e0121490300750041e81c01140002003007807554029488500c0701008922145602403101c0039520254108230080c54002e40c0512440c400341400d01c0300c0c5400f902c8024000c07030408541c290b1102c071070703c2c45c40d407c0c4000741c40042c140b1039000ea00d50500044440c0c08000390703402803c40700c609000002e5240180000012600c088603a400008641400441d421001e030340080302e03c801c041591682e0680c0d048000f0302030340300c0c01c0368903018140c50461603450a04800681410005611501300b502020608a01003c5800250030140c01d1064001d45d1401c0c20a403908040103052603c0c40f556036030344a06841d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 410987473 1250 410986223 410986229
    0xf070807020d1b170f0a0b06030a081215100219030e0d06020d0c0e0a030b09031b0610081c05070602070803090a030311040e040f0c0b0406090305010e03130605030c090a 74
    0x4001850420044a9140c4c19440f555240b004091318140510100c4203854540700040a0050046a008182992002c11009840c960496489629440c00b01031001d118401550b8011403492400040b005519240fa8030403880b0660342c00404c02a43c602c0d030b05508144200400f070b030074415000710030441602c5040d00d02c9032141c46080016074804450340400215540240110704000c0c40192031062a25441da4860039650451000825aa943e0500a141d0304c00c0c1c00b1168000000e4501d0280c41240004402d03000c3c1c001070050440f81601e40c0c4107255901a41e48900640c0051443e2003104030b80118000c1401034010701c0d002d8030b0329101c1d4841d1f070a5070384140c40d981200d5001c5404402070551620a292206d0000f42c0d50740d19291505078401205100900041c02d00d800100e000d4041045009800c0002e0105040d2030b500e641d640d147c0a000000725202c1911154244000300460803000720841e6940c0e039100754030100c1b10341040002c075041d400044c40e9040b5210b00300020b01041d0b88042d910001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 410988723 1250 410987473 410987513
    0x50a0815031905010e0c010c021923011b12120e0706050a0206010e04080a030218120c121f0b03070e010909061a09070807090e1602060106050f070807020d 68
    0xc0349407a6085940c1940c5c164820380252140380c00a03a440490a008070b50100c64001c0340d01c5444001e01c0b48100150721001d0700c0c000845150008450341c0c0d09000c4012002d0320340d5808912060301d50b900d07090414030000c03d00341c15820200740340d9000c0c03006084c410420150000300407026600e90f07880c00b10320750820004100041101500c89604010710707805010081c0c280101070526548500050050707484c0308040c50303008203040f40c000e40b0000c00091400802040405404603a11417140c07100070311600c043c0102007414002d441c0c034100207251031a828200014000c04010305402c54010300e0901c0441c0c3d45401a4480051003603040e06070113018119011001500e0101850400121070040303d03851038408101d00c07034601035620f02411651290032400c2036005503031180340840301c500d09500000c240d1049202403240c1d02c50b4584a03a0301c040e010b6001c84000740d072201030554050044260408921404005140008240781c01404000380f001e0070624070211280c0d100e41c0c000550500602e0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 410989973 1250 410988723 410988763
    0x506040f140a150507020d1a06030d052109070b0a050c070906060c0215160c150c170c0726010f0209030c0105031305070b0d0507030606050a081503 65
    0x11104101601c2200e650440315480308625010715802e00d415401d03020014082c0120703c11066488403000c030801e40b41e00200ea046079203800000507190900645400d40248188807480340507500410454150b841041200c01e060684115500840c1c480240007600b00c0c01452800519205414054924082c4903200c268880001c01403191034000642e22140c0131b2800d0a00c104041c2d40c021200e54002a010341ea086c446102e840341d064401e2080001d00c0f603065060741c110314203100303100107138005991802034140b03078088955404a41051414001802c0d00400000040300e40c015000104592082901500e42ca90b41c0d0356a8450106080b546000b0946104030900060032001e110b00802c502c41c0740c0301142840360000c0803d07a6160346001850600000002040d02002d0041c0d5011030300313600904071409641c8070720f08803c0d160070049444040078203000101d410f05002e4000c2d84165100340d82c076603041031080d10007283e00c0b01c2c019041e007074130083d94801812591021320503481c0d4007181d440104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 410991223 1250 410989973 410989979
    0xe0307171e040b0307030507111006052701060f020f0d09051201051938150c0309090601030b190f0b160206090102030f0d0b270415060506040f 63
    0x405158900724078020809000c01c800e00c0303408004420b9907001201442d00150b0b45e0344040c03094901a44040070304030705128101e0081034084098002609481081d500b5001008015280342040101c11880365200620f220050114078841c00300010400100c0c4103c60458620032003150602c00424420000510488010302c41070a16141858281020000030002440c0c8080ea902c186a400d507107034803113141c451000308a48802c0c82c0c60b07101408940180301c1800101d155a40010400c9000031501031400000100d9088002d002512086080c55003e07502d407400140030000c031040000c0900341459504c4a0b40100b9861f0024481c0c1e52188200b1180181401c02c256645042100c0c3d1280d4010001081001c41f820890030b682c114041c5d045c0c0d050341d298000341c80181c0c11405503681550058a02240300304840c940c07a04550901c210684045420f9140b412154001c0e040b0a015081d84410480201e00058010190106c0c1d05260140000e103c0e41c550000544540c0258040100c60712501e03424 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 410992473 1250 410991223 410991247
    0x10216140915010c0209130213020c1606090909230c040b030c0a1517070804060f05070c0b060402040815100914040303110d0204150207090506130e030717 68
    0x5580042480100b0b410340405480003c200d644007090007070160760400003082081200b10540c085c51a0b000b01400d1401c1d0140c3c1b401c000a422000840310329110b020700d4500040740001c0941c0036601580d54504049007081380040180c580c80c0d800b142d10560300240324558000046451410b0308605001e00344404080b0100001c2e00d05401d041482504200c42d20320035503580c6680f52003110000100c40442000302501529032108080403540d000c20040100089143c0c401080e92080b48603a80401494030b81e00c1c0350000701c800032070f8448080b0304050070507000300740190b15066002c84000c001500d080e4542c9c1c03520f424003544c1c00d032200742c0d426407005002c80e0304605031601000c3e100100b01007005842d1000c1c405648000580082d017415510940ea4408040210403107540380b203041020342d9039a13034810000e2001d200303084030710005000b00440410540307000e015603401800e00509036010b02c8980c5010600030f0170300e000f0038407851000b040824001882c9028080e007848103e4590b030b89400300c038011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 410993723 1250 410992473 410992489
    0xc06081005040203060607020409060b04091217010b09060c2b170405191e0b06190806010501030b0409050105010914010906030210030b0f1210200a050901021614 71
    0x944168010300130040c603521506c0650303800d182c044a002c10040443d080c41d40091490070780c040d80090405500c2c50a2102044c59410321017401e41c0c491003801141d1b00c11816001c3d00307002d40e414600303041001125900d8103001503c1c2c2c442c3c962050740c0344c00205005401c1d0380481c8100e6070014a6946c0d07a40f00c82550000600d410401c07280e80c01c21110302d0a0794400d13454600055182c034640900f4200b15003400580c0c0101040007002681c2205006918240040d404030100c1c0d00700c0c818001d0102400a18560549550444403100010b200a908200041d00a04002c40712250400c1c2d5846451010400034017566000380042c40300062690703007012102141d060146c0160b0082c40c1000c8003000180c60b0004450000d401b1443d00284d01c5400388005a02c0703040001c80554400d007400c000000d540f001186c10302e8002c0e080141041309225103000750300180344199048203803c0c03040c0320500c3c2e603500880003449910030510540d081c280c0742c0302e00c12142c51640e8202ca0481030483c0106480c0d810310a403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 410994973 1250 410993723 410993729
    0xa020a141e011d0c030703060507050f030a060311031504031407150917030705040e0615030702010b0406051221040b1b060703050c16020112021c0c09030510180c060810 74
    0x43d0910404c00401719660b00668403004050076035034800039591612403406e60300c0f00c000984640d9524140714991a01410300c03804281c50b0361100d03020310b006510303001805284204091080780c0682c1d0b100e440554030758141c20703844401180c080164000094000071540c103902d21000f00054020ad0a0500d1a03200300440d0300310790100c03001c10038410250740210a95003280d91035a0311030744565440001c1011101e00003600030f801c40012091003106501074004c440441004c2c2d904001b4036540750108002c148078410f40340300580040151034030450304200c17624402e540351010585450303941c07000c1081d154080102500e61054042d01d07190700e07990602030307941c004d1050b160500680c1400d0034054082e1060182c180f01c4014030004000846e40100c1c0d0000890500301011903c48070722030700c0712540e881c80c10001c1210a28141500d001e640c0540000020340c2d070400c009107241d0314000304090041550301c041381c0030102c80403201e6001401d0711403004083c1c00280c0c2c4484841c2088003084c0140491a0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 410996223 1250 410994973 410995031
    0xf0706080108030f0c030714060703051b1215032e0212010506090411040909020f0d170c0a08030103080d0e06010810180609050d090b0a020a141e01 65
    0x380100002c1000005035035203000700c1c00c1910361361090701403440c0c618803030440004e000d44460384103180500700100b402449040c140c6c1b000d1085545450382d02c051441034a1082c0000703c810b1201c0342e440140282440c1d40065050f41440211040360002486c02c401051541d0700a40241034000009280203003c1c036804180d28419410a0046030780d00c90042c105010700c0c0d0042101161502903542c0b03d07007181c1c1100c1c50400140340d0301c5484281c444040d013030b801d0042c3c1c000c10b0f4400c41c44806040016015409941020305412a40c0f5600d10f1206554441804402144282c41e901401b10351090011402184141c43c03880e03440c0368581d444c800351541c070a40880250080001081024404074000c1d08c024090b102c0096000d03401c80c0200205802120080c0503144ec219005040050000f101320304078150342c888584650b40c0c1c1603c1c0c030b018411a4000b00050700030400385d000240e45c0010520300f161502003580c03100d8100700c1c10941e42410701c4141610b1691a00e60000c000c005000721011420040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 410997473 1250 410996223 410996237
    0xa0e13060302031606020d050706090c08030406140306370e2d0403030c09080601090605011b03090911040e040c050f0307060c120225050109060305090613150c020f0706 74
    0xc17031406515106182c0158050200028501d4204481544503142d15036011042101042c1c0310240c5070fa698005000c0c000200d030030041a030b01c81040307440a40e131059134002d100000d100085001d030360080036414151860080109080c1220034030150003d000382028580785111480c110100c0250004540d8584a41c02a5050000c521002411320a43e01c560182008290f86850410072601c546059100d105980124400800c44003016000b4508441d02660341c400e440221213882240304840113001404a21403010410500313110341c100301001c01070f61083c42c0c240342d92208851000081150221074003903152605000b42d2070440c0f0b40300c8003014203400410b0310f581800ca000e00681e03a0b242014201d0921a02c04000701803080103400380f031001d224014100c000301c407114030b00c400c901801028041560014041182c51003032040034450800e9100401e00c0b900d44410b6402032189a1400342d4040c070f0520321540345058107010b9242c81c40c5841e4000c0100c040100348560910300c10780c2000b0100b02038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 410998723 1250 410997473 410997479
    0x2090103051308090f060d0c1101110c0316030302041a0c010c02032a0f03130305010b0f060403030305070903081b0114040804031e02030d030f0e010b03030a03020a0e130603020316 79
    0x18001c141d404e1010b05440c00c09404a000c0c00140d42409400c048041440c2041410003c555200c070500c2000690321303000380007280080c0803020b0540106420070708164800e0160201104400103d4243c1a00909006282c40d0301c8002c5c0c030500c421540340a81d2603400020f02c810140c0340074400c8420350805480990b00b000441c1d00d801c0c0800310030781020021607004030300000c462036052083c3c5d9580300301c0340700f1a81d8414131800c014104c07582c0c2d8801a5070952a0900808143c1400741d550f109480e00101303510302e040c0c25030360f09074024200940030f102084051103000c0006058080203003c01404014620034000301c540d01d060945065010710b021200291082c4800a20720b5400d40c0c003500c4d070000c1407401100c11551201805115424060361502c21a60481c4a46d40c00d588510383c01a0750079010301040d440300c0b00f06826500c00000f004c4d0554404c00007500b0b40740c403e501800002c0d540703241c01080c4501c10300028808801501c010b40c00280c1d501070030411498104900c2841422118034ed0f040d0307a103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 410999973 1250 410998723 410998733
    0x30f030e0601090b0301020c06010e040b0a0b180a0b0405011707090204050d140f0a08070c05090402090a0b01140705060a0b011103030f072c0306060a0b0d0e031309020901030513 78
    0x10188542001561591161115a5030039015101e4070080c8c0380031140c00e9a50b900180080041c2075038160341d901511008030342d00e5416070042000800010b007140c071640d0f10310060002c1ca6080200542201035465030201403503611409664001c0442c0049808018003c40569040c15001c0c0c0c071240c02103104000c104450b88501240100041e0080c41004c0084206242c03181080794a04145456000700d00c0c0304000c00c2020005046064010074039408542e4031001031140b103540544001c0d40c807880348c800080740b4540c0c5410000f0450700600d00b2010a0b031181d00d13054501d4022108c00c60346504680308008400c1070302e1183c00400c010903c0c144100d69107094641e900d911001d040610030701c943e02d001400c01070040070681926400b02454090410203da0312401035a12184080d1083c01414041549442c016454005450248444a00e0040c0e40da00480061001001c82c0400e80020b000e405201c0c4042c024050051685400c05a55010755a00041c216000142500382400e01013030200c0201c2c0f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 411001223 1250 410999973 410999983
    0x201060906182703080f07050304051905010e030409050406150f0b0a26040c1e060c1118070206070215010509040614090d02010f0207390e0103030f030e 67
    0x18121500203404034090300f820f603801c864400086140d051041c110410076601002032846103450b6400e0b030030242c940c4a8102e4080c0300540e00034109500281c003007003041c040104400c45052291000140c1c80000d0891281943c0150b4480c1d0b10303c40c1d854017008203029032802804010300b07842c043c0f02e940d54186409030364407807018046e030b01103080b01040e42d03049140112441840003507846072900504c4c20400114440030000c98041313544c01110480080c0142e01000e500c240d07061076102c0304250320300b84401110014000c01e010741c0c50003d002d1407023080380c8441c142c0d094540c1c25501d400899182c620006450300c2c1d801b1740b000f811540610426500c80d00d10011440c151b0f441100c3e800c0303486d00c5d2820148050540060018071071240001817100d54840003c20f10840d012580007807009089000031503080b406218805408000c0001034176000d03400302041214004c050340000030603070380c15184091141a59401124040d0b40000040c800e0641191443d12070240510f03082c4040d04180c00555110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 411002473 1250 411001223 411001259
    0x1e0f061602190507050a03350d020a031b03060312050f030106030b04020c150a0c210209011707200624150304060b1f0518040207061b0201060906 64
    0xc1202c0c003200808101c000c0c401c1320f0040400512904610780c0b80d06000084200e01041000452007080481e000b54410360700320600e609240c14030b18140790b07450007500301035031046551104240d40c5202c008281064103003544e41c46040340d0380c006101811880c1020010100203460014020148030b60b20070595540100c9064a8403460081110340800000c41d0190144d0b50f01c85e800b40c0900390a881c4001a100607031403085140c20707002d00c00d03c014460291500ea10780c4000d0b0040b80c1d0f40150140d56410301d43c004158001041c9010380c40881c460f026071002070070503209940021941c00d0702400144090014940e244445005441c0c6400c044c83d500300d0782102d05481890703c60261401041d40e0b901c10400049100b510465281c3c2c0341b0341440c00c04c005011042a99106d07000a9410580b080307012001c0c1e41d00c0070029200c0901d0f048034040381701c01c0000f60200b8554000d8003001200c0004002d4010a0307140402440e020811040c030107800b85c00c1d6075007600402c400da490441c04011a0050911110003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 411003723 1250 411002473 411002503
    0x30b06010e01032c060a1109060c0a0f050a0c0608060d02210a0501150f0602030a0c1e05210c0a02192d05010e01080708091e0f061602 59
    0x44807040700050700a40840c40440208082d42031420820b02d100001d480744208140301590346560700c0b100300300b04459001c0340880c0b0050050210040a041c410000d00c1ca030101c4200300d0b6081911591219441c4094020072078058001280301c0b800c001210b0204406030500b03080c1103480d482d03c2c3c00826101076030150040c2c400c03010004000c0508141829119401c0c13407203419a54410564144a8040c141c00c00032035418903982c00300000c2400d9508802415181d40740d014500d0035401da1800c40d4940212081a1170700e0b4143c58258100c503080e60700e6203104c60f2156018050000f419103400c00e404071101c5150240242c10011400342e41d01c00302c0c5142d40580d040b11107000b104220400040c0791482d60300300800b001d0fa0b031403500c901011444030312051400750003000940030745c0f24001190441c000c942628042000040880c1d000e600807070680b0740c4425003004036544202100d8400c0030848a8072a881c006030855003109495900c00d000300344d4000791000d1080c00e1108ac0c60340095031101c0070003054007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 411004973 1250 411003723 411003737
    0x8030403090503030f040e010f062304090603030314102108130e101e0e04021c06020322050a060203090709062402010c0801140301020702091915030b0601 68
    0x200350150721000080d01d4080c00301c07903d43c1210714a4088961140c021006240d00e00d000005409900607400019940a41e035000400c42c0200c00d451102c1d0280540c42c266440f09100101d0590012302c2004007c40c041d650102d81075a964111060407080a40502e0716200c00c07813030a111b68011816504200f03c1c8040300f94040c160103090001e81400303520f400c0114001e00b1040014030350f800054150140d428031201945031640c4810346030182c4420303200050b4010915800700240c0b041c2180c05030340240080e009030304e000c82c3c00d445d0a031007030801e01003160b000b5030104c280400c51030000b0801c1c80c003038506003a14103069004c0c0c94007036940c440080c0040c000d54001001950101c414021035000304182c1d1400e1042c0c5072a4a400c2c004031030012510440b131191180c082143c0ca20500480300929281d03190307810b103030742414101a001386c0340140d00381e0590340800c511030040c1c45e280000c85c0300d80b44110300091012502c003001000c0c2e40c0242406511180c203018284003181c050281940c0005090078400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 411006223 1250 411004973 411004981
    0x1505090c011404120b060405160e0103150509040b070f05070503160201050c0708070602161203080702011e021312080d0b190305100507020106080304120809030d0f08060603060d0803 80
    0x1065500c00c90b00052000c080c42d4000c08100300c020240c103070080001f2681805280d0700c0000709201e440000142c5800103014410400065020b0350000301042e42d0b810150f01400d48a0300030544d4414152000c488001500c02000025944036540320340d404458a0220314100b81034607240d0740c0e409181b00c60b2285510541503a0308580c042d000722510004c0d01000e4820442c0d580d5585604c1310704d10320901c030160040080962141d0316030301c5118107030761000c1644c24800b07909071821588031170300910001c25596203803c3d11409280075030981406503414500961368900541c402d0f441c81c2000d51000145442a0100e03500240c004000d50307a1403440f0380310008010540f40d0010f44d070302c002c4041c0111032040c140400320503c840411b8100549001074410b11554a64260807401c80e040352190000a410a0000340003031188600c604a40c640209401c60610503460002401c200e01c1a07940c2d800700d06144840a00580c100e84201e40c01001140e40710f045207441008584401e171481c40003000000000006 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 411007473 1250 411006223 411006257
    0x3060618030a0c0b1e040f0323011503110904080405060a0306030c06080a0b09090706270602071d01060203070321051801391b0f1505090c01 62
    0x40b2480754000d0004243c8555414540d680c5a00c0410000d030400b0344060611a0401440f003110704071980d50390507003040f9145d5110485011711036200c103034250307141c2548900d83e04000d00451a90f141c110441c058094910f140c000c0c02124041c034458006c0815a0401000c15440d600f950122142a20307016540c589601d0114010300341600014003041d020fa0300414540d0b4450700840c49141d90100030410120b40904003c008401203550041a9110710400e108107481a668001442c0300200c400e071a403c0d044121182c04c07901604014010f03403019404110300381000e0701c80d82800b18200102e4030a035040102c025102c0c41070030700240a04c820080029001e0a1780c0312203960101e0702c90020451818060710402c03038043c03110400080756091892510410310000d03004c00c0854003a80e034515070801d2080010800f44402c14070b8106209184084a040091584100d02d01300c5c400c1c040480c2d240c0803841e1407a400310b11031110310101481c100030000c42c0c0b400002c802d0750594013400d0191556288041d2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 411008723 1250 411007473 411007483
    0x5010306170d030e030f0a08180f120f0d090605390708190206061005040e010e04111503062d0103050a0b03010e0a06142707050d0311120306061803 65
    0x18041d007100041d001a808e0380501518040c080d00c82d600d8810401d8510801d135034840c0354a00300910b4202c002041c203860b8140d40102070549920003400d00300401107229030210307880388a0540d03556444104210b00f01c0b00c1c180f60300104003100c10f5403176130601e80403203e200348040e00da800b04602080040c2c00c0c0d0a22000400703035125076810320b20708524109180b034000d441c0c00040d2039a85c001c0c5608100c0c44503060003002031f64241c4460301260421686007410320100800f01500c02da5207501802704103841d0352551020200488111503041d07643c0e0408a0a0150001140c0344110049a91444014441c003103682407001040c42468042000e441b0108540c00400e58001d245500d5841c11070311401c07a400124007140018000c01c81042040c0207203036520f1201030211001a0765403400581c213805840d0903000d48413101610412556030a0300c510100d04000c0120340280d01041c07001c1d0003601b0180082004030b003e032030180703415411820711101140c001e02a406855034480300d00105620316460401c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 411009973 1250 411008723 411008737
    0x190203070e100c0309050a06050a03090f0501182010030e071e0e1f0b1b01020a05180d2103091a0115030603050a060b0303070f0c05010306170d030e03 66
    0x2490a00070340c02c2101030800d006040c012004600501c100080c4c0b0f140c00c48911040310b9054484500c2c0510802d41100204410b039400c80d4420440c2c90320201007842442414002e0b20690034246e800e420f5070a04203110b00124082c01c1b2007102140003c0500c1d151510340040b53380044c10042a20301038030030054200186600201c0c03001c83c07504010b0248180107020001101c04a48454071940c40d84030b00040d08100609154074920981d04080003020303038900040c002c0800706280920002091840242aa40049000c600258011401902c40c82c44400c46c11a403000c11910b40d40d01c1206580d4a0030500c0c1140aa4604040010b64528031540a41c10010b1400d9100c80c001300396018401051406081c01c1c00b41c00000b90740300043c2c0b22800d00a00c0b40800b0340c1c4d00480180f000e20082c1e40e623030005d89096a6140d40500082c42280c0c0003595100340b800c0300620440c00b00724482d0078440010100e03030741d030b80c040300030f440340c140100c4081d001c08034078403071940e426180200c3c0034a48010359600d58400c440b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 411011223 1250 411009973 411009979
    0x9040e03030105010e1c02190b0309060103020a1e090b04110316180b030c1e07050a1205040b1b0c060f04091505100f120c02010b0315190203070e 64
    0x1851110020a000c4015410303100240c90703200d6035140500c1808000190081e420383c80030010b012580143c940814010942580c440b10580c9003500c47d540507015410a031014084ae0740b0600c014421450158001000351041382114420200d988242d900708003250720900403c9a1385846031240d1380c48941280d00042030342da6903e5a681424a0610840111800075070000340900ca01d60399140c822000c1399040303036410745141c1d0454541501c0ca03500341d0301906001c18445030700e40c0420565416800a400c549000700041e296048880c140201c01c0d400303003140001042000c00050046040702c10a94100032546040d0601c0381283c581c440e4600108440c03050340c02180800d500702081c1c21100140142c410360030041c0011101f104007000200d196004050340030056000c0c00e1040762042c0180340710080945001300c0d103513844e0001401150700324102c40300103075140c807446031142c1420440f12422444d180c00d40b1806103080500ca0100204040910f106150004042082c480c480c04000046640013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 411012473 1250 411011223 411011231
    0x3090406140a050f1e04090c06081b031003031202040801050103080304120c02150306010e13090506060306102306181804020618060d0f15080f07060309080904 70
    0xd000e5409404001c0509500c200080b600114490605500310709000354050460032900f8036040c0034010004c00c1000f1a40c0240d960b00d190300c0030549500b03e04008104545822080b03080038a1604d100f007240c02e0f03100305403c2041080c40030b450900c00032041265050b15041c1d074060030b10b4034104060703c00c0d94004d0441c0e6007040000300c2840101c8000314003403031060201800c01c1301c00701010385071900d40c000b002c1c1d070201d0709002108034201003900450380705c401403400d0004600d48000048050384158914950241e4401c03023842000410400c49411100483c020304991528503604070410840d4040c00440400000e82c2c8410004240d03401401c4030b400607d000d84900302c11100581090000c683c039485032010303002c20201030b80d4459519005980180030b56140c03035001d0101c10a06450400c1c01d03500032034104a80c201030070f00d6128042004035a1500480e240c20f2440104241d043c5030f401c02e0700b842d00244440078802000190f81d5003100e00a00780450701140e50304100d100360280c1d08072550070a0030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 411013723 1250 411012473 411012479
    0x13030c0b07030b10020f03070b0421020c01120e19030908010203190c0813021516080a0305091501061209120804030311252111070909050c0f0303090406 67
    0x580c0000304400800d03250001039407032280c405c90b03903080c4e0380c2d50118491300308005202c046030404100320340c00b5000381c2c40c03802d03802c00c45424041040340c800489401a0028030701f481c25588c0c40401c1641c00307081003005001180c3d000711125283d00251300085943c04c00c2e41d0000341018012050b040081a200e0000c548916010300c0309040ea01000c56101c20311071074506442c6100e401001801d0150010140403883d4812990a20101e4004000c141c03014000500c40c03240c040c10a41540300825220705401c5460304108040035094450142801c0c4640e04030048100701c0c04203d415075811a02c0c94a0002000c00880c11000001e194008002d030941c808041c00148003900815028001c0c2e01c655401c000715a103183c00c0b40c1c0c01e8002c0f8100948050800c01c0490b40707120141c2400342201d070052004403022083c50034160400b144144281c000303d010011607810821003030120b64000c03c1c1c0c00700248010f41c8640d9a07291545a80044540304d44041c0400410a0b1010001c2e00c3d00306202500400030b480c0c03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 411014973 1250 411013723 411013727
    0x90e1905060406061a0a0c020109050a14030c040501060c030c1a01030f0c06090f0308030916080618060402010e1012052a040302010806130f0203010902030f09060601020613030c0b07 80
    0x4040b101070b11007a082100c0020340b902100856a8403030011003082d820820210750032241c0c1c0d84042d42c16130401c0020580455159141203d41c402458041c0b14940604488801d0500b0855244030b43d5105500e09001000200d80041021069a90503d010300404002c0d15000c1907456600040c142d101240100110800c06c1007004903050b20301074000c0c5920705a4452040f00c00d8410b9000e462000d03c0c200fa4204002004d0b20051030304100d00b01c099481002d409501c052420f481d95000050f00e03404041845045e203035001d86002e1403c00704014041300d01c0c00b900060304d068034041c1e0751800b0342c0440030000d655a22034100d00c0003040c6202824013050418035840c0035844a9008101c003c081d660703c8140c812150802150102c0794180c4604c12640d90f11410407241d446124440e070f1400752100c030381c542e8002040c80158007030400d040c40161a814400b1742101610002441401d040d8480c03018050180e0700016025488900880506011861403504450f076918002009004039081000d001540fa = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 411016223 1250 411014973 411014983
    0x40305060c0c0f07030c06050c070e0c040e0c040b0301170307050a14010614101808011104030b060d05070b0d0f0f06140d1a0402010e090a0b0a1e090e1905 68
    0x420100d0441c0c0d10190f04920598803540c6074030000700321600c00081044594081c1c1c01409100c0300d000c2c00c1d510343c1c0d40c1e21540d10194200484080c1d14411000034140f01203500c41e100103400440c1c60341c04a0919050002c41b82c55444103001d81c012101d0700c00103000d003031501081151405235101e0162600c1e01300b0b500e8072004030281c2800701005035003000c0317010803001c03c80e00c10b0350800103004250340001c690031758051300d44c0910b101c1c00e0700b8003072803406000c02c451409000d0386d440465990321032981c4910303604125001c684041d10b00740c40740c90603041e0755002c6000010000c050b14007904140d40d031842040c103030b080207201c0611301203c40e07418259082000c00090307111008442c110001446c01c401454208000980302100080c080c280d01c41400c10b074411003c3c00b80d9031140c8181443c42008002d40300241c1d0000c82150604095900c03584202005d080c02c800490040901070041e03011040c400810b554a4803107030182e0505503680d8203040c3d44150040242500c000020541c801c0c07800c0701c0f420995110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 411017473 1250 411016223 411016237
    0xc0504181e0f06050a1a070227070f0f0305040f02100306050a03060230131104050c0901090b0f0706050c07020414070810120320070b040321050a1202040305060c 71
    0x945030450380000d2900c2c80c0d020f268801039507411343c0c41c0350031031540c01c2100c1c0001d5560f841320309087c652035003c0f05404001d00280180303280e072a40c2f007520014200081400e6900040e00c1c0070107040505000005194114010085504a500c80910f200c40d120460003400356034841980080030f00b1b000006d0001c00d5000b00b1840042d4464219007504902e04020021800620305030f010b0000c00c00030f112115122425102e01d442500260a22000c800006050b2001904c0c000d05071000007481105a41c2c014001c3c03030082640c586110b00f4000c00900c00c59150086c2c0c0070250050392244000341440d028101110101d650080c4104100c6070113542141800b90201d8415011a4195001c100c0ca554040c030090103c030846404201c1800c6036035000c13101401d06174082d2000c201140281c58490b40c045c020710020700344034900c9030744407403070f6042031600f000078510800c8251040303081e12000c01d0b501004032644200242030081032407101300c0d404c800034405d550006e0300b14000c4100b0f219903021410014101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 411018723 1250 411017473 411017479
    0x50a06080c030a080f0304051c08090d0c320709050105031902100e03152a0403050c010810080d1701050f0108010603240807090c0504181e0f0605 64
    0x7034406041c10b0690341c0400da5000303012101c080c420ba03408403002400441d0300070b2150040d50100c541140845102003052004480800d00c004100025881c00f0803150340c88200c02e103171526201d14035407182d014401020180c3e0000d004001405490709050100c120342c132155000445411a0b554042c84004003001c1c01382510034010020381c115001e0035036617040012900203044442d0424005001c2d10300d00d500724091501030040c030040941007074010445910070880229001c1c401c0c44002c074103500f80d100045100400400070321040c1b01140c80003c40c8468003c080c203090300f0f55103c0128801c40d58166074444822480382c105e855040544c044056502030360303245103609450340c0718000c00c0812039030b035041940000e030020010006140309801c0602d840d02003c90761070950625501c403020700700c09034000301c010781d100300410040d5800c03610504500d2080d03840c19500345030602407814480625503415084441d116015216602180c001c22880350881078000c201d1214000c011030040e00f450f21500344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 411019973 1250 411018723 411018733
    0x18040b0a05031002180a0807051c151d01090c030f050304081b010206060a050d0605040c080d09030203060f040c17240403230403060f06050303040b03040b07020703020f0402070510050a0608 83
    0x195030a040784683c3c1941c0c0c100008c0c2c22030302c0c18502404421110303d00c40301c8613a034000c800c60020a5401980d80c0040003d00000305910840400541d0001078540103c0c0c8030360724096494000c216003007000b0003900c1d404000b0801c0c2c040f95042491075401350b80c01502c030360b0190340d071400402d07820600d884600980a070281e542d940e484004215600010340f041580110700c400340c11001540960106c1d9015109045004a030b0b9145c44820345000c19205101d404504104c0087c07055203010400d035030f030009421050031140e103010340d28213130618290f2140c1d0308441400306a64900c8035081c00f030080d040c080000071122030b0070803103400601080140c0f000d401044103605c11100302e5050181101003062140c04c440d143c2481c4d80c0d00e45000788908203104000660703401c0042481d940501c010401402d5581c040c1e074403400d050a2030042c3e40000381c803940566000c240e080006854608400c20603c07800c0760010303101d16040c2001800c0070403904030301381030915010420484040341d50101003640c008004481c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 411021223 1250 411019973 411020017
    0x121106070801030b01180e01020c030c0106092703020a02030105130311150c0a05040504020a020c01120506030c0607080c060708012903060607020109090501091e0218040b0a05031002 80
    0x501c1c5924280000742900e8071400060000d11441c0e5044100c200300010001342c41e840030081282203030005401d05201d60030014038154004c1090103400c0c05003c1158041008030b070300421021084664950103aa5210f03104d48401c140f60083c031501d5115074015000707018034942807940c40c1c00e400080c0344c07c401242d030800343c501c81c0d83c074001072081540c15213030210103458865017500991508050344d56010800d08010105054a4500141204501c1c0c0d1f0010402c50320b01038005019003200c5601555541d141204000c041d650000d07130a2440d400a961882e078501c018280b81e1094803802c115003402e48512401c1c043e980f5030080d416030480c1c805101500c81905403a1800c8502ca0420303c1e00c070307083d038000c3c0003091840c9401030080407603610505101c031280d940c8038034510544009038000d40550303a652405610344880c0c240d001114199040c0e0071440d12810784070210001c621410b1550040755110807100b004c1c5c550035100c02c06400000c3c212003442c0300780c2c241d0034003035800142c040007071102002500e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 411022473 1250 411021223 411021227
    0x6040c0c0b0103140a08040305070509061f080a24080d030c0e0f010203133209040f050c0a0b03090706090509040303021c0203041b0e10090203100312110607 69
    0x114080e03120881c660036920b941c80389820414442c0541210f0b01810a140e40003400740300081c07008602c50702c050b003244c0d880c01e800c00034880720042100d801203069000074061017440c0621040c03031500728281421281c450060480007044034040001e5030980310f54500f4644143c0e008110225583c0b581154200a000d2004400ba64808517901d404640c1d109071111441c90024200d02d210034040c41124108245003452040f4803549a03c64128280c885c100d03000303c10a4008404490324030007898030305d201e1402001c100030324002003001c2d010301582000705040003010b00901009000042c0a507102e60f41301c3e03070424516803003542c0030b64151084200000e8071a0017148a10100c400040107807410360b80381d0b10150040d61009558030303a0301d03014050000707002d051403000e90300942c0508481004285008650096000680c000c2280038503040200548030240c00346174000c2d40c01d032a07009030f103e45903045018070342c1d03180b40c000408099600f10030300031480c1d0004292080300312010451b00961a15441 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 411023723 1250 411022473 411022487
    0x20c18100603110a1209060507180504021305040504050c060d0212011a03010614090d080415020c0306130311031b060a110d020a0c020312030709050f060a1812080306040c 75
    0x10f2440c004403e1104408090295110315095050040003040000031540c6500c00c5070404c41e035100114032030301941c2101a1001060030040d20043e6011840c00c0d61505416200c940c00d0321949125503101d00010301040004c1c03089404403c00a44001d868041c448041006904031000c003481003c460310000a11401510380e45500000f100d1486145900740b04044800039604508010f03021810415040740380c4508107901601800b404100b900c80781060b4501c0d002991038213150045500c00d02410b16656004200c83d6008010314003002c125640b10b107800d603034a620340a9001c00f0b42c040407421842160008010100303010300d40c0c040c0c030f0017a582e40180320202e842c84c2986440c030b024240852800043d80d5401004615500d0602440d00e04403035000074036090b01c000000308216408000d02001c03541100c4180c01800049680000302d01c891000b18020740141c00c0d6104c00c000d040696201c8508420300390070050409400405040041420022159801503038145e0165240c0101d0038074076441488 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 411024973 1250 411023723 411023741
    0x101b21090e0f06060c0a06050105090c030601022508010f020c0f0303040f11040e010e0d080a0c08040f03050c0706110d080705030a1d0a1506120302060a0507020c18100603 75
    0x52621468039950007000b184880109542e82140c02080311034100300c41081942507442c0b185030041102d60402003405050280a13181c010031942c2070007485a10303a004a2111456003c1a100101172348500c5008c0e11140070550003081e05501c0c0011403400144076800405400070800e0032120741c1580c0300c003500c1d540d1100301c4002d087c0102c40510200001c5c02034000e9040355a0080001c00c811880c61859802c492420500900700d9002c3e150103030701e090b0404000b0b5031080030040c04020b45002d08401400c4180d008000a2041c0c14924000003007501840548110180b41400ca414058a81030040c0401e90361100c00d030110300c19425991030035031185201d00e00c40c50043d60340c1e03811742d2038541000c8040c1c1003001030780410300308a0090441c0500c040000c04400b80c024030983c9252144802e91008507485a000a100240115410404a9000110140c03c04036161000034141d03200300040b402e08011956007039110315294821540300c24421407031406800d00c0c6000160f0607a80c4e40064080300c60100c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 411026223 1250 411024973 411024989
    0xc0a2d03030504230406091a03030a020703080304021c0305040801110406090302040e0106032f0301110304021c0b04081903050403020d030e0a0c080a120e0a05101b2109 74
    0x83c004010401100451020402c01e118644d10104002800759940ca0304115501c0342d986002c1024983c0711151500c1440d0107801641ca40352041c02c0007520b8510701e000c0a040340c0000408181103480b80300e6016a01c111801141501d22040c2c600144254040c2c17242e40700542c201034183c44007216030070484044a891f0784805070030f00d256074280000b600009600b040c0e65540c591000002c16120030b8103000f03100e1280d45040c400032000440341c0c1050320301804140a6890450081b003000c1410080b6034009030105e400f15041c40d10300b00c8031480e8844000c80100541200420b0104000c01c0c14003818079180c51020b44100b0018080e0101c04641040f280500107078010030224070340034040c1c0d014581024481080e950000c0d656148e0286019869100001641c0130000400505c480d10082006030183e034903088484e045400b0000d807511030107000c1c051040c803418102d403100602403100300d907250300c1d002071040501c00203040c40b9201416180c2c04e030050100040c075a549040c840d01512044d24a03030307 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 411027473 1250 411026223 411026227
    0x21201020309150a0e0601081006060215060f030f10051602010e0703021203040e1f0b040e0c0d06031401060608010f0506030406020309010b1201051b0f09010c050c0a2d030305 77
    0x50250b07040307100544058604c0e035071652103542e1074405014081c042c1000600a080c0c011900700c0201c1240e178a036002604542090f0030001011561442030b541025084542600c00342c0580c00003410510b1000c0c1031115031080121000300d0840300d421052007109254034078008000081002e07426035400400215468102d07074814001440c3c447d02c026210b0003090304680c1008c1d1201340500b182c070002e0711008201503801812250501000328100e011300400c110460410740b5003030030f01e0b50201c2c3c0501043d18030500407072900d1800703460798094030056070800070158102011000c91030080c00c1a0003420700284203030300042080800030200508a8001804240c40c5507500d0b11010025080602445801e540f02e95040055544418000e0001c0f00c912000107418240120f8407a01c1030100350b651080d02c001800390f4811081c030442501c00c205800c3c00c0545500b085490134605207510360f104190300025a100104101c200000080980702800c44000f0516641042d0242c0c0c52000e480014001801 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 411028723 1250 411027473 411027493
    0xb011707090911040806101a0f0f030c0d0b040e0d05070c031b09050f040201090e190e03070204110705210705340605160c03020319021201020309 64
    0xa201080303034410554504014080d0b1580181029101803601518a5050101d030038401d410062007002c1e000500c264051110700d1900c032040c00070819070104503165550101e042007680d2003c17000c0b41c2d05040b10010301a40c074940303aaa440c0440d081034082440e9035107401c11414083c1818817515540b400c14030f0061003d2040008220340300d5000400848080980003000000680d080b8420107040000c01c0c40b4840301c6060045410440740f004290070390700300b505410b000150b6084841181030b10b4607081c0300440e50303642c0f41c1c00c0d101202e50003402020071031420f4041200210080301a01d03119108032000e02201d4907c1d40e00300b40a004914004e00980c000030003000814030307501074400c0c4136250020507500b04421500e4160411182c040749880074001c0c0d005520a080c40c4140c20040300b0307400490422854140100200703680102d00c911500c03590749180410500010401c4000115030003000c641040c050558000300010300780070100e020b0800c1c500341040f262818001c1c0ca101d004810005c0c119090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 411029973 1250 411028723 411028757
    0x21030a0b0402040902040902071a070c03030207050c0a0b18011d0f010c150231090b01030e0a0c030204050f09030306210a030e130e07090203040c0519090f0b01 70
    0x20350681c0c815401c0200281c900050300141006042c00c804c010303111070450130007171155111aa03c0e94501d80c201c40c100b01000c0d0304285100700650305442d0040e212132031450114649400039034255400382d010400054107034601e0700144000c07100024072024031701038203005441d00c003055003643d500d4110443d184415414450f0814003048230500d0884070988064a440380c0b540d23a00b1044034200e9800294608028485410b120000d860440304035800d1790b43c407108840c0700440350040e00061034886500b003520b0f80c882d41201c1140090103003901d904d00324500c1c044440441600c400c9000314148000a110250103440240c41159074402451031a5901010070054031000c82c016a050f200781242800700050401510701c055100c1d80304d119004006c1030400550310201c40012003060b0419403204802c0301d0120f5000c04881c0414009030f02d9840c0da16107240c15042e02c0c2c004d560030602303c1c1446458207041e8000101140c0c0c181c4010070504a00b80007034404e940740c0c0f490050115500c140c01d00d2841c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 411031223 1250 411029973 411029981
    0x4050d031b030c02150307020d03150f0e010f050102010b03190804030b0901020304210c02040e0a0b190506011d210618121608281121030a 61
    0xc0c03080c40c0c541107030750800781100056810300c002a40000d40e240015001c5040401c61001500b8442610074114541004000d42da041409955410035450741d41038481d0100410944000c1d003115626035810301c0d1901c803144a202c0302482890801101d0050009442d401840b0f03d840f48040035001c0c1c41580040b04240d0302141e940c4104481030b074410000000071400c0310103001d005148500015130f80303080508000d0034509064210340d0402101c8240d0710f01864000ca000e000301541550013040a44501e100c01341043c058000180888040c1400c0060b5602c505855244510b800002000151180801118911604403d00717000220038421540c036440c02d407095040d2504180100c8203502e807060859800d04100b600d5101c401c90a030b040d00c038680d00e401d0141d00850180381b4646030608003c0214902d50f04071400b40981040400144c91009900c0540001070780c2d04054803101603000d514034028050601d0314103404081c0104d03c00103050700120b014504500c1e484544080c1107848101082c4020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 411032473 1250 411031223 411031249
    0x1006020d0c08091c0201111621050105070c120207080d05090d060f050114041103010b030603030c010606082d010b032814130309030f02041d0a050106090606050405 72
    0x2250050083c2460781d590180c9640c00e400d03881107255150703031051001400d0114070410241542c2c0040a41d841005500c00241c1c080300c0841109012071900c030718540c0b01c80c07044081c002c0e00b1942000100110260480400403030f042c881e0303100300096800208201d0f01c0340300d1402007040540000034885041032007903000e894588402002d0000c01c450550b90101101d40c008000e60038180c50f20010400c1030803903070b1a13140181c402c1d10107000e5000743d02d12045540c03005001300303400390307034044049a8192410025610038002110003000b00750348420300541140c2d402c91f9804201c00500c01100c02520705944c1c14a00b81020f0f103003040159007401d00044c03258000929441d459001060301c3c105104146003c2e1040030f80c45403000540307140c2c1001c60808608000d144914100700251002c0020b0760018411046030342201d0401d071900d86030300c0010045c00b40c110786154100203c0000341090200403590711039203889070300204440d41c0da42e1800025201d5920a007008104140820002c50030215407c001e4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 411033723 1250 411032473 411032483
    0xa050a0807031e0903020f01020f25021e1309230319120c05090102100209060910030b030f010b0a0e060301110f04080c0303031306150302040e010c081006020d0c 71
    0x503010a10820034840250510382d000070780d100d10244d424940c040c8094440c424503080254942521080c920f14148076401c2d59242c6098500103a040701068003814415456000b81000c00300c148800021803140c0d014a4524403403030090405030f0301c0e8503c0741b15203400c940c0d00c00062100701840d50308480c002d8504140701c19041c0401c202203000010078074000300441c1744039210700355031540d03c650810456819070101800d0140811401c0b5503603800048501d9004209540542c5e58850600456194001d000c00d0076006100131301c0f60503800390540c010802003030007035007100c01e034900c00000d4a00b80c41e20409040e80181000304140140310911038005c1d4060005000411400300624502409500c1041c10783c40c4200003082c14000038105001030b40e1584400ca004608500300740702440c6d40ca0302074900044c6007035034940c007405004c04481044002980c000b003081048661a604030b03030280c4140040400044c4002c8006a05541e003a042c1c03c0548460f0307070007802e480031130500941d0071000702c55003654 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 411034973 1250 411033723 411033731
    0x50411060d0e15040206030f0a0b030321060a0b0a050c19060501050a0b0304122708071802161202151501410705070f030b07050a050a080703 62
    0x151209802031141207024400081c140c2103509507207060081d400e4440d003480148000f80405a80ca4009881c2c01801c0070301c00214030380719150424010101c446e410380d0180004600f090f0742c05403170301841da290800c540060329a9900c0c4000c0101c820002c0c00340b040b10000030700c414103010303100f84054a00310841904032008100d820708103d002e25004e81042b105143c0311030050040b404c00782030341d40041c08030100c95802c0d401d060b51281c3c0610070440703c0004010246510314000e11f01600c401094101c80700301c225601d61940b2155403620f6240c015001484c080c4034910311424460b2080300c90703c180194619245e901d09a4034161586084142d400071031040c1e1102d06980c3d000440300c075000c1d04c0f02c80c1d16140380384103040015050303d08506800c080c40c03074440039084041420a9118403644145034240510400810804001c0e008002c03015055101d200b0b13020840d012000110401d80e406915a882c2503901c146e822120b034801c080040c03000610500c214004280140040c3c2d030096000d05001c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 411036223 1250 411034973 411035003
    0x5040c0b030c160602040303020d02150403080630061303050904180506150f0a031a1b0c0102040f05091003030305090106051512010e071b050c040915050f0403120504 73
    0x40c1d008501402d1302d00c41c0e80000c080003050303010803401d47c2d98401c1c0e0000d001420680c04c8404407071600144003071706205041c40058507594446941d15085610041d0000341b50392a0080d030040324200e25920f402c03031701c55030b00810381041400070b5031014035034580d940c60300d450310318401e000107810746006800802d440c010740e100004009100c2030b8403d6090000d00d00d80f0b511a00100407140f9480040790340203085403c801c1c070120f41d1300d01c00a01d8040781c0110510058440444107407586820144828543e003022031580f180c000306400602c2211600303085452101c0c0c42e10108011610281c40840680c1d090b12009c00010340640c2204e0351040d211700c00000c0c5560358a020403048640c1307640c0301c1f500d03541c002180e1a15080e092001c03400341030380c42e416007040e140031280605148200c81905500310102228031040200400002c0342c4000f014009101c2e440a0340b41c4156070400060a03c0219418540012000d42c0010152031040390151340302c1c800060740310881740083c1806002599110350100e840 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 411037473 1250 411036223 411036247
    0xd021602040e0d17060d0b070c0506160905090f131106040e012112050c0709110403031d030d110a0b04080c010f02090d08090319080d0f05040c0b030c 66
    0x400b048541401c060002e1070842030b80140100c03140c9014102080c002d0003480015103664130803c260b81e41c08240e42145440d0241c1c2a01c0085030b0500c0201203104020400c0704d08000420401f40074100f644810104946400400148500491f060100401c40d0800102c00b440e40e12608540c4900401c03010301c000e0840800b10303d05038442d400c07045100184000400c0200554240c454155014440f44040c1d2400ca0342e036190b40813815541c030f10070041e01054100788030009108040c005c06a508007007240780036a000d10005c9070410310007640070800011404803501c13000140312280340c0000300948003035207820030240c2d0038001203001c60115208482014001600c5d20b540319008600400c01c0302d803a40d501942813825100102e00b0b8510050041c40072000b00d032110110451250740c814043ca40f83c4120b41c010a180c41150081c1401416a09905000b4010484010181440f01a00505c00900106804005c0e078000759801440303914800000c2050007501c002842d044030324401e42c03e15025a406003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 411038723 1250 411037473 411037481
    0xa1b0314010b09070c03020619060905240d050c090403030e010e0f0c040603020607170705060a09020108060d0206030610021f0f150e040b0a0f0507030902120f030d02160204 76
    0x50000c5a544104031038691a1901d000d6a00100d0707440c04645281e8156402511118068a80f6214a00c0c1041c00345400c0056004680901901502003009203051800045400355201200f011114654080c403440d013409401d0020450f0090b00521034403405005010540500420503820150750310401041e04000380a4041c88003080001020000710500c40c1905051180b40300b40d21403450001c0c00c02c016181d00f0140c1b0381064110b40f07680c034040550b5003203040a1060b03105c01446800b807003042000b1413410703502002c0d03400e00030f0b03864076901c0d5980780a00100c1e51518001070b6201d0814000505585400000140c4207040741c03042c0c441c0364001d107118241c031868006244550b107403614503219180310380d440366020710208810114a010300e41072840180107400750019001001400c00643d14034036a810410101e40d4801040045162295004008001c40c007812403180d212071001c0b0945a500055480074117a0000145203808203185515000750700502c4520414800003003100d002d80c0d40e41c45 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 411039973 1250 411038723 411038753
    0xb0601140c0a1716080901020c0406030f02011e1209150501121401060612050603011b020c090a060b07140f060709080f070506090d11032401170703080a05070b01030606060f020a050a1b03 82
    0x3241c4030b1f370034050320014140080c0c540d42010b04018119220300d83c558806200f8451410003013001441d2041d80c01d0002c2d02d0004544560308090400000140244144045158041c0100c140e092010a12202c5034241d80c518481c1c0c10015a020190b08505001035202940004000f000001c010f41d8040701c989000f00c441074040050380001c6940022402c000445a52290701d944007007100130b00300a894a180d01480202400a2000c41c42003031190b6010031000e154a802c502c2200c18510b80450024480000d90003060140e0180d1503041e9aa01c00c002414000d0b9080101404d0410880c00c1c04c1c03103003000d501d1206803040d03003a88501c1030b469101409034600b106a10a2213a036030380310328440f090030b841041e4402031501c10340402070760343c0da0400304a40d4280e9070b1102c08a9901c0751418402c903118011034201500e1221103000000800100383e0101d000c50b4055107540401500183c02641c546803204c0001e0400e820040401c40010400000f00b60804001610011025125190003180c002000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 411041223 1250 411039973 411039983
    0x60c12090b0714031b070c08010f02130b030708010905061801030f0203010b1002030d050403142205040c21020c1504200d0b0601140c0a1716080901020c040603 70
    0x8800e01031190380c44043c000d400e600d100409071460800310401d8107000d4034a050040c0c402408542401003020803040d03240141110402440604480c09018000f90701c00d60400c0301d050400707040018481215400e82c0d105004c2515000c0c5030380c1ca4001d20101500300103090341d41c08190100c44043c8080d103011031074042c5014a10440344584140b040c1800c4480155242e445242c29070240c0021940c00821110a10058031005c55035898600c0c09944442403640a803d6107140816030b111401070f0400c050341c041c4500d580200441d551a030601c0704079410000e0701d9001606000900042d1419407003000c5d10308043d43c60051500c40400c40a50418180030020482c201d040000c3c00103004e140821002031020182240b00300b419198000f51545000d4000140a44000300004130540c1c01580101015040c0712280f599495611b003d058840c020008101c40c0c002c502890700e514228808241c44c10382c120900c5804400340d007600d8111041d0480e240303050440c4180c003d240c0a5464501171100158469 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 411042473 1250 411041223 411041243
    0x506070308100e010b03160c0b1312090503030f0f0c06240103050717090106052220091302040f030605061008060a090915110c0616020a060c1209 64
    0x4401c02140b030200d81d80000c0c00703001a9001801244440310440fa040041e800d040140031400d00c4056800740c10070100902100c110b141000907140308030000070141071107424402d9900d01904003e0701c4983d51801031541550003032080c0310b101c0b07a15900804012911000c4141040c0100100c145420011181041c056110046402540c044020010600c0c035003421700b0300180c41e15890042c401024502c8806030703441a100801c0f0f4800c000c0d440100070301405003103680003019445280003402000c0004407086864102c00d2a42c82403901c0c0ca002008a00880c2645030045c40010820038002c81c1e0090019079908110001c2c04103090b80d03409000b1445500c0119040c94540100500c10403019449401c3c4203074202004265551000d4100589030b0581000030b00d080241420108600382d001d1480707806180010100300034100e80042d1000141807022212960340e048070346078081d042c00d403813580075a11103d114000908613030401501040304d850428228010022920160380030314105544900c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 411043723 1250 411042473 411042481
    0x606050c160501121107060e010b0111010e03030f0c040e0106030f0e0105040b06120309040905010501030c1e0b030a111204020a35030f03070201060e060108040b130c0506070308 78
    0x10300031070001c1d016100c84600414038000018140c04030441010405568034940f00548140010607600705642018040020103644140d0900074140d440c645804a40380c03824190003050140192001151000c02442c1107403a050804080e407000645100d500c01014031000c80e0300c050365401c2900070082680c010a04426214482049400d880950200da905240c20003010420310500e080d040042036a864501c041152100c508500624a9080d4000d00380314100c03080c010150802d9040e60302900c1400d0100d1364910700c0158000f1400c00c6644103e01a5100f00b01064a001c041d56108a00f80b40c003084c1e50301c0034844003c1d2175108000f440b2001d40404240020340c20409c041c80040c0625251040481c0340382512054030002680010060200303040b0200c02801d014801d41d1840c60803800810b07120b041a00c00a806080503001d000f40360b0280b1400500325601c500c6005000315080002d402980e00d4a8046050540c22200b05460b0318412000004898030303070000404010303000340e03240c40d00740c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 411044973 1250 411043723 411043747
    0x9012003030a050c090907210207210305040b040b130807081201080c03030f0f120906071409010504031b150e0909030405030c2404090203060102010c2f10060605 71
    0x4005002d1840d124404e005c200115200c1011182d0000702c107042a03403801000c40082c01d11408070050030780c091800411410100401d01d020703110024130348003203c03800301c107055422000c0f91012500903248021041c00301d8041031004200980040000b040ea0742066043c0d114031190703600459040312014000590407102c614031060807805003505101a04c07900d404040040d540e405010890b0200400000380650aa4054011544420310740612182c00c0d142c18811941c807150219540c41c042040264a10008001c050860705028016105c441c1003078159180d0150300c54400d484080d003440c00c1280814100c0860855051008030f50360341c40d00c01115403040c001c4005c405404042c85034014401404240d4011820650880c0260342c02c1c0448400e94104043c111042c200e030300405a400a0086998040c80d0000c0d8030a06c03080c0c0003402101c55003441121038000402142c4030801644a070f01c10180150000701882c1002c907411600c91613606c03400541201c03d41e44c02032002c51400500962000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 411046223 1250 411044973 411044981
    0x40f020a060e130e0d050a0e270a090c030b06010c02130f06050d080d151815050906150a2025031a0a020408150103030e0a050d0809012003030a 63
    0x950707502030901a04401442196645c9044090a0144040410092075076071107a07560040b1860000c100c40c030b04103803032007084c0340352103048000d21400c40720300c0c0c0059820290390060103012940100040121031840c4c4403d90100b502900c02410840d060347d007075015a541d00b29003c03401c0349081c40040d130700090070b42c941c007121007590080d1301500799050114085030295040e50b4440c1041c00f40450008107599013154500000e070061b110410048594440e10b406503481810000d07202904801456200e404028603004111045584030a0001c0c0107101c04aa110250001400d54140880c42c5055440a10f43e940c021000034003060380038021312401c0c042d510840c031010b9840188819559400c68440480c4103103119000700c4044404004a0b42890095044a008000c5e1109130f40030083c014050a084070300c2880141c0c00181082c0d1040024036011089000b158401000004001110741d1503011a13003102e16080d043c007404002c0c88800b003802103460b00003900c11001441d6203240c14070500d4115 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 411047473 1250 411046223 411046249
    0x521040b1f060e040f0b190305100605060702010e0102030f0c01090c1e031415010902030708061504090f090b01060206040524181002040801060611010e06060108040f020a060e 77
    0x5070001003410051541c20515010900380d055501054103950303c49070f40041c0249600d1142c202070113400d068481400c1c00c0252055074481c405403019110400750110170b4445600035142d06c01003c022640066000b00110b6809001c1130040e02d08100b0750360310001d03044d046803a0b841c0d8580d450344449020815840d0258020b880e9600c3c08410307413a0319924008643d081404024841d106a00744c51310180000c1003013507107080d161105402c0a607150034181001e500b05440d12230100d484480410460b103045402d100d24502241c07103450902d4540440200a00070329000609650794580c001000f080075005818041c0101d13400400442c20140341007850080a012044a0504946403c0c490000d03040d803c0d9401c90039950100c0125580a11080c4c10001040c1c0b00b100700358800030b40003401c00810341018040340e0882c0ca40705900341e003004000e426568404031400241d0417900000300f10398000c0040d2a00240540384039039038440c095012401042141e0022004103848035070700404c6203030072030702401d172 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 411048723 1250 411047473 411047521
    0x30b0f0103032015070903030e0a062304081225080301060825021c080c030c07080c0f0c0f0f09060f03030c0a080304020a061409010521040b 62
    0x9562441d00c0051091068040501c210040000041100c3c00c0c2000f0b20100408424142070312400c00c0b01c0302820950061208502140b513101c80c280f46403134a000702e80c080300c61945035543c85d0111072035580441c00b160a034031080c8101c10b110209032440100510300d05c1001100495540720b8001071001c400300110340f5450403003882501e811002803041010340c0c3c11603850342440c6695441b541c05000c0d10448649010407a12101c415140d4000c0e4005243da000403070007601c4043d1280100c0d41258030b000111070ba544030010420102d5401000d000082c0041ca0240040d2070500510084040c1000c1e483c019000155005030300410385445d064003d00b130384483c00c60342100a2a001004128031010013802640314004090500741541c13001d0040b81c05031400c1800303443e5152030618081c501d07608240c4080c0d00401e8010740108800d80a03419103200c06006078244c13070810000301c0045134150700003040c04403030001c02e50401c2240410304480d503014520078400e020061812210580d4104030141c003d0320 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 411049973 1250 411048723 411048751
    0x201203070506150909030910050409020705060a0b060f090904030e0d1b090c02060403080403030e0f0303150f01022e0e060402010f020c010e1e0a030515090a031b060b1306030b 77
    0x4d5003120000440d406240b042d03c00e0300f0001da100d48d09440700d00440e444403a629000154003010030502060491150095000400c040310f00360041c08464040c800d1030080740c60301088100075615211200583c800d110749042440404c1c004040b41d110740c07c2c1c10342101d98081c002002c01c0b00c03041ea120110060680c2a00030003005030b00e8000250384103000307000034040c0102c0c80081810700d440b0750060001c00320150202c580445041451581c0c80e8801c03a01d0354012200a0b1858105103030000100c010900147d006101c0090828204e02040440f11800c6088041a510790f0040035203038010040c4640172480941003601e0715000260030300076642d010204540000501c02980da801c80d25045a991003560035010b4000c0748412001c40d15100240903078010020100042023100001d60030140b802c103c0210341203a185c6c5514540c0e2004000001000f18240902d001c1948480b05120f11245004010101c1c0e140000c40201d40030f217550701021500e041e207070b6000380144140d900410740c12485152640c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 411051223 1250 411049973 411049981
    0x91a150a140f060412020103060e01030f02100c050d0c02030c030114150102010e010f02090a15140309150c0910090b04060e130c050306040b06072012030705061509 72
    0x50000a10341c000d0440c51289541e10701c1e40d603200c4450381d120010014080d10398880e00c50103102c0d06600e030402c049001030b040803000319483c1a04000c5e5412030f03038060010142c1049503800c01554500b4840f0040811004108850118404101d1510201d81648074442020380c94018903080c104903003400c50090307040c140310002200101440380e900158242d81901c1e89481000100e02400c0901c0e0807841c07940c00c0c5040030b698154a03600512141608585400d0b14640c0c036410340c101d0703807208d000081c01300340c0d0340030903411516018001750741c8800b40909442e01124135901561001c1c505444c900c035107403808980c40d4690b04140b400102c90004600701400003d2400f5902e881e00d205a0150710308003c02403443d2906c03620f0b120410b03160340b9a0004140080c12110344c000303180c1d410480300944200e0602002140c2420484100c40c50f440d0130450510008114000050300c0d1400041c2d21504480301014200c020070050024168042c801c0003d07120300e00f8030703c852268441c403c0c3e84a521554001c0240 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 411052473 1250 411051223 411051229
    0xb04090b030606100f02160801020d0501061106060607080d052a0403050c0d020d05061602010609020408100504020604150509030d030606170702070b1603170c04050402070c0801091a15 81
    0x10081c607480c10b01d0300001701811641e0803400c0803900d03008418041c0604d00003240d420019000390902c924200300c2000a40e0381c1d82c0080340c210080600001c030507044600811a0fa040c800c0003464800e028006003440c00c40c0a00c14102244e00445020500340c0c40f5203850520000003c0d582c40408140c0d9803a49d05290458035a1a259026294414031844082d1401c6045480c0c069500b04480c0c0c0020070b4600628010341105140d0791700c6415640154642203011038480d40a01c2518255a6807900501c2414440b0303061400a000c0a40182c2e4070050900c40040c80c17000c1c614082c80c8440f03c0c0d903113150b1140400300030316140c1250b0740040f00a06003000c005000301c90b8040c00705401d02103a40046202c82c1c0340e003403040e81440e005800a040d640e60024002c0300020008640d01c0d03100303109555003030b555034002c10620f000100c2a5510a0060f0082100300305500e81034002e0200c06001d01d00581e0203030759070b504003421140340e03981c12a11180c181c01500e8004c8d00b0258000c2d0703c60010062120046410000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 411053723 1250 411052473 411052489
    0xa17061f030b12011d10050c0415020c0306070c060605040501030203030f03131a06030d020106050a0510020c042a05040e0a27140d02160902030903070602040b04090b030606 76
    0x20141099550846080581e4880407807040245041c0f00810001c08402100f0340040c50782610403905101e0500314400491140c07090303030301c940c45150740a81000d00304190300e040802050002411841503861841e0785640070700625004811a4503418648202490a50255052940300601c038914020040001da180401125200821032100d60f54036520420114402c1510050140c101c800f20540641d01803140c0309210302a000440440c0c082d01c032160402c80c03c2c0d51107030040640050b800b60701004141800800500175940314015940410016404903040703505a14201e0380110802d40350f10f482521114050000841354070b0403500c0e140c107040f0400c801c03600181c00e4503042c07659251111000c2d40d4480701c00440043c2c0850030180c890040c1401b030444409480311001034010064020840d074000244040c0c0004843d511541c00d51410380b02500a420081169540f400100040000642a44000e1001c1e180c0910200d4885040070f150740102c1d0103a000f01030103503211005021080e0f0fa4414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 411054973 1250 411053723 411053779
    0x602010e070b1e03040b010501120203131211010513020a0e090c0d02040b09040501150816030b0c040b0409020d050a1a040b01110d0309051506010f03150b0a1706 71
    0x10400b80e0b01e0010000780342d04001d00039210102450f000c420301c82040300000142d03040380c00036a190045107400b003117540d00728802501c54004402d101c511003000030342d1020500300c151200d820141c6000d4900d041050035980221041072190a000c22802c0c11441d149920f00003403d09440140300d68542520b01c60f0b59040b01e9903a05e8407400540042804665882c1c01c001d4050b038001e04101164142480c065000c1c1c071441d03102e031507544070f45400800d102000040d413802d482400640b40000b10700c0e5460349401844040d00c595603001e403c010104200e4101c0000303100a02c985c4d0303001a0b44040700e15802c0c0c11104050010340b001420002c1c041d04400002036840b4030100221000a149070800c030050318512580c8080c421140500e40c52440004e0300b560242c20340900400540d2002000074482c502d0f2507104075046808906000c112001700317440b0b5441071103031101c00780c40c2c5204d00d03440d50086181a0403032550a030000c1c0c8402c0140c005608548070042c0c00c40c030103030381010300d95000360400c200c1c2c4071403c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 411056223 1250 411054973 411054989
    0x3030a0911130b1809060a18080406020d120b030c040b0a0e01080d14040b0d02090a03060c05070c0927030e030610060f031a010e030304030204090c032303030708070e030d180602010e07 81
    0x1a00c000c0030f2214406041c3d108d6512120695880fa1345d14400382d01e640c900c05c0030750b000c143c410101e502c1802590140c02e500c008020f025002c0c1c40001d0003008000c3c0400840703280c00010102c400308554141c0c400c524064140c2000138000004418002840405070140000c0c082105000400c0490b01034000da4621504001002da1039502c800c0201d12a06180c1d80013900d003a00341581e503580d40350090000c04c1241e008014481082c3e1300d032000207041d1005844220044851803040c0310300e8035000c8000c00b540d54428602005c460303003214006440d04a056621030b80c84a00c0d004100456034100040c080c01629604040c070044a4415802d001050289500c2e418410400090905a41c0920485010f154003c00c01c000b00f41c10390801940140903804101c0d00007250f1122000b4520b074150748125030640c50002107255030742e001012151030402500003c14003010516600c076545d03040c40351050003101c56403880058004500d404000040980c070141c00c1d645480c0f0000d0901001141c002c5c162240c0d1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 411057473 1250 411056223 411056231
    0x30201050c0a152009030a02060306061308031c09020a03080a030209120120072001030906020d200a05070b07110f010504020f1203030a0911130b1809060a 68
    0x1600c0701410304648038401002034080341c00441d014800390f8001c40c03642070048640180811410850700c4144228000d141d803561244600754010302e8440010340d803103080a400c0506008441400804005035600548002e410102d01c882e0030400c070b800c00c0285500c407108207000c50040ca40104000b46943c1c000900303607010001d00245080d000c0c2e01150b80144002d04980d0394a101c54002034028280c820041e8101c6c0070342c5886c541c2d01c03c0048160b40074541c115240c100302840c0d43c188a84005855190f8605141d112503081002c42c10a1020b041c070020800004614190b141141443d105400d44051881000521080c84025800000e8aa44035880700307405038070380c6071004155103000034030010a009200d0700c6100b103a0004103410480c080da10965490214044460400a40072000342c01088035500900000c1c1c00a809904640d580900a6043c05628110680810481045840394900c5540c50341e81c0501c29091071001c81c0340350503014060107020f040141d4800e1311160081c0c104e040d00d64131 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 411058723 1250 411057473 411057487
    0x24070609030315170607020d020613110d060b0f010504120f0c0509040804080c0607170a030902060310030302060f070504060c03020f010204090501091d06060411040503060708010321020703020105 86
    0x41e0340000f4a0700c400b1401050402c1e62280c03902501d9850140d540254000c101c0819650740c00010002d0f200050b036005010280c2c1ca90f00d68001c003280e001401d44401c504544030344440d464040b950003906000e6130700861000c20380070501c41035118102c04c540c104982004204280c0c160707000c100ca02154040204240030185041200c04c00025400255020b4000307008d2004100e4a03100400440c1c50850554100403540c2041154a00030124064030711951501020744003030644004181000032410001050901c1d500410032940003103588514010344900240185034040054661016200100d1642c07031400c2d02c40200700c0d0065100d02005e100b801c0c88a4000c0600134004001a6a00d1a000b151a11345c1c032042a00540420302c2103607540da00e4200716081307115050004a8104142000800b600c2c0c0710101030100405c2024007043d12900c06200100307840d9024450075004001c2599000444d5065082030000c601d40866207005a071490428a0401a00400d180e0122502402c0c15512005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 411059973 1250 411058723 411058727
    0xc130209040f022206080c0a03020c06150103060b030402061207210218010f08041707021c06050601080f01030201030c11010207060603110109080303011e0b0a020c2407060903 77
    0x3500d035009a209040032480990303442e00743d0282a181c8132aa100c00d4851440c455180e4252107140120070000d0b400c04005560703606039100500300d20402c1d25005161024189085051140544454409031207604c8030010765a418003543c4081c0010145091860600e03500044040c49961040b94002c005c0c24000780305070b8001d44032181100c102d94050b040760080b002141009500414440701402100e464411040d4894180c000f603038940c90301c500700e181d2584e84a0850f10088140401c0c2001001c01c016401620350707900c0a503100c5c6012141d1141415240b0b402c500f6601e00402a0381080320307043c2084140d80e03030090a0b50444c1d8080c03c00090803281c41c40103c4011702a00301e00000d544c00092a0001c01c9000e9100d0b40c1241d0040d004d640350700003031000442d6401c041c0d10580000354010720041c0405a00c05190030b4003400000e002c035031140c1e034a002c06101a002249002c0140c3c206640d200707418140207a030700c1c1044d02c026401c41a4005048540800d84c01584400307041d0f1a0b5843d81903003014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 411061223 1250 411059973 411059977
    0x4150504120c0503060f0609040f0501180302070e07030b010903060c0201021e03090607030b18060a1e23060a03020a030608070b0418180209100f2d080c1302 69
    0x1510884081803181d40b0b080c401c0d00e41429100d044d01034419100001c184a800d1300b0000e006140092800d42581c8503070b200d10103060314a201c00d4509550b15510300c4130105140c0700310542c0e41d109070050100c203460103502c2102c070355004101c1c03418107040503001009aa40b00744420309403680100d0000348002d030000700702c0c02409004210f21018084100c0e041441c2900006148509804422039401e944d560204a0945200341c46a541190341a1350589200d031180000c01d5000070068200c8000341da0f102210103d280c4818560141d4400c418400d100701086118400440e110130401250354050030808904d0610942c0c42d45020503074081640110740d40300303800c0b18005125003811a010142c407500258580e40c0103202c4c0d41c5d541040b644003c0c00140780c0d4003400d061b140034050b4020f0344410540904c665403c00030610110b114126001180c0e40704510700343d4004d0000e40707810b002561500107540c0c2003032a040e401c42c50b41441000042000c07010009440b0713903244040e01c9a03a520382905014001038 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 411062473 1250 411061223 411061229
    0x1407050d0807030210111b0d211103070e030f0d0207090b0102010e0a0c060f0c02030a030c0302030f120f07020f060601050c0f030301120c2c04150903020c09071404150504 75
    0x3075402c0542014035280100064440280105107c002c0c01c0c1600000b00e0383c545140700e008021420555004110500d00480f040e8200f81d6840040307a0300c4400c0040d8510340d8011202d000c0401c200385a507a19509040008c0700c4108980c000400c1c410f0403117400695a0b184a200c2c1380002d50f1108404a4180d100307410075640641a0400c40300d0101c1a49440750203100705002c1c440c001840c00c0480c507001031141944410a64026016000300341854a040780c128005c00c00590545c80100280e240f1010312000a00d0400049190381015003041070810715246806000700e4110351085001c03c200c013101041c0550044400d08080b544c1d0121003001900380ba41c0954048a0360102000025030b24400028003214070348100c81302c00c02240c4034400d050302d40f84150240850302060488180d040103e4080c1d2580180c043c0b03103010039044800c07152600ba20405441100180c002c01100300e80c80c18052551a040f0060382498160f00e03910b40b0380306805000e288900781d00d04c40746628495142c1c0c004c008842c05 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 411063723 1250 411062473 411062503
    0xc0203180f1c0f060c0212120408040518150d0203060f040c15050d050a0234021507140712080f04030803010b03100b040b0d1d01020a0c1407050d08070302 68
    0x1034181c241440c0707500c82400c140a441039070800381140e403031794404520040420540402e113411311242c200c2a10591a008000311043d40c0100004140355030358503200304006440404010b2540341101e0100341d480030300d0050700d0003580c1000349032006a9010900341ea10402940e460f2041351740343d080c0009455443e0b8032060600054000d20001107a0040041010503500d02080c00a0385405081070102d00c5101d440c0021010152481c400b05008140041c0d0510f480e0b4600c0341c0b07044440d400180b02803194001e8a01988400208802085074580c180118403907500040c3c40840c0c03401d08a45141c0000e04d07002004008000307102400c0401c02816a00a5500041d8250700d03917841d41d041c0511a40155211030151750b030440d0000300c1550740000c079070a0312101c02d0a0703404c0c003510403040703005032401445801d0240750006145100800c2403020300300c4d24410b03660300d0b0924034035030616071058801d2090032182030b00925000e02c000c0d00d40c40c10050441c2d5100c07002c6a52041c160400300d007845402480c0c0f00d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 411064973 1250 411063723 411063769
    0x60a0905060c07050901080304030b040b0c041a1903090210111c1106010909080901050c2b09081c05070c030c0f0504140712020a1803080408010c0203180f 68
    0xb1080000340030054034003d4459419590703d400c801603883c000d5200c0180200c015a0010700052081d0704110381140d8000c038003904140c1c90310f5240d0000703100300c1c00b040c466031404907407820380004034401c81c00c400c081c6003001c000c40001d50b0042465400c40700f1170303c1d041c442c40c0c010040071070608220380c40c1441c00310040640d5007a1202001454030107019507141c5030b80314600001c0f0701c0c1419842840b44056020b041c440c5445020001910f541d0026141c00b00c2c0780c0605aa5241c0145240000100c2d07501014014400c120035000090150f038007540048849901ca030301c001015aa1248000040100e40d01701280c0ba040c0c203180030541a0016000202490143c140003e0704006461b6158240d40c0f04840900c00b0000d5400b090440c00001c55480d00090f040b20624034401d00d09900500b04d280684c036111003415a000032001ca500c0940d0300c11205100300280400c480c003028400c48940d000c1c0c2d88061440c00720303000050402040007041c02c2d0301ca0707010482403009035a2240d61504c0c90111014480c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 411066223 1250 411064973 411064987
    0x8100506030906011511030403060c0908100b100203090105040e0402040e1005090111030411120111040b040305010f0e030d1a0d03030506040522080c10060807060207050a0b0702060a090506 83
    0x291245000c5c441c1c40440788194190509640c081da4007a059246103900039814180b640e140e14020740381ca82e01513024043c25290101f0000c0c02400010aa02c88281c00802e00f610a4818407041c03603078420707003c402c64109000e8450b01c1d07a40f107400c80307048840c07912002007107840b1400040d00400c482030142d015445130100703074610031141da00102d02c01c15001000300203001301507207020700c45c1c031084034001d0001b49124002145d601e07160718900403070001c1070300010301c20b404001041001c2c0d0040d00b041c80071100200b020070400909004030b18a444043c44203006c000c0010142c02d990b400b424800d03014180e10790a0084041c901c5104400c642280100382c9082c40942d401c02600030202550b12900481c00d20b00014401c01e50204030442c404c035050740092003040243c40741c90b060b401401e03841019003c1c0201c45404904140503a1000d840751001401815203403800c041c0c503044407036000c0350050070354001c10003050328804240c03071801d0340613a11580e0300d0b049141e00b190a04d08641100f42e10800110f804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 411067473 1250 411066223 411066241
    0x4030b18030c1c1d010c060f0216050f0d020619020706050f06040b09090c01140412140d0e060a030b0d0b0f0a0f1e020a1404060215010506070f030810050603 69
    0x3c0d15911250307240720784115910002103403890601c0c51071078498036100001555951040852040742402260300003001200402c00304243da001c1c9482215103400243d03480d05010042c082003169040c11030052222802c0903501a44540d0003c28101064254800141200c03685c0d0b0121070100354003600801945c0b50908901c081004180d4005000c0c40c502038144116042440303501d40201c050500030000010344400448640c08480c02c1c0305000a001c1c4000600811000848190b6505c039240100665a020b11521b1401c80ca02480004002082c401070402d511a5403c940400b1210711740840c8288210000c41c8206038095002400d0040311000c01c0f9240280d190420b0140204003002d0005204d445066410f0303031060340e00d21002c10000f280c0400010f082d58024400020942440008000c0354070701a12030781c02139803001007d030300540415695007010420036030244c00b04440c0d480c00c0c5a03058403006500c14a0003801400d00c400c0501050018050031411002081d000704615901d1030f0031440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 411068723 1250 411067473 411067483
    0xf0d120203121e0901020a2708070b07021503100311010908060f04030e030c01141e04150f030903300e1612080316030605090702160605030c04030b18030c 68
    0x543c1403a1443c04040ba811500c18022134510000b15644c01d2044456401340100114072000589642801c20500044801c030500241e0b00410440d141107413204254010b111100310400c29078141010308004100740e806004042c24147e0b50031580641000030800c0058408030341c0d58001c583c46102d140c00700070305005d840307080303a01c81d0744a96030300385805a4003c180b6030395214800c04135012a40e810b080b00d0100b110100a400280035a160425031224091601c5849600c103070001c41c200843e221b034082201e0f40140118100f62403d147c200002c0c142a200100001132091854200704a8514102200020002c592198600ca02400c128601560701401d95a03800c1400081c0300c0078002d14006085080d00e00c240018a8000c60341301c0c5142c0c1c401c0c0c2e81d88960244c088140d8207141c0d5464011900c0c2d201d11441034400c2c03c00750001c11840e80c14420040341541a680700b40b082040400402c559121000240d5088941c040b20341119502d0ba0442001040c80d03d0700705480380d11001c0b421012403800058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 411069973 1250 411068723 411068761
    0x10207020604080f0d030e0d03050a06030605070203030106030b09060a05010324120507080f0d0c2904060b0f06090d0606120308041511090d022205150f0d12020312 72
    0x4c110307800b03142080d1096003520012100001c1d076403c00f0720001c0c00725029030421f0340d0203212900300003025512a920a000c03202e0030350320000143d00c080018412140c162064981441c0222940c2c0310618100340028a08602401000d04058586070065144500c0c0c8a00000b00300d0400c1c8a141d0083d250450104003040410b420350305480750740d80004114001203000c043c4111020003030f0041240c400001e9030054480c4234200c80758000c40846090210655445480100c60301ea04010b4500300b6050000540c1e58007041d00e84140e400451420043e41d410003154608601a25000001c8a080c2131001c0180490b5208a541c500d00c0841801010390050030b00b031103144100740d00c2d04070382e6500c0900c204880e03c82246421600381000351004502d04030b0480540c030340c802003c040e550307015801004410041d0140003c08a61500e06120440711224180200c1d40b00903100c003100340e425400080d884459035100035226980501e0b0680c80300b0310a100b1a122046000300e031100fa424450400685992245 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 411071223 1250 411069973 411070003
    0x90204050a0b2715010507050304091b020f1509070e010806040507060c15020f190f0207080a020105192a17030106052712030d0f02070c06030e01020702060408 70
    0x1a00b0b144582035000400f058901c82040220540e0355075145007590341101140e82e0520a0910070030b030000d8010001040a420211008621221662211000380c03141303107059010b54200780c4c841a00410002016005000304201e12041e03130310742c020301d5400c004540e00116413900901d00080344036500000c0e0980654840d800f01e070407032503030740000315038a0f174485000900c001107190004040c00f040d50040d000c49689480b50504d410003e000e948500480381041e000411854251f101034542c040c00340c03200410b40c0030060440f4030b046500003000380c4540c401061448005001d449511031040c500308203190044c0c2c45080740f0110700c000300390355143d42403070071076802c00300d01c1c805034441c80242c0969040341c032583c407032609103c1d500f102c42e8079045007181c503c2d0103a0180081a001c51741c0380d150080908040d040903503596510b0198820946d506d04000c100c2141c010014480024121140041200d000e40340000b90801100c0f81c00b0b001e442030b104065072106010401250701e2001290300280900c801c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 411072473 1250 411071223 411071239
    0x50409030c1109011503020a020c041a2806120207020a0e0f10030305071416270c0f05180414060f0103090305040501030b0a0f0305060105100201061208070204090204050a0b 76
    0x582080f10f034100074000c1e50301450704c0203141039407680280c010b824105401c1c015a40c00c5001c4030081012280211496060708240300e80040c05414000c0c000c500031881c415213110900d181c00e040f201c4ca544c145c8643c404005003562100301c4122581d050702c0401c0e40c01801c0440042d5145c0049020440513160281007040410100d0b481d070a842c00380718101c030351603190f142c18204280c03108007645210f1100c880490040324490007a21604030701d00d401908481441748020441a1031101c05080d00124140c826442c244500980075000311a13441d440400d490483e039a40d103188040041780185076146034010381421040d90712500302d01d00f00e51144006980388a00041184011806c0d0380c032850015011410400090001d544a50800300144c0380151903150316654400e4101209991a802560182c100382d0050050313180c03825107010890440c2c8000e00c4101d040903040b1035081c120740001015494002400c8045444503000300f402c1e560000c2041025181820a0102030006080d00078410019 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 411073723 1250 411072473 411072503
    0xf0409090314030712020702060d14090f0105091c1403040f03031107230a05030313020406060503010f140d080a080910020c0a0204051f0603093f09050409030c 70
    0x2d41c1a02d2050072255103e00d48a0b0a0070400c1009502504003640c00810030010f03404e0224041c051080000840102012245080013400b8240390040302001c9440c0d04000c1840040304001944d4080f105409425070181c2405070b80c161040c4031410f03c2096410340101c10082404007040c20f248140d4003944080c00301c691020613403800c0344a0039800400f4a50b1034140c2c02c6405444030064080005910111414000162161b030301e99001102d41040030300c43c800d85081181824000c20780100440c0c14100e046505100480f002c0c44540e025601400602a00395000b507950301036080a9140c0050791181d940044d81001032100344211406003c602c199084e0842c0d8201034130071030315800d800d107025146042d595801c120107403101030a103201c6c00f00005013282c3c0030400e80c40888020701107510000703880c0700a440c21001c0e83c02d0700d55260548001501603121056954240c1078078520202c051203005040103401580c0c14a412781200b41c100c0e00d0704000008241e0001e01c11521a401005040e03041c1007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 411074973 1250 411073723 411073757
    0x50c091303200115062f030307110c031501050a0b0313030e0f0603011e06020d02150901060e0c0705010b0612130c090509071403030408070e15270a0b0102120901050f04090903 77
    0x8510000303806e0a500400000300200c1c440c01d180d01080307948605641c07c500325000040e16041214404203901c81d0008010400f0b4134000407030034020b02c07034800203608600d040d518400e950600c1660280501651340c0c000e40c010340d610783e20b0b840c03184e00080030951656116a110312081c008503c42c0c0e00200340050340442c089000040d5410402c0140e40244503401c0c907400d242c1d00350040030307204a441c0c1d901d13440c021414000c04415180704442d59691280c8603103c41c01c0c010300b510750b86404180107503010000d0724001c41d40015800d0780010304103500740c6962001d00e00546d81c080d25070301c001840c0d4a007400b440f11503075000c0340510440301020b0302100e816001604250b1680321f148a030704210b500244007003001902110810340c2c0b09440c00c001c51516661400420540d01c40780c82e241070040e242910090194620075402c0d9004800c41c54200854082c100020390340b9001406542c0c00c0080100f849076080c0c0c49613044480540725290384680321541c8a80d175801038204403034110045400040c2d5042070303070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 411076223 1250 411074973 411075047
    0x90912030545030309150115080a0b030a0f08090111030f1905130312030f1a010503060d210e060310060305040c050607050c09130320011506 62
    0x1c101200c801d0642c4010307440c80c54090615030101c4200095072520b00e59a01d03402d10285100700190409400e080c85011006003204005030090369551028482c00d82100d40c2c0040025440501b10030005880304a0300c00081c41c04041d08002040c0d61000c055003801c000c0c4132030141c03a200c1020780703c0c3e40030900d07101e003203070b8a07406004403403901810305004030051861401100103e000c02d86c01e1151800700c1c15122800541115001a90610f880c05124100150f01d4403801ea20302483c401d00700300c02d640100c0c1100208520321170302e07410001c010000c00c4240d034441e81000c1d000d562129032541c08001c107819007115036100400b6440442c24507081024241000d40c1141d00c20348a000701d01540b2424003601f50300811001d8015508403070000000b02c0c05882e0180140422030061000300f582040100c10401100701c000c040b200324071441a40ba000184e046803c0d0450f40d41d0140f906201c409404802d5070042c2000140d10850700c0e0000c00006d0401e80252040005171108054040c01200c143c101c14024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 411077473 1250 411076223 411076261
    0x4020a0e130b06121315050403090b0c0309100203040b1b06010b0a0912031214061306080706050313020301060b07050c0102030a0c03050c0a0b011502010f05040b011e0909120305 78
    0x24401c00c9003c0c8044201d04046901500c0f015401c0100240380e00e0b40e80e50200d400400380700147e910401d0006054102004100411741d81c00d0151500700b20700046074507405424105805400d08418110005d4000d00c01c1e01d0150510072015030321030740000481c144030450866618914000c680c0045800c1d00050304886c5151400e0301c0f803140b51880c000310200c24980300c40c002da04110050307192980c16142d50050422080c244000d0120f10b091480c100b15103246844003407045145091020016138402080000442d80141070540d00d9546054034a004001501d0009606518060700459515018409885858062421115089803442c010380e520300c201c1c5210004141032525040c00248507000a04c4c0000c09d00094501da607405030380340f0740c03c234800fa002501003041041c1070300c0d50a58244644184280d1000080c803090402c1c0d00c4052034201c042c05030810304138201d41e44d0401104944020401005202400c01c00081c040c03c0c0084a1010030f01c44600090800b0302203036004004c0a8101a4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 411078723 1250 411077473 411077479
    0x110a08030402061e0a0305010e06010801030b0a0c090306060b0408071a030621060406060510090b0a2a110405090a0c0e180708060403090b1e0706060504020a0e130b 72
    0x1654440e5003c1182c140c106039801101401080003001c00012030002800300c800d0075803000f00b05541080c140c861201002030815040003094001080492038401a107908140303c1d4200203299a032809040362854074030340010341080d05040c400070310309c9540e000910440f000c82c42500c8140740c484140303a2081e142d094401d11451010f0012039058503003201d1601900c4c0351724071650b0098000090843c1400c0044506443c0159142420031103802c0180070343c41c040344107182116a83d41820110301041c040c085845081042c01e01078010044030000c04403010f07100c0c034420704840041e20300d03140340e1042090210074055410503020070302d51040024504000c0b03a00200c22003e40d418042c0a5001c15001441100d0900c40c01202c80308500041c4507a0026050300c0b00a40118070382800c028100300b030564003072000411f00300b2544d0904045050145500c48540081d10390b601d1041c1001405400d09810062340310380300161420100c0d400400c1051200c40c19109224410544074003801183c41010013190 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 411079973 1250 411078723 411078727
    0x705041404060e040f0209010902090612100f0e0702012d090813080109020906090601090b0c01020d0c031b0906020c0f030f0a03020303071812081e0a020d110a08 71
    0x100200c80456800900031014000003101995203100e03070780414042c0d50036503110381c29854101c10b60900c1040c00340504280c3c2001e500d4002000c01159162003090103131020350100b1404155819031030244900103002d560100101507071594003d24130040180c8180d0007542c030708a1010701000018407820441c44400c100c007400c46485200a2001c0c0050003400c50f07001004108400c0f40c5100140000080d200407800003ca60110344140701b50145c0190005109070840420007003035070b91014035107040d1902400c1c400d48034217803040c3c107902901850241d0b0f06038a0520180101040d4144c0c4080c070a8052130702c040d5070055468000b51050001802128010f8010491421030313418088003101440001404603848210010301d4542030a08000c0c0407030060b00000700b4071840b603510800e21106c030f540c0340f0070032076402d49020420386400020000080c1781210200d031081140904240ca84841140180320355a15049010003c1d100c1c400e01410002013104140510400200003c03000f81e000c0c2e008034054 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 411081223 1250 411079973 411079979
    0x150a0c08010513020d110c0c03010605060421060b041a090a05010311064905010806010905070210110a12180609020a120303060e0906090d050a271706070504 69
    0x4c0d6100d000441c00e00c0c0e464820001e00131311400024241d8130071700409480c0d0401540304140c01d4420940c88030b03201c0ca00510003880403010300503c1e0f0002c1d1040c4028000c01c0c10b0380d032801c10054500c04403031a5005207082d07445044120311100e4540c00c070804440c410401c0d550061100100d80d000e000140404291040406260a0a40040c40c0340c00b0707500d070340701c0800410090720120442444228085070b030010030f5a980404200c0440309299a060006000703a6042500080d5205014415002c9213901c85011685550081c4421410400340d48030511070b02c08072460000c040c0c2e006100150001d182d980c000030341103030117100d1100307400080e50505c800642c00e600c07a0000792460000c1a44d010801d8440096800d100c3c000740b203111403103074401107881071a07c80c0c004201a0001c1c00210650411b0080100210b000b148503152030070b06040035034445546810480c0c04200b40c1c89510340c50140a80c40c481e40b0402d500c05003089400031414a0880080c0d6241151a80800e480000108100340018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 411082473 1250 411081223 411081259
    0x7030e060417040302060c030912032d0c0102030f010e06100c26161e02090403080a1b080f0718060f0318030e0109081626150a0c080105 60
    0x1d2000c1c9202e05031500e05003616a00003403419031040c0c0103242594400104081141441d0300c41c6030300440148051400d000401751000000416a0f1200d03503180c02c90801507855101403001c1d500e4441c641c2c80215140d290100030300110400038080c4122042100300040c1d8245400f01c9480400b043c80d59400ca0701074400c0c0d49200c1070b140d05009070b404c0c030f00340f0388100c3c840d802c111005414413080842550030022103d04090000040c0407084805a041303110a050240c0c45003c1520703089685840c160320701d5541c1512000040c00d80b80941d0300b20740041804000c0071540106154090040d00c2c100c0d84035034803480c00075140d25160212074204141405810820103000e00340c070010100d0907003808039040410202030701d4140b0490074105c02242e40c49640340c0032946d02041c0000602408001080d600000c58480340c1d4030801c1c0d102c0c151003c40c60304d00c5103c010b020562410460328003a01103407039403c03a494070188a01000c9501110f4945030511074503245102c0c0c9941412620040d21170344a0090307180344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 411083723 1250 411082473 411082493
    0x9060f0c01180b070f02030a090608060a0e01090209150408071703040e070507050607021609110d050a0207140105010303080705182e032a021509010203010e07030e0604 74
    0xd80d04280d5681e5040148410003861060b056a20907aa07404503842c1481d80a005000130380e4440701194810301c180e40c02c564114548e802541c1040c1041e4486a44907400190000c40035000b400e1905015400001c1015240d0064243e0b000b0403521450b00c407404580420a41c0101d2040301056844017104020340301525420265000042d01603034070703054841c0c5892411400c180e521400094001070040c062203014024030307400c000c040c8041c109800380c3c00c00101038091240503481900d5628030a03440c80d0381600c800c555504080071810300c400d1070708801041c000d4204810a40300b00066040c0103211304410701c00d2034140d81d4140c07552191a120b14100b00c45541103c6180301d880185840d050f08a990707260348921f2080c6200c81003c52070f12590415140d0700c803031090300d50141410150f00151890f8410078cc08240380780c2001d907503204181e04504a1401d0000203080030202c030b0f10000c1c003044000c1900154141d8510038824101501e49180450841b040d013122000b035030f006800450000358404038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 411084973 1250 411083723 411083737
    0x3020c0606060a120e07060f0201090c0b03070302070b2706010303021b06041d04060b0d0f020d03170703020c07120213050604061802070605010e04020306070e0a17100b0609060f 78
    0x90b091010321980c0d0b04c0c41d811104001a4262540e1004100b0000c0c164815104160300015100070300510707059a5800c0710f0500c0d54011841082b00200020780178901c0b0b50705507481a40c0141d801001c50804d20340c45130800003034501520300703052400c804d01440c040008645040300d42c15402405400c80c42504601e00003840d119035039124908000c0090500041d1074080280244007600c01c0f01801c02e0321303000301142c619020356070141100c0428003001c610135401842c9601d8058031211100c941d940380c101d49540c01c1c919211300c66900c0600b03000c82c55501d54098294181034600f101e18641d00c1d0704113065500c812140003540291030f1548413651454582115070412030180000c208191160300c001e072007501c207010035102a60701041c44010b02895000e581d005140c124203c104c5403c0c035401082d110000202020107000c02d8903201d00c0262182c100040040141554024043d040d0292040e2038000180c40c20200a052188813409031074054212010480300401c2c040ca068aa240400c405802240c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 411086223 1250 411084973 411084977
    0x40c1706032a221a030d0f030b0d1a0109050705040b07060e0a050d0c050613052a030307080403150b0a12020a0504090c0503060a0b010804030c053a03020c0606060a 72
    0x4662a1640e001c00c0400b400c0e0a01c000b80402c680204ca011a89010030804070703180b00b6400042044621a00050030160045007860702242c03007109400820704490343c00d00020810340c0d40100864000c2020003c10b4162554070300288072a465800f0121100c0c0501d000d1118a004100400341c0050215030020b0031600d500810b598402280f074079218200740071111624049a480a90f04041280034080c250740303d1484c090381c2c2150b4200e42c943e0380c0d40d0700007505500401c003121081405a0f0b00d005880001440d8014110390f900c0c1d8a506c0c1c40c02c202e4025110440d00e40c5600f60610113801c019018400c1d07a40006482e100c030151804500410b69030342540140c2e0042d603440300c00b04550300c580c012520158002c14903542454601401c1c10316200300280381e04001440d103807018060380c3c2d110080a030043c0d01032802c40c1071468a414100e0401d01c815009403181d202d282050500c20182032568040940d07807050244800c4801c1700281c0c1684900f64140c203107600240c0001e121480d00710090301d9145024 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 411087473 1250 411086223 411086239
    0x61503011a030405251503060b03011223100c1716031104030c05090105150702060f09030303040b0411031908030a021902030903100b09150609040c1706032a 69
    0x1e41c01040075000c12202d02030321400b5010180320304851b81c0346140e2040b400e440c003089000c0c502070021001c2c2c001800351891560554582c1401d000050700c2d03074510030411604503c04810a0728801c0d0365030340c14180340401a401c084001200b94000c022590468400f14404403250707558040c002e06403040c02c003080080c0741d61005030019150605010b00095403281d80c0340d2050700e040100704102001b0503802588119545c00e1414080101c940071b0301d0020b981034403199191649459030024500445c142945c0520000c8100b0040c00654100103000e10f0007651000990340c1c00505042d195244507140d402241200c0c0b008200082010300150360103d074984c40141800074000400c0c203903420310035250005900100307141107240340500240c40d5802c0e0107102080800e107500045080c41400501c92031281d038200751014210303100c50041341d05030000100100b0a8520f5080d000d8010f0a01d50451112089908000750245c2800120050703c09100348081043c000440080600b0030b00186a45800c0000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 411088723 1250 411087473 411087493
    0x40b07111c050d0e030a090b090a03020904060f0f0203061c1a0c030106090509070c0318031b170c0d020d0c050310050702060a060b0405012f06061503011a030405 71
    0x5400395200c040c0807503507101580d030b41c140700040081da6001c0d0b41540705604200b115030506500411000204d4030f00503c0340d0340f58540080010040b0f580c580c4060b41051565040208001d1941e01180122000a60810a400007d5401c1080340021a4826004078001c060070001c040c20600300402a40703d40c02c64226141d16807400d45040c0803c0e41c42c91390303d00001c001400b076150003a5240000e00001e036013181c02c502d00700d100101b10140c0c1d00310103010701c01420f070a0b800300c202011100703005d5a0001e1070a007013411140024925803010b4450600040794003a101d5111000200e080c61542000400d0b42c80740300c14540070031110319503890085900b0041c0360f400107000d4030240611003400d503607060300082d01d1504110107820554020044004607181640500002c07120b041038505484080c6005c1e2128210b00000c0c00800714000008040c0c81202181040003400c0050418410034050303581c0101c03581c0500220401c0d000c01e0003415004100d40d07011200e542c107600003566215005100312014030329 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 411089973 1250 411088723 411088753
    0x120102040906171507050d0e0c03010e0d1701030f0233040906060e03070b09010207030f0b0919080f07170a0810050a03030509040905010e120406090905040b0711 71
    0x1810740d01c810381c40d14203c044001c000900740440d04075981d50300d24104181c41c0449000b0114420765480b8002d0346d40d90417189511380c1040003170803480d484c0500200101421a80c150382c0e00c84081100200003041c140030200c014101500f105d0480e90b0000c50300031440030603400c0050240c082075400708059040b440e03513800d1140d141e0000d4505d02c2c0140329a55590705000050094418a4110b10b083c4075080907222429280014000d040f2a000d000e00c3c1d0300c032070700313480100c0c01c2241962010302003146640b501c40c1804000c801040c0904c03074400c00c0b1003c607285005600e0700e17114250009401041c05000c510150306558005220f081e00c90012400e04842c105e46041c0c0d20380013a4551030006285500300134000075401c038a0b502500c0c0c21203040085618680d0014032034404e00540d14000c1c2e403034441c0c1e58200803003500000b003120072003c250b450211041c130030b801300d0350494420308000611079440001c02e2086482954001c0d034201c10390013020f0b44c82d00411b0302c0303408509182c042c3c20300ca18960204100c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 411091223 1250 411089973 411089981
    0x7170112060e1605030705060c030a0309060b03030c0312090c0d1704030c03060c02071a0a0c020307050901060503101a0a0c020f060f07110613051003090c09021b1b1201020409 77
    0x1440546024107810300744018945040341a070000c42c0074503400c1010303811034017000041d80e03c0d20845190210302c070dc1300340c501040502070b5080c030700750588800b14103070142103000b101810003c50702c00819009070350381000c000d40d25006201d4568015070701c00098404225002604c101c2c01001d24001071800c0c0d42c80e079035040556411741c010f4515941e1040c2324800b0a034140502401001c0d1143c1010304503c042d0f204801030f1045804400c1800303400346243c0e00310b4130b09100c00401404010b0241019694408001d0321a40c803c42d03a6151150384403201150403048a88901c8442c6a0540b44600342512484140e500c41c02400b020307a80076402d141e024060b036503210010700d4003c01110782183c85001915150b0600d402040b4201d2040c8414081c01562000140704d1f1011071b18125071b1410505c01800c4142c000f004015006405005114004224a5156001825214514944d00c4640000c1110041d103440010050a4441d43e1088a000c4149404050003564090a0000520305982c81da0038204036 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 411092473 1250 411091223 411091243
    0x1504121719030e0705011d0f060c0604020a06020a0305040911070c06051c09080d05180601080601050a0b1206060a020f070e06011e0806100507121707170112060e 71
    0x41049892103800c1d00d07906019848107860f01c807000b0b000d4141001c0c0040c04460440c0005041c42c0381c1100701c0c403501d5a9840300340e541d009024100d503a85541c5003d059455a4017118283d014668010000909604c00164100803542558a144c105400d041850010380031440c40c030711040c00140002d0300421901d840354001403440e0b40b981592041c481d20f03608803080104082c42e06041c588119030b030100b0402c1c412154440001a800503085e9110600c9800300c1c10140d4424010348107040001c142c0c2000010440d0603102c00700e8808030b240e680c41d1761251552052040e038400020b00e43d80415050f040890251844c1111030050b28904128040f40c5860015940d01030b04480c880d074003e009165811842d84181014400900e081405a600005d042c524000d00a40c0c0a902da15481841451160054400f6107900500c80c8102d84180140106010b0081a0311080721070514041250716010719403488560030350001f0140d8980c80c0c0820b5000c1c0e2100c141068500944a40320780d01095420320180301e40c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 411093723 1250 411092473 411092497
    0xf0c090d12090f08120409111e07061b050a0c0c080a050c090c0403050303040308130602040b090f040c020a020f0604090c081005030a0b0402120109050601120204050615041217 77
    0x1100703140c521000800f0f2101d80c4542542d400035500000f402c04080100c41c10344102d04400301e0490426000e5011302c1c0b040708042c599010448003441d115101ba40010100302e070042e4014041c250200174040300002d0304d07018120100d10208103200d41107000e44840398946020304a850003440d071343d0300d215050a142c010107e07190740007110101d5083c0340c94002a43c10964003000641081d0840c1d03a01f90f600e100203030000e0140000c0c000040c021030080071070981e4180e4049015501c803030f5241c00b000c900d5084401850320803c4080d0b002c0b60542000d10481d004444694000d041c00c060f142c0030f00140d41c1d00102c2d05900b1250070000801c0504c25802000d80142e41a07031103103c1071078800000c0c58025925005544079401c6030480c274010420040c101074000e034040351410407900b98240814018142048010903d000340d0000055035046150704004842c000c0d541409207984103820440c403030026075110701d03d1b108140018080c4581ea81516848a032080e00c480520f00038140c01c0303034a207030050043c0380d030317 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 411094973 1250 411093723 411093737
    0x9140703030311120106110304051005030114090408030a1d16050117190e1e0106061121300a0608010e0d030b0609041505090c030f0c090d12 62
    0x81016414440ca000c26048100c90b513092402108403001440c1040c851102000140c0c14500c00c407040c1881220000d20000709081c10400c09260040c1968009114248490262401c000362a0a0442a1a101c0c40c0e001040515590710382000000806441d2034800418a140d400f03654001404c01075001c202d00010b5110351a68a07003000101007050701d4141000c04071900d8248542c1103001d658000104010700d002103401203620040341c2c6003128500c00d0060200380480413000000066000601f41c07000b550f54458111100141142c1e1640015201030b80b420100009900c200c9240002c2d10304c1d6054101c11890b603144140200d05c00380a0b2078081080c103000303e02800400c2c040d0b403058100611060000740310218050001d035450303440c0d01c40030205051311040000042c1d550203080390190b00000b00208400e4030350503003100760500540642405821044085943d145c10001603a00c246040501088640d070303401c24420040e04a2145036400c01010134031080010007448180c0711003000f698540c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 411096223 1250 411094973 411094979
    0x20c2a03010c050f09040b01140a08010609140913020a030c0b0903011505011d01090f140406050a0f0909050703020a0b070c0501082208040512100e06060105030a0b04091407 76
    0x9802c542c1c54140b000300303200b010440d07035125100700710617900f403c0b504550003c0c85400c103d0050711110100070384142e00900020b10200829000f000c0e0f141030b1203484d0b492139450f54a81c0c400e94007910ba6544150344c8a8131440001d400080030f0700c43c50407107501c043c0c0900305032950703691881c9a001e0142c0154200d000b0100b55010241000d200c1d4070061081403840902042c640b00002c0c10010035003940e00219811140100143e034000d40190000700480049a20b070340d03650300410030354611144820342c49142080000500c9280000030901a2220b100465008a02c2c3c440c0d14002812541c508803428081c800700003000d65610100750005080075801381c1d60391125860241002402c0350400d90610000c24107220340c82000d070200c0e030940c4034910b801c12848641810b000c4007074055a800f495000c01c41e5143d101c1c440c0b10103d08241309156119080c02a00b109032030f41901d444080f40c0039130000c0e0041c00000c62881c01074110b0b8420783d00240002030344d03002544817911410401e0b0b103031070540d9100745810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 411097473 1250 411096223 411096229
    0xc0d0b4912171501081816050306010f06050a0c0501061d010617040c051903020409050304171b0d0f060501170c120303070305100f030317010510090306020c2a 70
    0x200315400b44050742c1c1e078038a24001c000f40715030a101d0140d050420402c1400262040903a48581108244110407100c10b40b110191450ba80045400b03240d00901951000242c0055180d00050a07071701a91100c50030060b0300d240458000c40031400680f825900c588000400302401c10319141100d0b803051030340c81d07198180b4102a05400710b054455060210050400010410601d160b80903a94215003120350300c41d110003d0041807080d41c0003c2c0d44949801154009c008002009004482c00d03100c1c1000f201c00d44404460301d808000d400c1c00c07010039110b58803c0d09032909042504410b4414418018021896100c150480380c098010b01300d039a40c08440d180e0800d9042107000b6060030708503002c10004031050000c1d034881c0005058001032544a80100d107a42002034501000782c01c41014a006d001d41c0c9041c001c004010011440c04020304c4140042000e007070460345442101400c0d02c1c0c40e010a031440c1e944000070740c85000c810350140660815030124001c103141400009050704429034071640b00c0020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 411098723 1250 411097473 411097487
    0x903040f03150501080f060115031e0906050708040519061e05010504061a0412050a08070303020715050112260a120c0201140a050408040308030c0d0b4912 68
    0x40303c081940100f8541b5420300001645a0648499074001110341100300d07000e6016041084021607a01e0b0000c0e80c1803c0b03000158401c4041501580c004d01c020348032840d041c0d49018040e1030180c42c68200e41016608400c0c5130f0108040140320b040000b070300966581140002c0110310800c41ba81988400042040b032030300380a0013000c0c0905480740c0d520070454403401806403140744030380703c180710b4085110018803105001c0d604200780c2114185a4455151074010025400f000040340d0614490703203040c034104081d00c0f403d810b90741d040303100c00844070154980807240080706040450b0070856040099000464a000d001c168141d40c64280100740c03410481c1e415180c800301148116890101e019280f0b402d18041c60760016000c07800002e0750348881c10030844c14402e030380025160b84800418842d0907500080104141e0403005400c1000e5048541085a1140fa421288042c0d8040306d101440c44041141050440800c1c1e0b03803201246068110180b0710700220100a40b030358420002610080c5400c080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 411099973 1250 411098723 411098729
    0x30903121603080c1b0c12240a150b040f091b0503090f07080f060c120123040603030e0f101d0a0f0b13060c02030d080c070b0c090103140c0904050903040f03150501 72
    0x40940747c503103048025100201d2640c003690308230400a1000c40c0701d40f020f41c0e0208440e4503510541c41ca0130780c0c07a00c6008072598060710404603400058200000c605070345c0d03c5000f84109403150a4502200c11440864140d000607101c0c0402d4080c1004428050800f0001840200f802c2805041f0628841103454107003d4014040b02c1507800401c00c46d03c181e09a0424641910039000c1c08141d01c420070361000d410040100c0c1d0b15038200c0e20b03081c00030042c10703003021300b40c0c41c020b03011038421880c0440c090038000c85082600d40c0002185000c2003c160729000c0940500e0642405080748c900303140c2d80d43c944203107a00c0e50b0303210560195000821000c100f50300300280b005000c260601c0003030b09100703601195803440100c4940040029140c003240c5030050b1401101c07207264010000011a09021200207400c2c1d01c1600000c2c0441d1900000d40c40e46d265950420b84a010000300c1c45041252030014040900f100410049003400100000b141c2000300e04081c401030760080c48424a1000d580408100302c85042e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 411101223 1250 411099973 411100009
    0x1e060602151003030c1734021509060c100203090705031902010c08040503030d0e0c19030b060319030905011701080a3002030903121603080c1b0c 64
    0x10485100755003000c2e40c0840303505150290502500f41402c034011203440c107000b61240c8002074034401442d024280c41001c0c5410f40102c500d10741c4600d0350300c4ca040700c0900e0000d4000e0b50202c0401481d42d0340b00060044070320090304051a0428030034003541000030421072260130b16808014004844010403094003d042e06078010b02880e84101298031040c2d00e2100c00a0402c40d0180113032080100a5058400a1101070101d0340c44c1e40e0804090409005034001c0c00030b0902c14803010103810704e042c1c04001580c20424060b000b4241c10354031004c03500440108100e400d4400c481909121441d074220119009009a640c004c01c01c1c00c1a00042c5061202c0c0e440c00c407440c0340303440180800e02000c512502d89590210140b044814a96403619502100c8900e010822078101a0341d0f108079004401802268404c400b035440c0f100c3d29120b0002c2da8040c0c051b01c4400b02841d800540002809401403a412620000b03e00d410704030011044d2007510080142031500360016407050100e401c0040e0f004240da1500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 411102473 1250 411101223 411101263
    0x61d04110f060708070201090e04080d110a140c032b0c0e1807030b1020070305030a1809091202010e0d1e110607020718020a0c060902041e060602 64
    0x1090024400d40200b040103002c1d1301000400c00110381c0070f08842070040080003a0310704a86464148a0303210382000a09100d0300382000c001000304031501d001c45900d0000c03925401070003c046400d05500ba0440940038185110070080c04071b05004200600071004481041150104298842c100685800d10404000c3c00161810011160380702c10340010f41401c02000c810b01c3e5503810801310082e10285400030f40000381c4221500071a0740c0f002e144905d2002d001012808140309203e52075481e1641e100150060f081130041800c2c052003070050b85a4200c54400d881d46143c0c03141280821500014030132a2620100c0007048161358080c0548211090000040c0400e801a0080540513060b2070001c4032015540b2120002040e0150f540100c0c0c21020008540081ca0262406959040c0343d0065040c032144c100c01010070080c071030080f144044032660300c6488142550f50342d403000e400c1102d8100d80c09520390180194401090000e445140c04917503012640340d00e09200a800c00d80340c1118051b000f808 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 411103723 1250 411102473 411102499
    0x4022103030c0c0a0b0a0e0d0206100509041401110715050f0109050604020c01020d0c180609231003150603060e0412050702131b09180f061d0411 64
    0x1012065030b07400520301c00a140d58598a12907541003052005005100c14180b00c2800046006948a800028180411213054480700402665240380c1200c155170340341704c460400e00842c10301c2000907402a100b01e614441082050a0f51429980c10011580016101080030018000c5032808030380c2c020f59000d000c104c0e5040802e60400a40c2e014011050388a8513880454a1601ca540c1103810398070042e8021501d49580c49a0b401c045c0010031001000a4480d40020301c134141051740e4001100c40e0350726154401c80c43c0c4980800e1400c1c041510501000c1c1440d41c520b1207850b02014051088142d0b54005050080c040032140e01000923000b501c20989040005e102c0101c045091702e8009070041072002e40781c60710400c11103e42c81a40c4000750002d070086924000c1c0b41640c1c01080c1e5100e641007065031000e100c0340c01220081d440741300e0742d0a101d03d0722180d11f501190a5001c03010940d0000c0f40410f20940b516110944225620f40715420400c101c001c10003400003a0340b0415480f40101c45001c401e41c8 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 411104973 1250 411103723 411103789
    0x40c0e0607060903140703110705040209030a060506010905060f07030815010c0f050307020d0b18060402010e1002070503071d0105060c0d1d0a09060510030b0109170703080c01050402 80
    0x203041e2004001940c0d031102e101c10300d4050022010503002003078500ba6544403a02d40145481d1600c41c1c60a83c074413070704002003400e2401d4000c0d00d030340550141c001d1420720b2903a111000944809444941442030f0f200f0081810b8071200e00401242e40300301c40c400d646081600e00102a2040104482c00c4001000c0c1803800ca607a1056906119075002911510070004509045040d445036000082d4000e08905d0000b0420a0703d64400d4421002c100010b01035034000c502c090746511f01158020300082c2c50303503a10360741e0345071145e1403031101c04161040300e0110ba11800400d10707003ca541c1000442c102c00d00410705030600c81e100c0543c0940303002e8a00d00e04108070144030320380e42c0d10003801600c03e004030300301100704c1c4100355020300e403107004000c3c07074414800d0340c0d14001030080c801801098010b540c841c04044802e401380c011803007101810b0751a40c21301450301013a58440041d507503400321a8040c00e180007000c00e00d4080500300d103a0400000140506052040200021510109a048076003114134018060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 411106223 1250 411104973 411104977
    0x90408072306070507060204092313080702510405030d030e0f030d020a0e1e01110a0501050a0e0c0a0f09050a09060905010c031104050901030807021c0b0402040c0e06 73
    0x3c2203052880d110011898004042c0c080d80c4c0141c00c00070b00d481c0000d680c0c50a0601000b6038400f1010b0102555120100141210324514801411000c010440100141088c041030304501b070802060910b10b8103481195408070001c0344101c0f03403100742c129404503008a03152503e0f030b11081c030342c130300324a0145000d0210f0f4030350a090242009150340d0b4440402c8211084c0b02c81d400c16407110080c0c80d0f80388607403c41c04000303401503505200055a040b1580c1010304062410b002814929510030860380e030103200450700d05040d801009101d0150000d45000140c00340642801841d17015000719003000c0e0b05411900d401c036201c2200c0e10808107104204003030b1840300d25070001c6c1c860302d0001151660b10149a0406461860380081181e0310f4806040d090150643c090070040889075800d0012080e94010002c640c0030702c1c017450341d01040c5070380100000303040403008042403031002d40071600d4018442000341128032581030660350054103000304003c40c80c29104102004139a81031032003c0d0080f0f480410824 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 411107473 1250 411106223 411106231
    0x6030308131a13030e010306033c060603050f1501140612150a0902130b070f0506042303040e010b070f0b07050a09170a080d0b090408072306 62
    0x414203082007942445074012100c6140100c2c0040300c0502d080c640b0303402c0c0403484101d0b001d40004411206400284d031083c00b440d400c8940181d1012910503101ea500061064104106c00004074410182d00c0c0c59054003800e040355030300440707000843c1d42c03540c100b03d0304005424103140701c2900030600310742c3e14116048405040d81d01c4012501c5d145491000800d41c00c1c8545420660703045240700410050011150400d02c0e40c02080e940040025039840c1c2810076801903000104140d40086018050607000703c002e4082d00d40104000069002c40cde40b034090510310182c5040e18000785038000010244121820040111168401146024038201078040407140c180180fa07a50840000c1520500c51211240038207a6004040300c03c0606000f14080c0155000000e2500450744000c00011607113101d00b400d04000305440d0240c4011250b039520070b40c40b6404842c61481c1540e4403003600000d51500005244140e1144000d00d03034070700840c185030691b4422500000400300340c1c3d070356100003060080f0b421500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 411108723 1250 411107473 411107491
    0x11090a1a0906030f090c0f060307030c050702060d0204032d020105070305090a0806090d08091908131d2a090109030218010e070924110d0e1306030308 66
    0x49402125500985407003071841d620391000c0080140703e0041480f201c00c90085240c00c0031a80740d9a058018021030460305882e084d030010042c000142000d01030f40140700115240e00d80345107800305da5030001e48141c0040d010395107041da004ca0300323000f008207201c1daa20041c1800d0311408000020303035240030680490004000d04201000c10041b080501a00a03560b420800030a01180c494032801c056665000803205e00c04d99200d88a4110740d03003406401c0c0c00340140d09a0000e464000d60002c111000c0811214007240c901504010100c0c21600c4c0380c510700068800b102001b0754001d950100c001160001a05214052801100700048020302e0b103142c51711102988441e9498410560042c1c611141f10303440603411001d0480300031410500403c24a050b81c089a00103801031b00d80c2f40085800c01d000c0e0040125800580e18120034044620350070700070164483c58454494101c10305020708110010065038041098080c2401c1d0130b1501000504140060400c00c01200707256881c000c08208014021240e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 411109973 1250 411108723 411108749
    0x4050115170c190918060c0e0319030903050304060908010510060f0f110f0606040c0905152b050907050402030c0702010e180f0f0106020c060d05090f12040911090a 72
    0x30039490621140c0f4000c0131161410051200c034503110866000b0000000c0b5059442e04081580c014060301c09414580344c058005d0145080d640c2c441c5801ea800c0040c183e0602c40020400400a0b10420090010300320650302c2c2d040079407802c0c0c0c003a401e56802501d80b034845640c44405010b0b041d0b00c00c801c190004440d01d8408802c050409081d20714000ca6400388680c1d008900e94503850100028142e0300914003030340c00f0000d0b4a044401107885500c24003e896010b40044800b4001c1520740d00602050703e000f59507030b104404071a04560f26402e40312110011940c03600104040f41200b0700000000f0b050684040d0328501e4010808c0c0558494114020b05021605d28030152a40b50300004907260000003a011516082000c0c0000320781604644125003000c2440010646c2440425164600400513081c1802c0c40e003447da1388000340100808142e02441908061010078200f049520310114060308400c3c2d9031410200c01c1c0c81600c520501900c01c1480410154a03181c842e818070008541869611107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 411111223 1250 411109973 411109999
    0x903073201060b0901020c060304020303070b0a1401030303051501030c050f0a110a0515091605010509010e1503060a06030513020111070e070816020109120509150304050115170c 78
    0x260020400d0360303140e050740c0b8110780402c69410039001024149405d03001c950b803d17580c944c2001490b2004a41c001d40542042c05180001145081e006400c0360607291f01041d12900d039001c1542c12082640240c0000791100280840c4904480144061031400c1c681485811240440904113125500403041211310020700006c40d10704c10030b002d02c00b03d01c1c00c000b134078a850311900b061a5140920000c4068114000e00442d90801c8009020204078140e1080410740514080041d207586e005000c889050001003020b00b2155540c9000c02aa55982c12044a4407410501d040c082c003047c489d0040d009141c608400e02070324860b071a00c00098550b0920340714548210340c100302401c240c2a540b11507040724942c03080c8810150440e04480c401c03007100084546c4505400012801e960320514082c18205464036a0180c880c0b0501c001c0060202c05401c0c82e114000105840a00d40e00444040d116a55544800038030085500b05550003031803a00031481c5407034010011162504004540c40d8441d0300104080 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 411112473 1250 411111223 411111293
    0x912030a1e05042f0603040c050301152301140c07090c0201091707080f0a0816081501080907050d05060a0509070f09050405100504050102120a0213090902040b0d030c0b090307 77
    0xc4614130180445449003840c0c640081181100c2c05558400c0d400e11001c100d9542c0c0c03900e6242d040740c01504410008440001803a02050390140d0b6003410064083c1140c000c42000f40010403002d00c01c81c0040042a14001407102102d803001044821641005048000309a500f442d1074084400810304940d2001c8a113002104ca104680301e840c8114070115820b030400744c11001e150310981100c1d00018080503200707000c840003142111110440c01080c2c920f242103502c00c1401d40c1d4080c00701c00459034920b8071040000c07244060f0f48d8007104c42d41d000c0b40030001096110300801d40c220280740000e0141c6401c02e000500c07100d101e4000c160704140c0e160006001e02c0010010a18440d080100070482c900345800d00318081e510440e82c0d444000341c084046180c3c900036100300c40d20a5035620f849000c40c3c0c00d20316400050711403910260780c0180c5407107202e02680c2c1d07074442d0402440e11030349600ca074075042d6150441c200500244219296042441194041085080007650a8403d507242c0600c1d2079003401e51b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 411113723 1250 411112473 411112553
    0x7050c0705090924100605030403090909022101060306060f06021504210906031508030a0302070206120c040f0803120411120d0305011d0402030706080912030a1e0504 73
    0x54120051400d44da840c201120700c8142c0114121040030504d240c4a0906844922007510020001002010108803560155001c21f0009200416502c12080c844142e4a40314004010400660355110307010810420a48070b83c20052051094401c0300358075088002c1d40b10403c0000d00c80c000c0300c25500040402105c00d00c0500803414110c80f00d1448080d00da00100492140d00030034010034508219907400d00d06d4550240c0484200c20001d500d001e4400208034065005120304030f810a00610001c11614000000319206649010659807690318180c648500b0200603808400c07150820010032002c0d0900b400302341ea20540141a46409011100c08213500100020310003a00b401038a0070022011340c550070003070413100d1031405207002107200910f0310030913842514001d6050f03100e003204100140c050501e9a50000c1c4003006e17696040f14202101d4813540c811036030307110700c0ca95030707400d00403841c802c1d107000f0b40c43c03040c180400c2240345040c1d51000761440144420101d00844207032034054044844403 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 411114973 1250 411113723 411113743
    0x6050c0d0c05030402010f0203030412111f0912170105061309020c0f0f1207120315080f10090f0b0a0b04020a090302030705090c040b16080a0e03010507050c07050909 73
    0x30041c500c1180710007042a0000d44080f80015558066500c41174800800d4a000315003245400c540603d0903402503d08000440c26464540a061500c400d0000c3d0080c008c00581108100450581ca480c41c0c50200b44140b5650581400f1420902800e60600c2c3c617486410348100b580d1842d540c1c81c10204071640c1500d507900c00606103000140049a405001c038280d00f4070300c0210115441c0391100c460154491084505541c4000428072611001c00c0f680400219510b83e41e04001505c0901c50740503442c4a1110b1f040101301d81d103c1082229140e10821001580700398102c07040040c00110341c0e40c06191304440030050000c000c00c4e400304500c100107500c540407034000100119610b922041010b0034424162005130b109010b140000501c0342405008540301d4000d0120503403a150918911080e0303900050f41a0080325402a02200014100b40081c100314866803111204804081f04140c29100010300c41b10800205100400039a0310005610050b6402224640300d2aa2201d681c6450454240b03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 411116223 1250 411114973 411114997
    0x3070c080f21010e0603031c02070506280c0f03020a110303011d0105031c0513030203060106270b19170103060903080f06010801030209090f010f1508010b060706050c 73
    0x240707030800c1c85203404640040d4140125520b03042c0c1e600e010640e19040c0864540b074050300104400e60014806100040400c50030300c0300181007141680b100d41c0b5001003160142205c2c0a0400f804000c9056840790709520b988990003880401c0324803c0041100407024604000d0607008a14041010700074802e26075868001400c032034803587d45020306000094020207002c0c2c07000c0c10f2000030600e42004580485c090841880d00345a00c14480c004440c01e41c840c03140c07911a43d808910110045c4c4d0300388240c81c02051645c2e04c00300841d02007103488080c2402841c44c5180350660300760070000702800a080d140000822404001c44160200007500e1600c50380c0400101d41484100100801840d5030100c102c050107030b61041a6559402d240402504043d81c2942c080382043d03004000518050140c207178054020002d1f20307001084000c0403400d44072290344070710348940c0b21403100942d01d0790701c44000010b007103920091111047d080040343c4503229000c3c001c1c116945072000a2050240e07030040b181040280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 411117473 1250 411116223 411116227
    0x60304061b0806131401062003070f02040507030504050a2607050f0d09060806151908311e020d060f05010f08030d1a0a06170108010e0303070c080f 65
    0x401005100030001c80383c4070b04ca00e1001d10310104001d900e01c50030220b0418105004842c1e400d01500b610000c145d50a02e01c03007940032403080c0700c00f504284054102940724000b4426a038883e80704000a58038000e1124007010b24210030040030030400228220503a400084407650f0341314210784c2c42c040d00003a082070a05040c0005070481044000224012450038040c1900e00607641e155085075810010b12902d40000e04440102c0c00c9482c0041c80101d9144602a44520f84550040008900901140450081807100c2c013002421968035050f00101103030034440c2000d034902840f0041642d54680c1015220000d41200e40c54455108074107250f54980040c40c01240340420703e405006050b4068280800c1400c10000003002041c14085506845104000d1814000c401c0407038001400040b5000c42c801d40c110364460225110042154080c04003070703450a60b80c11901c80076203217145060348170007202da140850040b281000813090301d07000201441c11120f18101420301e1611b60042d00c1540128200c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 411118723 1250 411117473 411117521
    0x7120b0a03050f0f0106051302090102032a07060206070f03020306210d0f03060f120516090603060b060c032b020307080105030d030b061602060f0f1e07030c0206030406 74
    0x1c0c9180c11202030804c40b407550b00441e10580c2621b006200790703900400c10422110f80c050460300600f1003110188101c07402c101258010340603c0c2c2d05807803030326294800404040d071011000c0c03015101a00721030004280c6810004001084a0302c01e050300c4080580c0800481d40d1540c2d50440007009140c0500d9a9120701c0045e524280c48071108603840c004240c0100510f50403c2c0680550070456228040d80202c091a0030015440c0404410040790107000e800c1c0c1006140c410070031a40043c00071030000003115170442ca840022a0000542c2d184118814403150880020001c12a00022650142d9498044030700c6103581001060740c178400005400401005140359000d07070100d0403036104808031141f03545811420327404c4a03040107126030040d40801c84892003403040d0b0314510980d80b01409491410b600c0c010b00c452250847d04111604000006800307a40302d000031104a15900080402403411003503a4016150006c2c00100900646000c0009028849554002c2c220f50860040a00071408 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 411119973 1250 411118723 411118733
    0xc14040902060d0e06010e070c020d060e010509010e0d0306030b0c0702030708060a0b1806130c0507050708010b0901051c111f0903022418060c07030308010501090509040b07120b0a03 80
    0x30002c13104082c0e4840c92000148604021a855000b90354513166140340c5440368007444000408107505560303680e200d03184c58000d00320911403948126501400016512040342d0540d083c541644001000c140c24280c1c10710105215180c56500240140341b11550750010307101003410602d040c1d012205a0290070100248500740f0f8020700107018044889892000202440200205c0142c50154014400d0b0000d1940b52515030b02c2440d0f121200c2c20050b090404a5490529140d00c2c1e400141070b81c0d4560314803003140c0c02d05045007405004125101c6000c0002c00c1010483e907102403001030007018404000300c825440d1440005082005000d0400d00d0048450014080740d44e6484100e01540d00c1c0004100c40818004080d02c14240712180c044c82c15280d428000142c603440c0c0440c43d4070100c2004080b0081d882040201d0055209072210b0f910380d8035010000d01140c0d400e9101c0790242580e601040001071a132803045030300c45400d0a003051a04051400c2000505035509000d40210b0100c6000c0300f403003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 411121223 1250 411119973 411119981
    0x90406050108061b03060d051603030207080111041d130602180f0603070c020415050910080d02010204030305221a0702040e011a0d0303020c1902100305040c14040902060d 75
    0x24500c0c2c02107a0090701d9448850922030384ca0500c00c0c04041007400420a58038042c0103600129011748103c58074002c0e506140807844106038400c8015900520f01007109810a0080041501c480100789050a1801c91401c0009071902d2065000804010026a4003548000507464540c1c0081d0210b4503601440a19046074840d02911449455559031800f44c924140c801c85c2d200e01282d0340d5008078002c01c0d50920029085031041c034090805940c4000c1410f8031030b00c070083e1003900d8071b041014146141c06032207800d040c1c40103110310869004000a00120390000200c5410350310700c030440702010001c2d1400300f461540d02e800407034050010203036640c21030924030098605c0318001c5038204061070070000c1082c22034000c50480032008841454003851850314192103810b0a010b4180580f60024200440c0d0401c00407040008941000d8200c450640c01e140d07a030a004280c2f107003802c01841c1066101e000440384184510710a44058084c900c2641d00d9603040b00f0041580607220726203030700145c814003000d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 411122473 1250 411121223 411121229
    0x51b06070c021c20040902090703020a110a1a09100c03061401050c07030305090102150709060e012309030a020405010315230106050d14070801081b0105030a0f0b0904060501 76
    0x64440c1c801400b83d0092440b5410f140d1550010201600c204038880c00c480109581c50741503803250f135480b00007015844400b02c8602c0365115584c0140d42d1510b00758050300140041460300d203942d110f0034120340051106600c8450000d05c03081c0c2c1155035980c2d030f40000e00d41f405080614010b2800d121000042940540004007546c02840c500b5100700c46030001100c10b400b0340c010003000f69101031020400b1074050002005030308010301c1524030a010450314040d0010b400d4400b103001840c4684100015903000400e44601ea82c2481d06415494501e024802a40c4030484401e80004000030b5040c01a54200102e600139680900280107641c1d50782446580e400c8211a2030f0401070074012650501c4c1e440700030001148860200000c501c4c0d007400d2044900303030401c494012a40c2c0e0b072114412200050002da6501c140e445c0d9540440c2e0358184010705040005000c22000c40701d5041a0035110b50303030010b042e41e60200381c10000007558010490381c0005480c0074030340b8079080700c0300100380801d006654002c01e0603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 411123723 1250 411122473 411122479
    0x1d042d140a1709030304050402130e0c07030306051c0b07020c030a080301180905070306090804170102091002011b0c08070c06080a200d2f07031b0c06051b06070c02 72
    0x60162401a502d000d03c108484a549600108014499481d04d9030180005915a82d403c080c02501c0350034022043c142600c82c4102d652020034800201a4140561000741c1400d844100176503e44041d2a4818014008000d14021040c800100c800b4802c002107250418001c089502e081da55003800d03903180e8030038040c10786003407051a2000050603040c001c3c100d06a0f807010042200030300e55241c00008203860001150003c0080000141c1011b02c0d091b080c2500c03401c03000060f5108601c004000c1c3c0d407202465880156410902500c3e24802101c010700850000e41c2030044403d1061300c1d00304074074491018000c204942184000c02c0741540225010701c286a47d03030042000302040400c000c61590b0070035000c046207104110340e02c0d030705a040c0c21104d044840701804502c022000002ca00310b03608203118040000802140701c1c0306050703001d072410721001d4000c464610610303403a84400c4030065440c0541c0090110008460380c8008941c48841482044841510540d08211030000e10700030340e103402644 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 411124973 1250 411123723 411123743
    0x120102031006182405070602040f0e070801031e0609050607210207120509010c05060f071403010503070324060303020a0212030c060a0f02120f011d042d140a 69
    0x14030082c0d84514600796180c00c0518142441c4a03410342001c10b04c5259102c0c00c105060003541c00007207160010304042c0008100d03165110b410702005031580c51000340300400b0421108010070120300404242c0551002040c280d004c403070018200078000e403008000003807040c4181810005940e2b40241d51078141262400d011a0348030909581000382d001c2c40a01a003003081d40081450414001e01c0101041e00381810503c290030321a0300c0c0c050800b91308486000c81c03601118104605950f01c0070444d808404038403445421541030401007503540b1402d0000030b090030035240407800380403005848007000c4501240140715541c0c59141c002d440d9003e040c0c08034026110005d20901c001e5000c400d54402e20507000003806180c0e95000d59102078030f4442e0280101d50380c01c00c22945055038510740f851180940c0c8624001952510704110b0205800e100e1440440704110144800207000100100811110300311aa036203401521344800392003915100105034443c0d131184041c001c50081161200e280c01000b00c89 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 411126223 1250 411124973 411124997
    0x90f030f021503070e01200a0507050301060501180302040c030b0a120b37150b041e0636030f0302010e0706020309042a02030c01060510120b120102031006 68
    0xb9032940425250303600480c00d14081c0e01d4803540702d01c013040ca030002426031685a000d140c80b20700d030500181d4602a101500174071800c1c4003a041c00d0140c44010700b400c3c80c0070302410312810710030200c4c08018007000b8811625845a090424840e0b0440100e0610003001e034404141d859203a109104450a000c44880d440714001a0000b02444400d503180c26841d041401f000c1c00d00712880c1c400540140c50704034807c6c0e9400204100540c41490400a44003144203075a0344d90400d505030030004112040701550355a4100284410b07540700625075000f20b40d842000b070520321641407040c04081982d4880140c181034801c00002d20500e04042107070a4041d80003003210781c5069040545401c1c9034042c800142c3e00420190040d41000d5004007112a080d40fa03000081002d4072014141201070100f00c00180e1000c00e002001e90700a104190003070208403103862003100c01c0000600a606400f0320a80310940e100350307808050312810003586680030b01000071982e0f450f040426001032013141c05901c0000b10400c82c51 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 411127473 1250 411126223 411126259
    0xf030705070504090b070f02010f050a060e100311010c150203131e0507170c0d0b01030314120a0903050913240b0f1b030d050a1802010c0201050307090f030f02 70
    0x4d9a00b250041d00c880d250399111041681c04000f00030f04c2604565880c0c205980c0c1340007620580d40074080455007c501c02d450404504842c51016040f01c5010000c843c00f00001184010811079216081c2851010203411341007a60141c5a444142e26285000000704030100051040000d40544a69600017400340c41c90403032003235800e407550010f00c1507002000c00d00546241c0700103110f01a103004116884a50050f022030b4042150a82c201d4960b521000140300b05030b00480a002c0c8441000401c0e4140b903901ca100c10441300b400b404a081042c2c1d1101c44070103051045084481c5504013801079071100650341d028400410382c03100c2024030048015481403150b00c0c0346080c40d00711043d1443c142d01340707070146545e113207151303c1509240800100341d0000800b07880c040c070107003185002d420b00c0007500d454071075804401e940000c480c4902546200480a0050382c2240c900031500c1c2d02883c1854070303659009416112030780315400070141c42091440020403c4100542001640d100780d0b0542e480311110088 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 411128723 1250 411127473 411127481
    0x12020115090c0f050d060b120f070c0302060403050f1902060402040609062d1505030901050a0908032403010e010b13061809020109050d080306010e01090503030d1503050f030705070504 81
    0xa044002502203d00e000e110740304001420822a03001c100082c4266124180314003640503180a10301c0a640c0010000d0b840f800301000c80d80002c290909454460150350b0003502d407007008000406200d0040390850500300300e00207071502c0c00c411181880040d03100c035001a540d000e040318124460350520b00045030101d483d0141070f04a560f5083c040c0e21900b034030035000440207001c01401d120540311520001e0a07a04e2013800a08181107604c409036039041c0310703000d1400e4030401007680d0442401d0144201c00104040200d076480b9001c2001707800d03225198403e2000d40145581e0f020341c5503003000c54040c41044190700c180c0000000b1119140420b11040465041c1c441d00e20a4a1050950641452002c010b64000b0103400d0310516050a015448200080c001c4009417026240c1c000080100010742d40c102600c03070b403000d50900b854414a46442c000030f59072320690380014212a100c510f400c20b0004080491000385038800c013540d03100844208080d589401080080d40d0328429440e0015080c01c0c1072103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 411129973 1250 411128723 411128741
    0x30b03060108031801140d09031d04060302010903030e0f1f03061409160e06040303080108010b180c09120319140f0706050402011b05070602010c1121071202011509 72
    0x800104d403908001d0054071481d8000a00007840c010401107100260458461580600e120361240a01e400490aa550b51401540b100d1402103141039418000b507a00440040100c03039044c5091102d40302902c2c0801c034041044060103400c181601e120001d80340300182080c82c6100e0b01c5e5010050340760303100298a00003e1031102d6030f401400c140041811200c0c60424442e80e81c1031414501d130100b143ca008030340b156000e94410b40c00580f6a00050001001c00e02070354401c0c140440d041c0f1001e280c4156a080840d101070441051a240080c000780c07203454418a0700c00191004003900d498a251480302e400c1c15000c4041200042d2480c0d08e420b83c0001c00b10107031011100f0105166090100c00d50391f10000f4030000e0400e034144407032482201ca01d43e010b441101c40c49071042000d02200d80ca8104c0283c02d4a04c0d502d8110240003160f00c01110001e80002c403141c6180d21900701410001c03003203040040c980304003000500398003038a00e8007880081d0150064010410b401c2864024980d8a10001c0201e5103810 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 411131223 1250 411129973 411129997
    0x7030b010506031003050f0a0c0503030a0f031808042402060f0a0f0b1908010c020304050f0d02010e180f2203080907050a03060f0c0302160f0303140106030b0306010803 74
    0x1801406981010400b031540402149508001181c4a4440500d481d50320000441e10398886c080301000c000b0940d03070040042405038011410590641000b4161900c4a41d4120406507181c40740d80443d10f82011b0840701903008000e4641d9540c480310311900d545042c02d040801180c030124900340c0c5034030000310a441200000c0940300c0d01c0e00d8001044000e003001e40200400f04e40c031a4020101c69950300021800080d607640a1880d40d07280140135800d40344145c08030380c15500144420406500c80031542c240b80b142c101c4a2001c0840507100503100601c03c0d4100c150081950800100308a41114846014002d545c0d04141c0c11703135421601e40800081c5d8501c6003000e0301042801d0002a015140ea9a04000100240d03800e2680b103c01052884100b42e0080c0d880c0703a04c0c0c803e401500c09403880341d105140301515040d407800f0001a500c002c1101142001482d0b050b44415000c28107101c0e40c0300c4d90316078107107001d00081941d503150020040c09002e08428400e0041000003c0e65003c000102c506264100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 411132473 1250 411131223 411131243
    0x7092f0f03181c050306030715210f02040e01031a130b070c02100203070b13030c0b0a020702090a0b01020f0a02101b06050106020d020601080c09010b0a0e030105040b07110703 77
    0xc40d8010440062124407540c40d108a2034400d40d02e03101030b1460b03208616240e13903080d01c1345072000425190140170350207030048070155452807040503400b62000c04109052580540280d0f2203498680c000e10070070020345c0070144086004245001c400f00ca2038121390051009140640c0e01d00a1742880c90400d9801c1c5001603c181c010350300142c1d18940c100d502c080c550405482981594020420a085050bca2001604002100020081d5090140b5000313031000c0d40c504d1000c0403590b4041c000081001c0c015150880000c00251079410030f404540c40319902800f00c46860030440080b030080c0c84101c41043c090300804403207540c6841c0000e08644038580040ca07006941c1d0700d441040c5c81c80c19590b003501090f00d00540480020810500840380202860b500910848000c110028241070068010b040c15030000a00102280da91010007410765884110069440030203800546540d00d0640c1d00035050750a1004000a000e00b01c4160b0744140f0207916003410025800b00b40d0342d02e0f5207060200400c0c250706 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 411133723 1250 411132473 411132481
    0x102100c081302030a0b0403020d0f0c082b0213050406050618190504020c060402010807050a12050c0c1603020102070911040b090114040f050312190e0307092f0f03 72
    0xe2101150b4200d0015040e41e01501300c81d102c031441c0c0c2804441c00d5015a204403c40074443e5880036045440002c60728010844d0085039032444102c1c4a103049005503840c24001c03500c0024030b150115201c010720840210341e140b802c0c00e8070310003031116480b03421f1103580307400800503607400d003942200c00465031203555006c001c1002c41041584145105070400c002451200450943c03103900c011700300100054000d1070f41c0e02c1c1c184001000124010108002c1103400d0140d100003680100081e0a01c01c98041b0208003036a4610401c081c5028405e1103018911030152140c01080700c01d0750346010389000b81d00f07440c2415150032064050b5008030381580d01161003000108094200c09010300186401450144003400c0650b00310202c90300107401c00c05400c40440010459890100968100b802d2000c20722424262007100207422100311440d404244903c2c0703440d01001c3c0e03070300b4080440603104902041110184840303041070035490b10501030000494a00034540c0d0b03c0030340003d680031000c1590341d10380b55a40e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 411134973 1250 411133723 411133741
    0x6020d0201110a1e0e13060510030c1205070e09190506030c13020309030904152102010f030b1305070f080a14010330080406050a060503120a020312150102100c08 71
    0x18136808841e0070400c02c41d1000317107070b070f510401b40e000019664500030a005080800f0040d2880c02c0b0340d440814940781040b1300311840d81104445202d055480800542aa10490b003540ca04502814140e03012006a0400c4404100d943c600c5c03800f2204144d00b04115030307808040c03554480045010941c0171307901c0080c1c07000c420141c0e0000d55109110398181d0b41413003803041c04941034030303683c07025510509000802071040001e034409845e481818544241095801034001900780588003980408050700c4e40302c01003a54a40c2a840040d00302a4003080000c1d00d405100281040b447c0c03402c03400042c2e0610007086200c1003034001c1c170842c0011001d0320a403a03440e42d5902c0004801e104d04e0340b005613510078000000007d0080d42c140c1c0814840d1a403803d149028508a401c40f10010020098a40703080c03800d0005890001d41d040c92080005070003a510f0603a035070180c0c614002d02140010080c400d40800081d0f02000b00ca15081d100286c00b00d0300c6400c01e410b42d08040d13402c0c21210350b00060340000005d010b54 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 411136223 1250 411134973 411135017
    0x7090207140604050a170315090a1b120c0e09180f030d060608010501111e0c0d1b120b0f0703061203020c0109171f06050a06020d0201110a 61
    0xe0301c111280700000518406060808070708940a44594202d03020346400d125803110150713100e0010b00d480b58614544516082c91030070400b0301701405403400c0c01c0092145c843d15405a004c010f42c14005200310306803198014000305451882200107428800603103c41c9016183c02c15203001d00400c80710307940e65121421011000c020315809030512484030b00c00c030900001c1c4000d0584203842e90001c10b1090403d40040d00034841a801503042106d0194590940400829003040424401d41d902c035501004051180c80c08542c0d1809540c8900400011400c00a04089901c266110340030754440700303070355041001c02c80c80708a10040c20356808500011050340701070102d194011000c0c10006030943c0c4074041141e0b4409452411409607100a0302035070990307003008000d070081070390314480f072200c41c580e40d0069116502a003c800c8450b80154200d080b0704440d40009001c0c1001a0401000aa50b0180203564030010f440b9000994a42102009152014011110130711400d88071518141542ca901c188a1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 411137473 1250 411136223 411136237
    0x411040603020924060903100c270305010b0409050312101203050d15051503040804080109050601140a03020109030201081b0d0e250308030c0906040e091e070902 71
    0x8660303591000700050352600031280c0213850f84115095030303040c0756103003810011070114814816041408208410386c0e0020340480211112007001c1019100420709991700551854890040340c6410b80b0103400352004181041106e00036002400840400401c0c80121130b50b0a502512942080110f407401103500b1290540005c4546140c00c8890b540d61000700301d01d01081011800039a00090f040c2914040d401400d00e000c3c000031440301041d142500148004c1141c8a8010504c0300200c0010148003078801603034020318403480248507814051030055203600c405d00035000601540c0300703804500d0400a00480640fa81030312400714060031500156401300000780f0f51611801000d948004244489000c3c120100c02607c0204031840c0010310141071020005482e109113000320a1005094004203015041b250454a0640e81e601d590b00c903030400b840707480e05941d0400d000040c0014040075030021103120f00b040c001035030320010f00005920401450ba251207100c0c0e52041c40b05002c20019a0b00038080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 411138723 1250 411137473 411137479
    0xf050109290f0c010509060609190902150301080d09030809130b0a081e0a05030909040305070501060e040605091614010302040e011502120f070609021302130320090411 74
    0x240c4818007031041810750000d0380621065101140101d0240700901585404c0591400646080d241c0000480e80300e000060410080d902e5030036124200d203411f60300a4030140e4004d400c1d640400c442c9100411103038028499a4460f214441c000042c0d14842c604044c1600c1c0c1c4030b248245409421802c00c12030744080160800100c0d61031034808a070703a5599a043c40200381040c050800205802a0400c40d0100740e191a81990003034584140014004421260501401c5420a08075103460030200c41c0c45c02441e01c001e24943c170f0680c000c030300c1b8a41c2c01200c03071180348500c3c000d000584d59281c2440e25040f03840e000d8141e40c1101e25040c042400c00d4100c0002c140b40600d001400c0c15038485410040369000c2e03004103220303841d00b054060314540c14080c14094649415100d441e10a569589030a6407140315801f61400780e542400504643c1d41d1409203080481032101036440f00303410141c5039900303500c5100498150411408141c403004861060b50917001004001c8a07280d503854076014411080c5410042d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 411139973 1250 411138723 411138779
    0x50601151d01201617030316051201090203190903020c220617010b0f100806040212010602060610020607020d0c1401020307110712020f010f02100f0f060f050109 71
    0x1842c0d160883d0070084028881004098104031104161031200d400d400c0a40c41d103110a5010151181c00011641c1000f1000348107400200c00301003c03030709406030542e01c1c080482030000014031001c0c82c0d0003440c024490110404101e000140d2814103d0700c41c090010007580003581d0003146841e01048000108000000c41001c1082005041e01240c0745500403540d642ca8056040e03054840912030230984401c00e48640707000075403c10000d00b581583d14800800c028140e00000c1c007507182c41d01030b00e1400821b951201d50950712075078040e445c0c510407036100b07020342580084d00c2d40c0c180c80004d002e8010106a009000041005c51084035104c3c0e0038041580e0500c001c148074803200c542480250710a4016a40780b0104007240c0441c2c078100142c941c042c8040a20b0038849030003581d140c854000780b031042401c0000301c3c003218110030b0781401c1c20145c0c50f4040610f040c41200b81040070350008828030505d01c600304225921903440b070307441d501280100390005000100a04c07014050a144103d048500b000f654 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 411141223 1250 411139973 411139997
    0x302040c0908160506090d06090b0411030d0206011a0705030c0304060f120506010e0402031306051f0e01150c0c0e0a0212010806062211070602030103050601151d01 72
    0x2010390303112445400c0060340c020810030000c0c900f4060480c0c0100301c4003030724100d80d1800c000600d46009092686228480c204840030810901d03500218080740d0001030a5024502401c11100ca00c1a10310300c1c80c000d0007055245142244049030850580b07107131b9152000400d06504513400160002041125184020400b036081540200080c1000340103540e200201c1c09a4000028000c089082d031700071580d410300c1d09001490b80c0083c4041d003440c40c01d5500503100c1c0d80319411040c0c0d64404403000782c00d440c034200500450b8940500c03009459003845904101d6580d40360b00c62280c1c02c03024411881544c2c18100051582d034805c1080740302e51800389040c1c3c0d20b000d4039050308188401055a124060301c1c0e0000703004202120400c8100d0041007407a019040f94030b801000304524400382c00680008188100603c074180c10300390f210004090824510946410b15480c104001350710170702065419101c0c5100004110480c04041110100c8035500c42034a408000000003400c6141c1d4100317814803802d11500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 411142473 1250 411141223 411141229
    0x509040e01020406022a0d0c0302041409010b03030c060112030504080d02030c070603020705031b01060b0417150105030a031d090c1b06070c0f02060c01020f0a110316030e03070302 79
    0xc104002a03400042c3e440b4a801400307031030f10130018a40c4a01420b8400342020782a50700d4080f8580f80b10665161030307200c0f500d242c11041210030742c00082d0f0103407030581d981004103203c400b018400c01010008001303001ca07520425640e80240f00c20500c0c503501840040c0f01c90340640b40707850f40084c0700742840350920303480d440c41c0d41c2080789111038040164001f06601100040c00c10010340100741c00e080852401d80e158aa2640702e100302c411503c1c0511181000c070703c4c0341500b580440c1c024207241103840e0b00d690301c1d4001450805509504204940700c0d500d20400880e85e4070603854126030300100100084011980c080d04d2040e1020150078550b0b50f9008510764540710540202d106054800c04e440c0d41e0541110084032038103d040300c0c580c1952110040005540d000301d4031600640c0c01406151041401d48000b0340284210444c0d850903500109803a01561005405030024501988441e41a00800607100303640780180c201c03900b41d03c2034451150002c41d000302101c820aa8018003650407507a166004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 411143723 1250 411142473 411142481
    0x5070204020c190b0a020f040b0307021f0f0e0316030c0807171c05010e130609020a061106070e0d0303180f1b08071203052104050c130b1e01050904 65
    0x804040f48500c8940010004d100d500240d014440c0d0348118201300562000c1000f40c0224010055400800000700319558000c000000220f031031103947c10b1181c06a100c1d048040c1480070794010016040001c4244040313001310640760a04c0048441c0580d07030b041502c0846029200a0054500110812210780807a2020006000100001c0c010598030b0b0b120040c01d401400d204241c040ba00c500d4240140181e9281124407900b16280800c01d01d21000141040300042400e40c0009502a403681000982243c01610650002c0440e0041d50529950440c058800300c4428002d1f0b03074001034134420680003900030381c00b448a0501440380300c0c036190115035541455201c41030090381c0c0041e4007241026020fa080e03c070a4080c040b0703039015080583c606000105140180b079401414400301040c540d99407402000270b42c07804030981441d07449078281400c101d61500401d0f1030250042c195608112015000d034001c5506030903019003030052850f41103050006450102c030b480c1e4104041046403441070740d00d03401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 411144973 1250 411143723 411143743
    0x1104030506010b1b010212060f03030c03220f0f030201050f0903010f090203010e0c330d06030c0b07030509370f080609150c0f04060e0103050708150105070204020c 72
    0x606a4481080202e00c1d400c0c4902e13010a98103070700402201511b84842003a00c0e410032401e0364041c0b243c1000c007000a040d80901003403100e40d440045003440d0030005a21001000441c08080c0482483d1500c00d0b011750030781c5a0082d941d0303514000c8002c2005500c903100030038903d0086802c3d43d0804076000b0000e825035203c0134401d009292034808040a6180178840e41382c901c07103030b480141803403001800481c3c1c3c1c0e01110840340d1081c0c10140310b80840040c8030320130040640d58103c2859551081400c00d0002891140000d480c42c000c00800820b003000003004803030000e509034030740f00e081c15510800c0203010040c0d01d400444070003199004a4802c03040072203405da5401204e8900c00c18600700101805202c9499012054139403108061185030310000c103102282501c85424054640d84801e619811441245035040310b8813000900010a140e01128140048000341e074148490748407201c0407280f10f5001c0c2ea426080050040b4048040c2d1f00500061144500c00313080076041054030440b540c00d001c20300b1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 411146223 1250 411144973 411144989
    0x12050913090f0c0902161118040803100b0901200106030b013807022103030106030204140d1509390e0906180f0f0c1003021903110403050601 62
    0x92891040007800c4000b030f005011141011418403105404020241e400040e003c1c19100f00310040906a4844d1b640c0c1022902e401c403a4907400b4109481c0880d910303881124040801000d40c100410242c201e0822140544030507500ca1000c146d21400100c031440e0440120340d603a6503603020020000780710440f00b43c0240000b500e40d00e0300841405200711504001c0008602c901c0b001a080c00700000c8640a0b120550b030151000c000310307024811584213140242d10814941c3c03201200000d03074664160010410b0321031a41c032403843d000140040c460900c80604005041c4194281000d68030301d460790011500358084d400078440051b0410105052603544200050741c00c4003001015403400c52007150400928010340340c1442403602c01030342919040050281c0003480c504200502601c001046072440d44075020701030b00e0484900d002c041d9a00d141089095004620000d07601680900030f00c29950002c1c400c86d01980c4c2c031012110100e005005003880e5030701229042c00301102040080100e1400b80a010b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 411147473 1250 411146223 411146243
    0x170f151807091b09050904030c020312030c0307350a0b0a1706011a040302100c0209340c2d03021515130b01031d070f0801091205091309 60
    0x10038903004040310101c1c0d0120504c01c0d404000c0089445443d03500f41c1c010381524080310110820310000b03041c540429140070070f58901005101000e0b00e0701000b54014a071039100e00540c01d800b03841e4080304000c0180c0b5444100d8240c1c0342030b28a10601174646078027420031480000c060707461400240340805650407084035865100c02c0c1180550b020425107004d45281d4050300c9110f02c40f001100304a20884c00700034007440441804440050058030160f6030769074014048450380c5407051a8065041e2190304500044d480c007036420041c0c08910040a241480c507070345003148d1400a80396085000b4008400a620814000c4d51300b0006d652020400300c203912070340c0540400040d000f8924005c1a01810a0444400070300c1907511304c0d55030f04060140c139401410302040081b907403c010307401821412440d0407110f004800c80c034604a408038a90040d02c40f540350b80d420309600e0f502030030300f200d580002c0102441740e140c1100714894014006020015401000c28403c01c8942d03804406035001c80c07104681c0c820740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 411148723 1250 411147473 411147491
    0x180b070b070521010512060610112121090d030e0703320102030c0703030c02150109020904050a0c0801260a060e19030e010c03050403021801170f15180709 68
    0x3c02401b12114542c540c000f40300c00d06280000132400300d0f03881024801d11207041c510038035400007445420400080070b0512101c4640305400d41e141603009020080c91310035503144031040031580c8014030b0702544110004040c0b11803480e10a034002c000c40c4900c1c000b07d1249840000000d003000b0450142013800e803480c244140c10280e41c0b107180300744010040f01035134014002c1103010403c01054406003030305407802244200b00210b00340c0c18500b0004001400d525404000316500440c0e4000b86407692044d64108803550301e00c042901114583c020f8000042d4000c0010071003401407030800c5020b51010740c030840100301d800b41c10500c0c1c00036001048801c0303074907000040d401090a10528036100462011400c0440c61903400404100498101c00d043c03100c0c40c0460810305104ac0c0030303107001c0d40d405055810f001c43c1030800d1484204092242900840603402003409070803003c541c07100c014202c3c80007090107110b8840303030380244140200003100e42d041e449200101e0701020418038004042c081000143ca402e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 411149973 1250 411148723 411148729
    0x1504080f07080c06070206030712090524040f08030402120a050616050a270f030503130f0b030a09060b030105150a1505160804031403030106180b070b0705210105 71
    0x125035031141074070f60088180a02691103a008540b00c0b00e82c11a0400d0b5a41d032414800e441070b44035102d0a0010f2440d145210080010004040d07a0195034055000c614540740242a1042c0e41c013103d008000d00034900541001440c00d0001d140c101e44010075509030700f1180840249004900c05081e292a84203006106000340c008580c0408098145480d42c039201e103500c030142400c4440030240d0070b07503460000900324880c00c21050401600b15126048145990382c00c219030360b83c01812410a01502d21400003400300b0143c1c42c407204407080019900e04642d2540203490081403a486d040d14440e80b14400c5400300d41d001e104d85e42c407a0003c1030b80343c62010940f4082c0080f1403a141c001d4040e403649001310464454103c0103560baa00751442c41d0110b0701e0307254944515540641d510040248009240702d11420501202440c161031040c0d586490008141e0f01002002c910382c4941c400741c885c1000343c0703c0860f081100e030a5020241e810310500d0031100300175003415910101d07075402c40040103600502840c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 411151079 1106 411149973 411149983
    0xe1003022d19030b150307060f18030605040c090b0f120a08071208071803020904020a050a06020a1a0114090405010f020d06171203060f1504080f 64
    0x10b1180803001c00d20145000071910640034030002001078030312030b4070004589802402071130316174604842030381c404251326800000c100a200c1d803115000c9038510320000840c031071603000805241504003100800c0c0e0302e410039842e0b182450f03100c0001d55961007070103082010440c0d2020595240e50000c40c80c046141400810441000c90a40c0511440d40011401030704241c40d0394219a40c1d00f0012210b0035528140c8101000d0007030402e00140c1001c00420303500610280010022a403a1000128a00d00c0c82e400780006a01c410402d40401c0b400c8840c48100c28010703058a1440d5041c01901030340340c5d400340a520302030390349507002406005094000c803032004031645045660780042110a00580781601514030b9403500810348aa0813600010716070f8030a002c400300c5500716150701041240041603002c0341030b07100c8583c2c01c01d8582c032500786000b0002840756200406003403034050400b40c142 = true := by decide +kernel

theorem cover : BRFrame.Cov 410971223 411151079 := by
  have h0 := BRFrame.cov_init 410971223
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 410971223 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 410971223 ≤ n) (h2 : n < 411151079) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
