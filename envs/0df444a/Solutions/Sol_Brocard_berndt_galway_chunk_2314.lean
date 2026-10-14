-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2314
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:06.702517+00:00
-- url     : https://prove2.me/submissions/5508234e-ea53-4f6b-8ec4-3d3587691ed2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 416007194 ≤ n < 416187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 416008444 1250 416007194 416007203
    0x1e07050d03170411060409021b0115060c1b0e0402041a031902011106010308190e06030601030c030914030301091109060d18061107060c050901020c0f01051209030c010c021603 77
    0x1a156a2414134070441110010515405603001030b0004803c1e00d580c01a200c81c22840300040001c4800340303a5142203840b4000e000b640c0140340c2d0010480c0c81d0065107000280350007071010750141e045040c03a03440c10440c0f0740c111585410f40d42c428007040d0b0900d03100c3c500100009411041034800002d00003031f03035170b0540180800080b544030307650300840e40706812110117501041c0489145507120310304103029402680036220603964200203071411501c181c4c9090707002c07580600070b00d02c3c54072a0001100900301c50f00d4a1070505031961803d0000490210004c0c1d100d00c6071070050340d01c81d410728640c4001d8039070b42c04503c03000c01c1d4280182b5400e40e5440080301c05035294080000382c04d001d004c0e82c42e96014070444000c0d000510700407021064842c04030040500510800c020050010761003015180e902680b00814010703030080d40d0500c050300380401d0500005005040182c200b1001414040095004039004001c42d000440d5040c070168090080c11809001c1b030014100014007030680004006c200e120162 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 416009694 1250 416008444 416008487
    0x21203090a0519020301110708030a0906060302030a030c060506030d020304050603100e04030c02040b0406061704170a1e1e050319020a260c1209010e1e07050d03 71
    0x94008404004440546502c40d080d00d2a40c0300c5080502c1c4440202442680179500340f00306180ca00c0c1e1940d08030340386640e1001e40241552a40403085000f070520000464105a030761002002503a410004009102e1007540c405049200f20f1034140166540640716034000d03449000c1c084e0031a0b40100594050300e1099491544913959508800401c4280390b1019a4150814003031109250b440380031f41902c03600a07141481076410f00c80030b120403190b0501c00c01c8001190212040b01d0a11001d090f01e41090152000c0c0d00141100c0306100c2c010780c041000580811a520305420404900c1013020728072072034505045507000d40c2d40c69012a0b0003000c221000421900100003900040d001c01c02c1009901504011511444403d10242c054401e522a050b00c0c0c4203113501c07505c5d1540c203091020b48075042e240c5100e814542c3c4448400340400026181c62210754980300c100b4003009082240d840c5064000c41a101360501001b1014100545074102c103000c1e5084200f40b01c0825040315000000603060165403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 416010944 1250 416009694 416009701
    0x6050702061e1b0c0901141203270906060703110a0507060908010e01050108030a0c06091a0421081513060603021806040f05280b1207080403021203 65
    0x1000c620806a000c6030540a0110b650003102004010303040092074600c0708012040b00c10b1940da600e40c0d400780000d6103e001d520040c460035560b00300703545e102e400c094000c207112042d24007500e0850300b0411143e035040712010414107401e00160700a20f4402000e540b09101c1342040b0b000301c2e055201c0c5a0300941445984107511080c40020094042d03242c0e000010364401d248c0f40c41c401400075049205513203041d82411078100155506100d420b04032240d5500a6107400d00006040d00c110000c0034080c3c1d54180d4409824020940304000400c240d0580e03000500185058a05074920b1009044042101000700304071100340c0c0d4200e5800c9801c5091140302d50800b000f07540000301c0c4006a0710f540401c00f41131940c0040c2581e0990050007003d00560030070300384000c2d840c4c1070000c136002d04c1c41154402c000540c810405400d02080812011030075604504030400324440810310440540d00426002c58001114031030800302d03080d012341000003443d10405505260320700943d02c05000006550001000020 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 416012194 1250 416010944 416010949
    0x10309020913051009060902130b10030f020c011e0c1b0f0c0909151109011d010507140f0d0504030503031b09030f16050a0605030a05040312060803071502040f06050702 74
    0x800c400031407280405d00a8403007600d008006000083c00890180110f81040b5008106034018041190702c080d02e00062400d504800b04e02524150108816a0b5801c1103400360200d806c0c001d084000c00445c1400854240048030407044035145041d4074200840c8008603100e04c620803800c1513550b50404034515076170215061032720001d421948481400f62600710703e40200031a01014080c1020b03800ca0402416135030382000d0b500b40c464220320a001600112500c0c640605001c040c8560b8801231400600b84001c603a240e0b44007094145451005038000e0101915a500c1040800c191040d285002400c1501d15580c596990001400038010030754101c0c010b00c640007000c0180d4000010040480b10a0403a0281e9603442d2003451000b80c0401c07696030030109050902ca03824408840c0e1940d40c56185075121048800202030290088040101203802c900450941c0c0c016440581440e002942d500d84851403c800b42d1080108512003060060004200c3d01d5111110f0404941303450070001e0f541c0b40035100 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 416013444 1250 416012194 416012203
    0x9090c02030409020d0e07080304210f05070609090e03040b07030503060d21030b0d050c122104050111010c091a070c080c10090e0105060a03020c0111090a0501030902091305 76
    0x221114107440890110700c0b08195406c001011000e49096030910764444508070745900c581e010308507102003018a000110030a0f030008c8240d40340104030714000c0804070303580c070b03410039869134001c600103440d80c80140220300300c074850000114030400c000c5103081d00d0b043c502030300c40c0102c1d140070b0148000400018510303100c45503500035071076018a04420300e20b5002c1039010080c5120f01d501d80041d140604504050900185140400c2d4101c4000d001209401c41001100f00c14205099514058003009a100d0004100341d1a008580d0a03c25501c42c2d042100040900705c0170305606a4580c105140701c41050b0b0401c018030141c41c0d110084030300e0340b201d00180307140c1486485401000f0701c2c00c1001c0020faa0744003090080104000f21681c2100c40701542c0111070899141c0105602034103000300410140c60104000c3c0040a890304002d030425265040c05421128001c40c0b003929290001482c522078541780100c9005050242420409021700340c000c2071089100400c1280307410402e100642c00c1c80340421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 416014694 1250 416013444 416013449
    0x20a030f031e15060201060b0915071b0303080705130e0a110d060312080103050309060702041119081806010e07050f07030207030618030c06110c0706090e070203030709090c020304 79
    0x42c82044603202c150b490300410040b8035603000101c1000020070094818061802100d000700341c00340c14070200b64200204009940c4551180030340c10000c1c40002002420203444a0403030f000000c051a1460902400c0b11100500034000c01c05c0400000003228480000034080d01ca00f1322603101241d458900c2c00009001030a01030360310070004a4150340c07078050303034120200f0f1300d115814426000068990984160303400b070100810b0f5401c01c3c40004114240348001e8050140002e00c040703281003101031891002d40c4004641580d1813103a401700e401160700001c08941010541c1008035070a80b500c26003940790321040c042c000300000a0703404900c00130b1017503059490480204c001a55588980c0c13030040c1d070310310b49880216210307410074014080301081c030806080f0454260300d4400000d0b0a5980c0c050082484094584081303005001015040c4010480440504010b840f40d41e225821301c122004070060060031542191302c00c104002c0e6080d4000c0c802c01c11101010700c08225168040000e0b400c1d8040da4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 416015944 1250 416014694 416014721
    0x3031501090b0f13090b1e1909090210052104050a05070e070f05040608060d03030906050901230721060b2a010515120304030602030c09010906090303020a030f03 71
    0x2103072800071020100000c00d00111460313041000c0aa03035500035800d0300c13110001541c2c4030b000d8030700d01100b0b0540311003c1c001441004040c50b5469468440303c006400306900001c00d4151703604442000c6003014400d01c0c100301030303508003030b811710185188512b000002d8000e000000380e131040200d410000c04114040c0c100364004180c1c0c1d0150344034107075049014400c48100b000907410360320b9080464090002c0f5825224640c3c0e030085a40c0e1040705000076044111411810582d41e8122500480c10034030400e40180140c1c40041010b100551780009441c0b10501c4140010200c0c00c140191141c0140710440c220440310702c02c2d44240c4e2407020b4200202007650081c2100c04d0002501c91481a00000c04600884103c0071400b0482c000c0c020582258402c5400c0c841c00940002c214005241607007041e076540044000310ba240948903600c070010f80c1c0040e44c8142500c04080b403505d40320360b045103105014001d549410342d01146541c90080d83da4090f84005000d202e8902b0401d4072444c402d0b009071901000c2c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 416017194 1250 416015944 416015947
    0x307060f05070215160503150409050303060411121503150103050d081e01300b0a050f190b0d020405040b010312020f0a06180b040303020403020306160203031501090b 73
    0x88030040c0c805801c0458084005003c0d04816030a44002c01005500400d00300e50030030b44081c1881c2007564607500103001c0351800498654000c0c01a42e45020743c645251051002d1504c9003072100c144401c2d240c0e00185c10020000030b2148114405180c190141e1003500b0403446455820540302003810304141c0c079124001c1c00a1a400441440301c0010030201e8000c41d035481904954400301440f111080f42c004803100d40d0800001040041600c81042514114030f002d0040340d1409500c030340c5c0149003240170071260910b101c070400541841c248545940f018800d140c121152422002c0114018202407000303907002e54403085101c681d110000507001007039014100300300380c7c102400d00722200310007403008840d07000c0c0c0c50f8405201684046281c40d03081280c1001008041402c2d81c070305c400b030b01007000042c0080d40c1501d007500120b0440b0f1070103400350b8040c0e1001071303407a07045005040c03d0020003445e40851003213030003140c90104d0303001080b25440b40d04072042d080c1944007000100c40d16a1980c1c4948240d40d030 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 416018444 1250 416017194 416017211
    0x603081303050d05030408090f1302130e0105010e030604080723150c040f060c1a0711010b01080112021c060f0e0c0306090a0807050705090412020c09151002030706 72
    0x41800040050300d00940450b020060f2403442180c0c28481198001c1142d0f80030f212501090402044128600f10010120a030000c0201c00e04da080707800030a1806404050200200300700d150350400140900000c0c640340042d130f059240843d58550015100800301350000802005001c0e0060000b0b608549464000c8180c180c070008090f5904150204c1c1c9565900082c0802c5a03898500122411100820070429150b8035101c41034442e0101c511050b6200d20380900000b00f505045006180b08031801c1d1102c8511907403509409084840d0810324078140b00d40e40d00180007007840c0b810155074082d4110342c400d0003400102c840c81c5099100030380c01402c02e030902c00c0e048400302041c5c0060011070b12030412101034104d440d0400d95a440203030b6806040d6001403807504c020460210003000700d10b020b8811a140380d41e807a40441c4c2d401c8400c031010384115040707141d5550380d254103004011081c841207985d01100c1c14900100c400b0804251a228851280d480400f1040c1d4004d20a4031055500413a00300002e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 416019694 1250 416018444 416018467
    0x703031b020a0b0f0906040f0816050a0515070b09070602210301090c05130806061e0a03030804020303041a03060117150f0d0f21020d051606090210030903031a031f060308 75
    0x42802401c07100d0050348402b441c82684201d004044034001410b02c00024030702000d1050485090501c01010001008503030046070010881e140507184420050a03c03601e0b00318000e040c07007640301c5075107001d4038520410040c1c500602e0640f410b407541d0724030001d1031042c0107000355a107204149101120800744880024181404141c0d60301c5807a00b80c6640202c1100004100302c204c00c4403504039440480c200341400802d11695986070312030320140c2100d180580311603400c141c5581400c0f8482c1400c4c0c0020402080d940d02507503007081c1c441e4500400c40207007000b039082c0030b0310000c540c0700710b00400401e0000141c03030307950a40306805a500010035400300c103400d043c0712240304034440c001c2402003000307641507010301c5c8005080070304148a0380c3c0d114148091002c060708041d1080c0c1007503401940340c60300440541d58420594200b1003040e100098003600030318024040d140303003d40c016951380c1d030b845904403e0b480210f1503c80c924424a880c0c80340301501100707280100041d400c0603000d07407800306442d403000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 416020944 1250 416019694 416019719
    0x203060f01060f05160b0402060f070f1101090302030a1101050f1305031605090109050a140a0506010305010807050132041e0b070c090c110d020703031b020a0b0f090604 74
    0xc80d10b555550f48001d4001c542560288507040641c40542000888100400c090401168001e440140010b161082e0510b124016030001031094894020f0520004104a42c02c06c04000d03c032028204040341038590340000b038450451500c090110000c0d4a2185142d0303100b81c0c212240603502c0c0d18415280c81500303500ca9411800f03801030900034402e5801602141d100d41100c4005c0311801060560f4a0f801d1046030b0000d0031018250304241c0352161110b284050ba4614054800c07910407000203440c0c9802d50004050310010b0b44a043d540d00302c138105214a0368051400c3c140307c4000780503881c0c0c9105030812080e0b451014007174842c6246003c00e000c0341c0d64424180b0180000300c3d034620221081d884051024040c400c4c0394000b00f1007030f110308040203601e4081d0800c0c00601042c3c2400001820984d41003414100c55450180040c0c0117074905004240d041802c41d0b00d079080c021810001924203034041102081c450066070092500030032416070985001088403c1da040107008251219916250031081c1c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 416022194 1250 416020944 416020949
    0x201120f1e050417070503070b07120b04050c0322021c150b030721051e120906030406200d060303080c0c0a080f0d0908180102060c030703180203060f01 67
    0x40d2440391818801c842264012140556000758120034038140e02d10074804030b070380302007400c44050005111010109035488070642c42107040b81c8901c1a0a80304008240803500129010b51080f8500014021501e000c1c10640c3d512801c4500180f4013411300d0207101000390140340d0000d52107040f2400503511041049a1307034907045d00c11000303401240c0c1c01034044020b90f00710101082d050341c4030344010003400c408811003240456030a505015005074039114141054404900d03940071800c440228860040b04011252a22b43c01c0b031032050400c180040040c4951201170405810662285948800070000c003d036401d1041499241c1503686021810120140c0361500c81503010941580002e039480c4211000c44202d25129809894204e2850790f17a840944c00c285c0c1540c014481c18030600b02c00350150701c00c3c04a1940200c080ca07440d00d030b00301c00141074101341d01500c0d4111342041c03007030041c0581ea910640e5001240390a0100f5a07851425592510704450031010394580300700003e04c81030b2412115200d05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 416023444 1250 416022194 416022221
    0x40e01080a112d0402310b2a0708030304050105060109170a0212030d02040305010209030c2b110d060209011404050307031b030206070b070206150a0308070201120f 72
    0x510b401820046118040c081e041c3c0003c00c0341d1808580320301040405a0103000003000103080c01b11840780d40e07521041d28550340602014034088031130841d904a84400080c01e110303035003d24015084015200841d1812545039801d016000c081d4004601406204040c0c00c2c0e0f1411a600c03440d00c0d0400c94042c003801d994840c081112140c011848141200114418440d048003c190b003400c0c40c1e0030300060b4895030052100c540010312030922403508500041005501400002d625102040201405c000c003003255948115082c11110240680c4614000e1400c024101860100003060401e0079022203443e0b80c0355404036003800c1c68401c000c110750103060b00d00c01c01c0e80e4071110341a40c9001240702e0f00c1a800b40a9043e03000d903004200251800d41202c1142c503540d9a42d4a1103541c030741c04600c654101034400c0750514013090801150350750400c005903010b440205a070b44903140380004900b07170100d1400040d0030450000741300d4080da40a00c0b01812900c1d0382d01010409050f03500b403030038010000d0303614804 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 416024694 1250 416023444 416023463
    0x20a090219080c04050a140102072c090c010e0d050304030c060305090114040525051206011a040510030209030309091006020c04140f100f180f0c020a080906040e01080a 74
    0x40740f5001140954066807000350001c051a810441c0d1030403492035020509045210305080407800c010b0308025800b001000e281d44412602541c07162003000340300103205480ca42d010070a1202d00c0d0f81d001c0310900d4000c200340c40c030301130f0000242081c604520507500043c148805c1d07550300250042d81940854820a50307800204039100c00360002030940340c020f55000d0f02d1580140c02440c6d4000d00444a1425106100300c04201181c1c0d40020601d211449076224000380c201c140100450f03007412141c010071707902d13030bc60031703442c8c03d04040006002ca81c0c00d00001c0d040550114070202a91000c008840101000801c080803030f103841d600e5583c16101c103000b500c005001c0c0c05006c10b11070420b8003501e03945d6150401e4042840d43c906c0c2e10f201d10008010280001d000021000050f60b18105282030301034400c0c0340d820095844011a0001075500c00440c051002e40360004410031664045904070000f03500c10902551154201e00185190203140c03c0f005a180780b0340d000140381000000d402d07a071580308045d4a07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 416025944 1250 416024694 416024701
    0x10b0a0306061112160204060b091206091002030c12040c0305120918062b0308070c0210030b0a0f06050d06050906130b01020a081611060c0712020a09021908 69
    0x303d419003003405048215074000707105800e8078414600640030600c0b043c1661000b2440540005c1c054500307503441450400400140c0c20f03584d081002c101c0c000510740d2001400c2c00d050035105a50ba544020901744603032940400404d80f154403000444400d446e40300511040307802d060501c403c0e20216071004490038481e02d4480180303041c4246c01e85a0746c840080c01d80c1d0b01c501c07090303011410b03000d40100f100e680804c82c8034030240d024a4504448074500055a441040400103250282c4452400380011003404011450900160f4800b94594030384410f0349408a0340b211071201240b0b22200341c0c1c200345000c2c0d032031490120f001131388000501402000d15505000341660b4506000c0e420005860031900072201003421103642c69a0381045c074603008180304669560f52940c6408146800c02c112041400029003005410700900a054500881c1c04036016032920646104959642c0c4641c031400d04607865604c012420340d9036604221001317100c50740d0f05558a8012020048102d80840c600300046402a03010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 416027194 1250 416025944 416025947
    0x40312080712050106090303030b0d02040c05041a0910030b040b100f180602070e2e180e03030105041d0307030806280308090d060c050316110c0f0109030b010b0a030606 74
    0x740f0f4100d800d140c4070071074001d003162800c401030b001c00b21156800122100080005844c4c07485440c0d006565680d4807922182000038a41c01031b91090340ca2154184c09001c403c0c0c4990b074007401c0700464041e07414005000400e8030040f40c050503002d0f40c0660710404c0c00f40401c042c540c0026180802144603590307894441980701c1c0700354155485002da60700590128005000c400e680350b43c226003141311002c845070249210703040f007868031012900c0d80e0340d03100445070704015900c050000c8035001c0f11100000d01c04000c520b00c42d160b890005100d16032040da101d00000e041c40c050743c40e500d886400300d8010349075a28120708002c0c0080f0800c0d0f4055001d1488042c518940c0700d020301e9410383c1d000488260880035842c580352000c0e2504036400c0158822134401241000a04500ca4140110502e454440c3c40745480c2c042c490700d10184c0074544061000e0481c810b0790000001c41c0000d0181e40c01c6036413100d504228401240c103250b80e40c0000f403030349181000119400350304d800909401c07256507406000c0c55448040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 416028444 1250 416027194 416027201
    0x20f0429010801140d031202040605131d040b06010c0525120506010308090f0303070f0c05040b0d06050414060a0e072c04080d090b10080304050117040206040312080712 74
    0x2a003032030310b820380030346203a6207000c005200c41d480c002e00c1d00d044100301f100740780422a8400d80c4403a0210f0000248601c0c801f070400012030080c41c410349400d51504c0c0c05140304d040b81c42c00600c010031805403400080c005a000340600711206810a08913140241d07844a10503040e00c0e0f005076000e5403000d034140000c0b5001800d02800b6000d07449405480c1507461f540d0355a0494100955aa40c880f5061501e610a600d080001e04801c1b4020818242503541c542000030302c014950700128020b60620840d10065290079034508c1810b5442170001038699914180349000024101803407069005134801c0c4034080c906038210100031180c903000e0700e11039a0b032903125043c0000c0c0500040c00c0c2d52803a160b141302d01040c07441d02a034003601400703840345000180d582c0d52040315400030003161075018003018030101e0500c034104c44c0041c25181005524144c00c000c0040c2c403071014450411448080140050110f4850b6800e03180250341c84004602416201400170f409480119890400507800c111a102c510f80a4003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 416029694 1250 416028444 416028449
    0x30720010f0c1106160c030e0324040b0901020a0e13021e03100b090a052103130602010e0c0f311a0a0303091404150e041403040819020f0429010801 65
    0x441d490406d820b55a015280c40d40c0200603581d15004040c244201400110080100000c829001000703074646440d042000700c03000303071511469078414802c90081540004151031643c00c22240b1080342000300328004d002e840780c02104058420096079184041210300040d5020b20b0240401c0135007030b500da006820b082e001e0720b5100d40d4010f0f41d5040410031410301d424108003a02500d00ca0003282c21424200c03a2842d13015000c0030502c103605240c20000240e0a00c48c0800c9000000b02a0a25260320b0000903220030008600d50b01c15810490090740b0002100c042e80c104400340143d80b0310300151250060000c2a8004644804040541c0c00002c07520f400241c80080c0d980c56147d9050040c10704044228441d507440b1401d4006603505600280c44007451482c1005150300b1160083e685480c0c0b400c000e050040b00c0181c00241e00a2009012400011580802c03444040c0c2e4140c400741c1c4240000350755a403d6403001c0e82c00510308844842803112103420031504251804040c00440118001118804003d2 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 416030944 1250 416029694 416029697
    0x1e120108060c07020f1309030e030705150d0c0c06062309090a03110a0218060a06210c090344091302070b10030512030720010f0c110616 60
    0x100840001440e041724407000c6010040c26014115889100007011145098016808281c81042444c0a4030b010885003014200943c0c40d103c07008594034000b0300500410b4aa1518242c03035075048181c141c80343e11401000c0341c00c00c0d07042c4038007907840b02d014008403c802c0b0698980c1180035001149400c0051489000c0d50004008100303440094030102c8181d00c3c490600b4040780a5010600d0169981682400c034400c030394080031409080c61010800207200d030354810360038010b010a05006916840010045510b640800404d00c428000d0080f190303051240c10040501d0903038645808030f501c11300882c450002c1c038400c1039580354049401c0e03950100050a505168080100150700150030031001080c10f4a252081c0581060419a103d40d4240c40444444103462400c1c0d0080050240c1084125442142c2010007071450030100b0b00201100d41010b01c80601a07142078004041560943c001842c89003c941c081203e80f10400008110703064010b01603100d817080c42c2c0802e11000c020005418440d516 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 416032194 1250 416030944 416030947
    0x150702100c0c0f020f0d0507080c040e06070c030905040c030b0a08121c0e03040e04032c240d0204170715210f0902091003031407081e120108060c 64
    0x41c0d6543c0704a6400f1030740c12600005007100040e2951680e140c4809a6440340015081060605030b5031840c0800030352074540b040f4148840d80c103010201040094100b00b15180c00302c00308200e82016128800c25511860704145441c544100300b17940343e1b11401d51040212060400256140003283e03580040006201341d6410421004496542c12a40c01c40c00001444002c80d110100e003d40c24110341180c1d00071103014500d501000105540201c41190200003803225a540d2488455050106003201c0f10060241202002c4000340d8680489502001e00032041a070395a031a4494104c03020350464440d0445103054126410700900e004a581810b1360640840c9901c0c1c1c0d00e08003400c441d9082d240c954001c120b004410340f0000000303140921035641480e8000450190803910502c0320b51000100041488400f0342002c0c400240d002c0c0914450b900c0991400703031120440d00300758040d4401c90041c00340c00c0c00c85089604124116202602c420441c400700b01c41c60b81c1c0d03180d036015220103044601d801d04110 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 416033444 1250 416032194 416032217
    0x100323030301170a020a0308040602120324011106070e101d09070c0503030702010605150705073014120315191806050411090114070501090203150702100c 68
    0x550703e100c1080c0008002100d0003c011500403869121840d00183c0b410300d00010117000c020340401800401a0001040c2c500d14541012540742c4010098071048100e04a81c4958031268419601140309420280640340c080c140442c02074801c507060689a80500186c02d5000803041c0540e001120701035401a40c208417810110405c0b00300d400c0140f5982c10311448080d5040814020130246116402540000510600785070401c4101c982454052509480400c81e0800041001c50f42d00c0c2150091100088241c0c0c40c0000300310100c441020800000301e800e0108010b100712a0500401f11103688103950301542d40e000c0c40400761108990f003c2c1124110308980c1001c1c00c0c02144044100c00f6541d101c079046844841d0400382500c03200d1403520f20f40e1615000c4c040b41c0b03010701c10243c1445800c40303485d18045110001a007503000f100f0304d24101c00004511001400b00a402808059070b0007010f03900ba041955198410190096841c1d00051181100050414010740b1a86003031659907150390b0320703112 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 416034694 1250 416033444 416033459
    0x222080c01050909011403120307050d051302010e01031a220b0d050a2405010e0402100905130f02090607050a0507060306031a0703061802040e09011107080307050c06100323030301 79
    0x2c81e43e9404e25010b1080a10700c8d900c5410f020301660250900c0d070748460b40c032502da40c81d0206850018005c41122400144c40200603a000620100700030030a082c04140c140e100c0c142035a4078004580596003202120742046050854400211901002c0300410082e52200d94144a541c50210320018104da0040c841e030000300b43c20031000e10408500d50000340c844c000c1103411805441c0207a01031030300c6c1141c460900046183c81070f0042c46120350740c40c1500c005071401c0e001402c8080c0c1c0400807401c3c80c0d45d031140d0144892481d011a41001c101610319540c5610603c0c09076a0b50b14031400944082c003910901240d0341d40f00b03000c1e490851f03401800b40094030703186501680c11407074080e017001e060541e603040018101c845592807011035464003c0c01a110351412400b40a00a80141b00d203140d80d140c2140b142d10300d10035170151a0610340280d51140c480d0b0314030308240c84511030041d40c200f261080c002082a801c1501007600241c0f8030860664079410407900d00040301442001201000c5e0304180010b00141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 416035944 1250 416034694 416034719
    0x90209030307200415060f08090303060f0409021005270907111e07060f09050a0b0708160f0c09020a0f030b0f0603130302060606030403020d050d0222080c0105090901 73
    0x72207001030380c0300740704800000b021150705c9041d614404003a4102017041640106000000441302c0c1082602440c1c0086025124440240a075208030090700045070151030382d0b480100203c0c0d0240500c04038040c0940042c0c02030308821950740c0047c1d00c8448070203030580105524100e60001404510300342d11294400e0b034940c407421040410910031401851018041c0c00c5098a5142888010b841880e0a080c3d0062440003d04a14000c1c00350300001013081d8ac4600b444141150300515040b40c4a5940d841c22501c04d12407007040200900b0840380510a000814501040c0c3c54440c04464000c00e0b55a0124026030281c0278020010801010030038410038020341002e209200021301b19811029410300040d020f4005481e10902024081c2841d0109901000100d8024804071036060440c42c250b80c00a40e02d147d00d0b0080c204021010450320300355109074066500c00c0c10352180c188210305058028a05800a9110b000084e200d1025004480c2d4000e078106c80c504840900502c1442e0700700b141800c0c19 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 416037194 1250 416035944 416035973
    0x17030906180a060203130b070306090c030b03062d070e1014031515040b0702030106060e030604150213030503090f0a051507050c09040c080c060306060d0b0a0f0b070c090209030307 79
    0x10001b503a00c2640090700c0c840d1440d06c00d046a031000210107062513802c1044a000f201510149480d280c08400c8950700002c1141d480507400e0114021a100486100b440301c56031154040388010a20a0010594001a89450070082502e080300c5081e9285011140780d40011704095602d14100003103000c420a8002c85812101d01a008030380c0d00040050201c4c0651180d84000342d00a00410b0050441c5420701a0070014409442c0202a2002c1c250009840b0b60000d0402404080c148080208140894058906004080d894032080a0340c0341010750b120351000b44994441c0c00d420070640359500e00003403210190f440107400d014540340041c8081010b5171185030180c07028414a01c90105650fa4000160b02c100d20a55240748418902805e00749011035011011744507900c01d004004598130b0710020344e507030030f039036054081400d21034240411030600658010341118028980046904a5135000508645114000b2520301c19a100c0c464422030246100c015415003003040244080348240008411 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 416038444 1250 416037194 416037211
    0xc170703031104090c18080706052d030402040e010c140c070308070305040e0702071d040f0b2e0506040611031b010c0e0d020a17070317030906180a060203 68
    0x2d488440340b100b9400c5030030960084001903181c103c942c00d1550300c20120748001d84501c2600c1e50013810050b00c6515010746002d02d604101e0007044c8041a034404000320044c1c24a1f88040c0c00030184100142c401c1c07a40211070580c0030b5070409003025200d480520400300ca03450f1a039560100d90036030302ca22241a1340441142d640610032036102101041c0d02000030034241d44a81c42e100d030380d00e00e0030340281408607009110704150b4118100401c90b84210a0164186c06400c8a40c185130b9522464031408005800c18003504101c3d2880802000802c1d0322882800c107030880b40c0760b08609030006c072174070b440c0e650902030701c6d0704000c083c482003010310b026042d0450002036600680341819a2201c85284c50040280e800c4143ea440d039510390300301c507084003689038401025148808558201c0d008106070385800d100f180140d00341c04201c1051542c00f40100c0c0051a40300ca100084080106204407164009030b1382e0b001940124004a40030f40d0824500c96001440c40380601108402900e800c3c0003500020030504 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 416039694 1250 416038444 416038451
    0x7021b0406080f01090c120b04032f0609011514040903020c031009020112052401020c0402070c0512070e0f0a02040b041203090509100504050c070b040c0e06010c17070303 75
    0x2e00100a02140c12510f02507400000c001c3c40c5401d11482c402450b510100310b210420034418041020a810250711507003604017036420804181ca0b110072284010112220480030102c40b508000d0f0200701d441c0203e0b140c60080c880500c0318402ca03100c441c81e520032005469802c00030304d821030500c1e0708041e034803c7c000d0058411513101e4802090400c1c054809184505649074041c40456820021124070b4801c0b2000411552600c0050402e40c1e40a40700d105c07228641400b5184580c1c4c0c4204580808050054415500c0e602103141000b0401c00714081c0d60710440040307015107094400011190120f42c4c0d0b40a02c0843d5446601213100c4982c405041030300703425000c100100741c0880303243c0180300401034010321010444071818000c0c005107158012500c42e40ca01014003642ea08415112000d540b800c07a030004060701c0d6140403441e2840752900003401900e003e810801400700c0128140b045034403800b80f410903039407038500440b0349040011008007030700114100052000407042c00307010010312a0a000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 416040944 1250 416039694 416039699
    0x705010e030106091805071509050d0203100c17010b18060d0b100503091006080715020a170304021003020a05120601050c0a060e010b0f062b0c0c060507050307021b0406 74
    0x1308280c6145540c005030709509070f078880c400c11008011640040c01003040d44651100740550060030800b551289601c80e4400c1c2c4006019075400340003d144003c14044200980080e07480c000c0c2401c21a5000344030b4a40301c00c1e00028141d501031003201c40300c20013400c01c22003940d140c6003040f04681040b066540e0056850760136550b16155103c1810001000c1d4a50907241d02e05480d0052400c0b404a42c0481d00c3c44c1000c2040200c1d080000d403541c1614540e1054000381050504200d2070458050b802500361042d90b16620010740203d80110f01030742c0291216500b040413900245c5c00e0b4802c1d4803111001400030020b02008110340d80030300d500084c0502d0b186283c0010785c0348040c5030100100302550550782d070b01c40003501d501c001d204840206900391100d05248040d400000c0030350140801307045240260b016052444034070680c00e1200320034004001c00c60440e03507010090000e80000402c03180280f414001c02c10550048080d1f0f442200650b00030111007569484e64003801c201104a01c0d0003035110b6401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 416042194 1250 416040944 416040959
    0xc0a1112030f040b060d03020a0201030c0509062109390d03181a07060b0d0c080d08310219030f050d0906080c030c091507020a170705010e030106 64
    0x1c41c000c0a00d0100c2c1851810f1900784043c8500010b03011900c00c90007071885400082d008900c001c41280c0900b8002000e142d0200141d41d1072080302032050f8012030020b04541c0914003801c0c1820620301300300701c2d40c0340d5a5030040855a10342041c1c9a0595040c42150800e851041d84400c0340801210110080c184001e0b82000ca03000c0428508100c0128200c40b1a284130300c1e0710300c0c0e081c9008204208084c050341c01000403080c420702c2041006025644c5030f01010003203441c0c114081b8045503024610100280e601c887c0c10340c45805104e196800982e100000c034140500140e1421380901c00014410b0900000c08255202c00300035800c200c1c4c1280002c0300c94101e0200b121a0040154002c0440075024405481e1140c1803500742d400c070005011051005101041e4420601644a070501d0a41552500c0f5865a00803a008a083c0690700048000000f0030118480c0040d110072031007902c40580c1c5ca5241c445051151030846100c480380d0703008240420513584204502004014050000220641c43e082c2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 416043444 1250 416042194 416042197
    0xe0a060504080903060703110a0806120708060f0112031416082d0a050a08040f06050a0b030105090114070f270501170f01150215010e0105030d05030c0a1112 69
    0x102a281e03050b000c42c4000c46820140002039000c10706140802c10781e010701c07a0229050113a041640308104a600010b4180d0322807954480c00c020303d60044405c1039940303164040d0f417074104490182c01a902034000003040030180f5000c80c1d440e54151a4100c49494450204403a500314590782404581c54415400200b040f120003403110524880c200401654802d40b14403055480c1d070100d500751030040001d01680d90f84601035480c2e1590624184186403a242804800781e41590406006075151405001c203810995016059030001075009104698070100315500700d481c64005d030301034881d90000240821b442649030001194090620103888004070b1009103514000e080f82803090110410103118035a0020490003980e50780202100f090b1508900c010888601841080044400200c0500855000b40320740380e40f807038040d03801c0041c0351380d40e2007141c0d171001c8207114060290280100350100544034900300d074414021010401e281468501003290689800501c1102d20301276408008000780c803410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 416044694 1250 416043444 416043451
    0x10302031e09100b06040e060906120f0d09050f0a0303050d0204030f060204090b0a080316020111060a0b01110703030504050d02010306150203070611031312030204080d0c15060b04090e0a0605 84
    0x182042201400f1440445002c0c100003485400b040c0b1040111104074222180d001000766440003441e2038000100d410025249504c0141c4c1c01800c40d40328040307000184682e4802d0540c6d48020140356240140f16082d04024409500310600c43ea040c00800d0244008100c0c0907000d0030014680381c0d407a180d0441781c9010000443d5940c2e00010200300381030040c09101030000d412a01020303075602e81010141c0e40c0c450150a15116143c580704002968082c1c8601413544903803009036507591800d06616401080c0c42c10000340490f46403400160040c0d800a5141d003907a5040c1c4929280a0800c002c101c82c516049000300c1c10503865901c0495980141c0350802c0454550340c00558942d4040d250010035101e200400160180b000e10403c40d000060004081440e904605400c802b20040c0c0c10031000fa103c0c903080743e0040d1080011300d821081e84040004003c50148100c00c07091050164203000307641052040f85011001840f00780b140003140e82c4244804600c42c2c089a0b00640a956003100743c40089 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 416045944 1250 416044694 416044711
    0xb100305013c030c030c0512030414010306030206211528050619020f031806030403030f0213061407120809011b030603020f0901061d030a14010902030d031406010302031e 75
    0xa405c104100e801c00c030f85006002e080700c00300f1240c500d029846035070340030324801c0321700145d80003859810b1a40a640004051078001c0c010301d0b55a0014000741e060035000d5002c080300b10340c001000039901c0d400c220b901000003000920551030304240b070845001070400c0c2d40f880044815100d500040c01e82d1007034000c220302a10b03000301c030100080100c80a4200340d05004c400595800400030309400407095529030110340d804a9100307171240c895041c100d00424040c407400c541d00344006070181003c0f008034903820455805a44207450003e00315061101400350540003020758038403106c2c0c6542c0c0d030300a03e00c05500481e20030000402c10381c2c45e001b81c9141d52003507551300b001c29500c120500541c10042041040303080d0590700074030103501d007003401008a41403c040c429036200c0140041200d5601740b00d080c3d00d10380c0010380070121b00701410906000300030280007280700f48500b05094401500900807014143c880b1846001c0680d40c910064000e036200800302d11005408500400d084800c00d01c4030742c0942c458 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 416047194 1250 416045944 416045963
    0x314041413066801060504061b0f1b0501030b30010f0b10051c0e0a0b2706040c091a030607020a0c0602030c0619020c0304090b100305013c03 62
    0xc0ea04100d03000700205843d450b82c0d5080c0b80148442504036044500b11509440e01c03500c14035081a40030395460b88010001c2401201365420002d1021a1200e409007161040c1c038103071020395a500542c112440c622076aa08a5801714103202903140d50000310880d5000c01400e040c040300c006000c00e08442c4401c03200000d1035600d0302c040c00c04d810700000844c40c40360103003040c602d440444144a071108034154584080309440d01448180c6800600c0340740e1031150310650004160401c0e490001071404241115034481c60f540c01400000c060003e00d05009941156002d0041420080312501810006085045510a00c60184c859403003c2000921078a00780e4090030403030b50b240c81d1200d41c20702240c1c041000c55009011640c072810000c1005030704400c29101d00007401d46500d078048040d001c5c0c5812442c00d408040b80020310040f494110065108048513451200c0c00ca0700ea060701101d00138040c4c84e01441c5803546020140d4812103e00e4016036145400e501c44880d1402e24255904458204607110b880 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 416048444 1250 416047194 416047349
    0x4030219090b04091a060a0513020d051f06180b0a050a02060a0b01020c010c020307090507050c0709051012060902060a0302090102101407050304031404141306 70
    0x14440c0c2c15511a084070b003030150344800d448407070850503000c4080d000441c2c0310000c100e8583e11a0464002030401174031043c59850001c2011009402c6000c421071441e0905c0c2c00074841c400c00898a901303803200b80306084012414407100300c84400904200c10315280310b00310003040054940d009450031483c5544c8580e40e5407141d01009040c1000540740c01d82041c1807007480d1510b6a000f08a80c008a0828604024801c0660000034a0884c4e603601c8411000e140206201e12560b000005208072014081115903403580c1d8408141250821140843c0c080300b01481408002148000c8000d12170042e0804107605c0c00700e40005060380e00010b14000030960000c0c81c03004c1560107008000c00c1220441080105c1000000032100b01903004201100300000000014101070203101010800c1d5451030710281c0315925003000d1404c140324000c1c0188114001c07100310270b860006029900c1580c0e210865603407480170700070610b8140201680c2078240718403850b50082e542c0200e41120b00c040e07800c5c01408504100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 416049694 1250 416048444 416048459
    0xc030609021801080d031a0612091507021507030212010b0301060e030309100c0206040e0906040606081c030b0f04020706060e13030804031b1a01090b0316120804030219 74
    0x441d150100e84150a000100025000855880401e2a440c1408101f8240ca0900a285000740d1410f01e980080d003c01c0500700481000119449501003030100e40d500c028904906294640031507040005034048401e203544000509a000c0d003004c1107003000350400c00362446407100180c0903000590794801c040700400ac11a80950b02036004401a4040c5103019140d10200b40925034500e200c03400c1c0060409604110340311501200c001b80850120f200e0141410520162591010782d0284d03011400c0c481e01003241d040100d600606110340d00d415600c69541717114142c01900c20124501c1e0b1203101070407039002c951907a0005000c5a44107010008249040501d02400410080d26886111502c40a22000250001e45050300580c060030b040100200340c0e81d9440c0310607a4401c00804002040948070301400d010b031402c038141c9a401505006488141040c15034036101c03280700800c12459013004126824941d84500d07140b0303001e0184e0500e0503484e5004121543c00102e496850790451316400c01254 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 416050944 1250 416049694 416049709
    0xd150c110c01030908070206030c0c070b1905041401120f06080a1502090d08030a15030803060a05010305060604050d140105100905070318060509150915091c0513030c03060902 77
    0x5540c03d080801c1001c00c0d03a100c0d804035014600000f40103450000100381321040080c10384003241800011280350715251156000c6903005107080740402c060746040d82c01043c0c0101c080d20305990b6440f03401c074080c19070034004480c2540c1c0c44250828955072600400441001c03030040ba40540400c20081140300c41503c0c011101c1800500e10030211403050151312019071368903a81044164004840d1a02c0e1703290b500c0d040d03008041c410150161403907014030000404c070501004d188941c5040b1103014990790348030700640541e8000c84800364010b0040000703110303d251080711404028001c01e500890b03101852807032400c543d401c2d940c01800c2e0070030ac4420005003000d40900b40d400344103813405200302c02800f0803000a4000c0d07124010821600c502c001881b1440812682c50b28501c158100c14990828040d1103449032001249401045a04000104240c4000401d61158400600c040c00060000344084596030454031804030801c41c20000080071078201d0700900302841c000d150000e0080503510402000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 416052194 1250 416050944 416050963
    0x10c031a06030f16020c0315190e2505090f0921031501030905072601060e04020904022202030a0f1b030506030106050d1a0c03150d150c11 61
    0x6008100100030081400d0070f40240c2051204c080341092401c102c0e07060b81804074944219400d44101141203e48890303c82e1030a010301c01c01403030198584940010714054565a080b4288541d20a0b46802c958420300407a100a40070002c1202881d01e80302d10010f11241800d42d9440c100c01160342c00d01041c3c40d82072001c3d00c1505621917840d5071842c0b109840700f41a020081044003c0e40b0051710b04191a406030308030416050f4800d042d943d141e603e07120700c8549003460710501580056246101005d0060500c0f80381d007690a0040541606e598076800c01c00001c01c01441242c20880a071480c8001c0a0000441c1400301240f050141e124546004942d04403001035034200e804a080c0045410911407841e20f02c0e450345950b10303021400d50348807404070b2f0141c00700781d100d190002140c94451b8144030140e04201d41d2440341c00c41004e0307291502c010114541c0810f0710006000c0c240d110304d085492410040007041c50744212101140c10240d0754550080b10711a5039043c0200f20044003c181210051000031034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 416053444 1250 416052194 416052199
    0x607030e071202131409011b02030a0c0602030a1b021b0f0108061201181104050f190506011e0513171203060d0530040e0412030905010c031a 62
    0x7280c1d4603004810490a000d01c0e07019000703601d645114280502c05420030340160b0809564581c803420032981c024002c0203142d108600c031408154400100c948040304948400b58039039034003120300c00b29449201c000e60001d000000320507134504074501c00d1915900c0307803400300f1303810b0700604280070456004090300001c2000302c611408009411145036170304461486d81282060b60b6228030503c1d4006141d0040000c1c00e48500d2011400184100300b02d40c006080d000404c1c292004c1c041f544601004400460f41501d03c14800c0031240114110741c7c10940c0300030b0f0b004405241c40841094035660020202000c2c0444000044002405c41a000410160280142840d0811065106070100140d4071400000e0011280794000800300c0e42503a140d91a4111445e040029507025041880c43c025290a40030b20f2a41804080000e0383c4407100d00c201031b50b040303400f15400540b841d80d80d5a070f0302040c0b0712101801d4082c1542da44014002c07550910451030700d0002c90310001956043c0d000b03001c0409220300303551407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 416054694 1250 416053444 416053453
    0x3040e0a0204061709161206060b090105160602070f03030905160b0a0f02011b022404030e0d0501090b01090f0b03030f1905040e0a0501151e0f031d0607030e 69
    0x8903d5a0248611000c1c10040760405003580b00d208442d410300484121401c400d00b04c0d040d0104003405002d00c035200d01d600c074003030800a056035501510325038090060f1080c0452800d100d00d95441035062000e0190602c5454014688103640c1c1c0c9400901d28008401c0e00080d994038400c4082000402290802c1100002001c4040e03142c599501c049128110041c02004001383c03c0e042003074000d40103102103ea8032051211841c2003940001d40c0c80e448126100c013560000d0611a00c00d9070f0307002c880ca01035901070b07a60320403d026510601042c10706007882207500c2c1d9070364060540030170001c452a40c0030701400702000c0707081500d86851000b900c0e0300c2c0c100c082c440e8008100c420804518082280c10140c05401d01d03201100e10200c081c0c03924019940b0403d456203600040081c100c06640c004c50607a00c0200002540300403100c000c035242e10412820300c1704a03041115150480b40a9a200c003a880110315003c40d004042032100141244000044206a8415014040c0e5540c040c019101d0b40b6031141c0c01403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 416055944 1250 416054694 416054699
    0x304060f051b0f090303041d0622050c0c01050406060501020f12090d0507031b1511030a0810080123010603110f07050a1e120503070e12030c0f03040e0a0204 69
    0x90010b001445142c620300200000c400da0b0807090501600c5494a000b801d8903103880c2d88584440d07a01300103d2600f003072440300741c000407803600d058882c80c01502c00c1c1048800c2016a1030012a004040c05032101650840078462000182024000c2d10320480c46000c001c07406919080c00640f40c00810040700a040c0c00680304c145a00c50102c0c251008403004403a00d036501d403064280942401c8079900042c002d40020109100001003031060718081b2641c1301d408100603c00c0107022641da5081c4c040616194004000c1419003078440c1100c2a00007400b00324030304105544641580c03c4481c0d00180c0481514080d0340c480400301e14040040c01017503541000c0c000341c1e02a1000c4038080c460151601c070103882c0030481c0c0f4140f01c4200421600140c2c0304212412148a5540d400c01304c2c03504080c103d401042c1d140039070580500c10402c1e070b4090401a00ca41c40701290410821041512600304001c043c07006101030303611204100300254241c0c3e10000519955402d00f0403244a00d48020508103500b401003004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 416057194 1250 416055944 416055961
    0xc170d02062e030b070804140309130c03062105100b0a06080c040320030c0d0203031b0c0301090605060a090207030c0602090f040c030e1b0a030f0302030d060b0304060f05 75
    0x210260764a45150085600080308521a1040f6000035001604480400c60720b103420a141d14019401440010030101000c00390304d54900c5599855a0448543c09101504150f00d8000c10882803850401003203650f100c40310003680030181045840705207018452202440400e001000c0c4014900100380302040841000c6004461076200347c0c4100a1a40001032440360070500f510701550b4800121180b0340c2065401502e20243c0104d0704fc03281c000c1c4107040d0900d203000028a100903034090059410b2030142030b82c9010100e14014100f51602400021840d079035070a02c120100103115000006150601d9403e001c090a01908400c421030310420079400403903046407090340c08a602c07080140c2d40d459500c01141048032a80ba400303070464100494600110b0301604183d619101003001c07180120b00000b50482411800980700341c014007240c3c003e1010a242c0c0803010005402401141d02d000e0a0b403080740b0489d1256401000c10a9001c0b05200c200201d034082c00a000c0c000f008140002c0c24120f41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 416058444 1250 416057194 416057221
    0x51e060d030f0512010b120a0504020d0b0901090209180601050108090604060c140a02071e03230c030601080c090606040311010305060a08010906052205030406050d090c170d0206 78
    0x402600748007103242c80d0500c852080d42241c039080109108041075596891050002e600b21251702c46803c8140f00010340b07040a81d10800b8400d9800804825042da8652501d1041d40d4000d030a814095481d030b85081c000d40c40e0346400ba805029110a4024000014250181400c6e0b068104038101305400007444055a0005005034200d90415030006d0f00b44640c44050ba010943c010442028580100f203e0040079001b28020046a020b074250107515001d91905039014261408001c164644416159880a050301d03218000740e40c0384412248a90068030003e490700300d099000e080d80381e0284c0840a0035007000c00d09030b900003c5c1510500c1c03c080c00d543d06e21451960160803141016038400008490342d9555000700300500040c4000c00c08490075090039400b91404845070000b0804429240b41d040300001c080c4002c1c1d6401102942c14a41000b004a0303140d03000d09071051a45d0386034445540419041ca081400a0509010704004011240183d40c00e000e01118004155080b500420810343d12610 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 416059694 1250 416058444 416058469
    0x120112030f030b010c1a1806060105040b0309070504020403050706120903050412051006080d0806031504080d0b0406060305090c030a0201020c062802030403021206040c0501080c091003051e06 84
    0x300881d8038080f01c40100c80790444d00401a20507a014148a18042019101d4900482d14000c1c0d00d0303507042100840a81e104403e07560103001450403c41001349420b15005140c111907000c0a444a0035981c800240580c0c015070010340b0781e41c000d481c4c10455241c020821056849107417034213010034156a24041d2140c01a8851320400e41c05980c0c07503808200c420702c04500030400400007005500c1d250011030740d0340c2c00042c8191000c0744101011030080d00d80011030700d0b11048120303480c8189075620781da210229005007c1d0484c050303845081d42606a6610700600c0041c19455400046a00c2c0144a952401041050242c020f8020a00080150747c0c04541c0c1c200c00d107405c0e244941c0d950b545100d0075002c1c01c0202d08899100c040031100022990b070100081046030b008031074a41c07543c040c1b200136a4507480241d800400100d400354040120394010701c80300342e000ca4402c25140c00c083d9020082081c1d040104030100000c0c3c0d4840c100540c40c02089240b28a904d00825030400518040b40441d0900000e071 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 416060944 1250 416059694 416059697
    0xa08130e070e061c0c080a0c09080d0f050706020711150310030816021908070611150727170d12050411030718110f0901120b15120112030f 61
    0xc2c807440000c855032000d41c1004c40d642810000c80303803c6070b002401803006603901c0c1489410151355049440c031400c00034081c0c6100320041c2c6104041d0690580f0006400b09620085c490140100000701790284050b29159000304540048500020100409660f80700c402001e00503003441030122440b0f040360050140c0381e0003403404d9903030201411040070804210704001e52101d421641c014082104403c50303021510080c0407540a183c40e0f2409640b009284400502c40d0f40c03042e0480c404015031200180e400c08a42c0c105140f40b8403104464028080c0b0301c01c052035000319601010000561419030081d05a4003040191122154a075030040c261400c59009010490300d42e0085070510803108200d41d900c0c1c00040486504d16035900d5845d50180c48034850518242c07911010242e0106c02c181116100c042c00440d50780b420185100541e205100e91001c4d5030420350300d040c0074600c0d8507a07070b410f103d601036080f40c21038690a0300c6c5085149808143c00056040c000107a0400001744c21441804000703405 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 416062194 1250 416060944 416060947
    0x30221160305040b0c010b03060a0b100e0a05090a1b0219020105091809060405012906130308032802070209070c14010603030f0315150c050106080a08130e070e06 71
    0x1241002c80b501c0c001c0713401c50364a00300300082d6096031010551001c80d00a0090302074443e10b64a60000038104c0d480f00c00c801d5003110101d4040c1e00498450f4400d808091402005400025203a8010441c0d03481d0440c5c2c1c0064003952001d05204c100703801c0070407444d010110301c0106482416110000442c000c1600002d05001380880c6002c0260340c2c600d10861484804500014180f0f85000d14a65031138040c2c40640380755103000200058855034400450445500304100c0f240741000c4001d1080c0345d4040c0c410100702400e841c8010001980c0000194003600d003014211903a00c0300e8420807113a0000b440f24082045104100000040c0c0b9500c00450740700710ba9090111118041d400c004000c0010910a02c01c00c2d40b1b0002d0110130540c105090000403105a03404010b070220b0201c0710303015401d4070700400c40254003444520075030b148214a5803030350a120703100104515554040c05443c0ca080382c1002c0710840c0000c118051004440d00c402c1006050101c51040c0d181413032900038054017050741d041e0340100c0c1e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 416063444 1250 416062194 416062237
    0x220503011b120f0e03070f030f09080c0105030a0b090702010b131e020a050403050709050711030a0c02060c07080105150111120304112805040c09030201080f09070b030c030103030221 80
    0x6a0068130714014810550350788501c00d1030454807850341c803182100850403400c01c1100b280d00c00c24548095508110081c4000c4049100558003074100800400b1500e40369038900c1c0142e2100100c01d03000350b800d038001040038074a1404000204100144401c003161811146207041c0003280600c88440c04484801640d805220f4000c0350548290740028205124603500040d03050a03550086120741182e0b5a403101d000e036948255500c074400c1c07248200009000c510000007500d064001070191621200032144070903510f0000e02e0070b607941294811010502c0b0100b49200f960815002e940d01d50188028241074500f2044019003408041c0c0064081c0c5d02c04459454203880c0d40542481c00100700d00c0000c0340400c1c003a900070b1703024924012640100e080c64101950396000d962501c00750380d0305071038022580e550701c421540d20241c0140400000d1180c4400000c40e40c3c01840214000e41910040a5036503045040103032415210b4100018502c941001400500d4041d1081e21445103000480e44035141 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 416064694 1250 416063444 416063471
    0x5040e060621160f050607050604020f130c091403160621050c030901060519060302180901060c050f15010b2206121b0509090408220503011b12 63
    0x301d44502c10b0328030b00c200c03d0707001112000010402d0459400e004003240c0940c481c02840094002c0e034a008020b1b5000e01701040051619096aa440e9030000c0c1960b140308540c003a1840542e4402c50010021a000e020306110700c01c800740740941c4a80041d0b000b0080601a4984940c0e00c003083c2c4110340c00c01a148000c036810700006084e28400c070641060500079810410700100055105071050b0a8a42c81c0840010f0507042082c800040c44a80034800d00d1401d24064083e4003950080200405c41074404400340f4059442c2600b040c00b030555903542e8107403000545002d62074403030030400004850780300c081030410941d40c10b030001d81500c01c00082c0e07684440700440044d640c601c008101044056103140c001c564964001c01d06850a210003105104000c034696004440200403082a070002d602049004080e00303054030030607081840f80c810b4500d0a564403800e50107018111107081c00c8005510000c00c020b10b401d0007101810034100014036078548129002922a0002c0d4401c04903036034035000945000d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 416065944 1250 416064694 416064739
    0x6050a111e0712030608060a140114010908030408010203010518090307030f200d0f0305131101090f0303080a0e03211b072a0b04050d06110c1605040e0606 68
    0x81d448228083c0400c807060000d40a4401400345100c507201d07520008038890440d0142a80f91200124090101e0b420004160100544c41e000b9a043c8140701400190014041004100034010b0000041c1c40f94144010458207038001514102520140010310034003640c04400c0390485035150510700302100c3c400d070303041e5000800c000c2902c044090b100400d80b1031a00201e0b01d8100f440a66880621400d07171408268101d030b4050301c441d182000500d07094070000d44604d0040003449414100b8403e03040d03403042031400761562900b0440000e0a40d00c2031200c2240031b030080c558200e0480020310300f420729024104001c0c1491002801c500c15440001c140f9000300c01da9000c958412000c07265a40381020300708000030715005112829000308007041c4403e8410707071040c00f100395002c0c01e860b5454107150000b089044950301c0000c1e107105668426030a01070401c1001012a492400068503e40d6024a42c20080c800994481030040d4103003905040c1c2801c0105100303602050488603400c0c101284448000304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 416067194 1250 416065944 416065957
    0x12090a08010504120807020a0c0b07171b15090d082511241b13060f03050603011503140a020d0308011401090302061206030c040c050706050a111e 64
    0x5035460403040c041400040130042e4499000d544640c0c016450b84c801c220b98a00c60b4083c05080c07061680801d0100301d91503002400400d00915480c442d00544c502001403c1d84080e11003c441c8ea114090b10044481c2407084144000880580490034500481b82d56140d020050085042110020008031500040391444041950003c074010710f0051100000e002d4031140200c40b030491056154404e200120060100c14034a10b01e407441180340c0382c40348542554958460b56050703020382031100c00000e60113101804000c2c11150384003a194821a0340c083d048500180001e4000d905000030032044000b02104041220f0b40242c40032090b86018143d1418000ea00c3ea0096000304a03141403c249a4045502c6040e591603101c50584c4014003001901c031600c02d031100035084002400014451100302c0351041d4403d01c05400c0e610f1070307200280020211101d112154011402c00f04903082030003194070900e51b2000003850104003640c000076030358103240100c52801e011602003007000d40c4003194107401c2e12207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 416068444 1250 416067194 416067209
    0x170a03090b0c0a08210c090d080a0c050114010905092a120102030a091a0919061409060a0c02010510030602160c03080403020103050f060d1e05060412020106120512090a 74
    0x115901d0494a908800300400299555030703032128042146d03100020101d0b1000800100f1030448004140e40e8110541c001a03041400d02c500d1035101d2000c100c0a004981c2442460250340381d0b19030422108008960010788074000d0342e48078001c4428981064900001d1400c5003451040070329100c1c00000d85010100011200c81e0350002c414420f006035560400007c051090003080e48031510607461701001e460403900500c3d26404011402c0c0e07040c908111190013280140d401046564406203c0c81d01c01d83e00382c8082c00d480c3e02440170090340801034410f0074000c5a00744020300807070811a42410202901e804090925640000c0700f0b1610307140a01d82c801d9195102ca4101e40c250368130306182c01c0980052209034042410000050154021118003a10401000b044021240155115981e80b403541c51203082c002c0311b0919416006c0381c1e04200c81d03446248982c042d4800c40d0316402e402400cad6807141c5c0c4a9810000c82c401d0200002d107010904403816841c0c0c054243c1c441940ba400200070707039641d038001c68 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 416069694 1250 416068444 416068447
    0x109030f05030a33060f0c03030b060f03040b04021f08040209071b0c140d080d0f060504020c03030105041b08190902040c050c060601111005040204020f1201170a03090b0c0a08 77
    0x40000c2ca030314200840c010541c03850540760369a908050f90003020740921b44002920608803040000e00a5000708014a005800b050030b200b000a004003090f07005071010381c0d0418890b070400003185880d5441580c0fa004031201d403d0170070032054020b4048500940000c0c8119a083c0001e004540f00f0b015070360b4141d180c160074868103c0f807800c0c160100d4280b0701400003104288043d0401e00c2c10403100d000c600075882141e2030314001102012800501b911500194029102d03200003c9a41c2c0d9070000d4101088100301841da00d5152900f000200c861030800c3c80c80f025030464a5214281d0080202948115800603041071244050020001001c8480c00207601038900800340303001942c481c01412201440c0f02c04c842039501c1390001943c4203810041103070806c1e403211003031100c100c20075006180c1251000e030001d0300707200025000c00555005601d42d6590324504cd0700401c2440e43c00c1d500f0381380d08000780b00a0010303106d642d2801002442e80d802103030035403000018698032499040006141194000050b00e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 416070944 1250 416069694 416069741
    0x11030604140d050a0c140705030304090f0b041109091b070303020d051003052a0d08120c0310090c0e040e0f01060504060806042a0b03180109030f05030a 67
    0x1001d000c941e1a0000c25214204108000034058011244044030070385540e078040780e080d03a0b02e00c0c105c1001001220540142140016280c4082015101502e56040040784841e0741080d80d0086401b000701e80d51190f41480400701805075080c1c11580c9014003a00c514000d0b5503a1511400754110705080010440000105c03803040c140e155010303100c0305904410a00644d02d4034802c44040709400e001c050304a400000d442c1542c08145403210b400b1070040100b045e180d18107440092080c030117804c0c05940307103e00002c5800d10301c83d10110042e4001d207180503280c01c5040ca00303031f03038084c11030703280032341c100d6284e40c0d074007071202540074080c411800000207005100004205040544884600d2001c0c0140d40c00d00c0c8020900d4946801024180d450900007090a55100d40340c02c40b503046401c40c0e00701c0341076101032200112040508010040d2001c040071a9603400c192240300c10a0f00070f00d45112041e454818680c0000383d2100040721000d00700e10304143c0300d41399600c40000502014400901d0742c000d801d00c1c0e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 416072194 1250 416070944 416070953
    0x16020106050d06090212120304030f020a02010f20010204030f020909191203020d020d0c030c02191203111306020d03020906120c220311061207080a140a1d03091c11030604 75
    0x11031227203109a6484100400106041e640c0e0004807400a0119401a140c41000c0d07110700740a94800083da05190500c4010148050881e40260030a0f40c40810a8407250113508003440610380082010b001080a003c400c680182078099104005100c140034a040c01c086d42d11a07015501c581c13980c148110760307580040100d40020521010b0008c0424100400e40303801500224051384098000710640c00398845666036000d480c000a05a001856540d034066440b03001c015001d070000c0200d044109001606010b400703031400e91c8516240003058010401d02e0b02c5521000284d4401054680f031254407510380d5019011035000d10000c004440c010506c1c1300e40850310409110048900404001029950050034071071184100e0312440f00c2e145505000c107446a20030007040381c2c09056004000b5903600e06c5c41e5000340460081e070313510100c140c64903020505003c41e100c0070f1055596220081d881e002030800490350590380d110f210504c4080f401c00c4403080c010081e40410380b12100030107580e09442c0a251 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 416073444 1250 416072194 416072197
    0x4051c0501050f01060512040c030c06080906090c01050906132102011e2c030102130801180213020702060c03040b0c0609010c0e0907021e030316020106050d0609021212 74
    0x141a40d8540c00c200104841c6081e218001d8103a681c02d03034a651500036055880b0010040290084604040214000000c28940d542c2e03000903024a5449039283d0808002440c03130a0405810040301f45c014103a80704550380c120007225481c00042e00c001e0b490320072081c120640090142d00c804002c4540110044928001c8421010407901c00d807503e408540f40050348524905030b0710288000b180c6000007034180b22441307031a00100900003001c601e0b00317001d441c8003082c2660010b008001945c0707040362381070001e11402c0c0a0352224008070455111010b58503000900510368000c0c10083c1e20744c0c00100802036454480807540c080c0141c104890b0b0342c03a80c41030340c101140d011100c5541140500b0004c01d14240303040c091003040d40103c0d591140c1c62842903041281d000c4011b8400820341c403035268081e0b000956000c40d01c403200800300155031a807802058900400810320002d00c21039251072000e010954030400f8560030507402c06c40009459241d440464413500c0b01400795011845440981d0601c03060000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 416074694 1250 416073444 416073499
    0x81509010f080f120421050313090c051204080a090f0e0f2202040228020601030332090301090209090102030106030b090c1603020115030309050901150f0e060405 71
    0x1103a1035200c3e42c00d2007a86032112510205001d6130104410000070b61000312501c5414045e2600c000c030165507070303070700c1e80355501c4142e000d040303140805c404100c1080c043c480e81741c400b1060305200c3d251400d0904000100c0c4070051000b00310410109000d501c8034402c1e2040e0b40074003550115002219264079401d4082d16007265600c003000825800521781300031404400c4003401107402c02611054581d403c0102035088805d000306070f0001004400c0451003c1c0c401c00b05441000e401500140d411410002c1801c0180303034000f40c4814010210f490705202e80300718440d2400c00c520220303407103004c1e440c002400350000e01d0029522203051810701c8024034040d80114100c8040e500c0401c00031040d5014007160000c2116002640e0100740010b00035041d04150b250400351203440005061110045400c3c240e9078160000d40004003803040c1480a400c10040c8940501410306040001212103032004208a000d600d104c0100440f119420382192a01000e03a000b6020041550120b1140b03a0000c426225880 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 416075944 1250 416074694 416074709
    0xb0a1d130c271b09030f020609060d0c020d030e030904090f0f140d030902060a0e15030c07061112070c0804031a0702150609150307150305070906030e0c01081509010f 73
    0x5040040450300341048500c40f07a4a4a02189145d5242c1d540c98001070f070400c0c2c2c0c00090401201c0c2866072028014100e01c41480f00015130311407200d4000f45040960fa01150515152249401c050034000060300c02501045901144191041c688a141c01c00d4010740201000d0040c00380700d080280300c40403040100c0d100d804680b880030101748100e098468000d0087c7d00010100003510f0700c0d5109009440c01d242000e0141910001c055000d203900780e10448411020110201c0c1202c20030a0714060b26000d80e0400c240d450030440c600180210045010341203905001003640c1c0f6004200c01c03842a0790085802c0b504940d03810314079a04240c1da03141d00f00e86010040c00707151040c0d82c8403141a0f91550107240c1c040c0c21a180c0d80e079032221100b0000300e0100801e505100c0c0c00c000061042b9031008200c40da81c416a0042060305020070040d1041c4001d400c400281800d02c65810714080300005c900c5000c072070074070b000b041e240c0310784a2101c443c105c7c1002d003a4005a02d10008120585080000d40440742d44 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 416077194 1250 416075944 416075951
    0xf0e01141308030106050c0c030a05010e01111903020702270615070c05101205090c0f0a0602030706050408040302120f06070504082a03100b0a1d130c27 67
    0x400100145461104200510b14082800144110b0b40f02e03034040d14100340032104981403c101d01001a03e411040c950403200c1e03a46448200846200038001c42420ba000c0c0c1c07072030505060041000741e13200402240500304060b808281a019990b4000c94980c41a01c202e04800b5041100f007503001a0200854441340902030508429200c401d80c10225410329800029200045007400c04101482e081c42c492403040000c0c082806507810198070403140260003501c01860303041500424054545c0e9007e050601c0b030440c4040c10024650040225180d07164000c10000d216922403804040038020740d04080e400454290104903240800645040e0040040b01201ca2960310320700100c441d4819402180e5040d0004088000700b2070f0350301400c42081205034145108140500302092130f0846800c008180c1503169140a03005d03050010311000541501408528201d8080e00345104880e80986040760410110303011406000f240348010f0003400c5203d002c048036280c140710802403504105d4040010f1880d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 416078444 1250 416077194 416077201
    0x409230a090215070f030809251e0b0a0c0303140f0601110c0114031b0f030a060602010507050f0d1d152d07110102070f03030e0714130f0e0114 63
    0x10810360300f80c4c90303001c41400b4041030380759011560503030081c104180031701c240c0510121003490300c4c0c0d0040709201045c1c4008038580c5080039000d200140414145100c44541c0818840c04000c0c0048070001e0f00c581c182a0b003001140d2504500074443c140510b80300c00700304e609000d00031418601c8640921070903601c082410b5141035440c0d40b1030700042050350200d90b040c08a50f0410341b01c074014560208d480c1081404d8900f8181e001405a802202d49401c81c01c800020084411840c0c40341801802140c40200081d00e00341d00040c1441c0f2460301d60541c04400800c62501c201c0c91038004030f01c03400f142c0303211105940104010315514007144d910052402c0704000000d1341d02c0307000003070108014041220b40e15880ca0540b40310a0248014000404000030100038180010090005180941c4504109403040680381001070880d4000340c42c207072483c0c0096a04102a2801594407c0d040008990521581040e0410720b8001c00030f5a1032001c0301c90a00d48a071000c210194042c21011520010203c520355 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 416079694 1250 416078444 416078479
    0x2304090c0e0924060313030906022e1d030a1215150c060e030316030c120b03010207020a030c15080424060302060c0703060b01030903050409230a0902 66
    0x24420401c160428212000540c2c0396090b0285100410280e041c0201c1d038002c1140412101d50040b900004012182001c06007003690005041c001000a44041c2800f4441720060440800c50070100f0340c0701c20404000400440341503404001480035040c88419004d11503e9030742c2e1070741c2080842030003003105102c800410b50118080e014045440c941c009000f1424003e0102c89040c24030181c50810440c0060600055514892a09010b13507420045d034036460443c004070340318040302d541c01d004c05081240300e40440c0d07002050300000700180180030440310f91950203c1d00900905601950140580308d0002c203011112075280b06548446055001d41d0342003c10907111f44030156370080c624003000c0c801b4151030b220030564401c4480080d07404a40da03596500014015002501c2c8954181c121342c1c0304100f00a038074412181c002c9000e0805001700556524003600d01d00485c45112159a21590b0612405601c0003980e04040c1065a8254150030311800c120018003110400720b0150402240261500f13 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 416080944 1250 416079694 416079707
    0xd051503070927060b030a06020d18050d0c1515031203060605120402130207080d0b19030204050a14070c110108040213020a090509130203010615020607050a2304090c 73
    0x225448140f12404460803280114402a0310b00b00ba103a20360b48a050a00c0e60317400744900c105c0c840c0100409038a81d2500340302501140d00e030550b0400001ca03040d41034030000d000800c080c0500303401818492900c202c241000c000d00d0b01030900c141e0f60203240001100d9485100207000d0240c9000307031070f40400c20102d210254100e50300c85c000c05010500a00c102d0b0710b0200391003003207070344188007030100b292045011030a0301c143d8002d80c41c05c44400f4800701c2c84801b80c000d9031090403040742003105c03030030f40d040c840485042e00c2c04414000030303001710344501c0001d00b40c021580007008104d1032025426618940140004c0101e802074104468007031001440b000150300c1440e42c54042c0f0b4000307140c40c0c01d194880804400943c440340c10241408064200050160355451307c603441007121410000340c0c8a001d00c1050300b11401a005036101582c206413802915500040b25035000505003021680c032244110282d69090401417200c05200004880c030b03001000342805041101c040b03000038054810401400c0e20790 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 416082194 1250 416080944 416080961
    0xa0506180319020705150405040e060613180b0705071b060917010b1011070b0c1203070c122a050c09070909020f030106080c0705061b0d0515030709 65
    0xc1d4018482c1c84542011400320304400c480d14011141542e50343e802088032020088005031407044046403c0060b4209030207000504d044010290005280c02400241070044071000e4018141d680c07400e6231034082c1c548083d008015000803820b02d00f841c044070028150f500c100f6003114080340c030b00d01d000342e100c200c488848140e170701c1d80c1c841c1c01640d400c0039298000002d1030014583c0c40c3d0348407000c0310026214010700300024912941d40d90403205a80d00c0140c0362002e1640914500d81c410001d10004420201e01d03014082443e2203804d641c0d403602c0740c04640d040030030040234281580c84610240f20f9038210100150406038a20101d450b03040064201789a03039603110020b411500484142200761920000b442d41c000980e0415200068451a061040340c10200f4501c0341d0031400401413245940003003200d40e1043c40201d2480ca881e14594900384c488a02410158461390491011081110700d202925807408405004000303034500b401e41f1804907400511158028025010049910310741402800503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 416083444 1250 416082194 416082241
    0x3020d062013150311120105040e0307020102030f13050a092a0519030e030f0702120606011403250e1206011d0a020d11040e070305060f01050a200a0506 67
    0x541c43d2400c0d251441c80340c484210142095524500b011100b03001d00040c01d1240a1300030440da05605240a2000300c85040c8881055540144445401070381d0020455034a16140f920340da440e071000c01042010074625400c02e65000382d0055021610504541c8248156404500e041d03c40030584e0403503032000c001e1002d02d48002101001180313810081c2100036840d516a500d400180780488515250441d0030111750200007800000781c0006600c0e010880300d8164200c0c5010780300c20704000002074200b01d1003410501022102100040c402c050006104041c45001c031200d1070603010030403000f813568082c5800c9501c80c641030003c101f0651800106035040e00e007000702407180c010704111680c0341c0e4500108a0600e194080040002c0841540101c040002116060503252800e11880c8062141c00030112400c0500c1c2404009d00c0e40d40300c0e5a1101001030a0070160365955115070308a800700c0480c07000c05582203421800060b10107002800090042c00f43c0d0603204e4070384814812402c8110300b4208082c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 416084694 1250 416083444 416083477
    0x3190318061409030a05011d060901110304020d0f050106030605011701050f070e0d020a420305060f04061401120b030601150504230a0602010b010807030c0903020d0620 74
    0x42c081d05a00000c04100c10002c088076080c600c242e4030b0500307613200e240801c500300030343d0407804c14440f004010f481d810010340d40c028070500382145101480740c0030050021f442500d402c24100c0510503521600003c094101c07000307002040d107071b04040303018090a02c40e13480503060038984c1c40c0350988188100ca001c0d540403407180465844002085955a1180800b961b001302c88100c036800594900c40030100030640e04e00030000702203510b11040071030300040c1802c10700345006d0600d41c25942c441c0501d400600f03007241000180c544030540462007540105050755002440d000000c00d030401400c00e081c0c03020f0300903070329499601084007611003036541001a40d40c159201c3c0c001480880e4080c0003070f0711051042c1c0381c1603050580d94880140d260320800048400d0a03182c0404102a041c0801c1141c0603044900081c000c0202d2200001c103c210300500c54402c25617104174400c0f80a200c3e002d81c000854000b4092811558542403000041612128503a0080684040b1104841600c0207440c508902c000102 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 416085944 1250 416084694 416084717
    0x41b0f14090f0612071d04110907023a1709160e07020f0607030e120319110405030d12140405070306271209060504150c060b0319031806 60
    0x1e00222002138030a03005030785000c44e0340050f104c007050100b42c0e002c03182400303414181807500c1d42600d0785843d03c2c003c140303080c204400c49400050300100300f418107200e440340340032138400c0c5010400704c42e41a6510085086030804803a0b070014551780440e540105540c080e4481c03203122680d5046080c0d43c42211a8022010030600303084100080d40500180107603980707059841d18450034210300b11010b5000c2540d9440c1208030742c10400c0814440c0d03881e00d10907443c6081c0840c0e501902200d450702007102d02d4548400700d8600342d1401c15107008260240031203e665500c480c0290250003a00b00c1c00c03a1a61805001e8516018050b00d41405540c12a001c0c1c084141980c07038480103481c824020043d4043c5c0c00c14490002c104942c0b22216450054005101550101400525540c00c0ea03000c034041250a1200780701e1445440414403509145081c00124070249207460005421035900d015494000d03040114100f000042034000105c1c0700740e450305148001100d0030300c0b03100c0c140d0144600141010445 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 416087194 1250 416085944 416085949
    0x602011b0315050d080705060105180f100308040b040e09010614190321030b03060403020616170106050a09150206010506070303090b091e030c0d08041b0f14090f06 72
    0x4540508115a03880040781e143c90225148005242d01120340c2000001c400003445000d000b580d01600088810300c0c1700713410300c0c040d038030a008000c0c001c1c8480c50030603408501d03840380360a0910000c0d503001084540b030790350300c1d04001400d0300319200d000380302040d000000341000010b219090541d1400b405421425040000740010103864601d60f400c200711804020002c90207181e025144103829003111340d107003c20000c00a080c0e80d10724100c28020751084050000194005c10210b030301c4500103a0881e25000240c000b00c40740c00051001002d003282c00c2002060b06588030700103044070003481e1607070a003403076880c0201c892488100701c528005802580060100e494403200414245001c0d1a020400710445c1d101c0340c000d00025580000c0f180d2000b510f180b21810300d040344083c40c40c840f601035400c10010b402070039120388101c11000204020000040c0c00c11462080b0381560903180c0e151481c100341c8a0b0041408102940a4100c000702451008401441c102c500944543d211a0100040e03848440a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 416088444 1250 416087194 416087201
    0xc1302030403090801090503041706071d031f1d0303010605030103060203060607120201091e110d14070905091515010c02041b080a0509190b1e0108160602011b03 71
    0x42101000a014000201da00e024040d46c1c0354a07000308007a42d82d40c1d2402140302030318603000d50488407540241003085070310f1703030402607080744a8202e030000d04c03e14002200007400c01e60f0b0b01040811a086040041c0c0c68085240c0c04808400780713100100b8100300b43c8003030441d03a0713000910400000420070401840012200d4002d1504448081c120504124195640d6044a001000f003440141c1d5943c141e50140708540041c0d0303103400c4141701000700e000c030030b40c4801c01d0504da10385009004440b14030b405070402c5600c580030b0740507028420644d211503031103c5070320b4050030007078500c403440f88101087c091086c150f50008600504c071840030300b40f408104900540b81c540010500f640d200f0390340d070081c2102429450302c05174405020783d11002c080c13510b10b4a2004880010340f10003101e40c00740d618031001e207002c827601440190f0441079880031079440420305a2040e41d0f03103845100d0241c1000001400241c0090040464444288008096030b00c07564102e00300c826000d840c80007240d40703614a51aaa00950 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 416089694 1250 416088444 416088451
    0x105190c05190b040c0506040501050406030e0c04020301082a060a0f0c020301020307020f06010b0f0304031404090f0614030d0f1b120f1205070905090a0f14090f0c130203 75
    0x2035540340802c0010119072100c1080c401d650b80901d42c0d04100401c603410245101402c01103902c1400d01d8100f000003403281c000c5002d02018141c0d540308040070740504200300c0414002c014000e40d602e41c2c540c10601e0b11081c50030106030a0011114030300b0304a803029403e40c500c0c82c4028000c0d40c144460468125030880e05176000b40c0074010300c4111540980c50038001548105401d80042c500c051140e81181d150201c140c6c4a4091240d0601c49284011010b8084a4005408d03241c00c007c1342c004003134034113100c0c41a030b806441c0080c0343c02205001f445940c0c0110044486140d4805088080b28062680703540100c068000042ca071001031100060043e00c003031911030245080b803040c0300702c281d0f0303110345c070b0311210b031ba4038011600c08002c008026074029110f14040f007282c0c0341405a401c260901610302440d6005941c450560280000c001720400c0d0301c068007103607803040140810071010380c015041407003d40e10f20005006040c0071072456040010344a030083c402400c121081c105030b0200000940000c0d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 416090944 1250 416089694 416089703
    0x5130c200601140a0b0f0306060f0c0c0f040905060406110f030a05060a08070b04051e0904060b120a0b010b03070c051f0f050603030d090809060f030103050106050105190c 75
    0x8005901840340402012690303415918000c02081d410005581c02c0e00ba20445607a01c1295061418005942000292008641d0a16105840c0d032502800910709010f40c8a41523026200458400d550003400074012492078010744901240c3c915410070321017584c07294800035200e503000c20040703000185c090b40140c8072800c103000000e00701440d824039602198429510454456150400c0c4803841c81e04940110050880340c0007001d11074581404482580900d11941c0e1044601490026907902000116414000000c1400001345040d1a154004040d00c500d41402500d03441d441c21510000001c480300c1046d0044884410380c0e203807841e802c009620080090041003140d60741c0e1000518200000f080c070884030140038659001d454801070449107420b000341a039038100410301c103a07501c002c021125981d40e41000803d47c00424146030f001803040c012080d4101c00000364104500b6007505c0558141c034403400081c8030f11035491004480c0750003001d4502140e0301100019a090a014800c01032446104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 416092194 1250 416090944 416090957
    0x1a01110d11031c021207030e071502070b04060807030e0c01210f02070f0303050603010203040b1906032a09020a05040519120b04052b030f0605040606050a02061005130c 74
    0x1120418005014101d100354000b40c01094401c03080b4001103c17103500c00494901008444100708580d0385c6c8010510500003071600b0340040400751807080c400700010704107900c1c40c10741da41d5959a008049a0381100c0d05000a4a002031208180e000841d00500f103401c1603640c1c1c0f414000000c81e8000c011420b8043d00a003541d145241c4030511050b0000d8001c441c001e801c110021401414040c054a40042c4a00d200764810002c100000e0020810303590072140e91041ea180010780484400014005600b01808000c040102c2a008040740b50140c010002e1804000701a40d5490b5100d00036402100245004904184424000c6082040452544000314010100c00c80c1d99002ca0042c0100043c209890726003040c000c01c4140481000410070340c03402c564940e071211452030303c510141c000c03001c0748030f04045d152005004c2040091700490060a0010070400c200d66542c640600590300101082015004050000d51041c5e44101140c2c11500003410030801d98040d00100401800b1410500003800382 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 416093444 1250 416092194 416092207
    0x111071a09030d0c1505060616020303070c08012013092309030a091401020c120703240510080601030204020a090e2404230406110d1a01110d1103 64
    0xa003041140032a05158031101c020b07500754103118019010385c1803803041c0141804140021615030000711a005030000445100e80038082c40083d00b9031065101c0a0048010301c80082005031065000000200a0035010258084841d110306082c0c0500100540c0d20490408200203006032a0014a00000b0b441c0c80f03500e000380d0344200e0407030040b010380b0090380c0e680c4003040410a1a4000f151900900405c0511014502001c00000d6540000d24000d60098900703109026024104000d00d02c055540b207801c1d08580031028502494035510040c0c0514030038204000b0603004000c101441007903d400300043c117100e81c2103409000c00b0b5401980c01200b00040c8d01000512002c1c1007120301c0c05000d81415a0b80805d50813a55400c010341041481ca02c1103103020080b040c035054404480340810b02400546a15603180c3c10030741700501d442507a0307a42069000841101310030b89544083e0046100c0c442c08120114034500440382d01c560812044110f0348003045985086000707022481c440c80d813201c100e80c87c014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 416094694 1250 416093444 416093449
    0x40b031c12050a02070b2e12020f0901060f230a050c0106060305010503100902030703210f090b0f0c07150c0b0a02070c0302091e1003060b0111071a09 66
    0x24220516040000d040104100d80c1600038020300e504a02030f030030190b003003200c151508100420003412054040700d01d080c000462070341c880100114004882c00146269035640080c0c040030050381c7d002c82c0314000d580f0807020545404072f2120b0696070203075a042d43c0104039010545042030100301c9540400800403d816024000c407000f03080094446c2c3d520354840301181c41d0a82990b00c990828030a16041000600c002c0d240000c4160340201503403408140042c1d40d0011905101107074001901d031000c1c0c8100a40c0030001c031030011400c102d16036039020038002494001c47d0340d044540103004044034200100e2004a070300501801c0e01d69240000d030340b5110361390540c0c1000d29000300290000702e0900c0400105004005e0f0401c1c1c0c0c070080030030b0103501d031107403940e40d1044100850100a12494040d40070610041c0b404090814042c0d1a0b0500701f4103003481d06007640040514442120210304103a141104d6520804400b507002103d03000400c42241005165494140d02c140c5040000e0028080c090312603 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 416095944 1250 416094694 416094733
    0x130b0c0f0a0e090603010e0606040c09080d031508030702010c080304030e0a140103150e0121051902120a030e09070e21070b07120507020f12011a03010c020c040b03 72
    0x81c00754903014180c40b0b0080501c08009001044644a0303454030f00000c10300c49020409660000b0111000a0415440b40080e10684625080414244a2081d00718800c0f50980d00444180c0016109107100a581d107003916601e102e4840e00a0015043e4543c120019051501a580203803182c10000c40503202c200200d085c2401543c8a00c0f05090b07140080700055030580f00305040c200341f00c4040a03070981031410406088506106039110504140d40840c0120340c0520709403030141d8810241c845d108024291488610300101c1d06921a080c0e441c0e21200300d403000500c101003154540c07541ca01045078a0304002020a00510003001c0c070511815101040d690340c080144680801248006850132580c82249400e80c90703002400311090800062000c11071044616080b00194035009030742e83d14030b2022070201040040400c2d0481089401c503449180103402c607205c100e50301140541041c40e240b04160907035070000c9555002d42c200703d2040c03407a400d01b60000750803090701508685240140d855000b401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 416097194 1250 416095944 416095957
    0x2409040804051c030e010504060215070323070315060c020f0a05030f060f06010e03060c070804090e0a060c023424090b19110109170909010b03130b0c0f 67
    0x402410b41102000c02d60400c2030076074545e20a20b040741c1414100a4080d5803410703001c107881c43c5424440009441c0301d11a070010b030960700500f10b510503040e140301e4041000e0f90084c0c580301c0110b410110107000d010601c10200086600580d15030600625680903c400b41e81201456500600c100e18041500d4600700070310b4400c0303c2f1500080c00c0c545402030003d0586d01000d042141040b09041c0780000e030b0b43e8001411500400004a00ba0f030b03070049031030025080c3c07240c3e07401002c9403402c1001d140c40c140c02c082442410b1900451040c4103903c00060202c1e199a0805070f400d1140e41d440d050380010140191103c0084001c0c104444115a00e620341e02c40c50214262500c0668458600600030443c0c0c44032a0b0002032824004403401c125103548482d01c13180b880680e5004100800000707016440e025040721107145c1e08440e4440d0407030f140178640c2c0d04030303800580258082c10282d80001101e954080881e48500300c44401c2d80c09807510b6076600000440c01134550a80304006016007441b8078240001400c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 416098444 1250 416097194 416097229
    0xc06051302011b05120c010b090403050306040509070513020c070f1e08060402010503040303180f0b09010c14041208120109060f0602011b200604060b09240904080405 73
    0x122003003035100052421100076200150180074811400015000150529114004144180d11101015059801400c1c2ca141f65a03004911105000034990810015401024144c80c20310a540d60305d0005c13940c883c0d1522a0b01c2c2c00c0700b400140785103130a49580c05481c01c071044400790385a1560303503840111060130541180135007030f500e82c8080c1d041c103201007007100041a01102804580c42c181d00042c0090100500c0641459284d000204060305281104154180d018020b07000d28804c5042280742a14212248001c5619105a6228040c0074000c0d4082035a15400031610702400c08005a608107918501155141000d11080000070964071203140601400003001801602d0302000031481100d030350101c415a45001c1c0b030090703600f565149000010007541491544039001380030a040ca042c00c00a480d2b8680900b9091000300400d94003c1c8035608001c6411441d80c4d1100c0075036505200e00c0302d00542140600c00c60100550070880380703082c0d01ca4020103a4605181e40c42c004224940d0504c1207141 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 416099694 1250 416098444 416098471
    0x4090209012702030c0a2307060203040c05061b0129060a140d0b130204050f10110d17090c010f082815090203010f0b0c010f0c09030c060f0815010c0605 67
    0xc4070310f80c0301444d54240c1441c0d047e40d0f08000b8024050310003030f01c510b0780702034865600000040d00b88a51098448002d04014284035981c0d03171003212550201040c801141415403e0040d8881040c40c00782444c0c6980f1100d031074000e4040451030400c42e03d07501181c10759082c4103200a094106041c05800742c00c006031081e02c0031034002c0c0c1c000c040062015000303413413030080e41c411b00051141da1985006003801d54001d0350a800b402030030b20340998002c400e0b01800d00c2a0711884054a100a5126107148141c021611b5604082c0e02d0300340700140c54941c00300850340011810401c0ea442c0c14860541c2a800c29094406c0000c450703070200d00d9980320203800300d0031704207551548640000c5d0404401c0741c00c024401200c00310306650505004110398000361080b017030503070008102000040380030b43c010072211490700004c122180c0c1c0302c50040c00381c2d80070344001d5850000340c12000a40e50300441804035410300703950741d25015036118080a9035250841d40c44504100c00242c0c5071001562034410380780901107964141 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 416100944 1250 416099694 416099707
    0x50109020d140f060c03281503061109060313031403160e0a1a0703090b0c15070206040b070c050a050d1e0c0210081306050a0603030e04090209012702030c 68
    0x240e10f00f0071040d12000d1650f00000800560312003800c25a80c02040c51400001d110180700000310810481c0030800e07003054a002c81201c02545400c6c2c4820442c1c1c42410203008480342c1c1e6460f00c2c40c0b03006585101d50004c104000083c003801702d884000080c20700c0303414000102000303c200c1005903041207501c03141e9450a41e003184501d82c0c1104000314040c4048070301403007850400d0070142184081a20940e07003400c0128100040502440250340034181c80b81e0242e0302c514003046400e54034900b0f802d1a07a0034000d2100428a0640f010940e240b1982d00300100d0300258039403c2c411501e03015800421b40f03582c05560816030000d2014002d100c0d0b448205e64510398601c03c2c151840c0e9054864080f110140460300480000580322440d8401e043c81d40390078941501c0c0d43d0300c032000d0206850070000174601441c0c00c0402c11030302443c1c0d1040043c0c0f0700a985801c0066040d006200440d6602034001c1c0d885841c60004100e4101804009002c0700100c4100c0810007110303204060580e00305903060081501c011034903 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 416102194 1250 416100944 416100983
    0x120d050402040501080f15070203040519061803030c020f06160f11010c0308041b0807030302010203011409090318040b1003090506100e13020303040513021b0607140304050109020d 79
    0x1160701402001e0041c01006c062503070344a5456040b074800180704645800010b0380e0500a0041d1002424050550b02c2c000c5400c80c1c86000c1014107000304004100c1c00c007040c052440f44107480100b075a5058441c000032050940810406035007a071403459000c8020450030061628007000804614401c103010010194140303024098040c800103082c4c10030001050b8000840e41c42401d041d00300d50400c1c592100c40308000000c0c3c2010340583c112101c648200c0c1800020564154015030484003100400044614440d040103407002007503d07490760b598421b1048480702687d9035224140441c009200040386410030001c50780c0e0400341040f820100b0b030f441d10002d0901c60244619544007600071a000c1c609814001003907647c001c0940240803e2525614410454408100b25000381c5030040c003d0b120400c2c1b112800000c0c0d401180600a0016a44030b641c1d02c0c8440080c01c9406004c25880e2120b20340c40240c9010034641004001341c80d150b40380d950f11805070f00d4120354a85050b0090081c8190b601e00c0254 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 416103444 1250 416102194 416102201
    0xd060504050601061e050c070b070c03061a0105040915050901170c030102120f090f061006110f100b06040504090302150c07030f080612010606052106060318120d05040204 75
    0x110b6000c0c045881c0c9001c5c00803004840c1c0f0100c5031154207000ba100d25280b40c2171840c0074007542291a00110000d900c80c02d02554034411403c0701c1c41604244205c0c04e450b2408207080350760300c0c02a0301103042840103101c40e51454208100390f44c0030346c030b000d4030096036000019a40304080c0d018410741c0405d4140822100c605000c040c140010690095140c00301c3d1100c0c22240c0d140003021f04400142c0e40000c00c200140c103100000300301e41101e0480d2480c0c01e0240e01301044207040e119210108540342602030700c41034042900031450541c00f0182003814001c15005020b030a00c0c010140d4084820400441c3d0360341c07a80701d00c0701a24040d90040c0000080c5a503440c852580190010007015014480c05c0006030340401d00c006000060b1810010710788603c00032420f400e03a110b11000c560b50130002c001c129190702c035000d01045079080520004030545003404d698900300c19940c0d2500000e04000288404001490b040083c01c4131070f080307034003905040c048606250000042c0b002c8441e280e0003848190301e032902 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 416104694 1250 416103444 416103449
    0x110a120f0e180612010e151609031b03020607080c0c091909080f180a0b072604030f0501060302090f0708130201030213060203130b090a060c060b0d060504050601 71
    0x140802a11115000500c80c001c2290082c6400001c1900151003500c55076151114045880005e0150f05140d044442d1680705210305201d01207164000500b58517140c4040003083d00082c1c9030390420780d0640d280c4d05091a001e8808550820144400100589403030000704103007802000340903190710f140c000c3c42c1d0600050b8007456124514281c03e0244074030b0042412041c0307200d00107000450b075200d4541941c540c01112100c0250070004200c86413284190026225907030003c032005d03441c0d1600e4039182c110a000b0440068070072262603c41082c880c81007070b525114030300c40c002407a080540ea030b038401e01c51301013a00c01251642d469040400450400700c50098010040b500b81c42c0300c41c584068010142c120041c403212240090607048410b5900940c1111000140390f10400c107510303125503000e95a43d00903511030301c11030210310000450110f00800d803107207603c00600802c4c3d118038040c0210382080881d2016900340340e9540024010f541c641d241c0d40320f80c174801c0e080828a031500d81130290030507105a = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 416105944 1250 416104694 416104697
    0x106080f01061a090a090f0911010201050c04030b1503120c06070903020f041802040204090903021002071208180102030f01140114040504021c020f130906080303040f03110a120f 78
    0x81d005001d00007960411072080140070011a0304c0c1e2861400191010019a0040380e0540c680000710264500d190016216540610f40c04021309410307100480c00c0350b0342140d070010441024001880020348540103640c00c40700c0c184105c2060303845103000174240070600c0b0b84941501c2c0c001070f40c6900342400340441a0f01c03070120704240d8500bd14580100b440000440a0750f03211703d503160081301d000449041c0010308181c0150003191146e8494080d5070003862401c1080d400b61048407405075072107503540200c030441c5901c030752805201d040050040c0d03002000603160101c0801d08028148006c1000d2018500c074054a0005640395494007501c489807810740c02e0468108800e0020750030424001d001100c08071582039900581da2514070410012810034030040401d010300010b54500036464207000b40804803241803c08000654901c07885044640910910415400074000503001c1441103604010160081c104125100c81120550781030a00a40f02252180c1c2e80d07061450809900c100a04802e0809 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 416107194 1250 416105944 416105951
    0x10020c030a021b060307110f010c0f0e060405060703031d0d0201150626100e0a0f050c2d091816030204080a0210020312250c0b0a0c021606020106080f01 67
    0x3880f01040803803100030720032801c1c4140700341507503c0c4450411400c4040c2c030180c0008c01c00f200755408010440481110200b000420041070000c41c1e00e002d40454044540041c1041d141880d00d940a4014080b00718603020106000b4a102000030310501c40c40164804540c00022200710140034010410401d8010b00100641180280080d620245078982c0c0c0e031030001035070b074043d40e00e00c03182c0c000c0c4c5012030b00154490741036002400000140c0c0d402c00b04c9070158003034041c800356035000a2480e140c05502e040150ba640548c3c00000319441a0590918003807010044030b00d412080e03808119030038038150500501d60b0034241044103444401c0c546030b210348102e140a40c0381c00d1800c0305180c0d60b0181140c002c0d10483c800b10b80c001c0b0440c004c000701c802040c04092030540c07500c1c0c108081040c4440000307a070541044407003000980c3e18480c004800e01d4641c00700142d00700e6100c0840c05002008812014415886003120309520400c6005c2107000401079a40040341060400c203e603070805403103c4955000e41e06 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 416108444 1250 416107194 416107243
    0xe071715030714010e12120403050708072115060b0316020c030304050d08091f0f0311040f09020d060806090313050306040f02090717130b090d08060409030210020c030a02 75
    0x340003014114040c41100c2030034130201105a2181441f402c4500c40c03001d0b0300b002400004002c00890301804540302c0406903618649d035666000c08008120707080c403d4101c1d1a180c0c4500085054100300c40000001c00c001a2030790710707800800300644c0155000f036072100040540c00c100700d0741004400482d03030003640a1410030b03140a0100b103820302141001091910042106800f07600ca807007002d404508000d0000c170340100740100c06005100c0690b0301d03c000905000f6a8445510007804441c201e41640004500e4103180006120003908100900c2c0f40c25070701c4010000303070003004001c1f090003580b0380c030051643d41e085443c0da440c042d0781030340c4203d00a070410010400030232a214035240d51103070183d60441490b610030200701c070840340c01e01c1d070918203000e85402d11204103150a400912144105402101d548948034020b9440071041c1c26000056034034000283c1d68203180d0860403d0074172038012562080f24400810f81a600803810b080007542c000f1446041280d8104805142d408030072008840c00b29 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 416109694 1250 416108444 416108447
    0x6060503091e0613110a03031106100f06120f32040f0303020a05040f060507030f1e0e2d210604060506180a1e0c0203040e07171503071401 61
    0x200020000051041282d0012041c816405c1800c80c80180003000214469264a0040c2c6040090382e61854540709284c000f5a0b00501e02100c035056403e08624070340507910308101100d40c8219030390034802d00c8e9252001420910001d0142c07030b400b00740000144900706e4600c4400b1007013039a084540001a00c03a4003e10000c50945017090b0b41c160f400d4503000d40c0c1c8107034100701540c41d440b45911441d49007000000c0080c00340d500c14090401503110703640c0d0108040d5500f40460f02c1c480c031603d45140c40c0c1c0148403035885a502840201c042a00064024100500e85c07100010031207020b4000b107440e9a800d100d08101c58070b0940f001c49030b01c02145a088450030809100190b035040001c2000b0320302655880070031507540da11015070b107081c0d01c20161605546440d40d2088c025014002c02d175484240340440b803038903c1143d80952041442c2c154001d6060038500f003590644180003a0109003402b614100342d80c0c15200b10540315200f07120300c201c241c0061144006040c80c0c40e01c2603101105414082001b01002c1e03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 416110944 1250 416109694 416109703
    0x18060f06090d02040f0e070b0705120c2508100b12010213171e030703030b0a061407111002070e06041505040b03012405041505060a08070e0406060503091e 68
    0x100e40660b000078010b1000942040100300388106c1104074850448000341e00e045107001020064030400580741c542048a20f02d071050300942125080640044e61907001c07041c403c618408444c04c18110302e5000384c1c1e0318204c96081040741c501c0035580070b03120800b0030740d80d003824502c090000c41c825000711b00c0c210a01c1e42000000c10b86014001140c2c00c2100f4861050381c0c204694026160076010025040c041c807102c1598a03403140750304401007401e100340c0ca581403401c10058000c860940d2a074084190601130309142d10b501c034101c00c850310584855407080680b2205a146206012034000381503080c100160030b900000018120392080b410907039001e41c03400261151108a41c42075501150000c984c1e80064090301c504078201248401c40b541078101d841c1d014403c001150410782e0200480d0710814800300d4000568040c1e00d81001080003180030691007401c070f42c1d90122480c5000c1c0b8980403248005020f03500717968850f0002503404020f1044100d41404001c02c80042460082c4040323105100c1540c40c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 416112194 1250 416110944 416110969
    0x21b09100e0403170106170f010303020601060c02060d060b0901091403030703050c19031d040b0906190e01090c0306090b0315130f0b0f010b180f010e18060f0609 71
    0x41a401008101010b00135034182c044058581e100c03000035a1195001009600c0302c0f81c1e401c1440b40180081243d54130711128440c140da8259015100603801c20340d0079178102030002d400300c0e0008410010202403030704612a01c0c015260b07034907049a0b03d598032400100008120707002075074035000901121950f640d000044070081941410710355180d00d03c00f4280b900309800034805c02070455243c8114820903500800520020224044c0b4044c1807039a041408210b409415055802028440219000d80340140034086054491070a0f25119601d51b0301424040700d003a0f101001d11500d8840d0240116054042c44c00a840d00c204100688410301000a549003071500309007400e1103100703020a0b8865805038804071a60340040f200401280146070000500600b15080741003c1c100b400003060107030b2043c048030000401c0c81000d112044180b000c01403000c2c0c40403c101d06010515007814110b440e00101e21800200340307002e0304c0c103d00d8010140907a031900d64101500c500e40c10401207180d90740c7c04644061 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 416113444 1250 416112194 416112209
    0x10506010923120f010507020d050705060a02220303020a030813081905090a030c1a0f040e06011b05030d052511030708040312260a0c1e021b0910 64
    0x61022988082004000c0d030941003080c600401c1444e0304a030300150449802152254219008864600c0081f60280240d0f00020142e8000001003001010755030080c0c0910308010b9081c10441460320038580c916440c07948201e003d600100c2c0291706240d000b08499600110304100c10050107001c2d81c5000540c0704070502c00521248044106840e103100b941501c4150101501c983e241ca80c580c1041c1500c41c40510800b0174410208001e8040d600038142650300341c9400e4915141403600304995810380c88401041c4a040000343c00b580c9804c0044040c64078403c3e405017018656624880d1106801d464000340dc1c900f50700903400d003240c02c1e4407984010080c1510301d80391100a4540c00401c080c210311035a480601040c0740800c4c003105011844032407840340d01c1d443d20740070220741407098204540080700c04a00c1e42d0040300300004d014248035410407013404819107407070324000303100c88100c05110f01d09801d47d40c010b038400402c4a52000c00641118082c100803924a022440e04102d1402d410b030250040c1c85 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 416114694 1250 416113444 416113499
    0x201030f0b03072d0e07110c06042706050102100905010e101508010516030b04020d0e07050a08060f130f0807210c0506070518040f050103050105060109 67
    0x20121006901880e44094001e041d50340f003e599104115000c003041200c2c640442c14082c41016003140014260100d032540c01e9401100d981c0e24034240d0b10341150043d405107a004007400302c2205c0d564030008102400101143c41048802c81c0501605400114521900180303800d0b0705010316a00040e4909100e100000003150703000aa2900c18090841d0700e045041c1b0740f29181c0070b03c0c00c500c816008640035007220a0a000710f9a50b0f00c80f03203402c5c0d0b041950520070030780c40f01d8160905140319411402c0ea48030060300241c6040380c1e0580e141c08032031110441d50050340141c4018170491800106003001001240010201030038048000c651a840150061200040b11405a010007141618298155410030240e944856480c1040c001c03500403010f0000300e8403031444041e542140241d124031075154100c0000c0c0780e1940c0780001990b040d0310800944000d00344075443d417412607842e400360490a40c80c52401107250b51652a010f13003543c00150649044c440c0c540d07028403500408e45a01c5280c00c80009402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 416115944 1250 416114694 416114711
    0x91305090312010e071e050406182c0105040b0a12020a03020d050f070b0f0307080604110409020c12070503030c0307050d0e1e010615080417031609140904020103 71
    0x16207103110300d001a12600811000000b44c02d000d544045200f500035440d00c202d100075040540c1840407284500c14003240092200303002c003520403410845411240b206051002d501d441e000c07140e02c45034018104040c26130a1020010014140009004107000e8500340403824480c0000384c403403825030080aa0042c2020040e10035507645000410086070080c00d203440f5907a450030b1035602c94007070032652102849998400108040c7e000112002d100d0040c034a0707429501c4070710040301c514801600031a4065103034a801414080203400030802411941801665800d03560001d90501e1200308000140844c1408001d001c0b400102c102c943c040030903103016550781e8484070309807141d020314a000022546030074040081c98034001408041c40d000282043c14840b41d010042e8241ca00c0c90090303140d8594031400e040000b80c0501d103070982292150313025407802c00c00d04040c00300b00e800440b8030000407a155650800030030703081130030a009400e41a64000d404201c1c0c03000304000c0c03074001e40024109540c40201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 416117194 1250 416115944 416115961
    0x204090203030f0f0301090b10050708070c0e010b0c0f030901020703021201110d0e060a0c1b0f080c0309010807030e0a080a051c1a0f090106051309141b091305 70
    0x2c031403820900403c1c1d10340b100004814252079800c00d00600600a20300f043c240c200789010207001d2a03030b944030780d25240b0b403100c556071b242071540106034222910b085414000c600b080b04040840c4c040e02d02d5840042c0c4402015461070315080c008400070806410411081707001d641d01050a005480e01541e8420611012181040c010042102c1464883c0742c0400e00b0341c080d10031904000540c07844001140c4494581e40d124400b203804903c441404103640e60319540302c482d01c10411101c8107025031039045030703401691102015940846802540341d000003a003c643d540e080400950031003803a00d010007100003030790010360b5610002900503055440c00f040c0500d6541c0301d201101d4001d4a1006c0400d040509000e140380648008014404400d0f030780c1051243d1400d141200385095030008000308040d910f07026003510290710080c5413100204108102190440160003080d002000d49003550a013441c0c0030002c0000124801c5040e91501c0703041016000702e40e04c0304030000002c00c1100c0c000070951120b004 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 416118444 1250 416117194 416117197
    0x905060a0e100903050901030b01030513021309080705010f1404080a050f091f0801230909012702010e040207050607120209040c02150606090102030d1503021f12020a0c020409020303 80
    0x580305510760a0044000805600201600305a079080c2c23000d10031215094015002d40c1c204456104036802c640d06040050310346090f00051007a01c0420000346d030040e5446208030756014070001e5030640e450307494110300a00f062240000030902c18007041c2442c1000e6a949940d489013540c0c01080010203c1c1c022203032411602210559000100b030341d4010310002d604c4101035007060400c10041100e140001882c02e41722140101021140403024003416400400c00c005e816014061003025980d541c00c00c0e1046111200080c52034598400b6200d01a5440c40010000003d00d40c0040c01980184003144c000740300041e40c603800101e5410000346002400414200a00940e424568814240360385480700300e4001c070740c2141880d0b951028840c20390f0b801052150500c16a090310b80141d00c00c00c0341c80105d03c01540920b4802546403c0c00c1c407140eaa039000503c02c2140a0068003901180d428502c40d445d030400c0f4183c004001181e0198140003507008041d000800300340c800790159445415800071503500f0700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 416119694 1250 416118444 416118463
    0x50706060e0906090d112e020c030c07080114040209041a0a1a060f0301150504050405010306020306011205010608063105090717060a0b04090203010507120b01030905060a0e 76
    0x441281c0d0b140c200181c0d41e8030101502c6211303184c001c1c1c600410319a17124030055010800544010442c09030401d10800a40d61345203103094001e008818495012151800100b110b940d60400440d02d0300540d8403440d081020503400b043c0660314104041c854004075500d0558403a40490700780c0015521800e01440c002149107402c0d8441c210401045460111940f040444904440d03d0075404881c2c102880700038810710b501c854604800b0b04c0108032004100e1000c1c4c00941c12032815504103603594010409440e801e030421142c29801100300881964031108140e45106200800d10841d40340100151895102a0145004e0340810b6210f034025075440c181e601c4050040382c4a240020406030141c001480c2c01d071112a440c0c0504c03c40002c810031100e04280501c42c482000e401992104082d03035004204003103000781c009450f818680056a002c0c400d031481144292203000845100d1940b100446002507403e505040c40c003900540440e00028070654041007000000814800e4405440c0c50907900e01c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 416120944 1250 416119694 416119709
    0xf170301050d06020c031c0c0f05030f0f180a0308010e0c070c05010f03020f160506010623071110120f06061209020301061e0602010c030203090d030c180b120603030a0503040305070606 81
    0x181c81080d40d000381503106008281d00d940e100e018040c58162708036103501c000e8030b000384403408110114114066500300540c0200b0b000744014024910b0100340f9042450303005c019404203006000400008607141c401940c00100c03580c031186451071540d80e2040c01400d0b8066241041203110401000c2406507040b25100b0120b8000d4035222040c504010b903103048140c0302200c0c1d50217000000503980340100d0320304600c428030540d101e640307901079010782c64583c0140e2400d4402550302e6920175410780b0303a038240507440141d50341c2d0504822508090340094a901c0741c00d400300c0c54070f800410440d00c0d9005e00d0070700820104c042c02181032042c0d40002809014a9040010482068203a024411191038090390482e0090780007403201c11020703807094003280400c03518901c080d001246141104d074480c0d803003a60410102e08002c0c80e0340179044000c0201441c1d42e001108001c0000505d000c2c0714071903802196111034100c0046103084c443d03610040203404060001028020041440030800020350007040140402c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 416122194 1250 416120944 416120977
    0xa060c181809060b0a0f1401140d0e0a0c15091505070201030209060702060309033c0a0309060e21030720030705150412030501080601170309060301030f170301050d06020c03 76
    0x80d001c0001c8140355511894181b10442428081c040d4010544810240c080300b0b0f078a824000cac46c00c0d200300501845910b520720340c0214104000054030f10392b2a90007900c01488001c48007089903a015004e032040303070004010504080302d11940d69510100b120003060382840d001d030b2180114408102c0d2030003103401c0254013510200401c64012800005060802c4101500421007402000601101c103009100801003403180c07503c10042d981d10f840207281e042000d00c1c0006403510346840382012941c04074060300712074110341000c500c14044801c0c00b4004c00104a1054614109040058428420b1301495070290007080d4414041401c1402511740c4160003100359140501c1400002e000940304441c100c540b039048002d102d428a21038443c031030584112a00800703460742090510903c01c410300c2d104134404c2c8010007600d00641c8560000e0f6000f54425000710001c00740741d2900c8a91801d0000405000301000e00041100e9950910044405500200c005070b450248203009401e6200c0c605601c00500b0302d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 416123444 1250 416122194 416122199
    0xc0905040e0d0212090609090916031115040833070206191e022208032d0a0c080c0303180f0a1a06030f0a060c181809060b0a 55
    0x3004500650002069404d44944200f41140c049140c0610034000b40c00c22424008440203040400b035043c1c01c009400300312074403a0401008a99402851b42023141d55600c0b10520040340d0901e601e1480120154030380043c00c043c2403000301c0d80d03070f18558900700300c0d244c0c0e107030605402410002040b01c021a01c2e00d03c21500924151001a54504084d2240c0c40e659030380000c0383c20b1620081c80b5000c418903e00024222402462150310f001c3d400507800050180651b041c581c1108003488103490081440c100610784601d0600078010041000c000d41002c980f81d0000b0f050410041941100c01075400b5003003d5210558a00f07044825001c0c1e44540a01d610000007803004000440301c541d9400d940b140100c8092002000d40c030341d103c040b0000014503046e0400820040c180343c541e0880c3e0302c076502408461007094104c0c3d40c245804034213102aa0380c00d0b5200c2100c0a01307517000107101c02c081c0d500c1c000d800000d0b1070144000907800100311032858107a5144008030800c41c492300070744402400200182040354 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 416124694 1250 416123444 416123471
    0x230402011407080c1b1f0302390109020d08030403090b040e060a090b0d150f020a0c0b0f190905101505030105060a05010519030204180506120f0d030c090504 69
    0x902c050b112810501c1159204c240c0b00a034035841000c604800761000c0042c01040c07006d0807100302000145000e250f000d001d40c641c120448012016400c9451300324020819101c90ba1241402d1a501481003a034104580e183c09a02c0e030440307c4c4110355201c030300d01e40daa035144c6c20101c4140406410440c21408000303000500b050240c07000344d00441c0119640707600c1d5a6100130380d0f01116100d4038100c0c1c2000740e060701d100102d2550104451040003071503010854903240c181c220f00f00da20030031f10807001c600e1025414050007071040f120307940000c044824581700e0401240d0203418220051720007680d180c58450030001c001007800f0a0180310055507050010740e8a200c000600307940e550003079600035032038403000416070f1400c29948021680b060311218075040294100d4522042c40940180a0640030400081c002600c0c107100ca0400752000000112428040108040600c07240485a4190300201c0d00002a020100d0401021859820001207140c0028001d6807145003035400185e015241001c540e0225 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 416125944 1250 416124694 416124697
    0x4020406031a0306090c04110d090c1d042102010b150c0f011803110f0a110918100c0c1b0602010501050105070f0605060604030b18010e0123040201140708 68
    0x50b00c4007021609070494002816a0382e0b50890f00310302d01364000200c0c80e91a04041d88092810601480420b1030718070444500030030795140309011108007505a0b02008030074160303042800c040904241d00300440c203198036106e1b8010b14801100201a00c07100c6401e040038000d61151780c400c28050840c039591441902c01080c150413a808004a6000344902403003c0070061040882d2807591070b04403848640c2d2520212036954a03c12000b80520038090900c4d1070740820801c019903280320345400c0184044c401c0601c4680c91000c0d1515070f007079010451180101401040000102108803070004042d0300f031550407101703000a180045c00c1d0703100c2060312004001d803100c18031050310701d103070024461030f6a100c004590602c070710007001c0c10218810040400081c41d941000c0c4e0411002070000e400d09480e5224800541e2040d5041403140103006d0483c02c2d020030038060220003210b460000c00900448a00d2a10107507941d40d8091028013407a0f000408681c022058401e090211003409600c400c07117440c0900d0349 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 416127194 1250 416125944 416125961
    0x41503020301050604020406170601020a17033c06130f0b1903020105030103031202250203060708190f110a0810051507080d06150201020913061a0703030b0402040603 73
    0x65403c19000030814213240c021102140e01e569100c0d056640c1d0b110302282051000752115045025541946012440c1180d19454468144003500e0356070402803000c2501c07800c0c4440e180c2010400a10301c4120a10010b00103280c041b01150015640e41c42e0b070b00203a050100c2c107407140441460044209410020350b44000003011080c0c13040c10088084400c80c00041e440c510009000a80800040c000070b0302c22480c20240f008c282c6409800c0c010015094111514030142442c076072081b6445040651070108003440e044010350524058070304007021b0398400d07840c04c00c11101500d80c903554420a4818207600090f0f680c8031040140780c03500c0420074028040b00041d83c41e03000030811150301080b1844c02c141c1d01e851805505800f140352134110341d038104850f040048030341240c6503503420016018048420140ca100032aa00040e5120305010070800c40120062255144501d0450113000c040704a0138140c00201d11248040d40320040ca160880203031001030304561f0014004100010307040d825404c442603 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 416128444 1250 416127194 416127199
    0x200a020a060e010209210c100e10030c090911040503030d0902090f0c030a0c0c0b0a0509070915030f020310091101030c08040308040b0c0708030115081605040501080703020904150302 80
    0x40c2048102c0070900780c0c0254560590b000380300c541c0540c20b98004100050180307000c40150303441000d03240e0002d10018015a0190080f900c0c0c0049001c842c80c05200d800010350840c01c0400400308814402015030b2150b000c1c400c13503141d80d140000800c844410503900100030003012241d6402000b20840c02400b4a0314080340900e01b00c070301140c1446d02e404c608510410b00880f40364115130f51965640c0140280300010000d0242011100000c03558040d0b20520500300220041090305040d81c400381340900c15030003501d01914011400c401c3e001d030b050418040345d0300060307240b039000c4180c00000c0c100034019403e80c5840345071000310410010b2a0030a0103042030240c03420001c0003203450302554800001c990049c00221580d00040004000482680d00314030301e4201c25081a140c1c0c0d650a507942d0017a003010601eaa80303011010078040d4481e0543c2d5000041080031529009014000342050140d40101d0341400541c00c002060544203a06036a030a5500420030b0155500302030000002d40790320f000a90 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 416129694 1250 416128444 416128451
    0x90e01081e030403050606090a0f05040b04120e060f13050a06090501030c0c02060316030f0e060a05010807180e0c0a2c13021c050d090f06030501030b010504200a020a06 74
    0x41d0600c40401500e044982180181c030150b95900100004440001c002103501caa4440300d00c070313510145209040c815032203211440010305050800420450215200d20200305080c5a0215240c643c4015a8070312225000095140d068a2805008481c21504400d4000d01c0380800000d526500c10900c00c101d41003a28100300c0300282c12021901e840d0b040380040e40001c410004642c6012a6011136803000c0300510300005d0908400e201502518070500c00c0c3c1403d64041c0041c0891a13140740300b180c0c0100800801011720740d240c00c0c60707084200c040781c040d0b407462a82c0d40d07004040c0e90740074044801101401083e230a2019141d4003280c81d032426500710310004c081d58444c14001d40000000300c0e402105140c0000f0a40303c144d508005119200030340c4085a8003501c501c80d0001103041264455481032511400030302418401c040080d003056503c801c2c00c02d41014010400f00d0041c0c0a1107056807000d0794045403083e081100000804003507440b80d0400540002e01c00c110582c00f0912500721407082c0ca040c03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 416130944 1250 416129694 416129743
    0x405032109040e060711031608070201120f06140d12050310051c05010f0c050d0f02072907020d0f11031204120e0a0e010b07030c0c0803030115081b0307090e0108 71
    0x95901d01a108c0420030f06400c0764188804140d401c0e0203051503600c140342500f10901d04805601c181d07680d00c0c10900280d0303140c1c00240072100740240031050084080da84115003903043e44800480340350421a80b4180140040440c180c2a10034440b00003600d40903117a40315155103c0032445000340d0740c0109035907a510304144036004070030a020712400fa07042135039000c1c1800850341d102e90080c0a5000c041101581c00c1058070300003001056140400d10b10302031202c6500e0030304c40c0170021000008080000719000140128242a00a48900c64003061490083c008520005841d032840c802c8062003414030050408000c100400241c0040407040c0a0362409000301e040010b000050060b405803840403113040006004500031395020f4400140a494020102c0c4004d8941c00c801580c10b400c5860300b030300000010f020082803c408200d0440d078600e4004490b00d071100da0415505440340e11480500d9002000c9600301d480f9040a0001e8000118240c0095948207190b540e105104441c0d5105400b408040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 416132194 1250 416130944 416130977
    0x2071704151b0b06040510050d0c050307050303040f0b1b1f1d060a020901090b1204060c0c020603070804080d0f0905060a050405070b030a0f0501290405032109040e0607 74
    0x1c0b8100250710811040303168942c00b040001400008100d1508444c1801c0d00007160b0307955216001041e03001e5241b038107406080405050408010350000c0b4060303031040004202c030001012241e02165411200079071100d04020414410744040301c808070300342c0b140410385800b1208045003108410490341d800c2101c0a800c9004200c560808110030001e9000b04000070300500080c1c00805480d041490f015000584a52050100e9003080e4007000185000348200b00070880c1c14825414040301d10f08003004040741c0ca40c00200031340720003401541080410b4011800b008100d000b99480503880002c1808202c0002200d54024401e298080d03581e03102e48400f1400c491502e1103024022078200c0e01500c0b0203400c0201c82c0074158000b138494002c080c0d5a0240c2c0354645618822540608031140500f107440300c0404545181ea402c02425002104d0f040108120a680025a0600080b60250000c070300103c998150041c0d4050981c990350894109044082c00d1030b008a0f065114030050b49400030350a500741c4e007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 416133444 1250 416132194 416132237
    0x4031a100510051b07030803040b1b0306060a0c05010906020c030705010b0d0201092715170d27090e0307021f0c02122505010f0806030a060207170415 66
    0x8000b00032031820425400000640c00c911041c9081c410100c0d00015500d42e0741085a600884040c1c8294110000f4030614030786002041380090b081c200f807203045040040c0010364600c81c035500036081c000042809800c112080d008002c1c4590410750854540d504500d011f6100e501041040320903520308894800f00c0c0c50b29130b4558015a130182c1d00c001c0d50310308164183c644000f48d4013082d083c0b5554024060bc54604901510700e2010700300e02800922880c103c1c1300b50710505481e106040315041f00044a400340e07400000c8003544030001c1800c0702504c20260880088960603000320045e0340c1001004060705000200404a0a20a4480351401c00035110740c40501401c0250035000140d1010503140036181032280070700e112046406031201003900c00000b032440c411103610a0b80382000c040c010402c540e0440d550300500030140c100410549070240010b0386034030501000814240c0c1c00319000003809004001541000240042c40e60307569100d20142d01c078201c080c6000c400285c40402118540041070b1b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 416134694 1250 416133444 416133469
    0x4050a060c2607150207021512040303110903011404022403070c110d060c30090f0b0a021206120d030507120c080108160e041704031a1005 61
    0x54107440010041d40142c2c0e64844040c01c600b4580c0500c50100071403428418202c0300801c920005070782e0748081c818050300b03d6400b13540383c2000d0001c0c0708581d0210ba04132019940070390706260004030000d11241801c010b0091803292600b640c0703400034400d0b030100800d100c98040d0f802114589000256602c003a51810074100784651341490a01c0415103460003605980e21807803191508051842c0c0c1c5501003040700c010010144c900907221024080c10315000303504404010226540303038008400c4080540000d151460000031810b98920060041c0000701401c07040007a4001c0b00c00c03005003880038840020390050311b005042001c012021803050710f884542c182c0e148002c40c01078110140c6105040d401031500415080a0052821325441140410b126214400907103486d00e541c0765060850061402840034282402d107140c80720103000390509282816031082e8401081000100c604802c00494000d941c4000d0449560640b81e00b09411520b0350782d0711505d00141050107481da11810001a0103900 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 416135944 1250 416134694 416134703
    0x204060207090e0c090a050a0f020a0207171002030f070306050d02100e010e1504030b0906070c0f060603051902010e031501060c0203010b10080402030f07050a0509090f0d030204050a060c 82
    0x9142004401a03d03000200b0032a2a5019141d0751040f40010601c0c095049074640c080a9580042007200d2860344282100040455030031800e10004940c003030740d80c0b940350080c51844102c00c4444000d103041000301c1540002500c00954403401c1507980c076050480b0584500010030305010002c100b42c00c00740031004035282c000741074080c0c040c0610390a59892540d841e070241001281c890010f01901c402c0b1055a2032110856503903551451070404080c8010080d0102c9260f0b08000103000718994402143c501e1203801c9040c1f4a003403021407030008003d06141d44014200e002c0d02d0420900140a103891901c914000e03254011080340da003040540343c102c000d01c02c00701d1100001c01440102d204400c6180418405000000d8040e4690005002854204500400034002c407042001b1400d0074030802070100c1e1204002d03e2041d0400c3c0004254107034070301130a4042e1090b90001086c0038410442e26503d900e0701c10503940344202c021402006540140580c900600b00380c0340004609114414454015401 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 416137194 1250 416135944 416135953
    0xa120f020a02181305070303181406040b0307110708061e3601020c0c010e0a0b0403120c061b09140604120830010608060f0103050403090b070c030b010902040602 71
    0x105585042002c0c212801c0511081012130000700308001c5a0003445c06600c03a46403a0080480710100707240550440d0440c4a0b444500784466120344081d1803da0b9400313088603882c0d40d1407104c01c407130745400c41d14010303c0e621810760005518800030503554001d9800840701c040a000d0b100d4640041c0300e06682c0001c4c0142d0340713501c04841128107000000d983c240c6084a14180410103c26420790300509090307030094000c240002d43d07941c0c00c2040c0c2481d4020503207408500e1450605211200d020703520020740b00121845091200c513204010188005038004410400c0100000440701400600f2111300f0119a070384d000405e040507201811078200308020500c1d0300e801d0030096071501c0a80140f1080712402414020b058450381c0d0242c5610040080154110002e42d121f000010f1248044e400b003001d0243d08424043c0507102c81100001115084c200411182c645141c1100c28029550016034602400300d03c141c00c210040408104413402484002110713601d8a115000b00e200d903100e1080903070300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 416138444 1250 416137194 416137219
    0x9090307060e0f07060233010303050304170a0804030e030c2b12080901140c0a1d0a0602030904150b0406120b040207060204031401110904021b0a120f020a02 69
    0x803640002d001e005030381c000d65070380320300c80710150786446181d80100c1c026030003994000556020320036028498080343c103202e0302d80d81c44243d910940300a043c0006020000000005014403000e450720741281014500d002c1d54685001c400103040800980c0d013140080d101c03c03120901458009036408100c1790041c0918003100c0e80983e244400580d00d1b450800101140345207002080000c544e1008114098880f03544034604101024211074280117100c018814400a04c07a20780003003001e131031191010741010305c8100c1c1c04034054104107000188090340701c446d80b07801194460b03020000e4840c801041d1010300c000030603508040164200381c06030807260300c0c00340001c03c09107209a4220300c403104504400a00799802e440072905a0388056015038a681c0c00040800c100720306a0030348491801020000c01c1210580c07002c1c03251034851655028030858001c2444401d40c1c00d002d2100c1903142e280310440e405e070040c601d05120000c2c1813081c0403020a12581000b40e00301c0c004581c43c0036465008007030089030030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 416139694 1250 416138444 416138453
    0x906060a0b03070e131407080c0a02060a1a0301061e0f08060403140706110301060807111f15140a05010503190f1e0603050d2309041103040f020102060609090307 71
    0x1644003100c0303507000b03441400d40d00d44c4030058880c80c4a00806e075800b8500d6890038036005420310034050b01401c8212400c002501a880c1d01207540358208010110128207003c070455030303050036400450310503415441c204c030010f010300c1100342d90b91048031007661800b10f640e9900c180e90031000c032500c42c18180381c200d000010300192145200d081e501c0060b210311810060280c441408445010706404a20000003006000858020ba941584610a031400c60052442e0200040d00c40705040c1044020340c264500f10b904100d21070304042401140d081c810115a60342d40045403060f0070a0900c1401041c000f44041025441502100c0c400d2208017201c1c2608500d001761700c4002c00b034003d52504602c0d900c0203824207142d0384800446094880c1030000ca00c1c1c90450a20904150040300c0130f106001800e4107000040c2003e240c5054240002000162103a05c0100810003030600700e1100116040004100300811201d0160040c0b00ba000380e0884160350742d0b14040c424800c5050b9040c0d2000e030300034002100003c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 416140944 1250 416139694 416139707
    0x405010c1205070f030c020102370203120f0904180f030503130c1502010501150905210307030f0e1909150b0f041406040501090b0c0c1005030906060a0b0307 69
    0x2826186002d42c42c0219a444016000400d0304048000400b130302c106e44150761f8100b003c1640ca4100d10107960083d039004a00c00380245250050606034400a81000155078051105640c001203029401da40d81040c0d6500711520351011003201d2180d031a150540e507001d1055a070000000e80d002c1040417002645840a80f0309410080522042261004420300000d0b401c444800060105011003100c0400d060b0019007500d00c140c00c1404001c001046400140d54020800c408903401943c11181d40105442495204100400c410f20248030001d0710000b019800076500c00740c0501943c8102020000800304240030a07400040140c00011a805008441c80d030783c07000d0480c480c29032082c400759648a008c0c0d580e50300070000020f000315011500300808800c20103006141c078003c8034001d1800b41003030000381c803610f003e0050368a10070001c10790300c0c10500704010340313844608010445040390030b0380c440040036503004441c040614041c801c041a25030410250110544210045850841e40c2d4000e003140e15 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 416142194 1250 416140944 416140973
    0x303061311070807260912010605180601020715020615030a06090305041802030420030f070e10050d0f171c060306050903121b041806080609030405010c 67
    0x40d074540c00c0c9003030703206400000c0101070300c80c681d11616441507081120701e1700e03008690f5628100c4040340c4641e070f402103001203039a80d84003121541004110b0500c228010901070308620b0b00940030724900c014aa03a90362100f03108410990840d2501505d8028407180404602d03071103c0940c0c041c0000c1a21a16903c00e2200700d44001f03011160a03007045d0715110251141032205030045000040c041c080008840e45101450810007001d61442c145070741c0c2c141400052180c02c0c07e26003c400c0040d42240d50030300c18624003080480840f0001d648a100e0410200010340e260141c4190200e0000348138200268414100c44c1c010314880c250300c0307645d10b410141c040b07034060910084904000840f80040e0082c1040c1502e41150400540710307040d0721305602211400b4140042c0c0798414001100e840703003030002c1154840b00020038a440900d1820703d894031805250018008001101d031035816181269100c40100c2c0c00300c000322409619001c0d0b0003500e030f20942c000e5a0008a0b01080c15000c1104540581c04 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 416143444 1250 416142194 416142229
    0xb010f020d142520010212030606041d220506070309061d030d05010816120501060e040303151403070605090a030f05070e0c04050d0b060d0c120308090f030306 70
    0x60304400034110f0b601500040d00000e0244512941c01c1d041c80f07144142e010383d0421030320081200c0c04c03200700080d580300605403000811840010000c0d59544460381550010a80b184110491000140030310500340411204040d032503a1400621040d45800d20480282e550810060016a191848210003034401201c0c180c800c1c603100c414503000c000c1c1041c0740030428a03240020390b840e415110003080a40e003040e408640030b98001c13407030086600e9205580004a03030001175225071030b84091800602521540d40b1022804091804001c18103400da0080d8000348500c55980b002c181e110210300326650100c408940c0c040c0d00c19030040c003110340560003d05c01c07003000400136140c060383c03070342d8041c0d00d40200041200c3d980c010f50750801c000e100440c1e9260308a84030341503140c101400c10003c22848004040060031407011040031030000d88a5001c01c03807030785400149406030592980c0d214404800341d581c08130300007492040059107018011451402c200100d1000d9403860316101f00f040480e2440c2144001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 416144694 1250 416143444 416143447
    0x5060a0503060a05270a0e0601291b06060a0305120a110a08121614090f13150603020f070f0311010203071706031504060c03110c010603060b010f020d14 67
    0x40c1a0385016030f1341700780d0102d0498034030343c100400d200c007035110b0340642410003150800140750384900c00491040e054030200e60b40305405585204460b681c03550084402d1041007000a00c01030191110300c004c3d05907168000c201c40755500c60405000c82c03841e003484080d10030b404c94054010340a030610004c012102251170484010b81c1c61080c054107203ea08813088a51000c0024002026008542c444d42e008144290300001c2c007444001c060900c030600c0d5104400304000042c0090503903219003000030704001c0502000512861046501e0003482101d4101424614060002030b449119008071044e4619128459003003402c1652124111109000110103000500300507110100c801d1001c3c5201e00400c1d551401069080d2512003107001c0040c04041c066004080c420031942d010fa4512070308564060000a0341d8041040110300a11203190442a1064001103c0b0301980741504210266030044c1d4003000718111702001954008002e810038005604030840b1001c0441c004d1b403110010700c7d4400a4107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 416145944 1250 416144694 416144699
    0x50f22150806040201090e0705070b0a0609022d04141306080307030201020910090501021e010b030102070303060504111204030e011806020a171804110c010504230102030105060a0503060a 82
    0x40c0d480150300841c01d198040c0c02004159a4840303a20700080540c000b80c0c0c500e605003520005c2252003401800380c01403c0c00c0300410340141e8698810709c01082e0f902011515803400c0080204d5000f14000c001c01d00c050f4610135000101c042000700c0c2c0c216140003d0b0941080c02d2102800f01c148118510b48408550f80d22000514000620040520500ca940016030b16030411080211001207540390001b0030012410030303c0b01d642c0004451800c030050000c121200e540340a03509000d403008003c8036416500108dd42820540c00d9005603080d118100e4043c0500065801d20000714018214a01501e0f030a400c0410003003401402000c10183c2e06141004e458104213070580005205640b0400050740003490040038070015245090521004031a030710310303000105107810a000c5080011038442c540da207030091001a100000c1741d0031030201400078081450182850480b2a41c00685145204030f130201d160311000c1c1c10310807681a60f40c02010130782007041d03c000c11903258200400603600100b6a5602 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 416147194 1250 416145944 416145971
    0x20a09020429040317070f0c080a060501090b01050a051e070c050108060d050606011803062f0403120e0429010e03010504020306010b0c0a15090c050f22 67
    0x40024015107803900008486150500181c00140d0a01141c00e0800f400b0900c00140c143d0755035840c1031251840c003a2101e80e241041074288410800003030411f4a0000700241c18100855100a1a4001c8004100a0382c2e110811030640d000a840c0d03e00240042220040880c0500c014240110808082a860404801e006690b60f03015036400e60f10582c04050800440d0f9108021640c082016984030044200380e656150b59880c1c050800e40c14040ca4690382ea10984108500c03400550b04100d0a02107c10054210381e14588140a003c01109801d00050010f01e400012101180d0b07100c40030007041001480c0c00c40d1101c4000c1441c0390f1142d1501012014039140424000f44007802c0b68008c038210400340d0002d0000810650701c58020303410300c03081102684e004990f850448060342446540c445110b405141003030417041d0000c2200c4210300c40d020543c10154004e40882c1d00c10184203070200d03180e4041000b20400c0c40401a40030b4180b00ba00c200c0400007200110950301420004510800501003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 416148444 1250 416147194 416147197
    0x409050114120a0b0c0f070f080a030b0d0308040605060103020705010227010e2d031911060712140c030406051e091e0d060c02100507030e0304050409020a0902 70
    0x407185101c1c19200c039280540c40c01c02c6001c01d080c00c02070003c00b42124541c1e01d1480341c2600a09402441c000494940301c8001c0410454101c20740c01031040b4041c540f1440e20074003a40103000c2d0721001901d041602001c508000d032410a175181c145e103410394503036100c0da20b042c058440180741c10704050b000d11540780001d000740040e14514101c0000f043d440c40b82c0da201040030110201c641410000a0010200580c80385948054021248900c40c0e0700c0c606003a07850040e501c00940b1081e0580b141014405500c601c03280700d007510758401c1030f101084030540e01c2000618003800301c014202604c42210127200a00600000d8462040c500c001c0742000c40b1045140e00f540c201e41d0001d8085240040c03041c1210b02e844003040203071410f20036441d04256014001c5012402c0743320420380f50707400b4002507405035070713601d101852496840312003404030b40c030040002910b0f0660250b440e0303101420403000c10b2079207000303018a00d07501140800a5007001d01e000304101c06005140b0050b42c0080001f240807605541600 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 416149694 1250 416148444 416148449
    0x2071a0106050a030507050313030c1a091006060212190905060a170603030408120d020d0f0c0315050f013203091c080114040e010f15060908060402100504090501 71
    0x1110b0315100d4003042d0003d0141da1000b0400c80030030404108000300d8034151481c0c80704594040c0b510794100125498036a01060003031524010304106c000822142c0c820002d04080040b003149001d006055480030144d9482e00e40e41400000714500f482640c4800050520000402c2c810313103800c2284568880110303140750701402c5082e0014082c00740180c0041102d00c032681d08440164000d6141a2800d0710690b00c0307184080314800120750000300c0c2641c3c85003039015912900300c540320801c0040c444800e110001d001524420340420f050141c10414015104021011104003034501c203c041290780045491000c0510140c014044024643c00700d01000d040441d075001d0341010032036490400d086107600d040341060100c1c0901a860142040c2103500c400d08504690008012803000750780308001a014000d2100502c40a601c0d20b400c0f10011101900001411020310000c02d18050300c8490440e007014460003216020f50154000c00c0060500171500301c00320b9114940346052945451501e425160281e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 416150944 1250 416149694 416149697
    0x1090b01210f050c040c02030708070803190212061005131a0f070f02190308160f0501020d150b040503060c0703050408190510020c0c0f0333090a080d02071a0106 71
    0x1504480e04c02d060901c0b42c10109420360005500f0032040790b480c1c0080d03109014008102500110100f01c0500b5181c14140c00802d40060039500c4100300024640803a00c1110710b40d101d0080c00c0d9942b900503005401700e40b000c40b1905100c2e48807500741225004a072044000752a40013004102c401110100c02000c1c00d07016200302004610182c0030300401c001240e115923100702400c515a03081000400e06003c072940d0001c07050701446015142c0c203040e0580076105201404035400000d507820311140175484078203045482c01c0300c440059290b03142c0c44039502840c010250554401c0700868500e01910000d044882d209240080c902601c459400d410003189241d054a03100e1030382a01c80400005008124140075200d0003107052000d07040c412aa81c09800382c0306801542030105043c42c5850511615100e584202020036606a23508110081250780c68440105040700202003558604042508440c5c0c58001c0c42e098101041041c5c484020760044d4000c68900581c0d841034404110140e14150091619 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 416152194 1250 416150944 416150953
    0x30705190f06080709030f020d0605070807030c090b0a030b0d1403070b091b0f0301110a0c03020f0a0302060403051308010504111003060501090621060b09030f01090b01210f05 77
    0x80030442001c48203241c10107000d1181c0076080290351540003a00100302c98000400c1010f0000e58008106a01d06108001d00101e04000c00c1001c16074000880034015401e564041282540030b84c02190700740c006010700d0180600800804081901c01d0708200880f1100420518a01c00d0396070744d502000c2c90360782d00c54605d5040032496600b03018507100050340c42015400940020243e08940c00440142320015034480c8561111030882ea48096020300389909509001541d12079030340c8406007400c1040201100103108001110601400c040342114183e681500100869200da03502924140c020421401126100050002d0388140c240038590089004274000c0c1c051980034401e221108180d240400c00307050030300303000704200d9a01c142c3d158210364582c61718500518900c1003409000c0c141110205105c2e09200c8081403a40b024802018260403c1f030842c0c8031040200311003420380c0c0c0898400f070300078000d00b00100701d0303030160400750081514524080b190f41c4d101580e9132485028a600c00385d51b103500 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 416153444 1250 416152194 416152199
    0xa0605060a240f0e0316080f070b0d0c050f0409090c15020a030302030723030618100b0d0e0d0c0512090306130219060503090106051507060b03070519 66
    0x1000c0441d2405031521004051007002140c1500ba00c81d460344205038204600e1403800002148680e12080540b1402019a8025004c400c0b003c0b425240c940610090350180042034070302c2080015600044904030002142841082e4158200400b040001c0c44c00b844003c00484640c11301241c010400792208180001e280c400d98200391a180109030000081d00d002e8010b0740c8500d0f500010680c140c030b81c0c1407074003503500c0d59546006c5405070141d00021041d102c00100c0c083c6981c1e00c00740954400c0d40700f0f450b4100c2030080d001c00c803010f00c8070a0303ca040a905012200780708039010b4600500d00c0c00503103c00440c03642c1000e0304807490300d0443e1102e0400502c84041c17440030810300b8001d90b11603070628140e15007400d0502c3c001948455001d0244002c91040000000c11521500d40f0001140d4500041076005981c2d500d02034034590007114100080d5180403808503661402c6400500c0203103a2640707150500300a030307075180010034048000503418880c04400186035910400301460a024a01d1040429403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 416154694 1250 416153444 416153449
    0xb011211090928030c020d02041506030e0114010e01030b070327030905060306100503090106170a0510090809120c061908010e070e060703090504050705030103140d0815010306080a060506 82
    0x200d19507a40e0b80c2008604040f200440c2c1d00c01c0500c100560100c40028601030248001001070007510481600343e00b00e41d00000d038540e0991b0000751402040310003400008a810400c40595070240540099411034000520115180c0256a030303201d03143c5e0500250745010246802070030f00850241192030360780320450300109980107423400000d04d8261b0320b1901b903081a4002514a020704507004017006400700010b08540d909400034401003007080082d451901c51021015240c00101c4400d85044c82610030009a1480610030040000d4110901600705601c0008201c920706a41d07603c440b45200f034036a50070301c0f959008000c011018030105180c880c1c540540e0050168441607205880d0f1141410411003016001070082d0954002120030565480041c83c080d01ca80d045a081150404e1902e020411640d400400440c180d0703021300502080b00b0f0712025403035950000340c058540040d0341e00c0c01040c1c801618450301c2002071b40c141000302c2d0080d11505514903141e190b00043d1415600c400c2800f0450 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 416155944 1250 416154694 416154733
    0xc0d020f040e0103031206030b070311090a0b130b040e0c1c060e2d013008090936070e09011d070311100c061a1c0b0112110909 56
    0x406c5124402e01805240d82c45506518100034542401c0c5500d0381003a13003a03146244200c501e40c000050a2620064841e11501c4c4990000c611030002c0307a095050100380721010100f542e08a40400d0075881059407801809803468110101e07170080807601142c00055210507010350009841d20080c80940ca26000c00c0141080308400104942152403000342d49a480c012019181514001040d160f0a130740d020749408503840016402500740c0701020300c1c1c4020801c5039401841c120400b12161907080d100e4031482050740c8034007070444044192149003091180748004203400d0000506040c0e50520356250001c9203808801c03180301560365034800368404144c03c207039036001360700f0b0f5400001c007401821a620005250310030a9218443c8862000d400455441110303501107040c1d01160510950100d0042201c511001d02700542c880d1f1900b11414040c021110031072130449400541310700840e482c1030185203110b01c1c4148182c075003180804c0c1c640030342d485100e0181d000b21400d40c018045200c1103075000383c46 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 416157194 1250 416155944 416155967
    0x50a09120903020d0b060105070b0903130608131407090204060309020a0e0903220b0a031b080c090d0c1d0a0c080c07061a0406080f0610030b0c0d020f040e010303 71
    0x2840744000081c405a00c0f10b00c18040d415510150b1682d050300d5510058589000d505801007aa08103101007080d840001310140c1207540c4a09601d01085444400640d0980130480f051075201207810005000300704451b13985512003030a031054540468550210a0a03607100c7c2d0013540c0071a88603140c0b031045081000c5058001c04045140070024181400c507a40c0b2842440203400c001c455480341116443c2410100b88010085941030303136580c448600e8060064103400e0440e074004100d540700a88103c0c0200300c0648126a0398003085d01e000411400c01c0380501c1c2804d0196200700f500c8802041040040480d190310796081000004a0b181140c00b0070b080d01c40254a203c1080600024001c0c00040d01041d200c145500c19000f0400b03100c1d800c126074844038501d00c090b41c81802e0401c0022604408604074003a03d00d06401d031895a0346030014112003076018171006007280303c5400062107050380c081c0500003040c80c560000d4904110764100c06995041600602c0428100100400070140c003c10142103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 416158444 1250 416157194 416157197
    0x905010f05092125090e2109040c2c010e190305030708030405100204080a0233030a0e06040510020a0504030c0f0501030501080d0215060a050301050a0204140d05210706050a0912 78
    0x314a49208107075241c074840210348031210900101187c400d4101d40c00d5804905020f001000703005c0d00c00e20000c04038a9034103a481c1c8201d00007000d1301c07a12010303080c64071108181070f11800300000b0850309122507070130283d0f10303001d11108045011000903000d000619021340191242c507183e00b0300341440d0f402d003881180ea400c03c80703204106c03c02aa1030045030180e061a0100c643e003601ca4414000700185002e10001d15503043c09086642003290011405507000e500109020010303040303448503c41d511102580d001d001548228942c10030b00c9800cac1c0080c8220390141c0740c0f060401d5a66642c240705400160420301e51000e41c0201407046591600c9810300410a01c401005002d412800194441c60210103140001c08010001180391f2121454880203000140c005c21061901d542060001e4000340901e8801040342031001c1c0c443d152124440c44003030b81000160907502981c03051002d154101c110a2182400d0074440e05010030000c1c850340d84a5030b8004004a590200c80c686604e080f120344202e0340 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 416159694 1250 416158444 416158451
    0xa050d0f02090a210245090d0909020304030306080f010906150b0d0b012c0906030a050312091f0f0b060f09010e040f02040f060905010f0509212509 65
    0x140311203030403444031038050301915141b041c088180c0020074201c400001450201c0e0340240000c040070011400049104400182c4105648032865a29112254007040c00e0001f5119a024840f441140d801150040e00c00e0800003003d03691101418144040c600c13409034180d40d591135440900c45c1a0041c43c2c40102c07110b4102ca2400c0c28a4007a03242030186502103c00a90342c3d01000e20103900809002219180c0c01c0c008041071303410030001c50941d034081c1007194018040c100100b001d600f800200c601d45580c0c000c024504141e980c0807220500e5a004004500034440d2120801c00640d0380d05020501540707035000412244040020306003965103070f4080d18000d03002000003107201c2001105689100b402464804030740401e07140060701420729094024016840000d0002e898850102004121086521950a02da564000640e941d0845103000404a00200302c048014500f5050311072519040d103110f04030a0300d038819580c2c6802a0ba440c41046400002840c00048040c03030300d9040100484101231 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 416160944 1250 416159694 416159729
    0x30204110d0606051e070606030501021c1a010c0f0309120309140a03150903050d050c040f060f120527011d0a0203150601050f0316120b030d050a050d0f02090a 70
    0x460031744881c2001c0b007149102281000402007140c0045000f950028000d5483d610254842200c00007105c0e9030740c035018548901c8001d2a105c11200c107204d054140c5401303042d01c18540321140316560805e41102003000c02080410718180d480034814015019603103040d17000e414900c94421107060a20441c1c40750340170000030400201c08010000a500d403084020030b08040074a01580c582c081d040310101c0e85400e120400619a035050040c008440d02190041e400e00c0e038901003500e440d0007007030303903640002e01015540d00400802d800590300218904102d800709142c1070001078503600000110311840e5150189181c4445825000300b10701e12900c40a407682002039400241d5501e8070001440e107480301c900004030560700450036a094802604500c3c2c0d540c0c07800c21846100290780c40c00c61000306141d0b02c440620f403042c0303109038881064050700602c035a00c25181c0584441d0040701c041400c0140400100504001a02234040e122001d81005030312000da102c10408401820b4100b044e8070759860204 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 416162194 1250 416160944 416160967
    0x70809070302060c03040e0c130f030b040b0c190201062318100f060201140f04050316020f040903080912030702070b0d09061a0f120c0105090406030204110d060605 72
    0x4070307941150015030b6044594203240c114041e650101c000c00d18000100320107000c0381c200500c0050360641c0341e010000d40b2019000410034050001620880d0b0039000200080c001c1c110340fa80040001041d030781400e220150343d10700300c00100e0708180141d46a41d010400d0303090b040d45c0703c1200301140141c1d0030141c0301000400d6081c000d40e07180708488640180841c0c426a03c7c8403040d4054a8241a4180201d49a21019001c0d19070510800d6848008500148103400e040100c0d41c040c030f6001003c0c520308400852130030220548001e041c0e90040b441004012140e07214483c0126507480707511101e003103143c81400c46040102a8041c00c0a080d000c100304514168041602070540d0024141c442e2101c4441c8912001841218030041c4840d00d800c6403100c2c001100d29011103503c0d400c07650714420300c40e44804d01091020f42c91101c040d85e4032030b190151656001ea800b0b8080c0716005800012042d030b50340c001a0689218a8019286450003e00415420b02c1c41c0a40e4018000a04140e0701e0500e43c0b028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 416163444 1250 416162194 416162203
    0x9031107060509030a0b0a0e0d1713030c020103020c0c0901081006091406010c1e060e010b01090b0f090621010602060901050f040f050a1b05010f02070506030f06030f1212070809 78
    0xd00034100301546c800180d1521040d400010b5800c0d424040740d0300700c840010b000d0080e09202c0390055106400d074000078602d03584000c2030500d03264955103d80f1602420f41c010f4010f500301b24149400350054003900344864907002060781c020903210000f00a80d91003c121402194455040100d142381881640c0c844c002d20008019082502803030164a1450942881c150075002d0005800c4000d80c51582001030000c7c5401440d1417000f004000c100a4070180d00554909039684113050380000b01703010803008102801c1c0942601000509043c0c03800480058440e4042558280e92a00141c00310041c811168104007403584041214020051400c00e2090f080289000400061407a02584c65410410400380809440a680301c10011140180f200c100713103005006010390790000b0745921a514035144009451400c0b600301402e2280355031603005401e44165002400c480d01441803801c00d030200d4204101036a01040414803440e10340c9224240b4102ea140043c10581c1005076032018041074810104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 416164694 1250 416163444 416163463
    0x50406030b0105030606091c05120901030615140a050708130e010b0c0a020f150c1c03022104020607020a0b2a151503070e0105090108030316030f020d0903110706050903 74
    0x220349823214036034406010700e550a03000b00144135000b510b014110300c411840150035804c1090320280001d0b51111545001155035003404400030307115004003ca114090002001114114079040d840c04559440d040c2055005200c001c0000c031002008011002e40c2c0c0c0d0189001d440d0072103000349040c0c0600c000985d10b904008010340f01e03125100d502046a0794010115690003141d100c80c42c1c4455240014a490354040e201410000c0d1024062468062080c401c5808025210039000710000d1401c60700a0200c0c0018012038111508000e2600581c0e03451007490001c00854003041d540c1d2400c0b60781c502402440070300421140c000c1811075690a5000304109a6406402c0222100740d0788a08100ea115a006218950180198040819040110000c55050b600240e41a0307039241d03a101e401942ea8402100c0740441600303d44c040c100309520070b030040d035684220218058200407a0304a40002c440105500710081251401c0801405509002d014010440c0e42403c0c0d051584090100e0380321100301 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 416165944 1250 416164694 416164699
    0xc0d05030603101d06280e2419110703180906060504080f07060c021c080d0f0b0103090203190c0e0109091407081e010b03010507050406030b010503060609 68
    0x200001e0303500d8030200284800d110f50382006006600c2c041c4401807940f0203528101c0e005005280000710081848120130507810741031070240e50700c50b1455103040c0080030011105800c074010b0241d25007440c45441c2d00707580f4011507440040b0f11030402e0700112214071041000380e002c25081000012080d01e00e00c1c29182402d41500300802c1d08424081c14401104413600015640f61410402044240e4800302510698468804a602458210b42042d0f82e0300e003180b1500c03000401d025142c60050409a10082da220031400c20080d000347e4a681d82ca290350020b800001c603465440e04072351140c0807140201000d8900c2802e080020381c1203034000c0380d00c54129068483c1100290a204d20401c4050203c0a00420800c60b14000c01c1d61aa4880c0020b0700400506a44a007104050141e14140101d030601c112444a0000c0600240e0030303e0301c0443c02c243c100407480656803030280d40f0f01a10280a054800c10140e510140d499062940250840e1405c440480c1000320034010814991554401c03601c100804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 416167194 1250 416165944 416165947
    0x8010e090a020105072d0606290406030b19120308131a27010204050111070e1f26060a15090b0f1c210f0c0c15020a050708030c0d05 58
    0x100c2c0c54034080812004030280034410860b11b18400e00072264084070a0b90b2a0760400c0584030342c221000c0d071540c807103905401c60310403041000300061402940309404030b07c0007800050085001280015200f00c1075841043c0025040c6c1c00c1e042090390214005a024105d0440114091510745440248880840150b000d00707100340d0124607440008050300e40001c1c48a41d070444191501c002c0e01d03002c0d40080c410130b800f0951141c012103030164080780600c01d80350b03000080d0400307603504907142820b061140307032076070441410000c040707580226000c0d0314100121824030181c984002070301651421a00511030080185410710340c01c0350203e40c1c290082207400341d543c0400d14100c0e26001845ca011407000159000401030040081440192011503003a8003130078110b02610704c201251000200507440740d1001511500160340c50754061803220b0400360240c0681c0e0b143c0d0b51910003810000c44000012005603001c43c0c0e0341d40401804001d4a03000c0c01c020800303181009504c00d0882d40e512120401d00040c0f010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 416168444 1250 416167194 416167223
    0x1f050d0903051303030908070b040303021b0604051203031f05030a111503070903060605090c03040b1e07050c060109180221031c1b05041404021908010e090a02010507 73
    0x4100b064440b469824803030300400302d81d03034030340a0120783ea1886070300b80034080c510000540d1002d2800792000c03a80c041d0050301c000403802000a0095034810b00d11944880f05103c082080d455034001900c4654038600255503a04015104055040003150070314050303400d000e0280300e961401300d9002d800031b03807165811902c904070300001a200044803d000340715210101c2006003403580420b03080c1c2124005c2604100b01c64441061042050b01202d40074011541000410002020016101c1d80003a0750749090004140160045081100650f41080020b801144040e41c0e400c0c00e05c581030041c55112000c200c1c0614044a441001c5541c10f4040c1c800d40381403002128420281d540c503101052090203507030362150580080784880060701c514100803850855449844120080030507c50020360303c07074600f402c1c5440055040741200800040e0840e03000d2103054145c00078103000881c845000e0301c0e0311250790f040c40040713040c2071401003142c20158099002c640240c0d03040b1045a05041e0805c104404114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 416169694 1250 416168444 416168447
    0x30f02070204051303110a121209050106080304182c0f0601030c1508280b0306010f1703030c030c031b0c1f151404060302090a06051f050d0903 63
    0x21400081e400504200030010b1340c0c480300c9070b0941c040d8840c3c0c40c0c1302401100f0000440c3d990886180050000c2540301c01c4052042c080c00e03002c102d6032422a0045020846940c407503080d00c01e564404021540040f4040c40b00e5080303141c1e2801c075110307480b10811500206e034060030041d50125041214442c6020600348025a017404400141c2941c80100c4240796520f240040d40c0305800c0c401c409940822a241d60012407080440c6e9000380b50545851b01400045045149200c07010b500d014001d503502c1c2101e010540301444a68003e04880e8048490545020310261240f4910005511140c00820400491214801c107680d00700b0341140c900c9440c1d5a03100d0050400fa0981850009a00c4000c02c00d10810400001c0301d908104c0740300702d2030030380d603812404440a0798440c100e005500c0301030407818800c5400c0b00e1407120706102e0050010607116640e8000c1403070000181d403d6000c158542c6d600744080e041100c00e43d00c00f441041c2d0b0a01407082c04140041c254002c20350710a45141d2103020780303030505 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 416170944 1250 416169694 416169697
    0x70906061403011a070b0405060603010b0d030e0918010c050414062d09061b07051009050405040510090c0306060b070b06061602150a02060108071d1008010606030b011b080a030f02 79
    0x3568001b02103c5103003440d00b0400d82c4d070b10b02204c01d82e1003903081003807a6415042000505448940c540c842003d48981c0404021701507070010b1450381c03900d90b004006402040b09005101c049050780c0c0700c06645506049120004c14842c40e03445014034010000c41100f018611680782007592207400d140490b844c40000f4a403144a0301d03414690066010904d00101c0700300e00003901c40c1c0c03000384044845156541003408002540c06003001c000c905100403c108a06280c0c000c0c0381c0c0144100103442413014480e1b044c4d011260100000d40b00740f1a104028020003640744140b40260062040d100d062840b40e40d620a11103100400c1103016003804a035040204000c080c1001c5007550041114444c6648180803921903000240a10300603c1010000203010b41e01240000940e10141c600e890103c2070f103540b42540920240c50750b84810400e030070001c0e580900b8402d26000d0851590041078841c5c07918001010410082210080c5105458085000175100c404072420402035040c040f920071032541401009 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 416172194 1250 416170944 416170957
    0xb0105030d0e0607030c0501141914070c1416030507060912171e1e0f0306011808030a080f06270a060504020711030d170a0b06041205070906061403011a 67
    0x40d5824103841c0303090308903000c65051143e000c8801403080c5030440ac45100594011050000c121091400803501d02803044c2904c48419028000c83d129410011201c14a07013502e4010145003e20f5100c002d03c1040824406e0200415051404541190914062021004602d03400904c49034544484103111040304090711a414400d01640292040640702041680c2c8005680300b00c000381881c07003507600c048900580d002c50002c0c0001c40d0869540d100107488103014808030341c0100503c190005803940042008004030103940d134980540341000302c80c0031800130024046070302c1000c1034140121025101750034850003802c0808115104c0e1a1814020000d1000ba00040e4010f4000544881400183c40a8244030b080075421110031020a80007150349a404180c03c0441025420101d610109a0380289442c20002400c661400d40e44901543c143c43c0c0b041002c0b241ca4008407003c108102c514801c0100910300d90418558011241c200c0360060f1005004e40f11018802c140c2d00c4101d60b4191050300e1a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 416173444 1250 416172194 416172203
    0x6160e1206151306060203040302040e010204030b0403020a02040b010906020c01201e071d01030f031e0c02030c060c030d050a060909030810120c03030f1101180b0105030d0e0607030c 80
    0xa0400640c5904604601440c4030301441c48080500030000c0f10348130300811903151394084c6042c40d0543d400c0001900d4605084540b664003448080007150b128103980740580d1007500101070005072481804155080e000f000da06120491070100004c03078012034110404042464081144210855803142410890300908600c0c418203d0000c28604c0c80e00c03c0305c070111990800c0341d00c0b040e5500c2c566512650720441d42c001c020711400040001070951009800c40d40c1c03090819a510020f43c45e64085034590380d80c01c050000710000751503030540c2001d10001410348000d5548900d8421245000c998a2207211190015580d8540000d0407400c81c3d40e0080014085010060002c401981001410920107070b0b004c0ca0115a9401e00080a82d8100d0164000036400070258101d03600d1500c00f41c1c1c40e520580070701d0003403080c904170319034007241c00381300b106611128200ca400888a4a0811901095050700320b58000d0340a140c01ca502107801008010070303450b0031590710f642c6808910f021101c178407160300e0040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 416174694 1250 416173444 416173453
    0x20309010e0105070903030908030301050a122a0e071e110a021008010f0807060c0b0a02161209050303161e060c120b0f01080403081012080306010201050906160e12 72
    0x82d658005d4003082101e000341c0c0e50745a126201e4001c40c1d260700c030a10a00e030344400031140030440e1090035480300c07000d14092a8049642c6156094410320a4007101c6c601054541400c41070000301e900407422600700c101d62a01d03681051b03154003496956143c0c0c03001407041c0410325000c8038000008119200500c0d5000c1c0003406410780c45075002d0041c0400303020318043c40103c00408204000b00041040c229545540d4046011030f00381c0b02d40142501c064101060b541d002c20844a40b20740315a1010310070b500c903200701520540d80c044010300061554001c2c601ca82c0041081c866413552030034001c21004e0300700e04c00c06030fa03003800c0340880c8050141082c0200b215040c40d8185504030340040c1c4845825401c48021b01210091a042000e00700b070045800d8082405c0302c02240102e48200101d90f8410b2072940c1c0b8058154944400700c808803448041265500000410041d07196428090544c020a100c4010003031410705000303440c41c07103444418503010000826070301007042d0b4030710400100203e6084180c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 416175944 1250 416174694 416174701
    0x10020409020a0809190b0408191107080c0f1e09100311010f0c060c090803040b03061315090906020d050a1517030412020d1a040b09011b03020309010e0105 68
    0x2200650408003000c03000c43d82c0203001411101021036a54107004216030340c0052004c150b5544030082502500c01e031001a000d00405100c500c20412102103480c0d2034480d141001e001402ca40c0c5018403e41101e4140c1e00034904801054483d184860002482120261599038980412040c252308840d407866002c1c040d02c00f4031024551481c2c07041c00b56401440342c0c81030141c0800040d10388030314451000001512042806011950580c4a1090100e0516014440c603580d005042d1668006030007a1070008000018071016141171854002d030401043e10620113189407542c1041c205102e03104914050f41c072800824108541d45d4100d541074180e60500300218100a2a220001c051840380700425400c40794012901901c24416100f0a1109038001e524003801c240301c4107181d655034400bc03a01f0080c460101000500c138404544140303585903624621614141c01e1000c2c01100140c060190399141113901d0401c4240d006440705408114200941e582e00e94402a0340100b007220380203803455103483c003417 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 416177194 1250 416175944 416175959
    0x19110d08121506030103030e0904021f03020d0515100503090a06020409050105040b19050f01021009061401270207150908030105040b0109140d02030f01020c011b030b1e03100204 78
    0x41d18000c240c106004080c035480c1c0000c1c08040c4c4828000900400c210f1220007081b8a0070345000c6920903c0a44950719846502c10b0000740501c4044000c00400c6d0049605441a00c1a2164950103107143c0034051048142d5408910366101013001c480130800000005801d070303102005a107000a62000b8110340c3c4079520051040103040a0244a200c2d500742160384d1040c1ca071680c003070804a0090900c601001e480e2001f04034803900030b010313200e055009543d07030145d1050302442031400b0f29000702c8011410040024000740024016004a164015400c0e035425400c880702c1c03130000741040742c000e0041e0703180386a0500100f07407808074075500c030440d060000364401c104208020f58100d410654050040c0e07004c18006541d501254002c2c514080b040e04038000b0185020b000d1200a240040c050b580042100c18880d82039030700000c0030b00f13203c1e0744807906c510300520500706490090348545010801101c21400144014449040c0c20a01c0c031074010b50503013281d030180041004071a01220440d40c40740e44040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 416178444 1250 416177194 416177227
    0x20405090708061e0601053406110a170108030406080c040b1308011d03070b06011701061e030507021b030c0a1d0606030103050703080706021e071419110d08 69
    0x1400002000034000303e2800d500403401e99240d4440810b040c2c40b4482c02c8c0c034549004829444020112019510b6010041840c520031819075007080b040107669440540405007001200e9101204028030300c00040100000c00700c20340d0140c0d030070f51a08000a454052903140365000e60780148210120001c0c101f520541000000b20464107554024800c601c800000000b42580b00c80c101c075120381007005003800240e100070020303612040504100620020b0f62050344a28903090b0404008601c2660042e01c40f8001c0b03010803d0065075501c0c0c04c2c40240740000e0005e40307440c208002c40300c0034100c000382114156000e2200907513980300684801041d9695149903060850b010b6400d0444c04c2d0000d0210f401d6041400449060b40d4225001b40a070368510754800031150b00c40003041c0c0d003040d0301340b042480c020460f40b1030042d16141c0896054a8001c141010b80c00c00401344011185503029000f1002c2e20b000c0c60b1031408402e41c000014924003415a4041002c4007281d810040c1025400200300804144600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 416179694 1250 416178444 416178481
    0xe041b030b0108011e0501080a08070203013201050f0109031b030b0c0405190b04060c0c0905010e040b06030f06070c030315270b0901030204020c0a020916020d08010f0302040509070806 81
    0x103607000c800501700040031100c080c00303800d002d60000d04c0c0f107a0106044600401200348013800004d000088a0b0903905190015212903580400303007040e12508008220100d400b400c401c5800e00c0d4403000d408006001075800d44001840800c00410304902d001d0003411070801190810160401c0b842c10140c00d03c1640d229005840c0b242010034400e60f001c007181900601074600400034140360a05001007602c002203031400486040031080400b2400240d580a014002d1110300c0c1b5100340f6086c2460b21140d01c01c401000580640d00848030700340304000005505800c09100d0501e55102c0e038650804502800010340500940e111080380080c60b01700500b0140440d143c550b007000c481101c003040203c00c2d00c10300b5001c03030f501034905401400545015401807280c0080d40045640b82e21450340814a90503080320000c0c40c00366002e444d0010550180705200d02030b80249000e180070342c1004500440120700c1c0c040a805181d8800024404031003c10800018043d00c40440d4403501e00700b15014178008480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 416180944 1250 416179694 416179721
    0xf12090f0807050a0e09072123060c03091023181b0402040e07021006150203030a0b0127060f0801140f0f04060303050306190e041b030b010801 63
    0xe04001215500070440c00d0035243d0040c11100001e2612030301120400f03014003804450b00501c02c0000c2c05c0056840041030030b00981c4150074006600b8107103d041000c0c1c0c001181d10b18110b000500728002c44c04200b03c1d41c810311841d02c0c0f944a8a43c11441d03441d2501d401c242e062828545803581101014103401d95403100159042c05546e076443c41060b950740b04c4955203a00d49944484100c00c2c40c01c2c00524081d0000070082c00050425507100c8008407440c0050b1074210158029070104608050b050285402401c03071203d070700250803800c801c020b41d288002841c2100e0035644c0c01242499a00c190b06600141226503e070500154040c05510400c0d500e511a0f08045032814a4a1220750700034a0a54103e8810041101c0031070340030f1051002c288030040110768820450818040e040d90b0707621603a806180a40d8640b81c49140c1801071080c02c049072404409480301198040040c149240c0b0103940c45544a01d2400c001003015504e00e00042d07242c3c20052044500ea0300200780e88205612400300704036030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 416182194 1250 416180944 416180969
    0x8060a05090a0201090e0903090621010803041d0406020702090106051b010b0d0b06030a12111216020105070501060305120909070c0c0b0f120a060602121309090f1209 73
    0x21181465500d020403900213001c5401a02c0130898514401c214590044011b410749150489600006900354050144c0d0440c40000d0074015a4180c05022260302501510009500c4c1c581410b00450484080020440705110110002004c21500e03805640a040d03002d480c0c500c1650310b0790300241c8290400414600900c103655900300002d90140101880120701421181c48031405407941045444020901500351003082d01c8000010400040e034910703208a640c1d035469129800c2c40803400c011800300d2444c61850144a00d410f2262000d00b001e003141d0342400e10a43e03030000ba14060f805040c6903880504103004a10010360300b03680040040c20120000c84000c03001c0d07940d2000a03581d44405902c040c01c7c0c0f0303d407190b06003d0050003400401c0440d4022001c01d0910340303009915207072010110340d4064540d864903003c01505404225000c1000c0c005e0030703030505140320002c48014882003886034062440c1c44407400000d01111403810500190444031490080944000c094504003481c0f2400005198 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 416183444 1250 416182194 416182201
    0x102130315151511150612061e060316030b0a0e032d0c12190503070f05071e0c0503060105010f1b0c0f080a11040b06071205090a08060a05 61
    0x8082c4140c072070200400d001ca03003840f41010b410030a0b0000c907038104800c0c0412a541c090203100200094002501e8030540002e181c034181080c4005078400055000443d4018400e101c10003106004003004900e078408001c00300da49280001e440d0401d940020711b140d2011020100a0009144056100e45003040c07060010804144002d07a403403003500f01c0b191031018141c0714400c1c4841640c4490500000c030798401c9040c01c010821007070410302d500c0d00154200c0b0000030f50111420409201c600d10701c6039401c207036046182009010784040c464054090030080c00141100400c180c9a420010f80a2241c031100303014040c40c03170b1109000d0128002d980c0700b48619000091a98031864241440114559079540b254168415001a10b1164041120140c01506011030265800e5000b2001421403100501d00c545003414215014110007668501403410021a000c150300c1e000b045075083da130300c00e078620002a0107940403200360007610700582c0d016104550000f074a800000b00503005196070442000710342c6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 416184694 1250 416183444 416183483
    0x322080c011d0d03111009050c18040305070807141e010507050706050903071208150306070e060d0f050c0702130209011403070909020703050a02251a0c01021303 71
    0x7a0b10254400d010075560507880c22600b0016180d83c1501e1080c18919a1291071920040c10301c028401c513400000d0391842d000007844020440d000c0b12401c1900e040841c9144848048c244200042001d42401030020f013003800c00030058100c1d480e8517040b92a2041c480040e80445880e40b0702200404940a40c0700c80f425600e842c180f056600560081d01c030306160000c00d80d40c1c9000b40c50001e120407080c0c0014454100410034501da1806210717010b507118602407801135002178005001d110f816000e580408100036000750802640e081100044551079201da4120034040080c0402901c10b4a1590402c8180078445111101a102d0180708032110300000010201d03000481c002c0c00e40c0c00340059401c1c56803604031307a4060019a040009132524045060701c50040c84180d07070150104400080c3c0004001e043c2d142e0501481c00d03064081030001185106245a1308202c640c5805920f901040c0410303e42c41800c107500c00c071004018a031f00203541b0b82102c1d0202c108001990300c42070f120710400040b09101030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 416185944 1250 416184694 416184707
    0x100305090c011b08030c13210f050a0204090803061302030f011707090203040c18020c0d050c071701050109110f0406050a090518010f05030a0c090e0322080c01 70
    0x110400c20050811008160046840a080340ea10b015034084000b0b0820201d0400301c011807041d1114010980e5580c0d4200480c88094687e40c00341c8103461900300303000182c1d4820380c0c004080744c0d0000c00340704400c1d40d10700700142031070003114000750f1080c80c08030580100458403001c0d500c2110100c03514005419010001002e81c0f0003120580c400c9100400107112a4104c5c105001c00106842c0c2150141ea4603003010000306c0c3c0c829901980c4803903080c001049036803651544441e50000d901c0080d42000c918089403540ea032144100e91040c04004030781000786180c10444c1c1e50081405031540b43d407080000b00c003540202001e004051105003803000d0b82010030020021600c5c402400d18505203454a0312030104ca10303802141c017120400012071000a400d540301310000e020031070f10f022401040e51422902e503a00c0704450b0300044c000c1d00505500b4002ca14030078455801c444580d94080307001034240e030420381140b00302d080311070072001e03600114580c80a400a100c0c043e50b120004844840c0041401990310 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 416187050 1106 416185944 416185951
    0x803181015060302040605090409061b08060406061b081c0203180c01090f03110609030f03040f0518070f030f1e0605040605060304030c1a1302100305 66
    0x180c200101d2410010b1035141021460185002c0014240b4000d581c1d0f40742c82140e540c407002043c803049810a290840d50640c0000f00b886031010050541e02c01075403030a0049140c4940800c5250288000c01e4401080508450000a03a66114403541e4044240a09158081144d640f841c0420380013070b5010790701407000d0451036205e1503245460210203070542410050310140401c0080c990002e0a400d49812000360390079242c045012030054881c001c00d558161240100d0582015000b0016106862180c5039659130142e680080002091441c0d0581c401c2c0d81101001c10740850190340d102c3c84008503070602043c1c00410086442c1101d1241c00040c620300c0c1c04003c1110b0101480c4030f01c2c0301400c01244d00b0002d4509210110b00c0a000040c401801c1c40343e0005440c080c07018020007500c60100e0254415030625105002c1e02c2503100c40d1008900444240c00e6072610180a0702600c2d11 = true := by decide +kernel

theorem cover : BRFrame.Cov 416007194 416187050 := by
  have h0 := BRFrame.cov_init 416007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 416007194 ≤ n) (h2 : n < 416187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
