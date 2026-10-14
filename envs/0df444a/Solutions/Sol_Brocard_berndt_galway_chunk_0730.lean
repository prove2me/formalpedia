-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0730
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:27:48.123439+00:00
-- url     : https://prove2.me/submissions/b7902a0e-f028-454f-8e59-4d3ec91c4332

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 131115107 ≤ n < 131294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 131116357 1250 131115107 131115109
    0x1a0402030c090307060908010e0105010b0313030905040c03090b0a09050c0d0c0f03141b03100c0203070602030414190c030209090f060f150109080606060f12090105061e0f 75
    0xc6410031118000035003030030300c2c0400003030518090342d12040200705240410401510203002d40305015101c7c20080102d503240881000d040d10004101c0550190341f032540f00d040501440040c8090040508100f20481030004040c00404410354261031404004000426201641c029074840a910001a083c4103501d00180310718110840422500418a03030f1000c6640c5081042807001107002e086922802c071001c40741141024851380d04418071b603c54008500498a0000d0721000340c0340803080006e010984101c080381140103447d0021700d400d00000601c428483c08900144035228000e0070f842d00301100b100c0303410200310390044c010480161b0020400240c601183c0065100340101c0a494440c15210b141074103150044132011241c8801e9414008105c0f503841c20b2000400d02030912151850801a00c40d5449000401031449402b00103940c5d007114036510240d80e1400303210a08003026041c040140b07400b030201240e001c0d0141c0192010030740345d147e403141c0407030305904003500340340017854914 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 131117607 1250 131116357 131116361
    0x11d0109121b06020d050a0e0a110915030106150905060a1b0206071407170d021002090402160807020f0a180b0103020c03040602070e0106092103170c0703080a1a04 72
    0x4101503008464110800401c083d400140700002e01110000364900d4030103404c3e0101c41000f007030b00d4000d50102d981c560000307030f000554100038002250003076502d035030310050342c0b1002034042420358155090400004140c2001101c0c000c0810158881e1017401e52a002804010b01503003991500040049602c01042e4040440100c5c00a0000d040316240880c50380ba201e18500204807540c040b80d0040104012504036820b000c5c803403210050103410b405800840082d030f503400c12411051450307400030380d4032285ea03100ea044802009114402054650440c2420100c541200b10300b07900031000c024900c001403034040c5c40c040c295000d44000800101030f428240c0c00404a00580c0e80c10301da402c002c0700e40840b6040001d000140010b43c02442e00030300f04404101e04013410303030180c0140b0484036001d0000440c50804200a00714440380450411140d003003c0310500c00c0c41500000080d000c2c41800301c0c461a010090085d44c1c000c0d100e80354203803070310880c000c210344805c2c1c0902c90020b00e0803103560042ca4a5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 131118857 1250 131117607 131117627
    0xa030f0201020102070605270601140f030f0a030f030c020105010f120f021309030e041112100504050403050405120a0b060d17030c07031b020901060f050c0f011d010912 74
    0x42c400141000656a2440115141641d85046905801305800d4640c0003400c0d07901c51906141740500980c1d490010340307040c554443d95615100340c0b030440307500e1000e44040000002d900c2e00d100403901c1070300c1981005420070101d44030010000781041c3c00c1d10445401400b83c0ca04880245c681c0d00c40551511055042d01a1118001c45164200c140c010015035240d5a20810011090b040000c40c0415450040c124410541400d4060350600b10b501c0c80305020603041d6503640690724144105640c03510709810001500740c118640c0246400244400c1c076500801a0007a64001d8900341c8a0540c0c08071150382e11480a10001c200b42040c1c40000e50740e00f4481e5108075103511584100001280350301d40711507aa0011180640c18110204411041c1640000f0074800c0c1c00b03407410110402001500880d0f000403050150809100540902d506440d202d101155281d5884005481e030407001004c03403601901007008685e030807002e07401220062000600c56001d100740c4c030941e202c0b1130b0740c10964151804520 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 131120107 1250 131118857 131118859
    0x2070807052d09010305101503081204260d06051c08090303091201050609060118030803270d0e03030f120903040f270605010f0305060f030a03120f0203060a030f02 72
    0x60141c02070380381d4030743c58602c5020710310640c041c0c10a10840c0d090001182c00d200c2c2e8488142000c21420000706046000701c450007540109500015915400c0c141248003690385d2540744001c0b8038503280d041031002c0002e0007140c0c08024080c8040d0365100100070720044803c00c41b05881009070104400502240002c10039088082c0a40342000c2803100086c900002c0c140044160381d44620402c0a2481c19041c912362100782420000d03c2100059000c030100c000500005254000000124000240c5402d0b06484440c0041c01030340030524111303100341c0318940c02600b84003040140512900c140340c00f2083c1c6400140454040c0e0801c264050310010001e005040e011681c08104404625411040c1500c8007514200349024583d1110403440c4d05c10054109258415a251030401c1c402d40ea40f25000000d154050320f004a44c503180e00c030001e0185003000c8803842d0f040c8103000700801015040441c440c80c1c0c0d903064100300300810841541c4000d91104880c0c03103a03c202c0e44c1805100203001040c540b034480380 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 131121357 1250 131120107 131120179
    0x40209030c0f240706050903031e0a06090203042915010c0c08070f080601050103290f030303130314030f010308130b120412024e0a0207080705 63
    0x1070500840f10007100d080e001106400c000041c10400c0c4240e0b8003c664020078054000c5d0b06e5403074929105a41c45000352840c8240421000100c2c40c80e881c00e4100c0009000c104034215501e0a091402c06424003044501039100e0855029080000004080c158420214600d81c01d0741c6044601c011181044a10021281c000c07500c4401f04030784804100000c00740000c0030400d0001820104401d203402c0b4142d004074109401e011091449800601d440d0301039801d6104840382070004400000d109114080d0b4032500341c44080100503810300d20b0031505150500a0b00c8028400100d45004004d500c0100c1c0c0342d40c030b50081d00c1c004000154488004010b04248142c01010240c0c86503c104036030b501503211410904c0340c1c4018441808200703840c4883c001860300007044283d42900143d000b40d542950415246000e85082c1c00d10085042405261100c0c480c0d80d2800d010044a02c4035201d400400c50b0100520503800003180c0541c000030001c007940d8000b806c1c10285c83d00718401012810781740c00d606035002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 131122607 1250 131121357 131121379
    0x902070204020715061a03090d0e040e010f060614030f0106210603050a02090109050f010911090604030c1706150603040606150210200d020d06050a0902030411040209030c0f 76
    0x812034041004041c1395054049a80f9140070304035104560204050000d0780e40c00c20034001694400940521000f515003071420808903440c0c0010000d15600140121650801c2e00c40c84401d61250b200f0790684031140c441e0519515034602c4070700c150104442a0304002d800400500c4058003450070305010b001d5168088010800d5000d400d01510f803c0d038411909070340882101011440d01142281c00b500150074108241e152a101c0303450300100600c1180d0607155900701480f4501c44200c211a980c1c03c0207421fa968581d46d0749010100342c411440340a4494180b46042d00c3d201e00085025400b42940860101c40d0383c62007402c108299102910444840d541c0765400228a4210014101d2000160300581503c0340c0c1d07845440c05a600e04c00c40c07103083e0541a8540180900080242e84690701c2c400c0c0d0050315a820b000f0880028a4580c10099002d6055400041c400d10650000c40c071443c4121276100b12819405c00b0b1100307901840642691503006402040074604064030000c0800d1f8008090010070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 131123857 1250 131122607 131122613
    0x150b090603040c0b1b1c02100509030d06030c140f0a0608061309060504030e060307021b0a170a03030e01050c07020409020409021e0f0a060c03121113080f0a08030109020702040207 79
    0x345d02905000038120912140c082506009010300c0c080b140c08518108030206c0c0110000b500c3e41182c08107803070741d20f82d11004a101c07070f88204252050320090050800c001c80d16814103c160a1091180060002095601081c242080e4030754114036903015000480721410039400303a40d40003000b00825004201403481079107950150144140c400c2c0580d000042900b400e003402041c041c507211389103001702020030a00c0355840c2d00142c460700c100c108041040d031450012000515552580e404005030800360040c3c040003141c0400c0d072032a014425101003040034450b0301520300342d40c1308540c0e005850340c0502c0f441d409401c050708107010703480c802800040c4a031003950000e08a600d10449203c0700341c00000706c154090074410516140a10100c0d800001d50340760001c001d1101003503440013010425100c4520b01004803a8100c004401e035217203840b0307440703d04289445ea1003003110311880d8114031541c040c0d0b000d40078010440043c4503401c105010310b140c0c02c184100010354081a0100d070810350800c500004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 131125107 1250 131123857 131123879
    0x8072301020d091104060f12050109120915030c050a08040201120f0f0609020403020312070302031b150109020910140909010e06090f131203060e19150b090603040c 72
    0x3070341e0201c4400283e8030740682069510407030304c1130105000740d1601200340990480200c0c150201d03044c0d031000d1200f410407440e1840c058134405030000c0c050070007611400380e5540c025003544107603115881d641e100d021450313a085045d80c0e42407001c0790200740100424001b0600c501e41c043c1d8003d0042c1440d0080000700412001201d00182c018044585d58010210281e03105000304401056488810350038541980c00080d01c503011070702c002d04850307070019031481090700a0041e0340840010526040d1580e80b40000503858009405004e11102c60f40300020504103224426182c1c040750241c018010511005c1c000e43c0d5040b0410b074022048202803015407000d41e0b41000301e038042c0014442a85040c14550180050110007400b00c0b10941042020484444212280322040d0358220400e0300706000c0d1103c094000f000940c212a14030f400381410800c1070b00340440030311480b16110b102001541e030f902050032100c1b601da005420000804000c680b4051601d04003650b0054040d200f1004c00b0740d40e030070714012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 131126357 1250 131125107 131125117
    0xe01140d0501060e040902010203030a09030c0510050402040b100219020a1a04050a0801020a051c140705070b0f1902030a0f020415020c0307030c05061b010507050c0601080a0807230102 81
    0x203800351910700500c82940d100f81e510760906000e84050101130b209500107912400000c0007191100c3c2d1340c90b0420b040c1445480c01c1d4840340c1d00041590a02041c0700414070161401310340c140d0055040814501c00344c20550030307001803501c856014082180303050100000c0420580c0060b030380084035000c0807909a40c201ca0008100b07190a07003081e0781b0307403411013441104881ca5022046591050080b1a151a00b200440c0c1c1e440c242100c4c6018400d8100560388010031014014003058400c00c001c200c0c0c8035801c90010030840b8000c05808060b55100044490300c0101222120100c130780c03800000840da64540c02541d046070b10305d00042001c00750a4402c0d8101d0304254400c4140455030000160344513014452580e110724194042d01e00c0c2415501e0b11440901d0034402d050080400007207401c108910041c0e40f01c0c208201e14000c0c4003e04000c6401403258010a400c4030403400b600c000040ca80b040003c0541020380c1c020001420940c1980b1052a034528154008040b0704a036000390521440c00e20040c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 131127607 1250 131126357 131126377
    0x2010e030a06050115080f0103171308010c05070b160f05090103090209090a1713060e01020a0204110903100912030e1509031b010203070e150f070b060906030d0f0e0114 74
    0x40703000410010300900c0d541000e4038910002d08684014008108080c1400ac1c9101d18140e1342d43e50707a138041900c80311010310381c6d203c2e40d0380e54030f000380888445a2000c02000c00d1070041c48101c1d07854690b412184008459200c04401055210f4030021640d4010760143c460020141000074905140d500441c03030f03115003202e0b0104540c100c4060f0300100301c1d860042d80790300f00341a6002d07420000e010024603900b82e8107020b058240b00502c1c2110301c05178401c04c01c910203158080c0081c04904600c0010035059084074088511902400d24048590780d01c922425801c05d80080600500e82c05030b9000303800828805503912000d0040c0c205a4504200c803004d0701e4000c1d107038600119660b00b0039810b6215902c03500003400109900410074414800c4d4450403c00301d0401c12110009d150f803104400c0303481413243c00346811140c1004a1003100b403200c41c000d6144103c0d8240c0d2a410b1a6035080101501c0712960f59141c0d000c00c140c031000449407032183d0014803410a040c142000143c02c0281800b18942088840d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 131128857 1250 131127607 131127629
    0x1305011d0d05030c16060e0112110c06150402070507030611090901080d080709080607030f06051002010b040c03140c0703050f1801021e0d141306080108061302060702010e030a060501 80
    0x140c8011390303003041880001d6500da003801030300904102c2c00614000440d1802c504008010742002c0a241c2554481c140c0540312155859540210440c076a0b211381c41280c0054040304000600d0b40c2c141001c0c021180c54950113400f41c074030a4213681e1094020001402c10207070030071085c0705c40c03003454036100501070203031880e0be0041c228030148420040c091fa6000703165270104020f01e0303030400801400041e10b5400800c14140455403007144000a0000d0074940d00c2035500c41c1e00c09000c001c00700c1e019800703000204004e0390f0078084030300c0081050b420b03219040c03114410440280e0000303955005101c05410124800d181140ca00892600c0300000c0350000aa0880d204003241092070030356804100c07450407040c10170b40f001514110900001d444495038040d10b0148401ca807500c01994002c42c2c2210410124450b200080c640c03148001001e581c401d004061840c270454000ca1800c200c61440980c00301d42c01882c85181684980c0111110645226141e0b010f204804240000030001e018060192034a4180 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 131130107 1250 131128857 131128867
    0x40f0215030a06091503080901030f06061107140a15030905060c091c020102030306060703020703020303120f0a020403020a0b0904090b010e1b1201030204110712020d0f03021305011d0d0503 83
    0x6103070403200c507039010a1229140981020078501d28170b03805002c4030b400c40343d020b40750710031040140c0141000407101030030603240010200c0c0d1590401d2010342000e18020446a040780c503601e000100318020590960720461114040007a1103030b81a17888100025458041005020b42c2c2e07403246000400c2d00c07240a8090041003138004e9080888616014100d02e2580c04001c02998002035203030700c0050503140c0502d0b00018080189402080a60010b607070142c1180e03950100f161030159100340c1918004001c400c0c42c40810b51890940c0291020b40c1d800901c3c0c02106450044844007680c418481960001c0d201d201010200f80203c215500814011180d8505c61030607440200411032040100b007040035082c040c1100f00301c04061040c3c15694107490004140308502000d030070381c0c010a00300601201d030718031640d09210b40c08604442c00d4140e5459040c94035041c090f09030141d004a8450b0752020305020703810416580300396094014503505a070b104030000e03405404600200041d2506846039400014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 131131357 1250 131130107 131130121
    0x40f060903060c0807080628030818101b060b0301050709080c180f0a140403090f05060405010c1112011a030c0103020304050604032601060f020d050c03040e040f021503 74
    0x948040c4202803804d0304640c40c0030240135006030005442c883c0201d00c0c6401844110a01c00d41d10318860140043c008589960f82c41e00d2942d5a0103442a41007107501e1150325070043c00c0000250301411100c2d119001c618401c80e00b00f107d0303800d200c2410303190f144e25480c091500792000c0c45014011491355680d464500d06003002c5502c0c01d00340e007a00a0081e024003103900c00711544d800c031954001302550000e000f030781c0700d400e0140007a000607104580341c0c1c0c00ea0000e01c01055006003803041160028180781085030385e83c000308006402180b007841d000c94030301350450300083c8580743e0200881c1d0008240348560119420403e0031607a903c130343c6920451a044c4880890b180c100101c010010b400d02c0c0c01d41c0345140030350703906071600380281c401002d00c00c131030415a000002c45001103511640d4070345170342503960752100300604000c800311a80015004410f81d05090341d204008948081c0b03c1500190302e80781c909507421078030b03c1c0005c1c4242c6900710343c880180b00580d1207043c01ca4440012050040d100d042c101 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 131132607 1250 131131357 131131361
    0x903050a090605030601050406120204031703040606091e050601032a1805062b02120103060c0309050606100e1206060a06050c0703030f1209030f11190b0c040f06090306 74
    0x60003990912800748208174041e070707004044409035076036464000074204105449401030700680c0c00040649200c080c110a0780c8000c1800f45100e40d004d560b041c051ba0303030341c0c07020034048526104070418409034100d031940c4901c459810544e0061010b150001d8a4403003c40e40048650080c60b010b20900e02c004540403003181d0110859512220610058581c14039040003e81c0e10700c03603281040e0841c0b111901041c0752071060021070046420045041d540c3d202c50b200700143c0c0e000240800c599080c6000480c0e80d2103071280c4110007469500c174000f0300740ea84920080003250f0100e1402d940400c1000400350186480380079000c1c01d156506402840942802d104002801d48240c102c00c0030808240071100c1c2040000400310b04a82c1c050a1415801215180881e0b40e86181c002c3c40a0050828006008142d402807119603580400d55603540300c50000c1040300d880d10542e40880c01c0d0400e13050a400d02042080308a580c21071110b80d003c625290355888203c59041283d48604d02060100808100340b09082c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 131133857 1250 131132607 131132609
    0xf0a050c01031409061315020d020703030c1809050901110c0307050d0f02060a0b0a15020c03060a0902090121020901030b06090f040816051006180e0a080304061e0903050a09 76
    0x5440e00e182c01d854000c3d40e140c0d4500300101080d080c40350714406e070824485402c6c04a1b907401c02518055680c0d804440e90b140c007039404410201c0000389044420740100d4482c103000e10100131071020100b0b40742d2802400001804010b402070a09540e24a103140007030300450000c10000e2a8100516210301150070a94100051881154140464003c0200c8041d901141c1568000350ac0c540014140c00002c1c00b04010480c260000f0410510500b4281580c9230000740410070044228100d840e55550b068240080c2c680749074000b500000c0010050290000c2004282d489105106190291110940001d5100d4001b03034005e440c100701903001c0c480b40c0d06202a580358001801010400d5a00307282e0ba6a070035034441c1c0c00c0c2c403018070780a1030180010400103024044011017440c100344000340c1c5039440448003080700e00f104444149442e80e160091100454100c02d181e4128017454116580d540390340002d413204086101c290a40b810100903a00018412030340950b003c0c0e43d0390f50310b80d100071401400c0340c002 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 131135107 1250 131133857 131133881
    0x7170c09010605070803040c1206050a1d120915070f0308010918110a17070608162c060a0c11042702010903050118021809060a0209030f0a050c0103 65
    0xa940140b18076500802140c44455200ca8410742d85c0c1e0303990600805010341500140c02103505441f540d01441000d4020501580c0c0300c2004000854036014500340b003042810540c603003500051820542000303188054105070700c02810f003d00804003c10204ac60f80e0003140122001501201d00b001410f44c812002d502500c40480d04100800f40c400e039410600b010080014468443c0390780304130759a21000d0340c00001304030000e4130400382030394400e0094584099014503000681d030300d00050f031840d1030946010710031445a116203451503007410080d1001000d44c08d034024012640c0c00c9803005910740070001c19041c410b641d00d0826040503442c01014644880d0800d510403402c00d0703644604004d20039094081070f064010f2483e0340e402d1601c010b85d1039410907800078000c0e500c1e000c4800010101e0320703001d00c07950740f00b115a88041048500b0400c400c101c15501d1000580c4040001144400154010143d0042c001e084803103642a0301083c2d49402030084d42160309030840c945004032940c0601500e56607502c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 131136357 1250 131135107 131135119
    0x4060c120203090906060f09180109150e0f0c040b07030804030311190509030c0405090105040b010602030408030405060a050705100903080606070506060d03110d020609061012030c05030c07170c 85
    0x1035183d0010f00d000f1400f4042c2807240000142c0e20200d0700060044035800480a08903000c140d030302c41100350140b042480799046071404d00382a00320200b200701003003003503c12003440014140c41e2803050044000009180c0032080108000c0400c2c0d500300c6401505940b40b10f03590b110a00c0c5010f250042c240d46140d00e81c24543e04003840401101001c80103104210219850256215500d50b00024a04461615180e070007030b2502041c00400001900070310300c154098841e1401c00e903a280c2e01241c0d40d04c00e80c40368030b4040c1c1050009101a00e0300303400034003040b0070300d16102c1e09003c041e450342c6081260400710070707c080c1e07a41c800311010141c0002c6690380c8410203c0f0614100f48083c2c0380e4648507030008084510818810303842c041050b0041060600e006006000c0f50b810700b80c801006551000140e0344c40040388504000911207600c142c442c2400d032411003014816180315643d056400041540c021030307282c0020b21800303400d110100507000081c0380c0307025074111400c0034494203410220b056100d50f01801c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 131137607 1250 131136357 131136367
    0x603050103030e04091e05010204030501050c07021e060403060c23090a0306050a090501140108060a0c14130e0c07020a1d0126030301060e01030507030605030c2404060c120203 77
    0x40e400007a041c403d10300c1035a01290064251030550070034903103007a0000007045030400b00c400b8050154044e0080d01c2c8075000801c0f05880300355041505000e01d1030001d40c00b10348520405050400c070780f2001c000041c00380685040540742d607501815200c0d0481c20100007811126005c2c0308400d001a035880d03640d6400701e8546020140c2000c0344c048955400054003494a035008501c000045500c030020050b0003000030031070340014005500f40c02c0340030320030f225a40c4100800b14008403458840c2d001d091002d9103d6101203480342009202641001e5440b00901041080000b007078001148454421010909055600c850610400c005000d840d008860307202039050241101c1c2128011050542c1d003a1198050840500c0d11403081d8000b120f41c180240d80004000000c0440d004407800240e500700740c03010b00c030a66039900e0881c01c0320020f204082d072590144642421500300f074204000c6582c1c1c0d40e20f0400c02c0c080c0c002906412640305910581c0040c4021105000340092843c1040d0401d40b5071001d14504 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 131138857 1250 131137607 131137613
    0x7022403280603050a20031504020429180f0601030207050f010f06140d020a0b0a09080a0507030c0803120703110c01140405010f02070201050304080703030b031606090603050103 78
    0x60000410600c0d0304440d40c080600024680c0903104440341620000340a007a80b64501145c90303200381841122260390704125528200d4000480c052480c2020300200100411000700c2c1c0002c40d005841660003941c0c0719140c0c0c1c0d003d2150340c00040280b04848459020918000c01d021041014488228040802d00c09000c411a245020b40d50091824600543c80f8421800c10fa03080a80c00e602c10411513107801002d0024083d9904008116812241d000e43c40100d4442403007078200d50450000d50254806109118030484003014145404c4036180283d00d558071815010316006562200f42d54a5001c51010410407121640b02400341c1100d802440c1061001b039030292520780003400d01400e25032107501903240d0006400035030344600d14010090000454004400f1044001524150fa05500f060099030030505240200d0b1500303a41a510107140d03036143c3e250b10b912900300c00f40490401d83c45031506041c1d07607020884503400095200d850103a5a2074444040c0404010303900910501d0b05007001003003c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 131140107 1250 131138857 131138929
    0x5100603090201170907150809070b0c03070f0606090c0201020304060b0102010219051c050112030e01090b07030305060f04060810060503070e0a0c0e06030108011e0501050f130608060c0702 83
    0x16549080210f15100e4842051580c200456a000801c9004c0b03c070002c0461188e0100915010302440c00c01c1e00e60300341c0c4408a044461285110404042e80104072800009400b40c92440e4103501030311000916586820703d03541500d828a101400507900402440240314452084c07500c01c80c0240006c6103040d818426101c200c2030000100028024003060115045010821004a11001d11020001c560315040101202115420149d00050500042903aa540144803600a881e01d5201c01c0e03007010036540d41180580300050001c0d4005034050541d20300ca40340c5000300e0001d42100c00103081a032103034854520449009911891282c0e2001500304950524003021a400c400951000305401d0354140d8107030350012803200c0b4903070090000400001c20040651010314402c8200050780061110384800000382c510038000e031a880320142411004130700d01010b0481e8800402613012540e20f135505490303818041c080f100c0020f86400002ca800c21072810018070003401c0c0c00c100100d100310039004d0300810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 131141357 1250 131140107 131140127
    0x9010b030901020705010c0305040b0912040510051603030501051801151101180c06030c020f0607270320010f080f180a141e0c010c03030603060e0105100603090201 72
    0x1148000010100700c000710203404492420b6000301c001d0012015107000180108021075041c0d0705c000111001c03d030f03100f001040814203e040d000310303a400d29042000f0084c1c80240d01d8001d40070303c0030400c00c901211500e45a4000c03800d000e601c0000f8290714082c180010035007001c003041c0c210044440140140705090b201c240a604051405440c100648056180180b44803440c0d500380820031a454410400034400d058103441c46540c090040030b48150059968034142c2000b12145d8010b140050010f40c883c1c0c074218544542d8a482000302302c14010501c0340d0036020340054031550030008180c40c500860502c80c00484000b071818200808807100c00420703140e80036040710610010314012694001143c00702101056000c0107032101da082c030b442c150780d144454290003840f60140705501d0003000360000072032103910f016002902d05c5040c2c1b58011105880c62000450501d950b0b400d010000c01c4843c801c40c41584280c02c0002000e0411090a9480e401e05500c948101801d0078403040c0181da1000c1540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 131142607 1250 131141357 131141369
    0x140d060f06081e010e04020d0f05010f0f020909040210020a080301090903090f06080f09120406021e0c0603010b0a0512160306080309130504082101090c0e181305070906050406140901 80
    0x44003606e86200098000c94101406400d6004a100001c1440010360000300d0700d58040c030b020050981000c2e000b4050340282a45207500a2a030300010300581010005a0300000d00c45c410b6924401c0199200c8180740c0081e044541126a0f40146a04050700040b520000d0020005803000b01450000010b102a60081172510011082e0010824603181000b00080310b0340440c4140303031500e85a120003540e8a01c0104900e4045410700343c24190000b000c05d40025076603014000501d96800c0c01e0b20103030154030803145681080820000307a5494014800698000d11201d9190028600c20803801811385900d6000ec2c02d05400400c10304900380d8030700c5448004901c4210000c5840e0f42c075410320444c00d004681c030f02c440c4540031000141c0d1205412450714181c4150501c10414100228412100501d000d1101c51300311226007260320354400c0248080307910440048041c040400c00e0360b1401d00f0302e4900d51104280d5500c484003403229280c28090100600905a140d40b01c4410b454006262230318180700d21 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 131143857 1250 131142607 131142629
    0x90411010c021302210109090f03050c0a0605250f0203040909030e10050c1506010206070c061d06090f0c030a020103020c100509030a0e060a0807140d060f06081e01 72
    0x40443d207481c124001903180609046490f1401d480f00500702804484018500e484000e0000c1140440c510444100075003084086484241c1d035039040c1c0e810303400350b480621140325405d0340c00c0001d8014000c0c607201b800300c807030b8030314040d488851003540f0040320b001c4001c00e0111030780000780040d0780042554100e41c000d82d00400d00c55414103064a900680e496001d40024090700314444440d0408010044803010404132a9040351100800a001c81c05840450043e00024042444e291041c0850114213001d200009a0304840e40034544a131190b665101d4020382003030040050080c001e0200301c81048403140542040c9880d0000207441d607070440c034000d05142c0c0c042040203258004114035041c401c001e20742040507041000d03859549800c6420f0050001c2c651039601015820190240c0e41d0030100d5440d0f520349034036511015982400070240c90204000144050802400a406520000c2c112030080500450a0080040c800100100300c0e100c03402c984024071540300d001c0c80343d40341150040115 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 131145107 1250 131143857 131143877
    0x11030a020d0803060117090106210309121103030a0c03020601171e030c0a06090605060d030806040e011b080f10050306010312031e05100e012304020f030711060609041101 75
    0x16500001c204070303a0404200c408041040104c030540c4802c040ea8446002c02b00c420840b100301283d48900940010005007040000300104200070403803030030700351017184817541c080b8000b00401d186130032200100300029185c520050606405020943c00351203000b540582e0a006184d06603a0b940f8030003034070b80842159000440821000b031050701c02c8850b00100341c9500d0f070f15a082c02406081c103088190350051034500411031528001e2424900340e075058881070070958846003004005e12081d07048039410b548580c031011103030700403680b50142c42284d516000002e0410b21003581450000030400704d01610104400d00160b40e0000f000d60450b44e00283d40203581b0506101103010704000484a102852240084070f50704516810251080c3e8007581107840c2280c0d80c0f084010841d000f8885d07448400300011821105000d018410030b14031601070302c0985460071006041d001ea0f0700c11a03074400010203120400031424030900c031407a0489003c447c0070b00241000d855000d05070360300700c0210707040c0000c80710 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 131146357 1250 131145107 131145109
    0x503012f07050d08010602010c020c0904140c0603070903050709050f04020d03020705131b02010b060d0c0c02130e07060509030c040902031911040b0a030804050f011b0303020711030a020d080306 85
    0x40380d500325403020607240029810300018080c404d080c010380300076500b840507681202b0b1001400c60348011000f802100541c07165281e88842000344000805180621404800c00d40c41d404003c5000d508169a0020030078a54200b050400b01c4c65000700c0f01090501d0113001018407c0c10311140c0054040700c540030f4285c3c5c2841c0c16464440c140e070249420000040e0841c0844029034031200a403800403070942e500709001c8000701e00300c54000c2e08260748400280f04a0b001030080b0360041d0100d00d21800c0924913212107400049081c2c81035607c1400030b5480d504e8130410103500780004e200030306041c1031403401d000c4400d00103625a4070000801c1c0c001d41c3c0c0d909003402075550030800200b00645800c8054040c002904104003004444942c581c000e0b401e040c1302c0603040c01c00c4d10708801101e4001c0d82c91414a030038101048402e0207042d0443e0b0412200b044210304044290b2890500716100c3c0e2801655070f10b9515007040f05001d2901828481e80210a0500141c0c561017625205d40d40d010240c0d0341e032541d5100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 131147607 1250 131146357 131146451
    0x605061803030c060f040210081018060e0103050706020d021b0607020d0b0a05070915080c131e090c05040302090628031103070e0910020d0207140c0a050301 69
    0x2d001c840c81071013904180f0260300002907800780500c1c002c0c1c03420050040140020b40b641032007529500e01c002440c400420007042c1e4581201caa400d03d100020868503078960702180441800e070425551078011150811040340c04010400545290340060310076025104412107034143e0248409026a80000d9100115500c40c0c000c14140740d880540440d090806002074401801c0489050001c07071101200420812012000003490301c22683d03484540381e54a800420b40d40d08103918885c501014030780080f58000300c040782d200d03800d005441440d104a203041e08041c02d8400c1e202135402401002c01c024005a1103071f082d155404141920203a03804041b11401c4c030700000001851418000e004940402003008001c084e0a07200412070480ba802c0783c45044004001c0001e840e00040c5138444103111003201581c0d0043d154920038030000505140d0b65032203481c0c0088940600c20b0080e0481d040e043c01c18500380c0071406c007a081c1a00204a82c24103280c00080e440c03400d8894001078004100d04280400c04c82e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 131148857 1250 131147607 131147617
    0x24090522020319141506030d110109020d030f080f0112020103051005060408010e060906130f080702091501120606050f2505070303080901090f08090102100507081009060506180303 79
    0xc10358020b00481c54141a0083c4400a1000140d030081001c420500d840c41c105c3c0f203000e0352000b00501a021420f0a0680300e8002200d5840865501c51202d507015035110381c00002c806001e44c0b5080078045150350014080c1c4001807400d00e086240300018020009031001c200307001c0394282000100d90315102c08c50020301c80e2070780c090f640c44031000401080210041d00140341c42414801183c0d500d4035410069034a030702d030480e14811034544407074026000c40d0201d00b42d0801240600d210300e207803103e141c02103406d01404848003860481d162a400d01d003540c0c080c018203101c541d042c008009035030400d080148144078281e9001c80c803090200d01040801520001607541806404150f034403010345240840e00d8401c1f52005a020071100d00008151003018000e018910798041e0341207101982585d101440f5030001d0030003604512502c1c4a452203080c59204441c0a9116912854403603e44049000401d10558014040090400c0307410070279070702c0e8101990719aa0310154000c00c4d03852404c010034558050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 131150107 1250 131148857 131148883
    0xa03091a0901020904060b0f0304060c1202030907060e1801031122060302090709030f030f1b0f11030d021002030601020f060114180c1204060b0301240905220203 71
    0x3000040c80003011056000b05401c280548042c01007a90301d20130a0000d0054411a00061a08000060006085034000301c4e5500e40d90034a00700980c80b00881d0b000f02d0b001103c655a65600401050085070b4118007007031000c0c081202c0e5290003003089480301510301c1e07040c4002016103140c0c55900c00d0710341d00d01c800c0d98111010408500d11405691f0307018005090548403e0780190108001f0070b42c243c1c49801e4207429250000303d4841501481e6508441c0515140346480800c8403500b410011590314400006019000b9400362035004030f1814213107260484800c140d0b01c80d0b40300204549125030085030700410141c09000068480e503400e00140e0508020001110b80350003a0400400e14001e00780641000c074100740c03140340c3ca40c8003000c0700c025503c000780c0c1d00c003044440034008003a41000282066034450b2142c840854003540e07041c00309007907604820358111b640410182c025010b10300d0301c800c50000c01503200c0500c002e00b01710101c0103a15080807034646000400445080a64508010482540d6a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 131151357 1250 131150107 131150153
    0x30608030d090c06020c010c0803090102040e0906190203070f0819020f0a0201050a020a1407031107060e031018080304170f0a0e011d040911030a0b040203060a06030302030a0309 78
    0x1058400240180110b07030b411107107001c1410001c2001d41c80040d40300c04206041c1c480a4800b151a210207601d6080105840c520359020800420319005a143d51401890024020821800e1100403c2d402c1105155501c684920510412800c142d00510141e2080001c0c00c003150aa210480070070140711440c5100400c0c64000103d002c40340c10640c005004400c582e0f4000c00c41d079185d0708500401d91050844040020f40d6041c4180a0301c3da07408014441ca500c40e040110780030390441010303400c040540e84a040400c41c920071030081e6045c01d120000464541440c200581c00403243c0300003203070015071030241010001200003000c106100c00100d070f00801d10b04002c3d0707d4071b80c0303524400f1440d40124010300010742c80500d81111540180400740c070b030b0402c015000ca001241d403c10300000f04290b11058075003949241040c04030740ca0a000030401d17035020302111801382c585070050500d05880a41040511450048200040f030f43c0441910300d15801407801084a5019043c40460400c110309040c0031a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 131152607 1250 131151357 131151367
    0x20619020a0206160c1e170f3016030804020d060e070311090f06040b01020c04021c14040314300f0a0b0d1104060e040605040b0a1b030c03060803 64
    0x456a841c0508026100e02005100c1075101e5a440c00080c180c22003a9038841686c038010f00400f2814803800c1d59500307001e811150758521800707049141080b450310340400b40034501032102403209141d04d041c02610122501600d80301200d070080700603051080b0003408000fa00c40100703045546149444401030340242090141109044d00c0d90b443e0000e521003114940000c00001c500c0d800d103500c12030303c140094003007070010b43e83d08801d020207005078119403811402640b5035100242c0c0c0b80d10180c14040c1050000b54588582c0c180900c0031103450054800ba0380742c510041000080d4410f002ca002c0d90701e016a400d8856035841903448005e1400c00c2e155820400b08085040051031246889100c1c000040145c0700c1d903120880708030221034007203114942010841103204080303568bc00b5160a0408040d00000340181e5410341d8410349142640c0032901c0f189c5440c2440180212580c07030300e402c00c3e00a00308101e09501840c01d045072440c9402d4a200307151b269008950b411780281e204200502d1080c00f9241c0c0e80c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 131153857 1250 131152607 131152627
    0x6091c0317100e010504111603090b040b12010605040e0a0207060f0501080102070302010b0103020a0f0c05030c01140a0c020c0906120106030c26010c050301030f0c050604170c010c020619020a0206 86
    0x4a41d039000f400b1461410500008040c5803c3c02546102c000d25408549050744030000c1d89100c01d170074070080d814080300400000d0700c8003014000700000d00c03607902101d40301c0c80141e4400540303400680c070072010440c0920081c080036050400b01600485411170040c4d81d5403140c90117801030000109030240b41c6282900004c0e01040c190028074403a44641d0003049941490f00054040b4010920000001414250240c1032140140c002d09005070082c0110780c1020158a90700b402c0d00ea5180e80d483c181040141800790040481c00741032440c0c4805c0c00581440c5040c10b010820201c030051030b0710300c1b440000030301c000d10728400c1d07021401071754105900c00c0f10203480f40c040365445041d01c0792480601448800350301c09907030306100315502080301da9103003844d50346076880da021154003003003050761080700401d000501a690310000303000512224036a081d514180348034550070001c40001050601141c1000d04e001652000101ca24411040841c10740d0b045903644200c3c540b8221100003508120001858004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 131155107 1250 131153857 131153881
    0x1150521010f0207241406211b0901150e0603130f0c0f05090c040e07180602070e15010f20010906090204060b0a0c080306180703091106091c0317 64
    0x1d117003221020b01200e142001001801c443c110080102c035180c860021030150300e42a103004028468048504400000c032507906420606038402895510480c8884000b00c2e00701034a113280100700c9910b186021200c2400003800d190304084656202d01c1c000000142c12400c245010301400d9042940c1590311750b01494a00d4400240d8003520000c088000700000e030030310706000f038688202c160494203402d00d4079003c20800c0c8010090030007000e1050812102c0110034402c41004018a40d55000340701d60342c40d100340300030107090280c014000921707004123444d51640c012000c052118814604009001c3c07055521092900007080d87d1510ba5003000010b02c1030004680140d1000c600807282084500e55030700f41c1880d9441495056000300c2c0340300040c4404103903250040c5502034405000305d4a1142803501107a1860011038900340860f41e01d50036002840000d101c51481d040e02990540d141c2241080040c80c0104a650b0640c04140c24540031001c143c0701d811640400480c204046000341400c402c0101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 131156357 1250 131155107 131155133
    0x4090c0504080a1109011e0905040201090b0f040303080703050411090601050f0a02070512160605090d060606030e10050c0d0f0e1c030b0301020703050301150e13060801150521010f0207 81
    0x12181d145c140002c1810130004050206000d0590b10f80015075142249000180800800070f030305100490100260703450602004102c280d522891441d580c5065207400342c10004050203034000c040c5481c08201c0002c01407146c1c0075181d042142d005583e9130340e900040760140b08400341c5800384080460841400d640009001040d560100c031080785800f804424036588882d5a502e0144415114504108042c0a140203044000c001f5001200104070f649a038000d4818643c48107000135603401d000c90001c0310500031070b11002c1d0002e50a01450038600e440555502032010020075041c0e41e906c0000b030310034041d4022002d80100000b0b940034a640344029940005c060301c3d8000c0881e051a01400b52071030103100b25042c081c0c1c1519101e06507424000700d100340039450b8080800740464060a00070b25940e4112070b8001a460100100350fa0f030826652909541040800481030992084140110b03507403555066100441001c5101111070300000c007d0260031032001d504e104901c0050841c01b802007240d8042 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 131157607 1250 131156357 131156359
    0x613180212030a020c090907030209010b090141040f03050d0f05030c0a0c02060d06091a06180405060d1e0308010b07120809010f020309010f0501060f0504090c0504080a11 75
    0x41541d081084a5407244149a11507005030802c0b00b9010440c6050500160410b43c0d0b5001c0703c894036225408100d04040030780180c02001d03c0850030682c41d6078000c0c886400a0f00c0d01b0064010703000700407241040007550381c089058986104440108800d46c00c4260b9004001a060035440140d03241451a200d100d10030440700000c0a8403120345056016004690240180520503403130204015400c580000241801304d078410740401100ca2800114001c0901400a0b010b0014000580c0442424843d003207582c040e010346400c1c80188031403000f226103084410020784010645560303203000503420502c0e090700100742008070365074401d5120860750045096442500ca41610b6621504c1030303511405203d000038440000a0028504648500d11503500f000070f00c3c00220b03051100007524400c0e030300100c60a0100d03a540b180300d45404192070007514010002801d0902420700d01d007030f00502c11701c1240038001c982500d410640799600d100d681102c008080c10800e8500355440761030920760302e2050700394007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 131158857 1250 131157607 131157619
    0x30e070603180501090f1208040b0601051c0c0f02010c0e0f15070f030314060406050d02010f090906060c0b06010804030c0b0907050d030210050c09010c0311010e0a0f03090e061806131802 82
    0x907543e07545c02350703828900440c0c1041e160b940c0e95680380e00440e56503214542c401242c1d040100100c20030b03206402440d2032001c40c1e4031080c180b0394065070000e084524030703802d8404102407016940311584030000c034040c9049044d00c00400754001c0d02c0508510f40b1032000c00078130008081120200f0315615500000c000d056a0061180f151548010003054940d540502f40d40030f03081031014001980150041c0700002c0107410100206075855640d40111a01940188081030419800d60208210030988952000e02400c4c030b6001801c1c02e0320014001d40c054100108080990000300390040c0c001c01c50100205002070015110240500d0001e468a0440c51484403c0382080041051b030712105003130300c905400c1030359a83c000c02aa40c0b0110399030108824128029566520710904266041c40f42c00e151354043c3c8903224000480d46002400000d83d540591030505e00304040c09840c0d51000608241d40c021080c0300328a0ba2555000a005441d81110302c000b030078900042c0c400c2d14900c1c5502000c89500807189 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 131160107 1250 131158857 131158883
    0x6050403030908070e1f0f061701080303090a0f081e0c0d030e1b0a0506030a14070206070207090c0e0909010509190b0109110c120316030e070603180501090f 69
    0x44159110154002c54502400b40c0d00090440004803409483d22890074909140159907400e600c7c030340c0c607080c3c3c101c41f00041052511011030548104810300500c001e4009524500c3e1038051a0344504095000800784400c3c40c034000184040002a03030640c40303004068207200e22030740a001041d98400f502c0050075009076507003119010700071300c40c0d1410740320500050140315640f00c124222940307030b02c424660300201c4400301184948405020318800c9986800004444c3c28049044c0c03520030009260b581154441402c200c002507002c6268401c07510312100c0400c0c801c018410076581c1042c1100360940000000c030401c00440d905400c85401456603c054070821074207040078403c1d00a060102802051140d80108184078a0394052a41c0800301030b9224246400b0045060400750700704c1c00d80e5480038000c03083c020081802c0d01c41d07446031441820208014002c2144003a181c034028800c0b041070659074160089a106281c187c281d61907072060007000340d018a89404041000c0305a410b4500303210600c9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 131161357 1250 131160107 131160119
    0xc030b06070215030c04030b0c030405011401030c0b071e030207060801050102010204060e090402040204180207030305010f0302030a151d030d050a05060a0e1b03072715080405070e01060504030309 86
    0x80350101500034018030001e4814056444071130b440070301900580c00d420000000410b51800e24a400b43c2c0000c00703050746e241003034244503081d6201101a101091200001040000c150003034400844a0320318220f602c88035641004100002c00c42164a07800904144c06020554041110000d0366120f480d001c003940d813160012803c0303016074010307180440e00460306058140740151040f40d00c98170081000d854a600c4404195000c94404410820642c010448008040e014052980548085031407040e03194910b4002a6591514090103007510a158603100c2031201990064059005002400240030750418501992540b0000c10011803e181ca00840c1020800e4058030303000b00c20040c80036007034600f009940320200c0b40c041e000c031061001982c890503001340d5180c0a9442003100351207400f0b0000180b0701c103c242220180d00e6500440c1412420f00c20341140c003802c1e2004c400d091421040d555a9840c01520381001500402000103152000141203540324004106680c8640d65400740d446e60340f5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 131162607 1250 131161357 131161369
    0x308040c0e0106120207110411030108010c0203070b06270112060e16030b07020313120317040203030406030c02070509010816060f021f09020a0b030106110c0916020a05030d0c030b 79
    0x302407880058003c0c1d603506080b542c145c02810341c142c0920300310700c0c0c0d000c2c0c5580040c0495441403090303400d0400100041104082c20f10591219020a00142d45441d85546d100d6400c1c000c01000d80e4420880c0c61b0030140611011544200070700d034600740748040348d40c561501c000807c888400403150746080c0144451716550205481c402414801c0c00400942c1c1565207110003007100901500440c882404000c220304c044c880202c0013810f000c2100d15580d15039041c0181100e10a40c604074101001d4424000141c400000319401c540740f601d0300140003618204100e00300910755002c25401680c0100205400c800800c20010455000d05109aa030742c1c0d884054801416150520300560400c0310980c031505880c50590540880445000891042d550300084100c159a00101c00910000c030040c031000c0e400c240c0f464400c07802c00e40200200981040000d2903200003c0000c00c1d01c4095803090086a0b000700720403e540f56200c0107498580940107480c2d0700030b10360f8108200000e402d019400407141001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 131163857 1250 131162607 131162609
    0x8060307121a19020703050711041e0c0302070209040501061d0408040b030703020f0d0501080706050f040311042304050c1008160e040c0527090f1f030308040c0e01 72
    0x30001d102064500340061080b5504000c200d80444040c40d00031119002d0340d403000300f492912030744502d13881b10600d00341851504c5c00300b02814001c4c2d02d044041485800303086200d209200541030301041c50083d241e0300300e01230300a074407001350407044030000e204c10072206400a07020350b56100000c0c10380c8941c00346010b041d0082179802034205203080005224034a81c54000b1030303004c031003801c000d450402c0010381c0740700320760100c01010107442d0340350014040f00c0e000744a00380040c1011724001d4180b11901070107180d68411880020110700500340713980100d44135600b000002c188022010071603105c0602d101c0d0200003046400320382e24006c5000304101031070100c4900e10300110176035841023182d590744d90150240c10720906c00e106222030000c0d446001d680314062030020500300d59550340c90700301f03030000c09203ca001c0502c0e0001c44201c41000314a0340d181e0008180d4400e40d00f034050302c2c10340ca5058002e0750003002031032541c0c860450b40c8004010316800a02850160b80301d442c40350720442d07075505545940142 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 131165107 1250 131163857 131163863
    0x81e0405010503070c02360108070b0904091a010b1b0307030912170309030904050a0c020604080d0608061005130b090720030307110712030e0114190806030712 70
    0x3050004c1801c8512440c01d0910082c8040d05175000301760201c085801c0703407030701081010304990340003201451802c0400c441c40c0100052030040c4001c0c1e042004140c4140a0759000340e0007103030b40f8403c107024401d114012a04060145403a48039650b182c0c4441181070f841122543c603010304140e06080143c030300000b25040b0360f8040d40c800420354103021204100c032540e110140c0703034035909188100035807001c00c1c0258060304083d0011030340c0c0c0120509002c141c54005003080007140c50441e040000355001301d0341580c0140d00c050841e5446040c03040200040855030000d0460748520010071810410b81442e04007901c20844115080c0c00c04041e5100640d00b229290603085400800403481c003030b01585c4401150082a1000e240080d030b41d145080c5141c10807180080051500020050307140b00521040014040303144036007403441082c0d1005013241c2d10452685041210b024810841080c0c1301d810303140280c2103c0d0000200c0c42ca2000024a81d09c420f5540a02c80d008410000a10700455102c040e0300740e83c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 131166357 1250 131165107 131165117
    0xa121e080a02070321291302161a06030c01111209010203040f0f06080609100b0c1213050a05030d08010b0a09172505010e0409020a0f080604060c0f020c040c110a081e040501 76
    0x4100102c081c0070790000417500b9408015840da0b0000107031005404030704ac48407540303078031454a042c004042c40c2c030f1140c428582c18003000c01440b03d0300b42c2c0013003202d0981c01c090002403a611120b14004030728611403980141485090901c0200c2e5030400640c0f44401c413882e85d55030041548544041240e0194195a002c060b1000030f40c0800c1107904000c05000c0e8110018265580d04203582d00044059016207000e01400d040700d4030500030303880c10719a0f91011300003c0d4000d0031004811311010703003a4081802042c0d0780c0d0402040c0d64603010301c141c103202c01800e004400006581025035191b5954140c1380010701d40105100c02540010b000c80e0f00d46422104142d641c020346178000d4007440010300c21203500741d800c0340701340701c0c0484d01c1c44960348820700610403007004000700d1416041c828112164484680100b0018521880920360700107006445c8010440d0000341e42c00032018241c0b03050440400d0001303d40510014001400148005429080c241481c0c03500307a0980041d50748007510541c040c01e07002c01c0b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 131167607 1250 131166357 131166379
    0x30c0604111c0311070b2d07020306011a091201020a09060f0f08040c030b0f012301140903011e02040306060506030603031b0f0a121e080a0207032129 66
    0xb44581c2d80050741a00754010344266903115621121a035022030031103190003070034000680e8940341f44240c1c005401c0c0503411303450500c1480d90001c0d8551106100720f10580c1f030702d51510580103501030111005080c00804440941110802c42c4e8041d400c03024440c40030920303445002400c1801800c82d00424501ca0b0b0303a520803001308000903207907240060000d0311401043c910110001d8400d107403032406a21442c00d203840302d40c9801c000c0c00180803258076402c200e40010803221116600000e551707211014010b0321b03640303c1001c0400b10380142460100e03444094a04480c100c2c076410385d50700600560b8069041801b01d03c0d1580144460b07480207862041e01588208022044807800e40010a1490900c2d42507520701d00046020324981005c10fa01580c0d12100d2003000d000341600b001342e2286010f1100320701c80c01811140b030080c044800c0200401e4200b50000f80c4c0e034041510407650502c00116030400c1480f2402e210344a0002800b44011000b031403c180080c40f9500c901d16130354100300000040c900f0141c6 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 131168857 1250 131167607 131167613
    0xc0201020d03020d0e0304060908070f0807140d0609030806100503090613032001050106090504150605030a2403140f0613020609041406090c0703050f070f05030c0604111c 75
    0xc4d405a60308003202c070782da59440301a0303d078244004c00003400c00b41d864403000d5080030320385800e003a416032041a0034919045c2c10001c400011554000b140c0103503d0000484100501150500410100c01015146008990070415402c81155402100e098960891022200c2030941d4140700c00c0d60f0f0400d199200c03900050700403200611012900b8400c0c54071500c0302c005c80200d00d103580c06000c401e25069442e400103008041c0d0021400005100c1284c00307101409060220b00c50f400c01a016080c200040040080c5000c040750b0030000c440010700d0020013112450156860007040180422900c0c218000000d960100f000180a420040148050704c4540c8a0305009525540c4190080760450000e200b640c145035980c1c40780303420388401e80c0301000766858110208140810010913000c21103009229940100c0c1e40030090360041c0a2001445a81d02c1881c24240d03d04407214000030080c1c40005030701002c03070002040c0240198400d036808106c0e40681020030401e940ca44829071400300030b40c00c441d0f000c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 131170107 1250 131168857 131168861
    0xa05010e1305060412050c03030907060e0409020d020409030516031707020a0b13020a090608030712050f0403030302090f040504080d060603140703050703062115090f02120f030a09080d0c0201020d03 87
    0xb4100a800d1081c509000201d41c6411a041102d601854bc0c00c00c1070204510703a00032403c0d10614404841c10400342e0700a900180350b80800387e50180c001c550360195481010302440843d1074a21400c004041005000e2800034006205210803c0310914043c0c04a2403060000621807020b680c840c401c10002e0351807010000d80f040000106036807203034645100040342d1b011f501c1075102034041c0c0310240d99580418180017140041c2c09203d80c007040703410001d0540b03a20060f016941903035414540036030341d1503d1400041c82120351501c40d603401f82c0381400303000401c000382d4000c0480710030082c2c044c401150740b01e030160300b1070b20400c00c1c0d01d1501d0b460000003503140d0300c04da2110b039108805090004046031118060b2540d0354001c100200e44444018462050003508151802c4103030b000502445491115035a10840d0500700348001d002e01c6004880d200d00c80030034404615001102c004403912002040e40041c10b8040070711500a503400740001300c015091007140d04500d01a01a0001c0c10002003090007140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 131171357 1250 131170107 131170133
    0x510030201140702271305101817041a12070309020d0506091f110d0b18070c06050f071710050d14010617150703060e0a05010e13050604 60
    0x10300020070000040180e480405e0703580c154008003032412405048041040c040381c0060100c085407101c0c8404400018000148400d02001000d008184c0710b5001e604a008507288c4000100700c00e201601d01c04440103500c003d001120402410303101c0400014441030741520440700750f2040182d80c200040e01e458003d81014414520182034400d001145444090400c1d10640f0014595000070030369140c1040b0b1504541211002c42c4020890740e50070f68074000317440c825001c000a1642c0c82da0115020743d904c17a10b508112400c0c0880d6800d4a02d0030f074100070044840e40408803006403230100402d00d5400e0f551001c522980e900e8499110700100c82c0c050742e600c0c2d540140040e00c1001c0c0007001080340e46941030001241c0d0710548492a4090711583c0360b0742942c660703410031103d03018000400700784100009800c80841040c1c10141c0225110304600314090412904500c0107007100a00f409080121944000d040781c01120345401c1a4980d0140340139900005140a4102d80c0405e020802044022071985 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 131172607 1250 131171357 131171387
    0xd091203020c100e12010b0f060a0207031b0b040b0918010506090910050a0b0705010e010c05030a020f040f08030703020d231305030f0703050d0516062004080d120510030201 76
    0xc0100d01c084e000003484141c221102ca05240d44503c40b030000c5050526955881c481d044581904200550304001d564540502c00035120084000c1490101883c00e00d5001c0a8100c0035161a41c131a00c522103d02c07594400740d0000e001381c02305070310096180300c10300903207060700da008000c0c0341f8001812007040b100100180610b04159001e00c0005403035640c0c071070000d00404843c9245501d500d02810b00f40d007103a070006402d2240381d040102c603500d440d070301204995020941440c011f84800500c01c00219601403030300401000701800c48042013002d8000050858281f00b43c5c2140c0744865912411102601d07000782240ca200c0e21801c94500c200401405400750b6034032950045c90003650b40000910b4500b844690b000d20303421164080c8203000e02405120452041303828a240f90039001004284a107118282c0501215500c4c048035168418115003a011559400040780d1290784032054141c03254014a100000b198405204c2c2d61080864003031140304444240d0035402a41c070716001960010040031840f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 131173857 1250 131172607 131172617
    0x4020901090e0901060e0603030c0601030b0a150b03010e0a0605011e0e1507150e0c060903150109050702010b090c040618090e030405120a1121010204080d091203020c10 74
    0x301d04541e2541040d88540715040021901c113146c044c00c0d44241c88041c00a42c0207400402441c1c82c9140700080d280d04480d84200011107e590701c4030044000e10b030076410580d6201c1a80340009906103140041c6040c0c46405004a20395118104810200c0790380b4030038070307001c50461900c00440318000c119488441c0500d007004444110008000707641e40040010388800588041b91490500508101c054100204002c0030032100d03001e5110b0550315562083d21512078440024800e80c04d031001c0c4082040e06004c0350125a6658403541c000c00076150448040c0300640c030b40314032081c140c505910601d00519007604041d02d003c0c00d00a08994044040b03001c80c06100a00d600081c105081d07200708c40c6d02c891008050740d00d6500b0001080001126001c00013a01d030300c40104400842c1c151080384810b80702c215172b4a24810507410002841100214800c07105c3d51020800050005011a232500680070a03903800361116255038840c08a031800744400350060b4445d00204205007040c000306025141c4905003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 131175107 1250 131173857 131173859
    0x80f0604060b040e15030304121b030503190206060d080d0e010204122105040e0a0c0e0324010506031303050a030908210a0b1305150910060e0604140402090109 70
    0x11020055006520280802c0c0700c090170042d40855079100c0a505d45000c44c040c6241071f162064038020a400c3ca0005001d940d00c0b820030302c0b00c65804200801c000e59214040e0b94840381c205a8520004114800100140c01000d0000c0c1d51880c042803038983d0158060744081c2041c504c000300600421a09803000c6496608010200301c0400361105520a140300300c100540c00401c41e894082d442034405c4070442480024801807280395001c1420a0340142c031f42074000b510214001d03046035020003131200b4941600840e0140003003206011a0705c15054001d1368140c90b1031b42d0720014418184411900c4c20b202215411800300044d206e000106841203052030701003042d43d050f45491105512410742c12070b0750740c0e400301e074aa88800b6800c1d00e16803000080404201030074804020a04da103900b0321560761034036503900004184e0001041c03941860b0401030010003181ca80660b00504270f608500400021421120b503c000302d207000c0302264107485400f0200e0500741259000e000180d00500d404030b042c0000c03048 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 131176357 1250 131175107 131175119
    0x121222080601030c060e09010605090411180405010f0e0c213103020d11010908070b040507080d0c02040513020904050705040e07080d05130b0408061b0307080f060406 73
    0x5020406001000d01805195145107010000c1c104194800c3c1d0900c410072210340c0302c956402c407405044458070300f84150784020034030025008101c00c0803050303a04140400d2444802c003200000340350340c1105640030002a40c0325a40304e075481c16a032042e5540380d4195000100114280350282ca010760100c3c02c40c0146100b1400c05990003401203440d0400c1107000911541007031201c3c00e880c0c1501c070656801c0421282c036a02c0080d280c04100586c08244814485600e03008030095004104158100000e40d0301d4030540e240803031101078203507030568051103403030300200307045d10041485d1581035040d0300d4801e00c009059080c000a010010701c4082c580c00c0600e074a002580780c200a86104620403405401118100300812045800443c0c0340040741c3d0002d031042c4200c0000292200081d901341c00c011781c6038a490600b0b0f40d0406070355003183d2a8610003040000e032003000020080d0090f00d0480c80c3c4004891044e010080c00d020403074079a8002001d070340100b00038141e1038106a40100c405003001c159551142c0e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 131177607 1250 131176357 131176417
    0x3051309060312030606030b01090302120309060f0904050108031206040b060c0a0b090f0d080f06060c030a02030c060601050313020121090c03051c08070e040902040612020a051212 79
    0x1a00c01da0f000107028220028595151243c10040c1803242404c0203034050802c00204103104a02009004010111915508460030000d41d5030401c4020aa0b5589022081e41d24049820040002c0c1c050380c10b150001c1040c10011050702c0c52405c0d42021010b2541e52038040001508000d400c40d50010400c01819400c1841417103410b40c490302841180803541007062440346049000641009aa009040103800140d800f0001030f40080304a0100300e43d0b80c80f003500107071940c818081c40e01613511000600c440041e40100160881c80010340940303400f55200030041d6586c0c03200300c0740240c00c81e0601490000543c0164185800207d12a40e50040140441c070038008480e80c3c02401d071100720301d204040040000800c8070a41141d40d581c04081036002924002d8210340c40982403000b4001d510300c2d40100c90b01c59500c2216001c0d0020024044c03541d4034800c900e82032040c003900b03078011100c102c00450f940c1004110154004440c03001454036800000c840e5486070031000b180440c40300241800751401141d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 131178857 1250 131177607 131177609
    0x2b0c06050c030609060603012105070806011d1b0d02130f1707050d030c12051c0203060316050310091406070e1908070b0903031909080c040b06070305130906 69
    0x7400c10907500c0c1443c004204101c40000c040d10f2040c001080107005020104070389003108a4000040d0780a044c03686011418441c240d040100644540e0000241d85902c03403101c19801c0040d011140919160029030640414a21218043d480b40400c00080e510040c3d5008050318500c1184011020340c5030240f80c2c0302c0500355030141040d40c1000c111024641010b00c04107000b803500f00e0740009403524596021340808401080501240c1c040314000914a01800841d8803015802c00c01e0400503814040c00790094106854031070080c0316144044880a03c58540e02c03050f00c40050003803d100018101c42e02c05050700b078204a80d40e0010564001401c0400c001d40c90140121392251a00d11402d001070101c2114651520482003a01000c00c1040780800f0600380d0555184803121956061040f0110b4a540316030788040d014144e540445030703921603020410b81e09072069042665444440c40b02000240c03400040d5841c0e2100e030800070540002d018034006c005045018148031011030b61184803004854003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 131180107 1250 131178857 131178871
    0x103020d210f180e0a1104030807030309110321030a0b030a080c150115030506010507140607020d05040e0c0a0311030106030504030314040f020d0204020d06060c05010e2b0c0605 78
    0xd44080d55085900112000c200c01d4060f0781d0b0740415480c040e8201ca03030b1a406052180f5140c2c2e9228528014210201280c018540190001c0d41c0c81d03071580b40040c020104c0750000c0da01e02c0082304010500d4034022443c20701041254010302aa1180d01c00000d550b640050982c2010380e60f91241e100640d182070000c41461405038040b40c0d16003890b0b407030760341c1404070003031a00d42d07507124020050008a60442481d0460034141c64000707905e0f5030305401a105842021406805443c030b0140081c411480003a495101700350035420348080c50f003500026103050040e0702403510001c175000002248290154003602c1114504c0c41c2c00b21707045a0b080c0c0c404a0a91003030b001040041d840e00208401d150700750203a44514101030301900362520705602d03400461400008000c1c1700d425450208400d40da40c1c0c2e010f03207840340807084042124a035100c0d4050042c43e04620112029401e122040b20300200104004159080d0402d10080624482c1d450480348510300480300c0501005d120101c2c0452407034410349124900d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 131181357 1250 131180107 131180117
    0x60103060522050105030c0a0e07090f090e1b0a090b1c050f1b01080105010503180601121502040608010303080405160e040201030e010c0f030e150702010b1003060e0103020d21 77
    0x401e21602c8040d280d0581003a80280d01a100455641d124405054100c400c8000607151a1f11402c01c101ca00302e4295110403d240c842e060007041010440e400743d052070b8ad040b03007101e0a411645000c000d041e20405001c543c00703448a9800c2107610016040381c03501400051000d010704090703540640000d94000703010303103840e401070070742c5182c04408014420f002c002e83c2c9903c1c40b001030210300007400640140a2141004004004202c4810450140004003501481035504a40c1c6a8800750f0fa048400e500a41b10260980925030030301c0101c0c402c480c141c8205643c0c558007a803d5032016505400042c10480d101c0c070465002c0460300c00840c0541015182d51242100e0b141060700004003560740114108000d40d15044802c0311064015980d5402c00312203080214259101c2035a144c108901d1700a45840044401c04000c801c030790641c414285c00c01304844085030515009021400c079001c81c0a150b80b40003038070303005001620304043e505003542c1c82240ba4900c183c40240c1c400f07000100840301d07980416 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 131182607 1250 131181357 131181409
    0x16030f0905030c0706050309121b010603121202040302130e0f100501060905030105190c02101103011e03030905040b0f10020a020907211104050603040804091a060307080601030605 79
    0xf0f6414401c100040c5850310b0f01c24254200030600a0700c0e0b0301008008800e01c0400121440c0d5450306003101240c845034107000b008460f9990030301d0035841c0d180d20700c5d4200044013911130524288541c420303541a40d8000d01100c940d03500c80080032005180d1003503030000600c01e072004904030740d02c100200b486442404501150342d5240c023101a112a4464002d0341c800c3e4107140c00c002c2041c81c13001c00801501c0060b58081181c1030380b00d00c180c0c20440c40c0c0c003085070814200380715170420f4200da0b03004504071803c00310500910300040d2000000c2030194007005000502100c0c0800c01c41c46c0c03541151070429002004041241c4200c40040c107502d480550800c05a0040d040640c198506100400e07032140b031a0800005850345400c1910031441c054100102d80c90341ca40b00c10414060502c1a1805003201503c07046c0d407400c203814014450380062059542c5582000400001203d40034001c03d929000a011b650441e10f032800161050315000700700754100340d070b100400242603555613242c2591800e5404a901e10f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 131183857 1250 131182607 131182627
    0x1512100911030405030a0c0c090603060b1c080414270f070810050111030c01020f0c0705060712031d010f0b040e01140105060a170406020a0e010801050916030f090503 73
    0x184451510140c8001e07400c1c070030000840e0000c0308850b0850344500d040c0001c601903141c8072002c125980c008080c598034101001c81081141e502540041000b190181e030700f0303000c03618030b400742d10030211004061141c20b000030807440c0d84902070846c80000c000d000707500d0040d1090f404520038000300c1c1003039007031240c0005101140140721151350b005041441c1c41c11962900080c018108801c901c10541003000101c1e410010403018000c2c1e441a6501800940d80c84508118000064101054180050080f201c0000e060718214044540d09540b0442c00955416484004d400801c10640210084100e0390700307014150800b8464040d070300003402000104000440f0500080315002c8103068041c2e0314140008101c2085642da0504442041b03548a54a001c0600111888641c003001030fa080400c074420701c0108501b94001c0d040903111652100b65062002004552403c0c0030f2181907004505200450b2a0021401c111401d04200d41008112210303040c40c00011541c0084056415400206810484c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 131185107 1250 131183857 131183861
    0xc030906050f0f0c0f0f0d05040212030a020c01030902192607050d02091905040b0106030e03031005040c020a02060f03060f180f0403090b0c01050106030605010f0e15121009 76
    0xd5089020b4030b02440c15810340102e855014206082040000c00c940000589440441c0c1c1826a03140c075850302e4040e08183c202c060305003079800703d228011440038032040d444000f0685000b0000380c0d00425012052a0065008080318441a238000301200600d1038640880b81c501c4005000380407105c044484042c0300203501400806403500160440d040c00c06c8107a03184405a4501a01155004001d45400c60300540c030b194085443c002d0142040e04020500203802c600030304039860340e14140801071101101e9910b138801203c42d99602c524200003844642800e80c0210034000340350040711350b43c00450b00041e1242d009501d095400b0740c000800c0249600b0102e4441400450503501003000c10321902048800d0100100225501c1c80bc1c1000102890b10461000c0000c0005240160b9558542d01c0042c2c040c2209015040100b41000000901544218001d059a1031540e8510a8503000711040000f0f440c2c048001180ca00000d02c058140341c1c103016010f90162040d01c1d14112202e00e13000801d01 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 131186357 1250 131185107 131185111
    0x310050d02010c240c0318020f0f0901030305030601031104030203250801060b03040606050607080a0c021305090115051005070201030906060b030910060602010506010903060e10150911090a06210c03090605 90
    0x4209401d221080300c1c7c3e01c40500032080c200d6030417260754100c911404080381d40d0401042d516580945402d0002061542050045015803000c2e6401d100e0b110300180c40f40c68510070362000a41540c000000028800c1202404001084410061b031641d25902d4411a0035107030310f5046010190400014803041092034800c0100030501520b00c9800e16900d900c4000b82c0d40a1114440140542a07020004550701d00c1c0ba1401a5114500c00700101e04000301c103a0300824841c125103640c82010503012138186050a200c402400190b96114905203446d801180070b040c541504940c203944901011a0110030040510f12454105004280e00c60455180400351000ca40c07011095924090a02540b6640588420705981c0c01450119108152078060382c9080c07012980b01245600c0d010070100285c8100c51003c0444105c0c0506000f403200d008920000307845214180c43d4820f02901082001c18001e0b05909010b41c1c201b410518030312070b46045135080d0341c0e03030724420310000380d480300102e00304561481015 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 131187607 1250 131186357 131186381
    0x50c0c0343170c041b030513050607030905031605060405061005090412020f0a080910020c1e01020f0a0503030f160c0305031f0b0409050106050310050d02010c24 71
    0x118001d000881807641e9000d000380d600702407030110b00e210141c0040205242151001d481000311501e030240c100201c0b00003801d13603c00203050001040c3c00181c2040082da03c0390300300019184a0310340305400e80c000d04c2140b60443e09800b0030310004a004200200c50112103005001500e00c3d40381500d003941c1440d100030301a0003100c0d0031040502031034943d504100d600c01e5210000d020f07040d81c0340000364942808812955120300c201c080707480401c588074000d04943e01c002da80c0b5910100514009903141c02c500f088043c1c100083c1800c24000422503004006244018010b484480e000035501c5400d00a10340d2055a01c0d600000c24040d00c02124070302103901400000090012107100a00201180071076800a0304209000c8041b0300c1900f0000104002e00c115152005542a034441c00700403150843d01c03901880300d14010001401a0003030302180d00ca1003c188a0400441c286010015910201c55081c0d0400095010243c000703211182440d1803050048036003003060606048040c1607591900301c01c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 131188857 1250 131187607 131187703
    0x71110121109120303010806040f0609140d020d0e0102030d09021207060305070806012609010204150c0204050a02040b0d020a050904020a1d012105060607020d030c05070e0f0601050c0c03 82
    0x407c00394001241254000344d10054030310078480b03581440400b80090b16005014030340010031215564400107250810440c0036002c0e141d5800d400c41050ba94200300f4031100b4050782040000302c448841ca9413042344030303034401060304049194031000c241c940320303040d0000c5010a54440902c86215001104240d0110302481e0681480218450f8048000c10600640c14603240013000318114603400e405840141980385a1006107610b4144020411946d00310141d000c2e62400c404174038800c405008840903540b02c008880c0c5410380201c060740003980444401010480144424002c40e69240010144d1076071582e54842050410900142481020061981400315407000d0509160f1418030486a541810303c2c00512551100c010600d00d2107024402540944400c80c0304081507003000441c00c115010780101e8051035164188000d8401060b61004092075003e00001ca1661103a801082494031080aa42c4004100ca003c249803901c9181c1c0c4008881000334003800c060250100c0c080c024524041c8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 131190107 1250 131188857 131188859
    0xa05010e0c040314070e130b0a0b010509101407030302040914090d03020714030301060c030906020a020d140102070b01080c040c05190311071203020d060b07111012110912030301 78
    0x441e000c1c03155120080c512180d00c07502c1190a007090050718010208150404540e103004511902021014482117034280018000714180114a10580f80d2290068650a16000b0310104000c0da1100c5200001c0800152503000000d051100d80034100d284e00c6074a0150311103082540060680f64804c00d0000b503141c1d82410400c26520000e4140c694410500740141d8401250170858014480d01454100612002000007207540c0d1000d40100f1180c082d40c2c5084c0041e8864004a0321030014680180d806401c0030492800b00d1082d144c9c0d8203051800c140018600b1030039030340b0010160026409400f807500044a038440034105400345658500007441c0c90703464003448100d5511b030030003d42c3c0110109651101d007100041503002c100c410701c0350401040318009054540080282d4040728550155505294002400c3d05000095800707044c0d1016000c1c400c0f903062400d20100c0d044020700401001a0100d000403081072034811a044a11300382d0059559501c46000d01c00342c090f10860f40d4509500c2000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 131191357 1250 131190107 131190121
    0x1050a11090906090901090c03053409050717070207030201110102311805040507050a0501020d0e24090a060809030304110f060a110c040515040f0e0a08030a05010e 72
    0x105043d8020421a100d1940d0b4483d405071500400c0d0080004090900261020003480300004554000c90a1050105c3c075200c4030f4554101c1c504000c0c55000c2c00900c00000c180a400d50300e03081150700041624240050300d140c0800d0140f40c1d40c0581d81c00c000b5030403400040c020b55a009e40b820300031010b460000c0d494440c880c0301c403114004100210f400000c81c4010092170040d08082c0741401080d8a284101c0340391440d06026006000c280c80c02c940a118031000040e407810045c03180012104140c02030a510b0500740000c1d0703180141d02a00c5903002d2402c1010299020410328211144280340c5d031615111030140041c80140ca0b072135007054090182c0101042016000001201e60166100c1c1307006c180d00c1c5401d00030807080310741105c42903800403000c80c643c04c815034020304a071480c6001d03200312614420508140000c5807407d030341e4048500baa0580403551800d00e50440b0400c80c510780ba0019a042d44180e1050905880c14400c950b103520020034411070000d5070264502400004c1107040391414a05 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 131192607 1250 131191357 131191369
    0x607090302210109031d09040210120e0607050d11131505070b010e060102010f0920011202030a02030105010206070201020a0504120218191d0c061606020c01050a1109 73
    0x100c802407203501501200d445a14140c9980c48806107020001e012400c0240ba0240640840c3e0071880f01080e0700e4a400d5400d0328018030024022500500350030b01700580204100d5860b000030011204c030070380700d2008090317401c4100600e6100d100c5903915140c07110f030911600d4061300d681d40d08004e07035100b00b801503085049244558400315070240540e084101c7e440301045d40d00d030080100150880313000c0e500015031010050b0b142c3c3d00c104000d074001c0280b0a030040d2a541243d100b0113024000148102d080109140e402da01c80200382d0050401d1100452688140d1003a40c0c0220ba180a1554000c0010020b42d601007120035003290480c0029410324420101c01005801790344100388460700a00102d03001c1d51a185600403c83c080b0f24040c09043c5489425400c801d02a004003100d0245015040300c0061503549c4040c010580000c0074000007011141080a150000a1591240030604d901d440000f0082d10007090b10f00248800030840d40b400d5415031084429101050703c0a110410455280703540d04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 131193857 1250 131192607 131192609
    0x307090510091d03032d07080402090a27050610060206040803060103060b0d050103050d030608062e0303020c010f09030317070207050301020c06040b0603070806010b070203010b0a1502010e060709 86
    0x40340001a41c0f42c0101803c41c1a41207500b1002e001e000000c248180030107412851a6603c41c3c01041c0c221421039810311030a410386c2220100c0024100302c02060040ca00066580c1e00101d42c59004a54040d01b103c01c000304007445c00c039011000b45c00d585032a0403c038050003100c1d802400351059404403481e250020b034890600800003482030b40c0c00400602141e00a038003000c003800032103002c90b40301e085051965004142c01c2c0001d481510a02500d2418248280a9003050300d5602c400f90000342c40e40b0300d00140c1402c40b440203120414490204102c410362000092000314001d90041c601c450302c0b1340014203102502558981081114101800441c0e0040c2500e000d00d10481400c0d54641c1d501c00f4100c1c00d000441d0809541940001110380c4a50000508139009038001c41c4a00000e0301e070601019510850340c45009190b0300501d00400400819001510045001070000300d81e640300700000452002c401c3d00100d800071500483d400740168248240c1d41d02e141010010b20240c20060300140028180e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 131195107 1250 131193857 131193869
    0x70537050426191a090307030210060f0902030a090602070c09050a0525120509030a0e0d050604170d06031202010b01030603030228080d06030201021c0912020f03060708060307090510 80
    0x1641c1c00b000304044c908100c816602d10442d01807860501188060f16a404928180c0041c0f0409000501044807441000103e4512541840d04289040103200c06500024030b8039040c10354400007038010503041c3c002440c1d02440340d50101049424000c40204650024040484262401c0108140d8201d0051605404500c003540060b900c00a103a0460b19200c01680f569001e9041c081801908200080a041d45901a0f240c0c3c0c14500030320300c02c0c00005950303050b000d03010742d01640126010031000480d07040d80b44c0349111424900320f07004071081e0a0707840f50b5000315503800581c06035900650f070a218100c0d4030102440d00340845031440c2c8000350703220030b40e40030110015001400001000030200303603007000e41d0744000d000342c0b0b8010030f5003450f00402c8070b032000307a001d4007a2045a01d40c107005141c034544101e590340c403540d6a42e401d108100c00f090343d199204030f03007001c1c010080c805595800c00403244510318550303a032165490110141800c001d9650310a081890500b0240f204041503130389000700b9a24 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 131196357 1250 131195107 131195143
    0xf060c02060c0a05151509130b07020a0501020f04050108060d020d080c0309040e010c0f1107141203030a051008030c0c0f0a03020a0e0402030d08070537050426 70
    0x440550058180010203d0042607840f0302058044030400c00c0c0e010300e02c41c116000540352a42ca503c014004140021100c048850750840e400c4000180700d51041da410004c20b10403104413442a0340c0b500c0c00c99004624a079881035011408100d15a4841c4c0b91a074840d81c2540c2c400740003a0a40c0c04940b2081d0b681c13400811a143c00301340321031501c004006903095244000d0041c401401c1b072900241c0240030100c5804006410004414030003070290740b501c042000c140340202a03540c03404100c81120100740300726691100395003203070701c0c0d00341c50810207540941c201c644006070a04021003100c0402c021540070b80c0c42d540050016125070f09010500b00c2c5180802e5980c800c8049801002400c4101203030002580b092a170b45c00800c969042d00e0840d886a882070b01107411607003122609850956040702d400c0c00240b42002980c041200340b40c210a40300340c11083c3c00c1c0400d446143c8152400c0046084400000e20115007000900104844140c0d079407050170103039400d4103400e92059150b01c3c7c1c3c1000e019001d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 131197607 1250 131196357 131196367
    0xc0106080d1b030e011b0c091a0901060e06040b1210090605060405010804110406080604120207120807170a1d040204030203060112050c04020f1c06060f11030f13050a0f060c0206 78
    0x3900901c0d051007064465504541b4190241c5000d00c040c01041c0221203803103152525000c0410010701c00d05080c0380c8020900c010b1603103070074002c581450610503001d40065040c003002803941000d00c0605003110b05003581c00d50038a445020752603440d00f158410f024403030401c002004251610310807281a42c8085ca0706440c3d9036213505011a110307501c0001c0b03903082842d040000601030004101280a2481340890380440420400102c0ea222418040c885040031404a000002a0301600808000d0b1282480907404500245030600c0364015080407030100d10120008801a1001e20003058800c50880b000c604140c01e540200c3d80d40c5805000e02031861580c0c0208d5070074000f08010078089070f40c0007042907660740c807000c0d071245154000d03040e4102064100c0741c03020189800b500400d002c1e15030580c0e41c0c503200640748608072030340c07014114001807038042003018100b031010b078038000c200d5070032044681d804052070041400070380440e40d0f01540da2036081d40400e0001e80e5000c3e522607203854045a20030f4913a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 131198857 1250 131197607 131197609
    0xe06071e090b0a08091203040b070807020f010c0e130203010e0c0c0a1202030d11120615040302040510060224040807110607060b150703050910030e030c0106080d1b030e 74
    0x408407540040558201c04555026810380c4003100b248564030b04025150010b000d0680c9064034002030768001c02c0e41e80078400044055226030101ca61268083c412201c0c10600180541d003101c0c5928040070000c1c0a0445040c1c080c140030034035003840203481d041145150324090680548110281c6161a80440000d07203080301c039010084250400e0308040c0b208011600c180b400303035070703035000e0441e800048d4141075051004c88a100280d803260501c502c0000c115584100400c403641c1182e0303041207100c2d8401e00c00072000d41c41c0c0f4400d0038810301c042608840c040f404c0003006031a081641c0c9151b1800c90442c050305141d40860b000141d0842d0380400e10701c2c3c1700c040b18a030030481c11164818454000304041078801c00d010040e000515044030a40d2450948000c0a0780b00405100308140036012071020800394405050500040340111b07824640001c04403009940a415540300b05c0c2540031030380d141c902c10f11044030140401e07040c68015044c6440021140f204910f0303584000040034080c8008040145c8403 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 131200107 1250 131198857 131198867
    0x70203150c0405060408031909120201030f0f0e010f0509033a11130602030306031b04092310050115030c030e1603060b15070213180303020d0e06071e 66
    0x18090051004d625191212240c540e25041031401d40304030307080502003100240c0038100284c207030381142d02910f4034135003650015805880c15100d041d0041d6541c0c525081c02628510440305400784100005c1800d90a5105842c01c1c0c0c0d402030312680fa903401c100104d900074900c0007045074400030112070010342d480c900b8000c00f9840300d859030401513441c2480c1080900034003400081000b41503107035603802400d84500c0200c0c0d036400100d4500d034260780031401101944807244400106000d0090001c1035103c2523607030b001d0892400f1040c1d00011040014515980407050201c031000f218440c0c410080341d80750040780c00c00b490020004a0601d42d80e224241e5007280710381c00807402c00c842401124506580b11010040119061105551040c5401002c81d80d5280c90300300a0348080c00707418090306103030b225001c014040508058101c12540c1e900140e852a6480c600c0c11420705000c1c1d100182c0700c0c9542d0462030b00f079600740c0d001d00c440c58000c0c40030801c0c11a08070001344040341c403045904102d802e0107a0160740d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 131201357 1250 131200107 131200109
    0xc0a170d080705070618050d0309170c030c15240a060302030406180b060109060314060f0a030f1a090a050a150b03150114060307021504030302040e090a0204060b070203150c04 77
    0x10055060a500902c2c2181c480010b203e1288107c0454070304104824080f011038080b144014a400045500024101c804030b010f02030f6800100c064070324048038644207a1a040c1e5140451503481c0d6007504000d1524243c0701e5140c501000190071001345890000010180041c42c0221000d150340032001c641805110b41c002121900c1c04482c80c031824040c1e0074414080c150454841d03000541001d00850820b100b401007401c4500d080c0c100724800c0d214034080025818010205e00d0b0090440e850000c04100c80b0484941c10500586485081d5400000e107600740000060078507039240e01041102c0700244000550b0914107410170b114405070400c150300400a0003c0c11405d40d4503114034141254240d00f040180360483ea010b507422200350b12440240b110320301044411002680085803500428280c2000b85035005200b803800504e882d4851025600c121810350314814640c0c090404c036421400c2c103100b81405040482d803002c0c10207446600180e40c8001d0711182d492000600c40100700c51000c0107044c1c42c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 131202607 1250 131201357 131201363
    0x80a1b0f0f11030d1403060301200405011706090426120619050109030611040f1214011a0d140f0307060b090c0703030216020a080c0a170d08070507 65
    0xd41010380c10201d0444040000541d50403191003006505854000f84800350600300762102d684413041882c0820342034000410349a003554880c2d076000e4540600500111000301d07134420310b0341c6990030700d070004180d02d1021222540751341801e018000c0d1039440e0103810390711641c0316072100c0180d070400c1509000d030b070210030300011502c8010400000203c2c2c0c601d0840d115403800e0f1101c4005440e1a200c031401682a841024040381c854201400441c0c420340280c40d48180e03030090030f4a45640c5044107040103401d6400007103840e002808450400c010b00e40554080440307040240103d407900c80c07078002130001c0003440c0d502c03503044c1074941790070481c20007580e44e44541240c0c1501c00c0d4224640003103847ea44614401c4070802c2c074000c060055031500d44010341c000c450300c0d0240f85c200956590306500940c4031202003030940d4601d0f0b11100050f03403007070701e4040603159090141c001041c0c1071013844101d4140760881c03e1204603c019803288d2810002d020600410b0301e1428216640315142c00740c032548a07101d009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 131203857 1250 131202607 131202623
    0x150909120c07180203070c1401060e1312080c1c060306230a0e0c01032a0216050a0b0703030b0d141b011107030b090f0f0105070912080a1b 61
    0x44890110368001114001000011881203d03035142c030403444121031039804142000e44480c003061003481941c2c40540c15000015880c0c1d00e81c401c074444014112581d1100c04c14196004003041951401340c00400300c00e0404001d141400140c1c1e10341400f60554000c9001401c880b68002180c45820910046030070050401100c1d258901c074a41c01d038540e41605426008040c089420b0221511800001d90903e01c043d0101e814940300460143c4403050020082c007046100c51042040290407038074680b401c1c0c0d002054010031b01140034614134180d5219904c01e0014000400c4404008030072564419854500003a40064900c0090491401d0880c09030106110407080c10303001da80004e8280100c45981400c030f89402044004589551400d02644130507002814100001761041d03646c00d0704856008c003914411a000034030300e807a00700d2080201c0003e0313449006001c4400c0d04070860303001a04640d5040101c40701c43d522025402c1c4140c4d42001d081040744840f40c003003004101501842e0651120403 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 131205107 1250 131203857 131203867
    0xb03100306050a0e0c241317060708090c0a0308031803040f0e0a060501051902030d110405040c0504050306071b14060f010b030105031f09081201140915090912 70
    0x3c080203103002d01400e5058425091140c0003031600b028100c558401400d900d0f4000c0920b000d48003120b0b04030242c99400c0d10001c94012900010344802d040c1c1c0213074003200030b043e5458840c03401440400050501c18860301b00703a2001509849003500581525042809903650b0385402e140040000c0400c1c080c90485d000201d40450004079508541d02103038900030120340350341c43d0b4000f40310490b25a8424940800c004108402508551001c480c055203107c0c01070f03908112450b01c444d0300761f0f21018580800d81c2c0000030140094030b40f500c201c0e180e82d00d440c502142024204804243d88000250034042400204444110314107030340c00104214543c880d802c240240d004035000b554a51064404d05400e40740e490000c0383c0503444030b060f6812074000900802a10200f11b0480d20240c850380303082c450440c4c5407200200071071030810080c800c0e0318a054520203d585051140c5001c4100c0b20310880c41500d10b4824015007810b00c021801400e00102c0b451991a200c0210a900d48022039410048040c400306e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 131206357 1250 131205107 131205121
    0x2091c0503090307150801060f0c02010c020d05070f05180601050a1805190303111f0f0212010b040e0108060c0405041d010c030204050307060c0c0e1012080307030c0c0c0b0310030605 80
    0x4280601409075864101b616600c9a809aa01d0075400085500050160310320401541c03040d42001c0c0d505001504081e9081c5082d00ea00341400c1558001d0300022007110710410141c01c000903020750004008407554118101280000c0403842007611003401c126402c00c2d644120309440078510300400004128040c10700c00c040c903424915080307102c16404248112113000019601090415900c0400d4000043e210000d000e0701008040b040001d00455609000800c040b0307101c403410034003a00010030200c0c0c94501e8034180c00f0140e0380581080038540c21107401d1042030249003007620306403882107402051a00c1d821300c40d1900a203032200a1071a40d82084034081c1d11542540c0200103550f001d401340c800c0306031038a0007a1001000160024081d001c4d0001c104003003071121500c15040b001d0307044800c00980e540e00c440190a815400c0c1034170840700000c2840340045d00740c403440743d0700002814000780c0c80780715440b540071505003486201d0402c0d0300000001d04400064502c1809164825410000c070b0411003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 131207607 1250 131206357 131206379
    0xf0804080102070516060309020a05060c030d0e07030b0c0f030c0715090b040308060607030801180605030f0d021b0f0909010b0310050f010e01080d030b0d0b010303020307060f02091c0503090307 85
    0xb0124464281c0200004110107200340180608c1d59001382000300a07610340000d2010b181c0c0420385900d007a000a02254ad040c0016010b0140e0040e62007005082c3c07641581001002840041d0689070500c000b0082c00d24400918810f03a6406100040001d80b1010305003080f00054051401c030482d010700d031001c900100044900c405000c1e43c0641d986212640c1c03900c0c02e1003540d02c10b005018000ca070324540100002c91002508440c030740014040414035550700c1020918202291a866050b0b4100d40404450950b0421503504a1402407151083e19003414010400a10314880124080d903108000200d902c42e01b508080103040d000307000c44655424440c8a0340041005031070311050680020300005201ca125003850341a00c4110000e00410081424280c008080807505150000c42c904400c6020503000301d1039900850103a009140e45040f103184c00ca007102c84640024804620501540c1569216540300c503d2400c1e014013407400195480c102a440c1d405211100c541c10310508402281d043c04034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 131208857 1250 131207607 131207623
    0x305090606010201020c12031f061d030c010e04180c0807140906090f090c0303040303030608010b120304060e0609030607030c170105030a0b1e01080303100f0806040f08040801020705 80
    0x265098905688880d4012400d078420700f41e10780c410358005040d08000c20311042c021a0403054441c07504615898151010302c1c0c0d141158004004684c0041289030080c2ca5642c617a03582000440c01f529407041c5a0300043c5c5079050002d5118000c9030340c0c040200c00360910102c07603480039411070b2020041d566190946035030303242e850140595884041510001030f040c005140d038082e0030002c182e0201c56641c0818040e04c10f40042c16040d0318800c10458040c51f480030710003000558021707a00401c40d18142400079081d00c4074003040602a07414440c20400ca00c0d40031054406480041c6428150b02802c000055414040c01c0541070703140c0036202c184000103415a0214200081c16101c140695030845460407d0760000d01ca07468050b00306810401c00121920421540701c1800c48041d070591004050300e0300070082c241c100400c2c952000090103e0400b40340420300040041061104410b0f00700b201d0580c58100250000f8258880c130342c0620200200e02083e1409091040d00854840c051070905c250340e0325003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 131210107 1250 131208857 131208871
    0x10504080c010c021f0c050f030f060109050303090306010303030e030d060f0303081308070f02060d180203120c0c060304032d080a0c1b03030b0409050a05070b130303030b010203190305 81
    0x600b01a8550700c13400420900343c0c085200340000d8012900ca02d03000080c00700c2d00001c00800a040007000c88500452010b18010399138400c800900c3d00c0c080001408020164101620962060204040e15500090440d054030783c903180202d03222400082017480c1d80102003004602c84d0030440003044a111011a010031603001e6903821030207481d4829030040310f020030394000e070050b00104107010114005000c003035a21803011307203d24a01954021b020307044411001003e40c1c0c070b100d80303007019007585420081c8540c42400170000b0b91401e500350040a64238446031080901802006c400103090500400442600f200f803401e094100c90303030411180241462011000e40820790001c040340c40b814a40c4100a4074203029103408030b000d0760340201c2c40b2070440d01c414120100342e110682c070a210b0f140c0b400750204030744c800e90092010781c0062510505008054200c00c074101d00c2840351101388016601c0803000c60782c140c2000503500765410700403802c41c400c51600d51868020340c200c0c5c1c529594503610007485041 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 131211357 1250 131210107 131210111
    0x30e01110d1d010c0201050d0203151804050d021204170f03040b0a030e0c01121d3909040305130801050c07050c03060105010905040f1b181e06080414010504080c01 72
    0x10b0000041d200c1d030849900c040c0c0011000e00604080300d0044c5d008540000c220b0865a0319126441d0019182480412880101c00b0038001408100042009481c59800150014000d00c0408990080b4107024038440c28031900c841c030640044000d403e01c5540e101103a08000da0b03950b03079151300200c500d0364032081a40002901c0d0440d031000606012a00c001d541005a40b104c0c401c80d45124580090404507082080c40f41e0003594240307910a003000301c1e86100820604d00e9143d42503510784015040b50010034255690044090220303282d56441429a020b581418400c1d201c290600b00a500c4003059000b0300115841c010034020410030300806424028400d80c00c5502c18580704042c1503ca030800e104150105404c40740a0059207000d800208800711170041c00a22251045001c40c40c5040c14615070005c03074460000041c0103c4c07038500481c0a05040d1602514501d03014414000d80d4959108032010050100c01282c20050000d40040048e1036690007804142003908001806a02415008090358 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 131212607 1250 131211357 131211407
    0xf090306090303090607210c03060614040308070b040515040f0c0824091f05010f080706020c0f04060504230a0c0e060c0c030d090914060d030e01110d 66
    0x10000000c8a01c220513a001a200c141c455200c140d85078404000c085501901c668000105501948910240c003c40c81d6070120b0704601c3e18001800c004544c44000300191000c01003400406c00300402c446c0c03165805804203005568508215007407858108071810200d41201c00d000510040c0040d40c41018001c8004040d02552411010b56500c00c0415803544d0824404400d02c4819441415a42c052420703000d64029805c515a0a40010b01c1240041001d40d0f03184d0045c441110f04511141c01b9245150003014040c0c20131101950b60040c01d04114843c1e0303030300110040b9640b1240c0010f001403101410074011140d44808000114504000451107001c0c0000014500009805440b09100ca01d8841042481c07042080c040b05a01400c1c03141203a1280207100c1407162401c000c216840546503407403610f124103100b210806e803140e15504a48015400313013444810342c2d0304000d80c020180d041c00c09a011500a0b00161503100451014005601402664a500d039821900d1040280034085000e002d031b07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 131213857 1250 131212607 131212621
    0x1a070f240504050c010c050309040905011a060f0f09042a02060a0c0c0f05030708120109062403090c0e07110c0a1d040302010e100c110703350f090306 66
    0x16501182c0c060603551221307032600c2165000b0028501500e00900a4901d4401c203100401d0640d840c50700104c603640c5d0f44a0401a640c0801950701d06550000c03140c17030385811348035020703180140a807448008003103200280d10741040d03403141d100d44810b00700e2160080060b000768401b8442c41d804501c4440c058080da80008000302800d1092106e010819242c0c0d51030101c15440d14201c840f05000216403a100800881d004241548084d000740c41e03031002072a5103503040040d0791f4140d90055212154114405100c0c100820702c58041050f031560074a0300160900185c104820141120303807040d51564030540a11078041d0748200e0500104a44000711a41019200144a00e840542c801d020070a84800035030041007400020349500180244000b040c001545000d20341000e4240344481c0e045a99104204042c907000780c10243c6422020000c0d1055500d10b44030050b80d1010101510002c0c840c2e0010600074800f0b000040c01c00400c440f1005444411f50400744620f50700c0415250b11038404d0100050b00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 131215107 1250 131213857 131213861
    0xa140607090f0b07030c020901030b1914010905041e0b07031a0303040905090307061104030c0b0a020a02060903030408161a0403030210021305061c20041a070f24 71
    0x202c541410040c2d41c841d10300000b0400c107070061803007101002441c41d11440540c2c0c488103014061401046203028504100340301341042580d40340d0090300a802d00d446c0c1c1c0081e080415005045405850000c20995941d24001c040b4440120500f41c1118141070944140a0340051052152720741c0e03102004108012003030514003410380380c01c2e25450fa004000500030150707241c0140e6004030400c81100c4c2843c4903582d88009070341d00d070001560310801c08035040040c42402241d2000600e00803111034a088103180000f03464003003084d0302902501d400a22005141c904208a400620880080d2100c0184048441c0107044461003600c0e40c10700c00d00c855002300c5005004450444e40d058004202e480e0844100318080d400401c4409588001c0c0301000455480300801001d50881d000b41c085ca441c00d0391048101142d6100d000144104a201c032140c801031074000c2150309a520080601c1000040760410780c1080c816160001d000244181039141001104403558404a402a0340401c44180588503d02 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 131216357 1250 131215107 131215109
    0x50f060a0b1c0c0306180f0b0904050c01210f1e0e0303040308040c03020603070309060f20130b1b1908040b0d0902040e070801140603120c0a050a14060709 68
    0x2e1140d200c0070700e02640a80e644002d8404120b42400b18009548244841c2411240b0a50014a54442142141d17607800c2c0d05c104410381001300ca021005007000e8403481e070b0352105441c4080c18071000e0345941c0c50141d61090000310021070000180400f038031824954010b440c0c0c04601d100d4a424100079890990002c0c0170b1129047c10b6074004508656450b1402c071800742020700b045d1703400c003111031021002d130315400020b5204150320f4171b010481c985a40f4000341100d40003014075a03160300c6c0c01902c50100e5002d41c10b1307034824441c043c0c102d40c8820005180c6003861a2640c026040d807a800254002460074413a8110803003202c40007a0741d04004540c982c5981d448669030020310b48a4100010b000210806020707201c0140010000104011158041000c548820f02c1c09a800d50100004001032102406480781d40c107101203402d021414114003195480c440c00c0d606208410012824a01d092010060b000c0c07620b0700041294446075a0b414204510010842803481a000300b10001d038601e401415244 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 131217607 1250 131216357 131216377
    0xf16030302061e07230d060302120606030303062814030d020d080c0a0c020307090b1c08030610210212090303040c0902030603071e0602060603060403020c0121050f060a0b 75
    0x80300958908a080f9441011682c10713914201c203a160a44001c9511001b0b442e005c4140400060500e00b54010000c1240c1601711a48403a8007900c00c00c0002c1d1008425a0780043d070039a00c9070340486401c80f42c0840506c0c078000001c840d2502d40782c0020380d40e0705400c010301401d50541c19208082c0c45080200d8272000b0b0a0300c0c0d0404103044a0201c1d01004041d8001d1080034030b20300e4110104c09560b80002d08003c4260b00401c20720340c840c0301c8010707e0b2030108003999924000ca00a41100201ca03503542c1d080e4000240814842d00c9021205100107008415217100115021002c0c018081c100351448020b41000011010043d42400003403202e1034000101c900503a0811840d280349441c0500000c0030350300041c01103815004440e80000d0780100c010100c09060f8252041900710303800c01c80000e181c0031004111901c0ba6000b5414000440e401207004261040c0c00e20b449a40c881c030642010040b180d001081261807440d06d0704010030707403401030980c43c00f90204039400320081360703515244903450090081d07034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 131218857 1250 131217607 131217661
    0x7080d0501090c09151206030605100602070f1a03060a0e040f200906041104050a080c0f06030609010b03040303020906030c0306040e0309011202090f0d05030d05060409150b030f1603030206 83
    0x845d082c980104824002c6014030300010400940720f40d40d44c025582d0990b13080d0242c89001c1c1040c000103030184009000b03401d1048024560601e450303280b444004241c1d80d450503408000008c00da554552920000c050300240030421070a080924003041080442d50051b2400020700c5800301c0304480464645448100041040b407564613503400300b200800c51141c503194070700410400018542c5a20606000600320040030341451a50002444103840660207140e104040810070130402d6036402d01c006055880c1c15015503100d03600c5250503002031180d9180240c4c4483d001c000c00150141c5200210300c42c40c0160b030140b00c040300c20010280e481c040c4684041c00b142000d68408416509580a85050500280601c038504900c002080368008140700503100e64000054840c1041000c3c010548c1110003660100116110303603c030400908041fa622802c0a51aa01101100d540030480341c0c00c10400710013603944103440e40010400d0210305120480c05400f819000864004540c0c4030840500107131a28 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 131220107 1250 131218857 131218889
    0x506090103150b0118060e011812080705010b061810140f0705190602040e0c0702010f110c0406091b17060103050603030705010504052a03100209040207080d0501090c09 74
    0xb030400940005201c1c0b50400001d0b299220351140400ca1400051910361102a0b03103907070200004040003200c1d60104030960003400100700c21000c002079144066000302c82140c868505140140c003419641c407045901540100341001d04c07a1516030481403009003101e09003000d101ea1401907400385080c1c0e1410f01070200506c034202d83c5a190340010042c0078271a40c01da802c2c44041c01c50b05441284515019245681c1c00301f800c0c40840c002800c000e4001d45005101c604044003507000801d031072560300441c410496060741e20104084100130035800e0540041007400300d2074481c01400300034014016820701b0002d82400c003040580c09505580304140511441700099683c1c1e02c010b402034880a8040c40e0580300422002c0080b91080c40355034001c03845400a4030980303002c011500c101640d14012414005c84020700c041050764005140300b4450701d00030f00540c03202600d40000c0c00a015052019208403400641d14069004507804230341610b01c07800d820400314000c0c52044807076401e54001d1412003c40c07025 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 131221357 1250 131220107 131220143
    0x1205040b0316090e040c1406070501060b0a0801080a050304090f020c0f010c0806010903020a0302060903070803030403050a02060114010c06050a110c011e0e07090b0f0604140111030310120c080f0d030506090103 92
    0x24208007c0c000c003400843c035202c81c03540d495086903c15800120310a40100f460300d580384d40200b00c240104043d070000c2a0346043d035100c40c1c1e124072862240e03000d22139440210850304c00b4160144d4090f010000181d801c1c02c2e100c0c001140c06441490300b60400034040d04001003040d0b000d201004180c0c1d80140c41c80c5081411a428840d150b030003510309550501c54036800142d402e030108000c500c44d078801c0d520f0941b04d0414000181c42c0c40e0040c0c201a06100c0300e0600d0000e241d07407016012010304d4200ca0301242035110001d00d0030040c00c0803500320f0000031000480411000054004020100320300d0301450881419881c84400c88005d03803110505030300200010018107016410268100e40000e1010f1550920074002849a50040d400341000c400c051801095035a00319282d600c094020070041d602d145040550315100070070902075420100794040c40c00f410304c402c2c4900c0300c020301b0f825000c0701d00c026603c419556a5183d43c1d09003200081c1420002180350070310340b1744507040300d91160b205010300714908 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 131222607 1250 131221357 131221379
    0x5070c0c0e01060e0402073201050a06060c230f01020a080f0103030e0d0302070905040f110d020102100c1b03020106050a080307030206060d0323040510020a0f1205040b0316090e040c 80
    0x18419952009071090070b20761704140b04803004d1123400d40031001e51545280d042c01400d4035802442041d219203403407820803100341c11544c41c81449a120201691400ca5041790f00c070701c001400312003c0c50348650400c184004005500501a010441e10b072410141e032001c81081c0d0b055401d020080005c0c0050090001c1820030b8010000681c1c8203006540c40329465403020421224111010703940c464003100580140038055070407803004034040c1c991122058441c1c0010756960303108030280c3c017900d0b925582c0d40d18007403041c00c80c2002c80e5104601c802c40c01d8a0342c00c0c000e0190180d40603661058650f540700044450b000400ca610499168015090310b03900d183c00c01112002e061001e5050010000c007480c1c203587e401c00924200da85c444880c5441c1da00380703014050021003104150f029981b06d0303a90f03580800e10b982d4000c405250302c100c3c4101701d54250902150140078643c0300604d8114044184541c1d5040c0c0018140c0d40c52442da1050003081d0742d000306400c82041541c0140070200040b20901c0051826 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 131223857 1250 131222607 131222617
    0xb0a03020a140a030b01030c3e03130306060b0319020906190206160504030803060405040311060106091406190e040b0d06061404020c03030c03061305070c0c0e01060e0402 75
    0x508000001240c4010501019405402e054001075940c07564903070fa41d07826104100e00c08c0103902e48100b07409018030010362018041c41105013041881c00240d8400034440c3e00403205a004582525101c81d0000304031002c820741404126401c0d411301c6008921210003400f60392040e800c55040c0c400007c01c010810000794404500183c0005c01003040b00f0b102074903000c80840c0310280d6030080495241040e07103811a900416802010040b040000704045140d5800f5203411260444002070380751550b24040d208400899a01c43c054090200001900364210b0807038411102d10703d80c55259048044c0070440340784513009030140e260301c6110101c0100e501c51801c580e60010003820000c1c420320000c000507104d8041980c00c8420607200c0c10207000c0c041003050f5910220f0400d0f207007076007400741d1454803a84a000051458443e000003100160640c5d803103001003039480220036000c10507070810180041c454000c0c00d405032504010311600040c0c6041c02540503048603010360320b000d5000c0c1c1000c204400b940c01 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 131225107 1250 131223857 131223877
    0x3020307021905060f0601021f180b010b0703110a0f0b060a0503120d06050402090d1e0b0705091e100c031107080705030d1e0c0501021207080915010b0a0302 69
    0x5601d030340000104482c2c41c44400035019100411003840e01c80401a40c10700010080c80c119003003054a8488020411b0b00c82640032580071010849003082200442d4020610340c01410181e406800000e400410a00800213a402940d0f5222800c03500c40000d60350b842000f5008065501005000000c81c130540c440940005004140f10901e03961400000d00d05070201c0c072080314400000900d40030f1400a48500030040c4010703503095081c1441000082c482a060311009000302a05801800c10081d07074031603858080303030b00030a4040b150804100c0204507811004142c5c1c0220983c002190202104550610240c60014140d507040c008000d0110348c6506458401c5003844070303982804844040500038100501840790082a64510303002c1010314002c0140f112101380801010001c0103005142d9102a200c441820800c2100c555482e08500a1190040c4502c1d014070f400e041c428543e0344844280d00444048044030003000c800c5141010301c100c01c0c8110056a5000c0102c051198000d0b00030b0580c42079 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 131226357 1250 131225107 131225113
    0x14101503060f1a0d0905030306030f0a120f0212070b150607020d110f030f010507090f0303020d0f120915061706150402040e01030f031d090601030905010204050411030a050c070209070302030702 85
    0x24113548000140ca03900d140c01c5419400200030000c1074102003060210440c0c003400100b0401e00981c40750040052640146001c00c100c0e201d0945605008100c3c0c150345443c00c900c0c403036403040d141c14030a40ca040160b480d881005081895950249404000d544070700d41c004159004156003503a40412503002078032050703007040351880000c4c02981c1c14070540543c2e20070000042854540064000c04000d11030700041481c0d11144403d06c04a540000c2540880c540b505000186220659041e540921421199406581007100c2c000821115010b09540017007810001c1c01101d480d44040004580c80c4450344045500c200001000c50030040009009920090001494141c6070280c41803400000d8200b661007407008282c1c4400c144c1d00030307220340050b070000d500a0002000d41e800151410342c050051810551956140700a0020070342c1200c0081100810811030900e00d1080c0341300a40007201c0c800d400c00e03c1c190000d014820780008445a0503801060412640d40341c40040e4000e40000d005001144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 131227607 1250 131226357 131226367
    0x40c270609020c19060b0a090603022103041512060602010e01050702030405010219060f060303020a031b1a061201060f0302030c040c2007180902130606020d03090614101503060f1a 79
    0xe07c4180103e000340001500105500f0f0550051104504022a01309203401d0246100c0c0107500c0040140c8003a515031802422200180303490468250a040102400c06840c0c16400668140c05520030307001100090001d000d1540c0305441641c40740254401d26016800c441c0b0702c0c142c2e0059008003c2c01517032082000061400c880320507a8100d9501e500110096485400317048140754100940480140080203401d000380595034a0303941501c455000c01158070907600c089441d65035004a140181d000c1d0a00802086a031581d42e0a500c84071880203034003d02402074602c4142c14035000300d1294450940300d032120320a0b0b010400b8202a01182021414080c0141c08105404000c8403500d030340400c4800440c0c0c0920500411552400560942d01d0952400604010f0b5035000b299075040218641000501174960342000b6000c0d1502034018094002258204440c40160003412001e8034425201c01d18504450402039003250403078050054181607581007048140081c5484194220145952900f04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 131228857 1250 131227607 131227609
    0x160504080a03170a0e03070605130b0907050a080f032a030406050406170609060103052a0d2d0c0504030204020a0c14150f040c270609020c19060b 64
    0x8004044421800034148550303c240c441c200150960b00600102d500300102c0302c40700011039481c4110400102025107030f03000a8080d042c40c00502d0000358120802c030165241003e03500791544000d000c0c09118800640300802d40c5000000c00003082421607004515005180481d00a2840407440300d119188864081034030420050001c1d100a02064a91a0301d031828240d000c0c02910002c002080b03801040000c100c2d666448000a0703400501c01e080000306070b110f01100d1043c00d0000f40c111114006101c1c0300041d503040f0400208803065150b81c0c1002601d2940d0081c000d2440c0115450f910329250402002320f04009610440440b082c0341000c0b13242c2a600c1e4042400d80e0000191031004c80e48000072001849002c44489050140981c090090814612280013400744050403d2a0442456001404110552000801510315100701c00350791080c1100074020000000360f442c0c0c1c07040c104400040c1040e494002e8410000b100360140c9a11010075a80d4500d000385e40030b058800342d403110341c18005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 131230107 1250 131228857 131228863
    0x105150f0f1201170303150112090c0518010302030a110118060309020411090312070f0807050f0d090605040308030712050a0213080a11150d0f0b041401060816050408 73
    0x41c007400076941c42e141d00006050003001c0b08160b21101e03060f00790400035183c03060088206ca512200c102c3c9240710030015407004a0741010b140452418292900e45c0460500c2110305004040300c1d812504203a11010802d0078400f14038080c800290954002020f100c0018440382c00b886044506140900101c40c010a43d10310450740e42d0700c4500420baa515911040d802c06001d544040c2042da01681d1814204201182c1c2e01c008050407911900d10103e10403003001a41c2907042e4295420080701034071044142426512201c070f44011007403611500d00e40c40f640501400408003101d046448450a06156407511000c95000500301300800c40700c2120101840158440c180c05030042007001a01c1d05171041c09020000c3c0503401401c61035020020601c002085246039650714903080e110002a00c880030728036035481c002c203902c11120a0a0000140300307501c00764490004514121414003100100000c3d001c0500700a0040380c1c00291458001004035420b038508000c50707040391500501e0160350f0012503003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 131231357 1250 131230107 131230117
    0xb2d0703090b0103140c0409080a0c030c02181e04020109060e0301022803142401020f030304030e180402180615040e010614180409111201050703050703140105150f 72
    0xa400120588003005e103441040b8095004006a4040000003c140c842080038000c240c00d510410039181054403c0610402c892074880b94040c0070b489074218242381d011040b0b5001c643d5010160000041c40b04c00c44072404100d400385406071900c40001c0d0030300c042203490004100c0415090b6400300101070366920101803078403013520080b414030804000c0b020000e0a4428440c4a1030000102c0010301102050110354081080e507200000301e0b81d4454040145d04015030407140c24461300000c8200002c0c5900441e0540e009a0100c80c0907110f00050b1021204a41d01514080d4100c105200c2c4081250201e2116030f8010000418884e440b240c0000300c0340f45681f05411003960a41ca210042007416007100131545c0e07a201300107000f810700980079444440c445199125034400c44d110f103014030500a1408116001031800741c00200001d5034010f080340a818107980c000002840c20000600c1c0b03074424450593700940070940d004c0c480c0d1070f2104000141a8558111007844001c024642071351654900510f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 131232607 1250 131231357 131231363
    0x4090c080604050a03030e0106060e090711031303060c090602031b0115031109090a0816110406080109030206060a1d04020301060e04150501060215010b1303021c0b2d0703090b0103 79
    0x100c04d0592900400382c900511007c00c02c1d0307040c06800e03c0325a8014890702045030003550103070318a83e02c00314100c0d4012980041c2ca103240c0400a0010000038180e810704054034000d8000740084801c640044813540c04510418005030001d210614600545150f02504002510004566005001c000c04e89000e4030f0790003240d1100200b40509002c3c185003500030391040740c51001c0c013603007026519512020300c01c0e541c2d60407041c0030611492081100401caa4800400050300410840743c82e03031440e0780201820700059000d8803034400060030390715000d140c80d4195090480c2c5054860004038030300c240000c003c0c1c0b080b43c0c155203403000444d9001c001d844240c030660245502e8018000c0c10084030040354010f800400441d0805101c070740a0446c0550060b044032141c01c04c0c03555943e210a18203105525a4100952000820060f05420031400d418954000c0c05108600041c0c3c5480710a045204610300509601c2d00341c03046000800a4100d00c12036012a40d4200421000c1b0b4954a110310701100340c00c11 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 131233857 1250 131232607 131232613
    0x130209010b0a030e0c0d080c191a0a150b0a0908060a14070201111206040b03120408010b040207050709090f060f0230160c080f0a1e08010504090c08060405 68
    0x56031000c3d031600540f020403c90101a0040c04a00404101c402400040c050881240003d21440200007088a0564012100f6103542103262525186e00400c0184a460000055000100b28072400d18444d003060805071640740a103144c6081c03501c15003504130103800000d212015800082107542400800d214414040001a4800c2d81b9240c1504980c40074041404680c5840c2d16480c580d02c001040b1603c0445030036080c00719954030f40005001d45498842d07070703400d40500030f5003c06888249c8003510aa03942c1c54006c0c44201c0800c002e04c0124011100701401c0b950148200b0040d0015541c817140005010700d43c13134101c07400c00b5152082a12003000d00d1201d125800900e4109003405012802850790f02d49184a000c80142c003800f8410403c00f424034031040485c04244071207980a00440c0d0a40e40c1c1c0a0902d40c0c82d0760504d80100e215030070074078000300840c40c42500c00c00e01410700d51641c2400f01c05d54a4142c20342e404c0100740801000c80000458942e1801000401c62100800115205074451b20003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 131235107 1250 131233857 131233867
    0x70b09010c03060618030803060a12122307080a110d0e0f04020406120b12010e070e010602030703080412050706090602030702010b0a14010305090102070c0303090e07090308030c03130209010b 84
    0x401400c8450f1a40b0603003c010482c42800d44100100b1200d108598008a200d501c07629140d00040070510150f010020b0402c1000c086002c00129808484000c180c50f190341202d0504a4500340300c6d0828251030941894040001200140080d0054507140c412032400038250300030118160b01e06001da070500030128000190744400b40c07501692101803d203040e141507003418a4280041d0902222114046003d07407180c0810310191140034200e90100c0650001344520858400103d41301c49040c041c074406102035100104044d03000204887d40d1035819a0f402e170076683da40d00d402c40c0360b20641c0c04c1d01007000b408200110105800d40184009c2d00d00078070006075a070a055501900b1a900010100d0240c030304103004008c0022980c101214185003800c000c0784680d500304000e40280b08603100100744042c40715001c01410b0744088023109030303212900700510907143d0781c0082d101c0c01d0484c80000d1081d2400c0000030f83e260a0f07003000d560040f000000c0c284c1e44404543c0000c048000c260000c030036030400850 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 131236357 1250 131235107 131235131
    0x110c040e061603110403061a0307090b03070b0c0322050613080c03060105011202070c0515040e010e0c04030f0f02040606120b01050408030a141b01061404050f06010e06070b0901 78
    0x84050400b41c0c505040101c100c1c0e52004040c2030085100107010203a95121100043c07a1040081d800c030100101940c5a03191180d60302c500401600b9003080c0070340305041000c120300d08004100c44140d20088011070802e40740121581503114070710540141840b240743e00282588400010301082c00030204610781c070608200f07016240c01214a0400d10aa201900400c0141d0708014541d81d1510081009a550b00c01402d1514030085d030b940c4680d4010b40ba41882c4031000b42001c4c0035000380d90080f840944140d0361000044190b010075224003c1c036200c104410400500c00d80c82881281d80700d80e81c120f00030009600020304403003007940003202145401076000c1407110b8502c155980340070300342495800c0c28101041d42e07a40303014240e680d0f018007020f21095501c0c2110441a5100c4101c02050002c80c0c2ca503806819000e4021485070070301440400c5595079803440c05001d10f81c8100340020040d501561190011182d80b480b12200079006001000410046031400700c0052103988c0d00b1001041d082c030044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 131237607 1250 131236357 131236381
    0x41811060d0f09111008010e0c1204052103040b01050409230a050606030708060a0b0102012715050f070c02060c01020705011506050406020d11010219170c0f0703110c040e06 76
    0x6801d41740b04455503501004034a800450700c0c2e040d100c0c005140031543d62500000129449904102c901068104042004021000601103c242d08544241085c4101e900001003640001c0e80c00921801c401e000600c0242410740c096000c1501905283c407070350b03800050070809a0006080e00210ba00000d184a00b8000c0401c410b5810500650040030302500d45002c180d1182e001500c41c0032100e468074411010f070703031003504030050414100d1805210042400c910f00642404100210b440003003100e20080d003050f02e446014450010107500365000c0d660a80d0071208403009002c1260b00110504c80800d02b00400d101401c00702d0710400000400b00d241c0c440751380001030b0760b0f03000400f00311080000303200182c2c0c080341c030114100c4e076030038204030700300c4c0310303c2f04a01902449181c0160340241d10b000e140810b5119040c20004030005032060325a45079002a40403d10850066459840c001c010400001e80701e40f40b044074100c26101502c508043c800e0005003039400740d0a82203003551000c0d0901c00054022 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 131238857 1250 131237607 131237633
    0xf09050c01110a021908030310060206070302030105060a1b140d020709180f0c0317040501030c09050f010e2e0206150913020d0507180b041811060d0f09 67
    0xd0800044400c8200982c0f9590104284001c4c0200d10358008001d040000010603400781800000b525100c0c54001b0f0b0040c0e400c211849583c5c0141316100200d01910701078400c59050300c101a100c5842e0a05801c000c1d54100c2108460045640e4040f03200404203d840107640c41d40b60080c030107882c0c10400300e80000e00d03000d507641183c2d81e00380ca00f109800c001d200154440da01f86510080d164000380075410022220402c0e68406000882003501d00c40340c40002000034426500240c8003040721211401d02210720030014041c3d550010603010041ea225030140d603c00c03100e4a002000d6004148501402c51000c6003512098036070f0082c0c07115180784c00364062042c1c0e6442040040e82074a800030100006107000400703003558190000c2da564a10940d03c030b1000c1c85075566000401c8a0307216903034122400c4a400100b4812080e24030f800c000740b902e0310340360294040009145036400c0108456071105911520700d010b005074002e8041044411840d613a0203420464980e500002507040c10a08107a0601605 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 131240107 1250 131238857 131238859
    0x6120e070e060913080a0f080f04170313150207030201200405130902030d021615050f0c01090f060506011403040308041709031608010e07051e01120f09050c 69
    0x119081c005904080251940321000f11140040d6860b10b02500451065a40000d4450b610008003c00a00e40007800018002e1995031041019034480303840740500c0c0e0003a51300800c42d02100003004a00c503482d001850700a500d4110b0404003c07410303925501c441c4824040c0c0f848081d00824000245502885940250b207016101d00e0910682020050301b5031043e401142d2140700000182d48018000c1e43c400e01c10030b60f02500f01e0341180c0700d0400c0a555103083d40c20703840c002d0906c154049800212111650b02c203040b2501c1e118141a26112508100c0c0c00c01858404250f58405814002c9081c40e440402c0c0d141c0500000105410840b0004159140344e030041c01000800300148030000340d2004819611540159940c0c02c40b518000108410f8420403000c2d503494402d40442d0000d002c50f0f0841030040b03501401c0200030007000141120303110f0903c3e02c00c1507440196110144e18601d00221600c2c10058149403d8406c69005141c600490303500005080800d96100003090810004010310181114 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 131241357 1250 131240107 131240113
    0x10509060601050708070f080403060f05011a0a1b020a06110f03090f0f0411030106050a08130201140c010905030414030d02060f06010e040e03070803240102030324090106120e 77
    0x2401c0340020346640326801d801450f0342000544c241c02d00c049480828603403584051040d903a07994a003001c00241912290b0000039500e84400013a061140701c030b5510004083c00421820814800c00a03102d10304458400078503901041003d40043e40d5540b18040684056241c80030704403c0e024040d85081c00f039441c0155154400c000e4101581d031490140071040408031008440c0c84002030100d8060202c070350044a42c01c1c03010001040598000c009085580b1a5980c0c6155a1b9902030303100e0b001c48202800a40415802150900d640030610b004200c0d0b180780100110380d410059480c2891644107034021150b980601410320702c0349c681170290300d82801c4544010101c1d4248945080761440300500860306204528402c1d124039110f80c0c00c966402d1590740c080c4c0303442e4072042c101010b00d80c3c0100e0b031708042480ca1908140040107001d64218400ba410780c001c42c150b07500d0041d90700120186060b02a8001075250042c202640d0b2080303c10f0207031171a03555401ea900044055181502d000d00d0000034990 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 131242607 1250 131241357 131241361
    0x30a09030813150f0f0e0f1204050a05060325020c0a060807020d0e1c060b0127030b071209030e150a021902150301030f0203060f040b070f0e06040e040501050906 71
    0x796101c0114060100743d07800000740c4040503608000201541511140700d1410210721032135030f140200390019a80042400e40b070301d9580c00380d1000c0704c0340f1460044075804a1006400d00490418102840e400010b60221007a03d4078041d01d001050b45a03030201000581c4000400d0800d4204000020010f1240e802d0a030100e040480000e0340f01e0071406c0c1c1020400004854200003581d07003000384003111803502061041c4400d00d0510802810082c1072150100b03035086110b81c0d0824a009401741401d12120313555030254110b6845080556001d80040204240313240ca840c06008c0070b10684800610a44038242d00102c1d070700c10300aa0006041c416408158144a41034111b500421020b555079003a0814070710401e081c0c400038044218000514100f5107020002001b0800a0051402403a000700c08543d80356580320b61210100c00105d034010b00c031032404408141d6aa000d00d0003101350307004a00f0840042400040455410741056201341260b803049014001804001c2c46140c0d0404051409400c5c18 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 131243857 1250 131242607 131242613
    0x6042304021c03050a031e02130e13050607050a0309081b10020301060230190311031005090a0603060c020a0b01150206070c03050409050406021c0b0901050f01090803030a09030813 79
    0x14026048104241611901d031805241c2c1c804c41200b1f41242c00c200219201c40461012074a02c1c0224000c070b509540960300807844654040c80c840d003180e40c0c440c00a1240307a9440c2030480d45030300700915203020f1545516064000400b044042e062002e1400c00d191500c0c0465007000e481c03c8000c80c2040911441040140403c95001c1781000651032480000509202c0d1004068002c03998003075a1070301c004001c12020408607900940c1c2a258800707690611800000034094401c1e88020345100c610084000010003107801c00e894120760100b0000c1000602980d60380b1620183c4807180d040300d0050300412041710401010003078540c050108010329400455549602079502e41c0d010307002c40e06001c1d0628010041503c1744086401030030307004d502884142414601034000e0b400080d482e110700001c00c10602e190500600c103128001c40e009040904903443d00c0c040c0700b403900c0141103150400c48003880108903464104000c50142c18904000116145c890400910b12a0064a100303100c440c510350380c0d004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 131245107 1250 131243857 131243867
    0x1b090114030307050f0a0b01081b010c02011112031f0b04030305130807030c050907021b120102070206040e1005010f0e0613030515070207290306042304021c03 70
    0x549804100c6450390000140000740b940c00b8000300100a4424080c050710190004030351043e84038030a900304c51403a602c415807036445e00c04212504074107600309004030302550f101c1c180c403220150041c10587d295070074019165080c90813241c6100d00045000051001e030040c403005a004039540d50440540c00d034144011b41209120f107102c0581040700c003003104070401d0024103600009007840c0089500c0365540749040e90740682144145403248d641303600020626030001c607461003039203050700b40000040151010425280030704803490003d59800e103d184d00503110b100040000c4c200c10034486d10140340003c03144a000005410003410000b4810300c025061780c0005028030036140446003283c40d0b0351440c48a282c1000705a0025007144101015a455205c001c0300480c000c4440d542901c0e4642e445a50700c1c148103040540c00100548440344450600c41c64001868100c2070061010030035449550742d090407485a1507442d041e040d4148140421490a03a41ca02180200c5607201d44801d6515200909 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131246357 1250 131245107 131245109
    0xf0509040f0605031006210b040f03030f150801150506070305031308040308070203010b03070605040b07050309060304150506010f090302090615130501023a020304091103040201021b0901 82
    0xc05240c407071800c0d26080c0e045802ca840a41009001c070f42e02c10340045034007805404903115220f8aa21020304c80b085410341c000c078640f03215402c441c0704c48050b00d075aa0341201400860000303404042c0d642011303803d9400207010f052000c00800030806481400c0412040c01c40d50a540300340303404422110704201685401c070589204640500349281c0325518440c032a404500c10200007000c201002402104020b68000a080d1700b50085d8000c0003c61405e070145607940003140188408104244070402c89014140020b0450912a4040c0e074100b4000c400851217540042d81c00700c40c0894070b488110b48040703981c86042e074015001d28054840034070344000589503203c1c6000190003845040002200c5440321044907042c1c0340392411440e55880100181e142c4091079014050041c007802164601c01421626046800301c00d14007540624400d5180c0306403411407588420040d40020b00000030480b500b4410001c005052286c0d840d900d2510384002410300318040741c0c0c088915003100f00050700d500c0b2229424 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 131247607 1250 131246357 131246359
    0x114060d0807170418060b0405150903010903020c03060912040b220e0a0e06060906060a18180e0115090c1209050d0306051002060703091e05060709060f0509 69
    0x109180c00c050502031402c0c40340d540702411601c9204a004001140200140100c882c04940e5603900a20282d0410541d80c8610a51000034428441882030345010159400d518140381621480c200750200031a00b03681c440402074002d41c001400020b1103090078083c1076403112120000e081c0900f06e003c208065405180245032484c10302251108503c070742c118050700d640028540c14148207035140e80c5101500c00c12141e10421a050102c1d072040d020002403c540100d000400f0084241e4540c000e10540c0d41000802070100000c050b5589103052414183c00050040b005021f00410744000d0b1035000c6e10040c003400d92041e0f15104817020001b00324400d13801a500c80306004921884403074000c031104d03240c400d84051200d00e0807558000b0090002280c3c0d0000710652024008141e8400c200401182c26032040ea0240e0090070000c2c0000d403090380414010f41c45018900c880441c000650085000c0140c0e04845a074452070a000d5020f400c000c13900014031207460b0140c0c243c01400001009030003885940c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 131248857 1250 131247607 131247619
    0x301061704031205130c05010513030209090c0a0801090203150105100804051c0215090102030c04090c091502030a02011a0307030b0901110a05031f120b06010201090c090e0c03011406 80
    0x720381098030507580c20210300c0d075514040c4807509004e40c0480f0b142e5010070040300c640c0340410700007996501403c29152903103403c6031445005072540d002d00c500b0301001010498680201c58050b00700b0b6503001d010201800c0307503500014003128240b06040c81d00006d2500410410b03041001045203545d07154102002a886103004852915145040c0340342c0000134484400340c1c6d80c6095958040ca90000301903103249840382c291080d41c0c492015407800c0344400d0b0742c034120b1101c01700000c1c05003c010f9088010642c4041c43c0c82004142d8034610b00c0d0b0400d0166a40c1401a00001980e000c2158240110110114682811110740c20130000013940c4128a101c020200c0c41d6035000076001060070360201d032185548403003d80e625002407400504546c0300b152100c0d0032800008200c800c098030036400c40300b070b2490038010040d02641030b102c0180e1820001c1078a41190348030b08844d00003c40300d50030100101002640841c00301c1c1004c00c040c0c00d14405581440c0243c0c94020020800e104800c0000d80119043d00c1c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 131250107 1250 131248857 131248861
    0x301091707020a08010618060e090303041e05071d360c180906010b030402030304060507081317120306060406030506010c0507180b030309010f030b121002070209070503010617 77
    0xf0580403007103940300255952812000140806a00c1200c01c40f0014101c402c00200f9200c00300903880700720588510440d94024000100020000b2200120301c06001c501060501c5190f924603144c042d4a40048085041440303d8540c820341058449401c1200b40401042a48400c541004070448103001183c000c2c00d10038058480c03010610140881d900c000d490741c503000c0c054039000e1951100a40d08a4124412400001000c8906070241c0c0d000f01d0b03004018500d0300d481d010f4211160f80107008292a021410441c840b4103404104c20344000f44010b4003591070001049218900b0100c0b8003084d203800603010820084150b84110417141520382c14180000c10703864001c0102c80441d100c4100506500c5900c4001c03c00800b280200c0d07444908584c800d019814820062645030b00440300e0301c501069004010413021402078200400903040606084071140d010500749280101c45905201c903d640011500d0940c02c101750b0080c2d100e0140c3c2003562865241c954003c0c890220700c2400c0040c1c0c844540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 131251357 1250 131250107 131250109
    0x60c020a260f04090c02060912030406020f1606060e01061b0803040305040b1206031e1b0f040c1d0901031703041a151f0e06031003020315070e030109170702 69
    0x800e803018002e4210425031200d4403900d080005102e9820207030058480d502c00202c1958000039070910707443c0401001d9040d0b89840d030f41c50703001c0d4101c04030b0000c001006104400813601140404142c8502440010524916018007240c0454041e001f480c10456610107500140c901403406c40c0c145680401c12664a41d00d90800319031500131500078096258002405015622940100364040c1a045003601c240003600718050052210154028261b0b820403014000302c244c0d41011128029005171190301c101c1c003070500103400c440815030100003045803440b03c000b240c502951800742102054031015600d5046854600104001e00e092452006e00000040c0400040042105002a040451103010f080074500b00c241c003070035031282c14082c01c04901182402c0b80c650918a850840a48510b1031140350703c1c00703020b901d0b030005100d01e05110003140c0000042c0c60803ca042512019000d103101c0a04006c50014181c0e04001d462521070ba0401c0030758070220b00e00f00114204200c103c2e026031384d1803003144 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 131252607 1250 131251357 131251433
    0x1021f06080313080706080105010f030e01110c1501081b120102120c030601020c03060f070c030212181f0503060d0f021f0e010207030525090507020703060c020a 71
    0xc0c001d1025400041246850700941015030307001d80b0b80c00340030713107060540b101000c0314218006d20a107400103480d00c0300c1190460182d0701440c2c4040b6908004034240401c403e034812540d10022860b441035200f0a0078101c06040010401c1c090180c04c4082c01281201030101c1c0403c0101c00e407860701c200030038050440b0002c0251704441e10440705201c90f0006261032031907203050740c00864205015011b00075111045140106840e44215140c2076a030b04241c0b5281d9040b900540025000c4040d0b1041c21030710a8040d1100000c0c08051108040b0244502d0909041c0002e850001d0402c944901c020700b044841960480f00743d951084c002d44148101a6140c1004103258080380c0001e50450650991000c0c0c010110502401d104000d1315006411090f0b0001203a0366034461002a040381c206240ca4408400c1080310b010520003102c0800ca0b0f601d07261b48040b811038030255804405644120020020001c02c1d0080340d1440003980041c180c50009503c400c4444420f0900807105901007000c030301c501850384 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 131253857 1250 131252607 131252609
    0x80a0507151106130215070f080d020c120304021002030a090603200d060306110c0601030b04080714060402010e04060e0601080a0f0f0b0f03010507050712050412050d12050601021f06 80
    0x3002114a80c0c1030401081300c0820280c00144d0154002c107810080880d00901180e0715541d11002a0b04a20707086d4031004c4242c0c00c40c40d25081c20a40822541c0e110800070003090396540c03580100c407075403828203104004080d2a0b107101401950028000c01f0825500030741c2c03d20072502241804030340c8807540107082c40300c14511903045450840202e041c0740d100741c3e00d60041e02034138440d80d410024841e00180618141c0a103d08030000c0341d101c4c00c014800200015141a00144241c03255801c010103a641c00c140c890402582a034290b00c24000c100540da4007078107200307071280c041c0d8040003d0b506003203116410383e000800090510402101081c490007656100240c000d00400d010081c13024031685080c0a4400d0082c103030b1149541c1d1203420a2450188191030040003151151480d00d601d50b950703018540440400c01d001d01c00c040c0300024024000c001207a04040c480c1000e01456251100068801c48203411034015041c5800304018450360001200da06103604100d9a40000c40d0800520001e4119 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 131255107 1250 131253857 131253887
    0x10606020a110f0d1505010515090111150103350301060c03020a050f011e11030105090c040b190807030b0f13110d020c07060305071205060f030d0807020106080a050715 74
    0x200c0d518403428815800340b00f817000c902001050001d43d9881c41004401080c4240010f10241c080201107015030066000303007907041c54102a00c02d00b02c1e84a08904514100340d2050b01c04201a0303000300100c0302c031400b008101040401e0184400c400c4c00d1007003c05030205001d880306011018481c1000c0c54001c01c10b400500d07a001d0100ea60a00c400603800e0301800e2207950440354000c03426410b03425a030039406003085110320481e91904580ca05010000c1401e00a0040c0c064000100700124101480200505102825501e44280c0d41d00380d010007000c0320b00040004003007500d04001000303942e82e2103d50030310b0664100d43c04400642125403d0004010241084250200c00901d90b0003860054000c2d0082c0103111090740d050954400040d41503038400c0710310f0400030340300c03032400c2040c070440798003181e08004090f011414900d00e0f00c020a25010001c0041d40100381e4079800c020910780c3c24016007000d0000c000142c1040c2d0212707540c10743e8031030321801409009001e0600356482988a10042405841c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 131256357 1250 131255107 131255119
    0x90809030607091505030c0307140c12070201081302130b0613090504020a0f060f083309010f060c0f02010302070f08031f081b0a050d0b010e0702010606020a110f 71
    0x52030b100240c0741215511078011442142d0685540c501d00801c19640304403240c0c4813503440e581e6401401c54034400d44c000709241c0e45800344200603800c03504001281c840742034901d0f0703240c0da0b0405000150900c9001001c0c4800420050314240c0180c0321988505440603580f0808070751440709000180041c010031031a03601240c030005000868650a030080c5026900079074511007880d0b01e8404000416096001d040e0200d00c41580080015204c0c0e00c1003544000c0c00c1c070030b4110059101078000901c039080c2881d503181001c0341c2c3c0b52007468030304620703c3c0303005091034010507180c41d103054409440c038440010080c001d40ca405860b881964000e0b011604050360008005c2d8407900d4514060070746400546d004041c140841107040400b812002980095a8140000700030306064030040080341d0400d00c03131441d00b2030030741400015150ce400005100c120321440714010550b042260307000480c0001040c610444e81040d0040203c69004541c2c0b0b83c05c42e400c40c05414072840c8603800b20340d01014800c24030382c11103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 131257607 1250 131256357 131256361
    0xb070f2402030103020a05090906220209070e01140406120902060c01020313060b040204050a12020d060c02031e04050a05190302130207020108070806090a0207050118030e01090905070c060908090306 87
    0x14558002c0d4141c80c400c59102120796220320074803440101c1200c00700c0c0282d004401048022204000a120142450481440174800d541c0440c0ca599000e407191000300d424401d10040560700071034458101040307001ca01c0c0c101881c00030010994500300c203c80e08025a21007130f2605544a0104450380800c0701340c004d546c0ea0a015031085d03c50011084140ea4842c42d040c520380039480d080c001c46085600003000440d82e24140b020803030721200c1d11501242d1011800980c0d0700003800030702615100061a4001d551150b560210b5081d0000c900c4009508580c003c100c01c0c000f0356140085541503030350030303900c10711081c401405802c0445060f0300065400904800c100d40b20f500c07607400600d0345900c02c0c0d8030840161103d0605413064507003039444607031011640f00010303002c0f40264041c00e030302e500400002c60150220081c40b010304140715029000074408040c0d01c0d05030750b0004090801030018000410281c5400342000b0147c030101d0134020300c01c94450941d80103006031002580d1041d070000342503901074 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 131258857 1250 131257607 131257673
    0xf070b130314030301051005040506030105130b0d1110030219030b0310060e2d040209060109050d0503040f0b0c06060402070303060305030d05012c1602160603240b070f 74
    0x244c000340b180c0b40c40303032044552441d195440744080da81100c0001d080582180d09040400003084024200c841245543d80d402608590b950034001d40c206001c2c41302080030355108018010651030b4014504240341c0100710340c48420048051035803110442c0c0c60002002c846100010b400c1c00e6416020319880c0e4141040480d00480d81040540584400b4241c0080c0000c1c1c10706000c8800f000740e00c2801c140a41e000040c0143c28244680780c0d00490515041e44500c1c1c4450005102c2c919120301030f11285d10100302800300c59440e422034400b81a641d801c00303042c0440c0041181d50792600800103030141d40c01140c0c0f0020540650482009984c0c040c0580307031034032000d1007141c00602c4c0900c5854041c41c0b0300700c0181402270000b004c40f40d0740210050a00f10700d5480b210544038210b00e048000045111300740c0320a54080301c1d403c45002508491780d0100d03a000810400c1c0700c04c20341003643c15402d45044c020800c0904e100b40100c62009900100b488010383d824103146841c1801c0181122110791040022512 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 131260107 1250 131258857 131258863
    0xb1c0317010915060e0303070b0703020f04060905271807031a060103060b03010f0501050c0c0319110307060c031d040c0201060503060a0c08010513020403060c0305070305090f070b130314 82
    0x4004228010f0000715a80d0401100c0c0740c00181401a01034004005820219292046071a800000c0d8100941b0300146481401d250f6805070380f150001401d07140e401c0c012881c01d4217441c4001001420b0704c01c50044124260780f40d071500a080d807a9040d0340381081018031181884414002d603080030118100680101c0c8900c0b0051044640700d001074a4a070b00402c0b5a944501920f060741d00b00e003218840f260416005440c5a4004006020b0700c2c4101d100c040c8640c0d40800c082c240c00c0f03498130f04410100c64180360084a060b40041b89a2194105a1044c0111035010300700310304403505890a1440402c504100040c00071030703407091503000f40c05d21200c0c03e103582d0150024401c8410560464070281d0743e0302c0503e412100315250803000600450010041c0b40350103560a504105401d5005203001da9035038030b0b00200d618410001000c030341c44000700700713003107805128ac9a0700a01260252020100484400ea190300c054050758108039000b282148058510990070406162302c1040320103507944100400356 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 131261357 1250 131260107 131260121
    0x819021902161a090a0f08030901120c0f03050406090203061513140703090201090e01030b06100206041203020d0617030403050601270b0105070204090c090f0b1c03170109 75
    0x4050300c9440744140b502d108662005084071040c01c0c4054411001c10794080c078980c0069071181d4880204007011030a2003081e5072940080c0b005800650780c03044c02600149c502080710a403282c0003494842681012a00714980030003141e43d078640003c90b03a070307280f0b4800e004100c3e152020303400d03110340001c0181207201c8601a104220045038410000420454100705aa00945014010903900c0340802d0790305000303401161403207105040103540c03a0340351a100b142d1308000b603009407088440b40303040c040d480c1003c641c1036040252920107800d2510f080e855659801c10340c03234040c00800d0f41c0010f60901801155008002502141079142c895528040d803103981d0381c1150009880303900900c0000100180c1c40582c022050200c00d482038507045000300781c0401030444840841c10700c2170800804005981c2c510980d1040d81c0300d03804451419061046640449501580c501d11141c9001c0e4400069500e40908030039124020343e504d950045145400c0b1000c00800700d05032040f005000c004a00110190030001b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 131262607 1250 131261357 131261407
    0x80c0a030e1009060516020a08161707030e0625060f0905031803010b0916030624080f011a030405070b030c0304050111040b0f0c01060506041d0a020304080a081902 72
    0x4403250312801c6c48461840103008220016078807200201000421080113410a18001d40c3c003800703040c50a03250210200a10381800610180c001a41d030b007090380013a6001e0151006035035a900740400e00c0b10100031040744030035a410a81d0641c1c00c45041010701d400c00384485000210078400d070080c81c60a9a0307a40c121001440c41000107140d140c29505051140030180000200000000d0711503407070080b0001c0407440246d0403d034544502086041d40040b0b232802d41101d4440c1da062480300303994000c241c0c03100680107500e007440d04c4004004060241c04071078182d4010044903913407a140c524203107242c800550700c860b850010100c1001503080940001d0340c4218001da0080c0446c9040c8144400c1a03c214042c1c030164402c20f00c07a040c50b005a03480a845054103a80001404541300d03000036880ea040f680c03140e100201242c4038000540310850b1070a40254902c00150f0545c03c0c190340e4404035028401d400800c0210500008680c6200c034000e580038428404002c540d44c9003042c4982d150903020304092 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 131263857 1250 131262607 131262611
    0xf070b09010905060c073008070306081c02030705070e040507081207080c0a0b010e07030c09080c010e01090e0406061a03090a170708030c0301140a06080c0a030e100906 74
    0x100428018050b10242550201c05070426030380741108011290040042178560045111458426054442455400600a84503d0040c1e41c2481c4018500c82000b0090810182400c000300030483c000075400c1c550742845400d41402c00c00b0080120b256005102000d4100d120301c05000032003c02c1c80b000705000e54050070036500c08a4132031510a83e182641300701100081406c02c03105002c00c80b280f014142e45040881075451050113615401c80080081e004010314441d9a0288210180c251181c020005001c1c10621407480c54440c0d402c0d2204440300005050001060828480c7c0c0e00c00c84a990242c1440d2401c4141420107080c484001c01070340c06030304c005640c01d0740032046500e01e1105803417262141800a0040e0310840c2c0d2001c0300c50445078030b440904002401540001075208010f10b204000c01111a51650b140071618801841c070189110300684204100303101030740d40455103660200c541d00b42c0c4c1e5034a8100c804220020a4000da038000507001c0c0b40d1468510700b001d0340085524038010282 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 131265107 1250 131263857 131263861
    0x50901110a09140f030a120306120305030a0906020c0f0c0a0605030103020f0d050c030d0c0605060931201504050d02151902070e070503010b0d0506030f030f070b 71
    0x10408452195034010710100d0740102c8100080205403600d030180260140540c22207404160119150407886c020032500d0f485032110742c5040c15418458000104104040d15155800c0c2c0d403800781413032002501e807020f101d8807280c55a050217400d404071542d50b541c820407540c2e00e16045184644035481c40c2c0140d482460100d00006850303101c0e400341d9040e660000d00350207083c3c45000801026811084007100c1da400b40090b100090303903060040c070350191003d440341e84141c402490700b4000c8480040030248210380480a00c0255000c080c80c00c070f11101c2c050710b072444c1c041041066019058070800c009114103644200b540c6520455500054402e03c10f491f10402070400340f002c18040e001d98081c05130001d000354103000152400b545140000716041d00c0e99031500b00c11402580512020103202400360384039081c1008115040000703180c1c00402450898151350612100c800140305001003904002e0b10b0380080385590740d0502c280d5400004003005c83c0c4d40c1c2c03005580c0342a52030b08003017815650b0700000f0b40 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 131266357 1250 131265107 131265131
    0x3030509071404150b0d0221070e01080711160314010c052b020415021209010e040c050c0f0d1d06090105030705040806010905010504050a0902010c0b07050705030d050901 75
    0x420106a40b600710100b84181c041d042070100414000761001c48001042c0400150038004500a08941d0720040b4090303a1843d4240e802c1500032054404200c00d40025010411000e600c50615030325880f00b4030f0300003881d4403811821161142c155990702c11034010300624486a034606415401103c0c803450000d64800c1100b180c1908880101142c3c202090041000306070100c0d04d1083c1100100b1840b861018508802805004a0700690015284e84180c85201da11458042000100c0c1e00b401204039458149400700007002454040300d000d004030b40f0740810100c0d00c0e00400a81d0040c0d40d040701282c48034807040441907030b240b94102142d0045012000c100c4236a00307100d1071400403501d025240d6860080c14074011104d03644014480010828140f2001c16003c2c03040c0012402444085408601c42d410802004112040034003207050b4030340b50906070700050340c00c812403052580c0c00c0394401c3c07100c0d600d8031020f41c0e041c400d5000c0280706020000b20308492000b90789c0000c1c05041010020080c0008807a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 131267607 1250 131266357 131266363
    0x20d08090604030c0308091504050f06010e1e0a1b020703110a0509010e0c0f040602070303020c180a0902060c161701020a1704110904050a1106090114030a0207120c03030509 76
    0xd1400740005481000c4640072074000c406c02e0b500301080d00100c503a030380d8900342690781120303041e901240e4503000440401e032808030400c2b015014202941d007201640c14200d104003100e50010051030036078000040020307031651301c0e030344645181d104446985454410b41c090081d100c404a000031218a8214440011107081c40d2003c0b80c12b03514060300b900100e900f001030366006a2001025802168020040e0484410260014000405140d0024080300d070a41c80e012741810403a1030114098004a03443c00c1e1a2441029400d03085103001a00282d01b041c5800407440340c2c85003030350303650b4a44118035100074180b11010410302194403403800c040002140c1d400e564280c0c0700e600805400640382041c2d00c1f81401c000c401454206219041c208520300c00c01006c034039280700844040e10580c004010030024410036154000d02860100c800c2480c0c03040002c0041e100b040000e41a504500d808000214110f0140e41154205600030b40c08020111890400070b10b100f590a5084000038180720102d44841400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 131268857 1250 131267607 131267611
    0x310b18070302030609070305070e04050405070302100801060906030911060c121902060109090809091f151b12180302060c0a02180906040f0206070b0c030106090608151c12020d080906 80
    0x1d5640c1c000403114ac1420400506806442a2541d00422000100507034a0400c241c41b100d216450f007022541c50b01202170160600d503032001090504001704a400180407c00c8084d0703800007103c4141d00d5030b06407406075140801d940901017003004001501c45007081d080b40c580c5070b0030b4826400c90784c1030f81c1c80c0c2e40840c0c20382d100c80c0b0000348101400d0014008c10300e0031750102030b03004560054035480c5192070350820492030b400e03138486031406105110a08919903c04501503c0101c1000c900701210202d031b480380740d4032044004000800441603d41000c000c01030110b40002c5800410790341d00c80c605592101c0c1c9400c46150120300c10340e20400251101034220214600c030b0000d19004d00b0340e507500c58880c54124609080226484482081044e000039101c5c0c8105008140c0c5040c000d44030360400320302900c14545a0003c00074040b082c4100210300e00a03d2104803000c1c015180051200030f04a0440d903203403c038503001060400004011000c07070350300007918549584199242c0d0119200e030000c0546460b01 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 131270107 1250 131268857 131268871
    0x30304030f06020903150708070905030a020a090e0f030d050604061205210d0510060e0402071e0c1203020607092117040f030b06310b18070302030609070305 69
    0x200701079603000720b90154083c10400502400396013030340e495050039861000d0100c0b165008101c00b041030010055002000a0291030194020f00c2c040344e2a0300000d0b11410039106106200f900c0da840d80b00806800e0005444001c40541169201c442d50030780403002d0041285d80d07600541c0362400000e031071001600a043c1444d040b00c09414030b1614076010080004480501c101016810005407803251110303c9124819030500a180b00c885060480040c414080a000213216a005000c904081031f01189030508900081090310840155441e000800c5941380e4003c05001c1e800581d940d0505401041c0940308000d5540c0d40b4003807079169685400c552030300c80802c0b4001e00014824000160381858681d501c0c03e114000c0c103080a984a0001c010303030b0516003044a0740c24510041c44624180390700022418140c2e050501e4140b0101204c2294070241040d440c60b41d40d07202c402861645d12000ca8450704000e690000c454103181c10840500603510544820b07008108504c0000c100d40d220748940ca0140c54 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 131271357 1250 131270107 131270123
    0x812060d0c03060b011403011d0604230603120f121f090c120f0b180105030604080d0e19051b03030307110304121202190206040306020d1b110c03030403 67
    0x41152580c3d40204844500f050500c44202d0a804a804403034010798002c141450102d5020150a07000c0003038008080d03c150b01032412314810034520703051000380300b2110300345190f05c804941e0b802001a141c504ca0280e21010803130006514400b500c840f000404900070002d404030216242c1241040ca1940315842010001c2c80141080c40840496000b828800c40c082c80c2203401440604c0c003900440c2d503480c1114640c04d94451050442382815410301c0002c40c90040c01800542c540004281c50744001003004107040da0003d0340e803c8131021070b8006001540c400c03044581c041849110b401080031040d0f0103032070900c0b411030244507001070039400c1c100b440c1c1c01601850544e1186031040e5844600690140000c1c0000d210200340c80b208031415030101c40c01501700005d42d40311044080e040205840080310640c40110f520740141c0c840b00708940480368010f02c01170f50346e00103601074001482d20034100840050614050004e2036404010340114800d0703541600c0c40c0d91494400c1543d0b9200324400200052 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 131272607 1250 131271357 131271359
    0x18050a090518010c0905040f1505040b0d0503040603060e092e060305030705010b09090a050726060906010f0f06140a05070b01030804030c0b040806160905030a0812060d0c 75
    0xd80541219401180c600d0300744078600c40b00710016095401d0500d041c000200140f10403c02c2d403802e80210f107e22001d8074410450b01010b20038030400c051560080c0d50169881e02d00380341040d25140841c40303403141c004054940396600c1360401400380805110784104c0a4059003ca14588004150101c41310580640d661740e10400903804480300305504458208280e40b80e100102046050000380f1909119000000306160001c0030001042c40180c15104150300c441501c000082e00080c160b804c5d01c3c4168004030603d290079034a0f605006a0122480071402050140021890001045810fa881c1d414940401685442100d540340c000e621a00c00020081d904144460300301200400c0c0400d454601030b80381c42030544503c3c203908801c0c0e0084a07000320020302002440750560058018000743d0700824582841c01148581c3c030f1502a180c2200c1c00800354041714010b0090b005100149005000e513456070100341010460f980112418020040e000703800260b862806803a00d00035643d000c19020003903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 131273857 1250 131272607 131272619
    0xc060f091b03030c0706030f180308150402090406030308180102092803050d0c1401060b0a03051314030c060a09080301061202090a0321030b01090504110f0a09030318050a 75
    0x410000340e01c2d40501081000400316641800f01d04043c2880e52000b0641c0252044482c084480019028050100040900f80000c1e481900e044d080781c5c2180c80c140990419500040c02131003485112a4801e207086000800c240d000301080d80314092103a84a604540c07034460341400e07442100b401951010b2050f0f003c1c40c104000001000451210b03983c0c41e0040d6459a079114a403144542c132100c04901c4034500b590070400142201c4010740c4500c3c2c02030002c03c1c9051542d0286020354118078090540707410006501e2822203034407410f00d9810448005140c92017070902d58503540400c0c1e9900c034074000c50f400110b65010600900011592026800d49180e10380441100e198020b6861007440980810001e002951951460b0f0051805a111104010755900403280c1c0c119110000300e06060400132120406da8004001004076602034070301181d40382540882456600c20140401e55020303020640450b8603901c83c400b0400e81e482500d802d800e81030000d0310241c19108610905900c12402c00c401e101d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 131275107 1250 131273857 131273893
    0x11010b0d021c050109020301020c07030b071107060c0203211c060e0a0504020d1709040f0509060117010e070b0403110312070807170c2d100203040305040302060f0c060f09 75
    0x2c20740c080c1c4000a4000c0c1107500280c26680150507000d2281d001c0d41e01441481500440c0503040b507170034100751001102d40700043e520303500c880c0709038010310101500ca681551420301003c40d0396100e00c5c0c0141240c2281c0404a00107410064264030350740d0384903020000d10100740c0300386402e40e03500c82d848000d80e503621024200903202c001c004a0f0042c0c000c01410001440140d0001300c0050914a03941c5c8030701c3c1384070030311045650344503a105070b043c105028030080a4022441905594210b030080008102c0e41d01d603036002d072600c0704130b0704000e101e81e1358002245080b8102070401d89104022070701d22644034000b0560342d0804403201c031001d03800401c0004005225040240300342845180030354076408603800c0300f0b03107540c201410041c41c0d81c00c10245054000aa51070100300e004204c2c032004000c80d4009910365940e1a410a090314880e4000003060074507002d00143c40007903500425a031344c1c400500c0e41c25185904006250907061140c1e9000c200441102da0381e40344a908000010400c1c0c954031248408 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 131276357 1250 131275107 131275159
    0x6030233070317070c0b130303110d020d0c091802070203070306020a02032805070f1104091b050406030b04080d1d010207020a0b09030d08070306050d0311010b0d02 72
    0x80036400124100c018a040d40014003222402503c8180181c00280e40003c07051400070a843c0070042010340c4180003811481585030080024903d08086903402e10b81034000f002c1c107901d00b124041010a01c0150b022194000302419800018140016013940c102641c640c546806400e4501142200a24041c501c990203801c0c090700080031075040c1643c940b181804c80e48001c20744001a0800a510210700c00441d005481c48180a144000d580705801030040c101c1c094010014241b0304000e0104062001e03802c918005ca9030010300130814a0120310301000d00440461020301012100003002405240500c510400c8039004071420600d5039507580d4010490f40401300345c00304941d03100d00d100544000c00f900c500c10503d80300c00042c4c2e91100d0b4010010024540e920481100c0b1081120000f55100441d459500c2092402c08003044c6d00c039204150080d040e0380d008603070010350440c00c400c24035074032117060103038161240d0080190100c07000c00c0c862001c006281c065003007442029144010080048805 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 131277607 1250 131276357 131276419
    0x604031b0303020412030807080f0c0d0c03060504050f010501020f0606090c0c0a170409060b0f16050f0a0501090c09020703170c0d0501170c1c0b062107080d03060302 73
    0x149090384a1005e81c007610ba00381c40a070005650202003102442c3c2004009400805a010032002c614101003280d1151040c03501c64082940c684003021001402074101c5d2002d00300c001e1042c0b05601c0c01301ca010314155024801c1310300511030500203007a1a00d02040d41c5014070b1000d454007046650302103103843c540d4000804c2d05001d105003400c40000c40e10812242d10941402d0220036521407034a00e00070241da103260403618401100704844594805040200d030700a100700340b41141404e929080150038080d0300004640e081c05440e00307503802c20806600000e1528416044901610745410824003207001e082001000f0034074035038650b4036819860111b0380d4001805034000b441d00c2c040c401070700190b50342a4049010303001035189003142614103200c0b030b4441f090243c1d548108502103001450b842c40103000068030a01004010803a9510380000c8854040c01c0d1203520020612a02041a581c41042c86101344070f008404401520b180710380071b00d0044940003401000c812620301501403c0c000017408032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 131278857 1250 131277607 131277611
    0x10e06061c0e07091a010815032a04150605030612011529070c291b0606031603030302031009110a080c040b0f03090a0206031609080604031b0303 64
    0x854088255000e29800c0d1000c0b40e02600755946071440345016580084a000040c100c00c1c0081410307079034440d00d9241e024010f00002c20145d000303180032905004003800705480b00c01d070300c03c4050350082401601030b0761501c06680c10000311803090f54240800b00d00d4007401001074400c0011030040d103044090301d414405403c0000440d03410b030501000d080280d070703802803207040c0055281840c10760f22100440310014100c01c41901e00080c542c1d5011905803180105000144070700f07100b00c0300241c0a10114056400c41020320b55070400c0402500000340010381580c0c02d0320803100060f07250304007c03841052460141032034445460840e5000c0d0043d4200400c0300e01c0c2d509c0c02000c0003480a02a01441d007030b41c50b00d0a085c03540c070941600000c00d0000000c01ea50f0505608000800020444100b02c400c00314541c00b40a8032501e0b0080c1271030a000d4891742c046d40c0014088244648020b1101000110310710540f142101d845c0d45d5010252940d904850141c0810340e00c0b400c0c0e1003440c0c01c0c103030503041040c400d04e80 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 131280107 1250 131278857 131278897
    0x105030a1506090810061203140d050109061401021f2a0c120507080a3b1216050907091205010b10020a0f15020c06090123010e0606 58
    0x20715001c828668482c5000410b03d020070054080700740501c12058000710424440c003824405200100351089000400b040080c0d0801807444003114141c803d070754204807052101e543e503158a00083c0040e4090f01340800f08100380c150241d800000c100c1180032025441d80340c40a0345041e07141c01010404500103a01207140d5980107103a10780341c82c04000341e20944030140c0b10360305410f0052104140c0c0e20000c0a00404210880102d00380c1c0c0c00740c0d031000020f40340164100b0311480310050764025140c070032210290400c502d0203140340d40003207c0d6800c03a4159048200c3e207411034105507039040440703e201d05081c0c50f00020f00507030400c001d4a0350701204030705010300785a58880c0034200702d020381c5c4801d89060355500050095890600c160084c08201403004021200301520341258840c840c180c010805030310390a04d03041c001d0164042d603000ba40f5100030380c0c0051403c2c056060180c00a503110b1160345845d04030120700354038103030f00080c16541482c178000744075501d0005116440d072200082d43c1c000007013051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 131281357 1250 131280107 131280131
    0x3030b0f0603270d020c1306230103051005010e132003153c15090a050405040c0b09030c0402040303020c090106030203070f03230705070b09031303020105030a 70
    0x20045001c1d011010038200030701c100701ea1545480d00081420344242d0044c8204640103070b40014200760401044501000d03410408584d00001c0500c3e600c5200002414590b10072500306140e0344c0c0d40d500000380c806220603a030707154080354482d115014160214a044c00140050b0400f004c0e5459100b8032440300140003c4036554090b060201480017441c0c62900104000c5d1002ca003a9411554800c1a1404044062010003180b14080a0f9843c841486880c1c074541e10000075401c130300958004080c2103040018540e140e298080e41c40680c665001c0c04019100245506142c45603520464002c552184c0c01e5042011010143d4031a480080d41032040d4140c013503a80d51180f0041004621035001441544208000e11003a90030581c040d105051040c41001b202541002868510510314070f00007600300a10a1403035426000011401d410910090401c520540c100d801086102d000e800048810398542e59a20350300c0c8503a000e11011141c1040003000154028009142c0140002c103020403120340b608 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 131282607 1250 131281357 131281369
    0x40603080714010f05010510050d091e0506010b090d0f03120f0203071d031c02030d0f0606140f04090902010c05060a050105011202042103020304090203070306031208060d03030b0f 79
    0x41c2600c603030352900080705400c1d0702440781c000e00100040e402c1c02698900b500052110001400f103106101001a0441c43c011322a0300038840c0684c09020f50b80e984441d210f0ba509131960000c0e044415110f4003001240c1d90260354181c660000c030040c4441907080440c0d88104170314415540c11024004101070501211381c407401003000304007910000685a18013158020069505070464400c400f40c0840500c0980c2c8001c520b40840c0c501001c1c2c00171110004460492843c414a61410616031402400c001c004d00c07250010300888080c1c0d66610000385040414101c1031007030550a1065483c100003c1040c038005811401101d80141007001d0b03402c1107500c80034104030044412a0b410f0369100010b0000b9030b04401a03003220030402c013045080c00d0a103180d00d00c4100c200642039105450003084441014820412070b0054200b01005544906040310054041d056500045840081a00daa0410980b044407000d21501e002481d6528403042500c9c02e800420080d109981c00458a10340d80341c01e03480b89 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 131283857 1250 131282607 131282617
    0x6050a02030c120703030b010f120203061c140c0604080601060e060409180b0a060b0706020309010e030c060610051218010605060a0203210408070b06010207261b0d1104060308 77
    0x66503104c1d0384040038900202102e0044144605004401c50303d0380396568080543d1000071001c4100503504d80f11407001032401c4100400143d0000010780c504810042d4501090110302200c50440e020303ca050002c0000c1401103002c3c0318030b2a80183c0040100300d00c107180907104100081d19062519850790a02c800740c82c10808a0f142c00d0501c441c00340304010460000d20340c400d404900420206003480c4281207079201d0103a010700a05c0d004030100e11941000e602022a4090700c0c000c8941d01c03403103540500c2e10349504941040c070540c103c091404040d80180c0840d85070a042c20004131165950002c0c0c00a040c4000f058011507650f07900000c1a6600c0e400020440706c160740d0021604c3e020301c1a440a01070002c40c0c100c1c180070744090144000111480240d41d250355001d1b5440b0309582c1c41600403454080c4550103429041c0201e020014414114031061080c017000c601a6103001c600c0c01c115050070103240e0221501700f4070001162012907440e41c2c4102455400910100340d0981d0782c1c940d028540c100c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 131285107 1250 131283857 131283883
    0x31a1e090d120e032709130507050103020306010c20060406170604060f0605030a0b0d030302040503010b0a06021f090803090106170a0c050105030a0e0d0201020a021e060106050a02030c 81
    0x1031000040a50300704400b25407107020300034188120041c03644800e0b100c0c0103940c81101c940981c41d01c0031122041040c0b01d4010b8610141c0a25028540881b5981400c10102d505444500170080f0214446d40b20b402181d100b450182c440e80e5240e0950340e503410305a40d20300411461942400740d03a852544e0f506d801000200305c0c60342d40c040c16950003180421210030161900f40724074a469010049084041403140031070315141022616940ca054286002e807440b809010b40c80b400103a9107004040c0c26034068010b0b124198008c0200390000001d00c075905140b80582400750780072a1050300754010090030181d03145100e80c2d01103651252550380f044507410130345000c58981d4581900740b20301500910110070410083c00201028082501e03004c0c0c00c5032550162a041180020004400385015003015609690210465035040c21000e0024000c1d00705070100c0005016003c02c86011a4644994141c19074400020b0280f907440c007a4281c80c280d000c1c0e8168019030206100c00035030514140003005d100c01d1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 131286357 1250 131285107 131285113
    0x1c0e0f060603010b0108040f1205070602040303050415050c060a0e010e0613031b1703100527180303270706020f07060f0f03150803131502010501031a1e09 68
    0x4041c8101403d44100c00c80c110304000d203010411020480003031107010340d50740160303c3c101e545081031400c5420344291070010f00b180b400050000105a840801441211420310b0b00c40d008407040c40040760a4481c03040c030300240e94884001f103901c59502d80e205070140312211000040360031100f1070540c00c108c0201c94200c0403000c801940c006040c4c104103080014405800503152101880c0c0d54120b11040c8120350b1018071502000240d91011450326000140100505144203074840200014800352200c4604207850a2100803d2260710722000603100d14515001460556613a049010800c40c0c6000c402070000c0e003030b00b03003038000481d0030f00551014066503030242140300d40e4154103920b0030701168807001c2002140401242c40503489003140742118554900410000801100102001502c1e01711400601001404142c4407642d8546a0100c0f20103403d50050300b03200b00d1081c0e00302e8801340f2024254040e04581c4000c004681a24240d0108030001101040340c0100d800040885c012200810154 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 131287607 1250 131286357 131286361
    0x60b030405010605040c0207031205040e010e0a0b0a06090e0a06050a150206070c1106030a0615051824070f080301090f151a07140604052406061c0e0f06 67
    0x1083c020540074050070b8406101001e01d01c82d00959800d1b0500c0041d00100030425078808141c85807080b1001480081455005540c450312050103125058410240c400e103000000065800c2c0025401d00b01c450325151000d11034644444054803202c005c1010042554410000c00c0303d0340d41401000142424501140040d01d01c3c500291400d68064207142c00e012000750380a000843c102c082a03101d43d01503035207640304c0d1109820800070b00070135086110b2110101d01d40290312940100030300440707800c02400712a07040e465802e0188110180c3c03500041d16811150281c1d61840d43c10090000d1845143c03120518040c80d11810516002a0010304180303883d111000031100841c001c6160f0b80c1000d1076002c00d80761410100f00d0240d0b5031200d003d00c01c45030105060b002c1c8011103000d8840341d00d07000f003a55280d05d0907142c42919031501c80c446602c16004002e8410155104804c0544501d1015110344d240103040802d06120799411020f1003071a0340c44c0c0a40d1907000c1c1043c06030002280c1400011b280c14 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 131288857 1250 131287607 131287613
    0x9090f0506070318030507020d0c0311191a030c19030b0111010c090608070e030106180c09120201230d0b0406060c020319050c18011d0408120901020d060b0304 70
    0x2020010b401c0700101410000d40901500708030714200800c0e0b0341030400d10740d1840c442c4041245410086005801c2004003140002400045a151009a40121080924904040c10000c200c410358020b40782400300000719019100e40000c000c5d0b1300308040301c00c84e5043c100300c81400101400048140e40000351951004841540c0000009042d40c050200910520b0781404004080a10f280b0901d810406d0040110b88124001d045001d8250000750003480080d0f121039090150303808820f0b84003c00b07403504001911b0715100d04200c41c02e65507038100d4820303800607617001150240380d182c41c1d81021440020480181e18281d0b0b0051804c401040300124050307150f1010081250000e90090081c04002c5004400681e400f1500420311000ba2184001507130305c41c07d000c0d24045807400b009400c122050803a1101ca01005000d40c101e5006840038061a02944c1d07451941100541d0014000ea03c103110410204c44521812540404200c000506107a1504040016908203510003245004004244018 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 131290107 1250 131288857 131288863
    0x5130822030219060216051c03120606051209060702070312050d0e0a021206190f02040e0f090f0a0213051504050a0b0a0909020105070206070c05030313090b0109061d010909090f05 79
    0x102c1a800031b40600d001d854100820103040c0118122540012540015030405008071898003580070183d50800c121600d441c0050b2490388004c4142c10b0051040c0006020b00400040380d9125400c0d55014012181c07950b62002c1d900d040c910025814006d06000a00c0780c0c0e4068892105000e2003000108816001070043c80341030700c03008291010380d802060810034480750004030f150001c55041400182c59840500d03860080c02290460f2104043c00d00c140044c14180b042c03414010440300094800c0b00e014550060b90f980b8115800940054050040c000d003842c880d0701c500e0b40301c4180180588220070000025044990440399034140380e036119250001410601407400c00b40c810030300c08200212a84d0000f234554090500004c0c400c90002816030204100c040c1f41600600010703007201d44032551403024443c1c852288c0101502c131807070810086510349c4912031510490b42d83d52110103c81d581180000d5440114007111810700c42215400501c04141d13220700d034482070251044000340c0d4072a00e0481c0c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 131291357 1250 131290107 131290123
    0x10c0f0813030b060a06050a120b03070e010515030f060103020307120905030309010e0304050a0308070c03170301090b100e0402090a030803040c0305070f14040207021516020301051308220302190602 87
    0x4011729a2200c10b004081d089011900d5802850074409a198049888103003e008039403840b5130140a120713400601050080c0001d41030b990125404006494012840ba68a01040301c0e200c10180c075440200d90554040d90056410034060715203c049403007051150b805a078a003c82c221210f038000420011101420300c01e213240000c04e00041c0d4505481c040005501214500015110400016440040008001d07040c03004540c007441881c1903510109180c04140c200344034a02c0ca071414152040c03091716000c00e4648020995844803240d07000c260080c00300075003046504a4021030f65841c080040b0701000d0182d441544580e15120000703040d03241842c1002159801090766080e400d070148002c4021101c501c5c0f95032030607a401612900c80b400003526440b41c0028110207110001503484084101c5034040480d940282e0013440b1035218418641d000300d03108040901700031400c1c401c41003065280c0c110180f070302040362440d4a00c6500c0b900040c101c4021385c450440c01e150001c2c1c2c00c014603074045c80051 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 131292607 1250 131291357 131291359
    0x2811060c06010303120c0c17040e0703020408100209090f0402060c070308090f091e040305131205010506030318040b0a090c110d0804030c080309070b0c070602010b0a080705010c0f0813030b06 84
    0x71103002d410410140c15408514001010402c3c815035041040c8510380a2714000c06008030500014101100064020340c054025201e49025000f41248560310070300841303a200001800c0802c0503a1504012091220041c1c0100d0f8440d00422540000c490100f00c0c036400b450003101c520b85e803101500d00b044241088000c1c040d0007000308404110b102c80071444c8440d129880220002101d64031490304494a1003041c8131507001d0310078100d0200d0400101e04402200600c2580200111b40354842003568a0042c0c540c0514050409104011070381810b402c101d606a41c0642052034403a19504d1840c20b407104d091654000914501c189036807034000300007120401c0d00c1030914040d44d00301383d1001001c0341010500944505800800b103008101d0410041b0020b15032070503c0b036252035490000a8840301c0c507120b070070015824422426000c1c9400d1113150b08440f0824024505180340000544000800034015107001e0160f1548101207080780c00141040706050082003070b04c5086140540b02220054401 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 131293857 1250 131292607 131292611
    0x3070b0d2003040807030c060504030905091b04050d021201050106170c0702130c1e021606030e0c0d03090b0403050303040210020c030c040e0705040609050601112811060c0601030312 80
    0x2030111511601280c1c1c001e90061042e80c5c0d0b484181c2800e0716419581980103086501c0c003001c100038564440c0112060300c00850f00011142c0790b001890851120782c070050404000100401c000d11b2800d2000d00c00c001d44064458100064042d0340f40b400c40c1d00c00d030b007d04081a1002c07030013521620030310580c90388503800c0c00394142031102c02c1e00452414004609100038050b81d80041030313608d9018007600c448183d0201024041c070410944002e407124034501c10186881d14011002c80c0303050290066801c2d0f050228000d06002d050070080090880402505074140805020017060707000c2203500800103140607400456807800c0501c1840380840230704000104541118990070040d41c0c1c0031800c1c45a4403c115000b00e166000b800041e400c107040755100690040c580710002460141da03810041c860071098840d01e0028560042c00c0c2d0b00c0e010590070403120304002804692440d007890006e8052140150104074902c01e040c80880c042d503100150039441faa01038030042040540c001403401611041e1001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 131294964 1107 131293857 131293901
    0x21e0703020a0b1317030a06050d20040612020d050f01090302060412050406080f09120c030d0f15050906041b170109150b03090c03070b0d 61
    0x241110011000d000040e4058404402080d6050f0000c601a819403911700401007182d200828408101d5039500c408a020740b2074171034669103180300d40f40c41c454610980c420307140800320301f1070514480d80c00d085d0148513910310104900c2d00d00394180c41000403180d00c1c0c03401e80d08040000321590181c0d840e000202c0b05042d800540c990003180200c00340c0c01149c00628080b038041c030031809034801180068000c6019410149a50fa502c150340000707548998060441d8088598404000c0d6070880d40302181180c02d00000344140d1b01c0d22b052494040101041c04d550608248115118881c4202e10400c00541a603c86401002c0600f00e5038000c6041075450300c00140c101d0102010700d4040c4400d142c004035102400e88680375020350700c80303902c040e0545082c40300704031644001d0044a15000303003003503d82d064404209074800b400d564017241d81c4568248400d64100e81001c1e04144c4000302c8220 = true := by decide +kernel

theorem cover : BRFrame.Cov 131115107 131294964 := by
  have h0 := BRFrame.cov_init 131115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 131115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 131115107 ≤ n) (h2 : n < 131294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
