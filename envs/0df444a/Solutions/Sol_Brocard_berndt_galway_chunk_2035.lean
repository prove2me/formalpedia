-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:30:05.247304+00:00
-- url     : https://prove2.me/submissions/1a2c379b-5716-493f-bb5a-fd240c9a5fee

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 365827338 ≤ n < 366007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 365828588 1250 365827338 365827393
    0x11190f0b0619030605090a021915020d080118060509011d01090605060418020705010c050415020607080a1503060c0c0b090d050306010503150307081f09150b03120408 73
    0x5040d248880765142e40c1d039500150b80e4803c100103980c0d2100e0f5121071419402d03180007540000c606950040600c45030401c04104c40504800c010081c504407c1030703880d031404460140001d180b503001001001c0f03940c0c0d01804115604280000d0440d1104c1c0403400080e4260044002440e0100441c41c00480050740300d801421099001c010035401c16000070190f11aa22460311030899082c010303001b81103d80e04075422160311200800c40c0e801e41b20009422900544513682d042041782c840c2442250020444510a05040e51001d025950340880c500003081251004410610282c0d0040300088091040d50700c51051038448070384914580c0f91640034020014481a45034100031120741c070b1560040103403a0802000d0a00c5600c95aa0450011781c60500450580c0e151007000380001d10315001241c03a225294510301c40740c00803408011182d0070b80310358540050901c4190310940ba00840b51364815085c0680040a4401907007030244221a0354015401c0101c65811481d50b210103003400405c864a00302 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 365829838 1250 365828588 365828599
    0xd05040515090319021c031d0316050907030207230d1745100b090f1015020c0a0906061d0604170c0316050901030311190f0b06 56
    0x2d2181021907220540280e400e07030301110500114045681c1d001c0c881e40e1724600411085103451440c20700906551045182076a5248108074426081c10003007500031800a0b42083c2a0101d8500402d02c00d44140080103502016030a029190018a00103d071865551b099503031007205c4002ea060660800480013512014003211403480a1014000116030380d2000c10f148800c0301d000e01c100c0004443c40906001c600c03040701070fa80b402155030764940580e00c0d2207404c070b400c40d480104001620300031620701828080c2c0c014620000648550710f1070094940c44896640d8078844182d032480d420120100c4070f808000913800440d40c198460902c4642c001c01800380704401d001c2035242440c050000c071050748000c94400c5440c001400f00d500c468040320010080d08203c2ca02e4058114031071500d8125503d0198440d0088004103103e00c0108038140c1d0907900300034030403006a461a40c0c141c03818841c049207107a107401400b10500c40703040f41c41c114400f0a801b49110310b190311020b1600c0b8220040c006e0201d44500c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 365831088 1250 365829838 365829847
    0x7020d02101815091a090c0f0d0f030c050d03050609040609060603050607050d0506030d080c0703140703080106020618190503090d06060f0605390d05040515 69
    0xa960014510100c1ca040c4036000a8075619001d09448240d210a805443d07010a41c4a41611904592180100e14096400d030814090044411604600d054449a40a074080d106c007180e20715008030061300441d0020000c0803018540e81d80c489025036204e809401095000303001c0e40c1480420300007441c5515032071030708210754540071000640045019201074101a40c4024840420501d0b500c0b61000d150840c0460740186003003c0c0c000c220b41d0264000789140740c10031020400c07909000070003451014a030b858038074955441805075046504100b400b601000b00080040a0000d2920020000c0900a40c1c80800560400388042d141ca0400380c021410740c2c0392010100b260880c00320b08591000300407129030031650014206140365020f070880090740108240305403402c11840e944400d08484140c08407450296403005d0a07143d81c015007407410f030080b0380c00001c00b151a01181d007030200c568086000f00c2c1102138010b10640343c44240c81c8900b020800000302807110380f03013820740c1100740000266000e192 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 365832338 1250 365831088 365831113
    0x120c0e01180f030b0711060117010c05090d0209040515010b0910080912030714160501050603120f03040f050a0506060f151b0307021c0317010506181c06140702 70
    0x5100700f4031000c0c0c0f00c80c1c00b00000c01d505a06c40c0002d0a00c65036083c088408a50311241a4100c0301c3c401d01111203a0742ca81541036416031301030360944001c0c1d1001022400c0080c0c00340c01f400200c1c00c004000311514040c1600c0f0207104082c4000b000c0c040e00c42640b6840c2c8800c807a4003400300001310340320404240445642041040000001d03074040f107401d0b01450940741e454014040e00c4c00c0d801d42d00c01003c11000030030705c0c1e03418034084880320030f81c9070044009000c151181c9090544070095110b42a4004104020000c4601c3d140401113070814890280e455050703c8646419041440c081c3c000c4840d5080203040c0601481c20501444095400f101c80720500e521100070f454030780c400c0401031303c0840f60b0080720782c0d00450103100341c40b01c017900505119124007807151540300d4a42c0d02c41c0708402084941901c0b51140b2101c020a5042c0c0d90090565460000000c0c1440b0060559800c0c0c5a4051a07010080c03015003038072254070243c3d0b4424107001c648901c4c00070190000d200020030100466104403840f590 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 365833588 1250 365832338 365832359
    0x40203060303070f0201050c070305061b03240f0402030c03101a0d050402031914060a05040c0605090f0a0f030b0906060604050d052118101e120c0e0118 67
    0x40031075110000e01e004c003c00d480141c840b4000c031140a10307140110940001401400314102e885020000c1030b803401c2c003911300d20038070803030000395080300d248200320002010a000c90003c0e007103c804020301c248000b1807203000040503684101c0b22950170300004400d10207411702c00300001d0064059001d0104400c2003458003c0d1280c01401a80c0c1c00d000d8944c4d011030155107040c00302c0218100c840e103c1d003000d9481c40c2064080044031035420030561060200007000e40c1c2e02407107403a00a07948101c1c2c205602d4600751080700c0340d41103200c0184c1d0119482c2c200b2000c50351110440301c010031240071220b4181740323503003050150410000c1148040b03070042410030075580e0f100b008503802e8070302c2200d0314242c900e200d041080c509074a410340a18036001a09038440c1c1c954500000d89803485c004010016204440d0090006030440e61000d440402c0300c3c040c08002d5002010180c850b00c2140c0e180c041c1c09080c40308000f00c00d441810802102180011703401d0001c40d44d10001d04001e03030356071071131500c00580b4144010070b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 365834838 1250 365833588 365833597
    0x30307030b120a0609030f0c02010203031305010e060702100f0908090d0807050d030b042403080c0c0a0f0503010510180b010507050607031a030a0b0118060b030c0301090506040203060303 82
    0x20101551800c07806065500e80c0c02d40c0100e20654000c64440b4807440c034021009100248041d0f012422440c014145244299201498551b040e0b0245003540c86075078403440000c0c10440c003200c1c10354030740100710342014080251902c618260b40c018440c184105038401e0481c0d40d41c2041001e100d0800c0c8164001c00d00010450b10714903020340f45074114541d40c1c00c000c0c006000c1c0d244020000c0c00b851803840e09090303051300710f03104800c4200d604004281c00403904c00240d0341e807103100c244012f01c40001000849c1b01880a0201c82d2416801c0ea02c038080001e00003119960941c00500058075454014001c1d8242482550341c0040d103440040202400e10403c800400300300607804080703d44900302c2010b1039200e10103942000ba800800c80d186c509001001501401303d0000c01035206008011440f0307680380000765101c00c0c50b000012154a40d0804040c0901000f820010b03100e41d80c1c49000000d0049030f210000c0d8400c55291441c0f64503541003010072001d0f00c0b00070f441c941c450303801031060040076a008421074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 365836088 1250 365834838 365834851
    0x3051b09060c0a05030d020910030e150603190506010e06040c091205160305010b090f0606071b030c0815090a02010915032705190c0b070807051902040b01020106080303 74
    0x49440c1e5540d207815928204410030f004000c1d0201040030307940c0603126000b07094401811141464400c1402c0c0c4200c085551869000d4402d40c40105003c8980e5a45242c039074101401809481046641d1a190b814209562030700311034a45c850b00041190741040d5801c6500003401700c4040c0040203030340c00003c110521602555440b03ca1030f02e960030811004001c242540742c40c4a0350f440401c1e41d02d081450080c0f69814141e8000c441500018041030f5102c44144c0c4505801000b1724140046511510b02300800f100b40c949190007500c43c0800861340503066074005000c03403801031000846255801080c2d8001418068582d4071141003480180e80210726042941ca85000310300c0010075081049003d803640101950743c23180b84210001d0343e80c004034081d0445070300580880740d00440703409103007281545800c000342210800d90303001d10505c0c81c00b80c02411104e014910702403d203840703600d4050800d1318110075003a13201881c0345844114101405100039800090008000c41482c200b010b039240c4c403004145 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 365837338 1250 365836088 365836099
    0x706020d02010f2a05040f0308070b06030115170712050a0c060905011d010e0d0c08150c390106061b050709110d1407180f050d060204120c0603051b09 66
    0x81c05506100d1010794000b0881080c4d030441c0b1072303900d08140d19a50700c41101581c401400c8070000341c1c2400c1c14001c030b0303a0b0415010041007600d0315002020040d4038001c001800c15005035200040c1c2402030404044906009002802c8040071a10700400500310540c02842400101c88040042e41e0308525140e04000609204499034080003004a4064030030407141603001507091045400e1015548003c003e490201d412681d100d0303102100740f2400034084480c182c40320ba0412641003c019883c07006181004c1c0000201c440001c011a079805240f151a00c1aa2580d91a8000c02070b00340e00c1040401c20b00d080e07c4510b542c9070b110f611123035102c914600440721200d451b16842c1424818250403510b4000d55004100b154000109040340c0004040d210f0f24000b50229080d1300c4c08004d804280400ca070303260602074141034034010a1010300005d02d44199000c81c0e09000010b4140c041e02c1c1d140b85018422311800304e840b824810040c04440010b089a22014043c008450210003420101c95011104580 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 365838588 1250 365837338 365837411
    0x131a0d05100b160c171c02240712020901080601030b030c0612090f010e0303011e03080a03020a12021603050d06080f0a060c0509131d0706020d02010f 66
    0x300349040620354080b4032040ca001501c64404025880314810072440342100107429569000b8581541c1c041c94040050b40c4c0241a40560203d03221001042d800698019a403045d9101785485030300130038800c01c2e0346484004500300910194803101030303170030704042e000110708112900c80000c6c613242008000c0c4c0d05250342c40c0000d410698003004011003100000340450b94a0001d1040d9417085203046e0340392049845140c4500201d0311041c0901402c045903540110708503881c1000036100d1a80c0d061885100a96952010000ca0324a00c0106410207254401583d140100c4c00020030000c9070105211800744140b0900202030092200401c00303035054075009807a265100d00c050001c0000e40e0208219100305070441078090401b0881c907040714061201003051001540d8159440e1040d0001c0c15801500d1200305000d00c8200d0b032141041210303d8140341d2000c1e1590240a01d001d605030004405644441006100282d09000c0c11b21009285841070044403000c8800012a1407c0c507044008600b8881 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 365839838 1250 365838588 365838601
    0x5070206190f0f020d0207110307030302151003060c080906070806030c2101181203060b030601031a042f0c0319020a0618171201090213050402030c131a0d05 69
    0x400c5488490f0b40d074442107650791749603842c000096010390801c88103000b200c595104246004a08032080301d800d50090181000c0d0041c0c030706011308000341400620075411201001241162003200101d0b200c6403603041960030481d80561500100070500070411018404101140e100403070095064030003030b10102544120b9401c2003014103401c2c21004a01d40c0b0f803070b4040c039401c0c0e0550000001c681c0221101c078414038031075030100c064640344c0c05406619102000230540c11351207a400302204225000340c441950b480440004d0a442242035480141c40d00c1e1100074040c2011066944010f80307041c1c3c0254501842c065101c0d440740602021080114810000c08800c20300a025040c1c002d9031100f402c100c020310015041840c843d40050507145415941070a0b40c2950f4800d0880e08803200202c684207803030f8038109220000c1c1d800050710300080c031250a000106a2940d0000e035001d1100743d20b00940314031460701e44070181007550340501d2640300c500301c14403401303c501001c8071000c2c403070490085410342e240c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 365841088 1250 365839838 365839841
    0x507020307020d0b04020a06181e2606010803040302011b060b150c010c050a0c02090702010e010608101a0a120f0c0825181d07150305070206190f 64
    0x3150083c0d00311405000000401105032a0103219034030032605101c00c1d42e19600c1c100e0303000f1000740340d5045a5141e01002d010482034a9a640f0481c0480604100e400342c4400c0124800c802039000c0980d00e80c3d099070044480c1c1c4003401014090002c04000310300341031841e000203003c040448030691090802c1c0d200c550a1008a0b00061104c00c80038005280211000f4512100d582c41170007000455441d044003031400a1045040f1061082181da0b643c80d564101e40821440c0903015181c84290340d40e801e080c545854003801038400800040d0080d0120142d254426004c0e1500c90080c0001c3c1c0700c09070f40e440c02980d40c4140550594049076030b110010625440d01c600000d22603071000c6c1100803c4540040c0707828001821207540da034440d001d0f1031034190105c070071060540c99004002808541c4050605080d186900008030005100c00654001c1c0341ca500f1a8140416a04290890a00c500388100c2d415014022250802c0e03941c80182100d1500014042c44580c2120009050a0300c540603d0b590b550503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 365842338 1250 365841088 365841097
    0x721110d061407030f0515010f020f06131103030c1c09050a12021c050607030b010203040e01061106090d0509040b01050d0510050a0b0f1b12070807031101020a1205070203 75
    0x24420085121600001c510100c0102d6520b0f0000381440468003000e4058003c3d540100b9000c1c8200151020550040d1240c640102c0e1203400c52041c0074100010303a02c1082142e00880600b440c0c030070364200702c0c240b6090007000e010405001e5401044512030400000600440e00600a2882c004400c0700304011650040d141d4000e540c0001034036400b06e80c032280018400d41c260300c2110500e03401440c40d1313011030500b05401c0c0c0113049504003100040354940039800c90ba00c851030500c180c0e840c0c9520741d900220b00d90cc0a0b000080090080507402800343e00404c1403642000070480103103058916940014480c0c40f8818000b03010f203894004980f03080e40601e003a80c175000803c00c002d000902d88600700f2800300311030b40f240520070340d80340e000001e04101e254100d44503191860a4285071520b0142100e0b600054902d40500a03c20440445281120000600036242c81002c00701c0e81c0700d155040041c46001000c02c00076159104201d181c400d15008844124010381914000c00d0f80d0355540c90503401d41c001d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 365843588 1250 365842338 365842343
    0x312020a0c03061a010e0d02010509060405090a0c030b0109270204150f0207120510090c030c0303021605040513030c060609090c08150708010e0405010f020c0c030721110d 75
    0x20004070200402049400c41501100240040c1c0c2d503100e4103100441d400e07071181c0301c2190040301500d820300255100300010310007820040c020034541039076040030824001c821075054181036910510401165858011b074002e880013441c11002190801051003104560714101d02c06024010406003012803160b01030303500412131455201c0403503195240203050b20040002180060141c2500820300621099882d450207412000802c0c1403042401d82c83c001346202c06e8140c418400c801000800666090401d0000d544203601070182e8501712840c40c1c640d0259508228422401e003010428101c4d409480c1b400d80795010301c0c004000c0001424504001d200940004550b2403c0a4a0405000d881c0d8048001c891402d03040350501c2c0703041845101e00075004d0394071200040407880100400401103600c107400c240140000642c2c0603220784144201c0e840080394800b103030022101e840d03551401380000c41c01007110521400e40300b100c041c0149155001c80000034815004044002e01c5a26058400d0301c0d404d9 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 365844838 1250 365843588 365843603
    0x3020304061d0f070906060512090c03070312030e0d0c020418050d050a090801020c0309060a09080a0f060506180a0c1103040b071407150e0d02040f050613150312020a 73
    0x401110b550b0700d0b00200d0680f011144601070f40001c0c015420300c54401254060340d01e440c1003c02c480301a0f40084d030098048002c0e44151480c0a0b0995003e1140134004c500c40c60b00102c200c1c0d400c80c4081c041e51001d04501c42540c21a92103490700302d070040754003840d0540c105d0740020180030a191a50011081401c05040d0344248100d0b000142e402038028850418a52207590b90250307100c802d0703401d07032040d2002990300d81c0044c04000c440c0e04010020708042600e50402141c4c007620707408840d10741071103200203403075040350301080c070007840014402c140e0460026508007003031301240d02c81d41e214054050400c0100d40d540b9145810003d11034040c80b40c070f0352120700950390750315941ca02c4c591194008641c19510000c100d90f50703002e00380b00040c004c0100c610038104648800c90200d025600e030020301280030b0300f01102c14421801aa6248560348158803440b1002415082c40d44c02d102c1081000c086100150f460302c8940c0200e45141036038070b4110303503000402e119540200c10701281801c021000c02440324 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 365846088 1250 365844838 365844881
    0x103090b0a05071407021503180105070201020301060e0603062112070b0906011d0a0c050c19031b020f060c0a02092a040303050a0f0905130504060c050304020a060302030406 76
    0x1200981195009203d280d4800485104581e4402c2c4540b151880096004100d160003040c8207241e000034591020540811484400c4500412400c1d0380c011560303080142d60000040c426182c22482000d5071a900750303120b0f07003146051000304500c2c038036411070031074083e1000c0c03e00d45107507204110b141c8500d001d4070030964584401c0e2801022818050368880c006019150010440054845210307410a502540f205000e403110350414005080c0761400c48104001080b1f64402c0c40340030000b442d0b42480c0e0142c145411016400e0082c08000140e1446001c060f0381b04c204405aa00c003c040c4180c4941281c2480c4d071103a422010501c0c2c103045000007034012000c2810000c0c00300c0c20120461054aa80240c007100d28130b029500e440c58402e50000801144003070041e140c520740704080c0c02076026058245854032589501c00034004a1800003e42012510340c0c0820041204ca40250207240c0b1702c0b81015821810140d000070fa00d68070a0161408041d40032000a040c0010342c5c0100d0b030a05032880300004038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 365847338 1250 365846088 365846101
    0x3c03050a020f0301051009020c0a0611030901051f0b090409021801080c060906030a0e01241409040f03051e0f0c1911240a051201060f08150103090b 65
    0x100c25081100340d1240382d0494051040e402c3c10302815202e0604640c0d0300d08074030b06000c5008000d4000100e0a0414820785200301c1c0011010b2103490406c1003501c001b5916840c00da146103081da1001070000d003110400c842d08003220400713a0520410fa400d410204c58480d08010041001054503000103940311003c500d84540948030300100c507050341d2240050310001052a01803040d5482200020750b00004204001343c041c034210fa00200c440c3c1000300011075030940b0180c4060302080141c000300b0f5480a90030082082d482860443c01044c0c000f176030305110908d4292207900b0145081000601441000141607000c8000d41410360f4940e624001c140e42c40e00c9543c0d06416207504030328000c10580c491200034040c10000d080f00400c0240d0f11440c0800320000000500260001040070a50900781c081e03480c46004c0703041b2000d0303c0900510b548860b12010840e1001d250700c007040e170189040c0904502c01e810b4a6600191456100f0160140b600c40340400000490003000c1001011302000201c4041c0000e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 365848588 1250 365847338 365847343
    0xf0105070504031505010b030415090b090d18050d0b090f100603030f21020903010e011d06060d051005100504020a080f010f0e041101030b1c020a0f3c0305 68
    0x1902c4c000c0030105840b5410039292000c40e4428001c91800c20300500010300050035021628440300d10301c1c03c0204050900d075072040700b4100161440b0b502034103ca1003c01c2240e9003c7c420480c90b004040f804003100e0329041c0400e8001c140d10002516010020700041e5100c1002c219009020300d108003114a13030541c0082240040c1200d01040707001a106800602c0340c24411645004d2418031007407200b00250140a0500007940040d9002c0d415540f41d50340940000028418071918655818003507115002c1c0c510858105a0024030007031040c2c65180868001c204001407102c5080c6207203000103100d44a0403485aa02401c40d0f028662003800064003015040e441840c4074091a0103aa0342c404590720382c070b401e505900c3d081c02207140d2000000d0006020541d0001c084071005818180000c132041c200c000718031100b12403c40012142d4801c0c142c94110f0420301c180400616581840c074541d00e0401c2d0180000702c0c2c603030413420f440032a00954810248420003c3e44100f000b84a5040040c56891030002d4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 365849838 1250 365848588 365848597
    0x60a181512030801180506010e190b040303030e06070f050d02090f0a0603092132070506040309050402070209180c03060901150504020f0406140706020a050309100c020706110f01050705 81
    0x5d00b8200340a290345400066400b80700d00401c0e05071144424680c0c070500b8458503a00389107034241e1000d00c00740002000f2007076500a00141d07002e0381c2c002c01d6454065001610f018000b8200008000c04840380360040343c0d11200307607543d4030b12400f00545d458041c5000605201d052000540d4854400e40380040d4090b0180e0101c0b0315284a4003040400c0001d2000d481c00b030360040c1c1c59a1002c1484640b00c0d0040103008500110448101d48170f56008011120b00b81d440c0ba00301042c00c564591019062205054110607210b00812045405516001c100d0f070201c1c0c03110401410002d6a4000f914500038800001d000d580980000a02110207600e000b00006001e005000020100031182000c04106402c050088400c1791a42c4c5100e94506490100101d46c0d50324006801da118080a002510004103240001c1c10800b8841d603989071a401c0ca110440d041c06494036254a0040c60000780c610360b00e4001c80d0142c01c4501c54205440b0300c041c03072907007181011041208664503501e004100071140d0f80110181 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 365851088 1250 365849838 365849849
    0xf190f020f060105060a11030408100e15011805060d021003020d0b011b0b0903070602040612050606130306111309151d0604050a0f020d060509060a181512030801 71
    0x1103241c495038044841c1c48a000303019541d001030041048683e054041d80b020129540500220784c0f60554a02c1020f051031415140c12150300e0315503101008a07002082005961107545078a400795502d000e9586803020b500755099031280782c488002030520703561000d00d88025070b0050032204210f50001402030096000144d05590640b61010300081540700b042490100040c07498000e450160700d07180d26008401c000c011207d60722082022000003285400900020561030700c46601d1056465140b00c189e03000204400d0294105000741024400208941e900b01e07504403030300003180c541c084002210751180404910b82c01001c008002070760040703035000c0c0d00d400c0c1040032900440c540719281c038101c0d081c2e9001c00d02c85100840006c02c40d03a10b0190b10a68011180000000f0400d1f64000080c041e40c2005d03010408240c0da8a9041050341800450703d03512800441d20a040c1600381218040c2c166501800d075041c20366504070f421000c0000c00c14006c00f50110b40c0c89901070550501d0014501e100034040c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 365852338 1250 365851088 365851093
    0x3221506030c06030e10050a0b130204151d0f010306090e0f0c09090d030c1b0303050603010e030c070b030604061d0117010b010c0b070212040f080c0f010905060f190f02 74
    0x3e10144030344588141d40c0c1800000c0d010390110140510003030000034107903007c1560744140d69070f01540c5030103061113100702c00b40015868a240c82400e81808d00c0302c030008020700c28560b000d4141c0b101d03000e03414600550211041c09030032111000480007451950400c5144c00e180c10240b00c15144005a18081143c006007182c044002050500c505040107849204a030b60240f80700e8002d09009412940c3e071000c0c3c0d403030325025428240d83c0400442030011000ea0209545009001e01d6084c20f000d007441e005c2d002d0300103501d08604032440c15900c440e14803444c8050343c00032010444580d21600601c000f440d20b041c041c644060074030b0bc22114607400b03106840142d03808074483c50300d40006000c1c4048000050316020000800e50322024101c100082004086010b401d5407080c400740ea04016001070b10040703800d40d01c50307400c00e4041490214000b810341d12480e42c2c1d00c085001070303900c0100c00059a406644c4580c0b0342c1d01c3e003194040c2d01d0091b03592008840100354403509035242d100980001035480c5908 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 365853588 1250 365852338 365852363
    0x20c0310020403060f2318011104051801030201020d110106080703140d09080705060d0b0d1b06091404150f03051609022106060c0609100608030f0322150603 69
    0x1070403080310f8010007040700038818800e00c003004680c400d880d0395008141c02c90346031816801403815421039402745140100d0a00c040b60511580c1410071090880ea07010024170480c650554001030740e0782c85141610b0042090318401055008000c0d0006402450001f003103c00094403460120100c0d050705182e00d007a40303e10840b4130207a41c841c41d00745d0119101ba00c040c009017410141882201e038002d00c1c1c4044015241c00700c1c61f1250700c0b00d01000d0503050013078000045451201d040d68880102e035501c810100a0602010711038100300d802010744101007290001101e9010070380940348601e03250311007202080e00713002c000280200420400b401307407d08003417900031949400d0b02c8400c0740202040034500d0325807034400708240c43d25043e0b00c81e04064020411420104540c0081d803800c0400c039030301005034201c0050080c048440d40540b0740a04259805181860081081480705000c0100302c510441504024105d00a01c0440545941c0c3e401c0703400c5495100d10700302c10801a003440c0c842210b0403240b018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 365854838 1250 365853588 365853611
    0xc030702010c020d17040f0803100302010912080409240605280c02150d1d060703050105090f060a0b1216050f070b100b190905030705011e020c031002040306 69
    0xd82d00380341d1450b40d12888005c0c0344107941040301090081045500003504068400810701d1580510310805100d006c1c42070441c15840010301d6810b550b03000b83c09100c03e01c140400001c200034143c5082d204001000115060468109560351b01045034036800c0188000e4042032150780071000b0f0446000a01136003807070308180c2e0841d906015690504e00c0019001210904c01071510710080c075907040b014080d0500b00300703881c004802250040c0303010070710004c01c0c410011806141130200c180e001165041c20807032903140c0303408100841ca005128030b2078410440005015a40c0c2d06d80c0c0d0364042c04000d03d820361240040c3e1144110f05030144c4094194081d100c2c1e052522520510855102c01a100301c12402c00000c1c0d5114821500c3c05048d01200140088010401803940c1018001800d240004036440740e045038800b60292405420031806504142c00600c01a40c01400c4807080703580f8030301980c46101d4008800c03401c02590070940303036140c058100c20454010880d000750094a00030042040214a01c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 365856088 1250 365854838 365854843
    0x1030b0f010f090b030708030a0f031a030c0d0515041103060a0908180409020904050c13110f091215180609190f061103010f1205250e0c030702010c02 66
    0x901c00d0321074900d61102c0510040745240c03c09601c540c07018040f90641500c5608540c1144c11100e2040005000d401310190159032500a10300c6c5500d6004000c0010720342400400d868100100780d45015103500c600007820802c041100000b48154160b50603403900b4030b03141003141c06581510080c4a0f205032404111805028404e9594003507200358824036066200d20071010f03034605030300d500e940300343d881d031562015848001a2a02c1240300e40e01504182491108001c0c0c1c40c504000320400c2d0f03500c2c0c4100094107070325035011200061100c440c043d4a449500002491204241c18900840c5c000c01502241c101669100c2074012000d1500d05020240f20b650065510881100e848045510082c00461030b541c5c800f024690807070007040c80a03001c0900b0f4840505442e50700c09401c00302c0f01c001004002c04604041004058a0f945100d6814100551512955680b0019190414040e010b041440306000c1e0398581005100446c0c292481d450200d00440454004540b40c0e0099400c1c010080e0405201 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 365857338 1250 365856088 365856091
    0x130311120d020d26010b0c010c090b040603050a0207050a15052406070203150106020307020a050103020909190b0d230c032e1a0a0e07050d051b070b01030b0f 69
    0x2a5006143e450300e0240e088a080442802c01da5144031007048040b450307800382d804180a020060100c03561280111081070840f0b003085071000411107910340910107000320740101d501700c407001d24000c151a01c070503921500030b02c12404000d01c217104401550080050905040502007030100003003160b503450b820183d003814400003c14030100807031943e0780444c0c688040940012030020702115010f00781d0500f0030b655080700b81c03c20400350740302181000842c940743c104403002d45420710b000d505182d030050100e08610b0001d06180400d640204080b40403047d95071102000c00300060800000540070700300b0a0210380342000c02103660b40c492401e01002900004d080d50328100241c01400d60103007090144140e03200d0703404035214085e41b074840c4244da940c0c4d5011f01100a20180107001d1100554020030403066001e600041d441807030601000312254000c0c0c2600d6040c103643c800880e03169510340080145003206200310015840210b074400600c06007542007270580c0d1240c411103c190711810200041e0010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 365858588 1250 365857338 365857363
    0x50402220b03100509270a0b01080a1a042f0111010204060804080d0e011a041407080106260f180312180c0909032a0a060c0513031112 59
    0x15100c4208845d061038000c607030340501c1d034241700510900e64941c80d540c80042e00c0c014880030761046902c00f060084000340315005010b0b4100401d0f00101d00d0f99442490000103841c5012840c1d084005814008018400c0550520114150b2007514100d0b128905100e040b41c030b05130008041c5c050140c54117105100b01c600f076502540310300440e9500d5a03200e6015038000f40031681460746804c14140c007004c0074001c040116184800c442070000f100000d00c011244410341081085804d00240b1400507000030426064030b41c6840c0c11a0b0781846a602c0012076401456a484010405402c00a8130280c0c070700f035503008038040b1410254200201c1d10069482c001c1020491100d42c0303030b0011441d80070410407101040ca03000002d4401c030150380c0d0001100301d101101c0d60240354100054071890304071080a442507030b0303d140381d102c0d07800c400300c0c01b10075075a0001644c000d082036a240140c020041c001c0099a052100202c50007010302d0b240e01c0c103004850b00d464141c500610480c044e0740c45413400414002d601c1d18 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 365859838 1250 365858588 365858611
    0x51f050a1202061e07080703030f1802010f03020408030301120611030411041d010e1f060e0f0a0e120a02391512180609070308030907050402220b03 65
    0x1401a020440f25a02c00400388100b0542019080d55000c01c8002504034140115540760300c4403a10300740601038440d80741c0040c05203403424034591984800070f10507100494082c600640c49009050080e03000384079941110019210200002a4400d00d400403220801e01c12001880091880c0e40d5140e03081c00f05642c01050f200303800810b0085418594440c0d1031000c8610180105002c240301034070f003100c81c0d45090f603a00c3d410080300500c0c01042400b20f080c40400a00c800c0015038a0070140f01c4211001801e152103201c04980820b9400f031583d0421052a900b10055906250174005d109105ea80001820000350140f0080384002001d1012410178107901030500108078400020202d2082e400094000e40c40501c645000c1031001518000c5c209001c010903e484190624100041700d0f000c515030b007840b040d840f00d01004031548002ca4008100d0b41d208121a03142e445808683d410004180c00964200740301140411020104214548459141002c01c000035074450200044600c0115807690713240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 365861088 1250 365859838 365859869
    0xd051501050f0f09010201090606060509010801050f010c02041109090702300304060e01060e10090608060601210e03030f0f0a0603051213030c0305030903120304050d080c07020301051f050a 83
    0x4003c03107030081000c0c070414030000650460507a1000110341d15904800f00085002c100320555503004034100f400b604080340d90026000803980024041c40c000c5030021b009680b9005003600e801050401c3d94102d40b00240450101d2030460f500968031083c0d407020301e04d964105940507001401080c41007240301403200c0914550342c2c550315410060a0a400c07182103035076030b8607000035005d0307401c00c0214014032141c604d003401c00b464502e004003620150740010038280c01c03010034422144c0e0020107500f120301418031050b860b40d4050940030010720940c05500d0b440d020010810610041d4151081d201d082d06e2021101113848049210086980303d0100900d0b56100a040b030003007070302580280c868035000c0d203001100c4c02e031683c0e9003141101d650750044885a2011480202918090046d04955290204424110b1500fa102c5a81e101c8100035184140011100800c2803e20301000310384403950042c1c001d00150500c41342240301d03601c048181250b200018000455140f6040c404201110700482d1017000c1c2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 365862338 1250 365861088 365861107
    0x807050703140c1f0e07060e03071e080601090b040c0c0507090e030f0705030c0c0d0b0109020d0612110a17030421020d0807020102210a0e060904020d051501050f 71
    0x865001803d0840b642c4541000180e03034110308a1100b9568004c1800450701c43e030030140040c0740501c10b402000c14480e0f81801d000140e1030000c5c2480031a1482001c1040d00d100f000340340c21104504e60840095402600004980d01d02590001000c001040d0b40802c00c4d000d100358100c41180040400420540210104012020b4203402c01d1100e2602081628030341281d44580c400c41da801a5004c031087d40000c2064840d0003c14491032801e10b00c00c0e500200c4012143d55560f440c003105008940711660b01003808910070403a580008040d01d0b1410b6070004041060810f9a640000901401d1140180d09004100395550f40060107032a000000114202420940388038100c4103071680e46480480c401203410050ba03141440e41c1c43c82c50080014654450342ea000090a1420581915414a0840402181080e0b00f1303000c071090800307180f601c44a11101540014514854913080591081c00454a007402030070301e6200794052041c1449800307210900030010f441b80d008001c0e20400418050000400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 365863588 1250 365862338 365862377
    0x1002030a11010204050d050c090109050108120a0c0b01090914121b0f0d0c060c0c020109050f040906020d0f0f0b030604140c130c02061e010b1b07060806010807050703 73
    0x6070700c103030100090304090329003000c2040030222a0043d0360766030003800c020141d81400c4461a014146401080c480c6604281002d075950b89104034052900b00002500c510702da2150007400c64550740500104102d503500c803c44006403681e058183c0ba18410841e40141403030002a0141451101c01029402c01754104401c119012402c01000c40385d000b0008408203841c0d0034000051854295111300a07140c0340d030f040200440d64020711020510461030315250160381c110a1a00c01c5a00846401441c1004000854041c04c81400c0007000341d400070440150100e01c0350444410326080c414200818402403050105542409040030707050780142001c47d000c40c0b48031607400720340340342e40b01101c150301d0401d800708500c2c0c0c00241112007025a203d041ca6542581030100035000081d540c14900b6403400030084030f481c030301c06100301142104000b41c40035030300070f051488280e10110038041c0c5001c3c42c1d84900203459424221038983c002851000000c620500aa09441c0e0103a0141e950194100d1714191966 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 365864838 1250 365863588 365863607
    0x10b04060315021804060b120106030c0903060e03130b0a12180b0402011106070507062a05031003050f060901060e09070b0702042a02070504060315050c1b0606010e1002030a 76
    0x14415100c544c1080e216071114026903008048169030a95140e00044e85034183c481c1c10b0700140704243c2841410504551301884800c03c0d41e42103031000a00d00003400e0030b18a1351050140c2d0000072803510500195008101025101640041e1203160504480c0003800c000c0b20b8542d4030703044201c0c1e152620900850940329a860b402131060411252500006120620340541241c87d01d00040c00014020100015405401c842c600c0d01d15032440080c68401d402a0849025030307a950404c40040001007048203c09400c100660b001400c2da03600c141c01d040c07126243d420490b02d03a0169801c2500014007954000400c40c03140c2c4e1030f4030180c0f050318181103d1050075400110146d90098032003034140c800701c6500f01c4a00e100003411161071003410381c40d2406401c00c0c5055214510641c034110302040403a640010380b005240404600281e9581c1d910301400b00382c0203181403032200c40207013002d00c80074050010342280104c500340c84070084400c0c4001008041000514000d006070400e010111640707010b4100e10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 365866088 1250 365864838 365864857
    0x2100b01080a0c03020f2d03061e0a180204081c0c080a1205090309010305090303060328050f0303010614090f09070905060d0f0e070f0b1c1d010b0406031502 69
    0x25180c5140004a5030b01d940000c1e40d510140d808980c03a40714647c550840b08581a040c19489508600d00b580000d0090b03248042090811f11505410903803541e100348051015040244002072a075a802120200a4205004201d40d5204040541004180c00e000c66206079219965841c0c1d4030700c0707650316104560003445000c02030101d615031440d80285039001d81d520410b58903006507254441103000606075140544a50020307042041407164071f803804030f88000c007080e00601d1203600c27001d6000d02c4070101c0265403001c0c05600486030203500401d0b0110086048800d0760783c540034000e0701056421614401e00c54002c3d80900c4410b03568015017000807400b90711254130306180800b2035071603001c10f00c1648641d03031200b042c0b42d60700005030903034005104c1d902d9914514001450b81d1800c09011452015050290490201002c201005900721000c1a110b84106654041c0310401c6a0650082c0159035074954000c00d500b00790b054001c0c1e0420703116580440e904041d0102c0091510207042c8001e40c0720380b0b1103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 365867338 1250 365866088 365866091
    0xb030a170a18092304031209050a050a080a17010e0a1a0a030c15031407030915020c0601031703071e09081203060f030304030b040803070909150602100b01080a0c03 72
    0x20140c48000282011004042440c00030803c0c00e60805154400b00d04c800b2042c041c00b0000081c040400c1c0d001d007038080c80360b0548100240212503401e2043c500801d01c00006c0c131070700c5003141e40020000701f1030280203510741036102c20618611030b4280744801402401510305a245003000035000e0882a00b1400f500f400c1c1015140c084107890010039400c1c1c00d83d070401d0700c3c600800c0e002045500310a030120b10150003946002c00c03003104046040102c04102030855030030103880b90100024441c107503542d100b4032000c0480865440e100e59400680b40e20b024401561103208021f05c12508010340c20490f441980e032595005a19614500311006000c0c0205030002000301601740030410280802c4101c014185914825480381b40c00c0d8204000e00c0c801d292114020340091000704000b030030710400c3c1d40d0099846040c0c15200e13582c8080456000d400f80c0c1c4944034440c10820200524005040c00a040c1c0d1907990a4500e50740c040e9007404103a42403d40d1403800500468001030307000c0e40c86d0340188160092882d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 365868588 1250 365867338 365867357
    0xc020103230403030c020f0a0c050904080f070606060e27090322140301360206040b0304051c021e03040e09071809030504210204020f0702040b030a170a 67
    0x84412600c800c82c1c0440209654465401d945901000040082c2240400401c00316003141c3e24480c10075082d00c26a0300999080020604206070582901c13818150f506400d034444840c2d042c10341c05050180308440115051a01840c0035013000f4405480240440a01d207034002c0012011115490f4020541281d50006114402a0600c809501c98008510405401619007030101203040c0e100c45030502c03846685412072900b14070300b4105c007079100140d03602c00f00d94501e10f140005800c007011175100294032600c0000c0201c2c0503000d25014500585c010011070b0708056066803211039401c0d01c0340840700545e105100702c4020700840c59001d6000340b110000c4d2400c003980c5036a1070000305800c2c0d07032000d21034000d040144015840c4000c0c1e4941030320700712018082002e0584000e8520b01c594098101e16400341c15031402203c0802401c0380840d03074007800440d03a500c1003206141c7c2982282808034411801c26407448500c0c13070001240b0203407a07040340e0135180c00070300826218095448800c448061003032550 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 365869838 1250 365868588 365868641
    0x3080c1002030901090201181203050d0b060a0f170609060f040b06030f070f0309080405041d0f010c181d13061b080c1306050c07050a090902030f0703030c020103 71
    0x10314020003e00b000450101035910000d8103000071010005403e0138500c0c0304021103100c5461000c00c0c07940505100350384100e00001607001e484c202d1071140d00904000b841b4148c0e1540481076107240c3c0303442d544011884103c030714076205450303056131020350140d5107001041c0c4519001c212014a51002480000e010456002050b1260001c654602c00102c03a5801c0065440e04120440d100403002c0c601040048079564030f02416000d54011140107d03540c00310021136000154200c46c41c2030702c460031110003048406409001c1d14060b001000040c0200c0d481c2d194040004000b04182c91040400703507140d200362141d54000580c01003820029000d4400020003080c2e071340c81078402050b01001c1c039505034101400040c1c11080050440c10b01c484041090b549001c14014001042d6042442d08656400d040c0703100c0e83c0b600d11503170000f9512112411000030022650707441000124400d5041e070b030b5034000c420745440c2c81d40e0351448050301180300000140019846a4084400707170f154406115412403041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 365871088 1250 365869838 365869841
    0x1806090c190f1205070b07150b010509040f0f0c0311030f27070519030b060111070f080303100b030106120b040615050c061006020d120f02190e0d0c03080c10 69
    0x992010300e600a10000400071302c501030040c40e01800c1c192240c075240481554900103000111000c040c0714603540d00d501c042e60382c495022190681d000a1052101c04408120100180412100c6440785490641e20b403805038003d02a1480c100c1050b15158156512903e4071400424020014103113044039a12001008034a032024600342c0360381400a0800a040c501403007142010800e0390124061484070810010b0101c0b045168001c50a203808408040082030b030f41d1904034281c1000ca00014041c102141e1454008080d500c01c1002c515201011540c58043c0b8031980300a018400014200300f0b40c000d6440c495030417207840e020001d00000303443d0365910b9020701000c020307111590002e8000200401341e600100415604140f03d1929441c059141c45d8020f03643c0c0c440e942c1001c4c1030040c41c4a65201941e020b60044141c680400340565850300c414110820000110300d151002ca040310b42d81103110700b401c6000340c6056902100812000d401c42d26024400d806c0f20b01e051000b131041698218009501e07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 365872338 1250 365871088 365871119
    0x1302040e0601060806060403081b0f0f0d1815050f0d02030109050a0509012a020312040f03180e0114040b0a060801050301110c12301806090c19 63
    0x403801829555041031801884a81c01134443ca1040c03030184000e001190401c012509440c07204038021810514103812103080c2082070154542500446210503203110740400d504041a0389542d51b440e0b280561500203442542c07070700900d001302078003040c21074810b40140d00900010f0000000d00341411500c0300010141e0b4401d8110700c40360703038607101070184026890180703513000300c08030009210756070400301c0742c0c03507500741c150824202c0070410403c5003900c0d8002d000f160352860b2048842d0400386403a003401c1040542c910421070006101e155102d684100c07040746402900c044a42c000c440364601030f60212240107210401d0380c0035556071850111513407501210001424180c5603450990724040405003100e018040c1c2029003c805c0001c000d1b0844003040d0000e0f000c01c2d10380c4460f100e41181c40301c05195100e4503c200a14140d0b204000c0c04902c094040742c1c440d4440203c10042a9001c1c4000ba485500a40e03810f000d9611032154058689040c0243e8422048906020300c8400e40d01c52100328104d0a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 365873588 1250 365872338 365872361
    0xf060d051c0519051206010302030703060e15011106090616053705071a0a0612030824100f0210021b0601050d0213110912010c091418130204 62
    0x8203890050600c0460800d032084a04005042c40300d045d0080200890041c12181015400000610240d00a40c81840074101d03078018207000c1c1c076000900c0000071941c4902d00740072640f046041c64030580c0024885202e101940d01a0000d07850700042042180396042c174480c103008003401081c0c406c5460028801c6907042e1301100c1515105180e0b00c01c20a614a1248402000020490300c40401c46c0c00e14241164064060101c1003036490840c150010080d60308403081000059071088240350b8010002c60003908104140229103c03162203100303201141d80c545070b801003000d003000b070b0314140070340e101180d00c0c03900380196001e810006a901080741c0c06100c0e0a84106047c1c00350740c03007080042000501424095801046415003500000c1d5406280050075100e15195011800400059826141d00040c054950210120419495406001c0d031448881c0001c41144000404011858452105103405003001c1030755440c0b041d01c5210364500404004150400141c80001070321503118403d1042c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 365874838 1250 365873588 365873597
    0x1207060f1a12010203010803040b031008010c051201050d030c0605040c030c15020f0d020613150603140105060406050112020904090f0602031602010b4c170f060d051c 73
    0x6101e0000c01c158510740c6201060b050b07205000500802c00000100c8050b11241c213001d540701d40e00c4003407100389003c20b60411401e65090030f0020750740640020103002d902d12030030001c40d1180e80f25010b0112030031007003401800041000c2c03170750b0011801c0755108640160096140050281d00d94607440e0b251051944800f031404200c918a401c0203038140326480201c031030980a40642c00c03c40c1c80082d52924041c1c003191102302680c0c0c0103010811400c0c41c11805e03646240c0d091101b1580d908101c134000d00c400c42681c0055003008002001440e080c407811040d510305840e050a050100c04002000f90000401c00c2d0300960b990500c41c02042060300c0103d03010380304807400b40e0f50b8904007460149005040011506680c100640c241a0340d484002461100075042d07090208007802c099620440400b0002405940d00641c2c441708005241000803040f096007900c804001c9010280f0180c414030f03084404210101304140814007501d40041294580340c0070344103c68803c01060310a0082a00c40d014010218 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 365876088 1250 365874838 365874881
    0x203040911030114010f02100e07030c06021c080c0405090f0619061b17030411031b0609060c07030503030907080d0801060f030c12060303050706060b0c1207060f 71
    0x24016019403080078414004260440d403410380228081d042a4804906001600240850051081000003180342c4215410b00080c12030448003911801980000d4400c400d044401050813400002c40c40307000c030700400302c40002d0090a281202d04160145c00c088118000700f00005165491588060089441d040c800174941014400c00c4800b16040c54031090798140504204000d98110001c2031104011002d030340a05021450010005150740301540702c4c0c1000401440180a03602c1c2c05030102290070341c1114216540c410880e1000c103d48650706501000c1044041950700b044c0b00544544100002161142900e03540da9604640007110180341980c4114010000040200500743d8100841d0500703035052750600c0001000e145900050905264940170002c00c1903110320401c4544492041003006000d40b649402801030380140c40c25690780d410000003195184a2808803121042c10500a0440e01313050319403041a07800000301625031a940700b100c401c140d001c0c1c0c082c0415001502d9000c040c00c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 365877338 1250 365876088 365876099
    0x50919151e05090606010f030c051608070c06090f0603020708120106050c0d080c030705180907031a1203040303141e09090a0b0a060e06090411040501091d0c210106020304 75
    0x1102c0e8001c0031109694400402d01c0101d0340c003d0450903c1c00c071180360115410440640c169158030410f41d4001e0391100c01d0a4403403c3c0026031000d0701d10640b285540707000035581e450080b61400140e000380c0704c00400945040010501076401041c0e113500c106482410712841c1d80040e002d00d90300341d000c14040303240001c80c1651020b00b8401c02c00d500005040c041c0c140c5c2803094254401e4040100940c0a0040c009921110000c6400210449000040c441039170b9240600000300034205181c0c50130070100310040c00094514200c416034901c40e880c44021402d052031a1003c0761800c084e20050840c46108004010b08800c0280c1c48114002c0000c0140743d0b5141d400081c0008844001d03c854003145c500b0001400d240e440030512000c860581c0380600c41c0064980008001d8890076201c140c0c072a20300214007142200d00006001180c1090b20f034424070030340d03c518640c244511054034200380d031048800100c0c204030b12406011180c1416114400c90380c0356021828818000303070070105c096400840c04028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 365878588 1250 365877338 365877341
    0xc030316080c0a03050402030f1c030e0106051c14010f020910051204202e050a17181e3706021309140a050919151e 51
    0x410346101e2900034003601c0d003038012402500941a1000c10543c903074011905542c0c0c03c20411006400301004c0d94118442488455440f40e41c0a0074240403c6c02e1509621030354034184500001c5503006001c8000c03007160780040440c000b05442003114a84440035140f041c613042441105d0414030300d11401652940c1e20010015881080d203075000c1000340c204110864000d621151540043e44072040131010414403481120b89614900015007080303442d0090354a142d003c005c00c4403e04020541511500240e401c100c507188a21000d580100c0c0490900d0306010900e000729562001194034580d07908884140b140d03041c20640310359801c0c410304601e4001d030001c4040c00034208800807602c800c0e43c5c8010884d4080020024009000035280000304580f0910002d1340444100f08481042c400354641c03903c009000803d1007241b050315030912100000c81c03014251054500a101000c001d01d09a0038085903c0b41140b140901102c4040d80a501c00d80001d905020350386140100c1425038101b04c045158600 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 365879838 1250 365878588 365878621
    0x21902060a1413060902060904150e0a05270a020604061d060a0c0201030e03130e09010b010c02010c1e0c290406080403080a021e0307120c02071401020a080c0303 71
    0x1901c01010b50140518450072070546211903030301c008041421000c2d0300001c3ca45009958606801a08200328982e140110035042810f07144850b0320719055440c3c00c0d9001c021600222a41e486007903a42010556035103003c900c400b00b03100034908488145000b580841e107641c005910032404580085820f4a45141d0825158403d002c1900c1c901d0070003221080041096501c20f001034141945c0d00480101260180219101d11006a14610465980b00440107144600303c5140c54554a020b01c0d4000d9988201d901c994010b40507502c111a8101c0c540b02c01150702142c04100500800440041c800200000c034100300030510445648041d0109041e45031688420000d00150b4500c10001803000c150000951500640c05152030141a0340d0051410b000b072040a840c5000b14007c0d0008c8581d6009200045114801035540c4c0400406a4601072061306d603100502d20260b004007909000c2d45103d0f00010200030014411103186641c5030701d51350130503442016200281e80001042010030140c41243c40b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 365881088 1250 365879838 365879861
    0x41103010902060f0d02090405130c06030b0603181903030204050102070806010b040e0615040f0501030b0f181e0405061b0c071e031a010905060a14040504030201021902060a 76
    0x1c0c04800721540c001892881200c6003e2040c03c4c020600b0f00c00501c8641c11b41d8507000c8050010046424000b02c00203042100100c22130304c00c1c000c0800468058482d0040102c04440500041d040d51a909455041507850f01c03450309041c464482860021580140c000d01054029200160740d14180f800090804259030402500c5a201a004003c6103403907000700c0c0c0880303040c00e1036071034151034500001e407007d82c00c2c40580c80c40440206012800d500d0784d00c2c041e400c41d07409880801c104e40c4e4450500c001c98144141c1703a944103030508041007040e003100709200d81c4058040081d50002c2c2044c120300c500b1031000da5003a182c0e64030000c100842c18100a07811510420000c01e098140000c4815665483c050360155440c03030b200d014000d24428032000304190246901448140c42080505030042c0308560900c15928150708000129405d824402c02100c29118002244030807100f034841840003a00c03029104804540d820400310700c01d014200028400310500c0da000d003050341010b8150009a40600050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 365882338 1250 365881088 365881091
    0xc080708030708030406150303120c08040f020909070902070c090f110414010905040606030c0e0a080c06071b1205011103150d060e1b040e0a020120010603170304110301 74
    0x3840036500000588250780da010709207555130360382c1c1e19012000d0100b00d1120b1003585d02440d00401056040b4024809403101954200302e07030414081c2c100c802020540c2c1c0644010034036a550300150500e00116a80071451004885440d951002c10408030ba1100307000b0780b0741c41d407869000c0c010200a406010420b564500b01405040c0580d099151203200da88541d050145503460210740baa4084d0304008000c0800500400009640e000701a01400290f01d0050002c1e0b010700e5000c2c43d030300e0f207c219501600c100000600c9102c03040c0040c002194407a480075a214041c000c0c45c0100711920140440203410b1145c2e0a0300c000791649026400c4d984116002c00b008041442004450464484a103804107000c4804103102d220704e040c6040281011168881c41c0e010302d003200f40c0e40103540700d01e403c1100070903101004031212601600340c88025604000b40054500490100c2403504d0460700ca0074003089100010f207299480e541c0400300d40c0d842c0405840d801020042005000d00070303280240480082d0700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 365883588 1250 365882338 365882353
    0x1030e0703210e030316021009180e0a0501020703091e0e0403300c090e04080406051c0608011d0d0c15140c090301060b0c0304090c1202160c08 63
    0x31890780c03000c60703624051039224201c0c41084000d880f0300302c0c4001140c0040c06480d40c4280062501e0640000d110b016400780c2807014100642c02d201e118203a045400c92151000014000600390019000700d102c0f406c0c00d03200700303a803040c040384080c801441e40500c40d0b252018410301e00242280c8003080e401803050300205598081090044000e0202c1e801940b601d490700b10701401d441c00c45031440c140412601010001000e010307080b00f50758001d001c2c459043d01c81c20280c40c0e0354410000c000408541c000d102401c248010030001d030180004e0a074400105040080400c01d04420b0710071511207038045586a9158001c1d00c2140f00d07200b0080000b04428005007800c480d0450300a042208602002800440030b801e20740d0101c1d4079680710010308a1241d4140c070103410700508001480d001010500e20070351800d40c000440c5e422010880da0710030a5240a9410030b45060038000040420610031000d00066424408905202e440286900d1a8030848605020b1440c00c080c00710048541291042c0c0e4030040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 365884838 1250 365883588 365883593
    0x60705040b1e1210141020070317040603060f0806040b07201e01090b0c0d060f082103100306020d020405060307021e1906090507150e01030e0703 64
    0x2000c482415810a410100c001d46a2040d05034911030f103200f100c200e0042500f444054000c0e18404400c5880254840340408035100420030501c1501807040d011480c0401891880c0c815440b00030244403050041d80c3d01e495803a103594400b1226191811442d2500140c14081507400d449039001504a803807107546440c2c01d02c81901d581e0480584050041c4072428002922603124003d0151586503d002400c0c000c100d0356103065950001d00364034907054104000c600c080c40d00c148900c0440f5504080741c001e0a8540146001c050303482949521042504c0300790100e0403e00c0000c070000242418402030041d440340e000d8007562098040b807602c21481c01041481020802c0320740140c10380340c0189c401030340c0c1d09064100741c009224079400705400500c00310030000601d4001c24540790855507055003010500f5104400d07516030700075072900030340c29240042d034401040b0079601640c1514403034402c458a00f61180703060110001c8a090000000d104440c0d1404075507170600400c08144a0080101075903800c43c2d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 365886088 1250 365884838 365884859
    0x30702061f0b09041b210506061b0c06041719050607030b031c051312050a20091915050a050d02011202070f0606050f0907030203090a140a030206070504 67
    0xc1c8500c028030000429190501d65455000300005c184210141a064003c1c22000d0b000c2c10baa00180341c0c2c2064421000c01c040c10050180d6072003080c009042074035100500c0a1058800c08181100c0c04900c981c1500b8819600d640c0c0051010307000c4c130200b1010b034980d6840d003a45020308a200c000c140301c0d010303196840054800680c86801100501780861080e00e25404246050002c1c2d80504c1c2625040c2da02034400d50f08003000702001810490131103820b540325100c03031028041140000300640d1214103040041580f603001d0070b450180e0201c248018400c420001040403405460414000b4000702d20100050701c64070031a0340c416080c404441a203480d000010b01d07060032500c5400e01403103900c104002107a01c149121022a00342c2441152a00c0041c102103105080001045403030600d0103e010601e490038112151008034000c140b401141e540d40400c030080d401c0513000b20810300c102c2203208002041300c01401c0000c0f480341d0007400807405ca802e00070b1600402a20203070074400e0410041c407148488 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 365887338 1250 365886088 365886151
    0x10e0703060b1201091101020f0a0510050403032415090303091712040f0f0e01050f040b13091b09050f070302031e130203010b01030614150403140303070206 69
    0x4500007a00c000b81c1d40071400c0c0f00c3c0340c1c01c0ca080c1c2d55480e06140700100f107000340c0d0001400600b07030b084a078a40c280140e61991030340d032004050841d9110b030212108032100e9070400359002c0d03c6440d010a580c0c48a003031108401e500c1050980d580301c000b420900c00d40000003884804040c042c9022103805155850103810104280550b00c0110340c800c00c0c0e1030304003a04120443d0103c0c0d582032080d98959840c070884410344414050a9070725040540005840943c60646606840e0010006800011705008010090004440c4a900101c00801a10706170300c8905c10411094081c11210300c0039528441482807c20a50704405d10305031600c003c1c01b030b04814610005600c00114100161380340c5030102c195924000d116100c0701409207a104120348136000381c0c1e00d208801d100342d00a1000301000da006505070340e05030042c98484084030250466528280108902030b41010308424509030b200e80b01d4040300c43d0414104002d40e4000814050050350400c080395101c86120b2017900007132950b03020020041c21 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 365888588 1250 365887338 365887343
    0x2150c040e0408091f1e1b0213020c010c03060816030201180503120d0e012f09061303021804080307050c011506031509020c0a0308070c2004050702010e0703 69
    0x1400e000090400c038035602101c00412001700300500a043e0841c00000e92040006400c0000f42c0020001e403e4040c110000d03c26110240c41d088000b200c802010761034401c0035041030382c0c805020902404d140d030151000308000180714001244590500001409440403940301090540c0910a0742c83c07148041c0c10a4020b4030340c2441c00d071000207003043c2e0910240c82e103500180d47c903004100300030030461900c40041401d122210b400380803c44030851010700300c070f42e00d02000c51000060a041041144511146034000b50682e01c011300b0321401c0004240150031512a40c40c442d180b488081c0194603001d144907100e895600c100b030300307030789056a0f0f4070340d107800080c119006200300850032041d06c540c01e41012032250703400e19001040913070310600100580071403080340c8012548002e0100c0c2c40d64040c001c4030f00e01081007004000d61002682c084840c00c1e03005001c1010010700d140100300154018814110314600948910300b003105450802080301c0c4e025002100356890288080b104000100d000360850380c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 365889838 1250 365888588 365888609
    0x7051203060d06060b030406050a020a020714041d0304170a05030909061804050c09010623070c0512010204180b1c0213090503070b16051c0f06030302030a02150c04 72
    0x101c500c80400c00c01003080000602d4079040c00804120803107244040c521641c0242c4040c0025214400e0880c02c9201e000c0c00440140c00c080c000f0b0103040510314003d0351910014100042e8120714400061040100a681544903040000c0401c28468103c415601c1c4000b40c00240c00c10003029a6180d03600c0c8507142c8658011813544000511580e81d00580441400034102c2d0840a46050302d03005465181c0011020b00c50340c815400440c0079440b469100a60440c4183e2417110969604003042079500102c10031a00440032120106241d10b60300a40f5001c0360103403002607203035814001c44000080c80c18900320a69841c05400c1c0c1c80c1a6035800130040c00030303650512030314080080d00200318840b410b55050184d050174170780c40d0800c01030000014008940994550511a103440900441810621145000040051100c0621018035031a4056040500c00c00080e40d039164580401c02d4a05680c0180c0160308049941042c46405024503044500144108501441d0480007552540120302623026801e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 365891088 1250 365889838 365889841
    0x10050310060e0a052701230103020906090a031202280201033b011103041a0702150103080a020606040504032304030804090501150c03080a090218012907051203 70
    0x1a00c3d40c0000a01801028044541d2000c480f44940c451000030000346040d0101c45c000015904410000c01d01e0020340d814044480304d000000450194200c414483e03407010040141016655400b003801d8011440740c40d181400105007100a81409003191000035014448900d84440c0c500b0540c200c80c040d9424200003480001c80b1100900c80308020000303626000080c80546a410700842c401411140584028404100003d90510160000782c5004040c042035000928500410400c0c050b4130100901c1202c60009480c20104c3c03a07140e00b0380c010741c8c10007070010b0404003080e0b0601c0b1032030384100e05031400d000302e0400c8d9400a0408011035170304148180c014400c0016113040b80202c60003150040c0703440e0b803036603154071245005100c2840b44001031040190720603220b0303000e043d05c600441e41549510182da40c800943ca0080c10b9100300480e84030301403e070500b01704100c503400c680c007034a201d00450240060f505041100104030004000321480c1c180100c60001b200048e110705410084d55166449 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 365892338 1250 365891088 365891117
    0xd03050103052e0f06050415050303040603180c0e040c140f040f14011508091203150607080a02011401084606020c01060b04080d0e010e0316051005031006 68
    0x520f1400c0c2c0003640c000703003011001403019109030020802e8401c00c541c100300845e611070021900100a00c1240c0e01600288420404680658000000c280c800072130f00f040828103549015a5010740e8000055000c806001c3c0b00501c8405000c0b00f01030100300f08050001d800d04030000b0385103502800510710030f64540c00406407400807030300502031080410109500c0c40d40c542210b03071400c6598400c40c90006000a0025030080f0000544645030714107a400c861940e2115106000c00030001080250409003c0050000141d0300e04000c0030f0b409501c2c2c0c0009110900740f0041c3c1000d1106074800c9074076074401c942d59500c2d030102055801d07408100e80701a11080800d0700031303900d4020b10031012606800f6400c40c80710a2180e160000d20b14410360388001c01c8059110f06000207a0700950091599030f600210642d1540d0b1300a0804400040c01410f045002082290019103070072001910080d0011a00da410041303420700d0b800301000e402240c00d0903400c6107080c2c444c01501036500d01c10780e800c103c02294020031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 365893588 1250 365892338 365892403
    0xd050307020d03050c07060905100f09090f020403080d09050f030f0904150308040b0711220216150e060105090c032a120603101a0609040e030712020d0305010305 71
    0x45c55915101b5250345035503c600c0a003560429100c1d00340511040c0c0010400740784140c03034608a2203c2070302c2c0c80352004d040001c504010100900417407500b59007040003001068050014091811080f00081074548091a110707041040610040c480c0b94400e0001c224501d0001e000c1e40d194101c01e0b200059580c118402c004103d4903940c2c4040c0190307030006404030360166480020181e90340145006041e90f1445018000c2584189014455916a50301c1324035503403400b50014240007035010b8006002441c41d440343c4880c021144847c248550380d0340c2c40e145800d10180402401030404540403d105e03e042140e00c1591b06c40100910360100800d80121701880c3e5030220f400140a250a600e906d6170666044a088800c081d10410701c2440750ba6213a8220705400e0141103c0c20f403800540c40c0d1401c1e5a04140001604400111a172080d2507110000c81c40100f0409800402d000380c00c2c16900180c551800303410040200e4450341058100001440403a1000621901c0600035841590840c03090410b4800d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 365894838 1250 365893588 365893597
    0x1120503040f1502150105060406050703030b2206050f130b010903060207030503060f100c1203020f13050f09090c010e0607050a0c050f06041d060105190c110d050307020d0305 77
    0x8150100e0582c040340d8444548108042900d036a000c1751070040c2c0317100d040040ca41d424440c460740034204200034031416100d20043c214440c482d040110340e002c4100c001a100344400c002868000404100d0020903101a00514005003001d803116580503035040042144000c0c204032140600340c0764044901c20783d20a030140d4000303640000c0210740b14030881c0b400900320350095440c0e5115030819119168249000402079100109940b82c8150b00c1c1c03115038a20b940c1041c0d26806209255003480540c03505420341d80105103881c0981c0300c2c1415281030104004140254444550056014404000c0480d00c0040c83d01240d0b4000d01340103000c01f070b14100155681c0f02e082c00c020968050720509004020343c1c4030110701600c0080340c0c03001003600c1201c144030301c9008501c9091018600e42c03e030a80d83c854134405003030300701c24103244c074518120040044041100c2800b140d10006400d800d9500144884495003c03031914044800003000640740d202c09a81c0d000700301002e0301c40c42c2403608120030540980200c4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 365896088 1250 365894838 365894849
    0x31c09050312031f080604020f150c0717071a03040512070b09150c161415190204060509060d0b03240604020304030903170c3708030112050304 63
    0x11190042849010030183d007094410142c80c0c1c5084c00f80700480100340020406541c1d28070010001c41c1d840c0d40030460365203a024031050304034421080d00c0218145003002001c40c0220742004101091801120300070700c800622210804c2c4d00403c80c140070340e03407544804d00c0c00000c0e0a14019142e4549003003050400c882c510034446481e500181234000c00204400c007034416060301e429200450b60b410000c00701010116980800241e0400c070382ca5910640010405a0f240200206140b605110303024601d015001641000744040c20020000d1103100c00740c1c01c44c0d14048500c030550a00e071800074043d00a01400180503c654004a00394100c903440da4014220a58020105d88180c8040f813030f54520161020208104981c0c00000110207003094001c50340600d9050741c84804080c40c40e00c0d8102c24040c1e14a40250309002041072078061041089404100d191aa690380346141000400c600c1380d26003605402d880100500d22080820822410b9030b044919401144620601528002d4110f11554104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 365897338 1250 365896088 365896093
    0x11010804060204090c0e100f050d090c030218010e070f121109041b0201060b120a02030702100608060711060702150c04030215070227150f04052a0405031c090503 71
    0x201c030b1032580b00d07181010300740080d60781c0d47c0c52403141e07081150708003c408440d902088040001c40c00c403410710f500900d51036000c0e2602500b09a04c0342d0026140c3d00e500494170b08040450310050104004518010350090442e051862840224401c007a10304c0d1180c2c000e000710305a84000c803c48540800302100d442000c0140100304010724241401d28140b0070041c0c8000545c1b0381140440c011100c142212824541c032890211660759045100006c0d40c40208020110700030031564812500d468000c94010300424030240c03405140c04070300280f01e80750b014000c00036940301d10188108540c000c81c0052640c1003001d0410340c80ea807229085011703803250f43d00c02500100720f4544403602c841020701030600303240300f00d40d03400c403001c62058842d101403000c000b811044110680820700402030040102d02d042800340c124250b000210000800321042140c04007040710b0b0034082054802004880c5c800056100015142441d05003004256580481482c50200c010b000f84a41e80407409150210000d2000504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 365898588 1250 365897338 365897351
    0x3030b0a0b0c010603050c040209030705040504030203070807350304110f030307060506040f020702030d0507020d020901090c11011b0804020a09050705070302010e1c0507112d04091101080406020409 87
    0x1220b500034169403009a50034040c02008461300d141c24000c60f440104000c0040188904100270003001307140180049055200400a0100092205020300030660145030a06c0320001c0d01030030444074045198003610310075208400e10340000320f0700007640d0f0080d80019010700c1c0d510141340454008068203032420351610011070951308200e0140c01c980d100700010b640a101103c207000300c2100341d000b80e600007580740c0c0100f148016160701c2503010305002400180240c1d0b070380b41c2907008108256400c4e006120900d44078107a0140480c1c000010720305a0030340c1c0000704001c40210303450100c4041500516000c0041c070f50082001c2d50346d101014009041c40040403c1542080003028000ea070120381c0460141d400c010490501540114000c040c0400010400b0b9000502d01c404881c02d52208030101c030742c0c1c210701c200207045444140404180c0341e0740c00100c03441541315a4000307102898880c0711501c83d6040c00f40300303000034000b220031480c0d450302801e00034000d403281d182880103401a9005031120794584032 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 365899838 1250 365898588 365898607
    0x30a090219080f0f0604080c120d0b040c0804110607020105090301181e152703020d030b030307080703080705040305060f0109051501020705061308030d020c07061b03030b0a0b 77
    0x110700000b291440411584000403448201e900ca0302e000c1d2034102c0c290003500004000c02c81c80c400030a070032120a030550344075254542e20350304d02d40c02c06009160700e01d9890000300914102132207010302c80304417414219201d00c2c0c02d644540c248030119100a01038100828808211f900030416200d259000500030301414880000a00304002404000e07180384012070b81142d120105080c18001c2c00d904a02c4110009011a0b4004060002d00804811044440790b40483d103515407290101440e10a5001e0400704030011801402c0d5407441c00701c184260801c001400024002d08120340d002c1d545814960b80075503411006958030300036a44042e0690040804101c81220b0300359105050703e1a031007080020307440d13450804c10000d10b20300c1b540340980d100c030500b40414500f0102424440c81758161802c3d8542e1600301650850304030103601d0f0011600032541003488042448484050032142c6481d00134141d06c503030180d2440404030005400c3c19900c4070310410544800600401a151a16809070b5403016807 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 365901088 1250 365899838 365899879
    0x3140c0a06021c1b1e050405040c120f0c02010b010518190f0f03051005070f0e0415081f0b0306280c050304020f0f0604030b180d0c050c0a0e0c030a0902 67
    0x80000002900c28207240103080c12242040d4100c983c01c6da501810142043d00b848024144003e020080c819485a60400c506a600070104034440c188000b248140854038080d00703652080f003000341031180512400580407440c49074041080701c21194000740c480b1104a02c0005200e030b03048040b8489403c280840c5280952403100101c81c1303e2411a01c90402c669202d000710381003a944000005d001c40c40d2094038a218010b40400180020400903404111004d48030503040958000350346034110065140b400742c00c00042044040c607400c41400f0b00066030000030748554006060070080343e04441024900e10500724540d2019a0000e01008600101507002e07007030f90400c8400b00d01c2601e0918070385080341480c1c0301da08102c0300060042414181995188416044001c041081803071300d491a03c40c1d2003100b0000d840d845243c6494407031035041e01d803c21504061580022600a4140c2202000900c815164650344000102c0c803513501e81e200c0c0c10908001e0080058042e50003003a8178680150151031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 365902338 1250 365901088 365901131
    0xf031107141c0801030b01090515040c0f1827020f1602090603010c020304121e0c0305060c0a0807030905012c07091802010503101703030403140c0a06021c 68
    0x401c50100103910340b000881e125402400000c00c1c0c41c1511740100501740322500015040034031030000c2c004c3e511401c4042003c0b2450b1441c2c2c180021001000d00c410150030041c460380d0000c11106865009041141e409140d500b004007a11008007130111a40b8031403141e03070607104001810b00e1000c1e61412a0b0a41c1362403400e0091040e03104550b440c010a00601d0144079840c1180f180390044c600780ba00d80204610007000c40340b802d07601c00d10034034940b6841003480071746c8480c1c261244030141040c5003076040caa4078088008000c80c1c00c803d01000348090580e0410740056001c1c0040c600803c110304240380a42c090b086c0c1030f0717840d6010400c41600b0100c5c600117000328070303c5681c03120489001c0c0b66129808001d4905036201d052582d203d0008440155124100451344504982100700b07030107655083e588180c059440e200300c2550008401e0004050340703c0a0500703100c0703241603014101005400050746803242e441d001000a6800103e0200e050421241c100134608001070400c8400722080002c1d0b4250207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 365903588 1250 365902338 365902363
    0x40509010504231503070308030f0c03010321110d02010c02010e0109080405060904020f04030302030c0c09040210110f0109050c0f0a0b160501090803130b15010f03110714 75
    0x91020021401d820b00d03101e035100d056903a50440c2d40210007050714025004002c0e10711000400340800101142c2c904215480c000c0d40324844c0d555482c900281c040b48040350103007801d68080c1d020401080481d0302404001030800c819000c0440054814205480e603141420b40c402c2140520603030a8056074041d4400718845c02d85030001e2050700c143d59929422144403140050124005210502c96030030404060030303010201420042c43c212202ca00c454050708207500480050740002010811010300340807000300700301e090314403410078149903002442c2d108101e0f1035101000309001c0c0344919590100700d100c500c611014001c00080c40e840c02c0842d11540c54400b4140107109250440b046410800d403805c0071a500a0031403030810329003d11700c030550354803031800780c411750340303a4070003001080b060300095015004905000317958100390702d0042030400008010341e103600c0741c1c20b03c20041644c000c46420343d8001240b07000504403400c41109100c0740140700f0058803140803900300c05280c2500064080380340c0e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 365904838 1250 365903588 365903599
    0x6040209010b19080406020906031018050402100c0203100608030403140f030a1b0209010b282a0f08070c120c0603020c1005150f010e0303030402010f050f0c030405 72
    0x207072907400c000d29030301c0f40390455680d1942e41074640e50114854080d80f40c00038891140585086801c0b40094841e400c10b07204030181440400c0d040145100c407100d00540d80102d00b005210a283c07903000241c2d4810841450410300ca56603450000715a0103214883c43c0c00c0c440b00c400c2044030780745e52142da40ca0300517000072541b00115422045591b0710000e0f44e4403240c120000114541510140e003203172446001a01c02c50111040000500143d070b42c60a0240a01b4000400944a1101c00c4c514240c81d4401d401d80f02d41c0c0b02c41c0c208549495a4000c0c80d1441c18541d00d03900d00b81c0c19004018036504060040005040350301a4801701c410800704034014101c4034080d041d0100856101c40c4c070700e011041b10718002443c40d22a2032040101320700a40242c03040358180c80a0b6101120710006e107030140d070400c45030f0303280318420b0b1501003200746082c2c901213180f02020328220514225a42c0402da80f407001801c080c1c1448000c50704081060701c03900440381849000c24540d0384400807c038486540e90040c1c00381d030f031081 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 365906088 1250 365904838 365904841
    0xb04090b060f010806031e1204060f0306050f03060106030e030d0e0321010b0306152703061509040f0804031b06140306090406200f09040f15090f180506040209 70
    0x3d6205905090040320010007400e551340800546900c0c095502000040e140101d030b58044e89034180c100940001e00c900c0d12100072141d0521002130444070650041e41c8909100e843c0070b0840c0d10001070840c15108a4207000604a0301c441005245000740501025a58102017507a0f003480c0000c005401c140304550780500340c080f16000380c5d54100c1c809010f60586900d040c4006409481c001070540208400301020b149009900d91303004800745480784c0c0d000000e203480b4404c604682803c121031036104420740c000d11512465800040e803402400340c809007010240c51031202c14085108120344c01140d10a5a450850402c6942228086c010740f01c0c0d080480c82d907400025090707007a54100d920813000204601340030358581c1d07030b0314002708840104c0172401425400d803580d1040104005060801202c0c400d02d4480400004210a50701e10900e41c1010500740300f05221b000114804900581c0d040d0440441c1400301c02c05203000810035007010361601044125044244607000c52507502850080e1000c8100e07 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 365907338 1250 365906088 365906119
    0xe1b0a0806130605071715130606090b0715060e09010c1403040308040c030209010602010f15050a0e0403030b090c03061807020304060f090812031008010902130c030b04090b06 77
    0x15800202d8080040c0c40042c501c02d00090029400194452201d080003004881482c0074448940403c545400d2201e4501c44c40c150756141c00c6c0c080da81d120480d081e00f80103172030a0000082c01004a4881c840101c0c2e4086a2482044455902e1070034100c400f0204014540e0398954054214a058443c4d1403d03520344030001c852588034407141c0b84014141c505951440c2c4495400f2a0f000000400a44080c10f0280020006136208100e090092070a9070020075152101d071000720458080c0c812030000100d61075401c20081d102c2155081c12074aa410585103580d1382e0f41003d0f0081e001001403130b80d0266081080008003401d03400594010b050a031080c041840500d03ca0404400b4280d9003040564010b11040040601c00c02c0d8a0204030600c0c54030340102e41e80d502d011840d00040c107091284900010080090075070004900d030f002080204002d0000c201140c01062022521401059800e503d94000c00d80c100c0c001d4210300c1d400701c406030040180c1d00c941d061408004c0d0741038a06038411444091024070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 365908588 1250 365907338 365907343
    0x10b1c020d05121c020315210609010e070e0910110d0203010603060e0c0703080105090c1b010f050c03040b04030e0d140d1b0503090906040908070f02030c1e130e1b0a08 74
    0x2084001f00c807451488000c1004000d00401c10310860200c840d031040044400041c00d20109000b64401030010a110b8080303250581040003d0304504407059000081150003100011800d5000d042c00000240708118803c3c0c000880c0310b0220384003e04d5000000000b103890781030340040700319014207400c580766032a240400201d41c8540c42c400741c0080d00440041c0a68076100380e5003504030070341e0202e981c604410f050b1410316000c5251040c1149035547e1102e45100703075003800b0311603001200024051440c5080e40d1000005000500094100a008010f068840d01c60503101c00900341c100180034044503980d0760541e5201d1500d544840007604a00c010343c020a0400403410b14164441c02450070441c003002031040050009200c0e86e4440e44407115040840c078800000e1110301e006000e0250540700500601d80380440b800c035203e0190300810300110070340c0e6400302c2581c0c1c1c0c201d044074214074000c05c40f55050b004d8041100c2004c01ca0142e00c030011401103c7c0451484065000e84100c1078555844071820b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 365909838 1250 365908588 365908591
    0x30c07121106070f0f0f0e040603111906080403030b040617030703030b01030c0c03080a0f090b07022118120102041e0f050114030a090c03030804020111010b1c020d05121c0203 77
    0x8005c0380c1207110341305080c0e00951038101c00020501e80141441001d90010301030301c1040d401501c00002c070554140050401c0e0f0303014803400401c2c4014800b114a0002c0c02819400014405030030542d80e480c8811081e40c2e5600141c000b01188007030303200d010800003141e50b22a4008001203001c24501081c0754429406401482c02032902515042c9484099440649004d60002e080c0340d1119a02c0000144d50361551181e002042d0161080000c14900a04040d1800a54154801e5080d15141034840d4038000902201d19500c00b050108c0004103840011640d01c04084120505550000c1030109030304501420710810000711134019460242d8441c0c41e00c04c0840b41b405014005801c902490b90400c2c0c440d4020744d001100d101c0001000f000646602d00c20100b981c0084001034240400c0c00195039101030700031240004a0000c000f640c40490009180c1d01d8000242c82c2084051003d400c01d640e12058103103604c0b9044016a40d9011016620304002e40c006074807100914402181b40c555850301d882502e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 365911088 1250 365909838 365909867
    0x60409050723030105120114090d0206071b060902060712030515010e0a1401121515031a0907031d060609010b0a0e04020d06080d09140f01080a02030c0712110607 71
    0x1610310307400e050912981306c4400c511049a5034890f9403081811040d410614403402070080a80382036005400000e091a2020303002c40108012984035108030042080d140305c10a0b4400c10002d0043c0a80c40403807040d000d000030240403420b00b52041e015403074240d0080e510405000b6144501c00c2d01d2480195080440d08800c0c030303004808100c3c14481c1540c15041404900b44c141050310070ba401580008042e6000320074013451203800c200003003000d40c800c0200988000b00381c1c141440041809101110791000d032030009071041c000000403c003114040d5000e48940914074242504182407030308001d5403248250707980c40c003c4010400014840c8040c9042c2c54011042da80c403500307000d90600800010b03401481d81285c907191b076040c1c00240c0c0101002000013440c401d4840c402542c0c038001560300310034908031501e8050310898a280001d6a40300402c00da101c81e181400503141c0d19a8a42040d250141100041c8005c000041207051190410024800034403094221840d0303a88011048403074902e124500c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 365912338 1250 365911088 365911157
    0x318090207050a061a0613150804050a030c0320071a0c0a060908120117060a1815020f040303020f010f1b08070c0606090207050127020105180604090507 67
    0x381800940945c211115075503201d10200100e10b01c0d400007541a610071040440091440c1c01c1c20019801030806028100490341042031480c601500c405840f0a03000100a040001c11030090003050f0160044461401141d50110030302d0991420590303603041c550107102c8201c090244081030701780c051412210150342e00d002800203072003142c0d1804054611040c1c00c5a0303400e024050401030880041c0daa038001c2c41103114500e100c46485140314105030000d042601c5040c20908480c0d40c0c040c000a1011038207a001880901f42d24180d0ba54800a009107280c4c9c1f80748000c001000000e05034001f81c85c10000140b83c008000540310340180c40102c54541101480c003d00002070506800d004040c0e6503809010b5080c0541c0702c04095603460119a03544c0c015030304496011655006001e024030607614217091000d400c0078005d003841c07407642810009180090401a0000b8520349000e400600300b07140e020090310b500e403215107606904016000c100c41e0640043c0688040e00940500e241621041c14860001d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 365913588 1250 365912338 365912353
    0xd230c0d0f02042909040c05070308181c0513030602040614030112030f03240602071703040e1e0f06011103090a150504080a230607020d0e0f0d031809020705 69
    0xb60318560380e82c0d1980140144d0381c203000c80c000e2619180110041003800ba50b5403903540c00d2902d4050070000d0060719403100e201d50400c2c41200a10005215403441ca01205174840d0041c9000f821583c0d44258201200c10180b80c2d00004100714541d006401510300603216103c1c0410500c00d00c2c034081c0400d11900751250340c001c00b990007090141e4050100c0d01158030740800d081c00d8900e80124219461a2001c0030304450100400226074180810340240040000c81c00c2280051243c030b581c0d9000714043c1c8610800f440e80442e043c24101d1a002480400354103146200c0d01d810b6405107028601224000d012882c0300325000d4090b000841100c021480003010b0707004171828131819080c2411700701d00d10001e0000402000c5580d02040043c07091482c42122110915840c00030303400070140307407d0210401075100c007060220603034012803000d181400c00c4c5440002c1030200800208848003178085550004510007040090651001070302c100e001c6132035402d41c011941c1c0c0f61034001301c0c40b0b0140041d15a401505 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 365914838 1250 365913588 365913629
    0xf050102120903071a100506030f010302010f0314060f030a0b0a1509060b1e040b121608040c0b07030201090c080c01020708030a0f082508040b0108060106050d230c0d0f0204 76
    0xb4030b240d00302084a000b906e141c3d449502140142d1b0040d52241040c2c40002e00400441d0390044070080580042d103002d10441d11420140780e040388010b08440e00c9012106c920b044180c8003000400f11b0075420040380c0905040c008400f0004107152110385600e038002000200300301c103803402810200c0d40e4a1503000e292504554051450301402d42403158240420000004c580b40e690016019111480c0100180b60038040142500c0c038a00100306001d008000c0100710200707407081c00010443d040e01b4070090741c0d12041e00d8224010052000700401074030440402242103500041c03c0c0b4100402a0201c491850b213644101e5503a0051001c4a800586456954000390b4400c81055410141d07003d02c0074000800c032045002179400c1c4012450000300240200000d014000300c1e8640180722a030042c140035414500020040e11400d11580381503612a5414042d805000e020034900b00351b0b54108441c181407900c2040c80f29405007000f600300070b081030b83e10303d50030b56240308650031999515410080300000c2c0c0f = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 365916088 1250 365914838 365914883
    0x8010e01092c16050405090606010c0302100f050105010f11120c421005011103090a0602070816050607021c1e210c030e0d0f05010212090307 62
    0xd4161002102da440301610501500e10841402d1020107070151105903145141c4030700c451003e611803071240b4141403e000c0a030b0800f0410f590028800c0ca0406408240d904069240c4148524002036140c9401c0c181c1429401a5001506892007681c9040304010000001c440329010b515130520542c1040b00b491103559001802040c90031040d0301a1220480802d0009904125a8864055000c01c0303404500032061f0182c4138101110320700c2c80c0021141020406400c1841140c01018144030403071060007141d220403c00e503202c9803c02040070005a0300c9407402520b07a9014490380d6228800c0c458904202d541c1e50350040159174010b8022410402203400f04072000511001c500c0e213502e8108180c101007141220101d0b40d4450104464540913482d10b0300c0480c07124244050baa000000741a14114140d201c402c3c68401d541500d801d028503c010800030341004240309004044a820903001c100708801900904107030b40c100840000b2030b41c0d52001440d03c07885140d1004117148041c0900309400c1001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 365917338 1250 365916088 365916101
    0x105040b010608240a1a09040e0d0e04020d0204090510140103140f1018020901180501050703030b0f27090a0201020a14191a0705040f030618020306100306050708010e0109 75
    0x900e42c1940070b545001b0320f06007601911901245040c00a070100490500e13010b104504441c50f130043c112500d90480050000b2028003440c0d100301e40001d003d00b10701c02c09406071400740a40440c200410b0602c04910100c002a900c1101003001081800c1d01c1150f02a201b00c001d5020701d02a40c0d07020b95920900b029180000604038503401080701c101080c0001201e2424031441c250794001a60b4006200000d080300301341481d4110035041c160700a100c9640c2c400d06460b034160f41801d001c10303400755000000f01541222100f040d00020656080c400b40c3c004030000410340c003401c48410b0120380b545100c00d5161620114042d0160341b101801c100000c140403440e4031034461030000d8440900307002901c1901c00d400000c042d42c042c42e07203091410542e0140c0d0300664000a5038105240b03024502105c4c4a03d0a0152002a02d826544c4169410000d000200c2483d2241d00405a070740a00e415100c84d0301c100903600041da44a0701d0000000d100600400407141651405288100203a207040c80160207841d5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 365918588 1250 365917338 365917411
    0x2040f062105092103010f0e09011d0a03030e030f0301030b1f060f020f0f0c01110c211e030d0b0d020307080105071b200315090105040b010608 63
    0x700c01d00c444940d103880b44562806100a10082c0000c0c041540c8500c041c00c1144501000400d400c00c010403d030310540d50b007001101d03200c11004903d40e80300c140700390040c41d08400100c0c20202300d030303685581e84102180c060745003031094504110051511000640d24099880c5120012500308018030210f01d5060310741da8040f0284c2d9105d0000c41c0c02080546205807103500500200b040c440d004140c464041c481c00c400984020010096074003901d180c2551041011442410300103030203131050b100c0c1d4081c80308601d540b401400c0e160f4006940898601d07030461000c04103070a03000d007801c0202402880200078126119040040d800d1040c04030f80a00104919603200d41e100040500c03c000603102803100c070000344000000094039103004000641810308880810b060000340d190300c1400562100000b4407400d90501e00300c1c0420350118042442e2840014409040025120402501410541186210714811201c4e5183d50360b840d10300f6205580241c0300c2920075502d40b0200703841c20f480090100d45285 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 365919838 1250 365918588 365918627
    0x1110a050c1507120c060c020105072001090b0f060312071121010f1e150e0a14091c09061b17070302060f0f0402010c08030c13080f010b0402040f06 65
    0x50950707803168048983d15104d0f0106140340c014200b80a02440344401800e00f1303000900003440d00c010000c00307080b207022075003e819500000c0c21030241825800360a10541c483c05814850030240d0009503803110444000b8031a104080340c0400804822090f503101c1540000035145903098001005240c400c8042d140100030400320820000d65030901900b507001e82510000070310880d0392441e0040003d101402c1d2560103007810031106e00451f07001a0a412270364000c95048094580d8480c103030281c840c008440c07444000e00d106104c1700820110b10608407041c030003101085004940303416100e130090341c80781c64003144540102d0007400c5400c41019011500c200c0c0204012460480400c030250004201a4016403001c010412038000840d0340303075080b00100d40b101140b441c01d980000d01c01904c07440c00400009003c000306080301c5060003513035184012800756440568990301d880c1c0da1804802c989401e07075800d003a010034080c2002c1c802c1750165440e900541e104941019016103011012000342038080 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 365921088 1250 365919838 365919847
    0x90109080301090b1f210608010905030a1e050a03020d06030b010b2a120d0e06161d060a1b08040f0e070f02030307032a050901110a050c15 61
    0x61401030055010f0145001c0001d01d500e0b645060000d043e040140780858034404007000c0209980000a00c000c030f072918200f4a08071450000703024007400e02c5074000c0b1070560900301d0030810098040050960b80c02c203551003100304401110b192144100381400500070417070030007013174190500c20b070000e01c500b0501c1c0c040030034020b82d01c1d40c0386450341d6002d90001041d01008961403c41e0820304086020b4280e41c003400d0424161002d032041d0301d802141031107085511000170308002c07001c1c041d0010079480d03102c0ca050303074850b1034208550006281e03a00c001d0b0002520a03214941c0e0415a1550303001880c1000d0300c4207040074a224800d1300e04ea900030f902c1071520301802e200640010000f00061018004280c5003404191804040000c0b14401030701c1e040602001161003010a0344c000152580420030f882c3c04100d00d17841d4000000d0621411040811441c1004140400039800c200103007400f80080e600e90141a06500c500b60300c400c440c45000b0495000030204c10b034645010700b076a01ea0001c1100b11103140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 365922338 1250 365921088 365921093
    0x105070602190815040203010e13240b21070302130204050a0306020a14070b04240905070e060d0b16020c220b060f120a0e0f0606090106030207080f03090109 69
    0x3414140408200041d815810015101034885079884c5240e000d441c1981154107044401c03110341801050348810301c4071082101d05025903280025600300c0c08990032580003021510b810080c10049003e01d0259130704014400040300c0c1407081d2100b00031010007412886003198208842003003900300f07d00300642c0a200c00300e400d81da904103031030040d0304c61500180d55052003100902640d10702030302081c03c1070040c00f82e1800701d900039401940c810350019629007244142220070001842c94a040f940741483c1c00581410441e0001c2d502d42a42d2603656607211030b0f95000d003081000854131038024140c12420002c030340c49481041c1001d0340d003800e5005807102e0b890b50202162211032a4a10600d40c1d588100103641b200d0410300c0780c2d0040d8107090f00c60a162805001d48504544a00140070030340901c14000120b6900c0664458001156290306503034169110b44110360b5151419240c4a100d00d18042c000110940207208545c03c842c0e000c2409420027015813020141500300400e100d00654803024132400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 365923588 1250 365922338 365922367
    0x3030703090203030405041e051f060c02060d02040306020c06060603270109080a0801300b060307030b10030308060d0c050904030e0303030a020318150109020a110604030203071514060105070602 85
    0xc0000808d1400c1c0c20982d515403c1030075200e01074118142820030485800351409403000c810103960355400c009504040c9132000c2a040d2048014000044d48045030100c10020240c005181014101040b140c0382e0322010204041803100391041281c440310f030042a504621403884000328100d07220000141c1043d5034403001342c0343e40000104c41c0082c42142c01400043c4d42007284ea50b04280010a1000320b004c80017854820b04504a0064090501140000c07169681000301d000650f41c8038402c6401030401e4000c225004401380000c9010900800014005090580c400c1007055080281c21909520b042c003840440c160182c41074003081040f08034000c064400b000190300032500410010b98903d440101546541400004241c0e131360040154804110203a09a8a041d50311203100180e07610825201900d074805907110404060145800300300c141354012025065060087c1600342c0c6410000510b0302c00c45000c03200c050400c0500e0030102312303254402c1000d000094429074005103480501242d600 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 365924838 1250 365923588 365923601
    0x510291c0f0f022508070807140a03031a18041b150c060606050a09060f050912160501110d03050c09061204030e0d050304050d080708030a0504061b020303070309020303040504 77
    0x322070b50780000c0c0c1c01d44003044411660682007004518503404502c15604c9405610584001030207000e00410103500340a011082c40c2c038071110000403602c2200031454040e002e08840050580003c80b14041c500c031a00b001208002c031160984403c1000b40d03a1581c85003000c540c00b02c10000400c40c1c4480c0450034501d0300b000c1100b501c1c1692688d5101900528024095400c40c1d0071040400c00306000035034103d6080244882628000d0410345001501198116024007420b20100d9100d10758900c1d1510721034000c00d045007001d0b04114041442901c0307100540348800402142061580600d25510350319210398490380d000445403800e146840a02000100300303400c46940e01900b10100002e100c201900050031455141d41039410010103041901c40303d4481c019886034500828100790400104602c2c20115000d280d441040300303890342021029600100022102140c2072482e1003115642000e1850004007819100e0b8000c518583c0e42050407030140150040890301071009100c0881d040d40e5a00464 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 365926088 1250 365924838 365924861
    0x1021204050d080c19110a0506091e280305010c0c0f0803101a0307171003020f0609060a110d0215041b03060e030702090f0103020904031808010510291c0f 68
    0x100072962060400c1803c105c40e6008c544240000c2140b6078450301c54004800501c0364150341115144150300c0810031205603050615010500038040c0c9500c0d200b082480c0003941e001d90000c00000c03019440c2030f0303144c0007442c0015020701c8550384940c0004204100840e070150b1758a081c01f4500f5a01c20341c41558180e0090302101c901c01c08000c0021042d40031041d01c0c2c0d00b0b00c001401103003c2c180305032032084490003808082d01503036aa00b0f11680b075403210001c945041c1e10140010b0342d2074031000c2c0300130155030703041d01c018045026050b1140c14441c40012400c00150000d1007030072842e151542e80400020340c040d0f2540e1000c40441000010509a200300c8000038440005580d6a02c4d1520422100e4a401001002c100c1820001400940c0340c04180d40d07805903040c2410110a03000e10407592034038510741d220a8466003040e08010b04134007070b04500c2c42180e0342c00174032400854070110025240701c00c01c2044000020300f4010300c440c0311840034010b170340b010103403030b001505140c1d11003400e06540ca0702000303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 365927338 1250 365926088 365926103
    0xf130e07050c010507080411040e030714070312020c06040e09010b0a060201060f05011b0303020c1203132f04050618040f0209060a0602070608250801030201021204050d080c19 77
    0x462180b80c0302800f42652003a020324050070903150a41e030b40034200e0710030854a40225601d02c07071081d1003103003082204c084c1c4e81c01c50000c1802115081e429693b40b40107000444407010700240e08541c0c54000102a0b1303090134010800c9080c2030410344100c0c00250000d20400b090743d02c3d0460f140040d20350007098406000190700201e04035060081605182580c0e0340014100003485441d03140c0c4242c880c620750181585880d02585d1010f80204081c0743ca000c403807816107488030001c2800342c200c000180072120240718074204500c881102103005460301da00300910114607200414400d2915059000d40e9000030300a000c0103500310309851001380b50504540848003d070842101030158505074403101c0d030190088030401d00640c2411002915101540f003140700740f2900c5004582d81501031444020040304001c000444030078046002411580284426070143c040c40d05d481000c40d00110864050780c3e400741c44e0b03400b0030045549222040d444111014254001d015440b40307080b40f06800c0510701d0303028061 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 365928588 1250 365927338 365927347
    0x30801030b06060f09130605130e060f15010c031806030f0e0309061905040b0c030a0e010e15030901060b120411010804030c0b040611032d0c0f130e0705 67
    0x1040c074006600982268031805041c050041c070a03602e1011980034020a6a141c400705481002e40c901170022074001039441000f10941448005c1150301c81e004c8020401c0464100d030700da0141407404020f0030b40d1061181104d07840450104c3d40a441d400942500ca482c140c403182c081c0c800e9070481c1803031540105001030344030a80c141c500c0700d45000340002c1000f80c001031450603d1200002d0264490403020100c400c45442107003102c0c0e405001528000d2001e561b41d03d6075100720004807500c0b94080091000880c0003085034555079441000d406018807000b0b0001507114121b800c88a07001d42005162891642d00d8031320109916000e074001e84103c04c10040d016109050510303000b9030540e1159469030401028408200101e54032040303102090790403c01e498015282d82c00e002000e40444108070045180c000180141040f5440003064115081c002403100b01312a0003200d03504c1d00064074001814042841605840f520f000c0040444440d40c5000340f6807603075941d1310034510b090b0498142d400f003040481c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 365929838 1250 365928588 365928593
    0x1207020108010b0a02071511100207060f0504020604090905030c1b12010507141c05010308091305090304050402030603070e10180b211513111008070f03110703080103 73
    0x20900d60243c00c440c03c0d10360410701d682000a68422062048161699071103800a245600503104c0a003901180800d650002030600d14031006903100140444109141840e801c1104116104003401140e00401c143d2800e89019059009403c03c541700b0b0f51a0302003003081e100310f90401c04c400159020b03e40040c082003143c1c4410026050034500d91040a40d04120410036181e0340003402d1400c801c3d5141c605502c2c0c55541d04c03030440500320f00c1481000c503403600d4004130030b00ca400c0f0041c1c00f1000e8112290620088071700d00303941c10f850081d181000c10360300c24002801030780303015005964410701c05000c03182350070b588007000310040c2021340311035009005407035080c4182c904088000d07040e600116018010403503080085441c9031000d41030505947c40e108420b18404c0d005018042030200002c40300102070801204070980c070104080101d9109a00031110102410a25001015400c0d0364603117000942e00c20400381e50810600c00098101680e0340d000c09804401d11000e051140d00a56440c600c0350f0452 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 365931088 1250 365929838 365929847
    0x6040e010e0703140f04060929010f0501140304020904170706020309010b040204081b03120a02011b09080a08070206120f070801140a030807063c0b0a030f110312070201 74
    0x124004e4000c512001c00f0415084144000329030060b07400040060001c03100e04281162030789050300042d14031380c0030751000350000e2a0404141607e012903481c101d03031a40d90005458040403c481101703030801c01d20000f0058130b0103186180d4854010b010004918860002100d0f0700e600000048403056408002e00054038000d00c034440700b480c425203085140c103042030311441d0f80304414410082c0000c000c6a00d050365440504c038126000140c194030540302c0900c01c2000e07001e03006000314440b6117008c510704080b845204488440440d003012005c0d02200b07095031607120159001318000c2c1d070803c004019804045680132000ba1041d403007030764210303040e04042d030000344200e0041c0d101c4542014900801c0003141d070388040c0001221b03880151207039602c07914a41100a4008002c0600024104500c46144000400074040d18140f802034109050304010310f11031700b250f484644042d0440c034031810a0000a000345001c00481d4001d5402c01005d808020009207441c1000d00300c1100c91202050060455820 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 365932338 1250 365931088 365931101
    0x20c121b070e0f010e0601020f071409060d03090b0a020a02031617070803041401090801060b0307110f0604020409031209061d03030903340503041403060402010c1106040e010e0703 79
    0x40c88010b520381c10f00c200001c0f290f001c1030041d11540302075200441c869038020042804e0450b8620207451001d9600e81051030b03040c0820885a000d0010b160014100c0d02e0800c6001c11113643c03648500c1035850070008079182a4210039540400e600c01d02105101595003003152600c041e00e50710040500b1410001c4603840300840c01d8451080d40d100c2c04050000400110644003501e1240a002c00c120382001e00407681310305c4503032100206518004010074a5051040218420750b45500e42e0008000c8000c0340655880025650301c03001d421400110f001840c2903041f000205000c4d1414413a00c1040d01300440481e01c0e2070754200c1e5626501d00c02c1860400350000800380d43d0060320080d60561a04030422910b0303204410880c00741d040c85c0180740c0f1a60318050881810103d001000b41405205407030403e50325841401040000817100902218038a00081c409208a50680d10501c0c8070b10580c0d5401007440d6000c0485621030307024403020500b81d80080e900c50091801094552140c205503030040c044404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 365933588 1250 365932338 365932349
    0xc041412070302040c03020909040c030201020c060a08060d0807051506130b3a080c0c0d1101031d010e100e07060c110310050a0b0901051909020c121b07 67
    0x100e031201810084041004800c8070f4054030045028040a0320440007407081c3c3c079070310b5070118448050105002c110151142906e00c01c1e021151102401c138104612402024100f2000417455800501c09082921403010003620070300f01c1d9070400025a5415042c014180b01844005010030200011460004039803144200000c04c00c100a400840101d41070080750365203890007680c40c0d0300c0328002c410b03503410708540b8410500c010181050300746006240795002e82440c001c2482903040114aa00d00200c80101090744000c0c002c2d04c0c031202500660103480e01e440c1d1b031000c500080041c1c55030800c0a0003106020301d06880a8540c540130983e45000711180c0740035004581d0310400e800e000998020051028a5420821658518103c50002454082e1503a440e0080c030b41050180f2040440c603410070100c4c00c0040701d010900341e1701c2d541845143c01d0714035a02c900502590804000692440e401807424900040580749a540303403a41c28842c603800401b200081d031140103880c4240d1901171212601904 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 365934838 1250 365933588 365933599
    0x308010e160509030a020a030c030303060f0b07030309020a08010e03130b0306010e01210903050702030c030a051b040905030406020d121b050307020c0a0f061202090a060807050c060c0414 82
    0x41690700e140403415000540e000344a000265501c02d03980810a4640c603550080c401040107071031707180034080c4150b648000c8022070300388540840e610026010078020340c0d016001250070408691403c5019000040007030380c02c40d60704980401c42800070300443c600d04551a0045654601150101c0a4246a0382c41005089010310074070409030b0707001d100390899920911b48040c00c2c001214540303d00126140e80c0c0c06480746481c0c800710030150032401500c00c05000310706986580446d8000e00d41c4919144000402540007404124401025141d901d1841c12019100250000d980d640381c51039a4420340010015a010380130b944185a4803180d8003c000a04003824808060464810404030002d5001d0005100010000030940d91003040031418946e801800c8041d4150358a020110840480c0190000160006182111002c1038001c845007840c010f040c080d051481c03c0401c40e05400b0141c01c9204001c0c080004502a00040081ca40200d60754148595543e2801c1043c0d031040185441c524041d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 365936088 1250 365934838 365934841
    0xf0b2505041a0c030c0f0604022704060e0c090a020304021f0503040818130b040c030204060c0206030702010618020c1501060c0605070521010305160828080a0c0308010e 74
    0x42e5000c2d20b00494408401d80c007521546441c0d11a8214016824004500e100b00c4212002c480d0000500038000c82c0281d408540304002e17440100c0d22a20308050300c084600c48803010500080291340310303600200d00c000907504d1544814002540308081610341200d403c0d0048180425842c0881c8800d05510140385045000c00c28244c010341640030003071018104600203c0d203204a10214856000c0039000100043c849600000c03c4c24018043e441585008ea850503403640c41082c042d100b00c506403001d5442c2d4004004440e0f0070880164001040201195250240041d2101110011070f10888a56001580741c0c5144e8500700e150180c034400f0105079560460040003029008140f8440b01d80e001100445d003551b880100317035903511403001d05078450542000401c43c121038180f0014140d070f00c107009075056004010340e108544801030040c0c3d216500405a910810aa24090b004001104100003041100251200d4075035400c04517000010810440c58401010341c0601c1450140102c0d07000302125 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 365937338 1250 365936088 365936099
    0x90114040b0c0706090308070210060501051813020301030c090e0307021806010c050d0f1707050f160c09050403021011041a07020406090e160b03070c0f0b250504 71
    0x105840500054480c090000200791029405001c403114a6007000303052102110300d28006144031011190600103000c0c00038040051003d40c0551401c8901c165510380c02c0042e9018026440d000140150f684a5401c54200030f00d5902400030b103000f54059121403d049140c00301c2581500c07040d40e4401072a80003000440c0042c0ea980403401d080c03070b0007052102121354a08005070ba041c0241d080c003411503c5445061042d2903804040000c61001d40d64601d00c414a0b5421070741c03144031094640344007103102030000c0c054518034080909004618022000c0748a00075845002640043d608460301c42a1144204010316404101002110034542c100f080560542c1075000007a0080e07000e04200c500c8103031007120b04004024140c074401074000300100001c56491140c0801081401e404046134041c4500c04985103070400b00301c404039018440e070640341d603594140456495128540c1214181c030b80d80c0f0308a0100b2402c4019901c2001c28480303045121812a4001c00801780304400d560401000700f009112 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 365938588 1250 365937338 365937371
    0x91502030423041a0a06080c09010309031b05030a0314070905150c0f01050f1003121b080d0c03060504090c0e130f050a022e0c030302090a0801140901 66
    0x44034001c6000b40110034061420011910040c01110307442810540754134481144200350b45a18241140c04240640c1c0e134100c00c0d40e44500860708118024002e1141c15115406a013140d51014424508180b183d41c0c6403135040d0498040b05000d4946903c0411150610307909885603d5480840141d2403809203001080180760064601440d4050415094401c1c80410008107490411040d2004d4505048001c10791a00a00c230448000c010b065004020a00c030781807914074802623a401400c03043c1c001403292803c0d5540b142e4004c10019105800e00700c900414002c6015101c443d00429000c51440e12041000f030544a2540240f4801c503d88215080011000012441114001c1c00c8405090b55050411081e205c0072000c06084050940742800130070501041112541d80700701c8030005410000c0c1d10001408802c80780c0d41007030550a0701c10700b001501a561036982248a40f4000d03160000c590f010440c042c09a510561190791121503d0030400070180f03a5583c403c42c030307500030031100781111090316 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 365939838 1250 365938588 365938597
    0x4030f0f050909181618060501140f0a091a03040b0601110c190306020708030907060c020117090c032413020604060f030f02030f070f08060f13020417010203060109150203 75
    0x454541d0004d03000c054581d4140115203003904900e10130f0701c00603550039007104490181c1c916122403d00c1d082c0085110341c00b4060782e0001034030a51701d0609040705405031b1035040d80084603080910441c0000055400041c10442401c0c000c03120304d075610303030030a0318010700480301c0030b806541806412100c3c00c07800c20000400c40e101d090100d45500c002045c5840704d0000c1d041075080a0401400061ba420511010000450007681c0714411156032541d1494200c2e00440d003100000d0001340b514043d101c203c42c910701150b800810030300a40c4d000001c03201c00603160031158a02441009042207500050581c1883c011f0b5100c1d006444401410000d07600140e690b20441c00354a0500c10441500c0e41107910a90208140d0802410110b54a0800c45404924100e0440c0d9010008008e201000181d510401c5180d00a14000d00038100000080007041940c03003c40c000c0782c001d26420f0100140504201e00280c1400000354001a0342e07040c0800010842c1c0110381001555106580f52401c040c1c1e030000843c5c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 365941088 1250 365939838 365939851
    0xe010c26010602330a09050f0d091403010b09042001050f07060509120d0b090c0c1b0409020a031a0c0a120903030b060d06050906100806100e030604030f0f050909 71
    0xfa0b4600790200413162a02100400c4c400c265114001000b18042e0203034051910a8095001c03594100612101d40317640340083c103032000001e00c3c00c0c0801c100e9404205010a40c0e07041c000d0000c00d2880240d00452000340c0e04440031b503598107404540b826100c2e403400507031040134401c0c0f0f0f000d4070701080646200014442c054000303007016510130000e5000d11040c8074003404ca00c28500c59964501c058800c010150a007203c4541c881d04114000c1440c91954804894107000280098649040c4042d00c48002c0ca00000d402d81e08142c80300a01401a6070790744485028611442c0d4501400400688a095000c001040101c01a6042091a01403a009044800c2012940102045455080c5012809085504151500201c01203030489400129401c03c4007520300c240c818400b00c2e03440e5810030040d000380140550110300c3d06804a082c505004034a000c050040381000d26010303444d80003283c0b802c081160190000b40c0149200b0384903d50080c842c02d40b214803868664100324030ba60000b0100940607014 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 365942338 1250 365941088 365941123
    0x6070807030c0807030f0905040504031b030212041818030c0605070918020307080702010c050a05090f030303011701050f01031e0c09020d0c32030a0e010c26010602 72
    0x44804040c8a0304070070b03101551000300749407100110b1038040d02031349240505c08045024180b000c43c550420b441414840c03a00341d95585054520990030138035516007d03209408500a1041104100e1401c0c00148014000940502441c82103810b4840458130031a050825610701e00607101c020079401101040010b0304014005038986802c00d09448000c9158011075014501000c8042c4400040e40558030422154841c80e07101d0b59180c00890890341200c01079404100e00384000c00e07031f83d4440c1c0003400000d4005840031080407200340c00039207140c00c2644901001220040008030b591000c0c081e40e0740007548450f0b0304034254190b41e1603014030f0410100320706034540c13511000d00600c140c1e400b42c8402004016002c41d5141c4a000214014191002c6410040740261020304d032041d031440411101301550300e20641d8001403a0814101c10340c400703000d605016407602c50f0304c90340010a2040042e41d120f6511040d034500050200c000c0703240b06007484864410000c900400ca40f94011130210300b0034448421 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 365943588 1250 365942338 365942347
    0x20a0f141002070509040303051611030f0f0d060b04380f070b010306051608150402070c0e0c03101e03140304090e0d0201060f06020304060f12020706150b0405060708 73
    0x702245444030980c4141e40c0030464a041c0424541c0543c031583c0a5030300c1c400e03071406a0074408002c1e2213000c288800000b69510821004004544080140c2a4981005007a0345003090340c1e88504107036800c5403c450403280f00040c00b080100c2c51311140303483e050203540d0f9031007045040100010540058a1100c02203aa0009a40b4081450382049484080d070142d440c200650712401c1c1b40008241c2296117001610807050300003015402140360328400d445116103080c0311640d89007484080d400545040364958a0214085001581c9581d040d1142140307014a548a00d0003a84c4a00e42c2809a0b1001201e9426045100e50b1400381220f402c0030b5a030400580030b0b840c00c900703841d40c0c40c6110366482960300500d880c0042001c0040403500c0100c1a034158008d004540d29a440240821312500c250380160380308000c10040f15000381e25101c94040e03e07080c0781410f00e007207010080c2a0382c0030080403503100342c1d580c1c8d00d884001010940140640b880c018914240742c140030100e0407a10600300c018000103070218 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 365944838 1250 365943588 365943619
    0x304050114100b09040b1309060c112803020f030c0f070605120601270b0d1d0a030804020103291504060e0409050f0d0203070302190c060f022503020a0f14 68
    0x403c0e1140f05080000108035840003428004014101e00788007100080d4408034092442d000007880d8400500c0d51251208111401d151533401d10046070401c4095009090500810b18401e00c0600402c1c03901e00003a000c00005e801907641040c550790006020300405016070a01e922140b210554016400e082500b080ca9455150f01e0720f04c541c0c004000b800480714000072510410410150440064258040c00080c40d40f00c182c800051807039842d4503c075440243c518021901c03c6aa80b44c100c0c1c018180060203a240c454007840000d8440341c01c1c0101588074044000609001107050340711040c01c400c0504290811800611981000008902c11b6442d06c2115080c8030040c80385d0f0349864000c50884645010b00d00019440307070041e210030350141c091124503008440200124a0400c0e40c0f0110700d0800900381101a5401e24a042c020004c42c45a141e0500b00501c03480140824415030340d2801e9440d0b40f640c810072014509a4010b0802244010410000284070b6445480082c001702d5450b42d5054514 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 365946088 1250 365944838 365944849
    0x320a0b190905030a05121003020f10030e060a0603050f0a0302070b0a0e030d0c0b0c090102060406020c0309040e0c040617070521030409091e1208070201110304050114100b09040b 78
    0x112800390490100140b043c554a400100030301c841d21407103214410543d40d003140e4031811002440040e40282400000742b24600c0c2081480c40c0704103450030001802c80f40321007094a491001c0722203280c0142c1e60074040c800d0100400080011408203401407900b80b049a400a4030340da040d00c80c00c0090000070510b5442c65008403a500780b8001c02030225140403441c02e8008080140c6440c1c203442d80b82e07420022498014250080701e02c0044182c0003810f858990b561214025485402c1c0b1701418003041c071401466958501510500301c5d4680c00038141d850f900c804110448941c0c0d48083d4881d92450803002c91040c0104206084800885000035a03558080084001906107064112a8000041c0100300031f400355000c050034500401920ba1240640c6c00e254007038090b00c100280c114031589d28414842c41c810350405510000c14400880c010340201044080ba030000d65048640d070f51a00710303002005100485003607000b00c4216111a40520300f0b0349182c2c00707200b1003440600480d140c00c25001c06881c0c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 365947338 1250 365946088 365946101
    0x1e1f0c111b0f0a0503100516110706050306270105090703090c0506030a0912050a0f0c020603040222090321050c03010e0a060e0c280504051309320a0b19 67
    0x85d00361580c840c00f584800000f0b007021100d2084041e41075035010f11441c411420aa02500e00300c009003940da0505000795941c0e0401042c280c0d0080304650310103080c0c10200380400007005c607120a842554106810800381000040c007001c1094641413819021030b5215034130300200c1d01c0c00d565081c0c0c0c3e42c840f0003014018089480c4c018128048825000070840c0d0f100d40100f502c0415555640c403e0403066a0855883c1c1201901039800b090500102d0003602d0040c00302114081c0c07900c00464480341401211050b948000c100390040760f00c084400d82e01188540400704103020a0600b0802c5240401032005e00d80410301070000c8c103064500008454080542c8110003402d1407000c40c060a282c0243d00b034029038008103100000c040f04031101040340380301d1880700916111a441e05400c103810720086c07000a40300e0740c10b40c0c0c000c01d45032070700c050107c3c1c0405442c0c03846819035540500c00c8001d01291603111f503d40c082601207548040412800304588402081c0c00c803a6104240e2401006040620b001c0c0070b6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 365948588 1250 365947338 365947349
    0x21e040510030c06210213090510170613201806130b09060111150408030609090f0a0308090f06010e100e091e1f0c111b0f0a 55
    0x1510041c04501c402910890048a00c01d88084007001e442c1d680c115440300c91880d04a000c814006110300120826801a080d0050303082100c8402c00e95401391030b03007a564151011a260a400300040c0700fa48092828074441081180c02400d840c03c2c040c40d1010450200c080140412041140c031981340c46041042c81041da2008003100000c441074407458408c500195440b84c031903000b425507a00000b0303542c002c00b0b44a035001808000710355034490040d41c3e1083d682c0300340d940c58001c801c1002d840301d03440543e80e40203030700070000b080c1c4a15200060209000014241c140d07554010724004110410000350743c2c2110b40e040c80e0803442078803403082c0c00d8500601001100c0407801808000b1840421f104c01c500d00c0b07000342d06210a1025901d50305000303c5d50050312500c0c926000203001103e5080942003222052096400f1101d03052a04200c2c0328016401c58244a00307151901a98860154440030001110706140003400d08174580f00d40d002000b18000c1c0b0380c00e0041c11100700c54003883da41d1041074802000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 365949838 1250 365948588 365948591
    0x209060c100b0405070804210207030506090a0201031424040e030c01090c090c09231207060f0302030f0a1d150105041b0923040e0114060906060403021e04 68
    0x9500100006460b80a80c0765001d18505400a01018030a0207514001c0c2c0d0080906000310010403403200c143d0352040f0380c4406610854000100240c2c003004020700c034050b65030103016140040d10004069982a48603a482c00d0310407000e00c03c96065500e01845c01d00c0c0e0f054800446044001c021030080c1c5244c0c40e0f0060f050001085183c03489106401a515251180c100c680703001d6104c8004208030741d01040355000243d44070030309012802071000c1d210340841d00c010882001c010401e0002d0f0700c94110285a80f4960040d0780200080c0d070b00513203800c012541d1800d065055240a5480d6891124000d00d501c2000d91240710341240707516401c611040c0f4000c80c0c02a11030300c8014600b1440303062020f108050040d0714010450f48410b201c2c015800c20f40c407071a918910001c0c0f82001c1c464100c8113480300c10034151040b4a403890f5030340c4e1380d00c81c021002ca003c8001040030300d0003200b5000c64020040440d0300500941080021030742c0d074081114180c903812502e886180709661f0550004032040c050035604075 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 365951088 1250 365949838 365949853
    0x50403030906030f1e0f20070615050a0803190207060507110a050316080f07061421070c060506121f0f0e0601171204090b12011104080c190303030209060c 68
    0x103175034026034403254500c0c01c00e01181c4d0301c9045101d9400d40d240d1800240780c45c28041400014502d822a010007820314030740000700c9071504001410745103d50300c440e00c154000109100c0c1004454078083d03410381240040c20300d661402d200a00f5503c42e0400040003c0100e16905c803240d40e40c1d420aa02500016040390020a0b68105002c2003050501841c030b039510071100740b10400100050b0040940b11640d0f146256100d178200125000c2e08440c00d00c81e441142c1c5013001c030ba88046480c4c2c9078483c20041e40e8a115484044c107089080b148060300070350080317451020f0601d8822001801034490541607042405411802c45941c0c02003482442e44008581006d03080150042c0000700103040e901d0203861011000c0d0600c100c40d64038031101002441c0000300f8001045404401d9000d41054100540b40113850b012440f41b0501f10b0b0103a400c03080804501003811301c6000e50421403a5000c4030240c98046900c24546139002d406401803100030105900001c0c1f008007a101c5c0c40c2604c5982c4c510008585a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 365952338 1250 365951088 365951141
    0x2190f05060903041e0f0e0405120a0203090f0f0904030809010e0304030f0b01080601120b13080d06030c05030a0503070b0a06050a060801030209370b0307081b01050403030906030f 79
    0xd030741c0035104030011030300790f13440e4805001c00c0085e0340c07012100850b243c0800c1e1450440c1c4000080c500800540b01707400f5410001ca1290f040c0d900900c090b01c0c075507000d183e9403070540303041145151080440b01d020ba40300da246545140c4442411a07006501414111115501c164409014019081300c42e01140000700d0004104110b125030018680e10a1040b14126a00e0780c00c2d0942d10b08003482903480e440c540340c1a800c0412400300c416604010003003900e81c406a00f64450340e030700f40d00024800c442c8954a00b010018030a4005610340038140c01c4025100b07005290b298156070b4002c884001c3d21000700c82e4042428140c0c0d0741c1c010f000034000545030160b40c42c0e8a40000d00018007d200690141901c24001448030f142c098000c4664884045201c5210454118401c0303034000b1100c0841800e80e41d21100310042c1d0742080340304010701074407006141070025880142e000d804c181c0700060600c4030a0205000281e04200c030b07a42660707218500040c00300e40010044010307044101d81000c1c0c003260312071094903 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 365953588 1250 365952338 365952343
    0x120915110c061503120f0f030f160206090d0513050d050d12050403050706180b01090f1a091b04030c140910050f04020a09091103060112020a02190f050609 68
    0x400c1d00154252407107552405603108500070960451545500a5044510780c29a600d01800c030035030704c12000e10300b4800308601c0381e90b5540c000c0c0e505208d022107107810050b01d00090340b5080240c0e03c45202605481c18040c96a03a0384944140d81d0400307024011804c0c44441c4140646000100700003804505110200d0030a15101c001442400c0000f80013003104640201e41c41c00344030b014039499610580303420a02d1311550002e00e5085890710f8043c51484602000c50042d8000c54040c10000000190035810150040101c4812020f4410701d81d00444840c803441d590b2101c0154001d110303030201014207001d80c042d10350600c51078000404c06000d40c071010800400305164200402c1c0282c4011840392500c6005801643c481e1040c15402030100122408505040e0003800000b00541081c078209130702c0303104410030744020720b5890b0300003800441001a203690200404851580300c143c114640851000c2c000d4880092030301d4901e01080004401080006070300058003201e4004003a544030381084070f04581c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 365954838 1250 365953588 365953597
    0x6030a050f2d072102090a0504110313210806180f07050a020a0606150e0d050c0402090d02040f060e01080102040f090b03070803030c1309060612091511 67
    0x540018000300000c610394062100a15424480b41850414100a2500b501032140c0241034608129040102e1204806210703120b99080058507000b6844800007403e2015040040d40074601c500c0c01c12243c880310803030100031a0303040443c44207011100d8a040c10075005218400340708140c00c1ea0f00000b011240c5a02000c602d010340d0084500503283d25201c0c030985191b0340c0c2a140340351401c21180204011602403001081146c1d0240151200c0410a848035022078501d607000340010031005800310750459015401f0146401e044640c41d403c951142c90b9140e4403101030701d0440c0150f60015550040c0d5440c6041c2054040d4000c205122240d1301c02801d40150105104425104584100101e90020107009036019122040b042c0c004043c034001030040900604c2c140c0607014061000c3c044ac0a00c001c2c0000c600c02c0b0021803520b6a030390350086007040132150380e6100702c180910300300c0d043c0700c1d01d13520a008039007444014002003464045420805c0210600d01110f000d51854a058442c08964000150 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 365956088 1250 365954838 365954851
    0xc070e0115030605031009030e130905060109020708070b0402040b09090c0f010813030c020607080f041403121204020f060d06081504050a03050a034214010309020f06030a05 76
    0x80141c0c032000d400368181d4105001d000da15802c090030b031524801d0150f10016140e802461300c0030f03400e078040000c41c00c0540c8117820444203684440c004000e20004022050040507103220461400810741c451143c5400303060801084440480d01050540d031707442d00204035000c0c0090400c0c80508100e851155a00290045076010303aa45040f40800c540c05201c13000d00c5406800e910010305503480c3c0e000c640d05110344030101d900160034000d040200b0802c80251981c450341054a681d0740e410f091032014121041e1804a20961225803582616000382c010b0b5160b98415143c0c4405070b84980c40041c12850000003d280c0040e000300d268150000303036802800c1140c00d001c0561f65050110b04840329450421107001e07040798072190800e80081e100700014913402400f4540016040750380066030030502e0030a19800c060000142c07404030b000c0c01d00b00d01d40044d124880740c00f1004501c3e18200000511310502000d051654a250410564032502040c0300c5103c0c00070310580e628644102800020035055810 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 365957338 1250 365956088 365956109
    0x210105160e030109020a120f0f0c030b010f03050703060c050d14160306050603010e071218030e06030403080f06040f092306040b0a020304080c0d0c02040c141b030c070e01 75
    0xc1ca8a80c101842036284403600542007100300e0b07081c001051442640c03124211003001c0d05c010390001182e0b201c0f0001010504c1031041400c2c4a280d81131064501c1c0043c2c01024440f101c3ca481080001c900042c007030b080301d84c030000129000c18581c8058a4500030310b01c00c40000360a010400c4071907565060b08a00c1041040301002086102050440031900c4900885400410800061003581003410110341d000d402450b14041c820b0342c0c000300500b9141070949a08203040700e041418101078110850021503007056510700d08602d03081d1401000c080c07014009481c41c0b5205004501d080d140e5401c211030803c0306450500c5120b9161070814140380b801230480060b4070f1000d03820300040b00003040c054003960304411306001340d0f261648000001e510260080300c80300d50802c10039142c2581405102d054080e1070700d60103803012081c01400142e505110203101082502e0344080321500300070f4140c4000f24035044041d40892150803e082c91403184d00300c040858030400e900081c102d98800c42c024142d4800800 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 365958588 1250 365957338 365957357
    0x501330c031115090715020309040b031e07050109060807020a0609051603050304051c020105190c0204140a0c180b03133306060836010c09170c21010516 67
    0x82a48105802d00c46c03000058108101198603460660016070200c0c0c1c00400313454004082c940141070a500400b0020b0554000d17003400c003ca507170052581d000a1005091035200e40c41c025000a407140b01c054401001980d840080c82d0a102c1c08101c02981c0e0a95403000441058407410015a203030030038850a446204940a03040070340000700091303444154103840d1107040241c20341039020014281028882013000b20b0507403a000d03079258095a191114803516903602814401500310655580810a1003030103854240e100e0684044824201101c40000d59035841e070b1103c2c5410100300c0b08000700648020900130b80c00882a1304e00505040a200001d4160308200d000c01c0701505480b850721411010512120000c0c4080d640c54241a51949a422020201603000200010440c404100c14803050703640303c041100094004070740c2000b1f0f111502d02402d00004050305199242005940e081c000e03803100114801c800310711800c424070820f01c00000d011510b495516201400115800718000505080 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 365959838 1250 365958588 365958599
    0xe060a171806090a24150b0702041d0309010c030513060f110703050312070201020c010e011e150303030b01092414090d061508100501330c0311150907 66
    0x940315011355000c03a44004501c01ca241c0c2c005866620311160507441e443c0c5130700c03020802e080c02200014024981d1200d03141e0120b801808102c849211035401041c02000350700429120020560704403980034608404041a145800c84080c0600500c00e075201c1c44224020880d15000310727005542c000140d03503190416072880022a684ca80b030b0b1002820720741041240c6001c0040c10b5103025442126800094508a1404409400c40b41e000114409507559181e61b000e40b440c0ea44041320740650800c0043c0490300c000c20140c00e104843d03110040925030740b40d1407c1c440303034040e4040703e00a00e69080c1c017a40d80c1056002c64440d51307020072401000206a10043c1c140c0e20b03103100035902412000760400c00502e80c20b03690000200341c00c03d81742c1540400040002a036800400030740c07122900310700340402c45524000a40710546080400d4000491060382140c01d01150700721900c0361640545403000d03c105082c18151100d04404004804a015040011090381102201640260b40d14401c1f00e08855440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 365961088 1250 365959838 365959843
    0x60a120c06110307080403020f01090308070507080d0306030201270f090207020f0405040b1609090c030219020706020a081315020102120702010c120515040603032106060e060a17180609 81
    0x205005245c0c440a00050016080502d49103100502c1030400845071912a12841c0050b04201800c41d0240d106c1541400050000d01c0850702c644014241800075504546c0041d20803442004060420580741d012584620f42d4082164000c102880401007201d4035116503401030350018405900070000d80158203c0e5041600c1401e12440e00b103018880a030700c07800d2491500d0003620944800b004130022010072841c03400e2098581e048041d4a006a0356040300c2c929481c100000008503080d074100342c604000346900804c8011166901c80c0c4015541d0000c00514110901c0750380003118144024941d14540e5501580142401d0030900e06004003607488100c228203803041c40c019140040d075440d030b0b181700290590700550341110a0449080308090400b02203411201107620580c001b4880e00c00b00210039494016046907d11007810031301810b82000130142c07011a0058401d406440c00144880c0058821102420507201c41c04442c041e608001426101c60328410303400d52914022a4081402d11400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 365962338 1250 365961088 365961097
    0x12060a11130303080405150117070b0307021f0e010207030f03051005010e01050f070219030228060e01120c120b1c0305090a1701051e06031005060a120c061103 70
    0x55441101c030315801c6a0342122034000c003a204a519108000074030324148043d0311403a0103481c100015211601030005003038504034050f408410403980400a00c05030a9010400a01d0403241010311030f607014080e080b00000700211030100515520104c1c90008040e0302c40c40943c55402c1903501807007980c03101104941e511246104042c0131035914507884504d94040c401401061004501d19804c10f0400e0700030426612500c164642c14407881c40b004d0003140760000e070080d0500340d0359603090031080a24000d9004205a8041d0000f8028000128480d6a10682d5219844450540c0510444007140000340c102e550002e01303049290700b040400001c500b02420b42901015100521161051854500b51036a51041101e56082410880003203194100d081107240c0324482d032000020b842c40e200c1041c0d4a40038420b0301c076180c020044410300c40c8580c1c00041c1c40f5101234004400044070344420303002841071181a401064894500c0340c80000b8031850512040031260306444651207034183d5004140c0360b108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 365963588 1250 365962338 365962357
    0x2040903051201060e040e0c360405071a1e070c36110f0c010608030406020a060b040605090f0702071802120106080c030c0901030902041e060f180b0a0512060a11 71
    0x2100295090800014915061324861b082080601d0302804580c48111081114142d40c2075001c20010401104034040e000c0c0c1c283c980001d37085c00c005031034039a00e9100180038080001c3c1d0001180c2103050103586010350004080074601e04c006110f8125140458400501480594071402010862440c9841c020b2042c0018805556460240740c005084480d4101d000401c100e90740e200804184d41604000903c058040d0341c00070443d52007140340c66800d4070f9265581c2c0d8001c5040c910104082c1d00c4645d20160803203283c140e504a55960540d08a150902075413100c031000d5003080303000c4016240c07540201043c2101d0307582e096050f03880b0041540c6140080d135500da0f004208100046540456401503d8031240500d00460702c0000750300010107039092024800703142c001c0d000030070240c02082d1081c42c00628000d1000001c2c2450a140c3c00c4950480740a9050480c1e1520b00c5015180e44c3c0d10004c0c0045c10b07000f0003410950070002e010a580b0704080307d00710152454101a252605126010307034220f0b0b132 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 365964838 1250 365963588 365963599
    0x4050c031002040828171201081207030e03160f05010206090c090601050d0b040617010b100509040b0102010e07031b0e010308040510032306030d1b02040903051201060e040e0c 77
    0x1601c4c03140c101c0c03441c4161000804000b92000c0c3c0c000241b0a03040441c03182c01c00100c8503100e4104000b81e103042c05042c0d10001e00d96000c94a54405660194152414583c06060841481c8030540c0442e0504e40006900c0105170115040410584081200c050a03160280e0860b451343e038034200d415036641404030f4242d0b4440f07200f2000a4096105000820344154800c0010840110100100382541c0698000a1103250b44002561104c0e00234820014040e00c01c94909803011640d9602402d540301c1c01c00d2990040d92a5034000151b0b9000f50490407814042d9011101402d0307480c02d10001c0d08050b000801c803501c18208000800714402d009140c1030320b400415191407d40342000700548a0610788040d814191560030a8007101c0540700d4108030150807181074a82c528100741098204942520030b4020b00059000d080e10701c0203051444203195505580029407030f400c030300f02070720103008a0000c00910812a8008501d95600c20301c40c0d00c18500640d802e009440041281d140c4484403081142d400c403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 365966088 1250 365964838 365964853
    0xa030f180f050a320c0109030605090a050604080919062705031e16030c030204090501021204300c030e24130e01030c031403090904050c0310020408 65
    0x19545091054014807420881c1c1e070310405541d40e51070858652292005040040e2591564030200020403074804c0c50030005041ca800d24000060003280c858000030f00313650b41d540d0005d114810100540034042d6000011100380e41b41626120880317500500708140524100c0c2c1040400040504003401a9004ca4a031804414402070010309040c2ca00e09c080c80500d2004007001520342ca060000e403001103d0304d4010b84404140020191502c5400c81703011541250802007003001c00e1003141580300340c95044030081001682420543d000e4018013074181e102e02020800d002c00c00043d402c4c59004210b50103682c94124001201108034600740010940c0400c4030803065200091091141d140100d20082c024603d149070580d045420401800b58000c24000000e51215449031090144d4018140d1000c0c0c0c00940d8159981d002e150300c40ca120007840240c07900d0104503410018015142c10b28000b400c004554585410312070f07a204510b0000380e00900030074a0600d007000f10b6000701c41c1031701c481310020402d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 365967338 1250 365966088 365966093
    0x118090b1908060f06010e1203030901110309070915051011010506030c0f010509010315080106060809030301080a0f0510050a020304031211191b030807020d05070506040b0408070609080a030f18 85
    0x31820700178031540c100000183c02d1501c55462500ca025420710b02d030700031626440c3c005075082c2103643e440d469801034841481001040c440004000c41502d107040130100e007030a00d094400e0101411601701d140d20038142801000602c1d441000c40f050010303000c0080c01030380c0b0340c0c0342416118402c00c5d001a8000455040c845529405580242684a01803400298050401c10050b203c1c81403908045201e9444900070810f041d8818603d81e00812524091413555252140c00c0e55148942c0303500a1101040c001c82c28140030003400b24122030f00701040700344003e142009a2200941c0102d6048010940d40800032916985510030b1221000b00304000e6490b041d4200c2403443c0f8140496100001c00c0202e00c00410611070a2045482c401d20075100c00f829800e00084c041c2c2403803211003090040000c10b02004001c01c100041c8240c2094104034562401e44860524220390b00c1602c201800a42c103045018081001d1100140751180041c1c2e02045045015107000d002d98103482c182e07031003100c0400d001002 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 365968588 1250 365967338 365967361
    0x504030906170a0e030706050103140d020105010b040303141b0307030f1b02040b1201020711010905010c030c120903050a0f020a05040b090103020f061c0e06160813020118090b190806 80
    0x40d0b000d0b404c1d0441c1d0074103803143e9800341a04e000342c1044600210346400c038010b1810400101c04183c1d002d000a10080d81001c103040e00500540c40054200401180b002909101c014129481c503520b54080525049591182554070b03484030030300700c0000d50080c20b80e49035203100740074210126140c0c940746582c0003541e4081002401c41d041d856580130003c001c00609109003440203103203003481040c90303091708000c2d10b0000d414880700b81d00050501c45600c240c4800a6402400c00d03803400e6209842c403040b200e41e600f00701c92440003038000a082d4440d0b4070b550411b00100000c51070030f09108840d0500b0042c0c443d424002540d8038100006c1c1c104203e03a00500042c588842c55251070b180c050111070408400450340000c091500c5520300000e65500c04003014100305002483d070208644905c001454003214001740001002080c003264108140c407200116032150001c90b06c02c0100341032420140740c8070b0982000a02c2c403010014072654042c603410600380010349011040300c82002c040e200d04d907544c005000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 365969838 1250 365968588 365968601
    0x10914100e011b0609021302040e0f1f0e090c03160303050903010f02040e010f0e06281509080105090d020c01050f07170901020c0307030b190f0f0504030906170a 71
    0x14140f03d6500e4024035119860100780101d20700544000c115001c450052040380c4003940c02d450003290042000307012601c03e5080c02a00300ba0b898480c1c42c00b0b079403103030040410403264505020380c4801148001855009480e2254012000070040d550310024480802d50303196100300329090302c003078490002c2010034041d41c003502220038060000b00c0d4059001ca00b4508907441500312940c40800131006000c007140000d4004043c003c0703240b001c501802c0810008500d51020f0400740e440b680014551400440c0c0c00b840003004007600030b011000c40080450140041c1814026960b096103401c0004103440800a00c10344400d0042d005007000200d800c0044907550f001e5030309124040340030402c000005040c941a044071912451aa68035a03042c44d00083c02e082d507100d00507100b6400007005002003402c030507001340c1000240100e503105003200304071800a00b81c1c0300d0030000503500d0010320042046154012a10940c4280c1c1c86650310390f202c40c3c044d94444034500c9204011b0280d100000c004504a9001e00d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 365971088 1250 365969838 365969867
    0x901090f142e0801020d0915020909011809050a20030a150c02031e0a0e010518010f1704110906010801061b0204110c070e0a020702090f10051008010501091410 70
    0x410b01035154841c01d42a80d104c0d43e80c82d0f081e1a600d00d483c50601507940070702c20201c0507040084d8030341040800044c25464041c01f5200d41c1c198402c6c3e050b00c0c1c641b40b0703611420480703030b0010a507440e0400605001e66404040b820581d0140303e01d10031060b041c43d0114802c600154001b12804001028004400091518199180542c80200009041034454880c4842c1d00f800c0100e50a070354060000008044a01003030507281071010a012500d038000d41c0c1c0d818400b0a06080c0381081d0922046c2d1401c5aa01001068039003008602c40f05100c2803250342951520590415110603806440c0c400c01100e03103a03c24480ca80000700c00b07851010040300f00d16294103401e40004c101240c0000608103401e203903481072044c000d03d41e002c404200000d95142e240b1a0b444206104218186203054021500000008041c010031401c00000a040c10030540d1400010704400f40450303070640c40c0b5280280031001c0c00e0090501160100d94001902d0307003107000392480315002901030b8a401e8412070b0103940038210081c0a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 365972338 1250 365971088 365971171
    0x10c0609020d0f241a040911040603080d0506060f0d050c04031a180c0a0b030c1b0a031d1516060c0309021f0e060708090901090f14 58
    0x7036201143c03180001c180058000c46801d1016403900042d0002031400050b04213126007007503c0b140d0041074032503030910070000030707500802d0300c2880d850030907101c05c080740c0c03110750041c80c02001109001c0504007601d408048524100510340f100030070400710b8000c0c00140a1303007040800204400f130301c42c2c0e080a50000303071415901e824280c0701e1ba502c0c0c41c40000380482c4a04081c031070040249000000114070340c00d203000406030459a80440203d011885640a80103407068004003007100d51000004a51090507844401a00c103400741e2840c0c1d880f12900b81d0f095000600030304603aa54005c0090a081d40c4280c001c0c24102e88410b00301c0b00741c40c103400c821200740b902d0303070000814008a025800b9120b403084440d500020140d01d6031040080136040c500c140c04c160300e003901c0703800a4190480960340e8a42030886480d6100c44003450300010912420324041c0c0c02580c0840002680c1c40342e50411030000e07030441d806000f1103141d20790107000c44904542d60403c040d100140320b0240d040205031441c003c42c02024 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 365973588 1250 365972338 365972359
    0xe070815011509050405150906090105031b01090504020d06150311120402041401080d0f03050c18030a080d0603060b040e0706030c020c09010305030d0c080709031e0501050f0f06030705010c060902 86
    0x1c0c1c1101c80403587e440b001c04280d055040c0c00c0c60300c41a00c1d03501280843d00c08506505000100e44e0328007042907070f6040c0c105404a0059141c3c00b40443d04000d1038010025566141c40c0c20300380780a080148200802060078081003030b111801b80c064041c10402d0384084138107086142d91014403c1c803001d04140d802075560150070343d60782c1c45c2c042c51a020b0038211000780a20500000d00400004a8007005410503180400b800b5841e1010812a90301d11620f403075107650310041100003030409020100080c2500000140e81511682035001101104e010300390800181c146841408241c540f88401e05c42e49410900c4c040c44028000ea00c00242a00684104d8280038218030101e17003080d41c00e0f001500c0a0b440814000d504c40024092000c4210b40b030b00e80307400141031080025220000c14000104403404c0c000000d8048101030744070316819504a0001c2c041d0b828801e601000020007903410001100c80c00000072494100061308004449069564404104003900d03014001c1c1810002264000c00645 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 365974838 1250 365973588 365973599
    0x16031505280608061503031602030708030c011505010906050702040507030b03100b150c060c070807060c050a030b090705090d06020904090b070f170402010c06110a030e070815011509 80
    0x515041c00344140407400201542480c080e07500d0074000070704000b21640d400210401d2a10003106860b01c03d4100c0383d68601c5400f40f84006402c006071908105041e02c070100c1d140c5140c030780541000020071402c080fa0f500301a1075100440748281507003c1d8102113a4200700381e03c014285607120303e030b1240031031070006901a03086c1c000a091010549440800c19100d03403168096240078680f10300d4002039540b04c0d52a10000d08099600c8e4040100030b52100c580228400c0300340800c00c803c403450340307500801c01c12514000010151171504080c42402c002458984110454188441a1400b034038054540f9418000310404019111b01000000c50380250203110301655500c0311301500c0159440b940703014902d450403550041508030f1000d4001c081008804121800840510310503810503020318100003464a42d082200103071405188104001c0c80028828408603459445031021819010a44520300e0381c0350050350b41e031050740030191a24481d41d4010800e010034041e00081c41e81c0c1d00d0030b00840300c0761743e075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 365976088 1250 365974838 365974891
    0x4020408010f0f06050f010503040f120306080f1b0d020d0213022701080406181a0a0e16060e01020f070906031a04120e040b0604031416031505 63
    0x168410300180c0c0d181d0802c1c0710164120701a07080b040100200c00c0044510702000500903400800310541801400400310f018480002c6c0c250b07058030740001400202240c8200010000e05851242c91068081d00c15440700e60780001c40c0c1250340010b01c1c01c10050b03109010381040100022080c040b40c1c001440d07031a17040140c40e48210b0600341b1800300401a00d4117185a000340007003003060741d00516030342d01c03080c200e090342c1e0840c40190308282c001a000031001e015600a42e07d10305e040101911108054072200000b01c06a510307244101c005174818030503070040c000020754690420801280300000910203000c414440c40ca80c40f8076070014812940308203c5102c006040c00c0c0c580c2c020340140d60725100d060042c000c0c40940b100b81c100109130b4000326031078540c0303c40c00982003000310902005070644001c8215522600f10000307106004201c5540d81e5600d00c2e04042c0f20444a81c1124540035440060815150b83e605080c11079412801c028241062806030348020440105201c2000501c00054440b00118 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 365977338 1250 365976088 365976097
    0x41d01080118061d0f0601060f0c320105090f0d02070e06100212030a06060207062109230604020f01020a03080406051b03070f021b0f040e010209060c10050c07020907120b0402 77
    0x41e0090006c40d41003020080c640440e5141c40340030b0020f00c0d4100d40000b141d8001c800314190307144005d00105525084101e0541401d0040d4100540c01d081c140f150714000401c80d0000d900901085a0f1400c0451400381e171900403510611000ca1503420000720242800c4859122201181c415070310750281814050704150000d48c0c8410901c0d6640f0030a01145404010160191080b030405014150f041d0a0300f90030150300b00d010f5000395889028100c100911145829203092040c4414413806803001c1d40396980740012076081e803003410403e5002c651540089401910300b80c250b42e42d5003080c0d86030340b1144050300740503042c442e0720b411401c40c00000751500c0e8041c5000d042603940303e880300700fa190340082c40c2a1491001c2609041e88203c140300c50f40d156002c00f050480190b4020606c2c0e100c3e080c413140240a0f40b000b0603045a0000b4006840d1035011960003910145c0e40010401c1e41c40c0d488290010303024245009400680f001c021a4000d070050a1907016500c5030100402d40d51380190109060b40c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 365978588 1250 365977338 365977363
    0x90103030c050c0402120105010f0201140c0d11030601050f1c05010e0609090d09090b01091503020c0d0503011d0a1b080106030c0e060d0506011202041d01080118061d 73
    0x140c00503440304210b030501c002c00b0480030464040d8208080842c1d8500c46000c18802d450510030303a420346c0c07c0010b00070b401000300c15a00040003401e40c0362410004640d40d0091007042c00280c0b40c0101c1440041804065031b0040106079101e030304240000c0d00e03c1280c0d92140c2c0c0c3d9510a2420400e41c00b400511500601d030180a0540310104141020300520400000203840004240c024a1609411540c004070540032204110400704044420800607100900540c010305622182c2c0706444d0b120b1038164000301000e600d05002c580b68540a031808840c940400e0241c8501c81801c07817904006110044a4a070b0042c109840003e601c0e80203a0455005141d840d01c1503000c0b8292000401c83c0b17a0305071180d56603e660604252080a6240b800103030248100b000031904180e4544c08500c41da44100309030130310603900100455961303480d0042c41090b80001c00c1c40784c490380101800030540c0c403010b0246030390702140b0341031300620702c2590381c1c50801402c0020109481c284501042e0310300a8403c0000440080 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 365979838 1250 365978588 365978597
    0x170f03010801090b0f090a03080a0f020c0601140d0f0f080d0c08041101030c1b08120103060e01180201170a0209060a0801030b06010c0215031009060608090c011d041a09010303 77
    0x11444ca44070f105982c00801c100c402c843c006017000822800498840c903500e6041c64001a1951380b0540074000700348990007045881c2c07011070005000300c1c1c006022816629044030300c0c00c44a40010402042d000011801001d00c400f0250701d6000901c09040510030794820704070709040c05039035181c00d802c0701e40c0416001e0001d00d074041403005000340490310040400080c038083c4901c40003c4805050310446030000c10f55507940254001c107000508040d504451f18044a02c5a030f541e59080940c00381c8009072000b4142c0d481e002010003060400030013000c9180c1d040c0c42d817648170301c1500744601507201c0040510000a4017001207188070f0795024000c1008191503210090a541103080000e00d464008000d1414020f01605201c00351b41da070440f040c014001a00c00c00d0340d0b6038031700c108400071a255a006200d000c0c2404008034004c0c0c0c20407980380c880e40700c100c22140f140d801c920044481d082c06d2450240609051124401e182c00c0c10b0b044480e0501d028031214408005020104a98a600340e00540c000b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 365981088 1250 365979838 365979851
    0x204020d09060e1923061e01080705011d040b0301180b0c0708030f1b0307110d030c09060c0f0b1005010f08270a0506070801051003020c030403170f03010801 69
    0x1c0c5922030815407900200c010b050328015072440d018000308120000d042d1440503140b000710803171316100154151110805403005806c240d458420b8907104200710400c1003908100200702c001c0001340800480d08140d56861850144251524031000303061215900036403500c0d42c9000940303090103a04039180b5000c0520806100d2070070002c50540001d44030110080e002c105034030228103140b003901e8000c441c40010301100e840e140000e1049140700400ba4005580101c02c01040303e0b040b004100c086654401a98100d00e85000c0490842c0e204282e90004201b00d0300c424000340b44500c02140c01070b0f1084143d502c400711940c4850308012401c03904c0000e1012911814006941d0103c0b1015a529040c10303e00e03000c0c04d04915a4400783c3c14250301e4080ca0082144030211020100031a00705944c0200945103a414010b0004110b10801d004182c001d4031603140c0b60b603009120b03108135140086102c0285d8146400c642d10300d43d41249071150700305d074101309108a008561031f0000843c000e0070400000a40d0b03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 365982338 1250 365981088 365981093
    0xd0e0d29250908070501050309030c0708030904180201080a021305030a06020915120103020d03140d0b120c0105180d1a040201020115050609120f030c0627031204030c0204020d09 78
    0x8036100000d190003040b40b1040c040000720300000e42501036800c2401c01584a40c0c4001a143c6107004201844205201c2c0c8440041c84c10b802100810031504281c40074842000e03800700301d440000104000a0001e861440003c44541459010b0070040300300405c1e4444155031400001c0c901031201d001500e4459001484401038039040c075a4000710001180c0240c20448101e040c1032a03000140f00c041e0040301118200000c062003504115203000000c0c06080e00c915010214000600c001a003450054034650711b040d811001c00034400b2004081690b4052500c00388030480007200500b01c50003500306280131034402c0010491100c1943d00145440b00e141c0b2858540002801c1d5190000c0c249009210050144920b48860301240e1203c0c1c01680c480301c071807040701706952900c4801000342a02e4040840d1351610010b0115a16004201e02c2c8626046010615075103401c0700c0c01010022210f0b801000314070f00e8040d281006581c05030217402c00c0b492034030340e0340c0103c3d09a9200002882c40c4030750710340d0081d08 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 365983588 1250 365982338 365982391
    0x904060b0406061e030501150c06110301030818060c0c30030705010b060a090e10051e03010b030f06180f010906050106110705030c011202040906030b010303020d0e0d29 74
    0x22204d0b81c9014010381d40b4021f48520701459500725403080220350400344081c003442d034021501003189d207140b06540c0d45e52030810030156003010711140d80380c0c02a03166400052416601b43c2d20380a90f010701a1410f80744440400000c40700c000100300004038601c1d40c684031b50641340350b1990001000405540c4d25801868420300712903540d901c25201c3c00d8284000000f4543c0484480240d0f4100000401551139403000d2050580150340143c1d400740003440010030010041441c180d88940580c001c0c4090311507001011b444428840c4c80c2c0710558800130025000124040080750f00b0240c510030354400038042481503096031811442600d00d9500e400041145641c8000c080b0b01000002001e880d402d401e1a00007070300c40e50b9a07402c190400c000d447d0f24000b60889a0304a0b1b0042c0031141d400c028455503031915101640303003488294058000c500111400e00c0c010160a0304421000341102000d062580d901c601c5400e4130942010454401e0641028500146041e075014030380403050000510240c06c610076 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 365984838 1250 365983588 365983637
    0x40614030d1d01031d0703050d0311120621030c03030717070c111309150501050a0803251e0c06050408060c0f070510060603050615090904060b040606 66
    0x2042190341075104401030b46180d003588180c40246004544100420b40301501c0001c80014800640201c0c2c50000c10043c000400b242042000e0301d0520840081d1b0344d128480c0c1c0200603503103007500380d040001902032038500c0701003011400d2800700350703403c1c1102030300c0915540240c401e216043c1d00000c1809049500001204100c04000030b00603082d24040c0780080010030060030042291080c1825a0525514a0040850002510030400c0100e0a504188050442054408042500c2c100002c01d0a08083c1030484c00c0d1444440158640324a004c0e0b4101d46103050001c0400484080340d2240004002c24010380d11000340346000300b01e811072403c0070034043c078040c1d0260061000400c400c00a8040210307440e540040c89007111500c5040c0c170202d864041c407a41c907004100e4024a10f4260880b03113658885c00c02e4801690341008541d41e0034040c800000820001c40c00d1007441030061309054035010049a0b4041c0c8540004200a1400000b080503103000787c0046021550a02642043d1100c040880c0e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 365986088 1250 365984838 365984863
    0xd0204030c1d100506122805100905040203070b090315190f02090a030b090a0501020a090602010f02071e0201031401080a050c0d030801030209040807080a0908010e07080303131104061403 82
    0x408111301e030600084075445640701e40d42400034000c00090024890101001503038400d01e02180200d202181c0c0c0318000d0108a903000c4901203114804a074101c103c1c031800d8030866019000300b012900f8401c130b0440c650080300289a00d031098107100c0c8450180c45070158051065204400030300c1ca04540740400b980d501c500710506d9a4810f00185500f0b40c0c99041d000e08590b08240c1209c031944540038460b003410040c000240c0107600003d100781c0d0156200302d078442222510760003000b175078a1040079001a84600c1c0d4010780241102c1180424004c030110810465501c1410b001070304c0b032114120010004001d80c441e020603009040c8010a20400f44000000144101e80d540c1e0700031040d940c040d202e104180406405510044009000c0140c203404845d2841d42100300292190015a002040a900e07809164040c0d402c1c01884118040000f81c072100f5203100c5009503085039211040145ca070400600155030800005015107126100c91150a01a003800c981306100e0001c400d092501d02082d03008079 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 365987338 1250 365986088 365986111
    0x14060a050c030117030706091406130f03050a030b12010c0f0e090a02091201020d06141e060f040515040314120307030902120d0c03020d05040b0904020d0204030c1d 72
    0x70080d4209500c01201d0655201000000c250041c0d44105480c5018400008080074900301000c000e01c0211512524a410031008907003260b03941903031148030010340d00c0d401070041d003004200300c002900440103006120301e50b10b400030312944810001390100303065800c0c06002d0f0755902c440410341c642c4140762000e50916802d01942050b072079000710700316000062184141030b5003c5816000756030780c854004500080180299258041514200002c01d11403081c40510900c0c2e41031844d0900f8602e846111909403056408070003815101401241d6000403e10b584c40030040002007140c0d603d981c80c0c100f21840c200c01460302e5038103610300004140c6503000840c009502c110b40d0005042d03580c40449601a03a146030110b031805981c40810f02d16040c07618254583d0059048074040103902452140ba0035005e81d0840354140000c00081d901440355004211400d0001c100c100c100c1e007802e400904011101c441e005150994946440d00e111a80d40c07c11441003648041d4000c0b004601130720030360043e0f05c5000c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 365988588 1250 365987338 365987341
    0x120b01030213120f02121614010c060e030408012306040e030a03090809090106030f050601082e0b030907060f1d1e03030301080a05071a030c1e0714060a05 68
    0x803807001c8a0b114800e05090040481080007009030740b2a044820075400381014a0f50882c0c81c52450b100c020301d024a12140680800000300b0b0b1820050080b40340c1e8068440859200c065141e0401401c5c850a44921a110401001407520341c00d201d040d1003200c581ea8072241085072a901134400010240c2040e1040e810308041c2e1200314004022204c8141240c10000307200006890044018001d08004551081c07040c0d00008071250184c00c600c050340e41c07841042005641c2c000040da03a041d015106100c82c8940030b509082d414030000d999444403083c00110030802c5940d0201405503900440c1d85828503000740c0000c10013583c200c0c00c8528009810704004280750110000701414112050a061041800c2001c0075480020400410440c54020f01505d80e00d40c0c5465446940b00d0b0300c46021140340c03048110006000603030901546000150140041c0b45886446107039030107810010200d594800d0340300210f292100040014010075119642d00c1003255003044c45203040c000020304503503044e8141f030b0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 365989838 1250 365988588 365988607
    0x650906060415080a091b03030f1701090216080301080706110d0e01050d0e07080714090606030106080711070303090f060503090703120908010908030a060f032d050d120b010302 77
    0x84105030b811058588000c80340d070344c5040e104c00b601503034002404040c1c1c04c80803004140141409501a0303400b9480701c1ea6410810001202e240c401c406001c0c41011417040180704001da580c00400181c0400319040000302101c1e201d05510b80d000382c0c032031545988401410880c66070840d03886500500502c0103445d000540b001d01071701c49220059514100940050341462120140d0300000151031a0700842e0f02980c0c59181050740c4a51782d00654070100381c01040d10655181c00240140305010180409040d0b03403070130f44107883c185005020707038050100030b01003c0e1000004100041c01140a44d4a0101c1e032880c24850050280300750300314004005041007000011040007179544101da0740300c0103150203000d4044040715040416080b070a059402c0c0f41000782401a03070005503000d44021181040841e64a18841003000c00602c00240b8650b400c40743e0140f101842c034080030301d1491603200703103100840b155155420f28010090410125003084c1c03401c564003240d4810781100c2c076002c0c201107240c0850701 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 365991088 1250 365989838 365989859
    0x120212100f061b0323070303140a0b0a0902090109050312270f010c150c020a020411030f0103030336111009050d05120403080406036509060604 63
    0x40f2005000d00100842e0041d8500d14582411704142101e2042038444030186001000f825084020701e4480d2108c0c5c1c042241c001c0030b4030603c000108001c048002c41441c0c0404140070b900950955410b120b004880000e05403018403014403030081044c1d1403665003c51800f0781e030021451810320348041600d8492400180c0302c083c40c40c0844002400c1801040305640b034010402c40e56114498800b03401e05040020450300040e107e07a426200312000e000d0300703003140c200c103e00d80022104001820072000041010a00036880078900d03501c030454603209600b400381c11034034090700c05008042448014031140c091106554111441640407100b1055080344aa0014040200c5000d09440740c180c041901082100401800407100c0c0030b010801e807070720f5490510000c0364010344542c40102e818040c145080f00800540c0301d0542806451103400480104c1100f4142c14620281d155034400914110111001001c40211000c8030700300032006401c902c5040c0218100094400b900610090200f0b10044550 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 365992338 1250 365991088 365991137
    0x20d02040506040b10030606140c03190302070803040309030605060a080303071209050a110a0905012702120c0310090b0904020d05070b0c01060f060c0c0501120212100f06 75
    0x1200c0208598480a0004009005583c20283d0000d0454044101580c06800c00030481c0c0c00fa845084408000c844440f0103442024801c00707298001b086450b50300d1400114809055081d89801403c0c016181d0318003c059000351810307801b01301d65040c10000c014090183c20380c00342082c0c4404a030540f0305041c0326600c0c040034000c0c030103121300004109000100c40e4842c80300c80e600300741111a9954181419050613030080c020a01a1181890202e84150780e40100da0480d00e1000030300c5080b0780f5100000f65069034511200d00b400d0f400b042051040c8688074481303030040301031140d240d40d2800c00c082c10383c10030f0045910540301181031141d13150080d5504100306901a4050701c1000086210b40790880c00d003d00764100f1342d800c000200d051501c5032030550100303007641c00041b01d603a5800d44409080cac800001000c0000e1035410b040c01c1c180050351280d0710042d8400c91101c005820416041a2290007900850306040b80e04000d0400b04401c80301d040811000302001d0400c41c440c201e1504a00d1b182070300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 365993588 1250 365992338 365992343
    0xb0109240e0c09040501090b1c0506010501052803060501030b0f1e0409050d08240d0f0c08190203071d0c131a0a030c052106040e070321080103020d 65
    0x2240000202e203180e03403030210f403820319004108001c10342e142c6020314010000c1002940c00740c2e01178542c910010703141c8074100010680000c01001580c0c070741401152035602c183c2502500e041c101400703107035290034030400c12050003181c2c801042ca203040c0000141100c01c04150207200d0101c0b0001130003d52205103d0400d00804640c1ca203841101590104024100c580d2008003144200d0189004c080d5108261900a542c80680103a00c2c00c000b1010070405206101041c0d8407003521200a00011800c25190414601c94250400c8956940d0343c040d00380f03c0d0224003685420f010402d150214a41031010b40054030800c0c503200e50b103400b05201c2d40254240207004da042c40c6400540d0340c07800c6da8226145402004544500c41900c00713070809050050b0042c81c45100440d08000c407039074440d4090000d4030509402c40c0c160320481240324414004100e00a8180740e0007956400c40d46103001414001800954010203280b4603400804c2c5011080c52800116801001012001403005994048c036101c0c2898 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 365994838 1250 365993588 365993609
    0x70c0215130e0c130803040e01050a050603070e01020f0f0a0c08030a08071d3606010509040c03060803040f080f0c030a060b0402090a080d09050915090c0d02070b010924 74
    0x1c3e1003008100c0184107608014940040d240d5000910384000030040041c0c0380c41701c043c2c52190743d0707460500210303041c9030103040e41c0b0041c140005014031303106001140ca50001481100d010b03025462040d4106000e1624200454200014200c2401200305011009110100003035141103040380e001010f100f00600b41d40100700e4001c0e109400341340003c400500b5030784000c0c0014a40311300200303c4c0f903200707002c80046200320030030b510041e80c184840282d8071300c01e450603110203107086c800340d0401008040c0002d00d14107055442c0000320700c0d00401c1001d0800381602d8448412000c2c104840c4c1480c0520000c40d61241707901240f89605a51000324900c4100c079803008020550305000341c009406400354011103508969104400200c45400285158105034603881c1c241c0e0384c544a80c103200e601d0b48100c4014006012204101000d81072600c031040d4800942e000c00350410880004603010b03079000f80780a503400d442900061001a125100c0c0302c1d1844034110841c0c5111010311441d0303405c040789125410307148 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 365996088 1250 365994838 365994841
    0x30901030e37060c03020306120a05210c060109050601020106050a08030d05040309081c09080109020d0f021816080c07032309040c09030b0a05060d1202030f03070c0215130e 76
    0x3020303a01c41d100100daa02c0f8206006502d01e0500050007508100c0707000c0c2c031860b03884414140000000c5000e1500c5a00840944060103001d4103108045803616048203030a41c08000314039501d0024400540078104c807000218980c100030b0002400d40307510b5048248910315044003005811400411a022005414400304980d905d5040a1b22041c44aa1102c0801d00840c031140d255081403c0784003103100403907141c82d11141d032110001406c803804c000009400c9541c965040001c40c040303840034605544000c100c003910380b00d44502e01042e003c05903000805404103c000d50b80e9141c00c00c0e030440d4021040242c0e01e0600450b510000c4ca0300044030708050618400d19104480e01030840100ea40010707020340306000c0240100801010303240584016165103450308003042c46007030745000380d50040708005c01c8405680200c0d2504e4032502e5100d2020001c0d4031041140103030b601c0c81d00d4041c40c07280e0701d01c0e110020b4030380540c01480108030150580000c800f1082007001080302481818200fa1480c901880a99 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 365997338 1250 365996088 365996173
    0x80105060a1701060f031104060803030c041208070f0308012112110109020a0b0a1803330923120a03180b04080322050c0405040602130602030901030e 66
    0x11310190b00992489694000d020091084028500e0710381e400075182002500d6549a20756180d00040e60101c54402080000f00250f180c2202800c0303042e17024100b1145840309580d5081500105c50b8000c4002c520014010003421402a8410603103000c0c80d5424040e00c881136692105062420403143c1c00e00c4565503042e120000258480c500003540506441c0d801c83d10340b20b00d454141c2041c1094000200050f48072148000070010100480c2d612000414607003800e588030f49046210000300b0701d00c2014400c20304042c2d09080c000e42003414050100c50b9807031281104600800910228030100c50f07800038049e00102e5511008407a01d030201440c000401140380203640610748820741000e0104254001488240490400150b0241945900180c400d01c0e85907901e140b012080c4401402c203411070348103c0d00c1c508003504540c2d4468806c0310014036040010490449818086d0884401640b0216403035070b2550300f43c480c41d100746511100410400b2499000180ba0415080c0c881d0f4540e88401d214084 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 365998588 1250 365997338 365997341
    0x20d050c0409150b0307051c15050406060905070305061806010c14060702150c120606040909030e0a0909050a0204020903010e1c0e091e061306030302070906080105060a1701 76
    0x800a20042041c002d010060914424445150b207500101e54501810050f06142c002100e0f000c6071806046000070540c5120150405034000e2402d503810003c43d43c2c00300c2101101e00c41c0b284220301c5442c000507800c1c10301c40342c07104490006002c60185031800090080503680d1810140020b0418103000c4d41ea680c8800040700d4000c1115001424003040c0c085c0c541e402d95001c50f0b070700c6c854441542106c01d441c583c0001182000c50a407014808032204014504505444140c665444640039203260300d8655500300110840d8240e81e4241d0028540e40c00000181c40c003403140400030052880180591801a166a070300c610100800a2080b13a0005018150f51404c0d0089000341c00714400b51107051030911050a2040604d590503000203090181d82c00b0b6900e0546880c50041a190700341c640d004e1035214a0451112016246541c02110b81000e9100e901c460f0180c6000340d4803d0b4090140305161580340302c140d070810341004200340d04010130003006880d0311400c0e408441c400d04584001c508604281030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 365999838 1250 365998588 365998603
    0xf12080f06240f2101030206031303031d031201060801051309150905070f0602060f18100c020309030c150f0f0702030114010e09010c02120a03020d021b0f0309030307020d05 76
    0x1059001e010980f01003807010700b000b81000c9816400000c500045a041141078102c0900000358081828408140c0b22101000040030b06403290900041d440b1241400303441c4200452540c05442d03200140d0703401404403800105004180b00c0c2014a540c0d418200040c003003000d00300e45410401d5a900942080c0110004030b4150700408030410000200e0b1414416120b140600810b852100300700300c00280342d440022042d00c1804105c0f144c030720315103410541e418401501d001c01e8100d40f09004c0c003106414520312a01e8000107941c0c000b941c1e42c0721003c05150800344000c401070f1045990203070900701d0341e400804071040c0300c25100c03009564140000b011390503030144a1002e0341541c070b41500b00900400800300da84c180c0c0c8118a880720f05540706075081e420b886101c0c400c0d41c01600300f00041c0c5440401400032702904003007401d01504120521282e00201d0700035240400c84a01d0001d0303041ca020200384208100c4150b1040a0361400d08800d0100707a4030721406e04000c0c010101c00009900f440303810310241 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 366001088 1250 365999838 365999899
    0xc0203061315052a0403030e04090521090f0a0e0106140c0a030305070e04022a0307140c0f060408150c0c010c09050a090c1b0206070209040f12080f06 66
    0x10480c2d4104021015802e604c405203070440b28a01040c10903044411070241c40480368965101c900c1c60300c103502400090503000c0811643d500c203071581c05010300b49003030704032028030000100c66848200400130812000307902030b40c480c010005908140951001c509090741981c03030606220300405e030341150f0103940344900c0034100c0442c0030312141202016407603044140a18070940e610710082c2910401c0100301d1044840904030094481d0040c908020705400c0d0441c188020703000d0303d003812100d840d209400c100d551001100d0742c0100182c007006240010a201c511402aa24581040d0600200c0c40d966071390030341c0e11000034090200280f00e2000300d074202c07034031103042e80c3c001e000505450381c0140180c1401c0c0100e500c42c607000e020214100b840c91285c03404a800c00e640311600407440c864010781001d00c044041c0c0e0841010002e20015072940c905941c05144654100c41c40300a0780d0134071503007800d021290a0100710000c0d091000c0e54100c21000d5401035070440e82000d6440c0440034081c060a03c07a0700c0c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 366002338 1250 366001088 366001091
    0xf030a030204030606050108070e0420070b041505040804090504021c080a0e0f0a06050d0905240a0203040209010b16061a03010605061e0d060b12160c0203061315 71
    0x81a550540180045a01c00e200c1800f076035840740015a00c042040710840e000803841503440000d45055008211100f4803180f1000d0203021544424500381e110003002d940a1240740b0a000070881f400840c82d840180801c800c110f41c0c1807a5807415258802e40c404d15080d25101d0700450305566802214142074180c807a940c0010848e00e244c040c07035582000d59002c0114030007480c10b004c0c50500e0111800d880400900e4008480c0c01e0000a8500b80c120400d4048499507507200340000400811520744103074102c8200c2546d06403055049900d040008204018a0780140140401615192001c03819907002e428565200c52041d40c20b003040c400c074210042e0040703040c00c0464603d00403400e801e03030703a0f0312003038000780911502c80d014090184646510001c06c103503481890800944e141001d1300c1c805001c2c0502144155440c02c281a031500f10391408a003c86001040c80640090187c40071800399240c18582000b0800c0d070002030711690300a01e8011096410254401041070005560f00403501c072050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 366003588 1250 366002338 366002347
    0xb09010b18010305010b0d050616050405101707050415050a03090203060103030e03070801060f090507090f300209010603050c0c07080304030b01170a020f0109092f0a0804060903020f03 81
    0x40e0340007105001c3c40300303650325480c202c0311140c2814601e0340c06035a6600703d0300a01079a141c039142c00290b1041031103d042041400e20000c190780d56401d00c1500c10b51045c1d0390355182d4425024600c516030b032003d40f50205011040004100070031070744501c000c949000c4c3c00d06d80e845a41e00541a0058a2600002036260103028004002c15420000c904110802681207407591034a072400e003400c81e00c060250116141104104201510303064103c03035840441440e2040c1820780d21703410300b583d006080d0804800c50358074120503035a40005d03000380c075a00110354881e41544036594020418610040c0104400c00d82c40300009018640d1500841c1e11800c0e01c0000c0710f0b0f04603aa560030b16240c0d041808100d512090034000021202e407030a098154aa044101501e40c401e629400c01001d001c1030b10305d082c180702c4424400140c0141c0c038428212403403003101c4031101c00384004c545c036280c2004550f0070065800c818002c107a040340e400301890b0750241c0c0c800c0c0c0000c0c42e54902c0c01e09902d00221182d03841654840003c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 366004838 1250 366003588 366003619
    0xb3106061815080a0510050c070c060f021606170402011e08010302100503070912022b020f03010203010605041415040315052a130e0c0729040b09010b 66
    0x18419448141507071a440c04454403080096200c02440201400b26844001d005810310b0241d0b004c5600000c00d0f231030507881c2c041c00b560307444424401075012101103000704a00c07007071594040c070040e0180c040c2d104d8585c120074103000000d41311143c140c11310380790306416000203001c41e4040c41c0f902401c0784544042e0a03444000e603c008107002c01c00d00080340218000481100d01a0258043c1c13801038045880740500c090030100c80d010070b049680790580e4400c580305103090441411090740c034151a00c9450140daa40024018002549030110106000e0ba2040004015103a030150503502a070b0080f4080505c41407074500010b400b0410700844800d40f14001400008220240001340e030100c2c3c400e4018444c82e51100e00360380c204074150180b84042030000744800303612036505008007411100da80ea4045010f88130001d1056911045a070800003120019800d000d01070000c1000101c0b501420416044130985004080309041c0500010800c1c5c2100000c1504d9039400c0d004480840c1000e84a003c9004198 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 366006088 1250 366004838 366004841
    0xb0307120b0321090112060e04020d03182d0807060309061407170a020403020607080702060c070602070501030f06182003040c030c080d081501090506040902070b31060618 75
    0x130504a010030866034032190401c4c03060103160201d0b039807040040c2c07040c1d9850302402150036003008201d04100d845e41c07608443c010a440e02c4c03006824406110030414800781038440c560b407460244c1c1e041082081a0810111800041d0a0240d803254503001c02c149189180500280149602506000b41ca0f0402c101100350b206044e410140c421440002d043d81311540303400200d00c11400082e40240d01048801d001c2000c1e40000c210091024000c5482e0402800c03800c0d0411a09411010040c2c21003101000030f581d05010326840d89042c00020092640781c1442103201c0030004041d0b0003419116225490301100209000c3c28a00e04c00003e940d880c80e082c50030060b036942c20700086840700d02e14900860040d200041c5440308081940300e080c000d807180030710f020000501604903810017240c83d80100d200d031902c001502c001c003810f80c1e02607102d80307252402214003500284030681190700440800d0440215400d47c994070524500c114601e03290a0400350040d18180c1c20168203030440c80351004403800f29 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 366007194 1106 366006088 366006097
    0x60e012c0d0c030903050604060b040c0509031c0903080c0709150605071103070b04060528050d0f02040e0112140705150c1e0303100b0307120b0321 65
    0x300e0746c0305803811b032045038121486503d8035912a014209401401d00c00c4c3d00508205007451a84404207907030b01040f0045c0c030a10444002e1010703080c3e009900e03002c003640c0c0004040365105000e00b169551140c0520880c20058a40000b00c601c0c0c6500701a078100382c0f84241e07a040e1402071035441d84021445481c0506a140c01094000111340074100000c00003442c0e25100c140d142c0c2c08400c0c0310300c81207c240482281c4032170601c2c1100503556100c0f003100d144413110480041d2641484100360020301994100024807c00040085640901c1030748003070300c085c41140c8090610340d0040b02d00c2d890307056038410750341c004c89070086144145c07610754041c10106510500b01c0d45502c02d42c6505202c0103050340507143d4190400014070000005000e08076000e003480301c000740d1550030303d0b11004150603203041c4000c24855642d4291440340da0140320f0100e140c3c0c202d901c00940c034400c910503840550301 = true := by decide +kernel

theorem cover : BRFrame.Cov 365827338 366007194 := by
  have h0 := BRFrame.cov_init 365827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 365827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 365827338 ≤ n) (h2 : n < 366007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
