-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2390
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:34:32.455069+00:00
-- url     : https://prove2.me/submissions/fa730e3e-a825-405f-9f3d-0729171af7d2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 429676258 ≤ n < 429856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 429677508 1250 429676258 429676277
    0x40b060c06040c060314010312120204050d1b080c030d03180f08070c0609150c0501140c1902121204050c12010c08060d050601121403040902121f06050703 68
    0xd800d00d881ca0032078041d100d100f4501420000b10b501442035500052000c1d4031a02d0f20b60668480098600d4180b440604014403000e131143c50030303030b154140e6014000003482821b1a10540c00d001e511410409102030b6181005040010b803070100141c590b02801c000740150034080c01001e8140d00821904251242000326030032910009201070044003944c1380f00e0740e0400c7d159281c43c2404074084480ea084a0b0901c03990031010b001440d003a00e50090408413034039180c0440301c03072880d15501403c5c090110071000c3c282041402202c14000300500746108801c464940200c002c100c003241c1c0da98501c60020200f0508000301c2d08000c64405c0a00d52140c02442199a004090030111301502d621410b00095a59180e041002c0070754413451039508120300315100c004241c4180c5409840f250180306018100322511241000c101c0401d040c1204c4036038000c2030381c1d00c1d0b560752003181000c0e52203001101c10003800c40d03001401d41d402c08244810300c5000000410100360130840144c40c00e511080d019003e1150000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 429678758 1250 429677508 429677527
    0xf15070f18150302030a3608070b0c0a02060901110f0a1b050c1e13020c0703060c1e051207050306030307050a112704030c02040f0c031d0f0705040b06 66
    0x90000c002c401195401a5070740307801c0312444111907829100014100e189a240b1a041035038038251001200700d04a545450310183c54141000d100d8035000030001c0e030240e01040004a123080141030074100c9a000d4403015598a01484d00301c41e0800350001c880001403122829122250001d0311410300241048040c6040f07007144901c829501250403201a48207504244030360512414011841800380c161030031140c10000043e80c0c07104100b00d103600e141da000c50301152030401040b48000031504204104800000024000d10044048040e04d000c00b040c00c1040c180300d486402203e160f88000c2070300300400e031500b20301100da643c8098403141e4544420700004001c60024021010310511901000c800b10000d001404a0038680f5118811004046004840c650b224140c100f54000c0e40f51428200300b010510002c2c00901c80000881c0d840e40c905a1010740d401d42540c4440e00b0000c0da40c00d01c1c0020392071101e105649454580c0c0100d100e8004520420007400c1ca900030b40317201c030340041005040000d0701 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 429680008 1250 429678758 429678779
    0x14040e1504020d2d0605060f0f04031b03020427030807020c0303041e0602030a1d13060305010c020c19031707170d05090a0c0b0d060302120f15070f18 66
    0x90320703039a1130f0003402006262180011134140240c11a0b04d8180100d0785046c3c001a0540150000078582c030f000040e0808402013204c085034040c6500c03000030214171403d240c4c2c602c1411083c0c0401c90056152100c440940040003444088000c0301e00742d10071700e00e441650110b54089002d0721030829881aa0603010956405001a2019280b040c2c0c0034645580b0b50081d0a0003840705501c07000c19500100b002d8010113030700c05040e8582200c100c00c0151081e0750740001c10200045a102d6004041c81d01801104100040d00481c1007582c1030b03030031940500080010044110020244418002c4181e8000c00c0003400110800ea42d420340b44e000141000d443d038130741d1005001c959503000460707180050301091701c080c2481a180c0124a000040010030341aa965050841c020300811018100100f03500018240a40149000d194041c3c1000800c2c1c03502c000c0c51b0358a502d003850007911400303240100e20111000c0340c4118869450344c0e64112501e0810241980c1032085030201810803d900300f0041081c0440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 429681258 1250 429680008 429680021
    0x8180a09180302070515030f1008010507030b030c0901050604050d06020403021206010609060806102a061b0c0f1415090d0e01030212010504050a1806090314040e1504020d 75
    0x30228001d035001d880d03103002410480141c11043c4905032400005400a841d03000361fa5011507501c4d00e07001180c94441d50082c04c0c040903030005410f50300f014100480c5030390540020000400940442d010102002d0400c245d00500740620780d0440c034240020170962078641e03441e15130140548401454262241c0200307034030035a442a4882503a0040700100303c40ca5004080000601d42c610305410b01e42030080000b0515029000314808010703046030403c00441194501e99180300c1643c3e0a85404041443c0840241880818042001d03d18102c4403503490f0144400b0721510b9803181c00c7c90021400c40d901c01c0054864141041d19a200b4142c0d151500c01151824030b00a00100d0010081c1c010302c450020040d819054000e0b04140c0184551105801300300001e03810344000721408902a911038801a008111010b440542d541c100d5080300140441c582c40b4482c0355000e580c4642e1044849004c01c54284607034851052028241e10014070088054200622610300c0148054608108408240143e804 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 429682508 1250 429681258 429681281
    0xc030f06150409180b1803030a09030e0d0506070f0507051f0902090f0901050a1103040b06011806030506030f070501231201030503180f0319060603050d020718050408180a09 76
    0x4c41440790310502c8445d170540366001c119503000748107000c002c008080d1240005401c030481d4545901d4035200701400b401d0000d48118010b00007410303001c4c0303d08106640ba00140d41c0342d400302e0300c0840c20304001c0e407040003147c00490f0800000c2c40c080720365a05c200b21190b1071071610410a0f60302c2c180080141c0d00c91400e00d00030640807821041c10b00b03000ca100703030849601030402c401c43c91404004180c002c0c1d040d0706aa5000d0340154041c20a5500d6600507200301d280b0090381000d500c07640c04041035094069000900030a81039007200c0760000c03907622a030b580b00d03058012180483c401c55400000d120808a41e0b1481c00c44142045080c413000d0b1843c1c01c4041001e800450b502e4001082d4080228913080d881c20141d5000c131202e40c00c3c030352007802003500c842c1e030740300e04407464206141c0e0b590500005420000045902078221801c442031040029107030659070181300d0741b411243c50b42d1040c80100b8014140103c1d0031050203407030f095600e0100928048082d0550340c00001035080024000c00c144140e118100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 429683758 1250 429682508 429682541
    0x21e01020d18110105120f1003021507231c0507020d030f08070c1e0515042618040b1809010203010f080f060f041a040305040603050c030f06150409 65
    0x2d85901d007229420b0850a211030400c68240611503a0503100c1d4413240e000b9010103210500394980c0600c84140942d150800b94100c43d0440c0003035001e101e450010142c00b0b01941c20f0401908900042c0140c20241880309a0b5561088212044552030507840f02c01301c54013410000c0c0ba1060a9012603054000c010341600490310348400e0010090300203107001c0d80096103181c08030600f401551500c9003070010f0030021a0400c0050801c00c01c0210420003103c5114a01210301c0c5140b03000d1802c40303125000800c407030a001840c1c1d14001072000400041d14004039505031000d9500d0207540c14840200800c1240d1640700082c0d04112805804841c10f45000310710b481b0015944c2d40c1001c01c0401010f66a5111101da54824401e6110502d00400ca00381c01000c0060180c41d075844504103200c26540c80c0150340320944900d8148000c16410038024011038082e51801e000399a648410301c3c0d02800120f0346a0359a8a0381e41c0080d400d80b910750346801d82218481005800c041e1150301580845e60241803054111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 429685008 1250 429683758 429683801
    0x200709050f1302010f121d0c0a0b03040c0509060a0e0403090f0501050403030203030604090602130e01060f030506010e151b1014090d050c010b18071e021e01020d 71
    0x32242041c4264040501e001c034040c465010b40c0000c1c400130b019440c000070020702c0001c240400030307182c110004428000f40ba00101c1c0c0b03032140034030b92140080c0d03030064420f519010001609450340c5082d644a141c114070b40381c542a140074103114680c1c0c1d004101e254405c41850000c40e05603034410309180650b00035501c000c8400d0a1418044190183d604290305001040c8400c10010394000200d039800031042e40d020170031035514a09900a40518a0084400b0000701e10100351500f058040504075122591044995102d0384001e41c1101c00950381c0c1400904d124036821018100b04204c248000030304451146031107042e00c1210b40c0c00404000a00b8030340c10010030030540300181c2c020201c1500c5140c07448445070a0462101c0e03a02c2401d0360b4601c00b40700307000c42d440c01006020362080360008409171000c80251540241c09412941c00c071510f5010032000001021f8540c10900d01c03010040310b903002420800ca09440b000700c00e0030110b01032802590204200c13100000740d800f4170002d4144028945844 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 429686258 1250 429685008 429685021
    0x1812060207020d2910030305090607022d1c0609050c1c0515150d08040b040605070204050901090203070b0d020423010210051303030902010302120c0d0b120d20070905 73
    0x1400c84c0071180e000c1680610051002e100ea000d0014022241d2508000ea03541949a01140160140c500080d6101115200c2007620703441d01c42d02160032080c1d00c1501130aa000c0e0404100088030300d55540b20307041140702c80300c500288240d8003110640c0e029000b00c6819030940d41c006554484880c00b8114400011500d010030080100200c01c2c180010030040c4140d0b2800d40102a481c4410b540320500c0381804070f00341d00034099440110b401400c60203c009949503160383c0c001d4000c1e401030704200d0043d4070340300004511540600ca0341500c0c5600601038601c4a14003000d000c0715400c6005142030f40c2c4d5003000000740310f61340d03270022400012840c1c02d07007421116840300280c10030421034107083c0c040b801c03c1304200d2800d00c6180d00700d072013039411706002a90801da40012070080c0182c48000b040460840b0601241d5906680034000750b601019090014030b01160901c86590a0900088540c4d445180a445958010b045461030708607200005005e4204051300b2900e01461a8401c0096a80d200c0501c0003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 429687508 1250 429686258 429686303
    0x602072403150b0c011404050a0318090906201e0a1407060614120d0f031e0f110f04030605041a040b0402090a0903050912010f0e0c030705011812060207020d 69
    0x1840441407174803080c03510301503da840e1580c640c0800102003140bc03410384094205060701d48000303004043d0040040a441d86400d00c003c00b483c22885203110391000000340c2c120008000c0b80d80007804100040d11881d10107140c1c500e51b4204000e601e052100031344400300b0348154040588261406060003140040c030b0808107a0038614175402d014040d620b149002802070100184617400ca1450340b5123520b44500401c0304600030068076103031840358944421981003d000b190450685140b08070b20410800c010f404610360b0620406000100780101408100080f440a41c0450f5019000d0400301c034020082c85070709000300f281118100e030004000001e100550422151550b03014041640030014494185c4001e4094040c814020b48074600350101000888004c2d0008002000c5202007800150030220000e03488040700d0a080c1e0180c4544076000031250b110f00b41034080d145130041d010071182c0c280b4007040088040081c0c25240c071502081740400688600e509200403030300418210340300c00000100c1c5403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 429688758 1250 429687508 429687521
    0x10905010b0a290702040b0a08010b150a1d1203030103030807030e060103080906130806010609080f1b1905060f19080103050309011209020a09150602072403150b0c01 73
    0x807960403829845903956020070020394903040c00c03c0320329032100b9551000802a08442420039000b1035012000192110150482000c41d0000c4811140030300b0380200700000707800359000420000e82da80350308840c140d02101500401d00700c00790580c81d1141c011800c003850740e48280d20480000b0300c64010442c5507039052244d0040078807428058944c0e0b501d075489a125500440c1c411511a00002a60b01445103004508000a2149201784c1d0455a0b5913032015008820a11030852140500b00742c4d04107884011032203541e048010f40c0301c0801c0e082c00f01c041c8580e02509082d120111243d00c00d01140301d684100c0548a0251403801099a41c07040002008403104100c410303006102c00a80144000b85000c410b4426000c07082c6051022802805003031809001d40e80d40180d0004001e001c003040545c03140c1c008150039085540c03480780a0780d03100e01c1260307600c0041c424018022a0a0b80380c1059520400c011001d891a91038007103145d0001c50840c40d1411030030b5118403480c1d0b00004409503030080a00604 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 429690008 1250 429688758 429688769
    0x51618080607090e01060906020607200109200303070c0b0f041a0715020304110603060a030c0803030906090a080a0c0c091d061e0609090102040810020a1806050a11030408010905010b0a 81
    0x200400c5c50001c009e075980c1009040202803181c143d90f0100c46811000280d550701824100a000703450a41c1003c0ca07401d000000001b000d415009001c08860500008486a950b800080481c4280c17804240c1c0e11281c00c41445080c070b0081c01c00c400180f1400a801c0203600d6004060400d540d5101868285004410f000c200c44803280140100404100a0400c54400e00e0b02078039050382d80e944410015401984a4000410030310901c0e00c00715160390000082d5208003140003c46800b6100e03001440c0d40c800d502c80c4024a07a0380c08201c0901000e124002041440c5e1003107110192407500c44203410142c0c0c001c501080e41004158010102030802009400c3e004403000044004400181c14050300904d40100800e000380d030350b00b0118030000f009504903001850b0f1032051b101d580d0340c8807086e24083e5200c5903449000400c528004801148a60203140032030303005454040c0b600e08001010307281454190710006207400240b100190071402806030704030482c8288000100146010104036650b001504907 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 429691258 1250 429690008 429690017
    0xd0209060409020931080d0f1e0621150b01171501031409030403140f03130306200a08040507030803100612021615060306060f0603050a051618080607090e0106 70
    0x100001c6280c40e4212001c8854444002c20710b00230b4121410042c3c0008840300ba040000400010340c030304002d0740003000351800301c982088002c0e86003046184080324000301800c0e8249a89180c888140c0a03031100f02c00401c181010502c1500c030180d00000c0c5941251031208001812041e400c4940e410310410001d00308911709031609041100403d59640514000241100c40ca0041100448820003a001d071881028048070303034a144612100f5082400c61000301d5600381001404040aa550750030b02c690601d02406c004d09101112004481400e000750042d2218040d9000c003002040342440194801d4140207003643c1401c0c50800f00501c0142c2c0c1925040c0040d1041c0300000c1d050603000c01c1b140f04d890700406804030b644580c0310018010400d036840140068a015000100b100080c040c0000702c40507500c0401c03003070352840c1100080c0d6800720303201c5161529507800394090a000e101e810203080d00b4000d9503e40e61351201c1220740b0344081900d120f07010401d0329600300107240c0c0c510000c41c0900303042d140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 429692508 1250 429691258 429691351
    0x301090b030c03151911041217030411060d0212091c09080706230a021f0c0c0b0c04050d06060f0506040b041811070c051302090d02090604090209 64
    0x44145110040c040025016465178075803440360440e00141c40d4080701e00c04c0a80e039203584400c0401c90601e02c01c0211883c03200004041988031580d020b03a803103242c004001c40640b11490003007041c0c541c404a001080d01d9400d0124901540c0049442407047e000e00300208034526a281c210f10003100c03043c00324401c01010034810302103400040390400c1107038420b00f00f6507440342601c48104581a0f61004242c0c01d044089600c104055000600100e01110010406640341c0101d80c07900030394910f490b511000c6500000001d0002e52a060010790040034404103a00f4140c0b44c4c0001095829001029030303500723460700c2c01070003a140c110780d40740d000b0801280c0c0140360602c1e21220000500a0384180d0760495800f08840c10000e03d140c22206100c24010b046581da541c03d40380c41100300320603000d003a0242c01451004054000e41e40300302c5200800040041c0c0d0040202d0342004440310000380241d400c40d4480039000010b8940184140c003603d1141c104281e070103000143c003042c5645140f003241d4031046140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 429693758 1250 429692508 429692533
    0x9020112060515130e092b020d0f2102091306030b0c1318020d050702070b12090c040e0d0f26060d080a09140402130612110301090b030c03 61
    0x311403100d2014580d0303c0f5460300550a01030b0040d50450780031001c0b00035240204400b440003c600012852980444d0481d10081c200c07094180ca1500510540980d200030843e00e40307580984001200f22186180032482681c410071440d80d81000c20105500b07080d0046924110791504040030b0004000c40013080008900d90b407100603000c1405030102c282c011000605045485a00807064041e00d1441d4014401d40501641c4400951010725055241858a408562000d02c04240542211243c8111318106110510600066480907018960901c0389040901d41c6440b0f5018903540761030300002a02106200b00340207002d94260000c800f081114214201d00a10300503640c0c005480400801c10190745c3d40e49020604039040004040d0600724089211902984c0c07010140c0306490001042400501041040c8030580c029250315080398251070b0400c2c050745215103810a66103400280115070240f400b2005112980280c1003014100e44503059403029003001c000740a282e00003940244044080342 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 429695008 1250 429693758 429693769
    0x31b07120803040f050102090414070f08060f04020a020f0d0c05101104030b070c060e03130605030c0315010504440d03020a030b06040f080606030f03030705070206071203090201120605 81
    0x1807001300240034440b00d80702401400d505075035100303801500400c0080e590110980070320b40c0803a800c4001589000b1619807003885500e0070f44c00f948001d454160081700740810800a07401414650701140315544285d42c00e10000c11000b82170b4002c0391504c8941d17503040e003071040c01c04113aa203401f440641072019024106050200b200c0c11290003113400012600d40700307012581a100900050401402d0200000c62001c0200080401e01214000c9500041d680c40c2c040c1c40074001103401d0f40a400c001e000050000c44170300b0303030381c13215040515045144c152194590006400402c50903040b00c0d081c2003103245101001c1e00c0b9504103030030400740c50908922400001e96600c100f2401c0004154011503003034080340c0260002c1e52420b078018105a1610f881e6244056007100720312581690b80b20790700200d1111300f40412042001000c0c0006140b45981e0818191200e0f40410f070202d070440c42c10001003001c00e10103541c2d9904001a90350103d40807405000050540c1d126510102c60f0710b142400400075039540c0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 429696258 1250 429695008 429695011
    0x50412060c09080607091401030b03060604090f0b090105090106050f030c1012061d010b03040f111305040305030a05180703110a050a03051f02070201090521031b07120803 75
    0xc0180400e01050298049440030341c564002c00c560322500c0c0034803100700c1d00044540c09450320341d04c0c2500c03001d20341c0004506460341c070114150541c002d600450039904060300402c1140c0e00591480284049a960300b2807600700880304100c01d41d54803010302008000a0058100030003044607001da40c206a5000a91207200d00c00080e0300c16040d0003501886c1c03500407a40901c9400344101d0402610303070307500000000c4001c1c214102c110078005000204402d502c075002d5038000c5421200c1c032038134041e15031340300780d40001c1e02c0d80859406641501403070024061070181307500c102d200f070303940c90707100d052030590082907803805011810120000c01c03200c00404400035680c1d00722500000f070009038880407800b06100203041d400c2a074001609030000300c01d1240c001b8104980c4200c15500f00803003254003030310b1001c82c008c141c40240096403400c020450b0b89003900007406400b542c082420b031080c48000c03e2900c1c40e8003400101140039558941802c2928080c060070703004101c450101281d005030b80d52107400e00e120 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 429697508 1250 429696258 429696263
    0x12051c0e101d041a240405060a03020d1109040c0c05101805070306020a09120b130503090d120f0908030306041d0604053417010b040515010f050412 65
    0x45550000788403a100032000c160881000d07104100c8100c52040101c40074403500307041406000508100060781e0056a001c3d08179003061024181000c1c106020440c95a21980a101c101502842015400b0080f44101c10079250000d83e200c0c6d54000302c0080c4020b4402c980a8031090113080c9003850301046e4080b50b4607515202080c1e001858504005020016031a503146c06801840b42034800310400101c1e5000740f80c244070340e8450076040c0307039108000c02d40380000c5ea00040c0043c0924010901a05280300c244035158461400c2d681061480c4c8040745c01040703241015280001d8001d18400b100703401c4180c0d22040307541e0b86040903084c1d040000c901da82e84006081c840c0940d80c0d45950743e806407030880d94200c0300d59202040c4c812a05150900a5a9013240f0b54001c0c80c2003c28803412042c1e07000c03080310b407180c1c0300d4240d8900c010500e0301909045006648144441702e5403180c00c0d0200942d1a441480d21846800c1c02040000249000050401c2c280d07860020601c401000180702c04103c02c0d008100c01607 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 429698758 1250 429697508 429697517
    0x1a0c0606060a1b0503070c1a0f03040c120f1101050906031302030f030a05030702010623100516080706270b090a150902031203060109090209040612051c0e10 69
    0x40000303400326642c15040b003200183c1d903105410b075002c00001000038003402c0e000303007035101c41d45480f50030004110001340004c4c040900e04010076000042da04000d5640303d8050142c0c00440c41e6120714811100721240812240c1240c418040c1c402c002140904000f500c0c004e01e002424000300c2c0d00400e0b4184005000158058400c2110711308542e010441d080c908428201900e4039038030003400207405500261401030265081220210341c81d1010400346000000c0b40a501d050704080d50b041c0144014a26101d00c1048000c0204044840340c0c4070711100c44070700c00d150070743d501c444600f003c80444e10301310a01c80e404816000680008404038800200d0203030801c0e6050543d84030490303035030b142202004000305848a03540310001c0807100c03130b4881c0c0c07201c03130007a0280c850400300056032000b603120448240b030120702820070038043c1440941c00b4100300303a40a4000103c06803603103204070782c10020043c200c546070f0060814904800c4000381c0c071564007045080012101403008001240504013080300400c10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 429700008 1250 429698758 429698767
    0x50105131802100207030302061e16030f1107030909050115120e0a0c031a0106140d020705061501200a030c1a07021c21090218070305011a0c060606 65
    0x66007030406200e80781e54000d2000c048904845400381d00c0e4413041c48181c001d070050700d0001d1021607004850902c1805406188019951000c2e00d241801452103809800c056445a40c080000e0b41845503414004117040c0c02c540b41c0b0322f00d1400419412498200341222403d0100400c040c02d81e03510341d0742801003181003202140c2180900d81005080b81c0700e40ca0018841c818070442032018400d01d19007034034000c0d22440c10742a015074003903482c400284200d0001440c41660341c20454400b8002d4a88510340d0703000546401540c1d201d4502c2c14000341e4031035000059160700500b07a0344c2c10104035200742c4a447d42c1030025020011409442d03c2c90b00070f014060000300400c4030104654028400384d110100d84000fa40c5080011000b956030f48560051011702440b07032244081c4070300a034cc06000e00300001140c0440d000d0709001c10000748c864608100e0300892000c1240881d14000300c845403007036046590008041d0302d8403104d504402540007a140b82e41d0780400c4070300c075507400c0850741039070200b03040d21900d070381c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 429701258 1250 429700008 429700031
    0xd1412040201180e0a05070f0207090c051c050601020c011d04052205060105030609190f0609051905070b0a0c060506060d02070602070c09060b0412030e090a09060e0105010513 77
    0x4410706100c1c3c2c208500700280d01080d0301c0c402c01c00031409040c08041c10000e42e611003000703035985181543c04034050b0f448840c0030015004250480a001d54080c60036604050400000c5002c1c2c0d584200e84d4056141c55030108000b65030f0401009800785001d01c0c1030510a020100703510280400e411040b40566225000900081410048141e4283c1881d48034003117a0400d0908545680003070007460f110b4040e44c2c1c0480da030928001103040380442e0801c14900a171a595480904c8035584240840310f041d20f861444021030010301100d8103c0c1c03000d8006406c0103480340b600d68182803c13504900402c079800d0012498a40e48044601071866003c003000a0035214840003500c1c0c0d01802c20345100c0c09000151032000c00c00544c003d0b200842c4905c110300040e5484044c03140903121a0b003d06035522400380301c104003403107000014015243c02410424400161032011a401c414200e844050a9880340030079010401e03039104110100b800d100007000b96504040020b03c4924a055100c60110f4603221650345 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 429702508 1250 429701258 429701267
    0x50d020a18030b040525330f0216060807030507030905060a150e01060206040320010c0507030815010f210216051209061c1503030306080d1412040201 66
    0x818200e01c0c040c00300a9070341e00e080340511808840441d141c1c040c0808134008264060039643d1040314901e00020f10a040050801054035540740d100308005c50485503c4686a41c1c01340d010080640e80c0e00c059016104400203403505d040f04d48036a40b5000e42c007070b040222540c04010aa00318001d841c001c601030712603007030803000b1b0f0044400c05400740c0100da040c460b2005081e0b001a107460811001868080d03500d481c1044510824410900903030404000100002e01c141604203050b510040c080c011405a007664508480905417494040b03038001031000203043d008088903138403c800d002605c4a0300c100000080c500d160284140e414480041800000c2080000c844c00400540000454462404114065130009844401d9505004103e0000702901c111401c840308a600984444d280628000c690307603408038144e40341e8002076503d00718400340f070b461180707250001c40c060340d40450f0207030611076182c0c2010402c40418040c00f070004041c0c002c101c085400e9410507800342d00140c66942d11800141c1713 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 429703758 1250 429702508 429702527
    0x1061b051c021c09080f0114041106070b0108011d010e151e150f0d11060d11030f0a1506020c190b0a03150b09090f0702010f0c08040203060c0703050d020a 68
    0x10070030143c11508006140d10021103402c6070101030440d00c0a200c400b102c00d0807503901c1241c440c4041070a80c0041e010859600001c1d43c04d0b003001d0715031460009a501d1f01500c003002031f0001422651180140e0440b4901c8031140c0300008804002003007821070b070103c0079a40d95210405052510280c40006460301662200700031b0f50f2010780c019003041d2410714001007880104c041080d124005a04030b101c16400c10380b8070f64905a0b8400c102d02c0540c500e190420a403a04041824a891038031740080c1210100b211b40a180543c502c41c100c0d84050030320110341001d40d4004d05644801b9090304004001e80307940090b581081020903a1600d240d5008150b2041e03244400b80c100503001100020000c07805507041d07000050420a000318507843d40c0e150145400c00340725040480da480400d00c40811003c1e0000403140c2c2e0007165500000811400001020303042da40140c110902007540b0b030b004c010560500380003003a444080b06010600e4100c43d942e001c0c09501031302103203025059000c24944215030040b800d50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 429705008 1250 429703758 429703783
    0xa030506010509120f102705070b04140909120702040e0a021c0b070305100302040b040b031b040509070602060c0d0b0603010b07060f050408041502121201061b051c02 73
    0x950411311258031141d926000408001c00611444610316210081c500c80c0b034070b0fa210200d400344101400051030415a4000241c103030390720302540d180059441107482c014001804609004210190400b0410070390700001802214a030b08501a41c00f110f04000381103555165048400159800404d02e40b2442d00d405014001e4002d088240b8280076071240040c58050140701c1c2c01c40f0310f100da40c1c0e498201c0035500c041d03403081001000030700203000602c0c0541241c841450080c1001940fa400100000d19000c0c088440c0c0034048288a4000102c4c14a8021b5039802020f00d00240000ea03d04280250b50384801041b4080a8501281a03030a905030341d0001d04120300004c04054595031103d010381c52036407000e001240c04034038286008250384218014184104d40001503641440e02d049040d143c68449411048214050000c20320203024011002c0c1032100241e125048a80d810900054028100c08a1301012072041242080c00a600028801d0800d52112a500441d01003944142e00e06003900108 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 429706258 1250 429705008 429705019
    0x916030804330e1f080f0402040e2b0503060a12050f120a1101090201021c0e04060f140303030f0a021308031b0d090b0706051003080f0c100605060a030506010509 71
    0xc0d070042a41c4015000683c000403125071400c419030f4001c1c090109015a40078002c1815140054000900000f03501d500500103000890300d41c42d810002030500703903010500c0d0f410000e05d00c031510000e4440505440d12190b1400c0c00f5141d41041e0300010480c0211b0b104424040d44107490820801006100144c0280f0444046031280e00d0710011040b41e030f401007500280010301103a841801100c050280311066901a000b41041421005130083c04002070a2208280260440c004100c3d031a40d21540000380014500c1c21161818001c251003903540c8098010310960003401485031003646001c00b941c02c80e07140e25005039185049400d161908405600542980c000400c00c0d550600e280251034003030780e43c520151100f043c501c60702036070400307428042c0c121951024012040083d003194040781d00003403c1030050703040e11741d03030340d80c11025610030590388841500209031003c420070b0403c240315000c1603454052000d941010701080c00350007080c0b0444200341e225004104142d008204a0310000d401624 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 429707508 1250 429706258 429706349
    0x90906150d0203150607120f02070f08060f2809050709020a05071103030414040f11040305030c0f060c0706051513020405180603060103140f150916030804 68
    0x15618001e420481e41929403032110114202c0c645000c1701250341845e840301d5028007039080c60b00c00311203040c1c042010070190701c038030354021942c0c034510a16440203040c00d40081c034451500e164820b030f9401d005000d6800d50340205602403050011701460707002e842645a80000c100070075090807480c00e0560b52080c90b0582c4002003072a80b43e68404010b211483c002ca1100070903035504024565244620708c02e0001c034184089404038585440d400c020202d03110003c1c00300d200102d040e1000d020354842ea0085425a0001540c2c01d01184180008034075104031001802c2646040290714230b8074461101c00519990707940000070180b42c80c50208510100340640250b091a0740c88114900a5105001d5a4454032120001050203022900340501c05c900c050040d0100fa4030b1341c0e8440642518520420202c4d014540e24500e8030402048019602200c0300f018010b03909119400c241003000c4800008ac40012030030f410700100c2d080b002114111000b01204942030200d100c20704d500d03451141e0f6001080524042c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 429708758 1250 429707508 429707527
    0x11030f0f190510380c0102131e0f0609030b09161503110f040909030903050d050406030513050706050306030709020c060106030525031e0903020a0b060d0809090615 72
    0x240400503110342d03c0c50035a0322801e18075500302040207070150304d0401a250410703031000c18860000c0c00300c4200c20000542020340c1c030011603c0f01e5005400140800d40050003241e01400351b1013100c40200004100d4010302814800010f02c0c00e80240400742c41c40034000003040d0070200400c02c0b00300400b00c3d03000d611022601c84200d040e400110b40c0c003c000003410010114400d4440004442408044100350f5160501d801d1010000d890b00d03010a50900508510020202d4030a0000b00090100340d5540323aa0399051410180c2240c00c0505400c03078891544c0169000950002440d0b4269011070802544aa440c040042d01d058100d8000494450012950030680c1700001a003505a0707016031418800c503a1010005205072102c003000c400c241c200d120404801901990051401c520119028002c540c0380c91380d920251540840d08a00591006c4800002c0c400d03650342c107a0300320208407100e400c24107198903a180305000e440300d12882020004089401c50751140021090f40d0a07940d5040d07220034244 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 429710008 1250 429708758 429708781
    0x20703270608010b0405030703140f061503060a061206240609090c020a0c060f030209040204120b0114031011040509100e010504020a050301090b040914010207050111030f0f1905 78
    0x18460240410381c46000804c0d61050b0005450076114040c4c002c24240c1e146031584c541042142c400d450083c029101d001d441c0c08800d000c2c9520821102000d110b900c400300013030614007800205005189840c1807810f004c0181800120300c103864115101003101c01c01d4520070a00c03c104410301c0300826481403c0094803030340042e519403c48607910b034108a0f101d50b804099881e4244420b00408006040c403050000e980202840c02c5070005615006051160200103d01240d200360022030306803400621006c200140415001d0240ca00e800d0f503024801e0125001c60396032046d07039070403041b0291a80e41c00a04001e42030b041e24001d00000384803e41c00e0511048810b030300d09460103480e0803080c668001040a040c00c0c001c44e911403116903181460341e8a0482000f005013401500b1951185c0ca903040000841c0c490423080003418800000165180100d1034803a00711390b200c1e030030503a481d4420300400c400a003c02d9409075001c008860303445020359400c605101790b10050641031049610303100c00d21580703084030b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 429711258 1250 429710008 429710087
    0x3070c02031501031707060b03030a0c140a0b0105060913050a05061017042015180f060307050903190b180f2a030f01050604140103030f03020703 64
    0x390300b95400100046461400d0340d00901000c0c01038140e001201c0042d840400084c001d07580516000200c9a000d1400603003142d0200d03c526000404442c01003091003800803507040e004400340014101400c0580e1009420641481510320030305001c00e1200e540c1c4c80395425400150104c0c0020052441c2c24100350004110545402d4002d0362449541c804050144d600c000d00d0200d0141021f02c0c81c5e80c1d41c2d0312141904c1030645500480103564050400e50380796980c1e4034103510340000019488204050591034070910610f10a44251700d445250364542c0c813003c2c102e0303400c80b0303491402c10f941e40100c0000c00d14244c40d4111282071180810385030028045110340c41e038011100c0020300c03a6140d80c84080555168503c510b0400940c02204000e030044514403001c3c0201d0400902e180c10300c4c4c10210009017046c40c60144440e20b43d44590070030500340303424400e040c10100d40c1c00c0d2102095040d40c40040100041e0031011050503800200d10081c580117a51405a200c0002110720322489844100c1150600 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 429712508 1250 429711258 429711263
    0x1d04020d1a0901060e091519030605060d020a03170906030103050706080105010305090318030705120f070815070509040912170a020a0c08070204020c0706020313060906120e0c0603070c 81
    0x3064602003001e0b180040c000c0d8101d0302d041e44d13815111001c04040110a010190840b090390301000f00a502c15180e01000c000040c04807030080a41780d14608081090714401802c0c10710900c002003003100146d03900748240301a03942000403504180c1d9140c46511b414415442c0480e4418004000001041000280c010907a14155186002030360380e000190b06135441a200b110040e00280070074480526091204280b5507402021216110341c1d40d0302003281000d46451204507034002421581c2d08c98000c0010200030700b03200340108480c144512151000c10341c058010020041d00007100500e0760b83e00d4010408054010002e1051441c070b03500050403261004508403900c281c1c1000103445a000c501c2a40c03695034081e11201074040c1c640d6030310f070017540c8440340499019900b4001c0800d03843c4204060400f030000c580040d55617090341410782c0e61182d5103a006508108403180d09000196102c0104180034595103008100300d260740407003a09001019080310b400540200821207465400002e05840780e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 429713758 1250 429712508 429712541
    0x50402032d07090302100917010b030f06280902152a12210405071e08030405040c02010902030a0803150f06090906190b040312050a080105011d04020d 66
    0x40c0c03500c821025501003154070001041004101300050f04102c00e5001c0380145600d0721b10341998440c41c00c0d8600c05100d1103d0700c2242e540d1460321485050402601e02c00c924040c00034031107460f0a0000b200d11550380458440d034010040b070101100c003403580000c800d00e98010300110500c1c41c000340700700303103a0007100c841d42c140c016003840907050840c000c984030130080c046400740c1484601e0303a0580d50a6030242ca0921040400944210120091085618042c4c0d1240000c0c1010034608590410030800110056252410314441005808d900204035011603100b9074021514003000359041e070040c401c804000e905401000b801c01c0410103504011481021b0000c80f68034028060414002840c0e0881880740e0016020032591030a40380282259a000400404242040041070000d506207050780e80034400c0582d000c6414000c000e07003101c12212055581c80c2c40740c188824008014041a010310606040c000d045d0407036241e150f8034401c52181e10201800955540307001040d414000c14440c82140381c0c94 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 429715008 1250 429713758 429713821
    0x8120a0f0c0c050f0316030602071110050d0b13020a110610060909050c0c07030b010e073f1104080d0215010b0f1309091a0912031005040203 62
    0x11406106041c1c031564000840000300c1d81000c082c000c10702030070207200c0c0e854810400102c2c442009010510061481083d01507299030b07031460003582000d180301e00c0e903205440a002d03200d9181e52140c15150701c400150004030b49400c010000c070341c500c1e1860b1041d1000d070f400090342200c250382100400400e03203074100031154140c0e100d070304619150540340030310000900075035030403c0151026080550000c0d20000b240b031800320286075151a06103142c1c0300301d8645540100410811074a03c0b82d5592001450410b41d03141e118642c0040c50100f6508000c0720041d00007844100d400c2c00003101c40c0f900d640303540710401c03207004402100e41e180d8100c0d03c10055070f481401c00c00d0602500c042412200d00380c00108000c6680d00702154402183c1243d040c0d00c200e11400d1224642e07180319007100c1001403030808000540c5018501305203a60071450407100c00900c807074200740402d00c0d60002e01c1d04c0e140f031640da000540302d44620013082d001041c141e000582c028004000e00144901d0441410004400e41840101300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 429716258 1250 429715008 429715037
    0x7060504050a1a060604062030130302040f0f0510080606030111030601080c07080406050a030b03011b110c030a230c0f102705040e060103050a1b08120a 67
    0x4090200c1315160040b10621040090602a20001400e60b105414403010100170b030440c0c510300608841c0d5008910f25003100c41040321240926640c4940700f03505146c0c40d080e480100b81040480134400203020716541c00300070f030805145501c1915000c592000900490820ba101d51411540d6409600281d00a50020131418034051082003103034803100c580a42195541d00040d03c84000090481d00c03009020403070b542c00202001c0c010805030106468070741c0c0310350071040010111000e031840e05000fa0b1401d807001c0d205c4200c01550031468140b030300c0c4c400c078804501142e0900380140c6501a0750944208482101041441c0804074451343d4140d000148001d0318026242d55022004896a00034855460700c51141c200b442401c0021b0682c1d0425101d50310314105035803940d480701c04e60f4010306076122b03009121503d42030203401c405140d5100101851350454498a4444620a1005141c500940144c289003104400c001004126010950381e051001c102c0f924070382e511032086c02d0001210074400020 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 429717508 1250 429716258 429716303
    0xa0801050402180601140a09150e0d020402030703090b010306050619030b01060810031e0213090209011806080d02060603330a06050d050c0f0a030f0b04060207060504050a 75
    0x101d20b4004120421410342d1030a6620560009000e550400c13007001505404a880b48008110104142c1e0b51903c1ea00d1506407040c40880690444004010708490603411556580120209160b0100d0380184e80740c5960038207500509188100a0890b104d82d800082403201550049118450965000d4860030013080304920b0140b9500004010540c09001885414031503422140e0120811402500b196107030b4603500880c0300038078054103610310481c00090031400d00400b0719818010844080c0820106039001036040c0380140174508040c00040c00d101c8016081d80c000c10001c00c40042a41c212041b40c410007500c401080350b46600a11a842848004002284200e2005020f4214640501014101e0041040300140c5096a1552100307000302d07142e600e440358054024480e40003440842c1c0700710700b07001c0108100700714241704048004003080410400382071a04495440a404103c030764031031a102c0000c1c061081e020b03040900c0c1400300020442e00064061803580181040314204035030041c1d114 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 429718758 1250 429717508 429717511
    0x60905060a050d180609020a0b032a070605070c0303060806060609090402031e1e03041a21010b0903010e07082a0d08040f0b0c030a0e06270a080105 65
    0x303401080401c003100129119001504401401c10f002080030003003c0051584583c1c00c48096440303603074800c0705004515059804c0001081686034071411468201c5400102158041c0c042d0840345100c03580c01c009141e1181117480d00c540c00311040000c0e09112100a0030454100012030200c0e207401e60105a480d00043d141b445000c004110a00c4c0441410911813401f501400c08ca1b0140b00f201c10074940c004030001010341341014031008261003c0a56201d08851140c0c2c0d040c541d80c0d8000300001c1c4070b80c030a800740210640005200782995509120200304200e040300c901e4684d5040305400210b90291008000c1284100c21230007440740c240d0f00e0304281d880d440b00303100e814400d80c0030308100c0c41c08850901014000d0304520034445408044100840c4101171072050482d0803240004003807041c1042040c1d410b019241200d081070500035200142a561700c9042e00c600c0900454980b070400b20f688105c21070300b0880c0340100c0e4009200c521a5844d1041d421050120300c90242e8620110f00c0c103405215a9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 429720008 1250 429718758 429718769
    0x8180a0902090d0201030903120501140f0406050904030e0d0b0a06031203021314030309031203040c081c0305151e03010f180b0405010209030307050d02060f0f07110c0d03050904060609 81
    0xd403c280c2c0e80c1d005600810701d6030811001d00070522440100307000c4071721400b4001c100d803c7c481820440c0020070040c50b0a000080d45105e946405000c2c0116198403420303607482a8181040b1034010220800a001301540742001841c00100b00c2c10400d001840782c0120b170440f40b2500c0e0790600000100d034241c0980c054984000f00440d6140c03010841c03032070f080c001d0000b029805000d0700e19004620001c43d080c070004100081c06c503a4004240010842441186801440024080c11341141c0c0e2031040f000341020b2030001c41c10103441f000840e403246d544494140f180c1c98010071181005011542c160714660500344c0c0384c1e10039480c0035103138000c0c01c40301d000b092031008100030042000ea2440e030321300c0402c1d0340c00b40c400c0d40d50f594280101d0905403800c00c0240341240c0110010041525200c40c028039041d802804004807100500a11651240c8101d50a810040764104a60140034220b0402d01d0180001540d5030b00000c105220b5042c503800c03c004011154045e02c05102c0c142e00c40d0700c251420f4007180b040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 429721258 1250 429720008 429720019
    0x220902010f0f05030714041802041404090819030f0c0e09012103030e030f030f090f19030e03120a0f02010b0d1e03051c051806070f1103040308180a090209 68
    0x1500c5d50340b180c0c03171a00d202c00b20943c5560a107034480031700a1800141c1c00b880074a840d800501804098200c0c010b048007502c0454050007210500d95586c0ba4030b0142111010041c1e0000f503210320000d000f6040480105480704040180700280d0310014019810b07200e8041c00781100c45c0011030450240c040c03481d4036580c41c8007642c0344500d05544c218020325080c02000e5403070005020301c500d40203000c002075020314100c51049107a800d00c01941820802515560032441d03000203000d4801e02062448076103e1038050504980400481001c01d00b4644400d07080365900f080018000042d40d0803a40c108484030103640200141d1400409010b62601000c0c2e0203421440c60000ca45280d1041c1040c1300c2d0018460b2501c81e013000000e0600c405d1030010a02c01c600010303190b6082001914a00001381c05014120005040c84d003000c00300504020761003c010070400240d10002400c03242c00b001154015075020550702d6841081c0c0000d1100042c0c04804c50340b00b03404168000910340207c1c000d68100b013900038803 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 429722508 1250 429721258 429721261
    0x280e010e060d090501051602100c092709140d170105090403050c010c09140f0a03080a090b0f070501051f0b091c030c020108062d220902010f0f0503 65
    0x3000201c0d000082c1180400d91100c9014002490078042c0600801d008919401481307404000a4140048001c8a680e024039068892400302d0b4845100002c0758100303515100d4204031481382600c0002c002c4540100b20b410903142c18108a08410f030845d02d001d0b96400c0d684e084a02c1201250031503146010303640540c1c10300005011a00d0003800d480d4000e03100c0e04140740f800d113001c3c04890130360321000c03030400114000e14020040c44503010b295034040c00049900c1880c3c05501c000081c01084503000c054100c01e030100d2450051801100710001801ca803500c165240d84020032a061280d0040204407015400d2001086040050743e442d02840000c0050103200703030f07040c03001841540d0007404005a0101650700010340b4180e02d104505c6015020b603907070700350703510003070001502403c8040d013000d000340f20002c21203500d905130000f400000c026414110011501000026203e10350b03030201c180200d01500c1205904181507444000058400e880e400320144901006441d4560b01c03864480c0450b00400 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 429723758 1250 429722508 429722537
    0x11030a020d0917040e070302160f030e031f0b01020604030c06150b0c01050a0c08010807120203030405041d060c0909040b0907030501060f1802131e0308280e01 70
    0x200a0a40031440801c00038105000b03840d2055450700c403034007240305500005414080d25181d0360f103c650015060030258a0714041c1100d042100c01e000001800103d1084d903044101842003407184040300c3d006041740c1c1070f070b06044200015045030b194200344161078900006081d500101d074003407185416403030f02d00741100030f40c0b00c86001d8108150303002c0703400300305041c0070522802c5400070f862004548070000580b0301d07140102d28210341c90340580c2c9050106d128010410524006003140c00e40e100313070550301510040c03440800e14502503600101c0c0c0c010b00f00003894815502024503045c0c040d000d1400c40e0001d86518509200034413610300c00681140d40c4000040100b00042135860f005881c01c0c04842c080c0769603444150840e0199002400c524181d05020400083e5240a020300d4a402c01c404614010b55034803080c01040081c0301c2c480100b4a400d8009402c141002c40180065400c20f04160760b5800d03000e101c0b080081003401d540c031185080c40014002074414030f68000d41000c1a1544c0c1c4140d0800d5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 429725008 1250 429723758 429723761
    0x9081b0111010908030712150605090907090302090105040c0210050c1309050408030406051e0702030d0c1716020f01110405040c0e0d031b0507080a0308091501260318010306080111030a 81
    0xa11004030312342c4500380c81801c0103085010030001c000b5507641c02e844000c4041001058000603010104000440d5010b2000d0707901c03008580d04468045500040c4a503401c207069003049103118812403064900b1080145241c00c0d880141119408d01e40e14584050711030301820220749081d00d01030001b201c2800003900250b11036100d01d40104a400a2400c03040042e640010642e10880b4503800503040850654240fa070317107004005c1800c4890509800701982140c02d8004c041004154a10124007510003808450080c0110401001e1900080c050302000344281030f0700b0341c404d1085074040e5140240380c0700002c1c4035803040d0560880081071140041210344040302c40c02400100c60003402d8800080000040c0c0400c2684014a6010058601c1c040103040240c9800c0303004010081356044100a90945020b0841c400e0660340d10051800c404205150b1405d04c01440c00c101c0c1c0c03058403000610100c025808503460441c8502640c0900c08030b9200c800880c20307600c104840300c1280c04140003261081d1500e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 429726258 1250 429725008 429725027
    0x4060801140d021e0307050105120402040f0912051207030506031905030405040e01051e0403082809051522031d0a0b03181603021009081b01110109080307 68
    0x201109051950ba8001a41c568151282d1104c01104990140140e0909001442c01031a09003402428084240c003050040c00d07008000a200301d5485080000c0c0342840da2013a50055000750382202c98984143d0083c0041d0302c101906406904c0010000702c00078400d010300e42c80383c034000d005002d60302c101e980c800300402c9500d001210b1900040c030020440e40c54074800d42c60794000d590004a101e040c49082100507041c1c2c0d403d030102242203071041001087c1c00160071174014200d000022910f01e0444044400c0d05804805921340c030342855800014040c000860440520701c407003221400b0f072585144201a43c0409810603100b81c2c0401c40000402d009108403c05003085c1051000310405000c0011607105407a0041100010013109000e00102201c54104005914a00600c0d03070381d0780c2c440325a06402040c40001d00ca0b560000074149010b20850140000308400e03412124550700b244a0b481c017188841e48a80e00150954910300020141405043c0040c2e400c419031500d9915600e9003116072158 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 429727508 1250 429726258 429726299
    0x190b0703090b0f1b010507050f13050d030f0305060102150a0e0109060e0a0309170a1515260723030a0b0907050406090e06010b09010306090504140d020304060801 71
    0x8200141018444004102032200c3e15020340e56034182111090b40c550010340b6444440c3c3c5001d040110642c2c2000131915080c0340d243c0490303224071138a01001d00d04c0a403038000d607801144a116030307801c041d04000744c480c400715580c89c1401195210801280d0b640c20640070b0000544407840405c0300b16015034400258240840300103c0c003015142c8583c41981c865413580312903a4032440540d001d060788440300401401c3c42e5840d0000c3d400030f814a00ea550143d00d10041d081c41451541140c4903900d070340c003000310041004807243c4501e5940c01e032903c00c1c02e01005d95100740e850555480c2010300c0d02055180c26640090b000540030709031000002c140c42806064281c242c4a00d00461300452188628284a030500301c00500c0454240390501041c0d940581c8030042040c20f1200840d600c86010601c94152402011811344402c04800100c020f400e05034071050301c0900d00014402400110044081640a041d003242c9100300c01c0001240e5a1099200f007000054490005112441e20504071151640 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 429728758 1250 429727508 429727517
    0x3021806031e0103232a0604030b040c06200307142104050f0d0f060504060219020631080c030f0d050603010f0605010e0105070f080408060702010b190b0703 69
    0x520502c00014100c203030020340f161107140816901071083c03060030700c1c0300b00030711405031042c000203ca10300b488105a40e0008030344007401c006500c2545448050320019a00002c51400905160a00c08000c00003401028000741401214841d03158020807004119000240254506101c546545490892103507141c0124020fa4041d000684e54204c18185ea14a0750351011307a80d42c0c40c1004001c072524048950782e00aa0310b040c060004030361090b80380702d2919089480401c466076103282400c028810800140000145182c0a1000c40c0c1d0005a1520400407080b10782182011300000d82051480005001100c038200c201c0c000004080f08081c2118010034001c9038141042c2002c11034551304994900702d40180c0d507008018551500340281c1d0401c600ca050100700c040d00f403000017810007440c08041e6043c010001441c0c010402455595100c09400001407910340380c5074002640c8410068075114015800c207031000c2c0552508068080c0e043d40350401d40072000c0d2400719900100c1d00606829000e00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 429730008 1250 429728758 429728791
    0x41409060409060203041209050f1f020c22180203031e28200d2001021207080c090d1401140c04061103130501052b020310060302180603 60
    0x41042c00614040c6204075078042e20b191148900402142305c0c0d42c1311134810f82815840c4011915a00100a8101e011034405001c0c0162001c013a858a220f2213540c035009102801421401d0900c500d40d140303404143c1a0500c5400100301c0c12000e460612503019615420401000c070880b9081010010642089440c02e400c151000e603100600310166042c0c2200d0004010301c2d0b8500560000041c000b40788201b400303c1d415400b102c401036848a624542e0703020300c4011069522074402180e0030100e2104034000a42d55580a07800747e2540070f1059407112f010564180220f41c0d00c04214007071ba180c0141c082d00800780111035488881ca901400882c00b01d1a55031000030031020080004c45510030a442c185441c1c1d5146080801402c00e5510f494400080c1c00601030381c002e4205a012400c1111400d00c0e0140d00c460400045110324180d411310055120300c444280ca1001900e80c024610441946094015072942c601007501030f480b42070241c004c0407040084840091500901458110203540e1803035142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 429731258 1250 429730008 429730013
    0x50f06030622090b07020312010923180c01050a05030f0408071208041103032104020102121917280e0717010e0a0b01090e010209100f03060b041409060409 68
    0x2082d020310b800d880355603103c1d610001400891520b080d0800c100344029403a103510315180d404119410b00904009903281e0f40340c03c08981518100b02101141405c036820310707007028801740c440d400140303c0604160144652440c0c5540c024001d590041916446552465486107075039400071b1001481150110418003040c408941602c1460b40b031101e050325101d05504003070408161008402003802d1003948100001ca184a40541e4228a903000450140c05261203d1006038281501906e100d5825200880d1140d611038034030030074020041c81d43e10303000001d080549000300c42d0f0804448242c4013500c54013070035810701c0400418480403840c0e000000340c80741c050540b003402c04456500c6019948c40007a8810380400086c0f092039440d165140080c80b6074103031540e88a040c280140725180a82e6031303500c58664014800e40498860000061114804005001c00500300c1141e03007c81c0340c006450b150b404510a00c4d074200702c03002d403440301518001c1c02c0305904c20009400f0004000d65017158036070312003500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 429732508 1250 429731258 429731299
    0x804090f1805031c15050f03031603021c080403050a080405011506030902011b0b01180f0c08090d0f050910030906050c0c0d0c08070b04050c1002011d0304050f060306 73
    0x11181c0300d080610303a5558405400c011914584070201c80092074420080801d90882070142c1c01c41b44180c0d082004030246000090840c00341280401c0f5880354618400201940498100081e00b50110200c1c22060f810a044400c22021640280410020042d50005a0080f001c0c560f01c0f0780b041002041580500c83c105803800d10580c404404651102c45807000c640c1c000a50740c000f4100a041890300d01c495890320302039200180324804076440c5112070008000c6407070708548070805580c1c600388001d00c4070160003440d400781100d101c07855003d0b00a0301da543d580b080c5008042c01c1c20702d64810b41403222304020440c030f0ba907907801004180b43e40e410790000042c03d5800390b1885401034410281d203c860890106043c00c05604841d001c1040c820760030f40009440700295201960051000d440381d40d502d240407880e1200b11860564800700300158242c0c3d890303054104507070203918403a00d512070703d40500c0020342c0e0740518050184d1044d080d5420340440c1c00e00c007001d1540f1500c020070ba06091a2207868006 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 429733758 1250 429732508 429732551
    0x130f0f0f02190513110a05090a0806010605181002060c0d060e090109030207082e090206030a05071d03031b010b0a0803090a0b1206040902150f1201050604030804090f 73
    0x80c551aa400e00411003442c15604c008100100c169007030250f0b07074400620805904c90074070068207014010800450ba5203ca0000d00083c025210440e500380d6141d8901601c1d82c1c100100350800507001003000001401c0444140340f801c0744a40040c2880c1d190001c1001c10b58001241c1a10040d03540c03100000e42c1c00e80e10101d24040c01e01d40300000780f5640e190030b00a0906040d40c1200d1442e90050407000c4900900c4a0715260300818091543e84144840c140395003d0002140e02941c040070100900603030540b281e1000d4021320840e01c0e101081c001c81c0142c3c3c1c4600d10403030b00da01d034140c01c1030040e80010800c0700307003507030504a8239000012b000c04881c0021380d1780042c64101d8102c85c3d002003500300050610800c0721000d041c07074070310007400d120001044503110341c0300a001c01c0c011030700c2e12030150440d1901c01441560b0030040da402e0b900c9006080000c0466000408401c84960b0342c0c00000809080c040119000d8076000309400d4078140c10300e15924007401c4d1041d42c81040e5562142c0c0364051340040048c14 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 429735008 1250 429733758 429733789
    0xf05010b0109030213050a1803030522120804020d0602030705091e03030702040b0a08011401030c06080f0601030e0f070b09040b1002030702090709181a100f110a020a0b03010e130f0f0f02 82
    0x80c1c28201810038440c0d61358502a1101041c2e1008042400700306091081400b1103100d2506400d42c0e80c07143202044104c610701d400105140d00220a00c07000e144c021001d0002007005880700072080b11040c65001d049080e032450f00350103030810400b143c0903040030741002d100d04001600030000030395150500fa08482c43c0000a28101ca10300d030040c42002074400300f4000a00b620315005d0a02e051100d4413240580026101506041d07640b15002620320091100c102054000b009450174255a2103400d00340d0b9000015080c45546000007036002c034070380103801c1d501c26003440d8021410b080e10340e800e2200701500078095000340007014030000743c1400b100c205070266501d5407a011801c07040201c10100b920003040c09103032040403410000d071881c940c4003c5404003041d80340342c0544881240b0390754504128842c0d0019400c044c018101151010241c0015412100751907005811541c42441088104002d80e400602481000c0079040210700c1588030341194a010700460855400301e83d00080000760601542c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 429736258 1250 429735008 429735011
    0x1b140f0105010e0c030622091b1701050c0304032f1e0a0b060402030a0204170c151305060904060801021308070f27020708070f05010b0109030213050a180303 69
    0x180480c003886194244c201c135189181500314103114000950000044456203030900f8060315030105041c642c2c01203603103950461800d003000c1c0d6503015a910b040f125030040c1c00001d0302103590000c0d02001489280d12550031030140d1400d503103c030341c0e0132641c07944922007035204040800b054643c0f0442105008912182e40c00c0108070000d01c11082c241482086811040c00d5085100c00d04080b800e0b601041e5400701084400580d241e07600e1362850300a008070f4121004d851051a0001181d60001661038502202101c4003107a1038140b551541003441070300d0702c100e02e0003410700741006181403541c06003c44881c018408a441a10b440500d82240c00c08281c8110721164030900704484042400980702801001c0d26055003982401070541311248c01710701070104a40001c002690180d402c1d4103848480e68050429a9521420701708082c40b10600701d0700762080d51908844280c13940c0211942c0e02200d50207002c8401300155603080b0401400010148070450352a0a180243e500344001c0c28400c0340c5c0301e070300d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 429737508 1250 429736258 429736261
    0xf060405091905160206040b0601031d1f0501050307150e1e0f03070510110115080f0706020102130b0304032304032001020327030307230703031b140f0105 68
    0x40d10810f035070003e82881c1000f8071001000b4201503004c80c0955110750042c10940c0b00e519407200490040c002503105d185120607507082006400c201203103417802c15004140b2514140a036070b038101e088038001e12440e540f6a0040004220b00c40100018001c011503508181c9110300c80500860920100c01c20001245138001c004a5006d00e089002d0300f00420f003e0b80102042030500b0b001c240c2808a00c4595024403c4440080d036a58000350480000b0403d00034455102c1030352071211f070b591010400101030481c0915240425030a1052080d9481038000d03400d129030340d0b0b14000400f005580060300c282d08200048076110104500c003181c0d4601044001b10840d599032039820f1030420607440380358000821402c1c18620900c0da0307000003034a0789c0c006191008500000e10342e508a024201d00900260540000300d410810b0014500003c0c0742100310f90040000300c04841a074580303030600c502005001c02c120031101078480290900035a100d40c4117100c8000c44418134040145024071a940c0c194042e0344900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 429738758 1250 429737508 429737551
    0x10f0203101d0f06060706060515030f070f05040b1b1c03060506090904061d100b01030e1f050c0409140610080c0a0e06070803040f0c0b0403110f06040509 68
    0xe0611040c841c640500300d0b040d042081502501d07810107019240f00b0740c1c01081040620002e54484402084010302c0102e406200e000a95280c2e0003c440303a140e400e0384140083c20850094000f0392029000303035549450700341401803000c0203400c910002c0510010034440605165030070480360070007501c0d085119004060340740d802400d40304c43e600000d0203000207000c445001d40b40e00c546207400c00e41c00040490741211a181c482184060070900c0f0455104265110b1004c0c0c10760740c0300c0880c074282a07800348034ac03444494105a0300c1111100c4801c694811029219980341c0c02e070300407908160506c2c04589001d075501401d000b590241c140d0764203140b0003901404850b1501c5a0400505420390070098003030f00e440c01140f1101e00070900b0349001c0c40000421804141d60728000c45000303641c8a8030044d00c030300b024201412140d100e0941210b4820000c9400704101c284c00003520103c0b5070200d0000d02400996080c4602814010505500401309110101e6159161001d8511030709204000313100c11080c48 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 429740008 1250 429738758 429738779
    0xc0a030905100203180d0305090a0b0706051005010507030c020f0a06050301090b0d0807031d04111c15051c0606170c01050708070201051c0c110f0c0f12010f020310 72
    0x142400306551080003003620505205c3c1d02c01e601018102d8010710840003900f003c3d0303407911490090344c0c1d0000a02d02d010403400c40140c0a0482c031130080500704010343d11000000c43c00b181c0c81c010783c0e000c65010303c280320002e031123060740a800a102500c807217903c41c81e88004c19104031560700040b021a8002c40140701890081c0b15800c52108101d403042d0501c2010307200c0700400c3c801d06030058204010944d03102c1c40191340501d00005590003610400c00561001101b4086411040402d15040a490103210798010f0328014426501b4170070082e946102c0c0742208004119a90300c2d02c85803a800081c5090021401d244240001005084052240016213a20b03140c201140d80c5104c07030503c101885031002140d02c00080d01e101075030a00380070303030750310680c200c40480103440d140401c03e60303400c064002c0107540e806a40000e64502100858403003207840c8060584a80c0110040b0740c1107006080450101d180c9a9800c40400e480080009a85003441c1005000e903403040301c0c443e83c00e030b1a40c2c40030421100c0320f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 429741258 1250 429740008 429740029
    0x40f06020d0b040e0c0a15030b090a09062306040902040b030d030c02070812040918060c0509100306290c0304140109061728090b0a050906071e050c0a030905 69
    0x80017a01601401d68000f581078030b154010000c4070034680042c80c600710b0081e840100d01c2e00e0024690f07140c515010b0070000c003402032020110303441418283d03200c01c02001246403030400b0003004401c2d0b03401d9a031107061000070301e10070001faa80140c4501c041c00898806200126207c00c1540d401b0500261003100645462210360024195070320503030203c200052060151416525008000310f01202c40684041074004a402e001c0e01482c500384500590a4000380248005503098a1043c142c0c81c1d81c1800742c044501c148650920711350b2414401102041550300351f031940700c81d8a5214201400703003800900e140c01903000b084082c2c40741c42041c2400c1d80c216040d800185410314001100c040400f40b07004030010044e003101401d00c40c1f080a0320121071014444007c00c2005441080b116004c1d0400803000f8074103407a42600285031101181c48a0808548e80b4030400403900c4050f03140c0804d0005030040007541d1054010084203015000c1140c0c4140144c0700e0280c0650341d028181400c020411400204 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 429742508 1250 429741258 429741281
    0x602090a050d05190606030b1905010605040f05060313080705030c01050a05160f0207050312030f0703020702011d01120e0606011202030114150c160306141b03040f06020d0b04 77
    0x22036220382c0e000070b2000480340c0d10070801e50401c5158200f6442c0000140c1881d07000104082c1c41d140c10051846170f442250851407813012410b11540e66228810b6655200b03d004020b24207141c1030050085042c16801560004100004c40844a4143d1076000c03450b0040c1c081140c564000040c01301005009014454000c00181030401050030101c090000704016140100144a50800d08034140307802400090000e100240c15503002c0e070703600c1c20545d055a02c02c0311141c0c540ea0900e80858220b5210b48292042641e042c0c484503c11800441c0010003110320030302c49410424100f619448403161030003540302d0b490141c0000c0c142414540005000c001e140b2a44e4070b4000d1041c40100000249040c0f0001410000e035409d038094030035482e05041510504441e6030040c0300d01111242007040d0301a03200c04907406044200802c0c02000781354505000240e80400d403110700151602a03e80c0c2120003107801511500303030030301040140c2d40e50380c007681c00001c0030442e91541e510b1130141c0340c00c0501072441c0011 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 429743758 1250 429742508 429742519
    0x6030c0a080a0c1b0302100e070e090a051203090307020303040303082406091c050a11100f02100b010c0c0906140a03170306060d15170d0c02040209031002070602090a05 74
    0x2c0c18418000d100c0703071360300b040848449005840001854001d2010031080d5124800c1804010000880180d4980041c40340400700244940000c1940c140130400714040d9500030080e1a009244d03036100326064201a02c1c3d01a140010086940140d900700020030040d44285c5030751950340340c464119203096403200c14500c040f40d0311006000090365480200e43d081074007183d94041e0440c01c4105c0038083d00030110010001e1103001038000911540320740d0146034403c00c651140d003424400c0b208440540d036080303c0c0030250340b000060801b8407240781c0004901e00c506151691010055455030105442681d020520f440e603070f4031060080c00ca14841d4800c0307248082d01e1030001c49285a85445484d5400c0d02c900808500110224415594520894140c59040c040500c800020b512400c03004e800c06120360b60380c29004405014071000040b450200696164070f6010f218401a028000a07501c1a001301e60705014103800040460214400341c2082d2313004280c01600e820041090081c0d00d0b090307410407446075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 429745008 1250 429743758 429743771
    0x6010311122104051509100c032307050303241801090510170309040f06030f03080403140c07090f020f032a030f07020c01081303110c06030c0a080a 65
    0x1414001a44082c100c0030125111002c981011032011600898001a600ca8608081c0c00c1520043d903000d088803800803516031107001c500c402d06881008840b8001008580d13507545007881c0300102d0604041070040141294501591560740c40c0c01c0d6030048440d409000d003803c00f1040d00d01080c089109000405940c41d02d03103803081c3d124180c141e136814400d2405d40c5842e00c0009010355410360b02c400050418050a00740ca40004c0050b0381c80c0c3c2c1004000300e00882c40c200c080c1e002c0082c18020a0200c9401c891001c99800054800b125910802803060341800800c640c903603400c0004600601001c2c00c403101a00700d079400c0100440036503001c0c05c24071490a00501003481c0449102003200e8020f24503040d155400452030040b40389a401c90013034540c0d10100403041013258500c1b80c806511440496080e81e90301518000107480c207440c140c90091151542005210002c0d00030900424140e01907411905030940c4400001d14581c001c440201c80301c031000c40c5030303207170103400066154001442c4001480794 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 429746258 1250 429745008 429745039
    0x20c0607080c040f0b131205060106020c04090f12210b030c040e060c2206030b120d08010b09130c0203070c06170604020a03020915041701020c0606120f030c06010311 73
    0x10055207001e044030421700050440407504110420304000c001b00c8586503203042441c2411078954200348a000058082d20141e050303039103001c1c031410810b03580c480d1189104103004c1e00c5200c1a40c0c0b00c2644a002d01410343c00761441800340c800c1109050f000700c20081003408040c0281400c04055070100750040c2d04000c8074040703500010034140e5020340c0d070540040e10351159050203a4540038107a2034403412620407801142250b4103402c607000146080c0c0700700c18500d908040903552130300c202032806d000038642001880050071742c40081400d100b0040c180c6404460650711502100d1510b00e902000d80c0c00019640f0800641c0d42c030030401000c032400d000320301c8490814103905100c00109107602c076940c00130702d501e00103000781d06030740d8003000241c00e00706004806020b5130035580c014007800d841130740c10094691001505000b100d800c0785909014089507240c19080c040c000340f1465601c0b2030780c00b85102e017281c0100c04101601c1b140e401100140541c0d451401c1001d210b0948501c41c500500b00803480302034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 429747508 1250 429746258 429746279
    0x6010f170105010e010c06050426071a1005040515030f03070c0e060105120703150b070809060f070f0602180405150909190c0911090112020705010f020c0607080c04 72
    0x1190b0342070074444203403030107800100d0b1040e09002c0c004120601c3c06080c0020b115010303907146490403950011900c00c844403a141c14081c0560740004211000c1e0411a0f40700e1414a400b0b240c005401d05120302900792540d0015094840c11203010050110a8044031a00c1ca82040010001c03682400658a848500d40b42c812420019001d00780b880410b040c0440d072682d01c64400c48074210001c09501000d8102002c00401500d205440c643e805c494140002c610146440308407416281d0150215286c60611003c2c013409401c1114102c0c444901406600c011034000c00c148008540700304401aa140c00b00740c1a41c400c4100c82040e14081e9140078208001400c0d49080f10002010031078494403255120300d41540340c401c20b0800b505061038540d0041040003000d1710f1a4060340c40c1f102d400e01c03149500c52030144080c0903c101841c0010701c40060248940101d50003001418003d1001003a10342c1c0e06c0e000e0100741c4c3c3c450200c000c460b0b4862000c000c5074a910110383c5400c00240002c0710b01e0207142c108a41d6 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 429748758 1250 429747508 429747511
    0x30d0c09050a15050909150f120d081806010308040608090a020915040912020d12020f0a0c0f080a11060f15060a11060a23220201020102130e06010f17 66
    0x101043d00303441184928013800a031410840003c20840c454688090105000c0d407104080314020100b02070301e1251884c280018904101c0e98030010600b10b1300040b030440c4c801d030024025402c0f14600d07080e0f0142070001031040d18041e40c0926051070351946031400081105200030111611780d084040b001d401a81c0d02c0e041c480e000001200c40182d030b1425100000c000b08420342c0020140358000c031000394403035008298045400f04589030000b041d40040d0800060788030300240b00d14000410040035030b840d8060311400140e00d0045400002d80e030350075075840d0090f0388058160b00100d2034074034200c08032400c10004a540490344260300c4069003003400010303a04518807103501348140d4003c80d000c000ca0f84901c800c42c0c03020400000f00e5203203051040102c070083c42180e01a4100340c080306a22140e100146042c14010b03001811440c10080105c0170454030003800c400c00300c0c1195020031009490403000514400a032001425054150801030005010001440410350500c00222681d50000b402c0361000c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 429750008 1250 429748758 429748769
    0x30a080604053301020f010e06040b071106010b0306120a020d03050c0c030304090906050601080705030a0c0318150e1b0f030a140f0106360e010608030d0c09050a 71
    0x108050721004000650740c0384012196500c1c0e1003602d0301c3c60007424031000c40d1844000c2a001d5811040c0d20702d003506c0c00d952001503070444030340c41100410001025241801d0344030f58246402c155a9080490441c1480c90a9000052401022040c81207601d054050f0303c0b1102088c1e03000f4a080086a8046000031100c2400982844408911808020014045020101402000d9076036071174840d882c090060524800c2501c00514000000b01154002c90105000d55819104c103421030342c0d0260400c024106888041c003c05440320760340400c600215000b4807900d0320540d0720020400032030004900b00c407400031810300607600c4080e40c903028002e5a00a0f20900c01d050b2500480126220042880d141c07010b140240500e00000d001d034a182c101046086400c80040024461039a40d44c0c06c1000c46101000762202883c0b0500c00c841d8a1000d000880350000e400d81400301d030700081c4606207821503107980d10200c400e4000042d01007460011b48520a01c9820a04001c80e0890500012078592a01070150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 429751258 1250 429750008 429750011
    0xb030a060b0901241101020c030c01091a0603060c0708041d09012d0f02040b07030c05010c050415050a0c0209130312020a0c02010810120c0303030b010f050904090f0609030e01020f030a080604 84
    0x441241741c1c0c03c0d0100d0304801440c0040f07036030f2040d003c16110300909071902d09a40100071a0341c0250f18008042d14180943c00c014000d2201e030311a2500c10758203502021301100c554004110000b40350a103485a040141ca1084540d0790a242200c0758609480d40b900715000d48032070441102c1285001501300141034600c0043c0060350508021840009109603041a4038411001c14942d081640c054001d240035031081c4000c2c004c1d202d143c03001b40c1d240d0007907000da00b20f000c1c01100b584001d144208003a06090301645007643e05800946c000c25007c40003622400c154004402071807062580140c0804060701080204510f0f10816804c0104800d00c1d9510081c108480f1b0004985d12a401098040240109030094213030140395142c10342c0004007900c400ca001c2800c06d45110003039800344103411091012030701c42c140342208580030800280031244003124143d800140c400045400780c42840301e10f502c80d440780340d4030301c03002c0c400a4549000c40904200b0703903200300001d000c56503000d403d03183c1042c01a2030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 429752508 1250 429751258 429751277
    0x50a0b0702040f020409061d010e07080415090503190915050705330703140a110f031006110a0503070b130218060411120c0306040b030a060b090124 65
    0x41d01030040035540300d215078001704c0d0110306400705600c440216600150215003c01400307110700080c1b00240b14015a061016001813001030041040c41c1c0c0c0107200302c1d000c148150800c1074a504648400406903410b80c0040b0300b40f4001c403011003100501110b5400c00c00a0280303040f10804803042541500c2c0100000401c030002080300410082c8603c030000100641d00c2c41c8400d1111001c55000742c20001596100004914118040c1c814100e030007406080a8110f0355503a83d5400142180c400d0391441d048040087c01010f0365140b000d1802014403000702100c00345803001c000d0420386c805401100d281c000e10f809000040c0c1c00801c480031541c2c8a601079505556241c600100341c0c2c6401c10185d0808030303444043c40860b010b03107415440350300c085500300302d540755508011311140921050b543e01d803400c50300451440301078280a107500c14001000402c1085000d4086824240f980f081281c07072540322030002156150030200b060140c9134040d490030b07401d10742120304101055000c0100080c4409540e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 429753758 1250 429752508 429752513
    0x221d011202031501060c23030a0c020604050a0311040b0102030f0a08070c0b0106210b130b03160803030411010c03120b01110d0e090a060f03080310080d03020a0e030106050a0b07 78
    0xc401d0865a0000503403d40c0da60355090007034104d151000c4203c6241c684120365501040c1e0502c0e85480131a10b810007581030121421003520002004407045e40d2009c0e05002c00180c541e038101030a00611312501c01030100907001c03801d0005450800f084281550014045031072141841015951400d00f0707403a0180040e151136009540032000000007400108000340046000741e00280c030503101c0d0760702803840c600c1e50140b031004004503402640c5445c1d000808083c0307041c0540441e0070080d0440d80050039181c440200140001100c00264020101900044108005c1c0b0490103082100006c0a080c10080c0e070200c0e6400605001c0101d440d03c1e4420744c2c44408041c1a44551042120401080e040320b00c0781c442c2c2e0801900100107085028880c080b210300180c0107a00310b015000803030703001001d844100f50942c0d64960303d94000508032147c1d110140c5c0c002500b070404100c3c552410002e07840042e034a46020400070000700b540c40d1071500136818650108450340303944a081084441440303403551102c0891 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 429755008 1250 429753758 429753763
    0x50c0904080702040c051b0d020717030903030706060f1d0609090109050d0305010f060e0a090b190303050706050609040215030702032101060806180105100e0303221d01120203 77
    0x4003a42243c90001c40c2c0807296003002c0200007c040805540b200385c400c1d100c50035074502c01d0003910030058004800030041400000d00e1280043d40701030a8a0170001c905011070300d19048240c069a40039141c030401c20020305c030340382140d010b8000710314244401c1000035950028140041d0100e13015140f44c0b000580809020752103008401d41c443d00b5100028006c50000b4007a040170301442880384110880020524010444d26080003409003032000a140340c030080000401506c0101500300769001503205142c0e03224000c14000e94825101c1d10b0f01ea001604240084900041c0464000c41840080c440581d076070300603500007112140c00c982c4c0d40740d840030717400c0f03045010321106220301407817505041103d44400e6040d40d043c0c401599501c0d885e55107000401034031070310013494040394500150045c0403d04104042600440c6142401c0c6207a02c0346e840402e155900554107a00300a51a000e005441019100d005000340701000b50b044c21030a0707030b0303000c0300c2d21140610032906084880c2d103058045441c03e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 429756258 1250 429755008 429755017
    0x9032b020307170109090b0a1a0a080604060606030b031c020c0a0e0108010b0306040f0f05121206041506020c011d090c0315012c01030905030a030b1c050c090408 71
    0x1088015501d90030000405405803000501d0300320503140c0030340040b4102c150351180103461500b048940c5d0198840103041c00081c0340409051505e46207844e043c0c1c4140d124810340c0341c0188070700d030000c044515141c03d05404070786213600100101030500c0380d081d00341e0350002a0360099501c0044a85103501c01c500080e407a110030343d14900d80051180b00005030070294283d43d50304807400c0c04000d003c150801e404041e203940048030f008010312039840d01d200129408140101d48a440303082128150b0b00750103c0140030303812083c60514804900002c10025041a000c1e607507941c0c2150a40d0860b0900380340300652142e10706001c8070b04003d084030412518420501c0f81d0604100050070700f00e4603003440a0340b44201d03441110405605030400c5903400c0c09520849410640071360091900c0d4143c0e100c00220720b0800345c0c504545040503141e144d04404540240000e00309680940c8000451401d00d038117000b1410060b01c00b88414903080000c03580860700214081c451103a0482d1206002d07582c074500358005015 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 429757508 1250 429756258 429756337
    0x50637150b040e011d040f0c030609080403140c090705090f04090f0302120c07090c0c050f1606140a0e010c06020409140a0905100506030a0b1f0e0903 66
    0x103091002801080c80d00040043d6900c22507898075981c0c80740c020b5407089991020081543c1c94900002d40401d000d501140c0005100310005a200d0795241c035501c040e5922a84262131074a800a0100100600140004c40c1511160042c012820742d00c0e00150585c8401030034501400400507180c5160303074484544142c4660010010084031406050801c0f00040540044016104e450100c4d0000400c0d1000d132840301c81200000e0840c181840c19040c081c000042c407810604c90441c840d84005002407040000d540c07006801402c000501006509142049138031010602c442481c518501c41c8000c802c0b00c0d8086094140044051511001220400090034000c1d0016101040108005440360041d00e100c00e000303407001c4402c7e2202480d69088031800d08004207070380e0000c01003a091100c0c075040309a019400074255041c5503010381710302c074170710900f1641e00d03c2c1c42d0f2190000c46045102c40010030041c007903003500400c5518103060400d590b0300c0f801f60401c51000c002005a03110041c41c584108203200d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 429758758 1250 429757508 429757541
    0x20f1323090d0228020616060e0f07091806090f0210030c080109050606040b0a170c0c100b12122113080c1c0c02120c0a03030e0f0402070807050637 65
    0x1091f03050512060800460072a481c90610b0704030102c400b4009031352001c500c2c0c0300c00500405d034500403040d4014004036102c0e002c125454440b030404128070303105440c0c0c5140620240c001002d50352040155002e00500d6490506187c06481100300354442c86090556104541c0040c10740c842d800003941c94003c0f54480b031400400041c4c103d01c869800200840d00c48071038405900340c0c2c1c444201c00c0700700d4001c0110070b44e80755110341c0a01030708828079084050580b402030507048110f2071404209052001100c5216200d00e00024507070810400303800312030807c9500c0f21207030314241010300340180c1031300c800c51014017900790200c2c27190300501050008000300501282c8a550b03c032001c600140c004805103a06901c10700350720165040035140461000881070004103030710103050559800755010414001c0403030b040400205103840e40d444510084c08900c2c040d9001c940c8503540d9140031803038081c4c020503040120390904c2250050540004070541980c6621320580c5900242d8140741c0d008001d150781d0300c403501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 429760008 1250 429758758 429758767
    0x91a060307090f0b04030f0305031b0d14010905010308030f150402070b06010e01090b0a12021603050715020406020307030302030a0905012d02090607020f1323090d02280206 76
    0x2034002c40800110340d0b05441c100c0c55141c0c1d4001c4000c2d54080c038400580444403000000c03000078030400055131f1000c0c98021424580000c0e40702010140c00c5094046015035407076820f050007800c2c00050b60b00503c1c42040038085581035a594804600000d8201c0c40e006401c84003091444140e80d0482001d1100508110348270030b21400c01c1081708405a5120340401c90540308142c20b075108600b4013080c1c1760b11807801d070715000c6a1074085550340310690a0020255003032041442c0300100001c05007010303000b036448a0310381501c0d04049403058140c440c82e0466510410041200c0313500801034803405074250400507180c2d40c800c2040d902030040100002c04035480c28406130781d59106103d4003c44c5110051401101d4407984121204a01c60410401e6100800380400c82c018a80796038901c811000103007003204900400007801042e2201d107810440407030710054030001d00e030044210781948403181100400e6607954290002c1d44500701512070300c4000d030030030050308005603540b00300e4915141e0140145554 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 429761258 1250 429760008 429760021
    0x121e0306060d0926070c0e0c0403080409051807151d040f0903020f030403020d08070203011d0c030d09050d060b060c19020909070e181608030d06060810091a0603 71
    0xd90b081d0059113a00021052080252481601c00e4682081d40103074070780d0080d414400015103050004103150030044c1e0420001c0f0000f50740501800040c000c50390b0110b1282814003c901c200c82a44004021561042c0b5082019100c03e004600c1c41c00e01c02c1c1000040900c0e01420100800034202aa0303402c039007000e0b0101228141f03680541d0415000342d00b560505204082002e0701d0b40318034400603600c100742400c1c404c04500604010217445100900002c0d034030322428520103d449100030000e03441d40151414410600f030034440d554120314107140c00d4102a0034900051048824000d001c0e185a5a0320103203002ca4031541c00b2138182c00d24410454501052081e044641200c21f0740e804c03400307058948080b802005000a81c1030948500740c003915030603554490700c900616030100120200d40304030340f590300000c40d203e6400320241501d0740185540b902078034848402e8031f0960744002c0800110200300f0a040d071001000c2d2050764030003400030508440285610300002c00001503103078042d40c00010b01c000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 429762508 1250 429761258 429761273
    0x1807090e0d080601050f0403060b060d0c08010e060d08120a060b0c01151509060c05011410050102010507112a190f0e070e01050901110a050609121e0306060d09 70
    0x810010303a502d02e019541e0740001100c0a000700700c140301c0400b1052000384002079950f003100800310000340010b0709113a1106841401d440c4151b8440c030210f40c201340103000c40c07040b0030029075100e94241d0341a00040c00c2c550fa110b141f445800a0300f45c4103012a1302240106d0b5458005800616500120a450b07016582d405402448003003100742241604c003000151148030041e00031245034082c0c8800c180d913442c00009582021308036600701c0b03e43d541c0d018514510320105940a00403611440010034050070000068212000508880248a04001c01040c0c68100081d02002c60382c07140d81c0c0400310200c02c0c4020000d41050010168014082010903107501400484d136001c40d04030528543c006a41c030b640d00100f0701070030f80d0250005020403441000300d50145c0c00600003020185411a000710a100c41b140c00d100c54444104e4903500100184060702e0420041e100000d05520801031a0441c00030202a584000c2c03807081200140100004800d0354038031060720b071001d841c08414884884613250105 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 429763758 1250 429762508 429762523
    0xc0d1103090106171504080409020c0705040f0212011404060308030906040501060501051c020f16031d01090623133206090906041116020f030c01081807090e 69
    0x1080381d8030f0054002051400001c0e0101603240c50006000c1081205101118000d0014010303510380702d0400000443c00c400740b00601c400140c0801500c1d0850401080006460201194030300c2d40d80180140d5444580b5044580d04407041c0e04111054104d000b40840c0c007400d05640058140c2002004001e0841780100d1080d104521620081159548480064074203014241a45802181c440981c4070001c03120f50040610401c420219410300100408180010784c140000314001104081076807000380030b0980e00c07800c003602420207080780b604104004004600340122442da400e044890010401c1d0504202c038200d00c0910300d03071058191104500b0301d010460301450f0702c500344084940c8014040046910741e601030024246442c0c16048000c000340c0480150010b503026a0711006107034641d03010f50061450010a0341511070448084c0100009181d0306020b083c003d17001011041c115070383c8580d080d94490600d9251001d22060f0002d400e26040c00341c1c100350303540c0d441c080c03081d00c25640010340d10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 429765008 1250 429763758 429763771
    0x121005010311030d0801060309030509040606050706060e1e0a020c0d050703020d050301260f0106090b090c182710030b0601030b010f050c011128140406080c0d1103 72
    0x404102c0850707070605030366400070740820001800000041c02030501c45e41010001c54000d02d04503017017920480c0014100e0f0026400394005c200002480400c1100c640660b400a00c403d07008078030217250000607030156490032207050350b808843d44001081a0300f00e5040d0360003020302b1022200c0200c0e0046024000780e20400003500980310308004415050310610890381a507d03401e1170b5203c917050200009007603032400450000d042c007440c0c0c20050280c0e001d219200042105c0d00011601c0c484010078043c140902420070300901c1c3d03003007080d4010084450a144401102a14805402e14200c101c0742050541c101480c150403c816040c040440000003122003503038052003000c00c0c0b645800c00150219051461014081040d90b034100b20001d020b680034141014007140086a1a400e10340440c0e940da0101c00030075012811040822030108460a80c0440c0c0007240c20700611704604280b00c200e940c0030f5840703044100080369001076201c40c9402d081e202417040082080c031000c014a001859a50070451760b8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 429766258 1250 429765008 429765023
    0x515130902180903211017100f0204091508150405120703031506081b0c030d060b0c061f030f08160f0308130213051b0a0305040209010b0711010c021210050103 70
    0x1d05072545d001c4948900031a0701143c1a6201c07403406120f011840700321890320880e40a0708504500c081201d00403140344011500700160343d01d081009200c2291a44052520700c000c40c0c020501c0002e00c00034031070780b0595107002d000031603656501d001440c150782c003084006c10b5100403d0002c00c05425820009140305181c882c1c030f98864840104468103442102c1400c4202980183e1080141c5800010304e003000414090324640140201d50b00d00380c6090340d020220654002a01c01e080003414002c142d0090412190340c0c165400d4508087c61030003290001400081d003500c086d00410064004980c00301d074149006a684405c181484841d260200341c090300800c1c3d0120011307a9030f00d0ba89150702d00c02503005000d80ea52400c0d0400304c5000305030060000350640100d00718005564170f00009088690b1140d40c010405240500c140078032000b0690080b12421400c1c0000c0300040c401c58040440c0900c20710307001c10184202c1c00028240c4034445c400c20840e0241c03001030b01d03034810981c0006050782d018104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 429767508 1250 429766258 429766297
    0x4020d230106351f0e04020306071e1103070213050f0c090114070501150b0a090e01060512100905090703060e03190c03120c0906030515130902180903 66
    0x29043c81000710035450f0180780000030200b00001040c2c480680000707020740404180c1c154200d0303520001c0d015800180310060700b08100411444c08000e0260300050f649845000617002a0145018034103020343c40062201007103908100c980e00f08250340d201071b0000c00a070303621038440510710002c00c2c040e516004a4400722000032105580c07101181d02406040c0d403001b424480382c006c0324505070043c4000f11003075500c2d180c48290442040c103100001d4810040c00680d1001d2401000d0138000b100e030b20000b070900c2c01d1801004450303013100c20f49410b001d180385000b100ba5142001c4034104101c0360001e06019240c8018410792aa00089007020b6030301c200400c0015044800c0750503520300400503000c1c086c4010040080d0003038891022402481d07c64200400e0508015006400352008507000c2d42c0013540300344081009942c140031703483d0081807840c14510340312122004220110764650001d0300094440d40400308640f2210030000c240c110740300c0c1c00b900508201031816260f5111486075000c6420481 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 429768758 1250 429767508 429767537
    0xc10051602010603030e01050c01060503030304050d0906020a05060708040618081b01020f0d0b030a0f0b04021c0b012d090912140901030513120206010806090d02030904020d230106 79
    0x800c10f403e070f0b038042c3c80f500640c806040c0110b60560041004a0242d501c1e00d030001000c1d18108040c6000311f1081c00600214074075004020104045076002200b1076105c040312401103440071841e10742010044c0b4040c1c0c547c0d5228203040c00a0140c2110b5081408040c03030341c100601807058007030329281c1d0728031541840841d80c10080300d00707034040e0515000079203504202906003c01c02d540b0038101a02e0140507500d0010f96621201030701914020290740d0011481c08100862800d1850b40108041d205019464030781c4544443c0b0400c4014010304030b50142d480d0140b54181544118024850321407003074904015141c7d00c080c03000e454000412941c070840e46100090150096203101d85110b1500844d50400320840f0044002d02401b401c0b80014401c3d0b01391101c0410342c1e0000c146ca5601e01030300100480d5240c0301402c0d2900320010101c2d4640d400554150054940c023001312405401d0840e8096183c4002500d80d80041060a80b00d01a000601400c0f40c88422002c000d60b040300c101c0e4691301e50754031118 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 429770008 1250 429768758 429768761
    0x29040b0304032010050903090f13061d1005060a1d01020c0303041806050f030a120509090c270a03060504021201050106092309010605130f0807030b06100f0809030c1005160201 77
    0x12318909a11a941609000450410007101e05245a5108011078070b02c0d9178030720314038000f03c0080300f25400d55861000c0100e01107410f4020700041c6000c0c0c0d003140c039094407603800030083c2c680c0d100714400d100741050320701405a10030451900100c00040a603507a80c2c1d03681a0aa100500145011034014104400010285004540c80040e41c002901504a13054640d4542903c0340c0b040704070b4402e002083c0181d030030549449884520804100c50216601c04c40880c010740280000024002002c00152081206ea158940d05004480c1d00c5280072a142c0c03078620024140a02168078020150b20344800083c00581c001c402d0b1040f5440c01a92075280040d238081141d041500796001c2d901b00105800401c0721501c04e100a000b140c0c22000b031652041e071140c8100c50840e00650007240c25a008240a2041c031003003031030540c2c03c0728040700c41a046400040001c1c1400110070744007414805260000380c009003082c41111442c03070f00e09050f5101081c000703007000018a42500c0e031591300c1a00410104055005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 429771258 1250 429770008 429770017
    0x2120c2d100509130f0513050c1509100207050d0c1d01120b07031b02010605010f0513030b07110a21031505060d09080f0429040b0304032010050903 65
    0x6503640b5450b090028042c040d08130340c00350040014682d501c8070541d10050070b1207018002e95100078003d03080d50140c1010f44c6040c5090001e81d10918101e946102451200303011a1040f030401d842006001910300b806230308080701640501c0c1c00c0300603501080c040200c1c04c500c00003558101200016041d402e40302520800209014450060312841c2107d00441d10701072070346500214610f0041402900c1d05601c0841030740c0389841c4005031791903030340c103000e10340e0010805451100c85203081410300c0302c040e6254080040301c0c03001038102c440c0c0d0750214441e10b04c03030080c60075404101c03000c48a050301d035480c02205441c40c0d1400307555000301d07850075420b07868440c0c016000d00220700c07040e03000b54030304020420003117601240000c04040c0d6200b12040024084c0c6018018988040010546461800710040d8400101018841c0702d42d2030358010440c1031400b036040c2c0d01a9060a4803947d00d0b40e46610b015500c8050116001040800b0701040b0382d0b2607800041d01d01d041c900c0c104810b02082d1680000c01e07949000c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 429772508 1250 429771258 429771289
    0xf0b041406041502090a0b1b010e031312031b0b01030c0e061305090c18150604030f0803060d17090f0102071208070812070507030f020607080402120c2d 67
    0x1100080321410f6002d030300500b024600c01030018444903568142d110b41e0b40e1000c138241c09460882210004140c80c00e119022210f040c41014510f00400d4032203242c1c1c0140c4a01408002c41e007400002000d26110300c081c010805010300b9246641c0320181002e8030300d000c00b480101c950306075101c40072404010500310b890040700b01405404075070004c0c0d0403882c050318008041d4801440fa1400300003c40c1e0302e00c0e0075444101c565000310301c4d040c02e041103c10310000c440401903000317032010001000015200300c04801c0c840d400800003a203070384483c2c0000d91105841040a80307200350010800c4071420600c8001d0850721400c8849102c020b01c2c50740103a0b1105410300c921000042207400303000c0403401c0c0800038043c0b188220340c501e103040f0303202c41920800b110580c0c1e11130000d040410060105038104108032040c000c03c2c001016580340c400301c0189101c00041c4003c1c0a02c1d501c1c4800d1071907000400002120340c1c00108075080720707806113034000e030b0201d140c0d0004070700200804490005820712240b032210300b01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 429773758 1250 429772508 429772523
    0xb0a0b03010c12060605041a0721090503010b060703080415020409140f070c050d030207020d0209010e090609010501081f0e10020d151a030c040807060530041502070f0b04140604 78
    0x108c2042100203504150810345400b5071054010078030b0b03c55030b01e080140f0758598860000c803900b0300d0285800c4400064007035000b8041004040c0c04030780c10401c12030b4016403200050300d6221606060001034040c95200a001c1424004e0100c4444244c29910744558245050700b40f4555030300104642d8078540c1e101c050110340000c800d080b1007510a400500c05140003500000500c14543d0100c1d103050740c240d011000c1100c0c05820b0004910091001940203c00f050091003d0b50400558540760303449181030100341c014051040c0c1d1010341c940c01071720326200c03050107407aa01c848800340c110182d8440043c0800f50351601030303051803140c04015076070103403200104503542c494680c0e018048543e1020340507081c0d05a09000000340c0300c00401030540a024141c1e20b00703072203059844464024030002e0324001d0403c3c64031500c1ba01d42d007402c0c91101d030b849a000b241c000003440310717444804000d104480d0f000e042008160120740a100c010b62500e405544140070250f1130745880c251003a1241810f581c02403c21 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 429775008 1250 429773758 429773789
    0x6010e0604090f03080c07020607060606030e0312070f11100501052106040b04210302041e05010f0f090b0c0f100501061d0307091d06070305130b0a0b03010c1206060504 74
    0xd105c3c00034581e02040d8040024505030352500000c040e9000b60340c0446049444d4601030081c95454096103d826080100460a003010a10741d81eaa0b00c05c0107201d041085141d02008100d2841624800c1300082c0042c11f46240701c0760100800054070007405014024a80750340700c5900c0004140b501001c011a050203840d2589a07079845011000c4068010781d442c510704148000764180511100c84d45000a0310016502c074a880c0c1e801c402c03210803203407070504100f030035200b0069640c01602180b000c01440c508100c0c3c403941c10034156800307103050700600f800c3c2e800494000303003221000070b000d03008800813006c4400104002001a068460074080c3c000042d6840c100b813105a50001802c00003040d0080540d0210303034540c0500c0c4d0480758940c0303040c050038220502d1102c803940107001e0250401c02900e8240614603042c2800c402804525000030840309491300010089000303a4065098868010002e210345002500c0041c10021780341020806280341002c0062007901420446040b64080031042d10340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 429776258 1250 429775008 429775013
    0x105030d0504170a050316060606030203060603191b090602060f0c040b070602040506030a0506010806030a211b03020a0201020f01020a0804030e040f060e090c010305010321021e06010e0604090f 85
    0x110740724501c8a800301d104103180c444c0010b10030b00280414070340c0200c0340d03404d0740010704090083e03980700d0b803001c82070510400034000c140c0c541200b00c030b0780314140a1040601c0700c0c2000e0f00f01d0052480050003c0d01300f40761140240b0b1140c0c0520181f0071140b0580c00c9230540d4842c400e8004501e039040d2050580785c0c0d010041001464561750180004034014440142800c4d83c6501207401d60b0300c1150a07104050350b40003003111a44c0c0001329113030058003c1c0c0c0101458913242e40c0752441020420680c000c1d0130140c2c214106143e100c2c105010201d8014103540c00307152401e00d03000c1d5440c8442d4100324003500070150002d403125014400da45022009580b000c0540d00c171600c045e40c00c0302e0034207240d81c1c0080e1104442c0e00070a02c41e0003040014580c03d182803e0030310345030a2240c00d043d07400c1c00030f504060401e40100302254072440c0f0150440d4204d111700c10000c4526009910b041c0001e101ca500c004141b100c5001215001314100d812035501c50010f4000d41c1da824101b00c2240e40703021000b425802d032984507801 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 429777508 1250 429776258 429776279
    0xb091302030c19050d06030809041b0e0112020706090f051c020d0f090801150314010902031f060e09030c0106050a15030906020d0e0c032503061509050702030702090105030d0504 78
    0x2120569030402d24907141d140745d040750079a40580c20690f0003003c000b81c802040d00f450b1003881421214610010309520f82d141c401403050103418107a604005020755003601c8120144d04441c171050740248200b009240728500300200c5000300c6400c0d1610301a150384c04000344650f02c0801c1c0282a180d025003689000f41e182035030300c030301c0e02614041048a441c1000c02d42d50001d1250303005422294000c02515451440e0218501c0c4002d105004035904208032000141c400003100100103d0740465003084840751f4842600030308207a07110902e0302d815417042c030048035008030040c540c0040150080c04220b44500c1405080c4000b0701c19141e14640401c461001e00c3c0c031951041c54102d03c14035000d0b01d4210604101741c00d882521030165803036040701e40740741c5a9140410010b8680d2040c000c40da0890000e000452546c00d00c40c1c4001303010349481c0d06040348003400c0030108a0152118400412580c10300d02c100950b070b504021012401030440d0b10000c00c03645000100600200107a0b42c440b45042d007001403034031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 429778758 1250 429777508 429777547
    0x90b0d02030c130305061b04080d030509210a14070309030210090305061006110606010203040b0f2205091003050d1101060b040306021306080907210b010b091302030c 73
    0x40d42e1105015441401c5104494800158050320041c000d0703092007007450811010340c0050b050110010001044950404100d40795101c880d0700b80060b03983d075100d400904088411070b02000581c045917040704c4900042c0c0140000c1441d980e16042c81c03044030852070b50607104450024000c06c09020703040005190402014000031143d1402003001c50ba40e0341ca19141c198255464000785410403028007a16500c42d60321490b1901d080300070141070401c900080d4880c4140e00907100c6282d00080d540807810200070403203c820f051503640c84801d00380d00403280f040c06118003500d4400c6041d880820941182100c0715800d0301c0d00840034210b40c1076505001e031608184014403811f995264000003580011603000761005601650001d683e8082c25655180d101c10141c20100c1801640d40c10b0180b1440d0000e80003040d1000c0c00c0980305400c103440c144020400c20918010550502c020000c50829405005024001001d5804440001c0049803001c1a07000444440140510030301127032540520158040 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 429780008 1250 429778758 429778771
    0x6040b0403050720030d080618040f0503031302010f0c0b0f090109170918070e0d080c01020c010e010b01021b042027220b1306091506090b0d0203 64
    0x1460701c043c41d56400030884040489003961000110100510b05043c424000140d2040c5800c41061600c00c2c0000d4014070304c200e582c80510441e000103020800381310a103a503841e40000443e0b80f07d103004105007032011180002240001d02001402c80a03d0040081000850344003912076082d0380c515540d102500d1001340548065900c1b080b0000100d4004003103407000354081c22255a1300e1245005120401d254400d0280c1254a09010805280e81c020f005a034019421100960307020303102d051602281c025555640700c1c9520008000e0031101c41503115041c0891050000e20101c0300c0d400059803111076062840110f0324000c04102402e10342940311150710450b904035000e4020f00341444002e660001004080380480c0d5407590030102101c0821404454001c80d60054403800c03200d005c914410000b043c440142c0d0f101c107400300d1150b482400030728028038045001c00c8219596640c0d2000780018003542c404640c4040740c040b40c0107101e64181c40a0380c00300c240d942e14183d0500090b100039800200315 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 429781258 1250 429780008 429780017
    0x150402040b060c010f05010e060102060103110a05090f06040e012c030c06010e042033220905040c03080c0102070602130303030c08060a0501030b1215100f030506040b0403 75
    0x400320ba55807402900c072540200303000203491402c203c464411240e040c2c004410700240c036020046240c0e03001440a040d294003011400b1a42e150704040343d100707241c81d005998042030100070400c4000e90604524880e00040301c0604c0f484e800c00080a01b21080220740c610084045248a8003400c40c0f24404900000c1450840c0d19008900426a04020003038000d00c0580d00900180420700ca1f02054005641c0703603100e90400801007000000f010000f4034407a01102100d219580812075010740071400d4075080007901c0a82d98100d17002103003c00d0103c200151b581201007940803a40e6403c9100d0b017882154092941081182540c80d4010b4a402414814060f503400b00329a8000039045d002500310742c40b00310040c50100d804c2d4a00502039920424540e400c0100c0c80e01044110b81e9034840e503900300c440a00340080c0002c80360001c261240e401d12038040c500e00c02c101d00c400681038503c043c02e108003030070402c0141d202d440380e141d442c1d0f401c114030014000754032441c041408034944082003a0840c0c8203040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 429782508 1250 429781258 429781271
    0xb07021e150c0715020f100c090302210a080d0e070521102306040209090604020a1407200d0c060f0504150201060521120708091f09150215040204 64
    0x4107540e10409080c1350400503040380d0440c00c1c44110401844064006c0054144154290050024403280542c400a0f11400c40342c1000d0080d00c03110b011400c1860200c40580d604800c1c3c0f030519003c0d6a000d07214011420b8038051030030140504c08548042a16402010810013013440c4d0800c003061020114072900c0c030702801e980d562894400e8402c203043c440710384a88100314003e848164080c03980041859004038010080e60b030b09075032003440d400d03401101145c0050303c65440307031011140010841104113141c58000f801200b403144a98520f049924449100c41500c0d844a090124001c00d04100a0401041c00300c01d02503c3d0192240c82082101450120f0070b0558504848101c0308020202c0400340c2d40d1980103102c0d41c02e103804100c8900038002c0365a40d607090307000c1500703941e0b00795030300509100d04000c213951703003005500c07011582070701e1000f4040c4641c403040e524500012840721040d580811907200c80001c517081080301c501441001a006021451b0320140c1140b80d001000b80101d81c45a07a418 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 429783758 1250 429782508 429782519
    0x90f0607020a020102210a030c0504050a140a05060a0807110114010905040506011502070902090f0402040f091802060d05100e070f11070f12030302090a0b07021e150c07 74
    0x1144a205040c01d038010080c40d00c42d40000b90900c015403c83c121940d002403080540aa111401c44000d5401460001000811440f045403030f0702a9810007a0302582280001802210910519070401000c070b411130314070765650003089a00d00c240280352000c10703558400509903c0c0194100011142c1c00c03000032520131751915000c149020242c02c0955019a98818441030000400129016242038456880c000d0309003070019540b0541403240003000c580004140d003c5441e0810680c1801c5000350041d511181c40304c00c00c2001070418040c5030141864000c081e001c8841c00c0d842c0c01c4400d07070050030003803401d250605400e000c1c0c54000c280b81d05100c417140002410103c581c41ca10321861083d5030f43e8003010310300031000b410a10f08481d001150350288200f81b005038840051402200c044007400d407602c1520b03160030780107809001c81d00c552040e8180070000c2d0100c40c580003000704510841d01031905892180c040031408540c40700e02508000c294071003d032142075240050085a8919007100c4941e030307561 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 429785008 1250 429783758 429783763
    0x402010c0209041b170d182304090501020901021207030923120607020c0901350a050d030f050415050a1103010f03031808060615070b0703050123060909090f 69
    0x90b80403040458500a03004540301702400381000740c528a140c420700145000d441908644081e003c3c04017000d9004041e4907506a141058411402018006200060403410b01e03e000790000b108141c003502a00c04c80e25510070480044a074895491748a00020506014a14401e01e400040301c2e8141450368001461030390300c41001e071500d03680301c1004000c1031806800013800c1050803054079005a8540300148104900603904103082441c020b410441c001903414030301c40061624030001003502880000b4010301402281307014a00005172401d0000260f908070f49800c0b41c0f4200d80241100f06004040100c1c24956002513401180b0040d011490400044030000c80303034003c2c0c0c8a0300c2c1002924508004158024902c034130305d00402d0308985903c030b180140403510303000002c1103d48103000e00004500d0031091305041d109155040301c0d0000c0d8610341a000036000b403c017070207190364003041c0100010120024050b40e6140500140c00c1701d0800e000c0c981070000424000d4054036240c0100515540a41d008 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 429786258 1250 429785008 429785063
    0x108060406023108121e0d0b1f0306121101080601091806150e0a0909150207030503100504110d020d1b02030714010c0905010c020409050303100801060e0402010c020904 74
    0xe0f4401500000c1c60f0564140c581051411032000c0c0520500070000000c0178150302c2d992982100c11056925215610400300a145c502c990341d500041c8428901a40c05003988280412012901d080001c181c9490440701c610244070070080c44000c014100d80b0f0a540300326041ca0708540d040c1040c0740d8281d15602c15100d404070603000d061585a90701030030407041c1d100203142403543c0241c0c2004100b000c0d0b581e010580000786801401c1000391103401100800030072100881c0340e111400c0703085442c0c100c1ca140040c455030059420412628602c20041603500e400d115181c080c882000a59203460354000c090b10181d0802803440020550b52109004454041e188018040d15180d01541c1d98801910303245451807144940709a140e07140501c0d1005c017075004004d4400f40d400034240b841850800d4400140988101400240680004010302000007021165242540c201c00000e00000b525240200c0340c4030401c41f0080d0010302100507100c0035003004003003150003034000c85e4080d0342100b5a034511620b5200d07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 429787508 1250 429786258 429786337
    0xa0c031e1e180b060a0b090907120920030f1b060d0207060c020d0e0d0b040503090d0b1b03100608070207090908070201121503120e1203030601021203010806040602 72
    0xc070b04003000300048000d40e1050342141c0495006003001900044c80c080c4445140c001c09000021408450144502440c107032803102040c0042d89461421030889003108030a000c003011088416200c6180c04204404c03046c54442c021b1201e1545c546454100301a00150f49810040400c001101c000c0c003400207100d060f004000120b00c000d2040f4009280c1106240d41404010701c2d500030355100d640b5076418405090300400780301c0c000c1d03c0d00e0402c507040d881203c400c076900c0b00020881004120112408a00c5803c2a07020010020503142005c402c61000300d40e90495507c0c65517045c8035131406910b40507000b031054412108826115400d480c21550b050400303840511011500d0350444d80d00c502800407005d17961b00107100c40000000d000e41c7c9142103010041602d00d4010025070202d1040c1090429000c0050840800c104c1868015483c0e0f442a0b0720240140100107030300e001c4402d444100e0307040b02c0b030b400c005003000c0d80c44e61030702070003908841c28201943c2220b88105d440303000d125200344840003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 429788758 1250 429787508 429787541
    0x9010b030f10030309140418060c08070f08040f0f02030706020c27060d080c0a030509040b03010b012102070804080c0102010606020c150f1b03030a0c031e1e 69
    0x345450301d200c4401e801042d4030050001c04030240006a40300103000c04485d180c02c1c3d59403144003c43e00150142480b001500341e005c0009055405200d65900280c80d05840c80d201c000030394842c203c04071035054040441c000032aa051002c140010000d01c40c0c003000c0c41c020701806001d4062680002c0c10040150f100c500180c0c04651040c1b1285044400007080f901f000103007100704070600942e8000104010001486a13a02800780414010b404007101c008013200001d41c1d00305031442c600603000f5009206224000c1e460701d9412a181d0070705200310844008140c594582d082c0f049003603442d81c0c1c0240e900501e4466003e010400002d00000c0c041d201600b03060001d04140c8000710002070843c2c1213a801101103500852400c00300d030702c1d18000300380c50420300c5426036624014071000702c809101c2c1c40d003d50385854170600c00390500d200200103180100c0c004041840824010341e404c6080c0d1700c1c1404034056560b030001c1114400c00795a400603085030408401403c1d0095442d40076011160907541c80803110 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 429790008 1250 429788758 429788761
    0x2b0c2c1002030a080903070b0a0f0912181406030f0745030c05012d020a021806032a041b02011112041211010221011401021c0e09010b03 60
    0x940c0c100b4030301381d48028a40010340c1082c10a40b5054009000500b4201d60169505c1c02916000010742050040360b1300555102201c03603005c603000300f644000e40501d80d2041c002c0080400e1040440604444a010051075a821625140c0501140c418081e0011040c80b240070f10340078080321844000003203924540c401b070758601c02c0d403900d541000704080f052401c2008a90400c0c80020401803941054810a1a0903090340c3c80c07028100d00b2850208003204031089003038400204055000401a202d07500c00c3d528400e841f800002d460020b003e0540f0303aa0392540180000407076000c18010041c08110300350300e000e1140b07a0008041021621225007800c4e0392001090110069a0240101581c00a80c916030320301d4000c02ca850703080880d4018100a0424224000e01e90029124900d44202603a4000003155100e000c6100e20031401c80e41800203032900d00031800003403600785ca04203640c85030340183c0142c54403021010b08061210040361400c0c003404582c2e03614004584905020901030034240940d56500d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 429791258 1250 429790008 429790027
    0x109060f050103020901020a120e12010e0c011b0204270302010e06091501170102070507060201021c2d06230319080a0c0312022b0c2c100203 62
    0x10440356005541454010000794286903800509206c540c0d82095044050401d4410112a038882c03034150035030f0203540001780310884c03030b010751000d0058540301e0112000c07103683c00d006545d05661415412404401000070744050b05254110801c2640c4c03051806481207a1040b401d031382d06178400000e50060390754250400740928100800d03500424440c005100400c10000e00c0300088905000e0304000c1d150743c003000d4075002025012303250210382c04410755000d681c840b84024002d4000c80f4600320345401910030412945010320410311159070300441030b012404100401803d450207145144d059590b86c050014820000700d9038800c101e81e4904200382c503800304d030081500d00b600c50060203030341c041080c0d00040021080011a000030b519401e0424800a40381800e589200c412081804c11034000602c4040300494240710a207000c1c480020340d600e003031070640020304850311103804101168070700c1c140e01e01a1a4821104c02d61482120f03604c1d62104081c0081407043c00c894608001607840032038038250 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 429792508 1250 429791258 429791279
    0x807050919080609160b18131d0c150406030b010c0203010e0705010306080d0c1202010605090c0d0c020c030601140a0f140a0801091703151f020f030301030f02060a020a0b010906 78
    0xc1d00d260052541a00706e0810402080d41d200d0502c240c1040b0b4003826120020fa26090f0102d240080480c2c01003107984410994004003803580e0404400300d02520500b1541450000c00420304c01440ca4111800d00d410808250f0051100d540302c907060180d0010b800340140e03000d000390b203002c00c400b0740940410380c6042c0024045c0c0c2d40b580c01a911541214a410038074507803002a00c0d18540d0000103143c1103028206050780180041e422040d000381444040204010150700109034081b04031404010400c00c0d610120b03100c1c204020301d59410b801500040110381c00720040c400076204010103034030301300d9a14506041e80d58203c0d8005070a51108200c85c3e20685080c0c1d507880002d004a1f00240405806a61041e138205a89002e08400300008000304950034600c9170250b02403040641040d4048403584040711802040300c0440c40180311b240c0707401400d501e003c07044c1e0381220390064104200c4600ca608000c10f9030045040d60303003184542042480400d00704160207000300301803040011440d040855040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 429793758 1250 429792508 429792523
    0x313050f0315180f032706120403052106222406090b070305030106080a0219020105040c080f0316110a091b030209090612031918060f0807050919080609 67
    0x207043d081030104035180001e5040c6c40001c0c0b01c28104000300384160000140050003403c0c840c03c1c80c40340e2102080201a0028002c0082114903007158240018581c0100d01d10700c012183c283e0001948201c40d050340495034092211180b1114000c200c1001030701e41440340060a03400d140d648190044104400e84d0490002d502070170300c040d800b514080301524060036512045c401c8500300403096001556111603130b4142d85000e0484245540020011000240a000240da0554682006090000b500607000481c0c03030a0441e020040c6050560f84554240c0780d400c1444107a501c088060a61041c0340d8a07800b8400240c6403036413002400c1441c054694550074520640390b4145441004500c50340e50b0ba134000307654040310480301c0c0e030545440001400d06600903400806820400c42000042c002d810a074010100d64030492072071410b41c0d845500b294551034000d41075000c1103805000c140c03007600c64401041e61540140c4100f0300040c2c80140c08941204c00e610460446d003001043c072581440502548 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 429795008 1250 429793758 429793783
    0xf090b0117150c0306040204030614151c03030e0c0307270b0109051927050f060906012007030309081005071d0d08070507080601080313050f031518 65
    0x102001c00b41d07120580d1403240c02803c48031100c100030001644607a10303501110091640074400b402002d5546044070014103007510560350704000c2d014901c400d400c1c080c10701203070003502690030030314003590380c406a00170604404405c00500801c14103040c5903d081041c00018150108000c03000940d041c0c034107483c0d290f400c084000742c0b4106904405181e80c081418030940b00100d404a038900c0005018203402c8245600c0350106000c81c4841680c85200041681300e01b0b24130201c1072186a0f03c0000c1114500030407200e00303501001140100e0102d5110381c0e041410b00b103c5140300203140302d006460758900241a0b000f10b002540000d0309001c007a006025001100c402400140b041e42040c84010b0a840c4083da00c3e0003006d1030103010340c0c0035135462890715a2455042403603296030f000141040c1d5200c080a00a140b4244a0300e00001080440042224400302e0804903150f80c050500302081905c5a414002d1541485039810301d10a00241a11681c0580398940340b10309070080d4003180ea030071b114065068 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 429796258 1250 429795008 429795013
    0x6170f07030506220b070906090f15080c0f03010806040606120507090c02120409151508040b0a09021c03020105090f0312250801140a05220f090b0117 66
    0x20000030b07000292680d0000302200f09611071941411240039413400218025060309210410f0000381a045800d100685a048e41c13202d203042c2d1240c91401041429108001507a20104440302007144517031780c010f4000c0e040003c10351500666195440017500203801c1400150024000d0004200f890f204900003008403004000d010807060b1034943d00d4201d2485221446916907140d41c2c20382e8420f00950200300880c640c035980384c079251560040100a100500940701c00140303404a02c0c41d4901c01102c001028603940d20710503544660f18000f40d031001806404850f52035020800c01030340c8800148415400004959044590311f0400909490024016208540241114040c103250100c21a007059101c040c0600342516450b6401d2501801074001c400140c1c407100b00b01030325550040c0004d04072980e41c40c0304546119944108000e8a000d03100f0240c0c003550030410005040c0c18183c0b280485c0d01029400500f44c0c2d0304042804c1038274044c0d5402c80d110308480700103000c000c0d10145105280600c1100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 429797508 1250 429796258 429796273
    0x601050f0f0d02040b03010e014b021c050c0d05010b031e0615040e011716091503061109031218120f010f05060f0d05031c0f06170f 58
    0x11600050144801074019505c9030807000b0079490940284040045c200020004c00756080d04c14100b0a04814540001c1075600d06c45503c54103c21b603c5a0b01e40d402e0441d410908014021018000c1d030100160000006148100030f480c2c1c8100d10685200703000c00c02c00280d8501980000204840c81608032000c50002802030100583d6001404941290020700c91031254a5090006100c1a54070219400d4101d00041c085103c2e55040c2100b412200d04a030110325409410907080e8070f03022500c00146643c1441c540030400041c032600302082d040000c02c0a440703841e88a44440060399010510030256040c000f88a071000c0c20100303c01080103081b001810304240385072966400003414490009d1085000048010005000f405070765041c41d03101000b04a10310001c3c0507c0e015140840780c40e40315000c6034407201e64170f00380030128501050707000d406989007040445054900540210340100c00c1075031441000100203081c480e11018020140410030401c0d1480c1c440c9103400310942031028640c00584 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 429798758 1250 429797508 429797539
    0x60703020c15010e07050d0609050408130801060803030a020d0b04090501060623030c0f0417071409131e0f0506090c0d052805031303050d02010c080112050f06090601050f 75
    0x100f0b1703040541403511581d180c02d0329544e18003500080c2c002100740b40c42d000c14081000709840c014403440b5481024a94800d9494503e10f00700ca03414807401000da003003000080c800302c40711b81c0180140c3e071900c3d2001a84542d46030110b411100d481c0b0f012075003a9074400b0107000da075400c040c4841c03040341d50300168419645074800312202d5001c0034180b2008c102020034500c0d100f4100d2001d031000b81280e4010500880300040609903a00e226200f14244040380300c10300e01c690f04111912a100b150f000c551024460301680d1582c0d010400c40c090360145481c100c00346030001e0621a03d1b4451280110000c003e40e042c00000e0b83e05140420030b12520612134618118005080801c881482068440c0c04400011070480000003000e4000b40040150000080010420489111070000e403400342e8210b89030fa402561040e400c98030b800007140c0102d410030004010284c210000381100c1031040301a07883c0510140300444c503050302550071001a401081c010f101c1400c080355016403011045800111400014 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 429800008 1250 429798758 429798779
    0xf03051b070807051f0501031b120308060420120708060d0b060f0901030f05060f070c14101d0d02070b07030f0c2910052808060703020c1501 62
    0x100e4020402c503404900b9070306106040c4a040b40003840401440c0e03070003c0100552000b000b09000803034043c22013043c8660940307007101e0082c0c103540d8002d00c007074240c1c07031151401da8102c4001401540e000e5124802c58000c000c07200c0b032001042c10b120f005147c40d0f02d40041d03121980342000700100c08200280080000a0740c4e0f84543d1440035030040d00c24034958880c48082200b41c0c020743c280d190000000300002041190350308014114038090000c1e1113083c1c4880002d00d00d18807054941e0400110780c20700c02c502058003492a0322004407408d00b111400c448080604050b500e5001548520304400040b10040140a028000b035000151000c3e01500382041c80e09036080c01081d402404000f10180c11620083c0141e41c0050500d40004014901c1c40019034884001c1d0914896101072042101c049000751948000200c2610002000c41208104481c0c10900000c2c500c051081614034455000691100a00c51a80100b0042d500542c2d40d96140c0101440c0c42070201612081c4250040100303c0b52456 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 429801258 1250 429800008 429800017
    0x40e0c150307050f040f0611012c07081005060306100f15021f0234020f06070804082b080105040513080c010207020a050a06050a032a0f03051b 63
    0x140460162240c850342000c50b40313401031020700b40b00384000250115603488401c521200300c8109941c1c101900040d10301d041d090300c1080c0a40b04c2c404c110480501301c075585a4003000050148002150745403a0303035160142c54400112001da0040b81d46000740003403410140203c0f580001034411406441d4644441d680701c0129901c90208017503d1032003c645140c3c8240f00340360302c1444500040441d082c00746a0f50000350b010a807910a030454480d83d06e400d0310041c00580e840000f0350400c603214121540c00340030001c0914230ba0075500003010811000010b5840d0f001e00080c1c070301070006046c40c90410012608034154034070250210491910002545a0701c480018151402690042010f03114480c0740304482d441c46100404005000c90030070014101507002d4502c8c58001c40704244c88690319030030b0120f0102d0310702030400001c1c2c0030446020128001e8000c07041c4d0200001ea6a5402c40d20010b00b00c40c0916488030120016100380700005100354507000f95500202c44546180024080031540001ca218 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 429802508 1250 429801258 429801289
    0x3030c090f010c0203031309060603090503090d031413080606150702120f0f03190509090c13051008070e100c030c0206070501141b0909010618051e040e0c 68
    0x442080704841640310b1043d2418190f40a401c580d150800098101c2040c6424094011800d00d015400941180b003401540900d54025000d580f40c43d00700b6040c800345481c1c2d500b040c0c0c288884428104240080c0030024142c9005a0340d804110a062124817030500c00041d01c41c070720900e5060759080b100794a06013103c10065045401111015040c030075a400d01004110709680c0740200501d4129404010008000100c046038107100e141c00030000645040c01460042c0c3d800512100000b002a240300004000348912480d1030080155a00c001411704102c80d201040003440c6002441403d54204001072280c0c681141d04007440e90810364001c0450312100400350402100c046400c042d0f484402c2181c13039464010f4028480040c44034122803200710300307440885aa4003c4100920300c120603030151010007100403d554196440c20720101c03001c0b120440100d90032030110f6400646569244a100d00c0c145040488400d00228041040111740b112103042c1502d420502075a001551000c801015410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 429803758 1250 429802508 429802519
    0x30d051206010503010f1211090a09030e100f05030c070204060303030212070c051c03020c01050405150a0e070e0601110129060f04120f2a0b120c251103070803030c09 73
    0x88203003040300c044923584403225000000740d01842210b16064121308481030180c0c41d00154941210b0134080014602921f400c00100070480c0550030324401c4005507008060340f00a2420000150002011510340394012404a0f500203512640d0f10065000310741e00c028103080ca07240841e01c51301d0b47ca072110925803070b0360000c41544921816860195040c0ca1855281c070000700312a103441d1508941c0d404030300140000ca40315003400501c450205000d142400004000a08003080c0b800c0c107020301422000c0c0659050103480380d00b9041a00091050342c0b1091020080a0046c1008002c0d04d100714080f03008250007140204134092a0940e00c1c41240c04a07405240700d202c1425080c100030380c0000341d44800a2500003c12041c00c080e0030111400800c03034290803c262152a030361050030368584551444031002c0c004600009072002d4002025090380110750510f60450000d003d00b540d13203131941d10000c565408651402c4001c60504000b40400707001000300461540c20204802c010600454464900c02e2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 429805008 1250 429803758 429803789
    0x7020d0212100213050108011a0a030507050715051008010c090b0304020105041503050402010f0507050c0d230a051507080a1a090a140907050105041e05030d051206010503010f 77
    0x41c0c010402001110b0328610115251400042e0400a181a40c482d081c00140e802e000814941d4510951002803101444414900446804241c0c05001c00500e030350144241440910082060386c2e000044148030700c107000a0610313040d40c11290a50113a0030a43c0c89a01d400141840a41c11845c070005940144908544a55551004070b40074071403174203e40c510781011910000c259030180c00090182c0d100762561042e110003620122840c3c0200d00014181d50701807050b004141c209100c004669070b0007803240640c41c041c0c500300980000c800d080f1304602ca138440784503041801024005d07414031820b03554104243e410407400040440e0805000c0140343e42d5604c40541804080c8180b40c4003a100180c0000401d10302007450740c0c024400002482c0c9042030000000c0e12030300001c2000700c25904140c540d1401e1600386407041100c0750400070740c100a214134140202c0d4664042085c461107a00c85e0741c0e025070700c140301e0034100342c80d04014100d503040c4402440107101c0079000107186402d40b0128881030780704 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 429806258 1250 429805008 429805039
    0x301081e0a061d0601050607020f04020d09082d07170c0102091008040320030307030c020a02191e050105030c0c031c0e070501020c03060f0403200601061407020d02 72
    0x401040041c0200030500d40464040a00c04641d0800303081e03001c0300283c0381ca42c0c0e40c420038050f46100342040258811007540da0000b0750300d403541c0a05112062100001400143c0c1e50b1804402c2d4000b10308000c00d440489824036200d06110f56500301c141016809604026940e07540400550014013981c518020103d04208959400d42c1660720061001f0445d126004080394081d000701300595040d000200a0ba201c807099100ca05601c101d00b4041c54002c6185a48549003200244000780b100704c1140100001e0a000d0307070352514000c0940c0142c25140201c4c03807910801e49281c100114002c040c0031802641004540c0e00101560303440b004007800da40d59000c44c19126411440740c80d00400041d800c59544e85540c200561103002c00c18400c004440d080ca0b02c07503005a80d40d1006d4110554180c2c094400550803124528000350414800e08103d0310303824020500c44207620b0340c40d2090b141607204000400505921885002e0781c030f214850510301d4140d00343c020403412880d41030040e00425481c1d004415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 429807508 1250 429806258 429806263
    0x3010b0d1e052b030f020a020c0f0a031403030a0b031908161203050103050d0306120212070e09010509060601080103030f031a0307030501090606050609060d0f0b060703110d050301081e 81
    0x1a01c140108411968503601141d4416000c640c283c4400060700d000007031204140c040c8210740415420f5002886c8072180c003401c101504101c0c044d001e402c0380c1c000c1c10020001d86005002e010501314900503540f00d01e0035034100780c1150500f140c0640700c0e920080126249a884150383e091954201120356900c03200d04402c032181031003001c0010076045c80d1420b500c00c281c2c1c0c50742c0014180d030f1007801500d1541d00243d004400b502d206020b9041c1122400c07640300010714000ca59010007403940010341d114180d0320404050413507011220090b80d65114410800c0d219002d20400341e00c14000d08280546504585000300009540203d0307405041c0c5c0c52100740d04800e4281c01820040d01d006088500307041d224a8040e0281691074402c4a040c1d040c804081707403e00d800000e4132031130320024100398100040f503040c0001070201d091000c000659601c02041d45620703a0b500916001e0b001b915079203640100b07400384919101d14441c0a004220742840103010442020505000f110086207805000807040f8403d0390 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 429808758 1250 429807508 429807523
    0x150a151b02090403020d0f0201050c040905060a030501091a0f1023100f031d0606011409030102040e01030b0a060501020d030f0e03070308040b07230a0302070606080c03010b0d1e05 79
    0xd6010107414100410517900040f150410a201e41c6c1d0002410321000080c0d017a1181520807610301081400244070b002441d601035a400200180509280c0742d90384c5580d82120301822041c1c0d003240f9010524412111303035840c06504450400754a5039607240451400600036014000c10154900030b1a440c0076400041c400314041c1100140480c880c203640420103000910803800010201c0d007003601e28105c02a010703040101c80715a000183c01c0340d0380c8510044030840440003a5640e141000d124160032030b01c00348084c00241806030566100344d411400e104e42e0459005050b0840203003030800500442c0d90214030a000000745003008911041300038241005410f02d10070142052001040c80030500d584158514056400303648981030b9500c800808a03000b40031681403100300c00c40d40c0f20540c4514050030017408195814a4010706141c074954865040c0c8030070341d00c520802d43c4102500c07440752600303100c0c4c0d80309184101d0302410560425170f03400507284902000020b42440400081080c05014840301 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 429810008 1250 429808758 429808763
    0xb091806041e0b0324010b1b0105240607030903060b060c03070818031b010f17130b010503031e1303021f17040807120207080708010203150a151b 64
    0x21160040c0301107900101440000f1030f120340300d03a500c101044143c103001c4510840c4010b9000c119607082c000e0089080d40b2209800701004030305662603800b81400e105481c040e00d4421107008410072040b483c00343d200c1c0c015269a100358000c22800000035004505001220b13440034000c6035030305003e0001041d80c014030002001c00c1c00009414000c0144100c014080003950080038860070141d101030550740c1039440c404000414641110318282d6000301e015a40e0602a49400c42804c4bd8a500020ba80c2d00c0c02d0311103041e0b12401d0304000080120401c84140174140940c000d40c14080c1c1e1000c0c040c0d80e001011a401c200900001c0c224090307074004c01c4030340c002e590007401501e140d5042199002c00c404400381c4440015400d40f00d110551020015910b0203150031001e582e08142c501d0302ca121114459400c0102544120400004d20020a000c020024401200016240d18003000700a441c03142c000e03c03480c1f0428401c40180660710f2040000f4101c0c2160b880d2240c810380401000d183c0740c000d0342001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 429811258 1250 429810008 429810041
    0x14250203011b020705090a18060e011506020d080a02030c09010e130612060c020a030c0201032307020f070f1a2b0509100e0303070e0d140303060306010b09180604 71
    0x203003000e00c3d800041c1c2c9000c80340d051710181403036580c1000d401c0c1201d102c1c115038803a03d0000410306d008504a5046403283c1d0020f6000000c821101644890110b100c640c8550003507048086840340b00c0d5004401c4540c0141108425031540c070f080204071400c1d200390312103a81032180074108602e60303488500040b0f030b041e600c1500c100026500c85041c100c0c207a410800441e8202d0070094130100032803011400d40c121030352540f640c0380440741990040d406000c05040341514403545022100340c125082c488940500a9a00a40031600c5038204c16802c0155540213150001c4251204012495004182d50743d609078142c3d016468444407043d0804106095441c818803c40c590000031241c02d00e80d004d94000c04000d8110752540510908403002e03a140202d031501250410b1002440036401107101d00407003c0014011071149030103983d11200c0144040c40480710394408010445181000c01040380944000c0700580d090400c800700003803001c07401207035030000350400710b02203204d40c0c07181d4001d030300c1c00c1c08030105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 429812508 1250 429811258 429811301
    0x6060201020304140a0b0109050c09100509100309020901060f050c0d02010b040b0103200a021510050102070509040b0a020f04150c06060f1202060f0f0c0d1425020301 73
    0x400038040d4000303690950740000410701d54288040c0000701c9940b4a540646c04c1c251580c030340031808009000042a824141d4810030106a0f596078203180d185003120130b61681504c0c2c000c00030502c40600c5901c80d20400f80351615000c840941d640c980e4442c112009843c00e600600c0b0014001c43e005c4c0a43c1c580824184200f482d0341729681d07019000b2041c001001e0340c0070822003076810011403c2d1254114084501c0e09604811065a25604001d0200c1c6101d4012900c0300c6100701000882c0c6201116502c200a941c0076003400300d907030306000c8500142002c031210f9403a403c0c180c4031a100c903400a00704541160b070002c0c0410350380d410302059400801004246d6801e08940080c090807041c20704200319107141c54082c002c1420121002d1000c1501c0d1541c1312028030400b03035400e00015900c81048040500c0060005c0404c2440720f00090410440d0040074003291001c113040074040f0191201c0004009800740300000d45c20305107540c148485002030001da11147d107240003090040a0702c1c036108004402440c03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 429813758 1250 429812508 429812519
    0xc1309050106261203010620070503030403060b0405131e05011103070305040506090105090705090c04050a120611030c09040515061801090f0311010521190b0a030b060114070606 78
    0x503060700e07003855078152944c4280443c0c584a46105c240549004a40319440c500c2e0100506c1e10f000084d95546000c5803892921a000685503030400d5004481179602c4440c00c40c0c05007841c0c090280c00c0300c40681c00071b01009040d80d60209800c0c1c162004003105203009803160522109420603940003040c0d850a50b96810406401400f0f070004540c281d13840d114180204604080c140305962080b00c5c000302a1800600b040c04104c243c89015180e041502c03010711010400c0d6540c562140010040c6110326001c0780d40c0c40c98014241d03540610001c844140600820000c004110110342c983c41d0129000500390343c410002110310002c0781482a0480d0012405016510100106407603020007600c1e018501e55035851000115a0580402062810f908551900550080016284041c000344046005030150b12000449000c201c03110901d24000c0c005060040c1524810030140d00810780314007161608588441080c0714000d00350a040040c2002c1035810b40302d00304203075000c669020382c042c004a0750343d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 429815008 1250 429813758 429813809
    0xb0301060302060717130e09060f01050102061602100203070201090c1a040b1605013209030417281205130b160812010f080f10020307030f24080c1309050106 69
    0x31195054144074107004110ac00b10f0443c15a8100c9605034000e2241d81e4820403e400080907010341e16096100c1d20301c80180d01695400030314814003803907000066080301e6040c440d0740603410768000348254110b03030584000c44034900b084400b650302541d0380aa0310252666045200c01d14440c000e08a5440c00c201d0000c410410b03c456036074020680b81000e004200c1d030f40c51503500c0e04107a8040d009540100010041d0640c8450900301c0c7c4103248054406200100301d000321741c0585810b12070008070030303800001c0400c00000c0981c8280d0100d403800b1303424074035002424080402030380039a1060b22000308900d21400c204001140280394041546a02d4501200c01140019030030302076006035840103480401d648100050303c078111003032234000313001c030303410f1000048029480030380b000d004c06880f5030050300c43d90076a0081e080415055028212211b4406085404c00321007034001052903008030b002c200d1155a4510341011a0000340702c006003100700d914005004140c0355210b0712038801a0821032400380201c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 429816258 1250 429815008 429815011
    0x1090f0210020d020615010311030a0f05070c110d051f02090a0503030702031009020607080315010f02010c05071b030b0f22031706190b0d0b0301060302060717130e 72
    0x1c0e20030120000340c522059890784214284500103901020004061440e81410241d0034401814000303648180d1044c40b40c1e26a00444103480c0c05511003031100080d101c9441820b074819281d02e8841d6084041c0e0b80d4000b90210b1031040d852180414991000501200b4001d01055010f11b6074a801c03503601c8140b0301c002035045500154810026110000f40310708010003201c5415134010007a02011100c100194003c0801e045c05907081041402039030000b030201e0000354068031003401005040004e5100042001d54802880130859051000a11a0342e8100080d91081a0f0141c480190b042070381000350b0380d22109a001401e0780280406204047d074034400c807503006140340104030255610802141100d030b1101361005001480c12000d08cc03008110b40200c0c0d1308210010b02d00d414400c0e5901a090043c5441c2d00446212070b400900301c138043c0003600c80d9642130749050b4000e000161452300001c055004d02040a400b0510f0b40ca1011f480c8518107088801403403201c0042d0715600d44402c052505041e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 429817508 1250 429816258 429816263
    0x907090e0a110f0f210a1a070f050315010e03010911030601060302090a0314150127060e010519080a2d020a05010f0c0203190b0c041a070c0801090f 65
    0x50009500400c1d090440608400f070310f02400307814a4150007424042d039000c0c08421040c0c08000000840d96815080c004825000d000c2c040c00c00d801c0301c50055101c100d450241409050000300411034544580200550782d11501c681500d160704e914140060303c0810925154030750551820788500208000b03043d03a46484081a8100c9800d40c0c1c858030140d0032442483c03030349507026800107410000a51400001114481c142c0291940e09503003c0c16100c2511087c0c20910303421609040c2d1045140e0303c00c1414038203002c5072409207c0c10f4a03010090344a88010700902d80202d600c140038100f44500c100d900c0c4010104c0c00104d544100c654141411b160710b104644403002d81c0c0c10164036002c4098081011360042c1c00810080c040744c64040191152140d03200024103004002c0d0903c4c015941c03c2c0320311000324201015030120f20141b440d040c809800d0092526000100510091005c0c0d000003081ea580304062905203980c3c0c0130359080807140040d03954041c0d07a1030340c00c5c880010100001d6003d0001200d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 429818758 1250 429817508 429817523
    0x103030f0c0c120c0e182401090903110d050405010201051e070f3b040203040b1305100606111006050f0f0604030606151b0215030907090e0a 62
    0x80e801241140d280e5502000501010000035060121205030318009680714821507902c50710f0b03a5900d8800c1700c10038080310f80181054084108100b195000e100c5402021061000304034044004550010021010701406c9001b559908025007018000d6110b40c4086c1180c20031a441c104050703000516541c007034043d00b070040d400c00001c00c40340e00711a00805141404000e10100995903903400700c503504500000c0d001008004001030010008001082d013808501c10110b014401550030661000305612008a010354410010400841d0410540302c0d001004404101d000c3c24080c20310300d1420031305030180c0014619120300011050b8120414100c20090720302a14011680810243d00729481072042c0b6420101c40b11400d20586050f080316a80802c00130031440c103254680c1c40f400c0840c0c1c03268108184544d416112640035a400124680da000a429507280748040d0300e9000c180c1144060062805c607041c00700201e202030b0028452400a40b951240c00c01124910344c1380583d0f0340c0c0a000040d529031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 429820008 1250 429818758 429818777
    0xf030f02070501050712030b1e1837020406030e0c03011e0b0a0312030605010921030c020f042a230a0203070503120604141b03100506030c03010303 65
    0x4a00205407482168030584495040240707584518107410703102d0f0b540e44101540c54003044017503600d6400c0803000c6491441ca0040c0c0291550610400540b00e45543e42903280b101d01b001580c0e0038550b403000401c9841c007103081d102002610b102c820701d2550300000100900204d400300390701d80e15900c4200792402036001c540310300e4000f201b0b040c00c90740008610b0814040201c801050039000d50081202180050910840950307240c403110001543c41615000083d00c44404020960780710070481c014240d00152010841441410034086001c0102c0003028800e526621034155590441e09090250b80031348240441c801c0d80c000c21100121008080000070b4901c4401c845103072190030108000c520b4842c2d610040b402c1d6190701001a00b1480c00203046120402c60340c000607000348060414a4038419605040c0c1c03c22004100a0b540320950080c085007d81e01000b840c14041d80641445894054000d82e0b20340740d44025190b890740c143c00183d080400041400700a8020000640c1200e020340d85603487c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 429821258 1250 429820008 429820037
    0xf07090b19150e040c020709051008010504060605120706020d0c0312020705010e0d0f09050607300210050402010c030c153318050c040e04050f010b040203060a2108070f03 75
    0x32030741700064450040c0d1100c2c500340711924050340b0480e0409002c2c41450940750b911070403142560320803a8200c900a448032801c01c83e5040c9442c0005603002c284000d00f041d1070500e40d00942d86c0081c03051005c100100c4138003020a00d4003a0411910381c88407584150750b18841410321502030070001c6000746082c49140b803101c00307091151010408052060f50f80d2249540707400104903103600038400c1551114007408040300510310f903000c07211a2451200c06615944130100000c1e00300030819805900c0d413801c06c800c00005070b82c400040d0a4003a0b02d030a24142810702070820410710040642e40c0846646449203090007103d540003190f002c0080c003204d6a0102e03000c0d68101002c20400c0c4a8403940c04104010342403d24295084aa48400c00c0b03000d050829a0300c000d40ca1880c14161410b45240e0443c1c05016000b00e002e0050540024068409500e1801c0080200740402194491030000c1801c0f0300c080e200c01c0b8012247c043c19150803400c0d85440f40c0c002c0c00c01d0f10324484a82d00032408a040d40031811034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 429822508 1250 429821258 429821261
    0x30515062703010f09140c150d050403031103100905011e0312031506050307020f06060a06030b011806030626120a1e0503090f0f07090b19150e04 64
    0x610250580d4920100590060800407070884400305926540307034011902007900c1c910402003072501649581c5440741304408168181654003c5c024060008980304404402d0b5580c00c840c02481c0396240090160b840c1d040c2240200081641286560000803d011148a0442150342640c0f00c1c482d00700640d1f41c2c0c810405c1c080320200580c22007401482841040490220000c81115011030700700402c8800ea81d00c01c03a407501c03507580c04c464007092010082c0440141d042143c5440d00b4a914000c1a0504042001070301e003400034881c200030142c85546901850b48171f002045090f040032005069a251900c1e0050040c0220f40640c10080761142c01c40c030004112200714a542c024040d011b0698030a40c070000441e0303540002c401205001014035040003810008980407400c0c01075545090b140e0030000001c42c00e01a03124110303c2d00d68000d40c1011100c0f4008070b030000449011500010b03070640c0501c0429015550045445140310606000080c100583c1c41d0150b80c0035030b01d0703582c4000c00882904000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 429823758 1250 429822508 429822517
    0x4031b080a0318210512090303010608070c0201020c2403090706030c0f0503070c14030d381002010b0613030201080f0c0d0903030b060c03040e0115120b040204030f0303051506 77
    0x2004034003460030b0813072159107a02611054007000d1405600c1d00d4841000c11414030070544018800754000001080015403103204160491110700d40007405100382e800007583d8000d85240144a68166080591800d80e144101078040f05040200382c0c9920b8402c1c2d40e55100d955902c10312021900b0b00100f401014420b0002c80344600113522a141141c44004080343c50400c40d5004070764102102a40882031002040909002c0105d03002c00704215080c02e40d20850a040303203042ea01215000380c11400c41e40410780c3c145a4103c1d054400b08181c0c00c0d8004203d02500640510a801650004480c0450041d01e0740c602c05885c000e0b20b07412181d4542c051074540100b003c43d8014810102808409029000c581200755041c0c028a000315a132180600054007c0d4402c12240301e00c0e50001404110b042d095501c920f00403c12140707401507100c1c50107405040226040e004070360b01d5981c0c01c0004507036592541650b0107150001028883d000c0e0031319000e00202001d642e007000218040c09540720360b1600000304ca = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 429825008 1250 429823758 429823763
    0x101d0f0c030f060f01090905070302090406020711030c0109051201181b060815010f180603090c05090c03060d060615050c060a050105010905010c020301111210060c0305070b04031b080a0318 83
    0xc0c1301d0307868000300c1002801c94020446150140c4600003006da600c0d0101e050007903014090046e6030700b46500d840c2d43d181103042d09007402900030036031110043c0c0e0050820401c9800584035035401c02d255061260061240c1e101c200300b100700110b0f180b803e00c0240500d05281c1600c0c2c00f80c00d610691601d40039500e0b04411070b050504070b4004004a1101c0d4811000317003140610398100b001c1c045101c4070403044010495000380000035507400515050051440c3d076000100026642108542004002244a8880144002d02407011408a05d0402c407041e80020000c00c2034656415180180e4030f0700a20640c0007611a0403e4030450020032842e800d203118131070403260140c4600019a141c81d00545d000c14030814242d9043d5a50007400412040c4000108030801e21030a000788903207048180310a00c80c0c00d0390044000c0140740440c1e94002904a41102e41312900020003028658440c5812108000c6030308010b03400d040b10500e14410090440b0103066a070303156440c1400300c80e8417045101290340c03006001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 429826258 1250 429825008 429825031
    0x30c080c131404090b09100b060f040e04020a030503040306020307030606020c0a0314030d0504060f050c030f0a023006030c100804060b030c0a06090504050a0e101d0f0c030f06 77
    0x2009070102c850203078290804007500218030b008054443c4c540000e0204c5400c18542c00c0015203080c480e500f1f1140d41c981a50031a09942401502c0c030040555002d41d000321005082c0e038074049015980ca01526030011540002101d03951505e0345880e2003c0d400a4603002c011904010000c038405002040d000f11820f40603184004071440e5448250b002d038004111041c0301c0c0020450690040c0c0c09006480c03080d40100030200d1034800c034429136012600014078181500005100f400580410213001d41d400912041e00981c90b010041104944203402100607000500180341c440521142010324a01c00c1e035040341031702d01000c100fa040c00311203060000c01600241551002500181440e0301802c0584c401804460b030b0144100040380540925070085030209680d00d10400c0320f407030b147c0035076a03000031200010b0000b24584920355a032101c94008009800e07444190151409210414001c0302c5c030341210403512400f81078228203894270083e08125020703028240c40d00104240000d021801440d48002 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 429827508 1250 429826258 429826297
    0x308040b1017030705100507140f0f04060e10020c0d080c010908120a0b0a0b090f030a0c0f030311060601021c050d0f05010519050f01031a0907030c080c 67
    0x12420440000140440c0346540718810204226900e90389030201c8107007480003107a4941c040e0411905e0720841001080201c2d00741001c000380d06034400e8242c0003400107504481d44072081c403401c0d9042ca014003010b0760b003015004200000c500b90700c0385012184142c16141b000b0064485102261034088504442e81c200300c50201352400901400010a13103c0a40c0c800080c081c81e09654115203a03005880d842c01100c00c0300140014403080d4410b107071819400f120941700403850030800f0b9030540a41030407540310320b69801d00b07150651824440102c3c2c0580c02040d0080c565243c41e42c0d5198040e40703000580008412040e004540c0d4000112140a004141c00609e0072a48001c9900c5481e00031403049020030800384200b5441241600812003a074221002c045440e60408082c01302d805440b40d40c00806d4540d044040020342c40710400401c013a1001e180215600c080c00300381842580544040c183c00981460030000c60710750680c0301500e07030000d41e541c500c0f0f03503121040646968055803406c506200740015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 429828758 1250 429827508 429827513
    0x5010507020a030507080a15050f070815090106050c070503190206031308130e330301150b0d060e0408030c030703090503030405070609120b0606070302160603090209060d030804 78
    0x1014002941c8000c01c0100e21a80301e5840c541030001a40c0945001e500c030300c01a1042000c41c0c0341e4000381806000302042145089400e120b5550b401424100500c002040801c0e0a01141c20300c105010b03030050701107415565949070003055540801190340040c01100ca01280e01e20300890200210004101000765203034840c1c0030490640e2001d042c2605ea03084040e0050002540345001c2d00c4d0070304061100b403101d41c4c6403501d0305007032107001003030384c80714004909070000c5e0700c907054904e0000d98070103c80d14240303d030741d0b90041b074011b003180c5041c140030303001031a00020000e007110000c100c0e10301404424001c0715503c036002c1d1402c1d02c040c1d40040c40818144001084801050701850f07004500d4030300403541c407600b9100c1c80d08560050f50706a80542140f1030038800241c1219000780140000c1101044461f5180c45030708510708044e040ba80f00e40b00c000352140c1894820009840000320910700c100c0403a03079400780a4014480c00300120b00500050000450520b0a4840b20184580540f0b800c0040e5071241d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 429830008 1250 429828758 429828767
    0x17090a0510021e180307030c0e01050103020a022a03161d0c07080f070602031f150207061404050a06020d141c05042a060215041101112118190501 64
    0x46110640d1001c0004c0e00c01615501089203030000c2d4011003181044905201468501e04030503044241458010890b01c0500e0390b00003591000311111000b040505500c0105600c40c2c41070316148541d1510584070420711207000440040100c1c1c081da07401e800644480e280d1507045c0c903404c460a1303418240510028000c82c46800040c112820001d001c00e140210b41e582da03004981098900038105200c1c00c0d240a0800803e61b01c00b4050301c10b80c2c10030740c0c048141350f900968401c00c50040030200645011031284040c0b1001c00e447c0a410020a00c00f612922a0002503480380004040400900c0707140005084141d0741c01202e020b51a041c144004800c402100f03c00541006003048a64604469041c040580e03141400d101250451000883c101c2c50701f00001d1038599501900c8031044940300500c4001036030420610240a028286020540c1101170207c2c10803020b00d208400c002c610b02c13450360020250000a181c81c22a00e6450404004a0024041800c0440843c0141114040000d20656024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 429831258 1250 429830008 429830017
    0x50105030901060f090902040c03111801031d0120030621100c0906021e0d080c130801060302130e07090b12010e0a0c0b0c06130317090a0510021e 64
    0x240c004501241c4c2e403405041da40340c25034080001c1c1a07450000310b0452916008040c201c001a2a0600994081e03d9940071240300e004941189600040411310080c0d000c3e0b04039407002e40701c4a00200401248402084c080e00070b21207503aa03903003a04060078022401320710680e8001c41002d8011824002034074140204214614000203491280c1c1c40309640100441c0541d41ca004010750b20001045c0c070702840031703260814840440760b81d400cdc544170305038580b900040e000c6076080b05885c00380705544400e209182030741320301940c84010b000c4001010401d080150050780840c3d10a8400b4504150b01404402c100c0e10100c01a0b074483d000740e582001035503030350b802c26142420020300c1e0b05803080c180c105860840700084a49410383d04030071004014440c1e54032500b0010308950707070035600d4030610103070720380e201c68004110180a0200c20098000d2610401000329602d480802d030740540e003400e8200617600c0250040444141c840d80b44c4d11402200c3ca402a140da800c070510042d600060027106030750543c0c11 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 429832508 1250 429831258 429831271
    0x11209060e06090a21090503160e06150d02090a0e0c07050606040218040b031603110f010c02100503100308040b0c0c012606030114010b03040510060605030c03041106030106030c081b0405010503 85
    0x190840c0440c0650b010300c1451513002d4101271013801c4034500400030039800f00060099220755048429000c0d10703140074040310300b00e00e5406401aa15801c2c4800500c03500c406410068481012038104265040b8480c0103040050182d401c541c0156103200400040c4c0c4030354401030b081e00c81010304a1049003046e420101410f04014161444011800c901050030046030f8001c0d0b40d400c2084480007030724180014031040005081c60200248500c07074020800c1461a150072904000c000000a00d44045080030300b0003a6511038496a5191358421610486401160120381c144c0101e81d9030313051541c09000c910b00981d0707128400b208040d03038000404010820040600350995210078460710b4280e8918072240c06007124406117900e03800c103410690316054005042804c028913100c03080c02a290008180ca40c0303c907100d8141d5030f49540d04d2800681d54a46c0485050700b041e008000824110f4054200d50300a0790f175643c0e229095600c814036221030040030040701f11500000c00080c48594860070003140d00c0780 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 429833758 1250 429832508 429832517
    0x15060109031b230405010b0301050904080a050904090c050310050603190201110609071a030f0a050606070b0a0501051c020d0303050405071d040605072c011209060e06090a21 76
    0x2699800040d81070422564603002c2c44030115401c3da01890301d8807800c0e015041c1040b9144c03c0d5030504000c15410310000e0009001c0c1c1e0340c045040d480c454415030496180c810040c00078090200f1924083c030305d00c0c0c00c50050900c00c0c0200000c210800396540300b8507215a10003001841001501607000e00f42c202e030042c040c0c0c1000b5900301c046c20b403904208039450046030408010b202c0d040c80c1c2804200010610841004c03050002c0090124080c0842c0c10b003904048041c3c3d001030241c0390342c0c000030f170140306e04a0010b0141e0300b40800c21480d4031542c0d10403812070308103035404803a108242002e003151800d0f050000758407450940c20000440e200341d01203a84203124a046072203e07038448944011440d01c0180c00d1181d0000c07801003104018150140d03642124071814400e071a079480c405690701880c1a0101c00d542c02d105c4c105592003d0f88030707400c0c0d8040d800404008012000c040c0c00c0400150a02e081210028854640070400007500010481d940a0b0824810310494503401e01580050340748500e40c10410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 429835008 1250 429833758 429833813
    0xd0c0503060a2c010f060807020307031706130905010e070506070f0b061210050403031406032e0e0604020f060403080a03050a0f1b03060f050109050607060f0e030c1506010903 77
    0x980d03103100c0044c0a401201038011495242410043c5100740c0103100c0800c5402c00c2c020400025048550169409034030000c10340159605800b003450641940103030905c2d54200070340841030241c19884000d0019110003035a400c04c0e00d032000e0002c41e2180e01e000810210038400854007107010b10369880c0c0c00010080c10103140204c50804503250400c102c1c06003503804d81e64400e0200701a01441484002102da00c004812860010700180c2c81300c2c94490310906180c203003014900c0c1d408100038450518a52510104052428101c106e83d50f808119400c038062901440c01c00319901c3c01c4001d40742100c0c1d12600540c40c140611008070301a18001d0b180c3c000503030b182e805200c051441401081c0181c1301d19855287e00e240c007960003c082d0351465004e0400780c10520b04c00d00c280e0740e1090500d03040d110241c1b5840d9a44c0d04c240740c81130007003402a5240062520304111408080c0011004201c4056054119901c4019010071750140c0c00042d88c25074049030080c03404000064201c010002400c1c103520040060 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 429836258 1250 429835008 429835079
    0x1060206092e0204060f020705040504020901050d1506080d09050303040321020a05190303231803070b0c04060906090e06040f02070c0306020c1011071e05120d0c0503060a 75
    0x60360807035044030001c01d021440d021042c51f0304210200c001d1104072401e100c03508164001c184d0070081070180e6401b40c8132040c1100180640111841c40ca82404101084a5591866406c0d180d6051f2511040002c412074000942490004142c4064031f40080c0b064490110300700c029803c072461303001c144042d07001d000d00d8480030a0050140d40018404212403950b429054580241250030f9031900f854036110414025500f134404a41269202061002d141c90190390301c0102441c50140040041c01c9060180400203004000d04c06801125101e8481026080c4c40300d8065544680c140145420440d41400140503031419811040b024034804030010314100079a12101e0002c1001c0d042640c501d600058070000c0c080b42004005d03140e1a41d503004100f00e0500c151844414402c2c4074000e0300303046107051040d040a07003540703141c01e48903446812580407401d00c9419012a421205985500c1c900d0718020012160160017140d10601004281c0da016606041c40c58020300d4508000420601542460449 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 429837508 1250 429836258 429836261
    0xb01021609140a020a0207090b1809010b030c12061902041e060f210203040c050d0f0510090302031605011e0212060301021611270f01060206092e 64
    0x203010492004905900c0c1018000e0740c1c2e02c0041d202944070381c81000b00710032065010403100262020420046400c4071108006081c1d12202c1ea1058001207519041c08100c0781c0541c00704545400c141c0c1590f103192103100c20000040c0d82d020b032501c9aa0414000289181d04c8500030741609040c0c0100182003a07103d1888561082c1c004122401c40044658103205180e00540b1001d68004180f50550148450030b03003040c040c0d85000404036000b60080003040c1001803c000c040041d080140800d9240080c0c0d00707114480c4503e030b079000c0c0d0f098043c030003401441000e00d00810035080e030150015490701101c00c0583c0aa01203003c0c0c10f503940d56a0380400b0b0030960002c500210528078440003da141c0183c0f1a00798101603001d814030b440307031f0b104200c40c0c4503010012140101071500065803d04401c038240200c0d40c003c5110000034512035103007001c00942c1c1c8034107003654018480311303580421070703a01c0325001e9a41d0030782510100c2d0346a214103003081c2c04141c9410684024900341102c4d815503d150181d010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 429838758 1250 429837508 429837553
    0x20d05011707050a2106060e090d03060902030f0c161e0203060a0c020a0f060204030f0b09010c030b0112240b0a020d0201180f08070b040b06010f03140a0b0102 70
    0x1d10308095034840301c540000800c400c0e406408121102120245480c10038149444c1048290180409100016050200f281d0000c8001d01b5446122020342c82c2061400352036241c0125690003003880c0c004013040c00c4a5070b209032480f40f1280710300c4079081d40b2117805000030307504080305c80b41c44a83c0d090082c00000c2c516000d04000c3c004404803140c46011503104144c20000c004051028262a04428200c0d5650010381100e205401c1804030151401a0030040064496034002420420f03443d6040d408009254150070310070789144d07008220041c0d120000318155820000040d001505107961a240c0020a034060700461075103801070300d00703480d2095005240307141c0b0398040c0707140120105e00c004e41c103a014400d4043d40201840208500449214804a0001c0300c482c041c082c641c400c900c14040044100844159039048a034084e8280341c50301e020880750808440d4180004e4240b0b9401d038130b99000b40a8803010f0300240310340306583d0f5101c0e902d41300102a880d04190442c440d0300c40202461a2904420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 429840008 1250 429838758 429838769
    0x50a03060f0b0307230d020f100c050607200a1208060f0310020c33041a090706020c010c03090e06030312070206091b03030a0e03010f0f091b0b07030f0201020d0501 72
    0x4240d03000901c8440075400901703082c4078010304d12044000e00580d144241d810300300108542041c8400c03413130401100d0740c4000c003c1c02016803092509000607540c01c100d40043c038200c1c041c80c01d0030b0381c010100020b0711040044001480708038030594264a940c015100c0541c00b0a01510042c14440740d14006841c00c801d42c041084029800180354101030030071b220502490300500c90380c03100f003078466006400d40c1c0654040c01d214901482c4c081001c11003960384500310b1590900c0d00910380d082c03480300d140d2540b040d4030078500076200300015640954002c0c160020642d401d610f92800070352a003919803015000042882e50f03d40003c002080c07071042940c000301d00482c2190b001b0002ca10b04800405d10301602e90385649101e880000c540d10307041d80c00104840055a4900e00700c64044100c2001c6405000c541c2d024841e01418491034812080c01640085c0c80310b13006542c0c1400c1802c82d071030102452500f1303005408071040d04200001c0800c2c00b0300345500314001c00e44001071405ca001742c00c0d00b04403002030304039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 429841258 1250 429840008 429840029
    0xe120405090109020a0504060e011205010b0319060602031b0102090415090e120d020a02010603050d0201090516050a030f08070206040e040b061005041a09060a170a0204050a03060f0b0307 82
    0x144054104030795954094980007030214a040c502c2c1c1c802400b1030207148220340800076a20a480010307407041525400719440c156080c4000c1d612400349208582080b203000000c1c083c151000e03c2120618003a14080740c0d5a07030042c52426000007802040c1c01440300e805625503400704256685a16039202e00c00203200740951051419080000002c10f581540040102a9105040103450112003400f2500300000071300c6c0051b40c8003130090782079000d0100d9910140403405030301a021000c0c0d8040d0000349006100700152070320440350301c0c1408801080e074017440380c0012806009000140f491203102800d6400343c50781d1400c154240d0f0000f0032507889034000d2215000107138240f004024507948a2500310008848015240380e90b003800510318000c500c1580c110120780c0882901c009060812140342c020050840d651b10500301d040540360f4203559691100c40050907001076440c1005100780d8085e55001407802200619541315074000c2c1c10441e0090303600c26030b51402c042a030f607030030400d20005240c02d480 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 429842508 1250 429841258 429841267
    0x9030307020f060709090e0c0d0312060623070804090606050a09080a030c0b18100e0c0909100c0e0301090c14011115070509030a0302160f06120b040e12 67
    0x14000c0c00e0060703854208000d81d003d401405015508010350b8019205000300c0000e504500000c0c20b4038000c0c1500ca082d80182c810503070030f07081c140e202c12920003241002201380203495603288111254204232030416101d5580d054040201e0710400002c0100a000d0b205190074240c440d52003900f142c4541e40644040394001411039410b0740c200688500400d142000707001149901d4030302a04030100404010101d0050400103082c0c01c030001c880305003450810342111910100342d003040b4020526450881d07100d11541c24981c000e4034103440007621030400781002d008031101c24605c0b07201900d01581a04140082c200003441651424800c990a0a00420003084036503c2d102100b06420485000c0c1410840c10210b0f12480c2040020081d000170385007011101c0603a10401c0841d034070302500b17586a505004240517203041c50350000300803024914039009810700c0395a482c07090303500e4042841044041580c804c18901c6a134500d60000c400e1501c09400031031480c04e1021010f081400c01d03c03079103210031f40128 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 429843758 1250 429842508 429842521
    0x2070e250f0306090501050f12010f020a0c23120309011e02031021020d0804031a0f010501021c0e19080f100c0206060d081303080304060b01231b06090303 68
    0x2082c0042c811350004000d15410800801d0141d0320407400240a091642d071540305401d001d50000c403254280007411901d80580f00e00090141941c45800c1d00d01007001c2e168520b410350b104008003418140740c4001c1000c8469403003c50202d801c01420700950b5582c2d643c23492021207406441c003003001c07001a0016135034034181404403c60742181d002690861036241e4000101c103ca04611407c02d0b40445807040c2c03001c56840c00700e280d40f280350001001c2400645409000c41c1c4c1484902c0d010f440d402800400c80da03202c100481c0e40d240202607e400e00c500d41880b02410354003910000c0006c0701c000d00600c1d011013520250980d16101a071040c607582e885032500ca45c1c3e082d400d106414881110714001e01040011203002541c1d03000c068400f900c42d010860380d00c804c02030050200c0300350032074078013880700b2140d601e04088005070001c03601a100542046a078010640c401c0e600d4403480412104404036051b03c1c0340d03103040700e074206a41c407140d4041e20059a80344030500b002000d10454030040155540c3c80c048 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 429845008 1250 429843758 429843761
    0x60311030d0c03020d110304090e030406080903070c1a0702030d0503100b030c03181e0102120a0902090f0a020c0115030c0501050a05030a0b0105070b040c14030c0102070e250f03 78
    0x210181d41c00c210801c1c001c01c0001e0750128207881c00e2a01498010803030481100c08505621450b070080d0085403030700c4079000e04410301201510842d420354880310500e98900172490f0f22072255100c003c1140c1e800d90801d204801201c050110044800400c0c981005040d03408a840c140c14038000c00301242000c41000304060400f400d1034080c003000e80c3d001d401c50401e1204480e50740006080108045c8000440440155080242c800394482600c0f41c5507d0b50b9200108900075030212084070b0400c2d26101c0000c90700a507034050307044200d43c05808403c00ba91941201002c040e000380c25111042c0e000c105891295009004030039584441802d22442c3c10325500d0b008946804075400b681c1480018491810310320b400400791b9500642c189008243c0000c1080100c1d10b03845145002031100300c0380c20a02042c003140750b04200950b01d05c5100c00c3c520f580c4920405175600605003945006074007440c0280700c44402003075000c0d00800d032011704c8002d03aa002e64001381c1750441200f6150005250004003802c003a0305 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 429846258 1250 429845008 429845023
    0x105040605010c0203102f0711010905030c1021020903010609090b070c081201170105010f080d0c0c0e0414011803090312210c020106090b010219060f06031103 70
    0xf42052801c1e120140d010948506a02034000105039030b901800c4910b0641721010710000c2c0c246980110000f120f805415001d803c00306090340d02c1c1d8020818112a940510302074000d60f4401401050101c2040c4100090700c40c5016141080029084000c94128100c0d103000349805c00801001d81c03114056414142142d04550004001504000940005ca8000e11403603410040b10f141c10304100e065400d01c0110b5124543d4403141d16402d060000905074094031009004103c100300a02c200c0e43d84001d6204038080c030380074440f142c1d0811400d44040310301800c840820184034250000040d44e0b60740c2e0461101804980c26107140c00015000111220b084c800c0d01a2542002c081d141500003544000b0000ba00d1804014401011480e049804900440130070388440300c82d034040ca00542c8030000240140103031b52412009582008000f0030980254004d0103142d034410b2303004103012230006080c684000c195000a540040c0c1c0c1c1d21603420910075600620380610301034100051958015418549000307103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 429847508 1250 429846258 429846269
    0x825021219260613020909040b04033f0b03010207050a02090f0103050a0213150801061403070b0a05090d06060902030f16020d080c040f12060c090e070302072901050406 74
    0x91a1400d0a82d2604000081d40c02c14400d8403100300c3c0300350b0340c07402d20028410544072980c4080300401700010001d03007414540c2304900c20364038a4a40c00c2100302c40e04107080c1801c4034411007a1481c0e040d44c0e100d03403c1c807284035070300000c6c41c004a111440381002c00d00f268043c00c02a60542c110040d800305600f0f003031035866006035241695443d903600d55221030707403035444900e0020b1103499442c64100245955401200076807114170010301c11103907603220060090400d4030070b400503004416140c41182c42c0c00b1030f50404407100d030307180c0910b0942d01c00301c120b800d54090003e841d4000302421500d4046241446010042c20348000f00507943e0604020329240b001004014000e100c45100c4091031441e80420f0700c0700456440d0078001c10640350040c2102d41802150004054085180030000382c0088a18a01c81c40d1802203201f009000c503814411a4040c10601032405403e090300c01141c1d400c6d220707a00030180030380145146d841481c0c40700740000c2c0080c0004090081400c4040060101740f90901c5444010310 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 429848758 1250 429847508 429847547
    0x305031b0a1106070305120906060a05030a020f091b070804050a05060a0c11040e013603020607081e09010b0a170d1119120201050105010825021219 65
    0x48665410503114030004140b03005840c00701c4c00500f014050030649580380c50341e1518843c680780c0041c2d49565100c1c00c40c1d00314481c05e41220700050078100030400380c1400360068010314606e0010000e100042e040504141000c000e03582c2d1016181c60a0005064540c0c8516440382c0e507589000d0802200d181607400940c0f14084c00c1103814000c80e0880c480701400382d8803e0b585007094440c01c00103001020406090002e65003810340003201c9081a5080680c04c0038406072402c0f940020106460380006072403002809a400100890301c440d000710b51507540a10810400ca00902d4130b07402c071401103401603c076102d40340e4494801c13030014a030030110b09002d81080d5400780c40c4820b030300120b140d075010307108a0b40c014449003050030054110305000307480d074078440c5c0001400600c200d0301d4180d201d00103111101cec005518190020034690321650300c2a00840b00b2101d1078004003004d41940d45000c00e00d52811041d84120440044114800000707026542c008010610140d40460009404250079506c0d807020407 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 429850008 1250 429848758 429848773
    0x8192c011706040f0609020a121b2d090501171009020702010e09131a07050301090209060c0601060203030703060e09030a0e0d06110d1d0c0603070311040305031b 71
    0x340d0340a01548020300081000240e00c0c0c582c1804600182400200c0400903070802001003981c0074150024011511140e0b244212000d000160f90308845802c0880401444803000340d0300106d201d18021340c1c0f010408030342502010551040b480e4691500c000800104003d05000c220b2507800450341d110b503218500c46250b482c640380540440c05c2c000c1e0701800404950200340c000959208441c07444011a001d000080305081c1a0f07042a9039072041c40e01217a41d4440030030a0a1710340c140034502402180c4507104c5500396401c0280100180d0030200041d80c11010a0100e1418480f04210242c020030300e5401942e40e03818000c40040568003540c010280e031003021828409404070000440b00055031920300302468138645c1f400141071446034580a8111410640d112500004100040c541180801c40070014108801d440d00c0d8000b0300e00c00002600d802210104031a81440d400650384841e0707030b02d0000740c882d294049850304c981143c0c1094905138008100607040068005160f81c490290380000c207042d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 429851258 1250 429850008 429850097
    0x311010c0903140a0203100b0306340507061406030105060102071214010e060a02040f050a061b050309061218161205010b060a1716090902070819 64
    0xa00360540b000070094000342061030340c0014144039502940e0780c010151441561607a2148000c0c0c208003010501ca8020a00891451590100c40000902011004034002c012508408070802c1114505000348007041000c1c5000031b040b4840d18801c0b035190714000c500d9081ca0b005160844030001c0141e0b0543d445a4000e10441c0008050702000c1580011302ca0340c01020b001d040e901503c2c5c0c140b4054203911800052041540c540d0700500709460088007100d141550f21410004803000034410003012420717190f904012000602651110640039130b0031285070a40240101300a41c1c03000a8030300f99000300005001440328090307913024802d01160300800881c1c2850300320b185485254860000c4559650701a0010844290072007241c40000900a03500c2c1c0594032009040d0b612481580c00181d61424001640c41410094890000b003042d80e034012410b00701042c0c400254030840c001d45120405108807039401d0501002d800c1001b40c2551804810600030034003c0c6074540f1501300003241c010703a40c640c0c0e04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 429852508 1250 429851258 429851267
    0x9060207110406211104020a020f0f03040e0a1d030f07060e0303280b1807080709080d0f050405150738060f0306250804050a030c05030d180311010c 65
    0x8131041801c0301345240c54080c50030040c0514000130880c0c1190012908102864010424520240000b000d41c0d0004607002c0020392a8862409154030101808000c00c80c8000355a101401051100601c466042890000b15203181c010b1100100350200c0020048100003590280c480416810001141182801d2003200780c00c60101c840d0443d08105c0f020070400c4400302d50402800b400c40509003654026110b00c06090504007101c2c884045809035010030f603018480d421301d038121000320000e45203207444034508840d461070b0404008104041401f002c60140d9030301e01c085420b0f2400250840e0b0310650391071303c0024240c0404102c03906040910142103600603c000040c82c14070f00800f520503e5680c1c10006000380d052201d183d8041c0b20b42400c002c084c012140a45a039040c260080e00010030100300121281c82c0e0880340107140c0d070031041700800080e00410506070006d21410a5a041801c100b403130904540d0428070002048200703c20001c1030603001300000c0c01c1102c1c04d20081c848004191409003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 429853758 1250 429852508 429852539
    0x70b01052b0b0601170601230f0c01020a020115080601030201140412110901090b06160303110f0405130204031e020f0607060204210c0b031909060207110406 69
    0x3405260041000c190103004041c0c68603a05074007000c04040c51040342007110300d00204603080390100b000400e01200e1440d8204001c2d05c102816590008001103c400d90303948000000e50240030351105000f80040307811380744040d140c1c01c000c035000140c55210401c002403d4a07903244d41c0da40d4814250a040c4042e44012134003c0c1940d4080c20490304030028070000000da4030440d4071041c08241285054000c000708602150260034007200c8500c21a40c90b80301c4002214101c400303040e0b020004204110803124400d8946407030034040d0034002400000100304000342d0f4800c08840094100c00a4244070510b000070118500110200007141042d00b9a80ca03041e16581d61009410550301400501003150781d0140203490700743c0302400f496250603540c40c2201c003940050052600d010b100d4078a40c10101d030450803c95a0682000e1030031603075450008000d00c03540c400741c4810000d41000d0f802c0d42d4400501e018203202c007440f03850016526281420258543d445d15840d1600c281c0c1040010008180d4903d000c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 429855008 1250 429853758 429853769
    0x3070f02030d1112030709090c02101a010c200306040c030501050915011e0305190c1703090d03111501081903090501030f021b0c1201140406111606020307090506070b01 74
    0x1142e4030303106e40c1d40964640040e50310030800c803070a01d59401815980480e9450607c88521828070032104810300f482a00141c050110340060030303070080140807801d00303541c001d800c2000013807408901c4880f0300801d0805400303c505a8004a5038401001009000d110310355020010b04052b040144413201b103c00c40003410710442d07244820040d87d2620304000c0d072030b203440110750140032075007220780c0781000c1084c0d450002c909550301c0308049800101c04918028050044800f0382c045c61505905804004440381c0c0b1003000c3d010482a070300400d102580400000a4040c1c200040410343c1d031510039032130301d4035194101101000d00040c400800023a00070400d0707420ba610908002c1101103100074071744000d024404011f44080041902e01c51048008501c40c218400159144560710325002001820b03500069031140d40300580000040101c2d5899010480242480290a1038441c0080340344405201c210000e9800b0b940c00014045403507044800e0354020901555200c1c10406140c0301c03095aa80c05205d01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 429856115 1107 429855008 429855043
    0xf0501051c24062a1b0308030a2406081b031303030b010804330f050106091a0706020d11130f051516021203070f02030d11 54
    0x1000d0181c9140030344500b40518405031141e518121080c0658012500c1548840920b1703444103500001d5008480803030f164188030348640b040300d5060051074282e00203900c080c2e26640070101204200c0c1d4950034080700c1c59941814060f0b5401c04010050580b2a000080050719600103500542c5070340179640400c032141c1c80d0401900e141000342c401030108920724503d0610045007246440c107101006003850103200c5000010801c0d00e0008070b80c05121902d80c0010710034071758026415002481030015509030340c0d1546035084424802c2400107000e1036000070380c210800006400000c078070614183ca45558070010f641c2d0003200f1046008105078403145060000d404c1c588200711403001d503140d9607524585034040040b221080740c0200204c3c0c2200603420a02c000c40c00502c0601852409106892400d810070300c100f50920750205031b82c9041c000209000c0b441c0010000c0c0b01c10601e040580d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 429676258 429856115 := by
  have h0 := BRFrame.cov_init 429676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 429676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 429676258 ≤ n) (h2 : n < 429856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
