-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4543
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:57:52.791354+00:00
-- url     : https://prove2.me/submissions/a07c0eb5-8fe8-4d70-8eac-fa8ab96de9da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 816906474 ≤ n < 817086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 816907724 1250 816906474 816906487
    0x190912031b021c0309020402030a0c1101060815040203070b1303020f1c020d060b061b0c0f03070b031b0703030f060803090604030b13050a0c0603051609090515030d020a020301050c 79
    0x100010500368400209590035600c4000fa04201c001e000220002504a4004403c1c420a0104c5810030403203d222641c0e0300b5190409445640d00341c1c0e12612448882e50440460b48903142e04481c04075034002d0003d0f080729199541c40500781d00e1030b17001e04051540401282000c2c402c6151006035003c0d541c4080310000c8544000c1900d20315400c030000c100a201c1c03920b2014040410603242c01511000710700170036403502c030802134200180e4088422800200303809400c000088a2a040d41e541c9202c58018000308005070400b00358607116030001e818090b9052400500341c00912180380204a40b500c00ea80100e4040d40d0001d02380180c0301030382c0044919402c14085100c142e21030005980849400c071f1000c1e8510f07204c0350380a41411030b00079009406e0f805482c42940501100740c2410044070f20a6804003c80d55a11902e0012200840c4144000034085c00d000c05c4003d100d0703086140c001c40144100d900c0309903043c000903e04a5031034403150168000d101808290302d028801c090b40080c40d02c02083c640074 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 816908974 1250 816907724 816907727
    0x1903051b03061522052412061b070b10172a01030b0303030c03040c080705010212071a0414010c03110427110702040b030102180405190912031b 63
    0x11180340c10390380030703450000c14083c401880302d41c0c2200a1840f00005c0166081002c8000818400c008041200c580020300c1c1c0711441c24082890406032004c03602616050b00d805081c1d01003d41c040e01d10301d5000109106141c003155005441c180603120200c5101b010314038001060165242d244108070044d0040c01108160361903c51a24071801041c8a040030625260b070010390003004188007040d098031011041180c9103040c0e00046016902908090b80400c1e44c0300203590ba103000e28020307039006030000c405c00e6030f001d1121009460300c00c1c0b043c414005038030b14000424500703440071102519036016114800d55038030307030a00c03c030013944810340350911a5690918440303449201d240320740e4001a6081011a400101461500100b810726403420302c2001085000001c00303030810741c0c00364411440c1002d10841490140700321011462001614800c003120b00701007000401005010440825840b01220300200d414428002c4484c4691203103154181c405a004007107401400d140c125031250149500c010780d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 816910224 1250 816908974 816909001
    0xc080418020a1d0f0f0402040e090a060b030307030e1302210612070609150e0607060207030207090603202403090607110a0803091e0604032c0f1903051b0306 69
    0x13260550355040c020080340080344c001d00c544d6000d00e080507020000e00102c0740307000c03034a404020300a00c014880d101c903d00426440b44140345008000c07900106250825040041000035007090381400107040aa00c1002c075040c07544060320500b002c500089c1000b03643e2508a060101c4c07114901700804c006e40c01c142003e480d400e102d004640080e000641e1142140d4421004492035000c080c000704d41b1407000d8a8150040d41010381c0450240c0112080840e804200d40b240303100300c03a00314122a1000ca01d80da01c0a079002451280c1c180c020b40702e4414981400c0788100a403544030000b5030f00554074a0305a806c2802c0020260803881008500d01009031841d60009502640981041009a13071b0f485401d4411b203052018815022031140b2071244e84000340001c1b80d018850343c000e44640036440d00c0946034107440c802060b203800e80c1c44a141c0a01140d4244a011030a4120029040c070b0040c007141c80f0494503c00e201e03441143c40d0747c0100c8500340d0f00b00c01c1d81c1600d040500258024101d50815106034500c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 816911474 1250 816910224 816910249
    0x106050f03062e03111c1a03060106090801050a09052802030a0803040506130210050c0106050d0602070c06180905130c061107060e0607030c080418020a1d 68
    0x944000c000309925a80e0200c0400071402100b00351205a43c03807103030510f0400700101d01030011a01c2d00e400360f0400e019450807117148a00d8540c20b41041c0045100400041201485502c00c0030b0032946095150744040107040e0207046079444491003030749480d00c1d0380e0946400400003a20780b404c2030350020005600017214151040039109011613821603084a03c02c400c45001e029506110b4440c00c1001e01c00300070011400745005500b03440f850395482885151840003000000c1d0801100f49080221a10a401810480100b9030000c605070b0796510002c1c0002c850004d054651590018080c0e080144000000c0010103141c10300354245a1556808018040305102e803d403032688907400144140c00104541410680c84245180d9440e102c0390014080c5107051b0300c41106100d81003000c030f40d445c00781441851201c0020001e80ca40311803590708440d03503081588102d0b0848018440810300392100350301da160700d12a000340143c442400d0b21000b484101d045030b21020b08040b548a86d08039844106075501c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 816912724 1250 816911474 816911497
    0xf1902090a05010503090a0f0305071202150406020a02010f0905070f05090c0412141b03071a0403110102011b08060f1215040201200c030c040507120c090306020711090a05010605 78
    0xc60766551501b50b4180444500000c045030340300c0d0f12110826801101616402e4000c540000c1c410403501c07416030380c4060240d95402d0046080e80010000780702500105401c0146200201e4410820741402007603d1002c00110390700d400031302040c0041810448000c0c02007404407040034183c103094481c401c00f84514001c00c03030902d05224003c5c060040703510f40e00c2081c080a41c210381c410101c4c092121600251400004c2c400e008031200050100540c040d4440b0624100502078940f501d181d03550003154100d00d07a81d070f0640d502d4048148424011028012480000d40c403008901c1c50480704114141c000c41a456208480e06943c0c04104100011703500401d0300e603c50741030016184e500050f6045030701500071019004141b03810040c1070b40e012541003038884c0c041d401c941d00d4520020800c4140c074421102c0300d0004241088075031204500b80c125100400040c01e102020701d881e44c8802081e40d01102058030442d1a2810201c07a40c1000f90b030a560002039254100b01c25410118018407600c2003200c400c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 816913974 1250 816912724 816912727
    0x5030a09030e1302090f0301050601021515100203030108060906011214012c0c150306010f0c02040c110607023d0906050105190f0b030c0706050f1902090a050105 71
    0xd0415016440d00d84685400a04480e0310000d28142d88010703501c03990205015041140700010b25003014010310f801481c0507005410101d1181402c04201c00d80100030100400108030900d40f00d4648003100480d550b6581e001d1940c0390f041200c010315141c00a40140308035407000004101580e00e8400707007440c00c1e5214040601303c039a00c3c0092805408050f03820410014049180c07240d0b00088010004890580010b662010008108221000441d0000400d18000030070000b00350358031422030044800c1c03d909203e801d107080c0b030700810201e840ca4540c1c078010580101c55003c8a01c0d08000c401c0d445200c503c0105108159096020750f06207065010500780d0980e6445800d4240700700702ca2400c0c901481030308001110180c00c044026290031711800e4024207403820700d2141071781602c1c4400c0580d510000301c3d250681c50301c00000f15650005000202410b01803010a0000f00d0701d01030240a09011805103500e402d004e40b41c0c603440030740304808040c81803040203c0d00c2151180344031141159800d08046 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 816915224 1250 816913974 816913991
    0x40f03170c030a0c020c1914060f2b09050610080316030e01120e03130f1d07030212150906041e020f0f0324040501050904140102300a0203060105030a 66
    0x6920700606c4102d8194421403112100741ba540c110a040c804803100a0a00080b6114210a015142c40b03081d810904203d0100700b20745181e032501071118001b844050b5172124546040300164100c03980b080c4104c0d4903070444402e101d40d00080c06142d0740900507040246182c0b21207e00c91507611001d0795001010b101020340c02c00c040d80e0142c000303184804080c020a1104001e035a101e01d40f40c6e031190320601809217100502058554281c1044001d4510704039070390100300300c90382e9041490350000b041001050307001c21031300411101c650000b9008001e00111941400822000c11000b540000d10b114085c5103090444c0c8903031196034001c2c0e40c0c0c8409884006035221003400e00ca4016116200404155010010a001496120744020802100480b00b4003101c0f118400422040c0c0e00c0a106150f40081030700e02040204441ca00c41180d681d0700f010005251007040410668264044400d083ea000300c11000516189034a0100c0e983c040e00d0500c045203945000c10020300300c0d01002d400ca4510517580e2604 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 816916474 1250 816915224 816915227
    0xa05070e030c19050a060201061502010c020706050d09080c06070806010305070e010c0804081e19080409180501060f0501120204030209043e041a03060c07020f0405040f03170c030a0c 80
    0x2200301130080509010382003620b403000a4064842803140e80c00f41031141c400e8090a80c418451565815074070b0780900851840c1c8241202c0700c3d004a442000d80660f03440740c00c0002003041006000107010140640b80781d241c0944054055040184a181070600740000c00803460390000e5030f58103070002401c01d90a100704138100340d4020700542d040085940326002e0b800700481488a040040070100004035280070604121644101711103e0004007008001d0005204041036500546c1150111079900c15100845803141802d541c3c2e29803011031100b45d158002c0c400c2e5680a84801440c2400350030030340c9400e04d50fa010666118000303001800242008412400940c0b00302e00f04003c4e410340c1d1f40702e0700364120400c1d24450700504032084140720318540390041010101e220840b0040301070080c00340c45a035482c0c101445e215480078000304c3e4007901100c43c030b8a55589a21a440c0918081c0444d115400c41a1501a094001091a00b8412076144041015500355101143e60200b1199008620081c444a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 816917724 1250 816916474 816916519
    0xf0601120c05071208060a06230d09120e010f0e0f01030e150a14130506061302070b010b031e0c0414010309020d14100c020a0609050705090f0a05070e030c 68
    0x40060003110900d0b28003800941c420800d50240504940d2507c10654450301070300c4425210a580340b8903c0138902c0f102000751514040e01b00c03c02e01c0f00000c6208641661050110401d0b00140404030f92010790001155070704c100300607204182800d100c2075070071182001481da0982844440d04164840b511000030707007400d001541c1044245400c107101c900309035041e440070b04259125843c880c201c6c07000264003204c0f084c40d03542946401ca40940368544444060162640c003001003281075075020000d01c170008010541040c02400c600c441e494503402d15414400c1940c2d65803066004584200d4203128014044208a9085419003254203041ca04c6600c0103801a18802c240694003070103111291003448142c2d100041386a003144140c402803445c0d40002401c445611102d030300144d0240280000050b005d500a00f1206e00580484134200e503038a0015021880860310540c3c01d20005c000e11080000f507024103a000003040c2041c40d0a0b504030b83c080790381c401940443c207120b0042e10400c0e480c0e0f15a50716 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 816918974 1250 816917724 816917737
    0x30a06050a15030c080c12040821060f0a0312030903030b1c02010f02010219113d020f1204140f0d091a030f1f0f0e0f0601120c05 57
    0x82001c40701e55501c10421403600b4801c8000c1000c00e05080c00000c100b486440820f00c1400c0041c10942080710788040132000d010b0040c000c45e40900200700380601d6020021f02014241124060802549010410710181340c4420b5101801018051414000100c41461014000340140381c0061280d480f03007000c4002d8060a04080d4101031107440000b4503204895900c3d480740d000b0780b656135a0840c044000ca0803842400d40c2040d414403000c0c100c0311080e00c038a040101140d401c40c04c95140003c6015292034240589820b1410440446035a1261014408400f20000c0d694007003141044440c0361a8030140c899045080c00ea04400400030b802c200b052443c880701c1d113403040d0813600e0503c0000660b542e190203142040001c00d041d0070000034001c94203111828070701c80310351241e425074841800c184d140d61009408580e10040708441611100c2c45100380c08024070155445c041010318050101072400e80141040c0d0614541c18100305081e41c000300e041421441550b07000071001000b4800719014010b16 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 816920224 1250 816918974 816918979
    0x201061a0301171f140708040c06030f0912080103050f03042321030a090909050a060b0109080613150203091b030f011a03010e03120c1e0c010f060602010b03070506030a0605 76
    0x10064001d4160070342d05c8150f400300762004a03d05601e46c00c500342c7d5a0b0344101c80040c10348000304018008075210760040fa0041100101c00300390841c05599158081c80d0345000701001a10407401003051100030804000c1075044e03140614a403608000c42c1f008809041c1c0b400c0d4022000c41d2401c8601522a800703000c082c0386030141041c3c1c140c802d880c6020388a902a03840040020221f01000c10035100c1032250304900c5612200402c0d03440441e40e1504040d10031f110502d4107020414400048401060007064840c841c20110303040034580d50701d4a82d0342c6d800c0300c4001c05011441401004051a000580c201d2501d00c40c552106800c0540d400280c501003c0e10300780d803800d500303000d02c0182d20b449015403207510420440080c03003003032400c0b00d25a07600c0c010004200014400a000309411044041c01000001142010115062410460110a0750024041303240d641e565000e000d45441300c92181c0320281495100912503c000310b0700003580d46066001d110b208000c0000402c111050543c032100040a02 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 816921474 1250 816920224 816920263
    0xa21060b0a1e0e070207051c03030b12010608010c031b2001060e06030f03031e0c0f03041514370c1713030912240c0201061a030117 58
    0xb4500c0c1003040c00240720341442e48074442e0100304d0550012070b8440039a0405081883c00d6104400300707040b54081d110081d003d140c2d940c014081c003a11075074494400ac1c030200340049101c5180c1000d0908459011494070201403030516604410f13000083c5c6d40404100c3d07450710400e801c80c41c4038100c64010100e8030710740385580303000710010b4034648500c51184614021801d071140d4441c00e01c0199145d20040315040040c408944040220b842c6020255030400303040c3c080309081c28041c0e501034040358400c0e10b040c0c40c21111210350380710586460140d035109800060307191b0b0060030308180038010100031628210798100c0140f180c032200305140400c5040d11002840522001000200180264000b01e182032040c2004e500002e42c0030108200c03560490340d2554a4241c554588500803076021840b510440e0000390050800400096403142c2c030030091806e0034001807941e500d00380a821640303503a0140c0d008407180704070084040b00c1d80d006e9074110b440c1f0b502d00d102c500358060191824070f11044034003042d0100 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 816922724 1250 816921474 816921509
    0xa0206100f0b3403020c06041d071806031e0605010806040f09050d080103050d02010c0507080714010501030c1706090a0201030b15030703020711032e0209090a05060a21060b0a 77
    0x1004000c0c41190f8005d40039621201c02c10410b0210324400e500a2030a003298070342e0080d52402d410200140e0200c0c1c645040c0107400400040041c600106901c1100080e803503079450340600701d40302c2d4410001d550032802005251b00d0000041d0503080010400c3d4800d45e03440f0403400003803890381c002c1c1d031105034800300f543e06c00d050380100a80b65020a0200791411720801402c42c28880c0140704014179035001d6101c5504000081da142404d42c9d220000449000413541c2111741005000d004803030103940f0502d0464402030402c0c0c00d40340e241030a02e4402c00c107a0f12400501100000c04100801c000e5020318001c101da040d03800104e0603040c0c4c00715004062020000c2000007581d85507000d0080c0c54130541c034a40c41c00c140a0205070341c0318954031b82c45980d0004141d2080e0b0b1811298481304144102c208003600b02002c0034002168078000312504a42d0355150400c200d45440e000007000080d10f00134449094640c0162403510031f0160000d40140290f58401c440c1d5080d6030781e565604014610300c1078080270802d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 816923974 1250 816922724 816922807
    0x1050a030204090207051e0a110d020d21020c0a030209040f1a01090b0126071107080f010b1c17070203071203020a020a060516061e020f0a0206100f0b 66
    0x1314110241d001c0c10010100707c4092000407609a0f40e254014810200c1441e102080180c07401d2004c00403680b11501075041030001e10011094912410400280d54242510000180c00d22070400c1001d0f218a800300b00034401070390780e441c11540280d0801a41030b00c40b400b80c50100d142d0b084002010b400c001d1b0410000403c0d07002074100d41f482841c2a03039507071001124030481803d0081d01c00c1070040034071203c0000911852040e541900d83c998400111000144d0380c02000782001f03500d480c108a40e9456000303451483c2458480d4241d10b100b2203a15120f02c1c0d8090322001c0300d800500503042c420a500041030800c2d0342c1c0400413031019210341081100b1440316494041d648140301d200c101d020382e0840000044140c0594252050146c3d0a5074000e001241030340c1d02c1c5c0081503180d9020301c021050900011090450340b02601e01200324101d4140d80c4c402403400a0301e0601c0081800c0d00c1d18140c1c01040c8052108004a4003c507040031030f0a68507164503551140c544610580380425446452500b8581c62 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 816925224 1250 816923974 816923983
    0x1b03040b070b011a040b03010303080a0b041107140d050a110f06190c1d0607050a050709060f080f100207110d0615140306010302101707050a03060b0a0e01050a03020409020705 77
    0x25030704195090328415208413041c085004a1181c2a80c11209000410100f805551410345c06044080c000401d4005440003a0803600c06007805189030501103000c01c2040448007003503218119136002014070f800c641d00005c01030301c152600c40042181c681e00130918124100302003601b014003181500c9540c074042c01c80300711040b0025040c00026040040007510607002e81030310f100f110101c5250681c5050200188400b1343d12114003124507104019264001c128103026560140041c0c07080410000d26014141e2107020250304001c010782c00096640440700000180800310004511026881389440d05107803030ba03c0e142c400029001100360100d44100501a40f1484030403001d01304c032102190702c1d0800c4218030307a07a0305402a00750740204010320240c642440c12486041c0d441c60400d04428265904035540c050986822002c5000800c403e081c50b605809004040c1440d142400e0410b000c15000803d81c131720b2100820b06220300013514020091194040794007a08000c1419540c0e128103107001580c9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 816926474 1250 816925224 816925229
    0x5072105101b080609060f0a050405130506010608090309090a0b0d0c06020106080102071a130f03051305011704140f1b040f020913020f070c081c0809031b03040b070b01 74
    0x4880c9071040c03040032140160f4045002e068080e0244c90f090f0303620001e11905042020546a1010800c100000e05541d1409036610a0110300385400144507135113050380c94400103801020a20850008125040c203002054601c403100441e15425542c545c032003058000c0c540c0c480700d075410146440041090000d44110002103c0890303000300305e02035950599500300c0c028103e00500064281010340000019141070342d8220903015180a0900b03140c0ea24090303000800c500480c00b0810204d840b564801d051010200181028205a10680c08080314068103400040000b4058034040e00440c100706010444074043c602d400d4112501d05886c011024054a245220240300d039003070508401000c0020300039107040c0d00c000787c5803a6000284c0711a8002a4005001c0b41c80104414860f81000c42c2112000000408140000e002c46d140c0307000b802204040d0344048075050140041c1849450300000088900004114000921269110b400d05056108503130042c4410720005c50110180300102000f10304 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 816927724 1250 816926474 816926501
    0x3030f1b0d140603100203060d021201021908090705030303070c0618151e1b120b0d1401200d0b060706150807090c080105010807110105010b0915070507210510 70
    0x4001d9149178840043e84811101650401d000304034100060410242c5404044c08640001d07042c1790a40c03103034040007042c50044000150a4806004100b00c0034000b03900640b0058010b1855441d03e2900500f07441c4050000500e42ca40e14125141004100250031341060392044207000214000341c1e05030003915604175414a424540d40d000402c520484c490103600c00502c2d480900701440d011405c2e10003a551407030081311540c40d446500d100e980c0304050050350320722030480d0350034400ca018022421510750590858a21005041c00c51552486006884e40010544030203e800a91400032810a002d0880300401143c00c2c9000d410a4003507112510051350b1145040301d400e15604e400d1071060b90381c450009000301c0e404100500083d48100d0030294401e045080a401e1206849420350071a2402d80c4007500d4810041406030041ca064007003055100c5240124074100401c036103915482d10030a104410850745039440c20103000380a0007030b1f0340400b500b020980e412404000f40110103003c03900310310320 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 816928974 1250 816927724 816927733
    0x5010801020318160303030e10051315020720220f0c140d0c030207140a030207090b03121608070c0305070f08031803011104120b010803030f1b0d140603 67
    0x411040b030014a04c40304055040c0c5065425145850540040c0555500290030b8000d13450610590111801424010494182d0400b8021031740d0420b402994000b00d16020038a00401400e0702080c04002c0d0100400000d144050514003040d0018005561b0040500321010754650390341c1c40f805540d8090040303080c210505000140c1082003c42d0035240000307000d1071082d014000985000d400c1d92003c9048601c40c103005241080a4880031125950442840d415509c0303030108004040d41030044800a04081205018000c221070000381c407000d00327a172484005030300818000404181000514040c0d900070171b010741c0e00d1096090800305103010380010798161141c01c1c000124510889008e0046030440d201850410b0301c80302480c250040182c02042d071540d2900c0031051100b4401c4d00a10060080400709081c907416464824070041050f8060403042d00140304020b1521171558440e030b0b11002040d0317001d44014075100341c04c1d946d0103043c0340c55012515100c580000c0420040065000d948114102c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 816930224 1250 816928974 816929011
    0x60e220603080c0607030608030d09020409020a26030a0e0906030a21030e0a020f1c080406020d1d1005030c0408060711010b03010603032007420e22050108010203 71
    0x40d1b0a450641c86140722590003001018a410340a41c082c00301c0510040020034a0802500000c5103000c10782c001c180c0c18802c1e0203100d002e10040c030241d60408161000038500341703015160094503001c40360120314001c00010000600640d01444603006c1541d010034a20154021107003107100b01030182a142c008a80b078002c40b00031071030740040e00f60340545c2d008000c00c40d400340080600402410108020b030200c0c01b03442c04100012004c10290000c0c1145600820014410360002440f031003243e60603c403642d154440c2070850740c950302c0d021103d00c041e50a001e6640d8545001d80200b078070503a40954040d024440c103010300c1035071000c40300d8030058181009101d48003002c03081501f00c599620000740498035201b2406240c48401000e1094020b400007540c0d0719543e07501c0c090381d1082180e0f25102c0020604d401c08034410702001003240300303408126600d10140307030200406060b0a45290990388186000e40700e1341030214111034035003c4103003818028805c95039102c9160380030f500150b81c074090502003180ca1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 816931474 1250 816930224 816930227
    0xf050c1006080f06040f0f150e0609012003012709260c0a1709030f0c090c0a3e070306110903060a02090d05120a02060a06060e220603080c0607 63
    0x4135805030b0740058104a21110700da60703a110a04910b4011038850250501c0d401482d441446001ca04aa280d80036103010300d04401d0503400c550016039003075058000f04440d40148042c82c07090300e054606d080e030001c0c41012111002855010040c01e200401420b008120040017942115001001440c10100c075240d000c4100000c407501501c0600401a0300c20b644400210308091304102c458144022514070700415100440e003000301248408915034884400c10b0610f003081d40001d03a0200e401e00c0102d0804040c400c00500201c0402c500039a1203000750ba140088456850030400149000d980c0c031018101c4c80c0ca40e09171500c01621003a92114641014043c181c4114030458681d40d00c001c010346040d688404e00c1c01e0080d000030f688143c10400b08074000000403010414004200c24030b020307036070b220070070340c58000d280c52401400514001e062500c104100ba41207258901a0741c0200c5440150010358183d000d20700050720469041117003080f50001c1070195402c002c01081c1c0c8420192101d40e0b448040 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 816932724 1250 816931474 816931483
    0x9030c15080c0c0d0e06090613030c410d05010506010f02010605030723030115030b100e0c0304050f03191101020903060103170d1a011701050a060f050c1006080f 71
    0x301d0744591300300503e1550450301c51304208040810003402c5a04003610310000c84e02c00d402c80070200800c10023080083c02489881d810007401840100c0c614400654440c3c1d2070007401c05644c800d100ea6840d10006840c0b2100034012040c2c50b003c0c0a01581c0ca12515420414041c1200752030f502e01081c405d42c5c0c5c0c0440c151060041c4010765101400030b1410503d070540355410703c4035a01100103902d03110611070815036000e0107a550742c007180a40c05049941181010264200ccc007918600d40240180c00400c039000e000d501442d40684100c240c1c64680c1e41d01d050440c1014090700512003039010014003070292000804481f000c024442e50340324102000c15114500300e210740311b002981580300c10300400005e070003400006106a004a405030920301c0700b421540a462000a0b106d0250b1407448040c0c1c010350380f00b00c1940c0b03920500714003005c0c03070351612000c44c81c0354913280103403010003001918152605008008960f00c1820300c80465911720104400040105520700801426004016003407140207400113 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 816933974 1250 816932724 816932737
    0x140304091505100216140f1314070305061507050f070f0f1a0301121403041211180a05101a2107090605130306050f0603060a0216060c09030c15080c 65
    0x1226030010b4203002c1e0303175044506c44070443c41d400780e40c4001c0072a5071b84920600c96002d850060012038401c0031103442c0c00012500420450406161008008003a60b07900041d40210039a01d440a640d803d0b0b07405c0c054281190802e00310110b00c10900e0008015580701d1110044400901e149507409440e006e1748940d0030b090b5248018488404c0c00180310540080c212482110b10030342410240c4440381c614503080d500140c0c000851418524060700030700070103403240d114040d0112481106201003041280c0d1160740078041c102000c5d0b5800010f404840d0801038200a08501c40b1120391900958010b00c1c102d0340135045000002118141034405649118007007400b070741d0689c0351240c08509040086413207410541c100194008660400000b03e0700c10700c41c550250020844074a00c0e80b51800900d4a4000c01501582009104010043c1e4440d902c44c9481003081e8441030100751840d20000440f2034076041c0c0c00c01307810045018400641c0b108002802520b8039070585841c45a82d8611140b01c5081c081c59 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 816935224 1250 816933974 816934003
    0x402160c120818010e030a080d1d0604060f0b040204030507180c080433020711060a020c01110f07080307060e0616030e071502030a020705060f071403040915051002 72
    0xd004050701c00c2001c8084a92211061401d4548241e11000080c1f80541084068544010026030841c0e565114003400312a542d120040e40c14210381e02c242296119002000549030564844401112800c42d4000c010440f500070400c0d900c0b503449007001900c40b00720b4442c0921240e001003004552a503540201c801000c21074855601c1a03031551201001c4114141144800c40d0f502540d0340c1c4130a6001050030504046028016140c904520f8501c0c41500c1400da05c91248405000313a12500e680058050301038402803a0a103c0c0340300b06120b0314500040520000701d54010003602140301c0600002070680217020382c000b404984050400c0030380f1a01c081c0c6800c080107880c038010180e421301a800c800d0018001004851003190384203011002408022410070050b000000d0b409103a550401036040504000c03540940741800368058843d0301c2c0305a041c002c0800306405168214070009005803801000c074040c00384219079507000d41c00b90380c1180707005061169100c0d40a184142d44000741802d03201804 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 816936474 1250 816935224 816935227
    0x5011d070e090628050a060518010e01050607020f13050f0a021c0c0c0b07020d030606022a15040321020105070c060b0a03230c0d03050409090206090402160c1208 71
    0x7079800d4584240c4c45000c81c10806860303240210501442c41c030550b03220362202880000c64074200000c100e0308500c01c070251b03c1100482c82c010701680c0c400c001d0050450750100e4100359100c07500e20121310580c0b01008030b15400110844075802d801000d070441c500c50700040c0c98420043e5545602c0034201e01410400b1102004210b50015129105a00c01024104e560a0140340c40050b607684041d01e0070100d90a00050b000040b501680b5034040c01440d02074405030020745242c1c5001075a4441041c08a0700e4442040ca03c1c84007400503850b10400018031030000d84008d07940e10780320b003848480c1100e803074220809800d681d602426014418400c00c5d0003050303c2c0e960164459180e40b2244c01030f07d4403418250b070080740c0784000400101030122025452004521210881c4441c5085608000b03505080c42e000300b021083c40d0340040d0b441400c4038203460507140700181024146c000300780f540c040c0801c407030f800c2440010181c00342c04548904000051044a5940802c2d403261001701e40503401c1c480080c0318260 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 816937724 1250 816936474 816936481
    0x6010501030c05070f060e0c0d020d02060304030507150209270604050901020904020a270b120a1104170607051309021c050f041415012105011d070e0906 67
    0x442d40041c90b07440418541039003442880c2e224071540200d080401c0342c80f1583c421072511003280a01050040000803144500c1d2038a080e0041030007114a540024070441c1e0010015003007500604c01d60710016008106a50610719800c00d800080d030000a03c64810401001110b08600c03007450400381403900100c1402a5890b2001844080c04010b09490007954080c4119001a215440601213586850f6104100c2e25810030f01030414964003103d6000c4009050750a200551b8950100d420500e04900d50080a55401c600f400091108415410045a0005001a01260309056460965030b00002d130b84183c0c4071035500340c42600c500704100b0200302d20b46000304005016a8081d10a440a071964100405040044001100c1049400c8402e0850480a0005101511007041c0c8030108180c001c000c10400c100c02c542101c0740512891581004041100551050480810418651000090200d0701001e2400e038205254100039400314030404a00003003101c0d21101181c022080311014000ca44c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 816938974 1250 816937724 816937727
    0x14060105100e0f0d08030a0c09080105070f14090301051e070f02072304050a140a090206160201110a23010501150e0a12121706011d030a06020d0f0b0a060206010501 72
    0x203c0c08001c035035000542c403035072030041806000210302c01d500d490703000541c1401003200034000b0500c4d034020302026071500042004068111850404801d0a804c10103201070011200600d18072a5800da2a055402c16043c805070803035408110041c4404260265515a98030108580d070702c1480da443c030b00590050a04125504c2d00102c0031291103201c8140e82401401d00c00480c0680300c080d00d0f40600590b0b140744980302201d0380c0c40f5094004e0741d01501844100000e4000808901454841c2c010054021150390110b80c0510101548d508691003912a003001d603091141c20040e0240403584117891030856894640c0d03040c428541642c480d05400b06494001ca01d00301c2d4a185c540300801e80004030004049180302c3c0d0381040c8070f480c42c41030a04001020007100010501580c0011f00b00441c1d00400030300107640c0c1c02468a8003c8034442d010714080b011720000080c41c2c11038566024080074030000d2001c20028075030700081c01e0644050000c0c09150b0420091140c0030813988a1080160820401400380c1c1d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 816940224 1250 816938974 816938989
    0x105120f090a0602030f150a1d06061b16091503060e01020c1219050703170a0f090f110f15130512030703020705120d1101020f030414060105100e 64
    0xc404200326103142d0040d50303481089038400e40310003003001001d10070400040c0700c41080901800c03090340c50504103803418905140c0903008580b050b0840c880360b00011160780b144000e42d425124404111502c00910400058480312844241007002d10039074000720350700b541030103540c1c0c00015119513401d5403403464441c1030062041001035a040d5408001c0d8400c540d01c1000001c0c0034400307004e1826a1050155811904005140e542c0401d0110520080340881c0e00f250592802c2403a440c25100b03039980300900341d8028056001c0a4103400e01e4501100148503203600115000c40c030480c0f22590428503a000c00003504900c00030150b003d40f1040301466801400c20280082848155003100e01e507803504009035103041141c00c02c50880d80080b610409040d41000300c01d0040000b5680c28048415000070700b500c03000350f80b10210502c07006a210b03503000082507045640c08035442034a03a8803820685804a01d0f005000219890b80c42218004580c0e1700e45034003055044003e503101c500c2a141c210701400240c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 816941474 1250 816940224 816940231
    0xe0f0405061008090a24050a0b31050a0222300c030f1a070504060f02150f0702060c160b090f01060e09010c021b0d02150a030b010e0105120f 62
    0x94002c1542100020300e2000804400c08901b00b900203058004610f03c50484500902c9031101604042c00386100e074560207401c3d81094100a40c0e2040041c0e170b880c540d03610902d8903e80c20100c910300006c00035009600d038040c00e00d00041440010441200c01a1806960f440e401034604075542500e5003480464604502100348181c0c1c10811821032461300e03444902ca41c5075006580c611031441910003040110b286a03148803114045041c59401c02910003061401140626002d0004a02c01940d5850007001842c420a440b030412000074035012980b001c03082c6042d2443d402502c601d10208092007810310aa0360704480c1da4483d002452074a0712940d424031006841c0080c180108080070ba8190001c1c06a03401914130700c5076101443c10240652170859824080420440d0084980100395201d8a200040807031421070f0200107210f407600000e0f040050b010b0382c1d251010000503104c1030741e44c2c040d04244480c4200741c0341c003003c51480c01c005449034030070b0005031030002e483c0000048d1103510081c80e80e40c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 816942724 1250 816941474 816941491
    0x306060d020304020a0803030f0f01090c08010b0318011d0601050a270b0405090606090603030901140c2a04051509060904050c0307030609020f01030c020607031112070e0f0405061008 80
    0x40701580d86c0d0f146411640181d41d00380c0615000004c2180d0060001ea405004141c05074041004449c00000100070040c180070312028045c00201140c001c101c2e46609a040200303075002000507006202481d14486030aa1300002c0500403000005042d18000d0b03000d40459070b610405039811000300c840b40703c0d2460400d0095291540d40c2c00d441c165900c40340308a510942c07003c001403600342420020855041c500070202446540204445103441e41e0007031301140c0c20b40c0c1207000261600145110b50782441001700c10f40400036500345000740c0303a61051480c00140a810b890030826034548900d0b055402224000068011008902142c05410701440c1668000d00540070786810001110000341001000d500656189484800d031a05603d400603851408000900341000710b5442e07450080d44034000100070006040ea1423940010740c1c03403d0b40c1118030860304035034958800c4c03514180190102199101c114040c8215851448042c00d203449001e00919000704980503802c4910805c803044400108030a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 816943974 1250 816942724 816942739
    0x605030f0412170c090f0303030105131503141b0f1f2c0a0909020306070c0c180606020c030106030804150e0d12110a021c0201030219030c140306060d02030402 70
    0x49456080e80201c40c01840c213400013583e607a011004000928a10403c81803090f00b00300300400603030791242140301010550010101c5c02402c61076800d0510090b582c400340c00700c1d0000a600150364404542c0310f010301c118000b0342e502d01c0c4903607044c0041011000303c415000a00c082950120790b207038103020f040039083c0746080c03194040c200301c0d85507980300fa0050508044801890300f01e010305e8411410006080e20060802c003800321600001d54842002c0c065a050041e102c036240188040e00c12258054000c002c82d003200f251151805400400103886000014000e40c3d07600207041ca41030041030200c9802c001032601700707803c00381e035051404a0b80c2e030030000344200480f192100b0b8896003103190304140120840d40c2041c46021010740320b11401d451010080d04142032002c011380d110100311412080018070440442c0340c61006900a2240800c00350001484910800c6010781c10b800034200e044046c1c0e90381c5010944254205020300083c0c42035640310300103014000c000c82c0950b01442c0c0c4940010b0004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 816945224 1250 816943974 816943997
    0x120306060f090a03060209043e1b0304050a060f12050c07140c1c0c03111201152103020c06030a020412030504050103060e090a030c030e21070605030f0412 68
    0xc03402060fa60045800b1500403c43c04403a1605116075000489800a04601c100c6000308085001840701244a4034400e04000d26031034207800019140d10090714071442d220044248242e550f42d40051003918401e5801010219401c0d00c035013140f4013009210341720350f0303980003a00424001030000104030320380a94083c4040b10100d040359640303031000e140e07280152051400711001e1201c03485016400d588540750340e9480c0c2c000540384541c1c500899410450030741e00e07413400c8400140110b46030b5015090320748c20319180100c142d404201c0e40080310000c00048000c003020304003075001b400c110b05d07028025070404803402c0300b5400d10400440d4481010400145429129100c21518000f11030301980020340218040c045942c051058a0140445510f502e01c14078184e580719a452980000080c00c00c40084c0d000c40415001ba5201303822404010201826101e0b041a883d89108640c0354200f001c0c843c020000542a0003841140d0068422107140d0030141c0d1591110100c4c15100b07000d071410003000d0f0410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 816946474 1250 816945224 816945229
    0x601080a150308120c0f040905090a0f050114090c010516080427060801150312030b09070c02180f06011b1a01090e1b220f020c0609120306060f09 64
    0x4402451080302540e844e200400341e18841d01d4802850351406100400207100c01c203140c0000e6074122194000c01181965031100607e0400100c00310003010b0321001d4148104100042d008842d803d640d80c0c2000c0c2c5c40d1b61710012901d68404a0f040000d010460402c141c07076070301404801c64411030340200c0e5070034a400d55688031051108000342556000f552501c0c54140d880e48207020b484000d104070b0300203003c81d200650400e02c043c4018070005010440810107003012a01030f030000d405083c0c000b00007203414900310402604e4001d24400c101e205021039040208811005102c841c0a95460800d4204e65501e410041d03034501000c180c0d00c202e544072102e007440080ea9031071040f4004074004841301c815514250090043d540320040041040c2c10020040c82200c41c0111641c1050740103c4046088a505c500d0742c20030340070495a0100401c3c1080c00450b140d1907180c005118049510048501c10765400200d151241400002020041402c0011030801d1414401900b644150110f000d441e0030f149800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 816947724 1250 816946474 816946511
    0x51c0c1a031f030507151806030507030c0804080a031d010203130201110f0c01050913020304050c1c08070303091109160906030b0102030403350301090b060906030601080a 75
    0x4403099040c000004201e007002d4001001010711011060800035181076a84031a1154840c5c01150150f0b40700b00c006110251180d5a90161842100348001d803450325800f00034040e010803520440440e06004410740201e201ea070303015110f650402c0b40300341001c1001108902500e00e91080e0303501510851040941c46d142071008500450854070301c2201d42c4291700c00941504d441d000c0ba080c140c1c014a40100050070b01003400400c2c0c010911b415595041542c0000715072448081041f00414404400c01041000006481c2030041044270784042035803000301030070f85960706a0801040071500380264000640aa00002201d910501c0e000405010000100e040c0075001c85010000301086500080760980041d1232402405481c5020700284880c540080c1d41d0f4400c40c80001c207072104010031101601418003803501d40e8091680d000d40044000d00307820403da0028082c2a07025890408044020f18040781200ca210708050300080c2142c0e104001515000f5004003407020307441c0c6424600c02407003d00748 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 816948974 1250 816947724 816947759
    0x1404090c0e06040b01050703021e031c200f04030b0c040e070503070315080c0906030f0102030123011b080c0705030321010e07090b070602041208040e10051c0c 70
    0x24900c5a052501c4070402c02550b82c4d011200341880002c2007040003003a170104d907075023040d14541021032124440300c50b039520714422041c01c00305420b511882c24054074901d03001154112184070b40300c0c2e0500010010005148561042840260700030841000000c8600002d154450050000d55050a45d07840d00030110030b4003260030000040e4000200300045806100303503000ea003203048850070024204a0040d41e07820080a459208162038030000e549540c0400070380d440c200b0f50714000d40d16542d46669060088c4030340e14402210720180c6007003645651092070b500c1d00c0a2600c00501d104410551912801075102011051444c0100d01c00880c0903101000200041000c1d00d80c0d2440000c42c401c2c00709070000b01038000743c40740300d148414041100d80c0084a582520040841c45542d50704d145003000084c41a944610350301d4202c6070030b50084c0281d12002d4003c0b0303030b0f1021000000d03550755600441102c106000b180e80c841c21004035003650803500303003109001610841001c4800e0f522221520080c05010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 816950224 1250 816948974 816948989
    0x305010501021b06030105120c1207051810120602070b01290f04030201052104080d0e030306030d110106091a10091a0a031404050105090105010803070305041404090c 73
    0x114010000ca5030b0402242e035500d00d04500d915498010340002840d01e1006106e000d00c18407000714082e071054400e020680c0c80c60300c002d100301c403403500f45040141c40d12413504c29580b280c0021144510250f410814003441008591032003000142081c070004003a0540305da003a100d0356804e0024900140010b0200c0d4041c05807072000c464451a0154040341c20510440750091800f41031045c0505982000142d800740c0c1d070f09003030941e16807140c0454a5081208400c0120030561000107000038021340d600100124440810103101e2030305800a600d60328070083d41d0564040e4800107003150601e1140851002c01c40c43c180c00403c01a6542e060607040e201c0c51804044ca403003181d0301c1071405d460a00070040a2030400c0c1007442200f46080309440031112034042e8120f090900050700741c4d006d44658407a22008243c101c0440e514100740c1071082c0204411200304400307601e00300001c2040301c0000300740c0c2e217020751603941c9a24090800c000c000910a0441525403c1a2a49503400c002a03a04605c0b6010b0300c0710 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 816951474 1250 816950224 816950231
    0x507051519020d051f05010912020f06070308190204240302041d06030124210c080c0301200708180301180c1e1e05120307060b030c090103030809010e01020a03 70
    0x840c0c00446182c900284801a1780303086881041aa43c00001c0f9104035038094980164841c000d00224495401e0701d1548ad40c031040000d9808105900454400e002d01854000c1c81000450f84c4581c8041788940d000d01c107005c1d071038442050280072403080851074602251a01504040d52a4001c0402c0b515001c112204802075a041002d607060910030840410f005444880d2071041540303030f85424060900411400100428007071421844081841001c680d000c0510100c507560383d5485030311941011400e034802d5003400c201d4444003103d2034044400c01c480c424510301e40040759490885660065802e085520340d10102c65100b964203111300c05141e000c0c42440901d074034040c039001c94400c0c440e4100900b45d9445a000014095044940000b074816901d1000c280c441e09400c0101c3c02e20195214030b034000003402d1101f405003408805010320622030042440081005404c2507241c458104010781c01201c0a0010000700344214a130700d8014849500000d00004003c6900b820390707011410300c1c070200781c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 816952724 1250 816951474 816951481
    0x20901020c040509010b12071d07020106030c030b040b100305030d1508070b040611070b09042f0d0f06080307060203180a030503010e01050306060f09060f06180307060507051519020d05 81
    0x1048110100380001f004041c25641d401c080300004d50120000303103c80070f900601c2c00a4000b83c000d500103006903800091020426a5030302e407a0354502801ca608540c28454500401c840101c030130004401d4a80c464003942c00c100111640000a00e201c40d2034000c400b9078100e001401500a1080340098131546036900e43e80c50034407002074040312520758200483d40c0050350400410050000341d03034040b54210b802241c8401c9900003051551480c000e550f8030502d040c65105500940c81004020111000c40103101d402c1103400305404441d240c0c4502140398008115800000704030360300540c2e000c40e15102200035404040e80c914645881d0b58002c40100f01c0000040c08402104050580100300407002010545081800b164440007104505400756810b000030452540d80c10300c1100d44040c0150160f0307150000c442c0c0000241010070021030113800b0f1400d0126010344940c040765600354201005007135402a061b010307509164001e0510015003c02107046544003464001449003000180700840e2031706 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 816953974 1250 816952724 816952729
    0x181806031209062f0102160c0b04290c060a0b01020c040509210418360807030212160b010509091209031606022103060d06020901020c040509010b 64
    0x440070088002030002d204010420160301c04e40b80c405003400b105500301440340290007904074100007501c00a495001064075070103003041030001c2e0300050007a11107030442540c0702c1041e202440b0303901850141c1c151444040541580c40021403c120494485440c60000c0c0c0302502410071205803185d010781340d282c1ca1408401c2d0383c1004000140700c0d04550030003090404034451a03840c0fa080000e501c1b0f10b0300283c18214020310780c400b41c8000345144040340a103000b416105038001d084085004031000c6d00004900d070940e00400440c1e10748443c960424005080c181c0368607030306412850048046101e40c00b160911040310601803c0c403005201d4031001c510500745405081c029050b00a10b0103001200304008403110700240c8009403520070300420303507210707000720210b41883c18544040c60318583d60034000840c541c0c002461502c06842c0151980092400e046d840381c90300c01960103d500091400c4071102194041c0c1c01404103500500445004081000c080f03000d40d1800c403640510b0340d550b8510b03440c460 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 816955224 1250 816953974 816953993
    0x303040b060402090603040f02240c01050108010c0e240414120105070503060d03090f0f06141305091f080615030604080d090804031401050601110f0c0118180603 71
    0x50040b0390075801c085468000c11000c0c04020405043c2d080e80b981c8107000e42d281d03004480036002c43d0b071b44040488882d5130a091103a030b209680700d400340e6180ca00000350b0000c062044505443e800e50381c0014a151420402c803040c00c0c02d48a00401c2212105050000000f050085c4000c200d0307084120042e00c82c1800b00101c1140d039013515070607a4188070400c2062075109042700d03408501215080c101110b1420100c62045090700510620031545601081c0301d40503082002c12911250303141c030418140170650100c24000c1906170741c0c02150010701403055140c8010000d5000003c0000c98a205850f5007035003a0580255004140c2600204103100c90106c07080b400381d1141405a00506e1541000d43d0f45100f1407088041c0500700030380d1800050200825401240d00039500000554000c003009045d0a0003090306540f41404609000300f0780895410106003850648008009882e40940340001502d02110303000216181962140c804108101d58164100f410307171031070900181e117070708501c4c141c0042c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 816956474 1250 816955224 816955231
    0x60806041406040b18160810150f0b03070e0415050f010504060c1e0f0c050405070908060426070303023007030c0201110d1b21020304020a12050303040b 67
    0x40d410000400c800f240e506500d550300406070503414805d040341c00f2103c90412a80c8062079039110000400014045030024508a41c21580041001440d92010200f0580750041c0700710078005890240030007801008801030f507030111480c01c080c1541e0710410002000c540e04054204c8440d05240c2c01440b180c140002c90000500c42030030503510b0300e414003102601c00c603a28000203004500c0e1a00c4071034400440d40460b6091395004142c040160340e20b04d00b844c0e41d1102070240a000d185000e001805540c8550403410071200d2500181c000354846464182602890707042801441804900ca040c046c140340d0001c1c9001801b0742d50042e199013824008c0903118400104404405030141f19a441d843c03011113040f50403043d0b9040010707080945080a90140a04c1403d170a041c0002041040000c1400c0d005000305103503603070301199400c940301d0b011f44d581603659018210401c00803c01001d1a4255402903402c2400109a40069076030b4882882100500e81000c444d40d40011007030004200500341030381d41 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 816957724 1250 816956474 816956513
    0xc1805010e0601020a0602070501091217090304050f0904020a050306100f120503120a1103010b0711040e061317030a1413050c0405060409060504121103190f1206080604 74
    0x140d08000000079a108190b40c5d000d0012540001e0603c02c0090075840140b100c0d601034007102003401140b0000d0030360455141e660344201c4442c0c0000700f6500c0003104a5054900041c0060151165042070162601c00148200d802286201c0041810381d802c1004500c2003032618903040055081034580382c0c0900882c0e101c3c80301c1c0d100710744a02000580201c00d41d000426a1a030050165030750740a9032003d0200710030340e10078242c0e00200100d4403402d0500240f251720b028040603140e1803d11380910080b40c42882d01c035603180e040b040200d4030040c0c20040b003002e0240101c102d1488929101444c1c03c1ca41c1c81500c04942c1241d4a246605d892610019080e40c01020902c01ca4101c6295499041e21480c007480410300c140d0f50f0760000f0300281e980703510904240c0d4012004014510701480d0000341ca80c9031682000200c1c4560390000101007000003114611030f0141a1000350800b850801c0d20001c154181010074058500c00c0709426030318034840e6000034400c01000340703420308060802a82c0c1341405036440e030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 816958974 1250 816957724 816957749
    0x801050402090f1b0301060e0a0b36060315040c05191b0515091603020a0905060f030604060504021003020301080309090a0e07121502161e0c180501 65
    0x10250760340da102254050200b2201c500144c1c0c690010f0a440f4100702e1444240000110022070403903880385981860000035643e020b401038a03586003600d0707401211105174038880000011b82080da001e051000178544681d5a0b40452154940002e92a03041115107050440859460b50301c185014011031241d11840d051281c40c04041c03040382084510300480e00802e20100800c402e50124410712120350041d0030505032460110504409030b114031064541c02d1040c465031010301c0e04082e6401214089031750003480f028010303140444100240000801c1036500114ac6000921503440034401544039238441c2100140c04c0c54244108a0b00317a0845120200309441440141f01600c4000308569070180125109107580e5501410302c0003500e102403403400079000b100c1000589c3d03011105030540b401c4c03080f05000c00031075040310420120f002c2ca00721110484080080c02c4080307680341d83c1401000c00805c103000d611091130703102c00a503c3d216a000056003035204c030818818030340c2d40c45218050900200f020 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 816960224 1250 816958974 816958981
    0x330106050d020702150d020310050901060f120207060203101a032214010e03040603111e0f0903010c0c050607111b0310050903070201020709090203071710060915080105 74
    0xa21600400103440380c210782c005148419540c0c0c4145100c54003100540705503031213529001c000c0103504296464109504c500d80c001c9814a807001103a810b03150559280060022600c00449460568000304a0440ea0802204001c5290f40c0003c5120794442c0c42c0486c0d0592410048034030f49514001f0b241d000ba8000d03c14040c440101a504540039450700390b01d411402c4603400c0802e4550742841e8920840d40c40e03d02c41c08150a00030024000b1101503483c03c104040320290005518403c441d8807184400038040204401c10a610280500d103698860342818a240040400d007140d00450074140490004404e940801c00c00304011507101c1014a000740c048007020225590b0350404509034021a0007035071651a10351010005040c8940d0f21180600c000e040000300c10342c03a5030080800780c0c014040c00c14046503242c100c0c007407108100e9002d4010715684c1d00e0700b222400d080d4803604143d0024080c003091111710514034041c0e41c0240145070000100c3d41414034914054460a9021600310303410030080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 816961474 1250 816960224 816960227
    0x11010215063007230609090406020d05190614090c161415061801060f0e0301090c051809030906030601030f050717180a06020307020109050601080601152d030b03330106 74
    0x9943c01d00034251031f051540d45552a000300030303004045243d009207181004110800c61980c00c04040001400006c000403501d40142c0c1c1a0400380c144840d80001c0450701054920702c4d080300404283c040b01d900b050201406940d07495009007030035000c0c1d246502002c01804a4144462041d410103002c890391b42030000282c0c01c5501c81c3c20144503450901034995400c0300d010b80100c2980081c2140200204401506441d1510505543e4020f2034001c0000202c10074141c40394144a501803030440700103500301808030003001582e80c001401075040603160601500c103140306000301070003041d01d03403900016003007011440d00160600902d000c000607a402c00c40811188046000c24469800c50005a603a03524040d0580c0174065404004009101d80000015004000b00322181a0349a01c0804080b00300100c004560035610302500a9042c0381620302c4608454440d01c1000240300b25003004100f42c45c24400081c105400d901c1004103030141c0e0302c0090040c0000181c084201ca10b6580c00301180d5040610 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 816962724 1250 816961474 816961477
    0x50406080a0605130b06041d090f0c0a090e150c0306030c060910051b0a030f12060e0c030604060b03090a020307080102070b19090204020313110102150630072306 71
    0x1000038030a540da1740c0110b1a45610046501070500310040c5048003c2c4004000840e48007150010024021792001e40a54480401c000b0300c42c0700001c00147c0b2003800d11326020000d2030303a990115444d11851103d01030f030064604086103d000e820745116200d107020010706003010082d1048a1240c50200b09075162581c4004400341e20314003030300d8030305c1d1101d480d074651500c03414403803c05002e580300300084c1d0010143d00400c11041d00d050355680801d4030040c0d201910170740da02030040c2a1407505050009646644a002071544030030014001314049580e41d00c3d4401540c42a00c083e5010b8000d05900000d6040411000000b0200700008500e071210070f80b10859140700c0038140444c07195142d84c5007142409150858584150010801c6503031381418040e000b1341d2050207508403000512803010407255800841d80c2050300807140409100f55492900700601c0c1000d1340d0341904401200300380c400d47c03904c3c0c00d00c0b0710240c4800400146150340c101b2004c001c450884441640140341c0c518001525500c50070f0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 816963974 1250 816962724 816962749
    0x1906020613030f030c091a0406020714030c060c0c0a24020708280803070302070c0b0a120b190b03040507150509040209060c0a030e3a0c0e07050406080a0605 69
    0x80c0000d241c80070200100c9040d04103600580f11007040f040181040f0b41414010300448106030221600d16030380d20ce03407080140c42c0384421035040d040000184000c0c100180101032403081c12041e142d211503090300145140c3c3c041c0d0044940f02c00c07a80c40341c25a51800140c0381203446054002072005c0c501e4001074998481c02100c01c2496400d410304a061100c100001040001d03500c0074500ea00c13413600120040003508680001d503101101c0c42e0001600601c0300084a5402d1100d80d95001d481c00d850f007208010340820401d07a0b4010405880500c14141c2c100c402030040c01e81d02c0354081d41d0741801d0500c10b103408450b80050603900c2ca0803000800703aa401200712446000300b518003580f03862503040058010302683d040038a4500800c0b031000d0070035904c501300f0036600404030b400f0340245225900c0c00c044056481324207010101600100052100c9400400354054812008a45002e440300000d040c401c1c000c2d641200805c0011806010180e0092205644510440c50401c20a4038090000e800300113180c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 816965224 1250 816963974 816963977
    0xa0614062205100f03050a1107170f0d020d1104150e01090b0307020a05010c08100e040203010605030102070f0308250c15051f14150307030b1906020613030f 69
    0x146624084459500d081d5002440028004100181d90b00c034094400c0840d141c0d2800002c0ca003000040b0250240e20440d80d8200ea00e440b15400d15200d03581c0d41c000380c040008074071200c00f0309214920b15010108010014076495520141c0c4819903940c81805a50ba0b010001521b41400c1c00103020100c07103140c60440c1e00003140740111000c1c3d61280180c500f402c0641040001174000020010b5940d00018040c5096124400070001000c1c084801c48042c038040e1139503001c50b0054102000180d901c00c4010790003500060002038860b580310006400c80c0e11017182180c0481c901e0401105040e0070000c1580d001544c42103200e4000f600401400b40c40c0b00da0549e05c411712062480398000d2088045500c1c0202c040d8940130000f504000c45a9611640001006400e031901010081340000801d5000d4001c0b100140c40d1001104081c440e442079500001c0c004010541d485c0000340d0030303542d500c10a21a80710815201c461450034240020308086005010b07003411082c403403410000a5108014042c070500c103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 816966474 1250 816965224 816965257
    0x40623041a090a140f061009230604180c0801080a0c03080f070507080f011a060301060c0213060902030609070309030f0f0c140f0105130f0204090f1a0a061406 70
    0x140d0168400904242a1151595151034208481c40c040e41714042e0062404442c45900364500d914111500302e41c6000e030390300300d2146031b00007a0a818100c20366040c14078000d001c5800c240c0c440340846c08000011180c4159513031901a13100409030491809805440c2c100080c2032074080341e80312820082c400c0d00c40100342c820300260041030800c10f00240c0709003d5101c0299100340c3d0f40c3c1c2040e65612800c10300c15290079403070303c84403401030000f0800b286c2d413055001d805682181e1a0000c1500c60800e450070690300020001003100742001d46115800181608900058403030600d002403000354240201160181494000044080f0781c1003800180c0500d07481c5400c017040581d0031002c4403c9485200d0080c1700e0400600030090383d11012640008001000c2c00802869a501801984032a040d240280ca41014125840c016082c640c10a090705801800901025901aa074900c005980c15403001440e14000060050800f1b1030300405e001030408002c2d43c01202003400011302984603503250b16440141 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 816967724 1250 816966474 816966481
    0xb120c040302060d05070212120103020607170d0507030f0902010c0b09160806090f061605071a070509010201050108010b060f130312090303020d140703030c0905040623041a09 77
    0x52908840280d94007405090700c030000c49603100301412055881038058010800039107140f004c82001d131007652481e90111040c507482c503001d001c000d600502c01501d618458404003a5412022002880300f2004a00c00190301d160a550040840318046003000425040c5192200542e03070290400e401d5a801121030b00a5888005405103010b008414501c1e10844091000510440203d01076200b11284819141d500d04000d01481e110f5000f25204c80c3d903e00d9241c5c0004440c3e00c40c10241000920070001510301c01038030404030b00c0c128011607080000500010b1210355559084c0982070042c40710030020b210713182d140000940503000303020640c1056100881d803d00c01244011155000390f4006540f0840c0380e1445e28003c120a074a03020550240c4150340012414500c240c0c0c8814082c8482c000260810b003082c4c0e022400780c03c900304c840c400c1010b2042c000c030740755071036114072070052050003140d43d1080c0f00800c0b1540481c0001c409184201c1c9840004240740d240820303003400c400f1381110b40005a64 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 816968974 1250 816967724 816967741
    0x10617010617062e030f060b0301052809061715160e0301061e0e1305100b0f03150a0605061c1806050a091e0c030209060a0b19090602070b12 62
    0x520510804d1445603000d05100c94160709540142c800c021030700014002d090312507540c1c0e800f9100a00c1019001490440e50f1241150002e41d000103020030413080f031940e940c0d580343c0d100c1503c1c1c079600135100c900c0c40c07030030000101c4030100000e030301e52540300241d0300c141d10340b941d031401680035100d0015052110392200503205039000c0d804038014009a21031145031040b4050801c682103468001e14514100d07510100e100d120380b0360301c48038201d83e00078024240c48002110007006440d41c41c208a4000407104a00146513800b40300407400c0540d03c18401b4000e1500004010036100180e1002303008400c02c1006a880500e203d200100020790604081590012440250100e0240714070160017140360a052050b503680c513401445079680200c007181c0d54161100c1e43c002d049181e460000301400f00220003000182408104503070f21150042c80c0061141da0b07249502520351118440078100452208030070b100031f0300820b1520280c0034520080087da420a6aa41c1c060f1080400711607402c100d4400054104 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 816970224 1250 816968974 816969019
    0x3030f02030d060b0901020f03120402060d06171b010906021c2003040509070e010503040609030521010914101a040902120f0a05060d1e0b01061701061706 68
    0x42010081201d40e0391110a01300c0350300508011070040c0200000f5011071030000003599103160f203419404066449942c20450b240d40503d08040d03134191250070000f044054820b01824010301c50000e411010302c3c85000041411164001d0740c1800b60f0b0840c00e020240c1c2c0002c0a90208200d11001011141214025528040080e4288602010030140c22501704404400390080320001c0c1d0303065410351204201510399028142049000600034000100410b02c070340c0010fa0003d010381400c42c9401807010f205c2510410030070450a030300e0400070040060703008d64401c80c404003410b00024106420405c03041c030702045982c03149041801a45198010203203404003141d00400f2510740c11540c944c545205494540c0084490441305600c8000140c5250303840d01841d4030400005107001e401c4c031519500c0c1d0707080045100103140511144150000001c0011740c80300d004e030110340c40301c01c5144101d00641c141220160009010000c41c0011810107421340c003a4a60041c004844001c0708c94001074941421 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 816971474 1250 816970224 816970237
    0x6050a210503090319030f03020a0f180308160b0108031e0a03060b07032c0102031c06051306030b090a020907110307150614040207020f150403141e06070903030f0203 73
    0x1340c081c44000140d5540e5030503100100c1803003502e80c01401071888800740d0032802102c201c080495810754820000ba48246045440007041d100c4030640c4540f207407100c48403074010b41d000040754141e5450440c00d014080c600d1038014a4040015440e20324a24031a0924881609100440301004500d424146020341c010201403d003205209803981c260b420000e24004418690103880782e140002403017081076540c2c04c0d0b00e124206030000d5103001c040c0650304000c004e145101040803991818085816600d80d0000c0c0c1042d00207c2d8042a1a41107050480300c11602a011244592100f108600162220440c440d4001d100c0e05052820404181d071860451299010041c90748140300041e04c0001066405001600c5201d810703502d09006c04000e000480c440d83c003004e98003221040c088811403800e004400d5554036145055800d155590365105c616407e0580009c0694201e0031008401c100c81ca8055103007400701c400105031500f80460060090f01150002030b040090008002400900800440310b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 816972724 1250 816971474 816971479
    0x50c070905160e030f070e0a06050409050706090e0f0604020a0c050303040b012912062d0f010903020f010c14030a11060109020304051009150f050a06050a21050309 72
    0xb458816105441c01455802510100c0e1840c0003142c998200000c0108541380400d00a0451500b441e6007000d00420003404022200e440d07035404503981c0c40c1c0707008614445202d400240300da44d0074450040c00040c0b141d002480d03455646020015920441048a5006807041d02d0060380d501211804071a030401404c00680a84070002c144010050b094a03203604907072051380020451103240c25024020786104040281c0c0100a000e4543c80c0080c119a80c0d4120070b001702215000240949030b4061140c04800b0312405540780784000000d4248a420034010034006d1904a5481e0f017903900003107d0419814080d41009201c021741d1007006a05100c4620f0b40000c80d080701c0d00c515503c0001800c1462900c5000401e000b41e100000b2960240d0003580c0c0501d0703200d0050b048000d84200a1001000d00103802d9440605640d5804a0304281d403090f682c440c40000f40c00319035441c100841c2c1c016503110b80c1c0401d015080c0c0b01810803042d400311282c049003a440c1e007a155201402420487e00c1c60168080e13003039 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 816973974 1250 816972724 816972731
    0x150108062e090c0c05010608060114011d0a031a0a1b0507050a0804090e010e010b0619020a15060602061302031903090510260907181e0e15060d03050c0709 68
    0x846422080c0140c4240c82817009111480d201d0f911213864500c20710036070300d07503c00392414180d0660256500381040100040c0800501881c10300083e1030340314a82c402d5940b900d004580500d810315000307003a82c0c4418030810030311090b08844103680040e0242c62805d010080d010034440100b1805102042501da0841d190341d80f1580c6580c1c400000341030f00091002035610340650800c8000040c0944440c50b20010441d6003401d0691a4070388c000804043e480c000c50050200c2c0400280d80000c040d0005105107000040380d9080203000b82c50b206d00503101101108078090f0010050b500001e4200841d0400a841c02080c601450160707400b91054101a038001010204560040e604c880c0c02c02c4640300d140d003228549208a4820000088141c401018982126505102c0001c81c41c011424003c0c18650014401c0c01c001030124500409082410441d034a500c00701d003100a04001d600c40c0e00f840380c10940d540341020f80c00504181c3d00003500030180301005c00e0101426606008100040003503907400e1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 816975224 1250 816973974 816973991
    0x25030f081c0f0609060b04030204022b09020406050319110105040305030d050a050f0c070308220c0e090f0c0907110d030b0a0e0114040e030d0e150108062e09 69
    0x1800603002802c040e20040d4946100041c01010380e0050400f120b1200301d0701441e040c107540a000c003a50080341c2690012a41202c0506002421f46411421013444100041c1000c003610400c0140c610035440248642e002402000c01200703c044000c2486038060a451000f00f082e00040c0d8203800781b0380c0090158000419140c02c01c4081e030300810310a071b0010008000c5580e400d2015a9100401d48098132403e130f09000e5200068000c14505030402040200e6111000036030448010540da0f0a40c21209603c5005007048001d041da0f45054000d02d880001d400388841c103195440d03032441c41c440c03441d01c40c00008010034802409800800783c4182c10806541c0143c07181305003e0081e082401c030b018001c22451314005680c048079681103040e10003000d00f140c1035a444404202c00f400e1441202d10309400f0400c00540424480c7c802c10090300c181030058610301d684114549003a0030705900001a9410000401109400c2c05049003c071000a00c032400c02c1000c1d800941800700001c1d00044002480c00482 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 816976474 1250 816975224 816975277
    0x4050604150e100803130b0703090b0711010306050102010b0105090d14030a0513060f05040b0d1d0d110f0c0d0321020d0c021606050d09020307090e25030f08 69
    0x2410f00c00d000400300785101903a074003801540ea2084031005551480c0a00c0107000ca100590020540c00c2d010b0b00d060f4941e40d450f0f40e02c0200c554010030040341c4080c0800c3d02d04445582600600d401400b090000300700000c0c80c41c0000e072130351103200410b44c41041401240000c000441820900c810b00560440341c4800c400c01014141c1e030f0140c6244042201401c500141c0d880c801e000c2c0040d400c0d01036440c0c83c00c0615080340c003440e03030b040070f04000c802d030380c6400c5100040c0d098840301092662128005019900c001c502c00340c00c80c806103000782d6154103e1845031540d0303078000034a08906032059402c40c41c81c4042d8281180d40c58268004407840701074039516406104056000381c8a050240d400410502040c14410f03030348c441405007180e1814649080801c001d501841c050080e100644101160803401c03540020306140c1c00303402c0002000e84d14146000400320411442800411403420380020004003c4050195581403200410b041c5030004064100042001950861040d0011407150001035481 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 816977724 1250 816976474 816976499
    0xa050102091c030903060e0a12020c010906080114010804030c0b13110111060a1a0d05030430110126060316180f0e06040b010302030c1e0405060415 65
    0x440d01d101e6100d045101e06000c40051402c9050b56164a42c8001d161560362000094011604002150300900c0c0c1c50f103001c14a503c0c880c1d00741c0021039000c2c0050741035181c0094545a00c5230840010807040e0030040c081d4905400f1403513282c003400d0820034096500c510341100d08184c22400200304a41170710900050003800200c5110705841540005c07100c003d9507004445075900d607480314401e0f60010f27000c41c8860031b06600005a40304040b0044105058981c040b17803104000030000c840d29880003804114024103058804d0302400025070b100094545055588144d030000d000149c401040f200078910701c6d0703002314602c00c24074441011402102407100c040c01c02041e000ca50301350082c011114220380240700b420201c0150b5950141d000c0c0131090901c0301720001c2500070307211005190740314440481080204181c46c40340b40b0a0043c04815815032041c5410070792442421b60007801c0b2500c2c60801c0456054888125402c180e800155a9607071000103409000c0c80410005201e078510008150081e0021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 816978974 1250 816977724 816977737
    0xf0e030417122808090a02040c050405060f1c090203150a1514190501020d08100e13110d120e03160b0901090e0403020309060711060a03090201081e0a0b0409050a050102 74
    0xf0748203240801c4502d4180d075a840d08940503040d980103190300c040103181c80d9121450174500b501d081410103840e070010940a9201400422400c080400c002054039401204070070440108801880f4a010550100780d6455002215111107800a00040c0d001e258503070180c011110440100b511941d6a2042c280da250541d040da50301800030b0042c0c0680034030b4500f04e20401ca1f1010380c010107807a11403a90481700c4410107058410003486010000402043e02240715004100080c3c030582d0f082d03018507000c040c848020061600941d402120200400c1000c0c20703c05070784429040c0b03c40320300781d407900003800c3c030702008407030100300c902c080010070340102400c0038010744002038071000c80b6592101007081c80c4603c210740045c0168000c000d64a210b080003c040d0180c01c0c070408540c1e2500202000280d0250041ca44000000b55104000380c15581c0c0410380940008558843c980602e0060140e00495540203000c5007000c0d440b400031854640310ba51000000d0380d04002034405411f45441c1c4075020f5030014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 816980224 1250 816978974 816979027
    0x30a2106170c010311090d050c04020315191a0a0c0f03050919080a020d23030325090603020c030405041d01060f230d020d0c06030f0e03041712 63
    0x196180360b8a500070304c6404214800b0308501c50401e42c1000c01c00c80450030120040ba468083c1c41c0468140da29640080d41c00384140681001041056809102c2d00107035950003a84130800802040183d00c0c0034240124860394042c004642e1102c80850030b50303818503141002410008070b6404c103030034542c0c0700010f400d4442c0226001080e50520a420a042508500809a01c0c0d0042c040400040c40c1404170080110721481c162041117011501c841d5110036191401c00807500004100586408100302d2800155030340d4075404010306007084003c01d43d03030050064109050380002c03514041c03142081941c3c010308000704203100c03103c3d1080d02d07400842068482c004c419030a005000c60401c0c042543c101c142e03030208100d00d1030080c0703000e84003c45000c3c58a500303070031226a40720392000d81c95440d4298209400f4400c240d55080c50180b0040c11601c4085a42c0319480c0303010044024042c0c00320495045800c403541500c0c48850690810382402c414002401082000040010b500401c544103612030200c01c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 816981474 1250 816980224 816980233
    0x1109060c07080c190b070f051b01120c3f06090f050c0703081909050a110f100302030c0d0c09090e150105041e020a110c030708030a210617 61
    0x1005000900c0001507141c404031070080e105000782650b203000740040d47e000e0300020303035801c1c034585a8500304004d203440340c503161080c49107004a41d40c1003d082e0112400c141c1040200705401100109401101d540c00c07140c1140d03030400c03414480d00c42d48007080100034044602c003c18000200480041a244c880e40b07007440c0c201282c0c41c5d0751610360300c5494810311109480500e4000d9070307a4100d03210380000b0310104030030410051460703020095116452000e0300c250f009000702e54050400c5c00081980c80c00307440c45610400c0d50440191501203420318101e8048c03c01580b81c3d107c0184c0380c0d550380110916000c0c098580b0a00381c4106502c801884120344190400f000340d520400c1c80e064683c041c0c2c0c0c000201140400c001045a810264401501c102070100d000010342e8104180d4001c0c1e80c00030100c05c0010b140014100740080061000c1048000200d0041101e1403030002d5003510f03802440d41d00001d0141000380c5808820344004250414449540d003004441d45640d10a0581e091180001820340314 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 816982724 1250 816981474 816981493
    0x904200a080109300c0c080601090501061d10030903020f0d05032e031709131b020316032f1005090a03091a07020607060504020f010513091109060c0708 67
    0xc107000c1d1089110700d008211081c034601d011003904c040c5c2c1a00411100c40c6e19174440000c4580b0140607450103803004080128031549403a10003803507660002030f4144110041c0d444001c2e00e6540c0c5c504000206680c0c00c000c100e044d041d040907800c1641c5e2010f4030790f0900400290006030355100c0700940c45412120301c0240070700142d11000003160003403640c2c3d0388080b01000007840484c4280c13810311404034109801074581540c10340071800b803500c148500065203840d80b8004882408518450781200e042c6e00c01503040c000074108403040c200c1d5094014080c0817000c100c1c03240041c41d4000703403981d812690300300045003030001c0084d50703440c054486501e0001d8505004180d0200380030400760210b40d0140da60a000c1c0307040c00b042c404c860040d0080001130311002c22a07040141c49120141174203a018610004a43c6000d0050204402d85520024104001001498040c0b4010701c010019103a001d0800294400720f0700348009030b03114a03100c0340c0e4490404605856206000078400c0180c403065401d80c0c1c441d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 816983974 1250 816982724 816982763
    0x203090607081e060d0228140f090c0705010e0a12170112020909190332030412050918040c0503070501020d180b1201030c050d020904200a080109 64
    0x1480001c1c8502403070040204da10342ca001c0d0008030310107000034020804040c02c0c1000480310146904041c210b11711032041040801454480010007040a9074001c1d580c2d07480c0710000d41c00c402c1c0180244002d40c408203981080c4032013584409089249842106c031340d001075007030100f00007403e81c7c204000280911075425840d0303450b1056034103c40c004510b1010344c2c165030b420010300a100921801491042c41645090283d40b101d1400c2d1b4580603450303da003030b507400030682d40c0d03030382403003a450154092240b00c5035a2240f0358804aa9000740c2181e01e0031200b078500d0380c0c103d800e0b11411031040d520003551000903010015518205004500c0780244404180d9a0f070103051312000281b1031117015800c03030000a140240940d11300301141d8a40e0581140246c3c580c4000c1e02142c00105840b084a08144014010080c0906c1d026000e010110303100403200807190300158260a008000821842500708200045454101c94480a000003003e450441e5260900c46000b00388603001070b1041e1511001001011 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 816985224 1250 816983974 816984001
    0xc05040b010509040b1f0c050f060702060112030507050a03200703030f030e0a050d090312030618020a0528140c070302040519240b181c0501020309060708 68
    0x40c401a10380b582020f0003c0708210060544c2e81d4141c2e000125581c08601d0320103150a0500c220792a0307202d17003e01c0d01d400d04000d440c14186164000c0c40381e0051051107002a00003d040303044a49481501010080b1854200c0307250003180700042280c8102c250304000c00d50006030700c030701c0103203240d4100a003900d041d000d203955090b0a1101801040200007604511403191b081840200908402c41e041c4503a075039105860a82c041c1001000582254018020081640000c0003821407a1400b0301442e41400e209030303902601149080d010907800100071004900480030b6500405103615800ca0740000c1400078803501d00341e41d400100040468950009041c5d10384152200c11041c18020121a401c1d40e09010003084060310f0402c0ca005104110781800707400740240000c04610421651424225051030010300728ae5801111074540f00b88200440d10010500500222000b1241e1120322021465008050700603a1406095540004100070404100062041c001c00307070381d51a00010f90f00c40b050a180b0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 816986474 1250 816985224 816985241
    0x1713060e01170604020904060e0406090c05190b0a0e0603070f14040e061507080c0d03050f010b0a0f050f0c0318040e0d03050901150311240405120f070b03040c0504 72
    0x49182c000720325241059400380c042682d0152000a0190700c50140180580c400c4400320340035078460240000b00442048510300034401514288007110002110400090b030901945000d0480410800e010300c1c40742c03000300640000908401c0e1307079060040d00140003481042c044004202c260000070303056800c1da070469040360201d100203111a05d0f51420010340c0e50003c500c4044220081c00060042090030004060b410044c1e002001000400040942503a000a219603c1c0420850042101e441440c0172104002403501e40201c20604100f4283c602d401944e0351071650241c00720764503a03100c030004000c000882c0300440344a0100c00c158200410b4818000c4c1408841e08441c0385a804e8600a030403e07504660801c00110301d6180c00c030301d8403200c000715610903602c03846c4246001015080c441c41035020700f41b40e40001120001102c1d8040c03840d110328411b0b82d014004110701c01c810400180081000b9074045800e482c8015a074402400c09038005680540300c0d495203450010307441c5402e110b8181d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 816987724 1250 816986474 816986507
    0x80d050414120d081509060d1112070f031a01050d0308040f0605041a16050a0c170f12010b070302060a020306040207060609020c1603020f09041713060e01 68
    0x16150400800c0100c020540344601d4101d00c440310100540311041c40000864550344e5100c0701d81d0b1034000340b80301820030358178412406107001c00d0a12410ba00d41c0500300c2d4009800c81f203182036042e10103020900340c04034200710811500079090003140c90142c030f1103100216405915408a03540009a43c01d000789400e100b40c3e0790000400e81c03568002409119625440b5000310300741030104041c0d403a000183c4804440c1111488152240224543d4020141c00c1e044090907000d80390003d42560044c180d031094041c40e200388252100310703030200802c10780102120400c41202c6c64680e068200b10b40c515030880101840300c0c52003540081030344a0b06009980c02031f40c15500404141c1c0b100c0b0780540080d032010300050380003602001842c01180382c50064800034074008100585c0d80340700118060404c5022920554071241c82c4000304090703a0303107900310940302000700c428100070f03115464400000d06011001c11000c140114203801c4a009420141c2c0440304c0584031294804107080c01103600100e01c0c1c11909 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 816988974 1250 816987724 816987727
    0x30203040f1a06012006131506060c0b0708060a09050c2b0507050a02060c0d0e160801051317160507030318240f11010f05011a030403020a0609080409090305090901080d05 75
    0x1400c180b01c860500440d10b0241781c0c20030040d0050008c800c280c600035005480400c0e2010172100410100d064000d03480504c500d402e000c83e05000380010303c000940d129104076252154007040300380001000321050261941208288201c00040802d0702c512001c142c2c0d400b031403820000991090180007221458022a40500034540c2c07480c44550301508013490401c042030f43c58040381c21010f420081d0481d40750200002031000341c600401a800c1d43e200524081d074510b501e0092600041c52141c2042803140d600304220f03211556800c0700c144101c031440c2c016145200d000000002d264014019021105440300440c0740c0648402903c4103900d40c50100140f442c0d9220b0007112214483c54001040388080d00d0200d48030340410a0f41401e480d070301c545403903240d50f440700104003a070040030b2a05610380c4540031032415440d140c0c50194803003440fa0406000541c40344084001c001c44202101c0c040e0081030300400609903d424000e00d550800d2007841d0103408050004250300000044400c030707070f000c242d4503030303 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 816990224 1250 816988974 816988981
    0x30f06050f1507030c080c1506121e0a02040203240102060402010c120e03030301180b0d0c050d0f020d030507060b03010603050c13021c0b13110a030203040f1a06012006 74
    0x11100e40d00940044c0c0422506100390350002e11000000d100c5c0e80c0752007008010b5205004e0030709082c0800078010911940c100c0d06000c0291501060300100d44c026080c03529000c1c0070640c10182001040c1400950103440001005600948042e01316503c40610000c130144140d44001666185d2058801a003c10794001407000040d00c0a202113110381d1141c0790054100c410440801d2031031f0000c2e0010802a010f2031260b0540054904c14000d001000b202e18004240154550039040c40c0c50b4002c081c003900d5840695014400451444020154003408282100c40c003400d005000b9081420300f12116030074030401d02854a01406140281d0760010302800301d205005040095422008000340e1105809222078040201026849031071b24420010100e000c5410300108044142444900402c0c07500d07041c682c68030b151152040d54842c02050600580c1e90f00c030b030305040703002d084000401072034491281c48001c0140036041506004030800c0c0c1b17688400f4014100f040380c440c0d50b40c2c1541e080d03d03800790000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 816991474 1250 816990224 816990259
    0x4080d0302090109230907200a0209040b070c050304060201050106080105120c01120b03010510150503150618030a230123150901120c09020c0309130e010c030f06050f 73
    0xc81d40d524070105c80d40303407500c0c0d8041e020a01000044440308081040b94a0b6000842c0c40d405004200c100340c54081c0030000e00c030703074001214410090710240c101c203824000030725094042c0220030aa0380d08041280d89507550344800902810090080c0d00010f01914000074003800c042d1401200280e044024180d02c442040c01116142a582c11108101d51206003800040d02c00303225050103131040144e00d018042c2403001e100104004150502d08201041042100b0149c81c007807080340ca2601124095910f01400b186400d03a040c400d00b049a25014440c805002c0084400740c80099483e08005d00d1103240300c10920900302e0f01480d202010580094180c131350f4910f00c0140d026840140007101c8600e91000c00049006901d090b003110214000000c0840180030b800b078140401401040d00540c600300b00c0e810b48548900074940c80501030158001421002100c641102c10315250b80c500800801000340d0004014240c903121080845160980100c1c280c00c211440300b80c00d01020b00181c40c0040c58400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 816992724 1250 816991474 816991499
    0x2030610031a0d0507171f2d05240109050f040f0501080601090e0601141011010f090201140a14030c0427050702070e13080d0606020304080d0302090109 67
    0xc1450841005525500b49039242070f40500355500030401451800d0500b8203011842d000c0300303505c1c1d0f000d0740580e518022032040f006c1c580c0d02c484a240070204460b21200540c0034901080110312060444644500200ca501640308600c10f09904100102c044000f814010341c07242103000141c00200f044c54280002e040040300200c0e00580544002035085141903048111034003a00090a5504148010082895070340248004602c058000e0411075250010300344555540b404800e0242000d02d1940411501a462500034000701c440207010103180809100000c110956089010810303130080c007626001e002c015111400d98940382c1c0c1c07010074032241e8214142e400c010003c0e0303401d840c2004080364003070301c0c00c001e400078030201051501d60001c3c800501041d100000c0c0640115401080d0402c00b1051320041c003a08201c0402d03120045a40e1401d00f24805e10905045200550510f82c000900ca94004001c00481d011802a11741d4244825001c8050340300f18440940040d0303003e02f06000091800301c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 816993974 1250 816992724 816992741
    0x10f0207091107061137120902090906070f0207080d140f13050a050f0d060b0d1a010806070f1d010c0f242a031d0106080c040203061003 60
    0x20303082c0b41040581d54501058a00c51280703071040718008030313111242d412180f658440c0003110f01c1304010301816091a0221880804521034100700204c0c001c3c00340700a540c0e003c3c070030302c540161449504e890404125981c0ba4020347c0d07900b000640c03485020f00200d02c00304204c4180c0e070400c1c004c2c004000c0c050104850a01c5051000e0300f07038243c00c0040d41d0601c554003004005418401250341d000301d242004200306244035030301036030003400c040443c901030b0750303039440d9940c409540454006002e0f449072000c90103031140c15100030807024408050528040a0608081c1203507580b80440b40560350f03009044460540e004801804541e00c40c21031b010901100c90f02000714001890402141c400d55140e48001c00008413069484548040814610480a048a103480400050f05010a80101d01150212a08041541c803c1c6561404d4095141d10035003091750b08400b40603106188104658040e070007414548600a0f491050343c81101c000c0c1003900990f442418018441d1a43e2125100c040e0046c090301e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 816995224 1250 816993974 816994001
    0x10e0303042a290f0304031d0d0302060105030c04020a080f0c0706060902070201110712020d0c080f1c0c0b070f021c0e03060a0921020c0303070807050c010f020709 72
    0x122455908494a480140c1c003d1400141e480755040d840314049208020b038600c902102d81080081c80d180751003c50460b1341069052070840c0e044680c14007030084d41594441e1442d40841010204414075500245d01d07410f8174012416580812102d07000c1003b01c1c8500141c070008141e00000003440c1c04803005000b540b0131210309107a07162026a640741000c49021303802a0400c56804502c110a42d684820007800c1c004886004040c202c0c2082a1b00184c010b1b4818000d210303140454a03030003003000c40b00c0000010060350707007100e42c2d07078450360503441c0c03140d1940c1c010344600c44070610142c02c6c11b841074184070400c40d04400d20b00540d40700c3c000200c840440d0b103040002981300d41490071244c1c41940701c1010f8242c00d550f40b070740810302c201e10270981089000740174069070504142c51440410142d600d0f81071403420380c103281200f52008031010b90401098440b500c2c2e041c040424204180441070008140d4a480b072025141c6009039040103482c54031240c0d440c1401a40b009500b8400c03000181c0c0104603030b001b030 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 816996474 1250 816995224 816995273
    0x103051509150115081e0115020a0804260d050a0e0f0d030f170613090c0e0c19050a0c060209030c030f010c080105101416020d060c11010e030304 64
    0x582a101100718080c0c1c0210052a000a13810084c036074030069803074110f6031001d4440010000c8040400300c1d1030317060180d212056549088664600c2c02000154035030b070350205d002600c45a6541280703450400130309140c2c0455203001408039502d6008a80c114005103682c48190408490350800c40d1609480b10000d034120005810139a011b54842072200305030b6202e50745003640004003500c020103032020300c5100b4610302003440c1440340c02e9607413416901401036254000910b42d2440e050004004042e039000c03006120b00f1005201c0d00400c1307038004088d1940b00e40310440783d00304505422580c1c1e01c1070080c0c0c03200096988440c40005541c6400501d81d050b0b0080882d402100200c0020741040d209114507a1366030f40d03681910f003107181c215005030b0040c80704070b400e00c4407280031180150030b08807148003007902903c0c0040c02d1215564003c0940c0e0000e60058103e0403540d01078901071000700a0000400d0219a6140d405104007030305008800c005d903400e40255065489540c3c3d0701c041c10407040190f00e006200d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 816997724 1250 816996474 816996493
    0x617040f08030a05250e09070c0b070f090f030222020d14040c090c0c060509010f0509010207060f02130b0717030709090b01080421020c03100b01030b04050103051509 73
    0x50701018500a02c0b8029000403141002c40b01c0b9241c004102c8a07454915194100f0346030482c1d003040000c4008241910180001d55400340c04a4800b92070030402040c1d29045400e0001055000f044442284c1300c0b501c03442d000c15168a15400310b0903180c07100940c84038144a20a0a500e51840c140000b402d00d4080541000280d1850314140c80180000744441c0012804100074818031070380e08401810721507070410584c03c85500041c144400900701628007515000807074101c0e0000d5011404814410300104110b092a05980f4042d602c003580a45140c1c0c149120951100c011344210340c008032162040201681c500441707445e650300495016141044190411620310304194002d62150149903070740c540f110f00709808103044643e01604941086001010400004c01c0071807800d41c15040464a0300041044000491801038403524050b050f010755491440002020b40103c2c1c4010004d80302070040c4800c85041c841214401d22000c1c0032640040d03900c1c5030b09000d40440d107801102c28010b98a034990b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 816998974 1250 816997724 816997733
    0x105041707170c01020904060509100b0a0e1c050d080105130b03030708042405091e041812090e131b030c03050c0a05010e01090918060905030903160617040f 69
    0x2044000090f4440c1d400282c030b2400c2d4070b044c0c810b4a006c0c0504444135047c1d0308006c4169009402c2501034015058030024130032020f5402000070310622813004101040d045456403041c038151a5401c0c0403500f40c0f0500c240501d0103030043c1c80145c107844020308001d9154030f01c501c05201070005103000a801d03000412040c2c0c0401d02a034020800b805030b9025200c1c420a0141000a1400c014182d01e0208030b400d000c0315046695210340a1010305210301c0b41400c100420000034000c00484040d030080710004207a0201300308001250030181c03c92900c07501c02d0a903940c108010324801c112100141362003100034080c0050303112141a0703200d001010503818040d40303039500c00c603d0300070315081556242c0c400c2e0414aa140303450305020700a80020300c0c141c020108142c0000e80440c40d58000e040308a070b212480e5100076071943e038100358142d0304640d091260021504090b0b440c0c0e8011b0020038003d0103140122031104086a015404072000d55490b100700300741c507150b49025030f0000382c0300308c0b404920600b00b8400324 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 817000224 1250 816998974 816998977
    0x9060f1c05011d0d17010302010509120303070c11240a1422050d082d0a090f0803090d08090307180b040c3209120a14010504170717 58
    0x1d14031843c542c000e903403107a0324036481c040070003209408004941c0f0310a0401c0015080e03d07811254203003021030722585c2080000310380f01d100d4800c182c250b100100404c200c1a41c01f031039810406001d022441c283c01c43c804140f0481001070400049131a504103140c110111901e002010500c2451030310348941c20300d490060003150f011440102240300400f50036030000222030500e8000341400c03280d5184502c3c0c1da940b5151300c1d002e03443d03d202a01c0701c20b001c03e2495104004c4c2000e081d040300c050ba02c0d624000c05001406441c060b01944600780084400030822940c000129455810010540400000c050355030240c0c681c820071049800d0b000745c1e0000035541420720b08000005038030450105480c21100d0a0108580b0500b001008016071810440e043c001d95038981040da5003807090320309807954003402c407200c00d00c103090105410048500d030300048144080390140c201c6118012010000700c2055081d400e0b9141990081c02c0400007004100d04220403000808807140316141c031662210718421906141d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 817001474 1250 817000224 817000241
    0x80c010b030a12080c160201120b040606110c0d0201171f0f080f0d05040612110708030610020c0f040e10090c090b1203030105010c02010c12020703060b09060f1c0501 73
    0x1c4070289120104210313040044658040042d204480c2040104007090a0203114907001030306210041174505018881034100030b0004102030310038400607a0b034010007000548240d032100039a01642c50140c0843c0303010440024540d40580d02c2c400801e07101c00d41d0703043c14040a07040c0f0008020788640c80600076001e1040100901700e49200014640c078241c080e44c14041c2407001c840860f013112070066035640d0844181d40a4402524010800501000d0300703000611140044207487c0c40c0210b2943c0401001400462088805440f03a442d180307c6010140d95442c080010320394400c2150f8007030300403410309074804070325402c0c0082110302c03e48000c0000400c6404034541564bd1610340403040c00400800d0180c010100415101006628401100c1d41d03280d00040c011181000713030b21102c139030a584c07080450f500c03a00d400414440100781c000780301071366581061004840950912015412624090065901c140c1700603241d030125045c00c00401c030640700424416000080090344100210300c09200c0d4019 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 817002724 1250 817001474 817001483
    0x31d0f010504150b0a0e09010e0f010f06120b131a0a0f0507021614030304050a090603050601060509030c04050c190914150d0906112116020703080c010b030a 69
    0x1e0a0a1908000c1841c03000c5080307000d4001d090000d1914181c0300c0e400c0910840b800001d000c005515007010441c09442821090030303040c07003030301c0b04428075440c1036106034a94007042c0710400002d0b03520010906100801e20020b4450410700000a0490203d001100701c0107100e0703010f10580181c1d0441242001c101594072a2b4100d03601c1080096491051081e9030304001103000138696909040c5002190a11500450349010504004200c0c82d46040050710040c00c8010b00c420400c0d6107809a110040c0307160b103c155032900c289000095894003c02c1200c1c1c62040c081c018100100c1001d083c040036210242c0300d007841d283c0030810481d103607548070551701404240ea501c5c030b12841d140c585446400c50384407416603c5280c07014443c1a82079112002c0351440c43d000f440204148400c2d003031610003041d1105480c4183c10300000e181e541e00307900c1260b604034150701400350710319901c441c071040351030380302030003040016a00200e81800820100400703800300712038100c008510303500300c2e1020a080001d006070886 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 817003974 1250 817002724 817002731
    0x105181f03090b01140d02040b0d08031303030f050103020609060307020a0606091e02030708040b13050d030605010f030c02060c25080309100203131101110106080c0a0509040b0106031d0f01 83
    0x1c02414003c20b0b0700404111071000c5441010400085803103207001c0e8000e1203650744401e81340c021b450b07580c1a214800d40201105c3e07142e252240720003240342c8009800b140041e00d4425a045105d1881c42002d058940151040d82401e10302c0303040c450b41e03900250011056204510004c0d0018840c3d004181c054000c0400101d024034207491404080420f155a27400058014010031084543c4036001039407054200310381d008251210030011062200b0000b0141c1349008000d1030f0142c15400d90054400c44e81c00b0780e2400d4000780c21200413402c5a440110038030068001002140d0300340c07800703400350804040712030001c500040d02da101c2c2866202c0b008021a25510003008204035518144403640c48003a600b24113528500d0080141d10f040b441e035400082240806035401d00302c0e0f074801e21504031050b443c400208516034640c181c0c656580394001c0410310403015400082101d080000c112401039500070113402840e400c00f0700640281c456540c59040c041500220380248540030480c1c00c003000901d80000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 817005224 1250 817003974 817003991
    0x20304081005040f080304150203041a01060c05061501091706160804050a02042d1d030c0613062a14030903030601030e010b150301150e0105181f03 65
    0xc0c00c0c0701803803220108181c603280030400454a4110680b01050b40210b219035284d80b90319060620840a0803d072102504c0803040108000c014081038181e40480f2000d51026a6a80012210000401e40080070780d003040d000b2504040e021034003001d22002c141418108152501d5406a0464222a9510040e801807081c040c03404481c1c02000074450702c0f4503002d41c0c036240c56222180e0b55044a00001d0199988a5403181c0f010903c07107030001081c038000d850100d04824840345c503014004100c003a000e0342c013042c500070070048030010440300b15040c400064049940d42d034460100d001d0001a054642c1501c5038080c2010004815120314441420b0302c1d10f03040144007060052041185054203912010208103022010700c0010076030354805401d00e00800d41c0d000019041c3e005d022542c0006402401400000e40700c00c5051000e107050382e000200078805231a044038104c990b0040045020b0100b2410030000d2000d442c898503030b410703003c7c0c090000c440182c603190030303070800c54500f40b16940002d5440594 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 817006474 1250 817005224 817005239
    0x15051207022e061401022e231f21170414040c0903020618090a06060e0307030b07081b0307050d0b0a0b04061116240c08040303050307031b020304 64
    0x20349004d44007100c00d1500260041001070750355003440744001c09105c104a03030410868074144400026040c26002400708a610f146001400040e01218220700d200e21000034001c8030b1020040742c1d04600d81464200100c3c5000e0544d4100b69004100d038815031041802c01010400903d5264180c480499495a4403881c04031105442450030310b0191040782480740300d0928a1b8400001c0f02600d4049406582e0386011310031004008031000c14594100b03426808020001b4510f0340007204031045c5840300394090743c40808154031642240001404da40d0074001061026118844455101240b01c0001000c2e4040c058082c0f250740049070503a00045000800005411003406041c06561068a08561807802c040d17402c13810340100c1c003682040111003d03040007072075400c0080c420404c41406882c078655848500d02c020400000c0c20791b05080403c1540c04030464400c20381084502e81291203141400e066940440f8175070b00181c03060b020962149141100c00c0f0361a100325040d8901c03034004544c0e03640340845 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 817007724 1250 817006474 817006481
    0x18130f05013207091809060c09090b0103020c06040b040201021203040c060e01032906070606150e0306070c080703050c06130201020111090913030908060a0203010e0115051207022e 79
    0xd031111550102d00030300a5040d04031070018140c0d1960404800c49643c0810703580018506d401014000905147d2402509a0045501000d441b80a0401e11508254400550507445014104c01180c1d004000003030128200300941600544144141e070303080305111402075030903013068a043d500302d4032a080422045810520310403502c4001c1c20705000d0000c0131080106601141d89400b10034009500d103000881d500c00b82140d568070b511603003c02a058541c0c0050461504002021010402410f01183c6520300000ca161003201d01e80e461000c048102d5590700c4c011341010728101d0a001040c0403240c0301c0c44050180500c02d1801a0081098012600009007134807070101500c41d42140c00c1113100e80c1601d524034400d43c0f04128090990036003d01d403408403040d80096010496602a0b04c003404507240c0280c004504840304000c20f041666203603100000950707034104110f4003203001005103c201c1040c52400c7c2e680204140140d0320303044d0900d0f01880c080c003590400c0240d150904920403807072030064403 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 817008974 1250 817007724 817007801
    0x20f04170105100608160e01020c030d05030105040c0306030c030312020f030406050702120306030d1b1a09010b01080c0d18080f07030315150518030a0c030303050618130f0501 77
    0x82d0104003406d04c031456900301034600c07031080104000100c00c0750b4241d00800c81883e41c1d0a001d000c4034071001007450700900070b070020b000d5507220303506204591641d90720070f001c2e503410307242c200d4210311001c0d18540d810758541c0310104201403040e0b0244550344101d81d4540c05148501d000d882c0100701c1c0d15003440003c3c2024566014016078280030b000340180e80c0c4001410709512000750401003201e130040d55004140383d181c01030041003190210b188449442014060034000d800080003440059404e60040d1082c01040714940300040e0140441c00e07030740350307141c01c41c009040c000c80d9040320348030302d644a08407250300c800c00d00ca030250300000d00d07401050b40c0351003039808611002c148554881d050500411964280311030141c10040d02041c0d9800a45100703c000c508100003d0443e040701c0b61031702e00980e40c00003d220a6010070302d03000001d001401c1c21010101085059010810b940da00c201d44003c40e0420030105076941441d03501048000381091181100603482681249082d080c800201c00113915501c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 817010224 1250 817008974 817008977
    0x20d060207330e1501030f03091d060103020d0e07061d030303040b0f040305163002070306020a090e0a020915040e06060711090a060303080901061206020f041701051006 74
    0x452440c0084a03040210b928800c2d600c490104003242c0f00c201180c9441118903542e070140a0050000081013840c94200516510075160548140d503107100a400212031906600c40e45011200002c80d1756200b0780c000c003000305603610000b8900f408944020310f07180c402e40080700821140020745550982c0d06150240d071740b070220f005510b10301e80b60b925101c2c00030700074003401390308001c40003c00d04050007202a03604010307c0c0c1040c2031501d002402d0845111202e0492042140c20010300b0140c450300a0b130128103240a190000c000c020b14583e1180003d500080e49070701003040701c680100719441d030b0130a89405120850320142c2c036000c8200400c00c018001c07440001410000b0041001894205841203501c0361b4202c3d44107464070a103043c500c9241061940c0f440c1e0250b01042041351215513a80840c05590007541d40c0b00123540c40b420061f00321141400703007640d450f0412024200144854008040100c269038505080c117a840321a151368440148241a80f65199400c001000d8481718400c8004c040c203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 817011474 1250 817010224 817010273
    0x110d1a0909030711151213030e0607121808030c0f0705030a02091315020c0607020d021b090a02160f061506050403081e031008010e031207080a09020d060207 69
    0x1c555581d800d05113030f441c0c8140900911041d048504103c00b096a5181c02e00e80e5540403170389004025041c4400004108401042c1a10601c1e051070402d101030f07440c003940c440d8040300c1e40000e510701526590318000c01d03104a8004040c0210308c5030024805003194034640340040803450a8408900d00f4415580c200301d020b680080c5102000d03a48600400d070300146000003128031b215030780c14034282d8041422243d04800380001a04d1740c5221000401c9849240550b0a942000d8030525040380c0741e60000544180e1240004070226440c0340c02522240c10042800d001031030080c001c80e003856030f00340d1600252103202058035100c0900945d4080c104400e00d408088024460902c01c3c040c00c94007480c0409070280d840400c880071403010307000d10001110310804405480c1e1070300c00300c011000e13056800303540e20a5003030468840c2e0040c0d00005035142104020084180caa85180e01112500310003010007200c07a07110401c0d1800350702c0f0000300f054414024000035a5695150400200c02c172000c40b00501e95402 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 817012724 1250 817011474 817011487
    0x5040207030228050106060e1806060904020d060e07090305060114010813030e03070b091003050906040311150702010c0e10210f02040b040305010605090702030d110d1a090903 77
    0x3400b00e0b460589041003d11110030303080c540e60f00030080c4243d120081c050b601c2c01c600400c00940011400c01c041c0400c5503403000a240410510748001c42c10b59403da000b4400340101a140c1c58160080c11124005610000d415070b80c0e141c00088815003528a0004940c082c8024410301000740980d078050580985802084070070480001c0c00c1741c100a05400c8007040d58104841098403404500500c048010200c5050301e45a048684c0242c1c0704120b560f10424080028100282c024011b00c0d21410044000c0e11031544c070394405941c0b448401030307031042d0740c0a10301160074176800c1d42240f107004d00040da0000038078204036400039001200500046100c0e00021840a528a60040c4143d0341600c10307480440c5c00e0a16104010b0207401029066100b8900120303021640f000180080e00031280220024410070340d4410a01440301010341d51240160410080302c0e24102d1103410074550f01080401442c544550440c1c1c0c84200d614055a07040c4e09100011218000d02c1d200030300682001d5214051841d064 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 817013974 1250 817012724 817012727
    0x209060f180907050316080c0c010f062d050f0612010305030904060608010e270a06090203150103082d0c0d0207061422050409080301030302010f02030f040f060b040c02160504020703 80
    0x1282c00041c108000780700c1c002405c0000081c05270b80d405410f0b00000c2c4060014526040007600396800b8100c0c40c1c0e030512600c20ba1f0359101c5591010080c50b111583c4c0031031405e00c0113000880d0b0350f010025400c40301c100240c01d41036807108003035402140600007643c1c440d4003000400041c4d5074242d20a504000b100401407110b09042c8074400d410800c0c03100101c0b2100c035140e40003200360002090b014002c0c010400100c00b407082035041000c1a9200302c0988213000006050f000b540d10b000e01025060341c40600034255503070401070700c020104028241b070009603c1c088842c0c0c45280d2006800607003681100280b0b21003280c0400c80c04c8040d000c1400c00c1c40301e1141e08504101107001d060942402d000c50407031000719000000b200c0e00040d00b00984140b00b003000e5803c02a00650080c0720450042d864543d08501e907141e5072084e24000d036941d0024840c1ca40b5103456640108216803026681c02e59030350b00300e4805548038401d1200b0304003150003504117004004540107000040741c0c05180202d00400c21940000d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 817015224 1250 817013974 817014001
    0x307030f090c0b2a030706051b090d080c0604150e010917070f0b0a020309060f011401120b1801082103010501030c02030408010e0c1e0904060209060f1809070503 71
    0x300c3d031201007282c0310b80600c0c3d03940c1200d11a50f440010280024000030750104030120060402c2c41c000c04c82403110391103c0928182d0108003000809446101340480740043c545842480d2545005007102410300305010352080c00d01c3d80582d000c0750801d034003800c0c951000e07185000322000ca046010080113a5900d40d1545030038092240141d604007900020b60408114004003c440050b4004001084a14221007035000940c000e60707a101c0740d8841c039030001d161212070b9500d09060b901c512070100c4501c10380342c2c01540e4444480404404482e11b80309540702648030036080d152161054243ea2000f540360119440c10622620705044200c40c0c4000200a0480303400c0c112070442c0c50070b00c2e00152590078418102d0a50046420000d034a5080c000c007201d1001c070020b90000304a40450b4602900d40c403138122074042040b81c80425402ca1440c0d400100421100d602a010b45800a00710f540340880c540d20340103045d449808403045801518450008500301018501c2c4e2000c03840c04d009280d070500c421000102c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 817016474 1250 817015224 817015229
    0x109020a0b03100e130c0f0b0a03050a1127040b0d08180607060b0a0e09060406110408070b030a0c0806030a1509080a0201140906011a0d02040312050307030f090c 71
    0x40ca500000492403101c890700c01e0b500185816103582030f031403c2442804040ca17030410f40035991482e40200114144100d540c1d00c504640400800901d44180040b0541c00f6000c001c05203d00749955000e802c80c900d048000611501060125108511900003210301d409a00400c00300e01032882d00c51510200e072101c07201d070310a0b10b40104050b520303800e030010361000f102400000150020030200742e120400079503411811a520341194007104098441d10074080b285002c44002c0146e42c424400324000c0350140e440720f01c58082030a070f02894240c440807020314244e80c81d8091020746c40b00000300000b0840e00c4c0b00e4008064124035150700a03003403003000030b40d903052480d501500a20440203104501d600c5984a002081e034030a001da616800310140180c000c1007420304000c0701c8400301e00091100b80700810014140c072685418810615403501e862101900030103c0415159802c20000c0040f95000d07403595002c041e1a66001e5407858010002000d0322205903903641402d00300040c0c0e000007412960920305 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 817017724 1250 817016474 817016489
    0x9080d0f1514031c090f0905040201050d0906060f15030506040605241c020909090c01020d0c030c08031008121603050d020712030501210c1707030c09060501110109020a 74
    0x10b0807000380000a06000c00d026a03c0160003000d00f481d003081e50040c40c6041164040c1788048102917807400041d0560fa4200c1d00240061010040c5110241e8180e12003410f13103000d0500010b400362611711540820a1507000385000c2884036882c522181d6240c020a98080d009503420b02106203000d02040303158080305600d206600d05540d2045001c1903220a4503a0219407503003c014001e00940d0020095003e00103440c0100100343c00a403120394001428884054103900030a04520b10b004125330035461010200c0401030882800030110341d0720cd020718002d5640c0c94010f40000d00e45610311386030548203055840420000d000c23040c00007095072a038004140d0503003444c6070782d0504a0042e800038802c00030020512500182d540720415810b03800b05050702e0400c0f100c0c4010151010446940e01c1038240028a0185511814403501c050300c07140e40c044a82140c1101c004c147c80e650340c0321285189410000d009a5220010480b56a01802a20b03451140c035008000305525600402c0d1101c040d8045e004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 817018974 1250 817017724 817017749
    0x2601170f0a020904121704060b0a120209010504020f04170c04050708040b04031b0f060609050c090915030109150e0d0302040b03060405060321070b0108031213080d09080d0f15 77
    0x200000d006d4565107503d540c001a44440d42c0c5020301d0321200a00d070104071580506509180414070030260040307a0881a0024a015000ea1030403080002035031202c000e4030100d401c107002c0092648207042020511801703400150441e0380d021010b0008484004001c0c008010143d0180310125540303405440d0801d030580307000003036404950348600c1c5045281e000200b181c85880c40250034441268418000d03915507010600c072644941d070254030070b4050396982d80e0f40059401d010558500f6040e00341d469522020f0000b107010b09450b240e01040e06007003440307000caa507101d8503201419001400115400344584c141103007040d0a0103e40c100e40c0c04005c00c032500466a640c007040e00d5035030412802003855410340407150031450f689500d06040d0050383c0121240100813001107403660010059070a160340d203c3d5092460f98910341000301040b0800d2090380e40040030403101d806085140600ea40302030082c094241d4441c004e44880080b2881c68008248591030184058100100018103030101d810350850719 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 817020224 1250 817018974 817019003
    0x8011d010509070608150d0b04080703030b04050c090105090414090304080d1d01081312090f0510023a0908060f0402010906181e0f120807032601170f0a020904 70
    0x182d040c100d460009001c9211b180b04009c20814010010803c0ba440303540c007407003500504003d100a850003a1070000c0642e401340401600c552080001d481905030081000c45c8140261118122541003036030000881c2c1c0000170207004408041000003024560b52408a1000d003c1045450041044518803410041031502103905109594031030000c01c8e1300405158912000005c019000c16180c0c410880721102e550000191440c0c0400d07074907030206482d00600075144502c0c056180b1980700800e001c84241140200804002c03a007030601e029042a034507000e804608007164a40351000c001c1076462007440000c1080010b0b60b1200e20a0212000b500f0305020003c00c1940000c9000d00036040000040c0c6ca000084910403e40c00c5100100c2da21050903082285c0c8031100384a081c5654203000d860078504003c082c1c0000e204916448440c1c0c41c1404440b001b8640503a031480c9a0310a0b4405c0700c0d20000c111203080c0e104002c0c0040c000c20907411000b4841e0001c0b81d80421300e98040100086c1c84c150030303030581c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 817021474 1250 817020224 817020229
    0x25140606150309030702032b1112090607120f03050f040f060f090b0a060e090723040b0d0506040605061905102d021c0c110102010608011d01050907060815 68
    0x185c0d91802c1e802002e0b02c81d1144801d1072816443c840204a003c400000369900c1c40c0d65008203a10b905013107021014001c0c0c280000301401c2d01d5801080082e070081420014140405c1ea5560303250415022542c4448038040e4406000b015540c006c0c14104c00350010b18203100010b40c40c1c06100d0080340e4040d001088008003085081d000700700a00300500320b02d00728001c0000c550003a51001040d00e400c40303003810094840c6004556688001c1c0543d000d80e4402080c030b4180780389614940c80842030005c0c00400c1d42d03e00d0501007107816410701c0c4201e94070390006040c0002c000d0540503059000d4820741d1402440e007500940720a60003003601c01c0c503004001e030300680601103124598440c0421605040c005c0800412001404100ca42d540c000380140203035000d55941001004140e8030b5510721380d42c0c2500d2941c103900c0d1800100031802c00e0702d040d50b603a05000141c030310003070003901601d0001108020b440035500c0e02080c00d44000800e030345180e40000380184007054100c0003850304041002107030f038030b0000490013 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 817022724 1250 817021474 817021477
    0xb090f01120609060305010b100c0c21020d12020d02010b0f010c1109040b1501030b010c020603060a031b1403010b0904031103040b0d09050d02011a04112514060615030903 75
    0x3203c1e2141c0d08007400442845415000170b036002406a4005000c16180e100403100c1c0e4280d000d00130134054802404005c0c41040307100c1841d01d141190019083c600313882e4000350562007480e0048a600302d015000e528050b4062043c080b000005000a000c144982d8001a5540501c15000c5052101c0d0b4042030f0103210700c0300c02918064401819030005401c11341448440e0950895044100c10301e000506040b0394400e0003184814030041e103403507401d803e01d80c0c01c20000ea00010b000d80d4003c00320b243c1c0040403c00561070a680c00300b078044004441801c00e0f00c40c1d00d541c0d07030a0034190700a07030400030421019111f880c0078640c055007610f80030b52550134010401d400d52089038010f207413105010812080820090340014513803882042115903895124000340c1c241c075585600280d14880d00590342e00136040070f402c034102c2684540c14251804200280c22551800c2c4074080f0a6018a510314135000c00040b681d903541c082e110078005100030710f0000000f8221038001c2c0070204401302d000c00401c1c5031100800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 817023974 1250 817022724 817022729
    0x3040623460b060f1c0204080307140a12081f030c0905041e1a060319030f0302120f090d02062a040506180a0f0308220503070801150b090f011206 64
    0x144401e540d091315044e9030034103410440b900446491180ca14041c848014070841341120900400b95007801c1032602c841c2c1f451000302e1400c0f8240d00803100708400154508056052000c49d644444081c0d0a007042620108900040c0441c1c1c0300341c283c4010b00100704103001410480b0303980600480c42c0c0e55140f41003040e000082c038481d4a80c4203040c01500411415441109540e410b400311000c00d5980c079010517a5136403800043c401101700d54044000840d20070880707440c41881c182030140c41c0261174000c51520b0301003141d441244840345000d01040200600202c0c130030030041e00c000c1c5290308000c00010035003904a4000c507665491030b406046105e031240d0a82e0002c0c61b0040c00305440342c90040600c06142011b103613882c89405882c0c00800c1e40340b0364195440a41c0e4102c49543d00b000d00b0080c907400b209041c040d04079585001e183c000549a9001c0000c200600006000420b02c40c80e43c045040160f10036070010b5180c0801400359001c1921106c981c070801c81800d29001c00c8040d4501220700007040a038 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 817025224 1250 817023974 817023979
    0x11030406050714030a1e060b0304020f061902030c0c010302190c02220b0a050418080d0e0634140a03110406050c0f0d090b03040623460b 60
    0x4410080301141a51220646da12001801c2000901216004c0b08440181c018a402071800744085405801d00907400240603401900341443e10401240e00c00c0c40c4c03004040800010313800080d001036411810702c8643d9040c03000307080644c1407103402e982d203902081700040e03148100100c0038046401c0d03540345d0226803900c3c1e07854000c1900c00c01d141015400504000d03200307540205c004540c0081c1c2400e191060503020521444001034200d2242d07610030b81584250441c002154590a04401c0084107201460107104009140145008811b400e004481100364180b514401019105070100740c004214100c610440341c80f46549200c420303000ea00815244302440c3c0032683c08a00032440c030750014010400c00e50b2200c1110b880400300d40a503503403040d50404c0350001a40355071040000c04814005190854030891000c201c152010f80d801a640d10381008095851050340c09004100303a280c0082c901803560300b9824120740000c4400707200c0c51850205000c030381c1104004008110400b545c0440760700f4500 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 817026474 1250 817025224 817025227
    0x70302030708031015021b060c15070807081b090603070512010b030106021e1015090513020901090c0806011116030c260c01030c05090918060a11030406050714 70
    0x2407028039003901901c0c0111221141e11400288009000155494400d40b50050744035403081090223005c100e0708020081603d510880ba61144000050404544542600d54801c040751809044c0142103510141064410750038010405c400d14490700c0884004040c11b031412590b0ba03c44000485542c40740e03108a034440e10b007407000403400118a0b4000c60481b140c59003260004503118070f4840311040003285105465100034404109002e454004030101000054003c0c1c0095440101c403050360402c580309054031124130703200400c6252800a15024081c1d03058100410f18114138041d01d1140c0280540c0d05200384c1d040c400010003002c015040ca4900d290000c0c0030499079918001e624100c40380900402a4614002e2410041f91005c440c15011103202c01080441908401540200744040f411000c01c0810007500155840b2070800c1402047d0900308100c11000100d445400e2146c0501b50540060400c9010007188174200e0580741c00c6900200b0004c0d00341c03036000003511542e16001c04911403840 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 817027724 1250 817026474 817026481
    0x7060c0905011103090d11030102071205030106140301140d05030c101a011701060c05030906030c12060609281d07090602120307030b010903080f04050315040507050607030203070803 80
    0xc0c0954000c0844100b80c032a55000d00c2e08040301da40324051541155001014091000040307002099206007000026000505d04416511450710030b80b540d1500c400480c2c4000010030070b070f07513100e0061030701b42e03c0303a90141e030455050500f45504141c0350400a0310490385c40c91548207000040c002ca0740c100d60b11404403031207000c5070b00902000c0e0016500100503101c3d6105020090750103000210329007031030a0003090590b801c0520648000e84409410740741413200307200401076502d95130002d5010700b03103000c034881d181d034201076403440460802010380d40501801d03c8000b003030f601c4034150341c5880c0c04050000300b40e00103908050b446400c4164000c0a0000300c6801c2c5011075041d18050501507101c9589084015413562001d90b540c5c619a0000ca004200800c0001c1c0310038480d5000c0b082080f81407412007119562515010920b41140d1504001500006001c12462800700070546e200002c5c50f586042c98540307902c449440c1c00e1948122030068100160480401d4800d008031002250f101c65603d4072801c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 817028974 1250 817027724 817027727
    0xc090702070e0603060403200327040c03200a030b0604031a0a020c10020a0c051510051207030318031506091103091b0109121506050105070f02090c07060c 68
    0x801600c01d801d00b80101d1400324283e4200402d50a01c210b415440f8868210030b150b1070b095000b41040d031100001d000612001907120407121080326030312903c000d484440d803003c400300310840d2031070b440c0102414503001d10500d02c0c3d29428044818032841c00d82d4183c586403003000944c0038042c0b03641ca1a62188000401108006200010000e902d0160b00018070540e68040820224810845280c3d45940500e018411511254000f00340900c030034504464212816503c007880d2400101600089905000420010a040b503076000020202114901003006a5000464036900319000203010084060407103881c14900809010003135500081402001c1a0361a40c031005207002c2c000c243c1e40c20708040c600401d0070801402e49028032a5000a05904001541c210040c0c1f03c05002e200d060254110300043c140782c11004040e601030043d0200d042d1910903040810850341244c21443c18840c00b840900c000c140e10070018a89107505407a4003507552a0715540018038019944020803603404c00d40c44e40340d880e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 817030224 1250 817028974 817028983
    0x180207051009051603200d060c030b01110a0b042d03020a050607030204211103010c03050117070e1603022a011109031209121915050f180c090702 64
    0x21400f071420b407074070310781d20701d003200e16044903803002801e503088031185003583c2100c54402c0740c40038100912080c040c000d581c0d1110250ba00462100f40031a07541c48100c000c55800850038070a4011102c0a000c04c8140341d40d80404070310340642b0162480f50b00c21341d00d01c1d2610710a0030340c0382c03940a405d00042c1103c4861034000e644101c08481140c16020300e50209240a000c0d0003620b050f2120080200c00c070310320f454200b69210303800c0c80042d900404011a903d8541c0c400788208051292155408169581001803888080382240341e0034080d40c2c0a40c80c20050502c0164885400101e06516403c000c1542030013140a4092014803882c00914441e00b406804401b02c1642d00003a1004000c0c046400b2440b01c405980c064601c1280c0c041c0c11103004040720002c1803004141101004050b050341c2510208900e24000400f19401c0e943c100005040c01441140c004101034006001002d01c494a0600350126034504040c2030141d01280e01207641c0c8100c00284807150481102a01d000300c14a0328500c001d60300c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 817031474 1250 817030224 817030241
    0x809041103011d0106080403210203010b07021c0201050703180503030a03060305010518070b0a05040914010602120a050a210f0b10021902011412090703020f010201090c1802070510 79
    0x1c03211001d141d050f5640701c6040b0103040390080d40b111003c81c3c0c0d907038505072a1900034410b181200000000e4820201e5000d1001e103002e0521220348507200c0415205100050106503059142d2038446242940142ea2220072180e060740e241c03800c10f5900300140c200b40b0300305042c2c2e0805075140c000890030682e0750341d05a102c0c6080b40e001f50000c0c0895101c4001650b9503901c10340410030207410046080c020503000078014220341c50350303203020b925240e51a401032003210f104440f4110401019401000f507540e041003403607068071081150354500401c2900240440c420300b607008060011040f00f07059801c0280143d842e600115100c01c0c0000c125400c110130042030005079140c07113a080d5290881c8190301c0002d412243d61901d1110004000e003540040d1241c88401c0038404410604200c640396030a10317140344900a107000c0c03008041e2207045104101d501c5903140d840d0381c11680351020020201c1d281000640840e01e8404484c9031150601c902000a03215600707001e00548101c0103040140569580f00070074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 817032724 1250 817031474 817031489
    0xa0207061a01020a030f02161701050907060e15040e0f0417071a0a09080a1d0f0306240d031d01080405060a02030603070e2701060f030609080904110301 67
    0x300c00514040c1c2240e500000a07240c0141c0c042018880040e0241d0b80110f41989180122a0107906c3e58009200c0880c0d46e8100884074010440a552882e509006480e00700d415580940545402d010005241903047c4d01d0030303071003a00241c3c0d44650807101041181c01074254210307a142c1c030b4900a1603990702d1400603503044681c40790381180c0540455604043d21700302e40c4d10030400102d5116140200c04c19100181109800355642d1010b00700058041c2c00501c0079038801e4545d03078a0207050300030b11890000500c01c0e1038000d20701c26181038200d035000708065070301c56030000941d01c900c600c62003a9050781c10318040725504844040c1c10b40e414541c00200302c0300014009961402e01c950104011a26100d080c0c8009000e941321780003003080c24580d60051a800f2b400074080f10b000f25a82c12004400020a5840e408240c0003410141c04c026401c404900380d81d00d655000340200b0b8079014158180814511010708010740e50f034241020800c4c400215500c135040204180250480004bc541403688207104114 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 817033974 1250 817032724 817032731
    0x90906050915090c0d05010e06130b150105040608040f06020f09150a0906081f1d0702011e0908120708070f020703030219050102070c0f05040606090b1608120a020706 73
    0x4042c015107000d921444803c00a4a00303c5031820a00c10320b4460444c00319025503c4107055224000300304000f5100701001c141440100c0018104000c00c640007a02e0410003145146040c0c400f0b9070440122400c03581c0900d4a124107540300c1c1021140b1101c84840103086500005404125040040103040c4d41d2208a07a4600790610000d20941c00344074030701d0040f010600030082000b03854010f4003550750011030b94210100312a101d00c0c80c0d60744540a0340040c1690078070035006c0d00314400192941e07076014486000800c15100364640313400c0c01640303544903480819140e200001c100304149040d66400034a40c100c14045090034130b0081e00815040310100005a000b0a80e2f1020910005010f8100c030b0301034000d442c0581001d80084800350b10a5000d4400e507408102c110000ba4a01c26100020060b0091103d00d15041004110951746581e10404c00c1020540090040c81801c3d811180d085490140b600d4801a05240030500c2c1c0c09220030310040350040c60208983c0c005030350020016144101c2040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 817035224 1250 817033974 817033993
    0x20327120a350a030c08060603040c03110f15121b0d02030a020906130f0b0403080d02070c030507030b1f030b13111005271e0a0909060509 61
    0x11641c81ca58168040c0403081d051140c100c204982000b41103001d921003010b000950300c2c210010031a94001e018090010342d4030503001c40310726484200d49400013001c030384442c40c41c20b00f500c40c03000c81c400c40d00014cc40c0c0808001c060304103a0303c3c440f05141e48480580001402d009441c510328054201d148401709490240002444c0e17121400702030318080701d80f02c611905041c3d0300d0b541940207400060002481c0783d42002240880c2d6215030180a5200c00517041511180c100410080f000e10b45500c04207400006201c02c0c00002d0a040c1680c8030300580400040e00d4041c60305104c10607458903803014120780100075000c420b00170b807100210b11401d4010350444204038100390800f03d1900f41d04c0007901c40000c00c808100308603460000040300a011310340f880000031040000407801208000c000000c140006440710b06010494a070742c1900c09500b01100340d0018801c081400034180c079218403030301041e004a000065a500314040082e1a40f5a000c0044800c1d514080004060039280c4200c10320425140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 817036474 1250 817035224 817035259
    0x90f070e040614010303020307030503060d060501240807020307020d110a2d0608131110030e0c09040b010302060304030909110c011d030d110702030a03020c100e010c0b0403020327 79
    0xf40d60403030f0782c168000c40c64207445032000c6a40ba0006080c070f035804003d9000b0f903400308001e4001c6a001e00419444a60445c0c03e805608181a04d581078420602611790100141a070700402034442590301940d40c091041d80b82e24151040054103c0140d621071101140410707004501c54541261030040d1400f042c0c100c0b1321301c0d00d0301036182203442150009580708000540300005038140d241c485120300d140f0f4444041000c0025410564202c170340d0006552410011700f84c0c00b04000d901035520080d1454cc0050034562149254440b05000190003144008041010580b28110400040145540070000e0103440d04404001d548043d600c10401d608186408001c4801c6150313000e4806d01810065280c048102c4d0380c000a030046e04022092203505000100c09a20284000d210f40c0d4800c0d4090900b680002c800c004020100c06c070041d0401104100106559800150b88019580c10070354031049580c9038034003203255104003003412403c4410104c030364030403061403210410042c008940040700c103240c4030103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 817037724 1250 817036474 817036511
    0x2612040c0503070815070f03090611090a060314010902030702120705061009053606090102090418050a08030a0603121101050106021911120a0804320405090f070e0406 73
    0x400f40700c14024200440e00c41d500842e451000c4007c14280407418020a89515003101c50004e0f036103240000c0040d4242091500354801005400103080c2008866910a041c601c11241409040100c6500202142c41d4a00800840d80c1048491190b13035034807207003880c0030b0740c41e080c0903140d42d004c0c124440800f02e0f9920300d03402040d21440c0d661546d580d0110891090040d40000303980c1e071070303a80c1c5d01d40b06e020120748005002c5141704140300400942c1d2a00407a061108442c113880b844903000180d00d8240c0c000a81c04100d000d01a9004220306031030fa141c0030060f00049c90a5440241a4028000c90841ea150020b0f0400c3c1500f00c80300003002140c1c0d80da030342643c403102001852809101564030700b100050380401c27102060b160242454081e00b0200b920189002c150000a03103c05502280400085544040c607032400403504440000040c0e01501c0e5000003800b03401c21500c119203400020360110001c1011020001782e100442d0701556990401c040949030a440940b41c05080c03109501c0313064512507 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 817038974 1250 817037724 817037743
    0x307121b0e240a120b090c01030e0304090218040e0a050d230d020705030c0703110618130b03100e0106050d0b0c031005040f021c06032612040c05030708 67
    0x54065071082d002c420501809102404240d445031880002048251001a00d20030451081e01c8010190a01d0f4022601e043c010741741c201c0c1054140780310a0034442c008015036007121403181c40981c480d803490f8610695690340050351504103140045054400000155036600c840c02503081d00c1c405a0000000c5640d480c0100d52908140d0800c41580c10640e854001840100905240181041440e507107140c1180d000384001302c1d45520121092003440b0340c2c015015a05101281c0451038141004184c8a0750b403400c8103014070600040218520480464001920160b0002c041da09004903a9a01900800700108080d44643c80c001000c19103092524613045d689070800d07048000c5640720117401c00756900080c104c0c068900300d0440000d103070300c0d10b01600d20950b140c00000740c1c42e0200780510801d040c0c1c00303a403608071181c1040000c10105070300c800d8a0f40130380228050411040c14900410401c1c0c410901094181e04e8030000700b00038020200e000700151101141524442d99541d031010b0760300e00000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 817040224 1250 817038974 817038991
    0x181b03050616120c080421021b220c0e060f0706020a0903050d0521061e030307081209010c08090c0603070905030a0317090706050403060b0307121b0e 66
    0x30380c04990085004100600c40c14143c0c603000481c3c501c000ca05405995080d003500012034500c1d0207100070030050f60300e40c41e940a0703c0c0102512400e559200290b135450403850148440070400c0c408071481d2900b20308c01021522401c170b0040c141e82c000c021600100710318040c0f00d001a14200f40b164041c54080b08491455004034002d5061005a8450314025407040300d23468240045904000b00069050080405021207034841070740300d58110f001400554034040b501e03000040c031031040064555a107550003014140000700d101049681c0d202092540c45070310000381110401040b42c0c0c01100002d06068130801580009011120292400791740b2400240c0b80840d071078020041d00c00d11070a0500c0a15446041454408692a84c4001103824244400001d400094400104451014200c0700c600e422070704400040c0714003803030070b41c00400d58011404014080b94860400d00e4159800f000b2510150100c0384640c9401e080c14030b04840c1c5200078170004040c114074540e0010310012104299482807459 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 817041474 1250 817040224 817040233
    0x106030c020d0221071506031502191101110d1b020106051005070503120702060406150b0901051b160905010b0301030804170f0f010c030b0f0d081b01181b0305 70
    0x12a8020850728600c00e0f62201c803071014445c04002c580880703180340d0941d0291400281c2c1c2421400c1c40f540d54420300700b2030249280100701205048445158110b6200c020f4a4145603100403024030301e000d0240030707003074401001000c910704104e4031584d80494403203004070a14138020481030310140d0030303906144a040e91011541c440c00302e40c03a016070020545544101c1c10b03a4580b05400340361103a85441618200e0051f4045401c00040100600c00c5205141c0301c2030307003401814501000d0500720710500c45514108100071503080b014000821901c040d01c0116030980b61164204061040c0d42c0c0720300c0c42503049050400e4000103034190440d00320303410f0701d40140c0c941c0d14103410440790906280400480310440e00c90b03440020317080384042c0141080048883c002048900c04440001d040d1408070384050700c110800c0b010542265203150501129030350045085840c0c0002d0601d0060400880c5030000d0030f03500f840c0c03580380358800078085031400b1807180c14070417800326051113034503954452400014116440b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 817042724 1250 817041474 817041493
    0x100503073003050c06073b0d0507090612030915020d0c050c0a320913020111060429070f05030a020904020705030705150702030304030f0e0306040b0106030c020d02 72
    0x29280078007185980241011894103146500302480c200702140ea01001034800344941141400c2002034420b0200007c000d5601c40044940e903a60b15101070b440c0390b1241c1c402d8101001000024415030b07009201d58882040000d030790710454641220003450840000d07282140c04136683d05000c408080c400541c1e80244408075800405591f40a0300359000e5a00d0311407443c600000d683d6101840d005881c0301c414002d00d502ea41090042d050700d4801c90200302092182084001c2d40380d4a801540c80005020120360644d618001614010805040b072110341c001c2c1d80402080c0305821218800c07201a408110209440c10a051100554242c4211000900c280c80484540348150040e40d040381c44054011f10300700982c4000740032603000a004640540002c2105014032000348900450040c1c000c444140ae440c04100080d00c03440000c00c010700f4400304403050b912151251811503034180d00501114500d04050400302e00c205c3c824440d0b5000241044044a01e540c408607050b02d50960940040070b803c43c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 817043974 1250 817042724 817042799
    0x2150406060306020a0c060606050405030303061504080a0b040c0f0b0910050409150e010603090c090c0201020d0513200d0308190c05030702010b0603010e0c090102120310050307 78
    0x60016144103889100c0440030030841d100901c101000b540b2a172080b0305c0c0130b1511138140d900d60f0388081d007844801d0100b0000c9490220441c1d9029404652aa11402c421b00c43d940c51800340d500203119034031901e0702403020403006107503031402140500a802070704c030751b00e80c20000440194050000c402c0c0007448811b555051410003c6091811400c000303081a490340c00c0c01003100d100c0d0b2207040b15091a0401003004e50401101c40d80900707110301d0180f060b401035032641c0d414680a07200d04402d181e030750030318050344038801e5050343d001d42d41640050216091032905821011a203001c1030780d80c00d04190505100012000e1000c04202d0040c040501040c400e8609842c041e0000b0710800b41000b0030342400c20440d5103072181038072401752511010303124100804001c0c21582440c0c44180508070400c014401000c1c608980c990103101180c100d9540d08030440103d00b40502d24000c5001c100002c42442024100c00c42207605a0b00d041e4101e56980380e0321420307841c060000796240d00c10102015034000c01403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 817045224 1250 817043974 817044013
    0x41101050304050f0f07051905060f070f0f06050103060b0d122a1a092a0607020409200603040206070b1b34110f0f120a0210020d02 58
    0x2800f48003503c0780c44208040310ba0a02c071002c1410b2070140c0146030241300c3c1d89001d0425151000b91152582480c9040c0301c04580c191050181d0200c030104040740080070001034850200813079601049800329600b0610304500034003000c0c0400c49020382002c605481c0e9042111411094079042015280f004100020a0f0392000074003011f0146080c84440350103101c091724000b20310551180283c03803281d0000501888080c40c020308030300d0150308410303510912040d1510400da031844203400341d005410761038030025145210790480250090300b024000380c00c1c0311a0058544600b4083c440040b901240c42c2d0811129110482c0c009520600174868000410038070b408241e400613074540b6055038515141c440c510310303070010058500c444c042000f6030341d06106a0760fa01400a1442004103d8190056175031220b000ca03402c021a008403e000d0508229a070342d054948001d11000e01101c08040c2c00d281c5554440040c00800e0340119514240209081d01c0055407111808069010302044d0711045000d0091 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 817046474 1250 817045224 817045231
    0x10b031e0a051b091006050f030c12150103320402180c09030d050c030d150504020403060906110c1f0f0c020604020f1504061101110f040f0503060411010503 69
    0x15114951600000840822074100e0040c1d03c141d030300d920b4030011002c00c00800402400c0302860200c0400801c005a0014107980080e003900907081d40300c0e175410500720740034000c01740310300c0e80c400d02172040c000c80d412078100840040000f1307a001e001c200c0c00e81075601c03690b80c0134141e040c0c00e07034105061202c11001814010340d00306100801c60041084844d140308141d0a003508c2d0800b40c03981c0000c4104003480c2c2000305204210003800d00ca4142103a4290182c0c6a00030520344102494032808801008019026030b0000342c40000c00c1107491307503105c5c140840103020300b49040320381d64030301840880c07900d40c030380142c0b03902d5007602d0010428042c11040701c04030b206401401c01900e58032481344600b0301d1000d01031440818260390007069180f8050040204d404401c80c4014010100c00c1510b48003002e10b1401c4805542040c00e28288039191000228010050950b4a900144011603007207240e0008100800c01c03221981400d04c00035440d0300030981c4901043d04c3c0201100c805114906495008d800510760 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 817047724 1250 817046474 817046533
    0x2f0c01060806010611010b04090b1303090302150a0e09090c0114090d141506060a0c0f0f05060601080a0605030703060f0e010e0607020d02030c0c0913240608010b03 72
    0xe949944510140c070340002a00b0000c080344c40120482940300e000d00c10000030140448085c000c03100b00d0f17190b8190201c0058081e079191000d02d0800d80506005e001074400031a8054040e9054004410640d00304c0d81020340d000c40014109102660030345000a00280a60040d902030b10364241400c00640b410741030f0340000000d8260038001e01602c0e5555500b0100c10700c2c014283ca04858801d160120704009003030141d02207101143e410310a141d1070300003c2d213450a5490400340040041400c00702025152000f0044c000920307141c14004001000c00c03100d008110a07298440f198545903106c07001d0360128003c3e5500341d4040c91040020844c030350842041b07401c503600d00142540c10103100600b0344282e1040710f402c0f40d06c88000e0110295040050402c1c8203c2c51024500385040c0d10822522004400c400a2243c00c070040030560358003100a01e40c054550000c3c1e240c1e1740f0007501c40348cc0c01403048211802180ca141000004507090180030b10b111403a0020040c203510200d1050350741705080510440c0a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 817048974 1250 817047724 817047731
    0x203072d18180605010f050a090510210b03060f01180f060512070e130807021003021605010e0705090403050306040c0302130b04030219050d2d03122f0c01 68
    0x154601000c100daa004a0b085080401c0d800e05210001d0b003241c80d94040102040350400150126550200030602910802c440e80100e112001508981206841d000d0003106005401d243c01c254070154001c861046080d01694a15601c80341d1012222000f44100c442c02d068100441c42300301d195a10500c020309094200207200d0b03844602140c038880300c10f6550911070340501d100303100301e04800302c485610081411a8a5600c0126a2032a14074058990000d00038005005944480d034020b4042d25401c00302204d0104035042d640c00d0040c060b00c0451203e41ca140100e000202e600d0030118611403250707425032550f43c40c0d80c48920901004001d80c0c1410420035600f0301c15000c140c520900c50300001d29036604566140d5046004100b641c500440c0d84000701302c10042e0030440b6889401a07100030741d07000184190180e076441550440880c26a126410280510300d100e810107400c030b051301003a840103610401040100b90405120400e10b03001040704894522404d03180301d40300c50018800c4020355000030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 817050224 1250 817048974 817048979
    0x902180604180303020c010b031b01080a060b0c0a0317240d050304080f0f0307020f10030f0908042102300d030204320f030c1002010203072d18 63
    0x1069404502d9000c80000f500001e4075006620700340208560240100c2c00341070b001e5074220361b00a03140024050b03681486000b0f00080c080c0c2c40c241d400400209408442c2d42d9940c9400f20030181c036503814402c01c90101f00c101108508584150185034420000602d42001602d8a18441e0540404400710250710443c00510b01c80041c00a001402c01011a403000b84511445592418141108034130480c100758070900003003025aa6000c0c02c00c1c500c5009842000e681d21a40e03d0840142c40c0c6131030030254071030802c1c070001c0c00c1000b00c0d0000e108842d003051091455155581e03003503c0e01c29030700d1000703540140102140d11415490000060005080c600400c150046007140c06040c003100d104ad0f4000700c1d9011a04001071803811610241074144416032415000040c14194503a40764a81030b980650a80310394004192810000800301d000700402d40358007400c24500082c040e5101301d50000000742c1401c040790712a95503807000b411005090882e59480c1d18030a4085036141c1401120040b82080d40303000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 817051474 1250 817050224 817050251
    0x2060c010b1201020405040c0e0306011e1a1305010810140f030604050c0a1a03012306031609080a030c060c03140c040e0c03090309150408100e0f010902180604 70
    0x7240242d607040d4009601c45160004000c2140c000c7d41c0e11a0501442e14101540703a80c0c082141030669401c404800306040c403801d2a0070420160b604402612010341607011ba207041d814006d00007902005580444240d11600111060001a25404007810041806010f0465000c07003003000000e004e00703d0001c81c110113001078038000e030a031130641c0c054205d85c058480c0c5080c55440300000c1c0c80800c010300742030950600c1c0a091072105118480d11080e460035049442d5a820420f00d444020090810f600d07406c004098900391034402062002060f005007000035840800b20740891020f4040d2030f144205422500c5c0d01002c3c007604e10144081503030783c02502c0c0449102540203400b4820000c0000c1d2983c1c140340c03806410940c0034080c001c00d400f081c4100158200000103e4000050070360308210b0303061401c081019a401245c000c0c0300d950007171280c041c100700c2c420360048802c1030504044607010824001c00508948800750042c0d000050b80032140c40c6900040c0c601900030601a0002890f410003424 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 817052724 1250 817051474 817051489
    0xb120912040b070b060d031706190e06090a0b06041e05060a0305150102070b160c080d091d060a1403100513030306050f0306041e08121611032212051f06030c0302060c010b 75
    0x282f038580c3c009003c3c841d00d41003101d080341e801055444100003074100c00000035018040d92103100070220203907130700301da0251480d1103420081c0750180c0704944404c0011000390240004503059035518400208288003584005441130494203032541c0d003840c042504000103084000390400b900e0120070000005141075040201c501000c4656941205081c20f0620700c85102e0701101d10000200840d6050101c181d44202c0400d045035120ba0400300c20130144400b1030f003405c05550300d040c0d440f46014208281c0160015016100740d2091303908001c0f058941041056819210054603019030207500002d0018000d5500a00c000c0811038109210000035550384c03030168031074007149001c0c41d003400a000810612803000c0a00200500b414004862000720079940c1c0d000300300c4040043c2e14132582085580b0124032200d800b070b1a1091842c0700c040c005051083c0c2d80c9480894003072401301ca419403c0c070350500b50710900c400da95003c00a090b019146400f0071003660842c6000c002c503035583c3c003281011540c0e1000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 817053974 1250 817052724 817052729
    0x90503030f040f0b04150c02040902130606020705090103050601050d051903030207030306080f250e010e0609090f060402010e0a0e0708040b070201060b120912040b070b060d03170619 80
    0xc1070700da44a081003007010314001c42e0360201801001c103000901074070000700e03003012003600b2a1406607a441094000100a45012080650010300d00c2d004842e200c0300540003c0d05550054080320406a50354040c0300d40c8110900c4054600c0d00010300610081c90321690350380c280c038014001c030748a0514608180087c00c00e1260308802007540010464101601401040d0041a6510241600e0040c1c0303000340791142c55850b030074044c140141120b019040e62044c14072001d0050303002802055a110380c4e034154560300c191750345442400144002180c040001032404c04200030000030342020b8440d580190340d00d0203120110740e8010310009000c118050740020b02481841e05980e4420a41020300b032101c0c9d0301201803e103004690500209103d800c06004c2142e000b1b4180280781080d0395104c04586080001b1200da2440840b00010005044552500035000141c000c40c28004192100410004600328925008010440054183c1c003411558098682d000034041c002540840b500e15440002090343d4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 817055224 1250 817053974 817053997
    0xc0203100218121c140403060617031306050a030f1802040b090709050607110a1e0603051b1b01020c070f050301060e131511091e13020a09050303 64
    0x7050340241c02c84100e501c01866601600d90203081a040580251a9540140d54107070344084144101c04581c40b403082a10030400c03034070960391101d03140c1ca40000500001d206403100351684000d104c0100c00c0200485500740904031000c5909850f0030400e0300e40d6040081c504082c59039425048150701c000340103400d02d0007102d00340c00c1000480c0d40304010450b42a00a5213008000385010401d1460b000608202920000ca03012038650100c1d291100014000c1407101d500a800c40f4400600000d10408440746465581c1c98810b00326280d6104500311003088039485240c20120982c1e01c04580c1c41001452880420003000b68041c07414003a503403d9910203644c002c956401003004000194030444070b40c002e03210850003488041d1620031806c0c48820050480312110b00700e80003c60821625036003202198600c401d0501003064a03000d8081940c20070120300d4042c1c40c1000ac029413031041d250706c03070b20680d40050a0840c0c82c5440143e28009400061080c1c4c2030004110b004a5551b40c00c01c050070404c45403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 817056474 1250 817055224 817055227
    0x150b0d031106090f060601030b03011806020a1704030e220912030f150915030b0a051b160b091908031006050705030f092101060f060c020319030c02031002 68
    0x541d5080e2074004000e1031580750ba00003071590a428040030030010303000f40092034080713a9081844000390041009400f02420440760361681010490030b0340290120810b80e8650038442281a4061400d90340101d41c001c0000300d0b081c000a200307182504204683d01041c1c0ca54085d01610050106c048804d030b86825200171f00c0501c1050209a8140034044001d072803054244880d0300b4003840c01911103114040d62200a840f440c5041e006046400300071300441e00f0096060550070182d000c80300070107060350034001c507640c440c03140740020426000300c401e8a10a00c40c6500b500080d80c55a2030015005000d41016004007580203035040078605120014501814a00b992424200308450a1414981c03220382844000d001e5070b0085500803060364101c8004001861340d4040c2400012000b0707641c4425103808880302d010485802c0415403002c410742e4013100481113840d8031900c050b5000c10805030000e5040c1d0144050441012401180160140c4030b820070b00180d002c40c1e40042c1c203000000c407610b410944e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 817057724 1250 817056474 817056497
    0x81e09060310031b0f1206020f040e0121050d0804050304050d03030b040606080402090a0c030b10033c0908040506031603060618210c2916150b0d03 65
    0x515040540089140300c1c407000c00b05d181c0b60042c1034641191098540c1d40005000850600c003564044902c0d203644000c2040d40c03107407104590041c2c01c00a01910468104003100320f84061300981c1000b010603040030062a401d50b281004403003042c0d00800c21640340c04107102c005042d80342d83c0d1421fa0264402d44010030308040a4044c0011a000c0758018000c02c10304505001c050b841c0c000507250401e447e460040b40480802c481903001d041c07280540ca41050f4900e02c03a9881070f50541c070003400c1840164030f088044030032008d41c9110040318446141e04150360005040c25280591280e0043c0c0d110b00e8016041541d0b610000c5c0c80303900704580b8010311200351405460003560502c1100090070f400c0c00c1c4030340c80300244200311003005079078001c224804504c1e540e601c0304440300400750f050455104440c1c41c60a5144e415450709004400d04c0c000c20450116112090742c2c4c0038906580c04e04010451040d90414141c1303a01080400a40c0381c0c082043d5244460440d94079455210900207010f07855001c94200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 817058974 1250 817057724 817057733
    0x507020304050f18070c0519110306070e030d050d0e0a03050903070f0b07030c030c020901090c0f05071109060a03140c0a0b03160f020f01150602120403081e0906031003 74
    0x30100040741314140c048030341040b000107038003000e402101c03904d82061380d0181c80c80d255141001d2800c89041003072011003030b1800c000024211007900c0d1001c0c1c0230341d40036865828007a00d510401040781e56040e044400030008051246002d4000d41100950110b950044404040e080a590800c00d82c00030303000281001c440c2c20f04109060013030201c42030201c3e071686001d040c40411300132000000c00300300844650505043c8200f00c0380c03c0690f001080c0591a50750b0f546480020030125290a0106401c850902c3c111401a0291100f103900314600d03901c0e40f02c0c09000c0204113007004001d01d90103400c8400c040082122080d2807000c848801000b0115044500c1c10030030404401c0d03001e2104143e0420822a80e603940c140003410400d0182041c0c1c1c002100140164180300d111400005250710f01b840003045c84c20a045580b04965203602551030405100407198120b03c641d00001d04002e104010018450351a0120344004450011415050900c5070000500642c41a41d1078021103009403414824403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 817060224 1250 817058974 817058989
    0x40315090c2106020306042703200718111b12030628081f0b01020601230a030f05010c020606040204050a030b190203010f030b0a11030f1009050702030405 68
    0x1040b0000c800140b5100b0050408108200c0c041d00804968010000c40c820741c0b21901714088640180080345141030031852400c10088404405500103048160035101c1c0b01300302e03a014566516648090000305090011500000c0c000030500711005599600400c0300b4290640070301849210441e0040680900d00101443c052030b540700440440010001e0160a641e80141c07050711101501021480d02c8121030030701c85d03400e6940d100d064a80150844110090725904848035400c2070041c08020000007540120b0b0365403024003403214003100c18148040300c600c1c005100c54600b680204404100c54683d80c509000d030300030001c1110b50360344842e4080e1403d5014405554050420784086040034a070500044080503588000740541c00c0e45d401148e030440f84201d42405206c03602800350354951303488000c514195030910013038500380b00c110007044610312940240e403005c6064109040c115103c102d100150004042c2031900d44c4502c0c2c0d04001007034041801064170980b259000740da00c8510780024407411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 817061474 1250 817060224 817060229
    0xf0311040b07060f0b031b04050c0301050f1c0507061205091b040c0c0b13050d05070803010302090c09090718050102120a03020f071e1502210606040315090c 69
    0x140802448184201d2264105860b81a41c0000d0082800b076030300d05001c001802c03d41c00300c9416000c1c040001c503000b1b1204000014400341900d0400c0107584201407880c66000c00c0c084c080c4e2103404021100c90514121034404005c071078081c080d59890301d80e42d40785840c11140d42c5c0070801003100010482400350284c030036a940005100080e040540300044920001c070009002507125036503500030703480703110f00c20a0851012a071210350300c0c40608140580c003540b41c40c1c020088405204018084801a1180c0300769072903954400b2100e030031a425903007002000030000306401c09141c01032128000943c0d40c2c585250103800c01d40c603a03096554840149102482440d00940d055600c06803400c480340400700111010b440640ca001a01c4080c45514031066100f46000074cc40c2c0f80945810038400102c24400c2000c0034071401001c1d1003942c46180e00c0781680204d00c400a541041020680b40c1516445501c0da4030000040106c1c0c41c054682e03440706008201d584000318903d648801d90003c00c41806502c80c00b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 817062724 1250 817061474 817061501
    0xc0609090718150e210a02280f381605100e0706090506030a18050a15150b03071d030706020a0506010b03010b040b070807140c3a1b060f03 61
    0x110f100c1c80e04419903a50400e240c002d001e508080c1c1c0f407000529500091900c10707420b048101235a40c0d40c0c0c0c00710410003070090082d10180490b142110352005005062400300f1b09a100404202e0020324086c07031200d402c0503070441c28580703000081000050b0188110f030461005c650000840300200b00c15503103440080c0e008841800712010003031002c1c1d1b640c40240c0740c1c000a9910045003031500c1d0301c1451600b040c1c40d2802047d601c5181c800408120207480c40c0c0f400c040c98464108858007107210319428130050340c850b11500c80c030200082100304e8400c040c1c140584058081102c004040c03640803910304107903070b8826030042c0c205450040400c0700511465005280300101e490840d411320000500d41e10441c4541481c02030000b4080c0d0800841c0c2c005e8504039904103941610017a00d412034592174030000c0d40b04604c21241e600400341d460b499401c4100420310683c043c0d041040c028101d001061340b0312042a104686100d1801003501016a01c16000e8030190b52460791070f0040202c00780603640100f1101301c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 817063974 1250 817062724 817062769
    0x120605090d030b150309070503120a020d030b01050904020c070f08071d090606090414010c03050603060a0615050702011209080c0609010207051c0c12020c01020c0609090718150e 78
    0x2c0301d561100d15003101d034813424065950342d0f03ca202500e4a004030b16030189030540150f10f900944540c4002c040e00c0000655002e490309410b00300803c500715240028224003166082c8118801c07401c19a01825400124000300c035806030325009000b10301e040d203034040c4410b580b0400051207404041d80c1c000303880b200865a4180c207800c1103100c070740d21202d005190354010810440042c044c0080900e6040c00703110788000800c044012588000d000c0c10040350454000c3c451100420302542662281100301d0f01e09407501c00108000701380c00c0702d0590108030705030f0401100c0034000c1c0f890900d52003002c84561066810075074400c0003610181c05d08200070302d1488240d10520130722002c5031001c42e005282d0f001074804a004c0c960702000c15110a980000040c090300540c034200342410b6000600e484082500360221013070915001d0400c040c41c40382e4103606230007c4503140442c5541d40900c00780107001e040c0c1752a41801036104c0040c0c0b1480660280b0b030b54005003d00300b0481050808040a50807031880340c46a8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 817065224 1250 817063974 817063991
    0x706030209090c03070504090507020a21080c0903070b1206010e0a030b04030e0409050102130f0801060f0521100501140d020d0b06240712110d0e0a120605090d03 71
    0x7502d403000040c02c4031403110001002400803441002210301500750301108011508062400030b5440005030011900c0c0b808403900c50ba04060a606844030081580d40d6080c21030341c0702401c2150940000c04000d07014800c0d8034020a0140d40d240240a4400d5585105a05441c00b4400140f01220544000c0d0252441007800d1002c140c030b000700f540d4440e401d400c000000400d0500484e000340208400030b002540301003640015140403018403021600c01044400000b926403050728203c0c0c40c144241c0b56107003c0c0c036908018501704200015420000d503100c441041904908182c18007004034204020f10741d0724401401030001b4000722900d004403c0e104007078242c40b10b9010138040084c09001a2000ca695400580c80356140c00b000399030748600004400485002a45c600041e40001c0012100d40d51080c03d11903100d403041c0c2d444112240144010010101070034015121071041a0082e500803200758004a41f03401d000c4880c0c03148501c6240c000415141c46d87c0303450b041c01c4402007080c04260410524 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 817066474 1250 817065224 817065229
    0x101106100b07030302030402030313030f06050601020d050a14041d0702240a05060a1502070e0a02070c060809070b03190e1c11010b04060e061002010908191b06060501020706030209 79
    0x25070b050141e060070010303034175101c50002901d14007580c210346542d00c6820b640401004142206294002e01c10501031115860b000010b981382c45500f09040c0000d0700038000b914000c7c1c41482002c8100380f084020380c0c030305912500c0c100602e003029050107284031f91410500c01e11580c100442c2039032606034100300c3c44450001100c001c4089020f010132120380d8440b00400c8184c0c0c0c4050000d801004042c00e0b203448554105400713511899103100d1020340c50441000250210b9060007200c40c520341c07010103080e50509080342500c1c4ae10000c0c0c8074485034030402d08003003008020400254000d45804a95a2441c0320442a19064031140d00007040c254100410185010803200c01c0b14012003c181012234414a103550458014030409840c1ca0344641018000030b13440c1c112444888c0140381c1074581e11014004400143c0c2a508100d0b0000c01100301040740b00c0040d0211603009c0b0f81d203140b40c5004120500c4010b94031503000d5504005480700c50b40c810b0204034139a0100007010080c9103034102035003417490a400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 817067724 1250 817066474 817066477
    0xa0b010f090b0a1101020c1608070e040c030f0516030b060f010507050706080a0f0f0f1103091c050922060807120f0204020f1321120c02010e101106100b 67
    0x6072420300c40700f00c1c44c84040c2c0030290181c0342000c0c001401c8605105110060b2580403d19100c2c400003406811404105030040c6100325210381c0d084007100c6c249a2955440f901c0c8401001020b445a004007111521410310006004000314051408010182008420401c44803100180541884402c01c803c05c0080c030007203060740c211031050038235200e81d035100c410f501c01030070410032859405ea241030900590950664403240640b2071000040005090003420400503120540d503404c01c2c0d90000030751500110a4004500340741b203040c80c29500784000280820040045130710b510b01e6100161218180c00443c40c03090b10010b0101c0700041001600d03002c2d42d6001d0300d070710758400340003c4400c0c42c42d9411b40d211901212111a05d4007040341e940c80826152090000d01402416000f5013070201c08441007602d11001285650006002c0d908080044016501c8080c0710341c00303d05000f00d003c401e0700700c0c0d0355980148000f260141c880d0103034881400c031314904141c00141502a0020b000c0018000800e005c0c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 817068974 1250 817067724 817067737
    0x30616080f07050f0403032a24060e07051206041a0f0a081f0c050f031909020402190810031109090c03030a050414150f0d140a0b010f090b 61
    0x350031034030070384440c40103c501c0e00c43c07205550040b00340060000101540700070065201c0302d15408003140144c0994500e1071001e0002e002801c00c081e200051800781d4000c1c1445071030000451000104103641e0511280c6014048454402048000c40d0165120a4080d040d41d44074800f10ba0410980c020004100a10181c4026050094140006018458071116040c01c043e0410404443c0c4804030344140310681802c1480c1041d485080c45c1d03072015614001c1003911030790301c5032100690541d600c070302008508001c070080e01d0018a03181c3c00444056216071000382100d02030348035490340c2c0851280c0003524040d8040c000b10100b11035683c003000801c6403c91085611781e4210341c1a4450707103640c10f405103400c0d00c543c45194180030014030240f81c00d030498020411035152541c186030007146035080080411140e0000038084208000602c2101034910080101c02c030a950001000450369115400b03066044420307801203555030b1711f050195a042a00046041010f1800c10710341c43c10070713211560301e00450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 817070224 1250 817068974 817068991
    0x60a0e01060e0d021309051005040c050d08070b04050d0e150a031d06012c06010e0f063606070503090915060304061d01090c0302060706090804120203061608 69
    0x907030440e03150b91080021400c00380c00500440401c428000400000c240303000b03040300d00c0c8c882e82100404144c245d00030140700d16040000c0100d0b0910300b5080c403400241814040f40c40b030000f000801d00265241400c180600e01032802020401070500000c0d1035080c00b8542c1d03a22a10351a21109443c0f90420200d5070b0a1010703107000700c2d03e9060186c0389a50003100c2c031143d2481e03004080000c02c00340b05440c032101d000d01e507585e82d06036580380c044890300300314000f51500390010300498002801401c2c600c0c212040ca100142c44c4515001c07440041c02d0030000030201400c03c980e10003d820104c0b01e1b154658003c203420403203a052600700c55a40c2c1654a1241040c65402a01c43d038000440c00010311004075081c1201a09a50342c900c1c1a182c600010b00b0054520b14540680c03120304900000705103c0c071149a54403401c0741c0c0f13600e415a02040102d4010440c112140da813201006400580342c00701501c0204100d03031550030301055a00c101814480000e102013840d440700490103100030b030b10035440c0b500301407803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 817071474 1250 817070224 817070237
    0x80c1206150402090d05150601171618060905120309131505041407030e010c050714030c0102040b04030b061c0818060f071a010b030c1303150207030206060a0e0106 72
    0x711002c90003a00658008540c0070104401ca902841000300d02c400103864000380d80c44090b80c0c1c4100640360f5a400522442c280f0162000188000b84070742054803041d41641031421000500e00600d08228040e43c004000203160400c04004600303054050319541e00c03079800070710308080c062030105040d010009050300c021501d0381e00b60351242e840300c2c0304100544406441800314001c40c8898080c80141034410400280c80c0844074102c00c541880742c00b08009059440d00c0c80d05000c0d1b141c40c04024103400706034156010030040b04d0038a110910003400140b81d0160000c0e2550301d5070900c0511034800900050180443d2500c4034814a4a102c0d003031101c5500c480c005032140b0300902c41102c8080c0802489401100008110100c1c0c0c100401510207184210540344604070b4880d05c400e00c2103021b00c105140b090b020320200b1514240d80000d401c40b050344000600c0c405559482e41440c0b0f0300480300280b031207a0300164007424980d040c050700d9030105003a2890409645018000740405c8014841d20701000032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 817072724 1250 817071474 817071511
    0x702190f02041a091302150d060503010501060f020d090f060f0e090c271c1e0c0603110307200a0803100f0e09030706090201050403120207080c1206 65
    0xd848600d1480950003502c100100302c40c41d40644600d2a210b000d8510414506001860318180300004007403c0c2ea01808800003036001500c400903a410044003107504540310f02000c01c0b1500c00b440707013138028021030740d40d0380c010500c492000e8107022038000d004040049442040c0881c01d08030040c103045501601d08000a04010501101d60003003000045034481f000704280842c1c3e4400c20b018006038100c0d01c0c14031010300c0355a00b04100200d100141d190304014407401800d00b20005000038800d00e4028440c019403000e1664210980381686442265032481c4807000780324031070741407144c40000d40c580d24520745581414035001c2c0802207001c2100280800c40030118241c0c8000f44082c880041c1d22a500700d88a051010303864403031000703d0180784040040d00c50000340070044e40700e00500594040d4099807800303001d6200c3c0006000c20030402c0e0f06100d020003000001604054a94800011300e034040c003501814000c207141401c04201907603204400a003100f49100c54045003603a0010002081111502c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 817073974 1250 817072724 817072733
    0x10306030602180a080d0c020402090303090d0312180218090c060d1e02040b04030605071b0f0b090708100f0e0f060907050a031a0411091503060f070219 67
    0x1500001d080c540081241140181084070103070340b120b82165008940c0e41c072010300c5a51000745000c61400155510491409411306a004000400d405410b891500c105034001c202c40c4600c0840c2140050050b00201c80b500d200340c8a4103070024402510040c1070120717500001d08004515030450a06c01083d0b011801d410820884050038020142215440d01340303100e0440001c10206024150341c00150b400107070810014403c6070281d0340c2c5c062800d0b040604640361140141002009201032118040c00c02903100b201c43c1110303003410320a010000c0e51061510f8410310b06040a440c2210300da000d0311090001150205155028030410980040c0c2d03442c07012a0070010b852059181034080c01080401c0c40061000b1408500c964120740807140100d87e25418050425451b200140076032030300b9601d040c0103039181c1c0380068100d40036045400c010071440c0c0c000340c1180070950380b0081c000e1046003000c03524101401317140d501180e0042d032401945400240a07456520f07203c3c1d01941045020340030300822 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 817075224 1250 817073974 817073981
    0x50f03071e05040e0609281e1a0c1b1c2a050a03080705070c0e06130509030a0311040909051506030c01020c0103050a02120c07030824010e0103 63
    0x40040c1c11480c00300546014607010450300c64000e1601950402d0751200312903000003402405500c0d83c2000300482d0480149040d140c0c18159156440103007483d4000d0f0203d8014804441c2243e0144001032180c000d529103a042000f0b03003802c2121203401001001b07a05540c4001f9140c09503880302d1103141040304041041e0030129215841d10b0006204004411201d81c051840301c11464402c0c60805010745510000804050160004145902ca084154002842050600d0700041f082c14000c2c10801d081d40c1310040045603406c0440d82150344420131410345040341110005903001d034010025401c0c107000041c0c482c0f0075030980d001856150b140f5111400c40e8401201c00400401900300b001c139140d850101d45801c22840e9071485c021076400030901e14a000b241100a035174058008188441c08500190041e0038000c00d5800351a074280001442000c68111302449201c0018500703594213064075002d89410000f4103a20303d4008a440848190800107041c810a22000d08003056417440070801200603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 817076474 1250 817075224 817075229
    0x6030a0b100807030b0f07090803090d03110f2b090308072609040b01210c0e030a0c0905010e040f0b040807081602090601210b1302041d0a05060a050f0307 68
    0xd80f2410300c0000c140b014080c07045004110302e0181003125201e580c021030707103075066001e0400c003a042003000302c1c0d0b1881c0c01d0f5440074006e4440e040c543d01c0313044641ea2042c01c1010110444815800c40600051560814140d128124519481e841c0c0d000d0790742180202600d546000040c14080002105400e101d00e10944080410350300041c002e651005041d405201d40048440c0b074043c81c01d10001118540c0210980920616041d501c10180ea110300d000c0006040d084a4940c01d100d113041400205480611050800c54001c0007a05603d0340340010304002c958059000c101c1703200042c030a01c400a04c0c07803480100d07026000440224291070380c0c02d041440d8480c07600c0042c400701d00041c04d401d0b410503070900194190b001f2100744c5100d50ba002c00644180003030b0205004200d19501143c0320074003440d40a0b803a005c001900a142c030b0380c40700e41894100c0c0d0040e08444802050100207940d0300d00c8480b4a19400320701803e052126060601c0416142c04542c01140c1c4241117400e03030041c0540303082200800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 817077724 1250 817076474 817076489
    0x7020c120a0c030c0306050a05131101030912030c0e0402041508070203090d1a0609270703122c060906030a020d060b0910020f0c0d0503040b0a0518010806030a0b10 72
    0xb5100d5481c5050382c40180c00c1c1c03004580072424000050721900151148074800c003100c07010122884019502c189040c20200d80305418543c2da0110040030860105554500550075200040d0000d12500080c04003466081807030720850041105110174455600707d07000201503400c1000e2162500d080c280d0450150411840c1c00522402e0100300b03119080b2003a1180032140c10810a20303071140010300c00c148504072090301554480400901c800822803040883c088040340075241500d48a9840c4000001d016944000042600744aaa00d0305140f91600003d00842121910f0548800002c1442409041e80ea54400c64001c000294000c04580466461301902041041015203421528040344c02001da01401907c1021900800c5800001e000303695020403001040c2544181042101310044113504a1309400180320000c0c8004404003d4980030082d0b0700c43c1c5480d401030744050002d40154cd81d000d070405c04280c0500541c0d807004111407502c1900001c140940d60b4850782c40013450040342d4048603 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 817078974 1250 817077724 817077743
    0x2515110f030901060e0109020a08270a200d120318230d11060a020306060f040306060612140f060a050d2d020a0b0c1009260307020c120a 60
    0xb0007000b0650091054801200f502452039881e031503a1000c82c0200307507403c0003044400d80420100b0270841d07000054804900c11a003601285091000c1c1044140e54003121401c02c8000c007515080c00c811150341d0700600964400d401c07010580c44e4161040c01c680408000e05503240d512407280d50b1120701c012101504407400711940d0301070a80c6800f50168046819525000e814416040e00780f29402c0c0e000340c0404003000300700329150741e03000c0d00081d840a030610303510600030081a0030a214402c09400114011440011440d107086d0300030f88841003107100554100d1404015005200450054680040d0000c5101c24180e907030002194040081d07402c22548800c0700070b1307130f103080084043c0006910000862002d02407a42c0070310110802840280c025484000490103200d0001d80320068584598450300f258141c0701d901c00c0000880398100d0007a04d81020642c40350200c4940ca101ca01c041908013843c040c0303140f81c0410300944480c000d0501a209600c4441e800800e8141040030720750054200d100c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 817080224 1250 817078974 817078981
    0x200a0305150c040f14040603060509160801140411010e04021801031817030c162904050606060d110a111603020306040312140109022515110f03 63
    0x9a03403032068024007001c07601c6200015101002c0b400a4a04a440051550500904145500006003a040010350700301d03648940c00408911640110350003101003201400800081c1e044641100040341c0203502c140c4c0c140f4140c11449080b0b12150f80e445600001c0c2c4c0b422200e019001200c0611241013016441030002c00c440304882c20b528600c5860b02c0098900708078441c11134a001002241303d440203403240d0a01383c40101c200d045400110750041c030b00551285068041c48058003c5210580c0949071480200c000009031001032800e01ca52082842c50106335160942e1101e503241e80051000340584000705080e40869030b660400c00390207005440294507400d070004c0040030910a014103008a22408240400952080c2d0a10782a01c0e0044d016120710784e540c3d04d003502c080095a02500c10b4039505c1001d270003290004404c40b030107090311032740c0503071f0390403c0090501d001e00e100007a40d800b0310852490344002403591040440107c0740d111010614020303e02450f00a4014240c22280211000042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 817081474 1250 817080224 817080233
    0x9060601051c290a0806100b0f0c0f03041a03040b07030b0303091e01170405060a110702041506030f06060c1b03020909031c0219030e16171c0507200a03 67
    0xd000b020303800e448001342c403030b9516013103542c842060312a043e2691084505014544e00c0100a014020141e100b0f07514206210450300d05c0c003901b1281180d0550000b280c1401025101c3c1d810501000402031a079040d81042d4070b03503206030000900f04e0403e0542e0f0b901c0312403413a14180260384030964010701a9213511000000301642d244580040c1e400195440d44005000c0c00c24204140540d0300724008108640e502001c19004184100216912440a01035440181d456014002614050054241d00181780c0f02018064035410b40340b14401134207021043c821681d000c0e40624207590445c42c3e05610b070b121160340c800b80c105640c00c007079005030209042041d4041c002006004503613040280000d0710718074580b10402c0b406840009a8140240f01c0c1d0400c40300c3c400e4202182c4c1c2c0d09a401903851591058038140d403d080716a020b80c03500355055102c002c000d10b0501c80b03082215044420070a4020042e2002050f1380300d60361004141003a4400041115600c1c1140c0120320b0360003800c50a040340e16402c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 817082724 1250 817081474 817081541
    0x10030c180e0412020a0818010c08041e06030204081f060e161202071703040221100e010501050d0312020702130537110904050a0c0809060601051c 64
    0x10159181c05441e0f00b03520f80070784000340d004003564020b07400078109400c00980a443e001d90440480c10442081450700100e41482c00600c010043c136406651042c54820030408180b00c01c5d803140d01450b01c18001001850808981c4000d0000300400194829038031804550041a4640011114040303d03020400800706030310b0800a4481c1d161150103000070810809400c3c1d100e4040d00074040e10380b88242040004004000d1500544004d00495100400002811034034031003d423189442d600850341c14500e8019071140b1442c0c450600021312081d03040030046441c0030501c1d54010100141a65025280d0919034155910181c0c000c28400c2e258540c410944081c00d0107441400f0b48802800035201a141c01054402102c0ca550480220300c001c4e11000340010000c82840d941382031030070414070b02a5551413040e41d00c1070019180c00120313400b07042c500502d0305c9801441c80416a0001003408004e070307000016120080c1c000d94161000ca0404408200070302140c1e20440360b899900800c81414180202 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 817083974 1250 817082724 817082731
    0x60907032003100912021506060405010c15090b1902040b1b10020f041a0c0a1209051807020607021b04150503030d09170901050f0c0a0b0106021b0a030210030c180e 72
    0x14212003038000580301e0401fa15000780c500e59405a020803081200e175000d0b0361002c070554064409009100c451000c8001034409100c0d080b00e40400c000c040022800d02514a401041c00500d81141014188098820b0742d120b4209260095040100300c08600c01e810060030030600e007404800d5403250242110014560028050b151010451010b031a030902c010704180c50000c081640100421001a19030301d52800ca5141d05408000e03a011002c1200d45901200402800081c0c20114452a01802c000e080042c050903440071900004440c0c3c980c0c03080c0e031642c1e40d8004c1088900003948181c001c01000b20390780a034411030b050701003c500441c800350301e0707030217561241d000d09241d40300c08031810306604941c1b1404401a000c0742c014005d40340444d00e104080c04a2440b000c0c1254400c014649980c420320000341d00440040c1d100c4030b80551000750301e026801c03010b41c2c2903d018002a00356400030b5085080c400351102016607450a040c0002d228080c0040010309024965200c2038440c9805840008102d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 817085224 1250 817083974 817083977
    0x40312050903010f1e09020f0415090c0c030c030807030f0e03071119140a05030109081b0a0804152a020108060a050d0b091f0c02060907032003100912 66
    0x101040040a01500038194415030103445021743d00c00d481c0191004016008007681c021500600c50382d003075265481407100a818582c0c00903c01b034640303000c2e40152081c580914003000712240c0108006a001406c00b050349516003810305c49550b8040c01100100141c3d5140c440c601d040c1846090703100404001012014060214254100006001c0c0440c1e10014102d480441034108020401c3c185440b69403c010031000741800403c9648800007401c0d15044281916098030004009041684002080c0e501c01e08800c007401014600b40c507112160b01840c8240780411907295a040c261b244900302d80c0200c3c42100001c1e41003481c14442c04241e011a20000b207011410368808568140750400300c84c8201d8000502d08103001d041ca940b88200303035201800000040c4104c600d40003844004040b8803040c000d20540015101c04540300c001c0ca4040041c01984940e04518007d00c08124110103018410441d03460f0401e42c01c0031000424580059501d2030000c00385000c00003010401c040ca600749162806 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 817086330 1106 817085224 817085231
    0x4090807080909160905010f03090204050c0d0c031a04150b0d0203040b01090207020d02011b150914070b07030c02040b0d12140f04030b04050304031205090301 70
    0x480454803407001050050180c00e00e03e68041d07208030008074500e044008030340007808800c45170052034100030040c1d200402d003c0c042d420281e003542e40070340700b004a40f800305454071441d0002100d4902150401061007180c40c42400b4440d111072014410310981c402000c1044010311200080030700d58195607100051620a0401600b1251406038015903280390500d400181c4a1050304078040b51fa09c144442c00140e00da40c010640c03250340c2800e042d41d070013003d0314240b40c54a0082038020030000c0741002c2d02c6a5001d0582141201034070460514081c041420340f240c1e2030b20840d0142c0c01809105110300b401092050702c40961032170025200044d1480c0e040c0c0441c8400c2c0c3c07030090036070f91501c4c483c42035001d550388a0700c0c0710101071012001900700589030328418428800c511028124150a0001c0340c2400004c0c42214000e652240c04020500908840581282c01c02d1208502c254039 = true := by decide +kernel

theorem cover : BRFrame.Cov 816906474 817086330 := by
  have h0 := BRFrame.cov_init 816906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 816906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 816906474 ≤ n) (h2 : n < 817086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
