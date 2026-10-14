-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3674
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:21:05.143378+00:00
-- url     : https://prove2.me/submissions/3bb718d2-f559-4278-a747-2254070275e7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 660611510 ≤ n < 660791366 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 660612760 1250 660611510 660611521
    0xf0309031a0f0c090f040b03120403031d0105090603130c0509041202061521010f050f0103050c010212040603051005090a0e011b0e220c0509010206060f011209020102010e0f0303 78
    0x108440c1d5403081050f2603881c00d04030f4840004103100000c40350a8825074132070703038440a2130303901303000000c8088100050580d86503620b26003c0d000555619100031800e0b500c03074608145501403801c4420a007002018603140da034540003104500841c85009451050005501080702d031a0a8900d500a034040c60400a0206042c03c1c000e1801000030b0030712013415924410194552039370040c07102401c0f60014020421241584000d0041c4005c968900000c0d041106100c90680f9441209068074011015202d40c031081c140166030700d41451528081038182004100716240c400d41c020b5070041410080c14041c82d580d5400500d41000a43c3d400e602142e0341d103050500501c003445030a0890204915102c0c0e807400ca608060507042c03020300d860b40103c14003907145521104503a03514041c1440032070304000f40628440c004185030016003806001d8440d11011410600d8142c1100c03d0a610503503d00000f01e09415500006e081c00d50340803815503480d1510b03441110814000c058000c18001d0040d612440c01 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 660614010 1250 660612760 660612781
    0x4030321060503120d090602030a0b010f05180d061b0201050619080c0622030b070305090c091602070b03010e060a0e0c0a051e030906070206010801180f0309031a 71
    0x2014905040034582076040180340c40c0030500181140c9100c101e2a2140384a440307900c0540300201004120a20000801c00810001d600c058041039007a45d40443c02801204143d605101e902d090318004040910164264075040400c901154490b413004607010304100ca0100903c9107080030003015035100c03820070100e03040c1201030040e11910b07103102503941c0d440c00220715214504d503007a041c01404001810120784001494085030a080b40c4400541155a82000d170501e40c0191040340c0040c2c18900410310103400010001d440c424010080403594682ca41c03065210143d2202c0364080d4090701400050300b00c030100246000303050044a031205031525104015109095030031070001d0094480a0105c503040e040e055451142039810015600c0c00c4c0088480c00300c1e900303044010601c01000007088a0542c0128a8a0081c41c035034080f102d00b40d8070b5001450036104590a9001440d80254648010071100d540089030b16010b4141a2180c548903200c010300000f20320f2084180e4004c00081c0401e0f10031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 660615260 1250 660614010 660614057
    0x131b020f010b0916260601080c03070e01110f0118112413260607030b2412090f0f0703020f040504060b041d0105010e01060807140c03040303 62
    0x4a8200800200e042c01002079032065002d02034083c03150b402503001c03010078007820f1464400d0302d1740d400d402503e06603020469101d031400c80302140040c0701c01021565181c0070200313a80c060701641d00d4407445840501c004407103543d010070b81041d05110b001c0990381f103104207109500f01c503070030080101e880808504196850b440d009603542e0080c0ca1100b040c0240e0201a01d50315918110003440c1c650766003081070a0509072042340c1002e803000720621701c0d50303808409581c547c03441d100065050f65a03990303844c40250122040403a034540c218485443d0503424003c1c3e080181c101410540e201d5044c000e404088840f0311034104c903501c005030b008002008003543d08001000d000529200182855400c50303021a0004404c3e07000203000703540711800f040800030150041448144094020014245000601e24909080c88000420ba520b803400102d08000080c144a050310b0aa840d103451a0311443c008840c00c01c1e0102003049501002d00407540342c0f250a0000300700a5009030348200c0c045603c0682c0b11240c0c81e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 660616510 1250 660615260 660615283
    0xc080a030914070e061201090b0a02030a050f010305120f04080d11070b0405030703030c05251a0708090609031212070306060503040512030601030b0d05010c030c0507051902131b02 79
    0x50024204010800850000c56407180044c6c841484d1010324004c01c9014041c00c03c0c0c0105000d25007010024200d13403542c00f942c481c4182c8070b001c0c40191110071100601c920280005842608550102951300d01c0b840c0042c0040340540c0400c500e0241d4518460707080607102c0040740006900800030381307182c081c10814100074120100e80c803444e10346020b0009a40f842c1a100090621100e24040400d12006100c000c55a00c100c0c030b480180c40b080350303240703851b5005903001d000c400480c051400f04a0201c2c00b8103940d07a05030700040c1189041d5400c2c0c200107050b0400215554184101b0880d0021460103c002d450700ca05510321040c00f83c28480c00107400d403000c9400c241c0c10010305104102c0410400684d600c0911015600c080e034949402d00120090407010004d607420040b82c220769420014158011107480250713a80402944200b80400c850324032a09801a28580c00944031402051890078410000703031008003407802c2100080035500c10b58010501e003e098000070200c80c0c600a40501c40ca440c1c42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 660617760 1250 660616510 660616513
    0xb060c060c0403020907081e131b090c030c05090603040c151d09060603162a05010c020109031e021e0d0801080303280f1410050a050a06030c0c080a030914 68
    0x340348c00c1c401503041c1100241f1000d41c001c001004030301d01030300c1d03040141180c0d07800102415408005410311101c028062044180302c070300e000c8d6504003440c0300c0c0c442d00e03c050b4810b59419240519507410451030360800351043d42c0307041c0500000180e4800083c2000d90344012500c90000418924030701912440c0810501406104410100403041e6220740480b80c3c041c0d01c074100c0c01c0c011018400d04803221a542010424803891401c0c1002e0300040c0d0903103200c00c0c14841d400a110f414a0350804a080c0c8500c0b5000901142e1810104070100c40c0c46500b1860021981c8101d030b1302240301401100f140c01c175511900d140c80c1c0201e04100c400c0c69202100b103004d0f020b80c00086107107003002d50005e10302281890303150f81300030029014081c84008941001145c01100b03d8148020900c014503180c8001d8142c40d100151000302c0d4001a45c2c2c1440300d4140c0840b40018a01a8001d2a000013a40a40302d4940301008001d65200058000b85a500103000041880c0c1e0300010a82064a0640301940056442c50000d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 660619010 1250 660617760 660617777
    0x506030c0a0b07110301061202040e0d09051c0204060e090d2307020f030604121b05071a122703090a06140415051c0b0f01030b060c060c0403020907 65
    0x40d62240c100110854802420300b035034031002c50401580715012581c1041d415401c0010005202210301d003041821030003240c041000c1200000751035176074100c41122401280300314104116500d01480e8554942e0342c03469801440107041e43c0003c1c120f50164002000c142056001d0180c4500104a841450065400d20881c0150016011459680c074040d090740000800201a0110340340d40c00c111001c400e01401701d8559052603e080184103100e194880002055114040703402d1801e416000324140e0803e014040f1141480c0c418040c0c50b4030300f010707415403420400046605600c0380d5451031251aa440240320040203109011800d24050844d0302810390050220404e2603030340541d0030741120703031509059081c20084245032602c0c0c0600d9001417a80942d200c40700100d1030301316004001440703502100c003c51454040041c41251811112540c00000100241211754080d51009101004c0107160034106000f03e42c03501d00d0a941129551000003000c9420411418080702c81600304101d070800061 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 660620260 1250 660619010 660619033
    0x2102030604020f06040305070905040317011503051b070c09150f0b090103110309070510080c12091614030105060d212f06060405160818030406090306050603 69
    0x540e000c0c0900060320410301d000d1071000725500c03442100e0065500c50241e134440d660b220f00d0a402420120750540201d072142a00d01e481c9145410014180ca04110000c214502c100500310001d0400620a200b42c044040309a5000d0502101402c0c01511520240d6040c07810400b6240c01c1c2c030110003403546c0481200c42c05114030f510500c03400050b44d91054a40d520b90140344012000b030034101d4141c0c00c00a20001c10301c4001c01001c60700c44d041e108269030180e07680401ca0b00c1103032260300c00c1718140b001c3d24051180c1c1c0d43c4c1c60010500190000c0c0d008003100c030800c0c0352042112003d80e095000c2d50704c1c220b4152400c0440d0800b80552544510b0458503ca001159a01d035100d14406a00d0003c003800c0c00c0c40d802e0b05025001c1c42001131040414007079208003454028070f400d01400b9210030000c5034032030000020320503c1c0500400340310790554802040c00f241d001d1000d40e0908005400c00540e501700806600c117a8004001900c01044548d50b41c40b05a403841c00c11340c0c11104050a42c070300a401ca46540d95 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 660621510 1250 660620260 660620263
    0x4030f0201060f05132c010b0604030b0406090303060b040602030d060e061012090b01122a050d02060f0a090f090b0a060503370c020613110a0e0f01210203 68
    0x41114019611401c880751300301e240200030b20210041030304620b107005a0035169510880068400c007640c8008008d0442c411081002d14040ca100040103000b007a4009800102d550f0418810280f02c0d0901185070b540f11050190150002e401000041e0f01c08030300008144094040d110051040022101e024142100801e8940d03100506aa00707100b40b00d07054815503d05540000601e640004000b030305943c40d00b00742c0900309803101d41551106d86000f0000e2500000c4034645040c403209444a0030054034240612481e1898040160b80c443c005100e209152129000101003000060340c1d200c07003c505290509480345007a81050b45c10900d80340301104a520f40103140f00989000d81065500ca035607d24200800e035403c4402e681c012456001800920144400040c96051286400380125400508104d96504080304c82841d00c03c20004014041400c180301e8107040e00024010b070001e0340c3c48841c03141c01c2800c1600c006568468a2004006481403142d5100100c0c00000301d014030304072981c000a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 660622760 1250 660621510 660621539
    0x6030309010c150c020102040e1e06040b060c0f010b031c170a020c0d020a020f0414060f010219030801060e0916080a0f0f20070209041101021504080304030f020106 72
    0x641480440484a81800f84412070030f40032100c010700601c0400a0004020301030b410902c9608001ea201d9804200424528803000804201030041d5241903500e450400004d003180c011480d41004003080025100c40c0180300c0510301c00031640000ca08440d000c0300307141c5044a14020a040c0444210303840c180c00d07902020051103959613030a500b1440d201d0183c510b0092041702d900c010a44280461005120b40100d82d5030b164500898020304119100e00070700c01500c90340e04c1090a0400c1c0d8038005203c43c602a405038250718018412501003c400b01c1e9414003508282e541035000c41c0f40f41004220071a8006100103417030009807200a810705002c02e1103168501403030695030601076003400082160043d90b2010589011800062014103251190000100322103180f8440c0790004c10a003036045003019048503103450340500302d000107035110f03140c40100c07001c240041c1d41140643c2c0704244400e290507000c1d42c000c2d8003d02d41c0940d6400e0616001c4c21411850b040b030010340e4101030040140e5400203825 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 660624010 1250 660622760 660622777
    0x30c12050f160c120515101206020c15090615030a0201050d09111905040506042f0d020a0504060806040507020613082107021b030d03020706180305030a06050405060303 74
    0xa500d007001481c0f0385070903400c0c515040700461410466207102403007000504a9410510034842690b183c40d445000e808a2a4034011003255585442c21000090002d600414004843d482a80c1c546641d026103216200070980700c5462a600080902c10f01241c0c1006804003050124014001e202403607001034118040d801075080890f42c0d40c2608030622122002421804d40005c011000b00c4489000960f40212903008913400b0f2480c0c000000c584d800c162107151000c09400b42200c0030b4046049486142d4200030344040c04001c0140801d1391030030200d0000d030074000c06a8551a403281d060801c001d044400040c00148600d08000a0005458005c10941c0d0441241d100092481c811401c0c9039416104000d13921082c5481d02d4009100703a2800c40c00540500016401c0d40c2e0038032000b5042000310161450501d13499003082d801d90104a002c0d038010842c4a10a210211c2c2341c8403110050f0001030030b81203003030b40442c4001040010307682c09481030001900007110200554101600420307602c2c09845075 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 660625260 1250 660624010 660624037
    0x1a010906030c15051e0a020f06090a0605070c060606171f031e051608070f0f0608060a09020706140a0212060d03090e0c0720060a0f0e040207030c12050f 67
    0x10f074100200d10580803180c0c0e0101c1e4240d0419104117440604286a100040c00702c014051032140e2190080049041c41c01a424813009000c00703142d175140e07080100400383c985418880054464030020750b0ad4014000100965111441c200d11751600102c00304600802c0440300402d01e081004100b14a698950241c07504401d01180078079000145107071151030b070500036009100300d01031002d842c01507003802c03004c1d1460034060710061907079011100d600401ca40280e04d412114603030f041c805144a080300550104000b030214030a00da072410844200c4c0e000483c107450841d103620560a5055980d642d090300000d050000310b14048a040d111045240d018050358401c0001d00c4400052501c16209440038011100000e8024201500c01007142e50040c0411502855400c00b00e004104031900c030030400c3c0c44090815480d10500e50000c8842003ea804480c0074000549070b41e1500ba183c92014003803a0f81310740c40d01d5007601d41d40d0a150038900c00100880040045c100501403021004034240c913040d40200c01d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 660626510 1250 660625260 660625289
    0x18030c0201090f0e010305010f111215100e0405010b0910050313020301020301080312131e020a0312050717030907260d0822080a0507060b0d1a010906030c 68
    0xc0100c90540c80c0364000c440f80c0101d0f00020454009080382513040728801d030020040c680e0791141e00c5064070119501d9960400f414004511150790240791554404030404084004922003000900350441c90000d803c00a030000311603206900f0a03200c0e00c0d01600002000c1820301102500182d8821100003862080100220101d04035001c541d01c0800c1d03003503001740259100e40c1c4034031080d41e80c0d400454210303000b074400401080b020072842069010045e0045241c000310302d03040151200036070240e402242c211140030b03000008100040521310fa0743c2c91355030311156141654240304216800110705412445810000e0080207a80000d60102310790b01d01c01100d0084c04002d819000104400744402e4050203441c000110a680c84844240b045102e18a640c021752380740a100f003400b120100300100f41c0502002840328507405240603280291142c0000314510b400030000c80c090380d04501c070450754540600040c510f210315800c1100d0160140060400495113151600800c180451150f00d001083c410f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 660627760 1250 660626510 660626513
    0x6030d0f050d09080306010906080408030a1a2d0306090705040914070603020703031103060a0303141e0301030c170c040209040e16240206041104090f120f0318030c 72
    0xc1d81502c450390060141001240c2c018108406540e204554150005180c0c9030045601401524114050b0b6008014981165200c0c41428003e242020400040c040400c07a003103842d0755100c40c00d151540d004404280264100c406039030610380d50500481c0310381c010800300300d004000080d900c0c0440300c0031203020800e01da560412041e00c83d8580640342c060f000e121000b2501641580050640c40e200b41c0e820032006c2055000c48a02d1301040e20000e5028142c2c0700f042000c6407181c2110b410100309941e980b8641140301160001801d0504640c00340080044010000d00044040141c020b00400104400881142d44030544400540194520841c1e0201d0008095103403688a11550346401c81180d81841c03030186111251040c41c851444424909803c00c41204020003a64220060540003002d043d1915919901030030030701002103401c00e076a002650f002c9064400c0800585001e054811940d0040c000001c0c407103669803030f00380f081c181030000200c1c005c200c003e40d082c0c0e000d030185400489105a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 660629010 1250 660627760 660627767
    0x31d06040b0406050a0807030207030203070308060406090609050115080115081306020408010b040b0a1206020d150303051306020c0612070e04060602030a0e03160e130f0b011d06030d0f 81
    0x141e82003412456004035001c80d045410100805814501e40c643c0b01c030580c2d030610128107034031402d4002001a001440340300300090041c0d01039508030400070301c0810701d2510b5948841c00c03117945038400305031903458a004001e804200c4c91109800da240d8581a18a90b06058400e0000411030b0020b808020000340000c41003055032254080281d4060020755446650f9494039000c2c04d5108a528031440c90200340103c14903140750040210f40c49480121403581158803244000d400038104c824072251140000e9000c5240c29005c50040e603c01e0b142c071034481248151121090000760080001e6500201c3d401c0502c1d074038401500c00011048440f80615036407a0001c0324000800b20b41e10350003508000d030124000d81c000c000750402c01e180b5030716080e8002d8920109a43d030710812a103405141d4a40b002032080d0308002641540c00b50012694850314205035669034031000d01d211003910300b0030b245401400b40744007075802005405001e120421207802c03c44002502c400c03061b25100700b070140703408201307121601 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 660630260 1250 660629010 660629017
    0x1203030c0d230403111f0218060304030903140d0e0409020f030d0f031401050d02010e2d1201090b07230f0c120310150c02190602010b030a031d06 64
    0x22103001441e000080702c100721101c203042ea400c0340868007140204040490014501c014440302e0b01c640d0312100321540320507000390701c0f58004215904c1440b40700800d0361208001503011318480e41c0d44401d0b6500e1400e066500111000c1c44107015080408901441c40d846145c603021800d003141d00013045c2d0b403140700041c10242d1b40211190180a22400340c41d00d0b80e0880003a0b002e142640c0c8090098003901a04034403960f409004480e1301421001021000d5442030300c0c00401800060094040007500a896200c0031134495800c1250050280d100c0d0114104003006228050041000380222a51541c0320a0407000040c40c07007040000402810303808282803d0b0b100041081c050b4007039521080c072800020140d0204000c0c0c00130f485a40d10400700e00d8440d4088a102c1d280d580c0c2d284541e5400e050000001e1240849100f0030480d60982c010f0140c1d846118602510b8042c9884480ca645003180180c02d685100b1051842600300424046c0420303006900780d04980d0303600706105064006100050914003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 660631510 1250 660630260 660630281
    0xc01230f04180501081e190812010e04050c010c03050a1d0a0e040204050121060c0909051e15010518060c1c0206100308071209210b061203030c0d 64
    0x100034107090b40284580394801416140300c0020784034801920161400010042e00c40300d0440e03440310350103c0c12003140d0b00c4a404000d1185a10514208030004120038082d0281c10030f21103d041c21040c403040240420488460140070f003860a1140000c0c5c401a240d406161152420702101c0030362418140c1f14540c0076030007103500900c0d10082546070701c00c00f0360000c400c607001c0380030b54903201c00851600100034221001d4a03144a0ba80300030411a95031101601e404200c00040c080c16401c04542c440c500e0156503c21000341040c20144480390245403601c0d40702501000707c6c102400d1240c0400c1c1d030b00c9012038043d2a404105550940c4805000c40c4192060800f4090b42d4010070742d55480080207129641c2e0400940c0d4201c0d24681c403004021201c403002488000c202c14401c125000006040036550036690b83d032030600301d0540c0c0d0340e00009200c86211070395141030074103d86207144c200b00c0074842084c1c0040d02a62040740600001c0101c1d0340d24030018084102c039210109001801d2061500420b0088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 660632760 1250 660631510 660631529
    0xc1602030a120e1212071509020d0f02010f0e0a0501030c05070b010608010e100819050c090106020313090614121908042318070215090607020c01230f04 67
    0x4408000014000031a10701c3c05441040108105800b2450000c0c030044441ea50a000740c0c5403182603900c4071a000d52001c104c6201c95151202c03840540d641401c1c2926980c081ca40342a4034a070144001401d2034052124801442b614070119032542d10758113a5030b000d950003800c00068032a0900c10070b0320039000700d140c018505426400082005030b81301c0300346412610b140f2420311464440d084001c0400140d8011150301d64000c070401c003843c0d610340c80201507060040003a580880064400b064514109821280c00341c0e100040c0100d5030321311000c003180245441c803010410707607040c13407000c9008221070310559100d0024009040028441400408600e0340c0c8004058402605442c1403051900140320f200110014180c030324800c00d07441e1607580c414950052180c1071400d8040c507040d0034a08050414000c51150703e90211100b00d1f2114114042d04100004002528160341c0003840c0c400c0c0904400d04112120486000500518880034001e0080c032801c0d81d102d13000c030a910010f90045a1000340130 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 660634010 1250 660632760 660632783
    0xb01050910031b06090f12080306041805011d0a050604150e0a030c0b0106080103030c060e0106180203102c0c0d06090b091b090909100c08070806090c1602030a 70
    0x83d0850f6100a001c5950035202c0d1310b440e6136284032554203284140b180401e06000d202c0d01400003502080110762195000f0000605c9949a001003031804e0f11010084415a546050030591200504008891000814002d284041190f40d41585869014200400d407404401d4000300b41e40242c0c015900a4442c041240c42d24840b03801d00401074419000181c9004000e0400410749500c20389640d4182e98041d01c1d0074003110119174690380180403c1e00140307002d550704c2d007010a088407800e09009920030705240140c1c481c1804c004407040ca1210340c0c491032440c0e02c000c405d16100001100140c176100461030080c0c0841d511600b05195074807410310310700004c615000e804903221744281c3c0000e000210070345101480e607070780781c00c4405451038604002c150b0700c50a10441c0340519296044a82c0451240141e1700c000302141140c0e002d4032141080c002c04507040c18108404a58001340d204e130310440480381e8175024101000c0ca00e4040c815842489100402e10001c1d50a544003040400b43d03150388040c41d80d55 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 660635260 1250 660634010 660634043
    0x6080d050a03050a06050904081605010c0e0f040c0f1115040c060e0f030c06210108010b1201020906072a0b040f08010603050705010c031e0206180a0b0105091003 71
    0x180d100390494008285044003040d500741541c0301c2d1001b60341e0060070070007060b2166210a0728507000358110240020140100320b00042c42805880b0501015440e20460000b1030350030031404020070100140228030304842d29521079808524105e001c3c00d00e080020524181058043c2480c03c006402d5505506480a01c010000981c12850407a1007580c0c076100100742c00301c1048052100020060b615900c14004a1414a4001d0041000441e109441c1545803461010780c49010170907400300c0c90603552120f011019080000b2204c142e61103c0c0000c6151500340c0c000902e160050740d0700601005821100c1c001c102c4000741c0205a880840c1c03400c0d5800c1c5035140d00302e04145e40305003e00200d802d031a580c0015010380c14042c86081e01d5001c40030f0070300f03a03042c0b2004442c5107007900c00560070008124500440780c00e01d000c480400190710b41c040c0c14035150107110b110444121326565036103503003e1b0365a0f0021499a07440c0f00d055071821194844240c0b181906041c1d84e4102d43c2020b00095950b030310b05403 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 660636510 1250 660635260 660635267
    0x9060c1006082d0d030c0203041e06081b0d0504020d020402030901290612060d1202010203041a010302090613022104050706090b040b070201050f0d1d0105090706050d06080d 76
    0x554010144440702c10699401200001603101014003011682c400318884d21600e009412460101401d40304130786c00d05a49041420550440c5030010396002d520b19400c0c000540d01441e0580d00540b51103c0d01c00210310720840c1c80d801d20800c51940d100301c1d0780e00042411503407042002c103e1b080d00100150f449042c030040c3c1500070680203442200c500c640840540c1c07046a0b0310000030000000804035400e1880700e40d80000401d000078480c3d540100c0c0480c0850004070134008801203c601a0f00060300c074a014a404c40c0107800f840094030784046110700410046c1d90304180325a11400c252240b4865610411030203001c0c0c000e64a00007403e80d8416100300700041c1c9402c0d241e204a01403c1180c08580da02c00040c0da10b1035540c00369240030380c0c08210510410b10404010204140b0614006282440e20700701c030707012030704500319011090f80c441000c82d03200100c00d808468403080b110001c020074140f2031200c82e80c0d50a07a20031181401004194401d00700d0076503010400400d9030701300761003520b10280b0004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 660637760 1250 660636510 660636523
    0x2061303120b0409030e040b0406080c0904021503042306061003150f121e0f0311070b0307031b0e0f040c0e040609020a0215041208091c0e180c09060c100608 69
    0x45001f64a40102c0e091540740c2030203040101c2c0c0d10000504189441078044c05184007009005a81084001e5418040c082e4042c00942c03013980240914405068100700350021002413007a901040d42c041c6061103080e50302c07034039a011025400c1c2000990040c0709040740182d0380c3d440c0d010740401a00f41600180e8292501c90890400c3d00c21800c25001d0001030103008200d107690240034080354501c680d10340000740980044490b01c80740c3c504856815503220b01090a80d4800c0300d640e40007a803619950b0035158440d41c030303040600c2d4580c00c101104d02290700206846140c40744007a4403880d120b8502c904107230f0050303c01814840000c0c006101c400d031600030200196000b862504018414000380000000f02810620f0245a221220030aa0301c0b9111013182e040501510303000340c85c014442c2040c1d001c00e50b842c5005c04000d55840350790440c0c160004108004032180c0d0080206413110f401c1096141c00c05007210100c00e0201c400c00d8842e8042d0523418038000c420030780310303207203520784840440c00b801e000861 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 660639010 1250 660637760 660637787
    0xa05091f020a09090603081803120c0a06050105060324010908070e092b030f0b030604051b03030403051c020a02120115120809150904110304050d02061303120b040903 73
    0x412030070300d13941c0c48064100d500c94800071f00500f50900c2449a4502084c050340c00c41d05006007107481e840d140d00c80b64445c0c0d0303018001c8540c050340541c1217a0104200d5024450040104403001e50852402c2c01182d00710030a600070180c46407800140c0090903038000e13282040039010020840d5803640d121540d40c0341c02c0c1c00039100400c5038481d000700c0d94969003c4100c640d20401c0c20170140d00b01a20320900540284c80d5120503c0306c1240c441e441c424031520204001c61145000e0b000030100c0003144c01c1d000200c0c2901505a5020390000c100900210303900040b03154082c80c004030050b03480d82504004038200800c035640294403c03880c0710a8405440e05410002d8480d01111900d8402c0d87e45898003900320308030600052440e0320a105860003032400d006040480518441c895240281d80c40020301212400700c0c0800503240701006000034800d041009800c04030180c0001e00c080d0401c0180003e40d049140f80040403c04100c80c00d41ca08442c0341c002c00f1220501910510220343c0c00c3c030f001b03894020318155 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 660640260 1250 660639010 660639017
    0x70c0f0b030105060d1a04110706060e0c040509250206070813020f060306040f0c020a2102060c0a11120405030c180703020c0c131b0c0b0a05091f020a 66
    0x101141864400301101d04a450050000d40340811004018018014514850303a50308408061001b40f03031581e009602140020003030096445100d4503060080300c4003a0400c83c1050074060400146d1b8600400301d90075904201c5500710241d55844003103060540105001c5000714030565408881500020785034019010351701da4002c9907032503010410103000110310195014003804144410390a018005642098028102099180c0c848030000c1c1918824003006c001a4410f0035000284002c8201007a9526440020b0008101c80301400a5460901074509070b0300c00c2e000642c0d43c0549004000c8100052280700640320746000e189890710740b541003441118080d010381c1444985500c0c08044031454040c3c1494203071002e4881140c100d000350001c40c00d1101a200300600c50400d6074030206001c10641c83c044006c02c402100401c103d200040d0751103140140110710143c280000d0341030000350740c0310f50307882c200042c1c40d65600005894400d141c03072001c410098081200c10442d8161300144140030194a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 660641510 1250 660640260 660640289
    0x114060915071403070b04061a100e0406050f0d0809030a1b0f090c1d0d0f05061e0702150703090615240c140c030601060c02040515011704021203070c 66
    0x3030f07101c2e160711070514010854180c0c00d000600081447c0d21443c800309951208216aa0304c1c0004181c0034540004c40c0e1012171040341d05c8a2031481c02c3c0c010036003c0d000c00e848400c0d122058001041c0340c144900d1004201650100d86a02c1540f020020790580d190805146642e0440c0c0d11510111020300b4002c01a005403051008507601040340140ba020742a03d40d124000c0c0781c868900d0a000355500c6100a5001004100da01d0120f0b86503260302c0001406580034041c0760410b0740004d2491401400807008196002d820851101c0c0c02003112925102c510428003e250340380c08088000303000142000348000c0c0780510101c4200b42504040081d42c80031450341800c00300080c5001700082d8510071600015589200301c000040b0031002043d80788403000c08680c09612080f0000781046070036041100015001e4520f2030035032501d070180e0780c2c01150407030801e0f454400250008142224185806084905080200301192141e0307c803211140c0b2403105494441c541480c002480c40c40b42d00c611003650f600711 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 660642760 1250 660641510 660641543
    0x905040b0a020702010509040b13020c010501053a150203150102060603160b0d020c011103070f080402010801050d0c080708150609090c090903040803070f1506050603011406091507 79
    0x2d100311490140c05848160615203d00d04000103442c00401242c0c00c110a07850488446180340003078416004102d00120390b5604060038412074090003a442c40d142c1e080b140075040b000100b4100381655100d15156019040841d041401c14896071a03000140c0368070010803c48502c40c40c0c842003500c1d684c26402d460890701c6100406603600f000b2400750921003e41041000841503203c010449442d82040250801038410041800c40b294008003104030f203000406c2100035070f40f004003c401d58043d401c144915040640000703102d0304c0305002d03450003075141d80002e00505c95403084090017020214111202161030790140c580f00c800c9080000c0e551000350021071304510784188407900c030341d08460007030800240352403c001241e14040e0420000d400100710214846000740010001075020342c404541c101a10714101030b4850110885500320b81c50203c0a10156850350304480c1100c250b0402440c0b407102038000a0400e00c501340810703500a81da540f80b01741c3c41d1460805025008d0041880618a2041c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 660644010 1250 660642760 660642781
    0xb030a0822051e030a0203100501050a12170c030d0c05220b07020405040f0c081509010b01021f0b0d060b0a060906140a0c05060403080f01090c021902190905040b 71
    0x45010b140d50102c00e0101e04990400d5149400c1d00c0c16100508403180450240c02082c00d1810102ca4508041d03258030041c0011708007a00024018400450f4040b07070480c10b030b16002b101216147c0035424070f6100068149440c8020010348004001580c0104920900000068480e501422030301070b40c41e203103480185540c0d807003c5250041321803a400f09803400f062a400c200c018230f001041210000c3c021a150004501c0816200b400b420907030f8003d00100d9000c0000080300500107054040582c189041030f0b04e10790340803810f5080c0d07210402180680c510b820380309601501c1c91080282d004001001203009001d0f06401404180000303441070005c403901c0e0003040b074501c0440d00642d17011030060b8610703903071202c244802030840c5421803800580e8522180c0d1180d00304481910240d0006000c5028086140d540c01c10b00c500605c2030300c07030810400d0060385019440c1c80d114070102d69a10f20b0041120b0564403018080041810742c604c0c003d0074291507201140c001c00c000d9070283c50011100b00094580c080 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 660645260 1250 660644010 660644077
    0x2a020613180e0a0609020604030803010f060206061c0f150c020717060903030708040507090c0203310e220c0303080606030f150a0510030e06100b071202010b030a08 72
    0x11142c010300b062055545400024214040782207800c030b002008008042441500958003a0840e4000c0780369a45c13034404000e141c000c1c0a4421407141d10f039819107001da040070008030034190344d1140300c0401304000d505050186c0000c0565095426051080d403500582d408a000405d40300c1c1c03080c1402445030411070040d070b110300445c3c0041c40399004101040610340184c2c016070b8824880d1040fa01d03220b45510016094440040210015038008650132080c6c00c200c07050901e050034440c03c00800c6406031244070722524151711800e03e0700818600480c4003074480020328000c0711101c080d80d0075010070500c0e04240185140c4810340002c3d8620020074113501d8802d08480c0919003280994032180c898114031400441c8540c0e40c180e10070100c03180007490782c07500901c0244c640d05035240002c040704a0200f0604010004000b1186055040c00c04d01055802e001079822007500070b84950005201c0038410b03401801e10040c2ca42c0d00d4070508030310340308002c40344004040c24040010808010580101290080c42 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 660646510 1250 660645260 660645281
    0x60306080f28240203041e021f1b110a0801020a0c11042c0c01020102121f030804030501060609050306090705040509010f0501080601050405090d2a02061318 69
    0x4425098001d0b01c0511190001036140140c02c4078060701041c501071110150f16a4840680070f4021080000f03018120161a40c207414078a102c07200c9441e1940000c245406200400002048000017070b50100e10a40b007a6404180c044c00400846440703092400103c0904207a0921420b1300c584040f030f070908180250f60208450b91154600703261241c0c0c4205403400c045400b981c1150b40e400002c51144282020001010500d03a0128040112014400e00780041d11003510f055a004100203090303d1900c0b840203900401d14400010032030961100c1c121000060b40c0090b0001001190110031302c0810343c4048111007113a200c0c01c941c0740c2d03624107140d00c03501e0484202e49250042e00d4100a241001e401c2a42d01041010000880740c0008013607404452003a00084941e601180041c00581402d202d11038004540344c0040402c4040d88100030303c0e00040c0c102225481001c41d041d005242d0180c07450614599005008646408403840c00f81c0b03580c034051042099414100c4480030129041d80700c0c2c10000d4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 660647760 1250 660646510 660646543
    0xb2827050c0c0c010f03020c010212040c050607020108010909080f0c01050a0b090f04020123070c030c0f260717101104080304290c0706080a02180906011701060306080f 74
    0xf24540040d1144141c02c5012010b158003013050942c0024203100810b2440300710080244541481e06000c03041c84000e400c00790280070104140c1001d44c0e080780300e080c1190184000446c050a56140c0310055001d0742c0c081130710524004c12090091403040d0040c5203c0c0000500c2001443c2e10b42d0100180600c01340c0ea4241e4200b9600c2c04038026500c9103003080b00144501450080b03c00f40114000715540c010301040e00c1c0841c944006008201807060040e000306220f20103e00850300304034084400940892001680300031551042030a03c0302406414028807081c80e240764800043d22145484030040c5141084043c0b4054911a04217940c1e02a54155240c2a0056052904000308181d1954000c40d51417203020040c0c1c680107400807080004d100880228001e4008140303058405441180080d040d10141c1d401030011014800403030349010341800003200e03005142d4031388800580b0150301d01d8403203141e440b08520011483c0d0760160000400c45101800b01c460f4284940c0205843d8002c81a624250 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 660649010 1250 660647760 660647773
    0x22050d03050a090f0b0901080f010f180621060c08010b0d0e0c031006210f2a150f0e0a120201090e0114040e010b2827050c0c 55
    0x428801e801905400c5164181100c2c45911341a0362607481c4042d500c40a81c50000058402d825640003000340c6c0c001c0502c1000804035410110070303003644d0f0100d00400b070200e01d00600c0031980003403070340100c0010403000038010350010704444046021810840d05076005420008420346141c414104641250250341e05982480701d40200303000940081c2380a0f40d03462240f9400d154090364184012080759042c0340000941c81c1c90500c02000d00c0b024152118a4620049020720105222403900d41c0034a078084001c8411500c106c0d41d802c20f00381b82d440302050b402c86681c004101000a4140d01c141da03441e548409105003400c0508031224041c12030304541001804100b00400c80c4411111320300e40b0310504185540c3c544643c0043e0214909070700190107942030404600850915129011b040303d007240080c0801202e58000c20194a608403000c0800041044480c1803047c1428405018241100300009182c406138403201000081060120000e07181401048002403a10119190705900c0e401820a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 660650260 1250 660649010 660649013
    0x309010506011d1809010f0e0c0a0501020706080a02030c0409020a031505040603020a0302130b120309100c0515090c0307081c0305010f030b070e06040e270c04050421020322050d 78
    0x1c3e0f6400103091440302c4c0d0341f200320541101080d40507400c0851a02402001e0f1141010100014108140e0000b0b0654006034418445560f0080c0e82a612000f84500540e403500d134a141d0120780d01c42d5500c0810a00c0c030216110f0149a071542101200d030281454400c200e90301c070000c100880360307140320095000d02804010070050034000518448900c01c01d2000952106070808940b0700c1801041c420600d410018040400c1c0c0303485080b01c4440c4c0034078a8201212400750361525a5400384a4a2039406210000011103241c01040002c11451000e015101c096a481a07460b5032000064460018601c00c0b40c0500c0c0901d101c0d104150407a06000c00e03808206203074bd180c0e0000c0400143c81c0340100803400926080c00d88524008000414480e66681150720b0940074201035401c90300381a19a403069058070000c04100004e01421981d02103034001860b88171481d1010205104140da282000c500401c4c2001c400c1c0c02001405540e200c0c0d048040c0b8100e094140c00003803000d540151540030004141c501d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 660651510 1250 660650260 660650299
    0xa03081819110301020708130605041d0a1104060507050105010e10030b0910061706061f030b0303160308061201090302030f070f020307080c0102010f051b07170309010506011d 77
    0x89500402e00071861042c1c00c0003013400da1703008083c00d81e2025800961682102c0c550400c030b400070101407401900389030070503000100305a0003001c40c0f502d5082d85800304031030035102d41c40320b40c04c9064841065034540c3d6458001e4241c0d0090f240c1030b5201d51900000082c9e0305030680c1e03c01d11442a20255100e040d0455407200c509080140a01d0320510690b040450422168841d4401514010b4806260113481400262401c14001c02aa00a640411012842e41760104d03154000302002d090104142042c440402e00e1402518400c0d030070022081201e0080c507401841081c0100c1003941c90f00404440c1d000d655098030303030811000300140d1081120054011003580034107943c0d032103042807120000c100d80000b442c0403220b0f0024829034200c2e00c8180815a0240f00f10080710169070014001442c00003510b004103e4501841003101c90001428070412051002c00c8141c2501c031300d003154032030070504d408c00e009040c219442408180894040a0354480c40350301c1c520800700040442d00d400c3c40005042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 660652760 1250 660651510 660651553
    0x501030b06061e03070c0618200d0501090b2d1605070203030d0c020d09030206120a0b0915030d09080613050c030d02150f09070312090312020a030818 66
    0x208078000715514080c0f0004214801540101d229035030301c9809950b1030816004449415240030250541d00302a403000840081c4150300c80000f00902282c044045008654080030202c4000c140f5417800030014200045252032900504d103801c0a86003040d01070309091083e13a5096102c0600800c0540000c4413014403401010a030002490080d0030007040ba030100346140c0000c0c041980207034540700749048499042000e00004038030b61a10400c4545590003040092003003920020680f5211400210000314030f1300001051100507010035268500f03002c4400640490100355031107801040f2021030658450022203090b9401100600310b40d4590400034228198900002c82c1d203805860780010013564103000202c0200126005455074214002c008840110000c1c8074002901010081c0107a030b410004094090383d42c4000c505089241030310094841c070440d82d1000f01490a841d0405000c154003140d02d001141c4a6118145070340c480b04000d8040810144050049500010780d484118480c0741d5034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 660654010 1250 660652760 660652777
    0xb030a050604020708030a200f0304050c06270616120210050411010c140111040905010b070302070b07031e050a021009051b0406080d0206071709062410030b010e040501030b0606 78
    0x2c01c1c2d90189a843c1314003c0d4000c40564a027541000c81013105010062011103090141100c4051621414a1101d030003c4a81c0750020fa01c44c229000d80070031071300c640b000c5a80300e6004400300d9803810302c80c1c58800d180d454000c21090050240c070b008064100144c2c041c4034029a8002d40b0705034007a40c0b207001110400311034581554030f40c44c00d17560151251402c3c85042170f103000181804c0c0d80d543c10b040c00e90b0255072041c1e106403005601003240358040303903000c5840c1c81607401550003582da0b2075803420121220000128403652500c62080020240c5811000808807145280c00395409c901d800041082240c00408016100750017040007040f2441c0403841030080000c00410004510b511225860714100030020b1010150384040140040607400005038071890b0147c02424225141c13914500da141d03140034204511080c503070f0030b80304440340c10140c01804000c4040d15580c180d85540c2e10040203007112400b5030707011500d20344000d00c9506282c005c0a0580b03810007a85c0ca00c1d9180c800c207004007070b48031200 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 660655260 1250 660654010 660654041
    0xf0120070f0b0708070f3f0f0507031107050703111504090c2d080a020913140c0a0c020f04020903070807060206180c100e0a0b030a050604020708030a 66
    0x40940010307003825207a900844641d940d10419207805c5070060020702d0190034000c1449400c0000c45049031040101030b25007800245043c40d0301107143e4602107218986020580031604021104210240951082c0d10449660340c041c8084c011540c41060b85200e0043e01400c0380e008040f050000c150640505e5003003410151514545a903005099013490b08260000740c2501c3c0c0b100c0c200110154000308861640c0e08200e03049004000103604003401c2c6481c1400301040c0300054000403d150b00e56816105541c00141114007008a01c5002d41d008041515030032070f09048500104d5110b500d101f098512415054a5a000082164003003000001c440c00b0116031154003040039810b1614103000c105c0c014a48000100091420250040d08008c0d00500d0610411861a440322800390002200c0d8001d010a0b1a000a0405141406c44400c0c2c0e000c2c0e16035410045217030f000100808501d000b144542c0010320208500d49a050801c0240c0c860800f015001300414000b265603020107501402d0301c00503004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 660656510 1250 660655260 660655283
    0x30601050706151d090c1002060f09070e0415060b16020904020d062a0f0903030e030a1e030219050304170106150f0215040548030f012007 61
    0x58a02140300891312400d10080003c03418030213500c0003001034034131401d4200d8541001030004200295180d2000f458800725048501c0413503518001402120080e0211003003991480c80c081c1450f550303000400b09103444071807505a0001c8d1f44030501c425514403d0007058040c5000c0501d4003000788080000d041039030700403084851000003070014070a0001c0100400d0f900782c50540f0800290802c156115000c034140305008020700012980440f43c0d205907039041c101079040d40b20710030100b40b030711000690041c0456070610340c000820000b2480700e40ca1905c02d600300c800311001c032250100c0e14000030030020440c0c1d100b80002c0c00241110910a1a10000c581c00000d2560303494511001c2100d4a5a034400495600d9100c40102541849543e00e104003102511484e400c050743d0300c03959801100c0c820b0000c40c1c1c10310600e103a0f100c0d05c4030103030f150080c2d502c1c04441c40c4c1070f040303d54404041301d41084521038031407051440d0f0300d0702c0103003c1e600c66080a0303000014080c81ea460300207006d81c400d4100b02c0b1000d034144d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 660657760 1250 660656510 660656519
    0x8070807081201080c1f18150c0b07080105030304060c06090b07093303180b10030b0604050f0a0209060909090312100605030c0708070210031b0c05061303180806040b0c03060105070615 81
    0x11031134032398100741036919000354200c181000103010b10050201c101300300100f00140456140001103808407402498403502c80c540754103101d0000e10600d040104523a15182c18040500c1e4845c2410055403006100d02030001d5020048080f410100800809080c140c0101d0071a140e01950188584980380d10107840d1035080b6582c7e040200e9006c4540c10855504032030300f401030040741c1004030390185041d01c0402076818a040748184614000740000300c000c0d00021041c40036200c1006482c031080c4080e00308070140c100426056101c0d088108403605071118500020005001716000340111903098650910f140c40e01d04040c43c10303078000c10301a200503030200400001a2188210600d5002190f540040c01011044a00e0030140b07443d6038000800c0b20841ba03600c00716402141194120908441d404055407a51405503000200341406203945416100c4c00110481301081c401e2144d8454104100140c1d141040b14503203010546206001a1051107410b00040300c0d0b5200181c11400001f00c1c1041c030342d0783c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 660659010 1250 660657760 660657779
    0x3230103060c200d02011d030715230108060a05071e030204030c09020a090e010b040b0c0f0a050a05070f0f091e0c020d110307030c08070807081201080c1f18 69
    0x20448030700380d0144c040580da1130340c2889925401c00c0000c3c0d5490b40003420b400f2595076030145190280c00401c0c0302c10f2100f0320880660044c0145d6220842024442e0000404c05c2d0209100744504810740c05040005034110086104403445140d40d0307100e0044508401450581c041e90600821040c15070822021011443c07504c2007100502c03400c1005a90f03201e4516000380a402e450f40088105101200144000c291400c29107080d12540124180c4810703141310b40341d00e417200c80c04080c8558012070205105120022031040201030158084410f61507558450418400c035510a01d9980d444070380052240c01701d25007021003400c134400028038407901c2c54505241124580300c10300c80580d10201503440c082c0d070042005100303402e180000c2e600f01039054070050a4103041120080200200040d2041005030304401c0d9010103070041d0605444a881100348241440f084c0501c0c2480d2150100500d040d103080d84000c0f40a40c246840911384503a0301c18141d03001030003100c810003501d9407008003040c654407 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 660660260 1250 660659010 660659057
    0x506010b0714151f0e0105040b0609040507020618030306030705010f110f0f01110c0309040b0d08160b0c0313061a120d090f080a02190302090f0703230103060c 70
    0x200ca20300c03826074180003c9101d10a800d104c4c401c14000c41c500002c0210f4424070710f609044601c291004988a05050000b902911513443c403a40d02c10b01e00014004855800a080c03449007503040c0080e041c0b0090311524580d60301044417030a505074001da80510036544150350f0000d030031515082c151103859074008a00c0c2400d440c90300c500440d038402140300c403140780240607101445814104203450041c1d004200c03501d034030940e06428000d94844140701040c0d124840007450558210303444940355900416164000c000110068039480b4800e40420b20024001c1304903405118680fa5a0b2450392050355480060000c000320354400d2501f24888110170b031035140e01c01d10304241420250066850040001c2c100c410703241c0160080e0541c1b0a800e00921000090080c0e01c590101c600000001740040c030b6800f071082540000350071010701814002c0e0380c8102007503580180041d440c10701c0440402001c1c82c0c000010401070307c10841303101c0010808146c1e294004101d14100d4601079500c4032403800e803007140c010f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 660661510 1250 660660260 660660283
    0x90d080d0f05061504030506060607260715050603030306120c10030209030d03090213020c100606020c01080a0c1d060702090705071106040b120a06090e07080105130506010b0714 78
    0xa844108011540c44c0201c0744580c41001148101d04060540d00c40943e82d541c01400c0a020f1180000d03010103102142100c4502d40b4421030304049520040e0480c243c43d5044001c0c01ca40c2240d2441540512501034043d01c0e2280030080c0041d420340d0f448008200031034010141404450107017502c01c8c0a6a00c3c2c03420701c5e44404003d0307140940c3d503000440902d480e0201101e552810180ba0004c0070b030050b81c0b080400500220b14078070258980021f046560f04150000d02c5020060307280c5480041c21680100d5440300c0808241c03201c00c09a56070520850a030350403421980700040e1070688501c0b515411400300c00000c50040d240504180555002c107401a81c203417039a80c04908041820001c210401850007075020098a015007010718007030014249000c0e075141a1003068100000554080160f0320a20092602d080d050040308511403803551102d880d801071401a500300340018004204640903000310903801001800076030f2a1a040c5503058201e02d9003254070802160b86084101001c104407c0000c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 660662760 1250 660661510 660661541
    0x50a0e01030b06030702030406090504090203030708070305040e280c0504120c030516081207030203030a0b010e090406050907050402091005030405100906021b06090606011d0d0606091808090d080d 86
    0xb41c9c2404800360111170035920082c821030400d00c0080050b00d011050b183e11503480349005455022916050390782c0d00940e049145010f444204100000305101c0402c10410400c8134007c2040d140c10340324800769500b2070100008174000700410044c0d20480c1c010b542134240101074860742e454903a0f507090b0610141c680b258000c50041d61080c0050f000c00d002400110071203030402881c04c00d5a6038007a40300d0100030201348c11260f440408202a0340218141c01500d00010002e04003803802d844c0601c000d14060f5080c0340c1d184a207034000b0071581441d00c210b40760b01c2002054500315821804080b9203039440180100e40f0750140e0236014200c10b6040c0524040c2a100b03850140e151404481500d100340381c055403840c000d0f0b1081051140c1e5020114509401c00d5082c80c2521815610701c62021a4200340501f10703400144860740c0606118003a480001540c040c81000d00c4012050990004400418180600003a0301000306201a142071040c6410311807040c40f201d4105019540b04004076001d40c00e100025 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 660664010 1250 660662760 660662767
    0x1502010204180f1407080103030503060d020d14061b0301120615030f02040c05030c161110110f0705090c0c0a151509110406030e0c040e15090a03050a0e01030b0603070203 75
    0x140c11160055800e0011a038a0400052901c02d1001b031041c101880040c003844000008903500351500b0149003610b1380c014040118000151402900003480204003020134000c1d0008a4014140c010200c5405140ca4804034116420f02c61101200d20b2101812151ba1790307120590f40b43c046a000390308005500607078050700c1c082070ba8014842a1064030b84c2c10380c10070800708204400200c01030f007551801503400315812101e404a107042d0451100700010745510000a2000a445946c40f0072082c00d04010b9800355202c114902d010203507140c0440c0691a13014410b0340000710410590005003407041042c3c07084940003e80380e1642661038051b848611010b03a01d58184402c00902c100000300280b03440c02c0c040016118081c40d850450041d809808101500d410124403121001c00c000d0316081c900410401a017000750704031036542c1801501c2046401d0002c0d001902004001c00d110030300300c0c0c141d12241d00e40000c0c140c0490b07110341ca03495220b041c5a81c66040d8016900c0d02c0c00514810702158000355035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 660665260 1250 660664010 660664031
    0xa050d1709090708180102130306020d09020a17071703122505190903120c020301020904050c03060901140105090907050d0515120a08090625080301140d0b01150201020418 75
    0xe815414641403901d0360f00411541c6130100307223410301c00100c1e83c00c4000141c4945c8403848d890090200074101960001c0c101c00c01240d202090300d10f0b64051100d0408544141d0355542c0c0701150fa44294600c0741054009200f0188a140c0c068104c0e988806003d003950341000584503000c000d142c410907003200289004c102c1801c07480ba0070b204a000c4621600f0101141c91441d81e400d00c10001624200080100c80700c2c010046441c00d4041e2400c69500801c01d005519221103904120f400403a10644903030a028000541e00d6002d00c0d041503a910180e498618001410040c0030000201400c00d0302080800c02603030440c038040344501405014441c2d12486034641d023004000040305544041c505507042150083c0000e0980340032106103800541c3e11070307107449046091003004415010074101e003030b804d84214020030642030000c505079202c101000812040d40d4050000c1441464001001641d07944010304c40800712000d04410540f0510000d480c00c1d41b00ca0703101e204030311415103020300d1070f07200c000044 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 660666510 1250 660665260 660665281
    0xc060804031b050703120203090d06020d0606051305150d0f0e01050717150f030d08100b18150f1b07080f0d081f06020303150a050d1709090708 63
    0x458503242c00c0d00d801d01082ca42e2039898494560380b000034020101844000000c0c1d00034800c3c1c44251400030700f4510a450141000d0300694000070000007030340d29084000c0f5030980a50140c490b421402c503042003070303181010180b01008009080c08415a00c041c041038104584500a22055128030103010400c60000d03000542581c1c0060301a0302445018014544c00d1400b410031291303c11003000142109140807408191a011a0038000d501402984040d0440507013105070300e17018104056200405c1036440e0b0302441e40d4002d81c0b1814018049a80341080ca6240803201400000d0041401e41c2c604564131403584a44d9010307a00d0102c20b200d6440c142d024a1909104610060030040d01030044181c040a051380c070b0748128415003060240010103c1d0984070100c6507030842034a10903005051503254140a507698004882404041007820712654590411201002c102e502c09440365000381043d07521800d0a0100c1003241602c9441400342d600d0b142e40c2c490b0303400e0103540c007602c4034011414801d9042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 660667760 1250 660666510 660666527
    0xb1011070b030606070b0615120f071404051924110f0c09040305040305010f050a0c020a020625050114190507210e070b0316020109050a0204180c06080403 68
    0x4010700403091081143c0344d1101030444860b694007200d1107140c0e59400c000181c7c1030409501c00728261001080b2450116003102c0c81e24020702411071204a25135400004444405415810030b01140341444108103505001140310002c03880d485031141c0032a140d200c0040d0480c00d01c103240060100e201855100c07180c0003001c1c1300102c501e540203000c0701881700b6402661011601d085038000c01d1403070005418548120180d60103543d110000313011720700c40e01e0181c0c0080d15060b00c1c82d0644c24982160022200e00001e5075901d210380c003412860800724440d0800c014100d4118640700400c00342c0c04560000b82e02032040d4010340c08540c0d9952418103103c070401102c0c50340c03455004021032402c400e100d0000c2d000040d405564000103c2400c3d461011440c14000d820013480c00416031240140c003107183c80f103020287d0f201d64032410144144c800001070407402d0340e82c1d010014010b40c010101300c002508151b0414071a40c0e240b4103401006007000d9882180544480d404500002d442c14240420154820500f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 660669010 1250 660667760 660667769
    0x140c090903210f04020d08120406060611061b03100302130e07050105030c0d02250c031e030503010902090d0f0f0b0c040323071d010f081f09060b101107 67
    0x100b812850280030040c0d51810280019118844510346c030020441500e00300c40e030b02440e10600c007449003042d280400103000326004d0b0302c1c041111840301800107280013483c28403440d046001c0c44010303990100c2070501540081c040006090a130100800541c03100841e545a0001c06140094940e00c0212906e003400c2c802d812081c1008410418404184004c80c02d546001048420044c1e86952801c0084c1c10702840d05200741d03040b58001c2c482010b120402003400f040f64043c401101d601700d003010300385904032804a0b00401050f000d02c01401054160740c050f2107481c1d00605480040c0050741c844135086246840d04488a00300d00743d1200401ca17a00b007096400c0014024000e06250a682c0d503042100d0354403005480244000394840c0c1459020089100204081a100f031080410100c2e034440400c02401441010b06c00300c500090b140d540060048015260380c000f011003200c5e903d00c01c8000e050000c5003501c1031030702c0d40d44507070050383c5800c0c84403d2129191500c8502e0b2007101582c81c24034138990302 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 660670260 1250 660669010 660669067
    0x905090a1212020409060e10060212070b181c111c0c0c090501120204050f070903170c06131109070807110a05030d020703091a07140c090903 62
    0x1050000071009800c0807062042414001c5401d0b40000d1102c009004661081441c1801c0550000355a40780c2e404640c00340c918286460082c0d0344850090f680c4900300c0700070755070303d000c100840b4020404150420f500310300200c24034180100c00325030144c42e18050b90064017070b00b41305a40864890350400c5486580028450240409110900c0c00e031310f04000ca480c0030030500c10341035401000c100041c583e9030f0280c1302070242040f00e5612441c0004203854100c00c02c9010754035020204888440b15078a07984681055075510800c2800c5907190b000c0308025000f202d4544000b8004000c102005110301481030004100c01e1485040f14186100c0104100003d540a002070100b44401030b41d00000003503101549040c821b42c1600d0000d4854a492201c0001800740d010100e10100550519002080c403603010f507848848250b180c481d02c45000300041d05003800f03107800300048070000e00040c8581441ca0000019a410003154002040040074120f50086041c2c0000850b6042030b03005c0e030601400c0c0d20a000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 660671510 1250 660670260 660670273
    0xf37061707050f090d050d0914010e030c10050706050f07080c0705060c031e04080a090f0e0a0b01090914013816020a030c03020a06050a120e0f07030c090509 69
    0x100040d000d4800c010840400f080002900445a00c1c0e075028001e0f80c0f0b910404403038002000440041110700c150241d07071a425480200c1e001698400c40b0481c400f03a00c0100600048105101081003030700d44086c4400602006010640c049041072081503c600d002c0c5103800140c0c5440100109907100007002400140ea05020410200c2d000051081c2e101c00014400c42d80ca8440003100145100d240003410311010b031010070001004090300143c1140b1072580c1b00d1108036038503070b60b05065541e0540103111107001043d0015030300c0c08458100c040400b6047c1082d27400981c54200c2e64055030202c0500220024407880100407140040d96502c49018850b500fa5048461910007046d1214060003c00412100800d00000075034260402c03c041c41d50041c1046105556031401c8088524144003d0b8421465484002065070142046584586050b90b8a01050342916040350090103030044541180c8900e094403440e80c507042044c00055402103207140c1009160610b400107892000f0a0783d0450303000603 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 660672760 1250 660671510 660671521
    0x132003060312031323030c1606020f0a060f02190c0b0a05060d03110715020604030311040608071b060e0a02030c031c05180d12020105070903020f370617 67
    0x103038410f2130040d6100c0b00300c0c903100e1a440549409102c6a241c08001c6000c0040d440240010014003041611305e00e0492001d4295140700580e06d820f4503064071b0416401c21000000040d0041e4040b0300710030a4454010306000c03030151100d019010411070200482c0b4008118000d102106040c5a80070054600c140306515004000c00d03280d03440349500400b40400c07508004415074060000402030005125a580c0e90000707175400075940d403410384041c0c0202e4076020b010f40c603a103e13810840d0b041ea00781e1707110780c140364649a404590942c500c8981c185011481c006550004042e4029040b81e803494800400680d14940105810441c1414000f4442d034483e81a08420343d9000400054054030350511135210041c4c465400d008000100000b60b2112a8252000c10803448084100c072081d080d030300030000c41d512032409590740c800601001c4d51040500200301100d280000030143d0100991031843c00a2000308079507d040c8499101098413104490410301400340d000015480c61803c2d51419125401c00c07 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 660674010 1250 660672760 660672781
    0x1e0c03080a1a060c120c07030b09010c050a0507020d0203010c1808070f03170705010c020709051f030623010b0408060903160f0c03081314011d13200306031203 70
    0xd01ca00c83c007074100421107100c2e0003018840010413017060954581d48040f1541c1d4039407181160700040b1440354001010451a450504c00c0c4010103a01d0b0f12041d183c250b1041c02601e203034210740030487c0c1c4010100190001600e00b0b005003441c0d401151110800d61410440301041ca1800fa08807145990080000f0400c2c1c41c41c501e403000c1201c1d0082010400b4000180c04c45200c1e00c6110030143c065030130728590795882c44c0d000810340704a03040070500f00810384541c040d900c804140103d004644104400341440801d409501840440100180711003686d005810b25040e841009d9104950089000c00e0800a00804ac00791580c0020044045c40c03400788a107041104d80344040601908030741d035501402d410410b00e18401c030055070f042001c19484241c51559669002e0705406401800c50344803103400120b50180c2401142203010400e400304000780c0c030040c0030103011480d404590460711100e4050312030b501c80011403112205684e01d143d407071420b901414944200c0011302d0300d0141c010404c00070170321017 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 660675260 1250 660674010 660674051
    0x240d0c02121804020a03090f141c0804030e0a0812090a090209030a060207050114040b0a0f0b0102151506161202070b0d020d090501050a090501060f03050312071e0c03080a 75
    0x110f0300140c841401060440c001c1c402c224004102c0b0005001074802c1c0480d070101a1055154041110f040c40901c030701c5036006814002c40000441c22650108000a00401220002443c0680002d900640e03c0e07901030300d40100603902516444002480340a1801c3c43e200a0015004d0690198a420014804a5911041050060005540440c0c0f02c1e003009800c2d0030080024104800003036042c2024140004442010b0b80c611001c2031605072020380c0c07040c140c004c40142045c140c01405681141030f9002444030300013000348040c0f10f2002803002290f0f17151005801050400d5000e401070340e00c1890140001260210114159400010104207011001c021a035071b03010711503405a16610720f80c1c91030000e010700002c010700d594200001c010035216580e20860303503140982c00a01410356601c00700c40c0407052901025141c0d07002007006c0c3c444440550ae4880e0444220f1600600e28000300c0e000f60380c140f1814002400040e600640101450b5000c89015001180d004080042040540725004001c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 660676510 1250 660675260 660675307
    0xc0509060a021615030b0307080d05070c12120206090304050a060e0316030305091806180907080d030504060b04021c0c050417030702030f06090606240d0c0212 70
    0x340014000c003041c0c03007880380c04224000402e890b4102611a0114070180d40101c0c0c04000207881c1c0030b00c60070320b07184c0020300c20f040b079a00038040c002d1103944810817616503208503020341c0e1030001c1900001c0d440d0005c424584d691405100c220b81c41c0710084200a0505401030070080f196071013031005010554520503034008451090502044460f18540403906011b070085070034070b41040407040002071603005402042c00300070444103404807441064550400d01015038000d60017001441d03500c6048490104140d8020841d001150360b26a80c40188030301d413451002070000069150000d0104000c264010003001050480701981440c0f00d030a680c0f41070131a100c103142d8100e9112072601800c1c90160f401c03075018080c0d42d00c600b14460840f10074503a0741e51000d00704070300034442c0e204804215100803850a00400140c00604925150641080705520841008460351038002c900c0708502041c00e8002d068022803204042403a84503c0c01c06803c100e00544c00702c440307010401c5200810310031045112140e9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 660677760 1250 660676510 660676519
    0x80d08040c08030c0706020709060e0613140408130f050f0103110405030d180506030105130e070b16030f0809100e0106091113091b12092a090c0509 65
    0x9a8a5050420701440c4603801800c0d40d00001854441c0d00002150440c1a01c403e5022504010365030183c6a04a403141d00c075002820f0f6407540418410720b00034207458030100340d44002254424100b01c4080d84200b05503022128904009030034045905455071046c010a80d038610305420a01e040080b4407400b46e42104c1130b040541ea8806d10032071000350011ba42c045e04014048440d0a0511507015002d00c0e200f00540e980030ba912080041d803858010101c0381030750130140030321500b1501c14041e00c0240409010f00107060040360404117070311584401410a540d450790328590318006504015041c180d0341d0501e0030400030500c04210040b01c0004801c0400c1448081c0000d0501c0450071460042c0f01d10b400c07540c1014144014103900380c401c1405030984400d9921500045640d98141100312414000120503c1114090004909000340c0c0f5918940f00d4440d8040f5100b84203a4640c9402e0440395201103d850990880310f05e820500000f00300909426075040088002045d009401401045e1890f40704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 660679010 1250 660677760 660677777
    0x409050a1116020307090e0d081602070611030c06040605060f010c031b030324030b0a0e07030b0613050109062c0619030b0103080901030f0207030c260301030f11030304080d 76
    0xc6440070017150008107200d4001300314040700e64403440c0d120619028200c002034844000b00d0906460119100c02c8005150014040c03503240c850141d5100c28102061035050206114501058200b40712042c452445000001030a02c1e01904010007411603104907810001c030102014002a0401480b0504810f150048050000e0714503044001d080d5080341440c074680360400c0f08a0000702c13480300070180ca2041c0345c50341d03c5030364500c00d0b1412200c40003400082e40c1d0040500b000801e6a09140301d4106a000d0070007403a00a0405050341680c0d801e0344100070090f0764034410482d409024203605010700b084084100c400c03484408010f00500007034402c40c07140d40c080c6050300c0c46440c8a52054021a4070280004c07072980c2d6810004556006010114082402d0100311443d241c02032088441d0b0b50b07450346031003400f140b860702c400c0000503404043c1c0e0317090352440c0c000080020180010718000c502c01c5a44031064429441c0010860a10700c0800d030007a8801d000074031510101003959580c1401524001c0f10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 660680260 1250 660679010 660679013
    0xb030901021309090506011211090c0c1e070f120219050d0305030609071115090f1e01060506030118020304110607030e0906031b0402031e0106050409050a1116 70
    0x9109400c42500100e519100003c3c1c80c2c03200e40c00c094040340c0141c2c00c1e10790a0f0703602c5090075241c080c1094002d1148040c0c0f140791407286030640c104e0f41c22071484403500d400d00301d1080384603141c40b501c4039559050512023100e602840e07078100300d510040d1100791a60003851749000b00c0074680c80c8544074001c3c82071590100040c083c0741c1c1800076000400005240e001e01012504028007103500580700240128425000140c2c000d00807004c1490b45100e88005107c481800e6094000300d00b0081c2000e4114040c800e003501c0c2381842000814443c0390608040304e0781c417441440160855010f980080d004e454140f004001e05901c06100c5101103074440700140e40c1c3c1e5154a4260f0020100d0100198440004119441410740c410400c041c80001901c441e0320030388544003010b80e03c10701d0b07006043c8800102d0100141a007010b4010b1a040811450480820045150f2201c1c90020903044000051400326040003021400c0c040c0c00c0c1c2025050300204081200351401e2a40b921a1074100340d400542e0a0380741d030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 660681510 1250 660680260 660680263
    0x315100215090115092403031805030109030509060d09210201051503030a0c1a010e06010e040509100e0a0602040608090d1803030f110a08030108010c2c01051b011b080601090b0309 79
    0xd403071038003a4807000d1441f034132498007401820b60b940f1074506200c0105404a074504051180b4885a5099110b00382001405000c0240c69840507528031285030311200e5520001d104d04100d001a0149040038101e1100007910085c02c40d14010142d980280311652009219107020040311102c0c2118a81040c5000320307030a100d000030f520410114107038030301503000085008800c004c090185909994500900ea10402040f080d02d409841011843d002a2800540c001e9643e000350108000c403015605600700e90744803002280c100e03a2140c00841c040c03c1c00c0002242c1d052040003080a954108410710f010142c1c64410f1105544c0401001d010106141ca62028003e90700003141503505d1003100c0c000340440c0f50000c0660021b01c900c0805600380011211823134010b20840d050030500788a640d1551541c14440c1e03000d06080001641400000c003c0110100340d0441d96000440207080003141c2c1c030010301c0000b81280d9240c03000ea4100681001440303d140c0e80103030301c03c048031070145041c0d44a484003440170f03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 660682760 1250 660681510 660681551
    0x601120f03200304150e090a02180409050303010503010e191203020403060e0109331a09040f020a15081b130806060a120512031510021509011509 64
    0x80701102038070485002e01503000001801603072034401c4000701e5a0900b02c000c5d1071549000d6011035021120798001400c158165002d89040000204c4100505c62182c002c00c04580c4507032420b81c1c031504000014401d508003402402a51180940100005686840c01810540c0360640040440c1d01d0b107201808420311a8054078051508444200305900a01940310700134400d041080b5a010010b40503103c1c2890381044541c0c841e40079008040c0c1c01717141341d040500105008201d00100034a418400e0f603450702c030304881170b224910900000842500c4c6004000107420213902800b1182c1c84148800da400303a01000b5143c0004030782a080022a0224540700481d00409072540c0180300b0f000030000ba101c200050060240c14140c60518240d40c81f40b47c1221003d4003984c01801303d0340b0650241c1ca011500e50300842e40207680001700769410258000180020149165200c0160301603424800d10102da241256084031002c0700030020203980c0d115159880040d885040303629a03440071310130603220003401d10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 660684010 1250 660682760 660682787
    0x62109020d0b0703020c0c0102030405100e15070c140904020a03030c02011e0f1b02010c1716060e0d02060106080c0a1202042702090a0e090c03010e010b01110601120f03 74
    0x5601840e2490f0020000c1d041842600351703500c1103840f00c182550000c0101d8080c0d480c003a003615045000100c0540344c0701c1c220050f00750000080c036480341611810030050b0110a03c9400400c022920300801a002c0300002c0c1903041c403880c0c0b90001d000041e610024a01c049903494201409900803600040c0d0389040b010082e0720b2210300c00b45000104079800241c840b00c000040c0c40f202450807a5407001c406803401540300a021642403c13001002c1412249a089881e074004411840d019014007000c101e090a660100e580d181c884c02c1152510809012408080841e48001c10b410340c90494000c0a40801030082c0c60580400204284d00c03034482c01140a219021800640d40c8076950a00300120b1100c0e034500c681c590614206082d210010750088810307405000340b0745446242880e0044c403d80001404c8180d8601c180c07030406440391000c0c05414000d01c414000014964031a00000d0007910f41c2000d4046981c011400602c45081480410844103402a402c2e440c1070515180c19102c50215800 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 660685260 1250 660684010 660684023
    0x2070e04230f0d02010c0801050d17130906091802030c040c030902040911010e030d0f180509040c05040b10020307080d0617061b0901020c010e0a15050c0106062109020d 74
    0x60703500c1c0c0c0010010341c0c040c404550354006c100000309100100c1c2e0052084c01003603400201e4000c44004034490140300c00e070f1080b40c142c103c1e00d0031981d40c03c5010180384683c48110f003551146820401b40b5258030070b02c0c0c2c1d1012800324109446805034000b81c0c481806003501c600c0b59a8030000030100b41e10035404060035070743c06407040100715514240008101c0884c02c000c0d0000c1c02e0004d41001a00b404030b0141c641000380d45a0140704d41d5a0a8103640500151103c00500e0458401c001400d503100003180e80594020941e200034542481c00b0b2000750f130079044805000e0b52100c0401074035a68000201c03101076130084d01c5961518072096049001e0166a844500e103100719407100019441d002c504240103032a801351554900c04402e054440a00490f041180542c2003081461070b01d50013611005142003000700b40070390f135585820054000c00c00c02c100c030000082c2c021070810441c107030034030400b4050000e41c01c100041c0395954910220500204604514030341d110300b80c040c210340f140b01141c002950301ca407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 660686510 1250 660685260 660685273
    0x50a2304120c09111204111f0e0102010e032b0507050a02010b0429030a05072303010e0309060c07030209070e030d110c150f0a050901090602070e0423 66
    0x10200200142900d0941d403002200200103442500740c4519443c0085240c1d00d45e003450100e550144a0740c80041064a84504107001d074400703996030b800c101640f5011005600d08004420703000814082c0400c13041415685007010309001a400001661080c2c042d034440c0c0300d03948011080e4102c40b2001110048101400c4c5010f111442d50004040d10700003246600030040010000100010f4844011213850040b025491450003032154100c011400031001e0121000e242d06a56407500d003a0b240e5121303042c00318500031a00009000e00300c1c038000011045001307100100c03200c03060680700e1141052141c80707410000350300386414409009071402103800074120f400c2842c00d44005490740601c011444d101e0f004003560b007510381e0300611150340e101124000038034610490400340218000e0a41140841d80014030040518100450050450003202d6035419111300d407920000d0810880c40d004041036422442c010300c08080304006140c1d0080c1c0200c1d184040c0d0340e01041381d80414244024031241c0740583c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 660687760 1250 660686510 660686519
    0x906020f0405090703050103080d09020105220510020f060c1b0f01051005101e09051528141e030a061406070f02060c15090f010f0b01050a2304 63
    0x340603004503081580c0550325642c1e1800110b04a03031090100510740b05041c4036148084e04182e0203003103001e10606090b03252490b0300c51417004081903aa00000480d03501c04003400141803c5060003100710b01c0f80011b000303000c1000f5105441c0c0074003e040030030410f804542d6541d40003e00b0502400501c400040c0d07401000000100c43c0a0002183d81030000c06440d1b00014a86c1084641d101e0164515075820302c0b50a44240c800b00c1c0c6010300c400d01e40810900283c041100e5a51106061014031507000c103560300e0161034030074400b08000300080000c15905c3c2c9440f4013115049010156001d028128003a40c2d180c0c55484c034041171007000400308201c41c0210400400e00281da104005981060028140010032081001294030800800400c0a54030a01440043c00e2500281104040b82c0301a00c00d4800c801c44c000301030310001c4400c904d2950103000300b0804030b0801c2c4501030072807901e69802c1c040c601ea0080080c0c0244a4408214100400e1102c45030568140741c0200d030032001c2080082c1c0e03840c0c1d5107 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 660689010 1250 660687760 660687787
    0xf2a0f030a021f02280b0601090504110c010c02190b100b0a02031e0901210b030a03020a03030f0501060c020118050a09021b0601060806060a090b0d0504050d30090602 73
    0x30741d1524009031252080405c880104022007072200600d0340a40400c00c0d03400e0390f600ca01c201c400380c002414024840300101d0103650b0f034019002480407941202d0b448040c01103015007541c1d1442a001d0940d00503e4185600c4800c1000c800c0101d80c005082d070b00c090300e07034210900c0080c0c1c0c3d55001034940e500104041400640c00710040054039035590304a480301243e1100211680304071000540031031720800d00c0303000b000c003204220b400c44882140700050b90070166012a081c035005500440050700002e494008164051084000b0390040400412596061102c040c01449045d50064144580031402c2944880c402c0c0740140642400740c5546501665551504047d40004851405100615004520240300091b80398100e0380b4070303030700c040f15900ca41040c002140d110b081541c04001c0104804600d02c0e240c0f6000344001d81d0303090000100d502c0c0a0501034245040000c0d00310403c030014400808540440740c100b01ea40c484240c0b034154069107a00c1013070041a0086004042c070b800498007646c0f8000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 660690260 1250 660689010 660689059
    0x11090c21040312140a0c05091807090b070b06011b051506130509030702120709091b0801020901020604062c06010311030a031403040303021204050f2a0f030a02 70
    0x119850710012040352940c0300c0f040d10525010200c480503100005130020302c45401810040c1c00e43e040c0140b818508070045000b40d1034482103203030340c8102007040c491003e501202c890024162100c1060403e00c0e541d0321004da8900c0a45402c0c10408082c4440328400c1507150a00005503110088a4100c10b070381030603049a08088600c0c0e4801d42800c000e18584a41e40c2c01034602c50405032000d145015040e0b400c01031440c850000113040c0d44180400491148001e214804009004400044404154210105c0380104907004148240d0060084168503600001c40e03d0300581e228070049441005110543c3c1c140c14050b210000490114500c2c10007000040394150513280544441d1841c012000140742d558017448000900003142c9070078040707000170001d0203160002d11a29001d440d06d201a00e4160300102c00b61816201d03134101c1452066201000c220229900600021490303009011050340034030a41c0081c10a8007814403002d04444070f907401e11001501c83d0b0700801400d484107644006107519070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 660691510 1250 660690260 660690263
    0x80f1b0105090c0319030903050f01050105040b041a0d15090609050c010206132a03110109150903140102120f010609140a060e0a170307061811090c2104 67
    0x5181c4030118010800224038660b4020b0040e000b00944002c0c0308100e808000c0152041e02000700000000c00018014000520074085200000c14107504010410044485400005101d85c0c6041c0c0d41c0002040e0401d0030441554048a480c00f10792824241001001a42140f04498502d003601001c10440e80398840306d801405107007110418502040103a95503041650200070b1009070002903000500c001210500d13414000c1c07a40d00c1080f0621007804000c482c02e17041101d41c41c0b0040c00301e10b829680464004014414000360b401c4171700280b18050322403000b500020f0401070003041100e00d4210300f5011940420806a01c1d0820b516141503043c058400078062400040c43c01d400c0014000d00b0780400303030403501e0010009040e03d0300d014029aa006c60440c205a000034001030700003500954070b003410413540070340400741da50b4210f18a465421520b50350704a50a084030381c0e16900102e4800351503240340b80070940300f410882e02c4584440c0b50358000d00e0407081d21003043c3c1081c000d41441d503500c12401075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 660692760 1250 660691510 660691513
    0x6270e1302040b09101415070f0501060801092a060f1b0f06140f0613020d0b130c02120f04090203071404080c0a1403101a0301090c060801050d03020303070507080f1b 73
    0x29628a0104201d0540c441c85940f43d2200612248c03021940281c180115248100300000b642960b9000040c00d441889400f540d0340c0c4040742c82c81e1014503036034207945410070340b01c52200b104500f001c1c00a80159214215038040184441940004038211b440a103240340c1c00c85001f5418640c0c52a240c8003a00640100419000003100414033040c13101d00d50328040d10004042038865946401010002d4005844402015031510500d081c50b8842c50240094240700702c2000c2001e4002c1c0720040d01e44a9002c10a02e0000801c00048002c0360a02003640c0c2a40e1421202507600e40f0381d4101100d19924031142070031000c8000170002080c50b4001000b242548040d681d075082c807944ca140034018600c04800e03194041e040102c44c2803001311140c0c02501d40074000a10f41291001071400700342118150407086030203c074050b03400e028503600a2070311401804115001440e840007690000d4603400044c0c0700c40144103001c50088200702d800401d54164440c01c06a842d2946150f95084640001c40155000c86 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 660694010 1250 660692760 660692789
    0x50d11030603011415010c060f142202060403020d110a060203130605040e04060905030c010c020a140d0f050f190e0901090216030806120706270e1302040b0910 70
    0x5141081401d40c420303240804009010f4482d94019145d144d0515022123001e0b80d901340c0086014120303c06d10350100002154004149800e8241d68000a1480c208030b81507150314000c1d200694403d021101500e82c1a00c00131000700a030f107442c0e0300b0b62312800e00003079100562200c081030503a8000040d101025460b450703071184564070407043c1c48903c110701070b0250302c40d4003100003404683c00c0d81111518510070400c591800c0c1000b45001d0071151240051001a04408252402d100c4001115241c4640103005040c084581c48000b504003a03029080406004010441e1003481300d40c0b0040c0d51000d182900305031510718a80c100109400c81ca2103d0074810a10b402c008210f44e9018030a03644488100004400500f0039510141e070304031030040c15158014078a085900070280203101d0140280082e441c0e541d102000301c00ba50051146403191800c078034501d90804c0005d5000d50f09034980003200b40c41c004040c9500c03070022901a181403659690010040018410f00e07000d5609600111004080f00004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 660695260 1250 660694010 660694031
    0xd0204140a0f1803030b0102070305010c1d18040330050f1308040504090507050a0b040602071e120f020d030207180b0a060302160f06020d05060105190f050d1103060301 74
    0x80f202d02181c0340311014442c4800ca40001d00175808800d41c1c0d001401100c040035640d07036409007542c00707455262001a101200e5481c039038036500784004013040220750402c50043c24805001003110014000303410001e0381004100b40d2660304030503001c00c034110400529800201c072410409130100780c52000303c025182002400c118620b027170201e5403960080d40e103440c051400c1e040001619074100259020300642c440060595a01d10b03545000740b0400040b1500c0d14600400a410190b05900002d07010306440e401801400348031100d401034940d0038498440607079039820800b00c0c0700b90b442d034001e400c40060b401c0c0c90181500044c00804a074100b0b80c0012400598550301c505581c0710005041d04104021801d100490103600a000c1d4500e00c9000d9128800c09611100603e10465100381d031550b90004a00300b10f44403d024455000d0300c282046441d00440880c0d00b807945050242c03800c100101c200c1048031840c42003080740d55a2401700c1046c4807505085c0c065200b1036009452081c400e44c0307020100300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 660696510 1250 660695260 660695291
    0x41101080601171f0f030614040803011809050d081611070e13210207050406081f110d1509060605040b0a09031e0c0f051e0d0204140a 59
    0x184904010707507400c00031143c2d48005a4659101614000c102e0700e0b45010924104a40100c01e03000f00800ea404001c21495401c1a40031190090a01c1c08203024420402000c1002e05045a04403001207000302c1d298041c18000400524884100400d00c2c02451110580d07241d1080c069030080c41c1c10502c02c039400d440d5080c2912100e49801c2200c2203508400f8040200d030421203491a480080003400c4812050039689a464840c00100107041c103890ba20b0418035215070401400c0040e15043e5020092141881d20075a910f991383c41c1002c500c1b200304501c3d041e0b03400c800c0d00800095552655665295208020400041c01d00300c4078080d40100300d140e0000b041d154034024101154840e4654520b00390a1440408403a44a88518018020140e0000000820806400000101400300000c2010141ca41242001d003c1c0e4401c0c40917a516a0341407055948140c00e580b41068101260a9511075010101300138068840c0c000c1d60003071800b5022030002c4192041c0500c46d54070841e00f048100d01c081c0090 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 660697760 1250 660696510 660696527
    0x11404090c030b10080d1209051504080d0b0f1e0301110d0c0314060a05100c08040e16020115090c0c0606060203030613050915340906020a05121308070608041101 71
    0x6c40014000c0c80340050a08041d400000168021000e80c1c070401080020302412640588086520340000a5558020002803152202d00e040c200e0780701c3c0820004600255480079084c455410520b191510013005590951100c203140391036078110340c0c4a0034010080c00007030100c0d591140c046070030036288440600d0000324291241e60001d00000c28507041500b482030098140c0a80c2041c4601d2228007004120010b015100401920110103000d20f46240d150450700280c680380e1055a051200c80c42086074200761003c16900d04c0c4200150448030850125285400610090040c0d0b01d0b00401046559010005503c0794806544086031448010300c0401244e10407680c00a0b5031300b1444010f404c40701c01030403103a0001038030711091403003104c0c81e0b00780401500c03070410180a4112003c1340e84100e03500003c904004181c10f0014042c019980c0e1506c54942c1c0c40b510400a9416001801e58075401140468901501c2c10380708480005846044c060001c0c103050301c055448074083e080c414802d42c410f1600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 660699010 1250 660697760 660697783
    0xb041a09130207050f030706062d0b0903030409021b2103040b041a090a020901121104180b0108011406060c031207022802120c09011404090c030b1008 66
    0x42116882460020030094203c0034048450b40140c51155421801c100098400c85004072000103529280403100440160807560501c0c0d04490310340f81c50301542e1410407501c201c92100d1001513603400174100190540c030541c0c00800700c0300e2000c41c1040c21441c0d00300c8003c1c5c8100c0c0c86001c442000901e088e4040c030b07090040c803180303200342d10810000700000d04151140e90010b00c5191501038400c04005a0183c0b000c003245c40210a40c0210400030551502826441c01010f03403001140c1e515907191030391500c906140e107802e401240c5903080440e00000d11907103440c1d0150050b10407801561503030703070140c00703000b8194042d00c044500401040e00d61900e001207800d5040460025460020140d0407216031100040902c2e0650150142d001440ca448280e4400b0401005e168a20b4083c268410009101e92a0341111500d510040c00400c803602d8542915041d02c550220420b1031400070320010700174200c0d98000a0030320001c00800070800585c400824002c141c0c0c861808806134035044001e5440080445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 660700260 1250 660699010 660699019
    0x5061216110d050901020307080c060f011e030f0807061d0d0314010e18010e0708120702010c080d090614180d0207120c03020402070809210d0f030b04060b041a09 71
    0x1603140c00b81c0c080d000030b102134031060040e0303802c191103600d420015030444960400a600320404110401d0303242450070b4054aa40c61400c1a0b00d050760005041c07a8100e800020030915040c01c01c2818043c818058424581d485081848a12013588240d1603c56280c01440594815442c6403507003240a4001e031100c50303030341a030344100c00da2800320440f020260141c60b0401e054580d440c3c80c80740b46428001c50724a0315580000300401031600724a503107044041c001c043d040840a108110060b84d00c5408045c4039074100306070940703802c901440c41000380401040140304910b8182e59a00d800340d10380c103885c032442c02d5500381e014044682c11030580701c41c5003211001c01a00300b10303014003540341c0c1d500300014003d02401900c120b054a9601281c12a884444103480c207490100346140c5c072f880c003802c001c1c0002250380e010000f21911482103035900c0c00103001560600140f000c0642c0c4441c8170f5401402d94510090080c808a0ba03207100201c100c1e0f002c1c0c0682040403c1c005040642001d5507421240054000750 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 660701510 1250 660700260 660700273
    0x60e0c0d06242619020c1b012307021203160308071106040c090203090a0b010902121003030c030302090f1c02010809120301050f0a080a0b0108010c0f0e010e0301060506121611 77
    0x40d0f40e05a2030f000a1038000c14a5400d11081e50101d008111010306800910300014947c1c0c03500b0005461035900c1c4001d403151030f41004008030044c0d07280f0107540c40e1a40c160354001d11030100725142c5003140100707511100e190301c1c0c10f07202d40103040c0e004c00201d00803800b41d110050192540c81d400c513212102154080c112100750070003041003441e158000c41d8451840f0302954150040c81c1c2da6039103c20340030380c840d1f0380d2643c010400880101d00800c2c40c542200c85011800d080614503a0040c01e40117030f8503009401d041d8080f8003da80e40d25142e00346088a58000d250b05448403a52a03403640e19a020780013070b40003448010001e0840c00e0001814404882e5801d51384d81540e10700b80c10440c44514200001e43c00020080740000d040303800300000559144198511011036041c10722507400c49901c0c0d8540700401c0103031149000030a800490b4201420380c00e00e4134900a548000100f8050207055000c00d4022400080e00c28002224510b82030284440d5850400c80c43c0c0c411340c0031035031200c42e600c5202698100a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 660702760 1250 660701510 660701521
    0x8093c09062b140f0a02030613060f051905090c150702030f1207110f090601030b03430f060809010e030f0403050c0103060e0c0d062426 60
    0x3508941c40e103003079500c1c80c4500d40b00018038901c0c480500c01c0c01c803801d8100200b4050311540600403c841010303020f006090a42054001995500014082c0d4072492240c86c4c03940c09004840c0c00600f0100c030b40c80702c14400303405c01640803460071207011517240044e1b1414011409440c0085000e070125540140040440c60040703580d10401c0e4044141207a0521410312035014002c0d0901c100c00328901314610007900c6412508200000009100c00540b155140383d221408036524a540030f90888420701e80050f00310350f00300100345450480c22080c1c8080112400c5424010501e040c40c440900c234503840c0c441d100600209000504059003d842000c250b025828031040c0e12400506a00409202c00840e149800c054002e05640c4a108005034100001801f030090007001c11400c000e400c000c0c80c04000c118a40b0000444102e005480c41d00350286c000ba100203100ca0a40001c006000046024030000691000c034000140c3c0d0680e2500c081090702d0310202c0c5131403901c818030000485410818807240c0c1c41 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 660704010 1250 660702760 660702769
    0x60405010302250f02100906020601151106041b0f08060408090d0b04030206160f0206010b0d02070503040f08150112080714150406061505070602030408093c0906 71
    0x2075680d02880b901c401c0702d500000c0e40f850001d102118000c0040740c0b125803590050003651030080c10701c10140580e110341000300c1540090483d044880031801215080e0a0302c82c12169960741e040c4442c2a0301c2090140f00601005d403202c0610044200c004a0300165900000054030b05a8451000b09030030400c001400b107403500c00201000040149800c03076102d060307540e084460030144c0d81a0016032003074041001c04241e29050004043d606d0030a1032041c1c4820100a640c1d43c0140a210251100400c400a2503e02a01a2035400d03601400380e90300c4c0e50311800c150a005103248103050051080381c24086000b0040c0d149039060792100f1854500d002c044d0748415000b40e00100341100c107001e1050300d100b6480014840199050079100e03604180b403e040c10448240d4445130841418070300c0710210b9a0507940c0000448200b281d02c9600540c0741d42e60790411920034090350000d0f5400c0820149001c0300c0b801c40c008000c1d01d100e18841d01d510508600c4568240010074088102c0c0c01c40441c41c040b80c1c00307261 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 660705260 1250 660704010 660704017
    0x70507090b030f0a1509080301140913050c2e052215030203061306030f1109090a0b15191a04030f080d0605060a1101050c030f010e070504091107030f0905060405010302 74
    0x2c0e9003006c01c07103c1d80e69807211007641c4241d02081c40304100075604581c130714180c0c0502d0b4201902c0c40b04400369050648681e03403680452007c40b8881d14514200502034024040350060406c52102a10729280b82000d000e0042d9000e0700101d00030110190320070440075505801d07102034841c200f121088144800c2400d6000b0352018019070780c000d07071450704115000e0140c0110000342d48107110111480040703181103440034401ca0100c034030449414040050051002440c901c030356411100080c0161107261484034044030782d00000760052200140c0b80c1c01080600740240883e4603c0300010303651049110301c0c101c280118007004040c44c41009246001c0f6040002628204110b1000041c44603510000117080354811160440803a10644186038035000030300ca002d50100c440c41c04180b4502d05402d9001110005014070241c41e44003c3c04152114844e00c03d5401400c1d120f0000c00c0803400c1ea4100d80400c4c1c20803c0c4c200d0008a00c400d000070001e00c148007c40440740c0c02f5003003a060505000066020b0341 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 660706510 1250 660705260 660705293
    0x20f072907030309240e060f06040908090901030503032a19210b0a060c02060904091a010b040f080c010c0b061305130204060b0c1b010e0303070507090b030f0a 70
    0x1070302c6800d108041500c10317100303048a100e400c040200901e040003501082c5d034240c080501564000404200302c915040000b61341c031143c11103001884410503c0c0800701805100e20031a00208114000b0007040000001103002c0c40034a0100c0e1180301200010106152030342206080482040c00b4042c1c0c0d0040720a019103140003d0b0500d0700002c412000450340d103802c48141c500c51030fa180d91856186051920102c030281540740f070300c40310100998012600c00e1040785440d50103541e85440d00030a010101072340241c01c6c103c01c0c4640b0f06035659008101400c1d0018028400740c43c0703402d82c001a80b400b0020f1407040105044e12150b45100d103a03141c00d180503030010205134020050740d0407061031960621905110340c0ca8800c2d00d56a201c7c41e40140030440b0059040340118100c100140d048540c40003440c011913416003030003682c0180035440101d030781d80f810a5065405200200b254070821001080080586240b135004004003a020410140e455640d07001111076604141c0080010980000d0441020b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 660707760 1250 660706510 660706517
    0x6010f03080a21051504090f151103010602060f01060309020102060415020d092102150f28140c030c040608060a0807030507080709021306050703020c03030406020f07290703 76
    0x70005408030f001c3d200300e004400294141d94404004803e4040344031241642c074203076020080d82c41169283c120107580a24060041050048150a032001542040107210b000820843d180d594903103020703541d0007040e2148050303641b8050010a049210784604161140c0507801001643c0f90340e203030801c000c26a2541002019005c0050a000c81418003c0c40c4900e0704c18014a400a02c2c12015a41044146080e050854104032002c03d003150f0712000711500900307880c0750401c00e40c40700c40c00e13a465032010183c408000c41d010050030320403818640c800032801803140300c648480d0b40c2da081806100d100c11a040c56080c1c41c2480140b25241c4148407440e440040600b5000c9030640b594065454410380d0f90044526502201062000003414000c1c1801842c5024065047c020b40c42216062950a406802d080000126408040c14400c1150342840c04001c2c040c0d0b50340e0781d11620001c2d03ca0304404204c24452085020000780981d8240c0d00088002c800401c400880b05262103540c0c40b80d0100d4415801c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 660709010 1250 660707760 660707777
    0x123010e0a050a121b060f1103090a090905152e0506120103050f0d0903060c0203090a0305010b0f0906090703090f0602030c13050f130f110408030403050f06010f03080a 74
    0x45440e819080d0001c1c01c4e1644480c440c4140c3d81ca400e14040c2414529030340c86803000d0008105031900f10800d007900c0c4445040c42c85001c001409618594050340c8801544004195000540701c0c03010f6104c1520300d8001c00540e01580f1040c08041a455800d680d8807450003542101114016940190040d11100000d004540155607500046458001903c00d404c050040001001004400c02c841d0243e1115500680040206598081c0c042d0141e44000b421842d124200042d0051081c82142c1c00e820000b015121059102c2c20f080d402442c00c110100c0c020100c2800c01e40c40c40c5005c03007040744a46402015003541d640c0c0c0760412030141c1303c5400e003220f5094080320050f0004650780044c51242c0340400c00151a00002a645003c22403503a100d42d0240310504c070420526101c610110711040401c10300070070261300b807251110060280041c064076000c00401c3c0401d070080c020000b481102e0003003003103a60144018110607200c080078800c201c03228003a004100000380710740703002e0582600c2c41e0808a15 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 660710260 1250 660709010 660709019
    0x30509030c1f0824060d060801050a15050f0f04200708030906010f0803180a0807183615050703050712020a0e090a1119080123010e0a 59
    0x848070080799408005012000c0310b0540c1c55108010302c0c0e000d0540700c112180f006400c00d607464208000c004032801500e0000c0d62600801e00354104500034140b40c0020000b525012801e840240501ca00c40c1c0111039111000081da4903110402da80000c60091035400d0406244040000401400c040004018040310b100c03080410114040c0070400e004000c1e079507803440c09491f01402c011050b0000840048181014080d2003400400d94180c00c140c94514000b940c051000501000e6490380445c1240c03041080200d40e00a40c0482403c4c01c40603504103000c0c1011300c00c0203c0e0a180e4a650070448441c40441d2607150710000300300c0444c1e85000f0800203220200403000c4100340d80080350070001194580f410b100e03c007a813018840035152031010007181004403001c802885a10f10801c028850241c59021845800304d0b60f103e13003c0340100d0800e103030381c4201d083c1d4100c8031015208440004900c40400010740030024041e0300207007200a0030081b200120a500541c4c611800c10035854010a19280109 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 660711510 1250 660710260 660710269
    0xd021606020403030804062f030402190602010e0c0f0d03080a060b07060501082119020f06091f0603020a030210030b04060803190507020a0506520f030509030c 70
    0xf56000340d4541200345000d0401000340d548001035150303e280b0040581042c10100d0450601a03c2d44407091070340d9885900008000106644d640150b00000800000c1e855070150701100d244554281500d21952494040002c5081c907003820540100c1481c2c1c510002a100701185135001c0e505540009509484d030190402a40001c01c0865100383e0f20001801100020071030790180b80e030941950034200030b011b4880c220601441c0d4040c0c02c05000c11003a0b12100303000b446880b0f8140403a030115180c600d881c0c070042c1e030b48140c4400c1818103840c100b070407483c5041c141d0048206480c2c029003c100d8035450b540c24001c40d0a0410ba00e81c01f055603424890f1100d507214001c007002050120021074940103400b1401c00220514000c990900a04010000050710b848003a08121081201d0051b240d000d030000442038130f420117551181401c510041007404110b0b001401d00d2080d0005003140b0601507803500c042c0b0420888101030704071400402401d0000344220010500303c00017800741d41424a0503400309 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 660712760 1250 660711510 660711517
    0x1a010f1e03090209091603080c1e0a110102030f0717090d0309050306070314041103010e06010f030515040503180402090a1415030601080c0306240706061a0d02160602 73
    0xc8001036101c1c200d00095103000a40709400c0102da0014002201a0720140141c00b80280710041c04902d0105000d08055810702005011660001ca0407110b03040d50005551a5108001c086944014030000c0c4810340d440041640c062007007081d1650316080e03c0307884100d82c100125804000b0600200314142840d2035460302120b5580c03084c0c40d14042a0b04000030103043c541d000b046a41010702d000b0f40b00c08922307074810b00c1e1508280c001745203020340e243c101d0119001d0054802001120300c2543c0000480512070000e0500f10b034001c0c000c1d030b02d90030708140400402d07140a071000b0b080741d4030074000c40b50f00d500707460310b804031030003000b0030040c0760910b00e4000c5001010203a100c000000320081a003c0c041c184200c031681d0072440d48103038501e141f501000180003920050035100c01c4c1c0308080009022901c544540c1c0c01908604a0b180c000c10620420f0740509a20444086030303801c1c10704000059810364070084260400081501034102800003034400000e42100640b09041005038505a0105450b071008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 660714010 1250 660712760 660712817
    0x8120702210d080a05060a2709051501080604020904020915040e0309010e0604060504260a0b0412030b100c0c030b0c1b0c0a060e12120a020d031a010f 66
    0x58411102c4411010741401030007403242c5480c07410032040041590702c10500310706950115036455412044110350310704206408900c000403a01d03044038141840070001d142d1001d2040d80d0284003071680ca6029603074851800340c034002c0d00300700188003207401407410421440d80000410340d043c1103101800c0010b000c1c0c0d007401002c0c1029030400150f4810559100c4064040701d003055400e145480d1500e94003c0080c403517480340040071090145584001002c440d45c1c07990703001c1d50300100c940412007400c01c180d00050030b03941100c1710200390101001c2c0d180a8002c101810a004080d4242480003481c140c034203041c0c2200031540c00a8104002c000503c44107011401000c2c100d0b562070300c808403d042000c1d201b44549080c4856480011403801540d220a802001d540c940d00c0d182840c046103030041682c840e9a4454680c0c0ca00034548011880f202c058040c00e4031850725821030380d07080302d00202541190480620050400d0031841031800c1075001d13441121181815242c501010301d0b402440c0000010000325 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 660715260 1250 660714010 660714013
    0xc06020318010c05090109050d0b1506070c0b03060f09040b040605060d20011404080c0411090618090c0f0403020f06070b07270501020a02040b0f04090b100f0812070221 74
    0x44611703440d40d201e89010041c3c82c00f81e0b800401c04c207258460340c84c0400000c281072981040c44090703069545841c41a034101070b60000140d100740d0780399000d4100903041250a2406002e040c0b084003814582004418001c5401020408158130f41d0340740e240260100814a5822003841d20301c03100090b002f0b88124040d05038152100e600c135144403000604031202c0d0125009401e00c01d101c280440745000c611030301408000c9900141c14903c05004082d02c1c010285419407296005c1080c2003e103101440c080b045c03010484803260550f503034199003001801031030424284004140030500043c00c14007d0300d0814035000b012142409082c0d501c543c00c076241102c031040040c07a030240302a42d0402e030314401d4248014a20742d001003d030a15000135551035a498001c2e1045859062248840c6c80c2c94030b4940511074003070b10602c105440b50902441d001804c2d40d24170218220b107080019480300c50009030040e11305100c00713008040c0045000e0140ca4100600a0340c3c0318089150200c6040105210030081c80142030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 660716510 1250 660715260 660715267
    0x9090c060203031e100504020c011a040e0c0607110a121109162610080f0c0a03080714060f0601020607110d050a03060e01240504060c06020318010c05 66
    0x1410401116490340064107640c0300f03200744040303244003800d1100200d138080c80700c481c182c0c2ca201000900c94a01e520080d00f0502c0005c444814075419042110144581c0385003c01403a800801e1008503021100100c0040d0402c825089207840e0500007400c502c0e003d05440c0e501e01820305c1c0010b40b151900d50002044844a03842c0c842004040004052801d0381164104014036100d8030a156589020004404004c420300d0800e02d9003505654031701d000e500360300c0d22151914050140c5d5a4101c0c3d9405125503921641c003030301b010302000203000c039a01a8050100d0440394919610030182d50090301d001c5904103e110070000c81e2440400c0340754070846e1f00c03ca135100203061807000a410144042c0c060400c014203000721004003c000200e14885a101d458000c1e690221007038120010541c2e5005004440350010000406031020360500e95046000c1d6850340058240c0502964079100320b20520000c24681c6000d00082030f95075010b180d0124080114020b0b40b0500e40d01d2170700b19410040628082480403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 660717760 1250 660716510 660716513
    0x105040c0b03040b01060e0409051b1305010b042c240301020307080105270c0a03111219060b0a0c12020d020c09042901030303150323160909 62
    0x100800340c02088640525895824280c544181800c414060344c0b00b44076003012001d0300d03074403158402407809030881c1c1a01c2c00e500b402400301015058204105108140c82c00000d640700c08075204a60484000b036140914103171800603089160b85071180072905003039001003104110300510350407070720a040c0194640305104080840c02d0320569941c0200380a43c2c810310421040e50340100c6041d0540d4000c44080300e5260000d05031840a008001c641c2501c0403010b414402007045603c040c18888585440c148262111500d240f0b419000780240d101c20ba40d0503401044a00324032072610140007009600101d119030703c07100103040d0741e400710b203005000603048403400b0300348131440d07208941c0c240071032003d4001c03c95070000c004d50b034080c02440301d4440d003102004101000640d0700780d841c2510710b504407240780c200c080c0f0315000700755000d10064001c2420544042c0b080c0280c024414180c03588103042100c00005d80d2004403403001d040d44007866521400b4460504068503010110081400e50700c0441c0f5850103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 660719010 1250 660717760 660717773
    0x3020c07140114040b04050a210303050402121f0b030115120c151101060602120a08060d020907050c1903050f180406090c020708030a0e10030f0c17070c1709010917010504 75
    0x650144c40352160800b091b50200c4010780349e60003070f00d07050b160118464031140001040130104074030300d100c3e91060800c1a05c5920081008189104d02418100440c000c920185802d85074850552804120303594014003c0000900402003200d01031840c01c00240c1e00c0343c94240752209142048404144076254140080c030303003402850050300e4984003030304241540d03004488041c0076101c84201440346c400c2c0014000d444600d0450001c030b400a08940d09424240701c00b48c240c1d0311040d42900c03240505080c43da103d20728101841d54990b41035a4880c5000f40510800d40160002807800100c2070000c81e00400f240ea0300d008203800380007071a1000a0600c21210042d10b860500c0e4449401a0018080804040c0d00007924140c03075034040e50000d001089000c1d044004100c0c0703a0908030141c1c680b20319018a01d070b01c00c3c88509a5207032254410456100c0c050700303940e207800c4500000d11003140740c0b0541e6108240600580800001030508a5220340c540303017481c014010f54914000d19039512400c20061252 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 660720260 1250 660719010 660719029
    0x6040b0411040c02070504020d02090603011d10081e0a020d051c031b0c03090306020a0c06050a021612090b0430081e0403080d0b0a0603020c07140114040b0405 70
    0x480b010000d070012a030003c0c0d16400e9512449104980c007040745800300c4540e40485030126002050f20703a40750b868541d090100c01d8a00041d0024101c1c800c0025910303004a4000815699400020303c505c46046080f580181c51140222225000e070503007074030041c2c5560803d2044244513101908010042c2031004c0791141c0c084480508241c1803481d01221f01c0341d003902591045d1582d15224418007190308054400308010350004207018400145143c045034172001801d27525109075000d10541d107030070801400780c1c0074130341e18400740132005280f110014000c100c22605940c503038140500219030fa10000d00454200703074400c00d01696040e00f6149040100c441c411000c0c01c40d182c0da50413200842c3c0b07400b107860260802c2c15400142c400d0905941c20302c040c095800440c0e1200c1c0c03032a580d612050650b40900760312450b181c06072401c003134041110b034000d00917101c004079400c005210071450114803000c070400e452140ca0500c485180201c1c0498004d900810152080070540ca950341d140c0320900c2400907 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 660721510 1250 660720260 660720293
    0xf0a02010f03180f060e0304090b0f040c08060909011104090203190e061311060a030c0201140105060d050606071403030103050f0a2a080f16050609210a020306040b04 73
    0x601e0141c0f40c0040103003c0500c019015003003102100ca540c99803802c20028a030610b590425880702160004900a00b600300b1811014155034030010604484144816078001c0951440130481800001c5c140307082035140795501c400b5110021402100380341c05104c007603000b5048001095000400c1010000b5002e41d0344114544c205800c2140d113840310750586d11060080c182055002c02405103505029503403001c1422001e00405a035614101c41d500580200710300c3c181c0714055420006220301c84484851140c3c100c9001034401071500c00c3d1510000000c050081696500010a0190b44041102c00705c0345156000710b40005c0d6a29411410114582460b008a01820754440201c41c0c00140e07400e0b0074841c000911404000076141410700c2551001c98a0b00a1641c0f4407031452051441e49001600780b090794502c011860303d06454005100d501c1c0b288645981d0018680040388401d1108960075560704810001030f0b80b182c002c0c5a001909120382580c00b51651500ca006000600c05c43c80400170007030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 660722760 1250 660721510 660721517
    0x1211041403030c0304061103041a04030302010c08150409150903080402090a0225060902181801020f0901050a020718050610021501030605100b0f030f07050a08040605180f0a02010f 79
    0x44401c4042c44e52440b0b54082c0000300003101064804200c404c0080d40e000d0404036101102e182c903032410020311600180320540041d030034034000708070320b90080c1111070080e0100b03800d444032010381303109010203080c4509080351070700090f98001030394440d584282c4000303501c665107611403410b050040181024000e4490350403a441000781e2001c001d5501d0b071312040c22030340179021514524141401401800031000103500800000001684020b500440d5403140c40100043c11240c40d02c002c20500f02c2c05a0f8068044e0b2072800c2082d1525580284080c0040300c84500c11606800d40307600303802d0186d9110401d01f000f41d81d00e840600c13000749400e4400b050600c5403403009241d12003070f0300c511190014040c8405880d250340c03280841d00d03d088815030b1501034420900340c00d9403401440243c1c0c07030a0b481259400c0c0c00f000048081a480f5104a0459002840c103980b40c1e20700e134a0b02d49074a8001c0c034020700718400c00c0c82511000306031907900344100320002e10030340c000e0007100c0781c0c40c00050010180108a80b040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 660724010 1250 660722760 660722767
    0x318060309060a090c0e040b060a0f0605030a0f2715020a0503040f0521130807030221030412030216140d060e01091b080d030c0915121104140303 64
    0x505800500b82d9800003100703402207010035040c1441407107074200d40c1102803880400c81c01c1105000452000b54010401654031003010740e500c0720300c81003580c19801072034001001007012902c0b8800075044011101c29010b400070f03080b5001240c52900c0f40311000004c1c5041c90070034000043c031540d404c90b0346031001c0f58001903240039060003004000f072200820040000603900640028040104896400b14580c41101c6c0d00b150441c1c00b25079295042549140a20f045080001c10100404200642242e0b0701403c8140c01501d07556525241b90401080c5510610050000085d5221880004086030340650080c11007050810342c020340d0401d00760040b030520440d400031484a9101c05128640e415044400050461140b807807107409802c000348090200304100c01514650b10b44070706c0c03107011200e5100c01c445141c00402c60a80940300240620000304035805010070080e0004442140300000500d020b4014243c0110300d82e08841d400440001d0420340803030248069461541201101c0b1400c40040d0308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 660725260 1250 660724010 660724021
    0x3050a0b010b131712031e0a110703050703140a0503041e0302030901110c180609070224060f09040501051f0f051908100506010311070201020d0809030d0e03180603 72
    0x40340014420743c41c8a2540d43c0214000c54000d0000c2490320322070f800111b03560f041c0590500000b0250341d2004126100300f1010420ba19100c3c46002590120300f490181016140c0d06c05644c19000b001c0140c3c2030000091440a0301d0b005e4000901001080e40c94050326424142030449501d80c0960030440d24131041034400c4c0100b6000030030380340010024600302d08030300a401c40306400e00b003006540c1d03500601005080801e00300c2c05a403180c0300d00c4003560005415550088203c2e9035404480d006803034071100104080301c2d1a040c2809a0780982e0203080802c1044188010034031030541120180d074079075503ca060158656038550400400c68240461000903400c284032000002e456225a600c514452020360030903e1078240c41e1002419074100b07031140140000b0703030b090180504a50ba580040d00d4a207030011104550820346840d00d40607030051022507804071003910f02c0b000160900906100170300c5042c0a14050f40158810b108040000e15110043c2e0000610012500c0b4442441071205100b00507 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 660726510 1250 660725260 660725287
    0x50102010e060429040c0302180c07080a0509210d050a080c0d0905070605090414040f0b0405030d0e01060e090a150510030611070b100f05040506041503050a0b010b 72
    0x6410507080450855041c0a82c900200c82d5002a0134030396001c01c03130000f04401c1c403904407411011a40280c40e0000325480340105100c01e4001100c049013030840900000012824a001504a0701940c0c03c22614041009000800040d18150a0032401003e801c22070404001400b020b4035261480c11b0140c10480c1d0f1210243c400c000060503260092404a60031400310300c07640044408640110a031200542c9036000200982c1c007001240d070190b81003460301113025610b100c82c01d214a8001c455071007161417a603110303d00d00c140640b055030319100511104000b41958480c2c800210740d00c1c000016503e00d441140500748800400061203508116030440c0402d1141070001c0c0c4024402000254598400850800150294001408442c074043c24007210707070504d000401341c990086041451a680300402a0050101d600072490303421440d038401c2000703040541266170444402070010540000752445000096059402031304c00f607200f8524003045c00201102180541190b00c680c601d040010300310300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 660727760 1250 660726510 660726523
    0xc030f06020904140c0a1b0803131a131e081903140408090d2907271404060302060f091302040312050901021509030408010f0213031119120c050102010e 67
    0x184a48101c4428801c40087c501080d203e611105a0340c0703078100700c00c0c3c588002203428000c441240e0002d107003002849110403170510610b15646031501c03070000c0e60340d41c85007001c542e2903504104052204130000a4070010103044032003a4007418280031104013500400b0340c1d21842a84000075007801c00d100100f651942100c0c1416401d0380d60003c1d480103494500e21803a08404c0c040e22180d40892030b0900d01c003540c02c61500804a03aa101c03454804a0f110442d00c10034210440d107414490000200845007150742940c03088800140000b50042d80d98012072a0f503840100c1c1601103020008120405190060001d00d07003840e00c410441c10581542d44410012455980c03001c14410081000c0e4841d03882000840110b904003908118141040b01c6229500d4225000d54203c950034100b003425005500d00c05d82d1528095070040c0c604480c03650311085400c140340c40c03041c0c2c1c008074030b48040790041e8040b00119004003d07190658095440d00c1c104407a040c0c0050304540d0443e41081c81d040703014800003504 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 660729010 1250 660727760 660727777
    0x301050603040807060e0106171f271109130804061b0212010b0a05010c05101805060708011a12072111220503070b070c030f06020904140c 61
    0x1026030380d44403800c20611074010810010109420b0021404000e80f06400280840f86440700f01c8a50340c8406001c2521400d401c0100d4104140c24182a030030044d01e50450110720344094141154610716440c030f00d4051b40300c807406a415021050b2090533a0410b880d6081c0c2c080040b02609075229056540c641040c80f03507200b514104089a241055100c071001004500141d0080030410100240301c3e201d400307040a010b040d4450f0f1000000059194068100480c000f0703030004c040e000001e004941c41d00142000001401007824401c0e00b80700144082045a010b0601a01e84c01003030f42c58003040940c5070000c50381c20080b1500c03e0001360001018030388441d13007008480c107111304643c100300388508074500340c0000a05201d040100700c5400218200042000403103804001c201c50300c0d555800c0c03103084081c4c0700e40350f05a40303c00c5041083d056040d014100712031040c00401ca22591703075143d6108540f68045c0541d4181d0340000c045910785464442c060000a80010500c46443c2407007002c1d805010380b524 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 660730260 1250 660729010 660729019
    0x10060507080d1104140406080c060901030504050a050d080f06010309030903111f030605031c02061909120f02010b0f010801061407050a030206071206030f0f081216020120030105 78
    0x4510324405070a40042504103c03407103519441c0d40e51001c0369907120020040050107035250010100741046c011a03803d07107c010140030f107441d2908030700c011001440c0040c0291414040c1915a40020b02d0902244904109a903141d51490800800e50040709402401050515142041d03c00000743c0002803a42200c0e04048954442c51022000c0703a40070303524801240c040d03002055a200c03403d41651207501a00c0044d011503000c1115100303080c0d400c402e014a00703005a4080000140388525600a10400000750f060220380400c16a81e480e5215582a68003c04990003210034100c0542c24420380c0003010f022100a40b28130b94010020346608c07418002c0404205c41d603000c3c4483d905240c02155205075000048940d40c26250030002e444540a03148040000c0540d8040b0060b4500b60040c0030999410088040e00340c60340365190a0301c0f035a001d80c1184c0c14501400a0801d49040540f1140700303401107404000c0c0d203104114001d08403505c103803d10b090030000c40590521358005106880c1035900030f8a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 660731510 1250 660730260 660730267
    0x20d080f19110c1e0d09030803010510141801110102120a0216051005010302010905030609060c070f02090711010e1b0f032802270f0426040e1006050708 67
    0x12101001445030f2140d00c040ea102e540420480348851030040b50814072840140d440904980e042183c85009a00c4044d10182040c0014801c40c03802d00501c0f8039105e00b50034541d1621241c20721100340e42e0081d1030b0090f10307100c1600d80d909943d60400c10608818480d840218a000841254034485110203407088061681c0460300c507200d014848401001103810504a9406017060518107014140c03d00007240001d5150200080c40d050000301c207070091000034061310f030300ea0f02d0501c100a15045a101640c505940040401c05a211801203038000c071401d0751400d40c10075216101c0345c29100c8043e00d0400d181c3c031008840d01c0d88802c64000c1e03d01d5400c00c42d403441442003c04000703894004141c2c283c201e08500903170f0011132a4185c00c100071806100342c42c041d04000e000418444092004c05200c0003440c59080081c000e02c24840308107034404d1040b410000c1ca0408218104401d240c01ca042d0401810001002c0c00403c201810040d403103580900320000303060405800621a006038940285146c0340070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 660732760 1250 660731510 660731531
    0x617030711010e0a03081e040f0308030630061501091e0b030112030f020d2a05010c030e0601050a080a12030f050c0417010501050a120201140703020d080f19 69
    0x54004111010000b0844010145c5038200a8820383c080c40d20403c02d0208042c0d5081800681c8081c0c900b00c0d412001c103403a5007403640d19446555407008000d1a88810740c00d1a01540d800c16911070440c03052600b1001d40c000d03a0b904500351402501400e150075100d00d54940b691960783c41510034007590b1003041c4089203a80d5100e0413640388600354022181c0790f28040000305079115002c08258030b4500a59640d604000002c7e02a61540c0c0b8001d20340000500350390f082c0c918041c0e000e2804021240031622041c201240342c44003800c56090b002508000f0780c50b0203000544070006c00c0441c0c007411040314031202d141c0c5402c151039511aa40040101360500007084044031a000c0d030702c18842010320910501a81c07074011101d00b0030394054000c0c1e41c10f01102c0300e07200f2211901449400c0c16200080d243c0c4400c0c0b8280a031404410205010803410003912584081c00c00c40950050007240d40f0a4000b071002c840c4210300906852001004840c205041c04200b04404000d883e000d0304203081c2042c0010040d000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 660734010 1250 660732760 660732767
    0xa0803042105060405013e070503090901060e011205100608060325030c230112020f1c0501050111060703050a1b02070305010b0a0308090609041e0f061703071101 71
    0x2056020303140303000f40400c0005020301904104080d03104c2e00340041ca190156480001481c10f8040d441c0c550440c0007100c41c1d0300040c03501c0140403880c080c02c1100d081215403c0060403c110903040300d4000b90300c06010f17075069600f042307202142c0310015205000f01d02d403000128000c00c1d89441200c040180c144049001500d0500524896003443c84045004602601006c40480d0030780c802102c0702200ca640000700c00094a40c00320200040c2603031b20030403907404001103031100d10165000300740d10703820400c001302011600010b0202c4001c00c410138440d68a030103201c03c03c403401640800d0502c1401c0160303000324800401e40d540e21400c0d03070500040316240d0b04000d20080c480e11408804540811041d081e0880d00001d600c802c03607211354028410281414140000301405201c018101001030040214510341040648052035014100044110b142d001014100c40400c0c601e501c1540c0d915142d80000e0494000d00c4090165034054865041380b548003240e9a10601801030001c4161b4159468260f20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 660735260 1250 660734010 660734069
    0xe1603060803040603140c030103030206040f0c0b16050705010c0c060503040c12031701080c01051e0904051905070e0a050d03090e160306080c030d0f02030408120403060b0a080304 79
    0x28482200c1c3c44545506019006007050a489040c4c0442c4400141c4485c24000c02c41e13050701d5150b805403500e5196650303520800030030301c0307070031500b16102c01400304056102d00f02408407150359074403100c1d41d503205003085820302030b01d600801c1c1001440c88003040450600036401c403ca44483c03800302c0c0e581d66541840142c05407290441d01280007100c3c01d04040c140c0c04581c0c440843c0002d507250203140da8030400156181f01d10715007603001c1081403000c481c511055510407144000a49000c40c6401140c1d03002804540040718003000112100002c810b64404901c01c0c1e42e44401e841c1007524415048200207902a0410703c241440743e0b40c8442c100c804c043c40f40300048001d00c25035048003650305261540c070b401c0a42c00a01240064504600054541c0340000c140b07900350005400b61103d021500004c840140950081000390b1008110000ba0141d042269a200c8140720100d1920b031401c626004c1309850f221055980b060700340c20341c240700c90300300441191b089601c0d5050901c042540c0046d20b0b4400e29 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 660736510 1250 660735260 660735269
    0x403080a08042a0e0f04051e0a06051312050c0307020618130f0b01090e0a052716050906030d030e010b040f0f0b010c0812070903060509070f08070e160306 68
    0x200001c0c00c26030700c0b1807407501d100c00b66000c40c1036800441d071710900c06618541d4200c402030200d80c085005519040341c0711080302440700044040c0c8900244640345c0380309440042d40c6592141c540c4185440c28080b607000400e0804110740303049803034003d140c0f90741e503540c3c0501100030b4030594001034000e282184101004040d00c40242c8104130040c481c4044000605255622012260400018161641c030032080c1009840888410b200c5603240c100d4414010a4010212070304a048855003840c0e1852400e044c03030050000c000104402000d00316082d10b094455401607010780e40003c02c4c0290799501065110420545290010326038005560301d07030262025109070307a00310745080d00403d1507a41f181c00c10700717040708515005d200c8889030000445500114002c09807087e4002e0002c64071000c035112400360440c0107840d103c54007984986440c03044030005ea404d074941da40011810440c00c0c4441b250300c40140f0000b405000c4547c81c00f4601c08002c0340c01494800e07030b0760305074900c150401e009900250242 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 660737760 1250 660736510 660736553
    0xe010507020106030314070206030103170408030d0c030f0506030d030c020c06040305071d042301061805160905130b0a15050c011503240b09100f0801020403080a0804 73
    0x500344840042d0003401c050000b540000d080704450203108807a681190445a40903044074030f56841c58485090500c181c1c0c1c0a11601001008000350044041000e40050141c01000140031035200c03401900f120541111101e500f4148010010030b581c010600d0b1312028414100031410081040d800c074108090414840c1e4858001710380403040c000005003040075a640c0407810f0178050f00d107a01e0303c0e14084c421180204100c02400702c06100d54040c030a8480d20b440c2410001c150316885150309403c01030524004844131342e6403010441d40c512144415142d0007001c0c1888104507041c41c01003407104089030f50340490992244011011501c2d42d040200c001c100101501d0318070b04980400801075400f90318180565070801400c41000e090034004101200c0d4000340c52219030755541200c0e946450036403000020165036038405104c0e42c95803101540b01e84040104856681c0c10100d40713801601e401d8011301c1d4035a00c1404180001004a0103e444c0c0a1460525580d140e03034903c1c2c01e510505900d8008241f0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 660739010 1250 660737760 660737771
    0xc0806120709050c2a030301030318030c060c0b100e130201090b040608010f09020a09060f0302072102100b13050603030d1103010501110d0e130f0e0a05060c0412020907030e01 77
    0x95104c81c1d030244c4840c0d1600389140d1454002100c1925002444c500c550720140c101b00b0042000a000f43c1240c080482c40c0c40d100300481e41d894031030841003000390b80f2105c08a2203c0540b48100030751304084607405401e500d000700485042445a0100305401454408501181d410040035a80186040d170018070b1081015aa1281c0751800105007200071321404480415030840412403030100d00a8424440195940d4404949420340485481c02050718960902d5400c2140d14046040c08445002d02818103ca841030042c840b03800910744004102500d070b280345415a0301e07001b80e031440ca1105110b803201c44003044a8983c107000030b0071403003a81c42c210040703072901900b1140045400e0295040311007d032105010444103800040e11b4100d8004507000262540030807000614110745400f00e0403058003800910080c1c4845007908555400707004040540c44900402d042080821031558850f50441006007020b1904003000401c1041c0c3e00700134411602c0e40005803529200f80d00051300044102c009009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 660740260 1250 660739010 660739021
    0x309060304061406031f092a24080a0207030918050405011a033a03091211120c1216030e0a14061303050f070f090c080612070905 57
    0xf4280c43c0d59000718018070700300140352840d0200e00080310b80c800c0341c4950100440408000c00400c6d95840440345000a50710150340e20641c1e488549181c02030340a000700c220f0408502c00000041243c0d009207501c428441106e08550140100c2d4000c1c04021001d6100c0c0b100d86404c0c1c60b402c00c950021030409509480308040010590455401540120000c2004031504400003c1001e81d510480741c00d5800404032000f80c8112400d550014000c0d4a5118400c0e144441c0d41c01051444110301c0001a0f11382e245182030240542c0003110305805400c1441c0034915148810b516012060401072404101003916103080100f80042c0f442c80d404a0141da68520b0b0101480808904c4e10505800092164008010a04007560600f083e2164801522000c0041d1420000190f02103d01741c040003500706400000a0300c10040e41c0c0f40c2445004c040e0400904100800f60f1580382a8003190b00d42d400e00d400d02c5075258100741d4168024405680c00b00710046101c19080c90200c0e150b2080c10524038020410a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 660741510 1250 660740260 660740273
    0xb040b0d0b030a30050304030512070c050607090609080a02100507050a08030a090b06040b1c030905060c0d020f12030f130c17010c18050118080111091503070905120309060304 77
    0x83c01103031880d604113a030560750a08450b0380c0800c84008011034010007404048045081d2000d6200c00b86292400380400140c0e680c1c0e040a0f4195500008a00c0b500000c1c40450380084030327107010381038074802845504845d03000900c410b00100c0304141803080004400c0203000c3c043c803607101480e030001443c40c0e030b07170602c03500f400c0081806034403c0d00e5a0003208081800d6240c14020a200036900404a5403091001d92643c054640c0c40807003102440400c1000107026103444011700b000d415130300d000e06000401d65a002e420204402c3c00006545c2100346581c40300b074564000c0c1c035008a01100d40050b15914524100502c8202c20006054120194000a0044800302c40110f9131108070000740301000140c94113403040c1d04041c6e60411b50f0114200300340301d5940b00d0301c40d803c0d24003460409450401da403000903500b116950f50340b003070400000040b64101c9086c121108850304450310501c2e451441c0c10f42008103001c80b24010a8803c2990a1a02c02406000c00c19207002050080103684d480c201481c01c0e8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 660742760 1250 660741510 660741563
    0x120309190c05090109020a0c0602090604081507090608040b0c0a030e0102072604080a0602030703270c060f0806010810090e06060405090102030c1207020114090c0a0b040b0d0b030a 79
    0x540c410070088002003203c43d0745000b51418a0495210030348c1c0c0d0325041d5280c4d030194002e000d030150040c106220000c3c9030f40d010081d003080302e01e0495421003a8108580c4c001c3c0708110380c1e0022414054a1002d100008000b108240d030b106848440d540d440303541410089001d0208204400c50540c008a422003d00c030603040700b101280721409414810b81403149280442c0d02461140d80b0003a000003400c0c00c0400c0058004561103111450002442c640088a001150b0640740e00034044040b00f100030700401a141d14088003510007420318060240c84604000c0c003004008100904000c0301601250320505905032220203010454418051104013481d51545c90f4012a01c0742e20442c20039010550804043c0f0840340581c00c03818905140c00e619120020502802030080c400b15940d55411404441d601e480460185103104044d000300c0c0c0c030301f10801c00c490f400d41c3c005000c150030410040004806113012110b00000da6007000c145000700500103030804640031000f1b0049140c8841c0a50340041d10b050b007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 660744010 1250 660742760 660742769
    0x60d290703290f091e0103120e040203130f021201020c010f0f061508072c030607030e1906091709010f02030408070315150902030907080f120309190c 66
    0x44100100d02c08010700340d40c0d04001c1001d8214030020b0080b1028140980966401114601caa4620741281a034448641409910039240d0510341d00e113901c41c260340b040f00020443c000311415411400c0652043c18008101c440040030300d141c50f08c08004549030034101806079203140008640342c4894501040c0603182a804987c1c3c028a010b1004400d80214801c0c5415211002d20341d11600715040415621000054109000d004038030255400003400d03c0d00c203403891800e015101c003000c849902407520f000c1e400380c0410241030401480e200b24450000d01001e451183d907902e51403017829410868014254180090481e40b0f034094030340d200314008401031805040a80c0e4041030f050451f1022030702e0f8007c0d0701401c40381c0d411465040011a10840d6669520300000c00e00061140703130340e00444071040145d401041c45607004070030415201414048400140800d8000e0119016114081070b101d00d078404800c0741c0c9510110115880003c1000b40300d6411551070f4403c002c0407114240400c7e9001c0d0ba204 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 660745260 1250 660744010 660744041
    0xd050c1f0908121b0703050d090e06042906090405100608061e0f0a230112150b0304060b1008240d031103091008011d060d290703 57
    0x40003a1008001880380360783d40352070306981d040c8201da8100243c0c550041d4160030070340c40f44100c003001241007400020000c0e120f0752141403040303191680c1e24452040c010145032080c5c1ca131141c040c41d00b12000032540310407501d240c00c1c8a040604240094020701460480d05d0304145000c04029140100b4400d080076035816840e00040b0f40c1d0341700100701c0015070202c412640240300d84110040343c100741400a059101c0107141c104082e07200d42c3c00030458481c0507082e0241c80381e6083c0e40c5c030f4196000540e4083e4000040414001140712060792030000d90345204240c24047e0010014003400000d074801c0c01c1d80300000305074007290400b4400050200c40243d4001c804aa5860b12003034091800307118a81c0070344000703410402d00d81544c2c0c805440c00081c0d440c0724003240c08100111215951055070f141210120344d2682e201950612428200e0340c0b00d42c08c3c01503061143d0b4014880c0c5683c030106040d5015034000010300c0c0564041004414030786900420440c280704540030300c40b03140d406800007840c41003003e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 660746510 1250 660745260 660745277
    0xc021213030b1b160c1d160318020603220b091015050607230f100c0903080d020d06060815030a0308010506070c05060a090513020702010e0d050c1f 65
    0x34800c41054040c00441c10440300200310203140103c400a412516a014143c3c0342c501a0b0784640008801d0306d4980c01e1845500b00c5000c01400040c070414206204410385410040070f0652590128036040220000e4070504011002400d407040307003081c00300101001814000740800d40e24045012540a543c60380c998003030206052040c1200c6d12a408003035420028041c5400d01d45400e1144585c01410280c03600342d4202503901c0701e41d04607607000e001c00c00c040340100a407185510009050200104c40910841d0500181c400c90a130f0240c000c4060320f402000305541e414030321221200900c42d80012203001c07803d00000140741030300130074920320601d41112010007a90f1242c1c101511b414611030001d010841030b100500a5060030406000a584546140d0044948400000d440303504000303c84030020300f800e18103001500b001038111103100d030010025810801e83d940040d00d114554003d40340203072086c2240c207043c0501003041080035074010f0b01001070301d49000160399a90700100740080c049034116 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 660747760 1250 660746510 660746521
    0xb04050315100302060705150403020f07060801180c18080a152d020423040c051606020f040504050f010801050603030a0c06150b0409021206120a03030c021213030b 72
    0x107000c051040c07140b101c221a01609650800c0480e4201d0002601c03148192000e01ea0050b07001c0d010180654002d8000300b441c81440c8041c2460300045070042000c1080308401000801e0070f44403004500d642c1c43c1d101141000401c2c0d001c594080035038541540c108103582e400242079001148090310709000307005c128080081c2880705d209685004090300b607120f403007291a4034241c034851480d041c1c00c3c14031240546030682e82c4007019040c0c2c1c00c0f5412413200601c803c1c4030f540c02d4a0710303125148420740d07141016414011045c5541c5a0300302d4130240904055000600300206851550803907003d010008d00c100210308211480100b200b100b4029241250718101c08941649800000e1383c0718001c042c1c0d10606080c81641d10b140113816241e10034a6499100780300496400003060142025142000e001600d914203240c080841c010060103850140040703800c0f146100030040748241205406040100b100b1161800c120b142c000e64500390b04e503228006c50a010340f030351385a136144204c1e406450101246c0d01e50 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 660749010 1250 660747760 660747793
    0xb0f092b08250804020f0301020c070e060916050c0709020a0807020106050303030c04060e130e100f05060604030210090801050712201210081c08090a0305030106050904060f0b040503 80
    0xc81d182201d440c01946041a0b501e00c1162080d90051014001e09640300b402c40c08242aa00200c51704881e03034005960501c890f00900181c903900250440f085140c07800e050410009050312221400c0420000040f812104441000580020700426408554030342c5007c000a01308507040d03640c00c0c019420030713100007940d207000001d503805901080f2206c0e240034500903042e500303c11200d01e01c580010400d0201c2458244610800c40ca122050026208200c440007440040790200641f44c501545084c040c0f10041e00d40030140c1d070a49a040e140f6080c034483d24441a91280525400b113462982440208250180c5c40070721600788031407034201481101405150001d92641c07e08280c1400c000900492403c09007100101d074200e0038803101c9078100d5417150070250a03c49115040004890307000b800f402c41030352281400754040a40f03405080c011b400780d9401011440b041c4a507100700440428406500e0707031141c1c0503900400e102601800056a1082c0c20344054200b4800e540c40b0340103082c800c0044012 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 660750260 1250 660749010 660749041
    0xb100e01021006060f11010e03040902030118061413020c0106140a09021207052b02030105090a02120408030a06120f0302150702150c0904090c050f010203070b0f092b08 74
    0x138503803184224194079070b901b00c3c3d000d0f403040e001511564175503240c008040818001400503041da100050b80d039605150300c1c6608400303455001c050061504408200090742e801900c000c001013281c000c072a9a014002e01d0029000303501e0940030035440c051000030b41110040b42602000015118540341e80e5075041d10344102d004005000a440a503a0006a40b4521640062100e84403802107403058150310808918406282801c4961143c0d0020050010341380440c0159404040320509520f448040106404000405400140192400300c0403c02e52800c5820010142000e40c2d4004000511802c0c000d0154400c0740b41500540203281006e41002c0e056059a44034000540060104410107540c0c040d0124006144409008090018801759502e500036801341303e025202030031081d07003490100803603151612022030640d0b00c100301700c0d0009002507a07010381c402e9000503000e0701036a584008a00303042042458455014001018020201240c1d01e44d05800c80c003507841c3e602c550b8580343c0340501080e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 660751510 1250 660750260 660750269
    0x6070309020a15230a091a0c031318061412010609140a0e0a12050f09060307050904060803042607090c020601030302061006080a0e16080d2a150b100e01021006 70
    0x6010b40c03070501504042d48400968141e4107d100b901c0c129a503400d480c25034102042c40030f03103d0103011041100800d40002c062945600300020080d2030716007400c100c03444401164041c00764104604d0071403120401e42c001001401c0d40308050101c0c031010151090718410495000160070300c1c00d201b90002680000d500c0d4861a403108960480207104d100c113459541000b0a0203010110800c503410740c13620790f000a18003415864a540d0341702c407422403c10041c2e61564001c00907580c1305000401c104002480c03581c00520301c501c00105d20450300d02513503007080100e800001d0400e041640d50404640c2c005110b0f41200e00070760913101140c9481054207240f02d0184254400030340004042030590903254000d04004180d07130220784240b10420018030040b00a40c4c89814143c0100e0308002c00caa4100010890400038044d01451003202c0769006800f0030803031324003c0c003204a60400528030300507503071110007000c0000b072402c000e084078803100030030750704420390490300600900c0c0103402046080e004400590f1b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 660752760 1250 660751510 660751517
    0x10b030d0513050a0b04092003060d050316080421050a02060901170a1b0203040b070308060d06020f07030f08040c030311031c02130501090806070309020a15230a 71
    0x8a445050880e1150072103208610301c0216440009250b50755281810010500080401e0b2207510380540201240c254142c0800075031a84600444030b031180302304880d40701204862040d801895828124518024080e554031b95090440180d400d0141240140003201d56005c500c0c4014281051000600341c08164000c0660b40606244001850b10750060445008185030986602202440034000080150740080850381e4584030340042c80088102d03840380010900045203442d10300180240345209091002d010000c507000072503010340d101001503124079000b20b42503440b80c0810b403009080d0342c0000c400710302244255403400d800d14001c3c59450300c00e42e086042c0d4400107103981c800b0b0320942c0320408400c91501042219242c24800d180b0f105480d501050742c0103032152000c2c0407224091040d41c1015041c0110040c0400ca03408001600c941c2c028030515002c42d1041582c408510901c8042d008000400c103040c0f071003040b040e403103000c00c401115009400d032200f444401c01142180b01e0703140800c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 660754010 1250 660752760 660752773
    0x9010b030a051f14070305070e0109032102030f0a030605010e0a0b1210121118060907120906090305031b0415050c0a050307050a0507050103140a0b0f030105091e010b03 74
    0x420f2089610340c4544452504013180452000d51302180c101021195540030995800c103111356158022141817032101d0030b080c1005010b0840d241e000c6000004040600703241e0383c00b01503401e00351007481a14404207800611980318402e264002d006451b072801007600003030020064100328541031110754104c60300b840d078007860411040d2004015070340081480181c401d40001c0019035000c85140c107045035001d4000f8001e02d8429004224020b00342031020000600c00c031060004550700c0091054010040c0c0c20300b6a480114107145d00083d240c0d400015003c1468008480140b58101c8000c40c400d81d56407101d910702c40020841e40005009030b01070030414000c950256815180100b00506013400c0b40d9088451001403655040c1c07542d400014121403a410002c4404c04000302001900c0181009003800c4c86140c1d94401050700c103a00042c40f0b4101c42c2d8943c25a440c00340c440300341400383c1101c041e000f44102c0c60003402c9603640d90640383c118a03040882554070b00140d40c06108401c40c0c3e840c01409043d0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 660755260 1250 660754010 660754033
    0x301051302091207060e0a050609030c09070c1e050d080405070603020f1c2702033c01020a0e040b0904080318010e0604060525181d09010b030a05 64
    0x1c2d0000240181c110862440e6251800810007290004218070740d107040c0960810341c1403210206c16076210f180242002d11040d00f19690202e001c12004500790340748401e60340c2d8084100c0d14010a428043c0400d41c0c10120410341464184080122134000c8085440c501042882251544800c8501a0941d0800c1109101442c800d03001480c080344607207211400c1066a001440c00f01c10201c50203c516036440d40544000d940c1e42c100c0f0982c4515000c00400c224076190040703074480c03107211054404070090b1a603550f000c040002c55080035901000c40e2860707900245900728001c0d40440074100201e841c407001c80c010340c034050042c8480c203500542030f030181d03869981c7c0d9404a41c00c098420000020700c1a810044164244201d5074030810030030007441c40b8200f5040c0349045500241400c4643c010900e032400c0c1d001001d06008010840c60b1a000c200c020130885014160b2081ea0081c022400c584651050260b00034580c02d80070b10415002001010003480070036039544040d0b4002001c607080160b0840 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 660756510 1250 660755260 660755299
    0x308060907030b0a090f061512023603010506060405030a1b0302030a05010204030c0b03040b04020f030c040e061902210405010b060a02010c0e04060803040e090102070609050d14030105 81
    0x160480d0060501144210384400010200b1101760810801a0b5443d00c510543c03841502901000344602445090540b199120003021250f847d4906000103800040d8507401080c80e0300c00c04440161080c1031304e9100099520040c151654188141c030941c204000701d007552402c00116402c0751401801044a441583d9420711405498501100c0303640c0203610020140e101030082a00395885900010303a03940c21480c1500303c4512641041810310014020080011418003080e07422540485004241201a000083c501041d103a00c2a821500701060782d801c2001c0040c50030b0081c90542c114001c1014001e182e030080b4001c02205c05020401350304190b401d0702d054200c460b080341c090700010503003203881030100f2060392010081c580180e640702101c01c2203503401022041040404c90f81401041e1074541159030301d00840c0503d452100d28240030864404c02503048840440d4404403c0c000f2030404d0400c507483d5085106c914011800030981000d4120031402280c0c1690700080c801c070081c40c0c1203521744 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 660757760 1250 660756510 660756529
    0x620070201270b041502060c0403060b040f1a0405090d05030105090c0f040b04170d021216020a091e090209010303110307140d090617130f0c060309060b0d030806 71
    0x800300c0d510244042125110b0b000c00c4502401091140594980c5041100e84014000c0381010b0115046a81803126486c000e0040711f04403600082d010a611484d540098000c110350401e40b840d0ba4a8000303501c10b6440c9003400e180c08000100c508202c15560411034989a11016140c8800a139003000144a5071070407292680d0407001544807182028442ca0001c2901c0d44030350011410b8030f402290401489160b5804600819069400b6018251101d80080c1d900c0342d80020169904001203134000c01c0d20f880307000360f803032043d001003050310706996030802d030001403600798244100040c43c200e64402800060164001150f4080c0000c0c00c240c0c61500c0c01c5601100c03c448120079400100101400315840400240e109049203014151010030b0074809003201c010740d404507040c045c2243c2d00b00c0c4007000b400a2203078051008040c49649150301c1c82c00c18121000040010840740f582c0f134022640d694103900140c00c0351310400007041540542c40030070001d039a00036401030008028200044441c149000003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 660759010 1250 660757760 660757787
    0x27100518060f0c1b0a05061201060813020d060605040b060304050712080c01020d060501201002030403030608061003031715040b04150b09150901121a0406060c0620070201 75
    0x580d42001840001d03c1c1c1844009014210100240450340c04e40c0e1404a50701c43c01003404440240c40c110b40c400b90780040300014441c000510229000250103d1503034948001d0700350303006108528909030752910340024101809454051441c1804044482c281001140c1c0110b030041c0081150a1411a0034010400d120386c08450121042c0408000d0308800d001815120342c091f400480c4480c03c4c1000106624820180186070204c0c6412030b0742c1507580400c21800380641c1500142c0e5a80d0340341403c1d809468103034401d908901c900010403116905051500056034825a5038a41c2d0100c0c0005001034410160351103134640c1021040703400686015802817004803c042e0012400f000010030404000100d544030319140302002924102d989040f1104160000751111900e06050f0a140020f02203208041c090010645d180c810381018112100d1381c3e24150390007031050040c6511a10010066450510100c505505000481c141c0641c80c502421040d0b01d54101c1ea0304050042d001140c00241e094003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 660760260 1250 660759010 660759037
    0x20a0201210b130e0c03030a051602150307050d0e0a0b010504090c1a07140d17070c0b160e040b030c0f0d120503040b0109150e07052710051806 63
    0x10380b0103900c48911039200741d205071100241d080040140b2500701a205403c191103600b0811070902e059810074151003400d600c10540e503d03028440d10120720102e444942000410001108000c00c1d568004010203065401d039000f440012240c025184d912410301c00300509803000b101c0184100c2c2026405152075900138080000311982d00e07251006402c1c00400b189030201d200194187c14004a2019a04800102c0d00184040000e01ca4010b09520039120959101810341000c00d41e098424001c01440c144c02c540254540d042c040b1841e1110700b051211a800b20700c82080540d6185800d114181d00d0740c03400f40c003070003e080143c010001400c0c9003003100355009000ba1a0706d004902d40700380c41d040002d4280c03502903032410b040c01c4c085101401648141c0c1220300b0a294440150321203000d0101b21060380c05016810307201c10a043d03509000f101030000d008862420f0108541641e4003000d84010400d481c01006d8011107442201e0500c070320041e01d0f0441c170450669181c1400c1c03c0380203283c809000c64 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 660761510 1250 660760260 660760271
    0x303020306030316030e010e1c030f180e0402090606071208100f0b030a05060a030c0902090604171c0306140d0302030f040b0705070e010e06400c020a020121 69
    0x1300035800d02018850305400141c04140081490358104100c0e0140382c408641020703441050101030107015802e01c4005041040040524071041d0003000380101ca0829510307003c0b80030b5212501401c01c0e140032a0144e01c0b4804090104034203041c682d045485082e007041c2d241800e5520b115096428110203454081c0442d54500000740208a2400c03c10103080c0c044403040d520300306244084103aa401522192181014010030400aa102e201d4641160440712001d62038040000000707215015030f5016819100c003600c10414a001c021404904010035601c40c0c41794250703803000880c129803486c064940290742d02510401d040c07618480c11003003c0d03c1303441204c1c81d108013511070b41002c0d041075000c8020780c8008101e00c41000710a001c0e034006090810540c4070107601d40b03048041c03801000b0704800d0207180410000410000a035030045001b451883e40c150816400107419401c02c54031081101c081864100c40d075006d648003094440a40750141d484002d80300c8190f21080540e00000700c103040d01d80d560b1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 660762760 1250 660761510 660761527
    0xa02030919081b0312091501060e1804060c1103031b07020a0f1212051813113402060a051b100212151c0303112a06040b0403030203060303 61
    0x750a4521181c40c01000703151540105d20501410f1388014010039000e421068854400126250000d411030391a45404517034450200f02180303c0701c19004401c0039001d075a40401c01481140e41082650801d00d0fa240f808d80e50803101c0380784c2ca90205803111044204500d01e072403070341c1990f10081c05a040c0010b01210380c1c26074588407031001402503031007440003d05000381e60061080003908220303841c156080c014600f00b5040e48071280d609415200510072201c107040900c100031540c0c01484c904020541d02c0365203113100d8601000e0100403403002e0703100700709200ba69100075007400417140c05540e024002e10705001440303a0680755504001c00c0c603006030040d90503020711980d0401440002800035000181ea0310000c800e195403802000380f8044202105002d0074119071985841c40c00349080d203007110121004146800c40c050080500d0100c80000c1c0030559210110541080b2400d0b405c441101c0ca0070844c105030304984030762080b980502201007410010b00801e0181d0010340d031001000b8142d174600084d0303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 660764010 1250 660762760 660762787
    0xc1104110d0902030c0904060e0d020d08070503070c02030f010b040f0e0307020649020c07090e100204170c010212070809120f06010e0a0204081902040209091e0a0203091908 76
    0x7110123803200f03038950380c092503d41028804890347c1000c602c064100080b000c00094244070014144000300180000000c1c038452080c446180b40d20350003001c9e0350501070850309640c040c1c44c2829415128074a030040e001c4500c404c92050038461100c0b54042d500b040700a408104558010403a140c50882407413241001c0b1903c50b07101c02107480f0040e030380c1c081e00c2000c0826035a035a081c04000c821116104101c4004032420029042003260031843c40030a05440044080d402c00c0c0b0341c0150041400c0c00400c000c10a407490342111440c50014070215040d000b400801280d44288007560b840e500710b420006100820b90b0304004006002014043c0001c0e0032220385403d16262940003010481d0700310701c005100c8100544425038002801030802d504107418001060f40780e20800c120200b241c40da80701d0100c119225501540c0400f500104001c03007a00d02600c80420703148102004507401c002d0040000c072000280d100307a9004101210041184552055008010110803241a01c0c0d054060000b207414007031 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 660765260 1250 660764010 660764029
    0x50c040501331809090611030402010e0d0309180b10022d03120a0902090901050c0f220315050a0908030c030711030a05130e01150807110d0c1104110d0902030c 70
    0x13a00000d00b0a219051090440350440d14950b0032000420920002d45c1e40901d04007a0030804980400701d888403407070140e9220b001507010a075020720000d146e4100366a2640801050075083c0c0e4002e008072858002281c840c0842c203c1000350002440288144150180ca0611354858002c2200c2c40c04042d03001d01804410211440081a40c072070582d0700860074480600340d004050200281310034246902150707106c2c0078410100d110ba11011460381d1009131000403020310486d4100000c84410f8503803c0c8501400100e03402000c0e46410300020851005403440760071549500050242c0c2903488441c820031680d1300c044c2c00c680400c0100403450b64842170910040810344095100e4682e40c1c5107106400c40903003a01d0b070054456001c2040108508201c40b41c0302c030a40c2503070b454488200d95918105550581121401301c41a1280d884002c0200d03400c0990071540500800b118080d0003c46d0301003100391a0070342403501d505a01030050b540f05201c641c01000030144001c054441d900030b6040412880103 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 660766510 1250 660765260 660765269
    0x31306020405181e0408180103021911071d0a02090102012915040e0c161a04140a030c140111071a0105100203040e061c050c0405013318 60
    0x421000744101300011218036078060030078016540d260b01c0c284e11100c0300c9008101d9184622a601a447c1449a03c664111800ca41101407002805070b102070005203503e521a4945001d441242800300780b0203d24000414418000012100d1a80c0d030080007101a4000e020024155900c6000c000c00d000c0d41021512400c2c003200c1000d890300304a440400c405480000010320300000100018420301c582034801c00d51000c00d940889a588004c1604841311400e99130019181818620702e2048034203c060065000e1030103200300c0e10005c2d00c500e4200da211aa403000040c0450f0400c0381140c00074850020b1031002e419800300001c2d003080c0d07446040d86c1c103610040044603403461100146020029001040c1e016202c10344038801d5040030800040c4d81c03882075000303c5110b40149000511030780d4030846030480381080460350a070245400d1918959480e8036081c03440c4120308003000812a9055200a622010b0707022a0303101142d61003481493348400c2c0308004e41d0402013041c070504240d9417a50380050040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 660767760 1250 660766510 660766549
    0x30c03080703110d0c0501150e0a05090c061b1c2f12130b04030201171b0703030b030d08071403090102130b040303120b152b0c090504050c031306020405 67
    0x400c01d51500f6400c680b07000c9030000010701e50314009c4c4114101c2d080e00301e0f4000f03540200010291180d01300c5c140382441015946502003800030b198030402203181903039901e4090840c00c4801540c0c14001c007411404101c0703030920006404c10080028042402e60706683c2101d1041d843c9210400e64442e1424000041131030300340e00b40d0000b40c0c03003649041a40658002c10001100c02d060a080d50700091122501c059040c440c0c0f102c2c0b802055101100c40481003028821001d800e03503500c114a0050054201142160310900030110781503403840c0114242e511415842d0348092002c12070840e25042c0f40c10203042d80c1d40540d401e0210f0708211400c20400000b4100b01d000e050b4699145250003412240085034044c2950b09081c00b08882ea00c8040d101c010b203008070410305480b0059168030b07196603020181c00401e02c182d0340204000805c840e074005580400e5680d01c04004584460600003910b800351101c8003070010400004d03c81b003001840e20b01040744100e0b8090701d0903039100c00041c26039610300d00c41c0009 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 660769010 1250 660767760 660767777
    0x405040615060f08010e090a02130b031501031506150f140a0207030b07030c020c01080403020a0c0b04090e033a020307030606110a020904080a0507140f0f07030c03080703110d 77
    0x519044901c40e8010303c4180810200380ca41124200d84405090784001e00442205050032b1036402203800500b040007019041b5401c106c2044966600c0303940c2880180e80301c45da18030b140c8194155034000c3e5400d45041414850000d046448129000040902d4410411040c80b0390354601c1c4580100821800b41e85034000d1000a0941c1000c00e00303400040c0c020360605240031005000c0c29004682040d5009090a2903e500d0351a402c00360b050203040e40d0000d0489144010202d0043c0441015000b6180441e00800034007040c2c0c4103040da2403040340c08502c0051b010250b00344107001d40601982c10b0041d80c0c00c03488102800340c131520040c0e030000c0d211080404e031202d405010541d1f00c510300c081403402c024020480340801d03030082012202d01420103012242c00180a40d6054040d00840f05c0480d8002c0e01503410050642c400e5899100c40c0c101c2c500d1038000d605070043d06880000d07161064030303044828035540c0d42c42d51340e503c00d5a91090740104d041c00440903196100c140248803020384904592a071090 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 660770260 1250 660769010 660769037
    0x2070b07090f03080f09030f011e0606200106030f0308060103140f2e1d060105030c030a020c0a0f03020d02070503030a090918081303031209020d02040504061506 71
    0x91009018404000103030404120546a165000c0b0469410040c825a14503840301c40300b5103886034550050701845004490146d0a00562041200804015580520360100300364002a01d0903482600c0000e410078464000103103654a0b0407148e505510000a0440c0c3c1d80c0e03541034906612010241c01007100f020800203103580500403090302c0250019585810300d0403841c0c0c04d140701d1015100400c03405070804841c008050782e0300c04555240300104025401a9a9007103070b40300700760902c003c24040342e0703000104000d54020001d80c1d011b443d822078110b0440d40e4151010000f500f00e10102c4640d442100408004544031050100175640a580030380105400c50001030300d41440340d48424000d40c01000900101075000304030000f038400800c401304078001803074003500ca0940324000250180328002420102280c2d003401c0c1c0070440c0d2090315110101008450340d43c084a1503000065008140711100340d005140950085501c60701c24100010b00d0000b00d16901c10082058111902003030440c2000003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 660771510 1250 660770260 660770273
    0xf121c051804051308031e10090f0b010c150603081c182a080d0f08090a030c1112010606050406120b0a05060a02120309030d1413150605130207 63
    0x1d5407900140c40520039030515680c08011045140009400440c012000c14500021440c200212554840fa40c00103428030316040b03441103005210301d1503000d2410030007218140b064010404800d4050312400780d600000c1d110800443e80c00d0000e080c2c41b5607282030100005401300040c004840780c041500300c5295030f23840b5a8046460182425540c8159090240d0000d0345410041d54800404044100c90411240c00802c2c295000e420015407030180943c3c0b0361240b68400840c142000543d90342d6201c2c0c4e100c0d0001243c4801085c071000c1d000400040d05000440d013410408401034602810039500b02e445415900e007100c2464111400003040042e0410009602046056041901103010816001014001000c0d0342d03162044600620000c50700e003a0a86c0248a140302c503510b07a0481070b03564a443d200352610b0703074000b8100014451802c98165040109035144034402c5090303a85043d56080b850320f8150248400c41d00c40d0224644418000c80c450311180414800c00740034190268896441e450310a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 660772760 1250 660771510 660771547
    0x80f031014030c1f02010605041103090606011814010c0203030a020109061104230f060705010e061303050a0e0a0503100204031a040314070503040f030b07120b0f121c05 74
    0xb4480d500001d22444940d0b601603035224101c0e4441c2c1810f041c4808140141e01400b040c2c2e214a034002d281c21003025941511070002c501c01c440c0e80e4150383e05a0744000064408404280341c010540001003400e1003501030a0f4950542510141040c3c071324082e00f680024a1a0b101504010040c1d4550002000b00500d50250140d285c0c140d00c5d5450810782030940c90107000688032043c409100c14014020141e8640540c03480b084440900141e035a0861070500034060042c0315800c0b400361240c1c40008424001c181a40c003011603055407040e1038024050000c0310700c1908042c6c89544807150b0740700010160340c00c0181d0304401d0008500075803030b240b460070080886130392001100301600401081200096002c0c20050351510403181c80c0782c641c0350f141001441c600954118107041d0704904808418884240c14076031040785542e503250742c40d4111400320380545149140c1c00d1f0300000c440302c413251949800c45006451024410803103810901302940e41040c201074050810108130006441c005690311760641 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 660774010 1250 660772760 660772799
    0x1b011119080c0f0d0209040632010806060409091104020408250b070201120b030a321b2407140616201c02010605030a020906010804080f0310 62
    0x1c0c50503d1a02192509075100310851040655070001c0c491071690788a40c040006406882c60101c400038030f00840d50f02c51140440d00c594561501c10404800e0740c0b00b440322500c644c40151500342000c3c64131038514083c1c10403401c12070740040c60714441400c9445502c040c00040090300d0041c010844040120185215048407031038070040840b200340b010891756800c0b103102070b5082c030740040443c0300f08400340001c20b8024200755040c01000112400d2014003465610240304503841540c0a0b01c1981411a400030560721301040e64000080320f8281c103440f4044004a032501503d06a91100304001c00d42c84420070080706138842c40c003c9051000e2090422821203a2460b8200522660030003400e0345412001d0041c0b01000c00207404080ca260800c50800752404850002c01c840702c2500d1058109003150109250310019845c0c540000381610b0b000031400030180c3c0103007010303110b41c485000455080b04000e009031b8080c10108040d00300ca4a170703c0c2c0214441c0140c02d80c0580d4072400c100000060070144040e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 660775260 1250 660774010 660774031
    0xe070501110a0f120516030215070809150c0d051e0c13090b12010207260f09060a02070e0c030601022103132d02100c081b01111908 58
    0x66082c00110390242451040d6007201103414990480c5208a032541725440200c103421045000000806800052242c803150301804e0550b600c4c1c2e5076143c1190303003000c201c510700001c1d40060102c4007000602e1080581101d03035558140d14158810060b54180d6001361100300c400d0000e0300401c480924051701c1c003600801d1221007180b038910f03071100610840c1c5042c0920351030681c5d00c10880c1500d80e03070a58000381501260009544813081070400310044043c8031402d52000c1b14100740c961204403072608690505500170606c9007084c070040103000050308040010015071140c0c4030003246500107086031511030700003020710551b2460a03000081c142000e1a10300120b01c0c002804416040c2d4091090325407104030020241c0403801d0904200503484003000359040599201190900c03074034005004407240e18000d884021804001c5c3c0012180d1605959000d41a58024401111406640280c0c03051000b0b004001080d00355004d508203000c3d902a20508840c0e05003c0950a000c50300b040050740d00c4180c241 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 660776510 1250 660775260 660775273
    0x150106080c04031202030706050a0509101509330303110d0c021002150115110303130b0a020d320c16050708100b090f040c0b09040f0e07050111 63
    0x51001050140c3e010060021011113664000980b003002a148440d4101005000c01d00341004990010001580c0610f10390299000051000e4124044c4180da4601011820f40481ca000400401410303458854030141a203800708100b01144002e50381061450800301d603984334070310720f00a80070740600c001c2c0d1412900003102c01d40a9036000003038160f00580640e00c4400100b44404100d0510158041c184000410100046683d00411960030725601c0c007074980152142e035144c0c55681c0c07400115840e800f016908040100000e0b82440001d4000004c000e0160501c41040c03202d1003030b5400150001e0fc07070350109400c60381c0c10001c80942601d020b407014000788035040030150b50006208202c460b55880d2080050a0108641000040018500a0290b4034800480d038100c0e00900000c14072a8460243c54000c550540c4048116134001c681c44482021041d2400c095610300d038000c0e091090b8400e954807186036040e00c0c00d001d0780004ca00d818014001c8075046c0000940100c170703046550030143c1d01c440b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 660777760 1250 660776510 660776521
    0x31101090608011a030a1d071e0b092206081b0d0201020c1011060903030f09070b0406030c140a090e09070e0606132706210f02061b15010608 62
    0x10100f00c0c0b0b00c00a801e00d0b10350b4a5846254003009040607d4440b80003c102000b442519000403c11006451500450064007032003a5080c00c2c41e04614007907042e0100b400c01c41c44c0c1942c40c00301d00706159044000004100036110074006001c648085d48140a16048114440c1511020800071005241d003200c401100d280180c00003955007680600b403c2c0204400100000102e009100d10212102c00804407403851801800c0720362a500b060ba9104490050074000c9400d540c404107014040c3c0d118540c1040c207280c0780c94400c1703000d400e20203003c206000003121410a0b1031011401801c148a0a8684502c65441c241e0021007100c002400c4119603000300c40103001030105442195000b1804840294403000380005803100302c0c580342c1c42600000915921a4050032003400d5148210916035000c000d07441d40d4003010b201c29075100c0c0e041d150102c40c8418040024071050400c80703203a03002825960a0040d0002421444600c20205405a80c4822100e203400b803050100c0501501c800e19201d15070b428103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 660779010 1250 660777760 660777779
    0x6030b04020d060209060a050403050d020a030f05090105040e0702160e090d0315050306190b0906060703120617030904051308070b07110102030412030e0a0209010b0a050702040603110109060801 85
    0x1420080c0b04240080a0209101158042d0361900900903c0c42c1d5844e030f204034025117560311034482181c00f40150354941070500e00214201c1071490701748e1204006954110303000c9070281e004a46050600100340b00c0840d07019102054544142d8440d00106404451541008881c1d400e50303000740142c004a50400072128004160031461031001e0801080c070b0b0a84900309114503401e504041d4040c070428042240c0c4000b49061840c02c1c4175003107420044089840c01703000b1000c4e011114940c104804000d0503000a100c3c4052049040100034001401c0b40c803003552410320321045450000030b51002c103000b0300a24092040d660071030706c2c41c040d4a44110042e03075145068020390704003130000d2801d0340c005104540034000c5840c2940300c44c00215900d2030a40703814141c0c0f880c07545205000a00e07100301c05c2c03441900001c5c011003081c1c0081c962007032a031800110400c40d80c01181130b941046400d2041d0030043e11980102ca001c0c1d4403803051011820590b200050840d4039550000040144040040128220 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 660780260 1250 660779010 660779033
    0x11180c0a030b01020304080f010c120b0306010303050702010e030109030503160e030d030b010504080102040e150f030c0f010c051c020c060f0901050f04030f0c030c0b0c06132901090f0603 82
    0x350300340031070040701240040c5d055014a5100712030a00801e00c080b500c40e201035002d103851030503540f00c000e190303800902948101c400039404c02d9050b074004001840464014005040c50358814502400f101d07004002103420340324241e6044000c1000441030209448600c2c02610000010313203002c64800d04800006030340c0d195022501340c00e01d42d84803683d000c07a0344544100ca014165500c029940c40781d844104105094042722140340d80c2501b4051012249000310880c0c41584006000f0800c14901e60200a98510070040103414010140c0e01080041c40520174048007080d000040030340b405500d85d0290400d8141c01503a0300c102c0e02000940c40074024541961901503080c40c0c031030b850349403409002401e0b2203a40c0000d042189031340b01500801c03580304c0220717090ba4401c500040841d9030f90340200c01c0c0380c0961004004181c10440c002041840100e0b141203030301c2d01918828124842c4080c00507403411261081504181080d001030281303444500802c0301c814410f14003089070074510788810034a4079 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 660781510 1250 660780260 660780277
    0xe010e010912060204080601061101110c06180316080702090627040305040f031b090605060f0904020d05250e131509020c030a020c06030115120212010311180c 70
    0x5102c2d84081030041c0796056038050076030305044400c103513155040540001ca81c0d021340c501542c2000c404c4000d0590316800d4866504071000203040f81c2d03d88682c080a4815120607414040c88244944817600d4900e642546103a070140384071036a504228014050107100c02080140100c5440102c81c400100c404880120010a00c4a0502030303192468100c49922540d4005c0d0000050414044207003c4c0300c500c0703400b04038a40790603804e0290341c4400e800141c903014406c1a40c014420300005508e48080f20081160500003407006141c811180407500c00c071002a9410020409840b455004103081c00003420342e01d900f281004034841c2061800a185021201d41c1241015203804501d01c0b48003505040c040a458242d41c02c1d91104e0b800c401007613480d00704640f0100148100441c440540c01c0c40300440b8141c0d6070108448854148682055641c22082090100c84035800c104e0100d040c002c90328518040c6105495a0f101400032008001844082c03500c08001c0240d460280610070403008111042c21 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 660782760 1250 660781510 660781529
    0x403020601030f32100b0a060507051908090306090f030a03022d0a02070f0b0a030b19090504020a0501050a171e09031306020a0b06060306040902030109050604030e010e0109 76
    0xf031018900055030312070b03c280c0104220006000080005405440c04850410010071218108004019003054481624616070061440f51082c06800d10400062883c0c0780100203d4132480b22405550105200c079120603100243c010a0800c40c3c3d103024419144c0000038580202030031142d01302c5154491040000e00c8042c1a030010360660041484280c1d100d1241c80180111030000c104200540254052051000107008840780807030800d00c08480403056480ca500e103030b401c003c3d40c80703000d0b801031025100e02580b14002156031403403000341500c1003018090713500000c1414106881800008145030300010b051100600644810703a5202d160b02c155000b03181403210054552900c02d0b00c503100f0090303d1030002e0079900104040100300000074000806052070030f280d110307070350802241c940c0205080107101d00c00040200d0142d14211010b160890001000042c86070340c079900090841d2412071003100c40e6005801080207058010b11420306d02c10083c2809a036030019240001c2c040b8029001d0320382c7c03c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 660784010 1250 660782760 660782783
    0xc060f180a03020306070c030e270c13081c0806060d0c11011503050706050f0d0506060d0603050d02060c09210102070204140f090d140c1c090501030e06040302060103 73
    0x21a966050071000954000e4141d6086050015000b013481542a40a9012651220340444681403000e14841400c00700100c0305168121035500c0b08101e000501a01c40c3c0071014404000b031301e0104040003008006080c0104111561040c0c2c441003100c03640301c00c00500c00f4100410001e43c958804864800d00c2801001821040c0c440f416507400c1d445503e4290345600c0d000c12100c1040300303000782c50283c80c060021030304020f5a42d4400c4420b4070514148681d921001d010b0071807201d8581e08a950411402003006081c03808104c410740c11a0007551040c1c50fa40d00008190301015014050aa0414030301e0b800103107004186004100c1e10702c40004407480920f01c0303140703d001d152070030f505071282c00fa4018828003c60880c540600408507041d2140a02c1c0e0b4200004610400000943c0c41101303915a22802003526468070a501d0a42001c10305120134051001040760841401c000781d2590101c6840e441ca0a50030600010100c81e0241030040b17069005900f800003090b000191281100d41c00160140e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 660785260 1250 660784010 660784057
    0x3040801050c040e2a180a0b030c0f031302102115061115090303190c0f0e010513150318080304120c08030106090e07031814010617010504050c060f 65
    0x17a03c21414080d91500c541c04134030205a0076140e6002060175400300c07a000c28081d200e140d107108034442a130308142c0c80c482c01c0045038900b190740005141d03c4180080843d04440c26500480c1203106c1100b508000181500c203504801848d141020003400c035921402c01c0354a05600100f0f4500e8014081c2c502404001d601390780550b002007142d180d02d65004c4003908070310b0a1201e04c00d56640c00a55910f00022070b2040d1010b140c0100744200717644080207a950b0a418101c0780000c0c0c03812412803e80d1410407404000c51320246000f0041d0307000605a1010704620221102c0d00201101d016000c0946e0ba900e411288102140e1804203903904142c1285010078007840710310090321100c41540008144480102c00080c0f8290054030070070880301000740030b207216520700c00c04400320303a050324021418100c0308052102003000c404034030403018840c10000400944401a01e11380803d01c400d880c1803a0345071401c0004002d010f0000003180b0344241c403810308040701540300070028010286040a503404000b501300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 660786510 1250 660785260 660785311
    0x2c01020d09140c0d030c020f1c0c031704050102060408130f080102040e0604110d1e0911030c0108010e150415122a05040207060b040c0203040801050c040e 68
    0xc00e40118004100030128852a0110900302e4460304040c0d5070140d000e110040341031405001a0003681a070f981805080141e0802032003a091b2101d480d0800c064800700908050300b2420701c100d185c00b4801855100d4074525114401c2d41b0000d89904070841c043c00200901d9800040041d04240d10074600d0761946400d0780010f00581c5c1c0c42d845100c1c910700b042030006802c40d041d4000e20a82c2c8900401c008903682c4c80c424071050fa071048128464110b0b01304401465003829078002d002c0b0002803540c1890320640080002c0954000280542d00c0200103508006a441d08006d12480a0028200a02c99600d41403802c4070080c00142140030b80400030305500d401c0da50b01d82c003005c140a1104c101c011020f850ba05030841405084808890f214052203030130103440c40203068a12000380140e82003103041d007480184030103504801e0b412a5000e8844014614540c0e035030091109070310f02c45d4002c58860b407070800d120782511400744c041801180100f02c28446004031414035507102c8625224655490050031054 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 660787760 1250 660786510 660786517
    0xf03150901110f07060c0203090a03060c090302040f0204330c08072f12032208070b0a1b020d1101021005010e061e0d03030e0a0b01080604020909012c0102 68
    0xe01d08a80010f150780c041040c00300682483c5002e07210811540c000b040081c0e03030781d105031002d555000700c0110007000024426009050105c06074503200303d10958960204007500c003010f0a440c0500d80204080c480760030503480c1c4602400d4101551a10b0a8900c0b100d0f01042d080010740300200703d15481c0e400240600c2c1d104840e005a800501d0002601d0081b1081030103000b45c1001005030945000c4084031481c03d61004003500300b0344070155150140b015450718022845800c000848031200d031001a503000f00340529402800c00303246140da86d100500005200b040700d042e108d0614440050440050f840d1500c4022246a00041e03102d5154144001031b0716004003080060b1581f4100303400401c2e0a243c0d804c3c1340e4052001587d003d000004095a408001f4500041c2d6a800100c0880840c011a00c2500b045105d84546c0081d9a070808282d1122a0b0300503090300803040aa10050a10085003402080c3c030b684191032400811000c0c0e41140c00b20b03e540341c84000384402880c11003400303954107000c2d41207 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 660789010 1250 660787760 660787781
    0x129060306040e070b0a08010905070e03060f07020f1002070c061719020712021e0a03020c06181008010f050f03031b160e0105120f06010b1c0c03090c050f03150901 72
    0xa440e046c0145004040b03800034018a03d107107003843e0100350054091242441c40755130013000b9080a81c2c50300145014964010840f504511400c41100300c402c60502c001ca1007c50000400743c5d882203e424400f0760444160701640c01c212103007001815014140e10401d0708072145400200f158105284480041d00902e2800b03415940420b10103c1500d40000e03c078400b110342c1d0185078000c0203d1010080d10303491481000340150300030440d080074605d00000284081840028510b0460003844081402c0606a11994000c24921001403116580d00b80c452002020111180388680c407400c000301e41c49010b081100c40c400500d021300079410f10001d1050740c0c0541c1d048140003524a9035514500219203007880b4440c00340f0444030b01c403182e942c1c0100d040003c0d5101c4000410071a46490301e0f94125500c50701b4090742d114a002c00000c492602da0080d0580500b00c0d03078012840281030700704080300d0304070b69016601c601c1c8a010440741503100450b0310110f103559040100001e0b6105807100d400f41060212 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 660790260 1250 660789010 660789029
    0x61409060309030d0608011503020906120f070608090703121b0b07020a0605101d10090f0c1e0e04020c030d0203270a0b06041109040606020129060306040e07 69
    0x410040b001d000004e8840e00030114424094680d94240050072101c00011260403180c86c10414005400c003091015000701e005025907081c07254010109080254000f4282c0182d00200000c00a041e4081d0b040d581008448000e03110721450350f07035002d140429006407a400e00c5980c248010102141088030b5001d1500310501309242d25040b40001d40b60018060204c442520b000040386041c00c0c05280c64059603030710404d10140c07440d4200e03201c1c0a944001c0560850443c0c0f00030105580c8180e01441c0c4116802c1000031030888140a0301500180900b220001c4030714050241c0302c0d5817907100822448510050303800580d02e0403000420741c10343c4100c0d000c0590b104d000005004450248046000f5034045803609114a21000e02013140c64207202c0101410580000012400300e250642c4800c04007140014468507200301040410140c4d1101d41c40711015075900d01c0381e508141c51040c50034074800c050f00e007280c540070440c0700000d1050001030110383c0910741d2200080381d10001044110050501c124 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 660791366 1106 660790260 660790267
    0x102041e0305210c010c0903030e091e090a050a1b081c030b120d080a0501090b090406110408030706050405100902010c061a060a02060a060b1306140906 67
    0x20840841c0300f0108501c0888420900c02e84407905465190305021610714200a0130810b00425414061380c1d981c41000360081d83c0440035800070203501c00441c403030b44444025600d820650400101584155040041441204003134180c41d02914680c074143d068441c0c9086803102d41180b2800c503595090603c04000c24007941042c4400a80507014451081895004034600018200224045511401031110781500340c003866000d440d1104060100da001c0001243c2c00c1e820082c006040556580b5a07016560403020071940105607480807283c41e00030300e061100081c8402d81d403c4455102d041c00e01e036004e070b00a01a200d0020b805031120300c2481d009440340300c00707890000420204030282003100681c0360f0b5402e003e030200449550003404a4a030440d1984201ca19540001a0b42c1800b441514031001d071801401040e18a6403411001d6005058020383c081e016820b0f071240d01c1040403 = true := by decide +kernel

theorem cover : BRFrame.Cov 660611510 660791366 := by
  have h0 := BRFrame.cov_init 660611510
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 660611510 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 660611510 ≤ n) (h2 : n < 660791366) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
