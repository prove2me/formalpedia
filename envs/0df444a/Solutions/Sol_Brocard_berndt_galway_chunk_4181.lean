-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4181
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:03.254674+00:00
-- url     : https://prove2.me/submissions/ad34ce4a-0039-41b9-ae98-8911567b8563

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 751798561 ≤ n < 751978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 751799811 1250 751798561 751798571
    0xa020d0e1c050f0606030d0207030b270109020301060b0a02030d020c0a170a08060901060c060c09151206090501030f0b0c040302040911040c022b090b0a030c1b0c230a09 74
    0x71103c05104450304004150003600c00342545403800b80d50703088a440000c0402c0c803404001240c01d002c04080e420a03072110f040030300c04258040380aa000c2d00b99145c00f80e100354a0558009406000d46d011982d01d40881e030080c40c182350860b202031000b50060302d0541d04902443d031100000030141d101e1144002c84d102202a06e600851200038007040d8002c0140b0302540340c84d4014800075400802c0d404159902840100306403a1070700781111441c80c1a800311210381d07280f01c04e401d1129002900703040c0c030745081c0504000c880d0b03540451308143d4a0a2101611400c004445103000c951009541c80d070000035080c40500c0c0036034a501180484094a4068034070f10764801a0482c1031825020782d16450a03184010005e400e031401034008500ca015800f140c0700c4140844086031039010b583c6141c000e1901ca02c4103038407500c4c9000c024010700225500c070000504e0000001c0240002e08003c1d00b0901d07013005850b0556401c01c400303844005010780c400407204000c0302c3d40c40403d41c0c90700c0c400e1025100003880460 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 751801061 1250 751799811 751799833
    0x60d140607050429070b07020f071502010c1b110307030507060c120e01020d050306270f06010507030c0807020103020702042d0b0d06050705090a1d06060a020d0e1c05 73
    0x60410807080b01404c0501c4c1c0d060140490350100c0090300c11351508460440c0d06503d941109030729105110754200814051800c001131003d0311740f0700924261240d900284a6140c0d040402c80f40c1d11002d41824080b410094450404500b52040c1818440d0028013120b9101d07841e42c4803c0d141c80c4c0780b030340000000350b61101303103804014040030344140f94081e03400e082602520300c20010391030302420031071007040000110010f10075030340c0c5082c2118002545010324070400035a51074007d06040886041c40c5000c0326a01280c540c1d4821000c444c803035501940d4800304005581d5414015034400d03c01a410107400340a0700015030f4482c41000b1001c40010072406407201c0303628806500311202d11100e9803540c9040c086030030036280c0300090008a0360003900000c4940d40c1040c01c2e2014001da000c5103402141100d004038031508090b010304210456a0358a4100703903210310400a07a48500400200180c120081c11181b46000d00c41906540c1402442c804e4905070701615070b21849031100342951984e008800d03850b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 751802311 1250 751801061 751801079
    0x7080a27052107020a090e03182202190809071715011202031605010e120a0506190e030f0a2f0a11040504110d05010225021314060d1406070504 63
    0x80b0050646c99014070201d8151800301e6107900841480b10460031401007440601d68031200070b00a014070f800c125098543c13000e420000203400c00d8840301c0f000c8140c0d04c2d841c1020b901070115244628410401006424201140c40110700d00d025400c15041c07255144140314482160643c0c4d019200d60522480c3e100307010b0040514200308000128110510702c0010300040c2d80c490140c14031300500392901140000ca1000c0740e8904895444090114082c081c00d1101c1480402030303528200a1514050180d038030903000390340d100d12900c0c0e2030808001c0704101c802003a41c081c1040c1d03048030003010080f48a001c00d80340c0e45d0f00c00c050301c68007031902500986200030400c0f0000306407420307080b4155010440780c902988c400b602074030824000d92154940020442c00c01c002501115104180000e2100d9800e404075081c5101e0722590300c049104400c424840c1c2440b42d1588640300c22030034001d010455a48401c1c00b80094004000350680302c05054009010030041f0801c6124000c00860340c820781d4551038580b0417 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 751803561 1250 751802311 751802329
    0x30a0b0903220b0a0f0207083309030d021c180515010501121812050d061e0b090a231c0c0504051b13050a060f020a030f121407080a2705210702 63
    0x1c00d0727040c0e00300703051010b100ca001090b01c9180103480d0005a4411300940c001421007510601190b100d8180f05814048031120840792a9841c411800c40d0522014174030300004002c402d02a40e800034084050385450088240c010601076140a105001030303c4068480c92041840a000c2030701045001600c146094a280b10301d00c0100344075060514040036100f000414004e25200344800c13600040b460140659a020b61140101003031040100c3c8a2075420181d009941402e019611550461250a40c0034103010500c0d1210341e48809511405030034501007200500c07028043d0619507800582c24480c11126100a0490143c42e003200c801441c80c0004103c41840c1a800801c100450300e4500c03201c43d500059600160303507050505070080343ca956801c840600c0c28128000c8910300300340c203150350084849002401000756a0b80c0080a80d10f0201d41003c0c6e030801ca180d03070b012035821280807144ca8081c0c051852030340d10800c140c6a2540c1980003036021480ca12142428003a00000c0d00001c62a00c03041c1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 751804811 1250 751803561 751803643
    0x1109010617010306020d020c0d03090203010f0b0d17090d05010b0406060221090f06040b031e1003020114090307030b070f02060f010b09030a0b0903220b0a0f020708 72
    0x4651807a04001800340150340c010320008182c142c01168144040000b501903803400c0503074608542d00c07140022001006000c0210059010354032700040b481d085050303805004101200a4460122004181d0740c1c507d204030b6402d840300901c103050102e40b116a4030b00d900703042e056000f1000494941818410413044450071b50050b010366006d038070146441440c610340000b0181090140e2512140c41c070b00850264800c540c40a17500c6180003c000c54603502c00d00c003450140000721100402d002000c0961620802c1c1038030b60082c0904503d108100641c820170b411702c00c5900c001e403490308103407482d07002ca071400c1c5a5400440f00c1e0304032403040005559111160703240980076440100f0f40c07810b04900380e0510a0040c0510007010900003001115510100305900e90940d00079065140741c940741e85015165048503500c0100070700c03801d400d00120750740c449148080d88c0003041594600109a40249c6000281076144402e5016800c00001c01c40010b0091986d00210505010b80c0780708100108460345d041601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 751806061 1250 751804811 751804817
    0x6080706020c12010902090c031512030f090402070c080f0f011512030507142d031812010f020a0f0302070c0612091424150d110d11090106 61
    0x21041001690009600c000824191400c01c001810560300c0c3d40581402000603412030b10310f50912501000d1103000714400e980152400d4003058400007040940c0c1c0c01d0400b90900340d4010302c140c3e03042401050062140d100010070041c035044041d0380c0c0b040300175000da00058080c0c114080506031850240000003c13255000020403031401084600f020341c15a6014080418400108030710030036016000315044603402030070a00500f10a110195504c010846011039442c0340b818064041580c0741c600e220b0030000356000f035402c100b01a491f48280400c0703074107080e6100340c404004102c205403c6c460746d51810550b000140e5100552030014103000f142c2c11002c81050710401598022130320005411b400d803607492401130515411068410080c203540318004d4003192a4406507406d1001c005188404000c45002c030f4106070001d40b070805051f00045030107443d034140c0c122160b4071901e024003914482c41d2080c4c0c400c1032080705a401054039038102d40340c111034000003060310050528020600c80e00504c00c0d49 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 751807311 1250 751806061 751806073
    0x110f010605011e080109020331030905030703030903060203270f1b09040308040204112a0a08120705070b090a11090c040501050702040f0c020328080103150b041e0608 73
    0xe00013441c4101c144118000d0a81c0480032586070040903680400c00e8118410196010000c40d100040040c080c060440c081101c5038000034003400c002c14843c0c200c0c1d4054842c0c5071a50324684554002c0c0d40005e0295490f550265600c83c0c50082d5107400c1101c50464600811011081c0d84a4500d03012401103090600c072001d000800300e81d038403600050b9000d139140c501036141c0d03113940c404107015003451000780b1107039003000c00d803030480c0002d800050a02e24043c0f42091589a4041c0340325485100c00701010340314020410442d03035044c81c244807d64100f222444c2c642d1038000140c89454038514241c99820454001070340c508107011f5400e010070903448088802ea0460309154481c1d4070103110b0f601c1981c1c103002c0c4c081021400e55030381790b21800405203440d42c02c0c00001500c510003501ca0303100c091103980c1c10035020075101c0c60050788640e03c01344011a445403078969084d902c0310050b4500010300c0481864032040d80702032540311400b80d16803c80040800c040c0302500c01c0f00c020180d40c2d0303030707000515141d00030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 751808561 1250 751807311 751807367
    0x90307050712240902061809011205191401050a0f0b041506030b06090a14030f030307021b030f10022508160507080a030804020f01210c110f01060501 66
    0x1c1c00b503480080071070f5002c0c15840040407084401508800c500654884004206070080b0019034005c1e030008001107400340c0b5180e0300e503c50044041c0e40c640d4044c015503c005000c4800581c90001c40360304078054400f0a060454081585081d00d908484c24120f142e224142018000298016100e0054003114148270781500d030940207444400610408040603159000b451068488604131030a0240c040d000b00001500e9018050203903a01d120f010340284940480302038101e001005580c002d41e0250302600040c400c58109001d8443c00241060303240c000d0001c0e075244e141d010411403255120319500940c49101c501100080c0400d852041c0d50030000422520307000606a0341141c0c4814107107103040c42003503020f00b0440e141c844541c0002c4103502c20284840203068004028a00c070307520880c0c0984948400200459a6400003050003d501c40c00f82c2c4800c51001c0c064022400d030552501d0a0300c4c2d4041040d14007890071800304100100c90b5034a0000340029688481e5245101d9400808100d646840d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 751809811 1250 751808561 751808573
    0x303091b010e0117060a090609230c090105180607050a02100c0b0f040809030304060507020f12370c150906210908071506090e0a060b0d0b090307050712 67
    0x1349510616200c400c8400501030799501ca441d60090903510070100002512640c2d09002880c400c00c00e2401010910300038800421029002480341c455081020b003046417601c01901c1c580c0241c0000e480c00c0c2c0704400d1512280c0c40d0318000e480064014001400614110b005101111075100850000c0004c4038032540d0100311001e40880c0c0141507601403401c242c0d9107080501d103500507004003c1e4103000024000034515404000b41082a0003254210b15104081c000c10280601120b20025030350003246a0b40c2501004001048080e184644264103003141401358200307003500400c04803110740e200740040c0010350301c95800110101150911010403410000082d0000545c1015408510050100c596100b90560807000380e040c3d00c55081c0d5101c4540e0b01d40004c19280e600c0c01c0c400c01501d481d0000528030900d000c1d01d951400d464000e05601e0f096512000e0107440b6840c1c0c40c0350044040d500041c001003958404074403820128001d56200d00180c07900c60705003130f15a40200000281c00403100c0200e14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 751811061 1250 751809811 751809827
    0x6080f0703020d08070602120702160f09020a03060302270f040b013602090f030d0516050c090702030306100e0f04020a210e0f0114010b1b0303091b010e01 68
    0x501256081071041e0581303000b040c03c2c491044000c280e1030002c14850241d80504100b94001c0c40560261400d014140900300c03030104041c4207108111102e81401c0162490301e82c000e0140c10344030b01c0d0120311140c407500031407898850000419000360314170b10b03150201800d505800340c1003021305c0c1c80074800f07091a0701c451400c3d1006002d8030b080c07222010400d05044103117031001c1007030043c071002040c3d6001d80d140c0600000d42040850318002c4841140c10845032601080c49030803d01d094a0715410b00c0d5102e03580c98080d540c0c07504200c4681c403802042e02c4840d541c03580d0191041046600031550380c90072005100700880c803107180505000b08242c4030800c07135076003003040314a440040ea00141c0740d42c0c01c0c41045801655000c4107003100d02c1d0a000c1141d4004580d004a0382e0b0002c000211144109a050740d076089540910001d140c3d54100c20061003a4010f44005024401d002e49461901c8404030041ca1701307550095500d07880c141d00c1400603da0542809240c007107a56400d09000109543d0b0400180103c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 751812311 1250 751811061 751811063
    0x50a0b0f0c0307050f01150b0307020d0e01020a24230402010804020406050904050d0201050c0f0304080c0307080d050a06050405060102031207090b0a032705071202041409060a06080f0703 82
    0x200c02080107074485000700280e4200360b07000030841c0c0170001a20455402000000c01906a0420110011400c0c03001030003202d005920030741c0240300e84100c4242c01c850040410700160f0450283d98621004105190302c5082000141083d070750141c0c1c0d0880c044812654040c000500054608a5601080440d4000c0701e501c1074080c20050400d90300c6100080040c05c2a0300000c4c0d01403138440511060100c0005c944031081e48640080005e51a9030000ba865800354141d007110000c01000018002200e0101816500c22188100c0e401c0410940d600015500203400302d1100700d54030350421160b142035000314801007030141e8040040381070050000351244207200c20305048861117404140c24034402d50018000349481000191581c0003481e00502600e150094044817203030311056122149080e0100f860b582c1c4e8407000410b080c1f442c01c1c244600c1c5406070401a80d100e81d46d180c02c41c8a0845100f052440f1702c820300081c1c00355150200071002262141d800c52402030744039080040c0d80d60800125032041d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 751813561 1250 751812311 751812337
    0x3120506010302040b0c010e12040f03020f060c0106170106090501050a0302011b02120a020109050907021c1e0c1a060a1802040503030c060f13030c11130e0d0306050a0b 74
    0x66960354006802074441c541c07100341c800c000043d900190140c1980000300c03141d500c9064070440b81000b1404810f0b80030380e02844490f031442020420052500d181d0181d601107010b0010741c00d2184000a1f0b03801c6030255400001081281040035503240400e00c1280090f0502d59810080c07941040c011074015866408001c6c1444004090a0301189000d45400c3c40140e0040558840505843e04e00f9250310009408a0105d07084c06008207482c41e10b10f460303d00ca900703981c1c0140a01800351512035502c43c5c1400281060101500e1400344000303500440d418241041c5c1c0310038003441a0b501d0403490a20110948445003100d60040c0070581d03450032094400c80c0c121540c03c0002c0061174600c0402403090b0380c03220383d00d44000142e000560801040a5121780300c0301801d0307001555000a2654886d20104000703000402030700704000001e45000e015150481c025010300c5c8030107c2c441e100001c41e07002903880e850550041c943d28104a07070502501016000a5a4003102645001c2c01001a80a600041401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 751814811 1250 751813561 751813571
    0x1b050d030c030b04050a0b0120060f0403050d05011215021303240207061406090702030304080a090302030a05011b050403030e0402030a090b0411091302130506030f0106030311190312 80
    0x40d4602c80c2c3c1003a080108000c01c2040141403446030f64005122205580e030210b103505203000f030714207000800c3c07600e06c003622380c042c1c22240d56000010301c904030014001c80c2408420301450000955521803180a400381c0d1031942b5a0418a08045000c0640c000304079100c20700400c1906030081464813504209c96000104114809503901c41301d08030070351031048410036480440c0035801d00c51140c0007031481945081000303800c2d444000a00c00e0a542c11100100541d00c10004a000110442c005000340001d920b04885800c0d00c9a0001c0e00300740c00c1c072405a40d6a0744510301d018030710340b500301d8000c091041c07411b01c40d00d0300c1e103182e801038254641c1e0300059200315404000070b039410080e90001240d070355008808020310b14140c60400d0200a1400301035024a0701e200c00103010f044410100b0307015980050178407a103031141030b0211000c3e10000700402d406000350880c07211401024001d43c0040c5120340c03900b0054900d440041441c002c100f03400c0447d44c0245d07e5031440800e403c01d01c070491182c4a401c000c61 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 751816061 1250 751814811 751814831
    0x103210c1101020709020c0105041b06140c0c060d0c030b0a120b0a020c19060c02060606042c090102040306051005210703080a110c180112060b060403121b050d03 71
    0x41041c4007580810f170050700010312005121030645c032052090b80318021100403041c41e02446166613240707000d40d03800700c0c0c041c800c0401d8055a850242c44540d07181c80c01c07541c8441c01d0002044154102180c0c05d110b4680b18146c00ca400764050051400042c425075588003400d00e4005401112491000007408103002100403039540103480e0100c1d045104288111034026401e05080451000045020303942e0718600b2144030031051001c80c000d801208002c00b4241003d00f4403000482c1d1090121084007101c4800d56003080460304021820703c544808400140c441e407a40c2409400d58000908019030703085a036100344282d6441c140c0400300c565241c0c0c2065901d40c82c55040c54603081301a00f010308004001b25840c800301d50702c1314068101800300302c240c0d9050001203040c4042181e102c1c0c002844c01c20103100600060b0813107171080c100d0034002c140220745c68900380c2c01700d070f8154030680096038030080102c914102e850700700482506015500c1c11400c8a040261102c5840c1c103409207281003050344660302c0341c1b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 751817311 1250 751816061 751816063
    0x1509040b12072705010509010314030d060902190503060d06050702071e06200a11010306050405130b01060f0c060b0d140d090503161a0c03120103210c110102 69
    0xa001501c04003140e07900340d1100c0800c1d4030070503400d441c02c0441c15241c003204240c0e01a030040314105c81014100f02e0b29a400c40d611a52500000b0101007003600c001c1c0030003050251117000700c800030101000016624800c116443d461841ca09620b8802c0c07100810900915423180b00300d110610381c0004000a90352600d02e022814100d0640c0030340400c042c0003800c4003039075242c1c0c01140201c411035183e0b6001e2807500c6a480881c40441c0c410940b0a4010340b03483e42c00300f0704074101c400705108149400241d06807114001400c6074010fa4001d4240c01d111402d500800203100c40c003c0c090130060030320000150100710014805405028000c144035141d41604010b0380303a039802031070320300ea000c0d11000b40140e0f0300c1c1032542d8480318003600f280018040c4400088509012a4182811071054510211141801041c100b8440401c419070595141004032280e41403040c40035040311078055a9020055146003401843d80c4120300c0e6114058601910b000a5907402c210000380c1c559100050b00c00e58041c540050b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 751818561 1250 751817311 751817329
    0xc09020c1219080f011214030906040902041d100b0d0b090406022d0a0e060403020303121b270111010e0c120a120503040602071b050f1509040b 63
    0x60007400815024000601c0540d400a682d0060351403100554074000421000d07007003031140e0f100100a903000f01000c1565020100119001d9a08503407903d40041c000c1000c980c450352001c201d0a0707001c102030001941d40b0411030406002c42d02120694109244850004d82041c815aa224000050844150314007608642c980c024010050785d003900c0c0034248000603501114881c2800441d1980c51158000440c6203800c0c010f2290340058100a02101c0503101c42001141280c0e00120500c0300000682c1c08000804401268140388209810581d9912604100708002c450100300140403500e2040468180703c84540d0560150341c15041c0c0220041c2c03981100b01d030103a101942440d07140e903941d040000c3e001030b10010558403815444803000c246a211107481600030950126411300d2060244610040c540040c060200140342c444203a07107114183d0a100704140c20031041c04810400e80c602468120b4005105039160301481c5140b2a803070350a441440e45451007941d5821810149454501f41 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 751819811 1250 751818561 751818583
    0xf0303070819150f171b010c0606050303280504080c0f300c06031302010f110a1a01080c0a180b03010e1015060f050331050f0a0c09020c 60
    0x1100425603110040048098007501614502c101c48503c178110b031820002d08800b90a80411211408284940044960145500003903402945031000418903a509000904031000c10302d8600d401c0004e2030315004240a00911180240b081c1130208001120001c54040200401260f1100c290761020000820001803007580510003c5c60750005008a0b14510603403281545140c21103c02c040032400304401c0303101c101d42581102280c2c060000055005017903c141924090a002c940c5041c00aa100c1c54600d0068007915444080410329014580c0619141c3c094a000e401800c400b5100501091541a50748510040b001d1403a050719598503aa602400e05003000070004e0014020b48901d640c0e491024019117007a80745000c1c0700b140032038400344486040321510b460f42c40203103002030010364030364000401c00c8202c4280d00c01e100c3e520320b402c40f01e5880c4495964422144680160602e207240014942008019602104d07100340400e0443c0e800c03008031085000c01607620542800014284480101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 751821061 1250 751819811 751819841
    0xf0903150504080f0a09030b060411040323030d05011409011d09100e06010306050a06080604121701090c0206011e0b0d141905090307030c0204050a0603230f0303070819 74
    0xd91440c1060f07125050001f160701400000070f207034407407904000c2200e020b002004000b100c1040100001242007040724080c4072085441c98191140700700a0341143d001c4140c40008070340d030340c00502c03001525249150105005413104c510b15030401207000300d034031040d0420944690210000948180b400c12007404401c0080002f407154041b003050b44c13942c81c802804200c50310341c00e2400081000b142c134401d96003203c90746402488283c84503119200143e10f100b005004225034000840e030b002c1c4001c59130500a2290010003c4c020040303c0c03000741003c5060300641740700081c20140242e502c000030603040a581d0724610003652a0701c1d408030b1400400903000c0c0c0402c41e842c1c2ca01040034610791016001d808620400090100d9520001803a80300d114060300200800d81c0203c0c0c080c0076042a6000342c0d885480b880000400a480751506180b00414101f026070881e01c1240303e4156180501c411851600030038004c1d4154242107030081e2007040020303c90040070800340070101c43d039182d0341c1000d900b9081801d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 751822311 1250 751821061 751821067
    0x403111504030311521e09022d040b03040b0601110c0102071502250602061305070b0306010c021f020c0d11060703090b0d0504030905060c0606040b03030c100c0f0903150504080f 78
    0x400c05031300c00009490344c0d2440e1b444000c000078402c011402150507920301c003c60783c040401000160444044041440141543c00740008a01a42d10320011402280910300c010f0140c0b031710000040001600d0560071071140c1000710804d8850742c0003c0c80200303480a8022011a80a000c9412407070705100001030000100c84441403c02d80003820f80342e0042c2c40860f8282c8280c1d5940c8a860090450459402041d80e40008810040f400e503041c06150000414540041c12454580028000780d2604131308140005440c082001c880e901048611088181543d40f8404c1001c5511880707016a030b42010f41c0e0203100001800c1041501c14200000909180c0c210303e0388540078650410014a400c9071300324081590308101051510300340d020380d80d11030b12440082034181d84a01c2880050010950f03400d0305840280200c01c0103072002c2c00325050440e041e1000003065418100014041c001185440b81440030401040c0701064089180420802c0a800b0118080e00d85190980c07a43c4244843d803801c0901c04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 751823561 1250 751822311 751822319
    0x312071101020610090f061511060a0b09041103120720061c0c0905030d0201020310090209030703110a05180f0c0906040311150403031152 61
    0x100240040900035100c8030100c104640059a039103105464003080103102484c02c00580040e078210b1006401e034454045602d50344d03160030f030205446610400002c03d4005818181820b170401025500000918090143c2510b81011071500c20f03002c0c0000d4018002c1e07590701400da4508011601d041d84070714202c1643d40045040040c4649035030010110071224400c0030050501e46901034a24414890300b01381c55800c6031f0703a0004010540c0003030f40000d21000380740000c1c855805100d030b003041b132003103400159603850054035400842506401080540b48103100b00e0601e42c900080701c800ba2903122015803070907140180004c103e41c105600a81d4400b18100000c41d0b20340b03035001c4644c02903407640d00ca4421a140d80708a0000780c0a2100d241d9008a4144400c00c00701f4440c401034829030401500d01c200c204900e20030f40c0703803580c000e40003500401c4002910404c40d0340c0400001c0d50454443c9003010070008207045003060f0803500c0450050b406060020058151030440f40c4c103040000d5000100b03505956 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 751824811 1250 751823561 751823593
    0x6010807051e07300302070812040507050a170f07030305091302190504060f020f0c010c0609050f01050910090210080c090904050c0111150c0c0715030f0e0a0b0a05060f03 75
    0x80c5813540305401c80340f0461402802d01a009490149a1020486007044038600340d0151441c1c00900035140c0f0b1041c050000341688500c108040a07003c05030184904030b00102d07070140f0b0824503c56041c82caa00c51603003000070a0740720082e00c2c04c4050443d01d81407000d4560b41d02c0e1000c0e01456464074181c81c6880002d410441c0c00000400071141d40f5260503048200f1002e00343d0301d9a0740404d085150350000581c0205940c0b160482e820324130703c20000091400500c1d29481d02d440701048011001d83c1d500e80070b01020748010407002d614000001024042410310740d021422a0b09104160001d0024120100e60200203841c1610341345c020142c40150149028203016030365960641c2054003040400b1190f075905500071a8807492420003441098107038903001803010048e4441c0741c2c400e10500900c0b41c00f0401d00e08210600d05104c00039a00820034a10811004042350307007480344d5480991001401e00b0005a014120603803240359060b0000d1651307150004522900c0f62288840c2c1c2c5030281402c1032038071007030b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 751826061 1250 751824811 751824863
    0x39070609030c090513111c0605010303080603121206040609241406160515040309030b01060503190b060f130f0509011d04050a0807030201090b06010807051e07 70
    0x1002d148201c503407603540d4508004444050b50303c00d00100d80564903401060501005d00b1407540c3c00360082d5002402a44a1284410325520032110b4540340c0004009060b40907889640201c1c003240500440c080a02180080788a07031841c403241850038200140c0d1a40d22030b40206c00400300c101e8107014a500c110501096080101c203211010380700d180700460300010056040d1111030001c0d200d24501041c0d10740e10340205042040072101845007900716800c2d240141c2c60b6034001d51080e2038040006d800d502e89203042d6201600b00000704070701801041440d14103500e074168181c0410034001440000c40022958a05c031300307c1420300401000801c105440c2a01e546901242d1000d064001855198010028860028440c0003028400203112041c280e032018980c54001c0c0c894005c84003100303c0c950300da4015800c102015005030b55980c0e052014020354181c11680000246402405854440005042800b4900000441c1d65a5540300ba0035102c0010031103034210340102c0c0c2d1001c240340b41014198004 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 751827311 1250 751826061 751826063
    0xc03180f05071d0a060b0405030705060306060f04030c03200f100306240e041406120a05060c0304020f180a020a212901050304150b0d03050406030605063907060903 72
    0x10b80790800c000340e140346d09010344055913070090140c8501440c0c101040260b400c00b404155011a0030003002e0002034900c402480210300c01d000080340d1a1441c1440092a9904d031a082c56402c074981100c1c42542c1c4410412550407070842e0044412200b4403412801807280f0b4200c0c0030076038080c48034640c51f21143e608441c01d400c25681d40040664807030781400709499801841644d50369140d0003040042c075003105142e210740145030866444c55020b403038040c500380007030703400c21030002e000002e100650620035052401e05400f681c00320341038112080b40380d100c45030003018210b5040c3c0c0071404070354052141c45044c95018940858000a5000403e00c000400e1040da60255442c840061382039540894039698821020584804c5c0c01c40ea01d07611001044003140d400d240106507103030701401041d5a2420b40124541c001c2d681d880e2203e00b0070b207002d0202c41080c0c01051084000740404480c81d040003030342c8507419171141c03414455502c5542c2510085083c071441103141c2d0043ca0701c00705d07203654000c030214101c2e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 751828561 1250 751827311 751827331
    0x9280f0b0a05040e06150105070b01060807030b03060f010311180c03090d090602030a120609020307080f0907030f0809030c1503040618030c030f050412060501090c03180f05071d 78
    0x202e41d01d20410007210015a800c00c020740008000400350700c031719074920a565006060652421030030b035803565034000c1c1c2600250041041d102c14416199810702ca182c00030301050b0b005040f0307410800d0300c04118110511001340032995170041d03985951510f03004034001c1c40810980f0318541c03c21403181506d41d0000c136003110851107106a001c518601c905901d0049a42940155141903030300d440840b64220340010000b401d43c0c4688002032078004900c000d6207c1d011a071b542c070106043c07104840d107560601404103c0326501c031403000d201240c2d85000103800107921a0071103950b0400e10000c2810803d411034650341c0076000c801c44210058180c401180f145124140c10001031440000d00c054120403140068001607001010b240020300810303410f00801c10608241d4180741c0d80301340742007010880761421583d060f2250010024032900d0300078541c01c8030039402c1c14004909071480d0f04075200c01040c006130510040c0c80c0e007101400801c0c07021001038014200c1c1c200c5444248207044020380b42c00c1d5500500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 751829811 1250 751828561 751828579
    0x114130c0302161a06032103040c03120c03030c08100b130815070207060f090b07060f020a0f030b030102090f0d0809030105130308060a0302090109020a0521190b09280f0b 75
    0x464a00031a040300d047c518a041d031201d00a40701d07450417060308010030894030801002d8000c408a42208200660030082d6500d5070081d80e05460000d090350b1f0786002c00c50912000d04140080041180c1358002550001c14032140c44a2003400c100900c1503860784844c40c2401800e40c0d0080f600e04441c000342c0b04001070313003c031501c440d034580003240c4c083d44428884002441c0640c0501030b08408d03500406065000d41c101140600c2e000d00c4030000c9a10415410780400c03100b400240101e60140142642c1520882c000c500300312070301000c10281440d4030392651042200b001c0070790400c6061016244504800b900820031407030092030040302034080e40300030341c0840d42c840c1c009000d6143c2040d80d9030a603903014100004592800c000403000c0c0d08145003540502500f4000c0c0c1c04015811200d80440e0512114000342034105440c42900002811001211080c146504060561560b4015a80015410031a50a8010011007a0184240007081104203604003440f559801e046c86d08400c14401080350070110b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 751831061 1250 751829811 751829821
    0x151d060a0e04050a120e031b030f0115050d080d06091a0607230f0a1511041a090604050d0b0f010501020a050601030f03051c02030f0114130c0302161a 66
    0x1010041254014450f41c0b1140900f0001401030014200056080c14080d07800c0700d4004c00241001180b1423401800c00b100c050803010b41c40d08121050702091140c008000b140300480c440e42d602c41060045030300500c030b0b1089003000c0003040800c85007148850b01e1b08011650301e411140c1c02400e40c050041c0e02e983d590110300b110300d21340035003110481644010714584402c090b0a0980761511460003000e441e0040c08803000031741d2014000300340c19604c0340850081c42070344400c164088903150319021160300801c1c401401071940c0700c000e5201d1100391005250710b8041c1000080e0440c4140d0b0415500245403213138a20410005c584a00c1c000c480040d5003114981e00d0380012641c0f03a4a190000c0c0659008500401c003003000400c212090b5402450700d2494480600210300408071250308040c0201d07800010030140c03064100129015003044140488413800141c0000d0842c0801d043c40c4403580c3d41c909000000078000d6044030b03a22084225200c403c3c0f0703800d04056107140080c044070b903002076444c0c0c0096 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 751832311 1250 751831061 751831079
    0x40312050106050304020f060405061c05070201050705072a03030c0b0721020d020706140103031b0f230f0a15140103080711031e0c0a03030e04151d060a 67
    0xd41078070318980c0c070075096680356020080311000460ba515040b000400001c1055183c00d00105508c4510f10005c40002801801501c100c0d9001024141164507000c14016065440000c95402681106185859003a40007000f2081003106005040a82c140300c4000704143c0c102c20807030340340b500894442142e0781d5541400c4c0d81d04001061a2001c07543c103c04420110003480d80070b0500302010740360040c00c111aa40c0c03040100e82500340ca02c14401c594a0040040503449050b03425851101c9502c2c014111290fa40c0d6003052344144801003040c414510181421b030780c088540c0c10004d100c10100d0350000800d09050f0b1f2034084040042c1c620780384030415807074284e502c0d006040290880141d20b404d16841c58440a810350400c00044648400d5010044290b0750300300900d0030704803003441c0c0100540c0405d84500b494481208056805401c5c011003c0000c03903000880c088e0454015103011410b0201550b80c1050000e0300d821035900c0a5400654400c440100001140310303100c143c071007030000d503251f203038403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 751833561 1250 751832311 751832321
    0x250e01060f1206050603062e05040f0812090409110a030303060906080606030712053309010c090302090c0c070b090103060f0807060c0804242c1203071406040312 71
    0x400c0d08032004101240680c10600c84105072a1140f14015115000020101e20f2492030b10300790b200006d00104052100c1d0000c0300801000f040d000c401800720b6000c3e15000dc90b94040c580149120344c1d81d460350074040c407950051400d044d1400801c804805500c900c1c0113002008540030f8504a10301e005404501c8402c000b0706103001301d07c020000c0c40e02c18580f10486041c889802811103540c0038002d81c01c52014400300002c04440050400c82c2d4070914605070340002090003c260b4a420383c101110640101e401156200a881d01598880c041c0c0d590b01401400e503200300002c154a600c50300c0d00008038044000040c1c034003600300340d0b0248142d0340c2e00e6000440d0309805000b112034076040604200075807030040c1d458005039841425280d08090340e600720340b159000352241007149c40075070f542d201c00496440301c2c00c0710f62280424400340404101c44010035142044042c16030041440c288840d88100c8c04105480b0520751110f06100c2c2202e003680c03482d465540c19603086011508003281142200ea40d070241c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 751834811 1250 751833561 751833569
    0xe04021215090106090e1c1b0311060a091e0c12080c06010509071e030615020109020102010b06030c0a0507062c2e09060605030303090309090a0e250e01060f1206 71
    0x201900070302c145a008261170314051f80d0062180b07080e805c00e4154100d0040d101000d000e81c407001507048180600c0781c1031040041000400301c2c078149034140000e070040480515000100ca04c6621552203242c40344904000c3c1c1c10092807151480c80c01d108200120000303194403003000742030341c50f580d80e00d00a00541400940c3d00300041900c600340c2291030042086252200a56454040b6140d0380e1080c10248144a030800003006035154480300e002d40d6024000c403c1800e80503079803a4070310301c0c00340311049190051103908002c21000180382c1c41804040d03001900704040c0883c4010b03209141c0c0d509003240e4078158021a205000d40d4506030389101d00150010b4920044103010503041102036120b00081c0801c2c001100c0c0035540d81070204140e24208065440f452086000f55600c01d546410010080c200405491007141428075a002814001c00e4020380c4c9014600c000004a180c403100a810a1090b04580c192502250002519961240101403072180b2503c035181c114010103080000e842007070107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 751836061 1250 751834811 751834813
    0xb060412061401151b020619031b1b2a0305070b0a05041214010501060e040e070f03030e220903030b1206180708031206030c01180e04021215090106090e 67
    0x10038900098040c40c000c0504442c01241d501011707586074000b8404d60014489410400e0440780780750500341e01071094200f025466811a4805e1481c040010080f051820907001d0024100d9081020006d003c0540e09108104511084c402c0403090703a00000052544800d8643d440b8604001401c0e0500708110f400e1800c3d59130303500740341500f401400c10200d0004502142c901c6c01e880c4c00325035500e400b031007907034041e10045d9200969200b1100030802503072104024aa542d8024100c1000f6032116910004100d03981401c0034202c01000a00085001000351548802a000f082c1c440e110442c2d00d9100402c4c083c42901c04110450070001807001110050071441e00d42d62100000c501140c03040c4001010f0a501c041c2200c80303250711164840c0c11074101603940d80301c10304000d06008651805001c5001c4411003860428944104510044500c00691042224030b021000205095480310a51394142c43e404008860074583e03100d01c3c608000d4011581c4903036a5181a0340494a0a014018140b101400740 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 751837311 1250 751836061 751836089
    0x80a0515060a03200d02060d0606030b030d020703060f18080405040c05071104050a020f0a020708061e0a0509030708041e0e131515060809010e061b0d0b060412061401 73
    0x944e81042456215a03202d9005c007100c03001d8070041e51074000802042012134070106034645030502c058250b0341c003448894442d400c0a403942c20f5895000540408a07034204101007203031a81c10007084020700c1140900300c40340da9202000c101b030015110007072085a00071b8804001e103a52004e002c0b83c042c050344800400541d0b1244c0c580072107242541003a43c1100c280340c00140342c0000851640011341c040c01c0c507000581c00041c400c00440c0390602500d80d00000c2505103c13a0198018407420682c43c00506400d8096a5540840c031451f408000340c0d11066405483c9540d61a1214500c041d614545180611f02c411b4500c800310703d025041080303a0082c0c91080c0f100000829540c1d03a161000815482c00400d285d0b00d000b140d07410102406110010305040d1140d03842824603229a5080d150040d20102c00c03540400203210000703000d0320720303030000c0081c561005032604801c1c10208090b24070000407983c4014042030204451200c59202281544140742c00c01411030407202444540c8000d11881800305600 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 751838561 1250 751837311 751837343
    0x5060a030b07021f0f06051813050309060a0908061b090d0311030d0b0907231605070e010807081c0503100905190e01092109080a0515060a03 62
    0x5181d80e95044029401551500504c100c0c1c0304841500c03100c00d561500382c69080030802d25246125881c054001a5100e48101141c420110a1a44050085110440140c4192040c03100a00c161500b05000600141c1d071440f202000030a601000d010300318140c010701004c00c7d902943c2211941e001d4001070031043c100f1400304104102c25030301000907000d0041c0d400400380459403e2006004008240d01e001403060000001c4c828006802014039040c09050600d401c042c0700101d082d50035400d040700f0110780d01c021700444620401901000148280701e507980200e100030b03000c0d040038140c441c2101202c001d2032b80c403914a50760f1004408010341e4110202d0700541c0e1648104019a884030070152000c03216656080c02d0411140100d980e1040303240e0054815200e080c25000351030281100f070009000342070a03912a00f00f00d0075a0100a200c1040c2c21100c60f12290061450a00525291040e103007580d1850038080d88841c00f01556013007000c01c034400a4058a0000d200a0a8075080301c00e5012174081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 751839811 1250 751838561 751838573
    0x100e100e090d0c140705060c0106060807090812030c0d05070e030c04060e130c05030d09140405150f130c090306110408120c0c0604031104151518030503040303050406090905060a03 79
    0x3013544038841c103000316000460b403903c2e901c004140e00d01502000091180c078003080100341d214060f18200400c0300f500c10401c41c200740050f00d0204002d50541d090b0b603940320031f11400c0d614460800e060129500700130401551541005084800e650107500f40d402c100001e00800080701c2d15800740300702800e0680301088401065100c0140060300c83c00d20907586940705c2d40000d2410741440c41000000d1101030307040c04000300101c44041c0c00d000544041c0401d040c1014541c00c021152079015000f1342c02104074221564070040000c00d03c176002081000100310300080205a50350034002230f40c0003414242101440140d0108850444400c5009018225008003128425500030300034604e2901ca20001d00305a80d5503040108002c5110307080c0300550001080a0100340c4880450201c002c41d01c2580030006006c410f8144180311a140c42c003074009111003003100c0444042c9070800340c082d1201007008000c05400100600a035000307622104203c0303a55a0842d000c0c8e6604441c0641c124100e90801c0000640b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 751841061 1250 751839811 751839833
    0x1d031b030c0306011512020702361303081f032301050f01050316230a030606030809090a0507021507110a061a03010504020d0b100e100e090d0c 63
    0x240040a0311618424100003c0c5044400e80084a0a100e1a01c4a00301950071855006540c1e0101ca025030400d452900020b1036800d90ba68050310007000400d00c90700d1081300c60f009003240c080c80c044203441c03810400703602100200b5510301200400d00100107d10400d520316881c13007002c46160b0301a00c40302d0031561002c040c6003445626000120244608942c500c10a00403035100d00c01341e0300fa61446601d01400c161814921144030b1030340e55140034041c0a46000c108000c03031484021a003000420b030f08540450076000e425440036080915050000c000c0260340d1000f00201401200c644030580c864408001c1210f4050701c038840581e115440384841542160382195005902e4203041102e060b40703070001414000e001d0003c0320b895a13581c0f02070140c0109000c00442d074580a41c001c101d2890194007042c2a51181c0d00702901c48100100040c1446d1410038401c0302400c0c11480350190f6080201c9000d911982074080c510b9400c00000019041200c000b41d64001840c150355801c100c001c03d07440388903c8034 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 751842311 1250 751841061 751841113
    0x708072901081506090708011a040b03010e1017032b0e0d090b0901020303060f030703231b1c0c15050c0c03030f040927050c011d03 58
    0x140d0400d400a09021186401d0091104001800640c0070030310801c901c400c4003c0105114602500900c5041980560b4480c1910b81c10040d403240e050b400c8104030aa401aa8460400c0072400000030039403820b1840c5141c0941d01c400c08070500c00344c44600d80d81e1128914120464182c1c411f00003100301600080182d01d90010864405100c04c0d00b215038a015a0301070300c1420703400d90001c0d4a0001c01980070960800620801c5071030381c145290080000d44911002e80041d1050301000d151885580e014000000255808154040e180400100c0e00e02030019101d232031542070040250080640c1e04c0200c12060b92a0f000f41100d8010f0900039241801071210b000076250390507000408100d4620a1510f10304c24191511065103410009064074036100003200f01038002e4000703001403c0c00386542000d481c00c0e220420800310746800c0d034941e4440454030a100340088040c00c0644e84043c040081000294000c080e680c100817011400109501d04020404560f0183d116090003488218980c460f0a128 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 751843561 1250 751842311 751842353
    0x2403020a1218030e01030c09050120011404030e0a1202040905011512141501032301110a020d0906120b030a29090a0309030303020903100c050d060b070807 68
    0x51100507000002c44403000401000701c55180700e07940c185500107240400307a81c02481c090040b10290f110041c00401684581c9040c0242091000b81f401e00b000d05002c610f2564000801411358020324410791301009403030540118500c00341c0d142d401d00341041800140d609034a0324210070180b6900b80001009010000e55041d581c1d01c820019140c54034100300014010a00e881480c0d207034a090444800807490016085a840f00c05151000c000341c031211030450342c01c0040701c040d2800313440306c90b0701c0100a0040107609520f840583c5119000c1400540113000d000d5003150080c4614000684070303002231780140c2e00030034162110145002c204e034214a4580c00090160b030007c0c80255039a000c2d10400354528094071040318140c50b40142d205000d143e011841da4000e10503d400d5440162024425010241c02c0580001d0317211555202001414000001400100050940365000170526041505541e025904060b00092504041c0050306c40caa5040f1810303a182c900c0a5440300010f00003400c4050035 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 751844811 1250 751843561 751843577
    0x4030216060807030b041e1104031707062d0b010203040b041d06060432032506020c06040e10030b040606050405070305070c030c020a0506070c0e012403020a 69
    0x1921411442900246003945600c412824000800340c217880c0d485060700d006500c3c000300011500903203c0c092242d80203030400001c6a800300d2030009a5442075800281148141d01801802400c83d00700402a19000b0402088200030b030080d0310403050026213840301c1402c00c1004c48002d112280d48011186201401103034030302640c1e2806d103c02c0381c005902010010800030705103000c80c03402c400703816800b0000300c42840c40d041c14411050400642ca4511b40d03030f061504d01d48002c60042c04582606050340c01000c88001180c0441300d0500120700c9184580200388000001481500000c1e82090130000203101904041c14000d4110080000404068002c21200c1d80000482c0c1c5640d043c038016802540046541400c5c202407000365031000c1c2c02d2004040c54141008105a0700c25100032200b0f41c58580a0007002a6000195103008503400156011038000b509808214158524808850100210002c1aa031350380340b58100101c522154503842c24803900f040113042c03207036005103401c03a514180f030b43ca = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 751846061 1250 751844811 751844833
    0x8070c0b0a02130806160207050105040e220f110a0617040602090405130605010e10120302150c090111030a0c140a12050c061005030705041116030206070923010503040302 75
    0x620f0b10b00ca540140d41d150004018012076544100d0b00406d0720440d8001031240300d25080008145210f140700700881140507401295100c40a05c4d01516070440c24a04810113500380c0c140740c4c408440243d021103401c240f488441403541400407243d81256460744410300b0a140070328140c00101801002241c2c41a4200300b030100035501d500c5143d000b80e0b03000302d1801d035221041c54108111401a00b2491583c1e0300d1200700320505585035102c00681c1d186104215210303509180c103034a40b0514240c59908420f06008101207284e010018110300d9400f41d80d2075890501c030b5086152240b103081c24040000382242400c07408030b2070070071b100400d0003075400441d00030400c039841c0d20f8080311211180700b000580001e0051500041000740a40003803111a041d0720f094900b600003a0795001e103105c0e40380555120402001d013501003d059503000d29610400742850455031400070740701c1004448290210b0560314010a401a1140141702440c03600c0c0000401c20000b40015161a0030062084086210f0409080 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 751847311 1250 751846061 751846087
    0x31b010608160e070e090103060207080d09210c15090203121c050105190e090a0b0c040e0906041509020d05011b120c08040624060e030105060108070c0b0a02 69
    0x301e2910a11141d1103501400d000d00f0321240070024224104000380103003c5840d9a55081c01c0c1c40c112903005400517a10b011300d142c00b4006010320036403840080d2800480800b803182c01c88520708542441002280d00310001d406c00d841040045801420380031902d04445000c80d0250701103020507000504455020035000b41d91020350f403001417014411101301f141c2c555500c4050280e24050042241c0f03c05d0b0109604840100c01790991080800c0034140340089001310a06115010070290051400c2c4843c0c9440b071403442c081d5003e0720030000011810707000242240030200c1c0d01801294071102d080b18444030082e0b0003019203521a000c2c1d0f0702c80184510301000032003d00c28054000901d165141262959900142c070350031170308020383d60481c02e00a007460802d922803416540594001c40001d002d044440e012040c00840c24504810000101030104269402008601c08210114000c3c80103a5404004442030030080c0c0d842d402040d030018044000a50040015521041d81d07400142420071480000c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 751848561 1250 751847311 751847323
    0x1180c1e0510020d0e040e0c1e040903050c0709051b0304030504230f102705180103050c0f0904020409150f061d0c1b070302040c0509130e031b010608 66
    0x600942d106003000c541185c0c2184001d131002008607800c02206001036055501c0750310003c1c2c07803403140d092420340c10701845103030034140c2d0711180240003009500c02a1502500700d40c0088040d480d903100c0c29200003020b00c1b103401010b02c204500030001c42c0c0d00034100c1000c0c07050740014004406200042c40042441207107c4001c040d003030803a00c2a0b21240006006001e400d80100350007034050f00503031103a139600c1e41e00089000d06240c00100ea00f462584070801800d40003000340c225560050b800c00018002ea101c0003c1203044e2030098040d10341400255041100415000c05055004014880001d0151620340d008078101802082c81c1e45801560520820440c2d80119006844560715102807100ca4242c4851a09448a420751030705d03181031a2000c0b072501d0168070301104890110030b0000a5040301482003600844c1d0281040c080d90030041c4014080d030708488541800b401c403851481c4008841070042481d4848003201031850010784c6980030007141c00b0500e00300ea10350b40301e260000754030b07004000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 751849811 1250 751848561 751848589
    0x723120f0a05090703020f0d0c0302180709080304050d02040c0c1506080f06040b0402090c07080a170c0a0e040b060f13060305092e0e030d0e01180c1e05 67
    0x1026051420107050400c840c07000d8810345040c0c0c001c050520050b110100d8117800a601122001e41c480c0091410750031550158100940018102d02c014003101c56040e18140a0f00094441132202902c1e000c1c000c4d964040c911032980e0050101c0c5a20025040a030300115a908080c500814070b0300d0766840381c1c0101650074108030215a82c1d424208400141808511030510f140406400c007401c1507100d0070b00d81c04000c0c001034400c00384803000c02c041549190458141961001601d81c444030341410190451a00074150080c0541c900300040508504408507078651300240c468a030030742910400c0c48002c0c8012215242c10200412500c0001d8a170b4a02a0807002030300201d107158182000002000c0c0c480241980700e1a0744480c40720040340d4403016806480c0e00051641c0c0810255022007140a4402360124201e1750100045c4240d00441d1600617403140040c9038002d104d94110716080c1900c10001d510301401800301c402040c404900f80c034a0905580040d0701d40c0b210f009071640f00040b03640b00d104003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 751851061 1250 751849811 751849831
    0x80307030207030510060e0c030601020106052d0603060108040b0a200d0606080c07030e030c100305040209061002070501110c100c0b0604020a08040f020a1e050301050a0203072312 79
    0x1003c00401008100e000300c0c00c100b41ea0b00f402800c1c580200e8106499014180d0a149000800001d0250f4400d5000c00014200148111410074464910300e11070b04e000040c040700c8480c42c0e00340440341d05252003101d000b000103a66054040d03545844900309850050b20101c04151248401400c40700074035284141018605902da60f40d81f0302c52801b0041301e00781d03030100050166000030046d185009030191600d694040c240580c607070400303400180c1030248d0820344e5588141e07110801b1540c40e503d03510480c41a8800d442c04201c50f142c0748200120078603014513040050b23010640c00e21440d4412a88414103c05040c21a006140345100041541d20441510000180201d1412040c00720b86d561607a0841c0b01500c0c11450801040401043e44100030710192070318429003041000c6403181c201c0344009200455942601289401c22000f09490318415284a90700f0700f030224072244c0341442164000d02c01ca45440304103807e0360250504580d640c2c0e5030718003140310912141d42128000b0861748c2c4030b500e02c42 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 751852311 1250 751851061 751851073
    0x3030605090c0a02330411061308100515040c05070507060e010f0309080d050c0909091015081e070e07121a030604030e0a120b070906180603090c0803070302 69
    0x18000914042d45940740003a16200d0352002980d22502031405500c10303505448660003075030740f400c200b0307440303c0d00d40c1c0b01c15048100001c032003800ca01d4406409c070680d1148019030b00260038403035090059501c141c51751109015405150185480c2c1540450110400c50410500302502a21603a0801c21035900c610040740c1d00030f004c0002c6d0346e80b10900700002409420104144222601c9492050140341a0039048981d2000824000c100c260141d0314150300090407040289020f24080e903c402c54455001140340c100030840100516100c151800d88168030010328002c0742c042c40c1c0c00640242883d02100c01d000703850012800c149070b0080300307200792226250f00e8050b01035590301c0780460b00c07a40d1103d085220707210a0101d041e900071074070359002505460f2aa10383c0c2c1d0750b8000140524510390242c18032a110307401001c2004a82e1019900c41e100e2034855044081c1d13681c10558800801e40361307134418050714480078402140280d00040c0064001e0844504282d11402d00c10314551251a054015074818 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 751853561 1250 751852311 751852327
    0x50307020301060803040b03070311040305010c02011b0302070206070b060d0c09091110050d0e030c0d030b120604020904061515180611212110060201051605030403030605090c 77
    0x24092100100350540056107030514044001f0040e01014001208041d15070501000903520001590040e5030840000c004115500e90007a00810200c506607200c1c0c0403009082030b1a9029100362914190040c150f40d00d44580e681d1203c040c8000240b515034482c40c1d400ba03002c0803a0000e00c40c00050091850000380c0c0030103d04000e02c0d182ca40d19000c61203850440c3c200f031035103030340007040c2c034002040e148001c0b80e054882c200d901cac114017824100100e944a4602010001030381608800502d940684401c2c61240500c520340751107082c102c5000e500440710364041000241c079584480105980c000d507200c3c41c1900d81401104045015100d40001003d94264080c40101ca25146004143d541040201d40d1080080941c8a00402c0c21010200206c251242a00c10000084410f03220b41508500b045080011544111810503201e00da9082c012290101d6070718014443e01d17006a00c48080328403114109103048a1950000f4070071010907407100300000c1e0703c0d01c3d60a02c66005008080f10b540e15070800e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 751854811 1250 751853561 751853563
    0x5030d11040f08010207020f120a051f0e070602030708130e040f11032d0111030106081608070215151206061e0d03030c0215270a170d0b0d0503070203 66
    0x1c036400c103960f141d01c100200001a40daa0304001e20701030003079820280c1901502601030810b07503584000b511030301a2044181495205071990544a20056010000c0d004100891692110310780a0400036a004101900100b0280f0003d0042001940400003800d600c0c2c2500c031400c050b040d1411640070710510045010000911480a94075109500511030f0121150000b9140312074207035442440c1d82d2110b041c49000e07a080d0441c1004130b0704451313a0703660703540d403054001c0c44c0c2d040c1128014540744411000d48145845000300078041e0310503500410840c60088101078030b411001d0403c0201041c198940050741d203480c410314070001c1c0c0d060040c00301e510380f21703042c443c0c09040da005c14000d10140c0c2c0148101541c0d00c8038407424407501072030002000d040d082400d0b03107480ea91140092445010404220300201103072010340050810340e02070008145c4e04801d1a5488200c81c2e0004c00a26010175120002d6030194046d148507114102d020540d030b0503c03000718600002070b41090341c6540002801401b5814 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 751856061 1250 751854811 751854839
    0x303090b091c1806080624031e13030e010201140421170a051015020604170903030319140f041b12112d040605090112120c0c0b0c060115170405030d1104 67
    0x2740c4030f810f552a00340c2e103454001003003800040900404401e1300300c0d02c2c1d100b540180c0318283d0700395500c0e610341084d0400701c40155210300301c0c0080960203101c18450a10950b9544643c20300c5058489003916a40c55400140200078150105503003064400146850703404450600d21103650049d0119003804d08050618400c1e01c000b491003420b0411070440d00b40c90000032079901815401d900011000481165800741c69200392075450b00039504140607040544420b01030199114409001d280703902d8a141c0002d001983c4144000d184840b00f5001c0030590300601200d94260003004110b070445c58010700080b91403001000c00302c80040d0f5682600ca070420344119000b404c021219641c4540c948629588100d0b00800000c01c0800080c0d4245400c50140107588026a07015115803c981e0301c5458100158119841004aa200e50300001688001841800384480e840e569020704100c025560350081d150040c100301ca07148020000300b10005d8461044084e070452094a041e0303214607104585807005 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 751857311 1250 751856061 751856101
    0x60503090708030a0c170409020408030c06061c03081e01060306090b0d02030c01111c0302030402030c040e0d030c02030d0203100e01090c1b0303090b091c180608062403 74
    0x603008021090102d82c001c200c10b505e8561000c03850078410301350000703940140580e6010b200c400d400441c01013407444000c00a011724104c400c041ba01c1e6030740e4103000c00070811983c0c42e21410701c09086c1885c1c80400d22071364081b40d011a96070b4000351800d8814050f40b0481c0b40903846080043d50b502401d204451032406050f20310a021200300c181d04071039400203515540e104c3d2100c2c1c14440c500c05150000d440c14001c14660003808084c404500495003030240c007941c1708403012071080c0a00a6000d8041c41e10703200340342d109901e4900501c4200e9031080281e008200140c1e994003944003d114100b562400350005607c40d000360442456800d1a03e01011180141a0000c01d065402d024492003070a50005450030441800150310540c061282000da00070444d038030740904901600401c002c440e034800170b05400158050307030181c0e410340d2120750220740b09440c4035480e40c4c910760101c00c10800244601d400395000311004100383c0c07000b0602440c00d8002c031424080c10000c1d4402008000302e1003c0d48090320001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 751858561 1250 751857311 751857313
    0x905060a150b13090c11030309010603061107050a14070e040503070201110d050d0b04060e0f180d020a020f0a0f030606080105070f0e090a0b1e041b1b031206060503090708 75
    0x181c03800101118003c0b07900600c4080f9039107210303170f00d5901c0c451803003401c1e12024403096070381da8100a0109406406540015a80710742003e0014508030480c82c101d0f80f980390084c2c05480031245035038a9424150450446070b030b29203e15507000c240414255107041c0100d00c643c00039a9194040d200142032042d0034142c0049981109106c208200d420034100d40c07600c0b00c1d1400000d0611040740001d8002c1c680c03904490407070441d0204019075207404000c1c0c240a0039000c8040c0d2525075001d2042070b50365180e2030b2000c0050300050355110050070100d0090740c9240c0d005014040054035900c003100c6403038882d03000341e4409480721001c1008140030300c94a80c00c2107507440c1804500d603e401000d4000c156903070006000316103280020f0394491480d84414082c0b08014442a1108030415034154080d080014a500c12803074054480010001c40c440c00083e0740b0b507901c0d41000e0080340036103076a0301d0288010075824440840b4070b03101d061410b03209030800b0302400d403200c61312030910862551038506103801007030003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 751859811 1250 751858561 751858567
    0x5190213210209040b0c07171b161e08010207031e020d08010506180301020a0210110711060304140105131b0501050315121b09132003010905060a150b 66
    0xb50f01c40e000807a034825003100222505440780702030788890f4890710001403c1da5011503d10664900480010701800c1c0704c100414034585111074801d1380707509070034003049a42e101d044c00070000b0385003034120f8801c0074082c5038400c2c0d50030b581c600081f420f80e0300c03ea0080340050508010500c12005030003601582503550b20081c110900c082c0d401800010060203038500ca0600401c0100c107902d18008101c6004601070000d40d21103440b403c01070740c0e4000313010350f11a009040c4400348050b048482d082d41c602503008600000e4034140d6909103c101d60001d0800c6e540301c04118030038984031909014260003641d00c1c1e00b01d001005440d00701070415641007031808480c00c181c440c003040b5a0f0303404030690360002c3c15140c0901c0045407060014011038a001940c690750300810003c490141490704808100607015034112500f82d681e0794000205807090400100070700c55403c0c030b5480220000c12490039441002cbd0000a5040e0346407111841d12004032030003c461034031079800200d4002000350728002800c2c3c071040141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 751861061 1250 751859811 751859813
    0x30030112030e0607050106265502130513020f010917030301060206060a03050a0f0c030b104b1707080c01110c040519021321 55
    0x4180300c6841000d41004400707045012182d032048111524958404000c0145a560310240c8204d102d501da0303011180c05034081244107056000c1801d50308206411250b040950881800aa1880703a2000707106400303540d00c04254071020140d0329007401012601e503854120b1820f20420041d0590410704000e420b040009005c00445002540c2408581c12100020301410540041b980d82c113071544202d00003e13446441145454001c002141694103d81c261507050f0354880c288060541e0520008000c0d40c4200c80703d0740418a1010b00307500042c41428141d5503281c5c2da8039003003250344069030090807012204404001c003040c041020b0b09050100404000c107440100f62405461500d61b040003960200c83e035405a07181074482d190070107031126000303c01d104001a0381c0d00766141c0341ca0140c00c0c141d00c03440705441169805020303801205502c0c10b0040c4114404d407070a0101520025180f1008418082e4860035581050b001601d4203204440d01042c0302da140c02444103c4c520803051441c032000c2c406841c84 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 751862311 1250 751861061 751861079
    0x1305040207031b060e0709050a05070806060307080408091e03060106081e060310110a02390109050a151d0a060822060e1507050a180503300301 63
    0x18450f10214007514852111a080240251040c090f403035400d801410804184101c2c15400540181e03407070502041690785904003503501e035800307480b2294000c07014000500218484c07400e0030f5105210759005410454140c020828140c190b2102d12046803c815800b000d03400e00300031817401410289001c2c609424000c110903094104204142803460100001415540303040200d03000130320100f44104101440d031811203240e82c20a111030070050007200c10100314450200603c1c403070303000300c0c40c0810040701c3c145140b04030340c2c10807601c0c3c24180100d00f40c00042070340d90350221030024542410aa0301c0e5280f54807008200000951110554800007403140046480b1403904406036a00703802c0241a5403110b50045006114a5100e0b100d8198444440800c20104d904a003d02207501c5040350b44000c05180c280400c09000c5030a200098010702c10515014800c1400d400700b504409484100e19841d403011905000344c2c005000043d51408080c0010681f121140e805c00d4104415032a09650409202c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 751863561 1250 751862311 751862327
    0x70b0c10141e0c16020a1a0301081002030106120507020109050d020706090909080405100c0602031e09010e062703040902031605310503010c0c02100905090f0903070512130504020703 80
    0x8003051341405031150701151a0a2002809010003203403800b20040000e9420f50254000d0281c41041e0054403145030801c0568002d0b00d0594001e5291301c0100d5420003c59402464001e00001c119900c403901100480e60a00190401781e09650160585c1030814101070f20007074059001c402c90618101d05040071070880001d840542c1c0301110110300c1b001c69008111090241c020018020610010510022210100e40c011420140100301d243d59030b03c442c5080e00702d8121402c0809507400210008844603d1901004008240ca0311505200410a003002d469900550081190154000140502c41c030500408614203640c82c500b00385010b1030590241400340002100307069818150b1050321702070440035042e50242401400802070140141c1d0001c2c81c0c0911040c09a010f0050652a01c0039140701d50060b00c180c90700984102401d0b21900d0b061200f010000300519024001408601c00080043c410600300b1950460b0842e151090500707200000c10090b07000b40d2007584104100c50010303411104c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 751864811 1250 751863561 751863577
    0x705150f1e04060f05040509130521030402040e060105010c03030f0908180f0411070209041e200307061706041b09090e01090203070b0c10141e0c 64
    0x14040d1a155111040e900c10300600c104012441c24810021040c03400c0c1d0700180c03084400580d40d89525400d084000d8a140c4254010f1a0300a40460001110f80301c103510030580e01c0b445030b03040b120f00d0300d046403844000d52100030702e1120008002040c0419481d003030050740c985140324000741051b94941000071b420030821a00084c14540c0710213805449000643c81039900b42e80225072544d854000b445404035030b44c180d107a994070840f2031644804803801c1034403a103100449001085031a00792150208100c3c10303c0107004580c600b6500064007a401c0d410440303036207158800c42c840d812519425000c404078080503000d50703019a028150070020341d0ba006a41310107850711807201c0c00d880d40718000820060400031100c0c1144103466070001980d95480030760b01044030060341007006986001040b250a83e4082400a507240c0d00c80c110500c0306030155002882410b11300d4048072100141a1960401d491142d0400c1e201a0861070800120000e07416403900c00342d1150026510524100400d000c0310b00900030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 751866061 1250 751864811 751864849
    0xc0c04050c070c152c0a091e0b060901050c0304170a030207170c120f0111030604060f0b04090c0c0506010b0a0e040c020a111503010f050414070f0c0f081809090705 72
    0x400800c083d515002000c0310117000e0041d0540715180e5a0308406030841c0100c1d0042e1f02440643c0c00c1e81c58120f072086a445620061100d842d050150004540b55006683d0182590008010010350f04c00f080741c50055118805024180400050801030b040c01d086130300040d41c1010614403107050f03244c0400c88100c0d0340c0003200c0111092048010480c83c0000c40b4092002d00c2d845d0000c52a100e82c4400302943c401c10b03040710144990758880c500c6480c00300c05481035a10100c0244800d212211003074020102c1c100031860a402171004d0b684561780340030400c0c1d0000c10004000961343d204964001d03400c180c4410281c0e4180886940104001c0d0f1700c4400c17841c084e2211355400740f107030010b075103842e118001d2030104043ca60b201d5858064103021b21900c1d00c1590301c102c2c5840000d1540c0c6419110062060031283c540d8020b07100410815a4001da0f8003104507442d198000100c400914858081c04816454501203064403102109008440401030501c0070b01d948404d00800c20b42d41e44280a00c03688622003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 751867311 1250 751866061 751866107
    0x31806030a1b08010503060105010c08040b0313080708070c0b03150d02040e0a0b06030f0a031b02041506080712020f39030d060905011a0c0c04050c070c15 68
    0xa8110080c010304511103544080c890129070b040358000b80060689100701c0c260748444c1d03a40c80040d0354507044400c00401c0244140800c000150302074001d180c1c050100c0708400e56642d0710342e0303c2414951000710121449840410000140b100c40e509807400390400814092a40c10401d081c41d0400d00b180030342c50b126041e504421011903c480e040783c0f035444200b10458400d010645020050070034220b030018001d129800f4090200c9400259192610f40c068581007040e105540304444034000e04902660802e460f000d07a40001c141c200111002031006175610821404e16603402826000d084401540c2c0c0360040c8401641c03c9220002c540c501d00c0e0401c4980114602c402c90f12446050301485c1004e40320046c141680502401300080c0032242140008012540e100c10f07884044038421b004d07210034040840710903415141d414000b804403030001011a4030048000002a0030340d02c040300c1e0342d03003080320220329601003140042c41107018081c1c0500031100c0c00d6045d40b009101360385010504045c2c603004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 751868561 1250 751867311 751867321
    0x1031812170a020c0f06160f05040b1b0d090f27020a0504030203060a090c03080d090c140319050a02010c0c0e0f070f0e011710090f060503070803180603 67
    0x1a6404481005040300075203540c582150004002e4128915107051030048078121090440c000c16141d10541548101c2e1607040061041103078110b411050070f42c180300003084089803020781c1d0400360107a107100124034480502e07031140b5141080c2d25a0500340070701219034010300c0225503451502c01507c1c0329109042c01401049210425815810000c4660600c0011043c0f51a0b5000000740b080e13900030b0b02100d803a52100351084045496400c0c0240150300950310a000043c0680000c00c103c48030050085607200e01916a814141e82c0c82c6d110010045181c02d090344142020f10240d0481041890803102010701c6898064880c03081050003810440c841c000c0c0c030108503440b200300002d40843c40844410b86000d0043c6d030203c001c20344009003c6420b010783c0f00409807003a4900b440c0428181d43c5c8090900c2a80d154059251000c0e00400c1902211440441c40e4182403003001010b1080700c8000c40d03c030389880c05240c10214a90800d281c90780040000d2013595411443ca0001c2503000d4602554039510 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 751869811 1250 751868561 751868567
    0x30206010e0709031a0402040617030a030c111b121501090e01240f0902030103510518061503100c031e020405010c080c1513030e01031812 61
    0x450b803c0200a45e51003451218100003404803075205600c2960200080740d1100344000141e12581d40c0243e041d8020044607090600c650006440c0c4505400e00300303000400c0510803030078294080d03404482141450042e0006240c507050700c2d45480d41d1760b00640585844e4000400c0115014061400c0103a140c034030350070803107200b5400200501e2850040e01e07900f05da41c00d50200f4440329440740681914404d00c0c04140007800c0d200301c9040302c1d07000315044111259052840c00c0c0401e003200d100105500e2540186184200010410a035224500d840a000d405030031075204540b40a004040c00e000403800c45240c0d4440005c8807034108101080e111501800768000920340004a54041c119a003013064415280350076400c0511007565507800711180900090582c4201d00942c8106800500c80d00d0089020441140090914071448001d580d41c0f490030000020700c0c1c502c2075400601a00d415001401459480030910300b0318402440e007442050b82c040000c3c101c45554181c0030301107180b5090003c0000b40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 751871061 1250 751869811 751869827
    0x150b0319020a090203040803190b0a0324060f05090f090607050c010e3f0f0702060906070503032505090105181f030b0102011107110a0e04060209010912030206010e07 73
    0x3c8000c206660720310b0700b4175162066401c10784000461b142040e804c00e020900307a008040e4080e10240400c200346140d074480003aa03010440c80395100f0365010516003910300c024000c0d07202802c1c841180340700540c9440c040c010032000007002c068050450b4800d000c0c0301240441c0d85904159075142064481128011446c01010300c811707802614072401909401040103000004080104c102c0c0c0e049a11140310b9003620640075000f40752800340c804010b44038105600d54042c041450015280d42d09014800d8046840c59004140c151203d510100c20801b81c00780b008450708001001d80d0b0341113450600c8001c00b414034042d0200c41c5040c00740108080461a0741180c0802d050301d0000c0240c8001d0012610a58807000000d10003800a420308041502550050240003600444044028940455900e50000ca240326510b47c03980b144814800103035000900c80072600480c01500f005070398213003500002d000c400310381d84182a401040040704011070b4020075594119400385801101541e60000e00700c442d05 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 751872311 1250 751871061 751871069
    0x31801030e0a0311120a02160902070b0622050f01030215130302090712150314150a0e03070c03030329060a0f020f0703030302130918080c0c130504150b0319020a 71
    0x5d00209081000a85c0018850410b0b203211a130010f0350b0b9142d0004034280c0c424103e01a00c4c05039420082241410303c0000d50100c20341d034510030010400c049241a00780ea106860414203054608018015850000355030011a0441032009103040120340e40d1a00b01900361102a202d00200302c00108018003500880b40701404902e4108038294810010b40000d1100740016100c0884801070012407000014070117a581d110140c10714002c0d41c03910241c001030302d8504800301e028041803040100040003107402d0000341d842034070086040e0007464090714220201a03842005110b80040030a40b0391240700440f141013003145010012003060500c1646031021001c05045030f8460007200006050307050f0b02406518040514960445a0340d107115410b8500504a50b40d0081c50141c0100000340304500030401014003c1c02c1d9208110b80d8000903142101104d1003641140c0c4a40c10001081002805540d00002051007000101c1151020031340d55001800448541c2000c503029000b07655402c40b60b44002c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 751873561 1250 751872311 751872343
    0x40b0c120c124b040f1a0c0303101401020a02100c1103061e1b1b01150b0a0e011701050d0305040e040602090a08060903030a0506011808031801030e0a0311 68
    0x40d90b002c03414604001d4044501c0b584482d4007100d83c40000751201101d0444e0080c2158803440c1c2e080108070000d8010461040000000c2001500700c241000c6c00658480c4011100703407000c80b894030200a100c5050480118119007005aa040050f80c540350905005180e52030b000301d0318032035480d005005a01402982e545442108104010707100f600b0a42c0400040001c480c1415440d00400d8041100f00785a51140c0722030280040c40781040201c01007040822003400118003d4000c82d4140d4034040c075504030a138842000030310b002c0b050785c0042103080c20308802e2800c019001c0c290184141001018000c13580715103505140402030611a130250750140201c1e0341c1311186802c21b40ba0041c02948519841c60140c000300f0000501c1c4030300800c409210b0002c00c0e011714556a604a040d1005040082205060040d40c19064010440300b088403009400741000943d9940d07658000c3c2100c01483c007015a0401d420305e00e0201d030400001c210fa100003035260400444040080728000d0030324020000d041c41d1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 751874811 1250 751873561 751873627
    0x2030f0a0507090b04090c030f0503070b010f030b01240e370806090303070f1403070210062709031407060c0909050618041106040b0c120c12 62
    0x80c4040859020100c81540c0d108000c1041441c4c00d100c1500c01e9401c2c0130b420700910200400101c4c0030ba2110320315592003401600d1519410b0342d18400384000c2031b08128444140d03000d0900800070070719501405081e03210107121000440d000c00000c00c8045900d1041041b804080140240c0c80c0ca08556014000d000020001c201d00394921108980800d44810308030761807000009884040070400c64090014000614555036a40c00f0550302c40d000801203d0800c4100f0083c11101800c40c0c1c003a42c0520395507805400758580c61082c0c0b10589071550055245054009940078002d410390f0881d1440714401d000200b041405410252140c9183c4509034049000015441003041083d40c03000302046c10645500c0591070b1284406d03002c450b001c50304241c0103c46118800c2100749500542c1e980548100c1341c0794021080c0801166094005602c0702c2c41c000e40125580d00404420710854810341582d0280c0c42c18100d460010380c1d43c0742211035103a80d49817000109007000746e0a8141d4141ca0305817030b0a07000e41e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 751876061 1250 751874811 751874813
    0xf081333020a0c02030d0905010906051305060a03050a0506041104090e0f0a030c060513020a260111071109070903120e060f0d0506090411040c27060f020102041a0702030f0a 76
    0x1095510b0f01c001c034480d018101c03050281e00e015035403510641d401a03503440d1829040500554942c0c0c40410040c12240d4a1940019260b84c5c0b54001c00c0c992105035030108a900301100c062003920307005032010748100c2c00d05420b000da036682c60080e5804c4a004801c08200c4042090a160a2020f85100d521007801003c1303c400926403c0400601110300c1888108000d5075035880c0400d83c2624440029800000e14904010110b00b40e500030842c40e603000d82c0c0d100a804c102030007600319000c0a103060400758011400c2406c1c001403a00d48070080000f590601ca4601e00407500801300b00a40c00024440c1040d4600780190032300c43c00d00846540c4003d00340035911000d6051048884e0886400d6a40440c2000300056090070311210b02c0f800395034080d0070100c03110f0b9003104000241000d4240d2100b0002201c096420130902d0394481c0400700b07216298020a0f50810b074000341003d00a01400d40be580c0100000c2180b84001c03c1d1b03030f448054500d803003561504034503c006030510511084150a61113481c003094 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 751877311 1250 751876061 751876067
    0x10903141c02030408030409020715060f0510050309030910140c030d270b0702150f1503030f09040b010c05060711010c0c1110030902100f081333020a 66
    0x54400321403074502540c40350801d504a036240304a00030712440360030034001001001801d4000c8c01505200d862162203400d8a1200001145c5403544840d1038020f200d802000141000140b00e2885140c40c41c2861442c0f4000c1c440913982e01c5075088140c000e180810009100e0b074410907100701c180c40341c0342d141342da80c02d886d14000c4c2d902c1d00260035407850517140400d0b40c1d0100c0901c40070183c5110111050f462100715544681c13004950007040c86055000e030101c819000545004180d2203800c141e04a00510305245903401482044001c415000758410001d110510281c0320940c1c500c450111b0b000300702021000b00488491885460040c518403404083c800b461350008142220700e078814008110302450540e084074001500c0303c0181c001a103003c00f071161810469201c1107500018100030035200300c2c1c1e41c0803d160f08a00d01224000940342080344501c55406002540c0020f0907142d141e01d0002c95407142c2c84100303400e550800969840001d075010b03540f8030002e131010000c007c0d0401c5407507105104002e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 751878561 1250 751877311 751877323
    0x140a0b1501091805070e150c10090c09110405040c030518030a09060e04021306051314060a0320040801090b0115021207150915150506090f01090314 65
    0x115000450380480420554410990001201c810308000d056002181c00441c000340400f42c407840402a00e0410411079413a42581c0310402d0051800c156074850040c04601c1c1450861034000003024213029051001c20890b0710900c0544000200c00540c0c82e1032100300c038110384181d500c4a6001420701511026154165200c544941024141861101c3c1d10940c0030352a4400d0030515000f0410503601849054840c41c6080110743c40a4001480d0600d20840c0c1d85544e0250f900c03410004200145030509400042d01040043c0100c05000b03079442900000500d29005201c001000c041e610040302c0c0c000d842d210b8608480785602c8452a96940d01e802c0b040b400392270200c50a0741c3c1c0138008800041c4e402188540c0000c603c201340d0250040801e504042c010700da20001050b510907249010700c2c1705000243c0300c0d00c1d40140c46840100103005d240d5055105503007401104108a5040035000c000e19107916003102d000a40032582c400d0100320060058071165803d801c05000040a003000c40e04810340001c030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 751879811 1250 751878561 751878571
    0x20a230f061023090a090506061503160e091003050708030f12090109140c0307051905090712020f04150e100522030503070302012414010507080d050601120b1c140a0b 73
    0x148c40d12642d8220030300101644ad61801444110204005400136420403600da40001d15441c2001c07080c80e054001400620b02901d800c41042801e180400400c4010800d40c0d0007002600040c600f4440001c10194403400303a610700642c124a01400940c0c0c2c07170020341c0103800d2076511450071403034650043c44480e9102c44103070380d4600a2086100c0454240303040d94501ca00c0c9600b034a6040a00c038100010f01401050241461040c041c0840e80e48005039058000f6107180104280f003070b0340b502e01c8c1040520345440e41100c503a0a000d500b2035184015180c444081c000c1199506100340c1e05e1826554074903e1034150070130302c15602e2060001008004001c00200007460080e4000d10851240025004c4071082c002803002075042d40c248204040101291080b9245034141800d50074071840d501c4244040e48000051145503030750740b0070000b440d0b802481760000d21840850822800c2e0b071200100d002c118100c040b40c0184d03541d50401c0c6041025008183c3d800318048419103010303508038036080d00a40d20030781c1e07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 751881061 1250 751879811 751879813
    0x7140d1826010510062a0f030201110c210403050a06200f19140a03050703020f04080a0c0e01060f0503100f0b030403080a090b010b0a020a230f061023090a0905 70
    0x3c0086e89004040d01e200500741e1482c010540c0000c03540e680e40c0240305003402203066548407028245903078004806401c0c0d60034000058510101c2003411084a2108840c142e411a030003800188007040c0005140500294009000100d020300c001150b9540001e2201c3c22039180400a01d81070300c01010005408581584150710741c0241c1c100c0d8054814503021507184000034014041000020321980007103400451a090040c82c1008401803401e4550041d008018542d1140010700100038030203141c4401020040c185945550410800070329101e071000c91601089008004144803d419840c040010a65035200031190713641d600e10111180c00c2141d040c0e000c114443c00245c003800140c081c007581a030f4001c00f1004540c0c01c10140d01d5454210b10304400071032086180a01c00a842c2c882c000351070000e496140380e5000a520455480c000080b080805150030002c1480310b40004c40ca44d541c01d81700004182d1030240c174010300c03813405104e900680f5a07001410307000b402141819a07000b090214060b078 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 751882311 1250 751881061 751881077
    0x1020d0501120809190b12060906030a0b01052b05010c0807050a0c17160503090f060405180903120c030403120513030e04020f07140d182601051006 65
    0x10007071508100c480d5020f842948100f0142e0454035018003015140005c008201c2540f40d2501c400414a4021462800c0708210001c00d0042030320300441210f5000c10220014a0300510729907034502020010b1051034016a01d07401100c081d28041c010303040c2d82d54045411300c5c0c0d440905040c124040c0c1201c003045008101000081440306104200b10f8070403a031152100329284105a4810410312400040c11081e1003042c00207000d50341c01c00d0543c19502d0b01a00c000d58803060b03503a0401c404000c400d42501d228580030001000720391240540f14100e0245a0250103469aa07030081c0c03801c511612a4850f806190242000503a2028034040c600580c0030b507480b000054213000480044075010b41c0c0c01c0e0903c5080413503c0c400284190140d254460340a84054141540118144165000510110f900500c0f40010394084042000180311008481c0307007080c001504d240d9000c0c8025200d0103214014602000c046840841c103071b05500801d080c010081015103040406860407660b903010b4180015165 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 751883561 1250 751882311 751882319
    0x1903030c020328050705010e010e0c0103021e18060d060303080105090717040305221403061b090103020729070f0e0f190b0c060f010608160e09070201020d0501 70
    0x300f5038071003041440520000c0200c810800c0c1080d0082c140c11030070082c0c108884e1001950030700440c20704501600021504001520b078072414109a080c440341003600c1030006200d150300c1c0200ba008920080100316994080b14034200c01d40d07030b4660b00440d4100350000740c15844000c040d0303c640100d9010b40d9488025988440412440340d200355180300c00600404000548481b00403070a603002846800c0191800806240c948418024400c0800321006039500030031181440b051002403801e4100d000e098a464207008011003200b10a4100010502c01715800e820b0740d00a0307044071007180e0003844203058003a1545400b40300c0040c42508081919410001c2001503010704410b084056060f180c5001c0e144250061208840841080a034400034003164a03403400341542000c80944542410140e42e0098494103502c1c1040280194010712090401000102c0c0e000340c2d03141d0080c490702582d81d5600c0c0d02000c00c0303030200452a0354950010212043c4a41640c05600030300080705080700511690b1781e5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 751884811 1250 751883561 751883563
    0x30213090b0108070f2705071e0e04060f050a0303051b030f0c0f070302031b1f0e0117010614030a1506050306040b1512090304090203101d190b0607051903030c02 71
    0x940300b802c25940b145011071500080942001d540050103149c042501d2810850389400190402800c102245a464000009007400e015030005045021321444030980b0b00b00225000e0082c0f03100103420001d0100d100700d62001128601c105046129003226101d0112043e642e40d0359000015034086841182003001080a010903104200c0390000c01406994403080240c0c0c0b1100c0c0c81e5449164000f40c1140f4000c0f09010681c01d50f807004007640c0c0e03000203076900c2c800007400c030701c0c0b10300d1600a191046134010442240d1000712194181144c0c03110742d450740c840c0c400b200050116150b90415080c80d004c4003142c1580d02401035071055408440034000c0146100c02e001e64000001401204030804101c07041181c01e0305c029040d0401c400600700c919255545910b4012600180e8208110500c2d40c1400c020000f180d0300030f80c1c0e80c2d4400407a200d0741c40c20301c6805005900400d608502640d03469080c484a640c0e6940259182c0640140542c0e550f10644003401c41c0807900e203070084001c60f10300302c0340e1402c9908c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 751886061 1250 751884811 751884839
    0xa12060204150c0507060806150c0a030212130b0904020f0d0506090109020c030d09020d050601080a1703070540150c02010215130c061706010216030213090b0108070f 73
    0x50480c01601c94581030000841d1001c01c010640e07600100355000d81d270f410305030580040c2108102c0f84c0203025011454907000b410700c10380d210813400e004420303c185040f2410340c003640b204481c0c40c9001307195546e244401140203402102d0003095400000b1688035016042a0040b5100d5841190050100c0c2c0e02e40b40d207403080380101074070907000d0340c41441200e01410080d40000841070004200d208a1403a90782c6442c40c0c100241c000394030b940c010014050070046402c1c420b48154071054011400c40c40c100c2e0004119008000c030340d1a4899201074084c1056910074600d040c8042d41250f82006440b00d8449403039070b9a550710405440c011304441038a0110700c10201551007541c160301400c101c542c1e013101801800340107400d4181e423407001c00703100002903546100700c2e00600540e1641e401c00c1c2d0030150080400000104510b041d034001c4d02c200e9981c20f60b00f09a40b01a01c1d4101d440440045400e1820002003201e100018076100308080045103e08000807040c0c12502041e002c3c404441d02c0d8400910055 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 751887311 1250 751886061 751886063
    0x1209050114180a050415080c0a060c030e0111030f091507050a0f150623042711060301090e190312020a05091f020c0a0b0d02090a12060204150c 63
    0x69424000d024445602c1c80d803140032200014924011543c0b036030000b6080300c551000e400c0240c1d0348081e041103204010f00c01c03000040350031664000507c0c80c00720003030422000c0080003020800800c600d00c03801d0380160071645a5400e000c0840741c540720003041d1024144d00c40c5404501c100d13444002d1600c00c2000c071048807103c952040280c00f0440d2181e5400c0c0c241000b2050488010012027a1400040000c0c81010024802e180000004c070008481441440c0c54400660b402542080440f4004203449010400025040441d841d0b280c0310a09180003006441c2039601c0c1d108200000000c0e03140c0e86d40e0003c190704c1c0428411744145006c001e0307440c031070705801d5079008000c80d0210701e42c0c082c01c210740d6000d011000318138188a840c00405d500040c0101c000720603040c0702c0d100050300c00055564100264032601c80207944280084d414042c90081a0190f54082c58986800240340ca21703135152600b03a10020306400440c0c0e480103c99180401c040d4001e8040c2806444100340030440062142e00c0c058406 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 751888561 1250 751887311 751887347
    0xc200a0f081216050607090f1d070e0402070b010311090c040e01140103060504140a0507210f090f060906110415080702072c0112050607030509120712090501 69
    0x7650030061180b0050b00003e80e007a1550403e00c1002e00032400c03d0140c0c6101d56041c0e80c545050741d0500400101d4603204c1e42200301880443e6202030307045a0031126a641100c880d04000074680e1006c40000c0c00380c820088014804a00e080c0000204500c2e4504104518401c684910b1030b070b60f580c2400580d40c00b0718880c5065245440c0010050800030383c0c135100165034185400b0a8858841c0080b405484100c21243c10705500c102c01c00c000c010f024031886800c2009440d2041002c1280810407265403070400340005000d50351803012043c400f42c2e902006103250320075042e030b1440109080190050810341d03003d5070b6060800d800f0035070748140041104e0944408400031540000799030000c0301c85400040051003940300340c000110300884400e48414003040c4484c1200ca8418035100403901294043e07015102d204891405d48000800205009030f01603103074500099203545000c1c0c0c117803605540131409080c0100c00681e510600c080041c103070000210a40310703411001d40d17640044800e8203a480c0d0007000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 751889811 1250 751888561 751888573
    0x30a030e0609061b030405100e1015060210020f130e1e040201080f1519061b0b0103020909070e04060b030c010807120f0f0609091b050a0302060a0c200a0f08 69
    0x1401c204c4c0c01c003850708079005e03d0454144451200603c011200c0072070303e02010b5070040985040c0c980040c0a005004180d00009113451481c0500195a40c2e009005c3c11410a17000b18419420b01110390660b825032900da01a200816500c6a040310030850513225a040b1403890342c49042c0c5880f911504d0f50050754107a4944149a8808074240c2c040359001e4000c480024012460310104ea036080e000e000400040001083c01a2030080054040d400606920104280c400d5082011500088041e41100e4042e2442410395451290003400c10006421130030038006507100340001d2200c3c0e070340b002c000200d00350111010b91183c000190f429280407034191300000c00f4028143c14200658000b0346044241080208241200d4002c2c102660b40e15041201c1c155a2032941348248009807010180100c454041c5110f074600303002c04104091800d00000c1d00070b0100140c0003201078030600305100030940010003031084d1203460500164800c000c0c1412449005041030100b280d00f42e649058045580b10001048 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 751891061 1250 751889811 751889851
    0x3050913200a0302070501060b030118140109020c0708030d020d050106020c0f040c0c02090a0207060b09090712080f0d09061a030303040f050705220515100309060608030a030e060906 80
    0x99888100b940741016002e100103800a90240102800380c914036042d1034903507040c000c21048541303030341c900c904c8000d082103c184501c0d05505006815503107082405640e0300407542000d45030008039400300300e1901c0b00040702da4105985a001d0b180a05e00e801007441140d0761080101e0f9a441c0480030f980e03011102c11400c83d42442c080e80900700b42341d4141088c40c0ca90040e50000b480c0307000225860340c1040c1d00024a00204091489a001d400104030307140c04840c100200040c2d6220058010015040c190107a40c60611076540140c48a82074010040756031451586160406030008003406c40f902400c10700d8100190301d05100403008004050011415550750791503120462140e105c1c01d84481c001c0b0407010990351241a001044c4c403a00003003540300d0310b01c074a4801084800082000d1280d41d60340010003425a43e17000410900c05042ca0003089510007801e29070300503c40341c1c0c00404d0030311000503480407003a01a0004803100720380e6401c1d10655681c84211036240d403070403142049244211082c0701 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 751892311 1250 751891061 751891121
    0x203010b0d030e220606020c0f03010c090611100f0f060b030c070b060a0e18120301030c1e09020c01090b010e06030a0b04080705060103240e03030a0e010e01050403050913 75
    0x2003100030907215440584c81e24900d201e02143c4a9410000050300411841a4070303060485d440005500c096000b00943d1000082c018441c841e1385c0500020050590b0a034040b0000c10090703003100088580041250580c00da1a10004085c040000c07041d075401c04030001100361084003a284202d2410003c40c1c605402681d88031044000200101e0f4422514030700858001c0d000300302c0c40c1c402e820500b00c04004d2130320644010324244c10311002c000304000410040c4009036994036184101c40511011682c0b030b00c419503411180703400070303005030070100d10104d4103070001e40c0150811100503014054500c1d40b643c07100c2d00744c0da10707107401c54169805a00c10f1442d4000540c852001680c81402101d4050070241c065480505120003039200b5030380004641202109852024000000b0550701c031820001e040840359003035107a000007405180c01c641d81d412068001c4d9002c2d04011001c0c0d10f11002081071340b90030f140c040c2442c1c0251000d02e000381d20000700c3c481c82d480a403043d0503000c410300482a01980c0704000c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 751893561 1250 751892311 751892329
    0x405060a0201090510020714030301031110021c050a090f030218042406050906030105072307021203030709060f08040605040809030a0b0405060915130206130803070203010b0d030e 79
    0x10314115982c5088540109205002240365451904400360369882c1030306005000302c102e11020350345504100010800031340e56410004d20040e0a0b258109203d5040005a0600c3c045241d800d507003d48048020300d206a00a004000051254941d00a00c6840388106042000d65020017034100c9032621810789003105022490b54041e118400891000b00d54824200a114400c1040300400b9220607051001d860a6076107150b200800351300811107458a03c0d8001d0107844840c0c10409520254203180741014944003c0300d0040c1c0d0060001401c0b185c0c031160380390392035004441c40c80004030380e00408200d441c41562080304a6020b50307500c0c40551a00e032500c00c014040503008542c2c05204028071080d9440c117208810606006210025035850b01d420a9401c000b002000f119160700440b541c1d000000f120300944d40c21812080114175a07074001d00c040384443c0319004114561003000c004c001a170000010060004c1c2d4030a8000f480303004004003d1100018180b4401800b2400c0072414510300e050080d01 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 751894811 1250 751893561 751893577
    0x60b0d0515032a0906010e0f12030f070c0501050306060d020c160e34110c060313030f080c220b0a02010b01171308033423040506 57
    0x80380c0207503016500003403400300041c003011851506400925160441c0203410b0720f500c0000e40e4104003614245000800803401c00d0b4280d84107890fa4801e030800e81d1206410021840d400300c040301d5561410011000e070f660411001240c62482d21400800c080d4401d1007501d002c0c900c0030700382c0d90030141080c2e00107019402054000e2510302c0303143d04c100d540c44d141c0600b5000800e46086120182c0c01c081d40e0310103007070300002070350380e030401203141b10807002c40341a01c0b040c0505c52640341440b02800e04180c528240044100101c0d44402c002c020b1101c5901c3c070b086c01c2c80d0514401d071101103491449032015120f140d8111408020181e040c0308204c094201c1900070301c181d440700031840b4192a100d14840d015500088100320043c0e543d941c0914165801441d602c500b2910045440003910303050920ba5510350701900000c1840d00084045001624460043d1a040c01030705480d00c0b03400070038643c5007198120b21103030800190b021482d003ca0101162000070400c204d20008500d018149414400a6440490 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 751896061 1250 751894811 751894831
    0x3040209090a020d0f140c030c040f0213170d020a020f0d050a020415081b0307060e0604080703240506090121050114100e0c04180623010f03060b0d05 66
    0x107000e00044e6038807140615014800c846030f2025940340e0070020035104a402401c807255201c50f40f1304d00c89590008195075072500444003c124400c84420130b5010b4001c03d102c0c03203034580607904045201d0444488041c820b000c0c1c10110781c80d0500c0d2520884e510701810764081c0d00a004903068281d40d041c0175000e042c4080c0104100c3e060201c1c40c4e0702040071030b0400e00c20001980782e09001400329110500000070341038020900d4030300b81107290001a440b2440740c480c5c031061006c80c1000542d2500da035000e8030300805101054440c0c1c10383d0384c18001503c48029281e040518040c5503c034400011034400d203805604050300c0702e1126801c112246041000c0e9010f049030040782d151100780000d6090107001c1039500e031407074140000e00f0304030701c545030f03040c0b440d003000300320400400c20040c0c40700d4000c007503d0441c0c4440f842c0072009601560740e000284116041985030125603a5080074071140c5060160403113000703a940002a100c1840308404603448d83c001c034404020208003070035001c40550025900044110 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 751897311 1250 751896061 751896073
    0x804060c03020919060207060c08040b090d0203030a09030c090615080405030903010c030b120303011a0f071406070e061801080405010615020f0601090c20100501091409120304020909 80
    0x14002820524007548418406804d048052004640c144590001410582000550400b00c0e0350399428901550081030410b20700071a00180d65507581041c40d1140b50050f0540341e8400900030700404000b25400f041d102c14201087c00911090240b042d24103c402111a1200b200c540c0d08049424034006803080d1000d00c004c0c881010703a40c4e420310841c1d42e904c04948000400107075980511030f0034030200c0c40000042e081800100030b1b0320703500e0340101030120035071480e00c0e41e4296100f080300440c029030078050039040210200380c1c81c8000010300c2c0b078003c21032600c4401445240104201d07040c0b26a0a07440c02110303051185d1400c950150810380e400911501c0082169901c41c1c01d401d20310307403403c0c0c11040161b004500001401320180056409010080d10034888580555000340070200742155030060810810489041c000c01030112051269100a0522040d41d64541e120050400103102c0511481050003017803148a00003421010501481702c00c50850f0b90340e800f00903c0803001080410540a89 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 751898561 1250 751897311 751897327
    0x20d120f230711192103050a0819110a030506030c150d0608121e0a0903020120060903190c050a06090f05030c100c1d06031806010b0901030c050301060804060c0302 72
    0x3d400e1801002e140d100c541d034a90b17285c002103203001e041c507100c0542c48501d0355048401280e0300400321180340f02c460501415507124107400540c40850310131406112403400b205584000103180c000c18440300180d400307110ba922220b00301034945141c3c0c10400d52240140a08080320101e42020380b101ca00f02420004905503500300c2036082c042d04103401c40b684140012581041c4a00c0c03c4460044e03103032884040d0404c1844034011341084101e00019041c4000d0f00c0c0078802c41805089501e042d004a907040da10b413800c00302513081c2d036a0014111076840501d024180d8604030301c505080c1d40b60b142c00c4030007800c034100c2540b034050040100c28025626201e901c6040404034030300b00028982c0d0a0008010024050005402d20455008040c1c00b002c01c011070804ac0041e48114030408104d61044655a81c0c0e03071503810404110500d40c1c60281414050b48000017011614440602451302003a202400705030b82c1800d040f180742c4400d001d14030210b03594a0208021030700075400b9583c0389031607040042c901106 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 751899811 1250 751898561 751898569
    0x6101d0d06090f0b0f1003150902040e06010f0503210912030304080304110a050d14010605030a0308060a0b0a050403240203250e0f060313020d120f230711 68
    0x18401c0d603003050f038a4181c3c0c0800040c1c0c1e031455402844091220300b10304014484000c00c00c07961201034240c402d2100710b01e284d041540d002c0d6003481c0d4020010440e08008c01146503d440c024410408080e00740364000480b410045039583c1040b40d0a100403d1400b890b509040b25600104149038002082c0411220348510400c010b5000f54040d1880c0ea80340d180c145082d104504540c51018003d4504d002c1c10000c0340c95034004103100e19405110784d43c000641d0100a401041550301040e454445c240700038040c16000300e40c6e54014482980d812130402c0d00c8491070b0016102e56142000081e00070002080402d610400c1405c44085a54024071a284030385000c40903600155903403078049245a030044145040e8822107264000d09003003c0c120a0000800a56a8072041d020782d07000c0c182c00400982d60001c803500c05031700035500034400f00e8170024908250300041e04143d03480001c41c442d4140720300d03000e004804045144048550440c2640744c00300041120303030400e070703021541d19560244448403966 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 751901061 1250 751899811 751899821
    0x50304090507120507031b0c0218100905340207030b011412010b0a0506090301060e0c031006020a05120a05090a06030c0e041406210a050105060906101d0d06 69
    0x56990f4400e8480100c8010300e00440d44050144000e1520b001c40c0800514141448540c084010703080030600d150340360010901e814200c1c864040d1502ca410708210304e40c088007030f8044c240c2e00385000030019a41c0d00310b42c07010310341c034a80380c10341081d8652111031348604400304881510800c01c1c03065450301c680c0da50ba034243c2003400380c000c0c901d80c1c0140c5004228074100050400301c3c6a5180300203100e04103200012071414001c41c0101c41c01148001046001510250000401040b081045100c02e2820b0160b01c4807a40043c0e0f41d00507a00100c401c001a103a01c0081c01000d8990000040c240800000a205030590301020a081c02d21005011044441d41c603a181400280340301d450200b02e0f0b00110800030f0140d10000c004e10b01c914034022041d81d140d50001c880590ac4002960300c0d50107140b5118082d031413803543c21030310f40151040447c131508210040d0051401454251881045500d5640404c81c003294403022100c00100280c21400f01300002031012106070344043c04000100f101c3e0386410b805c0d01c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 751902311 1250 751901061 751901071
    0x60d081612080411061804021803071206110304080306061b0a0b16020f0309040b060f1809070905030d0c210c0c1208071401020f071a0912160503040905 67
    0x510884100420300c581507520b130403000801c0701c4040c5050b00011607408000070581485008a50102c0e04814a500c10403162601d004014200d0710b001d03640e455082c0050078035010841d022420040c04503084101d09081d81c0c0a907500c201c2c10380c00e582c0d42c1c4003849029042090701c8031440c6010102e41c02100d200b8058422004e008091031240b0303180c5581c4898600200c03514031b9045500c5041000c40700907000c4290703019414100c0300411402400780002c0d46501426145014110b000200c0d44e0546400c84091760034108165030280b1260744804080c0e0f0307104a1880360541503013122170140b110b948101e5250301c80a2248010b80c03290620420301400300b0300c5098183e004140e80c0720070780050050b1541c0f00c034024002008418101252135860740c05078040c01ca0024984000070b02e0803d401e00c000c0d01030700c14000302d0030542500d0384080d041c00c0c8001c0e009440000256050070021400803540490a03c00003214580240c0c42c104998119036003032241d1038404e0b100350009010100b604c9501c1e0203074500031 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 751903561 1250 751902311 751902317
    0xf100b130f0914030d050f070c0209090f0706020609010e1506061309110903060a0605010203041806080a120f0807080c0a021e06010f0e090706050c0307210314060d081612 75
    0x1700e1300341da517060440718090201000b688048040010182d44404a090010390586808600c0d0300c924920070300e01956059080480e0055217404200d181e0f0000300b2600c10b082c2d503402400400f0070300c4841e644504117101e4807000e5811044c0024803500b0200020b0544565507280c44124507a113028107400c0702c0050311211155500018000d8103480c0400c03680f90400c00d007000801c0014580303000030303661744075a206002e51004a40025440500325a000da030090110030142e035070f0200a072801c0e101d016a414403110109800c1c400c0207000511a11041d031144196841e02c0b55103444500c2d90280541010b03403107004620030055044260842d40440056409082c0014119541000d5222085e94500d400031240c108280c0100a1140d20018204007100c81605050303640d0081801c0c45400c5104441028000c14000340d8110400040700c070300300300105140e0750200102c48810318012800d03181540c00341c0e0b02100d280c0c000f202151248005040c500948910164000e0b0143c0e130340246807030220307400004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 751904811 1250 751903561 751903567
    0x151201020a030e03090d030f20070306050a05090703110604081515030a0503073c0c1208040b030603150109200712080c1b0f100b130f091403 62
    0x107419058010180b2009059018500b40b66406021400d241c42c00300000c1c04000803250720391025401071001e01e2050280b0140a11915440400a40c2c0c4480300e100c00c489540c0741c00c000928040803480340c1ca0241d684007000d0401c0e0762451302d480488841d45104030342c0c014400c03c000039131207804008240401e82c4180218800d4900b051420500039403526007103020390001e0249400103800841201d0b0246d50200042d12440000b43c014681c0c0e20141c80f1302206800003070b1120940c0314914904d005102d00c03036201d50092a4466401085080000ba0001c0c1504400d0205102080301c0c940919403110020b030480c1c5d040058003140034458102a0b1042840343e9030760807094150700440d0bc20224402001080c5803800c109a84e8546c9040740140c0800100124a03020458500148040b01c0085000c0320108030101c0c00d070944680c66000c820706414013481440c0400110310001d000d4454008402400c0021000c807400d810806406080321006070700d5568408600018100040f01c003081504a0007591 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 751906061 1250 751904811 751904827
    0xb1f1d0a060b03070206010b0d0f05091006170c06030426130807142e170f07082205010609060e150a18140115080c0a08010e15120102 59
    0x212000742e080300d50341d10403c1040064540d0000b81e501d04407400d400c4c08540c0c6144d1001040c00502d24048130790340c00ca05280920140e548002907070040b0a001000400c100c999880340f508400541c451031902c0354006007900d014034035002c009150310070701407000da1030015482d0140d0744212040207164460380001041100148100240000203010084010441281400c191002c0d19041d99503d0740b2404500003c00f043c03405482680303050701e513800e002c0b01e0b4442030420045c1c0108402485440620181d00005150030041c1c1840f07800780209880d2020070303072030b2409460406849400c014084084607003020b00007940900c2240c0090140d070b00c1c001005400c0c1005510500340160201c1080072180d900501c0e9917488415040440b5107504c48000040c0301006d050028100b900d080c0f0b0740d108051000010740c00341205000c024104680d50342100760b592104c20540c540501c4054200240d40000184030f2170190545041d0803001c0d907a2025122003444000440140018980070702036500070640700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 751907311 1250 751906061 751906081
    0x9011221020717030a05030412020f0a0602042111010c03021903050315090702120c010612050706030509031801260a06080c0a06120203040201050f03090105190203040b1f1d 76
    0x44042c43c10640030358500b41100d20003e00c5c900002d0405010030424030500d00d100b034001c00503810900d011006440c080400b5052640003900640b0402501d00d0b208800100301030381c00c0351650811507104000c00742000e11070f001140c0d2202120b1003202036104113804189004402d0080300c02c0d142c030a9032031503984e2034607640c10445002044050b50081024005021415402184e500c9640481091668580701100c2d1054090090387c0d1040b00a88441e00085041c00004910081550f0080c1c8051040c3e1301e03100b112030354078480c851100e4240c02c0c10342222003c542c414044801c042c2402500f4003d402d003007483c581003045007078404501d202d665035000c000d80c00080c4000c1103140800c070f9401d84c101d0300d0008081d0a11000306e140041c1c86900200107011a8098402e0b90101c0e4100b201140e260315007846000d00070f10040c1e5528a040e180e14a0200110791240200c0e880b44d039015901c40141c0d140c500c4512440c8803405030003841c0300e40c032040118080690098003005c2c80f0300d40b000ca00321410040890 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 751908561 1250 751907311 751907339
    0x90504110a08040611160507050a0e040b09210c01060506040f031704030c061106060402130504021c0f0b1306060203041203050d050a02040e060a05090112210207 71
    0x14011410080e060008206032000e40d4050001c03410034000310360320b900d00031000300704000e003000c0f0b4104c01051592140c0412518206807a00c59012603280507201d80800543c0020f900c0350a08580d070500000c1d00058401c0c07105600500c0c50003c030740c03c6520f8103034040d4854010320b48000030700e46d01044440e641d210901801004001c19a81707245403d0410801606a081d54000a060008110111490112900b040310700641e040002d0342207040e16a103008250a14036501f90495205050210b1107520b42442211580d0f0016004107000c21300c0d04082c040a5085011010300301c04d034140c50841c0300146409090600d00d140600041ca00c406401000900c000b40105040103078503101c41404640e40010482d82526101305840411408514046a951140703c00340791000b82400c062000b0030a0603000b41c03054518094031040c16685002c144410a00720303200700f43e40b040b00a1300400c000c3e007000780315426403801500401842c0000d496450580c41e0700d158078030010f901c241400c010082c840c41803 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 751909811 1250 751908561 751908569
    0x3030a0c050d09150c0f051e060901060f0e07020c09090309040606052110240e030a02150f0c0703080c0607021b0f01051b060114010f02030409150b040e040309 70
    0x380f4112030401c0c5405201c0d0380d500d481107041c0301c1440741c61001e00100c4100c0246041d4031100725031020b2602c02000400d89103101024000e480381c0000f007800034006000d0001581d50300b8058560035450001c2d010807240d000f4002c00d040d4055601c0307518150b1035070303c081c87c4241c08400003181d941d110481440220741d06a0710440400100307000b2410840320b14050f40d112106070708001019a200d1300000781c0544000ea000b03000150192444c803400700d000802c0a0b600c072000c1e407204220b4400350000e0684916422800940c05070361214030000301881440588104e5155040706400d2183c0342003d0340c039140c0c50740c00030743d13000c04045083e0008a20400c4903d900140e03038400307001c01c105a40c410841440341400c440d4805ea0100300f00c0304c00c0307034031078025038820703045500810582e40c1c0b0180c2599100c540c01c0c01090507510740315105d0702407940500f40c11907444000f603004601e007a245c030150b4002099003031002200c400c1350000000f440d00d0031201401c050091003045a40b1403c1070b16010b4508041680 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 751911061 1250 751909811 751909817
    0x5090105180c0306040227041404021f020c040c030609050105010302041d060d211205010803251703070318110f28050a09051b0703050903030a0c050d 66
    0x1012524402503202050b4015a680303001603200d0300e4001c0014080d0140251010001e00040980180550010303004100450180c800b005802c180c000c010710001c4c01100c01a4010502e55105224280d000c96403c008011900c1554801400100050180c0d40d10088200c0042d84481c1d00f03001d5130b4621300c500790040000b400d00314505480e10380d8420300302d190865000c80303a16139803000548035250007100c0401c00c0d038046000d02e03040c2042000e0071418107a81240c0310018100718010881c2441d030b4456541659840c80c000d50601c198070401501200005503402c1c4020441c040840010748941440e036807031051845903c2d2245021100101210621541520345000180002c404141162144180d403032058035480442550500459411100d241700e00000803210b60302c00c040c2c0c0031480b83c54000d0b61004c0b41e00303581e0280c0e40c940d0f4905a540903207040b1003100340000200c0000188400030700c0c05920a0400c5402e121078a0000390558000840240110b2a9240b005080003414014005143d00c541 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 751912311 1250 751911061 751911079
    0x50c010b1c11030606100f030f0204090207050d0c5010020f072d05010e0d020c0307140a0e0a1506081e0a06030b0420030f1c09090c020705090105 64
    0x500040c8540800c101110306003c3c1f40721035401c06920903040303c60403c4118200b59a10740c2d41d6000380c0029803248400362890301407182d020300828070400951020030317000f068170029010f130300e0750f4035484040c410140308200300040c5558084640c00c02d0880007007a440038200c480f04100040c2c450a00a125180c000e507148108001d50130140403000350b4150a40001701720030303408016044134072400e5100054541c800316102c58502080815004858004803000580f2540c4841c190145d0344c918503000c080b5031540185000f0f100b000c00a01c26400500b90040007902c2c0c49075140d40020302c044e010344290042c0b50321058903544205a000f8580018066481c0c40142841c040f941c0e119080c40c0c0070050050002c4181c0491200050358002101458121b00f100702e190400c0d1400318030b01d081d0144c011003000700b00c007042d192901d0041b402005400803800580004800b003440c0041d040132035600c11091203250000801d0640d044d100d500410b0b213103500280501c40c204010002c001e04c05a01c250700c905951 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 751913561 1250 751912311 751912321
    0x350901081003081206010507060f090c0f0b180301090c08071d0702030901081b0409021308061e0618040b060a0b03060609042a0507150504020907050c010b1c110306 72
    0x25000303c50340b1350a4480311103410b1325208012106846103c00281a035400d1000030034038620194002c0c1101c0d0710965444141554035005900401000d02c15078070f0100303041c8025040078440e40f40e0007080072001400050701d02e10790f03584c0e0b245184154211610560009006210140880001d045003c03031020041806103841100295248075020b906810449030401050741440b40d40c501094201d00d1491b140d4130f490b00c1e4890b0340000d420804903104150680000000e55242c04218140200003a840d25a00c500411050040c580d00140005410907c01114031002030f41051800b4050f600c203c9813191542807603410024500140c1c6c00200b94518200b0900103180d0b0794030101d40ca100f80030f580102d0560b40059409030703142c0c4a43c0007555400300030200261102d900c00c0040050f9882084004103d18021080c2411150b040b58001c0d00241a900414a028003c0303010f0400d2124010001c21400140008250040380d030940c168803000714449004100116a000351a0141081d1300030407041c0f0382 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 751914811 1250 751913561 751913573
    0x30403031a061909240306051c02060f090a03030306090f060e01170709020a02010903020f031806090f040e1b0f0901060c0c0e040f120e0d350901081003 67
    0x102c051080c3c20068880b80000001e008451003001400c0f030310b0a041d1400e00c065589806428040d10900000340b03099400305862400b105a101241d0303e03204a000c0200242e400d00034154040c040307805103000240600c032031640c4e520348107401440c07180da070203c1c0052074602c07c80d0503100c1440e5458601810500c050107201d080c6980281180e15952403900208414086617080075080e412403504180001030606a1580541003d13140a01caa4208c545210900c0003103a140d00480d4200ea410010705103c0c10b2503454190054410400c3c024811a400704011000a040b05c0803004280340c503422803002d11040854060749101621415549801c09440820010315820014010350f4240101d0003030380c0381402451400d040c081c0941610040450800307041a6001d5040980105e07083c0280056100006101e03540d8860400c0014002a030f46a61580c0c0310101e80394021035001141040d070905012954000340c101c446141d014018a40c1c0f00d1041000400060005044265130281008104000783e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 751916061 1250 751914811 751914817
    0x17010b1213080a0e1302071a06040b0a14090105090c0405011d03010f0f0e0d080612070e090f010c111c03020c010c0905030106150f030203060d0f05010e0d0806010e0d0602041a030403031a06 83
    0xc1c0c01c0108d45c400d60b03203030800039000f0000c078182581c00c1800b071403003c94001110b40d08072030b03141001c90b007003000c0f684d0391410002c039035008503a44844400140410019540500c0b80f28000d034145c55440c031a0341a89102003401c4441411302002080d4440f488981034000502c50000322140030009044602c26101015011100182c8042c0c05032a1030042c911485100b4000200036000c464104006402c0102c000d99440c48140348590181d440e00c0d406070002802450b120554000480c00782c00a000c10740c6490081c90805540d0800341074003001054a141c01c00c4c442d82a0f101d4254444442c0181400c0a16003103840da0f401114010750f5030010340385280e03004001100d05214a01d009039899a8040104105110b6110024141d05112901404001c0190420034105669200301d031401c0102240494000b1015039510b4017240404150803110f0a103807801c083c009000b41c1001d0b19065480f9024503d218900b00c0030300e1015008400d0104143d0305000c1c145da003d100045403c19416200d0014101d44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 751917311 1250 751916061 751916093
    0x10c1d040608030a05030103031710030803190203090330190e010f02091c020f060a0311040303050915030408030c0702040b03100b0117010b1213080a0e130207 70
    0x884042110180e596640200018090010959842d03030211a005041d540080c001280407400000d4101d24100c03007402400d2180080c5030a8440b81413440c0c80c0c0b01031030340c0041c0c100c41c0382003d10440c0003131a08103800114080c0380094010340c0e560203040c5415007104400c8880540c00e03082e800315851a00c16100e07209400003c0700c4a80118980002001002040d035580312040355400d04040c0d0034040015405465400400c0d2540744012200074601150348100d9040254003081c0310828a81500b46440030703000030303191401c00040440d40f04050018580040d48114001038001540c02024281152441c10888030000c100c1d04504196507030020750b0200070f1400300c03914800300300783c82556219000280054000703810780d844905204452806132960265040c0850382d41811200002400c50547d4102e03200c20701042d08000c03507108100500030303000d415041c071030351402c0d42400441e080c074004010120241d1614030316100c00c0b0b0140010230a0103611182c00c01d1050101d00c010405090040ca204 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 751918561 1250 751917311 751917347
    0x30f0f02241e04060f0b06280e0a1511060907030609060b1c020f150d02030a09170d061a120c04091e0e030c0d2a1a060102010c 56
    0x50740c1c44800700d900840b54000c1040c0d00640c114140424480c1d140d104802144154405104007120360013031028611440c1104400750881032030018011002001c040f4090303100f840c240007071181d600009003000e03909030401e103e19400c422100106682140c0140b1101c800d243c05080245071104000342c60310100c0c807002d40307030648584640c400c02445610000080303000408107901e4203101e01c00007041d5503041c00c0c02c90080e481d401080d4503a25000303041e901015094000303249044207120b212006504050001d2030200c0c2c44000990024051480c0c40501c0e0488401c0320791145450081d201c00c4e00c4256000140c0f00c890f084a01040c1e03440c21040310304000064000e1041602c030142000300d54440c0e50f01000d520f5141441e010921400404000014101500144181e086007610591607115812151b2032581c02000302403003050003031480d03017100190411205260380d03000c21040107040803640116038065041110780c60182803840d116800c41c6082c4001c019031310b0407034400782507a02000304023a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 751919811 1250 751918561 751918633
    0x3030b041427150705040b180f03011e020903010e011407030b1e061e030115020f0d0509120705040c03050106170c0a182c1503191e030f0f02 62
    0x724a0117907048074024920300d0102643c8864180120780c514441c01110361246d5086100c1880714941401600d0002450b0303810240784440400c0148000c2d482180f00c203415540341c2d841ea182058080c1304000215400c00c8080d801d03850900c2c0d000f0111510701000620866240340584080b0031508100a6061000c0e103e490b034804520401540340e0b203d100c8059031110001001081c1c054803036450303c2141c42d46800b2500c0e2494044411b50319181e07805110f4000070400c0c4505042c0781f030440c0074018070044040595400585810115040e10065030b22070001c43d40f2203004000e09076200d007508522108a5100d0403050400302102d800703034420071201d90304214030912916402d488840e003c10081c141034522001d9041c000e0505100c8050710a01810340750004030005110100030003501d88082c81c014090400c58410100074010714a8401054418030f10030070758140d26441720256914200c1c040d40314807201d940f0880740105440208c0f240b007130841d003000421010341c1310b962508141600c00200d43c004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 751921061 1250 751919811 751919821
    0x3030504180f090809040c02011a013b0901090c0e01050d2c152a22050a090b01051803120304060b03070f06021903030b04142715 57
    0x640a22612041400d00d891907580400030140c00801007101701740c8090201010703645041e400c0700e42e0f984100342d0325078140455480b15803084a12031001c6040e0442610b00b001000c0012101034082c203110032480c040701d80c0100752450a400101c0c0100401d0f0f40a00c501151448001c1c43c1c501d5056409041c05808100c10a1841c0392740c100610440c0c0104200034040002e400a0882402210004080b400b038440341001c0c0d0b02005620714421100000c1480c4005031385480b4190703100e801841d100400c04148510074041000a592107004800c15646050a9040900300401041103521034640e2503d0500c205056903000700543d03071102e0744903040c03c1589140d030001c24200700007020500d00000e0000200001c0200c135511444001105404a4034100d071075064603d18130406004401c0542d11801080394041e022a6458010b54400d00c2e01003202d0403900081001d607040d0304542d01c00450000208545068194005101c401d150506010400c002c0100e4580780c00d40841d1b4088000b00c00000a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 751922311 1250 751921061 751921109
    0xe0601020312091e0a02270117070509181213030807141905010516120c1808070302040f1109060d0b0a031a2a07050c091501081003030504 61
    0x112108902c1d04d10a80000100c0c0010307128905064124841c02442101ea1a810002850b88003010710440302026540d0030007a01c1040300c0f2130600840c086100f101c001103030700e864016415006000720100c1d00f5004140d42e10280c14134005904a5009141c00d1000011009100ca08802203a0b0001c00c00d039511001d5040c40c0c0e82c030910040c0101c00c2c81c443c110313141d03403000e100200d10406140250001c10140c0c0310500008211640080d83c01c0004000074020409810568400408a0007a04080c64003800e85c210104a41485c1c0c0d001020580045000b04290b06050294010f00024030204200a6484e01c00c442c1550282c0070186000b4000400d41007100d00702680445800c110051103589101d1f86c0b0714000c80f51040148840350400e001c02d010030403d203c000d62048142c18400c008a03040c89144920013078580004000b40c54500c10300f903c28110341c4070400d015000f91242d007140006c00003c40000341c00c0d040c000d400140307108400241040800d900c9001c1d0b41c10307a00d50b28040510150b18040003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 751923561 1250 751922311 751922323
    0x4090602040605220b120718031416050d0b040201170c03010609060e090a150f1d0c0a0203160606031b05030c010c05060105090711100b0a0e060102031209 68
    0x808051000a000c241e440c2c20030060441c0e900100e40210015010b4000000c481d041482070080564080c00403064040301030010b260710550602c0c1481078204a601565a00e40c4103074001e403021390403446500b01a96042c0b00e04820007046c450f00410780c502d45400300380c41412501001d040044440041000c582c400c455540c032152800020200c1ca0512210100032a4028422900071401c3d8000c001052406001c01c80703035400740100600d0066480c60100e5014044d01001e51032020313800d0a010a000c00c00d8188500540325410080f1135030100800a183c80100107080308007819428080c40e00d006500200711550007030031011440c20f803682464100302038043c40e0002852401661002403c01e801d0fa0040c1080f54011801c4a5a1610032401958103041c44800a4130a40046006015a0400c040005e4001d909417070300d80c0c001d003c1034070407901b0a8140000c0300f0b0b916448100c0c903080c5140402d0800041c0004207912411801c1040000c0c0da00c0c032030416606090f045980029688030014440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 751924811 1250 751923561 751923563
    0x3091b030c0521060103030e0103050f1504200c0102070204060501020309030a030f0c1502070308101a0903030706050106020708070f060e0120030c10150302060403020910050409030c05010e2107020409 88
    0x203c4c0d103507503100d250141c0f20900d180340c1540020301d404005601d50391081c521b60f00070180004112844511441400301804c003401180601510030a942c00304042c9502c01040c000c50340d0400103844603618810082541c0c101d520560466005101d041c01c180d0700455416042036150400c1095101d00c0300040d00c5440441c24041c00c035060741c015041200249400a11141c0d1080c1d580e00055a985070b20005211694060f0300045400c01b04940c461803900c600034006e03080010200c9003004555500d000664a090b000040160032400d000c1081740b0040200030f01401030000464081da041140042c03e0114a015040c104041c01040920f40a58146032061001080094a03601c0007041c02003035503522140f03d07114015140245880c20b460084a00e14180c1e940100343d5032526240d5000c20560300d2000d80905808203584000041c15075481c1b29054540d40b04c0d03120003140901c1c500345942110f0710316400070250381144000300d60110f062210700c90313600303510800d4688071051400810000c20243c10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 751926061 1250 751924811 751924813
    0xa0908120c01050a0c020721021903020109060c05030315010c060603120e01030605030705061b0607020d11062502010f02120103050c0d170318030a03091b030c0521 72
    0x10140040d541440020211520090000c0c0001d48440403107104449125442e4070040c0c1101c0300621109083c0e00d0031206c8184d14200340c0d4054000d40d000900c07401410050074120100110b820011560130000000060400e07040256142d80151241742d2640310080c9203416448095034100700a0780960084121907810820800a15440b49417100240c00c4482122000c6880300340e4200496120f40101420b582e80900500080c40ca80310038040c45401c1228920465000359100280540c8100100b61240101f54000d08113039144200c0034000780ca0703907407004540340c00440420071f001c624000b59850080e01484504074001090030b003280100b00752441e00c03980c5c5000144408443e035407140d1580c1601c0c0540c2c280c80180e034000080014040c64544000d12030000d4a04280c01c4021000140d903201008814440004076a034201d079045903c003c58400c0400c0c0e413a4441010300980d10030f6075014a01c41d403010100d15041d6101d010002e1064842c46100c0c0048160298144c104203c0d00451485014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 751927311 1250 751926061 751926073
    0x1a130f18031e0915230c0307060507032004050109050904211404030b0f0705071a15040905030a0e0f0a05040207150507050301060f0201020322051203150406090b0907050a0908 77
    0x140c03009221040b0780c031085c2c8070400071030402030780f145c907000c201d44951509200651400e0800e175103a801500c0020900402e241d03861031586c40025030400e07d4900ca80d1f405845a0307940c1d040c480090494484c0b0742010f40181e0181c0100310021b0010350600c0c9260b549001c580585890f68007044031001c015450403030700c45401240000400603914000d5019070070b650343c0303a0035503507070351034200c0e034602072200e02400f07a503180c40207019810214015a6041707951040b0311010190548040b03019621580350483d0181e20000e641d50010390b00c440340603801c0004446c145081e079802c0000500c03603605802454411940001c6640403ca02c07030f0040d12580c6070b504424000d41c5003405010b401908244207003004070780841403000c5050300c18800c85e40316802d2582e152001051900c80841c1c0d0003401002260301344120101e840a80303000f0005144507100403021095000a04002e01c015155142d11030b044250410b50b0300039542c0d079030b595085d5100b401d5180c90341e10342c1c986410403148480b241d071041c00700c1d000310703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 751928561 1250 751927311 751927349
    0x3050417130503060c120106081e0106090801050601020d020d0e04090218070f0c12200f0f0c030604200604180f0522061a130f18031e09 60
    0x340410307034100c0d1012000c2e00c0c21a610100403c000f4814038a100c0c1905001c10010302000d8000c5e404035400c80180d00910801d29410181490080000c1c3c100c0d001250044004020564090042951240e420310281541c004d08902c040e50320207030b0f485540c051003401d10101c0216241c40e8000d00790700b500203100d080850016000080e0052041e61000c000480c01c000d49164280240091302440364032039109040c244d000031044078441140300742c60610a50688061000040401102e2910350060024196071503080c10402e00e050034038107465000b5000b50080001040a842d500300b00001191001e83d00104180c00159091069402070b00401551100b00c0e104030025074400da5500a064900f00074030380311903440315445031400116040c000c0700c1c85500c80c00200640c10040e00140e280c09862002801d0750b0000d0316254800c05007040c5d6658680407108094100d000b521000c1d00d00f1103c203921090b490f01d0050041046a102026079000c040100740d440d841403440e040180342101c4803102035415 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 751929811 1250 751928561 751928587
    0x180a08040806010e0912180d050c010e04060602060a0c05120405010c0e0405040807020f0303041a0919050d08130f0311040c020c0117090a0206070f0606090c09030303050417 76
    0x41c0200c085900c01c0c0000130501c00402c0020780d00448841001301031802c2a9116903555600803240300b240c81c4004c20164160307468510038020418401c0000e462800100000101803100002040b4402ea080650030069903401140158015a810b00b01003030700d040d43d110940350707446000f0980300d1841070319040205000e41035005103468903083d81d84100880c005130401c8241c88003a5405446090100450340051800c2280724410810190540342041d50341c859003003c1800c09a0050b61440c4001100c0096141280309005c004070341c801020056810702010804458207600001d01e200780014540c40d800c5018207180c401014002010100141c80e85894446080c00d14146801780d820120394208090000c2452028030b44182d40b04510300d41c02d544940f00c000c6000d4402242c9020f184072150140c0c803034400824180b4060020300c0c002045520340703042100c129a205a4a05103041030309052240c0c0000310b02c1c01c40360540360101d215107c0f4100400d0003e5803005507906040c00040c03402c10003031 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 751931061 1250 751929811 751929817
    0x4031e0215040f15090e18030a02030d050a020406080f07120c09051002010b0907121103070c03170708070c051501031101030609050c19020f010f09061d060708180a08 73
    0x8400074180d6103060b500e200f2a03a0064a8010103008100080000e0006071b040381c48050303005105c0d0704a400043c0054020030308543c09145c81c2030040e0000241110f50324a580129500102480411840c252a0400050449c080a0319a070b00c08103181c0045122280708502d8060b81d440000400c00800c034400c1c50203000218544145806164400600c11900380103200e5168140e001070079500aa80e5115021141300d0442e54080c1d03803440e5201580c0c040c1d041008003441c407030071240c1c461484448090a0291014026403100038802030001c041000d0280c0c401c503c950001c10780e00300342c03540950524280f410b01e00015800083d0741030b0803000000b032010100050542e0082030b24104407841d2910030a105588045811401c103180030072418603006001448010441c07124415600d880fa941048142540c0844040c074602c903032034013002c0083c0f15980c440c07016401c0a51443da01c501c81280c45075901c400008010740280700d15000040c0400300f088408040130039030103050700c1e07503415146800001c42d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 751932311 1250 751931061 751931069
    0xe0f1507150f090308252a0602040e0f240609180402040509030a200111040e16051c05180d020a050c010906021b010306090515032104031e021504 64
    0x1810b880c01052904064081014092100c1103680e03106000d003280640300c82600d410b15000203482507610200440c181f0904c1000e080c416000507941d070b8034003600760124400140580d0100300e200c0050100101009291129115940031002800b0341d42000240707080c0256000706070090582d0b07603090034400716460050b00c1207100301c808009c02e85881c040199030b8003500402d000490285110950009000040903420050303a0001192a52845070f0b2054a5080b943c407000b03080784900d080c440321503d030300a0341030342000c9032601500340041c0100c1c000242d100106014051992200441c1d030f00b40701c002c1210ba0b1000107204503850034180700002035440352001d400751018001d07145108841e40c411b9041d0412200c03030380c0c014200c0b1400002200c04140001000b2410302d0380e2038000080100241c001d09105413110824410f0b11040702007454201548001042109400c00540024100c2c41d00306650560340c000724220440b51009002d10b40407080340700c0c00303540254650300ba000c031645040c0083c0196 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 751933561 1250 751932311 751932317
    0x90b1207031b020d0804080403140d0207080313140d0215070212120703080907050d06090302010b010329010c0b0a0501052806050a021e0304060e0f1507150f0903 71
    0x180794107103442c8031940100200d07005800040d562205507114401880d0824000c2c200d00e89010303900d0f941c00300d4100540e035070341ca03203074000401681400b50180070f540d00900d0701c04091031030072440b251000e0041e5224024400d0548251790307800c0041e201c0683c401815507004d402c00c0c069035404190741e0682c0d085440704a205030100807058281c04c50204030304c07204804003c0007504064807030b0350075110300307200034040c0314684112a400101580d500c3c0c01d18103600d0042800240842c01400c00030300b92454600404d050604020b00c1030113810381e410a0300000b2111000c480146105000100c85490446001806409040013800002601603000a040782e004842000b12245044a10510359000031448000d00c040300a04020890103140101004c0c90507106445010b01490301070b4814404c080d8001c41c2d203170700104050001940004a48a00c1c417812036030040700c4100c000000e079080c1000314580d08962030100d021800c003c00c0e0b04105449510200040c00140054440140100b40d00e020503400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 751934811 1250 751933561 751933571
    0xa150b090a0f0b0304060e0a060912261503210c01061710020703090503030d091709030c2814090601030e030307030b010917100f02090d060b01090b120703 68
    0x481c180d55804084038000fa121505542d10360b1903510003818002860f04c40340c041c2d1480381001545a203d103072031503803180007410304c0000c03030201c0240062800d080d404138a0b110340741d0113010610b2071030104ea8000412514048080d0003c0d010905089504815580402400c040e19602070705460140080d42d11501c020400c2750390314000008005c140d260740c200190007070324250304810010740080060900a0521074480c03907448010031307e913038030851803d290300d80d03a10f0130b160801101030076581780c141d003400682e81800802c00010b5250148000303900e03c208502c024080121119032007401c00f0003200183d00c0c2c0c529944051300c055101b0340ca001d89214142d1000061895030080c4540010b15912100075404c42c0d5640400703600400010b41c481d4148950294001881c4014080302c035131003103c000c09050704001a202d580152506820710012160050120f25025159400001c0b1502d411484c045046e100403c0140c68440c3c1d15080040340c5c40000503102100c00e22941c03c140255405d6800301301c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 751936061 1250 751934811 751934819
    0x71b080d0e0a060c0804120e0414040b0402040e070501050904051009090c090f0c120c020a050f0123010308031902090607080309160f0501030209032b08160e0402030a150b090a 77
    0x28807036001c80d1b005107100c15100b0142c3d01e041c4105103030190f10030b0203003002844142c102000c410141040390105c80744880a01003000318105030207541d52803007c000040201906120000c2c00e14040c000d030081c02280e40b4800503805184d120b103098002c00540780c1c100041c0c0380600b041104000300d1700590110f80d080c40440b041100c014822185481c0302c40d5280003420946140300e4000d4003008201e00214800c0a80c400041070052007150420136071200005a400113aa0403c4010b404400606000007090401000410500381c22a40d1100000c00384650718004403414000030700884c0c00003030b08501d01107145d00800070a000150b018410180844802104001100200c0d401600802c408100c2d20f01082101d0b50190300a0215100c004059503881e401e02c40c00c84003011201012180b1b50341d000482d15122030b400040240d0008040044044201d044800281c482c00e2101e2049018650010024001d001d095000000264640e41c9a800c0725030381d680304504980100c12518802c03010010001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 751937311 1250 751936061 751936067
    0x409050112140c010509040906020c0d05041505040b16020a240e1e0103051b0c030406091e03031b0209040c050108090102130504180804150314071b080d0e0a060c 71
    0x9100603d0581da100d28001601d0203010203480300c01d00480300103400740044c90030b2319018010036102402554441e51079038604074620b88088030251851052100c1004280901c98189007101c214035041c02c0300204003c01340c07010944016aa9101e10b0300540400e2607606510162046a4071003040c1d940d0300500c010010040003e8041c504905086c422460104c17154154001d070081c0364000003040c0110000c1c9401c03010900580e1280c1301010396608001410b11100c0c0d084051500604008030450022aa46010031080d00d02903005c09020f0040040c6000300f2034804405a4282581c0a002d82606040c81e25049000b15454040c0e51301082c4000b0000d1401c100500c26140300c0740d40011120b8866181c90280401055225048440c1121300130b000d2011a540d8030041005102c20110030380b26810b00903000702120410821091030503414001d2100046d403201021100854110700110710b07404502d00703003d030b503c291071100e4040d07030a00c5440c0d101e030200400c06412035806020705203d4982e8210080b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 751938561 1250 751937311 751937323
    0x803180f0406150c0312090305070c1401080a020705071d09011103161d0307030b0406060504090f0b06012c18010e0705160203010216031b030e1302040905011214 71
    0x341e503040b0803c140e00100c0c41c0b140508003503060082c10b0070310090014031040401e403885040d065012801c00102c00c2c00300300e0b460490500130701001100c03048810040000030401c00c070140041d990950082910424031909101c1c03a00142829188105803a154031031142003a40115100f243c00d511b4540704c9107001c0211021244160031002e41000078180128040d240711a0310040741949561132015032041c0c0d01c0403c03003d00918040d4000c01070514042c0741c808180c8025070010380c052420854460b0008a40c00b21404043da0b009502009655a59004072442d07136240d82d2900706000c294903007039100d4071100390b8500c0c8071406441c1d4501d007164414441d00c00301400c1c8940562310005400240c8010310a0001d40004115005038142004250b00002d0036600103400761014000b004550904060f08400b50300411205150149910401618094000c20000c41540c1c094503440711034200703086a83d8110380160003180010041c550311660091000c040c205000c80320000c0040d90710444100000d40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 751939811 1250 751938561 751938569
    0x3050403050a050a18090501081e1011130e09010e1c030507021207030203310308030709270513050606150d020a0c0507050f090406150803180f0406 65
    0x3078a1a04582c0c410032a45580b0046109040144490806070760804c2d090300240103050540700801e45505020717080307090404100160180e030f0000d42e200f440d12500480c81028060300180d000480082119140103140b10f15a5011190802040c0202d04440e280e413249005908000c000c02c100018119866610b0ba4040b000c4906002081981c010b15031098000980c40305951056803040e0342850989403d40c0c11841c0111b0141e04081031960036060902c0c45400e601c000080d8044004028007240c02d4804136600000d05440c000000081010b8011112a8010701141103161403140c041901402101408207803039190364100b80108081c00e496410381508160420043c0140d0f8490000304000071071061140c0d84111024003031340890500a1014207040f4045403280700c0007503400c1ca040760800036030b40c01c51445184150300c1440242c45010303205501035484000000c000707110b216042810a42544024450300c070018a0f1890000000c902c0140c210301039441a4849580c1001c1105a40c40c17802 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 751941061 1250 751939811 751939817
    0x7020a150605150d0605130227090a0b1513140f060d050a09120c0203101a09060f090903070303050114060a030b210a02090c2a16090608010c03050403 66
    0x203014803c8000c100080200c0500c0100004401d86c0e01c001150b08602d10000b0000780690226000c0402c015101508030300b802c140c0ca5880311032010a000031030329040900a085055620f0914210300c0d260b60040407801c0d9142c0016546a60404080e0715080c501030007034200b91140126801554201a00007030f1580d03000034421820500d1611100d401000c0c02407142094544400030f080124590800c0c50207400300c19507480c03103150824014546051400200c00e9841480e0141d64680004603420705c03455800200e43c0a240d84d140e81c030008040c07640c24042c096001781c030030303013482401c0706d0000042c0415403283e01c0500180eaa00d820300114500042045600300f9410000c18000a100b6030141050000c01840c000c1c1c010b5000708000b080e28502d00e00000130340d0208801000f03502e051000030760711081d000e49403864054900035099640070100c586034101c2d0000001041105400d00c0003402518500c6002c0350708036920000c2e0005072220744100e600551803e030028900b42d1103800f408d84541c1c0c05031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 751942311 1250 751941061 751941079
    0xa0f030b100306060306020403050c0906061b1005071814010c0f0812010e011e0f05010806030f060903130801140c09040204030203010603120318030e010503040606050907020a150605 80
    0x18031409040356004091800455a41a01000044072841400003543c02107000588483c10f500e00245042105452a4811048101003017a00e81e168812180d00e0100000781c40440d1100800c1140341000134200080d42c035081c1800c01c0302030765020490303c80c4240c5146050b01d1040c0da030451140352980c000225400a00720016081c0810604410b80c65124801d40c0b51900e00f9142403580c1c80f20300c07420b8206141d021100d5004010700074024140091100c0078000220103e40b410b9486001d40c0c20520602d03040c45001c00c0043d42c26681030285241d80d11f8100144d5075146062007500d9201c2e4040c5201034410b0301c0c05040410304c82414416590380e890102045a001d4958800c400f51580141080aa00580801010005031001c3c058a002107200f288210300c80e000c880350103401c1d194841800004407564513541030120f075110840c1c0400000c04e00f0720a6481d1500d04000000e85890b4100ca60044144402c0c07004103540020322180441c01401034038036116000c0b04100a0b9446c80c4641a403008000e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 751943561 1250 751942311 751942313
    0x203040b03060a03050d080a05060a18090809030616140415110c0d030203090f0402030601050a0f090306060e07020f06240303070c0608150f0d150b1c110a0f03 70
    0xc94000c581211004100342e4035240e49594142c94a40c40840400c009207034581400080c1380b19000301a0040e1044800c5500c0c3c60421070b00c1d18103030907241c081e14042d42d2201c0505050000750003c8034508000a8140c880ca890070a40c814480008807844c2030014200c100a101008404402d55082d10484d110222060010190840c0c0e04141d00390400202d001c1e94041074031944d41c02194814692280e009161a0f072011010005600e2000c2040c60003513004000b0803181c0da80c06401c6a00180c0701d03080103c48080000022540f8040e141c00040201d450070b44040348003e684c0001c3d074407845117039080b110382400303040c0696107074002900e620380040090743c5243c11070a41d28504910601001d07084030704250090700ca80c01e040b400d551000000c00c4412090120011440248450115080e26034110500351403000c07034200c00b66aa0003a001c0d10b42c205e20081c14040b9908841c1400800400400006030001e416145200c100701044801e860f00c41e804ca4401d0802000080845904428407a102859 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 751944811 1250 751943561 751943579
    0x902062d030609131a090706080109020c0a08070f05060f0f0a0e0d0c06020712051c09081803031c0b033703230909070302031003060b0d0f050a05060705030403020304 73
    0x304c0c07001119944101d50320181c0340ca142c0d0524501c590300c0303e8010310303083d0726214000e00b00301c406030022504180104081042145c001407501c04a80e80844490b0340e03800302d800c10700c020010b0800018258040d100c00d00040c0c40686003140d0054203040120300303c0c1d4503141892001c50340c1c00054001d05800c0b240c01d600115000d0741c414003815014001c00341c03a002055907943d6501144d00d1901000c541c010801600c04103007d59803050003240b44200f0000482940c4502e80107015045035902201c8569000704030a031028403c2d194030400001c00707200546a52110403002d80000303d001400303849880c3c25000d9020720300c480442d411200c101c4184400c2e00007000741544080b022025024005246001044050000b803015011020449030b80c4d01d50840c1000c206901d000982810308141c01031003030203910207140070303c0c204895001c42c0026610b0103440105803001c00040b030240c03800080c0b98000081c41b83c040340701c2414a00c5882560f845a90b070310743c00d032a20301041d503000c0e0059000b800107000f0201 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 751946061 1250 751944811 751944841
    0x306020906090414071b031202030c04080303040c051f0804060908070c030503040801060b04080606010f0e2809020a140c0a020d03110f2107060902062d030609 70
    0x64400c0e07190204002c0414140d0b44600c88464400303c8040070040c0c6940d02c00c6568034240503c107820814264592802004140c04205850000e50f0000103d451500600e080394002c11000003031700d889142505090101005510400b80a007000c1804111150b404503070090011220752540520340d19651141c4009020610040b01d9210703003000241c02258040451000542c81071008507904c5040403103050030f540a50b800700c21600001e20040c02860800304102d40d01c03500038641a14080803003001290701014140c3c9917900001e504807103083d446900c654a00001594051268040e0b07030b1095444c04138440c000d0307000300003020030f0130317064404400500520402d4040811100550101d030005040d015207048100c1c017050013040d040e0310041e41031091290307080008000c0c1c4442c8800d5140c14039905251060120039000014810702002030301c2c2e00501c1107540140c000307034480c40070303055191207000141161071101c0e408000d894007100010049030300c40c100181140c102c54a0361052080200 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 751947311 1250 751946061 751946077
    0xc03060b1c05370c05090904020f0d1b050f0a06020d0c0c23031608061b0c010c020102041e1a07061b0503011505040e010b25080409180c030602 63
    0x701e00fa81d003030805101581482c003000c3c0420355100340a5018080708120303a41c820089007444001d10041d8026560b00701042d5205405a628002c003c03103000003c2c1905c07035095401007880d01d080e04001d0030a1207080c0c00c1c0c82603c00640d004c40410000c00100301c0059100c2c0715110060740001e280044503482a41c2e01d41082e44903c1100c0512915086442c150b6016080c0c0c1ca160958002c0c110303001032504003d041c807040d600318884405c050500855030345400000b41760b4004041d1002c00c1c48d00b01d510400c1117030003d20380c200080000e4038200344002c3c00307588907106000741a0007065400082118841c0508215000d102c84036017084802d0007221415044814295640e40d03440c5440d003003000020180c000c2c0050b03d0380c2d849969605200b1040d810080da04003505c10010b06020030702080c0c0102e29084d05488188951940b241080f1665003d100c001c2e402d070254980000b84040100206000070303100f510004082403003070240038041000401158207011784000d0b40c0c2d402c100082080c50b40200011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 751948561 1250 751947311 751947331
    0x20114060402071b1404061d07050c03040e13060c02070b091005120f0103020901210f051204060305040c06030c0c021003063b0c030a050717010305010c03060b1c05 72
    0x2c00281411104c290301d00c1d80c0b09500100b19600402c030540b07058425000540782c0f00410640c0804101060142d54000410708014040c00080c0805030803c1001601c0050821818950581c6080a04000300f0942d0b1402190b0b180d080441d0100310b5800803c840d0b05640d90f0002003414a0b96003420810100c85401d030510030b03c5410000301680b102d01c004071302e22410055034801540e500d90b105220b5045c4050380040411aa8203040c41d034050300a2107100441600034030454041607103820300c1e9080248821a0f03500555001030b00082c0950150000d40c400c50042c4000444c01d039603a2002d030291075442001100142e01d441108005281820b031500c44000d0503e0005541c82e1105030804061841d4110321000e1652004404070310440c868040c95600890034950019082c90b1002095900000d4000d400c42500e81d00005e9410384150343c100324440c1e910320003103010b5a41c1d09182d070017404010402c400090a241d00072402d02d040000700d030807803220720105c8800e10005801c010018240580120340b6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 751949811 1250 751948561 751948583
    0x20a0f0c031502031b0301080c06031f2d0e0a0203070908060106020a0c090605210109020d03051206090910110d060303020f1504111e0a0608061002011406040207 71
    0x10411280e4902c01000810354010307903c0c18400035085140784082c100181c900b10030001445030391000b2a030100050000e035241500c0f034641e590302c3c40d2003c81c14650700d90144103d41c03000500b122035050b0b0b5410401000320950b6412481c0502c2c019400c103e004001e5010103190201c0c652402d02c8d4011a4894800d16090100c9074642803003034140102030b0701140c0180d1000b0b80e08418840c901c440300005090700c2000f000481d01e80400b140d1030b61000d9056003400407801c54021000710003034008076241c80d4014020036508400d0b107005445034000e0240188000b0140c80020070310306140d4070b1a4000c180d0900149000004003011001400412180d49a40c42051201030a1504070340101c1018612980241000d035214090042c035200346030031040c0002e001c10f410702c0b020591110b52100004025941030682c0048440c40e481642c0d05036801c01c0e048100c8080015000c2c1d401014140580c1d0300f1035808803002301c251000c9081e80e2403000001040b44070780c0c000c1542c40c80d140d801000f105105000e5a08 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 751951061 1250 751949811 751949813
    0x6010e041811040c03050f0403140c072301081302120705060423030a1a0417070b10060c03091217030a0b032802041d01060807050906040c020a0f0c03 66
    0x681d0380312100c048a11140010b9010114901801404549111441d003084241307014010340000c40c10250000d014001c0415000e08038032b0102c0219482c250152007116082540c900500001e07505100a000540011001c007918543c890400c00740644010741c1b03000c1203000541c081012202040103001c04070f201c2d58500290039103514020304020907941c4c0e0b0042c6017107549180182c1c074102c19140203209401c075403c4c0800244111010203000c400d41320301ca9034183e58501d4a40c1000c018801420140040411901f08000940d81041c1c419400d0b40543e54902d9520034080e5280c9180310001000720b0342c280c600b80840f1502d003840d10842c50289181d10090000b801c4d240d0035941c0140d81d1540c0c002d44409500511f030408000d0b200074000c091603044c01041d894420b40c1c1c0070006412000b445140c03a17031600c0340c10103c075220315030381409803030001c12545030b41d1000c0743c1e503407410fa2069a001d0060b210000348245028070503030740070b03000f1a006088820310307607510314a5000501004440705008880c0c040 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 751952311 1250 751951061 751951091
    0x8030910030203280f0f0e06010f081203150d05011e0204061715060a0503010305070f051305070306091a040b061e0f07050607030c020c1905010c05070b0d061701050f06010e04 77
    0x142d506010007000420000e42800b050418105070011202c085002c0820070900d20005602030304c1510800033151a525000038503e5100d0a0720005644010381e002401305004040d4810345044c50110000d55080601c804010f05074092031041e030000c1040820391002c50901400c0040d404121904001140c490820004041e5007020b80b40702c00040010006100b005810011310f07001d88030b0403818102031460000025004550b84116107441c50312100824220b070b0207034000300050403018200b0700540d00001f84241d060550940058401d0b410031004440c44d0500780704458800030b07200000600000d844402030010f500001e030a441c1e40100f0010140880c07418410305000b00304946e0003068a440e0204000d203800c40c40300303644d4030a440c0f401102c03004405040003030301241e50a080c0301c08036010038107010b070034000030354002d417140000040d007146402251b42c002000e03241004944804280c030401018200c4d00d00311901840030504001280c3c031980205000001c0c91402000419210000c030068 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 751953561 1250 751952311 751952321
    0x609030a0609150e060a0911030a080a020d0503010308040302043603080106110a2607111009030c050d0f140c040f0c020a1502040305060108030910030203280f 70
    0x741c440030340d14100841005110398030110400c3d501c0c8414014211080389150312508050580100c550b030b9040d2003001c01c042d42003075000303650000341a0707a01d81da420700300310034030f0382c8200d0044006008110500680310f00420130f40c1d0590750010340403424681154203100041c4102d8041d41c55403201b0740105410f00c55503078107c400342d01284030494482c4029240141c423409043e04900180104017959821191001a21504440d00011004807001d00000c03500100e5586218481e10100300040c240203004407102805c41507a0195600780181a00c208219100569070100500203140d41804204510740030840390255070184011a02d102065991140c020683c0c4070450345540000812a800d45450f00c40d20210400e0410140a45130100e14000d48841c58a02d00400f01d107411200072086100990695004d0f562150442c5c40950b101d0700355590340e03005803a2903845907031001c503c00f90b082e2090095034040d0300c82d01c0a120407401d100c035020408804407500031403080c3da2040407400d002c03241d000b0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 751954811 1250 751953561 751953563
    0x40f0e0f03070c1409130204020c0a050318060406090e0a02162001030e0307230102070b0f01090606050901030207020f03010c20030903190f0b010308030106020f061605090609030a 79
    0x8603078070009481c003220366502d943c0c00244007513504546036800ea140c0c5030750f00d42d001c56003e800091000b80d502c0003c0c02809041c12030041445510304090400100100520403440c0078103041601c0011401007003c1441a03008950004605401c104202c51840c0d0020703800c8210b0307490240c181240020243ca0302000490161504440108a104061070190030402c80e101c0c00e1a051111002c0380120b1640c910071108000c0a0103440711001b00c00b205030604404d04035109a0080d075035461241861602d4480c1034841e01c1c04000e444000141d410624800c0360115119a282d13075050459100055000b500080780c01d0782c01588001500c6c14070341c2c01303100e1010b01e01c0c5a501c072491008482c070103090b55000394401e4140e41758410040704009a078006030a00d0416002803134072200c5c242c3c03440c004102d107a0034140104441d0380a000881000082809141603403200d0b400c8030420300100e0002940c5100560320512420f0f10300000350700452043c40246a09400034000a103001d40910209140ca690464 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 751956061 1250 751954811 751954813
    0x1009050c06032e06031b02122b0209030f01020702131d101e061a030403090305070e0a050c070b0c2b050114060408280b071724040f0e0f 60
    0x700910901790103110700d00e00f8005405095840f0380e11048003a40e940c41051240c8900207001c141c80c41c556070146044803442000d031009a8000180f0074120703001c4c0d007003054003c1c40b030b008504559451308014402d440c1c156400071308a0420403541d210718001041041822000e0010b030504021160000300002e40301072802d03c000250b0032610440700c0f6410340c0d0a00360038040034105001004808400d52078403c0c603d255651490f9641c50700d24054031100c41d2948021b0803801040d00014815640000b40c4d485101503c8081c8055641c0c0d4003c2c8001e8815600000c0046260f00701080d10300300b14402074602d0704228030788c070061144c46a80003891600c2c00024080c80c1c076100d0005011041100050110030001681d6260a1034144103a031511091002c0c240c02d12100705000219050368040200c1001d2a000582516503081215000700b00700c40c0215006080442c410100303d500722400390f00c1030202000c0501c1034510f11550b0411000d00301c1410001c07d411344035105d000002400303001144110202038 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 751957311 1250 751956061 751956151
    0xb0f0d2306180c030a02040f030503040311040912110c2d09160c170d050a060f0803251a07110705060a0e010c05011a031009050c0603 59
    0x9034000c00348810040425019907541c03810415190114001d05801503c50807007541c0b00d81c2c0f03084110000780125842810b241c0c1300443c0000505c580840148140c03405030200c4002101214280400c0c0c03401d90f0340040c28070031801c049809861080d55040800d07404c4c2e8042c0d815010100c400110031219221a1070040756600704011141030701c43c0c4000300900c0040d00d50a00c18a09500b880f58280c000342d282500b40700007460748908105060001d8407140e403a42e050151501c020600d01070043c4801c540100d44545000404980c3c03c000c00d0f915812101400021407130014a641148620183c0c08924810300940b4004600040e031040218960515031800e840454645154010503503041240442c425070403005040c82552905011606071050700c0c204058000440c9004940c0e0068229028205500c0c007401512a03024645e8900700f075030300c1101101c44060302217203402c2c00c40d60100c100030696840945040d58504190000d90340c444502002c41980c41800039200700742d10b14801e40749414074038003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 751958561 1250 751957311 751957361
    0x10120c2402010506030c0109060822060c110c151c0c020d02060a0509070b0f1209010605030f010b06030f06060d020703033303023115060c03090b0f0d 66
    0x244907051307011030b08400500c040400c0303000107001d29601e80070745000c0100000004070540c07481e01c40349002040048501c6d240c011641440d80c024030504611200040c804e0441c40881440000c021640354802003401c03d200c80d04000d2003445900142c0c800f00d482804083d450a12600752080ca01c440d46281c018001c0c48000590007800c182004010842c140c0c0344c00306002e818000082d41505a074040011103545e1454049440c03210701407da1180b041d010a10100200a00190040000c6a40a03421124241c400712106400da0f01c50f811129044031040c0005400b001d12100b03004e800050240c00145000e0124004c00c09a0f0700c00042075004c41d07203070040b900306250b0000051039a201101c04481c255865030500444400706440060700c107221520030900030223042184d00600d2804030103c0010001803141034000b40241c2e980c2601c7c03030100c140000035081d0040c2880d004480d810340d07035070070858140b640c0e5038466080800708110a0405000c0000c01000922651390100d1000303040120880700 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 751959811 1250 751958561 751958563
    0xa0f09050c0a121101030f020c031326191704080318150304020904020105160506270d0320030c0702040b01050a0507030c050f15010306050a0510120c2402 68
    0x8a684101d4005200c242c641c4007103540c50f13080c401031100c2460042407118103404c01e04040d004545254449001c0011451030190300001008121906d41c0303003850090448419078003803c104000f510f030254122078241e000340140b4841c003100041c0b2803000481c408803010f0900d000382d00300d87c02c40d40c49072f4000143d036040304820100c103a20854003160044031486854460b808180000392000780613016480c0070404582c026420707200f00081482e5841000481800c0007a42c0d017009a4502d550001c040001404000c13928901d1402d900d800b40090880c0703440c00c0401c600400707209143c01c1918002c44a00d503201e48000005602450f441c40c0c0d00c580310003060041000300d8840703100f07441c103100040142109242c0c10038287c80d107007609424134540d94209400c0c82414100c41c4003004441d401110105800c010004034042e0603a030003400200b04e40ea590140950031520309813404425984403000400c40800300703074000c0c21010300c40c1d40222030781d030f075528071043c5010032401d05504e006040d02c40760414168 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 751961061 1250 751959811 751959829
    0x1030b030f120c07230d170d020a1103090109031205251a01060e010311090a0305030703080906010e28050a0204050418081b0a0f0303020306010905011e080a0f09050c 73
    0x2211a4829082144a00c0c0380301455608a12175000d1520034140405120588201104007800328100f55580d80140d4141402503000c2c1c4043c3c40443c1c1c06a100d9102c90b94000255900c1180c10b840d05410981107441e0400030090080300e58041000402a8003154201124440c00a48851540b258003140500c1d000400801081c90480c49000c404010414282c1c07000c40e0325101c00342030038000fa840d0a88007210300d03144a0900c1c05500080140720002c03c2010000050003446d01036030b14100e607922001e0115442e0305080c4200d92094080303001140c0d11416640000003030300011807118424004c01c444400903070350110b0740001c04560220f800c00150070140558030100c41503003000c00d0790628654170b40f401402155400d000071400301081a190000400c0b06192658009074205800c00300ca1034000c000e903008032400c41c009500030718009620350040d0980ca442c00c0502c1d0040b000f03541022012140708400030401d0010b0f41c2c882c2c04007000401548140c10182d8000d0003c3c190745400c50062100240c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 751962311 1250 751961061 751961069
    0x70906020a0302120a050409151703031005041d010c020c011116150e0d060b04150b1b011e05010906120210050c03040e0c0306041103100501030b030f120c07 69
    0x5080320216000090740842c4c3e48480c0d131401c0c410142c64170700248085899010701e03003082505e10710307242c11554010323200d00380c010440390f401c05401540861994483e88900055980c1005072000c14002d10640c5010740010521070202400960400070780500c0c94203542c0007441c11030150b006100810b65550b071014804c405180c4031002468400c80d43c40e64030014005621232407003480c01d14002e506145104007494082c41500828420b610b16060600388000d10b01485454451860311074010645c80e920704405c0c048600725a01641040009554048001c03102c06000d10315540c0e0301880001403442c106004c1c2d2601d0300540000d9030b0740c1452201011915140c101a003100c0f100d000381c00059a88610710b144207013681c90913030f40f0765600451441c40c50089400c0b6051040d4007408110310089440c02451180400711070501080f180c03000c1001591000342d4501c9a10101140180301c0c42d4081c2d0802c0c50700101c0078003100d10a04d2050742d20380c24200008200d9560420005010b4a41c440c00c1200c00060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 751963561 1250 751962311 751962313
    0x31e020615091e19060501090506090105090a030602040801022a0a03050d060b070f030315030b130c0b0a02030a020f0c0310180c080f070e152103070b07090602 70
    0x941007548140800d249200c8140384182d0030200059804600961001d0740ea1003140d1030828a402d0001100020b40d0401c03020080b418500940000d1a6124100a1045a00c007810381480c1540e504d00445040c1e00c8800c0454025140440020000c4d90320710041c80200f49140c001a2600f204400c5e000f03030201109030b1a0141800c5d411040c04482c804203030390b038070107500d81400c1d541c40c0060040e103005400079600600300700502103034400601c0b2100714175100700e0384a5902004034400c80d40907e05a050f650101401071a690400140c2035608407207a030400600a41d00c60001503503408401405500c10107844c1c00581000c60406981c030780403c40600c03011102d00187c4040d41515020130340c2d0f00b203141c41c2c40300d80f15125032107903094441c49483c00d001c8580010440048a49582c40e5656840110070500c10602c0340a50001d04c0101c5402d10301d000340d8000d0000903900f50362000b00320f0380c001880c054000080c124240d6243c00c1e02c0401c0102034503840740724850b0042c40c1c007d5001d010076031103038011025 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 751964811 1250 751963561 751963573
    0x3122e031203090302160e040c06020d0e042318010b030a0f0b28090c06030917030618040b010e061c1b0504092301200f16031e02 57
    0x180784059408041d120501c0c0000341d0030000c2c00c1c200c0c90f2012180c0314048100e2a4240498031142e03450080e8421401120107a440590314841280e0b0b90782000c1030796000801a80c0c0c0720799985480d0b00130a040224002c0c0b2611022182608a03002e610192140000008000d102d010810028003440860300b00880c0a0500f040c0aa201c4144404600000038502103101d8005030400d04080070441c04203a03402904504181c3c0049040010450203901f61742601030340170002a120721a02070798090941c088101050b50200110800e25034002610069000202030080b400e000150102603108030b0181c503903500075502d40030030a00f880e03a003d002c02c0d006159201221003c40c00d45c84001d804c0341e43c04405c0c00d0404841242180e00c900103500615402030502a4080a2000c070f034402002160000c9401c804d11220a290781d070882e00c110080c8140140b00940c1c03000c1982544001c0c00c44148000009132508810300c1141880003040c0c441200402c1c846545900351040c0401c2c1c1d0001d0104500080c64 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 751966061 1250 751964811 751964813
    0x10f0203010803031902130e070e190303210e100c02070303051623071a2809080a061406040506130b0301230f240d020303122e03 57
    0xe00c904c8010418103442e00b10a9841400140c07503411207503180b5990b40f507010380a465140e0070703060302420349189000548030141c14155141603818003a19074140100045c5c0e051a43d40c0c1500c100c034900100c0582ca0118a041050001e981d0003500c19401010303010302040403038001680c046442004c400d00465001190620009411408072803403405007075918203418009180114460700b40083d0840d41c00c0e081c5c001000d00340400240e0038265160031040419035511004250940e0003503650f066411036a03080302078401d0203100300c030860041c1c4500e408210f441c2ca4200552a01c0324881048030010303903803041c15020301080480c2c150401d000300c5061180b0300388603001810500501298580e103e50342e07001d42e09190f500358007083c0402848030001c2d030051048650b8030320030036044942800340b0703400380e00040142044809800e0404031004191506135001024841102c50740341080760584020042c05072040340889000c0d100c0c21005110841d52621181c514040709400c80c0711941d01003032810180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 751967311 1250 751966061 751966063
    0x80c01020c01050d020d0c18170c0402090109080303100906090902030a020105090d06050c0c07061404120221010c020c04020c070308031302090103030c021c03020d0c03140a0809010f02030108 84
    0x101c0031150034a0096240c2403840c42c090000e22413545407941c00f0b45043e0713001400e6504514041c5016154000c1d60f01d0b00d9903102030002d0b0b50300724038503003103096000003008208074034042d0301401c110301c2c041c90305041641c2c41d011003514550086c0d40e40340050441520412a062450040c000540030b03001c4280041240340d404130381d40f4041d0300c4000f81406804150310341541c4544030220032175508820b040c461800c0c00482030f070035a0300009034524580076103940842c0d038a0140380c94020b0011040152840c1a1400c203114000240b1400101d83c012180f6204014543c2280c0c0d40341940080c860002400c16440d5078040e2030020a512550302690040c0800c1d4001070780494a5000c480d0011009079132a91501e010b0b040b08610000f0080d0f010300d00d80d0011051603881001422441d20a449182442c000c00040c0c02004400c500000c0040e4405064046403600c1560440b640f581b00b07003880c45100c94414040f5255400505140c4c1c00100980200500c0c400c2c24001c815684540010441c51541016045 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 751968561 1250 751967311 751967323
    0x209091311120606100509030a03030614010c080412020112020a0201020c0c010e030d050c031303121205010b07080d090501061d16020c061303021906030506030106080712050709090b040b01080c0102 87
    0x1a0344280045c1075035549946c001c07021110890f800406803581b007111032401034001c10490040541c00701301140803500650160b80310200e065000208503092501c0c000000c000d45184803412810040120200320782000c5a002500c83c19460f50009038840d18113a203030928000120000604008004201f440c3c10f4a01040d03080c0e98911902d026541c52118030b01d0f80d0325503c500042d00a114108a5001042c0022910400071907c2c1e65654254201c41084204058602c28010b68989150070081000050040b40013481c1415407418085150503040c0c07902402c541c07407a480780c4800705442c0340e400e000154002c1c049500040b4800d60164800c2444802580c0d00440c1858501514000921010400039130202070000c1d17500500500d2081460030341c02e91070203428883c00d00424100000304005140c180110401d458092004220745850180c4203100e800c5d440000303031094000d841010558042d6401503141403400791681c1d007020300b0140f5200e005110144c0c401d0001d9000085411810380c1d011442c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 751969811 1250 751968561 751968571
    0x10b0f0616170f03040c1406160f0b01031101030606020102070803060d0c0314210711040513080f0c0c0102150c0d0e0f0a0314090d060f02090913111206 67
    0x1000030601c0c038a000e258903072440581a10000303001c40c404041428050065200b20720821140ba20b45079100b80b825940f405c8800c000398051403d0040e00002d900c0c0c52440e05025004000c46c2e0038000c8603481e405101242a0001e031900244007089040d0341d6003502583c00141141d02c000c614008243c0c50303a543c64000640a0341c800c0c100c603d0500107100ca1500c0490156070810144000211580ba400713950f01410140300035402d005441f1011f280c68850144c1301c0c0750b60040b003103e541800450820006080c010424050071040b158140b0100350120050100800040000c0c1d60342e060210b6210710703210440103954110350040c400f081140504001d91904111003200c2e29480326140312800000e8084900002c00c01e100e81c8010200000380061440c2d00c00740261604048689a5056008248511030303025406c18012010840095256888401c051b01030810041c1400d00100000301c00a000b51000b4015803052650310003440010950103102c50b000b01c441c00408030442c420182c4a40c0002d02e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 751971061 1250 751969811 751969837
    0x30c0518130914010b040b010906051b0708030a051c06030f1e2f01080709050d1a070503013308150301051602060901110301180b0d1103010b0f06 64
    0x1000701054006a0411410981e01100c00c8050f0480401054024100311403414440c9051000b1440701b54000c00920082d20700a0b078506203012040420a01c1d0610940d40c100d4103803181d41800580140284050000340340580c0d980b075911301110b1006040e1460088110071000d2601d03034104006014914402010765000131420036007170001d00107240d405405c1c40041c001e03044864040b0000402d00c00380c2c105050913049090a1000418011200180200c0303422010840e503800038070aa1414200c021400c1b4443c046100f025904508141544001564031301c000c0f84010006200304030004022000100c1d0448070603140041840301c1c0712003010b554070400c00f40712640b00400c420ba0603021502d00d4621000e0000d100f0f0341403608070440c3c5c0441e9401080f005000d08000b04807231041c1030140000803425592550700f580d003010b4001d02c105003a04c130070000150303503501880341d0b83c1c661203c000c0c0840c2c002c6a81840001240080c1402d54801040f6030b88919003030100700c02c29070b51351010381d0311151280e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 751972311 1250 751971061 751971079
    0x708270126180d0306171c36080f01090b15030316031808011a150c1b030f0601080703021002160e01030201030f050708010e0c1b0f07050108010b0301062a0c0501030c0518 75
    0xb00743d40c4600b40d0f480b9a0310000d0404522000f020044148c1c7e50084801d02000c440c020141402c1e80c80c01c03914902d80040c54403000d00c01050400181c02c0c0482c03010351009041e2454004d41c131000a00c6e00980c10411000300f049640724540240c0c941300d01100a010440081c44040c100048544452064860542c03140d28400b608040c500d0041c0d080d5160300103407808541c0e144000e1586100c2801829070014441c0c070a000b0b02c0030010740b01103001e6049174200402800f400b810366007044000d030001c00d10203003180300302405038011031a585805c000411148040254330350450000409403450b80034a141d8081c2450180140c07030381d0000071035045039100c15050a443d19031507920305007442007044480b1a8241e0f80c0d080300d8509004140c542400c900c03681240d810959034401900d0030389091003824030b80a4184010054070340900c40483c2c2d0f042c40a404500d40070000c4952606440f08581d059442c4200c3c0c90041c851940c061103800040011400c1160401c1e040042c0900041414072006000e04c3c505 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 751973561 1250 751972311 751972337
    0x60f0a0207060e010515040b090105060c0c0a060c02011b0b1609050a080c0a0503010c0206040312090204050112030906030203062101020708270126180d0306171c 71
    0x303034151500241d00c0b060500030003500e03d0f40c240c00307020203403007411460250500d8500c0300d01d001e1081440c0200c0140c240e90090307280804200c5103400030030700440280121b1768802c640d82e9034280c09002402c0b01d5100e1900c0c2107000e00005101224482035202c18160708040440400c14500c00558800340e41121302690903550340080b5031420465002540180740080d011802c9903010980010500081e0f130a160300a940380d080600340e0b0038504558002d030b00114049001702e0f100316004402e407203140c0703004103000009070302150894209900140c180da0880c9882f008041e40307ea0488002c0c0440e107010741c01c5d03007030140015942900407104c146c4100c440200e14a1044429010340307034403039004805503480707140551016648c0703a246420b40c2c1c2d50b902003d203514540d42c000d613981015030a060705421503910000302d03811b501540242c50884082158400311040141c1007241c1d0241604694010030420725000658a8140c400742e5040c6080c2c00081d80d03020100c800c4030500ca2440304a01e0503078189914 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 751974811 1250 751973561 751973581
    0x1031401050f0d050d1d100806060f0f0d0606020c10080c0d0906151502060108030703050304050c09010303030b0f1210021b030c16060201150308131706040201110708060f 75
    0x2184030f000740a07000b20229840b4641d080b01010060140c440d88411003600c40b0320800c11040000c1c02403802003204c1f18082955800d00c40e0207049060704183d4007070b203840070010554940341c0080d00341002e00d86e107507101401407075814442007564800c140e840c2d000a000030040500340c0728000301507640da602c0c00300390304d480e2111a40101c007000d90407083c100001d1542402c01068070906d80a20005890545034003000d043c0f001032030504a8520300c016508106403640c003103402d58406032007030b9054071640b0b0040220b56140ca14580c000c0d44030341c80004a03880000d040c800a10b2100c20400d1040b901010b590303c107444042902d00307290416400040e92100200045000002c5201c1c0e4614580300105400c02caa400001e0401000303c07081101920070795548400700d090b41d0f400030307655940e0032001c4020800128508044c1503035203041403683c0020b50b25800c08000e100c7e000b42c0d02d06029800030742480190b50300050034030009031184010340007a0b800c2c0030384280d0b07503100641901c600d18a003100180c42e000d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 751976061 1250 751974811 751974829
    0x327100c030b0d110a0503150f040206211009020a020307060203090a0c0f03030201290f0319060609050f04051504031b06021315140306030712150b01031401050f 71
    0x200003041805000b0690501e20303140c0c2408019203018050070140070443c1d1a00041d12505a052900b5408e05680c403490144900000540f04980254091065422110b4420000c41020400d03070b130114a18a08803c1e42e44900800c0d90055600510401c102d030a1140d01204035041c05421090140e600c0d1100c0414515101d44400050240007a1400200f0518407030b08520080724001c3e4002c1c081d290405000307078820440407901400102e0402020354803410011040e80300b1302802000d8600700e4900e40b12000c4d2107104242c00b00d444a607106428480340700c161107100c2c1c00520940c0005128941a5100383e6911405000c2d80462001000002c0401d4030900481c84501002d8400d0101e01e0b10618000c4003a41010840d50f4080040380303404110306540130003405804607035a40d09041d4111200460700c0360b82c0003400c84c5405018030140403c00382c3d00e5a0510903003038030442c410300310f02040250070411940c022458504150501400400d140704080d04a4150350302110900c1c40828644001048c000f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 751977311 1250 751976061 751976081
    0xe030f090a05091305060606030f15120106090608070f03030207051302090402160b060409081b0f0a0c050913021f050702090a020433030507090b0f0327100c03 70
    0xa203642c00c2004c0701c00c0000141904074400c42c2150b010703885507420441107001c104e64a51410286034001095540a8040d2104080c009854203540140094503542035415a40041983d6510307100e040040d8141044401c00400341c2000004000c0d045a070020340340c090501c19940f0401204d2403000100d651303941190240760006004564684d62a201410f400940039401c0da4905000380024042c0c0c2020301500e03620980c8a00010300c2c24110000c820a26000000c3e10b104612407540e08110781d800c00c001484005000e034200c44100d525110421424400060002d40b4030780100c0d001c140107886852110414592121b803040461a200d00212040c0c0100078011358000010024819044903540c001e00c00d4072803010381c400000d1404034440b0842003030410201000309203010b0341c0103160701c80d41c80360360846510b10b01404081d5854100300029013100691905403440001880802c010410504003948045800729100200f044000d44d00d9103a0018103450294550010524040c8641d010322058 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 751978417 1106 751977311 751977319
    0x218041b1707020c09012d08030a030902180718140f040221040b0906010e13030305101a0408010f0b1c05030714010509010507030e030f090a05 63
    0x9124000d0032142140183c82d662465a80c1705900c00f4000c000c5030503151803440ba50381a07091308150414820351014011882000030b02e0010080d00d0311008142030001c0e100040740080380c800c0881e600e00d005441210f02c20010740b03c1d048015455500d08e0340101404081c0c6500d84009a4652600c280d544100c0900c4400c10ba89059001080031028a658a003c00101e250b904000c00c0c0702900d08450000e01c00d003c021141d4010001d0300c1c0100301083c0340d251981845024149000a4600081d04240c0c03188001552941d0103402d02d0020032a0765451020200b516511083c240c2142c041c00c2141e5092103042c200d041054001c0d5081d01a000b44031000340c4078905004509030005d000d00300c40d14002030201c840850b8103c40b2201c54a00070300004034aa1500030007a0b402c5460040c1071000b854a0280b0806407481c00100750303904240d40c0a542c6aa0b80d44000000b03c20070140d070300007a80 = true := by decide +kernel

theorem cover : BRFrame.Cov 751798561 751978417 := by
  have h0 := BRFrame.cov_init 751798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 751798561 ≤ n) (h2 : n < 751978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
