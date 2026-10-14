-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0974
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:35:25.315622+00:00
-- url     : https://prove2.me/submissions/2ac89f21-0b12-48b1-86dd-d024d46ead2b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 175000000 ≤ n < 175179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 175001250 1250 175000000 175000039
    0x1101050f09040c210c091203030905060f0402090c0901090b0f070b010b180a0e0c2503080106030606080402010c02060d02040f09020904060815041b05030607020607081008071202 78
    0x300c034003c100084a0358028804080c030640f10214100d20040140144107113078001420011080c8a81b0b281c4440412184080c5882a0302070012558070105803525428104801c0314640c1054030b003644075165050200b14036403180c008650940c10181c40300914145084010103a0b504141d0480040c5801040201e000441140819001e40503104516850302056030005030b410900e81d5907203001b50481a01030281280012403268410090200e444d6034920580d000795020065181000c01c40a28101410425800c52051816108039550410070541d40740000c1b41c210006071000790210308009016400760900f04001c0403c81d290344405803401e50340c1e14010301e191019038001c8240545c0400c14071603510f0b081c00b4000c01441740380e00038039811002d01480c0c0002140904000c0500321740213001d201039460b020b80d01b4002d02008007030b15036030310340240040c3d100e50048503007034001165140001c44403c04800398005444040b002040d4039802c001043d104600700000590f4003400940319000600364 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 175002500 1250 175001250 175001261
    0x60d110a0201050703151202040203040c03050f01050f1b030f07020309120304051201050106051602180a0e01060602190b060a080a03091503110a031d100917071101050f0904 76
    0x305940001031501d01048002e0840d10103404072407556681a0081040c2c3c071050b0b42d03e800c0650100c1d0011307a42c2d2a0383c603101d0300a1840c2c0d40700401501881c1140b0188520650020340b0955000c1101000e5543d040700b9010301a041035450420840d0030300200d41c03140e8002038510ba005c0c0f00d40c011603146c406528001400d01c0031240401c622540300180038403203428000c082446201010000b4441c80d41072050207810350050350805c0303440c12640b6602c030003550b491301c192402c40110410030940b1410a00c0d0180c0140c01c8105060a60358205107001811503c0001e001203800350b9200b004d58018a0342e40c07500340b94080506080c2c1c4c03050451b030b0b0114451a0920414034158401e44403401c0152428000f0400035012031810810b052411a1a2017514040012030786103a03102d00d030008500b0000c0040708000e0040030040c070058410742080e01940700310799010f414110301505000050f8001c100718101d19208080f8000c201080c00d803a2520b144d401400600f8028090000850030480686c000c00c04698 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 175003750 1250 175002500 175002517
    0x13121b020405161205070516170d020d05100b03180a020a1d0f0721290f030303060a03020d0f06090c051c050a02151c050403030e07030b06060d11 64
    0x840d981c40c0d400c041340c228209541013400a44c0501181c504840d02030014090b038075441c1e80058041a8003000c000002e019403058007128020183c40c1e81c0144524002900030301c1c81000c502d403500700841c2e00094a0f102c05000c40344120380d03503031459a41004071480c1301e0442e18045a07a12401035160700580e10300c0344072400b502041c44a4401504001c0f4141d031035100190581d00015040002c0c040381d542d0112160101e80c2143d60658501f06030002840c00410407174880c4100102003d041540c0100c0e03c00205100400480c0e890b03000030038000030140c503484156212507025150b55030800041c01e0520201141e02d010b8018407020300081e80343e00059412203042203a42c5413203c1818400741c500b12284249604000c800f0580841003991429611018500e01a2250120b0403619444031a13203021600100402c1a4441d1104802c0380b11801405007628200d001c2030502944003609200041e0030310460b90480070f800e810f81c440c8030600103a544140708094004d9104c82d41c424040e802c2100409441c4c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 175005000 1250 175003750 175003771
    0x40e01110f1801080709030615090e0f0607030b010804020d030903080c0d0f0f022e060f0305010c031b03020a020c100206041506151d090103050a0b13121b020405 71
    0x2450307020b003621440d065107015a418440725005005004c0e501180b14000e50b43d01500001d4543c50714403001c00e0074092070f881f1200d558148119119000400f2602440c40c0000c1402c45e80d8a0f2107a48050f800c1e1009000600d00040c1d030303080002d001d4504100f200c1070050190608608054072070301d03485842d07071100c0707a043e42c540e204454410300786900c00034070001e00045190841000650b040000d40703810850707903110420000711000c8182c0c10b009102e43e00c060415400200702060ba14502e2180020042c44290b502d9442c0c00a007104103402401400e10a8200c0da43d10702207542c4c1114240c0094100c480c0318000c600c034101d180405500c03170064404e407c031001e400034401c3c0e141c140781c000c4048009000e071403501814002c082000800508210b50703131800342d042c50961560011101e00310589000341071a03001e00d0800000007888408240001d01d0f6018048050803569140f115900d03032000701000034601d85815490700b01c0c552286011010200c031008124684001d06d800243c00e807201a1074034003c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 175006250 1250 175005000 175005007
    0x30607081006080103030f08090c0a0f14370f0b040e07020f0c0411070507060f021204030809040906140703061401020a02100f20010204151d040e01110f 67
    0x196040801d10300000d10030307031500314910343c1944c3e0002d001414854030401480b00318400b26400f44001e0200c0c2600c0300000c0c080f03085c26aaa03240c4c60441081d6441000d200c40c480f00701200030790800d4030b01c171090070040c44401c1c10344050229420480010021903d4141050800c0209035800c1800c5c0a100802500d16803d4440382000c0e40f004003100d015100405641c1b0041c0340c842c3e030480215007080700c41000c0f01c0c0010307000d141a15010707440c07046620040c418000c1d090b001c03800d6900000c40ea102c0034166400c881c10b182c59001c0c00f60092141d804080c0c0b100302d040c044917072203185c1900007a42030740c0b04823004900300c00c2c00702c000c41400d40240e0703650000c01c4e2100300c01d002c1d0300c004013142500f01009100800d92800306801207402e00b03002040c0d00b400c100517a900100300c24021907403107a8100c032456000c05000c0421140a000350014050103c04c02000444c2001c20b03440782002d00f00c0c0880410401503411084c000b0000240a510030001065498159201100d071000c030180007444420f485041d43c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 175007500 1250 175006250 175006261
    0x603021002010207021509010c0204050c0c0706020d0c0b070306030f06050103030807170f060d02060403050c010f05030702030a08041e0605010f090c09060311070f151d0c061803060708 81
    0x110295100100401c5a2041c0402d4000d661420780c401042e000e4802c00a65a84603403004031f540540710706002c0d412078248020b022194808d140200304c08803106040d640200e48a440403619040c4e0440c009000900800e948000306d010266003940010040c01c0020750305660761f80d03c6126000b001c03019501c0720754880041060507000351860b0f610802ea450030101c0720840001000c80d824029044c00310b0009404006a001c0d211604581c201c0ba030010040c40e21035a40746001c503a00c0203a00542e80c00101914401c041c0280503209481c0148096000b4505204100b0400c40d602c0200030002c1c0c2c0c1d200c1c015606940380280d552800700000e0b0003202c003c11158140023400c22142d5144e800303002180e140c060480303000c42e80150b0140c00e451080c540031841c045110004035060040e45001b8003404420030f4100e080220a14030b1300c013586000b10b000d003d482c948524690f030300003a0712841c0c0e040d9007140440c221180340c80b00050201980604032a0f885041701400b007450018100c0308000482c015806014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 175008750 1250 175007500 175007509
    0x12020a05100b0604171009050304150503040f290118180507030803130203010609020c0f061b090a0b040e09120a020c0904080d09080a11010e0316080408010906060302 73
    0x2000801c000921a00c0d0452011402601c62032051605010000010101100043c407140c2c030710070020381041c08110054113100c2c0c0c4940c001e126240c4440e8001c0c1b0046c600d540504103903031140350040d4450b0348a06164940c80c1240118a20881c4c0c6c2034220101415482c4003607103a07074041c018003240c003001c50340e02641c82070845008003840c621a00000c440c45000590000341602a03079070064040340c81c1c0c1c40f85a60401030b0101030400a41c19400e007540855114030b03a40c09007182c4184581145c1d0345103401403480c1e40fa00406d564144840404000c441d00f8000d01c000202100003000d084144100e5076040020000d40168010004000004042c170101c0345041210f02003070101c10300190710b0301e00d81c52400b0f0f586001281c1118010340045000509201c408130585131201c03a2440b081c012400c107490280d903a94001d00d596408260000006149403005104240700e248510f00110f00e003107014209046900691281126031800c10400421507210030300445030846c1c4141d0f00455038900354070402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 175010000 1250 175008750 175008763
    0x904060209010207062c06130603050609010b090a09050c070c0f0e060312030f040c120615080a0809040e071502030405150315041e02070308090c0103142212020a05 72
    0x1005600d91403c201c400f81282092412400c6c019050001031000c40414401e0141c80d0b40c04440682c102000190aa0950402031240c1e10440700810701d031783c8401c4000505d000748a038650f0000c408040521401c00703241e0109800007825581942460b000355200744940907150801454000550750412014080518264220100324040d03c40d940760507940700010701000701504031b8503104030049400c0c0f1942203010302c0036100c03110592110501600f8000007a0005000f1700c0244600b400c2c00051050002c02c4500c030003540406c1c51841c0c18400d2040002411100250b044503000c4d48bc0000344855255031801000440ca802558549180c86c00b0080085d0003d81d0b503251001d002c00030030044810340c0d0410707845404101c80009810116500c0ca640945403559040315440c0700181d10800e16400c00340c080d100e04034034400c442140165900440544d10004901d110120a03040401c0c98151229103e0041508075405860079920585500700a44140441c200140e045000d0607024001d080c040d9 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 175011250 1250 175010000 175010009
    0x18060501140d06050403170108010507110304060507081e04080a1502090a0e0403031b03020904060b070b04080309120f12090f0d1101021909060f021b060702010e0904060209010207 79
    0x55074040c0001402041128070284001018103540340001020075024595a12012000d5a8042099a12120300c54001d0600351402404200c8000d1540f0300b0500000484054405a0b981d480c2080f00342e95075900d07a40c001000314859036400c0b40c0356045429105010300000c2030041c004000800701030403d00c0c42101e04410000c0b030302d401002004030b02c0d00d400e103840f4110756804118541a54950404030000d00c07a05031801c04031040c9c01c50505c01e1a5054028241024040740e0403c001d5543da80a1411846002c5000708a50140c60004022801c500080d540c4460008191068064030f0082c022643d8045081102c8401c0c020460100100c00302c1032141c3c1c8031a8030001080300302e1400c00007030707035600ba0741e50200f00300201465200c2c0303070190a40513580c641a0001070105010131402000d4041101030044100007032810078000c0c0c0c0c4d1440021214807a58103c0c0510103140028401c0c00800c0e40103040583c140406804c5155440d114002c1641c8070314000c010050702c4003141c01c0024203040b200e502 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 175012500 1250 175011250 175011269
    0x2e02071101140c070506090111070611071d1501090b040902070618050703150b041401050102060f0c03070e0f06070b2406090415030503031f0f15080406060918060501 73
    0x2403602183d900041c01025140c00320340e41921600e19a00403030f011010081c00d0107460242442c0094240d4121078040c084002003000e4401c2c2540328100391680707011070001400044050400308070ac03600002c607210445c1701d042c9020400d29031614501c0c8215407180d8800d86000b540024031505006280c482d007803085280b904038a85081c050744419641e12514003025018081800003001c400c03071a684401b00d04403020300306000810f0b51003c04d1204000920460380980901c81c0081c96085120360000d100ba61024011411521461000c5541000d40d013401c41c1c0002150103003560325038030f0300d02420515118200c10344851034003030b05c01d6078100e0396050a41078688014940c07441d559603080030780303100c0482501c00040f050621942910b041910f0307071024042c0d0000005024000e2034131241036404a41c0402c042020b10741da1086902010414031038412012203050105d83c00c64031400f855034005010b56808200c1036120303001801141c20b03003182c45900250030382c04601004803602800c2d004001400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 175013750 1250 175012500 175012507
    0x12090c031b030c04052809020301110903120d02040b030108061005030607120902060f030f1e010b04051905030f010f050c03010b040509100e04031101050f092e0207110114 75
    0x80303983d4504030080c091091352502c0000d24a2124043e0700301c0403030303400c1034020529201448401d00810b0402c40a0b0b019508207a41e5402c1c245096080303401c04400600108800d903070100b003d540342c2e048088401c00c0640c003004005021a51440030714042c00504001e02030a041048460800213200e500180c00783d0010810841c0303003a004030b8080c03004016070002083c075034060b100051940c030400c1e01c2014402008010f00555412280d0040d01c50b0300a50003200b45010540d00640303050009102c0d142011034100014051030504902d400c0d506054022010f854a0f142e50010f828070014000340e1007160754603142e0081a8005014131038100a5008103285554107141d0b5001032032245008090041344402c010419001447c200387c0018082c0602e1034180c0d003014a0300404001501e104d070841503081002144002c400c4005444c052101e1034010f00e0484032200c1c03412805000c00d142c0740c9440c000713144d4004030840b1600050090701d2159a409800160034000074103039104580401c90005000e0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 175015000 1250 175013750 175013803
    0x60f0f080105010518060313140303042102100912090b0405060301030320030409020d050105040209030d0e0406050913030f09120b0c04030206070c15030c2312090c03 73
    0x390a0324150340080c81c10542d1074442d03558118203560301710000d6030007880c00420000c1992200301c440b00308500c20740403403507001c01421080e40d4a000640300236207010759560545260b10744810040901c507245006035000f41310f07110304a0b021170300c050409403940c8541d810315000d01c943c03007001c2501800800d074901d4101420880490b10b2800140400bc050000c1410180401e00ca2070119000c42c050103030449a955880c1c1040c0340c06900700d8003500480d942000004101ca00d0580291499510050014001c00300140e600300c1d400c45075810056001503844c40007250710348500b0031079031040c40420501d170090b4030303107243c001e240c000040d1110040044044082c002298280c181c100ba80e50804089840358a03005028400c030b2007541c1c00254817040001e001020468020f0a40c401c851440708807032a4804580000c1d400c6d03c0b08181c1d081d0000b6454124070b8030600b0b690623065603030780064210740c1c1020758039410100c020781c0a80d460b0325180d005009295903403604019090041a01d600b80d03480300f5400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 175016250 1250 175015000 175015007
    0x60901060305064c050a050f01030b0406080a080c0d08090604030507030e12010e121309150e0c0c0601120c0611010e010c031509060f03080f090901060801060f0f 71
    0x1400380c085600c0c03280190506040c81241c440c1905442041c0600310595811901c03024040640304c03044403031094500050302d0f02d0050807030380844201a00000d41481c4020045000700354010403194402c3c0d54180101c0d915100300300001d0141d12a0207600e948044030f0320514641113086c411141003010304002c02662007008100c17650429414100300b0307107410703036071500b82c8856141d1408580c0180c260b00f0302410340701e01504600b4600c009081607900658144020f1146849115140441c0203503984003005040c2103075101c00d80051020300002041ca0f01c40d60300c0c010055066030511070070880451020b245d11418400140185100c203000f007403012a0360f0b1a1241c41034580300e40414084c03841d558800601c030a400000141d0b01d400001c1003410703418070020300200a841d030410084000c3c21400710f0308030070610a40068403542c0040041c082e20b540d5600e60244d220010001901c1c0c41880341c040a51103c01446000e84815241d605441d810100024401e00c405026a0308114022490342411f640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 175017500 1250 175016250 175016263
    0x30111040b0304080421030f0e01091a0408010203012402010218120c030f030406020706080103050a1e0c0e04021e0108160507080c0f0c01051e1b0d090503060901060305 74
    0x740c070039140d260341c2c032410204405e00407540407150460f19416054042d20741c2d003151180661181e101e130001004981e00c11112800c20350500e40c0481c50840081c8614440d0442d0714100000c030803c680c1c034164072054540d003a40c100f80e00419a03002079002c00041c00c10300e09408100011644021030800c0001103901c2880710b41440558001c40b036140c5240c03200704090001428040c0e01804a81d582c0b145001c180e541c0c0d074030910644006000b0340b180410074500c84e000c024101c94101c401004031f1102e9880b030b012515423803455610301e1850585000b0010390800f00380001460b01d0100307603000345000c0c01400300000140c00003484002c540d1803215480c2c0c2e00701404603000820701071800d40704103d400054842e40b11701e60700a03155203404100c0b44900d20000034103100c42848541aa03014044001c019135a90107160814440710550f04900c440c414450405006504840c50151540d1820010200e05010310301481d440010200794040c445400c6c1000040d4205120500030081c4620310381700c0c43d80710301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 175018750 1250 175017500 175017509
    0x61106270105190605010c0c0b130f08070306060605040315090204110d0603121407110303040302040c080a050f1e04050c04050907030510020304080909060315011202090603011104 79
    0x154894006082100664015800d00500810690500c001d00c6012501d07608410100c00341051404640d039481400c901c4200c660003207014800508201102c100e0760032400e40c01c089100c8103200080c0b5001044aa000281b0303032100505205070950501d0740680e00385410840a1100c10401000014115071402c640150a8100011000320364070016000c2c1c03c0943e102d6014a5001ca030745402c101d8203030b001800700c900c076104000207400700b2103064600603081300301c0d52543c090502c001004a00080742800a044009082e80d140a45a80c002401c4070f0814070b43e1000030f2a06c40400080724030300e00c15280c11400100102020345054192440030469055403c00414001804101004420000c45018500081003400b041c41c1500700c0e141d0758092480143d41d944600d0000304070754211031007140e0040d030b004007851b494204000c0c04d209444a0182035a80c05110b80d160700c0902e0110407030000e003e070611410000c0041030078010000ca6030070142000d44607924051402c030804080404550898 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 175020000 1250 175018750 175018771
    0x1a03010909032102120f130201080a0902060403030f08090f0705040e01061805041514060409020609100315050402120703091406010e0601080703090203060f090a0c1509061106 77
    0x6040c901143c9501d0190340d41420000c0440c01045120b2094016101d202c00d074005034519641e65108100c074015095a6a40c154800302100c2c2d030165100e103a800e9440400041c010411f4211580840c4182d0300c00c4d8419800105402210082d0580c084403140d04503490300c0040800090560701c40340ca0760000e20685103d07956075551489500401e410000003000c1d20014041c0c070314240c4810402510003194222a881d0000c80352152416661150680b1410443c10480803a0784140a010080c603002c9000c0e64007200502c0310f98015500d10b204942c03072a51580d00421807095078007a06803280768940210744268018000342010700c00f8501815401100b6190104a4210505200c81d07149001030b20707082075000c0c2e80008521186042402c40c0200020ba90720035169680300e03411000c854903180025032580004012500103200b012074950840c1946013178038140380450361219031403c203940c00740304c98031001090703110000e4201216000810041c149003458142881070261520001032020101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 175021250 1250 175020000 175020011
    0xb011806050a02010e06040f03030b0613150c0f060b1e094209010506030c1e0d0c03051501110d0507060b040519060503070b0406050c0c0a0b070b011a030109 69
    0x1076600c01d400c00d403490f845e41c206580050500c2d0800c8683d09000c03401c1940800d082505510035030400c4d804641d9448200e00107221260301b4080c0c4001d4841840c801401044542c00e9000c021440144924010902c520b80001e400e0014105204038008e034025140c0d400030f806249525191104500e0580c016181400d2171685012200a402c42c1e0b001e001018142e4950070741c0c0c00c54803041c2c0345071380d140101088418402980e40daa0070080a8030080310031765000c170414454071b0955801550000c00c03007160700d641c00b4240341a400c4410202e43c168880400060345440c10300188280200459042c55006c1c41e0800520300210101960303034400f004103034208000043d00005101c0c41d9440fa800482c40103009004078249050b061800703105100ca020380c0140b40c000001000c0c6400202502200c00e182e00c1d05084c24074000c410748181c1c01014160180d0301a01c6e0340c020703990b40c80199000c0681084038440d501c0d0700041c18824481e4105070032070050155039940303d083c100610000d8a04489440001095 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 175022500 1250 175021250 175021267
    0x30717100f060809012004030f0f020603090307032606010807051201060905090601230f040504050901060e13030c0809012f0f010524031f0f0b01180605 67
    0x384040c0380d1140300000d20040380450181c0d40108014055101400280800c08807051685c07442c00c1c1c500d0700205042801c20041002480318034070312180c240942d1411031064032070b0300407641a5000b140c20519540000604c1c108160b0468112444001c1301640d580c1031340f035400e42a154800c0d015002c5814003105200160140748200101d941070503410041c50010f580d1150060600d0000340100c922400350f0303000103131248d480382003401c07400b40c1d03810b000425111740ca101d5020940d22981c07030400c8401f810000404c00c0c2d11240185800780030014000580c051418100030703031024001c3c265249003042040004042648503840007512604031005c2c0e503031510381900584401d01820701e410b1041402c00c5452141604289482a00315545415503102031143c1c04141c2c01c1b200b04a40b101290403104100030100d241c40c01c03082c08224809812a40310a5080c103010252035941503442c01196290311a00d6030b01d01c054050b40c00c11140c01c0c00c00a01c040d09030030003081151b070b25000380c0b01001404501a034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 175023750 1250 175022500 175022521
    0xe040b0a051306090503030103020a0803070b07081801090503030604051803040b0306040b0d0f021003110d0b04090c03050c1e0f0904020307050a0303020f06010e07020304060c0206130603150803030717 88
    0x4542030f4000710030000f14460745401d580300d0b0006d1000380c0c03240380341d81000606502c002c01128030855004001102507030311118181e6590001800900300c1c0790851034060b012000912598013200c0c060001507481385031810070841a503800605542c01044d07541c101101111000098406482010007041c4d100d41d2030b039010a008007031180d4041c0d80041d8004102041c402d110701c2c4605094003c0c0d5401e00c103407030310301c800342d065818116280300d04a0040094a0341e20465030f10060b51050300620125a054554a0303912604200341c100b9203980d0046800c03034040d03182600b0003e20300c2222481000550f00c58100042e50f8024060007540101030080020b4119981031213004050b01008180c6810140c0b80d040003580d41c0340340030000045100d0344001007004045655128414001d82e030055103031600f812022266180c88010403a0081e0301030148501e4948007c484070302400701235a00142c15902c034004154202015400007240b03800400c144280c083e40110100c1500046a02406031034480d00485e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 175025000 1250 175023750 175023781
    0x6030915020304060b03010f0b130908070501050c300a020a0c050318151e0703050408060109090302100b060a1404090606020303041a01150f030e06070f090e040b0a05 73
    0xc03592520000070441000300320750100694134019030007003101c100700c00c80b44000c42e84440491036021101904105401d0429006002d101d4466100c103424038901d83e80345403d42d20161140903d042c0045100d10010000c2d0800e1810101c058964040103103241402d00c051110240c0340e8594140c000901c0d0f0501401801014a02c55004007100d0344e03040c040d41c0305000c1c0c804800355140b04121a0b4550780030340030540241c8001c140191028509242900740409217a803142c5412030901000f03110004044800b0f20100f0700908400c0f801240310f50041c50000e052031901e080883c10f01c0c0c40c1c4401c880c1c2c50f8550000741c484100907030600c0c0005007081c040f43c55003800780740c0c4080002414120041003055000c000786000b244a071007030032582d0344414003000c1089400d003c2c990b2040604240003607220701c2480703485803681c0d941c1030010f082954407460508041c4221030000c046000f161200c20394540c00f00d40d1500800d4802c0804286040c0b03560381d02405ea80142415403002d445c0d1010605512100205 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 175026250 1250 175025000 175025033
    0x92524021609060603140405031206010c0f050a0210030e06060f040b03060c040914041106030c07021f0f021518010e03071b14030a031805150301090608010b010207060309 75
    0x100e80389070359003818030301402807400744d500020304005142c10500651100c06004560180266003072410412030340103141401000c45041121280302e002c080f0b0340c05450240000e0040c03010300441102401404070002005144808061400c203190752241000b1a14a03080361b41114042c01e903040c0c040c0058050600031041640c54002e0307006110310044420000e00460316540300601070f80040300015099442d048801405c4908581c01c0d0700d4091030414021588008406265814212a9004291100380c44005410754115164140f18207541050b00c2c0c800208a9200504400184040c1040003c0014010011a843ca4107600d003a55800f900072048400b8100c040b26150002820301d011440f05413079201e1007a070f0090102140c2103002207a10b20300c490010b00104492216a42c007191038826000c10100c15000a02c0080b4103a514240000c1900462528607030306d9504040780c0270304403201644000312580c034000c074400d007598012408404031000d608002030800004d0520813a00900f01c40f0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 175027500 1250 175026250 175026283
    0xc1e0a021012020f030615070210050a03020d1e0509030a200a30020705150c010f0204120b0105030c0a0302090c0d09030c0b130305030c07051509252402 67
    0x3884140c0d019880045c503c98130045034030050318a80b0114081c801c1c403a968021f9042801644a0211a4001c038003c2401058628006140403030200b400e07802c40d468001c08400c99038010140e003034074a0346402a241c02c405010301071882c01c2d08846015001403946401c000464a04051100e0100c00910182040541040c003240384203000f0843c00f900c0100c01a0446c000700c00c1d00a03450156840012000284c1d000600f181c4010300345400441d015070008142c912040d07499640145d0441c89500150004280305581001c51914a11340b558003200c0507000180039901c048509011682c031150302004072901036130785286540b241c15a024403445205605028141004a446c0415600100307616016024038207060013034840c0c00c41d07403014846000b40030700042e40600c0800d159a02c1140180600385c03250044603901200090003030060342048a00c5040381d008110710070031a0051100e0404101ea092402c142558100300e41002600b0600c148100e80d1045c5040b03044101e4000c01c00045c10700407440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 175028750 1250 175027500 175027507
    0x5030a02070f090e0714060903150106030e06040506010e1906031203110307090b0918010f081516050d1107060c02120703091206021c020c1e0a02101202 67
    0x120080e40d54069072099402c030500751080001e41d4080d621452031030f54030300c0c006044450710f0400c0f811481c540090300c1c194400810843c0581c142c1e41084100d06a19103c0000c044075071410a025046031b901844c404c0c45508801c0030080010000320388503054844540e20044561514900c1c010824401088040c0c0c0518000d004014090894803208001311070307a6003440400501d08007000f403400305071000c10201d00400400d00c01550341c24040e01407050081e10148403070054000c283d802181c00c7e032005a0001d209007060212200a000e41820204032000d01c3c4a1414602c0f4002254800000032800b00180880c000149011507000203030f00300409001c0300e40714a81c03410900010f025540a01001d031103406001516402d0080c00e5420441c0c0507220903020324500490228158100b2500315010340d401c0100c00e00c20070880001c120144242100161290092042a450104800001c0d5581e042e8400780010040340010039020095040d80c1d03c00b00703903042980c00d450b100d0994004010403800407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 175030000 1250 175028750 175028767
    0x30c0c0e06040b04180f080f0d020318010603200d060e010506030f06190f0e03030106090f0e0415021e0a020309010207050a0b0703050c1f0506010e01110601050d02010c0503 76
    0x1030a10314010301d002c40302000102004000c0004882a0b0f80c161012209100f08142c0400d00c0200b01d0501c150180c40b9482c0782800d0340b44905a9540504141c480301130740402031099042850b0500b4121440f881d0080000d28210740307403c10800740c0300424110040500c4c6c880519500c50700046a1520361140d4140901409848454040d1074100c945a02910030711526100c2d00200040450046108401c03c40c1005050740d2a0406865100408410651500580d1810850030002140249502c0d80c44814050500c003049071041d005521100c00a1110b40901000c9030050014030a02d540704400180d0712806c4842540100c11320600c0791440b04d81c0402c45503603454000c4001c10f08014264252501161a541044a603242a0040144084d070520140d800207010354010711318201007030122010403046c00005040401540e00801c52a0780f1801030015a5803c03176034040407030809003404008110503800311542c80314140b01d018030030842450310f81c0559000c0c08091041c2038004d01a0780c3c0d107403100d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 175031250 1250 175030000 175030019
    0x409060b030f0f2406220503120a050301180e1e0106060305190504030c0b0903120f070e130902151206011701060315080f1501081203060607030c0c 65
    0x44070251110080c08002680d07041c1d4a11629124150515082c00c2c0910070340d18a404c142c50381c2030510b4120800b0000d42d03401c4c401200b142640c81003524981a64182080141800c0401001c920801040c6c18000380643c142c01006032419982d06059900d10500901e200c0c0303001d096410100300301d6004464074448660301c502188100083c0e410028031010740c1d101401c4040310011514810030070641d03010808480c40310713004aa0068001d10380080400c003a521420030043c0b05823031955840d40002001d1a141034030102e090340c0981c07002c40f42481ca203003079030700039140102c15410503200f00302011082c148506030307601840c02241c004d07000d01d0102d12003804529241d0301400715040c5500400f400240150301c21a0f08240b4a45800d01079a15a4604401500a0203005000c6140c084081d02c011825041c00c010741d81603004040020020b07480001d20580d84500183c01010080c4c214000b210300d80f0000004980c0c05c0141034480560f20181401e0071074200b000d40300000c0040f110303184006000c220 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 175032500 1250 175031250 175031257
    0x6090212011a040317070c05090f0a0501050d0206070b07121118030106180903050910031b1b080d020708070c0303020106060c0b0403260a1535030409060b 68
    0x301c01101c20b03108001d00090945401688002810020908482c41c4658050800740c01c03124031444000380420f031200c2c000354002e20110b41142c1c00307508580c20070031980070034001c4a004003420381d0f00a01000041e00400c0c902e200b801400740c140300c100070115000c0b134441c0c4500c1c3c49140c4110010001d2005c0702c16046103e030b0043d202c021402d40e0501d43d00400d45018800d500450b0811141c00c18090181c150078070250072003500c103400f070141c184058103c03034907403c06040c8000052b590001d1203a4880d070319240c2d0300780d000c2d40100801840c915a2a81c1d0311421061080d1aa00301e850103446881e5107503400302901c94440018070002011580c041002201d607684000e0302d1085e0024000c181e203424040312015640712001e0300b40d40c0d40130086030100740652a0042e03103400d24900e124120001404802002e03074191110b1504580e608442c019080a0744041400750582c440d509100680d03034010b04119481c00c1401580e4551840051454008200304035402052180010f1204550394040481c4070b80 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 175033750 1250 175032500 175032509
    0xf0601090f140a0f050a1a04080d0c020315090c010302070f0c060f08010b0f040512010920010f08060f1909050c03070f0f02120d020d05010e04061d06040b06040609021201 75
    0x1a042100403c2c42840311404d5000d480d4090446044c03140f924046000c0724031112001c18040340100000b00345d280f820700c02418821883e07215031000f40c02030310601d07243c8140d0040f8100c0c084041d07000d0240208000c01c81c01c24442c000d00c0d015840d01400c2c01e20030b81c260b075502c0c40104103900e02000058565041200b9a503020f41d01e4407110070b40c1c0c1c0d0715014000a403148540c58200000b040000303010601d02440111480b8111100001d1b101031141e6a144100004e100c030305070b600c407040f5581c142c6503a220b13801541e140c1c080e00c0d10f007456042800100d8403215040005512545d9800803841029182d00d8802c00142843d110a00c080d06119203140c40d07079402600d260002074401814120f20600442c10014480300c26402401000b1004504910035007108044050190f000c0004030032220304c502542e400303404440101403031401d292400e03500300c0d00c048000c035070103080d01c0d04a80b50701600484c01c02d521680041c00d00c1c8140d81c031940014020241c0d500034141c0d140c03000c541c291003111145420342c1a038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 175035000 1250 175033750 175033759
    0x150621030d090b10080d0c060f0c020114100e060f03030f030f070e06030103080a110c0d1b0501170f04030c02130c0f0311220306020403080721080f0601090f14 70
    0x1d03140c0c00351140e403110f118005d060480d400f40c2500c1c00c0d00342c0300340d41d15000e850182c10b000a441c5034901c0c00905a810f940307150f9005070b45901a45d085664600b518981142140001c0303070400e3719201c2c554201ca10300030405403048810340440320003501d00384102d80303504014414103a40c0785405a41410704003001d503440000125007600c9440035092400460341625003001545060051484045400306500c01c1c5030440c40c0a0000106429160111418800c510400032070000030131491210004441540c884d50411400160380380610190f42c0f15103400403d01c2c41115001d90712814107440052034200025000114402c0b00740038012240d22a000480d110b0362000d4524080705400c409603080b180e04e40e4103206d0f0410450b21030f084d0b400d50002403280361031101001256a5100c1108981080e4001d584c0e82800141e04810092030f02d5005924540c050403041078409150402441a00c2c02003074011008204000300c1d050340e00815405008101d0034200d5081d06440d5030503060b1010501007040c1c0035 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 175036250 1250 175035000 175035023
    0x190803010f06030b0904060207050a1509060b040506010f0c170f180f061909051203040e07020a0c050904242004150e0105040314010902010908150621030d09 69
    0xb52080c090110180701c0101031640e240c455840b02002988600c00441c0d162198405540c00a84a0084185000c03805000007031b01403043d0500e07606032001110260f100b5032400d010404540c1e04214042c5041840d480c2c1100b080c003007454a00d40406041c0003800ca159408507424bd042221440100840c440ce2146100200600020b11800380c016002e51a0b200b0300038400600c00038040e044900b1402c0c0c080c6400000d29503130340085078548001100c0300300d82d81c00001e42445241c0618030519044506413008020800c09602c0e20321800c4900d000d0b523482601d624012030b003070044200050307180218580300d100c4080042c401c540c00806503081d0340911002441003200b034244020003658200c0314170401c0272810b4180d00104903041c003400c0c00340340e052040500010003c0349403c50404110f14050000080c01005170001400340d2110344d21090302d551110504113600c2c00300100c21508010142e47c45c0055040c3c0d0910b41c00e0340303604084c098200d440b000c1280031182860350812503440c1d003d0042c081c0f0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 175037500 1250 175036250 175036259
    0x210f2101090c111b0405060301020403060906090b01150909020307050c030c160518010302040c020f0f010b01120603030215090f0a080d050112020913020a1203080907170c01050c190803010f 83
    0x100c1e0003c035130103145401400801032242e4202a0807040c0e204200800042c5400d4417996403600311002c2442c26221255a842013104015400e008180035241d003450394102550b1511005181103658055071019503000b0010509107800b582c1600e42903401e00050740c0d101c4001c079410640e1840311403042000e01d101c0580c0010141000c05100a20a900d400c0180c4680e0840c2c00307220203050201c8094045100d58144c40c1a010018403074944168000b100104d01e40c0403100004000990312400b851b00e1078540441040026000220000100c4503031b02404110b0780e81d201c9913070621540d00c42082160003044401410815040000c02035018071800030049640c840d10f094200000218000350001000804100e00186116401400303600c002c1200907511384410076000c0b03140380c56204802080c011000d0003102c0d9800d00111001c4c0084100200d8424220180030345d54100441c1c03500d0502c40d0018807060a02824011f00000000f10040070f6011152803070700303102d141d009200303003c81c0c9020800c0115 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 175038750 1250 175037500 175037503
    0x80703030f0f0b010509120307020d0c0303080606310509010b0c160302030601050904141501032907050c03040b0a1e0206090705060903190302010e210f2101090c11 72
    0x891940060f985c06050040c400240051300101c0c400a144501c000e00c96040144e0362031260030b2680b8411114038403e14514a009000440d02500d00f52007104180130203c107041d80c51b214001692840b1149030140c854082800440d0007403504541d410014000000c141a0ba0036001000c54030707540d808982081c0c021150030440a2503500009516030401c3d001000203140a107242a003190055101000038030200c0d4119141c207030a0142160700448920041090124210391142c08115130400d42485800300d07554107244050003854603060103c0803d420344060403c0003520040c001403002c0e070b5a41c00000c0c0000c1c0001c1c1c0e0344528040c01609000f405490580b001c9407041c05002014014101c00341070000308805600101507060f051b200e411640b2050555015a000c043e90080d00009554404451114200b4900c1036050780445a01442d00900c06440d400321000001090700b500d489459443c108540800c052281c20458088030001040c007807000d0b40200d140c18200c0e181d040189905280c2c56 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 175040000 1250 175038750 175038761
    0x6160507080f0a120f1803030f03060902090f010815040504060603140f0304120204090503030f0f0a060609180b10020d08010f050904060c050d0c1e020f030703110703080703030f0f 79
    0x130038518044241440e40d0340184000b0743c03284003c0c1403140c030300307a085400c4042c007081c2941b041d40060b40e032090b5546070a8162241001401c83d0078020f62400758014041450b10020052050400c00c0000004000000341c1c2c1a200d407c0900810611017402c00d4205207003d4002800190b908607000351100c40351400026100303a101e90540091414280f1300340c442d07030320001401016a007041e00e5200610015a00340010f5202d885807403c040c1e0079082011124a2402d4024002c0c000c4a180110901c16190040c00c4041201d110998101419429040c05c002034601c40c00501d40200d400061000030301e0300410b8011a06105603103001960ba616042601a01c0980c070131241c21003d200c0101d80818040d810403017042e01c01d1306005241512050542d011500d80450b41d400285000001301d2640070b1542c0c1100000c44188010000f10980d810301584a114100c002001d200c9800d07600100c00c00207101800085800140441c1c60b8040d5050140c06840c0d20714032052114035007880504a03030a644280d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 175041250 1250 175040000 175040003
    0x80d05030403080f040f060914010c020d051812030c24040c05011b0b0c07021c02060f1606020715050708042f03070b07021002030406080f040206160507080f0a 70
    0x43d050540c0b2035038441c20104a000e03100390b6010401005071404a101401003208991064413a6050601454020b1382100c403103059640c1190441c0303440301030150307000090754041030f408042c8072600c0c3c19640009402480a00d00c002c5540001f10b9081e05c1c2a201241c4c00c6182004150261701800c1c680c071450b10340400c11a40280843c2941d10248425403140f0081400900c41c0e04501300202c0c400e0321100c001101c2100c030541c842e080011107d086080600610034138031000074071021030041c00e5000400c1e034060a010024409408070340c0219010080c10080303015034001008541c4d13000c403810b1081140b100340301c03c0d0142500300404038000394401d01c411403003950811860240c810600b0a01450484e5040c1340711180c13070040c11800e2441d03500303008000c001c01c5941c0c01c030340e038a000303078414003800f2182c802c0d601c41550418001007080a80003c405c950029147c40256152760301d502c002507446c0030741e8130002038120400082104100001454000342c4404404442529660300307001560390190300f80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 175042500 1250 175041250 175041257
    0x90103060e01150e0907050d05060609060a090c0503010303090e06010f0315170d020d020706090b0904020d050a0b030f0106050f0603060f120607030b01260907050a0305030301080d05030403 83
    0x1040458500e900107011070011600101d51111000403007001e50801d6002100007080d54000e00807114002c01c0000014401510341d4000c881041d01c6080e2a0300c0024001d9000c0c29107240050100d07507805669002600214504126015202e007008280e50000d01085001c1140c0090104100b100303005820712818050755000c20320142084120040c040042004c859443c20846c04216400380400f241045040030005000d000c00a500084c43c00c07030003030b4000055401c070701c001b408061b83c03090b10f2009039681502500c3d682d034100404a0024400d843c00c1e034410724500018408006000c1d00100d14a0f00101e084464440c04018154201c0e41c6c1880740542c803814224541600717040020256078000c00080003045180396035800310b20b00302c03c80b007821041508220200401950140300e92800b4580a2030b00034103030303100040c8801070741c00320301035501004614030002500d03004200943c0b006442d019202030f1481d40d4030702e0400d95036082802b85a000b400303000040f43e606032149060300d104503015036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 175043750 1250 175042500 175042519
    0x3070806120c0415050607050c040f0c09060c05070e010803070302071401020d030b030a060e0a0308090c06041221030204030c050d0c031704030501110405101418030a020d030c1b05 79
    0x3082000a048000884d200d8500d140d82c0000c07282d50b480054120103006001412107151000c1c01c00c0110380ca5000c05140d071920380f046c05907185601a043c1800d449076170803c0301820005d420054a042c560b0f42c442541001a140080340b046c0010015001e950320079000c0303a1403543ca589101c0040110b20140d00d005900080d504c85c0b0242c480d0b004a0804c030000380903150000c6a540b102c9060f03604221088405601a081c130404040d4441100c50340540440c1c080d0025641400004002d0301c602e1250240d0600841c0c1c0c0c44042c4075000c966003549800c0009440540d40c0e6400c0094043d400501c4241d03041040d440001440c1c0c2000c00050b0032031507100083c46480c07030030b5a491103988940710004400d900030174400440054802d106541d00040588291515035140c6001c0018500003521140d04020030032010308c204840060503152450140c000c007103907000d541001719240c11102000650b00070860804071003410703000392502071068001c40c03010040c0342c10044032000080746445400d800801d90b1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 175045000 1250 175043750 175043773
    0x50c13090201020c0a0b1818090606090a020702010210050402060d050708060307090b0901170f070f050a090b01120509120d0603170f1e0906070c090513050a02120c0d0303020307080612 81
    0x11fa004070b0b1183c0000340007805542c3e400c004080c103820101c0e000382107613000f0420310a00f841d04410302c5030300040c1c4803000d6291002c1035000035190002800c0d0725007100d4480000c00d0841d82c0d00c106540d030660030940100000d02d40344500900d081001d499140c060b002e80200411f10001c28064010000707009132031408140d107028030449450f44040700c41085070103000c08510b42c000003444410003c2c11101d40b4002c1c4a4100010030034162071590000080c50300c0d08410400c980d0b008800f4030310310249400c00003020307581c5c202240e04180c04e00c0c6c0c9442e052940041c41580c0c1e102140e0240c0c0650707002d940341c0068041c643c40024841e00c2842400b010040c1c00780305017800d081c460304840e0703115010b0044c1c1908040b1581d000c01c0c1203402c40035003214031000307440c41030011078418410b46074010384903000351b04209181c0c1c40701912110340d403001034054811081401e0144500300604013401d500030f0100c40095403d400c0050080d0070030343e250030005503076a010403018a05040300d82940c1e01550040d02000003107 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 175046250 1250 175045000 175045027
    0x5030705060310031202030a090f05030a0f050111070b0a0e0a0302031e0409020729010617090316030f030506060301030c060f0210020a170606070c0e04050c13090201020c0a0b 77
    0x400150080c0161400413000501541e2600c424844a400864840c1e15040c009015100b00da040751210421500b0104400d079070000c0c811407080d4105114442c99041c60070001c0c050810002d908200e0003000072050200410030119511490030ba402c200600c50700c96002545070700c400400940140d0041c010b40e4013200d03640e0114140c40c1e444000c014940340d504d03d8083e0590b00f00c460b040d0f07242481e03603000010b803085043c0c1c4d0000b54000c01149090641c10803c2c054521003100b44e1b5501d41d01c5900f0700082e03d44c04104111050342818144a22026107140360040569a20201941c002818800450504c0c1415000e482c10b03654001e4a4000550921404803a0403882011550440c4207000e1030049100c668802402c1019076030781c89001c481c40c250700d10b4410900c081c000900401041020784082074844c0d1340402034070351056425105885500b861890203484241055015014030f94180081211358800f1541500c00e07001c2d41d03c0e02c00708004002d05a501446900d041d40300421112135a10f48 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 175047500 1250 175046250 175046257
    0x102030f0307180b0c0d0f02030d0902130f0b0a0b120a0f090c0602030315030a121b08030114010807020a030c120212030c0a0e120703030f050705060703090611040503070506 76
    0x4162501d5040d0070f03000c2401d000d600d00681e1004c048210b00182c22468200140700707040d800560340c01c2c100c45041c180e0000a5403403184401c0104c010382d403440a50f0465489802480070920052020300c03d404046c419000284481303000648030300740d420790000c0c0c1000d8407429550225016145903900c0e07035a0300300f010b000d0310400d40030340c1401c0d03030703c5180500081100300110061b1000e64029a00c80c82c26010450652003210003083c4030b80d0150012000051072203901c2001480c05281c802c0c0300304185010307003101c0c02e804e140007840c081012001044a0301c3c248a074945030b8030709a03520000b544651000f66103919030300002400060030244a480401c01d82c1c2c110700192107051048641884c10000710a000c6c1d00161041c0700d60038000150071a40300d034010924010005c0490300c40602c00c107854049030351503507030380b2000b42400540081010b03602d0143e402d840b08039411206807409803815840c010003c24401c0380464000740b418107074401007241882601c040c3d0348098020f202c12400c100400c00e8541 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 175048750 1250 175047500 175047511
    0x201050d0207080703080708011211060a18240504030b04140c04020d06080c0a05091602030d110903060a0501120201140f070506090601290306011101051509150102030f03 75
    0x81e020491240010720030f030028100c940c0a642d6000890a00341001031082d10181d00060b0312003401c18100700442e1b9a4070b02e00c1d050441c11100141d983c20084019100740743c07000708420310b50f006000c00081103194600c80c0c09106a907460003298104158005851601541c000030f0000113240000500042244001800182014085500c4e9546280005050380c0c0f040c3e01c07581003191180004c1000b10030070000d5101d115011036017011035a007031101081048800038481030080c142d0701007c0800074000d00840b000000260740c24041d6001101c0300f4a22540400b410340d011344103610000d44e842c0858071503203060303501019508880308950b40044a1003821450512007181082110050f101100c5004180561042c1c014210b1450201222414400141c0c0080c51301b88400c01940700c2101c90314035544003c10000105900c80c1c6450740129402e0300741482000702c80d860101480b00303080300c1d988280c403099011540400103956841c1100050003000360fa59026034402d109408192400d00041c5a007c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 175050000 1250 175048750 175048777
    0x307060c1b15110703060510170105010806070f030e0709231902090307050a150206090a030e012105040c0f050f130b01050d060608012303060402010e0d1a1021020105 73
    0x445e00da844600c110340341900d00101e6688480010041a62480b4090141106060082010b98544960540c681000400c0442003100024003403c44500035400500d03a041148102d518080d04c4210450080000407032404160354240b580002d1241c0c2c1c0d07240b451151400f007403000382109071400020069007000d0460b0307515008848010401d91555001e140007000505200150303003d820070080d0034284040d0000d109900a10000e801194000b5990540c0b05800e10344042658580b01c0f22980e010040800015401d00f40400e1106020801107404151103860214511090b951010800151411740c4160380004007244581c41c660728644c000c6e0740300703001818105e00d030503070720740040080710002e400950114481c2d00042c0450448400b506220301c201ca45190351b07900d84200003d640302002400241040000c3d0008803132a11001d40000300c10303500c8204000380d04800084490b00040440740c59800c52003201d000203011140501154112070300110301d0849211940044030340341c0c40a150341151 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 175051250 1250 175050000 175050013
    0x110d0b3d0e100504360803010b0d060e0405010509060606040315050606130602030406090504060503060a050405030c07062006010303080a180f0f030305010503010204140105070f020307060c1b1511 86
    0x9a40340d034043c400d02000003060760405400c03100340100071501e545d124621071000c8030004c440000c20070380440381034031440c06a464840a06003c8440038000c0707604124900d2003500244000c00505400050040e1061720236540a03039211401d110075030003140f0001d00305d031550408803240c56203540c1c061a04448047c2200b45000d50341040c0e1000d441c007a5000300c00503030000804000c1a40d00c4800c51014000455041c0310f210b1030500040e65030f5078050000300500b44d40c0e0022504010041003124182d8000c08103030341c81540d40342405004001e6203422240d030702e81910b03058010b6140108184c1e060325410f84620b840b988075440108000c00c1039034580a000400c0401c01008601c0124280c20301d40c2c450040440b8000036890b0041c142d520691000e070082c1c0c0140414450480c000415100d003501c2071130044d8690711907080101c20803100c01c402035014000c5403808510b01e0f901c102c0c0c4a02e100e000300302d902c0c0c05c082d4100084070030b006144520610113019020044015120781103205001c0111800c8444 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 175052500 1250 175051250 175051259
    0x21905010b0a03030206180303060d03081018091a070507140703060f020c0c0a060f0302090a090207060b031c0f21060e0603070806010506030103110d0b3d0e10 70
    0x1020b44642e0825000360b84038004014001c40071151040b06015180095811403c00c030010900c0303100a108002d092001d1840010440c214a6210000400340d9420000c1da4581f010710f684010440306000b5948803024440036036811415019190060310150356580c80d0150f2a03d1301240000b036480000c105005004000000c145a03015104191004000041e0b8070003861440fa4a00915040614010180c00800b003103042c0d00803a40f0b0548510b1801d015994021680004815106c03a810540e1a144042a51401c0c04507562107085402420340807500b0b401c0b0078103250f90310340070040c1000000031104000d0b4a41e0f980300e450078104024070314006034440c400040903801903828540182c81d00d10858030030002c262604000143c02040d001015000715410800455540e110500002c0c2001d07020450082d202c0d1190020242d0303654100b800c5908508010001d180c0800420030070303110803001c582043c005643e1170108024000e10b8110340c955507500d464030382d1145c21001025000032150403c80000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 175053750 1250 175052500 175052509
    0x61e17070b28080907061b0609050606090c07050613030c0b04030f020606060f030115020c100306031104020c0c01080901200403020a170d030e010f180506070203030601021905010b 79
    0x10a4840d60b40e5100003041d0b0088101c62070290042203000c004070301e01884082e007808500715096810610704503040241400350103480844205008001c14a080c11240034800085000d40c00398600302c0300f002254507201c00034203a5000c0c0420241294102c03030046500c03192400404400fa611904040c00300d00701903110460403000c2210160086031543c1405042c2c01d07030502400760f0002d42120322900f0100181d070911400d000500900f06c154420400000b4424020440304012280007048411407040030302000380900303c175100454185e40c94407070080a0f483c103802a44d1100d000c0d003004090b00500040110740c040741c0648030903042c0d540c1d10a6086074000084c050a005060740c8026546c40d442d40c03051200c07001c0c1a0f0302005500ca0381084451202c8c2e000710700ba421003c040d140100e000391480b240c4138010640c0200641c2b203140b50005040c4150b00e4040c80070034071405201035600076030f50031078181c1c0c480c07100725a0180160030400d1130600540455114500d102c1c0520000540110420040ba = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 175055000 1250 175053750 175053757
    0x150b0403050c09070809030702011b0209071e050a05190e130b0f0d030c020d0c08060a05040312150519091a0306090c10030203070516080a03061e17070b 67
    0x58910b074000c11801122410300000c81d540103600742c600500c5501d04603018a0701c03802200c60082c10020441c1605065a0381d40501070000c540023804000305003410100070380f074020301540c00d5090081030440d0324801030080f01500e60864064803154030b04500700b14984103c2407015180014441c40d1005111070361200341082c000000a00d400041204140003040074242003807100ba403240031241d09940000c2e9010f41c2c44080f00ea41030b01c51000c501c10614102800000d10313000080d2501c1980304000c0c006000d80c105600441c0280c85010300c1048005810003640e98002c1180070580200744200920b0400360f0100d16004921300011a1590f1591594400d03140504201e042100d04020345001ca0300d4248030164202198400524038149130700c0100c0c411080403500e540900d5400710014002c14003071422602c200c91152061030180d01c4902d0944500c3d08400d600000191a10307a000ca206030f0200140055822000001000d59140c4181d1003000c2d9080400e43c031050185950000d900704c1484080d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 175056250 1250 175055000 175055003
    0xf01061401020111090d06090515090d09050301090b1605040f08010525080c030c07050613030f031e02130f030f06050604090210030b03010617061603150603150b0403 73
    0x40c60140000002800d40b40a021425980708080060141e02c0e6580c121031044603074080e13030200384003440c0d0420600340101800400c4640011404101e0404e0020075014001581a203862540c203485001f07060880c2d1008200810120034180400d0f10301c0d08003050400c0808441ca01b8502e026180d01241a00c103d06a11032911a0344070f50900140d008001d0007400742c07807045c083ca0755644858800017811444064070141d150703840080440c88801981c405c8880d610341140440381d15042441d4078003c4500700703440c113a0018135810035040ca0684079001e41c0960b00e0015084944410300d40c60184002d6004490074110f40c2c070b10000000741001ca8602c958010360058a0800440c00c950030301d4015580c1c020001c1d845185030480c01d100507600c0650f061a03012443ca000142d0001c140b012034014411358000e03090740c50704211181010300c00094028414000c20001114400000354240c0c2a60081c14400500303c0b1107210130300286100b03920140e04005130804605600b030381d0b0340c040402c5901a800 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 175057500 1250 175056250 175056269
    0x271707090b0411030118150803120709051e0607050105070c4803150e0c040b09070804031704140616080c0a050c01020a05040e070906091401020f0106 66
    0x1010040403031244280011000161001e0081d103075880e4201c182c511050003100f030440013103c120b403800c860030340c0310034801900300328540685a202c0a1003075998004803682c2c8410075070300001421403840356103020111240603103110490000f144074003109001e682c0079150020ce00f403050602180b002d0080600440807070b201d10100103802d090100d80c0c48409221711a80741003400365011031011154070a15402025500305450079201408201c40102603403002e4000c1807800080245452590301982145c01280c0854000c0da9039102884183d403012400f6981c4090101d001500240c020105942e21034880d19140302c0e12007040c51414100202610180d81414902c00c1d0040c100c102000002c1d0004c6141003101001844018000c0001c040100300e591390030400b0400e624814015000d0300c01010380c6900075905c401413220010203a4205100d000c00d4020004003090103140550903201c00c2e0b501540e21100707000d050010b0540002900c41406045108100d01d4610301c08003032060a01a1403c1803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 175058750 1250 175057500 175057513
    0x20d0603030f0f031e05090102070f05030913060308040603020313051204091413030f1101021818070203030a02090f060c01090302010b0103020c0715020a081321032717 74
    0x9005241c001c228400805061030042d07039405446014002140d445d4401501050a6640d00320040c0a80950301c00145101080782855040003404000f0300b4021f44240c512151b001208007030300c0180c80d000d1001425070481004140100c500c02c1c0c00071603001d80f0350449041c3c10360403561078038030303107850f80700c0c0e07402000c40c00720b010300c40100326018018903000118001041030401d805008614542c0802c024180f00107920a00046405000c0c101602e0322110300840d2641148005000d407154400b40c42c5100c0c141d81103640c039494054030204d80c082c400d9903000f90705694844880a00035405805c20740d40c890300403514a030345903a884d002000000d61800020680c241c1e070b0314003e4251040d503045a0b0600d0b0040c88428011000068100200c0b480c3e5002448000a00e600980c28001040341c0a4180c542c0000c581c11040300002e0118102d4500e001203c400f1302c100303800c0e41c48585050310001c0020f10080100e030410fa075142d503403040c14940d11005e00070540c0d4452580080c14040c401d012036942210 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 175060000 1250 175058750 175058777
    0x803041a10081605100e1201020c03071713180b06040b22120b04060b03030c030a0207080a0305030a02030601350f01030305040e0a0615170601030605060a03020c01020d060303 77
    0x52201881e54419003840500c484c0c14200001d00450329110710504010303281842d40c01c070343d4603000500341e42e0b00c3c2000219074400380c0710791190b203c1c0d000b4401070302d0399562640c01210404150f41150105940300c5107800c0c03254140107070200a1144a8a03101000e0b8443c0c5c1c9006199581000510040440da603c0355a500180d1962800ca820f440c0d40b2075500c076868401c00c000c0307600064200b080c09035114205500c2a901d601d4400001c1c85a8101180c0510000c03070038034000c5c0b000000a003e22055a000c81d400c007580d84810f90f985031844000100090710600c0421443c43c500d40240d1307000681410624420750a4680c0819041400503031070101e03544405c5040104804e01141d240c103d00000c030321660560554030041c019200e10320135890003854480000340c0e6046642d00a05c054000200340d84403158141c0030003007102030a6034074a05c0c000d10341c0012411545c001d1080000310365000e0102800c2c0360050350700f41c0081d0050604800e60b55000c101c0002101c1d402e2085501851080d00c80b030b00e10752507a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 175061250 1250 175060000 175060003
    0x18100c11030d080c09060c070e07090e07020703021c060c0320040b032d040503031e190506030c130f050c0a09030623161103070b040803041a1008 64
    0x103090290300701c0181490719643c0300a41581c071041941450760f480485401043c01d070710801e011085603010f40c2c03001150030101444050300455403070b514600030079242c051903140400190b40d5040540d00480003040181048140000d018401390101b10881615455820940780f05c8108540000e5446020030344c0002c014080c2c9003402c0e50103640901382820092641c4841c88080e0540300e03848000c1d05c0d05843d0720740b00291b00030040d0f29500d1032800d9040903d4050303665042a40d8003034034007a0b0000c0c4d0070f00210403102d4491144010b404103441b1030814905a00052a0143c0f0141e0903011f49080300d5041d45611903200c4000740198000101540300b4400b000c00c48101800004601c4410008009913079400903c01058a07001000003842e04004208094840864050b0007000e59504c81085030080301c211088005480540f03070039076071060482c02d441e00c900c24400002c3c8890000c1010401180085019641c0540b19141c045100c4c580b01c04020b45000d8100e505403a502d401d6042806404c00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 175062500 1250 175061250 175061273
    0xd0507020d11070501020a06050c07080f0c0c09150d0303020d0c0905040b040b091803070b07030f0608070b0714010b0d0b150d0804180b060c1b0d050c010518100c 71
    0x1c40003401081c2c0c11300700000d4543c0074162001d03000d0340e220000704604100510071140c5150784083d505646004000d85e044460700100c40700b50a40c0a60580e92002d401d104220900c00c845c010500021240003008000040c1c40e8400c0070f504240d403c0c05480074140d030030320a4036445201d9032900c91a8500d49020481655504005030b030084c0d06085103190319454a1140c150005141ca2507512141e802c5400b080c914010584060320001744941484052905948126400e145c955808c0c01000d8036811195034510084c8920040316904000c0f81c03002c18a0404200701c440402800410703120300950010788461610082600c20840b07450620801502e404e124840026065035200690031407500c500394030380200d00c501c08e101c510404400f20300d402a0f0780b09548809000340413540382e18000758a40e6403a07215240c0c494844400c0a405400c1d403928070110340ca001c0d4020010980104401d004440c1030308030914200b06421804d0529400780e44080e2104440c0802c1c1d036404200e4840e600b03010358940c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 175063750 1250 175062500 175062527
    0x160618091406100509060d0203010915030203030f0703090f0305070f060c02030c150d05040506070905060f0702040e0a060c050316170708130b0c0405010e0109060e0904080d0507020d 80
    0xd2501c585000001e281c041c007550311540403a1800e4903010701e5a4151803511420820702e6000d030300024460020031b5242d001d1810780e010103004001500380302080d040074001d0340c000070b51316520030302c03640941c845042c000b40f80b414480d240551080da6191002c050300e0b90190001c403041d4000d500d003400010b00c4180004020100b91806c03848840707175500800e0715050350510b524050358003203e801c40c1a8240d801141c50609803c0303010002481e00b0300b0001d0701c80d90240c89407030010344c0301c420008003851700708107581d01540c1c030b02001490700a05508000090045086c2c980240c040c0c510742d00d001c12164031901c503503e48551a216030b40c2c54001c2c1c82000c0585030002c030605001d180c1524518000500303461690084a6040100312034075809602241c1030641a03000f0007460351041000b409500450180080f28400e0322482c1e034a10240c0015030740c05881e0300aa00000d000e41602140c03516002481903045402180200e1400d800403980405941040300c0f4400560700000c4004c2002e81d01010f00c80c00760 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 175065000 1250 175063750 175063769
    0x7050f012301140904030e060316080601090b09210a08070303110408030d0b0604080d050408060a0207020913020409060203040b0709050103150902072d03030e1f020705160618 77
    0x20b60424034403880d00030046000501031050f400001d82058041c03040000a660001c0000752030303140c01c522480811000c4520319000503882c0010a14a50007840c0240503a020f80400505102040040c4413050b580c6a9034402c44807903c03d40c18402c01c00602c09030441d280150100c0390394034428203000c0d0540b0090303005880050070802c0700300603000d0003006441d0b44404203503000c45c00368040700000d6254007458003c10703000d004003001100c405801400401c2200c075080b043d514151b903035141c000c00f217006031135029410112800c00030b01808070910900390366920013030000628800c00c2d150345007260412074007103541614600c28010242c5c2c0100f01c22005000c02d01c1d042c002d2002d4219404420340b124800c51001c0d94001c03a2001c1002104084558405281540b007a10001501036088200e00400000c2d008689000507402500070046280f410540c0c882a51300c800c076002004001c002c0d0302030314080c4d030180201102190550a5074001030001c00199444c1400c80000e03106030303003600d045a03201c150075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 175066250 1250 175065000 175065071
    0x4111303080304200607020d0515091e0a03020a02152701121514030307021207180b011e030e01050901061517061009150c060b060c070e0a0207050f01 66
    0x240e0b483c5d00449011a9061b1440f00d041d40084c0f42c005c3c58000f900c40c80d0450f11040f00f003000091080016061034501b860a2810001107030080c108c0d45400508a0140043c2c00c00c52001015040c0100707184000c6003d8001e55140c01c1481302002c5940100289603001c240c10076950340e00e00e6038051118000c04058100410501c920008a4a0001d0f80d51090141c2c011511500389a10b56044c425206959000740aa075400400b0410031030300c4081d2401280d00800c00c48102c940f95964900c00e08030520300607140d0a4080400064a400c0d0039450401042016101d60309071102c5c00d000e0250a0003415104000705e161414080c9100c0d42c40c000c01d4440c410084290b0f80207440e5070750f0000042e08030001356039101c2070040601c4100d40180c150b401c94903050000c004060b01e09a404a0021a0746005420130440c0f040c2d1442001901e00c0345410b0086590301c03a600c00c1c0200a80600364540001440e45e0051802c000ba6840d80c2c05c3c64111401185a82d41d181d881a0b0a14070a10f811402d043c040140c070001c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 175067500 1250 175066250 175066313
    0x209010f031521140106060323071409031b040507050f0706091e03090807050108070e1e040f09021509060304030e030a060908091003020c070504111303080304 70
    0x58200042c440c0800f01007480e0a600d8040f0b0011402c1440355402c00e500c8a4010300341c008440c040c044900c9120000707491328800703414901d040c1000003500800e400710f50400b0b460b18401100c1e011100007805180c0c00c01080148026541003040c1544420410741d5036000d400700004020484100400030400d1020801c109001000c0e064201c90000d5401040000c03407a109060051424442c80e115074806010101c02030103140d00400c40d81c0896144078111100151528011590304c141524450041500f00c11041aa0f1a0100d11000b060240c1440000d5040300000000d098440741c600490744695107114807030540c24444407200c60002c1242180d07240c4110180428002c1c4030040000c0d00300081c410261046550500c049004030760400c0d01400108103e00341210700e5404110b1443c461411800903170305103030007402a41d107108000c0c0060709000b86000c040c00040c2200f4040440015020404400c0c3c0001d10000d18015500540829480340707040c1c613007001c034101c000c0c440d00c3d0000c640992001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 175068750 1250 175067500 175067531
    0x9060507020d0606090e0601080c01050a050301210204150e0c041208220e190605091324051803030606090d060216051c03090206030610051b010209010f03 68
    0xc00c0a07906441d01124078a16080810003040580c1140841c1401c020703001d582c0100020f181816101d440040d580d04000d614015213851103850024804200240300401c69072400360102c0f01580d00c0f2142c814600c03c0342e980003c1c00c8862045d46840d6031204200203004001c2070104032640300c2c1c03090b003119107000c1c1070044048000400760802401c03500300103500000a0340700643d20980d41685402140e8070394881c0d14404440c102120255451151810f005461138a28081c0c0811a20301512040c0d140d10b49080518242081d440c00740e80380500d100c4441da840700b149a1005142c0c4035840009441e00b004024000d0248003010007400d281d005206010b03007a600d08007100d00d00351084490a00c241e00914051001c1e0280405e1800300101e0358042c1003e2180200c1c1c0310041348100c02805083c0303c0404402d40403030b130400b0300c01b0350021400e1001441d14200014001c44105e8541020b40c10041180211a201ca03d0306c104400b0318ad40102e071a11081d60040081c81c01c2100c2401c01f40030341146000740d0b4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 175070000 1250 175068750 175068757
    0x9050d0b040b0601050409062408040b04140c06030901091209180519020c1b040c050301090f0b0a030311010c0f0e010e060906040608090d0201141503120d090302010606090605 77
    0x2e003500100340082036050703000304225001004100c02c2840401d6450886181050000715a480022050400c0c00710807841190b0ba01e10950303000c11400d6464695866400c2c2c07030440c074a142101c07881020322900b055500c100103503100706200700022400d840b503031411030303d6407004414007818130014940600500c00c0f0060140071910105000040c1d50792031360faa00c004801041009554584001520551aa070100391182e42c4815100d008010304140b0040c0003c030781401400030001103007800148548030706a0020342c180035130040041404107540000035100d02195008801090800c100a00780403428090810070520609100300c0140406001501070714038219036504000b404c4802b0706059480b8000d80b8000713080641201d460b55210040134050040c2a92910010b01c60500002525841401006011800c01c0742c0c242e0103455680d16080520a9000d005600d0702880c10b07110070007202100507041000590340302045010f0f490802070300f110740980200003002001a130500c895900103044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 175071250 1250 175070000 175070003
    0xd1e0e070603050c040306110909010b090d03030f0213151101020313030c0609051b12010908120a1b0806010e10090b07050c09010603020c060a0b0a0b0c010902030d090609050d0b04 79
    0x1103416604c0042c40c141c03c1c4035607007000745000d01c2c110f900380ca0f002c00360f40a400a520261400380560f41c940c00d416003e80600b2745450b074060304040c6040b000030710a400c0180c00c401c1c40714000d400c1c0380c00f10f00e4401e10001d0036000460f87c4034010401c0141e42d94041130202e0340005042c0210314504040c03459200001e5001d01c0602031050404000c03040000b141d0044140300d4201c2e058851155842182150194151400501c41c1e55041e654221102c01031248029199100700e18500c3d00400102c50908954000d00e03041404c0e07501c9000098004040302851400b0000340d41e80803a51404500240144c0003608440c0d0043c0b50300c0a00107900c0f60801c1c052400d98402ea1282c03501da04080ca003040c80d0003404446c0d207820280f00000000c80d00c0d007580141603400c0c40e8030701381e90360380e56035441240482d0301840b841a030002c031042d805c01c00001010000c000c110050800440c0544094021905c1c11000219090010b140d0140400080e0b030f00c481e0820140c4402c8540340c2a4111980b00d5000d01800540b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 175072500 1250 175071250 175071257
    0x617100803273001061805070507050102030a020706141e091e0303070305011a07030c0305090d0b010f090902061c061703030a1802010219050102040b0d1e0e0706 71
    0x52035010300e042c040c1100305207000821a0128a401001c4050180c40308402c41c44070b06000754a040c150310707043c003892060f910340b018299100d54030b080030070024145c0a0140343c00d008081100c00086130080c0000e500c202080c4401580d50fa049103047e0044030f5003a07820001d002418001e02810384611007000d2984c002e80e4812801d84d844a4800301d00341a481072051840b036007051301103001d1000200240d8031584585e14100040c4c0c0e41c2d1003030108621007114078120042410080300f00068050392031448424028174041d030130070950001103151107940d00416500407584100400500226901d00805080d0701c1905101e0003c02d54085902801740045c00d50514038001c1000c0380009490b4031401c01403c2460b82c050449103110b4215803079502c162014980f15041000381e264046223210180d4440740d0690007041c91a80402004041c0700a41c1022180c65408020000d6400e81c3e49000d07007440e4824800002c2c01000f8a001040074202418140f110503061024a100c3c150000c6003c40480c3d14606 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 175073750 1250 175072500 175072537
    0x40204020903030403031706030102031b13180e010c0e01020c0402070f080a08150a050108040305031e100f0509060a1e120b160e031b0a08070617100803 67
    0x1002802a0080c00d00d0180c2500c4080b0380001031540c82000790010700001010340c03000b078460009146c02d0744030450711074082c1e4550b1558850121039400082080100301030025003260b8560138102d046240b00001310310800d8032083c000b1040242071044a0702907070f0608200c281241c0c0500080e444506880580d44103540c0820740c001070008203282004126401040c0d141d503000d0380350b8040d0038400240d8540781c1c900c0507000d0303119850400d00c86040c140c900585440610740c1d61a41c08030b4440c1c1c00101a00d00482400200c1800a82510841402032002c1c030200400f9a082c48080783c1c103444540c1c41284510700c0c000078002192a040a0b203010b84040070812200c07000c00c012420801025a8003401480528507081c1091044041c4034a01414002c0c1c0700c5241d02200060446000c10207489042d8150040e07038594034401c92012403c0784c17049015043d03615456a4003881d80c03c050301980600d002c02c1c00401c0c4d006400301809802a400388004820b405c1d220f040001d515034030300914048c50500d52119 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 175075000 1250 175073750 175073753
    0x9070f120512160b0906040c030b09100501032303250201020a0c06090510020d021c0212070b04030e1507080702010302091c06052404050426090109050414070804 71
    0x2401565840d01c2944045940d550003400f0311440e084594200f03a0f00c076005880407555440001c990703240500e81015440182034110340720301d00b0f07101300600058035520074050010704a8189028030340c02035010f5140040880b03c1c10740d04c0e401b005902d2030710138043d410070440b00409603540e0200c1100e20000d6192411a108a0700c0144c0c5801d49041c009080c014440310b000840550001a84090790030544929040720100c20041e079079000040b20701c03005a00001a60750a002c46400c03074030a4000b0351300c11150b5071039680b0078140340c5900c03004090314220021002c0206141c1c020084020100043e40c8101c0c1030421080301c142d040c0903080c40100440d5000529109581c4030707405980d19117000820040f424682040030b4080c60423841b1007200c2c4581000009000c4282c8030f038000d6190140b800400750740000c035008000003040010f00494030010100c202c1113088100c4a0058880741c1508802035586141c0400980515055072000348524103140c24007004801d003444103500203903982880c0c00d0701c0d240c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 175076250 1250 175075000 175075003
    0x1030b0c0c030d0f1808030f06190905091e070315020f270402030c09151603090305061303050a0815030f0d03200a050d0f050112030809070f1205 64
    0x2182500200c910020941000401c0f082c4c1c0301c007100403030340e45007006500c0807009410117440890801400400c0b0034400521001c074409a500d0780000c2c02800c40202d07400b00e01c420307001c40c1c00c180c019140c01d039034800801c0822842044104400c002c040014584003032414401565440340b40401000d4008202c00d100411485405485000e0004040103441d8450080c0b905204000303001d000d0f8040ca044c003110000c9040600c00c503400342441d07a1049140c680d120b0180100841145618092082c081000751458485414680700d40c82c80303941c9540300d4a2a508225180c55800340c04a2402001440c012001a40060072148000c01500340100d0f90307682c0183c17200c2d91004041d0b08541500500081001c0054041a1070144d000c054a0070802008908401c41c01d2030b518001c001e00b414820081121124040c101400c1070458003100400c494030031b51003500c00d4038000c3c0c1c40f0100041440d1012010540c100164940c0001c10900800a0915008000703a10403040d10a20003c0a044170036001807000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 175077500 1250 175076250 175076257
    0x10030210110a2406150c0203030705030d061a2106010c0b040302071a0405150310030f060204090501140306010312050d0510050306010f081b04060302030d080105040b010507030801030b0c 82
    0x80c03800035211031100c10305140360350f002074408851108a00f0340740150345214501c600000d440c070079075201d40c002d000d01c07000341d0ba0301c0740e0400d0907a4107201c18020310000600030030040a45030502c0e040808c1062400380c90603125060302340089540c1c40240030340d0103821007041c1840003040c8801105409605c07179400603109101c1100000d0f00d60f144140420092540000d10315049401c0010031000820b01c4201241e480d024600940754070900e11151003100c154442c000d507130056210520200d00540d250345244501245042c100d0380381c0c0c2c001c142003214942c3e0748105801031101c2c061841444460000107510340782c0500004141003809482a00f6052180090710b01109400c0820081c0d410a40c02c0c2c0d041000c007500c1a82d100c5d02c202c0c4000329280340021401401c6498000042c0399020085d4084043c20ba0013240303042e0815130b90070300000560381c2082502c0c0b00c1200c545032182e0950400c1c06000c1980c1c0003a080343c5c14000204075010001c0c0c1c0c0300c400e050449420030620a816160510303092110b21 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 175078750 1250 175077500 175077527
    0x7110112022a0d03060803070f050309030307061a09150427060902040c090b0d0c021f05040b0604110d0902061315110d090b0c01060803030109060e0c0310030210 71
    0x4408042c840000c01c400c451040c1001c0c0382e108441c020b140a4400301c0c25078041d070046809981050003c00002109100e1810700782d8401d60a40e81010f82040c042841e41e04844029951207445000e01d41006000255840210105444c80003541c40c1000c095442c0d17810742c16078103000f2581c802c00a05030070713030f040a03100e070a000004081112074601d041113006800360038401d901c55450105441c1c241405003084800f02c500717100700e260401c40889403200c01032140703200c101b056014a0074a1201c05080c1400a00040d034030400c0040c2604040c00c0100203c0c100400d450b010385d20300301000066820060a8444880d410100071a10003500c2c8003003101d601450103c01a1540325074000b10301407181110306603617803603070765500040c40c5200c2c00c0aa07980d0040c082c0e0a0003003002c0000a01101e0a914003d095001d41440041006641c030228240382d544240d00500700680d440350107103d1108891a8940c0180702414103d086040c0f4141000e21404c103844000d11500070340307070460300c071078010765a65a82c0c4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 175080000 1250 175078750 175078777
    0x3060b0403030516060c090f050409030e01050a0e030a060e010f09050304050f041808030f0705070209012114060108100b1305040c0801050f19020a0c1415012402030711011202 77
    0x80315002d06c050410004c40c0204078151140c03080214460805108415a00d6010f0f41c58010210300740005580507800b0748200e00030000d2156440e5800d45007080760245051042d88000b55416601811508444032814450001414085040b01051000090340d00741d034401c0718840608021030380050000c1c00b55403000300095140c100c01500f44501c03003014603c00e0500014040480c0d544800880f00b074410514020b60095044005000e1038108100651001e03064205120a05e203464a82500c0070000702030518045c1d011000500c0050024422080c00080702101800440c0d202800100d41c0c50b82000c1c1d94551a96600c0000c041c0b1020b8040480208400d8000700854140010201044101140d80c001140d0f100c0740c8000c03014141d0702c00c0703d00c80d5000d9500c0b000f07240c0245c2e41c0c1c108003c0c200701c20740350340d44229440740101035039200126000700044802c4080008210481410a80111000d0002e41d00280b08010109190001c0056825002d107001034014481c801c2c00d200a0003100601e1415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 175081250 1250 175080000 175080011
    0x31202071a0705061f03060c2606010905030309130c0306030807050c0307060801140d0203030c0114061302040609090e01020708180405060a050a060e0a030506040308100603060b040303051606 84
    0x21001c40c4010b00305203000700180d9103950348002c0d21188000340d002c000b210700c8036802002c0001c54041ea000e048402100d00c0c0100d00740d00c0304d16060850700c0c2e85c0180341d540b1081500c10300820b0368010001c80014001680603500b084610b2001039680c00c84880c1c046201d41d00e4052900b07102d403083d40032a014643c03049034180c07100110700384541e82e4084000102d0183c4039104011581038091025036040320600104880b0507001c2c10b00f8014015a0028200e03003502c000e0000d48101c40080c00740001e0f905e070320700f01c01215103030003030800011800389860301c945ca5104100501509906c2444041900c0170f540f40031600f4841c0100d0703980203206689001d0301240000c541c50b96002038100c48003040d800100e03020b100c1c94407040100004c3c0c041d103128140c0d0000c41507000300700c814050110031442e000014643c1007429034a860f8181803010880b070403400904a5010008030b40c4840f0010005454a13240400015040040480151045000240a1040200300551001d00c682d040c54440c07580144203200703 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 175082500 1250 175081250 175081289
    0x90f020403170d0e010605030d110124150503130807050109081b1b0d0f05071805090f072d0306090305043003140c250e060303070209090f03040311040b1903120207 72
    0x403040724033700811647c56288940c0000c502c0c1314109480c09050941d9072528100710035a5603000c5507000c1d040441d969500d80b901c41d40030400f064050841240c015080e04d801040110b011030401d0b2002003507018803000c6581c2200c940e01d50041114000d81c2c130080070004088181011844d26400d0740c8805c4003401c000c1d080b161a06002c1d044203019a407038008840d9403800e40c418840c0c58403210f004008002c1101c0c06031425003c5c0303110402c018090b40b5010540015181d03140d042c241c40480c40284d02191002408000d6100302201c0851802a1200210403d82030400c046144004000340a0200084c14204422000c4030a04950700c0021010480b81c5400200304404091002002c2c440e20501c200341001529268800c0040d1003000014040c603d05405607081050485000e80701c000700e4459102c8594460100300004e00c00786008a200d84030501c441d4040200b51107011516038000c80d210121805841c000045481c2070340e034031080074059801110002c174507190060340054039100c2d00400042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 175083750 1250 175082500 175082561
    0x10020f030309150106020d02060a0209041e0207051e070e0627010602070602070807180b1e041104060e150c0a0c05030708011401090f020403170d0e010605030d1101 72
    0xf030040c8004049110581e80c0c8401c2079032510840c2d5400030240c0c0002000640d0b14035190300808024400400c00100b00d80c014500d0720041e04480b0202184a81c000349880901204003ca100010310090485081401ca41e6040e0b41300e440074410f0740d50004442000c41c50759a103051108482c440c0325500c080854201110034802c0c5002841440701601035100b022034501e10101e01d10069a689400500c00c5925228801c20004600d00828034110390758562886c1c90768500c14403008464110550031600d10b041010041240c5040080e00305516042000700700c195000049241102d03070440f20204078052010140c83e09104050800d1031078055003050004000e010070240b010345200b0b80c110b0f80398548920740b4074200c1e0268680d50710302c8a04a001001b414005401c060744e82c05030014050705140e07407551500240c0c1008050042880b5021030f0001c2e0211192040020425080b0024885039181c2008a03448200a4551a04115851521009460094111086024a0a91000b0840c1440d075045 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 175085000 1250 175083750 175083763
    0x705100b0319150b010201020306010c0221010518011b08070818010c0c1704030b0f0a0e1b100c0b01050d240b030615060409020c0c120304050307050402120610020f030309 75
    0x1400d0180c544a500f5035554170508c03c0d00e104c0d50341178503003642052103a000c211062100c0344500306818a40075031414000c44c2805400e0050a100354404155a0703d50006829030b10f04a84050b0804c50107201d01d000503038004000e83e0040c000c1d0821003101d44412040d0401c0810080d03800c0b2035582000108a44142d000d80c0950300c46020300348070510803003070805d0031040e4800c40c071028022001500204010700a00f11150380c0100d040200000c00060403038081e8249415080720409800c40a8620300690402e01815070a0f0440f034079220340c95842d00d5580a00c0e103001801014003a452401246003040286240402c864040d00e00303214401c000c0c404080e001c6d10f03400d0880381c040d02802000c500140000f00300d20030040e030001d000d41e06080c20080c050000b5006010503d8461003481800005074880c4840e004440504401031507a075818a03081c5440d201c1d4503030050740901d104100c01010382c0c00310350600d5005041210302408001d0680812840c010810359407422500000003880290075000501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 175086250 1250 175085000 175085033
    0x1d0703053702090c0c0106140f030133050405010e0106140f04060f0306030b04030816050903070b0a0507081c0b0906060d150b0406030905010509030705100b0319 71
    0x204680c0c0324600c56072141c5500d1880d0600d10000c034914072140145024a02c0c207030300c510800802c0c2c0c18981e10844041c2911825031003c0000700e805c4503900300504000013070100d641c0007980240f040160300080081c0100203428040e0400c00340304070306c041da4283c0100190050100401c284165611400e290800340d1083c4a5100492029041b28001d040e07040145d810070b00b0035081c1103003003503d060003d44800c2103c504000c105947c0380c002100062900c00c50500a83c00381d911031556140481000ca160180c003404001446001d00200d45107581c0082c402d015200090030071604c41c120914190380c5405030400042081c2c9005c80d03100b4680a404494010202c540c0000b40401c440120500c4003419080d29007a030032a0341000141101c441c65000b0f410b070350041e0840404861740e02c000e254401c5d00311340c01c10f000282d100c12616040c401c0c240220358025507140043c5290942c95512940e654844445095035039441740169100d50f80c0a00604544074403130b0b4080c41c4811510700d02130442a0030b5015 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 175087500 1250 175086250 175086283
    0xe0c0907020706021b0a03170304050d110714030715050705100203010e13050f0715090f060c150e011107060e0a020109051c020402070501020a230a031d070305 70
    0x1425503480018820708403620340e00a0085d204d20031002e07140b03c00b00c0c12045a0400c1c0060301c0040007610131984000700041009060740c0780c0c241490024207000001c10410100725006080120440d0b02003200e004031081c800e40248418030000c0424240412075001c4241c0301c0303200b801c0740a5030b500301009201e4140b0070b400f5601e28500754441c10b02240002e00890401c43c1a24002a6082c400c070469011454000d5040f42c00c0c100b541060245030507455003201503030a524010117071071541c00c010a43d007d00010110052190708041c0001e01500482d00c1c0900782a0402ca584480c0c140740f42d01c8841d41000395030092041d40f680300c5108905a01c000400c0b42c0700b41c0f40544a0054020105a40224681c16135800012078a400708000701c41950003c1d00322428024214a40142d40360b00c02030540c01e02c14000580c640580c1c180207846110b5114064080c0f0346612500450000e0304821035200400c0341c1800075800030660100c01d180c010002504038984030317000d0040148400000d0b0301c44005030044 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 175088750 1250 175087500 175087519
    0x6010501121e09031106101403010608100203040c15050a0908030a0e0111010b0603040605010801060e070804030813120c11030102070804091a0a03080301050f040c08060d11040e0c 79
    0x84480086405200b8400486400d491094806940507006900c001d03000380b401c14002c01e12515039500304001941d11180c10320728480104070440044540101414084008121789441c1414503a00d4803401e00503401450360000000c6e0800c502e6520038000740198860031104403030b6030701001d0416030210510704040380c2500800035003008000205d89000890b991414420b0308a5801550544d250700f4501c50955200d40500100d80c84440c0603510890080d032020a1951406a440f42150555040580c151030120200410317a500b100340241c11a070303d490f0059903942d800b100201d000d40046001050000c0d58600d0b01e4009a01245204036180290411440d112800c0d041600300d110300c1d40c004100d55802d0000704101c00080c1c1c00104ca00001c034001406102200d030002d20780c03003da50400c890303108010005001e181030600c100c400421059400300446150300201500e0802c00828091007440510400da041000d000c980c01d0001030045c0052107640b140980b00d075201c00c4a103503890b00465030071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 175090000 1250 175088750 175088777
    0xa0b01111207021c02010e0d2a140109120f020a0906030812060306010f0611150106091403030a0801030b07030e01180501150509190219050403061505060f090409080a0206010501 78
    0x1520342d1340010390584448115411102c14800001820382c819903c50b010000780620510308616a9a2440003020740d03410380d14208a4811580d5110421480c10131105810601c441e01081c3d20070030010f81c01000c5001100028400260a503010750004d10b8081e0604500004011826024001c04902680300906a41c0c8980c2417554400c02413041505910003a1070400c80280140d0800c1184920780d816684a0701542d03000011a1000380d22810000c1c03e042c9e01000400700c2c4a5101c64100300031400746107007001e4050001e044500600000d0300074404200031401d01030083d40700c0c0e03080d0f000b2500284451040c954205091020101c0d003581c182d400c00090980d00e92900c030002c019100c000304510441d80300c024101c88000c00c14014a42020340c00c00800401356942d00e00d50000160030707500c042d40c4506500d08001515008284024024040701c4280403e039030f00f105944400106070034282e22141c41c0700004000d003241580c06404000d001481070300d02035011070b40c6410380300280c85528260082 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 175091250 1250 175090000 175090039
    0xe0c090409121b11040b0a03020d0302030703080702031c0c050d050408031602060c071421071a040c05041109060f13150801030b04030e13050604050a020c03030a0b0111120702 77
    0xc45001131081459504c603661034500350b4484a210700c80a407030b504001d0f0700c81d4081038280c0d103450b0f01640582e1012540c0360815500000f05503028007548055030601540b400751118181070700110540083d03c6440342c00410b4441d00984d900e1904d40c56040c0b100307007014184505644d02c01d6580001542e1103804c103c8a880c00010310034080c000c50b0311003070316095490715a60081104190f43e81d00741d0003030044620b114001c00344803000015994004581c2e80c000b070f00d0110f0204941d1098500103c0c1d204040102080041e8040300440e20700b42c501169404a41101412030322508800d594030220104801c0c103e075400070040c1c5907000d030200000d89060740340c440322108100042511000291800e00500c00924000440380e04548079090000c0030f504020000b9a0b000e0050000003400d6550794204140c40c50a40503240e000764140e00c0c1145000e9800c82e5480d22480010440c0a045840d41c00140d030030b0b449440c9010145000340b003a20556681d4402c0c005007a031206c1026407140c1d60550107a55103080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 175092500 1250 175091250 175091297
    0x90306060501030b01022503020a060e010f0e091b190909060905060a0b07050c040c02010902010306144f110313061805070609030308100608010e0c09040912 69
    0xc146c00410220000804681e6158007103400a40c004404550010042c1c555001039409040181c451050100f01040014030000d2000700034003c100e40d0f10800d00554032506d044d240c000721410007002041d42107080c87c0d82c580c0305500040351b5000c03100c0000c1481030740c0507138040b040c2c901064061020329514444c001c01e450040d0342e2698000c8a1140410010003024000e2090351320600540c0e40ca0403000f00003804503440d5280c8000980d440da00030008540e4184101c20141c0510300001207a00d60307400110304000c2c040ba084040d00e0691114200b0003070b0351055440e543d10304000b21001800c82da0750304018140e041404084070035041a0940c40106416001d880c828042d003551500900f245890f2500074120002c00d0404850030304c2c540c1c102140c424000300c80901840e4941c12845442d61030002e145010090038244e40344090a024402ca9030f03c01c500c281140d69080500d00180c03a00b4842c0c12080c49606901d5611601d03280070350302008504070040e00c01190035158810751404c4810442d41602 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 175093750 1250 175092500 175092521
    0x50109021216230c16062f0a050f0607050306010f0e0d0c09061a090303041406040e011806091a1306030501020705030711061612140a09030606050103 66
    0x101c400211105541102c440788030381c03903291158542c800d1034072007074280300052078060302480c001600c07200c400001c1055144d581c000d40e80c100e002c10b103000300041404d2006506a40403c10350000c0c48101860442c08008140034030068400020712032605a548410a0030a00c00070302070700e40018209401502528880d40068413a0403860418600468448800490b100c2d4014621227003000820003410b1513038082c0c4400d19000820504224442821008407079003034811010030008000c1e1500c000c0103850480e200a20390443c60303c4410005030039402960441c0101080117000054000884007480c140c41d2602d000c20020a03407511045002c0e107402d04e550140c0e2002c90407183d500340c100f80951000040d03e9000c006160b948a82c0c64509980c0030510984250744041102014080b0104113084910b00480e019450000041989019000b81c0b51000e0240d2281840189005000701247c01d9181d00311491165609038411000c3c000c0410b900040d684980b504001251039400780c49181d20b40c6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 175095000 1250 175093750 175093777
    0x8060901030c09050705040e04050a050f071206050c040e09031305011e080711030708131d041e020901060201050405070504060803040e09163b04030f1713050105010902 74
    0x103091180ca40040e1001405d80402c0090420000603401a4011414050b521582c090003455000c0d0030301d10714100f40700f004802103402c40d81c1c04109403c0601151900d0650081d4017040e5039842182100c0b40c1e01880e4000c4404407001c1c0c4c10032012410102c01401501d4900801486094a80700112040c42e6080001a02450114440c107602070040910310b522081c0c524000e000d01b80b400c0c031914255007001c0822580b408000c00c09145d003031103900300c2c64060b00081803052101a50007560003050341700640302811160321042c07101910b0103c0005100c0c800e8008d00381800950b0b60b488000d0007004100d41c00c3d151405452004504c902d070500441c01240c0514000350f05081c1058204280300c0342c05003440000e44a02c2e10b60040c1003049405650081804040d0391100210000c544e0414031701540f580c581c0300b1140c11002c44906101c5c20141d802a400d0b00d04001c1c0b0386c45055080d07031400445411401010490000c101c0e01100744622140071600c00c6000384040d1344e955904030103a0007200c405d808074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 175096250 1250 175095000 175095023
    0x501051e09040c11011503170c120a09030c080309060f0a18260a02060415051201090b10020102070c0905040311061005011404050a15051308070302120a03090e060a1805070806090103 80
    0x80d0001d401810509c0d2603141134a821240c9114151115072003241c02c80701040e54014100240700c003080a4400515618014515115080002404510685c2140142c6160104a40e420700c3e100780c10f00e140e464440c4a150a805407540300e480718490b4207400070020345d41c18010101d28120042280c0c8803459000e03000d542807905012803540c034094202108001c100d0300b0300010040c9a40503004600a085a803000a8000215010301c80603030044400c00040d07a0041044000113040340041d4012514400380010340c035229882e08450745480ca1255605901c980d400340000a009901144110386090300c1d034034510030f0700100500c0e0302c0c0164820140d009034190010050300c030004083c010703840e40503c0c20780d01d000c1441a04200e40c1d00c1d00c1e08007a0140d0f00c40f0109000310704141442d50704100801c0001c0042045550300100385052501503840408900b0000c00c0c025110310041c40088c014851070280001d00d03807540c00000b0041242e11030000b4031580e02280d81c50400d0010b2074107a94100320809103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 175097500 1250 175096250 175096283
    0x1c02130506090301090f12020c090108060406051302060c0f1b18090c090f06180f0a090c080a0f110a0605031503150f0a050a05010501051e09040c11011503 68
    0x24a03402c18048150155201c0360300d90700144984d00c02c808240d101e07101200720800200b01c000e150060b042d40d25401001907a005200d210800140140c1c4103500040c046400d40c1c4042220a40c0c8040b6600250400c0010a402e041103074041010110980300c2d0040718071030300c4131407480d0251217031540b0000c3d00b02450400e20005400310250f4158800482c400710340325907481c000407803020307041124907907018560001400f0300c91400b090707407940a064181c42d003980c40c00d003086480a1800d02401c00000c1566580c1003008121000a4500041000a0907150f0940c4c0e0303810f0915a200e44c2c000f0803203562260141c401c0562401c04240d170181c8032540e843d641160790f4011164000300c071807030046605100b80f5000ca20b0141c004c081240c400c2480086035105420712110400503164050440e0b2445420f140c018000c603680034081d9040030000c14a00581459008000311061040405190300581490f00c0840101c2d040140e50408424103c006c004c1c03040090215101e4111030300000b844a4201c03407001030f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 175098750 1250 175097500 175097509
    0x1c020f0405010c050703140a0302060601020109151a090108070e1b03220b0406020703030c0c02031b120d051c0b0114251b05010801030b0402121608031c021305 70
    0x26119200d582280c9160b6181e444605c0440110147c1940640c40b04945d0000c069051041c590084000c0c0001d00080d9950355440002c0011141030941030382d0f492060101880303880ca841c9030f4148010f0320318562540c6a41e8099100d401d00e002c1c2c03076194406640031520000003850034420b907002e4005101d045444900110b0541040aa0f2103070304071760044100401700c1e0790b03400c10760b01031072003480c0050b03507038560745005000d6520001030b46c01803003014048500941c0300452405201322501040740207500085e40040e940e6007000003c40703000d1081c0c1c08105000e61b040700c0101006401445011240d005545c07039141592002e51511340003482420300e007910f14034a0b0001d0010b00c03001d5081914040881105061a20503201e4141c8050608c2d14004801c011041d003048041c003801c0c6808030700c0c4d6056803070303c480f002c101070700081c040c0080700d0280d418810b0501c03446418100f1208883c214170781d100c1d8056601c1c1c10100c00021450010407086803a01d18030b10032104036582440c00d030000c0c2441c000400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 175100000 1250 175098750 175098767
    0x602060112240c0203030105090f091b1504080115080d02070605030c09030a050106090f0c0203040b13030209010e0a3603020f070b0d05060303030f0a0b04110a02031c020f040501 78
    0x15405000e0310b88403601d500c0c0034003451002e690300d68000e64032503240a0421034901c1002d0b01810502030800d0600a241c20041110800503010700b074120b119025001c00310713401e0b120310900c0d4000860042004a0004419005500001d145165816a103501d41c04515160940d2040300e1001d82c0c0a0b001c01c011641c0100c029541c02402a100303a41071840c5c003c082418070000e1a8201e0b01039540390014884100d0510903090780500b40304080001d0582c0c00790107507a80c407403409180081c010100b1604502c130402250070016583c040c3c60b480095950392a20340c941038080c1d844014103800c001d42c0504021804a1100136203981c441c444482074a01c0002c05440d000300d000076402c40c001c0141000c424401041100002e003c2c0f100b0080d547e118407183e0804481c0301502c120300c250010014854441501c0d0031700b03500705e841c04070001034501c100383c0050010074220105454040d80450b4034018240c0100240c80000004642c01e0000e442c01c100c818120710900c040003d950a00303010034412544030720380d035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 175101250 1250 175100000 175100033
    0x4020102100e01020a02120a021f0e03070b0901390311130f0f031a0a0e120a11060106120f020405030f011b020a24020915130602060112 60
    0x56446200c00080c6001c10b848455061100a030b40000e01100950750410820342d8003010280000c1c2400d80040000b51140c1c1200c42c100308540902100000b403c01039400034601030342030b20807607a60f80744526169a14440480301d0540359440c2030b003820b12415511000103a5412000005507040074101142c0100500c0700d400a01015034407540e0b200840e41140003480803115000302c580b032a80c5808180200d015244d008011212800030040001032090052250b29148010034440035949406545008051440e079a0401d4810610380e080c40000620050100c50115500e042003c04c0c220b0701560b4800c420700c24200010f103d404800592640759108032880100d03500058680741d40d410000e07252220300d0f140e0310182e95458010700078425141d4460070318201d4500240c50103410700c2d2960162140c42d09520030052440d10b09440c102d40031a412580031410003031869a089943d070301c400740540c202107091003000400703400c00f14905000080c1181251101090720045070615034070750040101d8050b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 175102500 1250 175101250 175101253
    0x3060903030b04050702010b190b03070c0807050d0507060b040e06040201030c0903060501080c01020f071220061305040e030f09120a080a08040b13080702040c021e0705040b0405060603070804020102 87
    0x3202050f40d507402000d0003602568008500e1800540421801201c00c6081e0152004e02d28420400040b004061382d60010b52420040300c900803501308124548a610300050543c069030890201c410b8000b0098400c00c1c9c050702080246406040c280411200c022000d000140d0090000400562080e00005944d07a524a02041100e07541d039900c0c0c0584200307811045058111440290b01f55034100315088400b00706100900141c1e140111003007540c0d01840020f01076031100c41307804c034420f0704e800c285600c00b0f040036040a6a40104085000c001c04081c06170f13a21aa04004503281c8038540017040e91801c07051403514a00d8080010200568078072002c07480c03140c0d401400b0280c0040380d000700150042031240c2c0c66868551400b4940754440782d500402d606503081409444001080e0701c50155000b695059400141000f0312803803c0c0e140c110410108828942c2d82092100d00c0d04000c94034000710781c1c0a0320b00f4864901062b0810003921740c100d4506802081c2840000c0c2c802d8030404140741c02500600 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 175103750 1250 175102500 175102511
    0x20f10030204091503050607030504030c0b0604140a0c120204080c041a09010b070c0602010606050d0c1106090a1e021c0c050303070b07020d02072304020418060501140c06010306090303 81
    0x24000000e4500f106455004c0c603c8120080007400f809118160f403010251070100000d20306983e010300300407192840030f41900310a038002210354403964060014440083c170001e035240752884250005d015058503020006032003000071300380d00210b802500c041d0342d91200509452045001800000c2800c24190801c84d0750084101089841d00e141040c041d042c403a19040e1340ba03959041c0703200e4441c0d465008400310781c504401000f01540c80000d0b41d0192426080c040340d20b0841d040304841110010802400c140200c4c1c0c14000150707800100a010240306074140780441d500c000e1302141c42100804040d4200740c40050700320054420541648030144108007001302e01d034032072011038074542202104035110020340c000c0c006401d404000d0326104150310b00c01488030b00d0408003680d90faa409520ba0003840c003480382c0590180d039102c0e01034a001d410101c0100110341e17540748200006e0300b428810540810101301041c545080d549003190b6100c1001c000030000d603482c554880c4010250a0000d40425950383c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 175105000 1250 175103750 175103759
    0x19022b0f030b06040303091a09031c030b041b022103160215010b07060b041a130902130501090b120c010f0306030204021204060c020c031009030905030a0528020f10030204 75
    0x40e0150010303600943d0b40d40039240c200142c4188401016030401448c1505109407a40c590b40001c00c0310b603c1c047e0f402858640c3e2041042a0080d2441800c0030707911900b002d80d18051403000c2c0c01684c00820481d801c484403880080e5000c008403201c003d004001480c204000303520b0800456a5034020340035441110309050001d070416160310003e03040200c50010001d00d50092000c85e00859440d610115400c21480e2221400a441e0100b1211a103000311124960082070414541c010410150080d20400136140c0c4000814000c141c24050b4281d038600e0140a941d507403c14a11510b0201044d9005004a000e00401503503010309580a4030304043c0c41d039001100580322303030015040548080a00d000142054503040060f54503c820300d80c01c6512141c0c1852a56500045000802c8503040c4001a410314900307080300c01e8036442d04541e805200e45043c06040103800244440f880640d0f004908091150540e80c40150003d250042c2d403084440418032074078071b0448400540300b1a01e06005182c580e54 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 175106250 1250 175105000 175105009
    0x1b0f03051b01020301150e090402040e01110f09120a03080408031009091103010605030d0504030f020616051b0307030201050a0513030204150602010515090f090f0319022b0f030b 78
    0x550500c0030740b65000b100401070720700e102c600c3c00c0c002c2c0002d045ca15208450840801c0c000c45009101a20a50702e6004544800000390301500984c600440065501c184288001c0b82c1948140c0a40380111040a00b1089481004c10404503859040da6018015102c0d600c400c6125000034003c00d43d81d4418100000d0b03041894850a4016403041700745081461160041508569150b80682d0080c0c01c08101210310310f0b070000488003500d07444141ca104092950010800074000e40003c01503c128281220080c860b00280341d0201d400c09031900c108210202c014552905001e01c002030108001740004017007540610301403d05071401a40c440703503180d541c2d00050103442041c12110b00e94295468141f0480e58280101980031010b008490f1403480c851000c589030a1004140071441c1c103c90000c509440014031102181800d0390040302d840d40c940d0300050394080a09651500503110f540705011181c1c510703020641c081c100d0f403050071684040c856001c0c0e4100e541c02041030b003010703518181505a82c2e44d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 175107500 1250 175106250 175106287
    0x61d15150a1215050910050f0d05030409060b0c07270902040b1503090106080109020d0f05070e0907060e0111100b1c06060807050d0503040311060d0218040c1b0f0305 73
    0x20321150000300c18a00024410040c5c0b000e424480c2c0d100940748180003584400007000104071064400f0311800056003400c0d4214080d64205001990800ca8000f6825038642d0103401000c1c25401a2800580d84180505004a43e1055541c08101c0040f0030b40080d44a94007809001380040c00100b01e1951138000500341021607040c50038104800300504c003134401d09102d8003025201c004001c12071428650002070903c0325580303004003a41120803007142084810320003c0f00605540480000a00784052616111486070151800244680000049540c0300303625403141040c00d4009082051010407201000d021106012074008008206004807003d401c40c1c0e0380303004c03801094001060b03414005050300f04007495200d14400d58103945100007244020048600f01c95004242401c90b010078400305440d40155010a0103483c0302281e186040310340000300d9040c07018101d4040002075854142500e481503680c0c0c003010160205092500000c4011142004150223400d104d810910000c111342c030b4070076 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 175108750 1250 175107500 175107521
    0xc0206031008030d090302060a0c0e100908030313120801050d0f170f13060206160e010e1e01090519090b120a0c030c05060f220801061d15150a12 64
    0x103581e11700d040c0038542c0c140301c0d03a604080f07a0343e000d00048070f503044001e01d2001c000800f603101d05240f4160074001307801480358100501c0c0c179400f625102d1412100d040c07056508158261030262070100512002c501c0f6101c81030681d0b1004010303008114842d1601d00e150943d200c0201c80a894640400300589042c03c054440c00e006c40103815a0b0303d40391240082c8607451640400159806a03043c1310f110004503000d9182c040c694600210004064001216411803000410341c1080c1c440407100308000c0d406081214019081c2c940c0070a60f951030051229050070060221007540e05a041845000c03415001010010b100810340d04000166042032824403118110460341054038250400801ca14480c504006240c11501c042c00c28940e00400052841620381001003459107480c09440711701d801c00080007600c111402044040c0d100c44128554140d00d1882880a4030658000740384400520720f0714a2090b40542290729110220440c64202c2d00040449001d000301c001c90a9452002c1e48589010b10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 175110000 1250 175108750 175108777
    0x60512040807050c03061003060b0901150c030e0a0b03040506070c11060c01090204050109020705070b0703090905060102030c01090302010f0e010603051b0a120303060e06010f020703020108101707061404060c020603100803 97
    0x1f14558503080040325460b01000340589141e10041003c1c240d2104505880740f80c5003006d0129020750301d030840d8404903120409520800091020405010300d001540c8103d102d43c0131620f85803617011080d01d00480d4548000e00c0c05401d03e18418960805001418050115000200d075003078256000a042c0c81c0243c101c41100eaa0102d20602480801c01c40080105421087d44c2c1c641101c640f4014608245809000310468641010850a0f442041207070600b02141000b04490906481d00034040e02400c85850203071070400e43d880d4000030741032080004580c0d201d4014640500c20b0505244c4194015034040d5000720f1400700009d4850168000000d258401e5034000792007802e0541d50046454054001d83c1088a08002c4040316600011a101540d07024289500f0a6a407a82203541c581c9094001e00340d035468016444030802c000140000a0700c0c0e842d140c000c0d940c00c1190704101c450040e03204002c000b407411031800d070140c2000c00040d600b00c0078221410032220749030340c0301600e194424180b0081c40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 175111250 1250 175110000 175110031
    0xc0806060916110601080a02090106210510030b1302010e030c061803030702030d0201060806150618040b1914010311031810020c0c15030601120518061e01060512040807050c0306 78
    0xc5140807004079026141d9400e08cc0c41d405001100480c002101c044d00207142a41c1c0e070b0205824603d0302c08203034011035121090150500d0034200e000c0030404040822804220310546980c180d20700422074008194001d050281040f4914010059100c00b185846030540000c000c02c202589040c07024820895030b03a000420402c0c03421080c1c514180008180403515030000380d4641d010740d01c9004071213550f00000315003010000e0344000500101031042006600c9012009101c9403c6c0e440c1c1c03880c07803c40c5d1403102215607483c0024019425503106181c440c81800341000003582d50410001010100c00c41a070417111121540b001500403070f88100b4003c00154005102881c0b036180c44000d04610381c1d03400c201e44d03055003080b01c00070303221104603011700501c50348900002d45110001441d01c64071050072400c075145400c0041c64452101000031124544000e07090010071400c2c006e60484a0307528000d615400d06541c0d50315881308070f4210510485880c000d5420784403081c0d4007001858000c0e0281100d0981 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 175112500 1250 175111250 175111253
    0x14010609030c05040c0507021003061e0e01091401060c0f0804060e0423070507080c03070803091204060c02121005010b130816091d03070b040c0806060916110601080a 73
    0x20080c0301030340f09030310440c1002c1c11014680c2d401020341e1f5505034169490500c8104030101500030b440d80d070300850440000040c02079068200e0003024822526610580754041c0d07210003041d8180c51005c0c40b18580c2c4040d210040140034070803009030014501442121003051401c0e5103507040c40c0e00507400382c0006240d03080740c2e8038145054882c0082400b0b00c00001840d50009840f80784c0b086500070006001d1110101d542e2081c003031390038100c44c20702118038240c0c0d80d9907507a450161a581c0081d16108040e2188264540d80100910220360590722251640d03880211079030b00b0800040c49040c88141c150280200c11f10b480001c1c1c0c01158081e0202d458000e80b0384207516220304020101e640b140c02954400100b0841c0c2d4200d142c040006ea8800c44000718919480400d41c2c052070303554103c510304a20000174003d090080204c0c0c014041c911500d60600241e9882000e19590141640c0c400d80c0b003101500412114000411040a113943c0c030b08000c070755800400301150805009034424021a009040b0260 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 175113750 1250 175112500 175112513
    0x1509031e0212030712022706030103080403020f010e030105070906020c03031201140f0901092a050a120e0a080409110301080604030516020409030c0203012a121401060903 75
    0x8540e04403810038095081602000940d184096110340401c1e510020104503180e00c02c0900004c8102180415036481d2000b845503100755a000340310100182445126044900d0305074100c074105c0740c120001c00c0c01c0504580070481350032031100c1c40605101813030200c10241c2c0c41c00c1c003511744101c81c6600c405144c030740750903400707410300841c40d0340c20303109800800a80385440c2075480c0042c19902c0c02240040502615404136090049a0441c140c0c007405000000655005540000051040f0507480e8150350802080050540f11071082c580d01003003041c84642c48040c814941080310008103a0701041051104010f0750400f80e8240060711009000281405400703054001d0315048001c00314070525544c582040d098030743c503021304010108107002622118170000c050f0612001600184200a00101c0e03150240140c510010100e02035401c141030301d405404c00e500c00e50500070300c486001166514684040392968400c0c401d10360240d50f0390102101c0c2d00a43c07070005000e01166201c5c0041c0710705504244 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 175115000 1250 175113750 175113767
    0x200d0e03040623041a0702011205160c0c05090f011a07020d0803063f06010303021c0c0c090614010804030516050a050307030215010e060a090e1510050f0301110f0c030403150903 78
    0x4109d49080000b8130654240417002d900c4800198544011a014240781c00002118035900580e80b1042c0312090000b00d25032040175a0495910089081d921880c0d0540412035000e00007000e0f40c4900203540b5032020400c410019580803a000f400d843c0000c1c01461828448041c065851406100d074541601c1c1540018650390384030510760004040941c0b641e54004d540304001502203036248000c04c00f02f00d0250045d44443ca149074040561b603a480e4940070107500800480c0f02d45464550600b00800055001701c0350307980030790b03090b0390340070702d002107480c0c03030205980d002d0404441522034008000d0110710107001510242c0e1080c0c2c040c251505a4800340350048006800c036200030000c0f1018425a969440c0c0e20310111450b050303010910003038106403d41440901c00302c00008854803002c002c0018031000782c0c0000d446088840303404d41e8041e581498222007202000010704c0d0300800810b80e04901e203001811031040c61404503841d1030785070b07500d1420710034000820820894403411000c3c10190000e501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 175116250 1250 175115000 175115027
    0x11d0d05120403030e10092006120a0506210a1118132108092503150204030f030905030d0809031204020103200d0e03040623041a070201 60
    0x40303400c103480800724800d40507000c0c0004092555611001e558a10140b10000f0f02c018070703290802c4207031031605108681038200380c3c28680d40c41c4447da003102c20340390060695890405001c000f036155964594500000c110191030560701442100c091004d1004407072a840c51641300d000508040c0c010b0780340042c00c2036110b80d58144500010303a01038000300241c10301e60360b004c8202c0d10b0421880e01c90307080402c241025010708420401030203400f203070304030781010798603016119080803901c425040d5040c0080709a01c4d0940c400070868840320070000f1555a00e030300079101c004a50300614150780d981c2c84600c8100149422008246c41000410aa203000c1c032200c4000052800c00070340d039144c8102425124880c0158602c081c500c400041b505592182d4003c0c010410701740c101c024402d404460002082c0c002100c8210352a08210380c0c40c5504030044242c07411141262504140d0701c1c4010124100c0c4001404107180140d818400044c00106921089503501c4140e55441c0ea156414000103010400c034014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 175117500 1250 175116250 175116257
    0x9060d0f05010803090607080d0603140105060f01230705030c030a09080111030103020105090108150909100b030d08010302010503090f03211006090b090402070807081201080604030210051503011d0d 87
    0xd0001ea600e1b04411900d0080c0d00a418607600c1e40107403500070081405800241200c400749a0342c2450280550115008810440d00e103a02121003200450f40c007071500d00700001c4203100c203c0d07000c00c40c0f4150740a01003d03032040c0e003540c0c2030100c1440150b03c0c503000405038a002401c280c6040100840a1041c245000f182d06005403640d811600007030a244149251503040002038030015441c0000700c2d0316100742e40e10060a010031070820082c81951440381c041400c40c42403800b5055100c0b4035000800e500c041180b40c1710320005a10f103030010340d01a08010b0100d00b150090301070001020340c00340000c0c4240568005445410101d520b5800849000206141401580070f0f031b05203d0160000d0341403084803085c1d81015a42e40d01071020601034003802100500845010408008000314000504a5030160705880400c0d0303070362803207159544c81054074090096080340001c0c039030412098000c5c66220b5040301801c1000e00e8628042400c42e011101c484800080c40d031a5050242c0c1c0602264403c1805d615 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 175118750 1250 175117500 175117507
    0x251101180308040509040602120106030b0a08030306030d0f05070c030b01180209130e010908071505062209060e0d020609010c26090a14060a0c0302160b0c09060d0f05010803 76
    0xda0342c002e10b1042d03004581c07003004d5101c0060200000e0343c0480e150500c08118079011540d4640001c1c001d0100c28800600c180b6505001060b8040008240e074440c180050040005240310601a543c458151683c0e404215040001c1404958000d64803c001d41c420900c0140c50340c548048100e0306170340010040841c80c0100f14044c2150b413002c15007000c07156003e8001604030f81c144c000c0c0380140103211000705164404510700301841172202106000d210400004d100555481c01044000140d0a07031030b6441c01c035190034030081301c4403a60000c120140328110020300d000240030903a25100c100708941005031301c94420809051020f000350740744000e590404242d00110b241d6125154050022030084003050800040c0710014104003c00c00030340c00204461880071309002240d103800f0b04031a485809800d000040e001c40f4842d100321040c00d00800d8000d06480c0c110703603a00c8072403036000d008255100818072214080d0b0f507890000784450080220000354040c52145002c081d0348050b40414001c0d001032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 175120000 1250 175118750 175118753
    0x6060a06080411060d110405130b1003022b020a030b01020d05070b2703070b10031a1801050a0e06060f010207060f020a0c03111804020a0b2511011803 66
    0xc0d1081d0020781c481840c0038150041c3c00450114040d142e03404220b1801e048800300c0e10101007000b4401d84005035042d0b4845241540654250b80c0c203001c4041e0401000e5030703154034052003640500b2411401e0b508613035040888032541111400c09074410f2200f55400500340e8165a00b6124912030a0340a001600c2c1c043c50512000d070071805100c0015080103007900010700000f441203000b50001400492400b490069100d071130307640360440ca0341190210401000f1810000802c0303850012a42e005014151240c0e4058401020401c0a030801a20502c81a0310600e015020701407284290041c0000168514a0084c41441d101014103118090b80c04082c03001c429980c04640e040940300c450030211080714100c0f000302c3c07914058500c0030b0b0454000600103c10807a881814100076003003105d03040056144000340c0b00c9542800c0d00d0080d840409888100000e0704190b02520142d850052003484448140140e1980c400007007008881118040c0b183c03200079a0841d41001c0c03c006072515082906065 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 175121250 1250 175120000 175120007
    0x20603070c030210050702030408062206020901020a0b01240e1e1f0807200a0b06031002070c0302030f19020f0d0609110a050f0f0603070c020d1406060a06 68
    0xc0e240c142085803207880c07042818001c10111100c0c0504440c02c00040ca80543c0003500c1e034000c0e006030025802084e02080400e6140046900c1c1c0c0481e00b40d008111b95555507851000b035210710388850560096000c4440441d0000c58441d00902c000134291288450028001e829101d0a49400090148000c50120961505c006046542c840c601e440382130744e440c4000013a4406c9142000700920380440c03c035030130103e83c02808540541c5032030b1101d102025028103c60050901801c090040368001e416080225040c90071003600680301905485034013070b407004001c0603030f480108251603030f2a01890130021828108810301d082d6501c4009454590b04040643c0c048401c02800644164081960400c075a03071380c40340d400301041c0d0004042104003c1d61820f02e40c014852800a446451281e0002a0909110302c003034003180c0000f0301d12840395940900704805a0030140400080040c0c0520b8200103031035404500700c2d07440c01400c881c091002c0e8020010f180503c0109030902a01e8148403c0101c10342 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 175122500 1250 175121250 175121257
    0x111305040f1505090a110a020307060b0f030604020d08040f060905030d0512180c04380d080c0304090e060a11181014040914060402030106050a0807091d0f090601030206 74
    0x2003104c007408641c880c6039a0502500c0000450107840c100013901401d0303a03400000410740d03640710f483c0500c1584046000c002e8020003808038180c040d040f410001d0014a080003e0b82a55442074030f000e800d103515800e50b40c1008445c0d07080800400e1540c0c100f40020715003080281001e03140c0345401460005503111508100d20042c01c0000018100006102c4c004410300440600c1c03a00030300f0400922800c461611981c00341d42070903030180d80c40b80d101400c60300e2212030240c0802c24084d060000b100c4c030650352040300350b0203401c44400c540001d110204c2d0020311809030791034130b5030400c00610381410050540c40444140c40010468101d0400002605550034440481099000c407507174007c3d12800c100503500d500074020f802c0c0d010400010041079144041c1d001040c1341d03001d8035449800760b543c1d409000891200380644000307d0b2085c40f000642d14804c240341a803000280c6006030000e50f480080c20071490b002150241c25030003090802c031504411480c455413022440d4028035040d403641d004540c4622 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 175123750 1250 175122500 175122509
    0xf05100b070809270f07050f090d0c0b040608160c0201080a090204050c030702011a030c150705060412111609050a060e0405030301030b0610080f0406111305040f15 72
    0x4030201d0100d0900001c841034544250b005041e8000c09884508800703013040d41c128407107142c200a00b02089030b081c1c10000b0288078841c152a503516124410710a5003464020182999100300210780038400039415080400c0140002c018842d01c840c2451009441039200a0101700044171650007000450b500010381c01200390203090a0001c0d44407456210007404007104042e42083c10071082c0711940d50442c008511400c1158000c1241c5008e90203034110511b9103015159040d800078280300c0f81c2d0300d8290401c044803003000c0c106500c0c00c582c1c0d59a090500301c1c2100c06480c55a00142c1400b940c0b604200c03040307403590700f0402410130010000e041d20390040490140c05055540d41c2c000a4a83d1030a83c0680041c0018a00200700f52501303117043c6540394400d002c03c4445001c0c00c3c000c19001c1c18000317102401c0c400c2c25295040207075108a913423180c40070000c0040c1d500544a10000200c841944000c1110360b031444000528242080140000c0d03403040145491540e140101c4c10003611010f00c04281500c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 175125000 1250 175123750 175123769
    0x5030f06070f09080604030c05010b03030f070b10030203060411010e060301060c030806060f04030f0c06051c1808040603150b0a0909150e0c0a08010f030b010303050703020f011803030f0510 83
    0x2d4010b600446403881640c100c01c0040c0304500c140424140c009003902c14541c400c0000b8402c6500c00014541c490140c5140070446030810b000640c0010200c9580f643d001c0740301d245464030641e030b94000034980501600c2c25500c1c02c002441001055a07c0311048441c070000365055451035140a800502c1e03450b110101404001200c400324100d99110401c130795200c1600900e9640340d580b28280904c0030484c41c80c0403134100c5580c0600203075480c0180160341a10340341d0f241980440c50303090b09130300c0546680c032135010b00c81d4007c0f040034000482c103402401c083c0015030340004c1d2a0b0300211290742c600c0c42c10707040800c1e180018400018000e510907d00019181c0040e0042520507266500c0300040007141c220404090720541085080c441c1d11011b41282c0f50705a403008441d9030380ea80080a2104507000290030034900100600119000d0b00c02000c4540c480c0c0304603050100a030824908581c42c00440c400c3c0301d510b030340c818024140c0c1402849401c0300c000000b00272900b8144d0101c082105140700701040b4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 175126250 1250 175125000 175125017
    0x3080a0b09131202010e0303180f0a0503040303110c15070201020c01030902060910050706020c1f020a0206061e0409030207090f05130222020301080604150b09010311030f010e1605030f0607 83
    0x7941300703402c040740850101d0b0440e900c2c0c5c10b000c240c0c0381030055013004900080c8151001445a00e20005e144800e02d0380000180d0301c3c241c02e64804540240f035140c4080114803030b4062a98245e1a0f21202030004c540d01076141d5102d1190b8400281050141802141018142440c04c40565292012030b00085001c551450404481001c19070300e80c0601e0340081d101c0303403000c2a15841c070b4402044204001c2e0b0700401c1c0942410000c02450100e0040e8804d103401a400003000030943d050890b403a4a0400a401424055444000004042d911050411001030704171410030040030549000b0048000c40d400c005109a14021601c1000c0c1040140040d00c45c9000c00c400d5040f2601031440a5400751944109650300c0da12421595030310030041d5011038007801a13481281c0d028090b0701c10320740a0b00c0002c0a404c800d91071600c82540c280c1c003180f141d59040c0200003401c480c0460921407003104248a00141ca1072030000a0406c0816241764800c6000340c003ea03003142851480844d80551008040c01d0501c03d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 175127500 1250 175126250 175126283
    0xf0403080a0b010e09040b1f24030b030a060b010906170a110c06010312120527071203090e0a0902010203040618090c1715060711040b03010903080a0b0913 68
    0x107130070300c0043ea900d800c068020b0911061000321001a40301e682e61800620182c441c1171189002c042051050344607601e8072500000ca0031000001802c0001c00f18030340070882c2c610140c00241032030324034881161079550b10690b000e00b558102040303500401c0d007400c0c41254181c0410390040d09580043c074170240c1582d01c07134458884080d10010f075000882c034002151115078480c03400b08803c01042600324042000d86005094020702c600440c0e10840e8010403892200744c4941c0544c42c28a00445a180d26014000000c00c065042140415600d0b0090390b400620710700d400b02885001d10068415285241003660081c0541d0300002141c0403194145040b184486020b5a410301003951a00001c401e141010300c04c41489a00c403c415008202ea1031240c0703401e464074600e104142c0000d00390707503410141c240500c0010502c8414002c000c40390142021a02c446203000003400c42d803442d203088011655040620440c0b695602c50b0b042005026910340005040c5046480f1104001c40c0008007042c000551521 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 175128750 1250 175127500 175127507
    0x5070203012301030317040c12020a09110a110307050a120c05010c0509030f010501050108160521370e1603061a04050103120f09080a0c030b0f0403080a0b01 69
    0x1810500108a242c406a205007440c000304081c8015400a00a1604104c601101852070342c01035138088081c082292070500401c8562000c84000d80e4030142502d000030307203000103001e5070041e0a401803945640782c00c001c401400500e9003a04081d00795100703006580004200184a4001c90340000100c103140451650444804480c2c280c010180c0d42490300c802c01c015000300103000a0705046082d40e552868040149003251824410903000074034200200f5900f503182c8041c150880301c0f5280852a0894a085400555511001900020034900b0800c00100903580b5102d28806807204107510190100522100b42c3d07a4002e0403480f0540d58440280500b00c0812000207031a2a1620707114205590b07041000003406034190600c0981420303202c010241c07034a4031905050b070394802c50b24150501129400c4400000b0003c80c00240080d0100101b8010010040102c0c11842004541d0f082c0e400c51030494101600074161101010402003032000007904404160342c0940504000074100f41502c0048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 175130000 1250 175128750 175128761
    0x60301030305032802120112170a020a060203041b0b0304051b010912060b04060504060513020d09020307170d0509030c010c03020c0a2d050105030a020702031204120311030309030a0507020301 84
    0x4640b0300e04c00d5110114000da840e0064143d5420003001601d0503a69000c0c3c480c07a144c0040002480b01441c02c1ca810030b0b2001c0940507018504503841210040023940c1e4440d0100e91090720251440001007801741991904c100d09007015091114160f429410280c1d01d956580d212400e500b07070300404e15801c040d002d0740b290240b1001001080c41424240c3c1540c10450b005018003800e09020314140480801c0c03504050054000310342018002c8850041c0b10b101040080d04080042e401440d01e4a56a00161794200110400780c20703c45072003044040e502490520f09150444d101c0c090040034032000810303a802281139079903241c0a091011800c0e0103407804070b042c4889070450382d621802d4400c01246840f01d000b0645154407481d20494182c0da03001d0000440402c280c840d04d40014001c1000801d117081e0340d009000c01714030250807074000c40e40200741c080700c7d50401c0d00805500200d0482200c14142d01002e0000c5012003a0091441c500703180503034503280c1c0f08008445050020004102c41191406d5001c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 175131250 1250 175130000 175130041
    0x9012f0d05150f03240c070f05030d0f050402010e1009030804060e010909020f090d05030d06141c0b070c110603010906050a06030204180c1e11190206030103030503 72
    0x40216181081c0c941102c00d109007082800340c1c00e6a0203030990ba080c001800d607038655440442c043c400008001c10102108020a0403402103030070321103034001880c40401303061813070320401c06180c48456010b041c108031207041c01400382c060b00300810f000142c3d80101280c01d000109a9040d003e00401040c01e0720102801d0380000e000c6a00028005045580b054203d102840c0c02d0740d0358101c0035600d20400059009001a0b200000c00800444086141010541c9002841a1b059034186180309004908035081a40052801e08405003102283d2038400211071040c00c108110420122480e240d8130315140009104c1014040740440010034020040c4600800d030b00000c0c00541c0d00c1d030319a80500e0142c8524810742d0f005110b04180811124006c0c0250343c16159480d001940710ba40341050000981041e40a01040c015840001d001616254072644803503c22a198a04c1c201c0040201da490b00704031080d01e015842d035024550b00180d441c0000c50781182d0f01450800d44a4884400004504c22a60207 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 175132500 1250 175131250 175131277
    0x30618010e15010810050d0c09020c03120105060307120c020a0501110d0c1e0c0f0b10050a1a03150103060e10140d0203031603030b06070f0203010509012f 68
    0x1414041c800d801d80c1c4980d08a041c041c0d8154901c40c019103491900307032500d1302985061a002d21a0381899019034800c00c0c045c229800785190b9998102049034019165a502604001074038155050f012010380c0c014101551418a1490300d40c2c001840000803002c0071000396100c2107241500341c800c2041c004003d42080081010b06881d5078421001e61004406c04035a6082464400c840390107144501100501c0720740c141e0310011412801c50750920101c008580301035500d0651400300390100c1a2070b104a15010314120058142000c100002d0f025900200000d4049170701c2200d040d815000303403508500021105015203031114010f070050482c1d600a2954203c101741088185103c94ac00102100c1c0700049a6160000e900180021000040c01c0650150b200708a40c04c1030104a16a00e0340c0c86000746400a516101d020001d0181d900c9480b017611401c1000c02d00d241980340170700c0b98a41061a650003000060401129501c0342c85100c400b00c1e45107041070509052007100101240e078440c26014 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 175133750 1250 175132500 175132549
    0x4060b150a020307050c011b03180e0108060405070f050102032d03161701051020030c01020a0201060b0403030903170f0d0207060b030d0207090c020118031e140f0306 73
    0x10300c000d640b13030813400d01035410307200f01130529502d54000d4403500d000d0480c2040f6150500040d0310140c5d40d107541e41d41410a03c1807000700018620801e1850300e4041d0927064040c040b0380c10142812450542d407500145188a10f5403c104416a00001280d28500d01c080600000402c4900c1018041d4410301d081b0071303034a0000042020700d10800e42c8260034003025851304000b100e4444c1104035648824020300c0c2c1c1140d04407a0400e1b10502a8151480c00c92100c014100c070010396500c0316082d50090b1107504010b030b40200d040c0d1802d03502800303648090501c518969003810714544000305003c0961202421100e0036800b20000344103542c1c121401100c041c1c050b10ba0700c0c000d8003a040c00950040c401920003074500081da0246107004a0b46c002090308a90043c00a281001d1845004003104484042559a122894143ca1134251800951640a0385503c1025440b10003411300c2541400018810403811840c2c5200300603010081d00d4213050800c045a0700c90f0744540110b00c8010043c800100c840d242078 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 175135000 1250 175133750 175133767
    0xd050409090c05030a0809090108060103080a030b06130312110c03070605091206150901090207021e01021906090303111c0515120705040c18031e120f090f0b0304060b15 74
    0x4d000900b11f01e1015201d92501d80e070382d0b40219449180c28000104880380802c507499a00d880b98011a6620034003c0100340390041241e03500c401c40000354400c0ba41071080000d840c44194100c50740d60030340704500002c0c0c0851007841300005c0e12002e40c0e00945040c4980400c20100c40d4855001d549051210202198080d0921008007604c0c400c58600980c031a0141400200e130200d40c600030f6030401940603242e0090051001200301105104035041c2e41184150b2040ea0729000000c048540343c01c2c051440001d003000141001010381c0c1240000e8600c4603008c01504440140b20240c420080560000004d0b480e2180079080340501052080c5d00e81c420000e10102d0462030001c2502001c49404540070002c81c0782c60582542d049401d0422946403000180c000c002280300e40c0c5803144403007020032081d5203503601540c0c0c42d4909088502c0315000588117020030424660004a888084c010303101051404074a0420700380901d120042c002000d480e00d440680a098441c140500140011000d8980e201c00c140c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 175136250 1250 175135000 175135013
    0x60305060118091703240f0409060e120d0b0117071409040f0e0615010507020f03100203090303010e15090a0f06050a09090303051b1207020f2d0d050409090c05030a 72
    0x30341b80128003003519404690685450240025480c2e4050035420802154204010041032082000d480c802d4840032240d116035030a01c06210403034a040e445580712056004054101c03078101c00528140724403d01090801c00103580074640c41440791914401400742031001c190603018010010380c00c2410840700d0841350b0500d8000003071302d2400d9406c903016640d5480c40c011182105d84c29290214904100740b80241c102040b040c0e003d244040c04070744030401451002c00803a841240c142545800100c01031020914030010380d90400941c9035070f8003410108000180c62040040d029041a5503604000284980e60781c01100003007900815907900255120085c0d00a02841e150481c0081e00c3c003000035046111a8840d121020001e212460604060721100102c1c920064400380079171140f0601200789000401c01e103004041c00075402d040da507143c5204d14842c40b801c082c41d18800e0308440c01c103503102c0e0b600400361230860741c500402280042c1c180c10510000e03540e50304119014010101c3c00c9090004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 175137500 1250 175136250 175136257
    0x150904050f041b0b04090b06070506100510030c0503131a041514010f06180306050a0617060f040308060a1d0601020607090e0615040b0c0c01120603050601180917 71
    0x14281c0c0389040043c111024030041c554014845404030900c414841c1e100c03203901422103040054a15132400c1c031191103040c0742c0641220101d41c400140d103002e000a081503405800b103800799080500c1082000b000160090000411056850f000c91601c441409071802c800d03011034040d6036020045061a08000c400003031240046520701e820803820450380c2078481c0050303048a914901e0807280d14100501140c071030594445001c241034240c00080701040079446050300443c6000d100165417860480001c090a004036801141904158100604080300003201da520a50518061003142d4665000511711700d002e80003a50048140407a01c0021110012214040d4900340c00f2501e1540c0e0f01d00c411a41000d030341c090444190303040ca01040d03d03414080b82c92422041550315a6003480d441d41481490303900100300444a907030040402140303d5030820b4601d200c140072910280051400c58840ea5030340c80040c0302c0c0b09150440c00a007020510f90540c400b408056120440d200007a40100701407032141c0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 175138750 1250 175137500 175137503
    0x40605060c1b0d0804050d0501060b0a090f060c080702040e01021b101103040312200a020102070b0a060510080402040f02131809111207050913060b090103050705150904050f04 77
    0x81c902018100b151424415541d201940a891145014240024043d48124400040f609992a031030040394595444001d040401c0040d80c4000001c1c0c6040304803520700701c0d590b01c6081800080020b400103d0344075003c555465806490206158a2007020540203108203039107145007003011440203d4120000c9001c004050140c20140700d5040d01d02204001071106803070040c04101410300282c814449500040c02c07c280c0d1105944400c1c004501e0031501d80d02010100c00180d47c00140f040c10080c50740c00039500442c41c024208072560415022502060012814106008409001030300710364a82e0003103070000840c031600350f44910111450103081c0b00c80703000300c207109540b0032201740e03c626003841883c2050360402294860020b0180621000114202450750240500080490b194454091b03880c0a4034100a2002241d426420131108803107004402502c01e2100200410100d4000515041030b81d20403150031070081e01118492900b4820300c030f6001e810600341810000218112195140b00d81d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 175140000 1250 175138750 175138783
    0x40f23040606030f1103070503160c020603040b090f01090512070203010f060f05120a081e070b100f121104050601050c010e0307030807020102071205092103071101050406080411040605060c 83
    0x102e99401005400340402c40d07c0c180010780510000c2e264a200100c1901e801201e820501015040c580100b8070a520032a020b4917038074030300070900c0510141089000d0792800c601d0001c10100303456586542d00c400303001556112200010403110107540d0298040002107000e080e0400c8081da803000114099502d5101b184e00c10281c0482c24906104003044203e034041d0310819140c6041c42118012000952007071074001c880005000410006048207140c40c0100c40304070b404801c041c61300000060941464000484c8480d017000c0c810002051110017040480d012070b0045202d50325080100d03400d001e481d5504440d5030914131410141c40c2c011000300540345c0a691482e0701303903980150590a03403056900041c19460920301c9441d003944190090030303140b00700030104248c040c0850420030340c040010220f80b109810001d008000c1007030146880404003002e0904608251030008094280c4000500c041d04224640704a8011a0b41e1503101001800c0c000f4403007500d5103c004111036450300d4200384a81c04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 175141250 1250 175140000 175140011
    0xe0f0105180c03150105060f070b091509030405060f0912030a0503040201090518060f3c090403090605070317040302060621121303140d030c05040f23040606030f 71
    0x350705010958840802138140041c4a903441c0030f090101e10380c090304c005040b060041c054100000c1d07800456500644401009040211007540540d50001d8003405800949d4400c0008109549902003901c4c50801031095049e201c103a16004211402400c90802c0030500001901c00720864001000d540500e0007aa1030510658031401071007001403c01803800012003000c0c0c000348003442c0a0400d18004130380600503208a180b1001040a2004401c0c080203503c01c0e90f03070980700045e6080d80b0401134000d04450a400c1420180c501501da28554080c440409c0340010b458820305000c0c038030720040d03c050a6805001441c09042c000d48808050313a105114040000d481400d40107065459039115403101c3c05031000314078100186a9650000d680943e0307200b00800008081030400031100610b110f030101400c5070410111005048510044c080000c0c4403091000f0305c1000c140260304407ea0300501540344c090000c08c60040d140c40c181686a55200d41400310103d132141c1d05400404604001c842d0602c40c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 175142500 1250 175141250 175141273
    0x50d080a1205060a09050a09200427020d080c10020a02190809040b011e0521011215140106030c0908070e0403051b0109050105041101021f0e0f010518 66
    0x546006440083e44400d045006211761806507203e640c02c840c0207080010318400b50358036000103101003079042100054000c20701003641858090f19144240c0c00c89680d51f041144503040e403204100180c00b900a1221041541c10030200d281140c0f59903a01e801101c200c268203014040103540031010907001805903400d50710640b400e000c0043c81d000d502100081c20b00302c0010502c070080134001280e50411000d141c81d0005003040d501c441941840740c0c1d0316940c0d1012003188803200981f0500c482d80400d41080c0042020300545201010303110343c85500750101041000f01031002d000802c48101030b030303544032000041054241d400400d03507100e5500e44141c29556692002d8a0300300c60700c242c40a5110010000d4002032150005100090800320407656202540350710f00d0854080c42c8017104e02d41c2d95407050005001251040d00042d003402d10042a070980b20320b24010044406c010300d030f034080b0b03111842e10f10110320502030310755040181e10003001141b5009081600301821200212010300883e901080d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 175143750 1250 175142500 175142537
    0x100e010506040e0f0601030809190906030224040605070303020720010207090c02030306120102070515010504201804060530031303150b06030a0203090d020105160513050d080a 77
    0x1141d101300381003d0441c0b03a20355280c00004da4488a1020f034058500400260414000031410028016181000621908603c184555509501000c24107040d081a110b11148242d0040b117051314064504540c40c2c152a1906a01034002d514000b00030340898901c030b55003d507211320740142c2c2070000d900b125221a42d8401e0340c421140c20038022030041c1c20800002d5190708080f1141200201c2d2440010314020075511060b042605954144240d00b240c0801000245894028445803050300c88400000b5040c014070403165205c1d0100c0c260301d1242d101070010b00c680c1e0307581c0000002c00b0054002d9402c500070500382c01780c83c90b004603145800b415540005202041c00015900c89601c3c4c5034147c10310b0b80c1951107491943e4600740c0b51840c9151204080700c500d888120246000c0c0c0c403001c3e0050f80320305009003410704040c4401008021a85000e040001c81480e03c02c900d07550f403034903081207540c40c0c90350052584220a1074010981080d41461100108803000703009204184040c1c0d942c21686040b1380b141c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 175145000 1250 175143750 175143763
    0x5040e1516020a0f0c050d08270d0b0406060b0a02030d051e0402090c2101140d030203030a09080712020f100c090306050a0b032e02030c1902100e010506040e 69
    0x1c0d005030700c441c1d0b400000400100d0310803c41801031071400619655100060450400307000300725001030b40894a01a80558507220542000008056000900310b450205000a0900602030241c03030060001c201803020380c0d404030010f003201d101c1301540c030444c503880a0b50340e51100310025091071034000040c10800d2440000d854000100c06189503d0b121034080012480000d4510b20344202c040160680881000b486000002a6004108260761604010011508160000c0303405008051103000010f0390120840e540300340790590008600c030710750415031114026030318000c100d040c00c41c1c07030250003036000103510b882c04d00003804079060700c0300300300c011001d0700c0391402e2840c0842c2401c00180b0000c0d049400c840d0780a001c10000081101c4008006803038001d05600515039840c1e2404030850a0002140c2c55821000e405015455030820100000c51840381048e84404690040d420003980c1d44280500a100c0540d09030900242101c0b0344000d00904007901d019105503e411082a803078000420308 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 175146250 1250 175145000 175145041
    0x150103021602010804170310030b0109050f0a02130302031005010e01080f100203040809040c21020a02070315020c0304030605010e0709060c0308152101050c03062805040e15 76
    0x207018481503a00549100300e02910444580380e80420b02c41d120100c04010f1031040ea81415400400c51a60602e8190b822060704500040b50414040001d19900560100c0c0c0054204d030300183d40340002c05c60200c14210540000b5414040c81603042503a081d00c4e007080381a2000b44080022990b680c03905a940d69502189291483c4c0020308844400c00142d409142d10501800345203160a03245030000d0b040361105411540844c205407032039a0038048440c003402d05518120000c618004008002039601d0b2000d200080044111031a24641080243c040d03501c468204421280c41c2d940342d2030050094042401280c00700c0302032400041805216880080443c0c01546a1040c48102510102c6608400810080c03000625414043c003d440b5480a041403140300c0c0c1141c81c0056031104440d094840203880d40407a440d007403082c44030a9484080c207807400510000c1481414400003101601d003002948510340c40303440e0a05c4000310607000b082034001c02070403c030040502d9599081d804096030b00c0456 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 175147500 1250 175146250 175146277
    0x605030609070e010f0507060f0504030507061514090408040f0806151e01030f092f03060403171b04030f030e1813050708030c01060e15030d030b21030315010302 71
    0x90788031041b40503d0041060f03d01074070010070f8004580c20000e003520030681d81180002c600007a00302c14091130b803007001c00c1101124034030455145460202d20020035031141c1948101c1c10140400d0400c90120304540c0101900d810b906100ba59800d0603548590f0b0846000b00084450402000c540c41c0c510140c40c20f48070050b001c0d4032a408100c004500130003036110914040c6542d141c0c0f4034046889801c0040780c1014107961035030240303400c240000782004885003080c000d9100105000000ba00481c221580c003001c400890300030354900b807410f0b012800c0701c000740500c0380d40003c0201c144821424024800350194658400d4200d02e40140001d8030b9201d40ba8003e19003414000c502c403000360001c4c1200c001e00a50840b052140c54040c0f450440e8001002c400c100ea5646c481000381d0f43c280404103a10418006c1c2c280c10450b807210110342c0320700040c100441003669600c590004c9a507103820341c0c1d01c1c062407a00d2406601c80310358580c5031343e580300340e4440d5095151800c10150a40c401c1c02103882d007105940c1e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 175148750 1250 175147500 175147517
    0x70512030415080a0b13021e040b0405060f04090603030c1205090307140604090f05010f27022104060903110109020102030414011b06090b0c0c03031611070605030609070e01 76
    0x890440f0704450280010441548039001140e1a40d540802451060060b2174010380d2214010504490121103142c0005110028403041010000c0c100681d000ca400980e4402d035108541000203e00f40324980100758080d1600f00c0100900d5400300141002c40d02c01c0d041100300310940041600c81d8001d891810350f055000b000244140341c440350701801c0000014059074200741c2c41c0c054510640d201a5082e4031415a03400c010800c0e8019420000002c240c00000003100e106d050110030010800c12004819603038000600c4031140c0c92081c0d0400030f800f0446202c0840b800d003803034400050041c252050f00081c240d0340c413040c0c50100612a40d603850358140c0013140f402c0c4c40e0151029000410079000c9040c00134006006c040c0052041440c000c0d24811040010400c8552070031441d40040505104c040c2c100a0061107100140003003101d401032422a6103000607081c03a002101d0450010b00f41d00200d000d1090000380440e0010055400390f03108032041c0f00303503a407403010032500c0700854440f030b60008164a = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 175150000 1250 175148750 175148789
    0x50702030d14040801140a14010b0f0304020d060603082109030a08040501020405030607020f01050c030402012c131d030c030a080702120a080f0f060a0b090607020405090705120304 79
    0x607400c0403440440244076608060744c60001900310b82401204110340248603041050882882c402c441400c140b00460034060750402c80380d6074040c0542e00d8408007401b80080890b0540d65014010185264807603424485152240380c0180030780c001000390200c0780c02041d03103c04081c0d00024010700c16036102c4005e505104455a0480d00c0001c090002d6a03c2c6d5400c12010078151000c1c000350344148103540040440d11003041e00942100d4004006c02c4252a0600034400141c0c3c2c4603180c0108505604403103800c646804007900148a00211101da0000000121410441d00794201d051800d00003620b0720041d07a82100b05903243e2040e070f000d00201e900100650b10855010300400ca0300042d0b1441200c1910144260b04125036000c09429808640702008000b20b24140d48002c0d075020407611160f4143d8100840402c4400d01d40d0300030300f208210080b0324000980c540d481603c030303040c1d002041404182031a210241d11003201d401114051301000902d07814a8000101300c400300c0d08500c2c81d0002005a2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 175151250 1250 175150000 175150007
    0x7141f0e01050a050c0a1103161a070213090b060a120b04120c080c0303040c06020a0c0b031306090f020301110c06070815030105270f0c0616150912050702030d 70
    0x819400400e02c44c2c10701195090300700400c0700a6400e48140e0a1400441040c0101751a084a503008801d410780e86440030311650f030408095440304e40801d05625140c400380e20006e101c1d1680080140e004500d020b008909015a60b20b01c640a640c003500d80100303054440020004044101001528510031000410002843c40410b051156680d10b00681480d009a8031116207034800355510714980d0000c000d0200f407040c030807000f40042905c0c1c0001d0080c002103030344170f80001d0710074030030070f00300400200c006010078420201c40c40c031203a4810300030054900b6525001560500d1240d00368025860141c4440741701d030307201d011600c00900610040c015543ca0368002c8428540040510b6402d82d0464244803450b182402036a025516401d0081031a11064801c0700802c032212080802d954000400315800010120b090100fa0409035400d560b01d00e0451800700d40c50200c1d140003404040c0002c0b04440c1d003400d0780d00c0800075030310445500c000c2d89804202200c940c050014040d45c503170041d1510ba19074901 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 175152500 1250 175151250 175151257
    0x10c0b06061e123102091902040305030c06090a0c031407030209040b070f0e0d08031003021008040b0109090c06030b03011b09050108060907090501080709050307141f0e0105 76
    0x1402410700b480c1e82003400303045241d420a900566440c1c14207000d008941d244410ba1180c140940d40c4000922490010f04800501c00c1c54000390080100d100825801e0324604694040100d030340c0e8040d5135640d92454000e0b500c0d40426036a04481c092240403131041c40001c50141c121030341042c4106a283e04507101e086000d00d04ca8104107213072080c080e0000058554136803240c401c5014080a12040c50f0042002d0601c4440041490070002c5000440b403032650766601c2001c070340350401d0066480343d0f503181200c003800392203420107944942603112030049641c0c03114403a407045118000390b42059980d8584d003030658905c5600280f5901c041941031042d20301c41c0e4400191040c0003800401d508811401e052101000e4000e4003000a000030001d100b1560002c22490704840d054407000d580b840e1070700c8020443e14290040b0b5041140003408902c1c0303580b086202102801d001410b8130311040e964650001c0f0200070626071401884c80511540c04505c03101d0050030a118a9210070741c61920000c01100ca0b40d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 175153750 1250 175152500 175152517
    0x1507060b041518061d070522060c0605060d051b011713051603020d020108070203090a080705010e01020f190c0816240e010509040915020304020f09070f05070c0b0307020c01030b010c0b0606 83
    0x60f090b080305400c481d2034a40320004051545450360032b40201d041800039110001d0a8038001d01d100c0001d040000c00004075098030303e89003600303504c250032079500488002d84c03101400c10700c056803a424040c00754208415105442d225804481d003100003c0c0c500550280030f48000b0354003080381c0b11428091350141c03580343e5004400740b0550380b511741020002250059140c000003466445008180f21558001d070140795505424002003000b0040001c92a0741c0789810000403912020307440c64001040420424500905004070913241e0804210100c1e040f046454801c800c104041b082d01c1c0e01c10310303025040f0905103000a030340359a40400f212005450aa22065525030400c0e55060080c000c41c2d04810140d445071b050f0300015130789007018010044000045d1100b588074440715400c0c0010b00e5009002d00142389011305046ea207400b241d06000d05800d015500108a02e1400400c1107207441d80417429011000c0242c80800c48200307440c1c011500751702c0c0e0080041003100301030046003091804402421514 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 175155000 1250 175153750 175153777
    0x6090b09091b01051c0c11070609050a17030c060a0209031905031206030c040c03090227010e041109010603051e01060207060507170f0d0501051507060b041518061d0705 74
    0x600308180000311010f20078006c00164803202050b4404030284401070040019282410715142020001034801c1010311030914040604c2282c0854031100f0710680d00500b60704000e60340300c0c2c54005c812001035406131036564401d0007103020286400070303601a41718010342c000c3d000710b0409644518081c0001e20280c0a42c0c0d040c401c04034102c440766107600844030b4a1450790350104407030034a4818000b006000e0107100748000c543e40e40c0004002210b61080b411a4129141c5140c3c540742c5080008564448070040e54201031118000b040e2150990450340c09100f008400400e40b011700e29132009031910030f004410043c0c0000c0300030440d07180306801030154139006d040c07526029881318a140c4215440281c1201c080785000c140c1e0050079016100e1107004020999080030300800101580314284607012000300b101d075403100c016020751281d42c0003031136610704100328100841c0c4035030784070304003c035031031680e00c0700c10f06104001c58845e11421080400c0d04501c04216255110740b0f4050b9050b401c02d06246005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 175156250 1250 175155000 175155037
    0x60601020706051c11040801021b0304080a0b070302120a020c15220809030109060b0108180d032703050301090b010e10050702060d0c080a11090108010e130606090b09091b0105 77
    0x82041c205d0040c4000c010300340c001030b0768260480d00d02d101380b103044e0245101c0381c209000c100800180800d4025249031301002c140302596918000f60000d019180c0400a845618020002c890003960300038074440f103d070b400f00e5410304e10100e121086004105d0740c0000c5403460404684c0c4c0c0b0014260300401350ba1180220703a0a28201c2400300f03007122400842900d074030351a05041c814550308980701c0c075003000074545100c100c3c4001a605035560112901103c003015174a0514803a071003401a001c00d0340c030b2031804c2c1c0c10901d01568200200640c2081c000c0324036162510101004640c01048010543c90300545005e5100d103805c00d06075900c0d0040301069810403030070012000e03202c5851040303504002041c1c1300c0c1c144600788842140201c03480001c1c040c0d450642001400410f030b81000c509030440703020190183c40307a654041a07180d0b11445580050003c0d04144c0b02240b0280682c03c4800c41c1503027540c0100c07440d6903180481d942d41880d03003102ca0b40420400c400c002e40b5441a4000c000c40d0030740f0b4010a00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 175157500 1250 175156250 175156271
    0x10020a020a11100e090604140f160804050714060408030c010c020613020307032003030c0706080c0301030506060f03010609020408100e06010b0d0b0f100c0209010608220f0c1205060601020706051c 86
    0x71a48101c9d11400722515510421030f16007403152941461000900d040c0140e4942076554942c1c580450041d40901c4000703407510f0907141d4410b41110041d0a0343c2c4151398585102c250100c0c060444821010094060740d0b000a031140c111102d5012030f10b8000300100241c525544403017240f130b003070703401c002030b400d012401c4038005a1403c000402c96035010000070950a031901300e0040000d200a007510004440c104010404102d00080c41e540004003102c541d40c0d1031880500103401402660f01c900013590001c0350000d0700c1000800d18890601603200203200100d508201d00d1340b151003d00841010403800d001d160034402441d80318401c00b020203050840d40300105400645a040607a61030303000038603404000c40031801e0884101d801030011341829400340c103014001c203e80c40c018592003050700215a01d000244030400b00b95607900d07a000311312110510344400380071514a8020b034058603d40300310408600c1a520016012007103408a50300c1605020480905a101d09440c090805440d40c403200a5803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 175158750 1250 175157500 175157531
    0x30c0d03111203040503070c06030507080601111e07051c021c0602070c0f06030c020601030201021f110307030207050d0809121606050106020105100503240910020a020a11100e090604 80
    0x140901d025900035910703244546401c82340c0c01c031184c0102e8201403e200903c01182d41080f1600c1e00320009003007003001c0ea110b8088162034034441150141c0c01241e65160000800004203410050314016901100700350b40c0720343c0181500d112140c0c000c0d081111100041c400b088110740c1081ca0310300c10b8801525080c45074a62240c01c1c0300c903030000f08080c81e91076001c1124a4241c030810b41324a1050024055643c59500080c0d00c50b81c3c01240380081c2e03580003621a500348042e90080050f0422244250f4490500c4400207000b034000001c00ca400d8425401f00d050301c01c1c043c2d2901072285820500a01d0f07800c1880c62003695a0308118107800c07881101500c00000200c0d00c1c0074550291849900000706031801d91002c1b80040e074a5030043d400394115a000250f8040c00640340e0f02c0c4200d001410a03455180c6400c03403860450300c00d215002c10b91001c100c451070b0702c0c6e001c10035000450084d5a40c628825100b0200100840955a80000301d50405121442800d1102c51036a01c400014400a440d040001010b07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 175160000 1250 175158750 175158757
    0x4060b061c0204261002031504020301140f03210927150d0206070b101a040f15120b0a050d0c0e070e0102030f07060b150304050705030c0d031112 64
    0x31a030715000702e824000c001c140f41c0e502c3c050012038454100000c5400e031050351202d03c5100e04512050700000040c10010010003410898000500110740da5a5500100d04568400700e4003240301d09140d00b403d000d2460001080441035103242004002092040c1b86c03020154000180305400216a01d050304865a5000347c8001c44024812003041c2071402039221102c40725154141482800082030301d0026032140400d81d1001c550001840031141c5490311810600c003815407005030040180c03050316001c00b4140015004481c0c4443d08080d0050300e400f02c207140344801903145000944208102400c84070140c102558103400a403502c1000394440001c03442d2800308501c155424407d242d4100201c105014003554030854900d0060341c4c0442c0500001d48070f218070500e0007a44c1001162000c1030151036440040445002030041480d1880200c003d00184c1080b10165064002d0500009142c200402c800e1070b00e03203006012030740c1a4111b503010340d10085044244043c511414107805003800851005 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 175161250 1250 175160000 175160047
    0xb0403030809010c090b0a050f1b0a060509031e07060f0203090d1106060306010302011112030f06190506040909050f010c02030714010c09090513050d030609180b04060b06 75
    0x891074246414418182901c065031135400403c03410b0602041903030007000c00d90301024450300c0c1155a4600034892050300340542a249039414101e42400e00c0041400612403480c140714a8041c403295640e42000f54903401440050b4004520414240c900301060350020400144a040c00103030111501c901031080740c0040f03403500132079405242500625078001400001030f410304402003031145000800b103030302d60300e0610000f03051141d50090003415820601c14004078a00594225450749070661089410240c144c0d001800380d00b02c0c58403d13132900c54140714002601e002502d0b581c5050b1a16a01800070404aa4240c880d070180115415003014207004804807011960700940d01c608140c01c024050111080343c105a9070f00d007040000c0a42e0b0000c4214085a601201c00542650f840c80304807640c1d0800d4200524601a4884000b0f035190180e0145007500d09543d401c00c0302280d034036030121072045003600c05000380f10044002400104190410322034030030040c10a60402c0102c41240c00d42e00c140d1143c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 175162500 1250 175161250 175161257
    0xb0d060c030c1202040b04050111031b0106061e0905130207170405030d17040609020402040801020a17011715040c0312030c030c03020a211d0a060b060910030e070b040303 75
    0x55804940354028241442a02c00c032008500d05840c00401395518480c911580d2705000308100805401d042c00c6c415142400030701100380200c0628551050b00130300c1d02e4020200400c0040c1a401c21201c5c2842240343c4400b89a2148100c0e503050008120700074046407040c51941e5001c000307400000b448254800c01032200040401d8030f450400041506000b244008071041240c0c80b1481d02100d031045500700d410580008001604150a00205000c2d01c5039070440c10036580005228805658028030400301e20500401049460740c0758142d6040a0101c59a440c00c9680003250074407140800c5d80c441c60700300d032140d040210555501c1d0b0790040a2100020400c0121741d94154400500750940107003a41418035250440c9007108038140648a8500d034651084902c0c0302d4402c041c003446013a4089105600d900c61104008104180d16a0b6a28850f8908441031410b1260101090070003409a6800080c01040c01c0400254118228010500c003c85032110744686040001c080c401c420060000d0340c041e0781c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 175163750 1250 175162500 175162511
    0x40803160b090a1707030201150b07050f030a0c061d150a06060f090306020c010b06040b091201020a05030f040f1e0201030b01021203071d03070b071a010b0304060b0d060c03 76
    0x80c0000c00600040442c402600900d100b0070014221106107040d850351038030480d17252041d40c14100e00510b54003030260502c41c48400041124441c500c0500340c001c0c030a50032070341410344482d072454070307409580c0c191804205104400c00005a958014503840c5207106802080b05185086040c07030040c54030300240711848500140b0100707030414050070700076000c1e508180d9154541c0b01c400426a107114400a041142d0225030600c00b5082900100c0701316000904072512503844a8103008158071a1141c640304007801d40403580320040600a40d06181348030340300d85045696812510000100041c82202c5c3c0d003491043d0310001801d11280600c4100309c00b5010100d0b103403148005001c80e0024020503040d03501004041e45590035100c02c5a41c4001e252400010884002503d02403826083c0701590380341c050450082180c0920314060b0044a0244034003800020b10181c1c00c922100080c00398001691042001401189464108441050014041040546c007036158003085076074200e803c0d400651100c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 175165000 1250 175163750 175163753
    0x40305071a040b0705070f0210020601090609140402040b12061e0c0306090c1b03030c03101a0d050c04031505091209030a0204050408070206130504050a0212070e0604080316 76
    0x10381e041d414011140c072501c0d061584500191101c024012000c10030002014002c010101e120908002e41c081e0a407010320b10040000383d2948424018554054600800014090594040c04c2248000300c80c084005803119003c1c8005007050010054002c41c414440081ca15000c00a841c07041c0c1d50112100700c08120100b074000c900c1009814400f102c2000d00620880d036030344034602500a0039005101d0380e1608402c1c1c9841b0100c0e00200154074a020110401c80039025560080d445486042413240e601c503103501c1d8a215507100048444000e0006002001900443d176101c2a0410500c0e102141415a00e541380d20f00d100d04883c90302d54198030340c01404502c0b84c0801c164408100f2401e034450802c0417903004655540c00b9480c0c06407080d5160350102d020302545070100d0302d51540240001c0e9407950440c5809082120502c10707180510311b040e000401c911480e10035196200d8000110000c180c0341d0800480702d00c08a1600140d101c4000c00000440d020304000800610340c00714941540c9a429 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 175166250 1250 175165000 175165013
    0x5040302041d0c1201060b040608060301050a11041509150e010e150d020d14180705100c110a08250f15110c06040620010903050409020f0d0504030507 66
    0x2c410411140104032002e00d4148030210b071603105a0802ea548000248218100394050803581d44400c3d41c24200260104815501580c001d01c15041a0000d101c06d40301d030b2850408480518100d00456401484180495500700020302d42c0c9190318600762090540302c650661005190000040125001c803401d00c030a560403c10b0310741c032800c0c2120799019103000d58100b100f00b8810650b407140300c280d001a008aa02040d41d100007190120790103481c0707592503c12260241d01d42181128000d80c4108800080c552500340210111010140e452200c0d082e0143c0e03035440540220009207600c014100c20100310803204105040c0340d10306001020700e029078400b142070380100694100490a540f400414448048a110074214118051400e86204101600c0941c24010100d625640c4802d000400290065100807940c1c00c81c4003c13009410380000340c3d441107003240d1540b0b40050103e5400d00c410070240304164080c080c0c41c07544101580c90b03c0b2141c000361003280c50031030741100412000f1400d1001e00c0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 175167500 1250 175166250 175166261
    0x10b04180302011b140a18090506030709110f0c012319060b041a040914040201142a15090609060108120d0902040902030a0c090c0903030c11030a120504030204 70
    0xc041221481d02400350b00085ca58804415102c40548001030700d8044540b00340494041001407600032040d55807505217a0b400b80406681040c402c5c480e0890110320103101c1d1141c40c41949004421354a0858120240030303040e00300c82030380c0d5040e5681c0c04609840320b01c8001c9150100728039403004881c42c40e10488071400b01e4495100b4008083c6021010721070858103c00312401c0c0c894049552071049000c224070f83c00e911460300605985c50170803810320441914030710118040c41c0300340c8841c0001c400200da056114001d2a200036411181c2188100c40592019000250014032030181c0d8460301c20310040402580c07081e40c401d100340c0e0151003040304003401400400d01512906011344180102d80a0609041c02011440401c0903034030103031101103503200e6201c6402158080c0c207960900c9141d0a0100202c403030752040d400018108034182c002c15110b094400300f540e5164031000700c26602d41c1c8410422941c0c00c2e0301e45425104841100d07000c80c6400381180190302447e03581310f0b5502e0a61061000751390 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 175168750 1250 175167500 175167521
    0xf0c041506050706090c1e090b0f0906100210090804080f070602030f16060f0b0120070605180402121906030b070809100f020414090402030a02010c0302010b0418030201 74
    0x300485414805590b10500b11085640c0000d80455121a01e061005200c2c0240d4800c3d98106141d103090f0301003103103403015401120fa800c842001090b5111041c001007404940656511040c17140004025182c0910402c0d00d0b80380c280f044440c1d0040e220f6051084401e8408181e64001c0d02090801803000100095540b840c42d4070080c0294518021002c0d5036030046100c0301016a0b0302240d030011134680403041c1645160001d0b018840f03c9440c10351280204100c410320390001e00d40444400e5404100402ca13000b0441030b000410f00140f0340300048541d034000202e05d003201c00c141844150595500e00150808040c02c1c0c68180e01d03800c0c1703002e00c0b2001840c0d800c641c508035420144104007091b00c410a46a001c0c0e40b40c1440042c582e83d03952a00e0910303400512140c0e0340c510f00b64456081e03041a41c003030b0090328411200f070360350a421401000303080c280c00c075002541948124260783c0103500c26514030407401d06c03a00020584501c403c0c0000d003034545400300f001620207640c001c00145582400b03128840d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 175170000 1250 175168750 175168781
    0x210030608010b030114160c02130903120504031d030c0612060a32061209010614120a030e01090b0a0210140708010608091e030406020706090e01120f02030f0c04 71
    0x88080305501541c0346c5e002091003103030308100c00c80c2c204440c0c058411030b00b203250b0082480f03000b2041511020018900804107900096580c00001c03011401d51003180e0003990151200c1050784607201080407022140e1245540502401124800382c0d100e0102504a1540300b000c1000207140c80b0b410b00c80e501c05164005000c1801d42c06510400c3d080c030100b5031040d0104800e9840b000c5d103458000c10700a21038500c0307040d43c94010b9010408105410340c00402a04e4040003007000e144001000c010130455080c07402c3c080d90300305a0a07140080e00404011040340410305011140719070f202e440800c2500501100340142c1c2007650b110100d1007242c411217440f02954a805e903c1130070580b000404884050003100180210303180400e840b840d08018204142d003a0203504040c41100c2c489982e140c0e08940f0400d0701500c1214404100103000c0d000300070544107a081c41040c582e20b0300c0014800043e4200043e640d06580e54100d20250b1030070f100c00c0b8020241e0000802c0125404c100f40700072680740ca000d40303814 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 175171250 1250 175170000 175170011
    0xc0f07051002120d0903030902190509011502031c06030f0f02040b04141302131805060601140f070206040b0f1216020d140c010903020d0311090f0105160210030608010b0301 76
    0x8281c03030000740c4418803113100d00010324280524081d030007001807841c0a54480f8240b1040190313811007032810029038005560034078003641e8481d0701c851850381d804903882c0543c02c144126900402d0140d40e0445e260580c00021030900d50b26241ea1001e0407034460141d541c01d42804691040d818180610030750600242d60401901804074803139914540084c000f036102c14501d031541c0055542d40c480710440024030100030000b401d0b40000c02d452140301c961080329140914000140598000c28113100442c40645503c0e107404032007070316400264030490003241e20140c1480049500f28030900602400400b0f081780c16070380c850407000603550210040070024400c2d075000300d00408590200e51001c1d00c469505000c46081e02e0482d04010724000d0300840201c66107030000c5a8103050740010000882030b80d80e2401c004c40403015150401c18460703c1541074100c5c42c41c03c000c002a51046004141140c4003803041d145040e055030000b01d000c01000c0043d000240c03580f01c148149031081c410300e41504000c800030401e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 175172500 1250 175171250 175171273
    0x1104030c060e0d0b15030601050301020304020603040219091d010f0605010e010c080f07080a1202030105011d01210b0a08010e19081308101d06011a0c0f07051002 71
    0x44503000c034090801004940740c1411015103c40c980303d820f0341d9100f04c500ba5a0315000d0b8000700181c0380905014401d03c02e11000240c5800c040c0300300c0e0302035900036081c2c0349980c2e101d07000c0c090b818a0f1030000348030259005d1400601a510b03880ba40709001050500812401203024080f4295410140380320400e6142c030a0821150ba0001d155041641080c2072403c1c260420703080402c1a8015a09003202a00700028507c0400502c0801001c00451a4403400480c2c0959151003080b4002400740d035002c6030780c0c01500710364000522604400e82c80145403005c0000c0120a101c26150496030030175504540f2001001418985401444040c02c0c00d00000c0000031041c0c0032047d03440d06041c003c50341c0c01001010100c20b1110074002c48040081103c24102003035a1200700d59a6101c003450a0805036140204122450740000c448200c1910000020a00c03a400c0200c80701005d00c1000c5d208455901c20014520709000c01e00520b40c5811548011b45101490a0140f000c0201d0051003d41150170514041c43e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 175173750 1250 175172500 175172513
    0x41410241409040b060102030904020c03030105030712050d20101a3a0804080604021903020d0308180a080304050d020c0d0f030903020604140f010306060c0b0901090209160201110403 80
    0x80d405900500002004e440e03a00c01030341140301d270824690b041800002c43c0c851300000040118100e170700680440310510340d6814016180f429101004050341c10407013a82c2c00443c8070b4200d1011030607010b410612041c1c84040002d1501c5100f0483e4803540d43c40340c0c00c080701c5508141d6000d110003815940e640d03807a00349900c0440321510911859034407400100d40e40210701d480d00200514961b01207100d80d40d49032076450403680c1e0242103904900c9181106001c40d90841250320b0a02101c2c5d020b08808051000f55600b5511850010880303644400d0545c042ca5103a007040182c4004107016404050b92410b203820101d040c800100c5c02e2405544c0062102c20641d1580200216450740240300c4604c032008034901181c5126140c3e101941c03208021401140b0302c12400c2c046000301c04200c0f488090b5844120040d400d407401e502c01d100109800321540c0e0041861040d000360b100a04900014a8401c0b0354001122942c00b07071072008421440300c0f0010242502440ba600c001c0e0205200c5a003803030314550303628 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 175175000 1250 175173750 175173769
    0x20c060d09060e0f0c01140903010c120c03090803060108180601060323160c050f1c030b030105090d0c060b0a09051008070302030c010302210106030c02240414102414 73
    0x10380c10462201451f0356085c5011050705c6030a840140284010141d440004211410351416600c10600c0c2000781c8034058000d10400b99503581c04a2407500310b41c0d13003c00544069000512007440c01408940851040e081402042e01800b041d880010319114691022100e40955560b21603d8014070001d001c110b40c5a110703e0b030178400d21842c043e4039440304c038a45a410700c003032411005503512078071610101018080b03e400c1c61010305550704006000260741090309942c019038400059400c20000070944602c030303040410100c0d02409011817060f40b010f0228551541540c81003005a40ea5014416402801c100c03610042c000302004000e86400c540001e17441d1482c2d035142d94181a0300060200b000f00581030740540d804451000d009c020b40c0d4918014029103214012000140210a6020134925411640314859951015055403d5445558103280480e44c95004046403040400401c07002d0401d00030000c115910316901c0c200c020761000507910b1407104e50408805030301c41c18604296921509001e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 175176250 1250 175175000 175175023
    0x81006031707080c0307060c0807080f01051003060308181503010f09021317060601030e15011203110303010b0c060703020903030a18050d0609140102070302030d0c020c060d09060e0f 80
    0x2107503a50700c101c0c54882d00c10b00c0703000014a4240808944501404101d90019813a0421900ca520b00c0d9a1481000c07150064126031005c4c1300c414010040c400c03030402c1c8001c0445001c0c94100000d40e070ba200c1d140d80c2d00e42d41001c511402404500d80c2c01c1e0305a41007079010507035942c00c5a80024219414503404400f1a402d900401088a5021a82040c01922003814100803e00040d4040709010a03081c0341e03442d50000c440391b034080380c100307094002441c0000a0009540012034400d440b240d0a11040c01325184850409500b04551600f04c000e45010a1004500905850824950310b00204108500b40079008160505152051250803803584002c02210039080952034008030107802c0d540c100e2451201904510382100c408082142040182d5024581c50341c041d0150b4464002d200c0000c40c284d2241d000c2c01401604144502c40b0340040b260042c5050617218010703550002c40900100301c103608072001090015844403450000c0c001944500340e07452001c48042c05041404096140c0d541032540328 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 175177500 1250 175176250 175176293
    0x1e05010b1c0309060c080d090807210f12020403080a120c14071e050601080f1b01020a0f05010b0d0804180605010e27070203041d01030b0703020a0507060c0908100603 73
    0x11000c011b901012120795640d1013404200e04a51400c01c03035295000514116a040c096117409180307411a8000c18221512a41d200480031a100204541018144146100b5640c09100104c00111014041d04045415641e021444480804280c0540e10000700c880c003481840c581c500020000170044400c500d8110b40b040140e00000d92100c501c00300804e001801c9801204000b00702c240c400b182c02000712000d64100d41a032000c51355102003101241448a000d80d0100c110307000011000c80ea80c4203c2e85c0907000014440b550800030540c2d4400c4000c08503242c41c40000d05003c4202102411441c04c403202004010710707802e001c0041c080e49100004144907108141d041c0c2a59100000300314280318402d005950b15040c08440650340703821078003404a00c17102060484205030301d040e1425040b01e801c030060707030305075183d9600030350082d800006400100f010800001021883c14010301c070350b00c81c2503582c00190901d0100c119040a401c0e01055420341e00f0300b6020004035404000d00302e1310154680 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 175178750 1250 175177500 175177517
    0xa03090c092a0806061b010507050310081b01030b280f0602032a030c010204090f0c1e030504060902030a0b0f0a020c03121f090b010318030512041e05010b1c030906 72
    0x661ba030790840605120301965801c01d42088112a809400365010700c0c883c00c5001c9840d80c41d010340070b803940740240e1040140900c10302e03560b00c1c66109801a404500000c1c0c040600c1c1d100310201c070810020140c0014401c010440c0b808c0150721520940380c0700415a0f44040e5080210f40c013038855001800f40381000310640082c081d2402d41c90280300702e0310508183c0d002150303150364512031000641042c1c488003e8540c6880300303100d481c80c0100d400100024801d401e29458802002c0142c000b024040c07c182c2e44955100a000c1c0140c03800c004c0c03088114000d00391114140340c07a01c40411000001840744090700e005110307501d2008000402d444030b41c00500c075031082c1c655555040440301140f0000390b10180701d408100240e0129190321244102c02c0070780e4103001c80403044503180c42240443d40000c0015604200020100306a11440c0d40c101d0300c41d07072440113200c4c1e201c1400c1ca02186580401d4070165540c001441e0a890062182401d04049001e80090400da945010b000c081281c0708407401d100001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 175179856 1106 175178750 175178767
    0xf090b0108010b0d05130b0c0903100606020307150b09280203041106090a030b0907050321040e0a021e04260c060a03090c092a080606 59
    0x4034001450004d6410112005100c018010b059101405104000207112a040781d401082d02010721600c64191600b09410a200703000305240944c5091000c00c05250044240c030311032500007240469070015034a02c240500481c000b01503001280c07800304400000841c017410115500c1151811100004a00305012880140d030050b025076802c4035813000c149000801009022005000c0c2d51019a40350703100d0305d4240e01520180c0c000c0c0c10001042c40039003010440900800200c40c041c14680c09144102404d80c0300d54000d0341c40011040e000654190181d4049031241c602104141c162401504d426103244d8004c0d0182192122000c09000b40551202c000d14408548110281000e10b1035101045060340c0052000c400707154a510144001c80d03200700804c1c00501c0310714004181500d0907900e20440c0502590442100c1c03804035a12000d09070f112007050761003401610141d50b0369402c1c = true := by decide +kernel

theorem cover : BRFrame.Cov 175000000 175179856 := by
  have h0 := BRFrame.cov_init 175000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 175000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 175000000 ≤ n) (h2 : n < 175179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
