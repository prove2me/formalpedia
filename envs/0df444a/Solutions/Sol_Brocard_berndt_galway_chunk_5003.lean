-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5003
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:25:54.973593+00:00
-- url     : https://prove2.me/submissions/c6d61e19-b78d-4c56-9857-30da6320ccb9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 899640287 ≤ n < 899820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 899641537 1250 899640287 899640293
    0x304084218071d0c0703140703051312060c2a03030f020409020318010b010509060d1b030e010c08011802131d01060806091e0c0906070b010519180216 66
    0x1010040d00101401540610324071010f0020000f580e81c01441140d0280c034290541d41c005001b03001c401242c1d040e0a4001c510081058043d005691004103d038001e0101c25955140c0300004013234070300703042e141246030004458110b440781d400d0b220713405803101180300d025400500c0c003480101584410340070075589040354000d9103000e0005000401304c2d02030158407400e1640d01d24034403800128a10301d032603160149074040359030880309480180380100d6900d40c6039442c0c0381131b80c00a4803613003440e0b02d01c18081c034411420039601507101402000707240c4020000802443c1090311401c4085c01582d034001d24400000200410a400070b02c810425480032241c410b030b907480c007086115843e41c1d050724a0782444005200e582e44c490103107031384600c2c2140c4040c154105102d01c080c4200160100d04000381814000592a001380e500300d41641c0d0014007829500c0c01d290803c4581807200b0b0080360300c00c9141c0700c0f4a410303041e00388014105131950074500e0580090300015840003588619542c41501350746c03ea4a02c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 899642787 1250 899641537 899641543
    0x140108030c0c010203070f022b0b041214160819020d0215060d02090603010605060d0207020306010f150822050102070302060121030e030c030304084218 67
    0x8015600055803a1114000d0321030501140d85000303411980107200b40d8012403001c603040702d240354041c0c1c0c070420041c000c454400e1006400000d020505040d5545220402509180d02446240100340090350540d8007481110a50442d00717092402070800c2c05050341c820b00c1e90700d49040851103000032516008030300c041c1c0003102d8100003e0401507000020840c0c881501800380100e008410350041d41d203468011b00081c0b2981000d400a40684071a40c0011030b140c80075800b04028200007030106444000b511001006940282c1040f4086d01a0303000002d10790082d0200034058480c03410500b100801d440b04100c80d00740c4010a106045601c2411410800b10f40c2c82d40b04103d2401000050b80d5555642400b03458400f042e4010500781805092900160080100d40461103502d8030300325001d150540c0000f4509500080d011b03030300d40400900091840c03c000b80d610b022004900d04404140b01c45850525011090594601040b46284090940c4145003600d01c1d80008859031491030340c03240102c0180f03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 899644037 1250 899642787 899642789
    0x806190807090216140304061d0a1712031003150b0f0105070c0510030e011404030e150d02032503020909070f1205010806191505150c0604050a11010309030f05030a1401 74
    0x20742c2c6d401c0003405000b95984010100e000b00d6212341c10b10f030a801508046140d0700424070800308100040480054004414072492920b1100f0400072616401e00303659466010202d071000300c07250a508c1800405501c85401494101c3c40700500704101d440d40103005407450b40c8520310032500c0c0c403901e10380445e8035651013540509650042e80d0005004407200301007801c6901261036003012000c4a020400000d0b40724024500220041e242f40310300c036255118566080c09070a0b0b4800d402400402004940c1e0155504180340401ea00b031140d00410703140c007042d0128400c1106141e00040e076030b40021481d03405406018510400391030209135042c841e085036006c490342a041540c454011100340700307506d178240d03c40c0b90640c480d400c400c00c8400144c0d080c2030104076041c440c0174001c2e0001412840701c20100025201c3d8005142c042e109185414541152150414182214000d1100c10124180d500c603114a00d40507901d80c480c12803034180b0300415a03003030700024481c050f00e036140c5007070840181c072002c0114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 899645287 1250 899644037 899644073
    0x6070201050a0b010c020906041a04020301090902010e0a1a0a0e030105070804020109050109050306180f120705070b27040b0a170c0321030c07120806190807090216 72
    0x14480c1440300120007610b1414005034100302d50f600a03040960340d16208548c001200300c40000b07440c00358071018085034082c140400e03440740c80030000295480640c0c0200c504a4400d80e90201d80e10a41c80070000304012501600c012a00700205416034501810010603246409007040100703041d5110000e42580e000301c5682d00001e404405000840d604944644040c003000d0900c2d44030b190030140800e944540060400c245a10741580810101034140412500300e48140140c9222100c4141e0603031040c2d01c04202110207118040340024882483d03c240e0301415200c03007120900b0400c1e9050394064180750460f2550056071038120060682c2c070340c000c2a0040148415440c03c21880d071480031304002d144694580030307800500b40b0b1440f50118031a6417100e040c44100d0ba903181d8a0b8590a5a01d900940da00144080e85415803001d80c26008020720b441a04120f0310344c0388240d0100c423001c104100034861003000c1d61107500140030009081d00509942c14019007680443e03000c80c1c58900560302c0c03107000c0c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 899646537 1250 899645287 899645291
    0x3020f040b1e0c03340302061b03160806030c090a0903090e150d21120b0d030207051e04090b041a04051c051309061409010806180304030506070201 65
    0x46048001d07060410b0408101a801107802e115446a0b900e0712881840c000042c02010100640c90f56413101d42c40c40d08401c4100e0003202c0c06851444c0c06036032031030261400000000c070304004080e0005020100c0348182001e4030030466005c00c001081d1901c000c06803000b40d042c041c0c800032280e41d49444000600c104441d610105943c1501d0074060403828507500882d40c01d01c502c2d41040303200002d038512b55200303038400d0702e810031082c6036414940d90a20354000c525080c1001e0741d19090235254060020036218062200c00c201220409040008441e40514001c001d03801400d001c00a0b0f28000120311034150180220148c0c0d0302d1400001001c9603840501103c5500c0798400384401d01c1540010020003c0d95200503035120309043d02e815954079654220350090f040d442e2005054a1301c41c400f03980f08030601143d4541015226040e14000d05418003aa50844441c2800e0114501c0d05590860494901c480a80a10340b203000c00302c12408035a0440381e90ba407104200000c0050420400c1d54800e0010380c0c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 899647787 1250 899646537 899646547
    0x5090909070f151215090b06090a12021c0602040e180706050310090603050f1905060a110706050f091915020c01020f07050d1206051c02040e0d02030702030f03040602190303020f040b 80
    0xf000c6c04441c0c0d4080d081d40262070511a0300110384490a40070207030344244036546094074249c40000c5507000b1899190307c6544401c00c8110803c000d980140c0156030040c00146a6a5521200141c010102c240041d003036910030300c410002d881c00385000f55003002d400040071945546031040c8205458440c0c0c02141c640d8000801030304010020300075070750040e0440f40000352440a5448055031918050720740c26202c0d070348840c403d10b0582c124040340c40345580b180007030096182092410301903010449039101031b4000c030008500c02d02505180d13406901d5000905030181102c1500c100003c1d005000c18070810f41d820852041e0442c1c001c000360903403d110700000d2620642c44d5070000d148001980075649981d0611400707101c0e5955080c02d003039040c042c00546d21043d85103400007802810415280031020300699100c1502d1030381c0400280a5503000780e00300c4150304199403145070380340f08912076080140c0140315443d4200207a48071404205020b40340150901d01c8020b8458080e0b44140d004030401d010000e5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 899649037 1250 899647787 899647799
    0x2415030a0b103b090d05030a060518040201020d0f300915110a09030609060f020f04080c0f0d030f020a050613031803150b030f0102070305090909070f151215 69
    0x701000e03004551155400071420981381d200d035102e4590001c1c0e000e01c04040000b0b10000c4059008000404008184032000140810500100c02d41a40c083c1e0050040e104c912002a0003800e400404005680d1001c4003000d81d0450110000e04820700d10a00c5c51010103c6154460725000d048000c500401c00e410781180c0c5448100c04641c0130840e800041401800215080780c0c0280c9060100e981002010a4030079052070090000c001d035090030500c4a20108111012040b040301400684018904440300c1000602c200540b01c2070841035650b216500c076034014002886039680e603038001c2c100c6c0115060301400d0381d251410700100715991350601e14142c0c8a1420306501400b107440306d50a401e241c40141d800c40d01c0f62100f01c180d202d030745030040b502c524124155450400c00c80350342c0d44841c0001c5442d41c2161400410640c81004aa8440c204640100340c9005d07011030311000b16140720143e103d03250302c1d01e40c0441c0b5425001c8450000e015451195882e080824081c02c01007402c01620040240c2c1829 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 899650287 1250 899649037 899649119
    0x306150e03070602060c0d0507260105040c03110d0e1c1706060304050d0807021002120609010e070e010f050910020706020607030e0c040e0106082415030a0b10 70
    0x640030b001194170160a0250080f81e100c11141005616903000c500c555035604c050322035040c0155080c100f900703000300401b446c2d10410204c0c0e050750000c40f800d008805010000320203917182100c803100031440810070103184c802194000e1903c8046103064072003c56000e2440403101c80c0322540c00c0c0c04141e441500c0c0a179104c072080d8440d4410011145603003507051984400da07541149520100500c4420030124003098001c110055100c8074040040d0340d01c3c4681c074041c203036080043d1651070040c84000000301d4120740034031100e80300305010b603203042c50400310100440e0703c40500013600c42845010440c81c0c045442c2d4440820784601e168004103e0b0b1031805000034904a030052040c410503203040c000c2812154080b82111070324108541c0881e8649124080500400003a40020103502c40c950604051031803040303000d2181181e150008000d95031342000c2c036500c07440c1100141d61540011460b034001580001509401800c0450001951915541c00e14070000c0e410a1620341e0f03540301e21141c1c2040900c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 899651537 1250 899650287 899650289
    0x90f03080c07060c05030a0309020f151801020307120302030c040e0403020c1207260f06100f050405060d06020d0609050a14010504150303110f060a14072d0306150e0307 74
    0x41c81c0195840013107172036482c3c0781d008058084c820036071505c41c00f406560718000403000380c00c0010800070400c260105448602c1c1d01c034001c002340110100034451503660011055030750710360f009403064820010213074040303000f98001422510085010300c8041000041070062511a034401d0300180000c00b5031204103d5801c0203608202680d078080241030003074240f40c0702c1107101c00c0c8044003000701442031801c01505080e81c421a112b41c0380f1948042194202c4001c00341c40440e402c1401d9131403920744940500c0140c0324110741841e08407407003000c04800a0020390080c0307007900e040c0000142c4540c0b80d071f480405031032080e200c0300d400c81c0d00d4403020740310340084850441c0103120403a000c1200000c6070700c0b11441c1d00072911000c0d081c4508481807000c07404080c8401e000350000d032000c1d5002403074146a84401000c03a18100303031300210503800050000c1e00401c0e0018035840350700c00d011507036481006046c0d54110982441e004040d1110000205119040303005014a4203e445442c100754480c01403502d08282 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 899652787 1250 899651537 899651549
    0x6110a051621050304060c0303021204390b0702190e19090512030915130606150c083105040b09040f030f03140f0108010501091e0c090f03080c07 64
    0x4104500b00007800081101c00300c9485003081c0c0e400d590107050981c002d01865010007603c114010401081206094001ca400200c003044110004400c1c0c501d800300c888815484407401040e0042032101c2e110b01070260050310310080c404401503060303240440e28540b561b80700c3c290342d21a5500703004903003982c1c5403081d000e103900c18003c0001565907120175030f4a180c030f40c60142d0904400804559098814013250111084c032040b00d61180c03c01e6415111540881801a54000d14102021410494003080c0381ea281d0000d03941c3d2005003070131351546242903102c400c00ca1b540f90103070102c821000301d4000a40c0070345160440040c0c41c480c5000188419107200300101c074803c141c2601007100113014081e40146407500340c58040e440c0782000000f81d0081881c0e004140a512100003080760803481e891915060703400d240024006039aa0300c1248094404401200c000d081c418011002944201d40c01a078140189142880a03207070f4074018900515500d400c240d40003800001d014000300c404024601c01420 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 899654037 1250 899652787 899652839
    0x102010c0c03080411042903010507090806062211071101020d051b0c1818062703130f140f0906040207140105070302070501110901050406110a0516 65
    0x9140c0d0b4000340740d1800148004c0032004141154481c07526254000707201c6240d035084e19003840b21a00070980f10080b0b0f10184510a60030300740040e940c188501000c204441000300201404e840d03003410403c10210405244c0040c1400501409402040f0b004010b010404002c07025a180100e0408000b02000140c603103041d54401c55080407455840030442c4c062040c58104007100242000c8114100114404900e034041d00f41a21a0145440340c041980580381200382042c00c00c20380c0c40e20588805046560388101004440078082c19800b07030068159408030381303003a6481e00c800c40c1040d20144400c1d4204070b0b014503521806010740301c041c907402984044211040300c1c11010800000d6080702004100340e0242e038001c82c1010030401000c48581007404110003d010500d04440018002d42049000f07445030343c00c090300340c400540c07448212158007606075a00391038a401d20a0544052108203403111041c4a02c60303403034010a078140003040c9074490089951121615008102007034140504070850552 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 899655287 1250 899654037 899654057
    0x200124090207031709070317031504050411040c020c0301181202070b0f0c03070f03050903100e0303150d0c033918090b0f01031a100e041416050102010c 67
    0x80e000048813801d0a104008000e003545c2d5001820300b46444c5a000410705c04034000d602c40741040c2640030b0b62158901c8402c0103c2c9810180070002901c1c802d96025000c6c0c3c0c075002007010780f820b25402044d030799042070045444051380000402d00311070b1602e203240002c0e543d40c0116005c11100c5022030320314851510041041d24200b600c60105c5116010600f1208900058110a56101802510901d07038116000414038a05e5042c00b81c00390744401d5505d0310038000c074001d0211140480c81224002c0007039100850960b600c04080780741e14100c08016592000d4500c490760b0000c0c48942951001e140304000054001c8180840c0310a24050043c80c200c00c40b01e4540d0031034010400c5400b540c200d0f00102e0409030410b00790314a080c010044541c000d8202d4070100304111a851480b03010504036445818045801c0303141c013030100580d000035104060f1804120300100301cac6080f000c003142e401c41d0140002282c041030041185180c440c980712401390048840c2000c00c8951703020f201d050000700711420640a04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 899656537 1250 899655287 899655293
    0xe030403050c0f150a0201060906120f0f05011104030f0605060a0e1b250b010803070201121a040912090621021e13030c140a06200124090207 62
    0x10740b58140d07801e01400049442070344550303480601c0c80c54210301107052941e55142c0741d4024040d00c024001c8009090400d500003540300782114a2410b043d422a045030740b44210b9540b0382e888190132610540c0c05648408a100b160a480c80080c03001b035120340003051107150145040c400740e41c4010310700c40c8503000c0c00c2c074104100c16440174125441040d4041030302520004a180c51001e001761103405c0c07903104c0002c0c05004c10704070311844103603058000c611b4000145ea80e00c50305561381c455500028002004401800101c0c4010f80100e00440f101102074110080140d0100302140c0040744142c99807038404c145018217030303044845900900802c3c64080c248101c1400100206190329180c100a55030001300e00800c0107030f0100d180000009000e05a948101d00c03600007040080038082038480884041c800500101945900c485690b005441e20311054541030b8161040700b03650640984c8241c006003003070b906560a210b03c3c4d514000040603940c8c9148141002064000d0a0700300b84c0c880c0f0710400100000c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 899657787 1250 899656537 899656543
    0x40f23090411090405011d0309090c0c0309191d0411030a0201050306061810080403020d020615120c04110c010e06061e0310020c060703050c090906150c061303030e03040305 76
    0xb4070080c2c500e44000d8407203203085801440011080c02c2441207607410056060340101c000e0100740300c200c900b000760391580314200805200d80203c541c1d140d442040120414144030b040c0c0f0401c031007990380c215801c03580c0d000c3c0a443c031101026001051980c503004c100400411850400200106038001c060980d05580040e04512000e810b292052201044040201c035005c505802c17885005084159540d4000d88041c040002c2510100c015014806420b040640700042c00c0d8460030f22081c1c01c542441c1c640c010702c00c08210304c0084a1031030007264080000ea44480c064030007041c52102c2960394403c4100000da08569000610510301d0f008082402102d03566007030380310a210f043d5505000c0c0049840c0010b858000196142d4400034008030740c8100107070010698a12403d0562800e1003140c0d110b000b0500c961041414882d801441600030801c00e0038500b0160341141c0d803c64095280c5060388888030315180341140c013184000c0040310764004055060090302e076801148001182030a003556200c82e2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 899659037 1250 899657787 899657813
    0x1c0c0606140d1401180f0309120b1306020903010207050a03020105010f350d08161115101e05030c0103060b040b03070c0c0602010b0f011416020303040f230904 70
    0x124038121140d00304030115081d031004452210700178010103c01c0141c60900c9100e0f1000d0b0044e40890103005000440d070120615400d01c01d6409216480b207a0b64030007038206a000d05a00944295509012960b0b2503242480203009240c00380000345100111480d0081c25600160444240c0c1001c0e580100102c24601302d41d43c1f4100c5070005089107030901c002c104c2294040c480c0c0207840e284a208180d0a90320b4005080034091510300c0741e0a006032040680503038055020f01c5200c8403d40c00200d0303418506c40003100c0ba40d0000070301c4900820f0140c0c2e480f2003105c0745608001c0341821103015602049940303803c2042c01c92100003800c051110b14580600445580260301c46e01d0030b040380000c00541c80700e1240c14000841d560003911000c03141d450b003c000f0b0003440692080340c090600904807800541c0111510916107103215100c5d440c00c0ca8450005518901e51002281c040c07206000208107000d18201d0600a07221122030030210380c070020018141700a26100d414000c0c02c10100384030100f45060130000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 899660287 1250 899659037 899659043
    0x30b0d03050f121003200108040308070903020303270a050d03120b09010b0a030c110613020a0f24030e120307050d060b1b012702031c0c0606140d 64
    0x542c4840580300d07000503510803482c500d008042d0036001c100301c409800c14204292400351403100160f00140c0b01c5006032260510029000c070700c0c410000703400244280501c0d544482079141494886540b035000c2860354000b0a1580705030f40004e0002440c03041c5291000c60b10f07a0301103500c030459600c2c002c0172918401003010042d0803c03896045000840c1d0250b00a042c48550280c0494020740e55001c0e007880e60f401541c0b000d400241003032500d1b50503070311625281c66001d510101601c00c0b03480350903131003070800e070541022a009500c1d89000240c0d5190040030354014032254500c80003088108400380c402441c09445001458944000484010000165007035102c1501250566980f540340701500c1d103010342c440c80030b41c1e82d05000000c500801d004c00034240d61011940307801c1042c400c100b8011700340c44800302c0c50041c003e80b0510130280c1c04450804c50782c0090028054030940d858030900e0128080c00c001860002c82c000552180c00c0201900c503030070081c03055103000000d0002d04c070009076071419011009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 899661537 1250 899660287 899660297
    0x90c100216091d1615050304150e0106080114010f06050304050601031101120f0c0311160f0f05030a180b040312200703030e0f0603010303051b0c040e1507030b0d03 72
    0xc0f1400c00342d08a803030420241070032140c04841100070083e0034034481c01081d0049180c80a103c0744640600e05a9005a42c0003500008400c50882404002c12203000f040d482c5648032800010307500420700c1103001c512400414a2819030604640070003c0043e5444101001020410400401c9001c2070460649600100c1d444140c0310050040b01d1042680e00201400b0f8034103203a11601c40c419034001d48040010b0f4600b440f403041021040c9115005001040140b00191300c021030001d07065104880c0b6240c420803421101c6001c6468a9265810400310040400c0e604544034210321640c0000074010f0950130101c614013415039850700107034500e005205051160802510300202e51002c0c940b40301040700c0080f43c1059030b5a040080c815100010841d010304e07490f007540b6280d814000c00700e07810384e40c254841c0ba02c0c1c0b20920b608240100e02c2001c0c2500c680c00341ca48103001e80c0d03655010303900d002c1e21031070014042449000100003d09a010b0004410705141c8442400c168550301c1d00c44240d280c03d4145 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 899662787 1250 899661537 899661551
    0x103050c0f01050a181a1b030405030703030309050a060203040c03110405060105040e15060a031505060c03091c291501020c1507080a02030a11010c0504050f0409050105090c10021609 80
    0x51705a404a68003c404004501186424002d05000140c01c00705203840040d0342c460b14100d20943c0740e124a0040c103400d0340110038103002280c0a600010b40c140d204038200c685038003144d20750710100e17002a00c007241e4602c0d41c45410070500c06001e081d2101d94108031403c0040f82401070003c2c2c1184102c5c402c0c10324900c0740b1000105c076000001c03d2400800305c0030b4480c0d40d481c01d500030020010706a00c05505a000d51040c0b010a85041201c1560b4804802d070008600c0c6c0313070701402004201554069035800d2404002a042c000605c8000031080200580d0840003070248000480c05074a48000d083c0440c4106042d2581d10580e030010f40540d041a09a9030000040d241580c51043d5200301400078280d1400011121000d6900100400c1d90b5545c3d966030080d401000101e46090710440d0b00b140d40010418007040c041883c02070350134107400b0750052000544411030f0b611103003594012500c51100760040c1400c00300c0e44c10318004007440d840d0701e071000e0600c400340540581d450303205901446070055604c0309 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 899664037 1250 899662787 899662817
    0x1d06010c0209090105010501170f07181a03072a11271803042909131d161e121101021c0c06110d0c03050103050c0f01050a 54
    0x468a908660058990b040500d002c81c0294040c10081c45024001070076886103020301c4007803007415401007801222140d034603250040704a030000c4403100005000c24801000148205031f805c84051210f094001c10744d01d0749071a51015050101000d0085c00b081100e0b960300800007066000c550381980e029415100702c10481c0e01141c0104a070800010b54210300d10904100c4000d40e105540c0700e803004000589210428544c142d0702d80c02103108010340c0c241c0714041410307264000b900740203072081580e81041c144059100050741d202e038007140600400c8d5171b542c03410b10103640711081c0e030400c0c440b004001c0803011301e2003860500884091007109594285000c0ca0603542d6080700b000d40007800d40800c024141e280d00e06000e2002c24a4517411070140c42282d10b00100740c001c080d45140c40b210a6200c1081c0450707291142e4019000e00201190524401c2003140004a13040c03007482c1c41e28429a8000a031507040d46030a0385084507e0030384a205004110300407500380e07405001c03956124010700d00301691901d882c0c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 899665287 1250 899664037 899664047
    0x1906050303122703071101110607080c120f09010b0f060d02130b07240506090f042609010314090a15020c0a0303020c0c0904150207050c190509070203041d0601 70
    0x44003410070f588215946110400e0000c0940343c024001c1e1603e4598158107001521644100c10840b515a001900080c0c5001d000b20310362680945403100851400d000000e1080a036032045035200e00c410025404d106c2000003d01c900b0f03500c41c00a4500b14114000780d80007c0ea94050b9001100034160000303150b0300804000c54910008050400d1b02d143c940341b241c9030202d1018040c11042d80c4480009030070ba001002c0d80d00849008690192a0503059110600b90f4803200710000d0003a1460342110001c02e10341030103405401d4001c00380c01b880540340d429620004050b610007054091071440d444060140b01075010070714100d110783c00400c158036800b0700745a00d0080d000c0c907550b010050260889040038075030960000c0001c001140c00384c1d045030705400200300140c002510f014107005400014005c0c500119801004418010011036024020440004100441004807100d100c25000c408200304d05110640076000030450001e542081c2c20101c02801c46201c11403001d84075465007010540c90790040c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 899666537 1250 899665287 899665321
    0x609150f130903080a020301030f030503180708011b020a0c06030e1e0c040605090708060f190b071202151f03020d0609020f010504060c0605060423190605030312 71
    0xd8415015410a85880401001c1100064004c0ba1403440080d05400c00380c421a81030b01c2d1700900c041d03403154a6450444054100034039141ea0409012120500900304208400c0100b542c40300220b40b0110400301120a0710305079001a082d036004141c88400590004010b03c15078044e468006a42c000911040f80750610100c0d84c000c480050801042c0f2940c00422890088042590240817003030b682c0c07041c0a8450421161500040d80c80c1020446524240c80310340d4100744010040b400018900d140d00e4030401466000c0d446807480051030340300300445220400d042e1401c90000c1c0a8200c0e001d4411148200000c14103100035248030104401080d0320b401c014003554002e0846c050321901850304000910050009034491010a02c1a9801c1e42c4a60200c8041d908242d841151441d002d03641c42018003030142200d9805034440540c107019140f0083c2440d403000040b14891480c1c00c020880011a5079000070300006035080410901c0700c0e8400000b2154a1611020850007507a11030349071021103121 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 899667787 1250 899666537 899666539
    0x117070e010308030709140306060d1b080703021903050d0c0611160c230103151d070f0c0807020105130506041401090806010518040602070f0c031101080609150f 71
    0x1200300120510000d8805035205c0c40150321241c241c05d403910340316400700c405003502c29855440100065130b2420a098503024290bc01c1c544043d03001c106180090710300c6101e8111007001e5100c101c0410540c82c101a0b03213011404405503c540c20350464031055225003a02c0c080c0f000344960121401e04121299104850204000103560703252441045080540803410805440104410300086120707a500c0f183e60040101181911030f11299200040d005400a500c0b64103071040e5207c400109000d001c000f40030032240d0a81c1c0d0700114600f0303640281c09800c0388542e080811030107400034000513400c80100c80c007460302400d02a40300c600010100d040d1051582099802520100d800100d00740302c080030b21410242600d881d40c02d981c58035403941e5224170912030550310481d240b4800c404194813003001070f04603000c0d41000d2725122441d102c000003040c0a5004880c00c1100d81020402d200100b4a01c040d81c00003441c04020604200000a4140d04060540350f034441101d6244161070b80c4100710b0500940f4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 899669037 1250 899667787 899667809
    0xc0f06040b0f0d020712111c0e0d060f09031205060a0909050f0a0b01080d0327080c0d050405090901020910110a05100c0207050d0305180f06030a0e070b0909011707 72
    0x485103010840400700c80304d583c0c04a015035030180c00d0301001146005c52342e48509185c08040100c80307000c07561042c83c80b054942041c0c0910740480890828064205c0c0c050804501090340030440c13030024128061241e000007000e2030402407280695820060700200e1741e001d0310114220025041c1141400413a04140340c0a03c0b50b8040e5004010b568000d242c12104040180c1c2c40024109a0030741c160388900b0040d0038206410a159a10030f10b050880c10605405080d001e0b0070203110051851600700c4408408000c2940850100154684640150f600c01c206800a504007804500414001100b084080c400d1000d02000200442c0c4104000800c164100b01100c8000d0001c201000081c9801c0681c0d5006000d82030021036a414580e4000301441c0d810740e2500d1034030080442c007810303030032081f240c180e44280860341d45c02803030f90f0780c0f4040d41c0101e01e42c1a0018048500c0105d41d440e00d5460380c01280702d020207000c00c5040d80d88803001141120107080d12141c5400c0707980324042c01c1c42c0c043d400032581c0c03035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 899670287 1250 899669037 899669047
    0x40b0703032013030b090307021c1b0605092b0213020910111c020d050a0201021317070f0f0504020906041d040302010b01080f24040c0309050c0f06040b0f0d02 70
    0xc180c150345401280c0c091590300c845d58a4045405440c1e110350340020350072000d141107100001d2952034490401d5401402d850030b00c00c40c04c801880d40301c01c1591004001590105012401d4035014840e0100710540281800220b90326605109005801e00006032166668000d40a400701658045520071500100440020000400042c2005a220003a009144140c1c1e00d509484030f01000125020002a00180041c840d0303020100c846074841880c80c8115502400301d400e14070030785142070028000d0941c8a5003507448240c0000e05e02001076200705111101240c08001004082d4034140949505660140e900d40b08040494210322a0b58060041c0c004146100c422807000781e0b88160045204e980240650400c00d0011140f44009861800300720b10003401040035154440260f100e2a158800620221000b102c00101241c0c0000031010210340c6a0001100b0004144608800610100e80104070a6001c2c1c010403440d014074018420080000070f940c000300c181141c152407a591950006540e24 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 899671537 1250 899670287 899670307
    0x203060903040612020c033018060702010606080c0a050c0615090109050714160506100f0506192f0c010e04020910080612010f061703040b07030320 65
    0x182c0d0180c440c0d0303000035603010700c001c006002a0089070000c110b000300540c20070703c240380110008005480d0302c488216070f03410340421000ca0f0500c1c03688156810b40c02810302c04502c50001c0d04024000301007400b1a45059020710440780c2069045030040e0300300e035030030b616842c612006035074074440c052201c19184541d2080010031541c40c00e1103800d04c1030540350b003045641e843d042d1406031901601c414011070b00c03c2c0c0d0b01c0910000400007518a06001c0e041c40d40d400b03540f5484042c1000001e640c00958829a104284034800103100070347e0080c40c082c0c2d000c80c034005401800d8401c104c81070070400b082110220103000c140c2c052007a45c03032501d54800301340034805502144c042e548003900305810303000c9251031105010b03d02e094800d0700d00102e8064128542198154011180300000a005540c403080c8401d4071a4600340920404148403040d0703c0000d50380d4245010f0030320700d41c25200c0850303150340108001d1200c0d20500c025960340031b51500380868503c01185404980f18140f04207001100c0c1e0200b602081 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 899672787 1250 899671537 899671543
    0x207030b131115030604090c091409160608062421070329060c0109030804020a0b090102030714100c03230105060901050c151f050d0c091802030609 65
    0x401c034421030503101e60004035000d02600840f1403503128003800043c00050850304258001c10000e5110382c0400102c6600c07600c00500729008000021342c3c4490100400c003418108001d80607103585003090f025072a500c0c02d0801480304200800e0a03000fa08068840c080e2480c441048100c500f01800c2810b844503c0314003010b03280401c0000181c036002501c00480c44d014028828040c0d841c2c180000301a410140015010200c112100c0080d0045c0040220562810b02849541c550a1003540d5001b00c5040c6030042010481c02c41d0060140785400f0026500b05a030000b04555105601c00760103a04c46a43c60307201c50400c0c134800c038040d200b0350600700750b0070382c1591603882090f6130b02c0c484820710010c11880702000e408040c240111900014100140800c0f5030065000d850705440503022540002202203040344d9880054420510030061060505003002000700782202401e1305035580701404581d501c6140e03600155226103480c5a40d251260404903224030400883c1075006000c40d4441d090a66a9590f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 899674037 1250 899672787 899672821
    0xf0118030306060305190c020a0813240807080921040305100516050f13080105091203060906040507020307020d052a0d060507050715050a230103030e010207030b 71
    0x100003031030070b4400704001c1d00910136176024660008410174644000c542550050100341c0c0400194403a817408200000c2c1600d00400c5a01e586288a840e10b614100103c501103581100c422201c60100c1d800060a5a0082c5803e60110040c50020319030340355005007038142069640510ba94081c041c20842ca03444140d0010000c80e84a40220303a0207884c500541012114140c42984545400400c8a8002803260000c0c103030305500058002c2c45c0080d031044403108030a0a034400b42450351690104070420500340041507031203407245a40c614614150b0b000034103060001b00851302c500ea036a00803401261082050315019940900b0365040100a400c100396a0b00c00c0c00b80040018031042d959041040844d601c20440d10806080603503130010940c0e446001c0e081c014845000c0103810300c1400c010440c030034000c20602102c400005640d0030510650340641d40c0d410345582e00d419050b01504040d44002c03000c98110f0307406113010000500c40c1c90040381000c0f620791001d40490350310780c14095240d19088940c4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 899675287 1250 899674037 899674043
    0x4030b040b070f080a050c0c1b100503011413020c0a0308010302150a020307061802030313090c0801031101031a03030a020714010c0804180b090a092f04020c0f0118 72
    0x1c0555100030040b92810039595181c00043d00c54004940f2480300798208541100348a54201d0070100e00103d02031414401c0021000150f4542203031652030b090041d0f403001d88400703516013945558100030801030300040d282d024034060444149046440da02d5541070b03c1c8080041000e6a059090a080003411a03c0a0006a1048000c03080c405034511010341201d1400d1000d4019504041a54035000001d02140c4080d2104441c668811001a9020f00041020f941d2074100c511070a4104500f143c1240e1080c0358150600174400014808601c02c164402c854480c2442c0101c5c0350380103072451440d00c02007028195014803021400c210030030b8000c16007009549000a20020b0300080e840115440700b0582d174050308807802003006010b1141c403c800501c0e000c2404001040006041e00070480e021000c584c1d030040d40c0e594090031410040c11005a074683c90102d0510408110300d010a00940c0e0151802c2603c180d60005d0361801c0d1010502c03000c115084210700030400c00c01d42a185108651f6400011 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 899676537 1250 899675287 899675303
    0x80703050c010605031f020705071d0f070302251a0c1c1b0813080a0e130c0e10030608030706050f070309030e210d0e040f090203060c09130204030b04 66
    0x1300c2c1500b4005000d500c88104c44c1d0001c6404482044440000e52000d2016102801031500120f0707080401002d6650311045040036008619150740940714460003d003004040500400007405140706c000114000180303080c0f1a540c030303000545070016908a501d076416401050641c10051045482405420b0306102c04000700c02650018201c3c504542609400500868050441031051481034050700e5020b8126a42180040100e80702d03500306401003d54032000501158001605051052845a9001100303400313101a12070350f000540205200c1031014000c01c4150000c40c1407500c40e41001c0e00419000701926a11610780c200b0402801040b00c0070038818041c1c0d0085119203120784210000160541d40d0b210803d07000404014003200c030340380c4448140f145804407108000c3c1c2880362111140c0943c59458064002c441440700743c0d124550340764505403400c0d005402507140480c205a01802013501281d03900d4079040060030143e901d1260400041c408140807003045811145940503a000320f080f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 899677787 1250 899676537 899676539
    0xc01050a1409101e02210306010203070501050a020702040e0606030a060c0311130302030d140d11091306060207060f05090906061908071d032a0409030504051e06040b16080703050c0106 81
    0x1300383c1e560351124041c0190000346d440d400c5111003004010790303048581441034034980855601c6250960303a060b40d0384581d0560000d1b4403411442c051103143d10b0140600080c1807246091000a5124541d940c0003a0103551106101c1400c0d91183c0e000070700d070016040c45551113820000c0003280369401804124082c0c03203090080c0d05100d01032032804490341c1d10f44c690a46080b40314510100070f00080644c0002042d03041c0164003082e44c5640044541c0008807600042c0d042c45e1040017468034510340c1c401c10a00203070f401d008010551140c1200c03101a0306990b03618260310350001040c03051250154003500b040e401c0c903050842c154803c1e40345c2d00030744107680c030859103001030019501c455242c6644203605902000701d00c0c1c60840343c100d502d0071040040402e01c07505242c03500404c00b0341d051000111300041c00014240708074079210424240e24000c400399202c40040c034401103145481580038200340c000c4003007a040c800b844c000f0000341e01c4607030042c00c00d520344003603240283c26501b00c581942c0c00c650034000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 899679037 1250 899677787 899677847
    0x606020102090a230a031a0109051005092a2d030a0f0b0316090e01091218030c14040b12030a030213030c260c01050a140910 55
    0x20b60b801c180c002400901c0442c94040400a1030b0303d82030003081e8101c00030418031101c1d603405001e000110b00503096145111001943c500742c12005070031030200c080c942002c0c80640703410104100c2c142e030001da0740c0905944405da0404002d0201c04100480d4001225540c041d603032080009d05412005004488070402e0311a41040005c0d91582c07070700c0c0c00740700140002a2009000d401c0031540401d550b0000907c10301040c00720b42480c400d484c65030400603294030104246080c1d03100304441003501c40300800519030b29560b40403400070070000c090200044a4004e0300600401180c4400a640c03080a002100c0d40c0c810142078075214181c1d401c1c1c0308514000d142e01840c2004c1c00150301411110001c0c0d850400700e06020390082d0084840b900c564903220102200007641c0704c02e02000340000e601038455507952040044c0c0840586008000303180c01c075079000c9031581d8202c4162031000a240c10800700c000f00c80240714000f400f0748031245901c14031402078441e8858004c034460550001c0c259072000c02c4202d40c1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 899680287 1250 899679037 899679041
    0x920030f0309130209120709060513090b1501021509060711032a07090207080301030b13080403120c0b070809060a060501080105040f021201030c090f0e151f09050a06060201 76
    0x1450300300c20010b4a0b40400d0f01150300a102204005000072207040ba2500c60b9442c01d003460700a004081e030346120501603441c0507400000c04200c9010284a901411380d1442001600a04501d41c40c0c0c02182e000c40c00b03607000f44140b80701c42501550590851900c0300d8982c0d071704c2005940f4500800c0740c580003655140c20110032140802e82020040004144005080d640c040900c580c04101307006140001c10760360b405000410050340101036a0b9241e50441c14001e0400c10060900041c40155400c59400604108290350841c1d403c00b044501d04030700e50b0300c207482c45080b072800201031001e0002001449600800050f02a000090488d08950b460015480888001c1d020b15404142888010401032515030408126185064400341c20803e64401d1600082c4003a001250081c6040b1000d0003030701d52900c034040c400e00b0a180700344950b60804041310b48170340c282240344a482e82c0010004201070540e440c6214941c48040c40d504140755030381260801003400f582e400c6607071403e209000441603c14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 899681537 1250 899680287 899680297
    0x1b0f0e040525050301140f0c1c0507090b071208090c030a0b0402060f0a110c03030315120106210204140108150a110703090905090d1d040920030f03 65
    0x350040480c074491444040b40028240c100c1c640125010304041982c0e2000c5c06000a40346510050700c0250a019045018140000b826040401010300c110010030038a0103010115000105000600c0c0d00c9032a0115441c001d00e82000380340d00000a81d500400020312820b1803400c000342d842d080f15440d0311030405d44030b0390000e283d61f9040e8001c603920400310700e2002e03490350018401080c6a1070442c0d0b02040d054960080301e100310228074580015410040d043c80700c0800d143c1d049010714594946a80c8003964201c60700c0416000e042c81c0c958203c1e1620003580f10901a0400500c44100130710305400020307540d13003000f00c1203000754240141c107c0c6084115100d14142c0d04903002510708841e410540c22000640281102c00458490500751500c0c9401c2d401020741d00c0c02662441905401d0454080a0f5034000d00b00300d00d15031000702640c01140c1c4c001c0502e415140020040f9200c69082d80c0024041d0484100c0500035081410041c2a40c0c0440c000d06500584141c054460140303034020303032544078000d07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 899682787 1250 899681537 899681543
    0x504141e010807140f0d050115091413050a0c080607090e090c060f04030f0b01150e0f19030501060f030204060e09030706020a2a0b06060412021c1b0f0e04 68
    0x760000f0b0084c001c00100b00b1a1511001e00240d001c440300b0b800107041180d00352000c2d61941d5488002406400203520b164014100c085002d00c0b400707007441981c07a0319040003040c2240080840c082c010400c0b5060108844140c3c024403074010540e01d40c1605521070100351108400f0508616001401800540015108a003194040c20000a65506101c0c1c0d80d403064003440c52810040001100242000080c210490300580d01d0014070343c10000705e4a076400c14110030704180103041510110380e948492521303082c4442174810031140c0d61800a0903409090b5500000d01c0c0e542401800b00d000b032142003c500481340203c405010750703a80c6072440b05d55602c1c15120000070781c10400400002c81c0040d0001c02020100d880c4c6010211800601c24100c2a50780b83c91005201502041205000e6840340458024800b1541c9a1501380790107042600f150f810080280a41030f424000364030a5481e050102ca00f179048180c1c105010600076030400e9058176405203100c0b20310048000328440d00d00c000a07504c03031a4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 899684037 1250 899682787 899682793
    0xd02060c07020111161806031e0501020c0d03020d0b1005040b030c1207030f0515060d05040804051507050f070302090a0b12011802011b0b1f0504141e0108 68
    0x980e64909940e5901540c02641400a45045402e44c3c850402103002d60710910420003040c40d06004110f80c40c0b990b04012041707140d080440a10100e02e90300382e41006a10301900c0400c12064a18010303003e401182e170161f850380126810f10a0090305600108006140d0140800c05101c400c0200038800240030107440c00148280811322210401500554208000b05070705401d000030180384c106403c100729a0600080d03210360088214060a00410b9000340c0f101c020080103e00c1000072a803e8001c00b91a01c00035910b800206041c0000780c1d08540162030042c1c10700b03001101c3c00614072030a9006800494047c880d807034400e54440804a05402565801000503680d40c4a04036440050030403408000d034401c00b140e403640c020131400d202e0000c860f03882e180707080303161038441c000901507040d2400000f0b036200d202c0100300c001039811941594045402b900ea40205140381d031001e01c812100e900807a412604d80280d600c40400a0011548900e25181080e40034102070507003100c80c880c0c20300c1600c000e58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 899685287 1250 899684037 899684041
    0x519110406240201060f09020a0810060e010e01200a02030706050412060b03012904060b031e042a0e070309020a03060506030c0d08090117040f0308060109080102120a05090d0206 78
    0x1081c03659902c030700481d6901c008540f854a07000e80b0b1008028541c01110895030009014111640182c0c046a000c000240c0d00c5180d00e00d880d01c0a00075102110601c0d0400142c0d50f1611740c541e00503602501c1c00705000010007604150b1000340fa0340d800c071b40c1c40c00340c2c804d01c00d00c14006103061207141106c0541c0c3d04000ea0b91550311240d6a44000f4280c0d00744551f80c03554036403030060100300c800a07846000c4821280d03440708500500082c4802c0301c010340c02c41e4400342010810854001940d03800030311321389007140c5ca9000e550345908144034841c105c60410401001811034040d00d200581200b441074503001c148c810420307141c0f1f040c00da00300d4010084c0250003884400081010485550043c0c2e4041c80203803d44481c600304500050341c48441500131601c1e0040440c1264055a00480405d07800d12203400b40c00d4141443d0315400e10400031804000c00300130408001440700d9110b14251002418014025916088440f40a004011003110440d070154900310024444c0080000c10401984094018280303079 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 899686537 1250 899685287 899685329
    0x31050f030d091a0c010203090606040c030204030b1909051f0515030c01230a030e190f17070204021b1c0f050f0906040605030f0105011d01030506010c0519110406 71
    0x1250f14000682c0740040a0181182601d03003800214801c40504000c0c051030702c0c05e0010001150000c0300d059080610622003400040c8000300c0c02030f0460406800d2100c50800303603100714090b02e105000144540207040084c0b541c2c05c0103601d01da51140080f0428803860783c0e241e010b005402172500d2070542c1a404080401540c2d40a9482c420240e40d55268240100d612620110f05540c4500d5115000a43d0364413414191030041c0900300e0f071a1900100b40d840009030740c54801c1d04800340360001c0c1c0b12217103c445c503c608a1907034040ba49050f07400b5005545031214003074500d00150704000e80243c039005408100700c10b002440b80c0074501903411740f5425171500d0461011a0140c214134420005d5900c204a20a4a6602c981c00760009000c03681d6102c2c1d4a244c041620003402c10181c1c42a814400c0f50317580b040c4080c2c841911407012200070b1070001030329507603c0300407a081c404010003d40307640150300080500008290403070348914018455180d400e1070510038002101c44510504203440e102400d00c1c815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 899687787 1250 899686537 899686559
    0xa08041518020d1505270d02070b0a0c021008040b090c2b08070507061121160605010b1e0306130b060409020406020132060631050f030d09 61
    0x70b440c4c01000070003122042e03880d041e02100c906840480c40c0d0840301c10702c00e07003582006441143c401c49180280c10041c0c90f110003e5511802d5000f014418100420107444079072003072040301050b0350000e040d1608450103e101034000c010544040d02c0f9600640c0001d6a002e43c0050340c4483e07010b024110780b0403420442c042c031104544070149103042d60000380c603903004503001002034003240740184040c0c410f9030303d028405040c0610344042000f058206800410458412100300054000710503106550380d1401800641640c00490008101c0c52030b100000c10013000b0000030b40008003032480207041c0c4201d02007222600740011500a580721a009880035065201d5422200c000000a4031003418252200000c0043e40c000e50403000050b0f54490900b1940004c5588803050a0b6880c3c1121441c1d80c903c048400b02d4440c010400ca010700c50000d0000c1081c18224904040d94551b0303a0b0709410940d550500580c00c0d81c01d88100b0303108a4241d50340c80200c1c600441c81004072030441e1a0610301501d40303040c180b0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 899689037 1250 899687787 899687809
    0x80c0c0309060f030601031b050a050d06091b02120909061306080f1c0c021f210b04050106051615020f03041b06142a030a0804151802 59
    0x10080c08148088507441c0c494501401d200d250b26544a6141d02d0701200044c2180e903001141c902c004001526026150303041011070b2014403d5141442e61510941362038000303803206501c080031061409420589040c82403d400003600c98542c250380c02440780d2800848a40645014280e00200020118850349801d0640c0e022144040002141c0c0303641d038445070381c1410202c480c030707402d503420820f00c41d80c0c0a800f03107070f901711002002d00381091044440e07000300d0311007681010171001c6410010b00c0805070344d000d1840c0c1c0070050000c9a000001c0e18a00c02500c1c0078081c02610980200e04100c0003040c0b0314015010758a4461142005410300c1150f5181d030311084444000d20f400a56080140031040d54921004511a901070125480968610040c4004080040d07002c2030400941c0c1440807403400b903801c2210000b80c01d40d0310014000d1400400170000742e12400f03080d8824800020000c2da407070381110086110303900070141e000d081040c000101e029104800070500c121113250100c1c000603e020940701e1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 899690287 1250 899689037 899689057
    0x11d1e010e2d030406090e01061d010e040617011a04050103111c08030c120915061002100c0e03190c09020a03090b09061506124c0e0403080c 62
    0x1041c8040b5007078181160321a40011000a0030014180113001ea2142d00500410382c0d403402d003001c0900303001e40703400300d00024490504001e09505814820354541e04980094004207094404402d00329501071b00a103401001449080484131144d074040c90f261080c98100d03034109200ca120300b0004000c021a203604001419031804801ca01c0c00e0204040b031018510031507528144541d0b0700f4004214400100005220641e41d600441503001c0700702d40000616002002034480c03180070500d41c9426810407014060b00907002e880c004c0a182c08517800b41010440c41d00503002c2d030742840400342e19204d0180c08842d0240600884000800c900c0c60517078014040c2000c03620300010060069070740c0d9030f9980401c3c0c403c010181d0008080c4000d80b0044403a010044108466191821052041e80121003030001c0000c414030385002000a01d2403d554030300b0000384c91004c000d170b02c2c8a0313141c82c800040d1000321015110305400d405010460151008580b0b014a40503118a06142c1c0c411242c5045c070b0340301100038 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 899691537 1250 899690287 899690353
    0x3030f0c0c0a0303021308030901230408010e010f060501051201180902030d020c03070506040f031106070804170613110d1104060609030b060f0a0e09011d1e010e 71
    0x24152085040c022840c00503c030755000f59850140c8403080d588183d0b290092a000c0d00b04100c00c0c900d036a080701c070080c608510b84054540407401584198400d00840c4c6c000016542000e680c13440c0000d040d80641c450186081e400c0000c00d864800454003405141c0302c1d00d42c070031a020010702001000c80682c04540980c0c0308040382a40742940424280b860021041000d41c2c13015014080358a024007840d0064241a14081e06141c40c1041c8040c05800d148409003602e90440d4006113140c840720308840c0b0b040d8201450a07541c558810b58006503c41d2401c9641d018040c040205821040800301704e580c1d07941160000c16240303541d40030000c0304c00c982c00d0b08407071843c8000b804100644a60060764000c1c102c5403a1440f0107440c5080940e0b100030011706080c8105406040c111055959090410980f8103090140c1496600c945025006002883c40000300758000c40344214101000141024130304210003980c544441d121601a017039502440c900c008070740000000074414461b900305803041460403541 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 899692787 1250 899691537 899691547
    0x20c130e07240905041a04090501060308040e0103030e1801171c170c0702100c1e0807060c020a0c12031e09030515062101140a0c030c020c0303030f0c 66
    0x1552200d040c040607080c1020708a40c2c0c060b4034442e040b12a100050000b0381341881b54110003500344200e01d401000d128410399039a501d420038058254040805140c1c080850f03030341c42d0745854001c000c0e04c00900c0114002032802d20104840d04121385c41766801a904c03402e8103800e03420803101d2062286540b20110040c0b240186905e402c080c402a0020890075135202d24407454518401c0b60a0310000030085ca41e101e10404c030442c01600c0703404004240c040d041c64914071041d443e26103248910f034031141603003004a81c0d00d180c8050100c00c42c0205200352060300304124003008114241e0b12066445000340991000764420850441200c0007900000d12928150522500d0807207200401781070003941500096000d64140100142000340c0107000e0f000f000f0940302c5281000008495601d5244e8803d4070880700ba01d60070700359500b500b2035003101040c00d038411120314014010400030803c1c9104500001c1c20408840542800842c3c01501031002801951440c1d0310125204e04040f0003402807480d00c601002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 899694037 1250 899692787 899692799
    0x150f09021f030e0c03061513020c013218030f1210120507090c030212070806130e19030c050d0527030a02100318080d0c020c130e07 58
    0x30548040710880311604040c800381c0c150040803030b501e02400032019800303150609038558000802650101c07802c20000480c06401c00490106054030451902540c00440c1174070b450101174104861070410407144252000140f1640e03100d101e88030705031090395545030002c54442d26084000070307071520042c401c880c60001c082d4070715805507010002d003c2d25582180c05110b6900858201c2400402c1409400c200710140c035101e464a40b0780074414102c8242c0d03510811070380c4600a8060740c9507000004440c5515107041900589291800c03a011807045981584658859800d4803c1c1100384030380c07400500820720300d00c0c0c81c0c01d5405089203099061001c4800308400041b01000040c221801c10f55509031a049a518400c406010226115014030408400c1210316140019026030a60b01200c0015041c1c8034240e041c1e00502142d1034407080c42004030750b10f1003400760100042480c034610030740810490450041c120386a01208a04c69402940341c0700112404e9101d41015100510071701c03da034401c0f56a01 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 899695287 1250 899694037 899694049
    0xb0403030209130608060a0c080708090c0d03050c0f12090114040b0c030403050c06070f240501081b060415080c0f070b0a0b0102070b16030e030a03171003150f0902 72
    0x1a00b80055561a040144031714142400007a400400d0320b003052011040600018100090003080b002c20005082c1c00600b0090040020000451002c0c28003021000d050a004007103920010b100030702d41c8909607540d5540880010241020042502a5820102d00000466040c00c0b148190464901c00740008903555403004000c20407064502c0045035590315601d4404d0402c0003244202c3e1103042c0921020300400d141985805040b603100030108404d88030105148804c401c21040b000e03005140800102d031503800040c4404103807902003007100c3d166051008000d0913100d540a0070400e044010076600c031440c0a1101c4a0700101281d2400382004890360913030403203422614090f111100b540052010a40c41c9215103000100c007840900040b500300112003145204072172441491414900358582131500c51600d2520b48600281038a44409642c20020720a00044001900041001d8081004d0208400b025403c881d07200102c20b080c1c64030f9020000042c41c00b00002d03000d4548070a0b034100165980 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 899696537 1250 899695287 899695309
    0x180f031f15080c0a1d0a09230f0f031801030c0207120605010905010801020a020d0e0f030f0601060809150112031205040c031118040807020409150905010c050405010c0b0403030209 79
    0x1142c0140290b0200c4810801c1040321a800003030120201d5008005c21450a030300268003c0d1100d00103d44803c441c5007540000d590581034203141018034400f100c0607280030480701811150f01c403c80d02101d06c140c0186883e44a9082501c0d040110713203c4c040c600754081e4001d02c4501c08180160307500c03c0ea95000d200c0300c0c0030b241602100e1a503907803001442410f84a210319405050040021400e00d000c515010350b444800c41c42c00024090b080852200aa0359440591218070700034003510008515201200d0fa0b070711082c0107038404113018a000511003100018a40039000d0f62000c1920664640480710101810002c811707020409a440042e10340300c0b4601034540100e02c02c0221040c0646941481c141150101240d0f0f032217025a0360b1140f400001a4071103642084e04003a9480d601c2d2400c4c800500103004d990b80c020560fa031050614080000c90b680039844a0340030340002e0150a1404134211410710450241a0104443d01002400b10b00400c4180343e015220741401481d250300440050721258030 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 899697787 1250 899696537 899696549
    0x90f03150406021c1103042a09060503010f09050a03050a0507081204050c1c020405060a0504060b2709070807031d07061101020f031306180602180f031f15 68
    0x295082110080303180300800c81444c0352081200b2010501001c07403512020b040030b04005051800440b105104030000c140761641c001a2400c015a2990002c011b003529125845c840c1d441c5c090300702070550b05ca00511240d140d01c00d02501500449583c1a250b9400c580d88440400805200c4440000c0c41400281412039000d8802d203454501403030300c940351500010b03201d030158210b9025080000445500c0103030343e40d4105c0700454641d4400340421607801d215030041d60302c1402e000c40000d03ca1907810041001030145030041c200c44402c0000c144e8848001c0c2c00e02c03500003548070001501c4a120311602500000149404a50400044110071102c54006041719580c4c009180800444c0d4100c6980440340290100070f40c105843d0355101c1c14103000050401074000c8061580c1020001140e02034103043ca64240d82075842c07580ca00f000b0b0025040003042e0350100020701d00c20708032450071540207090500010014030300780e482035024400c41404801e8480a01ea198201d022041c07000e2a043e402800c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 899699037 1250 899697787 899697791
    0x1905070b0703032712031401090b0d020a0306140c090105031b0c07060531050123160c05010507020904020111010b09010e040303240308030627040b010614090f03150406 74
    0x1c0e079003011904034207a00c10f45e4007894a010f190004850300c5d03c1c14181140c990075400603080b8203410210b0144440044001e41c04a124003020081240c254868808501922005550703562814048401403061031501c0340891410700008000f03220b880e040403a1000e440308a01e0514102c40c00c5c1e146481295041000880c202041d100503240003c1e040c940d0220015404e400d40c40200d00313080702d11803080e01400b41000f80082002410040000140c4c6190707141c540c125030340300111080801525001c010840d000200040002110362141c420b64800c01d80080048202e611154015105103400c0b03440ba8070303503540f40c6074641d05985d01e0120a50080c0600c91820455140a250080440344032107822001d40c140f441081d8001e40e40c5000c10b0083e2070348085019501d0712414005040032000307a8995212061070b2441904034140745580ca03020b00d100b260303800c8c801d980300e902c00c1c1e503080c064003c900440c002c140280d100034a0400c2c4406034802c4060162801441c21101e40c42842d4021102a01c1143d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 899700287 1250 899699037 899699111
    0xe190207140d0c0317040215030a050601030b0f1819021606050105030a0f08070804051302180f06160c08060c03010609150f031a031903021905070b070303 68
    0x807001e00c21041450300038540106201c41543d0043d011008401022102c01c65140000d81152070313200c0c507841217840c502c180c5922440c2150751a0702906080b680790f030020b8203000d103180c1c65040c158080150b40100032b102000c2460580300112038524000d002c1c3d40c020f0050b14148508120a1000300342d04040d900040c01d00780ca250400f1000d80c1d8069100e0f5000354030000160010a0401d4043d0341d4155010064554482035810250114080c0d600800c0e88400d203c00c12814215a0358001e1003c111007004c514100a001d00401c00312800504d038131608888104003000102e6180c004101c1d08510448000c00c100e500d801c105071401c2005c4a6941180c0d4000005000705604150040005c100c0384140c59a80102044020849124a10000b06042d1510042c018131020f0071664016101d0127811615080c0c3e6490043c11005400d42084e03001d070140c1c80e48a030b000c103c0c035055805625040780c010800a4903244484031650b20412050b010180d460301c01040356191032820300c08505088811407180 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 899701537 1250 899700287 899700323
    0x160c0314071406030c090121050f0103050609060702190204110714070f0501020d0806041407021e16120302120319240e07020a06110d150e010e190207 66
    0x10b40040400603210301010710401a0b4840d2520840301080028603081c0c07a100307210310101c1201d0002c1c4005e14503c0c0c1c10301c4100b21016203a0311903030f0304076401601104d00c41e0310313044c3d91661203400603198000140c000c031016205010b010b0780b01070b440034030140c0f00103060b13030030700c031f450b0340150420841125040003503001c801c00741404110083c00340004010483d4010b28240c0044e40d210108152281403102280000305503955590046107158a110b1451186250428009445010721038032000052002003003c01140d0000921402800041445000c91820504464407840007554120114841d801e400c60668421038041c2d4099a5140c100884d502c600c50310940540d0b41c01401440c0a040c0d5502045680c2040c00c00002162441581340c11540c59060040741407070659013000d400300742480062040c80740f0200003440c40360070028003049890a0568000f1081e0303200d00ca40c031254283e45006010040c041c02d1161380055003003542d0007980c6c0003480301341c2c1030740c01c0300500b03481500b00ea0860f0080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 899702787 1250 899701537 899701559
    0x10312140d0b0a1d22060c0f02010606090806240607050106030c06142d0a1106060a15080910110a02010507082a251401020708160c031407 61
    0x1810303526030001c040c81e503018490541030400405c0c2c1c0c102c461140b21040d020411042d8800c41700c42d000070061000342c038504409014860400d03225401986031010002d403152090445906403001030014188030740f0b0b1194002802c646541103207902c0b91400d0b400b030966503241402010850b10440c004243c444c514102000c00706d140344d1001050050201166000200b504100c81e04004200c00564100ca00416991103480c0078066000c0080d400043c101c01c0b09400028001c20305010304122a01c51382c4450034000041014410014600c41e0f00884648a41c000c2e120b0591016051080792000c0a01403603402c00c0e54040300316040c00142c0083c00510303280c0d080c0599076200c15603080860700303401c00d003111002088a00e14a4242950072030210412581a1421200e00c1c944210300c0f0906044402c90421011000050441d122001d0805128544d02c2c103000b600c81d0590050125410b0003042c002c5803d01411031601182c0c020700f08100400043c1320104503440920b0900000c1505500b41646d1000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 899704037 1250 899702787 899702789
    0xe090d050f040b0a020f010627020f07120e030313030302010c080402100c030302040e041b120506060d050307050a08040f08010b060d020901050c01181a04020108010312140d0b0a 78
    0xc0000420a03405440803850071902101c83c0d0140d0075a070355401042c100d060a1343e00c1c003c04129405c18000203030f803040345294662100d04075100501618a2000e0310340482c46507002841408106004000200f844a00d082c2c841c4103140c105004886031400001e400d43c2e1000c5081d0042800307041c018401d0650900c141c1284154600f03000149041076000600e6008880c4160401c01103400044000c151081c1c041e60000c00d65400100c1560905190460141003018043c00b09840403200c0014820700c1142e080000325085030213400e494079044280604401c040c0f00960710303031200b0000728000030342c100440d8582601400f100368461382030140c420102401036000001e01d0303052002404c1c03141e841c00f048030310302c04130800012b036035040c0da20060b03420380145520f203603480d407a02030f1500d5168440e17405034441030307c0350b0102000e81845c410103a440c540103440c081e0000d8580d45c01480082d80700707039441c0440d29840c200340d0762a1407142240c051507400900d880d004a500c401201d02541090001c45c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 899705287 1250 899704037 899704063
    0xf030f0f0a0b0f040e030904061203030b010f0e04090c051306091a031203060a150503010e011d07030509010f0c020c0f0315130303060512010515040203070c06020c07050a0e09 77
    0x111000c800c0c44000340080c80000c500078484d66176440b010410542c1002141e06012002d4030902003903564100c40f0540342010a4250040b0741004013040d003d6208048010703074154980c482c40c44035140001800018184000c044035141c090700004269035940b1145481d81c04400e0301c0201d011b508005802090328140040c49503540c164103c8800d02c0e81d001b040f080348075040040c000351203030748520000e015400070b50b00110407004040781d2000d20703e90200046040e0383c0d5190b401b4000c3d90361032044080f40c042d90b28622268120403000300300710b1762081d0801500702201c0f40003c9040d42082011f10115040b1100600240c0e01104402c0c8542c20140850710008104a026003407880000c84181030a2000400312000320301c81413079030700805000754031000150001401e00c00100c2c030350580b6140204010356540c04121429400c90b441c0380780500131288100d41980d2041e8446146030b807814003075006440100c00500a02001013035580f0b07146800390007000920090b610b541000c00c2d030300b070405064503010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 899706537 1250 899705287 899705291
    0x2506060f050d020d061d070e010501021212071809020a080a0209030d14120a0e0105090a11101403130311030403110f01030e0d02071d060a03170f030f0f0a 68
    0x81081d69940c0700004402a0182ea88094649540c0781410040c40307085c060741e00c5880089000c1007030150001702002924410f0105410030b0342c03550700590340c603041c0c011801141007042220111b030305011040d0b20340024040c284610040212506050f40c4400780c1c000c5081301c2d601080f84500f440d0f000011a4001e01146011498401400301281d2105102d02b81c0509001c804100810b0803401e483c1102d071300740f407190f07403445150900c240e081d805005043c3c4000310560800703001c030781e4211011a80c0c1c040700c2d50202c2a030382400c55013024001c02c18038401c11032081c40008010400036488003001544104106161060350711642d29002c0c0c200d40c11040005c1c9158000e1100740005140c01150008403202210317510300054a50703004030040e090040808000380254004018801e40000d4218141c4466003403200c0020201d03a030030028280d046450380c1d07101403a00c0c002c0011904140e403140f1810990340803107140042603a006d10ba2a40b0956058003030013142d5040040c2e0100400c4140c1c0c20800e40402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 899707787 1250 899706537 899706539
    0x20f0a12050d1d210f0f0415031d15010e060d3c050709090f0203011409070b18040c0c020904080a030b040203040210080903090a14090106050c0a080f2506060f 70
    0x41c8550f14040d15516122005c80003403040079400c92802071310000e2502c00030b581402c030040c3c40300070f003c1e11460701c4000740b1003401c54413204030361400308240d404141c2c2d90b078072111a6031902000b1480454054962a00b03d5078540124020034484945582e40808421004006c1d60b4080303100b0607180d080308240c03c070f144e0700004e01100050021901008650f1152008a6031180d01d04004000c1d081c10a0020344c158030340030200ca2075501140420788184410429104150303038580c03000285c1c2c407503400200a401c800d51402400740c80d140d808806e03152290714000d5880805a070101c0c81494041e1800c0d40c8130040401e202e20403c0e450b0251300040c1c0700666040d815820590301042400e2a21080d0105108201d800070703504280405c00d5071840b110050040c800a9540d5081030f803049958215140142c00b100c001283c4c9600800842c0d5a8180910044c40c00030303500c1e114080d003500035810740383ca2040f0400c0b0000480b803800c0541403c131200c4d40340d090410b52040c900072003150542e9002030360310554400 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 899709037 1250 899707787 899707843
    0x305060f07180306020a0516050a1502030601090e1504140901230103030c1407061106130512070501090c0906050423060609030703150912020f0a12050d1d 68
    0x402c808407584042c0241c1c50b13550a00381603070a4094a9082d88602c8040c800501c1804000540c14940b54001d02c0032190740b690b200103c2c0103070f110481e25240440c5c00443d04018204c1640c00803540400c0c0c0c0329125a40761000702c0004c0c203440c034158001d1680280c00083c03203030140c0d003803040c0301e00c505040c0f103007400a1906941c2590728000c140710240034448a0345559080c0b01e21513005040c07104003402580c05090b19800094580300c150a0812020712843c80000c0c46000ca68071260501c1c0e801070014000c00c030101101c16001d5110385d000300c4241d500c400303000b800258288400d9002d0901c10300d01041c0c4034241014441201c0c2e22502c0c1600c0c0c1c10080387c008101c5424071451729080f2600307541a40c1d03110300c40c0700813030300c0c1c07004030307800103051034004070202491038825440300358180e2094184022030304100900b01da554039101c901c42c1341030b0403c5009200158100701c45640e111070301d061080c206400b01c0d621408861560700a00c80005900007291641081403001c1e40201c08400c940000d141c420038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 899710287 1250 899709037 899709077
    0x10204150207030f060218030f0609150c03010509130b0a05191e020a05071401020901030506100f0e0a0806040c1703180f010306030c06030b10030903050a080615040305060f07 77
    0x2040c0903040c160b0000304034010030031031f026840020034080c0844100c1c03c041d10320542d0b101d41c00c580c0442c2d24028001020045031a0180040c040c0004101482c11340e4200303010001e580d1005000c1a0012580c100a100010504500ca07882407000c0c040c00651850714072010783c03034403880c00307640500a46404a00324000486d0028034000d000c00042c010b840310403a82c0260b03030038403840e000901440d000c609a40c2c0e441d20705400904117440300b80c0c0d0a001944803002400801031502403404041402d00a40880760b41c8682100d01004000404000f0015078a041140c2400000e0360203841410020342d0501c0301911140781603100000b0100194a001c2d61800c2e07a801030302e84840000d1062083c1d0042d00b045038865000030002c1d5170000b02c401c040302e6076038101170020b03c5000c0a80e4050303121903041c000524020b1145851680c0c241d00c81d03502e00a100342c42103441c840010441c952000c000300307200b00c2c0c03084590060300195200340300501c881d04242555040c041c01c002c121404000f00c0e885a048502029 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 899711537 1250 899710287 899710313
    0x509010e0f0f0c0f0d051b040b0a0f231b0c1e0d12120c0905060403020616050105010902210408160c150504090b1008190207060e01020415020703 64
    0x120094400c1911025403121036445802c213044240b100104102503681007990186000b0812000700f40c000124001800b48240100c1c41030700784102042c002140b400d40600030003606101a841c1c500114415007030040c2c4914a1000c05180b688404a00d45481081404010780c2c0c02000c40014403e84045900113020443c05a850302c2c43c0d200c1012800c0201d031101c000d010304a59010402e01104850f48400601741041002402d40c070f18180600740c0419030090070b4074000c0d281c02504003494030f401c0d074080c0305190344084075000c0303203c03600008100031410130700c9170a0280c8003503580540d850a180d04080b41c0310076956010188510701c0301c28000025043c1080381d100b0120041021140007441c24117070380c0c40b5005c0d4888202d4020100d40d9500360f6030b01800800c00e40d50500010407010103001c003809600852100346034041203402002c01d8100440324070b4900c0071120210302510300f1106954580c00c0c3c81d81188000c1c596034011a00b0b010f5044030305001c44000c0c40e01e100400180e451602c4110a000760 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 899712787 1250 899711537 899711551
    0x204180b0906030c0d02010e0d0308061005040e0a050414070320042708041212030c020d0c0206090f0307030c090b06030925030b10030b01090e1b0105220509010e0f 72
    0x44030703072174030116406040c094001540060401c16030003910306010381010802c54880f886075000801b110340040c05042907030241c8064030101e03010b507a10702203603000800307000c1c1040ea02080580c0031407040180811000d006117200e102c529458940801090300c4224a045503603210f1418104c0c1d01103941c0c1d40303200280002c0070300c0c000703424041010f0420b0402d51041d6001021211016a600d03418401080d803c3c0c10403034201e507802c205002501c14126200c02c40c1032203507800100c0c00b04c400d102500d820005000511070041054071381020b1500040d02c0d20185900843d03281c1e14400342000011030600c03c002100d0310035914103145103010390304143c40b10440fa2402e0103403071003100484443d500e00c07804a4080c40e44000d41c1d045605143c0200100540c9a00c07007190101c43d040c0000c507101c0a180a0b03195046005402445a00e51700804038400d008480e14444c104001800004e50807182c82d1108141c0c40d2004003c040000d00b06828441082016000800700100403001d0010300040ea45c3d29980c0014 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 899714037 1250 899712787 899712799
    0x5040501080a1a040201140f0a0e01080906040f081308060117030301060c0f0614070c050f070b0426062a121501020106050622080f06010308030c040305010204180b0906030c 76
    0x1d9981700594076420440b480202d1440041901d03204003070408001c0c054510b581d01e03107a4440c09401d0045960301030803603100a660b005240880d00280c80709422952a5215111050810f810304803e082000010b40c404507069001d04010080c072902e11000309400c2070090060352a41d1f040c00d5001e000007036840d500034001094031141205201680d03000202d1030040c0f0782450707810308180d42c0007032410150038010340d61400340c690a60010100001d50404503502c40502504140c98120150003070708c441315803955540a180600403181109111a1b403041c2d200c00500a800030810800540e410b0121054200805041003005d88200081d1115940001e429103640c90711420000101d0140285511a5801500215841c6411000d41e00782c000000c000341c011000c801d44e140101c80c0e40307030000d454500c2c007a040b900c010310100e080300c0c00071503000390517108461500d99030350380d205d0032a402540454a402c1942404070b10064040c054045042c0c01100c500540b4188603000070b0700c81e0401e0030494810f075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 899715287 1250 899714037 899714041
    0x3901050c030c01020403060518010606090b130503011409063102060c120306030d0915050c0708060c0a0e06070302100f1503050606150c15041406070905040501080a1a 73
    0x350100111280d04600300700a40d111690380c94018003138901507450031400c0701704038002c4154040c1445210203c80040c0d650380425032501242c4502c40d0711003804050440e00417000890192030034005c07460700f8011513004108a01d80403100a04000016240c20800560201d900031030032031042c4c2c100c0148684c13000240d0001c2030351000907028824901d00100b1740c0500d01c2000e50005545e03014503ca00d07421303015513104083c0a40211100391240c010041328500114140c540c1c1441840a062b600756031004960820780c941c3c00e824a80403048491001007440018020b098660003810f51a82c220103807400307030511410740e07000707515005c0c0041f01010490740d400110790310f4609900885042c52201004020340390310385c02c1050300c5a008072405401850b40c1d07068414070780b2410085903191400d09003c0d101d6040002c41907400900050820760700510228188850b007034041c4082801140d6035182d40e0040b5240c5024003055600c144c0c050a13068004064050108010722958044410703442c0c6154206d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 899716537 1250 899715287 899715307
    0x60509040207241512060905030408030c0d090e01080d03050a0f061e050a0308040b090f10030b09012108091c031d0f0d030e0d02040e390105 62
    0x2d0241520103819030401c8542c054441e1201041c0500900c603c1400b485545000200c10711507603903610031006034542d03800301180800c4035a881604d200d445102641d24080e03881c014945541c00c080c244d0801d9401c0340308080c1ca01e03504440c00200130000c00c1072506903585841103e0743c55013940801c038000e0503155000103000450aa10074260240301c3c1c030041080d1500c0d201d07855070b03c0450f10401240003004c40340101e40c529144410300201e0364498030003494103007030040f0408a41c00240210b42c001d0545d9a68030b03407542c0c440050f000516120f5400080a643d5182008000b00060384086d5080301803c1400001c0c440b0410810605500b00c803082c0d944500c45130104210101c00d143d401106007040c110f0a04060340712607403076020005a0301c20580d10050340200096202e5020300150310042d008059000a802262035000f002c0d0000d0240b90042c4803600400c0030b40f5607404011035160000c4851000402040c14110b1201c04c1c5041290812403100010741c500f0121116440d06221000c2000059 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 899717787 1250 899716537 899716541
    0x180f060324141e011a190504030c091a0f010f030c0207150f110c0a0302040b01260a060605070b04140a1b14193b04050d080f0106050904 60
    0x1400c800b201c801090b01e00392441d080c84100080e00510b8203000d080002a00b0401240f101049030351360241540780c00da1110702c40c11440328015501c0e00344002030000101040105403104000c18001e040031030b003045440d240550031103000e00d0741d51142180d0040085143d0744003014002701d1141c2d080024807000e03a0070090789040d0496005041201510130300c0581e203540240781d10f10b60815612401d1824250f62000c54581608160440e00700303440c020104050318085c1c00001544c0810704040300703100c0d04481800c510f450051242d01d40324003031030140000c0000c83e1240d03600034402c5203002400c00040d5510140e4118028002801c60b14120f906201c4a400a00c000848180e00103507141d8040f95208000c0c1c11003641e0310500001d1003844456041c2400c050410884010214000060700e07810304034a809a0660011541020348442580301d80c038100c4e0b0f01e0000000b40003102100351500c0c042c9800340c50000c66403d0281048004811b010480c0d1840c503005041d5030070380c2021a01c4201030300100f40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 899719037 1250 899717787 899717801
    0x140a050405090114010503071a0a0912140705011b08030405011d01090c0e060918030d020d0203240904080c160e06091807090506060f04180f060324 65
    0x1a000c0e280c10203000c61203a055005140c0014503210304c00c0c140c2c0c0c3e505c1c20103803078101e5803062806a02c01c003143c80c001031800200424003640f003400c01c0074003940c55441031551804001d50480c3c01260310205403032800e004100d1900140000d02c6c082c2c1801484040b00c4500030ba02c1b000c0108070400110102c3c1c10003100303411100f0481d203001c0c25107000203810070b03619000c0c100b00d202c00e5800912408011610b030045800061083c50003404590003501c4403000109010300040c1c0d6071a4502052114004c1002580000c0c0303004030f007450001d030702c90a001422400c0341720b41030b02692040c039041c1c104000c00c2e01c2d200e15403640f140e0404c05403519000e4000586081480d1080303422400c041908010924940c1126110b004900c1a0f41a1340b49a4510004c5025a00240c820300303000d07480001d00b040307111501d03008140e001038081c00803800c00381c0c208126802a00190884405444a540402d42c0312085218003076454810a2050000e145140c40d598100404a202c2541251201c480a0b09000c01ea42002e5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 899720287 1250 899719037 899719039
    0x1606020712180806150d17040b0d0b030304030336030602040305010e06091b18040503040513150b180d060b041d0601060c0201110f07031202010c09140a05 68
    0x42521880c035400140380001c4030704282c14078100304001040c882c81c0014441d03c111443d400c1c4900c013103110010004e17641c000440031070f245101404c40480101c141c00c0a030004010b10361082c2d13140d02d240f004160983e203403481103d000c2c2d4018401000400c2d413241819006258122a40713415490040d001c09810880da8100c030b4107084440000410030420b40d00410880e401400200706030b0851102c21500c88100759205070041c1c0c00880011310380c0e144101880074204005040400001c461201d0b00075852045500343c07071507040840c2c104050705080c03d00c00c10502122000704200c0c5080070890300d400800d03019444141c100455214801900c5c0301200c0401e030002408080c6011891502401a0014151450096090012180c487c0c1008000c4910500190001d00071710380c03c0800803100400605000d0b410004403040241080000b80704445140003c18081c003032542c2542040100044203c440300304581c036101d50300c11485c1c1d2001c180004d840c0b500000d1950401c1c030380001703040c03200113800003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 899721537 1250 899720287 899720303
    0xc121403073e121911010807050703050a080601200106091a03060a09171612080c03060d14190c0b0702100e0d060606111e0316060207 59
    0x2010610165480702e4030400b801e50300034050001c050100c01003603055540c000808210003008110b85142c074000044610078080222150500920540000c100032404199050924102200240d59104202c0d951000603414403600e000000da4009219204240f0200100034611012400c568490780500001d0340031040711890441103407000324001d01487c03044640e002d2900500e0501c1c00c00d4002140340242c00140504060303a41c80310194041e0544c00021108080c40c0c407000a0000e00420250400241c0307800304c45400182071511811010050801070203022054040200006486044076889101030741c40c648d0001052800b80d91052030060b0010041c010810030303032000c5517030120a950541c06210100030341035807510a080d81d407040240280d001a4100003c2e10114002e4202c2c02c00440081d2074140444902d8039a402210455040785d80019007910340e0b5080000308121403c0740c4950b8030040342c03d200d00c086071190750703224645116415020b0191b459051004940c103641030107800c0300071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 899722787 1250 899721537 899721547
    0x30203100f0308030f09161e05041107050c040213170a06051e01050a030b04030f1403010b03011401110d0e031002030c03100e040503070201111f0e07050108040c121403 74
    0x1140c01c56800c110396503001a190880043d00700711b0300082c0c21506081c5c04800c00402418100700c0045446e80440040a01d0304c0718074002815140c0f4420f25030024000745456803241171b24074001c0d00786202c1d85481c6200e1401800180e103141c02c220b006034201ca480014086240850701641810183c19440c081e00503481d00302007100e05010044900c100b01c961030b000d00c0d070b00d82c1c94108011041e20345000103425030b5800d10000780041d000b044c540110345000e05241008113078608009102e684241c101c00c034043c40100c010400300e007541c0c019082000f400d01300080018010160380340d44192100301c50080204d0811581150b8034188846503800c03031412010b660303d29294940034076039481615070800210402c0c40000d5007001030307041d8074081c0b0350007405185080200d4004403082c50400b544e444850240303880a860040c2205008a90380318000d2010500846040510b400c0c181d047e032019051018003002c0000150705034904c0c8041e55101c42100020800741e013000d540400040c4d0070404a4840011 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 899724037 1250 899722787 899722793
    0xa05040f141e0d0f0804090e1f020a1e2609210909100302030f0a05030406030902041b080a32070c050a052a060a0e031c1110050403050307030203100f03 67
    0x43c002e46031004424896848e0321000c140e5624081d10980d01d03110440705241c46a600c01c0d030005c01c8180d10a2629074401c5504003403598200d111951408003080c0c0e4071409aa010451841c07000159140d24915000c2e49001032a080c3c55880b000d0405485000403450070115444190070344a04080c083c1c08503489240602c0300315070381e18140c042648684629a003080288500240680d0038590180c047c500303040c6401c0d0254081c1032529001c0381d0042d200c21020f6010b41002052040115170741e03480007500d0408000c428111078040462000c002d1200300029400b40240081c2a10b00c02c03410800b41603692030640c1101c485010900040250241d1500c4000780000014980c0103003001c005042d01c00b0303402090340c440300c4420711400e980002c800e2095800c02c41c060200320030390031400380580e00c0408180e104400d00301d00030130703d00c0f01289552801800c041002c20882603540038070b060800003401c20b80c174042c2c80d50000401182c1016000400035075407000c03046424000304810491151855240d203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 899725287 1250 899724037 899724053
    0x20117091e011e0203071205060604050d12030605010f022e110c0c0a1a03070909110403060f2d02070602030c0307020f0109080904090302120a05040f141e0d0f 70
    0x508039100c01e0b0107000f9200c4030b4208900c2200d01441403901c520b06207031300910303140c1c010b81402465164051003d100000b055228098100211881102400907150351214060304452481d000710f810404800301103010079070005040784c440c1c16802101c1c0500c03176001c54152010410b40d81800510750409401100380311046000c2e0600680c5017003603925041d2940240030300400c691091070100c8142c266560507180000e0000c603001141441c0c201c8045880d41d0300b0301c0070348400c00d51406071404000b8042040c0300c003510414501c04d03455641801804080420b580b40e000743c2c04000691015030b80c08140065409030304542c01164050403d40d10303442d03c000e81140b5a041101c91380c0150103400c0c000303e9900f00c18403031505084d900402850500390304005210082c0800c91085003540700d1043d0700340754940810050424013a45075100c50381c1d00e00b404841040c1e0301d03080c0e0191039003c003400e070a800680e5550058854500810f07800e000011a28400a0b03569140c40201030030344001c0c288050248a604 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 899726537 1250 899725287 899725301
    0x4020702060c1f050c1e1201080c011202130504111207030f0b040e06160207032a080706020309010c0f2910060804080304020301240905070c020117091e01 68
    0x19140f030410000600380c4040503141d0031500503000840405c040c64511401e000100c0070060700c0074032103040c40603d03216801c080200381c202900c0c5502c1041c0161580d1fa000d0035010010005020543c107002d101300e0000300d84181ca001d0303c0e02ca542c851400b010000e00000a8840c0c0c00300c034001c50441402c01d150081c2c0102071410310041542d040100a9495080c24025048681d0060b0010003103680c41c10a41d550009030020b21100310b00a003c80000400c0d4185081070090400020307400242d5040e000b100c120015941c8030240e26086418200b01140e004420f588880c1e0f030070f0074420304184542c90308080390f0200160050081c03046aa80518282259a0045506101e14803da040341c840e0700c150810030044e03102d1200003d90b16000240060782c1d40c0091600188058004505070f901e8094144260441c0d00700308107664850142009500114003a030342d0041c0103803d00d40c07044182500000c203481e42d04412401d2901c112000b05103442001c014184014880c00d20701112440d00810a502070486 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 899727787 1250 899726537 899726563
    0x304121e1d0a080a240207030e130c0c0305030a090c1502071a041e081e010501050f010509040218040e0307050c06040f0302121504060b120a081804020702060c 70
    0x1400760441894145071030400300380c441100c000d01c2240540d035102c403061600721052180025080c00680703d000c030540041e1000e14070a88445e00080080b00501c030605000300040039100342443d004000c01c0f07811140204415415103802603a0b0b81e600440c0c180030306a113501c0105800c0c40c3d00c000080907500002181605000b55007074582103599078020000100d144400981250f40420042107070a1103c65038900440b0700d508042e642c26a10740d040ca0400007280c16881d047c015150049074444028132030b40f4050700d01221200e036068202c100003000360144080c020b003c2d5900040c04066980c0300e2040c0328109900070800e0044c29154804c160b242d070131207070007143d80e4480d11601d100300b07240000944050ba40e10400e00003095240d80c0030002884c40350300c24403001b40aa11203014080d00e03681404c0348203d000310400324076102c0e43c40a000c5070086450404540382c0101002400160950b01240c200c03480494180d25145e02c0800003a00900c5074001c002d41c45800040c91074801c0300081030040900ca4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 899729037 1250 899727787 899727827
    0x300702060f270106241e05041206090501090c0602120316050f0706090b060f010f020c040e0705060d0f06050a030f02130b0402121006140304121e 64
    0x54050058401c1d003425210204a000c4007a00541202d0240d04101c0680200b54004161a591008200c1040000c050019800c124918150740c0da103820549030300000d03441400d45080101781081c0104103000e0b034003030410b003c1d50201c9201e060021507080450f406400c030008200403034440c541003420520511580015008110042105804080135a4411034640181007685180c41100303c4159020055020007883c0078003c802c00b050451040614080c070130060714144c1d0809008008070041c1480701141003080e92041c0401032540401c0ca0b0051542c15100421020600c05e4528108403154003d5904500e000c964141c41d030110350460300400320340286c10841c2c192590309021001d00c45000290002d031144840d40014103044000c05070381002907000240005a850004099a014034480c40e8200110f2080c40841e407440c400701d50050180e42000940c0d4004400840320074080108007901e2112074030f030100c503080e000b892240ca54120240c041c6008903140c0c000601040c0c4200700c2c0c000014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 899730287 1250 899729037 899729041
    0x60103050c0a0804170f040e0402011812060b0307090f0516020d0c080f04090e150610090b03090114180d0e0d1538090c040b30070206 59
    0x80c0300316003110b11000099807000722030359841e02c890608916906850120000402a10200200350006000606000034403842d890515000040641c9017281a500c403400c5131180c1000740f01050140801410b030300c4200030440c0350f14100002d04107002d5501000701142019550328800d425507124520640d03100708602c0b9000d21a180c105d913074030f4040071594040707807203051094003051031070010344828104118814a841e48540041040c1c45146c4074140465020300d0f402c04000000758035040c1e02c20016515400c04071022440101010202c0c89203d000c00c0c4d001020a40fa40ca00f900700c2c114914a840c800c8640741480020a151780c12030f401c69a82e540260009401254407460045000d404028514204121107860b9000322110400c10608519540d116075a5801d0040081100440c01101d24a500359908440b54080b5100018154461b42664041141e485040d80554059603a00c0c0e01440d1192812a003030070200300a690004c04020002070901c3c00314140039100f500c100800e500344c1e8025 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 899731537 1250 899730287 899730301
    0x14010909020a030f06091b05012714010c0807110a08010212240907030c090e040c0b0304080f040905010f0b07020109031103071814100e01050103091401020c010506010305 75
    0x403800200001d600481164040020a090a4401c181319010f8940006c05c82000e41e940c9170710070070700c1409550481103148200f00c0756803c1105602c061001f1038500058000d035900704180008580a1852000140e60400040764464120060013580c80607040313542c0c41d890300307100c0103c502c030041d5540304898a000101d180601130090314102c082a909801003600c540307540f01c140825030b091401c24034409504d000b100340d58448074940900c045480014080584110041003040c0b1500185000d5084805110006900b001e2410480f25201c1c0090b4403a01d035450224001c0c882d04e40c40c03442c0910b0109010402d40c1c0746e03510030b07412100090032a030701a036520440081d56000780007020707000c660380020130000310301c6100d003d100341c00e80201950482601e039080c0901008241502c0000d441e91050f2140340c040103140c00e01c0d00840124151480c041c90050060002c44050242a0401d611408008200403819001648901d4007800039503d4070580d42869000b06011141c1c01d000a0900c00402c1b0300c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 899732787 1250 899731537 899731541
    0x6010902041e062c090a1b0c0506011e15271211010e0301020703110d0c0209071110090803090c2202031305030301030c0e060303030c0409090614010801140109 70
    0x1120300e6602d41502d07031911130240080d5500c42c22820341a0783d9020302c2440703c540d034034280c50f032044100e681c0010b0042c40d19240102c0c0119805149001d0180d9000c5110202e240015094111040004111801c107203060034400c404525500144043d184441000021504004c00040400c604241703c0390800c000302c5400c02d10b91040c42043c1c4500a421414400b18255010802610406040c020300f4040100042401c80c3d01140c4c0036000180b0110700288400400c0c4600303103088000385840d01c810312040d00000d800800180000007844220303841803191031400d222415200c00d14038010030081c4950b081c0740760b10303130300c1100d5105840c010b101d08440d4a14100394403511500300000e404d0905c00c0c5506845009504c054504190401106030607000164100020b5020714410480800100d20b0444c4042d8090b4002d05058403c2c1c2082c81000703516580d6000380d03411a0b020b80400b04040c142410b0070001405108165000b0442d403900210f480e00c01504a018202840d040621701c5aa8a04001342 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 899734037 1250 899732787 899732789
    0x308190e0f010c0515070504170d05030f10030c060302040311010801150c030c0605040f0b420a0303200102070210051c0207030306260703121106010902041e 69
    0x341c015111000c0c1e07601544500c3d90300f20201d203c2c4003207030030360a200843c1c5070b2454001c4030000700040c0c0010f000e10280b15100400140a1410700c020041000c07945805051400014142c00081003080c2c0041c00324000d20a0a8000315045038030301030040d441d0b58004002e5802400180d9000d01150f4880c1031551084102d10b049905a83c44d41011000e891021124140408000d404104c100c0a81502240080c07151502442c407420440511035401d14020304c0701c10000b007050141c900c1c2c440d1444020084044085240e110180103508045080e803400304008080c041c14a41101c200c240210805400260001c0c0b5082041b501d05840c031030b42003032a401e0b0700c1b884000135000a510004490100d001e8030103800c85e450340f0000c0240d8000d0b104506004c0f60040c0c5002c0e80040e803036040030080b44483d030040748041166008401c0c000800c000c04680c2d1550a03100c01801c0d000c0c134404010100e813140d030a5407451b0200c0010389210356034074600400650854000c6841034070294004585000761101e080b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 899735287 1250 899734037 899734039
    0x308090d0801053001020705061e06131409060a050c0f07060b0f0d060603170301081b030c10020a0c150206070c02040209181e0c1b0f070308190e 64
    0x81c19a030300700018001e07403a42c50400310910180703c42c21100c1c8100c00c0c05800070b59590701000180c50384c14500b0301901e8880c02a09615503001030070325405402e800d00c3e9016501c000e0681708500342d50b51601d00c280042200030b0001c4540c420480034000300681c04a03076103004401148040c0603949a04031000d40314415600100345c0000c080180c0e030005003607a0025046c10790018020f2000b4640007004c10070aa207041011a80c960380d40350280100078214414110703020800d00c8040c215070600003e2940c410070310485220854107038411030310950382000f0000c2c841e0b10152115090500019001c0c1da80d0031059804c807040401341c940491000b09a1403c500840e1080c1d009240540b80c41005641340c1100407002e0b6041038080214a4207519044c10410381d104400c240c03001c140c544003c007100c0b41d0030b078001c440f4825000c4005008003082e8400a99003024620400301914110b0040d00d1841c01410102411040c02049400000d000060001c0c14201c03203078040307803114800354102c100c4401e13803074034003403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 899736537 1250 899735287 899735297
    0x31f06031b0c0215040f0e01060f0e041503152901080f0702070803041502100e03030a15030b0a091b2402011d100e12030c03041e06090308090d 63
    0x703812a40c03160036003085950010f01300f24100c250000e042d41c15907000e5082403500e00c00c5101c0c02c11040201c00c1500d030060203c0e140c01601d08604400042050a1304e040041c4501c0d210340c00b0070b4502c41100760800041da484102d0301008081860039001511301b0320901d6520791221401c062012891100248500d1016592003244d0340e81d02c0c0400844540c0a840c1038218815254082a40c0008100402c082e00350716003041c0b019105a1002454508240381428001c0e0500d15680c2c0d9a21001080c0c07a00440741141c0861603030411280064000c42e16403010300790f5078600c810312240f804e16a203c030040a008100d03500781d0f0100e8241d040d0b02c000c480d10980c410307002c0c00d240d90580981140c810030700024191002150b032841002443e41c00340d6805040d161141c00ca000e251440d42c01600ca03070407800c01c0c000058440940c00d004100420b01000300301a441c0e00c0700200080401c40321030030560107005414102100c4884a0800e18000d08803840308a012134075400110315090f10015040640703504590ba0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 899737787 1250 899736537 899736581
    0xf0f0609061a0f071a0403020616050a0918020f1c110f0406080a1b030c0f09080c06031e0f1b041202040e01020915090a0b12010303050915031f0603 65
    0x1a002c001e0b801282c0a64200c00301410145e4812200c003480b83c0654002d6008250340e042140250003070710b04207200c0c102070000c200003904105802c0341c3c070901214000010403d82e1403540740c503a07020b84120220b002c008000054030000741c504500303040d004030105d11400c100e21118601351800e04d03c074010300c00526203014130007000100d101c1e1441039840810000d01044400c018003601c169400c0302d40031f44010907120384406181d250300c0b4800b0103580c0c01d03a2410403100e41c60070400c1600c6000300c508003409201c0000014090900412191184c4810200510120329200c01424040308094894100d01d00c000500c0b00c507070080c1ea0301a2420341d0045072202e82400a15402c100c01800403140303e03241c5540a001705001f90382c841c644241a2030112500641e40d080c0325041040940b103d401404030302009002c0d10384030344100e60701c02d41540e905090059640c4c0c190000984030826180d00c581c5008800010003114155400c0e802c90240006104800003e4a0f110140c09607030001e6219141c200c01668 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 899739037 1250 899737787 899737807
    0xb040f0b1c090302070909060504022b1e232401060806130509030406020c0603090a0210110712030f080910020f0c070603090203191a04060f0f0609061a 67
    0x301c1144824804e004a130300039551030840800b070b15a001001d42e104c9944908000640c00c02807824105151210826480841d41300402058034104003006080d13200990109005982898180d00156130003450289200300e044040300b40e203864083e1400414083c054801c1c42104076140500301072544d01714609110fa013081401c5404c050001d100c15803100c20200d0001d64a00a48141c074058510380028660715420042d02074500144040c0c10390040f01c00704104140e80b9004102601110790469124a0141e1502000c50b40030200440343d145d40c0c020544001403070001e81280b0948513110752191000c0c2c1d810500142c5d4502c0301154407131400e400ca42c1080380c1c000f4083d4003d0003564000b0200d00d040ca034007201075502e00142a0000c07000b007980d0704000c3c400d5160400c10041c40c01d0f92007507171440044040d59445501e9203104400303508200b20502240c108683c50300042030720000e4080030014030201000c0f010240405114680a2a2a09201003400d100044085110030500301e80c041c98000d03904 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 899740287 1250 899739037 899739041
    0x71202061c020d1401080d0c1e0311070608040b070503040510230406150b0a0c02010509042714030a02030304080a210f181104090512040b040f0b1c 65
    0x80e00c9200c641d0750800411105903501e109140810003005120040c540c18104010b00e4003240211000622441c500444c00043d40c0b00d0001254405203a00101103142904e0241e0740300300604024101409004004144540d00800340c5210b580141400700c2c03c1e0300d60ba0400d8503a03103c1034074042c04c0b03504132110194000f40207401080b4200311441e020780c00c540c11071860f840505000e41d8102c80700d940724a0005040315218080001610407500c032a86081e40c4514060b1200006010080c1801404600185156982d900030464032044103441c0d85c90181b0078444903400d011402048a03d2100030000c00c00410f000000d40d404581c00da0004c51444e01c0d982c03a4a1030540180b081c4004000c01c041070349583c0002e80034450301e083c408000205104882056800549412034510f080140b040302c96480070400601074910400303030540740040d0100550501170304001d0650403007170008000180004420784901c0003442220100480c00070303142c0d20b81c01c6200e09803041e00c09841864900720f0400000501035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 899741537 1250 899740287 899740327
    0x80f0c0a18050d030e0a051f1809051801050702071a0705010207080c06250e061c0c020a0201090f0602070312090801050c0a0e1005160804030b0c04060207120206 71
    0x445211866581c0b10009032014985981c03c80000d100701d5019512804c00401c440080c1008072124161100c50018115400c07041e03103041c0702042091501c180780402110002e40103003080c08428030507881d1200c1900011201031500306295868540020a03081c4041062000d45800f844240181510303912078040740d800c0b1410540704c555007040300100040001c0c00030000002c0c0b1a010b4506d0b0310b845084405008a10256146400b1081030200c0d606544800c05c07485422040354065282c144171a803041504038104a1821070510b4000d01c00c9031a900013071301c2d440061007661160780c01515201e0501c01d41e03031140300f80e10140c0d214460500020740d040d0050041002c080c6090f80131103540e401041d003914030070340300c012001100080c01500141c0c00346003c5403030360050351030410440c29040300038514852030042e5080c4416408400c1e08206240b4110f0b0025034104040311b181d410714074441082c9078094414000544130b819400647c0c4005160744400b0036400070b140354100008014100220300752 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 899742787 1250 899741537 899741567
    0x5070603020c1b060301230306070c05070603141b0c06010803041701020705031e0d060b04031a06010c140f0604080309011413020f0117070f20030f0a091212080f0c0a 73
    0x8901400e215181080210310034ae10b140d8030750760b0a5646007413103800c0652a4004078201800c024010003402d00074241c55030001c544040821080e01c0005000b40207014940e41203281340294000050003540c0000075100355150300c0002c002d644005010300d0b080384500040100766030424040c1564801406540644141c1080099440d045004500301c08544441d005600d100101250900c140300b00400200e94699429186640909003100080e00886801000500d20300c0101541803000b4010312140400402090464426041c00c0c41c0c40c0301d07150011108008030358030307013140aa0700c0c0b04500811401340e0311205a82e4615003154080c405003c40f00c00c0ca0a062000741034080c5501c1504d40d03d081c0c0300d4102a551000d134a09c10b0b12000f4050b03104a05440b080c0d210380140e5014841c00403040701c0c0001030150082c0d0f0344000500302510041080c3d80140c0040c0c0700070103000c050005049040000500720348c2c82c205155038040320003500741010b643c1b0520358242402060007050040c00f1100c0c058035 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 899744037 1250 899742787 899742839
    0x1062702040509040605310b06190905012309150a0e04060902130c0512100b2803090825060f020702040617150a0905070603020c1b060301 61
    0x240b0759000c01c11400080c3e0302110610760f200104810a2418500e030080100341d21190100c1041f0000225120850b41c031001c1e09120850000c50800d6075071102c500580e00300940a11011540d42e042d07040205001d11903d000e5102c50312001d41c01e01e04100c111182c0351b10061080700151111b134044940304420050242d00003158180110304600c01d1007865208900c20000894410094130510003030384100300c02e4070060350600c80000d64103500301c01540c4c442007460185010b650307100895a400e8000c23035400382940d6000040c0000c118000200d030806500b0f45008051007240c141e00c412002c6034401400038045440070b00030ba284504010746400450840c207803050301040e0b0300303840c0c0c50100e82a4640c010f01856001440d1300860415001d610010020f03012440300c59001004101e441e0f8462200c250300300d0203410001003070102664408101113801804981400d070300c8203070241c029031140d18041c4030391107521218044440f031800702c49400d0b03901074003060035a440e040240c003140800e5550b03003070540 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 899745287 1250 899744037 899744039
    0x50d02090310050105010e04090506070c060b090f1e0709060c24060f050303180103020306010212130306060905040309171e0703060606020a08031b04240f020106270204 74
    0xa40c0800c0100010054030000083c1075240c1000502041518071030706004034144280400840d0010a241c2c2e480210b13414400810505858118002d0207251285503002e81b02c0300074043c1d00c10f600d00300f00e48550803100c00c008040000c10f04c41d08070058220781d40f000042502c0c4060010500c02e44851010398840c0c101000c0248854a608580c00003004200303080a035141000c1040c03901752030300352009003015400380d8541212100c0e0303000307446184d040b89818945c000012440c0c40c1d02c2000300b001d0210b02542c520b501e8108a0000c412101a94842980c4480c2000e00114029035180300b0580120341c0340d200e103410285810810302641c08400110000e900a4068201480e0340080d20092030f41c00c00805040807a003549002011a0100e400040071940300c01100300005a00c60126600101000100300401c4003403007603110b2912840d0042040c01c405412024206074101050403110074a5454103130112908040403800c0f04c0c0e081c8200e148240c01d4160100a0040500b0100c81c14054480701620781 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 899746537 1250 899745287 899745289
    0x50c01181404113937031d04050105030a031d0a0306020405271b091206180d1d0f04091b060512040b060f1c050c061306050d0209 57
    0x20380100036031804906210050030301c00c0c4c00e110301042c6691074401030740c0c101c030b407400501954030b040035450241c0c00075a0300c3d18101401034441001070710840402114260515500d0000c0580c40c103254943c4007480010150003807440e06009990503100c020340141210405500c0464a411403500000307000342c3c4180c1c0210094484400d0b6a0140d8090130307016036140c1c0361a060041e189440c100051030040e20060078450f95070802d61070b581207002c7d141094100c000e03e80d0f003030301c3c50310620210903402420000c101c0e0321008041070b01c92050300c96518840d403c01c1c540440701d03140c145c094958000618200103001068501c004044443d0401400500003942c4003400301d8203c7c0c03940c00040c0d80c9541c038240b0200f8802d4070b03042c0030005010f2510b0110b0070242c0e040c0186a40510107840204100000400140e080e03d644040c041208002010024000600d04159030f00c090b45101c03d8845001e120603440d450700b008811500005050604800c0c12850114122407030b401070380300304e00c0c0e9580030071042c009 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 899747787 1250 899746537 899746571
    0x4060b1210150530071d0a0e0114010e3d050301080706030b010207060e0102030d0501031b120506150102072c13030c030503060a0905010b07050c01181404 68
    0xb0390026a03e440d6540c02034484100601c2e00e04203054081c012182062140c241012a102c079000749150914440c00c40c84506d902c1070340c01046209a41180448400090884883c00418125140c2d942c180020040080044408440d015502900451040c0030800305400601c070721044040310210341162511022103102c44c2500300001c920001b400800144011035040c4031442c000d1070301c0e0508209407001c060020b925004a442000c003440308100c2e022460345d00070b00464400c20503818007004550b07100c0c035180c140f0010181081181d00d440c40b17000304005084546207011103030410000c2c4110350343c580d08612a0f500801c0f60b44c3c110b02070180000781d405030318405000c0c8000301a00c502516030074140ca0042c2010014040303c3d0f5031210304446070103c2c1d0004280b060254152030501d56998070040030580d00301c440c0d4000e00c1040d140100014109c8203080207051107038460010ba450303010380e41c401100e14950042d0003000034012850b00f003080d45506102212044030140001c00d00c1800d4100c03000c2c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 899749037 1250 899747787 899747819
    0x90b1f110f030319230708071b061b02031606020904061e061407080a0f02191a01060525030c120f020609010507090605090a030503210604060b1210 65
    0x1c02c020800950813401d030075026441c000340c1742030110b1184d65000c0150f500050006080300050280100c00b28044a1103410080300c40e030044503082c200080146030040040c95003480d031000d00610515401001403005c0300302c0d4030040d0680341c60340c584e55880e2034200c005e6001046869100381da550001842200e581108440c0c4071507681415040c2c0c0c50800040c022104030f00074480741441c00c00401000815441c00c1da103000d06140b8100ca085030700d40da002d91900610410304000d00d406090b46104002d5280c481841d070b8628150620b2090f60b907600c05595078040ca10b1040d40702200c1a000c00000c542c48404d400d40c00d402840d1111000110741c80b813072040030130b500001000401603c100c4034021f404105031a0451503200c001c02c0706192407540284401c115002e054100040025000a00e940700c0300000c0c09190008156940d60011380c20001142d0851310410f0100d41c82e03031000818900e40ba21683c42110050341d0482d1600038031402c213580080d0010b02c9001c00901114000c14500b0032404044 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 899750287 1250 899749037 899749051
    0x41403010b040c051201080601030b0a020706150b07150e15041a27120d0c0909050f0106090b04061b02010c0b0702071e030c0501080903071506090b1f110f0303 70
    0x2545c42c00005004880d040e01604104a00d6014034010000144641c0714150701001481005849110918200e0094070360035500c003520898015004c50040c01c40d13401846141c0c072910840700760b40415900003080c0c07003981c03c1d04405038009141c4008202e01d030159032540980309402d0102c101e60070484141031000c00b901d03040c0c02280211031040c130310b000c0400a103c60105000c000c00394420410030310502c510811401151060301d030030507000d600c4d001d411040046c004000d001d0020b8500580c0d10a44044244102c400040741c2e4480000c001c00500121400d8070180c0e5207444e1840012003003002008039401c3c04030304006000c46048c010400c1b0040d600d0080c0c6481e809451041d1400740e01012410031307504401c0e4407440c0c0c2e503000c10001d104100070800b1140c080c00c25081c3c1780c0d603403910b1a0441c0940c00c00070f8800c0c141403106403040041d96009500341c5608036404c0002060400038800c80140c0684549640c0c042180c20408450081101900503a8841304a0380489200e487c558156001070300d4103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 899751537 1250 899750287 899750297
    0xc0f0d02150f0f01031209031406160504080a0b100308160b0c0427230603060123040e07090609020304020f090f07050f0922060e0c041403010b040c 65
    0x10410001034040d215400c5180d0b080312a000c0d003802040345080700030600c00102401c0c0a0910841007900071601c1030020754101108a4440c0c0300f035204152100e404541e10212201d0b10240340781030342d005509540603203051a00030a03547d05a5592414000009010f884c181c100e003001c0000010a4a001040c1c1c1c0303030b000316400400304003610f841044000041c0401485000502060102d4a8840100d200b00e10461600640e402c46043c400c600826040202c1c20805d078041a20501d11100414458000e0406034112801070380d03185c07002c0022400345015511101583e005c4041c1c60718040d0442503042040100f9600b46035520201c0204031000f0307a102c403100a802204000075807500e42200c4481e0f10701a40c0040091030704280306400c0b0310b0000c2911040c0000070801c1c000c01d046a07000e4516100e030143c218003d1034105000644141040b8540e01042400d20350040390044400d58207a006072000c0150751304107030070000c0300c0d001d00d02e4190b5903641640d610140500b0f030355070324040c1d107813120819112 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 899752787 1250 899751537 899751553
    0x201061a071209050310020304061107050d0207050f060403030806120d020d03051608040209181209090709060e0d020103020d14010515090109060813050a06020306040f140402060c0f0d02 82
    0x1240b00c40c0c1e000d0800030144116070608028030f0318080b0300d03080d10380303001400160b517a0b4070362503c0b100910802500c90f015401c0420106c042141c0003401025601c560713000c0341c5001d030340c960800c66905d07482d50519400c00740502007040081d0040074541c0d0011030040c8102c41c15814140c07071616125070b0286180059001640c05954290944036058000841c1c80721134801d0301d11410040d100d80c1e009040240613020b44000100b10401c00c0032a0b401c41f070f44650035208605059203c40c03485402001e40c1601c281c182c040403c060314040c22495080302d403181c0350500485281d104026240e4554881a41407503000c002d40d00140201748a00034102c840309d0440d010365410203003403240014a01d209509007000c100054016685c10032880011a225032820b205e80d5965030015220b6110000d40040c610320692201101300140d07034002d5449003409035010855600041c040340143c0721300c50a07034203400805501003005820000c0042040411420481d03c050a602c5211840d00c2c032141c805a006800c0300310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 899754037 1250 899752787 899752793
    0x30b0c3f09030a0f0903051b03070f06020d0e0f090c0d090c030f12020d0e0603150d111306050f040b010201090c0e010302130b09060d1401142d070e010201061a07 71
    0x44520b084140c58601040300c142550790392940d071541101101d407088d511034078040b86030390100403030405440800426040982d4462001c0d54850000005001044403445603e9940c01c109100c1d00c101d00f0014954152926050162219540202030803000940c54460460102e44084501c00c015842185600b44007a1603090500d468407804a401045402030821051001ea1001241c45581d00c202d90143e540d440700c92801d51146184c0914542014864508000380001d00703400c00c402034819503194840c800350600700300403155107000c2c2d00e5001400200403803203814a40e0040d80b0914040c000003500c9800382c0c60b500e16410040d4408503042c0d80380781c01030045080081c103408d582800e5480c10300404108100240003c82c000700f045000d0707140070f0b5504007840003216070112810341460082000014900900703500703010413102d42e0700408400880341403080e916030402142d80710400e40701045071140301040310000c2c48407e0340c43c119034841c100410503032400c1c4180c5c45135a00b6008607070b13951a4289 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 899755287 1250 899754037 899754047
    0x20010302160506011a0f07062408060f0606190806061b030705160e010308090d08130303110703020609190801021809161e11070f030b0c3f09030a 64
    0x240303c12507035541c203200344078140031a46d050701c1d00b1039480000801d0315055103041240204043c0187c0384901110f2500041038040410364900926184902c04410b94030300060100522460803025454035506c1100746007140300302c030640e070040b00c028211071030081d201c1e104c1b84140141c085031503016040082c640c004c02004000c000d06052002402e440741503e42030f40c003030301d400301484051b200f0100010800c0340c5e550b640c2100c5000a80c0300000548844080409041d0022280000c502003421141c0c82401d40b00000713a03010803654014110707132804400000b030043e640d007501c03a9802c1003d80000c000c00c50300c4084c00a0094404100320040e083d8903400104000c480380600a10854800207680524290b0b004070701d20840e0301d0681c1c04282d49595403030300712040755003104c02c00c005000c2c401012800c4021040300000300c90013100540c1164070b8503200b00a09210f00070303842c0b4100000c400c0c02580c0e140c000d2a4031402c01407541e40440c5991842c2c1c020300001c02c08072030a00300b98100181c0c41710300c240c00c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 899756537 1250 899755287 899755319
    0x1141b0f1f0b030a030c02041b081807030c09090f140c0103060b03060d031103070b27150112020d0204091b0906050114180a08010507020106122001030216050601 71
    0x40300240080c90486002c00d1300da0781050406020046407450203825901c49030450f03011100310070b12440c07840c0005000180701e206d09403030003850b00044800b00300c1400800146170044ea0303007101911100a203410403e138020000008110340a1070300311582e0b00810344050015541800300740240c000842620001021500550400d0307580601c140309000858540382d40c2c0d80c84445d8907040c810b01032480403900c0c2e4918050880024110b90707424042000c1e0b014800100340e90070b4940c1d075000c480c5011a07011a512011079058004039a0850b500401059440051021109002a0590360a4412500440c6c2502c060480c2615541000c5894043c00c0e180f840c2107000a00710010100001410000020035010321f0745125032500f1404030f89800c541032a014180d00d130010062010001a5850441d140648412901c420141d46400b400160380c10300c511822022a40c007001c82d48154030880121002500c8100006041542c00d01c0900807480d82844104c41c1d01c0e01a500528003903140c0b40000c0041d4100e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 899757787 1250 899756537 899756593
    0xc040606110c190f060905120105010608160315141002030a020a1b090603210216060807030e0102031e0c071a0712050c04140108010501141b0f 63
    0x100d800c406600020115503403605020448540d8010318004500d08071200407508121684c05080c4400911240c000c8122401c650b41a1114003612000d40841d40c200c880c2449080c0200c0d48020029242d6410300311902e14044141c1400075541503c94240002c141c0c082c0c1002c040c0303001004c41542103290050b8030801c1c0f001184011881d04845036402034507400d0188000703180740140c0c14840e903002400803802c03000e0954410100400e42e640e0030020704610341009100c0219503c004181450b910205009107a0007500c90105125840e04608aa130100000c102070109031741c0e28010b00e01c520302800214040c161417010442035205a03d85500d5000e0b000c4c1c1010b9601c40c04004c1c00000403102c40c09805d17040b00ca401d01c411983c0e81c04c81d080d1000200940499941840c1c4002c000e101720b6408003520941d07206401c000403400a200048da0311100a0007424081031092214050144000d0010300d0000d24482d6202e800740d9010210320314101609d40010010741040500d1140392405504507030394010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 899759037 1250 899757787 899757797
    0x1060312020f07180b030a0f03080f0a020f1615060e071808070512070801050a0f05090d1d03010b0a15032d0c0302070b040501150504151e0302060c0c040606 69
    0x444e1110710341c4000c0c500c20b4600001c503110540c8040b03554042c8903504070203410100c045140f00c164078005100310004c80c3d0f491080f00c000000b25003030300701920030b0310702c1030021f10a481d2a20404820480d1882c41c040c90407518280750f0101600451b51030300502e8000c01d500c0744021001d040c50203001e015041c210204d600d05115070f4070200a6501e0018000044640540b049040342c0c07954000c4c01d080903143e4201040940c200000e00290007140d905ca00c0c00c40440c0760382000551900f0301d500d6200c00480b4110340014018603481144072034404980024501e00030f00000740c48440300e000c03c40124065009404103040081800345054141c042d90103005450183e500c0d8401d555008130007006604078440032126903d00946c00e100e8000c3c3e04a035122504000c403841c85207003924095000e0140c91148070001000c0301c0b00003c15003024028030340c07a01d0484803180300b2682001c041c0d0000382c0e040f01c1d0500c0312110707600c1c0000140e00c034800108421044500680405903104082c041522100e82c03054007041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 899760287 1250 899759037 899759039
    0x80603030c060c0d200406030c08090a0b090708011e050f010b03011a13080102180a050a030f0c0e040312060b1918050303040b090a090b030c0d0302030c01060312020f07 74
    0x221010442c02d51050743c8400654568041450990051010400c0143c95100d10a042d04440300041e028008541c407940d418400c60214071022034030300b134066501e80700c02e0341f0113109007000810340070312a030f40212030700c2c00c0303030001e0355600140c5080d01c0726002c590701d40c04012023120300c48207014000d030b0360702403402d221b08405940b41205d50f62080c40305101e41c484049080f180c0003680c20980007101c0c040c240013984c0c442c540340c0700d4900500075404005007200d2444000c101c1c090504159103070808841000708051001fa245031030700040e04511501c100c440e481c01a501080b0000054080d5009034000d940f580041e03280d00c1c00080455100c1d421203240e07030b9014006006014140f03c0b1259480400e40b40c0021608510390300017918203883c2d00026858000443d021071990b1015018040c03402080703804580b0b0541c0c40c0351441c100e54003086107a070103401c10211149207040c00c48011101900c00d00c1124600710313510244a0840c1c100c2e403c21170700c144625114101c1c290741044440c480c030303140002800301a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 899761537 1250 899760287 899760307
    0x903030818060c0d0f061403100501050f060d0b03010204030323040503030708160f0302060702010c210b150313120201050f0123031501051c0b15270708060303 70
    0xc40d00201039001d103242c00141200000d03c2500300d5405210045c605106850711249407502590a4400050207440340d80100c10798070100d405014100d42c80540800000311900041c014294400146126001d072540204285070310244001c000540c041c0c1d40da00780e40181400c101c01400354680e040621000240400d0141e6500403084441d000e45c03050b400c0c0e42d140c4910041203180028450081c04015001c0310300000e140d00030644a12486a542c002c10001100ea50203444c1408143d141d10004004a074140641d518039a1110b50b001000070a41001c8541d190f036416042d070300403900800789030f016121000400040418440300c3c0d940c41e00080c4240e10780220610000380d814400c410701c00d106200490008501c1e45201403030408064140c4101c0504010403a010303510a201d201c0c001d000c01c40c1c055400b07104180003050096400001c250058403024040e45000100c500d00342c0c1d0080750400d60b180c4848810b00e0b0001d1081595410418506c0d003008040c041c544010b12300780c0260002c101c0c000c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 899762787 1250 899761537 899761543
    0x509040603210306153018110d05061819030504080c0d0809041a03030f040e060d03050d0e0c130c02010b09060f060d02090405180f011b08250903030818 67
    0x10010070181d510a80d030500c22a06007600c5450038a60041c0d02e402142da00c1c2548000c50100001d0123540d05c141001c01007428411200f100750700103046500140041114080c0003100d5814501100c02200e0303200406001d2244004a4000d0440100fa00001c0402040c0750500c014000c0f50000ca44c1c40718004169103500c3c3d402e108500c00130384200c1e40c0c1d100039070f090300e0302603820610040060101e0342c48a403442002e5116a0090042c03a680c0351000d800030b6650f1900ba03092180d240d030b042c3c0e5801c5c108246890f07228060941300345544450b0098407102c06254072481180300305054101800705400444081c0642101c0c03c41030300303e0040b040002007080039180c1e4004411540003c1c2d500907584d401e40813580009024421855900c5400d1506000c5845501010b031005011303040151013140079035400d42803c80c0e40c1001c04902d43c4c89550381690f4840d004442c0c01c0d03804010080007951081000c400344800b120181201e07004150040c1051040c59030101d452640b140081007072040740d1700e0003d0307841d903 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 899764037 1250 899762787 899762807
    0x206151005090103061806240c030f140d06061704260f13030507060206061c020f030601060f021b06040b090d0b04050a15020a0807050904060321030615 67
    0x400d100000a8142c0964440d61081000304441c0d820f912454a40440c0c02d0058802842510341c0352241c0d41c0b03141e00c212210b0f20300034407030b51158079901040609503905680300d403190351a460a000403070302c000c0408c10420b8010941151140000500c15080217405084c2011004000140807620400c200018030042084c01c14510360840440d84260441c0c86201c1c0b6105140c0d00c002c5901c00400e00912002450713140c1c00c1030324441e40c181c800307954a401003240d0380c000850341c1607480000aa08442d000148403d500c190b01d002514500c07890040302d020918040c0203900107400586003020440070700c0e9040c061038800800310583c009004401d040010b02c1030146004820001c40700244c0c041003036683c0c00ca141d500592020002c001c92503d42001c940703801e44004250b403c0340d40034803051a0103c0c02d200302c071007890f455280c0307020360384902c54222035680003034807440d0308907640e04408004200c01000380413481140549020103940304600003410f48549130701502596090380812007803c0d4100000c21 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 899765287 1250 899764037 899764069
    0x10c020a080c100f270f0204050403030b0301020a021b15040902090105040f09200301260c031e210d02072d0c05060c0316110307060807020615 63
    0xd80ca5014424200d4140a11140515a524500002400c44c51096000f40c0c100010007504420010160103803c5035041d02104020000400c001c000c00061909600158000e4040c1c81c001501c07103140d40120f0708a0b4421b81c001009640105040c440001048075100c04110302941c200d00444144e404c2d45407680a9401902826500401d810032a6440750703095030000d142040400030340d41e6441080070020101e5000315140064411514031500148604490480d5040345402070303403040d90251040d9003444010352030600c0c0244ca0000010756410052400b49100d043c2d0104031858291041c64a0103100e00181a91940761035032103000380c0d0000c0c01b5a14007403040e4201694400719441c100b88100c0608a50f40384828403508648000205a03044a02e02031007500d9690f2969111800c0103410b006076480d40650717a104008561000b1801c141c1c410003140310700c1520481d0041000000c0c2003030f248d40c00c00c900061010081041c21681080f64580090071040d01c1d07040c2d540e580340803034441880c4110761 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 899766537 1250 899765287 899765303
    0x210c03010c0203091c051c1116030201120f0f1406120705271501030e070e0112080c030406020a022b030e13060b04050f0604080d0806190b07060c02010c020a 69
    0x17452005015910104456400302c2912011515020100c0400e07500c00401c00c0021900c07401000f00400c0001e100415904075400c21140380d1071a8011580b01d000c02c0e1800096584603203450281080901034803010703103060140491507a40205004405090007822544181c016400c1e0701d0050201142c44000c3d01c0c8141c810780240d5902081c4922291981b0000c41d020301000010010f21665003040e00b05018405d907000c2c0041580c80c0c1503940e030b80c1c61500a4444c3c106c00c480041207a519603041c0c61403091f11584280e03040210188401e400c50b085a404000560065490340c811464030245805803a0518121002102c0b4242012003484080c43c0d0010103010240e0940061a035404a004c482c004c109030092123a961180b46a007207907009442070501070786980c0714000941c50400159400c1e690584001c002c1542480d10494000ca4081c0002d6003103114445600c00c03808800c1c038900003070007200101c2603841c24680780c4041102c200e84070301400c41e45809001001141c1c00300309a0400c94100d988 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 899767787 1250 899766537 899766559
    0xc0405040b0f07022503020f0306040b070509130e0604030e0114070213020d02160309090603240608030c0d0e060f0307120608010c0c0b0108010605010c0303020a02070302210c03010c020309 83
    0xb0070792401c02c0349006015003442524170000040303d003a40f2102640d10980d1940d0b101094030090503034850080d80c00402180a031000031b40f042d03110f078000d48200c0c84000d180c1e030620490303164601c0480d1400340d240d5070950010402c1109068010102007607800302860103444510200070104441d004095000b8030a020740700d010004040142c060340c0c410403915508654803d02c0348690409014040760442c04600b200701c001030440d41d14412142126004030000d44c5442600c00740b11043e07240880188011039035031502041c0e00c0700400c0a050b0f00d0101d2401001002c2c4400c40280c40c40003103121081c8240000c110f084c1e98214007406403500141c0604140420b401b80c0400b24020f024650807000080d0303e0440d40301051980807144007031090090b070151041c0c0e6240c0c03104a0903900c040c012035021859005503100028030070350040001003080e10590b411184c5903030000b2100e0315806221360984000094403d409541031218000c807003411002000038074010394000c2e417280240340c4501d100e4417840720707 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 899769037 1250 899767787 899767801
    0xb270907090203091c0509010e01140c06161107050a030803040204060312090302130c02121308120a030e0133080102040308120a0603020319260a020c0405040b0f 71
    0x11403005400c8499040d900c81c9000c0651950340d41c028036542c02d074204107040041140340034904983c01003106a44401c091080760005407002d68038070585218488041107145954842804000d014010306e2143e4001c10003031b6100141650f120401c00c85081d000100d0412007603980d00300140480e0350102c072058580c2d40300e00002d4000c1c84180e002900003c40c0c803004900700c50f401004217054a00c2101c1c40c00400d11030b0300d08802150400e0f550007025030712060328036028080ca080602050038062403c0620540c468100b5400d200c1030114070340080758040b42d4640c1251301400341e824544c54980c02000310051843c24208440304071494114100300b00e1540b8489141c1145181d00500b030844020b45d5900d5982c900b80c00075501c200614074030554044041080c1d6010360240d407041303d030000e00428441ca907038158581d2480c0c6100301140c0481400005075100d80100c803418005011035000c00b500c5040c2d030740002c2c0c244a01e035004039214524207000c002c0000d05a0306c000d86c00c640d4040c040c0b072080d59070320 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 899770287 1250 899769037 899769043
    0xc080c16200a06020706140702060a0305090a1509120302071a060406050616020406081b060306040902123304260d0203040606150e09150a08100b2709 66
    0x107540d001203203200c0c0842c1d41500002c8002c211401a9103549800161801d03140f42809404402580044104108800148030341c0005800c4505082998612101541c0341e0344c018010300d030b0400c1140e07110a4082d080c0b000c00d4000a01c4030b0003a040940ca082455a01c4034140c0c0c1c00300b24012070102619010030398584aa900c504090080a06680c0c0d130b500d0b90202078401c080d0501000c0b8400ca041100c00725841c0808100e03041800602006018034a01d280c00708140f039000202000d40195036000b8034009690b03903250901d5054180381c068810b44c6031088000b20941e0340c4074880310300c0940c106013000f0100449680c155200360001c44030034400114200c00c030140202120040a0280003103012101d509083c1e00640c09103119000c1008603955400c15446520014040c2001182e903400d4000001d00b05044200d46c04a66102d00c1800c03200890b0000d804100d1940140c2c8040c1e02100b01c40040c0d43c0c01d4032030881c4039041140d1b11400040036105192003c0c8190503a803210b0b04400c0f02041d01c0c1d0600f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 899771537 1250 899770287 899770343
    0x306150405041409010b040207050d0318020d030e01110f0d08040f080309030310090603080301061b0203071206050912191e030b011206290d0507030c080c16 69
    0x90040c8144400540110710449044e030303561040303500e000c11a20349407405200302c41d002c951047c0a0092040100b00903001800d88020303840060b08005015401a500c10b40440010783c840e4484800340c4d40a9800100380092210100c14542e010b003c032036501800c0016030101410702c0d454584010795891a0107140310700c0500d0010a680c0b0301009103c18044040b002c0e501c00c00e00005183e1f074055480d40803034140c810070711024060480c00c1006201f4580306510752032803951983c103210514007183e80407a140c250300f03600000d48052484038480401500b4041c183d04101c1c42030040c1603c8074a582c2c14142c1c0d110350f010b81c480b1101101c0b03800d0300d05d9008011080c0e00715001c1d00001143d00324200d0180c06410800b6000380041d1094030741d172507000722900c1804243c070175038841455080300103100030314a40980f141c1400400000e01400704501e03e07074018540b0540ea5a5008912086074131405410384101425486102409208010401046050008109401604d03180103603038100021440b00c440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 899772787 1250 899771537 899771539
    0x3120c030f181a12011418010f0b09041d0c010e040b130e070f120b070219020609010201020d020f0c0c010f2106080607030c1103090102072d031b0909020102030306150405 75
    0x10f904d0000440507403a000c080b11021040c0c650350341400c48859540f01c162000d004031814070b18042d800f400410000030246c041c00001a00c00612403c00030030700310060042c18101c26265000750240911542c0c01140c144200800380c506201d0501c5010004120b03100b00480301b80016900c2024080c820400c004820007005ca517903134443c400b6103411000d010030300403020940d008034104001c02c52461000800340e1060a080011038004c0c074071942005030b40d5019640a03411590284104c10b180c0f2054401407031002c00c0e074101c05641d540074a2940d41004103418000781030091081c0c0c04540990480da03451041d00008002d00c001895441845008100a800c100346031300c0b501c81007010300d9406601c0b1294089203a20344d9009103040d980c04541d02e00c032700442c042c0180c00c2040c04004240308524a0301d00240f2885154855180d92101c04080301440d80c816a41801880310010f509000340e01c00c4030241007840703002c2c1700040aa800103580d910024040901420054401521010044043d1009020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 899774037 1250 899772787 899772817
    0x10020a03021209030d0c05091c030201060f080601151e0804020d08030f040b010e0c0f030903040b07030c060b09011410021005090a031e080103080c030403120c030f181a 74
    0x90240d010703981c0c0c1e080b241400b84030a18060406c00d019000d0f500307135100d00070020000800380c44010400300003c0144802141550b407240c0300800c5c0d115020754444003819040740104160340c074105601100509115846c020b01903001000c664401c20401010211031281c1081c1006071100e101060b80c581c2d5452020b4180c200103c10312115080e60304120340101d000300708020341030f41c0300d5121000c03041e001c0d60f8600e8408410405200c0c0c0e18100c0000d903601500354001d0340e040c03564840540340d1986c04920203c000400c1e803082d041c1000703600c0c4a60807075504207560882c86581060120706801461502c0385210b20f40035440664400d2003005100100510418140409d082c5403d90300d546404204045000c10343c001001c0203801c4415501c4010004581d031307503400991039030b180c882c01c95110380001131f401d010030400440450001c80c1900d1840c8207aa50319071102c140303410001e0003641c0131400c0e0010003034520700709201d00d4160240344069130588540b018140400c1d0220410342e12038644c003c05014 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 899775287 1250 899774037 899774041
    0x3161b0f0602070204050f0127090501060b0a0f091a1804060303050d0b030309060901050a17010806040b06030a0f02011407140f1e0303040f17070b060f040204050310020a030212 78
    0x128064001d001424805d950034009500da0305001c0120034824081c03040c164403a0382c0300903440c5100345500340d50000c4025001441c8195502c0e1282542c103180c1200c91201c800069000301e266101c0d00b500036120952610f480d9146c1440d103c82092002401d88070001e081c0841c40c100032031201031000b065040010000c21843d5560314000c0c00c1500300f075842c1c6192524162040d42c50307003408011101242d100604845c6070440800043d19160002c0e02c0c0d020400c00300a154030000c00300801e07041d018181c51402040f844c609484c00640b040c0004110f54000c1c3c01034100b42001640c020140e81003603034242001b0000440054541c40c1e640951000a4001581d940d42500d000401203690b400301c00108080d070f0074a291009118141c1000c0e100c110b2503541c420400180413560070352012002078031405810051440c10010844203802000c803d4907000035190502030f2134a042c14088134020000d0714194203103460b050000e6202e038007150b600a13201d81c0004604c00384074030036411a8a11600030142107558 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 899776537 1250 899775287 899775293
    0x2b0c240f0b01050c0606090c0c07170d0c1509320105010803070b0c2d0928230a0f031a0402060301090e120a030b09010b03161b0f 57
    0x2030240d1000c11821145040040340407544103504466501c04004010300030b0303480d20300c14072012210040c1b900904090078480c0000510703061117400024480c1010070440c031140c00c51402d00b03200c5905080f00512041d0704210000554091400d004880541e00000e11100c2500302003960300141c01400254015400c03500d016019a11070110b8000070300c00c020007030741c1c2e00d5140c20b0740c0d60f110784040640b10500403000035880c0c4242500608411001400c03058140e000301c1c2e80c0500e50089603120800100c07002c9404486801c203c040f418100900c40d103035403041c0082210b41d4400440501800c00685840311740c0064804100310511200440603140442940e943c0b00408a05003442c00115101c2d03910b4460070000425100441c1e000d02d40040a40d40f840e4600706002c1c4c010504215036152a000310080e080c0700104101c094a2400c00320340f004600748101c8010800680d0050300f00a19000e01030090005401c5c441187d5842c0381c80300d04004400c0114055071000d0322002d8100107040182d050603403c10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 899777787 1250 899776537 899776541
    0x70c090f06031e060f0e031e0d060b1206150a051303020a030c031202010c0e0405060d0b15011719150801050703020a030c11061504140114032b0c24 65
    0x1440d40134440c100100d00b2100568000d90b000410503400c0c0d58800e1042e0001d4040740204e0415254254005500d4285124441b41c1510300a501044205c840401e500b59421510307072200b40e00103030440c0d029181059410b0b4126407409001346000401001113040341c05114005520300142d50020310001d4030702d0307036485d01959400313090100b15810380361081c80513101401401201601c51264454141c0030454105020090900a0916601220030451040410716150041d13010b2125a104240045101000546240c500c0d041c801191011f8404010405403601195008085027401c04565200028031110710741a05820407c00c0303510f000c042c425090380640c002c03d44000380c4d842c20700c240d0107080e100380d03500d0407403201c49007807a0403880000f6451000030400d01c090346002000052000e0622201c00c0056500340c11921a55041a0710035071140b804021003004403100c056200c9000006400380c07040b05002d0b00020040c00720840b0480200583c0c0304c000700b404400c2907003500d040c101213004000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 899779037 1250 899777787 899777843
    0x1020a1e061b02012301151b11040606050901090b070f050d020a11010807170a1104120614042004020909090105100603050106140f04080f150903070c090f0603 70
    0x1015619242c0b902ea52914061960b41700f644070250a429103a20300904030354001c840c401c030340d010040307400e4081c2554103140368900c1c4c4480c0203100b0070541e1170f00c2c641404101d032520340040c81030007400e03c0001ca06a9000e00d45030203440c2d01400c0140c0300c0007985000b96000071840070041031800703442c0380400420307400a03e20010710301599401c03080d1600300c0015110b01009131256070001d218020190110401b02030140e07080a18031900003281203510103ca00c0ea50442d030485070044141c113817110107000290044130150108109150494240359850f03074400940c07015400303040d420300c1d078900c0c11030342e01d55054400e07004019001c01c1c071510f050310b030300340c000c07e8102d48034001e515001030301040b210b00c01d10940f416140c8540300d4070494076848a008070f07103800420740c0c0200070790704020103e18214144500303014180448003c004030541c0680320032880340d0080285001c4d80c4103101e103102040d030061048048440840c80040c0040c0c8485802024041c903400185c2903c5400d40096102c9900300e0482c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 899780287 1250 899779037 899779091
    0x5130b060d061e23040b311b0e011103090910050103050a05090d0e1306090b01080c070506040303020d1401030311150915100906060201050a0f090201020a1e06 70
    0x9840781d4507105070041c1481807011005200c54010400b10b0b807420a40d021002c886d000a10680c1c0003200e2003088150103000304600718038500c0d031b003000d201c03c00154040c6007010700c00300e4240400100c0540300208600d01c200e4400b03040100c000d49040d011380d024011552580c8014100b80361602c1c084190054512041c40b0710382c0040d14100000c0c2d40320005d032081602500004029040e40c42c048602111200701c0c23040040c0d8050180345403000300341c030700c2d200d9000105500080810b0350f400c1071002600703081c1c005100c480144000c000940004a010500307990259050078010f8a41e500214010014010300e0b002c0b204005001f0004024160000584003050005c1000c03561040294402c02c1c8180300c054a5400381a80092610b81b10340401200041e840400c0d84165240299900305c5a0f00350f0b04283d01c5a0050b035510014800080d41034001d0507800200b81c0c0b0213211001d840d0740004c1d90740026000c090321296402211a481030444c40701c499006802c00824440c80c62001e60890301000506420 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 899781537 1250 899780287 899780339
    0xe0a02072a0609150c02090604060b0714010c050f070b100503010e011a060c10020c1609090c0b27221e060807120204141302091005130b060d06 63
    0x1345150080080310000c0ca61644c40400c5c001250307080c08401031000d09915442502d420000c282c20504002408401d401203407503420000317242d80740b01d0843e2000c290341c2c8108581040b2490082049000700c0c0e03580f81d4480840502d699900b0284150700380c440c0c1001f1f500d5420043c0a01e02100150000400200d43c4408000740008500400c512849040300c0d14015030052000d5007030681c40d0794064070f03511184000792080ca1341040f000218503000e40e00b00c3c1d000d890b520340c2810180302030420b210018282450407545070201680e030200040c81d065145401858170101260960b440d02e41228000124400b4160380508124034944003402d030140d581e400c04800520760090f00f81c02e90140d141120401c50241424a08100341c050480e16803540507600325495403210320449000013441d078130030b1501100c4803000c00c005104106180401900c1c0c1271420144034401c0c40b5540e902c0d02c0c40d015044480380f00040c046c540034007159446c010080c0326880f107440c01c8000124860384401075a2101180500 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 899782787 1250 899781537 899781539
    0x130f0312110306130209040b0a08070609090504020109050d020a08030c0c09160503012c100302100e03120c25030212120f030c2701030c0201060e0a02072a0609 70
    0x244840c580000c58941d03030b11131404030358002c6455039030703009011001c005480440d0f50400d031000b10f0595551540540083e0b070084c0020003000e0350041c0c4850151503241002c0c045800c00e5000246580b0140c0030b0940300302a802d40c03400455640301c3c040c1d0001c04890042e680c0701c032100c03940344e92100050b40c00740b4000d4504100050b42d41420902c1150400c0351501c8c0c850942c2d0802c0b01100210006280c01c0c014550002040312484100c03022037840f80061000c00e102560440c4103000800c1e0350030903110140036400d1804c0c015980c0c0818000f1402c00307031040d1140c0700c0301c0003a80e841c0340c011019221150400d02c43c918240105480c030040303050783d009840030b4a240907208542940c510342002402000e8005004911055842c2e030011908036940d4110b131400c00d500c040340d84003044040d4040c4000c06034182580304980d6090b00440800d5481ca00080000c03514108140c90a0400181180030965000410108101c03000b225407006548a03041240101090088541d074100b850007500d011072035900d8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 899784037 1250 899782787 899782811
    0x9030c150406090f26100911041815020a02160e06030c030a050d0e0f19090e0102160209040807140601032f1003020d360506070503130f0312 62
    0x388039007150010005c4041e50000c456403140012600c00440300d40380100301c0707000713840c614500408401034062010315000c10644420401222480fa138020500b007000044200421060783c02c0c02d9090982038070142c1e441c500310300300724240301050355400d009000441c00400c204001a03980c0344140c40650480350002c21600c20140c0d40c0b0100030005200368041c54000c40c0712445005600312900b006080e2121081c14040014540e140c1c40c460030303085000a000c1002a000c15004013051041004000c501d0406240e18500c0c001250000180c000c50701d501c08102006013820842e2906500704a00080c404440c403a005d40750344c028401980d010694090382c0440101c03022000c005014485d030b15901c100444810b02101c0c544035a03002060541c00d0142c1003000e1000d0003002888020500c00e0a0b075900407503960010400b9076403804800501e800382c9500010b00c0011941d410003039030f00300380d600d07560f030b00c1c03082440502624801040785100039001070400d500b00c40343c8544801703414424480d00070821 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 899785287 1250 899784037 899784059
    0x61713030f051e3a0b010c060c1101050a022d07020415030512090a1205120a02101103060607030c0c03020315090c010806010e010f030609090809030d02070b0d0209030c15040609 78
    0x324071500010500c01c0000340001644426800d28047c108283c0c1c0322016180d85080741c0c40118400007141810804920714903085c80b8050b446800b00004504000109506084141262011003103041c0942000c001420b0700c1d400707030b560b0148c0c010401d00c10064028404680e84801d44821110f0b8440c00700911094042d400c240c4040d42d10150011940900e42101c0c0001c100510700c0541e024081c041c107418080d1504030041880c0c1e080e6400602c0d0f102d0031910f9a000316030f001008908401001d00c14401e00d030b50341c4130482c0c0d0400e405241c002c85040d09414a031086408590000754144244000012030107181722255214000e0141650f41949003000192100c0c5002c4035401d000808540f1000301c19030049031611003043d00b42ca00003800680312004a0202c890500f015520900d020032420800c2c6030410081d1000e4080c1d02c040c0070b00301e1400311009014006c0785045410340f42c0204881c141a1001c01c8801c0360f0300b0000f0480100b000c071600c2854510341c082d000e0200004c050a00200b802c007144 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 899786537 1250 899785287 899785357
    0xd021009080a05180409200105040810110d09050d1715061602031905010507050427021908100f03081204030c02150301061713030f051e 60
    0x7240c0414076000c0081da04036080d41c08680c6141d1105014201c0d1486030b191032240a4031540f0030000b0b0038444002c3c105905a0302c040c01c2c0d505041160070003050014410101d190b0300e00e6a0085004070f400c030311440f81341c2c202e400f44a06500d0781900d407200840031b1220020f1401c1d12211070361140c001c0b00b075606103002c1d107080342100c443c04100581e1092a03100c1c1804030060110502e0203009001c01c03001c0d0350009041510031a40c10482841d031841000500800307100702074106003142091032500740f030710010b00358018510820b0140b006007c990b500c092402601103480314641d9070121049070030100009840d5100c02e0b00d4007408051400d10200b00d034071a40c0c0a02c0300342c03900f05041170b0404000b4800258034400051040342000300d0400c14600503154804000c0603038440b5000035480350b040c5000142141503085007900441da54406001c1421480c0484808a94240c035103441c42840d05c082c191854840d0359000c200e00451805034900100c094070180c0310f8583ca0070032101d081085500505046140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 899787787 1250 899786537 899786543
    0x11040b01090302030d05040e15300d030504020f030d0903030c0203010f0c050c0f06220f1e120201060605032403061e1003170d0b090c0306041b0504060e04020712020d021009 76
    0xf881d030111030f24a8140c0e4ac054030a025000c400200341d1303011340c0b40381070205503911007020076192020301c030441ca001c00c0c20a200f0070042d4010018602094001410503000707120140034000c0050b4882e00b9518203400c03903d40314140b40c0e03041c800c11150300d10040003030f071182e20105d407580540c041e103000e03950011800301e0190b15140e1091100030510104000c0840e00843c0460b58050010180000540001004440d0380b540810610307090301d15081158003258645264070031a40351000034030515402100785c1c1d410110303241c106010518045044403040d8100ea454950511811041241d00c013944101d124007078902040360702c0c680d1038076100181069814000101400724400c0b4903001d0508400190070130106100c0003040180012000c15040207041c1d8050b00035803000400c0041c1d80c10103000d40c04281208044088080c1c04041000b80b442c041c9019903401c100c01000c8401003995141c0550701d9003500041410000c03586440080c0d6140c5e0507405035009401003841c001d1244019216000c4030b150 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 899789037 1250 899787787 899787799
    0x501060206070f030b090108010203041b0506030a09050c03060f090f011509180602030a02040f0b1c051e0c21011a0306011b0c090e010911040b01090302030d05040e15 73
    0x444600c10342d0700450f0120b40008055840e9211000c595907007640500801d040400180e49060606102d0250040000043e19803070b0054410030403900d881049035031040b6214030010f0084110300e440c5017440c2d503031460958540708510900a04a03201282d4a01a0984800700c48501c0200250381d42038500241130502c40203080a01013041d411139400644011038035501d045c4584100b951910704a0f04103461811407158081010700114511040d0f00d4090403c041e030890610990304102d10702d4101c4071400d100640d03110400b20b054080280710b01e103d0100104001d1042c0d107020001e40d441070f0014240c0e400103440080211a00c4c103406100035060b111501d546d013440100018080103145d1001c1d00d1241006000280102d2450108090303802040c862103a140d10b0921305850142a2100e041211020343d24203240800000c68103121004400c80940d40030500c510140010f80301c49030507920180d0136001d01e03070840ca5485d910400401c281c43c84103240b18481d03283c5200c203507041e110011a01350404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 899790287 1250 899789037 899789041
    0x1005090a091a0603010908220e01050d0f08091002061609050a061409130e01060e06011b0203010f0519150320040603020319022e05030a0b04060e090f010501060206 72
    0x907600d10405640b03d6800780020a02034040c4d99400d4145c1d0004010301a102d90510f00e005140c11040709070401024001d440381a507505100024688406110001f080e802080752800c040207620700603150030800c024404001c1038816034019454000072602078102c0c06100c1440c45006000c2c861280549802420600b40d041c10b003901505e070300070015122409140240203a102c1903541e01c2c01064003480d0000003182c07414601058601351201350300482100f4146404101c420b0b40e202050202c040044082c0381070300c405a0010a0040c40582c489411180c2403104020064440a01000340345100820030041d000080340007c911100c540001050900041c11011010a54035000b216403140208005052952503002900d40089120b4246505112109100a525208803c80014a0444142c2ca00c08242c01410200001c4040d1444144040800410450040c0e5030107a03420700c20240003000111f4644402c51004e49080350616014444c582c00f030140c10f030741805294121075103600100020303 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 899791537 1250 899790287 899790323
    0x115030e01021e130e13060f1a0402070614040308061c02030c010806010e19061d060f0c101e0c0528020a02040515030d0915120f051005090a09 63
    0x75031240400400d010440000480d007004108002406017a00080442c0880c01b1403400300700f0740d1894a91481418074103900f1291000f21401514102c40c030486006036104103900e030000c020310014a01d0540c2c60048402c00c400c16821400c101e01841c1c044400b004144001c4150510307950000100035090382003401d0468055001e01c0006400c035030141800900e0040722004034040ca2951218101c15a0000310204605900005085808003240f69080300c07001c0c203400030400c54458880110707098400003504500b1240f0510141c811580e03510f00c00e10620308400760340aa40303000002c0384038130a4039201c44031000301d001d90103c91040260070030803005520040400060480c0c00300714070303080d0300440511200503039407071160074490400b081702846e01c0c10203001072614101018003544203201c02c034102440707110200c040903caa400c43d0b1070140b00b070f07905400b01d08000d0400d520001c035501c2d0520007480380100303406c000a002d85030182e070708040d40c1d034640c0851400d8860142018012645802c0c0f45062 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 899792787 1250 899791537 899791597
    0x106090501091401060e150705031603122a03110315010318110d080c01020a050c01110304080d05070c0f11090a1503020d0219060c17040f0605160b0115030e0102 71
    0x5000c07e0b00c407040d0706046503601c0341030441c2d0203440740022400da4a0811410503421841441c214240140d041040702c4510313040e42da00000041e0303c0840d040c00d030304c92581414401e4006001c082102152181c40c3d00f008400850501403408103203010904000c1510300120807004089625034101a5480c1c111142c18184413810208180c2500c00807001c010444000c1c2e000d000810000d00555a0b483d520a00c0b10310a608480c0000001c8044d002c0400511000c10040d00584645032401c0c44000b5260f1201001619040080306004108840d0050080c052181000ca0585100310a555150895940e0800201121040e9080a0700d8a8030303814140007604103014081e41040c405010410750f4403280300c4203000e690131035104500182940d1394842c204418021101c1c07030300105a081508060500010b07215104150040c1c3e0204500801c02e00983c0900c0070394206c0d42c540200a03000196110084158120b40010700d46010a050110010b07081c14140b00310b401c2c2001004402c0d0881d03a1403c103c8007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 899794037 1250 899792787 899792809
    0xa0504090501090c0b120a02120f100807060c050f0c0102100905010b0607050606150304030504030f02061c020c01061211060306150301090c0807030e070e07050c0106090501091401060e 81
    0x180c0303650f070312400ca0009100041c0e0b10080d0800e00300742602c91000c00c81c80c20f03444c40000c144500c858011b00102109419141d200c0b504500914040719140d520030401c44000038496200940b01d120307149002543d82d410011001515004070280c840700d4803900341056903080340c5c0071010300680c0b0528010031043c8003640305814180c840c60001c40c4146d104000a1040c0d00b0085040d50380f03070802c100380026840d01400e60304008141d0010f4504600d081c0c0c602804d2030180e13102c007070319218104464500315503481c0201c0310000d4814043c80e94400301d981280b8002c0d08145010b0403607621300070303000c161000240c4113610f60b02d07800808000d8510948003801402d030030251249030425031840702041c25a6580b0301540c081c105000c40016400403061000b04809400f4000300185171030848070161040b00411301000ba03c42d0311002060316103450f44115014070072090401c1d1135518020000c108011290081d904072200c1c010144001c030080c40034100614420300c00c41011405901010110703060010002c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 899795287 1250 899794037 899794043
    0x210050a020903071d0108060c0403170706050f010306050601140d1104150203030403081e06041a120a11180f0408090d06021b060c0706051f0303170903090a050409 72
    0x241c1880702040203e8600a955006411801c0d0a0b10551000c121520074143c01801554018000d60914103000c0000d4491804094940e4110082c00105080c2d05001c49200c940e00040802c01440d00448a200da004280402ca90350b03803c2c040031540035845001d000c00c0d17106490b4962072803c40c428804e00005c06502151042410782480000340d071906a000107850400140c0242d03030350789020b1900505901d80100984074151078013801503132110010100e0b55000f075059800140308030362040d0704821b0002e4a07011540c001010b02c1002c0c0e241e507002c100a61581e20581c900c3c6045c8084008104202492004000c209030000d0001888001610416a0804e008188003807410a9100100e4803100c41d4000581d407107030300011408480706440c4034806203103403540041d005500340304040302c00070f10403400d01504c40e40d21600032031034130032807001903001007da005003c10040c0d90302c2c81d0140200d000584005620a600b000040f24803402204540d40e8440041210015608201c1040000c20001c2810f03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 899796537 1250 899795287 899795291
    0x3070e091b03040b04060b24130314070603050a020705030921071d061f0f030b04020a20150103030c050a1731090b03120403110a14010210050a 63
    0xa035400c1c988800086000b070b402002110407a1a05040c28000d03105400c0103c1c2c0184e01e0300c0e04080c2801089864000c41541c0744107995030b5805403400c404015100d80d0005040e10100000070311540d23000040a004641003900c042c411aa60090503000324005c01c3c4c0084c1c41038004110451180c40d140710074000c248800942d13141c94548440c00b80749040241d80200ca540108202d24081c0810462103050b8006021a050304e491101171010700e4542e40f1030200901802118100502c0c503e02980059038154800381045403600030340b40000b0709001007601d000440b10040024108000d00129032001c9010780d0300c06a15259185540c220384000c080402610b16010b1010b00100141c04400d803a982041203095042d01c4200016900502e82c40003011102c8600c049507141540c604008005c13000c464541000050900115011a04000e2071005515031450700040c00f20400103032100ca800c06003000d9800c00ca10075150aa034140055551540d240564000080441241c055401150780403c3d14000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 899797787 1250 899796537 899796571
    0x1401030b090703120e01080609060312091c0506040b011a2b0f0504120c1124040609090510050303070b040309080f07081b010c1e080301030b061503070e09 68
    0x3580b00600c9200034007000200c4990400c0c06947c0d11000603a0003180440f284a85414010002660740e4240d00351103c40c083d0108641038240c3d43d04034503d40340610f080580702000018a031540d05c51008507030848609a116002142900c0c0749040c000b00c96031076407089071900f00406032002c5011100420b0760b4004803200043c403095841801403200c0d05020040218031030501d880e2042c520300442c0941410040b00048000105224402c03040070614180e6024030300d0f8000c80120007400000d500343c5907442e42d0010700041e16030341c422543e0701198884941000962900c0340c01102c0d4005a218a6074154020b2056502042d00c071107115411510074204080a29695540241041112828080c1c96004044100103801d418040642c803c0144a913030416003044800182075070303101c1c40e000f8207041c0443c1400e25222061401041d1116000350080d41c40790f80d0381c5845d083d80d2104480e0f80340a0842c0105250310405500d0550b4000d03003541d1200e040b1010201e040c402c0b401c0006004e42003051405030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 899799037 1250 899797787 899797793
    0x30c0409020d0b1c03080105030c0a06180e190f02070c1e0504150602160302180910050a090302011401080d03230114181303050a020309130204080f011401030b090703 73
    0x140580290001030f01c84c060b0308540d00380a82034541c140c0c0000d01a400042039000c490b550803030f50300251007450503d00407100b03680c1080803013840280c106038680d42404d014080b43d0310503401d4001441c1e481050500c003040c90709440d1000e900807500c00810700034840380c1c280043c10b00340361441200d8501020042045d907a42d40000c2c181c40c1001459a00e04401090074015030764184410355143c0282d0901440032817840d0b020800417034811010f94800f09a1901042105406005205820342081d90611090403e4440d82c4000c1680300b10803800740d0320b009400017002640a203401d0480d05604060715400350020f03015006071080c1011000c03400c000001d42c071450544056810702800c1000000008510031a05101510a0402c0c4c402c5022400030100300302044200440b0a02c0c2e40d240c580107407621803040060380303103008030031240d580008810341c0c0c0c6040c8210b0f9030140040764011402c480202100d440d80d103007200c9641840c404044030803c01440070840150149400005100890b000299252 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 899800287 1250 899799037 899799049
    0x12210702010e0d0e19380a09180507080601030f201806041802070f1410050a020a0801052427060c06060405180307060e060903030c0409020d0b 63
    0x7142c1c1c03000c43c1002c0a144414200b196a14003400140340e1174425807828248a1400e4040d82014021084107000d600340700b20500768204040075180600542d01c4840c8104007400c03180c40d50203866015144450181c2c5074007000d000da14017941a940380c0341e0031030311424011009000018000d00b40c180d2943d8a401408441d60030380e81004480060341c0342c5850390280042c40a580041c0000d204034002d010500151a40200c407000032003030b40800694940ca18588a1041c0d00c807428090b080f8007000c01e860100e82400300c0c1b81030801a8200c01000305035a0792440c00704a003c0d21000c40b0025030101e006002c1400c01031070180d5880e200c14101072040014498200c42c0d907200d50290100060051001c950b20300b1801d4440c848410110f6500c3d080071070b40c414580d62404000c125610442e100c03000301d1054201c0218028403c1c24640c140c07030b954661070610201610511160503114454503001483e0700d500401580c0c0201c4c80280041d2810380340103450806034101a502c4541c040da00c400108190385c3d21 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 899801537 1250 899800287 899800303
    0x3020c150301090f11040b07030c0c06080f06030f072c18010e011a04180602030702010e162d090513110405060105091201090b09070812210702010e 65
    0x25452a41d01d605106680c000d0f0b8a080d00300c2c1c585103003058100c2150701d10f01e4043e02d054801d0920941c0d1102458103080359070810404025011644207000441c6c0c0a900c0001c15100d07a542c010040890780b9510145075441c070102540b0794594204041c01d01c40103403113400c0d941d10282c4642d0468242d0245024012070b107941500e8a0f00201c800101d05100081c003030140901202c5c640c002001000a40080c1d005d001c26403c0c0d0301032089a03030b982d04034003088035a80300d03020b4a504090115280e1400c603001a0080010b0100d02e010f511641e55250b1302c81240c540208203640801c5406103240513203014800107036520035810000300131035000100352107083c2c3c8215441602c1500c40045075207904d08118000e01c1c10751802c14000c6081c04200700244cad0300300045507038012054460901107030145030010b0040003800c80050551880ca0240310408034006002002d83d07207550207030b952181480b84109010f02c60300103020200c103810707440803074402e07100340d000340d80b007501400003103002842a81d44504002071 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 899802787 1250 899801537 899801569
    0xf0f0109050d08191d1c0e0a050604030807053a020d0206060f040f090b060f030a110d0c0509090604110d0c0504090302120f041410170403020c 63
    0x5151010014480208616484610360307080034603003420300300c08641c544642a2041c0c80b4290b10340d140500d403190480d4410500020302c0e41507950100e0036421b04024002440c40990000d511218620000d103001c40c1890100c41005064a20313142c503564604c0e11580041c002075416001d10f08070a40c0d1001c42000300141e1030503270a40c060211191442141040004000307403000c540c061080c081905400041c40e43d0010b8048580d0107026180790f0000c0c02516225000050040c2054007039020400e10102080c042e042c1100c4003c00d2403640700c20f0503a985161000542051446e0fa4898458100000182c5080340a01c0d5160308482d01c0d0000304880400a49680071a0340c0100c0400060140075a0500c41c0117404482010903100c3c1900d4005c0d40d0003d0340250391146035200d4550041500802c090100206a02c0c2895100e8150100003581c1d9003052040720000402e0400081481c030304411201e908044503143d5104802044c5003072854104010411002e41c4150450301c0b1244c4d0b6110024070440307107 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 899804037 1250 899802787 899802791
    0x11040f0c0e2b030923030607080a06090f020306040c02013e0301060e031c050d1109040908040609050303030c030a510302210703081605010518060a0b030f0f01 70
    0x11926002c000c0c0f0890340c0301e40c0903060b095a02c0d07446084d1b42c0415403942000c1d040c580700440752509187c2c88020b080692110200758580f40301a115095070790065031041100f00c80c1040190308000b4140e0a0705c030a06001c032900320b00700c40c0201100d10b82c03003d912841406000c1c4141721003003094944a8503842a0040f40200780c18000212075840d040002407840145202806000c110880014007e40a0366105210564a451400f03440203000300036588400ca004105008a2100d410800440d6210b80507000c00141c040c84049100c1c10004201d0b4001e1740502c000514558a1a81d0603001b442c03d01c0180e03524041c620401070800b240c004103010040126500c00303820100d01c0410440c21480c0745040d901c160011b40007040942e0721180e610250720325011307000c10200e503203401340340c00d0041d1600300605800e030200e140300c1c0f904004179903011030502c900c1c001c214035110500d8000e40502c038200868910352040000070400010343d0060001800d000e022a0b0b40c0492001c1524109014007080619981d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 899805287 1250 899804037 899804039
    0xc01020403080711031b01030b01271706010e07030c050d050f1e091207020d0c06020102031b19050a121103070f0c03270b0711040f0c0e2b0309 63
    0x200c61102c4d90068070480041810103403c00b9400c0440b1040c001c080d041c9903840b04004100d034000c50160700215030024519000c1d2201000e03a190100c680c0c011048000e05001207020821000980076041c1d40103070000020a94071100114046d203403038418501044014032282039405854096a4095203040c90600f03083d142c09844000390b0000341480c1213308001d002071004600000c684a50442107078903555503100d0081c000304821034419070b0020190040700d031001428a0703040d400f950041c400c42c4548001d0038a95132a003141750183c143c003846508507190b01d02241c81d0082009048180c0c2c24117000305607078460452103045031541d5407002c00751703100041000041c82d4008141e552603a0641001e9805500688006050704201030b154411627a04034a00c0c1004c880300f8215030000c04804030542d40c3c44c4254548410382d514010755a9008604042e1543c2e2406054080c04080f0202035940d1140310340b80c003040003035044081c204403590318110701c030240703202c00e400102d03240841c0662106040c907 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 899806537 1250 899805287 899805293
    0x11060f03091f0c09090b03010204080a080706050601080c27130912091d07030605090405100605060913020906070804060c110d0f06020304020102010b040f0b030f1b0904080c010204030807 82
    0x100c15802c0000070311920702582e00300201e80298904d030940f49120000203010b00c00a010078020320560f00021107600c00c445041c010040b15800505003184114001e00148e100c0e540196204501034a008005040c1880b940c8422004c0814040b41000f000701c01204c1c000c00c450100c1c6d000c1041c4260803070900d461b00005d1061100c00c0c002840359406c5803802c4144c1502c1c00c204034481d00001020298644401030115121501c82c2d004040078243c014640d0076a070401c0c1c0b4107650354000d840c064915840c141000090700c1d207030007000e50300524002303002d4142c4080b200b0301d50402580007581c01984048148410800300b07030b0340c0d03015101600d6680c0f10344a241041c1c0c2030101080d40000c4050b84101c46c041d040b40300113010348001380381d090b0340003c01680b02e48039440140d0242500442c400e8100b843c0803d0216054525040b0403a5140241c080c3c915a4050b03044490f101c0020f0209196611050284110b590403d19445a40140501700d40c0c1d00b02480c0440341826603100d0f500648118070042900c1b014 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 899807787 1250 899806537 899806573
    0x270106090905150a170322091505100e03011d010e060a020c070b09010309060906150902070506070c1509120f030c02060708060109080601082401060c11060f0309 71
    0x2c032000f0308440c400685028006803424805004d406040aa00e00d203240c144101001502e614048040411030344003c1001c07440c0c1122040c0c07040d001440c0c11b1258080e00307001e00319020429207030b0140a12400a801e6602a500d040b008080150191350f01c140e085200c64000560f5021407078054000305065141c1c0850394079009000d05281042441000001e281c1c2800003610f008542c07082070142d48512602c00181c0050140d01d074080c007900c2c148000041001195400454500c9200d0b0b1207941103626208440100e001e9800d008003603a014002061440b030007411040e032101c0c4281500005110808a0030040d520031075004c4820414908840b80380c070390401c0b5002d02d07891051404001d03201c0340480082d92008041e00083c240107082000c40ea0a9108900c0c03d40541040011550256074512003a42d4440768031040b00e2140f800c4600303031810114501c0f4641d04a0304030b0794078141b07665140c0c4c5407010710022030211640d00103410426001c554003118040d46c031400e8010007070003491400c0c801f1060 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 899809037 1250 899807787 899807791
    0xc0809070e0106230a0306030302011a06090405090a02030d030204090b1804060507110f03030f0f040209151801060807090602030a02030d020d060f0b13150905270106090905 76
    0x44280c1180900380078a9054106803411200da62410705000030310080c1000180c0c19000e0103018404000485400d00303501500a40110381c1309034004c04c900d0b0042c0020f140000614000c3c42e41c400420040034512303250540203203030420341c088180c1e0a502500da00083c90445450340c01404203401007020440c02d03d042c464404c82c03030400d5030300c02260803a4030144855050020070061003c1e07031301c6000c1580ad520500e020580c0042d004211075980344c1c045c0715143e481d00b0440780d4001c05e009920005200242e0114000e0250343d000d848901f081e2203a244441600000c00c00c0d0a4100b480300800035003680c8811600350003484552607a8801d824044801814174860385c20203401e542c42002452880c0b640041141c0c082ca465800050b1245a000f82000c0030b80b1442c0d001006100c07090f007011076400d001e0750007071085410040c400d0042e15070f00c1841400403070300449044007262900d002005507042c4603003490110b011115505031315099980440d1514242a0803150025031406000d1200c201c09204035a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 899810287 1250 899809037 899809051
    0x102041e03150605330f130503070506070b071713060b0409050304050d02060f0a170108010e100f090f120f032702030a0512031009330909060c08 64
    0x1119960070800801c684502e1850017207260040703a42951414600018110721303200000c40002d40d59414080d542000307400544e0752401c0125020b0b40010f0728035002419a0459001030030640c14808070341c1325501022001810306050080901680348118420030140384203c81754888042c002c03181d0f0405504031401c2800250180345004100d0780481c10003c242c1703044503802c44021004580d40e00c08034140e0b010303c1d80882e01c01c00c004101c540e81c26410000e01018220360a5980006a90300d42842d8213840d41d030600b060803034000c038440010b0f4143e140c00c850245001100041825551075a442c142e500c000d1a054401020000d80e20113075540c40303610f100b0a030700185000d020201d020040c110030f041008100c68582004a10b0381070864406000040e160342c1c00c034090340c4030142012482600c55000720f41441d0090034113040442d103141240b00301401200403112040181c00f10010a503d541008883c5a030007400c190741c0000d41f81ca160003603012492103144042585204007401420b1500c1c060320700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 899811537 1250 899810287 899810291
    0x606050a08090a02090a0b060c0f0f06070f050d0209060903100506130204051e0103180b07021621061506020c0a140913080909070f020d02010b060702010c050102041e0315 75
    0x1001503131710541c8564201c096544006030800700100052000c1c45008801c1e81207005048129590500100700610310106035170544d00196990601203401d00da47c500c4000100d8004d00c6000b8028401e68050b00c810300c00600103d00d0b204d04003000a1414038601d918090303c1e921401000b12904110b072420345004690308041d820036051200054611280111482601a042032a101d0a81c482d0b004450f10081d40508800c041d441da003020364642e6002c641c9807004d4828100b0b81003c145100c0417810481d0310840c0c0c05454110030611000080e40303a02025143ca42e10b4800303540d041c1c4034030501c920003081d960700201004000344040c8000e4650541c003011146c4a0250544902c0d01c6032880f255100010405000d040c0c840c514096802d800381500098002c0240d000300702456400c030b2800d40c00300c400d9408480d103000040f40c0c00c07402c0e118050b0b0810f4011105010b81401035004042a0301011300ca0030000d410a626490394a80900007200c1c03100300d80b03a144008200340312007503000301143d502203482 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 899812787 1250 899811537 899811553
    0x131506020d050904050405070521120313030c0212030a050a0201360c080307031713050c0d02031e060711030301060c02060708070c0303200a0c0b0f0c010606050a0809 73
    0xd8414083c02c0c1456000d1a01d4200107420031600b80a00c2025240052140700001030b2030940c80400315031014181580d11034807081e81104c448071800e4070322038500b4072500250880b03d56000c444006001d80c01b20781241d04090002101c003418400f8005da12003680d6169140c490103500203013500c440b28058030f25000000c906011400f071042e18002e08503144400c8001c5c40c0000c1c5001e001880180d84080c01c5800042400020164014901d0030103480704d144043c40e9031281c100a4500c0460450000d120394071034400c100c02030070301046107075140780028183c41840842d40b50103085a0043c41094a80341c000c5010444084d8000001980c0c500100c1700841c10356042c59005000080300c0c40c006441034401040703d400304001a000c48070034590040005510300e0b907a10b03000d4482d040c1007401304000c0204120328260300a000608030300e603a400c02d401861007803030310800500a6000511484104008001114004009018400c010403465403980e581e2100440002d01d0038101a02480161f008119 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 899814037 1250 899812787 899812813
    0x11e1805060a02130b070804090f1e1a04023408090d060b04090f030809010e0a12020a0210090305150106050a1d0d0c080c04090209040605040c0513150602 68
    0x2400e10b030700004a04005903104030003020804040456808001031000002d4040e00f0468010080c2c0105c411041080c0a14829106003405803685c121112060341c0c200c801d5008501b080d03810002c0d080c0c03448518582612104400301e81070364010007500600302c446a50303a28601c0d50604c0d014009441c814107041009121f070f80c85058a1003081152445803422208950921035158402e14004200034000c000c1034026141081e481d08807040241c000c9850789001581c1444103025001480d007246c000381851400341c0e136818508841c09c407003110451160044900050b110002c501d035a000c265103a94040701d00e94640249403075042e01500d0401000340c001007118541041c2510b46d030340014285a100c010105030703a0380340c800c41030540c0f59002141c0c0c41c40005000c3c83c0140d160a0728000429035014082c00420301056a50200c80290060358410008011030500e51000d90410b100d500092486569540042d0510740c1400003e140c8541e210003d049113003240f0340311030085c00ea50000e0320303a1002000d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 899815287 1250 899814037 899814043
    0x3110a08030c0a1704090f0c0f020d0f2723040c140a032c07142101150603051603050c0306150c0f010902030706031119020f011e1805 59
    0x1000b1300045141c01d001d81c10010700c41c00e603005070032550300070020aa00044074801401507640b5400201d241c003000c48860510106081c0344800c0c45071034850740901d0001c02110b443c181c08180250895040507001e0380e03a0112a420707030003403900340b82100b0110860350100000441000c1458402c51400a04440c201e410081c0c480f21000380b0b05500780c075443c810400340c01030080302185500c40312010ba1081c00c00707640340c6641c4201000d0039080301d041c2510380c4030300415031000d03034840c82d8030407038241082c009955040c2d130520f14102150700200750321481841038541d41c445034000d8800b00383c5a07010041050840c8040015070400d0b85000c1c03140703040c2001c55002611000d00404e01a20401d03000b801002503220071120450321a508841c002c0fa0300f4013409000b0203003010200c0c4680038014001400c0e80c4640204e4012080d08400e60380307041100244050a600a04100e50560251408481c1c00700e030207104030200764100074000c0300c6080f00c54003210101c1c0d10010f400d40885034481007900c0800c0d800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 899816537 1250 899815287 899815303
    0x30a06290f010305070201090b0412020c15041e0f0b03040b090a0b04120e0a0e0603010516120c0905060703030b03060601020a080327060702030a021011180a0504020403110a08030c 79
    0x80c2000902c0b17881c4c11100301d002d49400e9401500c1078410b10140010030803069a04100d10600358207942040143d003041200c542e21280b44a0340f031113418882408082181403046c40e12004030055050707810354603c1800c803582050f6004c00c1c140c84020080105102785011031540c0024007401520250000f581d035447c01c282c014101520030072080b0f07003221600740030707003424240308400808088090b55101200c00700044200c42d5240294202004110443e0040320561040c01e00d0340c4034191403180d000801e20044c08904042d00421808180001e944d4860000401e81c6c54029900030421031480c8040c1441c0c0107015203d14110741c00205000e0200700350320144c0e42c204c400c4025441801030380c07801c1e80580d40381c0040541c03101d005071020b200c1403d400100800d60f40b040d0b5002d031000c24410f444c0d04400c0381c403030050b0f0440e06507003007013441603103078954407488100400100485641601c4001160490300690022201018204d40e50b09680c0340080e0074000420508005510340914030342c43c1d0340c9560711 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 899817787 1250 899816537 899816539
    0x30b0c04050307090921030b062b060e1b070b0c13080f07050d020307090507170106020d050712170702010606030b030a08040b070501091b14240f09030a06290f 70
    0x5a1204020300c07e1282d00044107195000705800d455104602a0100c504180852885454000103911017841030714000c000459410541d0311f0029607860f144401060864000039007600000c00224001818548210780104880240942c5820783d00e186c142e0040515007003019258000145a041c15070300085584c1624416911142080c006101083c40c202c41600308103440d608003000c110f40c00e903004001e010414a40842040c899030b844000b40d85807060b0064050025070104131180104181c00030042d14002c1a10b0300c4120040192070700c0c00d0407842991880c0050f51200740800151382d06002d0031468040c1107000c0d1169006982d070b440c1d0107206900c2404c00903140810042c00b885000c0d801075841039000200141004003a61464103018001d00030750394505250007135080d40317040896140710038070f070308100604a40b003110400910301c0e04215202105d030a010001c0e200542c40c14405e0b01c90552082070041442042c07503040b06100030032a0301c00240c4405404107841d0698440e6900800420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 899819037 1250 899817787 899817833
    0x1718030405122a09130809010503090f0615010215061f051207030209100e1018080f03190f17040f1406060103050105010e0d1704030b0c040503070909 66
    0x82160a0182021404841450f0414581e02c915000440403050021040b404a80191559441580f444d9030b002046201070003008052101d1202d1354080c100460300001107004450f6001410f8080320301c2c0640485c0c8a000c070b410740d803180c2805540c0401c051102c03002d01c01090a1140303008008100c4e1294a0040b5403241000076040001050061080b00c0302e2911521105595240401000c2c5c0a940840321103400707105000c0c88211001d2007410301c01c1c0651802001c11743c4540100100721034180a607441d2840c1070f490f21000003080c2c8410031450100000881c05161100f480e020307003030703001c0c5010700e607020a00a400003440d02c07146c0c2c005035507920075030280740422103034503079050850b41c08004403402458024207903180940e004000810600c40c00090340c0610650780c84000445100032842c044540141720400f40c43c0c0000c01015902450b0110b40c81c83d05e050990301e4540302d0022806441074440c0d03007800941403006050a1010401414082d1410310049010307644864074203000e452281d00c50700c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 899820143 1106 899819037 899819059
    0x90b01060e1509060702041109060d0515040b0d03030c022805010b2b08070506130309080d0801061808030a030204080613050327030d1718030405 64
    0xf07000682a82d00b0000c0aa080c00017424040d01291030003c020f2002d4502d0f620380c0d40c0030342524610b400d0045102d040245005141c400c0c2c4101442c000c0d814143c03204101c0c3c032107608140c2c51552514001074000010304040b42040c5c003442c030007080c40e04003100ea035541502241c40701c1c6d00c06014034000c0084807000c000f0070109080907504100b108900e04500c840d107102407050381403510300a0705140d00e044420764a40c1c4c00c10303408540c5040706914030314141d41416404500314000d000d101d0001e004071044510080c1c422a0144030b0402000b50092411130b039040c004130840c004107211821251150305982003d4040d4006026210040c816a00010341d9200c0c0c2003103410f00340d40c12902461070400086820095122000001c807420030094914507503645041005040a40450352154000b036000f10481e4603c8601826429806c481018181200c20b00801100c04480044074020300700 = true := by decide +kernel

theorem cover : BRFrame.Cov 899640287 899820143 := by
  have h0 := BRFrame.cov_init 899640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 899640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 899640287 ≤ n) (h2 : n < 899820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
