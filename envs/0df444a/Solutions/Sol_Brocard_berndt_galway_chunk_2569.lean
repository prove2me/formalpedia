-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2569
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:05:39.942418+00:00
-- url     : https://prove2.me/submissions/89d4832e-ac90-4b0b-82c6-045e1a2bd8d1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 461870503 ≤ n < 462050359 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 461871753 1250 461870503 461870509
    0x907030b060703080a1503021011070f0b0705070515070b061206010e0a0501122a090e07030b220312020f03071d01030e070614090904050f1b060d0218 66
    0x2e07020040c0240e03284103561074521824001c54401c01c1c089003801801d00e40420050303407169561505c41c86545003000c00903000c0050180f501005400810f0f040303101c0030300464a202840040d180c85409407084481280d41c6100348060301141265602c0440800c0102001291a441e0000d410501c060b00b40c02b184c5c00032200ca01e00b0113800382c0040c641c5042e1f02052040204980c003481d809401401245030341c03801a50f0b1403020b520000a40180210020040c0715140d1200b012441c0003484804400d000546980302c42948030242408200c0b80010a6070100d003070140c2e4900b500800c400c0103214481c1c1508103131420780e180c51118502842e242e808000b005104800c2e034014601964194640701d00c1c2c0d0f42100c075034040c0c04d01803207080782c1018a4100c010210003800607119007181d41d107007465607001c41ca1b40c0301c0c0403452060045503504002d0711030a10080010000d0100c03449500c9c0801c0d40c0702c074410750011400e03038088014010b03400541804083c400b0062a8001c103401c901d81180c2742142c05414002c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 461873003 1250 461871753 461871757
    0x1014060c011506081f060e040207060f060812120f060319050601030309081615110a050a0c051504050f04020d0e0706020d05040807031407050a0306091505150907030b06 74
    0x10400220000440800103550131011880c5c001000c0c1c1045079080380031000b104034000c802c3c8105000c10003924160280c0d03440c1c5034100d5200d2600101c1c00d1010501010240b00508464407620003a07100d0325412001c2c4860b5041920045064020b80020544420303019030000d29005c1e03c0d103641400b0b928804108510400c0c00440ca55204101400e00c03580f440c24003809503075903030744291911342002c1140656841716003043c01c182c03919198402c00310304a110045401002012414003244294074021042c010300040002c40c191041968006443d144c40500c1403a120000c1c40c0011060b040c0004d00541c40d200682a803800e001400c0107041410201d032080540c0c1e15444520360b242c026860038001d4580c180008041d103100c50a01320f00e8035240580321a941d182c2c5200280c40c1c13013085241d00300034200c2407103098002c3c03a0080101c88010380303d04180c0c006158505003110b00508ae13004952051f10180155481040c03403200360f05550303403580188900010700501800030147d41d41c514031030380c1e50b507040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 461874253 1250 461873003 461873021
    0x9050705011b110f0d0f030e010806060d090302070503030a02010506040c05160602070213050f15191202061b0d0f0903021008130602030c070309050301050115050a0905030d0e13051014060c01 84
    0x100c5907080c1c404c01c7c100a01400f080c0810795042055074420000c00d600c64904072105d114440d100000d4071b042500303080f4142440382d002281d040c000014415441581504401e002c4c0808407020003940c0c00c00001541d203881810541300140e0711400b110408582d4543c0a08030003800600141900e4800719075040894500300d6100004c84c00f40c0091140fa058440c45c86618000c0a42d44214180108141842d03075002c64800c0b04440741c4844004011034039041c0549600100c0b16003140341410091112581b150403d4030518000ba444183c003d404030b1088000c04100c80e00034010b4120000704440440d5400d000914001c144005005840e00281c1140b00440c804c10400030410b8540849140092908186600051180e03050a00501912215400d143e035604240e05156a03204506601a9a0400d0360b902040d4140500302c4640c0d4400c0e00f0042040d1003002c1102c0c2003508207030504006044420517205090005800c140c1404880c5180c030351030302c0107440100258248030380c07003000a00b55030402d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 461875503 1250 461874253 461874263
    0x3050709050403020d0e1e0d020405010807030201021c05120a0b1009060e04051611072c010602160302040e0304050316090e060906060925020109050705011b110f0d 72
    0x10030801070560501c00d106045c0380ca031402a40b40d8000e0030000380ca1000f0407031010302e00005185050599959000d0030364040e80e01500910866070340715105a00e41c8014802a030143c055103040030381e183c04001e0706060780000f0352079890520720382003446030360414001e10107540c843e921440c1102130341e1102e20b40c007000d6a465035844103081c00c0c03400c01032114807800b083c240280d04203018407a010324041e10140e941c46542c90404072190050034240d00d41135860f400294039028100c000905065042e07194281059180c0e850310450b40c0e01d8401300c1c0e07038604c0e45400c4054403092440c01d10040c0750603001940b5640d014001c0301e080c5034a40d40003a08000480c0d909900140c9000d00400c0303d0015802141011064003000e000c6030320b050205a611450014079981c0700d8200d4100040c012814a5801400718901004840b6000103411020f4000c100c0200b003910f42c0d22981200007813a6114501001c0f42924484031011280c55607a240d42c0c0800000303040c141c0c45849403030301ca051901c600700051034080c050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 461876753 1250 461875503 461875511
    0xa0c030303052206060519030302030301030b06190801050a0b0a030201171f08011b0207150302090a0b0d020702030615030a080d020d050903130f0302182707060306140907050a0903050709 82
    0x1401f003141d1aa90000d401885552100c01040840e0700402680e04503600007444a4041d0f88030380c0000e070008424a007104104040351800f04070719005602a910500f45d10008102c01360000d42088525402d030721009000a91107100c0e00d50300c220740d0002c1a04082d089983c0740141452035030002114455070030000c520381d51030400c040800500100c546c2a1b03e83c0f40003800d01c0310b0400c8607070340701001c4a0f41c100c4245900020103403050f407600f18242c002003001c0040c050301d9280707440c0203a029510036001a4400d11482c408540c047c1514041c4007914000200203141024013a921501c10790440301c01d4041455003403154144150700c5020703540c40f400c00302e400342d5603c0f1500d481800302140c0c070b034004c4120254146004e00042e1543c0c4180c02c1c00503c14104110155148003804048125850550700d60074582000d400072078400281502c00c0d921561010301c5000d4440305c000420000601050b580220000c001c601464012070040556400c01c1c5896050a0b40702c0d240c003882d005d01c69010744501561 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 461878003 1250 461876753 461876759
    0x6090b15130504170a0c0606120311010b010819021b07080601060305151e19050f01080910090309210303060806060d121206030b01090e0a0c03030305220606 69
    0x35020703441051290801c1008079040c603460310f0b14000760003071060f221060009a00c042c0a80512668400168001028020b03180c4407002c450009068800440c0072413a01c40480c0242c8006003e400041603060755009003642d13138012845071040e40541006803980d03080100d8860140407100b401507002501c0d0040c54000d02d00042d141c50204141c1c040340070149428240100318040301519002c0d6401150722004440c0d007411410f01081100c01c040f9403003500c00c0c4640140d41294070012301100c804954034412849000d00643c1c2c3c0002c01c41d00e8a041d41c10104441840801039803010f4401030082c6480e1200380d0310396265840ca448013414510401d00e00c0e9071f00310300f055490b01803500035110580c00707130000e4240b10700840c5103101d0700d4000916080340c00040c503c407648904800b55011041c0441800390301da4a0030030891080c401e00504031058284000305c035030040001074001816511603110341d941882d60301c0803001000064030741914410744560300c0d525006010441d40e80c1ea401480c000075890f203 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 461879253 1250 461878003 461878009
    0x50c041509030b060609130509060612030408030421080c011a2205090c210d02030406050f030c04030614100509010f060509030307021c05010f0204050604050d06090b15 74
    0x348400180100041030038280001280b1640300c68002c01c081c0c8100303440321034100000d48081c1d421400c54254600d40020006a0000041e402e40558410703036800c56180c1c84444507a4592103140140010703070303000304010490000c480605071142c50b802d41241a6600c1581c0e42c1e101c9661010028003003980d1242c45801041a60110a035071445049074580c800c280791210001d660520402e07020042941d030740014032140e00071f01000c55a107000804640340503410000d0400e2036400b40740e40e00424450341d1054001035000000702c605848407600c8440c10802d5800c02c0419951004107045407908080c00004001002801030031540c10a01c05030100f9890b0100c40380400c0c0305158006881242075800410900c00c6000c3e0f10001c0d11040e1800741d90305e0b0001c2c0046403440c40351400c001e4000719031b0701c0041a040c03094281c1003842032040d0024061410310140b050181e000341e009143d405032040200300507074034140140010780c600c0340e400414803110359120100700b034504407078040c011142c12441d076460345 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 461880503 1250 461879253 461879279
    0xb070308090a020a0605070f06061701050108030a09120c050a0e0906060a0b0a0c1b03050f07081b010f031e052d0103020d08130618051804060209010e04050c04 70
    0x19074000001c0c54524165000200840501d104400c00d00ca80002c40c2d006024410f4200503d080e00300c1000d21000355980c10b100301c2d0950240011540d5460b210000c244844040308035400c03d6134a550b00102c2c1420100d109509143c8110203c911410640f4002210b4907507045001c020500c03041c01044d0f610303014220301d0810070700030400c038031824207070700f0601441c00494191039080c80d40b4078111104018030724101004c8000c0170b150b0300d46c0d1420810700004102002a241d14201d814509444030309a03141d410955400f911000d51088008013100490654481e1801c000442e00528010442c04000400e500c1c683e405070855141c11070700d0b2420044018a0480d050b101c40c00801c20443d0010120104070001d0441070100034440c003140641c2005000c65903054411075844103c500040d1541c400015101c0024001450b4000400602c00a02031502c072100e603030a0300c044441c0d400542c2e00c5075541c034000c1d070000700514107110780a01c001400741c50310f00c5000d105800410181d40d446040100444020f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 461881753 1250 461880503 461880511
    0x1808070f140103020901090e0a0605040207051c020f06010504020a0e1c0b090c060d05070507200306160f0f110a0305180429060f3709050d02040b0405010b070308 71
    0x103d03004100c028441d0742c3c45080c01d0300f21640e1580c005002d840b1081c1c0c0d50058020790b448070303a129001003916824404089003248080309920400c0c4da800b40072200aa0300e031840215039020a0b00210b0041025042c541c0042540c2e500034035002c0e80d415800c2000401071141d140da00780711807440c00300b80010017000040c40381e00841410024440300080c2c2c2c000581500c910104e14856585410204070300500581c2a98082a40146603001000c5034804080a86c8450f140d058401d20600001c01c4002c0302c00c441118090020f5903484048155449095641e40b032400c0f4240100308440014502010060220b108814440d9548550794051103220726210001c5462862103a40f0f8070f660f0f0701c0d072540329000074082e51884602c5200c0c118803c900040c0a40150750200f14882000100380081e1602900410004544038415641d01c04a2003c60303842180e40341388003004139084400c1071002e0300d001f4142005143c8000c002103501d1560340d020070b0564600f82d2042c0f0119401044441c00c040e00a442a50300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 461883003 1250 461881753 461881757
    0x120f05090307030509030f071d07030b060a0e0a2c0603160e130c0f080d08070503060d080c03040305071503021602130b03120306040c080103121808070f1401 69
    0x2140c24404162910381c402d03040010203100d0001050030b680d880500107084201004800d48504070354845d60325034640c50555a4240410882d40028141800b0b8410a0746031400541002c1c1044c02c0c0810586032a0240050350740e201001d1040003603d10b025000d25482d07002c06501c10505a0482a404021601d002d0314040c41f0380c012a0008546240303d00ca0101100c80108070303c0b1258417148000316a005a044002d049241d0041000c105800c0b80c0d040a811208540101d079984a500d400c100d51104003518100d00141c020008910b40b0b20b030105c07030030807202d0255258628112060502c14034640c002e61080701c030303504041c0080024070f1200c20040d403a09800e05065150822240001c0c4050a1003080203229030000c21200004404a074002001c200d000b40071201e240107556410744031034008442c0c80d0722039801d2040440004d03100d006458100c13079010192420b8202c000c0c200b5101c4065461640a0003401440c0006410760100481b500501880940b408003d05000400603003603544041281 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 461884253 1250 461883003 461883011
    0x2c06032503020d15051f050d110909010819060b060c24071106040b070e1e0907050f070b090c28050109031a0603010e100b120c011d01020a020d03120f 66
    0x1704030f458003414080310440480d03805448846800c0183d48034010741208070000d030b2820b41d40007403928a200052402d458110f90f00c812030780c1d942800a40c0c0c2c0c0f00d0341194201030f120f20303010080050001c2e048403035540c100034080341c1007813514084180b600c6554400d0403c141030f80030001d0b1102507004026500041d0034a0700001c1c211600101c0c07030b5221030143c001801d0505900002e40307042d01c81d86090500110023003000c5900d44881c0e0300088201c6101c0309081c8184181f9003c01c264034010800c0f40c04540d08004a2410a203403911001c000481c010418240d5001c0d500c00c9008907910601c400060815080f4206180b5001407500f04040d00142c200d0303418810940c9040c408940e8103006050041d120650500751560b6100c01b280c0580030084510b103031880381c2d169810714200c0980010311140305c1a140149020451100b056070303030303207038502441c003041d00e03001034079843c02800080b142c0038881030040b6544168240c0c04214a5030050354140c0010b051440a0103070b90b003903405402605100c4110502c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 461885503 1250 461884253 461884259
    0x18150506040501081b010e1f08160c0308190212040302010609050c3108010b01081e04030c0f0203030a03060810050423010609051005012c06032503020d15 68
    0x15590701c021417600021158110078000380750784608141c80c45000e01600c40180c0c0007a000324040c0100c0501d030200c0200d0030020004003a0500d451003081c0e4001551f03150446101a81c8041e103000d0000b40048558002c40c800c01e0708810041e0000303001240c42c500031a8a90f1926080c024210303080340c0c101e0840303130b401c0c4800d006030b40440009032020714880c0c3c084038481844101110301055181600c0d04103c80e111000002e0400040d40310480c490403c1e00c800929035528404480441610110304044000480c0410040392152048401403841455111910740e6075030006031031504602d11850019490b603209007c2d008091100c40025071040b9010f0103542000c1e41d818504858078100e0000a8900158101d40301801350020f000509101c9001c00c85400c0402c04948010703980e01546000c07a070a50000c0d03559540c5408465421081400840c0718040c03d02c00300901c0350f00c05003400701100d401c410a544940e010503811004a80280c40059483e00d1020304481070702d6901c000040ea0310300c0c21030300f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 461886753 1250 461885503 461885519
    0x150503071a0d02030702100c0306050f0109050312030c070501020d0c090b07120f170901050405071d061309021008010504060f06020718023c03010503031602030118150506040501 78
    0x182d42984409180940c8a40e2021012403030700136180c058401e40360910525105d010f405a0044040ea04251000e02e006522a00192001107051241c903405501000e03040c10404960405507401003401300d02c0f80e141c0030b0207468072801c0e608000388a0b40d61a03520740e04032a60640019004006044c4000914140340300341c0ca42c40000007141000c4418032003280c12150500f40700341d400c8098400f025000c83e6990801119460080008a03030031292803240f110080b80b20801900b0b80c1d5031411541d078070a4055907940c000e024122840f12400070801d600d0360300303c000594031610022610740c80303559020f01c01d603d814104010b4440980c018048042c90180c10f000ca82d50103d0f500b0240d40182181e0410f014442c09030b600203104000141e0140c03881c050402da08803c2421106044203d16a075039401d91611200b01c080c103100a2050a1b031507802007011002c000489036068141c40c0c0002c00014003840c0444800d0300e48101d94000325103139030301504d05040035201131054942117841a5400c0050398180561 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 461888003 1250 461886753 461886757
    0x9050631060f0e03011d241603111216140406050f03130c03030c0506091b010c0f14010c17010602030a18150309051c052a01150503071a 60
    0x40404001c0101a0750342644c80075000b20041401c21301c184003224a0b501c00031621603584484140d0408400103c601c0880030401a46001720944003400040172a010800d90040c5503140090b80051800e000e2180d40107050300030720344210f007075240c1e44201e6a400080109501300000e0142c50040c41400180801640041550034032108504015a80d4441b5045c078450541070b03110013082c0340c0440720301004050f40007440c40a01c502c10320441701d80c1e4584140c1c0640310715511022800140d4042030448540d8030401074020041d001c1c842d0320101c1e0403662a16030749101c00842e20440b589d140e410309148a58854000d0703c4441d1a200c0c0312600d0750500200a459100c4d42201400700b0042911190f124428001c1400c0104100e0814030140220a80003a000d000c00b1030060741c403070184d000454941801a0810f582000da1995202d16103026001c8400c03440140400c00d80c4020540000009c00140c03d101d880c0641e101d21244120540c900b108045c80d009141e00b003003048108515a04c00c2c25007288003 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 461889253 1250 461888003 461888027
    0x6050d0216020d08070201080c07050a030507080c0d1d030a050d03090c08150703050c0705060403030f090c0311030f03131503021c05160302120402040207030905063106 74
    0x100150740d500400c2010882003084080c080c0d4050380c14040e90f810001e00720000c2a40c680f00f81c950040680d1010b6030003001c5e01030150040c0050300311025a80000703108400402a86115002407130500040f0116180b44c2641c03070100c030b40414803006103003444902c01d0303411310803d450840c014080703c4115601c0b2900c5000c2c1c3c00940060585031000f00082047d0702c6440001b4004010440d00f40720f00e401c001c0345094909a40d400701003440d210204d0000030b404012a00300175081401010301c2d4485a6045000782404216030380c106aa07140d501001401075400000114000e554080c4501540e02c1010b080c03408501000005a00c10001e61448007017404040d801ca13220702c00c00d01d80350134032120181d01038070405100704044030188501c014800040c0e4002c500a40e1040201046c0d407a81e0740d001d4040b842040c10203420108070500180040c5425001404002d20034a050301d45103558401160071074100100d0340706141d2000d4608030400c5203900b045004031104c5490703900660315040000e48406a844 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 461890503 1250 461889253 461889277
    0x15010512060a0b030408120601090509071818021804050108120a031e02030709090605030c090a15030f050615060403020918070906090b0303040303140a030e010203041104050708010605 81
    0x4000600156284424400188010f049a5540703240616061115070700c100d40038803400c00440c000c00c0c00d0f54131031454401541c0d0040d08010194407408425140445480c40b184d03822400c0c03050200d1048480820218100c101080141c4c6400c0c5058120343d0b62603448e91038a005520b480c00401603840d00260103078012000b145840ea8840390154220043d1041c0d0110f040c5a9030112001d141040303441d070003107110791410350700c18910032388601d820801d42c1d009100d43c0b80d05600c4850f0354615450010a04c5130080e079003500018210040320070765180c050155000383c0f400349105205900740881400440d40c8400d808031072548000f6401c0029840c2e0107140000f80c012600440022a103400000001d42e038112a001100c516503941c02035040a040075003d607448480c184001c101c01818000195006e0300d0341512070074441041d500c120752a45d04100740482c00c054855240d10f01c0d0050a20046d8000c0340160030003410191010f00380026110042d001004018000f00100601c0d40e000043d0754503070b9591 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 461891753 1250 461890503 461890537
    0x51509030303070f020c04060f060806010201050412200f21030f0c0a0302070c1e0e06060d110d06090204051c0b0c03131407092708090a0e0f010806150105 68
    0x221022490b03d080480d004d0b1f0040e203071040104d00714010014140480c0c0180e82c60540c550303502c800490986000340c4004100010345030b0030700310490068070011202000b814003001105000c03d042823905011081c010480d80001905000e0200110b80442100c07043e00f54140ca1424494801c428100006000d00b041c0c007004182c40301c2507842a0115080c85130040c3c103401010751102040c114140030a65014900601c00c1d9000480510b05071a4601c10302000300300f141000800a91a4007030602040c2c00c403000d5404000042000b0740354882c00b80500240e000c0140c846003048180000d0b8004082400c0303041101104d550009000d8040e681d51013141e0461040c1c99490fa424000c58080d498400189548204c07405802015030000d0b80800315003040e0414030020302d03100c84840c642c48003010362a80001070a101c2501040107a0000c0207a5900584099030480d5a01c24010200d541030303c0c4081c28034207049c01003010100c02c02105822049030b109461800181e60f0010b81103220b100511400f480c09 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 461893003 1250 461891753 461891777
    0xe070c020303042d0608010b2a060a1b0c12090e0903091009140f060409180605060a0f06080702150403031a03031303020d0203010609090f140d05030414120a02010605150903030307 79
    0x1422542c4040d000b017036001d0000b5402582c0742552203540481d104490710745010b00042d502c18040c0701c4c072050201c03e40ca60180c9400252903513b43c2d440c11080207000d00081140004403034010581091151307e00901450b1203001781c008011058401e000c0140820500700c05c140521525001811084141100ca103c0812088004a64540141d034458454a450403981010300c50915060a2089114903c20000c59850500b00481c03600f0074051450810807102003401424080c0240b150003100e40d004440040c200380c0701c0000b213402d0880b011800651100842000d4418403a8140031030601140034600700200321301e80c03403010501c0d480040d2040782c00c0c00e0707800c06645081d417200000d8100104140445150781c04c0540c040041114100d50420b440103c01003211400306001c5122001c0340d6500c0e1441e02c55440c2c0c05511002c1c142c1014060151002e0307081d0a40410008021107440c7c0d400102d01079191000304003204080701c2e4140d40a001c100500c2ca115076011003142d9101c0035030700340080c038545 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 461894253 1250 461893003 461893027
    0xf06022109240a0315080d080c340308070905060a03021b01050f04051203060f21100c030e0703050d081b04030b0f010605090a0e070c020303042d0608010b 68
    0x80b14001075200010002128200264140c010425800c402903e030091542d4440c4c0103940c0e00c6038144403100240341900440d440c2840b640040c003070030020100c59008512000d6480e00300c80504122100d019250b5040c1c0e104050f001203805511000314108107940c07e2a210101c0d445100c1c9100f4a801c15a00041c3e0b07102c810b58035840000117a40fa00b000f00400d00e041407104000c4c00043c0c0d400d8410f4400c801402410b088160112440f034503025007da04d2006211040c4440315082c1c070341c8080b424241902d40c0346104400c0143c0900c02280c0703400415900d0509070050215140104040d0003500440b1040c80450340005071484214010315115405640d200240070401c106040003400c0c0c0c2c98002030010a00000a2300d150081243e07801042259070b031800d00303a54510401c1142a0001d0a05001304608070752a1089907002d8402c0c1056601d0b1000c507400241103a01c0794212403082c180b504109140f035050a02e010001403540d5440030645801c040010388102c1d0144a00c00342c00c02d000841482c0300c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 461895503 1250 461894253 461894299
    0x4021e0a14040e01050109080303150103111c0b090601030b21010b0a0f050a120f020d02150708031b0702060417011107030e091b1209160f06022109 65
    0xd00500703100e0300c0d19151040009030340c90030310403580010b10240c00820031085c0402100c0c0261011000044c4440c001030055020305a15414121484828400c0300718030000741c0640b00014461180028106140c1c50400080005c01383c0b04604062030024400466217034400c0c102120046541280011b55210280a002d000c2201c5455045820341000007000f40180b600981a103d044540502c01500c50a000c90030b940714000150612441c2c01d20b0b0070140c1045070718203101c280054118180140d01c0120b001c001e9100d04004c8521007800000c00090441c0c01000505000c41c0e02c1e0b00c03d10b0030038160005416800740b03014183d03e90003000380400ce29002503121030703030a101000e04144c86802a0400ae0684c0c040d45000740c1c0504200000180055940c0c4108201380200c99100c07030800c0000741824081c0303c0001c0100d10203100b9800d140d8404440c40035940002c0540252200c44e2909100000f41400b0240740005512203c2c03500111030321a48a003607030f00d25642696002c007841d2103084000181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 461896753 1250 461895503 461895527
    0x60e04150e1609090f05011e0c0503060a0501120f050c040801050a060510050a020a020a09020a1101060f0b07020406092d0b03030301030f0206190201060504111801080712020a090303080604021e0a 86
    0x1580307040858005106010648e2401542d180d40400c0940c1820805443d184030803507190703511410303844090200b50301804d00203025004400c0700080e403004130080401240e0050380c0d03080c1c205a001c982044140c01c01d029036588014441e030140702e45840c24005c154001d0200080b00c00b07001000ca800c01140303208100301c19140c4d40040034803080940d10b01c0280000d43c041c01501d00051415158000c0410050040c1d8080b03d50348144056807615000c2610b440740c2004000302d9110b6190213000039413103003902a195040d070400e50180d0b0407001a00030714190b0101d02c0d0715251902e05041c42100190707804000d80b4116034100403800122801c40c80068054403550140c040d040868000c1d131082c00d5415800101507071401e60302000384072604c12070304499004048582c101d00d045000d00c03110702d5200740246a0480c55078203102030b449001c040d0400503070700800c9a050001d0001c400800c203160f03100d03c013141c110b03c0c26101140b0700035079000007100c02004003004c402c4404001980a10061113400c4001344 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 461898003 1250 461896753 461896763
    0x11a19140d0b1603051e010501080912040b12060d0f06050a1d010b010801080f060103060f06030c1409010b16030e13020a020c03060903040803031306060e04150e1609090f 75
    0x2d5840c1010380900814280241c050000e460200050280594210800f8280c50103d1b00001c0c680c0c070300001100c024000400e24009401040b0328510006110b00c054000341c01d141c44800e448580d00e60702c484c42120010042e900c075014805082e8045103412703280740142c580024001c103165031011550406070a40341081c250060f1002c0310104460010352004009c240300b641c6000352a40d880c61440c1d071300c0b42c140d809452650800001040081e259902171000800030303950115070940d8943b00d40c0310900d095400701040e001c142143e11064a0300c12801030242010340e1400c3c1c10f02c2e83c0c0305041c50030049001401001d1091074112507800d0b41d40c4109450b0021180b85066541c1c980420b07009450f03040b444400d5000307100324008201c030954040196815111100011819030352554000002c3da145010142d4441d03a075188041f411241a000c00c0e84142d0281003640350780681691340404850402c019a0580e401241f0303005130280d04014071707004540c003071130000c640400e040c00d08070054031140f400246 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 461899253 1250 461898003 461898023
    0xa0302060a0e03060609011a03040c03021804140a080a0e15030c090f041a01081f0f0501180e0606071106030a050919111020011a19140d 60
    0x100e51540440302c0080182c080c1d05580b0300e41c84070020b01001100a001c5d0b0404031007208104051403452001a540c454007803501400459607a4010a101c0311540c2500383c0700ba0071003c100020320070704014403a03414240000504001d412500c070f1078003502a489507001000406c003400700d06540c8160418800c03400c8880a595a41048402255a50b101e144540d00440030407120307103030038541032007161060300c0c1c00d1416410003591307003004450b0100010544c64401c03e90000b1540080d00c012807410240c000f8903458003c00e03050100150903c1361182080c0c0c0c1a4502d490184801f0040484c51608024140c031042d803035080c14505a54082d03040144590804404820042420019081140501000d205035400c1070f6400034a59000c00019401502c54413121b02107620a042401082d88003034000d00d002e28a40e114022403c044014121a40b41c540c1c0d1035003c40f1468440b40d4241d48071205049a0207000030820407001000b0000b2841800400144403608501070f441c3d101440c164698030905000b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 461900503 1250 461899253 461899267
    0xa11060901020c0c0d0804050607260d060e19021c020c060105010801060c081c02090d0c030b0105030d080121021f091202090f04111e030f01140403030b0a030206 71
    0x24001e400030601d6042074480c400000002d17003003402e191145590401c6ca864685401e29080c04880d5005203000c40f580e42144c000b51f0392003001d4802822030400454070445e91003d080303882c0c60582c1c0e400e40100b40c3c030940010a1040556503440006500c400003c0c0c0540c0ba09004241050010140d000e880110ba0000074450340380030f0089a9035050b108240c035048051390321803004071005c0da92090005c245050810499415910b14400200c10140c005805840d10410f4800702d00d4441c1094021581c24001c6401403080001e02e5807418090130f01a002070581c1405201c006207130603010f20079118006c900f24800b4054a80c084c03c1480700d076801a2080015960114111200b4003581045070006000520b0110b000340700103480764116600141200c110341c640035031003e040c0d080030b0811120107448003040104c0740c482c50840680301030170940416004010300b040c5400d0070441c0f00c1c0340f1030f507900d0120044410845003070b5882d000740e0140350004091411a02144140c1000d800c00f940c00840441c0742 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 461901753 1250 461900503 461900521
    0x80405071a19030216060216170d05060f01020a0201030b0a0905010e071202040303090312120e0c010206130336090603110414060f060405060307081e01030302060c0a1106 75
    0x10002c50b00740e0050049008055035049040780260103207912803001c4400d1800129501d6000f5003410044201e00c11405078080e82c86d81d0806001c80c281141001010071562560103261107401c3d409a4262440d01440d101300000030340703440e0520802814942d440000505030388a114241000c0c203031690040142c1c0d61030341e80e0340c2c01c040070483e049000280749091040c56080c15000b0345003126416210700690031f003160740e088140120304420408001c2e0307441a281c440f408a0040d0418604454040c24265a2410009040040080202c0a6500d184400703800007903118825011180d00d031b0a00c14071100c06204041c0d080c0a541c42e2440410800100c007064015199110100310f910035140710304503e021200f800255400d04900100003164000091075074100958154800d5100804a40c0342548800018210ba007060703d000e00011034a10410a09840daa068034800a01103052006190f15654009584d1800205200000c81000c2002905180901401040780c405901581c01500c0c3c44401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 461903003 1250 461901753 461901757
    0x307021305180a0b18010f0c030b0411090312160b010e070e030a15020c01060e010e04140a0c050103020901050d09050c03011a031c0e090406020301050f180403080405071a 75
    0x700c01412281880032030344240c00203292590150300c490594400c0d6508030360917641212001c04040345540310012510b04404a01c00d10300508100e80b80041c0400b112010b21040f1010311000c80c507a00420440c101031580e0014050642c2c100704100c01e0b680b522050802c215020030004018040c203080400802c012038a4100d0364401c072441da0343d0718610b9902c40c0c20541c5e9070b280944041c12210701e2101050b520b9000d900140f07403408a41c4000324180f0360303e41c1c002507458001d074000c4210140c00340c10f100400520300405002250b00100400071208c3c651034142d8010124402e40e8103050340058901c0099004105446004500050800012150b420050303210030040c190b0324840e5107002001c00450090b4450100380b9100a002041e0074103002c403604421601740707984c9106101c01c5004510640d40c07004041d903c2035125040141c1c6a524010a103d031450b82d8400c010301c1000d1480c080300c506041c1c4086260301035014540100c2075100e604240d0b0a1212541100b925410030006141e60300400d640 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 461904253 1250 461903003 461903011
    0x50601241d0a23030105070f080403111f14160203032a07031110051512030705071e0b0403080708030a06080f032505030324060a030e010e2d0307021305 67
    0x1300034080c941c1d400c00220748056080c0c6507034000c1041c840104003c680702c3d44449652081182c221940511103507000712800d98160341c456a01c0742c80b0b60720788010410a504054105220710b4086160a1002c00081e48901000380714a402c50070008040c0c46440c03d1030152101d580f031101c900e655981160800401ca40500507a00f002c0d44600d1928041448142c483d151080c58410714510f1031200d60010460035000048080c00281700c01e0210704003082081c410100104004400e800d400740d10680141e04401d0254005941954148030400215182e90201d0300344c0f030340c0840800d50b00d640388a06d65004000750341000a41d4803c4c50440341ca1100c00100400480072111502900141d04030201203444840e460018100c0d00f0a20108201a8074113081c00e50750b50b08102022151070030a804a00d06400040e14070300040e8480000b211442001c0c401d500e2141d2502d400b803c81c00c04030b504000789440d030100002072000b11800036125840c40c1442a03600310f9130300400c4d003890403280d06101406000261 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 461905503 1250 461904253 461904259
    0x1110a0c15090f121d0f0f03010b041401031a0f070302071a0c0417160603020c03270103060602030910050f0d0204030b0f090a03080601050d0b030307050601241d0a23 73
    0x6001d820318145d201c0d85a000c203074401402c2c1c200c0460303104144103922030800781158166403240c0c0461481c2e5128050420019a800e800d1032196145d030402c414555861504006040074075404d00c88400c0110411540c0f100700e40c02c3c05a512078103460401500303124441d400c41c441100406201021902d0402002103841050b010643c020003002e1954940c148400007401c3d41190040070002c0d203000b50040c4c42003004410a5a06180851840c45140c030f0b41490b82c0132010000031404085913070148a11000b07000c05100039402c14003020b001c40e000c4080104007009100d40410842030102d00c1030112341045500041c00d5450f256070345070114003e0001d4541d950000c111000180f45a0b0000230600103094041d034034010f298480c600190303499400303070b165240000c0d1215001d55054400300000d00d0050b12407002401b80e90301d000e100390012241510000801200170551140e03051740300ea6031840c1211050500650540c02d400003c40b11804c07a8484100e84604c0d0f41c030402d210f18845040b1018140507 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 461906753 1250 461905503 461905517
    0x70b0f161808012c03090a05040510080f0a0512031620010e0f0d05030601090b03090309182e0501110705210c0604030f06200f0c01110a0c15090f12 65
    0x604e02a031280034104242c0c6d041803640a08000d01e10705900155080503580031007040ca036850703c0403e410a00c3c41e0320715150301c0d4400013811080003020451030886c0c21500805d24118207181d21220704000490510408014404519500d0f400d20410780c150003102c10710081140002c0340c1c03003403a254134201c6e01200d0103004d20a107505245000302c007200d00ca110f059481010160810b9203c80b4035400280c5044020310083c0040c40c403d480b600091902010204155101031801c03000030886a00070010451303542c1d8603103590030b0802241d10310341b0b42618401d08207100c0c1700c2440c0b1001031402156604c40c0d984000f4203003055202e0f02040c100c1030f100341d10300310580e52030101c0c06062029503c84c80c40010301d683d001c3d1039001c020404540c00380101c00c420006e81c0400741c41d800c95038202a0000600340035903800001e1040e8030607109100e02510347c0000644541007400601000e044051940006030103011210340c81d0403c04041e03171084c5c0b40c1c1540090303442440c0040d82041090a00c19104102c041446 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 461908003 1250 461906753 461906831
    0x60f030708011509150509040f0602030423010605010e0d150504030804020909070f1206090f060516110c011b050d050703080711120901020a0c0b070b0f16180801 71
    0x1303a02a004484a00c00d221021881c500001d2010b42c000040040d144e0414a96102000135111300042d409940204a504448042c505e90b0800603ca00700d82035515030325003007040103940d130000b1003d106400110b440204011003810400384400102d1980c150640c5040104800c00d50048c0050740114000e50340c50761030b5070f2040740d110340c1d4110a000f103100051041e58104054607182d03070b60ba40c265200c0d45010802c4086669026501065040e00301d0345035407100c0c10000191458044003a55002626228400601d0021404d88605030111454100a034200e110001140080e0290140c10b501c1011200350240d20301c07000305607800c14031b802c400007218000820809071060f2a0740c0240e035500c4001e800b05a01042c0c504519a0101d0503107410340c010402c102000c900005900c20017070200c0d50303589644001c02d15081c90250402003032050849444001c2c4040c54031030a144222040460601814141c45840c007003a0910242c0d018400d00d44c2803600c00b0048160b4005940700c02640001100c1203560 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 461909253 1250 461908003 461908019
    0xa150314060f220f0803070207090b06040b04031b23040f230411040f0204030203010e03120a020c010f0218010915020d050d021b03120105010e0901030803060f0307080115 75
    0x40c0c50f00c11412810641c0304485614035506654030070f02c191804181d801c1d00d82e41c0ca020071307001196140c0143c0c201c05400c00180c022409007141d03018084804914150034521003a641e4091404050400e40c071a080c807a02659510303a409000d0a40d8840a8008120700485c180181d4030700240c242c0518100440d00300c10380e0141c0110306c802c00c02140d000802a08c4005c035928000402041a50760141075140c0c1182034a80d44a03900c00c41100c07d02c0540d4860544c0145802d403241840303141c0c3d480d801000b002d05085c080c034500c47d4004601c420050380d5500001c1e0a90301503c0e1410801d088c040c070020b0344010b034080102003101610002c0c0c9458020955a0f42070146000e10300e030091016800061300042907e2040c0000c010042c1c00940060808102440e8100615907029041c14143e00018a0a40e07070f03e10040300c68010242481d02804103410383d4040360305010f0600c0b005000c000c1c040080f0b14583e9510101952614001e001c82e000d04c0d42e40c00c81540a00540140290110200980815059 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 461910503 1250 461909253 461909281
    0xf0f071a160609030e10020a1a071e1101110405040e010e0d030f1b02030c2b08070302160c050406060203161214040e0a052203080a15031406 62
    0xa01011095416075990340c803032502904086108a04000341c04a14003502d9035286c1c403142072002c60398010f200c15002d9280c01e601c03440d212000f00311800d00c5c1c90100105150b200c41e204013880e202c0c800707044164816420903900500da6000d000c800b54200300000c207039905014040c10858108031410f02c95620b0016019088964410380c00b000344c2c00081c081612603020303400425030401910b000107100c10104100141001c01080c803100160030001c0d941c0503d60041044098001c4603584070b81c3e5829004907011901660040c18505119082000407070081c040da0580d0198120034001541c41c00c214139282c01c8017419402a24400c520b040341c08121284000107844c41d00d00160420003144030a515480f0014000101000800a1003440352441d07001000150005050380f0402c1145400c000740d2120a40d08018030038502915a12a0b4924106c0c040805282c86a094201030581303403500c1172540c01512143c1442c070718100000000004000d100103007810301140c0003040c0c41180d25405c0c00c9032052 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 461911753 1250 461910503 461910517
    0x50d02010f1b0f11090612030706110f0c010e0f0102040b090915031f060e1e06062101081e070e070c0204060305060f010e160e030f0f071a 61
    0x10009001068120b002d61040c207070040441c040c400c200203503a40c4a00201c1c0d003030030f021145280460045034440c10302d8684150011421921290800359941710030b980c1c0d01884002910300390300c8078141c403020842c01e4208d44801f140f120000703a842c03007030441845c060420f001400260b44a80c10f60850001018402d440580700003c0300745150400f40801c0003140200600140c0c000c4181e20ba181c801a50f04001c07a80f25901d1034a00b0440d603030010080d8804540240d4041180515a40100074080905a8030110a082d51880a10558032243c001c00c81501030070030340b2020b9900c14041c02c00342d940c002c2046412075421034122004410500d07003000c01c0c1041411444401d90150704140300d900c1d18884480e0f44a40e562500b081c9049094002800390b66441d401a00c41c0c0e000413080c4502001d00315403ca001d00000341104000342400040064804010b000000c10003d690f4071000b0b940d5020f0010042600c00030003228500c2000081094854401e4800c942d60b4601112480360181c200000755288 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 461913003 1250 461911753 461911757
    0x121403030603100b041401030c08150415020304030e03120d0501090c0c1403130902040801180308160207090507020319030b060301031e0b070207080c0303040e0103020f0d080f13050d0201 82
    0x843c1050f00d0280c0c02500440300041d80c019100c802d4080c400f810031840600840c0500c200e550180c1c5008082d40c1055200c0c11302c0310124a4450403c40400c51040d14820484075032500182d4a59650034111481403c041200b68903000d00c4544070303410404000075150700c03c079280e020003003170f42d9900050003103916035442e07030012605425418010440b8100400f8000e60038a003941e141c06401c0c043c048030300b1695000765610940c0800c1c28002c482e030900c01c07184213102d040a15490701d9260b4602410400740100300d607840700203c122000782c243c07091000d6401000c0c250414400d905045038042e459400400c881c502c5410386003007509060f403103030040580c0003030081d11031851079085496038840b500001003501141840c5900050000b1310703d004680c810301b0141d002d45110340c100817a042c02c01003001b01a9200382c0c800d00041c46595030001c0e0450440e40c2c111001c7d0241000c10010890781000c000b406055000302090b00c2a054110500a010b040201c00350642d0b0b0548803070410001713040980000c0c0c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 461914253 1250 461913003 461913013
    0x1050c19020c032509020408071406030621070e0a06060e01080408120601050c0a030c0b0711030f03040204150602010b093108040b0a120e0c030a06020f13121403030603 74
    0x910030885140602d0f01d544407249010345c461407240d00fa130340f0130b81c0404170f1039000c0b6408015944492002c403142407000c036492032450402200240ba0f00d1008a10130400d100144c0d0f107290b51010401c140001410707122510405403a012401e500244168451000464882036400704503601c18401280302e0b60348112818140181c003160201000c00090441341804001c020044007403404101b070030210f920a680ba21298455460070081d00c220240102080c041d20704d5811002c0840842590202d02c00040e0282d140e6403507000042c05080a0001c0c01621400310034081249981234003e54110348054910900d03684942c8018062040c3c4005240d00707210340700081d24401441d0070007141016024021607070410741c0720b40b4400000e0740690820300200d0003000f000b103070200980c01115032140003040a00300410104010079200c40424000911035540000c4d003170030307440d03040c1d099602c204444e45502e400261550010600113101103c05e441c2c03030700036201038041450008201c0c0e11413100580604 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 461915503 1250 461914253 461914273
    0xa020312070207120516060801050319020a0306020c0a060b09040b150d020406090f1b08041b030804120b09010b030c15040b0a02010504120c240e01050c19020c03 71
    0x40040c91000e0500381c00c40c00340210024800058440c03002d10540294040c08440e0036400c84280341414030b80c0300500340704400300100625940441c0c5c00d4580e072000400b440701c3c0c600c80d00c0010b1081000d500001c20345031000ca22440765003800996242400d00c0360908109640c1c080c03041000114044600030082002500003e0b070b4002000f00c80180345c2741c00343c070042021900760300003404e0f15010340017102c49540d2241c406000d00c4d00c9005070480350130b03c08200300c12440c0b8880000e00300040208090043e661111700303120318103158181500215000402241c64940350b030600a16081c0580056030040055000300f0000101032184960364180100100134020b804010702c01072408d41c0036060070b605c40a0000041144181c40103140300310441c1e000044a142901c0e25041a1820032102820400940000720029041038480c404840c19102000c243c174207102c0c0d12001901082c40849440c0d4200340c00d1082c02c103c1c0e04081e103105001e00820703a998100e0140b0403a41d5039454412990301d5445a6150 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 461916753 1250 461915503 461915527
    0x1716032409201c0b120a06020c070e04020607110109090e0307020a06320705011d0609160521032a010c080109020f0403021507050d0504140f1309150f020a0203 70
    0x41850404e01070440465441181242403d06003019010341c1c0340703038001800c01e0824000384254000303809400038038021800c4c29004076403140200f46004210010500c00301c0f0241e070184030207000814407586e0078464002d0020842e503c1b0f4204d10001c0340a260981030218840340500c1034168140e081445074081c00c42020614001d6041282001c00d07280d0080250300d011600038010b2100d01001c1d641c1510120510241c02441c08a00410341c003155040250742800507419001e01604903102151303484c0c08a12211032200b01c40c0905a03215103a8440002c039081000c00d00103c040c03444c41c903c50b26400d900648128079007030b0b840d144007000000e42c800d0014411004103501620711801d4405a4908290f100e40c041901e071001000040d03590306000c51064100441040190b01250246c94542d0815141c0a90b07160360755940d4500c148106c079a01c00000d130945603034001c19043d0245010521140c0414100301100e5552040303014407541c100b0300b14807009081d500803a0151b400c903900442c07a02c04403e0314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 461918003 1250 461916753 461916761
    0x5010501320c070e0f04031e090b03150a150504090f091407141c0b070c06050c04050301060b031e0405030d0903050a1716032409201c 59
    0x2000034503410100340c03200055460740030b01100704802d03004041803400d0000100140c02c005011103c0c070040c010400c0f00080e8001a8100c1c1141358400061030b141a414003030b02c500045070081d01050380040100036030043e802c3d000c0300300740b00c0590340402200d44401c034261810703010000140108404100400c401042503003d4034a203648440e0003d0140c2490303840700e0303510020f050312400c3c0740e00024060000740d08002e558441d0800c1265064501620f024080c0052092600040d04504a250024450074020440c1c441420f911020070030603460120720b0341ca802d03000350007801d0196180640200e840c1d0300c208100c90160044805249a001c8600c20405041348000e0003156075010038031107203868182d40e000d50524075101c0e84403a500c40c410440002c0240c410382d104140e90400e101c080c41901e0010340d40c981e500503840d141c00300b80d0780c5070311120041007446031401c00c100d18002000003c0d03106145c0e105940586000003803401200405440d22002d00441c84049950a0104008200800203900c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 461919253 1250 461918003 461918057
    0x7080103081e071b030b18060a050604020d09060c0e04050c12060d051f050f061f03020c070f061418190302100c1b03050c0907110f0d0e0405010501 65
    0xe20503d810a6681ea10038544444ca0030074209540d82d000510030080c00782103950303100000719100781d00404080a00c1e542ca16005c0d00001e25155140302046480d16a40c04450341003000b02800d1215520b149802401004143d921600090b2480704c400040c2c9050b00881d4003400c0b51210075410612102507070b54541c480a00b00d583e1051944200c0d1300060300500106070000740d050801107109509a29410030746070b005050049003403011042042580e03a06520382c40701e04083c00e17030344248000290150300a1040302c0341c100d69071251090000b42013074156601000d8031643da6418011619903000b41c0d080c1e0181c20182280048c0d0340501c80c13098208400c9424949072103800201d085643c030780120b4019a845949080040c540c030004809000247e461f0640d10107000e0b0540c00d15901d1500c3c0c82e51202d036041256445241c071400414072440c482c0d00400070030821a42a907000c059491246a52164122261004104085d142c90034030300d003d2150070304032801070310780f001800032103200442d25000b080 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 461920503 1250 461919253 461919307
    0x181b06030e06162d02061305100f200706150f0303050a02160e0403020d020705010905060714010204150e040b010905010c0321090212010207030c0f050a0f06050703050708010308 78
    0x4400601c00a0300d0901010708004c000f202c1081e9405400402824030800a0a281c0d840d1010030000000a1000541c0618103189410001d20141034085c80d00160488039180c0399103c9203048840c04d0a03400c200200f06d1644034050421092445400342c0c07444440d68412400004100300c0c080005c00e007d4801080d6420140c4152200d41c02d19001c0c8403d6000ba03500901e15114000c000c0204054042240380000003082c001010300030b1801b400203008240700d00480c1e0081e4030114001080118070036510216074003c000039900d0b0794a03000315407801c03800061034000140c0780f141c02c101181014400c1713030710244041c0c0d607140d400d0741040c00540301066048021400c100180c0350707160344c02884400d45071007514511808a14080e1500402c0b860210301d4403010075591040080c4030000360004101c142081e4040b024444003e141d00300141030542001019204400d0200c4046c01c0210036480703144510b20701c1c0c40c100115110300031b04595242c0c0900004101705410070840c004003100c189072140303921501c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 461921753 1250 461920503 461920517
    0x16140d020c18011a0c0106030b011d220c360605090a0515041401050114030903030109200a170109020702010e010e042003092b080703181b06030e0616 66
    0x1850844c7e001d0350040e00c0309440d00c0c0040c08001444c04c03c280c20f1200400000c801070924002100400060300c1020a2a0503800c4201d410442011002e200404941a00708a448290702c110320744080f0000781c840c0000c407001185600240d003440b40e6016200080c040d500d4030383d140c0c10094001c22010f0402d500066004015403103036a0b03140a0500c401031011b00085a0354034040014181e05840b00c0400f803400000e00420030240e41c00800d880c111400b40201284d5109540b00f5410081d020346003d400443d000180040c0c0301d03402c6004010b600200e0402d851007a1380c0c55080d50224014040000d00088018035400b03090361080290000d0444001c2000940c25480303c4001c16941110701c540803040c00200c02c100c1003500500c21504000480c0308505a441d09802555817030340100c54100052155100106480ba0700c20381c488900791549407401d00303030610742e070030820317100081002500d00c2410000d402003a528828051400c11900040080a490300c8042a008088040443c1c1000b00100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 461923003 1250 461921753 461921767
    0x201050f09040e0c10020f0a0f1a2a0f09010806060f0d0b09070215010306020a050f0c010207050105070f0c02040207020f0301110409150b040b16140d020c18011a 71
    0x510f11601429048050003803030300c014010b01303001c0e0b0810f0744d0302c55400303542124010007074094000c00d14030110b0341c3c00306800280080910380f0105000d40e081c183e28500f00d00e80c007040100c090401440c4588041c800410308003201103981018588203030a40c1c400d80007020f0101c0e0715154080c7c42c100d038019500030140b03030a2200249841280790852505c1802180d2aa100c6d40b8183c10700c0d032030150b0004c200e40301800b00040103114111503c2c1d81848024002640020000035191081d0251600741442000107aa40c0c2449607045001c0e400c029010b542552820011035244d80c05095071904540840e25011040c48060b02000000d4201d01403d0380c101e545d015048070321356021700c260a5040100107115803542c0c1802c40c03000031243e142c1d24510311130b1160b0f0414460169818103980c211841e01404032f0380d0781c4515040c1921100c86103001450024020b040d800720541c08551311000302c0700b550840f9220501142000340001d03851103030702d43c21050070005101e022042d18200390790080c070030002494150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 461924253 1250 461923003 461923009
    0x220f060810020711060f1215090708010810050615090402120c0c0d0302030402030312060f090106051b06040c030204020f120a050f0903070b061009180b030105010602070803070201050f09 82
    0x603100300029070703034005522010080c04000c030801d0104142ca4943c101156a61b03041c0042c40b070b62000d010b64a03503420004070708480c00c1904006c8a10050f01c0500300d070902030800752200c1070a000e800d0035070185000b05a9404900e1040900c1440001c02c0c1044018020b00240e109500c42881360790400c0d020418941c00c2c1202580c030f40d005110322100a5a0b9070341c150300d640d007041c14594003c6d007018010424040035a400109482d0301041d103070f512401584480340060023a102221801c0d0f000f030f030300c100002003050300280a04001520b051012998800340c50507245c0740d1100300c400508503a00480d0030320240c01c0c20340c007401c040426001c61500d00040301d048803071812012500c14001039219020021969600c0180940092154000754103000003580c98041054000342041c0c040d0200c400d0000e01644612030b107000500355250101c111510f059900c1004c0c0541407800d501a41c03c00c4000100c0d544009100c00466580501445c101f0803a0b034011201d41d445280d400060000034808188599 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 461925503 1250 461924253 461924263
    0x60204080606010906021f1a090a1d0c2404121b0b07031b060b0d2001020c031f06031208100e090706140c15010311220f0608 55
    0x10540d80300801891a02000041145010380c01080131900030b048058481000100c180110300e5021001080e64442a040704211010300b01040394008001030520454510b40d600040c0d001c100701e0409041000007800c2c2603540d8420a034901d0300140e12082c0c481c00c0e07150030101c0c12000968a02041d01d00b44c6e41d089508a9600c0685050310404240007106d044910480a00001004010043c90520b40103403009421074042c08038130220380d070918400c8020040f00754040d02841000400071030075a003c60409501c1c1c0d05404a821000c811140c41c1d0182540c000a00070380180703002030050501200d500c94400c0070b501c4110461208549521000c000a404401d1040e41002181d94610003072400030007401c00c102e2103a02c000c01c0d0010300024131442c4080882c100060300c0103030408402031803000002c2285840356100c180c1c898080d880d54854034240c45034030746040703a005a415020303c5070404100080c209105400000c141a54121401e080d402d0303402003810b02080810000d03650395a010924101 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 461926753 1250 461925503 461925509
    0x3050d0809010c02072607050319020909030c030a1d0616030f0e0307090e031309090309061b0609020d060e030d060f05130b0a15020304150201090201020a020f040603060204 76
    0x400c62410400181d80402d20640e52900c2c0c041c4000d2208603d0007010340f25801d0b00642d004000000700211410003042041440018540a401c94840c00c520321100b9403841c0369484102d2140d410640895103d030030000540340e100f1000809907150605002c0b054407007100682800941d0341c51030035103100a50b10440680717204103405079101c107004503a107802813140000a0782c5509002c1443d04540301034400207810400c3d1001c0e000b0004c2c8004200005c1440c50207101410698102906070202c1e10071a81e41018442c80c1c42600d0716240c05d0345401080e0351103103281c070540200a11880d203800105142d50030042a50380054040d081f50901c503203a01d000c5e2500040e6141031640001140c3c442512644100e030006c0c2070134003900513118149000188501ca24510400c0201e07128071001c515690b6200b40c2764000d20340540c20340d41070b00682d1006901e88d0440d1059243c4d044108161401460040c09240f42903030b8141e01420b00c440480d07081051985144170202c4e0429a203060101c00941d40b44010009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 461928003 1250 461926753 461926757
    0x2106050406020a0f020f0703020112060b0313030905060307051207110604120906050703140a050f160c0f1206050c090414040209070c12050306061c02070c080622080403050d 76
    0x1403a044150080d044d0901e11280e10300310f60010b560390426542c0411100f09403903092078120036444601411b10080c04140d0865001410700209000544007401642c941040c0710b03882d80c64156940707004211450004646040204801304180c0b080c26220321440c0d039100d969070900103084807404581c24540a000c84040b140f10014200e100722641e00608580010905480d02034645042c550700100785900b40c4428008415010441810660242003500c80d43d02e0722000083d255039007540340c2650402c202c03a0941e59a00702582c0410f4048041407800151364140d1084410300c401580e8587c003e150040000c211403000307010920140e0384501800313002040c7c542110000341070600410000b45000340203075080c48180402c0d000062101d070601c10030400d440c24407503180da84207400f0820350300c200b903058a171380000d080494400c40159806040b040340661420b9a203151114401595090300b69a1707800c405030b00103288180c18034180c030300c240d49900c82c01b4100e00b40b503900c3d038506207400804040300e00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 461929253 1250 461928003 461928007
    0xc150a06091e2a0809100b031504170a080a150b040b130906170f03180d0309350d050d09080f0c0a0b07050702011437020d0903080301210605040602 65
    0x9078005c0700f005101780e4600c181c4d00810031031030014002540c4c0e10441104540000a0070001f9003803060b140c0e500f000161844503201d64a807030161008280110031202d50380300314a4000c15410703248103050301d13100703540e10f4000c0c89244c9400d26007500365541100798520548000c030341c2c001c9a10203c1e4001d450003002d560841d03d24000c450421181032548900202e8010b03481030061680032103d10381811600181a900c00a000d00c250508660080441e0030480c00c010704605000d0102c80b000007281e8011542407a482d01e10758138200f20a8681458034001c0001030414030a00001080a51000f1122846605402c0c40c140f0120103118440d00b00408113102c1c0c0d000105080180a003212406501003c0c5151441c508000366001034101c070f460084000c1025004150410102d503407000c07002001248540d1450383d49444c0b030042e03c001d4015505000180a05000118101d00441c501026690311900302c0381183c0c20520007000e011203d81e911100301c11a840c90364041003540c89403600903409560003603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 461930503 1250 461929253 461929261
    0x31d0a0609061205040b04020f0d0807050304031103030309070303031104030c090204090b15032805040b040c0f06081603110a0c29060d080c150a06091e2a08 69
    0x18003c0d000c150000c059042c20807041100150b10f00e8111940950304482243c0c06016090101d1900d00c1d14180040c904000058840c4c1030000010240c402c8a100d924500304221010003450784038041680c01c0010740d071000f101440001d0283c0c02040000c01a00c25040c00e0a58a864054000015600110240340e00160038044d20046020b03480c0d926400740c98603004514060002c405030301c001030a548050400c199100d0b802d62648103080e03000d864140c1305014034101810074903080c40381030300d0484001c004000001040c1c1040d003030315400c54030251505801580c40e482000000c40c00c0e01c42560806a40c1c080040745401c4140290203859010360303850722a40c031249042405040d101e001011460b50b00284030701045035000d02c039584108242c81d1106080080c1c58820781c58005c1e0984070b85a4011011802d01120020035420720401e290303c414800a6551280d0713400b2030b540201d00311000c42c410380840441c0607075078000c180301100c0c00054503000d1000483e00da50b008445403c031000074403101c0503c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 461931753 1250 461930503 461930507
    0x30303190b1c111f0f0516060f0b04052217030717010b13030602070f050304080d1b030f0c05030415030b03010f0e0d0c080d020309010531031d0a060906 67
    0x2901d001c5065501c4e8800c107100c8840d8882d1109010800c8040000794403d0300722061151040d102096407100d410000318040b45002005080e05004010320035103030000000c3c0343e00c2c2074017503280a101c030b04c00980c9152075600145c0003400038000041d0343d9100c0241e0415484c00c03034007004500c43c07a240d6845500300c5072805203050401c041a407001003010401d00101803c0d112822940e4100e0ba407102005070b0b5034801d45041528240c041c2c501801e240004940042c0105003c00c14000e101980d0741c80b602d1640160310100584103480b03a0141c0003d26012a00b20942d005c0c03074464080c540541c007100d04166540300c0f40c00039512520300841c0000d440b50000c21303d07801c0c2409007048d2602e0b940800d00c241c40f200105580e41d4844100d40608100c10520050140316102040b580315003080d4900750341d20300c0d10b4410140a01400c0c1d418801c4110006803609040d6070400e016000400700c0e0341c06200c92441a00c0840b401a4403440840f903d0541030360405d1181da402e00c05800400300c54641d044401e103841c0d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 461933003 1250 461931753 461931773
    0x180a05211603330e010b010306060302070c050108071403090a231011040504020309011a060406140304030e0424230d030908100b0a050f030303190b1c 66
    0x880580700c00c000c0c000788009668100d103002c00c915035803c2403400304184114000180780101c0c0e0030888070300c0e024031140d4098046d0403113007490780c003a00c040c400725548490071801c9202d161009440340d10081c00a126561190309025013009291404a144000903c500d15059100790340d403014942c0a12000c104120480c188003000e840c800003040400a211490180c59050803101caa111650398806200d0780312801e825039024280140085490b071415850303081c002c105031001c41e4032400025060903c01d1030128120740c10b56040e0b6031401c12840106800c031065400113003040301803001c12541410151500d01ca5510907441c00619651400c000c0064018952090b801141801540c074441c0c9a100d04d002140c2500010280d0318a0305506150400700e40300103c5400c00100350240c0e080d030400401468024070350940003100c14180c11640c44042000141504403126055081400000d071888a10304603078858511403a00072800f0b00304c3c031000980f4901c0000082140c2543d406514051000010f2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 461934253 1250 461933003 461933023
    0x1f090303140708070c081c02040f091b0503040c05100509011206060c0f0c0f080d020d0306030c05090411040f021b07030c05120f060a0b0f01080c180a0521 68
    0x40c20807905003401c0040c100c0301c2c010700c803c06100320000c0d407204011101c400c441c0b00340541c1400840c04d111590b46440a54007501c141c9446012041000c40c02405600c03d800342051002da24404820340c200c001d55403504000d00c2501c40b40113448000855440e80007400700210541e940f200e170781f912060009040310350501c040d0b45403a4a0a0300c140310301070b0045003410100c4e420451900640d011860b0000d0380880641224885018003c40059401e02c00140700c0c22a403429020795964051800d0114100c0c3c019110150450b42d4542d800c0256007840c810064100d030203018140240d450880214003030b540030182c0d1501c0700f40d0014a0700300004c9030502503160650410041d1191600c0d58803400b05240b500d0180b07034424100c0408072203445d401000302040507051041507840300c3c40d2211004000b06440e0107014001e080700c048030b1055601c01c41c40544100c08801c099410701245041c1611062a2440b40302e4020803402e6010419980d040c4148806070340c0c2c3d0a01010000d0100a0241081e05400d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 461935503 1250 461934253 461934281
    0xa05010b0406031d030c01141b03010e07050903010e0313050901140105160c031a07050a091404090f0605010305010b030f12090a0510121107231f090303 67
    0x100103001032800c030300c1294211009894003007144485620440700034400602010300910000446001401c03043d003050710607003444000d034910390b13803104c07070210107504900c814441c203250410040c0580b100b1807002540100d10791401c54202003c010110b402c4644155441d00d09501c0403c6071820301207900c503600091708059a07124415450402500c2c2d10102ea504c100d414408040340320b041400e101c0f0018115150803144a0301803c0d540e08160700010700004e00d480d16018030000003032125001340125004c00510784c0d6443e80403440c0c50f2030604240c448203070903035115490305000808141a1030340005014005d400026141d451454498216840d07181c0490098001230b488070100500403403403d940101c03651425944050040000362015030766000140d201211168941720130360710811032500600d40d56810841040b640d118210b403400381d00002004045800800c146840d5481c00104400e402682103e00105241c0c80b1282000b1645803914001556001d802003815858000c1703c0080940d6 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 461936753 1250 461935503 461935511
    0x190b1828030803040303020c06010b0c1504050a030807270807080705030721170c06060405010513090804090c1806080f0a09050c04052a0405010f0f020a1e02090a 71
    0x800140d00030118440a408948040f0016007854001e030111048002040d080e205c1c99a141c41d800645604a202000d0b11071142d60a14100f80d551400c4081c0603c0c1c20400900c5840d003a590100d0301020002c201d0020007400e02c5000d1200c2c10014603a4441001a110300050941403151072841d101d40713540000e03c282e10030342c0104201c0d100410080199808070b006100c1c00014170034030b1000b00302c884030010026150407440110204400000c1c0c41501410001c0d10f020ba11803a00f000150342081c02190f90001c0740d203100c1100d80d1411f9202028a501c1003d00a083c0b5079510b100070120341609840740045040c1c5540e00c501e010148460f00c024219a0801042d503080840035400401c03001801096299070b030384544070600104011610303a40c0c6c0e0042c0140014a03250301c2c0140045002c0c50041c14032450310030100c081c4807a003420746043d510181d4440c0720080070007004440e110146030802c01903004203001e04012925103160820203101105078000c21100920611601050003020030381007600d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 461938003 1250 461936753 461936809
    0x11070f03030e0402040b09010c030e090703051f08070501050702011209030903050708120d02070503091003021801020304030b0f100e040309031104020a140913060e09070b0c060105190b18 82
    0x11a0041d1f0368100340a2030220b00d100410300d02910741c0440f10910aa01c031154004000100d681900060311410890865062031143c1202c103000e040c130310340500210b5410080d0103010325481440900304040c0149404d00c007031154114078500310f0f07030001403e031700050b1200030a100384603040000300300a10110008200400c5020300b0340905005007502d602d9401d4000810340e080c80030410503242540070050980e09108a03941002c0c00a62200403e442d059030407444d1204690300100c04c0e201207a400c1404a04182e40313003c0c41c101c4c4014014449001c1603601c2e1000308200b080d10040c50300c01c2e4070030703185c010741e090031400e05115442c1000440f40c4503074010010a400e0683c4100100340d02c0b40c1c00d0101644030110705000806011422142d60009c902e003290000da0303440d41e404110300800d048403c0e00d0405481b1002410b143c4950f031012165a4480d400401090500001c4945c2584900c0510903140e500c1e61140000daa005015441c031240c3d81c609090440d250203410210481c900e8480400b074001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 461939253 1250 461938003 461938019
    0x9010b060c0a11011403150a090e030304080f04030803090307060b0d0807140304080d030f0e01110708090a0b18010e030303070f1d030a12080105011b0f0311070f03030e040204 77
    0x10000518954110701c1800c211390103011401480c5000b81211520b070b1030041e4003a9500c0010300702052113820700308000198100f141c810843c1c6040c3c1300d00a03510396074035078407218183d070f0040a81d510148810440040412105c0001e103008109410155641d102a4104441034441c0d80389114852030141421400240c010421114041d6000c02d4181449604050803420342c042c99004090b18000c9084241030158540c0c464481c5445c402820011400040051800c84000c9200c1100c3c81004104000104404002510300003100910414509440340415101a0000c1c420050031485004074550b5941c1c1100c240d403c500800e400441c02d6150210004090821100290060142c0c0f403450070120b01e90322100728444000a01281c10303007201483c18a0b542c2020b40525000a8035820001c600c941c0f20f090803840d58802c01540544660b0551954846020340482c100c003808641c07000c40769101c5042c40b411000b00300c1020280582860f500b80070b0501c81c5000303000c80c46036104001c00d0146403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 461940503 1250 461939253 461939263
    0x218041704142206120b01080c03031b2103040203060609041205070303060f08030a02060f010b0703120906050a150b030609130201050714060115020a0b16090b0403050609010b060c 79
    0x104543c502100d00001000c104800c010a9800440303500f02040421169581301140190764400c5a10030070756aa0b517400180c85041e5000c0342c82c0d040c0c10405c0b2442207821050308490401d213064050301d018100d00e21300758040080064400e4043c031001f2040000754501800f509a2200c4140c0c0d6a000a1610f40d403007090440c205c1c1c0c420001d112000c1003900c240b601c070740e02101c040c1c019a1a5144029180e4680594a4010791300da0001441100000348482c0d90510f0114103d4111055807810b0035455902520041c000d0400b0545442c0d84c0e0103564007054460003024050030341c9040003d6525680c02c0541c0d0191565004292251030400c140402911500e101d66842000b803c1440e603040c1e020701c0100c55900c90308030090301014400f0040d4400102c08140710b8100c0d41000728000344030b52418801d9031946070450020b00500000d5000a00c000c10b141307803400c41280c3e1840d10082d000d494407000c0070144c21903001624598081410400200001d00c69040369441c2150030742d09041c82d807440e4503560 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 461941753 1250 461940503 461940539
    0x5070f05090f120109080412060e070305120304031e09090e0316080a1b1415160f09050a08060627040303230406050405060c130e0c04030218041704 65
    0x10740c80650025100f00004e503c14881c1ca03900c5080580c3d91580e543c5002039110081e0000d072402031400180c001c00c0e1100181c803034222035200020300300215948914090079040280190f040c010740300d0300c107032070300742202c0301c0b48845102d58a90305656410300305014221030400e49961200c2e0310400101059000e42d28819030600c0d030104501765a941c1c1c50f00121042c111501c00d40030300c2991031065104001e12241c5103180a40c120342102d050943c1d610060203955410b07103480c95041d01035168940d140c0d00c00c171a10f04520000d814681045591480814100c070000d50181409400180c24441c0a207013621051130400c03001c580703050502610311035500717074160b0192004050683ea1650b10841103401046400c4690040301c0e49849490141406005448111801c8906000751000102e28034428411f0b90700d104020724601d65002c0c1419140c3c0d14400024051a4180a06003c0000181d55015000f069a0004507842c0598100b40c0303032000303481d42910f241c0002c0c890300b800240503041e8540302820311 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 461943003 1250 461941753 461941759
    0x6050c010627020f0702060a080411030a12111608071e030302030a050a0e0a170114070504090b01110604030f022803030c03020705060115110102120411120d0305070f05090f 76
    0x500c40904c03083d20014400c07400002c2d0040800303e00030501d40d410981c1e031403241d070003290300b0101082000205a201c041d14030008095109030238076520000d100e0486245210035076011244da407038100e5000c0003904aa540580301c1075000443c103000c80c1d06903404041d40342070785150202071a41981d4000e03450f4000c9003503800c10000701241000001e0b110b504a109501e801038289500d154450700e20014100f09000898a9982003075513001e10302e00301100340da04c00c0300c2958179242410306004400002d0041e82158074100800c05031450749900d0280505170140f4400d071600c80070381e20f0764100030b03061041c180b82a2000d586291440359103044251071541041c2e6141c82c3c00100b02c82c00580c194006d004640d800340c000e11070381001264207003618500c03a07100c03040d80c1c84844001c4201b080d200d090b8031404503144483c0300b1081c04100040c074082c100d0101c00100030082010350900482c410701e05044043c1c3d65000130380f100300703001080d84c0090f072401c9002103e10300355152904541c08540035003628441580 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 461944253 1250 461943003 461943007
    0x11010b13020310180219180513060b0d020301030302151006080c04150c0c051905040f090f0605060907080412080411030d03020904061e0902030a090c06050c01062702 73
    0x2110f001c038142c49009412680311a62600e00351a510740000d40000502c0091808030600803507402d801703002c0700c0c804181c40c808024400c42c101002d010300c0c0c403100400c100610780c48010108401c1004005448483d40003040181c59601d141030003843d120b80a010100fa2801400502c039241c00c1d406501e0702580c82d01e040030340b090f4950303111301c1c445413003154099000c510000001c1c48480d076000719100402c5008039200443d05464000f00400d90b04102c5c45207806401040041020341440d405c8840300a001c010002900f1019444481c800c12103110115500c17927a51040040c203240507070310700341c003e11249060100c61501d41d81d0104080180d805a009001501000904018851241011850003e000e44844460b00340000e806500071100386c0d40f00e0790400b403001c80d10901481e01810701ba50186000300b070302854041010025403003d00040000c42d1030b908050045a071841c0c50308018406980c0d01039640e105401d125007150388030740043e0940c0620030f8003000015a03e0701480300c0d80c108510016 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 461945503 1250 461944253 461944261
    0x30a09031b03020f070e062b060213092a11070503030c010e0c0f013c0804061a01141308010609050403120207030206070c0f0b04110111010b130203 65
    0xe19848028151280502800718421041542c04034a40c01d0900021085a10b81c0340c07200750546102e8401c55005820030700c0c1200b560410071314003075012400200300111900c0c401c89515140103903882016600d00b0f10030651006c11600209202d03c10754100c1000ca4038000c010f49680314500a040c4034403030b00800c0381d02001c0c840315560504c034110040000800310780d03035079600100720b40c0078100c000c221008600580545041c64240304078030301c0c001d000c140c2d1003080880030341010f803260081c10046500c81c016410200c5401410108094030014200e440f070040e54a07103442c0c080151140000d100e001a04e0490300003101c1c0c0d8200070248180480300d000d40340c8415094012590032076069200440ca5030900e240003d059001d0b90001d4040c9010355641590070108a260b80c0680c8903107200100140e2200f0006140188900510140d00d0311818501c0504e00311038590410b00041680c00392108000192102103540c0c01029251804032110000e100000344c010000b64010342d4510080d03081a0000f00213 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 461946753 1250 461945503 461945507
    0x20a030801122118270c0c0c230d050a1101020f1c0f17060d0f02030d09060e041514010c240c030509030304030c03300b0405010506030a0903 62
    0x60801c2807802400e0341c103c02420b0303000400088030041c1d01120002c1e40c1001181e0403541046080d40794480340d103554600d072241440c03c001407603441c481c40200465104050000742510341080000c10038621200c050520442910f0b82000e031110300c2d58426000f0b04c3c01c540000d1004211a0940741d0041d656006540d8400c00503800c01c28071185130801d41c010345181940c140b13010301a100005070310355100081003031480419188100500b1100192040c2c079000a542071400400088809218900d03460081015502180c0780c600c518500501003682c000d030a002c007940c00002c0d03082c60700c001c5900b406240705020000e8101710690040031003245603048503101316409407030301d5a07045a0040520303290441c80c460700d1807143d80e0380d1704440345982005600001c2c0c44c801d00441e8011202d01d0007441c0b95441d25907058410091440d0110184218501200b1410f1400700c50000515003076401092040d03501c2d000c2804440381e20969511444c0b80c48014091512600292980006600c10010f112103c034101 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 461948003 1250 461946753 461946773
    0xf08070203160501062405040e041b03080a03050a0b180c220e070c0c050907030e030c07030203010605060304051504060615050a031b0806131b020319020a03080112 72
    0x164611100440c0c0b503041048415800702d0300b240c00221040c0b040002814020041700c0300020800d00080c41480184940300810403956001485400c0e2440b04600300803004603100010b6005460111020511506464150007102d80c050070760001000040300c1400011f0400960038850118039502100141c07950510708100c80c00e1400c0039070075050140301c8503c8280b2894007030040e40708140c40b070000305004500607828585840d6110040d040851304250a014514000429803810981c89000d255404c0b1420702c0100f900307242441c05041d119085005042c20740d03000c1d0740040e0180c0da040081001180010a02c0210760083c0703d0550b07101e864a0a101d80600407d800c0000d14500130700c807031800c282c0c2240060101240c60744080c0302c0c4603025114043c603078a0300054100442c0909000409a1910007a0000d1012242d0400111462000c0c211000812518000700c09139100107554803169003901d16042d1104041d10050100a040d950014100d21040c4280303114440d00c0c010302010007104040d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 461949253 1250 461948003 461948017
    0xa1a06030c031c090f1215051009020702180f06181501110f1204030b0a1b0806040f0905030c250b0906161b0801140f04021f0513060f0f08070203 64
    0x401702407080d840302d0103d4228050641c0880d041e620000160321050000d002c0c0070301c2600c0200c21000030300e2601d15280040d40c0615070480c0e12180c55102c02c51b6a00c4a00d9495024500001b0904600d241910900c1650516000c4a0346d45615041c10010307807440c1c4002a2503821003e180121040c0c5401501c207240180603480115140a88a00003520f4401c00b80070344200ca01495082d0000d03110741e4110811548000f000b501c0108800314019002c900945069400603c05000024910340c1d941d280300c102c0d2940c1c3c00c21502030704000703041f030000c0c04200201c04003c8c8410351090642d0307038028144403129015100d05801e403580402d204010765590415a40d41c80d69000100c06048000e24003005140c0058210103a42d520032a408110b194051240414000589402040310313165851003242c18540108101c0e48410460304940002c01d0800c020407103601d503521801c1d291005a100302c500c620319a0040c10820080014040c0d200c0c1e44481038000c1609107003441451030f100e1440407421407041e04 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 461950503 1250 461949253 461949269
    0x210021911010210020f0723030703080103050c090702061f09020424050a0e09061203120a05010e1308070501061a0d050f070504051504080a1a06030c031c09 69
    0xc101901400144001a112210240d00b5a4102a81260020100e0080e001c1c0507506800c24080c9000080e000440303000180b99108000881c40c014403152840c6a102c0f8070100c0004040c40e00400402604106941910b14100d48240d070a01d40104029a6840002c10740001b0b104005d507892a480c244e040c1050181c0b030b80342415550380d0344828440320301e510400078041c45207000000e5220054856001d8035074084403507a070169406140c40c02c000700007030007074001540300b008144200c040950400003810390040341d0951038030780c2c41c1c012440c60445905a00080f0046289000c0140c0d20750745640b440106a07000c83c1e49522920302e400c113030740100826040255102407140c00d016075408000f002c0d00c0244844902030140d83c1d901d001c40c401541060303030580f010a0040c803041c40a4a00040484009103111004c02c2c2060360b03402c2e2203490401d9030102a10340d00c061611318056035440d403402070b51104084e00100207407070f442c80c082581c5166113007a2507600500030350003100c450322491a100040ca820 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 461951753 1250 461950503 461950543
    0x5131a091312110d03091511091819020307020309120a0f080301150509090105150c19020a0e1e091e010212070f1e1413081207020d021002 61
    0x40d0400307040c3c0000d090441c0c0140c03250345100d41c2d55600c00d001c1c914109500c40c0068042103450181c1074080e215480782849145418441e130031490f256600c5801c04c3c052466504a020308105661603509503401002c5c01030035004004222640d90000115000b11106031145d2031440180c00240341404018540140f040100308400c60030701c2090001345060b40c1c00480721001f88496000c0c152080d101c1d440c4400e8000b103240c1c0041040d0301e840c90b82c811109058400c81850403100e80d40c1141004a19000d036240416821b0449080d4245090004040d0540e4205040e0509106018810a92065002801c4224800001410000184031004108001c00b0b02c41041c1741141d00114041d400400c0112551040c0030001240301e80708032403040580b041c1341c8a100c000038004032107005c04003000000c2c400740000400004250450040140601c0e071072258030000b007500740003082c0c7c01c000c08a25060032682092003a0809030b602e0f01d801c00714203581107504044200001106034202080d60303100709806010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 461953003 1250 461951753 461951783
    0xf1005030604440a05041e0801060b0906070b040206090d03020a02030d0e09180316080c0c01050a0e040906060801050702060a060f0e01060e040b0a080705131a0913 72
    0x100140c440090031461070183c002030484078101c00c0091031030809003800407a00f040c64800b0f50300744000348400442450418070301030b01c5a990341d0b9415a16183c880e59001081404c0041c50401c0c8130f03079400381000f04d01652a000c0c0940002d01a80078505000d41009500000700f4115991581183c4640001600c1e40506100c0c3c2d08000e034645001d81d105030701a003d5000e0142d006807207801170144120f4010417003580349d00d902c0c400f0801090304801180b0703d40300800941030012410421003c03030034030640340d4560f00c840e095541800c240300c2b000b00c0c4c1d0621105011000465070000421000c0210a0381c00240c2045c40d81440d001600803a840480d15501e018188000c1948c04500c0b01c1c07088081000a1045607641c10490304090701c0b80c030914849801b06401400b00798400c04e43c40092680050020400e00f00400000d0400122a4015891580700c0c850801903414940742d0700a405602e078004200c01610b250348215144402c0304601c3c8240300c503800046007543e92401088030b16802c141d4040200380 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 461954253 1250 461953003 461953013
    0x5040e0106061404060c2a030b0717190c091a0403200102030a030203071709030a09050109180c0c080415080901020c0703030e0d21090b040803030f1005030604 70
    0x1ca0059200042c0b0151461841100c1001241c0c101c52081c2d0780d803803042000342c4074002105109101c210b40202400c03124160740034859681c1002d180212000781603420814009403001c20343c2001c90342c0049c80304040010081450303289507030704164841d001c00c212111000c115290b0302c694000c00c0e200d900410069642c1c22013140500300717680c03292490340c083e0180e000381c3e6400044030f9000c00e030060303004100801c4180e129401440c1c01030b280d401e01240201d410b800b444000407044400540c42c0d8000318404002c00d03400008000207000038204110014108103182000e4100c0d0403040c00d07003a848a0808a04500c20b0940264442d0402012034035152103d012044054003041004c0008280300f02181480701c040c8200d4000c030006c440201109441c0d580c0c241d4015114038200c3d0f41c044a49c111368408035000c0d480489205000c00712214070141d25541c003a240042c250402c0d01205020b0000307000340d18000084039045240b00d91004896500c0d0034006039511481e0300860303054000d02091204000c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 461955503 1250 461954253 461954261
    0xe130c08060106030e06010e06040f060506162319030e091015030b3f060a180f14010204030f0b100603050907030204020904140108150609040809040e010605040e01 72
    0x500650b034140003501c0402d00c039640c6d0b5002030050030840070120001c5641c42c40c1036440b201010488401c081000780e91840003a8098201880410038804041ea440c02088205080441d4104841c002d40e007121124030300f41a0348000350607411400c13031403001d600c9080c1800760480c805030341c42c0104002407614141c903943d40907000b00c1c032030f0031031601050342d181c44e07818024021050081009440c80b625464243c0804e1103034582000d0f0709070203016025480072070460300040d4441c40380c069001481c540c10311844200c212104400d00c4c030201c0582c074032258001031511403c004001d8024201744000c46850501e5070081c41a984020440707800031559901b0404074044007403190224200c2c20000c40c0d40c50b4015411f0310811600030000c1e401c10b0741d00340b0052a0647c040c0039510405000043c12103080381b040c0d403964400381c0020310030ba072201c0b25005030030300a44100d540c02001030310b400440e414595101c500301e0003030203021442a0f45580300001c4071f100075031021000300001481841500c40860010f4020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 461956753 1250 461955503 461955509
    0x806070c030809062e0503030d0605130917030a060f0f08010b22021303022e050702010c0303050712090605090f070302030d08040804081b100f090e130c080601 70
    0x11454000004500f1a800309015201d5070300361140010701741c0c1c0b1503402030f80b0030101c3c0d141c1701a44800c0c12004c95940c034208090600c0349107901c000601d4905280c20002030001c0c10b2213104225040c940103030005040100c070400f03149801c038005500c075103511800f80040c02c2d85400103c0e182c05002030000702070401034054012100001e0003088001c000800b4041c03080004101e54200640f031104402d070388000e80d8001c114060701441407000170360700ca50008078490824172a13001d0400295090031910200545007594824843c200350f40303408120b03070002c0d00c00d07502000003034145907565001815242c090031407854101c0092508103c40038003803401800800301518100a288942c078a030040c4c1c100b00182c0c0d4020f0b07940044c024504c4080000045460003001001100c00c94070511002610080421020600164410319086da0501e40014845141c00402e50b180400205071b06150170980c004180030207882e100080c00c6940c2d610300548403440d240e04240204091121040000c5288004c40e815050b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 461958003 1250 461956753 461956757
    0x306040605040b030a080a020c091f060503130f060e0303040b150a0b070b0c040510090501021005160f1115060f0405010305031902150c03070905060a0e0f0402040806070c03 76
    0x32658454042c03104507000d40b15a2a0507a002c50012070204190b000503003140703066441160069040040410b06104040e103003a0314409111100d0742c4140c0107110031201038405440c05500314585003458018070801d10401411070001040801c05110360fa82040d440002c8803001c0340d540c2d080500d40310b2721603003040700c880c0341c08540b02512030010701d000400c403411030710303034541d01d40c180b1480f0380302c4840040000e80f141d08061004c200005460b180c04981e0400c0904a0f143d20038000d01e003c3c006410540704030302241001b49844c01f0424006002e80500c0d1104046151034032031350100e14070507a0524100c00c142000d41c070071010b00b03183e01c20007000081c0c8a0315040d075250812807401c0040c00242e490a01004081c3d0f0010b03c84c900300907100f19800d0412030701d684129050503c40488401d810041980c11140c00103001013041050351308001070100501091340c90380e00e044c0804400a00c0d82c1440b06005101782c8140c50044043d6031142c060f10060304012080c1c45681c11301c50400f0380440146030741100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 461959253 1250 461958003 461958011
    0x1a19121b08060f01020f0d1d030f0307060501090c0f08090106051201020702130c05070b070e04110405030c101d0a09060f030506070e0a0302220c030e150615030408070602070602030604 81
    0x1c00c3d03500c049100c4908000520060441c415505e4045c4c1e0003546403410300d4078040741c5d0700309540e140d682082a80c0d0f0707600e00d00300038540c3e507541d0b410840c0544a050704507602450421054041140d03000034484584c0b0a40e24160008da01c4655640d03025203041e90141d540082c0c00801001d0410040d801804080c0c421101a03c4040c00040c7e80c0082c2c500803900342020803000c3c000310300414034100846134401c03418900301d2600c5500b07800140c110b40042c4000f12040001280c01e00c40d9080402074a4040c1c1c40c00c0f108840b80ca1240c0500810042d85801c0c0303a01c0b00d00405035025034503291001250083d2000340b10078840e041c0c0301c6013404408451032009a03078510444020843d05401200005052400600000240344c11038003031048190134a8a0f07940103030780941c0d129180c800706120704010110342c0d035400f003a03450007801c0103490700c580a45000d1101099000788074641d51071108112030b006070040d000b07484c1c0d91a800c001206011780e1002500c040d00006c0c140c1c0070030043c0e500035842001c0c01c9901704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 461960503 1250 461959253 461959279
    0x6080304060906140f0703020a0b0a1a010c0b0106030f0209030a0605060109050603010e0a02090d020904060e06010602070806010e100e010f03031209030e04050a020c07030c1a19121b0806 82
    0x7107a07400d1000081915150405c5200340e043d09120080001d64004d004880a09200c0e075a40341c003800707040b80c0803000d05603581c0c056441c50215a42c50354066009181400f51100c1685030080b01c0300c01880b1750130030306640c2c0194440b60070340ca40503140d00143c01020759045442e1410907a0180c4000c9a00d030340095100c070004615454040305481c10380d44002c032031028075a0354400c614000c0d4001a40254820100c41d44040184e03540c2003558403d0f44207600c0800d0010b80b00d1413180c90542d040e0404415900607103801c0c4490303000003a210341101c440c0e800510190b20740c0c0c2c110b40d5140d81c41e03421803043c0c14812800031481c087c5816040c0d04a81c030035070329000c0103500035228904545041400400181503500c2044440c034064000e1034001c0703c05900145040a007189032031528450b46c0c0120f842d0b2020140401403030150b4030003030821891024002e40342110240c41e1001904609201006102c03054000d801008095804010784600318502c04903408005000502445070841c0d901f03100e03000c0070040c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 461961753 1250 461960503 461960507
    0x1512030a090e16020d050913060b210601170606070204060f060f020a020a0b0702040f0f0f0b060301050a0b030408070606060e1309240b03030703050c150403020c060d0f06080304060906 81
    0x4080c0900d90b0f0b502038040100e05640c01c0301d05511051107e5440780006000c3c0c181401d043c40b442e0b000b001d580da0030aa0303480042038041050080c3c03a4444003881420002c0107a1a60418001e00c1da90a841000246d284d807034030300252240c010b00f4000b0390401d00e01307640410103000942030201a41d0281e140e8850820000004a03070303076203500d50000d4028034590000c02c01c4584200180888900c01440400d05440d500d458400301c0d0400356400d0000354880c21a030480b40c40c40d03c1000001001550031303500d07641c10807012414002c00c601c10900e490f00000005018458400140c1e902c40740c3c003a8051180c550f50710401058000181c07000b07032040c500307803402d0b122840d080d205071200d06074043c10150440342095290801240701600314420140c8500d03581a05690500c01410011310039100d45460f24a840d030080d01d4451000c1c204a41040004144804240c0000340510b004904440440e520408083c42c0c3e030151201d20314070b0000a040c6031010a502501201400c103032042c0713035910122075681d0b002c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 461963003 1250 461961753 461961781
    0x80a1e090f12032f070308060609120d0306060903050d0804140307030e182502010f0207061a0a1a030c04030b0f040516051e06040e04080c0c01030b091512030a090e 72
    0x2203088904c500b0803001001a002d0112035500010080801e41001c0043c00411604020041c000c02d45410200d840881d554041c410f80025101c686409400345080d940c4456588043d1180c032400d00a28a0001d8100103444034076000ca6002c2a00780c0351181503e24020301004203a00d60310b80718000142035401204c00d00040c0a1040c20b0705401c2c1d4500c4024808410625620007025200710754892140c0410100540014281c0c584100000165400700707040c2d14031b140000101036881111240410000c504150132a041101100c6903115502e4659901b07082c4603201e1503000800d03902d0a4800c10100c9441107061f603118500840c1907622139950100707020110f032a28001c0540c4003020300100c140100300ca0701504007110f40644810f2909458010503252442c0487e8221880c40d000119540390040601c051018075800707013024416501c0010002d2901032004005c564810b08a20180d00150360b00c401c40818010f0500c103490b610894000c005080d80c45a0089480c001e00c28000f280240e800068 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 461964253 1250 461963003 461963081
    0x308090a1a180f12060609010803090604090b0a03020913211d030a0b13060b0114070f060f02030705070b10050306041203021c0c080a1e090f1203 64
    0xc42d240400d50ba00e410000010040d159030402c03000e50003100f02e900c5046504030f00201c40f10041010346808010090300d902d05811459a5400c24498025140c50303540030b680a540000308007013524841917000c9541840540d001940c0310010f83d050003000c0e9400301d60342e041c86029620742c038500c000002144c014a40e02e084c504000654064211034242c071540b404032080400182038032048201a03c6501c2d2184055800a54070500f004102c410010343d80b08000c04030f007085c00c081c1d068029001c0c1c4801c05000d900342c05030070322046c03000d0881008616803080715003d004100454403030415800041440d002071404071170a19203a03012038505803800c400310045a9000300241030680c1d0700c2d640e4029038860030b10311005050302402100c00e00c0100080c05075440301c41c0720000447e504010401450709402502c080c1f840e07803a060709100c01408410f038175401019046000714038240c2e0307442c166103100c038041c80207400d030000c0408180c80380d6455040704c42d01110361000c0c03041c5449070140b80440009158 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 461965503 1250 461964253 461964299
    0x80a03050a06081b030a050f0105061008010f060f05070c0e060f120304031209080d0509040f05060d0305090312040909050c01080f0406090303061e06090902040303021203040f0c0308090a 82
    0x402c41c1d141c05100810b40b245244e0301409a88000c40c0903601c0d00d2602c450002d554005035140c0e4200481c0d810505621107080307071103250801d006c0d4940302103100080014012402004616090020014000d00c00c84002c40d078005485500c1566440c1d41286032101a20072070722503190401e481c0f40500c2c244116451030f90300c05004d10f281c0381c5103959032009000021100700c1440007040d000680200c00b40001002010706840d281d03a43d1188804100840f00e644c1e050b010742610781010301c081c1d500c900f00303032415650f410708080f5610740d1000002071410300c102503040c240440004001c40d40400d1500607042d4288203400300d0300241c074410015148154200c80c1000c0004003240000d000c54016000259031501a08000420315155130000342201e0040c91400814490010104000c643c008240740040003004000c50400e415a64000e4861004a10070500c0e001c0100103e0280300d425146540b10b0356102d901007000030b503a0f14001b1040d40002e00202d2007607034984400a81c1d803000ca5031804032140c440c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 461966753 1250 461965503 461965513
    0x50f0109020f030c03100f0303030f0506040507021c0210020a020106080c01090303022a120109050601240503040602090a0305210301121b081209090c0403051e0109060603080a03050a0608 82
    0x41500144540c000a141501b0381d0014000043c0d04110550810060743c060354021410401699101e400c0d110301074a6503014500e803400300b1110f07950116121424600e0200d02d6462044100e60883c83d202801032070311011440040d10b034616640540c0043d0841310004166400540000010759a500e920300c4060050313000341000c42c01c624440c28207826104441c188024441c090540030034240c1c030b442484094180c0d510785003441840001c204c03090061002d030220005030050351480200c01c7c6100c110400600102001040800c00070342c0586207103031406010400055030b00c0c1001c0359152a8004030300b903403282d000406040702c800302c0b0071203060b6911010319402ea11540d40c0c030a080c000503180c1d0f0291a800071103002c291100f0500c0080b0004119290351601c8400082c100640c6c074201808104000c50104010030000300d001c162000541e1081880380b034410480b450352070146c4040c0710014001c0c0d18114000c01003110200150104607841c1d5010015552042080c1080f1074960107580010303400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 461968003 1250 461966753 461966761
    0x60e1c17030c040b0f0304140d0e150c0613020a06080f130516092007050a02100917060f061c060c0c081c2003041b03021201050f0109020f03 62
    0xe000550308141c401074958070785650b800071004503400c404d11038807a114000040c04144011f502002c1901c1e84404080d1015120140019142d580301a243e031703005d0516000f1040c031682c000c1054403003864038401a114145406803c1b412a4120300074205e01c101c2c3e004c1d20100346148580c0d001881185078401c0864140c81c0d1843e000d10500681c002129a03103d81c000107118198030400200c0185000d135000300c3e4010100c088840640566400c0d820b00040504c04000400c0c00010442902d40d0150f9507000d5800420004a54810325504903d44487c1c0404116804000000f00c640c03189403504000001511074601304006524280c0140c0c0891529451320b00c0821501d0f80425100350890405980300c03103440e6070350407007a00010010841c0100c080402c15510419005841c2140c9031010100089807800312050070038000034101902c6250155841042c1142d1500e04101030b50b0000c02c985c280384061070145000e030401b2140004c6240b61100000360800050080c0e6a084e403c5c581820300b1599 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 461969253 1250 461968003 461968043
    0x180d020705011407080a030e21030c090d0c06080415050f07032a0c020a09050c0d0b0a03060e0d110303061008060d0828050906040e0a0e010501060e1c 66
    0x104103459003a00740040140c40001520307517005240c0c0134007540f4003040000c80350440500b0a00359458030140c0c01c03003c081604025842c6012a9440398101003004d44a10600c408510314114440008265a80f0b4a0012030f4482d00901d040c0d200741d100f542480701c140c4001e4003000c2600c0e403d9034900e582c2d055030808a440a4040d0700070302c41d0464100c207001c86250190700300021141c01c52030040e02061503581107109509100302804042c051000d0180042d0400640c0c2c5002c51081a01460026a940c184980182e50b445030000003150032100c2442040710b42c90545884a5103044884041410b640c0200d00e14134010058034814407000700a084014001c01060f106900020181540710640189041c000703104100a082107044129800c0044032202c0010042c903070712001150288a001e0001602a68035030b42140c043e14902d040200c182d84541491301c02820740030300225410b5081400109066030b1280c1d00d407828481c02c07940c50010340c181882201405c4142c0f000900008080681c13152040 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 461970503 1250 461969253 461969267
    0x209060a0f17070e03060919080a0e040c050414010c0201020d0f030e0307140d020304120206090102010b0904050c01030f050f0402010806060423010f050c060615040801060e180d02070501 82
    0xd0905014a0901c0b0900c00b00304200c0c07044a100d030114850341c101c1011400d040082e141e014883c580101401e014402c00908c4440300c1850050001100082c03820100e81704800140e03160170058014030101c5840000a80190864060340c0003181c1200194007440d03100e40d2100070865010717009840c20540101003180c1540d1040c4241060548030591200951800c200a040d43c0b8090780b240042c0305c164100150500a04400500455100748028000302e000d00b000d0780841a411904569101c00440050f80906040d240300c1d580408910101320500501150800403107800340d030100a100485c1c4c1540e0202d42c010740384060703038801500001d00194000e4059a422220040c50142404d40c0c1d5500644010400c8100d10007050a1201300d6415580000c0d0b010840503840c24098105110354140035503640c801810507114084558031040c0c80380e02c442c105c0703000d0200c02c0000e20565850707441d050305e41c8030f0640361201d40d40708010701580c2640d800308031009031412580c050144245400300454402c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 461971753 1250 461970503 461970527
    0x105060d0602090d140a120807080a0f0e0a0309060e01050406051b0c091005040b0109081b0f0406080f100605060a0309021807020d020607390203121c0209060a 70
    0x111064820104c0890281c03d0700b000103100801c014000d240e0703540f0f01001c0025451a0442c280b20642050042c00d43c0c001c4503680e031060391100009040b40b40290300c40050000548042030718042c500016003410340c81011a42a2030f00c81e100c4120b013040d0440111054401e521400c400150140301c00410003003480c4100240c3c1881c1000c96041010403070016600c0c2e101610b0720b1160b0324103174408004a007028040c006408009003040741003140307481c018039110b4503040c1030601c0000c02c548100c8229600c1e01c811040f2200081e00410546488851540c1d4514040317041c1c1c021072154200b1505464440d005020640e10003912050610700c03508010340140c07000360301c12a807008621000020034011181aa449003940e5401000304805407440030f410580081e24640420042043c1c080219480039100c1008060300c000c40700541060040c0ca0000d10401440298907010740140c929580c00007801800c4911604c11b00c40a9405101d01104102d2080350715254004009119010060707000310b20007002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 461973003 1250 461971753 461971759
    0x806010315120f020607021c140c10050d140705070b0c0c150a0609020d06230a1715010e01050306160e01050f120a0c1106010e040206031b0a0f0f020105060d060209 72
    0x10102d0f035a001070301d064184609084100c40c09023598090010700d1a01070101c0c26440c001d0090300711380c900492000b01740890b102c1c042c4a03000550001c05203a50307011055440081c6920002c50510040041c402d0b4030000c8140d45001c0701502040c0889164011240100390350341c02003404011400302803100003001020200700540c3d172600040c00880e60f000a2240b074400a5000600c24180921603000701d00a040b82c01c0b0054800a10585584030030f142c200c1542c2142c100000110081c0c1c84a80c600f00d04c2c8070f0035007440c2c1518000090701a01d030f03409140c1030700c1089054981c82d0380c0d28803041c03500c1c0410040c03003800600054900390655006000401e164054010b8003481c001c0c4054503c100013205954070703a1000da0b500800c544150313004007118429400314029003000e5142c1072502101e02000b90019200d004004007050040305850071180d4000c07a144c07170141d1201c04850707010389542c03a604026004540c110a4540450b8070610070740d0f22034940240f55001c0260640c54200080d00708000b80780d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 461974253 1250 461973003 461973007
    0xf0b0f091e0907090e06070903080d0b03030712090501170403030b0d1208061011070b09011e090f0e04031b050c060d022101120f0602190806010315120f0206 69
    0x1101580384190a228002d07040c003c2c42064a00031424040341c00d0a1503890b8941c0059061000300c3d40c0c848840c2d0b040b039030002492600d9220100504009154088500b9411711000031180104110241c14484807030154944a001555800c019140541c0496071006038181003070015001038020350007a005444050013078000c02c112580c8160141ca80300f2444800b2541e204100400b0f46030600c540d0080000c1ca03d4050018941c00000b10364940f03590049020294020030188000d92095683c00c4880c1805502e81c2c2100c0181403001d040c2015500400d880c0d279400d00700124401111044070303400b56501d1b40d03642484104880c0c0c401c020241c4800c1c1150280907420300107006554040190201040d200c00041c0d5409001c810340d0300f41c0d080f9242442c008030072000100a144000000102c038107810582514004040385080b900030b1040e00b5601021804914813042c010b40c3c0125220300c40c4100b0b0300d003044400640015280096554460619600060300c2c00000007012454084d0240d4406002c0c14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 461975503 1250 461974253 461974291
    0x27061709121b1507051201050406080a0602030a110418060b090a050910030803100806060f01350a02120a05010f0513021c021e0406050909130f030e040f0b0f09 70
    0xc108000c04c0d1400030000b100400e09860780d0b08000b400c00d006040481d03041206031f00e0004440d482d000f42c6180a001158080005000072450741c2010b48104c4011080c1c50b552a03c2c0c0c1060000501c0c40d448840e542c03441c5c80e00128010294604031a0302030401458262001e24000c00c001c88680e004000220400754800f0000001c0d042c1c82c080c500801ca545140202a0300700401a450041c009007484d10031462140481c07810b03608124624400c00c0d81d403030b062104171031410703811192503e6007051170a0f00c40300740c041083d0483c9a0f400b815030070030115602003a64984500b00c030b080da1400c0c0911104a0b00c42041006140f070040324200c01c2030102c02016052401c420360300600090802c058000040d00043d4404282e0a0903c4400700508008002403c2508021008104c0e000300c0166074000d6140402203450b84114441100c20181d00820340000c4100034030340244120242481035004a040017107003489469240900d44200d00040c00302c9066a0b83e01080000d000d030068105044055010000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 461976753 1250 461975503 461975533
    0x7030e0d03030c0201241509120503030406180506071d040501140a08030a0206010e060406090c18050406060e0910030b0403080402090c0405010c0327061709121b 71
    0x10410030340030380c400260325034824501900b5503400084c143c440c58202c407051050b00c4a402c0e01281543e03506100540620040780c0d0503200701ca0250854064400401851030400800000462059116030424401c2c1d40c0460b94a460300b545840c4000e00c1504a1000500c95520800c0d25100062311952040845046540490229813080c1c01c40c480c01d8904008000c2141024032181005100e0080118600302c0000382c001d46030501800f503884248a5100402c5165489030450805000030070001c1000383c0340c002014085090005810103440819800080c0901d01403141e4170481d40e00f9262072801c0c15009003040001c250042140c080c0d0180d407100400803030491b110452255102e40c480b10014289401005400e800003842c0c0c0300040c1c030400017480540d81c840d074240c00e01c0384e0604085002d00c0f03030401e00c240c44000c030f0b2244030341c8085249000100154011003044110366038100926050301e40144541d10340b42002028520303100d00300302080b01c07600d007855021070400200c41601d103620542424 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 461978003 1250 461976753 461976769
    0x50a11030c1305090d020c0a090b0d060e0d091a0d0b04060816091a010e090403030e01111b0609070605031803030f0609090a0b070c0512030c0a080a06031707030e 71
    0x162a1141d643e500401104103801c10400000803e01c1c0002e1801e000400c0010303544080a020360740d1030a8a5000ea264070b0707154841d1110426601c010280304001c40310344040e50f901403250307070040002c0d00508001481000c20511015030702c14020b26a240480607903015000c0c3c51440c03140c41d00160307074190024115006010408280118011950006180080b401e050b203044000c1c3c803001c0c46c0f84044c036540320fa800140c3e0451004040c0c03804d0340c050b13403282025801055035001d011029403e010b02052492650401010a40c132a40c0c1e802203800341031120181d41e5101218181c0d0964000c42041c03017041c0c081c40145600c40920f100070104500044000c40c02d581081d1394070341d02c003070b281c03000d010403498092640c646c40313003262004080041c282c1e200d00f00800c1e00130784120140400c29107150180042480050401542c680a0b207a41c1e041c41450076100b580158034010004a000002c100000c03a01d000300021030b50045802000c200100314400001c2c2d20040085080c8070328079203072820903218112 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 461979253 1250 461978003 461978029
    0xc0309150406020601061419030e0708010518010603052104030609080d0b090915090304031b0306060f060509040b010903021c020f010207120f1a010e0412050304050a11030c 76
    0xc020751540e2408202920301281030b0018428400c03140741e0703044110552030a8030340e4641440050340107440640c006500138014604c1e0a5001d004901000c20f6070101500854050701c4480c0c24510401e8010000030b003264401d010040143d04800c64540040d8031000c055450f000983c400203280030ba0f6607440c1c004440100d0341c100c540f100302041202c65202c842c45045244d44041e101c07000b1034501280c2298a400c80803c1c5000e0385030001c004030b083c0c1901081510051a4440c490801480210b42c19074020754591004503889810810003140e002d110000410440700c01e0384503d420040c00c2c104020141c800640c40504000c1c09400000141c2d540c280f241e00070071280d401d004403902d43c5005004a41c80300501039415540900402c1007484040e81ca000d03120303078004503984804595498038090366462007a00c080415152000411201c400303a02542c0501e2060404a091b00404441654240411140507040b07070004000c1201040d00009803504810004060350314001d111000502c009580b41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 461980503 1250 461979253 461979289
    0x303040305060712020405101d060403060605101106011202181614040501050a080c0d1b0e0114030a1d06180601090504020a031e0510050f1003030807050c0309 70
    0x10300090640003683d080144c0e0f41c014040d490141020086030441000e0300c0d0400030410440380b805031990454a501844050007410b80313684035603909004016004a01500d407044201480700d50486004071840004035030144064580da03880d00017440c0d03207115a840143c0e00012209514252684221100391141c01c45440d421050400b401004158040300c545610305104100070603c010f0703030000c06031520b502852600d4021039450b122010424000c052000c4225810418810f0105030310301000412007250381e0760f00d80e03001c050100445034605203040f42080c40504001041428020740c000203480ea29019220500c1c1c07041d21049858124219661005449520001c02c1514014440e0500404a81c1028003a5082c1a00003c94202d090712004000c0104107040580d4811070100745102180c20070243c0c1d00d1651590790f442c01619045404800700400e4100241c5841034103044002a240c055580782803d1380c0b0070806035030350343c802100c02ca540d20085c001c2580700d5485585942582e4950 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 461981753 1250 461980503 461980513
    0x70b0703020109230d03060f12081e0703080c0301030c1403010902030f210c072105070f05090108030c1e0f10060807080d05070f030912060b0108090d0801030f110303040305 76
    0x20f020413a04200030141c1100406003045010000f06030320031080c1050300c00200b941500744180d89080c440500c2116844400310a9800f00f091302c01003550b010b8105640291140c001c01d507a00c0808002910090000620a5107080f40030f001101d15800700b5010b00e032000c3c00029225103180c0000c0d00e401c4402018400b030354042c1143c4a0030b03251402d40c1e00748500d001000d10342800440e5282c070351568982c1c0100d6102410400e00d1241d106030520840240a42207000e07610600d07200d005442c5840094014903014141c3c4500028100b000001103414075010b100180c00d481a01c00314152250070340002c055034a01c50034072500c8400c4400d125503650710f03004000000d451450686146e08204c01c0e5400360102d900711580c0a4031440c3c1203070480d50030396485002561241141d16040d0b0781441c46030814000c8190b0360f001c1c0400c001d651750011080c80401d80f2020140c2d0f480300d5181d1396a0310900800340014108000400000b05401365140c0c01c10712801d0380400e0f000074a0003080c2766070095441550720b6401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 461983003 1250 461981753 461981813
    0x3170a0f0c030b090414250501030c08040302030306091005040e0109061406010203041503110309010c0e032d0c060307020a03090b030f0f1008010e0705150903070b0703020109 77
    0x10301c6507900301d01c01810144803e190b802c0000301180b10040c409003040d54000c1e030581e035100e000c1c0542c01d0000c4005107600c5003480c1040c1e4107840c045080c0a85400f10780781404c00c800b041d0040030720500c41e170352681c0154a540e07589c00174000c0d03403030010b04507249403130312094003203155511402008040030000d400003941100e00d00303140d030507100d2610310444220304940030702825903130101c03c42e01512000c1d1440c40c1c1c1c0c1c07031940400302e00502c007120740c4902817603006c403c5c04010003040d0440c3c154401c0565a50b450a5802400c15172034410320200071448400000c0c505e460f000d0b40c01d00070101d01001d002962110a492004550030f07510840e128401030b080000038038101030f00030030340380050b2a0b080c900500390b280c5490414090f03400600126000d060440000700611204084280a40a0300000303008881011089a41d03070310641c010207100300c00940e083c2c643c0040c54004e9805a0000800404049103080d2800503103074002401034085548600d4568003040049913004e0031005000340d007a0100c08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 461984253 1250 461983003 461983031
    0xb070605150907051803010c0c05011b0f0e030705060a080429040201030506220f0b0d050307060905030d090503120a18140f0601090b01020c0307150c03170a 69
    0x3000440c199880c1c4521a400d911010b41d02980b2031030b0380c100266600059009250701514400701c1da5815030814110b4140a58045080c43d1031a1044e80203214190460340742c08418807203410040f00040d0680c0302c0d451102d1150500c052400000703000d894940d0f4441c1c0201d2170b01c0c1d00c803544010101c0d10a10500007046080c0c242c2507075940c641690170040303a10074500007480b110041d00c060b04040c1c807100404c03056902c0241030a030100790103503000058440c2913829001751a0300c01d5a201c06610f8845074010a040c140c0f10360283c1e03640140514686117103561508010590050300351200e100c00d00a0140300c0d00c01d4410a10344900410007035855080300340611500d9040102401a141d040050381c02180480c11202c1d4100341c0e22290078100001d0384030b100780c80c2034400350080e42c40c0d12600b000060140d5040d482440300c10002e9003038030300d110746079014195030f141e00340304e5029882560500c08010510545100352942e200f1314200003840c8041c09903002d1414241c5e10000c036145d071403003524410b00d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 461985503 1250 461984253 461984261
    0x8060c0415080103050c150405031c03180c121142031503192f030604060209010905061c1a0a2304140906010603020403080a1808010203010b0706 64
    0x1085441c02c11610341c10340e17848684488100404500880c400840d04a0f40180501960007038040641166040f00a0100450150b10b4081c5080d001c0b91400b0607035202c43c12841000c00701b41d600700300480919854481940d2410603130040540b00d120006881c800c0355034608100e04034031080401c0380c01700820208141c0004103400509400ca6070094542240e407007054a00b0b80c1c1c2d0040ca14071020048454140121f0308200c185e170010384451100c0c0c1418001c01209458005811840000e9050344011000c10080010400c0f08601c1d450b603c100c0000b0006001500140b05d41d0340c0c107141c0401043e0341d80300403504075000841c560b040701040071004160b000d00c51198102800c0c2c91071800360450b040c9000301d0041002405000507400807038040c41189885030300750201e103180c040c2c010081081984aa000354003000c0c0d03032103000c0d401000d000207481882402510156a08086038a02e0141080c505403541c44460f80c42d00490901da50000036404003e1004e14000c0c03140550059882845103070004c111 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 461986753 1250 461985503 461985539
    0x909030c150513080a0c081c0515181005180109050708060a060f0306120f0c0605070b060f0f28050303130e130602070c030b0f150f010908060c04 64
    0x2042c600b00800c1449640c480480c0941604814003503030395032981c081120300044082c006050828000361603517052114001140b07440c89061000c0100707840340c40149070500d6a691800d640281d5640d85810210102c2142d00d4000341494842000039581e403001c501002500011400e03001c29140041001c1d011a00400303074000050310b1b01d650f15140c50030000d91840c02c180500001c20036403110201010f2f009502c0440501030385001c071000c1c0d032610714100c0000d8243d0700041780c1c01001e14100140150284007034880c045e80c401c5171007407103036582028040c00e0a502c0001c1039008140021031101500e6203881d00c40220704c0940c0d80344c1c4031000016460821182c5502103402940104440d96106450303840500944000441c0c0451581781d03a182e40812b44014a0050019440010084c0800819100403800c60748142d07403107001984c1d0b0f40d020803a1110b0403241c0d14114114046081c4681ca419080c40d620100141400d86150781c4591185181c214101c0b03650141c04000039003803001c904000590444 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 461988003 1250 461986753 461986793
    0x1c050f160f090e0a0b0405010909051501030f1e0f0c03030806100804060e0c03070902030a050705070f02210706170603160b0f091309020405100506220909030c 70
    0x81c4203104030080c090300d800c0c070030484010840000702d41d40300d000e070f00159103240009109200300d584500c000c4d0000c0c020000200c2da2803080c0c01c0b4010305205072a1016041340d40044880b90314240503207400103030350404692542c0020000300c418001819600c003501306e5500504001c03552506504d0f0103462980040e043d02e205500e00b014052400e98803240c42a8402d82c00b19012495040001000380b42403030030f021055040c0500900421070048540c090b5108074401c08040c0156180e101c0c003503c0b40c0c0700e034240184c42c0c80e8041c20807002505184400788092801559400f4040222030012800c1060b5a00311600250303a040038482201c0e40d4001282c4c04c10400c801038000c090b6010005107041006218046203101c0121b60094001502020b4071101d00003e02100c4043d002045045d00038004020128403c80c5000d000c58101029590014142c810141c480c500c0c0007a41c100807659201e502003c2c11600302e4408012640c0d55440c060030b003107035100fa02d8414000d6041c0c0b509000c003002c165070450b1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 461989253 1250 461988003 461988017
    0x6060e030c010516030c050c030a15240303050c0c040f0207050c030c01050415115d19090815090d050304030512280902060306061c050f16 61
    0x140300311013600004060350b03140c1002c401e00190340c035005040600140300c0641c58003400c1d08503824401240c0b100d10720000f00c0e080401c500c400e40c05100207040380d003542c000f0310b10003029010700c0000d0213031004082c901042011a000000c003080002d0035118000400709203153c0102c0c01500308131040050407440b0008502a080709403d10300001c01c14000c80c46001c4041440e0b0007150031690188900e00d090045250650700c040914001040042030140b580c2d410040310041020310011510038568900c1b03560314400c40401a08940145800004400b003607181501040270404400000d02034401c0e040c030548800e4102c40c078001515082008040d003020030000b0395020170680c0c240109038480d00898900340b05480740c850382401c031100d0141c0d5020725503a0b140b41040c000d907143d2180c0741100c015803600c400000038102d0340c012002e844a51070001d40008040c40424000e01c1c005010b400480143c0c04400150b50484070300c10150340003952001d0091113030b281840311720b4405166020100f101400d00103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 461990503 1250 461989253 461989267
    0x100902060904020f0421030f0f02060c1b15012112050706020702060c010605030708030408060f09011e0209190303080610030216030e1009180c05040906060e030c0105 73
    0x34560320686031002d204942c0019000301409030300702603030040c00e5003003070030401c4644a41c11544248800c09094000ca00660426007001d84610500c086600d00f81d4003900c2c1ca6100c00c1c1d64501590800071500760540b04420701518070801c204200180210038228418680d450311810350200044451488900c4a201e1907103000300c1d50308484422009600d02c0d11507650b07440750600600a0040342002980068001180303500040d05400240a0700c000b1000e40f00c01d40c1c1c0c0c496620b5940d00c10b80c810f6000d1030f0003500001e40140051452141e10815150000c2100700700141d080c0d60f420001400240100e0b8081485c8406040103402000406d2400103140450390446c4c42c007504000c03004200364031420b00c111a01c09258403e80584005440280b40c1000001040c94042d00d000c0415104501400b2810a445869440f1381515403c030b07002c00060035041d84202c960030020700718880c03452090080800000038421981d11030ba00082590b039070307000e1400305107034101828031401d88800ca0412800340850 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 461991753 1250 461990503 461990509
    0x307030903030e030a170a080606130e061807120b1e041a030d050403060b0405040f120201090512030a0b0102210c160305010b090f071704061404050708100902 70
    0x80d068a41600304203903e5400c0e4800070b032070503080507801808410310003098130000c00803034003520b510442900c6510032941c6040900c170050269405200c145590104200f040b00404000c00b608600d004d04243d040c1d181c000c0002d40c070184141d40c41c0c5c1c002102d6403152044040148500c40505d00100c0e28200152207580010300c011304660307426071066076103071141000303500c000d01c9400080324040c01b954044a1176180241c01a0064802130301c1c2c1604003600001c2c90324240c86224411940004090042c12039038039101503041800c0c0f560802c0d0340d40d0b0351005011031010021010f2030411401c2c0a50759141c20307070309981520050780445066501030040d0324000c1614040801400c10121031168032601c0748109186032221031030b21403904241801c0e0100500c501904490f6040c402a522400359481d51410a0310030780040b0b8244001a094034006120b01d003035501c030150803134000c580229070108072a4050110010036141156281c0c0302d1601005404020303c26034201001250382008140300075008 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 461993003 1250 461991753 461991767
    0x5040e010b030c0d090c06030b090c07030c171612050304110112090c1206050907080a0b04030306082d030906030604090602041214061b0d0504060e0a06051602030703 73
    0x10102280700210016103040041c4060b200b510b262030300107000452080c205522082854000e4100290410000600c40d042c40e103412401450201209440c02842c0c0e20119003140c03c03040219502c6010400101c8881c0303210001c0d01c0c10340750340030844c8240500d52510f00e41c0c00484441c50402e0010900421001c501d01035a480039111003800c100090310302c0c48950314010f021042c0d00400e0405038600200c3c00e4840f000600d0201c4d4894801003000c1c1d111440e12996410151255000e580e10400300c0b1030006000d80d41840d0081d00c43c0c1000b190b142d4a544a032420840c030400b0203c100301c0c1703901e045041c118415071205104501e00b009581380c441c140700880e000d44801403c15004036144c42e03100c2c040000c2a8111802082010204100540c0030724180c0600c0c200d440c0f00844500c00d0704040344036420012440405284ac1c401c2681c904200c80c1029030103808000d1066541c280d444403407042640c03043c410b40500c0384c825000000c072440e019101184040e0102c00c2002154014000c0d07100003900052 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 461994253 1250 461993003 461993009
    0x150a0c1b02010c031103090a0f170a2109090501121a1519080102030708250509040902031005090c09010815010e10082e05060a0b07033c05040e01 64
    0x80e143e1400105d2601c03c030f15604c00c40da1041d0700070052504c0020070520842e0170b04207441e021400030348107100f415103455540310107200c05071a15203126818070b482d01910001e19081c00705800c2001c5915138039070060040780c0d0243d0040d40e070b9002d1701c204481003210b07800c00d8005030401c16000405508041700c403811056400c054050003450f81c3d42c8000c2e80003410780e0204c03000707041e040c00035503a901d031a0314003c00c249404d40300c490709940007100608108421000e00540f22825950300303410240c03108100005040c1c100400d0341c040c007841c0c406070084060b90258511a06c0014000c1107121150070510800501c168400081a0442c00500e02c00581484099044500512608140d0384070206040d051010a9005400034400c810030031814603000743c18110709541c030b40003203200b1503040240c0380103441c0112001540300d28045420b00044204034003030700009019240c18011090203114145114255100d008101403116025000c1d026900c6180300c05040c6900e00315042520703290181605401c180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 461995503 1250 461994253 461994257
    0x21801271d0c0a12050606060a0c05070b1305030307050a0807020310060e0709150c02060d1503060203010302030705030d140304060e1501140102011814150a0c1b02010c03 75
    0x80044224404141c00040005000125a40ca03000c00e001009a5803107080030054065400c1e000001800890b00000400c6103810401615031a541c120400540f82d200292007030030f00220079030550103d0000c000c1040500380300c400e001e94030100c0f100d032408024807039848a44a81e2041140e02c000035004108003044a600440c2a900c03009144006410320b40006040c9105500d80500050119a044005401880c5070703281c1001542d155184d442c04040e06074240b001051702c625454005043c142c0042120240304180003a4842d08805071030703802c50180c3d20a0342e8681d0084014025441d090044000a010450081c0700c5000307514805003d01300b42e24001500c075a408800103041c00129040410444440803d0301d4400f800d0700c88005004400307020300e003494030b80c0040f2140154014810000e0450891011040c07800c03070341d5034441c211003103010210b2960107052601000f0038603800501c1d000746a504030211300c9a82604004180d8000c00f01c142c2020007200f4004400350740c11031f0381610115018 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 461996753 1250 461995503 461995559
    0xf1b0b0703051b22051203041404020702090f07030f060e061201020313061a040203040609030e0f06090d0507091814010227010e09070302070309050d0c1809020d0609021801 76
    0x602c81c1c0e49001c07243d80d10030b61b00300d00070360740010070150040010400d070742c50f201880c0c034103040788020300007203020742c21000390020a40c0000c16108a00300d002c0f2680a60b20340380118001f43c0b005603034015600c280c3e100075074141d4100b0a00c001403821a15030403803040c015000b103040d0301d0310600c00100c00e1550740c2c0c0540296920348032a0400d85050900d03444405001d0310a6580f410149014030003008040c900b0b400040c07025021314043c0c030b01150b008000303180090010b0f0500074410b04010161b001288211440d00c00e43e040058016258011b80540880c81c00c448410440ba0f42429010403000c13404a100a920401041070040240081003140901520040134021000e10040e40c40c6107444051541c44501e003810080450b902d0780051158511a944019a0036600c00601c401220f5102c001030048101c4402032103004480005801c5016485201051040594000c664101c400711800c1c0c0d05a078480403408254140b211400745075580c0b2041c43c0810b9894164603458100241c0c00584034000d013 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 461998003 1250 461996753 461996797
    0x90b0a0504030501050411040e210d0b090f070f05040501020d03020a03140f09191707020a032f0d150509010b151905070506070f1b0b0703051b 63
    0x4a0300c281c0c1d026690140c020420b601305800c201060355001008503105034102040e11200d0302001c11101c0b800d0300c180a600029900350444d140f8036410103104c0041280c1d4903005100d551381d5003281c25000e900051808512401e042038014081401d0b00072220900c402044100705c00d0b40e00045242c403e882ca443c0c0141c0ba4031030182d0403009003401007001c2d1041688001448505145105200c0c0a00013000032100500318086100c442a03100e00c90141507584d00b4003642d07041d2025080107001a510007020f03500c22a071030380c2d80e140a01500041050174a2003000c50040301303030f50020b800d50040c4030444203034a420001b0382d0b43d4001c1120102c1d51002c06916400410010345094110004001009040e607010300c0c00034406554940042103502407a1501000499200e809041181e00b200d4220001d170003c0c0d03940d00d6040c1c40302c90080d08840c0400100d0030400010b041c04d28145100984600003a0f205400d005030b0003401da910142812142d0041c00860040c1405031000300e40c69401400020000000e07 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 461999253 1250 461998003 461998007
    0x519030f030813080307110115120b041a0901090302060a2a030b130b090c04031e080d0207030c06060503070f090e01020c0d08041b03020607030507060e010f0e1c090b0a 74
    0x842c40c0f000420403000481400045a04004100c0560115000820981000c00c2c004103a054452250224034060420b58601048207c0e814a5019020b90078850000501526030225000101e038500c680d40d640eaa0280f0405a06205440c0c0100412000340102e54070044d03641032100c02c0031a007e22a40c2040e030a000220701940040801d1680100000c2c0c0e041528032044d0084e00c215210b90b8841c5a00c10001050b002001081d1400da03034005040e900300d581405144034501c49a18010340c0c1c003900500c01284c0c0d00701140000d00903540301e0781d075004d101c100c0c030300d001c1d0181d500c0c40d001107200b07400100e82800040024524481124102c820120740176000f120301500920408a0203030316400307510121900e41e40c0060788180117910405040342d000c0d400e440d117060020303890b0100960096040080d480828400c01c0034001e000d0081200051003c00c150b210380c00c4440c3e0301c48504d465510b42044a28461040c04100e684e140002000e44c100140702800070694021802140e54035000031800c154824 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 462000503 1250 461999253 461999281
    0x15130b010b18150a1106090a120507060614040c020a0506060d110a080a0311010203010311060c1e0c1305040203060106181815060203180108070521010519030f0308 72
    0x35005020b07414803901c40019076a241e8861100c4402140c3c0c0c0a94179007903990000f400c0f92144000c40041c016986c006da40700402c00743c0401444041180500400000c01c4c45446548001c0c1001101117440f4060301c01400207982420b104602503411202c158000f0401c0842c1440d032115040750421103c0c59a460440480c02e01e00c0e40c4950844c58a84011848410018588511a0003a214183c040072562501404c0c1c0c80240801442c00c0d0140c3c0034800c4c1418000098040d40c001c000550f4015214644004c06111060607010070a5010000c0e0211508012001c01800030300207100744500e2402e0b4001ca95078000610900c002c0000040c103000750f44c00e855846002412291841d141441d980f806030308041c048903042c00b12008071107440000c80d503000100f140c56540403205170701d12102c41c0c00d00555410070010085818410100528024581120380c11a18417041c244e80007110b50600062111800d4800c203041300d4120101001e00100e80d2107040302d01d5181c2e06250050069480c4010b2074548 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 462001753 1250 462000503 462000547
    0x150a0306020c100605090405030901140d051e070c0201080117010912020304050307050f0102060406150f0b03090d030618110d09030324061407050f0307030215130b010b 74
    0x860301c08142d00105440225107250000e50381c0805002003500c817002c01c0b442d10801e99000f0529402000281c40b5540a0000740c070402e105a44100d0603e1000f5921200b541c0301181c02107048012003820303509a40480402c9030300442e030303460040b0407441c070f982c000f810003081806909041c400d1100b140301d81500035040001d6590340100e03d41142c10b5005400f0750349411a000355846801a144d0210309414020741c034403000141607008040c680c43d2500d0741c40007800501001100d0002102020031192406c40f5010000c0008041703495076440d25416840c1081603502000c8101802c2003410009405880704078a03104540e00000101d102e00c03110030380350600c6649012180030f811300c4c5450050540507840481d803030b1242d0742051104d10142e5800300900d010b902611000c610144518401e4494542c042c1034502e120340c04031050b8100c03201e4510301c0e5410a40b022001640310030030041075500340d0b032455030300f18410758031407000d42000350303103000d0404d0301406142c0c654040401c8a1002015031441c41a032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 462003003 1250 462001753 462001763
    0xe1b04060902120103110301110306090618011502070f06091a210603011a010f0f020f15160306060f030504081c0c0e010513050d1a0c07110315150a03 66
    0x10f64074260000816100c0244004e0703600183c8451511880e0406003d0414019100040285542d44d0036041010750440509281d401000f510200c8040d00c03058079040c0d02030505c0c00c1c0c030308440400a1400924005013a04845242c00107450204070064201c07a42500791101d004c00b2003188809040c1203403540c080c2c1c140321240400c9917518000d42408070100750f0300a02c0e064009000c00c0540341d030803801034195245107074005100b6413003c0103210701c101003d1a944e80035205179240c0e6030105d01950315200708100400b0003512600c3c1485100c501042c804440d170700043c24181b002e1407900102500c82070b1000864010302d038aa100040400141d40225100f0f080114482d044450102c01031100030706c080d911803000b040c2d1034251141c1c150301403030503a181d503090b699543d81030381e0900c800d000c0c0010245108440784407107880c0300c054540820160b2407080705200788480e00c442007030030425a0100d119020034001d070001d200d919184107202540560110410200c080300c1584440800da070890140c0c00500 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 462004253 1250 462003003 462003007
    0x1410020301090f050a020a090e060f0306090319080f0c090a031203050601120e1221070f020c060a1b020310020c0726100e0a021002031c0e1b04060902 66
    0x14060b03000d92052410302c1d04072404100c65a0b4091444080b40719042c84800440c083d000c08120465107042000e52128024000101d8407814001007483e100c01030311081e0681e00042000d40c20002c24020f00c034040c100d10300c0c00c00010308010030301c040022800b4240d071507540c0001039108200e894940290008540c0145a43c080d01640394000340182401d440140c001072525031307806040942c40c003071001181c40c144050118079500540e554119400f80007050402e1200a070b8107904000100d5070148034010585900c0c014401c1810024200789004900c00d225550078400c84040d698048022440e01107035140031100c1da4181c0c000a4a8000c1c0303d61100d050a0002a1174501c080010a40c501180d10300b4001030707044200b00b00116035403407140031001c0d03035603220b448a214001c400d600710384001c0d01000d00f9984d0301400782e000f10f11042500d04140380540d100181406020815031009404550000400c01070600b031005829201d0b54001c10b501c0d5226403030820303810181e0780d6a11080c020b0031103601c215 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 462005503 1250 462004253 462004259
    0x130804030f0308090d1209052d0601080a0309090c0c050706090812041d100b07080301080f07150e010203040810060f0e070203270325090603020603041410020301 71
    0x1c040280d1541c040780003894500101e00c210f1300018500c9482d0002d9240c1c3c0392480903840316517005055040e0243c66901c81d1140070104010b194035040000045c81d08000211108103a60300d26044060780300c80309642c080c2c3c1881f808242d1042e815002d1f150350500208481650f400d04031000e0503281b0300a07105002e141130008103180c008048004460600e01582e16030711503085600c0950049200308001c0d505040980b0301220045505503030b101c0201041079210b20f4582071070006540101c0c2c41141e103248000014000c0c99400c0103003802030280341c0b0040903070f00d0600000c10310300910b50801d4402e0103104c6000003138030780c02403060710041c08050b800c581a1101004002014104610030320402042014010a0300da042c1d080f050722900c079580045290041c0c0071121049100c03418920540040106c0c041034031642c081c4a14050b690013008000440b04408010845000ca607a00c040c0d51285001c10800041c1c45880a0700e034015013190b0101040d811303c9802d14101a280003e0b021000e20020000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 462006753 1250 462005503 462005513
    0xf052b02090702011505030703080a08100801090b01050a0b03090d0f030e01020c011d1501140a0b0705060106030605060c12161e1502042106060503030d050402030c0616030813080403 80
    0x400309010305c03220030045131644c1d00705154580d030181c000500105c1080082c042c0503401140c1440d08280c06144194105503030b8050709085030f150070b0781100e4600b01c2c80010001480d01c0c078913203400351410041441c80c41c10002c0001355101c9004c010341c418040500800701c8114040d600c0600c00703405540003591703100030203518030380240805131900781c0740d500b094002c9086410002c3d8910442d1408101e072800d69080100c00c440ba040c8002209902404440010980b140349901030081e140c41440180140e505119001d41942c5450708942e00a0405000f91000600005100000d2006540f54569030b9100f010314401103800691016180c0d401094943c10205101e1169100b001e0080ca961141082c1d1a014401a40b155100b0751000c42c003d07203400100502c2c08840411442c1c809c80000810759940e01c042800d503001680580155542d030300030402035041c00d111480c0e00b818200c0d04107240140c0040040b04e0f0380d4002c8006001c003e0050000750300d0018454140007255000040203840d26071f24a40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 462008003 1250 462006753 462006761
    0x8070204050c0f0a080919081c020c0c0904020414070f0f050307080f0a0e01060f06030b0604030c120501090203070b0315150906130b160c0f052b0209070201 69
    0x49004915010014041004a805540710f460441c0c0e0940d1802080c1c400403145070030013412000d0180603280c0c0360210346c040840346034140b9100705501515511055010440301c46020400e0b000f03035004000d50311186201040c21a00014211142002611180003150040041d29050f8407008818401d011100b60841111541d00b021595035080140c0c60400c00c072041d0205480900c04240090302180007154400700c41540584110b1001a1140030707641c0b000d003990380035403000300700b8095405d0074840150f00d070148460b11181a0f079994035281c910b564000e145600c52044a0340340c0441d00880041000a4200015194001f0115010141c903a00c00d024640e1040d00d540000b401004102e80180c1814030f055011840c002001c14100a904401d00a06034801514001070000090010034015414405003501e43c190184500e00c041592820000d9044190004041060514410041942c413200803e034284558442e0a6500f2480c2c00d0480c054441100e000703610502c0700082003e42541540 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 462009253 1250 462008003 462008017
    0x7350a080306191412030d0c081e0c160201050c0d020105070816080403030e070503060c0915031519090c0c0203011503032a0c030c0807090b1e0109090908 68
    0xd605030703802c002549030100107551031040183c1d10f072005424081074035254002e406011401c80c266440c0c800d07e03030078980449076081c40b050302142c4c00c0c00a01c803003240291880c40c44410f40039440d540d18142403460030801e0041307080c034100d140340c0301b0807100459116400742d405a07940c0d00700301d4012940c10380707010f4040d060848030080014681c0303000415074083d40d610940341d0a007a0315098a603032210703141100644030800502c09148581e1000040c251800c00030f003442400e604034117603290580d0340104164600c80b40c5400500e80c0083c02807100f00301e81800303d9001031400300e03800d0031401204c0c80007440b00169136001065041c40d21403020700d1560441e80ca1034089100310b00801242c070345548000c0c030000302800060000b410300c83e05a4001034400c08036902902002080c0400e0311046c1d500c00c04d20f80c0607500110b0304901e601e002000051000c01c2040082c0000420522004158001099500b00f40b4140c0d01c0440245c0304181140f6400740361030801409680d103051021804c142000d16455000f20 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 462010503 1250 462009253 462009259
    0x215040509060a0315111b07030b090a0c12032d0e011b1b0b16060c08070816090b0c0a030905040b090f090106090216030e010207350a080306 62
    0x120001e501443c0000c4401c0c00c1d603a00140c03000b0b142c17101203440c0d4000d0090441c55441000204001c50610b000749080300000300c0740b01e009225050451400703408400c0068040049a440341c0e400000198517000d076030302542d0194100d107030100c81a08040b92040e01e6450440f0012440c4003c4000031402050401888191a15894011a602c0004665402419895031403984410446000051112194100c0c0c240c80344440e070505915032602040e244d200100002e0300140e20b00d0150200406405110b4040c0f801c0e0601c0345240ca030152002c1c001c40c000818101c8111200340d1440020703806001403101500d0101403c07501c031201a50a295070316581d4605038045051004001020318050103282440b40c00038001c0203503600d490010010000c1c0143c21258555201c0c013000c541040d4500c080c0401c80900c584411054a1074207001d014142054012411504401c2d0b00b40801e00440707026114100389004140b160750301000040d05207001c0d0055400590052541306002d000106002d1402841d00b2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 462011753 1250 462010503 462010519
    0x21903050402190317070c05090109020403150203010503031902031332033d021209010b0f09070c020901090911011e080a0b120601170d05070b04020105040302150405 73
    0x52920300c000704006100045c42540058202c00c00802e421001d044068401c2095800840c3c0300d40c0001d003107140980080040642c0860201701740501c0503490280500e506104600d154144004070340ca078820b180d020f03021500520104044d16208204071084d80ca8545804006035465150182c405100d03a00110380c0042c02041c40c450410002c1e2201741c0c0108000c0c020100d401100c19240b9603c185840d5602410b080c1120881804140360191088011352003c0160380c1c51080c4a1101502c0307002d880340c0d5450b0302d040400d19183e222503a00e4070b0703011001c0795100700c50794442d02d0465104030550700094000d40401c00000742003c16070005a20980b084c00101c050f55201c00044a51030030b058184108000e080b8440040c150084c0e6125402804d081c6002c205c2c40d09c3d10011a02d441c043d402c045e015a4840c0b00100700ca4250940c41c90880614907020703140c900200c1c88010001c0c0545076014020320315032008a803c6a000c0c82c11203000310b40c09000c80301c48184a06182c8004e4209100790ae01072410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 462013003 1250 462011753 462011779
    0x1172d041a1518040c0b0d0b1809100b0301110705061e0f0403180b070f0b091b1203041205060a05090a12081003150b13061a030703021903050402 64
    0xd0816400302c0714001400301c4140c41550000d007407070082c0c040c0c000e80c0c840c10091004181814460003c1a0030740c8076942c04030b00c0303d503280242304146c41c08150710600b007012641403100300c18002c01c0840d034421605101080e032004020020b801082c0c1052403100c00d41000034050108000460598403405402400d14510b8100040d10b40800b001100d6030502400d81b40000f0f40000e004000800c400110020368001d40380d140c11403088160f107d05010303203034281c072241a842081580c92046901c0054580540b40100c005103e04c0407900343c01d03203100d100300c04540c80c80d0f032401070400a9800078941d003140480c40c090b2a0900540702c0001741c0c0e1008440d41030200154881000040420b85194000b00340c02d900010780d141210a41c3c005051607200484035032000001c0ba080a21410341e0380ea21034400202d903034110003001002c1d001e61510540941c00c21500300807205040a5038540c681d44140915900c1c0d841c403401f1002442420f150000c00c20b005a240c0e034026900d580414425803013900c0465100c55 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 462014253 1250 462013003 462013021
    0x7081e03070209071d0306010e010306050709060206070f02030f0310082b0c05010b130f06060e0f040c171f0b0c0618070302030f06060a0501172d041a 66
    0x8100740000e504482010082841e0301c0c880e04000d00e0a01100b0300700001e03029120000307410f0a0087e4403460200d0550b0005000384035151180a4008045052050650f844c00c0406521341000911030360030300072032882112105009000700c4030390076014000143d40345031070343c0300c03000001c5280204481440703081700b40140700f804031024201c6c03400d00300300c0b14040c3c004250088510408900080ba415521081700c4045525241001e4014030740841c00850000368030300c500b10031102294061820071a00580b200150740b5602c40041b0340003410342d400300702e201c0c070700d2010780780c592000305140620f01a213000c00182c105a1040000400040c801c400343c180d80d20240d242081c01810403001c0150440d0300441c0081811500140813510034406590325550360360002410401201c00e0100560442000c008052400c51410300c0585000d00300444000100040c030941641d0080ca10640c620105400c44030501e12a8425000000d4030502c0c402a46000e01e081101c0031070241800380c0c41c0140e0f401041d5804 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 462015503 1250 462014253 462014257
    0x606060c0305030103240203071d030703080d050405150106090e010b09062a1b03150403051801030605040204080d030c031a1e03030c0616020601030c0b0a02010e07081e03 75
    0x7501a6606401c503402c0d911044a00c080024250080c0e41c00a07160f0400408a40061449621740b600d900c01c20101c5034030000352024101d403070980310360040c034028000103000100352540c01460a2001610350f40310310b496031610030125050703a912400c0740c00010310680c0c441c2c0e01e40d0548140c2804a803d036642d80031034200300d018007900301d9409001802145880103400c4a4101e04941c1d4280c12400c0c410200e01d003504000b102c03c5501d082040d8903002d09230a040410904000a28003400c0d95282d01e4691030041c800e0103100c2600591940d180c1021040da03100c0d420400141c10000e00441d612565144250b03918081c1c40740c03c1003c00d05007005040d101d8002c0c41255900c0b07001c02062990800b528080204000708503007401004030482086c11031035101000074091080c101001000d050401e8040c280c403c10b60008080210741c8510018400031752444280800c948031002d141d91140341c00d0b10281d015100001c1e03c6881ea1042020001e040d200c0001e0000c444c844410b80c1d00150440800c5458580c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 462016753 1250 462015503 462015527
    0x6011d0606041202180112020a050f1005070c0510030603050d0801180b0103020f03040b04140307020a090902060d0c050306010905030114010e04020d0f12080f130201120f0513060606 80
    0x1003107082c0b000b00180e00c0703804903034901544002c080e013405131421000307214512000e805c40c1c909884940700650071400d00c10880b2020705012141914542c200c0000138004515603200c21040010115040080202a0321090b024040040070903000004201340100104524401594a03200ea140c03114500782c016086c49060703070007140c0c504440540600d408005415050720040c1095070800156518880d41130107140510b12902c2e4032043d50400d0304040140d0700080c0d07a6280395402c200051302c0182d030b032070010344116040746201140c5058140002001400780b02001c400640c00e04242092090b8044000d600c150b1090f00d4441c0e90b42c1d1170f4001d15080718030802078407241c00a55030040c024210000c0030700e070f44a48000c08903408884603550702a80e01023500411624521800b005400884d0444170541d40040e0f160010740340340c1f030001e008190b2070601080c00b9040c484000380d001143d5940760081d003491081200140310a0502408070355084583d45030a0350381c80e14000c4045186403140e2040222 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 462018003 1250 462016753 462016759
    0xd02030307030c1e030e10020414040b06042103030b03010e150c0703080103170f190f0302090310051914010e07110706080c04120807020f0405060a060c1b0806011d06 73
    0x104c0451003105600070400c2105001c200e115524442210b400076000070006826240300c211510740c800c2c001d00094500d080c511601c2100c05110034015640c000c171766a103040408507255040b040440c20160010030400402c60741650900c0c1541c403003650000f032400e52000c1000601002030342da82d10621202c1c090074100030001400c400041000c940002228480b07030b0018400e50780380c00710a44d8148500d80c00180c040300317048041641041034541200004c50b11500500f002d528010542d40000d0f160b0b060100d11507522030781c4601046803c200c052000c03946040c00b0008202011041d0b8207211400c40911030201040c815000080500c0c2c49403180303112100d00c0a005156040c00c4c107000f601d0300440104031603060041800000340100200400000407130190394155500d90301801400311103481082c4841c007c600f803200f80151622a041924102c1c0d10a00e41040286070628142d030000e00d9600881c0c4424600794004150760300702040d454121540242841c0010001d00710780c1042c448100d90060f4 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 462019253 1250 462018003 462018047
    0x1709070501050a03021e0a09081231031407080601090b03060402010815130f0f060807140604030203070602151312080601020a06060e060f01090e061c050d02030307030c 74
    0x46540c020707000f40501c95030709801200780c0140761b104111203800199038040003501d0202c0c00c120b600d20a0281c08a107043c0c01d100240742c08030102c0000780100c91902480e0804070b144031218040641031070382030081d59000e98412030107100c0315a29952000d040c015035010740258000069003885610561118076009000340c50320b07075900c1c0c00645810741c00130282425902128550501d60f52008080b811b8082880c0000800782006a0100d088070000c00c2c0f12455149010350071302c0b54440c0003590400700d55840342001c031455044008160207005552009426115082c03000c20090740202d010700209400a000e00880d9640007403580c0c90307075a0003030094105415040074000051041c158194800c0043c0100c0d1500142c55458030111001030380b1141c040c50303403481448114030302024101010782c1d003440c01c65a85030804903034198020000d0681d61180022075a9102403c40d400c000b403c1158014055031000e0b60003503400b0b9101c0d0310440768400020700c0c0a200d04160f501034209041d0040000c15000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 462020503 1250 462019253 462019267
    0xd0f17102c0f04030504031b09110c0a060f0e16050f1504180216030e1017061e030601120b0f070e010c060213080c030607020d020a0f031b03170907050105 68
    0x50140b0002600a8082100400010000c240031001c003510b080e0a00d4400d04026251698840440354038040d110b404580401c4841d50040c00083c25001c82074100350005511480150990014442080003188500800429020b003000c0240715104455043d10b02128824903801003001e840300d82121038003200001d210501c0707080e52080d19000524800400180341000088156407155640070f01200050016580000c00d070030140050f2100100034148440c02103850300d681102e242000744070b0b9002e00c400c646030b10188a50300d5109298608007505958080d6101c03040c1956501d182203042c3c500880b02d03070100b03d0907040011403d10880c201d580306900c14880718011505121440360566620340c00b4405045241000f964034070003040301c50700074443c0401a40a041c20b128000303140c202035420101c0080107054001ca410000340754044107030080c0c0c0a440c50709548600140305942c00c19050f541c0c60b44c0030190000807403000301c0c0340c80300f04803007658070029071a03501c038003500455000480a10040c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 462021753 1250 462020503 462020521
    0x1203050c0709020c100b0414130507050603070203090111120f0a03061a03160315080d030b040509190302070803030c04241215080105090105060901080606030d0f17102c 74
    0x94806d01300804c00f0030901c000c03007200400d00704180ca40c02c0025501042003001c004040000b800106001e442d80c0e41945080140a900c078051903014a040c4501c0d04041c500e180810310a415200001480c41c50b210810b1400e412007980140c071601300440d00c1e1000125484c0144102d0032500305020243c1d07491652040e030400404a000c985000c01d254a829900c001c04000c001c000c406008400001c100d01d0150302002420744a882c000d250007946841c0074007040400101c1c40e40c45030b010f8000c80f14030390100c1d464200d29285069201404902011082c403213080c03626002401191103000c0c05404082e0b080100000480800e021103000c102c52081840294000fa08402980b900304c115041d5202c1d0349488003070a4660071554079580740d548001304400d500c0d20500c03035809090894000c0030b481ca03008000c640e0315094400e0071411700070683c88206501d8460000f07070b6415003100c580d800700d506000351710515204140c01a03080307600311000c044c08500440509c104041c0301590f180499a00d44510f8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 462023003 1250 462021753 462021761
    0x60f051c020c0f0f0606041505060702010c021504030b0f06060c1b060409020403050a2a060813060c0801080105180303010915050d1b0f03050a1202071203050c0709020c10 75
    0x48000c2a0040180c00200c4003003d0004140384c160711800781400d07103024000c00040703c0041d441d14480515080d0103200a4841d80c0580b51025070a0904655410050000a0054404103200c01c07607400c0c002004000c01c01d04003001402100000490700d1240c4a4008005030b41c01035181c035481940c0702056130003208100201000303803144054415850141c5a46900341aa485900241c032903500c40546642000b04405940d00d403034084085001c4c0d01c1c0b07070310410074190184610841c420001408081150017040e10718041040e54041c80c01c02404810076000382211009108180195180000052064894500b024015034411006e10314503230805189000400d2142d040100458490a02043c035440700e0510065a40c000c2e000140200e036005444071684156070828440c0583d1b04900b0800164005400c1d00440d500841d0a1300020394a00101d1900100f071340207880c1c0f202803548180030b08d5004070050880f0303880081034840140d00c40844000364400c41c04410095400f41e41c88282182035944 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 462024253 1250 462023003 462023017
    0x40503030708280605030c010e011409040b09040b04060b011b140a0525051009060309050c0901122a0e090328080f070503220503070507060f051c02 65
    0x8482403551070820b0600d42c140f103401018960b5290703101c4041c065842c0c10481c1849182c0d091822403411200303200000c0450488012060030a0030209200f28030343c0d641c2c0c01480c0804c1015000503814501800d0842c0c0015046d10240d49040c07900c0300041082d48958660070b0100403102450440601a5460302000610015010500d0040e003007400005402032002c5250002e50400f25011044220241d083c491a01d5104d980324200800070b04030f0a582100852040740d00710708000940d152181402d60808007081d0455074440c001d0782c000306045052090003104075000b20410005645040941c0711710071303001c241c4041c110300d40100030032001ca459000d999100c2181c109032410003802100c11542c5a0b44410b1030b40100a400800107041d65001160341c0d80403030b00c800c030710b003003402c01d040003601c1e5200c0540003003000c006c50080c5a4001090000000b027686c1e000c0112540c94180f42003158940150307000d640000703441c80e84141280c2d8814003d07146100907100007000c1c41988501020005d5200407 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 462025503 1250 462024253 462024271
    0x20d050a140c0d0f1406030d09140907030b130203010f05060913180506041a090118030302090d05030706200406020c040b0f090a0e060606130509040f080310030c060503040503030708 80
    0x901035040340c1124020865803091700c40c07845c4603604204081508101c106080e11003000782091080241306601500208a044240c81922941d00c44500880141002221180e040b040b010400032184031160b008504880780c0c0e80e44030400e0346d1200108203007881202a02a88803d0050840030034400c140e03c04e10480500c00c0402001c1503140e84c3c0e181c00c3c000d0454056421490001805503000902c840e2640c0c0040410b00030065400706e0081c1d076126402e410f0024003050303070200c2d1040c101c0e00da15110360f0405400c00101c07a1035640390b142c40300203490120344103001c0d00542044d04000a60400a0b201581c0590300a00704100d161024040144003101403158084103040c0d00e4009604c0301645c1c1400b9140c1050007040c41030950f4655031504001a1010b4001d0f075081084408180c0d40b001c0900c2522400c03601c090841c3c13114149000c01140c3c42601400128002051185002580c150700080f2403182030404d214681e540c000751414041240c026015802c1000080c540034814480346520403461 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 462026753 1250 462025503 462025511
    0x27071202060f13080c10092301050c0106080604061409150907050d350703050f0408010c0c1a01060c0605070309120302041409010b0703050a1101090303020d050a140c0d 74
    0x400d40c50083c0c0305540e011100c1600108281811803c064801e00e100050509011203010700d13201071000c96102c00464222600e1154038880e0045c0e01c10021500080c1d42079001b4060701e030715592515210f50068501b16141840c12055140d4210780c040301500c5003840502500e6079001081e10070404400c02005a4140c1c0180d00001c685c80e610b0f0307050120502d010300d0703520802e05e80620190111165299502040603a4403110b0140f02200d0011144002d615103002510b9074200c0901811500413904410015403d003c482c00031554080c40c010001c6000b4200c89600d0f281004904915020a000744000184e01340702c0c110108510b0b030800380c0c1040301d5140c0000c2014894803102c102c901c080c0300150009800207800c0020100700d052b00006118201c88001565150014400302440f80c82001000c0c40340204400f070400d8010403000640d488200c00a0101d4041450028000d40c8000080c40703440340b0f490086440a9810700c60940d03130754034020100a103a103e00c000d80015800181103d03040c142c0b5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 462028003 1250 462026753 462026767
    0x3030605030a120e0f0f0f01020a05011b080a020319020c0c09181002160b0912070b01030b010e0910050a02090a08162301030b060d0527071202060f 65
    0x2000350301d60301da0241c880f500400000796401004c122105452620900307969080d10656030707440d0041c1081030401c40c0c28406005580d40180d080c40441d04001d4569485c0003851142d03610700001c141d55484003565490410350303c8c07848100c1240015108804150b14100c001415500240e006040b900710760b4040306e038442c0c20800021219642143c4c00e03038481350240c94100d20498104107980d560b031402d13941541032242c4201151030700285400054080400300d404124120028403031400b150550110141c2d6915282c185810710300380a200454100d20344a00000303045042115043c011102d0001401304007030100e12150203401d01515800355194200031036141d50351005c40c00c01c003d2000c078010300480405c054140c40310b560b003984000181c90201c15149290811910b100d803110354242400036400241c076002c9102401000d82e4808481c0ca0802808603802d6071311440054003065540d16403442e1541082d0a450b111503115140008814030740740782c014605000508214072501c40e00c01d0920b10707 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 462029253 1250 462028003 462028009
    0x1180603120306090e070302011b06150e060a0504060305190c05060a02010906060f0f0b0c01061a120c0c0d03110906070f1514060103020c100203090d0216060905010c03030605 77
    0x10044220307012a5030354038104003451150290980c6003203800040c2c040c807407135a00080c003a1002400b281c444183c08146e200200052580310905840208940d00d030340913240e200b03401c0601030640e24540f01e0f044110000a0718540b078003030300d003c0d2a8080b01030211480318191040c00c00440c428122030548004d60003180545441010f0017299420380e0001c140ca200b5402c2100403581c00c2d800021a03104251000e0115114021911301180c601380801d6980d0700c00241101d004004c1500194010300000d100f02201c060541d0240c2005400302c08070260f5902ca00c5001110ba00c52540305100f107800c0000b0f038a0384280030303034016850340b411011514074240e18880014025030000c54102e42e1640c8040081007400070140c120450340100e24001c2140400740c05c48140c48100c0103000714101500040c041200705c1c41484410b04d1054603900c103540787d04011034004e880350003604411005200390700d002c694901180760044203c1d00a501c031030590700d007000011a854505004d0035401e040d10f030f040028440e2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 462030503 1250 462029253 462029273
    0x20301090b0910050a0203100b130308130e0a1e180506010305010914120f0702270105030d1803063216030b0306391809090601180603 59
    0x41c010001403c1c4010b200080700b42101c501070540f01d070840c41402044104d003032064213141954640c501203520381c40309802808895040382c200419180c0b0108000b510221800845000d503107a080398640e0355030360701b400b0f03500700c030010814240750090103109486800401e03403103c480414110485100b4002c20b490300380c50040e0a80c011109a9507403030009090140144040000e426401d014008840150750044440d0051500403040068000380701c1d800c6545d4600f801301244403a000d040380034280c0f4501042610024411079001c0d000f81c83c2d0b102d20942c801c6200d01c0d1920b1048600065080c1540c68040041405244008107662031071850400340a035040000750b66400d00840300c1e00d81c0fa0404106254080003503010042c5030030030f0ba842c0e41c245d0b03005c5542a405080345900c9038050b040010100031b00700c00c150710341d4401e21980345101a030b40000d40c0100356080e2400034060070350b0b0074101444a0711104607008040350b00017100510140008044007175001401100c00b040260300d9440b258081 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 462031753 1250 462030503 462030511
    0xc0506180a080a0308010e010e01030303150905070c060f1116080f070501060f1a03070f140a0306081207020603040b33011112090906130905070609050d1707020301090b 74
    0x3540c00203d21504169000b81902d02400640010381c0a6502d02210b000541c00180001018181c4980045203a580b0414000000b850055000d00044c20f10703079009040c1c8414140183d4113541015001c19450495000d2400310103d100c042c50300c0c0c829903c2e0041c82200840a0881d5048002c200d040180420b03a005410814000d400000d84c2d41d1801001c90a821450351117464200d4482c44110800c14810045d03076440760039410240c81c0005003440484130909802003602c070b01c903c04504030b000745070715510010a892200c3c4c22074011800342c4030903c0341800384240096101d00c08100103800141403c4510742c1200c1c80c03000c1305001e0107030000d02d50700366007000040d081240111032015107250391140000201024480140100040c60684008588501003811340a00200b4011483d242c50381c8a2100900c484054201300c1c40b003103454072948441462060364001181150007003901c0c90081380003103a0a500c07041d07101070180340385150301c02c81e040043c080c2e81c995601d00c006400314006c0c9000e5441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 462033003 1250 462031753 462031769
    0xf060f0f13060c0305070b1509100e090a08070f061112060301050612030d0b0d060911101106010515160b0a0e030c1509031c05040201030605010c0c0506180a 69
    0x544207001c1103101c400307403160701007810010072600703000119030403030225012a50882158501075a42d021030741000034080600c1c54115082e00100403441c00e40384811426203c01440090300c94803821a52551840a1803015080010800107000003400090f90115070510a90001c203011000c411446403d2b04052195500c0b42c0007002085807070b150a1007000da11100449080b608400780d843c0060741c2e80580f5200707001a96031120300c00300603900c00c0c44100302e4592041c014050440940703008144164036194040c02058140d4204004900503440c40750040c40850007400503170701c1c210800184c804280c18100c0181c00c1000341807201c0f41c40c46000c0b14428002c0751011045e00786206042c040f220400070542461f0800d02400d00b0311100446c8040f80350031000d01c00720b22601c0d81e45645045226000030038580801060304500110516000303c4d1260b4000d0300d040050390740d1200150380c1d01149440042c2000e00c4104140094501600a02100c50358403e0307880a40c101280841c400c10b001d5008452 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 462034253 1250 462033003 462033007
    0x40c260f010911030d090302091503010905070614070f06020306060417061b1602040218030d080106020d052104080409020c100b030d021b130c05030f0106090609050f060f0f 76
    0x8140f02c94002c400580300e605500400e001200301800522080035408001d02ca0b42000c404592816529005101e15440040c020000c1100c141780c4036546000e544102e101062910580c52007000e03090302610511a00100010741107405541c1d038000a41c40106040d51201090101080700300394a041c003108040c0180007441e450801d4045062a04902ea1030600d40c0b82c0100281c0301c003001c8000700f0740001c50b0305807409a25040c1c1c2210a2009100003641190540305100313003900d0316684100b40714106d884940984101050401003280c49128085104840404101e036800a00c04a40c41c4240e1242c0140c805038100760311020407005076031261940248942c0320082c40d000410b05445218240042100106070392519400065142e458203481c128642030069081d0f0100d40342c45c0072050304081421000c000d103500310343e0003503c95002601c0500d0344501210000c40d14900416440b01510140d8503010f40351403401d82000140b01d40da10200d90000c0040c85a11f00310241030020704009190381486170b03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 462035503 1250 462034253 462034271
    0x5190602120a02090109031103010b090f0f1f12051c02030a020106170c060a0908030d06030b18120c1203010603050405120a08011211090408090414040c260f01 70
    0x214800d41d018144190700c920412070345419a0b040401002180c0e4008841c000c0381003840300080c01003000c50401d0390030120741c800700300b42d5203421040e1034480c00407541c09140c141c44000c00203040800c2d0b10306140285503044414880004030340402144130388604100c80640d03040880ea0480960841d9008001d03034804110201150b40a018440180003d03c9170b99250408075052a0b541c0c0701c2c408040c6005400014145070701d60700c1142c6c2d01020300181c0307040b20f685403040c002c0980107203282c1c17000f503981c20302c904040b80304d044124918110a05104000b86420245024a4041070b48141810300e80351080c0f1030324036003040d060000f944c000c100a4030700183c945444c0c00c100c0d0405aa6103500b04594800300848802740760400501c40c107646441000400c5803161b4074000c10142100b038034041d84035803404100010011804000e0000500035281405522224084070400142c191402092084000001d11080007080c0c0d461581c080e144070101c00046c42c5004560800b80e140304049002e9441c4d03003c42c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 462036753 1250 462035503 462035527
    0x9121005070e0319140715080109060501030221130c0e0f010f0f12030909090b1504060810111306080405211e19090503060c03040209040b0405190602 66
    0x1c02c040c201c00350060f221032003480309007030364801904000a04518035486040d4404c20200440006402c5045004075130601068018042000034424401c2803418400e0100355075100b8002e8482101c3c80e0034803000c02c465440d0511180110080041e04821171401550006c50420100324005000c0001c0701c00190030710503541038242e10f050300100c0348911199006c0000617040187c6c0000c45001001c04141864945011109104a90720050005080030200e0b428003031546595401610078111403a18190154180010f462151066900d5038120a1101ca400442a0007000e00c001c0280300c00b6141203810304209064624035081100051071080030401004003c210f01401040c52505103081d84041010312440da110350000412007824404210310750314689400d40c0c0080c4115101900303900307141d08004081340c00c2807248078424400c80f4045003554400d501200d000c1c82d005000c0103070369580c1c1d0312440018100541700316032610034000300380404920004000816403180e4000350307940b9924941 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 462038003 1250 462036753 462036767
    0x12060506010203211b22050a060207090902130905100f06030209040206070212070b0d060b03040b040b040f020d060c020f010605030d0c2409030f02010c050304080912100507 76
    0x40c0c90640d803042240ba04e9103500390140c01e4281041058240e41035466001e144100500e4018501c0c05440100d52407880504800046101061908240c4c01da180d49000304107038201e59100b01800b5802030641440b084403150890400940050108411401c0c450890403c031030050307400740e4494021040c8020f103420b407402003803400c0380401c406100305411030f000034608070b40103040284190342c001103d1046441d07050904041c50403c0064a001c180d85180034441a070103004850042440c0c18400b0514050000c141c07030043c0d401103a131b46c0c03641d039940e6102c110b83d0700041e000341c907068401014000180e862124000250788a210003203201c00712000701074905143d415281155904003041400b040d100012240b01c400c1940c80c044103c6d91050502c40c2100004100072501d03014100340c10803c070889a041900c40302c1c4240e03618070f41e02c0d640300c10490883c1d004542010000d8400c2000c82c000c0f4080c500540603020f0001e1403900446158503a2520f00740c00019440b564545a0041160321504542 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 462039253 1250 462038003 462038011
    0x1030314030c03060d030c0b1612020c030901050a020f0106060210050f04020906090c041d01080d08090304060c110301051503060105240d06030203030703030e0c0618010e06090604120605 82
    0x1000c0e5003941048500c1030903070702000300003900540401c20384405141c464061031490310b40042d4400079034140080385180a0b10101510703004a081030403440a5002a0b200712041420000040e505040002c03004681039440001c12200314400c40b2460019001d081c4a42c40051031542c005094180303680c5c41440c10b80710020801e60481e0390781420030002d80c41c1c201c001d9620030001c48048001d50b0f950105140207002d582c00400021407144000700c804081e5103d0030f81611500001c403141504580006c0701d000b18112039220031600180001c1144500602828a06034440c0400001c10380e210b002180c216002181c04240342c0a00384548034803801c042c4145405071a0a0b1020f480004c41490000e040002c40752042d2190340300010700d41440b5600d507200102a40d4000e00f036aa0f540d11504004006d042140341843d1240036078034140c0011703c0c2c02011288451022041140303001c1d01640103448602040c5207050300210300700014022580d6160040018240100a00010009a041520403102d00070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 462040503 1250 462039253 462039287
    0xa0815070e09060f041d010b1c0215070303060b030903130f081b1908060f090105070e010809010e07060201020a08011202010c1514070302040501020d2d03090c030b010303 75
    0x6200d09140d07071180b2803038562000c4207807882022002c498000c90020f2030800c60b200360501805260010145041d00081d24000040741c0c001c400c8a856200b01c050b11404400080d4070081082c0341000c1411084042c00443e402410001074080d600c01e803d0718907034400c83e00180c1701e4100149007e01802400e54680103445121400460704e400c10f090542c0d210351030000040040c0000702d040340681e41d0045c0d42d4440900c0c440800f0452981d40c1a515070300d06094400a03858600540050310f03c907814440c451065441e07548030590b9403205801990f1052020788403010759500c525040c9802803007001400010302a5500040c2d59018600c1c0091400006800900140c01c45400f44800750380c0c403042042c1a2900001c4484514080100230340c010216603421214808480c02086a01c2d13070503901034400c071042a0251000700c0c0c4003500440e560392940e0341500d01c84000182c1c00054440d010b02d1a100d081d400d08000903000016241c84410703225070760040790301d00002170043c400c055200b031100c03031016080c1c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 462041753 1250 462040503 462040517
    0x6030103260706091a1902070203120a0504030201140f07030309030513081c022a0d060c050d0f0903081609050d0b070e0306041a041109180c06090303030105040b0f0a081507 76
    0x403464401d0349081021b032a803038160085080f80c2555005d00c644581a03041440040c0d07a608405c40140c81a08a03100903400702d950716122030078454159040f01c0003202007038601460107802d9501500200100d14003502002400d014540344445440c0c40702c1c000c0e0820704010b1410f8540007451051015000e08443c08542117000500305e4010110070003551140c3d003510110b081010000402d618200c40c10000e407110b030604e50718201c0590001c00810050748944c00130b203c6040c180070828103403542d030140200041d881c5c0c0c00040d42d0201900006243c001289402c0741059600c17400075101c13030f0909900740c0f400b491120901408941000100e58102c40640140440b13107059126901800e00b4071802e03003024803c201c00582000015070080318941d03c0102810682d08050710041031900a14620315a20312034041e11003914038140c0c003907410758200100154074507803e16041c80b0180250184143e000548210200c40d9035443d1100e4601401408000342149207010084000c0f214016114400380550 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 462043003 1250 462041753 462041761
    0x3042a05090c21071e030e0a031103090a0b031509010b0f0a0216060201020d0b03011e0e030c01051306051e04060c0915020109030206060f06030103260706091a 70
    0x41000c0c080e44400081181a2610b80c02d55035010343c00c0c4180c4260104440143c200404a03400002c3e618074010181c0b00d100f2035686601d402d4048a1003034400c00720a40c000404c40e400a0301c1003114000d0380f0a184240c1b410500320001103103080c8880e400551240c072000c0300300403482e600c2515440c600c0390101c600718680d500d05141c40005114511707810340c103030100040c200544c6008112010340b007051503220801181e03440000030300135003050510030b04103030a14041000e07510b0140600d00c400451000e0002544128607481c400406100c00e0076240f601050045c61b100391310a108083c0304100c0b408041580f4503062030580100c070070041001d2140380000408000595401c0d000c1d41d4404c0d0b00c60800955a00807074000d81e120f650b150b0200380e5011603255080e40060741034112005031480b035021205592542170412030503007800c0600c290026070902c010408118030107001075072034920420080c80c2420742010741c032032680006401d032005c948071403112041100d1400ca14000f403082003542700d12810 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 462044253 1250 462043003 462043009
    0xd18030806190302150307020105070306050f040b12190b090a0f1202010b0a060207180e0a0201030b0627150c340816051903061d0303042a05 62
    0x100580594003a00400982c08501c565110003903001d16002403040c0b40d0031240328100c0c0341c43c1c1c0c41200c0ba030006508100c0440c14481c024006d80c800d640000b001c100300c1048540910005200c80035002d40d02c005140e61f442c689031014420052050541107400c0c0a09140307003890303000820003400c2540540c1c001c1c05c0c4a00840c90004a0328000b6a02800c2a29031010b0030038228094108141c100380d20501580b00026542d4001480c030080b502d441c1c0d150b180c1031078094503800459221b220341c420160440c100e03c070019072103503101c82d0108100402e490f05045e030303407003036103500f501881080752500c0080d5104007171a241ca00d11104152242800c03003440c00c013035183c0e0581c64000c2901032410010540249002e510311041080a2285001c400040025580e90405581c1c0300b0040f603007103c0710b404090200d52070800b5540c00c40d074180c610f40309096081c5980e9900005082051840700380040032581c400329100c051000310700a07805041c0c0c0c045040c1159a120f805c8444000c0b45d00e541c0f1020050402ca161 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 462045503 1250 462044253 462044267
    0x50f100504030303050606071e03021902010806090c3010181104120b0109050609040203060c090f100f0201050c0301180b19030b0103171213260d1803 66
    0x83c0d061801007050745804c40810545d000d030076401802031000c0300640000c04c0d0310b0702c494401c1d540258200c81c8051b00d50a003403585500b01c0c0b40040e0000e146080056a00d080140656400c00caa0304031f428648002181c03501207064005914a80d00d1068000380150450316040050b00150b03055a202d014031301c1c0011045c08454a80c82d034405c280d441c0e00d0b001004859080995008051890400252803001d29040d84051024001c1140e003910b0440810100e0404039000c0344240d17805001030581c0d40fa43d070007040c031a0b00301000c0141c3c8048074a0035038405480d1951240250b5880f44c0740d00700c1400d64420003038290b8100030200455580c0c00d100400044010740300e14030201a00c02c134005030018940703012400045881c1d900e0748500d0b0348440000200454407100038101d07401000100700b03003580ca075042031b02c6210b640780c0c1458400c051000b01d21300340c1d104000c21115611907072002a081d92421400c0e0310088242d200000e6001c000b1814031101c00c880d025040100ca88803100d485407145556010b0918 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 462046753 1250 462045503 462045509
    0x6060603062d050405070504170109030f1b120c11010c02030c060a0212070b01150804050601050f06091009060306120507140111030304060903030e010b09043207050f100504 76
    0x10008400003000301c0101004060b001d010058024000c0785410318000d0903039401841403841052614080541114041c882c01c80002d62540e1040d60101d14204110703209404040300f0742003004048802000901c512070101d40125154031034245c110b00c28100700c0d000744040360307659040c846100117520060381d000c1188402080c3c129982034592161500413032030300500c03100440c401d1000045140c01e100c000816541200e244d0b0300c44500280400204580d5014151401405c60340044014405464000e899412456000d003a050070f1080d5580000d105031610841040411044007082c80101e515010b42406441852010890000c0b1552132030781e582034904c1400f250080210201c1203a030b10030f00e560101c814004046944a040070701b4604020001c0c00c7d01180440c1c41c2001d01884c0240601621042e0030000b0200b01940c1d85a45500f001d005c4d20b08004103881603001c5030a4842d100c01e018600701d004040780107085482c10700050211500030b000c0000d1240d4043d808503c0080e070311500f16019 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 462048003 1250 462046753 462046799
    0xa050106170f070e03060c070203010b0307030f02040209062205010f09272c0c09010506071106090301060f03112b030203040e010b090a09201c0e0a0606060306 70
    0x360b0320b103d400c861030f01074485619850300a060a100038000c126015110440c002c034001c200810341c0300704043c1c0d6900c10f440000e2008070404d4800000d880c6c50f6000d0050100098000d600d4411000c0d00001303a94031191010541c07001e0900b0601065034407401c82c000820250500c1e114503824585054080b079208048042018a8140c2100d585042038100c0d43d6800402c0f040c0303281c01980e600310908010f800769004a130a00c03d4a82d1038941f498510881412914007034080791500c5a1600c0351b105070051001d495410202c200a81d4485490034400c14006108040c1205021400c0d1310304807445003100800344d803080b0410700b0610030320007040d0381c0050400c1840c03c04e0801501c0f1458240e0440c003c03584044501c0c0700d000000159049000e0040c4842c480c1201c0003040d0a4079040c0400407216a0040c0c042175120400130740c4451200d01f0028a041d0345040100c10354561400b144400fa54400100d2000c0341d0041c404c54402c200b898043c590241005041c14000d0700e0038510321820403c81c809030290 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 462049253 1250 462048003 462048031
    0x207051c0f020f0601060c0b070c0804090e100c050a0f14030406020a030e0127060209091e1302090408160b01062007030b01030f080408150a05010617 66
    0x108219040114a01580d0a0080c0203104640014054014010009168090702841490100c200c1d80481c900e4140e43d4a516070303004080c550340f00e1028008005020354180940801c1c101c020034641006480102128800407568540c007610ba1410304203405604000d1500b01301041e031941d03411030103451500c5040e10303059002055885040351042d08620382801e03441400018001442105d4009140c0030040f078400b40010050307103000508890014800501002d400b40802109085158030800c851f80601c1c005420107540d100001d14180b41a039600007892400001010b8000350491003643c44410031020071040016a00440e0700030b07000500040400c540042d0107440000c5001d01050030b036070443c1099880f0368681001600c07803001c5080e00390212001054101c0064800a03142003680d52041c0044440e074a103660740c80300382d01c0342181200d15181c184800320703007803408000f008048680c03900000c4041c1441208082140c1e0181c00140800911013008441d0055600e0b1140e003007040105c140c4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 462050359 1106 462049253 462049267
    0x406080307032c0319030212030c040504110f0a200a030e0f010c052e0605010206241002030d050114010801090e070e04030503100e1902 60
    0x140040c0f0140b603158070034503a59801410050800c03901c1c003454a207850000e400c2c080500c0a4130543e82c09551444c0074154100503038140c0b0700e000c112981c40c5040038850801640304600503d0300868907010040003464651089401c0217103241c1c0188c1d180c0c007a00310300401030510b04040440005810000303900f902004110820800c3d4583c440d003000072110018071000c0319200e9002410302c09505000000700307109129001c05103486103070308083e400e0b41c2da040904001d900ca1100030001c0c54503009115598001800070b81060308102204540d480441d0650251280c80b4002034000c68600241819207800001814101003e403405019a0f0788800411030040690f07100b190001e10700b980100500c400301c2d4806080c2241340d1054540701929600d091403882c10a035400c40c0080c0f0000100850340c003100f40e044014040e4200c850400f4201402c004080241d4029a00c1804c1d0b0300190034 = true := by decide +kernel

theorem cover : BRFrame.Cov 461870503 462050359 := by
  have h0 := BRFrame.cov_init 461870503
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 461870503 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 461870503 ≤ n) (h2 : n < 462050359) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
