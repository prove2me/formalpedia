-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3479
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:47:02.769668+00:00
-- url     : https://prove2.me/submissions/86bf9152-a3a7-4603-9b12-41acaff01e8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 625539568 ≤ n < 625719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 625540818 1250 625539568 625539571
    0x507230f0102030c030c0307021501030c0311041a091003080d0c080916060e0f030a0c06081f1a12070c0303150e0609040c090c020109170f251e05010b0405 68
    0x41c110b02c4d41c80c59a4680d181441ea91015084400710700c80c0b41074201c4a40e00020305031f8080c3d40b150b40d00c0d807005483c509040d1000012076600d0351081c0d00d003008000c18020310058040142c2d109039900300c400c0da02e040341806000040d500190500b50005107840718a1660b500c20440704003aa100c40100d5194030f85210b5440c86076080b03004a81e40c03241d5081c401c00b802203200561b20344008161100c4600b02c0f2002c0380c2000c112120890741c21182d92824424503411003c0a42c0c1300d2441d0480d034144040c0c03c800740194006034440d0300740030540d14450351103860800c002ca8040e008864081069424030721001415111a0402030b400a071929090a480b06088002d2504940810103500036a40b02c5a08000081401a000719102d9043c2c0300005804013040c018154841c0d6943c00006148800e41042040100004428207521034100a9010840d0803e0f0035a000c03d44c545400c21101c1c4584e41d000811100403030800751a4030942c001c2820000070f020b1000c421640f06000a00c14480150107100982e0310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 625542068 1250 625540818 625540831
    0x601090b010c060902040b100309033002030a0605030f0d02012a1d0a081b0306090304060c0501111c1d1b1f09030201020607020f0c01050a0507230f010203 68
    0x1080c01d00c0b5404161107030014030a107400104001400728403075000410a6400c000c401010a0b1100c82c80024542c014003601c80d21080f11560380b017020000b4002c00d52074040300c1e444200c840d60110103d01c10902d1540203a000d048041d04583c0c02e03490020380e031580c6800d00c1c6074000041d820b01600311000c2107482c100c0c1d04864141400c0e4446000d0368101a141d2180440c1e07104214156001da1545030341e5507155420003455072034041c003a034428000708aa280558000400d000c0d6200700244851540d00000300c070121035107403a01c203045807641c2c5422030150107803501c409403101b40890043d103280d49140c408080307030040c09410062601c00040299110780d0390310810030b65402030221070400c0c040f124a2495445c000070702d40520f800d074109100d03088004d40c8030000e000034044c103801d20841d41c04100007904004540001c0c183c071311303694825542d2111049481c0381040000304004499a0103001951046c0d03a00a003c0301d841c4046044054112483c240e9528985c890092803045009040c8222405040c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 625543318 1250 625542068 625542077
    0x602030a1403060f041a1302090306040f080d0e0d2c0f01030f0207060603121107050f01050c102705250302090f09011506021c030f060311030601090b01 67
    0x259103200050709410080c4020b400c140d6143c584102e683c3c580c404c011701c1c43d0304408800f5851101509007c1e020840c100c2e00d008140c030401a0360001e0358000b0b41c8aa00030b50104280450000d5458404424092140c3c0d1903947c17401c2c05844140100702190304040446035607120200f480120f02d124400103031103154440d40d110a01d851940505040c000c280c030801060401240c14920100c02c41c089138801d0390b080c0c1c0c05540d960428070401c803044111a8114150f840c02c4001c002001e0601c0b81c960100d031046c280b01c0d80301d81c1c000c020107074000c00544c2c0d0b100c4000d405803010400700c1e14001c0060007281a101d4000300d48006050350b80740d800821039101e40c0d00325008000c49441d02d42c0c110007541c00080f1019980b00100f80c00001a07945d29046482175448208039803450802d00c05550030b40c0c4607180410b104111800b001d00c0307190781c005002c64000e16030b800c0c402031961401c1c000307a004203440008000d8580c14a0804014445240c4003c2202c01c8164120341290307070380c1c03000340d821200c40d180402d0005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 625544568 1250 625543318 625543337
    0x90b0c070911271906020c130506210a0c06083705060a0b160311030a0c0305030403110105100608010b2514060f0103110d02061c0605061b06010602030a 67
    0x7003401102503503850401a151614113501d5080f1011481e9690b4056801a8008402c004150414504111820241c0103040c00a400d0000001e003940134200c1030b0304d81c0c8081ea010461040c0c1010411665a190840b8a120032191285c80c010210442210303104402615036280c1c41004840c00e0380703409482115160350040d841f5a50b84c04001c1d24002c2d12441d032080007100c022501c03900c007030010501070880c1c007500704482d00e091401138002403140c0b0500e0419001440031011143d00000f80880c06c950501c0e044d42c0e00d40d640d00e01a12585148401e00c1c12641ca00020810303041c2040c100d0310b00350703541d03a220340c1201e0383c1e924034000c05842a030688072070b8035a00b88003801d00716100c00c103074900c0c4901c541d04542c03602d48075090036890710b5400c80d003c0c1c4418002500400c10302c6618400448000c0080e1002c1740103a0040d00403d485124402e2018600103101c1c1c0620107800b0540e00800c00742400030410b6580720b80c0000c1d2440d52910810185245000700e0000080850000080716100340b0039031a001c3c0e03030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 625545818 1250 625544568 625544617
    0x806030607110a0206040b0c1b0a03062403030207090f05011406030403051e091002010207020d031805041107021915031e020316020d050f19090b0c070911 68
    0xb41a5101160380c150312840600030010ba44240190000d800403090558072040f00c000040d2602d00140b40640a20511400b814420348440810105490b000200810910615141e101e4122a03e14422a40c400c4000d004401c0580c007040303c20403201d46030020300201c201d000003441154401c1c1316900700e0340081140a1900d00740342014503403040c024189a41016030010401800e0110000403566050001400c50a0361030509400514107505100031800d25010780d0119003405004034029090000c4100c05150004002d40d0080282c40050024010500480e0308510310b6082844102d1180c0d00c0b2847c1e401042c541c0c00607101c100c481d519001508040e4644064008120000030741070b00f0300c00101481e0004c0d4080c0000d6005003d810000c141105071000001d0401d45804010300401600704030304100000c18005507a00510807813a4003854844003942903807180644d0340181400b0102054519440d01c020401ca41203900c40c00c002d10128083c900d240c00310740300d003c80440043c007611442001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 625547068 1250 625545818 625545827
    0x2040f030f050a0f030c0c0b030f24040906050105210a060213050405090c040e030a27030605040f1509021c030207050a12050c190b0d061806150806030607 68
    0x540d1030203241560001c803d03e486081d07085024400a4000c80c0c05192824104143d8200500050140e0080c441c1503090416400901030b0000e0000c40c90b00203110640c03540d0200c402000051890010b004006152041c90a031005e41024460300e0300c1410390300d1a28030055610160541544010b40c00380117840055681c0350000c0d0086020440711602c85c9070b0110351230725a8032440d8001c000c0c4000400031041842c08120507541840f0043c5d0700350308140801708196400404103d01410001078186000d6000480003154980941c0064400d900b08428001400301c0810142c00301405103020180c1a4615039a88040d2007030144001c2d00441e10304020b105004403c101d104609229206070b076081544d900c00140f80d0304060308010071004150b260401004002c00c41e80300322072410303140c0c94400c8ad104003003041c1391642d61041c0184c6140010703c8040b548550380c401c2010b044e550342650380302081c101b6821700402180c003030301014104020703420001c070b40101c00035032281c0b038000e000300404e9880090454 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 625548318 1250 625547068 625547093
    0x303010e070c02061b0610030b070e0303070501050c0c0d02060f0a022b0b040b0d0f031107080a030906090b031003120219060c0201151508070c0204090311070902040f03 74
    0x102040800d24042c0d0040e610b000003014003604001c100681c0d030381102e015501b4904050425484540c00c56400c1001402d071800c00d035840811810502010100072002c282076105180380240780d5443c04040141000011001d058440d004104681074412101c20981e581c41042c3e40f28100d003c019400541d2039041a0000d10b00380c14074039804441403248107000d416001e5240d0f6040406030315200b001c1100d08103032007402d600703010481e100c110801d426151100c0c2407800c0b080180800a80300100c1420085c1045410000c2c14841c003210102d25950400400290850044a00290b8182400104240054141da0054507142e100c030001d01e02c2c680d121891074a00c0343d0040198018000e94070101c0d50f04180c0c0c54049400b4002c00b040c06000c01c4e00007421601e0031070160382c540f4003605007400402038810920141d06241d0500e114961596201510035241d800002580142484028010154044110f208101050040307403000360311003448a09a000314060700700c81e06407005040012812041044 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 625549568 1250 625548318 625548331
    0x6090a26090f0d08072a050109170705030609030d0f02030105090a090201030e070e27030d0e011b02151819080409050f0f060103090c06030c090906060f080606070201020303010e 78
    0xa20031100715618503d8503000180b0540b041d07506c0701403907880d00742e210360300c205624078030503250301854101400a400754605008140700c8010300c2e21304a025002c100a114050038000381150054076000750016565403000c00f005480f42d00b01041c2e07111420b01070081c0c0307040ea80e0040071043c03503507a10303000c0000070031030800c0590415031240b104c003a4010090119101a1290101c1445145009805012200c201686072072100e4148200f580b0219004802e03940401088070b80402c41900c08009680901640302d400104410a484000d488580000e000852410304140400071070382c2d00080820000c81600c185c102030307040392000000b1080b84003194000da40c0304d0890642095103d100380804c43d60116036000340b8502207401d1100b40c0c6800840d6980c8a4800d280522071101c49648134110341105d44101001e1648503140a00400c2c01030100d20050041d420301080050b9442c5001016400f8100b20301c03001c41c00c1c1001013490b07414500f04440e40c5c950107800941c0340d80d103000d140000000d801401d4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 625550818 1250 625549568 625549579
    0x1406030f010b0a021612031b0215030c040306060e04020102010c030c080601111e0304061202040515030a09060e1b0105040e0c090a2103080105010e030a140102070506090a26090f 78
    0x21020052480e01604060034003c0058146900c880c940605560300c03023080909100021942d901c0141e88901800181c10984003c940e107940315251000e001c2c0c00b0f07540004040300c1c1849c00c0815400650076400e84518000d81c001d00c16980101c1c07007542110b090140c103a001906180c002003c650103070401d4103101c88000c1c22201d10b6907105400f01c000c030300c04a01503031242c1c100040410032641d2159540c1e0000241c11011890b0514100c00600c00030342c1005142500c040100009170f00c01030550000c501143c0010080c000e01d032a4007003490302c4462000004110000b045c0040e032345540f0590a4a050310400c440b912270310f0311483d0f190440b03034014136012035004001003c04100061111410304003010080b000407500d800301c1c42c0181207010141c0100e41001707404480078007203540008014400e96000695559500104407086001e44140c01d0007a005118110074014255000039001c00c5190203128400b80c60703807820b68840314240b44540481041c44061260441c980b600400200320044020007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 625552068 1250 625550818 625550833
    0x206010911070c0e010312050a02031c09060911150418091b0b0406020c01140d0f291002030a08010303030e0a06241a0d0b0a0504050903041406030f010b0a02 69
    0x82d00b02a5a01580144c2c030400303040e1004100700550403107041d12003400c9051050904500620080d9640140741c1d0f03007004d03c4140412408446a130b98403c1d201140c02c40c0050100081d0f82c00c18803504001c0c560094041c01300019100d009403049410b40382030325440342d03400c164402840c021001400307903c1ca040d45c1e11441481e50b1135550100d03403a0140140307491544036494504e0084d01074144504846070a05124200708900c1c100b00360074040b240e80990740d900006074642c07c03407039890040c000c1c21112007a0b04c480c02541000a00440340e042103101c41103441030207011851008a0f12402111641780101c0d0700b141c018000a4001d400440700d03683c1c14400ca48000c0d10980703e00044c0e80882c12510300852441c0140b910144030010b5807009402da216017002a0903803040200c150340300d208210b03c525540e580000030341d0b6850102003401018020024010ba003804180d460305c9900506c03a000380641e1040350000c4a00348034066070700c169400e1400c5007050b0f00e00a030350300031540504c0c8500110702a060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 625553318 1250 625552068 625552073
    0x501140c06040f0506010f031e030314180106080114040f061e050601020d08040b1603150806160e0a06050a05070f050f101406010302090d06141e07020601091107 71
    0x11207180702d1030140803034400541450030f03c0707070030072006800c891480100d2607014000b2030200316142c401e4045880207220501d480c1d0400700c00425091174020800c15094043c07004140e0030600e108032441c1208005c101c6c684d502c0740c1032822507440d0a41004020750039000240840c0440d0803050300f0600402d000b050445035084003010380361078007004580096945013401103a50781040700c25520b00060910341068107003900c030362800110003003604103180c0220702d0300c409442c030a410980e1002595841c002510344c0b00d624213515038030121901d02c0d42210b41042081d01c01d104000302502c008014200010b41070401c481102c095000c40021381c1445400c00241d00040d02c580425480280510017078040d01048082c00c0f42080703032242e80c0c2159141441001d10104562900d56500503509080051f40c8140340300200e060319020701000381009180c080d035444031000340020903124040c506101d01d00c0c0580f80350341e240c8007034059845400507801100140b20b0031401d075014000c42151914180e00f03066032075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 625554568 1250 625553318 625553323
    0x60d02030703060e130510020a11070909051c051602061b0a1416140a05030f0706080a060308121b040b18010c0209150d1703041101090605040501140c 66
    0x94480c180000d0783c800d000c0040c007202454981e0020840a525140c40805849003952040b40c2032030311101c01d50024503140210700440c03440c0741d800400415250410395682c0c50706c5c010562040d040d9200e0080c990224000b11400144103d124200c0d01c1e0030341030142414068080c1c10780d060040742c0000080141d10a00308000307004040c426003100042406003030500d0715450540034404c5c81d250707551294805001e442c4600c9440d03003d6075042400007000c02240000100c82c2d08265100b181c050090058050080c0700210b07248055415649500c6040c0c0c89440c1c601c402c48040788406807212a051105031250740600344041e4024540704d82c5619a8040302071814156400b07a4803030034494400084070790041d6002c014100300c22000f401e01d8001404282c010440322240180b0b0702d44200c0d01000107952030350b6040c0c5d0580d0040c0d080710200c0c514003000340a02419030300175035040e2403601c041a4103500303c0d823062100100f600c005944d494100381c500401550381c00600d69100544c55428414543c094004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 625555818 1250 625554568 625554571
    0x25020f0c0405012d090908130e150d020d0614070807020607050324040c02030d0b0906220906020a030b090603070602030406180510020105011d07050708090102010e060f010911031303030209060d0203 87
    0x2c2d8030031f0b035580c0c2c444904881003882c02e40c0320342d9403e0303081e00030800c10040e41207076038010060994901030302a0301880043d00406152000410b01403900c211000911214040c4c18840c2c1e001d5102c10b035940c1c496440903a50307031038102c4101d030001d44100000340040303800c103480704606112900c554000704074190008096800c1c049001005030300c00302e50101d02821901860311240d2058a41c0250390520384003107107502c02181e41c407160110f00c01c04921b090039059400395503800c0c2c00c038000b10340360401018001c0242c01481e015512500c000c8001c24554500400c040c42215000c2e00213601d0103107045820384107085041c0311551803032500c00000802c2e4031101801c5c40f042c40b441e4000207171036040c20006140e040780c02d0400c402d0001002d00708140242c10208a0750200d8000c00c000da01d80c8410310040f4007502c3c1c0e980040e030060244a041c043e41c0d1300c6442045050314031101c000c2c0300350b90142d0141111404211806800444200a10000b00c0d009900400f0201c0f0b01a25141c602140d560701801a07130320 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 625557068 1250 625555818 625555823
    0x92411100515040e0a020402160f0510110c07061416050c030616020d1b080c010e010e0102090102070302061308030a11070501050906090925020f0c0405012d0909 71
    0x1c49804014410807403110000c06814122400c02c0031000030038040c0c1d0b0319004c13481700030301441d800200e0095211081c600b1284241c0d00c1010f000c0945154500345403034111001d002401141800040e07103a85a0060554034491b840c3c0b002030034401d1401c9003c03621081812403941803540d042185680d0190301d8411007102c50701420040006803060400d2502c0d05500070641500f042030700c413100c440d403a80030500760001081031400005d526002c1c00c0300c1410802c80d0ac0000c002c04030018104800305c40640040d0070451454008200d2440340005644c00e0348909043ca0380140c104044c01d000600d0000080c20007100100311030b6180e60b843d25102171640e40800c0d00b03e004a907500e0f140000c655401c000190140c4002c3c6011428091140c0100b00240240104103200c0d10000f0005094038911032107103071031442c03014a41d0b6800301d20624040d4403034215080c040e410703010300420b000d43d50416008a40c100c0e8120b01440e0203454203124114160b0403c14140940c04c040001b0018004200c3c3c00341c01038590 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 625558318 1250 625557068 625557071
    0xe19080a0b01030c060504051f03021605010e0111031005060d020714150c04030c051c1b091d03030f090a050703030e120f0601090e07030c060e1009241110 68
    0x5055040c6034130a10030f558031510801408100500c0240ca40003480c034009042200e41c1030101c0c1d441481070b0042e01a443c40c0c1e03401e07210704105107814031805400c20102106c511008001c0d40000c503803400380c00c1c0b000702c6520010503801c0c0070400283c100b80d001054902c0400d0401820084191385070345207009012070302c4c00c09030700c107400c20264805044000354001022070540f500e170034a150343d104200350041c4280c0e407160000e44014854400178041101c11a503010030803100d00b0201c070700070110380d90359400f602d100c3c9403038034482805103610001e0740c8482484020003075045a03604550744d04603140041850009001d80740d4603900040c810090080658440d0b21a1010360b00c0440611180028030351140310300398004043d40710320000c0031071544e041d201d1001c804280000d4003071509107400c80c01e610052014400000005580e035001e120864070b4802142d89180b03840c0b403c081150101c01c1d90003030510b0200c861108042c1840c0c2011860346100c1e00b814003440d1096204e5080d401d00275055410107009 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 625559568 1250 625558318 625558321
    0x40b120105010906020312040b2716050a08070b1303080f0304031407020d120207081603020114030c090f0f1c030906031509020f0f07060f18030e19080a0b 68
    0x25a00101c40c1c2000c0e0130188000c50a1184140d6042e071940009000a40380410301c1d000309003414804805000720100e8500000f0030100c1d1907803125a11000120800c0304228469004540c0e4a01701e1424400c0b82c00100041c209141401c5800c038a55200101442030132400450010009000320003400002144000650b201e25041c14090002e10f051441003941d0070040005000590310140c481e03c1c81c070303000b07a00400d01501844003a454810780f0342211140740310b00c905401c0c1d504983c075000425a0b00c00c0e83c927603002040e404440c00c1540001d54002c0c1007644e061008521070f00f042030354154404d600030054040900c2d80000315900780121030240808060060700d42e024950800991802481e1619040003c0010307070301d804814144034016002c0076500050340b0321034400740906540849400b40d0341c140e590501403400d1001030009610814001d401d24034000741125002088a1040303416880300d0b400458800c00f00009083c2038182d244110f8ae001c0008210b020b400c026034100b07a88030f0a040140c6 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 625560818 1250 625559568 625559579
    0x918020310050a123f02030f1308070801050c0d110d1a0906120a0201140d0518150708070f0c060612050c0406062109020303280807090b0d02040b1201 66
    0x744000c580254801221034081c858004101215004d165042d8112100840348030700d00c207d045100390031254594400204451000104107000082120386010446001a03031300c0c020781e402d8980445041c0e400324814001d4143c0064590411040ca241d1044c040346440d11039043c8404139004585044000000e032641070071141803080f8003a8102908480d400e480c0d8001d030b100c80340c1e940ca403040c00038104000500280e030944061030a948018031031400503c07003072800b10554001c10014540d50203951240c43c82184005a000c010305e0b00a002c640d81d60b85031569905029140c0d06a400d04100410a0648500300898400d00c42d50014044040220310503c0c01810038510b4081c0000c1d03003600c19882c281c420444142c101b80c0c0c4000400750410855444114102d0550050642403c0690140000a03100c1000d005e8813050b5880001114061011100304280803203000600321504408544046e01c288035859000000d44110361040350090701d03064403100e142070f06402c1612413902c1c950034480140030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 625562068 1250 625560818 625560833
    0xa06030b030120090d030302040909030503061804030e0d23010b01030c09080a2a3b040b1b0c010e0c0102060f270129010918020310050a12 61
    0x15942180428521040343c1a009654180310b4200c0c1c091003014219515410503010744c042d1402042c0d1032604008480d0b00f07003005056940219600e80c800c030b2140c1030070582603004402c032034010b43d056500c40307820071051418003404e1500d156054423400708182c400002211201d00042084120400214041d1a280300140c140c0d001e000c01442406980bd4007400350300c0002529100443d086080340890180c400b100104600541ca01010082610040807a08000480303003c8003645d00f02d036503e07488034010f5440004c242203e65445424002c6e01000c40c01140a0111350360f004602c681031022034440322184c0755120751040c1000b10f000c1e5100d80e51005c203210140301665003c1000e0020304603a181030700000001d464002d007500c0000c02d400d059002d01c8080c00304060070880600d0020050407070080e88004d100c0b020751508070b070000341568031040503511680c206402c40d108451400c01c903e69010f1040040c1d000101440c42d40c0020010000d1681d8421582000070071403030030905107052241c01d1044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 625563318 1250 625562068 625562081
    0x5010e0402120a0203040804120b040c050d050a06090519150e0102040f09091104060e190b06070221160303030509010b0a050603090c04050a390f020a020a06030b0301 73
    0x18030551050180046403070407202d00961200800c40016520765a030302c0c0c8410a40580d0304100b103100c00c00442e0f0801c109490490354041c0b801060031152159880007049070545941da00180a0b4208030050740015005402c404d480622407402c0d034140940b041c80f152200c11000e41d09450f115501940c0080542c42031144d00d5581c2c59810081d07142505103901011400b046200729a59180c0c6c0d0340c100c45c1440880c80e01d2103031441d402482400b4699070390740106c4a0240c140e440c1c0402c5940300d0ba120340240aa40f00c1d03806094006800f190412019400f0400c0411005031012142d80e0308139881400b03800144401507240100b070440d02100c87c191306000301120b000900c030a005a1410390803820558030701039028103d0304d00302ca00e0341e5a40c3e1100d40f0a81800c1c208141c644d0000d050030140140c0000396088003d818600e69040d685808481040549500d50507500003156580582c0e64803042e8410300a113541c10200c7d00440e0130744080380e40401c05c10400d42d07010000082e0380e540950340700c0c0740c20700800 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 625564568 1250 625563318 625563347
    0x3060e0c010905120a080a030902010e030c010e0f060403140319020d12020c011b091508101e0e19051602071707170312060904050307020f0402220501 66
    0x40420500000c0007038551445802007602c1031148200d4400354150800403602d031207500404140c0c40700039540d07015000d0010402c00700c2c0030420000c00304025081c001200b00c1e0001d416592994541040710601500403800c030501900246c04020104c0032500d010000000e10706884011582c03800741503500c40212901595550454002c540189001d96102c0c0340200d00c085003c4d0300503170382d40c400001a40100010b1000d0f903010541510289503aa41001c0311b4011030301103410714070211152860444016004581034141404a55818418114102c0c04080c070103090346401c1c011280c80e92060078182c2c0044400203010000c1071107007568040540205504642500840524082000c40c081e48440d440c2c001c5104450310300c0c0380d004099804010980061400f011680f108061400b421900c0b80e00c800c1c80b0841400302c50010130307141e0900b4440544101c1d0000c01035030500e0110307400c0001141c652406039034895000d000341104040b18541411022103655071083d15180390100140c108109803000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 625565818 1250 625564568 625564573
    0xf0d0806060c070308030c0405030a141b0a031106090910050a090902030c0909120c01020c072405070302010f18061a010e24070b0f0a1b180e0901020403060e 69
    0x10b080a05200044290550b42d010124a0312641c4200e112102401113901c025810f10900164909103c20076245900c0c00d1841410b823085040000d10101040400c0c400c05900708644200400100e4004240e5540503003000b0300440c5032004960001710082d40a1b265000c80c0b2624140420981c40c1003010385008103051202405904a0341c2c000948600d4650001402031070682e0000744201d8080c0820b40e51241d2100c4126183d152500d501d5000b0b4000d10b803043d4041c070a400d00884c800c0100228042c15140564588500214451303040300d0302d4010003000c406564a0b0440354000e0041c40c02802c0d012844800c064000c4101801c000051303c527900c001106c20480c2c61100c100c580d82c88403a0504000041c1c0b09150240404000300118910055142c0c0b59140302007003480800c0148c1c401c03940500382085c0010010745845c0d051408485011140c9450080b02c1c0c010000700034010180030340082d00a44500015660f119260509000203e602d81100e0b54002002d0007086103610072042c90b4800c2a00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 625567068 1250 625565818 625565827
    0x1c020d08070507060b0a08190203070f0305062409011203080615030a020714060a090311030c0604060c030b19090c05040503030a0804021c060c14031017030405030f0d080606 76
    0xc0c2180c440d90002904131070300c49152171040d031181c201c00001400720308200e54a02507078070130407001402108000c034401c0c000c00c0310001e070032401115054240e9402201034203039622403018140002954100100d20341c8605601c0780c6480d5034018245000740030007030860017814002e10f030007080000d0043c4018810420140c0d0030f4000c43d22041a65030003102941c0042e514200340c200b0302c1028400c80042c401c18480c4104010081c0c4591b0000041c0e503109403103906c40388055510b010703200c1c003c07507041313a0550388054001408a1303140c0c0c01c0f490f102100e600300042d04032404000b04544130440a0050840c0401c04070410a891840c86400c0d0050554507007582001d0414001a0303e912a00d40e4480800c02c450002c00e06640d16203109082004038107440101d6207403a850020003502100d50342c04049020b546070740603c10b800c082201e20440d100c3c07040c0c40d00d80d800c00c0d038160145a16a17004255500c0107020100740c41d02c08015400d1607000e400c0041814001081e8020000c40004140710b02902083c0f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 625568318 1250 625567068 625567081
    0x14060618090a020f010c1e120518040f09210905040b06071101090b0d05090d08150919110418060b04090b04020d06030305030601031401050d02010e121c020d08 70
    0x203070070403299904440085050401d0710040f502e03044213040c0905260982022001c0064603102c47ca01c400c3d10035108040f4055110106039010700420300e000011604880002030300b441c241d8080e0840d1450790b2130002e1403620b01d40340c030140c5400840c0d164880c940488600000c1c6500070221760000c1c5002c80d02805441400f40100d02a070280800040151620007040074160b0b0042c1520005407845086003a220140c0000d20790141400342e40501c560301424111440861142c14028401d9480c2040704101105180602ca840c240040203101c40b0103480f9203046214905004011800c450f41c000c82c2d032183d081c0084125000b485485200203980b82c11000c000c500030420554085614490000440803034440208020740f060000180c0a1850108081308164004000d980074480a0780c0400003049d0100201d00d1103032080c0034242e401350064444100641c866500768121b0000903122800240c61800b8840c642145160038641c0041c41110102030b4550411010b0390b00d5102c0c1c606070301117040c03c5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 625569568 1250 625568318 625568323
    0x40e0601080a0b04060b030307030207170d090b030a0e030c01091e0c0b1c020d0f0f05150f01020102090a030b0405190c0b0f09030604061a06190810031406061809 71
    0x1084014140f081500c002001e1014070fa01814000744c024040d070740d4544091900075190992401071030014040070b0600428007100140d00c00f80c601840c0c540b070390406d051040c0009603820003846046065190f000c1b00124050a10240490448060011440058038644101c49480c541c90310a0030345207035410800132501200d018402ca4480380440c030f40e2001c2c0f0325401c40030b124503c2000204140000340c80d2000782e602d0f900000f03450a40c207408000c032503d032811010584e10f0640308003004d82d10001c0c180c81c55240c245020340c10008140001454480a0030106400050a031f00036190101034004000034408248002080b4028005111000d0300070350340c41003020f0f5041c1c040e03005e0380d02e4040b91100780c504606045030507540e00141200c0c0d59203000c0c5003000140c40341c8111300c0c0801d00300b0230640044c3c0c20940c050b1590b00703041003110b4031258180401142c500c0401084e4207805c0405480c00404034118816501c41c1443c800e000e4049440c2c410140000303191405550211103444400704048100e01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 625570818 1250 625569568 625569583
    0x2030604081b190b0108030703090306330603060e1e1306020705060703060807180207020d0c030f120f210608030d0203101710050a1811040e060108 65
    0x109515442e8414140c503036034500c0341c9911110840c03003030f0307030303441e00105052030042d8207852050f050111140c0c0c88a207100d880303016000d00140816000c0d1001c0c40080c2d015001510210f01804210345120b0b5041c01e02c8000001040041c0840319030351a051103641e1741405100042c08140014103030300e0a0684030941144408401000311450100c01b00c2c0310900b2110110f00358070b401070019900c1c0c0c1d081c3c1c2011515420151440008240f40110015801c2004181c1a088030000d2a142e0380c001c1c0c840794044042d62020704200c0c0c0c032085084041c0c00051344000d40c000070b1805000b034130b4001c41c0c1c45c1c030b411441c0f032900c1c107402c2c014441040d03945030701c00313a01041d94110900070340b845041ca40c0414004038090000e61b0030907042d41c0400300c0d803203a0b40007180d1301440c4100c00e684803d036005581c8440c02d6500c6c1841607511207180c1c001d000d1340c5c03690030070a410540d00030840100c00125480d004044ca250051203210031101208500031001003443c0c5405002003518130840986115490050325541d00c819 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 625572068 1250 625570818 625570823
    0xd0f050610061b0f170901031409101d0d0908010b010c0f02040f0f0222050a0311091b040608061801080c1201020405100c0b07050f0412020f040c051308030702030604 73
    0x28845080c074100944013016034076251744000700d0b032255503460b078002910f504180035090001e480c00b003417801c803442d00c80b0001e07004034584005003074003950090004000e0404d5610505000c0b44603002040c400608001c1408041e005a80b000406410f2030401400d41e81d0249603581008100c584103000b150350806148a00f42d4102c80000b00c015008a40702c0c0900501200c01501c03600c04511141454203c0c105081c2c502286d01040c0c843c9500c1d00204031074514503010240c81c51000c5065200e40342080c808203600043c01c819a03010328140040303da0925803090700964002543c1109010751400c040d902420021104810215158101052a595400e10031000d62040b000020300400b008020b504480103440c0180007110782d25400030300a000d0103012241207400d42040d83c00900500e100e1402d5884980c07201482920f464074001030a6100d001d885c2051303900051800e028a120b50700d84c82341d0010f840c01740d21100d03119a508040d070300a03410158882e0050740c008001920041e603020031015401035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 625573318 1250 625572068 625572107
    0x10912080f0a0204050612070e1915050711092e0504050a0c1d010c150902101107033c0c120302030714010e0a06050a05220b150d0f05061006 62
    0x250380740b604540a4509c100d017541c01c040c3c940c0d40d107100804101000025200c00b016011600c13682010211030500c01c019002d0042100000c0700519481e00c402d0240c0c2000c0c80c07400c60421800c036184541c1126400300e10704e002c950420081044641800e001d420f52185440000308440700d0384800c09172160040c40324107401000341414201c516130080c40c400300e01a0300081d840c101030b0800c0501c80d0050002e6a002c0e032040300c94800c1340340403c0c420071201d9000c88540000d080954034544e40c840c11031a5191012025440c80c05601100303012078060380056041d8401c5c1e019102c3c0c06400d0103030310624a0341240e2451000e00b141080400d4000044400513079012070035003000120f1040c000d0046c4488030a080d05030040b2005a02881070341c0d0000d034095000c406042145032142d1014144a0040030201e403010044450000045000c10b45002ea20030700b00070460030101040d0000442c440280707801103954000480c507500901ca41080310310342c40170580344085001824180081e0a003440e08810000c2ca0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 625574568 1250 625573318 625573321
    0x60a110c1002030109050f06030319020c040e01090c050411090904020604050901270903080c0703090509010b0c1005010819080d09110906010e0105030612010912080f0a0204050612 79
    0x122584040364088100c0400369244609140c0100001e940b007803181c04289400d02d4041a08950441000c602426004000b1440c0c003a05506101140304e0250014095016025501c411034031540118680805020000202c4204c1e515005000c103c4541025015038034012080744004d04c481c1c205c0322019411154100315658610010b02c5901c69500b10315001490000001000440001c40606180c0300c004000303622903210390000e0441c2c21407c40540043c11402c00701d0a41400203008181540c040d18000c98000c0d102d4000c03a011000a0344001201c0700e0014810700c0300312090100301290454060703707104951500c0d490301d80c5c2e14410b880041c1c40303490f1610341c42c01b0401045e080729440401984107102114003400d20b84424410b5030003140c01030980c80c002403040c3d8401c800c508641c11050f100c0905507110780d41400312103c002da82d400702030340d642c1614001141d1181d0011010b003405a446121600d0281110411944098000d042c41401030009100c69510841038494110040003003c219 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 625575818 1250 625574568 625574591
    0x1020d0206070f2003070b07080a150509041e050f010c020a170c160b030115172802070809120f0a0b1012050a0209060a0515070302011103091b060309060a 68
    0x4100320300e9040d242480005100f0003040140341e01c0901c11006609e0320440759880e00880c07000c3d2102803c84001501c2140700501003482c10320394154006000e030b41c5c10114500b084014044542c6003ea068505900a4200d505102024040c0f64030b0340c900740c400b4005800c250344c0d85120700b940074069207591400114103801001c10401000b00700c52089070108428079a110f80a030129030080c0600722642070b120a17400d503014014441c44144440f07001404c94103580305011065210800d005090b2000c21503880407042200038005420f0042c00f6090550395860b4510070420201110104605581c100c0c5107404a070000c0840c00e0701e1790a4012a82c00d00c1980c6161000041d40490f403c803020004c05111400c081c840001071000c901031090b1540e40c03d68456108000780c1c210248140359000340e0403d80700308011400d4000e030541798828000491074002180054003d6041240c50040070b500105824070500810000c1c03424039030b0706456103491401e0500f20300d510f6200c010300030055903407101c010f40312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 625577068 1250 625575818 625575857
    0xf27181404291f05040606202509060e0f040b0705370e060d0b030109050304032006030601051207140f0d0516020304060c08091302070201020d0206070f 67
    0x100c00090654146501d004160000c0345403032020181d40d0701240b4440410282480c1c4079032170503522640ca9204040701c909801e8030b500c2d40c485401d1207427806121500398450341400c10400c00c00300c0c5031f000d260b001030070107039240f048400d135601920383d120611043c0310403d88401c20b07140c1c2290700401d03112601d6442810039900380c495182090001c007036405017034070520711105240d02e481941c240351084107040c082d800c95071286d6070382d5120b510a00810520000100e290b07c909104c0310080c001081e40c203190307103504d411900107500a0714a0700c811080081e50300d928100000c44134030201c0700c160079400d006000030514021140c0b031500c20980340c004074484c1802030300300790003000403510101d80da040e0042429509400c5403220305030141c1001c0110380405076510301b030500c06905500960400746000c804841400641c1da09a60214040010001944910408900044918101698030b41952000a151081c50200344045400c00000d00c08419445080411a01010304d041c80d003030032500306480c2 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 625578318 1250 625577068 625577123
    0x2c060a03090b0103060501050316051f1101050703020c0d05040f060c0f120e0a0e0f3403061401050721032901090e040b070f27181404 59
    0x180b900006000000030040140c01c6141641d1050382501e00340b02d59110000050303c91806a542d0003414005a0312400c03c941144c2040b0003844d260040c0c2070805040424211076007515080000313500092425000c0703504000d502c200c10005c1c0341c89850103162486491039000c641c013070b2804116a0801070400e110003040d004030020340000540c090310f04a2600a8644912070142d00c0c0070716420400007404101d2010041d00c1741e100700d0010982c0740c0d24070301180302511a00c1603054580580048200d01d500317004211300448041c0b5200080c801e410814009601c8484245240c1081020003a101c000713100d4502c0e01070411000500a03000303c10312103081e00034001d203040c50401800c0c8440d400b03251581d508140000d012082c0c0b03801031015120494040f140b0f10455014140a04a40c04280c0d51445510843c0020b411480c00c00f1280c6040002c0d550954207402400c09000d01c2603002f40041050010b1206a000c459103081110111000440501920040c006002d084110203002c01520801d034554 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 625579568 1250 625578318 625578323
    0x9061e120e011a120f1c031b050309060f060f130b06070c050906031227090c07061d190503160516050d022808120405012c060a0309 58
    0xd2068800d28100f2082c01001d80700d90314410b000080440ca10041d000c00c2c00307031400b42054050601501176080300c40c00071030241d403504105951122138440c1e2031003500140141041c213950b59540d07802c000340030501e03240001d400001c211000005003c401d584034144446480c20941d03100451540701c01ca0140140307080c0321055041100004d4800400003656041800d80e8000c580ba0601034036a0001e2581d01d4142c10074100e0305c1901040307904040780510503075170000f4110010001c0d52003005c034082400e603078081d01c124998042c045041c00c1000040d000d0414150322101c2c0d455a160b081240b01d03565a40500010446426540c00b1601400030a1041b540440102c504aa17801041132818641e02d42e603207640402c0a10b40315501003241d18114200000c8190024080c1801c4101c440d10350310003410000c1d0010150020007000142c821040c45005031910030f0040c8070b034450740b5000000d49114140ca642500150790034616450020030071504000403001914501c2c1c803410615003d40c014400c40c58007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 625580818 1250 625579568 625579571
    0xa061d03070f091e0204030b072111070b090a02012106120c080f06010b030f07030b0d06021b031c0c020307081615020909040204020c0111120709061e120e01 69
    0x2088111558000014101c49041307101351144c40070140c0030881c003403070000400d000451130100f04103030b1050290900d000f40303144041c1c0c80440c400c107414040300c4c10110922458a400301c0e584050060302c0c410144e103c26124050110328403241d0000f071491811800b01c250f0507044000b0600b04003001e501c4038024042440d0860710321112410801804021440b9080c003600c58100210314000c8081030382812118604000c40c10341d100e0403940380c078007540201854105540c5003800031680c2d0325080c0d4800014005c45005a8a40c029003501310b00e640940326280c00c903072003041840c0c2058855100c03807110124141c8009501c40d20130320b08070306510520320098113410010440485107080d4141d2981514403404814082d200c07540c0b112070507806907460023544240041c00141c054101070300202003080d030301000010009000800c0800d180c00580360a1401d59800c0100720159810644c103001914042c240b10500080c01040c500d10000c1c08001901002044540c02030300a0440d0045c02a55105200 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 625582068 1250 625580818 625580849
    0xa03020c0a14210409020a030209060a03060e151804020a050d03030c0305160e0108090c0d08130902090d12050403080309030a0906230325090602010b0a061d0307 71
    0xc000342e50303100609116000c0e024088500750780342c0c3c800d022030b64003003031036841241000c0c60160301c000250090340c410310030f041e000c01688115550301c100030b03e4110059180000c0d25070500800020900f002420f00c082c980d4501450a80703540e9001c11030b08820a440ca81e0601a5551710104201740300302d900c495001000e044032981019019080503e4407440c0e135504000c10350300c03103500e141221000c2c4141000b00d20340000f028410752044004940c8001d10800b1100425400b00120f850310035009820784220300085007030105c003200001c4100003002180d1080d81010b051400180d250640500014601c1e182c80c0703a01616640148103a900850f08848919120b20303103c6003c41e00c0e0760243d03501800081c07545002040340780c06008045003444c28142001c070600a803903030380841c1c1c0e4000340088240303c0601c40c5070301d0002010120740701114110f03075030b001080d0305d44178000e402e40d1801d0300460721600c1c1e6031009006075513002200414418580318104010652180800d0804501e9004a403003070302d5211 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 625583318 1250 625582068 625582073
    0x30a02070804150206060f0d0b04030e030304091d15270102030c0d0e0706080106141e0a0801060507080d091b03050105090f060906070c0c0e240301200a03020c0a 71
    0x80c1031507491403d980035102d0395940c10082014282418121591103001460039002040c042c203001075204e88642424500006d1500c00a403464005500c0f17908240d444240d403030034008015003500b444565000003003001c2d0001e0f040400e2030b0b24000348a024520940100c140d00c0c0034a510007854802314000085540741800e04000e0801d82c84880200241c0782002d40d84191401d000032820111201035035003001503402c0950450b102c100405075071079680400d01c501100079903401000d1501c484251002e0760380d50011007019002210582c07242050003003d00c80680424045411034cd800c0740e601d10001a00c820b646030010756245140114294000e0b95170000c0100041540140d000c3d410040849000c42200c0d0311241c1d0310441101c010040340c0141001c42d04907402101c10311020ba100358070502e8003a4517143e0310004290100da40b407219040b4400700b120581c2c1c40100b8403e40d014190028080b602c400c8480e00203a180c00c403003669070b0403400540208140d03c00e41c155a80d40841c0d0060720300320607890 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 625584568 1250 625583318 625583339
    0x1a010e01060c0f02010503130b010e15030609191a0f090105090d021e0c130209040c05040518180d03060503060a05070801030b090319200c030c06030a02070804 70
    0x240100910140800004900d042c0210401c004142e480b070080050003d656004480641000d0419999000c02034620700006110f041c07290b000e07221800198074245002034610b00380018060301640a6080f0200340200314002081c2a030309104040c4030000001d01c98540010100d141c0003d20000c1502c03201842000c0340e001180c076008210b1b6000900061302d51845903611640c5480644000d80c1c00002100b80c0d244c02c80c3c8151100c0380c0810155a40290b041d004501e900c40384886120307010350b0000f541000381c48c0c548201202d810443c5400c50601d402c04002c00c001011540343d08054905130b100042c40041040003803102c0c2c1d410f01c800e8824200b5161409805408a801003e00c0381c014100001c81c20803562040500c1500d00707030f8504566900e1900c80081d0100040c0200000b4007003004031000054512030a021031500076601c11003901041080404d4450400d40384840e99045240020a581d030300066540c5021402c0b90b0041e5244c40d40e4010100038850303c40010491a000304001400c030120 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 625585818 1250 625584568 625584571
    0x11040b19090603020f0d0509120a0c14070b030f0a1b020a0c0b030903030402060703110d17070305011413060302030d0309020a1a030c0307030f0905100c03021914071a 73
    0xd41d1111052561901c10a805a01030041d044000320014415840c01308815004150061285010b0790949110442e142c10180d00404103503010461402110f020000052600604000f041018250403410910203031020f2001130106680b03001c2c01d00100b441c1c0d0200b9844130420131407511045280144040020791a03040c2e421b026070340d550380000001040400c5101f00c0c1e211b26459800b07585180c0d2646d00b00001074000241c140c08010240e42c0c0800002e5003008200c0302840ca50b1185401009000f000440c0110020f007a6001c01d0304240041003214410004c5c561800c2044030440c2c15942d10311b6400d4002c054a9202941c54401c112080c41c4182d056400f14108034000d5403038010090b200d0030014600f041101014034205000c200103448020304601541d00407002e4580461000034100341c542c26580e504000343c8041d0000303140b182d8000c40a1160f4407202e8014101075080c10391a850518541401d54400428840da50a043e80389004600860b08440d0340641e4401c01074000a1626008010 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 625587068 1250 625585818 625585867
    0xa02090108070e12073005030403030302130e0109050118020a0f11031e180321090409140105010501020105090a0308010e0403140414010207050612150f0d0f020907080f01060311040b 80
    0x1545083d40d6a001b070b81c09000540701e410800551074940355640072070007984032020031041c9010180300031a4841800e20b42500034540d012010403654100380c0311042003c101501d030742c1000d00c10802524110382200c2c000e80540214280441c18201d000b1a90b421445520155540c510400301c0300c85c80c00600304003600f4085962140704601002d004203141d6075103c01540c04181b81e80700c00c10000b109486000920160b44080c2004c60203040541d0762041e12101003110241c0b594440b0018005540c0c240306255200b0002401040c0d603186a840160003c0418005c8008420a000c0080c05150150840400080c045041c40b640c076556081c500d450084810700380e40c0140181038000032145046415550942c94248440341d098461000424889480c03070f01c03040d004244105c2200180d5950007a100d681c50185502001c42c030080c0c410410b1000d4010200000d001e11041803154440c8000070301c07030540c0c109042c0069100c00e842c0d40c40c000c5001d035078480d110003480041c0402c00880c1001d0034082082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 625588318 1250 625587068 625587119
    0x41a030f0106090e070515030903042705060f06090904050a020901030b04030e150a03090510050c0a17071b0503040306051806090609030f07060f06090608060a02090108070e1207 78
    0x4c5000b492038644905218403640410103600103000c0340a030b18020340d084020002160301c0c059a56020f0030083c190740046080009000c0c01007600074040d402100c1e40f11b0b4045480741d10100440c0c0c005003c038050030002c0e0740030781c01032800681040000c008261040e03400902141c45036030360303241217113032548100c0b0104e0006080c00206105810070130b607201259143c1401d09820140e14503800c4000f050000402c0c2c0c0c1c070340309000954400ea1143d1251501922400034a255103502c1680c0250521300350201065401006004000308560b00401d40c0880340318101075440440018103200d8594042ca4102400a600c3c050a200b000d514400c1e203200c3d50302045060350312540d29000c60304c0d16000101ca45605030b0300f0400965042d221404020001144209400035040001d0000707001103403415001070070002c1e69000103004c00c180820445920520340c80d8103514000f00e81000070000c0c2009800d0005228000007810074070351300c003003000348000420000c07210056641c0e040e403036020903036014098084 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 625589568 1250 625588318 625588331
    0x1e03040815130b130c0303080109150806010b1b030c030909221220070302030106210201030504080906030708220302030304082104030210050a020414041a030f010609 73
    0x101c0d400720244a00d2801041c0004682c440d1141e11102c00018410500b08082e040b50600140000f641a4003450180d41d4403002c66040007040ca040f101c07260500318400d01aa001003000312000200b00307042d60035000712141c86005501d81c04a110401402281d45404042500d80d0003d0002015205050046546800580707481220300c2403804900b0341483c960084041c940c1c041900c0c2d086a42119600c2d10f070100d0825107061100b1a403400c00b00285820350012003040082d4a000d024ad0005040083c8c002c1081040b0050b1100e0301911102c00241499160760000e0f040c41240e80c20b640c214500034100079524941004003e000300b404075030a410140c124001d8000508244548001590307158004500d580c85039114850725402510050302507400c2c0c800d003040305103204403c41307000c3da01c20b40041005041d89180c60059440c0103100c8a41036106010801100015000c04900040306a4002442c00b0b49080c00501e1080c00d250041d405120304041c20310300a105600c010111403203400c081044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 625590818 1250 625589568 625589593
    0xb1b07020a120b0105060909040f0318030b061201020310060305041b061709061b0d0609141816050607050a0203120717070b0f1005030d170a0e030406111e030408 71
    0x1079011f1b00540036008201400010001074007000072401c1c080c001c1c28100d01801a045850342d1021140c1c1080301e0f81c01020782070084c141410320000c504171160b04002d40c00d600d099800c1c07054101242c410700e010540c40b000868140541116000c6805149000703100c800c540310030303010300081048022041000d00b041e00142d810000491424081d450024607a02600c500415010304d41d0414000c1207501941c0700400200e040503031181c0303040d504170707030345100590320b050900200030300800010f0350410741050412400461044c1c0d840c0c030503580304913115500d80919040c980d14144c00c680c40203415125003400080c00842da180505a011b10400d00809420341000f9041420b00410600419000c00c030808200c81c0315242a40303d900889603404a000c155503600080e00d40358175540e0380d402060451862885400084083c964444d46907902844104840810baa5807071049100d0f46007004491040104844410310884098070b507140800b51a40f40c000981e40c0c2c0700e611a11600520741702d4000075400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 625592068 1250 625590818 625590829
    0xd0c020607180504020d022205100509091303030f0c0503090c0d0b1315020f1201081504120201060932040f060f020408060a0b0316030b1b07020a120b0105 68
    0x215184a50418002c03a15143c1444007a4001400c000c1d601da409000c64036810040b8842c032002d0b0701800281001551611080c80700e0805883c10f80c80401c00200032013040ea850301c54900d900307d000b01d04031210511081c201280207007900101c1103040e42c140540107003140c4e070010180d801091004240c4114020101c01c1001d820a90b040040038004280b001850544903030800d000c985010f0784003a03242d003000010300c9080364050303d00341c2c00390072000c03402d10392014000c1589400760807850020809090001c01c14172134180002c0000740449200b19503034040501c00e40015005011041d01408220000102c0883d541c884c112044c40d065440400150311400070081c044c02103410200c0c17503068141c5c1740c440d42c01414984a001880b16002c20000072098000c2221034131805800c4d034005130140c40001050300f010148a941807909407105002d10206040c0b20007d90030030103032110142005c01c404c9440c4103500840d00c01035444140d95000250540d4103140110f8070a20480749031f403050b03888104100c1e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 625593318 1250 625592068 625592087
    0x1209180c0e04020c07052d040501050d0f0206040504110c0f07050d110301090b0103111011030a0503130203060106020604120804030e01032309071703090f240d0c020607 74
    0x40c002010034004141600b050f42c000c0400b02d402c00d09031204030b600c64004c600c40840300c100d40b004204c8061506942d04c8446c1c4040704c00d03c80304441c18049545000d0000b0021880641c028003d100643e0a40301156a0744044400404000e031003403081c058030480c0142290414038144000d40243c4400321190748002c515041610740081c00307061a50110307112583c2e001d0074042456050b650b910365250104500f141c18900951054030710b90040c51940d000e1000303611518000c40c1c01c1c0b00002d0040c205804000c8161001051145002c40e100e80c0c40c8014031102e86107a08010b905070007080008210141e000c95094451801480580210003609030301310f40d034080440d000340000b484031710000076661194010032100c002040460600c0800c0700c94031612000150f8402032164402c40c0200325505182d001c007018000c40f40040d605001c00e010200d59175500001049100300304182c1014405d40d6020300780b4607403481c51800703241c580141045900040610610001c05403040000007401507100e0507180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 625594568 1250 625593318 625593341
    0xb0112231f0b0307033c060506040b070204151502210904020c010e12090103060602031309020304050f0d090e010b03070f0e1c0c03022409011b120918 66
    0x844901c1e2a001d094251500090500c1c1e0805884040403000725062282100c282c020307a40a00030f5085100c19030070850540b00c10001011400c0150411007661303014281c4044600601d40b150b60b54201c2d1000030000d1412819088017681442e00200c0c004001e9048101000080d400722406543d144000715006144880c001841d5002003025590030304003078001d0102519040300200f841d040d09401d0b40c0c00d059110a00480070040851580b40c20741c2e00d409031500414490016502c0c0413201d2200e11306140309401a0407041c3c1d0000003081c2082010069a00301c0c02d5014141c80442d20950001403100007039205850001015a00104085005404070790144030551142594913001900a5944821843d0303525840483c04440880546000d9001d107481840b5000c103107045815441041000204101145a606400082500010240d10071103203002001d0800d03055490f4491102941804a803034010003206180074a012200d81200d580c0b03081e0780d02107020440c0c00c1c1d40760981c00103c80041009 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 625595818 1250 625594568 625594621
    0x1080307030c11120a060c1d040207290114040209210111040b0c0d0905031e03071a06090c0316030b1512180712060b011223 55
    0x32500007030203400c0c0e4020040c0715240a44690b4014030000d01d0b2180c0c00100702e0100e0304402201410440180b140d11800d0106062028280c46040c08264001d44050352040c0502e600007100c41c02c0c01040e542c900703807130a02c941c03d030200c0001c1680719200d80301c002e100c2d03000804014051307001d82d858507000f074401110001c1c1c0060350303454138038469014641a01c20007010355540e94502800d0311041b04024006009600da81581d83c541d00f03014039181480700f4030398008108400c0410b200c95907000c251200f0f0342844003140c254a010780c1c01d00174207520500e20014940c0b84907210030418100605100340c0f05640483c1d441c03460f595100139041d50f41c881141c4002c8800c2c200b90303d0580c030a02a41c00312a0070000648424041c0c501c0c4c00161010b45e000102034008942507a0422024402128000401408040240000525081029801c1e207a5184010401c41d01d41e000400e55074401c0c1000660035140030f80c180a8600d4070141414802a134248080c107242072180062003403c0741441080d60484003616 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 625597068 1250 625595818 625595827
    0x14010b13020304060905071202011211091005120403120f06061b06020d0c0c0c1e06030203090f011401150305010308030103080a02124b03060f03030c070f0e010803 72
    0xc0610003540b00510485005550f04a0100459420050341e0003510742d049440d107042e02e00f030001520220342e22036021840d43c14610f54a80d07414864007903c0c5000c03015500300101c1d44030030340305492034046c0d00c081458055020081006050340401900c903407144000040281003081507515054594038096040170415192148040b00c0c0c500c920051524000d840060408907035402c4a401d580180c0800d00024200c9441503040c44000c069060090850b00040705030a2403005141d11180c1c011f10070701c001d042e800b02c00903c015806010349100014040003c20040400c01c502c0c42940300d0030b002e10580c0e44603a0081660450007842098181c0c2e0300211941c1c1168a1a035648510764031114440003140104110810f031912202c1c06000d00210602c000f032400c10a51500c038a03450078510368001d0601c01c103541d01c4040150041c401c000009021122903982d81c0f00780210b88401c8402c4001d0303401d44030014444d082da483c003040c2102030f42e200003d501c152076030312a00c0d411642001c0c0a0350105410401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 625598318 1250 625597068 625597099
    0x60507081009151703040504051009151505090103060e070309050127080f071b060f03021204062004060e100e03071503110f030a240612090803070c14010b 68
    0x1310308034001032049040343d10309170300c0e03001082c1a40c0050b550429031042ca013800340004180c85c0100c1101003803050182401c540780855141020901001410a002001403500e805074460b80041d40509400c030100269801e101d9802401806d2120080d2415481c20b44600c80401c000103d1901c10284419040b003240b0302c3e91503180f80c1344c0c0401041da0686030104401c00004d1480c42035500003040703403800c2000c02894400050030400c0340110f0700d000c1500c10003204075140c5001403201c1e00a60070240005031014044032583c3c040310f06005c060b00c40f282c0400d001901513840b44c1110f03800001a90003000002031a10305440d0107400c0d0100030341c10f40288006112213064652402000350240c42c0200c0d00e012101013114a5a00c034016050741184000300300301000e07045000b1044181525007802c440e0f0b212140d04400c500040740902d200708210a041a01900004d403c2aa00303c1d030040c5900d030b45ca09185001511000c548582240c2c0070007980e03407143c5642c0040c81415050315014241103030189042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 625599568 1250 625598318 625598339
    0x601020a170c01061806080601030b041b03140c0102150907031b030f03091511120a200c0114030405061305030d0f0218030a050a060b0d06050708100915 67
    0x14003407000200030300100c00111803d0094074000c01d1100040c0307031702c5104c0780c80e034000b96102a000712056034407100042000035400c203e840e90094001c1800500002c2c05010329009260340e40c8040c000d291201071321220701101246901148100341c003180e0b0305084417903610204072000c481a11080d00544801c001013808960302d201c000400f1054120301586a680e45003848240c00303010b81c00a0954001402200030720205052661802c1c24100960740910f070b03116940d4401001c540701e507000080388040741e0502540d807040c83e418114240030010110a2080c3d540e5500c0501c146002481115203c40c0440d056070491b40203640000140040788c0e14118044400c0240e08421503451204001b00341c81007402d8820351031075100604016070346291000013139020640720b58205109070000c20a010000c0d00004102d5a201d900442c00b05096600c64002054100b000c0b402800450810041081056001d10b10310310074403001c5240082c680c1c07980c1d1550300701c80e1010070b0090307020059001485043c800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 625600818 1250 625599568 625599593
    0x10c030519030219080f13020d0b0108010c090e151306050a0806041208040c30030f0f03060b07060b0a0e01080106031b050108040221070902030105031e120702030709050f1e0601020a 80
    0x723032009c82014030541d1103903c4484240d02164084e5903c03074540030315540c0402e81074010151442d0802180c00c21070101e508051020b00c10314812000019079070741d82e40e0960007403030007000c0c010254041d4a6a80f4015a1a01000c58007190450061905a01513502540b4458012504040030800060070640882d4242c0026808840c0480070260104400714800321414005d40c881d590f0000210003c4801030185079100c1544c0041c907045c0b25061080340906c0041d507401030341145010440c0842d00020458000c1640c00460b582004400040703501c0780305420500440e480303030702907603104004a600f04c3c0c5100d00300d000b070070300080503440400e0151400c070300c1c007401500940c503240c4540d03803a500c0a01e1a18405921005405801000400184c070b014441100c00c4011500410703080801c82d1401307500d074180503603079030804103001c112b00040d51070410030000548403090082002d82440103100c0f0000c0c07000c5500c09400d140100408500840190f009406810180c0041c0918011569101070a01c031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 625602068 1250 625600818 625600823
    0x30a1b0309031220030406170c040902160506010f120f05010f0515030f01020a050301060f0c0209010303080a0e1612050312100302010f09050609010c030519030219080f13 75
    0x20458088080b83c100500400040a2901c07138280070302da40f0325103942c40da001c800100110703041804100500c0390400401b4000b85d140002e1405603903941c0251003041e00485e08560300c654404a00320320103d020604140c0658002e1007100c032075030780e14003420800c0030301d502540608175200c0081c1c40c00203414444220341148594004510031411181c0c5504803101140d214402d41405010350f21182018408441c1448400000b94a0810151005413941c072061040750200092410a000c0715841800c0072400d2650040c044004c550356410300a240307120640d0b01d42c3c491450300e03441e04100c40000840b207001070306a071030300b1030014500821602c100345200800d544500080042d400107058021100c1c0c0304908406a8461032821030000500d550060703507150301841038440341800b041d55003000b07646440c00240ba00190000d60740c0343c05c1392a402940d11005425980c541c4400340c40340c058019068001c020b196000780d40e81c8401c800c4070201004d5440c040c040803180e010500c46042030050505c45070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 625603318 1250 625602068 625602077
    0x41a07020309040e060a0c0e1f1b0c061d0108010e130b0112050c0a1a0703030609140702010b0303071e06021b0f060717130501061a0403060b0102030a1b03 68
    0x2841480820b003600c904440c4c1341c801ea0802c82c104101c4507202e21900e142d51036645451040d4a002a020521880070078a103101c1ca03881c40718400c10603601c00c02e015102c180c5101a1020420114604139010842c0c90060f038010640da088001c1d10401c0e026141c6000030016580c00d0790030707440c1c07889401e035004000e0502180d0641e000e4100e008141030000b058002e14400000c065010350500300700e8101344408080074801d4446040800080703801b4003041079442038140101c1c2d83c0e0201494103400400159200b0f94521341040903401c3c0f1510340300c0d507061083da801c0c0c0082c0f01c070b620f544040588034460001d004004425a9010301e00e102c501d009103548091003140b0041c940384100d0019103101c0443c5110003c9a844031400111b810b600b80411500a0000e0520b0030787c00503a4400081c004100904100944003003030f003000c042c44825000b00c0c0041013060040c100382000742d0301518070755000340419207000703045c050004001e5100104881000d1825580d0501c900d414807006800d001d4034100550400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 625604568 1250 625603318 625603327
    0x7032102090409051624030f140901050403120213060c050111040e01031a010605030103080702010e0a1412060105030717011407030515010c08090609010c0c060503100e041a070203 79
    0x3502d81e44a5181c00c2c80c080d000500c16184c4003076403010160308a401c503c2c181000050310f90340c500204110500c80c401c041c100403c0d00d01816000780000d1030f9086803007010201c0313201070041540d019400980914000d030740b80601c29060300306502c283d100300c001c41c0200b640b5041080080310300c50300341c8407520b92142d00045101c40390790f0540c51140d0002c1d0441e2500c0d44d0401c00400400480c060501d80d55007082080c50555071504030301414601051002030420400024000c046a204908c0041c2482c00148141a101e0b201d0350000c03c504010300d945030013160b0014131400300b08070005046040b900010010f01d0084c0c00c10203c8204021010342c411010b40d01c03140000c103e1901042030f90300c10225640d00241c00d2500740c0261404007031400b802410302c8003000100b40440c0e010422140701c5001511000d07030710161800100d07201c1c102c03941d01a0412502000200d00302c0e92010040d40603c0440d00c009240316254a0f1403440d07e107003942c0052030100300340305c0c070015007103101460780d0301400c41c2c011b41e802d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 625605818 1250 625604568 625604587
    0x6090421120504060b091320040e06180c0118060e011e021c03140f1e190c08090a0b100503030a110d03091e020303190905011407032102 60
    0x69900550302100c41030b8481d800c585e0a801d000903080c0d4090000d110041a04184d926920070400b41c1c052659400700c0c08000058250300c82d60000d140010145044400d14604000d03c0c10341300f01035118164150003604100061907125801d641c00391900300a1013880b10b40307400800d8400500c60358406040c41911b801c04241a590b00a12010100150300a401c07221014002d40a41c1c0100f05404400d040c03800115512051000340d0103540700070740151064060301c0d001440c1c0c102d04000e189060300500c07540104840070494416090080217401e9092204141045040c1d95140044864040c2c5034807014401c5d001c10171701c01103a50840c440c00380c50b012864a0b1400f081c115032040d440c2902080308502004c40c584c20402c802d41500a03135140420002501d907998046000f0000c400094132034850107580c05541c1c0a10403100064a55400c0d0020030880c0c06c0041c04100040c80fa041c04a00085d20b103203800c180610484601c550f050b40c55401c207801000d15000d800050701120390100b0303400e000b800b0b50b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 625607068 1250 625605818 625605821
    0xa020f27010914031513210905010c051507110a0c050a0906120314090405040b0906090d09030813080d180602010902010819060e01080714060a020c130f230609042112 73
    0x580c40b01c1641f612151444440078010401c2580201c0c1002010143c0101080000c40c03c0b070304603c00a40c010b00251200740c01103c0c14400140490300341e01495041000f085080041c61088400544105800b43d9441d01c1c50300440d00340707119a07804801840c401c80b0000e8030031407030100d07500c1544503102d0908845401150490714101c0303040f20a60415024012115030030807159034002100801448a8401c5142c014441e0805102c024140640883c0303440d05c13900f00000090207050b420302190b4103d205103070002c0425082103202a1041c0c04083c01299007032040c042c040d170846c1c040e155440107855101c00901ca2425080280d50784940c2d0794400b00b031a0029150182c000c0c1101802801800c0c01d014001407015031960509105903c00c11501d000d072a00810f0381004100304481d140010b5011802410290070400d402c21031440c5455401c92900080c069607004041c003400c5204503654840c01031041c2c5184c01e503005482c074405c030001100c0c44145d40c1d1118500c00024a010070001821540f10300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 625608318 1250 625607068 625607093
    0x2f0307051c0902030c0d030f050901023a0f080711031c0507030605090105130914160f0510090302100909110903060c070b0a020f27010914031513 64
    0xc015030300d46864034250701d4101701d142c034001070440e103004000c449550003402d21100381c0f28880600c40301182d100d415038003c0c0041030b2510340c07101d40450403103100c5581107400d4095886a0801001048091009910601d42c00d002d00000d80c68014042e04c0b088400c0c4c030702d100603414607c2e69201c2044001c02d620742e020640340120003220404503590410710340180a41d02c180c1c0010b4001c403005001002590b4500100711480700c0341460004e5418464246689040c4170f06009072005d00c2614450520303440c20211850031200c04242c00c0711220b0300d540410282420844091000558400042c000351422004840c1c9514450804904545ea02d0745860191407055607555040c00d80819000303c1401c040c0521b6a0201d056070440b8504522a69000301940011380800b085a5020031091480c1806000300c840b43d0140c012540d88980704211103680d002c030190803107030000d480b00e08000303230280e030000c5040076200b0b00a01800c011504441c0181c184d5a0003802d0310344481c0c0c2800017a000c101c8038080321 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 625609568 1250 625608318 625608367
    0xb0d0b0d030e0906100203120a1d070e0a0501060c170c19060b03030405130b01091815050906030c150f040314070b0a08010e0603150108102f030705 65
    0x40014021241001040c483c02000e09000e2905984015500360b80401280c000800810380300c503041d242c038400f6400910010700c00061108216240c0c843c10b84002800d003003183c1080d104640b440c0d440c09a40c00c1550b10a01c01d80300421820310285000030703035903d9490f00c1134814020980c00c0c401c0b0032003060b1605030405c844120b502c4c800904901407185034052211183c106400440c80c01d45002c010543d2695440203440350030b90b580e005a095a8400c0a00c10300502140c0082d41704100003400703010040889411a00d02c078000c403400040c09041c1301c9403c41c800c0750020003030140e800b07000082c000c803054131800340080658204140307544080d0b210040d0015502403901c010909101c1445989403c038903070002400100c061085607c0a68007440607030546102c081c0b24141d07911440d000c2881c00c80d1203141d0b40d10031098030001061b1800001511484445600000d0001e0782c0d1450a500c902030a88801c4060540e0001038040c110000c2c00007141c000c503084c50000c0c03420518500e407013038103803a9140d103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 625610818 1250 625609568 625609577
    0x1023a1a040b10020c1909060e06030f060601050d020d0e01020c0c090a0207020a090b0f031209010219050d1b0c03050307120318060f090f051e060c040b0d0b0d03 71
    0x11050305040c40d1140084000c0140e039200e80c0000f500201954820342010a20320500c0350a9071810810a405100b40040450f02014400151100c60034a130300ca0342114081c3c0684240100505400700000d2442d0145106031195850003003104482c0000e544501c60144c401c544408104020100900c0180002000900a007011071100410411210405000908128010b00462026130368030212501181c0303000700001601d052400100305075082d1860781030ba141c06034060701e02c00060080014913400d4805d900361803019250900c1011b50b091006005009680f120f402640168001c800b5100d5003602c0003440140c105482c3c2d200c00c80c0010607081101d25801c042005010840110b0403d040d016440c1014010300f0a6561028035002c80d401000c1d005e20740300c00c1400030711001588550303c0782d1341000c0d07110a841d9050500d180d407950003100062000480e00d0682d180502d0114146015540c84044d561130903140c00410909034010101e01e0140e1507403000215459074600c00140305282c42a00c0d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 625612068 1250 625610818 625610861
    0x1302030a120917030a050724050a0c0f051801090e04030507031803050d081b04080303090c0d0206070f0813031b0602070f030b0c070203120c06060301023a 68
    0x40040101c481548200c0540c2220060007049010201c280c501d100e0851901b00e4960980741840b04040008101c881c103004e1494149821405881e007003148203c0b84100107000d0810403840071503004031310043c81c100141c8140301c20414450009407142d2500014904150386035100c0d8541c482e40c00007074500b1001b1400015000040542280e1039a0307142004441c10403203280b80da182c0d90746440c032422075a810004502c002030070380c1c44e00d002041c411041b100704480d26103840300415982c2e41c1c0269984910f40c400c081c2d40d400903150016541600301c1d80130346621f040c1890307640e4484801d0001002200e0a100034428030803107401030402d407001103000d002c00c01d440c0030b03941c0900d174205915904400119040301e09c050040f0030440300c0c11801c0300d6005102c1145952408d40410703c601441030002c1d0f141c0036150344507a504090801900d824000c56050b940e40361602403c250803031188644414144071041040c11548021039103481c00342103141c605003501c2054040c04070440e10b401407480e001428205 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 625613318 1250 625612068 625612103
    0x909090f0c0b1b0a02010801120c0807060e01180506070f030302040801020f0304030f14031807030206040b0c0d030614120c030d0201151715130b01030302011406040b0112051302030a 80
    0x2001e05190b072604004d400701d144240c000800309601401442e00d1842481c00c4ca208210340c260740603000b07010f500240c036442501d9540040100c1c1321070007140d000401442c05664055030034000384080ba03800414003031501d0880e5480d40c00c1c544200100303800b4150300b0322000502103401e0009121429010f0405075982c541454041e0000b400f2501d42000c004480451020b4541b00c082103a420078801c42104d03c645510303807189803910708075070402900000301150004041040c0340240605032000c500b510b85034001c0420840031200e40b84200c20204080c0401107905007450080c465045041ca0b05036203070404840046460310100c0780795200183e540d0503040035016024541c01000c2c10f24040c504420000891009650303501c11460040358044400101e48c100441104140440b580309103013002640e56414064000c2506002200055403e0400901203182c14401c0000e034000507140e07001d220100700708044c01010024943d215681c1c65010400150750704010002d1100d04c80c01c80000001c00c0701 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 625614568 1250 625613318 625613347
    0xb0306090f060102301204060608030c0c06030a0f2306011103031605041a03060405060a0b0a0309060216080316020c090c071505070c05010c050405010909090f0c0b 72
    0x1c002a501007605000d10a45070ba000c9a40000c0000c0c0100b02642c4801c000140031040b5007080d4900702001e000110b26074142c1d841e5000b00e11507801303414100030103561a103095440344180000301c10381d50402e0005d034049241c40d1000d907030003000c0802c0000b1890702c401046001c55802103114600789080ca801e9800c00c00c1000c10240d401402860a1100070202d120400ea4078080036000c0740c1003617803071805050940c0c450b4054900515940b0f0a000c807a01d024000c52001da0700a4070790758001e9041000080c89414481444412120521201890402030880807001441244002c0f1100f1b80c0800118000c903186110804010740500000e0b41d43c0e007094260f0200d10159000c0210540d00040d081d0340d8650b881d8803881e5484188041501c0d07645165191490b011980021131b0854103180000740300b117040c0e1041c1c01a030383c1c9104000030814441044826070f03483c010786c822580041c42c150401d12807560303103422140341c40d0310072980c1807800085507895004000480c1c0003c17402101c040b032618a0030108 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 625615818 1250 625614568 625614571
    0x3030c0e060403030216081204091d2a0108100303050306010c20040b040603050712060b030102190e0a21050c09010312181203080c0705011103101d04030c0201090e010b030609 77
    0x88030040044014401c0023030f030035008600c6101115965081e040302a81d80c82c180024140c14443c00780da01c1007454000b00c1c07850118124401c41110601e00011031749500816000e80210f04111011031386a2641c0e5084410b0307171005190034100044481a00b0004080040074400103042c50b14181e4441e8103502844100c9000c07030712880c865800c005041000c107102150361001d9070100980020003c1c03141c18400d000d00b20891689805600c0001c01107030440010103002614501070380c64800d04004101001042d841c00d000b0031031ba40b02c4658240322051052031011310340300c0c8a90143d030351040c040800980c0043c403d9009480c1ca040c01132810f4070f800d0780891050301d840d00c1011095407040c100103015240c41c0001c4002814040301d1004594215050015201d080c0d510400030f01100c0c00f0719251800030b410594010260640c90440894000500b034201d41024503405203004c40d40da125101111500e07813000703050f03060003038125002c0751203001926443e003e40303284807020b07640c0d040102c20300100440 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 625617068 1250 625615818 625615829
    0x10b010306050d0602030705073815010f0e0405100611070308071e02040f1b02010b030a1b0806012702030405031209030d0c08040b01060809070303030c0e060403030216 74
    0x1421505011660b0f401c01030200b401d42003c03005850f90381d5607a041c2c680340705042d070181918030044420460010401c0028402c00f0600d492040d10f1002044080d1244106a620141c01d485ca02915040e5501c2240d808a00361050f10f8901507040000020030304580341134502c6040070820040c1842143d400400850380102240003c010881c130f940c54101d1a4060010300514a5000b4210505c41c1c0c0f403000440764866400820401c100c1440c901444020050218070032a40e500030b004801c0c01c20300600c1030140ca00c1b00623015007010303001a901d88000380d031410305552040c0082c01c8082040503040041c6c80c040d0000210001005d001c09007000c0c500b0b5000400c03039044600400c02c0100080b000320550382d40d401c0254019032540c581c5800c250071402810721501000303241c150240c4400fa0320850f601e002c1c900481081003e07981360082110409411100030000c1d90003410b0030000240320707910442d2042c00610744190f070880c20600140e155401940190010307804405601d012100040c0b01c0b03c020103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 625618318 1250 625617068 625617071
    0x7021306051005030a1103131407090e0309010f03060f050d02130c0215013203010f020a0e01080906010303141c1104050310050601082d0726060d120c1202010e010b0103 74
    0x281011696640c000011001803040c0c9c03128100d1040c0384c03800c00c891009040c140d401841030046046d0b03a2680d0390805940d4500141040130310b403078030a00911840c000d0750010321260fa1420b040209200d0b001d049141b0407038010000c059001181562485460742640403540a0300303800c940303100054030051040e0418002c80a002c142003050300c42c0280800350b24151103503040001103140d03001a0050110741c41417060750b800003c203600c80c40d030b00c200481c84400098a4942090300d500c62116512a002d000080204212500d64442e850031000644130011840b159905180b01010800c0c054445101c6200c03c0400c021400f8091843c06000301d201c8540c80110411503894101d000034400304002c0c00b03aa1403040114160340c025681d00751456031a8a210200d0382d240d0034006801030010b03108220300d46110b1410500e1200380410940c0090113101c00403d103004d944c03c1da8880905d1502100907000c02d10484004c2c080004a241020404204480d000040c0c6111784000507820344213051003040c10103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 625619568 1250 625618318 625618321
    0x30a14011a0403060b01051905091002030c100b1f080a0c08070e090a020c1203090c4009050105060f030a020109030f050c120c18040807021306051005030a1103 70
    0xe001c90000c1d10700b00c80d00100081290344030400166428451041c0d40c08040d0300700c02c03095036a00e40060042212080a85420340541c0e41d030a0101d850380035031a003128081c1c2001c0445000681203801062400c50014080c00d803012580d0a00342c0c0c0700f4500803056001c10310f002e0410140c0280c51241181106003800c0076011854105d40c0102083d24441c5590301c0713400c2880c0840e84006841c0d040e141030381603000840e01000180c8541550070b4004a49111483c4a400c50210311410460428200020300c41d003140b42c220110608017020080e50200c855100500ea0041108460980240031065009100000b100d040c054240131010500c03e0b222030203948072918071710050340d110034510112030300104000080b0b130007490030b507041c40140e58507140d10540c28640150000c8022400f03900a441c111750002400070310500742000c1d68070454000c0c011901c24400e500150500000311001000f0000d00000c201c2c0e2110001055410044c40d1031001441c040100485000c091180b8800d0145612203581075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 625620818 1250 625619568 625619609
    0x2071e0312080403140a1d010207031a06010e0d0b0604060e06131503050609100e1216020112050c04090b0612130f02310606120b0f0402030a1401 64
    0x1292101c040070009114000350500d0310840e00b205920395400704d425520140c82100078481d00145a000f130130503031b030300421180b15070001405000b01c0e075210b140e546410400c19001c1000390001002281071124130004007290f6070704c1072481c248151060401c80380c5401c000342808201c3e034203600040941d62010052103000d5840150184041c80c2c03012002c10720001010116914400541c401441c80c841c190601201803004100f01c0808080c0440403c80d41809060311130f55880317100ca070100300c2e80e41040788102c8100000085c000403801814000761800d14041000d0843c1c0d021210500305890101d814400501507010380340104c07100b121081e0804541580105c2c40410180040300100c44011840b020020680d01444046400418a840e030068800f402642403a101000c02840081c001c07078141c00c03080038400c5405542039543d1f940340004000aa4100612170000655481030a003034180d00a07580b9400218401d007003aa10110384a03000400c18800300d00d060308064100320102000546 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 625622068 1250 625620818 625620833
    0xa080603010b0a0b0a21020c190b0105010c240b1206100902090a1a090a080114010314030c060a2a0e04050403030b030a0309051e0a180b03030a02071e03 67
    0x1a44c1c40c054500782d98032504079050b200d1208400030300b0251510f416420120074550ba000d41143e400c502e040d104c1e0b03074009003480c1004480d00b00b402040410004010301140d44100d081003682c51040d0803d0080814038402e9011a900d0070941c01d0700580c994064182c2400d00300c03100081c40c44480014011030800682c0828036403070901500703a040754041110403059a580f24100000c01050680c05030b2848441d1140c12144e000c443e06500580780a4800142c01c00b051148546900840b80343c00096421503440b8010900100000c040c81e10080c800b20106101c14400700d406400501d200084900f040f84011407290070509040340718520442503100c107581c20020071110510111070008080da218942500180b00981c10507405210301076802c401c1540000d0349105688086820031401942c0c0d4407503040102c04611095044240c1250410032070618501080b00900d0000c80410382c10a940d020a1440d0009002030b80146d2103140100901012031490300480d501c0d00010740e1541381107868801 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 625623318 1250 625622068 625622089
    0x209061210030c060c0b0a0f0216060212010e01030f03030509011b0905211b151602032a0d021813060e0607050f0304020a090204080c09010b070c031205070501020f0a080603010b 78
    0x100c1054407140f49030440703102039044414540007200403921004441c0bc00302c000750403810000d0040c3c00352030f001041001924060701c0c12261310483d0000c0c00e40d280c0e50110080e080c00360007444103640b00d01c2c5801c664202122518030200040da9160700f050324060400400610b084a540720316030110290800240d000308446445a659803514001c40c452100491007a440b02c0c00c410112803030100f901c400100f50140081c0030305000301c046620610700c401d11020340b110344034030b189621000354525003542d04010040440044c0000c1000512501180c00d403a0a40d030102e0b600a450128545050100110b9101e400a461312032401010f0380e25012101800f588200001c214075240302200040440da02c070945a03000d0300901c141035450b1076071440303100d503514250340030b09100d941c88800220310400703440213580c001d0340c0100a10100c2865034803030250325484035481d10704101d0100302184c0810303002d00043c050111044411a550b00190b54001c211b1800940350b0b0340b00f64145039410314541c2e01d429421 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 625624568 1250 625623318 625623331
    0xb0c03121e010501140c03120604150602250b0304050604021206040302030306041a0a061107060e0604050d170a080103061d0d0f03200712090803030a0209061210030c060c0b 76
    0x5842510140c1c1700d001c45000b4200d40001d030b80700000320f0624030302103031100c903001c2d101c20b40b4203101440b140c051085803a4014020200140d01c565500c10784d0f0102c0c1c0425002e00ba0240040c81021501c4960f02e90050b4021541910a0780c00361081c8001c5080c0048243e8000c40d000300034052078140380e50004d44030322000c1e00c1e580c4695120490780ca03103443c0440c1041d1020344000c3c100c02c103e07503403400050201c0170403c070b406401c0d01804100048590041422100c0c1c031000524192070507040004000d440e5100000c20303078121500b0901409200300030802031050081c3c0b52600c41147d0b155142207020740d0f919603c0814240006071040401d0240050301041e03410007400c3c046948141c2680c11001005500c00100300c0c000d03156804080040a00004c10f001c42c000d0941c196180015001a54950b4a92056603d01e9004000080038085607501500300100c00801407440c12001104004520360152076100000031200410005c020b211060311000b00414103181c0a202070a850315030300d50b0002000f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 625625818 1250 625624568 625624577
    0x9010e0402060f0904090f0201080a02040b03010513061511060604020c1b010e191d0415090f0c08030c0c010201150302010e03030c030c0601151d06130b0c03121e010501 74
    0x181030329280d80344251380d00c0b844080d20070090440302c0d04041c1515520b005080e800b050000000ca4140021402101c081d62004840c1d545507034030b04010b01c0b91520406a40c0c600d8a40d541d0008908604002c1603080301444940d80e20b400d15190341d040d942004c001402e031601c42c5104009135005007002285800c512000060100f002000c101c0c010b8801c080d5000703400b03030b010003107000d20b11000f400c00b0210021b03a02002c4076103156501840e150400d80d0307400d84018010384c0300d51004802c1b0700702c5508010a02d43c424182c02ca50302d400d07a600c0c0003210b241c50b001000d1075040400c035105015410440c403403200c603091009128000b42612400c01c24616400040d0400c40c0d005425001c90310300300202c40e00345600908480e500c1c0c0054004640f00d40d001e001c0e00280003401148452820720600d4540008030284100407080110501003000680c00b1200d07140b0050380e4042c1c0082c49406c900e01600711300308001c0c040c56a503241c0380710300d4184041c01498503c20381084c05181050003148054503066400030b003130 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 625627068 1250 625625818 625625827
    0x33040c0303050702040e010513030e04060e011a040509150909010b060306040b04110c010606110c012a02030718180c1a13030609020f030a1208100e090303100509010e040206 76
    0x445c014240b8a00400c0940d0700300401d00c42244283d8404413000c902a0351117082c404801c1d4100010b03203400340b02c0c080450040780300601c5010802c40000c40d10000d60302032030380340c9555440419102c5204840400010903504980c4000741003180c80c031540210714100030804004400006050f42c00040e110760700131a81c8102c070035920380b00c1b6441485980c5418074000d85030400e4000080c060981070054400043d40c4183c189200c40e000035195285580584841180000b803409846441180b40b81410301c1c00f00f4aa000805a2401d0052001401000c00ba4061500c24031410500b500c1001c0c070624070458604451101040c40102c0c1070050380c2d13401070340c20485280c0000c1900140101e00b035144012060000020800900380d0140444030300c00c3e140c810b4000c0e0543d00300b54444070685e80103040d4034003130700590710040e21a00526501c480315000000c07507651203c07a00c4500060447e02e24400707500010038003195a001e50f040740d004100c110741c1300c0030341d40c10180d105c000450041c000a026480218 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 625628318 1250 625627068 625627073
    0x51911070609200a0b0a08040c032a0b09011704020a0315020309011d030d0506011202121f05060a08040819050a080709081906020c33040c03030507 65
    0x40350001500000d0600240006003000c0a1880d0b044224074502038030401ca26103182002044181181d025280e00380c1000903054055805502c002d100f20742100000c1c4c40030000480e000b1203202c0803050b40088020030700d0708101005016190790802c11101c04140b100000d503aa100c20441d0320358088500f065026203803031021a200c10480e81004005903144d145401110b0b0044d8040c1d03100d81410b00090001d0007110054900790525050085090f82080020b1000f00711250050340e00084185400b207850604e450b80d110813a0069500442d2400c901e90034002440100200761054038680c0c1c035a14486031030720b800030792903200345082c4006011505000509004140d019100d02c3c0142d08661222002007080c02030003584403c0740c1c40d01096a000c0800c14052180c03220b00c0c2030302d14540060207084520b0105005206581c80b0486090b80c080000c00b400d041e040c09041085160025086140d000d01703010b0780040c2012450040382090b0720750400012498008060b011281c05042071940c403410390 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 625629568 1250 625628318 625628351
    0x7051f05071502270d020901150c150204030201030e060106200102090d0b0a14040b06010e060c070f06020d02060f0a020d0f060f05040e0312070509011e090f06030519 73
    0x8655207500c240c4086124011413041419000600c148540449481c0314038000b0004100b12410700a50010f036142d00501c40c4106599882d803541d101410215007151095980c0130074241c1d80b101c8215080c0d00424108110758241c003074046903180541c0074001d01d6041c42802882c2014100c881c07000803481c0c030b594a00788a02941150320001c009840c8429842aa081a5150b400b00b628010400c0e45404a201003507840786c1d81d40742c05140d05c00000352043c4c90b0038004644da851007a44540c2e200204100000301801d0800c0f10200500f00d144501c103110703103810b00107814941040d0745282035410a000300404905079040c040d40c0000149001130300c503800c5c40b0415000704a07501040c01c4840c5000d2020606501203100c0d401290b0003201c0500801ca48149001e459000d1003100d00900e0300510045a0054050300281500358818503003040020f1007114030312a804203400d40d40c000300d50700800600010f144e1b080042d000c0c01d902e0409012505056891400c0030f0a0000e1a01c0201d980710b000c030101c800c1d031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 625630818 1250 625629568 625629593
    0xe1504150818060a06060e0306060d03030c090f09061505070c03170c100506030106120203150a0e070b09030c01050c3408100b0d0c060c050106030206031807051f0507 73
    0x150300450b141e07842c010030383c1310043c900c60051402103a1200c00c41013141c5000a4410721600b00500900d2021b0240d640603405071400d080c0e01c0e07060064100300415800048681ca100901d408800418001c1c42c040c868016050641c240d202000010401040850b0302020450101c82d03111003164150344036000d181c40b881c0a4441c1412580c02900050460000b281e04091b001d40400c6008010141c0d0b00c2d00c1a6401810311386000350190001d600e581d22806944401641c0202c2001000c04c0c0b04540f0076003542820350580003400030303590200e4640d13000d080420500202d0f250a0030080d1404c181701c260303241d981030050501e2501d080111245100500e4542400000280e40101101c070f65444042c15501d0318454881000c003a80303030800d004070520b001e841e2080325a0f001a2031090113802c00408a860080100c0180d40664a8100001c01a180d480c001c610981e00014055099690f02200b02e080c80f00ba41e00052080100d849120035582c4000c55420000e070303250505564600451071f040c0c480800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 625632068 1250 625630818 625630861
    0x605040b06041208030a18060c090e09070b0d02040b2805040b120601020c040c031e09030905060a0c1205180411090d030909060e1801020414010309060216030e15041508 74
    0x12149847c81041703425044086204619107458a15a40b116001e10242404454103103140d480280c1c100042c02c020700060011080c0701d41d001d4a00343c0c464002e4900d651150140101a1402c6840500c00b6020440210620903483c80d10a00e0545030103400a5140910308036030304000c0140002c1030240c0c1c002c020101d903075400508284000541c1d030340d01030f0040c94a02641c0b141c003040309001e61034114062140000059042d1518102a420142440b01a4011104600c140070940350400701040e400002c06102c540780d03540d11940d0340c0d904012485400d072022030b400c0c09070707082c00d01000c0c580e40807005650440e4002e41c2c0c0030418104074101100c2c4415960300140e00c0c640b034041c022500e0401c15264034810a10f0f0380c1c9480002c006105d04500304c3c450780c400d0b1702202c0102a040b0029611980050a4845c080d220150401c0568000c642d01040041811804621082c04048840c1414416502c44000e000d2626042501d0001d0051540b00c100301400c04000102d0f000448403901c3c14000c900052 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 625633318 1250 625632068 625632101
    0x2119020a020915100302210403200105180a020307060e010c14030307110a120804030909140108070f0b31090f1404020609011101020f0c010605040b06041208030a 71
    0x41c0304a101d2a02d40f8451040c034060310001c11300340c001c00d009000302c413181c0034840100c08108080c20640000100090004c4041013500780e400d5560705c07401c1e0381c03040c40207801000008803400c02c20106504003902d21903d42c0150080c03c94040944c0d400b140030000c8481600b08204140c4000300105e5000f0501c0300b00801814803100b49000256000002d103105080701c3d21000d43c01d50112404640c0d030801c403400102003003020840100300a100b105801d0300a84241030040358980c07541254001c2c0c400e40350a80e20300014490040181680c200809001410100f0302c901c01c2c2030070101413074074504c5581c0d0400e5207500184280d61002d840340301ea0201d5a1014104d80f800281c50b14205405452200441c0d000c0508205d200382084507210a03030360040d94000c00c0e00d450021207600540d50103200c4110502155801e1111016841d280c0009201403507200000183c1b031400d1604000c00c031003500d0082405004140000d0060900f00303840103d0440d04400c02945a41c0c5400d200d60180c0f404007036101600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 625634568 1250 625633318 625633321
    0x5031c05160c080601050609100c150f050412030204061b050f1213050604050109090f090212150c0f0f072105211b16050d112119020a0209 61
    0x101440b261201650442c800713070340072666514100240d500a5010b0541d000f80340f00503070315655001d81540300c1d000b80700c0c0055242600e5a62216011034108450f10243c13144c44038100400c002c4a80d0703081c1202c02107800c045042c5810480d005090050722601003002c040c4030700302a030a12a01700803480b201c080350000c8900b0034a40f407100900359042184030780c0b0840680040443c1c1072400c1c40c04e80382a00d0040e904d800e02940f0340703982d0002408000d400d0070f124aa4880180c00940c56000034200010754140040280b1202c11401401c01c2500a1000024076020311040c202a60004201e40900b03103022807003030700c88920781000382e2400742c0440d031700030100000060720002903040383c080c049001c10368201c0d862041000340d030002030f030008a4040a2070526020040400105c241c0a04401031040c0c01c86003614469969862614683e0441500411881310282d4502d907400c10485581100484040740449422070440343c1e14000c44401e40e22040241c81140e4006108100b5510b40b10380041404465 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 625635818 1250 625634568 625634573
    0x4030504050307090b0618011205070305150406140111070b03010e22030c02040518010204080609060907080613111f020f03120406021b030c101505031c0516 69
    0x4560051207014040c0c01500300001e0903040a1045108088011744524a020040c030a045006400c101c8280d06100502129500d42a410320455110b4502d6440006050a014515400021158803d98402c1e410032a043c094581c900054203200c003020300341043d120b001c000b416410b1017243d402503003040201100000e4480306003034100b405846c031016184511320645802c10f502010881001d00800e202c12a0301e401130502d41d002c9544100c4d941151480d00b0b110f4409142a6801a404641c0503072080d01400404801445200c1d000f2071400c00034030150303103080051922140d008048005c1c03060007000d08418420899003101d080103008110002e10000090030b00c022000f1a50302c0401486003080d001e031445400802c807450000b9000399902c10781e40766a00c00002e5803207040503a022880b0010031711025042040039060621800c8050680004042d0240b8210340e4100300c003000840c800a02004140c80c0460103403110154540d0040b21441104401c2d9410b1003441460b042c581d078621000c50a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 625637068 1250 625635818 625635827
    0x1403071a070b1302130218091902040b07020901140d0b071b0f2307050f040905030a091406040b0d0e1e1005060306093403060204030302010c0c05210702090403 70
    0x300a482203170205070011401054500302c0c010818201100301c0f84500d950280d14080348490b41c40700303020040c4621400c01e00b082005030303045580188518013000c5024021441e280c00c940380074103030801c8154045035081c40091000c56166401502c400802008101c04502c87c070b8150700381386041d0720110b800c40a04c0c40c007008012100c003c2500d4a5030080f00340c20007842081240402640700400501591b401c10b400c104c10107101d0841c036903005a030b5a0500300010024006007270084000e44594400e1031800c000e42d520344102e6440d09103d9141000180407014003d81511789074102d13110000303804500280c03d54541142d1000210014003d1b0028801c0072400007460442c0d1034500b58280441c4d120382003803542d038410075912102d03143c1040854001118010b032407000e00005000d504100d5070a513044200c144000da800540c1c0007a000038040c01410b409000f030030440d007600d1504038a015000c1d114151904410b07003000e0141184004807404201c624001d503407105800414000c41c600342480c0280 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 625638318 1250 625637068 625637101
    0x2b030f060e010312020705090117010608060f010302011101020c060a0207020607050a051e010603120507150e150702061e06030703080f09030d0801080312061315030b011403071a070b 80
    0x250306404d42c14150700000d202240d0340c422200301508481150742000d844400d040d40050f00d5680942d640c4a0003c6e00c00c5040241034041d40004504109550550000500149080403880400d1b07004106c00034031160002802d90b80400141f00043c0c07101e0540c8002840d41c4030700d002c00740c1140304401c040c03000c0c0807020030b1071004035901e44254906120980c802c0f500b81c400b60b200282120283e0025280818081c1004100061280e5541c0000e0340b96240541c0841d074180002a03060761208201307031403180741000b000e034002c000c0d80020079003881c20180000100307203031910192044422101264a0341c804100d00d0016507071014185031124165054a90560000c9114a100f485000180a802801180072a050740d0080e80954601103060a41400c03d9001420807a003049001c2c1003c40c65207514411440c40f04000100c0415407071071030504142084d41a040b0290054061400c140242d80c0052150126020040541100c0c01881645440c500440b040030301030325080d408000e090030440f003214 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 625639568 1250 625638318 625638323
    0x20f1207050424030b041a0403081911071106160b06031e0d0503070207120b10050103020306012c04140a06090b1e0a2309092b030f060e0103 62
    0x400441c80d410000c01c844400c1c100c0d1010403003c0c1e01c202400440e25030441e19a0250150412450310141210541111101280c041e00040c1d022018448007144000c1e180e50350440360f080a1040d0b83e840a080c00040c41150f1001305500c0390304a1409841d1106000e403840811a2900768060a180741040300700810126030051080c00b40461700d8007901c8904480e9401646074100600001e0340740c0300b0070340c0c03164005056038007944207186000558044070060180428801d0401d40c126040c81c412000600c0c40c142c1119050500520802c4410390b800031022041800c40782c50145035000140403544442001c4e803805d9080b600300b0a04141d19404407075901d0084040074801c0002c995125044d4003112440d0480359480380505c140304104c51000c1e540e22141600082051310300326511070940740070b20350005030034820518101c1c0d00000c0386015920070b50310040d594050000940e0485298a140c801810580500c0a01d1950065814401da0041d040d540d443c5a04016803a140e000f03880b400c1c00244001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 625640818 1250 625639568 625639571
    0x310090e01021c060b07030c24090506070212030610030b0a122d02040506040f09030e041103191e060803130b1602010509010309021c1208010609050409020f12070504 73
    0x40c2c800d01c141310b41800c564020034a0390402d203460b50101e40001d20018241c52a9107443c2074407141807003070756070741d010300040b00d0001840c084c02d498451304001000300b081301950040c1140321580d442000c01c83e580301004540c41d152b51000400c09a000b050510380e001e40000940b803002c250701d0008040000c825020b103240e024450601c400d9501d01204010503581c4203283d0f25420801410150051a08124001c0c00407a03001d4a9003203c4088814095050b40054001400f104003410a032041c850804032500c003240c550314004546502c1075900c103083c0c22242d991014003030040181c2d058603444503207580000b8030201d9511124103569401051040c00050962000003038070350260f4086403d025540341c010812800345400544440d000ba0018606240c0c0724200040140e03500581050244000300700840000030505060340d251406d505803509100c040320044c040c8a800039642e1048600c1103c02003000032661000c160241100c8a07038540004c0e2801d01000c8483c004503030601078400580c3c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 625642068 1250 625640818 625640857
    0x6140703050c0406020c0f012a15090201051903090804030305041401050301060c32160510050304061815021801020102210a06031b060806091b0310090e0102 69
    0x40c8001e81c031070f0784a5080961300040c0c5094050410000846140c0d80c141400c0040301200c02c818000700c07800d5504c681d0a002d0300a510707420002c010b0106011200007031010010307a401503002921910410000382211480e40b0352007507401b4400d4011204065101012503210b9607203280c040c02640007400b0f1a00840004400c0000b654402c0090728100c81c595540c4a05055180d203d01049110340b2400700340e14000c0b0b40b12004990701d00310f148180300c2c58480c000c01118140309031420908646403c5180701d01c4440d400200140d62041c2940e81007600044006000e010700032880b02c50310f240c1d8000400e04500d20360a41d032100151345c09800800007a100c00e0402d0102d40004a00f00d00c1200001d915102c0124025034540c0087d1118551000000e200002c0950b10303901d41130345003074a803a0300c04c1e05107101100600000364415121500080291041c103101d041508034200c007005504d00c1c622090780040001968402c85400210040c0b03100314082141c008c0b03560600d03000c2c1d88551880f120f080400366 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 625643318 1250 625642068 625642081
    0x30a0906080c0306040e0f070803281425080307030c11061803041a091804051905010b040608010b150309030910110303150406090b150a020a0614070305 67
    0x1800c07940704148202c034080c51652000100001031080161b5a82da07441000070340c4a081c04c04101c3c000103001c40c07500850300c0341400e18040c0104812405440ba0124185d00d054070b100c1e4028200c81d5030b826154100d5500c07500441c4d02d01c10090f07051110300c4647e10041410200340072420b4000c5003d030215a40501440c1d03a652425546400c24081e00c2d002d0750310450000d070094030003207444424481000246d902e81070750342141109010900b148603902810015032903941d498801082c21640c5600503001d451860300751602510f42d5440440d200341c8201038107142d4200b00d820f510281001c00010003c10485459000560081c58810f401d140606180b280541020a904059900c0784407490021880d0644110a0291803e42e4180d51400c0c4051076029200080040c00a50300c06c0d8507140c020343c22055080c0804c41607070440e901c009042da1818110f24030648940306980040030100c10740903500e050b41c801c02c074a04541c045020306101d2914054850550b020034541d401801c55540500041d100c0e035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 625644568 1250 625643318 625643327
    0x60f06020312070f02070302090a021201080609030703180b03100509060301022d04030510052505090907050c030a020f0c0f1c032c04061406070f050f030408030a0906 73
    0xb8607440b10501c0040008030018860608203518a0540c410707a03070541da0307950200d070082409440c040301041c5c010607000000490550154010a4200d00800c400e0078040f0081da200c0c400d004026082007109690442d440412407d0702c80100260043c00f42d4914040c1d03c580626081401024440c0d6035902c0420180d150500030b89082c008145880c00b206500c03810120840b00784015031205404041c400000420814031814418041001c004542761801181044182401c030b00303100d00340c0300300b4492403800075403140540b240500160303003075129510781b01410344280c0595110052544400a0810506907010400030f901ea40c400f8104c0d09000404020481184250422180c006000384c8041481d00300c07041c08503808034040d045c602d1641d5410100300944070300514103002207218440700c201460609100e00e1006010180103d43d01168600c002103143c0f2900c04041d0510300046c0703030881442414402e2000300039a10f42240e58941c1d903071150755242c1d08065148008600400d00014409024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 625645818 1250 625644568 625644577
    0x7030203150603090a05120a02070501080103030903080d0b1e0a0506030412210501030b180105091905070e0103050105011e030b0a09060207021513230d021503040303060f060203 78
    0x116104446560844410b11620f50002000091940f00c1d4403a9000462000d00050411500c1013000a503240741da13a03006842c0800726484030f41080302c1240104082640b180c404802e40c1c1d031204030381d6a2840740d020000060701e009003407103620014026003801160008000001464416668080542d07039980400c0800d000071a80a03020600700c03980e44807035501c11110080741000329000c010002d241c40d00e2076821500300f60401c950b041c1c40c0b0750500a15030190a4404060100903000380714034a01000940d80700d612401d032450322000020440001c0100c2071100364046c013031800b85140c0540e52400d000c0c0c060719082c0724000a5100da450040304203441e40b603200d4140da81140000e14030351a1200918020b10003a001528031540c248140c0d001a510181e082c030712228243c0d00c207030f260b07240d040c60035030b00b044550b12041c3e00d0715250750b0445c0c100c45403465038400d004d03048945640922450000c1148009514a40921600000200003c0641551040080d14423141091048945942d01030340d41748103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 625647068 1250 625645818 625645831
    0x90f0212010c17011a0c07180914030720120a26070f032a0309050103050703020702180612100507090e04050a1b08030c100c03060e0f0903120c0a030507030203 70
    0x11183c91403002900200300078000100034000711420299110040c8010023070b2041030740803064840c0c40c488103000e80c0280300310440c00c2010145140207070380d565890480d607440328400c000c1c000a001200d016039501020b21040a2410162240340d001c038039003803101249031071207500854110098600642d50603815074084a5104a04e0301d0100314544055074008229140e400f004940400032003003a0401444821007984031b61100424a414440094140c0b1300040401041503c144482c501680d21075400c624512680d811041040e15480046084134444001155542c4540d1480c900068038581c4100e11076401d584c3d400303c00c02e848030320900c003e40d0300340c8c0c003d49603611100040c1c000c1012080f4425a00c04000085e484450340c500d021800d54008201146194000d440382a00f550b101d4001c10580e11081c2c5001c20100b0300300160800700100c060090000c52070341000240e01105c08008a421202c400e185042d440d2605c030401e034400798842203003240000d00305000b0034045070007402903e00486 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 625648318 1250 625647068 625647089
    0xa021e0c0a06031109040c0f020105060f0d080d110a180501080106090b0a2a0309090e12130503061501020115052107090204030b0610020304050f04090f0212010c1701 73
    0x10300d00b44040307002c0c00e8841c50030701d0041010451240c15507640d110b604110003031074558403034013410351001034211600140001e00400f01025001038a50300e820018081c50351101074a92245001d03d0b020009004401c1c480c4d4000c0e10000e01a94059007100a201781c1c001c400e102d078012251650011a41c02a0a11603040070402c11502400300c0401d01d03016000e40e518601d480c81000c1e00980303c40d0350084154006250308080c040c2c0003010705901030741c4000500646241445114084d114031640e03a441000074211105001c210382c075082881d402140d00a0000800701c03a03990808403a03c8007081c0009041c1e901542c03030110f0420100e024140603c0468200820401080310301c144105841c413100b045070440e0707009942c008148000103202820140d800b440700d507003480c0f400c4010f018981c03001e458804195070060204101076600d180c2e01d00040e060030345020a8018107031809074840001300b40004c0d4010403003185d0806d16401507002c00c500380703060350740e000025600a1341035140c0002802030f100202d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 625649568 1250 625648318 625648339
    0x30504030204230c040609080106050f010e1504090c0f260c070510091103121c1112040312140a02031b040f06090f0e13030203090301020a021e0c 64
    0x18038055004400f03103104040041c030380340f109008851011404482075844014045018013005078407a50b500c0107170a102c4001c1040381c5c104000a020810110035280c1005000341c0c10070b83e51384806404044c60408402800d8a41e80c582400d400500150700909002440e13035060040d1261040c880e40590b880c0c01080f800e060108001c2d1054207a10040038050004010030400d00081c604105001d080311000b10001242440c5162082c031760030398681114800c0c0e10a10480a1060004040307408000c000e031006417450202c01c00000140052000901d07040c207001c5540c200c1081d00010070ba04c1948240e85002a0408403146001100d1000e008500e0b00240304c00010640c1510b60b0040d500b1441000308281002e1300c440740c100b0f055206070802d0390b625564500030440340d0340203102d004c082d101406030903000508282e95112103600050048010502407504101418001d201b01c03000a03801800a5565074082c2e640030b5581c4032962a100c82c40c0c0742c40070f5821400d20b004594050051801801943c0b80d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 625650818 1250 625649568 625649573
    0x2202270114091c23070329070c02131a0a0504051003020118090c02030d0509060114010302070c03020933010509091015200a030e01031e1103010305060c0703050403 72
    0x103c00403c0002c46064114800c0040ca42d1401c1c024000401a408002c0c0403050031440c1040d00081d181204424581009a00c0600500c42c0d00341d0075400301141c6450740382d9030a1030000450002181e00c01d4543c682c9801000c03440316010318075a10000c40150307155805140c1e04c005010886904480380c1700a081b0400c0140b0040d0300c40c608000601c5608000e11031260f4507220000e044034007005036240964000034014001c20b0060142030f038805288400381900e5803400e001405000405032405040650005030b0000300a04144c8183c041c5402900703030071440c1303444803a4900c40002d6515810b81d00701100994019020600c00904001006a580e2030a203100c0fa07007400031040010b015151030314009040410481c000c81c030810100001c6607280081e0f410703070b2220a1000e040903000d869140c0c00c98118040841d8220b40c1e00c1858140c00e00c1d00245100e010440f4480c64020420f85964480c18104003041c281105000b0b18140e90140b0160f5001e0344075521440c5051054800c0103000c01c1d806e0004001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 625652068 1250 625650818 625650859
    0x1005091e06101d06040302130c0f0c0b040b040f0506101403010e0307061e18030816020607180b16020f03061e04060912030507091202220227011409 65
    0x4201c0d0301801d105d08041d160750020b4602c900f440504600180d40701d42888180303078007540ba080b0040050510840099442c0c564180081d1f0051025119504550125041044035103145040d15003210a448070750902440084900160388243d601c80350020200344030514041c443d4921440c41c0034001c52402c0081d680f400e015086010703019100280040c2d4480b590520b0380a407010b01d105100c420183c14145180203410084080c000548210411810350754081d00000c4207508213a40d82804011040210700d03020805465420800c4802c0b00070401a0b44040c2540900c42210710880702d0703450111101040c580e4501044920580400d480d10400b410310190701021a0410300400012490422070f0b00c402d00214980c01c09000040c1e035600402030300903804180070025110000081c600b002c4a0340010364024408400c01c0c0382818060211703502c5c03008590403904c42070300304c0711408003240340c0703407181d8007031030512441d45001c20309606011483c40d040c0c00803078400280084c2071084581da82a68042d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 625653318 1250 625652068 625652117
    0x30608030412080708070305070b0c07030f080405010b180a0f02030f011401140406120c0f0c02062809080d021617010609111b0d171005091e0610 64
    0x40e0221410011340d40843e10807401850a02d0007604c2d00c641d42c0c21103247c04040c1000007401c90030412410301141d000294007441c10440d408091030301c448180c49a0a0240c010035030144400e600034400340a254148410300c940303512440d08444100a0401d00e00e4101050703200450b8410490400c0400521a081601101200000c81898401c030700c10015a0309000c940e0181d001100480c0c0540b10b00c419006141c0100c121808051810000c00c0700c907040c0250017061602d900920a20300416803582c58000400c810f003c0d001e11702c1e9030384003001462601500d0020b07940584001401030640c0c0501d0607000159001400c44031703c450720802450065200b0841c902e903013007403000d07540318540094913007003c0c007440342c5050007000040da50b80da600f002184c10f500c02d4131146545411010031612034640246008074901c4100012405076901c0d40041c075007a801940040c2e40c000c05060900494010000b19603010007110480c8440613241c040801030440141d010440001d0725200b250003c41000f000e40d031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 625654568 1250 625653318 625653323
    0x603010e0c151306030203061c0b010515090405040b040201020601081f0c020f0a05070602070504091e030512070f08060f0915040f0f05060109050a080d051b03130e07030608030412 79
    0x903400d04644520b940e10f100701d44d1303014100094001c0705005a918000400d519482150306d40409000500c4e55044540501441840d00c1041d1000208150103102c1c8126050200000e10410151a00b413a113241404010303a0141d005209100c0046414000020184042e51802525803c8a03010740d4a1b40c2c050880c2c403a9610450191649000400004208000305548610b010303100d01410583c009240004540c0080d100d00e08100080c004590340c0c2d1080d0390f14000090781031b0503016082c1402d952502c5442c0301060130092003003c010000394015444201c00000c2d0b6104050340c0c80344c500300840748107826102d692005500000c42d1001c16986c4002d0508000507201040710a048504541224030b0301002e50441900c070f9080000039a800f001810242104903a05a1000c0c1010302c0241d9031000d812840c414400b00099020300e0b2034400e40c2007000301c5490300885e643c50300384601c00d0f9071490444c842d0004030038840700440c5c503240c02400b409042d180807074010340c1414640003200b00354a400d041c09 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 625655818 1250 625654568 625654609
    0x120903052104060c0e060711030f0d0c170301062f030f041805100e06060f07050c0a090b0d0609020f0d0b10080a0201050307032406030608060603010e0c 67
    0x200186a00d4009240018072040098403810346001c1c24008107445056080c5000c1100412075108603666041c19a0f24040c0c000c0c0c0c0c030600d0020030b440424581341c40003102d02854450341030780324841d951082c0c6014450b03211740e0f0784200f600c0c240b04600456000a009450101e0712644101c01000400d03403000303803001b140710150881540791018060655100748445c20307040600190034485079a6000c41d481d034000c2d100f401004945400c0b99080102810350003503026900001001c10403031390740c490986000e18611518155641d007a40ba040d603a590140003124000d2245460000d01c0b00b140b441490401c0c9800341194203500459030310100244000007013260f10030040c85005140d40c840c40360714070890303206101d141a5420034040607822003000e54085000d13940080003210060f6402801d890700041e2178140894100b490020028040e0300c2c0300c6014918036900c6100203002903042c0c00c2002110719581c1540d0464542800b81400d80c7c202c08442d62495210600207201418414420001050030861 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 625657068 1250 625655818 625655827
    0x100f0b070f0209101701020c150408120405010f050a09021c170a02070b070302031b0610030308150d06020d060b07170a1b03020105040210020313180204050604030c06030b03060712090305 82
    0x5051080011078005c00901d80e5010528800740740d410012101102c080c0500980c0d540381a40ea4100c640c4640b080844070200f402c0082002c101003500603141900b183d5101703100a01e000b90f4000010f242840f400da01c580036080d4241800700b0f010b8011170b002a0024150030072110410545601c942c440350701081184518800080c00c0c002841c00382010b2442507001c0d590741d110620314000f04d000404150b14454000c03005002464180075100007c40341d16082807601c0ba074800c8400c5652242003c0c0444d0481307542d062480c00c001069009103c4820425400c015081d20740345c800c0e8541c010b00da0001d212407820401c10210107941006080002100c0c0b4061940c0d40f04000c2c14050145410360440c00b503134407101800308520300010b45244144440c801075045c010310701408a56a410341c41034000403051080d6103800700755a601203501801001d48002e542c0c0740e8a01c1c111844190700d11441380081e14150500da41c41c980861828081c1040f075842001c500a0320482d40c0040c032107040d003181030000030407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 625658318 1250 625657068 625657079
    0x80301030b010f32280314030429070f05010207030e0d080a0f020c040c09240203040605090f04051303020c06030106171e100f0b070f020910 62
    0x560286100d48404203640d450711014540d600100d4000c56000c4044840d0100000d540c0603900d80390090540da6001e11900540101d00e0400a0f07085c03d00c0306038403403504d03840900401c82d0702404a80c89001c11030b83c0ca00d8101000f40e124001da025600d111040381e50418094032644401e01040700c006440a454440c00d42d444010009500d402180c05940100d83c01c07080c1500240300c0d0921600c145d070040c840344840e0303039842007902c12542d10400341f150030840300c80c41c01d108014141414030702900c10041c20003080d00c040c00100b031070301c1001c4980100d41c80300c08444000082c11426090315800441c1024105401903c0c5600035032041c0341c0201c9903180184480c1e61702d00407640120a40c149a40030b4980350305000f4107086000b14124041c68042004000059100c41d51081492441e9001907042c0c9070f0070b20701d40c007500c0c034004608088109201400300003224080322808603000b0071781401115a40c0c5e03080c2162801902c80240007140040d11702e00240c140911410390100c4c0d03030602015110b8499 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 625659568 1250 625658318 625658333
    0x606130e0f0105040f050601060801030803180111030903070209090a0b0115020a0c0e01060807031b120e06070305010e130b01060f051603021609480f0f05161e 70
    0x880703082d19102440074105e003e010003440081c0c050801454040710399811515108100d10024190069000c6a400049414007081d8803458040021802d080e5982c10800c5246580c1e4200750340c26032040e03018001240c8113540009180c484550300c1050010b090303280c04c01c034220b035214151b044419400b581c041c400c0026414103444002d030131280c3c2191003d5040080040c0310340c01c01008030080c5850028607036032185030611010004031043c68003960481e80f02e94900c001c1c2c000e00c50041c130b9902c10f40052014035a059000a81682c4030280102c509945e144a800f01c9903e4405018048140440040c004184141d089000c030343d01c103007400351401c00f01c1901480d4030206188181c0050300180c00c002655002162203600801e03200100f40b00d00c04801810b18104044c0452090841c840c5802050001c01c0e60910401703200304400c005030702590b610034050b01c815801e170244800501031010f80300c0b086003d841500c10203444010503440100d5180d4404505c910185200c0c841d03212001007480c0000c1b400d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 625660818 1250 625659568 625659571
    0x1005070f082a011e150b21160804020d0305040503250909050c090717160215090d121e1b0203120a0b0a030c06050c0f0606130e0f0105 59
    0x1d100400740d201008030354580d0002c050195107040343d05268103600700241e14110070350550841c410020b0303c000aa10a048141d20903400041480c1012801d00c076071094100d042920643ea065800210b60790f20800000958104d80044002c1912440450b025050240d0903070903092180c103100c3d00e015201c80002c0c0c50021118550390050f10300290900d034052405000c4002815921014000f01c081552840c0c0c03245009681140182c100c400060491445081306074000b166464100015052842030980c005440b102580054030841da108007000c0329000100d071260b84980041c000080c0700c1c44044502c0f4503207840a0500030b03103074001d400300504041c81c00c20464807100c0c1c0000e0f00d090a00141d640040c0702041e04400c4d900b050151481d414410150709601030b100000001d60303610b1400004081503400d820241500c02102ca01281540d0000020704d030190340a011a1040d00400480741c1d0303035840481e959a0041c042d4000341c41c0b41c001d00d03000100380c09125401d43e04088483c20050b821100b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 625662068 1250 625660818 625660837
    0x9110d09022707030c11030d0506030c150a0201050106051303060c030e1006050114130501080406020d0501090902040b03070f050d0201050903160e0708130f030c0b250801051005070f08 81
    0x5210b00344264203405114001c0d030031560307040c981a01e086c0301802c81d407070340199042d00110035100c1c40080c500340d405008108880c0d50003800c80c0000600398803450703025001034000001540c648800800d00d54000d105640081c4d0000440800150460303903400050450300504109050300c0c1d445009401c40d00b80604150b4801c0114002010381c90140010f111070101d8540100c0d07000f0400c0760310389400346544230905807042800c1c404a544c8407881d01d86c0c000c4c45020b5126022614020011540d18855003050880d40d008803800d10080c28114205a140ea10074810150b0620341e401c2c0070001d50405548212940d0b0050610900305905500840d081c00010b0307040c1e00400d0b558410502071705071416030b8107801002c94540303004986080e0b214507070b02440340940a04105184400d54041510559281070101e45c081261085824035600d105400c85622030381450400300d40d10759100240c402c2194904a40c3c00401c0d807090310700c00050554407603000d000d00ba990307484900707625404540c241000303001c80c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 625663318 1250 625662068 625662139
    0x1c0905030a030b010503220302030714070510021b0906130204030f02010809030310061404170601080c03010b0904021512070807081b03270f0a0203060109110d0902 72
    0x112410001003c0b280745010b154103116051042c05640a0400c01e0083c0304a1030034480380540e106070500b039141d801004002410840301c00012042c4000128644084550170380388210321241d1007609a8030b40080104d100c4509194044864591030441c000ea504000c000d40a504403100c1000d1f104140d034840e410a41c0c07111985030000e4110359001c08026440f10b0900040d600f181000042d0780104503580c8250400c0154a200f08804003c1c44001c4500602440c11b000c881120b8075034007151104d0b0240f0071150680202c40c50303401c5a04060040980704240108204000c6e9a29420406040c40c103600f03201c2c20350801c1c01411558107003004268065841a01d4198a5183c441e03802010918001c002c8072001c1081e0340420381b010061816a9017003010041242c42d0300c54010900f00e044160a4141c0205102e030541d145c0e920800804c4400281d40281c1c240c4001e40e8869112b1800d0700c4d40c070710800b02040410840321145d580c2560140881c4c910041510020611102d82d05494140000721130f507009 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 625664568 1250 625663318 625663327
    0x2100c20010506150c070b0c010b060c010519060b0901051c0606080f0a0b01080403030b0103091e0c0b0c0a03050d0212011716060f0c020d12050c0709021e1c090503 72
    0x40c588030050000010b044280545841550700c5d50f03e03152101d900c40e140d07201602151560000c0801c3d004120078000107040301d034650449816a50103048241c480d05158100c1c104d244c6000300c12409004191800c1c590f100e40381075043c0c1c004449030382c40071220038500070b005424041c1004090084100901d11542c40130307018140755041c0c40300b40340013421164000303280408d00300050360005512507229406003000240f440c980c07001a80604100c510003000c20450340314840c45448950300e0369401c1400f0302501000c040c0c45030003c0c1001e20400b00d110100794400c503450400170380310703500030850140088000740c10160f40c40711510340080b0a8100040400100c91100e8078145c0400c080e0514400321007a03400c01528109004e443d11502c0c1c0350010801140c03400305019911807a8640c0d44040d804140c0720a03500e002c10000b0601e0300140c000c01518000d07908002400a02e0b80250f400c101c00002c41440c110500c034000003120b80c805004100c80c0d6031040b00b5100e50586a200b805800d40c02440036582d507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 625665818 1250 625664568 625664581
    0x12090309030706020106050d0b0c0c0d1112030f04140a0b1510212c0a0201030c0908150403030b060304110f2e0e030d020709050708010602100c200105 66
    0x60040d543c200008581c98180204074650b1002c25010504d600040d00600d03075160a01184214801c8007070404c0148264134207601100d80c02035a0741d4071007210074142c070301002400351092140c0c40165100502600300002040200304100d00000c8204000012180010120b6a030300141c3c1c0c404031225850316010548185a0342080888003440400d14540040e814865180400c414001e00c0b01003203e043da0b5500e10450f016070400d41d0516808a4140c8000c40650b6288056860210310000ca00080c28090344000c464000c4c4c0700d803000c6d0346144e000790041542c079020170304007090020300540c03c058840b9020703041d46c0ca800000750b000354001d00400e840d04060360f06000105e20420b169a00074003501c4650303000c550391540315841d81011400920640e000c5c0c0401110005000b98445526010300706900518640018001c8101e03004030405104954803840190740142d001d05c14003000d0380040800e00003207240f0b07500808454005052000600b101055411a4a8007a15451403540e550348184800d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 625667068 1250 625665818 625665823
    0xe1c1202040303121508100501050f040b0109210b090d02060c0f0906070203010f020412200d021c0b01181116140a0213020a110a0209070e01051209030903 68
    0x44006514194607080c6540d03401010b04415407038108186503511100034000c0a00c0e0200c000504814003104c3c646030a0f40384080c0200b10a114651103500307000c2c0091210308060007a02410707003058503600403003403801e95034548103040e8800454140707815a91400002da041000280944a054010160400000c5003c0d00d060000f602900010f081405160386075070300c03a0201c1d40b840006030f60040e00e55509202003070261100500c408030250000c04e001c9003020040050140050084110340c00800800c02c283c0c1c540e2a041040c2504690481070641c0941020f4450740f84440702c5030302031001c4640f1512034020600003070f00101544075019002c969a01c0c0c4602841c6030031234140508070b20b0405000035042d120040d0101c010600010f148114213480d00c148240400150003400501d24000502c80b0075009500001600c03001c030369000908882c0a000184044041754003030720034250754564140581d103030b10301c40409604006041200304009495400c1e8103000e080710100450326801400101030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 625668318 1250 625667068 625667087
    0x80706110d111c02030409060905160302070533010e070f090e0414121303030f031509150302040f0b0f010503190c110a050607020120030402090a0e1c 66
    0xc208074044001d050b01200c082006503070100034400f5112644580072003079040d8002c641c05001d109182c00000601c034400303034200601c1207034081200d040e014440c1c50154103d00030000d02070301c50750100340e0038800615184400740c2990701501080d00010b1802d0420100010260802890004824280024144c00034402070b40e0021a040c5019002e05021160b100501d0003000a82051540c001004443d1402e00a400c001490a0000c0d6520000d4018030700e54400c0c2d43c4411000980d00007101c0501354401e00c210307040d60200d21040a01940f408242e20302400d144540880340c9001e48900000503542d51203114034400201c200490038012010403c21007032100c07402c103070500404000f0068080e4040c1802c541c0c200e0003050010b000d04031400f007180c2090b411450b524a61040d0035501090181c00213009100d410f4580c003e004224552020f02d44841d20410001001c2e5000e00c00309006207040303080c0940c014000764000034545022094580b40071404560019071005041e02101026800721468 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 625669568 1250 625668318 625668343
    0x20a05030c090a02030a0207020d0318150c0f06020c030d1b020102030601050a030c141b06070e0604180f060b070606060e0f1c0b0a0212010510081f08070611 69
    0x41001d8400c40000c900c28050041800d00b0982d40040080e1071060a0750554801d03e8000d03210b04500c1580d46009000040d641c03640074016071420700d0010302c1041c160300d10800d0446ea07950f04480d442e05a502c94443e406520300c01c0b290940c080c400b03441500c03005c00113030450705940100400d10500c3ca983c18540450050080c0e01164010010403c8990300710088030b04c40c0c40c0341e182c00219011030020860700140c54441289000e0700020f2500c0c007100c603480240314402c002600751030075078840e010146d030400404081c1542024082c40708204007403034600d004108006607480410403152201d100c100315642b503003106680c0040480c2039400c1c0881031007001c8c060555400c0c03000b005007419000a0070054610f9003140b040d1a443c0c02c044601d12501e0320100e03020703804124080c0c5410142001006500504148a40444200c000080394603101200c03c080c034005465500c220346450032040b182d402c60040354904800b81040001e0900d03c20060400100650355940c61070080341c200850908400d001034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 625670818 1250 625669568 625669573
    0x1a040303090b03040c0f060f17040506010506071401020a030e07060c11100509031b01020d020316030e0d080d09020405130b0601050d0b03010509061503070f050906010c080a0309020a0503 82
    0x61001940214040d41a2070100c01815142d41d15803400610401240e0004401c0100580d400620240c100d2104206150240c4459840f0490800340c820b8034071017118050000e5220307c4c010009414880c006280460184660b6401403001c1941d02d800e81c1d00c594008070000c1d40d600e0308001c02817814014100540700e00d00c0e000c11000740a0f16007451078248001243d2164521224010b1140d015408480001c04094180e03507161810322901c071f001e117001130380081c094000c01380026140f904c00b0085039a24564262101031032100c42e281120360352041043d13150000901d004030004501c0e40b10151110400030b1502058441141c418030050b5030700070700000042c2d1199180d4000140f0041c10003940210f080c600103490748030101c111009400d1150040d07425500c1d1000f845000c0070f000c10f00c2885002e01f41e25452510012005065844a2501c03542821500d00c6005000314a42800c42c3c0d1b0b006101490004031f4141151201d203c183d1080e1400c40100707a071155800110b0401c40004002420200c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 625672068 1250 625670818 625670827
    0x100e0f010b19030204030f030c050705061c18050a05030406020d090b07021e04142d07030510030c080f0f0106050d15060803040602100f05070c0803090a060c091a 71
    0x44890756400750100c005501a9418044000d951184c1e0686000b150042003501050f0703d90704000d0000340726407071b099a490003046404241d504103901224200124240302e401850050715600f4020146282c060180d4880070104002055041013140f0704c0030701030b002841e0350780d1078440f02a103032918106040c01440390f0700208000901508041e5881c0e0b035015600c82e000c8114003809200040500b403e00d40d0311600d00b070100c1903400e40c81c030201d910807130100c00180c8221903807412141920903404115007540c03043c0d5000515051080d00042e03007201d070040c40e06041c1c9440340d82d020054440f5030882e46050780880e8402c0d00d03d00d400c01981d406814000b0003003020600300008a280d1140c0740d100030341400088480c4078003811481d40103400500758071040d03e03290f03921220002e4403041e4240007115042d04000f20255040c07003d12030240108401d448100e98200300d5540e5418642000b801c822040c0150048030004c188640103003500c0010701e6640b000c60501b40800d140140c019071034181c2030706a041c40f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 625673318 1250 625672068 625672079
    0xb090d0e0f090402090a0b03030f0d0608060105090c0c03040810020703020105150a150203070203150f1503030703121806060810051515040b0c0303061507020d060b01050909100e0f01 80
    0x88402d50031035019981c3c8802ca556591a507006031605056158140c88001003032912043c8150140800d070000345000d004031a610409240d50754030a0103000e51000b80c40021a140480100080c800d1448a0741075038289580d65a045003004007204550348603640020304041059428411907611014200703400e00d0f803100601c00b282c0e40c0b9000340141701c101c40d510044080038500030420b94102076402000c483c603511030128080104a0150b1b4002c8d0882c800802140d08007584a28107000d00e07102174011424001e8644089940d075031030340895a10582e9902041ca100d50809203114070142c010100401d01615040b11146031403502940384103031318030700b45c180640c3d40320101c0c0c03402c0210021a8404a4020070b400712600912555000904406c0c0000d585858078034044050b61041c0c00413200d440e000208480c0c003611504c5200002984030345030050703503400100e5660148001007418540542000d0049021403903c540541d06441078080c8003804000d80d00031420555405107482038000c50551510 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 625674568 1250 625673318 625673329
    0x1219020c0a030509030106180c080106050705030f07060609020c150a0e0304030b100f090506150414090403181205010f0b010f230d020a0f030b0a050114070b090d0e0f 73
    0xc0401010440f001030ba88000f0790342500b144018001406444140b00e01d00b541c0000101a095402d82c041442c01c400090081c0c0294103580b6280d400c030b0051440d028100840c00c2441d48a103204490a0359a4000421b11a545202605010030030000070056075500032070307404003800300030111055a410944041d1014401100b503804407070388101d04403180e80b0b401d06178174000c04203604881c00c6011447d4000078003403500e41115000d021f080d54000b21007002020591158412405140b600347c404600f000301c82d0800f200e071968001d010340b03448000d003000540201da262140340d11500c0c040100000c071905019080c031031001e00c035100e01402c2013a07a003882c0000e8042d0052442940500c0500d03106c0d410400c06524282d04100b90901100741d41d0100e2a002100a401c2114105d0010310100d28114080d0702a118041065030010709400000d4031348001125441c0c01c0080701040450b00b802100002440b02140300d0050304201c024040c82c0329800d100405c0d15004103251445070402100000721919031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 625675818 1250 625674568 625674583
    0xc1c02040209060708030403021011040518060103060506220914060907021507110c030f070b0c100e0105180a021e0301090c0e01180b090a021c021219020c 68
    0x152005600c40c0c2200d400100c2034044e61030082e10b6110000100010558081900481d0400c1c17408200200101880c940d0404c4c00399000d0250040e080512401086015040c402e5100105240109206448502164041c0c00c403200d1001d407104090900030a0321100048840508400d030010031030000c10041010041d140a0f0105000d90910000708814510074406880c84400c0814240280c1c14184001000316000141e21403c900484850881c00e18005c40c0c40f90301c21020300d0040c07180074103042c0812016440a04d001004d4402d480d0f8040131003460380100c3c00e4810425000150343d04c0e003802d1281c49035900c00d43c1940c1603001200c600380181e84c1c2c0e00c1802c4410b400c2c1c0c01700c004841c0c40c00300424014045d800300a0003c0c003440100184000502c41c030f43c0d0617603107260202c0e12000703078a0b410001030795a04000f0381d0740107410a0000380442a80d178098035200d01581e08000d6040102902d200c220380c8801116007000070325208012a000341e0403138070070741d400d103102e01107203007102d400200b03901d6403c4d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 625677068 1250 625675818 625675823
    0xc0e040b0a0306151a030103060c0503090d030b28050328110a0e250f1403040503070b0f040c14030c01030506030319260601020a1203140702010e0c1c 66
    0x30396581c4038031002d41911080001e013007610100000e5081703240518566410911040301d209040c50700c0301a00300d2064058034080c6250200818a190782100103038098001c40e608a500a048000030b400c4030242c40e1001d0031410228204406802e0401082c10704251800c091400300e080036841c810841c169400d16401035603000410100007200c40c20020b04200b810340d00c0307803003003410a6081c0720300d200e401c0c554454084a040c420b011006070952044e01d550844030304c09400300301c010501d0076044450f003004582c480d10a00c01d07030307140c00c10543d5840b0b0320904c1554403800855003802044100310203054424050416490803c00c00c2d4403200020b6a24081c01e0b081504064898002c200d164a080044c0c540052181854101a0202d40c0740100351512490302e0b41f15150703688040c480000c0e00c114070f05000c0c036010780c080c240c01607180e1a00d60100d4078117103140c810107940d1240c0031311076101c2043d10303400341c04c441d070000c40e08060044c4154a011400e201291107860005100c07003059000c85200d401c03030f69 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 625678318 1250 625677068 625677071
    0x9010e060105040510110d08011d0c09030601030b01080d03020f090f010210051303030b04051012150903050403031106062206050405010b1c0c02100e0c0d05010c0e040b0a0306 77
    0x240c415004807964010f07944941d820849280c1500342242d000260a0699114041150748086000408803a0040207200b8113000c110103490b540400c0c2d0f031324209640c0c428940d4641d949042001c2020030300c0c0c01000da00664a040742c0c80014007803241300f4009801800990f1600394100600400011a03d11401c903c040c07185185d03103075164207a4024405a4881c90080008120524007904003003101d01c52458201c0001e403500f200f9100317034a4507103d0039018641c016915600e81d403c1001407600240703071260981c0c0712051b094985170320740102d0041b80006442a0740f000e03121440c0d464040c0c55803411100c04400c1e074102e0800c001360b90f111031540425003008085045138854132540000c004142c40d81080f50818101800802c22442200c0100048110051032004041002c424202201e0100d0050340041e00006070031031480c0c0003a0400044d190f10302d0151814003030580c0004000705a504c800300c80613511a00f6800d80d40e9003101c012a60500c05a806000000c0010b0010b841688213010081019 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 625679568 1250 625678318 625678321
    0x7080a2304050409110d0302060108240114060f07030c03030509034801020901020f0706080a021b0a060c0809150c130519030c09090308150312071a07080609010e 71
    0x42c0d100b0485481761000c0c0c00640400c04a0900075102c01c000d0003124428810104516050102c503103070851000300210411301182d0820148540003021070800d03950201e01807010740d0544400c400100ba800303200b5220503860f440285400784c1541d00080040c00160014001000c46020f400108003035040070940d00e500d11184219100024104440c10600c04203003503c003402080d505600410919000340c085a00101b042d0300c205a440715180242070003d012540891141040da80240003400d0340300340ea848030145403d070943d10f4001290740907038a19494010b0181203035003058031a60410200f01c081d18020105003150028543c000e070481d51454030025442a12190b0016000d0141400400c030002c50310650829000500c458041542d141440d220000b070386602c24801da01041760b0503160320b00725a68038100d107262024511800b0b601400b64141e170024100030b04001302881403096600000b400380300d945c0981e00b41d00081c10b0b081401905024081c1c1544c41c4c4402c541121141e5050a109 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 625680818 1250 625679568 625679573
    0x50904080306010f110f010504020f150d0c030902151b12040320030f0f2e021303050304060c1a130f0303230f2514070807080a2304050409 61
    0x2940441c00c460412402086e1185441c040190405801a802112580c1c031009406040140802404c41e4880e8805420007003502c40a031141c21140a0b800203084c006140d032031a0300400c0c0203c4a15242c0c241e001c01c002858402c5441000d441e1010369030f40002002101d621780340c1201039205034000601a8800d0302da4240807100030400441e42c0c1c1401405a0308480c84d80e01c1c0b100e96a16840c0924101c078000c10032403004144d031808440b601d250b00c82007032111109004260f04001d51140b00362500c60058000040040340040004000410141e40c44844e040310a04002000d001004e001d0060b9107218401d01104013454440500b840d0340060608a074203180746010b074010180d0120800492010350303081100b0294014400748681c52240c00e040f4036544840041d0300d500c1f0541c80c0e68189031744540c20060800d01c241e01808038001d038412490328008590710b039548107400460040300c04c210000703119403e10354841c5482c060100e011800003800c2201602c80364443c0260b0003418003031a41c83c9021401e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 625682068 1250 625680818 625680827
    0x909110c070e16020f2e050114041103130b060d2a090e070303050d0f02070501090c08070b031902120910060501020c010921021002100501050904080306010f 69
    0x100640384021500c1150b0342d002902244103080b00c141000e00301510705081c442c3d001081002c02d407080c3c030001d08107a10a030184c6107900220080140015451031203101c0880c481442480e0103460400c1c04089040c20040400c019a10714055003104404140140304202c005905503440003640030070000c000c2c2c0d44002c0030901c1040c000c030020b0300e442a00113a0010b80c140d4400000c3e1300244140740408643e40350908803050300c141105d920021381c40f00204102103032054000d4110b81c20f00381400700f0940180e404142c180d0300881c81c1540d050355141c041c0010807a48a052600070603944000d020013038640030541c036850100a10003c1940780b6000319148084480e0304541407210036080c41c01c000c0c244811050b5032000f4500700c08510314030b481000704041d800002d4800200c00140e446ea10294280b9400c10706580362000a0685100c0309461100180d490700034614408200e0f50003007184100d41900401a24011707806a40280d1180082c40041407842c821a13900600c00e0802c040130340e00000e401c03203 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 625683318 1250 625682068 625682077
    0x201050f07030504091b0516110a1e171207170301060c062a0318080c0a0b0105060a0509042c1005060f06040501140f03010b040e16090911 61
    0x20903920300149150815030410050002d070f64001004001c1d0144600c606911b201148040c4008101d0520520079028490030024868600c244000345d18040d605c4046420200b2640080b02e0119000c01c0003402e1810100e640b000400c120a80b100d0b0300114029115103030800b095001c0b101500000707010003848456001070302c45040b030340e02c0715580350303901d10000b01002d440c0001160701034104400c0c0007103d140c002c003e0365510070b13440c41800000c0110f5003d030010201a91008200034180c0081c00201c0d0b0a10017408000c84000007804640c031141ca400e03c0b41c024140c106070b1213640140121416654000240e65060f03009440c001042e4032007055504414603140b18140906800d210315285007000443c203201c070300011640500458861500b00110000010170391074001c0b000380420040742d80720716186601c4c8182e4001c2c0e140380c15000882c00c95150700907040010b20010004e010403030400244d43c03050b80850b0301c0da0351100440b0710201c0204400b241c0d124181d601d5450f9a03001406200c494102e4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 625684568 1250 625683318 625683337
    0x30105040b060108091c050c0c0d2d15140906090304030204020d020c0607032007021c0f06050403020102131202131d300f030408070611120103020907050c19020105 72
    0x246c0002c0f1752201d0060007548800d03006042c9003d61940c85455040598420050340d5010303440107100c10780c00200000c0210512440f02a42c6240054003001c200c03095221800301c280700c880030030702c400041c124200c0e0070000f0b4402549588a107040081e20f410100c00c1d681542e030704503400340c0d0b244001042203020380180400b02410380943c03400e000c000380c2c156000b019407014240314060b0712032741e04400c2502801000000707034200d01403404001d1281d10b02442000701038032443c140308411640791109070031600c00f22411000360b0340c0010b0756944c1545a003560001481203103c0f240812002e0347c08121440c03c461055501c0d10f454800700180d0706207898034400a0803000313007100e0000c0c1c03061140e0a02d440e80603580c805214150b0300c4400c842c0f0f03403031421155190001411980385450b00da40c0c0d000350b80c6c0306c240305684440e03036030861490300c04008004040d998107001c015586941103004000c10b0200c00b91074502401010425400421000302d242601c1c5040d0006a08442c41c580c00140e880e8469003a00c0b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 625685818 1250 625684568 625684603
    0x605040507080405010c021f0c02070e0a0203011404060b18120a06020d060608010f120203010f050a0203191b1b02030a031e0201021201030222051311030105040b06010809 75
    0x41107403056008407010312031401034000303110f11b070301e0710300246c0e2200041d500703a0f20401d405004545017a08a5040812079189610441d0011940e801c2c003640010410f9450b9054142c0005c010405403280c0440c099062800716020041c00e482e22000b02158861ba100354607518507081c10303142d03051f40c0e0002000742d106002429070748a40d00600d4040c00035480200c00103400b6151050104210f8826514503050307a00b00c86e142da03206402c2c500b0211004040a4007240c0c0341d907c03509118100e004030300820f40074000c0c1c0c0c44096120305042c9174401c17107020300603d0004841d00c0c00e0000408100d004660421896480c1020548000d0011000d1030400c0c0389580a9050301c83e815801d0200b603880794110701d8031500700c8022031915082e01012401d034416880d8640741681c1c002c0050026140088074429a400c034520390454a1202c0169901070350380803104845201c0d202c1000006001c03460802d0462500218003c03c0b4500d455580c2c0c00310a0b5001e80350504000d02c1000154000d00300308540b01c0100000c014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 625687068 1250 625685818 625685821
    0xf02031e010b0112050f010302011202040902210703150b1e0a05070c081f1d010603080a0905060708040e0c0d090f0309090915020c07030c0e0a0b1807030f06050405 72
    0x2400c0d40a00a00154180001c40c6100403803840c446503c82c80f40294a820080005a440c40d001110078020004900200603420040080d119140f13100030000140b41c41703004890301401c0440d04681d28001070001085c942050180b00380c03400c12104000030b070303418030f00c1c81500c0306a0034061305200d5040169201c210200018100e41c4290802c0103030240385c0c403840c0b031940310b16215203480d80c561004400080002d1482d1004254406440d040b81d22000350001a8214180010690609482c6035038001e0344c9c0c0e200c000544056107a84900143c02034230b0259403151420030540c0d070b0315101d4032540c07084444d2140070101040c881040181268820200440140f0540035542000e01458030035034000c078041070410300300041c044034500035030410035040130102012010084480b40a907000c410003050034003c0200100000b444100410054040420040c1541c542006000c1c2210f03920f040d068864001e6210000b042c0d0000d156055100e56607141c0810fa9800d2042c0e400d0203004650003081d0300605203070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 625688318 1250 625687068 625687123
    0x5060a020d0b030a150203130b07090e06030a02130c0318050102300414030409020a0207090c020c030307300c02150c0c150408070f140306130f0203 65
    0x801415881003644800c000d261224003c055036211000d10003401041d800440200411440d4050355200300c01d002804083c0b80300f41e540c9024054126a003201140001205104920891001644c0a50140d0040004101c9500004c00e0740514003084d50080d9161888840da003440b03a0403500805c54035002d10041601325141460113500f0100007105034080c1c51050140e101c113030700c26064803021030b8010000380e030b1200c1d00c071200d00b4900f4802c013035071a21040000188100c117510040030000c1042c1d0142008605003a02d9005542e2000305410840d0f04c0b40c0e030b05200300da9000c0206e034211648427181007800c1481c0c4c5084010000e02081d810301c0c10074603814092030290401031800607207200b281c42c0e14000e503110140384124021740035100d2443d40070440103152428944aa20140c0110f1030125082c29030b10003045180c4586604100a11099500704000d4509103c2d0101000002240542a80e03c2c2116100c050318041a201800c02c1500c41071280070b548050080c1c0003661104000f8a40c62441007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 625689568 1250 625688318 625688321
    0x1118040c05092206030f0516120f210c05070f05010206072d03060e0a0e0309130902030303040c0f0b0f0307050a0320040f0f030f030c031205010e04031205090c130905060a 75
    0x1214166500d010303581c0c600416607008c031542001d644550b40e0070060314440e903e4400201841c03e03411101d0380c0d12404208482d4000b01341c0c1c220b062009641e91800000345140007800d040b030950140487c11540343c0180078030f83c0c0124019034000024a805002e00c00c2815800d98404e04030f00001d0442202c0140e06084160f0540002007690010340e18440c0c141c9030059200201c40d0720f2108080c0580040c0304045149c80e01d2000440b00c0c00480b030001c1610026600068290383c01610120390322400307807a00700145103110052000a14041318100d0405603444940d004600c4003d02c5801007140c0001c00c100c503c0d002e58003ea504108911038002c1d103864132144551242d22034041e00c100140240400034005030b111036040241d9900144100072018156000d5810050007401101448450328030450600058400e4500070100d032402c0e001c417400c080c1006062a5015901c0b0240b0314141410400e000500264189071443c040c0d8801108504403005040100301c0c40d6801811400754500307010805a41c6d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 625690818 1250 625689568 625689593
    0x7020315040c0608010b090d031b021f0305010b030702030711060f070c17011505040b0a050904050303010e070503010302091b1b030405031002071509050106091118040c0509220603 79
    0x10703138841e070303605989501402d0014082c6c1c1200316400f080c0401c02a0000e445604c0b0102060380c100f00e08400e03600940d001a2091160030100301070050903500205d0010381c54001c060040c038a10904924505189000030740340d104009010f070481000901201c043c1c2c440c0310440340c0c05211510056101d004605c0c0042e1440710720b100d45010743e444681d0768403458406228074504002c040c0000502d091501c018000901008400d1030b6100949000c001b40ea62035100165100350f100e10003035a41ca6040000300d140c0460098800d80c01c01c40305100500058407030528094111080f0a42c1052054544803412402d100e052110030b840c0d505200700c00340d241000005042034420032010f94004170b4010507a00128040c910020340a80012500b005400802d548000b41d402c0c007840002c0b805d25140d450402c29980b102ca0804808603001410724003407140c91520090408044074140000458010010510301903420303014400d40010561450716030703411900c400b460180c40010f01c803030741d624242185092079 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 625692068 1250 625690818 625690829
    0x40b06030c060307050d050a090f0503190836070f081c05120901090f0c230a1e0801060e0906010e09061306290406090207051207020315040c 62
    0x7084110900c0d880d080d41564419422075884a041c0000b00d5051405414003030101500190b9898504012404030400e940150780500011541c2d45888800715001d005000101d1017002055400e000d0740e003c0c80b107200c0d0030440206082011415512031030440f43c0802c030010150034480c038240014000300445100d001c0b03400074016500c0c04104502c000320318009240812000078000c02c11065426640c01100d80c01c21508000085c1c02d84032076450381c140e00004201a6010384016804000070265034801a19409440b035074403072014001070101d0403503011030040c0340c2c524102c601d20401090201034200b0080c528580288500d9035035800700441204c080c2c07044020390040c440041007010030200703583c0c014a2031a00400e43c60b0381d02112280c0c01e02c8004001c440189c1ca55540300c1d00415081841910054100c210620482540c2d0030003003101e41540c4050711181c014421080441d101089422882c0000e00010341d035a016440002d0510565441180303450042c00c0501003031101c804804429240c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 625693318 1250 625692068 625692073
    0x50c0d05100b0303160b0408160501050a0c11070e1f0b0904050702161a04030506070f0912020102060a050606040b040e0901050106090b0a0c030908030a0521060a1418040b0603 77
    0x14030540c00d03d80c9a10406010038505040700c403981000441c80c020060307000d800b4403080b42c1022801200c507003000c0a03a070000d4a4682d150703418040040203901c40d00281018a0038040c034005234103c21651184946c0c4501c01c00041030310002038180200d03000348100400108445000720b51114402e04064015416180c0a1854070000401d41030001400101034a0a140700350410780c640000616074402c403900031641481d0500c07002000400c1004840d0041c3c83c00d131154400c480d02c2000c020031103017030381d8480c0303040507002c0c00300c5d90140c0d8000c0307078242d0000c02d4a1404107866991402040a030b104030707032000041600001b4002046250004624041c1d040c810081c40b03140d90343c200880719400355000b1807071400301c104072800420340191504212188213080c240305059039040c0d07545c11a002a000d40d40440c0e000101070300369186607850500d1088148040802c0c504100d80840c1c81d40e40c09000d1b0464220046642408603500d1686e200e0401c422403007000c5441c0b41610b080e0300b07550000d65403507020b40b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 625694568 1250 625693318 625693331
    0xe180108070512030409020901200c09070807140f041e0f080303040b15040f052a2d0409090305090f0901060e130935030601050d0504050c0d0510 64
    0x520f4042018941c80356400019401c0034100240b810096000c0d60380181442280806912603549405544200c140190060450100100188022003a0040c00601080f010f8010041c013143c024142c003002c20511142651100c50354220140c45104941101c1049201d10030f02103032000b0b10480c01d5052f0345810100b84100d551b1810701c0e659a0100741d4000340345100010010f0720682400d4002c11001c00c00500114190241d60442030880300155584681020042000001040010807001c4d980c945064910b180280710494006c42104000890384e04e244404002c0c50308242180c29140501100c400800c03080010745006080d5600c00f4a45a00503030040c44051928508020388904a03121a1200c0700400802c008000d00300040840780e103185503441c50040003080c6910f000110740e544010460b5000d1441c0e10103015400c05542c0f403c88010000c00c06c10040e643d01c0401d548490365942400701d410740702d40c0f60842c180031241e840d00e6000f044e542418000d0150000e48842240b00359001000310 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 625695818 1250 625694568 625694579
    0x307090f0605070209040f060603062013050d1505071d1002100e01020c0312100f060c02041d010e100c0f09050d050c091f0f0617070e18010807 63
    0x88101510414000c00c0b0140000c42c09402c1180340340b940b0900c51851440c4030340d400e544901c11a6070940003520015960507541010300c40c024542420341c80005c0300c4a003000c0341031881107421503a5006841c01241032109050801902c40c3e40031030201d07040102030100307141c1140c004004030405d0807000c4040000178065002c03401d01e0035007203080321650740c0900f0842201402c4c00011b0901540503817000c3d94200030755590400140064001d00c0e420242414050034510a8001d040500d500700410241100c03030100700c0b094001080742c0b18a41e05803408100b0a4004503014036104184003401c0c039a5080904603646a20007107001007088038804420000020065003c50f5034200c1061b0030360200e142e802c0180101e14142204501c2c1728880c1007101c1801e1818004214860020345401c0d00d007c40f2182c007403140c0c421545003500500800f90001d00300d50720b0140c00078050b07000c5c5036804071098400c00c0450b401c144502d042c580c0c80e0300b01070001e1840030700e4500c00840382c4400340709007000e601861401144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 625697068 1250 625695818 625695839
    0x109051501030c020c0a0b1305030105090a1e0c06021507090501020d0302070507031b15051204140708190c0f03170c011514090a0510060c0302070302090c030709 71
    0x1100c040320440a0030540d040150000c0a00c0c0c0d164105504c00d142d503914071a618a030060014101c0191655115401014101c0c2600d4954100318881d034100003c01802e4280066071552260708065140000e92040b241000c4400490301c0c0500300344105000030074003580018a5105131403241048440c0c3d982e502c1000c5450180502402c4e0050300700c0c6150402c8103102e07401a03c1c0c400d00074420b89036003903640c0d43c403110b034070f007401c50075444400d03500c40b041144914102c01035060140c503003851072030040320019000f50240001c0c401001000280070402401d00200f054101520b6080102c42a00d42e4072408060741c004085001c0718042080000032816900d2041704000b04e07580682c0700a04407501c800e80794440c0d08140b40c01e04941d0b50b103a400440c948101c8500ca8000c1c0801038074201c11503880c00a020041c14000c00a03441c80742800c051201c01c00d090045a0b0446410b8688418400081d14003203050409541c0065804484a000d1080065280b0021401107800792505074216590300090304 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 625698318 1250 625697068 625697071
    0x5160809013e030a060f0806010b0a20010905030903010c26281a0f0f0402090a0509040c140d080a121d0a0b0705040f170111070b060108010905 63
    0x42107011403402c0003000c40c12951510140d081c45520b1600700c0504940a0441d04115022000562104001c0010810554943d8007500c00b0102902d02503042581d42034042c854000780100304001c150b088001424032010901c882c8404200901601c405818001e41d03e8000400f00340c42075280c81020400b5030302031240c415140c10310548800d00d01c90640b402c080514801001ca01c0550b1224651400201e07440d400c17114504038a01000420135600a40c001c485502c210800340200f44070b49420f00c2580d80d00080f8120a8402c40d030250307907104003902003900c4004075400650003121104c02d00c010810340e64400000d403640500d80b000c042c0c185908016004034201c00113491040c040024100e514400c50602c1c0039441100400b2840d944101403610310300750301042c9000d07640c200c005203000300090910400d4220f081d528050f410907050140ea600344562a01c950700b40d0820b121a0100e074418203400158100d813080c24030b13507118001d0b41450f00c441c007011142580021080d00c000314181801d4403840e07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 625699568 1250 625698318 625698341
    0x60f10090e0c060304210f021606081302040f0c230913020a031e1a19090e1204031202060903160308180709020913060b0304030f050405040516080901 66
    0x74092503042d40d0901a081e48081c2040c2c2d81815002d4501880f917040031017561103aa0a5030754001e0000b50350768000d0030200c0c06048000d40c050798903000c100c429402032500e90400d64000c0c100d400c5064503c0000d006100e1110346603103803410302c80040912500446620002c0c1c2009014030040c0300c2d4840c2c207030060302c910014194030080c0341c54190013181095000d40825506414001030740140c14081000402100c1003030500d0a03250711203001c0c0c80844d151088640324050316011000300c1047c55500c02e070b050b940240a41d0990b600058185e94030204276aaa02611140000b03540325280d0411800700a8200010400342c420711002c43d181802c004116101c0350703003061000c1c64411180c2e0f42243d8140c1d015101540c81807100300f961903003490910904d0010a4103800069a803510710062051919061010390601850110100030083c0c92000710f80d07205900d454010441c040f00c074000d80302802940c10650304180703010104149008074000c00d004010040c1c599044036610350031241d00742c4411b8002d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 625700818 1250 625699568 625699573
    0x515040f030b0a0209031504030e03010501061407111c02010215010e0103020f0d02040e0c03010b06040b04030b0c04030609054207030e011b111506130e060f10090e 72
    0xc0012400c544940e54104240c3d900140c80e0100c02000280b07000d500010b071008240414052204040e0041605841d2160a03002400036614003074010b4003100d400c03a070101d03129800095420800c42a500900c01d00200240385000a8407425807103010108040412800351040e203840c1e400008c2d401000038101c0d030324400651196801c1d6401c0c00031040c65801007503008200b103c0020010303512809150034403080c1d000201401e200040415095485802085005003000c1105000424001c0700310f900380c9411040307500182d00c9201100f4018415980083c02d010314013003c94041050200b80d821140342207031401015004165550440031880340b407003500d50340040010312a0b82c1c03107950020340e10000c0382c00c00141c585081100207003540c0305450710400d00044c9007001905030760450280d2007000c01c008020720015540b155201103034900606034500c200c00116440201021542048202c01a03080648200c0d0402440d014400344098491b02a420341094000c035003046184180000b10000800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 625702068 1250 625700818 625700849
    0x3140910090804082e06051e030a14030309012904050c040902130833090c0604080c090a0209131a030303160e06040303090501110f0d02010204051504 66
    0x1000c004201500048510300000d100004c0d40349014400e0702c650020814858002c11124402c0e44a6981198650709159140400c14001901d5680c1121820380d10002c1c0618941e11043c0000d242144880d00180a07001030804a03482e240040081c0d0b020704400c80c000c1c0008108181103640b0a02c603d0b80c0001d103003120b100c90590301e14094000350b8115010f03411041c5010f81b6501980280d0740240c00c40310700c0003842441040700d80800c00c042e02e2082030a004844801c20f07030b00045500321500c8446100d0000742d000104000748014404d000030b40308001c210700da030b59a83c2c05640e61209c003c480790b14072860000000940310074840c000c07100c00c002d0040003403040b40d0f041280300d0000c2041191a03c584110750b18441103544040004600a508141d800e207980200c865004056030320b0842558003e55042c40300b0030000750001400010740301c003401c0c04a400c0b8010141c2c00d1074101d280080e01d0081c0b281b100f80207900c0790198000c00580d0f4050b20400c110305a0700c01c05050502c11403044000f84d980c02d24 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 625703318 1250 625702068 625702093
    0x80c0f030403140c03210408030103120306180e011401030c0b2805070b010f0f09021615051506130501111e03030604060e0402090f070306051906031409 67
    0x1000390360003886801c1850f46440010000b885039000314440705501e0f800000d41c1c140144034902c04540c800c01300b420341c10a5241540d40c9680c0c0d400180300041030b0044c010000301d0304600a8100d00c000c3c0180762002c64440c1c260000079030107842307404d020620b95460311200a0b00400002d1400e81643d80100350320000e00c0c6404e9500c5129444607070721810b45407400846505401841402c3c010303401f9990b44613034844001d403e100000480c1a4441481c614a88a04102604120b40c245046918040d401078468030210301d00091102404002401004e86004130700e80340b26207500403070044900036411400b0a60318400c1c40b0081c800c80c50168041820040108020f40c0300e1040b00c81040300b09800d540d9840804e07111016420542911881e03a50030201c00c11075503041a11481d070080144141c5132002d4182174000c0355421001030002170000010b10000f886441c00398101400070880506a20300b100c0f60301c0c091403000e0151b8014003001a040900346040d44191240240c001c1c24103802400841003406c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 625704568 1250 625703318 625703347
    0xc0309050d0807270305010501080d0c0803040f0807060501141005040302040b030307020d050d12110a140910050714210706140c1305060a050a0e0a03060513030906080c 74
    0xc10f1602080b9524180020040344848404020074034080807200c3c1c98118607080b400c3d100b058108182c5030f07000c1c0407042103056010080d140345940045000b56203803503a0618000d6003407042000380c91403500144880802002c3d41c072131812100050300300e445c0d1030030180c200000070161080034070000d442848240054a001c0d032100f064500020f003101d1410308203074045405181054010780300c580008258034070294200c01d0310040c003890800100001c141c48040b4401e140500c06c401c40400204d0355244c48100c1000c4100e5442c800000c02c1c3d9100319100340700c003c0c4a5409a5411101804c000820f8488890001000d60080f074810400c00d101ca10075000f10401504a0f001c10741e8019200c4444030920b481c00032826005046c040c41c0c196840712210040070b001134407640014019001001140100703a840020390b40340f490185490040c280ca4a00000c0c0e01c40e072150405000b0364504020700c1041c644034081182c405220b40c40c5c1c10070051f07807070805581d0250100c1c1c05031450b9400300080c808510741c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 625705818 1250 625704568 625704571
    0x9060c0309010e03031c1e0e0a060b030a02060a0f0908070f031104020306062502060d0615140318030d060b072904030c08120403020f01060b09031209030f06070801090c0309050d08 79
    0xe5103107e04070042e8802e0440142c95100d02c520b00d168001c02402d6052110742e008414900704140c000f0040001d15602080b25485000409000c2001e03030211001c015200301000c00003081020211580e0a45440c4044d00c032007002e102c00c5941c0343c0c625100e410319042900a070f07481200c009250750304102d80f1007a52110701c5000d0781110b6010100090f0000180c0c2e0b140050840b12404c0100050441c7c00d06e811200c07114084100b420902291230450801900c01004072580a442940c1440c1310052030382d100d0386140a40c03030585442c0da0400700d020860308404400f4000b580d00419450620070441000904180d240d0308e5039034503050b24000001c0c003090146940004e090320640c0e40784c1ca881920300304002058400d4901300c0c0141c0000b030301040c2d2400240119400740108100070742c942080d16002a40d00d10405424440105000c1340c00800c81e581400f400091000150648125103480d80c1c000f0841c010034004c013103c071460220410b019030710031f110f200303806a032080060502010174581a16072180 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 625707068 1250 625705818 625705841
    0x100f0f09050601120f0b0a08061005040c14040b0c0d05190804080d0903032c07031202070f080c0a060c0203060f04020418060203041406090d030c020309060c0309010e03031c 76
    0x1144091310135140d01c0c481d80c108070510100008400126408000c4000440c0e4000c2c90164410424000340c82c41041c4c1010440c1d208440014501440040c00e071902102d103203103424103400111700019002103281c01020896404800e8038250315030401305680328050044c611030030109084542901c03030300504415810a004004083c102100d4020700c07801e4880984003140045d0719000c0e88150040704a0f0051040c00c2c40b50450681b030788900414581e9540644406082583c20201e150b052074000d203c480702a0501c2090120681d803200c403003d5071814400c01050291003031b9072001403894401d006061203d030307008001d0b104603203a0480c0c014180341e000c1c009036405a81d541008482c00055810b940b0214459070300944c5903c0d09040c24070300350580209050481c0c1080c000c022030300801044841d00da401d80d05001179003100403c0100d1550048403102504200c0008008402010000140041000136078072008014004010b01d5228001c54001d0140e180031030f0b0000d000c40c00e841c0c02c242005c1030b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 625708318 1250 625707068 625707077
    0x306040b0414070f062303090a02040f0b0406080a031806080109050601020c042301080a030c020d080c01060b0316030c050f09030a17030906070806030312062106100f0f09050601 78
    0x2a214844e84207082a5a40f10f180403508015041010302d85c80c8110b1200300034100d95441c114078010582c1d54a0f8032540038002d209950303d0400704a900c82d1035006848201000c2c04c01c0114036100c0b4030300765442d5940030701039010890f00300d090712022400c1041c0b40e00b038030283d07500c014103070f46040b05640c098640030305903d0550099424a036801c0e1950300c070b154009045400e0240c00003503103000300703220180d044e048414103802002008001c25080141801e04c15419a0442c0d000109410810214000c17041d03500e00380d500702030001a00c0400107001d903000e84000160307800004c5034100d098044400415003d40441d4007448030020001c5100c000e04100e00f0050180d94104845a40d01912050f50b80030780c8680b0640030007840011001040a29401109070604041034100344000954902070005801c80b211101000130301d154a40c0d0a249407a000044172060341303054030050f100e40b201000ca441800b210b410220000b0703d1843c0d00c40c000c0441b800d4610b00e00c9140c0c200f10000300540801000340b410301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 625709568 1250 625708318 625708333
    0x409051c080601090f0308030c030613020414040e060708060f13050108010929011a0405060a081915050d170309010204090f0c120c0915080a06050306040b0414 70
    0x510140c400041a0100e40d034840c0c000786402c000142071440f03290044c401c101c54101090000030307800412280c00090f195140d035100e03039400d00010f140340d0411080c04020750010400182c0c94607104441e02040c1400ca81c28001380035020440c50395500c1c02c41c0c1d950002049c90303010602074104100c0710400403001030100240c40010055803010780780c00303911034078403a07645804203014010300c881109446e101a9495401e0340040f105540d00011341805144400750300121508000303150081150018200a0107050311000d4103000070b001d646045900b81101e036642450850201030521803502e00c54024a0040070302828942800001110000200da48010301801c4030038a640103c003851250349100d0025035901d080540701400d403005c00b122001001d06056040e1391003604240c4101b4198000d40c80002c1e10000b262003120104c0140d8805540d5016a94400b031000341c0c410a56485600420010311400360360b50149950340b2812a00588142400c80c04200021240000c91045000c01d50844150 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 625710818 1250 625709568 625709593
    0x18060f1c240212041e0305031506070b130309050906060f1b060f0103060f110720062d030c190c080d1415010e060a1808010b0a120201050405040905 65
    0x4980c0240002892440d050f403c100401c0034040f08114a84051802c440d0007080076a000740441c00701402c0f515040f007401222003c2070329243c00f607e1410348c001000748510700300003206900c108d51100041d00081e458190105903070510b901e00c0c90042c24050002c916000d00c4641442d155082003000300e00074000290000d41d18142048194003030a103a68083e0300755451481c1c2a01102c4000d04228149410062030b18041400d6038150b03a41e03260048620b0314107551080d01d6860210141d0030aa41c400008502c5240002c802080c0040c1d801c070200c96801e0040700c0800509003404210340b581545c101c00c00c42000c01c0e00b0084c07108990100c850501103000180c581d1003511381c0d00400c0c2030440b000d80d50811a8545030550301c2003904418508514540c1a800f07600013800e0019103c60140580c0c000100720000a00c1140194160300b000280c2d88981912003440078043c05403210b030389220340021240410b0180318034041984296058544034500f6150005000c01380c0548042502c85002b2034940001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 625712068 1250 625710818 625710821
    0xb03070f090b0a05100f0f17010b07060207060f0608010c05040b04030611120106020105041a060916022a0405010b2803020714061807030b1f0518060f1c24 68
    0x45901e0b1a01c40e48061b06400710018020307a075070f0340a8801c000960b0500381c20880303622100e6040d5a007010784e035a03581c01d00d030802201134852604020031452600300c03081145000d6038400741c240c40390341009108140f000380040325203010300d018010740540100800c10014a40c1e6005590105880080300c0c141108110448180f003000d070f100c0030140c0d446108100070849141651452415076803480750150074190045021000001c0500010040e0b40c1e1075242c07014020412804540301c3d21040920848611810090045000066a004600b0003001041107456102500e048890800348412015500c90300d11320b0f007503480c0004106165080150310042111460a18210140d41004010301d00b030a81ca844140300e014a180c00c0c036030300300903401c0c40001c0490483d035800100d41001c01c1c480d101c92581c0c01056030f905511403036210b20a03401e2504000e68242c80c07644201d204035030203011211400148455504005001c11074542501c1c003203000642c0740c008240c14804010880410516100308440 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 625713318 1250 625712068 625712089
    0xb04060207030224030f0a1d1606020102160807062007150e0307150b090106020a0c0807060c02120c1509031011090d330b03070f090b0a05 61
    0x40180c10071801030080d810002100035443e6070501c81d000007421030345a4100c00c0d0102402c038015400c00580458490304058129a8039a075160808407501d00e5410701441e500d8480e141d544a80e0314104000091950041c401d44441c00051000e0341c05408007075448255a6000c2d01003214402d6403006101000071800504012403548078035001d40c3d07140c2c0c0d41402c0009408050003041c148d4240340010f8803404021042c0d90401d580001607150128501302032001400110309003a03000302c8480c000140f210b40c0011b4095003140a07903500c3d10500d4480c510191241c3c10340c041d980115010130903040050605a0050030404582c4040d0707440d4081000000316034245440041c04e0400b804a20b50823186004c1c00551040c0303201580c10014510700385445011400b900d00d0840c400e0180320002814403903600c2c030900c07526400c07464035084040800024102d100580c0420b1000710b10f00009103540d400c4c000340740000d498048403a0000c2524040d040390151161400c503a0b0070003e81007000449884d00500c05 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 625714568 1250 625713318 625713329
    0x3010f0b030c0c01110702010e03062202030111070303050f01360e07060509011115040210021009050601210201140c030409090809041112190908070f0b0c07050303010e040c0b04 78
    0x1750781d19841c0d07000040240c0c1c46100c003503100790410f07014400c0320b010034189461807083c00030380d0105050311800000e00420007260800c3d4004130001c0c03401e080560560250344504504600c2049690301c1c1d00340603095800c00000040140d15545107500ca000142510001c0840c41c08000300744038a902100e2420044690f01c070001045d000700c3d94070140e45e0800d882c030403214508801000b80708245190500740c01c4000e440030740a0100040e001d002c1c40e100340031440c3d0445031394106200809242c54039550300da40034400d241010303580b40103080300b1404800603400d060345c0513501c8048861003035000c3c2410358044403618030988000c000004406405000d51a002d50044031901c0d02e03014044e003480144c400c1c1001c01005004100080d04d00d0031118580d1682001000780c0c41ca000c101611004001400f907268040c24548020881e1000c03c681410307008465441419000810784903a00c2c44600d600610304024110b406c00d00050040508548030254454012006541859a120090580c40d8441d4000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 625715818 1250 625714568 625714601
    0x60605100c1416170a0c030b0105030d0e09072d050c010b04020913020a051605030c1203070c1410020c030c01050c04030b06040203040f0c0906090e0303010f0b030c0c01 74
    0x160078004008041001e100e0810094080614415125010310f4958054500a04003860000001610400c1801d400c20740c00f1709031410440e100c0c18242074096007489154071038801c005011503018850000350b5401900900540c11944400324280d420074100304940d0642881034450040c80030000d03500320f420101984505954240c40e9500c2402e4450042c8424002e40c010040040e5545498503604d20403103150303100613151105050125001d120b500b0741058092040e942140c04d22130048000d2a48520480c111104001074200001042c0000c84104020034203810052020484958201c103c102040b0107456480e203400c4031103000c0740c001c2c1c02d000c0550b90000c00ca0a54001c401d204042e006000c208105007800d00e543d4407188a210001c004900464003c4045004c0244c00444c06280305d504c1345410011039100c400c2c0d103008103100d00c00d0f081801d0900c0b1209100d035001000312130684402e15250704046087c0390310038100e948041c10341039031100f0400944128541c00c1c4160b405c02c038040300d0f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 625717068 1250 625715818 625715837
    0x81b0415110a0b04120311030a020c010b092203050f030c03060a08061311030a0c090c2d0c031202032401110d1b06050f0406150308030105090406060510 67
    0xc0200500648025503003103902804521001c6080100d009074800d03402405506a0a48004118040d08051034000912440031007400310304c40a0350040d0005414120080100c3d05406040014081c41510b0051101000c2080f0644200d00c400550002c00d000c0e042c06840e00e0301902404105502c1107518008803100801400064689404d43c40002c2404100800090820100c06000e010521100400303011000200b2200c1e901c0501c014400c450300099625401e83ea80c1840b00f0150099900410005403520541c80c910749448201c070b209440720016840040200740c005070f4030120304c450142c00380000880070003080d9025000840c4101c2e441d102c8409003151001404141c94901d50000e0b052008c0c0c03a402c100d0514000840103440d124503d845a03291550003801103010020346005403541d0306041c02c000250700ba043c4001c1c0280d2140308101b220404251041000341e0f50350000038008401000100000e250071402140c205014032000100715940310005182c4210260022011071503100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 625718318 1250 625717068 625717109
    0xa020d06080a060603020306060d05060a0207020a03050d020d0f02011109192105190506060f01110706080f01050117070c1a070206090d1805190305070609090c0e090403081b04 77
    0x23001540040d0700341c0311081000e503190f07a40ea45074200100309691195010070011b00b955250303294140210740007000c2d15840350082e4030080d00e410071110800045000c000d4040c22041c4144503070920b4031b070900350302410550b105d01040741c000c14109050007103030080d140104140d41b1161607a40182c050803c0d00c541ca08240c54050700703101c05007099000c1d98101d41c5103800462804142a82d2041084900e044252000c0c070040c3d524801800521600b07110f00800800e01e69000110103004420300d0611710001da0341c6500440e040001c100340070940744200b502259502e1b0040460544683c4504d20241441c03010481c1c440c01c060007161144c0c0142d01072030a1080403a001c1c03081540241c131514211644100348070301104000b5079882154040c1c0103441d00c0c5004054200b00d51009140d10405036140256202030041c03c1c0031b0980148800a89003541801115005001ca0600c0c1c820107000d0761000d6a0310303101130300d0f2900001d203c0110341c0601241c0c2030f480c080b860000c1004d0f105521010304100d4000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 625719424 1106 625718318 625718323
    0x2103020a1704030308061c1203091a2e0b0705010b1825020c10030b0405161403041a1909050a03080901140a020d06080a0606030203 58
    0x162101e0711100d1207000410489000b581c07050350b5a01c4007000c100350f035086140e840740e072a0000102940001d010494000c5045101c0c10000f03100c1c04607072500800103c2030310600c4040385841c0d00b04200d1488200c03e03040c060000522040540da04802d481200e29441e00030a0f540750008111441000001d4001c880881800f41c040c5c20701021400d04100c0c48842550b126114448900310348200b803034082030604e09806d40740d0040a442c0480c2080c03040d5102e000829000700342d2288010070742500c0f1401058011101c0c01c2c840064158400c03401042c095a6003440da8030498200144000304401032111546440892802c0c10542c0340d01e504050b40c04c01810078241070606010312001401004a038541203203000341c680712029903c140e2403d00300c9003520390a007500c0495801145071220203502405601440c031800280d0a501c401800745810014102110802c0d00c0d68020720840c1000e = true := by decide +kernel

theorem cover : BRFrame.Cov 625539568 625719424 := by
  have h0 := BRFrame.cov_init 625539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 625539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 625539568 ≤ n) (h2 : n < 625719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
