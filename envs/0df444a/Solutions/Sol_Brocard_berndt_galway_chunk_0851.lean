-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0851
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:09:46.676547+00:00
-- url     : https://prove2.me/submissions/aec6d458-4e58-42b6-a26b-44df2e8db53f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 152877697 ≤ n < 153057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 152878947 1250 152877697 152877701
    0x30f02030d0f0e010e0304300b010b0a020c010e0901030b19060b04060e040219300c020d02010e0706030e030c0d0519030c120905030c06040b010503010e060c0f0a1211030703 76
    0x107038442d0000214109400d284a401d0400c505440080404e0560a09056042100c0c5c9203092300310341081c82031f030203507035a0007440d42c05034480b00c0350308018054031a20346203560180b00400c0312114060905401a070860f40e440c103000342d0150115075020241236401009a0240c0540000b818250814589913890170001a0500d0b9104803031922550052101c48041c007503541c10044562141d14040c81c001314101d841d40008202206d2408044984000314450100a5000602c5601041c0e00710f454801807007100f00d0072114082c5a48000303070030580081200600c00d4100540c0c0154460940c1e1501140308401d9241501c0904900c0200300c010800740b1044a1111429581040904041c440110b8001004290000340311222110340c3e5540104001d04c9020010385407101860300450314a401c0c6420080e0150200340329282c40fa42c00d011242551400c0070600364002c070b52901969080c8140800011510341008040c0790800070342d050f207044c800e2141d00550030122030964000e980c0303080403240207003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 152880197 1250 152878947 152878961
    0x705010516020d030504080909041e110a0504020c1203060105090d0b04060c0f050a201b19061d041107080706060e0415050a02090a0e0609010e040807030f02030d0f0e01 74
    0x28541742c00200004640a041100c08440781107070080b007036544a2800e0044070782c08610700056001040307074402c01c0103600021804040e84c110365410700385564008201c280d1103100ca0464540d084040092070703001c04080a940c000005050460405196102007408030701c040a055a40c181010180301c00d0000310301c20061041541e1811002010314a00c1c090054895543c0e82401c00032080d20300031074551009011a10b2087c5101910112210a0b10325130b00344403003030049445001c24030000d0480c0500311101c0740884417161200340d00c15440b06452110980c403508941e8000c2c0e240c1c00901c03640b154030402011114440c1160b15111310190403c102100c0309034000b6141d40d00800240004140c6a6449140000c2101004580c90355103034030780c0c00a030060044031900b003502040041100312015070414402c020584811155a0303076405a4902d00c05c00303503000740c035000c010403400d03000c280f24254924008d002c40c01128a4030601c2d600080483d4807c080000d9a07941c1d40b0301c1035045000a0181e85 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 152881447 1250 152880197 152880223
    0x5040e07060c0305130b0a08090c060a0c0b0c04030606080609100618020d0f060f140d0807020d0507080303160f0e0108070e010c0501020a02073017070501051602 71
    0x1012041c18194081d0503915944000340c14090081841c80d02d03820f0415084010f4101c0412958803200c050002230101c10b42a12040314078050121318021a0600c032043ea00140c90300c0e5550406040c503526444141407000c0e110000c80c40c0108000300109655000c3c5600030480c0784000d02c9076150602c21039040c41c0c0240d1411044504002040180d01602203c0e20000100700740c0059071603201c66000b000800107035110000c202d040c010f00088000c142c1c82c0c05000c54841140d030450f0807010204100c0e0450308100c00400b040401d02260300941486841c15014901c01c2c02110401a04c81100901e960812075a00c154070100000c030010f03055011103090011f04c1d0750b003007840c11030500e4000039207400f10003085201084a4202a210030303a104200d290040c80e041002150383c0c4a410600a4840d043d5005000800c16080001d94000e03802c0000c0103069001c4010b040c80c511011b5666014210b1040b4100401c04424495500070820a201d018003e00d40c503c0700181c0d41d00303100030203410461684400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 152882697 1250 152881447 152881453
    0xa09050115030507030902100806030d021216051906061d0601120e0a0b0f01140607050d03023114040902030316080403080d06050901120203250b070305030105040e 72
    0x410121901e0403109501c10454100400c181e5200c8004400415481034060b50000704a00700c248080d40004010303000e00d83c140e0079245d240c0019102039980b805106103043c000b100420201410101e8505c1568409200d4400e403014241d03201100303100d000608405803840b6035100800c001e80101e200b00080b0106421081e9180c900c0c0c49000a8250101144094132050320f0b500065108403062000e44003495010703c0701c0f211401c0ca900c0c144840d10090082d403c00843c80841440203291901c142d039980356100b00106410016101c045010303402c0800e0148a5111408a030816101804400c0c0184e6220a1074080c4071841e0142c00650320400c002d10758040c2e480c2800e104050780b03000c0201c40704416611050004450f07030307180802107403141e0380c8040e21849003c40c9015100c4007035084042281d01c1118071a403541d8030749140354600440070400a500d503100c10a0342025000c0402d1008400229946102d1159580d0f1001000f5a0026100b1000148000011b000d43d140520803044880300100017 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 152883947 1250 152882697 152882699
    0x1060f0e0d0b10050d0605060f010e0a03030c0c0e0a0209030601050406051302070206040521071406040e250c020310091e082205010206090f070909020316140a090501 73
    0x214605601c03024001c0c100d03010200004a501c003281124500400000c0c0800e43c5c411700c00e0a202004040c00d58a4910492020004441544c850040c501748014020701d0f540442c0d18541d010750f0002002c080485800306803040003e600340d06444044c0c0b00351350710030b00940d03030f030911700101800c0400580200d4030940c40d00c00240110344031030714000c800942603c00143c1d0788680d800011080c0c00340c3d03800950301200042c00c3c00b00d00c2d1103032003030000c0141c3c01500b1550740780d449520780d03030400c110280c00b55000b03d0248420424440b000b41c0c1a13400038100040040440030b41d9843c0c100d0070426000c0f10000c120301800440440c24204074417480c01c4403010f0100006089950740600015450341d40f102c0d8406000c052106100924045413104140c00e08001d031015610034422984c0340941c40340c1c602501400c400148640d102260392400d0034050409810a02d0a01e06040020700000d02c00340c0c0c242c891916807038201c0390352201d014060401030300702c0b0b000340000c0710030004901040d4114060840c00d05d40 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 152885197 1250 152883947 152883949
    0x51602031e0c0601170607030207110603041e0b071805031504080d05090106050109080f0d2604080d060b0c100203040f060513110109080a0f141501060f0e 68
    0x256512010038180107150101024800d0360603001d0101c208200d40180400003507101921309504520708001e406880c0c1c0c95072069400d400324000d000028140507000383c00040140707040b0000319407091142c40750031154868071229148249030307418102c580c084000c0600c4504c41c0c00891200564040022810200c2d08000c00700e0b0311180c0c10340604003052107100c0818100070b0a90203075400301000ea801002103140c16444030340a4401846100d01080c00740c50081440302020400c50760300c10f0810000c00343c89080d10001c07180f030b100702080340c001c1c001d03007440202040c0e0022034083e0096001c1c1e91303440c0c3c0b01e07400c0b158600c003110300c240d0000e8034030641003021200e50040442d040c0404511a4001078693341c950074102c07116414450f0040c41c0d9440d180c03c114414074000c96084e00c02e8041c10440f5138050802006440d58442800345140507884001440000385c040d01a2102c16485000c04801502044151515000594800c030f48a541100010710074294000b40500c034020013840c0c54600c01103104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 152886447 1250 152885197 152885203
    0xb0d140115090e041109040809040f020424021905030d050903030702060a051003140a150501080304091808032502070303081501020a080c07050f0a080601060c050a0605010608010801051602 83
    0x803043c2c02c00e5800e0b000000d414410001803074030520001906800350342c0f40601d040900c9900420000703100e940390911210018000b8400e84003914000c40f03000301d03806100c0c1203c4518001c818280800c62280c0c18072440c01200da0780d0344803000c40c860700046454100242240d020340d1401401240c05600a00c10484420b500240c40ba40110401c04002680c1c3c031184803000c0f41c0382117138201130142c001d0600b800c41400000147e01803c28002c0300c11864400d0301ea820001039603400e1203a981c10fa4020721040c004942c9075441890510019211491070760640e569a6030203800403141540a196000b62019a022004125507007109980c0f021703244240c203659010b80b03554005402c1c66200d60000c004881d09900820041c0160760300300c102c185e140c40e400803c071a81c800301d5005040c01050202c2444001c0d00f00104014255041d0304041e000a030309001e0200c2d04d440344120b0645480c45010700c8000410b00d6486400c2c040e00c1c0541e1460716560611001c1c5017540c0014150f40700c01c5c55112201a5140e5005c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 152887697 1250 152886447 152886449
    0x506040c08070513080303010e09010506041b030e030d0e0304051503040203030304030c020d05060a020a1202040e07030c090f12021509100e27060103060503071202090a02040b0d14011509 82
    0x250030002d07104c044003110030b2015070450304002e80c0c9100000c00851514005203805100b101e8150080c0080d40e9124144002e80e600103845883c1015040764120b000d90090b04903101e130350351100c112800c0c64140405101503e010300d2051150340c00c001014031040c101074a1410f902c800102041e440d40c10254003203607982c8030080c40603040040d64590f04045546039400002650b41010803107405003005121200250700941001c004100903583c0308038a141540255003c0f110b0704d0018603826510040250040c1c041c809800080140d1900040390b00c41138a001c410180000305010501d10b07140d0301c14440302d0440200060400b030002d10583c200c1380c0d81e40001c101c4502042c82c2900d030540440b4003140021000c031b992003540b2048500d00030000d4443c1c0f07110320310030b420076070301808003aaa981c141915444940130b0400003008540c2e050005d414408a441e422103a54440107182c99501c0c5544049904022041c0e01c5203034407401145c1200c000a0501409406007070512802211040c4d0302034618615 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 152888947 1250 152887697 152887711
    0xc01063b1302010c060509011406190b030a110403240501080d0c050c12010902030601050405042117040f1106040b091207081606020105070201050712020702310506040c08 75
    0x81d914030045900c60541c10241a512100a0046003481440c1601802d2000107a5011200e040002103070b61800507604800d6548400a000d1b40c0c90900d440c12050f83d000130b0211040c0d80d2a002070700b40c1d2401c010010002107008200c4212880b1500b0800602c00c0c10a28181d202241440700500c0140c4e40441d900e200442c40782020801001d007864801d05000644458030362284442c00103108903503040d040444200c2c0f084041c0c500e503070b89605c200021180c09480c084d00c074205c3c41440c0b042111800c0b4600181100d541055201c0c46890400c2404000302102c040342c00e43d6184440c001082810001d00c40540c1c1c0450340c2a00b405d080c40203200c0c0900400745018414104080f50300070408092100401070503190040d0341000d0712042404c011641c56104001c019032070300002030b0401c1e1041c86258060507032903450120002030740c8481c0b8080d42201c507060b603112820081600804102c000d044040e0750200c0110b40084c00c071071030102b04450300241703d01c0c041d0742003038008241c041d4080005d540c0101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 152890197 1250 152888947 152888971
    0x608191101090b1912020313030801172802060a0504060305060f060a0507111305061201090b13021f03050a0f06030b040206030c070605010803030406060801200307050c01063b 77
    0x151310f40b001c485030303440000d030400442e20010510020800c000841c0707030781500a41300c84072141d986441c60321162100c00741c04000ea40149002105084480c5944c428400110003c900881c140c0c0d0006062640018401c1001c07640001c2d0800c0003d42602800780c0c01041210704013498103200010230001c0c07207580020800c1000020701e0340c04000c0480400d14402401620300007403058071080040080c00d0549a052013031400305101c101c6032505004654800f60320910500c3c05482d00300d650281285e2050003242c0c4210301414060103401d00100c5808012410380e00452242005007298040b1400402c0c211085810300d1010b0000c940d9580c0782c00e4006074191921340d07a0f80c0d600800043d06000e031a0005004600b01000002e0401000002e58000c80c0070b1039080080c0c66403080858203c481c1018800110701103000311100e20003914000d941d20a100b814800c0c541442d00c0001821a2607a42050300342c9800c51000f00703039403640c1c080c60f0713050118540c02c809203031101518109000352000346240000f02c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 152891447 1250 152890197 152890237
    0x6070308041506080709061a181c05030307090e01080a2001020a1e0201031a030d18050a080a0c080114040807020307180e06070f050702040e010608191101090b 70
    0x70b0303a102400420000003031301ea03190b07200c900380c02c09011035110728058071009200803240819403078111400d805c01051200d1401030b148007070042d140180c03441c50081d05000044100411000e100a602c100004c0d039034001064184100e1100990068100b40d0160b440840b09400281000c034484c904c0c3c9107204408680c8000d5240101d18005c842031005280101410289000703044c01109501d803103100b601c084c40340001c44000301c90b2909056807581d40c1035100355410300c54103000304c4200905030003c0718071100711b54449000c075014107860740c42444a913100242c90f00500030301061400140c808440203000c030412020501c0850300c00a0000781c80307444006260300c11580c04020000c0200b107422420030b000d800d031450040c01400c070782402da8100c0c000d5000003000144150100a0700b81029203c01d428110281c0a02c0000d202c40c40060080d59030710070003c2003100040094400502e80c0069120f0b07200b403186032405200402c1c001c018140309035400c0034884a1042e03c16510340b4200121106204 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 152892697 1250 152891447 152891483
    0xa03140f0703050406120b0a0905070e03010e030d1401050102061602150f01060f02060423010e01090b16081b071e060e01060803070215030907031407030c050607030804 74
    0x512500c04100300103a00014208209a0041c004d0021510203895038100c0d0900c4102c3c22044d80c91054096611021380c110501091246038003803900006113161020202480c18082400c440f0310821180d8503a0000c60910b01c44181806081c02c0c6585159145c0c10304c0d450540048e6a920014204803401c101030141342920b00e100b000041d85c0220f0380514001c0d01e041c82400564109001e02503400094122040d180e030103400000c4060107250b000c00c0040c82068101c03003560703158094404005075552900c58480d0101824011400c50381d00611002d001070412026018400b03d082d0a540144101a003c10001d51045101034103842050207507203644184034901030000319091342d0305000000c06641280b090102070703400f00d1244403112008011858444280d80e50300d000d40c140007507211740228801080421201d02664215104004490805440e030b9511050382c0c07400000150140c0c0f0070b00b010020b102032418058003c12045d41e09525008880d10b0041091500800c09800010095851800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 152893947 1250 152892697 152892737
    0xd1206050121020322030c110d050d11030f04080d0e0d0b0601030c03090b040b0a060b1204020609040209100c060501050402030c09120c120a150605030d08060310020408030a02070602030c0a03 84
    0x3000c5c1070074006454800551401800d5260031446c141c91541c6110710003100c600300b1f10141d9188039003040040415412030302007105c10a040c01680d04841c0024411282e021000c48081d001410004021b0012005000d00081000c1e01c5d98804c580700e00749024281c1d0100f100a001950451028078003c104810002410303405801c000354005c1490303100c1420001402038421105000e07000e458070510a0a40d900f02c02d682a00914102800300c0030041c001c1001480c004005000c0500090303c00f41c02c041207200050070805180111901040300e00200d4020010244030b1a800751200301c50031419400c3c41c01c9040b00c180640348055004450080c1760509901c02000340740390f541c100400c084803800ca014010354460780501011161461200c40c00620f0164900070315050750300103402000c0d2079400b21401ca07031541020301140d800d8040e4298181680c010b0780000c202400100300210307559268850000d01e0107080c0c0c2c0c06141150401c1c0102040c02d000499800b81307035a0103140000000303850740381d0082 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 152895197 1250 152893947 152893981
    0xd0201090b0f0702060307200606011407150e16090c1b050f0d03091103060606120a0209031006030209071d0f12100902010f0e0603180109050d12060501210203 70
    0x141c0315101004002c98141d005028082d803103060748c80724210092020400e42e9801d410355540780446c0c0449040300e41c00400902800020b800344060501d90b800c3d0100250894001da40f0101480d0030050591071a4164404944010121410100480c10f00440000e08030708a6a01c4450405101030481c07003800f108020501118094005070780301d0340101d9801900030160320004440c00c0307003c6103c0c20050300d03002c0752191040c100a028039240c580b607042558038041d00180b5410007290309102406258808214040300c5141d1902b0014129095004018207102c0044c880004c008030941a042854035400032500d2106040e100c0c02c0c42c030a21000010280c820651030f000991050003050420100c544d004509014000c0c1c0360645590410b1208850306800c1c1c3d00443e4200c00f00b040440c800c80c041c00043d07200002407000009840d0301070340c1c07950304011404420200150b00c1c41c1c80c0f01501006445000010482400c0150301421181c1c1c02c07200f003209240c80c81c0500ca90110004600d90040780f1110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 152896447 1250 152895197 152895199
    0x30902040f0c0203031506070f0b090f0106120c09052509051314070c052d150106021e150603070b07080703030621020f1c080c0c0d0201090b0f0702 65
    0x1c000b00101280007542c0e030b0000c42c0d0391800b083c411005100c1c9800c2c0002210401900b2036032901c81400c0c10748840310040f5000c0c1060380d0754440c07489501041c0030300b0302c00d002c094840c05444607500512802c044611450542040c20765500d8030041c4080522550420659404000d10b200542101c20f0740075101008150300aa030440ca000420f640d41807490f0344003120703213042070003e00004e0b110316000312058814094020700303541c030069001c0845e10301d10030060070701c1752882803040c90640303a40c64840c1481c000c220341d07540b9000301e280148210b40e018803414011034624041c40701060f0003501030603500c43d002005400440c86c00e00c040340240d10148001c0707001d443c11441055aa103070503d01019260b005207002d80019117819800b04981d55000808420701840301a401e00c03200240d000c0081031040d140b40603501c2810070b0914107280940d0386030079481c2e40c000d03009951103506010103241004682d45803240318020303199002c00140c1c4c0054801081d00d4017000c0058441180c2d41d07a26519100b40fa0010b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 152897697 1250 152896447 152896451
    0x804170a0801170a030203030a0f060f120203010b040e030f0d0f02030405030d1103010317033102040b030a261312030201180c060c02130501080f210a030902040f 71
    0xc4003019400c46400d904903104000e002c8242c100a0140c41d89691502400074016041080462400e0300c80350030081004110340300c0000c07004d5454407907280740742c034a500000d4056140000c150941c6028482c813503e84505890070b00c40c845510100c5501c900c0380c0e041e449511100130a04015804990f400722001800603e0110340c0d03410181071040da2900b2030141d01410b2810145044508081e25056030304984e80a065070420f081c0c24544041c80381c10041050300700d440c50080385d1040c0d800003d070108065a20b9108103036559a58014030007910074a82c03d540c0258407901c602d2000407403281060000701045480c1c1700011443c110004541e11030068811031114985d1000315201040b802d204e18014481d800810640044110390282e0388050000034000c10340b1100c04101442c0203a01c0d004c00188001c200c0041d0311015203c00c0c01716403007a04060010f40c8201c0405415080400004000040c5104100c10300c05106000b04024410f0303002d82c1c020184c03600440b80071034545400c1078003143c102d8001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 152898947 1250 152897697 152897707
    0x806010e0a050a0603032f010504080301050a060e030715050d090b090c03010209090f2a0417010507020c060c12040807080607020a080423030102071101090501090803041e03051911060c060403080417 87
    0x7802f80d681007070003124032612400000040807401070408500409010b000b42850a02e002540080c081014800100b403180400c02c0e01c079580501c5c4900842148600b42d28821400c000c00400d280400c9071600500981c410841c111465803003101e22540900d44e110b07480b102da965400240c403202d421080007002c6d05540d1110740c5004107040058400d41d001c00d502c0e1500f07403c140806a09072002134441c0d402507080804010194144500184402c8485504840c0d180e80079240040e000e40c001d80c8040c043d40c012902c1881110340c14044c0540005851000700550032071511046007a01ca80c3c4510440840582c40320300c5880788142ca1650000700c02030007151034480a040c00901c520b00c074008940081c0b00581c0100d02da6018804102c280d8000c000210b05181c1409640303042d0710030382d603010602055692800000034404100c800003645424520200b203081d076180130604c05c1038030314100d4820b400030b10010700007030000510b1503841501850880342c180c8030760070b01c600390b0008042c070355061030000a1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 152900197 1250 152898947 152898953
    0x2091207081c090605160606170c0f01181814040b04140f07140303091504030b1b070201050d0b03010f0606120e0c090703060806010e0a050a0603032f010504 69
    0x1809100d40c010301d034040b0410060588212040010380c080c00c80030440920049541a0448920384502441900d00246a94865258941070300322048d4903021641f0403d008204d80c00d081c4101c15410f0001c0c2080c000d801c0181c01043c409100e0360140d411403039240d4800151081154101c08000606000c2010503400d080c21700203541402201c4c281c40d5000d500d5160f08540b00d00203544802c10841c18080c103030450414080c00a1f0309445a442549444180070512081e6503194440a5907611044595540c91a510742100c101714002c041c0d0b81040c0d0b00441505840d00c0010072550381d0350382460500e81d1080b0900344040204904c0400940542c64461400074462083e442034090b1905a111484101040d01160040d1900002c401a594210065000e040d0410003510341e044040fa090228209071641112460400240d10200c002c11640040c415048190320a0035006800d240d414454182940c401a0100180042c1100c0004c02c41140f001002c040058000744c2c0c00d0440024089400c0c03901b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 152901447 1250 152900197 152900203
    0x20d03030219090b1b0c09070c0b091b090a02130906050f1c030c0510050c0a1d010c110d020301140108010e06010f05091b0d0f060b0a080a0209120708 66
    0x44035541409000b5061000b03041e014822210484000c804c20524041c0100c9116107050000c01e2102d060303106035400010703d6654a10503502c00c40c500c0e62454102c10042c00e1192046030041c6c042030701900035401510b162080303010003940c0342c0400e4840200d07070b449910400000348582d0020074443d00c0c1c0000c0c0410310142640040b005c80d43c04540c0000840030500401940040e1412110721072052070303540d080068015400c01301400c2c0681d05581e040c0602501d40340641710300b12180ca401c400c00207444400c1c950024400d000e06807101515461070380c2e190002a105807804071010700400003c140145241d40c03210304201e06142e02900900c1410102c8528a580140078041d40465501b00f218400c20000f0001d1031307078126150301e604c100d0700714649020303c82c0c1d41c003000c1c0505d041000e950151600003050f81d1f004000e40121040300081d00800c41c8520000c0314219009040585001c01030b4243c0583d00209180e085960380d20b005a48008010018410b03512002c400e100d43d003e0303041d000452541c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 152902697 1250 152901447 152901457
    0x1e1707020d0e0a060801090b0d0506040602040305150115031a030d0e15190804020102150f072007061101140702071a030f0a090201030902090c0a09081b010516020d030302 75
    0x3a442d181d086089100800881120358000c54001500000042000d085c4541280d1309401c00600108506522505c07481c1c245802140e0070780c0c0302c503000030341001000350400c0210020740c0d45016981041d410480c040416450480700700f0101600e5052004031202d08643e10340c0003440c010100c64070291076900192a01581012441c856404132202407442a0508201c0702c074080040d4030758085907107098069400361806001030f41140304480017001e01d008581031440c014444d81100301d81501e42000d004007200741044d01e00310f04810804d2420407906002894006036001d504003511603282ca20314250041c0114034610541b00d00d60700c2881a00b640202d0084281e0301c4494a071001c09101d103428885d5444183e407c2c00c170070550113000514038091036000105585c4145800b16440805400048140d90203903000910304400140486280e500032140800410b1600007038003480e405520040b00102c0d0014034107050010000320b0b0405402203000c4441c200760b00401807000b03d40d203800c0c010025041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 152903947 1250 152902697 152902723
    0x30f100606021203010609060f170a050f0a151403100204090209030f03040302060712111b010e190302010c030c14060412051606020f0c030d020d1b1e170702 69
    0x90f0b5a5400c501c443c1501c2203a0595001c0d0b15903d08aa00d003000440306020407100403401c001c1d03540912452607984a103128085c400b14940402e0b42c3c00c0800c05000c10341030180125124600d059007042481d4002c10480d41110741c400c0aa80d4190f80810101c1d05040411501502c0c180c80000c000c12505a0f5501130000382e14150121800508401e0040761750740302d00d0001030b41c40b06051040d10009030310f04100041c211044e1a0020543c0d01903555a482c5c419005103249074101212400440d550f80100306101040040300d407842052955001d107040c0c100c9500002c0d04001ca45602c110a0600481c007a503005503124040c01400c0d01040340761911502d081d40c04940100b004001e0054031440b81c000d13070b0b40d00740c00c000e5546a40109907a0f1140294410342544203107130424804040441c000340040d040f030884041300566155041403a25040f980040030540c0a120700043d08039009500400038420116280e07040804074010620549501040c0c00030781524400500c10068029404a4100d1354401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 152905197 1250 152903947 152903953
    0x12040506100b04080a0803060d0f0309090f18060c050c030a020d0207060c0b06040f0b13050105150a0f0c210c06060e0115031808040f08060901110d050402030f10060602 74
    0x140b54181032600e842184070b058030340d5105101d09004520060000c542260006103403408611040d692200c600581d90f6050b0045078050b0030810001e0507600030700303a01e581c50724020021001d48804850707510382d40c100c010386a40d039140c2c0504110703030041c0d0480701c0036480d11003201e0b1541d04200d0001c0d0b541505520307410050054110000d2260b0150b281a441c0030b50200c29423401382d0b5508240b000900ca0a00d041540f00d86507030a24410351146201003ca0703000e010303008100c541c146428000d140f00d40000200b40b515040020202c031552254420800c5035a034588024110382605280c92024031440e8007004e0004032500c071034045900007041e5006144900800d11045030740d040701300c0f208503003403107110000220140710200c010b21950010744803240b1009840006031040d00d5503c400c1e003050700146490381d0348440600c0a01810401e0640c4082194000d206081c003910181040c0c4c041c80d421030a200e9110700200c0c04540d0140301083c89245080c0c00c850b050f548101e240030291220344212801340c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 152906447 1250 152905197 152905199
    0x70c0b0f041809020d020910050a0b090102071d01150302070219060f020d0f0c060e0628060821070611030a201e04090f1d01091a0a021204050610 64
    0x107042e0300855040c1a0010700c1449402500d8080c08005040200b181c0d00301074440e50040b92680d1000c0c032103c0580082282140c441e10040b00192501565030000c40202e01c0c40d090040d08046a240903a0554105260040b001401420168081c3c018048001d52001c0542807110b41001c02840c44412a070140d0b680c00517200003200e080e41c45200702852040010000300081128074002d99402c0d0380e0038030a401c0000d40c1584940140c1c1009800d82d81030218004128182c041590500703815060024140020442141790024240c1e40c3c5025205003042c520502d1000383c0305080d49800c1d56000c580000040c480a090105024055401240c5844043d858105416405015074840002606001000c9413902c0e80c0780242c0b244c0c01701150085030b58042e0410020801b11058003800b02d14284940c400f0400c501038003400c03117040c866100310b0036050385400c100001003601240389241c0c58100e0705a40c412a180c0c8601d4001a1068981d010001c170b490101b8002085000070b0361501c079078095940c0e25501 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 152907697 1250 152906447 152906489
    0x20a2102070b0a020909040303053d051203040603110903190201140a090b2206090302032a10030f0204170d2d20010e070e010f0605070c0b0f04 63
    0xc0c001c401000386c00c44030722000200020301075400305030041c88407401c121040400e41c01c018100300c20035065a5408248011003c00b1605100060018000232640c1040380070b045030700e0790750f0ba015620034201015100d400c19001c1e40c149504440108002400f03583c0103e000c0700000d00c1c511228402240003030040300c80d02245103424015507400e6800d03030791a03d148c030b8540042c1580907000900300d000b00f910520054250000136590080c000e080a44501c0310662a600405007810500182c00c0401c0b8034000d44a058406141088201e207403003154000601038807024102c00804c0c1840300c5c58486440040c021689041c2010000c515510440845125200100040398505081920040071440070500f5100300030b9404945101c1c241c29181651190101064000424001c0019404280d54035944004140c0c1c0600c0000090100d4182c880c0d125490001c2d114081000ca00c245070411801143c41300c20460400b060100800d5200d080c6a103604914100c06119070151150548001040800004e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 152908947 1250 152907697 152907701
    0x50a0f0c080c0d0e03010e0a0b060402040803070b01080c09040b040308090703050105070507050f010e1e010912030e06130c06050703050d02070804061b020d02060a120c080601110a02030a0303020a2102070b0a 91
    0x1f855403400054260558199900182c0c00c502500180e170050302804041030030f00d0100045d001207405000004c42c25450103001605100c80d04200a020320091010000030070014011140c01caa07151402521541d80c21000504145150300028840c0d401c150500450310741c03002c0a00394290084064070301402c45d10101c5130883e60454030401d09070304486c05c00900c1884020588941010580000ca00441e03903036600d4603010086c41c98035010070703603850750040400c82c10000c0b6540002d011480c1c80c60f00031280c40740f80c004106842103008100000611104140c42801510415550050150b484d08102d14200c2e007030f0f030000d01858002441a48105922040103181c164586030050001c1d0080c120700c1d000d01c000f80c0d01241d0100e090120700341c1c10400075140d0780b1810150b408156504446400c101c00018030344020380314120303266840b040d50b1401594002c65281c611a52609006079607442861060303c00310f6214262406038002e03c104805038444070b40051001070310654070a071440e0754802d00307001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 152910197 1250 152908947 152908961
    0x216050109180b0d0606090606080c0309070302120a050a0819051201120c0e15040c020c0310050405120a0906020606040e03180f04230702010903050a0f0c080c0d0e0301 74
    0x1090014442c429049808580c01200140b401038210304840700652070b1070094400c41e501007a13407541e603008200312050381301c0b1020707410840c81d03403005155040402c845036a6840d50700020740b24030414004d10340480700402103c00c0455000301515841401400d2608041c0c110176520751a50303e200c1d0301c031880a48203000701d600403240641613002a03400c000305040d07405108502202c0b076014401d008a40710402e02c0085103d085c41090081201900c2c41c18813042e504904841c03000e5500c030070024180f0703a40c04207200408984690300000c007076850b814824600510b2554010b1100c1000485c8802150301882000990321650202e58060700d56200344800c0395003140c030f400e809820074402d00c2d50581154210a4840341c0007003651403403241c03503000101160034154100700c4222460700f007510030401140039039901281c5800200040e41c1c02d91405001c41c07080c0101c0c507013044091a034200000b80141c451100c03d44e0880c0c0d6150310746e110265100c0c0d0343e0034291030010100d061000080350510301401210f07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 152911447 1250 152910197 152910209
    0x46090510110406092702040b030604060504020f070f080409020c06040323030403032d02090f0604031a0903041a0909280209010207090903050301150801140609030f0703030216050109 80
    0xc0307111707140c001c0d031240c803e2416005040c1d00095074400421000d00c0d001410103840c000302c2e5540d40341000c070100811185a03610940c001d0340180031030114482c502c07040c0d9401580202030758114046a1804000f85d10664102802403440400c6501c5101000240d55106510944a480e04c50444000c0c8a20b200380201e02c41004500c1040000d001900c0fa40080390300c01e080b851a400e8698038440d450701d480b01c1085001d18080c0d804268240646049064280d0b031010a9034401c0c40c06046480350140511501108007070503a5503004a24011801c00850f0018026604114100441c2e101c2041c080e40c050301c0b400b440b40c0303003d0010400c0b045104031010a144640c0c2c1000808001c0c0b0200c001c0650040288103040d40141140018091024041c11080c2c500c40d07030302c40340e0b207604010101d64540d5100100740704103d000001444008008a55642a40c2c2e08a8505031a4200d02d0002454000548203080542c01034000000c209a00001e45d039440413026420b0403580341d01e480c01104c0b486490300c110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 152912697 1250 152911447 152911457
    0x6170108061302060c0601060206071d2b0f0c050a23120a0f0f03081b0414060f070506150402071e03050c0604150546090510110406 58
    0x20a0040c0c101c500b4600700b4a201506450400380e4090540742041c800764070500141e08107008002d0f510358008406440004001c160794100e5503031801164118041c0c15082d0200b02e0401c8014290f0061103802e8801268040d541002c4031800f46090194081c070303807203043d0044100340000305621029005170300c0340c8040198601ca803844090108013003128071503400c041c0c42c0600032400010178020080d03588410301500c040718601d40c0030f00c0d00a00541c0e0003014031040200c2c04d2220711560b801c01d030480c1e049800541030281503151035400101548103644407200388100000d5440c00300308010a4243c404c1011191048a03418050280000da00c03c00c4402090740411749652170441511019581080e0300a00e481c07420200d810454a207040004d540c1501c07203100c81050b044034000d450003a9030b80034440b01115500c0484c0008100c082c08104045d52402c514000c0d0307014040c48903610100c85881440205000c4501035040c80b40d10b940d2621b030400d000a003040c41010b008840301080324121842503440d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 152913947 1250 152912697 152912701
    0x315050a1503050417040308070c050d0b010e09070504020c150a061424070312060605070305030f0a0f020a0306050a050405062b060603030815010c050c100302040503010e070617010806 81
    0x4030b004040050044a02d0401e9102c03001d11201d0035005413014600c240c80540e0f59901130b0902c1e4103496000c0d84003911030381582070346100040a0002480c11140790440e00c00c025111410302c4c9090a015805c425000b610105000c44104400101001e40c60040d003000c00385900c43c5c120405c20340e9400c3c051001d03e66589a80c10380e850418640c9050042c02560900e00101c1101d980d01500b640b20140c240e00040310311707a015000480c06c0c800d104c001d1085081003441e29001da50060490700000b0101162413914000040060201e40c1000074521015641195184d10489000d001008280161400b410a02034081060b08180c07182c503024203801490100b461088070324a0b001401a5498066645000801c24000490302e02810020714030903100c04005213001700801c41c460564107501c0341000142d103008000f190f4049009022200140c500740510144954241c1c088d00c0382e13600c40c9401d913182141007142050041103200503038020f030355035480c14141009c09120408085c0180e941d29001000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 152915197 1250 152913947 152913989
    0x61e020c010e0103060504141b03010810020313021207180b0604350303060f0108100608150901090b010807050c0c0d020d020904060e01050901020c0c09070513060315050a 75
    0x1e85a000c02d0780515001c55000d8903100820280d81a5000c5074055911502c103211050b041c642030002d50034031a2100608661500d003250b0f56400c081208500d00e030764000701043d180784041c6040e003001030300507000c4501c001c3c01e03580a580d030b00100d12600410641c02c03400344d0442507182c05031340300304c410081005080074102082109060114200c400555401200c1d0014611565078072090f40b0140c0c0025507247d00d402414440368840400c40c15042041ca0010403120400303051126094540c03a19012102e544d80190b520030a000701600c01e640300815800004006000d500725074500c0d4020f0f6140000c5490f4440c083d1110300913040e0b0b01c44580c1000c0c4915510b8144100f9140d101e60000700010910301264002c105c0d0080d099400791181c1c1d0f11164a00d110030303c240107003900190390100031458944010038090700c4100001c1e149120b4114500415001e9218409917461060445035100e6010381e102000f400801d40000740c144107400012001420b440c10141031030131600c01390030440c51208012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 152916447 1250 152915197 152915207
    0x621061a0607020907020f16051c080d0e2107050f0601030b010e1005120f010c090f03060902150318070501050307050d09030c050708010f0605120c2b080301061e020c01 74
    0x403c55411403085591f04c180b240750030004d1039015441203084204403402c0c20184940c0c41e403070710003880c1c0d5044c0700d4040d1307400608002e085961591030081c0009001c0d680007080d80c10102c9402c07400d107a0014200040b00030720f41102c0108810b620039000c071416079043e003180d56120082440086c0441c0c0b440c00040110350030082075a58042c01442c044c81603551180c0c005410504110300c400c0390355100c04050881207000341b08400c12842641045442180b406107583d140c1c14090200030b1425455018040454440e400b002c004565640811512845d080e00050980112404c907604a4441d02d080000c040d401101105e00502e101c0e5196803800352007006000c040c180d003503c11420400c0c2081e460005c00c2040c030074000a00640c1002040c80807490469005491082e00711512072000788003400e00281000403103030a1107505551810007041c0c002040802001002e05441e03040c3c0100c10305808100c14030000314141e84054075071026204210741020819803060350110090703031110902161540c003076 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 152917697 1250 152916447 152916451
    0x1e1302151605120a0206180309040f02040506071103070b0322150e01021306110c190b0304210201050403140306040906020409060303030c0212040b0304060621061a06070209 76
    0x100ca20014210059580d041c0f91503000822032000050109013210215818000d45da040445c040e1410307041d24507000c11036128400d9501042c4543d42d50302c40c00305013071955015580141ba00600e225100c0d1814140b01702410044540c95119004404001c0355403000300c0240c034003682e84c01c81c2c100c407800c00303903c0c49001d4104104820343e403411854a01c2c50810f60340b40a24200d50039014005a100c91441c5180901041103811400070722003c80c0810f11803460000e8200c0713075240125641a0340e149001144442d10100c0c2d002070501e60070020801040c0100c40b1400c0049052010400f92f6494642604178202d54041d070f0b00500295005602603501c03c5d01034083c50b003080303006200007484036895030b80a04a03171156006a40c165121101001403542621501c1e6000c80c203400a42880d411001030740c00c81e48110b020f5440b4003080400401d0a0004540c0104041d00b400440c060034056124048050124086412601c242c204071800440620f02418900541006001c8908000d500c0c0d080017196400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 152918947 1250 152917697 152917717
    0x50f090d020301021602100903020303180418030536130e0708060f06041b050f0d0e010f05090f1e0a0f030504060305070206010608010308130b031e130215 68
    0x103032504100903039020320050030140a0603a244c40c03280c9161060141000d20342d4100c0d001c0c448500300800150f107020040b40e039001c0c01d0071000c1c182101c410f00003a004240c0c103051945480c224121501c105a0000d0003807003900160b24032000d10288150051049000862310b0b00080400343c0e58036143c5040c1954a80070542c8a0032000c50702040c02c1021925041889d400000694405014840032041c0d5900d01504503406440c2440045413050405041000e40c3c9094000c20500103948022103002805441310741e00e01c0a401d00000010001c09800f03862030448801d125450940400c10130200000e8544e05021138001078003440c04850480c1001d07079448000300c0d2250140c200b2003000101c1c0c010061950602c245c4030b0300d8440741008001012a0002001c00007507600580c01484202c1d00000d405045960190419a551a0b0004207100c0c965440d1721280800c8800f0051100d0800720a10601140186801076882e65682c403500d000381400110300a900903410034980d0501502203030080070718800c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 152920197 1250 152918947 152918959
    0xc2c04110f0432241801030501090b091807030203030d021c15050616020307060309030206070e010917030d112d03011a0c06010303050901090e060108070305070908030408071505030403050f09 84
    0x221120074900e040c5d200b4044041c030390f04001c071400ba141d170300351150f00e014002c0054100407407007540780868074160f030103441d49400c000c0240020207001410002000515801740541f40c0b1410405443c2001c3c0d0071580e03290a94012a40d41e0f0050741e120f40c812034000d6048000c80000e0540717400c4c1806803580c081d114119014194000050250b02c0800c0360302c006004030396002404d020380d42802030800c40c0143ca50010005106412036a42e0707401881982515026602c0c1010028003115052951050201403101a410701c0f014580100701140580035800041c4030b10510038020310103010201100705140009a00284014484c5072860303102d030304889034540405843c0c03040d403209052070641d09030310440006100007480e00d41da591050482c4d00034420780009503220708003000068641880189614101030340d0300005901c55110b42c140d04005d00710a8140c0350390700c0d114404c00f0b841d660680500d00010007402d030f10800c168070400403a44110b80695800381080c00c040a1140968482851203074428 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 152921447 1250 152920197 152920249
    0xa231b030a0c0312030b060c070302090a02070f0308010e010906030c2d0305011e050103020f0f03030d2a0f09030f0204140703090203010c2c04110f0432 67
    0x24400b820028003a5001c0c1d245240300c941d42002c01010b540918550900400061000d884039070800103402c42030766411108a030131542c49501c00c030028064031740054162400c4250303d509142c0c00040700380c16144011005e4a80742c3e02e40c0b1140f402c4d2000c07440003c0440b031400101f080b1070f05d0200c5500c10079040e02c182160740014403400d1228200529001035541c1e9642d03900405e90340310400c071000b841c0100c0010501140d890343d00025030801e004000e06005840354014500c07140d9040c000c541d4000c04a480400180309104100040751811440701038842c0000d03200c04450a008140c00c854038592551480400d50550341e480c0f1809003030940403a002512624540710451012554912900090350001041c01941c0101820751f010781d0540814000140d00300e4240c00b183d00300301e10304410341c44414003080c10700130085001030441d030380b0359402614003081010740001210010000c80744902400d103420300041c1202d046c8040341c044031000721005407429440a0030320680c0013030240f40e04040d000400d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 152922697 1250 152921447 152921453
    0x91a090307080f0c030a02010f0e0a050307060e18010807030f060e010c0f1b0b070c051c05070213060b030f040303021902010b0112090807021c12020a231b030a 70
    0x1c0a407a0300440e01c2d80d008004800300180b810099010303002400c8000740706444442d00040e1103c500341450703804008000001c040345031a10208034004240c003408844c8000e0340c1303d60043c4041c900c0146548103030700002065143e240b807201e00906032a49100078250051031603880b000a00203083c41117070b065480c1c0302c80c0d40b940d00c028410700e12240300350780b500c500c01b80e408000203203001916011307488520090340310301011690101c40c90303a01c0041414039008803911402c10900d4481c5402ca044c200d01141d554140500c1c2e4040301801a1a02c2640e0460301b0b40c40102d001416500e55001d4841e11700700500004807484160181c240e0418003c0c103006250119014145640c400744034503050140c0e45504140d855564031480040b0103140c03c071020400780135160303a041618403441c1400b81c07207014220000d2040c5529100e060221a500035082c65407400c844101945402d41000d043d10b05843d2081000c1e03800c03070168011100415044003501c01d1028080c414a0602054072665130144900c892071800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 152923947 1250 152922697 152922703
    0x2100207020310021b03070507060e1e10020a05010203130c050a060c03030b06090909070509090c220e0316050606060306090601080a060510090f080316030f030f06031a0109020a091a0903 82
    0xc584c0c01640948421402d042c800741041001c004c1541c010991f448001c2c0ccc5240e400055140c0d801400c8621594902d0350402c06c074a03049686070058095440001403103101c032865100541340501c94444442900c0c0d480040000c455014425440403525101c14a000240301e544a010303070440080c8042e0401009001040c0c51440807140104107a009d900103008519202c0f00d003d40c0101254010901c42034540c000c200740034514a8102c5070f0018500400070801c9017500404126400350045070b44400120a81e94801481c40c0410b86040c0505804181103091031412244941c41c0070b0464069520b48000442c0c02aa004012012b00c60307035410045001c0d5540c04030100c6001a9076a1900d019080c00d11085101030746a200c8625603000b0014503d0f000f2649030701d0b059280c0c2504003802c074202220030540117008940c01181d80ca034503001001c02040b0108480311040c2c01e100d00f031206c407680c0700c42d0200100e10803804050042070b02000d040101c10810500342a48111030081e060805841e0000300c2c0c0703 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 152925197 1250 152923947 152923957
    0x23040f090905011118060c0111030f01031e03090b0903070e07020d08010503060601090b071502040f03200a050d0501090b092b08010b0a1803110102100207020310021b03 74
    0x4100c9484280d603009101c024007030000c0003069400c403145819815100f91154007804841580100342c00b08660040c4803003903004200b401201c09006540340b4110303002c440524000d01048138041741c120380c8115142242e401132450954961918188a410030741a4110764011070321980d4140f085000200d112071031946610700a8020742c0007807108241c2c4410140c44003405802050003a4803040800174036030b0348030a4141c11102000c14071aa00c00c2e1505004864039541081c5000f00c5000003800660401c00c2c42905080b2800fa4029242c0e90514080c01d541c0582c1c201c03081c56108001060a10103403a000050b158032078420000040c150b46290384600540d2030403100c0c1c042940003550f0804040e540c00a1410740d41c040c5542c4082c2c22003090002170101c481c18010b41d08488408510901c00500030718202030580928070022000750307a2850325000310400e00418500500881c0081218a9960700a855107582d004028000c1050707038101c03410081d00304031800c0d041c0704403001d03000f00e080c541400101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 152926447 1250 152925197 152925209
    0x406080a09141b030f3a021006080d0206010312030207060f02070b0108030a02100906180b0106020d0e0d020d030509131514010507060903050d060b0309010507020d23040f 75
    0x300c05104000764a10f1401480414081d03006294494141c2c8008511445052044900c10f80100e481c2c007140b0a0203070483d5a014001c15a441030f82d1015600003d441003a5060180c05201e240c0c0c0310715599480f0551000a480541d01072001440000d10811001041e000c8a1400504000b51030321100300f030302c4016120340c02503580024030106000001d00858054022400190720b00048000001d44e04c1600f100a1541644c0c0c501c4428104000b5400c030f14008608207002d148060300d58244030300b20110138481d800c054400c000d8500070881c0140710548032414000c01028400000740c081c00024500300700d00300e082000401000700780d90388802000302c661402000c0000c03800ba0f4800103200c5498183c11200e071241c0500e0b0300a9243c1c4e8000100d54007643d003c035000c150403503c0d260944441c051300300740b05486800d010f4042060f031420000766105007003010080c4070310b071101d400076a281e41201c207220000441d00e8110150201001640301c00f00e5100d040d815143caa03541043c035a444040390061 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 152927697 1250 152926447 152926453
    0xa060503060f280e1603020604120213050703020a02010605040e030d02070c08030304080409060506120c09040b040e10051806011a070213020d0b0f061602010309121e02010603080406080a0914 84
    0x100c1c1c0344e0003c1150400b00380c2c01d12822084c40d805c540024107207004038400c3c00001212000c000045443e1500481c412055402e000c0c851820f0035000980a908070301c610400562911600080514240c0901002550891f014614000203400301c01d019601038407059a0849100e0000a041171080000b188210b016000c0c817900c5a08000c9007009488080d8811441514144082044000000c17040b030f8100d050690007903a80d02074080490068080411400d62082ca050710007820900003050310440c2c6100810700700416a10501d0300d40c074000b0341035400d0700c0c280e001ca8014400f404075581205410059800e00030700f04800c9500143c45506042e203150b2165802250300d801001003401280320b140000c6941c003a0458901d800300c0e4550203070703001d10098800b94080120541e4000c0c4e100d41811034020500c0c650303802d0070102c0580106424904445c00c030700c442425101042c41072140360146c990001132075180c0740c6400000c0ba6101c80c003130715020f500f40c0e0324000040018a4101d11458078401c1e0009 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 152928947 1250 152927697 152927711
    0xf0e04030f08091c11070f1703120a05041e080d0605030c0f0402091c0507151b12170403020c130c020c041119020f060a060503060f28 59
    0x1c000707407407481d0394a081c4110341c800d01507160404169000b44070324800d455026103c0700303542203900d00d8032071446031090301880b440841d0041c0002c0500d410350303034504600704075512841021540da10030354011000031010350020609002031604429045402400c8244031080500c14020701a42001000c40f1b0390000022800d1a41401d4011000100000c401901e80c401140c40032884540360f03031402e40e200721390016007045942c1d10f940143c00c0040000180f409407040d207140141e034038100c81c0503008a501903528001204d45c42507100c8100c03289059420840440d080c3d90301701051581405032021300c4003d1010074510101c550301c06104e54002d030300800c10110b26109004400790100c01c003904943c2000c0710840701039000030780f036840320740305580015100c0080020344000303000d80041485880466184003c5444d07000810f8402072080c0c3e41030354501c1e125214440200d4880d485501d4160b0010400030b03015064406604c0c1d44850300302400c2ca000101d180d6402246000030071148009651450 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 152930197 1250 152928947 152928953
    0xf09030c0d020f01080a0e1b0906040203071b051504050d0e010e031e030c12071b0312031e0c0201140f040b16030915050f06031c12060f0e04 62
    0x1152840860584084281c1c01041d00400d19402c01d9016250500c60f890010804006059000c2c0b000340440e44180c48000d8444911b0402581d4420600761048007540c010407814a414400c980c09401c8039108c54a0740c00702c1c29541030490030180801d640714050028800c2244409c1007000344038a10a00c00b624085908900141000d811150814104158038541c00381c2030b00d00141e25803403482c00b41200380010000094480c958801e51203c0392242c015a00420003424519002d024550320900f51586103850300700d04013140d44194800504850f030001030a680c0f1174003e0344521944480345040307294010001071401c0c26100038545040040c2e54074030001080c602c80c4440c0e01e4014207048815000d50801d51581e104406014101d0b200040d012104c049240e406903100c01802d0ba81b21040408515059440c3c0c401007400311a0007000d58042d0000803010b14002c115104205400b01951084c4403041d50100d0701e412500b80c412141c80c0d681c01c070120300300349141c0c514401884d01d00103404540c0780601d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 152931447 1250 152930197 152930203
    0x14060109230708060111071203020d020d0804020604030204020313020d11030d020c0306010905180a080d06080d080a110d050a0b1203180d170a09030507050d030206060409020d02060f0903 82
    0x89000007040c0d8004081c80450341d403200205402240c00d203400c003000c592a00710241091100e0b403000220300c441807640300c01c142e0045821104c49032079400791601c1458265050b83e00c0042210029070013041008107100516041e4081c541100f1901d09484e4210103e50100300c10010499040e101070381c801030b102071585420090f00d080080700c0d101810a00c100440030075900e600600403000c101c0e40f200d00140500680001d600501e2011608413282603809062210f82d561007503698002d410b0410710085480100090701880e900c1566441c01c46c00e5903009115030003441c00307903441e24910204100240150107079014250051001580008402c0c500030700f08080c0c1c141344040540c8940052100c04090b12000c002078032844000d41e6605c050350b030701d403410510440e5485518065110003242c0c682150b6031200200741682e00c0750003180d80d480c0c0c90701c003004081e01320200c000b40180c1c0107100040641c2000c0c4c010701511440500f0058001170103600013072441d040503521a034001d0000c2000c502500e010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 152932697 1250 152931447 152931491
    0x10501050a05010519050f0d0207050705090906071d040905030301050405070318030c0609081602240d111303030513051c060515040c09030b0a062114060109 69
    0x100d411449103890b00c030020340035000d146866200001e07940d000b5020706010354221005407034140c800b540d50390500c1c8103640082d002801c080d6800e100d250804151820805115030044000c1002008580c0e030b1500222a4508689400401d050008200c46010389a034004c601416120b0300c003644e00c82d0b04100921044810051861081508102647c0d02d0b41c06a040c894030842d4061a00104407821800c1010103460703500c3c001850218009101c0b40700d9482c0a803014000c5108403120f00c01d15500001107204115012010307c8189070422000a0850f1143e005040034117201c90010700300f444c038a81841c100c0b0800d500071380105500080c84401c0341c3c0e2815800e8060a003c40d0520400d001e14080004100c0b01803500401c6a40d899001ca807151201c81d444070f8001c10b0043c000d1003840004d030310080414040307110072140e140c2030740e01117003102016008503019101314a0a80310b4030140c048200032000c019a000755028100d001c8005601e603401d005141c044d111701400030441c400c800c2e1080c2d10203e00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 152933947 1250 152932697 152932699
    0x2030d05090604080405270a2c03040603090218090106080607020d05271002010b0301183201050a150905070c02061804020304060b030d081005100e040905010e01050105 74
    0x41c2c0401c00042e08903400d40d000e585040c0d4540340051307082c1c0640305500c0660124191030030000020032190072000e8001081503406840f100b44203040e6100d401e4019000c180e00362200d0780091000307020703991003948081c45090005203c2c10030409150802003900c1d0041d41c2c2d000360360351540820300540008000c1242c201c0304074401070224110070580103200e4020140d040400c1010391031700714058a442c10750b029205000801103501031006c048081d00a202c003d00d428060750801c084410031500c0104035000a641007040b00102690209098009c03217005203442ca4404103a84e401e12f440b10092041501c22030440310f0000381c000800d008149203480a41c819040e0030704040810054a50001c2140340c3e00f981a15816150301c140c02682030348202144065030098400310402c41480003980044600b504182d09403001e81c11650800c1341d000b4030440e1544401c42945a04002900303020f1070350240004645031186489422400080544445060a580f20382d102c00c9040070384031007845042e004042c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 152935197 1250 152933947 152933953
    0x1030218070507061802060c010609150503071517090a0201020712150c050405040c05030402180c030f090106150206090f0303060d0609060f05041b06090e220503040602030d0509 78
    0x14000e0801005403160f090002c01564846140036121341d03504414500440d0b0082c51152600c9130494414000c2c5194030601a4860521085408030076030761487d00c0030b860014001e05213203070401882010601c0040c038035000308244080c0c12242c4c24050707002c039806101c1705006030100c041f190000a14140e031a07046120904420507000c0009114003d40158043e4150004104912940815a41c40c003c0fa40a5030300700d414501d8810815a000004501c200d108841d00c4454200400c050040e81e90102d40c1ca4132018001c0001c02c00c4070686001d13495101d15100c00104106458000c0c0d01d010260a00903070307015a011308288456018240b180f80c180701c40038401036080d40351a800003042e40284e240090309a5039201110400d00045820042206103600d00070b02440c00c1c507260003081c10000303000c0040703002c0128202080b110301c1201c400c01114a00540d9141540341c0b0a892102d2040c1c060748203620001030b00030300b40010001e10240004140c0c5402660302c401a206134501600e50040000c5140c3d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 152936447 1250 152935197 152935201
    0x703060602030316210c0906020124030213090602130323060c09030f01111b1605090603010f0f050a0c170727080c0a0e060904060e010b06030406020301030218 70
    0x4241032a0b140701101180b40903a405c03445010355000004070307100b0360012141006005e8070020303001100c3d0300440351568000c20000800182900f285070601d0480c503c12800c2e400c0800245c80c092064502c48454140f00103000c59095607100d080341d2158058881c583c240c440100b0511a421300d200c10740c43c400b40e454a130851241d49038540c403918000c04480b0501c40c00701d4040a961005c01550002d03101d800d0080007518400003170b408807a006240c01c0848060442104030a0900104101c0d10070541d141c44007201c0d038206402c1211180e402031500f50103640c2c800780010044414042c86a2141484d0b80024240c00c08503544c1068030300440b8076205120300c00c0d40c020500c0344404802035006503039150460b05900704091810309452510744241c0d052030310b0030010500e40130100d210100c3c0c101c02c40d1103520b01d0b036079403200c0c00d07500078100ea11690114401c0009000b184071381c0c0144807110142800003031503401080004459410030340d001e0b00c1c03a680c0480103008600341801e00d03030313003800c41c161030030100d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 152937697 1250 152936447 152936461
    0x40e070f170610140408012a05090f01141218030403110603040c05030a240605060d110c100504061103090a031101140103060207060b01090501090b0906040905010b0307030606020303 80
    0x10a0058001ca00401c1040e80040320b0301c1c420828422a030342903c025517699036440d50068080c3c07010441d140d64084c0c5c0c2e408000c06480c16500c49180f101c070705e501d589040c40303030200400a041004040550610260246000c503c0c81c0000041c035503c200e06944a440e810301c41c0c40960007016100c1503c12a40c0200020f10100350b070305070f0a0506050450368503a07a0380d0303280b40030116446103501180c1c0611664003050200586c9003208005060480c0740d00041040440101d8150b81a6101d420f0300184208120401440745400c80c1880810b45010540b07002c40c0c0254651500c0e00700902c18031201c1d030320030a0008002c100c2c06880d450003440451207066040c501041034480d1a5090000c05010040c1c11003521803c080d00301c100c2060222f030f10101c4540e96420603802952007040b00f00e030458505000d0100030360207058910140e0b201030b51024000d0303060080c4000c580e8403000344290701c050705010024200013203009070f07400703403850344046074490401340e4000d8141d0700150488000c0d50028020031200e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 152938947 1250 152937697 152937737
    0x31b0d0e0603060f0307080f011107020a0e04020301091403090a09060308090d06090203010216030e04110d150b0c1c03020a05030a050a0b04050403020303060109120b0a0c090b040e070f 81
    0x2800c0000c50304580e9940710301000036415000301c001182c05002d1100c00207170310300000c2414400d20183c0340090141c2c02442d03002c218070340301d100002940720106500c02d000e100d040b0548640c0c820300c003400024080c691a11045c401c028040050001385c1d02c0050700a1085c109042840000c100d0b0902c10b000741e5084d81d8400f80103010300d508043c01824400c2d001824003001e80c0210040702d40150086559451140800755100054242034000c61001a0546252f0401c1d110f40300704220b00c521407504211100c4000e001400d035444031400e01000700340700810280b04050060640096101c02031400c21225400a1081204004554149403060200e440c1042d00001140e6201840d01000141d075903640000c4c1000303007603000392143c00c54606000c00c020150008000c5024850913201d0241c0f840d590801030784680803520300201086075603404580c000d0100d030001c10684000d4280100c001d619014230309050b42056000701da50078a18401d1010362900000c0d442154002403030000c601a004404141c030f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 152940197 1250 152938947 152938967
    0x60a05011103160305041d040c050306070206060f0325050406150e061b150a05011502030706022104051b060304080a230c03030108070b1306030507170405031b0d 71
    0x19211640c4410f5004041c400e00407600500920310503021803107103000c1800d1100c5800c44003140d04031103080011a01d4640000c41c14030500c0d056006008076a10301080c842c182424015076038061040a940025803120800110760403841c0084202d4518581005c00050355108c0d4031102c175540340c9000c0c02400c07607404140c0540c4c80d03100380d41c181d40c0d460030740100c641001212462030346c1d180100c09100240121520030180a110154002d00c426601d032011601c007036240080c04030140e80101300e074600092150700a0003841045440f190f00b00f9080d040c291801010464085030b03580c104112440b25003505080540e045001500e5040c11413520b83e6810340c01c1c0c8150046103040c0901c0e0040a00e0307801e02c49003200a0364221101081c7c9070341e0315103402075507038000303015000e01402807a101040d82070400e03041da0300e4018006500803003240351200a07001480701504000400014041c900c502021035085035004034441c100a41d40c801c0110181003881c0d40000030303041c45812000c003103015580c0c007843d415 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 152941447 1250 152940197 152940217
    0xc1a040201020a0b0907230f0102030f071502090402120907061b0b090705041803030e06060a051203041212021501050901090c110d030c09140904060c0309020d0605060a05011103 78
    0x505500e450084900d00320b80c51f4001c4014002d1300760643d450711101c2c1d00300308405406941c1180030409600069849009000c0500316983c0c0510010780440c4464607201403140d1444801840d145418000c2800e0341d2041d01c0701c11440c99040c080c0243d11400300101c00003040355142800301454800340182020300400c43c05041c1ca495000850040c0d4010b014400081400030402c019884041d003505414001044094020910307044040c4007014022401c80d10420009024203000c0d400c000400c100c6030382c5106030782c405210610011590007025051a903585001c0c3e04071305005040000d00a103031500070131507280b181c422803004000d5038507240b141a064850303031440480c94010111044461102d0b40004800501c1540103500009405a003c030448407400d45d62159900c0d2030303c0c0c6401e000040701420a4100d040383c00000c0100d191544010380300307030072460301040e005030340d4000440190711020240c52007a681e000303220003458154000d1004090038217024071081030312190f0680381d0007501061 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 152942697 1250 152941447 152941463
    0xe040314040315020d0f09030806010906080f0601030c05070b010b03042f01030f0b03060408130b190c0201140c0607081605030103060c09080a08040801180209072d0c1a040201020a 79
    0x9a05c1e10b02840d0801c3c204041c03800c4c410041d146690070020000102038030202d01003080e010011416500c5154100e2143e1114081c0c150b0a40720b56004600500c1c070035626504000303080c8041c1c400644019aa14001c05040080d02c5d100e0070203084c0203518540301080040044140c41081d5082070100d03242074522003003428001101c0c00388401c8100a000e020b039816a00d030007404200410003d07501c0240001c51945181040e4207074840c100035040d0700c25180c41d2b1f240101800b2030038400030321484003075001910601d8025800d20092a0460142d000050a81c0558001908010495a0140301030b540100f010761802b40118818001074a03501c0180006131a441d2640d6035110803e0150324807500411529048882d9054503040440098026002d4034026500340ba011286100480d4412000d02f500100100440d440d2101c0544001c0880c2c500c07841b5001d200a081a088221803846d500924400d07103c2d20b83c002542e24060085402c00310a4a000c042500c0070b06c800360341d0010f40014040e90105c20 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 152943947 1250 152942697 152942707
    0xc061506031915080102070318090917030703060b030c0c010b0108060a090b120303040302060f0c070c06111c0504030309120807030c14060411120111090d0c0504060e04031404031502 80
    0x4507080c42001c2c0c110006030346c000500441016071213190801103004681e0030902d0561600f203100d041d98154440035086600500358145d14580d00c10085422200e18100003c07502c0e524500d84c030711600100c51500c5010404901320001240a000d200c01102091902c2843c515005000a180d40074a0040c95070325551000200c2c00d946a030039010060cd540402141d44918252078000d54805080340c000b40124110070100e0614014a400c0e942c1542d070000114000c103080031000c03602e600014600d142035200d0001c000f40640d282403c51080c2c08115514940d03039034218203000e02104c07000d5205820710000c100903c00440c0c00002507450309985450242c1c4146998201005040700720702d203200f802e014400c20f100130011010312140c1091010740d184e48418803079440d03650890b0408502d08003214000c001410130381c54450761810340f6602c14418011440d0721500894100c5030a908400f80300d0070042c090000303054100050010f024600f050040c50a419641c9045040e523200780030801d41900852 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 152945197 1250 152943947 152943971
    0xa0c060204080307081309020c0a060203060301140f0106030c050301050d03050a020307081c0c0806090a0c020708030d0605210a02010507060b030d030b01080a0e150604020705030c0615060319 84
    0x445008028007800c503070310340d0151700b041041644000c03030b0580011404c840001d10b070703106402510401c841c0302002d46070211040c0c44401c060350004140f190b02d5540c84801270030f07039200064000d000d1004101203440700d60514101070200c8218600400c14854188010069544c4a1255285d0642c1c1341c43e2094681c1ea0580e4140d00d0741c01410700052414402041c40081d0a00700c8140d0b15103000f0440092254492030002a240d658003a950aa00100c0003030002d00042d80580141c444200184100c610b038130390b1a004a421074021010240816031074a60400162401615482c1303c1110862840700a046400402e0b0743d0301c2e40240e00134103000703011480e4800e11145901046400402500fa181c3c04514004014020309404182501041c26040030411607680351091820614040d030090200d0b1200e40c0c82c65000b204020400b50780300760200700c40000240e00344082e181c40c88042c00244964141036402d02000700c03004d0703111409440207100f0803e20003060704815445200780785d070000f80288014 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 152946447 1250 152945197 152945201
    0xc090905030f0d09210e0f03030c01020d0207110a06080103030f02011107050a06050109020c0304050418050a030206070207060221070f06020433050f0a0504090c11100c02030a0c06 79
    0x410b0040ba9290040380d094160040d641080103068401c0c0310800c0c013844501da620070380c0c180c040180d40c00103000780f032459154207055400030b41c0c064005040b28140110003400a007aa484040a00d054030340100d011810491188540c8100d0741c401c80d98000c495081c004000c0c0b0612051001504000ca540700054983c0d000390301c40724000e0200d0041694030b1403117040c02580c8101f110b6013141c03000d241c8000000c00c40e96500c02c2e41c1e80c0b0088900594901441c1c0300401c000350640340c1008c0c0e00000740d200d10340e0000e2030801413280c0c400d21036009018907203400390000e41800001d5100406541011400f40d80907001e00c03c50000941500140d55180c040c03d0400e44020b00740054000d103920310000300420004803c2e40c90005101c1c0c0444010721001408003588003d0682034104808a581440b82107100e0b401d11015119080d154a450760426655901c04010303030300c480c040500440d54401100201c204188180c0402490b005024840c440e03985800940d82d20034043d0103030410404000b160f08000c203039 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 152947697 1250 152946447 152946457
    0x903120307111005011d0601020d0e18040b0712090305040512030904090803060a0b1204032007030308010501110105040b0105010509010302040b12060102160608010b07020a2616030c09090503 84
    0x1010490300c0382d0104041c01d00c0140020b003d0740d4886e00400803814041040307045030314070070101a4090024440d4405041c0c605004030303003001750f000d80300c111507071132501c100c170340c03092282d40100d121030145c0c2411000030b03049070a421540c10015007081111804607402c43d080b030b02200c000390b0345003584600f0300e9086400c0d80504092a03622170b060806503800d0100030000755000700350441e055060150786601804d1944120709850100c00240c500040c042405008800450942e11000c80c5081c92000c88903400e001307107504102c000c80c551138018009035030f0200c4150007100e00c2d20001c10041c18140c85030a1400c1c0c05200312070401000064240300d5900c40d406981c02048400402516040700000c00c1429420444202d4018468041240c2d010807000da0203000319521500c40000d143d00700803c001c000c0c1d000710016600502045000140441c60014420b121503c0e02d003800408525401110b00302104c096591382540340706001800443d0300380d40c0301c8048480e5500300142010b62403800c507045d4010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 152948947 1250 152947697 152947727
    0x40e100e07080a0b0a060822020a15020c060306030604020f0102010f0213030212031213290403090b03060a0501030e0a05010504210201060f090b01121a03010608030903120307 77
    0x300c0050040440c0c0108025002e00080d48091090207000014082800317003d100d00c400040d00100810241c44100303a402141d8000c0c2031442000d240c064010404098440e400010b01c80d105000540c03c1d6941400081285801102c400c4c0ca9410100c0000f0f0341c403140944064450080400508442c0c0e000b50f03c241d485040824056448117818004101c1c500d845110680c01502c003410150600308010044503150100c00e00e90070039984a0302d600c03248444000404a03401080d520400308081c0307505021010300c04c18440d0020701d0345070500e40100300303032440d1303200d8101c00300240705126007982d030503160100b40c4400380b86c0004e0405005008074a003041c4544050071552811090100780a0452280c0b40c0e1b071001000b41034a004214101242200c526200b0400f076484440800d120315002ca81012014450500d010010b99440c0500001280d1001c031000780c03d46c01d50b1b40d2050f203030b00703086c0921001003c605001e9810126580b01080e1200110440f64100910000004240c1d0303002e18180c80701003071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 152950197 1250 152948947 152948969
    0x513020406092903030304030c050a020a0f06030c020f070b0f130801020306030d091a0a02150c040801200f070f0804030602120a0504050717010605130f0e070308040e10 74
    0x3580e10324850040c0000404640d00b12480107100300c1516200903c24145000078000f0b51a559583d02e084501100c066412a0319004552100700036a5451207030002801c0402c0c000b503262458200050b086400c5240c001065402c00340115808010100b05841101c1304200b03c20394441100300220840d00c40c0364041442883c421350b02081c107190541c05144581e900b038045808119480138150f40c0120fa5200703c01c554500ea14401400e000341a01420b00305803d40111101034110100c00d21492130704807034405003140c0104003003100090074011200700c20020070090200e001425000c02d601c2c03040601004404c080001c12404219a0340440f500e01a04150f2098485880f460510065070008115034041c980c080c0c0440c0c43c24500d071140c14081c99002c0010424036180c1411034803000c6900e207503c181b555903094000384946800300031007401491801c0021781c1062800d603d008484e80a400d21940d580a540d042c40040c03582800c071003c6d941645526101603407621051031643c0d11070b0300700c024000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 152951447 1250 152950197 152950199
    0x91005090a0807080a020106050901080d0f17090105061302070302030306100522180b0f0f010e1c0b071e051c140615030c07030503090f0d0203030711010615030513020406 75
    0x740304c2d0040c04400c030381a07009100041d030314410840f0ba0f080c02e0095030125000490f003006c4040c002c40741086084030311b090645164107449000d026014080360090910b944490801a0030319000341c500c4a144d82c010801c41c00c8c00601c1d14000c0d924040200041e006003650784402803024040d1301034402005840f101c140e04604558900710a5070340c684600428a011001a03269003901400784018207440170308204d03005c0b813030041044032a0140b0042141482031400900034162142990904c907442482404100301400c6d241180d00320078010240d01c01c20628421003850032500102490041c041d40c580740e030722000c0c0d07586e0910302c0e2081c800401c98228030306020705c42c104030301c0400c161103010201c6220081c0200000c40d00e0700c9100464030280e94150801810000034015800f5641100743d10085805c5c039803500b0042450003e0300c000c6540546d07c04010010100e40c400c2036505402d0101009101d40d600d00180080390491200b40242410384450009801c1c5488608040c0d44540040041c0002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 152952697 1250 152951447 152951453
    0x140106030317010b1206090403030603020907020a1110170702010e0d0809100903050f1e03040813120b0c071b23030601050a051504080105070302040f0e091005090a0807 74
    0x180b600c03148418031214440c400090344840f070b201501c00180d820004020660340d5003003001546500200201d0606548000100c05625592082c0c1d02c14001e076001800f00e070006040c450841c815401c102c501c00c0344c8001c5003a100f2540311078031904d00141c00c02c104d44582c82d00c0300240c5c090100013005203810b100341d01022494079400100e443c0107100c81000d03958580225040201540c1c2042000390114208112009070181050002c00c08029003541c4015540c00501050034144d1060750242d41680c0081540b002c003480e0200c60b040200001d002c0e0300d00c404115a25002c003002d00078001090300002244c40c10a001c080b1203034801c1c02030007080703016140e5111503074200781c1580154030058175405a8054806428001410b40c107855005180e568814a46001c21040307010a01d4400c0b2840010701002407055802d02880340914a280c401680319400c3c844080c41c1c000141c3d214142341450141031000103840420028002d14580b007001c50380c3d0307441c500090b140448804d03000300007600025441082c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 152953947 1250 152952697 152952707
    0x703141b010b01170702060c13170105041b030c03060b0f040e07060809010c050304060f060b03151003050f040201080718030302030705100606020706120906060e0601080a0510050108041401060303 86
    0x1851001d8880b04c2c5803220307160304040c00250480740800940c0c13000d004180742c4200000504001c2024910103a129602c5120045005030502d005002c00d83d100c3c018001004070403000440700078a1103400e1000340f0f00e10b44a400480e030040c807010744801c0d6180e4113040a034540541c0ca072140e40000e8410301c0001071a0782042d980e24440c1c41a400003820340008078220180600039100100919034905040d83c8541c0c945000030110440d120000c10b9460f640052940c1800002e94070401c141c0c90080c40246411041c0054071403031400100030980f0b080108120580141e800540098080ca4400c01b240c1e40e20b00c065604030050a00440005e0740a4400401c060b8004028a0b07460f108000341d4011106803840f44044e030303001d80124005600400001c1c0651b0b8890040c40c45410307001c41c0c01203400309990301c403c4201c6140d80c105200f80e459020400c289960000e40c89a000440709070b04006500d007060f40602c0034040c0d4000e20781000000310200e81804a1400400407481d9454000c0200c5542d074500501 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 152955197 1250 152953947 152953961
    0x4030203031816031104020c010c050a020f010510090f09150f0e0d090b0a09090504081908040c0504090302030c060f010f060c050a0605060d0f03031a150703141b01 72
    0x34071500c40c6403a50348070441c00304078030076882d81c3c1001118500f81942d40d41c01c1c90720000070040703402036402d204050001c4000d02820f404032070380d07854103651048100002401d140b0400d522641680c1000e0500c0459240c91881c001100e070500381c002210900c09491030040c1080c02c40143c840030000040c0c012080c03569000c40400c08a0301d904102900d06410401d0301d820b00031040001203030070b9238020000000d140006081102c5140703030807158241c071100c4080448005680942c0d0300c920216901e43c01240e50a5500d4005141e07092410b00d40c81c0035941c6180d920ba203405010701840c1c0b00c0011404043c020802d6a015042040c1a03d480386030003411103107500801d1180205a481e11840002e1060003101071081081c0c01401034203003000140ca465000d0300000d00100d4012859070b8440010a860100140c02d640c82540c0125160069413541d0703203130341060300c001c602c60018207018182001074030782220960380d13060410500140310305d48502c81c1c0e80210090a118032200703506a28020606612041c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 152956447 1250 152955197 152955211
    0x90a0f0609141815090309090c0c0604020f011206031b06050c0c09070c05160807080309211f0504120c0f03111e03030a06150516060605090403020303 66
    0x10025079034410100940d00303050a1424540304500104824800550088452032404400c0720600222540c03101d42c501c40c00c0307690440c55080840d9001e014134101031500e4202c96116a11401e104224000949854010f403000f4030800c448170300800c069005180c907240106001004100d09a03407802d164030031080000030b240d5204002c140c007082c114064400e07030714000415030003003010492901c20300c0340003403010300a6014840043c22280009104100c0f08a80400400e1001f0815240045551410006800c440c4480e00305002c8091942c4802e2585658255088845201080410a49810f06052440d422600410a000d80395032442c582c01080c000c1d0700c90f15000c4603110034004201c2c1c811482d014001c00809101c075551004c240718000c986400f81c40d543c241da407050082e036501140050350303005240e025000481009445105407196100034564840c0000c00007510040050940c800c500c428445c1d1400141d40c0c0c42848034030f50194015080c045c011f1400760901e0f0030007a50f0307a0030854147e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 152957697 1250 152956447 152956451
    0x1c03150605070213050408030f0c1905120601020712020d081204140d17010b09210f06160c0308070201060906091406150f07080906031008060c040305060a020f09090a0f 74
    0x112090600e184285d601c9950040045030440d203401500904801c2c4c040c00c400000082480340d080b0303400305403505182403819925580d82d80c4880c03801245441d14024070003815500041c40410031483e00030442c55050341d045030b109007411640e06d002c031113074042ca4000b402111402d0013000200540c109842c020f8004020440e002d500800d41c0c101d441d4a040c0405d044500007200040121400c0d0720050070070070400034003400744418a10606414220004504004c07540081940030504c1024030800360459801c0704174801800f240100940b4170402031000800300b20b88a800118568800e61040300507000002061284c2680ca818800c0074102c0c0c0d16100b641040d22070003041c00c03031506030180b802c5502c400d598117081900c0100200d406400520090382c1841e03007000040c4043d038a80b401144940c0c0403034480f49205040442d1686050801040c41000b444200310a20100b0300c0021141d6005200e111702603910720520110480d1401081001a00011184c0a02c143c0340c1c880d41011401682207802 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 152958947 1250 152957697 152957719
    0x914030c0f010c02070303030902030a1719020a021e1c03120b10120f0b06120108070b0f030a18020409060f0c03091509020f12010504020f0a03051c031506050702 71
    0x4010b0885581c9220f120150b44495020000a80244c1141216600090036a104048580c44415248800030b1200c044480f00090740818018101c10b0107044280503c0100309500090b4080345050001d80c2c6100c401c0b104a90b41c0ea15259a500714044105d4a002c0d4251140c00302840d020b0841c40146035000f000700c0c2000980d241c5800c2001d035915070003503da0742e41d00108506600303050081c4200d54040040649a07640d00701162680c400600c105408400d0b02501ca6151428282c03c06080343c0158441c0142002158400d000f0801600d803c10540040000d106c0a00e403a8044802c0407014020b40240c01c00c0108414006254003012801c038441c00107200620076901c044044481c49640244070601454a180000707100e54010b050350b40c030241034000e000e2514400190400300c80521048260744070020002142030007141c0080e051425900341038040d0030b41e179410342c49482c4110f81c141d40c42d2002200c0f0201501c250400350809040b59425480151030700c10007000e9611110040e4000c100c0860 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 152960197 1250 152958947 152958973
    0x3151f080f01050f0f041d011e060602010506090c0c0a1205090406050a1d060a050a0b070c0519090504150e150c0307020607050a020c03010203010b040302010e030c06030703020a030914030c 83
    0x2200309100d8034005e0664401c00203035820000141042d2031006401030020044a402e460b00744503030030024600e010305402005603150070300c1c103440d9140c02c9107046904040a100603038441e050010340010aa05220f034a038501030310314130f190030810302000d00204880c5c1703d40540550070000800350070f84107070340611030b40b5250340512074405101d121301c8420888202c2c40405000034039003210b400081c0185001410307607841000444103405a0044401c03050b00050745000c02c00003140940007410142c1d403031400341619100007002c6111a05c00c00521540b0740b000507041090074558107000c0b035a0042c0411170040c0300c0b030310b0581d01c2100700d00304007074180b066000c9140c185543d0b05403031050358250700500040da00d1180498664004449400540c030400348849110b660a0015601810019110347e89039032441c00018203600204410901035000031800d134449464140850368040d5190134050395a84070400704030000c1811030005011200104000012044040004c100c4000381c41c2c2218280381d280030b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 152961447 1250 152960197 152960209
    0xb0a0e04050114240415030302011508010c0c030e0f04090804182a02031603021c030c021b0a09020403080307020606370902180307091103151f080f0105 67
    0x240302443c0c0a0218076005a00e1030240318290300744c0c0f1002d080424a004100c3c1c480300c090440790011000342c0d4540b000400070000300701c174860041c502341d0028003503032030791410160406584000140070008c054980c6c60f11900d4802644a0760700b07000c2c00c108564003407810082402e030454003552600380704c981c4410600d80d0580c010008842c2144540006003900c41880c4084004415032120a42c0018400d102003213039050343d041c0340720303020b41c0140c600100b10402c1d540d516803100070309030705041ca018241ca41940d40041e62042d240800051081810b02c1c0100046480c10b09502101590b800010040708014003071014501914860b003c80d1400e4030384c00100044d9006800201c91071b49000d1000b0f120104041040d02c11004480c209000e80903144d00c140402c0c1c1c0c1c02192181ca440488602e004081c3c1820015000201200e40080200b103640a511403c203100180903240c4075a00c8480190107551a035100c0d641c4020f0343d01c0c090889803c1194050040c00c42202d00140d014820070002469003485 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 152962697 1250 152961447 152961451
    0x90d060903080703060605030109022a061b042706090c021f0615030216210905010f1d030102120f0a0b03010209060a0302220b0c0111090616060b0a0e04050114 70
    0x1030f40b1442e0231682403542180080d0460041031043c500354940c8841050480705183c00c10450513006841301d0314005148803a0000542500c050701041080100700541404510001d075506100504580c18100c100800c00381540ea044a03004a141942c0303051015000201c500390040b4460404959004400b1450700b25074041c8038000144c469040080d07009880b03a03004101c00d130044c060401d22554a81c50f0842c60b1801e0209031680031444d001381404154020701020300401092070b12944100110324020809141c0944460a5401d80b09280b4800d60302901034804507001440c0104003271810307092504820030103454102c05a0300d00215a401d900341030080303d40030f0740090030052400400c20011002948858002c03e0400041c0d0318200c0c540c4440e004c64401010724518680e210303c3c04000150031501c000e413103400e42910802c028070300e0380c83e20801da80c0c956120591040c034000e40d0341030000182c0001441c07a640526030b100007250001811400a00443c0908003c00c20800203078400b415000c41 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 152963947 1250 152962697 152962709
    0x80a0311070f030206070c0f0e01140916030e0f120301060f02010c02070608150301050c0a0212040e0402100908010203010801050103030f08040309051507020603010305280f03050708090d06090308070306 89
    0xb84841480903051401c01813841500c502c4101d20740a54484003034000f1a61600541000740d10003004208114841001c040540300488034000d207410903005074401714010407501c206064803500f842010200510128008407100c04c1039805158086042c16882e0f4000d01580000c42c104007442d2001a01c140b291030316050064005104070ba080813010340711901f000300002e0107800701d11801d81460f10203000f094092840d01004548072011241c010303090045159001c1c80d440b074244420068080717848401030300940c040c0c81030140881a080110307a800c1aa03000032000e9800000001400c0c881540a6030499000f60349403100c240c15a1400c41d810581920f000d800100403c1e0240981d02d00141c60b41419401c640f080341c0b5040d41a03000c0f4103150000d90098445420a0380c0349500185007401c10b40302482d210704011003c10080c0e4440c140d51100c2c420180c100729000c80c0d00000c04c0b40340011240c2c070000080c46400d03c00824905140505035000c8103e000603456004202e516000f03002c1d400980314 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 152965197 1250 152963947 152963969
    0x3070f031206150806030d0c020a0302040b01031107050c03060c0a080a05070e0409030225061407021306080d020d08060f01050915070f05120f070210030e0601080a031107 75
    0x225101101d00d10418111214400d0b500c040025200c01880180a503000c00754461304400d107000070030141000e40e1001d01d50140300150900070010303500d21044400741c95044030700190b6425201d00407401880c812000d0120074600003000340600c0170000741c3ca1443c03581103080340c85680c1c0f00340c031600300380c002c8505220103d20240f01040c489246500507560000c403038a0155042954800010107451034210b080c2c0c00b40c1c1006500e0704810440c40c1d15004280c08544181610a240a00c01011003401d06403000880380d020034281d08640d50f40d03c40e0003000e4506c3c00c003404050348030503c00c0d03126018141c43d80c02510030302c048280524000c2840e1403240038003c00180912a00b00c005407013aa1008020321340c0065403103086000c18540d03e01403e00240100c0d0b5191003801c40c2c0c0f4085140038505980401130610030702946503950550b10890307170282d80c1914460b141d0011080f0036409080500520515401008000300d901d250000b682c0b00c02d14000e0b92503040354048e054030f0588a0b0014014611420 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 152966447 1250 152965197 152965223
    0x3020702090a090f0506101a090307032603190b0102060403020d0e0d05011b180e01180b03060108010209010f181e0819061a011211090603040f050f0307 67
    0x40410f600224105006805504100301c0300d41c0c640381046011502c1e07140944038010103100100001d0701c00400c0d182009000751420311098006a55008180710042021030003500d030b40302d0900302d103030416848520285c140d5203d040502c1041210081800300d5001c0502d88074110420791700c0024510300954040d0050004803100c10303012155108000302c540c0c0c00001d501c60010018109202c0c6131a007500c01400c4000c15a03c9110007001990b036220060444070784090140f101c44c031404200e604483c400d0800c55418004200d1072805000d0461f0340035418047c06000041d501410b400402c610a0242c1c0c4041189d9080c080a848000d80150201c0e240381c0582001d012404014451a051001c03a510f61101d0704c0d44c1d01011840c1c0025509a4021030302908990810041c06000300c1c056101d240000d02c011025000009110780102840d24952584070440d620070f0014110481e5007044003d07000c19a42d24003400e00c00c0b12014040d4048400d8424010342d08030044000c400d45014580c40940340c1842 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 152967697 1250 152966447 152966461
    0xc08130c0306050c160b070e01111c170f0a110703080402060c190c06030f0b0325050607060518060903180109050a030b071103090114070f0f08031005010302070209 72
    0x6140c02085501064130801403c01c1007020505814035542c031814a0210901d4410402002840400c0644c0d05200c1e0150918652400c007160070703480381071081e9085c9050142010115a81c50034a00c40308a0a030b0007a040c0525055080ca00901c40d420f0481c0034042840303512381900b058401d0b0b0101400292000c0d01040040c80d00c800100428107031a03040300c6d242400c03024448640f0000d48812a060030780700f0810004560140030b040301401c03890004004001050011075115183c10740e90060000101d404250065005142c41c4050b15000d007160b44c8800852174424001e210540d0040d2114508101040c0d00c140300244082c450380e081005107080080e00c403a9000b01e041c580c0d00640c1031203540b039400308203611241c800c24011401342080032900e00305800094003141034450fa43d4141d8008000010403a6041088000c990411010060359490740e130501403810510f8820003410780c084400c1c00400d0080100107180101c1100c41d0407441035a075480190124400c170100250802d00310300c002206 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 152968947 1250 152967697 152967701
    0x5010302032e0612020316121512060e07080a02090405100c0507110307050108130c080d0e10030212010504020304020d0b0f0a0e03130b0c070314010c08130c0306 71
    0x1208060348411076160034103462988012401c2c51616045192000c10140b036002c01100d0040c40000800c6146003401e041c0e911074410020b0b84038043c801c0000e0032100094142c1e010300400c3c62013100c0c03d45465151103204584051160043d1040c0341064040b1140c0003000c51401c045805480c0200191000c175800c0c070010307080c02001944c15002d8810700052040f001d01401d070085450355105681c6081c28609901410301c1c4000c2c2e940a540f0032030302448142d07000351881c0c0d001901000d941a01100e249404501d0118903040100640a01c0904c001110740000605034070150071101c85000040e00e2404400724000d1181c1e40d610003902100400c2142480e40c02150400d001801c1d182e002c0c03101d0b44509505800660b0344801c2592880104850300010380302e03041d101012800034506d0141848650040034003039004001a10f000000c039040f4441c4d003089002c0045070302c101c2c242200c2448150140c001c20903284040041400c0d000090181d04001c0c84242d08250300401c40100c1e10306503290480 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 152970197 1250 152968947 152968951
    0x60c11060108060609192c0d020a0204050a0b0d050c04051b0715022109060105010c050a02040f060e0907090f0b03100e0102130f180e1b18010905060306011403070501030203 76
    0x30848584940c6c40019040038040c026090101101c9108490120740c40c01c11030207600d110303020b102c6c0c0101106092184e8041090040e10382c04a0300402e0702e40719000c07128010a001c440455124000d1040e0100b00840400c0440c0550340864007004070341c1d100e41c1850000c0310404100390b01c1134010422180011410b00200440c900301c10801410300340190000421000700307500c0350f00400c064801704034008008000d410302400c02844c00280510540c0e482a556103c40140203109680b602091240402c055021000400c0c40c6604249141020350078103480d508a0300a1401711400c03d40720803611843c0d0b004410002c803002d0000c050006440d090000102203104148006540030007113240048a004000e8020f00825441c82c2d4082340782c00c12408451464005450a103420043da08014450124000b0644900c1460490a0202c80c00003d13403419034111b10340d025104d5540c001300b081c020076805603100d03120550498446988a441c03001018400c00b2840380c3c1640089806d1109501c82c0c4c0180d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 152971447 1250 152970197 152970211
    0x20a170409050702060a0e0c0f010e12010603031701090516080a110c01020904060e010509010b0d020705031819030c170703021f08010e0c07060207020f0904060c11060108060609 78
    0x2410a07464100c094150342003034601c0d80040c2c0c005000d000d403040391807058a51010310310b00102004009103001c074070403a819065040c140000408000c074640c0303c2240c8041e2901401000300042070300c0349005000c44540b4444a121918140000309482e03c06100700b60244c111282c40e01c0c003540780100220380718880200300e420b4840c1c8602c12500311050f1407000c1d01d0001060800541c07600340d11401d110450340954440c04803145008010002a101e000016055805400441e5a50540306942402911030804010814032000884040700d00c0d070340118043c084022100b484c03500d005440303141c81458003400082c2010341100820880f101d0484100e6104542e4081995415540c9400040000c1da9101d44070301140d03505021101d0706030f0721500181c09000ca00c80d40ba60340b4108080000320b18001c0030710003409168002941025950b515455100c400801041a0101e00d024900000602500b19050740070a000a400f50801c0e000822001d0503200954002d241aa448604111030904050711007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 152972697 1250 152971447 152971493
    0x102030c0f0607030c1403010504020f070b0106031e1b0e03071205010903170103050c0409170310092d09030507021005190c0f0b040c08160e100303020a 67
    0x550031803030092140c07148444076440074182c035240014010301650300140d1074100304a2416112107800d0000800e480c1034a406850050720b5600c4100d00640b1071003040400b80c55206110000034400c0c4d4160065101103417180c601b007006d240404038100070b54082801e004548107221848000080c07043c14070f141601001000c80f07802c2c0d0755442450700c1f941000c00080c0c40e1a5141c005036024580c02c1030b480c6559a10303900a103129985580c581c6a21003c814221900c19621107400740d00740605140da080403140d000b540c40740d072401c00c1c040400404905200b48915030303041500d050846504c600014006180d40e0000c0d00f111030580c3c0d10440100f41c0c60310210213109d401d00103d000358407580c070703500760321551034849580d40c4054508403100150b015402c2010400c940030300324002410205112801c950201c0c038038001d03460300d16100c401031210380c000718800c0c490124031a07a041030b000f130000200d80c10008103480381e03100c200d503040000055000183c05640a846101c1c0002d00d1001d00d400d40d00380e03803204 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 152973947 1250 152972697 152972707
    0x10e0c010f0c0b2d150907360b0901031401120204050405010603080c100501050d030f110106030204150f050604080303070c170a0c02030c031606050903030d09030306030b10050d0b06010203 83
    0x751601c050801c1840ca000640010803c6044441e07156017000c080021510300c2c0340b80c40d015100401d0f00751110f14210100f0510b0701007404100110200580d01085800240d01c450780b41c4110401c5074100b0020705000070705244c1c0c1440640c00703510b04c3d241030fa8413040c8008079440c0d01c1d4081c48050a80680200d038559a01c140c00804202c018018080c0c6407500b0024045045020100006456040c0c101c01d02c20b03034000d0000e40009800c070884c2104a499400c2450812030754580007030041c21280e0000e9000780c200700003151911080f400c11f1081e184c0e661507201200340ca07102880240c1c082c1d0700941015500410208240d640208c0c0950395a92040750380d881d9521590742d54452641250203002c0104030017940d00411841c09001443c0c1404041c0c4c02849115051814400380d0120342c840c4005100d000500c13112151414411118401c0400f0b0b8240b0460700701c0c0ca001001800c8c42e105c2079440070025400b00302110385c0c40c1150012500002c00424103a00070362911204070201420340c038194441004 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 152975197 1250 152973947 152973991
    0xe16170c030402100509090406051512030421080702010318060204080a122c13060803030901050606040b040608190912020615010c0807020d080c010e0c010f0c0b 71
    0x44400d109400c04039480381c603400d01d803040c003e00c81c0c4402d8070442441340a0102000300c3c0c441071842ca5005400070004900c60701c80c0055000b844000b14a8176030400c1a055002c41e400000000400c01c850700d0016030420344080701d8040c60540c4440c00000e000c00420403402d030156100742c02c181c0100d1002300d07420f02d00d1900c50755010200d82c820b5006240d140c225218520900a100208004a2115040003075241d2071100c91070009080300b1120075001401080c201c0c0d545c1d290f440e00c180e10100100310804c6055151a0309955a030400c03240781c41a076013444000340190610b80262000c036181c410307599050a06200064034003100007813648020004c8894400c8000b842d0380a01c80f200b41c0034022804007440242402810400001d0588204510f0001502038599110340b4028505030040c0d0144e4a44803640300162560507001d070044c151586c08146816104c0d010752000d5807d10001d001c841001144200646440c0c4540000d08046403151030030750080ba009010499012101008880d42400131003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 152976447 1250 152975197 152975237
    0xa0f06020304080f0d0e150106050304150605030a050f1908030a020313120503100b160f050c0409051501060f0801090f0b0301050a0204030201090906030b0126071d0f010e16 76
    0x10b081c0c0c5111360319182c0d111541441440082c8000c6912687c000140d810204050002d21014000170101c0c100d0003070080029000d07510010103070038014161041c5410303906140d56192501980d80c0c41c180200902144000d11344034413810841c1d40004e401d170969607070103180e200942000342084580301c1c00d42c1044000480600c201c1d0902c0e2129141c260712400c1140ea039283d544025007015140c10001c003c0018820094660b5854441c2e200f026100012030616101c0d040800c5000d03965041070401251008224010508011000c2c0c0b402c600281aa61410119015040030080314082825070380140618005608003160300118280701250319044200400d003110f504884c03090005901103410f004640e40002540000d004603801409002d02f152203012030040e0610907030401da8981d000480120b03850140480190100781c082c0d40e80c0f42d07502e60740607100245060041494032024030020316860348110046040e644060309854403030b9560203050b010702c0c854404d450306000181000d02500122a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 152977697 1250 152976447 152976457
    0x1807020c0a0e0708070c08040b0703031e0c0210050412030c1b0b0709090608060f130501020403050c09070203031510020a0501020c07080c0105040806040f0809060a020a050f0a0f06020304080f 84
    0x800302c1c40d0340b072401c1c0600901c8820003500b84070401108241080c08612000c2c15241690b46c513a03046642c5200c41d16080d00142162050142a02580f0521080300041c90703015209403001e80d02a09c1c4e07000300580d0410102d610458005202007032500d00700110700d1095100b215440b0481c100382041c06580c0078100c003c030070360082c2140e00271040c008100340030f60b1090000e001040654001d2080ba414401039a4550700f0051808142c000c034370000500440100f9001f250144d040790086582d103440342402e81d102ca80e0b80c035042d0b01604a140200f841d20703200200302c0f40720707070318401a90640700850307405c0086841d004852041148039044408010500a1008014520b4141c000b003000e50300e011403050500303203036003961410300200780010080441e0200e403c0764421342c008000d004075207032850514503d0080521480d0813180218210040d40d40006a0300e6a00740900212411905d403124029510a1085070003405e40c2914505840040c046401954009120304003d9041c400c10221440e916044 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 152978947 1250 152977697 152977709
    0x904020d0903030606090f0b090d0f0c05150f1206030c0a0914130b0a0506060409090f03080a2f07060e030d14010f05101404061808010504021807020c0a 67
    0x1e5070501a081640502c5007100904080c18890207061810300300701140f0f80c0ba407003001c2800c1c4c1c0000700000c090f52840c0c1d0042449511441d5490051914142044000c2d264028a4095001c052003400d540c442d100549200302620703005581741480c003841c0750369951809010942c141c401c13640003070395582d22601000040d00101d000012074824400c400300116a0184c500344611021000b154041007510003040d521428102000c602500d035000031484a1249500c140e10f618944499001001408800b07503030403074000d55560100e501c4543c1020700303e94414004000400d0b071407002400980c1f07824181c46107400c201c1312140c1050055122902a2460400d07000d241f600009014054101c844c41103282c503650011080146604000c4000b0301300a241c02114842e181c41c4080550291246500c80070009075586580c0e111070399014090034001d0005000c02d03410080d2200425041414441c1c64070a80d0014078903440348980b800c030540d201801030000d0003140184c4d154489961600040d01c001000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 152980197 1250 152978947 152978951
    0x1002100e0c041a0612040807080403080406020c030c130f06050d030806030d080906152202180105070c060c0c09090b04110904020f120c03160302030601080a0c0b0d020904020d 77
    0x16041c01000201d5a403510441c0e00324140441c00c0296440710010707030308921840d07101440a512541041c07100e0b4081c8860007000c030078001a01008008900c4003a201700c40c80ca07000c4880c4013149504054407100000b0351550414081c400c0040e107414190090503501044440000700141c854020030500c0c8244841034001c11005820f0103104c1c04d04200c81d050741d1605260110b1a42403070305400c0e44800001c0d00b5116440e0407036044040079601d914401c00075039242d01501c90b900c1c0381d03001c0d0080a07400115480160b5109d00f504111303154003990850303500a47c0705d900141801d0810071f09444400360060152402c1514080100e2142103507c01d0200e01c900403000132029180610b070141f44540d042c4480c60003004000d00b4440107881e41c0c616040c414608517004100c00e40030021107407800781c0a280c1a5854441d1a8a00c0050020001000e00b82c90082c2d054a526a884d007410703658a00102c0c02c0104038022058040295401c594050504001100e0025181c59440400207003a81c200b03208c6501915 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 152981447 1250 152980197 152980213
    0x9060c070f0819111017090a021504140d0f020303040f18020403030f080a02131d0702030a0c030e0307090501180506030c0d0602090a0308040e040302011a0f1002100e 73
    0x840300b00246050786410000d80141c02d0b80c0d03903484c080e0a8001550072402442c240700700013159400742e40d141003c89500c9488540030703c6d002c4046503444040440580c046c941c1d80c0b00310a400f4541c0310840e419200104800e0700740040020500031720500c0218161030002203596150016034060000300300410248980c0380355141004a4403200342d4809215054a510400081000a810484140c10f030401420070035415a604080000a4441c40000c070348007844452000c900204031007545040c2029a600340c1c2ca403680da21000743d81c0c82c82811102004200180e01001c000ce128150491405401405485240d50b5451000e000d4078401c1c6c10600c070391248502d141109481c60720a00354451011030042c00c0040181380404c5030104040409481103030005a8030544e51121000c480047d6409000343c0d5031070350343d00314020301c0720310a5a040b0b0065092500d981c00c1d00c88a19030205241c10010016807007020501c041002a401f01000d00307081d03006a81c1343c507030141003905c0b4899010700b80d20041c16200d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 152982697 1250 152981447 152981459
    0x1d191e0c0f170705010f03050601032d18030c08160c060306031118060418080a031d0d0503070f021e01150e010f0e040807121d01050306130209060c070f 67
    0x2910b07090081c0c140350340010010080d50383e100d00080d1607800607040c0013409458420048000d8441984000000300010b07080d40d064107500b00e00700490164802c006c00c42c540c495102004241c100110103000a00c01c1c170004008201c0c2c502c000c04601d5070381810380350032030416a1084006400c60380418040303a52a02c0030403d100c400540452604412580c2861104100d201003660000c044c103c01d025aa40390a210300361290781110300d0308141c0000d405a11903500c1c480080142159040707200200914440f0100308480c001340c0204100070f2921f403a41940d4444008460091400e101320007103100300951520808240302c84003501040315000410100c203581a010b1318091250b000b00000405031004002e10400c481030503054484000000c201601c4900344528640260800540340c10f00744101103541c542c000b50030410608820044003500c26000f0015281c2d4003080b2000360308400e1200c2e0702020840f071607004001c94a00285005d04180340ea140c081d00d8020075400c81505500800004c0c004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 152983947 1250 152982697 152982719
    0xb190f0303080609070801090506031f02040501090b030103240209040510050a06050f0304060b06040305190605060402090303180307120303061403030307021506060f0d1d191e0c0f 79
    0x44443c003a6924021130409017401855150144241c040255495000c5146541d091118014946a892924403203181e4003c50000951191040b50b0210f0200940081c0c81c026080603a4101c0b90090420006026924800a2000c1c181d1612000c407581c200419956a5510f10455029080031040d0030081c90070202445000415a0400420320406000c5070b414941d86a0842c4d43c0554081c4021611b0082d20f00890303d24052600002c103103008481048000003902011501d216009000501103610707100284001c9106d441e01fa203405030820089010318a01416811688540140403101d081d41d550f03550504001c00c030f11044001a440718001c00c103000342e4003400b802c90b00e0110042c614500740544003940d24401d040c1c603402c0101c0803d002450a0352000e050311030440440562659a120070341074540141001c0c00e20900801020400c1c00329080001201d40300c9440c4600713900480c0f0340301d444a4003803420040400d9484c8440103c0380c2d00203900001504014122606058282400c01c11012a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 152985197 1250 152983947 152983951
    0x307080a0603060f020702181314010e030408160e04020a170c09070f1e0504030f2a2102010918060506190f020f0a0311010f1b030f0e0d030b190f030308 67
    0x80d20a801400b0301c0081c2781c0c0ca500c181c1c40307190f200042c02c40e84940003038030601400e260592803005000102e00056060000b007980910a4110407010344800e407940340c0c0e00484201610084e40182c10131a05018440b1509070414003101481c3c1180c01501001c0006280c55108a43c2c400c0000c401c05000d071007443e00001c00b150800d5190550304e4030b05003c00002415070150388001350142d0683c1e2815800d00404000a03591307141d05089400c1d000103a4181c0c07080000c5a07202e0121201852200205140e480c0030342c0c0c482c80355050f901d4800c420300e001447c1c1c5c40b0b040080040580181d692000003041d55800008001c801180301c2d8442e045015980081c0c0340605800751441503400045141c0c80f60301001c00c0c541041503042c2840c00f0303003c1e03041c1902030040000040c00b110b210314140c0540418561070010040514095805000d40c021040101c001d41d18a183c0009c160340c0902c3d20750340114041e0300700d8505001c02500a102151030400303241d143e00c0040d4451001183d50900034010f0582c440c40300790f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 152986447 1250 152985197 152985229
    0x1020c101215031703070c0f080406121415042405040b0307060f030c0c050d1d0a0f0b0d020f030109050402090c21091204080601050306060f03030307080a0603060f020702 75
    0x3405262554450b046540c600d01c03003081e80040000300140902d80121011078906e82c000d030504023250307000d01d82100550b1207401010041041164140d1154945004500400c01c01c0075041e0242d032030f401440c465070711005200551158a800240540c504030180b850340a00150102840040c40c09041c80119421420103902030b4200718418005d01e0381000e206a081c03442031034001852540c3c4402152840c840140082140c0078000c0042081070707100b40d4407140d02d00e0f03013980e005030702c01c1801c00c104483d5498825020000c18040301004a5583c0b880640a00548001c01500d01800d00704450080d90098100410701507a0303209010550400319625a40981d0204009103880d4004440000c10b610b03440e50f0764031440b829400100301060910840001c4d40d111816162180e0315011a541c480c6400d0240a00034818040080c000c2c0c60040c12800c01420068061480c40d00c501c4005c944038240203098601c920740342c0764000000350162190440d10b55254000580320350f21340c410400f2840c5506000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 152987697 1250 152986447 152986481
    0x40b010c02030703140106090204091d010e210d0c020304080c0901030b0a1524030b030607090b130b0706050a0f200901020a150506090c0408150601020c1012 69
    0x1000c0140c40004421054076084450344190b40103c12409001d0a11038212400050000c280068001902c0c1c02031100340040c145851380d031000342d104040c00c8541019081600e9406400c00300c0e0300440456200c00300c0200182d0343c0346070203194a0994151600c0d04901001a0320009040140783c0041c082400154011aa10046540f550322120311801d00609880c081e1365641c00c00020390400780c0d21610050456075080c2c0032180390b0114090306100c0ea2410040402c0c1000c2450103145004a13000d445032408c1e454104040d428038041e0001b03070300404059040a6021b60000c6021600040600000c9110b0200031078a490460300030419280a413584e511000e04280680c2d031300040d51a91032031400c0c0341003421501c0d240d500f00102e00e8044d880402502c0a201c00e00004a4140d103a003103280b00300070644211140307894035280990030b0300c50761003800d940e40c10000c40381d01a00e1441d0609904000d0500c1150f0a9800c44000510b03880903480ba40c0300810748200d984108844d142c01600c4d01031440c40c0300707 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 152988947 1250 152987697 152987717
    0x905100306021605010614041518020702150706020a0f0e01021b01030b13020c0114090325050d080601020c0604030c15030608120405040b0a03051e0f1506040b01 71
    0x185450014140c000188502c0c1c002c0b60360180150114040362038103400000a00400399074880b09204104018440f502550504114100c045011407520003203414240d4100840d1507488036020083d0040e80d030890b4040380c403050618688a18074054544036002d07210042e9601c40c03030030740a030101118032101c0c002d1019981d45443c07160780100e6171100110b880405d11001c032000030012401400080710255001c0c0a400844441d00c8159000d052051390a400801a84480f400c003800e4a04d422074180ba00f55100304048803a216001c402001c1907801644a1500c551580e40e501d806e210400340180300040070007081011640e41044640000700083d0741003441c0c1811911484003600050040d0008038000612001241d40f0980c0440000c0004005444030380006600f59030185e0720901c90248250705010130400285449102d0600305c0343c0c80030050403c130003032130700c4040c2040e2030080140d424011100c018541c0e00301400034540c039540307041119034a49462000c10044922409400e030410540000b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 152990197 1250 152988947 152988961
    0x3060703050103030e19050303040b12280903051b060f0f13140309030304120303140c2a011b12050106050a18050d060204141e1003150803070209010905 67
    0x90b1705442c008180c600903286030f0440c41000443c0c945d5032120b07405210008000a003182004041c2c510980080e00c000038a84507140742c010204083e00c1501d1003001d12107204250701103243d06c900000c520038107185040440340f6a0b6804200c4d2074503465440c94011504012203c031000300446c0d4801d65528266080d410500155089003207802030080c002d10b03000c1011358415000b00196004a2401021a035566803151818021011100b000300d001c00d090100003064551403515032071007000c6480d040da00780038403d0b20700d020300303660082d84080040d0452010382c1045001c1c020f4903000c421500540c0c040607100c0400402c20a01800e0b00d0003100d1910f001844950f0f072060803034550f0090f51800c10401e000d00ba00ca1482840c26601151f48007856040e20003c000c0d0640150013100c01680c0c20100720080d2905000e003416040c4209403245c06c08244010f042d1525880140040005140020321031025040c00c800b0b0350f003076400481320341c0d00c003080c15021032500380c2509000d80141442400076042900c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 152991447 1250 152990197 152990207
    0x108040b0a0b0312072405070f0c030513170c03030c060103030f12050403090905011205060a0f090203030c0307051c090e06012a05010c170604051803040905060306070305010303 78
    0x79041d002969101c031070a11440c0ea080000141d8a214118130075940d2086180c00c001c07066600c0a41c3c0c04958031900543c012240c0d03403041034030400070703911845a124a4008220fa500f0350741801181841001e201502500390800d4401d4081c10b5450741140c018156802030341d140c80203040880784079034000c2180440001000c1071403811a541410514003540c0c0707a4000341c0e80107001f06290240c0e60b25150400041c158015650000c40c1d4541c1000c0120380d80743c8060740224084d02001030303c5544aa00130440c07440d526840503981d86c001d0700002442914650029003154800941ca600c95030000c140802800814007007106103810004280803c040d0081000e018240584030302072246504a0002d407040c1d001d1140c5007911700d6850709120300807004400400c00c9100e290419545507290821483f80305020b140700d200b0402e0a250640c04541c1c0b120200006000c004040b03424100c1240401540c002007003001e0006041081e102141d285041c10506150030030084c480010581418010804a5045 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 152992697 1250 152991447 152991451
    0x106031b03020d0b100b070609030807141801360f080d0c02030c040903030e060c1e090a0b0708030a050a05011a0702010c050f0304050a090204080c1309020a030305090306060108040b 80
    0x1300c01990302d80d0b603c4208003190030324280c0c481c1040c81e05c0003c051081200503440055401e200c0e48982c0d1103500c4040048812010750620824210340800004102c0b80138465000090a030501d0491303a03141441c0c8000d07200c1e58041c80c4cc10150320300d0310301d901c0070100b04888040141c07480b984900c10311441d1008040c0d031091403411071014002d40e4900002036440074810301c05000c001500c140001c051925005000b014250b204200c5401040003040c00ac1c84c00f00d080b550f81494400d14112400b4280d9446404c680c003032600c650340854609000101c540800c400340c01d0340e074004c2101c1622840c04241e100c05a0f80002c0c44001a0340c1b034900140180030b078540b17500144824030500c0f161034041d203200584683d000400083d0191240242d440c06840f0000000c005442d42980e01d8102c46070398428a2081e030060740216040d90f00010340c10107060a21b900342d4404101c2901000c18000303880e40104000c69103070382056000480005581108d81010807050360481c1e800c0c41c040500c0c5c942500c8404010b040 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 152993947 1250 152992697 152992703
    0x906120c030f0501180b1501021b0103111204030801080625080c1b030a030e060112080708041e060e100f052a0109021f0f0521090106031b03020d 64
    0x6002d03200d80c28000250b0242c1c41c8844a0041144850300c0d0f400c1280400340202c2d1046520ba800705a05440c80d480810540710000c0700440542050b050302c00154050000d0088101c03c01c50288040c00c0040c3e82c0039000341c05540a5207860340c5950501c6c0c951814142e000349445104203144030340b208100c40c149021030445036946000000c54490756004d421382c0c414074000d1501c030039051180b050414008401805600e540351001c00078245940c80c00c80e00e800003481103607183c81c161600e140225403020010a50148503680e0185041e0f02c4000002403181601c61030305020308225000d10901d85c000c501e6902c940c1080301c0b400108801444024600b0071070f100c0d40007c001c004200606c0f10b40181c0c00c501c841d10500e0081010556420400900030103858070160300c80c4040c400c4160300310300d0b0010003000c07010403551403944141004109840582c0440a0340f00b11040082c9050b0b055080501c0403401855520000700d402361860800030004401841100d41c0c02811000c00c00042e925082c2c41c81000343c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 152995197 1250 152993947 152993963
    0x619030c0e121b0d050303060603130c09140a05040b1b130b07170901050301061404030f1101020105100f0320060a0c170f030c0c01060302060a02070906120c03 70
    0x1032080007221402602024250041211510040c0d40c1c00041080001c510344680c41d0441001c6500400025a09460700174005030010804180181410401590703c0440036114450510440d40c1da00b868071020b43c04075103540c0d07440d0041229143e014042030341151621005019504041d11101ca1403113001d0310b80103070f003903030074001c3c10640000034107803900e01c0c40c0c08610b416566518010501154084401140e40e03e4040c0d0340b062519000d8010b4510012040c1c0d106070941c3e0030140b0581d102e8080200d40101d064080c0000000071359911a509400d91103000c142c0195605e201c006400c0d24030180c241e900604524805000ca085201012000c8070b40141820000d102c801c8022011504007400c4150440c01c00901c2203803c03178100c0318441d01140300760949480d007001c0700e0b40d800341c03801480030075800241d0030808145a6020403025090701e02c1d42400001c1c41a0783e03940003820960103603460002581101c103080125041a108100c010154030501a0034643c8aa84060300c0184030302004000903 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 152996447 1250 152995197 152995211
    0x90e120a0324060e030f01020f030402131b05070506060406060806060f070c08210901020712060e0f06070f02061006050307140706020d0c0e011d0d020303030a0509010b061903 77
    0x211503148403080c5840380500c800c14152200b40044c007460000b0300c1070703000c0d02c2490440e150012051007160214008011600d09544499003007011890000032112900c9481e943c8108000628441c2842c00e03074840d48901d540c501003454a5801c00308010100d40c0705c1e41c81e1038000c00c001900003036a580e001500311031040e50b684c01070b103030100c05008600001c2c0280901ea08045034402001038241440c01180619050074218200e6104071348c8030f941d40e1940143c100301c0f000c12042d216101c20080f014803c400100754000829480c500d00902d400c41c646080d403211061000725030300200315040c0c111442c0f015194919001d0a00aa800f400f803080c41c082200010006100d11710921b80d003480d5902c04103441b6030322502410b0060282d003110003171500b154030b403880c0c10142030b0181c10031039003905040c4c482070100d00010700300c038107205403502000b90040c1c001903001006950070f10081d0b10134021418002218113106404600b19044820300301d000d078008001501400b10101c2180108800c945408500a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 152997697 1250 152996447 152996471
    0x15020309060109051e1003023a0204020d0c0c03120c020a0f020f0d0c0305060c031612020d020a080411040506010519020115060201050403030f0507090e0606071b090e120a03 76
    0x91401840c8680e005d000d69084c040000c2403003826400700d074000c0b81c0c0707102c40c0e580c0f841c95150000ca2078004482c0304000003e000c1c03102081c03980d0700d0114a000500060510182800307020569400c2072101c0c000034410400842090b42100c00a40e00d905031060030040d034034900c00003030b43d10341103018080c04c0500c1e540b20100840d82c3d20020b40c0c070454006810202640158a000d01c0b0301e648601040703c3c1c1c0d004442c00914551009402e0300e01c1442910f815541d10715074a503066416515102d0004120354081045180c04e0700b40b4001441c171100950344180704c900d003e00b82458100740300312079144a94104002d0100603a070007820313038504a40252580c0041c030000401a4010002504444188031800e01c0009407150191b00c007038801c0f40652014090a1041040c03001103480486105d0007140845009210900815215552000e000307801c2510345602c0d51620005180a800e00d40035082d0b20f4501880001814021880300303454810091a40c0c40c001e40180302d081c0a860f00030010507944584e04091 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 152998947 1250 152997697 152997721
    0x6040902180d080c1c0801121703010f030303060f060203030f090f07090203041a06090118022503020d0309020d0b060f04050a0b0f090f070e0607120c1502030906010905 74
    0x201c100003403002c0000c9599142007001d90708544c04809003400341000d0b40f0104240c205060894a900b46c0d104034083c0e0a2801101801c0b01000341541c0611511514610690114005502800b4000d60880c1c240e4034501c4c0090175100d858200320146011100200040d40d0000103990704050030205000b0300d0340d120300d0303079604e04030008905183c1c0341300e0703400c00069425041e030085010b0360207807004c0c0001c400c0c001a0b012840e0000c0d10b0b0703550000c59081c01040001c0d5a100458041c09040c000980350860b0030080703007189a060340c4d4000091001408520425030100145104001c6908007131088140d160001a118240201d01400454261000400b20f60b81c60081501e0220020402c0204e414000507140040c00c01d0981580070351100851954030b49480e41d0203a20600d08041c0301a040d585200c01203079541010b001c4280c01c40d405000000002e1315000c850070030104c05681c0c01107a0500c42c14441d0f000440c4465a1004074410820f10550f0040441d03441d041d10800140400c1030b441c1d4a404e411 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 153000197 1250 152998947 152998987
    0x4060b0406031d0a15050f041a190504050c1f020606040b011202210a0e0c0d030e060403060f05010506070807030f120608011514010504060c020307050402030a050f010b0906040902 79
    0x3068012038119408114201c6004845c51a40c402c2c00c001c95601d402d00010954020f0300c0180001102a0142e826081c40340ca006034804d0000181c0a2340f29403550000d004d8440c191005c891a0700003280d107408505021181e1850664800d02058032041000b0000c0d403110340140c06030340110b440b0040001139900401108403441c10041045560382505802941c0c2e420382c00c0400690001c0803004940b01c89003500418188030071520213000b400b8011006c101951244800480610110f008000c00769034a030700261000710f000b0017000c90000c0680c48240304403007050300040d01c078503400d00c0741c400810203030000d9400082d41410003094503110201d080d03420194001c015004070b420120003050081c8190440500a082081c01c10801604c0d0131011045000074010b403400243c0c14003040109502c0b070100e4440309800a003c3d6074101c2e0b1100c01280c141da2048031f10450321a02c4905008a9601c0f44041d50f00511480c81c0c1d00781015030031400210144502e204401d882c03a00412811480710b41150400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 153001447 1250 153000197 153000251
    0x50703020717010c02010b2407060b1c05060105010f08040206070501290f040c05071203110a0e01020f0a0203100209060d1401030b131a13020307060305060f04060b040603 75
    0xa440150340d145543c0681656441d48005500700101c0100c90709000d4040d0501c610707103040c0703400c84000108188030a03401c20300c415503080d910340c0740041c802d40340e004a0319025280008119000d040c94200941742c0703081a4442410442185075400c5e41c694403c202a8200b0360440b0800e40d01e04d11030400318090b02c0c02c1d026440259030075401c9107110b8030355107904c85403594050f6407844140f600541040304941f5a0442400496410441240069a40c00132120f028000b814009141e40b00c2c1100c10110341c1010700d840d804103400b208459040d6804001520b800c3c42500c005100e212800da000c261501200d500340c400450700465440b04036990542a95081502c03a181041024400e411568010780b0030b00c4161110200c0380c0100c0c50340d14140700e40b021519000004004095503c038055806154000d00800302e10b60031041000069806004a40061004d13581c0803500c1c0c01c0c841c0c10403c04c0c202a00c200b5118520f1302c101044400d405509071021991035040004495280e00b0341921001e062560f80 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 153002697 1250 153001447 153001469
    0x301050607030f0c060e4e04090507080a0605030d17090f0a05030714030f070b0a06170106030204060605070f02121219030506010507050606040504080f0a02010912030510060507030207 81
    0x50400c46c0c00041a8280300036240011011500c0d1002d09203110030502500300c84d42c1c0c488800c840c020b81644c41d5201c80e03419840100c0d840c0555980b021001c903841074409000280085040c003600300080e005460280004501808441c0342e101d030701510f462a0b00d86400e8480214000007504030505129082ea01030100042c0c450006491034040d4580c1d100c01c00460710000781c3e0071205c005010001c1511034a507060754180b032912146440300e6840c0d9000521410410782c940c140403640300440311801601d500c0920020030700b0350442c8100029a401500150308120092150030081540821055000c40d019200006000f6100c04400c0c204403040710b9583da82c0c40700180d1a1204440914030b00020702081c0d50401950300c1d5030b00119124420034901501d00c2e072000000c16081d00d0300d80d1003582c0162003074180b140b1708841d11302202c0007a04980304000141c0d5481d4504010301c00f503842ea44074503445500d030400c2640b51250040c4c4500044c0d014000400c10b012a21703104040c020085030380034004440381 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 153003947 1250 153002697 153002711
    0xe09040c0f0308190201090312050c1b0c130506150309030904050408030a06060e0607030513090e0c0a120f080703020309030105010e01050f150f0901030b0402031006090b0301050607030f0c06 84
    0xf01c45101c4c3d0100140003400320550120b50503040c8107101c0c0384407195040d951500d0303040c880304416001e042c0151820004007000c1200b00c0c040c03c1c038034a91b1703040801094041e000031a4040100440c054025043c03003441420b000821040d0f0740c4a00018812980481c6110b440b510303002c8225185000701b048290f0030602e0503040c0824000b5034005148101441c0b132043c400240c0700c41d02200c1e01c0510f20321103604400700380300d1980003900070700c00340c260402c1c1c50200e2440259034854140c103465106601c65a25004102284524100704110202400c40b50044001c0113805581c1c4c0d44e490f800d03010019000040c0400d000041500c00c0c012100b409200500902030380d6159684040d81c07000a1007a1407180a0b080e402d01c00c1e80c10503924140c09003000c410b10b142880b54030501543c4540c04258a2810969552945820741d039552025502410400f480c0011113424040050200c81c290f07005441c4014007030004008940c0c81c442150283c0c1c1c0e240c5040c00d0003001021064503240382e40c4100500003401c0c801 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 153005197 1250 153003947 153003953
    0xf0b06030c03180a080702010c021906090f0e0108070308130308030f250914030a0b0a02040609051906120f02180f12070b0a1e120b0a05010e09040c0f03 67
    0x2d540682a910f50190310301e40329104260703403803c80050040461205000c8900550b008042c503040341400a40080c5601c050b03401498448011a00a20045a0043ca0a101c0c460024140d100682416003080000754100102a603840b0f00c144002440810b000410b8940f44000c17805160055501c0703484651681801013408995450032910a20309200c00701c010a1074143c130480c60080582c01d83c442285581c2410101300407889424140ba8043c817a00810000149498260601c2099a0900144c40d03608210000b0446600e0391302c03da1007080041112130703007400cc880404080300e606040c210401ca40c0d007501c00014003401c0010002080c03022600780d0589440b240021030101d000c8500e040c0300c8010b1800c122244000c2c0c0149000790780581001d00c83d070b101e02030007032031102c0c1351741003048100c6038020000c0740520411050300b00140c5007c01c0040a0002801480c0c818042211080d02c06810030380002d0152424030700f02807050300070b000414207115500040c8000340c070f01110500c030003d440b42 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 153006447 1250 153005197 153005221
    0x30f040c0e0412030f0b01050712031d06090f1f0b0f0607110307170c010309051501120c0603051e0a140a02040509010b030f040f051c0c140601060f030f0b0603 70
    0x24000c0c2010130705081e1701d040010018071aa194541e0161030303003400c004158880e5008043d9000c84082416544c00280500d0340c0480d0080440c85841c2004101e9031401e201000d060030b404107400034080c1c0c0454188540e1a603030180d0341c1200384a4400024061200b0707000250325240031050706801000004108050026103400181e0b54072003501107035000da6807a5103440300e803c0501601181500611461030040d0710980141110758048c400f1545004141d009007220001c083c1c0c0481c0d04c092568012008100350921124002d06860804210518280207008a12005600e00301000c028141c0024800303641d513031128042c200c1c85280d043c840d203001035a04000354068051640f0604440d000024902d0081044074440c0d6501150304019889550f181120004180400c1342c41d4000e0580210320301703000c0030145503402140e03030300c4618584144c20010b214150715a0b00000e2600308100511540ea00484041101c04041c0743c0003e040c101146450b004140c100c4260f60f1217140002480740e440701d00d03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 153007697 1250 153006447 153006473
    0xa03050906060915060901020a021306030b1806040311030d0905010e0c1c020609150d0b040e010207050601150c08031015080708010506031801050a0504050c0d020303030f040c0e04 79
    0x32000301c1c0c4103515070701c0800c203c80404880510100b29000e02a800c5410094080c02800d00103004407078841d000c0c1e41c00506001c0c150501030814603543c4d00100b043c404054891900411551088004d14240d0001281c440c540280302800348032039122841e0b0328001c01c008881d00310907004020440c200d2580341081c041c0c403100e07240b10700c03a00c99103846404600c1e05101e80049545422180484440303e5424081d65400034000103038001040c2075070341c502010b40350041c901d00100b030400003080b6240000704022260601a14a520b81c030505c43c0a0014100181c01815103030387e071255032801c89111408480030103012174020320748a13021050056070f2241580140c19500340104281c3c0090484804503081d07001105d1150000300514010825402c00030300468000b0b440076140e0090000250b180303402c0d0381041e906101f94607980d10030032040c0003003403215414081c8202c483c500140703142c0c1c000a55a00001d813420841ca2041c0001c0303010040445c441c04000c0c24900700e00501c40c0b5090070540c88040c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 153008947 1250 153007697 153007711
    0x503010f06090614061209010603080c0706030c05070203031602061c15060f020601140307050603040b07090b0a05070308130b1f06140a0f020f160801180b18120a0305 73
    0xd1843c045910f1152240042800902030400b604040411170501c2c10140c010305900c01e55540d03100c020010580c02002401d040b10f0700720007020001c0c5042c4005084844400ca060200a0103000410040c0c2e00442200c0c101714000d040c041001543e40001685403003088100c0ca034105401c1c4024100d0a1f103034010909014103120341441143d82d4480075546d4801150071140160014030050100c01c00c00e16111100480c0502211440303030302c500c0032076030315030082d901640c0401c00d200400c20801d038060304200140041d104c0c2c16087c0000c0b4103014003d801000c2005080c00491400210780c0e21112004002e6030b600181800c64604080e19070315201842c0101c00303000700100c4803010498070701501900032450020001d03d2324042d402601105c082c81542c04601c2103000d0820f004100c2c61382002918260401e0254800c0514a050305a90840351445000414040c048440902085e42c1041c000d80c007103015144a0034034505070a03000c0c2014008803140f4900c91010804e041c000754103500443c45095 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 153010197 1250 153008947 153008951
    0x30b0105100203090d080c1605121519110f030402130905071a070c0801061502010b0907231204060c0201090b070f050405121005070c2a0503010f0609 66
    0x625401846540c038514800c0e41c000d40e0040100c07000a0400628500c0d01c81e000d46410790038001c0c0c2c00c140c00d052442300500080030501a203030a012a203800c00c9880f0702202c031840100400010008642c1903aa0010600b402280303110110440c0041c494110501c50b540c44400e183e030320380e10540000c05039081a10b0690040c0c223a82104040191584078011020303411800802d1002d2805001d801c00d8000c1d4440e0010900050180c080050044821080501380620004c924141841c600051403143c1031018011603040c1410070b0500c1d1592258550440500c0c03a10003010301c0381d0f80d071130118004200800301942c280020049414201c0071207580c0507510400041c41900b8441408901ba41d29940c6c018241d412240c000c106501d000740c842c840015040d0800d5800d061751303040065a10f5605400e0320080303070000303060071807001c89621826038031113120300f0810b481c1d840546a10701108180703a40725030480b012942c82c000c0c145e628050000100b400034024001c0440404044016016902c20b42c2c04c4a4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 153011447 1250 153010197 153010199
    0x70f080c01090e0c0f0c010c02011e06030c0b0a140406020703060506090c090409030e030a030c2a0b070602130909021e03030a0503060a030b04030c0b060108040309090e070504020310030b01 83
    0x5031140700b00d0001c81d0380c1c1003c0d0710156211051040220341c0b021018804408080104802085003802030380203a00441c1c0000500f002001507658140d40c0a210408010346041c50604c0020300d021342d4041651159100b0b162500e04000d41520101650049030301c013071002050002d5200d5000610000f41c911400f81840301d5107496013401400d400c240e1b41402d85510502002c40c05041175802184d116001b40b400c500c45c40c640343e01007810004403200c1074002903910006e00080c03000001c00000d10480c0d008900001d800f04100c26500c65150740a0700c24020f1000910105000c05a01640c031403000005c02018280d54415054000f09000e035412030041ca043c448070559981a410f000080000140185292001c51802200c85a000a14190748000c1c05040440402c0c0c0e8080309501c10b5100303860709000e06401e4103103000c0170b100082800c1e04000d0320b4000c00000130f81c0728185508942c42d8000115080750600002e40c100310182c0c100d1034200d0b2000c804c200880100700030305400c40e0300404982d0b03240d03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 153012697 1250 153011447 153011449
    0xf0d0e0a0b0301090c170106091406030103050a030f230405010e040605030c040902040623011e05072904030e0a12080702090c220e070c0c0e0a0e070f080c 68
    0x6a024401e1001100d028030040105070581e80103807010001e03910300781400100c1e40502c101410000c0c2c0040c80016030701c010611494038042207400040000b00c0e401c90443d8916940c196803000c0d0754100030200600b800d907840c10140101545243c916008100e080000030000303482d92180c20a01c500360009120b100801c20300c1c01c0c14440d40d401c2c1d540c0a40a40410350030720082c80f018148242040b81c1080d902c030710008441c1c1c41c0300f0300b074403080650401080181c0c68000c0018148100180c0004840c121116100241c0b90000c04844589a10041c80d40a06c0380705c58a034540c00041c02c818582424003242040201580008000741221003140c2c411070307541d10380c850501c8140d8055001810000700b004804090303d42403106542c82420300ba890b92070160f90b03070440c050203804444d400550f000411000d01181c0b2450b101c0d681d0001051802510711910394551000c0d81701a803180e005030303140040119240d0001c54100960400181040741c0301c40f550fa04860403e100d0070320580706203008a25203080d403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 153013947 1250 153012697 153012709
    0x1b0a0c060f0210050612030f030a110408060a0c030617070e07020f060121020a06080f0703051e040c0b1309060504050c040b030c0702121f0c021506030309030f0d0e 72
    0x9441042d40c0103020b03401d080a10301c1d0080002400040d030217280e042d40c155100200f04010f1030010516028261a814691003100640d4414022403941c80002c0c4828080c0c8840052415444040c019011500740503a2000f90300800298020841c8a81c403100400490240001c8110880c0e1035052502120f0350398440c01c0380ca680b040002d010b119040744004111031504400750008290800c09110765440596001510301c0705c80d5400240481e0149040051070049005450b52041300fa00741401546000740e03813802c612500c414803a810688202c00701f0700740b005240c8000c010308910303100c259490384d803580202e00c44001440f500111508000700420749041034000c42d406004180e4140b4182401c0c1128413089800c001c10001d613010051000d0b00c09a600d00072400c000d000341e00044c3c44e1a2a40d050103603c0c6103400110081414200f40548411907400900d0b64100702501801003040d45800000a04520a00c41c00c1035040c452607108800d4403501241d48e0001503425281c040294403200207101e1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 153015197 1250 153013947 153013967
    0x506180f10020c010e1908071a0909010603021605030d0e0601150c12030209060409060806060301060f260d030c110c100305130c030b22080711061b0a0c06 68
    0x40c1c003e40246012540104245180c1c0c541c02002e20380d14110071a405070705840a41d008040d958400442040604032115111040310560504145004060700c041075002c0700620941040590025a4261980b90a585002c0c03d42c0d00405895643d92094650000340181c085d0308011809150300016142202680f180e403882c501e515110769055040d00c078088000d90a40701c601c00c1c19001c1060b2003180d078680e0000c5c000340001d040700003070090510000d94509980148286e0180c1e240c0b07c014032940c1c8240c2d2041c4201c900d1990002c03207000d4484800840900c0c0008091803c0c42003d1003102907a07016005080703403500d0742e61050307444000e840200307507202038008103280c02525800f040141c10b4800c1e040241d02841d80182941c824013550b0710a1036041465000ba10b4540025052144403429598000038902030701e070310101c0711551500c0f080264450024010a03243c080300124cc4188c079010140c2e400340d0b200206400038404411203854465000000454008101800c04564580100601d01c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 153016447 1250 153015197 153015229
    0x30304050c0105030601090314030301090c08100506090f1504090b09070c1b080303040f050f07030c0e0603070b0403210302280509130b090901020a0807050307090506180f 75
    0x1c0c40d4207001502d0a92020307005604201e40d2100c04804a403805a004500c50175010007107550f585050b281108440301c401481e020000d035401805005640040b0385000e943c0300325061742c0c3e6482d01e2070005030620a0302e40210b802c10114150000c401929a000d07100b1074805071001d01860203c101040641501203074403c2c04034004c04403040100b004c0840b0a8003400d5030708903000d2010b450b803d44070b03e550000c0350210340e04c51f0b5071540d600410209025591400c00000d00a2841c1811036036030000c031402c1801100f0303014440d0383c0003c140f641c00700050707801410150b0942c1d40e229100e00b0841400d48802980c041134002c81c20244070518440c1c4212900c2150b1203016405050300c0b0f0350b0b0504a840300c0d2445108102c010300c6005043d0b0349500c1d03200c508400682c40082c420380c0200500103929001001001d03642d1040c4080c005c4203401101a55100380b05141196032a03882e5001554104640d0f0031283e040b200c0810aa00f038403513800414444240c00b02c808070001d1542c0c00400c41780700381d810410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 153017697 1250 153016447 153016453
    0x1020c060c030901060f03050a020f150403020603091c050705010c0c02010c060f1e14011502060f070909020a0509091014101101181406010803043b0106030e03030405 73
    0xe071081c16500059a0000401030000c82c1c025034034000203400030010b400c180c0b125006005c1003811031a0030301303071036a22802c180c40e0f1101c032011741003a80e0b002d03001d984000381c0100350000004d038005105011045051110599103011403d010030b000f4815080014121881d40ca0a0400c9100034002d207201c0304c800364160b560302c41c1c2444558541c0040d01032907600381c0f540341e2210303800312000341080b010031000000b403c00004c0d58030305505a01e1041806901201003030034805d00300d100c003540c0807034865070103030302c0c20580d0200e034a80744812501a06070f0752240c041d0620228200c0700640c0c1c04070003010401d0003110058259150020180c602c1da0041c8601c01075072541e60004089070810034199029240342c0d08000032200881d40e960307401d440601402c68018084500200104030300d514131a070b6502d240d207006008640c1803000840d0b503403080303000d5842050500451240803a19604201110841140706000840254050b010750b05401707009680109042c90728014036440c0c000240d0348501d03044070003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 153018947 1250 153017697 153017701
    0x3090601090c0c020a0314120301031106070201090e0a05040c0b0910030b030118060c020601120803060405270f0c010201020f0304080f1209071d0f060108190c020109120201020c06 79
    0x81e68001d20200e8036041c03d0080d0b4a52000140e40c5c1c0c0a410001180201c0d5528800001061001d042010f8401040c02c0c0940510041c0049024070b101c2c000d01000968611742d503000c50340016100320f00320380c0c030000710511903204126088c402070300120700903440381d010070003000d48410ae64800c40c007030f582e441a0065240c81c501202d07144240c1194000c42c1002e0000142648200c48090221910031000e80d4210307207034036100e0b015a9041100d10b0050008400c40c0d00c280ca400d64139822180701c0600410f00c02d40c0c880d40803520700414140a1070041c89240c010034044c0514596032900e075490b80c17490b0300640c000c0000c01c1445500600840f842000d4060300c09242d40d6856030340c03245903000541ca03205104001e01203e00c494401082d618001c2602500406c481d519040d0f080c00e03144050300809a45002d50018030100710120088150001310908007414581e80b4400d801c10310300301a0011400c809d0a00c4440d102c4950194005012940505052074010038211004c0c0c1c00c2c0d218200c80039085910400c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 153020197 1250 153018947 153018959
    0x6050906040f0b03030a0c020306010504050c0d0b13180c050a050a0b18120609061005090403031a03030a0306080c03030415110f01020a05210603030d090618030c021503090601 77
    0x2110142c00b8422078400207414900101103131954020007002c80102d2040c10303d0780e0541c50100290713070051008030380a2110749010100040e0300d0045500300c01c4640e0b15420380e48016503a1101100610204031810458000b181d602016074042416054500208030075000c211414082c03403c4e4161180682070369181481c101403c0919404507049031400e07030f460781800b030003903407075008482128807054020442401c0410b0500d0400c00d0240101d4400044018100310035102ca1840e5680103130507040c0058420403806440c9400e06a05079240e0303042c040007540d02e105640560080082c1e86484c421124490482e10500d0b960b403143c4d010f024800c0400c2000388084500c10707807403e071684580109445110075003400f01c509a801141d15036020600224000004498541e003a2121380c015031600015070074070134003007500c83c8680701e03080d05455240c5901c2d01c2841034a420901c1600300f49a01d040d605029410b00900c0c920703881508038401d0400724a00c42c000c50b07910041d030303000c5c00c002d03000f51445074a03001c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 153021447 1250 153020197 153020201
    0x7050913060e0619030210180f03030f050307020316120e01080423030c0607020105150607020d1104090c030b061903031d0409063905030f1315020712030605090604 72
    0x1101090b804e50481d9000300044c1c40d0311100d000c00c546a91518018a0b080c805024a140301680048000140d041c1007000401ea03c022030030752a209030306205035a0380710360f10100e09501c1404814515a40d2041c072100420103511060381e00d4007569a01e5501c000d1803203004544070741080c3e8005c0d2400d510a00c01044c6041c42443c0300300544008070490785080e000c900c4050400b507044035003a0150759510700700a01c5081d000441a8180000c032000c51404040e6030001c0d100380c00c00381000d0010035001c921706190f40c0701c2d0303030140304038903000940f0705c016907660320349002c40c80070842d5518001e07025490407200c251081c14403241602c0d030585032543c6001411004807130703071040c0c0801c16034030944594108001c100d80c4e101e4070460b816032130b01600d030a500405880890710080d44104040c0e02042c10141299a0300409403504103046c0840000192034000c018140c0c0c10300e11002801c0340300d0301d5007514858440d950003003014901c80c2142d0303905c00c03221a1041d002c417419846620f403c581c4190010710285416 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 153022697 1250 153021447 153021469
    0x5010504090203060111060a140c0c100c0201021606050402031005011206020711061206010e030708070e04020303070b010602150604021810020a051f110c07031403090907050913060e06 81
    0x40c03400e0410580e408091902e071090a81e1485207484e601c042031a00311000119042c2d0000114420b1481d22515400581da24001421132050cd41d54401c4041c18451003901200da00003880e1007010050801170a000008200688040340703e481424800aa4000140100c5041391052440035191548585500703019500801c400c560b10020280101e02e26501e88014020441200220001c50f00e020380000d03114030480301010340710341c2c042c0c00d040056800008103882920450b1446022507195032000c649075001300b69005140701c10400c00420455030000b140200d03584091568041900c690040c0000c07440b458400386400c4124908400190808031381282c84013a00e0300c1214484a5a901d8842c00c0c030000c0780911104402c0c0c04600303202c40c0a10302910b0544408811036524008140c000540e480d03407181701c01084e9108010705102c403400e0910956491038400340811100c2c3c0380001000b4802d07446105072a104148649000616030400d2080750155180c5046440003a110003003048410b09203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 153023947 1250 153022697 153022699
    0xf0305010e1b0f0706020412030f031401090c0203040b0a050306090a0b030a080715060b0315030114040f020a03080307210c02101109040207060c030b01020a0c0b0a030e010e070f09060501050409020306 88
    0x104004c070100140d101c4c4010002441240b02c03450b124a414a001400c03000b442207008205410003904039100c030503074050b581c11035461030701c0082e2031107450350146e007940207580c4607003a007800214080d484190018025403003620120390800e265681c4440d00030840c0c003080c14154140e80292402000140c1402c000c0034894041d10010000844190441d0b09981480d00890051100807040c000d40c8040300c02c0041a88004030003d100c44a501015070400d960000c2029040d803813030030005030079521680200310103540c0044280742d413403503c41000b820461103581d4000756120300300c103800c0b0b040020740725a800b0700100341d0180072100391501100d400b03001951010002e0440070003200b485552548000c0150038843d07640031400301c14000010701221040e119883c10754209620590004010240035070503a00350302c901c0c684034110070008600606a40495a4041d0b1a01d244425080c200040e10340031940310400100c10580c890b24014150b40d0103100d1180800c0d0107000a0001d450150051540184 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 153025197 1250 153023947 153023977
    0x3050d020901270501031808030402131803080103021003020a02210408070303090e0a0c020d03110d0509030c0616051e0909040308090706030c0e10090e070f0305010e1b 74
    0x403c00410304030f40e000001c0034810400e00304106558040c040c0c90f11402c280c80503000404090f80b9081407a102c0100020f1191125080391038800304594010070f40d03a01c03494690000c1d108545000341c1084002e00041e4030034207041e00c102c41c0e118440d008491017100154040c00c001150801040040a00320301e00e070510080c01c0c00003050341c1d041005600c00440c001d03600c81c4011442c1803000e1f580d82601400002001d802c00800b03d10300d580001d01601c40600c0c6180000703c40584885401e010700606512030441810102403040d00c410010141c80701e00c404400f595416200d8001c14003003000910000004a2014081100441007081011500855030005103180034028000611980400c480c22008503500e41c4c1031080070481041a0005000c1c5030401300104407540c00042c04c030589090045104601c0120b6203121a407248402e60014420581800c3d03082c1400d44000d400300c51941c4000000174906000004e20a095900a601030b0181420785001001d0703c2c156015603a00ca002c80940c084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 153026447 1250 153025197 153025217
    0xd08160f020301050a0b01260412050408060a0603110102060906010b09060408030d2004030203030702041a0301050901290a050d1b03030c020901080102070b0609280b0102061303050d020901 83
    0x10b00c0c00e008181c4074035410840010544203007000900b1032046214104c110600560103000141000e40810f42c0054005100980c1148044022500c07841180c0108000b40100ca0038070400e5090360b009481a1303442901d080ca64600500012680c0b04021101103e46078040c10040005455080040000e0100680b40340d15150315410110b1866100c50400792840f80e47c5c0002d803201c03481d0251848050028080302e03c1c034041c995000a0b980b80504180a44110394454804512096040201d45015000390091201d864501d03d0540202a1840303d48038010051042c4050041d40401220444000420a151417800e000500c204243da0802c1101c49400100e40d820680004080d04c0c00191310a5958401c1d103100c6105205450006900c480010780c01817103594001842c0709105a8400010759031007015035100c0700314600340d244020701d901d000210404440380b440300701e80040b01480001e80864a00d5120803b42c0581405281c0340500004c1c0107020405500b8480c2d0024521b21b1414900b01d4914 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 153027697 1250 153026447 153026449
    0x122d0206071a090a0b010504050c091c03031802030303010e0718120c0e0705070201030b01050418050f2a070204060f090c02072c1003080c0604030801050d08160f02 72
    0x15480078000307035080742c600d11901070310403600299140d10600040c09010300751394540c1c43e0f009044043c09140c2c4604e4484000802c0c440020b81510314080c001411040c5c6420b40c220540c82516420005800203403c20b811424409540114440803590140041d4170710380c82c10051003800340c00603041e00c04012015811003004d903050b2004e074000d00201140715840c0c4800d80751007030b03081380c00758007814400b00e20004020b03113035030881c0c1503030a090340a00300481c941c180b190040b501c612650f04030303075030042a0310407089130110310b0f81c001481035015002011654940d4110203d41c040000520b1000340c800c2d4040d46407186002000c0d14100784042c0c40492901e441c0c0d00c00300b002141503001211100da0784c9028030f0103254100034841c0141301d000290501c1c454800c1030319800c0c8030580b8091004066807004140e40d40b401e044404025a041010540c88055444001c2d841d103000b92410b4000541c81d00000c80c072864000c2003442019070000b0380a24001a903081c1c0079524490420540340ca042800d5100e001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 153028947 1250 153027697 153027709
    0x2091003050a03120b010912030509030a060606020106090b04051b16060203190b010e01090512160f030c060e060d05040203010b090702010f0606170117160e070306122d02 75
    0x98921a495404103250413412a404440001c10321074100810320500308003406810000440c010b405240055440e400000800c1c0741c80b040d940010040e6103403000c0020301c181e040d4003d80075256034120038040d0011440800041d5903003680d105c0343c02062840d0f0049114841c0000b0240a00c1c5a058001c008203503843d60000c0b40c10440f8a5080303a440c0c041c1c180c00c5d004592203041c607805424280940507941400000380b81e658103005590150b000003900780131512007000401503071700e080c42800c000d807522a654402c0030780b030600c0b0450742c01c8040040030070801d00039403503102c210340090040e40c00d001400c0c9101c0050b04028105a0b0955660b041c5440fa0383c0300c0322f1019208882d160004592460340c0541c030422032700345a2000003002600c40c548650f031342c41500e43c1d504580c2d6a0414503004c0540410360b6080020112211034500b0300d4010009501201c0301f1650310400454400304441585d0312100c02c605165000010031030740d440848088140d00d0011518110355030352403a0303032030810715a01103a2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 153030197 1250 153028947 153028963
    0x100207030e130203090a02060d141305010c140a0c1e030305010f06050f09040f11070f0c2312100213030209090c1807020a080301060e09060411070209100305 69
    0x20015212207804400c906041c204884280c0301068110301e1341c504807010f2519810a014020701c0342000040d408a014102e400402a43c04405000203881c2000a0100e1902105240450b080d5080040100c0240d0107840c0a00c8050100f0b0401480e1490002089584400c0460b00f1540040714041440080001034103034100c40d4401c0d03d001a4a504054811100b2350700350b4040c0080000401642510710014810f65030b5000e0242d0380070403168a21084040602a940382280080001080b81c8040c096501d6100b64085d004980c501d90b0603440300020003001900305410552015030901c1130301c08c6d0815000702603030611040306a40c1a03010020f01c09003640d0190202c0e2110080042040c0306501d401100759800006010013050700016a4000c50200701020380e158014040c600700203901c0d24000e000030360826502100c42d135036a41c1c40702d50162081c07065840d0980241ea003440011101c3c2450700c1807841c0203040100c201d04000c9107500b040300d910340003014400590b0b940703800080003880802441d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 153031447 1250 153030197 153030203
    0xf0302100c050c10060b04030803090c0409051b03010501061b060b0a0b090a141c03090b03040b040516030503030c0d020702030109081e09090c070201021c11070812090103090302100207 81
    0xa665501003c0c01503103841005041211050714200081040754400c0d070848040f81c0e800401c1d941c496036008811410304100301c070f10581150130407202c20100880440c410040d1800c102d401b103440c80503001418200c60703090003103a0210720b6000621141e01c4008101000d154450540441c3e00f10604000c41c1103d0115400503d0264020500010714900780c0e5a0344040c04004401c03404d200c0d00480007802c0c00b4401c104100105502d0b0030280140b601c01c01220002d00708452030156a030410303142030001c20b001101c0a5800d409112160798140020003001c0d4100e0760024011421502c4641c0c2e042910342c080f018074480c40307600b0800b550040e1000c5c01200301c00341c021f106007600c40c552018107101a04210303e0100d4640e40c20459803685581d0244040d4000402a00c941c3d2140903d10040c1e280070000401180b055000b01c880b202038643c400e40c502c9801c051442503940c455990200c0741e6a5100c580286112450300f0310284c5200e5229038000360702c486c003e104451050070446041012a48a1101a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 153032697 1250 153031447 153031457
    0x101e03030338030f01051012080d060e04060e03032e0806091b1203071e0212010902010207140a092c0616110604060b150d0203010e06010801080a0f0302100c 69
    0x580b420f2030b091007403002c0b00803600001e00c8145462901036040040341d0041c3c80010b401400000103000829003035030807a60404a08200c415250245680f1081c801c03182100e60500313005a10084900c00700941c0e01036502c14400018403245103540c10401122012144480400304200040c140340803c441402810300e1030141000340c102c0000b2244114011107594000e82d00780a00a0143c01e001040f9a0300c160002120100301809088035132540b034510001a41c80b0060440341001c1c450103520000301981b0036001c841040d96555140c0900080c06208168050466001080f0503c501d400c40356000d004c0c02c00c80194400301c0001c2c0c540307404590100300a42d030300c16402c100446c0c80b000d07103140d28503c083c201400341900d198a010b9481a005000503c269160311002d05591508200d00042442c124003603912207114001d00b0000790024030072a02c2485c8030780e01045055020b0a0f400d130580d6150382c0074004101c15600c500c0f82900e03669100b00c046200e4246049180307642c612590b243c581300d907926 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 153033947 1250 153032697 153032801
    0x30a0507050c010305090a12030b040f1508160302041d061014010509090712060510030c0912050a030518060307080402090703050108030a1d0303030c03101e030303 72
    0x502d08055542e18605152a0a050060ba80c2c1c0004001081079407050000303051404400b4200c0140001180207074015041c22000700390f1848581200407080c00408902a00d2a034840903680da440600d1b2096417000a641000d0000d810103030813100d902172640c0d401070700c03294040b032055141c00702c120342070038005503030002c2403291040c03180001250103006d00e8600c1c200340403500010101d0a020f44048140001001d44008212440d04443d00401e40108013034140000c20b0009406480070720b00200024040740f001007040301c0c1d0303140c20014041c2c0010040c41034451b55601990123500c503901e00e02d89242c1106962444d1f51713589005520400190341d400e0380c5030403e407050282c004400b4220f9000c0c51300304001840089400400d0761181c42c0c6501e0186113503506150b45c1d00705808844051a018000002000175500d2408015030050b0208580011665a11074000100a00d20014560b200c003090031704001280c882c0d04845030340c0c0c220f05801107142e680003c80c403c03501c1a200480c4015240019 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 153035197 1250 153033947 153033953
    0x60903071d0c0408060606070614010b030901271e060f0b1203030702150721020a02070f03150507050909160e031b13150f0302100c1e1103030a0507 65
    0x61604040b640e051075080c60300b0411910740300c0c0c8008003054010100400e50500740821504010344000842100c004556100c40c21084d2a60048540003829800c000c507403510703420184406150a2040308060010049075541d0701c0511481000155070555031040700385c0440c00c03521400148001d00900003610004810234800c0eaa4030070041660541c00c24420408050780208000903020140306c50700003107a84500090310000500d40c1d050500340c62110300025104100d50041001c10740d07940032507043e155540303841000d00805000c000d003001d4906070510f00601c016046690029002d0600b0790400c1d24140c01b1a644100844803121042d4640c41e100311656040301e558409030348250003402d20f22014003443c2500c0a4411003280c010303418003001d054021550f40c0f0000a8406115016a4003542d03010300c00c4075170400e07002c164030503a12002a030034410702a040c00c0c0c8020b030340140685c1158540b5070700b07549030b1628968251020200000303c60f1043d0740610042c100d5032200d840d800d8071807610741 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 153036447 1250 153035197 153035249
    0x2060703053609060108061002190b040219050109181811040b01141e0c0601080703031407030e090a0b0a08010f0516020604080f0c0105070e010206070f08011406090307 74
    0x2d4180c0c0960f04a6040c4030150b41c0c00031460358001c8003515468034552050384201d107083e1401e1003d18106584040d00c404200b611584075014a000304d4202250941c010b044e032002c48031610599000c00e0681d201000217841c3d1501140411400340ba000490000c4003003c0b0040510b001c00807145100790a0006419180a1203048500c02003844d0031031403002c0c00701c071180f01032040320f10400e809044214030402c1e90072000300301c851407081c00003614160f5a4500403030b580c400b050301081380407441419080c0648440c00d8140c401c0282c06039100c4241d050340005006100c8000780c03011101c04d884101d0428207840340d0342910020040c1500006103138014065a030100c820107050201100203080924802c944d0010b1502d404c00d801041b22540c62000312100d100602c0744940341e0b01c2950a14081000c5250003107441605480b003038003610407c1e5600c0701c04840c0c0c1c000640b03000004c22941030051000d42e01c0400111008100644050303d0b1034440000645440b91980c80384017940341c8030311907060900c4a9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 153037697 1250 153036447 153036547
    0x103080415030e0705011220030106080a090f0f030c05010c091e03020906060307120f02040501080705130e0c0705030301080601080705030a120e0409080307030f050714070206070305 80
    0x42d150821440c502414040d441321000e1060504101c429580c4402c480226800000c1c220031001c0307042d01c10b81543c0308240f078a410034800d000110f001b400004011503480d01841404540c020aa0b81c4c00c070b8159558a02000c400100c190100707d41c0c04900000907c3c00d01c106088925203441d0030700c1c01460820352107000094443c600007103102d12281040140c075a2000d05402c44403c4900b40d07140d42e40d017807040704d211075219900c4c400e0070705051154078010090780c010416501d0a81c2c0350f1403150384064080d40c043c0700702c80f0b01404501d03d4690800112034101261508000b08035992440c0039540c0e00c1d440d01e1504203800614640e080130004010361141080458000c00c026009801034810030386800b12200e2540810000b848040c0d10721049558441d4014243d00d40e010740344680384e003840740c0d0090003030080e158000b090078034107808180c00c5406810780071800510710f22000d250600c20341c20b1244a421000040307003802401d101480308481c511800a41d1400a40c49944610342d1002c80c0010000701 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 153038947 1250 153037697 153037739
    0x60a0b100f02030d0b06090307060302030610090b09010305060f12330106050306130e0105070806040501140f0409020d05030a0212030c04120515100f0506030601050a230301030804 79
    0x34000982800d07008002c0c0c5002400e039010005e444058400402c0c072603c60300d40b44592501030381002250f160340550145008090685802d820103040640585040700039016100c182d00c410f016292882d0b110380c11055010002901d680241381d001700109180c00740031380308000b481d0000d075807200790b281c40d4011190103e500c801c202c2c074108640c5400480f804070180036103030406c0400030014101da2620042205c2150030300004200d560300d0381000c0d5000302815a0464009083c000104544d45030038040c0e54103031500700e080300745404030fa941004a044a007950580c0c21a4580911a015a4450882c5510315006401465540080190083c204403c11201d00000d02d014028490018194802d40d816101401c0720310403048a1800c061740351104903802d04c00003800c002e0800440c5003c110f40c04044585d05014440000c0e150b10400001e40021078110740091400d00c08420b841c0c0c40360f00720300320304c000c07544804108049000f04040c8070340c004d8000f07440d0000005000c02848503c12060884145 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 153040197 1250 153038947 153038957
    0x204030302012a0804050c0d0c091a0a05040b010c05060408030f090604030c02090c0d1a010306051c0602090604120b16030b0a090213090213170d08160908060a0b10 72
    0x84603c02200105a46901071020001c201000030b00f04042005990b03c0114001d2540c1805541c42c43c0c0032150809a02800010b01d0400381420016110703500052000d010052000000a0800c01840020b00b031808035213040144083d0108c003c02c0040c800507000f10300984006540e403805079540405894080d11080080e80590104804070354401c40d26850390f60f0450701a011511a44108400303802240210f260551812450340c103110500208015841c00c2a2401c0c08a0356540f02000000900001d40850700290192070800107043c80d402040d652500038012400c25803915800312840000c0c010483c2c47d003482e4400c0c000510307040440340c1b034020703e02d140a202503500100800d0708080308e403080420440e000304401c50f4896505d000540034005041d011922640107807504000c0b900648030344200580c0d82440c4442d05c440101d441c0707821910a869613404c0341c4603581c003d0825003d40f00c0000400a80b010702240140d0180601d600030450380c4008107040c000d203001c00c00c4040030104050140a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 153041447 1250 153040197 153040241
    0x70b011d0906060409111306050a05010309030e0d0201180f03060b06030717040507051918020c0a12050405060304031205090f12090409020a061205070216051c15020403030201 77
    0x301d0006500e030340894241c03000f0035440c41c9454040d00c0c4410400d44260702509280d4882c500c0182e507807003001150300865001501540d51001902180c29001d001b40016490100b1030246003003a14480060500c10300d4444408510001c8203041300000c2e030481010785d41240d900b0424420071b130064414540e000c80d03000d8a1409d1040000e0503881c0513440d01d0102120341d40c0000d041c808240300c05402403002404074041150203104041c8d445180d03000b92300c080310b012003400141010520a4908103404500101a116810b440e050300700b0b0340c90070812040201c100404200c5441700c002542c0a00d2007a00d8025002d104256000140c82e030003052000241c2c09110122407040001400440c1601c0c8103004980c0c031409030f0042005410441c0c0041d4000e0895180001d003103601c100302000c5105280b008100984884000300c0c0c5690b20754250003502060301d802841146032100b490105003442c5642c1c0c20042502d562602c070945a0401f403086040c0d40414100181174080c051424032a084520003032800c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 153042697 1250 153041447 153041461
    0xc030c0e0702030a05040501080714030a06080f0109020a050613030507060e10031a190e04050313080c090c0c1009060c0f03110304110d060905030901030e0c10030507020102040b070b011d 82
    0x1031b0207030388180c5040000740d002085140740200c204241c003400c0b829095a030383c0382a00c2614044d2070a480340c583c041c840c40e09103691011040c418442c05036401058218900d1811042146642101e4140039080c620442c2c0040041c00410810005000c0c2da100d40c43c141300f400081000c80d10000380e00200345404d00c0c02110f0030030a0114001079a41c011580602104480a08032030f5035a9540c10050356101803109100034000004003500710601e05c25030f5150100c0e2240d4003280c8462240c3d600f2034211410740c01141c01801504094040044ca100858a40c0759510394030406442c0030703080640342c2030303a500340e48510f183d8400103004041ea214202031181030b00d0b0020034a85884028406007201420b1400c0401a6071006013103480c0c40d4029005021641503400d1094403544041c14480c0480c0c688a41d601c0304840c0818034141c00d40009201440c03088080b8410750207018018260000c5540c20480841c065000c0405002030a0158003001031075814000742041c0c0c40c1e40d104106151904481c100119 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 153043947 1250 153042697 153042707
    0x108060d03141b01060e040219180f020c1c020106080c01020606040f0e060106110106050901061706031c0203040f0b0309030d0207020a050d050c03011103060102030d05130c030c0e0702030a 83
    0x405103004440c10307070302e201c56410402564030724500c1d01c11079405c0c9400041c44a100744101c600075802107800c41d00c0f071501010f100e454940c04c1d1140c41106451001c4e90b0160410580c0b180520300c4050002514148060098070700b0003521024030100340900e07101c40710721a542445800c1c0580741c103200074101c4001c80e0300040e64803503006101c80d11036510b400341344100702450380080b03140e840c00204840702541c540d807000d0000a0b50380368410b910341c608180010702d4a07205082d03074103e5541e0f807200c00040e1864000c000300e0320001003246415101e0b56201258141509400798002c0c00c45c0d40c041c40c1c4803810071620381c05820041d40164641c032414000e0040700440441210319000e070312800180e03103d07100c2c0b022480380c610030b602641e401042d4070b030494184180070844400341da074110001c004001d09074400701d05600054803228010f9006228002401c030041c1c0c0403070f40107042088075503201c1110765035589400d0b425420454140040550070442000107072035264010300103001035800c002c40c00300e0080c5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 153045197 1250 153043947 153043967
    0x207061406011b0f0b010e01090e060c030f040203070302060c0a0b090a02010917070902160b1303090510020f0105040f12020f030a0305060105090301060906050310021201030602032806050108060d03 87
    0x5031907a05000300c4400c1010040d01c50103111740c40844c080056035289008074584030300344500e094150404c5c000e01c0e14404082030a6100c0c9203140f815500759203c482c0e800b83c07000b00091040381c02d032203103080c040003503690000900800000c02c001450510070a1038989032045000c0c0145601e0742c007416407800143c5e003049070303c019220080100166124100010b070f1a00c11035620801c40c0782e20000f10104c0311000e80000c0740919001d8504401c40352100030211031f00103070b0000c0c003500184850703806111600e00200ea05914170150300c1103d8000351406195400c40b0801c0d50120760f12090002020100110002c400040d02214000791a044580401c05c40e164860b404e030781d80405545500041c8207070301580543e019804d0140080000740d44079241003000345a1030044900c00d206681903080c00301e0290007104d0f000c04200c01822003a901e5907560001940002d03140c484158064410550684c11031601812085c0c00743c01d0104506262070001340130000d000d082e2a0040d500c10010300701294008000320 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 153046447 1250 153045197 153045227
    0x206040905041a0903070b070f2003072f0312030a0b04090b190f0204030c050d050a0803091f1a0904111305100b0c0a12050904060603020706140601 65
    0xc2050b68461400e4444107503a0040600d204240c0e03020300035520000000fa040e0203102d14254001a19000002e82d07a0032590201000042e1460541c3c017030708020000005039004e1140d007224140300c03250f80d416804a0600aa14203030340b0800712003800c0d10002000b01041751801b41d01400403880703500b0240f00300d0f02c4001c1c0217984031615041280c0c0551141c1e4004030156800c601404000c0c201140c045803076026500e8009146800c107a1280303100382484c400c4030102c2c0c0d4818420450b1526000510414008011099070240503c0078140045040c1100a51041c0c680360f0103002c00ca1240d91340c01e11032034a00b51102050910f0142c2c80152410f802c0c28500e080740c803c54041d03403103503151300c3c4c4116404204104143c10204000380100c40300180d0700100e004440d032002441103282c80303a00817400360081c41549401640108031200200c0d80d0b041d044c2904c0f01ca146803092038400c00b400850251000f44d4801c100080c1e0010b0f1a20a001203445002140d11035400780500d82c0c10b10b40f0000b4801c8a095040f1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 153047697 1250 153046447 153046451
    0x51b100c090e0f150d0b0604060602010c020a020108040c150504090f090f0f14430b0c01020d0c0f1704150b0d0c090e06100b03010b03150927010902060409 68
    0x202d1004440420b0b00d04291200810541518005e45031244203880213070703003a40c0120f05103800800c2c803500600070101c070120306030b0041c0300081d0b0f5a0011035030035a028201b62600400c0310070100303142e100010040d21500701c03030300d580390b90b1890f00603039200700c4a840040d01d200f14940700c0c041000810543c00c4a0f021504551020090304807400c240ca405d0000c0e145004080c41480f0b0702503040002c030010419044030455962106841d1011528002c2070440301100400754103003028004941104050070744950f01000043c10400302581c060101e4100d921007402141c08480500070792a81f040d030340e0503400b199441c040c00600382680c0364030003a11000d01c800d82035507c984076019241c407807003102c50304030741c018000d610321642c0d0320310080c024a00c08a9245007801082c3c0054120007070700c5541c40c01c495410404a103140c1c6008025820b680000d090300300b13003810400c00d80c910359071210001070281c0ca40c200e060701280b50011801c11020280240c40c5402d906110300340000daa80d00c82500c0444204e0180 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 153048947 1250 153047697 153047701
    0x7110105102606180106060207030503090909070b13090b0402070f02060315130c0e01050a0c0201140904020c100e07080703020d0303060503120306040c03020405100c03051b100c090e0f 81
    0x2d0002541c44400018005204180800058040443e00401190310b03c8008005094030b1301c0d0300f01d844d88203e0101400c0d0340d004208101041c00c05684540c0d02c079019100b40c500d61078492140014070790144021041e501c1c6501800d0041580038403901d0450181101c00b10701e0131820347e403000303c41501210040d100310404070004540002030f2090701140c031001095516000302d010310100007003403440190000a10b06045442d00e82d40102c0c1182d05034020b40d10740781400030b090360044818181001041a200c10305110700201ca44481c0003409402c05001b01038181040c201d04490110b503c140c10041703155021107010001c2e60404240401901e4040d1580300c80c03200c2d6818180c020703040f2544a81e425109000b000b8000a030007101442c000c1208031800c1c07140d8042c0c0e0300200d00741c0c00385000d81540495038040c6155510f02920700e20302d05500ca1b09155040002042d4100e60360304030481800c41030b400c11203010352103c448d4400e042d1600310700d042c200d844c00e040007042c1215400041840c1c1c1c20b400340d000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 153050197 1250 153048947 153048989
    0x31802120c030a03020106150203070b01030602070503070b070309110102030a050703030e030f12011419050907030905190b0105060408030a0f03061a0a030e0105010b0f0a0c0b0903030711010510 85
    0x1c07188003080501103076940c01c1e00e071074000d000340903074428040c5005069010320842840403007141e01454101100032660f908603100e0310000d500c218001c071a28030081001400250142c4540781c403c0340301e41c400103660340b02420620002440311303414034110f420070804031002603044bc00f90348596405107400941c089980c140b00346981b0074510340c24001d000200c1c414040b036443c540c265060700e4802c0c85041c8900000003d10900020b031041c0075880d03022506050100f030418280d42540410304d4500443d00301c24030389906041941d210054031b0300c04440e006210902512003202401400b00b074454501c1c06140c940030981f24040c001c3e804040140d03030144548124869084480a0281d6001c00c0c14091074450f040801580030b00d50f0000400d062007170540d54000181314103812a5510740301240b8103021149101102d0348094090010310180c1201d140110b00c00a10070380c4540c0c4141c004503940e04007040082c01c00301004010804981c18070040100510700c20341c0100407140300e03171850040c40b81161 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 153051447 1250 153050197 153050203
    0x1b0a030f08040609090204150305150a1e050607050303070e240a09060c020f0103150e161404031e170d0b04290906040204031a040204060603180212 65
    0x9800503011400900444050000c1c0d034000300115903290300c8412180da135444008046e4080c600c91b1032440403401e050b1a05d1140a40c102d644c0c00100441c80300170040c5000e00091001c00c05800c82e1000300310f0b15070300182400c404031704440904401c56445062059903550340e6601d1000400c0c1c0c0082004a18410100340c8a61040c424858401040441c100c2c1210310540315640216102e0350001d0f002000004c1c0d038a028031410704615401800c01841c44090100540140070303010202c010f10924030b000044c00352210303d01e003030044191114400189440c2940107040c00b00e40e48800000d40001c00040000425000688054144011103d0420000c81c02d03c810190010780850962010028090242c40756507405083c84010449040058215508210310203450084c4404d0204c04c40004464251034020f00441c0d0140d0004c2000d0702e441e1700ca0b07075032244581c1c031410803003038501c901401d10003180313024000c05c005400306180400c6903c1c3e103d042030900343d20015000c7d0281012590315641000b040c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 153052697 1250 153051447 153051449
    0x403110d021e01080c07031d06090406080609011a240f120717070f181703071a190c020f01060602030406030516020c1201021903050f0a05091b0a 64
    0x341a980340a00e0380c020311240346810802e00d400601001c0001d076030400c0c204242e03001315030503584e10304601d1006400105c800000d050712641c001c40c1840003101c1a5568051388021b8000703500606154100020030b1030a403261049030210800c030885555005071903a4650141c4400c400e28010780384c4480541110b218840c540c4070b202c0a1300d0002d1151400840d900019014003900d603204a488902944031000481069524500080c00c803103003403080a103d0700d030301440000e150a040d0420381d5903541c1007409001c0b04484090395040800e01005020240421140c03a9400c0d0f03801341000e15064008900e40802080d10000107541d8580c04102c10744200a8158441d0112008115580c1c59410103950717034000d84100d0340003904100005444c0c502803103000d031501c01c4980080542440000c20032002c0c1e444051105120b40d401e01c0101918503843e40030752070020305c0d9100003a40b0300f0148000111302400074001e030070143c2488240304035000006400e9000c0308040b41e40082e840b08100c000b80c83e01c481 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 153053947 1250 153052697 153052699
    0x507110604090c0e030d0503070c11040e01050105010809010207020604050603150a06030e010e01060e0c0307020f1b010f02060f04080c0c04050f0610080403020a0206031e0405010b120a02060403110d02 88
    0x1080102e031410140d0b00c010811201601c40031100c48600041644c0c1ea00c07501c40441c00500c042c008100c1d01805000c012050341d00c540a42d850003a8003e02080441c0c651440500b02c90b0f4403003004000b0f03035800000140d048480b48001707516100c280c0d0081241803040707106403800360500000090355450800c8603041b0030800200943c0405688000c01806090903030b45129140d464548040740f065814460023040381d0b04031030014640e90360601c0340805500010948c43c05d5018000580074405800c1c44101160305808808801d415541d000041070707407408200d044159804a000d009a83c00c076002d0312513219034480c40c080ea451480301011030920005210b450b421a041005100341e00300030751400c070320a44050b220481906580c19007150b9540d01514080d01507001407a4000c05400c15000030342e4041c4503609040404d5074200c43c4034551000032141a50300e80d5449400c0c1d046490490000340d09441f10b500200762140164002038000d10070303440000c0412140c2556402c039501e034061441a00d5030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 153055197 1250 153053947 153053959
    0x170406020337030b040b061204080a181502070b030705120703021c060321050d0504050115030b100602070501021e0106050405010b0c0d0912080c0a020a1d06030304120201050711 78
    0xb031000300900600862803074903204504041000032681010030648008103810913008455441d140c031840c9650f84010003000420008080010b800c90b0070000507001070281c0403039800700c035840a030001d04086440d0010410104100184408940e008055030b41301082d40315440410f0300e408205500903c500ca1013162645000500c00c001902d1f642d100038110327030050a1801e44c04d2081c1c4082c0400240e64044140030600610811103403020583c86a40d00500c076000000354004810240c203400841c0f070b44101c5603482e20804000721007400920342030041c541400100001404c0c640042d40354460801301d50b5108140212035001c0ca00250000f40003400003800c200015615042040c402e6488403010110754412000390603403541c810480602203580c4101c1c03480b40d910041da42d07105254408400020b040c480c900100000d44d0702d0100072002058080074a045111848a8030304540c00c0042026100303800034041001050700c21405201295424688980d4402e5240f40c0185920000900690890 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 153056447 1250 153055197 153055297
    0x9100306060b0c01051003080a080406060b0d1a010f3c020c1f0503060d05101a0406050301051e04050f0a230d0c020f040605090c071704060203 63
    0x10b040403008001c100f40d0200240050381d19042c0700c0b513008059100040c18540304000218559100d58140c540003442108041845030f600d51460000e6007098641d420f8113503550440400d401003402c080f01d0022401e0800f001400c02102014010481c0c8151021a280071300800c1c80c5000e021039502100140503507007482d01c42d42500002560368856a00c00d90003108983d00440421f01e02d00c01803080f003075003540c4603440d40e6034110500c00951000c100407130701841900300001c004565070050003003182801c0c4c2008141e410040400040c4c503c198010741c000c0c0d2401045c80f206d581a0302c01040c6080808071001540d4403546404c0b4504220202c074030200740901440c920401c50358140c0102c41150701c0c1000552404d9042c2102c0d222503080c8030410109824402034801410701035480091488010800918070b03943d01c0210f0070800080f1841b8203010070000f900340401000007200c800c280c1c044001d440c00c0500b040d0380030f035480c841e00d02480315601a0800c40d481100b506404055095094113142d8019 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 153057553 1106 153056447 153056459
    0x20a090302220b04110304060504020102070e090a06050a0515040b04060506070308102108030912040e040506070201050c0913020904090c0e060d02060301050910030606 74
    0x200051410010169071100300120003010200382d4001140d80444042040b68003044006200c1d91600c6005040704007818181c1c0e51050340000005140d881c1e500060f841c0010990180c070600304100c0401203c6800400c00b600c01600c00c00c01070226407601c410600c1a5042140d0410701c0703510701c61002c0490314003900b1449860001401c00180c154079a40415081e6101107029008600e824082c00042c02040741000000c005481c40349004450041c4049400d0942c40fa000d0000180840840c010f40400d100c010421412141116651541c504402381411402c070b130180d42500903600050496401070054a11408078404800c0c54500d159081003c40c4030b01c01102c0030b00d5a400e001151141d16507104480425016815405850345428212584813100600150181140707040c640700585410b0192815110225281c80f032594603041040c81f8101c0d0f40e0f1001d02414100300c1f0000e9a = true := by decide +kernel

theorem cover : BRFrame.Cov 152877697 153057553 := by
  have h0 := BRFrame.cov_init 152877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 152877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 152877697 ≤ n) (h2 : n < 153057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
