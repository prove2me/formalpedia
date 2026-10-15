-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4130
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:39:31.585779+00:00
-- url     : https://prove2.me/submissions/13ed8c12-5ddc-491e-96e5-a74eb8636617

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 742625899 ≤ n < 742805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 742627149 1250 742625899 742625921
    0xd060212010f1a04090f020f0c0601183b15040c06180308090409141f0501080703060e1011190302091f09170f1b010206180705030a060506090a 63
    0x40a00040201c4141a0408129030240080250900b018a41005a035801c41c1380c80c110b26411001c013310200000c0842e407403580b40c0c0040709004601800d88601e4007443c441001c1000d1440d40c4c140c1c45402c3c00e0140034081d103140300c43d0480e40c4400301550044c1500070203583c1100d07494646640068101e2240140130400c1b4244020b402a0134034650701c1285039032001380ca050300152111580408030b00034400a21600074400042c10b40c4250f0026202240e6107000e007c0320906180400501c60480005842e05c04d603035100c100024810510071605140165a004000c0c00300c2c10481a00c0c030388103603440a40121380450007031966a84000c1c0007603060f0702440c900b45810400640000c000f20140ea411507810001a05001440726110401001e101c1003444024686502c9100c0c500c200700300802611228041d452403004802c07880300300003903d410010780494560200b80401e000d03840740070700c44100101002412140c28844d240341440103400111084c1341b0460030f1000254545240d40901d441e044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 742628399 1250 742627149 742627199
    0xc0b0a0921080c07050c040507050403060f0c0e010e0d0605010303020307290a090f050d0e031020071a0906071b022d0901140a0b0708090d020d060212010f 68
    0x5503c5440ca0001a00710305802c0d929449009284150b80e100c1d0721800f03010303900c00c2c0d580b04c0d40c0364210b05049040e10740a1072280b03929450080b12560403580038083c0350141000746414603000c02e003507000135041c00844101030400c911b05400001010740010040c00007a108014032811250b41a1904032901601c0c0030b100020030001001950302506a480030021901c129158442d8100c0c5444003454034041d41591404030301c680e05101258501080801e030715071040c1c0c10512a0f01c1407074170381005442c100020512074030400700301030081140039910110300c102880210740c0700e468220b280035507030813054031140c0105041600c411191000c3ea09804502a0060100d4100c0000c81c410024650001441c8600c00365080340c40c51115a01c007140e05000301202e041a440444641082000b070404a61100003a40c10400001d000555400d05441d00f0440449000d0100e610ba400072030751445003204020304a070310000d00a401900061040c5068501220304181740c1500c403000c1580e50081007040400b00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 742629649 1250 742628399 742628401
    0x1050c0c0a030e0a0b0a0309021201020c07090b030c030a0602090922030c060605040e070801230a020306031e0313050a0b180d020301060815071d0607030c0b0a092108 73
    0x20a00841c030315900c2d08000303007258801c13990f54107040307000360040e158044c0003075113400911080d441c140b0807401400114400031860011802c40e8666143d44900c1160b0460391a0b108040355903030148050408801d0140640d18040c900d860036330020b501440310745101f16446008201c0c2c17104016100d091440d849143c4109513109510309440c8903541c5c140444026450742c40100e01e0b9180c50250000c5510840020300c50705003004051030960f59084500d991182c1846410100088039644240e042250300c0c000581c1c03504c1e1440800d040c804141001460110004041441c0000000040801100c0101c440b650035484500f00309a1600b9841203030714070307003050080391a00c1d03400d2180c5401c0d2203001400020600c81940c08a0300f5603491303502c181001c1e0040c151500030310400e09482030f4040c80524150402408942c3e501c820000312107101c80c00f5074800b00c0d01908250281511401550700984407982c44e140c0055464041d00242c90704444060603103102c40300f68100b00300c1a001102c1207442d808a1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 742630899 1250 742629649 742629653
    0xa0b0c03071b0620072907050708040302061c0b01091503150302030a06150e0108030d240b041706090c091003290c1602060f0d060b040801050c0c0a 65
    0x141000c402e6080e2441c1d070341c61002c408184400c42001d0924004032054079210281401e18140d0f0048010b03880805086c401c4070703d106000084a01075110015040c10341e120005828403500c00d00a540000b9045680028090304c030003500c80d1303084a00041801c043c8010f0541e070004450305106071059030100d4500480b40c150240c000e400c40d103900d0321002410030310300b50780350002440e0002c03510050382c1c4c1580c1d501d00000d0343c2c8a00b85009001e080c1e05020741e0810351405071903541d240b042c4181c00500c01d540b1542d00744586660369405c0c00da18041000040c1d01074560040250582c018882e64820764154840d0f400001e001080c2c0070712900d5010003908100c01d2100a0110642c801003008417a051104d20100008150403115001e0340e000181c1844240d003e404603d5141e00080d0421010f04018015001401114800e100c105036054940645a0f128101c2c1d460150240118900d9510305041012603451261005001200e101030000d00140d120703900607004901c111b46503044a5000300ca40000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 742632149 1250 742630899 742630937
    0x60105010311071a040b10060903061109090702010605030c030a21030e100504110a03051f06090606080901061d0c030403020312040b10080d021b0406170a0b0c0307 72
    0x2010041505540c0b9007501551464a0796103c84c6003243c1c8140c01d07100340003d110240d4129644110040007000c4030900b03001d40070705610520312006100d103440300d0841d20341d069190160b4174031942c0031f0a2441d6500f040c0c200039000c0e101c40d0003400d019110b80307400101e642c500015207603141d41d001682e6501c91803a20505e440704188a11503c01031644561035545c06038001c101c0b02d9840a0710030341c0081d00d820589080382565090240e04c0d4414900c0c3c603403d002007038000c150070072120f08001c3c0f680003a4008030000409889640d00c000011b500d000c400280b096081041c0c1c902c02c0d00720b00d008100664490385080b458503202080c00c4241c0d1030110006442c40013100055401c00d00900451b428091100b03030103003000c0c0040ba0121140400c0200348100c2ca400c1401c0c0c0c40c098035000307025041c0144410002543d980c0c0090420384440382e0704818140d02d4a40d644074001501594040d8022840c200c03e2581d038a4250304411222035418034001140080d010b0103581c0903203190360715400d0700311182e0440702c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 742633399 1250 742632149 742632161
    0x30f01150513020f03040c090606020102091008070306030b01151106070c0f05210a081501120914011103071d01230919080f0303100b0f1e040311010f020601050103 72
    0x11803001e41c02c1200051140099000d148101e01c18a8074180300c0d030500b008e0b00e00b5501075500000035a0300500400c6441e507202031001e50801010300d000e280d03a0381c0c0c000048003c0d101c103a0010f0400c01c80703030300045404000009600420038403610b03203000c4141031240080d96843e088400c03000090304801000d0014440383d102003501070090b0122030740482c014011075504103a0444c1807001600001d40503d43c25006102c2a501401c00064086000354001c00a4402010070440d00201907940c0c5140040005c0c0b02d02e2038044a64501c000c101c00b039a0305006c00080d03802607038060082059900d9500940303901c1240021120010307034504600c6a94040c616259542e01000e44440c5202444001c8443c1c1b9000401d400c072307022030020255040e00d402c161501305640301d003142149402c00c00400202c0522040a00211068180483d0ba20004400780314518001c1000c203001e407a64032a41041c101451101030026a4020040106410300c0000195500a250024180543c110800401241d80070f54095 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 742634649 1250 742633399 742633429
    0xf1d07080f060601320a1103090a0e180609060a1d030409020a09150f120e060f0403020c0d060b010e01031a0d080c1002041e0303080a181e02030f011505 67
    0x60003050b40307204c1d4172880c5440d406106000c2040c0200c1c0040425a0294201c0ca07886c05900c0594500a004404a030b00700f40356000c0c0b1895810100041441d9100030201c500700314468400b503840f54104102115100d05090b01c180300f599061036942180000f100e0450106c407450400150301d010300c1c202807040a0340014070040140302011000152a510502c0406c0f0b44442e05e540d4004078841805000d07010080f05d126104180b03241103940c03611540700041082d00071455518603045a80c8600d403c03490500026a011741041c00394006008004040e00010001d1100740c981c440c2902c0030f40011421100420181d01880f4114403110356182004440c10072028056004503281c07260000364030389070842040c006111180d002038100400c02c00c0c0d2282451080c1c0c110305100d842c5146850007816104060410a43c06a0707580354407901ea120300100d04146039000d80084c00c528402c83c0c80d0780701700800002c140d000b402205031403014142d040c8160004040342015000c1818140340611502811250070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 742635899 1250 742634649 742634687
    0x507140721230f070621090804051c0506162c040e030903160e0103033e150709150215090c1309080304150f1d07080f060601 55
    0x340b82d96100c4000b596260700d8140720010030000d001100140d20b048000d51025007007000c5850f004100b149800c2c03824410f0801d090700403540b6042420070080e00c0c825a03104551103814034501d5040400344a12409160b8020003d0b95a40c0d80d88160070140205502d002100141a1000b469083c030f11044111001c6000c0341c55080740c2c0030801011508895442080e0046580042990708180c9410031042e11546951060030100e545048aa42c0400c1c0041c0402010b1040c1c03907076581030550401d07a210f0b080c00040800315500da4600301d15480026440300566195000780d107401c107030703000690450310700441069807030008040c5060100c2c140034048040c44400c6004440c3d0040c0c0240c03203042014001d02984014002d4013005030704200180c159149403c103a1820001154045080e80d81034035801500019035011b081402486a0003c00010410091540ca84600b03100c14103807102001040c0801e041c00c55258946800c0c00c1c0d039482035138540d40b0003503078040c0300080d110394410304044d20380d0076407080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 742637149 1250 742635899 742635923
    0x50f0309090a09061404061b09050904080a230403030e0f0a0e060d1406070f1403060f010306080303040c14030304080c0d210c03021501050d11060d020a0507140721 72
    0x4900c1c005d182d400d03141501c07007a0b141c40b9406c1c074450481031703010404402410034078070143c50900414409800100080c0803c5c1d404684c000305140604519103212402c3d000784490601e112041c801d003500940000d80002c0d41d404588046814910042c4800030802014100d406161404445000e0b80060490341c10138840c1d0224030014000625006071a4000c001520300c62811400083c03030241e8140c0c40310208020002c0706606ca0602030112900044291b4240503a180c0840050700a03008070341c0030104a1000004010074001c0703100400b815500101151030700740080c601010754a02982c0a451566003148148044914141440340520b41c800c000754a445100010300d0701110010508810100350b240035180308041e810300000300242e003115036103a483c2d4102804180c8400c42c00f03c00400702d460808111185544070b90940e4000040013200359560940c01f5402021a00a10421104030040703501c00e900d468404100001950100040d1840010003c0320010201d50344000964018a8001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 742638399 1250 742637149 742637171
    0x18330902070b1b0a05160c0e0108100b19050f040f020406110c030a11060a020a20040b0907081b07020a120209090f0705010c060204080d0903050f0309090a0906 70
    0x4006401c0080c0124080000b5143c00202c0740c808100000002020080c10002c5a50850304001034640e800741c1e00308681c86411662429407140c04158001c0c0d071058801d000009a201800110b012410170045414400061003c003802186e185010f0004150180d034541440a4204a0b2810200d00e01c01040800d41c82c5c02a0001c4003284d01c02d400c00e10004404c1d24425031100030401032044500d005600400030018141c4070322102c02040b06081d8482c031800a80041c4641c030800c403031b00e10103801160308034041c1820002c801c6007041034020307140600d082246002e0039180040400b0320861290b160b0a900f075440381e41c03030029034900700001200040c080c0400300258540401320b8014041103210044024414010403e8900c401069100d040c0d01a40007440e00182c082010000c84000703084c0000c3c05402454108041c0c000d43d0460f140c0d91198101cac49400c0c2d58001101000c4070300034401d0303d2108040c1102e25803248509010351360480081008551211682ea0203440c3c140e025040010f00c210441c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 742639649 1250 742638399 742638401
    0x9160203130603270b0c030c09041407110109050c060f07050109030302030a0b0306061318020d0b041412030624160c0f18020901110a080301183309 65
    0x5400ca0742c0082d942d8a803a100010102c82c1003100d1007029904800d0750180d81d1380d01c1010102c002c002003609100840070841092245003500c0c2d803620300400500510369000e152600c2d2110450340340c03001942c40c480036250580e0601c14415419041320180c121140b0400034414079a0000d241e4141c854010005080464028403551103070758403d0360b015a880c00c1280b500015079208903112071098001100f84a1990b036075941b01c2c801c001c103049001c41e02c410110000701d0f65003c04040030b904200c000703495904010344803c22034070440c0314070300c01da4918490b003603880e82c0c51112074004c007803046080000c07841c00d292052207002c6a8211209096402040511000a6420034005481c664081d84c0c814400c003c20740c0d82d40c101515441c401c0d501b80320700d060941d00d60780d01c00100401d203050340050011180d91142d112029007040301c0041702c41a21807450100c046a009102c0c04581c00d01d20f0b020b002400d841c03401a1034841d08040b06002c41c81500780c141a925140011030381c414411501d100103003401203 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 742640899 1250 742639649 742639687
    0x110910170109050a050610170711010c050d0e0a0b15031608011a040e0a08090d021f020106080a0b16030e06010f05180618220602041d0609160203 64
    0x41d0002c007250608014000f2016143c025000d10311480200d01010344155200ca4000501004445040e603030351128917003aa84003416540300b0b01154203142829459507007020007060b0001e000318040002d840700d040d605440c3d8042c547c004103140b48480114a0810401c514814804001400d41e10f450401d4002c1e0450400d5980c40302009075180d083e48014140c1015080071300100546092140010f5007000c1520749d9000d11005208020108403007032079403107041c840d07081107a0180845040703103e008a1006070020078603034040158240140440c0540001c20031280d00d65101c802c151079a19407640d01c034411980c1c12916001c0540d07450104141c072204010307588c020000703649000d105034185002e10401c14110065a10001920800d01031a501c4180c0c001100b15290702702131001c0d0f1140d81030344a644c2d00c0072800c2406182007442c46c07000d1012a034010821900d8606e00b90202c02541404100039500031121503510440500005052941c2503c030b407104400303144152498440c0b032100030b07010700311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 742642149 1250 742640899 742640909
    0x115110303040c080d080c0405040c23040e180606010503040510110c010c0908060c0f0c0304090605040e3903071203020d11030a0f0509061c06091109101701 69
    0x5a0b60810000000c00b03019940c8174269520785980345103460882c6460300c1c41240b25186c029651800112103085c070800b02900d8030300c01c000301c02035404240d220320700301038000b40522030b80c13a031124010514002d04221042c46030306050001d0300e01a6204801034a107900020010350b00e0b40113006040348910b40c0ba10072500c1d80c03140e04420f95207401c21158560308441c00e10301c60805121260605204540307000450a130b001f14404443e60381d81c4150a40c0e440716002c0c00c0d000065500c404900030400040c03a400100aa6400307813000c0003911030011800356984600d4049a80780440e555a4032582c0c403640141440e00010604038043c450700d01804240b420407a03030310520321002c0c40341d046401c0503818003122100901c0d61070b003400e00e600c0301014152203210b030f00681414491405410942c8a000d842070b11800c03100140041d80b10000c403c1c44001c82c03044d0740001c40500746040d60101b0412443e11403030551900304c002290400220b04d003400b4045480b03a40d00d50074801d40030080b005c298a0304002c1c0d4041d00c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 742643399 1250 742642149 742642163
    0xc26040c1e080c030a0c030f050f1b0f0406030f200a0305150a050108060c0a090e04050f01140c0d0e0106092c0c13020a03060305030a0302040305100e06011511030304 73
    0x3914090140e428400388100da54402e401c001c0c000c50121b0b418144020a594001c2101b0075032415610385285044420360f0100c0e180c1c0070f04100440d00a002c100310240c400c1068503264450140d03041000111161404001c2100c13011441c19400708143e1126101a2112200001c0c54100ca000c0004e9012030030b80e004942c260702144081c4005440306d11001c0d0080348002060202d54105a00952981c1c0010011208c54101003130743c0340301504c1441c0c8480100b101801296031420b15040c941d450700e000c032180700e00a40c2415140c0d6140303446019100c1c0320700200034100f41403189900c4c0707440c0500741034601018a5034803660007041c007441c5480784000d250845142c0c80c14030004410115010f851661041c05190400204080d281e141d000e00d41a4020060100580e9642039880c25001841d040e00043c1c45448003091034804c2c07036050390043c0141c0e4090340c1110700b840c690300c0401040d180c140d01d841584c0d4215100400c188140d1040c000228111401c04004c404070600140b403030b50f081110155000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 742644649 1250 742643399 742643459
    0x305100f1104050904122304080d0e09060d0c05190302090703020306030c0d230313090b0a0b07080714010c1101090f1709030102040b0a030c26040c 65
    0x440854850000601d00d101034541c00c1500d424005928580001c1000c1d0003059044004540c4500c00d0741070314500210421403400a6140c21880b440075042030049520300c0c0b08141030a10300e6801104019042c00c801000894142e460005015807105141c1c0116184c8600550220300341d5156111010f24884910604850500c1c500410169220240c4584107151040044c0b00e0181c501243c151071016003500e00a035400720340e03d010303080c04140007044d81e0b07000b240540c042d15119011008002000040024080298890b25044101c6103d076098070350240c42e059007000382183c80005049401e000340c01c1941010038540302e2000090440030b100c1c0343da0350f5070751142c207015400c1084041020f12a1008000c0d4045a80d82c0e40803803801a130000d00700c8034413890b07840200440c1100701c03078540c04d000d00207644035955580541c1e0f0f030f90022179180001c281899011700d042d500c1908101848c0700b1231103201051031030380c41c03000c00030700e2003d401a205100b40c850b0118419034406014140f0180c551604004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 742645899 1250 742644649 742644671
    0x30c02010911240d0b100813060216150e01060f0f031b0f090b040609090b060d060e0a0b090c031603170405040c050d0f110d050a0b03010e0706020705030109150e07030510 75
    0x6c10340071040c84809000445040c41101c1941180904e01c06900c500016030740d12000129500030710750418014001c990050000c00c07160b0303c68000c1d004684181d0028403d82d5242c0c10040d0100405d4012054810340c403110400100e60950595a6001c00c4003c00032852a100c0700615003981c1c1c1078021481060701d40c0132a0b105401d04c0c0c894070b401440400e0042100700d45c0703030707075009400301c0e01414803849003407007041d083c0901009a0000c0302c40c041040458412004030b00e0144140002112500414040c1d6070600c0418100454504030040382c0c000305015041c10b550340c20603e024030200302c50211703509100100380e0f41c0303e0780f00c1c19029003919101c0c03c0c0c0b18800031a4010075620756030036040c0c209040c00b01c001c0c06a54000c043e6000c0400d0b01c2404a03c0b03070b540700c0b40c00c801080c408031090f44c19801c03e22a52194400420000b056811a034240d80710a52a20700f031500740c0d01041402408c850156003506149806070b4080c000050028054403280c56507510f80b2485c1071a01d00400c00c20984c0d403202501 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 742647149 1250 742645899 742645909
    0x70f0f0b0f0f010b070222060f1a0301030f031209020303031905060a0b1b0a021804051e06130312090b01052103030c1e04080607030c02010911240d0b 66
    0x1a110b61940c041d030351258107089074010715004248009000d0f60b442c181e4045d28500d0340e10080311001d24900e0030404255a1814491144010320032251150021802400718a6801c0101d9041e6038001142040d02812507800712404800c101e0b03501001c950340c0310f0b10743c0180c2e0188011800303408803c4070349108083d191840421100090012846940d052104000d001c8041e0103560791500d2030f0303140c0035404440d90109410b204030b2202c02588407080c0c0a10124038140d00c11007a024500840489420000c0c02c4210f29102c074a01c0715076207050380104000746144181c2d60103107030703410320170b1030020800c4810b01d00d04416101074200859500c5019070040c061400e2115070b010f6000c4401d81c2044088151110305912480040c1451000b01d10000f581583c81409441c2030000041982200d03a0721640c810005450340c0c4c6c281c400c100024246810004072078814004e480000e608400c4040c40a03842c60304002c0a00009550849440c089110203041500614040c1c6018100040049000b122000401c1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 742648399 1250 742647149 742647151
    0x50304080901140c03182e0305090c090a020a0f05040b0717070516240819020c0f010f0605011403061002250e010602060712051b03090a020f09070c08070f0f0b0f 71
    0x101401f503408840c4540c8004050085c40703403a103d420000341d1500e5224040d400c117118400010b0304030100ca4188811a2003583c01030070f010782c040c0c1d960b003520b4541e00710441d07840c807031485681100c29081c0407407808560085500180c11407158a514a883c0890b620103007040010641c02148580600c010440429009840c107408144900c003080c822a01c03120180c03680c08050902c5000c400c0500c5940e0480d0308070f504840d07440340f0b0036013201d01003040c182802e4041d02142d1203090341c550428400040030750181c0d070b000180710688013901d41183d46041c140315503080000d040c041148203140c45c00380d50b807406c0f28510801002d1503040c0e1001c06e00380a00c00c0c0c00c2c100182c0c0f1007000c541c081800c00c00321552242c5554000005400003041c151a1843c00c21180300c6075080340f5109680c000b007030254851000a014900501c01e40d0039100e004216030402000341402c480c80c1340800d103160140070010b801c80c0c0041c80c085210b2003e80100d0b2403162101407138100002c3c801c6070410300403c01c0c0802c4403802c0c44c0c06 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 742649649 1250 742648399 742648429
    0x9081e090315060a03080f270109030303020d0f0e0109020901150206220209010e011e0308040605090a1d091209011d0402211006050304080901140c0318 67
    0x2245044010004641d403803500c001403101c089001d0001c20281d41d241c10b0b000e4021508852040d40b102405542005994000c0c50144802103902c041c44c03550f50401d07200100c3e0484161902801c0d107144d91000e2740650702580382520004d0741c48016101521407881101c0401c807812000041e403020343d2041c0b00c0e0b01d9006800c007034840806034090141c01e5900017065540018014401c001100c43c5814887c0c07001220b0b04002d500402480c00807490104008045040703c4002130140c400201594255401140303900002e03207803071010003050112a000e10300038400028041c10070315009540301c3e07a151035500b200b40000c074451800428805541c1c010440050613011b000140340c5040c0628002170500801c0c5a00d041d44090507219004945d95954166078030750300c0e00315008d0035440c0a66010302405000315410f400c85a442140851080d00ca80d069030710541d441800b0f240303048546001590003960101a00313010304403c01071000b400c60144050940700440e1461880040308036020000c8242d0314640e0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 742650899 1250 742649649 742649707
    0x11401021b090414070e0a0504030f08131407080a08030406060b1314040b0301020310050312040b040b0c0102160305210c1b070510200c0a1e05040908 66
    0x1444800d642e03855100703904641e001e44903584400038601e9842c144030056001000b03001810040112400403600601d12651181e40d911054421041d401e41d09a0300507101e6620001215024200041e0140b034004606a50a012100c4050f40e81ca06603280012142085445060210074001003008071b0103800060410a030075103043c006186030f001c6440181e40314001029140708c19400c16502c5a07444440880d00140007999a0b20341001040141040b51080034001e2285540e642e59003244081501c0036210008040e074641480c1c22850300d800e0b000058440f1055500300311159100d980464441c0c0303180d10944030681c54030807144072064202c04040190f0f450a07007120401040c807034440c049408810010a01c03805204643d40341e0391810003141c005941041c2c212407029902030300542c503c84000b8007442c0d140710751125903141680383c80c0c4030154640c02441001c82440f03155000c100001502410300f5414890564800024003610b203a503d0995648200042c100c0524074810b0003040c1c4072117000300b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 742652149 1250 742650899 742650943
    0x3120b010c020303120703020d110a230703080405071205060a0f0b090105011d0a06020318030109020319061e060305101104050d060605060301031a0108010b030a06020a0e0901140102 80
    0x2003502c900c0342000062008907145c002585660003079041e660000d44007081001040da2340700d174a030059800032000c0c0c00450201c00a000b250f00c68008040c0e0350700a410022410304c00280d506031440ca1005c0e0003160a400361035004100709000c17541014866000b040182103d01b4038142150403100d940c01000c0301e10f818124807990780d0310340d5924181110002e281801e1049004401c180b42c140c0d61000e0658030450042002a07415400400703802206203000c0b00340b074025450310070142240d1601e24000e4054021000c1004030050f1121a8900b41d40100d201180440c846000b00014404150382c4160320f0340d49003010b00c01c2c080100700030011f1803a040010072285e10032103c0c8600f0350146104183c445c8000d0203a000420119030845001401c014110030744950b12464001102c02092102e901c48466106c0006050241401a42c000000142c040d0020400503103450010b5480700014600344564051442c0c400e84a41c50414000d100c040788000c90002c62200090800c00301d20b190030b80d0590b5100c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 742653399 1250 742652149 742652153
    0xe09070303021f0b040e011a0415050906120601060c031b03020c0f010c0501090c05040b060a0f030c030212160906030b0a12020406050a06050304050c040c0203070f1403040303120b010c 81
    0xb074000f0451100d2a19011180f4a4004440500310b10280d190304141400c0d071800da14403054100c044040d44025440401034003101c20700003212109100060040e9000ba800c002d1400e19107540741d000390000d0100a0042d240c500500c0c40e10200381d0110002600318284803061580c07018111140390301c10541e40c5001202910025a94619140802d10420f146850303a0220381c000c203000c1000a5004000b072090800720700740a01000c403030740b10b154041c2c0d0604180c2c3c02ea40c036001044601c690b04546800040d40302440c001c80081c102c18491800345503080000b05c001c2d00c441e150f1f091080503e10000b40d0702184c1500000c0c03140d103540c1c3c010713002d0604280c200c00c607607a105540c5e10150744800044400303461490000a02503c8254002e6402c0f445000c008a40181d02000551255004104031541e061552083c00102c4001a07042c10068100f0701070840080c02c0090000041c0e4020300e600c0d4610b94582d0805800d5903c290b20480204411020611490445010300040c1032000d0070200c0d41c101e115 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 742654649 1250 742653399 742653403
    0x1d0d0f080903072a03060605030c040c08070f0c08032508100b091522120f0f230f0c0306010509010e04060204120c0837050f0d03060e0907030302 64
    0x40003000b0a01160000c25038080340948040281c40b03104c210703241d02c20650703a0610800501041c060503000c0c0c0514820300d22141411301a580c014800355507101c4142d5036018088880030440d444250401149c85072400c0403960030f00c0a540500800b60170020709a94451855200010182c013440510075510100000502c0f048078110465080070b4107159155045000112040c070740042810070010042000c50f80c0a6001125000c908515808900403645a1100503a603011094008120900c8450340d0800141e00007081c5110324865603800c03520141d16120203441d141c015100030402d0b03100040030001d05a00b000051a01801079010308581d50418001c0340c4041814040d2101c9065400041810080107504a90041c8107907401d02d1006812850300c1c0c10b00d1f4405201d103010600c6105100c401d50f031510740b90300c015410709118280c840141141070b2a10400611f000b0f0341c8500605002c191082010f01c41a00020156900010410f00f0b1004603038240c0d102516603503e03070707001201c184000790300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 742655899 1250 742654649 742654657
    0x3030711012003030a110702060315011403010b040b1606140720030f0901020a0b1003030f05030f0403140408010203254803020f0c0102010915020309011d0d0f080903 73
    0x1c401d9000c1406d066418080031030744a401c2d0000c0d005400042088080c100740d00c800c0218540980e80c0701c0100c1d000d0782845c41180020b000382070340050100400c110400720a0000c01b00e82e41000c8440e01c03101403070f80740c0208540051480b5004101c5040c02c01c014164000501d60f14002003e16920f175404034520708581c0e90081016600d0010b03000030301524268000c100054020382c1c0311841302c88610b011b10101c80034191a10007140821214000c49543c04e02500c1628424100302442840320f66481e281160283c038071b2040174071141070802002c82c0d070140c207000a500c11f41210f510741003000d480004114601003015186020414403154208000c012181558519250950405107943d100c66a400400c1c41c502c1d004190b10703c8200754dc0d010160041100301040b607040b0199450f00c0c1d07040f07005a080e0307500380d58004c205445070f2004400c05005940030b540c019908500000d0f41407e40d10040c0700c0c0c03501c030401803074641d170008690b0f61003141c0c01075006049a1403454000768509007400c001e0360301e000e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 742657149 1250 742655899 742655911
    0x5040f05070e04091e30030f09050c0904080409140114010f021005092a03060a0b061e09030102030709080d1d0d050109061b0306081c08150303071101200303 69
    0x45ea000422052220744190900311a0480800c6c984009180201d82c824210300303841c0f000401c0c14045408034259903441014400c40e001409040031074506003c20000300401407044034101d07014040070030703d0032252140d1024040407200c6c003c110350600c0c01900103c0010b07584141001810b5820803850795012406240d4401110740104d4962510240c45007014002c2320050355003081351a17256202101c00c1c100e054281d03070a4007a100c083c2c070740040c607106803014161070715008075081010700700003640140034800da12215800035050500e0b40c07002900760780c401e517001800160300d0541804204420702007805a60090708140e0b0301c0064805002841c00c3c650841c592080c0c16080e10300092181c203401080910340d1010f004c00500c100030440c00c502d20700f03100013070000910304840401e90400008042060f604840854411a08019400c5440090050506042d20084403401e0050f03101040a4032580d4030880c03804c0380c8034490400040c0140c1c10742e041074a2103500e40510189042000c13003100d07040703c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 742658399 1250 742657149 742657193
    0x9020c0d080709230f10090b0903010905062502210c0109062a02030309150603070e160e030307020a06050f0f210c13050f010905040f05070e0409 64
    0x562902c4090343c404081c0c0d400b9410500200000261400c59121120503c1200704c444c1c1010421040c103100c0d807610000e034280c002c1280e5290502044c0c031041c0161051200040000c110144695206818940191144d10380d00d1540c0440740c1501c16080b172440755407402c61005020f10350b201411000480480350516507a80400141c034494070f0405e402040b007281d0861410b100710b005400b130168400c045419100000029075105203619840482100e02414a801c018104c810144441040f808405086a54941305800713000a001c9a001c440510449034583c190181000c0b0f506c01400b0000602c64092003034204104400041e5141e02c94502a5030051404030345400f0406810071040c400e40000a100c103074003260078941c080720482d0200b400868080d42d0009a2180c036024289401404004810042c0712030080c04642425074141c4507040c41490003944280c0c0e11401719013101c4908404d544007540f00d108211910381c000d411010500703002e440801114100e5241c08150700168a5828400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 742659649 1250 742658399 742658401
    0x105220f0206031008011424011227060f0b01030603081c0f0e0a0c060201020301031a2814070906200f0106080601060801120209070f0c050303090d020709020c0d08 72
    0x213002c84d404031001030000c003002041495610500c0049101c0e041340c42c0d08401c001030401886a43d1144012200c0c4801a11003681104506840c01d000d000d4820052102c041410280b19404070210820800c1038019000001d00582500002d402ea4400c01050780c1410300781403040001418880441d1032154410106150741c0291301c00b07800140c49002e00d40c0c201c85c2d0400a01d14030080c2c001c85c8402c1c00c0c600c50801c2d07800c0d041d641c82040e0b0903070200348005000380065440d109140d04041e12180d0f4000c45411101c1c0640d0205950081c0c618502080480321a6841512025100e000c0205580005031414000301c1a0b01d8660010060030b09281d08910850921020004005041103480c030301040c0e00c0c00901c00c290701c80582e01c1e130fa0b40d024400e0a0024510340d000040100d102035086080580252507040b260351440003d5030002c24a50078001003001c2c8204d44004a241403000c1c5019180c920b000d420062066440289055016005000c83e18810400d030344009000044101c040b0900742021415 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 742660899 1250 742659649 742659661
    0x1506041a1509030106170618030c060a0914060c090d0614130506010609030c0b03061305010312121b0f12020a032c070501031d0304080105220f020603 66
    0x311100640d5800600301480d20711003841e9040682901c0005400030040301d0740d2450820409a00b4400141c0d4680102d80400c401e801107840c103040440b90030003205c0c0342c036500c02c4181c0d141071812102510b0480c0d441e12208100aa28543c14807012080740061016044c40640300c0c213180718107040d0794840d402034880f0b0b034100402a08448000c0000ca0a00c2105103044090115513203e0220210307114025000080380e0755001d09100310540c3d42100a800c0c07941e08201642d1030360751000c0c0c585a44034806905030440c07503e240c082e4501a5214580740845c43c442590050b003d8045103440b400b0b2541015403801c460074a04010001048080c5031201d030084a0060942d0709400d41d4018101c000d00026039010f001d42c068101620019140d00d201c410491301c98102c000e424201c03010703040c0a40002c0000c214070343c4039400a46034800d80c0e91100c80300c2c0e035142203450324542c000d134002c500e030740d4413201049503040c0c1880400c40d444520700300c080c0301c03001c040e560341d460403603c902c00174803508004c804111 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 742662149 1250 742660899 742660931
    0x24130519140321070b09060f010b25110102010e07051c03050f0703031b08040f17090a060801030b0604020403150e030d0204031b15020c0f060705060403090e09150604 73
    0xc494000f8050b20f005219100c0004460303402500181e48045000b00031901140b40082e189200e0400b0621904059080a09503805a0b0100c0700024100c943e1151411203083d80710404203d4511074004950984001c83c0007a00350391841d40c07400c0254110200030045a11001000501920142da01e03c0c00c05603585001c1c2c903107008012811190300b001081203410190942e000c1000605665440040303418440d40459089008850050402800c00c0080c070008008110354840c10042e251402c0c207209082d07020585c00480c0d540302d803000401c0400100b080c172103504440764101c4000d407001d41c070345030440e119502c00c0f070b0701c01e40c140c02604c1c2d8401c000030f401a804c0c025146030480e010f80541d59941d803410b00d40d002c980304a03000d6400c03a00104000aa210250300c41c080141e039a600030300110300c602c804000305003c4d0300607616044101000740800080c014000c00d8480c500c6900d41800007801c00e6441002400012f0014000e82d00c06006510b6003d001c441c0070b0792100040300c001c0b0307008090b000915 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 742663399 1250 742662149 742662163
    0x60a050906040f0b1309061211041407030212010503030f070215090a030c05010f0c021c05031b06310b04060f0e010605040b0609100e241305191403 65
    0x3414640400108100249000810005c41503e6000311410344880d400e8080710345030322401255030600006000024030003182e04c01500c40041001401c89608103c01d4240201201c82c18002580010145000d0207400720407800f500d0190021410f20640d003400e0070b0607104902029200300c1c030303150200c0c0c18901c0540c100d584000e000360500340303400c1d5a440e0122448100303000340380c081181142810340140c810307034004182d55001810000d0b80010180300c00c2024000410544803030104001044000580c0d02040d4810750407500100321610300300380400395120151003001c0f012070380b02040c01c10a90120740d1404c1903641000e1410701c151903c0ca410001000c0d48208070039180e0424a4005214106502540403207800ba14144640000b900402201b8820890104d501920754580414501d11510805821540c064418602030081d100700400140311940144865000000c01d0000b403188818100b00415080d41c01c10001c9002d0b10105001480034005c682e083c0005401c68525642c04120301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 742664649 1250 742663399 742663409
    0x1b0622050706141306020a0212240a0204031a090c03030f0a03020313050118060c09260a0807060b0a0501090815091e0325020a0e040302010b041a1e060a05090604 71
    0x1d00901e64907503021f902c07070312511070a80c860401002001110100441d001c0303080070341d40840c0c901e01070b0304001b80d2580174805824088915800d04c0040001100131820343c100369511400109545401d2120b10718009640d80c015000350024092030145c2d400c144103540c11b802480c00d0142c0c807952240c083c540050340d4501e02a02c550300340309941614a25031041010910b02940303040c080100c1030042510f0f00c440c14440c40e0070441601d511001e14254001400b4017010000c416214980c402d9100d08240740c000110685141d81e40f40007104044ca030130f0021038001c1030b080c01c0012960340340860141c0c540700303402c0c0d200034001401000100c80d50024001d192000c04006000000742901c004907c1d40c0790080451291071495000c050307100703800c6401240f244a0b9000b4814011207040c2803201502c880c0141045082d91748a15135082540d59501990381041817048030322180d1000001041200c507100c1d4030b0b00510b802000d000b490192a030108840100780a41003540d51070181c10b011a001340703c1c1d0751203 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 742665899 1250 742664649 742664677
    0x15090303070f0215040b0d0f0209010f1b1a1e10090b030a02130e0f010e0a0f030e0a090b03190519171303051c0507060906021b062205070614 62
    0x2010801c812000040c0c4124004008100041c2e88c1d2103040780308900c2003003486404101c4241c501d940c00ba1089500010403141c082600c03c1c401026134a040303014600c8a40d45590440000c2008901440009125601c850070108000907040c001030307a116180c654081c2c40d6040b904c0d52060f47c070903103040010b0681903a01400826030141b0051a0b00024140050601d10070b0184440d09200c410050090100301c5081c4070103450000c0140d81c8200039042010000c80a0000e030300c0b1004400e5440d901501c0040c2040400499014585001c01d401c003c1a00381169048042810b0700d0041000001e50580d40d503002c0c066400c503907403d4108403000b00000d04015480060001d52042c4c02154400e600c0c04491203401119042502c1daa45400a44440002c20001410600c10302c404210540c00001303d4900070000149000e01c1840203210350310315100c0500d0a58481e200b40714a070034440c0702081c8407000b1400051080c8841d9036409440d411b0305c0c4140700801246140c480000c0001c181142c5440050b210 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 742667149 1250 742665899 742665907
    0x3120f0804080702120f010e190213051003060603060605101e0e0f030a050d0f08090c040c050408010903020a170a1403070e1801050411090d02040f2915090303070f0215 74
    0xf000da01800a8078030881c114090105648401309c40c1e00d80e10000d02e61700801c1046900c3d070038112040104001800c0c0745121500c580c000011800031310030746014502800021507410f08010510150340b038800d107510300300110180d000c003100851001082e00c100d0340d4a80390a00103a218006102584ca15400e070b50706000f5000d01c0404c06c540002d0801d0381c0d50b026110b005204045020580d030181040b541ca000780d0b00020b02107646840d080d4010400c2d88010b0501500b015140c02c205821102c0c559421009030f84404145014441074007601d000c1c00d120903201501c0d01d40494001010072050014049401c0004000310306c9aa000d05081c449414000c0c00c100c0d80c1c01d00b032040f08803400c030080c420603000d00c0c80e22111660324440344040b070303200d000081c1001e60400728640c00e000041c16030350355012042d9940c205404611040c1c880426a42011140108003105001d003006030800d600702d100505841e00f0015081144c0740031090321841500b000040d000070341030b40046802c200503841c042c0c00c1c04100003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 742668399 1250 742667149 742667173
    0x102011113080705030606131808030a0b09011a0a030f020d0e060f06010f170907030c09020c1005040c05060d110a0804050d090501021c02010212010b0403120f080408070212 76
    0x303001030080715920b50484a6640d030f11401d041c0c492605864044c0c012100c0500074130542c48a80200c4d5014002030810004818141c1721100550026101e0450607034484905402e18600030f540d403800b600c0404a0311082c50710a0b00084000d11504074504141a101c42010355500f00303030f41c1959140215009d091040c604e0341c10005803181d100311014030100030107030085034045d44528030301046000581c03034800d11000c1c4900483c912000050001009102c1c1c074101000055140f0380c00300c000c14403584056140c40040899078241003a003e210003a06140c58108408106040e601404884003a19907a960702d110085040190002c1c1c07103039100002000818030350071a0b01c12401440341c1e00070415250f084058071030444184c0640d2245074010f074003011100744184c0108030288084825400018648010701080500c0340009034019860310a0228040080c0051601a412242072515100c6e441c42c108038070141501c0d001902c080c10008010400344115103032040ca914102030702c9022603103032207021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 742669649 1250 742668399 742668427
    0x5280e03090d0c1805060607110d140f1e03030a1508010911120604210504030605150103050907060c060902040e060a150b091507030c0f0b240f04050601020111 70
    0xc1c4940a074141c0e501c1354840441d801e605c80c060040c64001d01d85480e00e0719030307241d003091076034641204c2d9805556856030100080907080d900402c8915900903001d0b10605400349400c0c41d00a14034101d10079400060424141c00100440b030380241c1001d00042c500440c94125180356203a900010100e41c64000058144240c40c0101002c09404079081c062070181c0b408616181e18043d68010072104811001c1c120090315a07221580203c00c4d0324081d03003840d560340c4a42055079400d03100c0c3c803c1c18807090030010403135a06000d402da20000070401400360526060f4018060082548003518007581c07a0b40250440d5034641000b20040300c014100e810a0030305031230060040c0003085802e40701d24591103000600c1c40ea02c3c419031381c03a9400206044050354008054580d580d122240031003c12880414200000d8204010b40c0b1209000d0040c0c0708081c50a441040780440609400c1c140c1944411100842503407500b400d41d0b0280000e0710045071075209c2030f0043c4d014104005699810081c0820140707948104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 742670899 1250 742669649 742669673
    0xc051201240306140d02120703060f05220f0203100507180e01080304060810030b090f0706171914240609012007090218010305280e03090d 61
    0x1201c1a490031001c0181c0a80c1180c2c0b0502c601500c041c8010103424880c5400503610301d0260024104c0388004c10039030b10144c20040b140d00201c80742c96031007900130880c228078440e00394061101b4504c2c3c00000d540781030f0352408512183d802002c05290700300c031804540382403000b035065a08950081c0031601309007034043c0241c00700e0441450040c0803403c000502c9420601218102c40c144400f442c40d060410303c0071241c0040051000440c02c001110000010315609023080c814a62030019000c0e90b401e00142c94180740b281e07841441041114040240181c0c0301a03540c40e04503000f0300003280360382c0c0300c0011500078002441c050748420071808100407804800902c0700c0c680c0140111003440c0350380038008101c4e240c06100015800101d51084c01d909004000744105000c104c00e03800c86141c41e5503404104240d078401140028440c1058280803e1941c02d4061680c00902030500304161080020700c1e40f000d920200c4a44035015260146080ca0000a10441d038151001a0107000d010590782403003075110300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 742672149 1250 742670899 742670939
    0xf05040f03230a11010b0d050703021801080705121908040501030608121b07181d06090a1b1701050106020d05070c0308070602480c040c051201 63
    0x1c4104900c2110481010a20702d0044549026420702c80000c6048500030041400d03c0030b00d641c6c2d0f844640c020f50341c0c1c0c1c1f100c00308240306a0040002605500c14440da9a81e074a211190400d01d0300c00512400c000415510f00390313a8152a407440300d03030b815540c45103881d518440c0781d209845003003603c07414819030b00020401e5450a0700c051210590354922503030303100c1e070110700048a041c082c40440841400d040208607080c0307900c0700715542c0e0780e101c400840d80345449a1901c00b0403561284800c1d0540d258042801c6007600107406802c440c41c200703025580b200c0b10303490300500c03500308000000c00084a141e403140140602c2040362a0b011120010b25008000a001d070038058480c000d8054070341c0d07108004039500e403540a04105085451641c0b00e450a410602c8201c620380c0e000e0000e0030303d0004042c040300000c006107581c0001c0440c240c2c120198012441c0300c204103404241c80104400310005400c4403580c0042e90001840803940034101c510340100d14000e00d0f020086070000800740e48c58400c102e2100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 742673399 1250 742672149 742672157
    0x12080405120a080408130806011509090506010507060b06040f080303042003030a0309081e0a03050c210604020c0a08070c0f0e1501020a020303040f0e0a0203091e010f05040f03 77
    0x46a0a900619a0003101803560000d01084001000503503004050801000c006d1800054561a50003480c2050402d0308480030034400c20708032004080d03028017410f0080a100344100070908011000070300070710819a01500d581c0c0c4503106400541c981c00101c90040520b00306a2041546400d0300325220b42c415902516804080b6080c16140d130102c0d0b040c0022403400800071840c0003410181a006004207800a445501c030134009500c0c44001c00000064413003521920742d6660440340d501404444000c0c29810b040300b0305100e1207880056080d4094150020020f0f5140b26980d1540000c01a01c50f100643c4401d00400c900c0d07070304000c0c0c03002c007030204544542c092605082d200e0b51400303003078090741c07041c0d9002c810300c1030115920520703100494100840c184190b4030141d109802091841d40180d002d900420a603010400c003481c0e840d10a2500305400d06420740c86c6003042c60096a54070b841c480e0805620080390408200d08109503c003480402c0b40c0b80052140780f8050500c1e081106d0440010b41c082 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 742674649 1250 742673399 742673413
    0xa02010606110d05070b0c1201030809030f0601081b041e092d082a071502070302031b010c141b04020c071e050402040b030a0e0f0607180312080405 65
    0x1001d00450f40c801ca00445a403241e0400c002600c0f5044144030213004403200c150100809110040c200c941540130310b005040c50380c2c0d11900e08080c5460210980c0c91280e49821500060040c050049005441d0709540342c07600c2c181c41c4400001800078150003050007007010304035040314001807031500102c0000780100e1030b0400001c2c0d03110300c0c81341c1c9000907000000d41015001e800d0000030b07042d01c0034042c0c800903a034139060721400e454080c80800c18a945000e00760f50107a2410801980d10034502c0e10048d901d8800381c001a403030759002c13907942c00b55410341c1503e03164144100003150f481503e805988d20740141019071940000380480f0340328640001e141000c0c400240c11083c160515000b01c860020f0f0703140c002e04a26140c072140c0100601c005002d9501071110010000b01a40c450020f4009011207c851035502e040c0a2048411650300752511b003000e4002c2e1143c00c0301c503a000314410303922038042d050920751150440c231141c420314519000202100812480d82c402d50b0b500c00318040c8070300c0c07103041110780c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 742675899 1250 742674649 742674677
    0x32502060405030304030c0c0510120605031b0405070e0a0605090a1517071211040e060d1a070903020a0905040209060901080309061c0603051b100f0e0a0b0a02010606 73
    0x84100c22500036142c0c1e807080002c100080d104006c6684814003d41045100070b03210741c0000c06000c0c1c0a245c600004034a5882080180c6a07441f400c001003500721700405010340340d410031b1901c171240c1d0a4031502c550381d91800a0284c0c1d0185902c88031100009040000154030307800081d00c1c640150700301c0ca020340440c2102140d11030a142241101039000c1e1102d015030300300d460510440030308c0244078500304000414039041c081ea047c005ca84040c0b000301107150322541090707040902000c00403c203501c98983c45031800007041026150300d030204000411420f441e0340ba03000640b10b094455000239004640c001001850074115400b06010b00d100700c82d00c0050751148810010141000c0c024000140c00400c080d06291910360000c00d442c2c0d90240503900c1c2c406588090000b00d44459209440c103400802030500305c045400c0240c0e81d9042c0031501d0341e00401c0340000003040307941504081400d100501c0e030305100e159914a1042c006000102e08103945d0784252000034040c0240d8415140441c00ba101c83c2c0f40c0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 742677149 1250 742675899 742675903
    0xc0309091505041d0706050c0609120a0503040c0e24030708070605131701022d0406110f0d030605100504030203100518010614090f1014060f032502 65
    0x401e0380c2a03860545503250902040000414607520440410001c0a0303140c1e40d0f401e4203110100c020110b9896290b00c56161a031407030b04150b402880e0003541e4001c60503001c01c680100d401d81c1e2072204585082034030ba640d980f0300300c8921400d0341c0110680e020340ea0208400486102c4020650351030000d09181d031882c00105050340c40c80c1c180500f08550308004d50900145100328040c0815900f959070145140d559040008410065204107149070b03500028003128901444224071010624040d00c20003c402c0301c010400f26004070700405c0200034070040d04034001e41c4d04004038a0700210505c150b0704544507020010700100240c0c0301d4a0301410242e100030705034034010300075102126000307000b0703101d41c0e901d4070320030401032900800c04492144842010b5807079000901c070b840081c200320080ca03052400d1003c00c003c030300107000b003032072000c0c050302820848401081041c0c5011603d801c008003203001c070140006182c0380a0300744085d8443c2d0011081140400d00307001d48a507074a001c03108030360100c00072240407a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 742678399 1250 742677149 742677161
    0x61e0911010f180504020d0f09080c070501090b09060f0d0e0a030e1822050d0206091603020f10111506090702070e0c03070903020406060c030305090601052214070c030909 75
    0xc0b02c148400c3c0c0204a1402c0c5600100030794024210000f400c1d450949040c402c4600889083e43d0b241c60100b030811804c2d00030031030400540070034282a01103614116040c801c1d0b124030b103d0280a40c10215800b945080400b00f43c68032480c44407801c3c00001070b4002140d03074030740d8003000c2600028000d080b00302c95821300300000d020040010000205903604d003188505482e0130710001440d00d000c1d200d800c401044d4240500f4215510355800b03080c05040c03404200e460b096410013585000c900703031401000140d803548a1a46011400d88202751800c1c0c620780c054841c241c80c8a802d0f1030328042d43d40442e41c1010f4003090680304a0040b6403003c4141c88925040f6601c20140c00380e08090810342e0003084d00d011265000d16800036061405000241c1c4aa0119055412952144010031384000c8050f08040d0940541d650112280c40240543d61601000410541e84161141013602940b04503d941003110380124030400301040500c2d40c2420031180c000c05101d9012801d400144070b106000c0360f5621680601 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 742679649 1250 742678399 742678427
    0x9031b03100b030703020a0810050109051603050403171315020c07031403090307030303020c011a130c12060f2103080106110109050709050106090501050304080304061e0911010f 78
    0x1c0a00150180e2050014884055680c1d4948503289002005a8a07244038001601844001c1e0000c001000d91a105171079068100107509418107041240c98904003220392011a407618021599440398101075540352242200c07a06180d0b0203001304002e10030403092141da45c510507038a1181100300e01e00707600120b0240c1c0d40c01070300d1500014400c0022414245030708000a4018003540d01d04000640001c0c50140c00742e1085001c25000715103c11420300030300c2070181101000b0006500c0b40c1c40301c030008008001c4030304500c020170382d52002074182512a0341300040329100c81d9020041c4c00d0300d0b0303124050181031512410002c5119903420203c28603114034080d601d82e5068a03041410f03428200180c40f000111007540c45199a1040c001e0042035040240100400382000d00062a505018000704140301941150b414000200103010000e001642101da100380c01035800540d103030841c4010700c50350304200e680c20340050400203824103201510400d5141d04000340c13910107040e540640240c4001c40c0e44404 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 742680899 1250 742679649 742679653
    0x61e0201051003110a1d060f0d02010f0f03060515030609060d110603040816110913030801090218060307050d0609050105060910030e011505090703021204150207021509031b03 77
    0x81000041e0803a05404c80c0c1d0703040189034288107502d4803014899a0349452006c00038221b0201800380d00c0c18150f440624100d000d5902c21084411600082c1602c3c17640004542000700701d112a40e11a031107640030b1805420300802183c0c00440c0c452030f40c11103800555a41c1c1c81941c004003c10003500d0400722800540f03074040c100d000e032901e480d0308011803038000801c02c1e191000304202d00e00c61a003040c0e1201d41c03054440d4803985035504545051003101d00000303221000c00202d4400480200780c000111504650303042e50701694640e803403042c07051540002040d9940003030b004000d001407507800070043e01640005500030060380340d8540030710080e59420322034a0b811000800c41e60115081020a5a0410b003403400d01040040b01c10715101c1c21510034150314145902014030501c41443c04201e43c40d0070503000e00e010340c10085505060001c615010300000c00381903403401c1340ca04444003501561861a001841c80e0b00710b1072170070a421030315800303141034078071a00681903a1000000c1d5241865010440500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 742682149 1250 742680899 742680931
    0x11505011b0f081b0303090105090613200a0807060e0301021206010509040908030a14161407050f030310080c0901151805041b02060a0c0512041b061e020105 69
    0xc5888150081e12000d030f0305440c0400044c00e192410000d503110000010004560324035002d01801e0840700040c0c6940c02d1500040180801c0c7c44d9110120300089812802c0544201c2c40034005002d481000d1820702d421a03640940002c00c032202260441c01c40c3d4079600d41c0101d10390039608042c00c030b10800d1100c110584661000c1029541f10f507001d0000e4540c042d20001d43c10042c1d07155001c840e0000c6038603885041d143c0340309a914189107800550030591055061074142c1115001814503102d5506501d5100e90206038138003032000400c02c2c1c402c0d0701c5451080daaa281480d0702442c0543d981c0d0300800700207110b000c41104450820f01006030407208000c0e00000324182004085440284428030010316500300752001c0b402e50340f10300c83c03003000c06100342c03000d038007c41c07500c0c030180c02c15400030044013605207000c9007442941d80010850302109240d5503070030803541e1207291601010040c803801208840b80c101020441503004580740c5240e80000d9007401800320100c40407400e0b0380080300c110a41c900740c03007 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 742683399 1250 742682149 742682153
    0x702070305060411010e13060f0e16080601200a1208040507050112060b1207080f0c04060e1f020d0810060c0f05120f03010504060e070807080604110a02011505011b 72
    0x10501d800c484c0300502d0849000c002e0040041c4c1d402004800c000801955901c0800c000c0103842c01c0c2d0b40c0141080712001c0c0c4149400e03c0410000791241d0303000001d000107500099066172185006114820382708201d54800fa01081c8129641e21f201502210200c444030814201c19002c1d61556100350f5010000b4148070b4201001164082508041e042c5103913101c50b0042403074140840a421440c034201d11100c031918102d000101a000007510140120b51940705000f2540e0140c001c807001e070354031400d0810306c400f41040400c2c1201c2003403008204904644c1700c0e03011181d41c007180700c54440507107654100c0b01c3d485400c500f0280340381c035210b600041101c104002000490080081d42414058015150006261032411600f42e000c0310740401e0505001006010310711785442110041c2c840b03600643c025241003440900f001001400441c18407003408002042070752150803d5410707550011010b0303200c0381e81740d601074082d0001900c045001c140351407001c5199403280d03480e54405505400390243c44107582d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 742684649 1250 742683399 742683413
    0xb010f0b0f16050f0a111903020d110a0e01080109030e030309240409110d20090103050402040e01061e0509040507150302040506040b04082415040b100305010e07020703050604 77
    0x300440d01402580350004c44000280311404485014040106002d06240100804520b40321100d407505629107105101580311100c404c070705030b41d000119a240e904501c00090b00b9a003190700c10402001c1e0741c1d00226140d5819042109058030075240c3e551961050001c060300d03401645003641d0403029080c1d5002d10100c40d4541c90000424281c00e041c5000d44030418041030b91049200a40c18013000103602d01d40308100d220741d01003200c0304d0b28500032800ca4100c0c008010f220324041a810182c0b541c2c082000d40daa2540004914140300e0000c0003040d550300301045140707103c80c0640c9201d40403400001000d040c548410303845668414054580f01d402d0900c10b03506142032082e05c0d070400d9030a10001c80e25403100c2c8000d001820703e40c00c0c22610345240540043c5400e030681421000c0d1f040b0242043c5288500052154000f15881441d188080030000843d008202500340d80d5802203040d075592001640503406241601c412000c6400302c0e50320040241c1c1c0d00d40319840014540d03480400094080340c80 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 742685899 1250 742684649 742684687
    0x60f060d1e09030f02060f0412050f0d06181d070e0903071205030f160f050903010e19022b0305031015020f010f1109040902030703080301030b010f0b0f 67
    0x159400e00441c0080c1c40c100c22104900d8044000c03449165110403da070301000072580c411007100b002e074014606a0303180c003030381c2d12910316120921101007000d00104a42c0000d8491441c4031000c00c108856590007883c0c207041903485581c060f107240452041d100b00f04400d0301e00440e241c100040c000c90b45841d40100e200c94005010580305c0c001449032200003165096552456881c0340c1e951512420b11002109001c40064048028044880c0d4010072030794200282d03c0841c1203d0920039250a400070100740502110540640c090280301d5010328400c00d1810900b1205000f501c071400d558801d0140e0004004006180c5040d03543d960441600080c1305030011079201480500300b404403035550a60304003051121258201507040000849442c4800748500e8a0341c0d042c013841803100b0131410560000c9031103840030007070040751507a21600c1951402c0015400079984458840d50b01c0d0381d0ba04010714440028002c0c48500303001444c000031014440340071398140024a429079454501c03030604070468401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 742687149 1250 742685899 742685921
    0x1206010309051f140105180601020f01020426030901020709200301090e0c0306060d03081b0a05041a0406141b0f030a08130309060f02030c1f05060f060d 67
    0x7031201c015000090302805101d0a2440242000f100d100c0340111280940e2480001c00000c0ca0003003004006903a60844200381214051300c00440540b50540102c2c01c0510044440c00c0540c00010001041c11000000388000d00f05d2004440051442425041d01c0e4400d444005005a10844080c88a5a15580302103915a0013054840c4c81c11817640c1031031286d4200b40c0c0302e08103441d540e10258500c18402e0020184034081140074008a140050004031201c84411010b0304010b01040026260700301014104003d03c6a540c1080c0c40f8450030400600540c41800f550901d00d070b6000d4100c20342d590403c180d60070b0792800d80319402038101c1b0800e690969000703038200c0300300c0d03040105c3c85504025050150010091900000d1941c502c050301026203648406800c011581440c3c03004000800ea00c544100140c42c5146060000759012540c220b00e1801044001d44990081806424403c2e0602000c41c0c0110424003003441aa52094200050900742d054072941002c0f04005006881d20140e000c0c01000e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 742688399 1250 742687149 742687151
    0xb400203210406110a0c0e18010501050616020d0c0305030703020f0102160f030c1a01050f09011a2a060f07021903051e0c030307081602030a031503060c03050709150512060103 77
    0x42ca035900d1b941c400c440140d00c015080d80c510710a04c545051021045c02403404000000c4c042d652416001c24400d20641c465002c981f10322400400031566103070404105660890500d5515a40344c0c00d0098807940304000071400f502c5141403060140806009442c22440100c0e1001c640c4003180d11030709912000020110f013041b90a40318100000c188241d040a540944140c0c0701a83d0304110a102031140e01e8032000e480b6101c1e9400401c07070281c88081300b80e040e8000342021034840b1880d03003260030402911810000118201c020348070703045c00700090f900d1091845540e51192034540e80c0302641c03590ba400000d0b58403210380480c800c1c00700c0d0045005249801402c00e410160141d0b10341c00c074015410804507451203800010502444952014000350012104c1d42c40340511141008080d580f8820541d010052580790150346901950310001c0c000107540001d4144091038400200070005c1c0400c40312000411800d01c004501e1024001c4540c0c1d0410131903c550f0710f0900c1e010101710030380070001c11480c109 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 742689649 1250 742688399 742688413
    0x40f03030e10050709050402070b150d1205070201120c0503161206030c05040516050d0510090203040303090203010e0715050c0f030c030406020709090b40020321040611 74
    0x191820814100c0c0b00c5900d07540082d05041c409401000c00c1d80300d83c800d9108a0050100d9400300341400801c1f900040203030749407100c01c80c040f03002c500b1008010344040c0880d10122411440340d030700b220042042038400d036100c04104000d4910401142c194455a100148003270000600d07000c450355550100700312508081d5484000204240207880598004a80c2c078501d013442044103041a004164100014a690f07445403809124002c0c0300f405040741030410300b5281d4021440186105880700301800000788295900e2915040140240048020881c0030350318180a0300d031743c0080407503102c00f03558034800422a00784000d241116070707412104850300300d80a8032144000d0900200014900e086103c0e0113952120f2030400041c0c20000ba03640320020281c00d00c011540040c50458040e03078031a14a00060104064071500801c1d2140101d2402c40001c2da641842403d0b02c00c81d0401c030301034030320031411a007262200c044110040c010762544441070742c900f84401c0c445103014102c002c114401e2007080b5115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 742690899 1250 742689649 742689671
    0x5100f060e0a150c14060622020405090f090624010f0219121805210a1b08120f03040605090a060203100905010b07030e10091214010b1008040f0303 65
    0x721850501c3c1d0340042808441c510f010040c0c80800700401800000c0506041e2030200081503081e800c42d8054841c115980c41394402d8041d5a9065501074000607110000b40c4c40d20b919007042006080d100c810b66032045800140450121803844055900300d2440c00d0300d01a1800c00541d103156a0150060a50040c20304c51162104c8907481003119900420450f02d4071154403a016042c40f1610316081c0c03403403402d80010f014948a0740400c04500360401400e4400c0e0640070a42c904006108130010026416000404e400445151005080d0380102007940d02820303111600213900d20981d04103050b513000a03c000b4010a04960000750301180d500152118100e143c0d8903030007240c1c0f00b240c0c8400c52503144e040138403550810348511405410304500b202d04e000c14503180901188880000e252182c8281020040c2040c812a1224014804440881c09580d010300c1c1c40750410034100b40448641d0710303000c01402589060b10021088400c00d844405058455032038141401400c0b00064080c10b4443c001414 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 742692149 1250 742690899 742690919
    0x607090614090d1b0608071b0809030f010609050705070f2d0f17070b0f0c090a08010e010f0603150e030910020609160602120304110604080a0605100f060e0a 69
    0x8003284070f4413080c984100d014400d5200041150810030400c43c0083c00c01000759000070003611401c2024003a2080340b1050301d014646031003100c9410350540508404990910b0b81500000160f4000c1d21080c007007680d8403001140d42c3c1c0502000070380b8032150341c6840c1d40441d14507804060074aa04014000e0800c1c0405407400a285415808541904611000105011003484d40d1303c5c1c0b207602030321710030328001c0d4640f11018030380d001030442150b041da00c01c003103401c60340c0a108403012880c001d090401e01d291758111050003407e0048c1c80070019424100d648401104502c039070402d6941c40750200808034451140c080003800d00c00001110b51108011800d410343d0741c000e501c03a1040e00b80d03004181e5031400d102c44904100484d0307405103080c050f6050038060345c6c1d000b08001d008916070f00d120a45a81daa0b0400d90281048100400c0d081500020082298a8041800e8150f1030250600340950780b01c99000b0082581c89110302d000f101190403040c0038140c4280d0840d613520200900c203100300c6440384c0c0090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 742693399 1250 742692149 742692169
    0x304080303042906011e021608010e010e1903140d1103220302030d1a040603140f1507030b0d12081501090521030f0c0a0c08060709061409 61
    0x150f54200002d071024031283c0f4205504612003202070710b02c0c0c141c0c201000041d280c0c08000710340001010b40b40e080307103008074400c21180008070000307000003002c25a038440140c001c101c140309014071542032000032265a4000101d82c01c09400a010844002800b52011100800e660302e07142c02a860400807034406401c44e0081150380b140b0883e206640b800d1102c08480c259100300b0030901c1c0b540051088170f002c2500802a284090311a017004120841c596040441805c05842c000790300519094021084c8091203d44040c0d40050408482072908200f0b84184d80307641030403000103c6903048000503687e610a4011034103c0341c026200c40d11580035940c8001c052540445103d001600c4d9604010030391180d100c00c2d200e00d020070308000070305c3c1d828070300450410780404c251101c0f44100007103007142d148002c208aa44000301006802d40700c0321003c648030344404001106a0702c00305102c00101d02c0e200e01150050103074510303440301c2130403a240c900f080d01c076600f85420f038003a819400d210161285d29140c03424 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 742694649 1250 742693399 742693403
    0x3171e070c0f15080103020f01020106050301050906150109150f030b120d12020702030a140313080c13020307080a0902041b080a240b07020d0c1805010602030309030f0c030408030304 80
    0x584a040c101d031a146909158044511500409041540c664000c854541502c7d0140c64040790001410b0040c0e02401303903940000e415610780003c22440e00c1c004990540a00001469192180203020045403030070214082c0d00b01c581c01c000310b2159841e0150400807501030740f9050101d850b543c07210000d502c5a81ca602000d400b0303041425240241c2ea40b081358802c0341d01003c0f004500381034040e000300307680e100c000030000c000f85014003c03010300c80c20400584131030044801c02d01c0ba4007078482542d95103e50000d00542c1c0074070003c5403000783c00102802902c2c82224581da5010490740ca840001018001c20b90042ea0000d540b0704100214040000c56881c40c0c01084d00c81024030708000d020b82007100c00c10213029500c55009034400b44040e104020282c00c4505084100da21b8500e180002200f442403401700402403080c01e0000104c600c4d80817246c2254401a040c200420783e0f83c1e100998aa12003100c2030042c07604104021000d07030b52514081c08011041f01b0842e424a611080c845181d0350041d82c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 742695899 1250 742694649 742694663
    0x6270102120c1b040509070603020310032307091b0309020f0a0603140115050a050a170f1503150c0a110106060804020a0807151103070b07120e0703171e07 68
    0x1c02d104071400800c1c10050f20a040e03808101e02c0c900204400d80318210380c01680101078000000c20301030a0303c094200042c41d08061079014000480c4005140700d8102504a05240103140000416200d584075030a645002c5d02030441c0c045030300c460100c0040c01c0b106812640040b040942c003080c0e4031a281090043e103119107001401005032401c04404581c141d0001d42d000420302c0c80014030f50b034010140d40b002c41081c10001d840e0118001c080c1d80b6081440d007c100110550b0f01004040781801e00766502500811080600c055880c1c07003415240c00a00c0c460700c220255010200b841c003580e0300000c1509501134036010400b001344601d45425104503500c80c4000401140c188015803802040c2c40009140541c001e0601924058024014200308a01d18040c043d40c04030441c90b142d011300442c0c60807907003e00c071f0703c41915004038081d003002010b140d171002d00f41c43c09000b008201c1d070009443c3e0941c0e80021780603000f0b4141401c42000b035885150440014030810f8030700b41e03095402c038010b04a110300c9810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 742697149 1250 742695899 742695913
    0x1603050a14070210030b01051e12130c0e09010b1201060e011e0501080a062d0b07150902030f16030b0705040b07031d0d150b06270102120c 61
    0xa004010082901d520888110204000c00041c0d031841d14100c2060058240030641511030f000603a43c60142140180c840c000780c4101000c58414080100403480844c40c50b05842c0c1c49586a02100c41a26a03005000500000080c45690b00f00301140e540520f00c0c2c4000300b103210400380412500400c00c0400c5445a4443d0006c0c8044075511203076502401a801d03041d2015450445401142460340c0315040c1800a0b00000c142d0325030041c0c10ac1ca02034003801c046228444580c41540050a80d440034400d00c081c03d005000c1520380c020b100315011650040380c00313106260305150741d40081c04021800c030b1307143c41800b82440411000344400a5080100c3e100c49010500d1401e283c001c00c10020104401c1003000c0105106002c40401a81e4900ea09454465046600b004201d40810a00e451040c6d20011007000c010801901840c00480c4600080d07040c044244414140110b501580d01c6011110f070140e140c41e10400941400844c1c00c000c148121070600704040500c0031241e0241340d0320001500220 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 742698399 1250 742697149 742697167
    0x2919120803011d07050a0c030e12060a1a010c02130603060c051e03040b011202011112090a05060301050a1a09090c0c010b1009090c0203131d090a020f040b010203160305 74
    0x1280000703852802c500241e00f481c2c08440248035202c0c2c1e1103000700f0310901b041f005040c54810030190b0300c03202c40a0b00307042c0070640082034540d9407841107407162900e9051021001d06050326010304940c80340113071a0900007034055803c2003960f0f80b0403e192101d20356601800070124010380540911002641c8034a80d581c0d00000c0000c038030f0181925494000c50302002403200062801d908113044034220f2aa41003c5031251004072003d01d403981c1401c2c200d204808083e4105c0d00e082c4c005184c0c200080752107184150383d8006020345400244a00340d44001e80800410951095240c24041944030148051902c0c181d480096407000c01603c0303200c00d41e000400d01c003169110900c070742070701440d0844582080c2c42c100000108242214002c141c003480d1995510740000d4000c006646110700b440c1d00712103880c1d80781d4005036945115042c1c0030251554203000301f06450780216280d2a0150041d040c288101400024040500100e51400d41140310400140c410b07020042011125188241c1d12a6600d40b80d00c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 742699649 1250 742698399 742698419
    0x70b060108010b0c030a0e220501050321030a020a050712020c0f09090a29041401110a0f0e0d02091e061503060405130210020709291912080301 63
    0x58000c1c043c0310204101c108001d45000013507481c400b030207107013200141000101140d07000c00e40006964601c0c1090b10700700880c00745034100e14140c0f4010380483c0c42c0e02c0140307541229842d903e201b448450410420119050b0341c807603001407000f40d5046c20210718000c116600c40810041d4040c0140c01a0400e00303944030149032401040a00c104112488142401e1030319900da180c6815201c0100000d6207001100d030404a040420900c200003100c01d59914a40fa090200c81010245811896546040481402c0308500c8059640310030381d994900c40c2048400b84140c4800c00070034291544600e4110001c3c00594031043d203d442000256903c0400b1000620300700709141c4043d0405200e03000c081c080e40d00380031004040c4c1b0b034403410444005c24607031508501d0700c0f0301e04041c4230040c1d0448001c81112100369000900c4404540c0d0000041002444a034540ca002c501c070042a1030303200e40b441c60135507001e00e40380360076982c61020341c0f82d02c0d14403944d916810124a06d0b41c280865402e80080300400c00f08a41d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 742700899 1250 742699649 742699651
    0x12010602060a02190f030f02070b010311100215061801090903020c1c0f1b030305131a032a0409060612050705120c0c061e160f110111070b060108 64
    0x2d11102507091800007105541d6041c0000485010030146400364151740707109402002d2080c814080131507070341c0c0c6c0d242469014201c00f40801d544480c0700c400b1015050800407903184134038000e41d028151030503210b00c0c0c0700c4060300e001c0c082caa880205540c85034103c2d11700c49059802000f0406001881c47c1b01c0d0700d006400c0450001021b84a80c940044400302100f5481e072440107646c0c800510144002c1620341500706003001120f44900704204c00000c03041640142c0140000c451001c60868080e80e0740d00003138a108160301400c58000c3c4184007162560381c80301d101101400c00d20942841441d40d424140480742c100e44d10540c027590302c030001044490f400011a860302120081c0501452500910141081c401c40549907084120800012485004082514440e44441d001c0c6c0c1c010f1309107854000150900807806000071f86003800441e03052405003130249500f02150301e8544400703903015816108404064074500c019501d030003d11940004c20401004400e120b416450b4060a2801c001420810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 742702149 1250 742700899 742700911
    0xa0c0503030a0603050d080103080301051009080a030e0a0e090c0d02010e12100e0c090411060f03010b040321020d080702070e09010203040b010806040c3f02031c1b0c0b1201060206 79
    0x500e1f00052000c21100811030b8107680f0203a821107410f1210100890390102c0e01c0d40f0002041c051103000e01c2c02c01d903005d184000300d1142206c40302c158948507104031043e484280c40c0042c82c0d5000e00c2003403060b410b00c0700c041820346005060414141e480440800c030192045000404140c100002c0420380f1443c91040003804001c0e45c0c010002d050801c03020402440e030192000d49403801203080d0644030b94408040b12104c42d507808685403656550380d54030344147c00a010841c1e60802c14030b45940c506489a030b18000240d41a0b00030116180c9044050f80d0882000e480f141c11401a21404a41c46940c404203074082c6035820700040e9203280c18141428001e2041e00621019003150041c400070883c100d2040e4140c40100880c0790000d00c60581d6100c0010f00003940c95204214201082d07503601014840c1d40e1207038021b40c1a50030000054980100c2c1c1090725118001242008104040142c0304c10406002c061048060080c040e85800307941c580b0743c0040c440786500005e900c005100c0a9810311125801003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 742703399 1250 742702149 742702157
    0xd02010b09070e150702030313180c1b1112010c0e100905060d05090106050a030515160c1709040504080c07080d080424020d0b010201060e0c07080a0c0503030a0603050d 74
    0x81e00c03c1c40090a54207050300c1040100d60046883d10a541d41842169240c811003c0c1404000345d4418510140140802429111515000080007214068030111202004d1906485042c0301c00d0f5640003e5140104100c0303400507410b080b0240b80a02c2481002c404034415103408600700707000410004446500880902000814402007141e0340380c0c0703419100003510300c01c0301090a640d5000014010a0503500140e40104080000001e01c4000714102c8a801502d0030340034032a5132049040317064201006281000201c030301c2d00d04030200d464698038404c0010203410320707490502d10300001425a001503800f0303102c9101c00140a400280300b041040014404c800241c080343c200c01c20050200600200003820a2103140d01e15480301c082d9454008204c0a0104110b444513100034510006014504140c5d025610340040413801140410031a486040045100d500c1c011540d0380d142610741209034090107101c1e608180100040d82400994460800e8000c00030706180785082c010f29004100410b40284 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 742704649 1250 742703399 742703417
    0x50a0914092409030c070e041208060a060e0409170306030601091b11011d1c0921030c0c180f0902090a1802061c05061801030318080d02010b0907 64
    0x3025041203030a10703490701c1c100d0b011402d039a80c2c0743c89400c520030b80148078168019030102003017962080150a01136401104000d2000340c003488182c503814030039511568069820841001224840c00c8500111000030380042000441540c55003081c1070303c5070056641d250048104405810100400350041c4010b207001d01000d8900c02c910707405103a40c40d00000c104144012400040d680942150000c0c1c0100e0740c4120458207900103041d1540180d508001401c445816203c0b10716105842e05010350f0280c40304410012011600041d00c0804c488003101845001031004001c642007a80003001050040003100c140e2031b11207800422501c440720080521842c200d40503001d6210168015800803400c1030004140d040b2581051703000c80c1c0034000a5110b10000b5180d00d0009000c2d20320f500759214142c050100e9110f00007001071505024100c0510840300000410200784a80c00101d811842c0d0105e204034140ca40c0d843d5410036040078403c1000d82e4544400050f181046584c041d48849a89010049 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 742705899 1250 742704649 742704673
    0x5090a02090709172815050604020c0f06070207060f12150e1306050c1606090312020706090b010f1503200f0304050d030506060409050c0c010c09031a0f1807050a091409 74
    0x50724100d0b0011345640713031f610000103100c0d88480d4102e90f072949001013240c030341510060310540c1e00c1508a41220043c01403400005200340209420140d0b01c07901d403a0001c0721403000b4158001081d5468406101d0340c0d038120001014942c2c1101c15014510382000103412580c941403c3c001d0780d00140c1040b201c51810000c0048107040020002c440a5000030f000c100d02505080885584050260503640c2500c00900c940400080f0380c80f906103103205080f20b03611a81c0e0303015000d2a12030f40780300e0400700e42c071481031050f48540309900482c5490003108046015481c080a600819040400c601e003c1500c00020301060100411250f080c411031741c503062001c1d20f850804108075000c1e0344501e81411b611800443c2405040d00b00b59031150340c03190000c000056414000500031039440c03005072281b80451041e8101100400c0801d841500e401021210585516800e41d83d08035100050300c816000d41c900214a5564444c00b21000308015203002c1010344a1540e80d5820b010094140003040e4008052401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 742707149 1250 742705899 742705913
    0x8040306110a1e02100501090f0e070b07021c08070f060b040b030c010f02010906051312020c030601060c02060d0c0e040605011b0318030510021c05090a020907091728 73
    0x100c030304010041ca9401d80214400c4e440c00e00406811445141040004107100c101580444e41420200300f05119000300b85c540b0640700da50314000c0e40150034040081030054203045e40b441d41645c004042210ac1ca00050303c540326650000d1f4012203110308902601c070301b40051809029003001c4200ca0030010003210100290707480340300e0310300581803000101c4982c16490003135010084c0f054100c9401d1140c0e00e01400001c4807510b9103801190049100c005001d000c85c80002c911004c850090000c00c40c0e6400c1030000d0302d108540240403a8415420060314203840854012481000602c4d2990172455a00a081205a4010741c00450400040b030301c01801c010503088083c2003090f01801c16030317400004001200c03c4d54205803c09085482140000760300c04c802d80d03004042c00e030010f0384500b0461003100d0b444000d460301070394000300641c070500180d8050320308211313040e81242d01341c00c100114031380c1c030119074600141010130640f0541203000206500b140c1c000c0040c40404045003a0400d00700c0c107a81d00d0f0303 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 742708399 1250 742707149 742707167
    0x190816021f051009110703091d1f1701090c051008040b0604150b0403060501050d0f06050702031303050c03061f0e07020a1a2a0a030b06090d08040306110a 68
    0x4501035150300200e21680d5041c40380030f010b0130a40b0000c0c01080c20085061101d54807000d800c80c0051801840001c041c40240420b0b0000550780d440c4000544980c1d4600c5910b801200074000001c0b8110000a40469102c2c1b9001050105000100f410446802c0103084c2ca40307540d008900070900f8041c1c101d64564032890141e071290340038050b070019455000200e0018564881785090300c2211030b40204030423640a0141003201c1c07003040144000c1e07803150f091005080d500500103041c04c0e4041a00400244a40c1200d6448456071040341d00f400c00b00d85929907146170755070040c0d03490f404c00740b400d80c0c0c1ea0905114041e8070079054240d22405280060103410182c0a500c2244251255040403405280c4240500012141c000400c8500e9004801480301e10200988a52100a200f001c0d000903113840a4030740c2803e1240e10352140d041c445126004d40140c4a0002d1940c0d000d40c0401040000d66112410070038002e0003a44290f40740c9042d860f1940444051b101c1c1302c1e61100b070034000144080e5000c0041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 742709649 1250 742708399 742708453
    0x1b08030301052d2e050a0507080a0e130902011205160c0809060a0807080610050a050a11060c070201110309031f2c010f1a090c19081602 60
    0x1003c03826503481100d128105400c10800e62080f245401c1100818509280246100443c4070000e20142c0c80303001a43c552084c104440041582030028101045407940501400060740c100018007146180000d05c1b500303103440c1c00c00c089a50314000c05080d964480c408040c82d1140240230442030900c0d0490683c00c41100701c2a60030802d182880000b00318104007035440741d99003c0d100c40d44800b200480582542070171914180090004030006040e8503083c01440680c5010ba110b0501c0c0005201085401c3e61158000c00184104010f00582030102001000d21602207251103903101c00f00f038030004000a500b003034400d500d54000c1c070bd84c61065038041075001d189030090720460325800c0d50500c40c2c005000040ca804401101190740e4460143c0003c1c40080d0244540b03000b08403c02c8031103500c0c01203c0800d04400183c540142800500f400c00501940c1c1050070700c000c41e814400f89420001014041d0340b0090300040d404014403403100710000f24448150040c0c00900300320b410741e00d94195103103401211 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 742710899 1250 742709649 742709689
    0xa030b03460b0c071a06010806030d08040327150f0c050327060307030603030210020c060109021b030c0109020112060509060411040f08070315050f01090c09050402071b0803030105 79
    0x1003150018070f28103e61180764031030755481ca400008150410011800c884080c04108258001001880c0101c3c152818103600d4894011741d840320340b01180d404100c0d290005486a80d9100c0c48c00c000c248030142c3c0000c0c20441083c2402c3d0b0701c0b1080007401c0a0040c07101e0700612a41e0f607225400250040309440502e90000c403680c0180103071509a04019422040300c0385c1000700001400301c0380e40d0540010064900036000c40d80d103908111481d1040b4460440078401c02d8218200501000c202a0010b0204803544110700043c44009026a4110390004c40c141c0321980d03440194200f10f50300200801c000250400d010440e191400c000300f400c50000501d003911403a55445002111907400c030584001e0050302d100d000201d03495418990b41c88843e80030a45400d124025003100c4004c0c0c0d030160600c00d51480d600780029034070b003000d06000740c0030a180803028068041004203e80e2600d1015150150161f020740c1440b600042c2d1803181c4c094141c0144907907401c1000184044e487c0d00000003007003d89015 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 742712149 1250 742710899 742710901
    0x10203130f05121c0509032a0309060309160f05010c0803131b1805040c03080d020712050315040b030c061809070201090201080f010f0b0a030b03460b 66
    0x500942440441030f1081c43d0800040380c85030042c130307040480c13040340300c0c1e501c1d400c00003034a41006031682d034010329410204001440e140814076800700915180c4140b10007040b2401e1510003000a91160401c968640450780f00b5119005500b494100c49401041d862004000d002d00f000700003440209075010261101c0c10000c0801c1205401c0444210306035007045151040382801040c598401a0501c00c2c041d000f41c00c0350f049580ca41d12841002d0140d540316a02802961031642c4d000d5442d040082c0001040382e0900c48200403c0e012003225200610325550f0301e07070701c0c5408510b0b0741c160005d15100d24000c1d8038100f20308031030382c038000f03590202c0c1003080f40e0b000d031030700e036a0b250380d0710400b428040e41034208204505014060b034054110003031041c400d884040c04d035503d40d45030f81400d4a0034420b49003140400e42c1c00300822142c090050080841618011a0000503040400c1c5030000714032a4003c500b0b030400c440ea069101410b001000c008500003903009001240703880b80d1014140300d00c0a04a04107802c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 742713399 1250 742712149 742712153
    0x605030703020f0d0606020303091506100c02120616080123060d0204030215130803120105150912070302040c0e150a09030c1d06060403021c060b0a0e011403010203130f 74
    0x40c0035118207103c0c0c140140002d0b900c46c01e00a413690816039400030140b29040401440d078046109107032007010040c1c00020000d10000044403400803a640680e0484010022107a5481c02403103003601c2000503000f5543d8810b281c41004000b510160b00920072040b48507040c01000c100c0c81d00c10180c0f160104d031101d0f2180c012030310302c6c002031240f0340c0000e50101c140c0c3d4034040f41003d008007520f00700b080c000c045445c0607510803001da01e80c455549000e00701c180d42e000501c0b203440e00305495492210240084c5007403244070408155051202000400c01c0d5010840810442c6064040c03c86204c0ca185045600065203c0c00700e5000035040000c500748010114a203802d041c0b1400c1600e0003550420fa66140c03903a0340740340d92044600048001c0380e160f00c0150018055060020850342200e601402c0591408024001c82030030024043c4102c4410307407260129180da5540c203010340080c1a0344002d0041e2545000600d01c4547c803c00b103480c1c0213034014410800b11214121000c004203800907040c2000320054 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 742714649 1250 742713399 742713427
    0x319020d02041a0d03020f0609070506030703090609020402040602061803041433041e0e0103030c05151503010f0c0c080f0d0908121023040b040f020909010b04060503070302 76
    0xa00c00040d00844c900c0420300c1416400161081201c0d444000e480c106d4407990115601c686d50b60007559000003080001c520854404d9010783c25043c00707008000350000c20b0b940020309030303031180d031111005070f20880612000c0c0c25013001d84440000e980d4029840c1030300c0c101e1070f00141e09483c1d135414451ba06000540c1100c04a140d1544101030410507a1040c041a80780010399642241c040c98107400c06000b8010b040b41d48100c440c0064510310030310001c00e40c1c43c560701254141c0310f40c4000c44103405194040b034444402c1030b400c503005052480300101d13010400000d03d400c440845000714003450501c060780c036007039801c103040d080c0441d000818035031740380c0c14142090198494010309a100a103002000018000d0710400342031a405548402410345d1070700c00c0f11006c82803660242042e06983c83d11000c40f4040001c101c1060103d0203040407401c0e0100c6070000d000c5400201416030410740002d2903130482e00d0030200050242030031414aa0616080090050050000410a400307043e40024034801014030b0b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 742715899 1250 742714649 742714691
    0x2a03090303090b07170f09030d050c1603080a0b1c02010c03090e011508181c09050607060e070806150918190507060c0201020c04020f130807050319020d0204 69
    0x58030310603290402c204001c1404150701420014170040d00e0200c0c0c482c01040d000300f4005c07502d12000314204107001058038004d00c00075241c0c803a42d9000304444642c20720510114071200d806510ba42465242c8540206d0580d44081c9166205042056840034210000c1c640a48030640a03e0300700c40007000c515058a0b00710030b5402400500701d109000140b016040c4d840380855045917138490046440c0d084407411065a800310b8003807182c0004003169104a11741c0100c0343d1001c0c031841c050000b01c1d80d4101080580d4051001629015119031070308038485010004c010041c08110002e2400b8030703144440f031900d501d28004462242116902144d03004000300890104241000180d0345c1050845083c45a0303070350100b00c100e4444c0100800080e00500960350740001640603005050140552010003000f9808809031220210052282c0d5091045011081c0041d0456a004058490600007050325040b181c03041c1483c80000041108016101c040ca820450342d419a004201540003036218001398807 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 742717149 1250 742715899 742715903
    0x15030b0a0306060302031b1f140c060126070b130b0c0d030b032410090c1206080c1f0306081c080606391b01032a0309030309 55
    0x140c10314021080c8120365110b102181d108504941c80c0f40c103080d1413040c43e403078940341441c0c4c0172150007008110801c0005050340c040701103241c1004d514800101f10221a00811042c02840e44400010300c0021400c0c1c3c40c05440028800042500c140c6031001c8070760310309160003041411708006c00c02c54400d00248201402808d4664a201c0e00d0b40c04d42d10002c4d554440389803c01001906040d040801d605000c9500040c80f00c003008010030505032816000c52790100940380381c0c00e04d11302605c00151608107100b5242c00c0c105c581d036001c1303030101c2070b46904083d11410341002000350828882500c0319600c80c28420f61000d84064041110294110142c000b48010f9001070320034014075a802c45e030100c942c941e031214074038180c40f1000c594070382100b40f02140c0110f5a1281c010380f00650401c0414100103800c3c100c1f140d51017040880f46030152101070800910b8407030300314070b04120010b000d4150380500031102d1000315011f400017149051081c28100302c1405500d0303024107641390a414241071003500030000c2c03e6 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 742718399 1250 742717149 742717159
    0x14030c1e03090301060923090c1c0b0412090b041206090303200306040e0f0312060a030c030c0e180a0803060402040f0b0301050f030316060b01090329060d080415030b 73
    0xb56103c181e00094080740501c0c03040d140c0c0c1066107c200040c01010345003c0c2d840c40000b0002400d04000340001512034214424000325500e40071000288410251351240e0302c212000400d4425021300a00b6410240c1c003c2800c0c4101403006100291014194003850303500801c02180c0d800f01403e083d40105085484100c020780602e0706584001c9000c00154001e0000b6a4104070b0722502c0d103e03071900c0d42c80e0f400303034400c9a800c100302000000c03024a098903088003004200b15005075a9a4885102c0c22803584111141801c0d104104110301d010714100350300414040d58100701155075901d182d190144c8410080481d40c0c00300105a0640303859040c1c0e005041e068211034a00f94489019001e913400c248144d17842822400103044241c18044203071102c1c01c04101c01d282c0e400c0d8060b41c41d5000303058007244480c10401c0a040010214025503000c601c030204000403211103c50a81d042d000b486130091115000c0c1405070194000a0b080a080781c007103039151808001601d004590440c050403424030130613409 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 742719649 1250 742718399 742718411
    0x30c040e160f0203180f06040f090e010f050c0d0903140706020c0709060b040b2104080903120301080a06050c0403080a12050a2702010e100c14030c1e03090301 70
    0x2a40d241d00c0d2100700160382d1103010154419035000c82e520720038406520103100655040304658100021003d034003c800500702070030140c83c0e4020324404110b90740000d8226031600014000c99a080c8600e9048062110703050090b441d00c004606c006202d2102d14200d0266030300b80d044c042c50304c40d02c83d4106903181c04112a583e80c0c0a424076401071b40150b0329000340340c003400343c001a680d00a889023000715501d009480d424503242250b0b100240e0021800200d000098804061303000b549030901c50302c540d00c90215070b07403201c2608051514100d4100035242c58a101000140a19800000c0d00810030341e20000115a0350384000c4000e00c54043d90340000c20400000c60b40e0480b6a800c800030b8481c150400d10104440d40d40c0c1281001901d10404010850106440b08051224042a0845510350040c103103400304c1001b120200d41e00c1c503100045500000c0b020000d030010452018810b589407841c2c80002d40c1422149105103440b800410054119420229400c0036004410300549804240082c020040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 742720899 1250 742719649 742719661
    0x1a15181e1806010801151206060b0d05040506150603180109020d05061605040302060f071e0809120a0506011e08031305150711040f0905060c0904140f0c030c040e 71
    0x2911441c1c4000405001e03210000c51850380c144a01500c4050b02071a411400e480c180010450b010480015900661159804254003040f44028a04030303800307203070004182c40c00341005e50410001030400d612680200b4400301e2140c3c0d881056a4010074491031038480e104440e0507060040c40c1883c1c000350413203100c810210510001291941c854407810079901d0001c1c901340710465082c4a0750000035845102403001c87d6098480340003410421303104420807401861801d094802c10007009904685000001408044604004405400681c2101c008250010060740d5003034546505005000d03010040c010f21182c00d5040c050068010101c400540b980d421018803000c020b04490300607540510b5240e0b0240744008820021108079079002207205c451103500608010241400ca8400500c09458284420104030203008890041d0050200c0c680d980c44a0414001611425900d440900d90754004010b0a0380000214503884001c440c0e109503280d5441d0760100c028013840c1c000000c4a4a03030402c01103 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 742722149 1250 742720899 742720921
    0x30109080304020108010501080403051603050f0309100e16330207050f0d021815180402040b0406030506010909301e0f0c02060d091a15181e 62
    0x2010b00d0007a80e40200030381c4c82d0801540d12000c1034500034009501084a01101000864200004d511030718180b468041620085a15600282c4140801c0c1c3c1200414500e140d00b140710b09035100400c0406806a130040c20740e01e1450712094410344110400201d1741101092480c04040700c080c081500d410b40a200c001c80c002e5441086000d85405590020b00708520f501e880000c2c1c5041c03581c020110054000d1100b0207811442018160b41d2181441100c804201d6560001c841114044040400c10381e244c5030041200b5600710b804028041c51600405002145000ca00703181568002440416512414500031004070039007015610a5003c0e25200c008800040780200d03101c91440e0f84040c1101801c0c0c82e4520728040c50340044000c1100d884041d2020342c05400c590042c6800100b1040c20558040c03505c10a8505100c030803107400c4010031039100c0c02429106800c2d0405040032405001c0b00c5520040381c0c41d030b0750740c82c000c1400350740120028800d60250148004140a00704103184a0b060010b1240d07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 742723399 1250 742722149 742722151
    0x120e1203150102011e0209040b1c060f060609030206180a0906141f140f12070f020a0b010501080402060d060b0a0f0503060d080906250c05040c02100510050301090803 73
    0x1c14822041044244598414050b00f00d0700e000300d2007250015008040c22038002d6200c1e03c0400c2d0400e1711548050711030b948459100c64000061542410040e0705890000112940a0102c100c00c920308803050101070b070702ca00b07080d080d250306445090340d503040c1462130301c0c121845640740381e0312a02c0d41002041c101d030325810050445030442802c00810248808100341503075181e50207030030443c07031007410217000748281d0200800c490300e080502e14100c01e407020142242e01c402d8400c0203846401c0c06000d0400e920003100000c80b039452015001407a40b03075803016002441849494100f040b810f01003025561000d00f02e03072031481182c40810605641d09840b1056030001010240070070b4014503602d091501481c00c903840b03040000c1c501c01d1a010076a03240c00d841d8001281143c1c0007507060048610001500204c00c1803071040000350040d00fa40c0d482d00300f00500e12904142d02440c10f013442c40c1c01007a00016035041c6c03254007480124090b560014100242400c1d60b1200e541503082070300b48414002c0c698003c0d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 742724649 1250 742723399 742723411
    0x2120316051608031c0f02070f050607090501080403080708100512160906140402030a09080403111f170411040c08060a050301020c06130303062d090e03040501120e1203 74
    0x2c461803a40c590080c0d46a01441000c802c5030802c1c00310009020300c8540c80f90076084000e80c4d00600f40461522a01080c10074808200c0349641701c401800303040307a0440d141c1d00040c0024600341c004e510307243c0c1c0e000340801005402e01091081407004604000b83c0c0c4403d010240c840030300030350030390000c002e0516a00d1203004690f0002c0b007198400403070031900d54010714081d61000da821040011075502480300941c0002c224000720750b03640e40039070005100c0d0301c003c00003580103c1e0f84c140f41000c200204420144c0c074a04035240340030030aa01694151300310040c00c00a4003450b014203040d6880f4241140660309001c80d0f1035116141c00600f074281900202c20b1b038041c0c00140c1c1d403200100c0d20f400a01d400c0b4400c54141081c01e9000c440041c1400c441c08040c8900c051180c40d0214550f40c0c0c40034600780120040016521022040240d0001245100c540c01e004140c0141c0600040200c000c8554480c427850156030b0400200c600340804d05000c41c2c02003020004010202c401f00842d41415415035002038402d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 742725899 1250 742724649 742724683
    0x30207050a1e11030318090c0403020d141005100e04031206090e0f1615050705010c080609060901060813141c110102031005091302040507030f0e01180212031605 71
    0x41114142000419100c00703c01d0701c1061b00b00d07601d080c001c000101200404001c121720041201000503114444105036013485440d0b4640400801c03c00141011140c005082680d45418100802040180f099404072070054032100c000380c0340c508045640182c41040c01d2010760812a000844074050707407200c4c0c41407541c082600c007942c180340b9001ea2038030300443c0e80c46542506054180031041c4641450180c480481c1403403490903229954090039900d0702124070003c641b955040040a081440016a000104842d4242c066041c180050b2128001070f1880203400441d869040410030018411a116078449080b1030041403c0c000c01d10484d031a03952050700007204145031000031003050095a01034123090003100040307030425050080030000208021502c117120081d00340961103a100d4103001d030440b07070340100380f034202192020305503480d840d9042c82c00c1e0301d1310f034007480d01d48120301080400303507411a0218044c1500010261460007003100c03510400791041c05410401c40300048002a070211452 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 742727149 1250 742725899 742725923
    0x20f09151902060f070f181202090117120a050c0f0d0f020a080d330e010519050d02061b0703051212060d060f1503021e030d030207050a1e 61
    0x503040fa1100c40035a40384950440d1000410b0a0501034510003143d802d0700c0c940803034500092500d4100d0400b465101c2e008100f0103901c20000c0d81066041c0070b02500c0d403907a520100040f40300e440d07996984020072000900d103022441006841c890000ca03910600da860464400160703004559445045130f06040d000700d5110a540c442440c0081000440c281c0c00c0b10525060228038547c40003c0c0102c44e640c03043c030020085d510160000c070402e0008084c42c5080118582c0d50038000b400500c0001a04114841c0302c1c24411010854403200903401902c20503900c0c2c0502498900c0803030424003030041c980341540c1e40d50166020301d000004035402102d01a2048481e12601c0042c51003852091480f0711420000303c4000500a0419500d004165803040c4d10024500c6d28015146040f1410700044111120710403000700250300c2e28010130084a000560520315003001200082d0f9075280c840b803128180340e00032409009000091000c84102c60300007590030241c0810703401601c2d00f080b01641c01c60b12801025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 742728399 1250 742727149 742727197
    0x711121e100f090c090e030d020a180b0f04140616120f08150909103305060a0c0501110f09010f110c010c2d031b02090a020f0915 57
    0x2000f5003403120303084000f4010380c1d4204085040a8142c80140450324403041100901c05856403004002c281c0c156580c0d03070425880300b80c041c95480ca15030f101c0d4281030010301c01110346580160454048403204c610007190344020801103402d5009040486d181c1540c45840d031014080030000344000e941d4541c0c0c4402660f09900c8040e02d06400c185c440701081c0c03401c0408201c680c24003030700c00e81d00400203d00700c6131800b540241620a40b000c440000c2c6800003200e1074803000156003100c00e80c007004c80c0304091180508000101c0c655008000c8400204002d519000341488400e5110413031034400800c015585104030316585645a00100c8e010340050341c581200d420840c442c1986030044032088020307080d004444401107803401d042c408281c4080254240e070011400e03624080c0f11901108207801501c141d11814003416070220180c03802c15008200e0391420059440c0000c4a500050311500187c480311920fa0500d540c1c0144201a6080072012410b41c500921000251014803482040c440e0311b11481 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 742729649 1250 742728399 742728401
    0x60305030a022508070e070201090b0106090501141905030c04030f06060e0612070320190f0e0f0106051809180601081b0405181509060c0711121e100f 66
    0x91080d40c0b4550032900c014800d038006d01c41d80c1d9400030140d02c00499000c040340c562800b1032000303074402c6000c00c0941100f00321658001d21842140100d040d4104d042c0208001003c515040044200040090000002d8100e0364001d084d280690b030406116482004c0700c0c50182c0081ca680d00904201d1400c49002501e2403400204044c4020010005002800d14640e100701c00d024528803515402484200d581e109500c8200f80302c01e01900c854001d1800510340700e0040d6032621250007298040140008111003800e19412150444009144c01a42d9198524140101000700c1c0082a4001c6100040c0503248400000d0070303a03030250850948003640da0f2008400d079240c04040c0030700d0104400c0402c8604900e07042c2c0c403866100842c20302402894865100b040d0803c0c01d41859075046819241c240010840c040080c50303407101150344541d02d8180c0d02d0f1100f40d050751408a9051049202890a0b448440d00707010228409400d040e1090343c00318030f110920b440e510840f6070650314615141801c4290401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 742730899 1250 742729649 742729723
    0xb040602030909060f0d0f060c1e050307050403062f0a020a06020c030c030408100c09140607150f020a030f0b01091502030708120103060c09032103060305030a02 71
    0x1040d002140b0305a11401440400303500100042d60040e0480c1e00800c0350b40b40c22016082030352040c01c1103060700046140c808100c42c9188010000c001c80c5a0b006064034942c500c6a81c010110303420656181e5850001c100c1d158072941d0802445141401e000d81000040002040081e281030306149150900111916905010302c510f0309006901c080ca03410042140340c0d0042404610304c50503039183c04154081c141c5542c0c0117078002101533100c0b24081604174200c1c803c40f9000359007840d020030036a180820500c6183d04101806105050029040c030400c03105680c8030020501c3e0600034001c03900000b2002d00250016080700c80405d092110b03c6801c14060320490540d0307039050f11020b0109041080c620180905040d160055100030840c0b100840e00020280100740c5c45003492200a43c103603d020004d5882c988031603801d0082030b440c10b000084401140c0340c00c000000340c0e0544401d9500c41c0440c0540600c1d80013400600002504508580e40440c92503681c10003400b452800b00e42c40340d03000440841c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 742732149 1250 742730899 742730909
    0x60e0405160c08130f031401090b0a05060d0c06020607090602070b0301031704030803040f1e0f060f09080c0f011514010f09170c010f0f0801050d021206040302160b04 73
    0x3503000800744800340211985402c00b80038101c0b443c181890900382000b0704141c2c0d08092150360160700d0800c02c12400b009101540d021440003031020310007035551001820300c0501811046070319580003aa1130307104ca849411901d508902d0b403030000351743c40302c0294884805645d000000381b64084081417031340c00000c4010442d83c180403901d16585c42c41d04d51082d00d400c41301c0910b1068200300030010104180801850050b130140e200f00c1c5560401d840c181e0190304607a5403140d0307815121400303100032030780706c1c110140895080b42c03000c107002d909045800000d110000d0000c10b240008036846450800000b1201c00305103c40000f0800307403106843e0090880382d540314107800c1c01464400384100b54410005484400440c0c2001185240c40d0b4541c581c600440e440c2d100900c0c0c0c0b06c0e14041c2d14640c0d000b120741c50001c0090900e09010100110010b14190050048034001c1500c840200c0864640b000111200c58100d020b462880c18140f90080d12090184010602c2084191012400f0206c0c2c60454017121 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 742733399 1250 742732149 742732171
    0x221515020a020a030f051f0b040f0b0907180b040602060f0105041104300f0201020d050a141806070f030807020c0109090c0e040c030b0a091407050313050115060e0405 73
    0x41c1c95542e405c1c0c000c8098101c100c90601070719818104400620640da903503c4117010000c0f0f0851014001d100485126034548103485003881d10380641500e0b00501d0a401c000381e840d00a0900100d140d01c2d445c51780e103d9104180001c00002d0019080390b000c50241e028124101c40e9801c1c5980c0c3e5810131003500c06100c1c0c15058440d007000300300500100b40b10002411020f00b1200c079946032181c54908142c0d00c0d8a01c4c181c800c10805c0124004669051140304070200c0305017085410a441294000d0424a40d550100840e610000b03519001c40023002d20501420f1004000e036a86044510b08440200c041d507100b140400c1034000491069400030a600d00f40100c1a59800415850004040302414440307218100740482204000d8403521140078001d035140ca191408212a4092000d01003080d515500541005103405581c0b80804d45a030b881039040010303807621580b0303616a20441c1c80c8040240304018029842d00030260307042030024544804075035a40c0c0b58055138006100c1484259101192829010f07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 742734649 1250 742733399 742733419
    0x4020a0611070801090f0501051e1f030602160c060503011a070609020904080a09060311090f1903051e03090102060420041416020f0a02221515020a02 66
    0x5a00c9000001010841c040440d0900341d540d00c100c508650f0000001c5c0d13100b00c081c5043c031090100902500f9008410b520155440100b4400050f00521018000e030306454007000220301094900c0c100c2002071a00503d085556070282d4402d19184602d070541102e440c4005032002544d94010320a03241201c03120300290403440081c203076414144c0d001c042c04507152581c464484015807160031099201d00c0c0314003511039441030400b002800d1300640d5445a001c1604100c0003a41a5a08600782c0b019241c064074070f6521001524000342c210010304541c00d1210140c02e0000044c41000940364181c40c0410480c01002c89501035644e8580c40b40209890251740180f02190001e5002a000002d400020780041701401e60340d80024165020b2584200205c0c101005001020035140785e0903400011300c0c00105a0710752440b18041d04c9000030f88000c0d20440000c08140000b8240e45010035541503a03010070088610140415201d03013005002c6c00c1c08911040c010403880d01e0000620100d1950004c0c424406 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 742735899 1250 742734649 742734659
    0xa14130f180b01080708030d02030702071a04050103182a051225050d03031104150201021306321207080f0c040612020c010608031911030304020a 64
    0x80104040040261103986415000c280499881203004070851401c003010325441c1410301502d52981038001029640140310100003018000049580c90700307400c080542c580d618083c00340c0c24045075034421031000f21100d00d0504001d99201c01802610b10076202008061005040b0500d100a9601c0c001c000b121415540900d04041c0c0201c0c000ae82c0c0054000e40d2142e03168404540408180c51040703219030b01120342245601d0340041410b5041c00781400d046101403903e400500780740344121307000e420315a0311100c4040c9080d0441c2141c000d070440c240c25180c2c2c030301d0f00740e0000d00075484180703215442e40c80d040021550f00d1046002c8202603d003042c0b00c030b203219600f00c000d0f001940c0d8554081d01511041010703125821080c204d25103d0700b1191a010385916207452510100c14005002134107411080009114164122401d0341c1d0702d10001030010703211055003280c5801403100307402444040c4408140396030103185004150550b4500e594900c0e50050903c3d589070380d00e000035200254041d03000881448 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 742737149 1250 742735899 742735909
    0x105010f030f0e01020a090e0604020903030306091b070311010e010624021e0604030f0509010206070305092109040f06231824030c090c0309030705100204140a14 71
    0x52120003400300010580d102c0b41c0701e24221b07404800c4000100e075004100f00705222200d4402c0ba407201090714154504120b100000e5200e00c00101050311866215004c1081c21090381c8072410040c0131403101d241d5550071030402503c0102540c1100000f50f08020402c05050b4060240000301c62100d10441e07030125410a00d000708504404070801144111880a02c02c0a05000940c40200590000c0d1400e1b09007814014021944440f0f805e00340070301041541010307603002600a40c03184807454005070640f64410300905202c10a8a03114000e0580d403018440200d5070070003001e0f49030044030100014840c0c1c581e40c905840701d0f44100e48108814804090741100c0c0180b004120b80310050400740140b1f0030441990b507488050366942c01120620071842300c40e50b50714401c004842d80442c02411030007141000540000d00040c01c0c413118810200101e803c940c800c20694106551040903920003807040310080009400910948050bc10503540c0c4c00550300b018010781d4180d0790a410034016200ca4902440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 742738399 1250 742737149 742737161
    0x10f06122123040501020f15010311040b03010e0f0c150f0306010309050a030801140d02061c110408150f0732070602090109090513110a080114010603060b030105010f03 74
    0x10620800900c50714040c40030441d03200b01d42d9440c1102940311030900e0f000a252030341c003424801a990001c031000b6120f17081585440d0450380c4c0520030407001040140402c02400c154222903030158204a14008101c001150301000004440d089a004100c88010000710381560001c403030b0050000c00c144034004004000959001e40c2c10b04010600240542d2024a090705260301500041c444000620121484603103445014030100c0303c00312083d805030001640c0c0d01c1103140d044410300d2584030003010440035400203034100c054038680640700d40e07407035408070b4546000d110744104d000e0306800001d42e0a201400b81d14002c000581c0d480381855844034250f5407119201c14091089558070401184075220600205135651280368090307100c1c0210000923001c8038854002440c0c0d03d00f4a01000845c1c403210040e214100e4101c40c0b44040080241e001c0340000d00d0b030390800034403075082254100d0110113840225040f0b1f0b9681c1c0d010014240e55500c2d00005000a00482d400038002c0b084529689100f5000a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 742739649 1250 742738399 742738463
    0x304050117150d0308090601050409080919030c090902030105010e0906070807050910090e07021b0d1721130f02010806040e0607201b04200408010f0612 67
    0xb02a007510010000744204804240c12000204802c08001d01c91109002c17880c01406d050b5018412501142d4801c412070061b80e650034021044108401403607203811000303034019a0807034510000203450b5158440038040041d420380c041d600f01800000c1d20210070001c2803180e07104a0207094540c036116021100302c000601840b0800500b40300042040d503c0c01e1181600c089182c0701c02d075010746070034012001144000c2103103003035401131190301e051050040e6190f16404001c8030b00710790b1003000e0710b016141c0800a140d64802c142000c00c90040400b0300144000e03408000780e00c29240e59440158890410480311300050048501051010040d4007521240e0341040d001003021035031021420841e403a0280469130400020507503409000003455501c18014061a0030028024150901c0c150004400551440070300455a9054a1055207000040307010485e0644052a0b80d6130765605006002c0e0114001c030080842c501140082d441302ca4204001c10f00307520000400c5940406014120001c0304001a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 742740899 1250 742739649 742739671
    0x30610050c01180c060c151d100b030724050d14280c1b02010216091a09070c15150f1701020301061d0103140703050402090601020304050117 62
    0x62000000003e0040070701000c070780441d4140d12503c90508514076209544404203100c01c4000640c08111001d40080b2101904d0308041241c0b000c1c4903d1809241e041d05000e15103000703902d030310b03c3d04181a40060242d80e408034200c0c1c0200c0c0d2130300360100a041a841e0903810262060400028580c003503000350100e54002e81c000144a0504062035254400440d400c403c0d030744000c000c805a08407500b04480c15880c58600402c1014030144001c0e2240a40030307056080e035038200751076000b16842004002d40c089240800c503030805a507524024013a152004843c6544049004003040c0d0303050a0071000e1040829a0f1089066001a00d60030000075100607684115a01d07040e01c481452041c900784002403100e00c80e007400c2c1320b00d441d4003c030892010503140042640100f00411010380d0049920120010080c00c06290703020304001a0010903400c0103844c90840c0308400c00103020780651206101c1d5000355800b41182d501c8a00490316031003240505804070380c5484400d464244d006518590150f44150307 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 742742149 1250 742740899 742740907
    0x91b030624020a0f210518041503050706020f010608030906070f0204061502030d110304050a080a03150605031603050606030a0e0a0b0f180c0603060111100f020912060c03061005 78
    0x2ca60541c52a600e400303641240038122070031440d80c2c08120007132408030b85186c520704280049645107465140c152019202d1038a6202c0f0000030110089110003c56001046421240d542d04010751210840c00344004a0b52802d440041d10b1200401120230b00d802c028443c6180c821242e8591b0305800c1d4055060340c00503075420700407030022480e21130a06030b407509400540e01c9224a8400106683c4201e05102c01e1a03024024400041d4000800984c0703030f03512008a80c0c42d4071004400f1402052480a07429400390340050025000c1c1d00f00c001980103004400c066609105000f0040d01515030545140790071407006c200140c6843e80c9503100e0089026940161540000e06c0e0b210600c90100980b140c2e4403500000091000791210030508100c001140b0300640f10f407015100008020740401840300741400a211520440c4c0034080c00b80d501030403401c2c3d03010810042d04d06040e2000790440b8641500a0408000e84109180c000542c140318031030120760149150f41d000103200b005240207a6290074080280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 742743399 1250 742742149 742742153
    0x1020609030f04030303052703030604060f180216060f050f130b010608070e181e13171216020f0c09040807171222110f19091b030624020a 61
    0x180c002980c010300d58002710345909114082100f120b00300d500003140710685500c10000c6031800110544c0c0e16041c0003005031103107002a101800d40010201c01005589001c0d0703030310120060781d4400d40c0242c5041c8492822580c13140c440450201c3c216002811101c0bca000401903644100303c0d65030310500b1441c0c4510b209400304042801c2c003205044040c0d40b01d850400f0001c05075410041c0e0514034110700103003a01428040701003180701c00749800c007078200f022003464903141034030f288226441c0d0911030104032407519242c58a002c0101d078103401c1e01d00501910179940c010250004122400340002000d2000644490b07903500c00b140d0140c04200e40803110504059aa1480c1401a1180300c0e00704042d07540901d40540402c07000d541c1500642e200ca11010308070000300703d2202943d820310300240c03820011b80b040040003501121214020040540c6050008100c1c0d1426820281c0783c589800c0881034220221001503041e94028081d610015280c0c80110a400900104038914082c0350300644000340d01ca6 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 742744649 1250 742743399 742743451
    0x60f03011103060f01030926070c0b0c060604051501080a1d03131e0b07060603020a08160906050102150c300604050c0319020c160501020609030f0403030305 69
    0xaa1200318800304080200903c608000100c481c208100746000c0040034526543c00d164040602101401e0150341e038201c00030f440001045032032050700500c0300507449648103103502c0f00b0b92041e00310301032074018040840d000d0f00b80f41c0078035800303501148001313880448414011140100e00414410760191104400082c0f0701c0d9000c404000008000040c664030883c05019212180c2e40364000d1607201c08451007104c94409030711a030f01c2515080035149548007a141401400740200fa0400b130751080c00b20303900048880000415a0891250304000040c1ea6900c410740070480f01d0601c91240583c1180c0400410f522520443c241e0044035420030b181455201d804c041034607040030020a03410400302040b0f291180400c18641e40c00b14003181d0a21240c41c00e840d070200075000181c40c100284584441c501002842c90301a01caa40e88410b0132643c95880780316844809444a22549002d4003c0c4000310b50702500100031540088440c192442c90646555411001428020548500151000101e1f407414500b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 742745899 1250 742744649 742744661
    0x1811030c0409082b15470c2e061203030b01021603080406031d071e0924080f060c090111030a1119020a050d030c0b010b0310060c030c0605060f0301 65
    0x450003001141c6030804034898003804d0300700200d00d03043c0800c0d951200743d0b0704808000d02e119104992070554010800c1c0ca8000c0c980500080f131741c04ea000e502031005c14407001025607201100300014400323501c07146005400841c0c040f0b015007642480f954401c0300120780030380c104a01c08070041c8100c9500401d191004500328206410844a0b9080000d0400110360f250082007030104030443d11100071502095050354854651047c0aa025000d64504540180c040742c1003000313060204042c4800115411450349070702e150611a80d0201c06a18041a4400b000614102048444c00248204d8641d100d8050282c4c002d00501410810890107070b698011061000c2d29090181e505d4410b0183d25424815050189414001d140d0440d803c8000c009a030b11109102c00321072082d0380c140300f415a43e090403a040f07040c1000c00f03031901c1503440001442031031260003144a10050060014840c1e11940101d6280d12149800303400100051448070120b00150b1145070000320003005a644200814086825950 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 742747149 1250 742745899 742745921
    0xd0c0509011701110322061d0102030a0e030306211c030506010e040b0d0201050c01060510090e01050d030e100e030105070203180604060818011811030c0409082b 71
    0x80d600703202d031591042c2400755043c100700d4201098110b250104801c0240300240d01029010056501c0080a0250540c46280b1850310100d07444140d16146580340c0c041d62042d20001d00103850514030b22030624000c000e803800f81d08011318180b050440300c05003003110fa20300880c0c0780c1c15001d40300c0440400e0160409580d0040515100466076203055000175004007181d60407103010f82d050134240201a03030b660700b0140c01c4960900f816030b201e0604c544014010b040a400c080d41006d00e240614412580004021007203401c00000e8031000d03030301d41d414400c2c0e8624404c4000d02061080c0c0c400649031400300150124100f651501d0760308102c81200007400d49200741c542c1800740e04005200300803899402d82c0e400d807003101a20000d00d0540341c414010211000204458101e0180710750085a0510070f4000300900360740b8910218140b03205003441085034040c3c001c1c551181c400c0c05618030382810030340110b22182e60000109400c00c0181c02030701e402c480754100403c42d0840b080031800344c4602c50780314603000c0c0c2c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 742748399 1250 742747149 742747169
    0xc23190e0a030b06090a0b100309080c0601030f12020309030703140f01240501140d0e0a08070c150206060a031407030b0a09060c080c0703030b0609061215010f020c0d0c050901 77
    0x410a04240415a400609045041410540c0d01007e030b8803030b03250510064144d894009145151410040d002d0f0085603410351490050000001c00e00050281d40c8401d01d0203a0000b2000c1120014183c0e1380b8803a44c40000c1d0980c103c41c908001046c520111810005070072425a0380c5a50104a041c1c00c40b0004030200e005120360b8548051401c000d03441300400f510082c2840c89404a00c0c011003640e074080c0381c1403140c04544440c0c000103c04010700038621000c3d0301214254030b44441e481d0840c069041c1d40a140c1c0c0c0100390070b82810034281b00003680350250300060283c1c11130b54210f44804402c0281c0e071001500318400c1500020004074009600c030f12902c14200e0003c0c50583d1841c0c50b000ba280204581c004111814007800a2202100e00315260203525007000665414a800414140d024050081d6031011002c1500c0314403100721f4540f503115900c4000040d00301c00d928030066078500c1c030310307507040c00160b1241c1c00c40102414141036810405001d280144101690362000404031002604044103617 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 742749649 1250 742748399 742748401
    0x80d092a0602011401090b060403150b1c02090708040c0807060306051c02090c0a021203091c02033109020c030a0206010603090807020603060409020307090c23190e0a030b 75
    0x502641411a010701280d2009220300300d1642000c402e000c4040c003808158507640c503106410b0b60754800480d4011a880140d00504118102098000b081111100c5004145500b121104810000f5801003016402051800725456101d002c039181180100222444070000c00b000c110754070200000c40081034240d501040041c2801b0a000d0132a442c48a6060300079072a0b080741c40183d44655a8582c0241e5032110107032100c410708400c910f00310003d140f071048004000148540d14501140038501100d52818404c800301c040720701240e691141000004250100315220030032075000800301c0c09803840940440340d46688481d100030890348a41111400b0764000642048042d8042c0420750041405050800c030200150321542d003a4811400024420b480010000b0055904d641c40204481e40103811200e140343c43c1e41e1181d000f010504180d0700420786401500b2008003410401031107000b0f02d0407c49052040030010355005000303080d1001e0900c142400c0d0850b00d601c032201c0240c002c1d40140785400e65 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 742750899 1250 742749649 742749713
    0x7080705031b1f0302121008060906091e010b1504031419030309030203160c1d0c070f0f1208150105070b041106040f03140606090f0103080d09 63
    0x1070450020100203201c408018500c0c2d5990b6001d1602c00040801040e009070141c8042d0110b0080c420114420a0040001c051001e0200d400c400101070320303004422143d42c0e40380d0707000007942c40004803040c0303960b9800403030500507000680d19880c12007a00d4000100d041220b0500140c42041000c1c9130f1020120007140030014800141e01000203820682e0140c40343d03008030000b503028011003450203000c1c103441e00b8024003054820022580c401c0041840c2164505842c81c011552071441d1203414410301c1c0a0500e0380c182d2144406c214050b00104410600c4c119032680c490701805485078042d80c0c07041d0000003010105900c00113061400781c1c10742c1d844841c0c2ca01580301c101c4004812110504008040c000070000403d060710084e00103400040120b402c03136200e0700080e8144120382080684000c501c1000040140c04020381c1a0340d041c400076509141e48007070901c1307600e0904803041b04100d0202001000404d0118004010094020b0700124002c0503603150342440f000210711603a01c4400f06928841 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 742752149 1250 742750899 742750903
    0xf04090510060c0302060601200f0714010e060304020d030c08210f0708071202040b0d0203160302070b16030b120d0e0a080d080c250605060a15110a050708070503 71
    0x41c00c2d050618866404040d01d0007591904000d082e50705020242801084500c80d00c480c51030241c107403008071000c2818203140591101603600c1440040030031900e4031400ca43c080c08800f10000405000182075542d60340030000840d040f004254203002d0080c0f00c8801040c45a40105103181c3c03101d2542a01091020002d41c4044009280310480c0482d80c09001000e98400c42641d00031100b41703040b481d5000c804081c00028032880c0e02c04041d0003000242c0d00050100d40c0c0185204a200c0d916089204a0b603820a0b0300f80d100c0c0b0307900242890f41c0400090011180b211070031005040d0f6290019a00d000040451841d5042000c400f405900c01c150b0200410707407040c00d40c4030051059643e010740a10740300d0f0031651240324480e01d1041c8690040010b024801c06000c1c1d035044550490a916000003845800b50041c040b0602512003a00700000507609081c10410f12040301c000c0007000c802e50104a504a80365003d085621071b0314060458802d003c44c804100000260400e01301400b035040c60801058 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 742753399 1250 742752149 742752181
    0xf020d0321060510030e1c020d08010b040311060c12030a0b0f19050d030c020904030e090106090810020a030209121c0c05060f190e0a1a0f0415020f040905 68
    0x407909908000b0148540c0d201c0b44951140d5500b54100414003130040400c982c00c010b00040035054540e24071110450305540000c0f907806003012500c81d81c0480c0d03220104500c0d103205074000035003608640c222045c5281032a000a0030707228041c50649043e2901c00200f02501d901c00e0721100071054403083c10025515050700c105880c50411034402001ca50502c0204035220010f02c40c00e40304510141d503030814107004d0410702e41e4156006100c4405854585009868a1840240c0b54001c2941c90b00100d1024010a10034064031030344402805445140ea4a00010750711030541304c020103809020100705500d4004500040c40d0084d000340031138109003d90410700c00140030f001810000403884040103d000428000e410281440d03d406036030751450201d20000c141900c640300101e01c0c2c0390010507240c1c00402c14400c541d10a8888a01c00300c03070080d0b0400c2d405016224840d19100740008100020f0b1415500441c042d0070500140c106140a03021070b20580069001c0038442c1d0b1240304115110303100d50290 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 742754649 1250 742753399 742753457
    0x2180907170a02090a03050f0607020106080d021c0509130501060311040f122406140907081504180f0213020313080307030b0a1e300f020d03 62
    0x800716001909165100c05602804401c1070a9000803560541d0711800c410601550b00801111812101d181c0c1566a6213000c07289107005518100020404507000302d01d074283ca240c15401014060400d904003104040d40c218690203005081003018900d44ac0d09601c581168030b8400000754541c07401e400641600c0d02640f04800784081040244004480000e14500b5030300102c0c00c1d1200741d401c910307014000021802040c0c2c000e6001902c4441d1020881d00200d040d110501c80d0300298590082c14000600d200340d81c048045040900040c0c0c560b41c04030301c0901c401c10001c001141d554030a0307003d00e0b200c900c100300a5170b9484007601c90b5015410228503031002044011811451840c1032700d05c41d80e02844076400180310140020208195511036080fa212102c0c00402511802da46d40394222824941208c821a004080c9130000441e0b420311126140e80d030101002d10b80d048408445002e2030035500b0002121020702c070b11140c00250710b54450520915209446660b0780d01442c510120318900c0641e48 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 742755899 1250 742754649 742754657
    0x20f010509030903150a090b041506122a0509190b0604032105040906120b090727060b030f041403030c09131409031c0e0705010810080102180907 64
    0xa8800c40d0b0702c0004006000d00500600c4411700d8076000040b00161206110140030300d0006401c3c441400810300c0075107010305500000300304050b034810801c01049000c140282c81d06d0b2010745080640348004078014504c03080010801401c544039000585840c0c0c0a41d0310003105860b9080b044c0c2000000d101d0281c020030300f01d580c0c904161544d52108074007120745415801444201c00c507003480601510079a0003a0a0040c0203121150b141d090801c0800001c0800b61000d001031804a50240070201c2ca01e000c0d10507490104a4041c07d100400400b03078048420702e107846503103c1c400560200400e010314090900c0e280c0c200c0050030f00e802c1000c5030401e0308250010a800810500c00c1c1000801c0c115a102a01500d0280b0b0209506000c40c0040a0502c0d0103010018030b40308002c00e144020006040740c003443c2c0c1d0760581c180004034808044035208170380244142c1c400c6e40c043c0701c9503004408080d0b104481c80b1107800ba070364445100900766008409407120410502d02c0b40710700c3e46810b802040d4826514a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 742757149 1250 742755899 742755907
    0x14010f0e0604082a1906140f040224040f0e07051216090810060314010e120c0c0a0315060b090904021e03121e07033c020f01050903 58
    0x607226038a22076520110351028090711300c10010420f90134404524031020050383c101170044680101d19503070000d002c880312480c05a140c940d8201e2442840c0c0110ba20203640300b8159140d40c240aa2046042011032000d240400c0c0000000b6102c40280302603d011504840c0c601d1824102c1520075202500c40014030000703000640156810455856004501407450220007a12043c02e80b980001c60b0040707101400b9500c80b0a40101081c0c1084084a1143d2450f108011078042120700320f4030010018840c0ba0031200c0010542004c05010341645e082c036805a80146000100055001c02941e0080750000340000c119400902c0c2c610880700104120700300c0c04e15004a500014094803070080009220340700f045e4400c002c2014006a101d00d8100182c1100d00350050030100f080140c2190711391140b0403600c254003140d001c1c0304074143d0b00c6095140e150404888443c41840c028240b090180100d094050f22030750180300c0d05040200c01c5811250040d022240c45212250300307562008ac070502807684104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 742758399 1250 742757149 742757153
    0x6070206070b071803060b030c0f060a0302031b0c0f01180230010c0e0a0b04030f0b0405030c0a0b06090708010501020c0402180604090c0207090603020109150c14010f0e0604 76
    0x50440390800ea00464842d4035a030303251400e4500411031a00307004000038014000c01080311547c40070034040c10440c202c510b2800b41c503003040f154140868410381c107c0707810b200114486020760051500a810250214030500307203418051802d80148642d400141d001911040c4410003c1c0304c1c0d030144803c00003c00340080e48980120b0300b000020807102040c5d2510049890303620100d110540e086414160080c8072140840000030025000d80008921540b0104000a370790307001001264122680301304281d03100b0328a82c460f2000c06100030700c1070b55240010010890380a00900091022600c50401c3c0340143c2408814041c2c0f0b504010909003e100031540144251780e00001d2841c5c0e0301008940250b9202102c202c0c00b0040c401c2c050050b40c01000109001c140441c42c0d0304046035201543c1c2c00c90b8a05507680c003c120a0368150300c00a4080b4a030350109204c1c003280423980c4410546079060418080c0e00c5071b40c8105207005004c48001070b90b5540c602e1003428040a020f03002829030039030f005144500b02a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 742759649 1250 742758399 742758409
    0x30f0918096c0703120b090403080709090e0c062d07060605121002220b0903012a0c060204122a03031409010908030a08091204360207060e0c060702 65
    0x4030002600344500c50761080308100898006c410b100070080c00b00e010782e080c50700d40580105400d50f40200420840c20000c241d084892203020b40c16540240109a418455002d02c040d039030121034848040d0070b9418035640168207403078500f40c807514240c0344103948548074180ba104481c102d0f04041d1007505000e10360002048d000503040440d42c0c0f0a81c00603505c4094051002000070383d415510003021456000145107524440501203a4009500034080e0034880d22010b041120303e291001e0030190301d208a5039000384298200741c1402d100381c03030040c68551100b20040185a044030f00301c561507035244c0110981c5140c0400303078903801100c044c49a00c041c1151b0340030b4041684070325000306000000c503441e41c103684181c0000d0b000780346103c283d0760743d690310034801001c43c10110f401812910401180700d10f501c5294088508407100740d13903007244600b8002d806610170545100b8201211102076210800800240b000b04a03080c89418009401d1800c0416a4103205841692601c00c600600165001d40c480b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 742760899 1250 742759649 742759657
    0x120a0c27080c2d010504260d1707050708120a020d0c030c0207051c2301180b0408031801020a030207030e1008040803040c08030f0918096c 61
    0x240c1d803e54505214000100d03814016a132207100c0c20a044003001950132440190320480c00c02c0142582c202c070b0018001680d41c10409403003400d8101c150000501e4240c4a034001d410f20501c2620014507041030f801a940c84040180c0d200e4000075800260f020f481c040d02e00c01d01c8202da080c0c0c1070901500c000242d010b034072050b89115190086400e0564184403031030111094950303960008108001c81646070600140506407041600f84c0d61070032100c50000c2e440d0000054603540e0007010740c2c1040c2d031165501100c0ea0006000b0200c07422034480c900445540a001034040280d41b5600181c940703244e03080c010206400b07041d07503d0084600c507200886881e8440d8071643c2c866044840c20382d80791502e10700b10246150a6000c000e080c040800c62054014540c8000c1c0859001154030b02008000c80b4034a1488003001d50f4201706070f41c041504070070003071408140015840c0c44a40e1060001001071b400410450601c00259480380480d482c0207000045011100059004d1217030154031000440030401c01d61003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 742762149 1250 742760899 742760959
    0xc01090e06270405030304020108010b030c0a0309060f0606181a03181c08060f03030c060403030e010b1320070c030f0c0902070b100506120a0c27080c 66
    0x4a6921811031103080500212100c10030b0040c804240340604000340c407504182c1d0201e000403032100000810700c0b000d40540c0d001e684644a01868148886000e03401010070f0700b411981d1a4907006480700044652013103400400594540300c00e2914910780414540c00b5503001405040e68140b04d400351401000152544001d41e4559100e003881c1c18510b0b245850210503424402440c02d04c0308000460340301030030601601054658200e04468603040607120300840c218100150300c043c1c005408203100c0d412041d50182d40600000d0a4000318003c684500300c55002c9044041d156607080015183c80d172038080c0034070800000c40f81007200c9603495110048252002802400751500080c090110380e0650400804850f681195500c00d503151100c940c2c0b1040b02c081b400740880c5180046d1508041e41128105100321414203840d540700f180d002c00400c82206180200304218440310f00f494940140506404080711075960420710b0001428500f507801c026050091b4600441c0c0795135115001d0351012081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 742763399 1250 742762149 742762159
    0x1060e1815090304031407051801030203060718051215060a0614030a02130303020f0c03030a0909021806120f0c0702060f09030142030f02060d0905070608090c01090e06 74
    0xb40b5070092061650042d500090b01c1d80c0e13080d0071001003440002440c041124405e560121107070942000684503e4802d20010b90107400010000380e01c40d125101c00c444021003549a10714058850340800d0080c2144940c240007980001010000e40b0301041c00550301410850312005400d090890040001c3c44611020070b40320404404030f0600140d039010f071000001d159001001c0f00b5940d0074002e50b5190b502c4490005402104401032090502000716445c01200d0f0721040111440c2c241100c0096004026403091244889071022a541e507540c002c140c40392240c0004a5142419404466528006011a041c10b4020003400300161500026205660101000d83d0b46a2404030302090241c0b4042818000042d10302c070300544c40b500c440e050142c0c21200c00305041410414281860501c04072400081c21b10300034081c2541c01850110000c0000ca070a4280204401503550394480c5440403e42007032011406101c10171290074410415034200e41024030303000e03000710700d030a000d9080700c80007611450240c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 742764649 1250 742763399 742763401
    0xc05060c210d0e0d0f0f1209030c0507060f08151c060c020c0102030306060403020d050a0605040606060e030312070f17010803131203140711060c01060e1815 69
    0xa00381809840320a1000c0903012006150320700d4084419800007110445440c40c140d0301290f204400554800000f80701d8994007068035003605c0030703202180c0d2034241404024600554400300ca07494058002c1c214405d84a030800300c030262a04504088140c1c0100040202c40741001070b401c0d510683c00d542210301140f107500390b28a542c0c0031558034901241080e0080741d40b8001c2008021242c2d0000e0303494521542600d4502d50550012616480280c0300558070150600042c0054504806580445846001142d80214a607034415080c2da030b04440a60304c40381d56103400c0150f2600072110300708080e004c501440c42c10803103141c0303200c101d0005000c0a040100c002010351409006400c1030525803006420086950394032500a075903a44101c19500b800d91140d8000254440c50f101440e80440e41515924540c0001c100c0610440c0c10400c010341c2d030060490905490340d12124024480c3c006100004240c2505004542e60381540c0902030140303051060610000400010070100342401c1101030798505 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 742765899 1250 742764649 742764667
    0x30709061404090c0206180d050415051605010c030f2702040b031911011403010b0901090b071a0f0606070f051c0918021801050307110106060504030606120c0506 71
    0xc503002d10b400c541e2809140494040b04c2c0b0303800052661041c0d2580300300c80002528000780c552541800360010002c00c80c203110030b00c42401d0600c08100f680304a403406034140401c040e1800300c0710140b109c0a450595584084a05030365140c000d20000700c6a03043e041c001c800301200300c0d04000c41c0c490345040240d014552410b0440d82e50f0b8208114039440141103411212080551151030302a14070129070a203148a600d040a5010701920404205c40c442e0b10b50440c0c0c81d081c6441601d52181c92042c0c104062610003103020742500e0041c05620b40a0b040117196240400c02c1d00c1c510400141807a07105115801c200a010381e1094105c9a20b158008400000c6408034504a85820740e00c0110140c0005030b00d4980100c3c40c1c1c00001c42c01201c0800044030612816080700c04101d1003040c0c2d0b80c0c0c02c01c2d091180c025070b0175405407000f150800c504e4036008000c0c24403c0340b00c80c00c542450b0003090002d14001070800500c14139024100c0a8403101e20481c2126049680300d01b00401144140341c00707510702240320702e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 742767149 1250 742765899 742765937
    0x806010b09191806080709200d0e060f09010f060308091c020406031103100b01020c0d0f05121b0c030601210c0303051b0c030604140109080c0604030e0603070906 71
    0x4000d2030f1500c140e251020b45419008090600c034020321100d8450440700080c03101c100d02400880e01000040d801da03010400103444515400110658160b68485028401c00101040101d200f201d140750307100308a00b4202451825102020314030701605003030160034008a044042110340201c0104c45044204c040c1041e480005802201e002c2d50082c0303011400420301040345100b51200f5002c9098625884031651a881120016070009005a021011b1031099050151202100134002d11074007580242c42c0c1d50b01450542c0d001800c2c0420140070a40391034544170500c148454181050141028400d008082a9181e00c1403203020115221540154621450000c0c140404c940200c42040700c83d4403800c001c0d05e0380d80b11050750401180701c000e14802d900d40219170519403401c000d016081e5502c0340d0701d82c80c00e407081440b400c1409541c0e07460807c001404400013070060a001e0400b400107803800c0e041c00380117081da440503907000d29410002c21400c680c0c0000e03020252802410151441250611040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 742768399 1250 742767149 742767199
    0x307050910080604060f050f220201050909040303270f1506080d03061a07080304060e101404120503100608091507020a060e030415080604141e010806010b09 69
    0x20a1405810140414000260405039109028406c24042a12303090f00c2c0d440460400c41d0700080c40038650003515240c0b100041d0a03c0003500514040e4141706c00c8000141e00006c0c2960200d01003507032410b210240c42c2c201c5030400c5820b00c0c0750078005103c0405445691390b62602c204001e10702c4034180c1081084400c00d500c0500a07200c1c4d4000c41c0da0760107003000050000c140c81d0040150294100351a803074141c0c08d00f011107202a40c021900350643c0c6942d59000090001d40703000c00280e0040052880c03c003200380c0304403008252814501d41c0e05051600b0300110030713054500c43c40e080000400c200305208082c01c151034121625454a81c2c00c07079450101540c100030469402510140c4101d081c4903c0583c00511203410074001e041c00c0010034490070303038541d0703d11640c80ba00e045001c4000700740040a00a0340b6440e44003001a101080000c03035054200030480701140d20341034109041800745160b40c80d60a0041c05401520b00805681d41131445101c0705008041c4824454090780000fa103001c1c00b070460760 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 742769649 1250 742768399 742768409
    0xf1e2708030406240905090712020d02010207440304230918010b0f09060607080f04030c080d020f0613061409071809020603010b0304020d0f081c0b0307050910 70
    0x20003080d0131495941030303841d0030510503c002139045c080480c1c0c2440001c18070400300c1e0100003a036030101440350f00b802a0780164110680c154012030000264420415140c00c1d1040369206000d607080101c0300001007450300008405505002e00c0d0032014400700000101d4007a200c001c5480b2020811440b00350421940ba08809904421100103009050369231035089201c181c0f41e48020702c2001c085506101003000c00b0200c0c10b03031140c0048082500360418500030a246806121840e01d0208841040480b56000350b00440716404054010004580140704000100070301d48003901020100d060700c1e550700e14006d040a070f4051000c00c4424200192540800c0300e8401d00c0302694558500800541e8542c8150700c00d694950058422102130000c03240b0600849075801840780c1d045900b050090b03202e41d040100704981201134000c544010629000c04116500d12a07c00c0030b58449000200d034015a030103c81c10340540c2d0901015a00d140d83c08960101991425900c0b104185d07101815090f4000c050b41c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 742770899 1250 742769649 742769681
    0xa061a0414210d090e280b0102030d02070c150519030c050c06070f1b080f030a14092a010219061b02071e0b0d0905010f1e2708030406 59
    0x120010690800480000c80c0c074180810811651902c0c0e000071b21580b075940e80c8428148103164600c24501030703400003200c1030040c8100c0c1d0a26115114000403030744405026981140104000c01c8a070001528000002600345861030400800080011011045001c07050502d600c8101440c01d444c030038800d481804c205841107400b54100701e080a080c40041c02003900000d0070441c221220760045420341e81400307034030003000d40c5840401864407110340c02c050007285115840c0d8a01900541c0c40e400c0042c040c14441000e044002044140c403c81078a0403c000e6011214030003c80c0f489a8000c180c1c00b2000d1100d160003c103030000e515104004025140c82c0c2c24581d0301d00c841b17100aa40e40003540e1000c1d1078a032403e070b84100c6003010303070700004000c14488e540c0100c0d030400c0030300400c0e409508484000d912901c004a1151103001000b01500c04540417100483c2c0076080c819001030950043c200e000c400300c000d200c10310300d0b019042c00820701081c101030f1404c900000450104440c1d980f100c4100c0b0020a8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 742772149 1250 742770899 742770913
    0x10f0f050f0f03041103240c09030303040c2d03030e1504090b0909061611160b07020f04110a030e07030203010c02010b100f080703230a061a041421 65
    0x86007202d10b401c00c1d40c0a0701d0502141010304014100010603941d540c08081d00411000c121034074042c01906c00408100031600d003030103010004c0c5c604001450045104041007803083e410302402501401c5050004101104c3c04001c444580314100003d1003030702e0305458950000c00b007610120f0b082040903c0300300c80b204070010b40043c202e52903600140c81c0710000c49a81142e500d61130030890703072110150742c0e041c0407120405004240c0c5000d400c400034040c550f5810303030b03000c0e010085464440034071340e03030040440c118000707060021440d1059118010b00001c0b1010008000c42080100d0140151001d8800749079541118064002c030030840c00c2e000b50b034010001c0c0646024090020302805000310b049004400c486005010340d0f000782040442e65143c5e966440a9646180e0b04401400c0e41c03200c00418020750f4005041c0f00a10200389901c00c403010340300410894a440e0001e2036071820051740060140061209000d0442401c0705444604d03811201000c032038494210388400031613102c2c002989481100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 742773399 1250 742772149 742772167
    0x50711160e090c0d03050406031a0907050a02100905060415020a0e040c0e1f110a120e0409060515130b0d0609051227040b091f15031d0c010f0f050f 65
    0x60b00500039507230f0070f0350140f000d010451258182c044020b002705070b105099000050700a8420406000d01490a20440d50100c00d002d03055001c4509a070001c0d43c0d283c0003e401c000520004840f2011a100d00d0542103140c807281180080c00d10f80e6008030036108039243c40c40741c0e1142d0700c0746109641c103030401041d00074115141090310b10703c29501014140840e012820410340c0b2100400c004140030b03000501031202188250301218180405080264400d90b0f40d0284400302d103541c460341e03114181101c05c2007032200c8040c04100758100c500c48001411800d0100328034050700d42a0000c2c1e80035074452404140a0304a14000d030034284240789003001c0d1840440c8002c185100c0840c29170134081404584891480d8840600098030034030140f8030340100c680c8000c2031a8003250340d501c215601d03211411a101c107440c0c130440f204510344540790703600081d01c4043ca00c00112a01009ca10b41c2c0840d50000e1011010b4040040c0031204141c00c244203105110700000129801001151102c01ea84501c1ca0f81d214021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 742774649 1250 742773399 742773407
    0x6100e130f0b1e180705040e040305030f06030f3f18060405010917011e020a09120c0b070317180d030b0f0607140d03050711160e090c0d03 61
    0x42082148100344840e0f1500ca034142903d50440901c1c0d000d003000b0071903d8507020f059403121001e8203c0c01001410000000c7e403901ca031020303034023651180c0e4070599241001140021488009010a4400c1c6c20080ba11401034500081c2100c03020102004e000003403416950b0703d0f03981482161514110490704803846020b0300410014241808003404880d02c4035424420b00c1000d001d1805090702041042c2300c00d1058514109000420058210005c03a110f41041221021101050361030a00342c5e4002c103c6c00561500034041e0809041c42002085c0d0414190704d0f8080b010000b0701c1051a11200010134909151042d510704144021541c5681c013142009504c42064500e5204201190300079003000400840c4640501480ba20b0000c2001c214050080704000c80340d070000d070040f101104014180400c2d08014814003004e4440d03a107001030103240c5414040c0605a5108100315030785c00c500e40184106000c0c5050700291200366490754901d6640350707810351600382401003540d480780155074001c04045d44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 742775899 1250 742774649 742774661
    0x70203031812010c08010e19060b03010518100504020a020f120702090c030f0a0b040e100218150703030504020f120106170106032001022805060f06100e130f 69
    0xa44a00c20358582c410151802c0310803041d00c3d600010750300001009001780840001d13030040a0a100182e2007083e007182041100c0041d4015028030001000402840c900050b04402c11614804a6901440d06010784c200c1d5404c10300071769100d60707400700340680502d2007041144000c11000b411244038400881f54941142c010b41c001304c2c4071b00010000a41e09a00e084140d070302811300b80c0c840c4843c0b5101c3c09502c1c80503200002004e40c0142d6075550035405000c00304144003002281b202c0c016919280002200f402c4c00884000705d000e0840c2804c15a00d0000400403101426098500003941c1e072124400105600490f81c081540300302e0103020096880d006500c10812101e1b202c003000000c040e100b5000d426a449484058031800300300c03044410f191010680c1c040042c005205030354007948181d4030400c1c020000751489419010303000110b82044420400181c0202c01c3e8000c10409180000c0026481d580314200601044049014010251148450300e480d042c0d01c85828841c64101440e01c40c01008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 742777149 1250 742775899 742775947
    0xa021c0c0f08030402210d140f040618050f090a020f1b01020a03050108060106050904020f09041e0b0105121305010e0f010b011d1f0e030703080c1501260307020303 72
    0xa404c4000300010401e00124030461990760103001f8265141c2c0e0151404c0a404030070000381c0d001040820501400e038070080c0702034070454071000d040241c400355600b070340303243c90300000c0c0500030080284d02a0b0b911840391950200f42d51001580d56912004140414020701d07840c0d00b000c009180704031030707105019005402a5422030b0340400a503a600c1086540e00c40f0207115140c0883d83c208980d560508140d00200180412014440e107000b54503004070b012200c04055000c0405840340000e0002071441c01030302142c01003481c10368100f242040c03049004e00310140c8100a00700c01c51401900b000001c3d0065440780101106072150240402c4080380070702100182c40d800601000481036101c83c070701c00c0c0400210000303041c0d0058001291071060154507a8170104042c0020920400582c1d60304001c15001f41d4410700f02c0b0350b111900022540d1620171310441100c28580031078018017001704d02c4c103140380201400c215407402d4801c524800c2425480781c26130103500b500000424a0340100d4090010008007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 742778399 1250 742777149 742777159
    0xf1f030524061504051302040f1205100209030c010302091c03181205061303090b03070203071505041a130c0905060a0605030f0112020f1008100602030a021c0c0f08030402 75
    0x56140410000300b8070b10b2102d01001800144002e0115040c070508890006c918038000528261700e40b01c1492082140ea480b0032151441038010a0420400f80a10600b1000461065041c003540c20000382e1110302d9000c1190401d40d0215003081300d940d80414201c285080b034040c4140094407418010300c002e00580c5900340c101500f110015110004090719180580c00c500a441c154840e503941d100303e010340d40401e408021200801080110840008600444440c4c0045d0364408280c1381c1092405440c46c1e03003007c0c0030300d48410480414062141c1690108102c0c4100c2026a54a2014103d007640303c603014001c1d0308010008240040d040e80998001c02040703d910883d280c1c0d40400310b4913884215500c504490740301d401008859800d420004102d407000b810310391030720a044007041d42c2d01c1c220040c2130000b60444d81402042e50444a42502030080c0340302452410201e904042e42d00d00c1c08660f03500b040d50b100310a41c10105e1042200807041c0c0d074000107151170724400e81400112a0000d840a034030079 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 742779649 1250 742778399 742778401
    0x62e020c10020309180c120f0402010305010909330c0302070c120305070b1506030703050609060102071511030c0a0506100b1602012106060c0b0c030f1f030524 70
    0x110340004107031403813420014021842848091500320b09100003815110a01e40284840081800c03141c000500c1402c00d00c0b950011450503000040503108182e200741511407500283c04085140e404442140c40082412001c090480c044804040040401e00d08081440c00f0348407102e20754190000e1150078010200510110346078003812500c0d40e07c02c000240032840070050b07100000c141d0619151303c07049122410707085844000c0815400d603c12100100001d640e1020450f0910382959010340020003803004000e01c1703003440040d00140d807101d04100706000c0052046001c640007041129403242c4048183c40c0f0412040c41c0080d51000c00f071728101c05a0301c90f413901291088017003003512246413030114007012000060700192050600005030f4071628160000782e03140c051243c000c1d074005000c141c0c3e030f00c005040507007031450100300d000c0c01c4401c1c010810014004078610b580c1603140c2007c030948070f044000e41012003041410640d40d00060160203010000d100001035a030ba00820140d0700b54440e182 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 742780899 1250 742779649 742779679
    0x4050c0306010c1e02040f0902101103091309052512020102030a030902061204050303070905030c1e0613060201290a03031202070203030309010204210506062e020c 72
    0x34041110254000345400c070030b800c00b1a0011050f8140380d50500000135020341d003500450151941c81c1910035041e5107610480003181099202d04030042d0541c0707040c80b000036135081c0c0180c5034425440c045c0e1052502c0744400c0030942240c0c1c0468ce809601c2000c48414101c8850f010b1007441d82d0041310f60b051280d1280000f000381491000346200390341640035600d4540f144106400804155400b41d030840d500348140d503101c0c0d8240b0219402113001c1d000540d1a80740099004143c11100d42046020380c00c0544040d40307684a0003803034420700d00030754400480d00503c0c81c045143c2c1d010300e0404503200c5400f140c000840c0f54065101038140381807518840c0948010004c92440c181c00103442c0c541204442c14204042449440c25140011031307000054035120140c0c0000f891500161500301c12a507002808000c00643c40c2c031034589c104880310540b81c5104440d26807507103807480100031324001c1d140d6070344071f0803202440c00e45889600d8a209401c641c0d44100310000b580ea1500d525501c0c016402d02e440070720 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 742782149 1250 742780899 742780921
    0xe040e0705040612300503072c0915010c0609020418080a020601060906122007050f06150a140f0607061a121009080c06010e1f120f02131a0405 63
    0xb20600484103960305d40b4550007044449500080070b080800050004030a446064241800d11200d0000b03c004200c06444c0c0400882503005800d2408004198600f06011398110000407030480e0030402c00a9142c0c42c1d13001141c00390003040d100f40003051044141c1c404004109002e0300c0d60300301550803903071240c0e00c0d02011759140407140102004a103884020800d03080301904988010783c0b08510125403902c120f02d8241d02074100c2c000882d0290000c1601c905201c808000107a482610350841d410401011000300300303030003800d0040400304407051180c506c0e1521120108041110003516040d031f0f0360302e54104031000b041040855801c54000c50100320070b601c2c045568824000c1000003a202d8443c0f100624801415903010403200881d00b4410b00c2d031181418020035000702120f0802c001d4916000415814541214144c19420070108105000b40c01e1440b1386145035036070100d2254034000c15230001aa410860b103100380c0c0d0385414460b56141e1919070b24a00030800805880c140801d40b21032985c44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 742783399 1250 742782149 742782203
    0x507080a0809060a0908030406050c010f180f060b0a030b01050f09040b01060f09030506010905010f21030e040b120c030c0105180d021201020d0213150e040e0705040612 74
    0xc0e10000e0700b4810109103103002002400014001c0c140a5070181c0e03502c9145085401c581d015101089000c54103101680b028000d16500c01c40d0a40108070346c5240010300741d521207070703000060701c1504510112000c01c59160720029103024014940480c682d640c0c41e011014010074050745000f01c0c503800d645a861b040c841d4007180034591000010596a08040b41110000001102d01d0100005c00704000301103401481103a02034980050003007003e605007201403480740100e500101b265004603030218038902124220050b030070742c1860507150402000c0700007000703803048407a0b6591000e10128418902c0c0400501105c041c0c0c0240c050700d0043c01208010f6031680160103080b440d1f04030b40c0310741ea10f0030710b4020340c1c100007144024410492108039a440c1800c80e044001080e5a49500168030326400c0c111280703100003071012100000c4111030744071004000c40b2019003030700e0050703481c0c03040141c200c0014040381c03000c0d00c8003620410405540c1c05040381036441d40501502c0119491455a1805005007450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 742784649 1250 742783399 742783403
    0x2215030606022a01140706020c0106080f101109100c060c030915090512120609010e010305190611070f06050a05010803071104090606060f1d01020721120c0507080a 72
    0xf90400800c048640c0032103106440c0c0504100c9030b4040b4a501141500103012001d00410b0010303141c51210340191f085030a0b40d0086e01043c0c0c0064407000c514480041c041100540c0701c40041207880400101001c80d00820010320b50004010725021a019031101e013004207a0300402c1c0602072150703e400240c040300c00c5010050284410f140a1880044480d00b007010b41030312030f0040720910102400c1304481500421010700c0c0d800400707c1840400c0c0b60113410280500f00300011305145502d95070700c941d0b688a8011402c40075030301c01c04000003840030b41c0e03200b1032120000600d010f950f0401480c04403240801c102040700c10900c1c110224412460900c80c5a0513591407200031854404680c91320122003c0503110650722540f03520b05170707000800d58001d00b0010b0000351960041d0380c800400c054800b02608440d00d818000000301200c160fa400903000e0102ea0408140701544000054001d00c001c00b0140d010745010442c80d141c0d4000c5902c0701080500314001c1f801d83c0c8406071640c400e203884080c12500 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 742785899 1250 742784649 742784683
    0xb040515010609031403070828020610141f020d11010905060601120605041503030f020f070611030d0c0c031b0503030105062803050a0f090503070305221503060602 72
    0xc10b04c00508944100460420354104a80c2089071a5681c2c0c070ba40d42c0050350620740580034101c1c0c4140301c9900c60083c000c81d410340c0081d00c81880c0c41c209484801065201d820100c40d92203259142c00e03110140000b9042c1d8016040c407260448128000c0c1d03444500307890840010780742441001d00d0f100c3c10710900ca805a40030000d420f00341c03074880044030b01d203040000e2903600658410000915684500c641d00c00d41d003e4072050400c2d280b840c1800746c0301d40542101041950040780c5143e04581005c10864150b42e094104819800c129241c103518600130074840c05c2040780752669148507250001c14000c42d0034420342d15040300301e10801040c02030301155000101036500c00c1c4018880c0b4549940070300b108158003900300c000d504209141c032180100710740001c004290394405005840c0213901401d0007000d5210020702c1400d445a42e0300d640e84c45890380280c2000004110145041c0710884004200008195020052a01d42c000200f0544002c1d0b003100c04a49003070800501c841c0007240b600400d0400400e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 742787149 1250 742785899 742785917
    0x3010f15060c15200d06030204060e04050a0b07030b04150e01050102070b040b09010c020904200f0108010e06060c070b0a0315061d060405030102120a0c0206060d060f0b0d0b0405150106 81
    0x400100070b8400c5035403031a104c048040180d061201214003070404040380600c003082043c5140180401c4039003542001191404030340400020410000b659035049a000c41c1c0300d0301c1d56503024412001441c46c00d81c169445424041106820403c050a40c425203a00104c80c2d519030340c2e100d00690340c0708103920985280c0346040c44100014050000601009801810410201413607940001d5101074225811035030070510604c000121818821398028001c01540c0d458a90502c400c0041c0403800c05109180030450f0440014601e9144c880540d4800700c0400c5c11514800e445103401c103101e0b08074558500003e81b070581c40117080752510041000710782d00ea48918101070120082040448901d07a103e54000f0303010400041e280e20244010840b0164005a40600381031206081d02901d0318406c52408660250003444159510030b0b00303d042c05a0b21210020f2808034410600b4003a10300020111f5000b0202000303c1d00348240d0707600c0140310b1445801500c40c51600c59a05400c40780c0213008003400122200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 742788399 1250 742787149 742787183
    0x8060402041d10050402130903020303182404020409020303030f041401050103020108060906150a020d0207140906090a0f060b070308070207030302060c0a031509091a0f04081803010f15060c 83
    0x150000303800c03c6c006030190703d61080100c0f40b90150b4449400450041c2d10010420109400420300140c227a840c041c064000f410400d101d03500f422050500141c03c07602108041411541d41d039000c059001d82c0501900d4076403a000174942d0502000319130944601c84c43c0e031090110303000e040c42a1410b0b42e0b8142c50f65911500d1720000c0c001c0c01c40b0b0091040390800900385441c04800c1e60140038102c21034141c0e00600242c82182c9000b400c0103c1c5034481e003100110748009074090359a1450180d03100000b0381e03a07484682d440c888550701402d41c0303031507408d6060b18000300460600d0b2141e0003002414003e44072030810781c43d07904040340e03528006d01c000307001a048100880c0a8000f050002e0424025901d030100b190118800510305842465100801c0f0641d2014410f0400c00720040c1e413030303920281803420103292a008100c1c4501c0e1000038402030010000041c0045000e19403401e000141402800800c80603240117404002080341d1002d104001e0050704001820620402c004014682d2042440254102d22 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 742789649 1250 742788399 742788401
    0x302030618010b0315012d17100204090903030e15070f0c021206040302210f1e1b0105011202062521090f060e0d020f0a08060402041d10 60
    0x1c421041e00075500c0f000101e50035030341003007544002c010399011400759500d0003c1150800001c41080899402c086152041040e9186080c00c00c842c80d81c2c82044140380030f07000395401c20b00c1000c042951144081230229030020721768090000a4402d442c101b1500b2000d5021550310300148000884032003600300050001c9110302010110f0756440c0c2441c40d018825940015100d0428201d1100c1642c4282d080200349a4108066600702140c1d1081540c080f60110301c0c0800c605c40d450f0f404030340c039200040344105602d01c000025442130007404038948030034000410188041c5581e2169000b91709200010544800840150180560041004d884d1180b403503a28418507450000a40b04100c41c00140c17004521100d240428450460f00008072074090007001900c0e64916030000d0010b5141320006100050b005003200000907000c4030700080d0010f052000540300e07184084c072a40c002c2c11a142c009070101c0001116070240b8400c440c2842241011002d4001c4c140d502084c801d40340e841118404840841d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 742790899 1250 742789649 742789681
    0xf0c1e050108010909122001020409020c0c0a03030c1209180506130b03030405040908041221090609180e0f0c181b070515070c0b0708010503100e0f070b0a1803020306 73
    0x14104800d403083c7e410350020b82240c009078411240d05030000340c010001300c41848000240ba804440342c080c010b05580b00104001030940e00181400b0942c6050b402880c00341d81650014580c81034003003200c2030342202d0300000d0501610b07114003498562100040c0140d40740584140f005019000710f040615010801000c2c10300a20280e805030030411002c208655a4011640954003450300e000550b41004035403141c0c0705042e5521400c10a0200c81841320350381c084000012581000406071240d910760808074018840311035411414071805945100c0d05401141c1d0b590860001c541a649400c00300340d55100180c1c0489442c41c3c50340d9041c0095401c03d280101a01184c2e0040c0e0440320b40c84050f80d000744035514265441404202843d89c0c00d0704002551510b20341c03080c0d07a8a04090b8035450180400c1d6500c440701d1940301525140c5911040c1c0410410240340e06c2e0702c500040724112643d03214018000d6011088200001d14864650407004010902c003108582e800303030082410380e61b400710518092407 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 742792149 1250 742790899 742790927
    0xc0b06060a0c0b090c130c02060a27050d1106060603010324021c0c031a130e0616020c0a27060b03090c01020601081203040f0c1e05010801090912 64
    0x44803650b180860f10609800348180b200400902070203074480200051030b4030801d0603600c1e05040452a1160319030220340f558000d1114140800c85051b902002c4102d2211050031b14030320210207207004280900000c010031025050f07201e03a030301400d1261506894500c00c035180d9030801c10400042000403001c04980c0080303020400c203034040305008520704059a200017140449000128030600b40440d00d40310f4403214a90f141820000090700406858003840c114080d20b1181c4003284500000c045281c020000309c5181e24181c1d0300c00c0c5864545c81e5404030300e0024400042c4901202a950360600751000300079212a243d04c032040741c0100d40c645001e4450088203030340080d120b400000c0c0e200c0380e40001e540111940340c0682010110000020303d4150160302036080340e0302c00c00520f2000d1200c84102c03134029800210ba81c1c441c1c0c00e60b080030f101603810703a4401c1c0d14840c8200c1100280506030711400003600d001f643c4580c00350b680c0b9065001a210b4043c405000d21851030749000322503005922500740c04e6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 742793399 1250 742792149 742792157
    0x705120a02070f0f14091e060f0307090e0105090105010302060304080705031e0a020d05180418020d080c1203061302090d080c010e06011703040b0f0d09210c0b06060a 73
    0x1e0f00c0e02c5002d01100801c1c0e009101141000c0c4080c0903c06040003109101c42050320802560f10302620700e00030103007603440d00a900d969114081071690700d0b843c1200800e40c101030100c035810340d070317983c0004010501200f98005a5291070f0201c1c04115040c0525030490b40c004101303600355111a124102c0660294030100c0300d038072081181034000000380901e64502800031103500e86494410350040d080a070b0789204c10741000030400814040c840c0092090082ca0001e80b000100c807140051444655100002c0c003a40c0f082400c010322082203038080080001840388002c0e40e401001c03520680c0c0345408161002c5034041211101400348500036405060802002008083c007c6150344940000b50300011910384e481e510b4011500c00108108807039030060691030751300343c403120701d9100c450344034007881c0100c000245000602c0d144108200e402e561401032015402c121030401442c0c40c4a14448040c1402d02c8252800313800d280c03550042c002800c15980040c4841215680c20040050640c030010340d80040c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 742794649 1250 742793399 742793413
    0x9010809010b04051e0a0c050301150306030515040c0f030b04020906010c02090f1b0910030b0a170a0b01090c080f060d05031c060519050405070c06150e07050705120a02 74
    0x980e649000301402519100081e1090106246445c446003400512588000d401c0c800780c0b50b000c0e1740c010112030456040c06035401400d41d407404103d0107010642d002503d54030030000610341c00036540c0001d40c040c91003100704401080c1d83e40c4614641060318400500707149105000035001d07041c107001c40350340f244051420f01b0741c0040c6640041d000140554094200001e29402c00060f591002500400600724403007150a0040840019060442403041d4408054aa0f00700c44003d40307030094000007900c009290210f8440701100b1566a42c03050140594070761b0524000026400d4a51143c0300150b019070b51406c40640d40d110100d004110040e1025410840c2c48900c20045002400540883c04244140d1041051b400c2004001c3e1101380c1c205078803401105908914000030136003024115041950085100d50702d40105452440c00100007038402810245403503508001c03030344000e096915144014000d0b8660140803121805140c1008005a02540241c00c041c0b030b100b030240000b500700703104648407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 742795899 1250 742794649 742794671
    0xb0604030b04050109030f09080304300f12030507120911130204050307080606032e06120510050108030711061909060f081501050d0f020c0307020f040b060901080901 73
    0x1410782100c09640726592011040101070780587e9880c00754550703141112400d418140748544070310461103254003200345500342c00308491900088640904000c1402c1002188506100c040d400604c0030031900042d20419207105140170b440b6a50140480e82d0b9540300c804104240ca900a01e544501920610511845a1225920007080c002c0101402e0005a111031900e41490b25103110764100345407542241003000016140003a60081c01e0130010301c1095034280e10b14040b41d41a40380403c504c0c802c4e007041d4020698a01078402071034924440c40448000c0c02c02100c0c188200c510030b02400010350003c114a10104a0b041020242680c3c02440079160038000543c0b45e150041150103240801c10b0b10004000032500080c003110a0045805c07c881c0900d41708040440c02c544c5006d09505004003c43c240c0703040300d010381c84400d01b5801c09400f1943c0d80500f0340b40c56902d0708250304c228850100c0003801801030500740660348238000081d2029007004105001583e4030800100030841f20340d42d9410003a5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 742797149 1250 742795899 742795913
    0x20702031218091006020c2b030c0302060f06030c0d1b120302060901020306010f0f050d06091a01210c1206060302030601031a0a050603060303040e0a050619030f060b060403 76
    0x1000c1001403490007055290400b80f141440780104103c400000c2060300304605078012854a000351001ca40d040302206101203203400003201040a02041052412000700b095000203080d0304c143d000e502110515921810549001c04080722610f40540000941d0802030414001c041200780c4a00700841c071600c520421884001800c0c4e000800235210360044a061640500036980c100c9210802949146840300000e006803640c01804c1c000c000c038075600c00d1012071183e801d1340c155801d0000d040c00740b0b0341d940d84281c002d0480780d0310b0056000519040001c0d42d41c001c0d0300741c224a031012001244101814030b440c0c0000c00c0904116014002e092002030ba031501c11344148006001036807001a241d003441c01c001030485215440c290302569100001f000d450359030410b90400c451040b01ca1380c5c0c0d2590f40074080b90440c022035100c1c402010b81c040900a28404a4000701c4c45920143c4210170030f0444001c1a02201e07006100140142c403074606240d0100795982c00250440d500034100301e140c140e40c0d6648030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 742798399 1250 742797149 742797157
    0x1406040c0b1b0f0d1701031a100b070b010906081609150305030c1b0607050303132306061008010b030c07030903021e0901080309011b0204150608041412030106030207020312 76
    0x15550071000b0f01c60340b06074121a250b1081c000b68650170341c040d815641e41c0c0c2160403185150380032800c84c41c000545103291b0300c41e003d00940f41004260791a0b0f103061030141010070080c02010305513418030341d01103941c1000046551100034481c0d1401c046501e040c3c1c81d00000c10700c15407000100e2071029004800f154007040100000108a0001c1c03003400351424602040400754681240f00300c004000303030300100e00c000040e26040040300000c11081e0340a844c4c112815407828510140141006261101205002c11035500c169426101079218096003a011a00041e0034040e42701684011300104807980a014003402c04107209041214080c0c0c5c40390001920000e000c545100800141d01a01581e4200625045e004100c02401141424502c0d400a032416a506000e43c3c00c801c9032507410001e40d5a00c3d00084142510000700742d0740d03284c546000900500c2e0844041e9824039003640122074443c4006408940c0030500042c0c2400c3d6420240d007140650f1052a0a903407510a12894800ca030008070018 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 742799649 1250 742798399 742798423
    0x90405040f020a260c0a0611070e090a1109040515040309030204060e16110c15070f03030b030f0708190201170a051501020a05102c0a1406040c0b1b 65
    0x2e07120f0121600701c1243c14401c0c21321080c0b065046008120030a8451801d0002038840710304200f400201f102c0c48881c600501d680c065841d40c1440418814401008598440071500a05440139289068002d00c4200c01e0260f90080283d40605d40d0b801d000100c0c440300c0380d0094480d107090036060307549030002010b542c5280c0060309209142402d124890b004218018001e800c0c504000002d070341c2030350b00c66031500c045000c1140901d11440c4c900c40b4254880c0c04858074150b2041c01c0320404040e44c14010010310001c200207004e803080e10304030854480300107441c0c411503460038020302c00c81903a030450031514000a01c0c128180503070194441180e19107030f00b40920440301c003040001c9910384010b0011103551107604140c155080044801d000c554041081d8a052041da24040b5070303040c110303a43c4080030114181558061415098109005902141140e1140e00070844d03405211090724046840e40e4041c3c400401044038803104200d80803c9130082c0040407007841a0340d00c40600e12900300c0c1461040610 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 742800899 1250 742799649 742799669
    0xf1b060106030501050d170d060308070602030105090c040803071502091f020c060a1d0d0b0a02070611030f070c060b1206091c02030a050708070f14061605090405040f020a 75
    0x14001e05502d8403410b070043c001220074940ca55005e0f00c4d034a41142003050400c203045000115103240c0e00e2907800100055038400f00d83c0781c2d40c0300385003050b00080d0800c4c00741d94456103a40011610848a900c1a50241c43c1c03650082c2d071800c4080e42c0c2d044440700801340100080758007480008103035582c034403004069001001d0008902041040c009080c51740d61030006114100c140800d6006c10b0340003501040c4c28000f00ca000704400c030600001004198510001004101b186040103400c0043d50040d00825200b11028410034007000409503a41c0400c840d00c0c5458103583d000075440e644503e2002007003c1c000c01d00000e1003140752000c501003204502c0400082c1d80041d0600041d60707010010003003030158408260402c030120603c0252070303224020a910400001080c020240b0103050100c80c1c01075409892102e01c1103261905401c2d8404901c4020f03085d0051800050b01c1c0031115945007480025a1f1380c3d580361010000c204002450050000d40d00d00c019900040d005850f620a008058017880d00703 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 742802149 1250 742800899 742800901
    0x815041b03150b011d040e10020c0f011b0503160c06061d090d020c0d0c15080702010c030c080a0f090f030804200307060c080d060f0f1d0c0f1b06 64
    0x30b4200140c6096202a13030412010610902c2c10001907003802d0078a01013202d01241864980c103606d0b01d080d001400c80441c052002640030000341d0000b86440940c40050020701510024801c1c1900c240031601c1483d011070000c20004410b03000e0740484403006803450030b20340c1d02c8281c0e1340ca03440c0843d145030700800003460307401421613110140d51406c550311041500040c43c4201d5242002912200300030000760240da92080d070441007000130303403203640506084180c00003180781540c401030103482e0035130300040076500e0410181b940c130b03200380207180381164161280096a04c3d28020a0b0051166591010405a4824003480007509040034a00e031607009588200e400e041a0400e40c44a0329203484981b181c0c50340e5000c000b05030700e011400f80c04131140340c10070075800310702420722040c40d1040300844a00d251501c0004990301c00d000f95035409036a081040c10340055150815550828612588580c06e210100c00007000c1c001d0100041c405105031840c200d0803c102181c0f0008850100c000241503030308160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 742803399 1250 742802149 742802183
    0x91203071817120c03040302040b21070f05030f15190203010e010f120b011a0706051e0a180210020313030620091f1b050a060b03070815041b03 63
    0x401401e082e03c0030481e803840c014603090107503078901c540e00c0000d0069031600461900c981d0707004001e034000491100507900c0b0302e002e840003545a238003500907a00e070409881400310703141c10005000821900d00100130311149004070080020030200030491031804550303400b9104103003040d0010754000c0000524603102235041442030840c0c40c04503005014504801200000860305107035105044a11060040c82c5070003401014902c0e500c1a503401500440c00c203410300c0562141c080580b0a00032483c0d0b00c1e0380007911180f0a090646034030014004091030780603c100050f24085581d0a22080d40d80100e900d040311256600c0440480d03617000b90344560340c41c65a5004003c0c01c1c031250400018a003001c91600755000005030811040101002c5070282c0c681081101034000d02c0070310b5a1a074000d020800a014624015503202d480410881c1d0060600c9503141040c2000078080064618902c050696100c42020070602c0440042c42a141049a03210302c10840310400c080c2c401035401130104a485070a030b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 742804649 1250 742803399 742803403
    0x10e0102090922080f1215041d0d050334030b01020102040b0d05100b04090902120604030906050d140411010e0a03110d03020f010e01051608091203071817 68
    0x10702d1000310b825012000080e04100040383c50001d42d1013541607495a40001d40c410103402015040340c625107242c4103012001440b44545000803c0448050100383c040114005d80c40035006020301056100d2601341584501407800f07564001107942e003441fa0b01c1c000e02060442c084e40d44804420355a40701c009220350b40e81c14000c0c1405c200023030000350303d42858800d51414038410303039840c111801d5580d80072076003000c20135890400820844000c1522140ca440301c0e0401440613440491213400c5200b07070301c10703480320200d010361050703400d9250404d0952070404190780c1c40d800003132900c0c0041c0c4d4a041c54403c6911801c0054061070003070002d01000144840050304109036490070620071180841c0800001d90101c0200d0031041094810700145400303860141d01d4070702540300c034000c65400c0490300c1c20841e505500c001d1103154a4078011160414555055401e4101035540754800c2d004a46185405009040190b41060107403402110748240c100d0307007800a520580210000c0302103a620250410b4003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 742805755 1106 742804649 742804651
    0xb03190b010309140706090f140d03111212010b1c020c0c0411030f060105160602090d050d1d061305151b01020405011b0f02091008010e01020909 64
    0x42c4c151a54540c0c0460040c5070014101080001d12464a44108000c0343e8617102ea50440007081814000390001c030400c01c1d4240805540a0109420b0400c820740c0c010006036142030303d4000383e14594070020b0b010392105200317020910900144d41e29034442c0d00407549001c5d10050b1b585141e8800e5500307000050114036031007031615121440d8100c51000a61282d44841180083e5030388000044d01c0b40c2c01240f00b90914485000e0500000400590085c01c0074075001348400c011074950303500c6a185c4400c0c500c8920006408030400910601c42005400c1d00344030440e8801d08045400c1021045503000780f003038038466107208007100016100c20084039420722003080040e6200b480060810f010f94094814140000e10b5460500c981051110150b245590701102c007a00307120b415020883c0d03409000d80340320080c580e00c000c00125004244109042504403000250320341d5500000c0081d4018 = true := by decide +kernel

theorem cover : BRFrame.Cov 742625899 742805755 := by
  have h0 := BRFrame.cov_init 742625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 742625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 742625899 ≤ n) (h2 : n < 742805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
