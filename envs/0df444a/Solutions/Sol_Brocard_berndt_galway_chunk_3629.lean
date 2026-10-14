-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3629
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:09.935404+00:00
-- url     : https://prove2.me/submissions/e3aa0657-6fb3-4370-bdac-6705475e0451

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 652517985 ≤ n < 652697841 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 652519235 1250 652517985 652517989
    0x90b01020f0a050a030905030c0d0204051f1d010f060507030c14060f04050d02030703080a0902041d01020c010b092a090406140f3a020d030f0e0a080a060506 69
    0x41800c425010000b1640030498a04003aa07503400e91000542c0070030258180030a06090102d590703200010007528100190b1455420300c001003030018650b0240d18000c2d04807036898400c16042c100184510010080e612042e0b200c880c002c4001a4042c0f40085813030042001059006016624130680600300b1842035802814440100c26080e11005418080c0c4010400910a840f0380280154001c208540103008500c0040e0303034921a41130003401003140b2000182450400ea04001341c603d01c05400815191035020441d00303a040500304140c81b0f81d4011071103041c5400244980b0054a0045814240a00f00380044030303001d0101c0c1d003c052240d190105000d0b02e03280c140781100d0000c1d002034010885030303940c0c2c10707110180010411010700c600c1c2203121040e245c0c60300001c0009400c0040d4031003141c80400c44864609109403c4094104881d201000070260b940d082c4110782c3c1c1c90007034071012034440c103c140c020500940301c921607128007070341c04040c44982000550810350076400300300080e041d151400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 652520485 1250 652519235 652519243
    0x1120c03140604051b1809120307080915011409040303140c0d0e0a020906060a030f0c030e1504031d0303040b0711030714030a230d02010b0a0905010f090b0102 70
    0x1030101c032441000c1d04410364000071150700c210b00030829034030720014020501c40d050004000e41a44071420020400803680c480a407207402008000888d901e01740c05407401940f980040359400d01048e245010061903110602602c000154020003a519560610140000204450384440e0155075158000380c10940240c1c8610400f030f56035204040c2e40d00e000301e0070b00d03483d5006007410210720b07003020303031035641d04500007141c0312501d034010075103005030392150b0510865800a080d0002059200c2d1006005412288200320360030b94039650108050900075801440c020804400d0f01000c2c0c201d9040102080e0f100015201d0303500342c03880b40b00b503084c8400006890350040f504290309030200012420b0410140c92100150608203609540030603a42e400c50310b41c900001866650180c124502590005410158048d904c0381f50000b4100e8040854650501e800c8118080c40e0150b07540f02038012003850010341c402b004080407481072080c2e60401030026041400340c860120065110208065980c0c000d00c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 652521735 1250 652520485 652520489
    0xf0607030504081b100f1e0905100f060e090a0b0408030a06030c090e1e030f03040f080d090203070506180f03030903102703020a12120e01090506070203070b01120c 72
    0x4035510304403141301d91641e25005008443c8442a140416402000e8580d000b02c0308070a00e150101901c0860b0410800054400080d0844681c01a2154242061000c1c49100d07600107541a0018140d030a0403100800b03a800900204da0a5100c8000100080c612007012944268060100d5031030f0707101c20391a400944569000140500641c00c0082000707401c40c0d1141e02608801c20803500c4600c105894400303524000c100350b00450300204055100320291034000d680141c405e1402c988102d03607507241c01c1400e400c0100001103181d107404250b0300b5460100082c0c4042c1c081140e402d0314110349610051f1100c840740c80964019010742c0d6580395a90380900c1550050328015065909402d0503600c0e100c02402e0518014890000c245110100107120061103243c40c3d6142e0003c008040e041d450b0889803280c040c248070100311000c124101605941d0180030902500b030000442d00b0760380c92903c5820580010003880c1154010300048000c100c50100301411520001d4003400e101d0120b0034100003552143d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 652522985 1250 652521735 652521757
    0x40b06010309080f0c100f05010605040618050a030f0b01080c21010207021005030f1005330a02010209150315130e030301030c05090f040804090f0219080609090f060703050408 77
    0x11a0118441d03d000c01d1840100003820000c07c0402e014900c0413045801c20b015a50000e1428803041c40760341d0103504280382c081071203440c00060a40d0f600c0040d21061240e0021540e0002860f440820099040d40e0f140c05021108080c2c0101c0c0350900c0410340b8003211803008003c40600c410b01c49080c040a40c1110030f0396801409600048280800180035a0700565800454951120020311031000c5204460181c2e0b400416102000c4030821007101b29844003011110001800064100c488880070000c0403414101c0d0005a20f030700b0740c80c040007a141d1350b403121203040c94030400c20010140e83c2001d1100041604442e180030720142001034000401c01801004010f100020000c0244030b42521480304a81c0100c50301540c1c0c0d81c400320361203484082510014840b9005100a0102c80c038141c0044c2c004040d410001801c080c00084a800002003100075100481c40b520240806401c0172840b4a5105e402e2a00600030200001500c130343d2401c000b424101099603d0000c502084224000c552a910301c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 652524235 1250 652522985 652522987
    0x1c050c0c1e1b041e15170a06091e0309090b24070f0606080304181b0e0f04020706060e0108120304060c11100606120e0a02191a07050114040b06010309080f 68
    0x134440d9503c02000c03105100001100c005000181e0080c0118600d0389108105006e851008025a1408090544c08074104d488240c00681b0703001c01d0700e8100e0541011402691110005858111714404032154000a01d01840e5036058011241c0d026460011201d11903990321543c51b00da074280082642c02d40640105046e0903c5c600140020000000d40f0a9940c403d01824a4044081c0300b58110303059040f803280e042c0e0400720710300c034004e015010190000c10040c12507001d803000e90000030304990200c00102d40f0150b803080e0a000c801c601690345800f41a076040100420a2151a003007210300004100030a503944541140050511400c800310300401c20000300d4110601d64405400a0200350040b240007130f41400c6400b100500310700505003000140d00c00b03400c1c100c05a4003801086a9600700e08900004104000140c11000c8100c00240d8901384a21540320141032428034256004400b01d6035107500701a0501c07002c0742d0300003403c5030041000d003070001e4010b0251a054406001d02e6484131044c5078 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 652525485 1250 652524235 652524281
    0x105060a140d09021305150904210221040803030f0c07020a060e280605030603190f030206090a0309050904020a09050702070f0e070c081c050c0c1e1b04 67
    0x10b29500416078681c4200c4200094044110080d422030350101d50a03150480c01c205038100c981441c02c86660024040c4052022000340304a18100284041c01c45a005900011208407101d2a071686184583c009010043c40c0038a40304a00e552070101502e106083c824210100340d000200008a6031710583c040c0500424036503e880140180c5584890703035000d80707400e211000002d40c0c1c500380c1c2e0034a12080200010f40c6810010101c070a0b400c0145402d4040c410740503880301040e60b0b42c00d1035950794803450b50842c6e6041e842c90000d080000140410072123034444804440020b4110300410180c1d0001e5a4440c0c0c2c43d030b654000902c240782c540c1e0080845070724100c1482030683d4045540404e031940c003040020403559590b0f1040d10050100c50090000e40000c0301d00c00020078040092640325120b0391205d4443c400203c11004503501138400c02240e140009015150020070b0024404030b064002440200f561090100e503202e41e5803200420302d80b05044100491031b81c850740302a00e811180031440300400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 652526735 1250 652525485 652525507
    0x403020d121e0203090105090106050a1a040f03060b010215190b010c02121b0102030c030405040207080d050c251112150109050a0b030304030f1e150506091e0105060a14 74
    0x1350055400c25450b508001c0000c41c00041401104200c5602419550b00340d840d04e0003018a1441c0d0b502102441d4000300300002d80c01030728584140165010344c2002601c038080c4000a807901c01d12508000a2035010020071140607c16074481e440f80a41c1400415803580c07910040300c1803401200700a6100450320641200c440c000540e10420320010b0100c00900e800510059a890190500c03041043c0e20420003440241001c2d0045d00c81c07603125544c083e0400300780e0860303041550800c980e8444180e03400300751040c41e04568006c1c03500c5a019002601d51610040d00c0e9000e80c100040b18081c0a0800f900b13911810140410044205c5620303085000340d65616892004042c01c0c007600c2c0c405100d42824050b1101d440c001c0122400c80f9072152a00c210243c0e60382d40c1c8122841c1c031841d03406140602000100c04034028039500741c00c0514500740000c1c00d10748807080080c400d602501d900614803400e4810340200a0f10010315040d076900704c5159440781e010344000c0b101e404014100300016a00403403901300c66 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 652527985 1250 652526735 652526737
    0xa020d0608010218011b0b0c0a031d0607030b060301080a12110102070b15060f0415090e0403020a020a0b1c09020307050411030a110a09030204091704180e01050403020d121e02 77
    0x1807409980d100c80344c14401c441d03810081c0001b03a000c1c6c101001480414001ca01d0307100140040006410003045911034240705029981c4210f06c3d01c40b2540105e01040320b440d6151203031b601c0910040b00c4c81d90071541401080d61781c50004481c01040265840302184125000b0361868085004070f2000799901c02c51881c0186a01a0a90300545c205105198003030301c0346401c005640c824500c2007450741c00c26262184101310381d08a1610081880380c000301c04034149074018499032041f0b000b90000c086280052042c0029810307a03900c1900d41602c103100c4150501091000d50b582c4c0ad01c100404a8885160700010b402e004250b40800c1c0e00525001600e041000400051846441490800c1195080e10b1314500d50328807072050b03810002481d4000910040c03516a21541c1c14034014190180104207044c540f41030342d44035410010148030444800e0010319a6401a03440782081031000f40f01e1800e1541e0041d5031000c0c0c5005203010702c0750980c000c084015056020b1034000030030803050428644030307450700d00003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 652529235 1250 652527985 652528027
    0x30c2a020102100515090c0c010f020c06091b040b06160501050f10030201020a080d090c0b030a0c050c03071e0609030507120305060d0b0702010b0603190507170a020d06080102 77
    0x143c010245000000307095449083c0c0f01d1852001e0001d000003c100801182c940300801843c02d405003400341140b806000d01c51003d1140d0348040041e52144078548951500000400703010140e4000b02e111019590b910b030206512400517200410f035003010100041130790013880c0e8a0000054160004001d0040541000d4054101200d16403200e490300a000410415540000b03405039211801800004075038000a003401d00240400064080e4680e030341000a00c0d031a40100354201d004820301180030040c0c0300c1c100c1d241c642c03401c0c406c0c40c1c03000c4403061949a0050841c09000c0e1440c13500720481880050601e1201594890002c0004008514001d80780e40c0000f482552003055083d0f001c00030600901c80d1a0003500000d059450a40d00c0b9661a5080d9034010889011552103602240a13501d420380514011142d6540302d1380e100d0070440343c910483e200140294104101c40c42d060510710b0006040341c2d00b00c61100000350b9101013070342103500500b00c43d6000c42c07417039031001030b1000820a034010807001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 652530485 1250 652529235 652529237
    0x15050c010e06042d17160303051504150e040609050304060309030914010518060c0f070306050c03070f0309080403080f0c0601050f03100b12120d0b031c030c2a0201 72
    0x1441e14801c8800d158804c4043c149007000c120744010301d0f00410300354541404030305200100f4030f28009502c2080c030400c2030700e25012070200e03403603505111a544126640010134002941c040064a41c3c004103803255411710b101c4d00c07001114410218080c8800740c1c2141e17030080e80080449036166990301008000b0502e249050340000d03190b400202d04600801800188104140c0d0b40a003005110100040041c001441c400e0b0b10807020410030383c01040500c40c4015180f510805010102d10354188030098800080c9175001c109410006c00c094a038020071a80c0d064201c41c9070000c0d041500e0b140c0440103101d9a04003511700900801c0140d6825609001802d5024038402510902e076a80c005000e5000d1004501c654582c118001f1001140d805a2105034211002021003030342c5000c149246007841d20a1600c1c140204002840b4081034400b03000700211540c0c280c0007084014012524850f40d011012a03a204260b110b100c2024044e104903510700d00d500d00c0044a009503509180e102040103040e00c0100c3c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 652531735 1250 652530485 652530503
    0x115202409070605090f060318071d0a020c0a12170a0504140f070b0904060e0103050f0d080c03060127180609050f06040b01120e01020d0605061315050c010e0604 71
    0x1c03c400e0f11440545110740710140008103030030000810800c00343c0004240010342c0b8003046002407649402c20240d0010302200d01491045442144100100d0740e0042c02d1020050041150341c0710754100080d40c04056801c860b5090000b682000c044401052848400a5491301d80c0180408040c2980c4038500451003003400c00c1c65040d411360b0700382c2c9807800541421403d0300490410081c481858004000d5060b006000068480e03c41c42001c404013000c2c0c00c06d40f45907028130300e103600c05001002840c0014500e402c0100403881c01c150120500c0c40010130150403c001110b02c04070044030142d81c0c2008810100c80d20358042d450340b0310540b078080c60180080d0814149440050b242006100d80b9025500b03c1c0c1a160180d96600309101c058100c009902d81003080304a10640c1503d6035105100017200e01c08005643c0d400d150051006840d10b6400292081c01c00f0407081d007203100d1507507080c02100c01d40402d041d803000c001d400c1911207002e501c80c1d40c501942800e09008040c80c01040380d500c80c0303104858031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 652532985 1250 652531735 652531739
    0x161409060907230c0703060b1212040303030b010e0d14070b040b1806070b190c050301150e1c0803042a1e120b0708011520240907 57
    0x11440d404269090404a011010f0700210031002c401c1c81c0390041c0c0100c24584c0b0700322101c00210300c3c0034500d80c01600c600c0e640d0074041607607141c4809008160040e120003090401c00005000d0300030701c56840020f0030f055840c1c05061041c1d02640381014280340c01422400e85104508150f0741c45581c0d5000e0800c0d034000c2d008049507080300078094500366041040841c0c24031400c100c0d2840020501c0189a0340003405112000028031441b800c18842c0031441003108445a20305003940175a1403000300001402414401802203c3c003442e480401400103142584040280c4000311b40200807074040d10070402c201265040502016074004d5002d01d1082c034007a4400c22800e10003080808a03200c0314990301141000c100811010010720b00800048000e80c81c544d180c0d68441a00c28411000c4211408502d240070044e207550001219030040100f10040101c8118401005003a0704001c81072101003925507811140b081d80402c01010486d40700300c10b11840801c084003404603488103d0360888540309082c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 652534235 1250 652532985 652532989
    0xa0306140a0c020a02060c0717100c080601050313170c010b1305040506070804210914010e150703210e0d0f050d050703200a09061b0b060316140906 65
    0x2c1c000e001030040d40a880b000c44103900b00095035100650038207140c4904000840c190319404078130b4465095001c000c010b600c01e014104402e582e040c034074580501035240100041660014112503222100585039101117655243c0b44c106c0020b1754000b03e242c1c03080400d0300d140d603410540c010440005e00300c2d9000f0000c2c514124001c103640003160b00500765001705001c40c044900804c14513410500c9400400700c40181800b141c0d0400e00302000d28000607030078000421000807011030800103503a082ca0721740c0c80c024041010440040000503561840c00c0005180c805045c42184003500d40d1038001c040d071a1100308411000301604204428a20b82d010301c0201c5120140504180c2000c94140d844080c200501c400c1c0e031900a00e4001c1401045c0749d04c07903c5e8074482e40c103840c1a030303281461100465600c60201000080000f50780760080c10502507850a280300e6031944603000c2d84201d600c01d10b01a55540c400020a0a10f2140b80180c3c1c0040103800c030105110940c40740c15210391000395000c1c241a501d440c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 652535485 1250 652534235 652534241
    0x807090905060d170d140406060e0601090611070803073008040209100b1c0609200a0e06031303020c04020a080601030c0504080723010302280c020a0306140a 69
    0x59070940c083c910b20700c01c10000d8a050000c98140c03911060705801d25a2410805d0241c580d070504034014200d0000400c410000740340300e49400303040d03140800551031505c0f9002070180c030041e0041e1414400d802944102103c020050400600102c00c00d881e1140c0e640c1c80c018032900b105050303e106100c0915019200d6110001c45130015180d03950b607000d05038550f5001c1c0321541c400030309120445c940c4c0b01804241c0050341d10040020050801425047c02944200d81c012264642c014105003800d1641001004030304503041200c2041110015959030f2a410003a03800f10083d030030359600314402000b0000e01d001d403842d00081e03070740c0a60242c5a4a080c00c804000c2240300780c0c10f00c100426242d030003050603035101e54040800c40c01d036810080d05d09510703000c80a103040a40c0c4e02895010b51724a0302c50340b844540c80344a035404da100382801e500f8200d6080c03001e01691201820382d0101200405021201e52080d00280c4103d5005006021300ca40c0301d04003031014080b01ca02c8403001d00c9a00c1c0102e219104944 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 652536735 1250 652535485 652535491
    0x22050420120a0b040509060708150102070302060d0b0901060f231801021f0903030b15030f0c16030c05150903031311040c0809061f050418120807090905 67
    0x1031900d49000341c070018105101d4000307055100c00c01e589040c00c0c42e8646441c030507240501e0421000f8403c074548094020282c0c1c0c40141042c50a40000c12454010398000482d5025070b50304445164640b066900014001c0202c544095801261390300001011034208688490072440c85d0380741840c02000d2400d0307060031212020034141c0070400300000c0f007a010400e81840712a210502c1078681600450f1180e010144c42e2428201000e5a0307079640304109901072280104001e01515642c00d04a08060b03000d0150000800c4c0f400b03a20704034070000344240c080800f00c07421207901080d074803048445418020008030220404507100c3c45440c1901e0310580141c00704d588a80b40c864011032840e036680c4203540125000e16421500c0070301c0f03030186c14000d95482c000c860021001d6601d21a46140c4560a40e190600c05041e0480440c140c0e580c031120203898028102c1507607010b5401180c8000e2070044124241e142e00310140445c0c04803604c0103619544000464000e01256561050f03150315034a920049030815 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 652537985 1250 652536735 652536791
    0xf070321110604120203090a14040e07050f042a05180f030705040f0908120412170402010e06070204020a020709050603030a02032d070606030203010f0203090a140102220504 76
    0x2440004002031508102044e54000602c15a410704003110049804405150011089007003443c91400b980c1c1424400c0d00d254030b1390700c00100002d41c50680800d00a210404215004544400c0c80703c0341d900d01090000300d01084003a40300c00c00141c1d13002c01007194202e52940022400990001e2040c0d10b030009011381e41840080290031054900000c0000410086d001c1841c01c903110400540824070480103030500c03140043c081c4010703262510303100c40b041741440454420310800c54500742240d041000c5042c0d01079030a08042400f0642100000e1150280510007584580009110688180e001c01e560040b41c40300310040c0b0450300c800c0c04242c1c41e809202480300040c0d00500102000c0481001c5000d10294500e05890b8401401c10540c3c4d01c0c3e0384a00c8094034543e84500d800c2086040c2440b90440701c41e68080c0460440c1000b688568403103c0d4040050442040222403507030f014829411107030320210500600c601e0342201391803007400c2d403018868248030368034001c00001c002081001419581c151 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 652539235 1250 652537985 652537993
    0x315050609040e0f031b07060f1706060405130e010c0905010c0803100305030c0607081f0b03060117013003090e0709320a06020303180f07032111 64
    0x4441c280401000142d40012041c491034003c484000302c02c4c0000d1500d00780a000c1542d5001c0d88412451514006a2010003004801e841820b011944500609104401284100e100341c803000009826401a42c11403540404801c11440140000303a205a1080c00f452009002071100e01c2c80c19501c026091240501049219030030700300144503000210391207145540f200219548a481e55407950f0440d44500006521140910500e1500039641503030240c580002c401c0220103003c5c50310010b0078144622035003500003001160303150380106d1046a0700010950f01e56000c0d80e440040381076010000030071031135410325a44110400c898912103980616019200c0000d0355180c600700701c82100d00180071508000003e1004a02c808098240031212020002d00b442d00081000645c01c218031031196a0344650403665080003107503004804e80b544621640340000640303820b03e0500b401c1042c048034500160180c010080100174041070020101418226201c601d4800740001f07803045070120344034983c6680 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 652540485 1250 652539235 652539247
    0x61b0906090103150b0703090902160204020a2601060e06090f010c021c0302030406262406040e0f070c050a122a110a03080409090f020a090c03150506 66
    0xa0000c028000c0307000c10700d40050002a400990107602043d0f400c00800124009030b02400c0c507920040e00303005040c010f04114030303104800d07440c00100522400000d006680200b10789148901901c03000701250307a0b01510140451100c0b9520540000c01d0042c0c0000c14001361001542e400d003030060b1070744204090040369051106200550380030640d044100d0340302c040f004140e4950300c4001040c0700c5140c842e8006507280d504006000c1c150b140840541c3c0940701c100510640800300c0f0150940c0c120142d00204218494850a05000b402e154400c4a800c90000180060a204200e170031174440c4001d81c48000b025140e40504a80940394460060b140764420390030f800c0403c000c003103041c032100300c0d82c10642540e40e10094280128520403040da5500422582010700340000b4404081a00300c040f5072020149003180e6034902107008a0181d403480568481070282040307050841c07805401d40081004210640d25040640504120002007002071300741030402226103803000024068810003040142441 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 652541735 1250 652540485 652540489
    0x2010f1a130213030f0c0302010206070c0f062c0a0b010e0118020c0a2a06022a040204050d0b011a071709030a0b010f2d06120b06040e0108061b09 64
    0x14102c401d1166100c040c9043c0040061030040d00300c1c01e031610425090020314550300019007060360051190341484aa020f01c4000201c4680d10b18500561050001a210103545440a0781802510b08802c0c2610405060741080e030000409400c01485201c0100b2144e8841c806c00440c500280b142e02c0c402c0c04e841d803c0740800d60250300a0320460b1b80001c1103d14180c0c0a44400c240102400e000c0202000300c20307192219400c824080c04003405e42400104103001030030910948095014103101260061841140800e41e40d640458004102c01824030000081074104070b443c031402845011a656615009503450410b6801541c17030807030308034194580300502e242a10545900942d6816410b008201001c40000e04180e10b146c00f90580c80d10030103009042448101c080c084d82068095641d0b100813140d00082c03603c1c030b4100c0907512030385000b640c11080f606502010b00080201d02e6030107140441c000c031b00701c0d0410b400503040b141c1c407a045a030507448480302000e5034101360340190000c1d0310401000880f4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 652542985 1250 652541735 652541737
    0x409050a0f2d0302010c030c08150d0b090102220303021c031506020609010b090f060d0219080606010f0305040b070e12060c070c06091413020c03030702010f1a1302 72
    0x503401540c524840e1080c0d150030340100302511440b10300c420308154612050650910808624903440e040401020a80f42005001060010950b20343ca680b91481c000381c9448030035106070b0a50340014403485034107003e030a05000c0e401606044950809074a00d041c00c40c1c400c10206400c40e41c16030080e0000030b0f01d414a9002126100130400e051603103070b50310007030104062401100108a25805001c00d070030b0049105095918602c08240310301030082c140312a509950206540040e411503500c441c481092001c1a1070344000310b03c0001c2030544000016440c60702041042c821a02640e920100319800c2905904403607058030090a034540002c00500580d01030100c4403442c0d03e008100c402032800c1c08409600d004411038034450014000314280041190701c0ba0440054640350804405a0342402c1079010f4074000c0c02011842985203141c58481600140e0445900304071035403c0d2582ca01d40600003034042c00140ca40c8280d207a2503d04001c034043d400c80b0101d015207600504403130b5800f0003184003c020f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 652544235 1250 652542985 652543013
    0x6051005100e0a09020702030c09041a10030c050d081e0903010906140108060106020d0509010302130b0a0801080706201903090306060902040b091018090e0c0409050a 73
    0x402085540440c0da41c0e1844841c00040241d682d031149a0110789041c45950341540c1d1091190750300510820006070344c081488010002c059803ea10b4030b03610360404155032a80c07040c400103664291414400d03007a010601c01c100303130f900072006140390a9031401885040413001d94007038034200050003070300340607411501c903102009800d014030340c2020740c21400a403c550009070116403d95a50949070707a040c0d80c46c09140e00510030704020b045651314021010b90cc0300c46420001c420842d0003d81032074540e004e03605032107040325010202e01101d41c444500c2c0032036900c0990030b03c0c04510903400029040c60000340c000181c5560b40d8444071380c0c1c2e004d05e000380e038988030b06056010a806643c003000d440180118a0b41a428001e81d1124100c41c51401e04e07408498040d00140340306030042000380724440008007240d0241f0420b442a82014500c21011154413000d00406000034010700c00000707001501340c000c60b88d40380c641d40540352a042c1240070001102c2c40b5000080541c0c00191303120010440207414008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 652545485 1250 652544235 652544251
    0x60f0105041a060f090102010608010b150f071e020909010515010c051e2803053901051509040b07140c0105090d08150a170c0303160515130605 63
    0x140c8880340000b4640b07800c042d00e0503408200100f11009190b1f8240101002005a0760080140000b14008030340300c145100c141542e040340010714402e210600b003044594040c1c00048180d0400047c500c103044c11640920140e02c5a6403610105240403410b1184a020b080e0804030424070003804401942c442c0265407041d0303001c1c00344444902d92668810b0746001044040f0300505240030076034840220100c1011180c1c002d06114100b20000650010115241c0e4003403616040d03205500384500703014104003590004032202000a550500e907005400990207150351801144100d102c000900c41c07200c3d02160054404100e42c00880d6605005601e0b50310f987c80005150382c9400c0c0c1c500300b9142510000d456003550f582c064006480032a50000b1003c0c0c00031807050000c5086100d5400180711421940155640c0ca0030208803c581040300300310b003480001e0701405494443c4076040a0403c207506400302610b260242c14404d442414503203500030f21410030b0120390403c0d036002e902c500c0020040100066 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 652546735 1250 652545485 652545521
    0x10611151305060a061e0b090405040f02040e1e1b04020a03021201060f2307060b0f03070902091903051b030a020904080a03060e010b070308090705090f040b060102060f010504 77
    0x280855403d101840c80b98003503150101e1200c3c9811031107030100310140690302005115140034458185104215480f804089401103020748550820b41641240050700030b42c85403a020b8602c00c403000214408100545041041461902c1525259203c3d440c400d40064428280b4400c641c0c18a041d40c080c0041c51394901c4c005042040300c010140e042442a048040861401c06001c0c002e59440b511082d041000710044188614480d603903200b403406190001402d141e107681410846d500c4408200c465000c000342207810700d6645005c20f100950101c2c04040c001d1740c0074000e01c42c0d00f6590684078411a6441030041c4002861041001000380304c4203189607240c05014034030301c05641d0f880c201038055401490301a1303403504e00b22005400c0711015846020f4003d492401046840b203480c055a000780d4150814840c43e545d01e11000342001d88541000e90310902c20028000749a445500c500d1180f4401c074001c075034944452005a03035031407049031404111100c00c3d00603c09810076400600034094405011 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 652547985 1250 652546735 652546771
    0xf070302090a1e0807180b2407030309150f061d06010516120503071d1c05070509010603270f150b030105090d140f030c030c040312080105010801061115 67
    0x31609141040d802126680035486c0c696015001e944681d41c04c1801c1100d0000c80b070201d458045495507600311002001d14004245030003454000e4006003442c0d60b005c0c0588000a1019000c0b07401000401220403005103082c8000c00c1e550040030005010000c4020000072a9841c0e1004403800e40c05a61810581c0350310b0403018001940f002d401075031045803516817544a140c074841c0141000c101c1d44894400c6460720540058549441c14100900070344184400c4054510703003012442c0548540c070a030782004a000000880e254036074072002024050119080405c00c60450180100f4100c0300050507102c010115840040d05240f100c40c00290079034000308415050384000b81c07c480040381e100b030154100100160030103922206030400f600c0006907040c18220305600003603040c000100b11207041e800010100f4101c004603002e0f070b00215032020400a51400103200180051001c0c0700d03003404110303610300104100d40540b50712002058144e0081c890086015581401100003520614030a0706541503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 652549235 1250 652547985 652547999
    0x909070e010308030f0a09030804080d0905060405032107020709020a030e1e10090302031602011808010c0807110307021e060c06010320012c090f0f070302090a1e 71
    0x11040c0218000c030190b40e142c1c174018440d00d40a0000928003182540f5116903440060307004900260013a4108407c99120755007920200001c010212000d88188101402c000420400000420001003110343c046a00050502001074402c01030741ea00000d80c00442c02404002c00560140030810b905250100d80c00346840c3e001410311041e000c10f6140886c00720700d46070070b0100c20810103c170f150181000300924007030350b1130080d141e0148240000003441ca14600740190384c407845903040c11520580400345007039944d586181c0205541c00861002c90090700c005103825000d100d5404417102c060024501e4000c41d5400c01902c05502071080031450340c2c020341c0c1a6039031a030001a001080c2c0c00d000500c0345504508041071484100d040813201680320703a20301d00803640d009140c4034251004603d0814140c510038003441c000900095500d170010301001c10002400c02d68400240144a5640b4100c19900c5100d811400e9109040040d50003d01440c002c006901340d400300c1114580b11224103441058990075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 652550485 1250 652549235 652549259
    0xa03060c0302030601090e0c040501050c070512060415090b010e09070e10080c06040b12090a05060f0412080402091609030503070602090a06050c0601050402070201020309030601081c0815090907 85
    0x400400000d42c00700c10420f807540c201e999400a05180c246005241c9040070380a50715120710b0003203078100710340070582e00c02080040202901608004001800f0302c41c0500e001941d404085500b0f484407944041d00c2e040d5100284503170340e01e05821880342c120356800e290807001495000380042d4042c0c400d0800014800409090241c0601400800c4904e00391602c20300700d1502003106407551207810100f00800005c0c880004503101031405024480550342e6640b680340c10000702050142041c0600810404201100650544034611480b1140d0360004011811501d081007143e009410910340c5000c201084075070400f142c01c40c21035150440f080398803a074540d803d42c0c2044004454141d00031407415031a1402101c2107001d4810f91500504020202e15803c0d603555041c0b0940d409070f980042c0306000d591013407046812803040541150320b40d580d82c62140ba561a80d103a850240424030a0201c00107034030a07001c2c1c0740100e8006440c511181c49402c20031070b00c5030015104017441c1c498201d001a1030401c0700 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 652551735 1250 652550485 652550501
    0x1205100b010c02040e07092301090b06040801380312090f19060215241c0b0702010501080d0c2d080d11040303021b0103021b030408100b0a0b090a0306 66
    0x100250114511f050381c00c1069070483c248a8a0225096007045642205030902604481c0b00d800086864501c07031001c102c83c0d200c2da07003001145500f01507240200210280713040b111354503010881c002956500e200c48220014140c002681a0404441c0300001c520450180c1802d0400400318015000e2010015090311000484514a1441c034842004050303014050800b8501e07810b200750035181f070510004102a03c02520080700140000c0c861015601c8050f08030201020100d55010945100c0c00c042034401c0085456000560800c4004140d8100108284d013911602d625444840e18039030b6511001905007180c006121186000800d48007144810114040c500030060140d681c07011601a00031b6600d0041b010840040800040000950000c0c152542410074100d1011300044080128041e2248009003100c101a440f026080e004000c0024004c4502000448103001c1c1c0d8403280b501034862450449510180e69a010030203e0714110051009400c02884007a82c10b88035680ea40c110b500740707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 652552985 1250 652551735 652551761
    0x602030a081803040e06030d450603090b07030605060702090c070609260405130f0e0f0c0112050f04020d0629091f0909020103150e101205100b010c0204 67
    0x115050001608042c000144041e1580c07030301740d21484500d5007949601a8503411203c900100c5425007000100005c40c1c152781d48a9032507400790241e62103000034045e203c08c10050740c03100e401c800800e10840c024810303101114000707003076170781003102503002c005038600c00a2080300c4980e0200300400020f0b10034401d40322035503c5080e505250000001c1d008404520119211060a008020510181c0e03541001c127122100c44c4400400c003503030101c4101005d48214540503043d4401c0410802e0540c1c800325040140d00001e1b6264041248085144425500195101c0304225202008500503090500201b030140f4000c100218423800d0820380301075084035007512007c100400c45c3c0000b550385085141e0b0754002802d0110b40e52865807010031251006d8031841503211859842021004590103900f110142c0107002d19644030315541c070611500904000c881244182030340311000f0510040100c485401150403500601c800e0001e060440000c0c21a00d00316410b00010700491801660355004031a205596 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 652554235 1250 652552985 652553009
    0x11030904060f080f0102030601080609090a020d030339030e1e070603050a0e072903010308040510051306080601030e0f0708060709080c09061f020307110402040602030a08180304 78
    0xf40142d06410158603400340040e40c1d00400030b201c8c55170703802103e00d0b401c04401c6412880b503481e131441c50307868940a480029000840034440c0e81c03d1542503805054083c07848010f480e90000346045d502440852407902c00d00100e903002c0007480320340c440e074000402c00c55490110b03800c2d0041c645180c140c0e84100004044c465100d900c0920007150f25000e1107810080c003920a0200301c04c1c1c000d04a450303005030b00407010050011480405500340b1405c05041c40401030400c20799070750f120704000c5170070760090003024040d940b88134245170294402c800320b900491144600c840da003401c0c0501102d01e010302604113410181ca801760182585407e10810035081c102c440100411498142120b0400070b0085c40e89040c088aa103080045801c0482c00c000b10b80c908455050240c0c1e1400000781701c04101c2c50107008001c03038180790803a0143c1c0000003409a2030090240d0062070b0134110820060b0b10860084500680052000c8280207000d00f10003500548143c0c5801404141500168a15005035101c000c038084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 652555485 1250 652554235 652554239
    0x20d110f07120e180c041a04030209010e06061902010f020408030c071e030f02040e16030b131203020901020721020418050c1002010204050306071707180611030904060f 74
    0x100c42d114194450815081c042c0c505480703940010f80680351a185842039040940005880f090001d0450b00584082c0528002000c0354032507002d01c58005020032401200d0790800811255140d5040b40d211b040002c00706440c10500a280302800c103a144800b40c25503480700116111880700e800900064034035000115200c01060b000d40380b84c241c055000d211005801408004500d4a802800f8103491300040c8090a901071807010800070400c0700d82e0f00c20240a035140386003d0a40c03070785607076040764060b81c0381b5042500da1000001300c0c12011003001f040450fa0604003c0134502035009030041c000f050056035811682d505d40345120300c00c01560a101c01540a400b81c0461601c4c0c0700303100c05400c12407220b5001e87c02a503140c0f50340d4820343c07003c0c520031410040380303411f100e10035011240980f90141c180c1c6d1040c00e0002001d002003141290aa0035000d5640018502074412508494020903459403c0d04403440c001d01651a440780c1501000a8042002200c8407a00c0380e02847c00101107002e52441c000d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 652556735 1250 652555485 652555493
    0x60e18011503021509011209060c140c070522050403030c031d03040b03100306020d0b1c0c05061b07120204060b0c1225050d1e020709020d110f07 64
    0x140c0054000c0561103030085060000d0388540243c00369090110204d0b965420b204001610207404603c0208555130401ca112810407980390442c2d1400707a105d40f80c01c1017115014007014814010b210714290f1540c440841040301e0714140440c2050440c1d40e00303008540c54504030720581994012038017a000300b9260044a086c0c030750305d44034000d000700b00c00c01c28a0f02602d5840c10319071a8451032003102c07000180031010520041007822610000c65120074110b5888442d03e000d80e001c2c060300100070744030b040c8441c02840c01b4132000c1e003400005a40580a0340e0385a0501c01040000d400409000c0341c2180b6040490303010600802c580800b074421245403043c0c0e64054810841600c0640c0c20a400408003808070a050010000312140760b04500d0703803050303150b080e030a03000320982000d0004650346130144044e200c140700000c00c00c0000702002d0380d5100340c0c01c0d00d05480c205503411007103c010010782c001038080100e1502030340607114812035080082458988591101d4090b0009404000b0107440060040104 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 652557985 1250 652556735 652556741
    0x5040c03110a120b09010b030d08060406090603120804050c12011a03031c02030421030207030806040605010509060f07021203040e010801060b0322060204121509080a050d060e1801 79
    0x10881c12220054002c2c1000c6111007032040401004003400c00550104644039000c5d0050310711400e000d4112445540c910000510309442036a03440c1c00b0700d103021800318503007410f801040305880e0000200403030440d07450021201850020020f5545e40030b161091026907481c071030400d020640340720010405000e403110343c80803181400020380c46075000700002d10b500e00d44056000d48480000c080141c0365901c0d4108201075005401c5001820010318201c40149601503014092440c02623890212030b560744800e0100b120102d00070070317020032000e001051740c40c0f80620007809480303030722003000c1d084c4000e56000c100f0525403a40b41c01010340001c030342403008036082440b0070700408907003009000481c03512600001071321000d003100c3c142d070303401090350901000180110000300f070380031604551300c0c1d0303036030440c1300801e1915441140d8845030b00c591411144a40e00607502501c0e080704030355140001014050325070303602054004200729150380300040c01120004c09030344184403291500c10744245d11008070b421 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 652559235 1250 652557985 652558013
    0x1806090207050d11150f0f091209040c0c050609010603140303040b0f0406140a0e1204081506031501090507030c0318151107061d1f0203100905040c03 66
    0x56106001c000c0106900240c0894030a401e410000340b580500c0511604040c4900352100b00460200244003c0b10b0a008225110700a41e50340c59003c2e03100d1640c400d450344148410410301c00010b21014001e454030742d0103200d8190060801c4d0032606000c2e9034050402004440d07600341a5580d980400a21121103040c1203207003450b0001d07518500c1c10f0340e00c00b040810094888611b0021f010005010440207034000d084005110358000002d00d05801018003038811901f59913800d002e10701082c0104082001900e041d02c103100e01a20b00c8000b4507000060000380144820b030f05200e4035142c006a10301000e5400d02a184da040041424030344518090b007602c80b2407500350101031a0850070500480e00240b081400c07030b40000150248580282c0d15006800c2c110b6851850034030000e104000c0102ca540326508800b00f902e4214a10803804d03140f1a200c08030103a010603000c0211601a00b5008198020742e03004900606800c1c1154880030080221003007200c0c1129040001c0d841070090107202c0380d100704 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 652560485 1250 652559235 652559249
    0xe070305031801080c0304080d1107050105011503020f0405131d0d090e0402010203160203071a0c0d0504052404031218150f030207050a0203030f0d110910081506041806 74
    0x358101743d914100705110083c0701804074400400c00b424403c250340c2140804440e0100d03c40e450301a2410f0441c001c190a1103a2003014106080c18061a4020f00039103048485821900d420285494203020981160265042500d030f900c00103041031919118410414070440300042c0100c82c0c101c6400f031b01841d46d0760458a0900028000c0000503079001040703885c4d4240304a1055200c44062001c40d00e0242d56070015003090040300b5410428800100c00350400d55580011210110108001550741e172056000d00e40c3c000d1030707410111b0b4240c4580f0b400440803c00c0d104040c0d29040d43c036150385203a02e840702050800110000542c07034690b00c0340300f04240a410000c41d001c55000390034002134070100801000c0800d03d034010580c03400f408020311040c101d05030003605880c0d54820b40024ac00b0359174011560220f12a04e001c0784620644d002c84291403031b454010700a0985060240f80950b0303202002088409403901054070214103880e400058002000098018000304480c040080f06603403068000403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 652561735 1250 652560485 652560497
    0x9050604180f15080c03010b0a1d18060a060302040f05151c0c06020c0108071403011703160804151803060b0604030b1e090c010804150e070305031801 66
    0x7109030405044410380301140200001a50702c41101c801015007002d0b1a12502e00c41d410500250a0002082c95410308004074001c1140c4013a480400c003668045000c0c01e000140386c22026011020296851500006551000f031074111a0454032450b03c601190341503000e5031240b400b00700b10b04140c003c0d0201c408540005010034500700c0201d403500142000c0c0c0ca803203003c21400c0c81c480e4404030480324079859041000802c015442d07240207075654004502c80c1c0c3c0080c3c8140005154a8420540d100c029900c50b04081d285034601540c070401c070380f043e00c103d021601003084200031120305d00c002c40e19821710492045440e070785070140181132000760f8244070050240c541e5580d1490f000503c8240290b0ba403240002882910500c0442c060780119040105980d20f2442401540179460340c0c480c001c0d025284240d8141d540345c4080f01d0f2581c00301c820f16070214224501050000703d20407803844a001071160f0008558001e801d0f041e207041695402511642c100251240600048401d4200012000c0c2046 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 652562985 1250 652561735 652561739
    0x40602150603063919170c030c3007030e030c0618010e1f3215100903050d020303130816081b0709111e12011509050604 53
    0x40e41e071480080202c1c8884204695081144030600c81c141c0320400d51543c0064072032000120201c620807401d424180441d400b0b80030040b400481006c2d2074426244801080d003181c81c1c5c000d85d82c0b200c1e0030184c0304084290001e42c0308206004032a1191303100c440d01d004183c5150410800140c00c0703442038848806283c0040005070002c240c005000354100b054049003d100000c076008842c010142e40c52450050b020744002c05d000c000d4864000741c0606d10134042001505003605a01031940a450302c885182d004000030000b41e4206810307019488106c4041d540c022a1001c400900c01c00d00e582065404503003089414800c1c4030080140540a4080d40010352540c140006095403045101500402411002403040015003415001038541035010b40515100d00c10040d0500c009401440700705003611030503000007003950389405040c03003070f000755a0010710f1b01c482d21180305901803640c007843c01e08200812681400c21800081c003070080ca01c08080c01501e8000400050500039036502c0303284565028042 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 652564235 1250 652562985 652563001
    0x50412030c020a080306040912020303070215011d040f060c050c010501050d0c12051f020a020d0305040215280c14030901080123040e030903010b120c060a1404060215060306 76
    0x6070701c83e640d0003c0750541c40c0e80e50a00000c016101b100d50003410000e0301e0303a60301d0388590000059409400d040d02a20350700c1c0e4154000c02c2c80c0c08400d10400304214000c850040e03040d40e60344040703030b001070248007081200c0340c040d158141a500d081004400083c000a00c01007481c000b84950b5000d02021076100700c403014151908890200305010f110302c401140910401048010000e09000c0f0300d80108131000ca08140102400a4000351184400f6001c0d0400c49800c05100e4030a0710f01c035645c024502a101c0c250b540a02c1140c0c5c20410813004810148180c40e140354061840c144502c2400d951842513a40017072500b0801b9100300503800e045a44144a003204980e0045030290660304540c0001450311140844803901110861815410610703100b00040707401e0f00480200039001c8164003c0c08248070003011300407440c007803004191041d003000a2000c1c003803400d070000f00f409510030b14204980400000000c1ea1940c0103a0080000d80c4c00400031a60140300310070700300d5100d0f10844c080c1c0580c0c130b44099 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 652565485 1250 652564235 652564243
    0x9060e060c060601050918010e04030305160f030209010504051503041a07020a1121010e0c0f01170901020403021e100819090c0f0902030f13030c060b061c050412030c02 74
    0x3d41c140712002ca030240c9591150380d03803041d0007645d141010803d540d4030b103030007029142c0a841c00e60019082100180b04c222066404500190940d40d400e0300c14044074100314000d402c0401c4083c1000010030000403a9aa8000b9400c41117503000300c120b5a030b00f801e103450880b11609810041c460b44c8004200100c054020070110022030700070303504076482c1034845c0008071030b1000c1d41a106942041420040050001540318080e0201c0b03002c00c40d0b8451711103100300610104074035600c500168158401c1c81401c04001800b54100c1403460015081075240e50010f4440c215619080e905003080d82c041c3c0d4009c0c45c14414040c2e01c16047c0c00d09290900303100d010f11101290190340140d0994a8119460800c2201d07a14000207020039056014150703160000000654001d81d42440894480b0000c10800701c01094690b9415903da103400308078013080e960b208045d000b04403015034480385c14000d000c4030500da080c040124205446000a061500703160081410488000d14410140782000c0e9000c1150005 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 652566735 1250 652565485 652565491
    0x307061107090e071d0a0623010c050c0d080a0e04140114011101020d0c0228031808100207020112060807060318140d140c07230307030309060e060c06 66
    0x2e480030030b001c03003001d000e586007942583c0000401e0344104244c855100095207054000c0242943c140880c42e038802040e0242c00b907104051541882400d0306911a6008544680f03207140700794166002d410051002035007100303032003000340d0302d07000c0c002981071000758002030340c483c20742c0121400c11000d519180407500d2901d05000e60303c55041d400c5081d40d840c1e0300078080c00c1c0c4824024802550b445001c040448050800c40d0100070144c442c0c040050005001d14209000e140c5101146520004071900e00301c5007061800c1080d0b1030080e50000102e14980300340840070b0010004100580d58040ca48001800010701c94402842c440c9041d0062142040c0812000221a19450049605951100e05202440b0304000042c1001c0902d01c000c0300c049004205a462107030315854040010000c0d20201c2005d10914400b90703200c5d0441d10090055018218604074298200c070392070411001c0802c0400d242c00b2041c0c01c19408554504010819a43d02c054034401300702054410ba810480c05600184e0303650005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 652567985 1250 652566735 652566749
    0x60c0313140a0c2907150c0c08040b03010f06020d231c060302041b080f04080c0607090509010b090a0b07060b030d0c03020c060306031504032006060307061107 70
    0xa401c65001d5490700700540415260021580441151340314a44c0c09a1007038080003424400303103084500c4a401c0c08205441105411502504e0800040c0000f18010000000340f4414040400c2400d40800c40d000d001e00041e1504460942e41d950412864840909d0168031202c03c5601c4082c1c0d5031600b540c8406104e0307001d4150b242d41320750920308820844403070050000603c06d210000400110300b4200f41c0280044900a0b1001c001d668044021030303000c0c8520b5001c500c007041541c0089910090000d4405500030300132801030b410010080c0c1c6082c103200040d1045000215448024000c030728041202070b00611401240174030b4140d5400208035560514402c40f001480c0c0807a0780c0c03040c00b2507034000700d01880303005043e52620800e403c4041c0801011030402d9005101d408080c44950904c3c00441e801100300800400010088001f03105601c3c41c0204101d00700040404084100c40142006206400c85c11000c0c056038505031042c186001c40c1b580c07101c42008040301c80d0104c40762000c0317045002c1d500a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 652569235 1250 652567985 652568003
    0x6020c0f0a060f0f05090607150b0d0317190203070509040b06090a030311010216050a050d0c0b01090902040908160b06060708090114070206040b031503070f05040905070e090609060c0313 82
    0x4411019217050141e82c25690304503000150000030445a00a482003288a40c58104002d0344e4800034000c01040c0d00c000200402c511090310042d40c01703962321b000c1c3c1c09500d039070350005a01010840700d01a60001e0711618041540410350840614007030090104040d02921892b0401c4906030002e25200304d148405003e100c03294a0f101582003080d0100c41c103032000f0284001e00b0210384c0c1740041e9601400c550698a074040c001114603502d206150028080e03810101d001c030700d40d00307011140004141c0c0708000c0341e000b03175194002d800081c000300c050840102c032685607410380340c100c4c1011310311204000c000034410300042042e240050704040aa400f120021300c0c0810345407220090f103000900c24034201035030046c000f040014055000100075445600c0c1510020301402295081c517079105024000d01c000c4101c0c0c00c0d014003150900c1d03403141c000d0358010000c580300250f55682000700840160381c10400c40e0081d03000c000da540c004004036500f102a101000707140d40341445410b9102124064002e0030310070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 652570485 1250 652569235 652569257
    0x12d09020103091a100b03010b0f0a030f060e071b050a0615080f01020d0c0203070b0a110913061a0304030804170f1308010e07080c04020306040e0706020c0f0a060f 72
    0x11003940001d18440c4d01c144008503035a02030403101c4000078200c0b41c010781031050400200b8900c424106a0741210b080d1480c6900380403141d4030108064000740c2d4a031040650740d4014001d00d403c41e00544008003250000780e219428916001401c040b0b001b072100c0314480080700c10354001a000140108042d401080028074082803128440075070440c0e0340940b07c7c620074500b10144002d41940180060030303150004100b00402c00758160303101d000f030610213403250041e0400a071040a59030030605040302c3c1c440091f89015403900c0021116182d1050046c82541d035100c2c140303c0010b0400c15815156242c00840d82546401d540040c091140244001c1c0180d41c200c00c0410305080b50030a6a01d454500304402e500d81d41a107806090440051060380717055800c0554100c008200481e9242c240c4001e0b4024100e01040c0c00244800780d4000f8140580090350b600300c1e10190202070060001074601d84d030203400f607110604200065030b003031900200d200f0301443d50200803807074120350101c00d030f400c0310f007001d8030204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 652571735 1250 652570485 652570487
    0x7031815270f080c1c180303081b130e0604060504090503190c06090609020a0f06050a0c0c080d08010f090b0607020d020f0909071701060503120c07050a090905012d090201 75
    0x4000d91000381900c0c403400c041c01d001c100062004445002c4599901c1070440d42103484906e41c54240d20000d804206110081903550341301d00350711f800f03844410030150f140556140e40090300c0380c241d52010002c18182c2c01441000d152900840d402840c0c01c0f01d0034020151552105a10b920500d5140d01d542610204404c10700380c002c6c103003c0074180d0403400400251b102d60500602034544004101e124540045001c01e08900300d4440c0b106450841e5540c41c10710007505000c0d01d04040400c030a40e4205000c03040065122810024040d1a204d6581c60788542d5142040c0c1c50080b81c0750350001c40e40390707080240a03201034543d0015a4134650b011660781d0315503c2d160010500301c0c40b2010003160014104001c0050403900000c0c42001c89100748408881e03881c01e142058200c48081c041ca85c1e141d040b510050401800320005004581400b40503200c4c4c403941c1d1030000e100b00303c0c25801544842c1e241d4100005005080c8240041c2c5186042c107080140f0f11143c640b004440011818036001d5950740c010415a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 652572985 1250 652571735 652571737
    0x90603090705190302030606010810090c0203040b030907051e0616080d09061b020303040c0501050901260703060e360111030f060a030f02040507031815270f08 70
    0x100006441c0240307015003c1c0c05030fa4400c40c6400705034003d1081d0004600345500c07602800d4401e07998183e5940d00141800001c17009404480800f108501c018040072441001d644011400303040b00e280107240791440e220903c18940040a40407911003003d546080031038854400325907050f076508900010401c4545400b441c1c5002d09135403015010700c1c0290f08010091550300613080c8840030500e6402c0141c014008036902e2000719070003010404845c004100e6540620040c4c00d155105050610b801040307a000c006145024a050b44056580c040038040f030b0325098810b51014000081c03119246180c00440d1510034140c001540000040d68011544102c2e0303682540e584d12000180240a0341840500348c0d1600c0d001a00d130f101c1113481840200301180f07080741c8401e00300c030343c401c0c1c801100c20904d4080100500c40103000305c09050312160300b14040380c980e402c640c0c0e401c0c2c4180e4800c1c000070b241401d240101c516800352000f640050b12148001c1030135241c121403410b46d00052000e0058030a10706207101e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 652574235 1250 652572985 652572989
    0x3040e0106050a03111b1b0d020f0d05190314251b0e04020405010e070804030503040309270f0b0d0f15050c030a1406010509040509070b0f07051207080906030907 71
    0x344105c0494803008024040900d103032680c1100081f41c2e00e180078000202e000040c24010a540200203200b01401030406014250004a0042004460204a4581030b08203402c1401c18100004039201c00c030308064000c51807045200d41c0e864143d05220015041003d0040d085c5098003091448804032400c200c013401180400750a4148a8848141c1d00c40c0c00f00c9031071303801340c50480c41a41040300125a0030315002003144942c400f40c1e52880c0d1500d030390303e09803103d0380f001c1e0094040100100000c5103803413080c100410071041480e112801680300d60007004c1201e81a0196019850912100b81c80d02d695158040c50900e421417403550412040e85084000300c8428000340d0710712400c22080250207032490001e9441014802011310210001e49100f00c0c00304000c40f512408101c0900172608903081642c0910384c015001c1003201da03025164401400183c0000301d005095803800140380040000a000142ca10608100c0c41402d259440d612034641c1c3c014001d205010300b20100000308441000c01030400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 652575485 1250 652574235 652574261
    0x1b0b01140a0810020c0105011d0f19090305120a0902101202040911090307090908031513110a020d030504020a030209070203040b0c0106030210180b0903010207061d01050903040e0106050a03 83
    0x1140c0c3c0030401103107019412800701c2d04400e51034074000040d800321360782c0306415181521301c44031403079500c0c03451013041340c40080e01882149440750703100e111103c0f80303125401109000c0c0d214152a01000480344e01d103424000c04031111141000040b01c01a00ca1400310450f001050a04414100069040000034000e940c0112142810501301a100520500c02803074007180960035240200d1b141c0c01d00c2c1c015640100d400418441c020400100301e07003c8450640034241c0020400c000c0c040040038a030741070b100d0405a6846081c400542d850740c03160100080443d000c481c2c00c0901840c030b03103a00090409502448040c0c021001070b000100058802e10807240946170b408a042e4584c03039043ca0140c020700550000302e018401000010110900450501c907070841c4440c401c18640e0f0620740004c4003034002304041a010340d0244070901c0090b0941c01004c9031050129400c900022090a1450035900082c0012845810811040c001603403031f040c0d401c0c1941d02a090503030f50307030782119030490090214003003a0b9 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 652576735 1250 652575485 652575493
    0x902090a0302090606091309141b040b0406080336360906071d0f0d210509041401120b041a070c051203240402281b0b01140a08 56
    0x1f42a24980c3c4608080c5000d038583d00542c200c0e0000141e9502501c0842070fa1000410003548020b2809402c0113980d114090400f28501d81e40c1c1550500e15001003141303104606c501c0340c4000c00c03640b9032041c240c0410820300c01c2c121036030040750228055004044a200c65004103020140b4400001c1c10f130701c9542c0311030035801c0c9840e24050010644071601a510000021001005012000c03038105140030070580082070060098107076030030044181c0304050300f01d0b119a44411098040507080f80b0400c1154800c0e152581e5940c015010003044418001c401410b0090480062201501c00c004204105900001150700c43e203c6041418040b4400942e000703101c4035030800c00607011b0303100311840b00c1c0724032610449034130003820405404d150108681181108610001d0311505810749100c1c1d4194002c05000145055080c41094400c08260020f08604052110075103600b2039001a0060b045640d40c036140701c10741d1103a40c1d5142e6540c0188662400600500340c844129074034600c0500c01489860116 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 652577985 1250 652576735 652576759
    0x120305070812191401030201171801020a02030711060703050f031008071401020d030605060f0d0b04050106020d021902010c02090a0f0f060f0b0f0a1b08220902090a030209060609 78
    0x2c40001c941c00c59081c0e503a504141c41d08004c901c030503400c40e043c0ea42c141c44a101c21135640c800f585005070010f02c8240d16124401a40848000c28801014803900c90360156648101c40d003040c2003045034049026000304010084080404d900009682e410703407919441030795076100c504120000042076005000c8902407210000b55269800030a400710740c400382c0070b8800701030500c8000d4084480c68860203030082c01c104140121310070f450006180c0c45003468800580d2007004004201280d03000d030882c101503444807052928440c2c0410805014824800c1c000142d10703100c1c0d0000300300c081000c1d00203000d179030000042502c42550b904103504507000c04c00100a017031405d0000310098840d80c40b40c3c48c06030304907034400300d201102c2408031001d41a50103941c1d403410070280d4040b1001d1403a900c020700081d1504501c0030005450000820301c00c04460040c00b501482104030701110711160340521412403041150b80f0003610f504500e01e0440ea011201e807000741d034420740440c500344500c268103030f0311504401c00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 652579235 1250 652577985 652578001
    0x8010506010e030a0f1101271d09030a03150302030a030804060f09020d1b030804030602030f070509130b1c0501020310080c090a11091522120305070812 67
    0x81a80304903400da0301c0750520060a414107031030f014941c1018184a024500c94000300d5102d8001000200041c0340146500c1c509861400c01202d84003002c03103504400302d1081002090090300124031910101580c1124144014502c1e1307a80f1841d10048141600c1c2d444031072a035100021400b004603000f509950102199180c010030000044600311040c40c6800e1185982c1e410601c562541a07601405d07100c180182600c440040c101084030001da400e000e110040300040400780a00011031141d4005130320f03070034980d40325000d601006102c00100402882151007a603500350540320051103002001800c00686408198400c61100d00442403880c64030022b002c200c0154011032240689588016800d5210706480343c0304c54940b03c45551044034400031034092074296005184441515070700e24640582ca10126032a091100f640c03900340c0b2008076042004003062400c2841d10103c2444404120341002014403191802c1300d0050100280841c050781042512811603c3ea0408542e80300a24902800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 652580485 1250 652579235 652579241
    0x12007171006060801080304170309030307150b180f070210290f06031b1612020d02060415020a0507020406090606120216020d1e03090501020c031c03021b01060801 72
    0x4220501e00b03142400c00203200d0b10a07400342c0d041c1c2e24040091494103240856421121320941c1c4044010b00080014101f03c2da4108000d00d82c1500c103245410b80344441c0c6115008031138503031000c00c0c001e82c45190907400078031a900c9501c1d4808480c0340c1580e56616064801c070b140400000c0c400c511a4075040200e07082c4610f40111a550f40701c1c15207000104000c032001d020090384204c481301d80015042c07000c503080034003070b006603490740386a0186642810040700c0c580d121a404078600307645140c50b00d641c0310502d560600800100c68400d000603c0c4501381941c4142c0454650f600d0303000c0c0583c0c0441d10002d0300e8410012035210030b4004005011054403940c40340003d102c0c43c45510040380d203001c0030445a06842c000d8070500340c928122410036000e60707024809451075009085621101c072035400c0b00c00300f45003410101c17420700959450000c42c0c10310f00064548210740d148244a64001502079840914440001c031100006260240c2ca4144c11041428002490081003c1c0355080070b00200d56460154 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 652581735 1250 652580485 652580503
    0x10e1314150702160b04080c04180b190c020105090d23030f090106050a21060b040207060c0311070503271018050a080d030b060c0f061f0501200717 65
    0x15104c81c45603881d03030740300450302c41d0b4414112280c200c140c2c540d0746403800e94059500c2444d814040f4500b5009a540d0340500324044903844141c901d1060700c0034210105104550a600140c0003c00240c101610010760351210000d28030200805001d040c000f55920046850910140302415070b120700708000301d0032480c5001c0343c0307400c0f1562821070002928a04070300c041c402c940001d0b08154000745049a0410750006110090720250749451034180c03d51540e00c01492010f010f003000150800c0166001020785071004500705401e041403116801091000c01100c100c8084074040201180c20032401d4104040302e01e50280e881507900020109440d000b02c022104200811805d65001c2d49a50400ca0300025601a0f20840d51042010102c0c440c001e1b031160f440001d00810542c14544002c07199458910f03c0d5202074042e41010b028003407100460003d5081490380005900d01050524000801c503034030200c421810b02c1e81d664012003100c00c0602000d0040c0c0309078a1002c0382d00a07074050803546c9035207403 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 652582985 1250 652581735 652581763
    0x30602070203010c1b120e06030403030b010221040b092407050c0102030f03010e150a090209090c0304111e0612090c010c2015040617010e1314150702 66
    0x10a08508604c0c2c480c42d0200e550801c4000c900007001529150286840e041181420511040501c07200c040e546100c003651143d440307580e002c82d602c3d01d404002820020600c00110b00f4a060003891460388451000790780540e103c0d610600c1c2c03070300028400640280d5134584403074849040300c044c100e030070b071114401040858040c0c0c00b02e403181d003100401242d60780300741050034480c101c1c01d00060240480840c0080d800041a0b409108041c4400e40050f41c3d0714520790004c02091303030000d0140804d041602c0d1031a0b101e15443c01d20381c214906a1074808018201d031301460b100d05415012440c4000041031400055100507009a80310f00001c100341c48140d4080d03d05000303c0c8501d0501905540c03040c0501d0308220f51004044083c071b542c4010b50112420403400c001ea11013091080c0c8210b10705504050300080c1103640e02c0100c400e50035000c0c6811800c06810a56030241140d04200740e440c1a01008030f8226400b50345800e02d9840c074082d490501080d0048580070f00c078501c052007005036002070418642821 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 652584235 1250 652582985 652582991
    0x20d020424090608060f120d080a0c09030507050f031005040503043b130f0501060e18150a0204050306130203010b0d0302061503070b0a0f090b16061505030703060207020301 76
    0x1800400d860240161054100040c4544001005c07420020007200c1401006040301051400c2a04d0603402d1000d0000c80400207041c000800c0100c010500403107d030900075050039000da6045445260b101c2c1058081d003400782507800400c0c511034604001b00502c0180c0d0002c10002810140340860b260b070721611800c0c5980c040303200d4010b120001d07016020b0615002645188801c001001c038004001d40c020a80e41070311850820711800b14941848074459580304000018480f070511030600c801090103001c1500c1c1034600780403030b415103200007905262412440c036113250070340da00150070020340300f03a40119801d8021142442001d48100e0303031840600c1d208800a0244901134011f01c8210510720002800590110300412014954240103002e8020040e003603800707035500c803425540582d001c940c2e1100052000c008040d04690302c000e25001402c000310700e261401085c1c3c000340d10b81c032408031000341c251580c0d207400c5002d5000314010341c0001c05010f429148c51950300d040c840029008100164000d501f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 652585485 1250 652584235 652584299
    0x304080d051323091801140a141b161502120718050904060b1215010902040303050d1505031902010311030c120403030e01050c0406031409100c0201020d0204 69
    0x10750142081020318000e5030400450583c0c801c0000d2828060003821202016003440303500301c0d41c21b00585119103020314100c07215061040a0400b103904100c5081108601201803206151956840070012150216116154900300d8101002018054002800b40a03d030780214812130058003d0401e10801e0308007210b450366004002e94608080000f61000107030181009e01c09031802e4102550031901035500050040002c3d00030401603151a444084503034410750b1507540d91410101840d0140070410700540c10705141d0b03a8081e240340664024403041c281c807191110403c200d00c202e420000e117401400c0380e110600341d042107030449035002c0301a070009080c518007507000014402202c1c06062581106440d0080c05441d40710211009041142010b4a503218825201c03400d000d02070250905056040d03440b0320700400034003260176410b89610200300403010040b00040100d0070310702040d1080408201110403c1c0101d00921485d01d50300b000c0341c40420081048106c0e56965550709065246e06800700da = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 652586735 1250 652585485 652585499
    0xc060c030c021207030203090d0b091e1e030d241208030a0207240c1b0515180610080f0a0b01030303090f06050a0c03052a0c0304080d0513 61
    0x7481c905008800359001201c04050000c4a1006044080c000d2040d80d0030415810700044410402250941d80c84410000740041d54800f80084100003c0113a00299240341400c03c0c2d603212001c1100500e415400301d04994003d580c248203e45560200e200200580740500f4400c8020984041081520445040f00440c0310f0b0b034101851200c2d5604070000c241944d40d0b041018010758441082150851079030b110b81800e61480007000455148214804620b900344590700500031440448803c0d240d0b61804260004900c0102d840725030ba501c10143c1880b035035110444000d4002405406194911811040081d04200c0f5140501a28680b4082d51103500d06800b2003030f0760b10117014024180d40c803520f0042001a0180d441680c416109541c1280c41400c1901c0d44000c4400440395242c14540320a452084140c0c180704403a48145c0301c108001240b580b901c40407800b159110300c0e41502010008040040d80c104005a800500823802140c0d21480700c0c1e1802840307070b0400145e0041a410f9020041164 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 652587985 1250 652586735 652586741
    0x30414031303051c170604090503070503090f01030204210302030910020105010e07111507030f02070f060b0a0b070611040312090602060c1e07021807030b180c0909150901060c060c03 80
    0x2146030703a6498007170000d00c0314900c0d0350b5200544000c1c0e100342d5840713120001440c217002610070135000e01d02039a100c110510030700000200d45a0894101881040244500c8580034140913802d030806221404808007803406900c2d600c1420003c40e44440580344e102b404580c150061410b0311603008090740c9588030014192006050303210001210307006944a00c0340d01445400d41170b0700404510f400f051440c0ea0500f810101d031300000059680c2882d01c030b002c005011141c02103186800302a41d040f05024581604400d880c01910750003030800e5110560514450307008c009841c0599000380e0104428450644007030869191445200058001c50000492a02130101900c0c170351108104200c0c100c40c01d420800081f80e1040da0100d0380034100c00c40e250215050880c10600c0760300c546e00d0003d00d4004074030800c9022485410007080e98003500c41042100d00084081e03420321b21040e00c0c140b0480e02d4091010469003020b1034880d80048031b010000455903485140a0080ca0040e0070810036240000380c12030036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 652589235 1250 652587985 652588033
    0x7030c0f08223512040e0105190806190204050303030c030402090c030402030c131e0507020f01051611070b0a02010f0b120601051306081b030d08010e0c03041403130305 74
    0x71402200f02d642850041071494444000d410200b590750850780319564510729045a01301c000c203944410014015424252031100c41c071030401101841c1d0603d88a122540e42e000140500030b00b183e880303241fa142104e0398064401a1200405491716413918101311036050700704031000d0384030b001100c0124005010000440e03010715009030141000c13130700304402c1c4801e050a40d05070410352903032880c1a016080c8061003145104103816030120322801d00460003072400c4940d0114540b240d140200740440d03880c540c101028007900908200710480350111101c0d007410050344c0075540100300001d00300e0019606510119040510720400c018183c0d45200348101e0341d81e6164964519403004005001500d0712070f8140c002181c402c20045141522414468102007010303070313540c3c082c04181502d40c1ca1440d0034402d42c0c132072032054a002e104e20344c03400401c800707080b001506003400518008085030601110235040f502a16100080300c0d0303140507189603002d0760945880151500c0c02440701d00550903403c402c04421b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 652590485 1250 652589235 652589279
    0x10050f09120f01051b0405010f0c060c030905070801231503030708030106090f210203160303020a0b2211010e100c020a15141809180f0703020607030c0f0822 69
    0xc2811f0400d00195a445507142d0382000340700640306601c00144140c052481c52043c2e40e078020600351590701d4242d1501500b908810b05a07410860054a0700030031050000003100303950190142a107403035a0350358000440040d100e030140400640c00051104031f0008504885d003991740c40c41d5450361103403a10b40f00d0a01d801501c000301e02c19810b030005814105d8030002440d000400742c428403110640d0200d183e803169030040b001358203e404180d0611091000e00d5601c0300c551800c40000140342801001c03134411019004044003041050103945074850441c00e8408800038200807080c1c402900050f181880c0c00104912500020034085201d540545102c40d5849240e1038801002071806803051b0390703800404001c03407480b10501e8100880e5540c00080d074060504101e040b0303030a4491030b08003170800009507003020140c0c1c080c1c02d0800068499008640d2441e03013501c3d14240d00c0b4418034107189460079400d07015004100c0803030348000f25011506003919003c400c0001c200c00958891600c1c07000c07d414000c040b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 652591735 1250 652590485 652590487
    0x308030604510e04020d030512011202040b03210708090405011706010e060303030103030c061407030b010e030a08030a0b06041211011d10050f09120f01051b 69
    0x1119424203030040d440b880d050202240c015580a000c100341200d103000c01010360581c00946030200c0e440d01e540ca0803181d024400790b050550605207000081400980002c0c00f0341042010081410b2161040c2d40b4524041681124556550b81e46400e09e022901d1081c1c1c4968030340070641d00d036854000307500ca11038050071400c03c04540c0160131b000003d4000301c006030741000040090604a548034414140a8070801c0050480328000c00305451034018140c10525140d44500c003800308036a800401e580c1101d034507252003160460249002c1005d441c0181a9411b5042c46005200c9066007513009007101d11400e030307075201c59120b00e40300b0107a40307090114000d00106410004170b8103a1080c0c1c1c001040007000540300701d1400d0741c2c89030b0141035903407508403d441d00410100c0761ba41540c5d0222440c52032451295120048041748000181c040d0103880d4800240f10000a124510004060030b076811038400030300c1c203066901e041d08515121a000014501654a800009000429050409404024014121 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 652592985 1250 652591735 652591741
    0x70e06130608060d060501030b0a1503030e09192a0e06030a0c050f0406031a0901030302061609050604081f020a200109081602091815060604081e07050604030803 71
    0x355030300c2002a03c61500900040d0b214000302c1c0c040e015031802588248c024900500c0c0401d0317010f08a440904008414101d028810008254410f0382c003d0452030840b00900907031560094614000d901122141c80307181043c1b04100c0c2080924007071000c4040121118003a500c464404070f03a101b640843c06070348485c00f8000f103000710000d5882031501c0300590800c41e00c0c104803d80c400c40b036070300694880d50001340c40301c0d20125000e880c21086e00103158240c500c5a99941540e0b400307511140020301000e80048040e14400d0340c64840c14075800280009043c1a44da1502d4400c01074541d41c842001d00c1e00c0d8000104900d02034102c074402c66011045941d11443c3c6991440c920340c204c851034502c04a081c2d900c9001e941c0126940000a03c1c0e807071080b2110800c44c2019106000845c440104140c2e9400c1540c0400303a11031038040380046096400b00308100c6240e4445001404500942c1c01c141454030450391091b400103010491008001a03900071207400580c1c0d1001c02500c0e00c42c40c000100500030600c04 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 652594235 1250 652592985 652592987
    0x3071101090f140d140d0905040b010e011b0204060603020a1b0c0e1e07050406110a1110050c0a060203043806030a060e0d0315210213090506070e061306 67
    0x900d089010001e10040480c44c00740c0740d884c1c460035141c810f88072540050341c50325805500b00b14103170010201541d040c401c407034100300040c2035440d648861505101092682c1d100c0001c2076502440002d40c020001c22609485510040085d001800400e000c640100c403024040b05582c80450350440c2d01844880c1003506000b119181590090000901442002c1400d40c00b4407612007917901c83d000ca99149516145030110040c0300151014000e001c2d500300490010200e4038264444031652001d54840d01b002c5c4404004546034840c051104590b405440d0744c40080001c03540065000380d002e81220042e10603c0384038071a20391040702d8400c200c1300e03180d80040c80d9140b54543d456442000182580d091000e6510340c4000d0342e80c4001000041e4201401d007500080c0c0500c80c02d031032000c032110030029041c145450000c108108041010f54051022104d108540d5140d40d074201c500b030300c02006d201284203850459940c4c41e05485900120704521007803d501c0c1002c4090f10802d4010443d610015460040 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 652595485 1250 652594235 652594259
    0x60506040e0a0b0604081207020112050f3c01030b091902010e010905060c1608010911041107140106030515070f0c020a0b0c060907061701140103090b01030503071101090f 75
    0x14015402004c14400041c12a40510010110b0101c920482e980c2e80483d00c001402180c0030003220500030310740340920415103401803201ea8401d900c015118014822a010402100703104124124400c440041c1145041100d4480354100c038032400c203c06480d00c40c3c000e425212240e44600002c01d0b24100700c80300140d03210380101d4030040c1040c1410000142c45901040e4a5807101100d0500c65101154400030100f8030440140240301001c000c00a000c000d540b42091000c107400b05074811522541c03203485512524086901903540b188442c131206442c4003006000e03201d03030f1001391202e0090441d4540380c18090201c241c8102e46561307403c904640480000d40b52540c61440980c1c01c000c802101003070610381d8100909613518038400a214628045000501d410003942281e010131501802c8084100c04680c040790558124881040480114900481c001c10700000d018041c2c030913000c00002440301c040f0040c0780441c040c7c5405214070520000554551880744100f0b40026035200041140c010800 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 652596735 1250 652595485 652595501
    0xe07090f0e011e021c0e0c010e010201050c040302010c05030f040f06020f03130306200a0c021f02030307050d09080f040e0618060112020c160e0a0606200f010606020d03060506040e0a 80
    0x2000d42809035180205043c02c44010000c9185140c0c0800340c00c1f1300568000b2140c240d85032091000744100e161030b0768846894015480001d06000354505003800b017010500603103200f50360980980340ca465440080103800d0445100d6a030150082c1d403600320038a0300210407101411144100105820b1031070344c5600050412510405240500304a800200c1c0300b8540100050303a00d580c0e442070b40583c81d0040004034071040303101104125107a590514419008015246d2111050608070785610800c041c4030701034101000c1c01040040700140041009100401400c1500c0e55102001d07013a070f45503801d22240200c1d05985160444203d40055030940c480d10464615060003880981046543c180c410700d0302d4081070351442c6681e514030040c410b246134901e031181d10104840d01801107034541500038100b680c0b9100042d242c294203111014201c0303420401e03c3d2034820100c008000c00703555014020740303c00900001e500000c3c101030700044e0625188041d02c066981503512201140c03241004400104060 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 652597985 1250 652596735 652596757
    0x60d0f020d020915040f0e100b03120c0615061305100e13020405030d2d0e06191115060d210512130308040311010e07090f0e011e02 58
    0x30701d1054005844107150302d4050070070101e0000d100e420480411090381c998098454a081c40c08082904250000500c510700c0c00036820006180002c9502203401d000f00b111018801c01c0c400a9040200e2a002600754841c190707424814540c0141401003051178070500c101d011503c0d507505401d0045103407041e43c00c42c2251075400c00084040500002c5007010310100324288559902003010003850a0510204036080b040d40b03040080810075044100b1101640a220200e0f0052148110140fa0061070700b0b64100e18011310943c0c490741d20240008090221000100000708402c210060000300040c081c0400500c15214044554421041c400000480702c015240d0140382d248041703204001d5800b40595a41035560b065554441112068511401030030301c95803940040d4012000c80e5210320030640143e030500e040910400b15401d040d01500ba4000090f982e03001c1d0b200c2c0000c01c1101a40314071100100304800b400240c030041403860072141d400c010b40103600e008040c00c03100c501a59004091609030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 652599235 1250 652597985 652597999
    0x12030c0b190f0b0418081c1409060702011a03070e1f0b03070306060e100c1506090c0806030a050c0d08070b1603200a0c0609060c0c03090608060d0f02 66
    0x301c01c1050103a031041803880401c59a110082d14081c01c2c14080c81c2c82c5040c0c0f190354801600115503440001d4802c0110781d080d0341030740b4907100d03610070a241c00040e06215407180031015410640601612294280c50b0000558078041000501e00d03455100c2d0100d074200140508003075131424000d50714103840141300c901c0443c80354404043c00308007000d44401a00701094800e07102e181048015080340c2450300180244a000700f44107400780c3d034000120021800074501407128403d1481e04803581031141950b2061031782810b40102d00d803445075001c590282034030741c0c0d424410384500090503240e00302004054201c0d00079092404a50034030001c062a203a100340314561601d00301e6201d04490310b80543d81d1140603882c05a03041e1410b907041c0903409900381c0c0c1a601031100c102627003421602e4800d80c00c40109200c3e001001000b07000442d8800f020150300a0000e0011140111009141802e000d0084010600d21400401e12511038030700580b00c1c46000d0404903020f407250301e031550060151075040b07134059a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 652600485 1250 652599235 652599271
    0x1030b03030705030304140a0c03080f12010b030603100b030601050919050c04050a060f0905090a240608090a0c0323010c021f140a0902040207020907110712030c0b 72
    0x10100000c0c0802c07405140034540324181480c042e09040c0504400c241141d20a400020201d808462100704407540901140e036601d5400d2802c0200c1e00403042c4000d40c0d1005100005000b0480328001c0d4410442201070f07a5040d03011040030401c40f00c2c911303410382e050b50220b00140b03e141031005101d40c000c240c8000180700401240900800d40b0300440303c50344c0090010400b0840c0d4103040c0710035006041181400704e0b082402103001001409103200d220b104416440201d50040080e0b840300011141050200d401ea40c1c44245540ba81c05640c0b0070034000801040010702c800300041110301c881a84540c40281491550320303030304007149210107140c00112850301d500741004c02c2485080c55880054002d07040c101414043e070001040c08003002142c807424604c0386d121040d19400d85940c4034041c4035001900500f0fa002050080c003136003500030341114021007070119172034000000740303058001d030012190302c02d4481075030170408000c0c03400080c0070a9400380401c0c0081c160456255110b0382d80c0c007180140d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 652601735 1250 652600485 652600489
    0x302070f0501020a0e0105090303030412090f03050a0b07031808030c0f16021f320307080a050a09080f0a12060b0d1b0905010f030b100e090f0105130b01030b 69
    0xa45891011100d50307600003181180311703030464004140c21209080860500080e100071039280d200041c40104182c0250100c510154040e03007071600685022451300c00380540301e01d041d559034070705080d041c0c690901807000a8140382c46405034080801c11701c0740d0340941c07103901d90700c000312a0806040b06050640a00030100001d5411024000404c090801d0511184050040c441c000b030203100c00c440d40b0240c4070126101160007002c200d20b560342852038242680c1c0d081e069808590303625004035883c000700000b4407180300c2d071103040f00703004410405c0304200715224003240c001114040e000003490100188650300c0020103860261400c80028100107010700c403582c181c0c0c4111111a000000056070200d031000030082e162185142c081c541c056508010461414050300c0d100440c402d440c10400e0124460b020307a4441d0700054481c000151195207450038020000d0b0105007250500b900880d08600021b1198242c01003160484102a00400388010f0120250016180140100d0b05050316801002076603 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 652602985 1250 652601735 652601753
    0x60f0c120c07240e13060b1c14240d020409081201210f020d020904080414030f060105060f3c18090606090a0306091b030b07121e09030e01030603081801030207 70
    0x10000d00440d00c40103419030001c0046807241278245104140d541d08004011102d14980003646600c0440142c0e40041031000581d001c004040080d08941410002000c1000c2030020300420a007070005904d1b16030300d5040540311749841081900302c2d10002404030021035605811600c01c00d0028200c922201e00640108000700c101380c41c1152030007800079080001201200701d880e03800708100c0c098040c202d1041d488075540c0340c060080d10701c04e9100041e041c0c1c642500f1009c44001c0d0402035255107007140724083c401e100030710301c1341c2a0170758294010030321103240c0c40181100c5070511040300358103103580702e4014412800d80c0140125000003040040962664503201d1200c001d500c20080425018240e14085480502c1d001d4100003500170a02c06100248018004543c00303511440c1c03100903c0341c00c900c210003403e00e00114058109000c11882c190710450340107440c05d98000d864070340071030b0300d90300044048645a01c0f001d0a03190701484007620845054101790200d1a052401504102c0035403604081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 652604235 1250 652602985 652602997
    0xa0f08060105070f051b1903060513021f0210020406120c090807030f1505070801031b050a0602060601022505040b04090501020a081005010e060f0c120c07240e13060b 73
    0x259174090f03a13403c0b00c0781d0411009503480140036141d60005160641da0304001c0695800003c05a9440f02b00181945507914081c1115580080c101840041d03a5000008482d07103a00f4510014028804107625100d881e0007105c04a0f18280e40e40c845134440c41c00050002e2800c0c00b80c0500300030800100040c1c03642d01304034220245006682a09102c151481c100c0d600c0001400c00b00846400c0000304082950030445060449170068443d07802a1300c0d842d22040c2000c900d80069a001030307107078004a0180e50024016210301c600381c00302e03010125051400c1c9042c0c842c0c1800768866070807514003404242031640001481d10703070103030020400c3d40c1941d50f000d0982c0c0180010301d002442000401c400001c840004000401c1c1c01e0809070071030790781c90011a945120310084846000400100c0c0040c45c00100141600c85c080c0034071180d207400400040940f900824454900391201d03440c14564030700e004480e0000c884e4000e48031911400300c12000d101e601420850840500c9980c0e40c03000802c2e07008103000b000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 652605485 1250 652604235 652604243
    0x5070f08070f0302030c09040602090405070504140a1401050d090602040801240b030f041b081e0105090703030f02070b03150103050c03040c0b0d0204180f0c050a0f08060105070f 78
    0x80c2080c0e009864980c0c540e0000400c0e005401080001d41c5000c030389003581000580c4c810100d42e541d820f244001c0d100711504a80c00c14a40f00812052590080141040e6000c130300184d01d180745081c0c00c1200210351801440840040d00d20505425030040e070087c6084036101f04003155604054a4660481c0c005601002d00359454460318202e91500c1d21030040d00c003000f4440040890b0618540000602005000125005165000c64148001020342c1805804000c6002111a4540d445251100030400365040100701c0c10f2100d001800741030188034413681780315009011040c81d5031403c50340c070300c0c00d002107100798000c6060204154121038001c5200b40e8050040400c45081c1c03000040854100400e6001d5943d802e1090100180c05192044101c3d152080c0d419200d102c000070540c003d200d1351b800704480003600484406500d000303420001c61100d41c084104034210308018140c80358410501d040c00011119115801428040c0d4400794000c441854594200031041da0345c40500d05c1400310540d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 652606735 1250 652605485 652605509
    0x31503010f140f01081203070c0206034803040c08060708060307060327080c0d090320060a1206050d0318050301060501121112010e042a09180507 64
    0x25040b04800281d94021182c8034600c009585000312264030340881c004003038150303507001020504803441001c1c02060540c009042c0ad580c2d040000b05400c0c0950750414030a43c0c000180d400d1040c0141605000b181d0302100c0f00d01d040c00b071000a1000c07c80f940010070032255540441c40c042039400c1c00300f020720301c290840c0c3c0342c3d680c40e402c00c282014a04032040e0300c960b080504040e5030b9101000d1210a610031000a140790b030b5181c000034605500300d4010306c824403c062180754080ba6181d540b010302c180890340580c2d00c8259200d40c61140740c0f003107080200101d41114040150000c00b0b80f02d41030000d000c04031407000054140d102c00024006014540040d4000341605c10350b4440c0c41a194590002454114000c02240d803a01001900b40c20340300d0707148040d61781d56140c250001d02004003100c50680c4050b00d00038107980c45095018111b10156801c4d40e2280700001d080748405a1b4408103808888036000c803101041c0b800306408041c000d6581c4250301c0c03241003802000011820800b0402901ca001031903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 652607985 1250 652606735 652606751
    0x130203070921020f121e0309040f0c0917010608030f0c10140106030c0e0904210302090d0b0405032101080c0a0b18120a060506100309020a0b031503010f 67
    0x80b40c0040c508551410082c54203050010042c0d96190043c0141a001d80e45041800411a841c130b0034800102018010303000034034800b0144550101c020400c905003160204580145140c040c000c450649584034041028034400344240462100d1002134001440c00104045842c0c29086065411184000c442024042151100d40c03000380040846c2c1c002d0200100f00780c2c142d844440840d19010b200d0340082c03507924110384440074416100311428440c06461000141807a191134074504400c4040c000f07007800d02c1c04011510500c68004c844240702e000f4005414888181c407055a856009803040b60144010896042111424240c0901991500801260320740c502400b250401040d10181803060480800510048140070251081c45207400f41c10148001100c0100c1c45507104900d4030744d038a100c2d01992104110003600300381e200356002d8070011082c088204080d015a001144021350002400f0804d100140009003c0c5034041d00d5400500d2030341220001003030840300148980b4018580399541 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 652609235 1250 652607985 652607999
    0x601080115020c0f040f05010803070b180c01120b09180f21220f0305010b1c0b041118040b01120507031209350c010f05091302030709 59
    0x118a0040841c07003000707a0741c0303000d81d400203485000c0c84000d944140c520110140d8251650307804911050500c840401103035841d0200180c7e00e8114230b104580b41507030000000c2410003600f2054854000c400000c2c00c0c03106083c0c0054481c180721103442d5a510b55186d0042d01541d0f0b88000450184010321070f44014229a021028100503c07003200f6060f60740f05540268080341c43c1440316003415540084140c6071100001e28164401002c0303109010071030300e44404150801c0084038a02113030300c904003c01c8003148080a0010100d603146055400f59a440710302c1000c00d40310801164041e114000c0d40d1012002000040c4c4a034040180441e1a8101c5608100401c0303010300d1100c0c09445d441028414034109542c1e840e607580c2181c040103041041b006c0803042c3d024040c4103214054038402009803c1841241060084440080e120b11243c1104490101d005070010490040500041c2c1d6090107800030714005aa01341d2103801126040106032406040700040e903c00f80d80100961759402d509280390100b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 652610485 1250 652609235 652609247
    0x100609050601020f070612050c070506010e0f070305010f03020108070215151201180f0510090f2001021b0607021519030204181d15010815090309060f0403080d050601 73
    0x8065485a58284406d03504519505808082c240c0c011a1031f42d1112280701090182c075030028402d00c62480041281b00940c064503103e1503840d80005403d0361070503012002e8502c01e106a500419039601b081c0059403040968603031100071401140c10100030518050641c0e5811189401c049070b0410074054185400036030304407140100c000a0040d03110ba107802e4030350580b95410080600a1031001e0b10704100040c0154100103000c00c20800801e03042c0c4c10552011104030600b16021800050414a945428501c1192680040e4010205608003548204010402480e4240c2c00b060906c481c50050b644d040c4220240f1100c100700756200c40400f0703824850074110580301418580107000c02d10143c04c104501c6041d25141110214555000101c03c2c50760b10404aa0503074180209582d01c0f208682e03414a440c1286d02d03541c201d800ca00e680030540d0940c01019295040c0c03d4000300503004543c580b6802400780401d111260905d0255a0f50750300c0c180d41d1003e00d601103100e03102c1c02041140d6030049 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 652611735 1250 652610485 652610503
    0x10309051c2007090b01090f0b03010f05120c01030c020c0d0c0305010b060f0a0804111e0f060a020c0d0206120a060501120908070303090615060206040209100f030305030910060905060102 82
    0xd5000c0442011000036180c85441c3c6010301c0d0019076036a040c0c41c140381e22890300003000309100c0104c00c48064032a02c030820107074400d02402c41c4200d1194000030311800c0207131621440d144601e000d400501c0c0031000460152881c10000c504520803200b41d110540c2d41d641454803d148a40742c1d40f040b0518520303185d820341e446085401e2180b442400b000d841001f110003141c40341120340c030b001904c0b641c0f185000403801c4c0703491000b0358004200b0300c5104991085c048490200d0002100c504002601280400606200700b00e050001030f00700c00d609084c542800c0c0d2901a00500c000d16507420180182c0010321140030480b4402941c0d03446141c10070055070000a1020b40707000d0140709110200050322001c0306031040480050815503184000018040590300072107500c0310b0030403142da0440ea241d00c02907072500c00741c4060744520f80b0140401c8020020400103800c40e41e40d00e555288052540e10241d03082d801c0104140c000380140300c0d444481c080c0f60321440c0081c0051040014560506100080c070341038540e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 652612985 1250 652611735 652611767
    0x40209130f0305132312030418110906161106040308040e1009020a03020a090e011508090f0303011517010b0d2c150a050f01030204050402010309051c 66
    0x1003905101003030082403200d208503090304142d5644d58078040c078810b00c500b041d0b000d0241403a15044424204c8204010050701210071501c48004101d40380c401c680b03071b110f248502d01170741d003110041907100885e58100d600038000c4040b0f15410060000040b4040754089003005031032030400420403040002c4441d0710301140d0010380b882c90030a419a65804124480d5000d4548511894000186000000c2c030b01c0e48090640c20340159100d41050a0142c069040302d540040030402d041c0b004103102140203070560484142c10521004103011660550b0140e801410744449400303101046e064240c0100f005500a005120fa80841c2640601e0014441c5481604804641c4100382c01007021701d0044064680107050303020000744001d00d4413800d00401001843c0d00d10320a086c440360380420300000c43c6043d15000c441140703010a0b9501281c8100725001160800b83c65107029005001500b483e601c85c941c40307441810000356a203031680350145000540c80c00106034a20308080d00300d082c0d5005034401401030300e03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 652614235 1250 652612985 652613011
    0x30e1926040b0a0e0418060e150c0a080613050408040f0b07050d08060f0a0305010203010e0705130e0a090209040f17040503120306060f030a05061c02061606150e040209 74
    0x20300282c0000b510403640c00c1000c00505405031189503032a80c2c44244064003400004e0114207462034031202a03c0780135144141801996540c0080f41c540c526a14420140f54030340c90f00e003a135138070070544403c840030780241e0308118406500c04541c406442840e024900440070140c4a83c60000c45000086550f000400d48150a11040b40002c42c0000c3c0002c0d07481003820701004d140d07250380c040391240c1006002c16500980c000000818050107600a50594500f9000d6504aa0310342006491610409a1000b428a480c0008202d00d403200c902e4190009c0c030714180440e2412990b00083d0040a00343d801b0360340c0d040401c1d6034404100e180304608004941e0000d40c0c504091403c00001d40740d0604046039a00104000009801c50f540c03502203d54800080c417000e41c0b2824200c1218000308000c8030350f64000c04688403200184600701040307412181e030092180d442c00307240c00700281e08450090012110162650498102134102c040c140707000e0b1121703501c00320075442c1c50300401020710b001511710412100 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 652615485 1250 652614235 652614239
    0xd330b1e0d140309060a120e06070504030b060f0a080f01150f05120c0d3e0d02130e0102120c0403050a080c0a020405040f120311040501030e192604 65
    0x107032046100000d0350403000030300061541c020036608500c58030800a44c4600c0c0001c1c140981d542001e210b01403042248400c110301014440300e40d42d03600e019107104010400c14041000080e5a2403456503011801411078010030840384042041d648070394000b0342181d042900d0030190450300344a008803007401b8600325984589480701060500e505802224010503415180400b0200708100b484603288001e01469503402d41e5051118080344182640f502c000692444003d280668410144045040303811072480e10590304200144144c0c40b0400300d03040070340710060744a0034105114a124081c0500300150341c484444558005104000b03082d8142c802d0180130a00105000080d24611503034000c5085a582007080c0a0030701d000501e84000354000d0801040000300400d4642c0740042e00d1040d06081041c2c48881010303019a43d10b0718011303400d18410b10081049610039003020884c840070307900b07440201451a401c3c460107c0f8914042c0d0f00180c2c2003542a8803c22002080840c0d84001000312341414 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 652616735 1250 652615485 652615489
    0xf09080409020c0a140a03110c031c0c051006060e0105071e020d05030a0f030b1e09100801050c0c070b130e0c0f0a0f110c0d330b1e 58
    0x8095030241000196000c1040c40e80306600f08206081c071303038004c1a00c07a0115a8512040d566142490080740052684101e50303500d0200021260b561840081c003504420780c86071010202c4140c0180134404000700d000040e800f2070000e005294942c02e0b44000800d00d20306000d006040c88000c000a117040007010003200c1c0114019400100c04100c042c0f04601081d011030000400c4000950703400b6041d4000050583c051503046020105c26100b980c4082c0078121820702046502c9950041e07181d0044a4030f801c4503a140360075100c90358011a85054548041d132200c0e1114212002101c400d1481c81c00014065103010003003025000030b2881d045564500709805042c14220744081c400c1a00c624000340110b6106950351056034803850504003d40d40302d49e120100103113080000c00598001c60403070b121141c500000450f040c0518071000e083c65504601725520036104000421040c0d54806068000507010704404003c200304000001c4081a00c001480420001c03808420304110708015800080c1e000d6 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 652617985 1250 652616735 652616737
    0x70e1002030f1305060406030f15080a1103011b030617070f06050c150408030a0b060915070f21090905010e15030a020919050109050408070b07111006090f0908 70
    0x3054401c0c54640360055500c000003d0003064128980c07100c004100400d20302d40c55400641d100c05015414000141e0000482440901320301651060390000030209000c14140d413140c0c4141980507000003002180c0c59244100e005020318a5000681c49100070450b04a00302640b0f030310300704218013802c0360525140c900d0000410500c124410b110002c280008503210900400a421442100480e0303145010320b069566680f045850f80401c0d407a0828290241c00d2010035034480c240003178003002c4180174614440314036800412007100c035490a030090000051080d2010001c02d040c82c030305001c8040c11910081c1035083d4640005407010b1030f210041290010715581181c02c5903c9281e41c080341500000841c1c00e1082e0640080c4d004840c580c01c1c4042421340c0b08480301001c40311042000280d884003a40000d85506032406001000117118500c040344403003082580010b41c508010500e242003d000c42d0800c0282d020740d80442d95521010044945207025610036080210b104115400700d6507199825 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 652619235 1250 652617985 652617997
    0x91407090e0907080a1410090210180909030905090c0c0a080318060117070e0108060f0c1b03070b15100807020f0703050a060e03040608060616060f05070e100203 71
    0x4090703070200840c001980900844000c0d003482800d03a005020181442064024140000c40303903440743c981d00f804c41c00c4803885425002c42c1d00810503205155100800c45d907034203040780c10003e0740301d510100240035a054401c40d080c80c1d04c17946034145150b146c001004039110004103002c0e00c07070301d040001c00300005001c64082c0f406d030341c0301081c0e03902c0e070300c40b611041e03d41e410f9080c0038075181c4140000841c80500e161451031115030900b08544105071220040e0465080a11075001c1c15440000440c0403520103c800e1940700d0805c040b0766081c004841c6131140c0403105852000603070f420000d00340050121030701c0e1503a03104203071802e060361050325403012070072418106100d401005800313404608014070034081c010040c1c0d08442101d8000ba141d0501c01d490307144004c070071194140f5004480070343d10b82c0803054404403070341c649903003503d81c0d100701c14815258820890794000c4083c900210f4005003a600c5407040c4036000f9030700044e8510308150302a0a000f0254001841902e04810750040f4550010407205 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 652620485 1250 652619235 652619249
    0x40b070513210204090b0907060f1709010b030601030f03030b040b030c090402040b1905090a06060f110a1707051203060609041d03120a06060507110402070c0506030a0609140709 78
    0x11200581c40702d500368021100c00d009501604010451050101410750140504400b4040c0c91a1507502c46007503c3c04040c0d48400008190010000d50002ca02c07902e503580d100708003400104030320a040000908100c4c09800444000300f5104000080c03540c14425402003420941e02081600c07991000240d442c1c1580014900ca040741c440041c085480b10b400120101f000a001050884d040c020b03501400d02d01c502400c0c0c01400d03c140018182c80850042200300c48803600d428080d90000d482c00c540c6010107e526003801c2c801d8041c01c4c0c00003090700c00a520701c444912030701602d902c03203460b04d513041243d0107100310403600c42402801103e0b42c68030100c03441202c080340d0003e580114200c800c0c0000600801003869400049540203101c455482d1292064800321400c100d410b441d0041500d190084030406048441d0000c000a1a800e02e68014048140542040d66580e0341d580d000910981c001ca0380544402e440c1d6400f00692030582c0a800206100540618242e2401c0c0fa401010b103a00352043c01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 652621735 1250 652620485 652620509
    0x1b0d021609091a070c030e040513080f13060801060e040b0a060e040f020f091311120405010f0e01020c010605010305040b06150d1406090117070b0c12040e040b070513 73
    0x7410454100c8183d0069003c142c1c5240c0b01e071500e040080c000e0305241c03405402284c0500c0040c0301d80d00c0c00e40710746442000344091484c05904542c84c2c03840c49400440001c1171015040000c04003c07121410020000c100710303520340f041c0d036050503001484141984080d9000d241425908085d540c1d8071402d52003640c6452500066200d90b140014002e17010200003080d910784001583c20b41002c0f080300410b002c05060310b0020b0300c8038040926408852007088500240d450900500303003001c02004d9201d411900800002c2051141c0303e02c0b4104482203550075000301c0c0e40c0001c600501200c2070003547d00614090038100820301e040c0c1c42d2114018802841d403407003441d4014804046080700c00c155010990250030820002413140002c410402c0c00f40d40b01481014448000598500c200c071904603110b0b010001781c40864039203003640c1600c0d00300703091038003444c0122101002001003400141005240d602c2c135800241c05c003800c1000c03070100007500710740c03c0141c200308503d2241c1150b218402140c024070098 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 652622985 1250 652621735 652621751
    0x607030c090512010207030908060705030a0b040615120614010804080c0111070c03020f06040503030a03050702191a0f070903080904090c03050604030206012403090206040504021b0d021609 83
    0x1107810558036001039901101c88905201c50780015400782c0400f41c400d4580c4a80e41e51195110760340c0c2c6000300d8040001480c100001741035010f00d03801c403034000d0381c020704003140786074803110400701c0e81302440b5410000a041d0405803c003182c490113400024407401d211100d100103420002025401300a00107007000c0000100386074010301c250b0000201250654450b621050b00d441c1c0030703104803800c1c4020f912907201d07095101130ba071074807100b11400c441c80100158074254110710250040d040040511040d401091034415494100c510040c040314030407100ca80c0d115001524850700311801800c095114444603040200e2319400001182c2525040300c240741d00c500240f0300090280070540c2005004070101d510003c204480045c034a40264802e4082d40d00517078139000818140030b400314100c0c83e4a052010b0b00d0b4500c500070b0780034030400d50000d03041c240f40c99140e03404070f000c0e03034040301107403550b000a00d903491038016040c030241100d285503202920900d80010660300c0381008034010304c411141ea4103030f4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 652624235 1250 652622985 652622987
    0xc0e1c020a091803180506090f0f0306090d180303141b030415031a130f020705120301170601120311010b0414160801030f030f1704050a140604050607030c 68
    0x16a00100080320b0140300070180106800c04031007020b242100411400711010b00110b00c5c6409501c10703600094046814407540d08200519940410001a008400750b40c2140441d1824000c007481850031030700500581505802c010490002042c0000250048440500000b81e00c240c00080003c202c4803d10349031001d42038403075440220f1409031400c0388000107001a806001e55140813003080240c40401401c100030104c0c8501da4500c85003d540203819000101120209911a491080105c0d2005092000d56a0303003520b84185912002c0440001200402000c101c1d603502403002201400500855450100b42c4059101100001003d100240c400384600400960294058040c02007007800f5052120b1216903840d8000d960b4154a451140311241007240a213240a04a9901c0114241040850345040398610303841c07a07000e010040194820000509004d007414021805400a031048401c00d29003820501e10b0000b520076540c01403001c10000c40c1020400a600010600b0042040480341d20 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 652625485 1250 652624235 652624249
    0x603020a18081c02030316050a0903020310090b060102070e0408090423070f0f270308030906010e3402070b0c0c0f0d0b071b14030a030c0e1c02 63
    0x500082060041e440010b184900010060f5080340c991580e8540410360540490710fa10045510303016952440b00007180940c45900205500c2c10107107090356016860b507002a003010000700050398243c0c0c1310b40641d01840101109150807802c02d000411a107881c1031440308640000900c043c1040e200441e41d25400d4945070080000703403684d02c45c51806d96000020100d60103d050f07608900141c0c614452100c0c080c000c400b110003e0506d51900540c458204003858146425840055a03400d03800c14000006540781b0050350003801070b140039040700c1d810084c00000d032040c0242802d0103e40100224170b0000101c1014005007003820880b00031440707412100b0b81c0344c094264019000941c0000740890b156002140c0c8450115041340d8003441c600803d41003103401500842c001c0c00125420020401c1d0301e0096a006c101810801200030140c00c250325120030700c10114808005641001655200d4254548128000c0b000700342010030240c2810000310341c0f6403018003a204006041851400259505c0d04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 652626735 1250 652625485 652625507
    0x10c060b040f02030403020d09061107090f0213030503072a09020c07030b0a0e060c030c0f0a0207031a150a080d030e030903010513021c1a0705070c08010b12070e010603020a 76
    0x1030565417802c161600a40d14a01c001c01c2100040d42c41c4030114901344038003007a41016460000130080f46090286000003080d0031030300305001d203600300084e5242603009003110008500170340103146c41d81d41601b0300c1e088041c0c5d411400c94090f85842404802040c031843c0d2001075038511740b401611540121806840c0013100c0e0000307010403100c0c070100101c021594000e2080d01003407a041d82e186031680344a4010030300081c4c46115541105100c00d01c04005450050103070101e0074411288042e64a80342c54040c2d03241c0419400300c561000d4100f001045030340c45d00055000050300e540c2c1d1140e14280e41d0a480d80e988440507010552a400c81030040d030360070001e03a440c05000400821441c14502c446a50200c82d17200124010340704001210700c1d804841c44034001854000030300200b200d100d030321070110b5590700400503c24030105101100c0803491600c0c070f070000740901c1400041d090220313404000030800c01081d0741d0035580c051071050050715000c040003811100a4140961079810307148003521445101 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 652627985 1250 652626735 652626761
    0x207060905010f0e3304170c0312060306090703060b040209060d0606030605010f0905040504150911030609010605011b02122a120a240204120501060801020306010c060b04 75
    0x480c01da140d502d040c40d8404100b1112441c02c807040c3c2e10042c01d41501441c41144400d803039044d4a1a0684d00c4414185c2d050ba2091140e5000c2400b41303030045200a154020a070210030590002c568030005000240100e0340121040700100b6443c40e021200c42d03901c04032350200400007901c66103030031001e44503501681c0030000004e01050b2254891090140242440d1140e080040e040240c002a5035000340da0b2084200b9099864502c014101010700029000141c4204c1e42c08002e40d100000b00b50592041c88401486004030720ba40700c1000b002c0525142001e0405211030b45452010031041c0c0c1c20840f154003007224000f00b6241c0510900001d610b410100c480c1000b02e0054081c05d103418082038810410900364450540d414080d2201480708400a6080c2d850141e030125a000010400d203104600e212074914210150840200146030141d070800c2d4050b00c1b40d00c01000807142040000c1c01000b000c3c101c600c0c002c5040d0314044000800d501c0c1b0205010306006d90b500740440b403c1c1c0784c5400200c1c1217298 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 652629235 1250 652627985 652627991
    0xd020106240f03021b03070b22140c04090605151215060a05041805060a2d0902060c07060e1e01051c0c05040618030206040b09030304361104030303020706090501 71
    0x80b01081c03500c6c0d60001d50200d8805142400066131030781c040700c0365003903080001818560110030b991400b4002da91020710700a140301e0500301484680e01c41c090303420414030504000c1828140802d000d610741079031240051144100180d4200551000102102c4801d82d07050280080c0e00d854010031040301d25500080e4009080c050943c00c00700e262190055950702c68070848565695803070010040f91076403004650950f251700002607030503021018441e10383c5508040014030741051360005580d1b5012820100403608176407010401150004c1c075404d101001510303100c00e005605c50745440c46070212030390175041c03180100380c0702602d1450b80d40e035685144500d9001c0000202c0007501414a41040c4500000180c580048400d2030f6003084222080340d0340904514102070514a6112040d0000030350150140700500c00000e040109003801c0d00000300350200c085101c441d1403039503000e50440c0c13038066200c2400c0c25411244ca81c840b80c00c8074101d80d00b615005841e910607180400140101d042c000d481982 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652630485 1250 652629235 652629277
    0xb0409020316030b0901020703120b180f06010908031c090f14151602070b030606071514070512040f0807051c09080c01021509070f080d020106240f0302 67
    0xb0311441000207690260800035130980d1110a44c6090f031003007400040000da2140a2440340e20010b800000c880c80c401450000124243d04140324142c20454101e45550030400030b1100e15600b2041480152549201451a11643c50900a00384004180d104029030b81e5262030824030800d00c44a0080350340c0b2614a0705401091140c1580d9007020751484d541c41c4078540080b5011001442c1003c406401c1d0350080c20807549040240c10346038000926954014100300301c0280000d0300c885090b074922070007200002e5802d5100d540407071183e0006000302d041c814200800f20380c29140300001e5074856807001408100d402c0626089105004201e00144984035840100c00010500d200f903001c003520b00d03500c40031101d940301c554079543c0c400040aa40960040310300d9400700c04290242c2580182401d04a8100a03654501c4403021101c603031051049030041078014030002da080c0150002441c41110164002c1c071502c0c0d110b04005060412402840418000c88255501903015103502181090005074590 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 652631735 1250 652630485 652630513
    0x41a09030c0706080103020d0b0a06050d0501150906360903030c080c042d05060f0711030703030807181a07061d120f070204020f09100905060d0b04090203 68
    0x18204a0341c211590198400106202c3d2140206a048940003014494944400d44842d128008042e000917800c0f900c420703010410381c94150059000a200b50000629034180400304142d0700300301d42000811505000080003004825034040d908185e2401d02e06000416410080750841d01200f0442c8100381001000402c1c59095445084405170705d444000c034175540d00785000c00b244902d004090031200243c1e0444815030301c00e000310680c618650103c140664560000940b690030903981c292194070001460010400140300d4492801e1040d4010302100c0d04551b8040c210303810080c03010081001844a0300710380d94a2205800c0103100980c1da054462203e002900300c50fa1060a054070f049040106003208245190a03441c400865000545050042c2c0d4100300c031184c1c44844290070242c02070240c440942e55510007052242101007010399200030300340a20150515148081c4180700b200a003c1001c1d440e448111000391080d2440083d1005407000050000c08920304041d415120b09041c0400740307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 652632985 1250 652631735 652631737
    0x1050c150124080921070f14120a0c02040b1903060c030c180e0c2203030f02190303021e070609210c02010f1707091509050603010e041a0903 62
    0x4891181011891902c4160b500d40c5003074070800201d0b40400603481c07181d08401c401000410148050300e2070441e031511000703805001818240d9883d4412030304ea80360310004100c0f403038403904041c9849040a0001001600300355003c0760180c0607907210440c010b0b40faa144130801045904a10111240075105e061203001000d881001502291805842500d1103014028028001107e4440740d00154180b001c020700000c00505010f01c0131105204800e120b103081c0a150414800010f007450b581403460800074000410302d60100155041f8220000c0fa51440310040f0304c1c1503030981800742c1d40c0c2e00040d41c0d0a46607451a22048980e003408180303042001019041210030b58001d20f040e150901e09840c0715109000c4001021000c220491584001940501c3c241000942d2034101541c1850341c200c40e2485ca00300c1240c036040081c10001c007d0054102c50654188605081d140141400c0d0900002c00d5041c401030054a116103116400a0100020300c2400b81000742c040c1540c0700e05007002c2d0010796803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 652634235 1250 652632985 652633019
    0x504020a0b040b04030204090201020325030e0409031704020a09020a0302090f120a0f0f0c060e0a1512020d020f1308010605061206010807030e070f030b090a050c01050c1501 76
    0x100345204000003645a0340071050302c090700e20210505103030518560802c8010148a001241980414081c00b8000b87c00c400426420810f241c1d03144282852a103001000030502c07402da14892481c0101c1c02e404298440226002c0b400c10400008850b200d034000289009016071064030b01600025400640340c1d41a0080c204060066408c04115031031391003000740d0000322601c0e58200f50302c03d809010104014801501d0b485000d211908031050980d1214000c22001c1e03080480858114031200619050480000c002041511030341001303807924000c010440f403800301442501c1070300480c0c0c0d01460040c0e039040741c081042c0c20504035510300d48030304034012000ca948100c0d1201d500e02480003800f401d0103000c0b107502c2d514a500140b8659105001034400b0400a0110020540d0f1a1000d400190f000c0014101410404010301451495445c18034111480240001d5140d0050300743c1d1400184006510a440c000c2400c00680b603510109105141407101801c00d407050501400018101d0070304a24821 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 652635485 1250 652634235 652634239
    0x2040f140409050a1502040e01030b0f06090103050d23030a0b12010b09070518030111031008190f03050f031317120121020d0803060a060c0503031603060810050402 72
    0x1003410210800003101d41e03110010b41140c20030079143d0001741000e60707021028415050010308198503540201080d05098000f182d0b40e04030203040c0042031003d42e45641e80b01000300c070003600c1d40d811650b84580742e1a40e5901c004c1888210204003400007000d030401c00000001505880c1c032881d20307042c0280500740c0c1c07242090059119500403070007200103000f070940c05040a0302000302607c80c80b40c1240c2640c441d085841501c0c0c21403042c0c004031f0360203000d842c811007070507400681c0340e003000111225280b115074010724540d48910128041040c14005640b1416044890300242941c1810240d6891146071020a442d0500004220f900c2c0d851f0b600803403005002d00711007000c40d44001042c889902c500c004045400305c0300001085884110851110100030f10710282445041607800f140603580003910889404001108002440c10072204280080800f403030090092001a00c442e0b40b41d02c006403403101085070906400c030159000743c0221000340407420484030b01040080c1d40754010300061714128 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 652636735 1250 652635485 652635509
    0x2150c13050f011103220e0c090f21210a080112031b0c08060c040e280204060305010524030c070c05131e020a050913060e040b0901240311031002040f 66
    0x8544030701c854821608c10030b42000c2140c60050203600f0005101c40b0385008607800300c04801c88140e004200c1101d03141190104008121800303840c124100501e5818803040c003801c000307000141000c5d0b80b160351581180c103459041c240300c40480c2400c482131011407491740c1e1192240c0b000c1800304407003071015500f20fa007504140d460903256040340360158851032180703040458860b0f01086134800c80d4458100b00a00c003404078101e03443d41141075001c2e0703006a4410b4005c265500010000e50519046800040c84011310030102040048192110740c00b001e81b8510551801044c0b09003005180900c91014000043c40800103180d00c403501406425030b0369103e0040e940350781c2d00385416101070090725002e0406450f8030307042011001c02d202c00400214907403c0b506480b1040003881c000c803001c425020f0741c041d01d040b40c500d207400d95004e800c0d81d0f100e60031284c0500c4442501d401000e8030340e1268055a911800503001d00f0602030000e0711b440780340840840482d200140001e100c0c3e084100d45c50031205c04204032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 652637985 1250 652636735 652636739
    0x1318090c0329131104090c1511010b0303040611010e070e04060b010809100c09181b1409092e09140105060a05161202150c13050f01110322 61
    0x1da0b6154070a50b0241c0448018000101c0001e440d84014801e49901500010700306520361104099202241d108911801d403e45180300301540c00094804502d481030001d101412001c00801e40d40d100e907204102c1040340801040050020030741041d56021042c004403a80561100240c41c2141c50540b01100c0203480d00307024507115400b40410f5480307480003401400c501008012104080c1c49100011070400c012180301203001e00e88214183c512a6110400042042c100340c0710086105002c400507060104030b48450030504c0da00012200307102410b481c0040c050305c0f4a41d040c844001c0405600341072048014001d50700c0300e458040c40d000c032030302c8034400e1107248071080f403010700c074a000e006041d0001c100700130320701110f401840100381c0eaa200c1d0031038036840a016120f01600c44107444585005811280d03d0f041c030403006418143d002883e00600c1890b00b188a8445031082c09503209a5000c0c2083c03142c149002c0c3e0140750960207410105095903035400c48880b44950840700310b040000361929040700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 652639235 1250 652637985 652638053
    0x3220e01091806111204080306090f0f04030c0201030e061302030615032505030a080a020d0306080309010806012c03010f09030203030a15050a080102090a09021318090c03 75
    0xd1001e030b40700c00080d12605214180c07a86405032410810380d0400c41410041d6580b1607a405542a01c0b841c040c415103130f02d1f41409801c0140c030980191101c0312510703c2409001500c01c4840d240c6410640c903080016003201984016805418454130001c8180030300d50821070483d0b43d010406600e0752080782517624030b43d540d0240901c1c80ca0042c0b03040d03030903078040088a4440012050452018107a49104a045036a502d00192401d180418110344114001c40c4940d02e0741d40410680005045504080c800c0d0741c1400031142d03517802101c1143d03040110010203d03610741d025800701000c039454120301c604524034510794155201c0007101e11501075880d00d4894a5056001d1040e821002c0d4140d015600d1901c46003940d034082c110300d035030705124017102c071100064030307a02e800036400145120300016171103603280b80c02c204000006030302850200340100440c0f4031401000d8400b4040d079451903040c184250382d2160b0a0000e1105203c01010550011008000e00009500103460080e00b907410311484861105 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 652640485 1250 652639235 652639241
    0x100b03180d020f03070605040c030501020712031b05070303021c050901061409010614250f050606090105062a030f03011a160209040203030c070e070e010503010311011103220e0109 79
    0x43e4212190014002c1d240000e0b071981056420500640940e0710030f07900c07a106d071402c80e4010b00c803c035200c281c0c0d0303ca88000c0c0c5401d4024000b1410a100310045580c0010002510f58403c0801c0107042690010f004001010045030030b881c6098250810031040c5082c82809008098902641c4000540c058003a0381394600001c41e01c0c11f036a5240c3c0c0364606001c4808040721550084540302c01000005801001c038842d10641240c6078501842036020200101e0030424142500640340e1405007000b140184003e40381c403070482d00400d483e508452186080c540b46d13158180c808100d80d43d01400002a4400702c0c20f0f5907070185058462440703803a401807811039100b05051040408211901500c000c0347c002502d4a0907100e41d0090018080d00d2600101c08080e6040c07400903001001d0510311801803001040e0300c84422101482d081c20210714550458440041c40220348001504100c1c400c0c0f880e0104200c144281c5089000700102480a085c200500c1c2501401300e010b003201804019000051400c4940 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 652641735 1250 652640485 652640503
    0x61505011404051318050d18080102091f0212071209080307050d030917030a050103050d021f090c0302060a020c090a0615080711070308040504151508100b03180d02 72
    0x4040101c07080d4101010805041517001c900032a00c03010340c13283c020540a01c0b05240400760740d69400c0d0a290700c0e03c0c22444d0030300b031508950040e030b00c18416841183c80d890859039111013034420201c1c6401c2c4511080340707400c8100010386142040419040e0800030008880c80d910700e01d40e240c50710302544804401c2c0d981d004006024000b544005100039040d400b0303500031386142e070050b20074110100744100082030030b41c400d40e032110240341d481c00100207100c000d202102210000d4070181c140c0d44000d1001e8108100b245590794100c07543c03110314504103c2e9590b6403500656010306401d4842c241c1d000c02230344900c0600303042805043c828000910b000c4080c4280c0c8160b41c50101c466200a02100080f581c03000c1c0140451305210070f2901b42c0b00480fa0410008005511548100342c0e22800c11040c80140c48840c1405410180000700600c4065445032003014801280d1504140c140d503103001b6906184141d03400850414000014030000c17803c00b40b0075000300b040c02d00498218040404040746c0d240801 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 652642985 1250 652641735 652641739
    0xc1206010b130b16150b0f0f061209160e0f010e130219090b0f06121504090b090f06100b0904060503151e0613020d0906150501140405 59
    0x400103000d9242410050000a034076407034400c1e602078407030302200480e07070208001e11042031300ca20b400410405011854210608400401e015820b07454002c598607003880a0141e00c600ca01c020ba0161588511059850f80f040b541802201410684c00a548407404129040d0121007000c3c0003090b100e150002e81400780414865000c0d01d6071030031a0102d44050003510380d116094041e0492000350b85d030400c01c1a40840d0214902c1189850305640b641101c007454cc805000d41ca204103403005680d40c0e5402c0d241c491a13002c0401c401592040c0301c1d81685036030b8004640c1e000745895107000900c052071401c40e11581640c400c580c0c0c8980604444c0350346090441e1111600071402f007050000c0035884010f024445005403000c140540c481000908201e030800702c1210306000c0c0300c200421240040000c1352142450903d0720013074101b90010a202c9500383e001a0541b0b90001014485040558450258180c00032030402200c0503400b0300c100040001d2082074001850303104a2a000c21540c41142d0841d000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 652644235 1250 652642985 652642993
    0xd0c0b0c091822060c020d0e0a05060304031b080301030303062711040e0c03060301060609060c0206030c07020d03080105090903090901181119030c0c080a080411210c12 74
    0xb808503407100e100303004105821405180b120002e00341440781030780124601c0b403840843c0c4000741c00002031038a14940b0712881000000e844524498407240480c1c81501c8041d11a65560b64540c00d083d20100c0000355800900740300c10b042d407000c2c0a02c0101850680f40300c2d030307801e010203a5120181418041e021443c40c02ea4408036011000c0401150310410380c030701c04130948606095a070b403810b0415a4044810000601c0000704100e1a807801b845800003411142c00c003810381b5410144000d041083c0752400a000d950f0000125040740080015a07401590040000f400380ca038602d401007031440c083c400c16005441c5074010a800610120589a10340c4000d0003034113050f80f92511640d903e030540030941103415a1141a4000800c1ca07030002c0484041e078110000702e40d040d410005085030300e008904001c01c400869002c002410038021601d98620a10301441c00340c1391410400042d881c0c40c44400d9006803000c0a441c0400300845202151b600c04a0070355030b205d489502030248005640d5441555600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 652645485 1250 652644235 652644259
    0xa051806041517060405010e030705120d02040306020f0c0105061c020103050a0b060c072c01050111010b09091f0203010f0e0709030b04030e030f07080c1c02030d0c0b0c09 75
    0x91550203203141180c4409422030507566608a4190f40600714990302403900104104070600c542400340389140d4104000031843c001c0c1d5a26290345500d0702d43d111410300840090160200c0301c0319010b490145412050856a808070028489429400716007a4945035007800c0006800380b0302001011041d41c0d00d032600b90307010340e40d960044000b000700030300d036000070f42e0384600145158a902026189848018004000550424142e00c001f403043e140b00c50b25011000c03849285902408920230704440c02801c000c4408461550b050f405003800515041d00140c40008004c0300070800a46030201b03023100302c062509401c00071288400e9200902a1400340e9040d10020040701d25904c460396800060f5140c02c4140d035803280d450345e41c1c103030040e1000e90008401600c100350390700d0b0034001080b81090020091170718514041c0c266840b00f4401404501c5445c45c000300051411030300d01e00c074a8050707005096404008071150041c1030702c65203480545000d454180012003140401c0102c2d80c0c0c1a0004001e001405 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 652646735 1250 652645485 652645489
    0xd08070f181a0d150314031305150d0e030415020c1f05070c030302010b1c02010e010807020f0102031f0f0608010506030604021948060b0d030c020a051806 68
    0x52184074030a2152108014141c424020f0707110300f1024283c800803807400c0314a142032441d003040e03005403002c0081d00200410341d205081902080c0c01c1740c005035101c440c0c0c041e4000c0902164094034900f40c5220f0300300610074003503800c0400144140e0b9901c80d07042c03e101c0c043c0c01c4102c0c4d85003c04002250030480b0100d0405107201d842034029122005803401d47e1600c0c02a646e11420f07000c140c2c2c02240541e454800038017003464080d03444003500036030000c05504007100d03800003800540c0c042c290034148054800498480f174824001c1c02041005040259603138204824940c98104c50400101c5070b034074007004c0206a481d841a0f12504a4a1598070340c03070680d0a05c5c04010300741d4009003025070700541c20001d010515075420600000304000d038139562280410305403a00c000120703a4a03004442482000b03030800d00d06011200750712040c04040b400400ea8402c0c6010070051120741a081d40c0f003100503402504040d03020a62400a81c030036201d45107595914018041d000103202109001d440c40700001500c0f44c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 652647985 1250 652646735 652646759
    0x83f03040809030c100c0c050f090403030c1b0c030b06010c03170c1903020a0305150d03050d0b0901030b04031701180209150d0b03011a09160905030d08070f18 70
    0x2142c0010203840b0100484130021304428415030300039020075844200700062000ca0348400006100540e03042d40c00e070600c1d80001d2048800100700800340341ea9051507500700d910038018909103840d103e556120710079003800d0100d0032050611080b02e40e440f0040016145511641c00c600076a0781c1501d0f12101c0c800465041c1c07c8407080200071101c1043e00703001280c00000140280c10140f40385440050340c41041480c0141a188020001ea509400602c0356001c1034035a10191002c01d909481e100791100c00118201001e4034040000503030022040f00080240003c29071a94012031090710b0303540301504041100240d0160134441c084204d5001034a842940c1c0d0306400800c10035000419010f810301c00d644107030504e90002c0c000384031803565a800396401c5080911a212401800140d90041203a803240015030f200801000d10342401100191510464050080103003e07010060980d042440090b0005140700340840c0c00d000003981e9285000b503514040c245070344d402440079010340304160501d22780c1400 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 652649235 1250 652647985 652647997
    0x40e1204060c0f0c0b090906010c1e08041707051f0206060d0302030d0515120705030a03030b030a061e0b0913031404090f0911090708040f020a083f030408 68
    0xc10070000c41c4100042c0c13024003000e001d0300c001000c4a840f00040d205020340c0380e00090510b814422030204200210303912405c5800c0c14070f01050074440c50075140c5482640c1c1d018651001c050340800345411f50700e0220108003803081c0c0b0f02c2a21004005912416948080c0190464a00c0560011800b00e8501e041c1900204c502c64041c0c0101c03441c00c1921401c280c200c4904842c80390016032454451034151900b00d80c0a80a00d4824009104450800000949070704803013000600b450341e110707100e00d29910144070782291590411001c00030640d101ca10050f4110101103030b40c486615000c090f0b101464203104540c059416a500a0034405030766030309480d01c24441e800c240d000401480006034803401c6006500310400c007038001140048041c0783c4041d0320740503109203078851014030041104a030383c0f0030f030741f1380d402a0001d000c0f040890a500104590f8800340d008480356000c1d0040110302800360150b0a00c001c54038050340e0f406880301c164140030391444030500040d4602c040002c9808140c0310300180c95 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 652650485 1250 652649235 652649243
    0x41212090219080d020a08040e040f0c060503040b0c070b070315050a030809090108010209130209130906090b150609010809120a1205060d030512090a140c040e1204060c 74
    0x244a086940000b203800410880c441c0c0b06070700a40c003c1c03010070010f0000403402400c9000402da1a95190389400300750140703000b200d0180d000940020140000c142c1024800d81e007088504030219203072200106942d0048070250342600d00d100c0403d01c4803034160200c40e0901d401c81d00400954940780f0044020b417184400d0904055511200402e190380c4981c4804011449070440d1551481170b1018420746800c143d00c51071440c0d02c1030104401c0c40d00c81c5d042010503801a103000684e281509070001d041d201d41004a001854940340f214020401140d02004195001e004954181d603223701c00c50805e030904503090b642119061020a219500134030700b15411030980c0003900c824169000e00f201c03146d00003e00d40d1002030a0704480c1c52941c00b2034400e04d42c000030300b541c0304603000340300c0d441c0500503101d880141c4400c0302080700002c16594003801010001503220440002e041c03407008945946201d0203102d035200310f240c24000c6a000c280040e200d02204a01d040c1141480c1c80c00c041991688108082a6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 652651735 1250 652650485 652650491
    0x10050907030b150c07030b0901090b131b090209031c09090213030f060b0108070e01020a12020328090f030c0506090102071a0a080106020c180a0906091514041212 71
    0x301031854803030f002d850040801c400401d9a1840c50030640c83c4403101804d60380069140071188008154448844c0b50b001c896120300e0250340740e0074a0b01040d62000b00c040800304d010440701c0401c03d017040340c0040030b09138002c0701210f10700d1841181f110700c0040303a651b0b0540490824141042211081c0e0043d003940ca80c06010907a65550ba9100d08445e4803078a00111002c5507903010700c508941e040403000d5048800d40c0f604410722004000040e50f1102c02900180105200180c0201682d108108032904d00c00d54008209035001265403d40d214401e840500e00840c1c018200400c1452201d0001c404a0384c02250000f003c0b07140505004142c0c2c00016000d0441c05640e03008074102e2081c0c029600c44c105007100807986e03050002c10003072540d58182c00000454001e07464291241c0d84183e02684601108140c0da490368491803086002801a210001d00e45409c0c42542420b00c40c005030040c11500301c180c424001024805c45032402c0c0b290403180100b04404a41c2c1e400d1955201d03e40c40031018103140400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 652652985 1250 652651735 652651759
    0x50702041103071106090a1b03050d0c0c140a0b0d02070c06121407120e07080d05030a0c09081207050309090c090a090b0109120c0b03160810050907030b 67
    0x410141e401c1c1510035801a00d00000384920a41d00c99444240000240c0c003030000b604110700240e45070f8080c03c0000e0306640c800300703040ca0000e08001a0400441e4040201e03400c40d4654500606034890032281030ba1403040a51000034207400d62031500302c940700c00402c00f68419080401e099219009420b60403c01682070207480001841034244001402458580043c0340865031200c806846852488081d032100c0c240911180b1034010701780c464141d002200208035910001c01c1e081c81c00c8650741c00b2080718842d140301c2c840000c1d080b00c0298064146048144039002d002103095884016610032910b603503208400070410000c1440c041d00d10148501d003035034503058450700068902481a03e101080580024250b401860034298072002041d404106001c004298000a06240c81d207100d0361003030102c820040c20400c001c040e01e86001d060723205207480d202c0c20f044070500500810000c1c3d0700d01145454020a842e42c0e0441401011208000c0118105a40b6100c0032006800f0b24102250042119025 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 652654235 1250 652652985 652652989
    0xb2107180f05010605031503011505060d1b031e05040c060c05191103100501061d040207060905070317120133050a0917030706020c15010602151810050601050702 71
    0x40d20f03000340801c0d41e91a4580c01c084001d112249076900714148179a00d440c0d60007280308115401d100c02c07200300f2180075031609030740907644018000c1c03001101c2d00c04200c1b245008040c1d816a0081c4445c002044280b2807440400101078121030062301c0c081c0c4a0501503e04000d00c07440350f82140c200c03a10490642c0e9220741c0d070030028901814040c0084500d00b41002d080c002074101002600604510707480240035075450500d0150509440c11456a220302015030341804985072501100d04c0d913980214100300c00d01b5281010b540b0303944140070403900407200c500180010128103041d580024160303003090303c4a03440c09000c16442480c40c0d00c0e607500c600e00c90007400803d500c41c3d030032884070341c410341c0711282c1e00d90f400100204051403e0b008001c0d5030792221143c102c030031000029030f8010759010b000181d803600e1070b0304660300e001100484180c0c141381c58000443c40035408950441d41d40300780d40c040c41698071900110300c0700c17a10003c00c501080d400240c04c0c1501000c01d40003590032840604000c0c0c43c05500d500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 652655485 1250 652654235 652654241
    0x281e0b0a03080d02161b1d070f030b030c18040b010503071d060d021201060e0105060f181507050a0b06040e060403030c0908010f05010e07020307030f0c08040504020c010b2107180f 79
    0x25a10f031b0302c00c1089040284214021903500c04010100c0619054604900041c0a481c900c07141c160406940d481040700d151003c0040494940c00101404841c00c1160000d0a940704103c4080387e000c2c0722400001424100043c030402560340c42201e44154484824900d40c2400f0000c107119800024074150780050703103c900c515800f10000301c001113006070401d441d6559181040e0b02c01d40c01220b0400180300e2000c1070b00c0c10750310300000000013003000096000001d00c0314070413606614000b45001a4807802c000c0002240300181d07100c0c10090300541c1d9940304110483d00031044800701a040613000900191190340421900121410824405500d940017a800c44141a00440d4a903503030f0320051210101d440e8040c3d45c4400988021441c00d83c05a030b00401c000c50040100d000d01070103900c56400c101000080c0e074082c100c041e10840d110030418400c140a00140120300340107a5000c0c0808212a00340166090384031511002040c0d41c80c680390302d0024004145202d41a2550342c0d550103043d40000340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 652656735 1250 652655485 652655513
    0x806041104090f0501140f0411090a0609150314010e0912030a0903180302062a011103040204201c0e0a1a0717281e0b0a03080d0216 58
    0x2d00090341d0b80c61960740b8000c0302d4040c0c00c440c00c0004000d054850680c1e903094504450a415100840c403d1401002c0e41c1d280e000b24a0002d612040440700402c0881d400380786a42118580c200c0180000d10414040d401c9505045074100003c142000600c80f40759507c404540003840242185e181d40108030044000350001d803603507013815855140000034103600004401500c019008160039403440c59000a4071032003240d5000c403c82c04030381103100750f02c05104102541003035070500901000f00d5a0010384007a0b0300444003203100300d2034000b034042042c4904801002110b190751910b40340c44035600b2010031401407014030007101c940740c03010071030040c105124881c911481083c07245582c1c1000c0c000f01c03030702e004000d0001c010020900c0400354560080c00030309070052102e12001040f49114466800181801c2101028190600c110000c0c0c80701080c2946020030304540701040ba00e00080100841d05043c1e00c006814804180110005c428903980140030707850980e004034610050640c2e44040030705200c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 652657985 1250 652656735 652656749
    0x312010303030209210c09040516090606110a0c06110c1806010f050a080610050412051b1210181a06012d27080105090c1903030806041104 61
    0x22442180d03a017041d41a903641a4412007101c0240640944215038949070110a80d04c2100d8250204050140c2804088543c600d0780069070340840e111061003010b800c1a11904001461138050011803047c041036940c00345070301220a10102e0700d400340031103201e2540100920700d4010282d40103002d070340707400b11900a221b4205044125103001000500820407404150003400410045207034810307444154980e01503000c0742d42e40c0b0814941d580441780741c00b440d00560041d00600e00c4441c1800380c00120140120740920244010200d5241408005612104c1810156000a01c0102903a1884d040a02444040d191602011041d5204c0c0d2108100e000e800604403c101d4086c0969546c0c0040c1d118034805801100a00749682e808000210140030340d0301a0402191480314032070119400c040d43c50458031007500500c46906c0d01c1030704d802060261004041071003680d0b4544100c5c00c0c100300414560f00c40c501154581450340d2001e80386610010440d45c1c1c041e0790760740d48403800410350703003d00042c2c644 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 652659235 1250 652657985 652657987
    0x6090c0f031b050d030519020309100302070b2203032a0906090e1003080318030414011106010e010e13150501030303050a0902060a1d0315091011160503120103030302 73
    0x841d0b030114415065508424012602c5541d0500482d0b0400c0807901c1c2c02040b80e24865040241c0701c0120b00f940035510384580d00296054450402d9079064000c2c02c1b0090192084e50343d140ca9030164a2040403050902c02120088151403501180c0039610a516241402c0803880441600607004551360180c225408003003641c540d4140310043c0e00202c0c25001d41002c0100a04c01c1c1010b80c52601104424403004040c00d20020024100d103c501980d002d6000380d80003125150780c1c485034134200f02d1803038211460006042c84480c0701880300000380103040f1800074181a0050342400b140302800803000381b04500c2a605040d0030000104115541058554803580c0024554110f1500600b0b0b10405019034180703c2c00c000c0c0c0c60f000f603500c01e000c481d81841142021a9110440184500122001c0c8080d90740750042c0003281d542115050000c074821001c18081d42c6020f0017001c100f0040f141c03200c05558640109010b1641c503c1100b5550714402402202101d0900856068548810209800440010360 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 652660485 1250 652659235 652659263
    0x1050d060e0108011e0902060f03132411030618090718020901030c030b09060f0a080109050606010f05070b040209040206070605100f06030e03091905150c070909020d06090c0f03 78
    0x3001e170340c072902c8a0a0008184180308450f00014010300030b50040350100800040850354901001c0d0310034214a5000b03a00918192009010108044012501c142c29904141c0d022440c4c150103412280f2134440105104030120402c0d4522810741002003401d200c1c2c1c03040340d50105500359006001c03200003100c00000351703a4210400005003501c2500442105060070603041130304070341c2c6040760b0320341c0700c0820350f1034078100400308000411011003980500015464254040d050200205845101c2c440a880300c21391030300c1010041700d80f445040c1c009000303500c10402140051916001e40c1c0d40081c0014201e604000051304c45100302c0f141a600883c104d05200010000c070440e5031507900c014100c1d401c0810104190004140d100e100e81100e440c480d00b84910b1f1311161190410f9024090240900132b000c280d030424915082c1c5500640c5901d40c1c0d80b06032480010159024081d4140c8954058424000660180d843e030001e000c41c414101e4088503101004500c4202c0000e103030300114003d040b150b020324 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 652661735 1250 652660485 652660511
    0x5151305090c180102011508071e0302130c05131d250309022707080a0507050729070203070303110c07050d11090a050a0513030e01050d060e010801 65
    0x141040e030116014226250400c410b05204a055800380d0b038580b10304031030110400700100c0c018002c1d22041065443c012201180c40c4100207000010303911103c2d40c0340e0818011407181800410780d888000c0d8022040e5840c4114013042c1d4001c000305080030300b846801c200c040003031080500b480b03402402c0c50503c09070f071007200d0703030000e003152038008444000200c5000c04049242c0e802c00c3e040d6014805042c2ca8408282c11911509484a0301c4c400181005120710000700200d1305900c0d0550b43c9000150218001c242c4107000c40c4100ba0088155031226483c1030f505035a02c880d444202214200c00b8100f22003840d00c4001c2c1107840d980f05c1c03621503014680c1e4107050300c1c01404554090999610258040c40445100c55000404038181c0d5070450785400000c00500e031042e403d103070070a103a0f03400000807824080044c2c05600818050000440701f402213a403040c80c00000c0310748170200500002e500180306c0049501810042c244034181d11070210344c1c0ca4551425090f00c0d20b003a40401030603075480104080b50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 652662985 1250 652661735 652661767
    0x20c181504050402060d1a060328020a020a060f020702092a03101412030c070612020909150604080105150427030807110a030c02010908210f040515 65
    0xa80480d010842c03400c0c80d40200300103014044c00d0076840c0342e0300e4000d11801e02c0602078410032517000820944e03880c0b0704020083c0c52100c020115000590300d00004422840450094a9112045500405440b54552218400b40c014a0b00b01c042d0706508011910141c1c550103182c610500304c070405449055101c48802081341d0454000c055900d1040c405d0010070381c642141201180c0340c6042c019031030010207000401002270066196410f10001400d180e0540001c1440c00c1200c032107490f80392214030f86980c840b041e4443c4d01d0b074242e8050072050014003004d107014103141c60460050002c031f091546401c0030b2400c40d6030a0300c402c403070300c6813a100501c1646014060200e041540415210445210017800e58144440c8000182480b640d8030000d00a03620035000c1640031502c0c00b0445400208905026140c007801200070380c005101d16501140116000500001ca50180c0802513408100313080340802130380080440d1025607108100004041d40c400c0348203589a13000380348155507101d0319103d00d038032 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 652664235 1250 652662985 652663021
    0x106150c0c0e090f1603020a154415180a2414010f02063304091406010504051b161b0801061205120a020c18 48
    0x41210312880c150014101610340400c0740c09101c50340d0380b5a111506a0fa00b41441440e08a60b18401d404451004540203020300045a000b0b48592002c0f0f600d650100011404015644000c10404401f40b040018001c2c1d00802c205180741300040c0300c0d680349a84d400030a00250342c4841c054054800d010b002c1681c0d03d08a07100d190211384074000c08501007029003024000404015003d50783e81d14001a0b0b00d81d180003200c494401d42c80041c1e120352039104c44115084440c0c61280000c103240b22404080e800090502d016142c0c1c43d0800d45090b24200c0180704072101c03800707036662000030307180d640e3340315141c501403007002511840c4800d65040700c130f140703080c54605e05030310240c0300b01d00301400d002401c460b40f0301c015040d440007000c5550315002c0750300c4070580a1405400800403410038000050041c80340c1200400d990400c170003480119038418404099920386203001e031442d0041c02c1d00c0c5c55000c1000000301056002401651410148040080e80900d9008401041040080100305005113250b42a0301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 652665485 1250 652664235 652664237
    0x6090b040e12030a060302090f04050f07050307140102151017070509070813230c03151618060201060e06031f0b030f01051006020f070602150a0f0e010615 68
    0x4401100c64032520342e40d500300400c0b2100450000f000c035141a005070046800785801074901c83d50303420007440e010505482198151fa0030300506d0081000410082002c4007190001030051a5045c14802181d65800100c100a4194441c003600c000c4820079550f4858070a180744043d0f001c016207004040c0c0c2080f510f002c0c210a00e174010810070300c055030782c51a0054100540e460400c007103075124040365220120002001d0301050031540b9504c00c4280d11004000c900c40c241003139903145040c00050683d9140c0d14090081c440310340c200040c509004110459820310028031384204d1a034170030032004a05403a81e0300450b0040c0d440300010311010380318210303a6800c02c0095000b040404140c01031051502604007031b41d000704e5212569881242d80412200c48a01c080c4030081095041c001140c0c400d003503180c447c00000d80511603040d80d44003404200c400c03c490440c5c020300f030554101441521a840010101092541d03242140c1c00007440c5803050382e4800c0b1000c4000901103060032001c030499101642810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 652666735 1250 652665485 652665491
    0x120a03080a020f0f031f1215020a02030909010308030709060f0e13020d240f12030309020a0e0414060c0c070501080c040306020705070e06030c0a150e1306090b04 71
    0x103540804100d9100000c46030040c0c40e01070465044840f44503403c3d0125400c080401401800103101c090000d1103148441c020500c030f0360f102001002000110780107030280041003141d440d210740640042c514550320380b0540c0c0ca40601000007698043d400c1c1c2042d508101e000c010055055040342110000d000c060408031207103200f0050080202948620a13801140121842600e42e4025010b0342c4400540752420b010341c0c1610410401444900181c40b40c0c0c41c0e100d5800010070301241c05401090300d96404881c0691001c2c1c0d2003d80c00380504070000c9070018228100021070852528445000d5031040c4942aa8007005150302c1d847c15074040e020740550f070020403542207e040005450011603a0a08042c02d25955503142c1c20304602860b8400303400c0600000d6200204034010400d0029190145a202c40a480381401e040d80d403100c41c0791054101c0823604080c030040c1071611401c0403e42c0c02e45031500340e20080c60003165050140095013101e464486005100400082c05090a4141d040d6420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 652667985 1250 652666735 652666753
    0x3090108250f020c1903030c05010f020a050c10090201090b1c05070509091e06151b0c03190c0b070501200301050a1205030414030a081c0506090f0c220f0512 69
    0x80c0014175260b1000a00340020804404100301d42900243c0c1520180c500440d1100c400c0303e00a80158002800804603000da01d41c81c46c0804600e00c00d4126164040c1d48940c0e0711814490b07100c400d5408140c0b0725040c4040020840d42007946806071502c2485695565074840e1843c405210482034080d01c09040c0302d00807180201003032105600c2542c0900200c1d5210f440100c21103090301070344200e01d65070001c80c400088007505c4801c00540c1b010109030940c200c5034280541092542509070f18040200040802101005040c0c8100081c02010340280c00000741d180110101e20740b03448510700d0f6a0100c0502200402491800b00c0c0010020102e02c80030383c1002c042c5541e038a0b2240b04e94090010140c11400c411f403441c0d20100f155945c26584805455554032044158103107034102c0b4210072441c01d05250000300b990404401440c01005803802000c0c8a84500d501940c80390400d0004260110820850001600051002c0700083c41e0400c22001c62605050031301098103206400d05c08541d229000e0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 652669235 1250 652667985 652668019
    0x6090b03060403050a09030b010e011502190809040b1c020406080102040303052a03070c08060709060e0f01030b0607111206060d0308040203030730020f03090108250f020c 75
    0x28242e400b950500d0065518030f984001520804140d0f007005c2c000c100d4031300020841c0d1035402c41c1039042e501106904a032100c8441022070743c416141c5100480d150300345004600240151010b0305080400400102c0c80882d0840407450382e0a0100d410340c1000001147c450960a040c4a40000f81c0042c000a5103410b040d914013400d45e00c1100c07468900742840d00040e503c44030242c0301c00e404100101c01625070754070a0741000d8026150302d0003202214011800451034490043c04c00004898071503c40d40e100040d500c082010600d40d00c031055061586a4034040707000c6d41c4120042018622801900310000102c81c14000170004280030001940d00c80c00074003501d6640e0410030514103901d40782250607540c991011904600464a00800c125214046280c00ca1f018844041d1824501a14040c905d4054401265164aa24241e40c1c15400800400f8050751080011304d502c030502002e816401007c528100c00903440d0080c41c480040c140041c180c1841d5811300c804108610122502e900f1428950b003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 652670485 1250 652669235 652669243
    0x140d09120f050604080304061802091303020705030d170105060307080f0c0403060f050411012f011506170c030408190c060903080601090803071a040311070b090406090b03 75
    0x245200c000c00c1400c06420040041c030070129542c1d004098a5041c10103142248141d00b01b540c0071030f540da00748030407258108982c801e0340c050329800814841158852815001c40000741c0f440660450007940350104240e241004540b9501009907140c09410304e24110998410030182c21141c4228020410b104590f98040078450300080160070070400c2c0d88038140e20f480d5920032a800201a14101150a8030f00301ca5944102c5c4224001e42046818454820044440d20304034500659000300105c040800c00091030006066648168000100626100c003071074207580456010b40000707405821600250b170960901c0582110b0040242400c508007642d0300000360007446a59114001c40d6091414030920440c9282440c0750401c0c010405899207003401007042c3d000b161450701144940900050100000003100d004503000b0f01009107043c04801c00101c2c1c41d201400c20741c208250a09080443c510502c070f124000c02951b403032507580d90000003e00003680c00d140d10029800e8036182c0c4040140d20045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 652671735 1250 652670485 652670489
    0x90112020c0c061606110306150a0c08092e1107080a030302030c1606050720070e07020c06030a02130b09061603120f0f0e280f080a02010504140d09 65
    0x2c524986030201c11600c0710015004c0040500070504050000168444200017507009075402d81c3c82024404610010407268490540010001138000810002050198019120540c40140a05003041e19030042215032104171071103102400012081030f41e016009014521903000341409001424a0000115154a0340210140034507800000103040c84c3d0107801101c09001c008c518103c080542414460300402c000c5886802280d40400110344000300c0782c22059114410320001c00e141820300503622550b6402070115415031040030f012514554804028501c0342000d402d006890310380310711103200303481050b0f03002e042d03030f21420407082c0e6440d2901c2c0c00300c8500080340c0d161110389498a2804841c014030f05100c0515070762038034a086080c146180c10102c072070b00b6001380500107110708801c000e89415806001c110400240340c0308501030220781031568a40c1d0300400000300820190344481d60f0036803200c140000141d54940070172007000010010302c466003030044003d01c6113050307250024016140381c0c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 652672985 1250 652671735 652671739
    0x905060406150f03060f0f270c120308041e15021b16050103050c0f0403260a0c1b06020c0402070212032a0c090106110a021203090112020c0c 62
    0x303040e110302e00c815454800c0307000f0074500c03903210082556414000000c0c18502c0d440140b0a040c4400038280e07034854010168070b010f07184443e1a00c4440c2c2024100182400002100c0c0040d1040c00002c040041005140703d42d40691241061442c15252503034001d038069034400812540c0c0443d50703020442c103425440291161500c01681d03419400d0304455001c969166001c1984204080c0070070005072030b0312a04c200c60302a2803d04c84c58607009186640e03802140c1000c0755143d8184010030203d41302400428001030280d250aa0034500c061003002298030012040c401304650f000c1b13640c00c000c0d0724440d42c901190301c1e4400d0a6500d00709074000351038902c003201c01c0d40700d0340d0041072600540d0b451741003060382c140000c01125510000c000300701810b0700b510f84184500340080060704690b0000495410400301e0002c00d9401ca980c00c0400075603204400c1220a03d00380b090050b6500140c032240c001d5410000081d0040d0740f107042c040d0006000d14100c52203c10040d00501c03e002d000240043c01400781d10342 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 652674235 1250 652672985 652672991
    0x1503060303080c0a210c0311030105060f0a120213050f0108090d1d0604080c0307050307060210090f02131b030603170a1809020a02010f021809091e030c0c01030905060406 75
    0xd400400c403442200854505d208856084140008071440d52003035405200545040c09000d41084174803071240824445c4603000541044003030100c0200c03c00074820b10000c1c1c240449a900301b10740d000100c0c1c00036001c070003410300100e8003841a4a4090744d0881c10103c00d10304900c0341c3c90480d0800c0d85841c881940c000c00c1c021981d40707005403120801c40e80c074840c460103001551101e071341c1c4a80c0c5544075000030f00c01c1d000340101c503c0880c140c207020a419084d60010340051540c080c0a501950040c40300c0381c003c1e9030b8106085e40c1000140d0360301d42102d502114084000c202d400000541c00c9202c010003811800340351601804000003039500b140d055454007501c120701c0c4c03103421462051b500b181001d408996401d404402c0400d50500b641e014004110160b8000c105000301040040102d01c100401d82c65100ca01441c05e10052500c0080706a00624141c241d888640d80d503d003080c3e003282d08603a94004d94001090480101c0c0302008141c1039404246810f10400c907285d12010f45600c0050805020192 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 652675485 1250 652674235 652674247
    0x305010b270a0914010906060513060f0c021809060a050105030703140336030a082d0307020a0b0a1401050d1a0709180c0f050705070513061503060303080c 68
    0x65039507900b00080c46030b5041401002080c40200c000941c09002e0307482c500b407600c0c0740412500d00c51800d980e0800e034610030010110f804c2c04025941e20203113400820800042040030340c01070701c945004c82c400301c0141c0c100301c540342071401c5858102000100142402881c14004000d295800102d4100701e030741060500b102588951901400c5100740404440d03041d5408828810302c0c45400e103003c81c1e180d9080703201642d0002800030143c4a003001480500200804c0c0312030000b100071030440720004114a034802c2c1d0072030206490310b525a04201d0340740c40960803d04d00c0300d00703001c00c40d810701f80d12401c1181c003001280400d86481003110030600615000c1d5407010180d0b800c109240c1204092182d8a1001e649030b450150350040c404841c0c0d015040e03409200343c1c0304103142e415034001c40308015000e4481007040d0b0070602d8100d440c0d030008482903034030348100306d00002d0360b03141d1840c0681c07035840d00303d00881c2da582032482039940602d020081900305442c0c4081080800d50091110b60060300c0013050700e5480d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 652676735 1250 652675485 652675489
    0x6120309010c06021b0f0d03020702030c040506030307122c0607060c09030f0f1202031303030e040f110c0708120a050318060f040519150906020c030a020d0305010b27 73
    0x20107849510528403040321407101703041030001411150340040700206d034800c1070030034007c42c1640039a0a0003901580854280d4113a031a22350040c80c0c0c0300b00041d00320382c10512207440b41c0e41e254408070030321380c00320b110b01c0d02c8030001328030f85400c03680d0241d42c1c2848480750316140320100b00745110f07060010b420030b070740c401209642501c03581002009540159030407800b069075081650140c54800000c485001c50307043c030400034030300200035905010307400406e600d20249982c03800e42e21540c1d007000d2158042e0743d8500c0c00540e10380314466210030565101100e500ca11903004201d10700b0400c1d030006131701c5602075210304006141ca6070449012183c40e203070442c1c0301d03114400e45a9020710014204507050040e1401c1107185210b202006116502070700c220303048801451180c0c80044c10200020b0f2012444401003111a489a0000100b80348505030051130b025a482200341160013074103043c0d006802040d0b902005951500419014104110003240b60881075060b0b40203414440d08500488407840d19031110b19 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 652677985 1250 652676735 652676737
    0x30c080f19030b090f010305060402130f0c0c050c01030212011203120504031805040b030c1504030c0b03070306080606090a0b01020708070f0504050108010603030c0f05010912050d0506120309010c0602 88
    0x8000d0740e240804007414400054081c152403c0d289020b208110000f50000d000360392082c0c100d07900f00e805800d160300e4580074440c100b00109107200b40341c0d4942180d40107020b082d00c2990410000756403050301840d1640f50143c14484112102d5041500500c004a515500209064112000407007805000c180070b01e000d80340707200d2400b24200d46c1440d01d800c000506810100c004034034103000c12401030b41a00c420401c01203c005440082c3c06501001c054505824240a03510703e000c90b10890900380f940c0c2e542c81c1d40403015107400031418607002209100d605605070080c100074210b030354040e199500e08030300810000a03000348039452071b80e01c54006c05081c5c0d00a0000e58054000202607503142c0e82c4490100103a0131180c4a941d00407841c20000144840c81031046006a07981a40c0300d480d259580c0d02e0f585503418044009807855560741d07004400207400000c10031074603801911000d450750070086880040b242c000b030030079019074401451810368007400300851fa5180c2007403d002a24480500b090002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 652679235 1250 652677985 652677997
    0xa0e090a060c0302040512010c1d121e06090a03021b060c0d02031b0c06040e04081603020607091d0703050c0c1b0a060f120f0b130b040501060c030c080f 67
    0x5140c0c0b50680c207002055140c2c00a20a590040e41d4164156010b5518a403c0742e0b640f01145001500108a21001c00714004000d031000c2c0004000880014418840e0342c181044003811003105040c04e03820012000d030520030749a03c2440131000c3d00d210189a00c020b0b4a8000305c048020388180000c124085039650300060f100000000c0089400f04c0d4100384006e5070766800008010359a00d000c18480110100c0060001c404682c081c000a003480c0c80d050b840f80f100078000e8000c840121061000ea00042c2582e6150055640a523006240c103042159001e00040c6842d0041001d034000504414202d8803002d58441c2c00c00040d2400103035558900d40d84000360700500f4641d021a00544207004130010105141c501300300d40807a4000c031043e41d1010266203504121002a0100e2103c1041e21481d6030b41303500004003441c0120010804840c21000581c613160245c99a0111540d02c440e0b0a0450804c2e01c01d80e409800c05040c50300e80041a62401b47c01d500c1700101c020916040007031610410824a0180d80ca = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 652680485 1250 652679235 652679243
    0x3080a12020c0a0b0a020c1515030a0305030109180b06150c1605130605010206070e040b0612040501110307020316020406030c0b04140625031419110c0a0e090a 70
    0x148404054030410784070740026000713841074401c160204070b800600b4805c0f5070107001c60703500400040800d90714030120643d00901e0042d00c0160926261003540317092149003500361203641c0b01d0f9925030402484c44211b440004640c600c119024110000085408440c181c10003021990720407511100c1480401c140700c0d110020070203000790f0341c0b1007007156540c501490545400301d0303001111034900548801103610324455103005920603000300d02c65a00072103910125203005800410100320010109125611240c000348110882d079007000305000d800c0c850040c440414112030781c034505064500941c0c1b800f0700e00e5641007050200c8001402c56941d607210000850b8000d030720600c510756990305101c43d600203220385a191044181c0b817412507c2c0040c201c40074000903400d01d40c080c26000c4150f0403a040b01b140120240414446590148003581000d0b14040e460740b0283c0c1d00c058913a810085c120880403a00381210b51254040b00115600c1074200d5040d1303184c0500180c2ca640e6031001c1c051402c1100340c0098 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 652681735 1250 652680485 652680487
    0xc06150302030f0c04180507061103073e0f060c010612060213080f060103060515040501080f07050901030816150509210304050d0f14040906050906150403080a1202 72
    0x40300503903004ca40d00c8000ca5045908120007030381c2c5096a1031300c2c141e0300801060b03500041d0052001038013070040e01e03041050000859003046c0703680c0c0d1810700350040700c4d0072050390740b02c02c0e000b001c503604a40584025034800c0c3c18002140030103082c0400c0c41030240b100d030030340b05000c0814030018200c001d5000030020038510170403c440784038504121009520251070401c0c9082c1d0548007244050000a10100400d1042c0051004c2c1c0e00e1030721684000c010140407844a90040d45c00c007103040d074403401365502030610440980114004602c01d646840701c40e034023850280c0055070042010075000b0f415616804402114198840c1d038070724102215140141a4400082c0703800d0902002d001d00103064005071074081019025035012071441841800b0403103000b0055400000c0000e4058414902140840301c0342c10844604c2c1c040c200c90132960f41050700a4030005584840030041494185a450b40109055800d02d8201c01400441038442c0300718000a0071150700004e010781c4c45c51060104660103c2060011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 652682985 1250 652681735 652681753
    0x10f090e19021606050606040f0504020d020d0903082a0f0d27020301150e060f0a1802031605070317150406080f250614040b0a05120106020c010c0615030203 69
    0x9202448201c0000351041381c580000031710b16081c100d080f503090311072640c2c84c5c0140c2440d103010000a58011404810b00b20b409014214080b4820300070031940c94400c2d1126030302442c07d410105001011405401c082d143d09503031140300142600122441c03480c012900596070849644154042d0200111840c91001400716104000d07903580110320616200714000d12240c0980c14041004420174011a0b0159260f00f001c03511628045180221100001d080a00d000da030310041a05550b000ba8804403030f043d0004104070303402c01440050b200d10501410814100480341e100205850b0300525071784941c18058022a0290244445404151000601c248122074441c1403454640ea4550a40500e512a103600619203010504182c0c0d015403000c0d00c0e2141039845d10000312108202c41c2c0507006422400c01c0041040361441c0b00800f0402c0303803525030690b00c2400c1d15100c011200e050340000115085a07081c8103203070307a2100410021903048600414401c49024209c030010100b640001c1d8188114800303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 652684235 1250 652682985 652683007
    0x13020f0409050319110d08061c02101107081b0d030201060801090c1401031103060d03090e090d091d0103060e0f0a060506030c061c020c15010f050f010f090e1902 71
    0x1000c0030b610103a40c3c2c0c0440000314505491380c03005080c50f04004208031000045140c240082d40301d4127400454140c40d00c0010680218a01c403029005c1500002e04421149d450071000f0440103000300100401459903494000c50000300e03510400105218070380d10415402454400d40004010b080008020480c0520b10325081d8403450161080c03a00002105400c054150b02070b00c071f0881021086039009103150764800400200d4500c0c20405c9007800750301100030403019103c40a1601c14070640004147c0c200c551000a000600958052085050003004100003140d44114050440380d1000012501c4421000440c0c01e228020482c56190b00c58403c801d000d005d59504454082c90061f402c0e28000141e500600401d0b10604415100441050400400740450355004141108880055030700ca6000a48040e0060f0340a030300c0010f00e103070384070004c1c0510f2800918140c1ca000090030b000e807603c3c0810502a03c00c103040d100d0b50490a200f100040e600c240311800a60030000007404c21903442c40c081c40c0e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 652685485 1250 652684235 652684267
    0x50d0507020c0108090607020c01271d010506030103080d1a12101a010c020609011803060906380604090207061b090315050a0609180203100513020f04090503 69
    0x310b15001401001c003041c2e101e0b03400308899001e030225902902c80412501c00540e41c400c0402c155415100b05d00020724005048611000040d018500c02510088801c01d9400700b001c5040c5c0165210711820401000010700d000308881283c0402c3d100440d26000c1c034114007001e03000c6000c04607000420080313006110400881c180c11003c032031034030400001210309140d403c285206081507011440c202c0d140360151503c84080c044101e8149004e0105403401c0c600c0c0c840c0c6040c2c0d0791040701e50b80d4960200d00200301942c01101c10201c80c1c0840381054919120f1a2000e0301e2a003c11200c9030180d106185409440e01c0c822180a400181c00643d40d0300141d00d01140104641009002e80300c140000e200740c480e1080ca903444c1240e4004140520441c140070f842401090041c03c03080c00580c2d81c3c50001504101c5000c1c01c0c404a100c0340c014402003540c3d00500d420044002803c900c154600340420404035211a24002d04c030fa0140c6205601c40708070f80224000f0f02c0311490140c4948408101455401c038104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 652686735 1250 652685485 652685503
    0x130b1e0609131b1e12020c03040b04030611030f011502120f090102071a03190e01110d05072a150516180303140706090f0302010617030f0712050d050702 67
    0x3e203034080f1035118550122000802402401c1c000000307403511400c428404d40c42c03c2c071001041c0ba001441e100301103002da440c0d540244e0107004208004101041406603e00c500d001010319881900c1c0b03940f420040c810b01000050080405003040c0099180030319100b00900303400c41440c0e4949913030310443c07150409000e41144960310b005116500000c50403010020504a180007584445804e581705d103e40000703c07104107420f1381d103031715a22103100c0400102406500d60100f00003071040e60b40d071038034446070b0180c48004002106024020203000044028118041c1035001c03509401c0500090500c1c0c00c420b072102c1180450040c600300400d108566024400728001c07018680c54080e02c9141001512030450380314400a800315114141034030170000e01354010441c3d40d00c1a200050310702482d58902c142c0100600c07065005030755070842408204402e0100b5a07610700307044004c40c10300e000c43d80c0303200c028894501c006100030000700755880700d980680103075040503040130828069817404610080daa0b5480c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 652687985 1250 652686735 652686761
    0x40c05160b27060a09050a050a0605011508090a02060c030721200312130f050d0f031404060c1b061b05032401200a02130b1e060913 58
    0x20000500c045440100b007a404520450107032100350f455800000040220803800c1e11107014a13841b00340000c1040c0005600035100fa03000180c03e50400c0f00380c1c980d00318666441d50a1003008801e01c03146e61400514181d41e96170440300150f9070410010041d045014000006011803140070443c43d091000c2c440038044441c481c2c0c0e400c0c2d0801e5101c2c600240c0d00080e000d54070f540350800c0002103041103045c6001c0381c2c005200034266140020980d00e111141c8000030059900307400c04000340d842503500c41e4551400828525051000c4c0500d0780d004940054060303c01840141c1d23170408900b40c1400b50300b002d94208640c81d4143c40182c10303402d2000241070a0401003d0040812018211980c01482542c1c0100d0340580b890400082a40c010035201e24138030341090602c03070344d403284d460440340201c2c1ea0384220381808003400d18610035105004406a003140305616850800340c0302e940c2500c5d4403031400031080c00c01c1031038000d4152100200324584240c1d19a140c0081c1d5030041280300e400280c00815482c181 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 652689235 1250 652687985 652688011
    0x30f0d0614010e0a090e070e1e060a051e0409060618050a060f14042c0613080f030a060e040b0712091104020906040807081e0d080105040c05160b 64
    0x914070044030001e910440480c0d01480b4004140500304840d4445c140740343d00e40c8100c1e00e0007503ca58003800441c1c81207941511500c41c000a5402038a070590006170000e40a444401b405400d103000100500c40303580714a03d03403100d0f41c0b06d440314907500c5400208085401ca0810000c0f00c0d01c0d100a220092001e08c41440c4050621010031080b91142c461a0b00f16007801c2105040c6030b081c041101c1c419801a221142c0c0540c444901d4100364840103c041076516440322281e115200020845041c100000c00380e0300840d01c4a80c40c0d001181c1d00d00c00300c0780c2411104a80c15030325952890748000915198020001c4160120708000c00c128903d4009070040e05d0700d441e200d2141c03401c0003404043c0c8a26020052082480c2c1a201c0501c1c00d154020300044a0000c0c501c50401c0c1d201c0c44514070380304a41d4031011180e44296804902200f07a040c2d440c880c040117101030010351003204c0340500380070018483c0314040c5550380ca403081d0b5548202d044e140f09043ca400b14941c200400d0038080310b069015140000c0146c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 652690485 1250 652689235 652689269
    0xc0b03040308010f140f0105031519080d050c070e100e090102180f0a0302151b0705270403050304083c041409060f09040b0f0a09081605030f0d06 64
    0x1164000d80034060f0b100030846c3c1d008000410044400d600060805401c03400010744a00b503940e80ca40008010804084405000c2407500030585d1502014100342e1050080420481e081c8940100c1c1c608140d0700864000f10098480300e1030180300382e00315401745e0120080c4009012884406400600d080305952819924172003881e000c00110072140c00e035065100c074031194100b00500701090703100c01c0c0c0100d804003581445514000c460034840008054121508185810322103842c144480300d0898441c140140b61002031540411810ba5010b0005010303c08040300040030490b0140c1160f1244805141e10483e441c1d40c51103000704140280c07860b407805070010041c0e4200001c0310041d130b02100c0c032801c07465040c03064074418800c000b00080c002982004040c40c41c41c44584032609694000c5d07209808009580c504600c210280c84030203001c111500e400c0c60b85400124030190183c90002c104000038078042155450580e145100d4080740e80f80071030000c0744041004039141e01040841e43d9039500004004 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 652691735 1250 652690485 652690499
    0x90204140702030a030e0f010213030c06030605061c0f0f15080303090c1c0b0f01060909090209011509080f2103010e040314040f170123130c0b03040308010f 69
    0x44120750140c0141d009000001c44144660404215140c4800c20350724400d040320f20160990b800004038a103608031080d0b0410402c0b1200a03072a006000a01c0c0c00c00a16040c080040e1042c40780c5003101c150311001050400003918254081c0e14013900780401040180c48804d0000058221680d2420340c2c2041c6000003d400c80c00481202e204111b84806400180204020030070040310481d80382030756040c44a0030304d0010301c01e0800310f40a00c0b003880c0800e01e5503241c900001e001c0012504507128050800b034416005860704901207040d503503054080d480c0400c010320100e606600c250700c0303c0903d1003443c0c2c2c84000701d070000c19030780c119207a00042c10441e6068030054030100d2000307120b41c4005203003400008000c42e00c0f5600740d00498103a00c0c00b8a1405130750313000ca00c04101582d0004d1401c00000c0c00711905d201c6092180e540c0d00c4006000c1c0b1024000400c003850740c0d202c8014440d481e807070040d00d0710b40108079461180380003919881c206076440342454140201909402d008484104d070600c50081610 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 652692985 1250 652691735 652691771
    0x40308060f010203031311100201140a06060504180e01060f1701231801020301080c100305040209070e0301021c05090d0c0803010303120605040c0210110a09031e15090204 75
    0x1d8581a0019482c0da201c1d25007203d1590304183c0151381485071a004d0010b141d651000c052081e20099002217501c540c003e581e4068000d015040091580c907010342000110b80080c1620101d95402d149845554280405e020241261160340c16007540380000c0820600800340c59003003511600549000d4040c40001c0040c01c0b12812946201881c02c1011124000408141d01c00e40c41041c21190315010300b402445182a42c000380c0001ca4550480404001c0600b803880001d61001e08501d400c0c01a030800d500032480e080c80140003401040540d000c203c040c0d031001d404541814000e8500c440003113520318040c0c801442c003502c2c00344184c003400c001012040c0c0b280076854001070700b02e04010b282d40d10b950740a0750700c6d0240c54240f680442d240e000015076540c840c840c442c0d0286454014148211100561200b01c0304d0440006903002010f010101302e1542c085c90070003d803079200e180040f100c09420402c0d481c1d0125030740300074405120941131811030f20264011019541c800e45081c0043d80460141b1031103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 652694235 1250 652692985 652693009
    0xa090f0f15020c060f04140616170f06120c15040f0b03010620010f05040f030314130f11060304031206050f01080403030f1509020a120908160507091404030806 70
    0x6135070058000c904480e14082d10342c1e410612400f259000d00d5014841d0f54145075080700e0554440e036000307415141d100d0700480c450b003505d0f80c81c182603c0742d032400c000002e415450140016019071085e5841a0003904100441e071081040280a04040025800901495485401a00c001c0d441d0981c00040f2144008245c0c2c0c180d0f0019160000d140355410091003504180000c428815900c820030036108031464851540198000c041420648400e070502509030390502d081d26034207070001e00070401610140040303002041e5200700030075903121090400310140a0040c141c2d9500610000c02e1000301030b00100904000503040700103010711592001001b290f1079001d0001c0d404180c20034006000a0720aa10081c80c213a0500d01c0040c001c902e60b00d804041d002d20707802440c540d660001c1c078440017580040344004140e040420602c420310456a48580354050f01080110b002030f4460f00304100107040c080c03100039081140703003081400c00340354000c501e6800941d4181c021445c8080401c2c2c550600c400c6c460702d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 652695485 1250 652694235 652694257
    0xc14010e06040506091026060316030302120a0302040807060f120203010503060a0b030f0109050c18100308070804080d0504030b010e04022808120403020a0e09060f0a090f0f1502 78
    0x4108003204051107995031b815500a070030424001855100030302002045803c40301e1032481e12085150900130700d4605688258015441d03500c0e0380003040000c0d80040c001840c031002181e0692a40034824058010b40100d8000b0100c50180d84408203d035075000c101404400c0c03081d6511250301c00700040c003108a10080c01a0750301a0464000550821010740000203541e01c09022951b0b450220001d071402c4605200e412203031a040302881c0e0180c1d04d800941c507055540005000c0c44c0904000307100c5015041d89100c000c0071441c000c58072030140540d680c1560010300000702602c4070180c0103a0014926071190008403455100e400020601010440a4600c5594050580085401d58210307110071010b0642411f130f90f00c60804800304180b2070034480150001810420542c8803810f42c410040c51501640040c103201e1030903002c02424400006845412100369010620140c640c50051303406850b010360040d10690710340b0012010072184203483c461a50040911680104182c4c01c41c00682c030400303a000c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 652696735 1250 652695485 652695487
    0x503010f050904030c121d03070810050a090c080c1005040501200304320f210a0f08070c050a120201050c0a0f0b09010501060c030c0b090a0c14010e06040506 69
    0x7226504204240e00c0e0058041d04140041103129a21000740d036000c014124009008a03d80c19015035106c248041488001c5002e0030400d070070701109507075030941c400c2d500d45684d0f00d030380100f00c621085920203030842c1d81003080300c2d0406441c2c0010b87e680b4200548400e00800c00750165500051140301541c1c2542c4050b511003600c41c80241600c0904c42800052841600041000242800e604040d006411350180440c429220340340000160503400d480c4441c0c001c510200f003241c52540c9100c400c0d080340e1201e4410045044000e03e4075480c000500000426107070507107104009015401c0301404069215600803230900e40c6880c180091141c0520a013000000028107141c0198018000b5001d54201c507001c580b01c0c002d16454400240f140b8405c242c840c0754041c002d0240e42c102c20300072039026001e1406d03c030300b0501259400401403559204050090b030f1040001c604902c01c24088a01c0194001c800e5600c00d5850f18441a456190043c040707021039142003500b56182000000d450032100c00030911 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 652697841 1106 652696735 652696739
    0xb181914060f0f1e01092f0316030b19050a0608040c09020d0e0a060b2806032c0c0a090b091909230d0503010f 49
    0x540c000d50000e90400c01d03401909072030640c11004103a01c1160075a1040c0709541d04080340c080c1003403500c010000014441d07111f6000003039401e406542141040020842e01d081c1e4011004203c4495603050002904211170080211400609070802080c03040d030300070008951410080051036003075482d0a0500c154102041508098292410001400d04194445050502191280001c0103400148a0118002c2c03904020728000c003000c11942d40031590b28000e006425142d0600e0700a00079031402280000000e07101c2038044d1940441807011074103000003180500860709001508240c44c0850031040400341141c43c8100c200040507180092421042010131030103030f80140145030401e02140c49550b0350310011504440081404808018030540750b4001c4c014202c4040e00c240903c0c0c480d0f01485c4192815002080c0303440c41511040c1e99250419646130000703000b2150441c0d540001 = true := by decide +kernel

theorem cover : BRFrame.Cov 652517985 652697841 := by
  have h0 := BRFrame.cov_init 652517985
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652517985 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 652517985 ≤ n) (h2 : n < 652697841) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
