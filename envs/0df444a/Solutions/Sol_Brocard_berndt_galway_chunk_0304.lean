-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:05:30.974616+00:00
-- url     : https://prove2.me/submissions/3bcf3604-892b-47a9-a509-beed3c897707

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 54496406 ≤ n < 54676262 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 54497656 1250 54496406 54496411
    0xf1b041401021c140c160f0f060c120804081603020c04060f050904020607050f010203070306061106060d02090603030904110a0305010e07051207050c010c090905060607020303041205030913050702190b 88
    0x400c0455203491740c410030389040960b0324003511404074080306d0028400400b41448012074903440044254a030b01c5003c1182c40c0250800007030040301501d0b458206d4540700f400c035260b0003070003200e8a90902d00c0c040c43e100084100c40006034010390145c151241b4601d4140300300e000414844a10240b42450310021414610700204083d02c1201c0c045485018031005010840c41c41100030000c55680c40c000d480600101414000c03440002d040e821a0804480002181c1d4003a0700c2c010507041c01400325908000949100400e1190580410b12645407180c81e14003c0c9095001005041621103140300001811075005a006000144950040c81601a040811107004440d000754101e20783e035a0060941e0300e8850780c0c568400e958641640b554510798800700040c159066030006101544848081148900440740065032680080108003d40044130b080381040901c51400d80e42808000400100854940300b402d43d040340d01c5408000007581e050201a0142c0c1050780840c81848580e1158410b19200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 54498906 1250 54497656 54497687
    0xb040f0e070e1003050d08010603050c040503190c0b07080301090510031713030c09020a11060601021905150c03010f08120426030406050d0e010e060f1b041401021c 72
    0x901042c4008015110300002d540c0040484006c01590480103000440910038000000d20304408100c1d0800e10404540880310000c00614541e0303105590880d445010070400c5600c1610200000f072241c02c22000b9100c2d241c05800c600c3e407250307d8000e8040540b0401849017010307520f12001400000c1c40b000e03250040c0d00041004981780c00e50743c1100c140300b1240d508094030803250f000380060031380d003250020070081509640782e12003a0000b014550340d0ba001919050b002d42c001c0e64055481d040c030b00c803082108a0040c801c403081c0080c802144410001e06403040c140342e05001005224544061114500409481000b0016100100b40f8840140224010f1a51030020900c2580c0071503158000d1003a8841c10b601680d5490340d4402011305554000507440d10091304000300822060f006104407603081e401c0902034481a03450400f2008600c02c01030414580b0084c031056004070f402500d01402c043e0294641c2c012000c5480740019140000c4070107410040b080c45400c03d0a103a40c8082da0000000c40b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 54500156 1250 54498906 54498929
    0x2190b0717070c0e0910060305030405060a180906080d08060609060c030702030d022503020d1202031b0105071d0a05010807030b12010902010915082410030b040f0e07 73
    0x1059074009066210761000907082d10220040400d81c0c4d01c010310010300400e845001c82d0002a101c40d681e070300303030b555620001c6d05680007448100890705040009050b000d085140c448807111031030748089400000e42d000034800641e112024059100f0400c00c10b03855406c10708050135580b40c0200020001e01c21a04c0850217204082694000e1070810415100c03d9503000b4155a010818180c00a544d051142070710b490189106040341c07503600c140101c1000ba80e07005000041d1202c019111900f20300701c02030a00c0304500c01049115403d016000142c46195410030000c5501d041a11000b0020460150744c04010365841a142c442551500c8030f440441d4000e0914800c943e854200c1500200045002190013100e020090305c03d200044d802081c00303620036214600f0164441103202d50440c80300501c500490030840102e1140403072070702c3c0e078a01e00409024000194000001040105140f200703441c0c00310f0789030303e031968403440c00f401808402c0c0c1501c2c07010008030402e820225540d075107a200d06c101c0042d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 54501406 1250 54500156 54500183
    0x9041b0f0f260d120c030c08061c0506010b0c0c060306010c030c11130b03010608030918040f12020309010801050f010f030f091202060108010507092607090e010902190b07 75
    0x88480c03040c40c1c0c00074807802a10030f1008501d4010b4000030908010700d00491030040c6151005009116101c500c41883d80c4007403880e130b1058184100c04282c80ca03580c110091106480740050340800c42d990117000e10060440e1a0801c0c401068501102030a10078420074081c41000001e9a202642c666999007520300905007958504154541d0009660030b0340e0050201d1351845241c007a15080340c4001d841c01e5008120490b40d51800940301d000d1002da4551060031403040303807401d149061110b508a0b0180c01c150360402c0d00ca641e000e5480002e030b015400540c00c0469152400d6030042d40582c0100016680c1e48501c11255000901080e88038115105040c0c0c0c0351040414081704d07500c61002d80c4c1e84070341c0c40b54201c684003c1c007964070300c024854209598284400920000d10036000305044882c209180d800340002411a400c221340251000c4e2114444c400f000a00d0800034080c040200740030741c000060345035081c018080c00c0300b48643d408a00d07203030001c0c2c20440c020a4204035014a030b003180600c007920 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 54502656 1250 54501406 54501449
    0x606010806190b0d020405011d090c03090c04021201030605090604080d110c01020c06060a0b04030b070c11100801060e030303090309011b050102070503091806030607050c0c09041b0f0f 81
    0x202054029400c144400310340040104400d034010001e9410989541e0301c9d50070440795110a400348404280d1b0000000804903041e403803030a010310b4214450109850708001050003260480c2c0110803005c4403500c1100041090100c0303480340320b4101e034203100980384500c2c0948583e002d52180b5611112501c1d41c4854003078072400b2f40300c1680c0044d4028402950b8074071000800e1a40c9200503901180304500ba88400100c0015100440d81102d9104624003110340e41c125007a00d48002d00c0c001070740c0032990402000801d13600d850302070403803503441e8071418065410508002e100501c0d022505000f40e00c100148443c00d03900205682c00660240380c005c0c01d00d1041c00c0ca244140c540786800804640c00032a07207008012002c070207440000f0080e80c42d252003010b04031061440c082c0a699050300358001c000426101e9125100038072a01044008964020001070042500500103c0301600c0324948030504240e06c41c408a07095005000c180900039805081811102e040b044610880c840841c4007030100c40d02c2e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 54503906 1250 54502656 54502699
    0x411061b060406050f070c0512130b030a2007051c1701150206070e010e0405070302040510091e05010207060e030709022223010e0411030c0c01050106020606010806 72
    0x60040c041d1041c50810303282a0024010507100e1010003080307400007a490512034048096040c0d0003100400c03a154400d8071503801e0764070040c1d00203c00b48851401180c02c032650402980030304211600003030402c0c400481b030700d81e400a074054a00640800c01006000c0b500005450340d020103030808114000075403a034140c030700100301d92240c20000780c20800003598001c069900c8462000a80a40c1d0065558610454440d400541218041803044000090a080ca0340c4102d41c428010f090040c6441d4483d40002c42c1e00d82d803280c0380300001c2c0010300184010002e902c103c01414101a0000c00506c2c10039001035101d407442c0c0140710410058980b900e0a07a40e081015500800801030210742d1988000350014508105107514610803003000c0c000108251041c0e4031184140c982c00c11902840801340044030040c007890313542c550040d2210038101c81c025441c1c004502441c54406103030343e91200c442c64582500d105a01c4501550071800400c9102e90b0481281c0354003000c1243d44502009518a0380d500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 54505156 1250 54503906 54503947
    0x30909040804080f031c0e0f16030c0506031302010c030201151202010806031612031e0203030708010e010f0504050a020705060702070609091b0c0f1e060b0108041106 73
    0x510081040038481440a600001d109445404095800c00786070041e095131750748103500c0c2c01458800141d620b542035000582c0552400000c003c02c0c0c0d800d1a0130244a2403400b060034040c190042c00da06010400c00400700044001064103607207013829850000b210030b900060f041c2010707040c001000e429904040c803c1d030100042d40100c02d001203201d40c58075040118071028a004a002c108554080343c00c40c940000c05058100d000b0b1441e44e0b146052110800e961001d05c03004a040c4015802d14450281d420200c403038603803c0310313402076440707291811000380b03010010b070b002e02c6a91200328014081c1403800305011007a2601070350082200e407550303420b190080c407580750041c0603801450288105254040342d42c1d0112001c40e65080c400c40e445601210444003041c0ca41c4010701410050600c165014501055015020340c44d40003042845881c2c4010a5100e900f1401110090b084603030100310462050204074142131803c40741e14582556801d1005804410440c4512008240080e080b50703104210a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 54506406 1250 54505156 54505159
    0xa0e1912091d0403170f04110109090218040b0a03080f0a0905090411010e030f150403090e0a020901030c0305160c02030106050312030a06050f03030d0509030412050d020c030c0a14030309 82
    0x1c09000c0010402d022010075a0124001074070182da03031280520407060300c0c0c00f92425200b41e441c1c1c0c0e11590f0300c00c00a0f00492072028103104a4650006d0b80c00154400b400d00c8003046841000c126100760304000458189074083d40c401c1c6003100090001c80c1820003600d07048210031751025512090f07070382c06a50340178490340107552088194082104000c0703804c01c5520600b02c203072908901c025540c070401d51214400282e40c0300d5036000c080d003030a0104000c042c19801c00d001c3d00341020b0701611000200c502400460311800c9058002643e00351130b584c1807159a110a05a107010803403818400900b18400800c00070207401c00c1803180c2c014046d0754082d808134000308401402c0340c1481c003940c03d0354042500704072905848103160080001c0d42d41030030301e4442841c40740100130394640001d5a4030300008000103031811056100902001c0340003140ca41544c4d070b06600a0000b00300c0c5003202c650003807030311b0a5064141d01036000907406540c00e0b180c00f248071085e1040d15030904d0082d00c64a01103840c6014100400d0f = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 54507656 1250 54506406 54506429
    0x7080307030f090311010b06030c18060712020a03021203040816110406290405010503180a06090f020910060806040b04020f0301060503041505040203060c0a020a05070602060a0e191209 81
    0xf008040d0400c40740c2c0000f2820310300a20080321403800f0065540012140ba40c01c46408018450110010100303101014500500c5d003800c0202d203031280d542d00c4540b84007103009a480340100350f05142e010445401c26044c10403420b840e508c2c00daa940402801015820118407100001d40000c01942c0c003440f030300000000d0010028035941c0c00380607034080c004140500e5011020141c98011107060000c40301a2241038603a14910349804030b9821400e080c0d0880c1c803000340500b1040e040000d80501841c400c01d4000d01c00402600482d0040042c2c034000902250110203407204104100e542002e2207070340c044021a000602d64043c80e01060203441202408400c5000000c0007043c103c1d00007018500440c06a08040709200c2042e01d203c046072410b0314041c0d8180c1c00400055582a00c0c3c200030074521640c1e20564448800eaa505c5c9407400e95607402407405a00f2038010000840e4561145c0f000c41640d61000702094100d030345114011101c026801791000b00350031042c3c00301034003c0001324010045800c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 54508906 1250 54507656 54507671
    0x1912140c061006030c02150103230d03060e0a02030601140307030204030510060303030c051206040207020f0306150102010c0318171b010b0301050708010617180d02010f05160507080307030f 83
    0x103120ba0101c00c0c050f5001081c075020741d0302c56840c8000ba081021030400108040b0b541d081d602d88040942080385001450300188400b0401e10200380111102026140c402158150900d1040120f0710f0006109480300c603c10302c101300d2540c2c2e00c11003524210344188a4295243c54644084020307109641001e08140301e10182c00080200300e500c1042264044c0e5000c02c200c6010107001c407120b1190301ea80d4040b8020311400b040c1a40350035401001e49510060100b28019016000320f401c02c403048460b22460040081802095602070050100341911441c0070070454115603c0c500103480c001501501c0e8448040c1d00d00f11030320300c2504440040d8171402d9240c4030710044104c1d1074082c080071030110303002e03500b880045480d0501880da8107060310396988650401100010442180000040060356010216288a51240000d000c1c2420a2106500200311a100c2c40e114a041e107070040d04c144054000f131a05e829985511500b61071006a020107465500e403a04d00e001c0f070151003100304500ca0680341002 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 54510156 1250 54508906 54508921
    0x4140a050609070e010b181c050a0c0510050409020912011503060e030a09050d030201060e010b12010b0906030f1e0a02030411040902060405060f0409020c010c021912140c06 76
    0xc803940b05420403003c40721655261207000d420200c083c070440200f640148101d10701022030a1412141c50350182608a080070b60840e5031940d2101c0250640c0d0703170f0300840e401d4010321019480000c007524080e0388400c2407d42c3c1c0e04d8001d14510541c4a6020b003140d011800c000301c0c0c2e4590200701d00102002c802406a07a95002c050070b0a0700030392204480322440d0600e40b0451000c04001c1d1034207481d0325256844298540700a0010103088204100e045569484020075920901901d850183c000c2144403170f01c074040600d10340380b02d94040e00070032180c0c0018050096260b840001b100d52001c1052010040c3c0d0f19441d45404401103405004007001030700c8010000b00800079800703140319500408c208101d40d4401424031080358008880a90084c2003004140901d040440c02851045061130b0440d140c2952590304038126008541c46502d01d9448a2036006019410080301080d402d4001078054903000c95564807004500d082d6240c2c050081000d0740d0401110140c0581da08018051706452a51038900c8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 54511406 1250 54510156 54510163
    0x10306060815070e01050307020a0512031501020708070909050f10050402091e010303180b0f0a08060a0b0d0f061e0f060f090b03060a030c030602040509060108060d03030504140a05 79
    0x945503648a0b2030390b644049001400100e0084255031a4812405a0714004446a9000074040000c0d0701c01c8200c805c0005c1d400f0040054290310549420b0385038244103140c400c85d042c80b4040c250440d0b0201d0418070400360082401000c43d441d410b000a8006243d2a20500740582880495614010700484548088903a040b40f0701c2248220f030b8101c219074030301544180646110750442e4a81100000500001713004090b01d500180b030201e265444583c0e10030190f80103911406984c0086a404980c01e0740c4240c20081140d00300200300c42ea07034850b50130000c43ca030b06030152405a00d6040d07210403114440822561140b0054092028103a8100d4000b074401c400001c480c1c07084a1302003414400c002840c81c4520740c81d0110744196660540d907989071500d80f14032600080c001643c404400c0307800100040c2000141c0f0002c40c868000940c44030324000c06c2040d0700303c004042c1e50601c1041000c10505070307200d201c0341a09941c14140052141c4039420507018103803464140301124420545580184070000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 54512656 1250 54511406 54511409
    0x20901090f1407050d0504030e1c0c06020304050603040f06090803070c0b06010806030d0806150408060106030506060f090d05011424030307020109050108071704060e0c0a0e0105041806020301030606 87
    0x1c0005108241850246104100045548200007001401861040d100a802290300a80a481e0002c00044a10001404030980303041451080d080902c881c0700300080b01900c2001403c0f540007543c1028913080101d001880010b00003001032103003c9a4804210051f44103091068010b040d880d10703440c0c03004001d0807130b8803070759004e44014141600160f070759071040044521819010740941a56451030310300b0707a8414800b40060b640406041d0704008680c001c08050030080940a00600182d4548603002e801c6490260049001714410854540c03524241340480760020000c0d6110000c4914904089004210801c403881c0540480310030300541c11008007558007100d6082c83e00c28500000181016034030f101d0144000e0201d1080f46c410092503000f160500e5000d00c0509100b04181d594403840c2c0c240c036108850885a55603110040711071400b00b0810801c00b1081a80d0a018003424055060350800051080d03030322541c0c031925035098207030381c410140d04040e50158041d2f48a507100c0c90103031b000e0180f6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 54513906 1250 54512656 54512681
    0x240e030310031e080a03110708030406020310090501060903141509030a021006050a1a0c010c12060608040c090e0f01090507030b06010804080304060209150c0705010816120b030a02090109 82
    0x100042d806420303420207003c0c0c4150b0310070314007441c01da0306103001d83c040c2140c0ea050001c0c0768424050500421000c3c4c000358400c3d44110001070756803820701d403c80c84181890b00301f0030000303180900500503141c01442c40740c20b49420004401024402288240c40c0c101c03040000d400c0e1504150601980310800005080200381980030744002100e502c1c80304088a685100711548501003140c10004103440c0f2024074240070020f00003516004030302d10f8079803d44000c0305100c0c1c0000c036100081c1441d1601403083c030010704030310703d450055420562240d056961460080521203661440700c40004a0b04105062103603010700c0c02030108152070b007803c58032125584400e444550350440029115845445114495948060070a045840c0c1d0385030b900c020f402100100b504203810040015003584010003500c0c0f14a1254001d014041c00d18000615107100a00400740303c0c00100344041d0b150741c105058010a80300010002070440864001900e8800c0e80c1c2406034009000400100d880d11070350b00a040c0c45200b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 54515156 1250 54513906 54513923
    0x80906010b04031113090506012c060f040908071104050604060509042a060c0c211e0606091b020c0d06091a04030809010506031c03020a090902040f060e03010603240e03031003 77
    0xac1040301d00002c600541c0f00004118400c0001a0f400c5c901404085800f0fa4007074000500e0810740c1e62100c0a650100e8000d8905d04149507450a0a2601d4021154411400d2352f041c02210701c1c10380030506084000d0002010b017440781400d1a42d580c00080c0203c0030310010790014140543d60000070b090a04200c406540148112070003185034201d0840b420070003a01e0b01e00030003801c001611038680e40400070002c0d021005400c0c4004011a601c1d02903000903003151140007546a8403040303c1c3c8004814218048159000400042e00070740d200800c030b250217a0000008110300d50f0768545014a00b1441c0b55803908840c007007043c4018140e08c50b400351f01c10506507000304400d40710b0504169481408aa00c2001c4076803040c80300000900c25006420000854180881c10b40d0f11016090140e030403640080c81c40810b204020031065070f000c3e050003a424030a0780200701840c1507490301c2410300c160007002c8600d14101440b0f01d100c0d007110b40c0308a504215203c01d490b102e00345a03149a04460f903a00c0207075407550 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 54516406 1250 54515156 54515189
    0x909021806030303040f0c051302040602060a090201050316090504020703030c02210a0509220f060504060f15020a050a0f020f010503090c01080702010b09040b07080906010b0403111309050601 84
    0x801528124000c0381c0080080d03086960b16a55021161003188089903441000b900c0020300d070302c0340c0345140c0f5420040740b0050303126070500000070310305040144110006402d041072603000d40d0b0030400301d07504154408159148100001401d03110004035a000315000303880080c1613414160b260b40040b54042c1a13034280c3d0001000000d2a1204901000003005801d0041000160140c0100b00400c1e2075000038104020403a24125000029443c04425030089a1605902c00315a0914400c01c005410112820009141806500180c0712903a00440320758001041072070131464002c20030a010154464100c070114001450800f0621501c00d6080740100300070341e0000000d60050301580d100310021002003000708a900300445d1182005080d03d800e6550350900a440351316141074051181c1d01030352080580d130401e05801002654020110000b5030091401030100e420340c507040324204d9802c210b4440116005000003001407600d0326a120525182a00d44010040301060312412952944071441800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 54517656 1250 54516406 54516439
    0xf0c070306020c160b1c060305030304061a0105040303090b2b0e0105010b070206070b060111030406050306030d0e0a0e040c0b0403030201230106170c0f0c0601030c0801060e0a05150604090902 84
    0x448a8000e20344008006e0018034500d494505502403030781d121070000301d4210b68035299181035034000c0e00c091319a2030716560001000308803628a89441c840a103001032400e8a1074070002c00385007a83c094a004000000fa440c03c2c000c3d0005180c008005040c42202d4051100ca001900108041c0f502040103509042c000203020881d00c0c240c030f030f03010f40240025207009581c2d07603001c2c5240d000030412814002240034190311500e0400107403000e4000e03900c501d40d45c0e040220401d0300d41405140a80c2c00c01444283c014203e0300c682400f80c1c01c680020350003019607140c0e841c007140000744039040519a40c4d8007082c000203043e0f05411040c403104e081d10070304801c1c0c2c1c8000071348081d0302000d02854020034161090040c01580d88400c555010049020890810003580d500c0c030440c0c0e2020390902d1486d4840c034010f1080c0b1404812250080840c14001c00c411490407944400a10340103013002c00066030341d4001003120b10140940c998008004001c583d0b04e82d112003020780244120601640640e011f100003e024 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 54518906 1250 54517656 54517693
    0xc05090103020112050601230405041107051c020309030a0b01092301150c02060a0309020108090312130305130602010c030b06070f14190b0403030e1b0103020f0c070306020c 76
    0x607690180d4411201e10741d00d09424000d07200141020f4100146003d07150244034002c0c0340c40001005026109560300d141c0800c0000303540b004469190440c108010010004000081102d14407000c0420b0701018000d0b25011b0f802d5010b00c0c48030b035425005904070442040100e40701607041c2c0c8c100b500c042015081c5240c074030358802c041c003036905007040d10400141f040e203c103031820032035800703491070280c800021030340c08a140d9410012001000c00d8a4201d644210f68028902a91107007400000714103202d00c40d100b0798240100a031100500c1100c00505200f4584a103003117440d201d4040881c19000340c0c0da031000900a0407445401d200281c9494110344841c03602001700c1c0d0004c1d400024580c80e245154441410501000c0100012440b800009040c903841e00c0e0000c00c01c03140190325441e59854a41005419240d50a0f60b80000d40c100380620140ea804880340401d03000340a180041c3c07642031140081c40036200300c64080b10380388900440001008a0b68004210140c03909044d6a034210100703000801 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 54520156 1250 54518906 54518909
    0x10506012a08040308030103170f031302130203100e010803041206051509070804020414040f11010315080307050d020303010612020d0b0d0302100606020609030a03051009050c070c050901 82
    0x7031000c0308000c4000c1d0780d001510603038416100c0240c84803400c41c0c0e40d03941998003c0e40103ca01c0d2030040010018020345801c56921a102000010b25084a01c0d0503484284001070400801d00100700755503095403111459070340c42c6807040d6000c66603410614081011301380e040c4501c8401e26095000030074000c030044251001c89080d07046c2d48040c0502503403035101410008100105580107405542220740e540b9009600550b280d44034003406040500500054941e60064050807450050600001035210000548160b422030502e08405800500413405403d10340281c010240d0f40190205180501000038030945100d4800c540c200d952504040c0c0c1c490009126001c00720b6400c8114044081c0320360024203c0140e07041c40040c500d4286d03c00210204005c1c041640184e202164460551a09205903000b0f00958001031925140c45410b9540da40305a0010004054403240451010421071003070380007502c1e019809011a10740f0343d20b2a032840e00007820948030400c0404c000101c5050002c0880d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 54521406 1250 54520156 54520159
    0x10213050102120414030a0501060308190e060307050309120c0c030601050a03030207050108090a05060403050417150112150e0a0c060f05070f1103060109060f0503010e0c010c0512120711010506 85
    0x1420139141403190394138202203a10440c3c2500a41222200144085c481c800245101e468250345503040c000d0301c10055082e5100d000e041c000740340c1e95201550785400c140e0364005214a000713550303662501e52a074106554402c41c0c41e2283c0c0c003c41ea640740c05c640440c0d8a00f584a06808891050381d942c410072003041d0182c4000340140e0030140052000c6e52050407010340c8160110210740c40100706984042c13030510300701d800b03400141c00458184125a044c03200120214000300003020314840d50034107142119410302c910090180701b03403584000c002c4c800305200840d6250080400c84001c407600029103448110000b142c05102490012031003500407249900c451480c0c5c2c1d10b040c10040556952154401506410b640f402101540500555000c10805020340040000441d2003490240036080b2007003075030061440b9904140e45010210000950071000b0b15091803d80c0103c840c60030100d04111045901102403200025000e0000c41100c0e6210b0080070aa030b1103035840584492001e080b01e00c16140399 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 54522656 1250 54521406 54521443
    0x301090c030204050402060f0f041a0a02122b020a0e0a03030206010b07030c14010b03010f0b060904020d020f071208060d030c0b270703120305010e040b0405030714010213050102 78
    0x61002d0305099020030b52182c805020a4940070700004544440e070464144004141c030006001e001d2080103811864140c16100711060030441d0b03100001c1c0d103d03c4010480107019101050640c0e001039045001c0e0066003480b0300f802c0d0340b0407001800d580030b5400388406070042030031440c11740d050741060080d6000f16a0180d0150003140d0a0414020352136002000c16402c02061000807004191504000e40c0e01a40040000590403200b0046c54203540342d00903d41041803078920008050f403900c0e400c59044501c1114016a1450030b55040402800346005403c441d01c400b05e00002008500a92010f00e40c000e5140e28581e640c2d0318040001c003d200a400400141220f8000d00018440004494002c8481074110301d07031820004441d00c210340401040c5080d0b501000080090025404052614101502e0300740165030400602c454000005003004000d03201c24000102400410b00c10f858003d5406900c01e4980102011507074081e4200c0c43d10100c20300d4109100282d070b58000a6255262038000c601e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 54523906 1250 54522656 54522659
    0x20a0f0305210d02030708060a05010201020f0f0f04030b100608090703020a060c0302280c230d03120507030605040b04061a0d0603020603070302071a010602100203090115080d0e0301090c 82
    0x201002c590b0200548031200090040d64900e14050000e580b14019943d281d0925140080411481c0800ba5100c0c1e03065900c10001c0501002070b181c2156409040c02a10325501c80340300c407101c0001d104d41e61005d8683c1010105220511032081c000c807003101c800d562380b0803071521100b10a940700c0c466844029800810024100702143c02340740608002070090054030b500d1030b45c202c0d000480d58000403001d88065004c1d03843d0010481c1c40c12201c80a04000642100012000030300040c4481300c400c10280700d12200124102014850898a048081c0461b8207000500708400301401400b030500500c2d1145003040c40c5030600b03040c03a201705030883e0700001107a98200c40392280c1169540c850020486080d854410101c05030300d4220081d4040e10032640c0059840c1c1046c10001f0617441c0d00007449005030041c80042000981c0004e108203c4074608200580e20341f03c80c00030900505800007100c44200412070300040150700031490308034010701c54031035542c100c00031400c0608803040350030010584801c0000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 54525156 1250 54523906 54523933
    0x120c01210b100302250b27010204060504140316171002300f010501030c090e04030e0910050a1701140f070207060804021f1404080604020a0f0305 64
    0x968008803081100300140c10244040400c049203a07007102000481e4000440384280c1c103148200d1041401d092048507401d405070b50b9000c1c119180a020b5100042c01c8640000001550b100f501450328200c00085543e08c1c0e5410014080d500148601c3d10407010800d420746441c2400b0940d1541400740c003a22100b20390800d6002e030040007500f580301000b84503451543d100040c0c5480200f1241c100c9885091400c0d804c0700c01c021010719140c40c0003064104410074040701c1ca4174940802e0561340c003400c02080c0160140e00459600c0410391280717002c404040b0500040c181c1007d00c41c541c1c0e41090780ca404c1540e4821400b050b00007020320600ba000401d2807810048000e1803045503c0c500541e000109030351b03d00d203441c0800d0440c01c3e20140c0310034108100348869a60100116002014030341000d10203868140c0024184032071070324194030460350007800c00400e2480341d0041c0c06006041c1802d0f58982d5110700640d907a860084808900446001001003401c8070180890300c1129407007001050300140000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 54526406 1250 54525156 54525197
    0x10608130302030c030a030510080309010c11031006060e0102011a030712021f050409050f13230709060e0f042607080f0703080a0c09090903090302030609010506120c01 74
    0xc0d020703002c40c0001c2c001c40807040000e10080001007000c4d5004a001d040203401c1c0743d0281e031658010380841d030081100c520166042801451410307000980c004507481503030080b07070808001400001030b903071074001c0215403c0d0700414180740d1143c080e4020044440914501503404100c0c403195985940460010800d261341840c2c2030405502c081c2c01c5001c101200d90180c0e803070301eaa149150300450f03008101481034582c2441416404008105070654500300301c1d02d01d2400701241e400c0a00010b400018000201600c0d0440d654113046400459011590b11410240145081c0c06040030400c40c010120b02805001188103000c0e17070f0001066400201c510302482c2d080c6150002c610049041880001b0100350000702500e000388400050f00d5a95a4600d0020484003005140c050440e142c90f0030a041240c1c8841180107540d0780700d41c0020300d080c2d5410f083c0c620b07200b5903000960512500307040100b83c4406402880c010b00054814031000380c00715000a840c0c148008100d40080c0d41844030200c40401171 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 54527656 1250 54526406 54526441
    0x10302070c12050f0106050a06080a020c1203090c0d0203031204031107030809010e040c080a0b040b030303100e0c0403080a0e01050c0f071a07050703020405071116061205010608 78
    0x1410010325002050362080941c1d01107030312011040444886031024400c05003c1e2840e5090148001c004442c18140000d04001d0b0740e001c2d2404100016000803400c040c1d9504455541d0406030444519055102d454100ca03480dc0756450340740c0c040c800301181581888800321a046074020051400d1aa01550340994084000c00c10740402240b010b120410340c1d4144101c002450050000d9035682003040005015540d50031200da025910303111459240c0c542c001e0286401c1204003a0100301c5000400014000d0070682c0c0840342d042c0400014007520340d640b032046001301c640701380c0e0b207103d203070303690754083c411405548000340c00040104201c3c5021407041e43c1416204005042103402d1402c0b0410702480c2114140752800a40c2c80b45006210045100e11041c08454204240d135180a1259030746648400a41c48024026500c441c00308108070300501c40880c1342200759048072254969031001d01d00000052080c43c0208401001d500000400c0e03000e0b0714180c07040342e1281e04654403521500404050710 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 54528906 1250 54527656 54527659
    0x3070b060f09070c12110a060b0301021c020d06080102040e04030302031b0a020f06060301060b0a0302030405030d020c030301031101030b011d0a050406090c020609070e040b130c060c0515040c050f 86
    0x800400205966910011401030301182d540e181c0b0981c262401808240c8680000e00500c2040308201030500c80000c0c19040307c030350002010610741c400308040380c0640500707200c030505403c81e80000c201d8080183e0152104e40c1d004503050115566546041e401c034400c60050142c40030940002802103030082d0010f40d000344010920042c02042d05034001c08603008441e038140160069444d043e488101044056004202240200035282c0b40032044105031003811245c00030f15401000180500a0500c00d172038801503001c00075507a139032102101548030340c400d00046038100b12038190102554401c0c0700b0071640c084d06031901801041000d40e103400030340600c850302d68465100350300031400342c0711401031078000e10752100041101d04071614042e00341103000340300c0707540e0340c2c0f00d00300801c002c0c680c401c400c0f50010340041d001c44180e1201c0008070808a0028000b41ca0003007209400960260b024a89a0445001d04207030303040d4040d210b41108103030800351400707042c103c55804c042c0201d00d440c02481b2102d550 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 54530156 1250 54528906 54528919
    0x11040302031e0a05061305011a10031a0a080c030706030b01080402130e120309070e090a031107120b040204050606090f040b0120060402120706090b0d060506070605010303120e03070b06 81
    0x3c140d603040e00d45031044402203500d4a175060000100b040900455449806480c1180140c0d84d000c800f1400402184080b24105912a0254011f4000c1000c05c1c480c50704020b01070503031080d00c9404280d80e40c0710300354080d030007031207000030006505101e445a622802070595a003545a20f0701c1c0c00300209084040c2c03415003950f644400c525241e200400580407800b4002e202d031030720703460b050411074200760260740078007401d01c0514200032607188045140c8100d5581810039803041c007000d0701c0003403515086401200301800e100e08514184800300040382e01c0340f482100c06000641d5464180899070048101aa1300b02d00c0300804640c8906c1c06400c6000307040d00614112507041640c031912040c0d1001c1140b0391805420200c140021350912840d044c1c0ca041444c0c000b0070115203031100c02850905140715940c1102c0003c60313684502440703900020700070310703005103015200c90b91801c10303034003c050a100440c00318003080c01c07903540000d40d40298000d481103d4007031400d005180c0c40d01c2e82080c0c0000d181341c2d80170301c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 54531406 1250 54530156 54530173
    0xf020c0d0c0905040b0a0506030304030201050906030a090203070e010306060f0510030c020c0d0b01050406060503060d0b04031704080901090501030b0607080702131b0f050909040311100c05090411040302031e 91
    0x70b01920541d8410703401810201014248005407104562014011038042c2e0020041400982d801a04480c8245c00a90707009950340d0368032598600910584400952501560383d000498180e018080343c1a40d0117030504014195031401e0b4400d14900300d104440d005940e41200d070700c95078001c3d803041070309008078010341c1c1040f2000744c001003541d91412800c80c0c40200280040c06141403600c2413001070032227401c00c140b55042004c001241e00c803880c00000c2540207840001400c0510807156007a19400c41d1010440606043c5480401c1d074000c002c090340050316a00c0009003035031281c060020700310340c0908942c5c54400c050b250000d00d81d00c61001640c201c0e40e09942c000c4040b5180c0300e4004010b00b45c1140d000c2004004100400d00d50391b03090101c0c200b040500603071800d6074910312415003056160620074a40302c0c0610206d800c02121140d4400903614220f007421030990440000d0442c40303130032282046102d140c00c4884025009030300019405500844141c1f02006100c0320f01c46000020340202d03066030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 54532656 1250 54531406 54531419
    0x80a051e0a0e0106060c0326040206070804120309080c090c030106030b0d02060d020c0d0c020f060327010b030d02160501050a0507050303010902040306060b03070c06020906090910150f020c0d0c 85
    0x4921175030080380060980c8032042c0906900c40c1d1406070440c407013501540300b16101d0800340c540d00005030000e4440ca4000038407404208110303046070001d04c00100090288142c0d818050246070b81c52103a01c02502501803031880618141020a10401ca01ea07a030505590074004110000d1081c10511a0007450603008040580da03800040c04002c1e0015070007503524282d20b11980d0070003048080d440b0a0042403448240180e1303034441c284000d10400d807140c035200d81c7e0703203403000110744100614000c050b00e4480b40e44c6041e213419000194895402c1d801c0700e40792030300900101e07990b900c00c0714a0314144000342e40500066100b040145019001480c1244c03c00805860740d901310790081e80088241c50740020f04004204243c015a401040800c001c0c40c02e5262000c806808264401da00900340395000601028503a1450192149404082e000c407110f0b1620392410007040c0c80c0c9000d4005030409a22100b41400d100f4442c40c12062001d84c041d08110a5443c2408450070078403208680b401d01e10a000b0030350 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 54533906 1250 54532656 54532661
    0x18030a2102191506170304060e0a0902130303020106060509090f09150a060609150f0c14070315050a0501051e06040e0903071a01050d080c0c0a08030703080a051e0a0e01 74
    0x140c0d401140342071540c60403605044229450741d400307070b011702c80c180441c100c0361038021017580d080b55800c0c180040b04100e044002000a25140c2000001c2c078804070325496007030001c05111003a00d00c039400801000d43c60300c100b0f452038001c40f007040360b01100080c0001e501c40d003070f0340c0c100d41c020100d078044814084110b04c040e1503d6030b0840b00448642da540c01c08010312a40100345d00024280d20000b21b16103802854001e100300c15030803411081c010035000040401a412200c83d01601d4100240d5686540300c0c507000c0c0d106034420301c2d44030442d0b00b040d000c6a003400c018403481d070407134200030030148103808071b40070b05504003d44c541d4440d482401408005070041001000b188a00d2104024582d14040d6240c60150701c6e286e410007000c0002c84100502c2281c81b0004c1c041c0d0001e8000410f56251690a14090325104884030300c1c0d900251000c600254061001000e030618510a49658220b540c40d80a42d44c12a0700440707198041c10780d00c10203640c036100075030308aa401900d004070101c0c03500082c0003154203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 54535156 1250 54533906 54533953
    0x2090307080d020616080105150a0e0301020a050705010f050903030615070f032a080906070f0c030809090c070201020d03020d020c060103080d06060302090a060e0102031e18030a2102 80
    0x90780003801000001c0180b01c1500d8480d40450500d84c191f5410140400c00c804210904d142c0d00a90021b9404582030103004960740c0d24030014008d5544854001d4001c00a4014190844d01503080c100c90070036540c810f0284a201d03040390002541555140020883c1c1105070051a001c1508100b00c2d040104188001d04004a4041e4440304543e102044883d0500c5115804254901400760102c40015003034904581801c0300440e155a101c0010b070410b00140071701c1c054002c20000303901100000300080b1001502c9150012188020b481d580d0004880040c420003500a0058208550485aa500a0f400380c40700e440d10340300050034640c0500a89150030f0080e00b05498610740030803041c91281d42409404003402c5589429070415a2391070100d40280f0b111701071b48091003005446c0f116240d108006542600d40080801c0c0c0200e081c3d00d296416550202e110201c0305100d160a00d0507a090019403041005da00c015922004c17a01c080c0d80b101500300341e03041a02103016983d13990f510304481019051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 54536406 1250 54535156 54535183
    0x70c14010902090603010915050712021305010908070303050703050f070b040f02030c040e07050d06020f03010e061504030f0303110d06140f0f010503011502100f091718040209030708 80
    0x680c403030315004003c0402c00c002d0031284268107000210b400103400c1c40c82c0c03841d041c7e000440450b05071101003060340c80350764000b64040e181e44041520020010b07001c196500725a0280c0b100c031942600c52942c00d80b10101d500024001c18800c02c008030000344254010100582d070603070168202503417907079070848454058506840e040780000c55002076140078000310201d080110360402221800380480c5d070b03d560b900d1065a104601100e0310340c0600407940c0446a4030110468070396501c0d030b15504810098041540d48502078082c03106640c050040e40421903090300d800644408103501c181e60124041c200513155480c2c072030030920411080016a00031840a000c4a2405105030b1a40100b80300c4040c1e03001c403800348542d44281040c03005982050071681504c07201d5100ca115400c010905902d0041000b01550302580b03409007400007800c0b181d010120b041d02c96803500075000d076450a05041401901c01c0c41500804d150142d02e081d01e0544c0c02000b16a074083c00752551039566101c50b40c2001c000c444c911 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 54537656 1250 54536406 54536411
    0x90f04020c0d031103060a03020409110d0b1602071a0d0f0e010c03050907060f0c0609020315090d030507080c07020a1509030210020a051c030b030601060f111c08070c1401 75
    0x204111505801980340d043d000044c5a800c51034140d0001d1003405c0309101c0039001d9035580c9141000d01a6009440c28004400380031400c14407070074900808141c03011980800485070f94038402c8242031000c1a81400c9030940b00301403110448803100d0320700070341c0004014043c030f41e90f1b602c042c000c40800b4081c804104e0b4258000041842c038440014007070b10b000921700800b0382c025803002d00620b504207031603200aa5407485d000c501403006140010083c41c031400c004e981445080c40501018111004591080d2249000c3c4c815031740c080340c0190f055800c280d0f05080860701e20000a2090a07650001e044494002002d282c4810350b01c0c00c4051b5210b403600d2040c0700107400900700313105604040b0310140e1785074100d10042c00700000686400d500c501c07901d27250020020072008034040c4030348240c1020b0f1140d0b000900b079074070b196901c0001030010003c0034500004200c40701126084280c001c55445440300309001c0c030061298100b41c0889604600900120a11010452070000303c0c081d10440c440446801000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 54538906 1250 54537656 54537673
    0xd0f0c0210230903011a03060114150c06011a0a0e090a15090209030c0a0609030605060a180b030d09030302070b031f060903020307090204030f0210030f0e060402040507080c030705090f04020c 84
    0x313060070f407a4000d8030341d1565580e086080b10f0688000510604580c0840b5140745041002c000186d101d44c0c0e80c00203551260b40100b515050300c000803542d58100c61800c0541c098140351112401101d0041407403010102d848101c821645041c506c00c120761000310704000141c10ba6400c0b44051141e0096040300a505030302240e030b40f01c81e044c100059020b007a0219942c04610f490f0031402481000f80c0d0000501154480011440c1a140d4a81380d40160090700d03584150501150a0324001f001008400c6120344103806400260700e000f29543c1040e240c0560103000000d040c00c148140c02d030b1000d045100b00d207c00c40550042c80203070301701c504c1c09824240e9440c03420b1071440c01003600e0140c0503085110204e00c100400c20019101000030404d207030b0f05403110450b6001c0a172081e0010104079180c00203060414107035800c1100c0104e00c0381d200300e100715001c000a49503000101c80006c0e00320352040c94201c0030000306140034002c0c00500901c0304000c1110704280e10013408070f010782e01700c0048048035601c80080f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 54540156 1250 54538906 54538909
    0xa020a021008090613080f0705030307031401060905151b1e0102040f03030e01350a02041202120712080414010e01051e07080301031101020d0f0c02102309 68
    0x72081005540d5140000c8281003810009449690151110300c80c4402e14803040c0c00c10107110241e440941ea4000415204d50f01400c0854482c2c0c0111400000a45013404907499142d41503469816220165500b0000e281801e0901c410614003070800c0134503403001d010342c90980e03030401c1581400c8511000509900742c3c00c01c0305600e5403080007642d1141a4014401030000740038100120007240d4140c6090130b040d86040c4016100182d60803e2284401c0c10f0062014502c5440e40340b110394036030f201c1141e00b55903072907442d024103d01440c010303a441110000ea08070007500e06008000c4030404040140d44900356105000c0c03501d4650043e0403122094040380030444251010115005084203003803035050920000002030042c440c01441444a1884900f00001131189005603246554001c003020b94075616820b000d08800a851140c0740140b080160159941c4d210303010041c82da140c1ca48820318050074aa0810000000082030380c81003103004036150303c0644c000003691645922581003a590740c1c0e0600c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 54541406 1250 54540156 54540169
    0x20a0e16110106150509061c051902030112020f060d020a080709050102060912031506070f0605011e1406071a01050a0b07020901092007060516030902030a06091103030a020a02 77
    0x70035642590345041420001c00b409200c0f0300c500b001e114540280d6500381034002606601039943d00d5201c0c800c1081c00c03002c442113983d00c9107006007200c0040c2290209148600700692100740111030f0b800004146020041c100407a4a100940000346028101260f411081d81240c204e0040764000860100038020000e4200c074072100580740c03e10140c011882c0180c040360b034894808228035105c000010006d0641110961408500341000707089598404060178105468803061f50255240c030b00d8100002141200403501d0745011041200114046181c09540c0b000e003841c17229203682202e070820903600000c0e06200030320342c00b03040c01e5252905541001c003441307900080c40e0030a01601c02c04111020241e980e000c607803411a200c0c6030000c1880c55282000030381c244e40025400182007000306090f02000000d40145100f641d00203081304480a011004400382c0d0403c21000e0b400d50400ea1203034001c11800c1d0001c0e070b00076000d140f8541141c000100403a145030b00002244005030000402031085240a0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 54542656 1250 54541406 54541427
    0xa02010e0906060306130f0c02102f0f0706020a030509010501080c010215061c05030703021009020d0609030e09010b0703021b0619090902030f0f31020a0e16 69
    0x2581c2114031441d01d40040703a002c1c480540283c4c800c1074030325500e40e5490a140c014030307400c0408a10500c888410010040c0d528805210f40036000ca0600b85c040284100340c000c030f1000c180d0318050510200302c2c0f1441400059100b800200c0480074100a1000882e415000070186042c96960000301403506840a508442041e00a400d25800031011690242c1e40000e948040b5040e00f0f000c9480c58030740c03000062102007400f15000f00c0b0021802000180000840501f51660094081c2c4030b05403030003003401048070800040250310803152002c44000c07a11070380c882001b5a100b401c022141d100d443c0006415400240d01006d03824800003080801c00d681030040d0314003e5820200c0c0e031340c3d00e40c000c0700040c0c807409a5402a0003d0000b03030103031903c082c07080c04024014003891200719941d09001355600460305044440c60410034040e004200a8542025a141000e0040d8010032a9542e4050078040300800f142082c1da0190030114046119900b50103214002d01d4240700800107001022006400c45a00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 54543906 1250 54542656 54542659
    0x30402040b030604080f1c051f0f03030f0f03020d09060b03010e03070b040605060a091503060501080f06071d0a0803030601180b0703051e0304030228150209041407020a02010e 77
    0xc1c3c09110028503008165902d410002c504d44e929079003070940c0d800c080b2a986254040250800040c4546c1c2c501e40e1005080788910412401e10154031022020000c400f6071000a00207075102c100d1000c1c1e5407084014a14545151401600d00010704580c1810380c2c0340c5801c141c440325500c3c0006002d40c9401d2203089004a00c04020354281001515036440300d0f580104003501640c1c4030300000d001030380c44020440180c00d02c0c230700030040307520045e01c070f0644017480c0c0c0400c035169407a080010500030400a94014901d100c0c03801440c0f15950004112021065640d8a040891595440d0b20491b507580030558060202d850045481e46403540c0014180001d0801b02d00c3c40d03040d06442880a0719000c1e0441312515014244669107032211400c048a0841c658801c040c07030300022041c0300405038086080301d511040204042c020b0101000c00001410500c0b10081c540004003400c01d07404492034016180300c0b84018800110f0382c002d0030820700111000c07501070300140c00c00c0344610215a00541c0403648500c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 54545156 1250 54543906 54543913
    0xb070806030d0f0c02060f160c0e07030506060304110406080304080109110405070903060b03030912060f0705160204050417030103031701060221160212100b030a050a0b0408040e0705030402040b03 86
    0x10b112001030802061070101902030000001c1c1514400d0506c0c00f180d03007a900c43d0308c02122000c581d080c0484680030f40c6c000c10942d03043c02804136000501c40d0142e076000d21002032201e813039a11a5034031111000014032f000c9410070307114100002c40402c02d101400042201800110b601e41c158038141d0010300d00883d0103403080b460b10090001d5503602c141c084090380d9000b0000078201c03492500103813660150038003035039001c82900c2200ba80c134040410680c0c041c0c4280b121402c0b1540300c101080e41d41e809160104001503120840c2d14004d45001c0d0805500540115070065002030b0419080c1e00552090704281c01044031103800080b20042c2c0e0b0710050060009101800c41c2c810080c01040e119410041c0483c40c0da04040381900b24880040d0b50b91011650080492000c84404210140c0b5985511009400759151080045060a02190301d8450550010191164072710554460124400240c42510040e006010119180c540c848c051401003600e078494507141d140901c10841500c18042c0c0a501a40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 54546406 1250 54545156 54545177
    0x50619110d0e010f050c100b10030603021f05120f0603120304021509030c03100c170c0a0516050a0302160602030724090c140f150901120204030b070806030d 69
    0x350b11014010b02c44009191441082d40648411201c40c021101a4907180c0600e0a2145090080d90701c0030b10504400d95450441f0001d0400035001c540080c400650006012a1840040b081c2e1182980c1182c1407800c0560a122446160503040201158543c000d8407010090101d240340404c85a006a590151160b01c1c51620358081407201541a800841010000ca001092a80d050100040c002400340c21640042d510a1400001e49246415100403658031380c92070105000d0512820310804040f0f0780c8500e41800e0820894090303010750005103424100f5000701e40001e0062143c1c4141c06d0203913008114030000008096000d51141d4440340555000f00b01d09800900a5105038600c0c1001d0b44100280f50020681d040c040d0510300340040054140480105044116808011020005640304060342c554401070105031030303c5009241084100b4050300c1000c0d17120381c0c94400d80c2e051306100507040507500e0fa0380d10900e00040c0c8008000c5103031107041011030700f01001443d482e15820701e070140808 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 54547656 1250 54546406 54546433
    0x1030204140411060d0e06040606030605070905010c0206090f120f011107021806030c030d18090b0114070303090f0b062d0d080c060112120305040c050909010605061911 74
    0x1d603030720f0080c80c050034000c01c0d521078401180d403051810f02540d00a55585203083d00c2c2190080240d400100e40842c034010200d074410f4401c04150702031b00e0044c8c4988203034141540800501307402603907420340c0c002c0c0c036800f100000f9250030701550780c50070001d0010301c030004200c0121425900d051086c03400c000e000b4802007000da614030080c411409440c0e6012000c517120800030a040c1040c1c1c011080d0188602c451890540d80e20404014844603020300d01c20b801c0c0c0c0c4500042c0c0550301c501c6071050010715030b04030b00341c15141c444004041d407038403038200000c00880f40c0e51035203a04280510192014105941046201e0600d078a0150724001d103100b0480d4800c100c0c000042e00c9429050b0801e00a8080d600503078204102d030b81c21281f10700c01a00448480d50b95407000005001140c01d0121080c94009103650005402401020b004540c014203d4200b00d090074148501c161000384182e15540d00d5640c001002d440342e8009110070550301c4284803007101c0203d03018103d01d4100101950360307070102e121600c00b03 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 54548906 1250 54547656 54547673
    0x105030606160203030a0c050601050906100f050706060b0316110d120902090f01030309090204080d03090203031c02030a060f081e030d0e03040302011106072007030c030605010302041404 82
    0x200344211016a2a060344414038803400701c4205009415101c000b0742c880b0b2240c0c100415001591049044516581c0c90b441400440081641c141d074100200035050f8050600a0442006103415498000d0506107261109810340c2c81c59440580301401c004140710a900d224000d11100500034140619032a0300c6030307961030b582e520402d6501c0800900901c030103040a0b0b0750300900322203a0014141d11705814403184180c07075800700b07200840200d00310340d4000034852054000d035411124860080c0c00b4441d00307404194050100c0c9842240d050108210840702503d403203001003900d1940040050712842d20542e0030382211426000312400401301e0f081041b14400000f80502640240803c007080a503c0804981c40c5000740c0c441c0c1da11031030608205403645500080a0f00450707001340e03101c0450303440c00c40009440da40255141400510800c0c42c4401c90704021203e000ca00380007808582246a407602e4036060041180c0003110055203a82c01081585460b0080a0b0020048000b42c48641807540c1d0b14911f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 54550156 1250 54548906 54548911
    0x90218061303060506060f0c150105030a03020c01030b01120c030605012007090b0105070f0302030d0510050d0201080c040807090609061a12150406060e1206060d060213120503070309050102010b010503 88
    0x88141c68600045c5591110702c01d40c0c2500602c41403003034480300c0d040182920b910380d0000c01180840410000141c4c1c0c80c0001d41040090b8054001d0800705141c1e0004401520b903020fa003505104402049204400d1107100d1240040300aa6000442c01e040000043c038011414000403c1504085511a5940c001007008401c4548030100082c03680c2d003050043e107890041c2d10010b001c100c5940062414140c01000910b02c200c8445010071069803000c6a4194003442c90041641005500092100550189018a42200c1002102400c02e80e03a00c02d200d14001003600540c525940311282080801f41d680034502c040c16200c0342c050005900001a0b04d280e0042070b010138202c104c0d00303000c0381c595a00c1c0340d455a900407005c0c1062184540324030025050b10280041c441c0280300d149030310001c00001060b4a80104001411003a407510691100c10107900403450001050f001c1004c0002d003800c070392200c004841d2151014580340c801504014061312442c2e8441815a41003a102194030385e4400d0444e42d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 54551406 1250 54550156 54550163
    0x60907050a030f0608030a020a050606010c1a04030201090b010906060207080d0e0108100b0a03050411090402030709110c0706020d080a060513020a1b06051006020312040609030c0c090218061303 85
    0x10076814020032038004c0c00042d8400c82c40381c00009400140140d01245020440d80500d003150f4140d155140115078540f012500902070310340054414008444441d8102e070458003906c00450340c00c600b51a001641e100030381c08800300070741c0c845041040503010f00440300100700c180044e00751484e60750005040c19503084502810480881c0000e484c1c46c41060011002e01154000181c1f500e103030300740c0540105000e8400751201d00101003010040d1400c009580d00c03036a4040c0207080d00074541001080504002018880d0700d54083c4034140d401e000c01c02040307008102c181d00402c154580f1241c042d14445001d0403d480e00b5080ca4010b1251741c803241032500c080c40c041880180d1340c400c2448101c540d1045040c1d4810489402d500c0d0400b448803a4000030701914881c2000c20040d565a58140d84e00e1160200d070740690000307403000a0100310b481d40400310f07581c02030802001c00805680c3d02c03400390b00349401104019501040700c2c0303258440c03004855a84001560792034034002111104030307400701c031620004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 54552656 1250 54551406 54551411
    0x1180c0311030f18030309070911072a05120304090e030304120507020109031b030c1502060a0e16080303041203050903190504080a03030e011107080d020307020c090405010b09060907050a03 83
    0x72140c0c0e5a0130074800d0b004900d0002e983d12400e022403d40d4460503c1c1c412180d41d241001415610825084212500c2c039906c560b0854009080116003c1040039005442c9140380c455400001e49468a00c241c1003110019006190781303904265041003151800300c6101550b078030038030410000460280c42240c419002e410030503182c00c0c0f580300482e002d4400713410081000e0307449004611680c0031200c0703080030350380f20321141801503484165150500c2041c00e408001039001d8030118503800803507400340c1c1e040b0990b00207444809101010035962000c2d15440076035039610000800044c0f05401030750050084c280c1c03030180143d00300700121a50b01d000c2e0240343c001c4d4a075040e18054880c0d001d0001c40780180840c0301030f5a000505810003038010441c5076000841c5509001040409604500448000701d034003018081c204010760420303e000b90801014013095101e21070303400c3c04540d503407085203100b0b6108d0320000c6428106602480400c202c007801c031502034112802401846a0021700f685c03517203000751400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 54553906 1250 54552656 54552661
    0x19080d02071b0909050f010c0210051f06020a150c0c030503070c061802030f010b0a061d041802040c03050115180506071b080d09060c02041401180c0311030f 69
    0x22562030410404294030180110004808910340c20041444d401041980c03404a461135135603081e0740c0c03c0d02c00b000c0141c05c10505070812150740d5100c1e036000f115803208200c4240003940307911003228180d04100c1c0583d001071481c00422448603000c200003440050188101121000040c017218101040241030000c0400005c030039621411003164566001702c414014114a8440c0c42d142c40b10601003039000e40500c00301c80703107e06014014014402c4001e0200580d40d442e002040351030160045201070706900e1145a580956a2400348880743c12042e2045030614210b4410081111315801c6a1420b1508140c010010307440c026030075040c65449400d100303079103800030b8030400031800b85a045103902c480d000c18041e09004100c018030001106140301040d6194541000795690f1010390031110015101540c140f0017584514141440c46101074008034075031000d40b13080144580245c00c02c0c02c094600800380080d145040c0564941ca40840c10100f0034a140b0121260707007032000811160050005201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 54555156 1250 54553906 54553913
    0x5040207021f05091002010b090f0403090e07031523011202040b03040f031106090309040c030e1020040e040f02120d0e01020c0a05010c0b07020c0315060319080d0207 73
    0x5a0900e620b090302c42c0e1404141c0321150250072a0080c0402038090380d80c5d51072840c165401441010145c0d18010140b403099900c0321440c000124009000300c040110700c0d00005003c0c2c4e03e0380b1400d406840d40e914007240004608103148254a5940d110076460320b1404004462003000e030200c1e40e149031080c0f0300a1241d076a1002010064443e6601c9990b48000000403c42440303402c0210440103031003a5600c8461001c44281c49640e07403002e45041000c0c0e001005000404c1c942a800400c2c2c015117030801085200100210728144991140940d0701c1c1a01d400fa000c15484040e102c1c1000c0c282c4404000e0f0403e410010389003000c00d00244001c000c02c079181c0d07280040d581c51000d0a6142003d0300212407905041d84401042801c241c1d2005025108450848c01c0c145483c5400f50280c0c0d01c180d46601c500d610341e44401198480c0a0424010340c054500014501c2d10140004050040c108002000c6410100e0a043c40e00040c44981e04c90900004460000221940d04940444488500150316103d1a04 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 54556406 1250 54555156 54555169
    0x30e0d03020f1009021201090c0e0402040902090f10060f0f0309080f03010609030b070314040308040c320d03020d120204091401090b030607080a110415020105010e010b0903070504020702 82
    0x40d5051110320840300754030160f01054010b00d010324401d0768842004400e40d00c4d15402e8030008800184000c0d07103800c0a0040036100310945034058001800403d030109250041081d0250640d01d2511074440c1d1020446560b00400040006090300c0c070748551420341c000c0c0010314102c2503142013000c260710dc01c02c000c24044500e085d2001c949901201c00d03520b5035a5400607103000c5c05844100c1e6402204000554803a0186c400c00c2d094054040418040350303141c0e0340486103440001c02c01c50300d40c0040400803c0410b447c0300b1a20300302040fa012118542c103d5803204070400d480120551052040001e80740000340e001c94990052106070820b20723584896190104060f0007140c100a41d00c0d0701e0b04103540200c1c0c0d0b0f5911102c2c1215041038041024044910a26441b1102260790f500880c0317485000ca007817061154041c150046280b6030150816444411480c0c0d220031003034040005130b45880042c00741060014100340105030352801540b508488401080c0c0b40c815500c00c00d807256a01150300810b64983c403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 54557656 1250 54556406 54556423
    0x9032607030f1b17160615050109090903020303040303050c1b0606011b0c0605030c040e04080d0606051608030a0f0908070309080a050a030e0a0302040e0a06050a09080304020f120303070806011407030e0d0302 91
    0x100300380103d0b04036440340490f403111442130a0008982b4180001c2900192144060701a0140e0140d0326660b40c1c1e403026809460007410003503841c0e404000642e00304400d04401c601702100c2d42d004d0941424000001000f510f014001300d58a0011040c641000a80c1a1807510886032075003000c075100d940c2c090034400c082c01980d1020400402d280c0800042111000c000c000340382c0003072810804542caa4404440c20b01501100172a00460189180040754110010b0751780100a40000b0510b85401c0c501d600540d00051021038541101007080420940c100c2c04460142612000802f4000d00c9500c9075075861f03100701006014840102d80000082e1600c0e540c0e04060354015105007c6500c465803c01d50350800042c003540c1c158540400b048004205004406035a074000f6122401e5071210740800004e0b0325010001030b84110b034910590b03900c02041c8007440c800c4546072241c0203d494940e001400b60a00030200889035081040000002a00120859181c010981388a40345c480c5902c0c0076032421103031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 54558906 1250 54557656 54557663
    0x601030b090a170904050c030105130f02131706010803091f090312080a0f0203071d0a0302150309010b09060a090507020708010e070f0803040609032607030f1b1716 72
    0xe04050f8101402450001d0842c2d030000d860401150340c4607100c2e4401c6000078040c5941c01480680800401e4403581c0005401c490320100043c9454502c0e00184030302005c0d40d11030802c1500850340070080e42c002b400b001e801042c03d01c02452a1166410025085455902d09841c0280180403910380d043e100700d01d8030015541c4150701d2a0090108500940041021120300d011a400d200341c0c0382c180c080074020b50340591016182e060021009080b6403030101c1c2414a990b420804428001000d40c0c0c07045c0c034888030212220301481e5207007418001d8900b550038108020b8040d070315910910106884000c0031f00101c4101080008094503040390490400c5410b60084401d5070820003080c00703c2c80e001c42c034102142e8043d0b40204500303903140001c81d141c2c012031243c0004a41c480704108046901c01224442202110044800c00d0f60101405c424a800524054000420000070201c0694208806803084011075140c02c0b8607407500d80d0743c079643c0904034081e0b61841001007000007110341c60b40d03003043e5950f52 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 54560156 1250 54558906 54558923
    0x7060204030501020f120702010903080c07170304060212090105071d010c05010c080105030706080105030312070521070314190c050c0712030e0a080705150c060a060f08010606020601030b090a 84
    0x10000621186600100d11408480310540085001f0500501c103041c0c020798541c860712303499a21850a4849c9400404041e80d01c3c040841a880010107001c004503c2503104540c0162541c0c801c030110320b1002c05c001c00314041c0340c0c17500c014081e4040d001a50400741780c9040c41c01490310064900101c803404008035006041c1e40c24051080386440c0c01011040c180c580a8044445c060354070441215540000c0c882d06406800c04c001c010001000c1c604c40d16070124440c107100e403800b2070000040780010200551250f400302c460b03051042003681405854402d101c14030f07041c4240d041c882481c01800c01c071811124101540c3c1d134032001000d40500d003540d158500c0d80d4240c803906980d45203000442c408408046001440008174050702d803504490301d1040d29091001407003814181014131080100700c45840d0083ca00500c44040e1300201004202e108100d00d21000c100140340108809241c600398100107030507410a201030000030b6000541a0441f038002c81c1c444801c0e190001c15605042180101600050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 54561406 1250 54560156 54560167
    0x31a091603061802040f05060f03010603080306060a0c020d0f05010b0402030c120603070f03050609060a110a1107030210030e07060e2202071a01060e0901140603041a070201091718060706020403050102 88
    0x140d00b94000f48c8580c00644180404c203c41304101405c99942e400300502d1a101400810b01604244c40601244180d5040c00e8048001503000582e1000f100349044854028070000c000801100f0b001e002c40c04542a03c06506500307000c00c03a690580220303042c058001090360000398146e80d042042e5402800041040c8000310707101d00f050b548405044500072694403880020030007084562103008514010301212a0418204840440303280350402100d0b0381d24464030001101594070a01202c0b60307600e0319100014500c215400490510600f80d000400f4090740c03130200c64560301e44046001c11000400da9060300d000c46400404000c2c0150f40001e4405007100750160010f110000c1d0003030681d80389841d00309541440004000c0701103024000c05400034140c2c0c41b50602802c0000c05150040d11603415401000c510141c01202d0032411030307071000141e4551030b07003e080c8280707a400b8102410600010b44d1130110040c41d6001505400305081d07000300400500c0d802406855419200990340c0400255980c0c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 54562656 1250 54561406 54561431
    0x330f0c070c091b0206090a0c0302150d0213080f060f0711010e011b02070902040803070b07020f0a050d11030c06151311030f01120c031506050a031a09160306180204 72
    0x143c014180e8058480c080201c0c424807400182c450b0039a030312485115100b070440d4244000d0880994407228409400d102c202154405800500070b25903078807900c041300b9450802e610740b61120110000a6a82000c0c081c011600c080c2c05403540d00400314107005041c3d41522080380c0c010102d414542c03146501e802c0503003881c91030b59040700c4003011580c1d0854090301d8507a02120101c1c403880c0700c1c0070210f52007081072000140c3c044080035881031550042c0c07440104c060300756906103005114101d46503042807140198468005200c11844142880158240f40a5040407591024041d0104200c1c05218a00f0302c480d40c1c819080381120304d140c00c024070006440c0118202e15810035190420b44e0360f44a4004240c0d103007001a6008055003183d40c1159103803641d00c1c1c0c40412049a018001c50946a0304040340a8503440b03ca000218030071203601208a001c0d50f588206031102400c0502c07103802c024040600302180c2c2c1201d8090b2030300180005050b800461050384820613242c1c00030340141c00c000404820 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 54563906 1250 54562656 54562691
    0x903020d06020c0105010b0c0d0806040207060f050f070507110910120b150d08090904020423090d02060609010626090307020102070608070f030905010905330f0c070c09 74
    0x5030400c0c100280300e07990301d4090601c00c50207403804c038282c01e90107120002c0e03119105074a92b03a0418000f0348018681011500c8034810b0320165010140c80903203a0041c044203d0000101951003016172400318240300c116aa0b810b5841c00c1c40e0300c29407103481c1001c00305040c401041c24100c000c05c161004150300c482a8540031103c808115101c1c2c0c014419540314518905040c005184c010390301158051808102d85d00700141204050404d0780c1040c1d542561070501c4801c107084d038921144501e68014280307020918145010006208002150080401c1c07000035203e0300803e0781034a10030709203103550400d031683c03054031402c0d10781c07500001c40015801c0c804104008001000164000e03800c0e280c00c075031070300006c0e0ba010000303a80301c4000075042c544455215219600c801d00442c802c03400496443e44948032070b03180c29a424040d545801030030199031304c103040104810804840201995a403490301642c201c01c1c580d0000c020301010140011905c042040c0c68050304003601c800b0f82e0410151030ba10405682 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 54565156 1250 54563906 54563917
    0x213080d021b0102150703021b160302030c15040605030405030f071211010e030a1b050609010c1107062a231e07090e070801020d02030f01141f0903020d0602 69
    0x200010100c40281c82c951010a4040c01290648903201c4a0344807010110000e601243c054000c0c1103082c00c88100d08007051002541c0000003c048000d4a4214010542007291140d0920b02c00e0001c4a0b0342c1c59034180203000c0d10116185810526100e59550800e03904512803100b41e4070115100107401400c118000359081d100c2c45080d621541400d0002048608840c1c012a04003460b0307009002544150788280c800310910100d11081400c028120b55401d880e024040d0b55100290b5100d40c20829078039488042501d504203600010202c0514090024144c40d50341c3d202a440810b85010200780141e15404048085900c48105020b80c030302d03502440075000c0045108040741c024540342280e03107130203100105090102e843c090030a03546012040401071004c61030b038000500804500117113108081c400341600c182001c0b800341c1d4900d000084158184070581080c008500c80318144015030302c0d005c0a261449103032021044d841000070205030b03500c00065000030f505c904010081e0007000300300d802614 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 54566406 1250 54565156 54565183
    0x3240a09111201120201120b010903050114010e0603120307030518100c020c0a140f04110307050405030709051303030b0402190c05100c0c0602030411041109010f210213080d02 77
    0x2042d90342c0350000a2a070050f2404040e00040c003020413403801402d958086c0048000c14105150042d5480c1e903150f0a484441d40c0307940007188817400401542c456240801d034040c800328007900c00000002202030650101508100405544100180c00c1040d01800b0150440c000b00444d02d1124405c1e83c0200544154107805006000340c05901c140380c10802007400a507007181300542c603150030344400c3c8504090b014403002c1d40103489100038885024600c00440c00b46d142d640c2d585503114241405c5c9032400c01550310203440a4601b504204121501d421b502c150f859152502084502560340060007030b0040d028141480b04069554401c01a04940d03202e40c0140300c0c0c01541c3c2c08800c1103d04034200d801402c18000032401c541c003002c00080565008585c018412603901044114840109088980380d04030710040e400300040c100300545e013100390f40041c248240b4102da05c842c0c41c81c02110f2100c14402c24a1405500170402c507100c0322018110201408880041303401c60610b80000a542d03440f044040c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 54567656 1250 54566406 54566437
    0x23070c0e010b040e0a0b0406060215061005090f0f04020f0a1407020a030308040318140415240e0603040602040f14090705070302011d06160503240a0911 67
    0x4034909121100340c102c0e10310b0440942494582081c1d04441e960003011400d940340e440000a000b942c4900c6080003808095005200401c1c007010240d859034005012180709030024640d1010841e0f0220840c0e003031180a0700d000791800c01c17050100340186540b0389003ea024ac00840c0c1544080f00c0d48d800740644410540d5903001400d070341c107072041081c0700310603010f5041800c0d0202030000c40d014441c01a0058424900540b024051217203244a006003600110301810150065415034a000e0040070b403000403000d5400c2c00d003442c00555108581c5031411643d04407940401c000030707450003104802c412200c00703841307a5900c1c88c0614004000350f125000c5c01188a011803400b07d0395995031402190807041c090300185050303e404009440303980103c1000c40c110343d03c41c906032034000b24881d80822505150f10080699003800c000100e01880e03000f40d0b0a01b0000c00313004003d4443c0364000c800c141104078002410700d030329400004c00d242c018981c020000085c00d120094010503010801843d0300200b04112 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 54568906 1250 54567656 54567659
    0xd0f0b090709060302100e12060a0c0e0f010c03120f02040803040302041119120b13050402010e03010e120304050312090307050d09030308040204052203020c030105010605040e0103080a23070c 84
    0xd6411100d050202a4014070b15051ba48101c500134041e840c5030740d000a0012605801c070306440c0d40340600031030b400302c2001c1d00c1d11500c42019401c00b0102d1541310085075141e90a210240009003c0350300a1009000c2250070071502c2004072103540700981c00c00d00581c2c00e40d1303a90340700c80040707549600a11040b07001341c1c6048100c05005c854007059419030811841e410803440c8555504441c80003020301ca0642031980c9151010706550b0380d501c0784100119410b0040707942d10307040c00054410481082018040d9042c003c0e1400354840201e1018490381503480407940720b4031380d030178542d1960042c2040b03401c1143d280b01c14002500030000141510611031701c200c6d10300c4500345904960721803151100601107004580070400514050300141c0d489100301d43c04410016510000f01003205800a0581c0503030071620354005a400e0a000f113a003d1305c441d0910f170b1300e0319140c801e51000c940014400606001804030300d40c000d6a00c038400f02c0c1304030f000b4000a9240c801c0c0006031051030f41d0145404031250002c0307610 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 54570156 1250 54568906 54568919
    0x501050304080d0507050909040605041a090d050c010e060f010f080d0504050409030c1e020909060c09060307020c150c010c0201110d02090604170a020901080109020f010e0d0f0b0907 80
    0x1101e10499106801c9403c1501e4040001c000c0c08001e040380c410b1040030b200e000110f0711240a46c41c8501d014440202e01414039040003140035035001c46001c5082c9a2004001071004001100c13801c1c07541178900183c0e1891100300e404e00503c1f444182110f01d008003414019200d941d04541c50586c2d0003002191b05055031008172a90300c0420306000400326406000820042c41d1562140a100c1c0c0203080007058850195a410fa880c0240b00d81e002c002082d42e11508258100f040c010703a4418202c0c402040f490803d25120582401800b550300d218100010004075460f00c203001c402001c00014103074801000040c800080190800c1c00d02d003906600c1e0030040e51a0030301c1401014803080100059a00c1d1500002c1100d000e94031060055400120821002800038042c6503c200341c510401d003e000c0200c0340748100a5542d00607807240140c0ea050411281c00b517604c0d0b9072641d0b0001c1003400d1542d80e1030715000205502210040c00649075081d1060303220140808140c0c40b5210f4078401e01919841616010b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 54571406 1250 54570156 54570167
    0x40209070903200409050708030a09050a4502181e04020a0306050306090102090301060608240a03050a2001170a050604020403050f0c1914010c0314130f0501 69
    0x480602a0308007610543e030788000c02020035181d014040c1c0003191050042d01c41c14604005a44200d040b9880060043c2c403075070344440400080c2c20126015807020749804c1c1ea41003034910000944902c040c8000000c01c4682241a1510340022201c4410001c6403401c031200c002500709903043c10100c0c44200c800322151810400b201c01c08004091125200a008002d01000b074200c0000c40040c50b980f10310102c2e045c0d03402c0202c40e1080b4040000540d660b4034400906d403d444c8179130b1110040c024070000b400848800030410002500d038801c1e12400c0100030310002880c07217007141d20140c490702403036520b01d00348003440303003000c01c1458407600c0025100c0c2c030741c001100c0184400d200715495400344000304400940b1600701a401c500c0051015003001e032a40ca80600785490280032130300d80d41c00540e000c401ea041420071406d01990b00040281d03401e14181300e152100c013a0080e5581000040c2070ba003410140150a403100000c1c100001584a4109401c50113480b000f600820005103d001c2000134550701c81c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 54572656 1250 54571406 54571409
    0xc0b060d05060a0507230712050f0d11090603010603020d060803041202040b12061f09061a03040302010f0e03040501030e03180d030e030a0c0513060b0405010e0604090c080402090709 80
    0x7200a040d00e5581c21540c200601001c3d00c2d080030450110150000c0a0030342d18105007400030301007440d9a443c8a0318202118654126444017804401e1100c80960790800080e5071028000600c0800c0c007060480118015101b214401ca90158010002240c41c643c5a4007030a1340c50b5103090300300402601d800d021580e0f0b000d188650b90241100d82c0e00c1e0380c014206030b005044a0580549010740c00141c0f100300608203c8222451554070034201c041520411401c8840300007094020410404a414010040381e024042c141100305048000013107010140300754800d1070000100b000810200940303d102c6500e80d4801d20600c0d000900304a80240d002001008641564440d0700c8800c0c540d140a81c140403411541501c261700f032140200c01d0036401e4038140400e038170542c41128030f0302c074460800b01003100c00500083d050311101c5c50070a0a2040d100d80b10704403030a903602404c240740c04c1c103041c6001a00d54800d0342c105a1017503040031440c0010350380208455004501c222080425982c1e403290848400209 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 54573906 1250 54572656 54572663
    0xd0903060e150604020f040b03070503041e0512030c090406091d01110912030d020309011d2e0603060f050912130e0601051207020f0f0f0709020f190c0b060d 69
    0x4000407403e40e2134150300412407200c030180030b18241540c0e175407101140c0d00121566000704000100300700410140083c8503407503d8104420809c0c00009407100c903a1a00d5501040b0036003000000400c000701001015a14000c00040091000c151200c14400c05042407000140800d00d0010342c0540c003c1c010f000c0c1c206600807107103609050078810b82c2040701200000ca2802c250b8007040008515018150004500c504c038080004640c0344205001c0012104c043c2c0b00c00c0309242c21800da80c00c2d0180d400b2161005281101c000d00403950305c230b15068001000d0a42c40184100d00d0042040f2901000360011842a01c4c05819a0280c45440502104a1240f001050110301c2485c07000d01a080008a40d10307003290b0117141c0b05007014030002d03404610071401c0d03840da405a8800f021040f000716041001c0250248003c0141070320043c0200e10960314016070143c803404507004541001d002c0c02000079108076034001c4800120140c40042d003d0502ca4a0140035219140340f200010010b040980a05c2643c50b030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 54575156 1250 54573906 54573943
    0x2011109060f0711060406090317040e070822050105010f0e0105060708070f1403090a15090306050411030d0f1803020f010c0204090b0a0b0102100605030616110d0903060e 75
    0x110a104401e58490071045841410300940e000103900c0d070001902c087e0003e5101c2c103011030304606101030788403aa00c4012503514020041070022104111082e80c03c016039060613001c80d184e4080d0b010f00024103424198101000140c3c0b5000e000c01500114100c42440c04990211525100c610b40c0540c403d01078144c1050007040303244000380450000340320301c0d4018000400070104075900c10b000191450510307682c552011906c0121450054103983c000d0030100901d031024a170b0408064894001e0b0301c000303044142ea660000d014004400200210b0b080000d0a441c5103076210480605502c0412000c0390006021185d8803c0701044240c6e08026250014003007c00b048c0b0200c011994111842422a0403644a072640300002e021144603501070a880c00b40824035031183c0c400249007000c0c2d8041c1a04446c00c0110401c8141c030003182558002c800050400d000c0803020348150384801440001102c24854821010481176024031607000340c2e07106000a000920010781340ea42c0d80e00181007107055504 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 54576406 1250 54575156 54575167
    0xb0a0b06270a0b03041202070503070f0303020f010b0f1201020706020a0507030906080402010c06050a02090a0801050702010b0a1d07110d031508030a271706071812020402030c040905070f0201110906 87
    0x2000034900d490b4041c0306c1c1c4122501240c442001c203003803112543c4000150900e115050007003540510080b0b07000c581c544003c11a43e60088001500d01c6d48071000c0c00e009050389000d5504480b003c3d011900241d0304440103655400e91440002c2c10369200c005c042e00020706040c00810018420300c1c60500480e0141d52b002400603180c1c803000010880603005a001960800c0804201c2d182d5151040007403070702c41c000007a1454490000313400e40d040c1c107400710710030049000180884140348100098030422110300420300d544150302a0740000703003d00700040c035205903540e00001603030640110001d840c8010000038166551200143d032030150f10710700c1c4003151101c444035800c0441001ea82e8120592006407200040c1c0c2c507445202a40c0482030760765050b402c0701040040c000c0d00103941203101044020a02c4410340b61819030b20402c2c01e0003078024403443e00000400e210078050700594000d031030b8864040007541032640d40038000902401a480255003841c40c00e80e0001d032186d007980c2401d80007030841458070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 54577656 1250 54576406 54576413
    0x1b0405090d1215181d010b0307090c0516110109050117070c02060d09051c02120a03090318080105040b0a0209010914041b050a0201060503010203060d0b0a0b06270a0b0304 75
    0x1000703041d941920a0f041c0e0480020b00c50034600e42c240000000c4440050307807002c1c2c10390900341110000f40719041a810100020715640f0000742000440c0c06481d400608004092821503c1d44603a40890340010f43c00706882c2c05003c030a490b039501204098a9984589903207000541d0340319402100b17241361400c103800143c5c866004043d45069548001d00c0e01d441d10448030041012038030144000c1c1d03401d5000e081c0071003240341e82454002c00c1d1181400207001072140c40c0c88480c040c3c800c445245003050340f100e03092810075005800f00a600038041007000c4415407a03140560003000c08803002d40300d4200c8640401e0818280d80700300e40140106a4650311a02d003440b403861511100810540c1d040361f40c580d1003005030320060f1004403404005544450341c48099260080c29261645c01403403280e44108140003842d031302c4119510600e82e102d40701409942d03840d45140020700000752030030b8000e200014000c6042d14040c8940d14000c280002098180c10310030300340841c0620324064805060410030115011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 54578906 1250 54577656 54577661
    0xb13050103050112080a0e0306070504140d05060103080d02130b0703120b03030415110706021c1d0d050a0b0a05010504140105030601090905070314030406170601020706110106081b0405090d12 84
    0x850303402c5d0400ca1301007500d41f80031914101e8111220b0002803404682400a074074140286e0b00495422150610a040c00c0d4440c00e88945061000070000000000c03000551141d0b42c05549114210b540480e0001d41c1d5201b0320a074603440114201e0000340401411220007007039100340708503250b000e8001c60500341440b080380d103407144508200c0b0500400c5d8410049030b4204004000103421590b000e041c40c0a1040e40d00c2c20700e1080000c0f2002071080a020500d0000c80d221001c407040c1d90100c4004e02c00d0710740385c02d20754103040003000054030003a80c0308200480650690005412200140e03010401412030019031a6200703000e003e2294036070003407001003080001d10f4008089403805001590131195803a134a2080340070420520300c1b01c50304003140c1003040d550080c0c0308410745103040c0c19040141c900078000075200d1155000e1034043c0940f40303581d070350001d4095219801610b0210100d50106e203242e41003400405130f241c140c134841e034100400100b220740d0114020b00c5c0102e01e03854486a41140e80c450a01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 54580156 1250 54578906 54578917
    0x62106030312090102040f0806220201140705070503120a02061506040b0703090918020d030f030e150103050d050702030a080306041103070c06060807060507030809070b040b1305010305011208 84
    0x50510080c0031900c0702e034034800744003405074260500042e5030b01d103000d421070007a1555620402081c1c00410412000d40c0c851070150705000b0709428100300c11141480140c642e82c0c00025008403006001c90b0440412800040c00826100214116000e10044007401c01e030034440c0c42141d8005030030010214005001401085040740401448142819150110b040f4140c201000603000980301203c104640f88051240c10100030030ba481406002d0029004103181b908240001810030101036000500c1510a41c01003540e40300c21020303195211020041c0700c040c0d040a0005850700e026510030b24110501600c01c8070b50396640580601039140803500c84101a820040c0116005030700c40c06a142c1c171441c500c005500c20940307074481c00b05035550350401104554180d00600080d0f405040305101d910b4210080c1c40c441e0b0b0741442c142c4450790b210320b003450400c07641e944143d510707000202e00801d811031038401a000f0203401d5507220a200341e40b8401141619428401e109000c8e102134003581c04102c40070010b10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 54581406 1250 54580156 54580159
    0x1b0d1409030c0d0f110604030c21140f0c03070303080f040312230906090c0d0203010b09100e070503012402010b0a0f17010203090c1215090a06050105062106 69
    0x1280084240041410701d00003c07800c880c0048640c44410800850220281c9400000e41e0550b003000c1c19541d61031103201860142c40030701c68500c207507001080d41108016242d2079201f503c0300c13404400403103110f5940c40d2860003501c4501807400944020b0a0008400701100d030180d95071b18041c1c4070b02000c180340702c40140098041044401c800d1031000303014015074440400300000005a82d0403400038548001020304600d080ba0020021301054050006980c445243c08844101c441003003840040c0c010180084402d40142503007003040112491401da8104070f45081d80000313010396544008071958402409000c020003812030003071419607100e40460300440580d00000500c0c9031408000b80000c51540d100890003031a0080a00001c41048032000d100c01912000358214180040001d445500d9031410900031241a0058100d0071810448a04019041040c600702424042080c0d41c40d60241d00c419034070300b03060500000703031402e10700120f5001d6660118004410104000d08060b2800041c0259 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 54582656 1250 54581406 54581413
    0x3030706020711090a02070c05060a090f0902030109050606030906010311060706021803160506070b130c06030209010810060203090d050309060406020307120c0201050f070204090b0c1b0d140903 85
    0x44001032600c1c401800854042c0c1d0350b24009060320010000c0c0424020081c00c03a19005000742c100080312142490195a0b003100c032151501c500c1e02c0200c6480d0340513880000054000000001d00105a60080d0305880380b49006100580c2e641043c0320107840309a42c00d903101c0d40241c0041000c038000355149100e40360000c000310700d8400981c59070350030b0340c10010000340c00000500c00c912851034200200301840501c2155115283d02c9c1000160fa21700901001400030f200c6c1c000002c141c071200d01044c10007540c0c8403c0c0d803904e1a4aa0300010b0007504004011404030f051000411401d0002503292004c444142e4000d61405042d4000d10101c42007401041710742d807109000700c803c155984409040500510340c001c5850342c1c0a41402c0c0752245169100d038060101c2001200c0142c0d80c80320860b40640c4034a070b4907175030350141440881c005040310704026001074281c4e828015084400720081c0700c0384010b0354614001c0c2c006012403540b5004503590302c0020500968101e1000b0300d22a0242c080d032003009064 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 54583906 1250 54582656 54582667
    0x503060a0b04230f0601031a0f04060504020c0304030c050f06040915080f210c03030601110f010207030305010311030c030319021c0306080708160504180f06020c10090f030305060303 80
    0x180c12035070f100f0181960307190540100304409070003a02c02c0d940600f09290034445031000103009003802510750700690041d0700f030004003c420345880d080500182000760085540c0e200c1c14030050b460b50401d0100b00c0d03800c044440001441d2034132028003a001ca40050070545018940a0440c00810914024240d0045420350001e040f00007808000c54400914000d810380d01030000010005420000c0b100343c20380018010481882d074000280c030380c030200030300301041d90882580d840c0f840e00c2107080d00c00c2e0056000140d00d10400d82d140d0082c40c1220711408481030801490410151035420420001782c050b44140240ca680e07483c00b00903040382541c1401525843d2400c035003148041c43c0b03030b400050003180d142c0300d0401c0b50780c808206c00e0b0010300c8680042c2c041c480c050080143c90803840e1003002e12454855131412404003030f0a0703140017025031003140c01a10f103001c0e113441006500221038480c1d580c01074152401c810880c90084c143d80a038030604603204079005980590050501800481e01361000b03101 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 54585156 1250 54583906 54583931
    0x303050319090b010608160801030b01030f050a0c1203110a031d0f04020d0b0319030806040c03020c030703020a03080603070302090c03070c0812060405072f10020f0408060a060503060a0b04 83
    0x40f80380a400f56030b5a0459501e007069402d6071034029948040200a00440100701180c09406420305496104004140800480c103281e441c09070304a40160900c5e49401002403038451803007009107141e1203070700d908581d4841800500d8640d580844081c2c0400c0d680e44c601d0005a0914800140350000240340109003e414004102281c201181020340c49a0b520440040d602c0c0c204072000c00d0074065158070390103034016a001020b4510241a1902590310380600f141005d000e9010744501c000c00c04201c0782c44a105042c000d50b9101d000205502203468071001c10800c2c140440d8002c103494000e020303202d480d2906034900b01d45500003007010042007890041c0790001000c00d001440c0c10482450f42501500f050741c20041102c1c0301601950a000440c55085651500111807400801c480c82d4002c140440e503d03500e60030201c215006410140c800110005e040400d1405081555213443c1245d20960b070300c00405040720b500c0d000d0b10398035a01940000d0300b0310100e82c000102c4440040d00105d0710020039034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 54586406 1250 54585156 54585173
    0x30d0906060e06040203040c0b07063209030a0207030318030b1003170316030b0a0e010b1206040e0a0b070903080f0406020d0305071b02010c08040e01050a0906030305031909 76
    0x40100e0306941c031903404020a429003200d06030003200072103003185035081c035030340e82c05084080744194070550303401103000c00910985903c484000720400b0b840d00307810240384840c0039000c00c0312420f441181d194540411000030001042d41d01448041d00200010342c00c1d0b88041c1c41c40a410102420f449520410110000780300e11207003130140d40540b9034102001d05510b01011410000082e018a4000900800c0818070024a000101412600700010180d000901080b100e51850f0841c0c0d0044507002c3c0001030146941c401418040000ca1180a90f911400100001d440443e16200141c0d4060070208000c034812030800ca410803054203107080320581e030342d0303403007000d0740002644d1810340030041010841c2540505c0000000500c510f020480342c82c1aa03409002400708040c00089440791b6100034046900071543c40403069004000d03546c640740d4a074072000340310030240111402040052000110781c883c0e80100d0301540c0d81074503114110b42d140345030034103079145840510381590381710003070b56000c50240e2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 54587656 1250 54586406 54586421
    0x70206070c0f2607170c0904030e03010c02120702060c030c010f0c03060e0601090e06010e030a0f02010e0102030c0a080904090204020a0c06151d0603030c031204050706050315040e030d 81
    0x2041480103150543d081040f401c0007080034030f00c491414002c030700100d02242d010180d4005006221001d01d502041a241820040039140c0100c0b0030360601062582107202c1004404046009110400c80c0003004c980714041d0901040300b107002840014010b1034a5000707060030510180403a0300300800c241509081d92088504e0840e2596140456444e4a03031601801c00074101c07a040c1c1c007526040c0034000800114241c8240e80e00d80c214080400d440d81e04c00e014440d422100107003105c02c44042c03402e044400c6002a04102d000c11f45210b484d024550010082d5041804000301800c03070308466440b54451a4404d00405500c40d5860201000503515440685421925680d0300486080b4a15021088901e000d07504921590103200402800400000e00c0788140e2a80022030915114100880c3c69030040c6820a08540408070740305820300b0824100510031406401202c40740f40d5540700640302c5102c1950101000d5999a450301400e09041e0840301d8854100801c07640b070b004020103180100c80c2c4c2e0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 54588906 1250 54587656 54587669
    0x60f120f010f1401020a030e060405040c0509030d080402090f070c080d0507030e070b040b0f07020d12020d030207110108040c0e01060504060315050f2403010f031e0314070206070c 79
    0x80030051246102c0701000e00c0250900454034038407407403140000f1350fa40b5040300000f41004a0380095041503105d11058070000e20000d841849000010540a85250055402c0300c1c003c0c41210003a00f1300340d128800e654050fa0b0054400860350300c80c03254989111000403e04401d101c4c0b0102100000b0710324000500b802c8c584140700007102d041051005081d9154038900d202540e010b44000d000f05a001c5040340e00321120b0468403039440040709078401c2e01e805003031006980900011004c10a00440d10240521980b2075170039a02120601041a4124042d46001800b03d2081010b1030020754040d609454100d070185144024480e6980141104640241c01420000e0800329007085802e03010300801045160080340d80c40c40781c0c02c0401050880c40a0a0440d12400d43d101c016884406505650803070700e11080180c540e00e60b142ca600064400302c622003122a107070005003202c0f0030700d000035070101e4907503044d51100e445010f8002c5500035034102100c180d038000010010000080e44404030140100780 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 54590156 1250 54588906 54588931
    0x130e040b1501020f0601260303070203040302030f06150d03020c030f0d0201180b0403080c1306080106080c090f040b060d090b06030d050703020d05032223010c090302060f12 76
    0x4041c4040c524030300c00e641a542c195444508500000c0002141c0141034a5809054005102c03116421016a0210f0111030b00e10380000418410050b60100051050701c0c000d0b0100c545000a0100d5641e0b039407401c890204002c0c0500291051518086560070380441c020f104480d18841c50000103414180550303a174070301076402240700c00d401580a00894218055810b0a0002401152101c0b040350310010002000c000e85a00010b02c0503d10900307442c00c19090030b50800302251103000c0a03140c1da20038010b00021800e0003002540d900d400e5022103e23103850180840010240c2c1c0301c14040070b480c0649843d50b1000c0d0500c202c0d40800701d607125200300f0a00a080700102410030109250503c151000c10204000c000c1101502194000a01a43c1d655032480c10650326620710b001030550140040c58441c80c40d0b85a501c1b0300034080840c0c2c2c40140c405214800354010806203180c0d5088403c0d8164071400b04421501c200050b04c0d120f8003400403000210045490080050105ea441c1001100c420700c0c00381 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 54591406 1250 54590156 54590161
    0x90302031501031103030403030509060903120a020105040302071208090d0c09090609060b03120304030e0f040504030f0201050601050901171e090a0302010b040902010c08090d080d020406030f0209010c08130e040b 93
    0x804c00c401c0d503035840d405030069440e243c11514010130600c100d0349018002e07403000407401c0041c1c80400c143e05e506001050465117a040c44e44d0020b01074201550160014880c2000100d88036500070449108940e0001900340ba10760980d0901c0301c40d400e4980b0035904030086940c000b0b000030440c001d80a000d442030000080c07217481c5160410441d6010010580039610400300071070320100c107008aa40051b01420425848981c0d8800038082c56848212a500507040400344010903400c1f141c0381d5032a1515400a0000390341c1d44004503541d00412862500098000b03584150042c07d40350303095000068828003c0c941e07906100c0d00e0161010550b042e03020b9500507000c4106041e420301c80e101465000311401c0c411603e40e5000203003044e58016014020210019030000030f070b983c000c00d100b8029485402180c9486550000d000250058450000480c2c00e00a500e05007209500c211000800305844004200005455a109540000d40420081100c03000041003900800a0302441240320f180300310b03c2032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 54592656 1250 54591406 54591413
    0x6140a21020c031b011505090414030703050702040b090408030106180807030318090501080c011209140c0a05040e030f03070c060f020a030e0604050d050c0c1503010515030c091009030203150103 85
    0x18032a81c411320b040303a454490b4400c0640c10466161301112000c40d0749284607222030405a00114540c0c1043e8018400010a51308040e00500600401d50080301c0810803030002500f400848030b011a4010441041080107012880c092000080381191080c41140c5094841d01850b240050503002038001c00e0b62009982c0f0041403692a8001801d1841c000340710b1545010500d031354802443d9400c60501c0042541510079160560141c505290070100e0100b2121440d203806440b811080b9215000f092820400304181c103280c050b691100c0040802585403990030403000c116908090140001c02c01703040c2800000c43c48500414414107244080141d59200e20300010f021280000c0d41651a50020420000821004551100304904904206a60300c03d0707801502c2c1042d01e001400c41c1d00008421078003004c0034086c0040c50503504140d51409003408010740c105282d000448800340e048004001c1c4c0c4030030f401d0843c04001d000b1424144501500e44950010341009142c103a2030800d140b04c80010000d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 54593906 1250 54592656 54592687
    0xe0a051e06090d0e0f0103020d1404060c021605150c03040e012408070c08041802030108100207170705070e01090e0c010810050f030703020406081606140a21020c03 72
    0x95060051a40035248038000d020130040098140c803d49250381041c4469010742c0403543d10700c0d040d035410802640c01c01088940460240c5081d2401c2785401e110000b86400061b80d20a020104100056003d01d40305c1040340c031040c00392100032090414000750b9030006c1c04001900103088071400f604a0741d81030010304010814030701e882d06500740c03c0c07042d4100c06a41281900380c001c056468010034415550526841511855104d156110743c0302d110b00c5990603a55000d181600c03104801c1d582039016121080b420782c05154005001617003080348041d9400c10700b0700207000f1a80f20701c0580705450f6441c906c2d40c2c040c02c02640130303443e19070302c40030343d4041c0e02d500740032982000d0002d0a100400c2c1c2480b80a001c0c40740c41e503001d614001c4914540701d4203d03950401c0000d008642c014018400f0549a0210079200c4042c40c031620300b01c903014507010031002d000340ca50b4241400012291420040c0c00c2c030b07080799060302621010b000c485085040690842035030000340b112450110003107039036489241d0172104 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 54595156 1250 54593906 54593911
    0xc0a0305040e0c07020907050c12040b04090b0f0f0d03020c1009080d0903110d0c030b07050a080109020412080d021603020309030f0609060406090305040f03030801030b0606030702060a0e0a051e06 86
    0x14484070801c440e0300160396411000ba00050741c0c0c41c08c0c640302e01c1d4900c015460810039101900c0c4068000c1070004002e80c1c2c000082c002da40310040c080c4114803248003480800c0381c4070044140c2c89007036400c0500c901e0074202d4064130018020b05c11100544a02008101902e0300740400f080050b410301c0d070600050030f0412400310080c103185080205280395445843c902025214060303c24003020100c0e00c10321240954003409990070451045090800c42c00141003544588203500c0403c00303a000004880d50240f003920110f0319000b40500b00e100442c0d07183e250f00e83c0312044054881e6030a01107109810070032181c50a00d28800c0c0c00656692070703000d040600e440901c030010b4a1070b50090082040b0300310085512074110750b0043e00410403030320516081d1441c0c01980c000e643c1703201001300008180f5a00601c95412240034600180503074650304240001340c8000c640c1580581d0150011607040c1f40340e0fa004400c2c0e0f15100e800d8820340c0c47c0d16510b550804841c80c0c200f036242d00208800c0c492458052203000e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 54596406 1250 54595156 54595171
    0x3110901080a05090a05031207020601050102120a05030c041d0906130302120306041d011e0e030306010e030c120604060b0907140d270302010b010201060513050901020c0a0305040e 79
    0x906249045000904048000b0710008549450b500490b035a2041080003001840d40042a65203c41c41021107640742182254010018421880001280c0d400030030441410801f101d425441c0843c031000503a03699001034201c01c7d08982c108000659900c441408021440c001200801c4509080c81002d160003005444090020340d041d401600203900001c0641180e02c0080c80b490716580c4034800100181000030030701d981c4030350074018580c0c2c02e0410340c400c0e882168032507070813130f80300440750307841e400320b8000a2190645601c20008907006600880c41401550401811120380d42c4844011848040481c1e440c1e44556010406020812082d4001e516101c10180e4211603d458503d200030a4030030481c00c41d50280c17000061007500050750303820200004100602c0074000c801042030700500e4690007a000ea005500e000713a030b4022988107003d5070007203038401850200c000c2450342e0100010403003d0610340e130566003000302c055040700610944814a0090b01d9243e12645040c0b02c02c00214401000701 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 54597656 1250 54596406 54596441
    0x301060501050c0705010c1103031908070201061511010b0a0f050108090a050d0f050d050c0a02060a060f0501030f02090a0b0304020901080102070308130f0c0f090b030106030206040501030e190602070303 89
    0x1c000c03c1e40050280704a84003460300c9402d114050900300c0195801d03003803803a014000000c841c1181000c00c0341d05e0a1000b080c1e51a002c2c01c0d603450b0700c00c07422600907000740d40e849501d4403240c910079442280000589210b20000280c00490031002484882141e031121350508445942003100d5a000b48071168000d0100340680500a99503941544030300c0322220140c00d0101085400741414402d80075130300c0030040ca003420043da04201207081016080352003206d005200e081e0019450f20746030300130391084820080842c214581010010341c06807403101007148126034244006c000b95070724040944024a100d0001a549041a0040c40306c0c0150503000b481d0540e00400c0808006581320640c60f5004414440c080f00700b40300b6181c4600087ca8444001d443c58034000303c00320340c4c88207011030b010480f1104101001030380c1c003800516099420501c406503102800f408104465406608a0000b9101c80801c1c0d8039410490f504012071984014000c2c8c4400340d0101e0502d0815400d132056040360400740e00c5a = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 54598906 1250 54597656 54597667
    0x6010f18020f0301060309030c08031311010e0d022119030908030c210c011d0106060306050f0420030a0902040f05041509170a0e09011403060c130b070302010506030106050105 77
    0x10b1401c2d100c10300c0703141d040564070020007040c14840d610204a040e4400e030034540e6814a10400c2e130780f09030103210607919503445c0c0070120040e601401e60b400702c0242c050312a18409140d40c0810a0780341c0c00100085040e1591070409000403801c0c0442580000642c07200b400070032071806e00801240e0660003402d07156000300020004c901c40080c08a403692000c46100403450b51a60380e005050003452000d10480d8242500d007000b52007078880c0708a0139081a0020880f1036560001142030340e070203101c2d40c0d4010070315900c100c205003015003020061090010072801460040c0f41080210383c8101c50300109036980741088011498035010318102488000c03018080760409483e003120910000c44000788981e65902c20b04100444d60f251000c811501d42d8400e0740b42c180d0341714003400c000300039015140f26034445e4001081a8541c4103d40120200160040a166590b90000382d25580b200040c00c540c3c68145e500000c92514030300c0107040075803013507001141c5402c04400f49030075250140c020b42e060203400d004 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 54600156 1250 54598906 54598927
    0x1f0e0606060c1f06090501080307021207121502070b010e040510051501120e030a0e090c040b07022404030309060807020105040201021b010c0b01172503022106010f1802 74
    0xf410040e94015200c07a01854449210f08001014242d018085403801c6c50300009642c58003001506800c0d00a0758080e0036507a028200c2c40d1030702d02c80e0240c000602c0300001c69202103a1a4143d00c1340600442c0b90040c40c0c100c41c4c0e111264502c0d8240e02c01800e80ca032103000c0004000050002c50341d0450001c02c03c0c415418480448282160f42032043d6040000c6c10100c0c0100c041c00780c1121008140d40b009580d55110140802018040c010044600541c0007600bc1a600002c8034101c41c12115a07800c9541459482da082044030945114075540b0394801079080d80c10700340c0a100800c015481782d1a2251031518011000e045004020030000075a4502010040540d801180000042000301c1b440003001040e0001030f101004d4010300a4644101070002149051400340e0055108000d44100e95013a43da030741444130064020851076024402c0020104014101448038410961819124100701c1a03080c3d4030501c0c0c000241e01208165a410104102d00142401c1c50000541607600544c94908201d9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 54601406 1250 54600156 54600163
    0x2030d080106021b190e100501021b010513030507150f02210307030f061e0e1b07020d0f1b12030503040b0601140703020102040302040f090f03030c021f0e0606060c 72
    0x14541c400b14130b00410100096512224020510390360007900179403054035880350740600c5200719130034403100442c910089460360000481000e10000c10030030b54860020340004459540117400114070001c00050040001001440b5070000340c4010b0703a000300303204081c0c000200b01808100d1240155040f01503500e886400c1c28801d83c104981a141e05503581d21034000c118005d1880300c0700b500c9007525251020858082104035450009a0b49222070a0a030310b41c090200c9114055a0710043c0003101c2d20141590074045015008035400107000b901107501545904c46150421141101c0a01a6449400b1135020241d240c0c0f025080441d00180c07158095034020b0400d210190016003c0c051103000600107038416a0410707030362061404000c2d100e000c640340284c040e4106000481c070aa0420440e8145d4020500c6408180b9400c0100c0c089007499a0b1419402495032a800c18118080d540007110484201009031010079440705e00050b01415030b440040c1090f0001d010039104080c2009030444004000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 54602656 1250 54601406 54601423
    0xb040e03090904140a0b01031704080601180204150503061906020c0105070f2108090d090902071104050115080a090201020706140c100b040c0c0b0109110405060309010902030d08010602 81
    0x2502c8030081c6450340e084c8101c4498107400c14030f1992090100e824100f108600c0018100ca201e800c407003070542c0e4408800885400f842c083c440761580000c0c010400101c0d08e0104080c40d000b101e1005103000c1e20b40d00a11081d00c0082950710200f0800400d00445040c03a842d440a0106900c6c4c0070b290341e43c00c011009484086c124103290400c50080740842c180003c04040070041944091002ca41201c011820300740004411074203404510410b00140d841000031031290103040780c42c0d640c0201e540c142007130003000350800741041d25401c90720b02c50306019854a00c038681c0607045225a000c06004402d070000c103100b80c000c000c2d07070741d41d400c0c5601040144d800055034800d80c0c0d85800e003414500d20500d0408014003903101031881c0352003040800c460022107a801807103a400291414003000309441c9040c0c41d80d110320031000303010b0710125004001d0310079554000c0070b0801c2000741180c500360396940001c0c840d41080d070b0407a60607551001c044045140400a0611512003424904210b41c036001c40a92240c085 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 54603906 1250 54602656 54602659
    0x10801080d050721110d02060f010302060c0c0910140a0b0f03090a15050420030619060302060c070e01061d09040807020414190e1f0b060703120b040e0309 68
    0x10035040d0410404e1a80020711140c0710500d0011001903190040c0b07400f2a1110094040c0512956907004034800b28105206034401c0445580c580d185600b40000c1d940714800e1094513000d4480b400f5034503070701d8a55240c080c180d4100c4114080b820b00c103c0191009121400c40d00c0f814100c44100042d41c6200d0544801e070700c8140d80b803505c9a90780c0e0309003400c1059610b0010000c0340e0a40b81881554025448503006070301030f120022001c1030308800b10200c554180882941036000d800001c2c408148a000c0c0000101c0c005e40104100343e895001c180c0c1500140d0b4400080c1e04041c2003806504d04221030580100310518000d030b680b0b130340d901d80c1801d01c048042c0c0241c018005200010207002061003101d14983d40600100b000c02c09a080c101500102a26414000c43c860392202c00e1b054070700e005148480d03513480302078508a01c181188402082881030101081c9459580090060b901c40d009080664029241c202007200c4106241040760301c89040c40d48031300d1801d08030480340c2c0d2000040d00c03541c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 54605156 1250 54603906 54603917
    0xc0a090c0203040e0103030c1104020f070b0601030e030c010e0c090c041a0708041206110c2d010504030906080105030312010506030a09051e0c04140c07030908070b0315010801080d 79
    0x51018089046200d1038001e190445600c02c000807c2683c00a170345242280140c0c0001d0030805d00000700000c0e84100422842014402c3c0070540100343c16045941c0c000d18141000a0306c031440004207810340d0400c136042009030355120448070406400f40a400c1e01c01008840241180c50071040c0103c483c0554001c8074200440d071956650310f070521408030341440c0d0b0801d89103500c2d240e0301c00d81c4021210842c10211039403814402c58200d0206680140c0d6507413000304024026403200524074030403584e10814125000c1c288004000c200c2c180070f00c5250b00903800380d40c4110205040c518040c0010341c069201d42e01a41c8208880d00d40131003485502d50660f04100e80ca07907526240e40e80038002034020b90801910303a024250411080e0110355104499104120b415941c4060740042084111420b103100071075400c481c0400503626003000401801501d1180c1010598241c4a40c034441c6005066000744a00c40c00000a0001405107501100501c6100f440c0001e603d60604035420384420002e500b00082c00f1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 54606406 1250 54605156 54605171
    0x11a030f09010b040204030809040c0f1b0809060d06060908030901050a14130b090a0e090a03030b01020312010305010504020906030a0302100b01050f121803040b070f030306030b15030f0c0a09 84
    0x2020b40001024260082045d9211626070604111960180c99050321851800741481c920358015115444140960348401d4144100103901980601d808001140d05040c2045141c40985d1403001500d184d076064070f030015070141040c0002c0d10102d1290440801580240301800c190b81e030103000c0720000304071460120b03405880303580711000d640100428100761100e918400b19030580c644024040c0c1c0a02100e400303100e10755a07023804500f048160380080382d541000c01407101190117900305606514040c41260701d05401495681c0040c64280c1023298180d45030020b000075881d04403d5203822010031400ba080701101c83c1d41c00780d5221040031414000c02d0b15000c51840e268015000e5405079240301c42c8041c2d48028800c002d0701c40d20800c403450101c00340c4000a9010351403000060328240ca01c03a001d0140703008001c0d03c1d41050307105800c00c202e003011303120003003c03001503100c03e010380c01031400300c4001c0c1c0f00b0f4400b0000c05007091002d01e29085603034024640d0003441c1d41e07245030420071074440c044000b4401 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 54607656 1250 54606406 54606421
    0xb0306010b09010509040b030f01200a02120309160f091103090a06090c0b0d02040e100e0a0203100f08061e06030a1e06020307020307050706050f03010e0a060f080f0105011a030f 78
    0x20001c0d030151f41ea1600816000c0d2036010410b4104000c2804121114032681c068500500c44900404940340016400b4249540c14060880010b5030005224000c03160384251100006040210030b81041c24070840c080c5d000c01260815005c0d00951001c400c12032030031440c0140c60a80c0e1006c6080000d01125242c6140109110f5030704130801c003074103840c451580e46030303030313115070f11000e580071b0701c10f001413120380307c002600201013403021000b61186096088540d8480e5103000c0c029401c0a03000c0b03511010710201c0003480401c10080a401490410041c00c1c0610705602c07800451862240108182c207082c0082110b40da40c00709017030121550051003020311a8a030200034a00000303004e401031103280b001080c4004e25800101401c04644100c04440160380c4403402211240034202e40d03912000400d0006100214081040c5a88100c5401d00050802e0382c3d1508409581210703413020285070400140c00307220880a000b0030380500b0214062095038004110044220701c401091200056110408102c0c3d0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 54608906 1250 54607656 54607661
    0xe0f040515090a14060307050303040b221403010f112505030a090509011508010603020705010212010e0a180c0501080702032b1a0904021002032b0b0306010b0901050904 74
    0x10704005003078001580391000e0450300070200f92034490018003141c400510581350000740e203401c0e030b074001d0085c600b003520707042a017107180c1c00c50240c03940c1041380703816035000c54031b890746402000f004440d840c41c06d0345102000b41421180a5100152010304000600c0d0320ba50301c5204440c6800d01414040d10aa10310044c6038154084508000384140070000b0b070102c406601c4070152060341c000701d0303244e41e599a03a604404d080d81c60101007030003c6080a401004a640a03030302070700c0c81d20f0141001501c0c03c501d4940d002d06914098002040780c120075414003e94820600c40c082c403a40c5401c02101c010b00e40d80e100d602c04c504644c820a41088964000214a01d10070f006443c4040c09500d41501075403550b03007044414611100b100561140f0b804100806585800c60b80440ca400c0980000d90b240c5440c2c080c070501a203405411070952104005442c400714036811315040700d0383d41e0248151540b082840c0031b0140d81c030f07020f1003500c2a030012005105151540c011076000350400d080190b038420400b0040742c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 54610156 1250 54608906 54608941
    0xa020318040207050d11210307090815040f020d05030304030807030e0102070c03020607060e0f0705010f031b080c13060203090a0902040503100203090a14010207060507090b091302042d05010e0f0405 87
    0x2c2c07e8064464111010301c409005e9400f516890712111081601c0d04003c0303580300003402c140a145d03031109010501040010b481586200d002400002500340302e0303111145580e200f0b44040f07001600210030444c40e540d0500c02c4220000c0900c000794500441034a0b2854040705901020703200b4003000451404100f441e600c08807400640005861009840c244c0540e1100040e20543c0e01050300018542034192007072080340b0114020603043e40080c1d000b80e400b1154194002c0545204d094108100100c001d040d40c003000c000d040c541d004507501e2400c60144404207105600068003140180420f0101d43d034089040d04106021a40040c1c40744d80c1c84100514003069860003620302141a1300c0c01c40d6440c5c043d00188000743c000c010901007600d1b004402c859400d401c0c8284802d0010910158996207440101d1030000700000030094209911640703074101140e8150b090441541402e6001090011810700c0b0f02c4c014942400c0041c001d01010010945000011260b0313403140c5e03912000240d04100d800007501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 54611406 1250 54610156 54610183
    0x30f090f050f150609010e1b160c0f03170a0504150804020117070206070e181006080c040509070509010201091a061306030503090d020d080a020318040207050d11 71
    0x100c00290342031407600d0b58402c040304500ba004903a00391003018030480206000d401c01404101d5603a10717040322005200405000003c640d4244050101540075007009030008800240b03225142c14503a10700000a0440d6520412500c40c181d00100f01080f0365050350294044901429550740311600c0c0111080c2c425034101024010841c5111940a03074024010f61042d0b1003a29400000750205044020a8a04a07480c030010780c090400101d240f885100a03000c0100007628040c0030310315284028191070310855240c408400d1803802041010f5120205540004080038601d21346800c090100700c800500400d1101880400605045203034400d5000d00005600240400c06003428007060b03520607241602d020f4421480040c60900c0d2200a22460342121307440401949030800d60300601c0039000000034160782c010208200240811481d42c01080c600e61113038051550f030442e92001712a264410044180154414406400050b0b0006a80e8804540a00f003141c0c040000305015803400c3d00741d25026 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 54612656 1250 54611406 54611423
    0x1003240606030c03050a0218010e0f1201020904050705030f040320030d060302120c0a140406081005090114130611130b090301050702030f16210e090601021903030f09 73
    0xc4642d4035911042c21003030300313540038413003511261003c606a000c0c64880c0d8864188512030303100d0641c0941d1903890002c034050540274280c5a50340c00500390113561034605030543d4001404a0661030b041c40341540c00642c50800034154105002900100440200010b090201c41040d284520f48a1009079560510060071a55129600c0c4860030103415580b008078020650141042c000310b00110701c40c0d0f0302d04401352600c00910704d84005160140c0a040b940ca1300907659103004079882d041800080c00c1c4d203107030f690003003400d04280028070f00715a45041c1a40c402c01010091000f225a1601401500ca80000022130020b15200441d0315900c0780c000d4103501103094040005038500d041c4c2c09400e800000b18001c0000d980d802c00203076240d203d41c0450301191181041114031a1684225aa604901038901000e4900d000c011081403031590a5031300d004603040502c294074510345a64102d80c00342c028409404080c0c005165403008214040004051540f548101c580b2044503601c82e021550700031040303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 54613906 1250 54612656 54612659
    0x9090106030b091b0a0311090415061704020a05060a0e03010501060c05010509120f070602090402070b15040608061311090f0f070306060c0312090c0312090501030510032406 76
    0x7500811228540501038051580060b10014203105900c8011000156140c03600074041021001010240d844d5030064000f44501d1070703070361514401d0700b6200b0742001e44003c0c480c4c2090f001818041280c03441c546200101010000103864000300c0f40110341c000d4445503250038818030b065a10580c25101d10b03425600e00400001c8496000d030020b03881c4c034001d600820080d00c0b4102031984640c01103c4120b8041e900300100200101200700416606001c1e240050510b944800050f069078004041594441181800c0c008112000c110741020038100310f508018103842c21000c240c07522002800e40413804050220101408000e001101102d41c0040000300540b4140952071082d000955406040e8852900001d000360b01030b04c41d400c01d0392165101c4040104242c2da0840d50f03200c001a0110b4200c0d01c4200d0500011001d11300d541c091486a40e190543c0c4401240c000c041d5071103070303004c01d04043c10030003809100300340d005045007500d0f04079030540d0b8001e4030f01116001c82e02502d4842c5040d546480c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 54615156 1250 54613906 54613919
    0x4021807031a01090f0302151201060c0309050402030f0a0209030c0409060c020c0907050304060903050c0d020705031b1804020402070f052802030d230d0203060f010305090604030302070206090901 86
    0x41151a26003420000c00700080b607900440d2404414001c2c03107030701081c400d0144051314103d60f501e5035441d508000186403500c03000391310f80042001e910200124402154900030143c2141142024001c01d03203085082d03180c26401d02541c08806444111501d900081405c060b0324180608088410094818080b40e146450954002c1003814840030050080f0010106c65142c8095031a00a444507a90942561650748581e002409803c0c4110113208040010008800d800e110800c0d2203c41900501481d170b00d41803d050070040c0c14202a40500c1c0c24074440c41d000e580b00201100140100044103401d65200d1000c070f0001d00c035696015001040c1220b5400400100141e0490b41c106040d04100e03e24200200105442e10081c500a50503041015040c49040c40345001e9050600100c404a0002c4041d13410a036240d0320980380b005603d1740000c200081c3c0c1c05c0107180c05a40d01020310342005140f4109180c50384682024100404054001540406659561064420000c0b000b00750f200d00b07594a80 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 54616406 1250 54615156 54615161
    0x3050709060506030103050a030f0e0a0602060708070201060f0909020d17030a0f0506090a05071404060201090302010e0609030a050d0204260606010212040515070b070f120c020a08030402180703 85
    0x1140c000300c58201034000c2150b0810600f03590407661300c50b008025554040d03401341e82d82030b8901c109204100b0500d00144c1d41d50381e40d4515000130f0829401503d143c5c11b020170003c0299034000d09090540e81040410001405d00010100490703460700b4001600e41c0c1c591000601a015015020742a000034035044034444503440020350068208980c03c00445696540d0202506e008550403031f44401c00d00001035100e0900d40006902003018074007600100b580c01c81b0540f15070080d401190060303650711400e000f0960244030742c0c424100004000d0410303203400383c50940d0328410340e9440420018040b552512802068054034064480300d03c0750403000d0f804100a602042c14a1701c1440b0178850034020070300a500203d0250500c11400d10032a18250a10043c0034440085031503107880340c101048045e0110b800301c103049005142d035686410001400d800014068050100800c00003864003103000d90407500014100300c2e2550001f20070391070740d940f400043c44041c504411010030f2545c00d01000015540365 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 54617656 1250 54616406 54616409
    0x8060718090f05160201090201140714070303031506090f03030302070302070b041d0c0a080114010c1406040b06092401031e0e070603060b16060e07030f0c060807020607030506010e0a030507 83
    0x10a074800715101c44c04412400e9402c00380e00a80818003145540c10148249001040000c1c0285414680344907000c0380186040b0031031b80143c0000340d80720388659010f802580000014007103843c0202c0c5c0c1c9030428030a0b5012044510005040c5036000812104142c024012400103001914480761603070b076500491005011122451541940050300240c0500c079440c040e641c3d20301c0596215040c5a003001e521526140c00c045c7ca290502c0201030b010400240b1020f030b42c07681016118007070055400e1078544440110000b4000d0703032050141104019002c4a0301e44070b014014039019065148004080c0140c00800c41d0821010070600c0300c070f1301e1501c42c0c019a0030601c07001e00e050044450071561200100c0880d045806603d4560608020030246102400950184140130742000184445207800341c0d850039071581e00440740754100e440e0f41018801b544613200024101030030011024031b05000009e403180001455582070641c2d44001c25183c0e4400e0042c20000600034180d41c040302e0f200d05000d6542d0703403107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 54618906 1250 54617656 54617671
    0x90c060c0303141302040f0b0607081315120f0908030112051203060d02090c0d0e060708160906080403020c03060c250203030a080c09090a0501060e030708060718090f05 74
    0xd103104420fa441048203c01d00c14101e64004081204990342008040c182140d103083d400c0d61240100f281c03541c0d41c940240041845842e01c0c2e5134905801d0f80e40c020000940c0d20201043e1540c0010703540d21504030a94009842c1180000928001c0c4d0740280c100920f20003030082e0420102000115980b1403190340c2910716802201221a0603090314040412484225461500100000c2c43d090040c14558011900300e009414240d007008a01c0c1001c00454820141c2410f031644540c05100d00b079500420742b01d40082c0718140910850221000203421102c031840b4100400502c5000981498420b014400c17041038010705982c1242880848000701ea0014808a1a00d1002c280c950a18041002c90042c440d07074050055810301484810603900c0b0079000380300562070002000000b01c280c3e180c090081c0308031040000040d0550412600070141c850000303000c0d01a511a00e81804201d1b0001340c0d15500c4500352078001120185451031603101805a4444000c0070f00b13006c10910394518903009a8810581e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 54620156 1250 54618906 54618911
    0x40e010303210509030d0e151006080f1b0f0702040507020303010603110301030c0e06010908010213030c0e04050705060c0c030601030609050607180e1008030304030c0606140604050402030406090c060c0303 90
    0x40d02c0d540c030464409031503805060b8820044075004030384079000020206000c005440045d00c40c0e0700c2a140369101110016050f99038500306215242d0800400c68015a505e81000c0903440d004441d20101514101e50050074980401c11650403103e02048420466020384180410304110b24042d589410a00800020906000d00b4980e1404043e00342c038100e0b41c2000006421514059050305c2590003d458a8100500440082100b081c240024010340e0719201101c1c0321180f031801d01c04a990010f8001f001444010003d210214500180e48801c4c0e600848043e0303a10303810100712502c0d14007070034040da426000b0f010001003488000e500c00e40c15180100300b9200c0596518030101e514100e986000401d41c00e86d400300b44210503a104181d0703442440081000c10403500ca01d15245990400c842c21000504907517004400c0004a005100091045103d006154043e400c000340f8107004902800b406103070701100140611005420441589030400c0d51060501e4841400510044005000360007190 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 54621406 1250 54620156 54620207
    0x7150501050a06020f12160506041208060d03120c09090609050a06050906010c030804050307060f0c09320a12140d0905010e0904020d05010501090218030601050f011202040e010303 79
    0x14008900004005201005452020a408a124107079044150300340a0207d44045460000e03401700461802940111f1607042c074090034040040060314010326450240d400c11802c0310000303030850600300904400030804a41030318804011209800e159010404480c20301c14000340c1c80116920190041c2c198500a01c02c0c42c2c1c0b10800d000b5541c505941c0980043c0d041d03009000841e200750034490b00705204e80c00340c9282119540320801990703002040005640c0e82c8940ac0b00c110317134010750031038010011000ca45820386185025080100f079051491060052415244843c59981c0e00138500605110908000000802c0c1048001c9042040c00e03d1154070480c611400c3c8240940008011220169501900070b180001444642600036104a0700510341003480f0000071828083c0c0790203408000302c0181c13200c9401800c1c8214852002c81c0c24080c0d000907005212a40b41d20f090780c04802000c4c03c000340b148041b104c47c000240f05c0c0764044058040c58000100c00c00d41c6c031101003c40381c46004206444034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 54622656 1250 54621406 54621419
    0x907032a050f0d022b0b03070321021002070302240412030b010c02030a06050702070f1a090604080a0302060109050105040e0a02100210110c0609191707150501050a 72
    0x100340e125400808690180604030030446144010003104007428005030034150844864556400c1071602c0a240118508900000e0099442a0489118110014640e140c40c40e2110301904a0079243c1401c5045c130030704c1c03400300d06000700305070600b900604900b1540c80040d424000e441e40e41050800480c00c2032080403c0000b0f11074541e0342d008a801c101c8010752030541c240705800401c0d9160076181444207050388000540e60a11005403441d000c0c1201140d1031614210090402c0040d420100039410f40603018800a08420f01c95001120606413040d540e0183e01c0c0001c1d41da00131035001c8132040c841c40c01e41c001016400b00750301e03048512869090259036200d20411043e204910405501d030b40c4140b40a074003520740302c1056070801c031442c010399401d4441c0c22450016140480c4958944490001d00c121242c28104440e80c0c2c4415100041c0c24000c408944100c001c8160072405010382c0c611a0b0b02c0c4c040c0c1c8118108448541d0350100c0101941000c000c0e480340034000921900d84100d00050000904 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 54623906 1250 54622656 54622721
    0x30b090c04060f090303212405040b10020a02090402150408100b0a0602031909052d01020a0c1e09020316020c0316030303050c07050d11010b1906030911090703 70
    0xe882e0300d40c44000d501500b810040b41140c911002c00000680c941d40c8d0200885008603801d4510b48403d05c1e580081401c00040c88241d80b40001500d01038012030340340260a59000c1803100d24036038101d5458607130751101e0001840c0342655030b455000c902c0c0b00040c00510b1740400191f401201000420500039030802008110b04400c06108240160300200524181d80c0c410640c401c465561506204400030384030070101d030114042c1c13503000340a00350b1112420102c411603004020042804d1000704032038845a5203420340240584640107003086e0107500d201715a003a506a031400341c089034400b19182d182c182c100c03540d840c0e10f5120402c058050b100c0c4104080c100458400b1f402c802140003051940d1450340c1c00c4000700070040400318500d806001c4000000d10901042c1160703603e44d40c0380003041034201a00340c02c495402d5550f030312131040134207800c1c5030040c881141e80c1100d400d400e00140d0700109082014082802c40b2542e80c0c41104070307081240d541d0b0140c0c001c007480c01d403150481c1e04406200d4074940e030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 54625156 1250 54623906 54623909
    0x601050702060307032a05070510020403020a05090a0f020a09030209060d080306120a02120a0209150f10030b0d050717121b07180203160302070b0c0a030b090c04060f09 74
    0x100300c0e000b04001340c00540a50081c4a4038940c1701034606044c4e896203070403501007401d540b0346c8000134800141803003841020828584203407100c00d400c51400380b45a0010301043c50510031907004520400008040e05401ea110705e000c00d545060941d650094481c00070700701d07405408100c0c49201d600c408214982441001c000d442540700d44907600c0d544400e41041010000500500c3ca03604c6a00c1407100181c94004240500c004e40400802c01d00017548108425020020b10040030b509604800244940d20b43d48815001e0605403541590315041c160100c010704101c50860350480302c000e82d605e0421200281200841c1d81140341c5503040c040000c541500c0f54030101560640038400c0c00f00ca46043c407101e0489100c0b4142000700d5039044ea9441400344040808a40d240900d40e010040040c00c00c0301100308084e442643c9070452070701c107541d80c071901103850150900c94070b581d02023085204180294013107081a08010020b01075442c288240310b4046d440b50080300005030000c13905041c8036001d00039280 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 54626406 1250 54625156 54625159
    0x50702030309070920120907061805060306180f0106120207031409121006030201020c0607031b020301020c030403050105042607060c030612060207021002031303020405040c09110408060601050702 86
    0xf450b440c00842601404800e40040060100f040c000035200042000900000316104055842da02d44484040d0800c1c00c103a200400348100300e042004081e44402c07003041610400ca42080d100c0c0c8441c00031031a917642c00c0001011907451001802043c503d01c101e168100c50041d41c444113024807090a54060b40a01c04c0c0040c040703040c015411400c2c60460014240581014043c4814201001009071410200301034207039240350345020a01c25541e06000365041410143e900d54940020740d90700610000742d0302950f4140c075a1103a001021580c02f0f4044440015500081740d448035102e04205000700401d6404417a0345a50510400c1500655080d801103440802110b60074a90f03503807078000c00340410340210402c05694450121b042000c9400000c0203074011180140c072461240b040c028280b043c80c01c0c000c2558000e20420754146451403c041c29254196004103854980381b0b00996892802c1d08620302d00d40c184554500590300090140040750382a004940d007507201c0000558a500c11140043e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 54627656 1250 54626406 54626413
    0x315090a080a020c03010b04270807060c0c050c010201051006050c0109020901080c010e1002060403050d0603060504080307030c0206060a0909050a0206040b131706060906011b030201020310060302090f040b0d0b0408070204050702030309 103
    0x18280001401d801800c0901508aa51a00029a440038110313801980000046a20241182c003070000820810ca8032140c280020000740c140030942c1c0c511101d251084400f08080018039910b008420f4010584499000e130402c01c45585131414592103e11a0060318001041c00388441c05500d0090750340e6054150700d030058031940e129a00c08444c20fa001c808058031007a01c80d100000003980b24820715100d5070003510105d44a0a00b01d500500782c40800c0e4900d021544103d0a1002c1c0c0d5689012440440322002000034040d030f003900d000360030100c8418020758840310201e40011a198441300a00900e81c0d40308004000644880d20050054000780c2c003180c01743d10100c0019030500340401201d030070003c141070000c0051004070140780060011002100181d401009200c3c108805c0d100d441c01800c420300341036080c54050004a0081200300c07017000d103d80e88444540e0361503101d500c404004203800c806102ca0515060410034669408120124025803900c400141c0191004c410b480c024100700c03016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 54628906 1250 54627656 54627701
    0x10f09030b0c090a0312030603030e030f0718060b0f040f0503030f04030b060d050604030e09070c050a020603041110021f060509040609050f030a120e0604020315090a080a020c03010b04 81
    0x40e42d160b0401454190000d0b4140700c0840032400c40d40000305d040e00c050f640454810704502e0b0041c403035240c0c1500507009071b04c40e0a030800030000114800c070a46030407905141100401000e1a4050102a80007400303c4000044400a208000004109480000c016410f403c3d17130b11410302d03644e4803550146000e45481803105000051080350800d80240008000300000d104640340c0d182132420540d012004a095516110000d00f40740310855401407040c1007501d803d107070589505480d4645108000d21800000000808100641e40f42944480010300b409240c1510104043c0d036036280346010b614a1540b02d01110040851401640190381000e0702070704040c0ca07a941c40c480070302000f900442c0c0758056480c9002c00c1c0c441c00c1001c1e241c40b00c100d07614035204200c0800d443c021202503a01086140e0098010000581c800245e503030300440750800e492001e9503803800c0e0743c0d0520800050003015100d0010b000400790764009410940304404900801c0104446820001100e804181c000c00e102c601307152 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 54630156 1250 54628906 54628921
    0xf120b0c030703060906090b04050c090105040608180f0718150501030c030b031f05130f030c140303040609060c082401031e060305061302060409050402030319030209010f09030b 78
    0x307560003a00300c2c100440e00c01d0b1200281d005661711a00103004d250780c0c84140c100185024000d007038004002c1c0400301c0ca00f10300000020b08034851802003106104400021500340c200700103800c5103540190007510301c104401c112003500d1b140c00782700300f000389050403004010f12600f91207803046904ca0345a0b401002454a40150050f0003800b240b401403503501c0e0783c0c00400340c07000d10002c0e0700451160680394100c00540786680440c1e001500d8618040003a4440070002245104011103c1d509410320300c80c0d15403d803500148040190780084403134040441440104401904580066440f0b6035091181944404003143c0203041160941200b600c240000c01584004842101581c1818076010030003d2200540c1c0d121000441200e1081960b5a0030408c2401400e11907103402001900406900f40c00c03d800259081c012030040c8180b076580c4201140456800308215003c0300c40400c0450050405124082c0c001e40026200501041c0d9282e00e42400d0b034030503000101079036440510105c10342c94081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 54631406 1250 54630156 54630181
    0x30603070620011b03150b030f061207080604060b010e0f01050a020f061005010908030a0507120306090e070618080601031103010207050708060717040f020f0103020f130f120b 77
    0x1016040c2c001d05404400c100364400c2c0102ca918400790503c2c5984800c030503a005046413100c038050032424001c0700301440890100e6003141c2c2c02c00408a05400c25488038400105a800c1e80ca0504505100e45400021140004904c591140d4059581088510a41001542c4440d11511142d6004243e4040e1a0040d0701500161840d520140b04441901484880c11072920a040e1100380443c0c456510800003036920081c0640038041342d001450810781001c0c4094140e010b518001828031400d202e840b40c032540f183e48004c000b00000d62060000049850103262651501d02030500014200f03440411024a04500241256440002040e041c0c0c40c507281e281500303c2c10804d03582e03d55008c11440c80445c4040103528003800c9444040d081c18100380c03801a040a0f41c150925211407140b030308010109200c03100404020b601034604c1d508200402c2c1c01207000780f00e032041c055481180402c5044410030300004040c243ca500441421003c2d465826000210310300f084028928014940040e9490282e003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 54632656 1250 54631406 54631427
    0x11030a0906020904090807170406020a03112a0405060a06050708250b010f1a0403060510030605010b0406110a1e08041203030203060319080313020612010308040513020306030706 78
    0x304001414403c241c00020195240381509540c040b00118444040c0b03c3c1b002d482c84401d100035084507181c9840c4c080040d4541655080140074007049981c81c0040d0704007803190002d0700305014055041d00c072602180c601902c00901809002d82d2609000480504051901d101501c505884260802c000ea0b40c0b404d5040e800906080b03040076240815181c05050344010904162240080c00e40940c1000c0800000070b510394003981d0420070140c180405c203c079040c101c07400c2d25000f110104803a0340780002000c07500202d82c8010b101c2803800c3e00000d41e9000b00400b400903145156149105044013900c0e05954007400200a040b41c1c00300c59000c02a8030382e0300050f2014900c149403450600366904800da6299665400940220750000200103180c602404618420031031080c060348a04402e0b00c0d1651075010003800407410088040c42c0105554a003029945500320500140840c0e40c0c4030b16201e62150130601c1064001c3c1e5220000012000c514000c1d0f0b0300c103280140080ca01546070120445610706003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 54633906 1250 54632656 54632663
    0x90c0409051e070515030403120902060306120114040303020d0b190b031003050d03050a0501080d02100b0105040918050c010903050c01030207110405150906030a03142104030801061211030a09 84
    0x110b143c00034064441241580010082e80126504c9103054100a0244d03003080001c1c00c2018a04025200141e0740c242c2a07941101055410004410403000103c0c0107003081d41e0f50050f81c0c14007104000415078513400401e2145250081840b2030302c0e09906200c0b261401525050720008a16410b0003a40040e00145034007038044070740e12200e15980e4a4680c1461051000c1b6800282c0b00c2c0204404c1d004076001e560700500c4e0040091041e141036440c000d441e55500d261000d80287c0301d040715080e5a201d0419100036100e0742c81c0c1004211440c0860020400091b82d041b150390061100c001c030f0310360040841e40e0459030000050039440e650b24004400a510285007103604285944101c5541d40f158401c0714415107116401c46081c0d28150200240c054000b800f00f8442c0c0e001e56040380000364041003418282e00465400c43d280d5411211000038404082c9001407940549020403040c10351100445040381d000d074072000c508107104a00c05d800c0d68000f0300e0060940a0400c041030207860240e00c4040d06502 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 54635156 1250 54633906 54633913
    0xf020105090604030309091a0102031602030c2d010e0a031113020705030c100209061209120a0503180109080f090a03060213140406030b06060f0d02030f090c0409051e 73
    0x1001d01c00a1003d8000350026000194096002c0c032046005101d000b010128103883d00c1c941c407804000003950b900c11214490182c0743d1188003a0b0454070200701d501451b0100902c4c803803000d00d00e120150f080141c1c4000b104010380041c0e0741d8550550003500841c03000c0f0340c0500a44929801d584496080300c0551450b1504410441c0345401c0c181d444e8800b40508034403032400345949802102ea014179140a0b000c120f44403030b204016403540c59a4800458a540b038440c0c0d14100203565940c181402d22150b6110304a01100010308025883d1b40030004503c42c1d0400a184001022884402822185400d5004010140030480e10300300000000250180c618010500e0500540780da4450f401d82e00030315040e400000144d441400560302040090900b010181d0742004014a90b80b2542c00e81d078001b40c403050054100050a000580342c80701114a54140842c0a66480c1440c0c0130105c4441401c407401c0d01903010701503541c1c085180c180148034445070818020400c0400c800600c03014030402c410016018032 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 54636406 1250 54635156 54635167
    0x10c0b070203130b0a30270b04020a0803040812030c0c0706020615010c05120c100606020c09010b0c0d05030601090801090c0e010e010308041e03050609070810060806040f020105 78
    0x98410f80280a851800d94403500c4403071540002d40500c220000701c0343c1c140107503e86080c4001d888440131014402000000c10604582d50310a03c00d1407001540701245050118030f0414842c0744960039006901c01c1d1031030282c6698890380f060701e031300844c01400e900303030171040044c07002c034010a0140d03801c082151001e40c504182030502604c0c124261f80a0400358010b881001144459150716984510b07007820040d0021400360b44140d2524855500e10700c0c03a550110302416180001c000e0042041440c0201f040680d8980401a54842c0c10b020040e12400350000045042c2126201351140c6020210081020008400d0251000d40000340098100500b0720f034006031000003406010000303802405054001410170380d122207002416049922070950710801000000d440504442c100c80e80d4003c941506a5080c0c58800c0707000c101d03400a05079205020501401c0305000c1103440c22220a60101c500180c3c10810000646880b413142c1e14407038010100090105001c030010032881441450f010740340c170 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 54637656 1250 54636406 54636427
    0x3060503030a090303020601060219021014030c070215070b0406050c0903070b0c0f070f09050705090909010b040e0105060d080304050102040902120106020c0102010501030c090905070503010e0f0c0a05010c0b070203 94
    0x64000c00da19400048003403004000b4182c047c8441c901502861003e84440c0340340c1c01c0c1034090503044600003405000d00304025a0344900c10304030241041c050851055036404d0412180030075070440c00c02640300d10f84004c40b506028149004440055034000c1e0101c006079240e4580c1001407000808441544a013084010311a41e02841f556020308540580d035519506014030b107a02d85031074030743c810616601010040c840d10503a001e07920211031641d10041940d94a1b8042150f05014240099070070590340070600c143e481041d0814800d41c40705850820000300301340d80381403d8031415100c45c0c0d007080381c070f030041e102069000c0019036010f802500098176159443c1e10301c1d0201d90200015618420006e00140709065040c402c2d170b0880d4030244024080c650664407449420892842001c0b080c2d07589106440800606004100c02002e00a008010382d00c80b44030b1031a106c481480c4103943c180900700510986103040a5440c5c140d0380180e4826030300c18415501c143c507440b00070f000801584400e00c0340907140c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 54638906 1250 54637656 54637663
    0x70203010e03030c070611090a030b090712030809060708060a05060d14011203020601090c05040e060d151a0405091504050f010606050d06060e0127051e1f0804020f0103060503 77
    0x54800708441c40c5e81c0b2241d0b401c001085070781036403c1d2114550100000c3c40e8690740c000415055a8100080300034a40302c1c035402c00d00d0800d090344410340020140d405c26040c590020b2100b0702c54540c690940302c1e590f0700c1401c110f41244007120300c1c0d503000800c3e100602a03814007201412040c20084030008002c508091064200c1800341d11001000d09400303008410585d041c406140148500d0000780101c028103d40038240340680c0c05007940000b010703c0080c3e010b031355545801c4120f40d0040e401816003640305020101500c0c800724641034481c0c1d8100386036410b0409100c0c582c402c3c104400545a5020b011500428004003d482511503100d0160000d0014500388102d0006008940780c2c0c9603075050b510002c0040c0c82003548040280070388540c070111140d07004a501030748280c041c05894900401018446400029034101a4000d1501e18000a800c0c1400040c518a00401c4503003d203c4442490310007403156132004400300148840c4e000c2001030a18400e00f000680c0141004140300d034403480440d14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 54640156 1250 54638906 54638911
    0x90b030901050106020f06130209070512070806030106080a11041a12030c06060103091a060102070f080c1302090a0306020f070209090c1212040308032a040815010303080606070203010e0303 83
    0x35107940d140c0040100a804200d030020401e0003c0250105140420240800d070100800190184800340c00080940703100d24101c440549001c08941c000c0c1c10030001c018440442201c045010350718040012a401c000020030b1a0155480041090325103c100700b80030213442c019155070307541c40001c02c02000d155650150010585134800c000e588030000608002d28008010f051603040c03610340b501040104100c103000b54401d031400c0c042000e483e103039040100c1c9004165400510202920032000c030341401d000c20b045151810896101070b01c0082040304000300d2064003403007070740031000c8802000084c8003030f006401e020245002c410306210054002c50002c42040701c000005401c0800000c925140004184042900440c014445010900c2400e409032049020150150f071020001440c0c04600c0c020f136101b6011a00d10804840152521001082e0028003070009079000d4040818001c010052209040780e400d6501c3d40565111102400310541c02508140d800d55250651440da00c01d04100550 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 54641406 1250 54640156 54640171
    0x7230f031c06030215090d02060c15011a0a0807020a12030b1e0901090b0406080a03020304050102071a030c09030307020901030c080c180403032304060507110c010c060c090b03 77
    0x1655407800300381152140041c14514001c50746003420a02c007507100c900c4e041202d802d4128009690310354030000928101181280254422000590b43d8a400000b013081e81c03080348502c034098601d0740c84142d620380340002c4604100c2e2100c018400349030014030400d403280e001000c500544003040000c2e00c2e00b0401504aa09850100ba01c401e004e40c900e0425041c070341c03450302d020f81c0e0384c864484590001442d0008184502030855032544070030764541e42d642d40800300400c0a80c0c110f42e03008036180b5000c1c0d01c3e5001071203030307178050300494000051841448808a006820083c040c51840e40c46103504c0c0710710f4001841c80e907018031080c801c19005884200c100f0b8040c500962180d407006143c00000b40c5042d40403001140a45880e00d00c0e4840d075030300b800741035030407e5140c10046500d6445407052194000628000d603a40180310003030109100035030348114040c107041d0f51400c009164109003240c2c2d5074580c1c0007981c00a00c004036142c000c124280d200c40c1407070440b40380401c21580d81d1481040582c0003540c416 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 54642656 1250 54641406 54641413
    0x30d0501062a030f11031b011404170a11010e011d030c0a080702040e100e0d0c1e24020d0605030a080319020d02030403050c070b030c07230f 62
    0x5115164001c0e0744100c15004980c8602421880b500521600c0c41e890700d00182844043e08004030444c0c0140700c0f408250800000b2281c403007010040c0d2001401055a00700c01035440c01082101460030002700d10301c142d410112050f2031024050789110f1075441000714004220b105445a215030f80d0a008004c1d2040501c00085805080c0302d44030b01e1040300c3c9540f6482d495000b0018101c05100124015400c1d5401c9800580c40303400034000300380501030784041c00303c050113088416070102c89140d002c3d40310030301c07050101e0303512401140d002e5440e100703142e070090704138011003106402c01c0c1c3c91501d051042c1c44c0300e428107416000f01461003402380d04040c0e045010030764008c00d01d40444001d42c82040004c02089005000d0403c20382c03a144101c0c800036044825401261b0b540c1100741040740c040f5601c0134282c190442d601e16050600401e5030304584902100c501070050b000580980803c2601d0007540b4604100d0300c0d00c055070351254480c05822000c0e06404103203002500034440c0030b0080c4000700708a040074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 54643906 1250 54642656 54642659
    0x90c120b010503010c0f0e0402120f04060510120b06030c1509040f06050609010f0201090c03030909150b091009150504030b0f01080a0308040501020706111801050f07120c05030d0501 80
    0xe080545050300054040da1401451a0619522003d01404445a420b22502d01000080814084c1c41a010400d6050200c0c000303000d4140113065030b581c46640a41000c2242d43ca4022040e407643c01503100311410442c00d00140e9010419621003543c0240c0010102d601c15041e600108409150554410070040340c04903103c5c015040c0742c003907204075880d01d44041003d1801d2400241c51800307102038950400582400600085000354495007000350400c600300e07405036607460020b2a01e2418007845e02880d080c102411001a948010101a103501c08003203070800d645c0800740300712940c084c0322410404c4045100001c5030740c0c0400c0341c0e01d2403803a5651903e59880c11414017a0301400041c00c0b40354040d450300010080e0060200d9200a006da062402e141d0b40d40b00c40c10828068012400041e100320700d0f203001c282000c00c1c5500100b0003c0c4085541d000c0a911490054680340034901804040340710410101d000102c1c001c100c0e40443d00c0908102038881c0d00b60700c60b00d1031500a540004a801c0e030342c000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 54645156 1250 54643906 54643913
    0x601260c03090d090305060f0606070b0901020703030f0c0806010509030a060e0105070f09060c03030504080d0c021005070306180b06070512120c040503031e0405031902100e03070b070204090c12 85
    0x2842d40c0f00c04890400c00207842c91035684940c0d4000003040d80f21820081d101042403070fa02c1500710b0380d0b0150050b103c80420300304458040e0007540b00120450100e4504601075400900038001c80800c4807080d0be448843d9035401c5c006607110b034450003031a030341805101d008030f0000c0d1061042c0d850070762035000002400c0c54a500b010344a010348003061030031700c00a0042048255030080751000c041e030b0705103808101c603120740c50044040c0c010250601880e40c01e102489514680c001480c4000c6c0900100601035900c1ea010141e0841e00107010b90b80c00d60b0807504140003c0e0506802c154a0440090f0050380f0700707403840d107540d8200f0b80882c0c1c0d448200140024814a076000301580d894000e51103004c481d18040c90940000e9583c419411200e0b100e0585c1c000020403c074400341a980207040150a9414200200903031103400e0700c03502001c074850317107440c0e03a0582401d00c07410703001c0c0f819240a0018401d0784c2c10540000c041d50840b1408030391207910b07888210006000300034140004d1032840c00f080200ca52b28607 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 54646406 1250 54645156 54645163
    0x50118030801051207050a0b09130c020606010801060e0a03020d020a051c110402161211060a020a02010609060b040315060b0d090b0a090309230402042409030302060601260c0309 78
    0x80380070540d01a440901042c2e407907c61b070740125102100c030280d0b100303004001f00310480014100b14100910741003a1681c1e07903802003480ca01c200402d036240000f80e0b888100590b55292444941038010b0443c410600c01801c05c40701d07800030b50780000c5c60180c01d103940e2030028801c25607110814100011904950382007001c0c05d4114507922900300c40640c18a06480c480d18050400b0410240900d03450f0055240c161380114801c10604081005403152850704402e40c40295002c030502c20019884d000c1d001502040c684582016911002052498185141c036114541803485071181c404555a001c0050755416079402030486603283d030f60114207070500c1d0400705c1d0807000c001d104c04d0762035042000303c00001c6d501010007801d46001c20b0071802909000c04c41c440702c4003c040c10040d0007510024010646003904561961509645000082001c0710ba035421112102c45110041c05a0f00c0440418504d40c011003150f0004a04480e10104540450b00c401d100824159081a80c415001041c000900e4007403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 54647656 1250 54646406 54646429
    0x307090203040503090d14010c0305060a08060c0f0a05120403030c17042d02120601080c180a0f0e011401060201060906260c181f06020606090405011803080105 70
    0x210114250701d05603d400f51640320b140c4a20b031085624001e000100407213000f50007034040e0000c2c0200701c940d490300000750007440c050340d406203e91801640011002800940c1501c16485401103070b092801490801d803040d00600806014040d041c080306400c01200748d9171901c164003035035010030682440040941014100c035215085161100200008a417903404156a4150110038010109003501100714001000c0b030402540401c0d083d01400c1c0030400011440e050700c2041050305d0010146c40704005070f20703c01a51a85503800314500180e210305255000c00d5440b02c8010001c23404810a41ca141d08540038100f062624103001c0c00140140c0354248254005451680b17010030440c1e040191076007015010260b0214032105005558102403010b100900c3e500070081e124a61000c0440414860300b001140c5c200c0052503942280e0b140c0b8051071200c01c0c00c80d2a50740180010703484180030702c024101b00800c150384540d02c4503401c0e800d0049581244001500030b948010140d41408100000004078 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 54648906 1250 54647656 54647669
    0x20307020a09050708070c06150605090a0503010605010c0602071106040305010903081005030c0f0f1215060103020315040c09031205090111070509010b0714060a06030302010507080708071101110c0a020307 90
    0x10700f000c1002c020b400c00c100d19044441801c02501c0c5910701d00d401c2d40584141d140280342208141000114207420102400e45080101d602d0384200c0e0321242818200c0391341c0c0c071038240014a05609030010403130550040400d80d0244050400400c03c010104842e80d00550085806a6641c5003070030504d40d001c1d215503044114801204015403501001980d80c1480c03a0346a4403e4181d080010280d68414540d4040603070007801650031503040300704c119140c0d1203070318205210602c1440028169031091089030b1040070140441c54000c924a0140300c000c00005040400780306400d40c0c0880401d00d2440d1080c1c002e10030f0341c2e400f640c403d0031500050142da040364105035640e10146084c0482d569000140703041d0344c40d003981e81d600d810b020f05040c1041001d8920001843c0581000d0040c034102a42040c03044c1c0307000f0b400901a54485200841326120b04803950000140d65a0114041034402e800420b10901076000210f1000808602c1e00a29444902c0c6034500da0b000707038000c0045040078020076005210b03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 54650156 1250 54648906 54648911
    0xa020115030c090f0b1306030311150103060c0512090601140f0a06031e090f11010507051b0105090604150f09030b0c0d09080711011d011403060f0907020307020a09 72
    0x1075503840d0440540c96014414555482d4584c0210400c59980410030101c401806a07244881c001d80342c200400007404250001140b8507078162000c000094000315200950a021403668a140c82c1c46c0018a1860900c0d01002020050704804c80c4078007101e14044c85400e000380072254940400c2201603250608128000d00042016506a40d9041d26000807039002e402c01141050706102c0c580b40ca11440d048941d825407034242580c050102214590789182e105203070800007480d11600555150007410001821503002c1c1a000281b116115060390f105001814102d04003004440004c0746038029400141e8404541c070452000c41e684081c50703000b140241d0901040c000c1c1580c4404282102c018082960301000140706000016a944050740c0c49800100554030340c1218a00014900b4203880c0c4a4001621852004440e062480710b82120620503100c003912806a052141d8603900000c103d10360001080250101d1034480c603410030702c40c22095026544e92203541c0704003c04003281e60000300c641071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 54651406 1250 54650156 54650159
    0x201031424010f050d0506011701090e0d0c0203030d09020303042106050f070909051f08060601031a0f040b0f030d0c1e0f0b06032a0a050d0503040b1b0a080a020115 72
    0x5130807604030761070f448200002040a9844000507114059010101d1f40184084800064600803d81c8103031075907c00320098580c0c103003e011049400d64500700000c0e6054008002c101800281680180b404603c003030107480c00c05603201c0d80c00610408079035074103400c150a03a02c05c03c02c1010320b100720b603800500142c081c05c00341000071004164007080e015045006a850010591f481d110088600c10500c4850a1158154981c045152640b00070b558440c0800c1c105080c0707c60301c010401e0401c920031005800c900840500b901008081c4c86641800c0c1d8010b083e40380004c080740c03014005e140324001c003500c40d842c41580307518044150740790395030300a19000c0302c044171680085c500c50000443c042d04400240700c0ea032a0440000e05000719034064070300c03044c602c5c0c0c20141202c03440c5443c201582c000315a802541c0740e68005110040c2100351004241c0d4104010a0000651603009055203a01248021a0003081d4144503450441c414406503150203020600c0100306d5424014013104a40100c0078900c1c55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 54652656 1250 54651406 54651437
    0x12040b04030206031503010906060602010e060106120c03020708070f030909050603030a050a03390c050d03090507080d051201140f010f0e1f02060c12040807020103142401 75
    0x500607404002c1c031400c0000041000142c020800c91000d050081c020004c0d1b1003070703107803a070020143c600c84c40c4007650174803860521280005c00d901d4100e40054450344c0404a66601c40c2005000300e030190400c0c150b003800310102040d03525003d04030003846030700e02c100a48102c1c14090100c0007968001c9942c142014100015510048103a50314201d141c00c3c45070300e908120100b03402400d034001500d00e025034428039a200d0044944107a048107210100c50004900c40048111002d0310105000b170a1a030188080c0c840c8035100e41d00201031103001d4800c1e00d81540c3c844001c1030412140d007880310002000400c1d420504903a01824034010031001400f164044082d1f004169000604402d66052010700c0048005aa000d02440803092000400a600754070500008102e606407002172030006214400c0000e8402c2000800c40720351104109514010307507950b40d11070140380d00c0040120704058498060002001c051003d0038024446005128140a805c8450188204010100d00d0400c240244011090b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 54653906 1250 54652656 54652679
    0x3040b0a050307050d090b0103061808090d020a050603010b04050f040c020606040b01050c03042402010501061706010201060e010b0c010c0e06090f04090b0103032a02091305100c111204 81
    0x450255040c071585a0f51540c0080da2070307014040c510f00c41c803400c00d42110104855030682034140ca100305010800b80c241402103002c510074070040200400300805c10a108c2e850100c4c024507450388000c200ca9007090b241c002055045e0001e03070100e000d803a008501070000d1719041002d40c5083c0c00a031070410200d56000d03402075a0350300141255019640d03c03c01c140060344a501201d05401c8500c04695543d0b58132a508095859840241e0282c0d040164922502c0ca01c180202c078102d400642e5258100300350000c01084030907026080906540d41c0e07640004c1c1c1d03040032050039802840f68410180e11a01e000c0421401c2d00c1078501c1b900b04006110048002960381d00c0b00b40d90807110b040e0742d4003100c4000f640c0031800800481501900d9040c540000004140e4842c1b0107140e401ea46105080c88443c000343d0b00c6402c111000c500940c230694641c0000c1243c9a140c8030621030740d015900321800a44030819034411105407200301400511580501800613404010105604072800b0141c0c4c5807a00d421482c00d90b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 54655156 1250 54653906 54653917
    0x206072307030e010905060a050a021b0303030f0a02120103030c1101021c030f06080312010303230405010e061e190509090a0216200901080c09040809040603080d09050106050303040b 80
    0x9012094103d262203910400001000e4034000d485a599260248405000e9030400700300d504c014800e43d101c04140e010000020803512001034015825a11000301084001a00904680300f880c0e0030b204010840300302541290007503001e42c84036010f800c0142090035203610b45806c654155408041e01403500d40200031042c600002525001421b520031450003005000326a014541611001c161002441d030403c03030786c1d8100c0b4030a86810880a0601c12580c102c5030301088200e10700c1314144400c00095014205004503204000c03c03d914044240d040ca105d2080440c3c81c04841482c04501e202a2450700202c1004040d15410118200341641c4000340d40c482009282c001c800b600880c81031807222950780c42829003540281180000d07a00c03500e0344440c5028580b01c49128443d040f0000510000c01308020203001400b5002c0300c1ca41e074681e15080455400010307159000b40c0d072458000f000c602c1c00b001920b04407404500c042020102410a18256550740e00b115110b83c204120400896030481c04588 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 54656406 1250 54655156 54655163
    0x608100509090f0123090d020601090f020c030c070501020c0f0a050d06020415081005040e060402010c0510090f02040b0103060e01060c030e130905060a05010609030204050901110a0206072307 84
    0x85035540c900c1041c1d4280510740e03071500960360801d50b03050031100002c004200141d403005c402c0750035503a8000c0c00c6541d50607640c1c04800542c010b00014421805c490304500c1200c16900e20240c5066507407088a4910b50190110203a80c6d00007aa06110315a0b042c0500e15000304100c9401d01d84000d00303800a85090000d1050521074040c2803071100400c03000b81c054800400c131408100c0980320301c4400107440340070200c0e0104070f049040c2e03070003191a00d01442884600d01000004112035626580156217035035284409941d50b106580c1c1030005541d03680500c180030351040403480c03d101c08a20600054801e03142078a4149401e02c0424804880c0761003285044951625004240720a0703070030192400420803c101e03800080300c1c40e000441d0340d00d54101030720f000e100d02c04840c02603845030011001c440003809004e0015548c0c1c0401c101500c4c0a4200940011911000041b0b040300c9042c445c0544e4080000800036030042010001c4403a0080e00851074070704000001c2d154881074500c88032052080801c000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 54657656 1250 54656406 54656419
    0x6060402090f06070501110403050a050c060a1d010c06060605070201031103010506120406060306090f020108070905030c01031d0d0c1401060302010c02010305130c0f08100603051506030a0807110103050106081005 93
    0x4000d2005c02d40141c81d6109044441a0fa160340760300b0100d8031514060820344441c4505810404641405021503120001c541d843c6540c0642e440c440241e0400101c0400b070411000300c1c0c00300d01103640703403080d84c1c024202e17038441c80d40d20b100d030348005030603207c0c2035010100c18101400108420b403145c40407079014004c3c480d0707184a103070b845260a400900240d00094609450040010104005c080920480078000d88440205075200c140445007061f581c09000e405405c0807003034011a5010f5004580d02103060f0b8250600a02d8000907036107003078808141000001c41e4151510188030100304160300948020000307010075829500080c11072002000f0003030415032340d500001c404205007000100c40c00d503c0117000962584d40c10350780c0814000c0d0b0107810b00c0e60064000c0300d28507031454810030741125404005440c116030682c0125259660040c083c54150081c03018503400141c10701c0c010031045119440d09108041944001011100141c0040c1c1c244914003003030294284000d050032045910481320f2 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 54658906 1250 54657656 54657667
    0xa0f0b06070f110d14010209010e030309150c01060e100501030b01050f071502071e05010b0d0215030903040b040611010501060e0d021002120a0c02040e15070f26070206060402090f06 80
    0x201d540b103400c07200040c25410713010b885051748070b030b040d0004c2102003c240c0c2c401610150341c000301a02d0b0300c1081455a0301017003800300c0c4d100c1c0d1a440c1001d84803034034080000090305942c3d1032480101d84070441c2c904000c6206003034284a550303007520481f0240603080ca0301703030301f40000221031845511500300301404a8611503107052568602e40c0440c0e0010350f101c44c0051014030355280315100300194070f1007201c6550034a0300100c05400d01c24407104540e0303001080c0135144403d002c40150305502c050076120b0745000c2000040340140030000200300420345640d81031060b100b1602141e003195010b80280702005000d45600c0701c103a236500c00140c41181c0440d03094004006421050b031802c061210183e035000e0002c60042e0005800141104a090090f0303028080c0b007a500d0182c90f200da0340e5405484e0441c007140c0120b61510321540c24141d00e00514100341058801a0000b0400008480901c010500c00802040004c90741030110603005141500e05504160b000c1c400a210000503901c880c1c01010040340c0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 54660156 1250 54658906 54658909
    0x4030f05180d0501020a030e160e0405010603060c120e070b0d0b010905100504030203010b0301060b030f13020603012d0810020a0e04140402090c0903060411180a0f0b06070f11 77
    0x480c1c1850801080c036180c0e50803901d0110301039005021100003092415002480750302c4045504050307041929140407940b03003080041034074580c0c06803007583c840d940d504000c000502c0c103215406260314107481d442c2c4555540300303010f02038480c1603202540b50740103944100002540308007507401c140803901c0041a900341c3c0b04012038003070903294440355000b12805185c2d501307113411000400039280241c00034400c14180e001030500740d640920031500d007044100b00140c511107600413001e4020b5041d006100c0158295000110190030a8100c0c403001001c000c103100c0031074449856144007915940320416000e10300001c040d2102940210340721015000929800e5142c03007a040180d01c03090081003000400c031f42060100310194220b030100e00401384240844c82041400c800d0718044c4000800030640b07696180d0300d071003505034020003d94000900d078141040c40e941404c603251180c1c4400c0030000d03540c034000f5042016200880742042c09982c080080f50040351202806405840d0048c44248000c0c00590 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 54661406 1250 54660156 54660187
    0x1140c0922200301091817070f0c142d01080903091f080702060c0702040f090807060b0306010f0803030c131e060e040501121101050c0a050105190504030f05 69
    0x42c005508420300344481041615080070b507041c1e400b441010041c2c80e0301c0c00d02079104041c12150141c03003500b20404104c0807541c3c00c130040030000d12540c454400319030603179070300c04e808a003a800200a100c15603800032070a05100c2050f05200c041d90b00001501d498445030242d81e203603500107407410040c2010021300e030078030100219044150094028152503010b09400d100d0400f81d07800c03c2002820005c0883d0285200050450080d01c2c4604c0d65498648185d0800008000014030b4418054940380d405010a044501500503140609008590002e0000805051402c140c000210204004000b8001040d000041c0c03503100c0702c3c0c02a290b90764510182d4940c1c800d102da6202907410011141140303090300c103030b0850318103c07400d90b00d5082e000c071070400400c400e031359090140584d4400a40860008a5101003d02c1407107641814441d00c0c2c0489004030a0500060307880548840c0c0d19202800140c0034030180750340c00300003030400400445c1015034000300314602500c1c004040000104990035a001400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 54662656 1250 54661406 54661421
    0xf010e0409021f05030103060c03141f260601050402040b1b2514100c080702040b1f0206011403150403050c011e0f1104050112060f03030201140c0922 66
    0x3c0309901103110998030003c1c05a40240801c0301c550307050440031107046c0d002e8007401721000703a202c44240c9559544003219823603071100025101840d607880b20000f00182500c0c8604449103120303500410f21211294181e280840607800f4070b00880c41003008000300b03100c0e0707001e42d101c102032106031070212200c48007924070303204800401d468074513044c001d00e0321450350000c05171003183c41d03160a82000c0b0400c00c1c05c01c65042c207800100804610402819000185000d0007402e0341440204009a501000000300e480c00c130810186211b14158403000c00403181d01000800d00401c11000b103100504140404a0380322000ea1040176000382c61000407600301350003081a00c1c4400c6100008000304800855003402d4001070342c006000301c5140c0500500225001e01400b0306e89900702400d0791410340743ca4011070b07801420000c080a02562000082002141c808200d00294003d40c0041070b85210b445090308184d1025020426800b81000101035981b1180f00c0c0540044803420030f9500e01001103030410203007108 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 54663906 1250 54662656 54662689
    0xf04090b010605091309110d1a04050c12010501030c031101140706090c05030a0f08031906030605011a040e0a050712020a020714060c0c130605060409060302010e0f010e040902 77
    0x2004000b0a9240e400070181140600c100e40400c1c2c2d00d2441c1403a04100c03680c07041c026005400c40701c1e80e68002c1c100141564005d9208a0710b006444036001071f0246124810742c4c0440e000e400030b5042460714a0305100381c2d10b8850821008203c5545150f4072006900c08034440140000d11003500c6416076802104180c100b001001c001581c1d5a03d185012801805110300483e40d90f0b82c4c103203010800e42000140844401d6011202d0803801c2d45075160000c948d00020900c205c1040c40d8401d00d854116507000c0d103070003103100702408030740c0303505100705020214604480182c10810601081210302e6032600455001801c0303400005454955140480d10008050001c10240f80000365041e4910742c002204405c8070710ba00c109108144c07441081011510502c440950254000900300c4041d1420012035200307018241d20000d5156074510110745680c0045c0c0c440080d50399141700030019035810650450302e0034012038507651029401400604401901070100b4001c07a40d036a103d10440d110140080c02c080007 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 54665156 1250 54663906 54663923
    0x303030103060509011803020d2708030309060c0708070b0402010c060212090d03020c03070b060a03020316060807030c0801060c110603090c270106180f09020306030d0c050c0f0409 79
    0x2181e042a0b0050b10080d00d01030010340c0303008000c0c40b0f8032080c0800c0f1402a0350683c0a8003989180032421203421034211411018103c84661580b0051210b80180d0000d1841e031016681303c1c5401e410040c20b1210040041d040c03980300304800f80004080b40119000d01354000030045c069111b90004862140c1360500003400300d0b1000070840340113001000340e144030300042c0c0c088481c0840c01d01070444c00ea000390742c185881d59000f8001c44000811080002d54803a001410b910b6481e9a00d0300000e10340080307001d2003180c48000c0c000602400e039001c0b107500d500280074102885040c503281001814460144507901c00c10149004000c10065035050300001c00c24000d01c213540b603043c900754050722144081500c6209252060401c010f5a050104204800781032010819150386400c005444040713480002141a09a034940810012000c00c080c0000d860401d00050b220725002d0b05062511000605040500035026500000298009a03002040300b094620b2a8104c4115002c24090515074000030280103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 54666406 1250 54665156 54665159
    0x7030807060c0e060f07020103090203010f05011502030406090905060d02040906050a0b0414010311011707020c090109022701021e010f060b07080904020f040504090311010c03020a0504050d0206040503030301 91
    0x4205024100090044208101e410b024000503500c4540642c15660002c6042c0b00c03225180505c24041d040550040c140401c5020481e40000c2c2141c103204544001c80e075980c00140050034440f84034042516450006500d0181002e0b00038000c00d401c0e20403015295120400555141c4a5800111815502074400c1c02084c4080c58480058002121001c04003407038401e81105c50304e040d015142c05440c04070302907002c43e400c40c3c95007101a072550f400541881507031409018100c8800c451280700d020694040c18ad2440a2000c0050882d01a03008694050040c803402d04803064030040f4071402c0900340e0920990498075030040c1d003002d000060407500c14410094490b01090190004501c46003860020804245c07128014000f50040c00c6001d05104010700541140703041039070041001c070032000310050400d40e03260002410303100408800c90000b4200000c0501402c2c00f4011000c540f0802e040c2981007207020032000303006008510402d8455880c520081c0c0c04d5486560481c1e002d403a0207410b0740da032503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 54667656 1250 54666406 54666413
    0x307030603050d02071211030703150e0c01050a0210050711071712040e01030b10170a0302060601080112150609021201080d0302040e0a15090c020c011707020d050c030c0703 76
    0x140390510040d2843e0044034001004a440405c40d0030039921000032181202e0029117858100c0a1140500c90300f5101c0c108010001c5150349200d00b08031800220003051484041403d2400c0c85100d0a0b654140103041c032158100c40e80100f00c0c10002c22118100050640d10301c0411102c0b80f5014000c150113010302c8c0800b10300c2c890300035245100301c03910b04101e619510010041e4a998415841003c02612170440148002140071000b150040440d48031900001e1f04d07504240180d40e9040c500708055401aa110400c050b01802180d600404c2424121500d42c036050005d06180048100184200d01c03840e41016086141d0388901d0140c404050215240ca0b0071404616068000303000d044054424840072131030325403090084805441c0c100f2641d48680d141c10740101c010342000280c50846000003140401e1040a501c120f040341d02640c0c0c010500742c49414009418088a07198241001101c0c404116050381c00140810840046141083d918505035071940c3c1136000b000010511402041000000d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 54668906 1250 54667656 54667661
    0xa15020c0a02130b09131205030705040803040e060f090f0705161b051306030c05040b0303090411180d26070b010608060907080907172508010506010c08032208030703 73
    0x1040426200700d015506d69007106d1050102520000b440d148900d0380e4200e400c0d100e040615040300c00740c00c1460500c0e89032801d90b801c50300700e03421440c1000e6007002002440c1c0790003406110604000c0d80d0207021400c1c004280d0f8012107006040005000c400200ca40241c0d040c483d004219503000103444940490194885e000740100388141c6224503c00410a8030415107441000105e0350303c01d0f1403105c0c640c40c150a12003d008901c2245615003c1403014030080d440701d0080303206082e100c1e0649a65054245146840130720400034007401a0b00c43d07190000012008092400902040e19a03441c4c2c200c0ea0f41c241c4039151142000003028410320310000203015800c00e038058081c60703084864040d50750f1004802c5030507080c115044002c0750700c824020010000122483c0c42c10302e01d03e000f134852518078501e00326800001e0045030702c1048000707841003104032421f00c1a180c0110003403800c2c0c42521543d455004040c0000303808032698112900c06603050280d107a40300480940c1c0221001d03128942220701800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 54670156 1250 54668906 54668921
    0xc0606030106050603160e06071a06100c0309141906030501030501050c12041b09141006020a0803010306110424030e0601050105070f060b0604081b030a15020c0a0213 73
    0x3960900030080344510307142003641d10038100107049035417044402c082268050780b4620047e800445c01c004407030100d8422000d011500a88249680d110b0416409105560f40b403000e040f01041a50185c4500003988034070700274200c8070350210f032440c101c0c4043c002807d458101c0c031100c0345c145940700c80042e9050701078110604813400741e4000c00681e0744101620b5480d11a000348944524181c0c40050b00045e02a001c00002030101c107052002c0360344882d48401180c458521407500c0c0100e803810040c00b1101150032002401c000d00c003500c600c000300d0f9540c0301c441c00b040c00000c1006407a00002084400040c2c10344009181c28111030f000c21010740c0280b442d21019403c940c1c000b0b828050400f0110f4400694541280c0c810f039519890140941c0b44c031404114104c90440790a52161485202075540b540a80081c2079800003a0840d080340c01c3e212100c2071025003890b0300036000400454040360529150400704401d24801583c4e0310750210710f41c1c0c1020580340000394442d03800d4a826480c8100e540c06180b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 54671406 1250 54670156 54670159
    0x9050703110406050a0308160605150306060427110303030717060d030801140111010c0203030702070e01080601031202010f1d0705060c0a0f0c030b0106020318040209030c040c0e060c0606 82
    0x145030420307001030009980c900d000720368000a24100801c0060708000090111348410500c01c41380707034441da0740e000c1612005e444c828840d20483d400200503140921016070045421101040451003040c91081803801c1503805411001c110000c0a00780031603010280c1e17940d440182629030ba80b401140c0900400340c0040a95100d0000c840083c0c01c5003400a0b450f00416019100c00c440d81c0c0c42d028101d0440f1110030641d074100008a6a81e00246000340128212840705030091500ca28181c90006d01e81401c170b6204025045024004100c0c43e44c0100d12141500d401c4540400c4d40e00c4021f50a13070251004000d81c01c6110714103100710325403103901117520444071012020b035040c160b03840301000442d0003050a5140c168112a40e160001074074081500078451041c14007840c0540d40340c4400030506d109030300c01005038100044d0190a020f945494611241044408500340071103200400d5803420b4408456003d01d0b0b40d05103c11030b4078060540c1c00c1140303200a20965076504109425511244140e41c2d15 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 54672656 1250 54671406 54671423
    0x418060f09021206190b041203022802300c0a080d080f090a0f050a48090e010b03010507020706080a050402011b03020c10090f18020d09050703 63
    0x42041101c90080300c02e2000c0101c8620200e0320b0f4002040340d8000d0030f6054a6403818003400000f008030b00c04025000628008030722082000c142d01b0040d0602443e000100801c1c4511284240c1d044804114040c5c2984c0544010f8108160303500440f40c501c0141400c00380c0c03020400c1c44508001d00020f2000d050f840160750b4140c206942c0c055084e40d0340c00da04078280106566100151282035441c520326884440c5000300d410244950300c0390089a80c200c07109039a9500410074080070b00001520300c0000092000220803030120001180006034003170000c2440303940034445c9080d1f404004400d6140a80b0080804200410029100e030b8000c10030111b03580e0083d400e0900103071155001160400484005403103015240e629100114010000140103c0c144046507090030038414214124103120741c4290010000220f00400300040c0b10340c15a00401044120301082c0000c0100340603e60440d605918140320441c4200c3c0b03024040d00600e4400c2180034030306140c607010311400244100840e8002c1106 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 54673906 1250 54672656 54672659
    0x20d1b05090c04090e0c090705030a050f04230129120f0319031103011701050a050106050d0902030a0206120103120c1208060f04050108030a02070e06240418060f 71
    0x50090800c0700302c503210081041030204104540894120484924400f41501c1022030b40c80d0020708500701c05c0c1c0d120310000e8804005c01211000901ca265001000c024048107140340690fa004000814000c52080c805d40c00b4052004800303094208007030446001c1d941c4c500600001d1070302d8044203a0400e400f44160100c0d01e1200649401141c003104542c06100076510301418042c0240ca094149181c44040541c0c81e0000881101e41401940c003818400c103110f441000418a01030a41c1c0c005040800d0300351910004024540d00181107981641c84440c010990100c1400024204051044041e401c1400001d080c044003010700755150580b8031651031960740d541100d0b4221000300340b0f003000902040a818891001c503004a107025842078005184040c03420070900458181c0c2c1c020f83c80510346034804554403c82c0e5406018480c090004420007441b00e281c00da00080e4400750342e6001c09000401444c200c0c0501d0440411900940f200004102150598201c0e40004082500c030347c64000b05001c10 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 54675156 1250 54673906 54673909
    0x6040b0105071101050c240106410708070506101a03010608040c090c12061217070303090f03020f01180503071211010906020c0601050901050a09050c07020d1b05 71
    0x42e2491607411412074103039020900010745140d8010102e01c00c15204024400e100c502c080700d245a00310380625500e05840d40761440280c00300c440c0c100b840105510200c0c1440940380d041c8040e4604050034400301d030b620500d841e060f8a89228201c4043c20ba8900000c1001c00d10500140c29030140f040c820303200382c040d130b61050341c2d08c0384d041050702c2007600b00c07020001005002c1c40340d10480d8010380910100f4441607070300c0d94464111810740c40c519011488646482c403000049100d1800103061504034001d000040b661088400040007403d030703141d8900400c00388107140c8603620103099194418600c45a1502904010f96500c10b100d00101c555070a101d50118400c0443c2e0144103015448401981040400d03620080b14007032807407400c0d0030040f5040840741c44134424040d25a60500a090040c2d403101130101060500700140c00c0180207414880040141d07440e084507050441c0c020301e400281d5500c0c0d00a8515903880b50541c065804030b083c1440b81d00344003500322410510720618009401480e686e60 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 54676262 1106 54675156 54675167
    0x40302060a0c08070207031403040302090103081207021f09030e060301060f110604020102120a050702040207060501090b0d0b0114010207031505010e092b20010506040b01 75
    0x20144020160320703124060442c03110b0b103040c0d58280741c40400650703075084600c0000c004521503020b42d10b145200f4010303180607560040c000603003541d413800c040d10319030400109040b44007072400c00305600302c0c000a0100414803011250380f50448000d00d4a000621303001c1415010f01880000241e40c41e030b030700002107000c5c010545900f1040c1e1019400140300140130300f42400c2c0341d8400414400540e80000f040012004040900e9a40d500440401c8410707008810009412900120700b1074100714094210342c4c1a2101c500041200144990412180c040180d4029001c25400001800b040d010055451035000040c01101c5071141d8980c1d42800d0728001e51a040c00741070703850006204650140014030b0304042c881006149803149042c205660b00000c0446112007644001d040f010240500a1980505a458902017203001b1200440d4040c05048a24912485c508034045d40c0540c040c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 54496406 54676262 := by
  have h0 := BRFrame.cov_init 54496406
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 54496406 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 54496406 ≤ n) (h2 : n < 54676262) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
