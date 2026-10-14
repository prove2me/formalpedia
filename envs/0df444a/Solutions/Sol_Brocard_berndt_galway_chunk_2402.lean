-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2402
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:36:32.699012+00:00
-- url     : https://prove2.me/submissions/6210ba1c-6fe1-48ba-bc2f-727bbd6a1e76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 431834532 ≤ n < 432014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 431835782 1250 431834532 431834537
    0x3060506121f0525030506010e01020a0f081e040e07020c0a031502090a180b03011d07052b03030f050a0207150905010222091802091602010908180f01 66
    0x1070040407669591800d0040312103100c1408034480c0c1e90500d00403204c41c0400505074598601e9002c2d2500c080d40369200c5400781c1030998604180c5140315004a81d5401f002c0c0028050301c10b00c0c055280003446890003040406904c2c0440310401c1e50141059940342c100358454a0070650400030040d0031541400300d951803d40444460080741e08545070311207104203000c00e46014076400500c1c521580d5035460345400910620075012a1243e418034000040d00304508001d01035803c003003d41d4003014004009100c2c8808500040c24410320b001704002c40c1134410050b49401c80789100b0804034030208540c010380e032240a902d020440a804204403003c40780014246410030b4414082c0000254500b41c1200210302013801c041303030701c0e07146050080c020f104460501c10040085100c20b10020503194540e070440781c02c103208104001e010b0001002401100000030350052480c40011b41c9207450a4840c402d13102d051000040707038070441d1382d444d000e0703880032441150180c42040030011901d4180c590714007901e802e1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 431837032 1250 431835782 431835793
    0x612050c030a08160c0302060d29010f03090206071703090d03020f0301060c110301150e010f031e05070b040b0c010c030e030a0309081201030b0402100e210a0605010306050612 77
    0x15200d0f0200c5001d8042c00d52403144041c590b41040c0a401842d1001440d00102034550711001c02c1c21550043c00c03072450b03100303155800080c02250b01000c1c0b20100405481130311901500c40901c0801c0340140b13806c8800700da0203407041c08020b01060f11071110300401c0d6000c42c841a500d06000321294505100025001b04250040241c40c2c14200507101b03a81c11a915030400c3c8959001c1460408038038061400e030140c256103001c80b01c1c411814054661422580c03517002e03a15140c0d0700c5400800f10794000b0b000240851244040030564582c600001501250090f400d0307603400d076110400e040c125406036002200c591000f05158806240030706c25181071420509081141007413809509449000d201451414107a4890840c01440031881c111a030805030084d40040d42e40c3c41c1d140c443c61500c001e95043c1d0003000440c1b0b01c800124064040060070410081c1a546014006118880e8040c2c2802c0030410304d010301c660410014903d13019032400382d803107008041000c6c03401a09001d100000b6030200207955121 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 431838282 1250 431837032 431837053
    0x21209070f0b0318010c0915090b090108090307080d1a01031e020a03021315090e040b01030f02010309021c03020d02031c05070306051e031207050309041e0612050c03 73
    0xd141c0140121000c00c07441a489030340d03030403900c04c01a0f90741c4c800c0a51542003000c60030015600c0304c480360070b480400c41c20b07121800c04000c08030358500c032034001c0c540c0790502041071000d20f60050240742c0d4001084030413645051416900c02010342c1111240440c0c0d20340312030000d484034046d407441580f040e1003844c04002000703140d45c59401c2000100d4550659a42c0059401c22030b91003601240c2d00f4000d042446450140d503000c0c000014115010510b000515912001c00c2c8000301c80d800030b001d00d402260b100c5d0f0030b9007540c4900303040b0682407200328140360790340c5a1240181c407039140342c40104960042c03003032580d803060801034140302d401e42049085400422414030b00203145041075030f0790313500714070b00041f1556140015001041690032095108180e04c0012803009000c1c540a8801a01501603814081f01145003000c41c0c001e250f802801500107120030181800c280d480914038006070360b0807140900680010a003164400d4100c4c03103600300800260400c2c03007070420203030300b40740400d500800a1106 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 431839532 1250 431838282 431838299
    0xa050a050a03080a0c0c11030c0a0321050306060f18040606030b041a220e0a2004050408190e1207080114040c06081503070b09031603020f010507022202120907 70
    0x707040000d28401040d44135107c25142080188100080030f000f242c0c20b11384a04202503401145c2c5180c130007513503894640f4101c1600ca072060f240184000f406107400d09445404030704081d003219005001e442060032a07200d8507a02c0380035210080015440000e22002d9240030301041e110b0005c1e00005110102c40000c0305034848098240c40a03d90401c040d20141000c0d42c1080500b940c1c04135030070071b441408401800d101980c001081040e00c00c5060035407810555060100b41d49046901911a4000f413040c400450894001032620341c0c1c2e1440c0c4402c8031400100022000b0740f203014456060707800008140032002d000d10844010640f00740c0b040c121460995070303460b041c0309140186001c0040e07800c0820340f0b00c074001c0c461400c054002019610419118020102c1d44c8d041404814840c2c468404d0f081e82e1440e03006a20710689401501c003c41d001d802034015902a400098100d070406101d01108620850607a02c1031901c9041c5440075035a001100c0000c080048058080e10064100c007104002419 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 431840782 1250 431839532 431839547
    0x1506120b0307170c0607081c050402010203072a0305250f0510120c0206040b070509010206071b0f0503040e071806031802060304110112060b0d0506030a050a050a03080a0c 75
    0x1891640300343d07070180f801e07204241000300b680d002d41e4215001003502c508128980c0003500c126800b408100144c0c003008800c0100342c4a003900d020340903800400490000ca1509051004240400e2100344130b10701407421400d17645802d651003035030305030403802d0030110784100081c400782080310845404501500b48540043c00a0042c800c0c0352003a12900084031241d80280545240c43e010000d040014540b980f0001e5102c1d04200d5084074040c0120740001e401900400a890705690180d00170600c1707a441d071100f628001b4640103a001c0e5082403846140004180030180b040c1c2d20722a00203181c456151140c145001c40018222505115620704440c402c803540c0a4114120343d0245404124001c20399564104c0c9208640c019420802c008100000d00c0007105000003031301001c0e0380d41980105848150001c98143e40229114014200400c040490b840c0c0c100c540c10010003001d8450008841c1d840d58513140c000703442240c5580088081609150304038180740da20440c1202d00303100419031b040e0010003e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 431842032 1250 431840782 431840789
    0x91c051e090a0e0a140a02070f02040b0114131409010302060f0a140d050405100203070207050906130219080709051c0c0b0c1b041505130e011506120b0307 68
    0x140216020050355509030b82c1200070000342c541e903819401c11140030380282940800f02141c00c0f001e0400710301002240d208841d40c05403c0703071800b40c51014607801c1102402071120001e04024000d05600710042d072020041c545141c01c0400c03660324502c0c10044d00c4148225101491145030b04400410150304d0b04011641c00c8051b007110b059417641d020700203623500741c01d0064003110640e01190758000701c40715500450085019030100c4010801034080481640b100710380101c01030300802010001414001006604004c00900c0244410317001c1001070103d80004240c42220038001c68650076407904102c1a6400c00902d192040134242404080740403003403100780d40c640310400720345071200b40700d10517400380090120200396698a61451220b41d544004221691800d4400d25908410301c1c907084c440c82074180c000e0440036025921700010400b880040d0380c06400302c541c6410041c66502028403030300d4446126940f001c850300f0300f0301c440103084c15012031807014128030b0501c03403103035580d80050a0340c1103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 431843282 1250 431842032 431842087
    0x150207080d3216021206041e0f12030203010608011a0735090312070b070c021201020c011409010c140309071e03060b06071e0f0209091c05 61
    0x100403184401c2c1520303203896001c6945400c0007141c0810f90b01c80c1620b601d05041d0003142ca07034180c0c40201000c2503c0703900544008104129040080d412180b80b00b040c104070900603440041c00070401d882e2403030111070244080c00004e5002005025040c0c00c500154094031401c801440c050002990381c480303178460075402806a0800c00000511401300d2210f10320028801c490070144542a00d183c40c58540194505511a028052082e400000e1000541d56660303007248005586440e030807015904d0235050b0409980004000740e45042d4001c00b40010450b8501500002404085c4810100300808010703002c40c00b82d90400c0c030074202545c3d10a030700c2556a1407407501c1580d240c40e6a40d01600c2c0510992107283c86001403d844100c2c20718000f041c0003105c3c014502403101a12003010030000c0d10a4403c0140034206070402d40c010a4025a02c1040b1548220b103003d040014540000d01001b8040780c420742c0646c88400c041050710540d0700012041229410880e042003400781010540320307940c0311510711 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 431844532 1250 431843282 431843327
    0x604080714031c15080a05060108070b09010915090b030f010f050108090a032010060e0106050703020d0302132103030b01090617090102070b0711121903020d060503010501150207080d 80
    0x800888071101400034140380c4100c540503c1c0c00c0c81c6c4151580230900c9842c0c2180100342d80040c0c101c401d08101d80483d07405035212812642484101b01c0380300b2414800138108072945901040c1031000b100198020110000c2d821410341c075000760f400d039240d042e800c03090411242030244801c004002842d422403580c5420107190b031a5016000115041c401c201d03280491096100000b0342c10140e80c404000e50b508007611818503a02e07100700b554039105155004005900c00c500403080c8500c26400382004001c4401e007c19865902c6808480a00305080c0c1c00b134600780006149400c250b01441420b0060600382031500c0c0b4545030410250140fa0020031041c044480c0c1c0002604561080d8100c40c04a40d20488179580d81c10300c00c0c0010302008401c02d51014612a810103040e01c0c00540c001d07160042c642101203da1401d400f2000c4008e5003002c28204001501c0350b00104042c0d4080c000d8a02074440804c1d502c4513a0103002c0d00920b01b005652201841d50440d5203240110303607003e03680c1c18030803652040050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 431845782 1250 431844532 431844551
    0x5070e0709030c0923160e030c0102150903070f0c05030c040e030904020913020a11150906131401050103110f04140109020a09270c1704021e030604080714031c 70
    0x350f0402c42c03039105e01880300240d002c000c101486070a19450740740e207a60740c00d0b0400301c01c4000e0654500011029501591103001d0702d412a01000d6a025442003400c8140c80c28400740d69904118140170200840700e1a10301e1800744290306042001e200706080c00c980600215501000b015107038032070010b295004a40002d00306682d6200c43c900801c0c02031040108554524040200800c1c0781d6243c48000350324003030f000ca4000c00d20541c40e40075020300c950201030301094980d01030245045480c400101c8401019026070754001800703202d040d000358060041003000c0d4900d04100f00580a550b10014030591500142003003007003080c000340c1d064400b618801a0ba0f600e1440c0c050350101c0c0654070140141700095002d118a650007407801c1c0340100880030605c6038450000041d141004044546442c080024000030050300d8407155624415242e0b0203103001c0c054800000c40e040c1f100440d425104c5610014001e030030000e01490f22211001110040d50400c003054103d41e500c401c0103580340038095200d01081 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 431847032 1250 431845782 431845811
    0x5070203160503040e06010f0f030c14180405060102010207080904050c070209070e010807030903020c010f18060801030c0501051201141504061107080c0a050613080a05070e0709030c09 81
    0xc0d0080000d03600301c1181d811052a000359079038894001c02403080c101d0004222154003400c0c42c040ca03103c5585070b00f4224911240201c0091021528440800204003543e408032070145004001c2084000444a00d40300e02e80c1c02c0c40b040d9040500110f0441e8410071040d0045560708041e689608000c1701c0206d1251107466280440e4001d01030042e6000120320180070342c25400511461002d1000c0c3c03a415036079034550500350b0450b581000041c01581100c40600011741c410103041040c0007003403c1584000503040501d02c072688480c0c0204001c00c03000e50040c401e201400000c580181800d2801d6803900c0c01e070f8601079292941c188140031149442030801072280da11f100c04410762904101300b0303584450740c40c40c0007899009100402100b9005008000c41d040d40081903040b0034540241100c0310309807805d003c0c8402d43c0d106a0440e090820544808500d07004103100c038490490140006161060600384207445001d0060921402e07c101220300304009176510344036404039045180001600c1d8103201c00d9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 431848282 1250 431847032 431847037
    0x607081305040e030705010b0d020609090421020a020109120c06080a02090411070b0a0b090c090310110304030807080f180f01060902040f0b03060d23060702010204230a060305070203 80
    0x500c1d841403c000c5512003003031000000d000003a00440080c0842c448604c00c1c80b440696005d07000c0e40000b404c01c00d241c02800d0824500e80c01034850684020a282042110102c5590491903a0016005114298259a84500324901501150104100c15611580c131005503d6a038401c86051080d903000091003209607605a401c1044041c2c8140000b60f49900c50384c10980c4454411580c800e89131000c100b1081c08ae102c6c2c09150720f00500034040603100c14001d00040c1c1c101945065051084900702c090b481168010f401002011a080e10b07180d041910b009004110024480800c0008035010850854a444003043c0c02192428150141184d0003500c14241b0b800c1301800c4001d50b0034080d0001d20805194024411188442808540a501e61461a200b0b210644000e036200c11082981d1001c240c81020109446040c7d0b002c0400040300c2c4142c0b142440d0007194000c01603503020500b042816402201510243c0c88203501019000c103000c006802c00c0641e010318010103031b42d40e001407100d80c000c008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 431849532 1250 431848282 431848289
    0x4050d080423101704110d05010f0e191a040f0b180c04060503060a0b03030c0d021f2703021603210801062010020c100509070506070813 60
    0x718030914050400c0922007482508a074207000f54008651140325130f12841e803c40a205103000b90b21001d0300e89032103043c012554141e016900c41c641809000001d8002d1007400720502202d60003140140d44048030904220550b1400491481d03554000e5001a14001c6180c040541441511031140c80710300f1b040000c00c00f07030180201440a20420300221404c012034400d02c20018500701c520444041e0140300a072443c5105054040d440700012508003000b0b40c2020402c814090122420400400302192828644202c41409a000071105101101d845400401e801c2d010003002d0041c1d00c148200090080082c0d0385100b00f043e00c5585280030507109010340742907448d05030011103455440e41032140101c2c031220700307640c03189020341401d054150040300c0342070403134290751210140450400c0008009540c040c14015480c0100260b42c0c0c1141d4503031001c0c2440401040043c0030a41c400018101140c20240c2000019840b00380104410796866044a051070303481200c3e10b454040c00d51000b603540c2c40030340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 431850782 1250 431849532 431849549
    0x60303032410081501090b0d09060b03120a03140708070e0a0321080906130201110109050706030f050703050114010324080114100609140f040f060611030f04050d0804 73
    0x1842202c2060f0710102c3d0f98050b001c1080c9600107000c40340700568050100388160140380074244040000c0c00b1945d8895841d507409102c4c00b0458003000d90000341807003541c034103807481910b0110b03580b0b40c0070354503219105590142d00d444c0841070822020140c0081002800413080181c206840c120716290554035200a40d0312a00d812194541ca40d03422203404854801000040c2da45000141e0480002591500803451940300816004890b00111141858143d0689156403907546a4002138400c000344001000265800281c0481815464050344c0000d48400c08050403e170040c4400310340c440480c0300403e82401c0000e0596000b031400c0c0c00c0d1012002c02501c54500181001402a4041d00301c42400038640108489070b030740d00d261440380350546004410014800b07690500200d4481e11303000d40c13800710040c049010304020800103000c0d90f05030b9900c503001c207803191010003249410007603007944038542401039420096100300c0c070071850096101d005d1040b92060041400d100000703003205e01500003035 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 431852032 1250 431850782 431850799
    0x512013804081006050d23060141061c060306020318150601050f121314010c0813022b0201090609030213110c011401090f02030603030324 61
    0x41000c4112608548111421401101071502e4003020600c12402500e000501c1c0001c50320054a500e00b41102c00c000595070020100b8940c9020401003194900801c1800004012550a00c620f1071004244401c0307072110b48a41c00184501c074555900001c0c01e0b1000343c8400307481d9100034621300c242e084501103d1b99598503007400402030050130340007181304401c101005a861542c1180c2a030f038a4420641c600d080850200c0414581e44c8101e004101052070380c500d44c0d081c10100b00b407110603c0803d582e600c0c05c10307000c030390f003e000c01102080b440c0801c014000200900741c2200c0c006018400000e02440d815101800c0704002c42d52500c400c41004282d6170a071012032042e07035805920710780050100341e004c0f0b42038050001300c0c24410f00000c01640d901a102440501902584601038107101c010180c1d100c80a02c10b060584c2c00910445001101170040c119079940351040382811618030b60b40784040e02e801001002010f4800204407a000510742c04441c0700031094024005924910030700345903108019 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 431853282 1250 431852032 431852129
    0xc01030c0e180604140103150c0315140109060216120203031905040e2208030a11310b0f0c210a08060306100621061d07051201 56
    0x1000260f114a03801c2e10100104005409010b00101091000400d9007225007a601d03400c1000760405000c04034682004610300300c0300c0790b801030301c8191a00000d66041005000110380d60340000c40400909841c0003603c50b41c94483d074103036251505c81c004c80070051110202d41c41191810400c0302c0b400c510300d0b808022000c50701d540081481d03102d841450304141c000004100701d05652000c4080e104440c01d84003283d0500d503075426445400003054000c800340d98820b000e01c0e443c000e80c000d000b404100c0c10228503640309464420030151b00601d00100303d03100118207121601c0319404039201c0c266050380480c3c4405010915500d48034098840725802c0002c0c40a5412001d4600080c01d40021982c4600030555940c00078159100c1088808101415800008100311801104218140c4018940c1c0100400c4514000016541584d0018004120302e04400c12a04400e00019400c8012494a90318210304034241a480d0758041c024002e6a003604258680040d07502c0381601151320f8800e02040c1343c1e090 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 431854532 1250 431853282 431853319
    0x702011404090504151a0103050901020706050705090418050307021219031706010e0a03080a0e06070f02030d02030304031d0f1809060c041a0304031b200a080c01030c0e 74
    0x3a0b40c1200c0c200081d806101700a070440c0100c00212191003100340d0381c1c8a2040044000d40340c042c11100c201d56003000b005000c03030340c0b81c0545d80c401d0b25030380c468a41d201810000d2008483c009140121040a400324000000d0340c044112020b503a012502405943c42620030b207800c101c00c2440b07826841907001601001c064029200903c0e0b82c3c46c150f141d4007190341c0c00c40150303078440c019072140341d001411380c00031320004103032901502d1524514078000c200d10301c60358085600c03030b801040d081e5840302c0c10550110440c50f040100c1e5041152500c0a9411410207a4024200300b2040c400c11941d040040c4944403180c81e80246d42008803c001c0642024070302d000c0000c000000c003514019002d003c2c2100080103107600c94100d500b2114901703035a118541401089a455820250044040110318402030b848a6807818002d41c0c0c00b40101511402d0031141e1174101e8403840c41030907182c0a40100c0000300720520022450b01000b6000f82400300351842c49442c11500620142801a44507460070082e015061 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 431855782 1250 431854532 431854541
    0x180d1401061a030a0e1c030b09070e010c030f180603231e06060405090c0a020f2d120f0901030b030102090d0807030306030503030f040b0a0b0a0605070201140409 71
    0x5040001c00c505a10768160425480c41c1e1005040c01075001c00c041802c15034a0b600c81c40509580c4402e89081d084076007622145e03107000c0c004100000e9100e6031460468a01990110341140c01800e000c41da840001002800603141050041c0500640c16482c628203406858510b803403040c40d081503880c40391540c03000740c020038107010319803805104003411075206200070200501849003002880514105480700e0014003100400a5400060522001500d0340711a5001401013030a10031031070719040314050081c9890403a02d00b1816562000001f642003810416466208000592003c0907400242c19041c1c030304004c1115040c445c50000414005007080840500076504090341c00b80b1007880400205802d1f401240c070784d81c0d44200040b4581001440400051000f40c1c0b190901045044e034070307182c41d41540c10444400c842200c1440030441000800c00800b5032180c194441000480d0154011820780d041c2800b8a005101000401c0400d680c01031019503101d4070300001007691076445401d03e00180 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 431857032 1250 431855782 431855813
    0x8071e0f05060f090c0409140d090e0903040f12060b1305070905220b1f02010209280b0f12150a050d0b0f0601090312020106050a090903050f180d 64
    0x14020342c2e020520303140d4200c00c0b0038003911002d0024522640000200300c020001440100c880d2032511001c49080d4400b4000d24008005507164207034030b90728224000c2180100140205d450350420401400b0407449078404400751900008a81c4040e00740c0c0c82c01c100100240400c4544c462020100700103135100c0d0380c012900c640c5041da1110070480d1b0382d40c18890001040b000014582024110b2500d20302907a070b2280350032400040000031005462140812000e14261010380181d4002500300d02c14106802241031340042405001c6026400c0081300642841d02c4c0110343c000d5400141119020828809a419040580e1100030700390400c210441c181a40015056010316035817040001c292610319080a4015002540e6042642e102e5101000101c001000e5a06100c07211030048085401d601e50368028071400c0d00000380c414103090400840703048540c00703151100e00b0000407500007948001035807002c001100c1c0a0f034440c04440e030030106800c2e0f520b03686504254080196801c0c0030710304c200c21510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 431858282 1250 431857032 431857043
    0x41806050f04090308061018120b01060c020102150c0f160506070305060904030806030a0f03230903030f160803270d1d0102070929091308071e0f 64
    0x409403000c042c0415125500c8001d40416a25800245076040c1001c0e034414400d00d520304425841e6592112001d84c03c80c0b504504403202400462404000200700a01d02402c0c1c01c0c10031840d8990103a00003075a407400c0d901580b000e8090140841c00c05203010041d1040a4201e184654665088100041c000b03503288006880c1c5101d10703000318075224000d106041c0129005002e083c0b040d42d440d24242c441e000040d1156030540320302e854402c04646c0285503c05000d1080d03450500c00019580c0d4041400310301d10355810b00c00010480e2440c90b59000046502c1104c8504080340c50316910f60880600810028010700300c02c20000803c600c0000d119002d06030440000f100e040c07904410002c05903250340100304440070424079059a54202a61042641e02410502c1201c1c215a214040003090311401141e034145540c08078450514500712703070b0b41495031075419030fa4218a4500a0001d804c0c454040c80c02410102e40000e28030144070100d082204100f10110b5000792420480c42c0c80841019041c406071207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 431859532 1250 431858282 431858299
    0x3082a120c15060105040e0c0c060a0504020915030d030e01020705030c03040f171504061b02162309041b060c02150723010b0316060809061b0702040204180605 70
    0x540c0ca01d0b00d80080d00400042c0d480e2800c203810301e85400c0b40440b01800d0080004801d00a590113900c042003a1849031a03014404030300ca04151040c070204140242100320b4540c011903215896880c00034082c14500194030b00402c2100504409500a200c1d80c0c20180c801c1c00b001515001c1c500d000802081194141b200107582c0d1552440203204044a1410340381094000404000401c8d034424402c0303030024008c0038001640310011280d08d101c800c80d20104c0000d80c10540c00005003240f8000c0200c010b12220700000d0707070f448541001d000010082d112143c0304140000209050080f000c03da4462020300d0b10409151984039500a411120014030480c45410313050a404503404544d0143c0c0c1ca6164001d80401c40340140010101c12004201c079110700642d40c40d80420711555003040104184074010996041c01418154001c2c20b000000f0120340079a448030090024001200303401c0c0c102485a003008544565640c030008000c0c0c400d65114029001c00106041da210311164010012218111024070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 431860782 1250 431859532 431859553
    0x608031b070608040f02011202040504090b01030203010e0c0a09230108030d050604090827031005040b06010c0f030f230306100f02030f1606110a09080703082a120c 72
    0xd9210f4401ca500801410703180203110015405004100c0c811840501c0c0942055281c601003012541101e0007603c0c0281884010419410203200d400d60001d681c0c400b8141c4145440c000c07031036a961a200700440346507180b0301140c401e2503600300440982241035140010f940e4031181180e40c0d8010f000420522442e00010034164581881030201d015407280265080c10a240500e480300c249805022829100b14042e500e0075030740a110452420010900020f410708190a0a8903480c00c01801181840008080c110200c1c0710015107d0407683e1515144411070642e00c1c080300d40e400d1014010499500d91500a269401d4010182d4850102640e1108403001010012640c00807650001350140e00200011507403480541c005100c0d520040c20340c2034104400c1e43c3c5040c00c031100684844c40d00400804c031110b582c1d41c4014401d0041000c84d00030700b001415910358940031320550107030641c00080900501c1c1d0040d88400c1104148080d08241e48100307407003805800955201240328482d078002c0d02220b4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 431862032 1250 431860782 431860787
    0x200a051c0f05070c06060524031306020c150c0405060301051c02130c0215010b030106030c031d0601050a090608030d020912120415080c0d360606171b040608031b0706 73
    0x84160f02d289854a0a0950102100c01231590000d020010680c0308110282e003c5503a5000900149030a81c0040500764070380d003504010902e01400c01c48092108000c10440c5940d0720040d40d046d54000c46960340344001c103182950910948000080d00406400040310540410364401000048180c00395020b965070b0031403a00b5220000d0082d06076000e820b00c0180030310340c03099000c0c845a20260a0000f2140c402c006000c610401c908100b13000c0b54822801404035040800e50880200001c078000d20002e800c049803a030f1a40244103020006e10b034003141c0b00f5100c2d540d40c499507038005842c0013541c102c840f1100d81401c0640c003a025002c1c078440101c5200c0c40c02c1d441100c130743d0304c2100303050011400d014824801e02c0107007010020315888942d003a1003802081988940300070f2000d00100968482e001c03145850000d031521035101780d41725007000d002c21990f601c021031180c0070304114180006526056200240081081d0703007108030340340b1020545d010603d403a80000e2110b801840212140c09a0340d1604 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 431863282 1250 431862032 431862049
    0x2010e0f010801060e120a051e07030b0106030b181005040c050703090323160602150103120e0310060801050604050f011224090501200a051c0f05070c060605 69
    0x380c9000980807070041004a118070070402d000304004022841c130711030404100d49841100d99007501c041d000001070001024140c29600c004000c1000581509455038460850017101446081c007810b8942400c01056512038100401b0262001d41c00b5107a8200b920380d40f03c18140c80d0040300c1c042c0d841d1000824005008400b9101003d17450b64500c000c103411a81d038440c40d55100010407030082d14542c0030f08510b41040c0641c0c40d000f449a01d00b8002d26150a00080c0b414449001000500c80003400500c00304403500c3e0010b10060582c201900c1410700c4070007003450025021b00c8140d42c2c503c2c000020440c0d610640102c0e02541e0f0845080c02103448440c6070400d003071428800e103100000000b490500055030031071115140c6045030001026402940441015500c2480007156541d40d6488204401002e80144001031080034017040e00700180843c02402074850f19405000c4817854403104d02d5110080c2e0080c00064031448014441804c00c1c4c0800b42143d841000e08843c6541040c0e0007091a00b854100c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 431864532 1250 431863282 431863309
    0x130f050f09100b030c210c1f0e150408030a090b0903060f040f060c090611010b01051c060f03060504050d170a0c0c020d081e04030f020126010803030402010e 69
    0x2825441080b02c0c41440280750411000343c06000e0301c668140a42e071066181d04001c401d1001d41050754500c0d02080c0d04260403070035000d01c01e07100320f41005002801034480700341c0200c0509100312050305150004d68001d01c100e0141c0b00eaa0340000d001b00b40c11901202070b01130480705031104e102c0a0786440300503220b4000c0d4100344e5016482000000c04600500c090725400c0350080188580c502d4154507a030083d02c075012112404204111020008903600a030140040c801440c0200300304041100000c0092154041c203c0f00c4020140368024034540f6640104010700000002c1007459a81e8513001025040c1202d050358140500480020001d00420f602042520005d03c1c9038001c0e074501013502d00074a1194980c10421120341f04c200d0050701e41210007102d1601901e0b440d0707113401412600ca06009070b070010356000b89405000410001707a03140302c10300075141c0c2424201420f00c060084c03080f641007a007010742e02c400010800000d040401000442c001c034000ea07134510048201f0418424030001c000d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 431865782 1250 431864532 431864551
    0x501030b01110c041e02030903071205030915070909020423010801060203090d0f120305041209060504030605091903091401030501050f0405100b070c0518010e0a020f040302130f050f 80
    0x10b10b2502603107030560201740c81030f942d200c03603207843d900f040f1443d0200d07002100c00307251980c0001008410320036880709001c19000146800d0303246140036545191580c00034441c01c0b0501e845c2001140d070007405000d401d0041c1807400011500d5555820504d42d10002c400101154002050102e405c15403107004864103948240e001140350141510510070b140046400c01d507100d000043c409400102c04040f50850060603a40100340e034141130070900030b407032070f412810010f0004d440410071010750020190780413603030040d10002d00c543c0c401c040c0d141050340096150b1180090311904104240d04101c0b13940030b9a040b80d17440f1f54400c0b440340041d000c5420a00805600c04115a40000e0600e03090700300350350020345401809919a51a60b400f01503400c40c52040720f00e280001c1c814805400c0900d44904501001000c169040d454056aa050b0b00006010030f29807540005201c00d15600c441e04440055034080c0a06024040d020f5011000b4001154009040750800c00452441c19080450714003422120 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 431867032 1250 431865782 431865793
    0x915040f24210204020f030712050109020a14131205030301030b0702010b0916091a0d0b09010302090402060a030902060f0a020105072a020418050f19030c1205070f06060501030b0111 80
    0x2501400940c4401035040784d1180c0c01b004074107a9070001002450069030592560f1410310300010b0b0300d50a07500160000400140705201c0f44600562200445940300020640b065449100f070000041d01c40c19500540c1220070703c9100001040400001541280e010380101021920307011012030aa5202e240d0256001040c6008201c4411040000900301102c0307043c40306400b40c0d90b80304411000030101c10b4429241c0d01091020b6030019030300901c13041c0e21044503440c00c41d44c15580050b540c81c0c7c1c0078002a02580010070340e5051140694007420059400400c500e45400d10302e412520141c0c03200d07240400650a01c40030480e041e0040c0c07400003100a80780c01c91309021380d02045129040700d0054050340d200d030700d0300c4220108903c4100621042c41c0030314040c003071381c9520521040c40d0580d0074040740c91001d1810b64150101c0d030301003141304034075070b010300a40b009481d90801241c0500805002401c0120030610801c10006503038005805c50f442a00c00740f081c0382003800156103100c0611200181a001f9 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 431868282 1250 431867032 431867069
    0x3007050a0513081e060c0304030c141f060e1003170919060f020d080604020703030f0e0a0b011505040e06030f0a0305030603060a0e0c0915040f24 64
    0x68024080301041454442d0400000080d06191021150321400359038000015503455840c8008603c5180d50a810082419080c00405511140700090002d810041d50b40000410408201520300c1c0b03200010080303503010700c8a5180910b0745086c1030210024107291440000e2146c00355801c0038420a05499283c003489d2860300c2e900302600d003209218102c000c04001d48003450340c400900b0305140c18400b445264007428805c1c060f003c2102c04030150255801000d080000aa0148082e980040e0940700580c8800e243d04c1c0a5004e01380e00a138503100941080038801c25180002210600c4ca8001c00300340300c04c0d0f640c503034402c010f50410740e4402c0d0010382c04200510581d000c0c00f00054011102a0440f4003a0035885013807030800ca4100d00032030000300c0c00000d018803407804000f0560420710242003080351245003c00f0035034841140f0707490b41c09a4002e20018419034031002d0150480d14024005002c0000d8a03420100104000c170b025610001850309030761482c0c00410303021400c1d20701c501c3d00f86011441c0c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 431869532 1250 431868282 431868287
    0x7020906010e03010c020a150b130906060317030f070f0c0204020c070e01080304060e041a040c0c15062c060d0f020303070b01060e01111207020a0302090c3007 70
    0x18000c080c20705005040402c0450340d1000d100710841000b280e0b000e805007041034540421718010b5840c1d1691054241961a1010740d0769034400e800101a0f072100050304241c074601000601100e61010f0424079601460b406c42c402c414009510601040b8030700c0726550b40e81c043c2600c0e0741e032107510300340005001c9001480043c200b650041c01801005011103250580d649200804000260840d03c00c3d074000ac202040307280d03004001e0440c0345000f21420700502cbc80001d8040c501080f502000340c45184c580441c3c900c0c40707008646074000300e0f4201c084400320a10303480440c0040c10041c441c3c010b00040da0000740803220720032007080320034141943d03020302181c5031903041003251142080d054442030b000260325401a68100028815544581e03501c50b03440d03141c044081d0202404640d410705000f00440d012900540118203c90144200480d0545812081c004512000e109400080d009085503040c081031010050152250801c06805150303a41c504088400e100d440b04004040303541d008001241c0402e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 431870782 1250 431869532 431869549
    0x807050c0f06041428020112020d05100513200c030d05130c0e040b0705030903090411031b0408070306050a090506070816050a140702040e060c130e010602030702 71
    0x20503800407140440180e01e0054140380095030221038202521180c000c00c090b05110321440088004c0003c0c00010b160100000d1605007910003c2c100302c01d031b2404000082070390f03044d2042d01c2007001c1c040010346440c4040f07001100441c042c00d44203444948e0901100a41c0e4000d500c950f01480c051a610958214805103903500654082101e5001c00d1103540c0c2940703021b104035440b070001d0148080b810b03405418000c2c1030f481a82c0003500064040000c020100d1406800243c10102034036280b5601e90b110845581140205118150701c2030412080100f03591307984020398040c1050300445034201600d401c103051315116a00c110805500450b404001244680c0c0c8400c1d0302400c8218007180c004a20343d112401c0010484403100400c00c0c000500c10b00b803070542240b4680c403000b42082c03440e2040c0c039070001d880c000ca807820004500000185000c215182e030b0300300e04408407811041310b2160a1545200707006402243ea010b1020700070b400002003510040c0c10240c12110340d50040d51501d1200d030241f01584 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 431872032 1250 431870782 431870797
    0xa170c0f0a03051024120b090106170a060f020a1d012303072304030f15110c0f1f0f090b010906090f090b0126030a0e041803080705 58
    0x5810700c00030114500b840b400300700010346000003500520f103140b0740e07480703180312044040e5840c0c0a4000b8407900803c0a22007107025001280030f030060b950200074030f014021507082034400f03080300f0700ca0311210718000600f00180b604c104000d100c0705d01440c0c011402c81c0514942100000e8195500b080c0181101d40c1c1404084070600d0035025540c07201d01075140e400c09884040b00704800000130415865404048507450040041000705c40601142840100780194080544036418240058080107505007401036038040040040c44900310070fa0810700c140d0000c1c43c0744c189038003581c10f5076010741030f0200c0c1a080c005a401d191034036681108007600d008108034a256035a0507965060400459010a40b4034001c2480f040003007401410120407905070340c9980b0f81e00d0b83d46400c040720300c80001c502e50384460640d10603a604440c4024903540100c5030120300101841e00340000680c101101d6400030420003601d1083d1001e20908401d207040e090305503c8550044d00113420800800d00c0c1c244a04003e01c2d24 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 431873282 1250 431872032 431872039
    0x6081606120b100f0e0a141003060e040b090f030909010b0d02070c080706020c04140f090307060f0b0f0303070507060e01050913091b0b0415110a0f020a170c0f 70
    0x80b1981400031031050302401035101d01007000341d001d012030b00c2d0b03200c00701c003003d040180c1e81303810307860f02c2d082d200c40d6003080518241d8440e00000c1d56214280d442640100014020f9401e0340da02406c05003000626810295000310490013400c8501d101e5400001c1140e0304500064041c44007030703107894001c42064002181c0c120361f5540801c0701802180c4041300c1c2001801d400070283c03408501c0c0907000f9250900856100f80690705085003201413014108429510202c0b11311004840c3c4d076203880c0c40341984103180e401403a1900c0c00c55813540c00c0c1240e038010700c1c0b014000e80340d2008496440c020560f5a02400328000d0040d070085c1000d004641c8036001c03a60740b0b0401810130700d09109008000603030680d821a00c071041d00703a07107010200612101040c0d4008030b120440703191241506020b0680882d1040d400380c600b40c00d441103000c0c44030b0303486041442c0410030340307000761840c100d150f1030080720741d6900040036803159520460101d030401c1c207898a284002c02c01d00c01072080d40c00707242c1841486440360140da42e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 431874532 1250 431873282 431873291
    0x1332010518160903081b16060c0204090302070513061404021204171e1206043c0c1e030507020c0d06020d14041e0b010902072f040608160612 62
    0xa00a08040c107128a0304a460081b52501080503e00d8003508030301e2058180c0b02c022003003002030f411007603c100107501903d01281c401000d00341070789864216802581c015001d03c4403034041c0e04255005d07000395004101a8941444036a080005a01230103160060300c003580d0021400150401c1600c1804441145006003001148031864540101c0c4030368044085900050031030081514000d0990300000494003044064045001c891144102010724400e0a50441072a10310312004102c074a80d00c0b0800310107006c030090007500100040211300105030146030500c82010390754002e00031148038400c113074002d010010507902000f0b03030a105828141c03101903081100c1540850729000701104140401106c0866040600e0002103207444810191040300241400c0000600354002030342c11a0f11010b0b0140e2200d01a0400342c0c2c440741c505a00ca04040320050b0209154541180090442e01c000c450802050f40d41e2010b01d80ca98a061030120f241140d003207018131407c0d000c0d078a11282205020000203 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 431875782 1250 431874532 431874539
    0x206160302070905090a0308010b040b03180c0a151d130b01051201080c10050a052a07091505040e030d0e0316030c171813320105181609 60
    0x4644003070301c03201d10320f805c003040c90000c4c503400c08c4441380180300c15841189070a1400240c00e44501000e0880c03900020b802c0fa40070000d1001300803584400d0030080a02c3d078820740e00c18161b202c3c03170f212842c00e2000c40e029403454155003500504680420354083c124151081109410600904800c0c4e030340d60511006106486c0d80250340320020303000e8062000101400a00c1d08204400020510848420004100b08400f41d0b560f0100c1901c03003a9407409050103c04500c0240d028990380c0c006040f0800d48100c200010b1150a10f400c0340007080c481080744a02c25807a04144820790f10001181070309944100030a00489035903910200002504d181502e040c07004c102c00c2d0300b80c00514614240c0000b502c1c010313903006110345036203982e500e101c003551010702c0c000c4160b5411551513103055041d84203c1689000c1d989440c0300c0c0c0c000148103a02d001411201c00200d030001d0840a0914404842644082d800031820307081652000c1012441a00d0500013950384680542d0381c09803524181003081503610001 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 431877032 1250 431875782 431875799
    0x70f0303021e180a0806070e0f0a090f0c110c0d0f060905060c0a1403070813050f070608010320010503040602070203100501230102190615050307061119020616030207 73
    0xa0100400c026018800480f0920070082c282d001e60700012555000001440317909034010b0240700e1202c1c0700740d0382c024040c210140004c10802155014103030701401e15014034146070065126046000280e111803080c40c042140b095500c818210a540e0801034102c120004900d40003000d01030b1521444000c00d00d16100c0c1c0d030315030425105032140c0d58450b40125552002ca600a001c0758910b0b400d8950306400d41c81e00c00002420341c4030181c0010f6814400c40300305003c1c4031040c404c0d02c6c10501001e080301c00840d80e403400200702c01001d02c403d031100d5101c94000b015000f01e8903008903c91030165035a606503210394880400030b501142c4200d038107101e418504003000c0f466005603402490f01c4005542507230b42041c1440982207031400d1150464006400c0c0800c09035507442c00310501500801c002031845915802505030b20801d42009a051043c00d07000140c2e0341d480b81c1c00030381c1080b81c40c041e0f550b51321a690890045c4203248400070342c0a82d060108280680c2201c4484200318001c0c412141103540e2005030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 431878282 1250 431877032 431877037
    0x1b031d040c020d0207090504080711030c04020a17090703170a090f06090603050612030d0e100e0601080f0d0203040302060c0123060a0e060904020f360606070f0303021e 74
    0x181c005a0841824140c103a0740511503800100a0b03103406102a2400d0b5485841c2c42c414050700034980c4d00000e40d8106151005c002c00401d40340d000d8021581c4045040003c1c0c4424031032010348041001c0e84001030405030340480d03103200b02c0e07a110010801d901344082c02501c064005000c00020001c10050000d02021610b500b04001d001c241c032440c40075420301e5401030640d100181842d018842d1284014443c420000460b0820381c040e00c0d0000700200c40f100040d040580340303c00b501085007403000d04003600d48003103142d034101c600aa0032030f20450241210603494881000055016800501082001d42805801844c1540191000050640024002d80c40155000d800e50103284002010803000742003036071072480034140741201c00d0810f15010002581c1c801c40200024010040b40c0c41e100000d456020148000c0c286559601f4160310400c83c052501820721071a9170310390f18805000c41e8080c140b4004680c03d5540004a000700941d06803016000b950000124098220400361000b0a0301d107400007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 431879532 1250 431878282 431878301
    0x503032503121e0606050a0804060b062a0c0306150f0a090e0d02070807050d11040207020901030302060f07080f07140412080702040c0801230f09091c1b031d04 70
    0x82d01e01c0c00c10300f050940b070413222290003c0040c484100301d17810600b900050386940c0164003800200d40b01d103014000c96800e029032442d04201c1c002c9016046410070507040c05000180c0c000302154520b070800000c1586c2c480d4292440014800c007800780d07103da800c0007800c0103030350b4002030007002d815030761890100d08403411841800040c0e005034450200199041c00404000c041c00d07002030182504140026100c012407500c0140300d10103681c070100c030507210340e0181c8406a4005110f07010320343e501e080294507440122041e8400500b0600040d1190b40250320441c01920f91104c6000965a885802c2da00c88620380402d50511f802404001003000c00440c0b0040c0162003040c6881e02c48240344140001da0300c0c80b0406000744503280d4018043c88070314804168401074148084806d010b40d56001c14400f480340c03000503401405000821041d00c1e0000759290010b86d080704203081003003070309600300c5401d0030040e5a0398104001046070b0000c80d200d98020001c640d519076008909151a10024046500444 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 431880782 1250 431879532 431879561
    0x6100b0d020a1b110a0e15011d060a05030a050a14040b04150c0c0c17030306060d1803030207020f032113050a060c0b07030c231209010b0406050303250312 68
    0x144440c141005d910307444c018003a5421100300ca0400c1c02d003811101c0b002c04c520504100c19000120040c18016803004010000030b8810742d0f9501d410360005240d94400c40354042d4481c00c19000c82c04040640c82034020ba5007004142000c00d865a0b40c4540511001500c165142c0e0710156a4000000761481000a0318105490b0f01c40460340a1411151b400c84903480540c040e6004034010141c0b078004001c6962064044036241c0d900d042017805c0c10000c4c07c1d080820600d1100da244850201a01513005284580c000c460320100390b0940d40c20140d461111076140d000840c0782c1c4000700d501d1014540034003214550041c4403210036450314003103001c0040990094000641e962044024091402c51254003c081032401348665030556901500c01d545403004802805000500384248213044000c3d20306411994841048500b005103409010707041c40300420741b2442c9031040c00115442c0c0002200d2004081041c4d8056001d04107003c3d413030b40b034041d00080d8140882c1107250300544c4103034401d012247c032021 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 431882032 1250 431880782 431880803
    0x50f2101051501110d1103070c0e2422020c0f030a0809070b07080a050904050a0f0e16030204020705011103040c0806010b042601062606100b0d020a1b 66
    0x10107094000c40a100b0794906215026012a000c482d0104500c1d80c51206410325510404403454201d20314815811302070400b20400300d001c0740b003241d03010407513001d14014024920301c03080c5542160804a07070824803070f602580e8a021141032140d0503000520701d0750400401030518114aca0440c0c1880c00c45821500d4580000881343d0f0090f42100c2804d070041c0791900200045070400381000b6091080030070243c80244003145c1481d0341441801103584500c0040c10034416400c000c03607044041c02e0140440c40300903060030080c018404000a074901c5d6044181c5d24040380360700c2e540a1200030351044005454a540b00e01002100940d900d0003103010300d2013581040161441e05800d18106441a00101100081000100070117515400c0c016110000072582012040000b07400034010700c007950090720020b0b040641030f4801d40650f004081e0b911160f4090b00c04039516094101056141409429824003080c0241c2c6020480e9501411414076142058030b120b0080e401400000e00c074080c011110410345 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 431883282 1250 431882032 431882041
    0x100b0c031b0715030b0409170a09081c1220071203090b240306090d02070b09030a03080405071d09190803150105070f03030c0908070f050f210105 64
    0x6081e19030140340000103429280c0c10702095550074007460100d202010303241c2002451031380d0b035680582501030340071818514003405160885500d800083c007100100d210a02c00080d00040411455542402504511301c9132400714029110781000b2075425401a0350b5010012080c01d034641007400101007440e0154403842640f50407401c07040091103400030503042404400c001100d80c10415085001d052080542c6002c21491a040c0349030031008503410312894062003103002006c0343d01c0d17569446030b07425a400307651a10a001c03418814440d0564040d4042a101c4010030b02c40c2c0c0d4500c0e0030070b106070103448001355107010712181c0c25500282d810300d4110200a1005a01e01000180005002e1000c0365032280c5540d191400d00d0b000c01441115a285001c1c65240540e105508071080b0a0b03201c0302c407101200303480c03c00800516081c401c00c8081040300002013601000003a07a0b4080310120b522095804d81441d05011032850405c0c9415000407042c40f1440d101121020b503400d00e040800d0000610340350 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 431884532 1250 431883282 431883307
    0x3140106050c030c01111903110301090b030f06010b180406180e15010914071805060a090b030c0309010501082b1101090501091205090307050d0305071208070f090b12100b0c03 77
    0x200501d00e040c14900070f4a154140130b0710303060b0bd0448508100010307015001d000400c1c1001403040521416000310000454461840301c0546121140e88249416411880051008803041c60003400640009240f540212000c1c541210700e070900303460151400c0440c1d50f805144032203000c0c1c0200c40c3c940e07290780b0030320b00080402000f290301591900c0c04407210500300003a00782140c00c0c0c0c040d42d03000c0c02d000034103074094902488241004061410b03107035590740f9110440484540007940c009032903500301000001e1000300001d02d504ea90360b0328141c05000d1240054441500d0080e05003c1c03003842090012402403500a108040c8511b00030000490b44c0a0240750a601c8200f001000703005120342031141c10181d031800150841556015207201c0d94450701401c0c00e4640c0d000e40840104503141000c02c0303046030359000389020300810190b1500368501001100603280c00505019400340054244a9004000b80410b4aa40c2204c0c2c000303503202c40940c8034012502c1d070703030302149040e12a50b00008a0503034012 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 431885782 1250 431884532 431884567
    0xc020a030f061a010f0c02030715120606090501120903020a02120105071101060b2523060f0f060f0a15050a080901060302030601030f240506040b0103140106050c030c0111 75
    0xd0003400b0403c2e0301c40e10300040c3c140c40d0b0190400c410000d408003c4021034500300107a0000d000000d4038284140ea40890084c902d42155008500d15400d08100140b10347c042e11603603050b904143c40d2000005001444c00c4020011100f00342c046108100d41e0b5400b5807603180c00108015641e000200e42440c0005d8007510315005851250b445a1424008001194202017659a51924504580022484140c94200c0c0015081c0c0144c1152000f131010100090f030344150340c40c03004a85040c0c80155961014881c0203010807240c085403425500f0004540f490100120040103074020141660700352104841c0710040080910b82d00802c100045c003a600c15040224540d120703400e00028060641554082511000180320041c0181407110711a0304109072420107148410162005000888070382c01154080d103000d51340c090190345001d0020394154407a0080c40c1c5e001d03400080124241c4d203481c00460340c952081419104900040c456248161028000c0c01c040c80e004005207070700c0305412103513840103d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 431887032 1250 431885782 431885801
    0xd0204120516030506060d0510060906051507020d022e020f28030806030f010f020a0806010305040f0209060d0c0816050102060106230c0a031d04020a0507120c020a030f06 75
    0x202c49281080000920000d00c29030310610944001010044030f240c01ca181c200707019007a040650815101143d5503406500c0481128400c80b89049406d61300044804e86104034240690082500d210280c054246170001e45071540c000784220a5a9031034000d81e00003060504d40c2000160400c0210005285c03040050100400c520018140da40182d42031910140d82620001024481d680000134150368060200ca0358040034500203010442d0104c5403840254000d480580101c0c8291012404d03a511902c1281d21480e44a08405d210f10199002c128185000510b0554418151144c0c04002886203800710000d01c0904000c0040c403044030306201600d401a00203038110350285004010282d07001140504064646442c0d12008000d07000c2d8640318417903100d0740d142920907110020101584189000f01c0d401c14580d5a42d003000d5080f041000340d20030351400030001b03402840600b0100c1d40c0c04414607844036013800d0a40d80c501c484c0c0d020400b490a0b650065518a01c401030b02800e02080340103c5600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 431888282 1250 431887032 431887063
    0x4060b0307050f30060712050921090604171203090a06090f060e0606010206070201060b090108180601031412070c0b0703090b0c030403021c0503030601080c0d02041205 74
    0x1500e0070103010552078182ea910760703885030b050100143d070b006141340800c0740b1218128803403035040c0042c0b5180b207030f4503041582c001001580c412070300703018aa0944202800b0303901581c050705040e800e5018100d2900d10103d03d0300100741c1d0800035001f965031100c00500081156454200b001c107603c40049040244442c0040c4100c6800c00420480b104003181601400c1e0380440000368840560400c00121004039130001d1682c0d1500300981c0f1080000a0240d100da00242d080302c07180d64820800b02e003a01d2461103580b0102800348290813503507000d403400d15031125980c960481420203500c0c60300d05c0d0880a900070b8942c48424900e03078102c10f10920134014012800c02940380f0f000001d80d0b0708500800c951280445210001c80c0340010107115040c144000d00701307010701e507271103180300150183c99a2240c88200c5c86592140d605207004074080024140703950700000510b080d503480400546980c00000d0542140d11b40410038a40e2140702840a000070b003106066001e400c960314a00309103402c4031030640f040b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 431889532 1250 431888282 431888293
    0xa0e010b0f0a0e040303021e07120e061b0f12030405060c091f0302070c140f0420090102070b0d0501060905220e031e03160807090303140409050a0504060b03 69
    0x1d03540c5030603640780304840c45458080c0d455a0380e418200d000380030f4000c420f210340c000e96445021840510000d1709843d8024681d4a2140c41000b0080c2d90040001d003201d03410a8042c008580340300034031040c5204001c140000d441d44015004809410000318404141364480080144424002c0c04c1002c6a0b109405a4aa904d00740750b480014034421002a05103481308000c90010b40f4292080e011b407120381d0361104907070706d205864078070340d030f0528505c00c021038000d41e20b40c1247c00c00c62600e405001c1120000001501040d040360301c1f5500b4642c480d01e800360643c442c62078001055060400100342c41548810000341550424100900c12185a030205109079440600481600c0c40c403d403818007240c030b030440000c1180321030160b40d05500034003a107200228007000c002c414409285006501c1012002d900000d00700081310700340c034410010f80b0000c0000d919440148002401400c0b440700a450f80d007010f60a05541d03508034012794004640c060400c90300c8009100401c41c90b40074221105008801500 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 431890782 1250 431889532 431889559
    0x16110f01270c050607061103040b070f210e070308030109050a0c031e1a06040609171501030b040203030d1a040c0806180c0d05091b090c0703030e010e060a0e010b 71
    0x12102c100b400360600c1100000358010800030641d20a0400d0b100d200c011540300d207030604011060355021101040030980807102d204010b40310f0309150102e0700840368104070042d410b441c408010f025100203901070384103c2030048003042c001d03000f42d40284000c0c107000c01d5902c5d00c031001c8801d640c40402d800c1c083c142840b500c2100e12015400030400e040200c080061a40350144501080310503002c07010341c01480004010031442e501032031420640d910100040c1810391501c03000e650b240c0c0d220b12401c00021900b001400003502070703004241c010340005d048030305081c140f42c030070412506642204108090346002c1c043c03082c24039000da00c0042d0f01508140b0784a00e0203a000c40c04040e09404902d05071203401c8001020160000250b40c4900d9140e2003c102a24024424903601d14400035070342c440c01503500c0c01000d03070300e4502e00740c520501800c0c6c0d040381040b00c255010b8000e802d070203445024954131110a07c25a47c0b007084201d12403514000e001c5003000302990000c0c2101c030b4030803580303000d540d5500828 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 431892032 1250 431890782 431890793
    0x30a031a010c0602280507031b05070b0307050c071401082406070203010207060e0c1804020a0504050934080102040b0f070f0816110d020916110f0127 66
    0x1400300c00d0f0070040c0907030781e901c0403244100b41c501504c02d0440e0004580d000d2200499004018051040c40781d2909039405841108104802081820040459008480c1440602ca200c40615044182030410500700100001440d084ca2102c6c0c104185003400c10a0b405200d60748010703101e400c010511415074007101d9500c180e10510481e841d42ca030040200090343c90131500c0075811151810303001007080140e046d418079002d03114a0324103840e92103005681300500d0f2101d01184a04e000707035401810303005d80d98035140c1444043c200040075403207640a4400c240042d1396000e0900540c501e0383c0f141c0309002018807814041e00040d950000100bc3c1c0c41440705114aa9900088070b00401d00d0340521510303000c140c940301e00e0245401200400c82600841d81e00284240424400440c0b8030511a40317152581c404180111840d01d01c0f8084d6200f01000d001c11002c400580c152400c178920f07454101140c1409824161070862000782843d42607550742c0f10140c160701040c19a01141314840440200c00c10301380c1301c2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 431893282 1250 431892032 431892047
    0x60c09050609181315050906070f02030307080403110303070e010305090c03191b0b03060a050904030e0d1704180f0605011403270d0306090606050412050304090e030a031a01 76
    0x21042d408207020116402200014950000c0740c3c0c481890710317a010000707200501510003503070442034500c40d01001c142600d005040003612602c0c035600460841d96400c5088880450143c029000c0c042c0500701000041700030f200840c46049281c6a10b140248150001030884800030804412504840d119103e00d950204280c0001c00054407000704545580c14454450903205031440013040000600184c42c0c2d41c010091803040b481100c00c40c1215aaa1080c0007070020100e50050000395454000310075490100542e0f04054007a241c8200303040c9840f00c00d41107540c080d81101160038030383c0701c5080b598a45030140408001a410051140c2c0349448000b07000004042940d1103501000f100107031805610307020105408802c44001d05c00e41207820300c0103458007041032001340024100000468204440d00544040b546155140ea290500d0040040600400c034142101c0c54001003000144095850081d0400030190030007550703542d00400c0740981259603203100c0301058050585482c9040e0b0b0010036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 431894532 1250 431893282 431893309
    0x4030204021e0c071403060417030a11220504020703020c0d03020a05070b041502010b06041a120f090f010501060512280606021204152307060c09050609 67
    0x8015846881a607002c0e0380a0322007a40c1c603100200045424042600009160400c40f0615040311401c085aa81416222201210007428204007205011000c4020000441c1d1002c81c0240000390082d500c5000d201c03c1e4418081d0010600c60401c0c0c3c0e4401c480c07215044801840221401c600d400c00640d00030b511118042189407007840c500c500030050500921104c41c81680c010242c58003145ca030340000b86e0303a4010b07010714081c40102c03e0b14401c083e4014841d040010030000d000a00300340c42c000c0000c100c59840c0c9119000041c091082c007140c070b00314401c2103020742600c9901e044a0315041d11214603105510401e0b504c0c580c102001081070b15001300c01c60b4590b0b5141c211100c442c0c0e0741c400301620780c01160517010100414041000000e04265032044094481681c00e8038200144025040c030207000c0c0d4007442c1c0340084100010822180035880c24140c207100340c074070360b00f1000e07802c032411800341c001000a40c3d003d500e0b881c04e0b07080c580d4040443d801415040311498107018a50380481c003480d44404 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 431895782 1250 431894532 431894539
    0xf06030c030611041703030f06010c05120306032416050a0c110d140c01021006180525030f05010905040f1401200d0e0703170a0306170c01080c0906040302 68
    0x4084949800c83c01040320081c2520b0380140288032803480946039a40d02c00c88070040e0041400012031481d61151135119201c4d070308000100440c90700503000040c680c2c00074211590520400b458180408000c581550110006040d01d40152a080060500300c1ca100018041045020480003900c0354200c0400c0020f039402208000910000e0004104040300041d4050700c50994110543c1c881140012040c00200d0f00381d080e00e102c004901109810b076a82401035a0907100107010040d0340c5c0d01e6a521195102184c10456503030295021903460304c4204500007040000c1d151100f0641e2001d8600485004004117001005145015115800e5400c0c403000c0041074001c007910900007075542500b100d03010003000100301c00750b03e401e80440e02d00c0794001d000c10380d2250300703110b01801c0b8500c0c0800d001049035041184441143c1c619060f40a4560002c000710050503510740c804140c40343c0f0b00e202c0d0008200c050000304a084086000900403440050a641c890300c4108900b108644031002520110713a41034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 431897032 1250 431895782 431895791
    0x40507120507030c03050d0929030907030212100614010c0201050c0f010507090807080606010f0818070909050c0904150c03180c170613030c110a0f08010f06030c0306 73
    0xc0c5070250408825501c041d1050a00000c08020b012002c1404d40c2c4a039420384540710510760710303401813003000d04464010754550402d1400004426180d402160302000d0203050f94a5103440c0c0d0300090507850407912040155004d00000c2480800d94400d480240004d6114688482d0411300020039410080c0c41c0241040070110b40d03004030305410040301d8601c0030648028002c40c9403a01000340134090302e1041a103244128100016240c1d404601320340285010fa50302005500404020388d00240060318107040005084c02031038075844140f0900d070203040d000d01c001c07502e004a4200189080341c513440d0144141054401c5c030001a140c5060b0100c80c1207a240c002c50709080d109030035001000c030850a03a40c41154003201c50100710041d80c589041c0c60b0185503000b4010516540f042d0346d8401281e05581540440c000200424015101125507030b100d504e2200c2490300c0003021401c2d80807140d000d200781130046002484001c2c001e014180030355560b410300b04001461500d88000c0011701c0e1101038140d035500c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 431898282 1250 431897032 431897069
    0x708130510110a080913050705090103060b070b1506122d160f02010e01021305010f21050604021b010f0b010212071115040f080c0a050f0108091009050105100e040507 73
    0x620800a000c006c400b20208420320304140080c05944c810480c0b20300280c9000f81c007041140511094443e0340b40c000c01500f00c1555000113000704d0950400c0b07855809801800484050700d01c0d062014031400c00e41c1415240c00f0500c2815a02c601c0c1440da074460300418030f4080000d0102202c0e16011400103d10340f600290140c00300c1030f40109441641e011040d400003800e41c40b403004e01c1d81c0850465500f0f070b036521a045642007084590807200d56400342145034100d52013003a1440c5400003a007144004100501e049119900c40d11002036444001940e030b51074107006403029085100e88034a400082c009450b0985101c9481c40c0544140325004000c0c0750014a00c40442d1030f012102004841300140e1160340c1c0d0703142e604458480c185885584960301ca94a400364881c1404421041140c00147c548a10205007100544150000400382d0642d4403074080d0704081d25016010380040c41303000d4800082c1c641441c1d0b15403501345402e50805d07144030500505000000e034000400780119000004000740c1c1c1c212 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 431899532 1250 431898282 431898289
    0xb04140918011119050a090308071509030e030d030506030a06021608031e07020c010c0b0601031413020f120309010804080f0d05150a080309010c0303020708130510110a0809 76
    0x44045003640305600c3c0100c1c14100081c024020904043d00108030a003000c9000d81c101c2c1c89100d05c010300d078001114020100b00252000000d440300c1841060026014490203c44c0800ca5108660640002e07500c0b940c4500c142c1814400b0a1101c403140c5401d01140c40c104001c89d41e02d46911000504c05540010008444600d44451814240d07211459950b00d042030481814180058600c410461758000b0126041500000b4006420b80040e10352460400094403842010b410040600c0c2c1419183d00ca40309800896580042c41520031144800e03005059005101d2107080c4811001d000d500800d60780d1314104000815204042c01c00d1070310103100d40d030310315004810740598449004007603400714102200011541210b032095102c42040f0380145280420080b058203184507440180e007042140c000a544901d444d100401d01a0901501d029000d035100c0c0081c1d44003502107410740320881001d21643c5042e10003d00540f0041c0340c00070107050101c0c40d8580310a43c4046c000c0c0007010020301d0502588 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 431900782 1250 431899532 431899561
    0x3020705190b0c0619051005040911040606110d05120408090109031a041103060f0727030804080606190905041a07020d080c121302010c0206030c04050103060b041409 73
    0x40c0d118003480c3c64042c80c0342120398404043c3d6049035202880e030019228131415124580c17158400107035203640c0e1894441404010034401d14292281d542c1400c0e401c810b0346407800381c40d0044c841d41d40c605520300c681903a0141080c080071100400c00c4010003980f11405512498580c0158020524503076552101d00162107488482c0d20003001c4081c00130030001144a5108981d22490083d0b11600850200c1c100301525001c0031121407400d07483d0319001c00d4000e0310032520f040700a1000100c003d00050407815a84800405500882c1d030700000040900c8802e8040c480140c00000a403480d03e07007101841010300d5181698000c0d000456641e00004040c807031605140d84407015040d0030802c041c18405c000948851202c1204004500e44401241a810108007250180d01002e40703080303210b0300e4110030000400d4030030380c5c142c2c1001084071010003d40d0340e940046004080000702503a8072480d1000140c2aa103107a808a04071031002e001c10003504090b030b24040c4d03281c0d000716001c0d080c0360b8030018640d01c4034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 431902032 1250 431900782 431900789
    0x5060a02240a050708070507030f211e0504080403060506010509090108011a030c060a0804080405040501180605010f050d1d2a0609210a050d08071b0302070519 70
    0x102a1607980035011100307000d000c2c0646880702061200c1e0362611001d48911806030303004000070b0030030451100400e00c9000000010300b02c92a0250444001304015444500c144155103d003d546480c0e2040d40b80181103500c071000071000d424009880d20362a0148280124032003d400c1c00d4642001071000d83c0f280d4101d03405450001d013014159615410140d001302000c101c44003000410b144598603d1400003480359000d03800600c2640741505c3d80d42d003183c017440c1c098021945da0805000115440c2e8490040c5806040141603140269203a21422000c0c0c50080d03101c01e043c0000c009200c031909910404546440075401004140da514000b044100042c42448001d054021a80b904003000c080c80108041a61103440d07031003001d4a0401003140c548141d00381c0581c40303444040f1078180300c81d20400d800040d1031500295080a0a540c81d6076042090701212140040e41200c1081405a000035a10f484040e200504410807680c6550280d92a0168002c0c80e1007a104051180c4400044c1180300024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 431903282 1250 431902032 431902063
    0x809040203040609050609070b0412061b05130b03041a19060602060703150b0d051b1315020a05100e070801060b071a0408071b0314060402040518030405060a02 70
    0x807480d050605400415800c1300841e014020070740492500c15001908005803080a128140351510700004190415083c24080b00d0b0941c5601461065070351070b040f00d280361071349921b520b40e490348200f288030f41e2500c02d070700300c00800038051081c030020a09111140c84c0c18090410345840944500181c0a0b525502040145480741040c01c00b1070103c0e404110203008003413036101480031540c042155858a4054000e1a100d06020300c1103841240d81a0841034006042e9035000c0079020380c042c2e41e00b6031503216000045035804020800c2100300c0090b420400c5c00c01c1e5a20103803000900550380c15880e10b0010442e001000c0d283c4c01a881c0303000c01030100b5001000d901d40204601980c45014600607001044142da01d01c0041211074085171042c03012520450f44005460315004c0595141a103c14030030302d22031602151a034020000803040d48600d41c8000100d80100f100d4940742c8100800c1d06ca004000e45201c500150035002428000400d54094a00440ea45501d94940f03030402c900d003a2808569071321 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 431904532 1250 431903282 431903287
    0x2070609080310060e030d020a060b0109170d020613050606100912060e10020f0301030b0a061502010b1203090a05221e0b0a03020f0d11031b0a050907090501080408090402 75
    0x35440840c03d0400308035442e40d00d8441e52104110100758079502c2c0c1040c440c0250b00300140c944005800d0394440881030300141481b0108a27151044688804142c101040c215030080041d01607880d010091143e00004141103181e10411f80d585840d01c03a100074103582d004480741c0084c66685800b0712a258007600e840180d240181c0034074207012010301180c4203480d42074015501503840d6241513001f100c82ca000c421720380618503460f5503501d10803048010700380030710690703118008038600c903440d180707050b004500c1d60000c540c05000d0020000713214103020000c4020382c802c000c10402512905001c3d03080751021640c101114030200c82d011042d5164400c1c2182c0249042d03891401c5030200b0040800140c4070840400500380d00c00140404480c1601000c0d5114446aa0103a102d1400c0c688440116119001800b0403031030b001d01181c82d00712441441c0c03090b04102c2c11800418181503c062004201c2180c1500282c100b68a025100c0900c0c0d005150400c211440010284040c013801c540b10180060310465 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 431905782 1250 431904532 431904541
    0xd090602031330050f0d02040303121d12071b080d17010b180103140a0605041404120807170c070c080114061002070f0902090a080a0f06020706090803 66
    0x100c84201c101c0b040f100c1c10f032040006a00944a05081d414400000c05460748081402e5485030003c0325691190001000f0101c80d400440c000742008511070388480504c05510b6852a055815240c074645c8130004044105064010004d00404002c1000ea241d03a07480c0800e0608014404080c00706a044103281d0400180101d030000e105c00070b030704075035956101c0c2030b1014003106a66982881400b13055032042c81280a0000c2a0004480a100506000a05c0f0800c00580c2c0311404007100e2400314181c0c0c8030010000e90915009121000100071034220f200c2c98076a581c1c50140b28440d1001081006020000c1c072a98020145030701d103c3c0c9040300d680058a04000390b040c596200700008c0b40c14640700c0c1c90025a154050040550341c040c0314000c18004d07a500e0003407100103189840340c14214407541800240300c0e8240c3d0f103114060080860050f980c1c40f003803002d0204a548950285905901c03508580020405094018070740a9100760096580c03c91410f00c5000340c5440300c4040c000000000520 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 431907032 1250 431905782 431905801
    0x120c030409060519050f0112140109230f04061503150b0603093d02041e12030806030a0c0806040506100609030312060f030f05071202060f0d09060203 66
    0x14812144110428000b42d5111804e00050b0b003206100802c441e0030185062280d0f00d0041d0842c0480e00061402030009a80036590006548861256004181d880b900500a03060341e400381500e242000780143c0401a0210f10408421000410424410060202207410001240c020324aa403564192250003c0c2d241d00b001220350b040b65a02d905504d1402ca0350000c4c5041440541e881504200007a100e0b02e8081000708500e18040304042c0b408405010040c0c900350340303000d0062056201e0400060b00c9509015410040440082da40003841c00d00d000f040000e4001100c1074094183d046c9045045500d6000102e80740c40d5400ea802000e66071814804a0400d40019415104501035001c5403429114008007a4010005018140000d20a80010700100c1d0292180e540d120115290016900c0c0e81d82c0d280d244080d4954008075070350f400c07420018062040810282018040440c110a4400450343c000780326480783d032a40000c82000419132500d2540c20307502c164160f9411005c01d55aa1820344040c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 431908282 1250 431907032 431907037
    0x303120c0f040312030f14132132300a0506010318050d0513030f1208010f0506180d020901060305060406080604081b0a080d0203040b09010506030d050903120c03 71
    0x108001038a801d03400d0780c0310309560280c01081882c0350b4112446858542015084000841040d44c0c2720b5218a10381e41c40312403c1017002026401903544120004914000c44048901c660741000300031003a40306c1d44000c1d5040d0301241e4840c91118401580010035280700d400e03405064240c1d400851901040020890300c54001c103104820990b01003040710780d42d41740c9204c0392b90001d4002d441c903440001142840e500410050150f4054550a07940541c6e0305e03070b0360014031550305108440c002801c08641c901c2680188180b4090700c8041018041e4070300f4031000c240035010b860610180d0300c00840303441107942c56411114800ca40c010304050950361b103548024000e03107015602c80e4042c40c540200081d0300071003c1100d17401258844012072034000620051445440130300c0d1010114020381c44410005101e01004110b13030740c075445000da05c0746003a040400c50b80700b0051050f4800e9040004010301c1c0d0380d010802c0b085241c02c83c2041a241e01007140884c0c640840d104d440d44419000090344001031000102 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 431909532 1250 431908282 431908313
    0x3050709030506041b05031c050a05090418061118010807030e010507030b0316060207030809030f0a050c0901090b01050d0906020904021b19020a0b0304030c06020a050705010c0504050303120c0f0403 87
    0x20500b2000d99074006140d540d4800c850301c8000d40c04109401c141d089c2c420f0005110420191520600301031000000508481d460094461251500541c010800400740200c600b6a111486000e0801d80c08907803c1c480c17150a0070095040090303035070003d50700e540a507221000c4207480000801c418a0600c0c005001003071000340700c1c3d2207441014903900d0b81060300c65058090321b0381940501012071540c0c0d100d00300342d00301c1540030745e06004c4e90b1403048403214204240800240500020200390603940c00b07103c065103060300a100c0f098245185507403182d810000b00c81c825020403c00103005c5000e82400c500038001d550010f0361050000400c9004071203450702403d0310885480c10b8450300d410202011011140401000707400c40d484034070411008095030040c0d54441c2c0a4101950aa5030755681c040480e4800002c4d000840c00116660043c000c00348a09a40c1c801079003007807440c01f030a020019640c0d0040342c002c0004d6618800011390300c80c841700140c0703c89201203036100752110b0716032a000c040b1800051 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 431910782 1250 431909532 431909573
    0x403090b030912030a02220306050c041505030405010e070b09040e060112120c0206070b090609010c14070302070e01170609011e0509190b160e0f010305070903050604 73
    0x26020503100a0340e41207074002e06a0b6001008840044052114540c100a0219004641c2032101a00c0d400100388030000900076034620600b0903083d0300c1c101040f9000a006101162001d0000380030b0508101000103400c2c20790304010b47c0f01e545528105014010031014060580104000000e08414610142c040000110303002e005540d00c8401c81c03903131548244608200e2103240e95141004c1180982c00e1440c1540d80e02d001058a1403680100301141e100c00c0040f035103c0010320800102180900c6a80e42041da480002d0060044007a40103003600403010800702c0d0044000b0714202094001c00800d401002c0e0080904119a542d04c0b2031440c5154800804076070b40202c2e000150100300c18482c074074445510605c2c443d02c506070241400e00a00d0010910807551098481008403043c0180032603019074480e00c03000b106480c180401e14203a0003050200000c1c8515040c01e41030a983c0c0340810050300f082880c001500d591907010484001c1780541c005000c03030040c10244000d02040c28281c0d1807521401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 431912032 1250 431910782 431910797
    0x32a051e07200d0602030f010515130302040f060f08011416020304091a1c020a0b0f03010e220602040510090e0a0510180b150c0706081308120403 64
    0x1100410321621460400601c01c004000101c0c140c0090291002403040015190150350310181ea0707400200d910580c5c00481ca05c51b000c0c0100118a40211200100c002c403807106d80c00c01588ad070303d4950800c01404001c0c452600c0c0c141040d0648401c0d44120014054803090740c4400d03554500060091030714014055a481c004000926507076038181281c0050f00301a401146001e2404c07605000620b5405000001041310f0110003007240c0d83c510700410544401118982d101d0300b00c0c81000b007410700540c4800c810080c03d00984420621104c280c07411074110300401c100303e9940c0206081c01c43d00100003442501001a0507a0912880358060803c2e41d0042d1544050300708061810341d406c807030034400c102c00190040000b41300c03181983c2210760803c0e00c0f80e0300c0010063329000c5001c01d486031040700c0c0349110743e00d80c8040070610706030719000e40074000c0c0c44040e89042d0b00030381d003503841d400640101001d00200c0c00200d004d40c0650007080344010f42244a0030f803200f102d4084c003070807020141c41c1500045c404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 431913282 1250 431912032 431912077
    0x1e0102190305040213020a0207060f020114090606010801090c020a11150703050301090f06121101031d1f05090c100c0605150102010b0102060601120c1b060e0f0102070c06032a05 78
    0x5c603c03c45144000540051006528100c411a00c1159501fa010110b54940d038520182c0344060072141c4c01655540b028040b2450042d000402c2200141d008140301410312100c0e00321103402007036560100d50000c00080d2008140c4001c10881e4030410281181480006000da0600d5072020285040c1c4251100501055140303202e040d041e6203040c020480145050301e0700d1130004010b450280c159031018100405c42200a100c0c1c40c000c06680081c690141c0c11401e401d1000064480d010405550324541c01c00070f50412030346150f61100c961030814060310310103045440f118001c150b0403594aa0140c801e20135480c00030b06140507155607508a80c09582040b8001c10590300201c1d01034803900e01a510140440c0319118283e015040e080d0308001480b111264044100300700c03104641400340500c00100700d020440c0100c504d06400108500c140c0d91040c00039600142da0708201c041283e0309449c01040240344a60350018044100807050481010550020b0405400101801c003030fa1458100314107a242 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 431914532 1250 431913282 431913319
    0xb42030f07020d6803070b0a05030702031306030603030e09070e060307112401120807080307050f271e0d05190c030506070507051e01021903050402 65
    0x1490180d80c5a44060484180c880d01042514041c295400306401410406940c40308801c030400740d005509014100ca89152004030001d445404c1c0d01a802010100d21f081450b582c80d010310300318202000301c0040400c100a20070020394018015a007111012281e0707540700038005010303a2204501043e402c04c15840d062400052051058505031148454666010100001503100402100500c108422843e13484401041144021080200410500e03c0c66940108044005901140303013407401614400000e082c0394113950025901030313003041d1a51203402c800e55450084a90b4501d40351b03000b007040c1d04132000c803901b29403015030000003230300000c44d0780c41c1407200d0200c0000219041482541c0305103d54141800b42003032041c003030400e6444e2990004a280c201c42091441510903518411081c800d005040c06100e80040d85820710138076000c11980c440c0c1d1125a040032010760b100400041c03440c0740101390122107100203a4260800c1c0f4031324240025008040942e006d80c020280d141c50700c2101d51 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 431915782 1250 431914532 431914547
    0x250806090f240a0c05040902070c03020a050a1a0d140408070c0f0b04030213020f03090a0308090606011b0c0b210a020f1c02090a03080d0b42030f07020d 67
    0xa1a205945000c3c1e0710000c100c00a00302c4940110708120080000141d4402c50303102501c10f0611a001c43c4500301d14500400050b40c010343c002600c55250b0704000c0000e013901d800b0020302c0d40c012a00558a071016514000300500c1c4904420050341640b01c00c02081100c0075004242041c030844250a00301d89919040b0f008040d28003403001c000303000700f20030b0001d451b0000d60681060b03c044409072400211024409450b001a00e0301f1401d80d2240a81000305604555402e5100a000006020070f1170254002400025101d8200e0343c9455200f0126090010014000001d00324003c4002c1d6944042654805a250382d210b0030003010389070f0070115505194a0085071113420b81d0f00016410a1940045201c2288030030b605008215403c10061a10783c80d21420f1a00a500075042d168541c802c028519090303424a9500324483c409003250840134080d42200d888002000c0a091002980001100c40c114a4035081403c65004040100100c00d502484000e1041c42e06a003600c0301d00526400c142c4050 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 431917032 1250 431915782 431915833
    0x30b03011811060d0f0c02070509070201090309030605090109210f09050307030b0612120715090f1106090409121e050f0918070f11030705250806090f 66
    0xc0b1140d0b940c5150515000c00908022040030380d00003001600350103a078048800c83e0b940c4401582014004100c5450042c1850b41e01c44940e00007805408901e680c004e00180083c040188000d03610400306429280944c02034681c02e41c410400c5464a01010419005804090056000070800e03000b0410445c450200c030f9003100c2c8003070014400e20f415035440b0700c055072009160710f0b005803143c0e05103411044104461000768210f01803555a481642c1494048983c0726441700c0c000d1820202e038100082c5c200100524803540011411098050b01c0c3c001034502d1141118840d4803e051440c81400d101007080d41034100c2e113081c0c4860342070032a08949411501603248070729021440610019802d00c0d0748100401941000034240d542c135102218001c1c2807a403061741e44500041407031004140281d009010f454114920310300840c240116660780f290744603075070145182c0b06a071702480b0180219040c540c0d0406000c520060700e0031392815844103952007641514100c194401c2e05510340a80301d1403004080c44 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 431918282 1250 431917032 431917043
    0x3010c170105010212180d0803040c18090305180102030d0212010f06030b01050a210603061b0905030a11040b032a09070815012109290f15030a03030b030118 69
    0x80080801d40812148040030006807c08070038204040040d03500ca00862149106288000b6250b090210105621007032340d801c0c000c20340c035082103800402d4001054030b144100c42d00b8450303404000240100d0950203041c40340d0a1250001c1410f4102000b804103582c180c44600c0c0191941a0f0368440450580b801207000b41c1c00301d074081002c0c0d5490382c4a4a0910480300e154008240382040d10f6805d14200c405030f034004e80d6440d640c0d880410003e00c981c11107815070b840c0b9240c401b50b003905150001ea20745a84000c000c0000c245061804400d40707458208410444008003a500e000400c0c0c1280968150030459095034042d981300914880d00d02070f4003280c09248259280f002c65944c030420030080f011000e41941c184900030150748090043e03410002c0f02c1320002d42c008240980c03982341c551050320390549032400324503061000040031039902d42c400ea030003034040701e94080350f4035081000e0107400e10300c035041c58250042c40743c40c90071b141c1c26170072000b41d8160941c001c0094040070590b4112018607242c00401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 431919532 1250 431918282 431918287
    0x1020901080c0f160602091807031b30020a05121e0f0603011404110f0103090506070318060501090507260117030408152a072003010c170105010212 65
    0x303000c07000000f00000117104040051416645900140c860400f02c05460103054580c03040040a86d03160285110100511446241f1203501f180c0c05040001c035100b0190408048900c00c90203185507000142032000f00540031941c03013a00d184000c03e41c0c2d01c96000704501402000c040b8a0010421000e03881c0781c0051806a489610340303040403046130b03c019100981c03540d21060500c0600d900f804010713020f5031191070503500744c0380c0703410a109440c42e200c080141414680908040850000300341036501048500e0000344030500c1480000d940c40c000c200c045e00117031810002050580361135001600940301622020080c864007500301b03000c10100c101a043d207100c4000100041c90005170031302c0e544c40111042d6424107484400381864070100c041c0740100c009650b024031500f01035000e403008201c4403058210030540307110128503040d44104100188000e406121413024482c9401c1c54905051000b0024007031000d01315002000703515094580e101441c4c141d000041c3c40d43c000541c2d4241d800718208844e0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 431920782 1250 431919532 431919547
    0xc01080106120506280503010b04020a08041b0e101a0a02210d14011403010506280b03070c02100305091b0a0515030708010f0302090c0c0708010e01020901080c0f 71
    0x40035243c081d0076541c024902841c4050360342c40101070054144001500c4249062030b2408140c290b07940c402a090043d07104014804103e43d00910f44c2d54002d420046103000c021790103460542c02065a8040c1521244038024400c0701d01000302e241c021201c0383c0005020031540300c51580342034030410302c0620250703101c68001550380c4a1a10450175464580c05064184503140c801344066403800d034071100440d1150001401003410362500541d0584d0140c0007004207150290200303046500d26050841e040764000c03070603480e100740144840080c100a0042a4503401d00c51070140040c0e100c0d00040788500c500b066a068001d10034401d583c898807010006091031200d0a5801c90400844e042650300704000388008141c5407603100300c1030240141d9030308035996481e01140007001c01d101a00008004240301a082000d80d5800d41c2d580d800800300c8402541d40d50f00700840b28070307164140d4091030340c1d9400d1110000c1410010b60160074505402e88540702190348000f0185070501c03812040a420010070301000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 431922032 1250 431920782 431920817
    0x60303130e19151d090706051615092f06070c1a12010803090607031101021308100c02031306030b01020a06020f09041a090402010305100f0b040303020c01080106 71
    0xd400006100c0c0b5100352410030702041c020380360340034540c2511000c118030030000030f0702081d054446900e50f04041303025800c10b9000d050f02e503251803048404000e40400d000f14000384040c24551842d81c041e2a0340700c0f406204403d5400f82048000070350780b0b1100300c0c040e458241d100301150f41c0400810128104001441c00c208420350b00310200c04d80702c048074100003141c1c1c5070240d00c10300d0380d6440ca0304d40d180e2508801c040c3c00285101c160454642a08280f0110356241c40d4481911034003985030610a03042603101075440d009000e5400b01025091b0b200c40300051065001c5408a40803001030414044c1d42e50540003070f40c2c2c82c469200c1040c1c107034045c10700802c81203120b03038088002c01e01d0500c181c0302c074240c003500da0100b03a0b00058130240b20900d0000341041940f82511510801c1c03032078510004040e40c4c180b8005409070400810181c14161203c1c00280c0000c00c4c000a2005000c185102440842d11642c500c2c3c810341090200b100548254408082217600410450b0704076683e90ba110035075640138410701e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 431923282 1250 431922032 431922059
    0x806010f02070e010b030612030f0f0d020f18040c0e030c09040807210e01030e0a060e0106051c060b031609020d02120702030a02010609111b0703020613090506030313 73
    0x4503001c42c010400c02081d1140d01900280c001c111700f034415500c84c1070003c1000000036094544600da0761041104100d141081d00c00c3c0d54014000e00c0c8919280c0b5020303404840070b0b119907014491180000151200c85203840019030000b0701c0d09940c200304911009800742d8144444018150381580802c1104076240f4104a9003035205100d5810141001c0c91a62100c541c054444d17041c071822100a070200c0070050344140c60f0304c0700d9002460280003104510b202c4c103444107004040500419290440703034084d0701c0309402210042801401280ca1401c07100340d0b14030411920241100c0a5003880702102d801e20780065080c50310041043c0c002011864500820000d501c040015210150207100c5d1000c00343c00300c1045803054115401840d03036242112402400c4a82d150007602200345041641415056100c09032076181240503c001c20305502880305910704107595000039403140e80001e800801004600d54001283c421440500154440404061b100d00a84113500a5540a441d0400140c0380e810103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 431924532 1250 431923282 431923307
    0x50c03190b040b030304030b0f1e01060305070c120306030212010b06041e35150a0f020f0a0309050d11030d02030414150114010e03030d02030601090e01140a0605030403080601 77
    0x2c0040c25048441c0030034110f41244d44160740100d450820460003018000c01c80d940047c3c81e1901340d06c1407589020014402c0d006004284c10150f4600004510500681c0081c000320b80040b02b014001038a040010301030101c0e80070403400f62299048100890005024108074410020420380c1440d0030103024421400103052041180c80000c072001030102c60302005d180a0306040040d40d42d80740c651400804100240c0084024681e01041190f050441c8103a480c60b00b020b5004400b00f0a42002c654010190003600f6078030f6043c03800042c03900d9070710790903074051007100e0321600c183d030700225030b41809403810641c41c400960070307800410045680000d07542c020f41d40503105000d80783c1321301102e07424540b030101070682580036600380c1c0e401800400b03110603540142500918000d15024221800b29499008170005400c00381e4011001c111aa8000c000340c801504400311541c1c11381d80c0d24180343c5918040f1003001801401506008240c840c810030842e41310320341540305c040894480100440300c2900024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 431925782 1250 431924532 431924539
    0x5030c1c1a06011403060f1c0606080f07081204030602090604322704031b0f1b120f061808030f0906100e0613020703030c03050c03190b 60
    0x84400000d400500658403003503240c0711054442c604500090310381c070350464581614410038403c01c074642d60740b52101e001116040c0c4101c1e45800003e502000322044803d4010140b030308000021a0740100083c000e50203200042c01c58040325503c1c4500d0780c80700704100e40119607420401043c00801d64a80090014843c090f01903032800da615400400d400c00c60b080c140c9524280100d9007864228034003407800d2a000c044603030321040c03010109072224442d101c0344d0300c0001d84200c01c0060705160040300f64000c034030500c200e5243e111440b440c0200b100d400c5081b00b101d5281c40b086190f528080c0301c0380040292110001001c030082e03160b450f42a001d4480f40c1c030898489807114a94100c0346a00c0c840b1f240228410b24415440781049440c4110300e02c002049402c1643c4031208000308140311703d6903001101c00d4045d620f030840c3c903554042140c40b080412803400c61800010300700d081503410303802510305c011150b030100002d072640356660080b1302c801da4001c040007074090f4001e0000c8413164024049844003d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 431927032 1250 431925782 431925829
    0x40b0c0a02040e01020d060806010605070b041104050c070c08010204050109090207170a03091502030606030601050a021c08090d02062e0e10030201110105131e052b030605030c 77
    0xe50028054580c5544140203030394001c06c0201c56011507001d610090045080600060340c14240020524041c40b400600304405903c00709080c4503001004c2c44a0385809401480b0501c0c0640190700300c2d034404c0900700c0e12802c20703840026074031030188282da06a68059407040271f95854402480080d4211910030b480b004581c0304191801c02640000f04001c91107901d0101703220b01c040c100002540d611141d08080c0f43c1c010000c001d000d44d0340784212a4004000d0030540d884000c0c03000106d00d00840a5003c1941e80000e0100c0390b136041c1c00c02119449040b008040f2000b609400d40b040b622020140c40b550b4142d110360010511042d4400c2000c0407070441150384680c1d01d03944615454503076005542c481c410314205034042c415075a0001203a00800c1c5204000d2200b0304200d04096169216004080c0c00c46c207002702200b0b4600c080307612040102d0b80040c11115418810176003400d042d030031007030065149003c0c10a1036840c2800f03070048100f1604000c0103449034030300c40414030441d40104101c00a885a51 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 431928282 1250 431927032 431927053
    0x150103032f061501030e03030105090601050705071a070213140109051e1503010e0706050f091c060b030c0307180507051603030504030f080613091e0b090c0114040b0c 73
    0x10040b40d0310450189012054200322900050b040703c1c3e002c003d00070542c0081006000701e44404203c141c0201003880c05654406050410a040031480c2e0440001e0700741d60030f5210004035481010f070126500032201d9020181c010890b020032102e5442e4018a40c0041c00010800b5102c01e40c80182d115490034000f0101034800122038507400021151035440480c490300458480c01c1c00d1040310640e5821600414a40b41000b501078882c0c05240d141e404124030004445110f038560107115104a80c501c09008080c030903074544440070309408a0318070301a1041e91080b101501d00024858110fa95201070b47d2507903c064a0500050007000300381c20280441000310a00c40b840040b1848000390080d07800090384c0c2410318005000315245000c900400c0624014008165564882d0f100b40d42c02040002030b184599113070040188185800803140d001c4401c040b00d090202c12401244981e03031000c19540e03142c0d0403c006540c81c00c484821031806000c188010302488d1010b0004002440c807030001c490b081c152 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 431929532 1250 431928282 431928377
    0x80703060b0604051c02040608070b072a030f0f060c05071104021801110c0306090a0501060e010f06080702280c05040216200301060914060f0f040f0b03070e040515010303 75
    0x644c000300d10304200107942000e0012845401178400306003701000c000d003d0041082056044c1d01000d04801d6030320760300c82c080242d01444000120f60080c070a0100012219000e005074004400686100303044000301e600600e46032003290180d0384041c1031205881000c038011564080d08411b43c040d41e00c0340307003016500350b903040003001d03c1030540000520444195140c003a0940e8a5035000f4a4014056401400310300420410041529818500303c5520355403800203c0c03030907110203035280c4005010700c0c02c58408880101702072026802a41c42c446e94030f80d20814030089114042c6048084942d2480e00000036580400480d444461410108000e401c0a00040d00f1941d41394410112655246495810703220300b0500e0311f034045012511070620602060120316044e02400d0400d11480d81e84030705605000036544400c070700080190445030b500d5120b682c801c1440006523800c2c0c0c2e072031142c1b00880c826101006040b5043e0b83c0d2560b1038112052910114050100c400c104030b040d800050101e401e034050303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 431930782 1250 431929532 431929543
    0x201230c030301091b0c020105030a0e15040305270901270507021b091312030f111e0301080c060f0d090c0f0510020c1002010204080304080703060b0604051c02040608 73
    0x48a00c0014501285c80c50303906600f41c0302003040c0612400c04020000b6170381050a903076000709582c0303000c2404071b105543c080c00d003602d412805468410400620062551080c068091008048030303903004001c03c0c85507094210034001c4542d5010050b07200600c003045c441041514540001e0800082403449883e645c415218112610f20050b40040306220521440c2c441d0044018003e41e0188070074140203c4c8001c90824249014001d002c11641d82c50185100380d10040c454001080704114005042c00c1d080c6088d4000c1d401c050014002e605402070311640c44044904030360b402b200410440e40c0700810f1102c50741101c1001142c1800c00d10910102880d50b0145a210740c2c860742e5101030090400b030078401200034640082d40610003540741034001580000310032a1280d030403a24400d11000c0074804074064031450308440348a02000c180002c030804001084416644240010b01104084d0403c1c003456000b680300c3c1d15404010032628940c0e9510f01c404407007080d40054804580191222070992400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 431932032 1250 431930782 431930789
    0xb0d150605030d03091703090a0b25050d1506050418060306110910110714360702030702010c06090c0b0307021f0c090e0a020d1d16030201230c030301 66
    0x80d03c5c0d0032500100445160040041e00a28450500f10309002854540e24034804500800707840d030402c0072440c004040e01460311420040c40d00e0000b07201140c840103240380c10061101701c00d00d08003003000c8030000c890f486040680b00265601400c0924040400c02424842ca002c444402c2e075564000c03010985a024085400145288040c0c5d280d0404051000e0700e42400c03030741e80070000f40980b100300303030013000c90130740f003242e15106d0107589a61285002825440051101d0082100c604c02e11940c1c190b800345900445150268401034959a5480141c3c1c50344036088000b400603100703415000001c0c0503030b400300c00340f02c0c024041511070710344500c0c5404140c2c2c4140c0e544405a0722007881001245000b450740e450607125524180704810541101824151031802039008a4280d18002a2203464603410386240942d05c0707000780019444180001407100305030780809064001c031511541c00048800e0500704895043c0d641d01a017900c1030114500d40d1076900c4103c0a01d0100f001404031800042005c3c42c042d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 431933282 1250 431932032 431932037
    0x3050307090e24040b060910090503010c020105041208070f2d0e04060603060e0f19240503011e110c03040f0e1f03030806060c01050708090601090b0d150605030d 71
    0x12a4a000980e0401032807001c3c4003403140d410007204c0e10f0603448090944000700403d0320b1104902114030400d84114016400c429055844c101e820036100e94150420750240b0300450880148180145040341c064500721410390200c2d80100c003140c0064801d06010407a209060f0321092058212044e048040703003100315240c00110294844551884d061203003030024941420b08002c040c1c40c20310f00c50381c0d41c0e6005007000c6041003901c002070101c007140b020340003203000388600030003407004200380c80c0c0d05a00c192505402e405255450220382c500341485103112411186c206d20b9210b01d1140201805401100004204582c05100c41040903000300003a00280902e82c40c40f078412420181d80c5e04c03000c4002042c010003440900d800340e00d03000350403c40c4005e82e6098a042d0391103a541390040b0b0b5191140d504040c400c0c0d8a000d0030040b105a103c03180c1e502032500e45060799210399a54076000d0542c0d0b068015103902c50401e103050800034000305103c2e00c158980311000308250b56076100181c1449102e4615401 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 431934532 1250 431933282 431933311
    0xa050d09050f070f0915090906020708030a0e0c090705160206041520011401120c0b070302012301080c06280906030b03010614040e0703020a082d030703050307090e 72
    0x4240c422800000a040ca58004001d00b0380c40c0040f00c01b2410040c850310060b15038401001090000790703012209016040042c0c00d6a03400d181282c00014055140b00104500595100c450340d443e05661450040034036649080c01c2c10a0005070138026100c000d0100d030320050800000511922070407109088820381c0d243e07240039065900803014503a00c090701960701039240000e01d07069094111200b506603000c600d8982d01c0300c400307851302440c190916005603100c020003080b60410154150060b05060307581c0000c500070b00582000d078841840c000c1c0030700c903040d400c034101d46082030502c400a404500101f0011107072001c03001c0c9080c6040808503028100241807500e0501c0041d82501130302c50003090550003081020b213403520144c000e24003c0b08261240740c0b1408111508441085100051900246101e50b011340d02d0b100d80c0c0e60740410020407203040380544ea01001580c2820610008401514003031450107403180e40c1100c00380d100820540038042d42c0364020540c016920103191181680001c44413 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 431935782 1250 431934532 431934539
    0x10f02070507120201020a1b05180103031b1205070f020a17150f0c030603100c08061801080a02040b06070c030302030714030a09090e01090f0f1b0b0a050d09050f07 72
    0x3401d28101e5000074010009900e003c50050b45c1c001507000c0e0003604917004490390701014010320342d01d42081c1e00441d481070340c09200e03a00c1107140c000400e0484e1b2094030341407520010f00303410a41211181c4405800e6400d8070b00120751840c002d03002046402d00c2014209401c920301c3d0b000518003c00384e017281815610b8a600d00f45000800c100c3d40c1c90610b03070b4060303003011440c0801c1b01c01d2a9440c0141040c80b03191012003c84ca00d51010011003030308048003401441000e180c807400400c1000101d400601c5a44411100709205c41695a000d0503100101e01034080143d95800340006032100d08281900040c08200c0e04001c5880700010300c000d14070940c051a66100c80d8140300d40781c00025807408241e60020005001019001512801160b90460000c120800150231260051107244c001a0085204184007401c114903401204101d40c4642030ba401c61078021840d820400031607015203964610200b010400c81d600035400740184881403800440c4c1080e0a56901c0e050941e41400c05980d030b401140c091 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 431937032 1250 431935782 431935793
    0x60117071b0b15010c080306150c1c0305010f0e0a090305090330090108040b1008030a082d011e2c09010b0102211204141015051011010f0207 62
    0x101e00e5403c0c240381503003440360b4940b911080c922000e0701140c8100c90948044600e101d04000340c4004405680560380e038100020070f8a42824900180c2f0400a45040c00228180e9001065030050382c0c014041a0b49568400e00745500600c80ba03d01601070003014454a03060b82d50030800c0400807241d11540392200010200c3c9440f0b50a207984407240c40ca5014041565079980c0642e08550054204690060f15107030402c80903902e641c90340110310a0b000c00a010a44a9002a149800344802c901c83c022004940304415248802180940104100c2080100303c600415202510382c01c2820740104442c60340c41d0080c0d00b580b80108071b60316040d04940c009815164002d50410741c41a40c1d40024826440380e980000d4944941601400c1001c02d01410083d200900300240c410751981245110418101410414200031341c04442c103180d482410400f010b1440c4e94011202c412181001d513008241c140381c10091103408890744201000101049000700203424064400748400713102c0300581e10b24080c10308 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 431938282 1250 431937032 431937061
    0x90a091112130206030a05060d080307021b04050c03060904060f141e04050d03150807170d1d0d050a0204050a0516020604050a0813120506010f0905060117071b0b 71
    0xa00b280e0200c00d403180c4000d6140c41086941c40f4802c8480041c0a0740e0b00c2001541d018a0030201a00303406010040020180e000580110008444041000c0c036021400420040d0340c02103824640d482c50900201d00c0c10700300405c00c076410510408001c0313100683c0b2580c01044400010036490792260420601890344180310390506e00040d9180600100d01d80303521569910142d04050000300341c0e61300184450701c800c1085141c05028580c0548030130700c1d6682035540c103c144152894a050081c041019080b070f000c1c00c00f07105400b00c0481815124448138003044003074910020142c07418090804900c0c01a40c9a21a41d07204184245002419042818a8621282c080c0d5845010342d44440c0901010400015039542002d80c420600f6a9a00e140070607030080c1ea601e944190400341400480004029001c2002810f803801c41c4c5030003941c99a40c4076250207075a02614614003090500b155002b0b800042c0c000194015842d05007228030b045410000142d00300e00c1c5038151a00d0300c03d5000d00a081c0d840d0801d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 431939532 1250 431938282 431938291
    0x60907050f010e01092c0a021e04060c12090e090a050d0f09120f120e0f1039060614030303010e0a0c090509040501020c060c031902090a091112 63
    0xb0b00346a04003c120003e803410440c0d0043e08685112a041c4010f0070701a02c9082101940c0903104091038240460164081d400c149078501e00442c54964011600c1c0450702a60129803840e55515800c80745a26681c680e0201c90300004108407850034003181c40e2131182007180c0986400401082c2c0d41020b030804030f0030001a0043c007420002d070000f070b400c2c001d43d0141c540010346170b540d040030350f8440e100d20340035070481e0040e907000303003240c040150364603419400404146038180d040c0e4440412110110401c10034500189804001c600d1940704001505500c50074031b01702c2100043c620501c100d003404615400c0058075000c603036503615171606000240480885000401c3d0580086040d5410000845078501d03001b01112192a600c19100704494800c84015009110280000c1504d0500d400e08902070b5015001c040050b12880c804100500c80d400e085030f224224a0000a84500017582503034040c0d8009104581d000141d5207000c04c80100078840c2440b14514908565607920030008100c104880050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 431940782 1250 431939532 431939537
    0x41802131203020c06040f05061b070e0f0a0606080a18200a0e06011e05040506030a05091e1f110a0206070809010506030c010e010c0606090b011101020f04120311060907050f01 77
    0x4200411080d1701030801c15602300702d07139641d141c5003602988131003500100640d040350322607201c0000c2c10102c44601e2030f0051840b03910300480350b40c9000c151001d4603a503100d1040015400000110724944507070180c2d41c0342c81c810f42102c8091015840f141c42500c81542c0d6502c01607a0f2100317208031450003150180c02400e4150000f1501d26201c400680103a9500c801c0c540201d049048120301d0307a20400454002c1d15000305220b0f100d080581c0300d40b009013001c442a00304c62040100e600014081404043c0034800a40300034003514205040c207480e0400c02404550465468100700407907610120f010380300c5103030b035076000781401d240c51034009140003030242200b265a49403006000c4161008550004603400038280101c410b000318004981c280b00207103010b00124500880440c11200307039001048500c1c0240d0b03811040c0a00c80b01003508038031514a90b142080810402040b00e00800340c80100d2032070103401e0900d140c03840b403664a42810b1084558010580050200b8440d40ca0004821400d412003071 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 431942032 1250 431940782 431940787
    0xc030507110f190203120a0c060b040b03100b03070305031809070801060503040f0309080607030f1112180f100c02070f05060315040b03011a0901060c0206041802131203020c06 77
    0x8800300d07611190310070f0200e031480c46040071850554908018808014506414880d42c0d1074541c10014403d0840040c11100c0034200701403124185094040c042d4079250040280a131403403240c07280c50091004450443e0940900d01c0d000004c02c1041c006000b071580102c48210828185808011500000826000038131280c0c0c40188600c0343e10200341c3c0c2d880f550003103c2d190710002c18103069944000d241c0c031000003403150300304002c1c03504d80c1340c0c104268642c400b05043c403c10408440e951424001c800003008581e00c2c0c08001050309440b10f580201d204825020b90301c3d0700c00841001420444140d00074000140c84820851126904124050040c44060000308003e414400060f43e544001b0f441502140e40c403540725a515a59584003104091004008004101d991903a0740380e820203901807280309807145000020142c0c01121208911a802440d540c982070074482105102841111614004c50f424000300c1c070a20420b0541d00090300056908084010682c90001d10b4070344c41003201e074000c03d003d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 431943282 1250 431942032 431942053
    0x100f12062f07050c0a03120807030209030c21032208030f0a0f18080106090506060405100c0501020f130315090c050d02032103100807030305031b0d0c03050711 70
    0xc5103484201c1c001000c070041d0352040305003480b44c0381c60101500c007980460001400002c102416140b000d503402e054a13640815602c0f404245c08a0090f000441d1b016041918800f2a034500f2074540030f42104013107140c60103ea04003007620314603041540f88900015460b42d100801c00c24a1080308000d16101000310b150800440700c44e03010340241c084039020300c012101c2480c120f6003d0030403d44600003840342e20148590b150340c103c0c00f03082e1074030684c5161403816020030101c1c01c00c001146c0a590001d0302c41010140c0c400c02c22948049040740a85036558280302580844911000608c1600c91006004040b00e0640c1802c1da2007410f00b80c40400b00030302d45481d1900148101e1440340441f44212044201c0840358000304e0b09000c040300b07403401d1040b4581b010130216002c032005180284070040650380c08549646016030b83d0081800082e010417018000103c3c44040401c042e01044500105c0c581000148050388060b40c00c0404a10003180e281c50400078007640c003000b4075461800d004010a4247d41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 431944532 1250 431943282 431943341
    0x60602031b010507090b071a16170105240f0a0c02040e06060d060e030c0a0b070305060102160b0904060308191b0816140312060a051e010305100f1206 66
    0x17461042222007480881c0620902201d0000745030100021030180c003003442c020070344454071598406a40045807c440c1040c4101c248081e4840c107071038005c1c0040404c004010400380548082e248180d00c5c40c00b0400024100c4d40494004e00b041d200d0b581c4511201c80c4052042000b9590030382403003001948050104505075a45202c807401c400d4000740e00159411054a015007540314a5400b052640702d600205820495a003820a10903451750741c0421031b60311740500490316001141110403c03100f0ba03480030710044040000508582d400100006290350360ba543d8550f0540103500307046144840004040c500d15044094036654074000c46c00510751059582d100800d0780503440f11140011a900030403020800d8291502c40c200301c2c1c00b001c407500c9903207460039000b03100003c4459a01551030360300c00280360f0410401102000d00000c00502d10740075100011130080100074917109a1141074100041c6000360b8070704802c0038080200c1c58200714421800d0100c16614a004850090428030240316003258 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 431945782 1250 431944532 431944547
    0x3070b0f0d0e0705031504110a03051f09020904030201020d060b1905090d08120103030221090d050a0615091107030804080f0409051008010c0f0e0d060e01060602031b010507 76
    0x41d84002119001d840c092480c00c049034102581511039561100340e905601c15000348a03e00c103004031401945048240f083d41705ca00c4c400100542c0c0710350514811220740c40c03c80140f0071304081f4001600142e640015103c00d506840c01e5001d81d42c001b402e29081c59080c001e440c00b92030812209440d000d2a14960f080c030030400e208002c204a00404c0c0c0c00c4659032102d82812082da000700030710b41c44000e0a1964650101c0030f10045016210700340b50052420010b2007900404400960110304140d00b00c401d00c082002c011500329000c0c020240e14100052092050001c10b034016a596011241000907140407200301c4448001200710a01000002a50120500b64040d900101a6803101000700305031486001d00c1c2c0080c040c403030415082004200c00c6040d81c104640d5504001c0c801e4101158040e907100c1d00580111001074503103509182a82002401400524850f04001881c80c11010a460031580c042e044100140c000040800841100102164104100b48000c00403800c102c100070b0000c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 431947032 1250 431945782 431945797
    0x10c0e1008060306010612180305041d0609040b0a0207141614030604140a05070b090a0905090a060b010e0909060103290a0f180605071b08041403010605100c0203070b0f 74
    0x1c00721f6403401c4890348503a04618008103920280203003000172864080d20642103405407060704522801c0c03601b149403881c07403064050440540703494000c0c0c03541e1700e4182030703aa8000c1c010110241c08012400000307009038103001e0741110900c040c10421030b0407000001c2110055100e00e5200d1084509200b007558040b4400d500030303503c01c4000c0e07200c03544c424800c1d0030404070000241031402039803030003d010b2059200a080050044407078800d0740c1e845000c50011940e055801001c6a4482c1d001c1200180b100e174012000c0081c141803014441c0341003c0010456101121802150b40110b4010010030180400f0034010800154500305210a00d1751400341c110b0703004000044075620f598000041c1d0704268003404610445a0300840f82711544d0800b0f00c060042a2164000a100302144a108000410f503003da1300343c0c8420110b14081c5070284041402c2d00200916a15550340c5c00e0000e0150b60b0008145a10001c80e180d01d07002e0b61060041504100355139102c0c6400300c004001071b07a699071640b030440d44003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 431948282 1250 431947032 431947037
    0x60112021e01230304030215040f17130b07060b01030e06161e0e0a15170606220312030207030801180615020f0c03010b010f0c14010c0e10080603060106 67
    0x11481d40100490380600d69400e40c90349071030344010241c10f11401200a600ca43d010350211031075480c0d034690707042c414501110702a01e0321040160400020741c0c1b5060000f1801c6680303c60505080300c0a0b1081400c000300e40c060140464001400020401036000e41e0302045030900b0104840301001c2140f60725101d00810690f850480c030150361500500a16041164000c0900c040304107454098010300740784c01c0c0b03e030348034812030214000080c400143d0b0f003032140128065603031000340c10f40204070000074040942500e41c0101c0c00e100c0d442080c1c180e900700b9103210800074510703032016186050400f084500940b140041600400c4050042900440312a0442c3c6201c42401c01c05000c004265008007019080304948014052840c120325a000501e00f0b03003001d0640130f07200c4c4400c00b02c08143c201ca1403150341c0c50100741c2c07030740350225010300801849a4042c00b035040480c0813101c0143c2c60b821107120484071000310306c02e0300c041046030420003911040f0401a05001400b810000c000a0b40c406052154004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 431949532 1250 431948282 431948329
    0x90a18020d030c080a0f03051003080f1c0f1e02040e010b250308011a18091305060c1c0b0a050f0105040f29180103091103030d050906011202 62
    0x10144650100e5441607045220540c803240c2600700141800d0100c6c410000003414003001c64801500d01d6214412254000400383c0340200300c510700308942d000604106440b028116110301c0003070703050040b011000d0707504c0f01c0092001a811603c000545c041d10300194024070620061010000074041d60b0b05403a449400c07e41c8840d0100950b44030310343c0741e9610308800140100700f041056088400343d8142d9420b001d0803407074802250009005400360380d010b00001c1003103000485881c2421103d41e904644100082e0008460310385403503203006015078059010110005a841c0d02c0440c0483c10b50864000c0d1100340140b400450000711510a00d0096034400d00102c40000d055071b01440880740103080a22000000940d101015200d6010078815542800d26516100c0d40300001d44089034404080c040100038580c2404004400070501c80108070f460f4000320210000340d58007040540355850703030b03100003203100d04d01131607007508000040c2e114000c0c41032405801d0f00140d5602909075243c10440f444ca00303 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 431950782 1250 431949532 431949559
    0x2802060c04031e1a16020a0c090e120f0d0522030305060a051003061706130b092b030617071e090207140c030c0a0501050d110d0902090a1802 62
    0x201440f003c3c84001d0030282c411441664070b81e11103810318030501e040c03421080310422101c0c0507600c500c100807004000d40c411a40a00c04003025500c00751a1072458000c41d8010750707406203003c80941c400d1201040540d0040790345000c1814600489620207024155420703840e00f244a100c2495060720380007010f043d02d5030001030580d15182d20800040030010b103380c10034003401c100500201a2401010031428141001c03000031007001417101d0040c8901505069925004d4643c410320900141c14200d441c004d07001c60410180f41416030005c100d000740950f20240901640242c00c941041e44040d01d2040d00450320f0420400100380902160200c0e051880480c01d030189035100002d66410809580d440402e0040c1801245880200030003403c000325070024001c1400c05582d180d80d80a01d0f45d220741008410303c00c5503c0780d0f000c0c21652114050204401603a401008050b4101504d06000386580c0c0c01410190301d445000b4a40000c50000100070122055031401111920220043d00640e895070500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 431952032 1250 431950782 431950823
    0x403081b07030c2406090609050c03090307031d090403110f01090809040207020d06181502121311090c030615090f0103240f030c080c01080402242802060c0403 70
    0x2c1201c81c814000c1046584031006c0700000c00e036074094041014541700001d4001c080901c1201c0c05054414002c43c2044129601103c0b80745001290980700045420b08070302c0760300c0c4c078084240070b144039460343c402c502080030b150341c0751a1130342603031940a0b8142810b1034045a11039080b40c5800d40291005a5501c455001141004d001500f000f4406490880d4090003000d4284140c01c030301d1304c51303203280414076400c864141c160700500a00c0100744554074042042e500305a608269a40e1090352142c81e923100b0800000c45904080310f00c2e14442500004201c0c0758600044580b41c0500c40002c80b42c01c160a14012501c0140e800c1209410b255030b8190003005070448980f100c521410b0140508007094440c10030603000381ca50312044400b001890b10111b01c02030003046c5941424010b035035070000c65441d9000c0003046410440c2c03414682440d00e45442d00034991500421810306c800038402d0308040d58402e159252190404803204641240c014462207582c0c80044404036074003c4508602c0c180040c04c407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 431953282 1250 431952032 431952083
    0xf0804030c1101020f340e0a02180d0303060311060a23040e0106020c0102120f070b060f06070b0f0907031218123903061d060403081b07030c 62
    0x404685d0300c1030310350701c641c0404081080382489240d00c0c5140c035600c0a01c4410588500580101c17102c1500c0c00300020102c902d2580a00064480203501c140484200300105401001202064000a840300410f00070301c2342e00013080c10440b83c1554168036103190900024480800300f90f66591141d41151a00d550b0605201500c024007a103281c05012940d503035902965030040061081d025000d1034101d280d1640d02e042c1524400000740440510b801d00980e1034001d122001080c0c103907c040380c0e16504000c3d03103075030026058461081c0c008901504142c50340b80c0c0702140040501100340e008140c10320001c0c00c444030388100440581018440e0709000d580740d0072560b0342504640b0035241150301c500c0603c01004a080c4040b10041c0b070245845020082c0c02c0003040400d920091245035024003000051303901c2d0300610902e4215007014082000598805090400c01da8050b0002503404007449809000582c180b06031024226480e46048455034001d8100c04081341e01904003250080e008441d01071848a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 431954532 1250 431953282 431953303
    0x60c0a05060f090d0207140d03020708011a010306090b150d0207021c14060f0705090a0f030f051b15030601020a0f030306180603110402030601090b030f070f0804030c110102 76
    0xd81e15203280603001808000801c998412041c4100140e62840074008103241040d03441845549010b020a0418811000400c200850851003109000900c00c8020710884a440c4c01d040144030302d0000510005050350070a400812010780350003280140c1d6030718080c0385400d450500701d0198445004020107c024000c0a4000c0d40100b0001d0003d564090702c56034842d4494407034106940141001400385079101c2049075042420052200881d1900d40240058500044000c06881d5190784440b640c0c108400107920491340c08240098806c1044400d00030045180c220500300300c4907a43d8000001c00042c82411007400ca514004040b0348103910030b104e07140026400120340000322196141c02801480075104000814036600f0300a4040c540e030340103d108590b0445501c0c07203121f07407a408000003948040c01040c18070503517040004203601041d024610941c2c81400310a01e80c901400040c219110702001c0504001455080000103034005040e41078071504101100e0b5102c50400050f40b40c040345e150f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 431955782 1250 431954532 431954543
    0x12010b0616150f060312080601091e031b0f060c0506060108041406071101060501020d080604051503060c1804060e0a0504060b0d080d0b0904120e0105090d11090708060609060c0a 78
    0x40504074210042d0002d00c01c40e0311445480721120200a0200c0f614001230359520b00082400c20204000b054042454189407071405203c0000350b03495852101e591807442071104483c41e0a20204103d44410425130020b02c0c95040c0070000304019920b540d11510300519660600ca1400301080911001314070400392104200d040720214145030354080e00104503000b00c4070144d820103d011034154400301b07c0e01c06844d11070721a900c854840b4001c00010704001407803148040485050310308140e80401001c2c0c0164004950150f9031075840d11481084c01301006940d0255007052020803140030f490581c594442401440011140c9482c580705024202046046901844d41202d000501c82400d000741010704000c402081020700c01824824020000c03030300070308000646100010598014a01e00380074081c1403412521744100e520010711044110241a610300e0711201000b030f200c1c205012401e0b007000080c28410035518280c070020300c240c46099001c0c0e0048002003210913060004200d20300b015503000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 431957032 1250 431955782 431955791
    0x1207141204020406050a0501020a02060d021213060f0204061b03020a08040b091305161d1306030b090105060a0b18040e0a032303060f13150512010b061615 68
    0x40960491080590341640f15900d410300c00201d500c0c002502d041254010b0300604042e00c0e442e0208070302da07001411459845502003008816803030000c06003600c2002d000c0c007a204030300d17058184681200c0c90307400300c8044103204200902c0220340204241d006a101c00c0d400c14200e50701407800301d04101c45600024a11301004c42c0100300741061320040c10150b1010755400400e012503240207000c1d84c0e02a10024811030740b24105480f0548aa411002c079400010400f0312481d4001000c66081c94400303c10301c200130354401d0180100500c1d414030079080700d01d16009124030b080500001c0d104091030310819031105400980c01c1c0c10350500d2861740e0a0984002c104111486440c0d425a880319400100bc030001503140000e018001a4050b0701d400040b03072000498196075811040c0103840f55204969980207500004409240d98580030f0f0700113404401c041d0100707843c682801c3c030040317410411409281c2d90403c8600c2e42241c403010152410400300280044070b1020074181564090003019a281015040 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 431958282 1250 431957032 431957047
    0x4051608010b0f01020a0807030c02061905070311160e0901140408190203070c0506030606040b03190c0e0105250c0e01030314030c030601031a100810050a0b120714 72
    0x66011660021003902e0203c0c00c0324080004a8544c101a0401840700c4030234800c040119204441400c20070748041c0001d403a006524245800c81c04002100380d0010b140022440105503108500d65041e00c0e0b0500103020030340c403807401c00724944524060319561966060005240c2013094103d1881e00c1c100c0740b8102d08504290403c0d088079445080070368079041701035060400c2c80c1d10000c00c070b540154100000c40540781c10700f010001300e80d00107003405912200520012550008400086000e01c031400c1d00742c4940a441078860058031030034401e482c01e010b144402e4034000d036000011200302001070085091314000380c5182400403400748101410150130f5110100b4940e1009800d503050700e0085d212001d0492500c040c615030703440300301e44460301d1600920110f0481c1d4001d0308a04903104600300c41d10010139020001c2034607500203003080c0c0c00040c59041802607000c0b641d02d0b840f000d041c5c282c80e0200008d0401010380d103a8811281c0c00c40006030460002070056110308031034000e00a444603070503651608c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 431959532 1250 431958282 431958299
    0xf18022106043314060a0f051215100302040501450f0902090a05060d0b04020309010b0a0509061818010203040b0720060601141905030108100b0f09040516 68
    0x50440f12250540b451403010071070201d5082c43e000b507604021300f11454000e51701c200315401c06e0310040040601005106a02c04002c405848612441e804a00280060b60300030400c4030038010f070000314051520410043c04180da00541c80c02c04a031442d07541c2000303104010031011b45202681c506144a003c0700e104580c4a0300303207521a00480304100141110b84c0d8031144100b040340300c0c0380d0300700c3ea02c200c07105410420b90030150050100201c0d01d6000140400c01da6020405036030085480300403a075500d5010301850310707100718637002500c81610510b842c1e1801030040b507029464800400c404408000001c2c8210500030800c5101021101c025926824240703052101005c09840e0000030a510056054074414901407841032000008d0091045486070001540c00c440018404290260100204502006141e06610340b00030307255650390b5030350714003201c55081103c24050300c80c82909003941d4408030f5682000581030510121000400d07900c8500d442031805d021424192210b200701c03000055180d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 431960782 1250 431959532 431959601
    0x9020a0806040b0601020607080630070803220f090b060d02070b010e06240c070302040905030d052401050a0e04090b071e02060a0506060f03010f1802210604 69
    0x5901b80c0807110b1b65115200140d170124421206103400404008a01146000082c41501c0100c0e5040c80d000a0080203808a030501c0680d80000e00b803540b00140910a80000c02401240982e9841d0b041080313500f000c1d04082c3c42070892003030915031611807080b071803103030b0340e15044540031070910804558414240c90304901e01c4109105009101c114900017032550704080608020743d0400d50001d6030b40d04440070010a140d00000042145440b40c0f120100058a0303e101e105521801240115200c0701480c1c0150700307691004050510301c0603040110095072401c02c4658002c0c04003401c0854403142010412201105d440341e50341d0303000307080566000500c2040580705024007040da8440c4604080f00d42e060480300742000c40280103a00003c00240d07a00115030290350450002040585012400068040150400e1300040c00c15090580c1c108020f40103039008141e4500303441419404e00202d4020b00d0803154018080c00c00c00b09181c40019550369560740030400208880c03043e580c0090b641c100c24042003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 431962032 1250 431960782 431960791
    0x3030c020f040216030f110a05150c04180c030207330b240c0d02070603050106211a03160303020c060313232a011106070309020a0806040b 61
    0x80c10780d58002003580c1018022600c01c00040030780b58200d85081d560071117100d2854030031041002803200d000740c04d010040c0402c188060143c0d0042c80502c001000c410000d14000c0d09110b04460104000c0181c038508602134000c2640d0644c00040c02c0032810342c10b50181c890f040c0000c0c6035091421003401040c1444100750340c10200703580d0000000e4038451669085075030f02e01c45103074050300340c10420904104801024079420914807582c2c0c20642602003503890708a503882d008025800542d0140319041e490703c501401000c8900c0d15200030100a071460b01603407013111203800c0641c2c441c2164040301054019407600c410000c7e040324043c02081c50380003051100d070b001c05c400500401c07004525138034148055034021410f0021507481c00400c0c3c0c0c0c0b103a072150066004410450007100e4913250755081400158021040d2a01403120a01c241c0a4490710318031000c0102d041c000013071604400010000b1700b96901250300c1c1030001d0010303010300010300ba4058640c402c00283c4184820803082042c0c4410841c0903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 431963282 1250 431962032 431962039
    0xa052e110c061303120c03091406010509090c060406030203090a23010c03060b0412140d02011b1d100c0203070810060b0403150504060624122a051303030c02 69
    0x46848150403050100c09143c4003400003000c080350144444459840710740b424115080000d601612980d03401d122841020300c4201d11341000303004000c83d091904056501c03161400107840051504c00001e0294000c0b80500d01c101a030120016405100400811141607046020515102d5880c0ba5004020b01e4560348951113508250000401900078040e0f1419118032500c5142490b040208030848880005415100e2641035194414015028400c0107440c524a40c004204a28100c0190840712001c1c1100c00400003d03502c003110029140401223180081100c0c0400c282000c4c10045503045403000f00a50f050180d500d00040c01880007448200446415078103200c00c40d0780358840441400303248405455002001d038070842c500e045910095001744110720020b0000d88642c506088a100d507644150142400d010003044503400c0016054894610f00302400b01c0c13008144000e03110580c40c036840c8170030b1106410f044440360150f016241c1c4c1c601c400040743e03003003552400c0c0101031100380c0364140e00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 431964532 1250 431963282 431963293
    0x921030f09021c0204060302090f04030801050d081801051b07080c060405032113080307050c03010c0c030c020607050f0d0f0f1403060f120109030e030a052e110c 71
    0x254184078000da0005503001004120150000c1011042d8041c442600702e80c040e90f02c40e000300040c1e481620050144000060594a900d0949405848540185c100511481e00402d2940001c1e0f2554111840e40c1e0982940100d014800c0700142c2e86800cc441403200380c0401c1c444d030760400c440001281e1040780c21210449001d0854041448107034070442c01000e07090340003800300c8400c503540c0410107440d03400c100c44220326010344840e203d0700c1d00c00d403034110600729000000c8601c10b100c42044a4a5841d0044000300425100c440c0007400c2c0391000d40d401070502c00e000d8904002e543d40c8000380d40b0f4082e0403030207980041c4000043c0390384501070350071a100030802141c82c14008620458500030384040d191034040030004440c90740662900020031031540240b13041c400640546401e01424002d1840c04000305125031b0310f1501401c8010813680190199001c181084007145000030b00c1c3e00d0061110081010019414040001d08070345010034054503800c000c581050f202d0500014528444168290340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 431965782 1250 431964532 431964551
    0xa060e1b10092d0b030106090b0a020f01060f0303200303070e06120a1b08090607030e0f01140109140f041e1403370509061303140705010f0c080d092103 67
    0x90130b80020b000740070010b202e00c20305000b100c060f032004012502170f41c0100d4610400300740c445030a40700942c01c03150081043c48001c104140c2c101904617807201d52180b0a203070329808028280d0f62400002c02410401c100355070707605001d444240440b01c130304008001039051b500d0081212009000c2e10325030103170321102020710301045502c140d141358001e0183c000940211b403a054012009801c01d10308005550160843da02648003091281c0c0011011101d0301c84074039850803a040d02200c0000c8521800800e01100b080200042d1940441d80564010841341000169501180410b42055801010b8840f1710004089445001000c3d06414112850b01880780482e0074424080200012a801d0124901d550014119001c0c501034150403002404e60b40c00d04960310001100b12030310340d005461007604030303504400031801440719802070714080c00c0c42d02d050603804a0040141130290303005007600b1400700d420400c0034290b0300700c025110b8102c007682840c1c40403909a8518085811442c03004a4507200c01074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 431967032 1250 431965782 431965799
    0xf18440a020c060a093507050901051503040b07052203021903020907080406150b030a0b040501030f060905010912051207020c0121060b0703020a060e1b10092d 70
    0x210844e0301540d56414803640340003243d814040042e920320031254441a92244256091206110f9980c002c500800802d0304d4002409490f07041a045070b03003e01540030b00d075035409039040122500b0640c821040c80c043e41e80e4800c102d90038040d95036446034801c0d0b41007440c02500d13168034000742134900880711450114a01e074040d9607074003e0340c4402900a0444400a5000c0303009280c40740e0f12600510010640113585d01c80b4604110703640c1c01035542d0038804021b004103620244030f40c00c14150191030030000740d41162119880c1800b070703280c01044280c4401c0800100070317003904100e48041c5d10a00c0145000344809014003a50418005040d0040050340010200c5200145058a400060b12041d604140260302c0c10302d02020b10b00200c0307031310752079400000e625038204004001d118080d41c00381910001c01c0ca000c03c02d0340d0000070f0840c895030002c04560a9a0b0782d11050b44500f0b0301c00c9860310000c41c154681960720b60a241c0c80901040c94042c00c54000300700300c05120300307040441300e103850449880d010030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 431968282 1250 431967032 431967037
    0xf030f0f05040f0902030402010c05160e01051527030a030305070318110402070326010501021e0c010c0302011808031f030809011808070305010f18440a020c06 70
    0x40e4000300162a0040003404d0890f40119081801031500e080890070385e4407070502e00030710020405c07141d0301090320800c440d0402c840d406002d004102c0e44c80c071001c1c00c03040002600340035a0b580e07208412110b010007a400502c4004041110201a0030b80d40b810700384d810050001d00d000c48070305012a04060306c048401900c00d01c1c1e4078004d40d000d400381000d030b80b1060074040250012007003103041c04000c8800c24107800030502c0003000021811020212503040034002802d100b90320b5003420544070344459040e5003102c0420044941a000c1c80c20040032029400c00b00e0140c012845120341c000100c941003414000c1500085219803001810300d03600c82071001004281854074070014010000034040050150f00c690300401002c0900e010224021b5207a00c2c0c02414800705600480e204d0303644121001a4203900d00945268181c200d0841d00d845c1c641d42c03a14070503c1e0035099445204880203001c20a080c00c19010305000205050030b81614013003020707840310264003889141c3c0240c400c0205041e4145000000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 431969532 1250 431968282 431968289
    0x19060801021812070f1d071110150905010e07020f16120606170c041109030309120f060c0a03200912030d020f07050f0607091202010903141c08060d11030a0f030f0f0504 74
    0x2070508484202c002030041442d61710000c1201031742480040c0d0bc84403401210301130b1004110030059428a044041d1407c0c2d40c0c0d090000c45900030300e20140b0f000001c10800d400f25001c0c1c1d54408200c480c6c51521000404680c1c100c0040618035071440c0e103c1240c001030540710f51100380c5041004186070f40303910440b80500c49010364141d00410848160307003803440c4101003251a4a044914920b203000396281030180480d012100c0c0b03800800d1048403294140620200040100700d07803501800c03c004018810700c100c091050041c0001101c1c0c0d440102d00300121045154082d9046441e00d038146041f402d00ea01003d001c0e2014400c8003113420440ea808281140a211262039407030394207190044100401c09907580c10ba0601159440000100e40c0e515800006000c500b009414400000140117005071080c042801c100003000082000c280c485054a00c003040c0c10101596031082502c000070700d45100268010860031180000c02c04041c1c0120160f02661074545032b204c42c0011544040315140034a01c07 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 431970782 1250 431969532 431969567
    0x9080c0c18010b161415041106040605160c210b091603020123041710090503160f0804060302120714090108060f0919060801021812070f1d07 62
    0x1024150b091041305285800d00d2103030426002e52450320007401c0c100408590040d031000a0b2204000070000000060540d10f10300702c400070b003000e041000c01030403805500d0204161806d03800550060003e60b51140004108080880001c003103c07412803c2c1508001004443d100025008120a000c000ca07105002400d00c40c03ca40b6440c1c916001150380401042614100c00e14007111103181902c1000141f01800c0c540c21b13102d8401d410b9a5503545411b0708040c010030325528040082000440100481d04155080143c041255440303040c81c3c0060301ca5910300810456000030000303100c41d0150040c0c00c40b0401c80c44000036a41d22138806840e5000c0920401d815600104400519903000309005034201c1e10140116541c070741218003040c415003040d129080785c00c1e001e1840c418107014900942000c0c0099100035400c1001490081c4001003142070440c1c440c0320110361640c8040810044000100701ca0400c6541456480c1004903504d124102c0b002c4426140600096400d030043c00460148076a01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 431972032 1250 431970782 431970787
    0xa020d02060a0908010e01061d090d030203061503090a02040c0c0b0109110c0313150c020a0b09030c100509010305070507032f0706090815040c06030b0409080c0c18010b 74
    0x30340c01c01a80780d000c8a49541800160a0f0200f4040c2007441012101c1d9011030000403801d041c0b900d002c1031040a86078103c0072288400411003095804101c0702d00000d441d082c09612600e0b0399000444c0c00c0700380c51110704580004001c0042003a000551220064000ea40401c4200101c2800701e0b00c1b41c00e550000307000380d4901c000400020301298000d50341c48043e00111420325011030718090442c0d00181d100002286210824040f442007503814140c44070075800c1c03000d1041003590100c2d490101c5441100d0121401180282c12610240065108820001c0088a401718490005001c940007034806d98002454200083c12240c0070b1000c0f20410354040d229990001d131b00e0040c03420704007400441074035000e10305800c0c5103061740100190400b07006181c413220341540c28156140c2c40d110890200003295000b034803c5c840461190b40056040d50f10501d00481d4610410012502410b81c4440062000400142c00300200c080816181200c0340c040355260720b00f508031a10071098620a01804001c40300c04c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 431973282 1250 431972032 431972059
    0x1614010c080a090320010f091413090b04030c05070f0b190c0b0118050f07140c010b150301090f090201080112030903060219080703060308070b1302030a060c030e0a02 73
    0x1402070b6020a01e0200303a429101d698034061001c0500a42c690750310210303030b9072400e5a0800038602040302180b40c4411490302e0300480320344c10b80403080c106000300c0341d8401480172241141c0181c01a10b40012176100b00341024540200040d4100d941038901d40070741c52000c54285864141d01d822928a065100c1c1043c01005000c1841020300ca221010b00c068030240d400014401201503000b410306503907903005540380b003541c08185c510003481c1d0401070794541c082011032604101c119001c50510b00d4200e480e400015901401002a200041c3e40308194002c5491584003080040d81644d00034141880800850707003002082e90181107000340450305160060090411401c0c02c90f00c400e0080c500100182d50701c0d1a0f980c200d03480400e242030307003c9000d2000c2203041c1c0c02c0048603030401c1d40ca1604010341c600d075480b100424000c3c05d2008101c5a0004042140050721070302540c4681c1c1c0090640d085c00c1c40a1800341c004014011440c00802d0070070555000c03107400800c40c0d6280c01e17005004103030103c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 431974532 1250 431973282 431973293
    0x10302030a091401050702070e0405073c090b030604030e0f1305090a050c010207030b0114151227120c010e0d0201091a0408120c09030f1614010c 64
    0x400c8007268035034440074000400e10041040ca041d401c04000050a400c002000074200380719038000744403003102d406c103000001e10001174417000c03070f1210881c106550b410b1035014075048820b00040154141d04030b41610f03140c05203a4605080312a000d60412001e00081c081c951101d00031500035002c0341003a8003002c11424024130050f0081001400b1061f0082d036845900304443c42a11402001d034890401d00c1c04101c020408030018078000d00040108a01d55514001d100c0014003840840b191403000132005501c40d4810740d403001450034180354440c4c0c4054203032911400122244040f1300922a0010400c000d0a8803103021114104003500e803a0040c404075032070716440041242c0301c40d942c1d2100c4104c607500c14840600402070550000c5081001e5080c880c405040c2c641104220501d0750003403000040c0c2c43c02c101d50040803241c14034485940c94507885000c42c090030b141140c1600805820102d8180c001c03518a07403d07400369003a114411380741c80800f01d0145030090310502055280409401052 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 431975782 1250 431974532 431974537
    0x2030702040f0b03030d02070209091207110f060d020d05010b04082112090a140d090303030504021203031e0a020403050a02090c0c0d050406030515010206220c0e010501090905010f05010302 83
    0xa00c01e00e00443d0611070031001c41e1950b4440003981400c654049109011803078120082e41e08110018001c0000d00000403500105100d600c05c02800d014200b41d51031000d44070f180c41c082d05003a000f0807140d00c5a11100d10039019600c81c00952801c2c0e40703840d0000c20722a0b0f0b1b50040e5030a841200c4028441340c0c6600291056141d40600c01041801003440500721007442c040c9024811b60321503024194000c3e0f24030f8481d8000004042c145d445400ca103000d002d01d660310003030450460f9094074011400303072204d00110342e560080e5440720f02540400020446c1307060110711140803045080b1052202542d5040081c0200e024500009007550003e00c170441c0076160407802c858211900c820201d14081d0004c1495180c89050514080845c40c0400c0030007005401d0b1107850b0740040c08203880740b0401c0b0790500003501d80030f0007080c1000d100784054040408001301e00b0025403440d440500d1490307550310f508800e04218030902c55107000801001012980f4055406054105d8099043c0b040046041500540103034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 431977032 1250 431975782 431975801
    0x6050a030b03010203090304061403061f0c120519020703021f05280306050f100f0c060203011706131e0f020409060b271603060f062d0203070204 64
    0x951949501d030510b503000e100941c081c040d00c2c402955100c0c5060b0019084201d0342600e16032101c020f00400c2810f8442864035101c01005e281c1c0c01107000740820701a6140c4036180c01c05000e00903110a86052283c0048c014003035000d4094000b6a0407000e00b070100d80e5041940002904800790f05042c1c640645000b43d100403002603414480d00302100314100b00300ca05900503020320540c0c00b000028014135010f1050402038203082d1241c0c0166116a00416800520302c40860200004003021008041c03142203102003250384258195641c0d659481d1460402620b886903284a0188a0219004055a04c9840400765001e000c0380302d840d00104040302d46249901050b110b50004200100040e41d4034441d51040600c91300c1d0010b4401c44034400d0049501018441d0781800586004803d001200365030001d0307001d1000c010400c011040b080044025101c1540b12040036810403402084158100003149104031000c140c0d00d581000e6154408001c100c0e440104025030020448000035091503000540c10 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 431978282 1250 431977032 431977037
    0x303042301030e1906051605070b060a09020705010207050105070c030207060c08040306050118050c040503100b0f09240315010501262e0515030a091a041115030106050a 74
    0x945000c1041505101c6514075003440c4c3d140d090b10610400103140310382c03504001070071240010040300c42005050f03442243c1010300740b9080440040c1680d55078094202c0500f04022080d900c420040c60003502079040118219815400c01e03001030501c0d846000da04203581d81540c02020524a00074058990880b80d01c400d1740c84010400022001c120213001e503900a11070720f0501ca0100713000c0e842040444101500240600c602080100070325540080c400d4082c2c00504000106500c0003000503a6840c0c0c0850050b411002c03203420010580340040418070032038006176007460240440801c241d2600c407980182c007407041e201c5006120a51285885a8500c1f20925018035400c41c0280507503401042107c800e46c1e0200b443c4045024865003008420786d0140e083d50342007609081500046500000c0a414841d61101000051940640c0c0d00820026504000b55648840d031004042c02c0d54002142d0994082c05515128200d03820b02000101e000300c1a611180e00b141d0070050211913a038401c041c0c5204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 431979532 1250 431978282 431978291
    0x31415011502030c031201030303180b1803091c03020615060715020c0616020705041e0504020a0f09091727030f060c040f08190f031427030304230103 66
    0x3c007a1302003004204254001ea54840075603d5880c0090a94000b0032025080e81034804c3c441c0300042d00480e00940001c0c0d00c503944010910090170407841d41c0070b20844140c0c4501e815545108008090b0110104240a42c0c2030303844554454110ba01908014404550071084c10401c0d5408215250300e04034220354a45405454a0808400185002c13426100910107007203501062103c990104503035401031806450a002d802c001c070b00001041c06c414100e24104580300c00c002001c642d19000998040c000c8205024002c0c0d48641915000700b505032000c50b21504c0f903401e5032404183c1d03641901e4120036a01e40c00707081200d6581c0c80a03040c00c0d400101e6a0148250b82100c145102c090205900c40c8248040003901c9034580308120105a94543c00061a80c012600b9085c1650883c4101718195030086400d51040d00341d0328048900081880121000a5000c50ba100c0301c1c040e110b41d441c0c174146508040070315040d4184d04040c1c0300e01ca1480340e900880e840d0701c414540c0b001104504040900141030015 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 431980782 1250 431979532 431979547
    0x2040906061e14010f051b0307020a0303031512121808030414040f02030403140f0f040e040201020f07061209140102030702060405010609050c07030302031f0f03141501150203 77
    0x10540703480401c00b185007580e660203021000c10702400c801804002d20302400040001d14000c0d219220300d14010b04c00c01090440065400401c1080702c084a502038045418250340703040080081840c0d084400903120b040f40000f602c14641300c1919030541e000039010207142012b0301c00740c411800d80341c0382c04009459404000749244c0c3c24806007005120300114250030001d10010081210000204400000d01c14028480802c1c0c0c40003081054401c4804541d0340c030700c200c441054007070190704081c1d05c15008c005004254a41c400400a001c2c6200303800316a9408695007040e602ea5816014032000039a2a2004042d0340001d44c001c1156180100382016080500c10290342c00da900c1191b400c40540d205c2d006000800500344580d4008210001c400c11050801d008070a00c40e00c6446406803c064011004c2154448030704d8800110345050f0701c020080039503503802034007422a148402d582c10600750000058400020aa0344160f040d56800c5140c1e507820304042424200b192442c0a046100900984 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 431982032 1250 431980782 431980799
    0xc150a03020a030f1b0201111305060a030e07031415041128030f031b0302060f1906080d0201201b0a0602030f0412050a0f050903010e03190f08090a0204090606 70
    0x4517002d0700612040c2904070780a5004e42950401c10404640c0c4500300000318448600d034180344140c5104603076490755458828000c5001d0241080301440c0c0e401108070000070405055911300d96860044c1c04d5030041d44000e0103100c00c0801c00c8a002c0d0011120305c103050401e10340f858040000c01e81180345141c60380303400e10b034003c003007440c0350011507030030f1000340091051640110f240940e100403d101c54035158096500292110030103458001c0001502d008102100001d10100da101c11030650108103542e900c08007282d89035140b2410070095440d01c400040706151000400241c00802d143e51850100b00d40480c248401080c0010b94482c018090844001002c5000842c058003c841044400b42418180f4200140032030b13212405200d0104404c01011ba00315526100c803050901b006621a8509004207014044144038511203010010304100d124800b00320700001d400203540d44a80e040003480c000d0302c02d11400e664406007039020780042001450140c00482520307114103008296240c0e00c0340761 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 431983282 1250 431982032 431982041
    0x61b070f2003030703090311150d05011406070302150a060b1903060902090d1709060706230919050723030c01030510030206070624080c150a03020a030f 67
    0x200d55001c04901c204140420300401c00c0d03900c880c100d0203146440701d00d81d000350030a81c00344801802d8000c41030242c119995040304100d04030300501d4a040d42e0340564402c0f500100003d0080c0c60b9420702905c0e142d521420035905544036550f0640007000313640d50402240c407915a00400b06a5200e403205404a104250100540310302d00e8034864001030540340780301c00750684603103400034210f440c818801144c039a80ea06040580080d0091000d030141185480140d90b80d11a0070821600048000b80c03aa08010381580440b00785000d11440080110140098407000c0ca8142c5452407654044002e08040000c507155405016102d5000c45201907680e562005d0140c440950398522600c0005038011241018400031010b010b09180c2000b0b140340481c007010300300a503800081e0041001080078410004580d10100700b41e0408900f10031403450303080300390450b201c850083e81400d006003450340b01c090900e0b51b1410242c02000d2015070800c07800701d1040b00250880010b00c810181c4810b480c1c034400800c0d124 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 431984532 1250 431983282 431983313
    0x20f070b070806040c1d01030905010221010e070207150512040c080f0114160905060328090201020a0f02010c0b0405070f0f15081306060e0a051305061b07 68
    0xa99040d2407401030340107040d8090041c68180240d08000400700100d41c04901d00042107031201a1020400c4c0f0100100c00800c8284002401036100084c01140341c1e1010070b0302c405125541075007016580e00c4a1175000100010b55648002d039024010600924948482c0111100550b1074a1800e205034100c160540003402d64060361350f40c0c881c5005201840050201c620075082c0d1000900c1000703c1c00c4035803411040000c0101c0030f82d0a1030805001114400c0206100500c0c00409264403801d013442c0d82000b20308000d20340e503810401c60141044a00c610702030750b4400b03130301600a49118061601d54000032070020703c0403410015079081031400111031603801405140142c005040e918140300407030a001029401c542061400788204100d1440c02403003007800b021140c03400350041d85900006501d091a00b8100800c46414801d02007000300c980002c4030f20a012441701032080c4e81f5804003c0b04e100d5552032010b442a0419800140041894054001030040e030420803441c098998a580410445036034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 431985782 1250 431984532 431984543
    0x818011811030c010c02090705040803040e06010e10020a060f02091002060f10050f0d030201060b0a02030a020c010f120c020c1e15030702030319020409091212020c030409050a020f07 80
    0x100c0190500a000303205500d01d040c02e03001401c03440a0040003034140814120024030811803c0e000510841c410816580140814030490351115200d42e4140b4080b041100c1060000d41e08990080075841e00c44070381c400000b290b4001e0142400030352690000b80c01c04002d07001500360200884c50090b1112424440c8060059014002904101603448440f11000d06000191401310740c0903c640c3d5100764000320084e0b003c0f596104510610300e0181d003d003211ba84500c0d0b00e02404585000c00b0385c0c0100080030903240381c1e800d88106d20100740044d61580110512400055080c031006a060711955004900801c920300450b030700d14034400e0000b01c904a16919525031501021805291424008050025400340448143c21482c1c00c440c000c0d520300005000641450107a2a0303203010415a074103c8025151420b4103010100d21410119980000300740e04000103070980340c0090400d0101c2c03082d2440020b0b40d10140d03203428640310580f0080d0501800003804a0303802c01c0001404400301004000b4140b048 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 431987032 1250 431985782 431985821
    0x7020a0c06020a14060610081005121609020406050301030f05010e03030a14010504050403021f060302090a06030b07080c0a030902011404120203060106030b031024030b06151603081801 81
    0x43c54103080715104030130b0500f0035501100500c101592516500074600b401e5150480e2290303a1b0503041a41880c584c2e211a80041c5180003c1d0240400400e41605404018114190042d175824032803080b4480d62103400c002401c20300045c00014200041240c055006000114030300e20101c0080d4103580c000d4a0320709440c0d43d00c0c0ca4801607640a03d90032401418100d41c10015403a280c2c9020f91640440001e4282d090026070350b8208151035a840f080c003558002c1e140c2d440a141040664004202a0005a40d400040b40008480e284503181e4584244220800304d81012a05c12003034001d0450a0b40032814410944c0015295030007035405000246054001c02c203112040d80141420044103070081c004250808408084903140000d06909885154000207803014055070204844860005522409044000e0000c140814280014001c2100325200103080c20003020025051150310400c550a070422200103020034010401c055008601c50008505005c00c4883c045c00c6815050b9210b82c40e0191 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 431988282 1250 431987032 431987053
    0x28020406090603020f0708030c04030807080315030a03121a060d0902102c0d0203011e0615080f060d08040803070b0c0f12061c0303090215041a0307020a0c0602 70
    0x10040c0d00c0e00030459403d00310f00c0d0110003d0041054400c14401a090442c00404540d10300c1140782114025908500312503100c881c1844d1010b0349510540705010300c0800207698000d180b03004960f000d00c0360340c5519214100011011441d001d40b54103101e120a000c01c080d054a41a02d0341c40050004400c044c000040c0b2a010380b040040c9070f17000e0080340e000c00c14244035014140d480802010080820001d103e100c0c50360060000e8003504525100a40550800d2900c2c001c0032500104c1300a0000c010310300f480507644480e0320400c6203290f0b01300e890008213403201040461148514143d00810080c04205908800d41c8552680b503005a00001c416400005c8400131302409011032a000210320b03202d2071802c204690040511b0084112074001c880128003c07070040d07551000c05014a80c0d9010210601c080c44e0305001d0010406440c099000301c40c10041e0642c07581019049031300b0703140703c2c1c1c124055610b9200c0701208560001006a400d5110f28100100401e2601c09000c0c010807041e401072201200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 431989532 1250 431988282 431988287
    0x18030506010305120c0a060b151218030a120509010b0303070c2d0501031e0f0905100b01080127060e01050f03010e070b07020f04060303050a02060c030411010828020406 74
    0x14100d190021407213041c81100380001011482280d4542c00420208814079110001000300d10b841c0e51503040c04100140802000000c41107013031040c0414400c00d200412011403c80d100d102ea01c90030400100d000c4400c24134250240e01107500103031002d000080040e51180420314551013080240d4a0703000440c410030002c0c0300003a4441c00c420501c4101d161203200c0c400514810b13a020300809061549030080e440200000c10014014400d030710805126a01800941c43c005002002c6c0c1070340e0500504004400440c007a010b5206000011381d600c0c802a031800710b1402c250801030b81d400600e0380c40801c405c101144640203200141111056921044d4500740411900044c9000d900f030103030f41016445030040f48045214002c80380d424101541d614486d10002e800082a21000790344945803407004014194000c0c09040600c40580844003030341c65500484030a8002220000c101415807a030721040c5d54400d05071150000d41d6001d00102c035456400001e010b001007150880036190b40800c1c1081a2036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 431990782 1250 431989532 431989543
    0xe010306150602070509070309110d080414060304150203100308030916060215071116080102040801060e0c0304060f0207140d0e0a081e0c060304030905130b100e0118030506010305 79
    0x5983c002820598607040102d00e00c0d81e0020a10000e05a481907000144801d250000c0f00f01080100b040249189904d042d0459410a02071903520310601b1035600c8031401e0003822a4002d40c2c1008852001841c1e00c41200701940c4000c281c01c5070901ca60100000140041c4041d5018032860000b9040d0082000380200031681142e100e01c00b150701006080480c01d0070b500d0300a40051349803522107104403010f1106407800b4182c0c801000ea400107014000303101e55040d4090815078884600a01ca920742d036030041e084110065070910071600303040000c5400510140c0c8075000f42c1124210140c10070216886040300c0202c508220407130b98010094044c1c0c6503500915584024504590541441e800c004019942d406410443e2444c4a403c440d1100701f04003c00c0340704402c0800078215580c1c0d281900d8001c00f42030b50351240c1e0f4051010309004e00400e4455000302c082540700036211421031240c0210407618840a108614144039035140002038003498007441d80c0c080e501a20013885103507d540791a52801 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 431992032 1250 431990782 431990789
    0x5070f031a0609040305090d060605060a020f0d030b01021b0d0c140a09050705070f02130203091c1403060415090f020c1911091b1204150e061902040e01030615 70
    0x4403502e0013000000390b048030648480b0b910030340f41c00c1c0c1494081d203005001084a50031455004102040c0349610560004110300c0041800e802d031209401d06960640c1070795180c064440c0560042d8a00d0f40140501ca4080700e85000010100f900002084d00e4001040109800089059500b04407903603a90901c243d50748010042040204032030310388204001c00343d024042000300268400c3d5881000d560304c1c000e03402d00c0201c040604541d00d08220154030754031041c035441e082d000712488d410a02c140b030240c0702c12441c10044025243c6186c2e62601080300034803d44200043c1103004090206003141d440c45618040c0618060040e5144c140c482018900000390000072154a400088240014150451a0b049240c2074408440c0c1e610b50b0010b04c4c030309036400320a44c3c00c0d84501140c110b405408102040e401240034620b50f4406500d032003140d00903280c2251410310680d00c804045200f42d02d4010b24414548060b400050606440340710140e441704080c1c1c010b4940079140e682c10b8503071042141e1307010001d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 431993282 1250 431992032 431992039
    0x4151506050d0b01020109050f0a0515070816020a0f0602091903020f04091e030f0816080c090607060f0c030b06070b0a020a05070210091a12010b0705070f031a06 71
    0x4040c5000c1000300180710710900c010007a51192800c0307805074001d4200b0843c450b44030341955031000a20018564804000b081a1864450341c40300b545803d1804000f64041c156076540c038041c0350758500c81e80c540380b01090082c6085116440e0808041848008459000d510902c8050f0ba103240240c100b106070b0402c4891a40b82250b541000c00050b0748901405184500513113011500e211907003407a41400615003005071108689014106c101035000310781254111383d9031181c0c05284c0303850300c04c0c0f8102e80da5071000c0e4002c10fa080700807c0c252880b90016201c441c0f0002d02c46842e20441c1c2d80d58809071400304e800350000c151030307414281126030036024819008505813501c6080000c40e48500043d0303a000ba014203001c5600240d690b80c0071b403240c41200e0034a0380203840f0503024a0315000003040c4503040c3c0b0420b060041340718000cd8201d442275040310000c143d20002d007040d59090020300da109501ca000201c4032071082c00000a842e040d0050b58200550141c0300e948640719056002c10611180181100d10 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 431994532 1250 431993282 431993321
    0xd2102030412150207020603010305031e07020907031a040c020c090601020a03020d0509060405060c060406050703050907050f060403050726030301060c0b09011d0c03010f05060306010509040510050415 88
    0x2d0103000d00950000e070401d1844190002480450b0000c0c40359150203034120b80000004020b00c003000005085026240e00c0164440e0000b070781b190714900074107400940c800c2a48010428030340c030940041d4030369200031400040046c0c5480009007210900401c402c00340c0c02c0a0910b800c0b0b80381000246501900170300150003550101d90703000351540d010b0000c0300140280400d2000c170645540f0300f42d4000d40f00c040c00003691b810070501710f2130351270208580c211080c50500c0c000858840c82806014041c4034182c00a003103440c00e0000f00003150701c00e0020540c0215040c880040407071f40400501c1d000302055120040b0407030100500000c2059800440c1346940d104000402c00283d102003500c21480e080803d0f011540c0f10803a015000d0018a6005520980042629800584041034082d0300341000c030002c00c1f40842e6240400281d6004070b400360307890740240f0010406801c0c441c0c080391b80148600180d40c1c0c1000201c119404981c400c0d00d0a403082038005181845c200ea451041c000010409480c400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 431995782 1250 431994532 431994539
    0xc09081c080f0712061215061401030f020d060e0906130302070b0a021606031d06060d080a11010c0206160827010e0109060f0c0503090c100e0d21020304 67
    0x1400e918001d4070000603200240001000d403442a9000c13205030a101d1003c0c80159590240d0303504031080c0d02c40030384c0c945251031a010706901443c414142160000e645441c00e00410070019001031250350300010324660204150020001c0a01c502c2020b845144030389000c44c00c0901c0750515048000b4000b0381100c840303180003000b1070b800140410846030f90103001039031582d01d0081242080d512120f0461500060000130414ae0b400da00480f081e02a06440d901d02c600e0310407041580c50006803a8a5002021044110f01090060000f042007020600301104014414640982140c8247c14000010b8002a003800000b2121242c40a524a818a0078444900740b814a4210791001009230a641c3c4502d0b0190030404282900070014025410008203d82205c45c1030000142c0348016802103042e191050b00700543d0b0040701502e0203210030200419205c001d450910418480c010348500078004000c00031051503a0327089204060f6845122111210340781c0d10084220a05450250301c1503420510061 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 431997032 1250 431995782 431995787
    0x5071a13050d110607051011090616020607140c03060609061c03030f020406090915180b06090907110601050907020d080c09030d09031a07050f090f040c09081c 70
    0x302554812108005000c2c0d0b20701c1d068088596909005030062008a069014041702050071210041048010302047d0f608520042692041d55070341c0d40d21440900201c03130f014004034829005d5620180446281100c1911148011002801074030f90a601411800c003450800307020041d0049002c0e070311a10b07142480c400180039191700c40b54030524149090791800c00c1c1407094001203009035440e00215030b21511641e0040103444280141d8480c1402c01c4001092022a400d1942c100e591102d84400100158940d90018090003400290300ca0780901c140720701c40d0b4030101120300608a03900ea00031819801e0004a042000590215200e03540d16001c004042e038010801917480360840c03421404075078450402c190701c0d020300d00d01d0310381510486109182264110306144256800344a92403001464080c00d11440320003188c1c00c40001d04180000d5103c07544803005000317642401070600703403c680210040340032100414204800074000000c104602c10040c0210000701e60308003030300c500e000e0051001 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 431998282 1250 431997032 431997067
    0x907060903170913020a11071527091503110411220f08072603090f03100920040524012006160503040c0501121805071a 53
    0x1960000d20300080c000b5440e40e18180b503000c8004012101315219038140318007c00007000d901215000b172045110200320900340c5034940c01e40b10610350782d101070702903007000350f01411009482d03801c2801e945200115444146020310b9066116070b00c8100017492070340c10400380207452042980c1c0a00d1402400413600541d0704215a07440010540c43c082401c011208109000c250fa48004054040854003003001301021920904a806a140503a602c42000d1200014585021040b010651040041c200c40c1d0521300c1042110030001000c0d01d0f000c000001c001810b85034036a40c2140c101600010403000c1e014600d68030b0380d05c50010b0310100190301d00826401800348202c000740c4050445000b0002080e0b119403030240e00000c201c10000b039040d0a211845940e004240c40b0202c504294007640c4507a50b100d241628400d076000300c0e80420079850304d0015070710505a4141407800c1c5890b010100309025031200c9401c1254499002000030910b41040060114003180e06030003d04010010b81c041d20301030010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 431999532 1250 431998282 431998313
    0x30f0c120f0601180803071b21020a0905091c0e18060406050604090209010906170f090f011107050c010e36090c0f0f060703050c0307020a0b030907060903 68
    0x41281903502c410005a8541c4c9210203450306007201d914001c54040e5005c005411034600c5116880d45821030880c1c011491100c9000b0009640d00c4161504d00c0301c3c0c048031221505900207000003c0c07068507000072506a410844802c059940300380e03000c81c7d40000078841607e20354070500e0000d00d000240c00001c1c1c64641c00c4440b0b6680c160140d004a0b005954980c0208020900281000d03a07565880105070003940295260740e0104411040c001607440c05072401e40910054050075042c20754401ca0382c240e0000002e07000c000d061280c1c1032048818002445480083c24201c214203844039031070b01e00305181600e413900c0c0d28100030340d40070021942d03103465103050502e1182c10660310780d0066012440e241582c03201003804c0089550360522008950204506004050a0355000b4400c4000414082005070355804550040802c005810101e48640003034540c0c0616603080d00d00c1c0040680004421900d070307402003680d10700f000090250240003040040c0c0108254141005018915120146814000d48 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 432000782 1250 431999532 431999551
    0x204080c010806060d020c06040c050901050609060a03061a040e0901021207111204120203010509120307050c07030b010e0906010806010513090218181b030606040c1107080102030f0c12 81
    0xb000c5010380d070f140ea06407541000034040c115151100c070705005035039040684042e05c0d5100d440c000400c4a042441d00541a184003914852900300c44c00284215540301b500080101540ca00c40402e080c4940c542811105103500340c1d0a495a042c85180800240b02900041c4960320410149280b41c1c018800242d0240540c20502016010354441e2801d00281e00102c0aa0980004005c00e40341060404d80c01400c0c0250001c003c140e44103040386641e006040040c60f5582c4041c4005040544500c00511100100b0000c2d07030f11003940c0b0395a0240d200800c0c1c1150304410a00e10402c100c021041003410f00414021004000030351610000c40c142010007045406150380b140703040713001d40d103504c4050501d40305500c000340344914188809100700e07540c059081c0214001c004c1485460300d918a1060031004005016115503100d84003080f0041945100001c00d200644000d684202402d111280c02011807800150760f80c60003902e00c00b80c2001c02880c90400320741c140809100a0341d40e105055001901c030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 432002032 1250 432000782 432000797
    0x2180f210312070306061103070b0613090f0b041a0106270b030a1a030304060504090507030b120609070f06020604060507020f0f010618020412030e0117090a11040204080c01 76
    0x1082090440c41041101c001180c1082c06000320194180d0040044034190342c2d40e40101c0d0150610103407a407180e00805800550081b0120b07210345001074900802c039880000009084940ba82d5903c030402c070b03103182502c00c41c04083c10002031010310032441c49030017131410303640105605010010780f501011007114001b42030304d0710400581c3c0c548603044030b002c0c01c51650140e8032403400001d2030b400b0b454804a00d810685145d0394002d20340c180001958151140340c0c442c942803905000030a40105001401182050740703442c49a1159124038020203080140c45003d05598a0811a664608681c0303038015000c0305204001000b4607580419600d80069015901207800d4a40741e100f28901100d02c00c120301d140c09040b13035014038140158070030700c00c07681e1100340b0410075100c4c0480c07030b002ca0203035100307003003006503072403035070030000344509200a0015014140008940030317840c140440c04c9401c03140d40c80b441d40080b06440a22240c02c900100710b29085070705500d40303414600300c40d448041c2c600c2c1980c14007000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 432003282 1250 432002032 432002089
    0x80718020903031308030912010b01091a0904150f0e01030b060405060f300a0c052403100603051510110708030c0303010f121a04060e010c0302180f 65
    0x140308440b4840c61101e07914560036142c1400381e84952044587e03e11400041490b03410040303060050740000d140c140c5482428a240c0340d40d11440c428000c6080c6180c0a04024a034400da4452058000c00903000542d482118240a040c01015a00382c2001d52489011401080000e01103420301f94000c0c0c05131030225142d201c00c00414000d502512083d80d0000d01111280b0540303100e101445140038042a00d86108030f80201d64607100c0700c00e4600a083d040c030060341030145043c000120f0809449104030314440c0d80c9a1082800160400d40e054a14002011030030801c2d154540600341d0010349403444904030400860000380311080b03110328001031118154583c241c401c02442140000c001000580b82c2d0307011400021500c0e0791090191000408003020046000310070200d10f640050b42c480032801e8920118148420b00340001001201c80648581c0c0c40c1c242c0e20400e00508105d00082e88016850b540250205c01e4030103441c004c0280030310446942504560f4603026180c201d200760322030038100c2c030070f0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 432004532 1250 432003282 432003289
    0x30606041d100203070f0c050c010f0516030c0308010b030f041103070503030708040f0b04061d0402040503030711090705071e0206070f0f0507060807021c031e050f010807180209 78
    0x70401216859405036034510380320008a60003c52181d41540d5840c3c0b00480f0701ca106850382c000c10b101c091308645c00134100c040554021002c21041c04101d007082414699014030102078040e001c031085000075104030f000020150000c101d54003400100b00041c1c11441c0c0507100100c09600208058044010303025680000c0c5c9040c170604015100160590799107082c0ea0800300380c2c0340d200784209418112103400c0000d86820320b009407420754195540d40029051031170101280580505805503000d98200310000e11a54208014200c5501c0b55000400c100b4220b0300300300d041180107206030140f140420040c0000341c4035941c00e5540b03600c290854081e0f900d25001242d5113000d0140b004010080c4e00080301c0a010400c84803000c107500c5941100e1030386855007000c441c82d1801303903410070241c0e020f07510b10316203090440032015010b4034038900010344003000300e07080d501e841e03412000320b04240e96601449120840280c100703016024007001820094030f081400d03010b4441e2114001d50407a40424034a40540c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 432005782 1250 432004532 432004571
    0x303160f0224090d14011404020907090b0703050d0605060a0305091005070c08031306110d0507020c090a0c180f17010605010905010c11060a05030603060601030b012007030c0b0918040203060604 85
    0x3c5e100070020701002c40007219552105403001ea200b502d4660005113003500c41c07101d540c00c4d2816000700a0030b25017142e034140c81d035402c0400701d01c000540f9480d010499845050240c160000c095a0102c1c05040082d001410f1690a03950f454515050038100301280d60401c82c000c8407690300c80402643d81d6581c80c6070340042031885800416650800d810f010388049180054485015140ca0420254450901c180e944032600320724190003041240000385540841d910403000490203081812500e45e05c0105921001c000d504424400c1184400c140001d010807900146541c0e2003e000300011410000081d0251500d481803504112441d440d100800a0184010f14282000f400c4142c544030f001c0780240142d08100c0c0c00380d0092107040300103000740d840b9001d90529100306854a05800e98182124800042201d1103400e403842034140000008001d49034040082c060b0070355268507160401c04004c0d1501c00e03062a106521030304801d0002507a000300d407894000c1d07401c82d4000b9503151152146400764 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 432007032 1250 432005782 432005813
    0x7030905090a06030c060203130506090402070b0408040f050306040c0312021e071805040c06050c0f0a05011d03071a1e090109030e04140a05060303160f0224090d 71
    0x4050034070200300321680150f0b0070303244695801c144031520340310304a90f60f0140364414200b84030610420006401c003203000303100034403010340054900031031031f03e404040746026a400c542152000604001580494280c1d03000303010200c0240c441828551104c1005544031300001d40f810782d0f48095082298000c00c9141c984410102d0f041540c010826201a2140c0701449040201071080888840003030b1302c2c2c42070500c87c030703809095031a1845c10880c04541a811080d5400800d2207061407174504c15108022200810707100724004039100100e05441c0c1000c1014001201003075006020360000501d45183c51101c2c0072020040c030407a95501d603030624490728200c0e924280e18404000344400214190044821207020b0348a40c0e202001e94402d000484003c040300c15101207445001c01c0b401a560f411540d0010710041c200d905000c80c50300c03180c80c1101c48d810100d4010034030903a0801141840001030700c502d00c2d500c0401100c00d888007c1000c0c584918031001d03100b208080d983c3c0742000100465110741 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 432008282 1250 432007032 432007039
    0x9130c0b040303030f02070203031603120e0f0705060309030d0c021e030a0e03030f0a08060609030f0706030509010506010f110f1e1902060f0c010212070e0f0406050604050607030905 80
    0x4180d611034466069600600060300060b00b0a2580004040340c1d0080303c200c80d50280003107242221183e984080d030b1903c110704400300202581a4040e21031503002d41e01040074801c0280080d808810300380c2c1e2500e2015882280250800e02c100101c1803404000c1da403514034580004540740c10941822400d181d5280503002c040100c04441814105002029240071105500d400320740c01c0488042543d24002c5100b1342c8a030307400800c030100c0f0b0944200300103900210003170a01c5081241d440002400d008440c0364054555000740300400407140d00d030080d10340001c5000000c020505180300020004100d100b00c04003804480428410b06001c100640303032301c80038400f00784c6444108020304451000305104c5104118031656082103596108521000d850560050a052070300060f42100101500007620012840d5401d010f520f0b01e0100e0020b0080c40703030320a0f60782e220303030000d03001b0070019030192002e5014026032030580c0600c0a03440e008112000da85c0211119501c49900c1d1130708456095150300050740 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 432009532 1250 432008282 432008303
    0x72403020706051e100f18090204020c2505061b0f0105150a091b18030f0326100302060306040905070807060906020d300903200a030e0913 61
    0x403100d00d41c20825000b0b00c0e004e4141c40e41344c074101d400e4400b40780d00482ca880305e03551008100c00403800c182e411142c19081c1c40800d2001306600010100e0300310b80301501c1c80d40c000380032020880d8070034800401200c07107035050301c200c0606110110b9910f00403802d0070100c40c20720380c20400e00c1b45000c003c00110a01040000d1115281c200c40183c140050461107a002d165001d0380807501c03050718041c08074542042600d406540b061010101c6661a03001c024840590040c0c6000c804075a008211940c883d00a8981c01c0790049429070a50000518004100c023500e150b100344002410740c141000c085940455146440780c0311140014000c080c0e401c401050341c4903186c40065525000700b8002d048616640f40c036078840b542d03042c0590302c070300440399040002002c0403908416903040414001262101c0714a69026a490080382d508aa0a140003540030036800c4021524060126903800100110f000c0513041664055901921081641609a214a00420000f403e0340030b4072088120076600f00340e8100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 432010782 1250 432009532 432009541
    0x3031807120c1e09020315010207120807020d1103030301091505060a0e0904030311130302090c090a0608040318170705300328080a050717100e07110106050307240302070605 76
    0x46880c046030401a001d409503c2000bd40820070290218500d41c024200a191034081d900700599a000c80c1c90403200b81141c2c0c240703502c0c540c0b000c00103180604821040000d01e10701c0306100c444085680d51180e071240741d04000c8041420703031151940749000c0e41614030072401e443e61f00d02038002d001600002c58601310040b41c4204001c40b200203d03422640203841e05103213600c2c1c580c4290031510403c1412a0052200181001040d100e60002070b4428000d291119020102c03002a084011507644062507070001010000c02026051182900a200856029114510102c4900100300d11951006540301042541c0b0301d805009004660b044500c00301103440c0000140b04c42c1814600703620507000003074460030025a0f001e000744a06400340e03c10b922a0841020582c030070051240009050b019140c40c400c0c400a201e00c60b005040780107494039110040d18604144445085450b207070b114031700c25032200c4001c005020203000d041e02a464000030705207140f07a400c041900070b03202c1c0c4c11004261a14120410 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 432012032 1250 432010782 432010801
    0xd0c0c05011802040b040203060d080703110709060302270114040b04020c06011d010b070209040203010b1207050111010618022d090a0602011e0b0f0303031807120c1e090203 76
    0x8542c03461084030204849603400080c88120300003292103e0f0020481d40806010409043c05000e100e8030924101765008002600789040900c581c0c000b8030200c2e12aa0144210b142441100d001c1d88503814001e401004d00f044070400c080d406104410072000e80860b1460b01d901c664108040401010b40195510b918001c00716a5400c0244142c1e1080001101050a0b04007000e4640c0d048845100180b030070721801e0307003c01414440152040303a2547d42c80c0001101e644030001d031024400400409058014500b400142813989038800d400c07170591601c0803d0183d81c0301e0f11038003100e07651446001030726400d010807100c039045110b0078044c1c840025114180c000070a00d41c005c2c018010140c440ca046d0682d104001e90988035440b8250100030082c0600c0c03d40c00380c03507a118045192009180e298000b83e980c010030305540c004e0301e40280003841e80b0b01c20300c101181008101c0061034142d5010305003040507100c81d40003d03054011003a1b0452900142c5600410340001c001c007400d48404119500e0910704004d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 432013282 1250 432012032 432012071
    0x14091809010c1706060d060e090715020705090c0a17240d0f06050c041511010c0e01090e0a1e02090906100c020904080403061803230d0c0c0501 63
    0xc800866003841c80100b0500e1082012405060039404200300c1a00d9440030054a40c2040c2d406601003036682800280c1300d00702e84411400744107802d000d440c170541010b407003542002c68002031341c040d076100c1c0310104456212010354550021502010f151952103440c02110040c04180813101440c5003101030007510031200555541d0f507080c0700038901c0c480c00a0003d00c190300c43e030b110004c0c2450b0f8902208001046464000f2a40445000029450070392030300c90040802d500c0f030000000150240d418070031070610074401c20911041c00d00300400e25221500000b040e4403154083c4c1d816681032000450041c0e9425040390710f40044d01c1c90009600300400019400039006444118407540109020030240c2c02d0010704420712160039640d81031207103159000d10220100c040c4c000c81c0c08000400001012a1051240c1c20007010252025140c1c10814100200360b02ca05200c03d41c54114924900f0190490000445006100c0002c1c040b078003642096040e103a80b04448000b86ca59428880c04505c83c0d00502103 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 432014388 1106 432013282 432013291
    0x80a03020c1f02090103060b0304050a1514130203060f01300b040c08070b1204030c031e051c090c06030b0d0f0501061a090a0303140918 60
    0x2c540708885503848005450070b41c0803809113115a41805048000d290009400f0b080d4100703902e1b070303a44480f80500c0050143c060745444010100940e081301800591503480a483c0345030030002003681c4016184124401d0003400b0014041441403078140b8162400002d03028100320a40449203030007a4a051008031303055034260018002815811083e11a07407061003003210051510781c88a1a20305030740c004130340d04a0203202035400d00d2200b00f40198890b80502c1e02400d808ca041c02c090703503420340ca139860f210303007041400c1503a58a6822000500c001010b540300c504401100c8000030040342e5010f14001c4c0000512076040007140e2181d040300240f900014610040c41d100350380c1c0c142c4012048201250141d450b90810020040d5202d14206800004903100b0f03d404400310000d814240e8500006003800492402c18403c40ea8a90a4889228000d00300615680c80320030150140c41003241d = true := by decide +kernel

theorem cover : BRFrame.Cov 431834532 432014388 := by
  have h0 := BRFrame.cov_init 431834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 431834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 431834532 ≤ n) (h2 : n < 432014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
