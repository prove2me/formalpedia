-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5317
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:28:20.972368+00:00
-- url     : https://prove2.me/submissions/47faaa20-eb8f-4fc4-97a6-13751a87ba57

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 956115107 ≤ n < 956294964 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 956116357 1250 956115107 956115133
    0xc090c0a1704030f050a020c0414090c01020604030906030b01200c03061302030712021f26090712030c05060901061d060312250b070f1e180b0705 64
    0x10701c2141080000e025105420705690041400e02d580e04c0c003108101d130205242009920a02001002400040c001d00c110390444c510116065002d886c141000d119100e2448640d50002c51400c1c815a010386501c20700c54a0030754154044c3c11000d80d1a410000070010b41300c0c20111541402e07003115084802000150300e403000b810300c0c1050151944c0d0b43c020701a100d0744010303070b0005210025034061050002d0f401c5581d101081000b20b0200d020703004860f8400c0545c000e03980c04840c000c0a19200103181505061200008235810b105036011942604440400d00018208001300e00301c1074441d2518104524054954905001003602c1964569450720810014010b00407080c9072413050441d180d00003400c14000280d42d035140d004c05030030780c014049030b4411020080c0c0042481c607140906400740944c4c45103440c6035050301c1242c0e110040b0700004144c0350300c98810610700e1000304a42c102c0f03406424002d8000c0c1e4030b07002a1a00a641a80340400120780d92100c00050003106100c1c03c01003000900c044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 956117607 1250 956116357 956116367
    0x2040305150702070f0b040b0a0504080d1d0a030c09091704170d050c0d080a0e030c01020717030702030d0203270f01290402071a010f18050114120c090c0a 68
    0xa171002039612040d20080c08003500d030408660454019160b15540c0384036010f401d840502032580025954015414401e0740d860700118941d680045203c0c20032903542120080040c1040680006046070035842821f0101c00015031040a089002c2c4590b81c181d0b882c4100b48002e66072180c1c0205c0040c070080003007010041d0341042120071169450030242c1c10080441ea03c1569400551640000c100d60b4101260401c80264000148000e020301901d41d02e960b00f214681c040c0d44445800c545c5918403048038100102001c050320300510031907003e180382c803100312180301c0030703410280c50344003001c4601643c00c0e0701c62100c09131000a500c2c118003903c26600261059030071165800340442007400c1e0052000701c1504450506110395800301c03001a2100e18a05250300d09080817030541c80303800101030011034009a404083c0040b580780c001003c00506603002c1c42c2090b00c0c0284120258920303444140441840c02903109003500c0444c4c803c030782c1070000700e00014030640c40989000c4446000080e0340f1180da6401 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 956118857 1250 956117607 956117609
    0xc031b090b0f0f1503070f020f03094506121b12071d01030c1d0109090807020409030302031602060903030402091909060f050109090c090e010204030515070207 70
    0xe0504020340400c030408102d0803040448107500ca480c1d0800003000f01d9803500419020050362140c815101e1411800144c18030007200c09010144c030804240e444030090000890341310240282c05108011078980200690203440b4203510055030480c81241e843c11104210b001100f1580412a8083d0401d5014010707082d89901c000c00382c82c2c2160801800e40e06040301c2d50030410500303075000c0b2021308240ba910360030716507250085903032405014200d51102e4101008141070383c0c015100562500d903a41142c0f0003044240400520041301e02c001003140076007550003d11458014035600346441d0303042d03000608540030440c088011076808000d2100d40078603403000041d002000c3c00104254100441440c1c0d0b80c0c000140000e21500b440c00008983c415016140d030380036480802c003440540d02902c0e040e0094800d40028003071280c0f8250002801200030300580707420700e4225407010071080c1000c1000e0b000d80000c0d0f9490409640810002000500030820301c08810004d0794010203074101030300300074100760035 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 956120107 1250 956118857 956118869
    0xe131707020f011d0f13050405010917040806070e040209030d02010507180506070b0612060c0c012714072c100e1302010c0b040302060901360c030c031b 67
    0x1344030710160308412021555043c1c0303d011a11400d480c000328001494440c00e100240c01074034185820700c4200441500701d8240b1b00e215031003a00e10384840a8a00303000707000301d1240000b0396005030003007000940030b480703800801103020b0000b62510720f0120111385800d84580da4100141e55510420501c6075001c240f81c2c011682c400d591000d45032500c00000c01c28007451002502040301c41000c10300c90f82c2c0740200032820001c4c2e2410780c1c0e11071405035034142040e08140d4411595508140034240c21034442c0b098400008610300a0045034007135600d41010240245c031000c0b9091255880204c0d01c0005501d0409520307140c40c80ca400581440c0e0442d1031802409081d580c1403d0510000b40840e050103070a9552002e060001070b451000310380012540c124140344003410f0559000d0a000601d035002c07840500c13482030207000340600d010703400701c1c0311240c0780714410b074045a01e070b400e815031144001c40c00c1109081d00a2070301c1e401641c4c490300ca185000f80c050340111004120301c284070f62900003100c0010f0040c20f03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 956121357 1250 956120107 956120117
    0x13150b030c0a200c0103050a0207050d05071b050a140d05190213020403030507020d0c050603010b0a0f020601080607110111030c0c060106030902060d05072c0a0803070c0e131707020f01 81
    0x1030064196413165038141c2d46060648420004070342c808181c0c1588d808a41220844c0d56040c84003401601a5000c0101940d06100b520034200100d05078400038801c8801c040d20880086150000051f40c001c0b0314040d06030700a1140c83c3e01d8000c160704005000c0780105c0c5c0c0404504c212064410800708010100211121030b0041c4000c001294008040d600c030701d501510265072512191500000032040b0b03810a03a0700070000300c00858032042c260701605156070261680744840305190000d0360b40d100c09101e883d050f5444040060485841030b00da0402c07071031f004e10020484181c03088203402c1c0c07030300102c4a03d80c800e032001c01d24101108040013541e00402e00d03030904001c00012a008514244200c4e40082c034095141c1e004940c0c0e0b40d00c21902080c012420391458a900522400c805865413440c038421407041902a101080040300030040b213000c158000d5000800303d00c1d0000301c9244500041090074401120302003030300801e051140417111005108101e07542c41c071003032042160780ba42c2c0b1000d1a0401c9 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 956122607 1250 956121357 956121407
    0x1050109060314071b0c0b121503070512010609060810060e0f0a270614284107090b0915040909140d050913150b030c0a 53
    0xb0803580c00e1a6080819481d2221740c01450b1a0340501481060000034000c280032540003c05450820140c40c44042420007102c40d600d0342c0046c0c6805d48410850720345d2540102034104071900d000f00189039800000400450419510a22003086030025482004660480760340078418500f1407013000701614181c800c00e10641422407409092640040c40200b07010781c0c2c0d5a5540140d800000003518400a8281c103c54000c0b50746028030141c2a0f5503e8058010012000f1821740e201c10948510000d0310380e81011000f924a02602024000200b1a005c1c0344c205150030a20100c890991b0400e420306160088007030792401d201811807100c1c028100f50400641e2102841005004012107920ba9000c5400b401d401502c9281c035651803103190b1060705000c0c5006060002c0280c4100700031520081001640c06010400c00140d503140b140c511025030140501c4d0001416043c6980701c0002c00300720340400c0300d1340d548824080301d6540c0140d13003480441401280c0102803a920904090101c8003210500c0c140d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 956123857 1250 956122607 956122631
    0xe01020c0d12060f06020a060c05160b0408040302151809010f03141203181c05220e0f01150239130c0f030506030a03030509010b0a060305010501090603 67
    0x58451125032002c1000104408840400d41c1d00800042c0c1050854144c50580e15540031359184900c14044a00d10305020306600528058030a56040781e139145404441c6150984d104d41c0c410314014000c43d04d2074418400480540c641c10314140c691404540341d250fa801220a8103d041202c64141c24402c0c0c40328030043c00710110845410003141d9001d01d50030380b1218107a544500b4080c5940300103003d02d901004000e0040069441c918210001c50240d81c0c0703019011f14400c4180f840d0160600101c0e0342007040f1080c00010344038411008221101560110b903c42011181c1c6582c10340307104810f1001000107103c071091040c2407100f140414001025003400205000c02240030240c541140509084100c110225210300d4102c0104002040300401c0800000713000002e281c1410180c0001e40329a085c10005c40c06445603d00600000300200741c40041076a080f4013800e40202050165500d81c402c5840c6a2510b144400244c601504d000c42c0e550304041c001843d000442d80030070201400c1404803004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 956125107 1250 956123857 956123863
    0x405030304120614070206070908013608030c040f0e0609040206090a0305030c06010e0117030f0304152a02192a080102221d0a0f1a040e01020c 63
    0x488010b10460700d984151410520020007480300b0801425880030304102880d94085031061203021035490b544002394580780700c542200c40e09810310315820b04c0405038002003181d1007400d40441c03000180c507842e422030740c0c0c2d5408a950030170740740d41c91039001c085403e00c985d16a01202d04003422000c0c1c941416864500006061102e000d080680913810002d070480c0541c803500c0700b01001e9900700302103990311104401ea05640e01070900c035211300303e0381100020030042c181211644c02e4201c01c0c0300460900c51000b0141d5285d62000c0e1046840c80d5190041008000d801d0041254006100c071000a01c8014038032611096042c105c2c038901150000400b5902c5000000c1c0741441c40d540125251064800380110b81c080c00002c650150b203d44201c400024428105400278012030745c00740d0040c2c800044102c0040346030040d900406c00520580c00380d0320078207111810034680c8006141008544081d94003203500403144903805078004001d034074548903894241070088008604051008502e00118080e655071 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 956126357 1250 956125107 956125109
    0x1020904110313201002150603120d0c05091003150b0307090e06150f19020c093907110612040f050a0c060f020606030708070902070c08010510030b09030405030304 72
    0x8000e40380469101850022110840c4c252000076043d00002404068040d40d41c03e02069a01e0000c600b18001131128140031549d281d01901000d00f817130a00f0242006000600881e42c1c44070b0801c0303818040070350a41d40b40b01718030032080341c0c5480000e0b0302000a04114a083d1854011aa06003801c1040c031858075403101345141203860258005200d901c4040000d81140a204010009004041039036011481448000d0916196032000186250403c08099803510100c844560b88090500000303440e03101c47e40003451807031210b90014110100442c1d5111586034110000c28084003000c1505000c04c0306031540d00c058014121000c40c100b0140c03002c00145050300400c002c0c401294205800200041003009000b004d6000715210882c5d03031903140041184095000d0480180305080c04101d440c2000b041000903a0540d402034410a4140340c0b50601950140c00100c0e01c100c9045400a018542882000e01034406401946401f901d181071646159030b002d410880c50340c000300401c014903580081264 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 956127607 1250 956126357 956126363
    0x302030a481407030c0b33220b031203090d02011109040e0109022d090402030c04090507030602070807200901051012140a0501080304060e1003020408011406030f0c150c0a050f01020904110313 84
    0x7508d400c06104030700c3c0107401c403981c4003901407081c0e00b482140c0c0810000507501c00d0f110385c41143c40c9800c070300700228241c82d04c40d10f4101d01031004014000d00f074140741c0c01c040d2040c070409001040c1c4003041da02041600b0313141c90941280f140c4002e00f42482201c5c5e59901aaa000c04a5080c242030429400183d102c0c209018210300c295030740c2710304804200301444810001c541003001103440c1d0a0600780845284d03c004400c8030010f1084403c240484e400503940400074001400f0004144c0c00c02040c444180701000780003080c403000280c0300003024000d018a03113815018100e405d01506008850030251007040e00450316a40090cc02881240d0380210301103400d12080f50314150100d400c0d40260700078843d03604105680c0d420300d080d610708234000204080c080c0c0000e5040300d0001d42d1041e0238540b12440038400c15441030001c000c0a016030501800303400c0602d0880251080700482e5a500c914200040440202e203035004140d000751440c1c1449a00804009408820710714a040d070910201d070012540c2c01 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 956128857 1250 956127607 956127649
    0x30903092319030303050705030f040f0809040e15100e0a020d061805060f04111819030b0f0f01150302030a481407030c0b33 55
    0x110300003514400c8196440703000360020104003a0408049070610080c0030503404241802c0c0460b0006101c1c4048034420000d8904c00307141500d59540d1405184001081912005014400c580042e81d8a00c07aa0030281782800c000c200725026410328003030080d00200501d11401e80d18030104101a16603008582c0f2496a007401079603464030004500060a20b60411914240d0140921100007150ba00c180e010b20350494200086215100c10002070310014042c112048106001130717190f07038008004043d00c0c0c0300000c0030b02402c44804026070b0640700716584241da01450400070f002c082100103400380d4000a200036120a17960400c100d042c8010b41050900c41059130001c0010780300550740e0b100f0220017204016154085805020001c04d018130304440c0410b400d01100392500d01401c44510140c46c260b6600e440f080403044c400c0c242480d82090030305405200c1010360b400001644103004034402d12039201211865180c911141a0320550805aa0241c12000009185582d207040d402a13440c1060000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 956130107 1250 956128857 956128889
    0xe0a050d08070306030c17100b150706061706040209090d0e2707120f180b0711010204090203040b0606031b03090f070801091b060f081b0a020105040201090603090309 73
    0x8210f0040100c0c1c1d00c090305400b81102c012a00c800710036401028030420900702d450301221544c0314400c6a4030f140d00b03a07070f22032404080100810040c030040c0803954081c00c00001d0701642c40d440781e641c200c8060907035000380c0c21140822045150030208550441c4620000b0000c10860001c0a0802c2d5081140b4a1007054034100510f0070034404c2a1000400701c0c030800100d45818905006018145c04516006150b41041030b00045288039104460641d0324007222050320102c261141d50f805200900032004001007180000d00b1070200b40002c01c0100500d200040e903034549410500c2c181380000d00340c5813040c4400c00a000109500c10444410030f80407240c4c81e5540d03110b0448c46840d0081c89801d0b40d409020312500003800c43d05c19445400c02ea4007900c8640144403a00b80d910050300d04c0c60003110003203404d2440d456200c920030710101d540720f502c2c0000b02e04010340c01c003210401600301007002c0005030344440c1080b0841d640b04003028000d00c840d08083c03124840655018000c1702107402802e42e041c8600e03407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 956131357 1250 956130107 956130121
    0x90b030c092103070b15060703020615010908031306030f0509152e2402061302040605060432011b050a0c0b040614030c0301060c060f0507030204090e0a050d08 70
    0x1107030604140e02c044940e2002070345040782e8078560446150b0000e0720071905003030040c01d02c4c0c5e04846945505501034005562a05049040b0310440f070300480c10040b0600313020070701c0301e02040140f500c00030000b0003e17441850550f0040554121801124100d8100b03414410404000600005411010400d201c0e0545d0740800442940c4240c200401d880121652907655101d0403100308000d8481251540c541b51185001c1a00503030a12501003005138003c5c0c000944403070301d078491414114401040400c03000d582d00000f442540050b0400d180341c800d0b2440840c008440e90750304400c5c0100740345e2207100c1e420702000003810050400c522040d0461003840440b081150511100310003951000e20001d813152035241c0000c0f1600070f402400081101906080a11000281aa4802c1740510074140c9184e007421070448180d0040c00040f1003c80e00d561003404032121502900b440b4000d941e5006032034618003a040400c2e21091074000b411a0410314103c0301050010510a00b010702d541480451070700d44030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 956132607 1250 956131357 956131399
    0x9020424030f060b0901091a03070813020406090e010b030a0c12021c03080103120903050a12110714010e010305130602031803040810050f09060a0e0102130305070501090b030c09 78
    0x800b05020040ca442c030082000c040d401c000c2c000c0050280d071401592912661025151070f1107103041c54541c0300030b10000b0b00c082e208400c1182e21121808840507028416400324042d181942c02504010742c036044000e110001c2442031140c00c403411402402e01000980300c4030303020405c80c0102e8101d008189025002e54030f4507407012445146060b440807100d111418000c0c9540d00a000c11101000300d50080c0c110341d131164200d2825030390400c0142c0010002c43e51a080d0640d01c104e204000d010038401c0c2614020070a02090004000e0849106d80e031040c040001000d42e00c40d0150603051610784418022098154411400002e0780700c1d41c016601d889071031201a10b0844420380d510385200028010420000c00303d91550803800480c424400350b00e0703106003d1124102121008081d0b8040340c0000e40040f4290040c03011107900b840014a0324203668984088400c0b650416134007a80454000c10003540c1c08401e0000504903082d0742429030900208944c45485036801c1c2505c141c1c41c00b001000c20381250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 956133857 1250 956132607 956132621
    0x9040b06010225061b1205184f0c020a202704060519061d0c091f03111809010602030306030c0d141906060902042403 52
    0x140220010b82820030311202030421030045500103104840303850b0a400011180200b1700d64029025041c410407684226240d421150500031907081400c0001020349610301a40e03d08407250031030300004152000235010b49251510802d00d0b00810b5016518401d032032921a40c0074528503180403410402c10300b8124604040401c010f01810b12800b070040d4509451054403d00715401d48401001640d984800042840501414001d0800c05000a00022026440543c2c00b0783d1805465074942c000e00c49a50446101d500042d01c80a102428030015110409405034000001c0400500c1c1036801c101051031526060040010b49170340b9000e800c0140d000341c21000c46590303061019034540b05405220402c00c61050a00c0e402004440008901c0e41c1c4040708581c0708581c054000c1000c1c241180a020808012680544a80304d0083d403040b10000140490900200c0c401d8000c00c0c01413580c203100045503056032240188030f00c1040100080008240c6261000e99154071000c01100c0210059014000c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 956135107 1250 956133857 956133883
    0x9040f060c0806011b21090f0f0e2205030a021b030a020d080706020c03120a0b01031413150e0606030601150c02060a050c0609070f0b03040c090b060d0c05070308130209040b060102 79
    0x80c6c010f8403003c0940c40303400b807411954903220103290250b07200e00118500700980a903d442000202c0001c01036100300301c030094400c10001441001c41010745405056810440314180141c02801901c100d400c43c0700041c84456004034054816030500703078001403071a41d40000c000c049200104030181800319980c10741d2140c00c060015a6550109190b000b10016412980903ca4500d025144441540f03c0d2080d0703002400d82000021076515900d00904c42c10b441003208440c801d01580b525281e83d885400383c51600e081050086c8514180981054100301c01600701403041c00000058603040d540c0000f94440e0580c0540d1102ea40704194081114940301d0911307090f0403441b03000240078200c000001c4510894001505076500a81c80741344d24842ca01c41600d015100c050044014004842d540e40f2815400c1e42c02804189801c185501072003d0b02d00f07500380003012a2000c0754100501d60800c5200754895403008190390034040c150b0000300d6003840904042c000380c00b0480001c000e640200043e0250b002 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 956136357 1250 956135107 956135153
    0x2a020d0f14010b0a12030e061806040e0f0c1602040c0c0605070206010314070f090e0a1703011e080a110102010618020310080609071503060509040f060c0806011b 71
    0x180d0103000382d0180c548450300794013070f00341690000741803031010110f00304403a819603400421034070340310401000390801c0301c007105508000c0c4042c0034190b544c2d0004000418070601c43e2141450404401c2c03011503002440500006800c100140301b03d1000003d1220565044070001000400100708480d580c0002d400148128603141c1400030301500002d038941260310412401d1300c03901301c0205140e100e002074841c841c00410011802e00c034501c030540000342c6450b00d000c01c4a80310311482d00c5007450750001c9944000702c2c0200200500c9005102440300c240c0c1e5441500745401c5510340340a841e914000f603c805400c51005003282c2166a10039040075009243c103400413000d64440c200e07540d00a52055a0708130400c41d005200040c01da402040b861702c60010b00f400b03080b0719071909030b5000b0f1065507100e40c03204055030b403d001704d115950a030f0464050750041084440701c05035407134690100c0d04810707000400d1105802c20000741c0d030f904c0304540f401403040c521140010b145514000591340c03075400340300031405 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 956137607 1250 956136357 956136383
    0x3082506050a020c061005100806040e030a0c0309050a0b180a0306060924050303031305251503051b0a03020c1e070b09061801021614012a020d0f 64
    0x20805801508005a40d4411784840b0b49940f01c0c488002002e503c10940c02c8458540801e45090080138880d0b8040005440451201c5ca42414a402c5501240080e0003040d200c0348030005159210310040301030700051329020107003820640d0600981c0100030310030140381604c5a115072a0b448010360b10005542c00398060054a84410544d400f600d042d640040603440700700074105c4041400d01007a001c41d80007a01840c03860b16240c0c8074080f840e4080b241650b0f41e20a0714441442080511510144114145101c08840d4217017607ca850703540342030500008041c01e003000d009000f80304e541c801c04500c4602065990707070300340326405901038094402e890140d030141034061100310f10a01c069402c0080c00400b941d03001c41e100c2901d88100c0c0641c104444e0000f00c11311540040580490650509a005004075044021644032500c0805550340101038040c1c2488681078182d60410050400028a41d641c0210070405401c440a00c01000501a110b1540c40036118203008070b40504848180c0c01c401040d0f000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 956138857 1250 956137607 956137621
    0x3090307030c14040902090703050705041505030105041109030d050a090b04031407080303070509060d1b030905120a140708040b0c07030312090b06010e120102040305070911040308250605 82
    0x2c00b28070f1003a80c4011615480b56181450180318808003180d0081c091034068075218401c50080800a02c503806010040001240d00d54881c2440000c0d8011913403429a698100002d00c002e48030300403d408907000c0180040f015940d0045035040410016103800303529000c502004580c9040d00340e01010802400042c040240095910030b600130700002400c039a6010b55801d82150380788001c640340000100248407005407468010020081004003d00206000d00c28010602c244050300d120040883d581e81d0315241081001c0c484c00251605c4204100e04001c020031010f81490840d403d400440000050003d04000564050f10701400305c85c540b00c2d0b160014840070958406080c0815004180840104400410140a00d9010301e50103405600952603110055800750f50b10740205600000d0b418403151000d400344080c0c001940182c009084291a1060500448031041c0c41e10421481c200814004200c0e04401c4901c03101d541000361449020740c00ba4481a96040e980081a9030700706020300041d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 956140107 1250 956138857 956138873
    0xf0204060c050c1f03051b03070f020105060306010b0406031d0706090602010b0618270a020a031d0303040b09120f0901020d0c21030e0604120807030c080a020c0309030703 75
    0x1002d00c51400c48080400c6001007020b140c241c04400080403600c00004404148250803103600481010b00215541c2015a40281507400c111130301d00004401d80094401c25509000c1c2540100c02540581001e50400c072824101e0f20540c0114418503483c0c20724030342031020b51010a01e60b50b003500c0c240d818041c0c031140001d10003030091207403c00560070820b28031260310b0b0110440d5003403000098032071203031b483d50403d10841c101d42c0f1048080600345403544540c10146200341c40d2107980101d000607078400c0000e2026080710f04030050280920602e500e1910102400405c03a40c00a400c1800391410b0354400d8019403401c09078802c4004c08110208900c0424503400e0050001150300b40c00707490204842c130804803904c020344c000c06410351442098540180c5c200c40f40013034074135800f0304d808200041640c1d8060318041c0d090310100c50900070340c4590781186510404017900f213456894180800070030b002c0020124240500101c904507400204240007410420490380301d01001347c190360030b9590341d04003088 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 956141357 1250 956140107 956140127
    0x592a0904320702030d0b030313061214161b1e0c080f0d110102070c080705090618010608060a1d0108060117030708071109040c061806020c130f020406 66
    0x1804a001160718503201040c0c00a03807003010507900650412030010040c174080d02c1c0070701846801d4001000840444801d00502d179000e8840c0f9185d49070200c020b0300e82c42040390344451098000361000f0381072120480c0070407081000a01c01c1e20b403010281102da84400d18009200c40001c2946545440140c4a034074100910100940030300f044202e05a910340030691624580e030318020b4543c00001c0541c1505004041d060300c0307252001c2c0010309050541d84e940034030072031982218402da840544200321074580304d103245920400540d036018440001d000074204800060080d0824481042d00051060702e8488001c0000d104c03041060007112142c2da00d41904c400e0070701800c140e0340241400803036001e08419607140700720042c0c40214540350380d03620b404030341d0b801c04c1c00100c402e140e00c03240f20112940c40e03500d010b0055014026003180c0c5454071300080c01d103164800243c107458a020104100c44e940118440007103ca0603528a20300405084060000b03200364501e01c01c0c800d101003004640c807031340651080 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 956142607 1250 956141357 956141411
    0x102040302031f1b0f090e0402060a032a021006050a051f12050a05060a080c0307030b0624030f07031103040602070f1b050a05030102070c592a0904 65
    0x14246480328185140c001003154042d40282c0204039070524133100340d001c4010b00e144c103401c130003507040d910900c0142b8440e401a01c2006a0000d0121804607495104040c01068101c6028000c140351502290f460b90b0303003070380001c0a03401240e402c618a42c02000b00c2c0c3c40e41105600704104510306091500c0080c0030960703034103004220f1540045161080061000420707070740200107040300d9142d80d98040b0342d060000d10050f0020300b03228031018064031045a4042003031510f42603d8580c40d040c4185010480000c01c01300816003040c10350454004200101c039041a0402c901599a44641c1419260f1403080c60008080000711864150817a207014185006d175002100c0d101c0c0d00b20346e503070205400e0b400b4840003e0050312010000300642241101d03030b071403440c001000e01d072020348070282c5c507180200010030954000000d6607001405000450311028041b558000005810b05012241c1e07568809011000c49401001c0c07540d0210010410050f039945005c01002400011480e00d10940c443d001890f40d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 956143857 1250 956142607 956142617
    0xc030706090b0609040302120c16030f0b130c210c0f14060f040603151203021606050a020d0f0507051b030f060f190207061505030f0102040302031f1b0f 67
    0x490f5191801048842c0150f17096802410788a100d4072596480e940115004a4688519540d20042c00c1c01000604020740c003c0382054040c1010382010f08160030000c08038a078810080c640348002982e50101c07101911501030801040c14010216081ca448000d103020704060b0045100103013400544090100f0b5a010107201c0002e021000c3c180141d60141c40b01603a030305078042c4014001f580c840d610210111040074040c11b00c0c15941c405d00c00b680c160700c1000307500581000500c0e01111092802540c02003503503107016480c0840012000307440b0038041c440d1b00d040241d81d00702228810300c0782c4103540303245130401c0542d900540003a2120b6414140c40802030f00900507400001020600400d45500c520007854100003142d5070f02d01e103076440300c5842c808900413507402d00004010856034441c860444048410600c411030070304007014500005160340070b00e540c0c01040140016140450019a00c4203000c110090110341d095510b806002c8050540041d20b24100072040c2c5940d002c260014030342c40b40c4c0c5507 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 956145107 1250 956143857 956143861
    0xd02131502010605182701090b060109150f0e0a080114010906050d12140346022505160b030c040b071a1003060e06090a080f0c030706090b 61
    0x401d9003070f145039102d00c42c2d00007400002c4680600000313640316800780d4030304110310908081c107205807a5050903645038025a950b0f407140e0f1080248540609800c20000d0070184002854801020505005460340d02e00300035412408000050080c12001c0b00400010034005060b41c0b9a444940282003011a0f81e014880c03e2000154000c0716200c0e01054440140800c2c03039140c90340d1540b5110499505402c1c080040450003001614284405107014804080b203071084490400b80e603c0b0380c10090401e01c4820b002c1015140c0d0004107914600700c1c10a0645009610f80c0c4602098a00c921107014941045c00c5840d1100004c00c04003144084100085a40da01816912151700003c42e010460350054400800c110034880843c0c110080d103260b61213040401155427406c0305205101030305442000300501d042405004000036030141d0703460114110028070052901484d4150381c0c4c0e07804100546203030000900c0c0e00b43c01c0030010885582d408404216551045545061401013071101c400307030b42c00310800d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 956146357 1250 956145107 956145149
    0x110a0215071e0c1509091b020d1812020109050301020c16060c02030705010e0f1519020c0915010903140318030303041a180105090606030d0f0906080a020d0213 70
    0x1071010040f50050f20a01d2014146049180a10000c8015000340861800001225a007900a0301c80302a5981c1002103030060101000c0d1400410f0a900303024810102050740031010890003020454051050f007030360f1210b0600050b60804100e40203180c240d400025403030700c072841c005215800c54003070748100d04040c0d0307135008126444242070000030b6154001311000c2003158440c802e0b003008800000c9c07c44903141c0b4080000b440f040240802c0c000e080310045904108800c9041703120081c00344130f001400c04806d140002603000d4400418252001001e07100c100d03c60f900c00c2e007c01000d580e00c200010b440030000180582e89404c030010312400846c0000c20040b0904000c01a43d00440e4030030310100b000072607000ac030905ca410007860340020034070f002141c90301098240a07550103900d020001d81b0142c10618240341c10101511000c4003840716000906903c0d580c06400762040350100c2c0380403465911250810b0001e44184068103520074004030361003040740e00200d488011240d203a000307618542e212907 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 956147607 1250 956146357 956146403
    0x90d15050f090d05030a050709120606060f030e1c1e0309020901150e040c0311130515120a050907120506070314150103150f0e0a050703050c0703110a021507 69
    0x3c600e20340012020700104030701600640040d900101c00317040400c1007503101c00040c10250120001503a000d80c03103074410032446401510700012987c103171800780100010450125658207060050618000c0c0c0c070000728024a100342c0c1840206a04400b01c1c1c0c5c518032401c44000d000c0d01c100d440581c465444000001034680351500c006902c018030b91112000c03568070b10b0401c0014074606191105141e101e80c80d601d01e040900e0010a01800070680700c03c4200c1c280030074490002d032600f0f41603803103104c100020070068241e1000560f1010403c100032070540d403a00c178554100310013540004020b00030440341204021010544505c1440b00f5a4204040d158210102000810958100d42444072410340840d603540b09804c808124995120540d900356030b659407041948042c2d41c81100065412020b10080040500940b90040040c2c42c0910503030406000c1c2d850136124141005042c065507401c2444e90724030602c00700020640003825a4040c51005480800c1c0c1d9114800444001032215103920f0300601d0b40c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 956148857 1250 956147607 956147623
    0x180612020a051e0603090d0201110f070b0a060b0301091b0c021f051c09030908010606050301170f15060a1205070326070309030209160c08090d15050f09 67
    0xc2074841d0091401050282d40c00d14035504003048400c100c41c52071151a054020341c0960a5103004082ca1290305030000d00311440e0102d0027155002c1000304140d03416141c001d072910190010200c1c0e41589034404c5410040489038071034800b5081c044000110307183c680d84170300c40c40f8503108882e0417414445031040343c2034903640343c0c02940f0104100000b242013424490100740c104860905928003505081d620942c45900b16405040720340f2880c2e1070042580c811140310003031141d42e00070300887e070034820041c0c035030300050044c01e42c410340d4070050007075007041000400d281168031802d850030000e41e6003035030700f07503c00413100f80c0d0040880d00300c00180071a04040101600390414041c2a10714195681c440f4107000803000c4404a00060b000d807006044030b00010000d8600c01e0b164516980d00d5441805020500208900c6110a098440702c00403034102a4402001d584144581d50710100000000d01122068201511943d462103c205112960340e1015000340d03001c005200e42a40c1d010450b0b9a10507071 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 956150107 1250 956148857 956148859
    0x5090a1a0306090c092d1306080706021209060307031d010c1d0a0519051e1302040b0d09060609060b1e0304240b15210c070b06040b0a18061202 63
    0x1b00040c01660303102c02d100c5628040c45800c1d01030300681c100000582038401003c01041081d6120410080801d0400c12240105424000780103022101a05001140503154415010304400000500043d1003a4802e0200c90ac3e90711102c0550419401401c0c02498000080c401040c1c65151004021401c401425101000200784015144c1400c0c14400310541925408a120450444c0402c865985c0122090008500d40d00721072000d49003c00c000700c1c60300d04440740341c6542c8100014401005503400b00d40304403590201c081044003440c5009001068644d018400040c5000404a131003e8150000c00c07644d80816000c20400b84000d00c01c103201c0c441038400a05c00b901c0746621182014036040c920030b84100b86000010700c01542d10100c1c242001003200c46a00035000141c080701e600120203004170b240b18103040c4540da458518881c201c80c3c407402002500e007807030050005416681d0354110a66061307002d00880c1130580e60709952a8654101044041d0880c2010004034024001d080340703400c2150 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 956151357 1250 956150107 956150119
    0x72301060b0a2a141c17090709020a1805040203061809070807090c0318021c1103191e0f0b070e03011d0c0315040305090a1a0306090c09 60
    0xa10800e4030100c0380b102d44091500000c2c0c50f4003000c2d1000781007802605002e000138245103102e94002074280004400418103d188140410204a510040010007021000c100c803041d40c4038a98941d160040d20307440140d4040c00001c0c204c0402d035125625480301608694218082da441d84108416400200c860a4200848224400c3d42e080c01d9504650030500703a00c20360700219140c440f40da0a0030059040900c106403110307074211903aa81840341450814031414554100b0724182d00242c0038040000f2424050584030410800b4801c2582c4032010b402c030700030121110a00c0110510a000c000d560b000c1d5160300d8941810036402890000000c0308503030055410052a00c1075031180e006010190001c004c10520030882020381c1c81c01d114104440344407a50b11240745080c1803a1070300d00030303480089900907080a036030410f0141c14003022540151b0b060402545842c82c0c030010551301c4a0300ea00101030807803c02c103101400e042600003117001e020140c405917110360794800743d200644110707100d06401403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 956152607 1250 956151357 956151367
    0x2030f09060f0d05010b030711210a030b0a1205071502030f070305090303030a0f060b16080a1e09090b0d0203030d0b03010204120b010f080c0d0605070212072301060b 73
    0xc94608002d240346601c00d0546810500210030400031980d09070081100c0c14000000d0210042d00b02c020608440c5284005101c007400d4121041140d2031100003500b070088010600c410307803d0103508440b8104030050b21a600b180d0b5504101060000c0c00c2c2e000351214010000d010615001601d469206c035213654000758074102d50b0112040c07460f4003a5400740c0400c14144010f00403941e00b03100a40c000c004010000c21100d0100b000c0408a4145900031020408100304404c03118641070421880941c114036441e0302c880a150707060b00c1c0415649405c00001e500500400e8600d908030000400799101c5a2003000b40c846010140b0008450130307240a503040c1d0091101e9017441c05150003158440c10090000350510fa51100381d1001e040081b8030846101068400600a283d00f0f2116070008000b22401003e29920b40008030743c0700d4545e072501400c590b8891000a038407a0007000f07c40c10400e00c0c840c070079968800c03604000c06680100503849008101044111510140c14003401c401e681000e0b03480c1c2c1c944 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 956153857 1250 956152607 956152609
    0xf14010f0b071a09010b1207050f0405060414040f03020d03090f081e04060e0f03070f0509040c03020303131d1006030b031207060501060807110303161b03020d02070602030f09 77
    0x681004a007240e58140c1040c003c038907007102c811621301415000d0000705884107075500300300780c88100c142100a25030190307030308020540c0e6550050a07440001c0e2400070b0f00c1d4480002103070140044417415140008074000703100400c0301ca40191a1040d0190342950b20303132182c0c444101c082e280c11845c050a041d080d100200c0c0401c807907000805d0007110700d4039174448c5050310113100200341e0031035440307000428401409010305050150000d040203008402030070305107051030481c04245c4e545004090165980800150400c403d034540741c1c0c0616001030881341c5481c00c00c10301e403070300040502035001600d2030142c2c0e001c005184113801ca800b524120032600903803820804200d0007041000c0341c0030b50600c503006c020702806a90310f0060a40501580300070400c0d604120340949a0100a0300800030017002c804001c01030f801c04415a5002561452004881c900c09101100c003039190f41d1404410000306001c20f010560002070389010480c40d902525101c0d6980c075016a106d0081c0c1b0350310360910508200801c02 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 956155107 1250 956153857 956153879
    0xb0c0c01050a1206033212070c030c0324020702030a020105030703091505010303020106050102030703050d0209060f0c06060103050903090a05040c110609060601020111071a0411040f0f14010f 84
    0x55075242c0b400300c00c2c0b045070340d105000313440d040d13801035403521403050003e00007010351800a095074030760382e48080140303040701002695100d581810302c02e840c0c0049070002c2004034003a4480c00443c2c100103440031903526401c2062481c03c0d81648260310381850480f20048030380710700942d2406a0002c020341000502a001910360b5440108140308141d503070507070a4001113510005610310700e19500c00044a60544c40e0190844070190016410b6500034014000080e03404030868420300f0881101584401c400b601040c20384c000d0340a03000d00000b0201c0c41c58502d1600240c420700c202e00036a030a0000c3d8a400308029124401d04410f030f41c01010301101800715040c00e07003110400003091300d05000241c03808042c00b8100302d811b9605500d00e8200d2002d0003060740c0d0900840501d0780b013401aaa150100300c0d6a41e080e80105a0300c0c02d0503030740d08680000c0c240034140007030300300044c4054803d011050680260900400c0348010350640c0c85c0c13924280c845512407400455050b15281001840d0090900301d10f603007 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 956156357 1250 956155107 956155117
    0x1180e03030f060a09020f090405010602011416031409100c080709210f0c030b060109060c110d05120a090b070c12050109212706030b0f09070203130b0c0c0105 70
    0x3e00310201c44c07070024003000144014030200c0b4150341034684503c1c0e010204800e490060717010b041168140080c441030304d502041301c160080076007e51340080c0c04c880390b015809041604c3d11120445484400c2119942c0003050b4080c601c8004039080041c000049402d0340c02a01c00e40b08140041e074000003d020010100c43d0700c03d540304a40504408143d51552413500c1c11022000c2110300d20740f00712040080001583c1040d812603002d090514a4500b004001070001150040180c240074580e140d00c8255190320404111a80d04581510f110312042c20b0180708a5001d60b075920f0000c0c001c2d810010750907144130b054410b01a4082d010301c101601e4139460b10040b061421f130945003950b80d020a81c0025001900290342c690303451003e64034200403078402805484614580310180e44120300311025200d0100c100c001940e981d800c00207050440740300810008003441c4050f5412482890a02904680000c0034050700301d64070f06030341941030300e80e602003216000358582107242c3d6100e82c500403500d43c00340340030340 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 956157607 1250 956156357 956156359
    0x6010501170403120626460602091512150f09100825090b03120c011401060c0b07030e030d0f021206010c03050702060d110a0903020411090a0b0d110f0301180e03030f06 74
    0x101d24401715140032004011fa42c04122030141e0300040b01282070914444640c0074803d44e440450500d2602c07105804030202c01042002d2005248514268560701e410383e0000d50400079001184504e0f01ea100c1c84840b003483d0081035558402c2501d401501d1540d000800154a0901034488207a40303080a46405881c0b61352416600d40950140429400780c01406094411303e01d000104085140040c003c02c0188103030022410400c3c400061804941d20b0b240c10f98000c50b041c0ba0000b0300e0401d01c40d140782036020705c8101c000740505140c03088100e00750301d4016060079112003600da125612141d005448900c05038000402140003800300e2805450305c00040d040202d000340002c25020310403071030712072164003580021011500048061003542040e11840305c441d10981e464030300e88011440000c00b140d8031446080424540050007443c41100b0790031920212900580c4980c8030500035641c00c0b110b810034094080401c180d16000302c030071102801686000c0309208003462542d150081c11040c000c00003070500e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 956158857 1250 956157607 956157703
    0xd0c0201020f0c160506070b04110f040207030302180a05090a1104241709070b0f090d0309061403070f0503070e06030702010f060806010501170403120626 68
    0x80d8120b600b40c800188404086a00039080e4a406050641150282504080d014050901c020170002d10140841c0d47c00035048a078020000c0303410f00008180c0c030740d20720110350040d00101d048410181c01d41c01811307040045080701c0c18101c1c03152703050180b144800d10445d50b01c0007010010a21584503503001e90700b4040c0c1c080981d49007070303160038a1400c54004231008060051441544090791903104001403146640e07001d4151050400060156880311580070b54000c2c440d0000305004003001010444219000140c52038114071800d0501a0000d20244505004245140221700c1c0c41c0d103511007202d1241440e40c451201c170b03600003c000c8805403c0181440c040c40300d00c0d00030950544c3c60a0255104040c25400418501300c131000d0311040d610251b1140c0000e03403215006004903078000094198840010340c0700c076483d66560900b11141d0704900c1e02d06076070519080740420780716403640506070101c06008054440420a09506507900d00410880c40d801a016000502c0124103007a0b07480c400211a1407 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 956160107 1250 956158857 956158867
    0x612041e020603010b0309010c111c03090c080a02030d050c060a050c390f0c040c05041203080403030b180403050901020708150403090f030b0415110a110c0f060d0c020102 75
    0x80341070b540c000e03084004a100302100700007141d00c00f4042d42042030751500e040140d401c0c5000c05036545040403010107036900341c007504820070240f1070380c00840280c1d0018010721081c8d0761030034035641310407800005034004d010b588410801507008204541118400300010981540c50400300002040040c00802080a0412017111015903001408140403030741c51811038070100300c0c464031862140c8041500041e030030070300b101c8010070000700d40c500c1350110565020500424040044030140b02d26006104084d0b04030862009142d4080300c281d00c500c3c031a40307040003400f040000700104c40b007010980902c0140b080000400080c07041c0d0151040400c10700403a61010f485541c0c0d1404d06003180d0710580109007907001c01c001e01d5440348034000280302030341032200418215140c14038134000080000d044041c50240060034980e20b0343c0304500700c1601c01590340e1298400c0c0030003860700b00740b42203240707035885609034075501ca20b08040d42c5031650301c0c01080e2a02e400050005100600510140c40007507541c02d2007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 956161357 1250 956160107 956160109
    0xe060706020d0504230c13110906070606051302040305030a0c02130f0515150d05040c05090a0b090a0b030309210f03131a090105130510030603110612041e02 69
    0x10f00f0f01a6100d00c01c21400c1107107410542d20a40241545054154000040040315440b03440c04503007085445280800c0f020046444542548100c0c45060340002d40007030788100340f05460740028150f030f10445d01c01140e4080c4003000381c1a4080ca0002520f1900100303c200d0009019205d0180d180348003610624461001a480f4000c40340358007042009542c80c0e1707081001c1003000e203049031240c2c441210410501c500340c010010541c015808041c1748655508041002e01500340c00f000d0003480020114221403910f60b4400303026142c0f903500f190042c103a40e00482c0e08002c05015044003840003600440c00c0403040070400c2800b140c0503000258520501800d00c5420b00140819000080610700450f0f88000c50034240d0600102d50307010099003007042140c408080c801d1000c0b43d50b00c040901c3c107542ca0b0b40524540c08810b94541d440705034048241d1092080f600c1c0c264214104407805a070405507200b07801c0081c81603520884200c250140c102d100014001200003c4130b91140c0e124580460700050b96034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 956162607 1250 956161357 956161361
    0x2603090114130e1e0a15030b0711010c03021b010915090201030e19050d030506010c0f03030e0601060216090b1309151e0605030d0207180f06090e060709060e060706020d 74
    0x74a400d03526840c0c1d201c8001d00000213100c4c3d507400400040c0204003a44070710b8600b05000142d4003000381119151000b19071014410720083d088600c6150007001000260003000d0000d50200c43c002c0c24850002c00e5510415206100f51407000303400400b0100302e10004110680184030400040707060558401d0311040280040140c040d0320106e41069001d0f04006042141c900f00003080014201030500b000c0102999000c5085085180e00101d0340d0a188407501d41030380035011a0440881074400c45c000020080e0703000a025000420940a00500a44540d40c50064401026216800000d002407941d00165598000504640510f00001034980e41040450a607090103034005152417100100358201d003a0b80c45090700030001203000b440d1401e4101e00c0a900d0310800e1041603004940e0520b0054456216002034400c400480d004000d403030f407180441c0c0020041d410703401d1aa4455000081e400c02c0c0640c90f41d1003610324903214a290000510100949a44001012100b1580034442d95400400c98 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 956163857 1250 956162607 956162611
    0x7080a0b010905060a0f03030f1b0501051b0a140703031e0207151413111507060f0e071707090c0c0212010b0d0b1b042603090114130e 59
    0xc98545000303525000c440340a46030054041e510070541c10900700907551890500000300c9525081840c080d121403030050310007181e901001102c0400151201b4100101940070b54851a44112008200000b04d410030505005103603207800443c01c20410b8081034581c0c3c2c006002c0007072280c5400b05031035030300c5421910503281846441029507004940d01041002508403101d80c0401d80e0303820030040b180c107021222030340750261001185040300815003080c4119001d11480000000d0503100c9449040300c201d000641c01a40165042440e08105031a4031350760303006441c54050480001d20200382042c0d0494001b52482c0071807107161182e080700248101103801203003041c214984910140840a0041c07200101d0034060101e01e6074544030170f1150359965000521003454000b012888a542da11892087c40b0810303125441107040c0c0800d002800d10300d200000409000c0e0355031004100881c12411b25520700811001c039002c180d450088034810b40c21000582a80340300303503006590b0f040c1d440014041903401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 956165107 1250 956163857 956163863
    0x140303070c233018041d0303090a06050f041113150b07060b0405040b180a0506090a0317010b07020d15061e050a23030307140318090402010f08060307080a 68
    0x1060a1000755580d0f103400b903180c03c4841d01041490700c81607010210080c05200d40041c45503540c3e440701000082c90006240554400740100d9035070382091030f00c484e41d03043d01c04821602d040c14070340007a5004000074480c44c007860b804001e800d42c00b10584200b0014041c003800f100d1145544590440311a054400700c1d50040035207080103542c4514904006017590071004c01c440c0114201024000007810303a2529513440061504800c14441b00c0a81c030342c0c1890700c2040081c1c80c3d4401c100078000e0340d0130041111012184a41c441640d10f02110070b4000d8180801d1049009441091000401606103101725017002031180319080ea1117a405c01c110700440b170040d001621b000032883c1880c00d8070014602c85030050401110940022454010000703c02c1d00120000035600c1004085460f007618108292502240e104038040c201c44600b401c010f60300e4210180c2c0103404070702450408203604082001034011074040c2d4441c0e000d8104680203886400014240c50b07014810443c0c001070803c0b00b8440da2001500c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 956166357 1250 956165107 956165143
    0x80c0f1915020c060a0b060405130c08220b0c160b010303230f0a0c021c051606051b0f0a0501090c061412060d0c0b07140303070c23 58
    0x251400e04900052044036000340c07451041202c2d031000080018240d074005000d003004196044c121012407418001da601c00d50300040c80e2501c5241040c00c030742224903800426070300d07010f103a42c602641c009100da4113800e550b107541c003515048000c502d0501180e54030003a000b2402c4d182040303211102d00003030003ea00a071070041d84800184205507104e0041c5c0d0490420301c80c150000c42207001d040c807691041d6405072080e07003030004400b004c07140900000100035800511a8080900390810302100080c400b000711307101d001d5400220800c2100c035403443d040d80c86036500e40d41085101050110240d001d000d468556108140801e49110310800000085074852800480c0401080c035101141820b03039000041408a101540281e00300e003001a25684210b050229075540c03030344404541003001c4810040c10352041c6010118188103c203006240c400d100c1d00b9410444c40c40503040303071740301d020031b071248030000b941240400c01003248450502981705260302c0e00713030921008185091601c012040300a104003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 956167607 1250 956166357 956166403
    0x13050f0609181f15082a070204060305010c02071410050301051e060d140a050402010f0c2f1002070b1c021b0f15010315051f14030c0607020607080c0f 66
    0xba40082183e804c0b061800301c000341b05104080810b44542540d81d40c0b06804c002151034015513443c0e800c00d10045400c030008104800e4080c100a40303902c0c443c0500f850816081c0c11a41d1542030015a031780d04551641e94003425a401d00c8200b0101c0c0e19003005941038000b6001034079440d5a02d03100100080c143c29000010415080e1404d82c00f6850000d21104406142c0700c10040982d80214100702420518506215848a60300d0006a0743c0c10f0300d2641e40883d8004031502e005101172060010501204403981c845a00802c44201d03500c00b85405400e01c82d407010710461a0518610001c24403503078410f2400341c1016504800c140d900d14448446601039444490060f1400341c06002c40c1c10502c2c2c448a401900d9810b5807102005081000750307029109540d080028004402c072203018200004003050503091a03074a481e03001c032406410400b54803071301920441c034060745070020440c0c88040c0d01401003420035049484810203a040400c501e020303030140c83d6260026120500183c0001442c210700b0f00280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 956168857 1250 956167607 956167649
    0x4090510021b030f0a03020703050c060f060406170c040b01030b090a050604060503060705090d0303180c1a1e030702160305070312050307020c1e0613050f0609181f 72
    0x14100e41014044141c10411004c9641c8151a08a031100b050500f009641c4154601e401c80e411300c1a4011003245010f110300380715583d40c42d100050300411307045600340816034840f440144013070034410070ba1031031798403d0f1031100044c1003540104040701e405043c0040d00491000100354982c008954611010f0340d40c40070081141750510441001c0c200c2a0000c1c00c0620744070f94050254031604513114400c00810050604140c82a000b00b01e4081d201031076a08180642e2070304d85a000c0b601e0058041c1c0703035052010b00c5802030340d82c0143c800c03403d500360620b901d020454102d102507a1010b0310807001c41c02081052040e440403554800019441440201a07240c41c60a183e2218101d220344c200c1080400c0050101c11940003030076107401081110920b01700082d610f0035090042d14001641d402442c0400d036400501101c400030030440c3c0050750035040e40d103421b8040140030304c50140344581c0041c1082c10150751843c4002c40941c0300310410080f803500319002e00f0341c68500c036040d8012035006404a080c0880 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 956170107 1250 956168857 956168887
    0x601080d0302090907050702040f06092f04050111161211010f0e30011422080f0405040218132d0912021e0a200409051002 54
    0x340215180c11418090700800180410302c001e030140c0e04001c000304062040d562503a005142000d501c1c0b008001d00e0b9680e14101c00900b800e5503461502c1c1005150810b00000a142c400b046402c003800d101d0710742400c010040d160440c003c07100d55614420303d0b01d01940d608242c4910005080542e5001071036a8080c41c14070007000d0415940e40c108903210a9045c2195004103a00c60b13750401c40b59540c200d440003c4180481740700f00c0c001c101c94800300304440c4d8a048190700c42c440b44042031941006030768078180644540c404c4010a01950130b90f940000000ca0507801c09801448030303140c3c06131302c0e088c0c0d50f400181c20307138110041ca07180ba00110030034a2400d10317200e010710585014034002405980c60082d0042c500b50320403856109010355480d0310048680710b56204906c50340e0712180441c0f5070245000d00039640c90a00c07807502403148144c103111500200001d1001d501c15400100c18a201c1d6500080505140c00c081c400c1d90069250320f403520006206210f0700c0c600c1264498016200c1030f202c0c10281c0703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 956171357 1250 956170107 956170123
    0x304051c20030a03300b100c08030a0203060d050d0216090e0703020f0f041a040501080f0d0c031403150901050105040b0d021308030309010c030f0501152d02060108 72
    0x6200641c050901d62510041800300c11183c1505005580348403e2a214808100c0c0f9141254a980480c0c1780d4000c010b2203030b004030988003040e00c01e241c59840c425420303107881140d0b01c0003400001c02030001401c802c0194000b96030107500070304030070303400344040c0d95480c0381c80380d400070080146c0c2010510a010b009103054642c002c1141320002d101441000e00d91645511040c00702a003e0031f42c4200b03c500316101c1c1405600765460162042103c03080c01020303114400120000c0c4c40c41070b810f08000181002002800000e00340984018184002498105403171200704c00c031f400c805000005541091240c00c090183d031282c1524601c02040760080c804204134810140c00a07410700c075081c4010b00c2006081c80544074480c80705100166108440742c1030302d1414841d60311030702c624030000080064410b07040d0410b445000140d14103101c0154041002d0302545d50074021800030035040305031071030400d104a000081403240392400038a0b629040f1701c00d400181d031400840c40540d1050004000903402084046 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 956172607 1250 956171357 956171393
    0x5040e1f05061b0d0e090a0c051c14091f05371512080306030109050106031a0c1804021606020a090302090a09230c042c0703080901110304051c 63
    0x4169070175150010312050005070903820703880d03941c05105c410b26001e10216050030754000300040340000680b64100c054a03060310000c0b03e506a01d00401d00002c000170390810400e0f0451407107503c011103410064000d0600510b510400130441e618402110f810100d1400c40404084194442e515013581800070356521340c0c480c000314403203240100b2011000c1c401c07407a10151f2102c042e07941d0ba15000d000074050711180d07101074495441d1200000410403101c400f4031540e4105e80309001566a03010307500b0001c0c010f0f60b800c1e204002414410680d285490350080544030b0241b51125095015a2900300072070300185000008030314400000d1042d0701d400c1c0c50309a03020322098000e0100c44140c0c3d464140440b84060303640f041c1d045000c444030002c0414401025800b0028108100726280c0f10012080352040700d1100030f8102280c010070310004408103602003503076000741807140303411032540045840c560380c126040d4050100303003c0814169140701c0350b441c0d03200040c01c40e400d4100e00c509000007a140a00102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 956173857 1250 956172607 956172617
    0x20f04031b05062502060c060108100204030213110d0f0507030e01050c040504090c17071a090306040b10090509010912020f060121050607020d0306050105040e1f05061b0d 75
    0xc12441d0f40d07001c00c450031811844c0380c3c00c103503030982c6001340c10070b852a070030003507001d580403131100145031000400a040301c0d542005c460700c4214507031502c0100e1007680006904144e100d0b030003e03220002508000c0f4000c0c0e810241524045003044040111418503050003446d03521901072100e0b41e94140581010002488003c00c02030070f001c40d11800c94411482010b00903031326006410b003444940401c410042a102d07542209a40c0d280c60b8540c0c0301c290b640a81c0d510382d420510f0307101c60341e94603030103403103203018003a00500581d1150f0305c2c0d24680d0300c001010802004000c440110b100c40c41405035501030398440c0000304402c5010303c0d221801c01a00002d601c00c41d0f0145440c1c2100f0100001c095045400325840080003840c00d07841100c40906070070020700944241c00600c8802540001c0141c1461000e5a041044940364001100d1501c6244107900150f0b00c5c03180403074400710030349500c081c104850b40c00040a00e9031741c00105015802484101405070310510024480040911422141c42c600e4604 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 956175107 1250 956173857 956173859
    0x1407030c2f1003060f03060f060e0705040501080705210613020d020c060f100303030b0d0209010e040b010603020a1d0d0203120d06090c0917011d16080d08010324020f04031b 76
    0x170480c201c02600c006001c00e0386914040c10160350303e51007100900868450500240380121000d085035002d4862140095264000103500511540c269003030b52880749180030190000e580313100039505000c1d18190384802d8004d13045540c19010700c002d10300c00098110241c3c4600140606500b406401410750b02005c1c3d80c1000c0108164002100c02d06595145c240041e1080c4142d02146c2000d0b59080001d401103200c078000f0900c7c030402c06c0400e119901c1009a9056a80c079803404805a004920007803001c00c030180306158406421080802d0105005403d48240000340d8001900d0300802644400f54003400045107503a480c0c2038012034014201d140c4050050712060100140151124410301114005000444102040a4100c982040501071801e24090800072070075498002510405001404024001403203180100b03440c1446120754072161443da1a640b20b400c3d03001031280301365a180a00c4c02d40c0c022204c02510250044d000c04690490b2618107500e0101c0204010803000d903100f18a03400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 956176357 1250 956175107 956175119
    0x60f0504052701090206070f0210033806030c09090a02040506070b0c091f17060d11060d0f02030106035405010f0c1407030c2f100306 59
    0x341c0c0038598900c0400c081c0c4003661511030710f0061039043c1c1c2c000e50210300015202c3c28801102c4070309102130b00071034454450b030000d840241c0407645102c000028000580a0f024039656030300300850400000b03000b400d018840240002816944211200072341c640c40403801480034200445110b6000b2032102d002c510786801c0100080b46401618002402160320000103050138020200750782c0076501c0070300b5001c1c030341e0421b5484002104070a002100081c1a010742c0002c920076044d513440c06008054540c0c0c11040040c1c5400e1403105c060b415490700100100244241090544074082c0581d0010800603269410500010140e441840a90007509044495101d0001c0141e1404020320308001c000341203041000d11100c0142c560320030141c0c1240c5070039800018000190400528074008080030003241001c0c02d4191846000c082e001c0314070400038010100060302a640c000c101d00c0c024800301000240c208242c100e11102d03c0149422111449080c07801d904200d1071000160301282021302189003064 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 956177607 1250 956176357 956176381
    0x20a080d0203070507050f06060f06090627030601060e01021006080606092703090a15020d031e061d07030203090c01120e03130311090f0403080603070b030901060f050405 75
    0x201450344103540040454000ea00400c116a072156200060b500f4803084c2694150312a84200c131641d0180d0882e14450781240b500c0e04c100d0300c088a006190604006203018807903813441846401141112003d00000001c1d42d041040c1d5000380036507030701c0c08007041048000a01746960f00b4800d40303405060103000d100312000450050751010301556440b019503940600009013180d8594800d0410340516a11034007480007000070120050282c412890003a07036074046d1030100032004880c8006822903410000305074840d4000000c1d4001240a1481108608845604403001035010b0080f1002500c1034584680b04c4459140d03108a030b50508505528080c00c00907259100e1601d01d60400a1000d800041a0000e6210880a45080d800c0300e441300111950140c0c000401c4c002550b0030000a24030141a18080d294148150441c403046075064607503075801d031019180608481d505000791100840c440c107401f0061231240303020200100343c00b440d007050202e282000340c0000340168100001c00040d46101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 956178857 1250 956177607 956177617
    0x303030b03030f030105280b09031204061b080706020a030c0e030114340302040305100501030213020708120705030a0c080c070f03090801020315040f1802060c010605042406020a08 79
    0xe503030454489040241c0c883c1c7e043e11580903404414446000891036a000d5400340028000c150101d4285040968041800c2c1c0100e114902c005400044a0214203c0040c0020a420301c03c0d401c06081440650310311007603800140722100040d0f80c0b090520a5160f0200070041081002e030001c00c94146180c0841650440007481c002c046803451a400405042c560034900040c09402004112003101540040c0603601c10711042d01c051160390342412843c00705205213412280d0040c0001222150803401801a4008200a1b10100418048500208507940082c0e20aa110759202030792446c2408000084410754440c0350200b141d10820400d008400c8000c682d00540c000080d42c131507405514044800c991543c102c80110f500200900640e54440c40b400b0a110f003084405011800d03e840250302121032880098100c160354840e401c0242c140000100700800d043c0f80081101a141c0380490143c410625120150040c40544c600800805803900c1e405400d151000d80051452511400040e001d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 956180107 1250 956178857 956178859
    0xd05060d0506070518060c0c030705061314040902030f01050712020c06060909030c0a030c2102100b04020412030c060c111209041d061e060a06080a090f08040303030b03030f030105 79
    0x200007503503000360002085c0510509002000256100c41c1450200e03158010440d240c0d01a20400c100400c0928000c0c4c29036001c007841c0340c00c505105145c402400c41c600950b01e10030381c00603a10003a40025807410b10020074bc9840708800810203041440300202905419a140040c003441400780703030718603500440d502d40c0080301210301c99460384074107900f02d0035403190415000051040001c01801c16030003030421040140692074507951002c1110030000e10044244d4202c1c0140c01202d00584c0413034440d807000200c0040540014102616a4807100303000805003001e401186000203440c040020a001300102c079501131070a00d0740d0340023041c40d40740d0702d01302c00a80001700203004c03034000b080307172502e511102944080c010305111030b403081c00d0041d4176000181c070b1032002024141c22103004018003142d404e010b49005005110b44500d013450440b030541c009043d040007a520790700d07100e000c2216444c03840295809a105681d5441c90751074090b00300c4030f443d04064001d4000740600e560b4504420190780c11600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 956181357 1250 956180107 956180117
    0x60912081c0603030c030f020304030c05190801020a1206080a03090e130b01061707090b030601030e1e0c3a020d12050a020c0a0312030c230d05060d050607 68
    0x44410800030403040710715000860a151060000900d035109205002e140c2c000d48a007608a029004201d89078802c81c000900381e8031904a003044141801c1000c1d0b44801501036103100400d0701d03041e1107801c0e039010541d2403002610755911513a515a540c802c0200030319105004001960305550042c105101e54440c40540340300c190300058156400b80b20008205134030100c562490341c0c4468024201c221030403d9400e03000401000611545d005104444c1507409281c1c03030500359500c2c0c00045010b003100c92007003403050003118400076841040c005d644041c00d046601904401d81100103222409080070f483c4500f000701c40c0005540c50854050803c0d090045003c128000c0b0014008a10a9124000000c080d00e020944101502c2c0e80030018000703400440c0d094850402c003040c100240d42045001c060111a00c0e02c0700422600d0003035212060440311400d0114800700c214840c0b83c050001e19100d011441380009042c20300400c80d108495121602b21001a030450407a124503950310402040b500c2440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 956182607 1250 956181357 956181367
    0x810060e060909070f09050f0c12040602030606070506090a03030e0d050703050918070c05120f18010315030303141b0a030b060d020c0307121e080c0909090309090106091208 76
    0x10743c0c18031200c4041c0542000a480f501d5881010000600c2c00312004107005091002080d01c07082d002041310f22034600c0030903c0c04e81c0e807201d40302d5400941c00644001e0703000d1005c00c11840010740038170417076120b11840d50143c012030700d00d0700300582034a803d1104940281c03c4011311007140c0e50010180d4103441d8040c503180e0307100c3c041c16001c00c2e42c803c44040800d400024080803c00310035030011243c8442031280c001e581c4404600b106041c0b49026900c031003031303c84206214810b0000c0c038180c0c0514150384145404646282034120301b194510607504103900090f210a015422000e0360626642c11080c0400340c80200010040e505569001d0302407408101a281c03507132064280c4e99003041c0d4405491940085545910500d41c0e00d07036940c400942250307a50303400b608059106001d00000c0f0b11100203040304551041c4e10071070454203081d000b0200d41100c5130030f0014244607140d54031402c0c841d800210040da96144507030104640040c05a00c031404101c0c0b492001d200f000340300322101305203e5028008503221 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 956183857 1250 956182607 956182621
    0xe010f020405181b0d0e010b0301050108030a03150f060c0b06030607171b03011403152806080d05270a0b1e070803010f060c1a150406030302070810060e0609 69
    0x44c01500c446065011000724480b152803006070b202030320001c0000c0c0204508540d100a1609070f4a092140001641007030110013050303400384d005051030040102d80003805546490226025620766004000001e0071081e881d81080b95202040743c200c9030882c000d150504d45088001e02210f0030581240d0301e6411400810b00d80c01810f9000581002c1406403961a0361710b07100c0b131843c5032080d100214842e2140d68501122641418079090081c0c2e6034a91071450107059034562a41c032501b2a03115640c0503540c010019808105000d131005c1100079a030b41d036a5a0325201c1c0c0c0705418159040c0b070b00790f004d1550140fa00040d0f803200200001c8401007507103145c80360781c0c02100240c8120b801001c80201640012403408100343c40307000b18182c40c000945000700d19100c0500f16042814004000c012018054800a811120208590b1301403c01ca200b40c40a24405000c5415901180e0085000d0b03407201070280880300052154190f040d056401c10445030b840c00700d0110741030301c01911041c059000701000c0760381 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 956185107 1250 956183857 956183881
    0x50a150f0510051c050c0a02070b0c0613050a06110306130e150717131a100b310303031d100e03070b0903130b0a0507021306080d030e010f02040518 65
    0x15011070b03143d040000c1c1c51b0134170400c860742d8049551035006000d0400f020075640c4420085d21401503035680103005d642c0d1741198210768446e122406650500c50074004100045150003480806038a00b0303031240c2c40f41010000c0c030121000342911140300300d0030301c80ca010b03080031700103410011a880307204032a0b41c1d0340310380324161081c0c010003000c203005054032010030055134490485071140520448080c280701c16441c80111a81c40f00395034881c1140b04a950401400000c02c028006608802d03000d160001071a80c203c0d01c0c80d01141102080428140100308189501485000d000041010000c0c1100d0312446899481361035150210039032996584440c68841010010f90f07a1544c3d1003034440c407a900f412018156207410400549140c41100f85012400c441c0030025290b00e45025142c082c1003094640c00c02c07130280380042820b101203945610004259604120641c982c041980340054405601d4820358207503034008102c9650107004102c208203a441d2864181c0c480003212198a01039101c070040004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 956186357 1250 956185107 956185147
    0x602120c1305060712030941010605010903060c030204050a030302010c0201062702031003050f07090c020d090902090325140402040f180f06032306100522050a150f051005 75
    0x40d00e00104070b80e01010144024954008c0c0140e44d80a2102802c4d02e204034266000c0c1c1c0507503400140045000c1000800c02e42214001d214a41000f5080c07681741c20104448005507031050f00143c0d11400c0f02e4000c5078082c802d5502a0500c003c00d01c10410101440d5003440b00b0300e11101c0201c0d07a0000010b2103402d22085498099680901902d0030b07440c4403803e150340c0d1419406604545441e1001c220450303800050a0450802c035a242d82206a1a054904009402c14110307240c144c0070b4840540894a07004000004448040300520012800c0003448076983c10344111450045104010902141701c0707000b461000c4410000c00c0c118981000109040a024020b01021025050000110411203410352809512100e0070480340e50b2004003d01380e80d140c1c1d090310b901d206400c2c0a8004c0c80b035400d00c2d2521081340600c0c4c503a00604848940400f4088890494000c06202c0d03132880000c82d181120066440100340d01c00d0105082030524002550105d02d000c4d40f031040c4100082d020015208000d1561 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 956187607 1250 956186357 956186393
    0x1020a0512010807210f050f031305040e031206150c1c0806010c031107081b1c1104020313060f060905060a0f03020d0602120c13050607120309 63
    0x154442a0118024105030441846210001108000810320140020308202111030b04804a034202120403600c9066800090040d9510007948002c0d4000c01c004002d010b030f65044e101c0c01140c0d6024280841000c180d400d42281d44101d040c40500c0c0742c0c0c601d0000580b50f094212001000300d0f0340311030b000508030f0070076080c400405c0c5d040801d0f000d52114011a41c40362505401c0c1c520100d1091825084800303110403580c0794003040040b460707500030a01c82c1c0703280310b01d48130814120b41e074483c2c4444200b0f00d00f240e40b03140442c1e40c1c0300b0089440e0042c20b102da43e500d414210984069005011552000b5820f59110340540c000c0d640400040e41c25001c1140c0064a150801000c00000081255441c003519060003841ea055081c90046085400d14540d600d00f22034512880307901950640e800c00140d01d10000060b61195000c4c000404000d06d0241103c0c0551190200306a40c1d4000440203021540d00ba80018450481484540041101032040c180c0c40800b600d000903440300300349441e00d04151002d100da = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 956188857 1250 956187607 956187611
    0x22b1107080709110304020d0f05030412080d060812030705280806240d021810080412020a08091306150504050a140f1005070516061205060609010e0a0801 68
    0xa1000c0e404038003202500d840f101d05004003800c2c040c2c101640d10003500c00039000420144540d001c515000d02d01c201c89442001560f207425075031201000342c1c424016069688200c00200f101c1500d58512840c3c2c0241001d00151403040096211800507010050940d03052101c0007651100400400c001c40b801036010f14001c185c4500c102000810140701102c0c21809121071140c401104e000700c0b2803c10920082950003031600305849030f0710001c0d40280035507009104a1680e42c08165440684881c0b441d5000d80d00d4040034582802e0229400c4001260181590801c14140012030644000c48030310500517104550140c584600220060160b035100700d02e90f200d07500704603001540c044000d108440c81200d061107980c1d19901c9105810340ca040c1c07029402444445c0c0004ca504000a00011501c1030b070501b54201034090700c500d410080d0355400200c0d0000c80380411b01086400c071484d1040e4242c00c2c1001c000601e41140400c60301d104090103036050000a2500f4a402c1d41d0f4808030300c001d00500700007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 956190107 1250 956188857 956188859
    0xb011b05010b060a0921020a090209011209050313150921150203011701023a05010b09040c05030403092d080307440d05070f0e01022b1107 61
    0x402008171146024240c00c6aa280100751910310038561100780c41500200031070411031518402c0d600035032201d20042d061019640010802e43e07420710071540014000e2025665442d40030380c503c0034444a5170851195018490628404c141d4040241c105a41b00d03089104002c041c0111583d007442801c000041030031210001c07075001c080b103135006541200c003120204140e04c09d5072008207080c2c1c010f0142081c0b03120f910302c0081c0740200d0310004040d0701c101c010042d64001c03440c1c0900402a60b01c01d8010032121140001c01c031046082c1803090b641c9500040c900340b400c40c2801e9400900300702441c0f05001c00391b0001c4410000240c1c154108036044c040160305600c440b541c41c484943c8079000300d4010381c1d00c20202d0201c203040714184038548400c032020036041031029a50042000317080460005420f01a402031154200340310181c030803c0d0149950703458820080a00c84001072072051000f07856411500800454850240d0200316000307006c1040240000202800e401102d41a510304d0344000c003481007201c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 956191357 1250 956190107 956190127
    0xc070602280e010516151d06090705090f06040903110d0206040212010905071203050d0908130f06121d07180507022802030f0d051209010b011b05010b06 67
    0x24038580389007464480306040e0810400560303240c0502403100340150300403181c00c4002040340300c081490407109080050034086041c0c0a001c1d50303842c1101000e16a02450074000c18400030000c0c000100307002c40f0070b20341c14502180300940162000d401c1034051511411904c08041c0100c001c0d06110000b481101d03004001418001e54139078082c3c41c02e80c001e070403a90030290420818024110a00d4215004085440c501039842c001140c51100030b408101040c4200d014590060041018983c011b44171a901c91107010607060152120741c0c804083c2407810b800c20010315400000101864503070842c0021295111483c8040103070241100503024000c61801042c01c9000a100001d6401120b0080100b0b503501c91080c0d03034031401401244c00b2010300d91001000b20b14000310a24017184040d050b1555400d9102d400c51421800c41c1c4400081040466142c4070504041e9115502200e0b070b50023404415080000680180c11025628104607c1e604480302884000d4001c1040f0a03c00ba15156868403122 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 956192607 1250 956191357 956191417
    0x3e01110d060f0801090b060d05030d0c0504051017070c0201030207060603080301061404031703090f10020c0115120809060c1005071101051905091513060b010206010308030c070602 79
    0x4007450715401c010040c0450f0341d0105109818059a105003200c800b61208810007c41714050381041b64640700030084d0710381031441ca002d81003081c8082d441d40707a00e50381400d007001150036681d01c00c2c03402c000d5003200c14481501c0c1000404c0e040030f9075040200307120310603000480103403203030744800b800040c14804000108042e01d0025412a005079440760b01d10301480350700354414443e9110203040c003c00701100d0405021680001c68210021008030341d07450101c1c090003030401030111000390a070b0390301049110401400713001d160314450000b110a40c846003044010004200c6600014081e5900410000006d072201800c07200b916100104940c109102c800c1c000d4060501103809100040301301801ca50250014010540608000f000c008100322078800c42e440113110051520301b80b441040d0647c2038017100e4100c1c0c02c0c0240c0d580ba901210b07051203401c040040c1d8150080144c11948420010804245090b080c2c0f50004103550400350340b94102e00b0b0110190003500c80b6044046800c0c01c0c1075600c201e01c0c0c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 956193857 1250 956192607 956192609
    0x222604081204060f0516031227030801080a05071203020c0d05011e020702011b02030c1224070206011a12010b0702030606060c030909040203210a3e01110d06 69
    0x5a41d6400070740384402c003c40b517600890035500501d01c0c5e140014000039000d0140310381e81c114a60303030004142c0281d44400b00c402e022185d107011101c040c422034030203060b031040b261800b60101d90010204221280c0d1016921a018800c21a40c0814540c2c0035007054424058100d074140e004064000303040c07250800e6030080001d0042540d00701c4280c00201c420007828000d6610540c8c0584905416682c448502c01d03100002c2d020481e814084d800c2c1c0003003540c0d82c200d415000084110f004005034400c8001e100d030b089451102d03822803100c25004014030180d0014020381500c00070344075130000451604542c0d1481c02080c0c072414200d07041c580040f400307245690260195600132421940103031501c2040c0003d07446040c0000c0d01c1c0350010051701205007840e80b200c507080f41c800b40c104c4d032510307845001418900c070b030104802c0e0b00383d407000038146581c650100400340f034018240049400741c4081510350808260f2100a24000c010780b030405010b8000a500c210011088100d600c1d944180d486046c100600f80c03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 956195107 1250 956193857 956193869
    0x118050111071e08011a0f010305070c0501050c041802070c1809120503160c03081b070b070c020915131e09060c0908070b04171f05222604081204 64
    0xc0d0003025951b1030001c0002c01c90a440182140c001c40407588011805000000c05c0f110500c182003a2404c0010381c00d108076845024004843c0d40c95909100004001d030007518080c3c86a54014480400410001c150350b00440c0e078020260f1914203000d200300c00203042815400307002c0041c401c500510032504039000b58818bc0566441c40058902c100b01a650540000d00240001d6290000603a650f00040b4488062000c80107009050020554502200410440300000000d5800340c0c11011030400288050300480b105603c81140300450000c0f507011482032900d2400152213042100c2041c0340c0030310030058814051801d2000d201c560601902500c84900904002006041d00040301c090214140055481410203c0e242a00d00b04000c0303007246208030408400d00074402c180040d0484080c4c0b00b084100344540c0422103161000c1011071100b400f0184a005902c000b0803400011100c4000c0380c850003400c400980c0368040050320a102d40141c4d00085803500c50309140c0005809804003400c11510 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 956196357 1250 956195107 956195111
    0x6020d080106210e01060e131110020a0f0303020d0513051e0304090b120601090b3f07050a1206050106020703080f1806040902070606050118050111071e0801 69
    0x182e2030300111001e0046a0320341214940b40f25000c6442c00d09500700812580c0380a00118000361100800992002c0a540500030300710b01c05122400c00c0b480005880092004031000141024110701c00303503d070400303004000c0c080001055107204140c003070b5040e80d80f0000847d10401c0036140c0501e000341400c040da401641d55100301a240c0d50222052500343c0c200520b814099420140362003021006404d00c0300380c19922580c0340051f409425420010f05000b400003500c0815083c00400502c0001e000640c06005102418401381c4030041110b0281a292a03003501100403401c440300d010350418a0a0300596409460002c0025075600d0348541d000d00580104000c102e680d076103000580e507070481440000e1841d0814400d5660f034203420310260104030f0480e03501000200110340011059441604102c3d40154082040d4040c490750784103a5010b0402800d0482503800904030002d804c2a0340e100c0c140c10040c032022030003c00035003400b05000408201205c0c056008801d1640c1c07811250601941e6030540c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 956197607 1250 956196357 956196359
    0x1020a03050310030f05010506090c1306050906040e0c0d06120c03021216090207031107081f0209100c0605060406050f040f0207050f011d0304180c02030913020c100e0316020d0c06020d0801 83
    0x908bd01116188120300c4680c1d00341900c4d0404c140d030190011b10085a10000901c0300081a41b160400b2a10a084c5900700c142d445030040241000c90b0125041000f190a58007441d40014509448007016203804540442c10440c0c0451050f2820182892034454400c1d01a4000342018440d005820454071a88501491400d403055441d940c44446c880e40250b80d000603441c3e0401c003120064500002d00f108405071030203201c64003040c1681030000c1007900040c0f046081100340840e621038150800c004032010300450703103440c00040507004c640c00d0082c41140d4540f5172a98800d166070490703246640c00f0080d20708081190404078020000f4000743c22810101a0203a03400308008000c640c04d507500110100420a0042c04240080c80e01c07032110015403200304504046591146504815843c21520250346c2d00c8001004a0501e00719050004010b418403181442099011040e94440140c00c001d00501c0c0d903a80c0006800224146001b5081c125200c03c08603d06c2d0f804258000709565a88403d000c0ba = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 956198857 1250 956197607 956197621
    0xe06040f091a0106110f03120702031b0d08010905091c050904050a020306091b0f0a0e031006031104150923040501020901090605180d080d020a03020c070603060501020a03050310030f0501050609 85
    0x1000000c6d800b560907001048080307450000000081c0d04a02280304807810a142c07104014100b188610880358036900899500c5d035095407085030527000d04481081403010b414550302c0d140d5241d01c80b07805003040034013100107100f03824821000d84156200c010b0080c031a0341000c0c000d04000703500a171045030050302e5000001da40b00f5041040030208909414000b890213403a14094007154004000f14410006c0391180001d1a640401504030030440c0709100040991030343c41c0c002c41444680c105203000d80d00f171624003c0102403000815084850312070740442c00407036601c0c603070381014101c540180c00d40b00c8500a02c4144a01503010b01403502d0b0070380300c0c58415626502d0070b03030300ca02a000151203120980b03c43d04c9a242849404c500c1c490f80f1407a0480d05016980c80100705a81040c844240001da01160000440d50100040700060180d401e0410032541003c00003901c85502038005030503c68000f002c94440303444001106c0003103400146a490300106032a29501a00b026154240300d900840040303410 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 956200107 1250 956198857 956198863
    0x603050c01020703080f1c020403060e01050a0b06040506030901110304120e030105040f060c0309023d020607050c07080a1118150d051203090a12090e06040f091a010611 74
    0x20f40342c10031405406d05610841e0b0508039840400d40081c10880a00d220b20421a280080e1000c1e5105075004203440052100150840d440280804d642c0d50400616140720b0315000d044505076441900d003d603990f519a1200d82c050310300300c82031040e550310000c108804d2000014035280b0205650341d03143c0c016100401010b090703a00a0b5800340c5041c500d8101e00e0006031444d4410601803d00d8107003c600b042080d0001507851010039440c40f200342c0020024406040552202c03800c4514182030f45554001d402c00082d501d810040c41d6806000340000da0400550040110000814034401110000038103480c0c901041405408002c0c0240c240d00000c82c1c0410081250b5803007072820100c41c0b5032005c0840d04009410300c28180940c1c40d801903640701c0c0e103500da469004510580150009010358215480c00807100d00e00402c2c8041040710061050103266500007140740c2000c1c0c201c9001c200c030000700e0300903c0144283c040050a080007100c6070941065814022812503256484401c0c021071715032041c5071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 956201357 1250 956200107 956200109
    0x7050f0d0513090b1f0e030a1103070602011b1b0507030f06060501030216021e0402040305061006080405072c07030b01080c04240302041701060e0601110d08091c030603050c010207 79
    0x5407201405a0340781a0300c1d100c0c515a40f2031540c524146e801d508181000ca400c01022110a459100c46100c802c41a41020401d0340000c09152001300822610545082404202c0565800420520540d1024845005020b8111903500320702641c0721184d4038a4103441d00d01c1260307400c55402d401c152000943d50300034800d44024543d5440d01e00c5c07550070365078204810000507404603a14a01c20003000c045a07140c40c405000034602c0317200141050300304541d400071101c034180d10038410001c4140c100310010b40c020404100310b50f80011615010f80c0e1001142104800c440304880302041c2d1401040025545a0000400302800784c8510441e5205d604110711244194020304e560a00002c0c99462071090110320007185462130310b0018209a2222401c40703501b8116031010000d42e4649005020b480d44604106820100901b0144540280c3c0c07a8065200c0003c00020014003181c0000078000c1c90007070116600d420b800c1c00841100c0e092a030300240045c045030105907030324840c0d61011405c550001035910 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 956202607 1250 956201357 956201359
    0x201050708060d0b0a180c0305012d02030c0904091101140c1b040f060f0e0a050f0a0b010309021f080903030708012702070b0105010e040605060307030207050f0d0513090b 75
    0x526241107510f903081390702009810509690381d298010360760000e201c01c001d10950f100305011041c29186041050a440552320b18103072402a0000c1d140b0f00e905500401200d00041c40310250310b83d694896201d5140c0110002160003500f850000801c2080e481d01c0d918500c80241c80b92025400030003198001402240404c00035980181003e01000c49642044288000002c101103051011249980d0940c0d881d54041075000803090341c14009a10f10700b0322154002040041080285006031401d10041030151039548090b07030b00c1da891070099202e0b412200c0083d8015140381d1000c042034020000807840c043c2d480d000036103d400072442c48000841164016026550780050316404c0440c090b90010550380c44640e1085000b4041d540350b4120b002600d0018019201500d107503150100240c43c114040705101c0c813032071a264092005035119030540342c101c3c40c0c528005880310f0542c50f1141ca080410710180d20035119101d810f24200741c2c004020942404261032401c1d0351640c3e0b08601c81540c03040003441d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 956203857 1250 956202607 956202619
    0x30f070312030b030708070801060320010c03110a0b0f01140315040210021009030509011d09010603052a0c1603120e0a09140105030d0e1c0507180b01020105070806 72
    0x146190920a0300f103110000d200400356072055a403210a01d16204055008100d165105c0504105010014544482500c0c1024500f00d20400e03200001708000070500c0002c0a00003941d12803101600304000722280a07a1040c850303140c03030505010341c9291440903c1004216800c2d50301e250b40508021036250402400800d1500058446508100b4440c112280c0d56046204080741c06140c3e07030f2280200f000b602d01a403a015070b206000000141401040120f080c0c6030ba07001880d030506d41c0c90740300c040c13411a031a41c038000036036440704100c0381340f8083c500c0b0050f2041c1500000c4a4511003015009040300c442c200d086a00010b99400c0c413114088040c40080c040540c900a20b00903540102060980e120700104140070ac0d649031103071041220801c01540ba19612044014406402c04006410b0100d8071410070360240403442d800900224041440c0e001d8141c44580784e1030410a04001c1103014141486a0062281c001076064000b014801c00003801503023000007003100b06005010f40f0b4000c11010b821 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 956205107 1250 956203857 956203883
    0xa1107110f03031c0606110d030b01110703110906041b05180a12022d010507061d030d060f031e1a070f11030f0405011409031506030f0703 61
    0xe003034030303100e41a00a6a003108141402885654081c030040c00201c0c4807040f642400c0125007100e41c1202d2554010380244034070300d4411300e8400350000307404296800e03a04d0042460845040100d45100020461074010322800101008000e1001d04020300010300780c41000e1250b0b181002c0100307407803880341d41903c1342ca850383d10102040e100c0c0d4021700c101404460b10f02e4103803a40380e002c1b0b0160504c41d400126030541d5810300000f146028461001c002005446045d510704520070aa089001006d00700c0b8140640000da600806c10a90012846007401ea800a046880256480f5450398010310300405254a040740c0032807002c16003410281540e81003124010103d10201c4100f010710442e17001941c414091310000642080c4440c80540301380c1007561600700400c0c4040005c3c2c80002501d0b0710000701d070000e02100e00010003403000c2d10304640c42403a0807014080c074146162168490f07603000c2da40501410440001103151200c0c2c0502514094044800d81804205000e40b105881d000c0103101501c1c81130 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 956206357 1250 956205107 956205113
    0x1112a01090f1e0b0a0c1707120c0905090c031801090515071106010602030c1b100f050f0c0303070e03010b01090501030b0f04061203080906040b01180b10020f060a1107 74
    0x5241803004081c4080c00c15603026580b41d80c480c0b06412070714500001c1c4c58041030350346c141d0701104091010144040c4441541490000601200148007111204c4d80e550300001201d0780c85008168014500504030011a0070302450b440d400c1ea0003202d100f07501140791521801d15681c14400c01c0245c42d0040098904003681e448174441d0210081d00000400000a0442000740c03418020a402001d01e42c006540d200808000c1c1400c00d2012074152040d0345188000540c17a8860910150b40e114007440c00020302c006e10701e02030b1400e001c0c1c3d040d0038442100c007180c032106580700000194042c45554541c02c840701c00d0042010700703890710703194110b001039042c042c20021940250040001e02c03000130400d0b003400301c0072804242202e0b00d5500804081004950150504d07411500403030704855040050643d910306a118400c0e0038030f042c8034054407500080301c05042c214060b0301403038145c280286200b6608000701c200950ba442c411141c880c840c0204800f10b116500300344908140e0b00340c011a000c2c00c006580d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 956207607 1250 956206357 956206373
    0x303011508060105040302060d1b1107030210110d0309150e0c09091002120105330f04030b130b07030506030c190f03140c010801030b0c0c01112a01090f 67
    0x54000b50600505220210050350b50b203000c1d080060444070001204400d403240c100012182000150034012000701d405c00096000c1508800e40b50140d40d44441030000b018200c400e810102c07a150300600440048020f002d0b030640050840d0b90007084140e05400c0b010507840202c4401d8030311010f15910180000043d400c4c00a00d0310751151028065944483d940100c14090703034403003844034400044840040c42140350500011606a4044114450400790403440c002803602d0030441d00d003480e8000c03500d140051403d1045070091640203220300305034101038030300700b180c0c4c5402070045031000032003400180124802c0c0315192041c0f82c0100240190680700b414840010644800410b203060240400300c2c0c4210401e400b0300096208500c80e440e20380d40f04010390b007060301d1038042604100040c0010000f0803d041d440b9504440c212031901c0d6911458081c0354010031000f03024911100d0b0120364000c054981c0e0410a40c1d04501c1c41d101c559448010000740e080741c85182008019050081a10b004115a8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 956208857 1250 956207607 956207611
    0x1e030907030c151b050a02041e11040f05061312060608011a091f080d09170d0c0b13020d06051f03051507170a090210020c330c0f0105090303011508 65
    0xa0006d40c0d000a449401041c1610b0300510038984582c5034501801ca2040f20b481041410041c400241d81400d00340341510805642d10f1003464071940c80441c9a1003156207000c2c01c00e0041814070081c00c600b200501e051405801c213072113425500d52070300404014020385542412641c0d035000b0045c811540d03805c9203801c20200d00d0040c400d884541c0d4a00410300303490030004040c00f00c1080e100c584042e483c1c0400d40c0301300c46020024200035000310620a1901c1d400c841c2108081e503000b000901e00303a61314620402c4007120184080e43c41100c800380c02013400880d03400180500d02c040c502c80d40c00010001a10320300080d512000708154031083d040c0180f401907103400798111019151200460701d0001d4241d50004040e40c0c5407031980c0e91210b5603001c5250800c4058004e070800e0015240c81c1d84110009031260b441180da007902c1c03400000c0c614001c00003269091484000d0310301110303250008030322401d07a0340c940090091a60342c039001c003061050100105580c1255500c081d0a142110206021980f440d80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 956210107 1250 956208857 956208863
    0x1a0904050616020312150307080d0e240711150a05160303140114130624020f070b0c0601051f0509210102030f01091509021e030907030c151b 62
    0x4c20300020a25200121107280038503603440300310b12001080310030181050002d03440321429600104082800039080790643d0040181151000e21116000595039103040e0040342c014002440068030108001c0d920080b104507800594440341e06a83d9511882c03102d119094281c0b0119000703008807006d0404050025a43c0340c0309140109086808244080504400788c02c2000d0190909400824506000c640134440e1011440140000e51500c1c50024040205030303204e035a44c680c11180042c009000300004002e20416900300d542293fa150080c4040350440c0180c210903000d2070340005028642404111084500d00c040480da41601c0302007560154081d40100383c1003113014990b101030440d00d070807040d0360302c44150025070b403442c1400c88200c11400580051924915180c00600040c11410703406041c0d8602d40030050b82c41c0c00204102001c000c01e4400128050300c000100000507001103541e00c102e922551200918940301c10990424408042c1844d00040201c0d4100005c04613103c245400300d80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 956211357 1250 956210107 956210113
    0x191a090f0a0f021c03121b09050118170102070201030f060b040e09211206042018100e030f0705011205060d050a030f17130308070908010603061a090405061602 70
    0x10240580005030404c007005030b0218134407050404400e4800d0040e80208005030b112800396142908000c1d040036600c1c050350b410086100d100d04603031603222011b20064900c90b415000e44802c00000c0034003070f61092608900090400c0b1726a00280380714020202600c40a00890341007500300180d89012800041814141e44112481110900d54401880d1340103100c079801d8a40c1c50341c18281407200401d0151a03180594a0b101020114400340a110301c070b903264401c820359030354195104107004901c00c607014681c4210034268a0300500e4110128501010050f0203581a098840c1911a01d031020780c030031540812850041000c103140aa80842d92080c002040c0648203141500d5141c80d0821714035085001c541e007015403410060b0881040c90301d615a0b80504091840e1254413140f030041001c400600380300c0d440300469a81805030f0600c8014018001c02040000e98030b080c0000a0000e0090218541020907007010190904645403441a500040103001e0781d2164145410058400680441180 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 956212607 1250 956211357 956211379
    0xb0f070f0c08060a0e0a020d150914030702101d010509150706150f0803070b04021f02070306060b030717090106180e010b0102160314191a090f0a0f02 66
    0x10300d040524001402c9814010000b03881c0c82c0c2d94003000c54650a10004c03196203c0c400700401659035101818030b0b1548001070300d1003250486a880c000c1c00310000f0040c000d40c2c6203224041554400009041c46500848140e84c1098043c03e043ea6601380700d84102621058040303107160654051001031101c00005810008484c00f41c1c0c0d00f140b100c1d004000100c03074440c1c032540300d0412550030407150300141c060760341b50248203403600c01c1080c0c0c1d030720500c000104030b220000006015582d441c2044075020028400d100b902881900c0000e454800c20f01040341c00d5407818801260031042003058a11941c1542c03113050304000300001c016030304c6500402c01c0790705640701c0402044010366400360340c1c0da401d02d000c400314401081065560944076070102c0f1038119408039000342c0195403141c080a086a0700700300480f44414001000d181030640e0a03440b01d000c41031811a4208010704068100e446400e8035211400303a0312816003868454460305480102980020f01040c0032039841d0028048851000b0b0041e5511 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 956213857 1250 956212607 956212613
    0x114030606070b1915080d030e121210060e0105161b062d17040f02180618010303080a110c0f1507170f0703020903070e011505040b0f070f 61
    0x1030481100e04c46101503503034448803103000b86030040b6500030701c00c2c0b60450388003410016001d50310042c86030b80c1410181c864601124101c01803100100100400c0203207596100805000880b040041d00d0300d40700c145008100203003043c82078002d803412000c140e480c1450070181406000748128841d8080e10441421100303941c0e444040140c5070000c010545590aa03a100103541c03524841440d8186e032710cc0203103d1a60490580d111000c0804440304410500143e22542081c404c6129100d600940010f074200442e1440e0151116080c803500301103807122445442000444030700c250a1000034042420140800c10788151900140071045070301003034500b4200f143c2900d51520301030700142c0713000e500314501c810341542004010641c0f0581600704086100a501c2180c0c0c0749880080101550204100105400794869012035040d031000404841c145529a20780d40200340b0300380301d61000e40300c1041051401d540103400390350848030503550050800c000700c0c120303a0190380400390460344002c9a0f2080000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 956215107 1250 956213857 956213873
    0x2011d040e0d022503060e0f0a0c0906080c0112020d0e0703080a03050702061302090709120c090e0d0207140d0b090c01080a11090f0a180b0907080402011403060607 72
    0x1241100002805801d00c0740c0701c0642014030f46900c0b08903000391411300a803034242c400d00788801c0725800700000070100c04600140f03013080e4000c0d07c1110b442c00307a1006101801040c3d00346600303542c0c03043c004002041ea030b40301c003542d52103e800b40a80414000402080310003226805000300d026032840c080340814000c607225003082d03644c2e041110202008074105c6801c540c07511505031f1005482c00142070508144c0c0140c01e13000d1501b03a009100c0c005200c001500b41e4031941500c401007103a0011043c00b403100f8504120403400302d025a080040c6842c4104400140004440c0003091241d005000ca81d03040911901881c11280d074041c0c1c00810001d0010001008600d40342e21420b45a400742c442599000c000529075100501000700241c20401c805290b45515811a011110100d464100c909056800700d040c10703005500040c000402e0380c0303071042600724580041052031700460b030080075036a84410a440d5500182d4020f800180c1030790b00c2c3d2448034140300080d40c21481c000c149604080b00390b0b0341e0b011 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 956216357 1250 956215107 956215121
    0x501121b08120d0b0904050604150f0f0e0d0216030b060f030607020f15060604270e0a0201080a0501080304120809030709060305150f220602040b0901091a0702011d04 73
    0x141e0240000340040f0358440c91051501480b0100c44903105402e10341c503103998501c0003600150944a09800b810456046030340300b6403a080214009000340007900c00100c004041015625916000c2c0603841ca165902c0441c561141100f0f24112540b0241543c0ba00809014014901500814142c001c58419641001650300c80c0180b03900400c244088254030f181800780000011550216a009004540e82c80d442074800740d5100e050b02d5201c2284260700c4410410120030340d00c5403a464200380c000c40d440049040c14a2078000e03280d4101d2030300e60750341203802c41e4024440c002041d0000e001c02c2c0103100c4404c410b2044a40584101230a122200000074148221540010450b81d03452808104000c1c007400b03160303a400c14544481d0807514020440c000041d2005100301c0411a201428070401c3c1100001600c0003500072500f1034440c0d403030b4200005180e10041503240400c000480005819650480200b944014404e00c42d00b01400c0e54015100c140c000d0080d02c3d1007402060b288421074403640700d800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 956217607 1250 956216357 956216383
    0x1e0d051b07030f0c15020c0108060d0210021b01050301030c06080403020304170619020306181308190818150c070b0708010302041503030e0607030504030503130807090501121b08 78
    0x2802001d2419508418440d41711401031443d12000d180310325004603da45441000b030920851503603c802c0051a50f100c5201c00940c400d1034a960f54454550010b07060340403000c20110235090415840040d2620700003484000d1a40d0020442480601e2084485507082403080c0101c1c1d0a0a07248c40080c4043d603240940b2006940c440000c001007504050000803141025000840c998205140880c140d21004410b0030b86000002d40422400302d032689024800c1d0390011011f503100c00078005002000041805101c5c0000d040c500840c060641c0c003400700d011118490010b0070344d21074280d403c4003241c00050041348050002e0180b00049014403a8191240c0034681d25201d0350360552040204a6080e00c40c400c00d181041582400000e400455441405004681441c0c842c00130345003c464921560300000c00f0340c000440c046002c0c240c0f220108054403c69025604031544404650003120b1007441944040c40310b15104101061000d241d240c15840031104c0c0d40ca8480c1c44600e100c2c80c05d200103003c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 956218857 1250 956217607 956217623
    0xf020c0703110306013804090903051806040e010611010f09030e0102060f0c0d0506030c0406150207091406100e04050c090418050303011802090a060e031e0d051b0703 73
    0x403a1661606020003809090052086075000513150400c41c0c800c21300420300e101b040600c80c40d50441140002c245c0c0c0080409180911030518240b0b001400d50300314001c0100c2641c01446074403010b00d810b03070030341d401d031040c0440070b41c07040e03180c0f010480e0084100b0752604502d5503260b00c8800c3c1100d1a000e90710791a0700a84880d03001940540c0020b241c408014802165504460b0a21100700d11010807164442c0e01200d0200d4140c44840009041044061046602c14500800001c0840c041110900141c0c0703940c090320151a070711000d10082d550780d10b024000740d54114000685c0d6141895400a40580707900d45101050f0b20740020070216480ac2d07800d200411800b184130001c6180c82c2c080c448210f1310380d00098440c20f107580e5a040e41c03804103000d0481d912881c02c18031480c030189139042c0c0350002c2c0c000307100322082030343c500340a0029003c40103180e019006110038a03c0d4040300c001e920f07200a51036030052454420116003201c00e508500002e4034151100342440c851064204104400355000f4892 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 956220107 1250 956218857 956218883
    0x30803040312050c0f0705150406290a091d011401141f1b050109080304230601150201062d06090803030f0a0b180a06050409080d0f020c0703 62
    0x240c1403004600030245028106001c111070201340e0426121540704818150344c441c021071420a003000c81c00f400b01460400c01e0410041802000d0b0000d00c00c807404000f05110040306844242d58445d02030307981c2e540000400404008000e031a502030032205c2202d001500074440b04e40442402d403502c7c0100308075030083c07080c0180421114142805045181100c04070482d401c0401030500300700e0f03845158003d010f401d20005000d200843c1c030760403200d42d2004c0200505401da00d02810103030000e460648815a580c40c500c918001c840e040f140d2804c41c04e60040c2504e80c81c0608007803141d18001c4031881155202da40015007544101e41000c944185003207640449001c6008206400d85c46900c8030041095244003046514404801ca0782c006d00f402c111300c06682d81d0220030f0340140074421400d035001001942180d004003030700c0c41c00900400360300009010f1030341c0d50020030040d139056040140c2540c80410079403002180c15480f001003503210300300142c200381000043ca400c1001a500a94803c040e03589 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 956221357 1250 956220107 956220113
    0x90308010803122e0321030932070f0e0703060b030f1b0403030210050a0b06041e0e070507030206240d0f080a0e0f0904020919060e0103080304 63
    0x40080c05401c40500840c101005603040285016020300a0b007052031001100c011110300481c103c1c10300e4907683c540850400d81c0c83c80c4c903035038208030003001c01d0480b608440c102404c81d10a000d0840c52075002011504d81c1e071103600c4c5600940c0c2c54060b2010009041e01d000c100380130014000764005041c40240e08107618030f46801c48130503850040c44a1708151070444144140d0f6800c2c4142c23034000703101c20040c410a580d19010b180c610260079040c5000c500002c01e00004059002a0303c0c0c440d50a031003014070140d20380b80c14110640e5030100825600800a010500140d1912203208401d51264400c0c648031a540300c5034908a40c00079150a0002100026187c1c103068040204070f80004550780d1519070b1000112802245000c0900618400d80c5036101c42820f010305880d044003d103800201c0350355550300286014103407403d2010000c2c050702040076010780b0362418410203440303950007503c6000d20340c1c0c807058203900d5100c402c4200a0a9503032054045180b00d5a07800c0180614481d441c0180d0f60f003801e003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 956222607 1250 956221357 956221367
    0xd0b0601090f290702090f090703060f0b0f010e130c2304170c0a05130e1b01090e0f1302060d11030f1f06050a1205130605060a030804050603130b0a0903 67
    0xd0150100f0a008000c0d8200503101e0030300d0a6130022021061403903a03112120001e0600070698070107000503080c5140541410015400745100510032200041056010801907401184900c1d616900c00c0200754480c401d90f00c03d030040381c640041072500442448404c44000c000041c08200884511000b1905001486039500d080002d140c0c2e1000502082c41c1400008845513194051503003d070310781c0210604214400d030010015080840140c40c00d1519021600150308180c64881d800940440000588410707401041c40c024100c0c524000c666640780090040401248542280c014108112629106803180301d03500c02c0c0440f000545580307042074030705040540b4001d44000c00040c6501542080410f0000302201224118184940c8800c4107a509462120746107028207400d9041c1300400402c0980f140c41002e00034400c440c208603a40f66034040c8271180c4941e0000a142c841d040100340040d28180780650b0740004030005581d01e1200325910300001000554181c0b02d203944403010302081503041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 956223857 1250 956222607 956222669
    0xa0b1801150908030d0f1d06070f2105100e0405060411100c11030f010c0216080616030905120714010b0405090d0c0203070f120b06040501050d0b0601090f 68
    0xb85000040141840801038582c03207068084040142d48040400040c1c4180d00300405034101d03055610f203d0840d4a42c900d172281c0c004c507460800114107410f03060149000c1c24040d0340310751074500d10002d141c2c072078454400200070203402281e0211480c0c0000640070740d170300c04203445103200700e001c1c1c140b5050510b0803911910010301001e10540a4800590350242e001d490b602d12a42c1009500d24000c00340300119051109001200d01e03507500381844401101d0b0000f80780315544048002315014980d54021840d11900203981800c030003082441c5d1030900d07a20940180c00360a0040080e2400c1c4000200c0c80078155100c010211111034040c081c0c24900c150038402c040c0b001c0e8007900d0074041031034a904000d8036031702201018024000001410341c19910100f04002c00341c5004660b1ba49041c2e04c44c4801d100750b00c100b100484614169900040c020700382801105e0491300080c0c8078400c480020b0b40c0d030b0304010300d00424445c104249640000f0350510300601d000010800e5442c4000080c0b00d00760810500002 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 956225107 1250 956223857 956223899
    0xc040e04050708120a080601030515190302090604020405010f0807021c0c1401051005010c06020408150402030d1716111605010207080c0918071203030f0b10090b030a0b1801 76
    0x2400b50712030701601b00d01381c164441c200340380000f19a0fa42003d0105603074001d204003a00811101c252a0180d208002d004042d00c0c021120344038181c0e122010401644954003030302d03000828201100821501a90711550011000c0c015a003011204d80c0040840421400c0342c03000091603c02d080c4c0a0045da1030265480d1003c01c170081c4020b103030100500040d85d14500c01c0a0400035055009410b00c2000c1c0d054402525400c01030354485460340d4116409864103480c182d00c00c2c0210984000118010051443c03084448401f001159907034084410b03e10003030a80030418024403c40c000c0c40800103100e04030150161018070410b01d03090200080c6048a50707040241c0036030118050308896170f25502d0403544545021040c415680180c21f4450410305158440380c002c005038080d0208054042e04846102c1d41405000c0108003034010030003080f0005600c1c0f0002240e03c500082c048109668011a4081c00f81c20011594400702070200386040c0401c00300750562824600140800c41c0311071101d411b203001d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 956226357 1250 956225107 956225143
    0x2030406060e0f1014030304050307080106050906030a03020601051908012a021b210d05090907050313030c170c0f06090304030c0612090c03050a12051903050c040e04050708 76
    0x1425113400b14030a050741c000c15589176034890002c1c030169402c000301e5020784406000d89028036521607103103010346180c4c01003d1059a4820000e10181800180f0290440d050750040c0200d23440c05007804052004011906460000e41d40c1c04204550240100440b034001045488184118403a041c080c1d0084200d29104540214150220041d003a4125080701107080f45e40c4101002116816000c8a8014a140d100c038000c40320411800354018010301800f08050360822150b40c0c0d0719500b1039091004441c091001141c1e05018800b10340700f00a021030381485649814043c00c049100401d6540102c0c03809242039121060104020344140841508014003000460509081d540c45914a2519005060030812890ac0b400500a01038001d2110150800e1100781c0c0182c1720309119440740004c41040d14032000404042d070a00d4451001c5890f014203a65406041d1409080220054040501702c074100060500003c41c686050b10101c50040348a00c000784030140c52b00c010703c1c0c1004485240511410 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 956227607 1250 956226357 956226361
    0x607030501050114031003170c010b0a030b1311120d090905060906271303180b041205030f0f03101502030403120c050f0d031d120901050d02030406060e0f 68
    0x41d81000300c5249005050705040e4403640c031511701c1b0114030a40e50001c0c01068030100240520507902004200b44914940207210b800300082c18015610118032005201806200c0050f1007158490b01c0003050078400d081c07039415005110002600200f07204031040641c0c01054801003019000a41e186c001c11040100b80110300d00724000621007000108114044e04198410300c14000030701c0c0e111101062024000c44541c10104440ac00c40401ca030401c50200311a5206c00c502a000507003604201c43d07000071130b035181c01d041c0703030707100c0c0800751800c01c22501840701b400702104010b80c036405482114128005643c0700d10b070070103562072131003c181e210041010011502e5140320b58044215010340b500481214040769041208540d040c50700c400c00f4000b070250301c4081ca4101008146074180c089256418401c841c54620400164403820583c10320755400340d070000942581c2d9402915141e04141800c5003000c1035008104280c0e80b04480c200c0d12165140b00c03e102c461541c802c201e4000f080780d080b1403054 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 956228857 1250 956227607 956227609
    0x90f030a08040501032307020607121806020d0b0d060f0c050c0a062a020a031d0612040804030206070f02130515010806130606210e030f0a1205040311060703050105 72
    0x1e8807950082e681096241c82e1290a00c0c48400a241c0109080380c0858200386006540251250300640392500041c143c80c41d030f10710340003e6006079000c85403a03c00220f9100c1c0c1581e030f840e000f940700610742c2034090b4480480b207540b030f83c1391144810118007900c40031550345000ea05910494000d521108284801807180c170b0f5081c90006240d1031160307841000003c50000068064500103521302503403035800110000042c42590224180c94401d100c0d840e12f0071808502c104824003601c40d4080341d03421a00074840c64160243c001095600700b40950305a616050705c9801003889903000c0b45040d00e8150644c03c0c10011420140c0c508954400b800d00100800e041500030300a00300b1901c1c0c502810024803801040e07255a80845242581164480400c080f5035940700241041030b000d400340c608000c2803440c0c10380c0c500701e50065100c20389150000c2c42c50802902007014058100350780d20b104102100c1006d0008030064070585002e20b0181c1c480f00c6144051412840c0741c00c100070401010181000010001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 956230107 1250 956228857 956228873
    0xc0a021203070f1b050d03180501032d14070915050703080a05100503010f15150203041806090f020706051005090a11070803040311071e050103090f060e0102090f030a 73
    0xf00380d00ca560b503c805000c644807a90b04004540000c2d510440f80c1e88800101a0041c82200038541e01c0300f0382659032595000158222002071200790740d8062108900440c14081e262840081c6581200020f420381a0303200303a40c0c801c07004031001004102d05050501c905100303d40010503000903031800c5031401c0803039500104a03440140c1a040040d80341c0010404080082a007040a0030019000300f20120540d240607000d004000441075050315034240108421291089013113800740f064009514280c1345c1080200b183d50b0007041c00c031510341c0d43c80c8080f411129034050804e24011003c00940ca55030542040ca0441c0c030080e011812301c040624042200b40c817160038056100c0450a000202082a2014100780780706554000303015800c00010001010b03007200814400a24a4040f00e00054a480c04200503d03000f02c101d414001d00440200051f606c40d07003044081c5031140900855036030450b950201030300d04042942e40703245d4007c01e294010341401690089406070407401805581240d86880c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 956231357 1250 956230107 956230133
    0x23100e10060f0e090c0318010216021908030703030227011403070203041a0408060c030411040903110318010806060a210608030f0a0807050408060f1b0c0a02120307 72
    0x400d0259420b00b20328440c0c0103109a0714900c0c0080c240490602d4282d400e40007075801180c447c0000c0f4600c8000b841062814826034080c80981c06940310120141c0d0200841603280c0400c1c040107906001002c0f645005c2800904000ba01c2030f1409601c0e25041503840d000030300712400d00c11201035200301c1c3c884207a81c40803150496030a01205142d41c0d4440c0d600032810f5100e582c21549845442c0e808942c001040400200704941640c8107540e410b40710f41c0060491807100740c3c0c0241000c22400044203042c64158011844184607082600e168003018407094255003001c80c40c03a240f524081c0000c596540c01520f101e512036400c46180740303410880030700900510031961840c11803900a40040d80c600394203603c1080580820720450341c440304001d0190303850380d006d01443d40c000781d00c0d038000c01c00150280d02030354140d801000140c41c4566070800a41003006000f000c101020072030000b44071a550341d09008083c5074003101c1c01342c6420441030041c80616000039080c3d40740d90303108110120108907a0000c4130 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 956232607 1250 956231357 956231369
    0xa05060d030f050c0d0c12090b03010b03090c10080a0515030d030230010602010b0a0b0301170a121701171c0e030607030b19060206061323100e10 64
    0x142d080c41d1948421180707805100b450342c401d84501c0d1025507056810801900a0a03c518654500055075001c101c84148062050f00c0701b000041c00140030122280d8051a8090011400c03150b185107000300003034a0203800c04d05680407407084414000c180000d03004040d8011140030700200010120301c08660b46880c2030f4054001c2503808501c02d025516080d01e90b02c04100380180e030000ac2507281020721442c00080c13141030050344c684401c0001c00d0134000502001c441102c40d200f82181e04c1d0002c0071100f00090000c4000c00d000b0707941d00d0700000320042e80449031070146035100c901030394003c41110700000060b003000c01500c00b6403000c0286114001041c40c800072400070642c014101041099920f00071141c03845034940513500070051883ea05a1103139115490483e081101060311080462820106024035001030708030740001481030800c206140300845e4281c40020744aa00c4842103001c0461032401030b9480741113181030140030fa0a000c5500d01404410303c1e020540d007881030903070500340744511643c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 956233857 1250 956232607 956232617
    0xa0603061d06060d060b091611240702030d11091509100e031501080c010e010e0a0302010305060a0905010308030f10060c0f08040810091b080a140c0d0b0406050a05060d03 75
    0x1030020004c4e00d0300401b50051000d0221005400c0500490701d00012589101d00007804402d02da1141840018400010100307000300841d45070002035450701217901c0101494158030007048003c11075120f0f4403412140ca270900c0805130b1944441c40c01c0003004032028503800ca070f0110034001020540c0e21190070850200d41c0341040305d2000d21010201e410041401d6050080700e100c80000101000007103640006404266103c400300c0c1e500c1d00040d08c0045110169541021a1070024030040d40203502803504440003e10640704c40342e44400c1981a01d0090700108c8000b00c0102c148a1803411040c03102d138000c140c81c403954454a0525100a2100c1807550024140e40351010246c0c050203403402c2190301502c10b600907219a0381160580e0030140500e08403ca40444c3c130100c250650700b80103010f45051b902ca190280003000c00e2a1a022105440342010b041140160140001d807070f500c82c201345908920a1424108a24290909008813103005250295140c2050104829550365240010b010396044c100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 956235107 1250 956233857 956233879
    0x301150306080a08030604050f010803031f080106031103060f0417182e0503280e191e0213090f1b030b01170c0111150a0603061d0606 59
    0x490281c0841c0c2c0c0b20309003a014001d1500c080c07151000065110300c0d8107440c1800b680d180c13207801040d0264240b1600d03d0720781090020612198403a040e0341ca1080d561051300d80c40715264000d2a084401d03a03481181e03103d540b00d0728a006814103000b490791051075000100c10604d041d0f01c1d1904100b0854810700c9030403000003601c050240b528580d615520300c0141100c030003842d05245041d04c04024410590155000a0103071046500c9a41100d1042040505c0304041c038240804052403821080c0c8440485170326904c00b8180300c10200580390040d11141e40580070242d0710300304082506010028402d180f14414211409610b0701a95041626a500700008428405040c98118400f900200800c00307110340302c61b004207404c0e28444405403030090b200c019060340e036100040555801d07003008041c290003403594030680b0f40c083c016101001c003c1e6000c0c1c40e900b81010088a4814000700d60507040d5503641e04040c02401180d1242c00303800a0328402410601d841190130954802004021520580c0c1c00d800b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 956236357 1250 956235107 956235149
    0x303080907051f12060b0c0c09071d01091706070908120f0702190f080f0a1223030112151a12070e250801030c0b0f0f07050703020f10050301 62
    0xa10440d4100341d1281005081e03103c104025145d40004000b07c0c5d00d114082080f216403505034130341401071f040343d1104010003a0840032080d83c191000b08031070600c0030180740011550008244002c0c401c024001801c0c05240004018086003400c0d0400c5426a00c400300b0300448002d10303000c079084030400d1495151114058800903009100341c80c56200403a00c8190700091603058551010191001070055034030310034000307504a5445100640250504680c440210b0095025101d01640c400308d600d4104540405043c070f01c0701c01c0d8000c0e4080f4082d000807140035821700c14410401c00003141c0c0c402c0280320b1195403071400320305d07086904c00701407160f160346c51000703038134101080160002d04003204503015134a0038440e0408290030004000ca184094015501101c03481815203a050382c0e40070460052503410200b81c403126401c50520100412000c0000003c1000c4d58009400751074800d10041a02900390b10500000308260000035010368030484003449202d030003006aa0540380c001030400c1c0c110319412 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 956237607 1250 956236357 956236367
    0xb220b0a0f0e010212090105010b090a1502010b0d050f0d03290301020408010e1e010b060a030b2d100816030e010906230c04050d0f0317090102040303080907051f 71
    0x1d1410b602c640c0b0004860300f042188070807451003400c4600c000c01860f030b69030482010030302c9800c03030503988003200304418031400c050101c82e0b000170801132000290114104010510100c0391078230039034056001509800003000c2c108840c12888500780350030b203c10b43c2c0078441d100c408140c0c117110b0600070407a405000426282581940c1c0240303c40380c02030000c00d480005103515880d040108800140786000742c46d100c00720501074031102c8100545181d140c10075090084000300f5070b80428503844070b800480f100e16050440325a5040740d000b0300c04114100351000c00c121041040034140020b100e60582000082c01e499499841b000c1e100341004207002600f140514010400580010411483c0c60742a0a580d5021050000c003041074a49010460b00c45809940b4a40100e00c11207602051851420300018911580d009990348241003645040103628103620400100b1210214241c1d800324041081c076900c4400d1541008071840680b10710fa00300310101c0da035482c40c207000e0031390302005015031442d00d4852 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 956238857 1250 956237607 956237621
    0x30902131d010b0a03020a0b07030e0619020d08101401020f1005070f110a11240a02070911041205120a05041502060732070b220b0a0f 59
    0x8002046074003001c05004600c07400070058860158a06a001d030b00c00d062985454085c0c0f6002052502524642034109059a0100c1400c40410403482d485010f1911805c01030611001a01c0b103146c003400c0340708402443c1226180e0b10100b041301070300c203100d4200a0380c0081400d0760074451090600400180042c0c2c034000d4040c00d8940320307128030711070402c1e050f1280c0e1100d4012070007035071039000c081c0b12600c0460b01300812031504a8a6006441d50800003540d80f410000303c7c0f40064040107400300042c05c0000c0895181000c048002400204460304560502c80d22002d420190010020000341540b4000180264050046440c1c0c0780c50481c01840000c0206a5206c0f0509000643d50010240010002e4005100c0d0300d1050000d8022189440e0010a540d84510740d5a601c0e0030900303004a102d4a040c03107405240500004826040340c8400e00b4420061011900030610b01c07000f828980c80c40040c0e095261048000c48507030005d40c90004040c1003041b41c00605d40c0801080070071138481880d00410038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 956240107 1250 956238857 956238889
    0x70816080c16050c0f0a030507050d060905010e0c0909030f090603090a020d12121119091d011d0603030f03150604030b0709080106060c060e0a06020c06090d030b060a030902 76
    0x428040081120010708413040c0c02d800c2d2078032182e00f0241e1040c4401089140002007507a0000303081800941800c901d0940590700900e00490224403d803146421246900004612904164140e503014200608130a40090600e401036141c40f0030340c42103040502608400e40d1091200101044001c0c00800c0f00c6103605800525400000c03520b407800c504071050410480b80130841050005440a03001c2c446c488000c01305021180c80d20901c10100381e10650142d036140c0038061100c1e408104a0580c050300d400b40045200c0c41e40300d41d41446403803c01d0200910b420303480f020001e410484182c40101c19240405510a01035442c1d88603505c0384000420611549500004003050010030720075944044d5006a005454159449440700b520340d0a075441c500410b00818900c03134a0380001401a030044c5840c003110415161720310440c1d590b08040c0c0e0b00c0141c68500d90f0348201c040c012101c1040c00301c0003184042d400c007003100565000100e2140e0041c2c1c200c5c9410300d84c0d25040d400c01d5403a1b60403021403540c2d03 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 956241357 1250 956240107 956240137
    0xf12030612010e10050601090e040f05010f0e03071506030201050715180f0204050a1b0f0e03030301080102090109150c06020c1c0201051005090603060a020a2a0209070816080c 77
    0x103c40b242c0c1d256130340e8000140340c011500707002c0490183c1d40108003c0c0151382c00d481180d00c0680c2d80da02d68480a25109804441565030b55501c0c511000c5c181c031400c000c00d035120b4060341e43ca04007420a400711101d24103a200741945421020401070380c201c41140c440640c00102100034800c40a111002004010b07441c100c3c0c699045502820000021030003146248221000c0003551941c1c1c80030740c101c82420065400c408002c2205c10b403414029014441d0b0141d0038070700200707a04080d03404241513400a920a0324541c8d00032481465a6070400000d10181c140c40d009584521803070a00200982041840070709600d078001442c41c100a400e101d065032004451208150070541e80400900030601190b00d40c3d13804c00c0e03e0a0114451404d2150107001d403000800500e1591207104000c0025482031102500b0302403d10740a1415502907803481560112014410700351300307220300500007660307001400b450401856408003c00c00d0568210309c01d100580740b402950541d10300c080d00749103101d0f000090f04000703 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 956242607 1250 956241357 956241371
    0x20d2606120f06061f0f0e0307052106011a0a140708070309080609031206121c080717091b010509040f05060a06030903051608121905090f1203061201 66
    0x8500020320501a13542515045e02c01003072505d103040300d50343d42c02c12034000a030842404a00c0301e10820352108460130040079030318134550303c00c0022241c0e0a29095850a40781c07240e12800300070800d0161a0050951003000c034464081c0d424204590f100707c0c5900d1081c8103041403880e6000e904042581c00c0c40c0e9008659666980c0541009040080725200e0008988507180c005004510080203503803500140c00711381c180d10b46450080041414903105c5503041442208140c4140000d48403610458000a488803140c6051410000b00114042d010f031910011000050104191001400410301d03281942840803000d00d8400403034892043c10681c41d44070782882e460124010207580f2483c040c510403103040c449160390780c0081e0282d55601c0e8015003c203105100c0005030407060000076040e6407080c10f01c24540004480f038500c01120a40b05160300c1d406844100304040d00c180718540d0880081f4008021100007003261950310316045090750790916021022617515282c03840c1c8002183c4110003f88111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 956243857 1250 956242607 956242633
    0x17130608060f0303040f0504020913060e04031b0209070503041403030109150806060607080d090602071103010b0315070513090906020a1b23150412020d260612 70
    0x10007a240544a4001c12100001c80c0c5030000c05c8808603250130440c1205240f0701020000250130840036036030407951484072040307000361030300c04c0001820b591102407401d0300341410010126504000c06001d0715030301ca0031550246c0c4d10f5102c216031090041c40c040c1c0c1d59a40d01d18283c6072031991029040350307034807004c8000b0440441580000b000f242c2e02409a020072031761103940d550344200c02d42e0942d401240c10002440494041002480700b9031034044003099a105039a500c500b283c1c805102641e04005d5006030700e41c545800c0c010b0714000c61048000b84200f0410440150243c0b201401c05030034890002a2000c031041c007607501d580180a1005c0c1000041c00a007401c2001e0750000c050040043c1c0043c6c582544100c40e500005240d64000e10040d01c01d4004055044840c100840400118810740c008000000d080c2600a8440c1e417207a1000f40540303001034400b900e408141c40114080c405000e4501403c1181083d071007035100c03050030198a280c1c175218003041100d45260702c11421400350107a50406 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 956245107 1250 956243857 956243867
    0x120a050715021b090403050903150103060b040f090510200d051006020714041a0d0609060b0102010207020303270a0807060206010518161404060309050105071803171306 74
    0x1020941e502664014116148010016290b800d1065440f94018011402203882036000d010030003009011a032550065624a400201007640211160394558200380c2440c181801104080706a00d4010300a8000584d50280c0b144010600018600d684600f18817521034140c543c8580c0040030440256100b02d01c143c0d69000c1d042c1207450036560060480b00007407003403000803104100c40101c038850350505036160030400a41121500c5503081017161880764020b90307591076002d855510868000909070040d00d40f00041d12401d1033803a055910521240e805030301d000c004c0300d0611f02c409822079020006d04034203020420b400b00560750050300c0d2640204807200d0002d12242604c03c1074084a00c940e83c0d850402c0740c02200310313041840211072308021512000d1141d00ea03a2500720300e820400a28080c1c142c00080c140c0050380001c001a0301e81450740140324081c82155000020745c0782400c2003070348208468032130a600b8400141000782500b102001a16003034280c078544402070500c00e088903928000108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 956246357 1250 956245107 956245139
    0xa06020d1d04020a120c0215010e09070b160201110105060a090f06150512010e040305040605030a0609020a02010f050c0708070b0702010b130902030d020d12090c051305071e0509120a0507 82
    0x1809510304107212941ca400061fa003502342c101c1d114802e98070783c02c0220860f8403440241103c01240318059011420341e0040b005003440300310b05400c220f0541d10600004100d000c5a01e8aa01c450f40341c80140300c401d031910410304082d501280c401180c4000c0c2e4140900040040303510080c1003100c014811035103c1d510000400700700b48a0b01d000070f42039807500160154404246d40c0100824010001000386d00c0c064000785034050b01002000450a42d00d00452040c0c0e44121300c0800143d40d501c1c0f003e10a00290b118440d0802c03200d10165040481c181d689450320310540c44060614154080021140351003500010702550001d0072818203100c04448003006007146902c103d12900400729408004c620014001d10488019070718210180b13000d120401c01482d124105440581c540b21001c6051388668004904041100000040500d4a10b400038080c824141202488000c0c08030002000d070351120644e03a8100c0d0407100c2041d50b1030080d541d540f5001403c1d10041150240d030a00140600341014142 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 956247607 1250 956246357 956246387
    0xe030718090b07020d21090b0a0e0114040c05043305010905010e0f010e0d080c0606030c1f0f031d0c030c0301060609030b060d051002030a0b0a06020d1d04020a 70
    0x4991030f26401c01c1661240425102c4400041c0c603d403d480c08000c0810441c110707445100d100043e400d0440c1c80b880b5034008200d85d0200d080351940800715010300700748110710010749001c0741041c0e0750410f551009101d40c05e600c1200d11503600e0766040042c07640c0300d40f54151590b000b6540322050980450004100003114495940850700e00384000820754040c16200005404c010804c5440c2d000410042d02d408016003070807900540a0300c04540001c1c5084002c10844030800c1c02040d003464000308040c50800120031150062149140501c0c2024400381401c00014107030130040c02d01d2252500c120010b2000401098002c100e00440c0480d0f840042980110300b2010b8094800c0d02d12000c01341400d84d071407481000002000c034442007010403600b50b1031541164000388074148c01c240c185c403154603201066280d071509075400002d02011100b50f00c94032a080300e080ea00f05050529010780070703485100c0b0f00b9410b02803040840003113a0007054200b0b40204451b005004644076003107000c00400e240300501c505 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 956248857 1250 956247607 956247623
    0x3030a09061407240b190e070207030b041203200d06050916030207050f1c0806041b080901110f04060e060f0f0d06120f06050f090d0e03071809 63
    0x5620300b010400c126003a007034000845035402c1c0e0314800c035241c404414078407040b0744a42d151902121940c456400b0300b00100724101c8075110744c0c104010744a00300406803008040d94001c0703508000080f0f102e11044d51203034001d0000c249003988003074164054040d0713007943ca0041600103880b904409002002c2c0c12038000d42201000140c0c2c4802c00d0080040e002e4508018002001d505000b10910a800800d600c070310074400e07100800102603980307140c0b24101001d00da000700d0201d0000b50700b543c01503007180d0292049400b0302918014401c10030f07188522003108401c21403403000045203043d007500100b410803010070300c9542c1c07400b02c85a480c0e00d0360800d02036030000580388860301e849440c0c842d040d07480f0030200c070001a203031074501940104281e0020800d01c40b50764032928006085001101405007081c01031302442000e081c01d1800800700c0344002c080e4a0328002c0383c424803411909c0003425041455260030101104803854000a1402619500c0340740e81e182034007509080f040140e00070301401c9126110b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 956250107 1250 956248857 956248877
    0x3030e0c06040b09030c040f090506070203070f060507180b190903020915011b150513031e02011d010b03210901120e010207060b03070609050609150903030a0906 71
    0x419500c405003a6031960380900700780010f001c00d008040007042402402001c4804100038a0086025a20302c10340c41e210aa54602198081c01f00070f0000a40c8140c052010b145020a1552002281c40342e11001403c19541e41c000030340d4180c003c0303080e14814110a00f10075403090340c49050044ea41c0c0501000e1075090300416802d46646d00584a020550380e0041c000712032079031802000070700000907000b43c40c10040c2e248181855810481062180c050058505490342104502200c0a40708060f002d140341c05032000e019408a907101480298110b8200c440c900034442054080740940340c11808404000c012044212005205600242d45550150107072900c2c503011006042c28000200c02c804007400e420400e0b4402588992028842c0070240b40300050410540082c040c02c90b00306000132202c017036407001d02461798501003000c4002065a0714011740c055040002081c800d00401d000c03680030303401503a940d1031000c02010942e0301d281000b5003103a40305c804001c00106101402d1051030041111851 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 956251357 1250 956250107 956250131
    0x81b07080706080a020f07150504030201060b12071d031b0f01031b03020f120103050a110910051e180717100303120e010c0c02040b0306041a100509010b03040303 71
    0x41c008100c4903140c8460106698990000029610410400720700d0142008041c0008100600070302c0b03114000070000a00346018a0f0203070840707405030002c500525092000c103e0b4010451040c6030b1003078061520160111351840c6e1543c00e0b41d8111001c40c0d060140a102c8411400c41c036040c3c035020a01114007640c00540000194100e9240184071503449804103a2041da850182d001080c0101401c0c01036880e002e0240404408030fa82a0411a03c0350000001c450a018036204034000d0185c0840d80c1d801241041d412a0807060300a20603035016100d6600021030f00b044022000803582d0010b080c510f420280e0085030148600120303a482c01240342104400d45801401d00203500c01e042c1301c0c840c1c0100c035040d03407001d032088054071100d954240e4030740742003181c5c0c02001e0003141180b960030386800b0307a03000d0780f84104170503560020f11090090b0311038002c10011030318803408003c0114080c070344130800d42c51f030751103070200303660720350003540d0001500030000401528807402103108a0095500b001f900070170700d23 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 956252607 1250 956251357 956251363
    0x20010f14040209131a28060e070c1a010e01082802010c151407030c0810170f010507201b040e0c120d08070c0c0b0f07081b0708 56
    0x1d28080e420403a41c60005030100207050300310300d0860184502d02541645452403d404000c2250700b0b000300b20740001c81c0740f4602d00d102800c141400707079644248140d90030058151580e9100902038002c000e4000006801d10100b40d420090403a0701100d24807280d80c40d11441282205c2c28460000355100704440b54188240744840038120880c6640640c408441c40c0d0011601943d1103507066a10b80a844031650003800c20788078400c024840345c5000d1403107140c911006403c4401003d5900300307203c03014081000743e900803580803060b907120f000c801645003800c5030382c0c618001c0701c04220301c844e618000c203118050703403c040c5000e1111041c2800f90158002c0140d500d44400c14072000005807840e48074000c506180507003007c0c0b5800c480c142281e5664803003a0010f400c2800385940c20840d41c100d0a514079045500004469104019003401c80c69401141e44d81d00140d04a481504d45001010900300003001d0090100da14061f0080d503802d0b110388068040c0085c0545100401803907200b40350001a8008002c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 956253857 1250 956252607 956252611
    0xd060302090f1306020f0d0e0a05060a020f0d050c1e04091503020603070e0111010903080907090605240910110709051303030b030f1c030c02010b1f20010f14 69
    0xb10500382603240880c4d031104041d401003502c82111140601c20840320750503500c03031940105101c0d4010070b814a040d003052414290080e03c2050350a004010b90b082030301144044030202110801c00042680e01c0b20b120702c45e1405458444600044d014117940c0a0300301000c0908280c50900008005400380c01448081800c034510000350400428000144024000e83c00042d0301c0c4410f04014052003d005c0609084131b4003a44102c000c00e44540c1404a609010000007015021084c4100000303818240000d030007420348010b4000704a6407c0b4407003807110301541624404c4401610301b511101c401600646040901050b560203485800d40000300c040460060a014203142c00a03141c020980340c03000c6000d080c400140c03a4240c402c1e900c000b00182820008888400141481d010390130f022481c0080540d54407400b82002c5a041904496450340d4054580f20b0091481403840f011041d036103400c3c1d030b1121200e841c0b4007800c002c40e81d480f44000019000500e031194050b00810a441700509514061807007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 956255107 1250 956253857 956253871
    0x70b1506130504090c050306090f060f070801030f0501020f180111150a0908090a030605070f0f0905061b01150915030b0c030402120609030901111504060b040608030d060302090f 78
    0x102440c104014100f65100880040c080d418150955490708003180c580502554052959071148410140d551000c2c481d140c0c00840c1c1c01080055414281070003400101f040c000074003407540340141481048000d5040b513500b610040401034946c1104114403070161100c0300200e0119420b0080e1039800400403686000d103e1203c180f00d54280c6821360740c0c00007009042c10881c2c101204001e030702c48030360b95a40c42c900114072860020500c0d04d800000200544003408030081880761012400e000c03150032000352400e44170207840f8035449405e4907481922904003402090800d518154034000781400020800c0c0070307550601000e002c1d85d0740702002241c110502d4403014104404147c0400c101821050081d600140020a0403c030002d14480c86410b02d00e054403007014581c4002044601940c201c03c0d4840203400c4c1401405a0035802e42d0207500000303004100a00c1c0b9075550080995a581c0c42d404400944207d10480c4c1c0c68000a640800041083d8001a41310307031107040004400b00043c524452244074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 956256357 1250 956255107 956255137
    0x20402031810140c0c07060e0406080102031306060806240a0e07020703050d0f080c160206030114032803030c271707060f030e01090206030c030403091a160f020402070b1506 76
    0x111f003480454080d000141c107550b1041e01e440c000a000c81e424005540101000e014412003c103562030544200c420550201040d40c0182d01040010054900c094402d010484081035241200000148400300c46400160303622184200340310700c0c01c3c1d000a6401c01d49211c3d10480d08003641064055070500c810070309400000d0305120018160800040c040d0400c00d51120b10003d014035154000380c00c2d034200341c00101050701401d2100441d864108050060210001c5180900f04d80d0485801c05407e880000942456103c1c03900308042803051071580b244a4107800d071030b59003005004482032298614442c1c144104600c03160001c0800012916104581e2251030380390784040414010780141c916003810700e81a540c0d0389131040160b00c0d210000d52107454a0b54025582e032a0600e8013600c084402c0d003040105130494018022101d440c4812141100844c0e02005905070503450910a44418050700940240c00403800340c04001504215500850302e03c1c406044942c0745400b40f0081c0d0007407031407030301e0291 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 956257607 1250 956256357 956256359
    0x90a0204120f02030f12130b041a0304050a23010f0b0a1a1905040e070e0109140604080d09150e010914040912050d180807020402031810140c0c07 64
    0x2c1146091000c254800380a8442109099048600f0203991010303070071146a00041c14010021410080805401380e071038400d05260901c80c403090203425a51036070042000000110702401410803d2030700c0d0a5001306100103000152906800600304506542515030900300c542030180e805000d00c10b180f220150404071010302c2c0c03401e00d20441c0525800c0d25101c02c01006868501c01002000c80c941c1341c550780724607654074508540b040001c1c80041c0f1b00c80402c00c02c400c01e01c010360b92201075901158210030046208a00c0c20340090f038507104d5a440003095201d00100701d204207800c032111601f110034080010700b52289808040d6211540c0c0e502090014102034002d100c2407000d0860a400c2a502400c002070381c403219a14500c0c15080c000441e0003080780411807034100041c030b0169a28160710200c0d4681c0c00b07007035036a8403900c0b400340c3c8500a05c62600440003c41c11403010942c051800400303000c5a4030b10b4040000c1c0c0d0010b100b514000104444044002032002e01c000003204c2e0142c0716040244026 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 956258857 1250 956257607 956257613
    0x609020306240705060708060a170c04020901050d090c1a03070f050313020d0b01080c0d0804090c0c020607292203050c030f09210601090207030e130209090a020412 72
    0xd070b40c41e04008900c5031400e100d4500410403c0108920800c1c00c1e88601101782046c00411807c0ba1a5a000304000c50b0324510f0350007080c9001c03600d4144400c0a480258035410144016146401001c42003a03100745400d03402c1082c840114545821188090b80c0b180d01042e00c3c24283c00588000c07510180400c60350719092015074810402590300c00510039a650070810b95a00044424259800960341449964014000c00c40300b4402005003c50880300010903074910f940340045e500940c462b03101c005640305514844540101254003032294018001541d804161521098141c4c2c6203481820742405641503128071003140b520680110801494030404c1401018800100c200d44c10089003007010520031070b8000c01d001c10103080c60388800400300d510b440503507060240070405203034280003001c2c04114040400c400400d07414150b5411207000741c0e0b03801c2a800c0a030b4407641c0c4607a80603045019403c00c0c01d03201107260302500520b141240e102e9041c0e1190784200e804d074081e5005060000300c2c0d041d411000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 956260107 1250 956258857 956258899
    0xd15060c0803040203030f040815010e070f0507060b09091c08060d060b0d060f0603050c0a030317070e1906081b0a030f091a01030314030907140d21030609020306 71
    0x3001c4e00c0242141d00e02500c0441401d00703604940d0008880c0e9101c00c2403000e210400c086a640900f5808440b81642e16003414010b25011906142409001000803501300740580c076046294241c0c0d015003817242d1410900490790740c131881c03051618840c006c075030160f120b458800c11600740036800040c142044030015480380c50044c44500d1006a0250400103c900003074040c0c0160000c881441d20f0001d00a441c41c104241001c0c0d440c01c00e01c0c031410f030b074000c03d00002ea01300031400e0050a000b100070855a807012001d0390312592072030f401c650081c0c10014140500088040100aa414607500c00c0c8068803210684400c08000070b0070300000410a000002000740303c0c1c0d000780d000004040c00400c02d8405911449122011000c0303014041030104d0040c401c0c5600280600c1c80c4407414064280b03989403400400d074854206004002c0150103641450301c01d44e4411070043c4a0079000800304030b0418002d50440784400610703008001090410800044101a078805d40e482000060176880502c0c1c584141320312 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 956261357 1250 956260107 956260111
    0x1b10030e0307050607050306040f1806050624070c051c140c0405010f060f05030f0609040809040507030b0909011e0c03061509050f2b02240d15060c0803 67
    0x90144014080b90011501c00c0258a010300320355192596030742050b0050200351011042025445410000c800d10461070010400e0625600541c000135561144000540013074005c0901d2040451046007a01902c00640000d10b212032080203c03480550340d40d818081d140000c80100701141074035113071034400300f4092548003460303441c0402903c540c00403400016003243e0080c4c01c0f20343c2380c601400050111a0300650424580c9000f418a00c0c2186480d94041c1c08813080201007078080c0340c103440030804001030b40c030585540140c0244103100e1032a05940040c01804c194240621034940c58020808000301842482d49400b02800ca00c5a01001524100c014000b408401c0080542d1944002115001c03281c2c240a01d0410f580d03944845403504040080d000001c4071158415017045007460a814800c8210f6482c41203400c0381c2040304400da00010380300c80351450030000741403184050442280c40080040c00180284441000351002c0b54001c011100c07154010b140100d480e001075000482c0400c17014503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 956262607 1250 956261357 956261381
    0x11030c090f09060f191e0e070201290103020f032401140a03020c07080706050a12050f071d0a06020a0312090512220e190b100e040e07030507081b1003 66
    0x980000e90342d110505081440200a06e010784055005000c2c1c0c1e2002d6403155000b40b0b03584000c0c04020341e100002540c0c0b8041d03039140307140300c0e03002c00e0005040d0f40260142d82c0d05500d042c0c988c0740c484c6031620002489103031141c8441402d10101507002c9981d8080c02c03d44100108150041d424113410407010b4000b0b600200e0a042544500c100000d041c1d0800c00c034101c0540115a949501d40c1c92001c1c010380003240058100c0c0805043c20b00300a0244940d41c25a43d106116103032800c0a00c04103205c0d481800e440c034110a030010f441ca030000c10300e079400044c4000010700c40c1da14009003406440c075040860f48040c4004085400071209002c1181c604070150100780026a024002d04c24000b61102401e042a400504000c0c48441000074065031941c0d0429080c0c850402070281c45055800555001c044070240e00c1402240d10801070203485662281c1240f0b45070000b160001512414401d40d1000702d84034104452260419501401800d10302031808040d010785880e0390480d680b0410b9000d8042c0d24545 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 956263857 1250 956262607 956262649
    0x191211010b03030409140a051308090d0b01290f041e0801090b0a050105100905040c030204030609111203040602120a2a11040606120902030111030c090f09060f 70
    0x4001c15941400244000e0022803000035902400a0700c08141000040050507290318040070080701080c440b040311606a0f105102554885181c00050b601002c040c0c0007030208a004000410707840c60700c1101d042d280040b003421031170580d24940303000424400e01544402801040c801049160b464040550302c82441481c11007010b07865038119421102d07881001d4600425500c280028082584215405080141c80c030700b0030903800c00742c0500050704e40d100b1107000c0c40c3d441c40c50200c0386101c0e5042c0c6014640c4401c084c0034100b007500389907407208010711107c0e2280b002c00482d00762001000003150211503840c3c014105022481040354503035041381da518024003000344021000101c4804840d81c020700404400442610f017418000c0d500042e40c55442d024078940101444030301c3d006180c80d500001904c5000c078003449944007080c003401c00c8440b541103d03100482800b1100070104040c00c07500b2425100d0781000a281c80422080380015107a031174022441007035800b40350034001038102040e0032007204 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 956265107 1250 956263857 956263871
    0x50f0706020c0f0309010e0901081515041a031501050a170a060e01091101050c030f161205030106030f02090a0306050a0914030a1107140112090803010b0c19121101 72
    0x2c4a0704181e20700c40052200c2c0c1001035000c0303156030803040004071503500740c51200309981001e080550358541c1162002161010a00044603542800c3e07103001a081c0c040c10500005428084c004102114414013621a0040700c0400000003500c41d15a03040756001040e400d45a80303481c03002002100c02601c25881c41c002c0c0c03489200403078498040c0394240350810b00002a000082c1c1800703880740a041c0902410031108120700b6640e28800416112540c0c5280c03485940d070f04442d460b002064803144401000114011a2100d0301034021014604a070705648050003000380c020401d2080f485181011075000c0240350080c004903101d54000c0d680410680d50010314840aa11011001461588501c80c642c1c400154400310992000303546056461a60003440c046040601401607081000d0a00d0f04005989800020081441d005040040d070001c6e8940e550b0b58581d61502e945074000603c40070a44140d5031811843c440e41c408080907a03401190400104100340e9045420140ca80c2c0403e40035134a80308 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 956266357 1250 956265107 956265127
    0x20c10030f060b040302040b090402030615010c05060c131a1606020c0f03041401020a1208190203101a0c060a0e07083c0d081009050a0c0305090706050f070602 70
    0x4a0900034000f00207410362260314610401064908611520780904200414000161000120960070082c1d1101034103101007078800499040505010240541c8551014800e14203001c00040c941e004081903c0d1649589135402d050340304404401c4081d410800700010421040721503007850b0391500c2204050f19183c42c000210786845540b01d000c0000d9000004c0c1049034000480c0da1210344002070010300703000c0c65603440707510030200c0b0b145100c0103011441d00014401800c8030b903010b0300ca0304440821505c905125080340e107120982e0141480d0540220320004400e0403210580c0e040d000c2c3c280003007020342d0f6814294270140081c107052101c2c42c03040f1180071401e17001c1406001d040c1d001d045c90315000c00445480a8103032090444002a02007a002c2054003605000f003501002b510b042d0030710714081d8480d81100c4055150302d070703c65200c252a2100348040b2181030b400006903c203155400303100e1925820700190700d900e02c43c0f00d03180100d00100a144040307807040b0094801d580c01060010b0034000c02d45 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 956267607 1250 956266357 956266361
    0x1f0c05040909061a0a08120306030a05060702150c12061203090303041e0b030105010c1407240215090c0d0c090203010e10060f20010e03131a030601020c10030f 70
    0x1c0b401c0b1100c54555104c4031220011042c9158601000c460307100030585440d120580340c000c01c010440b072440c40040018401c1d14100005000980d000741101c200e031501080c02902d4140b603082245620f86120046045d1321071030400d6440d441c9200800900584415041040100c0c0000209503280401d10000d10b8039030b0203002900007420107214041c0b02e210700400320202403145400c0002403240610040c48283d90016180c203055500400c00c0b0000518801c03841c2c03030301d6919442104a013180d200307028500f814054129410114640031620700b10010580d5858040c0111400c41182e070040d0030400951a10010800b1418040c641f07a0380c0d404e440e5104002640d0098201c0e0314495000011310112061400c00c0744020003a6180c01c03035118034038003001004000804d03016552400d5884070046014401e51080765a2a00081100e9540201c101030014082040c450000b00c9500084003a42c1800b049040700d11422050340034054000500b42081411142d8800000c1003603a46c8445a41000c00c42c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 956268857 1250 956267607 956267621
    0xe0108060f031606031805210d0207060603020405070906140a1103030702070512060c03010306020f090a0905090c04050f040206031e07090510052a120d0905010e1f0c050409 76
    0x100d150f00400b14100700c1e0140a40d215483c40d50f0566141c0118480400c20106103503401d042d088403410084a616070149803035004040f07551240c2880094524100003850b4007d0b01201d1095405000355561804290f620179454407820b40480d00504081280d80a00c0d00182180d20042c02c0c602c1c0e030060001000c52075904115441800b60b40450414050b40c035042c54525004400741e00141003d19290005050354041844007d0041d9000b02c4e058200c004498141c0700300200103000000d00a44c1c1d50101c1c0b01138003041d0f85002d5213008218401c0043e06060080603c034020f403012100250b1203642c280040303903200400d101c1e514100d030604540d542254400710341c054580d581d14030803000d0810f820001c040103030005040034171100304161008070b110302d81803900441c0c0105150043d46000b5003402c0c01d1100007074550b000746d540000c092800070705582c000c45405004030002c10007812116080c5a172007025200c590700c0d24450421100340420950000058445075241c1181055500c15104041e2000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 956270107 1250 956268857 956268883
    0xe0903070f0f110a03080f090f18040605010803070b0c09011106010b0c102d1e0501090c090b160201020c0907020d12020f07032f07030c150e0108060f03 67
    0x4100c0340d54060003a005100c000d03d0004840c06030b1124610303075441403030344038000035049000c0d40416141020703611010205c07071006025000c442c00281d01e40d0305458000c4200c601b1200300c3d10300301c000f080f12100007055503d542d0780444406200c0c0c42e02c45c10b211198018400c028104070308000402108081401814000c0c400b1510305600d030b40703410b8106030900400c0c00070400034900e0111a08a501c0c448403800c0400460b059000014843c5600810b000d81000503c100000d0052040c0c0380882d40303150b11283c121810301c0301c02c10003007200402c2111f100102e0300c9100203c900901405801140881c540c074801441401124030182021001c81c3c0d5940c02102d4500243e04000c2010070840d802c082039010554032090210318103400700c4000b4203036010b10400601003050070244040241c410344607016040726800020320f004c514006000340d40d103c050000320381d40140c001000421901e4a0b015040e940e40c592149241c0c0e011000044510290051429508c03c5082c078105403982c40170320a0005100e1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 956271357 1250 956270107 956270123
    0x402040b0d12030e030a0c03081305011104050a0f060f201002031608160f030e0a0c0812090603060f0f0d110a0509092d15041101030e070e0903070f 65
    0x410002d01213444011091500da0070400c03a40e0901c1c3d03405140241031581c14140700c88e13551610305034012035040310080140305621701074206030407540c072402a104880044800c1c43d20b01e900c561b0f0005186000380700e0440440d900c804c090101c0d5006002061010340452001c0b032200c00b4949040f0301d0954042d00302000c0710340c0001840046480064500c2000c4c00d0350034444c1441c1401031400e5140368005101204002e280350003004494070980100025401c2001120f07486191414000d000303144074452008581303d00080803824030030300c505690903500018078542c116600d64040c02001440c107140769506c01605804011140e0301d0700c174980380b403501540b4036104000c0c680041c0000c05400360031a41c4a200c400d01048040d45002403280b0740005045003040028481d074040c1c003245510a1071721070460181406c1c01d2401c40003901d8151060340100181e41d00c8004c6000150120781c0e605038051519044090148a21b0520841c0a074005e035101003203a203880000c3c1c54540c0754111520044031824 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 956272607 1250 956271357 956271383
    0x81005072c0906030a020a0b030711071e060924050408011409010e070e18150703052a120411040e0f120a0f03050702070f0305062e030b0402040b0d 65
    0xc142041c0d843c0d07001c2c0d8190010a84c0c5a00d030380011307216140c2840740c01e6a088001000400991054219800300111242218400354507840e0310b150f0103011032454442040c8840e800100240300d00307200c00c1142c0780300b0b1a131280039030300700d100110a0307001d000b25030f05002c0200000a411403091140d000e0780c00b103000488042d07003040c0100714290f60000c0040f8580754840501841205002101540c003d00a40440c0c1e6690000c882c4203406e21b01c005900503000f017400b0303082212140d0103400051144010b41040711685603600940f1403100300c1e14852414102080c0180368014095007035041e00140100d00c40440c4c49100da0010782500da080c25030b45619040720305403800c203620412180881c0b00d001c140d010b06101c0c076504020211100024064205038681d800700f00710354003c4c00020090301501c00c5180001c0d4580c10120303640d80303056800c5100880d0b08030a8091a000909140940e181200925001c8910f95110001d0650014006a0740556aa24074001c266129408000c0c03d5219210318072200b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 956273857 1250 956272607 956272609
    0x51b0d2c070902092b020901030b0406050108120904020a110316030e0f06090d0c090527060c040603110f0d0501180515090a0e0604240204081005072c 66
    0x3004030340c0095041801407020320b203950340e5a6212541030f9164410a6840c00c10840d140c5c0341d02001050203900459180004001e00500905051149004034400d01240e640d5461b030b00c1d940d4442d410f4101e0a040705004107805803405400030907185075589030000c0041e05448040342580d00c2880c601a4102944d03040108054018410603000381048aa50b920400f824020544a200b000000740c4601c440c80c000d20200005681601c02500080000300210f143c0342080e80d0712103200341080f40304041410701c0300c0214800014250b1080c0c10aa80e52402c01d071800500360081c00c042c2c40da00b007000380c00780800b0700d200b40e105015100c0c965107500d0204603545029075428400c10000e22141607035040ca005c11101c0e08400208507c025015141c000d080ea6901c640000248425040052180540003c0c041800746601602c2c0320b501011210398801e41d02035000c50304030310852054040c03d40082e040042040c04550002d0b070f000039203003022000c9800081c840727041814148181d94002e01ea1403042585 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 956275107 1250 956273857 956273863
    0x601080f01060b031f03080f1c0207020d0b100b030903070c050d0804150e0d140606010c03020a0f0203030405030313150329240c10051b0d2c 62
    0x211025900c020014141468181d04042c800106070302050818808003295039106035015100968000c600c264039407081c9900301301e403a441051172a16600c4118a030710404442c610031034044a40c000d040c4403c00c0990355a44d0448503009012001011440200042d0031141702c2c02103100f501d0b44406035540e2a400c1c0350140f41030380e1a41015001d0589001d0505c00240824111410b43e4220407200c140003031204400c54584400c0742045401090710020482048000c4180440c1984064195422036035218011102001c2c1200085c0041e4488040c48000c41c0000340c00d8480c09001400b501e01e00343d120400300c2e05d03517031180c0e41d545240307440041d04210b404131b500080c07010700c1d1103440c0512018501034580360b010704000000c00714a5214a0924082d95140300d0b2180c43c0c01e201e0f10035100703254a062a0039500380c05c00c0d142400540544410110501c1481c403c1c5c0d40314071105980380210354044140c02c9115008510b408000f5607503244081c1c0243c600200d0b001004042040303006000200d5800745007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 956276357 1250 956275107 956275123
    0x17030702040e150c0304050102040512010c1101110717040b0a0c05070503070303090e10151d1c0b090f150415110a03020a05070c0e0711030301081c20060108 69
    0x48190411541011012007090f8a281c200b041411100d032030b502d45007091402403140b0340c041544134400081c403600d080c0c410340100a001c90f054075486001c1c070960030310fa42030752160410005000400c0044c02d0014540c611015801c1c420344030300700e0a164603542800c10303a41c400c4190320082911680f090081220400c140b070017402d4250060402c10f8034599001d171240da0306028001c1092043c01c0000e00700174888c0f0070030000b0400302c02202080703034006c01c2c05441154000441401280b0a180c0c1d082c0718240411212640c262003641d50200b032a03280c45600440e0406000c0c00c41c94000c103083e0708070580007005080d220f4a1072074401045401c0a1070400c00c3c49035a4254592014207001c1c00a03042d558403800c1d02d82101300d5003809603451070a50400c8038a4400c0c6200203281d4140d0100201e0000005e801300c500c6040329840d9400c050303e47e402c9141d540c1c0401d00c41e00c405980415074401d50040211103000e20200503080c0346000a08000c18540c002c07440f10342c0500c0310b40c060070041100780000c1082076 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 956277607 1250 956276357 956276381
    0x16050a060b12120f2b0c0e0301060510081e01030b060a1517090304050315072007060513150f03051014090402030a12030c031a09130503041703070204 66
    0x1c01045036820030f03030f50540900f000c04c25a00c034000c10303407034000c0007141070183d00e4003444400c0000e99064040442d008100705146600003805240c50a40241014450b00041d1a40200000c00c0040e032007104840100006011246603010b201510090340089140f89018600c10070980c03000e40380540610403003041d00d901800e004d204010300201c0c410341040c070310f10010041a0900754031780c1d07400800a146228551140e03801d40b141d6101c2d00368203183d04849500900e01030b51040d000030040400962940113040c100c003400e0700030040401483c0e00600040c00c14111203040c4e03003506503658115200e103074100c0003408041a040c441c4195030548c5032090941c050509144694220f0401c10b841030758043c80b5040a004071032070030200341550f40400010040d541d212070240d402d000700020003800303407841c0019003010070300300250041004010040010803407005031030500d142e6074031100f402130061600380c01e42d05d5000801001c03803031264130f0b03420304500e12042c0b00940d03458540348140310440700062800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 956278857 1250 956277607 956277613
    0x30b1002150c0412023a140303040c0b13090f1505061c0b04091b1707150302030411100201091e0302031c0b040911040e0f0c010516050a060b12 63
    0x510107903050b0a140c8000b0780d0151240561b005120b44000c0d401985000c6107088044240c5c1030422060200d420002954494800c02004801d0b1002e2543d684c00281d50082c10b0181c8200b040c8000001c074000362580c4500c00c095282401e80d12400841110040b000c0c2884a41d290160a035108880120600040c0410382d40c079440c00c2400c02d40c0300484501b030002500c413140c441181c04640e5440c1d400c48000e8642050f2400900001031002c130008030b815100350100104a040103681c440000703c0c031031049484c01003c00d503907000d000c0400c800942c40280111094180112450b5813a101c000204902e84c400c2e4000092102407400e001c104456000c0b02c2d00c80701d840d0000f10500095000c02a070710802a0f120160140c4100c90803000054410200c07029001881c0844034828404443d60f58202030784190f030f0400c14014003611079515450515003603a00d1350721003e2148803e5101d080100001c0100030407034a25040241e54050404546801c161140c0340c85201c0c4c000240f819810080080c60000c0003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 956280107 1250 956278857 956278859
    0x303090b07080a05250e1311041a0a170612100e100911010f11060a1d060405071401030e01020c1c02060f0f060f060705060916060507020d03030b1002150c04 69
    0x2c4c1903d0680000c0d40b13020481d5040500b8460749074081013401d5020314400c180100c24440048c42c4864004c2e01c07a203801012100c8203035103403200540495240304c0580e9601d0702c00a240c2a680078131850090242504440000701c0311030100414001c00320807100004002c600c080e400c82c80c180c030309810842100401c0d803800c81040005000780800d0500c1000c20308044d201300d240800242d40c0f10320701c4808150030380910000c00c0f40d02d560f641d200b01d00f403038803405401c03182a20681c041031f0ba076881114010110341c00010b041c08001c01c40400080303040303814500811080c011055480c20b907000120000d016900150b44403c124102e48001651500548010308640c40d200000028406000c1e000d8281c2c285600041841034030f03091019481d00001510040d6201800e181042c0d9a010841c0d00348440d014190445d00b660707803e0070209080303854540c1d0301c9040079000c1c2c01300310401c51100710850600d0b9441480d203d10317480f201c0f500000b61400b03801400d114146955041d61140d40100704081d03079041008 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 956281357 1250 956280107 956280151
    0x10e0106230618042a0914130506040e07080703020a0501050f250b090a17031501080a14010b030f07021c03090501061806030c09060305060708040303090b07080a05 72
    0x1550034880c0c5910901d960800b83c0c00108004007860344848405440714003080041c112440e00c0ca80c403800180c0d8131800c446580c1c81455035074034050707000984d0100d101d85000035100843d800c0036400560080c80043d1b600f200f504114070b00f031541d5000700c40343d800084c0100190302c0c1c8031845000030003084c00c01c0e519010195203240050f1280482420311030040c0d02c40c5c40300d50b000701c810300404070703501c81308150b55403d10803c0c0c190789445414046540320103150303210342c0040446003540d006035074681080c84170100700300041d1900d18004210050b43c5903220070070070b492020000d99074000c20724105413981c2c4e42032164140034100e10043c040700c03d5505c004411a60507007021410741400c0481c1c5400520000c0ea458400d001d041568000580902240645040020075030f000d01d0071640716429001c0300903626100343c81920750343d120280c0140c200000043c1c0341401030035115485403080c03400095041c07940d610140741c0401a10300200107004e940401240310200e10581e43c00c48640d004030000001485 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 956282607 1250 956281357 956281369
    0x30608010b060313080f0406090503010b0d030219020609030a060c12020702090f0c1201090f0b030708070621050a0203060109080a020f10030f110903011415041a03010e010623 77
    0x9803070b0704d0f01c803441c0003081002e0000400a0301c41c842000c0705034580d11940c40d1402099001c0a0092501c00d51030083ca85255181c03d1581c1e0000c1c0e50b164015003030707510713011103050222410120160f07048041048503001c265000d00c40c400204d48a06e0002541c1c240c5000c2c0100180b101840080415104100350405039803600907680d44a0126644455595104010164540140d0b88004400203c1d200040f40891154200c0c111040007403600b00a08200d070410996111300c2c41c41695003507000004140b01041c4202100c0c00902d00d011001411844504c80910460741e0490b510715004d41d022080c005150f900c45020713001890084010143c81905800080b000700d01c5940e6144a0120420800c0900b8020b420452100c0c0c80e110f400c00041112050401d0964803683c041842540390201a032100148501194020f0f5200c10b50007200000160522000345141c2d02440740d41c4811034a140c0c0207617000d003e0426482e041c8000400c115140c0010002c40082040011011003000448420540c840c0303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 956283857 1250 956282607 956282611
    0x15080d0201150f030b0a0e0105240d111e0a080a02132d150e0a060e0c0a0e030a02130b0f0a060c080702040b0d030c031407030e01080402030114090a03030608010b0603 73
    0x300d07017115242c6545180704002d05c80250070704081e50030941080000508000039443c01196001c0c034a500405c0d00c0e04104812400003001062690080008540d608052513160200701903070004034460620000014021892035100000e42c2e0f110b01d281c0800c6050580c0d420851031300c4400140544c50410040c00280c40e100f18807440c00960b001c43c564080086038000c0843e280c0503804d040c441c2510b4480c000d030308803811101e0045040c00c1c2800096052141c101292151703000d1185030341860f02b11301003100d0035000b006c2c0c0315038140f00c0d400c44c0e400903030b5521803080c9070500300030310008480f1281024410b030b50403250000ba2040c03801d4401000616007001034854942da2003001581d40e035070f66100050041c0901645907410000780d000200070503400003203a00500e0300a840e48500c445000e03007034140074414040c000b80090f40d22001d40c42c00c0c0d4000c0c0c2c00300e03800c42e100500201f060b0301444e15480410508680d0280b82e9800342d0400c80c02e25400d40300390009003c035403001b8005007021b0400700c0c00d01d02c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 956285107 1250 956283857 956283863
    0x3050616090b03040b04240b1801080a0201051b0706030b100212030a1806090b06190b0d0509030c0f030d0b032d0a1b030309150f030c0315080d0201150f03 68
    0x490009030400c445018450143d03400800d0803111801fa20035000001c00160b0055400b40740c00303070306001d00d00d1103002096048842e404000c0c03103030b0900d9600444031500642514849200101c081c00032400050140c03070040c0500e0f82d00040c40e12682020026413140030000700342075401102c0e06d41c441009980450760302036005c1e00003044014100c000b1007040303d070b04900544101c2c6405000c42c00c101107094801d00480d41103171042c10f038043c1e50504680030f00e164482d41800040400003106000c4060f0001540869401c0c1560304214150320800d04108400c2c9811886800000c1d10207445002c5102e18171509005800420701040301c408010f800902c21282d00c00c2c503e01003042480d00003410040110816803000000c032039040c001600010007082030008401003184000c01240c000c2c54134140c0c0803400c0c1c4503607884020021003041a8000d080440200041640700c0c80c0602c2d000c0745004010340102240b2004050420034000024215600c1c1d003036090b4002d001140401c4001d01003802a01580d070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 956286357 1250 956285107 956285123
    0x91a06070317150402030408070209010510050d3c0e210f2a1002030601020309280303050c0607030e0a0b2a070b01081f11040e0103050616090b0304 65
    0xb90080c003028050101110325a000e0b000108010808c401d0001074412144262007003282039890360108a41445640000c0000035000c0c0011549031555403c0314084900705507290110320400d016a5414150320180c4000f035112885ca8580d40c01c00030b00c00c0340301c07040d90140901a15034410308401040b1810a80207a0401e0000c1609141500c0840c201ea03411380740c12004085010b0320360740502458800d15030080c0540105039a903010810079008a07845480c050780035620345400b2504101042d492107640001c020f070b0f01d00d1040c86040400260502071802034440c5920b81c1c0c2030404880c5022001000c0e40c08050501c5041340704442c00248a07408139520103502040b96075011004c1c0a04540404c42c1409205c244605500c0d00f42414004c008481c00760030190351581e2201c1c449552480c3d0060070000e4003c210028132101c203142e03072000c11221f42c4404464905552106681542102070b042650b07250030031002e100c1480034010b502c241200e21800c2640c446443c20b840807072940030041015114035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 956287607 1250 956286357 956286361
    0x7140c10120e0607021c0201060303090324020d1a0d020904171303030c0201030b04060b0f09030c03060f090d080c1209100c0905040b06030907270204091a06070317 72
    0x642600030101002804044500038503213035100954034140d80021815103400031103031501d0f45e1300c1800384105407034060715418156403445e601e8110303140a20344040107409005040b0407003c0c031140000d14400e00c101c0300105402e031441c1402c6189160780c480452260b2060b000840040e21100e202d160b126800c018010031042003148502c07814070650901c07041c071030702c03980c008410107070420001c04503030b4000e0f40c0402515075984180022221513001c2d5003c4281c092280d0407401c00d210005001e0600042d056078481211440803038984001a0f4858411400e000104840c0d0041001142c0200085282921450428451103443d900c11418550200e50082c40040c004179810494501050201d103410130081d01c4d441d030000c14880c000c0c000c1c00e1103a428040050301510b4203405481c0500010b402030b100032440c0415400440424683d51005101035000b00050041d5900c0940001c0911030700c04102c400c103d101c0baa41414054001030301c40d80d414869000883c6e0302001d1510700301544607541100ea = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 956288857 1250 956287607 956287637
    0x314090433141014071221021206150d020301090f2304021c140a060e010b060d020904110d05010501120c020d080705040b070309050901090603080f09060409020d0207140c10 76
    0x280c17085190182c07800c90700c242403007202548500b81c40c45056030050442100d074000c103c6401a40318880c7d18140c0c0e0003500300803030410718089811102d0581040c0c0c4041c5480500036072003040e030f00260f201141c00c40d56400f080c01c580382b09000c1c408202c410a5030301c1641500070241c00b074079008080c1c4042d0007910310400c1410110380d200502500e80d0341090000030403030f00705a5003a50701c000c180821205203040c00c0041c021031005004070303d18a00020442d605055802e8280c100035042804940c1d8410780700c80e142c0c245000080c0040040c0140142c001c2070941c140360000d010020b074041200346052034404125520741d0301184900d0450f440b4942040540c0701c1103802c0b82c0f5030080d60000180c054002649004141c0c0000c114421114203544a00840e130741d0700c0f80300c000c0b04e03085c0c840540215000c00404408641e90802024803101c001d0043d0f04041e1221480c404a0f00600b0b110b8906960025986044c408001c9031000105e074050020801c1e400d2a4011824140c021030421080c0f003c865005a18 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 956290107 1250 956288857 956288897
    0x3180b1509090c01020c09010501021f0f11071103030f0304021909020a110f160b030c0d0f062d1205030d0c080612070303140904331410 60
    0x42024020022591402e09041d40d41e10349a02c2211103000d4070545c480c0b04024188448094100d03801600500030207031400c100090003034031580300b5040482d500d00903017a90084512508003804803143c219615414149003d4000306158003144d4880c1d0301c1840300e565020380d68030440c2d130f0043d41600c10004041c5883340c0180d000c140e40c2c00256110340081840704040794801c001e085145144001c48104103035540ca15911900c565a102001ca20621814009001d1242c011500a04245401440d1440c03411070081260f14008489034a19200c0c6010009404540b50760309900c0c8001c04a020044450512018100d402e0b2003200000354260f1655001d02c041401611550a28254148200b07106043c1c0109910f1003110205e1141c4410011143c9403100000d15105507135040e120f801c441c107a00c103c4108250003080c2e21584c456121520008034101800811401110480e2009000301d00d040383d650100842d900000d20412680342c4001d00d07a5114184070102801a003004041c01580f04142c0d12 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 956291357 1250 956290107 956290141
    0x7020d0f02130f060e150d020120100e06090d03050919050102090301060b0f030f10031b05030705030f060f040303021318050c0711150408190203010b0103180b 70
    0x361160300065220360340c4110303801800603d800e150f03081040d0341d21000c410003000001c2e10484105a5945105900c60802038101e6000381e00504101d0001d03846a114030400c0021540c0202d444e42141c5c500e100f226009000b01011200c0200141c0b20a180125aa5540380322072112001003503203c001241161101344840c0700d050381282d40200d101801070402c0750207903101007031042c020343ca01500015410790401c15649a801c840280c0f41c595102e001410201c20343c06070a02103400b9031200008009444000150310700814640000f04880c505010142420200c0c0d02c2540250028003d030304412a0100341d05610440c00600c04000340c40f2414214024001c00194000e000011103001c261503581030b600301d203003945854091000d80c1d9980c8905500740035000004001070614102200c40d0304e0903500340c00d41000f60f10b0020781810350700c3c01110300e09a140c110112008403010b07480815420700f07004100313040d8020300741484516441c030105445a010510301500d61850780d004500e03040c0413550740c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 956292607 1250 956291357 956291359
    0x312150303020c0f0a3b07020c0f010926030910120c09051e01030f021b21030f0a021c0605040e06060307090e0325032307020d0f02 58
    0x8816588a260180d40d0f4000d84032281c3c400e64442d031880f101031602c1c502003020f031441000e60211301404540d00300c98006411404181a2032154a000801282d800340075105d82a80d600030041050000144a00802c10000041c1009025207040c000c02c4084e89081e200c0c083e22400d141c2c010380b00c280489055020f88214260710819158942901540c06250141800c1e003009007001010603500d42a14001640e2055030f411141c000c4658150301e6884200401803501810042000940545540100c1c1d2080d5542c4a001103141c2c0d8400201008010420041d1914404690500301904440705640802000060040401030004940c24410380648601480042408141942c0e01e48010040c00842c02903a00070345c0342c56410324105000151b01409030b040a40034002e640d05180c0c0ca0000703005003490802c2c8a100c10042c21100342d8035200c1c91240a0710300d1f20221075060f47c1c0e103001013900404c4820781d98903c40f40c500003a0210425001c0b12502c6604075064000c0c0c48c0b0610341121161400740c0d0103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 956293857 1250 956292607 956292641
    0xe0105071d0111030a0305011703090109181d06182a0607080315010e04140610090f080618061b07021807020d261902090607110301050105040c05070312 67
    0x695945d6095000941610304040c1807107084200080c0b41a581d000307050809000400c903c4080001c030060703601c6228980300c03400c400701d0006440084144458121441010181d00a00030800724503202d82c8a048241c0e1203801070107603a4041400d0406180000030756060054203101c0c04501a030340c54007150245584662050b4403441d00c1c0c9511540511310415040c041550048901164641442629038405861070300c0030b0750f600c5200501941c07141e034140100c1840044d030300101c2c03202540000840200f952000514503441c001480d01980000090078035001c1d801442401a110403801380c149651140e444120784950281c000551800580b03c0c0070540e6801010510483c280d010400d41c0080d6202c1d2a00b4141241c54504d03503030070150f0405643e9500720500081035500e01c0010112182c84072600c0054284025140080c1a44c0e100c000202d600078114011015282400c0c06001d00400c02214104a04008003402038464441c602d030080401c800008030900c000c04540c0410321440380c02c025 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 956294964 1107 956293857 956293867
    0xc200a03201c0824091515070b0a0c050702100c03050f0c0f060903310515030a0e0a020904060f0917090a0b090616140a0308010302040e0105071d011103 67
    0x280c0c5e0f40c440c2d81f0801004d0015801c1340640b203000e0245500072690300340a80803004135a200840360003402001e00040300940d40c0c0d1105031034922103e00b0a554140400c2c94221590303c990801c0a02d6091b001c50107810a04e4001251403e0440202c102e600300c0e2504500b441c0d680c09070398801c02081c4103592445003842c920342c0c0c2c1207940c02d0030004402c2016407a0000a006c0385420118402d040c40e011041109402e401d0003840c0744441004082c2004c031540e42c0120360340b4080140050941500c880802d90b14800990100031610741000d200030f0211003448014910364404000c842c42005001004a0f4540460040b5500180002c210301d2400301c00e54011684c00750307400410745017440d00041d202801d810900107504002d11996500c980f540c11841040215100102411801d80c9802c040242980e04900030301d607240d403031001a0b04a070800ca00100c3d103074805449844410f000c0880e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 956115107 956294964 := by
  have h0 := BRFrame.cov_init 956115107
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 956115107 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 956115107 ≤ n) (h2 : n < 956294964) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
