-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1565
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:36:00.086897+00:00
-- url     : https://prove2.me/submissions/683a631c-4df7-4b32-879d-cb77ef5f4e19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 281294964 ≤ n < 281474820 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 281296214 1250 281294964 281294969
    0x609090509010510090c141b011503080901050a020c0a0605040905160e0402091809010207031106040309171c1d150d0225050703020f0301050f041103030d1b0f0504 72
    0x44d601c43c00981001d010b0070050002c01c020f402407000c1442c55114891441c0c1c050009a8118001000881b540380300c03040c25650607000c0740d040d42c041b042003400054031000549804200a03e012a00ca81800c50300385d282c200442169607000722205400151590f000c0c00a10655100100a112a0b21103041244c0c8a00e50700c42200b02003408082c8039042810150301030140e800d0001c024180301444400d5800f0b46402c159081d4400b80d40001e0741400b8550820101d4a509080b00c0050085140c16100240402003c1c01b90035190050380d400e1810905c030401c44000c1c0201e00900c610b940034080000642404c41c1c800d010004c6078221103000040b403904180d07003001208540c2c00301d0301d00086050614000c0d4000403152402841c14240c01e40c825104803074901c4100d00c6100281300b40360440c0104000e90010030f00740c9200c0d0b81400100401c1504440011742c005910280c2d4400e20b035020b400190035030040140100700f991902c041c80165a0081180401699554a40c1007416545c60b0086501c0d200d2030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 281297464 1250 281296214 281296231
    0xd0b0a05040905071a0f0c0a030315060e0d0f1e170c250f060c1109060f0d051002070615090e060c0f07080f0904050a06080d0c060b090106090905090105 67
    0x1300b04520b01100b44540100d200310394086140074003803e243c2c0e4450b04240c0c9002c1c019400f04215000701070b09446100200c0901c103c17034044a03458a44008c0c80100e030b850a0a0142840141510400840200041401c3e901804241400c400e94882d16802c0720005000e6601140035018280212604002c640ba10400480600011982d40031400c15813600211b1186102280448c0001c44a45400410300a44400c1da56070314021054288600d13540c5261007081e00c500e03152000d1144903a00d03000b61285945059a080c1c0301c00d030081c1401c3e41405900c050600001d03000003082d01c100508c980c00480d2f003202c1e8202c800e200340d4944103c90201c444880720300d16141d00c9080402d9240c2d0480d4040c000750300741c41c802545400615034828042c0d8011130b40151070200b000c14a0b0300c40746440d028296100300c6c0d60504010042c6010200c580d02ca45602180c4244060320b4030100c203005058004010180028203000300c0f07941d680c0001820704ca13440c440d48190364940000314400407018050b90740508080b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 281298714 1250 281297464 281297473
    0x30c1e010305040f0209040308010f05040b0d062c030c0f15130f0f06050105030c010e0102060703020904021204032106030308010b0c16090e0f0f03030c070c0b0d0b0a05040905 77
    0x5400041d0010000a0002d45500702c003401100010b80d281211207106078401d9031000065450450307103000e03441880d08102c6c80350f400c1603121600354032011562203002e600180081080b414003802001c0d17950794070000100d011808003a507050b000c40000100500c0d0020707000c0758001d6100c1d1040d01e4035042402548010780341c240011400c43c800003031450f100c55004d641c01d0b45a45d4002e80d45c0101c070b4100c50703c0840749541c03104010002840c05000c144450a03003800d005591038130700e000007508ca050003010304050580c041090407413500d40f9030544594503400402c121080c281410042c040358440d6290503500706c414052044201014007400c000c80740c3c15111082164208080c2800c2e030b0704269050021842060203503502c001d410b21324280240a02400014181e007240c0e0810301b0a41d002a501c1c640d5441400c100107861400405c0365440018070f440a0b071510b142e80b602a02d030ba1540d520036507100c20003061032001c100300c81c6e100020481044844010036a034840074481078075400000500203800 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 281299964 1250 281298714 281298769
    0x1030b0606040e090c09090f0d0f020a1a06150408120702011205040606050a06050432032e1802090403030e12030109060b0c0d0309020d020a0311030c 66
    0x508014a9801800090103141025140c0682140405040701d0b144400e602c0300c090340c001802c1200c407054009407050041d101c66014044810741d144001c80342d42d401c0055805500c1c0003039100344100a05242d101c00003c2c03070310b040c1600243c0c901000351030480c82550200c03050010000f40070100d6049926100113420300c58002c62a496103501b20341c406038144010414011145141449070f640b00c3c0c2d1144100044003400c05007031288100c1c5030341102042c03150401051009888840c10000c0889450384000c007815103200c00703030412a80d140641509132240040d000c44054520350081c80880284040903803070715465060341d003074a0310311802586011712a880e40c80036082100d01903602600030300b0046003004900711441c2c03500d43c4001101480e00000300c014444000240070701c2d801030010400060078031800b041a1601d42d40ca00c1e90000502d50303203060600c21511030482d41510305400800d00c40340d682c1e4a007014070300c146034044628843c0c090202c0c40100c62400c4c0c0c40c2c003803082c2603050080a00f100c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 281301214 1250 281299964 281299973
    0x20703060213051c030e120c04180507030503250308040308060f1903020f06030f070507240218040905060106120f1109011b0b0610050c061015050f030103 68
    0x40c48081c442d011940b82440104458880c58542440c4065507111005500a9814000c008104290319240300d100c0026900742844000284031411807011a0006202000034000302c0c40003074134150041c401c0c02203100000030b116000c0041e00110910b403c00c400d171301c0c1400222403008819188000c0c00720782c034100410040381c4558641544014040e006c0c001c044010f00000d1110b004030121141702c0500790105004606040310407034041d010541c1c2c41c0d819402c040c880f41041400042030701c410070002248050a012212100e030042d40100c1c1c0c2d841c0449202c4082c4017000e9409034101031000305580c0b40c00902403c0a1051103005a006406401180d00f0100b084442c540c0065880300200d880e05c50045010b8028800c04452200a40e1015619000c07400090308103010007104d14000e1701e8403e611004225100780d140c3d444a01240e040d0500d80272030100b07aa6900510409503a40c6c131843c400c02040a40a945138000d94401d1a160004c159400e40220342c0c0c2c0c0300e04280c000c0032003000d00040001a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 281302464 1250 281301214 281301217
    0xf030303050c0c0703111e06040e06031207110901170d050d060e130209160203030c03040c0909050601081e070b0a05090d080909070f051603030b0d061415010207030602 74
    0x302080d07542600c1c3c00b895500e075502d07000c541d800c00c4d642d034040600020083c0c40e00484540a54070200c200740190160003002400070f0003144078501c81b010b48840019000da4003070050340d030328959007110b01e9110b01d00780c00c0801c2c0d0880c65900c1c142c0640034000001c80d016148060b040c0c83c00105074014440b86c2800003040fa41c41d0482c03001c62070225265070000c50260002024240700d0090b455581d407519502c0d004200200707d0150002414000c900e40f0100000d502104803540004855052540c036141d034905030400100300d0b440b8000c0540b609040c04c0030400040f0b900c40c102d07820001140c0140c03074111140d0554140060b5800e40c0e99009107001c106c40851900a42844030301400d18904080b40c0070b000c039144000c043c00403030300418001208035191410308082030b0801141c0c17901400c20101e41e10042c0185c441c8207141490a1403404070f08042600c40d400c0780d42d000030701601900d40c0707115614001c405031110031144d8001c0c420240004985c50303a94082c1aa00500c140d004040b5a0300c0d5488a2009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 281303714 1250 281302464 281302471
    0x14210304050d050c030d031103071409060a031406010f02070e0612060f2e03030c022b300818070b071104050135011b020d090f03030305 60
    0x46010034000041c5507600c9040303191415000340e010340040c250340300c1094184480c5030f10b0001454940850f42c031464034084296544aa6607084c080d0002c1140300301c846141c0101c0381083d5000d2400107001c055164142c00c21000d001003a1910441e64a1754401950030046107081c10006a104420410a50391110358154202a002e07000700d0308288e000311010304010044030440e9070b0080300401c2c04651035511100c500e1011610a0920b0342641d21508156002d0540c8000b03820031044400180540d5030701102e030200d0454040302c81d241003018151045808495035002d5a030644c441c4002050301000701e40b82d80e828a00d030f404042020000540c20b88482202074060b9040a000305490001c40500b001304002400a040000c2c0d2100051720f0500c032100d604881050042c0d0810004104080350000c4e500c000d44140403201c2001500102d01401c006c0c03500d02d41004a40c01d00004c0a0482081440c8401407140f035400d4402032903000348192620b2000703110703200b40c80c026103404101003031195015540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 281304964 1250 281303714 281303779
    0x3070c05033622090b0112020109080105040803010e070e09010609061b171605060403090302311d060a1409070803070303150510020609010c090f0e090703021206070914 74
    0x810b07141c1d85c0c0300c6420b101e0090b00840308038008070302260305544e0811300c0c5200500c4c1d4500217000c245070607030300d0401034081031254003803030031000d8081403500c1e0140c100d6030020b040150668409694880c0300400c01242c0303118200c0801c100500400b440c2035004840c000080c0c01c13030381006482001d4200c007207035039100c0da07842466021403d003040000f5030144045030080d1b000381e4400007024103500401804400a0303009000314100c040d20700031401403220418100d40380d8070000281a549195124555030504500849140101c100700261032280358018040f0743d00342809441540d4401e684642c0d0f608290060106a62081c0413030310000c0d1203074201c3c981994080341d600548956039004a5010180e1990200250300b011301001920b40d000d22691300d8900240c0b411192403454440312a802c09500e0184071152844400040c1c41030b0004c11600c0015540a0603c014000c44c95000303a4032900d080e5030b01c80c0015080c02002440d038610018820f0000700041207005809500312100e800080e0a1140a4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 281306214 1250 281304964 281304971
    0x506070f02150307170106020604030e03031306230703081302030c04020a0201020307120c050a03021e070302030c151b0d0605090a0e070b04081203070c05033622 71
    0x300588071040c80d000060042030050340c90342064440a40500b1a0801c0c0300d1241d454903004010240c1c1c00a81c40c0d400c10381604200006043c2030012a066200d2008040015881c0201c00181a54824000d94449521a03550b43d41e9211508000b600340c07242032000383c001450305000c2445248080c2424030001d2004045400120081c07002c5000d98014880c03440260350b0210401c25506d402407a0102c0b82c00364004104010446241e0140c014003401811404069001c0703040c440120300b0001400c1e4640a001955883d825030707160003907882c3d002e20f4a0004a0289081c48001140480003640c040d522150303007a45804111401030039150072030307050410903513111000001c050705d42040131402103405d050045950060501c20501d030174083d5010300c40d541c10410007006030400c041001e130b000d04490401d03035940c0d4840c1c0c40125407210740f010015289010004645000d180c1028405482d41e0042105061030030418041422048092101523084540c1e1502c3c804004024025201000424031000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 281307464 1250 281306214 281306243
    0x1d030307052508100b13060513020904060509010f031a01060f03180c090e0f0a05281509060e030a0f030b240901090509101511010e34050607 62
    0x740ca031424502e100c2402070717580c041541c160700300034032020480510310905001c0700d407601011480300e0000c81c150b05001507000c1164001e5a41e250003500c0142401044803640b561181c01081c49207a052004503107a0045407200740a02c0e4202034498103c420507142c01e1600391130040198040c1010401414140e100c0100303040c0040c0c000006840a000900000154554030300300c094070f4000e580e80b0502c40342c0d00420107600050700000795640312822128030080c84c062226092840920310708401440c00e25a140c40e01040f24160341300080090080400303105910800301c689490348291a406400124642e9038000030f9030003600600e00e0540d0141c07240e120100c07403c2600c02c0450000310b40c648203500008410a040d0b9001d141003011348808c41d80c0600c1ca08050a9540382c0903601d100b1071518003440481c48542c40d014804088403100444000e10650584407611070f100c00262047c034060428840d800084403490006080d980095481c3e101d05582c1000c2c10084903421901048070311045c402c456 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 281308714 1250 281307464 281307479
    0x2040801020c06100b09090c0903070b0406030b031c0e0d230c10020d09120602040302090705091509060703050c01060503011506030b0409021c021f1d0303070525 71
    0x4008a51402c4060640c07400d20038184054800258851903c08605100b84c0c1143d995590586800200e01a0002d6440404101281c2885e00d107503c0115503c902090000700c10350150442c18040e402101610342d0812080508000845804660000240c0c0f210006045081c51445e08101502407045420000300700c0c40b1400320350501060403801900144103030780060030407444210b044007190024010103c4480c9006180c41d00c0c52080c042e00c03101040318907040c440d442c0e0495015540180c0400e400349801c80c03000e0300700c0c0d0240680c54000d890300d0301001c900b50001c0054800c0303c00c0080c140d510300350140e28111580d030000f6482c11019503070b440000803d56402d104883c080d0307030340200c100d010f2840e010019044821000050740034030700703043e54900140d07501d090048903199664200c014a9010740040b81046440404001d048c040a0411143c02500064100301d243c0181d03c0032503003646111f05150702c0340503d02000f00390f50300a080d04c5488075408400002c04100305800d1500d11aa108030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 281309964 1250 281308714 281308717
    0x90f010510080625230a05030612070b0d15080f0f0f010b0102030703030513020d06020904060602030910030b0105130e15010c0c0501080c07020a0b191b080d0204080102 74
    0x40024800e01e0001041106190502c00c050303100340d082c094040d403a111009003104504000d89050304200c00b1040e40d00c0c4009107000a1030b4142401d60055482c0d1098600180055109607441482011940c08514001100203818000d903503030340941f1410002c180728a8005000c10749005c510241d035200700450a0350b020042240001c00c00d100070480289150300140c2081c81030b0414820990400070114070b242d0f000002c546c1510b5240c0360000d00c50b0350b460291184203c0f440d2000b94004490040d200902007517401070900c81c1c1e0103c50401141d9500c450580e074900c2400c05040e0000c00c1d0b105a248101e000c4d5100d5050403d043c1016450408a81c0310541c1481040d084055205240c1080c40a81096201507426a101c00c2c288084002c01588503403013540b4040c4955410072080c0c7c4002284c0190a505035603401d540a094041e04c9512410020303c80c0c2c01a142402a00b104803c0d001c181a100340c01c0302c18080c0118100c42444c18182c0c543c1d0400e54010703408070400c580c00300000110324a0910 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 281311214 1250 281309964 281309971
    0x906020c060406140103050c13020c0a05010603110316030b07052a070f081f0b1002010f0f090b0112020105270a080105010b0d2007120912030f0305090f0105 69
    0x4064405440d10f841e0140459148222070300a4400e603070018000290005040540904100c8514580001d40700100d000391044034601d02150040d000c2d40702c10414150040740940303105100d02041400c814007031541c6e9184040c0014015081250100b0224810302c000c02d802c010305243c400c0c0741055410084100c3c800d08603903002150703940e4ac088080d020090117400d01600d1400000d074015460454410780d80c41080302d02c3c0000442ea0303002c04510780a160b02c0105003c2c40a44441c10103480785901074000c01c030341c5640b42e0142d0b007009180c151001c1a80314805d60103a00c5907281c8400d90034900c20344800c9601c408100d06000c020003020280383c600c0d4213403502444514a1258440342840700780240307104c65500440b41a8107020060000c5001c04042d5920310108030000206da41203200f81e0390b104040850304054a940004080c008d101034910340d0b000c0250540c03181d03010a42e86552107502101c0d28035000c1c0000e2200c160420305203100c0e80015030016644000c64030000b202d0868a421030f1400d030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 281312464 1250 281311214 281311237
    0xa1103040906121511270a151101060305070b030411060301090903020f1203060f01051903020306100e0f04020a03090c060e27040210020a0b0f01140303070f03050d090602 75
    0xa00f0400300300925030505411100510300300348040c50303441c049401540200c820545088042d0740b4a03c0d0356210104035452070020040031801001c0ea203882040e035103035030a24000b00141c6101880031380320105008182c2120b50000040400625200503982540c2026100312401480c03110031103590b50300c039030245001e4503851b4400555221945030180c5170114143c8202c07031726000036231003d040400d4034040d00ea000b0001e5074500903111403400102e40714443c02c5c803500791108414010391285036069014612815055400701d4103100c0e054410b44184080b08661580b00b107140c50088101c0c05e003600504264081c45c1804117030400740b542e5481c405201d1f9000003001038818010b0041c03d2030301c460381754900000c001c500351250b0034000050046460041010740681840720840444034802c1054007121900944c1d07060490400d00c1c030102c0d2200d400c0c422039642603035000740c890181c600401110b40665000c0a0040d920b071031540c05aa00c0c1d001030928a28150b0f4070249980171a03d42d000500e0003501c907 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 281313714 1250 281312464 281312489
    0x70207170102040e06030a020f22090b0a05130b0a0f0204120b070305180304120203031308070303020d0f0f030b060904060303020619020f0307030b0a15021606080c0a1103040906 78
    0x504c0400003152200425081c03180e0b000005200168581384412043d40c042034920303126240311318241c0480a1415046464680c4c03034154440c080c810040c45860041d040e2810078001c41d120014201004111940c1c00b0341041c030a0b00200b401c151181c1c2c0030103010f0803035110140c10243c1d16a03481110252086065946030072400400041c1581407141aa101c00390304603254100ca507107443d1903601d0191780901c80c110200c00422005669040040c2c0310100300c0904550002e82e240e0000765107501c03503480704030054170070318a0800e442800b5980074184a03134240d803254403003e00300c40218060460042d0b20307608244100154249511540564000785000e60010405403c03d2021000c2846070304014130315480c41803185810b003400302002c4941005652401107401442000000d11031009544601da07041c15200c0c0c580c01607500031480c03402e910240b1034498440d0782d072400261668801140c0c6401c40c03240030030003d40c590b40501c0d02c80251031070b03900484e400e207600c80c048c500c100c0c1e14942100300443c03207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 281314964 1250 281313714 281313719
    0x181906090308010803030702070504200408030d110f0909070e1f020c040218060706020c0303040c060e180c0a0504031203150801140408090f0d11040b0f030d030507020717010204 78
    0x801c502c4440c010300c0d400c0015461071030003450007074942c49540180da2003203498986c0d41d5050f400c00c2d07100408220988428031355580d56112103d41d82c7e07219000301c0c60f1070f070f04241d8034200181074074041e070780c0e1000044102c51500c0c03542820400381c3c035402080001408422180703011a507d0b442c2c410401050070b20a9117480c3c880e01c500c081e00c0c00c400e03002510302c521f004100c1e56034007039401401d800e903252083d00e003203440d440305113006c030064004c00b0300c1c015840c40080308007c03e00410000040071a01c954032844100321a010500c80c0c1c0b1000c02c0c2c0f4a4103010f1451303010440320350f0a100109403000e11890981d00b0940c40b90b40d5141d4a40ea031030070580000751034001e82420700c00013207005401403e10100820555030190040c101404000344007900608000c90452082e49550047d481c0140c0001c210300c07020072540c644285855801d0005501451400382030180070708200c000c00000c0c401c024002c085103403030a90201c01400c0c004059104500841c400041e480458025036921005601d002684490 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 281316214 1250 281314964 281314967
    0x31c03050612070503070603020a050f0c1501090207021008091501080d08011712030411121516080c030a0e070b190906050d0c03180b04020915091819060903 69
    0xb481120034401c0e03004040104420394000502c00201e948909001d6266200b0240964042c080d50ba03248000080009201d120076002164607402c8245c001ea0101090342c03126480412401020002508031400340400390b030b00d40c004c2c0803041c0d201940d142110840040c030741ba441e2480c1020790100b91507510010040203010341219138540900f540c03508900300012072030b440720b90340c82d081080b40c00c07400e0001022401f40600c4120003800400c000c1c1c4001016110600596600c3e080580c41c215212404004907492054041c00b000c9030354801d44c5d44225545990151080a0f88041c1030000303410364400c0d00c0d40b0303200b1061155500900001e41c0c01600d40208081a24003902c0492121041000e4980d05025142e00102500d080903076891000400c01c1c1500425002801000389425003180340030003510030820000e00d11449036100b96030074079194071070aa828a03e4402145155801241100001d0802d00540c0a10700c01454800440d02d070001c11140c000e008142000c020303034126444000000915 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 281317464 1250 281316214 281316229
    0x5100f06180207050c010201020c030a0819050c0306090c0a020c010806061308030403050c06070308010b0c01090501061202040e0120071532090303190204050909011b090509010311031c030506 84
    0x71710280003d61411519112450300d92054048a0003848080c6001c940381c101d49403040c0c01a80321440e41001a401d020081700b00b16042103600d24410804040000e04110030101074502801c0c0c1078004081403501c20005440d4002c0042803160040e07000e1140e56403140b5860110001404d4800245a0303640c114140f5034200907900103428087c000c100003100009620090030790446511074100c940310070f1400b40c924050028918080c1140d800c0100105003414a07000d445a5644200c808028440b036400500d801da43d020444050391005250116000000400041000500c520240c03030f00c00866103515001c0f6400f50210390150f10f400101c00e14019080542a01c403259078010186c10307440c00030752042eaa071000070001400395403140300000f555450b03034041c0c8014220003804503131245410403c1c41c0c0242040941e1001e140c000c1d800202c0c0c0d1074003d10b652001d0b2072000d03145807402d81c256110400414802c442e00c43e01031066000f0b040040c005180031024007403440ea000b0034035040079810455131 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 281318714 1250 281317464 281317483
    0x20a1b05010f09180c120509061f0308161a10170c090105120106084204110609040f0e0c010302041d060d05060709031a0405100f0618020705 62
    0x703020b44040b0a21451801c4c3e120118841e92000002c242c0b20540c00d01114641400702c0030f4080c0c0c50503c2d0a20120351400700f03a1741d100301c40e94500341040070400d9080d60207014007480701404090042140500c5820300350508420107010785000d29100f0b001c030102c0e000d2840e0448421980d106201000c0c04403001240b072244004840c1801043c1c0c005230798000410707140c010300c04c20388640c01c000030b40354103074100390481e200404c000010341e1b09070a44945d6140c90482d20700150141441103050f101d9010700760b0028008604034010500c200d603500c0d943d400100300e03042c40400d68032102c248543c4966603294080d41000042d1724501162165501d41d03100d00e415804113820703050600510003130003a02c2103400e044120030704600e1500ba164840d540490803901c515280034046005290800c03030b80b1500140c00c0c000710380c4a00b03910b11440902240710b0149890586000f016900321400c0030860301159006000545002c0360300140007a40c407120710031240450341107070703500540100354002884800d1100456 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 281319964 1250 281318714 281318717
    0xc090503032a070605030f07170c0d060929010f020a150b0303030103030206190504112107060c03031104060c080d140f160e010519020a1b05010f 64
    0x505a0628000a40300e001e82d070494081d20075807010b048800c40c040703004090321408080981e805541c544070300815661080780c40c3c100d140703043c1000c16076040c880c0b0984803840d0195a0000035035150a504000a5806040203c012503142c00001c10500da246c0305080028001d40c03424141000204107800a081410414134144916000c0740c90050390041040248258013144003a0164807804000004100507109941c26100200021081580010b82c40303000d0425078802d15000c09240088406940084400900d00103406900400a09103512041c243e03487c0b07007079a002140c8080d00c101d403402e080c6070f0110001890340703070a0800b490342600c14090021a40300d07013945403a0a02e00b014122000c0b1000040100b00300003070381c041400080c1d101d82c15191098140700403034203007440e41d500d244900740c41900440c0601e0001181c021b0240c140203183d65410b031241420100f844d42018002d154503d140c00035409800706120000c0c030440e0018071442078001188010781c1c100704c00141400c044558980 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 281321214 1250 281319964 281319977
    0x6041d0a0c090b0a050f0f1b0309030c090403020114040b0a06080304050a030f02060c161805060d260c0703050105010609030503090d0201051209010504030311071505041b0303030507030c 82
    0x75542c0d4032507608020741e8007036030310030380c0d00c030070003007040764903200d0798204445070364020522224038151217000b0541858907200f10405003040c01e4146880e4894804115070650002c409060700f42025400142d001303000303000001d40101c43c40350560760710608440c00c48120016070704012101080784900400340050f2ba000350f08050a00b00468074248081c0406085283d002800e04110342c1c4681c100e81c1204012002d6901c1c0e106d00c9482c404400e04c05001f0340ea189a50100d0ba100c0c03218ad40d108140c0729041c0108000d00440141d280c104000d280c0121078524540b014841c001c05001e041c00501d403420910b4001d02000307145040c11402c42d04181c10407820462202e5040021034000020b40f0300f030036001c07524521501c11314030058605106d040c00c4900007104400030400e00c2101036019520450082c0c50a01285501201c00410742c801c1180040499900c0604403011080c2944550340c00f0f441001d8003c900e246000c442c140c0100383d50310480001e5125000c20000a03850300071102040f04905200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 281322464 1250 281321214 281321231
    0x30c07090c0c0b060d230304030c05090402010507020f0609030102072a0305070b0d02120c07030207090501051c15051f080c150a02010b0a060c2603040b04030e06041d0a 74
    0x12581c4500a00405d00c150319600f03824003030214643c0040502c8600482d0400e0450800d0700031a1690880d22059030551407a6800145a04040c901240b280750705275152894040030342e08000128049840346a0042d409010f03201036501c00744004c101d041e01038510b000ca0703040020b8554110702c010041010000040c4d0320300300001100040c0590545031004400c41e20b0700100c0e034901d40280500c404d601a004c070306030248561781c0c0c0c07020000c200d01e80c041d9003540c0480c2d44880820040e0344c800c2c130035150040140d02000da800c4a0031212143d545100d106010f507080b064911903420364030151a001e262000500e004500d0f10220b000d0f5000034a110005801c00c0c45103140018102c1480503280344100c90002420b21100b40700f90b22881018000805507182c982c1c8510000f01480c0500b502100e080314400f000344c00c401500811909070b461405801841c5d03640c1c542c0c414001c480041d004070706003d144000c10140b59100da0141c0050700504d410400c4040c507044030891502c401030701800080b40b609000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 281323714 1250 281322464 281322473
    0x7022b080609090c0406060905030d0f0504060f11061503070602070303050f09122a0103051005010513030b0a140f060d1112010608010e0705030d1b020111030c07090c0c 74
    0x90760301000c100e03042503959854a01c1d10341003101a001c1d0a510a1800f140801e829800039105801d4800581c121074070700d90000f10071303211340d07036a900c4807030110300288001c03c44d8500c00e00d180d6068808a15211002c0c000e13400c1c896251040648a429030049079190404031400c0801850004181c80e200419203130345180c40140c0248200518032a44440028145405813142c20030140d140e00401c08031980d0a626602014100b680181c4a407480c0410031500c040b01d40c401c2c01032900584c0103500c08503406280500540b2107600600440103d011060b000102181c001c860042c4110519003010424101c2c1107011400240c2c01061007244a0004042c810192210b00081c120079034440d0752000c159086a001401231208282c4911541d0301780007002c40c004c01c042d04003040040001c0210307042551a84105074846114110110003e00d200d210924204000340381208400c0c010b04003010440c1c02d284c04a821a03000d030000c200c0342d0f40301d1002009000030700d106402443c0a03d1500d995119101c0d0b89 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 281324964 1250 281323714 281323727
    0x10e0d14031e040b06011d010819111605060a0908090910050d0602041707080604060507140a080708060402090a0506180607230303010e060603090f0607022b 69
    0x101901940c04400a0707807200600000000310548150440c0441c41c0601d040c5051000448a107030007c0c0d8400f025000c4982c0324685100e6425051b1103814541d6264500704001d0030040713401c40c2142da25614100000c1c17400341d0060542c4a00460060561400c07802c140780b82800191a10038a40c1c43e208400e00810150ba05444000d0070803030705400d0a0b1505030303a407441200c05400c05070303024410078403107401c0080c0c950040085552285981c4001800308030b10a44070740c5540301d1a01c8507002000000d0004105038031866204d441d600305107564584901c160001d036040010300c0008a2001000d1081e66a00407045a51180040f54150b2811a40c02d0201e40c410300316107d41d600034000411440c2d103201109142c0340907148090002e548030011800c1c100c4515090025040303088885024002000c0c42c08001c40341a80d10460040300a07850310f005208440c1d000401d02d0300c481c01461022a502401401000c1c0641a581c0c0144a90990300c0000344142030048070948ac41401002540c440c0c5070000c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 281326214 1250 281324964 281324987
    0x1c150507020d0801120c03050d0306090609060515030a06080d050705010b0405041707080706240b0c0703240c05030a0b011d010c0c030f080322111207080105010807030302010e0d 78
    0x200c0b000580c40c046d0b000210a03040201280100b410320380d00e2a5240d03010710110790522105200f142e650b964400101c40c09401080d412000c00890348221080c208011358220b1140500080c00d550703180e2009003040e03054926000010400a070078014840240108110f00000b142e041200b0b007410364901d9408002e01450058260740407409200f80400c2000b9502d4141d00900e040c0140e814100440c2c03024500a002803501ea00d044c1008280c6407918010340b2102210b05c0700400711141107031551039168401540108207440080701c5040e00560300d0182808230040c0351142a00d0f0700b011340042e8241e64031844254100100790502c80c0c400000c41e2031601c50000d00b800c0510b20f6600505140411040641010f807214064508481c10041101c005501c40c0c04100d554483e10081100400d080c0c0c003440c0c3e00901440b4030715030241c00c2c80c07401e01c8414130362650400448081c2903076901201d0a48109a1010000390401d240400070700d0f4083c0500b1440b207142130041c0c03600b461405400707021101e030030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 281327464 1250 281326214 281326229
    0x506010f0f1e11010504080409050f07051e040302060a0e150c060c1308030a0504030c060e060a030c030e1905160f0b070201030b130507170105060f091c150507020d0801 74
    0x11500d4018060406040910003c03030080c0941d06c1d150030602c0f080e0b8043d03c00c1490345c034644400101c41c0c45c801d0b020a4000d21081e0740d0146455004001e44001c85c0c40d0306695180423104000010050703540034020556100300d138407600410a42d5000300138068400f41403041117064108025a407814020841030b0f1f2001925000c1900c6004c401e13451405d0a040c0d8000250501c80028034698458100002c0c10440c1d2003550485d14250b181c0e802141e0b0201006d0042d60803440074000201e50f03a0280e0410b0325580800d15002690141000c4000d10382204020845450711805031124207000c0d0501201d85041c8554400d1119685090156400d00000344900d8491100100b080c000310780c4240c0042c40165001090b9195000301d10211400030310094035003501144480003402e0304070500300102c0e41219001048107007481d101c0f4000300441d034018058150321180b11416801c4642d07c44c4c0c00c454180780141d070000c1034245070765030b07450032640003a00da14150f6100354005820150300c07a94003815181030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 281328714 1250 281327464 281327507
    0xb041e02070f081b070501141b01090b0a0603020a0e0c1b03070c03060c0f09052202090901030501060e070206042103020c0d02030d0f14060d020a030609060506010f0f 73
    0xa090022000e1402d400003401a540040e812590858640b80c0700002c84010041d1580d580e82d0380015200e903e060034041c12548014822051901001c1450070382c41ea050308000324044030150340341d224481080310701c00d8020303594641c140154200a980030002d81000114920302c1c1c20501c0040c07119000705130351103100042d4000300309907000052095440042d4440310b0300104913181d141060240c0000401c4100186100f142203d105124842aa0031184040d007400d5000c0303504640080460440c5601441a40c2c080007641c1040d16044065402035005000000300141000c7d4988920140944000d04642c03058003808013041300c24402d07031049100310a842c0c0c12201180b1098000e40100120880613009220404042540200061181c5017041a042000d141000300c0034088403051003800c01c2d0185071300c2c005038079424040002c1944c83d0000748214007140c1e0300d03500c1500365007807440101c03442038482d8244207140d60040b2006003d00e18a041800c030407151810028990b8100d000f114030380c41d52 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 281329964 1250 281328714 281328727
    0x11122032a0308070b06041109010c060c0504081609060b0c030327061018020c03160318030609330b01031d070e0705040501020613030504150806040b041e02 69
    0x164005040082d640402002d40f80c41190801000e01c12081700c0142c081c0741021703658100390150001b11680040c05840300081c1030440d84508006059800800082c00420003000c40c13411030421040c0484110366071a4005076040000090558107141c1c070401803208284844100d54502206030303032340b0286581d400d0f07041d40c05104070784c82d040b100100b0000340341c010842030000030380c01e9030241000c0d17540e0400341d5840d00150032503840c201d20820340140200c0e0800c0c00000800035001ca8000c00c0f250191421480040700f0301c0d408207440c10254001c684440ea24035254007088030380e403004010b85814807100000882410390400c0203000151101d600656a140c2104141e03019078004c06040c02044a400000c201c0484420340e0b42c803035805900100701107840001c3e080c0d4490b40480c1e0594806030b002d0801c9440345032981caa108420001101030144c18400840c1e901c0300000c91210034010350380c1c0d1003607905000e401e110445040011880c0600d0605001e0104600451454110380c2c13589200107a440f031 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 281331214 1250 281329964 281330033
    0xf2d1b050a030605062416020307051818070609120f0b010f06181a0c12191d060405151e0c0607231b01112203 49
    0x56940110394000003100000c02848110b902c032078401d032019202c084008240d121030030301207828a0302e580d41d441410414151041c032500142014544058100d0f10300c0d0b51a8130000300d0300b0503240c1042201d490700b9400c00254410040c00c040c29519941d01401d0101d060903402802d82405010340341c0911103050b07800d0300b00b02207140140d0b0a0383d00509805030355616000400c2048046200b5200020302038801c1848042403821030030111810060300784210758524809144942161315001410b0045c1c451a4a441107200000d18400b40e1584014035034030000d2a0140c514503448041d00d00900348221225060f40311101100c081c3c5104541c44a0301d44401030752500940700d0420300b0040000310201c41150076455070064540c014500095980b555158002150300700110608552100410508103070111080001041c000703041011400f01c40c4442035846095401d400783e400c1058500203a12003107012100f00f454034038560070091003002c40ca942c84200400c8010420880d0a018a0009860f00c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 281332464 1250 281331214 281331263
    0x1507050d0518101e0b0303092e0207050a060201051920040e0403080f0c03010603090206041d01030b090f0c1314191404031b0302010b06070f2d 63
    0x3081220304507940c001d5030012210241006681c8400811412000d444084400b40203201c5c0c507000240055003010009001c00580c00300320b42465003207500d4041740c1d800d1455602c0c0014045030f44c54004080c0d0518203018013441060319840b40d02103901d8101070011403403108145442d084948000030440c58a0100e01d10ba4049102c0b1043c0320041000400003280c501c444140c500c9280031b52583c4080f40e507070741d1541000010441e40c0078078048003080144400350090780201a0345002615040c205500c900161700000c10b12500c880101c264040100200062075014662000524000e40080550080c25581d036104440910f4400e04555109075411419035001d079462042c001c00c0420b86003814120880042c584c444000c5210703007000da4100d18028564000e80c02a0b43c50f40e0340b50070700c900311015640010b04c0d07400200c0441d501c03407410303212543ea075a0241c10500c2c000d40c135041e040301540c6421a19400c4603140d0074100c40610141d41349040d5031050300034000c0d82284082030704a400d1244148079 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 281333714 1250 281332464 281332501
    0x303070e031905100608070f03080703260a0b0616080f070501060b04080f1513050a0b0915090106080607050307030b041b030507020703080f0a03020c0d03020703021507050d05 77
    0x2001c1600d008a051180008641c004d040040100700009521200ca0546503c094040d050030103001241c00c2000400000040101900a02e44403865080907050450b00a00c11124104585170090a02a00c2000b1744652044800110391084c80d1024114801c02c083c41d040358068041100850030444144c26841101e07600f80d40300000708603203511002a40500d800a0003100150710941c01c000100600024440104401701c500b248401c0e81c40c20500c450f0001d001c40101c0d000d005e08420140054036402c80240600c5040340504031654100d10b09660900300103103208126810004200f225560124607140c00ca00c25107411030f03590b580c0c0e50040e000340000c800c3c2e8903003161a05031400d654000320840b07480c5200040c0e50600550b289d5041c220380d1044a0300000d04002420407080100300c2d900c000800440103a07007409400d0283e01b880380c0d81440d03404000031001c2600052190200759045c0314040d581119040741c024a8103041c107009010740210010b03e00c0003070341d5070086000d0704410000242c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 281334964 1250 281333714 281333743
    0xc040b04090206031303080108060c030109020304020f03120406030b03070b19020f0f100f150504020c190b09010518030304151806150504062702040302060417060105010f020303070e03 81
    0xc0c2c1e1304281c1c00d4100c117001548070590004817840004985400e0200e411809141c18900c40303402c59003488075032002940040c200b280d100c0f5440c226025507490500150910700c803001c4002e0317151450701c400602620b0801d041c40c1e00c242c024400502000d02d010040d1940395170503070684101180c141c28168a40780c03880c00c580241d807148080f80d010b0007000044070b03042514511010f00081c07504c01040e00c1640d0b51441c41c0c0c00c807010400b006020908095000c1c02c140c41c0080116550b0044400340d1030203031b0801900c103440c089050010080c1041c2c0902840350414030141800d100e02486801e12034480c00041c00040c81020211a2641080b87c0340d0000c03000f00c0000226810001c142d890b00400600810b450100300e500c44080008152030144550001c41341035950850050400010601a59503010401c00303039a5800d10000c00542c80d002e002c0c001400c450300c1b00e10702412003000c5417807401c10140e1000303041118000c180112a5404010344c0d421107034078100a4401d514000000f400e00b2240c010100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 281336214 1250 281334964 281334967
    0x10516061d0703030f030c020a02191e050a0b030105030d03110403060e010f050105030708150406060b041502122502010c120c0b0c03130305031504090c05210c040b04090206 76
    0x20207590000c20224101d0b8441c1c2c0300d504201507800d00a50940381c0328403040001d43c03c000a44409420a82040003519a14541c030400701c544650600030240c1c4030988000b03881d40380c50000d214508000c20010041d00d1107410f107901b151714100000340c1d00c401404010b4105621588045040306840094602450340040f06120950440081c180240a03d0b007841c00c5640c1400000911400c001c070702c030000e03141c81002604c204120421030080090300500300f2a0103903039406001031030f1003507000604041e0440065040c3c0002c01d00100900d0050042246000038004000ca01440340c2400200406582c5440e41040c0380301c4d441c0016506403c070048040c1c01c0c01e0103102c2900c0d425902c90844240b4038424000901603031181e401918090100f194042c454841004401021901403c0590f03480020401c0981c2c46029080100d815549005d00440d02c080740e8200034842450290400f2880041c02141c5035185848900d80340da840800000090059540312420742d00b0303450742d41000280e079030013501d0385 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 281337464 1250 281336214 281336261
    0x10f03020409023004020a05040c090807060801050307090e0a020d0f0501090809030708030f120402190602031e2109010207061a0102060c0a050a1412040c0504180201051606 76
    0x360069001030000c9441520500c034155102103c5001e490003170750090030590400f0b0510301803000410040010000b80565a44001740051080042c8070203000740d607583d594594900418140740c403220750070440b031403410140c04001d4017000150b60780e50560101c80648000703a40d1f040c5402280310b4044050075650030411104188447c0100909809409504440f515079407441c01e952a4001c0c0d44000b51010410842c5000040c0c4601e40d664009000070203075010814001c440e81100709003684064050380011444046054182000444000b00078118910b0610002e149d41d80280c040c00500005d47c1400d8041050a0800d50581f012164010707010412301c1d140e030301c00e5150000c250010f20f00501c00c0a00003240ca0900005070385606960742c840074182407414009980316031a6900b4003142610500416591410034001c2c1d44c0900e010b4030403c200203050000740b1056428600c1e0420240c0140441e090050b6800800c0f10100c004d100042051b0214500c1d040c1c0107482e00024031041c005d0300d40074030f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 281338714 1250 281337464 281337487
    0x6040e0102030f070f210e01110a0804060506090f060103110409060b0903010608163b09010c0509010f03111908190b09070f110712030e0d11010f0302040902 69
    0x10303006010644a080010b0a0150212000107000041b4170070000038194041a8403516080401e030401150700214040000c00344100080d081070325680002228a014001846010301c9502d40050050350350014520700021140c9030488042c01d41c50405645223040e00c0e418a0100984000d8249114140301081c4d45001202d0507030408110a0300c03e52070030b400019420000680301000041441203405e420303207411401d1010f503402c4d80d020030f204100050807209940b440c03418645481d0504110400314108130304d9990845900031440818420b0411482942d44c1c6c0142c4041000b1a0a01d408101421a40403492940c001d0b100031043c04e200c10780c6e1a1034040d401c890364520400514001005001051118109030754544030941d0f00038030084003040c04144075090700c0c501c1c0d484034100610081e001006042c41c1a00319800400e840414001c0f610401d684003440311506801252a5100800c8a03200d40c007511824024550510102c01002800305009405440c02019140800c549450141d0f55 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 281339964 1250 281338714 281338741
    0xa0c0b1006030f0e0a080d0e01020d0e0d020c060d0c020c060f0304030206070c1106030c220f0608060a14030a140c010f110d050319060312020607050a0c0b06040e010203 74
    0x2401e00401c1c24a0704008034038015204100c40c40342e0a40080001080c0d60311801c2d043d900c90880342100c942c55074000e90007030310b00b4001095a001000030000707420f203140000604106c510000030302150828025000c1954034a425102d0f200c3c04002c0029120100c400140d00e4030242003c401c1c3c0141000c101c1386102e256282c007451140d4005d40949520355a4070204403010004404010b280c9072403040e11a803203042c180302456100c035420441d40d1800840d5144900ca0381080300c80c045171180740389024001d2403143c107a070701e0061401c0c0c2800d404c1418240700140030490341d40201246210001c0300560340c0d580c20081110325a80200b8954080c1452449080d1075180058840d40800c08d0300100a01d05481140c905110058200c0074001c0c0003104402100c90758809040340b14081e05c0c1c130598810700580c6101d010003d44c410b51201d400310714080030103810070703070001c00e80d40c24000d0178054286c1842d0403802d60542142c1c0000015510742d141d0001600400d40501c0258140d0300c04410410038812000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 281341214 1250 281339964 281339969
    0x60504050a02100c031407111e1c020603150105041703190e010c111f03020c07050d0b0109091505040f0c05060a0f0c0f0b0705071401051303050a0c0b10 67
    0xd50160144400303000a4940741000340000b400281401b200c10300000a10b8003811149104210800100d294080002c05c030745500c040303844100c03a000d0542c08a6242941038180103142c40d1451110000c038580009469001c0148001040100c0200041440c0c1c403503002c840c060440c0c82c50740715526000c000c090395641c01c4007000c0608442c40c01c0c45040c0583c0102c02e00100d25405a4909904507541d82d55440540ca411101640041682c100d0307401009038a0501074188026950050f00c0b41c0060038031518281c12a48183c0c05490040240700105000548850544592450100b0351300326070f10700001410740e08210407214510b000d05110800081d1700c604821b907401800102d120640707031000c01803944565248140403d0340e0b903021800c16809122036100e5540610b00303201d010100c40d01c880c20b02200c21588200040c0300043c00c4810000c45441c140c403c1c4d07241c04001c000300d00e416034244000341c2500c84040c1c1445004900c01007003a105800205029a000c034401c1d0045c148003412407034900960 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 281342464 1250 281341214 281341219
    0xf01090f0204210201140c0f06060603040512071104060e01090e0606130b0a050604090b0a090e100b1306061d04020705120f0f0309030405010909020702010e060904020403060504050a02 81
    0x1142000c40000d000781c030195156000c03001c1504002a881c841445203400c3c00701d0500c2801209440c11600c400007a000c149840e00140c1040c0682c200418101030004042d00d1082d8024814440400d10000d83c40c405112110030240d5030310842d0034198001c1c8045020654010f040c01c601140120710300301030f00c0c1260040d54040c001803005105e0251210822190242c00444145c00c0b0a54829560441c5054510151140801c641c58501040b0036038401c1d04060441d5456502c00d070140e041c824800c40085c000c0324001c104c03c4640300003c541340c032000003802d6400d503222044003584d035960691640588132801010040d465540c2e0340544a03074501d0083c001808210301080440b0b0a1a00031591100e50000c05018002d107070401104058002031418144504280076595403e10303c980114014034040d4011500c4500d010001082c0c0b0103540c0148e014030340140275000c0182d8002d2040034065400300c0302c45480d058000c001c1002030041c0d0380042c00b850b0030403051200340140400c800d103010340203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 281343714 1250 281342464 281342471
    0x70e10031118060f010c08030412081303020a0305300a2d0e0319030504050d09080c01140903190b06030d05040905091515040608060603070909020310050f0109 70
    0x58404102d042c02c0e620300c116007050300c0c420008041d4034180306540c07282c5405040c004201105500c64000d42e8001711002c442da01c0704081406c42c407540000c0d1407503024282070740d02c8030f40e1103555800940b1000418001801c0c084041054401641e02d10b60b0000035050304c50718500c12030aa0030200d1120002540d040d03010518080c04898980018050707440c0040c0d1f10a1810310f510b03090300002c4002d1001c5058a034950009000001c2030056680c03610303001c000c0c00c0e98041030342c6c04c0c40d0901e2414000107540c004240b181c828010880e000c1c2c04617481d20f0044090074142407003100582140301510860720400e506001e0440035040a001054494074141c1c090b850750740c8540d541b0f00070f1603030340c0c107050301d0307000100b02c0a000800c12040140c000d175a000c0b88000580e88008610000c1090310300c4141d0391038820490450420100382098810b900085c1021002405103041c0000803c0e1039009030300400c40c583d91100340c2241951410400186488001c8804105a203482605034080210a0041402d003505 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 281344964 1250 281343714 281343743
    0x20418060c0f0e060a110a060513050c0906010c03080702150106212d020405040207120201140f0105010c020409050708011e05060a050423071808060118020309070e1003 74
    0x414410030f0b04041000c0d02152a0a000d92010344203e20b080020120301e1150650a07000524a1b0084d2400382c186003800c11481d00c124900369082c101e0101b280c0c0c0c01082c1401c10050143c1e84001e0b80f1000c80d030941843c0e01c20b601c0e0390100328102140d801590411503099000060000ea01082e10175004c000c03941207030080c03006100c50034195648140036099049801d00923a04105801140c210092400c03140103281540e80da001c603007070760031a520699150b10142016248681c0a00502000c040080003003092444c00c0314910000400600440741000280992141103445642c0b1001c0c8484d040f1003211130166a82150764041e15440c0301800c1d0b40200b4100020318002d582c0540c600070140100011482420481808020311403039031031912210321b02d84042c204030100c0c0c00c01c600403020707070b0380c1c0c02c0c0854054100c2d99490380c2070b680038042c0342e4040c1004000b06404016888041c008185000d030341d0b51150a5218581001131304000b140b20b030864103020094208020720001c4921074a401031a10300d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 281346214 1250 281344964 281344967
    0x91208150d05061819060507080601110a03080705090a03140c12060a0b01051902010501060908030414040b0a1a072105032e1811030108030a0c020418060c0f 69
    0x10a0981c0081c22944101d002c140801403468101600d60039420403a810440390b0300800c82174200002c000c0d0340c001e07502c400b4862440d50090302150700c440b007800c0c00d01400c030103441480c1c0d0f106458a00901040400310100e40c545208134121014001c0080141840586908020f103007503409154a020364031a40b165041c5605140e410b08034040b054030081c004c03543e10010004042c00740725080c141000320807c0562881940481c03421000d820319400019198107061003d480c4d40001c1c0c0001c2000da0081c8400c0100081c03011001180980544000c241e8030004000310304410810b81081040d409950344007912a013450b805040440e000d11a2241e98500916007194010b1010f458140003602c2000000d609101651442800c030600d140421540200c0c50490308020056812290407100c90748072110030242c8902540044081c80101d01d4a113502d400403040e41d03442000700da141440000740b03454056681d40d6028a080103d181c900c0c4131582003074900580241007808040c80490200d0ba090740e40b29 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 281347464 1250 281346214 281346229
    0xa060902011209061a103911040e0f100f02090306041a060a050d031b080d0e161202090a0204030f030507060c031a0105070c120c0f0b2104050109120815 67
    0x4095948861040e1550b402c051f1203000d00c4120094030b00300e00d50584d0f141440c051801004c100f40134081c01019418040c0421095400c81005001c050340138004410203400041120342941050020000780c2c0583d032a0072034042c5c0180200c1c2c60b81070007490100401e2215601c0d40c281041802401c00e03180365548070400910108078081c46800040022611000a02469081d210107441d9001c1000d4200291b4500d4810b0f400340c0c5e04000f0107030b202c502e01c00401c0c40410400887c104403071025034010341070602c05007481c060030360064803951500000c81d09112190781241d0146820192a00c2101498280078041d5441004100ca03000c0c54400f10fa0b1080d4030070b00c25201c044c0b44001900e10643c51101c01118070707402c41d000c19100d0b05036410000488412071600d141c080e41c030403201c0c0c0c42101d2070300c0d50700003c60603e42d11480101d4001c1000ca00d0784207029280c241050050710307890007180c480d414401c0c0107080804009040310400c603026002c05420141a07071103007a82c0754024800c14030f0903080c0b2110 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 281348714 1250 281347464 281347489
    0xa06020903121c05041509050f0d1d041509060305010614040b010f110f07140411030106050a030f020906030708060a0b0f07020603070c020604061e110a060902011209061a 75
    0x400f107980c11140b032561019000b05400ca40201d4445011050020f60941141c1d030916044031550702116062440d44024000001240c625080174a03156502003150058440d414065a00c0343d6940c15030200100d80c80042640900464401008416124078040b4001c003c02c0c090f0640c1030f20020395100e110718050107007096149040e5240349a0440112080e1240c1c070000241a0417405020300428420300300b04480c20092072101c0140101d04e881c035052204542a40b225001409410030040c81415008001c8825841140c6000640e07202c074080000000d00810016a511010010030303c01d10542c4002954000d1000311942d11120340d488855a1452003501003034a240007040c00301d1009481e04501456200d409410000d0200d4480d0703000803030a61280e00018082005848003210051a1b480a0200e20b5110304061658442044171907507901f00c0301c140202900e85900a002c01c59100d0b0b035288040c00c3c1801740c2072083d61220b01d00381e4040c0070f20010092995010b00c411030000d18021442e001c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 281349964 1250 281348714 281348737
    0x40801060918030c02040e1504020f0402030919020310060b0304051c0f140c030a02030c070e04020f1e1e011d0108040f060902060711010806180c1b0a0602090312 71
    0x50b1034406607829652041c052000ba40d001d641e5400490900000344a0a122003806000515982c42c0c54410401840c035031083c01c2c4d000d1881442040401a80040e00007140100f00c2c44040030014a840000e181000381c00941080f1410302d2400601d10b95004080e50040b4462030554000c580d810350001c8405108905010000b00d441c1d0260621f10b00500309901c0b014070b0f00f01450320b40f00741d981c0780e6032445e40540e40541c0180c2c4005070035940c0003024801030019100e0190f0b001098101600000d03620302055016030300c10134103250102e1024507a00340340350020501801030761f400c94100c00304581c0c80c0c90b100d101d0342c04180c0c05050041c28220b0301400b45800c12050b10340340c3c0705480c0c2e902e401d212095070080885080f680d45580320056a940c5002c4d010305c0384541d1140701a11001300004040704c034050441c80c02034200000c2c8419045c43c04030755991141c14896a1500d52083c6003406ea0407a0010141c1c82c000d0180509210502442e0b0b002800c10203401e40031034070a40c8640741d5a004500c41c038504801c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 281351214 1250 281349964 281350001
    0x1406010809031e0f1912020a1707020a02030a030824060703030b0102071220040b01020c041a19030b0106050f09011b1406090d03020f030a0924020408010609 69
    0xc1514102d03842065004001100700d400c04d4002d06540003d540a000d45960200b0303c0420b48500640c090200491040090703425810503520000140131058001e4088145506400c0040c03a6288200903503070701c00fa002411107500803c1c1d4100507105040580c0e81ca08003181120054003c000c9080d8000313032410b0082c01c00c614150f402c0d18220010025156907504501444a002524815207241e8242580c01801e034030868102c03d004d00c14070540034442d064001d41c1070000c0940d5913a001b189040d410036095501158000c101c80c410311131103061102003640b00e0020102e080b128000d1103000002c1d01d00c03c1001d8803140c0d0326200c054815010f11260b680481c5410042e841e100d5103c0c141410221040f810b00d50030b0b0b40841e82e11a41d0700d1071208440b2800c0ea00510800024040070000f203208410181011171810000b600001d4851000500c003e40c203540710b03420b14013000240d13444042025040d00d110042d132030300e03081e42c84080d40c044d2089504940c01c020b00461904214070400300c040e0400301008 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 281352464 1250 281351214 281351227
    0x11010207140d05161401020c090f0a050921030a0e0a0203030d0c1e110601090b0d1b051206100501141206010e0a0f0f0b16082506140601080903 63
    0x4030041c0b020421100c60080703240c1c0300001c00c40f2564a0001d0b0100c560884e400f440f9541c002880d10307224803c03140c0b03d00f07546030511a01c0001c00c1c0017240c103e40b4030400821190703900c01d0528503242c0303515840880041a800030402ea070b94420007560003107464030000d008440340242e00341e98488010801941c150010406400b6002259114000c0d00301d80d4140311101605000740c10308680c003044030820102d10205140d101d10401401014050142485d040094084400c0401c6403916848401071011140c1d0720041c5d103030b00140c4c50040081c00b00074030542c4a03410008616844440c00d49510316805e015150105d1a5030003400c40403000c00c8107589490410031001c69500000401a1800c0d051003c100410166600c031030b0001d0010b401d1120b000e040c15490030301a0b03600403000d07a0010011903010f202aa02c01e510b05007d0389031850308035054036268444056005040d003150030044450380745000c105000c02031940c11010300f000c0610440c001300e40d2003a0044d900044100c407a0601d40e001007140 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 281353714 1250 281352464 281352469
    0x130303180b1b0a020d1a1b03132f090106020d08190e062703090a03060207031205100e160e12100504051b06040608010e07030e0102070605041101020714 67
    0x3541080030403104a500c03190f42500818810b25071000c0640c0c81961074999403084002c1c01422a400010740d411007580c543c5485040075107400080c100c0c2030380d41780c3c0e040b2a20078440020407003c200c401c00000890a44820603c0000c05546158418090038448c0c00003d105400450200004003641d2100700703040c0c1e258400100004404015040010b0b920340c1c0103a56a2400c108543c07007031017101c0c0401041d01414070018031b030b410181100c000c0ca620030000f10600d41ca0b507020003012603900030b40c05611068140340540740d856020800d5580707103181804107c0c1d84001040081c0488101c50070340340c8640c80302c2144501c600903069560000c554021340f510b04c9030a20300650a8960819026140614540745d2400c090f1001076400741c17803d500c8105d43c0442c000e6110401002c4100031120705241c10325000c405490f03800140316030940030b000c1100240c111030080d044204c45004a030000c5580361010316202000700420744065540c8001c0008030202540001741000640310440382d10142031a0700801c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 281354964 1250 281353714 281353747
    0x6010c020406031a04030801120302030723030325030204050f090702100c02070302030105010f05090a020903070902040e0a061e1a0706020406080f090d08070c17130303180b 76
    0x20100d0300700b030b61a00e001001c02e504040d00e0b84003605401e2008291304007404c00404088060704210205050346488400107a0004100c405041e400800040d015402071040d680c1402c0c0d0b0640082c06000000800482c00d070340080e404c50121081c0208002d54500d01d1086049020303c1c0906a00310300407000310b40e19440d00e10950396015400d84101c4080200c0c0c0e030450b0095413001e2400300b02680c4064000d000314502030007030790301501c20504921242072501000840b5400042c00c501c61583d400a944d9850392002d001c1c600141903105025565240d1710bc01c00f81c0c90300c0c0d04541680c01107107495408580102d0700301c040740a10500909d40d143c4103081a10340901c01d10050034550a0583c00c110303120015804c0c0c005000104082c0c0c0320306280e482c2001c0007401540000b403a81c02da07504051403c0c43c0f0076401000d0030b03400c1900c501d004060b80005240140700c01035242a0303a081a803002c2a072012443e46096074005a0348260384560001000510300c03015081c080c0034003201c1010a00800700071040485 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 281356214 1250 281354964 281354987
    0xa0501140f011202040b03071d010902030717071704030801060201050f0411040b06090406090c1e051912050c040f050a12020d02150406050403060b010e010e150c01151d0705030601 79
    0x8100080100d42d0700d000a00c0c100b00c0c0e500442740b400840029406c00a0100281e9005141e6550b06600d180751047c00200400c400b007898450744058540801c04030f0b8881e25000085508030710250009081604001d000401c00b485a03800541c20705001465010503024494081c55109d070005046540220401012f480e014042c617421650500c0344c00c0c02035445006400082503812070000d2007502c0840c0050900860a0142c0c18044410160a0850341c0c800201e400c054000340c80103904d065880c608480404488000f5a41d4034240000d214124184c20001c00c101d800300b440d4050b000d50f40d40c00b40202d04c21503205980303e81c0c5a450010003d8203001503000304131440100b100701c007000003a0108003582c1240c0c02a1002800101d0280b0070804140b150581951090803c00301171880f01c00000c3c200310307008201c43d00401d03848045c20030030907010068403554000800248012200c0c02da180804106603c034000b101d050404038240c000e8403032041540645901c3d03950501e036540b10380c01500c200b048074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 281357464 1250 281356214 281356219
    0x6070507210c0623040c030201020d051c0f110a03060e090f07090c0e0d0b01060f030e030306040c11070303081504060308161505090313050613052b050a0501140f011202 74
    0x55200c2d80413864014418441c0303100d1928900f03401d0650000a180000141d805810300500b000701c1c0b13510390350b01d07182110394100340d03003001c6405404042410003900005034490b542d001e000c1062080c094054010006072444141e448425075207000010381e840041041c00d0000790420030b0184024151078001e402d1104203800d040d500d04107240007080d0203002000c13065039441400c60060101c20303401510041c601040d441c0038010340303501289443e00c0303100c0079003100d205595800c41d01e0364045c081c3c10350900940d540800e484403241e6038280940300c7c1c0d50448802e2440004a81e0a80c0c152501e8456603054941008605080240b40c3d82ca14402c4031003640180c0b0103480d0a2040c5a00d9816400303507038803410002026540f40c140b40041e90341c207080c2d180c100600c00c00040c0003071561100340124103811120116601c0450004181500c40ca03001840103a54110a13110884400c0c0000010360000c15032081000300300d607001e81c883d03104095000380c443c0c80011b98003000420242c1c007203d29a01030075000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 281358714 1250 281357464 281357501
    0xd0f050705030a0302070611070f05060306040b060316090504050408070215070b0c040501020f070605030c0f0d0e030a110a0314070203101b030c02340806070507210c06 74
    0xd0340c0002c1d01d0a0101c000440042c0e00010060100a82c0420245000300384540100820303030602c1c0c1013150600300c6014150203404080b0014051740d9480e04030310054036000d031107103a42e814031082e410005d6811561000c04a500c1c0c400004040c04c0c01e03c40d0a1044c3c0d00819128140800f40e030802a021401c0b048800710700105001d0540400e4100101c83d01038881c96040c1a40e440c58030002a040c92484001c0f00c0e01d60308291410070203590800112503210b98000d0001d6038611603040c0b40f54590068014036840345103030024624036810008020301c82c15420b52204020780c9401034080d0740e00e03a040d060007070008400700911402d540d0100c020307114662001b020780d0825000300710494204c035101c1250240c80450074801c01d401c260144140d1440d900d103403016282800824100886010f00884015003810780890414810b080e4040040050b15851040d5a07890404c0c0c0402010398210550580b15000790015810503150f001d94982100c402035241d0201005554880d8401800e2110014404081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 281359964 1250 281358714 281358719
    0x31e090a050f03030109060e0f0406020a02011e1410140105090d14060106120e03040b0315090108060103061107030f0e01020f0109051c1403180a080d24050d0f0507 72
    0x1400a01c008901e00b0707000303603181d45c901505202512900d1b88181035100c0302e0001e12504401e002d05095006800c030b00003503a50000c03000c0490040010204801c60100040e0500e204810203030080424491140b06a00c144e0b210340c400c0084000d6503106400a01408115914082d40140f02070440584003c00c1502900d007a5101c050b0880306503040030325503801150051005507004503880c480044003c0c42040700101081140360369110f02c1c0103030010150080002225002c401011a500e82c201400f80206940c4d6120f540f039484c8400c2c04202d034407a040941c440440054001541e09180d01a038541155030b803000010390303801201400075411030107001e03c1d541c031000b024000e1854991090008120041c0600d90101200031000068001c00181e501c180801c090845c00340c0e40c0041032102182030700c5450541a80c5040850030300240f10020100d05000180c40d1588225030b841c0300710101000e02c240351a51820ba4405502450303502c03051701078020003c10071070007014900500c5242104d02664 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 281361214 1250 281359964 281359973
    0x60c0c080c01090c060329030307020415150327060b0307062001201b100623010203030a0b0a031719090609090504060b12010605040b010203031e090a 66
    0x1448a480d016242c0c2d110445501040749002090009100c030b4542000426400c5216520b2140010780a901100d07000051204955052085440d8280e008004120805055401c00304407101445020000700c0800945a40c5900a001d052007d0701542c070003160200b140101a62504e07241c1c00180d0702503a03035512815540c0c4040080030090034450311500c510014050b00640f44841c07811801d4030a0b41402005208445540b42e400c00e004080030303141e40c8401200381c4043c5500305682071b540661040ea0f02c20035004c00d0560110041e6580707102048030080782062450744c2c0c00c408041003401640304200150b0710300350581c0f0407020020010040400240c2d240c58040700c081c048100440045400614a06c40c103200a56800741c012040c01c140c4e0000b45020743c082d041545a210300c088441c0c444002800f00b01c0550b01081c80c03000300034000126141c0b14150103000b040c1c45c0c02410300880c50121000e00030740c00001607030722031100b0070904080c40300240848402518007074040305051244401600009 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 281362464 1250 281361214 281361217
    0x8030f16060f33030609020303070813050109090e0717070902070b060f0d0f0f0201360b041a0a110a110f040204030b04020d0c0f0305100c020316060c0c08 68
    0x34180c0c10300c0455114001841000710080308020f4240307001d030202d8038502401406030320300c007229005003000503008170500100381140314005000b01603807400900c036102c1041c1040050f06982d001c3e40c0707001e0603070784914010085520a0780c0070101e0ba44441d0007000101c040110521450080a0135201d40c16a0740f032100080e0313080300c241160400a401c0c10414542015407401018500450b101c5145840b545c54841c840ba440110141c02e041056080c0c806690180303d181d90328000480740071112446451514841090385140f5058a41c9141e0b400075070700103a6000e49044e81d01107407417110110884400b00c07110f9485a0109801d00c44c9150100c0c501c0082031281360f902600402e840c419140d13450b0b0800003c44055040300d48034920601c400d0010512070611182d00a03030542c1c4900c15a1140d081202c60010283d015842300810004040108080445d00d6051708034040c105102d072540b03601e41640c0724011030324901800c2c0c0d41f80d00820081a015000501404924108405d46a8054540794031781e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 281363714 1250 281362464 281362481
    0x60509061807091a0c061003020d08090d1e05061609060503040212070b1e07111c15090308060301110702060d180309150c080f0c100c180f08030f1606 66
    0x405001040104c900325081c450b1a6001d43c407e0000d01c6150708540c001400440380d60710250100c031020421458030703290688406542a04224070244450030f54207140700a20001c07108407010f02070303000400e1410001c0003c80421000720786407072408904086084546400040099a04c0f01010900018030385040c400c01e4044c3c00f5907a0100c2ea100314120078180700000242034099880010003820022880744410302c45440d00440b0000384a40d00240c1c0b990030b040c848140139144481c002c00c5030044c1009070340300c42d10280c400d0312004903641c0c1d103a0416080300e84009004007072800403c8524014a8484000e00e0604480d0320002030050b011940f000e02c6a0f030690041740417440c000710500c1810708107069000c110840b454540c05080c0b40b5a226041405804980030700c4040200d0310f800c0c40c00f41441240440c0b010400708000500d05a0b40040001094800e01084082c03402c4000c545840060450016940890001c501c0c04c0544101072601d6400780f0f42c1c40031000b0019400070005141805503004 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 281364964 1250 281363714 281363759
    0x8161101140a15060f020303010909020f0a0810060b09060a08040c1703030403110c0a03061d0a0602070b0702061e0403031107061e02070f020d060603021f0306050906180709 76
    0x2c0a51080c100750343c4110b91034001c941845010341c1700b00010307903000084030705540030400f011403054172610200303907001d018445441d0f00005d42000800d81c8440051400c2c5111785441c401d012050340c3d440142418803600390010380180081080c001107600419a44d0f03001842030f0403c02100c2da4408010440c01d048540a40d041d810000c00d2209041c0d005285030001c09c020005410080e45050008034001c841d07210003040a5154010707081c1d680c4441c2541c82c020070008054459403071592810324025802154119421042c03040801c6482e840001d801d80b1540840d02d182c00b008451040e24211000002c02c100c2c10192101d11000b18281e02c10702500440348980400300700300071141c4020282e40078503900020030328814443e01e408520f884040c444e00c1d50f016110050400d4141c00e0000c01b40c4001d80019400036185440f0240d1a0a041501c3d2030f01226558208003081d254801c0000100d002d40380d040c1c0c44440601d1115110503005041500601e0354189100440ea41d01030343d0164400300c3c200c048 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 281366214 1250 281364964 281364971
    0xc070b07050d0f08060910080106140a0603020703082208210109050c0406110f0601080307050105010503030702150901030605031e0705030c0123040503070b04080d08161101140a 78
    0xc200603082018889104050900069103500101d0042c4448401041d991141c0400d40209826290b0042980080e0103c94002e01090740c40b070b11200b0403010300c084d0003030041000c1c1c940001c4d1144644251640c05600d9540e034807080d2901d1800841c84030b40b02500300c003940840c28640d0001070460009052001c0007a21400c10640d182e04003000740c600580c002c0001c142040100103110850004484c00c2d00c4d030343c0c02d001c0040d05507921103178a0714410070030b0121207218040005c909800000301034215030b40320b50028012a0380310428140c490146901c002d4210301c0350880b950b40045c11401a0081e840107140016005a6580c00240340130b0b005075540c1d0a18500312038912441501340300d5803019010030f40041520040840c0000c040c0140f155402e00f1104100e041c000c02c2e209840d04032401810018126500682c40f01c4080c038041c2d100b88200d42861041840442d25140542d03003040c4280c01c800c01000c002c24a841c0c1c16240d80341c2840f15614595a500e44030203a00d80c20f072420901500d82ca69001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 281367464 1250 281366214 281366227
    0x80a020415170a111902010609140f070203090a090c050d05040b090f010204030f060903021906020a08060306090a0b07180305010e0123040f0f201504050d080307050c070b 75
    0x22031000d000343c21100383c907080c8001082c42482c00002c5030b41a424032036210340541c02040080740102070940240000600f400c41441202e0310410402c0e010324008121b000312915035000c2643c0da84580b1700e0313040d0003070280c110800c9001030b01d600010201815081072845c140182e1840812683e080342d04440507444401884100c8004105411440c06980c0086143c60b0440e22501d28080c12160001c0540307407295a080b003003601c02e00c03c0800700f5043e100340114400851034240065000300b1010400210040700041d418900000c0c0700d40100502d0010303180c80074454544860302940100340c0d40030302a40b61090759000b044021307010001c6000b03200000c1d403081d0300c41525095a500ca00900c1140450545500400840b1051903030000d81c07019000380809900d1400962004105001420a4480919040220072503d014804000c400c40707416001c000d5a580c85111402176004450b0071564aa00d001d0008140000550b0440b85a0406c0303401c12061354142490581150011040e504011402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 281368714 1250 281367464 281367497
    0x11e170a05010c0c030e040e01021201090b091513200c03040e07050301030c090c1205040b0402101107090e0118030906020c06041a0a0e190e0906070e01080a020415 72
    0x49103c41074080c42c0848a200040d1070007406000c2500b001d5210b10303994042c8044801c000d50468001480b481d48100c800e695a100364002000a4602d0031302404816002030300da02e0707101180b8424800001c21426505558100301401069030700322240300240e02c806c0c50100e881c01080545084086a4001c40e80c075401c0c20190381d549200901110107100080c001480043c2c032211215090380d10300440040c0940c645441100c4088180304403080803880c080510081c48818002184164002c0d00d2000d01615040c9044420341150441081c480d001b000060042d00980c1c1c2000410f04540c0c000070035400b6243d21940355507607402c0d00403004140004e60801100e03405100350840e00c3c40c112584c2d810585490840c1484001c05c140204140b0300009240715000d02070361807402c012402800529407017054020308100c044282c013525400c0d40f080800034000e000c0c0011b50502c144241d40d618031002c0105001074420b0b0f00c000e458112441c0d001e200c0450038080d2001c200c2003105140d580e80d500868000b60 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 281369964 1250 281368714 281368721
    0x5040e062806110f06010512070902040626010602062a031e0a060501020c060715060b0405010210090c0e1e070f030501140a030818061216020312011e170a0501 70
    0x1211140740c10070684e01d00d201001140032411101d041e40ca082081c81240c0f00b10b0b04014090300246005840840c0104100e41c0c0220303004079582c0342091003d1500306d425400c021020091141c0300042c0d010343d00248003c0706c0c045202140049007404204084001341800300300d5081210341d2200c55440c50f0844070784034141c02e21380d5000a4044020030a090428000170344540320301d2030407801003200180c40020888480b03845020031800072010070816449480e0104541c1c03041c4111401449010080003010f14148500498960f000c1c550384c000d0b41c684840308404d00401003980569880c7e4118807508075582148603403040382103649039004070021190180c121941a04115030a80240c504164507440d010482d50582c0d40110b42e298580383d8203401d002583c0c41c41c1d2002a08104080782002406124074003990248044040c10b440c1d410949104a0b600d0242c2001d03502c00000030300040180c952a030b584d48900c400c0072450382803100d0300c078900f84d4501103460b01c4c1c0304e4182c0d00202c4c1e884144a800c0c803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 281371214 1250 281369964 281369987
    0x2d070c090510061806051e0307120e01021303020904140a0b1608010e0411040f020c1b091e0702101d0c060a050a08090f06070203030718050105040e062806 68
    0x1c1201000860040100d290200f44c00745c8010701000050051507101084000c04000309002c202c030b0758910b0001801001290718010718641c141c104281c0105080b41030081d12614111040d40c0d41741c070b40c0b031138080180204010b4000d80d0210b41f26154480b102d41c0a000c0c8198181c0903034000d02017428900c0f040c0c0d0f0340c031585604250801c04483c0c0140a68080f586101d5006034003e6500f0041500690010300240f8003e514074640301e10002c0c141c81d50b090086a0300d00000400a03101070890403a80c1440843c1d103045a41240b03448100340840f1101c0307071040318260084482e1045a030119a10407030401140c4030340c0f072080e0301181c0b07058105060180400610044007001d0f15900d082000d40080545140201c01200d0b042c000344800054000388100312810f5000c1801045540504081390040e4803a84141c0e03031000003d50712007900703c80540003c80d49040300c8043c0d40e9a490240b47c41d002d202c8684020300030980c0034120014120300218404803081e0526454800c07864120316180c4003905851446 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 281372464 1250 281371214 281371217
    0xd0c030c080a030e1905060c0a060513050309130f020d0516030b030309101e170702162310080618060306040f0f06020309030a0e062d070c09051006 65
    0x4050b480c00682d0103600c0d10781c03103030081d04c02c5000c881554040e05011090303030b005160400c10114426180c9000012900d030070350301035882041542c5880440e031a001d0002c0c08050002c0d0b00400000d541c40c144241880f55400311518001054403184280704140d900c001e1000c020281c0350018000b00e49040402d420403007655003000c0051401400104e40c0342d000c1c80a025100750f42520003030398040d014407064840659143d081401e29690400041d0440344014100050800c0c004000b650540c00007502d001600c01c1c1c11402c1410a1400a520100c0300e141c180d42014103a01d4445103441e502c41110071070070b03100143c546681d103283c1042840504030013050b05110301823f41090024948002c5421a000703030f00300318084980209030400d003044c0300085400405451000003000130580011024016010580d42ea06110f409003a0411205014070100206404078500056030311078062108e181e28000380320261414000c2c00c0e01c40320400700c900e0b80090105030701e46040020038141d0195090140485 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 281373714 1250 281372464 281372473
    0x100f061d010c0b0a020f04050619090f0b0315150c0607080a09020a030605060103020f040e0f070305070f0c03020c03010204081e0d020303011701090c0b07030809010203130f0606050d0c030c08 84
    0x5071241d01c0c0701e51000c0e002c4c200c1c5640c001581019101103030111805483e02600e030710341e9100c44c03c1902030300307620148907036001032070301d08002c540e40e400007600d642260802c4112500350303107032400800848410000c0c0c540d0300c182c1c81e01586041c1e51011016050030390080c0054160351a10780303405003680d14010510b030b1606103422552001a40c3d02c46001c42520f811440024145d9501001a4001c0c86000c18000043c840401d00145078003420401c58441e00042d03075020400e4488002c142d0aa030415203580380401c941c407045100c007a206110b81940f00340240304540c80d6850103c007290880c1c0c00354000708007607044007000240c104007110000381080d8010000b40907500074507600a480c0d00060144109690400710441320b204001d401c0350310f90703582011b2021501079480440328900c0e0302c100c40840100c0d01340e00004035090818401d5a102d80c01c040384590700301c2c240e40c1c6d034484940d1501c0d100700d078010b07652040443c143d00d48400304280780340724201200a450035070414022946460f4080038a0340e00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 281374964 1250 281373714 281373737
    0x3040605040303030203040204140f09010612120804020d020a1415091c170a0302030121050c0f010c0803010806010501090e010b041a0c0a08130e010f0e100f061d01 72
    0x40c00030444003101d4261400607107a4071180300050192400c0d55401481c6900e40040c01041c4071031100352070044120300000c1150315078a64005001040ba600003400c6132030740300d1251000601468041e41e1091000304810740303041c565800a241e10003c0d030040c0264610300360b0101424100b64000e001d14242800980c0c4c20010020300140b1130740301d08034151340c100b1038050104007081015038009518000b00401d1584440e801480240290400d1040d0511241403a2030844144110704007844601d0b0001c02500710070b50b06009112400a041c8038580c1006280000c11000c2070301c07a17018601034401e400140c0642c0d450100018011010b80d008902d40100e868010803004504004540480b10303c1c104400c0b401d5000a0a40c1caa409090040340711401056018010821018024500d640c01d005401c42059220003144e11861402d000758550300040540612460484084999021402c00c8484220701c0c0c840301d000c1d0080c042d9034020004507002c609061007a5408001d0500c01700400e1030010b42c48803 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 281376214 1250 281374964 281374967
    0xf0d030c0c050715140706021c02033603040e0103020a0803040b2b050f0403081503060411030304030c06020d031103070203220515090307050d050307030503060301091e1103030406 79
    0x3800f81c8a11101c0b24003580c010040ca80c0101c0034a03802004d01c1301140d032114018208600698050b030650380a501044401162084451003a2406080c01000500009004131210303a08070841d00c0b042d4001e055004404002c3c12010001000901100540140b840d450f510521400eaa5240c2001030690000d00c17062000050b501d003030b100444081840f80b4444001440104062078002d07040030740b17903030522007007102c0d0019402c1164011813003543c45c00a555650301c0800001b06180319041c1e4960801da01080c08108078480748030a9100041c1a0303450030b076903a503034194100c00f50746c0400050b03080781030807481d40c40e0540b1410b4280200c0c840c0301c51462806960080d220b1244542c10503081c4119000204241850042c00015000c0500310040342c0c503995414160036003000c030500d0311911561401050506081c1c101000740396005005504242c1e080c0e42c207641c01c2c4c10007441103800d50741c1c1e205100041124803128005944a16040380300440e024100f109074070294400a42c041c0e84100000c00445 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 281377464 1250 281376214 281376223
    0x60304031209020a120302010b09091b060d020d1404050111071a09011e060321090b25060b0415210303021201270b0607021309050f0d030c0c05 63
    0x1c514950020b8000814030014079070044a03007100c03813040084242c40341050b405500800440000704c1d0038002c2540c50b006076036a036403810752640304486000c107807110302e9080003405005e80c03184040b400350401d00d9113882c040882e03e91b01ca100f400c081c90003050005018003031082c0c15104403646d141501d801c0c07a030748902114246c20321041100281040000c2d102d800203500841180c96111021540c242006c014100507284030700084c1d4030207240030f465444a000c01d02d088a400001602c07070300ca203179160000700a0030340c019818140c08200d1402c410071414030364682040040d4070810001504140f02418401128a10384403000000030080342030000400c0520303a03149403038102c031640d5411042450110081c2c0195500701601213100390010803051041e055102c141c20108003040502c505000344041a83c0e009441c030b903000081040020050f0070005004912095907a0740420307581140c0da55030b0726110703070951601e0b9280c000754001c0000380d40c1809a002003a00a1070000500c1c3c0300e40d2645500c8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 281378714 1250 281377464 281377487
    0x2012c0318040b040603051b0105030f270a0b0109110304050601090b030a06140105030d1416020105090d030e0312090f062b090b010927020a0b04170105010506030403 73
    0x4002081001c082036550798005800208000d0800d20031030b07541e460416650385d00b92141d0020103200c41c5c10b28455511907000d4a208121030300311482d01d515220200c59242d213084007808a00c040d81090658084810000070703280c54400c100305180d9600d0007918200711041d820401900510810a200c0840c00016559040d903201d201e00085034000d03030000a1034800e060000800b980c0c20800300703940ba0003e625015040b5030090f001da0304682c2d5041c6003107980b00c450104200d00000240700740d09076182d1110030f0704030061060410615040140c0002041e500e0700311811000030307003016681410340c1414402035084d450031a4000d8104070050001480c2c800380780d58103d00440000c0b0ba00700d0140380c00040d4802d804200500f6a100d0203409141a01a011031181507401e0140304000140e03400301ca01c602c203030ba4200022221001c03440121891041102c064040e07030302c0f0345010004542c2e800040014401004441800040d80c0710b616045803e66405030b0046104003c103100300400705c1c0e04602c08200 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 281379964 1250 281378714 281378737
    0xf06030b040201120b0a08010b0301050703020903190201030207060204270b030d031503020d0803100f03030509060304030207170102210601090b0d0204090516110c03070911040302060a02012c03 85
    0x200140010070000085c64103450f8a81e00c03450b51180084c1c2e079803040d4001052500181e00a04c1700c0d60700c2000035016032046c0711900c0d030185d014a0799918010501c001c104d80c1c00d84149005858076441e0740b240820780c0c02c030b50010401c80400784241482d4407040d40c8034401502500a09104803480400080d0711540456082828941c0f2403041742040b1b4041608080515402821181032840c641058a190380003240c0d440e400008000f40807601010b45030701d91049a505036601883e000c559024483d40303400150046041d449a204c010400752250986160902c03148d03400140c94100040010015442c1040080c0f250b0110760180101640e0007a00700064401d410401030341e468a007940e120091013640d11180e242c0f0718000500032055100d002d02860000e03181e81d0525034001c01c100c0117441e9403945100c80d91581c4503200410001c90640c201d4007005510b858014105596500402e40a5004401143c0180d40d2040b0b04102e106002521596142001510740b1051012881980d9640b04501d400c09 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 281381214 1250 281379964 281379977
    0xa1b0308220b012310020307020111060408070303180f050d020d031104121509030c0c3611040803031006110a17071b1a0c0304090b0d0b07120f06030b040201 69
    0x5440408561035031320000c0c0030f05000c00100c85400006d40b20b13042400c0c22030003e0320b4919008600701d400640c450283d44c101200c20701d81800d540d416401048500101050800941c0c03a031004283c425440b00840c50240014054a00050300000c4c284004506690181407506031901c41210448007a20145c03107041c20130180c21400c500f4051620120400d200c440c46050800c20400c0580c02805120030702d10410301d581e0b2460701c82080ca04983e029031180c03c0c0710302103a40040f0101d105000c0100010b8140e07840010b6685640c481f2224030391141c0c00640741a0b10010a0000d17039110f00c441c43c0001c001c0d40c41c241a52260400398581c482454060103400d1128001000c022520900700700c2e46c0003035100ca0310500c10342070203000c01c00d507500780c0c0b0130b42d2016000304203041d048140c04002c580d242c1106102940c81c141c18205004002d141c141521a044030754010031800103032031039000d58000e00040d21403040d840e401034008000d680036950944240307070404070208009020180200d4020b54242031a5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 281382464 1250 281381214 281381249
    0x7030b1806070201020a03060501051828081609060b16051603030f0306060201020921010603050604080408010e2406151303050c090610050a1b0308220b01 68
    0x88001410030110010360340584010b105103160150700400d03840300942c03014000d0310350f60390040d5041d0040d030211f01c0c105046500250307514905203c1c034016102711854465a220a1030808513800d038059084011207500440010075039107000c0c2c034a1002400c9103c414030a060425000c4200c0c2d000f4100040c51088009a40d0307810460140070b031401040000220a60281e0740781001461101c01d0b41459010038540030700403584601c1070013202c144920180c1048a070742900d0b008102202410401d00b220b035542d0b01c0c0e01000060080c030071240200d0094003d281c03168204103e41d400c42e2403587c0707961200e620001c80810303000185540b100004040e040c02060710750714040407603a00e100303000829144074000200c100b103140c42c1e13050041c26a40035200700c1d10881140d00902c00303240e4083e04d0031940b05030b080848085492203280140781184091030254148001055981c00c5210441e904402181424080110204a0b0508000c0352004000700985803d0720340c540f1091900113008034500c4c0031680e2543c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 281383714 1250 281382464 281382481
    0x40e07090306050f0105011205091f090c0608160215040803061f090f050411041505040e090c0906030c0d030e0d080d052d0106030c090305011416020106060207030b 72
    0x300000d5410020521080c54128081304e100c50090080501007a200707090000322114a100c5c80b80304104040090000035900d208000a10b402d40003000043d9468640c074500007001c2d00b8a1304005c2ca020b07100c40345507003403054a8a041c0b1000700444811540101c004d2128003040c4010307503821079004071103259681c5960001c2070021031411951414010351081b0301c500c05074085202011a07010404681c031250700c4000308016500c0d0a406000c4030a020301090220705024201c8150213145400c2503458540d56030320307600d8100030485502c9042c1d0000415020503041003801640d11400882c080c1658a155000003a2000d8a601c8091b00b04043e0b24500602034071140d91810b141c42d0032030811504d420070800700d140a4103040701e01510000400007014210310b1400b02c0c50181d8002075041c14440e80c00c03d0f1044005041ca89402c0007040f13000180040811400c0c8244221701c94038200850a61401e030f402c0c2c103482c2405800d414110380c5400c030200495035000c610103040d2036104220030115100d503244c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 281384964 1250 281383714 281383727
    0x2070215070f0507050d08030a0f06080f030705162306040503100930051305040f02120117150a0f181103060103031403100e0a14100b040e07 62
    0x100c21411200020300c04007440b0344012401e0301c00d4801c07000c0320485500c0b4400d1084003400084001c2000780c1c1400403906030304180d008030107580b1204800090190352649260301c0d10a602010083c00e4000007400414000701f4000303c009503603c030f6003090505180c14504012446244c2408101c020b01e5010b03003020b44e41d00c41c101c40003010f0040485002051100c01c41c1c0041c02d55034400c41b20000c90440a4000103c4540040c2e00284400c1c41c2001a800c070b40350503165a03100500000f404480e0070702c0490326070365074030926006c06c00c514001a15800c0a070044102d1900682025048a01e00d100d000000791000501c00c0c7d503241014881411521500498000307000c0f00c541000040d0304020300d1240070081003098079038581c01162800b400c10258010b050f12081d0a000140001c2d4080403202107002042c0c0003542c2003038503142e250720030320760f900d900440c0c0a0083d41c603040c4503900c8d0f5030650711f00d0b1034424007560005003a107030000040c0d01c0c02c4060107443c0310b940f14012040078404001441c01e40141c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 281386214 1250 281384964 281384989
    0x207050a05030a050d0513051e19080a02010507111207050c09130302061e041403090d050115050415060e060c060f040303050f0709051909060803071e0510020702 71
    0x8040b6600c5024a45000c0d0a5403c140180c1ca4400d01d0000024110a940d03080581126044401f9110801200c006030b01d01026504808002d48200b02e0051150400e800171000c10074040c480e0241c84081140d402403c3d140041c118404005203248105082800403801032100f28a010066075107411610b0110b06080302117021550002c50315007044908400722486c4400e15203e40c0c03d80b81d0ba40e881134890071403041c00c412101810540b440002d40066041210181d03800c8440e01140e05100d60200064083c1c4130010080302c85944906452a050204084000142400f224244803241c01d003c00703a800b060a510407002000044000304106445400c12241d4140400f41507030f840e03152000c8800b68132041510201c00107071600c1c000911409804007030a01400c840da4443c0d04031403900c010022a05a043c54203030601181d41d80005e0601883d20600c3c00a000b20070107161545c52030702b011804442540481c65403442c82c220b6400020b10082808003555501e22001a114011400460b00208030030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 281387464 1250 281386214 281386223
    0x50c091b0403082101030c0b030402120d02010f180812061507030c020117010308030a110c070f03120c0c090905030d06230f030c04020306040e1603060f0b0f040207050a 74
    0x207010007030141880c018030039400d00307944015480103000e540d000748a0342444040d1151b0a2542c0038805150081e0085800c40e0006010182c4014440c14103800c0600c40546000942c2d5a85d07800306201c4c4550182c509a04c9100d200c2c0c003154000c42d21900e140d4426036064080025481c4002140d035500c0303010500050401420803034840c941c901e0040c1c003506480c481079022814414090260111541c01c141c16a54400007581c21340d1201810075001c0c0c490550321068911f010320550344410010803a100080c000240d80d482d00703030b02d1420046030b0340300c1d4000c8000800c00750ac16103002044000402c4c604480d003541c0300040560359428518190b01550f801500d080d824200c00082a013254811000c180c1041446024003d412000b041400f0b90107007811901500803122170b480529003a0301031680700300042d002044c2e42d64501c403001d01b41031400340302c0e084030300c2d00c0807040c003d00c400751103841000c0501480800410400c1c90004465a1000501e01d104a8000076030034100704080c442d1320002ca521 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 281388714 1250 281387464 281387467
    0xc0c010c060e061e0c03062101270c08030708030402010c080d020d020c0105090109031209030e09010308070b1302010212032a0d150b031b0c121b0a050c091b 69
    0x121281401100300800f21300d9282d40d0740801e0307809400b0b0f4212402904000c0105424135084180301d94280204201d10280355070f5002000c1140e003142d80040821402001c80e000b404070300b86001030348501c4641002013541d10611501c0002501d0304116070b045602402d08a100140318540b0700d9841c8a04c04503004071034001305009070030b0502a000b0b09500c02640000340825039a410344103088030100c0f503026001428031202e07038552101f03a46c1310007400341c001c2c9844140442a000070402c100c10a130700c11510104000b03060018440503580c00364011030000e00c130700c40c2c0d80584c2c0c0000396111200803c4011070702c80040801c00480150100d240351450184007100c072000840b0a45910382c10090880d030b03906003805088500c030f901785034445080e0760900c400c0d40d00b5903d0740d03c01c40180303124001415103007003c20403050b1910740c0104503101d0000c4114070001da80d855500304112105140100c06c405641c00007a00030f00041c0c0c00304060f1040e1005480c2d500880d0b82c1c95540364000701d01c03001d421211030350 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 281389964 1250 281388714 281388721
    0x6090f0a120c150f021b270405160f09050705072a0f0810020a0212070f020103140613090201051603020a050111030601082802030c03090d03020c0c010c060e06 70
    0x642818003044952041c080050610f0400060702e82c284403016100060308800302c0c1807061150f0021115222102400c5a80c24034541d140c202061180b0f0785e080041510058200400c0200801040901c030444200100800d0304d0100c1034201c0d542d241c0110555107454034009480944140c01742d954154105850711461501265456801d80222405445c4005028004500e40541882c51011903683c0402006941411250a0001d400c4504c000003180540c0c0c803508002040000940866400303001c1a200101d07441c40090b0840306944280401700e0750143c1003140c90340d1001004208101c603070001003840c800520040b1000d1081c1c00700000f5a1101c02024418075500055032010300d80305070300803c078440005072004070b0781c0000c80e010760003c2e006200044d10072481041080f680200445401d20b62440640200280c0c1c000300c43e508004040071080005601003003100000030211400c0462504405441072900c59030303024043c50510040c400d050341000410b03400620851030007800d461749401d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 281391214 1250 281389964 281389973
    0x70f0504271112060102010b131509060617060409080405010804031806050d050c070c1503151202030c040c050f090a0305031206031b060406030914011b0f08010506090f0a12 76
    0x30000c01400350382a040f40005442d81d4014030580001c028002e10603185034000c022404050510034034504d100396161800005d11a0003400762401400403038031b130650001110021440326000040c8000c0c0300700d090070708010204001c40d0403071301501c0f42071030109119520b0b070031b00350f400301024001501041b524101c0000d4803a8480e01812300300f41416014407003500d468201607224011024058450400b590f010000303809907801c0030602440300c0c24046512083d003031102d110124294003030032003807a00140c2e103411490188104030409004035400c200080001000130024010505100c100700380c001000356141c0c0e50741901034002e65000e011265101d040c05c407440e5a6100a84145001744607403a2034000044c442002c1c1d0401c944081c11240c01c0c23919164046001e00880d207010307141441e600315100e841601c01c0c0100d004228646c0440180e03803000c04c000905189807407054208000880e40184000e0352440c044544100b800c889071382441120354009400c001d9903601c403034410301540c030541c1e0420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 281392464 1250 281391214 281391217
    0x10207020a0b09100309050d0305180610031202060906062101050c040e28050a020405030a0309080d020708061f0e01060918090206030402042d02040806070f05042711 73
    0x1034113890111071190710f46001c0c0d094503c9104018015040310300b508098a100b43c1c0100d502c80c0c110403010f0024502c0c0020305003031580c16140304207420110303d0140103100001000d10840c4090344001c103058508a80c00e141c0f943c80c060b040070300c00c1003500c04629000c0c1a5441e11282000c1c058000c10440c24000d0200351154098810752004607542d40001d2401424102003c02540400e40f904e90910180c0c0e0380940184002048081425403d200100300d0b41c508100030788140380300c0c2d2241ca0605041c000f0140c80c028000c041c3c0c8085621403507052055031004283c0c0c0760402d2600200002c58144404580103425241e0081019886076800000b00d40d50300080c603404403160402c02d5001c40c0218290b010a0314110034004e03400080400c0400c0c01410254000c8000000c0303890002d0f0500b0800c52404103c5200c0c01d1800e541d286c020600744004001401650340096590500502d40d020b010406400c501591152010201d101c40e99034211021070000b4005011004100b0048039072000b10801d02d5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 281393714 1250 281392464 281392477
    0xc01030c0e0330040e0105030f0d051e040905040605060916020a0f020301061d01031101030c0822080307020d02010509010501030c12080c070b1c1413020418050c15070f060e010207020a0b 82
    0x46c0c801d1840c02000f27401c0118100c1e4903100c0690701e0510700608080c24030740d1107023140381c05d00d0901c84c00c000001d0301c10001c3c0705003402180305100110f90b40c1820810080302c8540a020b000003090b490709c020809a400050035190182c1c04100a80c84c10740900000340100480d520442500c0f64060742c01600a00e42d55003103040c0c0344108500803d41c0020740044040f00c4445600c0b1000c01c0a50002c0740080c1a22981c2102414108424104c40c907103d545014941c4c1041da02840035034004101d445a042c0c0a002d0b0561215501008200130341c0745032103401c80901d491041a04031102d844280303007800002001c450b6924001c1c412103511580e070b12148025030b800780128600134151800400c040013240c2c0209210700d2840ca03034951007521018080314400007010012070740540d50700c1c0b0b010086107540710204001800f0f0703000360100302012014408070f080e19090302206810108070010000d09491b1940c00d103981c0000c00003078001c44240d0920b00911800502952014458900140e2898100010840c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 281394964 1250 281393714 281393719
    0x901090b090a020f09090c1b160509090a0f0821100b0a0801030204020c0a0611090a0b0c0d0507031b14100204050105071502040f080c01030c0e0330040e0105 69
    0x69a0b65500e610b500701e01a180c40c85080b00002c00c01e0415500d4075884058008041c098114a08a0f04044401d12400c440d4913400c40c68026144582c9465042c4c0c034040c004003400d8841501d10300d00480a10346a40c4948070050149500c2041c05091240d803100f034405c01c2010380d40444da03061140a480242840c101c030200b030001c22201001c034000501e03030309071a018075203a100c6403056400c641c05c000c040c2d04006011207207072091a0072180840c0140c060f0282da59819500706650307440c604180040d0001c6500b100c0f01c90202000f1885421100052481c0006198640103449a0803031a00f211900210355560b18000003076010001400b403100741034a000c00f5060200ca4185000e041c2450990145200b405c0c0850000d0040101040b001d940d411940011600010300d81034507556025101d0032a0707007040100ba40401114440c5580510484c80340c15507508003d1442c04109001030341e120609108144620447c290102046010060200c4681180244180c0b500e0f107d01c03402d05501d009226052 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 281396214 1250 281394964 281394979
    0x30807110604081b100c030e03100f050618060d060f0b0901030821090a08072102150a05040b04020f0a05130207110a0308030106140706060e0402090a0b06091302090901090b 76
    0xe00034600301e0040010320b17080b900c980f43c100740706071400d84074440318203e6141c040c014205218010748803440740380090444800c000409040000c140301100d49140308d502c5012840000b8407450b6078074400c0010409074001d034041044440000d140014151003030989401400d10000803080001c50000790a558000088401186427200085038215005a0b68401c040d0000010500458211002440c5581c05503811180c1d94080188007100f18014901c001d0041c1c1000c00041c1494038030414a9401205c1c80106000e50305007a25505400000a04024800d460b0019040c881d51201c00c544801000f00a1040a044030b40c031244d100694403100c81140e0a94500100b00414640594a102a281c002c00b616085a00f0007030b0940d1603040850032180320300c0d0180081c00c009901800b4000240100c00002206401c0500c1400080100603108070304c0709040010480003500c5039419140c0d031040440d42480e0440e080ca41050083c0b003402510780e0004010000401e850300b1030380000c409403900b9210308 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 281397464 1250 281396214 281396263
    0x702011107030206030109111b0d02060f06060a031a180a06081b0607020a0305030c0109060e0a1a06060702130b0a080325021513060216060203030103080711060408 72
    0x684a1010b03000003940a0f40610040c004200950b1000350345800f02d1461900d481100480100c10400c041c4207000d1036804091500b082c1d41e41032281d60340112020b031411015092240016560b4010440301c14101130741c801c51620340d2205007001000700b000c0a4240c4007408940310321208500d0040780d8442c105424003100241d0840001040e00c0040020100c4d00c2e19140300340108109688504000e980c05484180040b020460a20040c800e504041d000043c560b60039103050010f895248901607843e410140c0220040340307072401070054070b68070813445a80b02e90343ea200141243c0500c0748003941000030080c444115442c02d0f40042501c40d01200c0b2400b503076a0307480c03015950b4410303210040701c00000c0c280011210285401603c0d107580c40140450341405403607100380c1c05500441c8002c01d15002c0710404200301901400b1030068080c44a0a000081d8200307d00a5540d00c818440100b40700300c0000c5031024440c00082c0d142d03000d203005024603600d0340d039101600c1d40d90300030558000d0f0704c49180000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 281398714 1250 281397464 281397497
    0x20f1f0804031e020705040b150a02030a0e0103060605190311070311070509010501050d0b0102100507172208030a060f06080f010e060913020d0c0909050f0610120c0504060308070201 80
    0x70f508400105500030f161850070882400301504400c0d050704c2c1c0205513404010303520158000a401c501d031444d4019a11104000c100400c40d2001809060525203025800d100b50742d489802c90f1345500380c4950050300040740a400324010314480d00e0012b518030011490321700300355218282e0b84a01d11072208403100907845104201040f0028811710307011407020403507048544a1340d0040454018140180c0c0e400300341c026120030541740100da44600184004469200d40c1480740c00f0180c10201c80d00070036042103113030940327031901012311000541407043c0032000841c038000d250040006451500381c858001d55541801400220080d10304811050400c000450516000003a00d03125000003010740885c0e0300c80e69680580500002410b9070446024001a0081200e80e082c4000904001400281482e90380c10210308158010700b005103181c001900b800344c40c15412440e0401c1d1484015000d045000c5480c0a2645040383d900c0207400034104075001040c801801c0c064403e05d07000380c8821142c1800d2518 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 281399964 1250 281398714 281398757
    0x50405010b03070813060618050609090a02130207050a050316050f0c030a0b070e0a032126060d0c0305010203010515090112020d0f090609020f1c020f1f080403 70
    0x11807400040259000810070a84000303145c050746e004280001720240c40303440c03407100140007100318001c15451740d0901185060048140d5401070b06403016160641490340042c40c104030841c059141603030003203126000c0c410184501c4003144d501400f22035850301e0301d444a00e0401011030b0107582c180100a24105640801b0075418001a00200901940030055450741035421001d0080ca0410988802d58890345d144c003503005002e14001c1890206a00702c0d10000508440003066540800000118004070007003086c01282d511b40030341d0803100195403890013090403403c034090041c0c00501c020600205001040d802503050710425100c500c1302e4440021324150b10301c20f07051401e0004c0c02c650802da080c004194041c1071504c03400b840c08038580d110424200b003a1403400c001580d4496840800704214605141e0704001718005640c03821880c54021660f922942c01c0c84400303400b8100004680c5603d565442403030400211000740840300782011440245030400480d801c0300032480442040d404200d0010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 281401214 1250 281399964 281399971
    0x3050a0309050d050606060f0d05070210111804050a02160f05010606141806160803100f030c09090203011d0d0e03012f0c031903060506070b01031e0b090304050405010b03 75
    0x14000c0c01d05d61100380a00410350b1000e00c041303c0c84242400f0012101d1064058140a101300358004c00c450312a000c2e82d2422900340c400c41c0c005071b01d0204070084940b6041c60000c040440102d42c0021260346402c03825019100f80c0040c184480d020b01044e40400813201041801540039a0081020300d45030541651450013904421522900510125030821402c2d107880503580000740200e1f0501ca52045864035410301e92004540508001c820000c018000c0342c81070b001400c4504940808078a075481e0040300400c0360150a04840e1192740c100c0540d00c09400811404146118220780941d49a21090b207407030702191175000042050300d5000607840c05016043c000b642c501c0c40b620020048464042d0942c4152029000c503072000d2140e1604003d007400901104400c150703080b120b0001c00300008084880f542c00480c0302e91420310103079011030048201c15040d241d100800c41415000c43d40c44c0550728440300c07030040c9000440030401842242c080041c1c022900251004c0c46030f03980358030030000d5500044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 281402464 1250 281401214 281401223
    0xe100512101d0d230702010e13020a12090201050403020d0602120408070308071106281506180305070e13121d04060510050a0c08030a0204051503070206060f0f0a03050a0309050d 78
    0x140858101c135001040a20b105042c0f00003a4050721011071450721480000c2059a6800b096500b449900703c40c0f950b104000c050020881ca405503800070305503004902029015000c21800041049800d0b07041b1030422020200d06009071400b031804e101c1c140d22000d0f0031800511000e001c0b40b081ca0113290407001c019210400390542e07a98004800e90f10204010809036030040801e0800423005e524416018220300c40800c00c1803031810600f0141c20420b4824000d04c00d01003942e402c202184001c1035480541300c0c00451900141c940540090400c81c1c8814050000303500c011710746081c190800003480c06001c8024041d501c2109100401c011a01503103d4103030030018660b01460a148100020a00581c09040c88404210107407100b01103500200c41005800382e0000d014400b5107003604840c82076124085110f851850a01c800944075100542094010321810100b98001d5a50030000e840c084400307845252140e07941d0410680d0707411000f0003540480e004c1c02011a03281010050f404415820 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 281403714 1250 281402464 281402507
    0x141603060c050f0c03070302071d3402100605010c0b0112050a080703030501051804050322150314060901060c0f0218010e0405070e100512101d0d 64
    0x110346401000d00780d4445800d0800c542081180e0b2500d8281002d1300c400c0786078030015030f103407051494060310300041500300c5095000320f081c0f040103d45c113050019030702c0201710381c600600d00440c964154903d40540d10348100640109401e803489503001500496640c240134040c021180d40f100151540d045602000e440308101c000180400c003508082c504d4003512174000c41c0c078880035036224000d07546c10a540480002c0c0d00c0b400100058508070060185044007217940f011a0300b416601c183da24807840700c00d8224034908515800400344003004800060880c2002006c90100d0510020f0050089044105004031000007160807400c24510b00ca040e21007a842c1d4584003c2c01e501c40136110080001c0c03c983c4160354101b4051050804600b030b5008220420040d0001c0c141842c2c4281014620303000031042d400c80504120b4803500060a2030308445043e64203c4c4c2016003400c0480c2460301c0d1804545146007481c403440040040754154902100112040e40ca03070384003100007210310b500d50992150850b9903 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 281404964 1250 281403714 281403719
    0x150e010e0a0b04030b1006020d1209030c0b1f0b09060a08040f06110721020c060c0307050601082b080414010b040507120e070b0a260901091416 63
    0x140464858039440102107200c1035590740c0d8108600d5000d608102e40c9400e03800288071081c0700b880350303040c040c1c5210f001500b0407040040004241000c60221921000c0e1210340550a16010746d0318011501d07048405440d09140000c100382441402c4245400c44285010340020340e0361101c015038444100090200e440c06a44840407100031070050b0054550039074000000700021143d110780d141c01d8101199a40e11f0f1002420007070000e070780915a04c080203210760340e200364113640030500360a19041100c146448070303000403c55185000d40d0304c0c028101e214810011500410000e5034070ba1100c00382d20142c104030340811071400c0f83c0f10912600c2c1c010a80f0340b0041400070300c05042d0b80d41e1607104038000084078512540058141e44066038150041080e51140705520010b5000d18248246400010800e00b0b182c207100d19402d1003590014001c000e00d02ca42011032012004081c0c081140c801948199410705548041c028a00d00204651089034000c10b0722041c440883c11451410310003204000061 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 281406214 1250 281404964 281404967
    0x1130070221071205070303080106050c06041709030a05060108060702070810020708070602130603050105030f03070b1321170105010203071407051e090f190b010306030b0c03070801150e01 82
    0x18020000403115000703819020648140c40b03580e58003d83c1c01100180702851940c10040c14031181a00325004204003041040781c0340400003801074000b070f4403c440400b4100b04500241c0395005003500c03990305018100010007401000620319058507105801c0e141142c0303c0900c21b81c0d42e4035051040c141d481c1c0102d009004c0030001c5d6800f0741901801100040c1c030304801d035692481242d00c00844e456600d450541e0500c00580d05204e0315000d0300083d801400e81c195142c2145907203004468009154280f41c0000400c0d00401503e540c10031a0310184602c4076624440002620641c1814901c0c0003510b000ca80001460354100414101c1d601031f0061480d04400c0c0c0c40d9403040064511442d0a50300c1101d000052980b14402410720300c1c2c04001f120300c3c09a40740380030061411000307000c40301400d54050900c02d041c8041040092031100f50703480002c800c0c40d0310005801903c45035001505103000d04041120ba51940700086114400c0c5a41e440c4440c0c3e200d40c80e0070700c9190911440c0000990000c11003600c2d5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 281407464 1250 281406214 281406259
    0x11090708070c0c09050a150b0f04050906040b0904051c0203091f030603050d020a031e170411040603080706050702070f0501030e0c1002010207020a0f061b0311300702 73
    0x30b034094500d5400590b00c07000c1200a5900507039a9003240c0756507081ca064418541052500070780b03c0386070407915080c150100d2180c00e020b54055244220031000c0449d116a0300c3d41d015202e8030310b020301140f80300e180905000d0b0b101c447c8031814001084110802090452002c0101c40c01240c2c000c217450800300301c241400210b025540c13070110a02d96940400310101d0400c021004001e060f0b035005180d004030341d1600501c1c40c00c80b5050a034401c601c00340d4440b0282c1c1c020500040762010310b044480d060381c490520003ea000725601c81508940b40800100500c802c5000501646010700b0081c0704035103902d90201d075500800e00c501e050a9407200818092503100c2c5e0408180e00c410602240d0480f801c07200003c0103030709880108000360391300182c1042182003001200008190309440702010350711700701000d48250300100d0340b059881c0102c4034500030907014042018101c5103003401c49404914882d00901c5c10950340c40c0005682e150b070880f84104001e000110b9200c581e010305028441551180300c184507 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 281408714 1250 281407464 281407487
    0xb030103120c05100b0f09091e01050c0a210204060f08060d0506040219050a080c010f05030c0a0f050712080a0e0c1c050a14010606080f150d02010201061a03041109070807 75
    0x5614046c42c049036078034000c04902810f18000608104031680c0c910701d10501c0c16100c0305036180d0514041018404c40882501c900e2038680c01c0034212000003d032901c40070340742500d29000d43c520204022a000c0d500500b01c180c41e00035625260400c4d1103000c1000101c4441060051081c0d200c00001801400c0180b0800c801804155111010986071b500003034102015410184e0070340d002c0401d001c00c030369026000d10032180290034200d01d542460300301041c403845035220020a010f11140d9180c0068410401c0701c040c0350304640c0e29a4007680a8100412007007007500e0703403114a800d1400f00302c800b41010680800ca500d0040560803964a8840190418402daa0003070742c0e2030041c4100a0042403440440c1c40c6010a84800000e5960401602400200b0050602610300c11020108801003004042503103803c0c0d0704035188210103045200407405041c0079000702c41088002440050203d0403540654021881a5208545202080c0500c14615401c40d0628000740320742c80456200d90140490801 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 281409964 1250 281408714 281408719
    0x1225170c070b04061d12120a18030807090f12030f03020a230c0a0308040311010501060917100204120b06040207032106090c08060117070f0e03070306060b030103120c05100b 76
    0xc036090100e18181000006c1d800a100c07510300040444610280700708141c1c1c042818903080045400c0354103c070501c0c030582400101840200380108440d13500a1510200620103a020480420f4854920354070b5401c101000f1400700e0440c0814a01441c001d0003910411001d42da40c1d161511400302444050305a1101112160701003003015003c9842d042c810a50a41e004c2d88030060241004d01d002004204504540086a40b4110050104640c006d5500040b20700120040e00b00d0071029092a0a1181c4c840114a1540c0300060010b00010440c2200c0d40ca2402007604e200c2030f684010901003a48105a0000d000030303219582c040d0201c00c1c0002d040c0c800c016443d0005011611041c0840c12151500b8840c800b1580160801c0f0840da400350005060900c60039081a190a00340c6004c0d05130545040d400c028418000840d2402c1c0c0c40822a080046030080b80030b000f03507a660740395141c05174000e000684041420b0707a401e0601300d01540c0c0110780b140c2e0100081c4041c4d400c10441000501d551044151f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 281411214 1250 281409964 281410001
    0x60d080f0a0e03010509160909021e01020f06070e030d1d010c05030c0111040905060609100e0301090f12090611071806030b0a0b01020c0d05031225170c070b0406 71
    0x82d41c0e18244126842001560001c028881016055240c21051644103900321810051640c0050310707000d10008601035000003840c000c100c0540180d09100d100321650803c1e100740010000d4450307001e1021885800d054087e91807106e50741030200d8040e00c4130412005a0990f4180480c1c0c03039481036003104401030098056905040c0b10311038150940e404110b800c00340e4040441c042c0500c0d4402e02c9001d410090883e07100303203416040b4011900e542e28107040c1c1402d12852000e903100a4a0a41000224907407001c00c088500c009032500f030302c40f43c000a41c0d000000d0040040800c04034010b0500c8400c20340b2020041070001e00c0c0421140f4a004403128000d0307069150320000000030803072a0158018440d9000100d6420b004200091a001694160a01c1100280141404201c01000321092101103c801000c01e5a0f80c0c02070303a01c003642040c01c9108104000f10800481039000b050303103002c020b04410b080025100e14031644c00c0c81c09641400f03030880d40008041400904a58010724041c0115410300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 281412464 1250 281411214 281411237
    0x10308070203031306030b131a0d0213060b0d0e0d090314011503050120031905041412030103050d020a210e03030a0203070b0604140f0a020f03100608060d080f0a 71
    0x104c8503092079071280307010035210b1a4410461400308483c40d04101144800c01c400c1c3e090707100070540b01e8030115080d8080d4001c2e01e82c1070103546901d01090040c9007590418410948c0c0c4260f03c40c0e041c0d018030043c81e007291414007900c19a99001c54001c96400c107586e9001c08250035909c80d000718001c1c4022014440d0f50302c0700d02c40e07030060742e1070559001180100000100c4039460020304d0708035240c02c0a07001c01d080080041208d00201c032210305c6c03c0b0010350b05d00000d840c0d0b154680066426000400d5102500c510308c020143c0408090056050b030384a107090f185c0c0001d000380240e98405201c0c5005081d05201d000c44a01190448002240383e03829140047c50b540c00400840d065034040c00320400160000500700040c0041c96101c80c0c3c212100740d400f0405542140d1489180c20800b401c1545403804080100e50f01c7e01854051350f00b425030810107590749040041d59003a62000074466000031841c1480021440c0c40e01000182029400c03040980c5001c0c5140d04400e11544526201420700500c0c2620 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 281413714 1250 281412464 281412487
    0x30818060705070515010602060106031a03010203310f03050702011e02010609200702090c040f0b07030f02030a0c2603040516080714040c120c0c02100f0801030807020303 75
    0x40c94040e01468a8003503490403642002e41c104002801d1149440705040d004100450740020300d1411108580790006904c1c401d40350040b0401130b1344200e03035815800401441070048000502850300445a8145229824019008201e40c40080340203041e8807140c1d41c80f4000f1902400041c000d03148145003c01c40c0d180c41c40009000c80e81001035980c0180e40d0762005100d01410313480340320003100d12040200d13020042c101009501d446000b400901038456400410261241402603c02a180c416036850304241c84211041054000c40340c16000240d000081c03210480c0040100d40f482c0e80281d50f03080982105440d044c100380310340d01c0c10100a00d1010400b4100d070400390b01560040c0c1c0b1480280500550280c1e46001c48001600050410b0300041810842d08501c1c50150070f40080a440c00b1032080124a0182c07082c0354215082d940702c44c00c2c82c503d800c50710384c0306100910b290710888180d05521081e03907044885c6180821100046135011005001107603010303029101c0c9610090440e403421003003020 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 281414964 1250 281413714 281413723
    0x6040b040509010b1306120204110906030112051908070f11100c02040b0303090907110715020c03010f0e0703150e15071b03050409020c07080102041e0503010203010f03030818 77
    0x40388a9a41d40d6500030b280149803031302c0e1036017071095040340501045040c12200d8621403038141d4001c0c46a55a21060b48a00b146501910900070300100226217070345e540c0160f481c0d0a00c145500304c2d024000c0702d524428094031040010074050b00010b11074100402030b540c914a002d0129016074a00c4a41c0e0a00c0a259581801d40c0d90303040c480c0d981e10740c1c03c00100d106010980e1114905284250000d1000700c0707003515144bc032039034803094515281180744d800c8510355040040640110b462000c040380000c0285800040003c40154254000c022808403e503101e02101e00b11580c1c1086900306c0541080170804001c1103500c040c22520000a810418a1200f840c110134290b603211440520030802c021203410034580942d203109044002c922100e50742d002080c0784142d004040c80c0c030ba800b00c0e49249416040000c030003d803500c5c1000310760751070b2210756019810024055000003030f803a802c0041018103040c000d8038100e5042d004c1302003a0900310356003039401e02c0000b800d111000b1605c10303402d402d01c902000b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 281416214 1250 281414964 281414971
    0x50d0f0608120c15010501171b030109060e1501050901050a03110d1e0207050a0f054b0307020d020d08130303030f0e0c120109140601081603030c02010806040b0405 72
    0x1030602d41d912003c000c01030a0480801000350440f050310010401643c010190803a0103100701c1c00300c031036a07903207210314805030085644c02c044603000800080b07500181680700c0c0e0250340d8155501c8540d03690b491301d01602ca011900ca8540015820312402025502803c06804010850305021407080d40b145202c40d10317900f000c0c00c0c5070000f58680c0407810142464101d00002c6c0d0700c11100c15880d0103440d46465039903a01e41d80000f0b00320b0a20780380620500000344880b483c604142ca1411020303003000ca0000741c072428645110820b0300c190340382d0402c030f40600809840c00b40140310040c6003440c40903020040003171081138040c0e80142246807580d002070200070050034030b24000b0b54441d900c2415410018111003200401c02462440c010311060030780b20022f034034000c1c0001161149140005c0c0f50050f40986607564008001c003000280880c940381000c64018161240764045442e00107408620044503415844040c1c003042040e1206009544508a01a40044040c1011483c004100085003c848089 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 281417464 1250 281416214 281416243
    0x914101805060d06030605010b182205070305070f0215010b0d021902030307080a0612020904050c06040f080607031506030203060303070b04060504060e0304060905010302030907030209010b0c0d0906050d0f0608 92
    0x10f04c03081c0100b200d5803255a01410103401c05070704107064203240030001d001c0484001d206040300a42000b6002d0f18400c500d003806010070040c800743c2401e5001401812094500c030001c1000c0310410302c1003d01c001103c0030042d4007814080000e034030b07000c802e25503170740700321030a90850313801b00300005030120030009481c60400c441e4011035030b0b40f07480e02c80240039000141001140c982090000c0216600d00401020a42c3d0105c42900540e10340386030580c07402482840130f0b0380001010a00048111041c242c2504445d2036509940f090354800c01c04500700d0b0705080c251034204000003010711100c0c0c400e030701443e40008054201c070f1a154103504e4040000f4000c6034201c403090344450400c420040c0320f0186c26421802c100c0294242810070a010381118a9406002d0416601000264030314208028100c0159000b8000e5a11940c49903201034240d032041400c8036080c400c80c100507000c0b41c4a2500e40d4101d0b2000c1e41d0707613410181340d42c440c80c0151481c4040209602d44420b00800c888109120811218070403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 281418714 1250 281417464 281417471
    0xa09020a031a01060206010501140a021f060317033105060a06230a050d03120504050a033203090a05120a030b01020f06070c050a050a030f0914101805060d 68
    0x44002d40195094141c100c24219007000004105690708503030003444900b01c4642581d11490700c00822031414441e030440305084854064600b030f0f03090080d0300070b90580b4091100c4100c00040d16144180c98407040c1c400743c46a510010a400c20001402d030303a91020446140003150030115074459a1521005881c0f009010f41d4a8900700284142846803170075486420700341d40003d410b81c5001400281d00c6200f694061103e00fa020703000c051040000c20040d0109a204000300c1c141070824903035500b0342c1c1d80d0890106910081c44100c0030b100038102c80a0000c881e080c1050f46003040c1d103c800c55080504118114410b00398480d0000c0c030140311034004500954410390702ca514045000342602c00c0003340b0f42c1550080390699400100115110b40c0c04213045c18800c805808510701b543c41c0404101018086000d0030400004051380404082c3d000c0c1c1c01645c44031042038480311303003442e0500180050740e40940c4e001d0130200c405018480704021025182114542165104041031542c1e1040341c0680d83d0b50756 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 281419964 1250 281418714 281418743
    0x20a0509010f02210309030c031602030c12030a14091002060405072324040f05040f0204150c0c050d0b06030601090b0618040213180e0c030309090a09020a03 69
    0x3482640346a15035400d200800801c200d10b01c2407074000514840004085100100091b140c500c10401c8a903104a408100c1c1e590f10703410920350842c182401d0b4102d10038000d8108640082c40e00010038204600c0c15405180b5018440b0f2084d0f0301040461140111030209100c00c103240e680703141d180600441290040d05280ca001d144c15800c044294020451540003081103502d0000840041e501d40c01090321810000304110403082c940006050303005040c2a000600800c03441c80c400e41030340c1164800d56061000c41d08401010041c2d0003540281d020035240c07081e8540038a40300d46040c10550740200000010340d0b444c5c1d004074000740200c0c0e030195801c1e41703a0740030b100780344c02c0c104041c4d0300400034008100503c10318130700091034910034405251800040d4410007095556690b0440341040e001c040601c002641d42c44210030080c0c519110401c0082c64041e0303140340d00d0390110301c8030b40c0000014007071450b02030031078100728407254040c1181c00035a0780d0b00d040e200161509a0040003440c001d019220041d079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 281421214 1250 281419964 281419967
    0xb03070b0d0504030314090309010c0206090d080c010c0201020a120209040b060301080c1e0102060601051b0d0e040f0605060406050f190206040c080a030504090915060611011505090a050415020a050901 88
    0x110740d01d50241c5565114410000e4454008c815140e00715400d103404031242c100c900019819004a0340c01c0d60344076840c100c14204120500000f031641e00c0d9100b00030300c400d4841d0101039080f401100b0000021070107190035804c079000554010180618020b2000603020244e902041c49500240c000441980c030002c901d44c0309141030294500080714840b154000740304c00c0d500017500e03994041d10760b0b81808404602100c0e21280b180c400d000d085188000c07940c1f100c1001d03c000f82144558002e03140901c1c03504006a0605080e4041c1c50300307540d070291129290a1030690200d649a008010030b61740d444060265000c8500744c003189000b880341950007801203090074241014544171952081c225588540d01d030200203a00601900c1c01c03101c0861000a0441e03403410000c40003404000e20316401e600d029004108260031810003201303000d1050003040301c03101c82590303042c41001d14007400c4e90050010300080c010302003e412982d4482c4c03203050351101a0031160106ea090f40c0082d1040c6d40030580101b400340303295 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 281422464 1250 281421214 281421221
    0x120c31140f01030c02100203040302060106120c020d081b04150e0603040309031113150e09030c100b06040803030403090e07031e090323070501050105031f0b03070b0d05040303 77
    0xe108000e144160049028001030110541c1d4103100d043c1a1186000034105000b4003c030300e500b11038594259500d182601e4002d4031000c0034005d040215032000704000d440e03401072050450050307940d002080300d4ac0506900350340d8184014814200b040e10203510404600100c00904020142d540074600c000710600300142c4500c1070668500d004050034000c0001107a8400c1c421030440360402da0281002026202069031054046d40180d00181803074104d803949000e110002c001c54990140b1480030780c513500e040b141c0300d101d41c3e00c00c1500c541c000040030030803041a6111640501c0002c0c41585003555600c0c0d9142950000c44060380855105241000b0080342c4100342540304141d8903003000000c0440c40700090750318446c0d00031105d15584271048070030580526032456001e0710744c007080c482d00505240c100e000350340200d0040f500c0f9400c1000018650400140755911051041140c6504401c145403140c024401c4001041c0e052250307000c00940807030381034020101d140c071911b00890145090306014054 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 281423714 1250 281422464 281422469
    0xc12050c040b011403010308030c04170604020f0a150e0d1406070207060201090305180d0215070c0f0317180406150f0c08090f0d05060f1f0308120c31 66
    0x140211384554414070341d04502143d054907440550309459803184142103209001315005184007440300003a6440415000451500c1548200c902030410280392040c0120b20381c0721b229110300105506101c50040f8001c2d19121b0a02c04050041c1c0851080758503010303012081c001086a07141c1116007031141c155414844503001d0840c900092140c03210517640180303980304606c800381810040c54420544c954402d02402c2d0416001000e003010322001e1240c40100b80c0c403044045410007000b01000600120f01e904003400c40350050f034500701c1030a0952240106034460a0352542e50700714680d20b481160780d14892103014002840c0140201500000c01610b10428200f007001400145464040001e05460842d2603a0109640b03250700000b4080224843c074007004001070880c0104001c01c82400200d6401d030340b141000b0000016100120030480441081d00c0c00080c24101b801c00000d400d140f00914100d405c4214200294a0100310152180158808140065035034000380c801001c2d2115854143c0d01 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 281424964 1250 281423714 281423717
    0x16120203040609090b0102010228030e0c0307140d2108240609060c010f0e0c100e040b0d0813080c031204030605070e1909050f0712090c12050c040b01 66
    0xe06030800b00e024162102c1440758060107070700e402007030f1500e9100b9010358101c583c20101c0d01405240210207406500c0f014003e80300004c0c076000304410700010000311004000c0c2c000c0d0103040340a003000094004510b680c810a50402032030340d05030300004e080c803d0f04800780c4070705000740001461444005150b85400f40010080107819040e6030341d580188200001c0c0a14100d45450355500e86a01013030050155a8601082d9440d00407050305050b8aa00803440e440c1104060302c81c00019401001f140040c0c0420810001e8403540b030200c03150510b9482032985010041c2003c02c1c4505036500c980d0194003044038400e5200303020a04000743d02c0208004148118124082c10031003031040b0840740980914400640643e071200003062940c0d0140d9483d50140c40007134070301d4160b4030501c0100c5c1032181c403501c18400601d01d44000520b2020004080034002d030040da807202000031703c00e04100050404841e058a0f590340104000030368888410764190001d200300f028103012120642040308482d5040c05450 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 281426214 1250 281424964 281424967
    0x5030304050118200a150e1005030903030a02030a1805031305010e0112090602090a0f06110c010903240e0d0e150318030c16080105070314071d030316120203 69
    0x400a01e40030001d0107994100c1340a4400c01d5500d000080e030580e03079030707200c41c0401c1e40480d03a1807102039102c5980c04e144541504ca14908a1010300116580d01c02201c51090340d41007480401e80c0c0c0310180e0011600881c1c840c0c404504da0140c2e560500f42000d80442c00c4640d540b0001700f8006500030804041e00400303003424150021151080081c0094808e4610419915652a20401088025416140160005800403255540715080d4030007120843c000c6074049020030110082001002480d400d80800607546d2503807180c030b160385410031590320400c0401040c40740000400c0350140c078490b503059412038400030001a18603400203002500080c1c0b0b410302070802041c00543c401c01e80d40c11603030419032200c041d1040841080070b0318194042c000c190003090054801e1401039009022907070056a040500800590312a90b0041e030454440300c80555100c200310000806007400742602038548030007040802201c488100019095030b010014018840e0500f07404142400b6420950f080c3c03030042c030300046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 281427464 1250 281426214 281426261
    0x130b030103021c1e03120c090602120f0711240301090c0914100215070207030b090607020a030f1808031206120a1e0b0403020c130204060504050d06090807050303040501 74
    0x1082811089840b10b01c000805800c204d04042c400d040b100c092100c1e1200802c10403120f00f4006181f81020310407800148901542c0d008601076540840d01c1074602c1240d81894911280e4a66201042c1150030700d5102c00c20b80361014501003150000c42c00c03403034000451503603581040700d80c50840d81c01030710050400420030001c2c4003901e5026010030240300e049410800354100300384201c4c82d2003401a0b482e030320346400009001101781c001640c0c10035039104036004034040c0e4500340d21941d110790440b060b80040c0c1c000c07031503540405d00400c80b510b4002c0c1c0500c3c0844180044100e2540108043d51101e64154400142d0410040b06101c80a800401c201d4036003440300c1d110104c0702e5940b09040340240003000d084001c49403801442590151895101c0c5840d0424a02420007a4031000700076445400742c9a01d407400b0560702402e1003100c00750f40b15600d4082c2014100000e010800d00f1180c01140c03101c1d80d4007210000326070001d002d015040d1040e001583c4d02e151a203001400d440560201c108020703c0321150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 281428714 1250 281427464 281427473
    0x20708040902090402040f0305010b0108280c1806091508040b19020904050c09031501060923040e240f06010c050c06040920071a070302130b030103021c 67
    0x1114200c0c0c0380d00340c015864a03c2c50300064024480c2d5801034600c1c450b04040001040703010f4004500c2d45000741c8900c09917540c0d00b80d401e010301c52408514002c03030750113030300091580c20140c0c440f030048052458040d40441278a40301c00701c44000d681004001c1002c000c01007150100d20010034240804500d17122001d4182641c982c4404d1074060446a0f5015a824a003841414164103a90070f10714014410f0065007008546144560b1092207018041e009500702c0880c0000c0703121006040350740e10303a66904800d16000c8540001d0803c1d440d0201c40b011000006842551346e4001c4580441908002d001c0074007908040342c000c20700c02e8658400c8c6118040400641c5c2c410081801d500080c01c1c20803c04091044c03030060308021280b458258802e002042c00715140e5810750100d01c100820050b00030411065001001080c0100d60009201c24019005201240c450320045c43e007110440c1000b500303244845040320501115030b0091508090080300410552900b0506140f650003d1442c001c00d01c452a00d0707 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 281429964 1250 281428714 281428717
    0x40f0e0a02101e051c2021160f02010606051b160f0f170d0e011206090b040c05090d0611040f0b1e03010e0601081905090601030312020708 61
    0x14042d22900380001041a0700b802291804110300c00d070f01c000303424284003100c090304a070000851040c02c2c0c00c0f400d40107400d030011889805040800324504018004804d4907030340865000ea0030b100301c40c0c400043d8010600424207601805041c11940c14581441c039001c0042100c0c2c081d20451046a040500070005550031108803030040c0810168008035000c60f4408603c0c10f40a6505e52241e178503000c1c8006400502466040d003510920740c16801100e6440ea0710017a480c01600b81000d9642010216140c1e00d40912048654040117061541c054102d845480c011101c0075070140f580746450307002c48109843c00b446600c4200c03217075003007090410001ca4080b071988200008014003183ea185402052140c0e00c009642c0100918140e0b03113100d903110303884110180c12076030700e12000070303620b054000d02d1000c140c056a050b500d15000000944d954803004562008000d840c1700000448101011001c446501880b44245200002401030307505d035150080941c030380050543c3c1c0031441031100c507002031440300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 281431214 1250 281429964 281429983
    0x2604030503040305190c110307030809100207050d0c0311100203031b0405040603060f051b0f0901031104060f02070f0b09090405070512070e100b0403030c06090606080309040f0e 78
    0xc0d0640d10303651140b5041c0c61501c900000008041480c0310245000c50740b004078640e4440c401c10059409001c881c080c187d54036143c1c0002441c03058103000c1c01d00b540c10700b14915a41007400d403045a00740342da50300105a1680e02c80800f40e500001c0ca14042c420311885103403050703000760302b9a82c284405280b41c10081d1a800b01a05550100d00758055a0007032a03400419140544001441003040941c0d03407401d000104845415410603600f0f081c0007542c0c501a01c028600103040280c011850512504468010b507480104c0450506540380a800102c4c2c6500c405080035081c20b803105e4a000c0103030394003c0c1c90000960f002c0002c1e246003480a1103116418001d507280040701b070314284120b851394903002d8200440d940141d41c00004059080084100004800040f90080302c1800c0107911003804080c40c41a16009140201c0c40800080000a129600039a1914000c03003002952044a03981d1505840340d540c4041d0a0b6800481d039580240740c07602ca07a0094450f00350003085501d0310104680d89461140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 281432464 1250 281431214 281431217
    0x180610030f0b040c0e160801090e0a1410050a1e0b010f0e0d140601061b11150903100615021c050f0f0301080106030606050904020f13021b030307260403 67
    0x5802003010048070042079409003201d1702c1c0c0203040340740c01ba21403001c468412030fa03600040c0c2990000109034141d4842e01c1030b40ca0307642e4080d20503c049a182c01038030a807050b103203182501c43c9000250310780045200305405100b02a40105040c606000f0072500080c01200c0400000d14014451106a80001c1c01c0200000030713052012800c1c1c030660008001d05000400605280c0502c04008800790703020601e24141d480a4943e54070421414064020707003c20240010825408010140c900c0c6c42d02d00c808030303800031000d030342c01d8540b07042e14001c642400113400001c00d8031a11108180190b000803c500303c48000188020f005e072801d071580141d44c0e000c3c43c0c0e0301d40b410300c0b00000b103410301c0712018812101f2059240040556a5071b42e124000d00a0881d4171059441a01e0882e0210f010f00c1c0480e66a8000e940040c200301800c4404400c002da40303c40c0700040038401d5420000018610301c2c10000300c0c81c540003a4040d5849103080c440c09048410305a24000b107008115110002c942c102c40035060b08207070507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 281433714 1250 281432464 281432483
    0x12210f0806040507090302041407020105070f050406051303050d030905060c070809130e0f0a050c1e130605030d0504090501080d021207020415120c060908070506130905180610030f 79
    0x13510019284902c240c0c001a410a0901150201d0b150301844d00c503000d8031240d03000304003581c0d414174100d41c6001408074100c0001c0c020003042011500c40c1c00075000700da084800da5120a540c0c1e0f905c00c4c0c40c0c42500c2c040c01010948030310703012052100a00545520000c0368458924001c84c40c4c0e1404502c2c402d000105205841000c0c0089041e651a44040741d03059504007101e048101054882d941c550010004803520310070704e00404480d05109020303081c15040e11440320000da8448040012141d00c444507610862f45e05d0030005000d41d030412901c2c1194901e0346440360b4850400c60711714161201600070380c800c1c1d4000300d500c41d1807943c0015588603211901c15440d0300c4065a10020703010f44104418100107860b4068081142000094828140e601c11444015120303540c6609840c410341a01c0348039525001a4010000750400700001c0075640b42c917006045046883c1d180120840d00e050b038070107c5891407242c43e080f030104208101c0d0f401c07580c5a003420180d1407641d540c03249841040040107009680 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 281434964 1250 281433714 281433721
    0x1602100509010b180405060c120403030c0e151201080d0c08130806070305090d030e06060d2103060f120b010b0f0c0106080303060a0e04151512210f08060405 69
    0x29400b0340351610004220130791003d5509000a2000402e0303038152107038010100411880e1484c0340c01c03520301400c02e4102048681d80d50302d0980003448607641020030700080138a06401e6a0314a0582190344860b40e00c40d940b0340002c1da003c0914000c0507080340c1010750000100483d0b09070401203901e0b10316841000c055458a00c0c00d4461085461648600c0c0c280c4a684140807401e500750300b00c188500040340469003180c0c407415044007654100ca807104030750f03003083d00441c000341010300c8122030480c000d000c049207500020058124103800d030507108001a6440c2c80c18000c2c1d1900031401c2000f8016540d1030100800c450b154070740c82e10b10610802100c1d081c0000c10820b000018020380b4041d0303035031300000c00c41d55555210705e50712079204032140c6100340c47c00c420104180c500c80c1007507802aa00103561940e20950013510000402801c0360307010030049000340010707110391041c0c80b16031118032804a00f034605191015078440800300b00000c500380f052a43c000321002c1e030f101c020154410760881c1e01160584 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 281436214 1250 281434964 281434981
    0x1030807061107080c0a03080601031401051c051c0e030a050607051602030d02010b0109050a0e0c09030f240a0c0e01030f0f02040303180906060f0c05010b060c0a050616021005 77
    0x103d01c980040a14801140030880c01c50007203410b0600340d000c0e8403410500d560300e00c011001c40307a0743c0000004601d580001889a8107112507280a0040e0409031030a004444d902d80c4c2d40341040b1042d81300d40d030b20520111031008542c49000d1140700c141c1600240140b0125558081d01c907000180b05008020000c1420001ca1440404494105070007074213580b0700040c1d001e00280681048803819000c5080b00500003902d0410b122404102e036001e10045a1540b102c10780c1c900c103036005018641d410301c50240c03022181401070042d40000901c0e100988501c3d031a8034500000d0b00c90040c240c00ae03061411401352081e0382c009204059464003460b0000f864100458403100506210001840d4075201003004003c040c1c000d0000c04488843c2c08840010a6641c070007001a60b03114018140002c01b0300011600903401450007108152007500003058402a0740b020403600d07000000444107a0344020141c0050203c24000a600a05a50190300c814101c041c070180d550740d001c1d40d6400e00d480c0c0c0c840020310b040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 281437464 1250 281436214 281436217
    0x80f071502031605030d050c0910050d0b0907020607020d030b09010b0901110d0c020a0e1005091008101d0d0e1306081b0307061d04020c030d0e071d010308070611 71
    0x700f4030000480c0802d41030a0160352038000b40b002d5880180b13071402040c002e83c2c5080c282c95410070b00600c00e1805a00083c021100c50b00402c0c4e94902e1a6181d05407010300d640e8805a19100f40841d5004101c249042d100007880d00944104a509141c80c1c54129541d80d281c040d511415a107040c80c110b82c0e205910001200c014090b04079102030307401b40340007000c0c501c0d50200f04c2d180c185000319907040545840311070001846006603406031000c4030402040100381003006113140e00c01141940041c3c40c59880c0409418044c0a548180009a480615840708030090142d04180316902008081040381000080c00704014004190720410f0f6141d2030400c484030b05e4001da0050042101a11041c0080c82410b030007000441003214030900460401050043c881c81c0c2c41e040c4900e981008404610410040c0802980034440d00d05440c0001c01134210740741001d004145040d049203008009051904101201d644402d10640145580b45001080400c4c000130540e142e6541180c40040e00100c41c0180c0d0925 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 281438714 1250 281437464 281437477
    0x9021b0708010e1204081005071103040b07020111010203191d1b0102010501060f08040210091d0402100309150b03071701140a06060f0807022401030c080f07150203 72
    0x80384206400400d1500040d0000c0c0c40d03601410045070707003988240c8080360481c0100e00513034034158800160602c84002a070403858210440f820403140510410070001c1c25075216030003030600030200050038011568485186013001c443c100c0214114200102c12103480140224640d15072911032104181c0102e4824407800280103560171a119003d5a40001440000501104d030244d4604400028150302458684104103255501d00795281d40700e608000314544071a001004002c840c041c0810b607104004401007120041d00080b100d00d2a0905c100f1280032111000c0b00d080504201650f4001480e0b60340c000384145070134501080445070300000c203140c000302d0381c01820501d00ea042265a100d130191301c00358415941c103e509200d0f640e01020081620038600c11240041c402d0440d502039a0300c1000c0c80ca0300005e00d841920301e0000c0350450601ca80340301d10b209082e000b0390300c40100100110201c40d1001001850050403445a410102d1522054140715680c0090103401c40081082d1092044900 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 281439964 1250 281438714 281438767
    0x30c080c030d05150103141f151d061615090503190305070804020f01030c1709100b270703091208010504180203120c0c0618130501030203070902 64
    0x12204421031202c4007034003094130000c4d507441e030554602c03a59501c0385c09040805242d170064188540c8491400703540301c0b90354505400303001c024444003240040c05884011080307030b207075950203c201d69800a10400090541c07400d40c031622003046600201c500000c00109095045100403443c1c46800140d000034200080d402015800001505196064903049803240411555810446a039a0a50075540380a003034030080c0d80b14043c40c8061555621036084511b034003a01e49050b881142d001302020710f2064050f5603011070b03a00320220b03108156050344074404901800711100ca1034015442d040054401c4125100504426030f1400151080d00a40109100e240d01a80c40380d480801c000d4020070b080300030f011361403280303080034800008401000750b0280b0b19500100501840d88541d440300005500c03500080b0b80b40d005400355803055a6500340038118a010070f004902201c94450704014800500d000b540c40028503202c01840541c4001940c0c100f0b48441e40f00040c0e441c0c0c40545c04890100c084400b200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 281441214 1250 281439964 281439967
    0x61b03030f01061d0102100c050c010606050408100501120201030b060403080325030207020306220c080f01060f03110d0312050a06140303070b130c0b0414100306030b04030c080c03 79
    0x1056107407812494100c03140c0343d5030b4100d0740480d046052540070714043c3c140d0040e4400f26540b03404040c243d10480100100381400b500d85030101160b03a003074603000da0041c000300d030020908020312201808640350280300000100280c0d81003461110710202e800401034105031b560182d40f01c079515514221f801445c0c116483c0c5032646044503104007502c807004451030044810000304801c5902034002d4038074459004000d0000caa640390b842039210034280304403210200c40c2660402c0071a41001d0034034050203a05005c0d0000c0c440700207043d42991056400721680302580c041c00c1000c1410750b000400032071012540d500b01180281030032900644855400718420f1314150511040c0382c0f00b0350000c801c8039010024120056401801c06440b40588940582001c80f1640094003200030b600340d441019101b250310010040d15050b01c04990741154102081ca0410303805801f074507103880c900c8a981d50b00145018410503080da41c980503024401340006003840720410302c3d142000180000d40740200781c101c0803039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 281442464 1250 281441214 281441221
    0x230901020a0b01151805010210091509050a0c0609030b1603020f0a05090915010903020f040e1c4518060302090604090206070f150f09020319030905061b0303 69
    0x291090342031104c0c0710b00401e011090f03220f1158a4000401d040f0380c016005828003007811800f070000b07428042021541d8960364400902410803520844450b54040c0d070042030000c9803840c141240b05d91366042801808180c1201708001f0301110160340d4450210b155030145e00024840c160068000c20420352181d02c3d01240c6025030540c00b10140c0b019000c12520700400342c54030f00002d08010040e0a0103400109400f0060000d4101261403440d001001380c40000d106800c44450b50501c26603107500036105241e283c0c0c0141003944000b04010107074103840b02c141d0846a03069140b464109803035443c9040a961440b00b9000360058880700004c02065044503455580c0941c030000030034850000300d00ca91070100200d8100c2c10144074040c1510740c00b6081c68503004083e160444003440350340080f9099003540d80c1c0c0107004022401507001d02640d510340455110407d104150030018005600c00280755046a0400481c1c0e1114502080394000d0310102d82c1e4250911035400341c5162100b805c045880000f041c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 281443714 1250 281442464 281442479
    0xa030b0403021608032709010b030105100f050702040c020a0c0605030907080102070807020d02130e150906100e060303070204021902010e030f030f0612061602010b01230901020a0b01 80
    0x16511491180d4203442c1108605941e2104901580c0116003050b44140040ba002082c1074803450764080d40f40300400590380705000010580d0000344c110321241107010004010760700304103540707195511082c24035102c145a5008010301340d0003410406031055480d504180e241600912160011070b0304100390202454441a015100c4c1d80f056412041c43e1050900004803c101803003598141d0f60b10401d124680035182d000c0180c2841402803e90b40082c0c48289a8100c078050700c65020f280600c1d4005d00024001401c0400440758006c00751ba01580105080010980c10602d052080d2855058800003e40f100c4011034030b18014102d000350002d100042940201c116440ba1402c0508a54000e01103d20307042d030b070b003034980c0102c0744118203000044c008103030000600340541d40d101303802134030303120090034011141c5141010607901106940c00300030608204031f0303081c010348510341c200782850313241750300340c0c8683c2d0328031041402510803041c1011800030200d038030a200300103690b80c010b0080b02c51541c54452 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 281444964 1250 281443714 281443733
    0x702010c02040f090302150a06050108180106170c0a0f0b09040906060939210b0a06030507090918080c010908030702160621050a0b030303131a0903040b0d06050a03 72
    0x1640d0401602400050610002da0149d003090310b0041c0c0d03c8002c1a1035050240c607410010200000095407940c502144001041e0608030ac00440603006208819107442071000050b2190012034546250305401d001034010b0703100721900c080e801c1d14001030060003410b0038001003031035400000b03019061002c8035070b500e2401c90740502c3d010790f041c400521400440e10480c808960f0000c2c0e0001045143c03810b0103001d19500040d550b14401c000380414890401c1000482400250308160007084d031b5001400059984824050040c203900e0718208030080f203c1c1c0406543c1c40000e80d00504070701001420185040c020b400c2001c05943c0f01b04034985a0429020181d01c03000d03504031400385545008400100f45d0310031604000c000c8a51411a1a0030728080c140e079014000051246840c01d4580b984c0403c0c41d201000110700c01c801c5140310000c201450b16040a02450312082c81812010450600280000201c2120b04271908413040e6030340d0342034450b103007000352030f06a108a81c8049a1540081480007098 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 281446214 1250 281444964 281444983
    0xb130519091a210f120307020105060a0f05060904020d06032603100302100e0a030309170a17091207030b041a09060412120e07030204200702010c02040f090302 70
    0x4100344501410700c903a141100303440340400350b4080e2a101559000b40c4520001810081075007068131075000486240900c0c0003600540c0c403a10990000400609940c21302c10140c00800c00c0743c0c41702d145864520001102000d900031507124100020f6541a940e6850381126190400740105014a41da0b82c00c0170540141c1800e104011602142c0300940b18031081c0303007101d2080380c942c003949030f405042d40c003404609280e440b420014020507812042e2031307554010400c00214031a64680c0744150503c030403141601c090540030302440d44940d45150020703141c0c0380302c60a5001002d0314207444001340d20004110080d80140c0c00618040c2e08008020310085950451040380200c000180c800c08441c0c08060902e0121349000385c0317401000c04280001c1004014810707072082840c0ca14000340c840c480010854550440c02e868a030f12202d41007086040a002e0000f85030002c0400c203002e4007400e0f01c41c1002d840340c0e02c00241040015103d200131540c407988664807510200d8070400155049207406591001d00c0c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 281447464 1250 281446214 281446229
    0x19060e010f0914010e0a0203130803160f05040303170705130b040e0601090302061804110a02010905060703020a0f0e030703060c02010504031418040902041d2a0a0b130519 75
    0xc040f0140040e01c0c1540141280c00d00711103c011540c41010001c002c0d0070280604510809ca118800c02044030440658081d514010380580480d1134410003401e80000214001c003031050078002040803d4009a564122481a500350200390340c3d0404100c502e031059800144020131021000b01d403080307021004e00240c490701c111400e800e440c0d8900544080c105448000d42c031040412240906001e541003848240c41e001c1c2c1b01180e01d0b494007484103a980c02c2511034200613075550340d02d48188581040312a4206178030f81400c51030702041d11002410780da00c1801110900082004601158074200401401541c104c002040166400d1400038041c000c2075400740c0008440100744040b0200e0b0404440c0d5a205006100900c1d207406000c0c00060891703030030140c2c0e1080d61481e2080e0980c41003800d1b40020124040500800b00d51a01d000d40030b910041043e00004d40007076104c01d186e4540c890300b08242d9003100100c64940c00004000c0006440a81029400240351601c00303c030002c440c000f0005a980c1c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 281448714 1250 281447464 281447471
    0x218090a05010c0914011d0a18050a02180108091002040303090e06030c01020304051e09040809180105030a0b0a0e010f0b010917030430050a02010801090b030619060e010f09 76
    0x14400032145034129003d202c002220003917840b12150f002d0740c104400c031600000c0040d500b4154400042c008040c95212404028003000d6000300c1c1a090700c103255101070791101c110b040050340c69030000444441c5c500301c4d05202c03680b00461220351b0108004828100c0800003955142c3d16031800904400f82480b070709180d0101000813640c0c524020450958068040c3c0c025800c162070081005580303201c0d80401340080840c008200c1c0346490f0043d03814429070044048555a440020501c55011262035400c423091498030b00500c01750f9000b02e45048032582000ba41e459075140c1b80346040052000c00f000c0743d501e62804681e0b416144498001c8200d0b890240c80d0150300c1c13035484107401d44d18200b084210749540c04c00c2000703010642844402201308403224500f20b10b20078a03141c1c22105c50714100c405607000d074020002c01003190b0b40954240d002d001d00b91810301c43c5015000c00b182d505c54019010250b179501d84180d4203406222036009100908407003080901c41d581d180014401080e40f8010807201c10304 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 281449964 1250 281448714 281448731
    0x4030e010306050f011e090315061406070506010b0a110d030b03070504020a0912051e10050105101b0201030b04090b01030501050c0a080103120c0c090203060330070218090a0501 78
    0xe0a042410b80c03030b401038490020030303258140110450b071b0720b900000040c001004000700125100c08042006084500b8000542c2810911082000d00c4000d441c1032240c0e1040040c900001c1d00440d4140c11a400042800e032609006181510075a050031584c0e8454400c945414082952542010a14846c00d0302030300c1c07105444a05000603071158100700c001084004400b007003111711100340c0c80c41c0d1070b00271019140c191060300d027040b4148028055404140e4408103012501d040503101c2c072401054100ca41400c0b2004a000280481c11122000b01143c08108404e10959000760090482c4420003031040103a4451845c3c5000a6002808195401c2d1700c1c00e40054103a0400c0e000300c031150f8415440e1095203a2840d505e411250084603508001c01c0312074420200016a0342540501400c030a260150700c0e498450241450042c41c40c460310401078a010054642c07a58480c02091805400580c482d03840d00d00d80041042d00c0c5041c489024800d00c41d004001507050081042d1100901c520003e210015 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 281451214 1250 281449964 281449969
    0xf060a06030216020d1704030804080f03040f1511071701050603030406080c0f0c0102030c040603200a030e010207080d0510080c0102030d050411150a0210020f030a0b0d0b04030e01030605 82
    0x9030451a038103800c2080f00f85025103040007482602c40e100e4520329102d48410300c80700c170154220364401c0700d1030003010034240041401440140d0305481e0720b00c021030130145490741d0b00d503160000e03102e2110003004018039140100c2c4200d0f42014004116411103151954031580b02802801031a02c14056500e0706e40031030840d00c1e01000300d500700c9a050352141080d0701c40800c1e049040c0e1040306401030800c020042801080000c2c000380d44a0409890030580300c61922801a00740c80000201c0950030a0f441d941d07080c01c1440b83c060f91142071241c60000740030103070f10411710300a10900c10054004040451107222465582d003103c1d00c0740d4070304902e2a0100c2c0e034400e0001c0e501c0752004525030142c0c100748030790102503007950702192307000d401040114030410400e40416401c560300102c0300d9100d80001003041403103030100320714203108511000861404802c111005030300c0c00b01400c00c2d0101030712801c8500903542d80f007011603241a04901240c0c0d8600b402d01e80900400459814140400d01f0102c00041e1031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 281452464 1250 281451214 281451217
    0x20301030f020108180609070e0a0c0f030e070f141207030321020d0c020a20010801030f06140a060305150f0a0b1f050301090e0a0503120603070e0f060a060302 70
    0x22540503005903422a1142d0056035a00300081050b6040c40c8042c1c180314200d2000c0100303e000f4000c64021b480d20f00e04103c00c6020321440103203508a5103046c5050a8001c0d5845142210405040d150000e0144104c1005c0c03420100d265214018120ba00304000c514860816100003210908541c44c02c9080540c0c600c241d241d0741c16200240104901072003281a01e21008840400e030f04664800500d0140182d200c001126814003840f00107a201c003a0388801c001c1a41c0c40441c040c0014288002d00f5105100001c10710001408010055940b180c00c0b5402c101d040e4000360101c600030260035000349424401040200100e00c4281c07098400c92600071000c1015107038250103071100403940d0201d5555a031506028001d0211101d40104440700c0801c0010400c00c0c101c0410310700c0381e640307603580c0d45001031000c02d403100b0549038003850300203c42400c0003440000403503500105130300d00c1e16416035a41c00000d0819001e9403000c03807407040c1c98041044401e0020981489200201c800310b0303543d502d03510110200d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 281453714 1250 281452464 281452469
    0x708160e0a090b070507030302040302040507030e0c09010f0308091f1218020607330e070503061e1e15190e061507020303071202060c1330050d0909020301 68
    0x4410320f4085080031780b190005051b418024107000d45481c2d6243d012804448045512000203650b40c144040300c8242032101b8100e03011304840842065040a40f6804038840a1000a10140e0001203202d02d41d26922028044040000c00c4400c210302c0c4071002a181c80d2500011008140c50b00100f04020b0794954010034100f038010300f542e0306240c01035444184250300a1542c40c64064461170078810b180c100c1c01210609111400046813035540040340b40e1828105400881c481d802c441d08001650500c00d01281041c0c00c1da4021980640781d00e4240320019040260014410600d2020051407019890001d038052500f600c8100489103083e81d242c001140502400f07001c0090f12000c5070032480c059020b04400c104044401c3c0c90f2000d1640001c1c6103501200c8100c802d01884e1070951038960301030141c0c0343d224030130400305803030300e8040b0044400a5055004040b07210b6600400c10f00238101ca00c000241c5c1501c200303014810303507410741040d503a10b41444142c84001425403801003100d40c01070007a20304 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 281454964 1250 281453714 281453723
    0x30501170106060e060a201015180207083f090c060a2a0c0f080a06090c030206120f01090605010504050d0515011203140309030306120708160e0a09 65
    0x180401d81c841081810392108040804002403000903490f00e2000d64041313000021918014580040b03510712040527110300f6040f94030b005010940c1000182d052988000c02829003c500581c2c2d60400c1c40c00a10901400340040c50900c0c10740d69015030031380034000d010840407082001c4402c4a2814616200e003460844107100560045200e28056040c01409060703003900301c1c14020300e26015a0340c2c0040c144641101010301c0e02d040d10f80881840002c501010250900c0c0a81440c01030502e002e055882c024500020070003a80c0f080c4920034008000440300265500610503660303400390138080a60004180e8604c0551600c08000003030940b0184119000c403541a1111410140b41c1020031001d10000d03c4261a40d01401075540d40200d40414198003070440058121036007031036402c00400800d02c401c2c5184002000304203102640400005072540031b103044035881c0b0b401407030302c42090800d41c081c1e201c0c43c51403203880c60001c101007003450b00c134042d5403514285038880e513143c124402c10b60704081d170040d0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 281456214 1250 281454964 281454977
    0x30e0406031208060604081f0b0102010908041202030a0605010b0a03051008070b0c010213150206010f03020d020405181209120d080c030c1c02090f0406150f0e0d0303050117010606 79
    0x5095030f014488840e8407210007802c2a00f0503648009003420a150050140e802c900b400c00c0c1040c00c8a090700c154580740c0000e1008001c14200b0341e0b903202142c883d6020307082241c0804c0f444802150750801000f840b55a00c040244420f5954412080e00b5400c003032103905c0404d0521001450f07030340840d0407180482c1c402030b0061901d42d203003104001032903000115501040d50204400701414002d40450001848000f01102d07507404194002810408181c0001c906184031400410159989001c2c5420694045800007056150078040c2a407036000c6070348030111030060100111980c02d80b1005850032103403e0b070b045801c04c1406008180c890a554a07081c0224004c40c01043c05400c2200c045c42d44254142c2c0d185180c00050349000e2408104d420111840c0f54002508036a2070400891803242c0c0d400c152000d014650908107500303958850101d501c001c01496038100518944541341c0b0300e0b11400042c1500c2c070b07481858100180640000d00071103440058030302220f040c50384140320780802c0310340d9a82c811 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 281457464 1250 281456214 281456243
    0x3010e0612100c17070207081e1b011101050403030b0406050105120406090c0f090501061d030c01030b0a0302040906050f01050d080a031104240905010c021309021c0303020403030e040603 82
    0x140010102e60b00f007041000b0f5071140b6107040c8110700d020503010341d50680050901c1803a020040e840c14551001c2e80703040da52102e03601400180c000175400840f08500881030045920071004a40500201c040d905003507082c9014882810340650260103203400540d0140f107801c0e140e40041d900c40c4a9032010103003606001c00020301050103644802401480ac1d8110300109a450516080c280100e0708010950341c0c0e100010080c10703410850803c86207142191242d8022a043c2c00a9102c01d214414035041c9600c99000000540c6d460704140c001d15030080042010800c0303070034158018a400c071070505056100d9000401c040c909101c010342d8a0707a05c00f144600d0245104400c83c09040c583c0950113502a007400f0200b1034540c104103294402e410000302c64040740610800900345490795000c0341c140007666481c5800743e01c41c94240c00d00390100c103030040b405221031f10119913800f1010b01c0784801256207403841000c1542c960001d0013200d000f036607a42d401d00301140412049071902c1c84001d0a180303401144 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 281458714 1250 281457464 281457493
    0x503040509100503060403080906070903081207020717100c020c0d110a24021203090312250804060f1404060903200c0108090307030912080403080d0203010e0612 71
    0xc2075101e450042c11000e0580e0311000320b444d007071096400b10040740100003000b00c80201000342031f40c0040b55151256129185460300301142c8540d140c0030712940c1c084400206014003c01c00d036401030007035030908661441c02001c066155100014080540340c207104034103800358400518a601c261004258003060b011907070b5440303200410200142d800284c03e03c3c0000b42d01c2e85000b880a1000e20400c03100c441e10304120740080c06c2c0104aa40034880344024028400c20003400420740d0b10801065401c1c10f1281c9542c01a5a0260010301402e10295038003659010100d0b40030101d1406588030703220900c40e180100c40d41d1810b403490f0303801c0710a045801350001008103902c0e81158400d64068100031800101e03000e80412101e5010b4102c0b04190301542c050b8000d56808420340d6030110040000d141411502c4d50001d10b0300d00d00744110b010a950604c2881c0500810b80111001103a1001065581c0e0000c2c000720406500b09200780521480010300040650415529514804001074060b10381140e10325607 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 281459964 1250 281458714 281458729
    0x405030c011b0b04060902041407080a021b0a0f1403180d0812150f01030902062b0c170a020c0703030f090e010803180102071208030717070305011e0305030405 70
    0x811900402c02c0c6005800300e00b20b520b2281c05030340070b11004186160301d40140010717500629680e070141c0803d0020440f045601100e866040500b20b00c0c0035035542800c207030b109040201d240340d030805809061040d2007009240808900c0061255615080089a14010343d48030b00440010011403031440441a100e0310780000c0c10803202d4890703a00719090034800403424210500c1182c1c0b0803079414002c0c0b4003135900d2034181c503012701c2580c003480d0138054080c0756800304010b800341025000f21071869201c240d040202613201c94075440d0f200d00d001c01a038a03e07002c004000c05017500e1000395250099011400401141c000c42d400481514001e002e01c500d035580c11901040320801c0402004944140800c649180b400355134001e00c8060b0003142c58252119040034035140103a44c4505640c800b50081009010055804e460190060070658695031843c00594000b010010300d00c4001684008002040d501540114140c030480c14000f400100040c0c00c1e0b601d41c00c0107000240c819801404100824640206c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 281461214 1250 281459964 281459987
    0x30305030c07240903020c040c05040e0402010306031a062b120912060209040c091d09150108060f060301110412050f12070b0c36030d02071a0405030c01 67
    0x6043c001c01407a00301c50034120840704540000300d40c41e02000030915504100034050400111000c2086480501001c0c2540c45940310b03c20103c4996000035065a0281e40070320000c640120403e01e040580840c1402a16001c40700c15215071105543c0544400f120300c006007550030400089440441700c0c3d112101081002e00ca60002c000c9900740c04146503240d01c51022201d882500d001da2154501c3c02040140c1d84003104440c1085a0b00d2400c02550701075142c04000001240c06107a107544070700344103c1c00d040100c07000c11540a000e40000407018400903505108141e0700b01d110a150711150105400e99808090000c0200001e0000b44100904500080d0109216104403440c0d800c40484031410a0a18442c820341454040794940912841100465001000d60704041c07900220145100e1568242201801c3c0032948502c3c00c848403658541088280d41c00038101d401034246410000c4d40d0f001c0b98010f41c0b402c5182c0d01c41c0c1d07a040307900e034406540568130010003802d45c0c0a240c0c00111a28208803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 281462464 1250 281461214 281461223
    0x14070f1203110c1504090b060901050403080c071e0e0f0f160909060308030f01080a02090f1f14040c0815011809060b0315030c030a060513021201140105030601030305030c07 76
    0x28042921a5a1410007056443e0900c5130101d48540c6402c8008045410107031a450150908100c41030550f80c0c0001103d0507a070b07105120766141d4414101c5e5902e417070b4250700a0400c0b0b0070001c5e501030300c0f8401c03a041230b800c032003c0005039a029914000622045c110903200301e64084000c001041100c4010b004050841c1241c1c40c0100c1a1543d80d00307404103aa01c0ca500c01d440c03c01c070004c244014844000089070150146500408138941183d02140840c5801401052944515400b041044644a4810504041c1409100c00d03040d2035900d819400c00d080c440030762040d4500502c941800e800740b007040380326182401102c0c510b5811031006544000341140f4840202840b448081500229881520042d00c10440c0c8180c50740381240303503608802c1090b4200c0b846544803c5080340314cc1c0d07001440788851035004001003000d4139007102a240b80c0e010684000e41c4200402e400f0009440158807002c80a007980000814990f41d6205040d1038030707000c0c003001e400036802f0000a4106002c9100411005215 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 281463714 1250 281462464 281462473
    0x9090c0f090702010b03031b010608070f150509060d0b01030b15030a09050c06070f110103020f0a140d0f020304060b060304120503060604030b0405150a060510120e01020714070f120311 81
    0x6a001a086034000c003400014234041d60f807980300e464400d1080d0f80280c46080d0042c0015804e1242c02c0d0809581407144001c000c00720707248200c4051191003601c144a001a10340e644500300d200240c400783c00c7d003281c0e40f0300280c60080c2c05540c51604414140300568101c0d0b00c0380c50342c3c581013191800b50154210507226481103000c40681038641030000d0034030500603402409130030f80300c1c07401c08009a401c1e40d689040600602410030f048100100300c9049501504140b070321888040200912401403001c061599031030545111035a8046800640c8241e1041034108a0b0010324020070407d0700081d035018280402e442c1c1c44c404820b01903401035400000081000b4202aa281d0300c100c05030600300d0301242c5a030040c001044d01c020903070400d250004a108010702486080c200824a02042d02c030f88181003003d04005c031b41a00b07510360711061550101200075595500e80d030604081484500540360030328801d800340040d40d10802c601c0c81040c1e907460414070000c02e005850881e04030142c504444064006d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 281464964 1250 281463714 281463731
    0x24040f060e01030b0a0e1204060c050a05030c010c020c06040608070c030306081b03062410050409050106031d0102090901030807081606150806061c1407090b09090c0f09070201 77
    0x5000745094000c610601d441480c03884d1400e610b905540e91020f40512603400b003d104d41c000014a001e840076a90f8030304c0d21108406044c10030516192800e0f001070102d003c00203400942c03050640000c02141c40c4ca0f000c54502203006400d00100d1312030340c81010001030303000d00441e030711510600c121422240030303180c04200d1507240c0b00650b0a0070340c0b0741311565103202d0412901885081c240141c80d8072040050210030b15140c100d013040045c00621060f40d00c502882d2120b5003200b8012019034015040b00d0008000960710b460006e8010240c603190b0000217005200300c1c00d450001402104c0d40203c01604010841c0d01e180d03942c0840b0781003450b044512620510082000841c00400001d4840c00b892004c00c00c1c07180301d11885041780064000c0303507150304814108509501c07094003c0f00ca5200d25039040d4010b00450408054903404081001c00500550800264805468114401c442d800f00c0c0d020b26180c64450090340da0310027121020707400140b5048003604a10344414565400340083c0008130b8200c0c0d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 281466214 1250 281464964 281464979
    0x70305092202190305090606011b06051509061518060408010903120e032b14070509090f07021902010e03030f0c161802131a0a0824040f06 61
    0x400000075a00640c0d400704808400c2002019044884161030504203d1410103078581c0c0e4032504003c0c0018140031000d041100d010210f400202c40c9160401d1041169041140844d800d21414003111446495075001007851340c588600c910b007124048522162404220708859111038150f41541c96220390140000034254000b800f843d0034030f138403c1c0c1d6030b942c0059a02d1090f500700c0c0c0e83c030403414005e81d206008501c8003170141154203074501c508000030080c04000c94003807400740040040c80d007501440c1000f802405a082009040d503c842140c140e4600d0b130350300b0000c0c3c9130704204070340300c5c1d0069002d90350182e441444911f880c031581d8010315041444480403c082403955000310790305441c81c0d800099611303200b1410f01903e0042405880c1815002c1d00e00340d1800c58490741310b43d90144050340081e0340200c500b1400049030041c2024400d0500b0361054848403809a00400c0c410004582000c0000b0b825001c0324a03105da10301d440c1087c01c60203c2c051800e11005240303a080301011156aa49c2c08200e15 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 281467464 1250 281466214 281466259
    0xb1c05070b0a0f0306080c03030906070c0504021b010b010215180f03031003062720031009030e090705190216121406040c090203090102070b04060b01111207030509 72
    0x440543c0ca80d0071402c0400c04004003240c00030b500550305030b0800a100030817507401100b02c4214413012550303261070f040d5505007960000d505600207680700340700050451030484002c0e0a10241d964840003004814030100042e030f140c0c40c0e0051102c03130100018001840143d0381620094170243c244084a080c420003080c2c8624551080d00d4081c800001004104100600d1707000305d860001c4910041030b502410710b58401c801a4605034020480c40c00d8081e0b0806451448840b03000b600001011180b04654141c1010018a41d40c0c1042c0c0c0024200800d003003080c00d0054500c0c1c01601c207503481514140c858400c7d01401841c4070070001c110701590381c07000c40c04441356018201924a25040e40c141212a00c2c102e4040902d8085c9d4454a4100d1001c020100e40704c2d0100000710f9102440250b44ca9945200050084c4605a00240050920300510043c400e495000001a00081c3c80300b440d070a4055102503610445252078021485007044001c0000c0e00c100040c2c4201c9001030140d800c0070f1814003400132070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 281468714 1250 281467464 281467477
    0x917070302130e0d080a020732120a030207021c2301050f04060b0109030506011e0e010608040201120f0c0c060605060906070f050f030a050706050f092113080105060a05040b1c05070b 80
    0xd0403182c140b001151140c0156002e0880b10a00050412b00c5020302101c1d903078001c02c040f613801c2c5503000c114a410740d200c44040ca05030044842c1009108822450903a6410603044c2c41c030401400d078003c0450080505205039030090841d098250301640d119901c5030054008611202d0400450b091b0010000d5030800080d4060100c1c145502d20340c4851050348030407039400c0c0d44480032a0007210010810944c11104450b0466028039007116012600c40c424405003111204111070f451900e480c049101e940136010009080c4100340c1480f402d503896080060b9405002141503001000f04840000158a0812106043c0c40380341540c401c0d4140741a09402c40c1c004250820224100040d0711042011a2203201c0e030000084c1c7c07240d04c0908190183c150703120400d0305500806041000305241c01982c00c0255040400c9102c6200f26642d01c844102d80039200a0300c1c1e103805141c02c040045014601802166110308026001e0b140f00d10f604080e185049040e150141ca0900a080b0046420b00d80c80004004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 281469964 1250 281468714 281468753
    0x30909100b0a0507060b01020a0c14010323180609070603020d09080a11010606140406080403021f06081009080f0703030b040504030305040308090d02030301150917070302130e0d080a0207 82
    0x44584d4903040020a030340c880503802d03045400014103000001c400101000507030303d0715100002c1000d01100143d00030701c00301244d0303d4410390201c824400c4042c4002401c0c03040c10316039180c0d10202d140300e095545e10b44042d1800e000ea40c0105106200c924807950141c003044020301404074003034260352182403082c1d00207800b8500144203944d10080507502405054000d22691508840302100306c41001524000e0740035103001c0244070800f20b4103051003009031302e00e414030900d112000201c504048000070441c43c4035011b018000d82185049030380c214414116442d4006004515203a0402040c285540c04880c045091580d1a91038031003e8840340b18540c070032440f0382c40000e11307410142000351806400400c107800651200352490307000c9902209036030448284600c040840e0240110940f5142c4407034008039805280c40c51803409020b0005001d4085078000d03142481c04480701e0000c1c4081d114104000e1a00750f00180002c041c0c01d100344e20640e80b00c40078480c01410004a81d40c1c4211954041d0043c00 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 281471214 1250 281469964 281469967
    0x91103010e03030c09180a06052706010e032d0d0207081b12010203010f051f0f360f080a0309050603270c01030609020a1b0309080f150c040602030909100b0a05 70
    0x272060401e560350303022846070032403e0544980b144400140300ca030014030142c100920001d0f00089a2020400c1842c19041002e0740e00342d06018069900c440d25480210100520510800c0c3c004030b8004205c02c41902c0d203440150004161520560228080041a07250014004942000c2010081c405140a05200030328103556924102c100000a002c0f0b0300f4080c0841d80780d58003402c2c6160041c440208001044c1072000c82d00c06c50b150800118010780380780b25185982d22280c2d0282c80c01c940f511409031b03100442c1c020341486e107850750f2640d5100e64038001008074062020910842ca001c40180d5481000303040001c00100032030001540405c00107181081a84c00312071081101e6030540a103401a25920500314140b0704d42150050040e10062101703c2072101c0b1406034014184a0b200000203040c0d84812a000703415228102559500350406481080b0b6414001c165001e9139074080b2011101281d00540c10306400f6000c211424002406140490001020010300680984041c22600e0312545410307 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 281472464 1250 281471214 281471219
    0x90e130b0f060f100f031119052505150a110c011b300e060c040608010e070c030305100312090303090e040812090f03030a091103010e03030c09180a06 66
    0x483c40300b42014032240701d5242003124502c0e0b15481520480140c4561501290518084000e21074074420144c1d0410b20104200301c81d46140d4204006003498400544458144040e04450220942042e00d0007400f6800c050103021030281c9070410150401040c040000b43d000008012500d1a480008002100c0c0d4403800741d045803288401c4011624441810030404102040d0300b504401020102c64003059420f80b254a0001d4001ea0302a010107042407040b5880341c14802c0461000303400074403a000002e80008000700e0900c5181d80d10500070825600e819054010340c4d50305801401c0002e007154001404403a00001140c02864135031b4440c1a140c0b15042d00c5415070800030021000c68020780a9800003006000015500e10200e0f50007a9408210440c0c40d10ba2400c542c4c203002210081d404248408010704c031500381d0342c0c0c2c003001801d80308500781c828807003080e404c0c507003683d0850700c0360604e0b50030134400160380b0744c1d40d10028444d90340c00900c11030401042190503a40c440094820041260741c2d080103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 281473714 1250 281472464 281472469
    0x5190e03060709080705041505100e193f0b090c0a030c0311010210060305010204050a090e0a0308070c0b0c12090f0a02130f0e01050402010206070e01090e130b0f06 72
    0x42c1d0080803e107000314250b4145030405584292074840d1602455a44000034804c40103804400081c010080c9544c0c80e4680d080c1000f080d05620643d680d20414107020340103284000d0025180403100d141516000354400740701100c440158148c0b9109403e042000003031031004107044240b5a49106100c0c1500e94104100454a041090301015000e211000001d001250071904104100d81e440050344030100c020f200100d090006902010740b00e03e040c4a008010084190080c01c01e5500035504084000e070340f40d44402c10758480340e004140c00e401041080c80424490920316600115a040a480314030040da0741400b80c01d0112048006000089017031400701200d450f00540207000880180f6046803094522030312950200302c001e104804440c0d1a40100107142c00240003035001d0f00c420001d420888140f58081c00c800c4508a006011b090001001d150003034429600400060b9540640c150514451548806000d86680301e0540303403c140c40005954041418414100164814641d0602805 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 281474820 1106 281473714 281473723
    0x8030307020d020c0103050606030f0c09030d091401050901090e07121a01090e10050105030430090e0f0a05130818190b091005190e03 59
    0x100040c0075000304520035149080d8080d10b08008042004508032031045614a921040900c0450000d8441c07000c001c1d072044107800c07028600b01400c40000c0c034004540590070000750302d214040c4600003c03000b58072041070084c240716040240b440d0000c1c120001600805008a40d2400025800743c030807009281c202001c0c000421001e00c01c5850b4884060695002d0703070204d4070486d8000b610310310841d8003502c181803804107101d517941071000441c0d181e4000f6109440c280104000314500f660440b84064055100c040409030080c03000c400503001c0440c90344000000300c0c1d09020131805101c8820140d91024045034001000e030b03500a5410100506190041c10040f800b140107091a030148a00721119101150380d0502d458000ca05034804a131180034440301c49030309000b0300285082c400084c20f05c003240ca0818505046400810440c64801e11100c2c00024980401000f0141014017 = true := by decide +kernel

theorem cover : BRFrame.Cov 281294964 281474820 := by
  have h0 := BRFrame.cov_init 281294964
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 281294964 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 281294964 ≤ n) (h2 : n < 281474820) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
