-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4806
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:47:20.64478+00:00
-- url     : https://prove2.me/submissions/13f645f3-ec4d-4a7b-942a-02817e40b492

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 864208633 ≤ n < 864388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 864209883 1250 864208633 864208649
    0x180308070302030304030e0f0d020405070905040e010f050708010b030a090807120801060815060f0a020a020a0906060206070305010302031b01110d030e0606090f011202010509130c090e0601050a03021c06 89
    0x40741007900c0c02600040c4240181400303a40e511182348030b25911140d2000c0e8035601907500044903240c0781c40031550300100350401a04281441c51418072610305602c682e10910740c004c1e0801a17500e8480003102d81410a2041105540d014001306083c202141e201070051071007403c074146000065074030440c0395440c120041011078010401003000e1500000844c2d40003d0a000012140c3c070b103500007400500509c206005000030110302010700d030b402046948402600100071000250b40c03840c2c00c00141c4001c3c080c502c011301031880444c1029001c0c1c001c50341a643c1c010b001c0c000c40c0f0b41c910f6507500b0240d600d880e0325040001003140440c3e044000c0c0f02d039028900d243e81d404519541056089407400368046c007410b0240d5080f0b010002000403211616042d9000c6000a0443c407a071800101c0b800d01a061145500c00c491015041d800b0310240e101c1541300302e01d80c8980d040e081c0d65010350030f07507070310204c410b140170902c1003000340c078640d119174001c00340c1c0013260071503518890644030343c202190300b83c1d045500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 864211133 1250 864209883 864209887
    0x90213180b1806100804020406030c0e09010b09041e0314040b0c2103070c1a180609070602120d11070c030b0c0a1d010c1a0a0b030a1218030807030203 66
    0x11414000240b0141c0c0404086415042c1400404640841e0700c0410750b1007040384500c0482c046503a5500f02030015500b292404498139102d103160560005d094403450101e6207801100066810701101d501e04c500e400c0350100c4804503040b884400707608804a000c508101d51500540440450325020b0700240140300485034548010900043c640360340c0158220070107152003480c110310010201102d40c042c0c102d00e4403003411038440c600352110381e03100c0d40714800d00407461080210146003d680f041501031014115562601e0306030080307440d6036081c054003006802c49207009882c008141c0c01410140004040010014200e04002072a500035110883d10072282d92010414084072035081c030b400890341e800b100d00d4051040e00c050034801c00201216035440341740c0d41a4605a0144904110654000c15001ca03ea02c0d62031103044110f000301d038211070180c504000010b00307090000e0079905c8594800021159211036002c1a5001d032241d0940410711211030a000c40007a0392000039004941c400d400440d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 864212383 1250 864211133 864211151
    0x305030406090e0f060402070c08013b10150906031527032604260a0e04020c0708030f120105270403050c0109050303040c0b0f0409021318 61
    0x108901070b564400d0680d1a0564144000320450000351500240d0844005a0321712151603d4170a1074100d60200300e995180c0300c880c26481d8403a41c10141c41074030000c00300300c05084a10182c0311401805440c0541a4400d2040780d8041b0b07010703401111546548040c580c2250b58403001d01043d41c400790012242c6901c2e035061680d80145074004e140004800c007410011800b88a048038015010940016080119030401880f205410b0303c001030388509032103a082d2036031410341070088056030f00c0301c510894260a080d21810a00703040042d200c003d5034a6840d0408401c990b000c000c041d401001c0c4041a5000b4800d000490707006c100300030114028001c1000b13072208203c688109a40d01e05a0003d801400644203090300324141941e1b0200d141d010a403d00b580b40c440703080465884c0203c901e038907025807034442c001003433040000c065841503100703c7d5024242510340c01900014040c04541301410101400207000006903134000d46030510803003504e00301c43c0381e172013016403400041e00b070002d01d80b0382c0c1d01c1c00741d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 864213633 1250 864212383 864212387
    0x103110f070b070c081c0204171506060306030a2d0c09060b3103082703030c06010303141c020307120c0906030902130c030c020706111908090a0305030406 68
    0x700303612140340d042116224145407149500e034852442400403d03c2c801c0007004e100c40e0171f036041c3d40c09001d5151180b40914020140300b0f58a604038201e034103070500c00100203002803801d0030480b480760b038001e8007500840c03041d640c4040030280c1410b083d0421210142d90034200545d007045091baa10301604a1f04a9685400c284204803034543e04401c202071000c00198443c0d14040ca85840c40314108505611007104010030307840032420640006104c03560018042014802d104859035040700300019070f1842101c41c1040540e0382c4668a02440700d90000801000420b00524a03259502040440d4a16000615000800080c0f19502c1c103641158003005001c0001c0d401307420740340a43c041e900304101800101030302a12240311403142c0320401d038940160f1b074215142c2c501068804040e000c000d0160000c9080040c0282503102201d0005101d40440081c440348585100068075501d01c1c042e0028056100c200301074003100c3d0100380e0342c0101c1013213050140d443e4011000004c40c0220055030b202d0b4109140 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 864214883 1250 864213633 864213653
    0x100b1e0903192018131709010216030c0e0402030f0102160c1e05090705090901030c050414010f0e040602160c0312050f03061c050a06061404060e0a0b0103110f07 71
    0x501005601c864204080c2a00d40c031032120401381d640d181030300c0c156403002e82030040060382d403500611042c07510900e1aa192040409000c0301d000036000d441403001070504142d14a241440040c0c944d04c6607640c10400e00e07190100c031039003040c0080c3c02e40f030310030001c048014203903072000d181e0004440010b0242c0080c403028400e510082d00c40032259a00038240d8005150400c42d69004640c4110399810110760312030700903800c0720340d8084043d00085080d030713584c10800c0202d0078511981d4000d44c14110710801103115050030381d060781c0507101e41d418010b0501e0301040801000810440d500b0740c1c00c01604140c141a0074540040a01c5140503072859821864270040307004a5080d10707418400f0034400c40410703810301d2064075805501542c9e40c480c6445a13a078212581100760304090607502850801509000e2950051001d6401100c20418880082401d00084520300e1090412085a64000c9180041c85030042c1c42922014500400c01441903000b000c0540e1142c1001c0f03c152000245400420003c064 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 864216133 1250 864214883 864214913
    0x30702070519030b0c183f07150801060804060b04020423030607171f1712030c07060e0109080a031508070e060909160909020306100b1e090319 63
    0x42c01c0c2400031b1024821900c03004142018442e40342091485000c4c80f010107001c000c0818524114003188000101002c4000764001041160043c0500868004a0101550411241c540d10303516940e1070040200e0f001400504202c0300151103200340c0000d0b0b542d5002a01c09408482d54042d404254400e800100140313080071940240c000104001c4e806030001c51a50380210039505006080c2c1d14805100100e008030a641038580c0c80001020031080c0e00c81007410358640303011044407065130b00d61883c01d0440c041112550b034601c408004040001341d86800a40d100b210750b10002c038201685940350f1245030480da10382000039940c1c00380703040d0300d07110921107a0051000c0009130a80500303101c446010000c0040607140900d4640c004120741400130031051880090581c6404101c60b00c4007006800b0307001c07030001a40320b80b084c0c80c0400c40e0442c2c40c00408048230206c190030f03850542800140308081014000d59080107409010161242c0c50a004142081101110805200304280340044007175030001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 864217383 1250 864216133 864216151
    0xd080c01020f121e01050306190e03040e16030627180b0709050a03020a12020307031e1514190b0306181203040302030708090a051f020d0c0f0602030702070519030b 72
    0x400401c01b94801280003504070603927140c10a440c0c3c079030310b90541c00740000c440c0420346d50ac00082c0000d41009126042d5020b100024141c0c140500440c0c021005d6983d680078081a00344414134003c503890810341c1d9000120008000890600004207071003541c00c1c10658185e0329903a81c40200034040f40d115070500c01401c4111081d82c0f0395421078010840c0301c1802e000e81e21090a03c49000c80540d03800f08031318001141e01c600d40161220b60b42c0010038501800e038a00301d038000e4100014022403481c81c090340c203124034509940b0401e540c40c141c0101911581502506006076182285845a01c080c020742d480380300703140c07841c1c05e100f0602c83c102e41c84c2a803108442e592040c0e040c800d20000030780c040f04803200d481d0011861511540d031240041c83d00e800c1580500d6000001e034400e4559226070901540010b500c0c0c2e002e07200e101c0c03403144064504440f001402000e005104151b00b0001d0b00b544e01841d0048064411552410b071942c0114080320b031945480f2400f285000010010880d25128855120b603280c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 864218633 1250 864217383 864217441
    0x110c01032a0306210c150e090c090f090601020a111201330b03180106050418261c06090603031e020c090c160209070f020115050d080c01020f12 63
    0x2038641160080c190300851051b2440e100285601900c1183c00c1c2500c01d00080c080c8141d82800d01d0213640a912003002c16015402080030702425280c100d030740c1445084103170094810140b007551404030480800b005180c1c05540302c01c419038007003000d01c5080c04000c801140b196044030810000c2c1032600c0c40d04050f03208440114014003036104020150703500a000c4441940911080c1c0c0308031405030496801c8590030510f00708003640d000100540c400071081c064040c062500e00a26618207500654a8050f00400c0080102d690016001c4201000e458000100001c8454940300d222042d19015817083d0b000804083d601e007140c040344d1a85100805281c0002c0400028800c040384224400801d510700b40c03400400c2c4141180302003020b40c51990340c0203040003220f1030a104e0183c0601c10b1211151b0056103028210f5088040c5401d190342030311001410401e0034802a907403000968070800b800e43c0555001c0c0041411901d035580036010f40341c0c0403114104503241240e031041d1003845088020703814140c0707 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 864219883 1250 864218633 864218699
    0x130b1b06282a0e03011803111c110c03060403090602060a0203070905010c03020a0501060303031d1902090916081c0e2107050910060f110c01032a0306 66
    0xca214035009064680d400502d02040309109070b55601c20340d02c4554155080c041002c0324a440d8000c0d1310040c42c46900e5554024510800d480c1d503a00c101e40c541e03400084650b034101c1f01d2070b00441c0c1d4803082c501000220380c080070410011a05102003660118045400c0b8901880817a070148002c0c0d41c414141c00085081d4a46110000c01ca00324034415036062000012488080c10b10034004070352101d40190003800248d50740e16000b00242810040e0590504d118481c0110407200032501d124150040030708003500040d660204680c0c034602410b000f9552140713040304c076a5401030006070002032003144040c04a132403060107010b10340c1880070b00000070000c4c21003001819130384509200c00c9040c0620445001d11400c41c3c1c6041c50004150400d1703a000c2c2009081200c0941041c00310001c1e10f24030b1b40c41c030528a1059501f941e87c00c400d111341d424a9081000e90340d9043d4801d80c03150400314140000170b01c15082904e110030a42590608240000740c440c50700f4011b05048840c180c00c8800040098220102 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 864221133 1250 864219883 864219911
    0x60f06030c0f0c020d020103020706021215040c08150a0305060c0d471216050919020d020f07030309021e0607080c01090206042702130b1b0628 63
    0xf90000a100b48004542001503912030b5040d204940c3d40444210341e1400c10807201009003508039129000000000c00c0814181818003070f820520710180c58040c11a164901c032103010500480c01b007600201c1144001011803c1001828010f240300c200d916076604ca00300228082c1d804c0e800c80c0300030184185400d41e545a02100c0508246070851118801d111080e07080441c14503c07080302c951b480303c0e202c100340380c0044001c81e0a24109400b40d211a400965a2050161001302120044040594040b03488072018454008100c5110600300040c41c0c43c494440075511500902001c0e40000e584a10520450030243c0b148031002650b00c65052040300390340002400391244200042107107201117014001c100c002d41082c2070f0681d0007811140ca0301e40702c886101384101c4c0c0c5c614281c4404403819012101c68480e10031aa00350714540070050f0600e0805124158981c00311907603000102400e410170380d10741e1007881356031300602c40c1d11111300ea008916901012011340105007030408078502018032001d50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 864222383 1250 864221133 864221147
    0x9030d02041815060e0f032a0909060609060d030309080301060306030b1302030d0c0201020c06030103050303090d03061203050306010c060515040f051e041407031b0603231801060f06030c0f 83
    0x10304106c0c1c007403207124942c1011a0410500c01c4002810f903103025001031080c4180040c0a5138418181e03901403183c1e035140701c21503860f00241c500c00d03003015000020030b002e42001f58020040d24001d09000c1080c540590714003940d0360003603018400107503541da014020000c6504901d90071440d02c04807560903403500c1e000a40c43d0501c3c0c0010f481031010b401c0c0c00138110390090104001e818802491140c80b9a03481c1030142d2640d1003103130f02c0d0041c0c1c02001e0054070090b00a11801d4290b4007803c001040c041034030390702512298006450b45051040341c08c00d250001c0e1541c000c151041501c480c044240694680510058590f00301500310201e08010410000e44e01c0b420206614101d01c01c5200685e85481c1018142d5401d10701184034503009104000c4140f0440846404100c000d01e217090401c19640c83d0114229448040c0d40d041028807a4a50020307000e8002040b41c0140895506110032021410020300710341c1558003400c044801d416003048401d8061145103500c1c103290030030484103118070000500da4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 864223633 1250 864222383 864222407
    0x2010501120f0813082b140904090b01180b030604050703030f1e0215090307170304060e0f0106140a050907030b13020a0903021c1e110d050f0d050a09060809030d0204181506 76
    0x3c7c080101d024840c0f591b07650401100369400441c50f00180d6152800451281d0000456101560403d83c81604a0600084992160780c104026046031819564103d0340388000003a45010080300181ca0341101ca40d1444240724a00b02d5001042d500810f1425100b0404004006132000d4005200b00700102c3c43e02540c240c1c24090311044140d407942c4c1c52a122005048400c0104094400e410444507200015070150003276604a01c2c1c842150348880d803c00c0035920840c00390355003121408000c9281140281c20048040d84010a4220f158442c1481c2800703c1e0005600200002c0c4003013001c1044d0b081880c81940c080c1c44040c0d4001c802c12980d1224900407804000790300140306090740b100180f2042c0005c1b000d800038018030440c800c01c070a00700650b40d103030080c000000034002d856040351190b0155003120b545030764988828580034a03200381503034014002000f44005000c10001c600d2080090720041c406000350b41d9100f0b500461044103c02150035009106a4840345107609100301030b0411151026 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 864224883 1250 864223633 864223667
    0x6040c0807050d02130f0605070b060a0302150901020f06090115050906060f1e040f080d1d121e0102250503030a230106030b010f02010501120f0813082b 67
    0x6910b810b142c946a002c6407075404030414286c49540400d002d540301c0014806c090207540260000d45503d420003c60902c070b48402907200364460070001c6015901c0010f042542c4050048c1e0740345000c2440c010381024411901601d19075034681608100007216071180c00035180585000d041480e007500418110711880d103035440500780221f2004042d80d2400c0c4588050f040510703070340fa01c0f00e98031a005290034015024006141c01122a40c4110324070030801c6002a8000140414280310004240003c203844a4800002c1d4001c201074107180e0034104250403010525180010703681c0455a100c01c0104000ca005411990150701e469004100000141c94000d10100700014240c1a941e840325035501034074915119510080c03000190403a0140d000707044405081e210740103800c858a41c124200c1e0002d0003150410800900c0301c00225014000c00680d02e03200e650b40d14036100c0f62a4002e030141c5100d92015096501c02c4220768405800b0941e030350041c04614040e81c85800131000041c100d03580542303113036403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 864226133 1250 864224883 864224887
    0xe070f090302100c05030f07030f030b190b0307050403080304080304020307050a0f0311040b1201090b01090e1e2410121a0402010306090c05091203250201030906050c0306040c0807050d02 82
    0x117102c003e0040350600b0110302005541c0e0300700b40c60003601140814580401003072a041080e0b80906001030034400f0700a140c060818510f082924040c02e0350009410310342001018480400001c6130400114061170040090586910340f038070416280100e99080180030310034420080007042c96800028003601c0d44017075a03076079503008680407074010300c0b0106006070311905000a81e403100d4010742c480ca0f122809580c1c802c2d03483ea02c1300f207072400780c84291609504503403281141032420004003c81c442c0070b0200c0801c0e107060740c000c9c00808544203950488003120000c100284185510484248001400d10031107080020605071145d5802042c412040c0480c0809032001030110384c400d0340800c1c00792000c294104940d1002120007400c5407c6500014099042101d42032a1030a0000c2543c450a020382e0b400401081110111492055411822814035448501004c006843c2d800b45911440c072141c10203803603103805820401561440910310041c040188140001341e0307407140880f04403c215000240e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 864227383 1250 864226133 864226157
    0x70b0108010c05032d070f080a0b010507081324110616030c020c0a090605030c030c030c0607060902040207060c02011407140c100e0718020301300605010e070f09030210 74
    0x5081c5e1288000c201500400c81e410440c04070b03042040030300701c81c4555542800e6980c03884100400c442465201034040340c001d01c000c2c00007a1540005191320402101081070140d42c1e46440c404071080d4081171000b0703c2c0400460b00800e80c0c060900c2c40c42490a00003405036003040448805c00c1411501c01340201a141c83c00080694000c005070514018060194804643d075400200300a003998000c2e1031280c000c80b80406050b24000500c00c0d1072480c01006011502411030402c103285c0e010101c00c071289501d6141d80c0016176143d202903e00c185c012040800c646042560003400c4840c1480f404905d0340fa44414450700c41d512201c0007400e00d041110450b6281641405a840c224900317045140040c10020b1450280d200410080201c401d8840f02d2022444001201c82c1070340000d00450200c501404078043c281c54034206a0409825582003980071003e0340e4580c6015140f00760032070680c4070300f16020b00c0140c941c042060b1803111500d160501c031440c11540041c046081180c214020841014200c17 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 864228633 1250 864227383 864227431
    0x70e16021011040521160602070506120c031b0c0d090603180605070201150f15050a02100b04380303120103061a1e03060c04050d0f06110f070b0108010c0503 69
    0x524200d5400c100f2680c82010140c0c000b440c1c11b8040c0207503030043c007031800001000d04084041d242040c10100d0030300703a940c2d5604009003058100405070368040840c07041c040002000c110090108a48840c044d018041d80361034041d0080c100c943c0600d00b00740c42c200840c03580201c54411074001d01e41c00b05d801304068891200407030241a40f1010303000d21041c01030300002e01c80200645102110310101d1601840c454007203080c0c91500440c000c09000d07811400034400c0f0f048540c5d200840c560001400003440101020b0944203854400811009c01c0541440000b44901107075140744d4080011801103103400000002440c0026062100030409a1500000d625200606a100c8071020000d03080d81c07603030b1100b621103415000c11f90001c40d0090041c1c4011070074480443c0c04540030341e0005081802981040d544441a010500500f510a940d5030152201c0c95806030b0010320308003007155809515842681085502d03408103a04c8421640c1c03401c15031186083d00325051b240c0c002e03401611700b1200525000b41c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 864229883 1250 864228633 864228679
    0x1a06010905041104080d05090a06081b2b020405010e06130e040803010608070306032111030408071a0a02150c07021f0810050a17070e160210110405 65
    0xc242d40c01400c03d054811908108030181080341c15081c101c130380c1414410800c0c2d0303140c400c0c4e55243c2d1f045100300f0300c2400228010000355030040e50041010b0b607130840a00349200c40d60032555030b80103030b6200223001c520f440000300e5450782110b107020821841e0601d02000070f440505901e2407140140d40100d11010304100c5494003a008084a0a4110349440c0502c2c0029541e80240074540c0401d070400d021829140c03003449240180e071390105580c03001800e0903948001805011144400300021200c4108442c80c3c02c1c4050701c001e103003c030010400e1901f065a01541c12501c2041e1100300c140501841d421241d00023415601c008207080d021445494400d0b0644a6100d80c4030301030342164814500e0f017114400d40b540c5201c8091141e80f03008281e00ca009210018000d81e2046640c45904904144040d07410f4030002c400004514084450320380d501d01e0020800c00d000c40e050301000b180e411654100580500008601a020080800505078030b080804200c1c041c9014045c016030151784092500318080302 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 864231133 1250 864229883 864229889
    0x9060f0916030e030a03091502090d0807050102071a06030d080f06060c28060b040c0c03080606040f030507171f020d1112060f030c06031f24090509041a060109 70
    0x2505d507505081840500904407a40c802c941c5921100c80364110311499109407425a0002040f00b00c18101c00d0700c88101c40d4000a00a03203180d50b0030840340001400c2907036010012a280c0350703150101d1030144105070412010521240500615108000c96128001e00742980914100d844540391008008210325010400100b0303103003d60081440340d441d14108824150641c030440003030050700801020301041d02c603c80b1083c000700344100e8551000034020f2030856480310010b04a0b60410f0b5485420303541090b4958000c4d601500078040c1803012401103a006540307025030300b00500f0510103132a0840030225604160802c400d80c04988103202e0300081c1c00a03221808000c90382d9894038140e0442e034404000a4070349610400c0900c1805055050100d004015080018461421030303945008405100507520070b00c104c02c84120b00d000c24900034078178039003003260318400300e02c40300d504a4000a001464990495882840900d0422001507020b91704841c171101c141141d900640c40c0e2000582c0e84002c90b070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 864232383 1250 864231133 864231161
    0x2090709030804030b0f010b0412060f02210a110901140c030d0e030a020708010b100e0f030105011d10030b0604150801061e120b16050d02030f040209060f091603 71
    0x10000300b03000805d41418002c0c0e02e110306660807642d961b04c42400350710540c81041034801072610601c005c290280d00803c00801800e00141c07601e40f414020141031020407031494001e81440303003404048207407032127000c901c80c1900141619040107840081c000c0c03003c81e0848074020000145800311894240217480410980310001d201c00f0000d41402c031f440b80c101150402c0184114003000800340317014000c1d00c400101c06461141d8210041e4030031030305a0302c400612500441c280892240b551424803505000b00440136200301c0d0300045003402c0e88031400142500010603100502400070401942000341c1002007220006581c6100e521220501c00d401d5115401551034940001404154603000c1580c10303100300c0a0002164903100089941640f0300800303070014846500023401c03025583c3c1c00081c050000d0800c64200b448000300740050380d10840f44041c0c0c07000c0362400e100440c1010141d280d00001d0854501c0030a00022020440c410700041800044111349080c86034190700a80c1318480d440108c4c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 864233633 1250 864232383 864232387
    0x90c0a0c05030a031b0306060f05070c0312021e0601030302100504020d060c08190e070b091201020a0e0a09090f06020a0c050f0115120c051e120606030f011404020907090308 76
    0x114040c0003002d2120466400d0300e481c5d0210100d552207842508182c170b4050f181c1c20381500c10144215100c0c1c10401c011213074841801c5002c800700709942d1280003842440c1d801840c46003091040c2225585a0040c0004c043d886500103000080d0041030004c02041d50120000702640c0300d00002c0c0c5000b200c84d0028107014a821101184298451155407059100c54416000d181c04002d0803021503003103c0000603c0e4210000c2440b45806650080c2802d00005080c0c00c2d070f00500c06200303401ca0340905440c01c04200001c4180000f802e01d10060402001d408004200c0018540c6803000e1480d42c0c0b040007000307660300013900041c0030700601003506050b402408460922400d4070710580200a100100c041404080c0c400083c106032010404001586c84005e50000e00e2500090192641050f8103884100b043d0025900040e2070300804103070b1400c3c000004003241d003005d405046c03d2106111444103240d0404007643d00404c641002507410942c1a20007a10304c7d502d0500c1228001c229400040c50300c0c0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 864234883 1250 864233633 864233647
    0x12031f0e0928050613081902030c1002040b0a23070308040203010528051015030c030b03120403260304080d0501050a0e070e01020c10020a05010614090c0a0c0503 71
    0x40002c807030600d1080709960401080a07000507101c941000030a580c1c44200000c000c40300d00c9140d4144d8522544901e410031003e040c000d408552003048040040c1c2c8041000c8221090400080c0d20201250104500d0542030603400010703440340d00c00510070300c483c0a0348107d088010b404001080140144041d031180d21070316006005d142d06a40030791107903003000c0100d5000303500304580d00c00e02e0054131040c0c2c040c0030301c9410b502d018103c0103096008a0503002c00000b42c40071403815118000300c040e40d00082400f00002c010b0b040303075403000780700d80179034000da0b030502545c00c0340d00494094a400c80010340140141d030302c2c00d45218480c09440340c4074040c04028401000054006050b841c0768484040c081c0c0c1e80c03504140401050244640700c0b0492084c0081a081c40c0034540c11a0b0130407040c8140c0e0340e01d1150602150b0717954010409500140e00400200c000c0c41420300c00d1101030b0000320041d0604041c0000064000f807400381400344108400524100c6140c05a11413070350180c0e108041d20303215a9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 864236133 1250 864234883 864234901
    0x10605071211161508090102190c050c0418050d0e0604090f020c0d111011091e1504140609060a0e061e040303080a09020d06150b041e05010212031f0e 66
    0x4c5851aa010461034004100010018000d4548130025807400b00056100c0600407103003a5410360007940c0c0c80c010080e0051554a550290600c412100707008111614480d282442c0751101e2400030a08212901031184c096554110480e804c4500c091808078546103800d150400900c01c20009e20058450b641164010640012031180920313000000c1da505240c0c00c1c00004281c40c5505c0f040260f2034420010160740380303008014400101501f01428074000850030105440040d043d41c030085400d0041410082010340305030015007404256021403c1c168500040b60b224010881e203403040c0110280c104905840e03c00c10f0b5580c1e2100720200c416180d1404203128001c0c0c1c400e000580000d100e860010764640031901034507140f19400340c00300c007488046880e480c008040000d442407414220010000740d82e0307018406840504181c80614002d001d4500031400090030507404541507402c003699491f480b80750541a294040140c0300030f00104084082d001e03119400c2d030340002059000c3c203014800a00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 864237383 1250 864236133 864236159
    0x2100608060406270209131202150a0c0905090c1606020414152d0a0806091602030a050913061d0a11091309020405130b01060507121116 60
    0x281c001c08040000c0002d41e400302c0344e030740340c1a81c2c108044268080e44d040142419a5400c5c2d10101940a5561980096a50b0721540c0c058003148001a80034095000a04403110402034210350100303002c00ca040303034142d00900300384050b2080b01e2003615504006103490f004a411170302003410556240d8008251032074908000d40042c02a04c1d00313144120101709060601d2481084051031b0b00d01464203040d1455245201c0100a40340740ba030f42000445030102130400c810107030612084d15160400d6903c2c02c87c05101d040f0310000c0900d5001d04465402402064003c421031b00000480d107481941c481680340410340e440e806501e200d407001d02d011000560300136048940c113035500e030041c0041e089880c1d1100c06c109862040d541500c07580c00400c400c216034a00398040c0c102d08441c00c50040340500090700040c0c1103d104951000352a4240b815100c10024260000c0740500302d9420554203000303050700c0c2e074010503580090700c005101c01c00803100c204181c2080045540c2c0121401c03800300383e071034198454000c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 864238633 1250 864237383 864237391
    0x204140103050f0304211a0a14090309060a08070c0516080d0801150309031b06090b0106020a03052506060603020a0f110a030309021f03090b0c0310030b06010210060806 74
    0xd07004600c44048915004011603080310f000201d00e106059040101c4885072002410885031f100000039102c0f44450a100043d01c40d4546120000303a0007000440c5440c5154000c041c11959081000741d00060b40e00c840c155050071b0040c0c5400c08480da9248002c1d1101c030701240e80a4000e104190944c494a91211f54070801d80f2103c4041d80c42d4246015400d0ba4a00020b000d9502d1070100086e110400503c00d6105408640c0030345888007001061086019100c0f0344088240c8081c2d40700d107418000d0000d204c8819006200610042c19250b02c035440003441400381c14140381700f50406584000802c400041042d04c0d13150045402c10105644400c01340c020b6111070b62039408030301301d0228010050301801c18007481144140140121b0304007503030101c00500b02403000326440489204654100c03101c0340d40480a46865480000c1d044016041507150150000c2502895481c00c00400c10710070061021141105e501c072001c05529143c000050f0f0600e401350000e10764540c0703040c00014040200117082409 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 864239883 1250 864238633 864238643
    0x6083706050906010e060307211b05030c0f13090e010b040507020309061c020705030c07030c121211011b0e1203071e060603150c030b0307060e0105070206070204140103 74
    0x4103641d290140681c905003102c800d0301280b48411101518100040156888540c078600b80e0307078501051081c0d04000341d51000c0e6042c1c807551910801e00b00c0c1054520b8940303200c440d0074824190f1508402d40d103141e00c5070480c0c4c0c2c500300d000443e180001a2085108002508039407105003c9000420180b45c000c1c006c00b04031912590911002c20382c0c0340d00105c104c2e2040c0c400909010303e02264a9618207058a604101d2410144e0800252000c52000e10142c8018103408001c4e01080f46141048410040c40d5009201c45806c4002d0440010720115a00c420500841c1840a45001d8070030640d4018a103840090021442860300d10001310746c020034050350340c0c0e0215600115500300440780b40c0d4a000f950030040407403c14240306850201c501c9903000380c0c0d6224510120340c03551242d56002c54042d240c25901241070f250040407203403d401d8050007654090a40060480528020000301200c00c2030000b54144180051f0b4a03042d52652400c40d4900c0c0e402a105101501421f569240712241c01d10080e54 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 864241133 1250 864239883 864239891
    0xa080f0105010503011a0318070f1e0f090b0123040306060e101a091008090f12030a0f060308030c03070f0905010c022106010b0414040603080301060837 67
    0x207040d0300480540741a10007007000c3c0c41d010012030a03011504d40c005001c080ba4503a064510079101502004940c02524155810440751440c01d1030b041d2040c0f5040100c6000e2180c1e100701844540580416041210800c8802260b00b402a04c01a11000120030444140848541214078502030ba1001003007260300c681800c10032165102141103104405036035a00110100082c108820004050410904100340314901d1070b1111210002d801c0103c1c2e49080408241c8400402c20360010521002d0034080c0301c20080c1004000070081510700b0702c0000c20a5603800d58074010341922040ba5031044010f580e2240105a41c1e040486010307480b50001c03111100000d00c402140030959109d0f04020040b5101a128032000031017642c00c1081c0d00c2810402d500c11003010300c00362200420108000c600030104141c125030b450b0708286490841d0303107006850b140550f0401c03004100140420b41141d04448007850b1440c5162201000c40440c088001070b80050001c0c410208071821309900c3314605c4401a10200300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 864242383 1250 864241133 864241139
    0x1c0c261c020415320d0213032a09050c04050303120a05011a030c0d0e03070c14030d17060103110c070f141003050709080706050903010e2d10020a080f01 67
    0x41345494444072090190071154520011403030564104034640c129034507400e0814010700ca4040482c2c0280d05040c4da83c0034001d00800034011040b40504510011101e00d01c6083d088605003048446148258419140e03640300103070390710515000380c0340034000c01025031760783c0d114a200c1c41c4072040c820340b059110710b480c0c03000005416281e8907031032945102034647c0c0c50650355110300e4580a07800180760080002c0d250040f0f2085c120041c401024114421041041c00c61300748620f00301161a10700c00075010303031f202d014500040d9401000d124120748129858103159910400100e000d00b0a4080340480c075100455000b201c0a4045110010344508011000701d4541c0d5400029510021480c16a005005181c2c05003d50b031080d04125848100360812088107a130751400289440030a9000700b0004001080340095840c0038020011140300302c0004002070f160000906442005901c1c019441c520310020510402e03130244280c441c10402c9100441d25a02c0c800360162081c0c3c012190a150200070380004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 864243633 1250 864242383 864242387
    0x90c0a060210090f15020c0d03020a0c060905030f030f071206050a230a080307060b03010b0a150315060f110604050c040e0c10021c0c261c020415 64
    0x10011610568002c000828800c0c288100600201e04242c904601480420020a84030b0f181c0e008030840d620300c01a56124890307205820000e40142c2241003500400801c5000c0f641314500d80c00d0590450b10000703480903246005032030761142a145002c414404030402203400e69003c82c4500c60b0009031100500680c000c44508121161401855802001500c0620140c01d400707610103112102000d50340c0100700303440c5c00141c1e600c48a5201c01816400002c29001700166800ba5006014041e0300071301092043c0303030004e00100f405000700f0007645060015800914882d40000d104400280c001c1003000c2c1d1140380c01000c2480d04110704c404910350b00b00407595910000344241c8942e030000007924804080d541048043e0041e0298800c1d54460241803007066035a4844200c61514660005c04024105800c0400280c13204010030060008412018000c20041201d001201024403401050002505031000303c90091585400c00060319141d018040034142c0e0061054420140c01780502082d91501 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 864244883 1250 864243633 864243649
    0x1008010f0b090631030b061509030a02010e18010e010509011e0b0f070203070e04020916050306041e050f040b09010e030f0f0909040605060a0609050d0b1b0d05090c 72
    0x3100e0300300408010b0080c108500160402e85611002444c00310709244200d070309000806030704280c030000c00003010b20405140030b5444c50078140d2080c3c0d1681c00d106035140000d46a071000c0c0f034003905000d079101070000280c6d1201c800f0581314221a40710320f03a65031916011041d05500b4080c583c000c82c044030000c00c2490025024075150301540c0c1154240b1801d1031010501c9810001e2440c132260b4003404010010380d03050012201410f4001c2074202c01b460180100001c5903805443c00c08501400080b0b440c61070340c0403040303a40c0302d00141c0d80451854407102d03080321030490542801c07440c1e520f4542072042d41001701c050680606c0c0642c1e01a0440d44802203002d080360390b200400c1c4255402004940c4030303038100383d000c0c0000e102412107040c108440d9501040144c03c0403941201d450340d03508200b2010f468031403d81d40103401c00b8a00740c4c0307006d820030000c01c0452162100c003030260400c0d4400078292915200621140d81401c041c025200c13001e010402010b4041a941050140103078206080c5504100c40 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 864246133 1250 864244883 864244897
    0x604060c0329031e03130501050408100908090603130525060813050d0804050d0c0b1f090c17092b020f0d110f0a11130204051008010f0b 60
    0x11482240d40250034151441c42d1214450740e094080c070050003000e1a0803401140b020185200034569503020360702580c1c10000540c1000d0705000d030601041c0650b900010340c04801c0351902d900041c2106180c14152218060b402c800d5601c26000410484c00d042c030390b4064901d1510076000c848060440052014170449203900102641000500c208800ac0c030131038600360000010700c110085080c26480f49411f008020409038081f40d2624148800c1000c00c21007807908444a143c0910305031a1980c60340041e200290400c2841c2a04844246031907403c0a00100100300b4403100f04070310f80d54003030060a045e841c000c00192507500400042c544941c0401c041091008404c41540caa1349811a0901e02c040841d07500d10841c40707682100c20344c4607410419190306501c1515450840342405001a01d4a0452000103216800000d800c03c0010a24000051304040c103c81c3d040c068188215850000d006990283d035104041364900c0410301d42000391141600c1c0c0ca0803503002d1450b200c800190a601c03440f8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 864247383 1250 864246133 864246161
    0x30c030b13050607120906050f0106090e0c04090f020c060108010b0418020f061b01111903140402060919090506040b0d210e0909160618090203070504170604060c03 72
    0x200004c0a051107240c41811141828000160025694403540e0442d42d0803030b20ba190b81501e000043c0180f03038022a40c20010401d0801d444018a8080750404860045201c2c202c4525154034620150b0003150f019249110801c10484503550380d2440c4890207801c41d02803081c0100d207003680c00200d0740c41043d461411a07401409100c0001d8441c828840994080c540411a01c4c543c1001d9501900c070a018400c8100c0f050b4040c0c40e22810320130003190610164403480e20a0510301242070300100b12000742d080d84203804441d0345448416140100e451141810f103451001004000081112001d40e8405402880141d9080100119a03404d0100003100d070f102c0600600003043c45843c0030600003030848650301062070580301410807038005c503408007400c0d58a114681c100f1954400e900480f14260001030089241020030704040d948103d40d200c3c29030140346c1c022500000003a840d01d018100300c0e40140100c5160300340d102c80203501c3d5a01c4a03001d480450700d06040c080c400d00c40c18400c0c003a056070388090f2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 864248633 1250 864247383 864247393
    0x409080301050d1a16080c1912150b071b08150a0207080301030f052505040207050313120c0506130506091f030e0f0703260403020604030c030b1305 65
    0x4080203c40500030340704461546080c04081940088004210b024060218001c0d50840700c490010345103500062542241035010b1000c01442c409002c01002c0d242c0d42803c20700801d50842c1503c9001e803400c000202c0b045913030340800043c142c141100038440c55005102036071050071610382c0b8214100881c451108158000b000342c0002c2001e125040d900568406d80c014a003000507500c40c0019042648180c4807a628090300070b050000c20b000c1e500410848010001e0380d10001d5a03407001300800741c00760034025903021074400b0420008000304c5124014201030104156940c2c540040b00c582c22807811101e00c8038401c40001c1030304100d42500c41e41c2c110703101110700c034508250038044190414201d03558000103c00782e88046d0f0b14184071026408550707035008038903282c50300521031410705401d24a41e038a5101d0b00042002c81c02c034030081c0e80350010b10103000d00c0c014900c40c41400d06020715080070750712100000c0c0010070406032140d02e00c01c44e40318140c146a25500ca240e04500810000f4000d031840e044 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 864249883 1250 864248633 864248639
    0x121407030302060f10090903050d0f050603100b13150f09050105060d020a031410080d05040b09040504170a030501060809010902030705130603170904060b0f0a0c081b01050105040b0409080301 84
    0x15040c112580200004d542e00840c559801c251b2059400140c0c0c260042000060300d00c1d00300f00c1a000d4411410726110050107181851b801080c1e49078203080040c90410764403d0440c80540d40c8007011562920401018028225003003d003640c031004621806d001c02d0015040002d80c8015801154101e8000034020350900041a41e00340107940141401400c0540e1212820505101250300074040d40411400240c258180104546400b00c40c0c100941885424031040005504c078004503600d010096401240c0340c0c46174030306500c551421001c1300246202c00f05554900d10b80c5070340424101d031501d03940c1d51215281da150030341c01c880f1403900c081e4058020b85828042c9040403603040380b802c0c1094400048481d606e440308941d6240c2c41c640c00c8903030540041c0c03030109440c0c00d0050001038289002494a010700f4070320000e0441c800c076034045060181d413640783c000303001301b620070b403500c0c60a0001e60b9041660003007035a60085c682401000d100300d03d8008a01c003982028412441c0740350b40810b00500c0d41c0d003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 864251133 1250 864249883 864249901
    0x3060108060126040f1e0606050d020604141801090b01090e040803280e010204090501050a0b1b010b040e030909090d0504030803090f15070f0309150f09080412140703030206 76
    0x20402d584040094030380a0006075030310b001040e01510600c2c1400750008620b01031003238071015805035114980c10071904025960700400c8504642d00013080b0450b08032418049292400444900115044003000002c1c400d00341c0e4100d00151102640e8000205481f9401e501d29850142c5025048030424000941005090000c0030018035218902c403c42901030001101912880c0d18041c0c1d01d40d4010504102c03030700e02405071502500c0b0450f008400141011280180c902a4181d1035070304801c5140ca144a4203400c2d80602e4803880c001e003027844001c00b040e401541d6907101c1c1d01501d01645605000850038400031881c40030300102590780170b150603d107486103081d940020781411b44a0080c3c83d00c60780303c0202085201c00c2c04a07640d55100301e0385071180003c3c180305014034418042c1802e1141280000d01c070134003021031060515100050f840090a414401003c0344440201510380000707004c01d49640b00c5401c141000d00c18008141701aa44903605611241d8610004015078812004509016 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 864252383 1250 864251133 864251207
    0x15010e040f0203190203011d1c0c080d02040806070f0f2708152401030e03070b0a0b0a0801021201091d0102040b0a0809191101050717030601080601 65
    0x5014807403868400c507050700001d08005244c02c034080406107101035101181028040d103100c3c000c0d121114043c2c03400c00d440c01d90300d40d05561070795040807c0c4a40c48510b02c030b0141c031080e80c883d07803c160f41c5d90b11441c80c070020000075071107030240c405103205030800500ca082c82100c0304200c051440d661075140d2403401c0000da90b01d034569000321032031101120410b0840c8540805440051a200c00200860500f80708100d103480c4002c1c0c00750a01000c000717501802d0103007511045950300c80a107000518089034140a84c02c40c060f500f80280b060005a00384100701c07115810803034041c44d0450307100c0300c21591440494202d10414141100326880c1d4001008007a82e25070100640400c405400b5004003400641c16003260300641011b10240e0002c90108191680280c00c0d540c00366600c0002c1c1340f1003032012105603c010640c64010500f10305118085110791007002a101d016600c04818460041c46490b1003005030021100c07140022032400014009610440390f074501c00300040c8000c0401074071030040356808 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 864253633 1250 864252383 864252391
    0x1018060b06340f06050a150b040510140a0e010206090316080c031608220e0a0e10150e0a0203010308030121021201090b060306090705041a04060f0f050315010e 70
    0x800c2145a0b00804118812114880c061164400041610b001c07000c007000c803406c01265080c14048078406010b02c129502c02c440551320100ca100b4000700c6410000c840702040b006007214228002b180105180d50002001c044404090b0240c40c01c07a9a220f008998034003a078030400ba040c00c2d50f02c0042011070a440d000342031055540301664548814400b0900880340103102c115950a00059001c1c008401e18280000d54111582e060009501c0d080903107040407000380c84880415912100e061900c00100040340c900402c1803028071844070080310b051980d0100e03200c3e050900640c00d0010703110100a10841c1d0503607a004071211700316400c0c00000e920254a40c8078100c46d0312990504440581da031400300301651000e500020407044a02e04c0c040c41d9504000e041c4901a9003c042807082c14030011a15206581b410307503001410700040251070004854003100141c10034a44100840c40f29011104802a1550001030107034643c0d9a609040c5c0d64010114103408110b008801400140e818007241604 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 864254883 1250 864253633 864253717
    0x90309010c0f0611030f06090105060901030506190605123405070c0e2202010f0f1b03110d0c05031801030e1606020d020304080c01111018060b06 64
    0x2c50035850340c41208582c45103d00b80d082280200c20003c011341e14050039607100034240ca00c01080e501d0030000c241076006a00d0400d05040e11100003c40603200c8125010310440076034031a4181c569035a5000d0b140b0350110515850340407a54000a00f4081c4441c804010196000000800041c5418000340d045192066500c02c2220402280303012991540704203000e0106141c0011345410300c6540108010f24000848003400c041002e11000350380c000c40c160100da415402c1c00148449543c5003210000c6074281c1006214030b805020200340341d0301c00e068681c0c40102c60210f428807002c504098402c2801c814005045500070070141120214107490601c900c08103040c0840c4070f039412851903040005c0340104403620b042d440c00c01c00c02d01f50304114174403425805001962030581400300154441c0d5506081c0c505025000f0139200c0710802c10400d0b410300101040c000c1041010000300340301c00060310101503030024104540d0380702c81d2504030201c5156101d00c0090130302c00250f0844401c0030032503103091030394 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 864256133 1250 864254883 864254903
    0x70204020a02030d0207050312010920031005180601020f03130b130803120402090601030b0d0204091406040c0509070816080603030d0603030201021c151806121b0b03090309010c 78
    0xc402c10b14000381c004075226402071071702d03031101140c0c279250094160b00c2032286504000301c012141640c04104000b1000504c0245d036203a4480b425603400e41503d501c07668210b0a544040d103c400345e038920440c05910260700380e44003070b2418030105999008142444030b690f2844842040342201d04c3d802008010a20404000b590381e0740c0c1c9240d419600002c046004040c1503070108821444c1400c410b6500200034201082081d40c4000894440c2c080010000d0181c2e0b0b852040c9014011000300c00c0304220042d07001c80e1010b16161808103120358152041c140140b0210b004100694098204e0034170803c54844d030048401451281168450703800741210303030140404c00141010001c5409000040d5010740c0006da0340300c070300160301d6011040e01000c0c440c6040ca03101041042100860030304084070b40d180703e2014011242459800205019400310440c3e1800408803800c200a07400c520100403048029801e104d41d68050962583c4402c0301e4080f01c0350000c0002a00e07960141c1c00f140e00503809007811403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 864257383 1250 864256133 864256147
    0xc0a031b080907050a060203070f230f010c1e0305040309090c0e01020601050607030507031d040204030f140a02150a02030f0408010912050c1902040b09070302030601091a070204020a0203 82
    0x5454a0600c81110016600008000003484100100c600130201902d90b011441e03c1c21a00a4807030142810040c5118243c2c0901d1046c4005030501c94640081c0c07042c0c84408203280d540c5035a03151005108481c0039407d0001c1c0001305401982203c900c1c038802c5051044003541d1460032401000000c03c21401c1c4560040f01140005861040000c0101d55444401540c59140006454050b05070301c03162080404010340780c0041e5001c415030f032613103605042c5a1380c0b0b9102c400845c001da0501d941c0c032a400034404100002404007003200140c0541c05000d0303048601d1011820070781c880c00c0044000c1c1d00071521954000c2c1c851290300c0206400c40c0f003441540c4c180041d40d041d4031481e42c050340c0700d0001130b07464141600501a446400c40300450701c43c10a1454515181643c9841d5146a40e61030407030361000170383c0001d41d1100c0e0044200b003000200a0700c410f18040c3c0002d4004e4100303546171800203103840f0001c61111511050921b00320f205c03074a0203060016580c2080302070b610058886045010a010034 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 864258633 1250 864257383 864257411
    0x518060f060d1d010b010215010f06081003050a0302010203161806052109150c04060828020d06170f030d0903180605040914071209020f101116030b0c0a03 68
    0x1000c1c80c00143c80c00451001498000203251184404840c4c004220240c010401da458281d0307a41c040f0750f05130030b0402195031007c2c03e45070708003036980c40a40140551440700f0201070381035001358800d0f00c3c2512682942c25901c0c4044a42c0d48079801a11000004581d06001e00f41c0508082c01c4e102c4640300d801c8100d00700d8149120300e0107900307940300340c0140d009401c0b070500701c01c1645d02203910245071152981041d1610034020000d04010b00480103071200c03100c0740300d4404c5051002081c01c0000400940d501d00c598400c00c00100350910651100860900907041ca4140204084503001f00340300c000c5080040002106000741340d1210110180304610926101811140c00c0031001007406032103136078940c0e1510910f84261a0941c1341410390511038010844600d411441b001c1003c891032000150724902e0b840842c114661002c4456400b88540f641e031205507a000145010a905400c00c0d2800e051107180c10048070816400028219104003001800f005101d801815005289180100d648800e01441c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 864259883 1250 864258633 864258671
    0x92301021b01050402030f0102120a0b0d020406140a080d021b0d1e050606010c0b011202030f0709021e04050f0d06110a030f0b0108190c03110c070518060f060d 70
    0x541c585035141e100300015442e0510420550184c0c0c00002d52401d5220301c51081924002401d0300c0304665141014041e68484240318001c1d990b0107030040154076140c003044a0a01080039403030f449544400300c0802c4680d0041000d03030b40d81307145400402c050312585c2c0c1d0603044060030720140d940005110420030f0100310481040400074032040d4540700c0d0001700c0c1c1032150070840010900c03414080a4000107000401040b112070440e40701d800c02c1300b8002100c0c80001c2c18400c0180311003405100300807011402c004c00749d009100340750700985150307103c0342e404581c822180218030545912243d403001d5244581040d11442d09850312401c00014440c143c1c01c11064240c0204142c000000d580381c02c0140c0d000d10b14403815041c620b003402c0008882c41c1106002c240c004003080135900703558032800c10521880c080c0d0441407122a000340c8494440000c9214543d4070045842180d100e00010000c242d124410314600f035016070006030072514800d10107000d1110503404204440a0642c2c1d9480700110550f020039 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 864261133 1250 864259883 864259927
    0x180102031e040608070309020901030209250f12060806010e040c17161212050f120415110c060601030c260f010f120f020d0b0a0203010e0a09230102 65
    0x40652243c1c209440104140380040068051514050350100940d803010010342c110703941140d02010542d10b5865402d40c0c000f00c080c0210850202150308800580c001d080309410385003d0350784c140c40883c844a40416141a071142056070b030030540c0144404a05002042c1c5d00c14002e07210614420303503842d85d40b9055002c4506d1007801e41c1140030000c1040c2203c003600c82c02001c80d1086080704202d15103840d01c01400c0c00c001c4405100300080c1c61856440c5117004c0e6070000d011590740c110580307400c2c20110140c84021000c10074841c90000c84000200b01c420907212514001001041039039590401980100288100c0f5424802041c1d441c001802d200d1140a529031244101d07c0b4a40c1003501b00410341c414180c012500c20006041c0034424113001d42c161011081c0c07c0001c0c85601b40325400400c041540a090280200142c2e0b010409092b0243c0c00460481c8e142c520921590b9450411278012a10360041c01848541001002d04c0500c1803503034035100c4045040e00051800c0282d0700b5180c15049410 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 864262383 1250 864261133 864261187
    0x1f05030613020906180a09090303140a0603050a1103031c020c1501061224060503070f0201060e0f0a06170703020910050d0b0a060312050903011a0618010203 69
    0x8000080c01d054200d5030000781d404a055051001e150002103da0280c1860010f803160a0131650945581e17003110880200315000003004240716030b090040143c01054489000114414041403024400e4816001242c0c7c015028000e01ca0b401d542e8000317201c0780ca05460b981444203200d81b4829001950202c47c1c4980f411200503940d40e002c50005007428100a40e80c0f1890000000411945400c510f100c0f05002014400049800c03900aa401c0c0b06021410b14040100340008081036640d0808002c600031001502c4030b00c064150450200d00362080ca0181c00420300c249000310b4601c0e8021901140c10840560002c03940d0307070b240d038200c1d145d03081c1c10f000404c61544444070400039420700301655a080600c00c1140120241800c0101d04407580000e0014a83c0c11007800140700010b040d4003c0d0040c41e8403135100c0855818004009002d50480c001d00351084d4607020807800b56517502031048100d408058205400c140c0c410a1074640440c00400d558154001000031100805010740000c0c401d1000c4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 864263633 1250 864262383 864262387
    0x90204060906170a0804060c30110c1c03020307050f0d12061a21040609020f240a030605130e0114091903030b060c01140c2104021f05 59
    0x100c0904240001200b80c9120f0903000f004410703000c13803941000c4809590781400c01c040d01081c01c0c9006010b001070301041c6546001c40c003c1c4400301c500c0f003020005c6003c01c1d0341d40700d084000003420b04035110240810890342c401d004084980900e84407009040149000f40107480c140b060765100d00d4140446103055900716003288038040c00a039080340c0c3c000704282c8241010040f50f13051001b5910004c500d4110f204803840701007110804800030801c0c640d03864091030b40415850800f072401e500901040d0600302d120f124200c82d007035003604040e0008000548003401d80f894411079541403c5035940001e14607004c240e207449010070036071598140440210190500042e1404a09602c0c40c04c4440c0d64451505e20500102803055050002402008000200c182181390403014038090b001064100c0034189c10800c003160480781c0c0c5d4419413242d200c0c00f1454800075a40d80c1c4000c142885071080c59040203000014070700400d0b10741c6840c40425400f83c4050490043d40c0705040303a002d01038810328540030000d140 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 864264883 1250 864263633 864263639
    0x3010c0801030512270d05030c010e1c0203090d020a08013b1002130918020307060503010621020912100c0203040e0708070903060f14060901030b0601050d090204060906 74
    0x1042003d09404210b8006540c207002050400315425124185c202560240d030800004041da98900022520b552140c00c80796540759205a85003e8005c0059512041c018060030914070300300200d04841f0342240380c1c05140380c00500c0c802c010043c0507507101030360000d844001c08501500c00744505405040031040044452040200d4a0021034008400944c2121180c41580ca00c1c200000c00070322140a400000d80c07201c41d164000c2000880301c0c0d004040c035070700700000300c0450030068218401040c001c0e020ba90105803030702002e0f502c9100a00c034a00002d038404031b0810b560b21068a404007403030200c5001602c2c4c04220000a0919152104a001540c001901c5201e543c580c038070405070340c2321942c0081d5003014a400c0780744604040042074038042c8078018000a0320b482c030841502c409550b028900300a82000b5108003401800c0e41c00c000543c10882001003403851400d915146c0c100c2c2da200a0280103556540c0044a20b6040342e0604c10540c1d44a410702801070743c8900400300a0708840d01d0000348585 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 864266133 1250 864264883 864264893
    0xb0f0310051c170a141b0a0c08010e0607050a03020a0e030d08090f0706020c04270305031618030f0507030807120801140307140307120605070807091202150903010c080103 75
    0x20500025250303d40040010020064016a00510141e01c101240e5151444500f03902c50b086807550b038040640c0940c1403041b04015110f11000180d0b0059002001843c02186946666003410350f602008204240032080240d07120390004c00c080f0040e031620705401c41c40c000c00f0070725040c90841c05001040c0300f1000c000c9000010440e60307c030340e0340c40401030103028940b000194440d080d06414900698440680c0350714240319209009200741142d5014240d920541401030080e00309407000d1500c0c00700c1e15601040070740f081903100107641c0c0c21211584141d245071307190f000900308000101e40d98060440c0002c04aa20080a000c209000c2e126550f00b40101e40d80c001c004000c160440c4103040c07101080d203456070720b001480300c042e10008010261485440750010b0325248542c1e129402c86403140341014200320320b81e04182d010320040e881c0e5501c16220100141e0b40c601c401c1c001d42c0710440200000c0d2000d86440303c0e40c60101690703540e4152901d404100400e09607000b091030000842d01350001001002 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 864267383 1250 864266133 864266153
    0x406030e0703112106070c0c12030801050d0c08030705030c010b0117060927010b0a052d0103110d0902030705011d0112271a010b0f0310051c 62
    0x300001404003142540d03a2031008429a1450501803030401041003212994582600d1130045624126031042ca07141800408901e16010100c4d00c0066a6000203403118001c40548040c03581511004103581c02c1c035003401010094000d0170741d0301c4800568000f450f14810310007040c280b0701a00c0615a04c50116030150700b51109001c4150422008400c003084900c0503032250307500100d00b2034011000d5241d00700500c040d000302d501c510350511200072805c501d0341c40550080c500c4504c02e81d080c40c5038540e83c03001c1081143c1d4201b05800000c005500c0340c44041a1203500b4058090141400180640106441e080c107800030350040c41c000c0e5a4501060a40c601013184500070502440c000310b010601400071503217000c41c11080d506118036100040040b403c1504540340c00d042e00c400e0115296840241c040040159540540362044d0030001d0620741e41912001905868448400514011190b141c4910b2a4001006000740303004140c008609643d50354080b0103110b80c1c0101404080d000c60801c40c03040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 864268633 1250 864267383 864267401
    0x1606180c15171510030e031611040b060304082506020421031d0d0204110913110910110601060201020a0e01030218091305010c0215090a03020a0b06060706020c03040603 74
    0x2201042040009a03070f4501d503600f40a038016a00107410082a02c1c0903000390014403c3c00345a03000100c1d1016031105658482900389008030520303e185c00c461814002202c262449480e0808401c200240200351514001d10000040104019148409806d0300c084880d040408484403a000101001641c00d01d0503d03950804545685241601582d13a010348500b99008034103a07072480034030b940d001d5541c1d900b558005603600900241318011070700f40d0202680c0c4c0141c1010744260b21000c1c42c10407205062180d6407500d081d0a0005284c4410901000041c41c034020781d200c1040341d55403401e5441141070240c1c600034050341d0005600c40a20601c0640003001c50640d01d81050f20500075080005600b004080d01e4981c01c0c0c404014541b80c5030b03001c50700d4508140000e007041d800c1504030b100c442e600040710030b0015014215403006490315000786480c0c1e05102406401603005c41201c002040041154640111004210340e1030b04543d640e901080e6004440c9030309203030f0000b0508100c40c64040c02103101d4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 864269883 1250 864268633 864268667
    0x203070305070f0e09220c08011b14070f0609060b03010b060702011e020304031205041401030204080319022505091305070e060a05130c090503031606180c15 69
    0x1445541020081003941060004c1e44100502000300d180f0041d05a00300d5800a5120103500b04020141000c144d04c2d2290322608403150b02e0048005402c1e411510040c039200030300d540b11500c0c20f24010748181a80c01002c0f050340d401550780350001c00501c0c00c8c402c13010010310800d000f140c0640020105400c480d0483d00d17850040034200440d90043c2e17402145141d0911211800c44080c616405089186014542004200d0b0034000000d80e49960040040c000b2038156400c2108400503250045099029921401820f41d1040c403d4058025224581c1a0103180900c103c4014000344000118442c3e650960005007a82c014006e000c0303030401c5d1811390f51001701c010015610228598913156160201c1c070442072810303a5040031504030303552442c2d0070006000c010318005d60f0030042d0030190010000c1081a0021a01c051000030716800c1c04001d40c0c2002005004400b03440181c2d813503d00140c1046016440101d0540e580500021480f400840140010f0301560150500b4080e0142201d40c01c840e030010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 864271133 1250 864269883 864269897
    0x40204050f070e460819080d090602160b15010c170715050901050a14061005040807061e0206010f0b0901021c020c03100e06040b100e01030303020307030507 69
    0x9940043d002d00c0e003194240c40b21070100b004014202d152150060707070071001020a240080c07030102c894550010358401100c2c0365001c10b070b8031a00e0a5590466a480503115400d808141c400324001d500a004d83d002c1c000e4010400e42020380e0b8280803644031941030311215845801c402c0038042001c0070f0350303032200c4030203a1160a004c2140028100c54694400200540210000340f0600205841681ca600d42d000c0703002c0405c20b01c43c91002001d03250407100004691300e040000303441d0601c0b038043d4070440d003402d010250170f5803540300501140d1321003aa591002c1c850204000100340f107041280c50700419951360713040c100d43c00f9481200460301d841e2841c4411544940c005128121001c1a0402180d2107280c0706592103c001005034146000404040413040c1d000b4440c00314180c001c10a402810000c5065417a480c060003c104120b8a0049001a00d6804034000030b00113001100019085440c0810344036415984050000050b0310981040700020303008800c0c883c3c005e4040c0107641d040740c40c0e030800907 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 864272383 1250 864271133 864271141
    0x1303051f1406060a0c060c021e0a03080a05070e030f010506040b0612060409030c0203011d0d052a12070302011413030804110a260d050c0d0c05120301030b040204050f 73
    0x12070050240074a0302c14040080d08000b03044c001c041030170507280d006070107012080046202035200c003103891204403440114a040742c40fa05000c1400764141d81d00d601c070301c18030380c0f10200100c0090070010030901c140014001c88400c25030b070411020320303980401d400100d01d41c503000e002d100075107001c80c9400d40140014004121002c0000001a82c40030060f030300040c602c800d0b41000c032002102614080e4140d46015426179041c0c1d000b200000030b808010080710300308001031200301c44501c500c20509140440c40500c1700340c24200c6c1903441007000072090403a03500c40148c05801100b6400084210090f03903507070b10945296521300700401e034007044040d1149030100f03080e14040d081840080004151507480500c0c2e0070315560b12006440600441e803407001a01481100d030501c00d01c0c92280f0480c035803182e5042c01d1100d40c40345d0200c030f00d10b03400350000c2c00161001080a44101c880326808a4040c0652139165910040c060b003d10b0003503000c2e1486004c1401c0a005010443d44058070505882440d04100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 864273633 1250 864272383 864272411
    0x615020c10080417030f161404030201080615030f01060e010e2b150209030c040501150f030608030d0902130c020303011e0305010603051515241303051f 67
    0x2086644031a00342000c032583e45141002603520104500101088040244105030b1050f00e000362080d0915000f50941119404041d680f1a00721140c8558280c8104000d1005510420031180c010002401c10b492207040c03504446181c0c2c104440b5010b00700400e000410030960701c8880051800c1d0203003000c810070016200400c0d0303c1d0744141811400e044440c482000c2c4584800c00307401c403498102d000c0031459202841140040d500880300c040c800e01c10582916250328281c0302e000d0480e1f844600744c0c041501001400d440e40000309103120249070340c0c0c41000815000034402000512407030400000c125042d44100a2810489052100b2840c6400400e4608640000481c1e055806290703011344044110050b4036980c0800350801450f55007072800c0002000000240000006d50180c001e00056071180d800050a03082d140025500aa02c141078031030150200000030b89211921072201e2600c6240c3d0300d50900510650702c200c420f60310101c030045c0071758228401c2da12255101502070100400b41042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 864274883 1250 864273633 864273649
    0x40201140309060a0203071206080303070e0a2108070803040506270c210f01060f05061309110705011505040f1104090f0212070c050105060603190c11100615020c 71
    0x4e0305440a60000101c4c03801d0740189505031210300040809d210781911822059200d400a075045c2012842c002060a43e51a00d0840c0d402a58080a841d80c80d4200c0104035200301c40809805480c598420001003000ca02d42c2002503110398083d40007800d031402c220440c4c081e140e0544103510310390a0b0008010350b0584c804207401a540000b181c5248a580d11003107811100050040c200c440e80c419207069501000b01904107600f01c401c071064080c0e502d03644d40d05000c8903206c2c0080c04000945440c1d4103004404a590010071030a41c3e114045080c504182d417200c0c212254180390750020703240b0304000c010500e0075000303400c0e054406080510540400261360483d07802a4000d496030b4980314421828080410f0381a0741075001c280e41c0c8041c06041032034008d00000d1040d1402d4985500f400c1c00190a41001c40071280101e8044580e995011038102c80c040003404601014010000a4422078220000800110140341e64540000521a14081c0d501144804c100a10310564118981c0500c89a41e9024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 864276133 1250 864274883 864274891
    0x2d0f050114070e01020d0e061605060108010e0d020d0f0309140303090f07260a06020f04080c04050105010905040e0703080a02030a1b11120c03010501030f0614040b340201020304020114030906 84
    0x3c21f15001103003900058140e0103a41090411b1191401080c1c0510600055560407108480006c00c2280b440015464071518040c0c0060007690243c500401c4242c41540c4200c50030401389400035213458165986d0410b0400d802c0606055880401407102d0540c00340b2000040708800c81c01428200d01d490384440310b8420b0840e00c4a03404000d03000302da10a81702848840f81c0b01342d022b44115590090010303810b0031a003082c025400d40f84a61000050607050600c1024140c60050312124006454a42044040d064030b4682444c90b002d8020b00100081c560700c00740004144c640c001e151114440b0400400007201c1500080010015508550108220b44800c01a220068074039484950304504820f01c0c090001c960b03070750558038050002062114103440d9405240c4034440501c40c0c038000418080b004441550050310007801c20001c0303006024114080070b4003c030f09000c0080300800a80303111032588544086000980d400004202c11981c0c886461410441242000c0d4118242015034580c0d51100070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 864277383 1250 864276133 864276137
    0x1903150b0f0f0318060106050c030f0a0309020406032607110f01020723150a0f1b08040f09050f0c0f07061d01091101020a2d0f050114070e01020d 64
    0x35181c550041e0010884500c1808080d205560341018142a00e0315000e100c0d2580030740c01a0000801c0c05481001128003c8144c00000e60404000303501080d12540003c02100a040c2d8403003180380180c07158040d0a00039130142841882c180030340081107100c200b1140c08155031100400251000412184003800c1032501070340c40019000b0b01b200141c1c540380540e0420b10740c4944c00d0b0a490541001da0020344442d0806544071009103103011851201c902070a03405d200899000d52003d900d061050b44d080507103181411001091040586034482c11754000e400500714402e05000c10f10400f1074500659401c2500c501d60560145048003015440c0d010b262104a0382d040c0c0000d0500034440190080e24002800c0704040802011402c03005009051000c02140d003c2402c132185006980045007036007805800602202050140520445124140d12240e10160b0700d05000344010445203440034025911a4000040c03507a1030344160413003810002c10382000c000c0d40c8d40c20f441459a011502d440400468 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 864278633 1250 864277383 864277387
    0xf10090f17090d080910050a0819060f0f1409011d060a0b0c0a021e0d08070804080d0903050708030702180414030f0717030124030f09081903150b 64
    0x41070481c241845007645950b0f01c200e0386407001040c001160010000a00c085490640030b44840105075881d0140382446000303c0c1e0140700064251610058840c02c00d031a07041c2c0002c038991100242305200141e604550191144032809010402000c4088031904504441c1e800d076540c5011050041050f074240b41d442da1102c02400716901317841d52803180700034102d103850f010340b994021000c0340c0d910f602141e01a8451178a140b0b600411130604024840d12003030142102d21586011380700e545881e40462811118407004001c0012900760911074030405980603070b01c46184901e103007800c0f80f4000c0c0c00d800203411608200051300060741c0f03e0f98428041014107102e800c02e90750718204050b1301031020440d0700e82400001005035040404e00020b0440900c205100d0003d84e20304059800940004d01800460521400008008221410030107414007100e1802003030290482207090142c030b00981c4115140303040032800d121102501e200810241c940c81ca01000700b00202200840030240601c03032490000c00c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 864279883 1250 864278633 864278663
    0x313050a02100309060f05010501140702030307020a0b040302031b01080402011101021608040f0603051504050925030b01060507031403091213050103180c061d120f10090f 75
    0x414030225410903001424600d840d8039407078029014200381d490844900385441c0c194100032105214880c16100e041c0d40316445894401c2d4182400d510005d426a41444140003140040c1d55202c1c00c07101034110785504603140d03840e42c81810326003511466582c0c0720304541c1602c113109980c00043c40764030903024a00403c6c900603203c1c07098024450483c1d01c1c070a43c0c0c900390420b0140702c100801801142c22a858010f0001d41c1d641d002c5080b20001d072450b240200070000d003040c80b07280607040300b40c020035010192072104901c54199644100303035514020140c072802000b0010b104d03500082c1e40c0145a2070501d140760403060754005000c0d414051030a0fa2103180880452540e00c070422080c0e0180301c011100c2c95035401807203000c048c24945882211700190500c8200c0f146111070200c0c0c9100c3c0c6600003030840c0d40c64140030b41905e48100c40c07402c0b5100208501c1d0041d02598980704160304207003000c005403082d0811801400c0c1007440304801c942e2140d08100c15a40043c038090140d488042c1c02001080c10910 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 864281133 1250 864279883 864279893
    0xe0411131506021605031e0f07030609060b090601021507050412112b0807111e0f1c11130606110105131a040f060204080d12110313 58
    0x24800c9200390594a8036003281c849060070003a41003070ba40d06800b01d80002c841c42005507151602e0340038550f01034101d50315007919441071000301641c0200007000e440c06110201c05030b40c030341042d6a1007a201140c4480d292028000d01340301d6203a54031401d54500c3c0f17180c605240041e5642d0a50102c41100039154030016451500c02d1054401031b03c1143d81c15943d1008500f0140500c0e2140c4600d144604004200010f200e618110b01030b4002d00300303d0a854514040b600e070b224481d00140c0c0e06403103804d4404596149580c44040258040c10140c2d01d4030041900320081c44213520301d00c08098011816000150303404240184d4109419030b02000200344e0a2450300421a054601c00c06120124248200403542d99002101c0400b8460040000c1100e56039a4035902c50221004074040e11f0f00f03000562185040384080c4015900c68059440b1048046583e55400b0490344030380e011007801c2d00a892202c41140c1c2c07201a800c5000f09030071051145c00e82c13650710708185110141c4048101d614040c505c02c2008 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 864282383 1250 864281133 864281149
    0x60806100c2301110c0c1003020405032d060601021216020a03050f060c04051008092401060905060309030a110f030f0d061d04030f1724030303010e0411 67
    0x140d804103254030841c031050303007200c04490030794100b040e1035007000c0c0c020640820340025118014402001030001c4058541031090448051000c001016020000401c5549040003c1d11010354540d00a00c02d95022000700c108001d001d1902c0810360700920140502b50381d0004903400078600c80d100a5903541e00703000c3d4061072100074410003034000782c005200005000021541310300e4101d902003681d4460340c0300680b030312561285000346a0b219181076010703e000d501c103283d0745600186079030807206000041d0703c1d2a045604da81c03080c41034546c1c03c06d00610003a41d110803000c1c01484140d692a081d420702d07000c0715440303024400985017005085c5a0f0701030190010000800782c420070800b569078030385030408100712681c4900017448042d820240000b40d074a2111190400b441d11a200703a84e0355441e96901202e1409240c28201e003008100b076249079140f04c0b10420a0f0103181200b1103016800c4403e480313407400540c03011802d0712a8005200420401d10061001e84c5c0c800e070701001190303501d030440001400e90 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 864283633 1250 864282383 864282407
    0x903010e0a0602030403091e0b030c04050909010b010210090224071b091808121b0c2503080304030c050307060c2d120b0f040507050319050106080610 66
    0x50720450500405100080e8000c500440c000e0f80c0b844086a15012400c07119585074401e418040c03507900c002c01c10140f40d14041c6400443c1d00401c0ea00c0d0a5035030300001e5403031105135000300140c3d5650349012540d6804001c25000c5803c7c0c204248243e03001038001442030103000c84403030040c842c1200461a20380b110811502d4103a8060611840305076075a41c1c034440c6002c41d0090006403031400303410864080f96070000d8903c075a80701d0360b198604800c1007841c1c0c800c2840508491103165134144a51014002d0304054040701400c0380045c8400301d40740145200d43d6460b82d0b02210150340ca0b0b802400803c560b481107030703802601410248041120303072900f5441d612804001603c0b03d481e11100101150740b008140804601c1050b40da10008110031020f8041d00640c0125004030780c00071010340c0360101030381100c40000401071004c010301d00108081000d80d4001c540d40c200140000040204d00d601c4240b052036a4101490104400e60400c80d014040303c4010702042d10074000c401102c00280d1103107543c0089 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 864284883 1250 864283633 864283661
    0x709060c0c050d2f09070c02010c081b06061c08211305061f060f0903200307060302071203051807080f190b01060c05031312031d090c090301 62
    0x10007522400c0c4000d000409907482d0941040407018a004494441080880d5450003030049245e071310303120819070704002046012418030400d203502d01c021402c000e010f07100e13002d8100ea07010240d010400c0e1441c10894003e0440340b007075020a5141e01e50b0403204d036291040c1980100c03804d9403603100e52a80c0c424105034100f910b102c21100810051054a8426070f40901c62045040718a03c1d2202c3e50706521021030990310110500034004100419489419000d0024410f400c042064940320f0300c680449003800c00022400c0751000780d07154401e040410051004001d1481e08500b07049051352a0b40c0b000c0b0946c0c00c24010591034401040004140c1d0907103050545181c81114207866503410540e45814a01c00408014025082c003c4a41d0403000c0942c60b83c1c5610400300e5a00303030708103402030340c0d82c080068040c1d8180c80140094252110b82d4400e00f400703044034903c540d20803130451030014098802402c3e40300840582141142c1a52509502c030307a007191091922a850b2400c0030046401402105c9441c04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 864286133 1250 864284883 864284899
    0x80c07081c0626010203131211010509030c060c03010b0409110c0d08070e0a18020d090506130b01060c03020c0d1401090c030b09030942120702060709060c0c05 70
    0xb0f1800c0c80c601c000408040c0c003d5400f00702000b291145080340812602040480361039000c503400650341404c0d0302e807002142d050010102d080c0d101d0309421220100e6450b80d95510000d0503030307402d0908004180e07200300e00d81000344c0b071507040c010310f00700ca80144e10031001c0c0f050300e030504140c07851008800e41e5a10000c1c00c044a414004480e0000c4c0440f50a40d0a100071174000c1004028a0924004107800d80c3d02c1c9410f00d605800f2801c0c410f100035403040d00100703100c0750b680004d84000f030400c1c02070764003449821080d05240611414a081155410786c0110140001c0c02500300000f900441e94118a2104a4580c0307400c200c079007020580880d007840c0c0400b5551030020040100072500f11200192402840c1080d003030707940c06444a0750b078420700c00400d0340038411681058038107204c2c07a280c5001040d500d0b015091a404940c02070002032040042c0c5115220101d12050480341c0700404d6603010103684018681420040ca0190540d5514080c03003040100f640f00010910141001d010700502700580628 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 864287383 1250 864286133 864286139
    0x150609011b0f21030e010b0604060e040209040e0a0c050319200909010e0c0307030507030f17040902220302100f05070b09060907060201061409180106030b0603010b01080c07081c06 79
    0xd100b0f0607064100300070a00c0d2180198804505105041c800103001d445c141c906400d00d10300340d60260240721030581c4a602004044500c0e103540c081d07035031200c0308080200b26000582c5040d01c0c0c40e03e002d4000a00984c404440c0000b80d4000381e50b900300304e03500a4410711903a01c41c0785d11031218524851106400403200d805005000e0701c1540101d01d542c040009a40382e4038650810151103002510011301140d004102c01d002180180e918101c3c0c1512404220101c1c00b0030320039030072240d009684061001a8081240300702d03142d5034001d08142041010110700c0c028215400503445801180301d900400043d0030009051a0188080f54480c6400981c10880381c5012480a0342d505030480e07420b2042e003e80480010f00703134014001c031011b903521040204091000702040c4121054000d0003542c06011a041c611801e4800384100d0010314015000c004684c40d00106060a40d060035054130304000d0201c3c1004540078240c01620b009507444080a0f036202c6180d101410020b44441118a080349066000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 864288633 1250 864287383 864287423
    0xa0c12050c25050904020a152307031b050706050d0b0d2604080d1d060304060501060311070c0911040f1820070f060e030a0503150609011b0f 62
    0x3000d4000b81c0070075907085464940b800d101c964181030702c1c02504a14445824080103d4901400072040b1484c50440c0e507080c825101c0c01050350483c20410440da03000106002415801894101c44000f48500f15489034116035800780ea400d018400c8004211000c900540c1e08620b5070010a5454001080b940100c006820106039500420510601115007e20055071054a00b019103044400c100c02030081e8013550001540c0120b42c540000c006011081410039a070360f10350002d540100d024060006540d0305041c4003400315007041d4840300c151031051103100300286000c41c50009681c0001d10100f110101c030184000d6a010395000301012a18918010074203030303c100303210280010918402d00610340c110f5503041e00c01004203544c405001c402c21081011869100c0b8101e2800d102d03e400040324110340c41c4550564011200f01c200107032000081c000c1c1440c03020100050300701f04550040c40c0210007000a00b03004003101e01b00c10203400c0e080c0040e00703004101c043c10170069003040d5100581c407480012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 864289883 1250 864288633 864288673
    0xf0c240f0f150509040f03030b01021e030319201803010908070506060612060607022d03010f2343090303020d110709060902041a0a0c12050c 62
    0x6480281c1d02c80c8103000030f03d0302d03140720a28004c5030002040c0c410340502e910201c001d401d8088480e0306500c031780c41d02d1020448540510b2141c02d2082c10207503840341010700c3c0e440b1456104410801c000703414100c00145405c684030206800400e810707006540c1d48110300c01000f8542804d1201c980c0365113800d161505000c00e1030010a841d5100304180da081360f85c1d00040285501415083c2c0095962003030018015003403640051a17054001046101409014040b511a96814014285100c500010071400780c2c1405d006e960320403040c080e07041c0500078900e815405a82002040c560b040c050190200344902000f060074500313050000390340e0750720365066a40d040545110050000307801d1f4400318012581da00c11107a10058a5165001c1c2880c920380349821038041100420421090003503000c006001d01c0d80303101b805c008100ac0c00c00561500d01e40701112106c0301288000405000007080000d00c11a40701d06440c0032550710000d805001c0c200b51170210f0702c0c1d0058140b0b03019588181c90b0f10316090032481742 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 864291133 1250 864289883 864289901
    0x31801031d06011d091c110a1b09063602040b2107080708100f030507030303053702040e040b01050306010807060507141504030309030f0c240f0f 64
    0x44c55210100a400002d080d90004440201003900480c1401140342e014130408124500c0c6407034100440d00c1c4000740c050038403208500444442200640450f80400000e01c168024001110704200759490800141c80c400c080b1016010410900e503020560b02c143c0d00b0a03c44607807424034046495580343c5005003905c1e030049106029910400550195460043d03054511508866a50b0320464890350b070241e40e203004c06040e0761b55009081401241840c81d2000171001907024800908503070341345040250403540040c10740904090308602203080c07002e07906030b4208581400c2c00c0c001410703888003075204001e0046801801d4048500e00070700c0305000d40307554981d0581e4411006d480b0b20380d9030ba56502e07640707a450b0302c41c50002c40c0d0280549004914404c1075000000301080646880d0b0340043c09180110b002101c00300c003caaa280703402c005050740071b003c5c2c603900c04503801c040c02c0311501d54640c0c0a101250304a0031203800d0101c242040040616000701c20114000002400100d01030030a420107001d00741 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 864292383 1250 864291133 864291149
    0xe19060b0103200715020c010f050a1a030607123801020c15030a0f0603030c110907050327030c07060813020a0509090c031905010c0e0102031801031d0601 68
    0x940002c440ca0318105180c202034201c000380c0c9044c4240d075503550b8a00300b804900d01216824054240000f0007801101c0c19a00340c0203002410780b415048050840e414402c8600788041100c08018660305c00089080e001016414140f60590f01c0b80080d42c06040460810307030011028000382c10100c0c200c04102d5040a0002944110780007250b401240d40d80e28180b078840d841128180c904002031400030040d40c100c40c1c3e205001c60300e960000c0440d000e40b400c2c1d60040300003403409135061060140a40300c58009442c120307402d10145c01c0c1150003e1940c00040c0c00f01540b20b40550140d03059401c031040c038404011092090b651a0140d000c2041d0f2511038601c500404210f42c1c000043c0c0049031110600c0900b40c2c0100740d5a111420113052000c09900100481c0300c0d403042c100901d0302071b64200039080c1c92140542150184220500d082400c0da1000c00d2407000f40807440c00220090380e004019584005000900d80e8000700f5240012805400312191110321843c000306510300d07440c404524581641c0c0c01ca = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 864293633 1250 864292383 864292391
    0x3060108092a100201140a150302090727030203061b130b030a060b030919030c06060e1509090c040b1c06020d110f0f071515050a080a0201120e19060b0103 68
    0x3c3c41c001d9003078600018a46a181468600041140b48540d000c504100c01c841170485c1e41984941c0400d04200d8161001400b00c0c91000c1300b00040d000504042c2c000000b9500943d0b0031620310b5004c070340d648501030103010340740750040d0000e5200f9855800b5103910002c00300c4824101c540d520a4200141c2c010755545131054100b034004655034510f802180d005030010001010040e000300c0310812410b200b128201c0030090300300c0301d143c0171031041e0280c40d01400c41d9040000c031074240039075481030510501c1c03030710345c054500203040026050020900d008520000d40700031a0140342c84c030006002041425941e0f01090404000c00c05000907039019001c510100345080000447e40090103903107015120507403040190420003406101e8442c00940710b6980703d8400502004141201501910100d007003054503a05001803c104501e0501201e4000f4182c880c042c00100c40c0c207400080c03a241d003642654150f03030707121252403000400c10856400a145480a41c2d0b02a220034a40207015000c40b01c10180000c2c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 864294883 1250 864293633 864293659
    0xb06161b031a060301060803040b09190302030d0e131d0c0901031e11120a11040203010f05060f04030501050702060405160e04140c0411041e0b03060108092a 69
    0x5184155054a03041040e1004403501c10300d0b90862110b00804494155407070b0000012142d008101402c045c0020701103c54880042d2414410894203107803940940426100341000980c81c0850300c003060000707074074003110180c0200c004660385c000e03540030f0030541c00d2078148507003c08004c000454115170030f040191000c0500f60400c01089032402e01001d0700d07a40c203400080d001e64100350742e40100a0320526203c08061701400008aa402400c422000203410440c20742080001d030a40d01d54107201c04440c11411541404008080403400b8001c5c3c5005500014042c0004500e00d81910000c5034401e000b030200b8980018001c2d01d5607800d0310100d0703003480340c0740601c54460b9000300c8030010303982001c8903088140c0d00e680f00e1056010605103607034024004e030303280608191070b103014090303501e2042f045480e81c0b54030b400310030450111101b090040f2801e5144081c0b18042c0318400f04c9400040034603006c801d58407142011401c201c0e0002d0000c0b0707150900d46a15603202c42c1c000030780100c80c030211414400c60a03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 864296133 1250 864294883 864294923
    0x30f1c020901170a06030209040f031e080109090510110c0607020606010804020f0414040302210306150306030313030c0501031b020601092310091107050a03080a0b0616 74
    0x1c0d8403489021800da007103090701c10b900c02c900031548801c4405010170015580c2d0041251800c2c03d031800c3d205000c9081ca05002d041c0c109041365607581681720644030890940e003008041e0390040c02031114580e200c9000d04180541088400560910341c0010424068029034014655015400540d0a4054540000d10442c000f140091090006845400740c680c0c071503003041120b007030050b80c0640c803a036241404050303603c480524504c5580319400904c0c1d00343c0b941c2403800304a00c96803814104040100108289038466480780c1c46110003480c0d03600e459468100c002410750154104500005600380f4000003440095440941182c4003030701d00304008085540318104000c2450320490140e030205004100380c04403580985011200203c0080301c580d03035601e200b0f031200000c4d100d001c5050720341b183c140203ca4262213000d00800b00b00c00142c0c84c0000550780c4540725091102d000d41400b03944000144804044e401ca10700c6a0070042c1415941c035071825032601c0440752140159007480c04181d14140d603803 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 864297383 1250 864296133 864296137
    0xc060c160b0a06470705011d101109040207140d02010230060d02011112030108190201300615180f1404111b1014060d14030f1c02 57
    0x40504880d82c43d0381e520412401c04d0079042101614060340080104070f012030341c02e00c540401d00c04100308100c140c1441007040341c41c1641c9958124645440c2c00c10840c42022218125098188261009038a400941c01c01c1c0e603800141c210b00601a024015075040fa055040d40240443c1c000700c030305000e00840f034569002c081e4044c1000c0b035007100d200f207001c5400b918012103c071841c3c510500d800c0c440003030017021083c1417507555655045d1002006c401400068814007560079a908000000ca04810058000801c00d42d00854002c9000c610103c01d100705041c0038030021041c50312484240003240e515565420a089000281c1002030b410f24111000301c54002028411030b01c007114800030007800c00c050402d5203601c02c200d5075402942c031081005040c00341c3e0003a00081403085040758075480383c0030816090441d0f61094100040c03401c10304a480c3c1015424003a00000c0582b4802e410704900d184c0402c010380e001c4407a0001e440301060400005107450024500b110400a10840504414006030264 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 864298633 1250 864297383 864297449
    0x80c010806010513030821180c211e1606090b09030c040f0c0233070225060f090b07031404031e060e030c060c160b0a06 53
    0x1481203011074419840340c4003034800c2c008045034448003a640c07a41d61090360f9105803207400f0008059040c6400c840c444192540c0c2c00410070500e11451790311805c84c5510790506403055481030302e0150482542c504610f000d1010703480c4580880c0c4582520024120720a02a008454a24401c598028201c048104008000c40b8074030b88640c1c822a04048000100b600080b0500b134051140100d0061b031030380c0d280a2141500d05280002900d1600c0c1e0000030304016665103e0b011000c2e03d0314081c0e0140e100d8028005c2183d40c0c81c1c2e400302c11a11020002c030f040041e512314650b00c0b44440c1c110940e4601181000000f00c0c1c5258440240d0303102d20b041c0c01d42e41c6181d03034420307000381e803506000d1800400c2c00341000d4900d015103a01c4062505489548190115451500004190b0300042c049010403107644201084002494000d42c10501701054180d6a00301c020080d020303044000c06d807d02c001c01444172403d21541e00464001c0c070f624009220000400552142a007290782c2e045241e880440191510b07119 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 864299883 1250 864298633 864298637
    0x1b08010b100f032009120303040f060b01030e0a051b03070305070315061e0602101b0c03210b0a050105030405030f0a020312010b090118080709090f0c080a0b01080c01 73
    0x40700d04180015169203a081d40010181038559220402e024541c82c0154101d410082e452034690048406100c90340f4034001c45090540c1c8200b081c07101040103840d884050540c48100442c07003041801c0104d025010b01c880c40d034941d00c80c80e200681003150200d100941003000743e4034500000042e00070155182030521028016030429a000e1002c00d10140400c01040b0702e8403030204020b40da03201d2507400030f00700d0300100306030190301041400040d50620007072030354259018091000a07034150700da40e2015034841d200c0c818020040845020103004004181542d00f10301180c511010f9440810f1002e81002100705100b091950340100d11580124262402542c000d0002d5050421280200c0c0040d8414034070740e0158807007400120550341140d2610740c040c1030b841c48070640b5032150800140040030302e0116106203565021040c81001c1c40003034040215100707802d020605050b10300301400e5952640101034a20b102040b00401c16400c00215039001600c20004501a40e986030310f03040d21500c2d12041640 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 864301133 1250 864299883 864299899
    0x203040b07020441091605092e14030a0b0f13080301090605031603020303030c0a1106010e0115030218130e07140418260f03041b08010b 60
    0x2025040c03513400661541d500f05007005001409441d0000415442d080c480100102d090004160a200b844d1442d0481c1e02603004103400989a20720500d0142d4500825008185070b00c00135261403d154103000140001c0d0409071780381c48020b0124664485203000d809031034501080079a015050000e01220b0903900030b16810003946440f41104409140548680948107072088030b80041a90603004500802492900003074080ca4001454184494500c0d4528801c604050810142e1004000ca07a0300c001c108404581d601c03207079081590152202060140c4a114074030002c00c03080110801c2506903200892030119004000720100c041c2e01c80c0590b00e1140b00038050110b0320f2424406818610808031940102e100b643c0e03035583c2c5242c0410356210201c0300c02c00d014194007504291040c455042c0c405420041c0c403070401d0f120450111100d03004103000441402c01e20001303c0c03900003918905103000580541d04c0c10304d42031003042d2118210100480300543c0c000011266414403a80faa04540030701f05034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 864302383 1250 864301133 864301147
    0x7120e04060602013e0a020a1202150906040c0911071a040203152401050903060a1401080f12070201210605010e0a05010c110301061502030309100c020303040f0203070911070203010c0203040b 84
    0x30b0941d0881c021001c00c2d4400c1c030302c2007400900c160009999440c1d107903000300003a00d89a20bc00381c1c0201c0140481039150006030601010800c5200000181c0b4803811010401c40e4007548000c609107e2028080c04041d002d0f5407100c0001030340c01c42140141d008031300300c403503101481d0041e1500b541d06031a150511004105a141c45458520700c0b03c030b802d58141803a50401c1e1a04000c68103140c812500283e80355964a9080c8410076001c130740318090075010008019182000c0c41441e0f450024220280086401050400071688901d48444500c0344603507015450303c9a130300c07031100507000a001d114040749101c2d2403083c5904040030108200d40c4160f441706203003150350300c0301d44401e1100100795405d552a000b0108041e000c407140c501054150340c0c000c5640e0320f41040b21070309090810a0700a1014144064202c81d5540041580c0d003068000784070340f0491030310b4400a407038a0000d82c001c020f164146011041200340c400d016040d0380d4002c0d0000e104045407003000321b841e0303c194010501000828040c070707 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 864303633 1250 864302383 864302501
    0xf0608030901051c111204032d59090403120902041107060f0203010602060105060d09050d051c0516030b040605060d0203090706030b0607120e0406060201 68
    0x5600c1c00c00745110004480e00e820500c10895030041c44100706d50740440b801c0c8802c0552080541200c141750402002c501049134034014114401d0340803071410044095803911031450b42c40240a40c014402000038506660f440c6a20b0070070480e04c1301642039410252401e03a0549540c1c4103404200e030020040aa55513881c2e80c03c1c3c2e40d0020f030b004e00d240c41c0c0c0c0c2c5e01d0102c2030041c1c031548950910301401c5c07048141c840b03016141100c19500c88461104030103006000420a25800240b0341e41501c07003c88000d5100c274a4200b2980042115410180c81071007500e00780c100b0f2981100050454905c042e48154002c2c801400c101309555069400140d40000d40414201251013541300443c2d54000078004114550344400203159034005100f0402c000d40c0c00024001250000c0003080000e2000381024030a02c1244000218103010b04070014200894400003200716512400e03100c1e514020040007001520b85440009000b0852044500041005501c0104c031a0181441140725416518200c840121a0a400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 864304883 1250 864303633 864303667
    0x7020307210e1306090f06030f0b090a0602070335011a0409020d0212061507080306121e250308071b09020d0510030506060d11130f060803090105 64
    0x169080000e200b1400c1400c0d6210800600c0c05009001e02103885401c1805100403030300c1e1030b0301800715503145c802c0810004900d80c4549070b080d904903c6d03d104039a20801c805003403c20304030008103403500c002203100130103801601c0416203003104e02840ba54503030420401c1c0880e118150304081c083c080e00c401000060840003c880024a00c007091604051340c0d008444243e8220000d0110240e07004100c9407440c20390702c0704003076006100b110a6541720003808035055291090290160050500000140c07040d112007100800003071969040f100d940c880c1400d106d1410740409091055070095100a0a860040d121040b814800c0100d1000340c8500e15651000f1640c800f03601114468000c03090120032040003500c0500909014001680d11081c40c812603085a1001f407080500030380b01982440800c6002031402e80c810411f07900e881d404021828020140c00710a00c801c0d9000341c1c013400c601203c4a15420501007012500c8080c0061512416041e840e8064004000d000890074004808002c0b80560 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 864306133 1250 864304883 864304943
    0x131205040801090c090e0705091f0b0a020d030e0f0c0d1407150f0302190806220c0201060e09060c1b0105130308060927070b0c060f07020307 62
    0xa110345401d0380d420403a42964607142c42a10340c0341c00340d4801c001ca4010b0703025003801d921900c809081410304090026080c8180549603210801c6180d04d102031041c00309401c10301074000000942c1c1c07100c038210700081d5940e2030548076500181c10a060401d54000003d04440e40b260040c0c00f070000500400d003403200c1c0010114095810158941590307021501c2800588007505c4c645207943c043d00001080a080036005045410416104106c055200e040540c900c910031411440d10020b682c440c81d00284035181c251302c01115a821a0340104086c0380c1c25801405400d566800034881e60303a544070422003020003200c80910030380211000403141c501c500000c1007917080070314028100314850b00c0c6080c00c440c0304852185c025030001514000740754008100990040e0202ca4641e11480e1400d0307075001401e6018107c3c0d042d0b103c4840045070255041c4609809045108a8107031502d00b402100f960350201030301d0150141c104a0007040d41203202208884541ea0085507081c1c82c014010804211030804203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 864307383 1250 864306133 864306137
    0x40209070521011517010b121806010602100f09120804030203040806070504032f0f040b06030a021206011407020618100f0201050105010207120b04060212040b0f010e1312 75
    0x342540029400341020078080d012110a001c2889940031019000d40d2100000c01ca10417400310041001020501c1140c03d10024038100d1b48079501c0c0c0310700f007412a4030b5a108080c8203002c4c0000215038280e000401c0c1c02c0402e01c0b60024403000443c400200210b07030241070701411510340426903900e0076000d01e0750302e17800034860f1044919243c0d96200700d9041200075030322000086e00c00102007041c0021280462070303070071011034620300c07401c10b406070820b900d8008901507010301c05140040407159070310f500a044104018180c01d96900d44103202400035802114807003400070950307004c14610f510405c06d0240441c070000700c0e180351500756000c0103141d0304075642c0c25903024034801411146856400f200e07407100c00301752206a00441c145201a0035941c0c144c1082d0704640c000e803010801101100d148842c116080064040d8030b032036a08140b0040c0c812190442c18809810003400100b0080d400e50600c140003414040c2c000d07980720401100300d0799041d154503901c2c5c50300d42400800304401c0c00714a03110402e14 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 864308633 1250 864307383 864307417
    0x10c08030c040b0c0303010503010f18020d0206040f090b040c030c020d0804080d090308060a081204181116140d05030f0702010605130e070e06010c140a05161d0402090705 75
    0x42070060000c2d401a00d001d500b5410110040019003424000d2f50349110765818144140204085001c0104080004c080e103d00081510350081d0b40310001241d0180c0b0945051480b903d850f00304103405000707600130450145240c462101d480d180b00f445010740d800c4040e80541102c801d050421201d89802520555810b841040481c0c2d50365400d1040c080702e5407080e1240c180d076181c61030030440c0048084d400b104241d005074040c2e1b400030011008840540d510700c14841c524160908586000f0044e45c40c2002840f100042d00ea00c010b50306407403030040d40340b05d80809102c201c0c41c41483c54607600d1a41c82003003ca04180f001c0b99058a140880c681d200c0740602c00042e40e2540c450001700880303070b01d51042400c1039440609000f42c507400d020100252018218966090400c240020701e800200300d400b4004c500705814000d003004050100500a030340002c01c8501c10040d100389105c3e0003c0c1031007030701014108689034040002c040800341c0d20554004041408990300c0300000d98280c1c0c840c1003640c17217101c86 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 864309883 1250 864308633 864308639
    0x6100b1c11030703050f060901030203030a031503120c170c1b0418030e030106171b0d0b071e020c031f02160510050106210b1203120a0515010c08030c04 67
    0x103840091440f42ca80d0380d0b004941420001b58103170601c10041c00d0f15009800c80d0006101507280001101e0241c4100d00d40040d0142c01c41c004880340000c5a000100440003a1260119245c1c1c00004442413500540954156603180503911200380320351842d002c0303c1c0d000540040000403c540782c1001610000e400400d05107125034200e0100c880814088010542c1160159100e0030241f091030060300c04110406240c000c480703ea903580d205503181000003144045103143c600d8907072103401070707205074040c4400b00c4034282854050100c5030f92000c1041d0650045040c50000c0303100041c8031419042c0075000c0c2c4505541080e480944072482c44242203140e408115403c0003848045801d68070388d0251015042c401d00840e5500b080d1001030b8410010890441400c810200d580481c80c80907010001c0000b419451000c081038028103080800085408041440403481c89c0d401701c5548603400344401000f240d80c61405010022890440703003400a010f01d8a40740010b40c4081c01980c003e030200c4100e40c02c0ca55 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 864311133 1250 864309883 864309911
    0x4050c010806040f0c03051b09030307020904050f03070623011805101806031e0312020706110304050f01050912072607150f020f190c050304120506100b1c 68
    0x90a2004400000c1d681d030b08201002c000800390703010703208048401c07274503020204000130344c0c0307000d2450081e214409041c046010010100001030126031050b00f540d8851006003003e500400e52101c5038162038550401241c0e6400300c44002d00d069581c100c0c107000170511003500340d0005110090030381c00c0d84540e110010030003440c4522000c00c41060940082241c82c21441c1181002007046007585500c400e2269420000e5000386182c40c0c1429684401a00c81c0c50604141d0041c100280d2000c03da14800001e0000344000407900d10340e03150300342c4002e101c2501c2c0c00d110303182e0f110b01904020a50031008c4c01010700042850301014882c0d0900200c240c920703d0324130003100440d0f00ad05c104845441715034415121420660084084090080104504111402c02c810340c807803007400a4414881120f0343c510302c50902a01e0102c2190750403004503034645440d004504220a04032000b6219403142c0c0380090b03010040c0483c10000c0c0c0741b500f00c0785400c2188503542c035268400c080da20400000d4a440c16011044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 864312383 1250 864311133 864311141
    0x2a010e0301050c04030c09020906070314090a0329190c022103041424040203031606050a11130519030f03030506100e030a0b130204021b01050f04050c010806040f 71
    0xf0000122550351461460400417505c031940c04151460b0040c400020156a204255452590503041040c0240c640c8032600c4858400d4204440c4d22043c041c4010040c01202c0d040980180c01c200034000c0c03100540c0301e00400000046400e01a500d05a003441566015103030045c00f14690a80100c03502101d15400b1814035424028110401f00e20210402061000c4100c94142c11b082000241083c02515011000c5441c010b805600340b2940c060302050031920208110380c400a0f8801c0600031800f90381c9004805800265891441107040200c10b040b001c0443d8200c901d100518444514494a03100501206605001c4641107000c0140300000114080e0340f4000d10562082d0340c005002c2c0350080c20020303056989044081007104c0d030341009080342c82c009003d2902e141c010380d50136030507590403202c12001d03208114000c1d00140045120703681c49010121582584510300c00038020390395102c0c14620425002c96000e07180368407550b195070842d40aa0880b030741003500030f0404515a212844a48269 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 864313633 1250 864312383 864312391
    0x71e0b0c1c080702070303081b19020601050114030103020d0611030403020a05060f091b0402090622053a060504110f0102070b0f1305030105190e2a010e030105 70
    0x1504003441c80700d1006030445658034003900e01c0c148159a0304001c48000c1d0b139038003140002400d100d1804089290450300c07403018003510034080c51503561144020240d612000072109414050720039600085110b60050500018040e080d000c654116861034080042c00320090380c081e0b0b19130350341e00305000d0401094001144120b002e80c000700544001441d10a180800050075408001c60103010300400a001080e00c0d4998084290307011004c000c91000a0000d109004805038049800104091058003055500902d802c00d680c480080503900d10900035030f40560860342c5140308001070007040ca8640c2d02c5010710000c51210039130100c50900d80e40d404c115036080e2401d175081c40261b44840002e142010160801da0000c1c80500041031800803800b0880c021000340b0064080b02142080d403000c42040d0890003003a008000380841e080074652100c148408081c00e001031418001d1120300040e0004510721100d40307021883c82c001c1080500455881003114400e8104400400ae008043ea000d0017241c3c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 864314883 1250 864313633 864313657
    0x4021b1515150d020c0708060108010c020105090105090a080705160b090f01033b01050109051906050112110d1a100305150111100e01050a0b030a05071e0b 68
    0xa5003046100e01c801c0700c8111050307510412504450700c403018010001d852802030440c0d0050b80319500f07652140d0034a0003981241c02c0520801c0700000c0c807171005400207135184240303070000c02880d02d4500c1040e09864084403030618540c0101c0d410000a0b1442004081d068024000d5980d080110302406034880d0342a4045400e1713000c0403403015510f03d040b0764018080308090804102d09000c40740c00c00360011500e02c9445007c0f010640b8950030707440400942d6012a07002000b045603603100c4107080c008000070340320ba0709140d01a0712040040d010754401c80054580503150042c0c0f503d40c1030040c03000b41c02c1d017450440c00078205024070081000700307000d50100100f051007002291101a13060000042031601c009041500302401e100c00035040071100e280c0b00e2000c0c40e000000303c9611a40500e0105803074001003140b842c0c00b1200c69a004191b011a004140318002071204c15070580130596a0080300320090400e410040d02009450031000d82000211000c0c2c141ca04c1c1c3d00d80e611512662900a000f400e00c0b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 864316133 1250 864314883 864314923
    0x40c180b010f0804020916020109150911060f030f060a150f020105100b030c0a05070213050403081b0306011107090c031e090b04110105120103030203210105010c0204021b 75
    0x800d982c00041040b88401c991611045511300340c0c00080d040c0740003500c07142c0010f400703403c0441032602c03c2d00903010b06500f0201c046101000c0e140090010302604000341c58a02c0ca81458014034500714084900607040c120055041d525584010b4a5947d00a0b100300c2e800b1411240018544140c42081d040300540d5450303140004404034006401d50b0300c003c2000000503204007060146401c10419690032400d00804140c403288100c00030f4a0512485030042e42c80448112000c160200c0c40c0c11451040d4400e95450078162074152a588005108048001c0012010300019803a54410040d00d03d1003d2403008a031701e02c540d0384082004440740b2410600c002900ca0b803054500c203804080d4141c0d401c2850604101210603500c4103041684041d000900d035500240c080340482e032240003078603075001007003402500559492401039525881803180e40880e0760040c540b524600300740d0444030f0480e541a120117008070b110390b08100080d80304c0b810b9664030388000703130070f041200d0420086d00e199034614900c0703d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 864317383 1250 864316133 864316151
    0x307320102130e130609261305010201090209060409020d06110a02010b030304030f0f0305220302090906010e1506040e070818031801031e290f0d0b040c18 68
    0x80c01d10b1090304101040070101d01809844000050941c1c2420340140001503010500d01c2c1608a216907410038260351952410945140400030000b00211030102c4445008140d940006900340c4030352410103580810f01da00000c46132308240d00000050b1344002c4c6003148404140e500c0c20104d44101184100c141c81c00f0941e10100c2e40c092280c020084401c60045080602c5c40d03035500d0301501e15560090448104080c5402018000d40540d460018101c0196954416000e0300b00c01031101807000b0780c403420000002c5840c8030004204241a90b0320425034101e507681c1c00180c0d44e0b040361001c91180c1c00c21801c103c00244c03082a81c040318050102a500c06070103080507045140b48a0703015500308410f4204015040da005041071b495074031041c2c282404249a910700d11802115550056803240160070500075005880c60141706040c40e030504494040030a405c0400c0c08010a5410035268015541d03224103404568800503059105104101e24001180c0301c00c883c41d070b940b240d5010301652030340b22008a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 864318633 1250 864317383 864317407
    0xf060e030d32060d120513090f0f09052802180105120601060915030b0d03020105190b03031210050307080d0224191821020601080307320102 62
    0x50b5040350541c07007052201c0d0802c1d80c00954501688500103088181e034100c000c1e04a40207409843c030b07100340c400c540b2a605540c2e4000030054403221118100003890030b03884d403501a60b184500140250000c0003811003810704445440b0351451000405103100c030120303850700166642c145032074900c2c000000b21012540743c141480040401c03401100080d4000c1401070161690207103c4000b21100240301201c43c0c110650240d0041440110150300000303901c10385024150150448d6000b00c0d4842c041940c4841c510b501402114011080343d41d054004000041c00030300d824403490b130411420001c001100c2c0d51000060f1900060340e11200c0c4540000c0400c443c055018041144a14141209000302c0c4440e07018160300c0700300051100c628a46100d44840901c15164003100200390051401c0104011504000b074007805010148070b04503c9103030a54440c98400328080b4100c804942c01141402d00360f50b90400818100038401d031140c1217450100381c140d11800307214090f030740801c000140c1d901c200c2c0400c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 864319883 1250 864318633 864318701
    0x1706060103090302190804051e0f190605180603040515060a03020901030803270f010b030d020a170915030a0f0606020705010c060b09040c0f0807030f060e030d 70
    0x1669041c145003010220120743c000ca428a400003d41903201131400c001d107040100d038040d0344c200c2034001c1c1286156508100f00c004a404a00c2c0c0100c6032070980b411032800b04822440004068610540220800c001c0d89000c0c50240160014517050300507440e240030702103906a00115400e440c03591006410401e4103510258598022200740d07210003d85d8119004030341e28000602c401801c03c1000400254004640c00c441c02a0400e03100306100614142610265a01c00220807070a19510300000d60903070b172070b0006400d06580d40c40c0d00508101c0001d07440d4040349954040794245190300c10086081640c2d2614000b42e074030b100d00c0050f01d8481c100103110000711106104900456403034400d050100c0d9400061030030841e20246801c415020a81c94400041c0c21080c1301650048042e00c00c1c07000708031484c5088410b440c201700c54600003d80e02e800c940d6517064203105c041c060106401055020445075000030618540402c2181e2801c5d0940c0320704000c490318956a00c100448155491440c0306d0003d04e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 864321133 1250 864319883 864319891
    0x9090c140a05030103021809061605091201061802120705131d040c05040c081b0706051306050907150c063305061e0d0b0319030207121e03181706 64
    0x40c1c0010740e890501001680d88501070105cac04800451450541d540c3d01c80d2003181c400c6100a060401c0350115019030710702074411401101001410f1440002c000b980070310a0b10601a1003400003081c917140c8060541d003aa00c4201800c0f004880c0304808a10f289000c1d550041030bd4801c6026817040c505802c0c00702102aa07500000d103d18204a0722484c00c943c0700e240941c1100010301c0c0845100c00100e131070603a41c0f061181c0289800e040504000e0904180c01c000d0140034050f03901408130f0790781c400105848145074020090070301c2e40c00324044810703449242e030111190f06c0b0b200700281d10550035010b500e0240034150fa200382600c0711001003034164030140c0352400505050f1a00390a204900c8c0c100d03035200400404a01313404201144041d021026034018445051025090b40d220200c01d0180c910341400c141403d402507c100400003030400d5189480c0320405800000c3c880300841840d420160081e0b240c9410b504005500c10f0101c030904c02800b42030024885a11642d01071101c2c2000603041210040c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 864322383 1250 864321133 864321169
    0x40321031121060111190203060f0103050d0e0a170606040c0905010903030e362d09120d02070c090b0108130309090c030501050117010609090c140a0503010302 70
    0x404100401d0041c58049032582c0072421100007540e8a200040f00c0418a14103602018810b0008856000008176507541005000b0b8081e00e040c0e40d6a00d03202e13030f011807003840010b0003540142c048444a6200d400c4a8482a10042c034028006540302122282c2103d800211200d03504000140b143d60700e4288243d281c51000f508003d464a40f40200189c12038a41c0c0c0b1001d0284079001d0310a01c01a510442e0b00000043c240104250000080321400c0c0010408080c0c410300b0701652001c60341c0d05888141801008002c2c07917071101c4243e524480d1020f0394038090b00c030343c065124141200c00491030010180c108144100d00060f1500400e0410042d0400b2940c0207840d11440c00702c40d24526607001141035806448820300d40e250400382c1ca03003140e42070810342c40700750741c00d28000004404a61640140e03040310710903a40d0b50300760707102e0346070300c60030a4400e10a4034003180c51910100f00800781e98201c40c40200490074075054044e040c80c2024803035441800342100040b4000010b208525040c41c008036581c480c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 864323633 1250 864322383 864322387
    0x5031f150e1905040e03090613030b10081b040f0921050c060604090201050c030f070c0b1903180f060608070803040803041a0d0e060403020d21050603030403210311 72
    0x1d400b000da082c6409010740d5000d00d0301c07000143c6040380c0400c2103404503500070300f000b581d03500540c3e036510038801680012100b1459043c04100c11100c541c2c40c0006680d20f207000b50400201c0080c529198007482c9580720340081c0c656000710308400c0b0500c00c0c50a15405000902c00300009180c0091f00820f55546900c2445418000b80103190400684154070030010350300052a03000a0005036128001d6041082e268480010344005c031541c440c0150001c0c038400d040151003561500603c5a00f4000c01e11710f01d108511100001c4c101034840c0d0041c40301030034421000c032a20010b9454030b0791126014503081d1445500c410082100c4101081145d0080155401640c1050300f00b0441d00c0c3c4921541c07286204500c07030800350f0036003007224008503090310b600032000b080070b030f040740c040c582d00c0d040115019170150140d80c0070607440702e02500120b80742001d84044400d6400c1d1410440005100c040d003150f401d07200502c40440024011000300740c0b6962030f9074a00c00c0c0d0300e40901004003941c1195100007010501 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 864324883 1250 864323633 864323659
    0x1701090302070e04030c12091406091311300a0504050a082802010c0f0206060117180d02030c1b1003020a1815080109110a05031f150e 59
    0x30109201060f201c0c0e01e4031005641e165070604513003000d0441406003c83d04998441403000e50081d807071900311240c145142d11078414001c10010320340525020203030468082d80030020680043c1c1c0c8201407080c580b414107820140c00c1200071400c03400000054065081405c84040307000c1d11b01d0b502540c8040d0615041c003051405560361516040c0ca4039000f4828100469940c10042d201c900c1c0c0e1421640810325007164034400d00009002e880090000f6002c100782c045030f403241c0e88c40854500e120ba038040c1c4500c400324010f49030100b050b44000300144c5e40b0684204080c0441082800000c0101d1000d90082d41c03035a8089a116013010344e181340d1148031030006250b0315100d4603904040e2000d0912401e005803142280c2c078058442c405442900440b00741100000f00782080c060700d0980ba031000c9503481d032207240c0e2a102814205d078601c14072442c1441c0140003844165108500455208413038003002c003c2c5e80c0050441e0900105590031001700748841681418003140d01c00b41d418403644080301d03d0455400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 864326133 1250 864324883 864324887
    0x12060f050402061b03040e040b040209070905060901110106120605011706040308060105092709010b0f0d02040b132d1811032d0c0303040b043c17010903 67
    0x126201d01c210f0120204a103c001c4c14805006940080c02c0da251200140c0c545440c105e038280200702c6003244104064001714415511030040e00003501e0004d0300310341c41d111921006590081000000076040d6407604008501c40301c02100d00c5a1040c85900041900c1d4109100703c4c0c4021039000d40140641c1c00441000042544030441c036800c91400e09003542d8405191000c22103110b00d6943d40800c0802e984c1d00f03140114030b035007001441280f2003030081050081d12410002000d0b1200c60242c0e00206000ca00303005072604e40c2c440c0719034500003802030500308040d00c68007040d600150141581c5185120350741d040100042c2c2c00f43c0c500702000030100040346d0328039a05c02c0140d100540240a0403c1070140d251241c0f802c214041c1000305c06c800074600400d00000014203400304161405c0f860103825002c0181d8140081a03d013138804010a56003010304008000b910f2200d5030841500c1400032080180b10783c81083e907002c01165003140030040080c14400e121102120041d05084982e142042000c0826 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 864327383 1250 864326133 864326137
    0x1f152405070618030c02031e03030a0c030e190b06151207050405130902030f1c08150414070810152f21130e04051612060f05040206 58
    0x25850500646a00060a00500902440001c0400e4031080b10710700c0c060580003440e10340c4061007102151b0103100350a88052406a4920040040d035009101207040c1d10300380d030448000d04481c0e28001a08115106800c1d284c0342400c0b0041d800300050280081c2844080031b0705942c486c6007540c58440c0da20041000d00100d00c1920b00d904d140014000c0880c80c0316114100b114010300000348072800002c4184071400c000c1418007403ca22a11134104100c0741a00013290b9110540e0300c4c1c2c01e62603500301a206080e510131100030a0340e0240300340000c43d01504d564034442c440d000b5140c8070641c4d01a103041c120140800c8000b800c501910008600f00b080008004021049100564038164807591085103141c05200707119051500c03030b01c81401c2082084d105c00640c1c2402c40c4c01c0c0c1440001c030210b1081480031984590019083d0241d0520020f1140a820a4100707811911030400c54240a00c00c041654100400340c02c074403078101c124a03c010910105000b1070603014030720305040000303080c0399000904038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 864328633 1250 864327383 864327449
    0x7080709120620030c091309080f07031403040b0403030506011119020d02060315011202030f06010309080d0f1a01020c10080601121a011202180609031f15 68
    0x1241c4508030801100d10290003008003100140d0300580300d0174205040640340c0c002c22002e5024130050340003035401d00103e0081130003c0760811006450041c0d00e0b8980d1082e40e11204007a020700030007400c81084400c0c0b9100840c03140c0d001d20080d03903490030071340341c018142c0300081c1000381040441260320721b802c240403c1c140d111a5039480324003200340ca0b80c80824842c020041c4080c2d88140007004011412000d50701000e034481090342c0301303241310100692010481c00160358850500c1220340c0010959402644596507076400741035840d040107810784281040c0c40d0203040700315030240c40380d032445a0b102110781ca8551030182400a041100249d50226041030b6003d01c11501f04079112021031596401100004d00c15030f05000144125203c08c0d1711010300c0c4940308401c5000805608220483e01c940d4401e4903030740b0381d02c0d40c10301125100000800c14140c10070030190b0f605008160302058006003036078420056043c43c50300480c1d6504241402c00281c420380d131019450350f140d0011181c0f140c0300d2500400007 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 864329883 1250 864328633 864328643
    0x6070c081c4805031b070308040b070f0b0702071401020f030f09011b0b1006090509040b06270603061602101a151b010213051c0b0f0708070912 63
    0x1800e201412444541d811011001015455421844003400800304c010072034101401d0400c0b01442d0311002d61540c440441c403018005031410300082c442e0700c400a000f003e1080c041c1c0319070064090661201c00710030b001520002d0260340608000c1040c80243c0303040d4810003500b400a80100e0400d854055101d100d901e01c0b0400c8090300060510440c0c1c0144030115850360540042c2410300c000340b4000744c1507101903c20300081c003000040010080e118142e080b054501c007602071512511583da80710754114015010315880320110041c9143c0c0b8089000c0050072103024440c10045060170400d05d414403101920484220b003031403070491407442d0005591807103580d001e1030004086014030120000d085121440c1c90b40140808082e40c800f0076039101401049050501d81c4000300342c00b100c000d0813445584c016039600400404104101d2070103180240e0440c0c0209207081b40040d49594541030341c001200c1e46020f0305454028071010039400703e0010380c04951403c250a9550070b196002c0a503080301540240 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 864331133 1250 864329883 864329957
    0x1e0106120902041e090c0e091b12070315270305030a2d0e010b030703020904080405150a11071512060504050414060c030106021c0c0b07030e1501050a05060906070c081c 74
    0x35444d00d62140110302b02201c40c0c1036070141e40c2c036031074080504030303041070b0a0580e01d0400560009025030071820080c130603502c2011040c420600c0d82d0641e0383d1703000100500300c029910040f208412083c508500240c014003810003000b203008001400c1160b20162482c001685081030102071618005002000e0b2601107070700811964a034a00a801c52140f42c0215400c445000c8440c4503903c2540b0181280c2940e40d12440461814210030b00c2d41c844091007040e961040025488032250300071100c04400f4a50100e001c40d00d961200c011030107840b81a5400ca590f4600d8060781d107580d0740b060015507003218180d46151b245515000000f9941d003460170b03240004e04034004401025038025640200d8041c1e00140f44080740ca07140a025005100585100d48940038402243c46000107410005040c0e600c001c190044a90410040c0015500480c80044d00301004109890106000200070b030001c01001c0e00420b06ca40840042104540440c4903480030b00c510b034004980b056008032403070080c400c034454001c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 864332383 1250 864331133 864331183
    0x11040501023c120c030d060806040b0103110a0b1801020106060c0c0e070e030a0506090d050703050d0513050601120303060b070f03030c180602061e0106120902041e090c0e09 76
    0x10f04005044060103c84000000c04144401002c0050942982080010441140e0300c081c101c0e00c2e8001118001d0218007460018000285880d40d00600e54901030b007a251a941c07941c0d00c1d601d46a100c5080c0510402c00815000c6481d80d090003903802810a510b080c203114030481e80d0b070301e5020010780103201014807403a00043e103007071056024481e02a402421a0f424010341d040968a881c2e0a03690104140110418080904c1c081d50444100b603a0640c1e51a1030810a03104803030040c10080d00c0403113801a80c281c41e60205404204150103049800e4481c0001c440d2890042c007180c0a540c0040e201090501030b00000c40e0819001d580c603d50036003000f152031071010501b200e10b0302c0040d05400c1150011440401e60701e500140441c42040d45c01d03021282109000034a624500c000d01c1480002100400441c1c1c584d1680e41198045902c05040801d60700e280c1a01e42030072003c0d802c008070130155148100d00912815901c01002010040d40c400c2290a003040200c6d10386103511901003440c1d0a1074044 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 864333633 1250 864332383 864332503
    0x316140102010f020d0207060e061003030c0c1d090606010c080703050904090804060c17091f0302040305120a020c09010510050711091f09110d0507050c011104050102 73
    0x2000080c1400f0865441030070542d210002e401c21101602e00718506807494101c01070005a0b1406041c2e41c0f070302c80480034559a01221100c40c5c0401c1203a126100580000c2d80b40325503044812081c0d03590040c8015884e05003440351a05000074603484c1080011082d15011918280881d203060740c040c40c0c003659a0b85804085409021540030040c0403900010700040c02907482030822a03060310a04008034003150943c281101030046030300c569403000100c0075541c0b90b0251242c14181e60015410301504156803625094140b44039407114404000f80081d0007002c00360f0620001c070f29a007040b5108020380d41404003040302c40c88298807410900100080d0346040c0620b80c100c403a40042e004011009914105445000035021800501544491000301192085841c001c5900d542d048010322410812211900f0300582005000301040c40010084984e03590401e024005030b1185401e01650758900d440002440c00c2840c035410021004400141c00740040c81e800b0b140d94240201c000d4040c91103c048017 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 864334883 1250 864333633 864333641
    0x60d23160f020d05251208010923010e18061003021816030507051308010b0a1a03150d0b040318080d140d110307031407051c0507030b0607060203010311031614010201 73
    0x2c05013141b407102c0c0003009041d900c03420460607145051800d0000181000c41d400030b021551511f1510300c0c1813100144080c140d82c2507040c3d071081c0c100c640048414501500c8905000094608101160300c1010600540c03d0502c511051408403d020940b10710b00b490881000b040c8844040c1c0030036469170301182c0c0e0340d40b00300142c2c0e80100c20000c183e080c555883d0101c07402440340d20b25113400f80c002103100148203029211064034201c07c41c426a4a9070341c0b400100007007401104409680800500154000310312400e10b003d00c11440394403100040a190241c00c5940c4030141d0100505500000c41c840b40c6991044080d50f042543d000c1003070311100e030700c1e103e640942100c204451008a02100700480d440e8143c01c22039807400c81010443d01c1c1d46031050100d03a10f2096228220742c4030188500441d86050903406590701000520340019103615000c00140c1075072014100362041034001c0300500c18400c403641004400721080700180f400c1008610342038074484d41846202041c4016011040d400e9000703401c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 864336133 1250 864334883 864334957
    0x603010c1e18151223010b09150403061a12120d02120c18060906030105010507050a020a120209060a0806060909011e29060d23160f020d05 61
    0x102d01420090381c0e820003868040c46070007206100b42030004040c0d00c004404c100a803c105d220340200050380c02c0c41c02028040e0720010085402500c20a01c50300b000d442000a800a584105030104510b201070f4821580e800e0204901440303050003800d00440c00c2800241001154840c5124689078030581e1140c40c002e004250040b00c2080e0007004001e50381c85400014410303031801c0308000e644c881c411001e000542c0554103050303400c0f001c04c00c0140510b40c010009806002c0c400c0c0101c410140040d404503416441a030300010f401c40074a01f1100440c83d040c00166801142600c0407100145041f9440c0e540305d602600031402100d200d4081044404203410503003030000c0d00103403070341051241c40540000b4544120744203001602c150140c0c00200007168001c80e0218000d24540c10886810402c030010281c140c0c2c66400070b0b00860480c0c180316808248248101d0341d000702c1c40c689a444400151a1044080d240c3c8115080503480c490740b01e40140607680e070901d410350019083d03a000c8090000c414030f509 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 864337383 1250 864336133 864336149
    0xb0301110c0a0314030408030105040e0102070609030203090f060c0c090403090f08070e09061b0d06050919230f18030d0c090504060303050403080a0212030903030603010c1e18 77
    0x1074021240100080d0149000d120f503a03940702c045240c0d00c0456540c00266001850848204010000c03494035400450040d400200014500880b6990704011605111380480168001086100b0b030b52800b00e1a0188007641a100070f450070801e213007400d85600390400e040d8842c4504101213418175101e441c58002601d20030070302100ba103071502c0c0d48039070b241c4075842103001490206000808424001c20860f0103940f00408030520000b40008910907504004120260265100400505075403464462030040402110f6001401c030546100c0007601c824055402c00ca2280c10052408003036040c0c1880e0f4020400da07070701904d9407540b0b650901c100e101800500803134400400d4503108458168860201050b40d61a44c422070395540c402c5c4415100c4d03e10000d001b0a0081c4020030202d51080001c1100b0704181c4140c0c0c40c010340110448155400c1501c103040254008000c00c206030400b48110081a00142000c140c0012101034100145100c2c0366054200203006507a86100805142c40401800c502 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 864338633 1250 864337383 864337387
    0x50f0114070609140d020714010309020916030f020f0c010c03020412110f120f010b01020c030706110106050a0f081207080f0c0f1c0e060408070324020a090302210606040b030111 78
    0x3005c0000e54030000c03805111a00441980c004045600921440c4a000e60207841e161095652a200d8061894150340e03900516031500c481202c03011480c8000c01121618220741ca484422410041d401c4641c408050001e061041005100044c02d2001e40c800d850f038800e88e1380c883ea12103007020514a81d1810065070b0005d01d0781c1ca910188130004120310100c0d60090001f044031064200c0120f980300001c1e90546d03050b400c014030500c1011320a02c42060025400700012422a54482c0411071811140d800300100980e054000e100c405018050840030340e03410410789081041c5074503007103154428462620407407440010180001c917018020b0108907001a020b039102c0f40500c0314511045043c00c21340340001410310510341c003680b41c648242d405440c00c0c14018025207045603242d10748801c0702d40700d031075070704412400d150288000750000302000e20b070942ea00e012151070b40c414014041542c1e00c9045030135200e50f091002e0483c0028400e6400b070401c0b07402180340714050010a00415004207030803146200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 864339883 1250 864338633 864338653
    0xa0b030a24090b01090e0c100e03060f150d03110607050c070605040e06060304021c031e020c010e01030c03020f0c1b09040803040f080c16050f011407060914 69
    0x500103074200d0648050030601d980501c03050015080701c0c0e64080042010304042c2c0140401440e9606c5040c0800228080b01c00c0d045521000a002402c54082100001c0138601501c0103030905000c002d800600c0564101d6060a100b1000081000401d401600820760a114401450b200c1d00c11007110244400c25a8414102104000c06a2740001c000c4a8a881403503c001581c521034011181141e00ca1852041f0701e849000c02c001090703201520a90388052110241298040101071f10400d4034030070b0300d68102020941c0c80307041d0030182c0784100c0015034210369403141007a40c02c0740c0a407901403403d2a00143c41d040ca038105a0088c0125800c4405044010a041d02081c400050281801c2c000000c07582201821408000c1c1c0b05600703c40003000e83c0e405001160008911400320740e0320901c03400466052403030904070140307840039002d421960042d2426041100b42480da200c10040142880c0000c00e8074101c00352080c0b0f0380b10700304c00148043d40d81d9180c103003440f444c10800200070300108190b441c1440 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 864341133 1250 864339883 864339893
    0x623041e03030201111206040203060301020c0f0c0a0e150409030908070f0801152102030a060504060c08090c2101060b0a021b04021215040f050702071d0f0c030a0b030a 74
    0x10007404100c025610700909108074646820585410681c1040101d0182e55004207004c003940020340103d80540d0280146002c200050081005044040c001080d1485014040060b288441e41c841000c4018090902003590308801c4162131015094030046015002441c1c11250102e40d58040662400b81410100d120301880c1e0043e007c4608000080c40364110440c06503550b140c0a00c141860340c0038000d10300005c80d28201204060314001001e503002e9a115071150429500122421244c1c150b80314003c03805103402c203030743c01d40115103d002450030f00101c2011400c003000e140c621008089611b501900ca003c003d400c110046c081c8003c1311500c46a520801a5840325100405105030446118803902801d040c400d0b52440c10a084201c00d15456115021210440c0039803201d402580303a410f204641091401241c1c0101c90a9005158040c9055580148069031400d00514800c8800a221540b4070312103041d5044511040403a5503600c84800050081c809030001c2901030203481100700c2401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 864342383 1250 864341133 864341189
    0x60a02100516090b0a050a0c05010207060f1b0e102307050604030f081b0c150c0c2803080705130311100e130506131a1009062304 57
    0x6445030711820502511520300f118113010701750751080010814884a03054501c60040907060502500c0010702d011041e40b01c403010b540c400c40c1d2025800d510350700c0c4a02101c01d651103c100350a5a0329211b9400600b440002d020090b006aa1400300143e042c031800b0700360103543c004007584a2800b6000d07911107141c07130100e807070350350486055000c60343c0701c0b00480c1a28003909075035100304500a100e034950131080031040029008803400460521490b4040880c501140481d1400b501c45000d2a603200c5000300c0e4414608500c2c0c450400c00749680308000100002d403a621201100e9042c10200290342d604142154240100f041105408040b44000070900500070503102c52820b081d18088005200414241c0340c60b40c1081c05c140c1c000e00180682c0001da260b50748515007002000384400c00450020519200b91501403683e1010207800a2900495144c0003040c0d191640300740c1001d00c806842d004010342070402031502d280c000b02c411420144460291421030740607110740c071b11000030106804c8102080c2c0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 864343633 1250 864342383 864342421
    0xc06070f14071a0921013803120a03050705040e090f0c01030603020915060f0706060e133906030b1309050709050408070f0b0442020f040e0a0b0a1202060a021005 71
    0x2a00b50444540b87c0760801041c1420741001e40c02c4914074044420030114000d00f4014a19010081c080c000406c0c40d8400b04a0a07024180d82401070203004107040304c803030801482610903410325141c40d20400041c1c880001e140e50050000242100300303216000825514428488a6210442c0c0059200100a83c41d030003102034401e6200d9101c45a40d5120050a4a409508016096070450340d8506d040c0b580c0003441130044494400c05100c2828100b80d010341c90f22440d00300c40c1c0802c6d00d40c4040316807030510000100030100d401405100d41d0209455003a02c6a00380c0c000c1c44801510780b000502480482012110840e600520b10b078201001030416030b00c4000d09560482c0c030a000640008441c0ea402000040b4001e03184918500c1c040c81100040c0e100c0d682d102c110103c15800b44040c121411010014200a104071000b2441da840c1503080402140ea00000c110711428030003c0611100c05041c00058600c1e906441c080e59604008000b0303483e00300c03d010701d03141207414442041103610200b417040401d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 864344883 1250 864343633 864343721
    0x1611101a030a03090e010503010504030e040903020f030a0507110607170315060f03070305090d05031515070303060e090102070302060403030b0607060f0f0f0e0c06070f14071a092101 80
    0x540d1f2603408141c00c0c0c031340698000c0c002402140ca2800c1030f00c0c1c640e00c4440c0d42482401200c02d48110544914159001600380201040703021410a050003144944070314030b00d00031a00c0b640381900a50760002030904900105200c10300201c009034194001c2c284600b03031070100a0030a80c4680e000b52105116502c01c40d01d000c0000d0804000c030700403400000c1c01018042e49900c0b024110b60350782c0d89180c044034800d0030301c0e07a008032030006c20012825088010045607029640120b2640c0c101800ca907108040030b00711050030b0f03104012070743c00b00b540400e201e900194507240218001c0c400e240011107134010500050407651404803450041031681d808100a1174000d03105109440c0014480e6088800c0e0054aa9660300002aa2907062401500034059240701d4503120014401d161955102c4030507500c41800a07070300200060085010f2180b03c100d51502c086c5041c0e05e0a0358032004980449014901c401c155007200b4000402d00c4820341209047d8032002c112440206816840c903204001d420190944d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 864346133 1250 864344883 864344909
    0x409050103211d0f0109050607050601050108061207090b010908010e07030b0106110a0b09030c1c0905091501180801020705030706050a1107150615081611101a030a0309 74
    0x1c143c00340040440c509030051100704000c02860900810b500521440e604020940f04003080c16611100504141801070b40141380a60614001419004000e06918031564040400c20700c2c48400003600c60980b41d58043c082660f41c05140140d0b0803090719041070102d54203001c83d4140f4580001000c03400c03a40140c1c4a24032903681c03a8001c1e41c10310101e020a82146d04021008000300b03032084404d980100e40c40088070b20304040c1c0c207140780c24002c080404e0714030040c1c01e000341020300740e0100150000d0700741250016500e00b0304d0a482401503202d05040d41c10311201c1c141205524801c2034214008141c400e009569928082c074160307071281e0000c03c08a420b14500f0003c10210b00d0140300c1c500301035460840e00d9240c480180c41d0030442c0b044168002c84050b440301004144003042c20902700b001085900ca950141c100340e450820b03401340f10415242084076610148403000d000255100c0c045c42e440c9400a640b100103c1c0c89180d45107042c3d120394051041100b00002c040d4485040070071241409900382c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 864347383 1250 864346133 864346193
    0x5060703020f040303050306031009140601050f0901050d02011205100e0a020f160c0302302a150f07051c02060a0209222c061b0409050103 61
    0x3404038040c50100c488000018401440020302803002150030a1005007200e0089500b540700100392031a02000711100c0606010718030204004100311405403200301ca0700c0348402c09100118110060512070740e0712540344e4031a02d44c19a405000c400481101800e41070000c1d190071240c40c070340c426035407095801d02840d400016007019224420740c4c05407469100520b24001e800780c2c032400408035109098600100610340000180d50348003c1d10564140c00c55040c403e814619000403541003207443d48100c941003d8034800740000c107030030031030503900702400c1000e2010300c0c22000ca030034007070b0011046c0d40070300b00080d188a0744a40740d0050060b03107119008841190004000c001041c0a881d00c400002d139120b80e001c0766440b689038000d003010306c6024103c05181500304d00a00c2d4085818030081640320340e04c0503500c0050102e085103110329a401b40740d0725540c00201030f000d6598000100703a0000d406407420b0b0702c4418128403046400601c5140401d000c2942c5a0401c05504484a8a81c41510100c07650070 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 864348633 1250 864347383 864347387
    0x10c231b0a060f1b0318050906030a061a03071202030c010f020601060c0303110d05061c0b0a1d07080c03061b09010f0e0d060207020f0a0302060340050607 68
    0x1900980c80c010780031140c01440c0000039500b10103007540e1801880403030400c00d100409006100d815850190303485e101e4891003054500104211a0056401198900e0401030191000188206044d41c0014001505030b00303540940d00c40c1c0c824481180d4180516413002641c0100181d034003070818001c8090b640072000700d00042d110812100111009038001c03c2c0101b20750340c0680b900d10700040c02402c0106105140c100d820203990b0001d1402c126459032002803240f2814942000b0101541d195080c104100e0207880e5034101000c01071024905989079060246403580480512124001140071280c00b01d440c0d85941c1d40701c840c000c02d0140a449000e0005568140d05c6004102c401c6440300d90502c1c0250b200c0044848010015041c0144542100c04610300c1e00d80c0309000e040d060286800503102e40382c6204004052983e010900c0c800d0410400a1026035645000c41c0d4000a010100d0f6602d0094080545184c2600c00e140b080d580c02100c17200c00c4024a1450f004001c9445a81a10301581e9480c0003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 864349883 1250 864348633 864348673
    0x61002030306031c050702060318070f080c0409060608071212020c0d0f050f160609151710030f21090e01051e060708211b0702010c23 59
    0x3206905601a040d40c6241e1304c40c040070070032003001d2480c240b03151800c5600811807550007904d0300001c003406808000c5141005001001c05001c1b070b81c2400701120f1811031480d42d211403e1401e0740c480c030768401120003000300d83e5100768024810360054901d91030303540c01c10403102040890141d59200361503950340c01081c40415515040c44004002c0194003034292900c1c0d00070000010100c420340b1559034a50603000d81040201000c00185c1c1c0404446410705d48024004132059004080c2028004899516550421004d4040101d10200c00c3c21710380d1000304101100d0140c1c1d201512528043c0c0c4090103120051284143c104205c2e1403000e003a030980d800480b00c1c1c0c034040c8a407030030011058006000f24a0302e4000f44a24008001c3c103051410300c1c00d00020358940c0481011100c0050002d04840400d6114113043c110104c0c0b10600205460035181c07000c4000d4030210200d88100c0005a411300310381c010030003800b8254010700c1c00310b45511078801c000f81160540413070540368810f0f4104140c90f05a4404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 864351133 1250 864349883 864349891
    0x40c170c04120605091906270b1b040f08030909131101080703020c1603050d090602030d0b15070b062b0b060f061c0c050702061207120e060610020303 66
    0x2852100c4544207483d030700c00401c00a002c0c0c1209026481140094890b012002c41080340a038400040c01c45a113001b80c0c0880e006840049401c0e0744130055140420078140143e03a0201d112036a220148046520080ca64490758201c103140e2505d2820110784050000081c0906e108260f80206558841c00c042e0702e19800e00c1e41000300131000b414000802d95200b161003940140040c1030240c10085c1000d8610704140c2c42c007010221501d0780c603408001b840800c006040b046900c03410601c1c0c0107824007000071b4680c42160500a8604d0310b1f18041c69498071107042c00c18000807040c0e01181c03940500d2600c00511386050b0340d0345209034400340204460703454020741006c078058a02d0b00d012404a040c0d5a0100310400200035540c08015603405400ca03850754401420019a00540454400c224008410441d00b0703800d002c804010080c0312007001611198210384d1401c0401220070903a554100f8111140310490b8540c81d80d16042102c1c00d940000d0000d4150700501080b580b0b02000e080143c0c0890345c9000032a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 864352383 1250 864351133 864351149
    0x20313142d060c010f0b0f0a1a04030b0c0c070b0922021b0307050708070303090501050d1515080f10050d110d0b070813080f09030309040c170c04 64
    0x400d491044000401c401c20125900351989010700c44003400101240c01c0380c0e02c1c00f00c00c2d94607100901c40f401d07050700c1544a0800c08407082500c0803c800c0200c2ca0200640c007034100310140d4004d0001c00c25001000340c400940d03101c41d10078450718100403484a15000000c8034880c03803241c1c4034045400302d250010340e02c009002400070103040350015640c0d0071000c001070840721041e03400c103e080600701c50070f080c0c000703ca4184e50080d541e800003480d00c1403401241c0c0d80854100c1d000f03070703e0600000c0d600003d050700309d032001d182103500e48e02a400030400400594842c402c43d40c0f51900300281100c1420620ba00c1d900c40c0c0e484900301903071403480e50b0b00031000450f0005060001c0c4402440103252001c80346000a0181e070308418403090241c0881c01c0c0c0707031480e10180c1d10040311000f004034007a80016050341c071103195103071960340c00029565917025004a001404070b0600c00b003143c5043e51410401c1e40c4007180300500034800100300003006000c100900c0c644140b241d01e188005200707445040e0031101115410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 864353633 1250 864352383 864352399
    0x30903120403020c0405041a100b25080409021e0f091011011b09090605060d0903230304060506030309010c112202120f040c050d150f060918020d0b06030c06030702031314 75
    0x4002c07007144844183d602f81600d405a09540022500c040f002d000a0122044016500c80c941140c00740c0600b01645503134081441041074400410202d015120719010644984600791060b01098600c100301515510b455032030940500302c42c8040c0c40d000380703da80d9542c4502ca019500d030b500c07050907200203016040c1c00c0b080400c03280031a940c540c4e0014100c03c0c000d1402000001d0007980b100281c100400d4040e880413804014882444403910071290001c0d4100e0003141340c28140e000203000c03400302c039101070014114000143c495456055920b02d1444030110882d0f03c2051403480c202c001e4000013442c03902c44100c0d20002c3c149240e00c08205014a030016030341500240b0f41400c2061041413660121030001802d009100e440030a40901410502100c60105819091031000e404454071119400540c0341c5541d40d00001d030b15030108038090503400201c00b004035555100428a40b4140c11245508400000f003080b150740c4e4044040c002648241c84031013551503452003001e1105613a019019400441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 864354883 1250 864353633 864353647
    0x3030506180c0307050c0d2f061504061716081f02030702070b0a030b01020c03121204060b061303050712150509010b030115060311030903120403020c0405041a100b 72
    0xd14010f503902c61038500e05a803070418002c03540c6007041d01c02d0283c00c0100d40c101200e003004544414285d0302045000d054211f614010400c0690740d1000941448440c44954004d031041c0c1d101e0380c1100000d8074143c1c0141c50807140d0309039059680c04242d40b00503c00c64106101007120640460f0740d150039000500814003031022120003034001c1d440603021000f54898a04000f403104c540c98040e0a91088a4400103600c000346400a82080030010040344242c0205040d010b45038450425105a00511803000010395514548800105298003500c0d62058000ca40740329209080c03200c076802d070307881786042d00e00d402c1d52407032584100100044000d100c0649031783c4400c8d05281d00c0d8007080d4883c0326900081400300780c21010908550070440d4600080c0360242d81030154a8140c007801c01066181d0342030790310f5864118403141c0c40c0e00660382112598404800481d003414801c004c00d01d18078a004104000074246890708126040c000340e44444251407020000f80d202e00224890411280c404402d1071030140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 864356133 1250 864354883 864354901
    0x230909060f010608181920030d03090f0503040f080f15060f0316150f020a5f03030402011706120f1005160c151d0105040303050618 58
    0x800217101c8043c02c4d1403508a800e21340000c1020412030720122141303806440741070420521042048000550200c0c10840d128542d40300028801141601071400007011206440e02c0341a101c0204070141c480d200108020903c900c44e540900c0403100d0800480d10a0394105416986481110360030441009913100000d40500b0039031880c040d61580241514400c242d60741600707904910300d0b0450806003980310b0036801d0a540090342c5400200319400207050041c141d56540804c0c0d00221410241e03a013614000d9041800d540d20080b0004500c05003940288420105e03140d402d80c3c90046c4a0740c0c124552814890a42000c401c413405190180e4451500c140c03004580104102c0240c42103403c481c0d000c10811006500f4080000c101c984040601050858030120f80c0035100003a0510407070076102161040065000000014038540c8130030341c00300e011071190886000341030758070300c00c5d03840382e91700c08113070030000041d8003607446140b0035102041152141e8041c0450301d000040c1d08005640c1250100b441c000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 864357383 1250 864356133 864356147
    0x20303150a030203010c0215100503060c07060e0d0c030923040e120c03030f06090f160903080706050a140c04091a03032a01020703091806230909060f0106 68
    0x114041c011507545940c079030100742102c004007400c00068001a60880504513114038042d08440282691041242004002616040c02420411041c000000d0b14410401c9981001d1041080c59050710700318026210301904e5240c140d582140090b00a24001c0381500c0c00301c0e4000d03811558940045050300c44034083c44010116410049041c4c8030348551041c00e001c03100014101442010041d585a00b083c0c80301d00060b42c40a00080c5c46064600f0402c0100100100903d038000790b41100308000f000040f81c295100c141640000d000800700180410500030b00e50006030080c05407050070007504c003000300011003251080e07810444000007000108407100c040d8006082c1c108040c15004003140c1f08000091075607010b006e84070741860305100070003a81d001c40c2e58005070a0345030384029032034212159402000c02c10703e80031388495030350081d2888500116592204018010b540c1002846d100002c5050900e002130111b5644107420500c005180000c0100f50180611800c403000c200907400c041c41500e802c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 864358633 1250 864357383 864357421
    0x1030207021216050418050c06160b0117061008030f0d14010e01030b15010f032403030e0f120a080306060f030403050d110901020c1315090204060f020607020303 71
    0x15030a2990030b8440074050040c00c0c0705400003240da076840751412050009a64110081e014034203209122607000c29004202da804c0f8100403600035a903180c0507a4250451004014040c0030f00c8450400442c04060000c50042404045402c442c04e03035943c01001210b9409134003800a60f0b030000e00080c2c854455402c041e040342841b502000c602081441210150311400764840020410541e0042040c0121136135025040300500c0c4680150300d41000010b001e031441c0300481c0c02090380d80c080c0c0c8507282e0603001c0000480c424624101c0070a1303070380f4240200a150074003500c92040400c980452030502c1e01140e1540c2a4690002400c040d05264076400100d41004100319040b640401c07889401d404407074011441503129859454548a0444000703080f14441c0a49280804080150382503503a000078059a00d03400480c0c094034510010f644c42c0d000b900c40c40b0003103110741c40c4001c0c000c2041040c54003d0029030382142d540050050804c1400c80e41c5003015585070000d604100041040072041100030095 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 864359883 1250 864358633 864358639
    0xa0b0d0201120b0603090d0306120c1202010e1c060c0e0108010e100503030d06030c0509090606240a1e0807090e09030910020615103e030d0e1203060103020702 70
    0xf003020082c08207695920031500004d29422a030303042080760350075216540c080c0143c099030100900e659a10405002c80c0c90003a410b10510b90555201161310400200800342405052003d1ba0840801141d1100c0104982101c0351810000e6070780c5001d2144400200466059403140e406901c0c0048a16501ca070103842c00d9180101d9180c04a0541c40402c010302c006c1c04000300c0081c0e06450740c1422078890a040d003000340705001d5201480350350b420000d9901d0b04407004443c15210045c800c0c000c820b00c1c0c9242c80c0c428170700c00e9000c50f1250103180c11500c2405080c409200c41c8021910040382121034010884414001c204520401d00c41c200d00c3c08441da500101900031203180641d2080000d04400d00c48224a0041e84444100320800621041c131100140340ac0e10030100c41c581a600c090101070340c07031900221749455401030044c0a444031a6a91004c00b040802030020403062180f10b44a034031080c0000003540c109144030003011030010b0303183c0302084152070343d80c1140c440b40d0044010b988100d4090764 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 864361133 1250 864359883 864359891
    0x102030f070f050d11060a02030606070b130c090f0b03010e06131401020d0f0b0409050607030c0e09010608010509090f0a080a021e070f08030304050a062004060201050f0a0b0d020112 80
    0x1001400c02c200031456460030303441700d504603005910354600d0410018245008240148248000c80d00d0791030a40b64580d074051100200c4d540e9203505092180e503018000781091550100001c0c07851180d5100740c01d07402d00c101061040c00225000d041c01d84040000000c0140c1c820000200410104400c41c50030720310811403d60a0b9203541049400e9030810718880c00c081d5078a07584030707015420b184a0146450b8064400788009000c648400b5200c1c04010704035070030716844a400070280c078420003040c100d41e9402804a11156120840109a49030074012076000341402d802194031803000050992084240d0f41c014441501e00c1c0d0fa4512003500103102c00801d51054000034040c09100303401d60381032040e00781d0080c2101c1d4038103e400700e50b0190a5000844a801c10403c0c0004241c0c00301c0d990300f43c1a004040403c00030700d52a40c0c0552080030940b1400400c4c40801c000c206180d064000500441d042c8102417280e4071b41c26003030011100541c41c583c0e8004100d131070910055000e000d03c00c0500803e140009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 864362383 1250 864361133 864361163
    0xf30110120070603060503061b09010c02030102040f210c03020103020901170a1a0d05030d09050309130606090b04050105030a0f020c010c020f10050c03011205100c0c1101030b0102030f07 82
    0x103034041a140101e5405034002100512903158140710384001008201c000f044103091001003030751a800d800ca0800007000e000154491241d0013410b010000380d602900842d81c0d02c1e92005039501c02001809825401c401080501c0d05131840d01110090207500001d080318050700c0c1d0380c019002503101070380300e90500c266240d008010400000d04a881250742a5001c1074912800d921124006c0740b0032000c6100b03803414000708001c15400400c1c0c882d070f42650719001a03052118100b0307524601070031544036070181c41c00c0d14007030141803188c0090f0700301c40c1541c4400a42c1d540380c0303038092000d0055000d41400a003041c4006001401d081e0401201512000d00051522600c91803540c2513911030b60110300036a10007101d0800700f10f0f040100b1180812942c40402c82400c2806444145c0d20040c803c00c0c20b004c001045200c02d10000b400054920b96882000700a542042400a049040451010340c0c1d030350980f20101d4919406402128202c00059003d075142030190050014030740c04c0050142d88420401c4104 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 864363633 1250 864362383 864362417
    0xe010201060504180b06010f0e01030509030f0a020706020c011b030e041b02011e021218031210170a0222060f09090b250c14070f301101 60
    0x503503025201c0b4110718a0100315805e1801541401030112810028808810b4407403d6010b5a0300c4041d810900e000b14440d26400c0c19149180141d001c03c50b0303091030026201c05e4154000943c031003181c006400341e948a0014a00655003011070312202c2c14042c9039181c8031000244904001030018400a000042c1e100031000c1354800b5501d51041035015039503a91451924041c0034038110503003a20100e09510b03005d07454540040b1080042d00c044184a0b9080e000d41054106000f03440200c140a0103042092400c032041c1c030b4040c0141c1c428000010112200280c2484001c1021581903402411040c1c0e2190701440d210651800d0341d0311100f055503101000704086410105d4130000301030302c54010414003000d08110002e914068030341a1081c4a08031054002ca2881940b2078032800da83c200314003850450f0910314603184603244100440e0056000c00f0850b600701910101c2591503090481860603040810700c050031501c071242d8030766100d5040c2002e00150842c0d45142200d041071400701d100103100300038 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 864364883 1250 864363633 864363641
    0x91c0f211e02030901180f06180b04120807050a0827010e0c0a1e050d14010c110f030a05040b0a05071a0a0c0c030c06050402040e030c160f05030d0e010201060504 71
    0x86011030703540003c00d11600e40d034240160424025001c0441d2000a699a29403030300c13454a0400400054540900c2d44031911001e0304114030640142c49410307245460300c2c2c4484030191030350000c004118420042200c8611072001d0740c41140c2940c035407004c1921410ba10f82d080381c2c50081044096050301e681c5034090b950038000c030102c080840f00103000a40c0104104000246207800114807400c44000001e980c000805080c03048070404d032058124480c442c03c01b00e100600904545007290300f82500a00b80682c460301c02c2001421400640c2d02000303948422548038440d0080340c0c00001c0c07007801f00740b107110b6060340288114142801e0071032410129a442e0041d400d5035000f200d4001c6100420070000c0b076071600450b12840c402d032a202e0304030110b035a00540901070181010b41040c0d6070782e0005046440da0340c48501412000e0044035120a000d0311040d58940480c909001029070a500c001104115010b5510070b075100100505614180c03030400300c800796030590f2664119901c03014009225162485 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 864366133 1250 864364883 864364931
    0xa0c14011a030d0c150203071205070e01020105091b01050903100e06010311010f0c082d0a0e03010e250e0a0605010320040519090203091c0f21 63
    0x20803980d007401000101400e0020000e007001c24811091034000c0090382000298110700b00e2010016141c0d100d80c04129076000d00c0a405445c510f2a000612030082e8110304c90310b9000c5804da0003444156a500002078030f8250040c01d0f0030040aa801036548150b000300040d00d0036100160840d4030503820348154100f03441d10005030b000140c000f00014410321041a041007041542030903c0d8081c0c11350300000514207241c7c1900034120500110325001404d200204c84569002d45400f902e260b10b0705040b5565240d4041655400421400c142d0480181410300410005010b10401b401001d0360b003a2040340300000001034070781070701580300c008071346051404030700c071700030b200d92400001c6036420080094221040030304000303400d82001d400000b41822034801c44040c1c0781d00707070340580940c0c451034100070306400030b03070491848540003004018040b03000090700c461900039040d100c2224192100191002d07003070911004001041200d080d0b05c1e48600c0503100c04401c0321140005000f0b41f824404d004c0e1403900007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 864367383 1250 864366133 864366161
    0x7030e0306013011130b1324050306180a0b0702031306030203090703080c070e15210a060203060a0b0a0206040b07110c0f010905060f04030201090b030c0a0c1401 71
    0x120020089000c421901204400154006441c070407a58070350181d040c54134640c0602c144a409140c20320340d517407a08110b803041005002880703107625520400f000f91007079107200c4282400c910f400300c1110042c4003242e0112100640504030a4850b030109a64007007141d116852140b0410801c44001184034150f41c1c400e480c5580030b0f50b218105441c5c4814112001d0f4000d0341010b0040c070601c5609100403500c1411a0752208005985400380c0d0233150508829501c02e050860802003040800d00041c2c00341c0c4542c080880d40c1e0407040d21305c0020800300307030101142c400361503125070010700000e0050350096410074001010715406a0361001d0601031766101c0340c000130060304030609010400c088455281e400652500304442001c2c8000400303a80d806103030324880d109000104041050340d000341c1e02c1001410024146c2d50340c8041402c00842c0c3c0782d100e03100032400030348220000100c54a00c082504d0059480d651814604240410201d440c044440d0040d164001100c00740c2025032001d20902c18455a69 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 864368633 1250 864367383 864367409
    0x21e04090504032015040c180902040b09010e191d03191b0b1902041d0903070804090b0a17070303110c0612090a051207060c031a040207030e030601 65
    0x43c5030040c084a02104619030059500b41c442061000200f402c1203401140140005030340e0303a40c101031000405a40c40100c6560f4509500510b1407a16080804814000e07181884000d040c070040c400106800d104840c070f10000312000c110b0032065041380c11000310038840085180e10440a01c1e210b100c1c0d440d6003080a42c0c0c80000d045201d815048442c500d10b003110706000101000d590101d05202c072180b54001c00c04221a000079040b02d0903000c01810861114070115190ba4035988480e95a000d44003014142c41401400942c0c405000170459001d01c0c0c0c0180b20a003458030300080d820150170030750794070f5505c48085c00022400c14600345240c1c00c003210075001410700c1403840c00c0190207a200310340c08680940003101e0060180d1078a5003150411600a401040c440e80d443c51100e0030b00f07204020040640c003401c1e0004501c080c1c80d0010b0403025010310030400400090b05810340481d40031011a000c0e846251803264428034055003d07111150007410070800c4c00c1c58030170029090000c00d8200c0c1c0c850300c0364 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 864369883 1250 864368633 864368641
    0x17091c0807080f06030d0c031e05040e01080729070501290a05060702010c230601030b1303020c041104030b0c04170d0503012108070b01230a09021e040905 68
    0x4070110351600040c03c0d4903003800340c4c1007510102e6215000c107031004e818403400d541d00604042c0f04035a00c540c1c00700300324004a004000020300603c540d0080c80303425001898000085120f00010801c0b40c1181c0407030030b03004c07502c801491080a0040d60902da01e4104d14050054102064081c021101040304a81c04141420002c0080f40c40c141010000d460003a801182c045c002e40e1128403c962030345809007400a0880105e140c08400080e82e130350304455216501c1206401c0d103100040f654140d0b489000303500c0c0f095441c0e02c0e4003a2549084038018005034800c00c000066410710b90f0001da61010b00c07038443e514064403516003009100c020303600c5a100440001d070030420304c4134818103e24440e6000c03000d0440b041c94558001c0032804180601810b040310000b00442040b03450300d602c003015a00c90001910b442043c204040000000d01c1491000403e0403090100c0510100c039881c01a40c0040aa81255041400340c1e0025088442c030380d003400a064082c80884070454015000800d1290742c003082a2030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 864371133 1250 864369883 864369887
    0x180d080c0319140906160f0807081206040903020307020d050c12070e060d02060d1e0c050c0708071d190905100f05100b1e181c0317091c0807 62
    0x5421070f40101115800d0203c0404c1d903544c030341110780c0e50183e1480d42c0034489407820071a0f080000f442e0001c02010340015240e0421414001a0900c040c80d54000e041d15030ba82810b02c4140c0d600c90000900580040290784018030b010624010040e0007402100c6c02070300ea8001040d1502d010700d2a06d505a80484002c00500c01c4409680c0d60140d002d8443c0c0002503813a5000c81d20a0050340d4840702c210b51942564122641d140158000e4100011400e00c0081605c0c90043c142e5400400c1003641801034100104070b49600180000448107102c0c0807050103244140003041c0c104010f8103005030500b9603510142440c0f128083c40d00064028409041d01c80451400c810480c0d000246299100c4e0500d03040109600c600b82e912403c55042e50596903685c0e070008160f000c003900311038400d0390120010451107122540c007008145440426100e1390004642c5c03a00c2c4010f080124800200041d40b28a2190b5001010325111504a48102c040380d2500c20421445901d2aa8070084100041c03188030400c45815 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 864372383 1250 864371133 864371147
    0xc1507020c031002040807030327030305070b070305070f052101300c05060702030a0c0306060f090b060a0c020d120302090906041a0f0105120a0917180d080c0319 71
    0x4007610811440e052820540700d0700d43d0106e1001400b8015040760f1307800c13030403c0c1c00300912901c10549440048180c40e46005011030b04640420f8400544420028010e1400391103014066091a1100141030100d8035040380c859000c158541403800000f512240580c4180151030b000e032084480702d42c18128403083c0e00c1c040384c05585030f4140c082d1204580401103800041600280c2e64160f903090350320070380c2d4008603240000f0440300410624004a002062007102d90141081d1088035000d095440d80e1100c0c25002c1d0303000100c103654494000c000c00185c050154002800c080d10283c141c80c06910151103c8030381044112a840110707030001410203452600140c0c5d13913880401154200b0600c1c40103680c000817805004026030054000b0716104525a02520544505d00800210f00d2042c0c90003011400240c05903d4040313400d000d0a100e16010440d00105442c0100a107400c03001d0750300c40c03020400121341c0207003c00782c4807503608000c2102010b60074001040c1c0d102d548100200c4001c40528000c00328 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 864373633 1250 864372383 864372403
    0x51503060a09111e010315081b04110a050d050604061505030103021828150618050609090408030411060d15061d060906040504052805010b0703050c1507020c03 70
    0x28400181304186070102c54a280300c0904c00030f00c0c001401000d20907228040020a800039400c501c543c0348034421007049400c2d03220314580295001d02625059140103081c0d8000c607860740380402c105002203080001d0551016a00c14802003021620f940d0b00c0d4a1203034141d02824024000404c000014020350403c3c4150320200310004100c04014984042812000d00355140c002001310701c260001381c2400859044290b03d40c2d410300000300c049075034100180407000b400140c10080030441200044501c1c1400a0740c00e0000060201000c4d50380350741c2c503090158001401107e61423540050f0780ca00d9110360015103400070304004009041103250480000c2824260b00000c10404c0a01850308105605100034044000a0307560545911031240054044e00842c1c208640191500007040400101d044500120380c038000a1a0a01c01c0c0d03007510031301680e000f4060482444420000c0c2e0000030311910040102c5c4c2039003400d0300c000040d040d604204d510742c2907407030a00680c8a1001500d03e461300b40100303505 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 864374883 1250 864373633 864373639
    0x30c04091802100309060e0607050414030105060d030f0207090212041a0702100b0102100c080f0705070b0112020d050a0303020301081002031506220f091a0a0306051503060a0911 78
    0x32920a6400610103121403c01c10040545400c03a950802240d600710240d1441d400068031303000e1034440c03001400782d04180704104500307003440b032072080e00d08040c42001d00428001e00140300c231800c0c0ba00e0903142200b007101c4100c11031040c048000b41d18241c62005e01181100082081d01c05c0c00e26041000301e0b00341810f1034803d0100414140103c8a1300011015642411181d001c1510041c860041c3c2c1001070040301541c1d01400c0c040c03100c50041e07001c1c444501c200c0e8907154001d45a240c150080f01c01d4011074000402c140c0d400d8005106000d40024041c0c1600d20007080c070105480d0039030b030301070501c80c3e04001207010036000310042c0201201441003884003041c0101c114150319140303200725444403442d075845004400c00a40c00c01c07a4280410749404014000c010358802c1962011580c003296080e08c16540100d203803403c03590b0084141e40781c04150120007461407215a08545800340140400381c59011a400b000c0061001c9403001d002941c4942c0c2a6000050130084901f01013124011950b69948 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 864376133 1250 864374883 864374921
    0x110a08070f080a0f0207060e0a060c0507051510180603050601050f03120d090506040f210806120f01090b0f150604062a0f03090f120204091106030c0409 67
    0x10784a540506100d50140c800a00480e098083d241510000c2c428a038000d024a801c040003001c000400040e585aa20b10843d800c00018410540c00c680d9809064001000f5401c00c4548284918544022035044015200c40400d0b040d942d0705140c10b10905089c2d003d03002e03500d40404005000303040c4116401410155080101070070103500003130302c0e4030480601c0fa55031a0085242d044d084015441404110b42c4032080740c250381094188460180c0000034120342c00704c85464080c0042c4816411016801002d4443c0102d03621028104845039132044036407000c61041c1180c400c140902400350300c45490207404090420300b413001c07044800c0d040042040d106410160300301103135501c80130225821140c451030700214188424440c14080c0c491580818240e0070014114010303c142c1a00100d1510b1082d00d503100110b41d54403142c0e0180c40c1600c20150142c59100d00d0601504103a0050300801e48600001c10080140c100041d5454001b526a03000c2c00f41d020505201d01102c87c45001c207140e2112080e10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 864377383 1250 864376133 864376157
    0x6050103060503030403140c060c211603081e01061710030309050d060b030a03051803210c0a080d05011a09060a1b0c0303022d0d050c0709110a0807 65
    0x1035134038030031440028034032800c001c4030b00300a520500440c2000c180041c0341c13a581d108075181d403a03a0380c21060883c000c0600e2420b1802090824013003103461441d01c50140360500a544e8505032280030004142c1c1c10038150815640c2100141c094009001e402c02d80c84002c8000160791507210400001003008409026071b0406102080d040300e05841155021600081958a20319102d409001200041c0390140b01c0c07002004200750704400602800030601c4042c012026a0307000301070740d50740743d1000c2d10784400e10158002005082c4070000d140011041d01140c5a440c1d0507030700d14895178080c10f060354019580720018485040203502882400320b91103086401c051180002421b00e10400c48204140f00420443c50902c0006040903121113030883d004202c1139580b821301a4598030750002950640509800c51700e001ea66001e58607a804076090018541d60504c2d81069800d640802080d200500c1012400140f984c008c1c01803400d6010119031049c2c44003120f44024028a1000e841c12007403040c40c00d040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 864378633 1250 864377383 864377389
    0x10503040b01031b03080d06090b040504021003020c01020f04120308131205130e091b0303070c0b130e18010c11030703031509022214031005040314070f06060501030605 74
    0x706064079040b25007030100c1c00e0101c62002c00c040c1982e10040001e00c001c15201900c203501d60064080312003070a018424080c104e000c0100304e80d4100e4000f58042c1800d044049024401d1740a0201d5079000000145800716021030040c40d5045540700c003850400b1181c0171410035500004064100e510710503600d400f0b00d40d55441101c03111142e0514000c1042c042042004c1d15112110705004004006d0781c0d420310304142c01800e460b6840100030031010965420f0002039400c00008940807030360080e079011245402e11904080c99804050f000b06000f0003d01301040d103100450019001d402020180c00d001d0051656060030750f00419180414000c2d19000814001030110403185116410300c1e0001d541c008000803104003010b980c110040c8640301007024088100300040c102407050b035000e001003403240da0f940e811588083c540030454060b0051400920a4030300c40c1c11894000d4424240742e560207410000035406030b0420710094500c511032440c15001d0001c81d1042001610b004c3c40c06100f107600740380c08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 864379883 1250 864378633 864378653
    0x40f080a020a27230a02090103051b0901030510031a040506060a0f0b13080102030a0b0f040501080304030f05070e070e040b040504240b0d0c061101020421060e060f070e01050304 78
    0x280d43d945856549500a0b002d542c0000d88075a18030406903071543c100240814000d411031000076012928110200d415000d07081c8061010b041c030030b941c892801d00f0740e40c01180a420080c20008403118490800300c005114009a0740c1c90500f80b0039181403038035260070300e04d141103c042c0c03d1234080e440f1400144160591a03410a00340c40002106a940380301c0b0900c6060300c441c0340d078000d0801d0752001c02440b1345126107401c600c00d039840844010803626850806c00046650a1044800607441040208000380103101c0c0083ca090050054408165903882d24080c45a000ca1303142c00041e094070036035070035803800e44152000c5003c00c0d242002a442c00d41d171074034401c50200c0b04802842d602c86050075820381d81900100494000540342d1604440c0a14007042104064003070500450805066241c80000500c04d4508540e1038250307000d015401041a440c84000c100c109171180358440c80e4130080c0b03180403c40c0078010f4030b15145a80284c42c0842c4020040071000300903504000d402c00600000c101c4d0010303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 864381133 1250 864379883 864379949
    0x905060f12030d050103051f0e061503160e100e091b040e0114010503010507020d050403060b0f03010c0806030106052409030c09070207031a160c08040f080a020a 71
    0x1418007142000561141c81c6000703541841c6545030901001000300b104c080760012422074481c20f05403041e26407482d1901600c0c12040c1603100c90b40320b4400190140c5080403030b8000240e0150540f411804e650300703000c02e01d50300c41e00640d40c840072710310900800110b000c606000074003c40421600e503007005500c4540314000b44c15241005500f9403911b0006176240d500003c86208150002c0186940c40d0b0304517500e02809100702c6c0c0c031952074100001ca42c0d9002007400c04c1e203400e4560310a031420b4255a00c1030020400d0611143e000321008002145a85092080c42401180707070700c0c0c6104904e3301100301740c20b44040f504840d0203071b16010a50003580d1440452007900044c4004a030b5110b010003008245408441034025602502003000d02c04605e40100d11103003903034040c03c0d00401120a03505040201d440a841401d07000c01895105030840d03114045800000d4881c2170760302c0c41c180d541c800101c0c10032100d811441c05500040c40790002c43c503000c42d0350b40040402c0b10741c5018428440d2060807140070411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 864382383 1250 864381133 864381139
    0x305030402010e150c010b0f0405251701140411040506042105030a0c0302011505060a0f02070816172b050903010f091a0105030d0e010908010f0905070905060f 70
    0x5444080d44e903201d1096401070f04a216055072154064007800d4064410006130b0341c09540105501403050811340515885071a0128070610580c4200000491100680034190200300410710303601e00070328a10450a0003070540e491a5010860080100002c9a60503039280c4500c5800304420030081e1071300d00660741240c2c1d0f414200003400650640e0030b600c06180b2000104a40000070f40900f0154101c00c0c0c0c641040e0199000704141c40c0c4501404801c0305590164036403101003400008030046c441e0010911480c1c2c0e2f44142c8020f1607036002c0c11498800302c10210b011801000200b8094105440f403680b22070040c010041c410410124040e840c00150480702c0074000000e04251821540100d089420600010b0001c106085001e400c6800804500a00301d1321030340d800092511055125000318140c440003000b91130185141700741500d334803d90301e424906000b072481c0d0000e00000b003840b84400c01c0b903a01e08045400d10091908900302520f981181c10801e04e49010f211040c1c4412080d034811000503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 864383633 1250 864382383 864382397
    0x9270a15151203081f0e0a05040311070303050301052805040225060906050603011e180804030c03210207050d170c0f07090209030613030c080309010e19030503040201 73
    0x9895890802819400480c20302c11039a044000309640010350380c0c842e10300d000721600340c84060040e00c4003101c454801c020070410000081002850f050b071043da045440307820300421402c82032464034180b00243e030056000c54000b0004103c3c078107254244070404082000021480d02034000007103401482401007600607030380882c2c40b0804039401801070903802800307044081c11143e28501840949203428040351418100300c0408c280d400c0501500c001e803903144442101d00341c60754550340c00405040b0f1494042c50388000c064070100782604001d001440c02018540390945c110700384000d24003c007406c8100055803d540122001da4080f6180080e6401200d404206076400c1c00c02d8501030304039a5010445c0310000500d140b012000040e5030403420507042c00e44502d19503c2c0d8441040340500708405805400c1308000403000303480915504801d0b4440d0420000151706900e0b02842d03900100c072840f409a40d909840581d00300100082c05070039131081200c4042800e2039400500500002d48002d043c4901 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 864384883 1250 864383633 864383651
    0xf1b0409031e270f090b0f010c0213020a20060108030318070e0106020a0606090b0f060d0608060723070309090f061505070c0b18120a0209270a15 64
    0x200d9101400c4441140e03e02c05100d6014445200d9181c0c501c0c414201d20104003038000604811a0080c441a110010076680788038017003400540d03262a82030340480e804100c0344044414540700f44061704d280441590303001d0350080344100d003101070013914500751501e0340024010403442d00008200c81e0b0084900000d90074041c6440480380c0b0349582c42d00207040551541e0008903010f54002020b005441c0211024070559036034a40080480ea100201140c0101b441c80c05c038881801d02c2e100400c0003036102440000d05a60360600706081060540d02080000c120718281410310094075094241c80b008001c99900e09102944c0251440826204542c0025140e010042c40b20b08181e11040051144007941395150510b00002803d960010108a40c81030a5042c08540c00041c001030340e5801003650104000050300d071003007000000c1649690180380c0b24803407034040183c882c8181c01d400b4500306111440809a03045084521040e03101007599240c2c807510032200810b03500f90341800ca11860000009040c0c038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 864386133 1250 864384883 864384887
    0x6030103050a12022a0306070806030c0f01020a02100e0312030c030a0902180f0a1107080906070c0f0b09150c0d0e0a03020402070503090406060c0b04031206080f1b0409031e 76
    0x10001101781c0e94004582e68401990401c1042c10f005c1060440a0340c0c3c0b20780c2e07a2030f01500c00b90070542d0700344d805603c0065200407904010458201040050045550702081a800660416075020b559400242c188103059401d050030401d41e003442106108442c2949401036041c1d261380001454100040d49503060301040d529900701381d649080760300d000ca000c00d203005610794860103010348081110a10305400c04109420358000d6890899000c540d01b440c00c0590f80400000390031040301a078050a8212000a070f29010000c50401440300c44065074692916508010580c4022100d00c0c10702030040007000540341010494159060070b5052220180c0b1260700896035844150f0402508648001091001c2c02400809080b20b50011203050204a40707802007114510200c1000800c200214404030300001c3c0540c01d46981e07181344040000b030095480100600c1c00315940003602c043e4214040c00c8032003c0651400383d4015901b55000d020895180c1d40007003140340d10f101038003540d15802014001070b034 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 864387383 1250 864386133 864386143
    0x6050c070629040c091a0c0a0c060f0c1a25022b05030103060f110f0306030d050c0309010e1906080f0f1509130206030703090204060506030103050a1202 67
    0x58001a08100c550304038211440302102001107200b84580d40101950146014091250b112aa590b0303051704880c6000801c08280b540c1186d000f01e040b4061000421220003004941c1c0110f010703d044c4c41d00b0302d02d171540180c82c440c0250004410040c0904414000ca503800e4003444801d250020a0300b00d59030b445008541ca0900c0400c5005105d244441702030459500240d030f4802c059410039042000d2a03150514003036001340400b640042a0240010404540c1036400244001c81072000465580d1444424031725035803001c8500d503041c0314003006200c2e04c1c0c2020005400080c3c010f0414501d04002008602e649004c0ca198a42c10404011001e6915895011801440c900c0400c0305183d0240c03180c802400c400740488164400e07070300801c001004e586401c500c00e4000c10145115040c030a910405003c110000100702008003e9404181c900607102c130300c000c5100c0c0001d0707500025110040d00c104000c0d5070b03103030f031006105007000e10040c004501c020a40f0185954010030314491312b01013004c00d0b4242 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 864388489 1106 864387383 864387397
    0x112050c040b011e0207080d051b01051b0702040b1504031a1303030c0c050601060801060207080a05030d0510090603060f39050d240605041206050c 65
    0x100c0341c4045440891130031803043d01c0c0b01e1622030303840c02e241043c0340090500080b4005488442c03000010312074282001400024011414641c070403100d0420140c0131035058400000b503200840d0356a5022030b10402001d40f00902c00c4800040011150b0041c0c03109441b00000709024031700051038041440c3c8602e0000e00500105509a20128020a80b001210052101c101a014007040c02041000c0c000e1030160b40d0403400703606109009081c400b45501c90701040d1301101907440096030220503140e00d040c403014005510381da20080e100300c44206900c0049540d16095001c000c1c4110350700300c181c1c6a04240414405140d25a40c4142445034020341d0f00054031800407500c6110880c10004021050540380090424952602010490308a00e083c205801140c801200d2070400c44008000141010708085040030310301842c00e2100c85014800a05040d9a84000b41980ba00c5805a0743e80c = true := by decide +kernel

theorem cover : BRFrame.Cov 864208633 864388489 := by
  have h0 := BRFrame.cov_init 864208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 864208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 864208633 ≤ n) (h2 : n < 864388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
