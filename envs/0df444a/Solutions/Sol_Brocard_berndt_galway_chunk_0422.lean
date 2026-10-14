-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0422
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:43:57.26997+00:00
-- url     : https://prove2.me/submissions/b431d983-39bc-424c-8b2d-8e9e031985e2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 75719426 ≤ n < 75899282 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 75720676 1250 75719426 75719471
    0x21605010603030e0f0904030e150a081006080405030f0309150a0504060515061b030d05040f03020c0406060801170a06020c070f0807050d030513050d08090319080912010906022803 79
    0xa000050a0381c88069031000702cac07800ca08000b0410180c0b907100c01400140001800d5455000c0340c2000d00002c6281c1d4480c02c6a60b200300c1d0084015172030440d51103240d25031070b440280a00e006015200b004450100c2416840e03028282442001c24641010b003031032411074201501221603903c4035421001582c50310f10039a004586c0d00b002c0104081d04070511281148640301400400d140703000b040104010005204161440c080d600710707640118401c0c148000c036080c6e4080d041c0030074407010040060016002e1000711031851b078001d480e01c100c043d640c1c1c030003a81c00c109140cac0e0715600402814444001e600740108000e0501c0d41c0100161850700012541004000c1000b0b4208000080c81c500700509a0a02100a29002d0440c1a8140e118103013860b06802c6010300d184203001c0c1000c90350014402070500603070141c0003e80380d45003003218002c0054203010404200959500ca001510100f1420300c0079041414210002c600a49461140748098490031030342c2d9001c0c11300e444070f16000641420444030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 75721926 1250 75720676 75720683
    0x301180f0507021c0201060305150115050301121509060903052713150305030705100e0109020f13090c0f03060c0503100905040309090203100609050f01140a03021605010603030e0f0904 81
    0x1040404c802508a026041c9500044c1803849406d00ca10080049100c800e03048803103a60200d03001d103141100840d85403100788100400300b07080b11140c1000c26040030f00340c2e156410b0010001000071080e030350300003510814a070540100c0c0f400f00310400950380d20301c0ca611000c402c11903002c1c111140840094405810620a401c04540d14016960519a84034250b4003460300b010071640ca81e03e06152441c0e48a48078a041d402107402c00b10301c6400818140204000381da4001c00d240310a0201324103219401e40c0d07148070140403070b46851200021400403039003000a0040000c1400207242117003004001e03a00c123134510104005017002084400ca44070403d40e0700780c0e0109140814281c07074030709044845a400303400c2140183e200205001d00d0b40b01102c2c1c0c00c2c08480700c54881c03135440d0b507036001080f20b001040900f103400304039040050070308110603c1c01024450403174100107040c1030302c0302843c90060000100454890795292014003d050304510b03d06155001150385800c05202c001c0490110070300588000c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 75723176 1250 75721926 75721963
    0x7390b0715060e0a020c0106090c020307020d060f020a020a1101020a0317040218180f060601050d020310120507030506060901120b040201030b060c211e0a0201090203030301180f050702 81
    0x81c0103007400c0c0e800100050003e1000c4820b103040485500740254040c0d90500034542c600000042e01d000f00d03001c0c510341445031343c0185061909d16001d0003413250700c4030f804540d03241c0d8901c0e624419020620280c1b84505440e80180070302d007e5031038004146182118990306541c480280d4030002070340154200c460300da000d88400001d40721407010540c0c401890040348480210801002405030704046207451900c000d000700d0711510001c540840d11a0810750327029001078820003c008001000d900256045043c049414003040c3d07845102c9510100309640480e1942c02c0b0180030410b0000801030950003000072a40c0d150594500700503a03032085c1041c1c0d0f0041039101c450340082d042d03a000740c0c070101c0000c4d00980300590380c401e4103e100b030b20b88826629025000c04100104284001d094099070031019110002c102028980f10181c2000c0c0c014a8201302190341b07454000006844c00d0002c2c60080100c84a0b102545208101150030f0714155041c800c02e403450041040700499000070361010540341030446 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 75724426 1250 75723176 75723203
    0xf0c01020105011d0420030102030c250305160201020c03071e09020a0504050108041a0c030105030f1207021507080c0c01080106030209010e0f150301080a0b100f030206030c07390b07 80
    0xb190140318414041f50316510100c20404940d0f0711100601c1c2080e048042050b03200911505503d40c002c0c02c00380600098001e2014408070704807694100040ca0050045441c200c64810019150096680240c14902500c140c5141c0c035403012410032010b0404080c083d130428001d40e0004140307004905c02c50381081030401c0032800b448040003181c040c0d440c034840780000c10301c3c280070a13490560081c411107000303100c0d907181c0421144012501c0c140740600c0c2c02e0124034060b9180c08102d1884090000742c2080b920410180d4009a000b02c0280380320f60a12028001c1020781358005420000140d00407414180104517204944c0c1e80324990040e0b1520032242c01203001d903202e0115005d0f070402d400f4043c20542c00030001c40c2e00400061202031143c4512009e10265543c05400c03e5402054031034003185000082040c001494400c01075a0b000c4070780300a140c203003105a1a01085403441082108190410003421a1050b000c960100b1807440d091000d65041c61501302c58503060b1003041005803025207205070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 75725676 1250 75724426 75724463
    0x10e09010806041502190c050d0207050a090b030106270b0f030a03141c090501050105060408060109240617060316060c060b04060605120a201305030f0c01020105011d04 74
    0x1a0382599400c80c05072008075041b5200a4265650540c05803a0342c4604070b203030002c00784002159010b460029104a00307051520b20060042c00040c103515034955220200801e8503082c42c038110080e42c0842154031740903e5200400c504444c00d421045004801001715202152400070398103000350790500d083d0700210056400c803000e50062500100300155580030310b06079405d59401c00a0a01d02900080081e0b980e034004001c4544a5072181d0710440e00701c0c85c0100308104055100c803c40504e1f0b80d204446981420008800303017680e0742c00c0340f00440c58040000c004401000500307a40040150014191030701280200b00c0d81d01c02d00d10400d002c01c0325103000101080510f0300b00c0c000a076000780c0306000c2d103500e0307040c042c1032078020110103461001c03c0000100c40f400d89014248104090030075a00402c0ca450503c140c1560150301480c0400121000010b90b0703850411130103c00d401c401c0064042c10741d01d030b0002801e5481c1a8444101d40c11304881131410030311040c010b17a82041d030008031060044030001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 75726926 1250 75725676 75725681
    0x10207030c080114010e1303080a020d02040b0408010c0c021e030f010504051e1204092708210f130309030b0c0703030c030c0e0f0f0618010e090108060415 68
    0x2040141002155000090386402c1504042c001c2003210400b00c0b004d03038850417900070069088510b0703d40b810000c2200c80119015408254108140724005031601c0c0d03403510004103a900c6903024480c0450005410840000b00303205141d500609840c0c05190016183c00042c220f102d421618440903958041540700c6030303020484a11054410b400a121620b0507041c460303182c0c1c080403011900c008030350400c0b1480c20b1012440c9600d0724401140365013003c3c01c0503848401040400e1161441d041c1d0101d5003011041c0c2d080010070b14a00c0b40c0f114955031038401030070310100004c004003c000710004100344015401c4448006e0792140500360110f03000e2015040c100c518420517440034091510341c0d4240044105584010720507a0b0290b00e061003000c454410031022038240490720700001c2d140c004500c1d0a80b40c90081d800a28400030004401152139000140256000c90240309146110301c0400740e02c1d50b0410186800c0b04421035285440350301d030141d6035031128001000103042400442c02149200e0696 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 75728176 1250 75726926 75726929
    0x10e0a0e0a18060203040b22080921010504031d06040e040503091011150103052a0301060603021206060f0301060c08040e130201020f07080a03030b0406030b0f160c0b070e010207 78
    0x441002c050301c205080c000001c1d401501c0a84d0641c0503800040d600c5410000381d001c0c841030300045400b1407072030f94584000d96000442082e40c440081404203c0010910030300006100c9140700000e03030b03410249005007080041c404000003440c2120040d0006940f42d40c00e840481e84241c05085143c1c0d218a4414154428441201e50200c1a0160b0311442135201d4144e012102c1c03036008599200807000301e07414007820240b03c0185164800d0000588a40c2601c140415017400c090030805070707100100019003510041d4002000099011130303085548140a5000e03034004400b42c50f514544100c070486540c480c40140181030602815505003c00c201d0680c0480b40181848900c05145050442d0314818101c07960300305034014410050101040303e408540c0380211510000141790805da980d17002e8014003254021039610668a900020110744403c280310321a803003400880c01c503071410103075208403d00c038210450108800c1104980014139160b815076002400d030300b071140d000c90002d00100d1030145507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 75729426 1250 75728176 75728201
    0x606020111070b042a091a130b030f010c170a0b0a231305010305101401060e01021c05190305070c08030a020c0f010b0a080f1203040302030c03030420010e0a0e0a 71
    0x600d00403800c8400b172904c2441611134002d0305001c20750140b20182c0e0411801c14802d903104503621840c01c00c129a56018140141c405419101e2446144500d80d0841d00714070501d00104400004500000c1c00780c500881e8406458034007080f0250001012a4010390039000b080d80907000c261040098501c0f00c1540d10349404000e102d0030201302c0c000600000f80800384030441c1d5030b126290380101d0140c0785005060300000365000c03400d01c0c1ea20307164086034a003442c9058941940a00d19400c904a00800c2104000d0401500d980742d4402c081c020740f40e1201e8280804000f0103140505100c0c055502c142d00040f5150007110464481d00e55100040003485900444041032054260460b003c4c176040d044032100c2d00d0304854060707580d540e071541103860b9140f416448000e5002902e401030000307220405150424001d1044a080c01c8080e2403080ca941c0c4141c0303064440b005280e42d180c4005080d12031842004100f844c0c610a0201140041442c11019000d221001c070031980c002140c0f80001d9101001c080030b03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 75730676 1250 75729426 75729473
    0xc06080c1c0b0901051c0204020d090b01090b0f09041203020702061207020709060b0f07021207030203120304050d0306081c0311120a0b0103020408030a080723030a0606020111070b04 80
    0x44158090010300440201900030140030f800010365140c0314807030301e0b0780038000c00c1d40b100460025400c00000307603c01d008111046554665860110301501c0c40d0030b020301901140010101148000c0080b15151003039050b228040001c01c000c0010582c0d215a4000b40c1281009a00c0d8215480040c809002d291302d4000d025081004210940364001394100464013030390403c008250300c4e15814000381c0300358081510221410041100142482a400360101c0d80e41c406950b5015220740c00a420000352400303800203850044184421b01c8024480880c0d41c0304241020005581340074045a19004000341d45489540e5190908154600a8014107d01d1983e2250316955802008480b0a0742006541668283d40380004510080d40a842102e042d02c40c660021424510702840840b00c12500501003010084464200c0210715444050a128603404082c200e440b490000e5200e03049030318907440041161f05240d02c07210120314440c22503c1c202d030000314220403940d8a042c444515400c002d1501003940 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 75731926 1250 75730676 75730717
    0x1a0402031e090d022a040c050403110f0108070c15061e0515040506070c0312050309010c090e01050d08190c12030b090c090301090b040c061b0c06080c 66
    0x7400c8200141840950103550596034840041d0243d65035001003038140581d2107403d044c4070740c00050721907400f4441202c03400034121003640c0100703068503040086c00b00030850100c0e05000704442d4140c01c00c1100c03015124044c260b0036210000300702030005000c070340511682c030316290207100f000303001c00c801d0710a0310b4001d120181c0d0358401e444d10f1910400d005d0700120340e068004290f92608141504902c840c00b41c41c03504050802040101355880000e0469400403090340c0000002c650b085500084003550321101c2d00da103001450079094a1800419804000300741030140b110b11036948031141903c2042c0e403000031095141c81c11070042e01c240b0101c18112403d5240c0d01c144254040c2c0c00c182818400c0307088400c024040360082c0c0c1030351290b400f0150700011402c0056020140c0c3c0e005011010001000840c2c022040d844482c0002403d0714181c421985088041c041a5042201d00700014103076043d40c0e00080c810b8652410800c4240181c00410400c10042401c2d4442c101c1502c4c2c042c1c0c0b03c00110700005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 75733176 1250 75731926 75731941
    0x9020414100836070f06090e0c0a030506030f010504060501030c150801060e030304050414040323030615070618050106060212071e0c0b1c061d060105130e0402090f04030c061a040203 80
    0x117030f451243c10002039103104081484520b0307900060080b00d40302c071814180500300c0d00036409820300425103501072240e000341140c050b4090180c030740294001c410002c3e040d415030604040c40e000c55004921007100d100d500400c035039440003546044840500d080c1042d9102280024118400d5502460380181041c4e0030f540b0700c802c12007196004611a841d038021240c4c4200d20389079190008201c07104403070720174030014400b4140740c0407405010078070825440c80c24925030303101c00403504a030400320a1800d090000b071040000c00d2040501818041c002808211036403206c0184910440c1c0c03004003800c07000040723108103048519108041c99844205155a19281c164032481b94100d0943c900040103101403001d44840d01d4801c04080d10303801d81400c105003c02e9400c0d0060540041e00030760400604002d4511500921504080034202d00740f0f00e000701d0b0800d8010070800800c003425055080c40408140800660824001034410340c1c4043c002c506101c0040e04104c0b68860320041c0c0340c1003400001040b406 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 75734426 1250 75733176 75733199
    0xf02040303020f0606040b01021216060f1508070f0501050f090a030822140103050411040f0204050a0e07080f07020a050318030f12030a0f02040902041410083607 71
    0x54801c110444d5000c0c0e48440800c0240d4100c18551805038100003510110f0f407140c403004000781a00100c1602c0c0307103191030352980c0845040103040f06029a40e00982004c0042c011842c400500944008054980c100240c0d003805099504c1034130b0510000040c12034450707030594207a447c5503c0080107030f0041d42c2d403410041880d0740410124206004540600004c0c58030202e246810765680b00402001c1031350040054004100141090ba5180c081c01501c1007141d445004000714100d40390409604c031440c20007032103a0403a641d00301c024a030780200f0401000c80c0c1e02a81c0715500254103440400c2a817107860301a0b080080f030000c00340841c04001150000c40104181c004c00544013a01252900c1108171942600d801548906d51a91102040843e001c0d01423500980c2c0a5010000018601551000401c003203038090b074460414040340c076a05d09281d14203001006041e001c2410030318114640186032514524001c0a08a020a01d260329129640714403080701c42c0180852080b07c020315110380740e0004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 75735676 1250 75734426 75734443
    0x20a0305071706040b06040e0102070501060f06030f0e0c0d03090e01091b051227100606020f0a1101050310030807060614120a14190305030603010b06040b070201120f0204030302 78
    0x341c01c0c0b1034825402c5036140000d44511458003d010303206a03490350350820001e84002c122500e955034003440a20f01185d420300c81d040007841c51a50701d40f0014038003030b405419601225400d0b2031551134546003c02d000030204c0c00c14030f481c10441d0b444420300801d15081d2404d0560741c00c079958400304400003140200b4154407103100301c0c004101d000c210100e540c1c012940d1b4868000a00b1000781004080381c01c46011240c2d0707207444d01007205102074410000030b40900d440e01840000d0201c80e107403042084000d0b010f00104149040040c05088994040e8440080d1040348080240c10800f001001030006421052000d01941e80092401c1d030710756403401d1042c05072950b406010448500c1540c0c0808500d17005801c0c2400189007000307032400203481c2e200c1c2c4002511a103885111405004510b40b8400d8a0a6441c1c5032588680c681d141c481c107210084c1400c488000812074003a5074100300620000100100b603c4441c0c1e070910340302d00761400b03861940010b40321504404140500114000c001c0680203c0d0005 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 75736926 1250 75735676 75735689
    0x30301060e03010b0f011b11030d18050d051c031508010c2712020301020f0f030f060105120a0b030705121014010506030115031e061404060803030c0702040603020a030507 75
    0x400521340004100c100081881c2060105102c091031031a0707000c0b111706041d08030b0300881c5c400c10304440200200742001c40c1203a0701d00c00501c0800425100d50710202c500000b83c0029611040400260359466544440b000d108400d55403050380c103001010710907000850b044003171502c600e0009540c1c8c40c0d8980a80b600022103404280380e00d22104644165907003030f840b07800d14040900c1040d03150806d180c254a4542000344d0b0555000c201062580840c5e400a06007010305903c00c50707072860030340070030141458050b104e42d04001003001034011040760001d041d074029652043c00a00f011a410020349002c000d5800b103500814498645200d15001050100b0004140c2105018580004a44001d003410900680b54040028401840b5500b1035511544501c2000e080001e9030f03400e0344207081b89050005c04148091a1686010300c0100801481ca41c4098070540e8144810380c03d0990280c3c80340802031207150303204400b0400c00c003959100c0e0000c01c0116006404100c1650b01c90814584507409405102c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 75738176 1250 75736926 75736931
    0xc0a02030115090e1606050708040b0310030c080f0d080a0e15070f09030807080913050408041a07150b0102030409020d0b10110703150e0d0e03010b0a0503061611030301060e0301 78
    0x2005004c3c042099042c9003d003c910360321a41c18a0300035201e41d00018016541400180701c081402c91100d001103000700c0590814011540c51494100009a416082034042d600501d1701306170b40318800030320f0740040b42c002c3c20300d48660b030b070b607986000f0047c5441d0366100380c02c0c071407001642c045840103c0500e0040682d80c0c2e404662682c19041654200b00c6440002e00e1107400b009088082410309d001b070030502c0c5d001890840d003c0c480c128054192030055505940340c110000b01003007600d00d0750000111000444c821541031403403030707100d808418824513001d40340d07144c4408030584107a1007841103130040d02800d00c045464503c0403650000074103400f60810b0042c040c12031040b80242c09002d40c403a841c4040801030a11606569400d0501c1c00f600b0f0361418003d45910381c1c1e041c5810140192141c61001ea543c042d008140d5004260035210110794960081d01704e65418001034401159880d40320a5440092906000d030f040101c0d0f480ca00c015001e5085c0c0401310001c50813990201c801140248200c2c000e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 75739426 1250 75738176 75738191
    0x809060a0f0806120a060c0e0d031d180a0902010201111c060f05060a030c1e020102120c0414090603030702180405070905010609050906040e01020c07051503040b010501050c0a0203011509 82
    0xa010013414004003040362036004440020014034150030040d403d22582c50800d4500c00640007041038000002011000700d0549a86c80c1400911882c035545034410403a02c0c6c1c1c3d40702d043c4040700401d200c0040c4c406440c054940c102c100659000350040c14440c41c00038207607945c0315941d8540c0360070140741c0101d4012590408030006250860041140f05503400240344c540351001200e0158000c1c10b06614410074410160181c10701c00d1180140003151410b1074001682c2c58030310300111441c0c60380c000c2000264400501003403203031a0485280034640d080540c1c02415544a40c0d00080c55801150402584104200d03406144144022141e03802148204116600709031241c0034042600c409000d136100040c00e0500401152904140d46500040c0250001a030307034641c240c0c3c140c203990206042003030950054208026604105140058000003108200e0071400c2c5503844400001c01071044504009020440d07840503c0217210b000e04041e4018000c21403120001050201c0740c040307200e41c0c0044c528050300c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 75740676 1250 75739426 75739429
    0xb0a110c040506060f0a0908070605040611121b031605070501080106020d05120711060c0a0e0f06040b0f0c0105090105190219110f0f010207060e0313060c0809060a0f0806 75
    0xd26010f840d00800740e905082545080c03046a4100c09241c1c2c0030040320450004142d00c042c880321016209a90f82d09550741d0038604007030444c041d0049400d9543e800300c0d07100c0140c4180321045d654480b000752262520340c078181081510f14091802100090181040d100081000c00070302141142e43c04c1e02c5800042e071f600c1c2e42c241d89446400342d005010550410190903442c40c0d95001e56400303d00c40c1441c40c0c90340715850003a45003180864504d2002d0780001810f0448541010b07030348280d540129205d13040384a070a804200d560149200c0ca0981c1100810f803481d00304061001ea03990501494001c12052500c0101180a4401903a81c200300c4048071142183c00c0c000350003110340c00740700d03250703e0b003017001e04c080040b1070355008540c3d100d1107070041d445000b0340e6440511420f00e51441d000c00240c0c81c2c1c00b850501004840c02260007a49a40c0304104024580d0818a0700004441c01c0e403c01a514284c5d504000180f4450642003541c003400c00102d40741103e404c800ea0014001480d81c2c0c480c195030f505d00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 75741926 1250 75740676 75740681
    0x90b01021504020f0d060c0914220e071d040204061205060613110406030b100201150b070204090f0605040605010b21060a030203061603050f0705220b0a110c04 70
    0x4001400c1d511036500018058100f00c40c0008080e14090510f545504181d115941124403403d214000101d0b80781040090f604401d4a040d1484000c4522003400440512801d070103035072001c440f400c2c00303884459100007000188034400007811000c410b07040980d200d0f03011400e880000c0324103d01c507074508000840d01d212031200103c1075592240050060b529280100080c8464002001c82e8868668001c4040708240601401c014403050300c0c0400c114107107104115003141c0a0000c2406c6a14040c52101d68664a1203c03030102c905100e001583ca031107a00100d809408942800f81c032010b800300340881040702540c401e51095014080422941c2d0f02e4140100c0b2031721032980340c104c81c2ca4a421071a404001c40f05501d5070130801c010104002c21ba41d030380c0468100710045a034807045001c0400036880d0729400d4019258014000c0400406d1494a8440906903004243c1c4258400c1c2591000815582440440380c0151903407014064545a20341c50080072020301100c0504507024000515451741000e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 75743176 1250 75741926 75741943
    0x507020601150c0609080f040609080d020307030c050c090114010e01110706050d0605040c03090b09030403020a0b030703020d0f1a060909010302090405120a18210308090309120106090b0102 83
    0x22007520140e91004102200c800f409020305803000d540d10707808140080c1000700107003202c078006954980c8035403601303202070000c8400ea8030a000903080360f40511581c1e6404030859074990380c1824810035500c8a800c2044c82d0405408a01d60089000400072032203004a41030000018000d070f0700d010000d50300ea401168a142c0c0205042041e520a0070140140f41c091805070850040000002070f2055850b80040e0968090320110804070b0743c1c0311014001d0002c0e00d24001e61000561006500c0c161540c0d000c11282e10b164824207070200d00100106426611940464107041c0d440c0704203102c000c07800400c100c01018040016606010102454000307410400240c550800008280011030ba18640900030003a00081c0103d03058080e0380f451b65400f40d0240701070003900489a4481410a007104000c3e00001007540003c6020010590030103031300c2204086401b28250715140240c0c0c1c540740c02420b070f0710318044c0e5401550b0000c1e003822804d58644055214508541810400340054060140103985600c01c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 75744426 1250 75743176 75743189
    0x10f15080103030806030c040603060e06130b0c03061f0f0f18050904050c030a03020c0a1205030a0c020f151e0c0316080708160b070305010605070b040606080f100507020601 76
    0x3840d004101180c091448a5030142000c0c040d41c8025004000003000c565481c1c104a582c952740c5c5100081d40f40040100341e9100c0c4400382040c055030251749400d020505c00800070000d0703540c00070004070706845840580d42c1035080524900030101d100e92000c0d0500c0c410415a0002403620805520001d100d4045100031130300c408278070441c4604080901440c14402842a1348034403401e800138189460401c2101e043d18000c0c0e010b4600703c14504c040041c041450b81c48003488103a03101040300400d00120403500b5030b08031800c04094001300ea10104454140c100b040c240d0001e41c105a031019200020010460140c62110001960301e800341c01e83c00500a02c0d45110480c1e200380009114011000308944e0030901842803035040c8070241c2d43e501d405038071541d0011f4040c038070282d0810810680c8180715402c280300381000d105948c103140d4002c3c041d0140e241c0c081c0607a40401c01007000d20170307254080c1000d00300150564903003220801c1810f550b00000c40020600300e15140000d02d00b00d00c0450304030f068500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 75745676 1250 75744426 75744437
    0x207111c031112070b0108010e0d080604020304150c0203090102010f02131a040902040603020a110715180e070201091511030601050c03161407060c02060921060906010f15 75
    0xc4548040780e56481c0040003503410701c035100c4821082020b030409442d050348140c078182610342c10700c1c42c045c0c20344003900700349407440d481144070001c5076800645903640072109680041c1c40396244d00340740c0048102c03010006107076854520004100c80e03021004041c1e4038400e800912a40aa0b6074607013089202d040d01008034503d86440901c5401254040551140b001040080c10680c6034103825049038410351003880070a500090740c8064130703042150201844042006001a185016401d280c076218a1a000003040308180d0a206420107450b002d034050f0540300510205460700c0034002c2c0c000d00501c20305440001c00744007040300c2441b2900802040c4a0290091815030b2039a00041d42d05401106180700b590005110380043e50340c08400101d0741f01d0103000305035040c0048211450529100e504440204802040d00b0005601d820741100c21500c81614204500365031011500c103030b900c00900b48001070040300c05200310914000341090598010298400ca61551303001d12541c0703501e2081c04440441d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 75746926 1250 75745676 75745729
    0x140306060f010c06050a05060a060203120601050a050d020c0307020405060907050a05030a020403050f071811040b0904060e10140a03030e04051b040303030509010605030d09150c080c01020711 84
    0xd015552104807030040c140b458044507039507600e10030795000300d80a4500d00d946404028462030141d080e640104440d0000d90700e8407501d031429195010004100c80d040c88000140c000b0307401d00c603504850410703072954011502c0380c0d83c12401070307220b85c0242c0c0c060b1710030780c01e02c00440c0e030501d014281c0c01e0042c3e110303491315440c2c00b4800070260390540008041c20103050b0309000000c0424424400b005155407454040c0840303504005160b8038000c140c00512040624000300800c5403402c0c501145d09981c1652440f94841198900250207021141c000b01001c00e02c040030f100643d8560000c4009842c00807031441c2c901d00c840b03806e00010070080d100142c0000d101c146102e807241010343c8a070381c0100408030031459030300d10305401e5801c917846940b0031800a13a8403001c2041c900e100307218400140c04210003420507446445030080004580d80180f0294217a54a020b160039030098205e125152350240d5416124448241914000d40200c0429103003020b0071b1240010742d1900751503948040d40801e00c11078410 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 75748176 1250 75746926 75746929
    0x32d070305040602090406091b080105100804020a0b0406020604110301090c0308030a06080f030c0c0a0e0115051e09040c03060302090a09050f1c0f0206010302060304030e010c12030e0714030606 85
    0x1d010280060790110741c200325009246e11503004110103420441d02c0402e011108141c1c1944c580440c8850a04000042c0d0040c0015550a40344005009039880d08107003a454900018580701c07080d91180480881c0024000746250b00807528900ca5401401b0160364010880241800e03540c900388000d0101410800520000c2e80b110b01a58010064540004031242c441d900103203032580c00600c41c0c2046d48046165000c1903001c1044965409050719440801442e0072058440181d060286d582c580341d03c119040703800c81c410030075115141f0300344034400045205448000380c07070792096050a0042d41080e16004e00f1030b000b4080c003400c41c0e030b000c1c02e2440d091392044038a00c000c081e520403c80d094080c50b0756442d02001e0400c10300010043c4a8400400b40c035440401901c011000c0304070b40c055400910040016a03221030540398000d805091103105403450600480d60641030000c0107221441070000a030440ea4035074400d12681c82c21004031030740705071603000800d56141c1014840c1d9040c0d200c1c01c00203280703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 75749426 1250 75748176 75748181
    0x10f050d0303020d0e060a0b041b0e0d0501180311030c0a060e03090d0606050910060c15110304030306030c08010902060403110402040314010b030d03050601021506120a050102032d0703 81
    0x400d4000c2c0380050919500c0303a4003100361241070200d24074942c0801e05000e07100c2c00e1803181047c010003c54040207a5126440c04425400250000405200b4400d84090140e225131190103103090f030000c020050082d20000c008014109080d05030002015802e40500d4034000004403030154191a0042c010b04c101a62142c0c041d004003c141c00042c00148241c100c1525590b00a603141803080001003034003400c16040c05a050b40003019911071502c1320004002e0560441c1c1941500d41c1c00c00807601c0200c16894804011300f0388802591410480001040b09245d81070340b210058034400c000d1440101d0340e500340d050981d80f40850107984440100010000201480e9038400050030142016041580c0e0303480305104200c0c40c0468400c0d0b42d4694000c102140f9007406800d40301d000500313003004a400c0600000b90f440102e208001d900319100400b241165a40c8414802c089020404032040e42d072031480c0850107500152030303182565a009140c00c0742005044103000481e17002c1c052545c00f0b580d404804402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 75750676 1250 75749426 75749449
    0x21150d020103020c0d020106080f060402010c11060405060c0a06050f150103091506030503040303020105010e0106050d0203040c03120903060b090c03041b050301020a0e1905030304090c0201110705061006020303010f05 95
    0x5043d803c220809a059050020074032400c03542d00002041840c103900d26050070030300d07400060260403100800c00140c1e000b411202a058005070651803024019022404c544a55000640e1000d00440c45200001c000100c0304804d52080100f40a103840e0841c1003030034800199400002000c465490300c00551195105640c00f9000d14901d01140c01100d02500440f05160026205500b0000301401459024000e8500408030b082c40e80c4001c0d850700700024aa1301030401c100f001c0d0340c1c0020101e01403200150503400510f80000728101518540c100c0681308842d42d22003103540382c2c14040c0201071881c0c0314002030f00c0340b060b81030403a117960703140e070f81d99503d0003420600700c03502490310080411603071824030150a801181e519402a500c5481c410006c008109119003603114000c1c0c80103100940b40402520100c40349000081400700b60004140d01400d188041c0c0900c5240c0440c4001c00d1280020300c072801000d144403011071203a1a124100c2c0ca0307110034010b159580c0c6514604000c10b090002030030a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 75751926 1250 75750676 75750679
    0x9120610090e010b0a060e090114060301050402090409150204081005041e02120a0f030305010b03040c09020a030b0d050102040603140c091012020307080603010b01020a05060a051e010b21150d02 85
    0x144200b84c04000344d8403503000e0b08034000194007c600e0764034030305001c0c001601401d54000140d41c803c818600003001c0d844140181409650041740b800c85a48070354000c048010743c458004002c521854000350020b4216110310360062140800c14110b05c40c6501c03a190080703030044104846440c10850040c12143c2444089801110294a40c1d200078005d000580e04c0c9403107818006107040d0385080c002c096401c10780101c0c440190400074007002031803082d0030400301c03503d811025890f1840f0180507402000d031080a10380019040941408002045d80100306499954404201040741500c40c0b440011046480110b0302c00e08210013041ca28001050701c1806130a854807a0002c1d00068101003031744c0040e01d0000102c0c03030081c1801200c2c6070a010b1149803007000e100401064100361240d59031441c0c060900c01815a4543c0800c000032a8035254051132040c1c0c4265a10300c4d41c2d511142007944d03200c40340021580010a07400e007510600780c11418014100514001e2281d40781400304400080b1070203089 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 75753176 1250 75751926 75751931
    0x60c02131a15070302060f092e0608010605092a09030705061903050606031003030818010c02060106180f09020c011d0106030c0506041505030a090507030809120610090e01 75
    0x8400b60303941c0081030041c0041928940d2a42030910740139180400c00b030b0503181c0400d02c900800005501c00103000c00b1200c004c804030706454800000d10005da94800d00d031b90f100030f0b023000d10101d650b101c150003031000c0769000d0380c0c10031140d0b4a095004014861624000c803400d000c10b041c40640740c4034007020341a1140010240e51071030340d566000903d10b92000c1880040e80f062001080b0642d074042c45060351251040d146603142d440c00e244011002000c40c00000c0500504c3e50206006000c010840e62014011100070403034130140d5000030791340704400d00c03800c40000e110f080c0c0441d28401c00003152045480002c00f0002072428020049c1c0a504803207001d480f590b40c3c82c040914628440140302811003031041c00040c090b801c5040016a0003a1a040240075850030002080040c94444069800410031315210340c603502c03040d001801400143e200138145201d102800300501c000318006000060701160101c0d0300322400d40e22507445510441e141404414941001c00008815400100240c0080c1000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 75754426 1250 75753176 75753221
    0xc0304080307060b120c0312160b01120c0807050a0302010f02010f090c05040605090603060105100903050105280e060c030a02070c030f050d02150619080d0f09060c0213 74
    0x41529503000704a00351a81502d131036504201e07090075200d142100309500054054550044c002c240d8030000ca41941100e0040050800101c40c6410b412405c403d0340243e40640319695407051035459002c7c144183d03102150b003503002404010000d81807044900140400130901d103990015076070800b0b406110020f42d522070300b40290282e520710440d5005032064000b05081030a00c418002110400d0300018040c041d400107200c810365000903a241158070803034007403c02d01544001110652000d83c002001c540c01d0206000a03085800099040101182c500b100080c601e4072032682aa04212070000840c1c03c90404030341c00200000003950f2001d070944003d4541200b43d504c15400b0207042d0f05c1034520304a00000e62007001f20a00203510801c622340f004080001200072941d0030100081c0c040c1d803140c008a00044840e00c0c01483ca000200f5903402034600103a14248068a4041c408031400001840750001284481c082c0c2e4440101b10740103420001d40c4c500c07555500c00246100c400c040300c400c0303a0702c0c42e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 75755676 1250 75754426 75754439
    0x71406030a1d1608071d07030b060307030203010e0c03040305070b07030b03030a1107060314010e06040b18060f040e0309040207060f020408031c09082a0f03091815060c0304 76
    0x41e039010801449004101c5849143e42c11140c02d10150403600e1981c0002e4001c00c04001c0404290161750079040d44450303180c9031001c00740c004101190380c240d0840400701c10440855003582c0550f0403504541d00b0303c041c43c1d03210076900c41c8601c400c4400802127542809401c0c00b1600b40c0c01d0b0250301c82554240019011413081c002071850b00b12030440c400085080060304052182806808018892402c091281c110084d8a508000707005008030461041480c0c00160603a0701c0c0d402c6a501c105014240484010030407001e00e010304003c03110a4083c0500300041242c4c1c2c1054070410640e5180c00014500700000300b01048065401640103a403410340310840d120211989100910040c41e04000640d80d42000c054200310101140148502c0701e0314201c440c2e030106904030115800d198004e50604400202e0000c41c0f00d003a0f0020200030780c240305241d0b00c10381d00308000001f8103039503804849015503a68a80c4d00d16007420422030b003140c0040301e0445400c903541000005000b42240d11025241095152203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 75756926 1250 75755676 75755711
    0x1120b030a020918072102120111030109020306010f0804020108010923010801050603240a0b0118030c06110106080c19170a03030b060304120516060207080a0f02071406030a 76
    0x944160b6259600003403120913107030812000c070040502c5842c0b20032091488100142840c2001c00183c01011401608000c0300006c1d4030056a182810f0380c03480d00c03540c48803035010013500120351035800300e4010036030b2940c850702444a452003594142d44030b03c05a23092000d0300b03001d0004000e900b1642c0700d0f0080340b000c0d41902050404d01a0090800000c1c0a1501d041013501e00700c584100c1c014135a80b64520811081e0a0240b5642d2000440202048411030703100125030903202c2003a1180308a0350b850002c010003c2c44542042114041c0d91406001101480054203e840f184164445540025220380040c200b10501420f40c1076051749214032503980302d280c102c0422448110b64000e402c042031a17810183c16204072800380300c1c283c3d90642589820f56406450a41300725490081c4180820b01300b13840400180c2072103155070f20500954950400740784c44015608544d0a00000c078411640924400748005203030720031207107412005d048059604050040e030390300c0030300b1980759681c403910100b92480014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 75758176 1250 75756926 75756931
    0x3031206120307021c050d0816030c11030c061506120a0c0201091a04030f032306130e0a0b01090e0601030f02032b0f0503091b03150106090f05030102030601120b030a0209 75
    0x180c40b044410b400c1d911b8003509200c600305598051226140501c40e140c444404420103000050030000f425050400081c3c2e00044854610b92640c4000100403024000100311103002c6d80c6410800b00b0140c0503170b01000707042e02442000c009400c1c108070008500341c41c65040594000414000050b1055140d1a040b0904a04030030081d20403c3e024280410103030f000c190403000c500c442c613040041400e25500f84c000390500c2342c00c070352040e0041004035109982c0c201440ca0310156001d01041000300c1003802c5515074145c204c0940305103024000008464000c0c1c02088507a0720518003400070f82e800c659440049024859080e600351140f0040441c0000c2d880b101220015000c11510480c00214a030040400312815282d030b007000310034024040c0c6200d000425109185003140e11841c104170ba9070103c2c0c908407000f040c240c001c955080001a4107904000000d094400350225060001d44a4060509034482980c105000451217404076800b0781c1076a02801c1c5c0b0881c01020b8a000c2c0540b600010710b4290305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 75759426 1250 75758176 75758209
    0x917030c070314070f14071509060e0409021c1b0e010312030c0e0112140c091503090d0e031006081b03070b0d1104080d0c030e0303120612030702 64
    0x40c40760241a0080d010300e6460159000640c03403c131540d503c00c5800000744400600907a60304c0311140d85c010060013032502400c101403580300e0071045041c000f484118144034a03004106081062038042c18680512408140c015000c50a00b550503140d0305500151520195880c3c071070341e48045401000b404440703005200700940403100b0f504508001d8001240114170006051400300e007850013a42044410152078424204810501002072581d000f8010042403088a45070350010002c100c000700001c0c16041c1d0081d2030140c800f66252540568070b10064030010320a5120000c8078403030500c1114a141c0881020f411745061484001d1060282c8995070800380aa8105c40c0021140010903002038602100c103c0c0109040b501e1b0800e00200c6201708003a2a80041e02c45551070f008600302400c8900400918007110709851110000820b040c2000d40e04030f00043c101c0c400141c0910740041510144e664484144006884040400401c1081c0d104035145134041806514003590b15860303e003045901 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 75760676 1250 75759426 75759451
    0xf03030f080a0b030607050307030905060406060f060807020705060702060903060f04030311250602070c060e030105010b03010b03180c04060303090e0901060305060f0405160305030c0c031b04091703 87
    0x900e030405010a10020304000b030292816006103100d0750300090380703500224141425035594980e4607003140074019105014040344070301403d000800486a0010b4111114038450712112030701c4080864032480151800030044c0e201e400305101d0b03071502200500c0c20780d200405071032070725010300701007401c00340c04030364211040204404010903d134042c01480300410790201c0710391410b032000c05103210030090070b2042c8455010818007803040002c43d6044451841d00201e00510180d0f58000040181c882032100034020750a110000032800b20100c2030f281a0740200700c0c0c650a647d242a10403001140e98020b110041c0309121004d0105e0301c841c03150303d0195000ba40c0d1801424240701038a26a07040207030202c06560325001e0100041500814030ba904590911000201074032941080d40ca0700003912a5403c101e20b46410010070003000000070004076940300f0585190030800f034201a1140c0c0f000280076403120301d1264001b110b00d0203601c0001c0451181c4c140c00480b40c2e5905940340f41da041218006503c04 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 75761926 1250 75760676 75760697
    0x90108060a0e0f070b031005030114011406160305090301060b0f04060314070507020607050309062b06050a050d03020712080c070e0c0d05070e19060306080c09150303040f0303 77
    0x9a4500038181c0c0c08410000419000c0c0083c1d1410f40e880300144520720000d80c0110220b20359104c0d03824400d0050200030000d00c14070444010328440242c1c207206604a04050805044403410002c0c00d54009008440300c02c0c0740021903032402e84950340190f10340303949950b80b044041400705075900503050103001c004425880b03900b00000038003100c4690302d21344100702400c0304000f038840d4060300302d030f02855042e2902ca4581505107080b07451409400d6405500c060007180798142d21060034121901c01ca6442119000f00c42050910303412184580101074000d48002010f00050070001c0b21034030701c18802e104640103203950700c080b1907881088000841c3e41240009030056660010010440a4051924800828101505c041c01d852164804441103aa00d580c002220305008500300340c3d19582c094030340c0c44803618450410f201c20641d400b40b140401d2400c074010500807000208034803401c0001d40301c540261a40041e81182d24140985c01e503041c481008041250742d40c0c000c0c10001144a80c69400500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 75763176 1250 75761926 75761941
    0x3090a08011e11090f030715170105180a05060105070609110a0e07050306100c0501050f060301051b12062107090f02160b07020709020f07120c08070b070e09010806 72
    0x1800415071502e4030750601c0c1c0d01010103803048045800f03d0b54201c958010403011040800c1c1040200d070b100e080c40b102d8814480b001c25401070103040310480c0d400150401a81c03280d0803c0807110360314140c00740805483d000611000f40380e92009030021790504046040c402d150360384c84261907039520111035400c0e81c07002c1141e05017001c02100000d81680343c81d2604a26100b1002088e03404014200c6204111032440742c3c801174001c04400ea801900320f00241310030314081001c2d15a40e48240c510500030742c0f07080d000446010071101503840380f100d01c1c500e0614161640b00111700206010306004c0d8821001072190b0145503480115100c046000c80141180078030b0020744400711b84100c1116000c4500401c140c58690100441d600c0c00c05520120341400c540316031408902d050a1500503580140c40000c4441d43c4d096400080d100151091134004600401c1d410101c420f00e101000c0145000f6041c0841d500189840070020752203102494851030240c42540040c0080c40300781d012150a811100500c00e070b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 75764426 1250 75763176 75763211
    0xc031524020309032808030a15060f02070501080a02092205070201090c05190509150a050d020a031502070503030709090b1005041412010c020102040e1e0a0e03090a0801 74
    0x5200c0140051818880040c0200741c480c0c844c0101c9010111031160043c903000030003040c0c460195040001d2507220701d85004450010494445404000d01044500107001c900c1000c0c11400d8601c0c60b4041d04060b440c100c019950980080c1401400b07035000d001c1d403d896103509216041c1c400390f03240004404556051100c0886201400a03c216414040c3c1000031514410302e04044450641d82226481d0b803144504140700c860707404c001c0d444401c003414000442003020980705604421580f50329503d594900700480741248050082d0400f48008c000c2002c100d0601c01d80c082e5481c0c40502500c2e106003643c540341180d100300c400c1000700752041d00034055880540300707400c2505c0f0f003034a42107190340c00010040e100b030040b031054500080c140c60910b170f843d40360306180000742d0507448001c2c4100c01c00e00c100a07020b904103010311050440c43c04001480c00300c0d0043d02c404003202c0c1c0c00f035240d42030b21138201d0a0b014044482d662405032100f0440c0c0c211503143c074082e6100a052890000440c82d500d030403800e40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 75765676 1250 75764426 75764489
    0x70602121003020f090403052a010c0215160c050703151d0a020405060301060b1204120f140703090302092a07050c0f011e0908070501030905030d0c0315 67
    0x1d480e000310001d00050310b40503a405602d00c0304030b40300d41071641c0d1031404503001d00c6900221548101d003400682c40408403211110005491000240004080d40c0c2c000c9a4403011023218402c4c0001c07070408202e891140050500f0001900e00d4030001944031600c80900e015803550048580b0855101191542c0c030b658402e2052209104400a46041009580e95520546400003038031440e03485020403040e9809500076402045201c92071030703c43e03065203d54001d05404641c140c03840310440c0e841440e554440c4014000d80c5090340c8840311201d141030b50841e46a0803042007241408459480032000da51081000e5200c0c1c09440740920140314440d04201c004101c08260040440c01800210000b83c0003041e2110303200019641480240c0341e036401203403a03528103182040300c1c0b05e00e428180600e1f03910844075010b440454084581d10b0780c4e1140110300300c40700c0c02e402900981040c4880c11003000c8503001103400c2c20507850081010100c40840302e50600b001c0e8031038001d5140102d80c0c1c002e0390004008104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 75766926 1250 75765676 75765691
    0x601020c04050c0d0e03160b0a0e010e03070305030a110f07050106050f0604050909010906050405070e070905011e0c0c080102120105090f070f03020721110115150c050307060212 78
    0xc5003001c02c190201d81c0501302c41d0414071a25507005002d240010401c2d60301306207050144001d0341883c0c1c1446030a0b4001910800b1200c1d06103444000308000500400c032103a00860300440c42c1c444252000c5a03240c2000d02800d85c0d0a4603042903202da00404805803200c54100c00f45140d40d0740061814900b1140c0031f43c0814054500c8414400d440d84d1518203590490300181d500d2902075032f40b44003150040403110301c0200050b260400740014000700264610a44000b080b01c00403d071280c0030305503403100480c85824002400e200c000115103c401480818180042c10b040d280d038a555510714442091a400244a5a501182c5c1100ca026110301440c0100025248120241444182016007010051094062265010485583c0b0388254100c503145900580c0d482ca6032000000e9071506c0340818840c3c43c0000300042c0101d0121403041c410300c405503e064646100b0146482d08040f920004080f013030080c00082400d400c007140e0b050008200c0240300b0b600041c0c1d00d1055624081310250f0107450344 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 75768176 1250 75766926 75766931
    0x162109050307091e090f0506091f0f0b090a1506030516030213090213170c010905010e011b060f0e070812030406021b070504182024030601020c04 64
    0x800031600d0120301401540c0440b1000306500000a50042015031604803c034020340c5031210880034800900200161079124105461554541c00119030b59015103490250101c20000d000c1d8585450a502c044c0c10b00440e00c00105000d2540c0e40020850801201d080c40c100d030b00d81120000c000d00790701010300a804941420051801c0c02d084800c541c1d481007465030f090580c0066000300c0c4100c2440d4803030041c550300906542c0c40b0328140412444016a110b0444604940b440c00280380201160b1031070300507410703904d107218585000011a81c103d01c1103003031070500c2441ca501e501042142502100428000d600219050190099103c22203040340204080754100385404c3c4007907500841e41d0b0340c210404030b08442e125251400c051009110b0fa030070100e09001c0d041000c403c18000030451900300c400844080040038402200110f5590f49680000c0000902019200126045001102071408080c190301904441c4903100398901000d400362403010702c4c4c00700030040030790784c104000741d20640182e40c113 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 75769426 1250 75768176 75768179
    0xf0f01060c050c100e0303270105070b0a0b0609100c05070f030507061d06040e10051c02151201030b220c0b090f0a060513080303040308041205162109 66
    0x160350329200343c2c8158500c0f4007002151642c2280c07103040c12160a14000701a0390b03403400a240c021744001c009000b0f4002c1010759000140c0c4541c000c0c0705840705507401221144607991503468100090001d0310b5200c1d8410018442804517031100c0c00d03140c90940c141c2e1942e585803c3c1c1d50a0245c6485142e90000b0350103101c1c2d0009000040011036120100c0e503240c1803005d107151003c074600d900e50b40400e25107a044100400d0000d44018a0f55800307004a4244a241915680350b00030700c60f01c1140c1122042000d82152240390042c24003011000c45010202100ca06003c01e00b101d01050f0030b001e07030041d140030381c00da403d12988124505055001400380d40340d203a808031041d030b107186160350340780304210b240394003c281e01c0c0180d190801c01000c1d9110081100711042e44500010b0200e810002840302040a00d00b000714225100100712030103a60580c0741e482c070300d03500da0303903100c481c0c040c002c000900300f100c04c0c482c1c003030b84081140280d114030b031040410340344092070b842010004603006014101000341d803840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 75770676 1250 75769426 75769433
    0x703020904060e0412050706060518041208090706050f04030b0f040201020d0503070215040206070b070306090b01051206100908030301060f0f180302010806120f030306041b050405010309020d0503030f0f01060c 92
    0x10f41045e2042d04080f525900b190410000500d61584a02d8010840701c10380b01030a400003d03c288283d00c82c42e40034100c0c41d0720010440c1c03042012030308400c040e80040e005121250184018000c03c2d031160004502d031a440c1c4c0e46216001e20180e03074214100a094081c0000c540c1c043c0030849122080d86409800c61415140082d940d45d07415950903101e880c03040c003003019500c030325049a4050741c129085511a04100d08024010500c80c030440024610300002c01500c0d6100310b0880c1e52801003131102400c40c2e100c900030001020035181d28a4140020481c00080d1000144041d5000308902c0d12420201984d00c3c90190507080c0010026007049103405290000304520340340401600e03020301e4a01c82507504c84020586141030034052402922030f04460810a4030004011031203414150f0b03061055104071008004c2d0074032040c40000100d0414041441954481d5201c0c2d03210754001046c895202c103480c0c503076030305540c42074605850080e0ba000030440315422602c9a10b004054514022205056945 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 75771926 1250 75770676 75770693
    0xe0705040f0c110d05041809050d0e0f01110a110a0816050a06030b090a0b0102030c030d050103150905120a0201090c06080402010801210303020306030705030708070303110d1b021302030703020904060e04 89
    0x6408401c000391f940d1500c000010b501a69005610508903070b403048416a0103801850142100c621070b03281ca0306c40d00d180394070400d10301c031050f01c00e00010a11107011b66120a064120724911a401031140c1c2d0001510260420545003c0b113441c030120070902c0e0914044c009800c007982c10000c2810f0800d4008516604e502e802560f014640c6a00098000ea0b60340040b41540f050089030001440702140c0e48070121050b0388064100d920a880e10041c0e1913051124030281c1d50b60300f0000c0e01d00c0d00800054a1036601103c0200f0200d106c5200000b0307010801c1d0740310f500d4450550070100001c0c4c449c108020465070010301403400f404405080d4541442003c1203240000e2613064010101500400030800380e0314204a1100035104c003c05175229030f5111f00f441ea5442c0c1c8181b100f507000507008040070080c1c1c3d40c04030751030081241503601c5d0030400010440400d030130248802c080341c100701d00c80f0f04a2072000407407010714040e021076500503a0b504e4188081005640b0ba9401220215a01c40c092100146185 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 75773176 1250 75771926 75771929
    0x8011401030f02041a09010f0f0e060306130311060a0506010305090a0507180b060d02071a040308070f110f06060111060603031605070308030a02090901090b10030e0705040f0c110d0504 81
    0x11540070800d000460700084802050703694098004181b040082201011a00590b066a41b408080103195a80c2e0254400d00e034016507581e80c0503080b032400303d00f180c0c0d80b10080000c3c803402810010500744501411a18201045400c1c641e1165590140100c80d1fa050081c981c1080e0b100e0010800c201464403216140e0195108400c0030714910b000e100685010340c1c205180460005041c1c40d218000074458502940c40a01d0407240c0d41a01d480015500101d00e0b6500e014075095660258a40e941c060250340c1040e1180145060045071040444c003000d041210489200310540640018104403001402280002e1162003c9400030f10405c4500c3d1030002c16034400b90a07401c1c552030420030034100f07207042c00215000a88520400030400014000d160010070501005665814050b81d0301c14007101180c00708480154440880880c04c41e045101c2d401140a4030600c00594904c5699200001c0c200c13110198098803044e01c07200b1110721150481e41413444884400c000d40810601480020070030b2049 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 75774426 1250 75773176 75773179
    0x70b030702010b030a05060106020105130b070807140d0c08070504030b0f040f0507030b06130c0c030e210a0605071b060c020313120c1401140d0905070f08011401030f02 74
    0x440010034840c400d4004107032810010f4141c4507604803a003415a12400c1c2402010302641c03c107004140030b01d02c09d204404040d44c00900201198803180340440310117201a01200400000004d030700c40e1035016000811000d41d103c140041d0841000001924440700107240c0020300805001c1000828500c3c2c1b0b02d0382e4003946940c2c1c2060325503030f58504100448541c0b0720282591095a2020003048010310032140540d804445031103040c41f082e410b40054400c640d170f1a000107600d00e10302c7c00001740918aa8017240c00000c103201c04040c80f00b003403500c00d031003045140d210302d91088414209100329407149640001d240d00c2c1ca105603056a400c0038074088541d0070000d000d9507071422011196442881980d29034080c00c5904031115036549401201184c0248082d181c030b2f05c480794001020b003c01d28600c11681d4068645d00000c4130b4071074122495401044c41185415220310b000000100184488000b900c0c1c0d4001c03020f41d1504100b84d081c210780c407003507400002050b140c00500124142c21400700481c1d60 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 75775676 1250 75774426 75774449
    0x5060c070512070305010615030b040c0509090a0b030d0201090614040f02062209060303030f15090b0303040305070602061602010c0c020405070e041a1302161101020f0f0102090f0303090307 83
    0x40e80c4119902c3d103e100d50000e01a07520380790000c2a1500f28050709069914559001d00c030001c1c402c0200001c4030341c40300b87c1300041034080260070395608010303020750f0340012440c3d40040c0150310364002c241848295802400180d5460541d075003003003001c3c821165030550200b082c400c1442d10382c0e01c0d00750303409110101a10817480071a0340400040304810040314041c180c0801c2d01d6007075a8102c800b01a15849c00114003280c103100146800b6020762003081115070100982c0c030a01c03032604021100a10400c500650180403c120210110b507003084244001d103520350040c020741c0390009000880440070440b42b011641420844410b55a00c076800e8104290112030004460725420010f03110501c070094603e8000d03007001800c0c000e0315000400780114000548101c1904418101114200e2040c6102030a00d4191910314a020035240b1048a10958060046030404896486403d00c1c113500840345010903900020350910b282008038480c60a002c05074011410b01c5290b20000b503d500041c0148a0f02c1c05 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 75776926 1250 75775676 75775699
    0x1709030406110a0f05070323061501030b030703050721030c0305090a09051302090106030b030715050405060304060506030709090803360303480d1103060a05060c0705 73
    0x102c14440c1086855020103c41c111001e580341481c0c40e0b41c418072094031f03100601e82038454022481558040b0907900d100140c4419034801200e079074000003000c20f4504050341e40301c40c001151803c114540c06940150000d0107210719002c00c151181d20303401060b8035444c0c10410140002078001ca4007545041d03060614640b00d4051b0307130101f5100300c0550304c1403c099051000f44404812a031080940c941d00a4032002456a21550b0036003e98103500c20329500344e0300038141001501103c86000e88a0329640ca0468500303a074440c0040d080350025181a100d46643e007040c048280307400c04c000c0006200c0f24100340844030980c2c48103e098000100405a20b0801c1440b20402d090040840025502025250300c0700003011041d0f56681e4100300e0f62290102c210101c101c5c1c40c4500203c81c040c9581d00242c05809150f02504c01424808038941d011095540610144815402500801000c6000396a000e501d034540041040108906d541c011741c0a1141000307402c0400c40b0100b550016107009440c40e40710072 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 75778176 1250 75776926 75776957
    0xb070b07170a0207050c0108090705150d0203010608090c1909090203010603080a0507020f09010333060b07120c20061b060609010f0503070303030f150303030b011709030406 76
    0x22003603408141d02100c11842001881145a409854034900a0701110b6076aa20200150b034802415111030742c003944186c004014510f01a80f091545010303a810340c9060290464960b0103a80003a013000d000b04a1180402c41030f10f0701004602c0d060001182d03820501d50031425008001421400b60780b45c403c1d100c42041c41951002d4010300c00a40d40420210381c0e800003000014025001071004078400c00410441000e50701d0180d076143c0c142d81d01b00c00d1042040e0442609030408604110401c516580c050200c824040c585200d028002c00440031701d00d5840c50107240100c50382c040000d0001c10320070501c421401007668090144058082841c801d00021400e80011300c442c020304162100034078030350b00740500748030000c49c50341c0c0a108261114140750343c85010000824519003d00ea8040c1d01c0307244100082442500181010319140d480010682e40c2500101000751031600f081d000b21352505030001542d64001ea80d0802801c0342c50446c0c0311070404c003030b1080c0c5174892031203080e0411040e0500c0c4d00cac0c0d8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 75779426 1250 75778176 75778187
    0x120807050c060405010209040609050103023015042d120e04050c0409050105010207080a030e0a0302120a050c0102030a090e0601090e010807140405132a030308011505040b070b07 78
    0xe80012080b0b408501d001d00e450b5002c3d40c0a03a80e02402941400e00004490b6606c0c02120306899004181d4040950f0b20030703840b0001d4070115006115507080440312000c82c0c20038090030206a0f03032840803900340d01d400d0400241418003c3c100080c2c0c103000311000300509035910340c01000c165110038807903012780c0344600c02c0f103011103140d1030154844d15103400d0040b00d41c0031000500c104c400b050070170311040e03036200c00590320742c1020310504545800491403400001e100c0c840c0072101800003803a036241c082d1a600801d8101d0001c941d212002e038440030400050203020441000a250244001d40c60f101840c44010030503a128442c40c1e040c82580030108299078080c0d042c0002401940c00c1c40815580d4484449a9414803807148900f010100d44903105c0505190188520810809004464492856460007042014592081c10100d100e107014034010f4485414000294020341da6001a5410300114800c2c40400f02ca01c01d0074400c0c04c220811002060170150740d2442d801564507600b03540d514805588 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 75780676 1250 75779426 75779437
    0x50c0a0f2003040b0c0c0f0a06180b0c01090b0a0b030a0602130e09072103050405060a02010906110d0e060709150c0501020a091d010f051212031e0c040312080705 71
    0x10140800300c1c001c1194107400c4081d0540e06a405d0440c0c2401403104107000104905d03411250300141160024001180680d030303020113521000a07000d60300ba0b80c403640740d400c0c1d4001540d4405165181c009442c14803100b0250103411029401d0104030000103040066174440402c0c0c0e008200d0780d000328861646044062014000305284250465240390000016444d407449000b642d000b42c0741150702001c50300c136408080030907581c1511920302e4682407104028041d0010340034a003c640d280c6010100254545c0952901c000c64025071a455807880e02d014001d54203861311034203d65200104100603103a1120449045507140d1b090100340312007000007215902409270010f001580000b81400445034403c0e00003049a03540405007482031024081c0c0200c00302c00f03101d9620890704000707092009180081d400443c11030180d04840046c4040341d050640390308100d0345900341c0c4000101c085c0284089034840c1c3d0340490700d80c000900c2c2c1802c60707a40c03a101c591881880000c01450a000403000340c0143c04451 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 75781926 1250 75780676 75780737
    0x90201020f0111040614040f03150b03010c03150e090c06031e010305100e03090121061e0f050306071d0a03021906020f0c091b0f040e070201050c0a0f 66
    0xb54402118640503613000c3d00c0b80000241045101070141c0c041c01090b1000d44020760700c10101c542c03464031100f05010001d180d0607401e0750741e817100303034050740d4248111504617280c0d880109100d9034001c54040e01d900c0a43c082810034030b030340c0d080007540c00c40451441c3c0c02d8841140c00c1c50320fa48512080314440052195104070320286080080300740400003400c11840d01d10842e0900504400c211410b440e8081d51488c94003142d508040078200400094048014102c140340000b10b041c5d039601c998804041c0d000310300d9485a85450305100828041100501825060340140201d061060b03000703044003400004403040d0101703040d0480d10380d507505596400644d00140f14041c0042034080c4601d481d0420301c221009031040c0504d003a400d0070046940c50f0baa6600610444255948132481e2170701560340346048070a16800c11000710829268009003000d00315184010545180401003c0e0840e07001038540d015200050001001c9a0b80c48114154414524500714200300c403454400134000f8090030313828 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 75783176 1250 75781926 75781931
    0xb010e06030105060a03050a0221031c050901050403080406020901020309060a020303070806030d050406080603030403050a0302101503121b06060815063309030d080106031b090504090201020f01 85
    0x9000444100014054001207000700240d8640790100040d50200303202c001c02d036400007d641d0015180010520300d081c6110440d0042c0c282c01d05d016181181d0041d52040c840c42001d03512142090424403035141d0040b4403c0c020402414161000b03040804000c0c0024030031a00080c80210b240d01c284140c1e4019000036085c0c60f15905280d2000e0744a40041b5941400106241d0006079035240026041c0ca401501d500e6141c6081c0c2015011903801900a140c41d42621003000700100103002000a4101e2601a40c0a00380041515209009681c075400020b82968003800040c000304c0c2d645200c04008440354103154248031080200080c81c006100c0e8040d040a240c080c00280321a00424200d55461111202114607a41da03c20015195404202c1c075940c8440e42d00744030218000c8030300c0900884103040c0098104140640001d01c0c01c0f180c4a030b010002843c4200400c44903416002e40c13041400d01d000340d02d586810000d8000c007100c1c41889611310444d2a040b200041d03900a000705039903070303514070002d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 75784426 1250 75783176 75783179
    0x30d0c05120f0313060618091407030839010606120b1309031b05030309010c03020711010c030504030803040303060509071d09060f03010908090907020307050703111305090a0314041d0a06030b01 85
    0x1040000c000d10034050b142e40031b4042c01032594140218640040da94420033180c10705075450400e480700c64224860404054152406241032004586420000078400d000450042d0070300d04000d00c21010010101200350400350441501c0c9d503201044d4008180308440090300c0001400c003140d0140241c8840c100d042110340d441c01c00e0cc540400118070440c2c081000703010002100b1000c400700e2059282c00391100030040c141007415071040848404071802880d0503070070161213032201910755000356011404a5030714807003080316040c660300c0b00768051107a04044000030001600481105041c003c128412403040c030008101e035880d80441c22210102030003c2240d5040c9240030b2029920109244c1c0c030030038180e8006a8620307c000101d8040300d0703010780602180c0d807450b90b42c100c41810440c10076900450f01c140d070301d111801d82d101b13140c42481180010000b54010741405408ac2841740c00b0002581c4d000c00007880003500c1d1a48103010059060340d082c4481d030b100e401c1500201030781d400c020038041a0900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 75785676 1250 75784426 75784469
    0x102060106350702210f030f04050109120509010807050406120c0315030311250e130206070b0f101a090a0914010603060b030411040209010e030d0c05120f03130606 72
    0x106802c2e1981c410f00d00180340340c0602c2c01c41c0b403d401b652011210782c000c1003002030040b480c02d21000390003a200b0700c000f01d081c2a1540d1020948155001800001a40424018825030740208410341188503424403d01c1c0c9420858001c0c44180b2034583e00c0707074458940136030000c803510030303400116101d2802450013000c40c4c403890b0080030900207924500d600d00c540c0040150403104d84085029000c0c400c0b0060030103e103030000c08410042c0040200806000c12594000961500c034000c09800c0d1040c00001c0742072400403c0400d400c0000f5054841e06041203105008000f400e58007940b24903a40440180c440c26603900003000c0c003d041d0040a03049087c40c5158a184140e42c448078145d400d151001c0c01070503122140148140001c40300545440c509404080c00341c00c05600134241b120040c035011180545074400f10780b41c1003c0c9038a04002400e607040a200344541441201c07140b5060b0891f0364681000c0b0024141c440c0000f07442c80d0100c01c00030b940300d020000150b200f14010550032036071a04030440d040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 75786926 1250 75785676 75785683
    0x4200408070603060905060315040303020d02030f0403110109050d0c0219030501060f060203070203030a0e040902091006180302091b071b030c060c0b070815120a020307050102060106350702 83
    0x702d000d0100b0305040001c50721518901600b44100000740040c035020b020483c0c156003118001c1d109806150f8204488901d200090004600c96004116507140c0da0a20740b40090100f48200a0101d03540d251986040010340c000c90008142c4580e4601410006024000201c8421911207001403030864050300104020040d04007200300c8486417041207080e80d6030f50341a42c8a11800900139815041003151a0017140142c0c2c3d2099040340181c000600c0390610341c04151a05e00903500701409442050040040700c2d8051119200740b00d2002d520b140c20313480d44c2c0c04104902d4028000382e5002c11002d01d64009032034604180c610300c0c0e030042d0007030781a00a46000079070202c16602094400508417400800e44600a150426070b0030740c401e58203a03041d5a00401221380040180c0b00a010100406072500690b50705203171541400004000343c13541c0c03c0c00303204040ca000c1065222605541110004010f05a00f00303880401440c0e20300c5845a00d200503070042c0a44c014490100030180680f1020300c07616a5000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 75788176 1250 75786926 75786929
    0x10504020405100305100f09061a0a090908030406020904022101030b1b091504050303070303020d15050102100b03010212010602031309060b09010c1b030b150109030807020420040807 80
    0x3900d0412594072548240c400304034584c00f000d07105600252401d138001c41c2683c404040d00c10039120004866549030384200036140a110401840c0302ea5a14071001403501688100041518075005c0080000079610039115010051002d81000c1d0b02203205500e0361520340443e590040c60140780d51111403440c0102d000d0319028001650441c804100103041101c041b01091003500d480d00a1500b48205e50081015a850016840b020700c0418000040c1c2503c040010f4640544240c501607180c5001070b0500b41251407200022480e4110280c00300442d98002c1182c046002082c00040360512070100464068454490328051002c8400000200f0981c04000b800c1000003140b501004255103170840c0c42503d03ea0b01030040700705420011100750f50301450003c1d200074032440c81001066011103000002c5000c0e54000d540648407602040581c000120f00000b0254003400c080550703a0a42c1c07a03410b554061100c00034011507031503860100034068012414001246d00c21016074170b075100c0c075501d92505131a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 75789426 1250 75788176 75788179
    0xd08040308041508010608060105160309030c08010c0206090109020a030f060204030c0303030203060306060306060a0b0717030705070201090f030b040f020f0301091b0e2203050c100209090108010513080906091201050402 96
    0x882c0007046d80c40c07140201c180103d07016982c0c5800d00e140c031840d41c4802145080c08605210318040c00200003601107105000821050000080525a48002a0130454020042034141c1d140159000041e9a510004410f0b84d41000400302c8000ca81c2c0740100081c41590030180c0b0307500301e0380800400c15034142c00852148409606a452540714282403559440007550b00700da21000c2e5401c02c0c003803403030f542c0060403c16008054501c090f41d03901c1c0340070302554800e8601000207100000c0a80955070480420b90040c01d1112180c0440c6103035444072441004040c00040060309440e07400350941d500d94501244281c030090003088111060320300494454044c11000f4000700d84000001020b40424a401d0311400000d240192020450912200484078460b400c40130f026041c001d1aa1102041100802a0110150059450190b5010820302c02e605038044020781c1c0c1864204000c001c080a04103e0305980426140e40b102d08480000303031140100300c3e090390404c1d5640220a0001ca05400080c003c032300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 75790676 1250 75789426 75789437
    0x305090a0b12070e0105120408180d0c03050c01020f030405130209060309060f10030201020c12070f030503070303060b04080a0204090606080114150405060306040b07090b030a05070806120c0d080403080415 90
    0x1100001906d04e40200040003a000703410030300250100f00f03008024403400024406000b202180d0200164804406c1070742513500c0c21200e04288200b103800c0100c1a18454240000c2c0083c42040682580d0f80c0304500a860080008025540740c04000750140c500058000b042d140e1240307401180300d5a00c0c9021245407280c1d88444000c1001c221080580d18140c94040e0301500c40500501d050141344111001ca40605105040c0c00241000310442c402c00918820700c0555030310002410000e003511007030b4114400e00300c030800041003e01ca0004440c01c0140c0d0544020503105903504243c00141950b07800305040b5401c105030501300c03c10141c201e45c4142d42e118106041e58114205200841d0400c0f20500c2c0c0541c003460200740828240f02c2140d81c072030300c9883c0140d80709448041714400d542080d16a03c3d040385c0c8031030610081503084607940d079000505031880d100c0c008205107529543d14110030510700807090405604e09204200080382c000c1c5401c81035050740c0d5503070360323881c8043c071103a12510000045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 75791926 1250 75790676 75790697
    0x3090706030c0f050315030604080a020d08070e280602010920010806240703030915090302101d0303010305071503051302060903010f052e120305090a0b1207 69
    0x14024070800e81850450307668042018490f69081d140c0c0d9101900b040729039101c240c0c44004075981000030b03030301c81c0380310b2040e1070f8440900b00e10191600000c0042c4005001501082100395135001b6041289648110768480000d00b007903581d13151100002d20a0030a00039a11004116990150802003215201e588036160f48903420101c9888003e00e0003490780000d0103400401c58030b1424141e04ca0b001510322140c0c18400e148040d4400341640180340450100e910780504000307002503483c610098440148050240314802c4d03400030340f0740460b0300346405441d9072002000d00071650144903e07488010325040700d42c1c17561241812030355098207218a000440254850190940c03107801107034026808003980000201042d401c00c11140c1080754002d405658520108101200b5030141e14041e0a01c190340e00b10309103102007100d0031442c00c8410801c403044010010080c0c2400040c94100071901880c0c25519000c607240051401d12040c0c1c03010100b044c010aa60b10030700c401c03804203400360b845074548a9920 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 75793176 1250 75791926 75791939
    0x2010c1103120a090804090f0c03050c09030706080907350f070b3004050106080d020a0221060106271202090423011a150301060c0507050a060203030907 67
    0x34403940900b0141602d003440802c41c2c00c200741d0412601548640802810981c4950ba4801100c6100682d90403942c0c907141c000900f0781e018800d6540102e90a03035414500b140710404a40c3da0b0100d03115500400c203541c0001100a5020320210011345024801b00074406480720503400495030507941c4040040ca40b49518090407400100b110491007c10050308040b441d0a150201a030042d07050845d222850b40c40c40130040004000f0440440d1400f5001591404c1904009003160040d81140301654400509105401d400164001440e54119851008550700b009215140b06d02c00c80500450302c03d030400401e0032500441111288861005946802e00d007a40c1c44a40002052203440105d0892101c6000076003001e40c00107500a00403010102040b14038952610344080c0d8488154450359181c4814060b06800803102120040888110b002c1f006000d07944030080c40184240e40901440350600420410b06200d04001020004c2071103201a98610000e911303940202c0b100c42c40b40c02106404581d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 75794426 1250 75793176 75793183
    0xb0306040f02031b09012a051b030c09040c030503040602030705010b0a0302060406180b1902010608030a0e060315031005040204051006020615030f0f03042303100506010309050a0302010c11 83
    0x3e41c0000542282134607101e2007003003055000ea40a00d04022003424140b82d042c400f696450708510400703401c50800f2000c0d080041c20020640100702400d2044c841592055600044940c1d40106c00c4500154030b44482c6002505018030754402080d40c000480e00183d05a00800070340400e5000c1c20007405604a0740b0b08021034044c0c2c40c04000e500c01000e00081c49100d02c02c5100140300419030072000b14150315410000242d4000c1903c0c908034000103851503071078135820300521006220560046080c02283c4001412000704021414011400880000c1c041d600c5200074400359440039081d607454110356860003014100031a0141d0140e03041c1400305d03a402e03458408034000c4900c00d81c00b03071240ea22140f1130004003400b9808941e0b807501c202d641030a44181e040c80409640149d85005540d0b4902d04401c209402a64203004455942c41c1910200e1607100890107400c40d01680d84005043e544210060300100b0b24164040d1403485881c1c0c0c40d000b01901580002602521510303020070f095045810b0669 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 75795676 1250 75794426 75794431
    0x130501060507060b031603080d0e030408030d09080d150e07080402031e010b0901230109030c150c0b10051311070209060d02090a0605090112050316020a09060b0306040f0203 76
    0x540411450010828644c0030301c9049400074141d603070070b030381100003140e42c062150815503241c01e0004d100c810002c4948280710040d002d0302e01940c2820300e46100591a401180510341c6002d03181c0920000b00880202180d00440303651204006190808078030704031014860158013102560203010550550282003110310540d070043c0144060303100c207400404c03003403400100c0550540d20361001203680c1d034403900102c4c00390a0b134900040149901a08100031910b4498140d41403000141003400440d602d581101c00355140320350101c8640d000700c0003c0f1880541340c1e002520120140c028440c17400c1603420214103c4800300e900b0382c2e16450b003c1450302115401c07842005040c4d02080041c0040c00c202880c0c0c0e601c00c00040140e10440346a8020900040d02100c03e000e02c2c0e0342e505014071052500a003c1805400b184100c0402d0003555a02d032580c034840c000404401001515070081199541c42d02400138210340b09060000a07516054401c0542003555074a104038102142e0b03280c080f60342d00c00c1c3ca2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 75796926 1250 75795676 75795689
    0x2d0c03060b0307030b0a090c080f0a090b0c0f0906070305090a050301020f220302060a08010f0e060919090519052a090405010b04051311010c15020912060a050105130501 74
    0x1442e40d00c03031000950051009510468004410050000c2c5034183c0348a000030550b0540c03604201840d04072614a24080014200042c042c0b804286402003014100b10583c0110404802541c58520b0b032501e03500e40c0614a62180c3c058000a078103020980d01074003411010303000340c5d0740780002912041050700340e01440c2c1c00f4481c000c105004426008147c840030031b110828250103128103d450341c0210341c07a035001c0140c12000c44c01c000c00400001d40b036200325000400d54000c03d040079041c4103002075203104000e021051020318000c0f0803010003120350302902e01c0503441000c607040c01c0501d1034100b00007442d41e003041d01e46000c0c890035224010340c0c80c007c081c11040040801d8483c0c85601d01000031406002c0c1c015580c0750758030350149620340c45510841e4061850301f110440d4050350f41c0341030841d01241c00704c85810000015582c50000758000b0718100120302c07141000d6150900c80300030654103640302c008458140714000c1808104000c40c1e006034140c81096403401d0728055a03040c0c034400d48000303100e80c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 75798176 1250 75796926 75796949
    0x902191508190b010903060507030e070f05030a150b09011e0f0b0f07030c0609081804020a300203040b01090e0a0b04060203060109052d0301090201081303032d0c0306 73
    0x15200b1418581c01031189000c141892030320030f0340700d8903a20121141101c407000401e03501c4080350300601040016000424040300700070301190411000c03a840303140c198801080c0c00714030307240402081600e4100c0206103001803c1e03080709607924400d8000e04003806c0c1c0e0000b407411501e0400300301040440c110030300750f50309030b078030a407422000048050841d48101e9042e41008003070550400040d00c02d0080018650040380005d8840400e905981008095204898460762040203e200c8141c1c22180c4140000340d210f0360500010030307914011150703421620800162902c00010401002807049010f81626075500d410408449070070310440d591035000f030002d090500c1c0070780040d0010703103150001c1d54050010301d04542e1a59640021410500e07074101c00c020703080996540e207801c40202c20784440122a00302e0081c0001d5180382c0005c0d1524901420f1109032003440b840c0c160505005c0c2e000500d9080e1010700440e90f0380d0300258220385549401c60101c080320300f4401607400561090159509495a13407041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 75799426 1250 75798176 75798211
    0x3060112170403050706080c0909130519080c06101d1015030c0305060114122d1005010c110120010501060507110d0507030b0702010902191508 63
    0x80c1609009000c10407101011661440c4501c84044000340c001188910001c000d0b050424034050050b510042c840c0d10385840c14800780c41e00b03503a150700031508403150b0025007181c5121410a1410003118080310350594001d81c43c600204144240103098070600d0700c1c00e8901d5903c40540c860a4140e40f0300c40c2246603184825160f0342c1c0850b0410740c030b400417194440020300f20358480ca01c8400b2108603000001003603030b8800d50045260107009403940160b00746450349a842690078a42e107580505514020300b0748200c0d002990010380d203000d00000c52108540460341d00c9105030700c100590000c0300c52078030810741090001115402401f008840c01d500012001c010ba5203400119140b6000481010220b4585004148203070002e214490180c01669545542c812080c1407107002a84040102e60040148802250201c3d0b804124142030700d50103c2d40c00c0c00da851741c20080380507128258004e9070103600c1f44404007140d00b101a4034003c4410144240b20050880134040e160b5540803140e111085084812 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 75800676 1250 75799426 75799439
    0x9010606021c09210302060601020f10110d0207210806030c04050c07060603080406030b061e03060109150206040b0601081003020f01050c01150302210c1908010903030c09050f030601 80
    0x80d4501c120b5040c548507030210381e00c0301207500900e04145000950314482046409166060010360391210013030005005074402c18200998400c100030812780c0507541d40305244598540b010444a803110209015501c8010b40d003880b18100c0c0d45035400c0420b8186910600802d10b00882c0d45901c144801000740501d000024184000340c07034002d1000301d65020400a550000e03555208100183d0300170030301283c5581c107140e005001c480021000d6403003400103008540600f02d0044c0b8038400d04103500343d8182ca03a103800005840b2981207800108034010000c440c8452903a00180d00740c40b03640650b2645915859000054070302040c00d407048051095071410600240c201400000800a4180342c0107141141c044161400c440ca400b024a00ba00781541d42003040d45400500c1502c0e940040c014507004d0011010b425541e10303030302e80c2e0080c0a8a41c1c410764044004805805030f00a107260030082c000e07031f100352400400404503140f440002c50f0800d013006c1042d0800240c40100140050f00030b00300c40e4200036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 75801926 1250 75800676 75800713
    0x20a0809090601090e100503010605180a0f0e15090d0305061e130221090303010b0d050c04150e0a08071a1b070f030303060b0f0304030e0a030606120204050901060602 73
    0x422a43c148250721200040f021660348401c1e104409429203c2c00c21030500d8100b5080d1007142c2e200900c40d015910a03912000007002001d0f0700800c42c1800024400e84042d0201c2c003800c12156881020300405401e005200c05070305025116145a178159444440409030903811103905807001c2ea08801c905000b41e06800310510706900c2003000500c28801007031120150001d07a40104c62201111901060742254205040156a08065214081c0d4115030407d0621103050182084074815a51a10301140710000803108440181282c28040c0040102014000e0701691101001c1c60081d20910000108808007182003400d0701c6514000b07a2202561401c6d0000580155951018074078003e45000300060003042040018a50707080c031451051300e5810007600701d9140c2e60021081c01c6041182d80260441442142e500540c1030034220410070704100490038842c0c6582000304207928002c0081440e031032401d0707401f40d283c1c400c43c0c06025a99800c04070900b030752054420301016030312440400664050300c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 75803176 1250 75801926 75801931
    0x1030f030c05011d0a050114040f031d030319080610080606130902040303020a05060a091101050f0705060c091002030708040308031902070b0403030b0d0c0e0712020304060204080607020a080909 85
    0x25000452202020a0320113081440010420740075844510b421080180c03e00441c000680d24030040c49079071038241c981c074003031412408000b02084220340540780880306c0724500c510080c101900f10303a19411641040500c043c1c204900340081900704000548038035140034041e0142d45150342e0307903000781c4410080c0403140e002994280d2501f1200c0d0b1001c2035510b40b61000e40f000354029801411440803074140281400c4000d8004407078641040c7e20100400d04684030426002c40030310f411690b42c0600c402c0c28030140a8100001c015004020502c10307220144d0003d040b02c9041180c0c0c41d0300e244908402130360349118500e001403003100d0a01c400c00104141c40c0c0a0740d40412020040321409050541d0501288d1050304201d07503078080c590030b100c181036143c4200100344130181c170284024241502c49a203c0c011500c40c0500c402e1010001540c030501c161401a20030f11510401d5440c2d0416142190283d08640541c030300c648250070000e05600c2c0300089885c0da07250000031072454040040240545180e00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 75804426 1250 75803176 75803183
    0x17030703020f070b0105040c050301030816020f0402030a1b0201270503071401021201090603150504110a0303050417070509070c0606050a060c1109060618041b050301090f0501030f030c 81
    0x203101888420b1000401001c41d2841a0750304450341d030401c030030007007115200712206013000b0081c801440083c2200080301e983c0b00101800004044092002501c04041ca0207942d80050010060188200082e0040c206500c88901018044141c81c10103d00303d42c00e9580c00810510703d00007554214081c0c110031111907004400b52841c2410b0360b00e90500d945220400c042a40c1e60014481d0816003038609a14090180c007481407007500d01c0c5481741c1c540d00c00c2e510481442203654101150400503821026240424080d1208030081c2e9a410042e100303400c00c1c400c0322081080084034100000c0c02207244c1c425111700403c2030784142c480c913a040320100c4110307038111595652204003040315a6004480320003403d065550304221045480c0140000201d507110a00880c000340a110007a0344940a03039000450746403410210741c0750440001e0103003070b40d05082107211100070404c244072a4004001c40c1030703845130071042c0f06030807410399000b00301d40d82488003802000100007a240024401c0c10007081e141e01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 75805676 1250 75804426 75804431
    0x11030a050319080105010905010c02040f0e010c0e0f06040302090f0703230a0f06030507050f03070506040b070b0708010303021c1806090501020c06040b0301051207090e030409050108060417030703 86
    0x210340d00d09203107601403041440c0c003401e00c968222955502808960140c1000e03c0d02c00900d51510740060105618808000e2081d07889008000607007a03542e07c00907000022800a004c017809a0002825032001350b8009400f604070512210400d041c4102110704403a0301030040321040c2e44d07510071290001ca0190041e020175032126001c0c0003220750044014110010701c83c56100a040c256041001c4a613030501000240e4213020b010001300394045003202c204c40c01034501020b00d0f9058400603042c400a40c00c200d600481c08100070820380d01220203001e03094801e1404540f543c60729001903a00150034403000700141d0000c02e070040d0b00c010303014400b01078a09500380145074401c02000f81c00040c41c2c540103000002d03101c2c80200401e45c1d04000440d203401007599030b80d107010304102c04030102d84414021030b4091303001c0c2028210440300400c441c00c0109880c140070002a24908809a02d0780e200d4070a8041c100d092000128050b280411214040c95201d43c140400c15460061401145c00c0200030406256 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 75806926 1250 75805676 75805693
    0x80406050c0a060f050609010512120c10020301030503090111030c07150c0203061e1f050f030c0d0b090105240108041b0602010e0f030f0d021303060212090d14071103 73
    0xb040f134000c40c03031390b4000300750007150a01e42203050041140b8160320291045401400c2030003515404106c3e02859900d90300c0701c40d030b2100c41880c07607841e250181c2840501180b0000000080c020701002800c4402d603340d07070b0080100e074136888403a503900481a405219400c15282008514020f10302d81c0e107035078000d04040500b81040c2c0c00280c10a04101e407212840022507402d0941c490000030500d902424101e250142c141c0d0700480260900124050b0030300596040344c00c0880c40e0b0303007000301400700400145141180305040c5460200018140c401b1b610320342c280000302c1c4060002d4000b140340711000c0740710298510706407001110403402c054800c0d40c401010440c0c01007103120b002c042101601030f51b0000b044040d03100c040b2901d484d6071a45401d83d180c106208460400070350070119858452400070250b1101c402d00c4d00c0e401104090b52008041c03610018080c5540302180c0c0041d0b1140408000341d445a0800080a4a45111250344011182c0f03080090b030000407401285a030320500003804075030445 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 75808176 1250 75806926 75806933
    0x30d0507030b0a0e0601020c120d0507050f0613060e0a02090a0f060801060b0a02160b03010e0c09030a03090303030e12190302091003060f06090501021c020118030f120504080406050c0a 81
    0x3d03005a000f50980924004c02c0000a5804010240e004002521000301484c2c503140c00c00d40b6480210300c074404100c8001160030030b00608014000307018510f030003510304034241000003240032645484122542400c1c00281815007030045040820503401030300300703907a41e0380360500301c070003410209840f031a01170742c030680411444024410340d0050180c802007150355040c2170301c02900e001c90307240c44030404448004060026001030402e41e030441d914281c0d8031211761549001403025005960b0810f41500c1110003001c10300d68451000e0044a0107602c0400c02c0389507040101d51202d42207141d2904200d41000074004019158415900d05c5560b46001420b020b09580000c084100441030500060b403a16003d020380503d46c80c0c148020002404c01c61074403481d000c0081e440d0b00508844010b9815034141121a8038001c0d0040900d0346a540240341301800e1a290151601c0e001d5900c0c0740005071500e016004110f072510444e030142d81c00c1207800d4202840c02d041100c3e20341c0803030540c02c003a0140c1d95071000003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 75809426 1250 75808176 75808189
    0x81504020d0903020c040f0908040510050c012c0105100b0c0102040506070f02100f021207020a0308030a0e0609160b0705070e0103050102031608060904170408030a0503160c0203030d0507030b 84
    0x41c0d07803080c0c0c00340a80c06000401c06c01034541481c1080806803820714600300080e9840129402c454041c2c528407a4110600170a9405008070310588031294208210305142d12540100000b442a4520079120030342081840075088540496414040280c150802e210030081700001d40702c2c840520300003514050b1100007043c0725420100c0c0488918820011000071460004545445103100d46004410340f1900040259101519805950140c00006540042d07403220b44c035240245400c9040e2959906000701d98000030511103100b90201d010741030110755664000b090349904030a08a24100801c0d040207510300b10342d4850102100d05100305000018189007a101e02802503000f08001601d078500083d64000c4195056801e00401c1105402c0101c207070380d07030601c05402c1398001c00c0711400c0d40d40820040d60148265002107095210101d1214034141e40403008620038400e0400c2c1b8051901c0c000c0c020344030b602c0000300080d07040d04103001d450304002c8150302039030348000c943c03402252140500010441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 75810676 1250 75809426 75809441
    0x3230408060103020a05090709030305030615040311040506030607050a080a0213060906020c0f0a03080304150e0a0314040b040b0f091009030303140115031d010e011416081504020d 79
    0x450350010750040095140c1070302c40f1401003506403a006403500d00031a008007000c0d21400010140300c000b00c081903454860200c0c9000340710101004a991315144e05160461403420031000d271083e0b040c0300000d20f41d401c0115a041c05810a9200c9a041030103510083d180464010300c860350700e503420b0010000150141d28010f00410054030390101d454108040207007044104e01006008500710312034401d441d224220700c0710460b5000418a9100d480b81c2c6000c5ea03840c520702c40e512002034200900f11050346c0002c51940a110b100b91500c003000c0c400c403d80120303075000e18411740d00d0311035080c0300402c44240340038000d1042c00764030210645001c040200240301c0465062076030000a49040c01032040542600c103420024044048281c11589468081d0b041c81542c400d0f075204040d02d030304010141c66100e0010941c0840000000d00400003450107843c020304034002a440c8102c0c0c40c401251900c0a180c003010220040c90b602c1e80380503a2482544002a0030012040b038220794200021001c00e55035200300070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 75811926 1250 75810676 75810689
    0xc05070e09120301060e01120b03070b0c070801050408030402041508060a060311060304150e0a06020d020307091505040509040c08030307080610090b0d050c0c120c16080a032304 78
    0x450305180d040c003890700c0310107200b52220301010401800519000340448849075024038200c803001d0400701c14840500b00c08001543c25118401303020850004d080003904118604004884886035901c5841e4243c9900b60b41c00350200c94200089800750900d0f810040c030701164808900304865075400b8040c42d01000b255021083c8c0d9480f14103104205980c1440c00d0010000c1b503c541c15410300d40c0344c910750301d0095208400300517a14030b4409240103051014450b1242c21180c110346a420074032200029600c200c4003140060014000030600c80d00d0b41d00d560307a801500c2c0e520f06060504100500c180d407500a4000c2ea00250254000210b41400b0030042d4072071321066036248240c0c1010001d105500944910005c103210482ea02800601c4500003551040c55500c039004c51940c81d40c0d10740c4009442054000b00080c003420b00c800d8100c0c40750354000c114903d104412541703420030070700d400c0350701c02c0706809143e10031382280c64110086886410b10880010300c1c643e414445001854034116954015440318 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 75813176 1250 75811926 75811949
    0xc0c060213180c0e0405010501120e01060b0a110705180a0203100b07060902030c12100b040617030c10150b030415020a02070815090706080a0906050a09210509100c0507 74
    0x221503e540045080300700b600170741d82405154104070000e442d2030407640d445010140d40310030b100c001c004250803600040a6038000e1a03a9890034000042c07440018104600031031056020000c0c0c5070070452001803c401c03030a1000103584c0c82d010650b8010307500203803aa07142d8010017800800c82d00062030040c45001c0c400c0d0320018200803140705041c01c3c0007410a695101700c0504551000c0c4001c0890842d0101407403000002e4907842c0a00005c000700156000902006110301c040300074014004001d06540040d841216010003d6980c444250b99441240c842081c0b103081003040494151009076401c40c0c4180c100b021042081305458040f138028070348240060b8040700e0f080151401c1488540c840e840d43c6840710300305281110083c1e40c0c880d400e10519042010035000200b404001e0b41c03104040ea0361001c001e2107603040907401d0001038545000140c6002c0b80b020541803055840b07162900405516131246d41c1080d10000401652080c00307400300301030203c20080600000c0c1c0c01d00075280034000c1d113440c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 75814426 1250 75813176 75813191
    0x1a04081e0129040f3b03040303031d030307120509030d24060203090d020906120a05060604060503030901080601051c020c070305010b10090308070c030501140105040b040c0c06021318 80
    0x10001a54030000f144000b051406160884140020b0a174240890315800280d4004940f0310034103c600c001d00f0325000d818000480c3c08420580e050b003180c02600740016a0741e0044002c850002c0d180c1c4810380e401c90104a8407030345141003803919085a98410010000d490800d003c4031041c100b500c5000c25034400c5000f0f808a6000020032500f00080542075030310003035003840790060110720806412040603101d404c2000010743e150303a410303440b80800030a041c291600d51070149402982c80c0030986030706101d50304200f00481e10342400000c1e100001c005941e0b451840c0c4036000103488a9000442c600300396030301d0a5030240700d551280020513003200c1e280020080ba9103507003449802c540b07070720191900c2100e40300c19450045900c00e1100068070340081107103030b4410300da10f00107189042942c8020451750801310f401c5024081c0f00c2045040f10801c0d20b040c02500c000d2010041140e00f60515240858980302284012841d940d0280c0040d000c80626404413036100d503000840945120004240381c0e860710301 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 75815676 1250 75814426 75814429
    0x1124160309051e09100315020304021c1202011a1f02010b030f030d0605090606191704061a030102030c041e0b0c0d1209020609010c030c17041a04081e0129 68
    0x26170b80b2014000d50401e0311415991000080d010004288031401d0300400801c00395a24014051781522100040f08501580c514100340718002414000025510744580743d40c445d1a00b4140c5510100300400d500c1c5550000028843c4003007a1540d50000c6642c0e580441030316884c00c004081c0310324808401181c13036199460054050301e0041e00b01c01c1c0620941c10a01501c2e84401081e189a015070030112200a8150407085034002c2c40c0406044100000384140018850107510817140c0445006c00c5a035100c040000349800d174802501c0b0642c14501c2088100403000b00c103001507004140c4608054881d5903035030100c03400c51308801c64000c4a5000152540c103090340080f90b0600c0300415101c2444420030a4000900c4c0b401500b00703080c103000c0010f0b01401054481d041040e4032030b5000d0300c04140c00202c045800704541190107072981604450400385004901c41040d1412201124000d003118980c80a12120031004040744503c290341b17810908600030030001c180e980100f1050020369050385100b0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 75816926 1250 75815676 75815689
    0x9060605060403170c101d06060d03080a092405010503060108010c05030103030e01030f05070807020d02070302030a0f0302031c02091c030e15070b041124160309051e 73
    0x340803610501c010031003000020810100c41c0d2607828502403494030383c074500344414200305441070400011880d0039481058030080c400a9451403c130181103821a036194018000b40d03c0e85e042000c2d000c5100c0000041e40f6600300e411405c0307114400e904a007950640c038455800c0484451781c3c110340c0b107a2503500600c458201042818018401980240a40d4100a0000d40648018080981040b4040503182c07240d9010780c200c4140066001c2c0c1c100201e24041d0002031030210300b5030342100140500d01c445400e9074800900e180c03e813500100136198061060341d40c00b204090108080382580800c1c0510706242009000e4514200661900560307034401102c01c02c07051503d08085019240c035641c4504010a520400300c0102c0601130307420708490860b0700703d07031580390142d00002404155001c040000300240002c03110718081b0300340c035001c0b0640d49000c901c01e02c83d000d180040c09042c0e0709000104c0c0490300004261001402810141d40550319440452100c0001f43c0188000c4003061b0511062428030f04d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 75818176 1250 75816926 75816929
    0x5060a0b0312070803070c291530030a09030201020c04020f03130c1802041e0302010c060b042910020613060e1903080a05060301050f070513050a09090606 68
    0x8402900c0a1512104404100e025488010700391000100000d10790501640104005541000c140c44900c55022458840006c0207610818005001030101e100d8094800b903000712504010070400c24400e4201c424200030b0254070204101c818ac00b400030039898030910042030b5502442e81da190f242415030001a1802607a201d07000d000e103204016182401c1500015282c10002000002000c0d0544d82002c090908031030b00461800200c4501d03900c403070080b0394018001c803002c004914220580040f0007100c001c81c5440041e000c04d17003040b150400a40d45600501c1d0002c00140002136548044d04d40880c02c181954505403010020745034420035151903480b031000110b50788024a002d2500031009506e0040c00400108240d80b6444540c560b15000d00000c01e401075103c01154002c401410001d00520f0113843e01e40540b443c00000c55218101800344a1113a10303008590841030311200380c00c40300c550001007554602e01c0d00c03d2000c9259a2064108401800c00c0c2c400800c282c0882d00300481150b005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 75819426 1250 75818176 75818179
    0x405030f0c100c1704030f1106091609020a082d040308040318051f03020c010c050a1b0503070f0203010902130b01031409060402060a050415020a060c08270c0402030405060a0b 77
    0xb8000d800600300e020003504d58000d6041c40c00c1c9003000d610f00c60030307078000100c02111036290144a04200e109000042e034608502d003d0442d81300d003140e5480c01c48089220703030440700001800b608d001a22103c0100311100841e060740151018070040e014002d6035007502901c0840010301c0704024001072640c0100f20020f1a10141e00c800700c03123403900b4001585000400144103100c100304000c1d41a95001c0d506407020001c03050300911441c0c0c3e00110051046c0d1044035510701140700324450f03840358009403102a4525502800641c540038950f11258068858080200d90640d25040f41000603218000d60034481e848088021078135101c101d0014040c3c8a044521001c0d42031100c003003203048807001030016009501034403200e543d40c250513800c542d00c0c412600002d0503101420814051280e00055009205001d58810004035540082c1110390034019244d80c4e1207420030090804030311110100160300106001c04030b9002a010102003002d90308121400d6865412400400c1002c044902035007000000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 75820676 1250 75819426 75819437
    0x20f0102120a061e051005090406030b06150c0c01031e09030207091a010503010e060303090a0b0d0f0b01020309040b030106080106030812010504050c070b0a060509010e0405160b0f030405030f0c100c 87
    0x42200308070720040b07051720440744107070030408036007581034000c0b412201c94060241c000d001603034581c1042c2107555801e80b0146d008625020b89601e2400d460030680304903008100180401108000044000d4900f41c0a10115642c00d03103e100c0445002e4032484907902d1080e00540911850a07030b00008840918408855240d84650560702d560381c0320040b241554494005120f054807203001003480d60045410060300b0001c40d02c00810716804135809400d854071071400c00d00101c80d440002c030043e11524032503e030259000b4440483e407843c1c01c0c1c10002251102600004099540d400060700b5602103a000391920300000854000780300c000b002840c098102520188254100016180441e01c01c000380901400042c001203004c01d503140c0c0109000b424018524100d03941c44004624040c2d009860445207407181c010301060256108109100316040340a41038140380060b40e4240040d8401002150180030400202e41c500d62030701e014081c26007400004001050135041c41d0800c980710350b9442c001340039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 75821926 1250 75820676 75820709
    0x30e0d0f0305040c09020a020303041407150c020111032d040506030c071e2f1f21150b031012030201021207110c0a0807060807020f0102120a06 63
    0x16081080d003800c2000900d400105596242004070070215540c020a10280c0005000e410159001000d0b40c007a90040548004a03d01c20654030341d54020761089142500c0d24943d0b001c001400303104039641184c01818106040101e903901c2c2c9003158041c48420550308610040c400d41207403518414418405208005032406c0c0c10240081d0840c007004100078600040010044100150b071551b2880c11030b001500c141030b8007410301c0c0103c1c00410341d41d8880da001ca01f11607840003000854032104103448014094a0303008041d07480d0b01d1182d5100700440424446103040c141400400d1a415044461418100098440d010b1120605401e03255111810703010b0284240210031040700d50720800c80d0031a5802c0900301c0c0d04c1c5c0c50260f01900880d0030380089600716004100c00144c04c641d4485400d0100d0054403c6203031110b00300a250107960107005080d50288009204050140500980008682c01240c1200c00e568405134260390189001070a010980c2d8140891118107000e03402c00b6184801e101010f12 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 75823176 1250 75821926 75821953
    0x201060f0504021812240703050c0909060f01030e060f0609090723150a090f0906300203030406050403050d0302070503070209060f04290904050a240507030c030e 71
    0xc05110344458414485441250341c117410822940740900300d05201040403d4480140300340c054803c8440c6000f1034108400101c48584200894507945401031010301c543e12a030301030148030800c40b562241899540c600d2017103841c0040090601c154400d002540c0d0929010341400f116107070180030b803030003540010010301450750501440001c81d41d14802d55421a18541c0008170700c0d221101b29001680f0001440c0d20368075602007060307419603007801800308030165102150011280c9510984c04078900740e015101e40011600c0054100305480003101c40004083e8001a04650181d4000400f1460006080007040414041040c206183c0d04085080c1030113511000d40720b10440400910900c3d000300090f01503981c008051018103809801003003818200c03905400c00f414042c230a1044114001e1401c4000d140c030342c2c0d8541c81198010003600710340c400d030750b518104050401c8442d0400e81801d45803610b0b203103040c42800d20440c06641d010510710245107010b030840d9100c0c09175105c2504000c4400810 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 75824426 1250 75823176 75823207
    0x40b0d0c0509010f0f170a051e060f04050c0904110d050601023d1a12070302060919090504030302030106110d08011a07050307080403021806030606090c13060201060f050402 76
    0x2c0314417400d01661504c403402017103e50290101c500c1d140300e22064103210340c1c0403aa41c00148101c08059841e03007061603480e1b10aa043c20201c80c8103910403900848444a41059082642c10460700d030402c1b0f042650718400981036400c4002010b1070f41d0030100700011015858017425400020030700281c02032000c80c510300070140203506101c40d0002054007545107403440145140d41c0084640d00c0400007001341c4d661040d40c5220051495105071514003d168100001107403d00c212603008005910f40140d04042c481c605450000c24880d8444649000659141c0b90041ca4812403103a1f0340141c0d60760401c5000303400718402200da5102c55004c51014010301e9080300c13025055549a94a83c442c1c0d207a466280e10603032081c00d400810302d0102144000400c00c1d0314028009a0303208654080c0038040648502c41002c03401c0720310660680c05140494000c5c00c102c100150407031050010246000c031141e0700d003005a50b20341c0c06203005031340d40c07801040420360074002134011302030481d010762a012000201144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 75825676 1250 75824426 75824447
    0x90301090b2a0a1d1002030307021b030318010203121e0106020f06061c15020a020601050907021b01030603020d0c0302030706020307080403060c050c06070503070201060906060f0f1202040b0d0c050901 88
    0x148841213044012200c0003c2032000000001410341e412080840030080d01da410a0358803402601c904008640807161529401c903044202600441c10102c0c002c281094040c00030358014154001040840300d8000541481807050121b00f14154001131002c41015545105034001411508000c903841d40310600800c015030040c80c00c54034414a0103100d4031844082042100081c041110000b40485803207581c0c029149a440d55001e480e410380c3c0c5c89042c0a007403a4100c0310800141c0001c0d900721240307640b400e02c3c4e03a00c014044c9800503503940c403035004c1410301c00c40311800c1d10802c00380c1d401002145410000180030300f5161000c2c0d42401c983e42e6a10100b03001305c1c0802402c2075202c0d8401d007c180c0c410810f984403484200c0890342c950800c041c1c0902513038004e41c0c83c1c4c00154240400400c031448103000d001c0c101c1c1c003a0f540e202c407141e111070030803a804007070081c0c51820000c0301c06400700008c07814009400074001032100b2031303913640075008101d04032175200b6448400c6c050140202c041582e08401b5004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 75826926 1250 75825676 75825697
    0x7030c06110a02091021020a0e01031a07020c04020a030209040f110912010e01110d05150607060513060f0b010e0a050609120307080a08040b063003090301090b2a 71
    0x644c0391103031103d048461400d500440045c9000348050010b03910203103403048000317009850f295006503e807207207008903800c2404084c0403181c00c0e1000d40f43c04420001c03801ea000c522841521a032851040002c1c00f030b644010200760010350003240610103483e052080c0bd17a5a10030b140704004001c41c0c90078419603801150320251017600c04605183d40590f081d000303c100320034004002c03c903903045162000040d070070034411640050324080008030706080010440c03200c1d0702c0080c001030600c40d00e9500c00001c3e020052000c0d013100c8104403801c00140850103144942811b070000031520305203102c00140015001c400e054032444801a00300b0868544a08403040000155980040215036045280c59031040380d600401005000650218580c1c0c000070b0340303000c0d0f4031519031105c180d2101801c2103a2018544401c0c20442c0200d8400340c1c042d5941c1c0f4104181440700426282840304d4480001e0031600e0700300c0d0a40d0b203084031108000021540407032440328001e00100c20f0b480100f100d00e002e04507004000c1c000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 75828176 1250 75826926 75826939
    0x709050d0201031808031f0302030c0907030e0f06090c06161b030c090b010801050105031905060d060905071509061715120703060507030209010e1005070c0807030c06110a02 76
    0x118190b91198011510b010114001002c540c1d0f40b51405c101a5802164489030140b01120300d4048860004410812282c0003001012003d0005080009417007002d0081c009055490304a0030300b00b0011700c414400e01411074058501450844802e82c1440c54600001d44a00c070304010305190071403200755900d0b400b9040491111403201841904841c42c00e07a0300050982480f403200015200d06607000091451001c1c1d95905060b640c410040d04e107804245c68601e0101e6411300031828144090b40111b50180000700320607884609a1030310011920151415901034014071014029501042d240a0303014441e841e06a00940ca820402030820307501245850320700d40c070750b800f1454001c40361440303030f03c9104c008006103090000b1003451561511681300440e4014184400103400901074800c0d40c00700501030715041c61f080215410024241219080f160511805101c03160204041200703c102038000280240b0a031411803c1c0b03086c103039259a00000030030421540e41c03140241d01183e40c606043d4152a05e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 75829426 1250 75828176 75828199
    0x90615060d090606121b09020406050d0f0609111206010207030b07111f0b03010506010e03070b030c07080c1f020301150e01030605030d0905040b0301050408030105010804080d1503030f08070905 85
    0x1000103013265900c001d94070200300c010300040c03040ca004030208850001030303149602c0b13595056400c141c0c0290300c0f4520128009100000000019810002c0c525000050000d00c1684407100c1d0800c9403505090700e800c100b000300d042c14000d1181d420300d139003100c401d000900d4414550f64581e5079000b0700400c00c60410040d00101003c1d10410000b0b00400c468904920f08800304160400e0010305c0381100c0e0600c030f5070130180402d0b010750040005c2074a505014001e0301c03400b400d01445001c2a88050061070140034100a6040803400d006c000c1d00100034030101410310141c9481150311013000c00303135051003042d1040004110300c07000c880c6402804030ba03d0800ca03102280040050700100300355803055405000d010f410308a8141d2140103581a15021a010401001048281822100b003110028803d444c00c0005000035130040581551141c4034020b02803030030f00454900c5042d038421010b0030100203000d0708144209904581c00c0381e00b86c0b00511300070b1158900780800400d291040d210315401502654007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 75830676 1250 75829426 75829433
    0x90a050f150a14040312020c01081005010c020d080304050a0507060f020c041e05010305070501030e1209060319020403052d07140406030803010b07120810090f06050414090615060d09 80
    0xd484010303081d50000c0136100d80d40c85c20312600843c10720302c0d40401405030a0100700e070b0f58014a0450b028846008440b00e4807410400199606280c2c480240d0307200003440c8200e80050201c000552056205001620201d035507403811a2401c00a0f070070140c14403906000100740654002880700f03e02400701c801141c40880c0c4000701e044881c1c400e41c0c0743c295608042c0084180300d00052094202d4000384d07810008642100700040e1200c040c200c6200c6031040c00c000c48252854014017640d08041218003050168010b104450200e03449a40201d0756034201b9030480c008c1001c0d075050400004c10124030201c00d107118204003502c5004a000c0c03000b00e108890b01d0029240c0b03880d4400009164071403d5144c1c0da584070b803640840e541152500303e458004461900b440c19100d0f503580348c042c880070b0001225140c2400d4990025101d10b00b014aa00c6640321000500b503039036030007102d81603c03c9039162189418106445802e0030341c0108103940c041ca10000c2910360361204404c90b1840000d0042c002201d218918 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 75831926 1250 75830676 75830687
    0x306040b060c0604060c02061f030803070201060f09060608010609080607030509030c190209010902070b010603110f041203090b041802030c07141c030b130b0a030b010b090a050f150a 80
    0xb039490b5051264108010802101340d110720880600b81c1c00b2121075a0300c07036031220303110240c02060902e49412018100b000500c04400380d60010050700012610700d440f000e009088903040d038005041203840c1c0c082004000d8202d880c10303000d81003a240050105040000042c4d03600c00183c400c1080650300e50000d8007030b020910075140441c2005043d00e042d0343e0041546a00c011f40854141d03c2440c03840000140703a030f068421100159403001c16150560f01e0540150000c11407003450607124441001030f141c10240c69802003004d4002090559011401803e0051407001e8030340000216032000c000501a401c5800b040c02a000c0503481c0160340d9036554441c0c07812500031b801000f445d14810069066040744049890502d1200c000140c08400466041c01ca099079015000d00f90008022200c603a0300c0704041d04030105403840078002440c50341d80c0ea500c505040790241d01666144201188035040c41ca0b050718642d00904080300c40700c0b007103081140005d280c43c1e1402900c66041b2800615000854041c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 75833176 1250 75831926 75831937
    0x209192d080f0a150207170a030b0618040e010207021804032d0305100501051603050705030316080a0605010804020f04022109010b0103020304020f06070f0b070c0605090d08010e0c04080303150103110f0306040b06 93
    0x502f403142c423034540d0134203090800c103100003052043e4100507a01040200510036160380c150024210303503c0116008c00380348103d0024200b80c041140c000e803081600040d030480f5000c4140044070b682490754192100030f0031203c1c05803034131401078040d83e41000240e90200541e001080da400145c000013130ba51500381d8085c41101c0d001050303404040100194856000c40c50701e81e43c45107440700c03900e81d900e107043c90040307604074002c2030701140b18007000c04c02600b01f20030a20042c00c1d0260005182415120450080d1b94082071048144030040042001d402c00c20b0280e4000f0880c2803d00b175040d800c055000812580c1d03401c0e0150301880010a0f40800d01000e17a1000425139004961410340342000c8500030f003c08400780b02503841c2c07401c050202e080310310005551520303030310320b43d8903c001039003400000c0040080107441600301c10300c103000124401e00c2c18401140506003a46c00c8200c450360080000d001d80f0410542d2000354201403010111100c0100c0440e070307010300115000030301d03200c0c8a00050158040d0307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 75834426 1250 75833176 75833179
    0x9070e06061e041e0f060822060b01120c021005070c08030403050d050f010509070809071502030c0d02030a05160302010f050403030209192d080f0a150207170a030b 72
    0x2000039140140c80341a0040040c0e40c01c4901c8610a607140c103c100c540138000d4411002c080602a6040149a1050203a190080064541d0711600c0300c09070380c03203600d043c0411415907502e075030349024184540e0802d200481102403610140803c0359802c0c4081d40344c0460303070040c141c0f10740c8410020f06810b100302c240098603944100e8039622400c25060050568103e0a402c1c1d80709850540403c1c0745a4182e90018101e90008010907901d80d07880fa01103c010401501d288002d01c541a408980c070408101e11025400180d4021a15a8103801c41e09142002070b50707003d020b40d00104039600402d82d0200480b50000c1d4000c80c0c5240c0c9407043c2c03500320300408102c0d8040c2d5180d4503000600c010144d168004040405084940c000c0a0320300d025000080b06161066451611101014840714120408039042c8800c2c02500c1080880c1d40e04e4200c0d05251500240342081c0d04100030020070010703400b803000c004482c02c800450408001d44d4032001d07010000342c44888408000308441c8001c40c842d400032500c0150 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 75835676 1250 75834426 75834457
    0x70f02030f160e0912040513060506030106030902030c0901050117071206090b040e0d0807110f070305030703080108120307050721020309040608010513020d050304031205030105100809070e0606 85
    0x3007800d0150701114150103101030301c22540c0301081c50a000010b98803185c0c100445d240785440d103004100410406155141c01207a80c40c1e110004266032402d010314000c0c400ca40300800d000406204050600441002141c81403413802c0041c401c61f64030420404170a09289403850303180c1c90310801520800000407943c00b289052106c0403407000c01d03a07000004080c0c015a0140042c440f802140c54640d00345030712000000714446c0010701c0f507605c50800c81c10342030401c0c3d00780c80040d05000c000c5400c1070340c150801d40d20740d440002c11078201360b404182c541c01010130b600900555444c081300d4041d10300c4090b05041c10008003050020900500c002400c030f8445568080111003002d501c4084d46941050183c3c80c4a05c1c40e00b0000201400c040c015103100d0422070950762a61240f560030090541040da00a5070148003e00001c07001031141003495598000c030307840b20b40e100e41c545410095031b000c858400f002008020400e000680c0800995242500d241c044c0c00b02d29039585c04082242406200c0c01c01b2040030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 75836926 1250 75835676 75835693
    0x102070c030c0501050a0210020a0c051605010801050a0803031311180406060902120c0d0b060417060a110306010e01111014010506040324020d0e0c030c0411070f02030f 74
    0x1103a9145804581c45035412007941075454005413280d0041030308800150b040b0401e003400c1c08905900078030504185080200c41c40c0039503251103242481b840c4200300310a140e0003090000d0341c1c200141600508040391413209190500e056261179002c00b50515031080ca001074804100802203240c0c02420402402e0b4881d02c1000c0320540340078401c16182a2486890304e60003007000700700d50084070440e4210545890403a112030f130a04549622400307030034050643c2d070303034441030642d0710748006100419403140380c0780c8582820f910380f6040c4400a4a0840002d00c1d107a90319030145220380549912031401d0034603004e913114250041c0c030310304111402c403800741c0a00300c10300b03141111aa0000400c000104170f0340c0c0fa20380e20790342408103510413070102820841c502c80c10f10401d6150110319a0040041d81d2000d42401401074030a8143c0b4041c8244131501d803c1902c0141e03050401704100c2e000c0110844040c0214480c1043d0410750381300c1c0320006415090002195020f540707007005070303804400080080342c1054 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 75838176 1250 75836926 75836933
    0x403060f090308100602070e0915010605030103030e01020304050d0b0a0608060901020a23070803040c0509070c0209073e2d030301030c170a1202030307020712050604021c05010207 79
    0x4000e4901c00b1804a400c11010800380410310b400042030714219002084007504002d11010b109000620f1101d06104a042c034003c50078040c40c3d440d000703004980f292a01da50542c0b40c0500351034200310030141154801d000401c0540d8031000702d01c01e40303a00a4017045585c0c8468071b00030094415904068030500c28034003400321580055005100740e00d040c0e40d400c44001a8a011203a05e00300001c03040000c420140009008506104002d54106100e1100711035602c2e1340c0c2000c265204012a810f0011400040d1141c0c10b504141000980c40542ca2800700710040112584000344104200a20500d602411a481c060303c05401030003002020f03001290203850b104102d481d2601c1e42052400302d012505654072201200c0041a64143e87d03014105180007810b0041f401c6103200c0e8110109020710455030641c1c041510696405072500c2c06602950352494000d50103403509806500003900b408401030240040f8502240c0e083d00140d04550401100d03000b00c804000702c2c1d103090720207011544006118400c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 75839426 1250 75838176 75838181
    0x213050108100e1204030308090a1e120302031006050f040b0d0e010c0206011d040201140d050405010b010906020a0204020304020316120606050d110d05032b0605030102130b09060403060f 82
    0x300401000140490118000e03074548a040001130490401c1045c0420300c0024010380392a82d04c40c0700b400841d0003d08203901d0702c0511143d01e413810b00720400c03948412018068801c2418400c0c16060a0551844c20802d8560000400611981c0c04000010030344d900c500b4401c50440d00101024224a522010700005440051003c0c0c1c0034001c0561030900103802441c00841c0c23041c1210800c0984918103041880d10019068000b0401c904000c01c1126110b490500036024000c4980003010010f5240341518216003100c540303441c0319041c00074105041020301e40c002004403100341d041e500540c60307844034404245070200e6044042c0d500710b0500000f10305950102404004c0c580a244148505507443c1d0512480c003464410242c071484107035142e250541400101d030705009101c3c100722854400c582e07000c807804066a480c50304055003013910b401d00c070300414000e09001d000c04600861034490300304400c2205140c0c81c403452103501d9000c1240d5006640b128241c0f401140c1062090000040d54142c0100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 75840676 1250 75839426 75839443
    0x90801061806090504030207090b042a0e010305060a0b0d0b0306071106070302090f0402090d020303030a02130b0c0601170a050106060305090d030911130b030a0308041202060906060108040213050108 87
    0x100c8926110b4006024a4140a860302403034060700a499110b00b0301c042a40a800d0000d1500d800c203403901c0c0c0309841c0c9403106a8020007000440c4d40541c00352801c4070700070450502d00004504050814050000660396411028211004040312907034420070f107180750b006000b4002040f50700d03000d05410804250703040842c05200c2c090050560388a540e81c04c0c010341c200d000d0700c2a519080360503001c29041c41d040c503070300400b1000300c02070910140721030550001c0d05c0c1da401251000c0319290040f61600400c441c815002c0043c040c444140c6040041124030b040c0c0e1801c0501c1100b0480c011100454130007042844660b070f00d0341d0080020301615403950400340180400f5101006d180c400d50300114000c0b4442e02c03541480aa01c00d4070a480c44d45044108100010102c040c05100356480c80c40b8140742c0e904011181140780b080c0c483c021903203030a04100d1f00d459481000718065400030700c00c1040410f008603820354007841c02d0920944030345490004c40c000020000c81810240c0c40c001c0007044a0301300159214 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 75841926 1250 75840676 75840719
    0x70317030412090b071403070b0a020904150503030f03040c1206020403150b0d02010302340201110f071e030609140106050a2102010c080301030c050319050607080709080106 76
    0x10000040380c2d000703c03101c11281c03240d2904010b043c461800001e0b8803282d020b0241110070126810325080343c5903000440010741d07050000c0ca83c000340a2001e0304041c0582c14032811481c182d0500c807490400881c0e246d22402c0201900d02a00000107010400c00c20f80c41c10142c04c468481c59102135075842d01c9002907100c0c1c002612030040c030b54800d0b9072420325805180280400a000d40021081d04d90042d4042d400035010014000c034032000c0e4001c102e820740c820381803da01490b09502e40351301a0001504221100c0344c041c460390081454a0500200014000d00715440b0070f17099004150080e1200c91080e0380c58000500241c1000380c1c0c20706001501408035681c0d03c00c00000c0085958580c100220a441d03032180e0791000a020802a01c0e109008000c68261801030500650810845d96150f041d42d00036041160300084000e13003030081342801c000840c00c40039000351140c40304185031512039827080b00900001c1080710f01400162010300c14151035004100c2000240b0415851340080d4070340100c0032040c0b0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 75843176 1250 75841926 75841943
    0x313020a05040e0d0f05040b130e0916030803071e0c0203060f090d0e030a06060303120506040603170a030b060c010b031923010b0604030c050405090105150d050703170304 75
    0x1080ca45014422400d14416600003086490b241c0c84c41030f60709071040c01880b406d002040c040000c401c0361000040c003d10810f882ca80303403c10704118101c461048060b09119903035001d001c00d182c144480300862410f894010003c2d42d283d1365030140441e4000411090704a4100c0c9600929000c250040c5403240150310890649030169640b0369054102c0c00c1c11200740c50258440b074406008280144064109842c0140a0781c01c441c5e61516a841628115031045000424000302949686441e10450350040f4085a051088601e1521209a1200f4140554580030340000303104101d140260700020388528081d01e06500c1e00c0b03411214500924a150846000c4d018400840ca04600d00304e000d5440d05512000c180d0000020b8152940c030040c02000b0040950b503203541041c041d507900e0005e44010340c440c850500c0300500f40414041039910140801c82c0ca60705120a2003401c0072800019041480d080c1c5092804400394144103103030100551018051120804004021303400110081d44614014040d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 75844426 1250 75843176 75843179
    0x10518031506120a02031c090308030708040b0c0405150a030906150501020f01020f0d0e03040f030b22020108150105070b0408090906180c0f040306020a0c1e02010e040e0f030313020a 80
    0x46495962103130000754940c01414501003036505100d0420303021841450070f9410184c8030303952800d2544c0b00781c03000c001042986081200308402c2500c2158401015401c0c40c0c10a403408010681142003038036812034641022480403030980c840d612074800305e80c0050040c81503003800b949082450340c060140318018041c8440c200402c030b5050089928424180c0001440d111092002c3e0b0700602000348800e80ca4042040300141c0c6403e0305503040003031070180b00541980d0601101d80c0c5032140e0100e41c004681d1000300440700c003507a04000d00799400f800c13030020040c1f01003806004032042c1c882d0780402000000a45c00f800244584080545504103042d0383e562aa9260310381005404aa501c82c2590211000c000045040c1d412002030401815415100c1e0705045d2a640e0b26403c0e81c019401080000340720b004280148901c945611074400c0003010002000c101e1038000070300c0c4d00b007481c041c10300490b21034803172504400d01000719000401e4154243ca0712070a204c5903041f1380f19900b00c0c00381d20031580c5810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 75845676 1250 75844426 75844459
    0x90504020412021c05161e0305150903190905041d0a15020d0606020c0907030234080a0503070908070b041413110705070f050609010518031506 63
    0x2140c1c00d45a110325500c0038807525500300201e11000c10754410a0f00fa2601641c00014001c002c800840403030111900360a03070804102c041c995684240400e0303011741026007080030880110303001c02d541d1104001e00c0c1040e41e652004504c5c501c04c450a0584e00503001101480f1550b03c041c04601b6604125410301c0301503441d06500f04041000b18085900d0340120001c2d41c00210200c42e29038030008001c8015042c40c80d11401142221980c1c2d0102003d07803c8684441290301d0180003081e0300010070b050071424520381141c60300300304c08907603400150002154100c02400e1080301d030b10f083c41d070360110f045603071440c0b007550042c01504152940d801050340c0c003c0100e0322a40106161050b00c2500301124142031904040111342c03156000038503000018031348502d0358888180103841d8030907012000d0350355550131440d2180c81c250065000803c11207640900307000940e90034048600300b40003440c0c05a2200301c001098540d014940c1242ca03458032070f11b00260130388460041c0d03941c4108030032103207040603205610 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 75846926 1250 75845676 75845681
    0x1306170102030c1b0709020f190201050405030313020303070f05070e07020106081c030902120615010309050d0f05040f09050601030e0c1005030901060b03010801020c0c0a1202010309030e090a0903090504 89
    0x1d502c0c01c0c00400038040302e816124400d414822043c074013005c40c1c40d51a92407243c4402c0360701417011504240c0d00041e0842c0504003e4606007280f080305d1008001629141e1156510303804040c0204481c4800b10912100395032b410070a40d12200d800c824000076441a620b02107645448921600a8079a02c40000039002801032050034120340002c0c01900c10800c0301e00304541c00e0513689000c481415998890800135031210b0315045c03102c02810380201030038144046000300304620004110304143c1071000701000503c0201d14541034400c1070034800c00029544405442c0ea0241e42c02114101740d80c4600041c100c21590401030090710b0030f8900300400d504104825840300d800721310264109068a04000c10140314000a42d07109044070000a117981d01d030f0b465006141d00030313800f0208981d00494040000c8005020030303225000200c6003611441d107042190480d4166061010341450b42d11000e002c00c2c540149100d000c5c2040007400d03116140707010b05003031000707040c3d10340145c0018411003000f0900c1e08092 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 75848176 1250 75846926 75846931
    0x60309250e01060806060d0221010b0f0909130f0b16080103030806090415150f080c030601180204210308010b0a02030d1a090103080d0b06040b1b0a02130617010203 72
    0x90001d00c1c06030308101d01550b0b60341c00075061503008501040010300d416114400f40010503114117460261a0700140160812801a004078034680002c020641e00d4901c0c107400c5501c4000d082c0c0e5820895030320509000e041500001300940b0b0010340350615004c0003a6040744034030491610200e0101c0c9400c008044940070000d00000b40814034a8020a001d40f42251400340d0041c400c240703442c944100c0e0f50011042d0b5008030580e888210079400d00f400560301c0d13842608040c1c00c50030001c1040c801d101d0300090340c0308010b01c129800c200c00413543d00014902e60301100c000d0450b03001280100d001d00540709181c140540d030154001440000046030003e000411901c040013554019810805034a40040007040d1504144c14000c211032507150054444007000c90003103005088503602c8280c044128425a04030700300491140008000500860700d40f0015144500c3c00c04a000800d4811110164588007200340040c1d40681d40d030710401c416816680004058038410710480c000c945003001040d00740e0206 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 75849426 1250 75848176 75848189
    0xc070308010e0910020c0705010e030d140a0c08190201050a05090727050f040302120301030f060911040516020c0a0b0304020121020307020c0109050d020906060a0e06030925 76
    0x3140010030480d984214101d070000100001e88500e41c04544c8010304917071114001c020303a5000004208015a0041c140190091041e4064569007041e018010900300944101160310704001c1800c07580a8410304d801001e203903000c5002035030b031954810260b00141100d10301000642c20100002c0042040d4040c40340211503000040c40e5450030702d0114400c1c04011220032110b405d140c00300384c41c2041203004050040c42c03041950025130405040090402e01c0300f5142a42c060f2080004100054803016040816908000300103020866071401d1031084070b4006003aa442030030f05042c030000780c0001040554008881d001c07140040300307039000e11400a61511450300005018800180903500070b0030380040c40300024000640c1516020443d604a800540c0d5590050303000d9810180785581009030320b000b030f0804841d48500b8032b9095001038010b5400600e814081c0c90042007100303415024140600d81200020582034403854a28800c9a540254000041c4c1d8100d9005d040260305080184500035a42d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 75850676 1250 75849426 75849437
    0xc0a060e030616050d050f09060105090c180103020d050405100b0406050d110303160546020312071506120506040602030411100f12110703030b04110708030f0c0703 72
    0x7100b4501014090f540c010080500030204003040d4000c0907845007a104421121890a01d030515a215624042e01608424004d850900512204001003020768407a00500701c81b02c90041d103140300480c0640074126004d42610705200520040110102d0b90750400300321104200200500c140400007070711003a120340e54000c0395600111003c605000d034140385254015084a1a0804503030134840302118803030003661190041d900c842700704401051001000d8003103015003108410005d0b501c40c24000040210a81461001400802c540b001d003c04003006040220341516a00ca50800c520001d00100d02c240b036040c03800f200412184000c0002c00315198004009110030740e80e5945410080d800a0720503a00384190340c5280000c1d031364604110444108980d140b500304d102c0100003a0840c420000b0f0140345c14284001c407115032403030354181d9002a402d80740200300903c0003000b1500030050070440700c3c94010006100000e22540e00e0046014500594060419942d1406146040e0140a41c020000762 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 75851926 1250 75850676 75850681
    0x1061502071707030c0312270b0313050d0206090d050403030905010f1101020a030c0216031707060b0d03110d0305040819030b13020a09080c0109050409080c1e0d050412120203040b0c0c0a060e0306 86
    0x209c060010b19440402c5504400d4040c0150300c440d0714200340a5054070069000714100180f02105020783c281d80c40303550500c64109070840d640074020304828061241004032024440b03901d1032150070f54104010042c0000c55850445070f000501400001100740050f1181d00300c09014100c810350781804403600913401b00d11a030000315107507419030f02514003a43d510f078803203c0803810341d522150700c000d525103e51243c50361060350320074841c1019050b000420034103141c801008003041d034038030446075012404a00070401d00d25200090f802014680e1407244c0240060781c3e0043c4808081d030050002401d00d4a54500035035139900c5180e0b49040c03d064040c0080c1c50240200f005080540200ca51144104515800c100601600610340841c5050183c0911450380c0e180003001d000b417014000c4100d45140851400c0c3c03c049005030714041460009000441591500c103141c1d2090060310301510340080c80c0f50751410883c001c6507442e00031210451080380314082c0080c190740640409030046001901408030366 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 75853176 1250 75851926 75851939
    0x80604050709240e010e0c18010f020114010e0403030516120c11030a121b050708070317070302040603050c03091f060f030501060801061502071707030c031227 70
    0x10030399603940389044070f4015503c0c1c03024003680303286402411007035620707104541c5400400d80e5080c3c005000d00402d824100092201048000180151000e0070300b00f44041c168104000ca004040348140b1030350b038144040000c92152865226603001d40d029540610464544c030600b00c1c072041c80e16085601041000701d01c1c5112800b15007001c0242141d900b031096100d00e0407001c65080d07a020303034103003c0001c80106280108400f58440e070901090040401c1c90400f042c00c001074040d02c104500605008408140c01c01050b205030340d0055956502100c0e240c05041801c0c0260181d01b2500807000468246400a404260b142c07080c1c0b84100c00820040601c060754400301d055281c006402280282d49400c0081034a4507a02d4a10004500c19800025054542400c05003100c18941004580118606020102da940024454184d4044400200e8a0791000203001c0c0f030001c50341e1004001e02c5a070100001480342000c0040c2e03007010340381c0307400c42c600c00340404c84001320202c46103500c01a0b11500d802e000e81c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 75854426 1250 75853176 75853181
    0x711060f0703023114030307030e040e03040602150601081012030e1207030c0e15090c0d1803170705040603200705010606020d0c02090c03060409060c0f09080604050709 74
    0xd800e50500514042c680c946094000303050181350ba01100c801c3c2c80e41d51310049a901c2000003002d60b00c09020114036200c0c0003903280c0c4500c06001e01040000c100c0d0243c81e03a0340d90f10840c582e14a0714102ca540f583e89000285d1900b9071545c460b02c45000620010b04554020882c49208190ba025074150003401e200b2044605000c4100c01c0c1e0400041212201150301c81820310350b0a247d4040061081910303510745001d010310070760401191001c81c40144102035889089201c0350304000c661205041e550500d0340c40c50b6015519401000314241103001101c0c06521030442c00490080c1d64000d2002c501c01c1502c8a158001e584000c005481080208021403081c1e000324048072510f90f040c01601c2070740010100e075420002041d901a550340808001d500c0d01004014a5506c5605040500402d9500061100780340144402c105180010000703040342d8459000440440d885202044444036801000740040010620390b80855400000450001c100203000c506c2554000300800d015810450254003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 75855676 1250 75854426 75854431
    0x201051b010905070f051002010608060c091203030406090b07050a021b040b0306010306140f040f1b031a04170903031602010507151a0f03030307180504060605040302090711060f 78
    0x1955845482d10001101800b845004098112503008400c0c288001c2006020f42e04250005581c5080703010040305102041c056480480c400d400c40e200c03624100491461000c91100c0c0c81396000010801003003051a600c02c41d030742030059070f4006003903849500990380c0e88200c1c0c01010250b481805425054581d00a00100011000d040802e0a00c8082d0120b1300e170802c00e030011103005440e09a0031110420480f10541d0140354502c5480c000d08140e1214845a842980b0103031541c06007a180e1020314001d00d00c02c00023540e02002c54100c082c07055007042c7d480c0f40282d030308071012200a03d0040d811840782d415038401c904000e0180d0f1800c40355240c6001c1015000004a0520005001e140c0125402d080004425000c41c4008904050742d54403410be41801c0c114624441c0f41030844c225181d46002090b268451214240a158441c40f24048000c3d4400b0b0307400f060b44141099004500e080e0301102038400c41c3e00c2528004c6080d194600203036011200c1000319100b55221000044403038103000300198 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 75856926 1250 75855676 75855727
    0xd0c02011227060b0f0906180915010303030905010e0c0a09021c0908070311030f25080a21020c03091017100608090d0905010c020a0f080105100f03020105 68
    0x88a04031849090350001c2100c20b03620309940315113440460074208a11070701401c0c103c80f5007515243c0000020101c03d011a500e0110042100000e60014410004032100f0030b160340c1c4640866a6a24000b4080e00350300c1c100300c445d54282f00160302d030b4281c00140301e103980e640213103680389050500b400344000b50403c0d80c007010707080c0340e045000c00440c465100d009078007406041e41030b5407004103050151064290f421250119801004103d015000c0c0e80f0036940902ca052400c0701c513a12400700c020040c1c0019101c080c001d4540000e9a00190b03402c91a82ca03e8034070040260703590300200c00c80080c220b02440300000c0311a0070800ca0a0402d00e0300c00c1d80b0542c2c2c5501070071701c01c0000c2204088800d092804440301180311040310814081160007400341e0b648142820f0003003c004a10070001406034500d0f00c01c0c64140b11518041034210342c0c5402413500944488152030640507510900301f4082c040a403034600448994006c0400c02031050f000807803d481e01078448501d000d100d0f116404c22410400e8090 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 75858176 1250 75856926 75856961
    0x102070603020d1103101a03040b0606030901090b0f0106180503030702040e0a0804090510080607020a0b090709050408031501180b030c190f020105090c090103080f0403050f010c020d0c020112 84
    0x68950302544004d14000c106ca030310325450150800c94000034241c003071204134035035840c02d00400c030015405482c4541e1088007500c50302c2c1c581e150005442d015204110b0014184008041040140841600c0b024121045e541e110000250003403809151440b041c050b444e00368001700302c003201500381500159400450751084868070300d41c0340c4130810786400940200310f100c1c0c2c0380c030240300426940a003c20054420301c0060415400c19100c041d58400307a004000f03105030740b00d1700000c010340414817100004102d0b590b424000f40c42d00345010602607000325201d0a50b03031f1081c1c0d1450890b510940d03884404101c1e43e224501220b0a011103412070781c000600907005010100401e110240d24107015480408141e1180700c05080c507480c0103801d5502c01030100e046a03000c1c0301459503070343c0c0b02e00d4040e04498203c4e003010f5480c000c0d2000310760540300b0380d0405044c5200e8580d038a44c01c224154040c6412000c10f6095411001000008640c40c07840ca03c80030740041c540010705c8078403041c030303501030444401c041000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 75859426 1250 75858176 75858191
    0x7020d110a030f0b1b071202030f070b06120715050c01110c0105060f0f0f0405090a060510170105010303080c0901090e071d040509060103080d020d1418010b0102070603020d 76
    0x2019007030070b500111043c000c2ca054420402c1442402c180d0400e03040c01440340002056003105040303001e082c0010b0a5042c2c12100301d50003500034000c5235042c00804000c0c580c1c840d02d508141800e004181c0c0d20b940901c100c1007000002070004a142020b9031000700c1000c960895104080b40e054000112205140d5030b102d061850000c0744200405800e00c40341c00220715841d00a0412881220341190980180000070100c0710700c0d55280444403200c501101d00042c0d60310307240415407900e00900c90041c543ca10b0a03003803044902c2d0600302c0c042101c0e9441000181c40300194021402d0b02d5003840000c1c08a0090070120380124017060192035004011700d0141280c42d92040c1003442c0c1c20042d41d1100c0881d0100c20007030148601031445590008043c1d406100070708200501c00c2c0d0b11501403101511120001c640d081004e17a00360101c5440c6a04c424080c804150a03000e4500312100a40380300e40c0403441e00c0017601a40c0c5040c09080c0d5030080507006802c06a14000c3c06401a500001c2800c503910743d22440c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 75860676 1250 75859426 75859429
    0x90b0301060801080615151806040e01050306010801020a020304030605071b03030606020708030412080a0c08070b06131505090a0204080f0a120503040f02041d15070e010f0507020d11 80
    0x694000c1016507104407095260068060810300d02510303218010094420229094664003040060408401c150341c0da02c002212091406041440015a003e2000140095403240020341c040c1a070701c08806035105a60f85803e01d500300d10030403400c0005608180800c0000c15150b03400603502012a041200700d800d0307074042d40d08040d40c1d0028110003280c0d503601c0034010168100200b002818282d00110b250900341141500c4000c02c612000303041510009040030b81d070b440b44250b61520369000d10036a0b15481c0514000c0d200701300454030a80034402203920070111000030b025403c0b0038240800404451810303c030500421800040c40581c0349a020480000c00d800e0822400341600506005000909010301d0214552013950b01d00004004c8107200b4480030400041100414a5040300c0000c0c840c801c4074245400d030103212980007107070b0040c414156201007200d00c84078424081c031399074204408819401941d141202c1074104001035028040c078130040c1401e030313010b2880500480303200700c0c19481c410 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 75861926 1250 75860676 75860699
    0xb030307060606030e0a030504090e03130b030402100305010b0327160f060f09270c0206100b041d0402030c03010c0f0f030513110a0504060b0c060108062509 69
    0x303000c031200790750707824100801c0350306118003000598a40e01420110001d51401492406940118031081c0d590780100c11340b42204004540c1650001004c41d164255140314120154000301c400743d00030050b040d404081316220340f0605060301c003000245801c40d1503008407001d205150101020584046c0140480c240c01304021507c00c0e602d00302c0884003094103124924181d04199406581031045d2845c814050a802091070402e560121011885480d50070300400385035800c11115505940c9031403084c0c1d8015501242ca5841112110f640041d515540d411043d0284030b5031047e00da400030b081c0844400130741c3c90b200d015002400202210402d00b64a00001d0864a27a0501040881c552651a4203101e8000200300c11010007800d0030051858900c13044032040510100003010160700510f04c03806036480c420321401800e07020344204000c548490f401110790b80141400715061058400000b254a000151184074082401c1240340b071841c105199010b444045c2d451100b40441007001094a00200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 75863176 1250 75861926 75861937
    0x603160b07020f0d0b071107050d0c05041d030a26070c210c02060a030f110903010f0e0c0603090a06050403051c1b050a0e130c02010b010228060b0303 66
    0x321115556401d1500c1080b640c1d040c0d00446602452601d52010301283c0c20a800b00e50105c8142040303e030010004111a00300002c036044260701a031090181d00600c002c1032400415918107940c01c0124402e01c02c0c08040c0c062495441c605550f004014240d03400e03200740200004950a210709545491410003d03a000c84000c03260000020714074006841030001c164464080b907002005103107454841144010079070006190041c0c00b800e40000c000700380505c2584240900a01c80c0e20030050888101107610441d404118250f110350b080c44e400d03003004001445034201c0441e0480003404001c000e00b09201d03094000800d035840c14003510360710f180460b541c2d0040c40c0c8928440e69466036589010141d0031a120072955516844628000030035150001d00e40401c44d80c41c00030700303265460b10305007401101d645100510b0a81c11404c0c1c7c90b085843c0300b000350040b07801250301e41c000340a51406800121303030355106131203a5140c0f0303481141e01c2180411408031900e582e901500010403820307010300100e465035204 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 75864426 1250 75863176 75863189
    0xc010207060e070b0f0301090207031b0c0609080d0815010302041a04030213090305160206040807120501050705120103080a03021207051201050307050d030815030a0c08190f0b060316 80
    0x40e040a030b81c4450b000d0000e100509403455001d070a0540d14045100c190005001d00181590300050741800c0c580210007000d5209035200d401580036a80d0f180c44100c010f01480f030b20020071541c241c00b04110002003250100144241c0e15541965a412404d1030700c48c01090349241496400c00002c503000c0d4414613228040c40351000e01c103603503900d50b2041c04104401144004c2c4668a00100c41c1c00180d4400200c40640700904490314240c502e50000540758030496120310111b01c0340c400e001943d012043c000e0f05a20780140002c0004d40d83c2c0303007010340b1544145400785113081c421308010b2000416080203003000141501d001070401145c13a000d14440720090703442c40c000c5100400e0000d1024040d1110f5809001c0030b40107045803514101c0812040d216488000f000d100b03003000051681800f107040e800e80400c00504503000e401c07460a001007802c2c56400380c12814003d408081c012540021080e4601c40c2d0720145002d215101500c6004140502134451641801448110f88000e100191910040c0c40e0303 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 75865676 1250 75864426 75864431
    0x307030c0c03020a0803220b070b070908010c02010f1401050f090405010e070b18010f020c120c060f12070e010f0f121b0e0102010b0901030f140d020109170712050a03020c01020706 79
    0x2804c22144032513085030100543c941d07c400f0050084602c1c4c41e064890055115140207216100d064003603d032902c40d508800201c3d80f80010108603540c0c1500b01104900c05818100000c1640540300b1506082c01d0180f26007201040d604249207040c01c5181360352180c003a074000903440341c0942915060a00030391050a0786280400c3c5224843c0c15400d9841d0600401d00702000c1000c00035001035142e804100445120f01601da14201c0080d00038000c01e002a08018005a42d94001d0b1b601c0b1131003600156080520310800100240c1c01074081c0800e04c0c11894140c440d036018690340c500848540c0b08410300e48080140f00328074440038075082c2c0580081040000402c160309210000f00901d51010785002a046a0420000b501261074004c46641582e402c64004500c0081904010660749803418003c03078076108013100000c21582c19403000180701d00c205000b17400c00414000e008801d028a06014001c06541500350103820700450041c401c00065040143c20b00400503116401c90300020425905d0a8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 75866926 1250 75865676 75865687
    0x5060a05161a0f06060304050705040b01020f070f09050603060108030702040504020414040506010503010f02040b040510020102040e04030e031b012001060f090501031a09031603021204080d03110a020307030c0c03020a0803 97
    0x750f40d15040d5921180982c1c60500714600360b01c540f03550f28540d100c0c3ca40210703510589000e07141d100341f140c003550550342c030200c801e440d94036510020744000c0d91140301102e610307240c01f10705107142c0824854101c505510066051034156000c110040c0b0016104036031083c1e172131046640b8100d521882d81d104600032400b030003a9601d010705041c00e403440f942000e5801841000f050101c1d4554506490a4500030385582e81b802400b18003e0340207100700d0b002001c10b502c0f0403080000305644a00c1002c00c501054040d1400703107030080c5a006801c206140558085442e101d40b0185422428007070b444000141c03800420610703600c00000308543e881d90440780c01a41c07240014410700c2910010000314490f03c84002d43c3c1e40c0341c0b4041490302c034004ca145a404205210201a003403600c01c00c99406a03181c82c07000d0700e65031782d07480000350340d504001e194000100b4105212079241e1404001503408150b40c54000d90b1030300340c0300c2e03508403940150400121600303002c1d5140030003d40c82d440406005003542c4002541d841 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 75868176 1250 75866926 75866941
    0x1c02030d030e07030f06021b0a060c0512010b0706060f12051b0603060910091802030c04090305040b09120102130509010b0a0207060305090319020303010f09050105060a05161a 77
    0x305145112040c9030501d4110440b100b40042d03680103c0390055483c11305c0c0c0b851440c000001c1d11070840701d030f079860003207188541543c44c0c0441c0c40000144074001c200802d8203045401d0302c1c41d000d009042c803079195151004010a49003503004105c440c0c41194000351450700c5805000e4000120b4100c64004075100702706004026041002071800064901401300e103400c0b140000b13115210040105019030312405c0400c0e4840c40e04400c0c1d40103401d01e850140407030700c0311200c008489900c007a0300f80e10910170010180c200e030034144284d41890750907135505031500c2c0c208590b0100644c0040f5140390030254104151105100a1002e401c0396454121106d294030f01e40403c0144103407040e00444081001000510b614a80014800d002c07600181808a9036641e5120114154040c0d044400c8407910345c0d184114030142e01000442c161010312110f0703840700d034684207450100c1d0742c00d02540350071600401441d00124040c00c0540b9094071a001d0030740050803c1d0340c07403c46102480825011903d148010700212 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 75869426 1250 75868176 75868183
    0x90a0912030b04150506070f140a050c0112020903070504020f1303060203011a04080c011b120c1202030412082208030405010e0f030607030b03031b03030f070203070201020d0305151c0203 82
    0x13034401205030410500345000200d06100d5510010130904222200340f040010107104909203c403c08192040c00c551414881e40b16004030010300d00184411070400744c6100680300751660340300007038001c040705410041804001e40c0491000d03c14a001840113404e0400042003107006980303e40c0007d83c80c0d516140a051900342c6410b1400c0810b0010b200c280b00d4840c0c000703940c0380d5046091070b2018803407a00b1000b0203000003c2032006400d4000400d040590035170400d16040f6082c1c032402d9400041c0880e294101d0f143e0146000b000b001c50104115a0b000c500c40c1005800042c418445440c600b204244a4400c040580e61000c13000d600041820400e660300842c03c0e0f504070605441807100c15645030002070300c0d80c0000b0611001e04d0b0385c591181416403010000d0b03900050500c2c00303d0341c1c1950710544907607403034000711410014001038100086010780702000340c80400754181c009280e03070038210300d0035000341c0705c000c010b03169210003840041101c1d6103106501c3c0302c19048540350090f41c0000d0051504 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 75870676 1250 75869426 75869441
    0x20d0318140f2b020409021005030708010e010f1703040503070303200109020109090e010b061b01150f06140c011401030506060d02091501020a060204090e0d170105090a0912030b04 79
    0x10820640c0c2c82d03084411124034440b9215652240f2800c4114402e02c0000c4c010300c019400603400050258003280b4440d041030055002e80655280d54209a0303980d0070003c2c0e50102401008914000c48004211203844403454079180e50b0304070240e9080c0745d2514040b03407910030944d00980c00540101036032104a01110424403080d14000d000b802540c006800203041c1c87c04511407682500e81d10402000c0c4a0801e501c1320400d8000102125500d00c404ca4000074083c3c2e0050b48441c0f29481c00c00329201071542000a2800c840740c24040d00452403030200181c58000306d081e60f4543c030392010411a80d020780c081c0704210103048000400760583d41142000780c40c048004000340d00581d075007801b4401590b07407070383c0256020200c030107119109601080100c0c00c1c902a105e000b800c9a00125010a000e102e5800081d81d62561004803100044c0712401150171150010507414001d000b000148050304014500c1e03607122040d01c4020a502c00c00303940324032941000081503030000e0b40c2d605900c2c280c3c3c600f9020320300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 75871926 1250 75870676 75870679
    0x303011707080c31020c0c03031206060702030703050f1605060307170a060b1c050c1204060504020d0503031e090705031518030403080403030305130f020d0318140f 72
    0x607800d04002d001666046072140d050b120b6144640d007888800403048070002c00d464040484007203c90300d040500041c1d0005000541280940d5030a2205420004140d4042e00d0304040001c03071301c0c0c80f1442030042c150f00104050342c01d03000ba01c40101c08148200303c09042c2c0500e000050890300300e2140906000101900014400d0344100103224216620081d05587e00c0340c03090300c4410710b44410fa00000146000e500c10b0354006404502c804811504d090440340320301c0103007001c0c0600d6851901c0741e4100c0c0700f100c0b0303040300a0258902140c041030040e0701441d031092002e0884103903510103032241c13491500110381c40005041d080814080740070715100c256401414503401004402d04117800a9140c506026000702c44c500346000080d20100c048601c500060495400e5031b03074942d10b03400d1901c0030707500c2170000b0b50100e402e00002c07540c0a082c403007030000110340010b80c040c03068903680d08000e425081010181c0030405903441515105515040b84401010b01a0507070507001e0003c0103114000d282c2800f903d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 75873176 1250 75871926 75871933
    0x20f0105150102100e0309030115170105040f0b07030f0f02030907080705011d0604030606031b0f03020a060c14060702070f09020a050a080a1509020301050909060601020d050702180903030117 84
    0x7518581d800042e40700070001e0b000d4011a051034070b00d00162440c0205440701c2e40c158204071500a191010001134001d60b204581d0101440c0114811a0700766401614000e000d034010342505008034640c55403494125820389000304003004610032000a48096000b4480801e81c00000c4c049401401c000c0ea800404000001d0007003d4981800a0194802036a554846543c48458601d680d5580c0f41150701451f806401085005d451381030491a01e00305102d806416080200e000c1803620001a440e001c580d8000c10304034038036051800490b00042e0456040b5002c0c80c2807440980412014041d061060349140c1c01401005c2c501100011a42410751014140c1407040203007076a202c0d800381c22107210341d009080200c09501c1c0d008a10740104005506040340c0d20100c0340100e18010f240c0c00450481c1d0046031400070316241c44d44003c1e1103240a0320b25078056807001d50128440d03030181d0050101c032800140b42000c0818000310070000d1110480d8002095080000184140d42c001d1102d0200d40314500c004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 75874426 1250 75873176 75873211
    0x150103030e010c0609050304060203040f1e090b0d0c0305011a040e030412050a0609060c030506010e010801090f06030c08030306040c020f1b0d0614040302070501030903020709050604090c06020f0105 87
    0x3520800041d10018100039000441400784038081c0c100305a000c1d4040d00701c80c1c0e02c50b0345010094503a0007170300407281c41404454002800c1707070f8900240c1c2e120b42d010911407000a0326044c19000101520002a500322009c95082d4001c900104c40c0d0100a6004a001140249054411030340400c038280c0c17558030992410a90460082d000410786080d00c0b8440c0b01014203e5150030054940311004c0c070001d00e407034144140c0504114182d0044204104251414031080c2c4500005641c40c84d180e0002c207002a1415004006031426034118a1f000c2908420014015440341c580008000158004c642c00754400400c0c0002400d151181075403045083c40588130003040d0b20242034a81102e203006003a420301c509646a00780d52444003000055034486c0c010808082002d06130011030101704c60a234054081c446c1c00040350b50003401000da0a50345071b800750034080d060501c00e400a280140503c1c6d0001e43e01e1208800203408814498003034101038004044014100c5081429a0740052a154103119031002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 75875676 1250 75874426 75874433
    0x41a0a0f0b0f0705070513060812070201021f020f0c0a0b01050406031a0601030b0604080c091b04062006130c14060d0507030f05010b0703170702030f07060b1003020309150103 77
    0x251030411034032000107a551111811315600e02840b07074001c1e640c000c2e0482400c3d0300001c4141d2010040b10b54141c280c43c4c0b016085c0742c0c60301948c0510803010b40540c000c00c95490b40d148601ca1b9110702c01203042d800505203d440d03817a801040c0c00840c000007155001e20407000c10300c0074030030401340100021581440958103540d03030415260440742400ba4142030680c04258181e000340c0010801c81005000203841e980e940100361f03620078000010901800000c2e002c1034a0310a984041120b0440400c0d806180c207180ca402120004000b20300d2004c913038080a609035040600784851030185003103844074819000a4200b59104040f180e211a07111803403510010300540740e136400d40c0c07048000d81100180030355030f001d4154040c1c036021111000151901001045051000d0040e0140318001d0352645000812030040c0c54103c4001c1c4d0f1b0000151b8000d00403d068219044014010745104040c00b141c46911300c00410b02c14000148150042074010042141c84002008641c00251085980460070f514684 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 75876926 1250 75875676 75875699
    0x150609070903030f090e04081206100206070e06070227010f080703081b06040503030a14060d0b06061c020316020c010801051908030c0a030f1115070905041a0a0f 71
    0x440202409040320f8490082e41c05090804010702140f08511642c0c1340c00c1c50b16800d141e00a209c0301c1e00e1141d091010640ca410461680c0400c2a000e80042c200341e10f07900021794a0380c50b00316269034007150400460b40140c440d032111508d0070322103201d0030114042c80740204214103016080301c0510900c25178104218000050550100c94200305010303500e50a030225680426440b07000c00503a0310850003403008009001005510485079504208a0000f681c0881048500305407520340d4005501070151012410f9482007036044240208001d180c2800c020080c2c108205900500129590220030444501e00030300b4000354513b8a48090042c00c6110750000e8900e000600400d03000f140c0720b46940100d28040000c102c054403100f01225210641700a400d681c41c0c1100c3c4084001450070032900700024095480c0c03800d50007029010380703291441c4c01500c0305010300080010040083c82d04000170745480340d100e512031900396000800e1070510742400b40074801240340d01c07002580c0d01100e420090300d031010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 75878176 1250 75876926 75876929
    0xd0c0308070306051e01030506061e2503090e060a2402070906090603060e0607090e07020a020d03020f011514010e030106030803010b0c01110a080c28021506090709 72
    0x506000015441d501c2048009051076004107410000c0030800104a1440b484606203201091f0703014001991600284002da0145480c440c40414a0410f8003098140f035070050b0865041c140380c013a0b4030000b110740000040c05942001d501203000c4050a008461410204680c0103809440c1c0040d102d11340040c240c03e03144600c1c0c51042440750042098840e602c2800f41c1d01c02052000340600980d40c542090100820041c0300443d001440c0c101071600103000400d20780c3c800c048076103554080e10700e450040401500c006007201d0850044424040040c0d44d2441c409a0280c02980109144003482002c142101c00740010a00c007441402c1c0c0030005240da00e800400f00784401c1c07800c0114002001c0120b800760103681c1004202100200021403510282c07009011000c4120b4028000c0d41c0f40d020b0020b80720b101c0c20502100203002c050008084e01a403d0040c00c0b00d2182212005180c05c0507102c40c0851440c030b41d103d400580012a00d5810a0611958187c22030000c0b078041000341040e0b00c003c1c2a03660319 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 75879426 1250 75878176 75878183
    0x5060f041503050303010b040504060f050604051e0307060807030b0909060613060305060906040c0902030c0a03050c1905190201180303051e100e090105070806120f1005060306090d0c 80
    0x40c0c4074480841c03410a40800c00555102c02202d13103d50711500132040c1900a802004e0085207403150010790007422123411001c40e0fa02614052819003044140b00d074116580c68030040302c420000d456010b40c0c0301045184014107180e618a03026045c0030340010240e43e0241d26003485070034040203000504201080b00c2c1d0308181e08a895030000c0003000c000b2800391070154000b400500810040000242002c40c02e940324521914240140300c0c2c445007000101c1c0019120000690340c11f00c29404607501941c040380d08500c00211690a00680e0b5242204100c00c6803001e8000800214060021104004510f042c26a080c002840f20142d0a540343c2420307842210060101512a804a880c024200641413200d1007070050b114518a4500e2901d0701a038414030030800c80380381340710001c0c045d20b0040c860180a607101e5642c540381a1034010412022401c03000b8203004600900384415145003081054501c040032590010400c6d140c14010542800c20081031000c0a400150580da02c1e9580142c50746c208952 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 75880676 1250 75879426 75879431
    0x30305060f10050c0a14070305060f1501052505070e06040c0507080f070506010e0105150405011d1306030f110409080d15030f03080405070603021306030f0b04050112030906020105060f04 82
    0x800c0e01d1390789402071003030029140e05140203c1010703401d0081034640a480c000c404440702625482241003406404881c40115011034982d0b4407003540c89080101004820600d4001103028a58402c01c00c1c40540b42d0202c42c00d80c0100410403d00d1099950745038010421a4200132460703503544041d00521500c000148484400103240d60041444426640c0301d941000440b0f80541c0c6030080e40c04199005c1c040c0a11400b0074130500f901324914001224265041039480142c404016000014543c407108046d42d408145040005d8038290580301d58401075005504d4800345464034100300810380c4842100c24050780c14400603501241611007151014083c10100085044000c0f508226110240d04003c01c000711003880d1106044d800b00c201e5010303034064416030f41d80d2039450b01b0940c100e00c1a119040f0001a0000081003120300039030200007000521130740495103000fa02d00140440b4004d8011100354082da86540c002c2c103602c0500a40500000c2c0020480c605141000031451281500c5c2e562190743c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 75881926 1250 75880676 75880687
    0x60c0204060b0a1112040f05060307090801240e01050906061b03192d0c1b170d0c0804030b04020f0d080408010c0503040b04081e070b04030305060f1005 67
    0x1103407680044001d081020442e910f89490700d500a10001425440a00034407071048446820540001150304a40d24a0345c0201680d107410140b200c6600000e1440d804c0c07001c05000011160000e000e031070490440110a407440030000e42154580e9403403604030b440b900d411032005100e107886a840150b001402150a0351700c520340c5229105003008001c0e000d0200d0b00002c501d07a04003600c2c0110164070b40c130844d10340185048426007195402040c000342c03944c00751413031a110200365010701400c0b0a000d0203107010050b55601c03203100003588540c035404429040c0030300345180410b070340070701c1084520071191811136150b040d0368481401c3d501071808017a1a103000e0002080440da102c030ba051591140140080f6040d9420f0306004c140703500103210f280b0f155400d202c8065001d61244084920aa50024070a4200d407204c0d201e11520750840b00c00811881080881c0a01c0c42e11100007400d40300384148000c2c0b8444c1b4042c0350003400c0c3d40f000391a4900595001401902c9581c07003041101d41402d4602c0c0c00e94480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 75883176 1250 75881926 75881929
    0x20403080d090813080a0c08030a020a0b09070302090f0601110304150f1e08040b1308180307050603090120040305030a08090304120c0906080d02030d0c140301090c020f0115060c02 79
    0x40c07180341c881130400d00301c04d400050141004194042494040d0000a0903207a55415035500d921442c000b0400507048414400001400140b443e0b8011110717a040300c41a907125030204070508002e494075400c04180c0001c100c030f691b0703000c5070001c0105070260246042074600000e04c010b500002c1d0000c018020321500c0c80300500c0c03103a840302080c480c0341d982c094840b0303803c020050b02600d4182c500382c8185039000009140468020b041203c2c050f40040a24500070340e60f900d040c004583c09a140d1741c14003d02c900080c0980d03e010103580a8071006000144c048104001a540b80400386101e00c1000018070082011904c04800c0c0e030541034032030400c0002d550303c0120b990300307500c11500f000103c02c05d44210241803103e032414007c1640c0c1000303000c210b11030315111141d40d503484229910005074410004926072060390303080101e060381c01c0d0800c010f010325180394801c0c080e08260000c56415544141c0520001e90400541403103a000714020013000b0f2070030362120900a0103016200900054002c40c0045 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 75884426 1250 75883176 75883193
    0x8011a03030412081e0f030a1b140f040b2208060118020d1d03070c090b0901050607050106030213020d1506050a0f0c060e0105090d08010e13020d0203011b020f01020403080d09 77
    0x45030059900a1b55130703100281780f080181c20070b4441005081c0b07009102a00000030b03001c0031803544800d854014880401d803803140e01552201400110480e018440001d15a400308068030f258880c0c4801e6001143c85004c040383c000d5102c2d48000034991005004001500441444140108240c40c000d41e48500b142942c0c0003038009524159074402040c03d42d00f100d00000300103003943d244100d004804140d41d881408007a14060711390164805842c000400c00e03450503200816880b4400c3d000884d50325940e4002420b0400f00404c54552540c000825005412b20751294800c0101c0082c20b00c3c0c0c00c10300349000100580142c0030101c06002a0308040c18a06000700f64a450041e8841d0382804404102103105002c0c3c5000d41d4801070b1842000e150007503d41c00342d0039040c144e03040c0d0505081c1c1c8c1e940c0d9004c901c1c102961400180d81021f42d03907510f0f0025072002e0041c080440501024110006049000240342210820b40885c180c3d1040c1320601c0003408510444440e0945000049441000c60405149 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 75885676 1250 75884426 75884467
    0x912050f0a150c110601062d1d010503090d030b150c03040303030e0a1709010c15050105030715170702070816080706050a05030a1a030708011a0303041208 68
    0x46841140040c000300014444440c0394034050403401e02c002e0400480503101350700e40c0007040303000d40c11080042c09018800c0f00b07034690925824846450305603c0a2941065094220022000131840c0035001c410110100f01440c040c1c9c001c2c68050318514040945903102d201e803075012020561124024070702551482d50114841003003480b00c550b03800c40c0352601c2d80e03a0303882031004801003424444544c81808003c95802d42558001a110301e006400880c0314420742e100801d414180010000c0d03030008500304040344601501c02140c0081c440d414407080500c1c10466a0102d216000c02e41c04c0c1841c1c07194022010046803090019540450b00c1d0341c05c0982c10031038070344c101391400c1c410321150000703c841e40d028460403070b2680c005403842146c4a034421952803040741c4250700441c0003040480c80009842c0d10240018480007450001980070320300181c10400d06901c2600c0e142e45130000d03554400345c3d250042c032014804070002c510303041c901501a1300600341c52501501c0800c0200c0d400410b0b1104881d92403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 75886926 1250 75885676 75885703
    0x406050c04080304090b0f0f090f04060204091805010f0506010c0f0609060e0d09050d08031519080304030c0f030c0608090a06020d0501031a0903030115050705121e0a091205 76
    0x36140d03070f01c40740a8002012103c1c46d10b4800c07216600e194060b41001340049803882d1020b171810300140e0300c01d801c4040d480c03000b42c41260516400c000014920f400e070701c030303065501e0050000e05000c1d20036420302070309503008544d400018520341010b01003a0b81e0016188006030b83c0c404803080c201d40c90b0b8244440140704001d00904858204603003244442c04c003060080302e04d825921034141c042d45440521900b0702401500806002007000460305040c1444402c07903800350010040106040d400f8450503a005440c0e0051000380e0010a0030310800a0b02e004c1c0001510b01403030716230b00d214610303140c2c0d18108680748280420300001601149209009000040b94180c118000b590b03148139a019410041000744010f803805c0c24289642400c4042e80300201d8080c1ca800c100950840c0d003031084120440214450142c24003104210140004e082802100d042000f0600034680b04c1c110030203201d40c5111006480c00c0003410800c8040d8416401c5800c58043d40c410007040c0c00045c030b05142440c83c05400d03042a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 75888176 1250 75886926 75886933
    0x1200105040b01080607050306221e05071b02060d0509030d060803120108060f04060e070e0a02092803031d030610090c0201060509010e04170406180b090105030406050c0408 76
    0x52245840d00103048507111302c01c50350543c0c0d8010f821244c5000c05d842c16644802501c10703440b400f10708000450003140c012000010b003459440003800403d01080c403078106454441c0208044103070080070403400c40c40c15070000741e48100d036a8000389141c400c0e09106c88056541b440820394444007001550038243ca09081040710781d0f11500038690703903001128068018401d090010803171440100340702e4041e8000030a404215116503807407502800b80300820261921400c0c2c4002150703a03000341005e0041200f050300507540e24900c1c05018101d62601c03a1110022480160026035514044403401126018900303642c1c1c998100c012030051101c1003054581c1807003640d041c400601e6184c02c0c484210f42d0159000c100403d07031940c061307090303818070301c00c0680c01034060f001001a04901d1358200d40c0948242d04142d20124244100816600f060f04803000140b0160000c0c0307805a0a40c21603006450b400f01d4280c02d01840e0360008000c0d20004000074006c81d203075004600c440e15001e050394050008203064 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 75889426 1250 75888176 75888181
    0x70905060a0201060305120f070b041e0c050405010501020a02090c090a0909030e0a0501091406071e03091703030115050a0c06050106050904050a05010b03040311190803061011060601200105 83
    0xf80a003903907000c255030a0143d5004074415400c1d100880e44d0f0001426842801d026203616001c00c0c0c120000c20507103d5255102201600c4c580c040c0403051524481e0000201883c1050b080c402155016000b00c0e05562100040c0405607a074000800da220031240102941d0300e105101040c101402684204140d5042c001d69208043e0080c0c220000d0810903200340c40800c0d41c40e00111003083c100d10a4104045000004489500b4014024407441e8001c40301801e41c018009065080e059907110300303800088000b0760601215001c4c0d0300001d071100d0007400031760075541444a04604088011100001d00030000382e100203003400703030b00800b0b0a260000700c108419a55004058480c0d480510018071462a14001948060080c8100c90681c0e0028945030f085603160768042e80e60b1042408804818400c3d407100321040021000c03050301c654840c1c3c00c1d05859040420521200401c1303040078030103000c2a540050243c00c00000d0055000c40246800030030315420b040105034201c103004032016a9400c0808 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 75890676 1250 75889426 75889447
    0x22803060509180607030b01051602150c0f0d08041a04031211090f0d08070b100f03200409050a03050a0320030702120304080703140f0c0c0406060201150306020307090506 75
    0x240342001019042a100517a80e1000200d0813200f89000c8035010940c11311002080710480c810920304284068105014a180da401c0005035420100040708260700c060321220300c03c0c81c203004010203201c00d81003c91007400c240d0388966400d0100851f114100c45074200103810b1521074460709120441e40c0d04c0c00c0280b4640550b078681181e015584442c041c0016107072908250406001e200d0301c0d560410303062410044181d45180c60614050002c01c00203d0b191400f15103103100340080d10041d84078034404081c08846032162482e807003008c001544514030700002900802c20220301140c000394189001c690754522035a06800402c184412000864903a1110400c0059807500950084030590205c1e013804440d0600c5403d0392204807030050808006100b40700c00240141204150b03c0c2d11100424207045104c6000e10807900705814081150f0302c030f00c9000c02d10381003510030000640000c0c4000d11141a09004011044080384801041c5950000000d0b8a107441482000058a03004100b250303910450350 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 75891926 1250 75890676 75890701
    0x60303030501050d03021b060c0d030203040204050609060f042a090503100603030906050d090602030c070c090c02070512010207140601030b010e01120201121506050c010f022803060509 81
    0x46000c00e160500201c0caa03d800c48458126a0707040d401414070040000c841008032242020305900801c052028420b099000d000b059003004031640d00507240c1c50940108400d8030400303003025010340150014000a605d0303008074030742c8211041e2404600c100c1400442d5054081d030318803a9400c44551030250f03160039400410700084a80031821201098042d21881c01200e0329803100038085000c1c4c0d0020002180242c02a11000301a034100150300c24442d241e14090b42d000711150a1507600009440080101c4e51000c0c1003d030400d810108010441c41d40083e695100f13a001d101d104803c0e07031280444050b42501295191076015441e2401203c03000061a5540000e000856042d80359400105180f4180380c012030485140090500315952650015109035000040502a00d900c440186500d018424000740c0100803079501c0c0d40e59114021040ca086459000c1100c08aa00410000c03204000300182100d0004085101c0b0b6041c040d407060940081800e43d1103d600302d41001c040025a09025 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 75893176 1250 75891926 75891929
    0x1012030c06180b01050414040b130503180405070207080601230a090b10080601092d060f020c090105030705060903240709080a03020604170f0c07061106010608011404180606 76
    0x5443c40d08050b600e0b9030030003081d1000c3d8007400340030380780c50340c00280811061015030750083c0c0601d007a40340440b01500d1342415a44034803c0840910410405030301c031070a00f4403804d5486203491014008560809603060b80750b80c4103208140780f10303110440360916003d1510400c000840000c1c4003a0b030256844800390003a14001e10303650b218030728035901040e8482c0515070640c81060169116464541080c40c1d84081a5401c00300b46240e039451540c3c420550154080748001d014036458508204448520003480c00703140c100c2060048000000411041d100000d011059074001c40d10181c80b40a0200413a25180040001c0c0d00040f6801d14614481e200e05410540510819a42c00ca4000d4030381014559a90b25980f004005030300c031130009070210300d40c03282107c0e80b030107408903c600d04050800c100400380c00074409660690030920003007040c190001c050810301c69042c07000d80342e150714045001d0900034051068103001940c0c103110682c2a9a85d52013502000c50810074001d440038981000401060607 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 75894426 1250 75893176 75893183
    0x130b0d0b03120705030a0c1415040203070f06021b0d020a0609050f0411090127060207090e120a05070201020a0c09020712031b110109080a0203070605010504051012030c0618 76
    0x482d40002102006101240c0c03005800c4070041d0b1404001e46821a0008181c220a4445561442101d851450240981d0200b03103c10341d6101d0030340c1840c0c01010308001055025800788018508104041038000c6003540f484011450306c0400b800d906e101290510303440c1d40000b580b00e102c4c0c4001087d501d4100c00094203845c419519040da4044076801d0108031901e00307a040707101600c140011a01d56100b00345c0715480d0341d1030290b80c60b46486548401c035440106500441c007da0084901481040c2951080c0070103003101c0070080010b0581c0b0510706040d4410380749440100003000aa00c420359008000c610081c3e940001905100c0d90ba80142c5802908000345c215110380204408030385180c0b20703004031800110010481103500d0070101042d40c4d40c4880422080c1c803552255547c102144501002d0051400301f6006156a8441440c3c540c040321380c16002113200d036140009220351021000d0781a410b682d04805a442400704504080d1949440703900020000342c00c100d400202c07144500441040c0e50700c07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 75895676 1250 75894426 75894433
    0x302031305041a040902011e0905011101140f09030c120405010e0108010e180a0c08010b0a080703030c02060a051204080405131e02030402010c060507020102210f070302130b0d0b03 79
    0x80312000c20040e02d0f203000704418944254035500e4000d2925600c10005a881418800d01c0c841c190800d98036480d613804600400b1840c41c8004001e01d50300700c10207404e05543c01000b003103020340c0e21812901020000c0e0079180e00c1da00c2400042e0409d142001150f20518800f0110b40038014900d0314000320354441e01075a0f00207111200703a003840354024542c290690703230000d000d092140e0f5480d400c175028850086014400e403040c5c00b4070802260b0910b6884000d05580000803034060a03078011b11900708407030b500099540d40300b043c0801c0401d0307201002e0420b00d0b41c1103607815540c06040a0840d040e000d0403140c0b504c41c07100003051004201d0f280c4010012039509540034040011428a94001c440da961644002914681003149602c0700341d50055601c98814180310452540684031101100e600301c035188050303980003440e4a012500340c11a091004000c42c3c8101036460041008100f0203400380825050540109103540900300d0100a900503089800d001621520140001409030010642c0c05000e0701 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 75896926 1250 75895676 75895679
    0xf0615021c030b01170a0501060e241303051b03060108030c1e1606030b0f09070509090a060812030f0106030203010b160201020c060403050604020405070f0909050c0705070303020313 80
    0x600101d491035112040201c1d0140702074103420150003400d600d44001e070401c41101003100f001490f40d09154082c3da1405000904c035810709002401001022424510411850481c89912030520300e205000420a141d01c64407403940001c074a101a0440d00014004d000b0707000d1682c058808d1401400405070b003181220000d0741d0710305881e5101d1040200000243c2c1210340d410000300c449210486902c0d50443c1111705018080b48003400000b8980c1203480000d84880e200107040c5080c42103400740c21070455001c03406082008010f4028031550112500442c40c28000074413150751640441c2c020149001035500210945082d0003c40d032080300d441412000d000c0000c07903041d2103031007541e050b503c0d800b5030940341503043e90410560f0f190154080b81140700e501c4007400b803602e0300300c06480218828002040107081600c1000150b40c001801c1704104a042034070059510b91001c07000f81202e004000010306078454000110f142d100b0341c02c001c0c0c524030030f0328130000406500100402c412161810f008030090f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 75898176 1250 75896926 75896969
    0x11103010326040e190506030d0806060d020a0807030c020c011b11040608030703080f07021515060a0c060b040b090a090c0b0310030b0c0a020a08090402130e0a14010812070201020307060f06 83
    0x386c0003a01e0480d00f44d0b11180000508600418040da0484401801107050038903c0b080502641d104003500340006019200740540c69415014517000c1c00c00c28000341450200d00400202202100d44a14244080c0f041c44002030000810f1400c1c4994005413050107030545402e00356550b41e0003808101d0025078a400010529a8a4940c0c24000c1d4001d40c003805884c9036540015840c2603000d4151840303e54405020701d06580c0e820002d029022403501c8a17542148907080517400c0711541d81503580500c1c202084640f5035600c0c2070304240c1c018004c040002c1d01091609143d050b40619030004904d400f00041072003a00c242c56080403040b42c0c4101c001214680d202c2103000403a0040031741410141c0e0262541d4030005121030040d00c24110040c00040c146948028a054504069803228500c84164028860300781c1c12030251451180700c0800f01c11155240c2500c141c1d580210072810341000350041505821a882031048071003176500114203008104e424010034005009903c60714810f40d001072443c440c035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 75899282 1106 75898176 75898181
    0xc03060908130609050a09020331051614030d0e011d090a0501060f02010b0607060e071a030f25030b0a17010501050a08011103010326040e19 62
    0x130f1441c5c4410b00c58016001d0b00000703d030a004208001e1011000c440403012003418400302d0b8101c1c406c950709003115000360039005149004840e041c0e40501d0200300e0b814141c0748901c0403035400342442e00406a580540c40c40e010302180410401000c9980140c1001c004410300304071134401100f141d40020240c0500700d40185289940740014081d0701d5101e0304851401031980005c000034002c42000480f6030044410042603030741c40701a00761584c04d0900c0b0410052000141c0324213140c6401d24155240e4008944501c4407180c02e000052101e030b50300c251000d050b05445464040505a100110040d284081c4400e400290b4507900041e40828501c0342c5c001d070007400d000040c4950400c410072580c0500c3e944002107903030415400e500310060b044100c1e41100c0d030164a80301a400b20040a440074054200c00c504500404903001940c0030645080c1480317480e5500c124440c00c00030030740c0c0b03004 = true := by decide +kernel

theorem cover : BRFrame.Cov 75719426 75899282 := by
  have h0 := BRFrame.cov_init 75719426
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 75719426 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 75719426 ≤ n) (h2 : n < 75899282) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
