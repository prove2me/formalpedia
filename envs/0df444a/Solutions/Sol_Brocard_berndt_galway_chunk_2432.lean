-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2432
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:41:57.60961+00:00
-- url     : https://prove2.me/submissions/b69b3c6d-12f5-430b-b281-604c2184639f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 437230215 ≤ n < 437410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 437231465 1250 437230215 437230217
    0x117010e0703020403050a0c0915081504080903060c0405090a020a050d0e10110d0b030f0a0609021c0b04050f01020306060403061104030f0f05010f0b090103030c03140414090105120706 81
    0x4035000541e2544254103036400f9561200a403558800c0a05002c0d040402602855114a10f04002e01c0f0019401c4e0182c40d08072a58000601030701516041007801002000b4001e8500c4c46c0104111280c03903405103c0248076030224507200340c40b00d081c441440490000103000140f003510400003c40c40580120541d52107941d07482004c070b40047e61102d6981414420f405403d041400c006051080302c0284010300441c2e1600c0008010f0400d08008040e034134103856440e00d0aa800c851110404225283c010b00c0311240050219591403070b03001c900d444842c60600060f6012030001080c88100907081c04200c0e900d40c40300d4001c1d41181868400907095215500c00106000d5450a41c41c1b608048601510000c5070000010f200003003103820050002043c007903044400c1c0d481c0041040100a1500c12032003000d40103410301c10140c0c03d503601540c4a8956060a44c14080740c0742c910754041c03100d400207001500d10840700d5404600c40d1030074008a45810382243d481030f250340c031460107143c46c0012007600700d03466 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 437232715 1250 437231465 437231489
    0x1030b13120e0301110f1c1404110f09040507050103021c0c031401061d271008010e060f070818030c03030601270902091215060f011701 60
    0x480c441908000100c40c402032001c240111000c002940058a65203016070540080c050460904c5400c1014420048000314035131040c042046a8008800100e4000d203a2000020704034042e983e8011010204031003c80d99074040400440060515072441c1700c5820081ea14410581002e60382c141d01c0b49010f016043c10594045240d00e00000113102e0903600c40c8001030b041041c4045410018050300041403007074940d07141d070f03c000250184111540202d1401140c010180d014a030803c00c81002000c501d50950200d034074070b800118042414a060081085824414456190500e91b07401e4519892101c44035400a2040216000ca000500381e032107065071a186585a81e07201e41c2c804410001c40c202d44092001250a2018460000081d4090304090b01c0d000d002640e01070100600360b10a10300801e4489200800700400d6000390050074005c0d500600861000e4010020546046100c1c3c0300207041d898840d0a22800781000440403218503402e280081a000c40b105110913044018404c003400d450b0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 437233965 1250 437232715 437232721
    0xe091b091c1202060130060e0105130203061305032a19060b0a060c0215091302040f05191e0306060e07031b0f03050606090d0b1807060801030b 63
    0x180d615200d00c650030686500d141844142c0c102980344408180c40700025114400012034030610350b6111280c0440003000361164600c10460110324900022030484110380c84442c0c03030403032140a0003441e01c1003207090882c940e0700d20140100b501d0f1010160801c1031005062150b10041400401128003221080100983c184400c030138520316000303440c0d1407200b18054201c0ca13450035080c01c0383c0003a1503805500144003a1540f00208031090f06c41d0311461000c100380030302b070b0401420310740101c141207031500e000c041c145181000440d458440e118100c4d41384650014082c000c029880302d440c0c0c05000d0640d12404ac0da0803940b10040030408138026080d24252a8005002d104400c101040141d5804a41031007201c1d41d40214519084050380c80b10046030034000f615094141c0c02070882c900c2d170040d5030391042092104106170004e08020b020241c02610801c440070f89915655420903805108080f0040c070b0307142041c180c64480101c220000c0098125140c104807140e400946681929004410742030261 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 437235215 1250 437233965 437233969
    0x1e090b0d02190e07210c0f031e02031003020a081203130501020c01020f0301031a070f051614030a0f09080307020f032a1203120c09210d0e091b09 64
    0x40394080c441c10ba041400f00f0002651202e034161254a00c05040e403000c4145c2d58a01c0e050b40c01034103422000600075503030a0540352182c0c01000007002051411909810001d40d1242a0391046403084481c2004e568100b00714240040d40b0402448020041c2224441c8510408000d00c40609001c003401d4002860a0a000c0c00f0b6040710980541c400c0210747d01c02030b010360784445400900c001d84582c104501e20110010800d0b510b07511401c1940d50707000782c00c81c08220586154001d0000504042c585200700d40010300201c40054564003000e00071615508442c4000b40a101c1008000c4100318800e18204404000002982d00403a4111403080d610780c10100400d11b040041e6046042c1c80104090f440990001c9103040c441703d24094500c044180e00840c40e00340d40380b14214460b6600c44100e0300049003010880b02904118030001d24401015591904c40750002d1300710740034070302281c01811420340d09a030440e0240340000002e032000600c40ca800007100d4450314440e45101c03064000007030706120356 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 437236465 1250 437235215 437235259
    0x6090d1b030f111501030611030708040b15060705071a1309020313060203150102071d0612070b1201091b0c060f060f06080f1008070b130b041e090b0d02 67
    0x140007108a5000c01c8481030404c018007070a100035582e5503e441d0b005481203805000312032141c0f0003038403141744617121542d66621541c0010261841803155010f12491903562030000e2000d280564010440c450a0442c5074007084000f044070402503004200c03400002e4025685d6004440c8810320040c0c482da20909000c4070307001c00c0d5000404241c4000100b0807106414080c04030074080c06c0c0e007143c4c0b4040d12800d0f285564860411014400207100340014018501449102c212504640039a84550f68903406c2244507000000301001000560f0010301001426104000d079000c2c80f2141400244413a40003c0c10703007030404170050b0180e82c980c88207100000c041d4000d14014070303c8440754080702c5c0d038400000b030245009440c075803885401100072540b41c1581403404800e964008015140051070803c54600a6111901a8240c00d40a52000949402c1c21b80a400100040720001500032042800030381c20702410340201041c80c2c641941c1c0c00254540c940c001d156a039040e910810740c01500d1112200c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 437237715 1250 437236465 437236487
    0x204050603040818010e0109030b04020402070f0b040b15010f030c020a05071d010506041a030403110601060f08180c120307080301030317090109030f051c090506090d1b030f 76
    0x400e000005201c100300400c00202003007031888608803603540c201401118510b11038001e060000b4080d6070240007080c20070080d00d420a2004100603c0d00545568004104040130310646a540100d400c001c10710490401c4103038440044020b0b424880454400a040d8010104001040641d0303403000c0c0c051300b0b008100380c50141e034110f401c46094640e180100c0e4041003500d60f882c10035400c00e000006481c20b11406603802d407141050080d80e055801101103600c0c1d00002c00c2503041103000c5040b10306280307003445070b0780c0a4502c42c0d6a40c081c03002c0c00440640491342c0a0061507a4040240406001500c046484244000204c2d0324510041480860318076601940002404c0c1180c0040008200354119038102250644a01d11004981d41c1c0c150b000d088400b0080042d003c200380c1940812818440c8006100001018450f42036213014a01400e0445181000c125000e40c840760030b120082000308070307218031200180b800841410748a103030b000300c54440c500b0040c248600d506902255034040c1c000d040d5 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 437238965 1250 437237715 437237719
    0xe070f0b12041a280510090b13020705030901110a020109231203030702120a08040303090606080102070507140a230303070b0a0207030e040908030f04111201020913060e07050c01020405 81
    0xf8403030500300d0002e413101c04808a500b080c031000f090350102c40031250081901c601c0700c02502189032440d214160015010054010307900c032150203a40d0004812520144c880c4d00c4c000d400468031b4450798000503003008250802d801407030b1700c482950b90050f80d20441d18070585602e0203840418030f141d60b00d43c50f20480e4418045500911903103407528208000400381d4481c90072642203920b000d0318460448020310840c0c002d01d00161500c00020040390007a04914611403160070700040c65640c0d00e4685003280c00c0720074100c4068122040820104050001e04580c5072012680305888034501444081c02e54039500040342d0418081c1c40302c1e101503070280203841034241c018025444615090404400a505c03e0008502240e070802d46051242403d12403100c0703050380a09001e2031038484448040305140300a0044035105640100c10145844841032a050a0f003007030300160726090000c0c200144081c94040310b40b1000d241100800c20f0031500d1540301c1c0c01c100c05041031969206030f058148c0c00f80c4900d4101076 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 437240215 1250 437238965 437239013
    0xc03110412110f03030c03070605010609060f1b150507030c08100e04051e070f1e050424062a080708030403020f010c0e040c08160e01020c040c030e070f0b1204 70
    0x111400c06c01b00081c405035100d000100401d03070703c60000391085481806050005440c60304034220685c0106201c030440040721003d11084c000903501c102404881d410f043c80c10b01d031144144030110342c150180400754003290900141610b0322003683c0141242501c1410166403004000c2424002d00b031014a01d500701000c0c0140d40c01c004821110343d64270a52044441070079a42100050144201c6507815040c10b9103481000e00d85d152108000160041d00c001260a049045469001060100540c070052002d0384074028400c020000320032544400140d1072401c10460200180094417410441d03924035880303074049407a900c03181022882c0142508001805601c0c05000c10301c081c1d00442c0520002d4003c980501011221400c101c40d490740a42d201c280c1100364054150720607000c1c29401c044c81da0180b04464248100f440020182d90748210b0000c0031075950984840140002e10140b005041c1c0d03007410003e0946005a1060340d807089620801c2508491004101005804200100c0c1c50354400020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 437241465 1250 437240215 437240227
    0x906020309070f0819060c0e10030c02070602010b10180b1204060b0409021f02030f040e1503030f220924060906120c03021603030c03110412110f0303 66
    0x1d0b540c03441140541035201c44a180001040030000442c88040c45070410703d054004496580d2601620b0030060a80a01c007103224090415124111500d80c4142030344d60100e0070f08425280a42000b005130000c40840e4101840301d403403503d1300003001144c01c0c2240b0701140c3c000c1852420400c001d0184c0c1141c1c600c90000a29852281440e00c0010b001d28086e10b41003202203440403c010407140d500d1002034000d2b440382d901440c0021050040441006d23540140c0e4640520107081d400306030300035081120441c0044091000300c00203403664801d50308061740114a0001348c0031300c600f02402000c600001000010001c91646070200321030340c00620259000303001c004817405516040c21003c103115101040702410001d40c2d80e00c40d10211045988648448004100f01c40c14038010381010302014050540070410261615150146020068001c2d0340c009450482e1101c0102034450340001c00315054010b000c18442000d00801100c0542e0b8448044540c803194078001c207a0490303c0100040d4180004180 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 437242715 1250 437241465 437241481
    0x2190602030a0f053d08150907230a172a0a09021809011d0109050609071b020a0f031e050c120106051005040306050f01080c01030902010309060203 65
    0x60750040202c2c18040c860b5402c0525158101c43c411602c40d0b202138400d03450054520003201c0703801c1e16061034804804221055410208401003180d000009680c42481c1c04001428111540c40d0080c01c0d5001030086145482001d01840e0740000f50900400e00141c2c52580f2030f0388105100f4001c00407181c22520720784204400541341c00c9050b038080c0b20421000d0022807590345080491311895001450118400d0412507031000940100c1201036520120300144406680c40302c468500030310145900c050040450040c24800d07260680c4130243d2541040d0a000b41503451011075940402d161524540c8580c008240c14860914180003a4204805640c0401c03d440b54000100c1628000c40000100c0d49c0108104030106840d200c0141454014203180c0c002894000c0c120707503004038420300110340c0c9910b410005105d000080441c5000c1000018204200702d50b03030041d2948060311075015100f03985005000f58030788000d601910304040e0f603001c50100b16802540107a00b060340100c02107441e464000c2c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 437243965 1250 437242715 437242717
    0x20306010f0512010b0622030807080316051206010c081306020f010b01050705060a05040c0b040e07030b031b040f020c0a0c0302030c1512070e1c0b0c16080a02190602 73
    0x240b40c0120754202c0d10900c4a00140105240c0c1075000c0c1030b8501e0903070309140c0500610f013000421525500d00307882c0000412001005010030b54021f0550aa070303418605000d0000c2a09100e0035010f00c4000d000c084581008114520f51210702800c0c05002546545000c0059108d03800c80400340b00c00201c40854038950016885d61881c01810007003010320020b40c0192064082c1d941c008141c3c0d0302103c00a00030310603035084075801030f01c112899000315466814040c5540c0281d003280b14060814000c01c004640d1502602000c218154041e000c401001d450705251045000010360140d070312030103104c0d071029a0b03a0456140b011a502650010502440d203070183c4601888103030701c2803141d00c0403d501031420350114a07000071412400b52501008100d00c0048840c0207081e0b105001c024000d000d20b80c1c130b506900c043e00c0c0410140b050b01103440c82c5406409070401600000323425000b40701000304010b091050300c54560b00010300384d0301c4494004040340b90603c5000304ca4514104015880c00b0442550 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 437245215 1250 437243965 437243969
    0x3031b0c05101a1c051b0112060b070f080d06171606080106140418090203070605180105030604150303080f090a03090302060a140f070519230307020306010f 69
    0x1010796a10541d41e0b940700081d02d0707995440c0a001507144095425070700d03181c96800d03030441c455a1919143c801c00e481e004d00348220080303035840c000e524174024076084d039110465400c180c001030380c10890a41014410b00709401100001003419400749510b80901c44c102c2c040d261500085002400381d40d4a410740800108070f500c03103034140c0c0c0c400d40d8030100e65810700c2600401521304640e580d4036141c0c40d00c041242c01500281c1c43c018030305001c0002060b8039585c0294445040c03d400c0001c5500c201c1d07803040c186000f036640e01003010008184410080d07044800d50b115010602482c15a45a44030341c000070303004194021402c101171100000000c02c00d43c105148502c60300c280404848555140c4501503107604c008140200080c1c000001440145032420140220b0842480c0000d4003c00c0251030500b6540003001d80041c2800100e4a0b80410500700104215450000501810501d4030740c0c40408141c1031b400c031a4050682c251440c46801c408005491041d40c00500711641544d4071500109411198 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 437246465 1250 437245215 437245223
    0x13050106210902090601050304030c0c0b030612070302031b120109050a0c080601030b0c07061803030605030706050f0405040504051507090914040b07030c020102070c0801020a091d01030201050703031b0c 89
    0x24031500c54000704a480360b4005550043c0c00b80c4020b584200044800b548002c004500b4040c2c1112200003041101101801032700005603c540d580c1008820440700760f000c1903c00100741e11640f000d00050710702265094248030082c100080f0a4601d03000111541122502c60744258640b54aa4051042c005026554907000381080307401140c43c1d4000c41d8840c08240005040700781c564003c1400720624500510206010b0040002c2032105c0d0814401c03400c0f40b4407025800691203a0060005140c00d2040340c0080510303091003032801103d60507140c00b5010318820b041c41150f4420004041c04024403030070550301d5061601c00181c0c6030403600500144240e004015405160030b4544c200402c40d82111030040750400c55000e15585d41460031000340099404110840d502031100034005401058101d01030240c030000540c64107000c80009080140e030340d0100780801c410001c80340001030710062050540741c082c41c049541c0c030360a040540141404070703000740c00d10340c07441070880d405544106820041880703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 437247715 1250 437246465 437246507
    0x30906040611030f07050306130504050d02100204180b0402090d03030509061012020405040302070f0303030603201011031c020c0f01110901031d030301170d02121813050106 76
    0x382410000b1400200c400050b815048800f00b004203014202440c0c2c014402030490b1407412400751050242c4d1002c0ea8121402d0307103d440300504a0340c040c05908103d41c8048021410076281c01c607160a21405a201407490a580c0d0100050603255601105e40e1070030b0150410303c6081c0340346801001400104e90f2090030f80114000300340d10b01d090000e080308641010201602e0030219400f040000c00c1c0180c4120f081d486803400004d00342503101c507541d00035030007528005141c034918141003a10041c1d84c040e0070540c0d00e56901d00310043c1e0b1011400c0405c0a0186401c05543c01c00d01b45062a601c6091158200007045400d02440140c00b42c00400300140b515007540ca00d8041500c1c0d91382603400761100840504020b000d03801c00c6503caa4003128110640e0b01301d104004407a254001d06560080e0402040103190490051070000200209403d4102510003040740740e00e0f29810303100500a1606080501032a4501d00030310769248518480340440501003041a07507940c0704090155207504c00e05c084107800c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 437248965 1250 437247715 437247731
    0x604020f0313060f060506090f040603060c1709010c08070f0212030c0913060302060d0e010603020603090f0f03030601020709020a02030903070906060201060e04050a08070f1a0103020a23040e070503030309060406 93
    0x135182c0240000c803900686400d0a1640e0b9608014000505401c125003165890781c00101003074081c000d09600c15156251595102c4107850400c2e0031207402803031000c060781002c0311450890f50007404541e03c00000d1801101c0d803000c0450483c1802c810380c8101a0310240413082c0036203e14204008d01442c40210f40029120302e00100c1401584d00b1031101a521200070b008141038074903a0f0b0454060032480b08000164107480f50b00141803030b041600c0c5000c00d9440241c46110041007004102c3c1024203840096003585010300000b566844507000d0390310352a0b00803801c110f10324001c001b44c95029500406450940d41c0382c0e4880310050200d4800c02006600b4604001035108200409900584e006400b501e1030700e280c1c1d02d41100507444540b04981c0c0300070000410021480c004d1440307581b070211035219021940345004010a009441e0030144145c2d1903070550b440d8014101c03030344440c8100300751800700701c00900d0302e500c1c0e007800d6039540b081d60503000000c1000050701020605174800c61150b50704011001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 437250215 1250 437248965 437248991
    0xc0b0c2104181b121503110405060108151e0d0b0f0703020c070e04110607051b0906091519180608030705030409470603060d0201080604020f031306 65
    0x142e040c100032100e030401c0c83c10328001e00344195940c0d01403141341075001c0b8402107000d001070700c20010750740b081c1c8000486410b00d140c0c07882c1901440380c118000b40f038125070505005132004805c50420b407602d4820000702d0b00c000713920706003000341802124000b40041816042c87c2412014110304a07202031041c1d0b104000601c00da4003d10923200c5010042c0001c02180b420b19400e00b581d40000707002920100c0502811800f5559120018103040d48108050030303200701c558401c0d040301840020724a1141c1583c1d410040e050b142e002c80315901010100402e0404686e10000c0b45841d0290044122001258200850300c3d4009010480c00e29500d04c50811075960344025050300c0f030003a401d006040e50010001001120001d81080d0351f03c0a0444485d40e0103025004c413190344c080c105001802c4004098120342e2150b181c8040768844840558446d451032520400142d801440b524000381401944800b150454070343e9419205c2c14003c00d052541d0328200754401105c0303152614011104030f4141a03a00c00a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 437251465 1250 437250215 437250221
    0x9020429011106070210090c0807170d0203030403141c02030a02040311060f070b1503071503140f0601202b140a03090f020405100519030c0b0c210418 66
    0x655856001d45100311742a100d44000e051001800c0e44c848409080c003140009c424040746004003115140c5802c888070000d8020309004210f89080299082442080042500310030500d00c4441c00e0b414060762940314880c207410101c428420600c2c0c0364130100800403031007840c0d401441900d01136010300c2c5103006148204021441041ea858464810070300070140051030b194082c94000d0501c2c102d0499050780c40020a1811489500008200322150000f200d00c542502c61803039072152000a0800303034580842e02110500019060604000d0031150400a0305d602d100d401c0c2c200801c90b030030360750f11440c4032400d00011424401000c01c031201034198402564080e1089100d03000e2a0140c4500780100d003a420b81c01400c401d039007950004c2854414200580d55032281c107105036a0080600c510728242003d10208141d0006052100000d42c641840854001d00d101c000719031540e0f83e02a95042014001c030b0400b9085113008102125a9210049039400740c00503000380c034009104007c08050079401442a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 437252715 1250 437251465 437251471
    0x111b0a0b100815090c240d020d110304050c0f010201020919170303360d030c020606030703020d080a031b0203090f101709071d010807150206070309020429011106 71
    0xea884480300c03868a0500d128406c808021840c0070410b54010070100155a501050020210540c0060301d810700400a02c62001c1d2040443c001505501d030980d075140c0d50740344013840c0d82d01c52034502c5410380b0f040e8402d4044800d000e2021f40040c5007a4440b060381400441a40507001041e0425030410070b5403080041a039204450030750754694006c1900c661404142c0c0b0144091410303550384c0ba80c641c2101010007001503004001d58001035041d0658100a08081000e0300d03107071290b00700d1a01040581d9480900350003035604109a540d45022582d01034005003098440c031803c0b16505200903d003d50080040c05c0d65030b6080c0c0c1c1c6101101c12103010003903030306020003242000c40c1c001d4510030301621011081da5800441c0100702c0d41659103d402c01d0082030188081c01c040d0618400c014089103105100001c000c18040e01c01442c04d62203140003035141c04009106508040e80e9540b22401e540c0c40e6040700b070002000d054039200d00003c40d00729010070400c000c01203001c100c4440d10640c41540018000b84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 437253965 1250 437252715 437252731
    0x10507031e050c0409090b040b28020d020403060c0507060c18030311010902040e0c0a1d06090a1b03020304020f030a051c05040503061f09111b0a0b100815 68
    0x10508405081c103002440054000c401e940d00500000c214201d092003078402290250101e12080e2402c1d00d00314000c502d0080204024120200304a0400220b04004c6144000100400343c1c5441031200c3c00d0000340070315403000c0c12140c10f1907c0c52490540010090040c54050320041c080c0f98140c2c40280c1e07541c00c03c19580680e9401031031080012030300c549885003c00c0321090006c02c90a4030760b0000703001e8810b07144c1e00380e00c1c54022000b0005186480c524001c014260f8551403040740034403181015003220300a1a841c0500d0400e400154605103e80c0450b20555000b04075000c5482d071301034020f000f904119005ca000c0d10100c07a511282c0d00d0002800491203500800070541081001600311502075480c01000501c00103000101d090707507043c0207151207250b800144a07007400701c402d074940c00d0328042d51101110a01e400400784e81482850308440a04100001612900c00422001442d0036241c54025000030500070034054000142d0103114201c500603000c03118148003030868040c101c2c1050707444032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 437255215 1250 437253965 437254001
    0xa2105070f05090f0114090a03080a030f09020a1e0f080312150a03030e060909090303220b0f270609070b0a050d09020a03051b0310140a0f022a01050703 67
    0x3c2c01c0c540c850132040385c26440ba03801b903606005c4903030045401c11226820072102000b001c44c1d101078140e0315104804444400034030034000d840381600401c039070b05500d01a40c9070f4100d900c0c11500c01c2e402c4020301030004000348a01d0010140d82da00c5102e07202c0d0040c800c85d0b000c41e2030000c003064840003d10b4000501c1c10001704002a043e19545d800d0f1926011407005a810200901102003a540d80103540d9105585038000781d0364a2a001480084400401070403610420b402c1c0084800708490001c2607503c4070102c0c00d21651512510402e400b5100360340280c0302c8442000c15402c03080d80c40402c4490003000c02c10100c0e4070058580d44041030a0203107000410001d681403100c10708419860301300401407800600052042505d07a2940703030803c81d040505822404c0001640c1810342403c00c191606890060b004008080f06103242d043c09450160004d40c1c0705842d4811881843c1c10b40e81183c40e0003101820b8444011034240143d11519910000c0d6a0b09528140000d280e840c0240950681c09060308090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 437256465 1250 437255215 437255239
    0x11410050a0f020c041812030612060528090c0608010612020d0f0203161101060f090b01020c03010513031218031107030803150918120a2105070f0509 66
    0x2c4030405001c400b80402c500c6503a10713803140760300c80c1d200705080348403004c00c1010501c081781003c40c02101603840301810189007100c20415401d24242c4564a90b510000225030f6440300400e600e068065400815003410b00580034045201d15503105001061040c00300814241d92400b043d20704040074416100130a840b054500c501d4100c41d802003641002c2d1210002d01240c2d1804602c049030011100040d50b030018040c004025138100c141c010401054400078490581002c80e145030b41201441049540d0f5100c403801281c4d81c5c001d01402d102c0721401f400803c214580080b034642444090700080c2d0104000c40c10012511405002c2c1610160f80764000800014281e681150055510318800300c1501807440701100003010280218000c1d0590b541c5007002d60031400400001c6400075000700d0071212460603284036810042000b0840d0f03000002d239585c179409480410b84280d00d041804549541407141c002050315050392209026049554806003003c06104003070341c0720300c81c1c902c016900100c05442d03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 437257715 1250 437256465 437256467
    0x30f0601062304030501060f0b0403020d35180f150a0903051218040e070306050604020c1212180303060907030f020a020a0203010b0a0e0606090a03020d0b011410050a 73
    0x451080c54210344504541c2ea078085003001e416081030b04100c03000e0f5180c60741081301d42e072a13603811009050300c45140c1c0e03d010f145070300050f412203180e03030011300705461034003401401e544403d240582d409c1204c4e100e170141452219031584541c000c2030341140d071a280f40d50704c545a0030005270850520001501c0051050190302a0701d0340307a00000342c45002c119003d400440000d034207014452070302c840705c0020340e1241140745840880c0741501d4000d1340158a000e40f4230441ca00c00160708000c0b80d170001400180d0752030303610108020384100c41c1402498800c2c801c01800411324940281500f9101900710812a00c81076001c00c2c1701c0d1220100d40d0b20552007440498441e16040b00c8450b00b0040600340001c640761041c0d160f030140e0700651050800f60f040078660205505003805203a440500c100c60200c02941003008003d8031500282c070260240ea40841c414082d521000c0030817001d0350b0010402d01191440780f0b084440d2040034020380030001c90710309034001c540c00e043c20442280400ba0b11120705004054030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 437258965 1250 437257715 437257727
    0xd0c022b140c0307030506072c13020c1501090f05070c0303020f16030203091513030809031204030f1103120d0c030914033f100929030f060106 63
    0x1070510303080d0041000011599901300a4000214807403006082186054140940f81380013190300900c2c0d4403001c01c1025455919259003141c0c01c203084402d1305200706201646070090091031680541445240c1c0d07580b1112848000041c120b035444c410902c03440810749000816a0801d580d01e1020603a80c2003044c0001e0701a8000c6c05000c0c41c4008001d00f000d1200300d1a404200060b032094001d40c0000a05680381d0a2201541c00400f0004045a14041500c109101d000c1514440a00841404144c0c40047d54052005541981d021400382c0d03102d50b201d0411110028041da41100c0503001480461028100800c9411550803002121400c00e4017900c1048098001d80034950205581c50302c4000008081e84001002d1412200045851b28000901c1350862079100c80c4440444444040c84028105104025000076403514540c4165071113821201c00d90031899080682144e050101c1002c0000d281e400e1214001c6142502c5110765403800289a00e549440d88150425006040103100c41c5000708 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 437260215 1250 437258965 437258993
    0x10507080a2604030f08011a0c0a060204080c0a0e010e060108041401111309050c1b030d0c020a060501060e240409150509060316031203020702030d0c022b 68
    0x400c02c111104141140c1101d44260480208003405840c4240418194448038868014049051041c019414118030a0003069100180d0350710300701c00a0034050366803040c000d003c000b40d8001c109545941c2c9425240341c40d10b00c180980e5016210768400016000c555807030341c0d4101c415a20071001c203601c039a00115207000d40180155200d0079040080042035109100d0508002c1005280139180c05200710b0080c001080d581c8003004150821042c01440ba20500848450300102c5030034000900c4024140ca096003c0c181444002900c1c0003112801d054011400d480c890744928820086a80c8800c419907040f8660003c280d007000003030700d48251000328000c184480c4c40e02500864281565072914a00740d0701010340503441c01341503000801150070107000e101c1e00250100c028200d029925044c41d07107503c400c1c0c440582590082e00128846502070390403100e5080d00a02904e07a50000003401403d00b80001c1c03002c0740500c1421002070b120340c02040b10280d8a203a01206807500c0c4c21a0388441c0001100c003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 437261465 1250 437260215 437260217
    0x80c060703081b0c0609010605190506030a0926030105010f031a01120618020c0f0f030703050a090302090a150e070e090a153206040510020a020a17010b030c010507080a 74
    0x800110b13181c80c8041101511441c061400480e44a04200a00500d01809120301255503100b01d403c0c1711070303920401078a5214000c0800000c068045041c080040e10f0060b8180b00030903403440044540821000080d4141c0e50280ca0319110b5500d1114101c0c00c44180e9940d150020070b610903131440541c031400340303005040d0880c00081420741d160341e00300072400c0c4452814a0081c3d400a40d02c2036103e424050f041c1c112050b08085c02c0b104030107241c00350300d91154000040030800b002a68034001c0c0d004240b54030203940c000d0042d803541d1900302503204c020803413001030b161a100b6180001a41d03005c2a5002c0c0c0c851515a928640c21502c0c00040c070a05a00241c50340c81c0070b50705c9510740d6001ca400d18014200904020107103481c83c0c40c00101d10440440e400311801c21060004560030070f1078032101e048030101c520580b800b05151000440803802d0500041000358040804a000210880142a42944042e01d10000c000280c007140805658240d001c5040340812000c0c002e48020959141c05440d6041003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 437262715 1250 437261465 437261467
    0x318020a1701110a030c030b0405060102030a080a11070303090203100506240f030c1b0a2414270a17031305030a0201021806070b060f030a020301060f080c060703081b 73
    0x7000d007422660441300031319001030303900d012000000b40d140c01743c40b4444a0030365040184c2e0420200003920780c8581e1600340140305021b008140701c1817441e4801444c5007405448252600f03000c1c6070003000751908a03c02e900c20b11403c10380300d210b8419442818006e0100802ca03030040042c084003200c07540c450150f840010703201440003140d87e50100303000b103114120311401941c2d41c0c014020203003001e0035654021101540203029520008141c28500f4200d4081d4006a01ca420250300d40d210240044ca44000300815072a401e11201c0d20b2500e807030712411071484070060000d1214180b0540d88282150340603010f00c0590b0300340c42e4141c000a00a58101d209204200f0480d480b540314070785103034410320040d00142c1d80003e45860319020035404900b4504101c80052800d5110340b140e040303411001d04054031401c3d011490343d03c2c40e42e040151858456025000780403043d41c8130050084240c080c4516221b900590f181045103103419001c9481203641912120450340300c0406070f401c5008202102031000030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 437263965 1250 437262715 437262731
    0xe010e091e0106170a14030a021209040905031b2a0913050a0b31021318060b0f100c030c0309030602030f18030415140d05070801060318020a1701 64
    0x108028801e4866800c0c40c00403c1c58510910709403004486c002c610030982d40040c0325184441c2e9000c20756a4001d442c1c44003090b1075042d5500020020b2494001c000c001d484000781000b03815448400313902d4082e00040584441454507001c1550031203440b400ca07581d425036200c082070140780021015400c031580740c0d01c0048098982d6200c80c50701542440694015032000104010301302c2c0c842d851030a00380c4035100d4040382a0504904080c000412400034030401c0c0324801d60000e00920350280451005a984103402d040c0b103800c10800814070403206034007555050b1091103850401c0b00c0405d040c14255501e6580c11005910300310741c0301042c41c000302c3c1040158a00000491464005180680485c80110041c0c0c02c00384d810544400786000e0030410354105000c10020031000e10130b402c0c50010306040c502848001c0f00da0f4003d0360710405101400311842c09003031180c09540064914161000381d107003000700b0244400450f00e92041410025441283c07000b0500c22000301141164400e0601800410035003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 437265215 1250 437263965 437263979
    0x90504060b1e1e071506030b01030f2a06021501030803130c0902030f01050108100308040611010906020a02161707140f0306010602010506030c011d01050705030705070801060e010e091e0106 83
    0x1110031010030092040c08100354050103041c4400360917900b55540100440c510b1075580340d9a550051101500c2030010980520a200c6d80200e2804901c1050b2103000c0000d6503500940a104582e00601c001441000300c20300d28503110a0743c0505076030304091442d065540301c9600d003520070242c060448a05418070300c0043c0c121040e001850040f003442c900c3c100b00390305010005042c15001006481c0e00d540b003c0040001c200004200e400b0749219160900d0900512402c090140c40c0001004100910004140300c480d5800b0950f00e4996858031000c41d6820355609145e440344001c0000c16045400140080045000c240031901821202a1003101d00070011400039080080980c0400c000d0b035102c20401c05140340501001c45190001d090015418030b2920700908847e40e07800d030b00d81c14441c00241d007005000c02041542e4209600004444d021902d481d551030182c0201d10900f4071080c40c1030004035200c0602c02085126500110040c0140340c1c086c99150881c0c4071024848460355614400440d6170 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 437266465 1250 437265215 437265247
    0x6010515040b0a0e1203030402130f14100303091e06120902180703050a021201090507020c0306040c0e070c021003050a1803020f15010602150603100c020d090504060b1e 74
    0x2044444e1a007088401e0090184030801464608444098008004200059540c00856004c103c00c44900007901406444100000c140b03890f41100e50000607030030054062030700d02050060b80d2096035034842060b580c4403540045500420790150706d00c0150001d00c00580301c1c8540300503031b9002040104001610703401003841046000e0303000b14181600b02c100400b13260036004440e0000c0805c83c0840c07820b8501c00428045c0c3c2018002d2109142e121000304181034030820407040f40680003003ea0702c090030646030408145d040c0e4401d0a07240e0110a00080c0312500441425801f0740d00030302250401030712301d01c0807070017003600600000c1c2450344d41000061090300c9220008000d80310742c0051038105004e0408910340f00034400021980d01c0c10200520049034040b421003490030b01449a02010707100d0500103401c1c8031910340c0342803e1034038000100642c075500140800000c01507442ea90200f0351644140410340342a0700400d004441c0070001502034503104401180c030b020240e00c0890a01c1d803ea1814189 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 437267715 1250 437266465 437266477
    0x61a1207021903031b0503070e061c0507121b05120714040602101113061209060c080f06040504050303150f0a1508010803070201080a0b130e100c030e06010515040b 72
    0x80d56451564240404403030141810707464508191f070440c40c0a090090820082d8000240900400b00d46241041c040200d503142c0301ca04103806000c2d13442d04400040040c0c4500301d00403211828000040b180e04500c40b01041c40140c41da440501e889640e1006100540001d01800c04001030040c0300d0511014602c00381001e0201c40d400340221160701103c2074242ca90984041c00388483c10031141410f040504155030461300c06042145a14000c4030300c4070300821507801d01911040c184445115099401840c8032310500004032442815295001880300b01e03001160000c215a00130030100300364840242d4040d146440c02003202e02c41e4542d110120340300d240a035001c12500203500d04171740001604540910302400f904402982840516000200000000f428100801d60703502c03d40850f9440301603100000d9002840709020346a04054900e60b00c0034030321880c0004514000c220f91059100f4066076010005640c0100b0150742407204010014401c00340400300d101e010403001030500e20b41405041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 437268965 1250 437267715 437267717
    0x3030b010c0212030c070801061809020312070c03020117090a0b0c13090e012708031314070306050c0705060c0c030c0607180f08030a080c09030a0602090301061a1207021903 76
    0x1456004408101c0d1074a00c3da90840b07c80e40e41001400c0c4000b52841c20107141d0100700d0f01000c1081c0b2007500100c1d0401080032100d1070400e0300099080c041c0040b00741c007031044901c00c0c0d0320300441c690f2420211883e003401340c2c5d02c01d260b44c000585480c0401d004404407900302d21810f60b00d502c4c0040081824a010b85117a21020315642c90341c41141900c0d0003032050203280440300291819114005200280c0924000002082080c0100c00b02e841c0781c0715117001e100179641c4030401e00d015540081c081342d5258150f02c02101c50600b440e0000320076121017001d48101541c401c000382803603140d9000c0c2e074200d0342110394040b54510040c422000b003a401009894002e84281d1144d60800700103003094107540d071040d00075449001b02c82d4420090800c0c00011503013100c04030300c3c0c41c6215031030301d0305418000d103d180c01596041c8a00c46d03150050080e01d900514600000710002c00c0020f41d140121355040300ca8500011f49480d06000c462a00510000043c0d1b000d460b910581301140d00340e050000d0903081524043e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 437270215 1250 437268965 437268967
    0x609060b2101060b0f12151002210412030507150213030b09071809020d02100e0a0905060307030f03052b0f060b0d0f150e060a0b040e0403030b010c021203 68
    0x2001c440081c4200c20151103900c0c40300c1c1c609401d428900d6168490b280c0005024101d100003d40c07480e803401d401c22500d01c4001d1880502242030031000703503134084030020144104512056803002d200305c88101e404803100503031680c4e8000c40781c1c2c82c162070300e4014107c165010740301c4a444500103c0e191000f015103002001c09030380840e0a604050702d00f030000500e0021540d00ca80d006120200c00506001c0348030880c4000403030740d0801131000c507002e0032a540009402c281060038031b184080e00207a440d03058103020745800c0846651907a084054074801d403030b62500758100c1d49090000c19000d07501490f10300d0080c2041498110200b0383d10440329158220000c2c042540039019411420078010080c051040210503c900d41c10001d010405104024105104654515034031000c40082d4020010a212100e6541c818568401c4c8404210b43c045680301c1c030802e001030000c0f90054400e02580c0c20f903411030301c5c02d58a513034455500783c0052031405900c50500c0350507031142005035a1102c28003949000c1d50095 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 437271465 1250 437270215 437270269
    0x6070c0e0c12010e0c0d0903120f0501170c090402100c08030a050f070806011d01090b040906030302070b031005130209030a0f050d0c110607230c1e0d0609060b 70
    0x20480190040c0c004c00b60324981002030100000e072000942c0c040301c1c200348001905002500d03064400301e41da407610048081c100941d594020005601c018101d0740300c908410426a40125210b40341c4011a00306584400c50308080f50160410003142e6144400701e05101d52401216141e0341d485803c11a110359880c0d8a82040003903c401d880143c507003100050410042c5400e1400000e000180c0c0d01c8640181310a136000c030350803181e20805002c0d000341a090081580d82d901c0328111400b6001c2404203078090b1241000c0050510340d0003040300c0c4100c0344d250b00c1c01405030170102004cd5075441e81c1c0c040c40b0365540912407111165030510401400750311620100c008107046180c03240c10180c00c50034030403d0040c038481c0140840d240765a0440d00c3c0d441250019614016454001c03aa8144130a89002103042c43c0000c0c0d040c0c1000080c0e01c0da5100c0103d45c44c0100c80f0b1000c03074209801a8103604550040c001820410002d03105400c420b010034814071000c00c1c100d94400c041804503506074a800301d045403030a51 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 437272715 1250 437271465 437271487
    0x180b072a0f051903120804050c060408160509041205090f040c020d0305060406080a0f0c0306090b010603110306010e01030b0a0911071b0602060414070305030a050c19020f06070c0e0c 80
    0x701c1d02c829189540348541c5103135488003030344c14002804060510442d0400642001800d000c0200c0c045801060542c4458495001c40d54031814404032f8892a501c40f031002c41c0742e00c1e1003140240300d20345c0320b8610f800b407807142134080b42c00c2e810122159400103103e83c5005850b641c2c038003840d0501d8001d0f90041900710f840610044c20f840000c0c0c81d140c0110315080060207515800b081d100d850541080210b0140005803030042540e404944c806480305141141d1a010084001500360491701030b680c017405001e44000c85401e5512041d1003290100c0c1613013103140c0c099400b0303802031840580b0080012444560310101d40080d40c203003140380c149900000607004208591240140d0700040002034641d00a4180203000c0c0d52180302030006080426214800144603d0401084024591041c103403525070400d070300003405d07030780051102d46014040c814140000c0d10100e0b41c03c1c590290014581c0c81661000b00c00e010707865201075800e90b001c5000c020041203c0c001580140d01a1000300714584e618030b50541 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 437273965 1250 437272715 437272729
    0x103050a0b0609060a0504030c0e160306060e120a12030e07060806090103060509100911210703060515030601080d1b0c0506030c2701180b072a0f05 65
    0x2044031032051034600e10311140c0c1c80d03000030b4514210f800c2e540190345580d54031040d141030107613502c02840c2c0c40b000300c0085000040c00180a0060084000c0401e9035444810243c1c1500c62a000380b1000840d01c0032070580e00c0c5041064031010300d03103540c01d9800c80f042039110740960007840c0d2280b10101e40c48603c9462509010030600d00206074901d010660390610800080103204d040c803014003007546070400b041139041c003803142c0c1c000c8180b08038041060041a10f810901c41950140315403042c8403040101e20081c44034000e14440b04105800f0f003800600350b80e00c0380300400000d440744100c1041c6408441d4540c070108090b40c0030344a1400103040c22003a03150000c2042c1409011440c0c4c01940303144190015905550320402c0d0b80c0e00f20f0741c06440b55906822205c1030700522400d061740708070b220340d40c0c2080c051000003901000c1d4281d803040c0a1203209800c001d104110740c0f08600318480b0822082001c100203c850410603c00500e100c280d0784480c41ca00a00d200040d0484404031120420401680c90261 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 437275215 1250 437273965 437273971
    0x17010504140a02030627040215040e07031104081f0f021303080a02011e0e1002031b18060f0301080d021c080907030c0b07061d0606010c030c0b04080306010305 70
    0x4400384040030020106111040d0040c14101c0769940200205d425503035049240c20900c000e24003180a1510070896601181500741d80c03d03402003004108d040d01342c826007001c4405030780d48941071211503191361780110010a2450b101c540c0c20300c2c01b408003103182c98043c411900342c607058540014049900d40000d0007120181041c03038095520401001c41107600c2002d280003100c1d001031480d911282010b078141d02410b1200a5007003076178000e04008402c8241c9a10103800520300108546188040710f090030221b100c25960610021141001035030f005a84500510360545e445c4000c0f400c002850010601c10b802088a2600540010006004a10080005080d1540540700904170301507102c039001c0d102e0410654000030000341600007140800f0400022006541c0002c49088095444560905d19040380c5400c490885c1444884058441940a41d40305501104c020f00200e440e410015684003503900011024040403a10b039401203408903c140d44207502600c0c6139696441e0190004003121030003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 437276465 1250 437275215 437275219
    0x160317090a05090a150e01140909060c0d090501020f070302060f1312030b031e010e070b0d0e1009080306011b030207060e04060f080a0b1e150103020c0d170105 70
    0x24444030129695a54411046074020740750103100c4d0715080e03444000f400c0c03200000c0c00c0a2201600002d01034000104040c100c4150301c10141060080104002c82000191428282d540c0140e01003a000c1c6c80b044000c06000360110030014000569956031800d81e0400704400c5904240070a00500745501841140c0d4042d80c80c8200c40300d43c1c90702040c500b003060100319000e001d0100c620321290409000354030290710410024119000a00c1c0c114145a040504549942c029406c2603224415a400060100180c5803025541801c05840b05e000400514104080d00800d201c0c103c1c800801424a100b03500c4143e01510406075203280c40c20001d002c404c0003d01c1d40304111040c00c0310101082d404140315041d61130925016018842d8900003030090316258100c451648100c08001a16100c0003c41c03e11a600c522b41000056440e51200d9404840b40422414031241ca24000b860340748020202008d0142c05042c01401d100c0f490b0f289510388044224000c01151031400c41c440c020a00700c00003801070100f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 437277715 1250 437276465 437276467
    0x1f091b090b030c0703030207230d120608060105130b150304120804120804051f05090615030a0b0712110a08060f060d0b0d12090e13080a050d0b03160317 67
    0x9403041c00c030540f154440245c105039011919004004100d141c082c98110501e030890f07200300e43d800c00d0944a10708000700f80301007a03c605c0711890081884c09564116403103103003d0f000f2a0702c0c100c144200120f02c0710010b221a5618100400e80d0313515190b00d008810210f2002649a28251a0100b550348098909009015400042100040b00030a131180d20082c5840c0902c100c0d1a940350052030701000701c500c450070100e001100008240998080c034230440700902100c00c1d98a444041a0110350464000c0703805d42c0110031b00c500421400d03a05150419054500781151202c0144041c04480134080e012005000010300b80c1f8441350311181840d00b0140448101c0142d00d031703a10003d1418440d013120011a2902c40e0080d065503503801c112000c5482c0c000284445910350104020b1901900303000b0540b090802402044c851f00348101605c04650f07000320001d107890850401607845420204c0c0d04c000300350b190700d030840d501d490034080000d583c40b540180c2020b8a01354030b00030714885101c00c80c2640b1810 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 437278965 1250 437277715 437277721
    0x30306050f0a1e0e01120c090501030201020309012006070c02100f0806040c110f0303012d0b0c24061c05102703020604140a03081f091b090b03 63
    0x2849501c6101283c1a00400c00590410345500c601aa14035070f010fa14000d001a000095803001d00c1c4201c2401c40c490904c0104c440e40f64940d520403144d01707020290040e030040c44502c000354090b4542c20032030801c454080a034071414180e1540340020845401000440c04280c103000c40c00e080c000852040410305040004403440c0d04010f012180043c070042c441c0b80c88105c6824800e0140d80520340c007481c0d50003a58a00601480242c2d134071f0340284240d04a9030b158003032082c1c40d40c500306e11a1003c480c2d2031262035500ca01d070008048040d00510140603003401101c0c24845030314050b1000103448044cc880419540ca00f0900b04004e054440f80403c4001440009610020b0404a064102c0c0ca1078200005004007140c490720041180488480b0403102040d0107110600d900000c2c1c0c24030603442140d2640e80e64042c100d074107131900e081400050116141d180810303803180c41c02800c11640c000c0701045100c0c1682e2001a038003616410050508a03040c008a203d00e001e50140c5850050314203001160b2840c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 437280215 1250 437278965 437278969
    0x80a03020c132d060902070f050c030321060f091017030406140307170c0d05010b0a0f0309150207140f160b0a2d030c0f0207030f020301020f0a050304030306050f 71
    0x34403c41520741e80c048101c540415030798042d400b082c058002e60004540340d4650746480b5035140c0f12150305407154801c0e14071401003443c0020858171288031180500c90450410911001e43c000701801c0c0c1e96008042e42110341d21030b160325019070710502044400004013460300c1050148004401c0006001d5041000188150764001c401707402040310305000b60f5583d5645150032030b0820700e41500c130500100e032a03041c000c20b140041c015001c086c1c0300440810280c0d0ba60500c440051043c0200a80030940f03c0c202c99001c0b50095201410043c0a074034200600c141c4041418205d90100e41c003202c90360724489030b48035072210030480d04210021840003004400c4465980c40a04100c81c41422000500044c90000b081e21405500d4200340300768981094400d200c1c030800d201424041c60100001c3d00e8a010000007500c144a20003e0400c247c0142c0411f40c15034440c158495125001a60599001c000c060b460084540c001d26204030544c5c0c1e0070340c407802c007480c00409885196110510400340100819816 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 437281465 1250 437280215 437280251
    0x1115040611030c0304081b01030515090907170706090b0c0319020f01021308060703050f070e043b0102031b0c1905010b0f03070f090b0109080a03020c13 67
    0x380d0041d08214800948441c0d2032442c1d4403528026a246010100c0c000550800000d42200e03282d407406000c0034030801d01401102282c6048408168981d4080351400a9040c05200317640c00c445400c05845107070b138446643c0c0761501c00d0340f65560341603030200c8400c201c80c0ea4085a08006041002c0025140800704a030481da61f025410004c0c0e100c0c80c82c0b5010303091040c001c101075084240c0e02c0c80203548541c441390180641680c240f0400400d80a2900051500c42c840d210396445010185170388070054a507020119410480e560400e40c0140d901d2224041e0100108211145e02410b01d02c2e028401c90011307070804280c2000140207c41ea8014810b0020015044c075070305281c041a81c0340c054030359543e0309407030b1b1405c20141d401034800015000036100b4131006400107200390300103840c400d94200c0901c0a056503007203a0f00c100420240d089005020021068000ca900d003003051511901d2244c441188078181b9019003412005071740078080c04501410003502c03803100f1790079904d802c01c007042c1c0050105180e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 437282715 1250 437281465 437281469
    0xb12030904230106021b03030a0c1101030f05130218130209042406080d0e01120b010507050d03020901020105130b040221010c03050411040204080a0602070c031e111504 74
    0x4260b0b10b60300200c46803480340e210703004421504001c1204659460101a4503041840c1c4845410303402c0c0e610004840c00c000044420171105582d0704040c4080a44a2002020700726044504040d1240192464070b100c5014550284e58501c00c604011a071510410186503107003081c00c84142080300801580150740c2a44078091501915440da49039110300d032201c022082071100140c00c80022600219036020703a031002c4255007440c411a00c40705000c2409a407a61408070440e0700040400d03c0702c5040707132580d402150309080c041c104103060100d5139840c0c0b400c0070700c00c148103000254040b9000d5111360b0309001e02ca401600301003600704808059140c0c105940401407002c0d015041120480f004400b03101c008103c9080814004c0090111a09009000d417600b030710150384068074050b271007031185498821501240e103220000c103010a0306030b4482010790070941058481c203090300c40000c04980004000c000c1c0b2a40da0010ba18404428944416000488842e09020b5131b074503090a90710405e04012501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 437283965 1250 437282715 437282719
    0xc02060c031902160312060608090a150902100815010e0a0509073501080d1b0609020301060f090f0c1b11030d0504030b0a020a051b2505040b120309 65
    0x200d03801030a0403540c06031080030b550300c6580640040c035600717240e480444441c654096a00500250f0341e51101107a2181c82510740710416004074920200042c03c54001e607920009040c800b01e60303211260002544409030504090108a14004120410800e4610001d030394201b42054260314581c100445c0100c85c682c001e039070140740303404042001e940c01a00b03680600e000d4580044421071010a202e069006281c42c0300e003109620800104031505d000c140e040044c403140d5030742e0941002d6080c444210813107103802552442d60310039803c03000d610280141d50160034202400d00000f031134079255000b140d00c1003c0085c00149080c01002403550320882d481e6104d00c030290642040740c4036080c0440f800200040041d071511030380d0703081602d1503003040c00707031044034020a00d030612030f610340c414541640b241c1e01d004000500c0c200a0102c1401c00d40d03125141d14841c0f0422101c1c1e10240c41980b071100301c000c1c96841864400203000304490300e010302501481e10010b071851490f46a00310b80b81503076805800320f654 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 437285215 1250 437283965 437283991
    0x70207051003150b090a05090c090913050615090601030b03060705130b04030f061b0f0c0822080d0302070201020a0212010b030303041103011406030c040f06180f0c02060c03 76
    0x3035041c0b1079080b1001a6036a0840f10000d0b681d10045500b4950011100d1070080f54640b900040c1498812020341c070440044a10710320380304d903200c200f003a9440024110520141546290300124408014280c4940079554951060302e2082d0104002c80c0310041c50b950405044c100403000c00e80700452080c0d006585130810725102c082106000d143c0075081d82160072200e2000c0f074000280807408070604251070044404112031006c042062035809161a011004951001d03070780e0341c25512421229005da8003c2038500d0400d01d6601d559444407202003000b44420440040070701400c2020311150340c4400003410304510f41911980048d484480e43c003070180c420b001758144681603070020f41020280b842c000303054990b07074070b86441c1c500803407130000007207174000c0d031130701030140f140d1a130f104111405010000c005140c41050700040001030304034038030b8413010719840d2000000d006030a1a00030500650020010a85000525580046510b540f0034042191f01c00c8051046680c614070072241c10940e498518 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 437286465 1250 437285215 437285239
    0x80d0306033020100f180f110d0f050c0a050109061202030907031a07080603010c09090203070201060317071a06060319060b0f09120105011427010303081602010507020705 75
    0xb01d450400401e000040c240a102c100b051015185d50110b0800800280100040301c80c212203c5940709017404000c0004600c3c158070004500056901e80d0442d038000c00d0081d440703090b581c07801500800c07034a044a50307030b200c60a410454a070440449000d0f100a1800040c0c1074589030000f85200c004040e55410303241c0c0040403c2c2808400d11100303000cae6401c070320103000c01000340b007480c4400d0b80b0441d8600b00143e1030344d002c2801850306010341004203500396201d030007031810509014000d503c040c26035000e5640c0ea200c004000380f01c400801000c4807580d68650b03120342490600c40c90000c41a131244140054100401c80195180026290070100c501041500d604410013044001c00c0c3c150090394110201080c1c26100881000003400c8400b01680c0c00300102038130900950aa80d02030041c4954605c071041c54642a051002c0029032242000b81c000c5c0703034403842c0d1458038030040702a0130540c00a401c0070108001d005000c1140380c0e440465100803c460714206200a40380d01e52030203a2441407015441d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 437287715 1250 437286465 437286497
    0x30e0c010f140f13170304030803070513240503060306130302030c1605120c0f060309120d05090607020a050d0f0e0918100908040b0c07080d03060330 66
    0x2c01c0e0071200030101d4241c0d54803c404110800c1d0b0450140b40c00502d05103100070540041d9a00501d4003109181c004500b0141599500d11080d08000c0c094801c1140c03d003c44d8258640e1407214034001c200b080040c1d200f091a5454100e86200c8510107070781404820018403565480000c2c090368401040039070481c4100c0700307180c00c07811442030808480040c4a0030312203820950411a9043c201ca604581c0c01d1913000b011030303a09446410014403660701c007d0403100c0c070480d81400e00c002c6511005d103a040c3c800c1e42c401c150f1314401503008040c89000c6983d03210100081e05a00b0001c40e5041003450000304500a10f5503282c1c1e56554164074180e003004200c0390307060103481c00307040c0c40400910010a46800da203095090040b102c1010040c820140c0700d1010108980503480c800e40181c00e81101c0e004e40791900380460200c450340500000c6105100d929400265010305000040c2111541d5a02203251840d40c204031100a0a0302200300f0a401141c0c0030301c00c0700040309100005852641800500d91413a072003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 437288965 1250 437287715 437287727
    0x3010905030406030b10080403051204111c14030309031c0b09070503040506070302161e08040f03140316020d0f020901151704080412080904180201020c01030e0c010f 73
    0x200200144004107000c40c2180d00358100e120a00c2d42174899000c1254010b804030707842202500d024003c11000c200180522400080c03007070380640101c0310f2a004280d0340b0f010502c035042c0300f00c4a01d0a000c480322100d040101a1010002d0003d4810080d42941032001c0103075164070590461454500c4c203864240021011500600c41400c401051050240b5007110f0103040c42c2e100f21012079042c003540c00020f01950092082e00c007416171005a511252803030f0303681c081d000708200042424030103100c018900041c050300b0040c0050708483d0035151840b8a9450a41d8a44040303004c501740c5ca42007842018501a014482094465011142401312100d81e050064400c000c82c0720103034100c00101d00200b110804420b030340140700415604c8c04174569401c0b45600d0764410507200144010000c1008111011039260818031107406030070030915241e03001002030100d50040200a000380241c500d40815586c0600421400d03400a090900c4140c002d07075001600c4048140c3c4050500004000708032005100d11 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 437290215 1250 437288965 437288981
    0x1106070f0f060501080c010c03020c12160605071202011b1d1201021801020f0c01180902030907050a120b010312111212010b07030801030308072601080615030604110301 74
    0x216550000750501e04186002c0c1509024400300c034820b10980e280c140d40700b6182c0648094041c2c1c09041240100d1041109604078070714088154440c104000e441c0c000c065120000401494403005e545911518283e0251074080c518107055901d8141e0803902d80b5040307105040c001105240c0100c40c10390030120128040280329590740c2040044c248120080015802040c5184030b05030420310070340801d0012a1b5079503594a0703c5040b03401c490a42c071965402403d400c002c02681c910201903c40d1100c0f07200c0102e80048510950640c06503100f00407a040c070416900291075200e000d15185a100e40300c1007001201844000c10003003042c1c40c000c03101407203444411070b84100402640d8000c1403001d07640100d034011010718131598003004000604e01e41036004940c005945034640d140b441e0f2a6440c1990144002480e2205000d03400309003071340c8a0880129120b00b04c0c610f540000c0070394140102a441c0481c01040c41a50100c4d01d18410780b01d903000910681c0c8240e1104050001400680219001d00410 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 437291465 1250 437290215 437290223
    0x507051005070c0501090c06111f0507020c031606090b032703191709031215010903080a03020705120f1605030409090c03030206060d0b0a05040218091f02071106070f 73
    0x100d140c046c1006103c160a00480d01c550b0f4544000d18140c1000c0d40e210340307004105540c0301c00002684001d41c0a60f400c1103504c03983e140140c8a070700b40c002d0b0109082c0300255030000b4941c4003d8400340034540d000701c8104098204130059900b54070300390440281041c1b03160a206141e9109080b1414011410001c8450401c407036824401d14856100d0042e02074103410131a07103541c12103e40007800c070341c0e00081555002c50782c013826200503444148150a204019506060410122110200c0413441d06c0e001041404c129540060343d034030803810480d06110f01da0303000c8040c406040150b9085440440c06507038100000050803102c200315460554a14811680803c040a041a001d00140040030b2141c50450b030180d025115035540344c10030440981400c0400400b00059400031a0303114000760320040e480f62001c0c00a00c244100125000d59400d41220080501d0b880405c001041b10842030118141c9507520401354245800ea0750b07080642d1548600442c0030300008107500d03007132102e4901030209030317504 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 437292715 1250 437291465 437291471
    0x170c0d1b030209122d07090c050d0f0b0312180301050106030e0d03060e0a0203040503070b0f010801110304200604030c1e0e06100347010507051005070c0501 69
    0x129100600a908000c00b05849080704c845128001d22010460b6036200d0304281642880341504030024050f01d6116030070303a050380b052980105000006106242c000c2e616900e8060311142c0303d100703200a0b6041c41503142c03c02c82c2059681c0b40680c4000960704001e110111640340c43d000b0a01c1480c0040c048081010303495070a00c000061072070f805a00016801020b441908c5007101f0201058080c2d6071940b142090304445800014001c0c0d00f03c0d0301940d0440d1080d41a6842c04a04e511290b41e031844c03d803110004a140080100658500bd110780d04c458000d0b035180da419803500c0e4842009002c07200108801342016024554483e0b41e810040b13401440d030102107000d280340c54100314200765a2941000300e68890007400421007000c0154400e00c1a04010040c0c0828000798104078090242c0790080d0700c000803a4000d8000e4000503804050300300d40c120000b03035884802c3d1454405d40d507070540303038071030501404000250104001040c0409401c00449020920f074507042d0b01252400111312000d02030b0b5217 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 437293965 1250 437292715 437292761
    0x9170c011401050f100f03151805090303070507030f0504120c0503060a140a020903150403030f05070903051b04020f0c0a12050705030d241d09010605031b0402041d0a0507170c0d 78
    0x109d4400302070440c4000d104001d05d680302c04005542c3e100c2503c1c00300104006100e9030000920940030300030308010707034a0041d0070250b8543c0c002042041c175007800c9404844504060006040070840c0d507920800303100050148000c1d80d403000610300700c003401003030105800080094290303c0c02c0108181c2c941e58241400a103107858107000700140024581141c031507080070003240d0050320680440003a240c01038080c01c0d48200401c0325861800e1442c074030076003003502400100150300030780014202e41c4052038054981c201d40c0745040400c10045414510502c1020300c152804643d0000668145244002001030f50507a210220b040039014a078a05441c004441c1c0c022a8103200c21120100d8540552504040d03131f100c1a401c2400d90b00c0d03e01584d600341c0d10480b00030405084511407c10500d40c0540018500b5071140c00c0c503d140d01030744840b4400d5089440070303c40310f29070b244505ca80c080c45518020a800703c045040c500d1011020f407000030744080200b180d01c19203200384d011801e80740041d2003200c4102 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 437295215 1250 437293965 437293979
    0x20c0f0706260412031508160603060902040b070b0403090801020d0c030e0607080a0b04060503150618090307110105090307060e12011104050409170c011401050f100f0315 75
    0xc0341c00320048402d481c0c8a0001440d0030729a0480340d000b02d5100f2409031112942d003900b14014100951108440310b400f4500050b503880603c408902c1300e0014002c41005420540e026007501c023658006030711544104020041400c0c0c0380c040d10581588001c0c442c02030344540c182202c1c0d581c0740c0d070081d00440d403001642860002c916800402c2c1c0c402c051702c05100c141000b60417951298011a038010228003481c001036480051540607035168a8005e00004806444078042468451401030aa100e44180000e00000345044415410001111141e101e4545010b0004588074000d02200510540c000d60031000c10b83e0040c0143c031142e84010303080340c20440c1c0d01c0c0d500924002c1351181082c00b5480c21240c150701c088040c0680740003411600c5519181074988402e00000b880881c42c182d4a0010626251a05019400082001c2c40c400000071400764100d40041e141d003039040c0d211074031501350b2042e0039646846040b000c0f21001c0c001c1c14a1850003410702000d43c0589040c0480d48102030300e16030042491 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 437296465 1250 437295215 437295227
    0x7170705010e01050d050c1206060c121e03011d24010513120f0b0603030702030309270103060e072c0709080a0b0912030f0f060301060e01181103060a0306020c0f0706 73
    0x90456005023070703101c41e010300a0502c24958109200e03048003e01d001c3c803001c100d0082c80c0540d1120794401e01e11705480c079100400d410030703088011b40e20760021941c1c0070800701490b143e42010440000d0214007201c02e82c103981800400f0343c0503040c0300d000700303882d1080d42d10750b0b610a000340102e900d0000010118504182740103900e01c821a902c00511010410606002003660007090380680190300e4403060200b04108a00900345c1079100845024403560b110903101e49141c001c521400c1d000c50f1038030f0b00808980c00c02ea0107810084403c0c0c282c26820034203503c60034141e02e02d03020425031452652900c2600311140360554002003024030503802c0e01c0c0c041066480c034203071140c00c03c00e0a81c1d14030303c0d950120102501c02038841c2d00048a45c20017007900505070705801e80e0490b0004000140302070740d0b0309501d80081c100b640000c80200a0001403000c0c000c042c00380a010307020a01e030492442c9400c00009041c3c2030b00c4c2c08050310446c2e001ca2181c4071000100400c00c0ba412082c4100d84030666070300802080f03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 437297715 1250 437296465 437296477
    0x40e010207023303060f120f07050913110102120a0e04060f0f0614120a09030e0301050103120513230a080d02030d0b0415150207170705010e01050d050c 67
    0xc00e000c0e62007102c0c03c50240720000b20f81d15020700701e008555160b03620321a00d80001e0001907000ea0f0103c0f8500450b40e8900d1030082c01040b1501400440d40984607032406c04040c1c4d40102d006400410030001400610011400540d5101c08649006000307080101c1c988240c0c01d00e0344408450004809024640000082c811040c044034184480364940c1c00240801585200f1800a801c9061040c01034600402d8040c41d0382038207602d40340c203052884090041c4a203042c2d641c20715040d034861000062650013182400c840702d040c1c000b84600d502d140e4845148468111041d01040750210b91010100d0480c61682e0041112450511502c0c0340501c160309804045101e00788241c0c2104c4001808001c0450034105651294014500380410304007000040c141c00d0030a5580259100b40034540b80481c100c41c4009004100a408003e01d00c2c01800781c5441d80e650840c0c0320341c11099942d40205000080c2800c1559000e1030680003684040c001070b43d40703000328001d40507070b50306000030004030068003006424 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 437298965 1250 437297715 437297719
    0xc030a060803070510020c21030703050f0402030d200a0b060306060d0804030206031008010c0201060503010509010b0a1406040b030109090303110c10110d060b09040c08060a030b070905040e01020702 87
    0x140c5a40c03042216600d1083c94401080750708882013603e484403070750740685070050b400d600b902c0c8082e8404c241c042603c6840000e1100812000c400c0c403041581c07503c00d00b80d0140184401410078203250300002d5a9502200304c400801020090b00d10324468403415110301221114200d402c2c1c0708035484d00400f200000c81e44103020380306990000700e69180100d4080546600f2080d070a241604640070310059600061000c00c1c4414800341c00038002500b445000d50140c41640009602802e000c1098250768005c1c1940039107070b0409440c0411940e8440c400001c94003105010006907200f50b0205116004903449079101d028040000201d4000b9a008500c4844c480e94040001e03d034030f06400c07072040c01003000078600c0345e0004c1d070140c0d020803032544210003528450140c507007800300045521040e80c600e600b004020001c003048010050401d0300139400d044500b030901c040d81e8a884004904510050f2001522480f00301000c03640180c002c0c2030704405080701810901c8515201560603010354003c4400324 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 437300215 1250 437298965 437298971
    0x1207031107200315010e0709030c03060e0606150405040f090b07110f0706052203020312130b120f040c090504032c09010b0d0b030730020d021201140c030a 68
    0x142c024074001c240000580103c03040d00c0e00c540d00b01600100b0307428005040005001c5580008408a002100180b000714841c081c0032888080c48902c16040802c090310190003240200c0c11020314440903001c0e141a03440c182d0700051440014455040945480c100c0907010300c8100050280c85036200744d09041c028681d0044410507818913540782d0340c4040e944520000200c06006180100c0300300c03130078405140070b00707000c4c4c086040c1c513500080c0c101005008829602c000020310103c2c1075207050302c85002045003510076404c2015481c054040f44600070311014200c0b80b000700040401028510410181c01c01d20300401030341c9040d1034003a000d60140d00d032441c014040800d61002034132040602101c0c5031005400f207007040c0d10300054101d4035040355240341c648a485d9022203940b514208211002000a100385103e512044014081302c2207802c1302404081c88081050702c0542c541c00c13984030710325605554400242038103144440c010400071503448100700c02c00c400e008a41010383c018500408002d8420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 437301465 1250 437300215 437300273
    0x120f0d110f070c15020a060902130e030a14040806010e2805040201030e0319080a1112070f08070c02010507020d0f03020606030105070c050c0603040c0f080304030507060c081207031107 81
    0x1515051310340969580141d000c0d0014500055981d004101c031300740f0203005a007008084941d10000c0c0c41d50200084050b41c008141c0d030300504c1c3c0c4032004445140b118500c4514040c10101d443da16510140181d256541c450004600d00c0201040040c010f07004601d414410805080b101002801041e607041e03000a050440300440300b07201100304d13142c9211482030f03000c0400c003840d030948000f04003c2c2030710300550361600720401018082c00100500700c01034012032601d190006020309080c01e000c2e000307420004c00034200a295600020414500e58090a003641c0703960040c03000880c0004218070081c0621174902c035640415400080f01030260004900170f00c00c99807804012242401420340c041c5c2550310800e000c6030142480e00013142c01130b009030340010700641c40306c075006d00201c4c15920451031344d440010100706000c4240000d0002d48864640800783c0c014030303219545d250003002804841c80140c0700101d03010a00a6002c400740005502035662183c020782450000072016a02a1600d15040c11103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 437302715 1250 437301465 437301479
    0x50304060c0c052b1509051c0f05040b1303173f10050405040b04030f03020424230d0e0304060f080403020109080415020c03120f0d110f070c 62
    0x32985905402c1d40b03e5201c41052210585000d55207a40683d1032603807005045d6480703800781c02a456600c1c0500c0c0100081003555a4064004214640000030406805a0442e16591080844080710803083c009611040ca2240500086140e1f40c0001c0121107803480c1c1c015180044806880c5920032544440200050001703641c0601c0c140301c0c025000034400c400b0030051101d020029503003103408641c0d100c8502d501e41c000728040720300c00d03034003910205003200402040680c04106109514030b40c0ca4190305061518201c90711070000199800560884040080ca03458440c82030342c41f5241c07000c500096100c503003046192540c0c6c0305603220012142469400e4a007a00004121030441d41996100716501140d000100c85080e00500103c085540b6120b54001280100f4041e001401c90707803925034080c40c0c41003030180c030b0b01c01d0f250501c034013035001640010010180701041da0906070f800c501c039a41d10342c0003501041c01850380441000980401050880c00141e03201d000e8461684110764012503282c880c00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 437303965 1250 437302715 437302729
    0x11e1d070f02070609060318060614030f07080703031101141f06080108060f04020a0806010311040c020105100e091207200d21030605030303070804020a050609060d18050304060c0c05 80
    0x13405010443c4180c04222951095010304004840e4a82e040503617010380d50b440094070203942c4070140c0f1018503011810f9515090205000034079103080100101490555220b44916aa11000d8117000714005c2d4a140813100390010b10f070140c041051207025160482101941d0000c1c924120720042002c0800305d480c0340604c100764140c403048001060307a9a80c0c0e03000d14124401c0104102d03000180d4500c0042c0c1c0755410403050b4061880f40f0241d803c078180704018002280d1407403030361104582c1080284800c1180680000b41a01c038030641c90000307a51426000b83c41c1c201d1040c400c41c404480018800e0601c14a03a4000180c0089407500e00c40b003112100400050303803c0020090000d91019499440e00748400c0c988450702e035000d00340030440c2c950f03c10004e070841d00102c9568010031b00c01801c00013140b400701070f4031002d484202c0340c407401c00c20840d010802c2c5000d0441c0c4400c1c043d6441801e080c2c00c82c20400d1103181c9950010882c1e6449442e070701c0080080221a40403102d01004880208035850045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 437305215 1250 437303965 437303969
    0xf070201090b01330801031e11010f0905151b1c030e0c04090f0c15050702010c06060f030804080c0603011a160c09060302090603010c0206011e1d070f0207 68
    0x96030360b41d081960300c10014048400c50b030a021321040b80200a200150460f000d072541d2030710f91351583e602d1401d20b16036066800550f5083c8005e0942200001003912030700402808003803030154130321001a1000c1c2c422541d590800c2c0d901402c845013030040658110028034502c0c0114501d40300603500d80207901d0751003412100d18104c030100c5140c01c40c01d0781d02c40c2d4800a415842c0604417143c010580001c07904961072030505840c0245110350480038001c0200401d0000c04d5444120500801152001091030040c080000e0401c000c0700040014007504d500f021380503024030b100c500c440b540c1d03a00e0003000950052103016254002d0940e006c030b492520314290390480f00c05000b5454541d105000c0005907610001003c20700e0509052400c0118420743c80d2a8003500c080500007808034103600400c01c141c100141124404d0303040541003200d4981c04505181101c2e4244129081181ca10b55118201445c031380054151112043c85100c044200c400842d01681e240d441e0005210000d15080341ca0b24218 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 437306465 1250 437305215 437305223
    0x1091a0d020f01122a030c090303020303180309090a020310090b06090d060e0601061d030a1a040201020f0d180e04020a0608060a091b02010b0909060103030804060b13050f07020109 79
    0x2c242944240d405000c0600c10f04100060018199001011034142c1d0501da010006a01c0b80940c0d19064482e090703c600204a0400d09150b92414034507a402940d920006000700714110b04c0100d46880100d007002510420342e4001c0c5000d030580703800346141c0b00135082168001004900c0c0380c00007441c8801032050784d4460724003602c40e525290300c1c00309120700210b910204640c102d0f51000240c601e03282c10b006032800391440355562242140c085440340395640114841c24800d0300a46805070000d00c5600c0c0e41403070840c800c04a03840319622800180e041604a841000650140702511600c41d41d1050020841040b0940301c02c000380e4603003980000c01002101d00a400c03406600b014003c0bc1e00030b100040d402140104160b1095403109282030a813160700241c928a4107401500e00a0507070280542c014020060302d082d5602d243c0b22440030768a6006200250074081100b000c43c05000707003908000b40914014200401c200c10305164030004250480303c0082c0241940042503c5e00e1041c0146118a070700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 437307715 1250 437306465 437306479
    0x9090809010e06031603051314150106050a090302040c0315060507150902090a0b0301060506040807090b1c0f03090e0115170717100302030f151e150112020301091a0d02 74
    0x5d5040a600502019000c09107a1480b101d075440054a9188218200300004024040c40405108410a60041a0003443c1406000e1295135030f0b1917030184032081100c0c3c0440300401c410b000c60740c00382e00030032401d81c00e400c8403203401e81c0c04904e240d0800010103440c1d00c1040b64842c8030028804e00710403a00d4070078009500199000104400c01050381042604801c01800000d0306550b420000368503521651140100e50400c070b1041096075046d2140700040740c003e440c440554118404448005c0600b4a401030607049090003200070f052060441d81c0290800c81d880b901c880d40c41d071020080b85d1010221020009440115011003544101452170041c0d0360780d21034801d460f00c030744101721540741c0050102c6210303041c2c44400000340e5400c00a03001b20781c041c280075120003150501c040c1020700001b80604003001202543c901c0e490254290340764442c13042c1e40d0701002d020b18000100d070000070440d8000507180c000b01c0049003000555006208803041c40106402c109100b03030074442e5450600c1c81c06940145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 437308965 1250 437307715 437307751
    0x20c060703030906060b18030c03013c1e05060a0b040513020c03160b090601050a090b01180f090f180b070c050307061b05030405060a110409090809010e0603 69
    0x4043d0700006040c40c400d4201050240d222007039104140c0010070000a246048524866541800d000c0d075024080294001c0c4540405400c40404039607080801c90f08045000010702400e51024610600c40d074141c03c4140500f42e2908600c04501e0400e2a6003031006143c040415010320380340e98054115510a80c030385040500d49030800c103903804540c01c400501078003040170307884001c0d003070004112111204500c40e8940c4030a05011002000c01803c0e40c4455001000500c065030b10032150304221b80702c90f032003c910005080c004842561540b52421442c41180c040411a42c0708140c032901503500c07011f010489405500d541e00251408a030300c2042070385c0030f089010007160082c0403903588445c081c10840490111030b5246495a4031000e4140d40c902d645603018022850b0130802c0321080c011074500a411070805480d03d03034807400302806a00b17a0665070340c010007184009009440060040807402c000704038150804850a520101c1313201c0c0040c10360b610000744c031301d4410192801100550014aa002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 437310215 1250 437308965 437308967
    0x306020a050705011401090e1b090a06080a050d020c0105040b0d02030903160f020a32031e070f05010203070c14150a02150901270609050613050d020c060703 69
    0x1502010300e103010030404202c514007140302400346901c49124490015400d40c580890030086895604161469400c5844a200d1105598a600c0c1c50313600100c94641c1161690340c04c00c401410690b0240440d0b01840700700e8002d025010441c1180b0403a16002d8501c0c003860a4011555440349008840d07907100103100c080401040d66014592240d02041102c1c90844864040450848400d400300c55031060304c52007408500702811204018820420120300382d450204102c00403006981e0100a111740d06840d990150380d00300030866902011014407001c085195001949510907030291420064448000292a5100004540e100f54100e28814296800d00301100301d2080d04e0050345031b0010803800051043d8042c40000d0104020607001440403603600e10044181c1000281820301591425400110040c58032000b54010711040c0d45040300d520052416100070440d181010300a27128043c10005c8040281001068290140080301d02c9140114000c9a0b50080300d0340403a00031100b44036603000a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 437311465 1250 437310215 437310217
    0xc2d05030c0c011b030b0a14132408010e0f0a030f030f0f06060807170a0b1801080105040209130302100c0e0d050706090b0c030301030b1305060705030402120c0109030602 75
    0x110341c441040e00d160140c0d401040742503136580f607110303510725000850240344250544115407051100796044d5205624060044485680c40c410b00e40c0a114550046003070034110784e000301d440781856075140c041d0b02490b400c0442002098007138a64190f00c0c00c6030020b001ea100146804100c2800c00c02400d01d245c10f0354007140c030344001052640901d034641050101c000854004c46500030003842000421510b0450020b19200c0701804d00000c1c0107800c800348480511601030141e200030f80c00800315902111001040048030b600c080d01c020060000004a010307407064200385e0256000b191604456154142c0c40c5088032036105000f009a0b1107002550780c40125504040704901d4181006115900400c0c01b0031450444180b080b125038022040034804150012030250203000d24038420741c10407288020080d41c0c2d200600025003030f0350340e180018540c006403100c248120f81d480030a903416070a00050140c810b82080d1022413180520f0440904071150010b502d05007010142e40c0e14104070300d140c50341402 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 437312715 1250 437311465 437311471
    0x402090d0b010801020a03050a0e1c05070b0a1b0503130b2509090c0201111206060f0c0a03020606090412080402150a0203030105031b0d0605060d12030c2d0503 70
    0x3055400c184000314081d0100e00b8000c0c810b103c009030744d0f0310300300742d0040c211000104020055440c4c8180300050800c0082e00f01c0380f0780c000e17070243c18916a420405440340c4c0100070f801054010701808105800550750840c501840082e041480c026030050740503030303503400110386800c0485040001040461007103c1d000360401041c6005140e400400504c401c40d442d8034203045004540c8500c010801d44419120780c103c5450148003c03c141d00d805031444c0c41512501a028450749100380c0824000d640702411506412244180c00350f44129143ca4291941101d00b800e8002d4000c00b400a1028103103042c0040c800c0e68070602d050252640c0e1042030b6010400a0000c2e40c010303992840c500352016001d0002c2c088032455800864030fa40c9020101440c0207400204207016141380c000313800880d01c0d88880c25242380c4e808400443c041e42d039503000c00c2003000d4210f0302a100310000d03120399080c103400d5032204601c0400781d83c80510f8928400002008450b003041e040303150740049810380340d90038440c001840d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 437313965 1250 437312715 437312719
    0x1a07021c0f021c0201020c03030f04180f0e06010810111c0b19050f030a211119021c0203060a24080313080c030703150f0f0605040f05090309040209 65
    0x400c001d155004070307074a0b1a603030460710f50a8041120010556804200d10703080308104400851a1514003a24000140114403e00c0c200c9a00303513001da140e611550b0000c00300c82c0ca61000c100040c0c84100c0d20780360303204428881c40300c0c01e004072005101c40b880340380591504040000380680c600501c01c800c4c1d4001c6441c1c149044d070350580da050104030036941d10310b165078801c0d41d50302c500f100c00d4140410800e4020440c40c1452190b03000018510019005552512800c010111042b08d88034510400b80c03802310084c00394618500031001596203001c1039404040000340240c40403901001c501d249400060700c00350001e17501d64081000501e0046454100c1c9624a100e440c0d0042d072001100d40c500601c80040c2c011003080d03040821004243e4800b0400f190003060030b080104060b446010210380c6418040c0005040c642d03a100c801c0c8903942064018125030441c0c010200880c1c1540c0380c1d5580102486d020703091140d82402d590307641c412106e0207424000d070815405503140100c07440400c0025400340342443d03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 437315215 1250 437313965 437313983
    0x506120606131806120c0311010903050109081207030b030a06110d050c03420a0b0c1e010b061c110309030306090709031121161a07021c 60
    0x2c6402400103540001c105585074040c146607901041000c1e02e10075001018807400c043d03a03250101c0c4d51556401c0c112600030210301180080a00102c600f001c0541004d0142d41c00d06034041d01308a44171000382050011404070f90a1902e9030801181502d40d080300160380340d030101c2c8103031b4003150965001300d5098160820b00e510700b402d0300103240e060700c0c1c088844503403149021040006c41a010002014040e0102490400907050340f94007501000303582d41080041600c00c1e04211041d12a100100040c08000003040d07103c4843c00c1a490b640c0408070704808a1019901d40b0662070b2074140240c05055000605680c00e0032458030346542c0300624900e0b21b8043e59142c03030b0f50703024038a03c1c1340042d030040543c0c2c4051a80c80c940a0b003070000754031b40541040204600310f8410000720f800a40c071109800300c103c81c10f082c00113225003c45070703406010b960456035006002c0030541c10541d110900017168103400300c00082c10301c0207082d41c201340910000a50409502900b51050780154441c800c0d15030302c0b400e120 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 437316465 1250 437315215 437315227
    0x5040503011404051203010807090203060d0606030f02100809122101030507030b090606010f0c06060905010f032d080a021f0603110a030201020d200a030504030c0f0506120606 77
    0x707081d60b0300c900300010b0b1610301c6400d100500200f03000c0c2c640000c18000752a807030340d450401c1042d503411035441741c91100b41c0d011001c201076030f4518a0300d5011642201c03003441007546034186402503c00d140301c100d218160002107481428001c1c2c0038280726500c01d40240c406c2e01652a0448440e5114408605000300f1654554800190a040250203140603070010000c0c1425031800c02081c0801400b00400380e07000c08104100c0340c0c0d01001034501118030346484070741940249401c030060f195980040300c00b541000004501000b0450000d01203900410a01810807061900303810703d4043c1c15000020300c66503410140105840000801a90845204940090200340f00d900940c034415803110302c1c0e85845250400500040820004000324222240e0850b00e2955002039564031945070440d051201d803400565007410396104840c42a00002c0944043d140340d4038000b40b040d0303c10f002c01c81c0ca04102c0c9a020071101508440c20003551030262481d407034822621f440f5100c0ea00000d0249030701440c20404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 437317715 1250 437316465 437316469
    0x206030c04080f010204120f14010903030c0e0603010f03020f010519020706200c01080c07020d08030403110a08030f0a0b0301020d0f0b100507060b0109031703073c050405 75
    0x5512580003922015140c6081a203298180809184a98180d81c0144000d004686810345000c1420303034000d4001d08614034520b056200c0340d4919041c0301c0705501c0d0071490f500b0b15416422000003808143e803007401840155041140074042070240300c0c4460f880e034105000500b0682ca0441e0b000e48141081030529120340410054a00420304180043e00007000810102ea0811003c2c28a100d903107c601c0400ca003510070055071030101c54080307410042c03200085014481c078201203a101603000780440320014080c1c10803804079030054900300d002032031a000000300d0b030b40701044076036180364481c60040c40c5440d000c0c00c807404828041c040c00402640c075100d000c4507903001d00c01004407021480b400300380045071000400446030b1040c0064008c030301c01c4001d4110b07940e115049071141340d40010700054031501100120f132501c201b500018111080904080b41144071f0b103000e948a810705a84040071101c4203184104c202c1c0261150079a00700d020010b51944130b00081c1c02c50303d460682d00c7c205090641d2000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 437318965 1250 437317715 437317717
    0x2030a0902060423060a081302120106080a110342011202040c0503060f01140409060e04051c051c14161e050f0708040e04111e0f0411070206 62
    0x4041c00b5848507410009484d05294022202c10030011100f440c104488040094134859009012081803420f910300581150369500c4052380c51703903840700204030450301d404400d9901e01d1030802c141d034003021030358000e00940740c0001c0108801e8230400030f0030780000740b804a040201c6040f40003e07020102c1c440341c00c411510300c41c9000f0f00030100d54a896144403120f005100441d90b129800c02e042100410421085450707000300080a8038083c039120fa05c12000c071800311a50300031a00300c00700765420310800040c03420031810220f005602900503a0740042400303aa40d000c1114054032003000c1082804100d1048003854904400c03520f0000005c58030b80310b910205101100c1c1220300ca545100290403843e50594040c101824903d8218000c808645c28080050068058241c0032000c03000300203410340c10482682e0a840c010456080c029485081500c1c0490076415034066043c0a441c0d02e038800c090404c800e04c20a40042c002500b41e0850400c0c12040c000075008560182d41c00c3e000401c9004c0050311924 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 437320215 1250 437318965 437318969
    0x102030f010611070302010207061b0501141806010e04030c0501090203060109150608010e01030602030702071517060f0f0f060717031005090c0f0d0b12070801050705070b060402030a09020604 84
    0x180c69150325810100042c2070103e40844043c0c1c40e80c4140024401030340c001030f580058541a051021303546440140103003110700280c000070465400c00784005c60000801220f24000c6403140da02d1414401d0360789040366940e10908c1045c5045034254040b0300400e0142c0307141d04101d8090320010031510200e03008645410006e038015100c5a603680c2c1c00c50351105000c0c0507032010340007130f10700100954500740280512601c10301019207840d50000c042280d050003082108002c1107a41e03c2202403c2030584080e041e081c01c121603a0f200500e1100240040c5442050981541301c000d0429500d251802d040c050030429600c58940c0000f801c01005010480610340002e001801004a594074501410b0003d04d03103140c0e51025015080780c034240145a401c0005a030480321401101988829205007000041d11121003255004100319600000420000c1103c40944a50704007d01548e11064021105071044503006041954040c001c6541031a041e0001e582184055002051660345500065800d501075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 437321465 1250 437320215 437320231
    0x110918060f0c07060e0a0c150e09060402300a1407120e0318030d0806031002070c1502301605010b060c100e060f1609090204080106050906060a022a03010203 69
    0x1030350341000c0111002c10300001d46480f149041c01c9a140c03201c0540502c134080013075848ae041010004119440e6a41a503d00b042d6011006000d200410b000581140c0324041070f107012040c0000140c9014060b0144250a02440800603450b81c3c2e18102198070b900c12003004400c01d40c5900c603034441403000308040c1a901aa402c0b400c180c2910000425203030400180c46941406179000c02c1140340e541c042003e10380190080350250350341000d841e01c41300400458110000144004000c224815400200d000c107850124811181e07050308010405140500c442109640030001c1142c4200641511010302d1518032440011030f0341080540003d5260b0010800111103901c10255140d1840613030050070031019896015100f075044c00201c0c0014210300924104410002e1046000c0007031240c01181c0c020124200d04640303c1d6264040e241c00f070b0060344949445a278080c800701d40300c0d14010044416003580ca030010840c0c0381032020507210288000c80002001c0c1d04a00341d01515072800e00055114480c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 437322715 1250 437321465 437321473
    0x30f0115051905310204030803091917070618050102090306070513090e0a0b15012003250c060e0907031407121107110918060f0c07060e 60
    0x50600b8040d650301c01540c400c0d840782c00003400700a01d13203c1d49542d203064552500b20b201800001d48880c0c4000482180b040322491001a001007801385480140d4000c1c001ca4090700c81c04d07582c1c01801030300010031001c0030307240080c0201c0754101d840c0c4c50310003810940d100f42400b1aa1f9500358614400c807500031030f4282c031240d40004040a080c54103008032640441c07a410031a082161103040880421014043ca44030150303202c02860211070200407445025034000211105480c1c451114000c80d02c041119a000ca46460810b00b4190102030b00710f5800b40c180f000550600142d03220307665480c440c2001c01101c01d01041c0c44000800c0c40707010180042c0c28a51600300a41032074805200c0c00d558000c10050800d440c25107200048007014081680000103490480005c8402001c1c2c00000c0810780360400585c0b40c00140e4000300000381d05404138001c1d0413901641e540d6174404440910b14104440394038150404000100d40e01e090030b821640103004844442e05040080e501d40c022124900d4000700540c0c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 437323965 1250 437322715 437322719
    0x40f0e030d050903040602060c09120d0306090b0f090609060d140d0207050a1d060102012405030601050909030409111b060f090c0a050105031801020304080706050603190b06030f0115 80
    0x3482c052190428842d20096180524213130000f510360901809000d8070030740020742400165500c07450b00b80203814800070394600c981e00b2400600100030903c10044554107110507a209071030400c4000c1d5001e03030701401c0d43c1c245680b144100b1501d0b4500410460380812100d50313010200324014a60f100d2414071500404040f540703c04080d02e00a02a030005100728005039050007002c41e000d9072044500300c0d01421816540b1603d0050f0301404480c10f5031450201801264110380c5004034842041741c8044e0142c651590700e81b014802c4102040300c1300d00703d5030700801c0700f001300c4419540887e12040850309664100916659600b8a460480c01c0703448441d1b0201003800090a07001304015000b602d8400140359041c42e800c0441c024a150741714841c103014000c4000b0b1040c12106c0800690811040000c40d500d01d814039010065405c42a404d903451458500007503141c4c00d0028407000c61080131381590b21480c925565516520740028a02a094011500d032066955000d0081c2d40c54003080c4080c10b40000c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 437325215 1250 437323965 437323987
    0x1203040b0105090712021e0d090605010e0c091c05010c0e10020604030206072f030712030204030803040f020d020306151c080409110f0301062102030702060f06040f0e03 74
    0x3901a0081c51280341c84005020f034503500054034541000c0411000368540310070307904c2c6c0060002c152031404150000041d89581c0785042d640b203111024406e540801061741c940540c4040082d044904170904142004810080d01d015090404100c3d8044405210440c3e0b5941d02c43c02d4492000701c81010510840a503190791921603085020840380d0700c0117000918041e14000e503500c90251211080c481c1400009100003440c2d09040041c100c00c400c1510800140d404160b0341c1c0e40300d440d043d140600d0030b64284c2c010358464022501103036003000d0340c5030942c2c4894842110042c0b0f050812a8808014170880d001038809000c042d04c14642c02596000c550040c0303061000143c2400e80c141c003400942807840002902c02815a800e5407068000010740381040920400a881880c20007901c0070400b0000040c0150700c04e03002003201904000341e4130524a003e580100340e000a032840001740e0498000500c2070480e078030000e540325070010700c0810240d450600920403544204440c030341c60341000421003018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 437326465 1250 437325215 437325233
    0x2b061407020102070f060506120f0706030c05070317070509090a05011a0a090e1302130507020106061d150405040606020102041d010e011404150b0702040e030906040501031805120304 80
    0x100d80001d51030201e0303903034842c000038040041c001d01550b59000400d100d41c4450110508030342840c01140c031034040c124055541c1d42c15510500000a0414240040c002c1c0301d0030a84e64031951585034040000c07044c00f10070032200c100505560400c0003e00c0340c1034155481842203801500c1c030210005980d41000e1070003102003002e40e03131030b04280020415116926440001072044801810f00303607560b5100d0f80340c0e1100e031041c1600d000e5400103a000c0004000304042c2e024031300030710590b0020865190344040603a4102c5210b5192081c03003028146100ca2070910304103c0014510205c00f403071a003a241c000017000c0361041c4d0041c00041c0c1d03001c1424488903444105088a0b8038130104c541070150314103000504d0043c014041e444004001c440d076030840b91a5500b010745c8962102c1c01501d605500c0702c001c40383e141c00c10002a4816402e1040814411501104440040801410241c600360808006401074143c65480038004e0404088041c04100144550000c0c0780340c1c1000f07907a40b414541040500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 437327715 1250 437326465 437326471
    0x1b070621110301240201020a0c020405090a020d05060106170c0f0c0a060618050609092a040c080f0a0e0c01030903020307080a0f080a0b0d0311030c07030b010810050c04052b0614 78
    0x5c0d6841000107e44254008510750750155040b42c000c078180c0d4030034a84a0506101c0c480085d000000d00040e1020088041241c42c1030382c030250354400d41c003224000900c0b8041e42c10768002c41c40003020444038182450fa4001040e0500007070040b00e01c1c1c9681030b0f40704000c42d500c42c1d2188074004081d9031032841d950800c3c0541608030b0002c84e81030002e0300f002c528480d01e81400300420444c58081d00342800321742d2040481070111481c001c0c82001820340c10440900705200407030741214000e00075800591082c409100e00800895a040100030b00c450800042d4020140c80d5401d8007035110920054000481c980c00030180802c05543d00e8401140030900134007454005044d0b000c00d141402040003540d110784203002a0300360189044003101c000241401d08606c00d074540903640d070081440220a000c040c00d030301e0341210250400c56400000058240b8211032054900090f0754104010400c90340ca080004001c6a0310041c4028449858100c043e2082c03100a03c4100d6803240c503282c4450340f070342900091682c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 437328965 1250 437327715 437327717
    0xa020705010c05120a090902042c090a11010509061b0d09060c1509050a050c10020c030a08090a0b0315040c0c02061c0608121b07062111030124 63
    0x5140c0705a07a60a0f8842e0f2508044c00c81207600400c03c2c0c80003074441c50b07165004000c42e01c401c56455858107100a89000d000d020b43c0710b4000d200d200c00707812094000e1840c0c419440400030706541815542c07012400711984411a0400800744205d448680d02d180c000c00c500d030f15030181061204010004942420780a181e042c0511100714020041160801200001d49a00c81503104070382442400704401012803410107480d40c480c0403100340c01c104001a00f143c0b03000342118a80e000f40483c0d03100301c1e40ca8290880c09509904186418000a00c15801030903102800801e54640d50fa111281a034158008807612091100100703d914a5401e0911030480007500925240001780380303030b8000c0342c0c0300d22407658804100e490800b01c000190b641544190301801c0002c05031840f45848241c0e2030301ca41c00103022402c045510543c1f114409400003501070843e01c207501c54400070841c0f0104001c0400088841844040c0c42d00440303641008800c0045003c0c0019030f1454185008458050600200c9124480 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 437330215 1250 437328965 437328977
    0xe19060615050703032f09010210060f0e0604180534050d020103110a020a03080a0209011b0602040906030c0602010f0608060a0e03070c1d07050f0a0809150c0a02070501 74
    0x907034076a038068100c031802030b0941400308444042001ca11104500820f00e25810320fa1840c1c4030b110001220020080110242c0c21580c00c4040740010404a507420705c40e039580c0c854107100c10442c60702c500c000d081d84028001c0c0002041311901d110203280307440461045a0b144c014500c02c08205440070f04c144527092110200704581e64014074002c45494060050074810b44100c003580085a100b40c110039001030004102c81d0701c5581e00940a03503074000140d4124045148240051001482da20a8405000c016951420580090707258403000f008a07141c180c915640811000c25407210600480d00214401e243c12246a450844003d0841e00c1605d4140321150818108100b031140000e001034100703610a4000036050030151090b80745100d0403400070400480e8241c00945100c10740181c1c1d5003510410040086580c441f241211248640d0300c94080382e442c140711200280c3e01c550142644a103900045580a0705055400c1e9403483c011200c180c14400c000031300102141e41802061700818083c01c141d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 437331465 1250 437330215 437330249
    0xf050a050d051903180c08031803030c1c090317030612011505060a020f1207030f080c0d050414101a030109150f0b0d06060905010509190903030e190606 67
    0x58460061030f15241080544804d00380030704505482d8041092a404649070441039a43c00806d074594100c10040444442c1d40004e0448a007004030440d0b05980f074501c050650f903200e000b45000300c0c90302014200100560307084040009011540c003400c8100483e5410398903851f146003084aa21880031584035143d0400700c030b00c6090711383e10100e442500d0342280c0b1262200c0d09640100c3c60500b10300c0400040384681c049911814811000800b0a0703070003a502d02220002c0790606642d80e040075a0001140c1000f0420760500c4c91150384566049842403010340c681022540c0d569140980c80c4044d0100c141d03a991511010350300083c0c130304040d01c1e8103a000f03004051280d100c061903031101c0a6803594075070300c6080320344444005034407000003117000401180e48184541440030050496021f142540c6182c200007040d40e2600d40c8880c2d1294030181e400342d1452402c1d05019018040600c0e040702816110124007155203414083d04031100d444200440780040f0380d05042040c2c0d0b511b07a0095900800c03070703049 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 437332715 1250 437331465 437331487
    0x31911060a1a09090c0406030b04020a0611150603070b0a17060a080304061407060c020f150c070305070302010b031e070b03060d02010c1a0423060705180406030f050a050d05 76
    0x4600b070210001c542507000e80d9104028203040401e11029150b1003840c00501004000801d84803e00560095410301ea03080d0312a041039901100d01c010195840d4840d00303c88110940104c2c00030340c001c8001d802d650343c050f661034004000f0381200c030740308011031160701800e80324841c1101d03501d600c1042160580b00e1945802140c41d102e10843c020071041100e400c80d8000c07070b61410300071a5500303944400c080202e941d001500079182d44003080002c029004420704405802401f0010034000c203844a4400d1406900361b80a641c02d502c4140300314103654032605d03100c3c0e4a0340d05100b0345101951041002280b45130140744681082c00d1a008102d100b141801031150340d8482400b6660096420b08100290b11034508144a0b19002000e0158403000032030b041004100156200016686240e690200707460312600ca0a030f02e9000c02c82d00c3c0d100060090214001d01115005009203030000600b00081103601d0340c0312200302401801003911a80d000c500744c1c00401c1410064402e00c41058580142003901c03c00b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 437333965 1250 437332715 437332751
    0x411130b011e05120405010c111515030f01060608090d09180908040909051b03060402030c150f040306060f0806102907050604031b08030a0c02031911060a 68
    0x100000c03a8520450303000c20700b80608200c510206011305409500d10300762810f54003a0058001002c00588a0391492009074000103d00031050b08580f07500301345a944070380f49114006415005a41441000c41e205d003004400e100f41405032405542c0d2044925068201c03519010301860b940c01049008d1104001c04c1c01d0340030f06a9400c00000901003101b22441c01c040119006030b0b000b0560b560328203003104041000004943e03421484d40c3c1c1030141d050b6007440c1015240e4004031000303900742d08120000c44c2c00740341281042c00b020380c1d0b88050f607080076240042c022054116810845540d41e90348018014804400740b4503009002550081c4024504110110380c00c2107184159508070f0412a4080c51a8404914a52041c0c0e20140c03541e032500c145061a580c1d544041e07034250089409541c45606800c1c128020118168006000601c0c50325006a10700040c05d0003002c550840c0404c0c016402120b00c00c02c0d14001005143e520600103000c4040b10f1810100d028004582280ca404c800200300c486282c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 437335215 1250 437333965 437333987
    0xc030905121203070c020a0b0a14040501020c10030e012301090605011e0e0d0b180304080a0f14030a080f0901020306100e0f04020d09030320041a0708030411130b01 72
    0xc0302c05070b20b0ba120b0440c26034001d03140280095125020420200e160600a0702130100b0784502d42d5030b181299007041e915910391195000740350050b007110311407820b68200b20030300aa2500d010314001540e103011480140c00c50b081c1c0e44c080600005521880c40f80c055070810300601600c009141004560300d8500081c0203060980c8002803060094030782403405600640101540c2100a055000100394501c2c040b030200c401100d4404621803100608464101c1c00010b550941e640840144940c40f241c3c6c4419004108600701118a04040f46900c0120101400500300302400c0342c440030549d0406595400200ca4014101e40d5503071b10510070441180d440301c1c10b200c2500d40f03600f4003509000c505008150b0038103442c1c43c91500540000756410452070141d1203103406900036030f002c20450100340c0320b22103010ba25203002440c640c028441031001c0070440210034404100010314a2408941d5a281060303504115006e0710703a80341c0030b0001512810491a02901448855800c0003c0c5041a0010342288400 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 437336465 1250 437335215 437335243
    0x91801060c02100c0506010b0301091503050327060705010c120b0102071a0c01050c04080c090f040605131a060a0501050307020d080702011e02030108011103041707060f0504030c03090512 82
    0x483c4200e10312900524268203642d8000e000da91544d0b841d141203c075564428807800000d0381c03a01d96042c968907020528402581c0e80040550314250401700220002500c1d207580100941c4038100303682c02c80e0355060060400c43c0c400c90000c10898254580035140d14009030050f0006030500c803011030310341c2c1e010076030340141e84110003400304010703aa142403440c070f00401e00440007961030001404031b00300415020303100301d80c2c941d01101c1e400099442404040300e02901c40e520140c1c00b0380d0105001805a41080e5405240f00072041c0d01320790592182e22500461784c1451484e4a210018080c107410b0581617980a03040038203100340b850902c04002540c8400541c090810440301e5804100703150310079040381f0020306414207000c801d106600c2c07040000394001e104401c100d40c6010300310203091082c082503910458100d1440062035418482c00081c0f5400020115203465581ca240c410011052107900c3c000c90003903685000050861074083c1c01116560080c6104606000058220707032400035a1402d80015 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 437337715 1250 437336465 437336479
    0x81008011a0a08240c0412030207030212030a050f2107031b0c02060a03050403030b10080a06060306030f0305030441030c0c0103110702040203090d0306050d1106070c0f0902091801060c02 82
    0x80c03900709417041c01941c1201381d044903600c4641c424103034001540700503203000b1129404081400c82c4015568406d21145101269051115100071041000500316400b506524510031044045610904200031250100480e6480218044105040c1c42c140d03103a013203a090200c54501d0940001d0f00d01e0041c1c440074002c25860740006410540b1079003004540d000013070f001c3d103e00141244003a10020084441d100007910b031207400501c0b40d01c1b034050103045941203000d001034144c06032412502c9520060095949202c16241c00600d000f18032600c40c10384050214054100c0d49802081c03e409100b9402c00381194418003200d2026400443d000c001007009007070004030382c14103204816103130065240280d8084e10100800010704000b14200c00d00300945c0e40c0c1040102d442c0ca08208607400c602001801007009210300043c1414494020000e43d0f00402d6080c00441d42e6041422080c0c0b0142c012040240d00400c80007103d007004c01840707404401c5000b40031419030400000600300c1d5040344010f442691 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 437338965 1250 437337715 437337721
    0x209010e04150501060f02010b0d020108161106070504080f0c090c07060609090803010f1d07030f0f0905010605100509090402040c050f12160f090501081008011a0a0824 74
    0x44404000b2540c6078011a0520140d0381d44c58000d0f0268849111840141d42045114403041c45c02c03400000500b5070503101c108450302d41142d0746903d10300341e0080385c1c20f1105070b07090741c1d030440c0c8100031191060820347d81c0c00744d459051240c980d0401c070110a000b8244d40c02420072600c1507441d420318076030040340728003150f84401c0d00c1d081100252003194010303a4814501041c500a00c884d90008505a42140c068000c83c1c07070f56a01c078030400031211442009c02c1a583c20110311100c2c07003904070a411041107000494079800e060004022038000340300865090b9500e2070b0810071410b00c9844410010168249141081e8200010420100c030080c80240310f59641d101c1c1441d5a800740d13003590b4024905080c103a0700d0f03c00d01c441d4000c60f00c90940741c11101d82e080c1da00b4904294420142082051150f070b0760243e52600d0000103440d00b1b4000350540142030b2014034041480c820034440c80301290b1808440400e201c03100c205011701007900c0d40041740380303412054456010b2080c00703180c201e00010a41b190000d5035 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 437340215 1250 437338965 437338973
    0xf02040e2e09020a09050a0c1b321b010903020f0402030618161418090726060f010e150901030912020a02031002040501020717010207330204030209010e04 68
    0x8a205203001354084840d10001c10010f10076800326116442c110360030000355864450603505488014400040f01c1401020500098044540c035602c01810b00040d000d064200036641c0001c0c0540080b10034281e02044201c1416484a0441e594071902801d180d03041030305540101c1e400c0c0c810710aa05000325000030102d0180d0f1a00355602c001c41c0905c1d00c0d41440ca04124038900000c0070200161800102ea42c032000304d1021040d03048510100d205005050b4041c0310105000011000600c448140320081503150300008040c07031651071441b000c5d510107a080c0b81c07240c2006904910388450504101218490b030007680c4540b4001e64007201c1d0134003204c0d111541180100e000d4003180800808610f18944201c4807250001000184c0074400c9042e036030425003040c0306200b28001d511a240c010fa000e08010080800c242440d0300403941104009840c0c0b410075242d5625800c410751028000d84080011015100310655100800c6800700c6001d500c2d26241d41c0005028400c18000c440c3d1100d27030840820300b04 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 437341465 1250 437340215 437340221
    0x12070207060e03070909170f0712050324040b030319030e0705060418020405031506010806010804170a0c062c0601140f0112050106091d220206070f0f02040e2e 70
    0x1000c05480507948c1e05a840740c03561654009d80000c440c0000c00d000c044a405010700d082c3c074880c00d000b07800f04c0350100c102940a8210845803c041c0d401590b14003807440c541e10180000c15107a40c00507501e060f00304881d640242190412040c03043c654008410501840d903483c0b084030f0440c1c810301e225484114610301800024441e9901155242c8039000c05040c04056080304a071040d44241c951941c00ea603408015101b1900c00c0794000c01000c220761006600418502c05001c0d0144907180c07010707500213550b451200700c3e1082d45913074060984440a205014400320b40060600b00400040c0c0b526500d80316040551b880100c464a1246070810102086039108039000c408220208009101175659150301500e0001e041c041e52024007035681e0520507440c50146440e01549100030710400c81420008100700c0d149400d8000ca1b809482017184501003400d03c1ca8000c0c03d28041d0096018844ad50f10400003110280c43d28469641c10018034044840219820580101c46124464040081000ca44d00007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 437342715 1250 437341465 437341493
    0x308030c090a08151b090a051909140411030d0503012115060f380403081206010e010f170907092a031404140a0812070207060e03070909 60
    0x20f107200e4401ca04220543d0401d6a0b0b010307440160300340c0343c1051072005140442c49a0411b042d002410860304210504100314040d18205420240000b85915103c1c03030340030340d080780c0c001c00c61548081042c041030251902c011185164200d0007840d40c5180c0200103001c50005100b183c0350710300301540014000c0c8c3c0140151442603408044115101c05000260000300618066242005c09566002c01d0f0001c0400814514000b14100c520a20103881c441058580c00e084203403401200601000000525480107040d40c917400445500306454480f0005140c584980011410003e00c180d40104454100b0402c807034900c5242445045a55030305003192070300406a024100d00c1e03140c10402403d01c100c8060443e084c0118107034410300346a403030f0021029144000e100b407640b203002d400410000f44c03441c64200c45900c49001138441440550302c50400310780282001d1219403821108001180c0d506200744d00c050261030030001944200c100119503100d1180c0034420034190b035040142c0c248190301c146416 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 437343965 1250 437342715 437342729
    0x507050304020904080c0c060307052206050f090307050a0803030a0f02040b0a032315180115180f0b03010905060d081b070f1511010c081501030b09040623010308030c090a 75
    0x394a00b020ac00040081d0712040089010070511407021900260a042c07402c1120000d503543ca04140b2600d42410f416440707078a0080d49803140c13030000141600d82070340f02c1c0001c00b230030000340d5203900e01005000142e401016620440c04d1041009018400040c02643c000c40c1540c034002030418101c2c8904017040b0543c0380030711344a003203503801c00044806c608569031000c01c0940b00300c49007000044c000002e0b900207002e0884010318104803200b20510a18030001594030222130a80bc595031048100704091407504002d07000000000140100c0d0141d01035903403c1003064030f0805441c02c0e5a141c00c40180507244c02c114001108842c009102e003400c0105030b02414a030900f8420090f0740c1c0b401d44800380c2c40e00702c00c03c000c1350700d03844c44c80d110000c18444e0510b0b000c44c03912003001e6903480125621200d6a04c41404c2c0c1815901d080d41c0c1c18030344400c0d00042c403591060304005049840d903c90300c10402101408600c06140304001480060749041c10303a82c0200100b0b10f150703190851200003412001440e00003c1c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 437345215 1250 437343965 437343967
    0x20a021e0d0c180b0d020d060e192d05070302041104050a090603020907091a0f280210090c030f06410c19090b0c070302040507050304020904080c0c06 66
    0x1103243d070b001c40030340180010000c0307041002c868000e05100608141160203580040060061400b048081c2c120b4039203082c102094400d00d116098028407106a00041960050282155502102c180c3c940080000750b9044040e0004049940d401c2d940d04103500000f801603440e07100c0650b4007440042a00c01900c402400e030380060f0303110500078004095034402030b44a81d9400e00823860302030240081d602602c0c03c441030072043c456008011941540310301c14098100408004100541c2107107440a5908880c00b181c12240b48c0510100174a0480070302d1008041c286482030f5280001c5959481c0e1089039031044000c0035407031050a10200601a0b4808412194a039080b5120000241c001c85071036900520306000b82541a555003084000302143c034601003031020400a00c8003074200c42c11100442251802c61086a00c07400307400c41030b400c8407030f05040b00d41c09204140214503060144c0e40c6e11042600d041421840e0603000500c440318050805441c490300043c4d240ca41d6502448281c91072113020b042a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 437346465 1250 437345215 437345219
    0x7080a0605041a0402030a060203040f0204020a0e090a052701090b040812150609040b120d0507031106221505010f030b130b07120e06010f0312020a021e0d0c 69
    0x100058002110102c5043c501901c05800201030854458000c03070300030f002006045015541c8600a510190003624030010f5690a01e005a031180001c112250540d5a40c09e0004144000e000501c9406001c00702610300304010040d1a4011100382c29202944032404a5007060789845c4500403c0d1901015044030184410402400391080c001d20b61020408890b400556601c2c10b000482c144601c0200d0707001c00100554001c6283c20380081010520040421524a8040001c1494658441c0100740440c10204d415000e140c0c0004a0304040d0503064003804240c640600c080b0886d400074011282a59515119071091080c6080e1540c0a88804c11040141356147c01f019028850588012642c450007680000e40303400c490385a03000207a80c009003420031521811401c0d84c4040802042000700c50b61031285c2c0000c21810800c0e18024404c018800c0691400e41c2450041c010f50003807075074259442401c2c260010385441d085c0e621528096291101611500d100288404034204005000f0035540180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 437347715 1250 437346465 437346473
    0x4060207080f07050906010c060e0109030914060315062208030714010e0604061107171210030f1b091b09060201060308040902030903120906101d150307080a 69
    0x100e40141c98040c01211011050401500c0d034648803809040e030400c00b600007040995002d030010404030343c452500814100301480c1c1c1e00742111801c0c40c0c15000110406820040c1e583d03040c00701032503020300351981407441c0382c0351122440080085004601804000030310350100a030070302c034210650744004c000d03203401680d41c0d0400e903598008641c155100c55806506401c0c66005101d040c4184210a02402640d030319910382c81c0041c000209031010b41031081000100141c4940c16010b0b100b418074080c1501c403091050b1003400e04500500c5801c804004250074030110710564030030b03114076501030506003003400c180c010000000c2c01544108081820a10884000e030307203508080000c964655101006d180d50b03584101c0c261000d520001e407999404000a100081d480c1d001141d1000d0350208507841c00c00c0780c203411610b844d0200c0380b1511a8000300180b090703c44820034940d00608061a4084c1e0843c8045a50140c450f4041c107680c402c07000c2c911819113291000d00200b0000d003000015120401c1072810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 437348965 1250 437347715 437347723
    0x207050c060a020f0319180305060a0b040f061244070f08120f13030509060702030601061706030d051b151003060b1207030816081303050c030a02010509011404050402040602 76
    0x2001001f18101106260000c1c10315440442141e0f0020024945612548103000c0104038006002e90850346070f007146503040c01c440c003440008095100504e81498a541403007425030000108400c81090381d0b43c1e400c950410f00c0b0b1440d81d003100c15444a420100702000c104800c80c8600ca0703008040c00b603040700c0032080c88480350240002841e00b07000310750280c0e034480552815202c2191b01d407141d00c4103e004174020a124030003802d04d038040544454944441500000c3c81d01034240d0003240000d080d044641401010381071038580002c401c0d00106040204442d0141960160790b4200060407060034141981c0f0300704004251a01c40110501071940c01c141002c41451b100d5400f055500d141001c09580d03203804e01516080002455401601030030f4295510b400c4213512503c4120180e0501c10503000204480d034001304074012404000605a80c41c40c81d0441c100380d0400c1600344280c000301072850260b40c100c4101c4c1d040e00700034a040103110130300c4240116540282d0700040c0d0000e10105001c0b4120f50005 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 437350215 1250 437348965 437349007
    0x406080a11070318031b05101713030201060b0409060305160807060c0503160501150e0103120807120203090a0c050603040314090a17070302040b09190c050702060a08070801090207050c060a020f03 86
    0xb98407030044003140d000070727101c103424050821040d80c1004009130307941c84650b01031080c90380303e8400800e80c0ca42e1004180702c80c0c0c010750445581207a540200b0010003030200881c4281c0d1881d40c4848002da440c0010668462a551042c030040c00015000082000f60074021590500804841e45510085900b0018000e007191101f24224212141020840300c0e00d000030103040780c0d440042540403170001a412107a41c40c018098805102e48155400035280c80c90014502c00d6910304014501d000316410001914650b96000301d026040030420700c00072a6203d0340c83c0c250000c109214543d81c03041030f8041000b04d2403a80c031980704003107210701d03081d480d09011800c007040b207000711020301c24800c4030030800c04982c10644100c0c82404d130034000c040610310360b43c0001d280d1303039594142142401042d80208803541d004000302e500080d8813000708011303d41c026214901400c080c0f442141070400994402d60745054950556100d201e003c5000c5a010748200720219005500741c00b5241c0780c1c404858030b101040f6a030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 437351465 1250 437350215 437350219
    0xa060e010506070203100207030201062601140603060a0b120706050c1018060b0a0308040b0a180b07030309050a2906030a020108010611120c030406080a11070318031b05 74
    0x4000004642c034000c000d8616050300200134144111945003900025408100100d0540d501d50000260020f45016484441a4200c0c2807206c5894102d002c0707802c641d04603603610030120003030301444580d4400290065000900d0100010022203080004030204040300c5012010321170100086111903105014061840107502103c40d00c98031007500e0000c2d52000003014000b4155000000d01081d255040b078210081d01520f1028401c0d241c2c0c41d0301c5015800354004c1c0c0905100020a0301c0000c0d44001c031001000c56812045404a003441030340d82c1d45d0301c10706601804260310341d034140c014040140320701e500c0075600c101c04401c0c5c8400c540c07a2007114a6407203010413000655000180c0d85040200b20120f032580c2c142d541e00066030078600c040d03941c0303249907030000002c1c8603000008c880500c04000070704007130240100454aa17864007100910200c002010000554101280e8180d52007182d81a80c80c03584e45030a0000a03082281030740030b0322130450350020741040c2050a00c01210f4040c41c419030b050f0b50007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 437352715 1250 437351465 437351489
    0x40b0c011506050f220905061c0503091005040b0406031401060309030e041a0306091b06090603040b1f030606091113060f021203040b15090f1302040f050a06 69
    0x11001528091010610481c00890410051300004142280003094800143c04080028200d040758000301c100e42c980002070741a91303507030030b01040d0b02d00458640741d43e00d210325481440d412a5a902c1c0d440c0c0c044d0724806400ba640c00c0d41028515405101920080c1c030600803920b840305d5950b01c0c0240505020300410541d41c000a0011030158807900a204146030151210542c140c103120601005007680038480c3d990710707138001c680003842d034003848030a002d10000d42c0103000004410714038580c80c25280030740d00d2240400708400d5050b0b4558000b038950098003c0341040d1655140300c030500c0c0c0c180345000d00c0b550b850611701c0040f041210343d40c4100180d0700d124504014101141d0000c1d03100707110348018052090135105041241c14401d41d103170340300403209105481a144044150560308e401c00c0c0d41c102d98440c108400c00500700c211408582450008440751401c40c200380403030b00324a07040a08050400c0d0450000041903490740e0700207032914400018108010b107044a1003200502704c1e80034003116801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 437353965 1250 437352715 437352731
    0x1c02040e1c211a0307091802060d320a020408100b040b060c34140f060307030c030608030901020c1e0d0c06030b0103151e0308040b0c01 60
    0x20000e0001e05160000940340007014003140103035a01c0006242610824504809800e2840c040d03001d074500040214207030f0b16901c0020010103003000160380220201d64070703216840703150311030281510f020320f9010b48600b0f5591000460600240a00341003d032003140801e034050b5580c010040b55501040c40380901d40303106441c4c020903c010b0344100d01c0342d40c0306035101410220715481c0683c0203a0340000024800a83d001d9800041049274100c1065220307203401c50260020039078400c1901118550943c20311482c08401c1e0402c5101d00240c500036003007664902c040c4c8602a854880b049280c15000030101c9449161259006000e403801c00d9802001909041001401c4200042650344400b8160007a203450070420051284003210340c05883d0818400b40340d6080c13244c4500e420904207078080c0410040090034150090107407024800000d041614011846800c10100070683d000c0c0c50390011500f1006103080060502640240c1024102e04400540047c440c1480001000703441c051000031301202d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 437355215 1250 437353965 437353991
    0x1f0c050d08060a4103060604060f150207091802120c01120b01051903020c06010f030c06050d0f0e010e07050904080a030c1b0305030402120c010c03120b1c0204 70
    0x240c050302d8003900100068001d101070003c401e21400748442c046a030050b07000303000012141242c3c010b440840381c0307100c5807540c580c0c50400340030f065400082901c050150341d00d007030411040210300b4803400c4001e16020312440301d00c0d0310900001c00240007800b810702c03224491b0314000040542c109401c034800d00040e1a42015582d003c644d802444005866040c1120400003502c0d02900b261500f03d810040104a02c5164540c660b00400c2ca10540d586c0040e1280080c010070b43ca00003044e001080c022a20342410000a08440301d864151081403401a8030342c20320180c101701400c1c0303401000004504000700303030600318015402018070744600404c445103c0e60b00d409110f03a00000751400707801e9003010005081c50b24080e402101c035580603403904080d05c00300f040801c01151b510300c1d02100081c400006100030352030107140f01311001306018083c0c0407030424280041d0501e01074040c000d0a015145c5240705805165900c508001c00001d0004103072884c00d0003500c103070580d940108911803894940da0175544 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 437356465 1250 437355215 437355227
    0xf04090510051f110a0503040305030c070e0103150b1512071b03020304030f030917030a140a020307030c020a05150c010c02061014040f020c0f0106050105160807021f0c050d 76
    0x1100311400c055040c84202d800440300105580b950a03961711903920500300040c001c10003400210301880c051512106000d8609091003096407185100108043c018004603813041e510044050001c0d000003848a2840c1c0824144a2035200003c2c0782c880c0400e26222688400011910071902c598035503542440912190000f040c150074050700591040c041440040c590544005525001c1c0c1003085003250b465148030030b440b40017480c4801d0341d00f010503180b48a513000b40007882c40801010700f0900341906c4100007952400707003000180c10000b84030344c1d140a540300c1c2d10401c806000041c3c040500002030104600c40c9500c21440e4a4140d031078200219252440880c07160b0141040d550030400c0149092810000301c2811026075500c5070f43c4000d102075031076991004080c1e280e45e074800740414100710b040c032900b100c46e00e034000350510108000c8001d88078150400c0b10703603040e44200040c2e2034035024004100301c40080c2008011510131004c1111000340c1044d210009503100f101240c59041d06003c08441c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 437357715 1250 437356465 437356489
    0x80702061302060d060509040302033004110d060c09030308060a0506031305030d0513121706040c0903080d0b0909120f030702011b050a122f0f0409051005 68
    0x2011004110707070001450140014181c8044003400468200c0d203e0000400a202c10303203084026a000144d41d00380c1180d556890100107200e41c40c030800d4000300c8030f0603c401200080000f0040014009031010035526540030050325a0040030800100c0c42a0101030b103104a00e01045e80440c0100000486924240986005883c0d0107040300b8203540354548120300320b0b0584802114640401d00c11118080e826100709407103511500d40c003018240c0d06040c600e950100e01148a4104210f03920400c60b0025075202154001c90240c4001a0042e03059004640000040d000101038110014128204541940254080c508102c03074901d140e458500b02e05a80350020482c2e00950300080c0451041142001c003c4c0d40d10400034000440c1c5e140f80c00b81445407100611027041702040000c102401c0c16580708404001c00c2d1100d810410a103000c210034100140c690140d028052861010000500c001c0d035000d85030108404851540c0b159218140030018020440d40d0341c0090303400d01c4001030030f45816a40c01d40 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 437358965 1250 437357715 437357731
    0xb0c010b06090d1e0f0c0905250e01050705060103080c0c06041a0f090d0302062d01050904081c050a11040308220b07060212090a0b01060309050c04051608070206 71
    0xb440c2c069a49200c2030600040304c07040c0c5900d901d14500c0104021035001c00758070b0310400c028107405040403401011584003902c2c001c40d04003880528407242c0910800f505103450310703007002032038012082c00403600d622650800800358010600004100000311001d8100340c88810251030768146c40030244462070060b4482c0050b10100c855100208100350b01c02800c14074901d00e125803426000c04080750816414510072401640030004000803c0c1820141017000f0645080c22110f0300c0c1c034030000d030000300030600506108007400c401003400c1207070304821101010310b60038581348509145c151030b100500084550b0700b102410300400d42041e4000c1c10890302070366401282103040003015480d00030400c0c031014040c4d031540141100481c94401160282000300c0c850b44015a40c3c01a503a119400680d01500103140c2d60300c100c17160340019548000460545880e8900018a40c01606083c0e103051211816a0b410920303040074410320115140e1410b000850300d4a40d01e500d61100402280d850b141140d1a030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 437360215 1250 437358965 437358979
    0x90d05120c1b06031b0307030617060403021b030c090a0f060303020a0c060c1a07020c1c0309080303060603010b0703091a071209050f0111030409020f1b0304140405090a0c0b0c010b0609 81
    0xc500505294080c64000520703141c0007030a180ca03504c4500441c114a0003140d0290711110822003015810008402ca62400064050700c40e08fc10010a03070b95900501090300c20b400400000390258032030760140751860903003542400307031a03600c0c10041e407900c00c8070809407105144450b0100d0402d000c1d20680320050b5110442643c2c070b00849040341180c1d24094480d100b1401200b9280c03015540308110070700d181000c0c802d03441c030050030342c40d010300410300540c4805010340003441041200d940310000c3d01c0c1181c40510103280d44903024034003100c040403c0d42014880d281302440ea14008040400600000c40c881c07510b58006a800600c2601d000c081803060079842940020345407680d5101e428002c244081c840101c0782010745521590060341c012401c000014640807800c0c000c4d00300c40c940508446940d1101641ca41418620342140300901070388114005e60303c0d030020521a13074080100d2100e1a400c0714010307003c540c860700100e445a01ca0300b50800740c2e60806c01100254500041107505001c0010329507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 437361465 1250 437360215 437360251
    0x218090303070e0613060908100b031504080f0304030306090f0212070f0c05060a05041a010b0702090c1207080603010b0f091603060e010602030903010f11090d05120c1b0603 76
    0x12143d01d0300b41e0031801c0d0000000d001c8040511248802d50002c1d0803a621121162400c1040e01403030810045010146141032094038004d6890200e2114910108504090400d03176079400c0900c618403694201d0b42c4920400002c0109155041e0b00c408152400c41c50103100951049620006900403001c0004142c0c1c958004221100c1c000c40c047c0c00a0380090400882d14801c0d40c54490034200104c8150a0315512901000300700300d603003500d4249000d03009203440429410b01315180c0d403d0242e0b09000f03020b5011080403910b241d4101040d03540700e4020010414062030810002004141d0954983d0b00035800d14035404050b01e00341d60b680c40c04a1001e0042449036441d1140e0a604442e0342d200c400038155103283c040344001c130030000f480c0030303003403a400a40c0d4910101080c1800c49414003043c0c09194035103261040e0a2141c0310444803400c004a4660340f140010f41411818210108140c11007001d00007038804400c280801e802c12003800c1c2a4802d0608440c40b41808014481180c40304400400c0e4494 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 437362715 1250 437361465 437361467
    0x1b011b0503120718090e0c0402032205070f080d080901050705070807060204150507030f05030c0a0509030f01020417070b0c0c060c0118030302032505090d0f0c030807021809030307 79
    0x42581c0f0003c5403400741c403010910064a0310304580c0c0c0c0c01409403140c1b940214a8111401c0166250500064400b1891403a2522180b00200d500903040d0f00894541103c00040c03050420000340540320f252840240e6036a2101525900c00551a101012404800010308007020600c81d0a00c20903403622810f26104060390780e68585d501c41c8104490080d0300340404100422694003982001000b44c0b81c42d0356034030750707820043c12403840c40340108200002002000302d0194400e068400200690801903111030160b00041d0400c0310050074020951300c041400900f00403111881040c400b94202900c40440d00da01d4255118412003200c1c2c50250720202040b01142001e800810040101700b000007544001e01e1910040e924600c80c09400103078000c428041510001c0c820050496200034400340d00700d1000b04043c007a80244181544200d43c109150414882c000314080318107030703020048000c00d0741c803417070a04556004100d09a01030071010445001180b801d690b081e02504081d0029030465030f8040f0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 437363965 1250 437362715 437362747
    0xd0f03050a060e1501120516140a09030f1a0a0c0f080105090708180613030906030b031e03040b041203031518150312080f09070617060d051b011b0503 66
    0x18958108822460140d02d0588280300e4607005007224904c08d201084100001480038001291a08131403004100c100c80c1031f038000c03032140c04590384032007500c14407101800c040c680300c0958074809000e0a0f69500704540c010300e5074402d48001c0c0d060307155401380784080901160080700900906800c200707154007251100d0b000d04c07640f071f51020b07041c0d43c80c0b00307280d03907858040d030514401f0b4030f02c000340c0211003400780c0c200342d046500d80018140c0d40ca020000a00854000380d0b480b199071100c0c0f032112120381556004014180200c40161042510107559540e6580105100c1c000c0102c0960000e46410580a41d68051005075011034000e00060030001c91109442c0d401005484200d9460080f10703040000050160391a1103210b06070394441c114030b0b1503c0480d00b041c1140043c1980300c0c580206106000007a003080b002c1d100d500d40c4055515007030307840c5400715240d56040c20019001d441900700c0180003644045407002e401e08203a0f00d080c643c00721440244020a20b0b440002c2c40394100344040724541d0111a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 437365215 1250 437363965 437364001
    0x709091e021f0503010311060f34050705130506062b0c051b070b070620040b0301150804030906050901020c12010603200604051509030d0f03050a060e 66
    0x2030014402e080c01c400700986a40e001d00781003010800100c010000d001c0c90010f070700e05e0210240c0e01d40d0300d480d11407100050b9038455502c042280c07405070103a070300031110b4407400d03500c24258600303d00d004010766042c0640d8a400318443c1e80e02c03038014844600c3c44280c1c5401400c1c090703540038048504141c9080e0401100c0305440e9100748031a4090903480c0c440703404500840c2041d8070f0070b880d500d035a001e603c90581d10030a1440303030f15402a80b22140401065888900b00d490454105400080c4a120b0280c00d00b1b920034502440800a000401c01043c40054240210b04072180104c0c8000740d02c1010009a441c0c0750f00f00c0c1e026010420103001003040720301400042c640d01d401441a07030450300b84d02c0005001e940740307010b0043d1640e540341000c0c81003204100040d00b42e0f4a48002070303d07807800d04600180c0f25100b03a02030140502c1c3c109519504c80c00c403050545040000003400e03150300420080005001400c080d511100290410b00840c20300b600902c1407009907520b060078940c0940d00c412405003412404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 437366465 1250 437365215 437365219
    0x1c06030b04021201112a0604050706030f0207061a030f060106080f0405011d010b01230d15030b0a0b010801051009030803070504210c0b130e0c0f07140709091e02 71
    0xc03812a42c100d02c05c07000401d00b40d042c1c41c1e104140b030009803600c181d0300c840040351400d44e9400360307082c0000f1890020300e203004c407070031490041186400d418a08019004e4000000c1c0003c4c04e02c040d603c0070103000b04080410000690884640028621586564203402c1c4038410102d038074400850030504078510030a40c4180918000300d01e940c0c00c0c0301c10113540b0682039800d80550b55102c010006941c1d0140301c030b06101a500701c4004580711039003984201380c8100000003080c6955864040011b0b540c1c80c0310040219040b42080156241020021024044102449000890400010409140c5444003001003180c0350380e00807556065544508141e44090002d40030321000344000559400f003120080c107003408140b500041e00308030303180030b036500101a009240c3d590010701542c1c0c0101c0c0f4140320001102c03001011404c1d40e40342d0410070407861145014405011400040b5101400b8a0220410401c040c0400326240d29940d0755a603012102e0104004205480019401c142e42c0704da080c1c000009800 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 437367715 1250 437366465 437366471
    0xd0b0d030c021e0904030801080708010608120a030905030a0302031006030203010803163906020c01390b060a060e030c01031a091906080a020a0b130513021c06030b04021201 76
    0x15500c04405c941c100e00041c900001408031000a01c178850003400c480d8000c1c004542040c241681300c42440d8001c400c015408a44248024883d030450030340740f5086801d81f940d074602c074080240690300c03c0795000d520300114074002400c1c0340700340300f01c074102c902400245041040b403100c10540c442c41c0441c1a2480742d180300c500c40b42c00c2840d40803c414400a00100300b402d0728103910091402d52a9800001550400b001c0d116903a41c00c60703000d05086400781c0d04034079840b64103000440303003043d18100b0840c140280c1c0346c05010000c11400345d174001c5904540408003107544000885e003050200c25440c0c2c041d0885804581603500940103161001c406000300340170101c4c070b200421100c203070448e803030012682e41c0b041d0649148043d00c248005007001030040d11000d841a004250250814070038402d900710002410380082e41074480d28005014020000b03100030813880c0e255006500f00003080100d00c0c0342c0d804800c40a90079482040112a4440c00c00c085a5550340c00b000294941c03940650040c0d52 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 437368965 1250 437367715 437367769
    0xd080415110301060e031b0609010f050f2a0129010e090c0702150a02070e09190b090c0d11011407050a0b07170f0c030a09050609030d0b0d030c02 64
    0x7035000554003070100e079520490350140890401d464055014103180040410242005240c2c0301c81b400c403044040203090105400105540848151185490514002001050750070341070902e25100003c940300c1800c01c050481a840c0c000e0b00b2a034075a10103882c1d0f0300626407107552994848901c0c46805005051110380c0c50f4131100440c91100c01210200250701e00002c408003140f900e500c0100103d41130320200b41c28141d4007803020f9036898680c0200c000e10044080040c06520080028910002c80d813501c103507540c009031800e062500001d40e010442c900400d4040d103042d091003100c40f5811500652202c40e003a00941c0192544011001c5016101004100540c00f007002000786030401352249402d1203441c0b400c00d0340244240f010808200c5a2510503081c4800e4101094003140c21200c50303410b903603890315100c2e00c0d00014100748000800c01c0c062031040040d0680080b01404404072013103002e00025905904003c208a11f691005011070302c1d20701c0710400340c100201a442a080a104000c001c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 437370215 1250 437368965 437368991
    0xa0b0d150504050d020a0308061e19081e03042315180105090d030e010504150908240c070c03060204090207060e01060f17100c020601170d080415 64
    0x300d88155000c1894481c1c0034401003080800040746a141288041d10a060455030024000200500450f1050800601d000584203031130041d10b903110b10040032202d0b01c810070741c520002540e45104d0060b0071b0044031a0640e0b101910002d80681c9045003000c0c5152078284500d48071511420305c404000031800d00030004460700c8004510079691416030720a074441030701004041c0c184c0000b00b0510b0401c02c043c020040030b0b0b00c541c5144800560b240c03d02c2c0f0301c1003213610012603081c007659011160030750b820102200066000180b032010780d2840410f680c211460b1a483c1200301c0145100310700e11480074000580c103803a030800640041c510448541d01c0315603480d2580416078101d5001407600542c0040d003401001003c2c40358a00e203407640e0000340700c0c00d031500000782c0f45204240f10b44d02d4401001c1c4420070f183c4206200d80c054455289504202d00229540000e590720b0090007150340700c20400d6000301042c607001804849251007581d0302805581d51b580c7d100c01c44100c40c041103a9442c0c40c0d1203c8141c031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 437371465 1250 437370215 437370233
    0x906030907080a05100f09081b10051017032a07090f050703050f091b01030b0a032405010305030d091104050108100f050c031303020f0601080709050a020306090a0b0d 73
    0x119001c4ca000b4603010004c4040d44007144c16404100c407000d450900001d00080e403080c19144494200d844c10300c0f4403600e900140e404d2000646040700c28600d851308101d0703011101d40e504010794000000448400022f038132402e0392403249030450300440605d000300d14085812010382c00c8800603c9404e807891142da80707130300e8004d858084d200020083d0311002006002a030503c2101c1d400400c40c00841050304003214a01c0e1501440c800b00f542140d103c1e030080071585d029822400440d00003408072285603949003014a030564205408800300c1c0364a080008065400e40a0300d4140c0350400c002d03510740807142140e00014030b82e4040499072401100d0500441d0b50700d500c501c90080071024090070b4920407861440e0101d41c10103041d14561450300040c058404600307000d60350311031000c01c0d015003104441d090a070718100d4089040d105031710500c4004140c81c0408550780017118074001090181ea00e41c0ba680005071f00085030420341200300e5800103480400140c01242c4454000790130041e402c0d00e035803603890f08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 437372715 1250 437371465 437371483
    0x2f0a03021804022806030b01260a18052103102303030706050a0608010c1e05040e0117060a06121b170f120403020904240219020c030c0105090603090708 67
    0x206403104e60200081c82e00b5005480b00f80342c0074a010484441109486204402d00a0380040300011030300020360540e07041e40c03044680e6121803050f1080c0c000c0610b01150b5a80440030ba110034078a81c005042402c2d100301003540c0c09488900e07480801141410071103045002400b2010750704c6800c402c41c43e000c603103040c40103004031805a03c000c00c1c0303403030410704050a0300c11070360003c80c05070f00d000e04060459600526013139400035051070f60140d05802480884507409140c00460716114180c000280220311f00002010300b0030a8070139107042c2e0355580040c0046559074803c2c5007400010b00501000108581d441603586041c58507141c40903501c560305038400d5448101d142160350f010780c2c4103005029041008600c0b4280051215150070304503400b0445040300a44001c0c4001244081e80d690700010b44440070103490111401c64544100071000c1600c1500c00009038003600460390701600504010030001402c6406031605840c0416070400c2c025a43e0004050480501035248e000c07803c0c440138040d1500f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 437373965 1250 437372715 437372779
    0x1090605040506150f03030f0d02070c0b0304060609061805090a06020c0106030215031e180a03030f1b051b03090d0b061e010806060d092f0a0302180402 67
    0x21514060703130a00c10300404491514403580c0d00c036844041c503580c000115510011000300150b211100c901200010b406000300c000d00c6503041040103e180241400a144070b680201c9040c06020f0fa5a0451000c070f030010700480c010507011000c03000740489282c20958124a29004542e00048980c039090100d800030b04981c0722a9440e00700400a500d001c4e144100c1c00c1080812803855400d2101d00600e440d403040040c0c488030880c00c4001410042000018010082e0000944504401524001b002001400070f00c145861421888103003414820040d80350100c0503460360b40c03a000300c0744030312a0000044030720450b840c8420440c0c40126220312048036070b542e20070040102a07040a004002a0300f030041c580250504009007919a00d030b0340130b000103400007001e03900d85981c4c030b0001c86040050300c203540d070140a0010851404a05501e0f144070712212800c0d113142078000428500401000c24214172010754490b010900f5041e005103c4600c3d150014401890b0300d150605001c2c40f40d80c0c103d03034040310302 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 437375215 1250 437373965 437373973
    0x141e0306010e010e0303180111010905060105040609021822110c2413034d2d0a15060e0403020613030e0d11120102040303170603010906050405 63
    0x400d281d608000c00c1d005124090034001c000780644c4000c650703603010300d06943e00c2070003e660b0002180d900400744180c5602c03406c00240309500303179030510a03500c680c01c0c4112030107245450000a040c0f035440c825505c2c00390100500541482c0e010080040001200b520762003c0c01051405400007480351041010003004500c0980c1c407004030180da81c0c20900740c04c5c0b10042020403142d40c1c5e0106200d85c0c6c8007940c00441510a9180403c02c0d01741290b01d2030481ca14000d04000021680c488030700860b0340848580003038000c00c81c40da02801c0496030000f0890b05c15540340c1d880141c0c455454105079001440340c040301c2220414240f04101401d1074194403150a5941c1040f103503141e0b01c3c0110034010070014014080320500c4c035050640d802544c0301c8000b01860f070b01514640c02c0f841058070031303202d43c000c075180200003582010303030f034203200308406204007007648035805081c2d000381e00c3c0006000740c0e81226056281e510000c00c440c641d40005c100020300703455042d56a280303654002a964840c0c5400740d40510010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 437376465 1250 437375215 437375221
    0x509071d0f0a0e07030f061e05090d0f0e12030c1c030e0c0f01030b120f07090617070b070c031707051006080d05070203010b120105040b0106030c02030a141e03 70
    0x5181100700580b4010101c0d0804421541180002400204981d8010b1040300d02841746d04000c4014003c0c4c031200c2c000b5a00c550800e0f120150302e07801c0940200b002c04e0030b0f80c4810502c010169500000981444041840b003070f0300d800c0d1072520024884944c1860019a468108981c20450800502c20b904201c035000001480b0422581840f682ca1094038500007404102d09480000707007242d0199882c141015240d40e28101e0b0b035141c6460f40c0c1102250030040740c0c40c40c01c210041507200c00da28007a41200602d0000002032030580388801c0d450102d910800750035894200200443c02d40d000341030944802520701c4c7e0000008070481160507410b88103a04941e2220403918041f810300510389030b2000303418180300d002d1102c3d01000c03800203407540c5c09083c226a0303001ca030b00c0370a024004201c082c503403081102007868040081900040e03c00e80c41040c2e07014042ea00d884040e021a440034a102c0010b03442485030f03940d41d602940d1b9240035041104052401d0000038007121007600740d0308190410b02c40c404014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 437377715 1250 437376465 437376481
    0x209011d070c0206070b06010302070515060f031606110304080d030903120218040f1e0903080105030616230d06090f020f0d0902010c02030f01050601020d1707030509071d 75
    0x40c080e0041c80d00e1801121080e00c98002a41038010480003074a405500404204168041d60461343c80607802425115015051203215007c108103c80040c014141c41d803d280c4d80d860041213800303201c0824000354103070504060040714a00d04e01c0081c81c203540320402000c00c0d85a410081003401e860240d40120300201c491600510144800c0510f20100b0700501400124182102d2200c4c10b09609940000e074602d101412000500407000c94401400e6804040c0701005841d50811691280a9100c1d81d1103a6600d40034191340e040700312100c40320100300c1403150703440034401c0c1440c1a0b9a048400c00c103604006d50500b13004154041c0c94a2154107944810422180030b80f40118204416403840c11803c081e1004118038042c4110102c5118441d42c0e0b005040841e030045000800c6240c01408071040140740031203e49c02480140c4020740588900c4664100031441031202480030300207000314007829160396605034040d15000e012448107009840c0c001c160350140045155a05441c050010700328102a59 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 437378965 1250 437377715 437377769
    0x61c021605010c1e020d0e040f0606091712030106050c0304031e050111030105060d090206040f170f060402010f05090a1703120c0702030c09130b1005040b100e1507020901 75
    0xc0001103001e0300026000c03034540101b004291900541040c441d510010b0380080d0040a2141d510f10f6560716010300400c0050380050303c40d094540740e40ba0742001440c0d41802e0760741c4800324440380a0301c010810040c04001e00c10f0001d001038031207510480741031980381e6071420300003101c0d0b4071240d4a42c0301031125035080c410240144011702c0041641c01e855941420045000c5104884072050455103403101c220841d00c45001700d40041004020b4554019100e10303958441c41004041100d00b8810000e080c010100e002c2000780c081c643c140c44200b102c04811b5010781e0340c0d8005409950380400700300303000250a1403d440007500c10350040080d66030b2b506086d0821110740c0d0003a0080c40c10690600020006860016000340c00c0801200c16110641e1900c000d0031a403076030000010104c00d00c010901007080201004001503500c1240c0512200400d0000c0c01041b1001864040006000c0300c2e485545050050100300910a40311300c462801400c1d8002c207403100b40a901c1102c07420407021101c0203541c1e01c05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 437380215 1250 437378965 437378987
    0x90c17010515030c121006170f070f050909030c0708010e160e0720010e010f0e1b10020f030c0a03030b09090304030303020306060d09150b010c02061c021605010c 71
    0xb41e41074002030307040300801c1c1c0e0b5488a0102c940110042e241010450004210404902c6690141805070503200c0c40341c410f4010748140d44010b50301c03440944541002c1d012512405460f000401850010f14000402c6441700e07001d004941980403c020a500140003030001e0f101400c402800031a5003511030100703901e00402c81040c2c0181d10341218082c40700c4c0d943e0100240e00030400746030206d105030f40b2412900060901c40700240584d8a8007400740c034600701c103420185040518110400c98041c400054540303500b01010f6480c114162000c01524501c1c1c041c1c520104448140304031444070b10b0546005143d81d021100189246d81328001183c00c0551500036150415001d403040c211500b09008400d68901403404002c05054001c40000c0c240d440b52002d0340c3c819201c80d0350610140d8181d003003504445158940080c070007810b2045496865000303c1024552580c06800140b130b04805144c01d0780c01c944801805011646c003000700f49004e12036064503000d114020000001c1c004007101d0f014004219407 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 437381465 1250 437380215 437380231
    0x6010f05060f0409050c12011401030f020406210b0406030f061a010c060903030b060d020a02070b030c07030804050703080f040e09010b13050618011424070f0303090c170105 76
    0x80209280710b12030001590101c07640d21202081503142c0402080041c0140e9a41145c42c0c103506000040500440c0854145500280c03401c12801e17001c0f850032010f921807402180c01107140b02c28240c80788015180000f500c14002240006e45546050019003698580d6006540500ca018a504140051031003590291f0f098000754900e070030100c000103041081d80580c0503013503942e5100700e1814103020f9000b0502c0304500a04c0c16646200c0034901c4c5000707412601c44000184603230701010420101c4501121b0003801c414240d11708051840d0b13011a01d19100030700442c0d107070060b0100080011100700141000345c00344038955860314100403c480b40503034000c24411007030b0704055440a07c3e49504004444a20803000081107070303a15040820000e10003000070020202402d00001901c4403205035005c5518811943c211035028001501000c4060b03004840301441d0081200313800080401c51800307441840b0b803d0101d000f840c03e80719255002060741c420344a80c14401c80c00442e541d000c1c0b0585a105501c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 437382715 1250 437381465 437381467
    0x5040b0405060306040311030702090c072603190e030a09030b0a09020105090402210718060c020a0b1e04090506100c0c210b04050a050d050406050306100318030206010f0506 76
    0x40b4002a40c80b4000340c405024848030b00f014080820084c0115420f0f03e4000d4125541414000f803c8401075220002c140c80c40c40c0d8079180b0076210088038030b031118040e405600460446e03d07040925007440c040d0b121511156691824070184070902031000d00450411500d410f50b0080c914102111010002424a803001e89407170741d14401070783c0141c20b40d551190300343e40040c1c0364006001c008080505540400c00d80883c1c83d41001112a40300745022f004d284051603003040c1e80d45c0c90000355181d0b03040c04802036104503511014420300702d480d4050110310700d860442126400c6581e4405080d07a200750007014540e41c49108215007420000051008240145811a840c103a540c03246501400c55024844100754507502240c031a401710042e1000c81600f003424030300641400d01d0441c0d82c1d103200c00000c651901a1103606241a400740003503a044640a40f1807920310b680c0c0004000d000e00d02c0d50501c10605940d0240e281034072040f44040600c0c284030b9002803000d54144001f40c00070044075031011b0303c1440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 437383965 1250 437382715 437382721
    0x6150108072a02060c0604151802030a0605060d020603010608070306060801140f030c180603060f0603061305031b0f0f070506070f170a21060f120309031b05040b0405 73
    0x5071038050000700b0310402d25101201480050154400d1720b01d106100d1145109120910003035500c12001d10507014400c00410300840700c241c40c55100309102039070603080203400348046440d40d0400c3c0c1d8420f80040036a5800c4615a0001d90660400c0e0021000510048100b00089806129160280040d0f040031556585401d142040f95400c2894041c018a000300080550b92001c014080d8402801401584050b8014594001c119800c03541c03944203110366800700711074403030034000780d40034500140180c4031580d40d4010703520081c609000226442d00c802c21510b00ca4640b540108000102e190703015200400d4114000d52500d441d40350a85c142c0d80001d0740410199456004903045940d0106e09100c14a17400e040400c0036003807441403281ca034400000c92840e0341e6444955088240f0207200c109002400d4849600c003100ea043c043d00828000c00b040900100480100341043c00e8480c1c90007035022602c13a83d40740c91036800c00d4030111859225080c1031046181034080c81c800c0e214265810000b0346 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 437385215 1250 437383965 437383997
    0x606010e060405100e040f091e020a0e070507050a150c080603060a0b0406090f02040303180305060a0b03100c02010606020d02030c15060102100c180801021e0c0a050615010807 77
    0xc402d600c5954420700c00c1018502c04039000e80c0f1402200c110007003013001010701c0c54100002502c220501120300da80c2c2000000c601941003181018100e0300030709004541c50526200144a0401411075004c1c010700b80410400100d0401c10911300b94454966607a007411040e0400b020369142000c00c606000c040307810081a40c400194103a40001c109202144007403080300841c000b0301c099000b50b03141d242030601d00c049642c0903070000c1c02103a01c2a511016010750f414102d0350020400c5c04024440d03040500419003821207904505a1600000c007500c0228407501075a070200c51010219070f0150351190001c010b4035405210340117900e000340c0081e514000d014259951100f004540b1240d07030f00112800b00c1e402d644200403588120702c00510802880700007140260040c11350481000c00c6c0c0e020410086044070b07060080e9841130740003034840034084516800907401508240c01001081c490440001c0114004100040c055a00e81b100190b840a40e04001080500020301d03030f07800c3c4100c4060b038407500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 437386465 1250 437385215 437385217
    0x3041a07020411071502180d0506090c0d080403020f040f050a0f05011437030516050a1d18010609050a05161d030313082a10050309070306110c0606010e06 68
    0x6407a001d00e006a0310812201240950107d0300d41194000c0382c2c11a0090403c1000100e142c000c905e400110351000703c1650410405061003c00106140700a100070401400c1407007071989450001840440c8200c404441101150400c8900d0300f4103a4036489040b204441e039105243c0907200140794403800349010703c041403105030200c9044507026100c1150481c200412010429008140048280e69695a01b4080c0d0f0f107640008403584880305d51180010186441c1c03000078111413102c4903000b09100318420b0000c452070014540500c5400076080c100c1c041a080c401e180203881c101d000020b403802c00c403071544c0459100411181d00340c40340c041440381c00c43d0009682c5044480d0b03a21900c461444c45004a800d5026900c5020354140c0c0c1d001c0c002c01c0c90030021900c03000070080400409074089041d40031825001d0707603c011503081001d05d034541c116544580021a80041d82000305c2e1089540c030f40d01c500c11181900802441041d02140140c0c200300c060140c2034004c1000d20303240c401030755100000382d00703 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 437387715 1250 437386465 437386493
    0xf030510140f04020c0d0203040f0501180e061f020f1011090904060e0102161407060e040b060f0a0215010f152006010b0913020301150c030203041a0702041107 70
    0xc5040c01d0418000142d43c0c68045130141a41101901c40e43c8180b110041c0d6260000e02070403042146500d0045041c0d4440c03400301d80712004890074140300914100b5410003080e0042c21650b006000806445191100e010b1792180c0e00040f40d0040480603044040141804c3c08d400c407015034a0300340b9a4480c1c1c0002a4000d640300044101c07031000050302c0c1c5140000040c51207002c48989540042020445191100701840c1d113507000e840080e801c441404c1c9166281c149502a030b201045c0241d05e24010703810190302200c40c0020207440f0f40e1510b400c40c00c194a994202c280c0c02c10041e44680c2c0c2100f03107880303681c13142401484005922882e0b5400c09905040c0c14001c000e00d0001c03c050704885138035103040c12003c40f460700d0300301d030a580041d41c440360502480d038800710b4924003030403d4620940040c9500e2013128100c1d40d000d1880314102c20307140000c580d07448102405904504c401d000c0801d4001900450f050403880482d00d0640e110101c0c814842941c04c41060b5181e150000e02c0010040307240031102c081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 437388965 1250 437387715 437387719
    0x80606090105030717010e060f181501170108010506190b0f0d0b060c07060845060903070c090c0c110415060c05011d0a1506150f03051014 61
    0x61071380d480f410b040303c0c126070b20500703440400b4042000060303448408101e030340100401d5132101100001e540601841d0300318000104051041d0200041d80c08043e8600c0190150301403409102000080750004090079003a0001c092595441c1c040c09001d00c0d10303006881d40e8012142200d507005282191044140c020ba082d041a000340008084c070600320264001070383c519000b84115200c1c2800c41034107640d840c40d40a140c020449400100381c614050b4401140813030f075031554820003180f001f048061090001c110403194440a051503840009061040701c0c03280101900a680f502503900302031040c03050591040101c5842d00c03505010031a4008141e02c149034200280381d0944103000e02190003001d07902d045414482c0c40380c00c0400c146901204001d00c2c0317800741000b481018400d042c0c3c1a100d01440403520603990141c0c80702e10004e12507400f608940001c860000641c80d03941c0740024001c103250345504000400c14003e103005290148205900544120850000d16040030b01040700c00d4103d22000e8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 437390215 1250 437388965 437388967
    0x5030a080703050f0904020705010902030d110d03020c0c030708060702190c06030b03100606031d0d0503010302090916031202061506030a020903070b040b040503100c05071203090f080406030c080606090105 90
    0x141854000302100c1176050302078421580c44090b8103006000b000b444070224400c0c000c595040c0f04603440341512031000900e2030060541080c94100540080d802101280c0c3d15000701051420180e0b000c0c0080401045020b0241c0950329060380b00a040c4460400c4802d0080c058000c040c0208214181c2d4200b900d15038100001e8036500302e4002441c00340400701400c84c0c21b040080214400d030f895045080c4102070760001c500030700c6880744100c0d125100d100481e00011014001007000d4036045103155000702030081551815041c1c0300041c07032060482d420503039001c110b00b40c004140072350400006500c00b2001d80300d18200c21202d0300082807480060702540704207801107aa00170b03968091000c107008002034086241d449a44070f400714100d400903c2100c0c0301b4001c01922402c404c04500030312440105030380c0c6552820311b41c0d0742c0b859018200c80000e00c08140e51003940600191605081c0c044107030080400544440c0303070000080139100d140220b80100924041400196210b074010b40e404558242822 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 437391465 1250 437390215 437390227
    0x6030e06041e050a030504060306050a0333020c0307140c0a03080306010216080c01090b0a020d0513031e060b03071a0c0f060a06080c0603040b160e040e150105030a08070305 76
    0x803460480d84040c0c0603003d40104400320003090f8001000b03008a80c0180c500f44686680c0701c0030040160800e03c005040540d505002d244015060a02012b0348012601002500710b001d110300c4049800c0715081014a9200041890038000f06082d000c1c4011007920051420402400101c0c400074604c3c8001860640c0100204040740c0c0240000e8184208814054510b25a5000007030b68440c07c83c806903000c04c031455804030703080881000b04c03130780410981c00401c0c406010303040c1101c0d19030001400210b4050383d6040400001c0c141410100c92082160032030340300e104242005000c8901da41d200911030313800440c081001400000d485100d10968800c06505c80418008907800c2c4600440029480d000f80703820409415800c5d40074000340d440300c1089a12282504003071126070311095401801c030080303007400503910060010908096889a1806802c50380070f907000b00d020742c0d0b100c65020700d42c1e400108010450000d004519401803400310014040c0002c01d460b40c1e113061240686c06001c001c000188 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 437392715 1250 437391465 437391503
    0xf04020f040c021e150a051e09190b040c050307061407021f0207080f0303190c090302100914030303070c08160516060806091501050a0215091606030e0604 68
    0x6140c04080d0140d5048100008504281c0c54217400d1812030007070016100414022240c501c5101e11400300f100380000d041d440c01c1c03003412400c0030040c4402603510412101c0c03207120455003420111684902c4800183d800e2521b801004954103420050080d8805202045002d9000c400c9034806594104c0c0300b80c0c0d80401c0c2c008a2003460103281c04a00d020300444454500c1d030350004103d4101d91342401642c070604030048251740c0740e1001382c40203001103c03424146a03446a040e4014031242c180742c145030300c5569480d17000c034a80e94404903040700401c8501c074080180c1650640d441d036800c0c00440c00346242d85002c060290401c4079600016002ea1303030210300c000741c59224480900f00e1503004002c5808407040441009075003407850254500060a1001144441c10a00095030080040d80e000510689c401001155641c00150f5207604511580303107202d103c02104546540503081034400b80496414401a60340361140c50b90141c000c0601e08805500c3c481c0000c922a50020f90201d034100920381c038100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 437393965 1250 437392715 437392723
    0xd0801050f011103040b1c0c09050f03010219020303100602030415050c0a0f060b0f090601020c04150f03050304050103050606070b1617070c0b010501090f03080d11041206050f04020f040c02 83
    0x20f151095220001e000700d500307109000034110713280103410f00790707807100d0890b40c800d0590320a0409980801d2410000b4802c1d49400750908021800180005007814031a00f54034500c0420700c046400980c02c00010700c10302548002881d80904440c2c00154540362038144411045040c00012900300800440c2e03681c43d400043c040d00d1040f80e08001c0030300290005042103c000c01004003603511840010300026a036003000801d0318070840058002e000501000c00900010308a815060009102094004a2141c00341c0310070341c0c0954011001161034a084c00005002c03250003908041c8100310510598000620b841005a0301164918502c6e11500340304070191600404481c410340086085c00c2080b1180b0f500c0080c44176864000c480100c21a640c640055980048a014004a110642000784041900d6200030300c00401c0000d4005682081005070703100d241c01641044003440d0110304c1c0d540074460280142c41c0c00010911074000e031070800c3c0e40007030000f0b403604010b103005644030141001070078003e00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 437395215 1250 437393965 437393987
    0x61416020c0d050a0b0106090e0a06120b04050c040e240907090f0209060a030b1305070f03090203150412020c04020a090909050c31020703020307031d180a0507020d0801050f01 77
    0x10240c0d0071766584a030800b4080b0015070203610020001c480000350600001d00a10b000c9503d41402404030503640e4958030181e0400420a0f030f801e22803003c0c0d401140e210352040624500c0200d02500c0021458040e10301e541c040603c0e0f803004c4088032014040000c8012601d0340072034064035000104203000d403020201a000703203914640c3c0210045900402c0e2505600090015078003160503c0140c41c1ca1040041100c8003561000c0c0020751042e01c0e904031a00070b03484030703680d9400182101e0840307004582e0f2a80440b0200e48c2160440141d04850b001c1300d8040241d4644581c040320158201440782400404403c214404c20101d80d48070404c05041c8981442204507464005e400d0601006409034090a448110310b1520310380f441c0000c81180d00e0b89a031082d56180c41e130550296142074840d407422a014040f1800300740030000401142c00444d5038105d46245c245000e00340f01301c42807410304079180450310020000400d40d00510b610700c3d02150b000c030000c0d0544608859030780503140c40000403600c0344001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 437396465 1250 437395215 437395223
    0x912240604140c0703091d0a140108030f0f04050904061b020105060607021e09013c0e100801020703022d060a1a1e190e0a020307110604061416020c0d050a 68
    0x4031701d940991030400703503146124a644440601c05100500d416031642780091056409030781042c05610700e10b940020080995a0084842c9800d0a0b160381c0015182d220603038084520b01d035240440b04031030509800140050314980000c100f030b441d00f08007041c200d00c0f6030740c0005c0c800d4900006180c02002d05403440e500c620b40113032000c1c4180d83c440c030790080c0400710b03071841115200302480d40c0c80000c104000081d100d808483d1030b80510916000b40444544005003102000201d0707402e020030b500c4c4091020700300c941d0080d401000c241e51b4016803c103515504d50344001c070111205940d004190000101103810800b5420700281b80c0050108024047c2c6411341400e50000b418002400d152110001c400344070401240c03c2a10100d4400c101d41c40c5c80e50f50321910a1400403840015403158035030780034651007180d41c1080d00f07096810b02450390521408443c105c03181e940d80c45070005410300c15122664803400101030b11f800d030082d0782c1c1c1c065551810640454800c0c3e034154111010070006002882d895070b40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 437397715 1250 437396465 437396489
    0x80d140702121b030609071208070f150203060906060910270f0311030304080a0b070e040912031b02100e210d0c0504030c09020912240604140c070309 66
    0x380702c40c1160440c10038500780e132007440b9000224011844c08a41310003194070100c4210000c0020b56a40c00140d0440d0000b603802050f0151408042034040342078008440751117000507504d1900004100c024030b405411240100f006104030700c03940e00c80b0246807220340d0307032810b00f400070407001440c0c01c9051903001c48202040d204980c000640c0703241c1c3c5403100c095a01c50f80c44c041e201e410440070316680340902d02ca101c589030301401e03020000c075150b20603058201410340f40c460300c0050408041000d0310740340d42080301e0301413180440c1c42c10355926128006146904284413210200c10000007542c034010207000481560b03480201000c5c0640030000990440d44206c001011004220740e031032216005a12015015400e02015204030f42c420307030455007a294449070411000e0b060184041c003c1d000080d085800059501c440d110724039040150040f01700e40d40440300440b0000d0700c42d40c01c54641c050400c4d0702960030b0521010742c02d8131190b580d5900000039920b564444505040c00c4895502951101c01c5401c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 437398965 1250 437397715 437397733
    0x106080a15051e091509061302040f120302010509010603150e03190e010206090601050d030f031d010e011a0a03080a1803110a0b0a09050112090b0a02070c080d14070212 74
    0x2010a504a041000b00c0c0c0c071361055030710514500e05180c2030341c1c2665480030300100060998a4658100f0003207480441c0010700b09a111185454140703559000a90210f040c0c24036030080690902070b180e0710440c5003000b806880d08c3c41c0d80300750344460035142c01c40005880b8619030504160400660b03098211018404a150401180c09007258540c040d2003030040c040c1d0f4000800c18000040e28504807207001c0c0402c0001800c2e0b1310100e4465980e44100f10070182c507940960702c00003410401c1d0790000c40d01d40c0001203107522030f000c0c01d003103941380540050f0321002d071450407401780d0b50a5020000c503a0410aa16540c0d2107540c0115841c038901400c60366100407411020052208518042001e03260681d040304035181c842d008003041c4d0250408503400902001e2050106520a042020071101136100100c2e064a266030f58800e05d29040fa10081007179404981d850602c446180c0080040000b031026104020040c88014401d0080400b441d010050008842086481d00c040c05001c07440d58109455010b2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 437400215 1250 437398965 437398999
    0x50106120c12031e171e1003020102070e0a021b0304060228030f020f030c01020d060b0406120c170a05160e0a0501121b020303010812030106080a1505 66
    0x142806030a9580d8140804081034041e4420500080c06406403a07503104d0145203c0c250459160f50b0035604104001c412141400c3c108103401640170301081500511255581440202d2100009050681c130303030088001080580d0300882c40400b41d032140f1000241550b118040c42c8080e20403044202048140d00548641044e008006001036400fa0313400d8a0310288500700c80014480403552185042010400c681d00103070148030031805110306801034940400096461030f04640002081103076a940008010007040300380d101e401c004d0038502c074005040c60308003000109004844841d0742010f0b030340c0b0b04103260464046c8031004095080718080004603d44501c800029000036110100000203c41000b90814000c2e03803041303000900030f8081d20203940342000458640814828100c01c1a5590382c101e0900c520392601d0942c1c01580d81c00550340c03945811400d600e81543d60800915040041c40180040d0707602150a80c0c0185a01c18081010002014120410440ca9108a6021070702c1d20300c40d8040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 437401465 1250 437400215 437400239
    0x110a09080d090b1c06080303150906120d110c10050901081e2a07050105101a0406140d0c0906030e0109050c0607050a06060f050405010b1e16050106 65
    0x5245140165165503101001c2954400e2603070045040c42c21041c440b0900542c0d55460290803440710798804503080790b6400107103041d0741c030a403200c4c01e148a43d04160b90450802c0c0e82c00940081040c2c0d46031130300441e1142c03280d40300c9054450b070318200f1981427074140c240c035000c0004004606000308401c0c0310f410001030282c0168001c454a07030200ba5064001501842105040c44901c80c000b62019020f0366070311010b480b50200b4001194603402d0000fa000008032002d03001c1c084e0303640f0440c000906420248103a105512003a03101d00c2081d1954503520800d1461081a103088690605104105096992003030040e801202c45494915141c0481c02e00d5803944060024200c40441e10208404524008243d00341d5001c00c6024050741e0140d4100f910300c3c10203100030310509020f82e0941d02c100c074185c0d4540b425981e440d405610061074844041c04546071a1042500500789002d036180380c0044a803001d0a0041c03e03d19040704e4441c00f00e115018440c0550400a10a034850001c0214503180c0c40781d0045 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 437402715 1250 437401465 437401469
    0x20a18120b01060c020114031308070602030a05010e09071214030c10180203060402090604021207030902010201110405030615060d060f08102304081306030902010e090c0702090901110a09 82
    0x2000003888000a101c0d13000303444541420350103964079118007007141540703962607002038030354007003522410301090100301480064402588509000760307a038146101100c09a4a041e048101d00b500c0d02c07414812200c90004044045a20040c07024014100341d0800c00c151110711014050345010002c0d40418410021030390f0360170900055070810406404051480394102d400100a4041e805a80490054500034980c41c3d4407000080025240414520740000f10320010390f00f1001080e1202201d004540c2c080c050040c400d05030b00c0312281814074081c00250344a078050070109550780070300340c01c10f8640c490800b128be482c1d0544505100d19035940041100040b068400d41d099405400a034120400b014007810080c0c005515502c4408207440a009144440260041340c070003608000044802c804003121030b0044c1072540340061380602500015142001485106101e1404001080300100d20340c0c00b0b86003031680680d030a5900b030341c40048445c01441108000e01e800031001c9109250940e0003150a42 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 437403965 1250 437402715 437402723
    0x181103011b0816050a050a120207060c0504061704020d020904050109020306181c021c090905160305150312090a030f110a060f02030f09010e100519051c020a1812 71
    0x40c0c801c200c803404c444901070107000c800007030020400042c003244120000d641116141a00614101c01ca44c0c50000300c5501440040206101113020413600d5080a0040946041c030300b1311804503d000e9001458080041800903c140740c180081001d0281c25401240503660140c12030707000d41042c0100350446035072400e070a00203104016050076001004440305000c1011600208000703c0072500c114143e203401c50424040008401d00001d048540e4011706024100950b125a040e04150310b005080d180300804d03125150380da0110010742501c00059904104180c0740d103507622524150f00207000c204090b40081c00030f0b442030b6240010302540f0229403040d190111406440c003950303440162040c040049218001d81c20034000301e02200c200c00003d244d000c00508d480e08004043e0000507030000b1040b40c030782c00010030101d1b1100b440b29101490214401181c20018280341c091000c1c0f100303000c2c18184000c240e94001c1a0101464004e15442c180741c03144c61044240c0641f203050161036401c000100f51 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 437405215 1250 437403965 437403991
    0x20d050c030705030a0b0604180f060c030e0a050709020315030a120e190b0706090501020c0703140106030809040216021206040b010608010806060910080d030905010c03181103011b08 80
    0x1d40c1e131a00080c80e40301030b540550500c0321581c6110410004007003e8200c11002004850035000084401d041500040d01c281000501d0380c0390150001c08030ba04905402899900400950700401c100062120441d80d600c040941e9a40e1111120740e030392050380000d41c1c2c140c81200181d000300803101a0070070300d0740116a00e104001540d1010402452003a036420310350190040018018000003200800308540540d40215005619503a1b00b0308990102680300c807a80c200140078010000c6040404003114028002882894103540351244030b0701c00e54640b284196400202e2600046804c1c0440fa481e640007000c25180e9504050450b8540e2021281110451040400070030710074019540b8a041e140c290f0010b040c15910081408010200640440489650b14074002410541004a4890031849070b030041042d03d038a1401600f581e9005045c0f105041c03c01c4840b442041c00b015501d40e0b55504809032807025040c0201080c01840e5149402c0702c1500d201c1d58140060303030010744550241c0e24101c890 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 437406465 1250 437405215 437405219
    0x1518021804090209070c030e10020a030906081e060a0503010203041a01090204031104020703030f050108030408010e0c0f100504030b04030e1002070302090613181a01090b13050c07020d050c0307 85
    0x4800c0b15041003000b5842405403000c1820103125840000b016846170900400d10240c80d40003d501d051022908001139015030740c1c010405074405000d0000300380c982000d071664181200e40640c1841c400022208415044c000540d040d50313558840343c0204400b800031503a81c1010300b07200318075104c5002c6080080c08240c00004800400c0c0c8216011039821001040340516400104006988940025402c0548808a4040c48011442101d00800c00f0100540d69140340030002420b46d441c421414403d0313004440100c00d16180c600d1a0b60b901a821a0300314240c0d440303524151054040c2d5000074140035081c100308810140c0120b000000c2890031508602c7c0301802d58000c0343d41d44128040290072194180c003080b040d05000104850002c80200c020662a075803800065070184265420f403011034040001041d04c144201d00d26014040101080c00700c021848007003542403904413420100d15a80b48009076661403200155100954001c103c03003141d952034100113641d01c1003a48100c0c800d004420740 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 437407715 1250 437406465 437406469
    0x70504090825021507330e010e0d050319020a03050601120905070614160f0b071b0f0602190e01090b0a09030803040c0b071b12021315180218 62
    0x2900c000c2e0b0780206034400350b13440c000300c0d41003680240408484a01455800d000c8801c3c0c1120901d43c600303054860b42d6220482941030000380c4d9840603c101c0319902d403d007508000c0c04003040141c100a441d0503c141d480d19000910301c404041001c160081a10100b440441107515070400760260700c09a9610044501d10004442113818000008000ba405100308008003405a000d0200080e0b42c800e03414241100780c0d4142d03500c0b99506400316401644a04903070704110039200c4503038000505180c201c0348080a100035030001112114003a203c6030440e420401040941e40465142840e005080c0c210525540c5000d004904031840312800f05402440108200102c0b005443c0490060354851003000d29540b500101a1720240c4142c1c0d903843c40c9940410901c021000601d40a40300d4100f2480b508040c1d103144e17070700d8510b40d04680700d212a0708241c040580c4d21000426803d1000752400030300300000c2c120941010070a6401130749203440d0300a164400032000d0303019120303c038038502c41d09500c981c0c1081 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 437408965 1250 437407715 437407777
    0x4050f10150906210615030506100b16150207020406171e0d050d022203141b10020a140f0610150503070e041404051515120705040908 59
    0x460304d031900f40e062504040189980c812114030b00990000600781d504682e0240d0780e4110f038105030341940c000800d00070740110008468008160b401342041c103200d42010b5003080040020406803044020310140b0b9140b03d516412035442030b0b07006004100c0f0540c1c0b007000840312800000301d11014052000d0032003140018108140c0c5079180f4401a080400c44030105a44c035410540001054039400d00207000b000c01050401507075040000c2c0320b41c0d003c910b1460b0641c84d62050092240c40e54000000311007040b050128840044c41c401c5074491011881003404900d0901d0a400282c0841d500401c0300003203c402040d50240310444e042a10501d64407130050f001402e0f150700c100e226030807400404c110f2042c400c8000d150003082524160040c2203108001034152004c0082a4844030b000f001800200082000150624080409201c00500d0f000003880d42c0d1420f880b0300d0030f000f001d820151800704c0c0c1d0103010f400e01030003000344200290452402c00060a07044000d0500c4941c01c035181603442140d8140c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 437410071 1106 437408965 437408969
    0x90b030f040507060915080405030d060b090a050102010b031207031716030c0206040b0402040b0402090310051e04122a030e0f0402040b090904050f10150906 69
    0x402e2460400e482d03a4007410a1000480c0704001d40700381940c0d101444801400e203ca59a900e60034a20306510905900f42091440e1080224200b80c02c04094004d42100392a4050090703115001a401c8501c800a100d60660040d000b10002001150040c26200d04c2440d1280801000302201c0e0001a0107440c511a00c000b17116120340f0150f458428400381e551540b008020904003501c450054074005000a40134507116151900d132034880f5011904414000b070f003101d07041240407416500031300040d220380c80c510440500c9003008190003051a8015608a04d401403101d500030401d540c014007000207540356881d2401180d030801c9400d40002c03690341c060b40364054600e0b034401c10810b40054251000e8132440c070506c800e000d440701d40b0007030358003603c01035850111544450500341c0c5401c4190b181301c0300510501032400204407481d002010007660949215480685440b003400543e8403034 = true := by decide +kernel

theorem cover : BRFrame.Cov 437230215 437410071 := by
  have h0 := BRFrame.cov_init 437230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 437230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 437230215 ≤ n) (h2 : n < 437410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
