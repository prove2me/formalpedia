-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:54.598967+00:00
-- url     : https://prove2.me/submissions/ced5630c-5779-4374-a96d-1d4389cc0491

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 901618705 ≤ n < 901798561 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 901619955 1250 901618705 901618709
    0xe011104150e1c050601060e060f070b0403051b0d0305100b031f0f060201063003140f030a020a020d0f0c03080613020a110f07030b16030b04050109140a05060607020d0804 75
    0x8055508800e01003000101713156040710241c3d25000e40b00700c050001c1c083c051155512480b1841c1e070030442c100010720f03c41d0300c0d0b58101c0c0c000c3c9040e42c01c10110700071080c4001c1d403c0d803007078806500c100314120455905008042c0e100c3e2101c61402c030b106143c000d00c0e0401e80405401c109602e440071003041c00100c03da00b101c20041c40342d1000c048205540e120068002c0101d4001c0d0880d124429102c0442080c00f600b4289100c15600c45e0b03c45500d0240e201294040f01d40720b552100ca01c8100904840044900e01444c01220520001641c443c1c007000042e280c0503400e0130080c280214034031030b8600c2d0360b0400d01e104002d6400d4100384da016541e035000610403405d6240c41d500254404102074a0340707139200c1c03484414190402c2c00c854400d583c60b070810359142464400202140c0d030100c00106103c070000c1485035400120309000c101140c64200040c00c0e40c0007600210b034035aa031012044452100d150034aa00058841c004000300d04150740801c5180c401c0010203030051240e40c0402c0200084401141c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901621205 1250 901619955 901619989
    0x319060c0c151a130c080109090203030f031f30080301180902090108060105121204052707120c1409011808060f15100f030e0c060c010e011104150e 65
    0x11009030104c60360802860310741c28020000c1c40700000031460458901c102118076400a0045003420340325500d2500c0d0303a0008080440410200280b004030031b0603203401c0d40142414401d013460303606e0160361103401c44080620024031070041400c8100450070910860303064508103040c060115007181c0f001c501178100c035600203400c19011b000008406030045221410380d0000c461449107802214660740d5510328500c10720150301c2d0100400c000c50301d801d89a00120480400c0c0382000100c001c0703100c40b0010011107962001c00e20030b6510641d4510b080c0315203030400300740381050400d12081046100940c002c89120a0501003403212003002c0340c514460407401000c0e00707000c4074076a1601d44802800700c80191156003040640c034031706100c68500340c490400e4039aa203640b603421140070000d0407005002c202c03000894134021039043e20140d03140c0b903005061000c200000465a00c0c03440d01c07c0d0342111280144080114400d0100744080350314030b541c038031882450b803406138005502140000d005c1c0c0d0010301156 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 901622455 1250 901621205 901621219
    0x915010b0903070b040605030c09120f01050412030c1403060105070c0b250305030402040b0604090c0c0b07090b191403090c09011a0706050a0b0319060c0c151a 70
    0x11440d1500004041002003a01501c0500ba07a8080b1203280380558022403012400031300000b2941c00c00f4001420700e011004202079203501c50640c900b41452042000c0c141c9a945860070403041c4011101148818030b414a010032055100e080000e100c2543c2c0701d02e01c03918401c000049803086e0b01c41c10640703540b01c0e08107548a001d01d40d40e42400b211680500f42c0c0c0c00b080010151103e041120240034000f02c0394264545d10700d95504d03607013000010001103104541c0301c1e030103110100d40c416107845505200003598641c01040307070305810001407500d0028540700c100300403110140b19440b042c00a8881074450086400d5401072010000c1c0d582e03810300800341c0b51080c404020001460740004404652a05c2136802480c1ea98032150004c440c040c1c40c00c5070001080003044400700040b0107903c203a60140400340001222941e1200007820171054042441c0e0140d212040c4005008251003102c0f980051401c1183d00006030f559052410208000100310300c81c0e5030b1300510709420030100c640080c400001c0000b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 901623705 1250 901622455 901622459
    0x61e1906020a030e01030203011d0405010e03130518130210030212042307051c020d021903170c0d050706140a06080d030203060321121e072105091501 66
    0x20b6494a04000c00c0e000540b4036100706075154001e00c00c50341602d1440e074000c16030a03070030340342c015070700740080c100308c91643da1070707030210340921040c00640740041c0700341d005401c01c03440c2c08100000b200390603050803204448401400f000e00300d510a0b20a0072039044e910350340000940042a0020301500544020b00c1404038104410040f49040c000e160b480e030b20040550a4501d00180d03580c0b60498016640c0014086200c140d0b015121924004031506c020501d4200896583c0810078a070461107511113901c5254401b4400c01200c000206801c14268a545040902c0c0d100c000d0740d80c13001804241e0501c0400107070207051150715004140052244c0130f00d41030900f04040d20f1801002035128404c01d43c01021080c4101034400c0c000c0b24050310780200140070300c40211101003001000f1000761041900c0801c0042c03002c2c4aa41000783c85104c500c104007040305814010402485401060f00b001c001d500398111a1712500b05200408a00140d000000c680e503882211500e0301c0d02d24481200154400c07400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 901624955 1250 901623705 901623707
    0x8040f0b0f0604230612031e09040c050f072004020c0d0305070c0f060f14010609080705060405062d0f0301050a0503071802030702010f09052103061e1906 68
    0x1107900440003602d0820820107003016640354034078048081520740540c900402c401e86021060010440b4241046d64503002c3c419a0120314000d040c515500c0a907000b15032074956180c648110f801d04c1d8410300b041c4d85400e80802c20740e07803540308d0382200030310f104150354000c41c83e800c04960460050801602c11544d43c0c0e03000100981da40b40c91014400040d00300800140600d1050b541d4182503540f0180800c80c51081d1f98944000d4429114540019652965208c040d04551400d00e030091040c1e89440c420241031040d03160814200c2d40156014401c1000304000036250311003180c0c8810041c5101c242c4480c2d5645917000c58840101d861003102e0b070041900040c0002140086041301c004813400201580d46000740350b11190304e4890040301190003105401000010303001503500140038070000880906a0b00020115055000c05990070783c0180c9200800b020210030020365040000c1c031803415450100c00040e040452000540528040003022070842c0d110703041c0803415002c250703d044046c00c3d160a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 901626205 1250 901624955 901624981
    0x606020709020a213305060903010b0a0e2d0103060b0d1209050910080a1415040c091503080904022b020309100207050a060506030313090c0914030a020108040f0b 71
    0x9410b45100d90400302c000034245c01800c1035100c1102035070310015000e241c0000c0001541100541e160595250044514244d0741d200d5140042e100410700c050304e07400e040d075900e00d15134001d05402d2300d000100030240c40686018070500f0f0449604c0f80001c18130321400c0c004506000c0d84000d000345240806c03514a205141c01c840d51805481c0706890303140700d5541c1d160828280200c40d1103881301c9500419980d0010507100c400e1030410f41d100310101c421000706c4d22800342401c10119016142401d008609020300c0f10039000c0e0444006405054050184c2507403205110b902c10091190300c55980080d1960403a0300018141c1d1080900400111010107150400d0000c5e5000300c802d0030050003004241280d901551007605d1485030002c4c010039128500b6590b9000801015155651501c41800302100441c0e004c24120054500c83e5000305080c44d01500140c1968899007040d005400c1c014081c282548001071868102034092a2207a02d90b101c1e0b0600b03c0d50306000504c003a010000300401c021041c2c441c20 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 901627455 1250 901626205 901626221
    0x90c0b0406030f0504170c030f031e130c0e100b07060212060d0c14012d020708210a0903020a03030201270519020f21060a0606020709020a21 62
    0x52801c3c001070709000800f40469038120350042122079510110f120024010300946094454401164902140f810f401c0b1070320740003181d81749450700b1030748080b51b944808019800d8003c1c20300b41008440031038a035070320485142a4041c21141c101c3c6440081c05000b10144420010711602101c0380c1d450303d1a0130640c02941c01155201140c0f15001c02154443c1441c0d81031030007850300500341058250800f1180329064107015005410030000c6c6145540c460704c038000700d162104d00210a411030013441c03100a030505551b54410601e076000310260202020020390048550741d4040030a540d0341e038500314261120003060300040d4100508800c04800c068056008aa0701000d00d4503105203405007400035018000750820040090300301390b41c6910320165500705400d01500c020030952588181c2c1010031052090a941383c9001c0c081d4034091800fa080500c40c0030b40040d8203400a101c02424110b01035686c103080d1041c0e40304507900040f4800518070030542c02030f040c0540e04800060300154103820340500402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 901628705 1250 901627455 901627457
    0x3030415111606270302040c0e150306060f070f080307020304080609070510050a09030b0c07110402030915070c051e0c040605030607270e07020d02030306180a090c0b0406 75
    0x2800c40514403182603070100302d81240d5100400010184c4119400e45110b40b0f5429040c4040d102c0400142d03a24000c5180e5085955900c944400242c0100400071812101109014034104103000c2c894840300200c41d4141c8060680c0c07035645081d4600301c000920f50800207490082c002c02402026540403008104031041d120864901e515001031807502c40006100f02544088208011960b59001d4000303021450310504000000541e20b40f039002c3c0b8041c0442d00c0009030b120004944003044010340c403240e1100c00503030b0114150b18040f042c81c1c2c0e680d03068010b81070325118424005810b152180e0781014640780d0000c142d078800d146005810b058140270503080452070050021160040c2400e110b650201e9030024001c0a01d42c60b01501621451813048101b00524a50fa10340031100030b007488810f0042501065941c103a01d41050000d0030300311440e4410007103400030030038841c2c6592941c900b2008000c5004420b0340c00e44500b4038a500500c990180100100c8400b1030008a808260014004079612 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 901629955 1250 901628705 901628713
    0xb0d020c0f0c0a050103050901020d09140f06041a1801140105040e191202030403020607080703080708040b0f06180a050612010c120b190b04060e040c0c110303041511 73
    0x6250481510b40201c0d03044580c000b0f01101081285620940113035421036800d400051505043e0000c0c4801d43c1d00540e4150740c48080701c0700d000e072001c030100300c045246580d032000303810941410f986440500e040c03032603184100d00354200030400804910760710070126458400200201a00c0116a49944038240301791340c031032442c154a058101001050b00c0401380398110840110307030041d0359115000c1c62010a034208511040c0004001a218840104081c9000e0000c00b030b1512940c2c5402015000c0003015041004940c100340400649020103a17030700b0951802c2d80d00881d580b0000820594041d004a241c800c0740d459091103a10313040307a030149001d1041a00c03c805a019070101d003d007079903006184a400a05200c0c49056034075859404070211b0b6900a1030144107481c15030380312080b80c841e41c11109006400007000c0020640129040c440c8100a60f03007400606650360000d0503900355004007030300302211101c10004a80d414800c803405000c0e1704800c0100300d0581d01d4014013031511002016003c0c4a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 901631205 1250 901629955 901629973
    0x4020f270a0f0b03040b10050a0801200c0a08070501020918070908010203060a060e0a080105070809010f060b19030902191820070804150c051015090207020a0b0d020c 73
    0xc1e4111660080d588070801c05444c41d207407643c5807045544010042c43c201400c0d070201184c1555902d094500030b0040381d0010071900c007052691203071100310460941840301c041241c8818624042070b15690940c0103884a0b46075252814450301a20411440ba0741c000207501c01041c0d14000c1c1240e060003108203540d001c48880d2528002404c03440300307482c5d0940c4605008820400c50744920f15040c11240054460305510341d5401c02c00b8251031040d5510400706119904000b43d0035800d2040c03c40d10307411084180409171821076400c0716403184210145003030300c500800c0c4694038000e8115a400560282803244511440e542e0351000c0302950045d0382204460b2194110200c100740103201da11264400300081e0f40d04171010150310399010600131114130800b4800010303004903004402041041030784030300200c40d029241c402d05081a410003c05410b20f44015401c540100c00d00c905d040d91303408503005035140c40c980002601810319074030070400d0301400a8408081d150301d401921090720501c1c00c44000784 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 901632455 1250 901631205 901631219
    0x70f030509011e0c0201020d0e032d0703080c13080303090d05030606090d0f06090b101d07120905011b0e061e0a030603020414010501121a04020f270a 66
    0x101c1507510800e46501c603822200801d03021341e0008480082c42c0c0001031802421114800580f00c44118402240c1c002140c1c9041e04006c04446049001648400c000c0161020a00710014020000090b0410060f074000038181c06540302118a070401d00034080e442d560303403946169070382c1c0d1007124604c0c500d0080c41c0b104491305025000b07990084000620315401c143c42d04007801648256150b0075500748801814050100741c1c01d114000b802400380c652111036103003441c40100b8880702ea034007091401000d003048840e000d0282864a800442602d040d458414a58111710064020300c0b0300601294a08588080d11410031180c042e006189503c40304501c00008041080c0703070141c9688140740300c10440501d610180e2850092950400c64100024131540300e4010030126607245009001504080006204031b607005000402c1d0b40320209814010480000e0600e581804002801030003247c02081c42120001d4031000d07135600d119030030040d5080a2003400c950030441e40c80011680100c03900c07900030602d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 901633705 1250 901632455 901632461
    0x1806091e0c050d020d08030c04090606110a060924050f092116060e0604110a050d24020c03130e0c030708092d060a0603030e060d14070f03050901 64
    0x250740000207680220301e00010702400c0c0c0480e000480e4445003880b9024006448403000c3d50007010754071485601d50f4240488041140d95a404c00c20a1001d48010b544c0303900f10011303aa0b51300545c03104002c00c0d000716500d000443c00c544108080821000c6000d0301034614000e40c08036110708113086680782d00351228500c0546070a460302c4d5841da280e1890402203050b4290034001d0000340c0c940d81c0d90440c254075030740300e00048500103214140c003900b00c03006000c00d00040400c02c00c01c0c52400c5600c0300c2c40300d2034040020b900300300e40031008141c0e500c520100c52840c100d2021200d100100c50800b55690400c0c250318649030381c800302203441000c0c2c1d0040082000d09294040300c0c4142840f0108074915164a04203854841d80107040002c1032203440d802c0c1088000076140313070718509010740c41c80d01040f080783d0b011800c0c0480181414040d80c0707080000c10100340d0095100ca103210003500c020769280195031001d00a00140d06050b40100d0354281481301c080e602c85002000ca1940b550100216150003a0301030036 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 901634955 1250 901633705 901633763
    0x30b011b020619110307120e040b0f040c050f031f0e010b0307030b0d0606080709180c0501030c0504080109110901061d040c03200c0607050c0a1104180609 68
    0x44041c0054540f80102001400c44030799103041c501c030388440b9072440754078580c449601102d12111201400c0d08007600101002c3c50603c048030180b0030040c1c0a0080385040b089a070411344266110b421008100d4060401c4503d543e600c0454681c0c1ca00d03140128400c045441d07210018410101d907000070f1444e4074520342d98142d0f05800f44407442e503101d4200840160025940456128414010441c0003074070b244200001884140041c040c6545000340c0c1000b10340b10000005407882502c0388100014184080700000c0d94800d0a00056942d1281812107103030040b500820003070340c40d140402c001d1260310f5000601006003110f804400b0780e00c84d00c0445051055401000030f030011420301c00d8251034140c01082c01140d182c90006201d0b20350006403800d1004d400ca0305006a400003840092006082c4612070b03020fa92820214a481c3c0c00c040c00b03a030703154200701c00a018110f0b50010324000fa07455811502142e40b048034042c41c030006030305240c4004c02c410340b0304903a020b002e1300340741600644522110389 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 901636205 1250 901634955 901634959
    0x4051f02190f2d03020708010f02122a07050109230a120315060509030c010906020304030b040f0c03120801090c02151527060612130309080607030b011b02 68
    0x800b0115035656aaa0120b140e480c4880741d503030064034600e41541e004202c46505000e54003c2041d5460040003500711866100b000e085540100964440310b040c1c80c0d2000c2e007189100781c5490180f20040c2c190001c010790300c54408440980052a9802d01105400803450130740100e01c2d4aa000345d00c00201d110038200800e100009800c10f440c080045548140300400d006002c0c1004208500c140c030041e515103103160011404620089046485801d041159080c001700a0810380881030400f403000c0e42ea4051888018134401d0b00c00700080402030f5000c011030074154424a00301a840e240e140840c40038411500140000f01c06d00000114415280070301d800c0103001d0303000780903101b0005502d07024443c4028841856040d02040000c07240c0c403811880200d907050701ca44901001e040300e51807080854050502031142c1390074000701e81c0d015020070016070031034014650b21030344d10428a803d80305191150310619981c05001c1c204003016405412040340035a09980300d00d021070940b2040c454890f050f41001e5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 901637455 1250 901636205 901636223
    0x30d0507150501050d060f14100e010e0f060603130605070801030201030515210319081807150c0212060403080a0608030415030509160303030906050606161704051f0219 74
    0x303020075242c0d4007140c0c1c07c540b030040102e088807180809422102007900c1c0346d01e10228901e820000306031501d020380e01404504502e0744a0381440451076072100805888a84206400000b0035400024080c180c8281d0f0750100c820b124a00d0150000f510072082403000740c1c0424106030000b540d00400c5003204d03a41200003004d2000c1d55115039800001c400480124803d140f0040220507500700c4805100d40004415541e01c1d9003924011403030702941509250f50401d50362015405010b008580c89005002e500d061030a2050902103000144071100140c01d181080d001d080c0c01d00c818540e00003500341c403548101e0b8090040b15078509803a41d491269101e21903c000d4400600e021a0344660851600000807100700c810070b9031840d60b8001c03180d1099000300d002c00c0e80c0d41c40d20801c000c8240039241d409101150307a507003085a0078030810802c81c004080100301580e0b44504100714990b00341a40c000d49405040c014120540c820401d004114100c003140152164184107120500420100800e5950010000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 901638705 1250 901637455 901637479
    0x506030102120c0d0e0106141801081f111c2f0c011e05160906050a0c08192106050d060b04110319050906010f06080a0902030d050715050105 62
    0x203c586070404956000050744403c25402d642d0024041c55025041d0800401d1940f42000e0410101c4001d640715100c0d0640f4000041151490100c2c000b05000300004946030000f040e198510006c0509000851580307001080c0250140000c02d0902041207041208000b0000d03c46140b2104480e00a03403055480d03e902d5081d2515404400a0081815041e0010414440702d203004080180324100d00045140d84c0d02c10042c40143d80d91404007280f0301820070501d440c0c01d100c1c00400c43d06c90041450140912080c590341001002e40441d0420702c0d00140c07107403d0803e000705c02044104d0f44400716407150581c0d8440d400c904000d104445c00c640000741801001907d41d03503000b010305048034070103501c10f541d24909291a030b0078000851240c06603d030b40c417213244200d211b4803081703c40c050034582c001c1d40554014021410000c0a81060300d50f2424144074559400440401034140031000035050f02513064010142504140a070040c40d125419a004e9003400030114000c45a09200703055220b0518500 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 901639955 1250 901638705 901638721
    0x1204120203030c090d050703020306042004020a05030a0b1306080d021006061e1103040303050909150114071716170703051936080316030e01020f010609050a050603010212 75
    0x503245061b4810000d94842d16580e400290504a0440c0c0917500e650034501004000c9109003459031401c2030482e011420003859400090440c000140001c0c003065841d00c6181466450b02d08080c0b68014240c810f00400b80c4030107065071034049400c54207026100d449010700d107500c024010070068500d1640c1d01c8265000c40b40c100c01003020b074800000e09105c2c48441e041100d1405100070006103002e500c400ba610300c031160a015a54600030b25200e030340103540e2080c0b41584c3c0e010300b54100601031107001c00d40720a62400e0060050300608902c0402d80720024040502d40744441980e03048902829000b6070500c003800500031a4440c0d640e0040010f0030401400c209845003a059102003111407400c0001c5002114140c81c03e40c0400140b0160000d0154052444254030440c3c4400f0304040c0707010b141410014400d0800b4030007050300060601c42e40100b2000145d01c20000c0200301b4100c0c0000b44006686d0707883c034000404c801d4490f10b40f03003414580058001d05050085070b64055841c16014500c1d0b0b41c07030340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 901641205 1250 901639955 901639969
    0x10b01021e0c06030c131e06212012160c050d08040303020904090c0302030105010501030209010507080903011e05040320060412110109060203010e010f0302060313080f1204120203030c09 82
    0x300311707060b4400d00400300b02c1031981800c4400b500310454640450301c40b10450800d400800e5004804002c1c5184c14000500442262400740400020002c11503034107284801c4000c448200030203070320b2503000c07401610712080e4050b81da0080880012125412840d4681124008415180074219074048000681d49038881d04155034003e020303140050420007010002015504044803e6a111071400700c28801d600c1e081c41400c1c010725013401c0462801140741d0020b00f00d405117041c09007803503c010a400006850030342104100141020910426110345403102c402400e00352000e5002540801c42e120400c7c2251601011403501e01006041640d602d42e210f034121040072002400700150707801d0700c0b808050700b401851030130f500c030f1480940c0303e40c101054250107540507440841c0d00000840c0c200050385031001180d410800ca425084d2150000d4280b0b020507115418500c10040000100d800f2040144828503016601c20209441c540c415002e0480c3c0da80400d49240013501020070941c1d0309460200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 901642455 1250 901641205 901641211
    0x305040518040f0f110418020a06020c030705040207080408010c0c0606050102030a080c13030503030c0c100501030218040602040e0c0909240d11030609010606141206090406140702010b01021e0c0603 87
    0x589400c045c80c007000042070907240502618000d481c02c1c0d0100d10114900701c0018000b07458a07200401001d1201400642e0700c801a1080c02d004540c002140003d010200c0115030180c10f10000a210a001819004100b40b1000724191185440c000010031590f2022046610486072a514403425031900044000c030b961103521588801c00400708004002401840998803419086910300d032561150015582844401da00901c503031450000107000594906400404066000788144000c2e40c40d450084004c0c45181c02820340100d5640c10029548c81c1da80003800c058400340c40380d0081d5140c207880d481c40c80305008103000064611160000d00307810641450014680240d050100d103210440229060407001c2c0c03401215651210010312201e508524000c40c83c42c03290081500e0021000c82c4100d030140f0103841c00d4490030b44000400e0900c02c1c186c11445105e03e01c04051041da0400070340c040c0c000d05100440034007600410400300c02d0f0540300d01079120b501003240080c2c007428400c0001c04c0300681c001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 901643705 1250 901642455 901642463
    0x150c0503310b0a201203070908010504171309060f1424090d200102061810020313060f050106080a0b090a0e0102121e161704030e0303070305040518040f0f 68
    0x1006041c0e00800c020800c04021305014103176103a80e0308046200414200e03ca402860150303060006102c0015407135140d0580040c0c0030450207031104980d0509810031103881d400711958500341b50300400c00c0401000c9020845800f8400c50b9400120320090100052141c90781c12403030884074034806011000b4400811604034024030080070f207240d03603903000892295850304003030001500182480d196010806950070858003c0041c0c803400f54805050f0351061923540c8114050740200101f0a901040700794105c08592026041c0103841040542400a12003407141d80e0010344030070040380c5601e4442c421400e1105015052008540e030f4140820041d084100130b03101559420000b548120f074049007080c1c0101c0f070b01e0188481c0d01e800c2c00c0180c20300480c0034040000d0980041072910003980c0000d08400404124290038015a41d036003802c1e40d24280c200020750b098000051481c08140e844001001a41c03001c80310468161505d0b1400703980f0b01801c0b60b0080481c425200c804000c1034841411444042c82 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 901644955 1250 901643705 901643747
    0x15011e18151503090507052407061127010806130b03030919080105060f060a0c0203070315140c040b0702191a07050c0910150c0503310b0a 61
    0x42da00c503141406a84040c21400a0340d14406042049000d11080300185022503040c40c10300400d101800d0402c286107001c002039440082c0306001c10580390040211504032244454442035000300302c03280b41d11041e4100348001d031011001302e125800b4200240c055a80588500ca521004041003c01000c0110480e9031500c024042c82c01940ea40d4555404403503410300341c0c0c00f0054600081795081d54006401544241102ca0009080313072030302e800382c5500741c002c1d103880d01010390180040f0341045035a401c00340c03c4501c460015030115419801284000c0c19126065020b0780d180c0c000310641d4000c90241da40307111800c01484002d85000c0c0d0b60540103591002078042c0140e40c6038406a48007440300e08031900500041900801d000003804100e00100041d52442c0f030700c0c81e081090340041d103203034024180101d4a443c5030324009031007034007020700255025080b283d0b510020940e62074034016010121000c45842030458481e00c5034440700341e00b110001c8c1891400c01580800c1a0303119a1480c4c40d038100424 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 901646205 1250 901644955 901644959
    0x1a070804080d02011407080717040201030e01051510050313080318010912090b120105041113030f0c0f0e0621031c0e010e0a14010e15011e1815 63
    0x18010407818802c66000014103181903c111301408100500350414401803608001c8c24940085841c000615542c000066039a1140b0058004001d6030151050b29842c12080002d030f007100218044e601c0504403404618a6005203007106c245c402165450b0034840c44190003000a08988055178008040400000840680d11000360844a220740c0642d02030100f41c0d003120009401211030400b505000b1002ca2074618650750641c440700040c851140103940c0e40c40d0001c00e0b90701c810150303944640d0b911010300c0301d250f030390429000803140044292800702400000180403052283d414045849000901c01540e5448041003444039a48284d2034001092401043d1000717005d00090586102c00d0040c2034000e46020794680c200c800c6c0f1144203200c0c1c2e02d01030008401840029106081c9036102281d0361032035080041d803d000d0600046a04054442e102450019080d03440b81541a9864211344d460000720f40c10740b00c9800d119500c115040241d200c00901072080301c6401035124404110400322400f6 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 901647455 1250 901646205 901646219
    0x9021005040e0f071e030f090803060f010c0309090b0613030818030d02100209150f0406031b0c022103030109092102060f090a0f0b040510061a070804 66
    0x148010810000204005424400e8800c41242150001c80041d100c0046140044c03010380300c1c00c110300f10548070000b120b04e05280a842500904c0e100d0103000d000740807402c491b207010301c0b960f001521410302c240c603610155240c551003807a04000d216019680c6441d00c2e494500d602c00184540014107420120070414802e01c28400c1c0b101c0c00003140708914050b6540e030003080502c20702c8100b50702103100b50410075400742e0b400d60010b01c85040711411040141d942280ea0009a4003d982e0704408245d141e020582c1041541200301500446115403814851040760300350034002d2810140c2d045001c00c045038110009410400380b280ea28004d840403842800c2148103003217207903070801d80c04540d02c59165142c1200f0004044400201c5601c10350608808242c03440d4042c1d102d410090195500002c00340004200450406c020045907400411046441d8040d04010b2a2440301710b03020303103240c85070400f0742c9004005840b0b201f00f05d45503910040d8200b1104426060590b000040694042c6001e00000c1002c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 901648705 1250 901647455 901647469
    0x12030605092e03200a05130605100309050312091504051606021507030903050f13031109070905040f2702030601060f0e2403040c0906080a240902 64
    0x68001d079500b0196003100c00e11000200242c0d10119694901180c401c200080d8640f05501c03002492000d00500c0314190380215820120030f0b840305503c625080c03016043c216096110405607582503507854048a16184140c003914058503004000b03038010440c0c040d500d5003101c14250001550015900c83e00120100c603821a40c040c3c90640720390300700b65900a45840e0384e58904008043ea400501300b00200c4113480d40c1400303130040c8a2418140c49028400401d071060017103d03007000484071302c42d442d5034540070181c40c5a00c2e20b000072540184444011119490028180e40c0301c5d000507542c00300e10030300304406c0c403000d044010300005006442e0a603482c04002900c034a401c1c00004080f0001042d0351600401d0b1138032006134044400d004024010007103080c1d00020569880c502078404242d44001d00403401c00f01c410660481c040c0078804010710040014800001d0b01301d40c0081b0042c400c0a4854600ca616251200c2c07004060740102c030a41000b21a041c2c0900005e020101070005942c030380c0d0303004503100f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 901649955 1250 901648705 901648711
    0x30c16050105100515030f0c0f031009060b0424030e010212041a0403020a0821010b190e0a1806030605250306050603070c060b04021c05061008041203060509 69
    0x80da5102c2c0d0420071024407218101006003411903100d002c030420a00d00030464800501404414103850000034240314000d0212501145100788156580c038104200e812002c00c940a098010760601100250525500090340c003603e51000c0c1002c9010207030058450402d46000c0300c82c091584606040320604000c1c03001c1c150060220300c0b4140300d890146400b103080c50000c8040c0180c48001810b01c804a135002500750110395200b100141c0d14405800c2c200344164481d041303400b254143c1000070803c0a0140301030001110640304009105071780580513a81c02c4102210079411410031501000440b0f03580c13407140e0a0f18007a0300001056600c81d02c8050a80740102c2d110309414000030520035690540c2d43c0350841020a91404200c2d26017000d0000e2101d10020300072400300110030140c0002e1010b180d211460318000200215510700c03400140540708a0f036181406041c43c0b03131034002010390505103c1008180c819595108980da80c95403544245a1544180c404050355030b8404125900c0b10303449540 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 901651205 1250 901649955 901649963
    0xa02010b061303020939070c030c08160b0a0c14100b0909011104091d011d15060a06050c03160f170a171e0109020a080f0c0a05030c16 59
    0x51505500502c5101d40014004500b00d40814180e50400072190980309041a00c1641008139240c8040d00c05c6e40b5400b9140c005011403203650400010000800d0151040340c800500362f400c0242441441011480988100180b0038820856600c00e030b445a01044a02441101c0d0084045030803c4801d183c10f03550005070074525980c07500c040c19454004203030399010700600002c3c4640310020144414034040c2e40300e20810395486942c10210b4801000d4035041c4031161030000c102030300d400081d1404940c0800d00160341c074000d80d0f01c440c2c031080e48159858810750b4080e0400b000180b900f003040380c0307540c801031300346596002c28440c1c3da01101c15200e42c0240c290050390181154046800e128926140f1174400e8041d41d24108142e040044d003120281181151405200c0c000da80c0d55040031000b5404902d560501140802c00070420500382d5000d44003912566940e40025510407040245c04581501c4940300b442090003100c2459125500450b44403c2d40302d001c5041c0468030f04906400090340d0000c039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 901652455 1250 901651205 901651237
    0x1e060106031d0d050d0906050901091101020f07030b0604020708030703060501020d05042d050310090605220609030201140711010509010203060f090612030703170903041a0a02010b06 80
    0x300207035050045141d540c07856105280c0c80002141915658103c0c0f01d008000c3c010f02044039090f0721041c0d44400d094603000b2005101c3c5e0b1504c81c49050081c18032110032200d00045581c04e40703c41d4800290340d500a1008001010f0711815900e81c018540d10082c001d40d4880d0f000c002c4480010761400183d4025034694501003007190800002904200c030500085080040a110400c4460713042c8040100d040d94141400c030b895580c1004002600d241c03504080c0e090f105a0302da034580f08e03600b6803042d90218001c1c0403c009588032481c01040146900c0f858101c0400d11120600201d8810ba0242e0803030307413090000040c0460103015880d01c020048400b0380c0414030018145000b92400e009580c0c1c8052442c000b1451850141c001601481c07502c0c20b010300070403125002a403151501c111480800200c131040701e44641c22454000c2220a00c41c0c554090808071001144500500000b52000d440040300301d4480504c007105800341c2c40d04030715080e40031592903107403519403510751b03070010100c1c00030002c1a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 901653705 1250 901652455 901652459
    0x12020c1c08060907171b0c0a1106070209180705030a0308160206060a120f06110306102303060d020d030f020d09080309120a170403141b121e0601 64
    0x5040c8481c01412540030b015007900f0441c40c0ca034410204900040e50310a09100e6442d09606603030030302c044e03010b005011500051041c0070302c3c200042d0ba01e001c621508d80c0d41a18000081407009500521500a40016200300801d05856800a101c1c0d0501141070841e040305a89a00181c680034480206034045a08801400311100c1000c010081e030f41d409000400c0c2c1e500f020000300740c00f8147c510403249480d074954002e00030071403c20912008140c11031401d11140c51000000c04460b44142c030341c0d41c8902c82017120005103038045c1c4c43d0001a0015140c0c0000501d81c507000c56055580018051507104075221316050040c0e0b41d14501011582c066603c034122012000700c040d1078855481424428000c0212040041007000170490781112001d0b0350b0300040000740000c0b1458000c0340b1500500d101104c0d1000800041d100000e00101c03805403050000c4240030000703298030380c013901d0600540000000c1d600703126410b000302480000f2620000f107600610005182c00c480550000c1d014074160800d00c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 901654955 1250 901653705 901653707
    0x305160b0a05040314130512010f0e010605010f0c0b010e040f06021603080901110409020703180801020a080115120c050c0109060e01050619032a08030705160f050112020c1c 76
    0x1040b9601c1944004480ca84004402c084000c0c0d4814400c441c4500c1c08c210315000089001e4100b0202c280d6004000d00c0181d51002c040350180c5000d003e62800900c280510001c118403603038900100d580c20101c1780c412a420300c0404d01854200410a0726070b0510381007102c0c00a43d561005100c2580c20440e1450302c18040c0c900181000f0020b00108400d078141000b40015901c040100d9085800000b801a6a440a4030301a191622110621001114004000103400c40190014445032140f42c0e2a080940e07242c910503c48014803480000004071081407520b01018240c4c03045074124541e06006042ca035080020317038250b800c2d14004035002600c1c1d88102c2403c007000d000e41034015404484150b00f2910008014030210b21a200c0a0300403c4941d0704c0c0b00d040c00c0a842c442d0041d250044118075216100c6403425074951000c1c2c021281807140c10381c1c2029940b109030380d1130140e80002c034400c9056441c1a004480d4220702407545600d070741c1d0821083c48102ca041050ac0c05d25011026480450010420 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 901656205 1250 901654955 901654967
    0xd050a030801150f0e030f070f06090b0f040501030b040b090a06030c0509060306060d0311150702060603010603170f0d0f0b030601060e031005041416090e190305160b0a050403 77
    0x10080040f11a641c540c0344076503401160740c5214800e41d152640000d11500006450712000b01c84401986c0507400d404200681005205810707254142c9500f0f00d04d9544050080e610b10412005100c00c044c01c0c40180301d07640c880d40208525040007040810079041180000e102d801050310810f10460ba502410403c002c1e0a60344c5000030f06003100c42071018034042021a8850301c000f050381d4400c4002c04128400c0602440260201129980840f0015800301c160034041e41c07002e82e1200d015101d00e10005400d0b00d03050054001f540d52100420304441022007010b400b58002c401b21200009007400301d002c2150b400c0c8900c40713844440110104640c24002c090500f04001a08540b0401c260080c0713641c0355440008040003200c81c03032a400112030b035032400d020540c2548000c0301e076150b00410105002080f104c425000c1a02c140344001c00400541040817542c52401c0c0d1001c3c00c00700408100700c00403d0040002d041c80f0f500e100c944418004643d40c40010710602282d400341e520b95643c3c140800d240d4028 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 901657455 1250 901656205 901656209
    0x3170c0712020325050c190803030103030305041a040f150605150d0501060801030b0c0f040302040515100203070f0b090a02060403051005010f081f02090415150201020418020a0e0d050a030801 84
    0x201d000000c4c4800e4075865182c00d002d440b020b000b4844100c11040c07807511100280b0040c07840105413601c81d44c603450f000780945001c1c0c40540d080480d0b0300e17a10003001c4050740154041d960103500702c03a1001659641d00003196100e40181070860340c60100007055200c001001280107405900581e4030400c0c001c044007141c1c1c068000e00100410100188001181c441c0010340248061000c50b03137405c101c5801340c0d4036200341d0304001e4009062105001c600b54507a80840c0210034126020990307600d1122040341e503030184030b0000e4a012214800100450f0312400c18a41146503113003520000d002c0c0e9000300780203900552044807280e01c240c41e60306c1010a83d01ca030501401050105090923072400803101e13034550500f41c03444221000c008a119148015504130390408601900601455030580c0164050100620945012070082c40042003414070610131030307041d500d07500b01200a40c19134414000003500f10380190000c3c8401c030320640c1000d0756909101c041c1b1500c6507005081c0c2c820f50380b80043c00e1b842c040e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 901658705 1250 901657455 901657507
    0x10906060e100311190302090a0e070e01030207290f0c0901090905150438010f0f05090d061b02120a180f090207120c03170c07120203 59
    0x5a801d00307040c0d96440e03208844241151801082001c160825000ca500c0f512020710103020020b5000200d0b2501500070b03001b041d60407a54410000da6946a20030080f00031591040002d11000030100e81d50300a074042d12107180224500038420480e4550400d1481d00d6a40c400811a064420040d01c1c100e603440465000360443d503102d0034003503190300281c55001c107030180740700142d2a040090500d010858030324011140080050001c8869074110b520011030307500326884440760000103001c900c2e10343d00c0304060403001a9507170000c1d4000104120307646e42550481004000c2c0820009419aa0310440c0f1728941e40203460005200c103c040d10344440c2d601603070414040d50030092610015255171000d544500071541000e6330300940c1010880e00e144a42d4010302e44400c450342c40070945452a5000c0c1071814402d0306540488490b820090f5070704510030300c0090000705c1c540c1b00d443d110101054820b8101031412030550278110316a5506040140d10002d40b00143e0000c604014607000d0030030005980741d10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 901659955 1250 901658705 901658717
    0xc010e16080d0906051803060c1c18020d0203030d0234210203070c0806070912050a20040c03090203061008060c07020d02090705041a0405060a111e0601090606 70
    0x104014020583c10310905080c02000304801c081c25001d4400c901d80b004005040c0ca5981c64004c1a0014940000b001c11403c00148002a03c0050300c52007941502c10302c1d106010b2040d0107503820007502440002080f07805010500000b14218154009440c00106d4003039104005000b0328100c0c004080c00d01801d9070b81054000000022404090502c604000f03015074800e00c460705010309034076502c569803000301190300091002885010100743c00c1c2c015000c070b5684560040e81e84c0c0c00c0b106000c4002d800039200750403450110001403c2201c0200e02058404051300d8132000c032900280440c0c450095080219845002d07405c110701e001d014050344080001034540d8514100044030350764450080c000c010502000980340159901c80e03206d2044254010450754052a2400303001302990018030400d60302d40c42d07502000700c2002c0000d00341c030207949016000720704040c9507078021580d0042d1110205014054658054030240080e07000314072841005000f000a03501d810015403c80f90b4a0348401c0c20007030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 901661205 1250 901659955 901659973
    0x50114040f060504111512011203050a18090e0109020102070905151207080d05040f050406050612062e140a0801030b04060e0105070809010c020606030316080c010e1608 74
    0x941c60070300d03109007074001c40006860713900d5240c0540120a10f22210341e100d50b85450b05244201114020140080000e070f030003885036079520903080c00d8070902c00010301180090046032007841c4600303c003020394030841501035042ca0b55002c01d07000300c0c1c81c0040151100d1b510b81c0e404406658042064000074440e05074100300c5440d058107011440001e24400b144034054041511400f035108100e002c02402d00801516071310340450b5009416030707006100c0d181941e00d07d100002440e00c1c052060b1f8084402c0544028504000c600402c0000380009111540c002440030440c070514816400480310400140c05d03d6204c442c0c10079010f821f2050b00b100c1c1d51110003080000c10400c036400b90b40703141103e5000c049078556032210b140039405004c840c1c032221078a619140401c580e03c0d61120880b8042c1d0510700080140e000e0540080342c941404481d003030740660003084030304400c0759980e407018006070198218034203080b981c4125a082d1049003444000a41c007007828040000300350308512009154404c01003009035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 901662455 1250 901661205 901661213
    0x3030c030528090201050912070e18030d0e0f1c14041a07081207082d060f0f04020c070e090307120e041d0607080117060c0a050705071205011404 64
    0x10864800b22801c1c1c1d00c5655007400c41e40504280c42090b080103000c0742642c0401011103a0700c110340d1280c59803030301c41c103004581346286200408150001d40e0015504d04041d42c001d2602400340c2d110001880d20510442c41d18000d024014101d44413445904d0141c1804001e40040480d07981e640145a464800c110421043c800040b5441e0807007010b0a1241d120f44081c2844c540c1da0013113000c8007030003008007020003c60551000c4440d114425030400022405002242d01c1c0c103e006401400b6800802c150200d14146413400c0746014640c1c00030240b801c01200c8070301140598002c040786400300d41c0030304020700181c2588144150b100d05440011030a140702c42d2070303803c0d003441d41718060310a00007841d4200d5000e07160794000801d81d1075800085140b56104000701903450740c0480704d800010311060004610f01d0b60381c1044003c20000c0c0401029036881b84004600a98800f4251801f0302070204a06c5002130405e001e11401403280108902c0300d00240d04003a420341d60440c41c0d0410a5149804000c009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 901663705 1250 901662455 901662511
    0x40602070306090804031a1902070b0a1d1e1b010c030c03051e0909090106082805070b0301091a01050714100e010209030f0f060c031009060303030c0305 67
    0x580d00702d2000301e120481800d0512151145802c040c00d032400c0702030000c9a0b1106031480307900420074a40c443e00d052603114503800c00c034000c0d80d074020700d102c0364100483c01c03001e15600701d0000c8880b101051103400101041031450300b032040254240c07005031483c160204400600444104102c0c80c0900407105410200003001e0340421a002001d1140c0c4003045001d1511131400c0d560001203802d400c241548035041400d080d90401c40000380b08081142c0046c40b1382a0601030707402111189001030950300803100161032100c40c08480003000600011803000860002c10032880245841320031130b80d0b83c1d4101000d00c020740f5400e071500d032901f01ca01c0c2c20300340d40344e41d0240c00c848031660041b07092a5032500e0740f44500d040803803400008280b00d0800000d81c03c41c18041d40245200b4204804031101c2001940901da00c52008440340c0007a90005c100082100d10440b0003076500084034801801029240e640d0b50341240e50703540042d8000399a80c0380040419400d0310459400143c266080349512060091143d10 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 901664955 1250 901663705 901663709
    0xf0c180412050f0904060603020715060b0f090d02040501030b181f0209040e0d0f0e041b0305060a09141b030609180102271014120601090506030a050f070504060207 72
    0x400c1000500c401a003034860701031303e401a83c002d00500406541ea00020040e40089d0415140c0e10030501c034103e403005143c030480d402c8800040c0c40604101d00c0c0c2c00810b280f5004040312a070418984c0c42400016600d51041a000e940305189001c03050400100a84051484411040ea00c0e0b002e150891080f608400d039240c043c00f0a00c5000d070f076414104001c1009003d030032203070081600c01c407a00340350180d03000340e002c48140c81c0075500c52481c081c0311410001651810040625403145c40015660b0316031007038101039440b41001d040c4040c001c1d40d90f10107108465039401d10400c0c0c0c204400078002d81c0780740c4030039502028496260050940c10b0070030020b1804180500450700265000700f903001d084400703406540f11151003a102002c03003c1416501003502410360b00301c1c3e02c6481030180341c601207801065502040c050390300d02c4c5030425004030004040b0783d0b8040d00c01414045443e00028140c1ea8070390041d8802c901e400c0c0085180e052000c800000039602512a8003880002c2c08180140355000441d041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 901666205 1250 901664955 901664957
    0xc0607261009051509150916030e0601060c0308060906100c05013b0f0706080a110c01020a2d03020d150f080601050301140a090302010e0f0c180412 65
    0x4280c440c1c1e65240320340001648400b441c02d0500c1c00304402d8404040103100c2401050b159a807a503a12260007203c648580d540443e44403c1640100f0300034014500d00c0704100c02c59040029450300c410718004e2400741c09a205100085010004100b0107038003003c4c04e0703008981603807104128280000010101c0e05a201640100031020084134140701c02508480703041d07074512440c030304e101b480d15146100058403240c02d13a1106403c0921a14a0800069801c500c0c299200c00351003154100780f07045031050f030050107561160382c440302d030310024403501d1000b45502d415a4000690310324040c0006002c1030100c01a00620403501441d200c1600000003004034008030786e15006941d400f42c22506801070096a20451411132030b000301080c491510b19101e8141e4907400c0844407242c0e0f80300105800c0c0c070301c846002c844084200c07000c224400c040350001e141b140d202c3d0002007408a01120f50a10340984c501000d0441d9102c4024210281000002c0c00c8240b0b480590001c4c0300c0c41e1640b108851400824140c40c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 901667455 1250 901666205 901666277
    0xe0c0304140c0604080f190314130e1314120a0c030903050105010303260c09100e03100213290a11120301060801170d0806010c060e01020c0607 63
    0x1580840c280090040244024a11130300c440d1110700c0ca640c4e80310401c0b105001841019020b8400d1040402c1c40003186525990303101e0030210307141d9409070319008a0740d0031030b902002c00c01c041500c400b00381d00c2610811094048281c0f04145081c615071040c5519031801f07041d0011141c1594411802085980d07080e5241002d007607030155442c040b187d982051384058071951811001108155020116101284440d00594640c50b440c0c5588009140705403150360509104008060541c103180b9407038a001c1580d401d20316803a000070b00c0864101003003c0d090041066000500d5403102c01c01090b044050003c1c0000640d0301118640c1141514851600d0540344c0c0030049060740c1202d05c42e5030301c014100343c407100362060781c041081e01d03000c260000e006a04c00300340120004995051105281c030a40e111a2008140c0d00d0014070081c2d236403e0014003030604221400390030102143e042d000f1411510013200006030740d20748110300b0909142022f004c8001b0001d00c04d0b400e0507980004508444044241c0741c0075 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 901668705 1250 901667455 901667483
    0x10305010c1b0309062703050304050f01110a030e010c0605070c150204030503030103062705010c0801152f030a02030c10061a132105011b091a1b10060e0c0304 70
    0x54102e0304011b201003c1841c454980100c10040044040c00440d541655130407090030072440190784003200312941a119520911105010078030802d0502d9068006050a224281e16911014299a070031244800403e102c1a080c4081104501610865050b40c0c41c0071070400381941d403926202c0c4810721001d058152180d0808044400003094004840c2d0b081c0e0319540310388c07800d181130b0f07000e045071802100c04078045900000d080301801c2d0345000d004086589003107240c421410801820008516240042c44200140f074101000400040c5444100798000f19241c2180303580b220b19110303078031500310000c5003094810410f80e00000054100c94222182982c0c9a0303461188681144002c0e52005103494500d431702c0c54031541c12996101c0c2500380034100a20440149118460b8000449641034000132040c81e8104030a8070610901c54420380c0c2907003080e01c1d240d5118181100c843d4041c02100741500980740b502030401aa201d007000502400520484910b00107001400900009101600b202c440d483c139 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 901669955 1250 901668705 901668737
    0x9020a17061c0f0b09010203040206040506070f0204180615081e0a0f0c051f050307050c01110d0203161d0f180a05091b1e18010305010c1b030906 64
    0x3141c0c0690486186036100b50071410583d081c184000015030b8100d0911012440100040c021207204c0c507000782c1194601850304060041941c0031910039106001b890300d03114010780e1030b0b001d07110340c6104c51004a0080481410b0000496800c8180b43c45245000b140c01c2003013000200b14000042000040c818010030145941810300c105640001c16410100103c5c00c10070481103030318415103c050b60000340c0501811742d44002c1455948403030010501c10300000d00c140348038500030030380304102c030002040d6042e45a82d05100344d049101405090b94010041002c0c480d0508416075610145140c200403106140360b108074001c3d580d01d212400349240c2110308565450b22145402c5442e8409103007021303440c088a00c3da0040c1026141d10145002e0038649060ba20f0244c0102811204002c013034180c0d25900300700c0d0481ca405044040e58000007108100014001802c80f694001e600500012440310044000145556903404034001040e880d91004d8000c41e60201541090311045e051101002c855088 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 901671205 1250 901669955 901669969
    0x12020703060203010f1805041a130807082511040f0b0d0311010b18131a0403050301150c0807141002042403020742140109020a1706 58
    0xc041e120500003c00050b104544414140c12112090382800b0000c600f400e4802c141c507429035003e01880c0b458184011076100e00d618107500881e1000302c0400f041103545c3c030f10480b42c00c00c5005440e46000418441e10040807100c284000b080c6c1c4c4214a0000241c03943c921031200201140300340103640d1000e84600004072075000701c203028001420101e0a420500e002411440010802485542030802550150a01da041c64148080c0035110307661700d50752504030003c2c140a0030702c240d46240042e00781c98540d080b6800c0c4907001c0c500941c0c80039540d41c1480090090244c9020804040000b4448220045a0030000791407819034080700d0043e42050000c5020f1400344036055000b4001e10024000600c003001c030b0648021003650000c5000060443d4070150101d000c1d0384809440c82060024500b003c1220000c1e20903110024120746215a400500360300c080150207010070740381c99841c2c5681c070440ba06500e0090051800c040c1c01c1d441c000220000a002840b100303104042151400d011401c0e03a40c50314 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 901672455 1250 901671205 901671209
    0x10140a0b0f1b1e1b041509020703111501060c02090403020c1002011a030303010501020705131404060614040c02031905041707060906030c080610030e12030613090f120207 75
    0x48540b800c1041e0b480507071522032880000071a014444006050900e00c000304803281081c544420070301c03c26141100380b00282000f0f41e501000909010070104008035944040c1c440a8000c0d070350040031500e181c9103d071030300e01003525850100504a004100b000e0f40b01061030f20699068414984a40f542d240c03c2e407801035622a0154070402442c040508254154003d5070a90f405017220085003111000380340d103900c020300034540140c10281003440355003810303010b42101520a0100040c4420680d9030740103100c406840440d4030903180c0070708000880700e07117400ba80000c3e81203a04000c43e0707084030000396a0f4820f2180e005241000103000700302329801383c030566009110701111004015182211907489032101d000340b070041001e440380030613000e100707100d8110005181d0300c40f000c182e218101004801c1603904000e40030103444d800c00c4104100305003c50001c40b1501c4070066140d09101081212001c00c20200500c1e440c41c0000e1500403031940d8040a00042d04602c0d40e10244030b6843c006c07410603142d5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 901673705 1250 901672455 901672477
    0x3060607020d23012007420c0e090103170f0d0f050c0c280812060f010e0f04020315060a0807090b0a20070801090b10140a0b0f 56
    0x202407180b183c2660703a400b82c60b4900b900030800c645424206110203404010000305a50090180b04e0001d5400300000001000000c10550f94014181c1c0701c1400d480182c0c02403410420184001c0f01c0050030780181c41c12101c041c00e110a03107071003903001b0981001052202030441d146050740343c00c40b81e00702c000700d626a098021445030f85483d0501b135603001e411002109a46289044000f4407010745090540d000c100c000d02c0036100140741c555480011228010202003d03441d102a21400900c2000c01441c1d02c3d606400050018a054001c03c0340313010038000c0d00381c10f220a84c0e0000d003070fa55030103114000100f4100da005072a07850700c401c4000581d680c0c01c003041c0c0110000038020900760304110134620424666569948103a2140891215401000010004504491410b00000000e1a2040c000d002c1103421580c0345a940d201070f509455600c0420340d0444214001e02c2072052561411078090f00c0041d000300031668403000800c0100303000d40308950240e400440c40321f49000d045000c0310792640706 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 901674955 1250 901673705 901673723
    0x50903030a0e030c0405040201050d0903360806090a0201120f02040b0d270f031110020405010e0406050906060f0403050a2906100513031524050603060607020d 70
    0x321a1002d011100c1094030b251080c401c503c0340d44024505406400c0c483c580c1039584a0030450382400070009480f000300201d040c00f10103c0700e58641c90740b5101c0551a211400019010740314089204448004182c00559007500004108141c1440c00100340814075428a040130001e0941c2145800030520007103168500f070b00001c2c000070030000c8d1401501e003400300071408111014209c0c000b1074120441e48040c0c19401c00003413004020810b8900860b05190103400e00340342e40030000c541241080101c04054200c698082070074081175070300500c0a21102d6003681e040002c1e83c00c2c580081d02d030400051640d4030803180065042445e4080c142568000c590010465045c20914903001f221010b0903a603450208170382d001046030031004506042d00920001d00880303180085a8000c4425034070500010b440c0003050100040007a12a103032a040728442c0c0e00d0001400a010040c4070b500346004011703595070034243c1c10184200c0c0c3d1a841100d4112501301c8566503254100d00c0440c60f1030f94102d402401644c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 901676205 1250 901674955 901674967
    0x1a030d0917030c0601080a0b07020a020901050d030e040e06070905062a10090303050403080f16050a11150105030f031309090204060504020d15050613091820030d030c050a0c020105090303 82
    0xc0021f00b00d500d05205801c0b4021031351300d07404100d03621060100c000c0e5118802c5001000f0700e0408915241a441c00b030315118520300c107040d0100c4e082e220f004844d0701c025404070782080595a4064490400750504541c240e1070120f01c82c800740e00036040329a18084945c06005662205042085603141d60140ca020a004c1c0003040d007005001050304441c00e401181c040307400039044486481e403040c42002c800c90310701145000c40c90f00329400e41115280c0d40500141d010010b4040b00304001951441040300001c0b009981448141404c1c449080155620b551050000f172691000450180e0b040c1d490324000051007198600000b001b030b00c40b9500c82d0b6005440000e1400e00d418098002811250b812075020758203c1d0745005001c0e40d44181420b81002010300c100a0001c842182c002501c0301403038091543d05400e0350785801c0c82024141904900c0c4c4001c9414803400750030207001441c1c20049a043c1017061403c00c030400380c445d12442e44000e00300100340043e9011603004009840c40c0010203001c49858031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 901677455 1250 901676205 901676219
    0x1c0c080109030f031e0c0201060f0e0420090403082d0f06010e031506060f1b0c01020312040803040f05030d060305070902070f14030c030d1a030d0917030c0601 70
    0x2081c40300c0e0940020fa010a0342c2d00c80580203005280209662404410302420a001000b0080142e04506000c41d500d84500080403007410190310050002c00c1c02144072801d144c5490f0051450079010040c055030718030662241030341d600b90515485a01800d021030f0311b0340d84022401114032000d1404085004d0b4800d211000001c1801081c0700d142c140c1000c11198441d0001501e1510315604143c0c3c1c5036210790b081c40000c44518400c55000311015005a08056180100d485d1541000704076011840074813010070098035042003c0718a109082c005140740c0100d9071030f51500380d040204050280302c000404103003000405078900c00c80c0e1b40c1000c00c0e00d840e8540000e03040d014110911082ea1b441c81001c8000c2148101442111503555028000100003c4603603100030203607058408401d00b0740030620503541c1109051000705500300710243e00003074002d40c003071342c1503003941c1d04a0b1164000d5100c2000b103284142c000e100c0030b080c4c42804031030f030101031543c0d113010303242d0320889840d010240141800080d4103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 901678705 1250 901677455 901677461
    0xa0324030b070e0604060e120f01051b160221060a0605121516021c0f1d090a0b190807082e0f0906051005030705040903020c1c0c0801 59
    0x40e9100d41c030070300c4090b102c5110854100341c2c40000709501c41003c10041281c0e90195880c0c12a101004d0301045a0203802c03034416050840181240c80d103070751154204441590000f4a10314413000880d0300c20300f0101c050900803400240308e8002401044885854600e4512310303015030100002410480304030b0318004404d900a00f80d03500c030b0203014103242c14800e040c403c004101d0818841c0101840c081c1d0350341c0c890b0910300026020007064154041c2e00405086002d06a02d00038940a0540381d85000305580e841c01083d50449402400404541548241036650303101082c50300701004440100b005400f580c000b403c0204100350100c460307103651200152034107020805c5030444902c942545d200107102495400c00ca5100d90303241146029a5803070441000440c1c4c04820a0030040c2e00c005201182c80c0c1d2540c0856400f9112110741c0e842d003c004000b00c1c030b410001800903000070790781401a45101c6c1e074003035601e00703611150354460428001e45817072410910914403145600301e03442e5403100341d581c4006402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 901679955 1250 901678705 901678709
    0x605130203010605030d0c020d020f09040302030406090605090d0b25020606090606070209040b090a1203020d0f0c0c1e1a0a050a05011206020c070b0415030f06030c0b0a0324 76
    0x42d50800c00300003007034940801c80003003040c0b06495146c80321009508002881076500c808a9000803200f24030071080e120b002095104511a070011a80c0c2d5050034405030180b002da0340031030100f01c02080980c803282c407000c44018400d98484c081107055140c50090042d4172240d010071035001d8800c0c0400c07022540d0700050311780c040e40051312058403e4580c02c0500150748907280000e034012460030003082c0054a9080c0f042d60264400080c2e5004e09150b90700d1442071004221642c1c00241c001c240d645d40c503d410720484144081203d0204000840054094106417100002502c01c035100c0c03004060740440c91505602c8903902c0800d022801540144500c200f040682e2414503081c500400254410228810300741a20b10714201084200c150f661468042d5201c01e00d4403001740110f4100245c0c0a29031000f90021b01100010741e0000380340c060b8000d0403214800c08500d01c443c05c005040000c1040e005000b81901e00d400d5041c0ea40e500032020540c0a4082c07200741690600e204d00003c106c0016414030001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 901681205 1250 901679955 901679959
    0x1216020103050c03010305060f09010212010f06120624090f0603050f0108070b120c091207081b060a0e06070807030e0f010527031207150e030703020304030f0f06051302 74
    0xc1034442242100343c60100f40402000b0b9882a80401d0145100080643e44290b6003030001d4581001c0314170030011140700b03030700c414107180c41c840c018002d107a0400f40301010392094140030402c0ba4074004a50154103046400707246030359219959001d210748904884000361031042d00c4141c1c00341e40c90000034000d0108441d10341c03012014900200300700d80041115411503a1048225080c04215102285a0b0300050300c0210010810050701344503803174001149180e5081d24001d271610519005040303080544c03000d111000500701c0800f60000381d80d00429140d40c20108d1034004018550500410902d100d01c3e04090314130100400c4040405a105041030100701094544034040a40d0310015611070041e02c0995030601003070039249002d4881c5000b42450580000c04540a080c20100c6503d407079403141c401a22201b41c0358280c0114881540038103840c104840d4000c601d0601c01d42c600039100c1c05540002040c0d110352690f000180003601190603441a00302100704a00d0070600a04080c80520f83e000324 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 901682455 1250 901681205 901681211
    0x12050d090f1202010503180a05061609061b0201030204081b0f0603040f020d1506060806180601081305010f060b0a11160918060212041119171216020103 67
    0x70403000180c01c1c900302210740000749600c03800015401590950002045e070034201c054002c0c9000780c0241080038810b070034020780c00342003241003081300300201250340007100d003d01000c1002000f05070f0344a151991040e84405040d040c1c00003900c0100d020784582d6000c0307422071040480c403012407401826181c030204811144c54100c00103500521200303001c11107000d4800c15040c400c1d240942004080500064480d00c1b03004032044144d01e581044402681085000548100401c482c07800d24040208003808071020000891030144002080300e10000e112107000c028503c08102000300940200814080c3d808040c451710381c603140313140d5040d004012000e000482e000200b41400c03100bc505614a0030b008000b01b88490304010004001d003200d8041c0e0500c002d03100d20004081123141c405442d20b4140035259082c141480e0800741c0004850300ca225100341c0000c06007040142c42c4044030400c88555102c400400311500d4411400c154000c031004080550009903d4000d54807400c040c40721602c03d032010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 901683705 1250 901682455 901682459
    0xc050c031c0e010810050f0d05010507090e01080303040c1203021908030a0c0e0a0b2805031801020a0c0b090a02150a110714060903030d09230a0210031512050d09 71
    0x4542440084c3c5c0da0424200c0c0c001c4c170510081c1080c81d5058a407840150000d081b81e041a0755143c01c50381c085500c4800196000c2d4180b02e207494184140e40148003260056066003015110000e80300381e1480340400a4a000f81c13a40109402404036002108001e40c40810090280c2403603907a651080703442c0d0800710b00d88082c861219001c2e82504440c25000790901c030744d0b503051400600c0650302440d54000344020380008034003401281c3c4a00303403500d100ca60b109034076400c0c4038580c1c1e484c0b09032008450001c1e900500914502030b40c000c0c48500d0440c2c101500718010340f038800f00541881e0010101071341081000d0703a492001c40b80d440027009a0f0138250346051046c042901244d07181c03500d03406140e01544000500e00728600e803080103866080c2c4010103a07841c0c410161241c2c4101c4035002021100481d070700b90b110f60407018000114001026000c00750940a00070f50014111440c6550501c060607a58444c099100c8401d850310400b411900ea070881d42c0007030900345207039146e18030752005c0009207045c440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 901684955 1250 901683705 901683707
    0x60d0602040f151112031306110d0e060f06090a0b1e10181505040f09240311041a030f0604060501080f03031801020f0a0c05070504110a0c050c031c0e01 67
    0x9044c0c0140c40e80084e0007101e002e07507140c9840c2c0d0f2028180f0074024410100800100e045417003509085214201e50380d5440700460403481c00d13181980708240d103980182c020000c001080081e055801802207030501841d40d1034200810050105905694002e290445141103011100040600c03001c004c139032002c491910440103c41c0c0a12502581403501d026400030003401d02c0c020045001c0314420705009080c0f42d200c900314103444440e43e0002140c00c5d2554000e11484281d4008400503204040032684030301d04540314621221a1107035a50300450351000d03c1d0072220b1200480032018000141682c444903020002e00b6a21041a20140e034550314010001410030000100751201c2103440c4040c6080d95a68000c0390042c0b00e81e20340e828019502089180c014650301c01c010702141c04180c4414200c208d107420034a00d046003a4020314007941c41c1089980c200c0c40c03124140c1c0c40304100c0f858848200c01641c6401030405900040c896018802d80d00ca00c0419280d50340700141180040d03441e4040c45041c080 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 901686205 1250 901684955 901684967
    0x304060207050909010b091e1501080c0a03141e0a0e060c0d06030c0315241a070803090105061c0b0103030f021f0c02010b04020408100203060d0602040f15 68
    0x10a80015911816003003040f401c0010b511644a40c0d428000108031000401140000508540d03a04111805840240601c0c10b0100c4c80c41d008454010b20003002c0c0342030400a80105c0000c1c00c0070b039a480000c6105400c0c2c500c45e4101d01408200282c881c2141c0c10080c04c614080e0703800910384015a20000c0000d40240b0051103060600786582000b00708a85944c0c0b4070241c280d00490018200036107a02012000c129a607a410004510801d020300e4bc0954054040003100c45400506030500808040c0e404404081c00100068400f103051141d001908140000c145d440783c00c4000784401d0010040000601041d40198410b103005d0700c40c2c400d05170f00321620690450201d600245600410350051001c24402d080e105001d030b80c00d00481c1c038160340e2129006a460f4030300b401d03034070040e031141c11501d501942805400c2c1031200941d415814907040c482e81c40d403508072403003401e02e48075404400203100345d40b040402c5020755040314045617101d4480c502000e0640b0349009118079101100140c80420f44561 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 901687455 1250 901686205 901686209
    0x9080d0503091207050304080f0d1d01020d1d1c0201020708060705070f030e0d121116290705100513020d0b0414032b02030c04141c0501020307030b030304 68
    0x50901d0074041e03c106145070300114403d03030390740c03200380000301d400c10003040840e804480a00060440d2404940001d0030700300001400d100d034032219110b40d480c5036000604048644464144001040300d0003041003c203a000c08800f03a0720115822503901030078100d22040480394000e0b801c4d25821031711744482c1540c4030410b60300e43c400a281044910f001c20800468070b8a0544030307140428081007800700089042c00c00500548200521001e94144550480c003403a50400009001c0c00c4000310502202e07070303029200d118500641d544a10b204044182b02e21550806003114400c140e00d8607000d041043d9201e00303810362080d1003880d2201050f01005c4820b80f031003000e6802801c0860020860759480200304020b0012600b00100c01c140c00b0440e8030038006018416803407002d10351070031156a80561b560b120072400b2000340c0d01c1081446031502d0210203c0703003900c01d21081f03411003804400203d40e4030710762013148113404d420050410041100c190011030203405161b40520600504804040e240c0c4114 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 901688705 1250 901687455 901687471
    0x90608031806040f060503183f032a040b0f090301140a020a1706090103170904110c0129190b0307080412050c0c0607060e010c09080d0503 61
    0x1404241d0203182260a2030300380790000307841e490805a139030200d000d1201140e040303500860404010402003280e014210081040c410005101d4100700f01410b0b0b22540d002c01c0c0f80807a0200d0038280902d0801181480c000140900d10f03015a40d2034124071185c2c9145401c208134200c04204000417442d60201000d80d0103407065403110a10b4111440c0c401d0409038401502d20740c05540314505c200c0c141c119103546501c507442040c0e001d030369151200c0000700840943c0c000110038601c4201408000d40310001818103481c0d020a024146040d0030700d0300b406500802c2c9095601c1424042c9800d0054030510150890382c184a000f8820f41c46848a0b0201001c00c44019555104030790103801084d04d0303c0c0806c180440c640f00f06a4800585480c420102940120b4001d070108424034103000c20003481c242490401e0485185c15803c0001c5ccc840301c55190720100100d00c0c442e060201e9480d044c004154070440c0700c030034040000c101d52100000301170300401041c07084010a016041c141d6401d24050b0044034455002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 901689955 1250 901688705 901688707
    0x41d040506090115050922030e120a0b0c0903030714010b09010b0c0604060f0207080f041508011212051603030905060604090b0612030c0f0c0423040f110d0b0a0609060803 75
    0x40c4401d0064489009000e050f2a1720f07c2c56010100c0340540c05100301d09402652440d485d1280c442c140184a5154122084158054200100402c0c843c0d15031541000302001000d07641d590140010b407441c040c4040181c1182e0341582400c08050055010382c9440405654040705030fa40d40840b8051030040d03c4c0c0b29017464002d60002000261654480a6405458840103080000036190403100d50081e03201d4690a401c0050240903480d071401d048c0c0c28004c0f480c904642e1642c1001d042c0c6480780c06101c4000c00860803005c3c0c0d804402e0180b0f0a0324844451592034000890392401e008025110303e40c0103942d03a00a440200360f40d0308090050032089a007000c940b5a80f911160180610f03c205d02c194001203000611482c24004000e1000c1601403403a0300060080001d0314040200302c2d009081450f080c1081d40315146062720309010410b6216401c1961094058104c0c102101011118203016a2141450002030100108200a28050300c0ca00d84200f0010b40c07200c032610100c503400d000340741c510342c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 901691205 1250 901689955 901689959
    0x5040b0901051e300c0a06020703261606060503190f0206120f150d1109040611040609061d09220b0a02090118031205070206041d040506090115 63
    0x10450303e190141e6000d4104051424030090b0505040810075030200c1140c022402181d6640d001c00c641c0b80106421a01e1680c06407610101a41e210007030b00c00141907403180002d4681480001403220782d91504030300000e6507026844110240b201408400711001440d080000c1640d04000401003164004922042150350040e102d0354518044e040040340d01500810000f041c0c3d50941c46550b0060340b00d070b41c0440e10750070900107440e8001035100c0c020f0b000345111402c810208442190501100f042920f100c683d944403410120080c0022816a0040c1500004d0004d402c0b03074409907100881b850f60380e8005204440051a00a135440c1202856220300000f0110b22060740f1445146a02c0011700d060b440410483d9075012075805044a00741c00c819030100354030f132865801c4483c100d0714049601e8031001c041c1c00c60b50303450000343c124420801000f501140381000c41d21002c04440144c00801c100b002c1112011030b03050940001224221b501c0e000300c40c00300d02c40d00c0c41401b03208481ca8160300f10b680340340c0c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 901692455 1250 901691205 901691239
    0x80705090f03010b0d050105040203120702151602030d08071d030618101811030105160f030605030a0b04030e06030108060a0b060403121808070506070212030715020405040b090105 79
    0x4640c01d0039282e407656844c00804142d960f00e0640c0110a8410000407a4601d0240101424580c59403c880320081c01005642c00584c0c403050314070002c01e000d402150712820561000000d06946440013505441040054009180c0282000b40b04504a40c0c510f072804080c00340070084607104007055901648039401040201d2a001002c100c0f503a950001c5541c12072a15000f80261204804250f0b40b408552840710103000e042510000304120a80c000d11550034000c00b18120340f1848800b2000b0865809407414440d44650071a00040c9001005c41e080103216081a0086010070b45046010490352940a580f5042c0001500d04948188028110301e60304c1c201c0000c0503010039881591300c904100404000145943d5400b070303418910381e0320151601c2c901450f801001c40d42d40c00c0f00c030503136100341c1c0d0400a5981d0740d4211041136034103590340315124425494a0349075000d0058014181e56041c5000e40407950a0342c040d1007100c80464003404041c86036800d005e040c01003802680d07009519001850200 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 901693705 1250 901692455 901692469
    0x130b101710030807112b02030d140a0f020c100207090b1002030d02030c070f0609020411090a0302130204240215072703200f190312020f010501141008070509 69
    0x7017405011a400d130210681c44003d0003213000c5406951000e01d0240505508040012000e54001801d00120218420250b120140a100040c0d020015204030000325a8424046580c1180380904040d414500304a00603444016500811018900d4207010348000d2800f030f040d05414860741d03000355240031144203108010303601c01400941c0140042200c1800644041c91400c410380c002c41001485525605c1004191501e444d11a01560000c0c1b20261943da120f00b02c480845e94100c8248544c040381c180708e80f02902581d4400c8102c5a4400325548000040c40e20110000000e54207940220100345184092010162080d600041e01190b51100d040c050039041f045015800d4059542c3e142e907542c90907003800d078420101784140b0181110000c03d0400820200e46d100e000c03a82e8007000c004103016a131654466210192288440c80608001980240070010780010100002d1220750b0311410321701c0504250300d004a0081c1c0d800066a54001d103d03041003801105c40741d40c1d0700c1ca40003000c810446e072 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 901694955 1250 901693705 901693733
    0x123608120c0f0d0203040b1308031303020c0603160807051306030f02070b09010b011715010f091a0a110d021b0316090e0c01051206130b101710030807 66
    0x74022042040501c214100303005840018194480540d40349807a10b898501c4460180445c1d41080c0041d8441c00041d42d80c03025030358040b001111030744c50001c0d1030804918200505a400b81c03c4000001400001407480a01811085041c0c5030f004e2607071940070040f141c038410000301c20110842d680f82030004510071b41050a111100100250500321030340c4450710840010b441c0500c1e0f80e0354440081d200707560000d00118440b0070f170750150b400d9031611105542100040c030303004a040106600d1512403140c0200303d4100a0301c00482641c0b03010600d030040c20020751001c1d01c3e0602045a6101c2c103140702d50001f5513202042c812b5406000b886440110101d0b10f18141c00005526003e080c50f190303c850361000711580100403141c4003007a03404506191606140c5007a02e040d040110412030344003400342b2890410f8104d082590340b8040d0341529100e9000500a20312a07e90000410045890180c0c0c85480d04101c0a2541c65200b8541c03102c4820180403000c511005050f40c10030302081c400f090b00038240d002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 901696205 1250 901694955 901694971
    0x71404060c15050f010603063002041b03020711040513121e05130f030b07080405070308030f060f04050702190c051f0e0102070609090b0112360812 65
    0x495032405103032030161030044480a11300000c071401080107980c507000d050028403207203244c0000401c60060340f10082c49000c0401d08010301b2038058104540300ca034054090341001c0740e45c40d17014100c0400000c000c8d610a1303809643d01c070b000c2c2005e036810380341503c00c580c02030011101e00541c00900b5a02c041e05202e01d07040302400e0110303500846400301e9131100e00c8124041c0c00d0740e416507200340c0703000c2c81d0b00755030703442c2e00581a841440b00084c030003e0308907288a5040b041e43d00745084240e0791894010f180541c90b40001308031080100a10140480c40034085015120450760a1319500711107040c0000c81e03508454a1005038030080b1812403a108001da207009850088001a00e00b075180e8012903400303040000070910001040101612199102c44c0801c0c116100b480035215051600030010b160b5983c5020319003c1c66901c46124003180e0003072110320300288030324005001015114001146000700c5800400c032a41d50129010300003454540007061303ea500281c00d9090a08864401056100c01003030781c0707 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 901697455 1250 901696205 901696223
    0x10c020f03060109090b010f140904050304080a030c1a09060a11040305150702280602090315040c05043801020717030304140c0d080901051c090605071404060c 70
    0x201e072000d000c100d01915100d88003260030380651600001c0400305a0000240c651844810301c0b4452035016021040303d4112400c09841c1c80d03a0510750704511072680500c0892040400b101d04040d0406907103809a80502400381078a813a040c903d0071010401c90707480082d87c0004000660498059002c0141288900d0603d814940c0700d83e0b5282c6403585084c00c5044086901080003a01641003102900c010310540d03696050301800c0140c13007034454440400807c0c164001ca040c264948007001084c8102048a000c04000e0906081010928100d4000d00e4042c0d403c02c00d40c50029010a6080c81031302840a0700300091510315021010010702c07514055045000c1c84000140c0d000030001c8420395080050041c580e80e04203441c100000c0100c90071102c4254108c2b2000100959581800300e00682d0841490f6540f00b69810040f146031252000c80c502030303565503a0301d252505c174542c48034011b40d12130002000140c990207010b460948401180401c03903502000144021486150740385c00c0350b803107200c0c0c403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 901698705 1250 901697455 901697479
    0xf02040803040801050109110a21090b100303090b0408102417100e1c05090d060b0406090213150c020d141506010c030809030c0a05031306090e010302010c02 69
    0x10741580e010ba840085603030b44800041c01a07072400c1c030902d0755160541040600d08054420003421262440140c034045401903004424150800c0d008290306a41c000d104138110700e400b2500070021800b601040d0700164100502242c1c00010b03500b19401d6403800c000030003410051103920000b40c07154854200c140111a5260b040c0d198201c00444040c103010080e000300c044401203068649008484084002814000408503109000c80c40105510300c2908450030705904840c1a181d605c580000b031034201080410100621109a00000c0800e4085400717001c5141d03500e11500607030268480744104000c1c80c83e006c000c81058941030f07074501d00d818180011940c5464000541c195008035040d07401d2b40c0b0075100c8443d060814800410601101070842c0e0740e509020f000242078a9100030300409101500001c9103500d5020004d40f11415255411242149e0301071410507100e402c1051861549900d00c807001c5005401980c0040548130049006039550707103150011505194115402d07078000e0241c0c005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 901699955 1250 901698705 901698719
    0xa1b02161e1e050306010803041a0f07031803170405031614130905060106080612010e0c0418140304080f0615090c090a0b0414010201050c0706150803040914090309090a0f0204 77
    0xa11750081202401960f1100c0c600100084040c001d07245d85070881e8010400c0c01c000100d284280c0726010707014580020500d5001d20341c0310300d0b00d074140c0000c0c100480130404141c0e0031b18404000c01c21b8940c244c0070340c3d01201016104e0100342d0000c2c064042440070a180e160490700f001c521500c0201c080540c0450300d046503482e12420075400780c21203400a80490708101060910881001c0034015000c0200030204c030100c40035440780802403119100729240c10380c8054051082a0003001e544e04442c0181c0c102c00c1b510360701c994940c058810f00015010b10f0210080d00c6001181961244000011300d4039400511020001c110600504400d410701e0709000c440019104c21540d4070140c01c0404004d9a17840c141021644001150719816045a040204000102501e02c09403110a80d01c02e00115019544020341d8040040c2070700318001910011900040e0041c1c5600940704001540c1740d0040340313482d03100c106912486103c10729a00040d0075030100c1c1c0c0381c102c154000031200d0252030005040c143c4801c9 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 901701205 1250 901699955 901699963
    0x1802031b130b0a030906290111010b060316030b09010b09040903140706090b10210812040602120f04022413062304031a0a1b02161e1e0503 61
    0x181240042d644200545c100841d40c81202c64a402501c003000c00c9400c40141e1003040e4010b10103130782c10030078000c5150500d80800d400404641e04002c000548a203440109a070350910b0580c15030740000e080944050907410408840c50503210640e803018940007646051001408901c5000c40070088400349464100d14020003800c54644640c801107040e1060f81095480360b4405401c486040a010301c0400101303c01043d60b00082c0c15904c8182c03241da800c0d081042450051010005940c00b24008000410074660b0007000321660360480c2404903103449014008075601110001d4011440c02202098a41600d1080d5040340c00810141d15081851940d1210b50b51541d2000300407c00d0590750301301c51148840c00641081d20044030608052842c0c88520748801c07002c0b1207a1019041e400400e0b600c01d801e820868084150511504110084d40002036485050484580700d05070700d050041060b10108002180305511a400e80d240641403001d81c071182c4865100000d4441d00c40c42001590741c41c148 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 901702455 1250 901701205 901701217
    0xd0305070c14060a050c270d020402030c0d060f15030504050f0d05180303070206071202010b060414090a0b100e0f0a030c0602120a02071814040c1802031b130b 70
    0x40150005040c01d1a0b140d090f1040581220000711050050016000f0401c40b21880c0c8014640307141c4118000401013001c5020304423000e500240000100817a6642c5c50009140c0214a11400c124207540d070039401409240034000c070020b42c0014030440c204280309401503504140103034240d8500c85d00350002185021780009980000c500c0206441203a1603a155a80e450b0b50000d4000c2c1d03142c07240030381c000343d0540300d014002030003011001000d1070014801d500130540c1c1040034007220b0f5120346034813030340c2e00444d01e21002c64450400c1e8000106040d8680c0180c45110202400001c424074281300c2c103071904103280340c40c2501305a528031300c116a0398410400100441c060384400740803034200100241040c50208250a042400b0842d1400103039001074500b0440e041c5041090b210250b80082d0340107801d81c2020541050310b030310180810300181001100440d480c1c407640820b4021207004076410303800102c400c410042c5030b0729030b00000b51070040020568071181c41040c801c0c940d25400c51401030340041c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 901703705 1250 901702455 901702493
    0x809030f06090c010f0905030c040e0f120403060f142a130608130b041b12030806091e1614121e090d140c0708032503020d0305070c 58
    0x40c1c15481c5055800c51103a0781104058900101c5140c01c0c0004a2740d140308010140d4001d80c0e98910880301c4a50510030304500c036125030252040a040f1f840c86c000c498209000589241c0e19004030031411791180e104400a01081d03100108280c0e9503612a460320203030880007981000b8801c074110080180c1d0070003c20100700e590f0b51040f003045c2450802440790b00000e0800c1128040c068400007c1015400c22561241c0d01c60540c070901051030b04804500c02c00303a80f0807000d800300510303001d0070141c01034181340c4680b0050703d4046c0703070b559120a00171080102d002d01ca1301c1190b213440071582040084001403070443d000c1c00c2400c40130b90003900001c090b602c02d0030290300031801c110502000d0601da004000404181c546025428182070032456115004950000d0500080319081c00b41c400b2920b06680d048035110003681d04c06551800116120343c040700c1c1500c03005914441d0f00381c62040c1e9044030000341d42c0681c0181199005160168010500501604140301d14201c0c500001000003a00c00c40b10041 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 901704955 1250 901703705 901703713
    0xe1005090f040b010e13060f0e04021e04061203030e010b031902010e0607080f130b03060f0108090a0c0f17070803030601140702130c1b0209060607150507020d090f05010504030809030f0609 83
    0x4d0803448e0701b5081840e41024070085100390034080540d135000041d60b0b58a0b600a004034030244203600080040c00c642d4025440384081c00d400805158050340b040c5448a201002404481854010580ca400980700d011781e040170602d040030050f51003060381d07803040c4c0300180040d80b0b44070842d202c5c094550062003441d0009840003e0240c0018030020000c001092990741660550425000141c0e210311880c010340e042180b00d200140014104100d004009604184405030943d19000200d0a42c8400d00800040340e54518004c000b44200282110854001401540c11a02c0f820011203003002d100d02c45669541003449060056554001026601c50b103a883c00902a0540000584041001c03801410a0020203900f10b0150710f40000c403690010301101c01c04d640302e000d403034050f101885600b49000343c6c51030b1000b003010b81900001c020350310000c03a488408409985146076801643c140c01030900041e414030003000052018409042e030154014103888612006040f80e030716140046544540a44c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 901706205 1250 901704955 901704959
    0x7020304090906020d381305060f1e1207030f1b0b0a020102180603090d110a0b0a2403050309010e04090b1009050a14040807030318030e1005090f040b010e1306 70
    0xc105000140b0001001c24546c03103c80d09100041c0003034403901124203a1512400002d40b503550340c404c0082100001004201200e80f4032869809581800141a01030801101d42c2050300750001407503c00c40e0342c041ea29444a030085e1752504500a028080c0c0f0b03100c070a0241c40802d03844900800b404440500360300058403044c1200f503851500003170340403850140f182002440101c03400490905d1488400d418103904181846001d980340c0411074802401c044451030601c9040c41850300500062046208500ca2506100c100941c03c12000d1000074526441004440701a5014501c1c0100d000c038011300000f8460b01d40c1c1c46081142d00100c074200c68044041c0303000d0104d40b9080c030800340c00020f440801c01405009030085d03da884406803014109200c0031070201300f0107200350404168490305441d071000c115903500e0041c0a101c04154120b1141c80002041c0080d6445034041c1c9000e2907004001181805504050100400d0850307001810020340e07085001542e21070849260031504a03c4c40024458 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 901707455 1250 901706205 901706261
    0x8070b040309090e03090f06160501020306030d021f050c0d02030f0a0507090b07031d0d0b010e090604020109050d0302161205120304080343031407020304090906020d 73
    0x640302d038000c141803d00d80480010320441c00403d4070410441075604480015580d000104503008003046c5c14a64190a4058000c120301900514000c08054084607003c00c19148240d880780c503002c180c603080c0311010814041c18161070f080300b074100804400c42450540c0b4514400e060f0b0303104583e0036610311200c0090103000c048520846522000c80d14120f4441414840c0010b100c0c8030303401d0080c0c01c2201d040f28074041c0440001a840c06050002d0240c4441c0c411840e1007000f04800f440b9440108580000184103090003083c214030855050b900c10119a040c0001c0001e001d43e0b0b540c0a5007140704108807103150002076103180000d003010442503121b008040c5049c0c0d1402601c40e5140c0c090030020b02c1404001110301040d250030001060210104210300f40f0305c06003d10b181d044405641107140003c400821000f0440d9269000e01c3c0d600744280807088031407040821082d00c07542d005900c1000304201e0706c481c90b444050140d10406000d4034209584980c082990701c5a840241040742240c402c0d5404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 901708705 1250 901707455 901707467
    0x304030c1b061121090a0b16020a1a07080c010f0e06060f030312010e06010212220806070e060c0a02120c120d0c111c1505180c040e070308070b0403 65
    0x40c2c081200400c09880c101c405801c00c505040940d14001e0070108000175240da41c81c0400024010003550303180c440549000d04103080d8200c10060340500749182000c9440a88489421901c2e070494000615000c0c0f199075007800c0d40d0094040078295560b81600003a0034049000320b485050030b0710000c14560804408202c034801c1d2001400b4482e600c1008140201c400c040c2d2614110b40050a12195641d14040143d081c80104103403011510400620801004800144070040c1d40392403a00c240015101c6075416a1500142c3d03100004c0b415003070718a4541d00d0410000c003280c10220042d1100f040080c1d012a00128901c0c110850980003220700882c617040c024400540034500700014240240e000c0e5000c2c1c80e401c8020030142255240088419441e02d036101e00050342018501041e0b007070b00087c01d11503080c94240b4034008038a420320020491141000110194501b081000341010485480030080103084404108103903028402c00040450910b20280105a000ea080340b4050710385441c008000d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 901709955 1250 901708705 901708727
    0x606020a0519030e09042d150c020304051008071404060c0605061909020405120105010e161701060c110901062114070206040b0601082503110406050405010e09011a0304030c1b06 78
    0x10414030310306511f0100740c00304410280b00c034031140005010700d000380007242103100790713001107400180203090904900c1e0b1144900c0d21402c0780e9600c10b4210107882440da9410700c101e12490700013a402c0885500820101e0344030300e4121710000c2c90708040b10281002d41d035844a00c1d601110344d60340d01213002c00403802c00d51a800340780b1003208001c20082d8113145002c49014000380050007441c41c00040200103030b00503c10008202040c640d400d00a60356010000e004030380c14030302280e4881d55041003507104d00b0802d0209060342c51a4076600c49008100c40c0040d00b0407078050f40010001d4854810000380714041c1c8c0d000e801040b5941c041c14141c6000d0401a03064480603068078100806a070070480e214440080525040001140f005c441c10525042100a840c0d446c403e60701c40c210004d00000c0541d000303001402120401c1e21507040e130304600303410461180001d1040c00030624160b405a40c1488240000390391007442400d1031200e030b81305503c5120380c02050303174840980060004018010142c05c034544c1c100b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 901711205 1250 901709955 901710023
    0x30209190e0106080c0d0501260f120a0210060e0f090601060206010b0a030b10080a060611070504230103060f060803090f0f0d170304060606020a0519030e0904 70
    0xd42203160003080840c07004148101c038100410034000c1260703000709030201c1d0480c0c40c0d05107040c0103958690b5114500d0714041642a10200c0d0408030000200d28003007191058000c0040c054543d55000c07024054055108145080c11409030b0040b1142c20552446800d0107880f00340d204003864034103c0d4a01451442c094821850369100000411185a0024184c2e0648103080c180b561078940c3c240054002e8900b00410f1644040c296000208260f4080314181c89268103900c00d0014555800d01070ba195000c80b00080d840e9081000c050040d81480c1d0080302c00c040442000002404014800f44600442038204548041e01c1d840d00f14a250520300404000c0c049550107186400c400c4000502203401903d00180107180c244004603299031350480c81c5801d15040341d401c40c0c1e15001c107038100e01c1c15482150704942a5190490104887c1e00c00a240c0c022194072000408860030300111507103d05c4034456048080101072201c03070013991140714020340101e1090003d901c5001155203619103241e44006021 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 901712455 1250 901711205 901711249
    0x19050c0415021c12020702120d020c0f1e0114040e01031a010503031e0d0624090602060a2a05211b0706090501090c0806010b0a09091e0c030209 63
    0x12401c0280803021070070543c0c581c2000e2a80c0200344810402074054800060b51100140401c0104004041510700c9064605c2d0301361800700e4080c01c10842156800007059801a00180b101c400280f0800349880d4590b0301418801510454003611030640d500680008840302040001082040101c84058421014842038969150b05050100c0d07038a001c0c4c10b4181c4034000d064510b80e065002064210303840300400e05014043d02d500d4408815505040200550a80e4285444541c440c0c0c4210900801c1d1201c5038050402510340040350005002038903258642103a1803881c040030052810401a01903c6580340e2070749a08007403500003001c03c844a01c0004002c02c00081107407410701c4098140224041d02380c840d8a44485051003001000d1030302000340300d58a49511a4280445014400100d0700410b045890507a01d81c103007003155000d0300300002e0100b005144244030821040d00445803148070885154040703080b03103011400751061001c440d40826800200d00d105070801110031515070203110f076a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 901713705 1250 901712455 901712473
    0xf02150417130306050132060a1202090415052e0f1103030406090c082d0114010b031005010306051305060a1701060906080f1519050c041502 62
    0x7000c01015224900e040d00000b030026101c0b000e10b21190050340e04154100320940c1c48561486115070703d009104001006601850074175044541204900720000c5c00e080c1c04e02404500c1076a24005c4105c0c2e0910341c1d0740174030610b00e09485a204100c914450004160b040d10f1414003480003052403403c80e0944030320300101087d010b016240d0481c0015a5619100c1120070348040c04403850040c01150200030f010000510007800415040f104403a80034a842c0ca1103569150700190780d5941040304030b50502801a036240d0413100395003010300225903d100108560403c0011102c0c0c0c1602600010f00b801d1000c002d0100224682041d400601001e003010410141445c0005001031100c1580c0306280d6152400900f898503150880c4004180022150341c00107506902c10f4041c0c00280103409003246481c10001d404840042c1c0f0003083c418009c0501030019040c100540c4800004244c410b840020420940c0041c1d090711a8502c03443d0314501c00ba40310307820304102c1c0504020280381901103501c00741c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 901714955 1250 901713705 901713713
    0x702040b060a0c0b13050f010605120d0e01050d1103040f0b0112150f150305010b1f0512070e03150405010b010c0c150915030203100b1303021e0d030f021504 69
    0x15a580642c0c1203403040130a41d070303000070469181c2640d030001000c3d4050300c401400b03c048150068400d640003101c0a2100c40894064607030340300b05031205500000e420306059141075000d10b0040110042c5404080742d511411201003903503034401d8908a5541e06c0422010301480b1a00122502418141c0580000c2009607219106840391140148508564450f404500d6401540c0900c200c1c040064038441c0f00d135030b00c0c01c0c114001c01d40000d02d1070007204184000c164004444114540140c81c03034030f601d4241041c2620080604400421030024842d010000c482c10740d50820401c0541e101007813001da09490149070071802c2d00d840e403031407a051004003c1c04c0b00004806002010980c1d62136810a501740c200c00100f00c51010304c0b5032002100908200e090354109625400443c41a00d042244041503940c5900ac104940314a449000000090700e40038001450420390030301014416404000602c03407042c0000d28004551407044000c0b42007920300e8002250140310040701061440e41c00c040034541529 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 901716205 1250 901714955 901714967
    0x90504030e01080c03310203010c18080c01050a0f02010e0304120c05040b09190912120b01090810020c070b130e150d0f020303070f050c1e0d0201051303060903050702040b060a 77
    0xc1034a216440000d810600310090a60804511f50014020b01010030100c0001e032010f8102600c1150100041c032002c0b03501c420026001500d0b14060350359618040d182007046031000c54442c1c0010440d503c3c0c00707044904001c01c00c0504081c141c512001d1000002e03074030341140318020660101d40138500b00f07000c0c20312583c3d80c1018140e00c8002e285440001190980305a4018580510024100d141f80b003c1204a282c0c45550403000c3e155035074041124914480040d296040148600301081d40220525840c418468002d007105a0b03076102105d00e000e84540d039116080c1c11032010850134407030f6030707000308000b9028a0207543c11031030003150610500403d01c081040b6407140c02000d00801030700007141c02152003c108550300241c00c05400c1121100500e05113464444500d002441080ca690940e180b030548007a0310544000000e001c414090b80320703070054415030028500c0a82c880a03085000021542074010300010030720035074525954204074810442110682d1081c0c3d4003e00060000300c0b81590089 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 901717455 1250 901716205 901716241
    0x170408030402300105060103060509040507260a0f020f0a030c120c05040e070806100605070b0a02071406060a0905040519060e0d0201060312020a0c1806090504030e01080c03 76
    0x640c0f4201500220300100c48030b2003502248184030240c0c0420710640590662149010700000d0b6010b00030035a803181008000d020984001c0c140303030401c64041000d410444040304a00d144581c1102c10044080b06543c2061140241510600c46002000d800c40c54a1904440b0b0010b080b902140300c581580c54004110140340580381c000200032032810700780703c6088240070042000903c28000903e1504c01c55071248030b1441051101e200d800b0101784409251500d4405031041070f601c89050904d0b40d10790783d00c0000d014100c2010240d08020110114807107240010a03c00040001d080b52b04061050059600703955010900051521042c0000108080751003691210f8030114001c0040c4030b810710030010003401c1c14410341d910550010a034142c1d019041141260300501d0540c60101003604141e843d000f45010080206a11010034401010301c0710445240784003440000030b4540d1210a5501200c0c015030741a800b103003444140000340e603403080e9a41e500c440c20036061401d40c28841e8440640d11010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 901718705 1250 901717455 901717459
    0x607330e030c010e06010b1806091e03011b0c020103020310080a0f03020d030204030f06050402030705090a09030e0303121b0705011422080a0e01030b040f0207150203160507082701170408030402 85
    0x154003030100503503c8100350781e4618ac0c000c0501d078054000e0301c9001c54801d100036401c2e0095007400d81c1d100480c0e0300018458090311a0740c5a0108070700442c2e004400960006104071840503158a0105031402c1c20825110107508c42c400708550409181006482c2c5014003141d0000c0500421042c400520754a0361098165808035000c21252a0380c40002c1c100400e682100390840d20050400c025017001ea0070030010305020340c8521110078400c0c8280340c0c5900c01c5a1400c40041a1400403d031094481e03500d04002001584403203007850030a540b110300b5545c000e100c420904591100348030f00d195004010301002c6003014200c0c2050980340e078598440b40680000282072200d81b540c03a002d00d90080e00404115000100200002c05140184600030b40127800259003005110302440b00d11415403007243e000d941c00141c204a0002107010860f8680e101500c1122004824080c4d00c1d048207048400d140e4492218803000342e0041c502000502d40e4004400d00701c1c10301c005a0900000c101c100c1c040740c0d045501 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 901719955 1250 901718705 901718737
    0x1e050c090a0b030a030504090f140c0c0a05030a09090506060a020601090c03022101030b010e150d0305070510060816031a100e130b060607330e030c010e06010b 70
    0x181c124200d00801ca0304540b641c00d401051540c1d420940e01030000d006491011908121001e0900c40400842c0d1342e80741e0001204845002195803600784401502a044842c82200c1d030f14882c87e07480d40c0c110b40040f900080803508681d400e00006800340207040c0d120342d0544285052410398400203643c0c0c0d1042c030680d0100c550b203a0001c4400b81c0309804170f4045806c0219500eaa42206180d540b6180c0024401a281805000004102d41500407546401003020b0321311014802c4420007001135902d441c1000b04c040c000e04001c0b01001901c1809444801e100034038000035954908040c81341400039402039007000072008641030000880448054146035001d60b4125019076502c820082e4290864100030000c50300d84041150b440e961700b1001c00710340c0c400c003200d543c1a00d0350401c3c00316a00850308020109101400f19140c0608040b610464206064136a0440d999003081c40404889241500304056080000c0c800301a242c01d002c1c085a0004480003071a49600d0010610301d10b0103407000d9100754441e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 901721205 1250 901719955 901719961
    0x702030a03150b0c100e0a021005091311090901080607052205150a141305061e030c09040b090412050307090b04180e010509070b0904020403050d0302071e050c09 71
    0x1100200094000c5110150365818110860350752148045465405e02c1d04000100080740320200d42e031462191f020305170150442d0203410948440c1c12000d000d680001810100501c1c81d0100d0060901641445a8190351411001e00348100391505800c00b00c0903a12800c148091141d0050448808141003110211085400c04080201f0200d0390712141e8480d07250704028980f000a240244040c400c0c5031920403040c000d18100c0580d6000701045003007a190881c0003040141444001800301c01204e40c4030043c2180603a61545203a001a50340c04e030861000304081546007402e20420005500403150410645132070b644200d0100c511400100801a01002140845000300d10007800760880e2244140c4454480c488100d54421010250820390f091888612003072606200c1d040c006c40e2014040c00301d26007050000803040e83f03c2061641c02c940d08000010210b40d042c4801141c07a2596a0050395409003407e042207102410503c042000403050070701d0300018400190b40380220010b5410740d4082d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 901722455 1250 901721205 901721231
    0x11d0c0d020a121104050403051b160315091b090606050c0304120318080a0b0a1b08091516081e040201080c0c01090c0312030b030316020411040905040b06010302030702030a03 77
    0x2103424120b25001030a01b02440109500318010303244840c901548000c0c2a8007190006540f007404043c1c4110b500e01c0c0700d0050002c182100340b0880c2003080c480c07000c01e00500e140c0d03075902207028542c120403006106480501c81c000b2603006070402031115251082c10b141400d96019100c0c451441000380c05641056103404142c080d541d049641c0168000b410b5001d90348a0007a601c40780301c07240c115881c00b104000140c80343d40d140300d180d444411506d00001c1d41c0c0780d000c40550f910100030300954a24401c44601c00d140d03800051003240b00d1002d0224460910003502800b0346a408050041050300400c01d081ca00303401082c2e01243d40c482c3c4c09113060041c0d901e170701c102100b26200e1421141001e50078401b0780c900b440440100002202d104140c48110203101c507c04804481021092980c542c0013000009008204002c1020305180018800a80c1920714000522903501c140c0c40440400d4461003040f0901c61460911640035200303080940c95883d141800940301e1155600d0701d4180742c1d480000082138 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 901723705 1250 901722455 901722473
    0x417090f040e1219080705031306090201020712140f010612110f310b0a12062c01060501170c1606020d090c150903081b011d0c0d020a12 60
    0x250f025a07038442e41d5060301c0d0022060000c0111098004624032501040201744188210b81c1b0605000059040944a40ea2054040c10742c050301039045106176a40030034200381100c442c01500744102c80e05071510150411450402c80000600e520507490410200301200b00008900a03040d40400c1d031050100891001401d0307440e094641c660004c034450403a49060008804040802c102041c0c0710020300140303103449090b40d0424071415084440c880c001c000b17000007040040d00c2c0c1d5108540109201c1088004441d60342c00407844a507540c02d5205254103c070600b84140c00c0548420311300a000310b0001c0440100e5840040c1141100c1003002450b0300020b05a01c0382038900d9580f01e00150f655a40021042000d09929a419540d80341c070004001414492101001d00803202038032030301c003505e14541719440c05400000c8403000c002500b225108040d0b0007845120260404c00340ba0064507401d50032505d14004941f00300d43c0c041c2c480d0702000005660b40003d03003403c5500b0010f03141c01800192901d0101d03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 901724955 1250 901723705 901723723
    0xf0a030b0c041a040302031e0c040c1709010519020c07060815040c032403051b0a090903091a090109180b030303014505040c1701050417090f040e 64
    0x3c24440b110308004900c0d0150014011039000718200c4800754110100c81c111038501d10f04501844c0e2152240304a0340c201504034036002680d604040030044a1275210304490340d4100c0c1c003143c55954490030040882d41d01e85408a80c800c25071011400e1202003094070b665596103000788814400608005104603030314a01c407403030140d805001400b8000e400c08020f40030304a448d400881507600e50b92a19010f20950124104480e0020300500319860000e942c144002001a034058101e01d488138041584041b50050b038044034401c2c1e0b0b54880d10b6103840c00c0007841100e40107200590810810040f400c0d40c0e4043e6911050782c024000c0201d0680007040c40304010403100210b56054007003c800001c80541c092000d0785030018418007240c00c442c191101c050230281c1c0c0590b02d07607600c5681842d40500c1c41c055200c1680079100f280b104106c40e480711030030998031000b440700c0a40d581d125402c0004200064110384002c4400b20f05550030030850780700203083d001d0942d2800340915a190135100c0541010054590 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 901726205 1250 901724955 901724969
    0xc020a20060423090106020318100318030509090a02030127020415020714030708030706021602090103150f1806050912030c070c080a03170901110309010e0c0f0a030b0c04 75
    0x81440c08102044580300c26025100d04c0790031075100003e000c60011086801d80b025816464054401c46030420400042c4092403108043da04da0729807074842d461501d0350380054069201c00341c039580380740100702407a407009042c60040740c0144010809009800e0180100d501ca03442d060f6144100313000e01000034051130b8802c03200000402c0d10380c0101500480d000c02501c2c01a02440c040c14a42000d041d40e82425204490070341d0300400628000c501b07954083c040700030ba020500074600c201d0390000740080b0006e80080d103a81118a5009455051030300c210070b03051254070b809204150710801501081554010f01802c0e1544480008800f02401d01c02041c12101d50b000040e182e0420200300f00c9660814039007102d4a0704000340100d200d2000284044d001d030360607603c03642c1460754880c400e206445c010300320300001d6480d85034441d0102c84100c099442100e60100000c3c0000e003a940e818580684619000c2c000c0140c4841c13400c454503808102c1040ea074110031540c0c12500c2d41d006082142c0f14030b074000d0f5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 901727455 1250 901726205 901726229
    0xb090c0a141306090509220f0206040e010e0906091b0109051005030709090509071203020316060f06050414040311070b0304032105160e0109050402040b040503010c020a200604 77
    0x1903031049a40b000d14003a40c00c1a642c51103450380710800d00c05d001006540c1102c00c806071b04401d02020000443c0078880d28450001c8100c6102203601188581e00311340c00501c0700c001d83c10018070019802d0030b40942d001c101c01c07006092a040c000070341503c61146d1050941e0f80c0c81da45600e10a40c0c0d000e8804480104000f51a0000da084440c0006241d40c02c1a00c403d40040e4440c400040e540180c1d004817400f070402000508495407401c4085c8803200b15800c0e084055000c1030024482443d0000070652402d40600800309000c8041e1410030100c0d0340c60b0300001e03c41c03481c184802d120011240b000c583c2c4181e0604080d020200701045440c50702078258401940130500204010806502c1035404240d40c801c80c1c0d18107045154140d007441075810880311220542c01500710a03a1f100c0c8908160314103d241030509202480e11040407030141e0788103410185035031400050811850609220b50b40540c40e00303201400c612440e07591000801500d00400d14540c0d4145400700d8110b645500031140140101e000030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 901728705 1250 901727455 901727467
    0xf212d0e010f0903210f090e010e071e0207030204061a1b030903030c011b09030f12031104030609050f03070b0412050d020d0903030605150f03220c03050c040b090c0a14 74
    0x900845c025031101c001500344035003c6110790244050400f541d00c0d0514400190b8205044043d40e01c0000700304808200c041c015105610100000c038103002969a40640721890540c01804190340781644400000c504c020032000c4101e4403201a0340d4904025454070822440c600c00b801d01d98040c11446951501002420784600b5105601c01240302241440c401e040741020384094441c4031071440301030700300b5000d41d00c1c01c800101c010b0300d84003544a207400c002542c1c0401c42c440480c40e42042c1c00886205940d0720b10401484001c1007010110000340c4000c44c5091000d0781d0380700306400302030402000d4200540f21403903007a015074145d48080c0702480e021500c5a000c2010100644480c440c203902180c602040495a400c10394002d02e9455400c81080f45000da24103640c1c04154070051054100c0080c142c2c041c070100171a821401c1095000b0b41e0a2a2441e0071820b06506000007091a10303c03031031a01e484440107448060340194880080342140da103400c503058090b902920b100801e41d031408000288 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 901729955 1250 901728705 901728743
    0x90f070b031b090d0809030f011b080114030d0c1a070302120609012126030f180703030503070e0a0305030a030e031201030f212d0e010f0903 62
    0x140d4418030700c000c0a16401d11000d440700b50284111030070241c020400d00c08200105405074000d140184014040314214000a001c007402c540061510f8449a586400c3c030381085c0b0351044ca541d01401040d0b5290086060140009580f0030080180b4403c3c480c0c4a01150244090708080c901c080b500c1780505074182c541014010002e600451112a88040c20b0f0301007040303400c2c00101981a6501c01045040442d01c0190040201c0da01d220210741c822541580700c07240c40c00ca001a20110268486e2a0b9202d003801644c0100290000b4280140c290b10302d20036a000c10800100881141e41604050f980d81d1901041203815221301512a90400000500042080b000000030103608455079020000030a880c060f80751244101c2861b00d5846545900500c081a0b0b1040003030b034001e102d44c2c04030150104120340031468910460b2102c01081044900002c2081d001c0304108110701c841080b503481404c0500c0c094800c0750040c40d0241040741184078044007900a005107006960000d110760800310240c4e40d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 901731205 1250 901729955 901729957
    0x5030705030c06071e080a2d0b120d0804032123060f010504090b040b0d0501020c06060121050709081605041401050904080904020f0301170606010f0e010305090f070b 73
    0x10710400052104000c008600e41c44008104130900b144c1e40783caa841d10303101044c02c0034020500064404548c11000040780c3d0f080c0515401400f9800e5201052040c07204c0104118410024182072040d00b18081900d2031592010708241d12927031604012041050340c9071107000c112100f9440b00780e01c03450286080c01e00c58204200c210303c20718022800f00150b940740d00340542401d4285005011440034401400213100b036030080b5196500160001640c0d00c1d01c035002401d002820001640c01da5400070303504400700030034041294004002e0034107164440440d103a24003521525522000300594800100d14240e02c500b80c0e0000522440003180c1e040d11000c0c80c12010300040e40b04030344c4250300d0000d504040010300c20300d003412550014264a4943e0340da0b21801020350103007c0760342e0300c513030f08000c0c10185140306409940130b03280910700c40794640c1a0103203041c5000300160004d0705004a03040c0e00d48410360f002d100c5048000082c03030003040c5502c40c00c00315403401030403404510680c015001c02060504800c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 901732455 1250 901731205 901731211
    0xa12030e331c1e11090a090e160e19090308060103090201090302060a110c0f060a080403020705040504140d030b06090f031c020102030609010b0408152a03010614210405030705030c06 80
    0x3c1010000040074075807108851007190000307078121445684c01c02038081d4a0748030040c44c440e400700340c48070004c107882003546a280c0358103c078501130a00700031f000d50201070082031f51345e12a00490800040032640c40107042c0c124003d212604064590701c2c800e0869115800f40c00c001d540c0608240c1e222720701e00d9000b40c03202c86072122020701d0303100c4c490300e6102d03501d040c0c8562403680001a000525180c3c1000044074a0721000b4401d40551240c0000000c45c2d0b180d910a02c1d210b03034011464549070040607004d050030308002c0b441d140201410910901515034902080f01c0c004a801c03510304d1030001c5e299012070b06100c0c00c0c1100310084410003804c4074800d030701074005521a01302150f0098245c0e0b01c440003010b00380924022462580d210b140e142c030003000c1250b03c854102c217480901a070b80340c000d211b520100081401c0e45401c0756002200410205400c400f14150b2500c5200e001c508028154110380d9400300385a1100034030000601c0400c00b445414811911141c0c4c10400303481d581c02141c45001d07681c050903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 901733705 1250 901732455 901732511
    0x31603030806032a0d05120d02040303030608010c120b0102011410090b10020706051b0a050d02010b0f181810060e01060c03080708060a12030e331c 65
    0x180041260300d11140e070300c4134100680031414020500501840050403000307004582c43c0c492800042c3ea030a62120143c1070a0072610030150740c82c1c0c254900102540c000f9030040083c0d07814150090182a00250a584014115040010800c0700c07480101c0c09410301c6a0706480100e6001d0921465a29442021040d100100c5080c04140300140031b00000c120480d01078001a0407200d03051015038070800c0240140c00140803100121b2840780082c07801d04602184c221295442a414280003d80a00452815403011508550041c01110101d00c803d000356034804170459402c40010510302c2402d2230905c949070b4220445840780211401d0b000107040d5401010510f55850000081d010301c0f4500b02004181e150381c944050380c95102051380e803d10007a001e0703035105051140116507240c034401400c02c554000c2d03030b604007820144010701c65000350440d2841c0498039244648041d9190458600500300c0c04429000d550304070502d03004a24120a075501c1c80000c2c141b007824074080644201c010707400100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 901734955 1250 901733705 901733713
    0x9330e040c11011802150a1e12140c09060f040f0e0406060936050d020709050109060b030402010c03030b1518191a0d0509030c0f060c071103160303080603 68
    0x14004e180c45105100c64000790302482111601c0040c80c10f180291002c6203c6080075040c02c020103076050f0240c465228103100107000101a44c00e4076066010708040000301031628092805c0104002c4802d20400381d10328040d5400240d880402c2c00014119001886002e04a800d0300303484407001d16500c1c1d0181c405840c0c01d420301c01c000ca00010184203218004c0031301c10440e503142c249140041d01880c070102200b003906080b000c0b50000f00e0001e02243c003144040d42c1c060319280303061542c48000c990781a002000700e00c0c5084401e10400b0200fa040701e4100340c09080c27240800403d403034110302400c05242125044100d01c03480e490341c0b000e0768000e0b04c0300034601924007100701560320501c65803600002009246a052600401104074002d4895001388906a000c038904422420799009031230f01a1207a421aa0000513190300c04901400709400104100015150a0900ca0442e912900441c14050030281801074548150b039400c100c1840c0906120520300c21050b5070f030401416101d402c071411802805 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 901736205 1250 901734955 901734971
    0x30f0f09050307061e080c090d0503072a0821090607060903091d09060601080712150f050d05032208060906180703030c120c020a1509330e040c1101 65
    0x805006d00c00d00c41c1a003200203c1c1172452030800c000564502c0740703050307559020410408003c6845501000226880000381702549040b01c2440c00254100384c3c4900065041362031003001400c5a811400c0c61008201e1078913445000600000780b451084150003000f40f883c0509443c101500109504100d50460300210b17003840888900b01d43d1442c045828000e2034004200240103503000705041d40c0c2002441c68414205551000c400046411644038540309510140c42000010700841080340900340655201481e044142c0d5040d40c0c9004802c00e046200c4450511005440c064141e071360002e005038001c507451801c1140e20300381c50f10000e03074a060310300c4ca143e14801e000310b00001d8040c0860780d06a88240405080d6110791395840c1900d10002c00b005000b00d003140240e134829a141c0050000301c170001d58903001240001d8000340055200010903140b01c030043da1081b206e010480070b800c0b002d80044c00c407944820744c2240d0301403161107060f0348145801caa0304000c40d130149070b265402e0300d0b1400820402d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 901737455 1250 901736205 901736207
    0xd0c030f03270302120d0618111b031e090118080a150e03041508070905370801090507081506010507050f0703080c0d0c030f0f09050307061e 62
    0x9828000c5824030303407290000c00c6079401e222401400d0403d0080c07040d40d180c4c41c070104403d80b95503c8a030080c01c0c01070f105c6605001000c81c11040820449840070200404584480c00c803176240180400072071a034001260381c045240301031046030002c884001040340700e03440041c8480b403244c100c40522070005640151104c08940c50155080c16209444028507035003c81c5d44d540c1d801c0744c1c8021212060356032103050074150040d04002400160414292501c01d280005a0003050180000c110074100600220308014907241d108000c2d031512212150702042c00c00320a8103003102c551521000603000701078a0300141c50201907020f1543d252042c0261a5020750f9a00d10329910b5607148d40b4141c00128140100f142507003e80014440c1c10310402c29140c4072064010740030300740500b50b44140c954500004440000e04401e00001c1488401c42c10f00c2c1490030080d481c020174500d4903840060501020122100741035000d030301c43d00c005020003070072604482d0300d4080040c03c01070310012504150b155050361281403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 901738705 1250 901737455 901737461
    0x100c12050907061d0a12032105060f010f030e0d02061e24011205040b190207030e0609031615080c0f07110a030510090b0106031404060207140d0c030f03 67
    0x101e05540c0c0d801600c9001e41001c0c00b00440074958203520100c05c16000a640882c2c0680600c0e8500940b18015001c20b14500440016444a0360040191a1130708000d110b942c0d80540d60038140c1e0a18000b110f4801d0808168014a206a0500c44070b00c40c209070100c925a00050003842a01c0035080c0c200401515034111202d00d009507403134518075000f43c8055000003034031943d4440007541498049a64040741949a0840720103403010b8440559540411050f80366000c041010041c00c2c036021481e00c0d840391401800c05140040141c8134200c0001c410645d0340e0204442c441d00e20101085400d200e640380417100d04401426000d00208003c00700040e60313080c906e400d49000021800c0141e1821402e55506510120310701c0d0b8555005d49a001e0200205e48100964007110001200024100159041c201000c140c141e01c040e08050809801071003e00f503070f00605030002ea00100258940a007440c01e0306603140c1041d68008240300300440480d225a01285000c0804d0194803101c4040e41030040071019 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 901739955 1250 901738705 901738709
    0x9050d050c0409020a0518070e060c03030f04060f1d1002040e0103241409210d0902041d16120f0b07020c03030d020d0e06010608010b0c100c12050907 66
    0x2907030700440390711042400c090300811000c500c002e120152039501c40000034a4171641c0005600d50b03042c4802000140e580010142003101c2c1c04403005070800038a00b2010703603244001071480c05003920900104040081d540c01003030100304040741c240809102d000780e80350444220581c0c1c03510761160580c0c5076240310703082c42190155440014510256800e5440301038205004141d041c0c500e00e00c2c1e408000c1c24213510311688418070b04002c076421031414010b42052030308054100d00402c10f07131901c115004070440e0604031400f508030b610300450703121000c2c000100280349014400d25401302c0e502c00800040008500c1c680c0c3d8244a401035520702c0e031940400190715100c55001810042e62441c4180821501d25000d907118003144120343c1d501450740c010038203503040906540356803900881d0003940080d035409003000e00454040102042d41c5040001481000184030380118000d0009550841e08828081d074019410341c500244441039085c00020614000681820101e6103040045400c981c404207000302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 901741205 1250 901739955 901739963
    0xc0c13060f170c0607140c010201060e16050f0c010506120105060105121504061e09110702010c03090f121101080601020c100e1815030307080f0906040b0d050709050d 73
    0x1452410b00400410031126800c00d0107062060844001d556520300c001400d03c03921444c84001120300c110b1181f480c01e1064040075066905000d81840101c03826000e01d0340c44528803071416401070b20304000f503c041c8900741c2068030704100083c5660161005401c8940954416a0900d62011078142010701725101502c80b1400a1000c0100c401d6036091098a1600f0929954103c40f110031004001000c45201d54000c0e00611b0303440b0300e030050300854800100f00030840c010b000e0000308a0809a10001d1003005002030601003406020b0003890301c03075881c20010305262409a01c180d91901c4c441955003071910030403580030b50380c0107c01d101944180d910340c0c01818107800820300c0050010130440c4207840c030600c041c10802404000b00c2e05640381c0b11100e2401000e04a040340c01c1c100491500c51945641c03407141d01941c404c100711000500c556084030a034000030101e964a4a10b840d0029401d4841d0b0350245030b28150128000b038990b8a50303401030340610816214681140d544200707000b10700b00500e101078 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 901742455 1250 901741205 901741229
    0x80708070806010b0708091e04090609120c1a130b0c03151e010305090c0d03050d0b030a0b0705031f080d0e01030506130b0f1f0e0a05100f020c060c0c1306 68
    0x101f00d81004000e18041a050242110902c0b8a00c0040b0701103940340142030340c900d500ca5403502d05116645a401c00d4604083c645070700701c1051521502070700c0300c0700c0421103c0310b52210001030700c1d90754a14040d0800b40e4051601842410120810051a00140c40003011000001098000340c41c088a00f40107496040d07089007081000310006400400c80101003840500401800c1001350b6a800142d401c85c81c800d40707800340c54010030240b10341120580540781c0d000f82e2014480c00089861090200d43c09841890542e42c0d0303690701d00504601c80200f800103505180d000c040458000004182c02e61003c81d01c0da0b80e000000841d800450540300d095800760341000b400c000b0b4a400c8444d68111700b01e0490081c0c8440c0c201382d50070b400b080c0c18100381c1010201d00070000d074103214810f41c8543c1b40018078134115502403407182480000780f003450307503680c00c2c2c028846c20100c1c0b40c42c0d0a00a00c00b1104290005003200e8131107200c0f4241c5520b038020380c150103200c0c1d020030b10329030342095180c4104425501145150 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 901743705 1250 901742455 901742467
    0x7060e09160305090715051216081f0e040807050609011406040b0d0f080c070b0406120c03150b0a1215090c1404030503040e0c03090d0e0a080708070806010b0708 71
    0xc0e0024a40a4600786544c0607000001c03550341b42d00e10703260009616558926a071130701c564810300060103000d001d030016140c1c0707000000c1d0015800501ca07600301c41c00001c58581d20802440c1c031364032401c4030352190070a007100710204001e01000300c01800c0c0c01c5002e00142d0b41590786000709103089540c580b500030ba07441d0105011903814202540322000359003024040320860449a11804c080d20191081242c4174000001c05811019040c800c01c3c008040408030181020705182001d04403509010030700c913201ea07548100140180c0b083c3c0084810098500c80c00c0542600c580d140f14140d0b010320740000214407000000003600200d445416404aa1414003951850420759000c02400400c0c45210400c0085800d0380e81c0d14042500502c01035100e0402142d07542d1070162401e00840c030003010400c6964050003000b8104c400030413200043e4090b03142c00e0041c40c44100c0080e8200800d5005100f49110303508022410803000110b00040c0c071041001c50ba01683d0f0344086036442d214002e00113143c1e403c24804 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 901744955 1250 901743705 901743707
    0x3060603061801020c0625021c08042d0311191401020909130203060c07150c090b1201051801080304060f020304170124080705010e0607020406060207060e0916 70
    0x41c00c0c80c0000b1140054034000c0800079451400e0740c2a10b000b10741851042060008041c00066012042c8246c006420301c44e5603030414900c030704004200d01d010301100c1c074001000c0148242200e440d4a0042ca5402d54900001d10900400101d00400300d001c161300f0030300c1d10302c410300004610342c000401d074030302c0e03c60200c041d9220001c40a684100f11050340d001c0c0119410381d44d50303450711881422460000404041c080c0101484d050010b030140b07401c0d407010080e82010500c4650048000400350381c02003001d10001c8400c036052002c580c03264111502c080740c45425034152072485c504840085440820020300424050101002880345004a0344100000c20200c0c4c007400703100c8415909801500c2c2060368450a182c07407a80380203800029070355a90b40d406032002501c18103440382da45c2100070146c0541070511013a40e035101805654140854400d41030900c0d0744050460b44130380d60280040c07010954512000e03544000e2801188082003915129001c1400c0113a9800c0c800c40903440700c40846008000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 901746205 1250 901744955 901744981
    0x1c2c0d121503050303072c190306060902070204060902040b070f060905070b0403210909090f02041104050108070c081b03130b04090f060506030a0c0c0506011d060306060306 76
    0x12010340065114803000d40120350020301c10004501820185940e450f00b2000208403003500705460070340d00840c1e006011064200140030103020070655030151a42c82500540780f504186900082c00c90b4284800401d070343d0b0b415006480301c00d100ba5410310415032100c441105a000c0e90048034031104061007010040703041a00d05034042c0d8024000040d000d00607443c2c3e1800d0101030b41200d80c024000040410070000038072208002510303180811001414102c000074096510f52003200000e076252a0010244544604040801d41d40200b08001e0100380b016040c0c2c07113804c0b07440b030302d40490700b1100068411f80c06505d010b03412581c0689030324070301845803c0607025409a51708a0307025110a00030700c1c180f01c8042d8140000b4020b13502550f074a451a12010074103031a040c00318a084182001403c10442e210041500c0d0072004844011507413100e8018202d40d200007501001d4a01c0c450003000003007948050344035481c5400c101d0484082540d581c0c00341580c0f10416a03c164041c0d11000000f42d8000c0f03501 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 901747455 1250 901746205 901746227
    0x5180c0304080705062403010c0c0605221b0509150913020d060914070812090f060403030e040b04020711040c050f0a0306050901080a0b011503021c2c0d 67
    0x549043d0802c4a6600c0d074a10b458411a00710b10714a40a800c2505002c0e07022000b103129800c120001d00c01c0141c0828010f200c00c40d4000001e1280d6242c102041c0a55403040350500c0d1403002803005000710740716003000f12100c0303107240060f0300400c0c4000000c6001e04191052511922001000e40410300c2d582c02842145030008003104550f440082100006076a030350a81102a4081c0901240b0b10401e07051500300c0103822500e040c0140e020540030041400085441c080c0039100742a51901c44c0e000d600851702d221202100c0650042000601208040d00518110003049082e20200722080b0f41c80d0500003244213841000c0e114140c1c02c840c0401a1078140c000540f120000d1a09508003848520b00c038565400543c031a5000c00d8680800380f18904001640500400d012801091184001d4032107401410060003a034011840d100d51240204e8041d4040301c02c40d00240c0c0c44050b15280001c401c80c0106503120b0040b103109140007004600703c43e0308200e07000114a900141049003540041510104110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 901748705 1250 901747455 901747463
    0x10b070318030b012634080a05100f05010f030b10031401140c032a0909010306060e070f09060f0c020307031101171302010c061e06060905180c0304 65
    0x220404400a029640f10794000c0010a072242e40d44c9541389174005006009a240200340d9025031a1380d20071500c065000c09980c00c00346980c00003407500c100c840404800941121081c2e10403941c498081090000f4801080201c1c0e0070100503c40305e000041e0309030b507000c0c07040c0781c181c2c4040c400610209280c011916000325010000b550702560f00d0740e40d06910a403a2003d030314580d54620402030b504a202000340d0348029405061851881d080540c1480e000c81d841c8111440310030942010405e404c81011102a040010040c030955a560b24100018221602901154095440c0070a55090003016038440ca040c040c2c6580c181181400e00485041e618207801108019510b940c62000d030310300340f0260020b18041c14000e11001c00b400005040340c1d00c2140c0e40440c081d074103010003298041d2081d02c510312550900e0004158402410405d0140c1817060010311001a4040e81421039101c5a108501f250070070b881d4410115500c0c0100243ca031200010104203400701c100040d405c21407074008691007441 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 901749955 1250 901748705 901748747
    0xa08030109050901200d150e15060403080706150e0402010f0822120f05071a04020d080c010507121a0d03050c06040f0606050a03020f0f03010209031207020406060206010b0703 77
    0x5c4101c001c205103084901c002500d5000100074400a08030300801c0d00e1604400c0103041ca092900400d881c3d4080b0040c000c0310902644d210190483e51030004a50041d500f107030003261075214500700440101f03017034841a051140d807884009003100340c05001c00d201c1c3e6016120b6908203068070b00300b614a084020a00a07000701907130044000e0900940001d0303241c5010320b00c080210030018201034a00f9200307507500d01c207000341808104c0005050803241500d203546030107010015162072000c5500c40700c1e00c44006200c11804124048150310540c81395101e43c9181e036034821500368020301141200c031254a03201540d01124403c8485080441020202c90301c00e16041d450210b540914604041081d81c0c101c50b0710200e0000c090501829004600c060300040710780341a218a10f80c00940c82c1c001c0c40c40c4503130045045040e41085035402b9416502128800fa0680e030405d60102d00301b002c1c41c1d0014500301e109500c1c1c80c1000c50400e1001407060305850090071064074040154909550710244440d07586c10080d8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 901751205 1250 901749955 901749971
    0x10c11030c030d09090e07180e1005040f060f0b011d030f0703050d080901020a081303090e0702010609050f06010212130b04060c03031b02030d02131a13080a08030109050901 76
    0x604003e034502031030090f80e980751402d0030300d8507050554103503241c0b0a1040d03006070b20600ca0500796480c010000710f59100001112905840c1c1c03142041030045151400b2440c040801003800846405410741510859007040301c00e81c441d41050454244000b800d0005140c44036040c00c0c005626107035098200010101d81340f85800000d907600c0c008080d003088400780c004c2c2403515200d90300014081d800080500080d803d04440c4080103001c10340090503510240c40480c1c10005040c01001ca44024008035500101395151644020707020700400d10400501c50b2070040012502d24252421a00034401640035125141c07610412445940043e8504140a5041c020000c0c0c1e410138100140000d044946440128690a00b0301400b04e840d801c0b9000f10310513003003920f040d030f2b00d13404000c03a00900003d60005803100101c08110002441d507812007600a0080c0b6a00500a10b41e1000b80c0b41c04042c1c1c3d03806e45038451312132101c262180c20b00c000041c800c0c0d50900050000e0501c58104035802030300d00000141c504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 901752455 1250 901751205 901751209
    0x10207060207021f02030d0b040e010e07080c0103050c040311010521010f0e04150e031605074e05060403090e07050c19020604030b15130902010c11030c 67
    0x1910051049030469400104003045040201114410740002d03000e110700840d6541e0041c1d240d200f0003070740c007c0031350b601c2d07100c00c286540e0b52780103100d120b5070380c4000c102070441d014038503a46013042e02602c2100d22681d04910510340c4280a0380e0b20503140c031800c080c1424031319510702030031182400d90241070040030711002c504034aa81c00f4020a8450310fa0441c0c2d0341c1d51400321040044805078200103502041001041f01040007186030901c280b40803e00059030117011240c0900314010802d2007600d00505400b50000c1c0310307002604c230003038070003480045200408a007240703410005840c803c400403501c06140d440c0c000160030900f41d84603000e0081080e1940d0030703940e144e00b4054116003c8020a0400b0b03000e0010310050540350b98401c01e03d09003603181101101c000c907907034850800820750300400102500c1c2192a40f105031130096603c4082000d80d420311400e02c0c0303004000b8001c2c4500500621846080d2100140103aa61560701a111040c009030951144000024203d076941d8251207512205100c0b5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 901753705 1250 901752455 901752457
    0x22809180b2e11030d02041d152d060703030507031a150c0a230c0105040509040b04110a180e0111031315020313030806040c0e0d020604080102 63
    0x11440c5000003081c003401000c00ca0012410b4201040140300c620741180d2024065a1078155080d90781411050548060341940c95403003102d800100c2140041740000300d8600c13118680c01c0030a40c4400c804882d0391600200001d81a40c1c246281c1d00c42040111403d486800003c0c226515010042e906600200784010440540c850002140000e60700e100300420b01c0d5043c441c0000384400d039000d602107400324600040000080d0381a64030a01c0000800f800d100c0010004a103905602180700343d102d44001d220b070f13400289050500c44860080d10030303482c040e600c00c030308441c00d444004051b80410344440e241c407040000014012a0b03200081c1090782025906c440000c0c00600c504880d860521008065500036500d4031014080345a040c8160250043e41900642e1751000c00e801130394682452508050091031218428400601d10000900c0501c1c01074100c8114018000e4684010303503110034041c031003160001e296400000700441c14445440c034000083c006814001441c05007030640741c100c044d0072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 901754955 1250 901753705 901753739
    0x1213080307080a120506030d0f1e0f090e0103050d050708160c0918080706090f14030d0516020601030602220b040816060e0105030604090b04060e070801022809 70
    0x10010951603581d0361300c0600c0c1005800c0008040c403a074149030f00441c0c0e5810113005060144034110504208080c401c1c0d0700c5e09040344c9076025450603e030590700301400c0c4216026a02c0f000485c08440460b840200030580380c103ca0707204009000003d000d040440b00b0303170800c400807101d50b14108a10384002c1000790001035414003426683c1c52452518114504840d400c55901d9040c941c9400a100072980e0758098540442c0c10400114541c00c00d481c01d035a41e020015001081b420070010f2510700c1355400009404408642c3d84100610b403102ea68500040303402c1000e070030046e84884014400518035801a06d811074002840e603024100c0104044c9260341507410642601101150400410b10100a4260070b18143e0041d5000a81440c90041c500c0300070b9041141130000000c081005078031a42d0144464030740100340f203e61420240f070604080c20550200e2031503032040c4a03020980750030620854ad0020a10390705088a4461190500d59000300c1c00f00080030b104509100140c4407521a0619139 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 901756205 1250 901754955 901754963
    0x30a030206010e07020a02010c08160f0501140709080a0201110106092901140d09020307091b09090513030309080408030304080c060108070b07080306031e07050a08030c1213080307 79
    0x241943c10400090324000e0b00818400c1150301004041d40580d80190804400d203400403232080d0b0300e8100c000171030701440c030780310008083c10349440c100b5081c424190300c000340300c0403080541c2030700b6281e250044902103150f0048043d81d1b08100c80c00001513009209000d599a92a1700101e01c542d03a8a51900407a007250310000a914400c0b110303015101e0310502501a412800d0810640d8640e508401410074002c3c90030940fa4565a9042e0200313640d01004044000d204460080c000f601c00d840000b00300c1038102a400020030300510011039134a038280181e42c0305001d8020003c105c00c09a450032000b0f00411003082d11680030410000c6020304040c402140b1a130300826005d684d500349060100d183c4074050340509407a410008040c803200b0031810445040310781010b00c1d9603d035140c2000090a108080c407517015104403200c130381400054081600804c40c1d204a80c40d001d9503545035041a1240702c0d11200d408244c0200b20741201682085000d0000000d1601580c000c164440d58190f24680c40f80030709407 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 901757455 1250 901756205 901756213
    0x3010f090515060d0c0216142107060903031106060f041503140601030b0703050603030901030f0e0d031e0e1e07121a010512070b0a05070b181207050c011d030a0302 72
    0x1300440c0e01041903810b0300d00c0381007004030490301d06900000694101c1060314400d40b26003040305407081c427201028417108102010b8480f503a683e08070241244440348401c07000309000702e0320b605090002050b040d10030040502200b00c080386501c10040103041c1c000f4840048581c0107008000300c0d00082c40074180c80b0403d07004102650442c10010355260006041d0810907090104002c0c01ea1030108c1070750410071080c00c1c040b4510807829010700c05048006d810203914401c030a0341c040103540c580c21a41c514599032035500e10070402a1b43c5007080c0d805c40b92182c051641712496901d028880d85082d60f007903003e4202506c09039902c5015003420146250741c15612410f0f041d4041d00b40d04c4207080c006005000031954540c030400907488440c1c4408103480f84080b0b102e00821141a45800740c002c881416600c5040001d2520b407c0030003480d5180411010b82881c45403140c0c58507595240390071510503e030040010b2480810b520011500d40704074081c48903e0f4440c030083d0040d282c80070070031003010a110790090 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 901758705 1250 901757455 901757471
    0x1031e1d0a061a0303030403020705060f040825230f0402040b0406050c160e13140703080c100603031b210f08101d0c090a15120203010f090515060d 65
    0x180150f0b021007000c19110750010014080060380004260080b6402601c41d280c5912402208a44500840e8803040c0c8500030614565a4071074800103442c00b01d4200c44c003d5003050f88420000e038011040742c01303031001d06441120701c41035858007000450000304001c0015280580700c00c03143c460782e0400e030302501c0414004201598141014001d4003007410407100c0441e411407401b4040e040042c009000c0a0700314019000321414016000044000000d0b0301c800c58090796541d20307194440781c1c0900c0b41499103006048500144542c18060001141d170103955202401107050b489084000c80f00d50111280c0c0050b00044d03507059920040e0800030101c5484140b6984841e907406810200000c010381da5040000c10300707006a400c02904041d01380302134852002d0301d986a04482455100b500303903050307100501e400001100a0351514032031109140da80c903400c5440ca40c043c005d0590000f800b90744c2180d0300c896824040013810f9400036511081082d502114101d00c0404030716240d00c2071140b111010b4031550f00d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 901759955 1250 901758705 901758731
    0x1802091801140d080a0534020111070806190b03100219030519020d141008120a0504270f05010801060b030412080c040f0b0d0b01031e1d0a06 62
    0x2c0c455092030a6405003c0d010a035583e00820340b0030f44451000380b100208084c90812001c2c0350801e00003803062984802011001c2400c40d60f0100c22408078000744d0700e001c020908040100d0040102c40c2044000c1800e619090301d6103200c8440780c50718a800e2070741d5501c605a01d5400308582403051450010061b61040c070707503510306900c001640450080c541024144601403080d680c0258040040c4040182c940b03181c010342d54050b007100e00d1880c0f601a02c2c0e00c24410300210011070380040307400042c110341c0485100300745c090103070103600107007008608184001c026410000f0001c0d010183d001020300b00f40c061503040f401c02c550081e0a40d501c069543c0d40180241c0340e092003118090402205401e0543c03402d95100c442d40705411100303008100c40c00380855610103030141070783c001d04804240c031701151751501d00c070b00d22542010b4100380655007480c0404055500070300c0f4000003c0c010f0641610012007401900b00a812401c00c602550007a2041420400c01c1c1800b036880564442c00000c00d0301c00040c01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 901761205 1250 901759955 901759979
    0x40510060b0a0e1020030906040e0601082505130b0a0306030201180b030a0b0103020403121101110a08040308070519020303091e030a1d0d061d070b041802091801 71
    0x1201c0d0b00624414070384c00241600000905040e01c410a0b81007840214124801c0c00c0d40a849074a6800c034001040c00b180054204030030720702c102d6003030365908a280d13070704008110750120240c41900e05200e11510b103d0141d2088004244400341c40d40c0c06d204655035904124950f600c0f001e00300c80000c2d5151014011581d01c462401004034103c0c1450000c2070514450700380c1484003034400d082c1c1e6540d941c4d25a03030304e0b4041e0301601d005503040413101800d2032071654054112040740910816039440d19007141c2c0102142400d8a240e88400d94881c0b42c0c5540355074081d03860b504054583c10a0000510560404482900c4040c00d0210130f035003d5510307810115201460110a140d8001e05e40e1600c031007200c405003000040c7c48c0300068600d4020380f420181100c003444000604160340d00300001c0b049030020f1160300d4005891030009080980290501c0b0104181c032401c10340182c050f0f4560410081240760b144221824801c55402401440c000d00c1c540055800c002500b4845282c8902000400200c55802c0d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 901762455 1250 901761205 901761227
    0x507020103021306180623130509010609030c06020a03082208030115200d080703060f032f01080106110f010c0206010e01080a0305030c0304110409140d020102120708040510060b0a 79
    0xb0814041f420040c48440c03401500d410495074500b9004500f403109585c0e00781c100c1c0001c02c4003400e0101d041d6110440184024032500080c2e0340001e0070310002545502c001007041d0b0540d0983d0b158074507500d03120706000e20522044411040d00f0304050590b40401c2d0030200441c020061050300c03507144a01a940a0525800b01291507601e40c1355190180308068049a00381901c1040e19084885640c2c0e071905600902c0300340c0040c02c0c007201c100381c040200120340c190120b012407203845040960b8441ca0f086440040c00d9140315000469070740041113012b004032150140c0000d171a054420030904140e01500310b0700c8106003d801a03021074010481e243d10b001d1020b02500000000d052a4801078a010788075100191920700d00250010006050100a240286251070f00900038032040030a400c7c904d104c08000300c10f08405006500300740d40118014400c0b1a0b10701d621020389122541d6400060f0f1741080d006000380d0b2140901e1071220250b8100b0300c1010003800c0314800b20f60700e5845107200100480088 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 901763705 1250 901762455 901762457
    0x1050108010c0e0a050a0e04210f030f2d0e150403031b17060a0902070605010e06060705070b07050a050312010f0e09060a3201090b030115030305070201030213061806 73
    0x40d60140042c0d03d9080940064070319504110009403504d25050503448600c40da51a0a10070268020245560200b04044ac1d00070940e002d100d00c0307041d41190750440321261300c809070012030380540442d1950409146400154541da0014000b0f01035000b503410704101d0641518001558000c1000b016010b01c02d0107405107402c40c24034803051420b400a002d4841c0c3d51182007901c5904000202165240c02240014014050f419500c42c0120720b04080903000a00139481042480000901b0b45d0402e407080c2c0d42c82e2600704000300a22031a1190383c403e5035205d003409032518042d0044030004140100018218880c1035004101198074010721003807001c405400c401c043d03236a90003d0100340400010400d070030102c1800c00107000d41002e0352034425508240d8403010181c545252074140780340d0b601c507043d04071014588180a408980340425080f20460203855219000f549001d0010034030450140c0029403042c100107190611162136100d110f0a01d600420000c1c0e24402d0b0400e0200014075458024511 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 901764955 1250 901763705 901763719
    0x180b1302030405060c070c150809100e0309010c02060409020c0d020c0d2003070305011a0910120b150d06050103020310140c2803020c070b09060f0d0e01050108010c0e 73
    0x1a50f02c803500c41101520b9680003005c0803810109000e84e40056400070094144801f80b80e240710394001d440d5000440d0206058000c600c84503005000c07500032600b40c00e18100c040c40c50130030b00c1d20054401c4100d21005980040d0140404540020148014076202a60000400020017000740003440d001c180d0380024081e02c4088003110016115003035001d401d0741d44216024203c6a144042490301002d40c2c4007412941c2440b1140c1c03032100c50340d10703204050070054541c01c903240d44001d140040c941c1144592401da40801c038540020819010745540c01c222007512000511420b0b03400a41c10540801e01607540503903400042045240c10000503002c4001e0040600030b2208000302003c0c1248018031049600302c000528480c254018000c1c1b44200f1040001380b00c0703448180100800030340142e03c0c801268400c20401050250484043e1030314100c00500c03080c6400c9036255007000542004260980c03031fa071503105a0122490a01419020301b0307003200000b4018050800003400503030110300700c5000b458 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 901766205 1250 901764955 901764961
    0x6030206091507051c02071406181c152406030209061c0b010807110705130e100f060b1213051c09060305150d1b180b130203 55
    0x164039003941c00740308040742c03007105855980504840a1040000c01420703401030b001300904100495541e400e551460341c1c00c4407000768a424118440f003c0c1c011040340d20240622034a0211001c0050b00114640042c183c0d40003a02d1502d400620740428102c1207843c01b05030303645c001e03400000d4070541508611a203112611a004a220401c01d981c0e81d02813a000c1580015070034090351a2142145c0400768a5800c0e020040c50300c01602e00242101d416650005201c4408902e03224481c0c2c2100700c2d0701c92414043c20382c451034281082002e201085010140c0380e201c03480c44000100c103000143d0700c1c2e140064003185024040000000712038490300329a44201041c0301c48042c00c03201d0f55807240c1c45100c0c201248401c0741d20342010b074a000c030103c4190150300390220804000542c8410f450b800c48040d52010f02468039910b41152011070311041c03585d000300c0d10004500104012000014901a20607148040941c854003030101500d1100c1c050b00105481d0303002e00815082c0000c0058405141500460940c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 901767455 1250 901766205 901766209
    0xd02030601033e04210219030f060c020f06160e0a0b030907082e0605090c0703020d080609221502090f040501030503041a041d09060a0b0609041d030a02010b03060703060302 76
    0x1c20171682000a06182c02d5104045485964001e48100c1c40e1040d204c0016540345404031080184c03d0003100e4039400d240c0d1040c42c0c43d0000981c810700070201c0019100b40e90b51031051800f164030361607100003004101030040046807601d000c101c3c050300840441c9a5030b032414100c02c501d0640154042c46959001c00a100a494140e4410b00100202d901086201c8019908190701401551700310f80d078080302c0e0805010000c040720009103252403007034007551003d0f143c4150036541100101c908940000c5c0700030005612400c0141d40f8003104503600c0320145010a01d44510503150000d5010020065000034005041d1611290340b80c8150300846040c40340351704540d10191603000398400c181040502044020122810000340e501400c0740421401480341e0f400c400c11300004007503a50000a02440000c81c13a4609680504404818003803c2d09282022520600008081a083e408031280f0f2070346541c4c1e0101028801003100428583c000304e042c9600504240c00c0c028013a044c141070500d0000100016 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 901768705 1250 901767455 901767479
    0x7020f0904030f0509010c02040e06040b07091520010501061d0306011a03060a090509060f0901020909160504080a050a050708060708011203090b0a0305091c050d02030601033e04 78
    0x83d1054642503842d516800d00581c2c007104007403402076000c0c0c28501d5400203070900107003c9200c0e900400c0d0310b40d519101c0302019620201c4c1c50283c031200c0b440c1741043c0598580a60424908000c043c1c003608080440c1030102e500710340e070a8029400003071220f00d02c0441d840440078113141c48a01100946090f52400031101458490012810010b80300031001840586d1840c6814000342008a01842146402030390340c3d4030792100325044080f40300c258011400c105014800e030780314035030080d00042240e219048007040342c21144802c0c00410108110116411505220706c00d05140b04a0060045005601e0928107254440d00005410f83c024002c02002035444180c090464075158982c1d0075840c03c42c02d044603103000c940c21a0a191070009014103441c0d600d580301c41d02c105070072010740391603843c40070182c501000350720030043c00903109106c0710034409020341c0190b03044001414000752100d080b4010903540600d01d803100048020101755484140142840004020100fa0b20546010300302000c818070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 901769955 1250 901768705 901768727
    0xf1c06090b1c1e1103010c0509060904050c043201030506101101020f03011202100302090f0f0f2d0301090218070e1c021c0f0816060c0507020f090403 66
    0x7454040c4001003d00c480b44a1801d0100184420b80b580f514490a01c144030002c207101403402503281003108050b503031182041d6000340c5001401246462800c00810018120140040c041c40304100000104140c03980604158620062520903c0404003940400810300840c2041d05160a1200704003555a4448005691400c41c3c00d1950310908481400390081c01144001e00e015600000042811548400311503210741c4211401d895580d0568070032020380c0251040c21b42c1081d800d1a0012040c07508618402001c83c01515840007041d1060000740091410901100301c070040c2ca000710040d500c40d061525030320b24290028008a2010381c0400d00c2c0100360b0040729400e141c1880445c00c254459900e000940a00030022450440c1e240341007000c000b800e10049100754201c00e000c010003442d01c41c221002c0c0345c1003130061100000b1b90b2504031107a03000b0610120030b0500d07240392600098540c030030080c018440d9a213090300c84949205100c5603610324501c03148148188402c200002c0d1b4000d1040702 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 901771205 1250 901769955 901769989
    0x605090609040602090d0b06120714120a080706051f0308070b07050d0903020d11071a0c03040e010609030b07020a020d020621040b041b08031e0f1c06090b 68
    0xda42d850f0705140d0028050021103950011150015070103224545c01d01c80c1c01508211070344800c00d200440f13a690b413080d00344100d0210340e0f00c60010f222103103410f1074001c0403151f0f0f21080c0c600404c09503880b0203c40d4090b0404803596075072101486880c0d105140f40c1810340c000c2111164000b421519040c1960089030f100414105500c00010400d40c407540913a98420301d0620b0034030000b409864042d44402c0002044000600d00c90121101c1038400034841003200c200a0f0900c508407680e486500890b0300111212940d8031007081700081080c10010403900804480d501c2c100841e040d031801005008024148604541c02032104902503564181c61142c490740c104d412036951180b40440c0305240040c1440d1241ca480c41004110610500d400f030f0f03030704c5944180c0c0500318400348100040c0c1d108080e4012440c85520901824500c540f002a203c541941c28035003140c20403207912503a0310140d100a410841000c060501252103800c28080e940140140d0402404020400c201181088403805023040e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 901772455 1250 901771205 901771219
    0x150524090103020904020a0e1201090f020f0301150e010305010c08070503310f0b09060c070602030a1506050901030b06271201021303050706080601080c0a091e031506050906 76
    0x4650303030b01982c1101c0a07482c010740155141d80701544090034140c1c241000d1400390707034581481c3e4040001032250340d196030303404803052110884030340a01c14001c80608810f80c166607181e0810540c05000e1980100500ca08400203580d90b05514140342912010302d4840180001c510030b2021068100c0c058135403240781281e80352040c0512002a660910811800984170700140060009000c80711585500203070082403c0011521903121a550b11103080b194000b8a00060003000700144103500155040805100007007400505504200450319130b55102501280d800191720380b455800d40100d81c00c10b10708413a520704006921015100c51090408a040410585041792216685118120181c0e6140e90021502c40d00503082040c5506c0c0580003c0c0c03400e118020000540394440d0003d140b203590181e41d05d9041e5280c01402c003000390032071603105091142180d00440c40d1a40303103080141d80032070382d039600c60801e01e1401c050714801c0c0c0ea0a0115405800c3c08400c0c00603440b200c186982001054400e0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 901773705 1250 901772455 901772467
    0x712090309060e0a09020408072c071422082b0c060906060626011505031e1617060d0b0924040b060108151905060c01150524 55
    0xd80c0859240c02c45c817616440400e0101c0c0340e420000e400300035592102010340307100381505da8501c2688640c240100c040d80f411800242d81d135104070004907140d0341d10001682002104a60a070b400b401107010040c440700070b01e20401091074108824003490b842c010007181003a403410288192003500c2c508001c1031001a0802600300001984488841c0390030030300c1080038686a0100400200c48596824050040000001e4100320003080050413034124401e0940c000025440c1070300e00760030042042030000014000121141e50304005141302c0c1c0751090810001c0204c0d104058800d03201300701003000789a056020020300e500d4691a002c1c4142d0481868001d03940c0706c00580d40f0b401c2110700300002955401d9545030b032480c0d0340304451780036a02c40e03120012207944100044518640450f20314510900a071021310032414007a115141c104445081248025250b4021030055440002c0c03051050390344511f84140d4200c00c20f1000b015042c1142c051aa00381c8054400361843c00b03440c140c4820000000705 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 901774955 1250 901773705 901773709
    0x7120b0306010302061303050102040f140a060926010534082403101a010305040803060906060405040e0303100b0a1e05070c0e0603011104290706050f0712090309060e 73
    0x2900055234003171b009540d04c03601d9450795481d00c001403180e00d038800c3c08a6159662842e182c1c20810540b0203d5503030300c640c1031420490740e1040c1c00b1144011030004011200122904007030082c00d2140c0d005035882c83c3e607443c521009821900c03422801103c240759a80910071402d40c000c0c00c0d01d400c809081c1d42040303a00301c01040f90943e4030807070807405d50511800d00c1181ca403d4541c1c10007595018518070b10b40c613070200b01006400f40c6030200e4009099800800c00110245004002d264105901030000c501b00f9031980085411a0528403842c1a15440070042240c41a030104400c40502828007105061028104018140100740d0124005c030b0380003000310066051151080d120401d81211080310700542d0b40e0310f00d000c0c104044d43d816001cbc3d400c0c155007840141c4071904a808480008000b802e1030340044014202e00c0c0d41000e910900c0b14001c11205c0b010502501030a4081c1407090341c050300074109202c000d81002400e00da0540c0039400d03d0303541c801090700308080710304035905402d15004041481c00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 901776205 1250 901774955 901774987
    0x9090304140301020c0106080f0609070e040807050c1507060e0a11010c030c02061207030e010501080c0d1a04082d03220f030905150705030405041814010507120b030601030206 77
    0x1c01c405441d0300c3d1540000309408001000c480240401d02a18054bc440301c40d500c0d101c2c0340342d0040c02c80c055005130100700010020001805810700030007e403000700d51020300141002c180001219540000421088144007852065045206120005080e010f0307080c0d4400080710352152829041c880041070160905000b84042103001c0d9000300000d540329101226141f034102c0c21741e4114006072030702190460140051080f00d040c0c3c0e00307003030007800d944000404020000036030b144112841014840d1182588050b819020b0140c0c1c0700320714a40c0c44101d80180404445010380070920181503980e200b411102e000b034103c07a049940d004e03032803030100386864518404042d030302c0008061080303d041000c103040d400240306083c1c81b42103403a8003510041074829481805080c10107050380c2c00401007085149042e501072004001194000c0b4400c860944070680160707103480d41d49450341d46034001c0001155010a601070068540c0104103c96070084022a5441c5414000240103c0000400000c0501140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 901777455 1250 901776205 901776217
    0x90f09070807150f110c1201020f030c071101080421090308070b060306090a0b010b0a0309140a020a0f15030506010201150815092b1e050304110909030414030102 71
    0x100300c2c0d00496036140380050805090440000154140c0c00a04a951150b504503040241400007040038007515001c01450030307a10b08400c04a99401c11288600c0000341004c0d602c2610646405500d03040a0f04103610901541510181000703101010480080c0f8505400300d00025a41c45d040b883e00075041060301c1d01c100c03e8101400c80e2401184880803c406015620710424003a001d4803080e0300c614010719a92040004002e0006400340c0040c0b0100303281c2740c050304000c0b83c0340c03401007241001c54446095400b0040c010103426001072020034103606010303c10034010100410a03010040c9022040801c00c002441030404040d100c00110300c1e603a04c02d41180c501c0302600c040006d8200e681d14003503541d07140070007071240e0760144550002d101108040780a400103a040015000c0081c43c20050180c4240000d03100e1080c0540e507864500c0800302450841007191850b00c2d80c071f55900703141c1440d184403c6003a400e90300c00c550103002c124100b4004800d031821204015021503120078040e0000380640035007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 901778705 1250 901777455 901777469
    0x302091813020f0f0d2604120b06060f040b16150204050306160801030320030712030506240a1101111c090201080c0a030f0e0304180506090f0907 64
    0x20001c1c41041480aa15441d005208940845003600e03a44107000100c92080d0304035510403407043d02c0f20041400800310b440100310382c42d807107402c00e5000c51030505070390425044500030b106100c400701c040042070190300d500060116400d078100015025074509910441c028400143c801084a0403004841c9034103d03041d690110b122281842e480050784025006446018840c0c458480403800895a03965560035070f85023907840702041c5e030840e1019110f00569820208030b82d03640001403030102c01d0070320150895038850955640400858140101a82c501400d4203204140000c0500d038040448240036000d101003908030f544800b000d10050321102c01803c1102c6080d42016400d5106601141c000c180e840b00103000d516045400a4062003103070200b03540280420906004940c991240d540030700313048019450701245442070f60481209440b0341c902d45101e158004602803107591403003032681c0c440a5070640200250b01e0410700007800d0398000b41824400c941000c02003082400140400d001820031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 901779955 1250 901778705 901778749
    0x2131e06090c0914150a1103030f1014090f150402121e040803130f06090b09121312030e0d050d0315050315060307150c020a09020a0906030209 63
    0x500c0c10840054940c1c110000005504400701142d031303041a8007503150908000d8140041c80c040a2a000d03000d0713105040179414003200e100058100036007000110300c240c400301e40f130800c1ea0405c06521010b4034003507001664440f4011501e204103884000060784c2c05440c00041034403e81781c0500c4014000f0440c2c0300260068000910740700540d6172181103a000710707848108445d02a01240f004944060184ea00601282c0104040340026640800f03030700c0c18078041c840a03112150342e562600102c450400003102c2000040c0708004600b001170050a2007003a00d00800d51a000d8202051600461640600440c10a40c84104010706119002c1c0c4042114050b0210341c800d00e8a040190b99032021100c1c000010341008440c0070f28049540700c00044900113801020040084000704406079001003000750103204510300080c0100c00e4036600064448913483d00d0480c4869801886514185900444042070040110301403281d4072451202c00c6550790325005031903542410025440364241091003000e185 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 901781205 1250 901779955 901779959
    0x50910111615020a02060a050708040b180901091517030904060806102709150203070908010b0a0e060910080601180e0606150f0f0304031e0c02131e06 66
    0x42a140070301540c0032000b0079a4807085100e0104e0b0740c0c00e01250025003080080c801d080b40d80c0c1c0110090701c6121300c2095a542002e84401040c60607400802c296100a10b28800e030009a0a114070b41b1405400e5189051001109c0d9201c0054040c0c1148102d00c040b010103c0034015034442401030324200d50001300140500d9548030005a900c440c01e4581a002c03c0054100140310118041400658000410b54030f1810400c01c61410040a425101b50703031290700e600180d81c11052a1008600c01c4803291a922481c60610f41c0b0b803800c50398008a400d00030805e501d018011000a162002d5006408503011002543c039540d0f80c1043c81d106901ca42124483c8800225002c04540e0031441800402241000300c070080407101685e0382c41c00e581c0d0907004030f440000310000d0b00155000f801c00380c070104a00340c03070001c000c1d800340c2c990340c000c032001d400107a4030341c070621010310310100c0c882c11b419203601d40102110381507000903080a40e000d0200b0711580d0365854010030305d00d80d062070f010b02e103007041003c0081035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 901782455 1250 901781205 901781233
    0x91a10050913110607140f0a020d110402130807081005090a080f0705010905012711060f070b040602121b0405101b0b0711161e03050d09032105091011 66
    0x10a1018464000d010703504c7d161074402c000045003c03901e500148001454402c13038a500da1174032103200182c4e40042d02001850040d130500e003a008001c0440000a101903445c01c0030301402e00404070380d544049802c20701400307034031030740003840e40b00903a080194959900b002c03410700c01980c8110b070401881542000e4043e014003c06611044000440711407900325501100e071855801843c00000030048245209030f80c80c1d0342402e1018101d0060040030461610241e903d91128401c42120100c503001d4000a000c5020320003240031a0304142c40c01441124003c0caa4000001401180100c500902c1c8602041030f80758802c000d00c1203180420b907800d9121020304e041c031140102d8101da00318081141e0031503900c0c0c468000600110541c2245100c44080c0e400c1c10242805003210035644101c5800e00c0c840800824418040d9030820300007622103099039403640c0b5144226810b640c40d0704006225010010104035005000c444c010b00e801c0350380c020301d028030000540344001104513810041c811655255664 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 901783705 1250 901782455 901782473
    0x1905070b04120e010e09070e0a0b221a0415050417060a0524061c02040810060509040209010b0304060e0106060302120604090f0f030210091a10050913110607 69
    0xb2607680380fa03280740d41d4200658150542c0720419030403402c00000a040148180c46c403e0342d041c1c0041080ba05199200a5050f0b00d4116518a90140c2001154619a086032604003801800c0703107250b0840071400004888464002c034400c0c1541080c005a03942d00085c45a0202c0d00600000740d03181038081a02c1307035815a0b80300100c9140038800c3ca08030200306c0188100030f0725078517000c1e5011940b51302c008000511020313802001450b00d00c80101015198190020700281000d8040704d0010804103502e00303c4102614010b90059000d014200b05100143e2142a0028151440c1d0f9501580d69200c1c0e04c7c048000f0004100c108901d035280440115905601d90005c114080703813441d04038070944170700d410441210050b1200928401e08003498200050344440101d048071301038010b0f40c031821030340c81d00c00f0f06540e008041102c58683c031240c1044000308034100190854078400103c0201c03800c140200e43c0b0003001402820409445030040d108104000d000c4207030700c1ca40941900d0701d42003186002024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 901784955 1250 901783705 901783733
    0x60509010b01110c0d1104020c0a0b0a052a09041a01030b04051510020304080f0a150203090a03140409150e0c0f12152101050610051905070b04 63
    0x200d50810a501105622528090f01c94501d0203000d0711901892104020b60402d10300d80845030824000240002c0d07545178800303014660051030190100020514161800e55002800e00303d1007071404003448080c8201c00090720703110010880702c0300703189035076402c80c40940102d0000940c42410000300c150b8001080404501d802c80c280c0381408010f4a20b0304000036508111a261442c1900c0e1035017009a1401050b0440400d40c00d0043d07038503003034035641018240a00c40460346015840302e844081040b03100c40c074482e08030707018000450a5003001003009407500c803408005030410009140c00340192462808903402070509950800c003040340307000204500c070558031500c0100403007000042d2500c00a401180d410b2204d2000d0f0383d152101c1080140072419010388100012200d000c0c200765203803200d9985400044000000380c00320b408490074a070948030010700d01070080f1a0794200010040d006020784e13010b4040d0480a52034441700c0c41046940c0d0242c0700d0042e08580c603440511091203039480d101d00c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 901786205 1250 901784955 901784971
    0x507020405070207080f120909060a0b1303031206140f03010e190c06090501081305072102032a04020706020d110415030501061b05010b04050a020a032304080a0c08070605 75
    0x104c1000180006803514451f90b90001c2060301003006401c689080703010140c0c80301c00202484805902c0f454103c4040d0841e40c44440d50324080d000034003d25410074130405910399503140c01e1151074180103254180c1c00200040c50702941500742c62640e1507070290407a417800c41c10502268803181004920081c8030041c0c9100360b403032100305c440100c1d507148510031201c01d48006071946907071503c0c0d000c00e401c400e80b41d00307101340ea1902880c200480c410005c1041ca43d4403062140241d142c0115a0040600704600400f8110890300003002c040940f0050003103801d5100360413100141c640c8410f0030316202030b105060180a11501e8111a1428181c4401c00381044d0340e1883c3d05032442800c461410fa0440f1000c1c014640814905030600c01c403100c40c5c1205101541c0325100124110b00707000e02040940300241c0300d100c0c0850700442d146400c0b660510a0301420101242c002d0b00c518003007c102d48080c80c0117000038262980c0080c002c4407aa01454100c107071698409410b0390783d5885418a90700411054440b20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 901787455 1250 901786205 901786213
    0xe011a13020408121e1305011116090c05041a210105150a0221040819020d06020a0c050a03211e0f0f060e06030f0318040b01050702040507020708 64
    0x40e40c04200d100380d5081e60072400007402440b01030700c500c444640291030701a0a00000760700d400301144024014041161081d0040c500d0b0342e0908001600550540400f060150302021580301a06c0d40d1282803002c0b28441c003070000c2c03c9610381608075060b02c11900548640c4d0505504503500f542910003c020503100d01d4007195518011a429108000c000c0c8030300f95001088041a00c65040303290002c03c02200e0500489185c2c1e061541240343c124a0302c00d0304440d1400200303007000300700c1b014441058610000d0401c0c80e8101c01d95400503106d2844820090030056001c03e40040182c003481c50301c00d58035084400c0742c50081007484c0041585102c01401352111500c401202001015401030110240c4040d440c801c21003c0c800505000302045456000042e40311004802d40085030f00c0b400024001c084803400740b615088041c1403825130011031080c2117900030410380001da105c60200b4560540102c4000c5043c0d0b0030400101c4003405242e001940c80b91824051000c0d480d00040c0140c1101e18942c160703 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 901788705 1250 901787455 901787479
    0x60108130b060607060c0305010501020d0c0b0c07060e0601030b0405010f0c0e150405190915120f030201090b0a020a0f0809210417070603270305030a0e011a 69
    0x1111801026600040c16800301011800041c85181403142c0c04000604030f00c0c282182078580e1801e643c1e684d050000400c1e0340e0001400156818408a003c0c40e51900f0891035207400756940c04040c48004003940d1200201150810400c130480d000743c0c0100031594214bd81650316802c00030780c3c4517415901144d40e1740c031303002018030080d4440c0510a1070310410744444100b0165032040c41050004103e03003c6c01148108408903942d91016104100400101c090034036840c10300646408a8031891010540b10140320010444028122078402040317034030400000b0200010316059025181140004100e409484204161204254040d100580a6035202e501c001e900040075100c00200350340030110364018a142c4200203402079907085290500340401440c040c1c0d82c601074046a0001e0001c00c4082d08000c80800100d980360141e15180c4d1034101a2103182500c01c0303800c1e00082c3d07002c0c0005060020120019005e560706d68000c1c1000c6500030003c2c4600381d41902c00f070b449003502e01011480b6156814072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 901789955 1250 901788705 901788707
    0xb0f0a11070311100c062f16021e0a121b3c03030504080607091202010c1a01090f06090e0c010804050a0c1d070201020915091503010e0f0601 62
    0xc62001c0300d4000e002d8614250b802e0051200c0c0080c8980584c09010607500310800003101d03481140c0351003644a090080d1041241c1400d025079044c040348040d02d0b6028050030054000c644a401c03403c0b03604031102d40d4403440340301507002d210f0242e012480d440440300400086601911550085640c03207108004c002005014040005c040380703008041505480c02c800e65114445404440703d0746540142502204c0c510314030003001c0150300d41040300041c2002c0f5040121900c1080500d41011540c10011880b60030710003c0000c940e08104040e040010300d0324039406011010040ea00c1107030700168154100d607140d0304244080c02d0800d0800e107070725181c02000030f11100148698410301c40c2e0304000e40040059000116040f0324058816034550160240c1880003442503607850000f02106054003071030802ca010200454800100001e0942e4010840395030940d03101c46058040d40c0e01d0800780354484060201050400070303082107580c0c03500800400450301020b0342c00f00510810080c900341c6590f82c3e500740 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 901791205 1250 901789955 901789963
    0x15040b090f0402040e1623030f1f06081603120201090b01092304030f030b30010209040c050706061e2108030106030914120a0302030903040b0f0a11 65
    0xc103607079049100c034041001403a0130b80003a411401040b040321139072001d800d040c40410001d94000c8124000944038030300aa080850070441c4840205c0c00382020403c58040c05483e1881d02001040d8038245542400300060182d1200014000784411103100c0c80040c992520588103e00042d51811810010150342500c140a1241074541c0541050380c00d0f460000040702521210681209502c3c14161407001d1800310281c0c540b04038081d0f0b0328906080d041c0b00c1d0280440318403c0c04a4003a66000340350f41c80502414041030361880c4020900b114444524009a0090040340f028590042c2401002c0702030a0340311021341031640c003498081012075640c0ca1641e00404103400d4201f910540910108402d030f003140c81940d0b61246903526240440859541d20300717654002d07017006005c25581d4055006002e60050800c10030b00d038140003080310007805a13401c0010301030b46800c1000c040d0008005060f500007071040c1c400503c443c481003503c40d25022140901134110216600c0000c04032030013907540e00b030006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 901792455 1250 901791205 901791211
    0x21010803031b2703010f05040b160f0507120932030a020a0b03070e04020f040603050f090c0f0a0b030f161e1b1a071404140f0a0b0315040b09 62
    0x201ca62441c103c03890024103101050801c0c1c560656813560b050340d80204070b0040600ca51720415a420680c940701c0004108070b00c03001d100310200724840303007035942e2950000100c84005401843c0141813000d030303400c11030b81e0781c00d60b41004d80904941088030350300d4500c0051442c0c4600e0700f007040d0f840c40803011060542e103051507440a9842048098204100c000361001150889403910b400c00894413520042400d0360301101845600036070008007004420340c9841000c1c0c00506005400700703941080c9202c41d40e6050001400c0c3d2245595044c001055a00c044c0003100600c8220390a94880c640401c403408849403c48044500030092064942c40c41e124103034009021100c10030002c0c58007400b14045481e0310401004110918081d41c000010510620387e44400f5201e00c0c03150041c0b0b1502143c000c00b8014803100030000c500c0140001d0241c555015403142240030142c400f5101031400301c1c0000e150360790562003440e080b4000014070001100e4000391207401c0c0c2d0706903000e012007042c880501c84852811 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 901793705 1250 901792455 901792477
    0x150e060a03060518010204060903031b1a090705040f0902030c09040804140d14060a0c05070f02100c14070e010e091c030b030f03130905040201080c21010803031b 71
    0x1804081c40001c10780e9000980041030361205050291500643d142242d0041e0001d01c0420b04400c010010940d2100c034510f5400c200503041131220442c0d5540d601421000b4605a561702d00940020314103160400800d002004024010301c604094800c2e4600180880303031003680a40030f285c4c0814014280903020718003a039800f002c2185002d1900c04e9840000c000000c025070710412040300140410890540070030002c11103000b138080b0741041040907040b60440761140c01804001e01011700171a035154012501c1d99010303a8000241e0640400c112a02030340d41100520150007190407080140740081d0307a0f803c2d2004206404880d0341c0310000c80902d010112600302250740621000302c140c403400c20030301d110010941008100b034000480041c2c100030501c4c1403e011340c9c1c004101d001c859003502840c00005d080e440c90410150600341c000a0800c0c0004111031052807000070805580c4145030541a11031081e0201854030b544c40d180e14030703180c2e40165801c0c201c03c01c00710305101101d08460200d0705440c404e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 901794955 1250 901793705 901793719
    0xa02011709070510050a09061404090b0d020d14010b0628140d0c08010b0c030f0a120504030e1002010e1b03030c0618071715150310150e06 61
    0x11440d903503103048401000480240900000000c044c1c13901030442c00c890180ea1a00c903111102c1170b60080c542c1901d81e000d030b0704101d03500c0c00c181c1050003c48202e90640f0324032100452502e244c44042006000500c00080d00110308507000024801035034810007a5070301c0765009220908240c82003003140e000341d0040758104042140c1000c8541411009460700560b1424040c0031030901081c5c001e01c40d0059005240c403941c0b140b0014035203070f90003010329014105084c4168180700d54400d01564074001c108d0817070491100003410b0040320340250050045042424001c1c000303840c0070300c2d005000120045045000f032201140c0289001d006000d019861036403030f0014900304280c204030022010034582c41c59051300007049151100f03582408080d20803c0441204460200741024880c9041c1d0035030b000d2010280c107140d030080c1114001c204180c01c20203c106004058075603c03d044071109162141681c10301c070f0780300e40c025024116040ba4010501580305144219601c24610a104c0401c90b07000d40d000c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 901796205 1250 901794955 901794977
    0x60f031a0c030106120c11011b0f020f0d0f140f07030e24181e1207080c060d060509040f02011b020d06111318060609050904060c030e030f19020a0201 66
    0xc00b86d110742e15000040ca030101500c02c600744800d0840d164001c6030b1000380494130140c200713550440c0c0201d01c840840d2000307000c8800401281501e41404202690811010a00c04a20203124100140b0741c2d494000213a950b81000380040b940e0341d4411401100440c44643e802c02c1d03549040036000071600164520700700b080c143c0c412086d46941c0800200c0070f0710b03407004050740041c0e10740041c190302880301040c4540d280c0154004010340900507482c1c0d05010750100b4018402d5030408215222000002c0e625192104a400150400b0b49066000207030045481400c02040c0710428842214107170003a01e48222071144600c000f0000a89010080d4010300c81480000024480c0c5d4024891942c3d130319181c1c0d0606051800c610105996903108401c1524181e0369003844e52914401c070b1000f01024100400c9951410011540306040104003808603a910303001519000d01a41207100102c0d10b50040d2980e03651a90461103003034201038401c01c066505104004501400000d03000100b5405031100c01e1040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 901797455 1250 901796205 901796237
    0x2f060105100c06090510090503070212060c04120f2009010501020102160201080408070b0108060a1401052101110d0c0207120224070605011202181513060f031a0c030106 74
    0x440f1491040350981b0404103140f082181c14803480404500c614003540e035491140c01017001e00240d101c010745054000c00c0034005001c0d40724044604039400d107045082c503480b480c2004010365144043c06484042190303c462096403245100108040e4101d5080b0200d07602d880049080740640326504d4070038690342c10407001541c0140d4089038450b116492803813504005a48286002c0740a030700c010096840042400000b00b918040c03041d0103600314031140e600750b140c00300050525840400320040c1e00d0341d5519001d481c00c4203402222400315a41e08050395800e41030b0b00781009009400c0404011300500b080400e20350292000d0840441d001090204034412144d204000142c07000c45000802c00200104000030342140292130003051022031038404080b0781c0c018001c1c2c1c80300311214420451584010480519007840034400c00c3c0da81907c1c400000c03190402d44800130b2040d03030404014101c107114004100b200512030f56240d8040780701146140d440302015400d4500080c0503407404904540c180031f00e21 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 901798561 1106 901797455 901797461
    0x10905040b0403120e0a145209020915090d0b060402160b04060606021606030b0414040f0606081207060c2f060105100c06 54
    0x61a10395942601c03000000d10040901000c0e4102c0c48103507459a124a030075078900e1085034074a004904003044c01d0412042000264441d030740c2c26000c9000e801250a050b40c203c2d06a80510966142d4002050001c21402e64018440c1c805c6044070f8030310440901004101006e4016a030300502418400c0c000310124501a00319010040d210468651094400955030080704e050700035268200014040d04c1442034000100300520310071001d1060f40380049004910402c41000303c00c1c1d1b100c4040e40c0f00e13001c4902c801c44a070342402d0200104c03402a04100e1a8150041000074600b004000000111400340d03801d507441c110214401e000c000807481008094440c8000600035503608000ca00c15a200d00072006141984411705031a2003800b90510312840440d1041d4034580d55041295144109200110401940701d104000034403810008c440701c1141e205692030354020481a1192405 = true := by decide +kernel

theorem cover : BRFrame.Cov 901618705 901798561 := by
  have h0 := BRFrame.cov_init 901618705
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901618705 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 901618705 ≤ n) (h2 : n < 901798561) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
