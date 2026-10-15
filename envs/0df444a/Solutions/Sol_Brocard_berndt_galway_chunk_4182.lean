-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4182
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:48:23.562994+00:00
-- url     : https://prove2.me/submissions/5b5a25c0-8e8b-4bde-a557-d14d9baba786

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 751978417 ≤ n < 752158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 751979667 1250 751978417 751978457
    0x15251103042c01060f0e0f10030e120c010c0e0d0b13050f06070507050f061015270609140d08030c12010303091701150b09060d0218041b 60
    0x105010300400d503002e94030200002c11102009a01c06004541d07140c60078004150000d43c2000103a80444414542040000004084080c070b00041c2e4209980c480c00741411503410821424040803903240715442d0307154801468040d00d03031101c8000c00030740c0003120b50460f804c0001c0c0d04080280c0c42042016a83d941d500d884144602c144010364091254501204100c801032083c030303000e09203e559070381c2e9440d2541000e5141040680e010100c1e90700070010880c114000c17902c8981940c5408803015041c004540088511082c80703021049182c3d901a00000d034071405502c0d58003194000d459410703c4503524000e50490b01c480c680d8050700054400c002c01e00083e003090085500c2032250098509103100d4100c261a0a00240c004901052828000740203a0035400c2d60590492803020091040b0601a20004140c40030341c400d0000e902c001068204181c3d0742c01d03042d10b1004019403411900c0750402000b404c01030b4a61696180070310710b840c0300544041901ba1200c0858141d5880310b00c5000328000000030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 751980917 1250 751979667 751979699
    0x14040e0408070c0f121e02011d0127060923090403200601182304290601031506020318060904020406020102040801150e01030b04051525110304 63
    0x200c4000300d04002c0745a80c1d01d0701d00d0f10054546105c240038282c44e10b02e403078000036500e2445080c1702800540000300503a401940c0b450f491030115043c47c0d020080c0d500584d16030280f4480300d0f00c900152542d00c11401401030340ca1342102d40c0c503514090b01a550300c100f28942c0c1d00c080d001840702e20203e100b0f5602c83c10243d000b0b540251003850040c0090031491036003005c0c1801c00d40d0321540e80d0020001044185042c4054507800f0b921300700b04000b000130704c150501c2200690603189404411800001e424002d4030751220b4000f0800b5120712400c0e283e40500e034001c3c2501111601d000c0b81c40e003017812041400850b030303403000c0e40c01c40d40041d131814030b103910319400300c1e41c03d1011654450301c108074015464496002400040485800258940d800c1c512003609451100c1c5a040003039051031400c00040309031040090460b50080201d60030b9482d03508001e4180703000c908081c00e420142c1800e1003021400044941956075404805401c01888160304840100103580c0034821a40300380001e06c058507010807801 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 751982167 1250 751980917 751980923
    0x402060a0c0510091b0503030a05041e05030d05040303110a020d0602090406051f120e060412120204030b0108160305030406030c1b050a1e0206070312021b0c0114040e040807 76
    0x1031543c502c1c81106605803640040100d83e02e0380c0610008a20803000740760113010304011000307507007054083c0c0e10040c4140182d2046002c520745001700100542c0300d0b809140d000d808054165002605040f501828550161104900103030104880403424040415200d0925600515201c0c4251064a500020350400303100c40f41d02c00e96850300006c041d9517803204000748107018421000181420304e800362061180990b056039050420040310700034900440d04944c030030342c41021041200c1c2101011500b100e0920301196009200003004003e0010602c0054102c038a20310441d0080d110307100f60b040c000c600911000300b4940c01400b050080074041d4102100c888071a02d030024846503110040c90b18128008025103c0380c02190501d414000703640206d9900010018003441c840b441580411224440d0300005410044643c40705c2003038145030303012110404103411103003114107882c01d0602d44500810f0380150205403100f02c9000c10005000036034048807040c40c0100d03030643e15a01d0381e4a4070b900c085012 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 751983417 1250 751982167 751982173
    0x60b040627080c0d061d07060e010516020d0812010f0f0611060703202718010306020306150a090e1311100315080318010516150209100309020a0e0402060a0c05 70
    0x3000d4040c03200201b01e06024510000c00c0490714140000e00204030791031016040100401c81e034141d0001c123402c1e10100e2681603406803d10140307402c00840c41d0103021090491680110f0002031100001d98900c4180c0300e18025440302d081da201000e540c011803007030752440541c1000740007419990203684500801408400c0d501c8030000240c041c56100d07405104814803000021101072594544a00785020404081e0f8044056440e80154800300070320500c80182406e4001000032110745880403c100705003803401c0381c20b841c1c80741420007600d040b4241c0641421700c4038200c005000da1201c10421603450760040c5001040390110742c14064045e41c004442030a15450f080700003459100340d0b01840003412008051921030312030324030618002da00d01801a0400c0320502c014100022a00034001d041c41d440f00c0d501c00c1000700c03000c00700c01a01401c0f211076404074080318205845601600a104aa4401c4a2049501752240c070034482442058038080d400c10424440941154021000c080001e4001d100b1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 751984667 1250 751983417 751983431
    0x12306180f060d1e180b0408130b0408550b0f0916060f030905150903070204050c0301030809010c08043b090d12060b040627080c0d06 59
    0x100c0c054507107012000e15880380c00c107884140c1c510350703200303c0c00440b02d405c11544a0399165100c000840c0c002402c00382045a0001d1404548414142001c00030540c041c1c0054440b6650700c0802e854000351000c182554400c0741c00840821100030740040f2001401c006a0045032581c0200f160007504100041fa010110314a018003003400e10003030074450101101c100c0c1c40c0e440c04230b200740d0614082680c00c001544152009000c550b420940b0b0081081d6503260008032800076051091408840444808000c031510f010b01140700004001440c800b4003e44041c0001c0d1541e1048100c0c0c0d1000744005400d000c81480f82c0001503120f1040326210720701500c2002d0030300b502c0b94040f0fa0080e0035540c0494510074030004e1040c50028054003c1c102c85654100300a840c64501032040d11020200c1c0004104aa003202080f0182c0481d8044009050320300f05036512a901d40c50054090424404a5050346064000207510856611f000e0015900c0b443c01801b40c8005040a200c0c40313031003092040385d9003912030030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 751985917 1250 751984667 751984687
    0x10302010906051e07390e060d060609050709120b010b0924030105100c02090c0c0703140102070501150303090b0d020c010c0e0109060309030806131103012306180f06 73
    0x8081c001150080342402000a1505000b1b104a0f10383c002149001034111050b00290a00c0e201500c01c07584e031030014124a5480200250154a20807030007401036241160101c0d03a216298401807045009498001006456a0010b041780400110084c4413184280041c01006090300190080c180068150725002050450361507503503101c1007210241c800037000411042c0b134607440c81d84503030b0210300b0110310701c21003078000c101c040d000181000390030000010310310742e60b01007000400c00940e0003285410340d00c0250300d0218041d6012600c1030310b9560a050b466881d00c2110101030b01200e03490784510b420a46044000f4115030080c1c810000000c0d824803002c1d40303009080c001d12021500903030380c411000c0d446d0070025040c1c41d11900048109441c1a07004000a90080807854000a046920301018050000c4402c09080d0040c00d000c00540c0c08000026281010301441c01042009400c64061120100502c80940250074503103c0034110101510312906202042101e5454080e20007864030350000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 751987167 1250 751985917 751985977
    0x10c180f0b09060c10020304060f0e0613050c030a0b040b100b0d050606162402030613090807050a03020d080903091c0201020a02040c090e0609010b19090503060c04030501050f01030201090605 84
    0x2400da103402c0340c00000f08001c09c06584907940c40044c070388104010018400024a941e2100105580b04086002c00d030b0400b400750400c1041e1140304003c00b1580061024903140c5981a0181d408480c070306014000b040c14512811900c1c015644c44445441c1030512844240028000282890b50010f0080107040818548a2000e01045016541c1440c0e4030078503107441c8294440c0e2544d1800c0c500d1041c01842010381e541c0781a40749001c2d180c1030124000080b030030061001c0c42001401451803169a0841d000c1503000300d4040c000280307a441d0005541c2e140ca038250340340e1062806c01d07035100b007404141503501c20f400007041e0340c054011301c1101c4031640c00358003040894219508800106420080812540444581c0c3e194045003d1311442100c5d4074065601e02d283c040c020b0b6548600030101e22038002c1c0d5115040030001840020203e42c1d03542808a40054194030a010a54041d401c0c100007408140c130001c0c1e000c0c101c981c1a074400c55800c1c5400c40c1212290402051203080d48840c03424510081202 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 751988417 1250 751987167 751987183
    0xc040e040303141b030a020d0b03031206010f1d010c0f120e0f01140909040807050109030c020f09090c19050a14030610120213020417010c180f0b09060c 67
    0x2074400250711035440d41d01c00003d8800424124844014448503180c03500002c05a03034104049240160302d46a200c0314610191042c0c1c1c4045401d480702107500d994070b035204003007103029000a80314008e15205449003113034810303224441458403098410340302e02c0551241c081241103074040c017000040102680c3d5400880d0524410040001307580e84542511450300a000c03c1d4801400d0030603005c00880c01a000c4068001c00e106039220f44403210006051001c48002c40303503c04d506c40001c0180c840d1915003c0c18640014900364003c55481c40e0302150303824a5501c003405001e51000a0140d1411002080203500c903003440b00401c03103d0302a0004803600ca035950400a8842c07091040a00c650b0001858900b101c024140580b14040a00c01c000a07d500708411110304d40564000c2c0e17072520319101c950068402c4c0d901004101d00107a680507064641036100e1841382d84c0e182e480a005192680c04000e003009140039024103200604030030884140003800401d403c04003c0d02d10f034181262010458149400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 751989667 1250 751988417 751988423
    0xf030f0c031b05071e050a14060709050d080d0e01180f1b0b0f070201051201170f030405061b250f0510090302271003150c05120c040e04 60
    0x152241ca0350700c1c429004140490b4822898000e00308203140c0c4030754191110f00c0302c003288080704114481081c00b50070b02030044555000b681c00307c681c6554a059036941c60f005c85102d4001406010042007902c3c01036184803880790130100144c149454610044001d001444255842c0d42d644d40001c8208601a074401000c0d40c06405444d801c2e040604080f01c2c2c17924180a0040580d0b1101018048104002c060f503524002c011000c540320803407880140c0d0548900303414550304005041c00018011480d286a00b1268035035016a4a03114403811420344e02e02460041650000041c080600041004070b448212107510400b2168000b00c0c0d13840283e03c071a1000352001c410030648000344101d00ca5078404a00074403040d0703040502042c00c0e5400400c482c0d40c6010091045a40309000524540c0b11090a80c0030302c8001c035184c901d401c200404c8180412180700480b07403d00c600200785841c1c40d8030312882000d02000e4480501c1c040d0b400c650528407a000800d410140f90003807201003104101500c25521940c4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 751990917 1250 751989667 751989671
    0x103022d071106030412050a020a08120103051902130e01180303020309070609030c03020d0302010e160f1a070f02030a14060f330301060b070b060f0d0807030f030f0c03 74
    0xc580c1082c551042c0660511401054100180000100c0c00d110500e04400c0e5454011780b60103040030128141020350001900d03991002c40c00c0a040c0c088d0003c2c50b4100d07071181d170494619681103542a080102012001303544803d4001e40079641c01c4003608460240d10303041c800041c1540c025070b02031070300c0d02400d101a80000e60101c00c100b0040c1e001c01404010745154108540814615039400c12461030a0000178012440014000c2c02c0500035080506103241c40b4003980da0003010301c84004440c9103584600035510185841c001141c850190500000701440840c151800465445c1c00d20b6402056030100d0f058454442d9400204040000a908055101e40600924106407c41081001010304940480016800c1d55100554150318011780e887e401c500f9882c0c03541101001900500390f90788034040031000042c40340e003000311041440348a010205d440c1c05003090400c060100020ba554401000030100300400004a8091410104082c0d414940400c51b4103007503402c08144d0b0820000440032035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 751992167 1250 751990917 751990927
    0x20309010e030d091407081c170f0f160c08070507030209010609090507031a010e040e0f2406010203270604030f0624060c050c090405060907050604060503060103022d 73
    0x8074800940c45c0241c402d9034014003125042c803000c00d488202d40d0000102034644699038240040c0902082e00e4064030004000c056464000e229000d034540465119400c40000000100e8204141030600454100c0350364640d101c24403540c4000560788618400c2d102407082e031000000594071042c500f400780405a6038005c8171807070841904d05481020b041e8a040c0f6052600c04155038061000e0302005d10401d207400d800951007030700810000c004403244054540910041c2041c010300000c0d480141c1422244245c070b080340400891410380006540c460b0058204000d549007a510140d80020085110702d100071100140c500051001c1d03010782c3c411540f0f9000900c0c01400d001107440b0701c0c0000820042000500002c03911802c5020b50705000d80d000344030980c0080024090100004134099a018101062a09281c248207071f0b5914100c8854041e4810b00d5000300c0d1900301a0251802c030303042c5444007400d64803560019006500b0980380e0a840901c3c08035032510703084d12004101049407800100783d540d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 751993417 1250 751992167 751992173
    0xf0605011211010525060f05130506010f0609120510151403010501031e05100c0e21030315010519050307030b0a0b070f05031303120809011e020309010e030d09 70
    0x5880d82d6030000b03052000a1104040601c0c00804040d61000c1e040c0388250541010321301100180b00e46a000345c0020720300000c00001c4600c840503100c6480c0100110b40b0306030303a548000030740d0003154003a42c1e0000c0d040e140200f01c103214195400080b079101d6001d07a4000600e184100b4100c175148007504000d0744034400304100400500300200c50001003600284040c2d03046884903481d16410400000d0714071108020102406401d114003088100f41c29014010304000140061428980182c1d0300d101d103140d400403080c016055801540140b00600c0950b04607501c840f08070381c1d982e41101107903040c0a0f08104c031100100b0040b00100c010292601c8068980c28120001004c075941c10642a004803010700c414400a030248040e9180154040e0040395410382c646402030031806007942030300210040b0350f000320030007a060b212510807041075510f020844c0d4400f00e0950a031070110303108110320799410030000c00002d0907800031644150240000300309104c00a8159241d43d010a0301e003400c06a5a1480c6010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 751994667 1250 751993417 751993433
    0x50c0a0506010f091a1c02041a09010e010303020d03150302060a09090f02132117030915191d030409060e0c09060406050a0306050a0e1602031905070f06050112 70
    0xd081348070000c1280940d461100310500c050f2108035445a001c005101440384100310f402c05410383e010f001480700e18401c29004e01001c5100042600c2034440c3e200216900380c0c046026812290940c2c01004280319981003680108041091841c205001c51404005a1100c0300201080d9481c0e560b0442044d19100031071007251180c1d035610109c1401085038842510035030030254152052580c020f2007600d1501403410351070300503890060100000c45410481c2548440c0514880c0d506541524000c800c9101405001c0500700d50080030701c180c054845e50368031502e5105124030100031000c46506407118848524641181e400680303055140c6a0074800507401003080c5030404464402030b4200306841c0c0000d81c8034001c9005580802c9008141400068400d800c080000c10000e02800b07200368541c40b47c564040c2d421604078100c04850f40301680410700c0002210211074074003803000840e03c0301c40700456241e4040c0605869596030062040d010400c14840c00c0d0007012000e0010802410743d01d40008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 751995917 1250 751994667 751994669
    0x309010b03070f0501050d0e070803180d08120a06080610140604080319020703020a1d070903230a05010f09022106010e1305060405010c181a0307050c0a0506010f 71
    0x80242c110350700c100018140742e004070041e641c00b401c0c240e4445412146031002070204503500c004070b120320a000100081c010004081859030005149000d4505805101a202413894014171b804010010481c1680d1071210064018000d81c80100e04ada60380d0405902c0d10f6000d940565510030066802c00c015403900b81b6107402c10340b044d45d1050506180c0460a9224021a003100c0e000000803903030f103000ca5100b4081040610b9000303040501282d00e41294804140103549400d1044007150045401c10f07000c0c000c03200480341c3c0001210346185000318030f0f160b810440500e030030b540c0c0300b040881400203c080c0103c0c0d05040000340000b030703a500d2900400810140800303080424415103101d00d0640a00810803038152107804840c00e030961902100c0705a44041c0c81d2018006014050603c070030842d041d000b02c00290f0303a40e550717040d504140b1190364090607060300c01e40070106c0e400a012911704038054003541e40601e550070034070b09090b505042d082c100105000101c6858024400512020300d80b80c01202c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 751997167 1250 751995917 751995919
    0x9020306040b061e100c050708060f0f0105010305090c0622031101021c0f03110c03070302151506160c17010618020426032a0d030c050f0903010209040e030309010b 72
    0x1610350042000800c12000e4800c00040c100206e0f41070490902a0401c61000244104412544c640c504040b010291507001d035a07501c0c08050030b00000840c0d42c400d004d8140528a000d000c1c01e0006040d6041103241e80c00011207000703a900c81c00c600ca00c031043c02480324009600400209040c0ca40001c002400c0c20b084c0c0c090b205909080020b08480c081d41322a4070002d0360980d05000949150103091560980210007200108c0c0c07100240e488200750f4003045d615544150000000140d4891442080c444000340d042c89410503414050055040020406001401d0048001103401a01c400881d00b1a00190f200005140c2d142d0b18100140c00c0c0400c6081c0c1a80c8903a0411400c1034180013090ba40604a04103903518490011251305031100280200d038100c114164400c00e815802c3c07a106c030421102c00c8030038000d80c040c03d680d100080340030340182c4070101d029031384291410264a100b0841038009200032a05598240400d500c180c40703a02c0b0703040c0e42d203c60000554503403a180071040e003580c12204100d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 751998417 1250 751997167 751997209
    0x1005180108071403100b0a0c0501060e07020a1b08070b1809010302090402040b040f0e0f2104120c0315021b010905060703110d05160f03021201150309020306040b06 72
    0x95041c1c0c00003840006000f814903003030396900c42400707610000020707030030040c400c040000d001160303590450505d81645105000a00100d035455036070038000281180c03804056041003070300c2d0f07001034940401c41180340c035082c107444021038485804504e8003c1680010300c11800c00501c0317000054151022504000c4d04503000c0f006076040d40c1c045810003030050402030260f511341400070025500c40e0030003c140f119104040009120b281d0a0360790310318070395a11442e180078100d034540c101d8001d41d00b40c40305100d0a085e01d034903003483c0c00f0300000c0401010700c0588007c126100084005010803620541480303140030050f0701d40c01c490b4000703211800d0f484441c43c442da1510701c00d000000c00124402d41d00900380e09000030034050400031250b0b035115164410126600c0d0200700554405040c040f1038240d0510f50b289010340c0d4070f070b29044d4100d1060010315042d507480306004204900c034958605400c0051844d0104124489a008c00e26040c0160740c102c580c507a001e030400540d4109500c00032b8400e040c103425 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 751999667 1250 751998417 751998421
    0x2031806100b0f09040e0d030b06181908010c030522021f0e090901050a0b060301060801050f270a15060801030f050a08030f040b0a0e03271005180108 66
    0x310600c05030292003502d005142c0490000e1101c0c2c012829180b41c0f410282c4103200c46288420003a4890701d00c080c4140209141c255910203d080074025101c00124004410800688020800485140603400c0d081d503440c030300201054007182800383e0324080160740c40105580c1011000d07281c1c0001c2c20100780a90468510518000d44d590001c10070360141c04180d00d221358140c0f02c3e01125240e0b9407844568105003403109001e00d282c015030080d485030071300080402449151400300481c611080c4117190014a00000500251030714117290359160100610310f090842001d1489061007030110090300d5221513460401000401c94000d40103002c500c040c02d100a5401c002d0050440481030002038200b6900030070260401c8800c011080051f500501d40680303915154904c141090011241212200642808a040c6000d02d000300b90103100c441014508081d4600003e0550054516415071041442400c8044a80395036550340108019513943d5942c408401c813000d6082c64041316100d04008081007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 752000917 1250 751999667 751999681
    0x1401060e0d060b040204270c050f040e070e04060303030c0905031c0c060b0a0f09110702090f0403020c15041706062d13140907080c010f091802031806 66
    0x2404030700382d10041c005000701c0600c001c10001d00880d040b0140d10300100720090409030b40013414222142a2032000e1011b1008040100c4445c020141019035032841031100340041040c44000c5a400b00c050710303050250f08030410010303059421135481a000301c0e42e1804003009040c0e00c483c415024090640041094000407040042128980d003003070020440c3c8084240104495a0490f25024000078003101c441901d462520025159034800c0050780c3d8a80940c04403482050015207160f950014640e5040d0340d0303800c1c42c082c440c0000500850071402488941300007a52881c2c0d8901010860001c0c00c0e45807800c00503920380c04448052103050750744c88101000415610b9444005c00781d80703903100701d1045044400cd110445200640c0603a8090345d0300c0810440304900703074814000c400c02c42ca0740718403a840c0c1c0381000351142e0850051400a410404245d0030710350080d142c844454005103440d1640b1550b4242c540c151000081d00c82100076000001d02c4420500700016815654804010b440d2500b4050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 752002167 1250 752000917 752000929
    0x6120f1416080420180c0301050a0f0501021903030b030d050307030b09242d1f0f050903030409060b07060e0d02150c1b0a0219030807080c0a0f05011401060e 69
    0x341c80b00d10b05400c40c1c0b0310b403086880c1e0140d141c00305c5503038003000034003400d00c03041c9012550024043d41b170250f07804050015038140540101003c494041c1c01404000c1c14203603841ca2120142c1c2c41c25014552601b003282d295480030001c8480b0f0b5030a581e52692242090103008051315015002c4901c03c1403280c0520104445030b03010421115807070340d000714102c80c80d8000b080200120554211030f00001000d01c84030b0340300c82c01525a04903421a54003036003050403c0e284000b008800c0100d40040c0b4078080c02c400d8a8010802840c0002e80201102d0803d961a0f0307000c1d00b60360340c50f0000054a031010070000c0401185000d880000c9060101904c90200406d100070359400f03800109055104090010500116007402256101550b02c4826030040d4400254103a580f0b81c2c10200f02e020b106001c11072005149041a098203896200310300b0fa20380151602c901c03c581d00050545aa07a004602c2c0600000321140c0d0400075451280c0e00116200c1e0855003070445185050b400038040c0400307109010002d544030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 752003417 1250 752002167 752002193
    0x90a1502010504061d0c04020315030607080702160803090f1306060c0c0f05011403060a030f1a010e01080d0e04020c07180f020906031f05030f03120a02090a06120f14160804 76
    0x40e100162270f5503c1c0344015282c2c8d528114010740601500040c4001c0e19400180c0070b114919917001c40d08605070120082e02828943d2059070b9061304140200f04c2e8505e40171000244804c0010100700c880c9038124014005c44800d03030700c030401003101050128100200300300040000e25400001040061a082c00a882380b03403156003c141700c3c103002001680991f0b4690041015541000c8078401c00040d61a01c405006200012a000503400c0c0340001a2b41503000b0301103050b42c044001601c0707801c0c2c4590080c0c80245048a18540c4a41c0078022240c00e548100000001424100006a845840b1740103940c01c031f406002c2c418802c0f5004010b00000c54450364100e0341c00810809121a08418031510200c011940307401940c4d03d07004803130803840d051f100000901924658074200301203588510060304120700c203550b050b5400c21030060040115600919601e0390008204502181542036401400d08032548010f9020140d00344c001401803904080008019050240c10112a281081e03201c03c400b400d86 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 752004667 1250 752003417 752003419
    0x11090907030207060c030207060b0f1f020307050d0c2906090405010e250e060310020705030f0408011a01050a080c16050f01061403120708090a1502010504061d0c 71
    0x11440400e0a051280d412035401c99084102000f02d100424002000307940880025100d081c2020304000d164500041c2545081d040202100359040310310200c3d85258203003803241000d5002c00c0c018840811348c140000c17089202a0340e1020440c080740d18000c040c2599903513282804503441d01c2210803d030400f910403a0005c0048480b103800d03540b82c0c07900a001d0445d14403440c0c1103001d418010880442c02034144070006d4071001c044035801c1e03211620ba254450007281d02603410303800701c052100100c1c4944c0c020000747e401841070744d1801142c009030404c542e1043c1d004110b269511400400030004d2485158407850007468442d203002004c02d0010400d003006800403900d004006009000e813002e180002041c50b5102c002c0d501500c565400b454020301040c0714849e218803160590030402e1601140d24104600400d9100e8200300550325101482d0304507441ca5034000303965600220b42007140604103c0302d81c07450390003c6403034540fa1905406407100c40c0c0a42c1e40d4105d86c3c118854802c60086901021008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 752005917 1250 752004667 752004679
    0x30903010e06070801240507240906240b0d06080604030203090102010c0f120e0c0a140a060f2001060512011b05040b04030305090a030b010e0f0f0c04170f060901020c0708011109 78
    0x1049040c22765001098080d103003840c030444814960300700d403a44c0000403041e000d590100011321415514801488211141c010601c2c00e0081c140b00c069481c43c0607100507010205d00252407910fa243d4145050016241900507074404545030702e2a6038240a2b21555900da40350985904205400c040c06250841c0c200954043d210510056140001c21448a81c071340020300c050ba030a030f5603c401c40341c0141d00c43c2a890240c0c00b5910082240d82c0a8154000f408140f03503100901814546800122407106500250703055403103103070000300c0341c4e6164245420010400000903000145c0010021700c0d41a150306181030280501040003000301b80001d60301102d80500705141c0c0d80a803000064a562030980008214144840001c528410205d100600c00c0d00c6042203031660b83c480030740c2c8010b101c00c100c0d004101d0540410040c0440c40c0c1c6040b500401c0c001d071f0000c031407880a002d6942404c0c2001100c1e401d01c160b60205051003810403c11a42c401004040003c100d04040743c190f01d1101c2c0302d25090640150 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 752007167 1250 752005917 752005927
    0x304020102100c030e010609020f04061b0f06020307200303060112060e040c0e0c09090103080f2a190f0b5a0a0509030903010e060708012405 62
    0x64001d01c81c0000c4642200b0702040700a0140902400030012140b03d00550f601c0d04502140c2030380d00e4422034a00381c0a083c80d00e8202840c01004541503048441c60b0249c6002c140701c1c4c000051203515601d035810781318500141e20307440c0003940144546650000914102140d0250b2000c4800110840c2e800441c03c1ca0541401b00880c10340c540502055841004050061010042400410b0450006481c0304504035100c2ea280c0e617110080a000360b1455690202c2504010800601e0207001407a095010311201030901c080e000315501e00d007504220141c0748840078218401400000d20401240d0680c0429040040c2c0345030b1a82c039198140160014800107511000c42c14500810f108042021015500039503e51404c60f40c1e69559400188980c1d280394041c0e40407512080c51044080c040f003007140d16200c0030b68691300d040f006044003900100050000f0404082691000c0c010b45954001c0e400051a66003050600180843e40c140e001ca2403150314110241c032075080030650300c0c1d002101031802c1034503a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 752008417 1250 752007167 752007169
    0x9170445050a09050a0506010302091803090d02011e03090209090f0325021003060e010e15090406112208190303110904050117010506030d09030b18030c0a0b0c09090c030402 76
    0x1040403c0018056106422040040040c0010014141ca10981e0703040519110248406005a0011207003040b58100741704035803031070902020b160146401450305000c0c0414010882000840180c44800001d495403545800c0d400c2c440101c42e00241900010030014618015464503802703500b451100350181401c0f0401e030b24401800051041d50014004182c26450300c4028001709068030603c03001e401d59000025031240001c1d441071280d04c07500c1203070102540c00b60401c0b24501c001001226040e56401c0141341d513400d4400134101b074170072040b55041c00c80c1c00046491400d8503076500038809940600c00700507030800da02507211000d0f41d00d420046681504420000007500038008036942251408000040c4101c0511603420403090b820001c01c995190402450f40f20383c424203c080210744400d00c1040001c0c02058016480f00f0005071062400d80c6c0c01ca086415640700c000e81c01042c3e400640361380103000c03283d00b0a54100f5811010207107040c1215005c82c050b041e0003001030745140b801200103015 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 752009667 1250 752008417 752008421
    0xc210303110d050702030d0501150e09041a150301050112080f0a03020c120d20031b0f0c0c03060703020405030c01360f050904050303060409170445050a 67
    0x82c81d000407005002e2071624000096030303504410706450201e0301f86000000c030862410058150302c0110ba070f0304403244a0900500404540261088a00c42e03030002102001d070308100b04203405009019494120840300b04101403c0d942e060300032417420a010303c24803001032403542c1200c0d64610a517070f0080e1156403510023540240242e50f001d184a00a070f10007040410301483c000e0012032043c09080100c8000144030342030020320441c000d010048100042940480c141c035030528443c0c4180d204500d007c0442621620541202c40b4084a43e4000f20380581203180074403545a00c819a8078045080918002c0040e80d070310032031342c60a4188403140d15045828600c0c002000840607050040d105981941c6e01801c0010182d80f0403a08601c1c00301101094520300f0b070304014000c0b41c01400840c15034491001b040000d2a8020b41141c000714903000391138007018070b04080c1001382548000e09040c030852012080c0d001b07034001030440e00820f01800c1c40e4074a02000313002460660031400005800e130740300080703500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 752010917 1250 752009667 752009677
    0xa12021506211213030209010b030f0406020c070b211f0306020f0706090b06010813030c060b0f090c0406030f06050d171b030403020f0406053f03070c21030311 70
    0x40b5900c0001621501d0000306030440c0c084a00c01d5506c6401c41c0e03a1100d40c05030f140401d803142441321044bc0041404102e080d00070b00300b004554000e841506558503021a8654810f1f4100c504904c00105038003000f6002100d10341d0300140004241d543e081a01004485409940c00300615103940401d00084410140043c2e60300d080d0700501c100847c120b17604022001e408100c0e1982d00003090700001800946074550100002d9600d5254401410075995802016104003544160002c0203c812100e0940e501030390f044c0a646880c2c0310f16074a0741130540040580b00c110000d061158109030041045407641d50400180710340060700551b18144407189180e00c1d12a07010b040f070781c0409426801c55076500200080080340e20844041e4407050154042c00240c51480c402c0c0e03035100c503480103210040380865400b0301640d04402c070007040c1010902c0540303084400f20451290302c0c0d40042041402c05c42e2400306900540281c0c0c0b00c000c0b850000c00300c044903000803048001e04064595a4032203190780c2d600e0a690b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 752012167 1250 752010917 752010943
    0x90903021f0905010608010b010c0209040204111c0b0d081b0c04061d060415061b08041401020c180106110f12120f090c060901020f0a1202150621 64
    0x1560a910354000d071000c0c10410906641c00d51030540300003000030741446480c0f030020040c0c4135203107102060f408000920760014000e982080d246c100300b5008114040c000c1c02c2e604092090000810f0b40c901c4240b0881e5200b003400c500940c0100c5803c07010510040648a81101a401c0f4040d02c2d40c07040f040a0505111030501d6401500381400841c8e0b00c030040c1090200064018a50041076650b2000c200540d00c02004099804045810520060380310b440f41d41108086400b1403400d14816070f41d001c01c030364065070101400701000b00080c0b0140da8188200c90030309900311003d50b4120300c0c008441c409020180b107090248469280d00c6000d00d0f10600803a41c040100100b03480304031a081c0b05519055210100302c04040d180b550000743c1090749194000c1c0901800401401d003c54003500388041540f180010b941984500c0b4540c4001c2001002031001c0c00744942c3c203408902403801030180ca041c00744089141201c280303000700b01082d2506000d0b82d8046c410160000080b00203c0d0302c0385c0c10038a07025201 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 752013417 1250 752012167 752012203
    0x170a0b04050a150e121e09061204050c0a060e01090e0709030605010902030612030c0c0f130203070e03010b0f03060f04060908030718060509221127030705060409090302 74
    0x200c00c03c40700c903800042c108800300c0944084088504070004207104100960160410030300208003c100c03c1005000c910101408070b51500080900c4540100070807202100d480d80b14441540e1a401c000210000070030341810200303803142c904000070340303612418010740d080110b1078070005003000d102c3c40080300150340201c0200825615083c1000182d40300b1070f41309004100d0350300c00c3e01c8180000011200002514000342100d00781c010100a0220341052500382d008451515007245a4203e100450040500d41ca9441c0041c0c603d20a141c01e450b03101c00303032034450400c40000c80c14540b0089140369110481109250707481c0d441e8135020005101007c00a0b29000c400700811034865040f15201c411451342e0000c101c0c2c06550782c00111181d10400c115a90844242d02e4081180300b040e0305030440b0a00d54030b201003809130f002001c025041c0c024901c900c0d01c640445840c0d400644501ca1003003110102a4040e05d03280e4200341c049081032049201d0102d02c169228880c1c014944240f0981d0740082d101058 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 752014667 1250 752013417 752013443
    0x10e0d080f0c0a120503070c26040b0307090f050a09021e04030f110405041a100513060608090309310c050703022b0302160507030305030f01170a0b04050a 68
    0x8a590f07103071159a01203070100d5082d5800e04110b4000c5007030301c3c0300c0d01c143c0c0e0b50101a4242c0356902c802c6e03401ca48541168851900c04643c05d20a500030242c03020f00481c44200ba10703450700013001445000e569001d94180a10480c041c00705885000154080c2c0c0d03d03145000d6544c2081075201d08400c8001c002c0c88c140c0d4900814088100b101e118a010a56801281e10507189043c840400c030490710140c42c0104100f456003909449100e039407a400341e010b40d01c078a401c106180d41d800881e81d84410b200c2c1c001c404940c0c4100500a030f40c2c02c407820703903040b110302c81c0194281419040400c034007002c01030b807000740c0e980c0c804080f1240d0f510f1521607564225a0400c20300c40280f075030f4070140098100760000c4001d0b00030000076a14541014008419101d022408140e903462203107021f600035800070341104060000301ca40480401d108102880082d0310a030780315503036840c104d0041000305d04181c0000785545d401d10707440000d540c000100040b00c2a0802c0c4014516255131401e0b51a24600c004010f01c10301d01c0c0c0c2c00f = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 752015917 1250 752014667 752014687
    0xc040e0303010302010f051303030e061207120c050702030d0315030609030c02040b010e090411041d07030515070203030a02130320270f07030608160602010c030b010e0d080f 76
    0xc040c50480c2d200703032620f8000034600c042c1074031240208210f0070390a051405040010a2080007103c0d1000001742049287c02410000503425013030454420010622500034160802d869109010100c091403070304034140031a0707a0010361034000070500d00e010192200721703000e05e100081c81c1130341c019a4071040800140f840ca19003c0d0480322a10320070383c801c83c9411101c2d11a54040c64000b56070b000c00401d9004c25079107030b03030310300c11a8941211050b402982c0c4105451a61540a04259900350401c005100e11740c82e41c68050b14040c041401100c00441c02c0d001c5c05a1b898000080c1c84d00802e8442c2c0142c0c51b4210560282409102680301a05201c52410548240d100380c0401c420801e0f4290f1306002e0850450310610070080d1140c05d06903048100b600010088004070400541000307803444c0c04030f0030310b54072501a0310344401c1d811190140001e40b9410440c00360240328080f48404603083c1402034a103502c00190007030540705405400764409184e40e0702040000000c0f55034800e40c0200403030b00e401c9600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 752017167 1250 752015917 752015923
    0x10050117070918091b052101020f070f02091807140f060a03020d0e0606030304050d02030c31110d0906111303020a0b180d05012d140c090f030c040e 65
    0x74800743c98120300100036400d07074940d02c2e910805844010348281e40000b8051600484401c7d00021418955801d03c86500c0301c418070b40080916038014030961207004150b004001c5461405001400036403d0640080305040d0080380d214115800f06080a046410a0002c2140074550201141c3d110900007079881c140d036010390241039841303010390041180900f400c00550b0384100584070b4980c5a881840104401d00d44195038000c41ea2016007a030710003040c018041914005084040007902405030220704242e00c0700d01a418a03e500c02c40240700c0b206003840c03119081c0c42459800d0309050740f905040000e00084cd0454004100d07034038400341d038890301d0400300801ca1006000032031040c0e4071100005080c10450007a0342500e80d10303c081101030b1070860104007074060001422106552030303907130305d01504040000b2400d2508000328088110414107600008883d0080c003031000380704209040c840380c103428a066505030842958051001d2400b000000d19100c1c0d141c0d0119841801d040c0c000a4950b008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 752018417 1250 752017167 752017181
    0x80307080a030b0102071a09040609060e0402090c071e050a17040503010b0a26160306020306010306050d030903080a050405030618010c0203121302210105060910050117070918 77
    0x282e40c082000381c00380c000491b143c66240c40707a55012010a283c00350085100f500500c0079010046c4001840c0d0740d120043d10aa401c0c5902c141042000b890800042d4100b18080550007011801c25a00d840003540e0740541c21750284110841d0080400e10303180400204000601c021340d04400c50007022000509620056841405894029428481d014150341016480c10095440203101c18180354440c041c000c00000030403821034281d2282004002d2030f45040115240694091000036a40737282000002d429101ca5600203402242d030b032012840841d5011040c0c40035254845401541d94005030411038082c082d54105642c0750003030200780300004201c1c1810710748807000d5800900098a48440c2030381c4a0040c01d802046044600300062400120459034159180c0300030507241e40c1003142c000e903040a0451240310341440c0e6440003484924501500c455912040e603103030340d680c510304140000703081c1c4111a05070380783e44d00c171500843c1c41c882c0603611250280c458221041144040d48040c00050110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 752019667 1250 752018417 752018437
    0x1d0f1302180411030109030e060a02031201080706140f03130201030b0406120c06110304090b1c060504110a18020915030718050a0621090b010f060207090212010e04080408030708 78
    0x103d26035112079801d060050325250b070740688910f402c284d090014003a01d40d10812110046010401c410198400c070110064043c00400c401001200e0920381c000e4041503080d0000b0203141e40030700507010b8080d139150450360700002c82081000448924801600600103115285a10071709100000c00c0c440c0300e036a5000e4096000b074608400440e0f80e0801958010040d01010426400c100410f1110a4441c0c00500d1402006412520803000d44c4031200310520101904031423490700c6900f40410b00a00c0088214502d0003110f524456518100012a040c0044070390700000c0c0d40c011560b1091542c40d00000c100c2070205200302c0360340e49441440100412606e1302603004001030041c002c01d850421700041c0f400d4a20301e8032004480680e0745401e10b1004d00303146044405e5511445900c0005241c09240c038003e14000a031209094200324010341058810b8000c59086441030040d80b01d81d4955904c600c1c1192011059442c0c50344a40c1401700043c4030340d400070001840000b800c40d00b00800100142a00c1030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 752020917 1250 752019667 752019683
    0x70c0f02061606330509010e100803030a1b02150601030e010905010203040b0f0703150e0a0b0d03030209100216120302070b1801110f0a2a17071d0f13021804 69
    0x114203614004d00100c280100b5030844400c2005000581c0441c1c151500140188202d5007929900e410207403656000b120a40c140039224020301000c0d10842a202145204500241016048154442c04c0d03c0500400c245d04040c0c917400311070741c072000c02e5209051064000009560b01d00e4035080c0600c0b204c2050b40c0070102140890001003056220f41710b0314000d00c1e102c0d40c4803207041d483c0030802c00a609000c6c0800b40c2041da0703080c041d41d075584d450140c801c0c1e030744c0300340c81c0541c945456404120b184a40101c000341990444105d1045e040b130510000303025250742c8585640e1108250030120310b48645600442444800041c011000164030000748500541c240d03510080c54540e0402d43d40c407042c0340c01402e0f0441e441400004006000041d00c11007000c900010020901c040c03681c0401001c800d0f621110880c00307642c2c42a1a8900140038080240584610003c4003080c2c10b40040c0510000401d1070795600580000700f159404040c5102d00041d800030303c0c401240040319003e944000040c0c0c0d084401d13403 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 752022167 1250 752020917 752020991
    0x7021c03110f0303070302091c03170a110405060703110601030b0103050106121e290109050f0601050414010e0607060c0e031209040b0303071703070206070c0f02061606 74
    0x80028802d0000c080c4400a18219118141c00340c010307410880c40b156014141600c2003100000d000185200c8900981d103005403001e94100c080c100c248040e24034491b6a052981c0944e11200b448216402c840040c0c3d05142d40d000d050408980600d59210440204c0c02a0380001040c00780a100d0541030300c0c0610020885540e0381c0749c900d204040e1008001f80001c0c505910b0094004086d614014041d020b07041018001c4003501818800080c01c1d18903800040407000144501481445000c4c2c0c40b454407114615181440e00018089014610580500003088540301203141d12442e0003180106014149685401c1e41d442c2c0800503014049100001800100303c501b000d190025150000c2d030014000a86082d00803c01e020181804001d29500351100b040404005100c038484007a40c0c0402198240e00e900b17040700000d04284026004170b0400a84244180102d200d00004000d03007503040780d203999030f002e040d5068280001c08910240c4428076040b00c1d603143c5202207904001800c15002440484 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 752023417 1250 752022167 752022197
    0x10302090f040518010615030612080f0703030e011503030e09070e3003120f04030917190308010f12050309090916031208010b030f07030b040207021c03 67
    0xd018854100d0340c0502403011403011810309601003500501050101840c1030020b9140b9425a4001d5100107504030203240d5100320b00354036125040c040c014202c0c1c04015800f140d1262022030044c90182c150076680082d0f00b008060080d0b006500d26407041d002800401801106251401c102d031101343c01107103503c00c4d15550b62600800c07240c4103a0140d12070707121205100d03060054007114030094107803c0c01c00c044006481c00045240c1408464020020360b40c540f9000180d80e5541400b03420ba0120040386c00c01d1000003504443c140096a107103082d02000596410400c1d4a040c41c0a2042d03810228a00c918100345988680113a060342d80b001200c1c079580d9510072403042240b22800000e400c0750024030624181d4034040c80e459800010410031208400c862034011a601c05280d442241e07a0004641c002600c84d0b040000075004050344090136003036142846c82e05003c914000d01107010983c0e5910b090301c080d611541900c1803650090480c03d1030408040d214001c4101c04035060300490104001c902d91 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 752024667 1250 752023417 752023421
    0xe0d140306010f2a0b160f08041b0e0f0103050d0921020105040b03091f140714040f0305070f090c0c12031b2007060e150421030e0103 59
    0x80d40040e50381034080440802d0071201d035040c4052120500602c0c625842d0141103e181083c1018003d17110020329003000b428100000c8601030707402052003022021400380c0da4200d1510b90b8050f401921b040150790080e442a003000e41c01c0e8010090414081084c04811200e120300f05060b248a50100c1d11207202070340003a00c00803058424915102c0f464509406e1100d0800b50101e011071042c10407904160303c41c14805500d03003003100c0c0c0881d29800f000c1c403801203601e09a00800e010a0400c030070401c0b14040140e516800c0702c01806c600900c902c82015449082e40d071307421600180850141110160340301e1410395124049071007000044542c0900104503c29948260115045162240b2070100396079a540d110005405010710207040c3e440380d81d00c1c04c4021003422001040b049545440810259003107078203000c0305000b0000001c2d4402d61041c00055005030000c030994004540b003003684074100c4010300103171017903030030003440102c002c04003c0391140b2001003140341c607110b0b48a403c013011415004400f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 752025917 1250 752024667 752024671
    0x13050307050333090a121403130312020313421e0e16051005090607050109230102030f01090504031101060e07090f0f030318090e0d1403 60
    0x1e80343d041a100c3d440d80c90700c18941c050f0690b4483c10100c014056840035605210003c0ba0ba40c025500050342e83c000701706aa003102e405800c028103120038901e0050107446504c0c04007c040d0a0401d00d030440450602d40105404100b44c020081d0565a0340340010092a200502c0e002c1258841c240290310f100000d03802ea01320034200e901c0d40b64100000d60b00703062920b0400000c03000d8070440380c0c2c400300c01c0c01c00e02c5100744040c450102e082010514903c051b201c24034080303560b10404a8212000b0041c00380e41d585e060a829120b032540341039030f120b44c14200003581074445d992004015600e0807035050700700818180c910b0352814004808418000409402d2803d07480111000b444148501d801840300c1e006c6984042d0700a400307494540f0506101203181c0e400c540044e040303424003841480402012560000c1114050304a102020045a1400580340c050f00018000103090104540c8081a94090b142d940002464406001d000c0440780e841400c0c0c54a4455a10700001703904000c0120305201c00c841100c2c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 752027167 1250 752025917 752025919
    0x103061d0613062012070f020303090c1002011112041101140d0c09080318130902030304091a0a0e1e06010206040f060204081605040f0b030601140f04050405031305030705 75
    0xe202005555031400208a45010381040007000768900d00c4d6400110040c003002c8070035040a003e00c0c1061130001c0e210035840d500c1c6204540c0100700704071200c1e601080381050401c060740c09400c0c4100d1198107030f014050100341c1c44049070002c5100804e0100c00510709014501030b4204600e030300014001194550704050300203649840c1000311080c07041807688402c2c1001c8052030407554060f103a0002c5410b40d404010341c90858014012801c54525100c1c00007903802085000800078003200d980444d8407805075214549030680d541d0080d1140e030380140c0c91030404110040c445d12080343c650054002c120702c1a52491a1550a2126005101400312000b800707244140c00030896943c40c1d1341c402c5400c02c542503003204c04a80901000500c05010800c40c00d503400011031103252a4201010321045520900100785124100481c110540c2c50214426040d115048080c46210030180040740c0e1940c1781c10040303074106160001300401d0100200260202100400c0350042035641d850415554070401e0090f2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 752028417 1250 752027167 752027191
    0x601030203010b0f280518010806100513031217060f060316170709031a01060918110a080406051005030c0f030703060507080916080705060d0b0301050103061d06 71
    0x40013000703000c4018040e0191816090060104985051409100c107210a2004103e003c908030590540903400b0f02c80c4c03500d00f0f00c0c22000902e4200c00280b5041c40c075090141c14440005a0304d21040b10182c0980c6c09144c0010392a820f0854008001306000c0144188915005100d00820307502c1c1351003c40300b007010034020085c81c11521070000880131034003500510b42c1071049483d1504d04988031221645d20891141e00e0b801c2680c1d20b5824418840d86082c5081e00c0001c0140005000ca19004450107042d1400d1041c1512003901c40c0d24210002c11034646000007070394000c100d03020681e5100040c58401c0380304074401c0c07080d82c803081e8042458860074001c050741a04892201c0045080041d14689800f00040031691110707030b69202d0a085070015194440091860410400d502c80f080010030741c41c0d000c0420144a80f49400340c80c40c3c50350458081c5030b1244100044145551425810010300020003c1c02000196928038104004003030f61441c0010105009101642100e00800e100d40f103012020a2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 752029667 1250 752028417 752028427
    0x20f0307150f0504060b03100b030a29190606110c060f1c0209010e0604060906050f0423151c020705011d0d1704020f0112020906130e0601030203010b 66
    0x74188004020300220750740d4542d208039444600070140101d5008900a03100000d030440e010303050509003415803e071040001c1c103203014400181c0300041ca400788950000306c0c5041e03c4450902051002030303050062400f5411910610900c120117040340d0500141d80d610801c62955038031015505010903100d0b4020390381210120000ca410f200b001400d0380100b80403010b01d0302d40c240b0b01e0205518446540c40428550101e0040d00c696000040c00c804c0c00d40c102d85c00c034242868200001c2c104610341c010803003000004074485002030005401c4d1005000c514440c20a00c2d0190300281c2c6a41307068804c41e0b0b10850f94880949040c0c400601120202a039480c5001000c15000200901a503c03010045801d5940d40300100705a03d020b0b115807020745405405028156607454005010504c0288921417071140c030018000180c1d1190385c00d1300d80c000c1c20708001e08940c10b034042080003406000310442e0030080004040340b08107620a80d070340c141c2e214030003960034a80b10400110124002402b0703481c00d100d02040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 752030917 1250 752029667 752029673
    0x51e030606090d030e01020114011d28150501090f090b150c0c03120307050f031003050109032601060e010c0203070915030219080d23040f030b092a0a0509071e020f0307 74
    0x20540c40034907540300c1c2d4180b20202c512000a10302203014030f41903507541c00d51550000c03160550f200c0144ed0900c0e04945042c2080d03640002a4900c0c440e1006456035015102c3c0c0391b0710341c442041c0b21885903202940d03d8035a03a1030441c0d20b50141c218540e110b80150411041c1d20304140d81500d0140d055035903000c1c1021845000503800ea031028140e100b01c018070f5940003000503001d0240040140c8244e40e84088100d27850f0030361a0381103071141548280e40c0c601e00103110003036201c4515408000c003403802c00018601e038000b2034281002904008089810901700725100000440950100d900c01c0d50502129940070103d844411001c0c020311100d03800c04450805414428510310408002e0100440301021240910002c181d2080d031048058a906200401c18402000d20542c0e0002c80c2a0141c801281001140c8000051880d094200c0400403483e9603600d882d03451030880500b50242403e00c050911260213007100450358200751503600e041032000d1007039102042c1004202000c00041d820280c09039 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 752032167 1250 752030917 752030969
    0xb01051002070530070b030403030b2701140102031206010825030501030c06020a030c0204050a140a0e0607021c21240501051e030606090d030e0102011401 68
    0x40c0008045210703034a030105090b0384902d8120204102c03101303c00403c0824900041e082c0c515116504103a801201d010400481d10000304c035401503051a00003059101540090f103a105080320070900489240d8011040600340c001050607a02020301c1c1090700310881d001203a036441780c01141070701c65090b1400b081055005014040c1c2100c45042d107080a1100d0f900080501c9000d92800f100081d150001001406564024200a41440c1c405401500220b4402510704c10040000034056903a4000140807010141d000042c48100601580c01e07034105015040050030142d5680384c1e0a009507004518554000a40400c0403840c644800a004820407001c0d00c000d030990b00091094184c2c00c2a9076074041d03403841011076201444000c081c0c0580d80300c0c9149081001600842c1c1440f1040020040e12004a0801d030826003e034441d507039403a80e07502c0100c1c04034050031a1043e00322206607241001c04d03170070000e03014045800380e00030000ea100085c072800080784203100f0a0072003c0c0044015480401c0c08d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 752033417 1250 752032167 752032189
    0x31b050d140f1618020711150d062306041d10053006060a090902060c1204080607020307030e010807020c1009090501050609011434020112090b0105 65
    0x580542d0703055640c1c40c2c10030381841c12160600e0801034102c1803c2c41032141c009103015000d607000c1001c501385150350340c55100803080304924500c1a15615022024000c01404880307101242d01410702c05540e560110035098900716900a080c42d04000e0784e81207a080c000305407011580f046103540d4000301074109008013030320054035548001d61131810200f0140c4903941341c84039000c1c4010074010300c180d4040c07110884120800a444c102e42001e011300507242e40341c442c9001a82c2046030009908911480050340e1440394182d01075260065003114072032103007801e000d401141d40c0803084d9245541c0300340d01261203101c4c199004002c00c3c0944032003407495202e109050340c013081d03d00495004440080001b115010120a000e00144035480240303c1d030020b90150b1401004165003503410310081e030300040c10400103181401d000304d40200300001440c1c0000400304205000155000c40700400c500540300005110105901183d91442020b1145000348503001d180d9400803070501560342001c0410240d0010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 752034667 1250 752033417 752033453
    0x41a0603070c03050c03030705030a050708091b0a030507060e0a0605040503151801050a0e0708061603110f0a02030405041b080606090a1e03030305070c030504140a08031201031b050d 80
    0x42400201c1880004000850145019489542c1c492402f03072882401e40c4c0c4020120030410401d032060200303a1400040030301c2e000e03074056800c00050382071901181303403140186e0000d0414811003e00241c410340100717450703004c0e6009880b0308a0040c1c6600c000d4138984524400c940d0143d000800f0f070485608190681500001150b02160000700d000100f1400d4410903503c0c003804070342c0c929078241201d4081182030b00902000707003c1c007401d1030007020810596a25282c0c410501d900d40041840040b009000c0340c0d007050552800300d8880c101c801000359207402078024240550f1500b10000780e20303844140300501202150b582c01c2d207140d0740c02050107a07130b4010003c19a0020405540411118400058185c03410103580313010307504c01e1a40c1401010380e480039001106000022840e00c000c00d40c020104d406540d802542d4142c07030320000c40401c940002591112040e0300010a110740d500300c4081d050760480740030300c1051025008000019468903803512a40703510400a0301d030980051705009a048003001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 752035917 1250 752034667 752034677
    0x150112020f210603010c09050607050a1709130612030e2205060405060906060d0b0a0e010909060509161403100203040b010303110d090303230c010209041a0603070c03 73
    0x6081c0004019800070300180004007605080682403100000c01241e11081c200d00078000742c1c0c11518054070659060007868010340c0c0c00500801446010803031030380d489502c11102c050442800400b281c0d20307042107048502c200c1803840000e425032403c0c0602800d41c1c10400040500055070764080d40e03d403620a90392031300f091210220880c41d01d040480c0742c0050b6444880802e8034a00708080208843c0000d003094070403c505c80c18084c0d0f0f0f46400041c3c41900412900025100f13001c02c0010340d444046500481c690140c501c000710b03010a080d00011026485507500340002d8a0f809062078541d010320150315440088100308114018000300740518040c40582a529818152004681644c2c41110b06a99003203506004200701030b80588418500c041c2240901015920030340003c200c031000e03100107410880490b50306034007041400b04000c813003043c0b5400c0070780e50401000c0d4130303010b07401000c2800d120b980380803450054020100c4500701200c80007441c80d803440da2050300c01e5444441009081c0c04000c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 752037167 1250 752035917 752035927
    0x30c0108070c02121f06120b07110c090a1a03010b100c060605060d151d0a0902220c0e030c06030106050c121210091803121e0b0a050915011202 63
    0x541c09000301e1201d042008549045ea00300400c144c0140e0702c1c05d9000f0403600d461640341a0108000059403504460980303040440390620382c016600d0800300d195600c0d0f2120000d0103001d85003601340c0c0300103042d8030320800550503c10102c0415080b910a841215001203042c2140d1078280d00c5950030015851040c400064504c0d00c0f400843c0300d9800180d0035020551f680c0c120403241100e80a030480041144005581c41c80d80208000c182128019020340480382d1581034403400c40d980d0b102d814680303070743c0c1403101500b0108481c0361001400d40c1c680340a0126440d03400000c56400c0200701e60300c481c0b0018001629591800408880e1a8011811003065001e1000b914086610b5100180070b8003070b440350b450046041808403040d207507055500101085180164900c1c2103081e0002d10000b03070390942411004c0e685140c068101a210031205203810503d22021203559419641c000d44034402c0945034a108651a04107010400c002900c881090f030400c901704c22410b40c442c0504070002d03081640b0140c104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 752038417 1250 752037167 752037199
    0x101401121109034312060506190b19020c06030405030705010b0a060c0222060f03060605040209090a05130b01140111011a060f07050601080a03030b030c0108070c02 72
    0x118030703001e100320701c1010006400030719140030011002120011070a041e1021105141c80c3c410b00413030f40404003a8809510000d4103030115500002c010450701041c50800c00c0306252880c010030080b200203120310b00a80b507200c002500c0707a442801380c1e201c1036140c5146c240300f00d000c2a80c419450b41540c1c1107108040300341d005034a80d440a18040c500ca40011904c41044bc5045e0307096610340d00d9194012a40d0250070400c3c2039018407030300d0a00d501980c4040c0c0c88184001d030f4041c812840d07242c440b102402c1c6400000c860215203101c00882e405480d040020742d844c3c804103c240e2003404080381d80440540b010590585135544102d400040a03214103032181035540d981c4035420000d034000c04041c00494001d45c0a540c2094086815042040007008240c5030200d1040e40c6004000302c8600a90000c43e030743d52508048412a49900d4100084130090341c0e49540711503694a411000320006070600290f142203080004401e048264161503031410b03507444503011241c10f011124280d9026207030000030450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 752039667 1250 752038417 752038421
    0x40807080303100e040f060f0b0405011502011103011406130518010305010c0809100c051e071203180f020409024f0c02071d0414010510140112 63
    0x14803648016544a14103403207052001c2e601903104c2d0074610200d20400c00007403802d180c0c948416900031400076010400c000e265005045169555410520700000480c102c2d00350a4031158452285d4000c0c05a1955025035800c940820b00c5030400c8070358150118900d51501030b024000100c0003107610b0a100d40d82e0400545c413000300360b41c0310344514202c00041c001e000c0207024038410300045050a034080d0a12950303140d5500c031407200303242d0102c0e0b9516031303582c11520400464001040348010840900074100da000502d90007400219802c02201c20026220b50003400745103100d00d101c2c02c03c02c8440d821500c800b80348021400049074810755414503400140c2d0307a80c1039030004100d080000203000380c80c00d407100c14502002c1c108a0011208404a81084c210094a00c850074000c0c41c1c00b207040261040260b190241c140c02110903600341034000280ba040c5010442d10440c024401c02c00611000000c540c229a81500d41e95008403000302c0a111500103011121b081034810326001240c54191088001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 752040917 1250 752039667 752039669
    0x1e12110f2b090602040e010603420816050d0309030314091806040c0c26040e0c0a090504110313020a080706020c090708070818011b081603020f0405090606040807 71
    0x5001383d0118051111b444480d100711701514003400c0803c44107001d0422801d40b400d925000a0005401020825800c01c0801c09054840794882120078240d44405a06441d1000c402c48180400d903513039000111450464001c1307001c20303056240c0402c0503045850440f0100d032280d4450030b262104001390402c94858215600582203041c15600003400d1101c20001901d11103420300c001c12034140e0f8880f001c10f10150582610341da000040440308424100c2d0340849000b00d900c00c2402c0b0081d4800c0003034548003d4003c0000410325038403034513410740324810081240c584110082c0c8202d001d000003481a44115908212107000030032003c6121340d00c9481074909412034000c10010380000b01e1103901805d20702c03842c0d500000a07003044029441c01c541d0051141c04000e10f07018003910003826041940c0700c2917210a040309121001c0003c40c0c0c7c1c2c1c1d0140a4044441a2100d605180d90381c0340f000a0a1310906c291540d050940c07440f031b8646460f04007088960003010b0281c80c5d1140c010000001d80c0402080004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 752042167 1250 752040917 752040923
    0x4090f30031a04050c180307030f0f0c0b0f18031e0c090109180b130606090b120708032208030304061e27031e12110f2b09 54
    0xb0516151030340b54904104002c0042c80d01960601050105251056090300d0720040c2c00540d05040160600c0041d01d80500f6510140070b0703240188085052050000481c82d00c1d50142c000d080860f640c402d102c01803441000d405d5901100305125020740e4078400b50048100c40c0e03008044500b020300c00b207060b406101004210204990165030f0084440c18102003150040c002c050041180c40c052014441c892030400c100100001c5800000845196001c0c50425180350080000c204103621031040030010205450824442c1216054141c40c009000890400390380401001d542840d207960012580350710301c0e07110035111400348040411443c01c2080a9403140d030042d040401e100c200d58a41b8080e4212039402d42d070310603050880304218101001c040c010801c0149074483da50401d00d0604a94070706110408503103200030060050303101daa0110903d04041903007841007140e0302d41a69502014840d22071a030701c806070180040344011030f1403400308101c0c1d600307070404514000049081c032089820882040f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 752043417 1250 752042167 752042171
    0x60d0b0f090d02010209060d020304080f0403050307060b19030b060f1305071e0e0603150d12030b0402040806060d0201021e0607030b04050112020910090e011a04090f3003 75
    0x30400601c00c00c071064202925000851030038071144007040407440303503520411400703400201003010020880c00704c1d8132085d94800100e448507100c0c034242d0b032654482c3e04142d484a04009030896185040841c4524200c201454881d8030383c915914018603000041050b40c1c030001c0044d0321241034981a00585168540325400525840e240e0030140241d0b0203074803120150b0380c51200844215800103402903400c401221401c1c1c89a94a04051190051504100342c12166500c411405c00c2420501c0c040203000c41d40301031040f0302c03485e806e0200300e00451041c0045544402c001c01c04a061041d0f640c8420340c018410b0303c680c61814003541c0028400c1003c00c00b20f0303900c8041041f00c000d51620130701042d103604850600082d450043d0519a10306541c501922640e1401c02041c03851200d403020400501c0001414400c494000552900808105800002801c1c91900b4a1b03041d1400f8440e64178000d5001058848072001c9803a160720100b010100340300c0c070242100a078624514802d800403081c103915540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 752044667 1250 752043417 752043421
    0x1404050c09210615010c030e03031c0902010e040506060706020c1203100f0506070b16030e010e01061403010501030b071b06060f081606021902030a0f140708120702040203060d0b0f 79
    0x206072410b43c004060004210456501100c0382e82d006181943d02a00f524101c0054801280040d0840c03080101c2000200301010744004c0c804429001003450b0350003621350780700050300c00c0f0a100c02c0c1c59084801c154070510400ca01000988144d018046402c248400c0b120580070282c0d01c7d40071a403068035000c0c00007000850800402c3c905544030005460140ea90070301707040443c0d8a030010020054880c2064031014440c01030058403070707404100000d16400c000e010701606440c40b40e0080c00c807801042c0d0000d1071007106601a08050007420b04990b44009060783e1130f030f24180110788520540368031185030404c0301348801c0802c1e194001c90014001d5668800885481c001c841e40c41c2c102800d40111200c05120300c2001910b070042091130400d0790014410121036450702c00241416101400141130103d0100c030350003840350000710200c074101035508035545ca0b6145c08903281da5503195100700c42c0500c4104060001420aa00519000b46c40170300f4200a82c06240d0b2284c0101e2802ca0303081d0358262103842 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 752045917 1250 752044667 752044729
    0x905090c0a120b04170c0607031b0309020f01050901090305070b0306210607080a020705060c040501030606020a05030405010e0a0e0f0f07090e0f04080412110102070f1404050c09 78
    0xc141004011490011034026141c0d600c4840020303000b8400342080803505c0060001008580458070440c0c0c2002c03d985d11494101c0002c0c0c000c8c0000c03003c2c41000213020404444484c080c0c866038090b903400500f61100c2286071300044541e9070101140c00d041205c04032000000680c00c01c16200a440d25030300b4240c491a0010500604059800000b405050000400c0040c00808a02c013038000c05107181407040c550310700c442180640f085100080451054408015070319064034058801e44009076400d00c4999a1614100c0c2d85042150f00a4001c0d042000700704410360240c039a1100390040039002240f21a507a01190203441000c46107135500f928081c0800c52035a00c186c0c1959031040140c2803030440f0340d0424106480e2184010a403d03091202140402d05028289007603030300a00340354056030b000410514181c0c07011107403016441e0240c880c400003c104411107100800980f44010107124050303010400300030151402400b49800c403502003105044980b9007011800d00004030303503240480343d20a10 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 752047167 1250 752045917 752045929
    0xc071205061b0a030c11070909050f060108100515090c030403092103050c0313030f0302010614060904020d0f0c030e0606040c2016151d011211040905090c 68
    0x82c80c911096554181c240b2004a4000c2503a95030400740c40d000540c1e400c00e2070107551030801361000032030703503c0341c10000504060a508140e0109d440707242600c0240c0d131000113040c1d403540c0a0081610304d400c29445000505029440a42e214070b08146441c45507008a003c504038010907592881c05000c000204000d25400017031810003000c400300c52a0b8072149000424000f8441041d0082c1040400075902d94903803001c0041d15000d5404801408400743d892405202c00b112050301240507500f0014002401c1d46284150081c000010f01020b01e04402c00e4200402540001c0e010802c1e5a80c8080007015a16148211560f888503504c000400c03100d40203109140c400010031440c030031800e168034000e0b00c99001040c96401610200d540c03405240000c0f8030b0b4204016252104000008200005410f25a106c1b2041c02d40145458443c2c1206500c840d002800c04003201c424042818034408003e616000c2c0d0000d035a04100305503403802d0580f15015071042e200107480240459204074004040c0786000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 752048417 1250 752047167 752047171
    0x30f0e010207140d14030f070b07050304052107140606120109020d020d0206040b0309031207020604050c011d0405040804080607020a11090705040902070c0e091f0e030c07120506 78
    0x1d000a08459180a908011070400390100500a8101c10341807420010103400b481040c5804800380c9445101134a03029110350450042030f2400b141c52070100d21158042d6003200d004503009000790040100c0f001c101c0d18401802d0b0701400e0309a2017005420003003a8003156500628010901503c85030400104000101000001e001540e9141c40300707400050761450024044940e05580d0504030024900025050380165802416500c0000042007080800400148000064040484410f8840d00012a03854108840050041d0b12059a0406560080101095405030403110b440701520a1010030182c59080d42d003124104800302302800000310500c02640d11007850310003030001c0d11480d11405603e1044001d03050041c0c1a140102c0e200500c60401c1b10080c1c40207103800d5640e0400e601c2c00010041003445000a034101413000705149803030114140b00b0704905052645083c3d00254000c0d401000c080d500c04006104c10081d00a101405210b0a0010000e401c200c0c0015038080c10558101400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 752049667 1250 752048417 752048419
    0x115030201120e070519051003060513060320040e0a0b010320010f050a05040e1806070503071202030a18030f090905040f080915180102070b07050a1e060603030f0e 72
    0x3c2483c400402c290004031442141e000f100d281c0c220380842284841411003642090780c000701c6c4c4041510b40290103402c070030100c400903100040d00f0b2982107420011101a400002c000810044500901c40e58181c801ea02648005000140110030300d20581e10304031421008503176911400004005214420300c03c001300c41c03003c950484150400e040000e189110606100041c008041401e05503d4440c400b82d502802e100c0c0810790f402d003042c402c010b01d0126143e883d00042d100e407500180b4120310401c00c0d64010083c80d201c00c5082516081a00d029420060843da4a0703a42c81840b00203c400007041029100e00a486003050a00345c3c41c0c005100000c15041025203d0605060000080840c0c00d500102034000c440c4a0320f402c030100024050642070349045803203040100b0110f103902102004600614000d030200c1d002c3c142da40704010703080d00403103002425941000380c0e484081075030f00ea01c404416000b0412002c4842a90741c074081201c0d2542c2059000496280c035000c1000d400c600b1598034030310 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 752050917 1250 752049667 752049671
    0x1020c060f0a031104330f08280504020301180b07050708071a04030207080601050f040203150307030302030919050a1205030c0d0c06060803031603020a090306020c0a170c03091011011503020112 85
    0x1004040247c44a1802c0c02e074801001000c5001500c01084600c0200c8481c44201094940804040003000500713000d45040e0301c02c2d460306a0000454480b5908603001c2580041c2080e034550b2018002e44041d0010082a03400c0c01c1d041105c40c0010b40742600031540a00c800441c00c5150a1130304000307240c07a0346604031201590140d00140480d40e03840012119028044501681c0e943d5454a00c0249002070110143c05109048021040540200c080c106618042d50710070081c420318400300306a0041da00c55a070700880f41e4602844110040a49030b11483d00600461386400c001103080c0d4034203c0c01d10750100000e811160100208022405510001e1103d04025070850400351712034800e01d8044082c010074554005100324149016400307150003035400513001c6460b039010403003035516041042c400311032560f8400181003076501000142c5071402091001542408100d4040c0884092100d0441c4c0a0000509424450381710034000c1844003640b410800080380d1a40c8000f400342c0e00056250301401d4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 752052167 1250 752050917 752051009
    0x309061611030c100b0604080a120c02040e0a0302010c140904090804030f0f0b060901030b070f091205150105010915050c100204090c0e012606061608030702060601020c060f0a031104 80
    0x108c80050a64449078124002c84450205414161500d190002e0000c1d0032a003004420703c0106008a4078680132406034009004c000c4654a003102c07011650350030340205900078400480d040c1050361281d0542440340b85114500780e100e071224010115121402c40700803030200fa001d0104444c2d040c140c0d80007007041c2d030840815411552042d200000041540c81009822141149860310450b100b00c010000300d01c03035105214040c01e202c0e843d9008a0079a070342e0b0345c11b10b20000481c0e500c1003c4081c101c44050211000c94004004125040d40c031030203800840f8401c40040031483c07840da00c000d10013844283d400160f03501c00d442010301141040240b081c14410081040207843c4101041c04102d40e0314510b15880c03650781c0e4000036800b40036500441356101014141f0504114a0000540c05080b0a80803201340b5135580c0c3c01281d90341440c2c4081d9400c6141809a9100949079001a000c004441c0c2004103000009810455103900103034000c0b00c440e00b880c0e698103040252800d11142d148030740c085448001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 752053417 1250 752052167 752052179
    0x516091b0c0204020306130f0c1e050f0c010609180b090a0b191d0307230a060b04020d090305040513050c1b030705030316140309061611030c100b0604 66
    0x19000c010301c042d00882d00000041d41c01d40d120896040c002c103204408010092019212400801d000b00424005c10750b13105d43d10500c61419180e00030401e503d81c0d907051a205da0003d0101e0517401003201641d084d0340b12480440c03000b40900803075040c0c03110000440400e402900700b40623509006458080036802c45d0003100041a6840c62440c0c0c0032440400030400e099040c003511000301180044030700001c9400e16a408821000310041060134080d01c0031070011544c200380c0c2c0492041c401100c0f41e250f0700045171580000e40f2a0800c0b40847d0000700018100503d200c415001c1e101c4280c803c031300250000800b0304c414901481c00034041c2d0141441000b45180003485402d8074410380e916202d007401011609028240100308448803da40001902e880741001c0702c40c10031304103200c100c1c4c0340410b0101c3c46029500a46c00e05403445209404020481a240d0702c04400744207060050305030801c110610400c0c1c030080c00300001c0454001040040c1011102c03242c0120488000c00300300391080104000401403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 752054667 1250 752053417 752053427
    0x204181e03032a0e0a090501031a0f0f0a0c2f011d15040204061a0304050714180903090a06051308070501020d2d0e13020a0903110d0516091b 62
    0x3c0106007050070340b408403c800900640760540c0016503481c101300012041240c0f403481c480010750f1524032600d840d180c0350140c40210100300d4160030600064800207203c8001a01322540c41d00c2a41007a5610303990350640c3c1d4412641c4044400221030300d54900140780882480f03082900c0408240b406401000d007c0c5840d01c072440c0000c862518500a4081030540d0b46a80c801d80c02891080b80c00c420351016a40d001d8030a4100f120251180c1c000e00c80000303008060b06030020483e407801040c24000301000a800e10301c1510103460310303e10788010b000140d1207440304804940a41540d441e00b90325160b409044016011483d0071480c02900132403400c1140d640c0000b2004003500ba0ba01301840038142e0100390410383d00c460710b440c25405600c001014000c40d01302e218a03c03210000d6070040e8403a5692105030088e03201c0c4040000000340c1c21602040803c241c88100c9202c50b400501551816803aa161646010302c102d0f0400d01c0794807895010042000144030310305c450340d000b05002c003450945540c007402d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 752055917 1250 752054667 752054741
    0x506090906162a051b0411040b0d06030b0a09050f030a021c0e100903050610030803070c08070f1a0f09070612090215031e10030204181e0303 62
    0x10034490081c180c0c00c1900d014140702c3c0000310f41030000341c007610014180182d6400d4007070800d201035004007240d00f000e800c00d80540c088200045020030718003440c040e03c4050b030b0350107020103500da651350741710210002d0b0040030050f00420340408081040703072240c1404d506251001202c840d01e0792007040700300982600490b001303048201e01c440b100607025024906031600c021010603a9480f14080c44036404072600422088250b0b4010000c5507000d5403800d40c035084083d02c500002e0451141840004c0b00e003032203802c40c03403e85803240b13024904000e025615a6510703000c00d2011180d02c1901c4288040c01d0380c1105600c3c1d48111660413055480c100100036548074610b5006800401502181c50041203040e90490301d0125406000040401541e50340c04005030019226001d00d0400c0000a50b128040c1c450128010064914514001407540c0e08000041ca01140c282601c0352906110b040403e550041044224010282c8421402e00e10f1400604481c0c0754a003e4005090340507140c0109c0409085c404 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 752057167 1250 752055917 752055961
    0x9030c030a0b07051b070305060a0501060c031422080318031513080f070303060f09060b0909071404091b110a030804260c07090612110402040b0406030506090906 71
    0x244e034941903817081490117004403022a406100e012400410480005911489850700719004c00c42c0c0e903200c1e58119a42c2c1e05112019000031443c3c20ba030020140c4901c001d0160098a86003ca69004c90410756083e40322558813a582582000c21460650078011242ca5201d00080f0080d200e082c1e01c40c68244442c0c00702410007807440e000107221104001030441103440982000c1e00305500da000c540b8006018010a0140c5020b81c81c140c0c400154003a030502138501038481007402241001c4204082c00789460004196800308507a050810b000c014450000300040c0c150400b0100c0c01c44141040c203c0e03da20104481001c008045203007800c03507400854030188541c1d041c9040c04160b140c41c10815800c1403155003680c620700280010300412061300000f404400305510503507481d40e0307841a4010071540309118010054540e00c8002c40001da55844032100120300820060605440301c01c441c0068000b034100c00082691142808410300d010000e895014154500501c041c2c90160508054180881c041e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 752058417 1250 752057167 752057177
    0x60e06070609050102040909200f151321112209210903031704050c060a05120103080306011b0302030d0b01030b04111b0304050f0d02011107090209030c030a0b07 71
    0x848100701c801c5d01242c004103183d801c103004012250900202c030f4a5954a001025600e1421000035810704400640411000a100c4860010f5102058207540c0c00302030700851180c00341c1e90101d0405005031500603486611000145444102e24080b0706441400d01d41a11507100650070f03510101c030700034090758104044100401e00c550145415050313044400c103580d445011500c41d5032040d80d413016039001124001e81c2c94144040d141090b10310060410368000d005a00201022952400c014000f00700c40510707071901c40c1c50207030304000f403000d112004c1e00229410303200041070001a40e0321071b070107440c1d0100c940c1c2d0b0f01e01c2510b0a0b41e8080d41d80d114101030718040f01d80b100010307031450b070290340301c00040c100c00741c02031144101000c09810706601c0412600c1640c1c004d4a030500540d040001942e043c0c0c0c802404c04600001d505080240d1400310200407410001c05110500c404d59050140e100182126200075131500440310800d0f01300708458138254044c0e40008940c2001c5102c061019402403907034100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 752059667 1250 752058417 752058431
    0xa0f15050403172b0506040f0203060619120c030b100f020705040507091e081606020c1522060e030d020312060f1c02130c020d030c0504090e031201060e060706 70
    0x12038446101d0450010202074186070a00c804d400c55030b040503114050440b4100f03c0e10401d070340326504a010a460361030300844203000c1c82d8042c3c000e180310314107070426a013821065900051041c0381564000643e9400080d110006c05482d8148030b03040741c40440403420b1107021203244800c000c3d5200c80510aa92096884001250605000f0303501800038100010078001d4408501c0243d60301c03030040e441040c1c91032051404d100d0b000605450f103501960300560140079801d240e002040041e0030b2442005144080403c855441600d42150f001d50708140f018994207003624104c2c001e09102d01040803640250003084106d9003090313010086428202d41c06140c01d1403034440e440030070201d003901c05000d5008040300701c20104500a100e40719004910860b2611034641d042c000c034005407100a0f0b88580507a02001c111007106020390040000340c00f40d44ac0031410655903140c5581a00d012041c0c40341907400c00202440203000101c1c000340034006904000b001c0b41540f42c00304546100e24039020740300380c1e03407841 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 752060917 1250 752059667 752059687
    0x31107030c03080a240503150c1602040209040c020c19150324060c140703020d0b090a0215070605090f03040303050d02070501020a09150e0105030a02180a0f1505040317 74
    0x10054100300d01c41d14645290105c1708543d020381294900860b4030070312a0140104005940000b0702e4815540d04415600348080040411046e522140b41280d1140d003d0109078260380340c602c14190001c1c1c6540c02861482404424030048403c0c200680d420082041c10070300501c03641c881c03c103096500b42d290000f0703000c1e080c402c0d04802d4441001c920501c40c6042e24002000d55225501c54081d40c0038402e05040b40170021001a0388001c10300c4020740201000742d0720000701d000c0e405030b180e00c80711070020703111020090390009400000d00501601c400c40041011f40a1200d10f11071a03a102811030014841c030009455101e5072801288002010401e00088c0550700b80f013580c052720f14156104000b591a244c1144028242c4140c0303000d02180440d00d2100b100305984202507001403880180c440324078580320641004080e50068504c000b2151803c04420700c681c454500b01802440800010020b00d41400010005800103031680402c00900303000610201303001401c0c1c15071800b400c50107142c0d10042c0d14 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 752062167 1250 752060917 752060921
    0xd0f1a0f0127170a0210030903110a080a020c030304081b1f120b041407121107060902042313060e01050406060f05012c01110a03030c031107030c03080a 67
    0x300e107240142030489030001101c4402c204402c00c0d607100050810005203980c03070065807a024500040d603c280440c0b0302900c0b4900175840f0014580c0a4a01031441ca0351402d04a072070310f500001c0c1114004000030300341c105143d0500a842411030100d010398641490201030641e2902d60083c0030351400010f40b05900b040e511820401e070402901e100640950340c020700f01800c50100c80050740142d600f004030540c500d1800344038070540720504030000b88117a21b6902003281d0509112908080280d03a0303514080a01c1c1d54880940141c510441c40400d03103820510520003a0380052050031800c0c43da0101d050440c04070141079607800001c06001016802042c108140540025a05003625521300300c1484180702c4507800100582e103006116038a05a510b40c011030302d03c24024803809884880d99000000301d54440f00741030140205150184440c2400d02203181800044134085000ca40d444040d500b242c3c1e0540a18246264540da04500b868103c2d180a030811101c008020704000a5400089542d1559 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 752063417 1250 752062167 752062187
    0x712020d0611091804050c101b02010201060503101d0726151504060803130506071121120703050f0a0903080412030806060a020c06030405120d020d0f1a0f01 69
    0x1403805000401c904041110080185c400703503071502800c0c0100c000360421340403140f4000801d036034901040d821008821600410b02008078119522000001201c0c0d800300a00002c043c0d003000c00003171540202d0943e40e5030500301c420580403900502d4042106a2085140d1176182c6000c01c2c0403030700c030704840400d80e080100010705141e03800101c206020000c000050b400c10b002509403030030042c003502d460b682a41c900480a80003001005900d040c0024200880540b000034405c000300c4545000134000503500445102415a24200340c04001c2c060740700811112034140300d120304442c6841801e071002000c5119401003848821400109541c1140c8601c0f0560020b60708004245d44568407510110014840b40005900088658011070000d140801c00c4541a840e103030010020320400005120301034000410507110790240b4005001842004d1008208210740103500581c0c4522140b104401c4404850080380924540a1250f8040d000e00e4581160380c842291402002280140104c40200ca8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 752064667 1250 752063417 752063419
    0x7120305121506130303022b0e0607050150180d050a030609060b1605030d1107140a030e040509070306020c060405010b031507082e0302030712020d061109 68
    0x141045030302c4c0fa5008404142c038802e07801d5401424000c42a0490a080580c0c280a151100c031390161b0703040c0c0103084520361068050441360408100341c40d1142118a8540c0d5040d84024951041c035009e0000100002c20711880400103901005815400c0c2410301d84480040f661030000f804541d016100007000d15045403400110b034840d005a24005001c0c3d000b00780001c001c01d040010100b0904640d0140800f40c6500d101d88030300304409803050740507001040c40e003540c05010400084480082d9400f40c2c9120241710724031180d4620ba00d14003143c00211030307030b110021504145401000a0740c04948490191000c6402068680740d40c00c00074141000e5501c000c00c1c3c070f480010100c6d280f07580031503140d1007940120b000f0030040d60b12400f41030711228000141030540001e080041d078640d0180014075040201000701018100811310224005940340840766180300c41074808004600d8108030400150225404030616015294049811132480104c001c104030341320010f5034003152440c019241007841c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 752065917 1250 752064667 752064679
    0x19030903080d0b151206060703110f16090507020309010f090810061701020301080a080d0617030c0607110717280605091b0f0d02040203070306050102071203051215 72
    0x100c030300b0010003d0100c00c02c1035005604841c1845050600e070425100b200f1294038024403186c0d01c140030020254010314045040c480900081d00ca800340410000d19451240c4000700b080521035001e8a05114907a8031103800c071400c103001c1100c010b60100940791248000c1c01c1c209640c20818400b0b40d60180b15800100040c459107021036101400c80d00880212100751000e40000c6258601103402d0b84002d0282c0c100c540d00070780c011800204c6800003481c10b21241000002d400ba118060784489c114200d00385015a80041000c00350420148a165000150340c14100f601c0d600030800142c840f0880e108a01e10500010000b10316a00c06002c0d018540d8400f01ca4400d80b61080d06084c0c220022a00c002c0d0b88152070040010034000002400148040c20a41c6580c0e200c404101007150076050700b842c003a0482140580080140c9445c0051406104262800706e162420800028500380d2107a103d50303034500c148408200800d030001c088a40090f1180b582d19803d40e16107044a21041c1041012030f0006 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 752067167 1250 752065917 752065927
    0x1303121103191b050d080405033a060f05010518090a020c100510050603090a0f080306041104230a030c1e050402070c060503150301021b1e1903090308 66
    0x1a04403602d42000c0316203601d46464000703214028225040715001d006220b43e000340b0400780c04034002c2807103035071140c07007103044174600f41205035002d040d00c8a2040c0d060700d88103003101220111101d089a00d00c401d1358101708000540c6407080c080120341a6114190501000040320080d0090350340c3c400041007400b62081d0500d00700410f23000d000f0342c0010035040150041300000d0307050700814003403a40140c41e803c208164090030807040001c164009000000580318014a0f0000148160900c074100e0b409a24215103e1402909200644042920600c805c2030100400d1043c501c192a100c0305410741e4030301800511711064040380d80ca405640000e0000620b008000078030b9000984200f100045100640607055079503000d01040c0d0080003801005503004100a02215200c0d2000c0d41d4001443c0c250021900300340c0c0046403c83e48284140b01c001c81c402c0d80c131051407810030010304080c201c824408050380d01c442240d0a441d01107800600102c820045011800c0c9442013050b580559000040c460f554 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 752068417 1250 752067167 752067187
    0x32901060e06090d0f02040e0615060f1c090501050601170f04170c070303090905010302060a0c0203072106050610020d0c030c020a32010507030305130f0b0108010509031303121103 79
    0x1c5c0b01c20303501281300b02d041c008120f880c0e19010071118002c5440780801d080a02d0800100709890300500c0711101e16100c01d0000340b8900001124981154250800000c1c1c0f0b0421070030202e0940c0c070b00401c40b138148000441224280c410785030300b0702e0748403030200902c202a8480c1d00e40341c54004480710442030010008071350840701140c0070418030112846500c9001e1000c2d81e80d6600c0d03055680134132001c1d50143c01448a512158000d044000a0a10040c280c400f00358449040503580c0400001441043d5407898400e02002140c0c0301d030b990010021145032100214590307000b5650404005080100120030503071001301405111080c94840d80108880700e8681c89011641808030702507105030100c090456400c1444642c5014040f00c030310103a5070289001007646040e0007034080079022001128000b0802d00102e000c04406d43c1505100d01c0b1480038551410a40c107095a50180000c1f500c1e030400c002d5000c0104601841c03004495100c1d0151010015801c030680340100d08155035645030100180c503442e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 752069667 1250 752068417 752068433
    0x91509030a030f0f0e060d05071218030801081b0d0302030d050f0708100b0301230d031e0512042307030c5303070507032901060e06090d 60
    0x20710060341c0d030340c44040009213008032640414010626040f5108202e046040000e84d001a584140326050004c0098a000b01c0103040724500c501d003440c40c03900100c08030300301a0b200042c0c82c010046c4400514a1251103800342d10a004a0701e003403441403a030150f10340d04050080c01622420306100d1001c002500c0c000342d810300d140504680c03035400210000e00054a40001c80d100e14256100c1c030341941d00350b80c00c001801c040c0d40c540c42200e001c81c2000e034558004580e91425a02c034818445d035200d020101c000305040030400031274130006041c040244101030307042c16400d0403240d100b50000d2116408a02103419100d0120105001d9100b500400c10040f0a0103c01d11401d821954542810002c2250101c0400401c40803800b900c644a41c00f851650200d010140030f9686035803071441c0c8a00c10a19230f00405143d03920088040720319420111041061004e076050481c001c4030800880310301c440b141340c1068030000b4140030703070424400004004d82140d00e804061380c0900d6405024035102e502c4070704011070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 752070917 1250 752069667 752069687
    0xa0602030c13080f060f3615240105162607030c02040b03120c2104031a101511010b011b11190b1b0111091509030a03 52
    0x1000c501d040009841403000501c940c413030001c10041c0030240c442d0302e0001c550340d60103010009000413484c9801e100000b280142507880700010038402004240510b10b506043c290400c0622524007041040600d075031841c08240d1413580c0340b0303440c000300c111800165a14041d44082d20b082290084c5a002000b072107808028080c0c0c40d8400411480d80c01c0380510355140306140000300000c0c00d4003218401410301e600102c0410310003d056640111030801840c1294000100a41c0b2070341c0007100801c41901900c0d1610080b40034018440d00c1e043c1580c480700c450030340780140425003ca412000901c0c001169a01c5009001c000d103c7d0210380c1d8070b0000c01088429030041900c80d9500c0e01c1c010344429800b803140c2c100b80099160800c101183c01e510384a0301c200a080000380c0001c03200b502c1160b2030040c54006000303003140d09505512503451807403148050317900b01e5035100668504018540e003050380000b034848502d0111800f410000600c000340b540c82c01358030103090300351055140070b504064114072151 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 752072167 1250 752070917 752070937
    0x403050307441003021c0503031f05010e1f03060f0602030a0305010e0114010f020f01020d14060301060f30050c1c0b01050d08160803160509060f0c0a0602030c 70
    0x1070700151182900b10056901a2081618280703607803400c00050410761003440307098160b004003074072000003502e40c1425a801200d06581c005004010327070340c00f40313203810b49600900003c0c645001490500d2700070030a0440032641000280c4050300100910922a80041014040200011400950715100a5600d40000c0c00c0307070010074106400842d0035078a0000250403a02c00d4011701203003459107801591040c8105101d48110702070b41000c0d2001d103000340003c208040d00400300003030b03a00c41d038100301c21850390183c501c6110340d0503c58100070700c0a443c54403905869640e20940394800401d1000d140d821800d44840e8441c00c2040400f5050020204042e41c0e40b08065035440c104c20b40d0004402007082001400070036140082d4010f000d107040c02c1402080d441d100303c1090f4a40702050800711543d0718500b00498540e2000020001c8001c0401c8803010010000d00340141011850720015189005401035452058404980c0c050740c44c50030024a103170940c220008543c3da0030039401000c820b92010f0b07195 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 752073417 1250 752072167 752072267
    0x24030706091706160c050a08030c1803030c100e0c0405160807140f09060f0c011a0109030c0e0c070816060612110d110303040b0d0b10080403050307 65
    0x201e003201d030b003c80e0706489048031140310040d030021044142c480d803c5c01c00e029a01881100400300005020300025400303200760301601515115204100c65030b485030b03a0141c1d4002d800510410f070040d200000c1400008500341c002107010225285c1007460b0981e10850240e0060600080c4003002041183d2141450050754440030652740b041340686440402d0000311109075001c01404500103800005403203181d100038091307464542c1311458400207801020008281c0c0e596414070311410300c0d03880072100c20084282400d012082c9580c444840302249840342e01c207407400003000250103a01c00c000b2500c1180c0c0c044c011507216081c540203400c001da0204003c031031040c6090703008580e040300c5800d42d0227078a0b8401c0d001d48021402006110801c1481c68007291000c09203551580305076001d00c013071701c090302d00c04084580311480300d004d500076204400f00c0c181c09407120a40b02402345600c81d504c56030040e010704200d95a1f40f00d170740041702d4000d16040b014411000f0110204c04200c0b90940c8070211500c030703000c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 752074667 1250 752073417 752073449
    0x4050414010c091a041a03060301061a030f071418040e0102040807060806190902071410200a05030414030d050106081905010803041e05182d2403070609 67
    0x944100e403141c0d00500e0040c0309810406c03104120741e1030003507910440150011418603036a240c42011016000440c0000e0380c030110400c0141c0c03040150603a80f014181c0341048880c3c0c21113200c0b00359407144035001000039030302010702081501c96400c1800207140c0e02000315901c503613440206031104500c2c041c04000500c2003022403a035240c00110b20000300034440d4250041da2500241c00020b40c020f800032580901e40106e80b00c0c07510428082200c0c48500440003045400d15104030503c80780707100c200850001c00601c1b9041855901c68140c0c0d52003584842c3c9480303d0035440d401c0c1442c0d80a486800009039007084008121141d000c5030382c5005445003a130f81d000c1404040f85100943d0424001c1e800164014401005402000d42003000d8480c120841044000c5c0c50310302142101c00c03245031041da041004010700009001884000c56015032802c1c90506014036480b8000122401820203203007e400340d40b0740100407500303104e5003e081c1001030481d07529a1303623048054090744080c40b4031804034180e111 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 752075917 1250 752074667 752074709
    0x1321030207150f0f0e19050a080321072304050f01020c013513021f02070303030911040e060a0b031b04020c19080903010b010f0e04050414010c09 64
    0x20b120b002082c0e5440d2030809050080c412128042021101c0701007250031121050661201020961007203060b0751943e102c58206000e2090203885c2c2d500036031030b944c8100210342c0c440601d15844810720083c00b5462050751900101250400611075000701c00d03044140c1e4403145803210800070301c1165000d948001d0360104007401642c545a002d0816400f05111211070303a0b0794003e000016640300b5120010205216840c05500d070304a404407402c00708032501150620543c6407800e1800c0c581411551801c10008074618004e40b181300c284001000c5c1611001c0800c10440da01c00210040d9a0180c010098406141070641d521402a24000206442c1040902a5060104e1003201e000c11446031803000b020302c5800d1000039030001100244a0041b6840c0c10000340b41510741d109000c0c05101a00c1e103564400741010300b10f44c1c4080c82c080c14806180c512150071a0480e1010345141c00489002400b592241082c902400c08014114140e500e00403501f100c182d003111103070042d25010990403900580c152 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 752077167 1250 752075917 752075939
    0x803071205040b0306040b1314090705150a050f070206030916050f1509030102090904050a06060602010c1b15050c040e0a090f0209040c080a0b040510201321030207 72
    0x1c09894144001000014890309047d00b01800300381000d8204004041c0700300554003162401540d404940100405108a14804000c0140507003400c8411114890180e071440135140305088140e41032040114030414568845800d0301c0602e600034103101d0b520302c2c090290340c0d01d419000f0820380540740752110100b1141007010076220f0704a030260103608a41c0180340007a80381e80000d84070590540d02000348103c16102c20a00c0b5014a1040c4014086103c03a850f00e4000c3e1082504070740c04580c1342c01c00005600303510201024400f0030880011803402100c3c00d04400321044c005903094518101424040c1106080004204990203045820084e84038100c540098645000000d82100c07401d07001000585040704d41103822610604003683c24540d0703000400c0c10000c0208040c0c422014090400c000c2c00300a112200c0c0d2030014580811558061455800484d0000346050110101c08242c510801c0d604021400c09080c1501c0c0000a02c198420383e0303010032058200450041c0145000012152081 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 752078417 1250 752077167 752077169
    0x10140601081308030105041d0a0309061202250f061a0f01111b0d050601120b01080d0801090c0543150b0105070b0f161b080d09020a080307120504 64
    0x43d09903031541e485d100820014003028190000303101c1c0e824581002c6414104500030740107110381c8405224604e1700c18094400700c402c03040d0300d2883c0e004000c2e400d24a00c03c03800c1d000200050034034000c820701c0c1c0c904103402c0300c9950301402000a458100c07600310020b205010394200c2c100849042d554035140c7c030011035031070400c00318401190f0f1212000441c02c0080003a000006540540304800e45400d80e10341c0c03072420800b80d20500c442811545488144102e5083c41d0380503050840090101a50074030340282021014803854101c1940c41d00c24050552055044424694541a8900721462542550500103128070090703c0140b5a495400380b0000d000851180e25903006030103010310700076600840e000380400101e154100306081003242c000600346034045010b0f082c5015010391900e404c3e1010080000c00040000c28000400c00c41861030440e4035005403c0c990000d41c103a169106941e90310040c101781c600096004146010120314800008040c0501c203000300101b030040c100c40c4030165400d200d0303 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 752079667 1250 752078417 752078423
    0x50a0806010e0c190302041806050d11010302040519150e060301060c020a0902220b04080a1b0b07080d110412020108130605091006300302101406010813 67
    0x52030042100103105030341c05512800084020349001c50100c40d800e900480130800c1404654040b4050080b290f0340ca101c11a4590b42c54410030003581810002a1241c204030001000d9a020000944207a440382d01a01c00400015080c101510000700015020001501038020150103134100310200510909403841c16070406040903182d6420118111000310b03404405980207054080000303108281ca1000302410114ae8040303081c800008a888594070189034482840e618050006011030030011801024a81c0c0c01030462159001c0ca1108503451031055021818080011550340c00740f00034000184180300c5002c8080001c040301c030004400b94000c81c003031103441011550b072240055005060194110340e0440c104007113900c0300c1d56054182c3d44103c0d186a030320342148a03e8416507102e405090041c1844211410705007107940c0092009494002e20044544092103105040c103001f84120340220b0f060a03000d00a92180d202201c1062500741c55281c001500c82d4000b03440c1a410600130003400b54 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 752080917 1250 752079667 752079673
    0x601080402120a0b151c03092303070306020702182502010213080705040c05030c161e050304140f09041502090a12050601120503070312090602160c050a08 68
    0xa4540a024920b540410341405522603095240003041c843c4500910840304c08040c80301c2500d60005006506010412414208042545a20001e600f11074241c0c2900c40b260300040202a4841c404491080011001d54060013000400300601c850303a001041c0b10f80c02501c079555107c850803080403070644122600300c01c2c080e42c0c0090118401140d120701414111610001d03041427641024002e06510503170050130b5542c40031108000030306150142d074488200900b0000d045181911400c0d00d0381c81b07680c0e07024000561084041c01000324600400441e04205e10034070b2034a02d224500242c2c1c0354400e009510b40031980302d0b4018061700c1c2c081c04810b40d626001d44441071130744a40c1d441440401a402c50fa014140e028000144151038000d84080101003145800000c070a0340d05045050a2041e08070308201c85401985a01158000084582c2a50325242078035040300d504141d2401040212402000903000150300550540c2151101c41110300488803901e81a07614001c10410034882e00c21200150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 752082167 1250 752080917 752080921
    0x150301060305091606030506040219080106120c0503040807030c0516140a15030b0a12030810080c100807090902071415090a1712090303011806140603131523060108 72
    0xb40c0301fa0817003038001d11b000c0d202508050300c038050302047e120034079003582c0003c900b05d0040152680c04007440204034002041007004a801b600003d05901c4010009440c400000544d4410148591160301409401400340d03020182c2c0351100d00d0b240c031280c0c412821620303444281d6130454a00030713808030202c8030701100b0f00304000140c12003038000c0c0101e4200300354080ca0003030001622000c80c10543d6241886540c3d44031052501100d18007108181e50000707807041e030045203400e030b49490f9418000c205100d00c0c14445c100d60342d43d10341240c8c1603030349800000d803650000c0b4031802006202d004c5140804840b8007a5030500c0002d22406840340c038102c0f95481030b603000028039000700c0d001c403020a41030f0300b101182500d005505d121208075103c041c0c40800300c80e440080100041d0f04001c4040244010b020404d00489140c400341c44810807281c665148103e20000103c1c900c040d0589580c29401e9100c4000e0200307413140c0c0c1000000301130a0b0545102e04034545500743d8046039000d00c492052405071610340080e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 752083417 1250 752082167 752082179
    0xf0302010e04141501030f0902030712080d0f021b06061c0c0e07090f140a090f09050d031a010503191d0109050c0f09190e0307021503010603050916 65
    0x129500004103500a80d58084070705000c3c01600c02c01d803094800304640c082c00d0356110001021604034140f500080344c9082c041d800142e8001c1284400c40707110212514220005081900745c92050103c001405881d003014058650710a402805855401d40300207a802c098851411352a64812506540e0142003510178502030620000d00000d818010b05041d80c1080d02c41c01005030881c0182e5043c0d01051501d201040b10000300075840015040106440030300d03111281c04120014483c2c09110149030f121a01c0044401d1281d000c044019000411110b820302050b401400401070580700300e0342c181c0d040c100c440403940190b08481c01900180d9101d1100841c040c0602c009080d034022034604100300303100c0c03280c0c0304609000380d28200703004001500c969040c03842007202001507a002c072405000b032641041070408603510000318400440b6804038500e01c3c030b100c100e0301f503200710640254407241800e00b041c980c0c08403030081e50581d002e80d10200302d1034903840c030f43c10f9072901000c01d092013903020130f00306000c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 752084667 1250 752083417 752083427
    0xa0b0307020607300e070f03031d0f0d0b070e030c0102031204080405090c0c191a0c0d060b0c011a031222030503070b06060c0d050f0408030424090f030201 68
    0x80790302c851882c0110058a04850340200d07544c100b1a01c012511064005030320841800380400405501182c080240c1c1b45039005428402c0155858130610345e90b0b400d902d00781c2c49440b00c42c20110001030221242031018a404900350606864050024240b410b0410f0305043c006601c0000e442c05030021810080d00b56050002c080004108075000030043c0000590703611000900341c0203000c150b62140d00c6040044a0a242824200c14a0000c070024401d4102003a0940c0c1c900b81c2000c1070f207000c0d00c000d0b6100c441020241c440c14200400385d9107031080014040e000003002e02210320048000740f0400071904411811707045022000ca0785600000070204960042c1c100400300d42d035258241102c0c100780651100c41c0781d440d940c81030b986500006842d00070030008a0800340c3c0030380119100b9003000302d0385461541e00d5841080d8801030050000d03441540e005d080e0140c030000d00c41101120b548580392808901f01250300b000f1951044107034011480c40d103010b20206026902407410b680684c1c2d26613001194 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 752085917 1250 752084667 752084687
    0xd090f12080c01050709030303050603150412030b10030626030a0f0905130603031709031b01140423030c1f140a0b0a050301140705030408120f060a0b0307020607 71
    0x30100400c22008541260130b0184510403045519111140c61a45c140a821303644c1c024000d5100303400056201c02000c2451541a41154005100c043c50500c0881e06034000c250203a000b41c0d00080c003081b1080d425070306030400343c10740c0c2c0e00c800409a100340d1941c40c4040034003150140d1341103400030301220100c5841402d101d001029240707452602584d645000c202c034040814207414840751200020300a16070800780103520781500440da0841803030b11044154607409003040c2c0a01080e00064007440f10788094202030346031482d4001d85151820113217041c502c1d030454002c00c58058041c1030b1140a441e50040300751501c0b07480c1a00901071881254001710080707030042c20491801d07560350000003541d0b104a030b4040e00c940c400c00000141d8a200d030040000e900a1079001c40d100380e041803c56080d00e000c0c14021a0040760078108280c80351603c3ca0304682500581803501000310016081000422803002c034640281d4040d9804403a29407502003180042c44110791480c0540d01c001e0106007458401c1900b07070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 752087167 1250 752085917 752085923
    0x2040b010207180c03140403020703021c06050f01090c081005040513050105150a090204080a110402072913030c0f05011506051305030304081e100f0e0d090f12 70
    0xb07400d1944a010b903010800070305242c043ca0954038034880c0f600302d030548203000c440113018a4603403c40c5000d40c3c0003550b514171030000078007031039049072100c0100c011184502c001980c40501804a460a085c01d010045800d115032203c079410071305d8001580d805078200a0103400d40342050a00b8504280c2444094400030700650100d060700d080d10004540203200d0f0600921010701d40782c070083d0901003009076440d40c9800548005204010410003075400090350641254800281060181100c002400034081e40c000a411a190107c1551855900c0000d8031004190782d003032180c00b502c40c0c01c2035041860761410000d000c103807040101c401003154070403281c4005119200200302c81c20340801d0074600d9665640094007081000c102111501000a41c11026000590080d410245402c01540e81c41400794001c0d040140340c00d000420503401030043e20200c030740054040c00b440710015502d0004100301c05400941380201f5041e001041d20424000c0d084030520214101c5480c10140f800ea80c80380c2c142021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 752088417 1250 752087167 752087173
    0x8011d06010e060c0a23100f020c0d122f07111002010e06010927150903050301050f0a0f0b18120f070801050105010f05090103020c0a230f0a02040b0102 67
    0xc2c03096640c0e2a0000e2820482690251121110300d00d030045030804500707004505c54002018811500000140074001070540300e00104103244118100c2000307118116061926020b840f080300041500b0811031010400b052078108070005491003091803004608900b42400c180b20180b6504105015020b4001d8501a556280184e550701000400204c04120400e015035110081100450b005004481c0140000c030070a02c00d0b540c501000f0f06018500000180d4000341c6801034209200c00307054114501c081820007007101484a05001d04142c100344210713403080e44402803200e014180034541204503101104034151045c1051103c980507000001004101c2c1c0203144800c41c166501d00c00c00480f5201500540035006051500e142072200c15040103140c5c1c0e0425004004907607000425100c04002c1c2d191183d145c4c40d0ac480100c01074810b1407030f10a114030a681680c02400a10301e004100d800c00c00403a400b001e0440c1d60502d854a64002221110703402c00340c403020140c102074104100c111414030507 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 752089667 1250 752088417 752088437
    0x20712020f0a080105180604150c111605130c0801050906061317161d190c030c0e03150a0e070f0303081009090b0612031b030c060708011d0601 63
    0x100b00c4501c1e860380040000d07910307201132160f01080c1c0c85001001a82e0340d4054103141c80c003521156058091848034401d101e81d00c8034881e41d0303581f0039248240300103480c2c0e00782ca0120040da800301d8440f840c540506071081101c0301d810314030b0009910503000030301c0c0c1549480d1a541e2074682040498007008003402d40142081018a0346504010b081c3c50142c401c021640094544000410707143c0003424050101112071030b602401440503c01990f50ba9002c0c650700b0381c2c110794400300b101000301e40c42c04820480a04200780e18850340d8164000e41c80c40c0e0126658582c084a010f0101503803200c051080b0507a00b102c01d0085104241660400b03a0741c000c2101c105c40d22182c4d5240ca840103070400317900603000901d0880522101c5600765090f034004004011007400003104c0c94407070301141c91011300110f1140c0b144494003100d140062080d15041000004004406e40051420989030740c4000c254146601845000403030b070320f011f08a9241a00c0c8466080403000b00d5002c003640070340c807002c0d010714148521284 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 752090917 1250 752089667 752089669
    0x8010303030522030f05041a0304120302030903040902070303140f150a0f090914060408030a0e0a020609090403020a051b09090114040f03031104140f1002190f02132901020712020f 79
    0x40f4203c40c0d230503000c0381d0341e81c0e4500360420f842c9080e94903002000b0180108103005029000000752400d41d06203401c0142e88145c40d00d02a40202040c44010185108290802690300c409410b070300d11503030301223104a01c40004034080018107070f018045c941050450140500000d146a03200641c0d03180700d80001814180441003030761034070380211411100ba240c00010480c07400b403a4001d00f02d86c41c0098001389989442c65000481901400403041e0080e2401070005080c1442009200507407500801a1b40142050030201601c0b04032003801c5501418850001c64131070941441806880e24140745e41041c41d49035503680b200c4440c1d01c140c0c00e904164844c41d1166403808104020401081003210b582d05030003540c001d02c04034508403140380e4424602c031103407101419004034140c0d401c0c01c000022404145030620b848502d01c981c004001c2e400042001641564061340c2d4003e000d5503001444994804032450340c1d04044a0003074414a006070801103080206e034414060503000e062000700001c0d000341d40c500c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 752092167 1250 752090917 752090939
    0xf0908070806101e060804021f11160312080402010c0602030f0601200c120f030f030a15031511160303321b0f0a08010303030522030f0504 61
    0x380011190342c20500030321800b203805060031401040c44a8003200c0c000320f20728403401c492007580b1508080c000840b000608654407008480d1152200b5841d2840303601c00010010090f204401c0c0c2d604c003a114000005c048054104250b80869600100b900681d48002c10102c8600c90f0240080b0705004100d00c1e41c0700001c0c04c1e400070b103210b00741d001048041c51911320001846500221004c0c0109900c2c03900c000701801c5c000c204580741a038180c60851040030070448462401300385d0301e1101c915001c04101c100000040b000118040c0884500074840c140e890f4503c5001c8030401d01c00140307036100c140342030040000a504042c80d00c415400c101401c0c042e4424074148540c92494044000950399542003141d40c6850a81444d9188908042d075031488130040000380030580548400240000c940b510390201e611007080310b0410b500c0407420ba8a6600380300000d00380031800e00007103000c213040c400010121180f28200c00000f142070103241c03072101c002d524142d03000343d00c001c801d004004040002183c415031070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 752093417 1250 752092167 752092169
    0x20d110409090b13052113030c0302040e0f060a090201031503030215160e04090f0203070e010f08031e09031c050403030810080a0215090a09020702041b020304060f090807 75
    0x18480896200c1041c40c2c800c0751070100a02905a4140100c03140021540c0002c0b0201106406c0316000130703224214280e041035000d015401110704e000020080104480240500205c03442aa0288140c854a01c8029214a86245080417136480400001d14503503250700038008441c01810009030203082a0030001600740c55400c140d0149c0d04c000b5050410140d03220400380e00608448240c0342c0365442550080007406040d00551080f500c03003403c4410700c07604041800289a00800f1992041d40c2c521160103032540074031031440580042000015424808400c07581070f030001303c00a04400306c8034440c00800c6d0304404042c1e9014444e20800003000840419900403001031030325920b85640c65444c000b01300782c40041c140c03448a000942c0812150100040345550a9812201200e044030a00321a070b5640c0601501c03142c1c0b14611200c0041c90300750542c000c100003402a02c0a2100301012140640c0603515a1004c000580c010041041050b10800c03140078200043e00c0c000e0380156451940328645941 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 752094667 1250 752093417 752093429
    0x6081603060803070b1f030b07180b0c0604140105090717010b040c031a0a05030a0201080915040c03060b0d0b0f090304090f0c1e05030403032d050105010801060c0503040306020d1104 80
    0x500c5c1c00c1c8095241c2101030080070704407a1a100001078155500c0a650010282c103031300c10306c44a41e28a024010070404600d0190012a00c107680b00c41c3c086600316913400c403d64041e40c000d808100c941c0c40c900c40c107008007032003590928010040c9520f0480030400c3e41c00440c060248555030b481d407070707802a0f8583c0540100c100060b6004a6400038409107904040f8503414400c0c0316500f440ba0412040e18080360f22038400c2d4090030904036a40e581e00c0185d013000e241c43c29610407142e031a8208020000800c0d0040e050b280509010030410318001b0601c05114800d00d0080c001010000000313002d00c0c49108071543c0800e203042601c0c102030380d9090041c103a0b03903804400300c88640c8528580760b1a40e4084540007025200050500901d600240090f004e880040d2026041644945550b0204854060002ca09906404202c1c1898060040002c0140717002c3c0a0b0f43c4c0041c13000000011124800c01880548503040300186203058655a154002517000240501c004ae446075004010342d46044080c10040c44 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 752095917 1250 752094667 752094683
    0x31302100903020108090c0d0b0601051207020607022103060d0203010b060f0904050c040501171e01080f1204051c0606030b240118091802030303101a040608160306080307 75
    0x402c1d480090182500104060881c0e4402c1c40008441c5d030740c100e0308000c0607812489510068481d440102d03001d04c41d0420050088820406000d00380794002045446000d0603400da9141825441070380b10050700c150390112440d0b0003030001c10340b6458400d10240d0300900c000c0000442b402400e003c00c0740303a00001103c0d41444d10200b58000c0b141014091158003c03c001c0341c0c140b80c941084000303070201400c2196040130003401b00000b80c03e4400c0200e2141c1c018088442c110403980d4841c0e106036030b6048051100024010912400581081c0791300756029035034021b02a00700d005090b680d81c0c44a0644500c266010368459100001244504410500880e5200b01d4a600201c8580d400f50420b2910722400c1c2c100109100b5152170070802c17a8542090311881311020950039128569030b0300c0c80803420b10103907145c00000306120b514000350110f4011a1038501c03d411151032034015000840c001c80c800d080c0440c0c07041000421b5008200c441400c06609420005401e03511141c0300d42c07443e0080a01120084 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 752097167 1250 752095917 752095919
    0x809011d01062306031306060306090b040201021b060d020a171608010b070f140c130e070503120706050c070501020d0609060b03131e14011d150106050313021009 71
    0xc0f441c1c0c403402c50201c3c1c210615101580e60f83c400b0604d03921004151a10b200c8840d405d4004009040d00003d00135030f08142c1c2400300718041d0900c41058041603408902500c00c22607038110ba00321015403158001c0d0002c02090070644c002c039a031000303588a80040d404010520b81c11031550086078400b07d01810048100d805500088280601722401c1038014146800c5c091141f00c00150084050314091940301095900640041e60114075001502030b8099028010542c940413408169000c90b45200c820000c4a2401da607a04c181038559058803400c3c111032408010ba20040340403500203c0c0c101040c00c6d03c0501d0b21400b40c840d0f9003260442c00c140700e0340988607601002168098061140a0700360001c0051442c20601c2c542d01c0086640103001744404c11866108102d180701007030a01c103083d0403c1184100100c000c80440c020104490600005a40c5103e040b0b09003400062540024001d0081500541d00740b00083d074840c1c000402d150008040a0705070b0380140c4412116940000032a22403144035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 752098417 1250 752097167 752097179
    0x2040f0e121e030f0a09030e1809060601031e0914030706050f0c030601120902032e0f050402010f0e031002071202010605120309010e0a080a03020f0d18060809011d0106 74
    0x3815040c58620b16144280180860a13680740201a00000710303070000112442036103002d6a44070110b18a05500c0341054004800f0003000240322841070b900d400545909a44500c0150202d0751420140c049c1c2c1030b0030884011202900d58012115280188401c0c0d40080000640c3c9196500c006c004450454030381040c882d449648046094104044030348560030340c8ae01c840000c00d8607009002d18000c00d625841000155107003031040d40c0d00000369204e8a081010f08291400c0303140702d44400d0f1824039140a40c0c01c0160400c510849000301c3c5d05941700c1c40050101d00084032105002c00110b60f160203074284443e8440c00364401443c032a4426031460340231025120011342150460340c401d9000d40555400d04408150220450390640c03030034200f450010750500301180d1040c1103504400424413690f0303800f10034150001020702030858a070049480c40f0356a2201180c3d40c61010076014007140090b14141b043c18050b0300d032240e0001c00f5000006010480080c10b05003a002000030300301320f035509c207018425 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 752099667 1250 752098417 752098447
    0x10030b1312020105010e0609100510030b0a080d1e0203160c030311060118020a030605030a08270d061116060615090b0405010e0111010e012c0a02040f0e12 68
    0x14000c076070000700400d43c5400078002c2c0c0d280009201130700c295800400960580340c1c0601170300c00b40c440a0001086a080f41c9006001800743d100b0403403240c2e030700a07c001804803000918841106483e130714a0f4545920241c15219030352b081c8500320035408188042c1c0c8407002c00385582000c8600901108004500d98100601504812844085950883c5006001a03e0114130442c803508500c800141d603510500822002080c4940186a06020340210681071110302e101030082c81c0f454001201401c241020070301c2d001c0c1d403601c200c0d5410810141410002c900e542d03118900c0c0c03100703850b04e0b1858040c10072050050042380345801c0351540d903520004c1c040618031224034a001c00c0305041c4030300424140928405035004900c58230b41006800d50301c840559210b0003250070b500c4105130080c09099003581169000e040704600003803081c011070307000300c40c84100c2400c1c4802080f112409070048403516020711010b01011500280a6a102c3d6280c0117801c9003040401c0740c10310f40000541d02d4004204501107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 752100917 1250 752099667 752099693
    0x6050f1c0b0f03060f040323040e090c010503040f08071a04060e010b1512060609060f120606210403031d07080c040504120c02031f0218010f050a0810030b13 69
    0x80a60302080410040c0d0807010300081c0c06c5500760600c1c26002d03151211004c454490380c144040c0051010400240052508400d28010301c40750050f01d5840c00384400458180c0401c40d8040d00d0310181400c4500404d13803210080c40d4003400340c940c1010110520610001203503060350211505580d6a49003a4581e10a11480d144a001191200307500c0d5201c520084582c01909240014088100041241a6907413011608a49030140c206521a110420740406580003130031508604240300d0001010f5107841011504041080c1d33a69421451450034840076540d030003030003101456603a8051a11200c54500b802d01202c1c1c045004100c1c260a1101c01c60810070540c100c039000780d08010500c00011a401c0785014115580d140c41d035003426a40c00048c0c03400480038803492844103820040035050480390014650701e512040e08101c03508003000115904c451184020000407001c0c030405040d6441f501405070030620030703810001169142c4d1100840c1d20b070181c5284503016008070b4064104075038000100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 752102167 1250 752100917 752100919
    0x3120e0c150315060904180c03170307090e070221040503010f050105091b091c290720190b010b0301050901050f040f1d0f0309060406050f1c0b0f 64
    0x50b00b54240300c0b400a4a030444840e800d0300c28040801c01c02c1c0c907620303154819002c0d51081503001c8217034205800c3c401c880702c520340001c0e68000c1c51010b008036011030340421a4042c80d01995100083ea1501140690103800070b804d04017140501c2910f060803008021341c41e65040344080019503110300c0d00c0101070071101040394080040c4c0c00d0400411040d070315508160b90108025011401c00c00718200030340b55522500744181d50000083c8001d1248000031100f1924091203045107507036440088030100d6003442e4161102c0c1c901e403560f1000031f0046100f50780a07902c00c0301242800101100c0031614604080c18900c1201c004642c81404000f8845d04c1407805006040000599295505042c0402c8841d541400b840d8012106025034154a490316400f80040c030307400140c10404600c07011200c0350382080c404500c1100d84901c500785220050702104403401c41000414a510741498900280c0d04d9800403240c82440003024001401400c003411555401280204d800181b00c1020104020003012149019 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 752103417 1250 752102167 752102209
    0x20c03070e150316030308060d0b0901061a03040203071a0405090414011803080115050706020313031d030601030b130510090204060605030601050d110c030a080a061a03010b0703120e0c 81
    0x3c1d0710b003014028884143c94051401100c566212030104142704a01d94000b01154004800c20020400c1941b0500540f0a0403441020b8009020402d2106000039200a03501d600001403c1001000034a50441c1c4511400400c0b070509641e00c0000386858401c4400380e4814581e40c0b90240c0e182000c0c03142600444004a04075a210b006441c000e14480050140c0f940c0007060104c000100d1780958295800c3d41d82c00f11080d9a2460325000c07652442900400440c04510b410741e24000700d4110400000d50000040d004281683c80e6450301078a10f0782c05801020001c0855804001042c024482100030781b00c140350100340c807100d61040c070040b5042039012100b08441481440b6460b83d1180407074042031845000401d1043c55540348103000d119080701c80c020741c800000d504c0c0580760420034084c03040c00d504100b0007806980d01107140d84000311040f248503041d001c00060081c60340b00d40c05405070714000c3c0f0f058009070f040414443c044a4120302d4001701d541c081040b08016240c140142d0401088082c40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 752104667 1250 752103417 752103433
    0x21812060f1b070f060501060e030d26090a03141201051009050901060c03110123070e0a0b030f090c1509060d0203070302031009090807080a020c03070e1503 69
    0x100d85603140604490141d1441402050003205214165100241c559100c2a621106841c1c00568024030710011510349043c81c0c0000303001405400f0b0f02486020180141c188440ac4941c00c07240341c40c082c12203030098030400292244107625906464071654900000b003002e0010750501070a8410b15185003000100704001508004103110034590450700c068900a46ca948080d00940c2c0c0c0e01141d03001590844000400042d1880c1c0c4101e040700324034041c0e115603200900c0005603a0980b000d0b0490320b02c01f800c107008013801011400c030390300ea0f00600e1031400c0805442c0020000300b500060358441c0e41489404828032082012101d4015002004000100706009516011900240700303040702d011030400c00308105105498010450f03041a41c0e09008559a207070100c00034000b904150f40d41841e4950036030010883c01107600ca2940a1a0465000e50030b154850b56442110b5001c0c000b00011402021700c3c0a01da518100060340c094134007021401b4640ca856030f02c44104824406010b0711a030f0108030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 752105917 1250 752104667 752104699
    0x90901080303061c02400603020d020f0a0909030302030610020f25090204080610150219020f1c0201180501050f0a0306081f0507210903020c060a02010218 68
    0x10044c0341c518414a403a40004060b40002400f8030b0040c50600d80c070040d1403140c20172641d540c3c1c4a41450307080c2155100310b00e0340c5044049049500d40d02000790000b00206140c0090300e01a0b91040d92880018207014201b41c4400c4003006465042d4001c501191b008000d20440c2e26084070822003920301e9100034508131200285295540080340c842c500924210952040000b480c4102a4060301801c20159603070b03940c034141c09135103c40845010441b50f01e40180030030110340b03460441084c00380036402805421004220302694810944007207a1140090350050340035200e5440781c0500c00f14141c41038101c40b02c2c6000241a0740c0000e00340391400c041a41c401e022036a004415201c08290451600e61502504c0d00180c0007810160010f5126120b40c1d524a0300550310520301e6109005160000d0005450b407146c242c500b803484040c0e40752009920030341c0200303541c85940f01034202c0303010f4030498489a44680200b800c59101900b5140103035000507180c1c20320710881c0b600480c62003094135441240c87c26a8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 752107167 1250 752105917 752105929
    0x30114131202160602060906070c031706010c12230a090933090c0e060306010f02101107210827030a090e13030e04091502030a0209090108030306 64
    0x35400804400c404141403801034802c00c00000e5801c007a546021200351202d40295035000e041b00c040070503105003800038540d244030b00c1c503900003140c1c16100c51141002c1406403241940f0020621380c100512115560f0120380080d07036809850a49842c3c4846d000c101c0313000c0c2004464000803e051f401020451504125848000481102c142e900c001902a5003038507082c00401c0c1c241400500d040b20503030541402c0e501c10b0b10440855190036410006018250419500e280c10141601d622420034170002e00c85500034406400d0038459403043e45d00c0005044120000c440b07900318603078503038480840d141c1e007004000c0c8d807114840080f90301c0c818240781881e01d0040050200500c001045125402000c03c0011180c1e01c00000c070b04a0030540703484044155004229907880c0c8680900404940301081020004103804112140c1554424981c5413580f4180701c00fa0440340b00441e080d1501c2c2a00d00c080900c03d00c00345000d0b00300c40d100940c1d14500c007410004002da046e040444184c00820512030307544c1e600 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 752108417 1250 752107167 752107201
    0x80c1219030b012f0a0501050f1f0512010915060501020d0306120323030f060901060309030f030e2506081605120a020405060a020a0c08071d0916060c02030114 70
    0xa0100380d25482d60130b4154229060444c11416552040e00c1c14582008019004607200f840c000c800c0e1900707903a4a0a05c64200c004162404808610b0b6503402d100f18280b800550345030010f40400030421142c05d41e01c1c1d0650791038102600c80380681d9000e042c4403541e818880410b0b05500c138542441407905052100c0252900400d0081c203210700610550700d0081c81100e540400c421070f005541d200d180c801600f10031258221400f500c41d81c2d0003c004a4074901911079425100c6e0542d0710541a401c2c1c904007500101000e800c4060036110303400e000107880080c0d441d82c02c8042ea5090b40c50501a03e0010041c203500c401030043c0c0c894001a540248440c1c0c7c2c020141e41ea103010380e01e1540600d0321002d44d8640240324942100d40c12003000a00884140c0e00015030320307409440b4071000301c450769a55800903200d90190040c16240d6480c00080032100320b00480c50360700811800b058901507201c0007072925850a003a0f010801050010b0444410341c5170a200d00c80b1002c01d13000009506240a6409100084030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 752109667 1250 752108417 752108447
    0x9100e0312310e0415140403020331080a0209010905010e0a0207080f16020f01141209190f03030501060311070201030507091a04031e020303090d080c1219030b01 71
    0x58046602c1150900900e8000705500b5214440d02d00303190400c00b59618050380d17020380c8035017012640086039445a0b801e901c1190181c1c080e5052940d48022580c12401d03580c84840104080a90015504400c0d008017008220190007402401070070f10503c9000300d81640b100d04070310f140000400c4420080a010307607020301d0894005a40d1a02c038500500d245c0607414203e04655008990907102200b0021221070342c90003104c1481c000803200004440d02c0c0da080342d0807007034170400740700140303590b0b000691107508482d014068580c4202c822412494035000c0001c01c1d60501c2100d800c0e1002c0c541c141c0b085502501d114507050001d03400800700c00029129440b0000e040560b5200007502c060f2250308030304040c1c21032902c0498200007003495089990090b01043e0ba501410058058070024036004007814664050060340c14580c030001044850b561481c0280d417030280400c504059143c0034041151510032103980b854503843e0070354403524801a80c800381010f1624110700401c150307030003151000445d0071b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 752110917 1250 752109667 752109727
    0xb06031b030a110f0406020c2409040f0216031e020a0f051c020309100302120109200a080711031c0506061c02030601270b03070509100e0312 62
    0x54240440000b0300100f414004a9080401e07001400d40041c1c0041040f41c800e5422111050200c40400c110448808404002c032803a209400d080c1403040000340095000003000007815100130b6900e401a644810400311291003a1155a0209078029070002d42c0d8000c20401503c00000580c40a5903c02d0783c0c10001d4155001d6200c3d0350b00f004030030086902c514507210800c92031009e900034065541c2c0c12188240348603644130082020018070038401e81d03c4031502c10b10281d503240d1a10302d0020083c504903a0130a44882c149078800300315040000140081e1546030b80c2c0c2079051800340001060007440483e2040305070010041c9101c90641114822401c44081a001901d40c8038640000c00d28070810000c0c1c814504c0d0710840e451a008158007642c440c0000b0317221004011903081c1c501c40480710650044c81c814810000070300400403000044c690109003070900524190703400340002c00c0406030140d001d00003004114021000d04040c090303003080c142d00c0d07400b15080c40c1c4030300d000450007412980603101c081 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 752112167 1250 752110917 752110921
    0x20a0314040512060103050d020111070f020103091b030605185a06090a03050c1204080f010b0102010e0309041503121e02030702060403020409060b040513060b06031b03 74
    0x3841100445006000007050810941d45000115444110901c000c1c0c480e8005c1074a5410b2203401800384c9034611460702041807400100780d4130500d0007a004402641055a5402e6820000d0441c4020281e103050300c00c400c4100e03074518503061003581c030011b003c07191490403c00400f00580c00081e28054191020310303145000180314207808510401d25000c0c16000f0101780030403103580094800000c0060380301060703081110b003070310440c0e0342c40c5000d03600448150300c406441000b0034401c0300a010b6040002c000d4501c0002001c90820854200d5001004035405c256804c60590000344110002074100707000034419004050310703003a01c03801480349043c0500d8584042d641c07003543e601c0200f0059640b100c6900202610000000c000704804821074041c40c000141b0078208600000a03074840a5005003282e15150456082c071001d8024100202e40c1151030b09044080340c0d84c0d81c080c5901c074140344210407a03010140e0402c02d060700c40d641c000a010790f0f4200140720a24014003104402340c080c04000c942d8135 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 752113417 1250 752112167 752112197
    0x1c03110d0f09021302071a0403020619020c01111c0c140a110a0305030603240406020a18170717030301061b1b050111011b081e010b090108090d020a03 66
    0x82c040211000b90b004124040d52640000b40d540034145240c040e200d00070200c00f0340c20708403400b1002a200a40075078006000900280426842a5498030b40114058204803800f402176094400c40f5142c0b080b00c00c808900c3c105800080d074014182d00303961550521191001c01e60251020901800145109100064100b0080d001d5020b40460400321021101014214280245281c0040e1910f902c00c0c001e40e44005030010569096006110003c0c407290f0850715940d40740c0d03009610030030307414041c031480c40d410030000101100e0f00002810295500041d1040d052042c1e428081c440c1c008816032a407020114040040000681c0d040d5a45428071f0b4030a00214501c1074031503400307403900070152154000c205440d0034000080700122402a200c806404200722001030998440001c811409082401d40c160b440e48a02541608001c40d02c00e42a200035200301c85003d0762000760815503020b07900107448206942e114aa21f544803c001025240341c0342030380c000030341340c014030070016040000e00705100e108 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 752114667 1250 752113417 752113421
    0x103020a170a050405060622090609050d09060206010f1a09030703170408010f05070f18080d0e091003030f0c0c0e240f0a0303110f0706021c03110d0f 66
    0x140d0340e00c1018456a070319200b9141e5028007001c940440e407901400d0b000c038510b030508529881c15032070844c06070340382090028095030040800900c191281c40d00d80d600030010030000c0c00900d07400a0241e80d807070240350070000301900e0000103900c00c040e0854940810002d10a205150b201f824000c11301c056912109a00080d01c2c0260760740028104e158039a01c94074201c04107000810486071503500a2100d603021110010455401b115800c4c00300c4d2a4610308224540304081d05688a50107150302031009481e4006245080502c0003001c0106100c2e01404100345040070040e6400a030303001402c0030450860740d0041ca01c0d011220b0b40380c1070010081108081110880164001c2c2490361038240181c684040c441c1403403d80c0072400ca84c0700c06080c2231144241007461403e214010054080c3d411185595000c0b41c00502d490030300b803107502420f41030941058040c0700c004002c220541c0104545a91520940300000716903074850103152410010b614440030350010f480d8540720f03010340002d80e042c0c58a03035400 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 752115917 1250 752114667 752114687
    0x90a0608010e030a0e030106060c080a03090b090703030212031608090a021009031b0b0406050f0702040911011202040819140d0206150609030c10050408120a031103070e0103020a 78
    0x4075402c01003445020100040a0103548503596240044441124141802c031805400356000107031031020b800012900c801c00502e480240361130002540666510b4006070a00c09840c6d0b2400e03500314103c100180340d8100040703002d0701d481d02c0780d59103541403a5007290302030b210743c42c802d00622070114000351401c0740a2001e006190b4003d4802c0d6846854404000e29415882c00101c41c03602d07407454141c080e06016850310f2301b982d107040f81903890320f8103040c01550150003484410303000d10b00030429000144c07204d02428004c00d02c81c4642c5c0b04886215000503145e15a84004000c0161041c001000000d0f8000780c4501c442800d55451680c1c1e648a0030021030403910200121030501c20020001d14031580041c40a106152100030100300c0900d800800c04544501c124007507240e485800310440518040401504d0b100d510b0410a18181d42c0c0e0703c2242c100b420201c0e61090380c05000c1010b1242642600400701070802c131458451442c500b00c4c070301803e039000c00c5140b24101603001c42c0c80703020b01e8000c84000c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 752117167 1250 752115917 752115929
    0x303111b031513051002031006030924090204110c0606180a09030e030319080c0909010308090a050d030e011403011d04031809051515030714070b091b0906030c090a06 73
    0x944003981780c2c4400c034081e502c1035803904483c1040540004504c3c0c8607108050b0003e0b484445500c0c120300d50940746441c410b8100384904142d0780c0e40c06520040e03980b4455101c24443c1c1c2c4003038903113444405800030f0910b90700034101d901030072201c0002d900003d42d0a4200d40d10540310f400004640700641011a09030a500d404580c042c800047d55400c200c940b46505201c84030181c0d65481507a503a4107558100e0300441e0303800da41100e002c0b030040c40020303c05c00c040d03c0003200c042d042e0b600c4250b13a20005040348000c16400c2e0041800281030107440e5900003200040c1c00380030b14036a855540340020034004100011503c0d1250313001d2001080170548210050010303d100e07a842d100710b8507200c4006100420095501c400311014541d002042403d2210900f080007140400660456544000507202500c9001d000814000b040107172800140201c0922400b407170355030b00101403410390710071f0000f9940e50300e043c890312510000c41004a240d4000881c045446819114030015451301c00814014006a420076 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 752118417 1250 752117167 752117173
    0x206120c0706111306050f070605151801061d090609040201120219081003030f140405030d030c08091f0c0e04061202090a0c02070902220303111b03151305 68
    0x120700c1d00500c20240c0700c550302005613804c419503200001d070307800e03c43c2038007080d0f07419402d10081c0c000c11603d500c07642d030146c5039149007a900381c2d00790b0015a40021890345105594004001400080c0d401071048000011800c01503690901110000e8007141008113410711810f14580020210391080304d18140c0c0d80000381066441daa035000b50a080a034003244034000040c0038400040300000b20002400881c2d40549036100c541e0160501242c4c0c0301e19091524003d01d00c20040003540b0b4404002c00787d0b042c07079181d8000551440329040200b0f1b102c4084e0110105070f00441488903401440d001143d00741301181c0c0009403040074070070103441c0d14071110405c3e9881841c0000020303202c7c4d00f40345c2c200307420761086a001c80340b541c07025080021640031704410801030380400170038070220007281c3c024000e1010400b1050141001c503004000d0b0841141c0044000840302108400490300401c20845010751200c1002054803121000c29a00d020341c0d5060008528410085240c3c0d08150308000d400c4c64002007a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 752119667 1250 752118417 752118431
    0x903230f0c032106011103070b060118230906035104030e0a030c030f30020712022220070516080a060e0705030a05010608070905040206120c0706 64
    0x2e56420943c0c00c4a62a003c5010031100745445800070048031107480c0c1c028807220841e12418011030f80403c070b0040210950680c40c5000c035010ba840441990b0890064100e82c03075094841086c0005a6006405980694018840742d140b0700c480c8410381e49203080c82c9030b078420b034954038a6441111910840c0e00b41d12030414083c0d0340340200d40c0c032480e00388158000e460303501d0a2012081400000b050f02e01c0041d0405041980900000300c2023540034110324090024005142600f00c07400825441b00010700c041c01c46488030111940b901070020400a251a8030034184c03441c4c40750003084282c50200304e00c1800c50480321000000c0800e41d401005911100c5d001240d1003075013014940c03c3c0da0702c0703c5800e5075607102d80c00d007101c242e881020b6500300380c44510020705225511a0f45035800b0304a08072448015000c1c003a004240b5880420601d042c240c00346001180d150324046e000390900b1426000140078509142c100030143e110641158682c7e040e0303600c400b000d42c3e5024100d101c180901d40d070080409040c000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 752120917 1250 752119667 752119717
    0x31207032007090c0513142110020a0c0c1703040519120c09060e07050909191a0915010504060507030207030804061e0c1e060603020a090903230f0c03 66
    0x20281403031014050400b14040c0e125640e0b2000070107068641680010103070789001a00203a0b008d81075528080b41c00302c0e91b48041c88445901a80c00182c1c0d0b0b100040c00050682e014881c52000c040014041c0c1d008034400f12240400b00d6840b44524010240100d914100500c0e03070341c00385555140100400b120082c07002d040c40c0391a8160118500c50107840c207040120208008080441a1340149055201d003480e005e000401d200011100078404020503602d264912040d02940c081e1455403454070b8160305240f4660350400c1312520010b07188103d6001100c00034040359801c0f4013110140c42c07803070510b40d4545446d1300d0201d01d0802140c2000f8034030300000c600018425000340035039000c0007191403880420350040c7d2084809901c4490301400048080c1c0d005010071035000c0e42562064055a03010800395100d07000300756201e203598440074610795074511020600d580140d4080a0b00c80c090040304800e103540c1440c01c80790040711003500030f0410018881c200c4201c100111861803e25401ea10500d02080c6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 752122167 1250 752120917 752120927
    0xf030d02010c0809010c09050f060c060412030e160e0c130f0303031a010c030e03010f02121e0c030f15031b09100e0103110f180402031207032007090c 66
    0x41c0102d02282002e0041282060180100d1030050300680e120a0142d2800c0c0c10001d1100c2d201402a070042c04c10454060000b00a102e080e202d40e01410b041e0030900c070030b42e8000f0200c0b990b1010202440e0031000408810040b11451a030813507070100f20f0403030359031112501d40c01284100d50150070078000002c80012040c0c031074075000003181d019403010040c0a05900c0a180c1a0003c3d084250010b0032444401d000640101801d41d840500903000103003805040c43d005080364855034181c08080c0a4100704140c00c2c00d084105203411a03040f56580aa0030700364a1b000c2107000140c0a030701d181c1050000a010b151814840030040d074001412980ca40d1901407002407a4070790064042d003d1100c0d00700207905400280c011a04032000034400c0f0700160328648400394a503410340480390f80003e5482c4000c28a41d0f9400c5021044c03d101c00010fa20390800740b04141c506954080c2e1040710280520a050129030824502d440420700301c40303d00c00300460900c4d03031401c3c042e407a048080b0305807070009039000040e481 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 752123417 1250 752122167 752122181
    0x60b0901061d010906200f0f0615040905030307030f0b04140a05010602030406091403010902150c0708010c0e0d05011407031a0f0607031209172701050d0b0f030d0201 73
    0x800d024140d14010b900111400c004500424020864900a40c00300b0090400140c1c1054507940a852011001103082c50800b06160b243c12a9544404180140d00000280c40030110000315810045d0b54002c2e511162280001448803060565610303e01c0000d103080e0b0444002640010010070104a6010721000300700010b81d00c4102080c9804004140b107400001202d042d207030316071205421030b8900402a00104021141150555268a02140181c64a4040807500303008803140e80c1d1a011049007852512085500c81007140e03041014240170990800b072000c070a10300580300503d070302c6903504241e40035018190340240ca902d00d070010408001e0345035100000013181d01503c4120703c4480c03401c000c980031401098a9201600b08142d000080c0180d850b4010322004e91404138280d941c644941d640c0508620000f8402007001441c5203400004100f8000d1000c0101a202d0b0300c40d102c100000c06c58002c01c164100096510403c54815945230f11080c1c0d00c5c440d0050032105c0190341d9100c0280079241c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 752124667 1250 752123417 752123447
    0x130f031b05010206130203070306060f030212030a05032706090d0f0804021c14030313060c0305040b04080d060e09010609050f0106080705090a1d040c0b070b01030f060b090106 77
    0x414000c0342526030411a801100c205034000c0030b01d901c03204c0c50080345183c1903108036458441c4440000008039240602c20040602400d08035800d440c50040c0403d803080380c3d40303500700c40c0c008012410000d60003500f940d400a4510030700030155021b0101d2102524003410185202e0302c110420001c6041c4000b428000802281d62034080949010905440da604180c400a40c00b124600003044540340c0c0d06102c4211500070406d5505512447c2c00d4a411a80252203038406122064030600612a090048020006103403408020920740f40d02c5000500d4406040100440c0c07001801006020568100101a0541c0000e401c5036083c8840e42c18024806071040c5c44100d402c0c8000030740d00d198031016250484200b0344032201150b036441c7c0101c410390700068409038040d400e0140440e072201445501041d00d1724058040640782428103261118031100c1e8001212071a040050390001542d0000c01d604490344201707000d002c0800c0d841d0400c00340c0440d60245401010070000014215440100040c030321503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 752125917 1250 752124667 752124683
    0x60a0b040b0303131208040f060e0102061608061e061606050901111804180602070b010807180b060706050c25030801050904030908010c0512090a0f17130f03 69
    0x81c001082c10740364041c1d001076480c402e02116080150741c07060859421114030456040e0b1a1603226003042a030803d0b60781004000940b50f4185414658040204e5600001208110200194000c00041c0200b0005042c14019107614412084c0c10b009000e1001100f4401402c0701d4650200301d480845500340c0c981c0617101ca030f040c040440e90118040c85050101650450b0343c514100040808007400703182901d078030780c001e5a5150754401c00219205000c51085c8902809a40c070f24103400e02c030340700031010303040088150048101001200f02c04a00e40a80035508076010641e064044006211030042d80d10180181d81800f080201a0029100a25004d201032011000080704400c0e01c0840e043d80b8540200490350b0b0130014420792801030312081d4810b110345440e406035901d808041d400e45a4403811980810700100d00040301c2d0054001080d401600300b001801c010724130352580c0002000f030800140c000c0b0003140d0903000c80060740d001c8803903240016041e444601d6072120142d0104c03500748001d880d549 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 752127167 1250 752125917 752125931
    0x180a06110f210d0603050607021b0a03020f0918030307050a0347030105040c0303020d0305060607080306030a0f0503130b0c100213030c18050a05040218181516360305060a0b04 77
    0x11800d1103040060f66000f4020381905003070310b0280300d60110050150701c800d094300c060b0380c44613106c10001588a6055941e0b9180c9440300d03854083d054840480b00050010302e48100000100c0c0306005042d03201c1740b00c802342041d2503080140f4084c201c405018454255091070100b10a0002c0e0000303220490303100c8d80c00c60703c4603081c248085003100d4058428560014040048502090000f806550840300050030f48103c20080d03680c0070035144409401725004d401c08a030003c1c807100c601d44000028040c09440078617041c0207860032034980e140340a00d240704a0f4003003040711100c90300d0b04480018550145500742c0c01d640300c51b4040820a80c0d0514480d4103410003002507464421402230a0003240d01402480c005e000094490004a08c0141041e0b2040b08404641c242001c0030404403507040c5031401c8080141c04c00d00101409001c1860180087c4007290580000b80e000304000705132600c2d810605001c175904019005002d400b0301d584050141e104001c10700a0400a6038021080300c030040380d0030000e034 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 752128417 1250 752127167 752127169
    0x10e0d08090f030316171005040e0708060a0906140c03010f1703090f0102030d021201210b07230703020c0a06180b180a06110f210d0603050607021b 65
    0x20b5018004800619002800802c1c181244107080c1c4480d0846820a0300d403106d0f21200b0000c030040c0440300c4110384400c1d01c0023006642030034418501740c0c80c00d52010b01207003400c00403100c0c0c7c0c8501c00b6090084080c0d842601905004142e445419070413140c80d01c41c2c9030343c02e1031151600b885c1c00c2070180c00741c01222040005010100c3c07403074407048010300d03402450520082d00200b0111a080741011419070204000200e00e54955100a0550112000c0d074040307103504140c0060b503044440300304040c203404803c40213000706001c910110f601c0000d52406a014843c0c0381c540070042c8803007100c0350000e803a000c40e0704010142c0114040109210648810f03c000307070b6074a811280340181c0c1c04031000703c1c40005014005600030a0042a4240e180103040300304030107a1001c9100f6074050361017840080d00300820012641e4060007004560420000108100798082200280079600f007414500307155000110743e041c3c00c031150401d00c0290740203000c0d0f640901c0e114030080c1d12141400709103d203121407400c1e800c41d0b03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 752129667 1250 752128417 752128423
    0x10506030109020d020103020703020f0d030c02060603210304140a210807090b0a030e031b060c1305100e0a140117103305070209090a120302030c0c010e0d0809 70
    0x290f400030030081005919800540003548000c50541c01c5000d0700a0400e80c0400420000040d559580d400064200030382c60001e0600d100605070501c00d41100a24001080c2015220850313039160303840c86a52a119403401551141e08480340020501503400c0b0441423101240310740d01c50851522056404110218040b1000101103404102240c59401c00348062041c036405072416982c1070030700140781c801c01e8564038996085125420150700710b0b1200c112140005000d480d80101d07180005609080002009262071a8140240c0e406000f50034107502c8002c3c03280304000c00c203103070103040b407000c4a403682444000b075040107003403502140c01210940b0300045409555881012080f017010340d41410036035508000680382003018818450b00010000c0c0d40c3c0c480851070011030386170b01c0d9540c0c0ca0f4214418400000c1c00100740500b15001720502c03e011422001482032440200d14005a60750703202c280c0b40c83c55019844031b03505690311708442c400b45040000b580d84820490b686540296076100032151780c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 752130917 1250 752129667 752129681
    0x6092d03020a08090f0a3f020904060f05040501050103030201110a021504050f03270a0608040b040204180606050418030906050a02120d020a120506011d06091c050105060301 76
    0x30050740a0794468001c0341104000d400340b844e008042d1602c00081c035002441800c505d802c002021404258580301060421341c40006910b8841050300000c20072950070645035506070f070b0190280c06841c00080811410b135002d50b1130b070201c50504000604107418018000e10017400100c1c050762a0404000880642c3c01c252a00b941c2150300420200c5030898121030001800350007107a0700d20071400003d2040c1c0f41840501140301d61207080d034903000202c5030095089800c0045942c09224240c609006250f03002c6c0582d039005810101c0d40c082c1d500c440c0f001c5001054040c0760340c3d110000030892502000503c0e000f8130200c03007085609015680c0040703e000800e1160020040c0887c1d18210100840d900901c064084607006005480b407050403600d05407250342c03011400d2002d25a000501000c840e8000d0010980750480d98001c111501d40320002903d41040d802c114540894910b0301e040f80c5503180b0088640d03102c40a08103070b180c040c0310004181c07811801e000442d030399420440055000d05052003001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 752132167 1250 752130917 752130923
    0x516120314060a05040e0c2205060a0f090b1f03020a0201140610110109020405011502060702010e03090f1c050102030f01170a081804050709150908030a050a090306092d 74
    0x400d03d145440c08002c020070180340080117501410002c00c60b42d039120012110b00858854998030a00c0103607000c1b01c203d070780c020841c5115103200700041c0300a1000024102c152a28550001905080c0030000790200c641900712034101040c45c01c03020702c210b0741600600790a074030350f80007480000850850300350131400840d999504620a1240c402d106c500c2408014401180c401c0006007000d0660086001d0f00c8090300840181c8007502d4500c00403030b81c108501c5900c929188000c04c034148014111544074450212154441c0c48c2040314024941d440e42254102c1016030314800040070360903c0d00f94086c3d08200c805036001c1e28208000103800342c810f43d010a0b54081c40015100c00c0c0010391b1650781640004505400084c00880d04e40c3c0e5a80f514400c3c0d82c00313903030302e034032a4502d09141c001c0080105022503100c104102d268401000802c0000056844141d0302d420251344860994604440001e01544090f2080781031409040c1440046c84000702c80360f044030b035101c01d01910b04503110100d0b40c0780e031001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 752133417 1250 752132167 752132179
    0x14150c041a190e060d0207050a03260103170c0322061103030109020a2f011107031e0c051c0f1e0c050712030203090306071e030507051612031406 64
    0x1445140740f003a61020352a183c0280460300300419840800201d8008807401c0702d041e480001c04106142d00030101100640b05406a9102e035032800544131303801c000c107100051292032080184540b041c4501c0c1603070138040fa5101200d4650308401c101911448042600c00f4000140c8030001c0346041c4201800011440ba42006500c4c0d039103880c00d8000254810b2800d0800c01c640b420000c41400e4010143d0440c40348241d40d41da6101440001c070f64210703581a00e000c3d40d24030b002c109100020307801120034500e02c901014881c400803030103a400d40306400c184000900c24060b003001030601c0c00003c40b1a00c0000c0300340d0b8980b00304034403441c0c8c151000c1200c0f01541801c41b20440f40d01a00c0c03882480103482c07941c0b013481525650f9544840540800d103c0c00700c21400340e00042503040c1c05080c1000241c0d4040d1507803501c10302502207005d0303030b4107002c80071115801015119400204070703034012400c88480c0042c11400d40045849810f2100440e0845e5040030000390500303e104860280341c0ec2801c0c094003009001c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 752134667 1250 752133417 752133457
    0x41d090303160903060905101a37080d08090d1d040b040c02070512060403080708070215010f0611010b03030a0c03090b0f040f0b041214150c041a 64
    0x8120500c58940b00e8070080126485021000070380d14001c4800c054032681c004c10b048070f11410742d034081d5020310510440c0c1802e8a0181c2c502c559545840f03a03444002d52200c1c8581131040c03814188001560788100f07402190004000545010024901c010807100da40e480c4d8403921a100c9950f102c51041141c500010710012510b100460092100e080c4040300500c0003800e00454804a000e69404078108000b58212120410450500400c0d2039481c0c48000d000e064a46060380e80907284030f202400d10b004010040b40000caa4034000c10296254002811110b9103640e556035003000c038201c840c00f80c0000119129080c41c0d20203414001c264400c50010060b5080461042045442c5602e00030182e0800280c58000910183d40200030808003a2580c000390341d9034204125211084c00c3c6500c400d0404408006c1045145110a1b070580c0c650303804001c1185c140b4000310b0b81703464020740003100c7c02e051070310401740301c0090001802403081b280310304248111140314002c4800c4070700074000300480d40e01440740 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 752135917 1250 752134667 752134681
    0x31b090402090c091305010942090603050d030e1902151210080c010c03020a06020306062b05070207030305070b180624090106050712050c0109030302041d090303 71
    0x100d040d0700c01c0e840c50240b4102080b44c00054010100101150400341d6030320014400600d0130b000c0d1501e00214207143c403048261100000780f910a080980b8400c4240d410340c601300048141110740000d00c40e910301032010039260b040150b00c48543c20b0b1520301003890b044194030b10039000b01c0c000c1c0580d00602c0c003c40c6540703540d4080c06001007a8024014600c0d4040007000b14105420801601810703042450012a9041c2a001d628140b203c00245050020341c07446d03a400a64000781d01b0000e294052000741e1242c40c1c1c000030585034050380703284510038101d203d1004040b00408442e50003510b04801c080c00961181038050ba00d0303000ca40405070006004006100204411070310982c0c0143c0211700303a0004d840e0b401c41041c10308c04180c0c2e180c04030f04200030b41544074a80c1002c1c252540300088414610f0f652504030003800500c10084000c020562511800e0701e194041c106446550464030020f0201540502d00217009611034040c43c1c40011302007982c28080a14584d000d441002c6140c015851900c4600c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 752137167 1250 752135917 752135929
    0x90a0b04090c0309052e0e01060e060d0803070e041d060402012d0c1a0115111204090b0d020a120b0a0506090f040501091b0e0a050907050103091a040c05031b090402 72
    0x8086d07050035560316010346001c098610480070580c0d942c80002543c3c0e13040141020416202810b030500c00c0c00c01da8412008070350100c003200d0b0030100a0074800003a41051000c10003804a002001d0107c042c60240c4003402c0c0800b00701030344618400d07a60804090718541c0c803000b509a01d414034880d0b1084000f403014006015140310f811050040c1c40d0460705948034141100390110903002220741940c030b080802c1400c0d030081a01406170a0302e4000d0410340c06c1c03200300400c050040e80302e04802540c0350900c45205844059800e505550080e22009071152580c0e0500604d46030030300c2c12a103021042002505c4426a44500ca000e20802880c201700ca44401650400c80364000e4802d580c15581d81700c40400240840200d1102280681d2420802c1450443d10980088008201d107610074140410040c4820005c00d0581c1590402d090018003000039080400921440303c00412040c0150300600c02840740804924049032011000c0307610610441c101c4400c0745194240042e0000718040224006181103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 752138417 1250 752137167 752137213
    0x6070309200d0b0c0421050a0b07051c0c1b0221070b070b0a0b010c021810180902041b05090411160c05030c01210c05090a0b04090c030905 61
    0x10034000c4400300e02d0f2a00b002d085020f50b080715080304001410092103012520321103a509269040faa042001515078580701e04903c10b009282110450005a01d20702410a45291140a40581c250141c0c41d4001c60001d100130700740000410000c00d84002a01180e00c0c041c25075079400390041984620200701301424041ca14040306043c0181e6501147c003c03803200203008007074002c3d07100100034100154800b04071064506824100000c844205000d6291104410410756007061100b1403956100700b070280030042c03034000324407652034074119040342e4150750001c0c8410303402100c007003218806000c03046a00480005503180450018011041c65141540c000c2081c05081e0803264a0310500e8460408107401c1020300701c422507000f40701400903050400c48004818000c1c02c1031065004044401d000301e618200d4201c01240c1c5915450b050240708000b41d0340c4004d0080e221400c40c1d501d0301c1d04e080709600903008040042d440d110848445600c24000c02c1200c680020250001690b810720000c110704030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 752139667 1250 752138417 752138419
    0x812070602120f01060306050d0b0f090c041e050c0901230f040303030906050c0309031b070f0e01090c0509130b190f0609050f0609013507020607030920 67
    0x109000290b5450a4500d00703500c914a4006011510360500764007408494203604454002d0085100740d100090201d050107401c4401081c0b11140d650fa00c080d074a2402080100c40c680183c205140f892642003817150780d100480c4100b005201a580c1c49100324220700506c501e0500281c0401254004c5500404002420601030561180b81040100c0d02c1d050950150307108400299462a41d5810b11406118540d0010891104e0310302e1414484a225500e000c1c020040d040308881c0d0040112640c01081034030010030b005c0f07007004031555840080c032400c08424481c035200301d030420b142090060b100d0030803915906402021190391802c440807850081c140103400c6504441101d590714240400040c400c1d004051024844102c181000c03001440e2030942c3d400980100b403c905244116510041510304440d0203117007548108420341105010b17034040041c208101a2041829007102048000340d91040baa40c0d000c45e00161201c00e0102c04850076840d01070000340d0300fa102e030000c0c0c0403001c01100d801c44c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 752140917 1250 752139667 752139671
    0x4021218100612060f05060f01121b080f09060103052a0d11030d140301050d0302030d0903031d060906011e0f1401091e06080a09060c090608010f08120706 68
    0x92540c0040341122443e030080c1c0079400c0040e2496041041c18011484c040020000c02d10080c1440b0003c108008828004035043c014030503502c284510030307036114035003204580c4200c581d000d02c0a030020700340f810156450903012440d00000307946030000140e45170482c1c2e440740003407580e0128940001c4a0307200700e500400711224410b2442e0042e944200c20b5140c0345003d00c2040301c0c000c400a0402d89042141106d0005000182941c07071004040403054a04441060f00c8000c07032403050b0b150490544c81401001c00f085444e00c0c1d00301c02410780c19032044090700303400390000d4000d101000b080c42e0740c1c0108130740c411002d80c000702c0148040103900106c1d602000c400824591032548441309501100303415046607000c3d140360441d10b8a03660b0b1083d040b10007400103040c1605000091200050550702034040d8034280011800403464910140d444040302c2d58110a00b00401caa18620082016445100f01d800240c400702c00405e4410310071030494215000840181512020340001c8141d54201900c03c0d10455 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 752142167 1250 752140917 752140933
    0x2090c0c011a01080709080c040b030703051207060b01030e0a200307030515100323070b04080a0501050109051003020f0d0c0b030106090902040b0f030417190e04021218 74
    0x301090061035254148565002d095003481e00005214420040c40e8004002024000f00800343c0e005c904250915002e0302c01161101902380803a20780402940014410320849030355940410002c0040c03d040781c45030383c1c01d00103000440011425209650364808103030308204950400200114444802717010040d403014840444240044d0414105900660386500303d600c202c20642d5603680e400da032091510594070102c5003507454203506034000f80a0a0b1003c1c6440301c00240c010020030605004001004120366201c2d1102030085d12110480340c00c071110741c04c1000100300c22803c1c0c0281031141c042c1c17901c0001400d01d03503020480c0c04116040f100d0303088803421070440c0102e6400110240504007528100b690395140250040c4400d0859202d903800c1c61040c4400e10003c500c0d44100e48000c07555440179905ea850390309003c400c0e51100103101c0000340d00081c00c2c0d410b4007560202c01c1414002502d68200540e800404e10080c0d10a42030b01400c13076418200001c10300c006820340703c151101482c04641c085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 752143417 1250 752142167 752142187
    0xc0303030112021825020111031008160e1b0c01021201031703010303050d0209040f091401060603050c12070c0b101a1908191b0305010b1602090c 64
    0x1039100b0703004884200301d001c50090541c00c2003103a1041100e80e29050a191380740151100031400d44068140e080c00b00c2a040081101d40700350404c003050800400340c00c3e5642464062000146518803440c0c0e8503014003007012586030b01c60b0142608442d189040c04165907251320b0120130548403004050010b1000340b040a48208091000d859441000c0151580780c1d410341c100311081c90380500604000d558100010310000b9404405d640d01d2114042015848410302400107014000089141e003500b40f401c3c40030410700683d47c00d40350486860400801ca00c9481d000220251401103408030100c080420600f551110808050390b4003650340d1400410340300007991205c190110030b590214045004101c1070000644081c10a03041c0d10021034550715003010300c00c80515100349481d180e400d1204610002d54202e180404012445008920800c60852800c400140c100b00c0400144002880c200011410b0044501180d80b1700b00240540102e00110394208a02c40400800c580c03580300c0c0c05c1c0045800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 752144667 1250 752143417 752143423
    0x1151107030b01032315060406030b090d0f0201060f05120322060306050d050d0c051903020303240a0e040201120c0f0305072f01060308040e0103030e090709050f030c03 74
    0x1e1441080c24860551460070328040f10200c01c0b0034132410102400c0403000e07094000034101040c0d4600031703201350b03280d942e0f4000030014000e031762010b401c10070f401040180316500455014125034098942c41414121103208034221006401404030001041c2000d014600c0e0000903080380f1064a4100c1e071800010400c030100d032250b00580c0e1032540750120070a11100750036004a6003d05400c1da00045c070342c6a00e4035240c2d6074440300318203d424021541405000d008041c081031280710740451882c01c3d82c0c003280c60002d650ba8002c580710003518a4200005035010107180c0f00346c14842008048203034150504810030b075400c00103001203042c030030310702140c1d603c0c401c1070301400d00182010f880740c2003101030102018013501c070000c00b45000c0000b2003081001d4112442084802c07695020b05144690521420382d5005043c00e81020300758207008100003511001241d4018140d0380700750707a8081c17500c094105100016000351a10804943c13198400e00c00350506980042a5510007011a40750124004c08641 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 752145917 1250 752144667 752144669
    0x307030b0a061214060109140c0309120c28020102070b0a0219080c100e03041406070b0f01061701060504060807020c0904110a080c031005060d05011103061302030f01151107 76
    0x50b404034114541009880a202090040401d15414803060b092580d00180c0c0b04401040209c1c5040c0100118081688c00c0118100c0741c040c05d92a1581e4200811a840c1d607101c0181c5010035850308807130a031003020311802d0402406941078000700300b0b950400c0e1885040d908403018140c00c601c201030103104600c440e0320f099800d0900803545c06035102660010780c1c1c00c1041501c004035009040102e08946d20748000b08840441e034041004200c0c40010600260003807041010140110030001e0610190000031907216048411580ba2240c40c02800c940307218070b0090912800c00420f50600c030411082d802080b10700e91015640c410f90b5442d40081e0001200303d03d050340c06880203c40d0000c04855418080154001342c4600c0d0000d00001b040e8000095035031074580300c2640a29102d802040f215110030003040e0005900c28020311048084808404035904200ca8084c8180d40300b9165080c3c0030840e2080340d001d00703080389041400b682442070030503402000d41c228904208903140c1d051124541401030384 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 752147167 1250 752145917 752145923
    0xb1c03030c0f0f0e010e01020c0405040602030919032f0f010f0b19030f020f091504150e04020d0203071e0302040c080f180304050a0611060a0b0307030b0a0612 70
    0x240c14078100c04020600580c003906102805000c50a00c00d1603500301c0511081c502c824a440c548500032440100d0800c032040805641160400003444100a00758010310b108a90010403540c1c3c07412950001d410f0482c0f03404014011541c441c044040c07907544000d00c0000140150388140e17204043c1d4807114905406111001b0251f50354412041004034640291440c4a108450b071112445000c03d542c0c400888038031000344200700402c414800c644601c80941c140c0744001342040c07000e00d0002000590448071a981501c601d140c014466400b1190524503425100e102506003c2a90740c4e901b44900aa030389c841c1640e040c841c0300c10003d40350b030b080c600c0300c0003540b401c1c90040651850352060000790b03542e040023901170090b00820406010307191803541c3d50010310102815000a51441070740e0030340c8141c0d0011900070b60102c002145054114501200c806030700d1045620955070b200e1000101c17105448060b0380350b00700f6a403c10108220445d000d40181c00e07050000381c8180d45181050321401404030031 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 752148417 1250 752147167 752147171
    0x1c0212090a0204111c05090f010905070609052205090a15140907030819090509010e011d06010f030e0709052d090304030f03051e041a0405130b1c0303 66
    0x301c011030402d8003e04d00c04080040f102c0e070a05030381d400a4003154020401000040342d0780d4001425031b0004106186240802c2c80081049032076506246442c1c4c1a24000c1c0000b09942c0340c400100381c10f0010800d405200400c8032b101c0c0100c5030b0711920f005000c025000a0492050641d9040031941044105241d4049100001404142c440d9001e55410300100300c2459a08a009d041001c50b102c20b040342c0030401c160346101e0901030039010070f540c481402d401058000320300700d00104402803241c810764140c3d490f1100c0010820001036a03840ca10310704680c418001250701c000e80340c1c071500a0b0414600e551058050310720711a10b45522030202d40d400c032290715182c80e036000810074429403103030000c00380e4130f640319800080d00d0308a5106a8921aa2200031300c5103034010100c6041c54400e0042e0b80d18990300e00d24030451405640b400c0d0140d500240076508402511140704009040c41000300e0701200c0d4058400940e5604c01c0c01c56100510b000b0000c1e41e0028102d1501c0300041c9044a09941c2480c030039100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 752149667 1250 752148417 752148433
    0x203060f06070c140a0e0403022d0c0f0607080c06040b181213090203240a0302030c1306050a08060718030b040f03230705060601030606051c021209 65
    0x812040da6108080580180c208026030000300350307041101402d0302e540c54403642c0da1108000c04034407259111350041039104a59420700c010941c0c042640d1984400081c00800074848804050002001da0344402145501001d040f5101d42007e000c03884540c83c000b4043c5042040d5078690803216402030141895a4120760100003c00c100501c210350080c149095900c01081742c2d03a601c136501c98a40801080c280d00100303003040c52041e961018405456a100c06546a040c100d44080d403a9800c45080680f1000b40f0200c4055420403601c148105c0350000c00501d1011a640e00b80207068030a4070004506079100d40012070140c0b6040160401030504000500080c58408002002e1300c6d0341110507a149450b1010400101d524a40c0058200f074108020707400006062500f65841c03401451082929120b01c03007005c004c500e6160203020258096000e41e55242c0d106001101100c819000c1e03400030400030f12a0f120540340703000040c030b89002d0035240140f03004041208601c10010841c1c1080e019448015 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 752150917 1250 752149667 752149669
    0xf0702070b071b1d0a0902150406020109140d05090103090c030210050d0f05010b040303050c070e0108100608030a09030f050c040906051503010b0f01030c0c020604060513060203030709270f020306 86
    0x90040040820103450724941c5891350164400703000c050404490380342c1310000c1c441590b8038a003480201d40c07290003210303545641d80c400203400381809070000d84003080034960005000b0f0001c01d505034200c0b41a91200d143c0342d81d42e0010b50080001200c01d982c102c204090110040e12060f0324042c8010258440c20740700d4504407180400d0316031a10081d44520f0408004004c0b00c0b115806a8041d00e900d410040e84400c0c2b464200c51a0075440d500c0f101154504400004080c0c0003c10b14140d0343c80381503010f1051544581120351b42e807140b090301c42d002481415040000c0380b2050388a00c3c8152040098600906007040010103580c1c0e184010f45140b55900d050005948503034410340d2902505600920411809200058520500d000d00905150300c0300c5481411500c40c5150f02062030b0700030107454945031602c4005160b90401e0810490640c00081d000c01c2311400042035a10446040d90303101002d03801e1074102c0381e8041182e000031117003200410014108500e5400b500d1489801d44800503241d2034aa8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 752152167 1250 752150917 752150963
    0x120501060e09070507020306010e25110f03032e08010606020c0a140f120a0f050c09091b2416060c050a0e120a0b040605010501180503060f0702070b07 66
    0x1908000134440c04008030001603c000c01d0980c11070320301d42c0320307540e11341d0f01c0c140b10081d8020034008412003d40c0c0d81040030a0250010704c503904108901d01105c1a03020041c3d40c50b5500d120544131070618001000d003c0f000e040c0011081c000700e03041007207081c501980e181e003800d0035034074140c0040000d60807131003000b00c0b1814910074050042840c006100c01c003c0a150105404200c0641d249004135100700b01c4e00e040c1c980802500c641e0030f0f400320400070280c07507505000d9280d54000911a2158404801050400d03030009550b000412083d500240b403809040100020107600008056200f480d0b03007000d880c0c1c0c0d0581d6010b00313614000c98100400c007407604e281440c1210305c80c1091740b050007c103104058059505c12102c8a075540240c554900c421061a003035032030700b01406c01c01400c0d01c0a20041004000540e00001d04a64083e29403c04003100c001d0707002a903070958041d95030587d0000b000031700e650441624954000d401030054503001600d0b010000c3c40c1d5441100b080e6480d040d04141100750040c06 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 752153417 1250 752152167 752152171
    0x7120201021002120601030c110a060605121c110106050406080d020105010b0a0905060d0e0106060c052b05030709080303280e0a0f05010216140f0a030801060f120501060e09 76
    0xc2d0108520b46021903240c113000c1000034041e18100341d5240d2165203058000e180c1c6500700251241100c214024900c1c0070400382429005140c0140d1520001c6500700b01c1c006111003008403001c11100e00d80301c0c106070840352108102a000460364031104001240c0d1140e1060b4005000608003505c1c461841d00c42c0642950810307400480400410019101002da1107807031002541c0c400c5850560b02e0710800382d80b8024064a5078000c21301c1d40703014400100307580c0241f001e03907065114009940c26007407403000401d4228840a1b030010f43c52941380b40e4010540c8248002d6038820f03545e007002050140c6480384e09146810440740d80c0c0304032030070040c041c0121290061040a00d0344583c001d001d504e17250344200e074461001c00f10040030104415404c008015080d016a2920140150300c418403440e28104052410035050500c102406540341e88a540302010400900c0303180c05845407050703646849011240060090800e10402801c2c1a0fa42c0c4400014016079000381011344c1c0b080045982e002c2001940100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 752154667 1250 752153417 752153443
    0xa0503041406060f0607020d1709190506030403030b060c0607020f011a03210c0d05040f0b03100b03070210020304060c0306050303070b040308220c030b0604110414040b030712020102 80
    0x20408000d1107559603141261004c0c41030310b0075605c4030481d2002c501a04000341c0c0042c003000c00708071480c0f8200c014002030049a14101d5800526a030040c00c02030103140903016480d0002c01c204001030109009410083c002d0134040c1c90f1501c0c1c090b40d00401804c0a1060f143d001c01038000607603203039000400b4003440f440d041620080d40040e42203071b00003030354419191000c400c204808820250003403094406403600c3c01d0101003518040321a803100103040b98058041c04503003100202020a00071012010341e481051042c180c2040c0d00d0070302280c4a2540c0004150780214818022a004064200d0014601852055001190040d440c0c0030282c10381e102c0703401c254020b50062000c40d0108007440c9a945c2c00c030343c05052800c0d035070703c0310100d1229980000c10004070a4000280c030004101c48410030800322405030b4146000b0752140300c01c020580ea14002c604980c680180030a0003050203070075081d800307054000d0000070a10303410004242440c19580c041044060b100380e015040d5601401038034100d9174 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 752155917 1250 752154667 752154673
    0x4120c03290c12060d050705034c0f02090d03050310300f02090705070b0c09180a0b0d0f06050a09031b14120a1b0201051c060302060a05030414 63
    0x2d20580c43c00705001c00034541845130000080e410103104003445080c0103010091f0984442402052600296a128950340125100710124548001403103925841494103496220000c2d02030b400000f00240442c02003081c031840c0c0c00c00440d012590703420380034441c4070301c640c9a0380d4030b03440c0440c500042a101a070107000c0c00f8140060b028403014402c12807400f200d924001f6641d5a03405802c0080d0085881c0000a42191084090080e001d8100f0301038450305110301884801a0381c0c89992481078003c02480c0358024080901d0020120000359125174844c006240001c0c1c0740407204c0000b21204542082a208500450080341c1400850700620354004100c480c00c1c48080541d5500805100300c5204031704011405148101c01c00c80e440020060b0b540d540c0e0101d030039200d800400308800e54401104200410f4040e0100301a4480700d021000e203103501615014100a28404042100100c0140340c2c41d200b6078032100880142c1d580005419681031a075250f07a100d2400c3d01e0111030a040343d1180c560303258 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 752157167 1250 752155917 752155927
    0x3010f06261801021e0909100b0910020c04091406130804031502120903090a081f020f040f0b0414041518020f030a1a010c050304120c03290c 62
    0x8081101e501d030308010394011500c0840020100d40d8020300070001c85110200068141c0c0810680030405401080000c8948800c1e0751101d00319103006d4641c52054203c84034081c0102c82a41c03038006a4410521621300603114009409000202200d00e03684048800074241e150003880404101b02082c1e1140d4210782070205102c860b290301089000340d10004104540707003130030140800c40d0342d015a0a4440380b1040344002c1e050614510317440742c005e007843c1802031201010005080c24001a04401440400564401c4587c0503010102a44c040c06009407541001c100c00a420400d80072544004c0039140045600e880c03c00d08007012001c074a40700544a141455524448420380d580820304607541d030022100188040354903036000c0c0c05203655081001901104011607154144c000780c41c1215521204a002ea01e0503006580c07000441c0e0028006a000340001d101909001092500440c01001d1182e1003e66980e50107010160140c03401c0407002d0b940094162140c5a0961250032203441d01da964100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 752158273 1106 752157167 752157227
    0xb040e0312041e0809120c150a0f031e0507260f0106050a2c0a09020a020624040906060905040b0708070c0209040b040311010203010f06 60
    0x19002c0b501c04140c10500e2448200d00c0381d6444200d5074148545c0100b400045c45000035070101d070784180704080c200b6507500d111b0103002481420030595100001c0400400f00d014422417441414100811781c01c000c004500d54007494181d0100c0005c1d683c0c2c07918800c650040c803810310804030b101c0044480a03060b41d05d0100512034291000c80071442d136038401c401c031003d10950340d2050000e10751014914151021500c0c0748000c0000001a141a00c010000680d402d0039030342c000c090b00c550014403442190b40600130664003c000003520040304020441d504c5d03002100c0301ca03040c030407640c0700004820030410fa0b100c4009410725010400640c074151a161002a00555004002c900f6950000b030146110f45c1c0e0300d0740e455038081e107403962a45803079441d00100b01c0090000c030184013807610701950700802440510b0081010b2050b10110b03514001001c3c01c04184100100c0500708001c1c945021 = true := by decide +kernel

theorem cover : BRFrame.Cov 751978417 752158273 := by
  have h0 := BRFrame.cov_init 751978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 751978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 751978417 ≤ n) (h2 : n < 752158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
