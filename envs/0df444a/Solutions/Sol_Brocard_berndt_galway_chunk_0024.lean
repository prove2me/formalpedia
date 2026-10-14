-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0024
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:25:16.274763+00:00
-- url     : https://prove2.me/submissions/d4d9696d-f243-4f83-817d-63f5bad954b0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 4136698 ≤ n < 4316554 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 4137948 1250 4136698 4136701
    0x10305060a0e04050604030e0315040b07020c04020d0608070506070308040209070909090c06180f06050706060b031815010308040e040602070c06050309070e040c0b0f0c010e071703030402010c020603 87
    0x4034007100582d500c01000b00601c0420b1100303004003c00c20b140190b000e6600c200038864090141995a1800c06030a250441013800007400f113a40100c0e181d80002c224410755101589440026081c3d0308943e0608094590b0340a0130441e85c58204140c0300100415a00d80b030910103d505d016002d90070003800a8000c14044002400c0c55200c0d503080c0c0c0107002c403901c0c01c2143c031940e4246428000000d020341e030702013884c5c8654280344c0e0a4001d00c90045070f110f141c3c645090750600350101c5060700800340c201c450b1a01c5680104c1d0125942e4085c600c20000224a0f0076008180c2007107900d001045100450b10580c41e400510200d48c1860881382900c2c0030030003da40342d840b1407900d00000d2103401c1c80a4212240744d180800c40b01d07071000c0214000d9015000700e1b400f8981b1001040d495141c02e071f4004000c2400d0220821209080ea4040c0c4600c0b160a80c81509020340c80c0703039031425500d2031204200b240c1c10082c1c4c01d00041907880c5104a200c2c0c241e01c011400d61900707500181001810030b1020340700704000f10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 4139198 1250 4137948 4137961
    0x603070906060905040513110f0102030903030304051c08040302070501050f0c03030906040605100b090405040201050c0708030903101e09020a090c0801050906010201090320070509130b091209010305 87
    0xa4802031802035801c11100e540e03144000e08001d401d003d00da200364100004212042d183c0c82000843e2030b04075600c40c80b40040300c810407151030942c0240605501080c000b03c41165418006903119501a001130300480448966407401181001600340611000f0720602020a0740003030402e090320004c1c00c0003966501d8103a4190101d02640c3c0172905180b000200704284a41c0100752075000b54410700051003580c54201400f00d02c1c42903802101205003040c85000502c3c90329420084e002801070408615051602041c2410520300c2e40000000da400081c000341c45003010098101c80080b0a0401c11061046064000c00b181d40400c04d0884d45441354403410540d920700c1c5121006003400041000811034821010f04600c000340714417031040030317004000f611950045c010a0b4038282d1698a1580d100300c105050208000c040d20a082640700d008004201da407102074900c1c3c0580c07803203407000101c22001d250009900f0002003150516807c6600c032001d034070f0307d2503050b550115070909020513070b9640e04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 4140448 1250 4139198 4139203
    0x6170f04080909010b0901020625030b15031314060402010e010c03090e0108100e01020405090415020903011103040204150b09100e0301050103080901020f010203071b02010e0310050105030c010c0c0e0603 89
    0x1010216400b1500f1000080e00d1171244000703018040c400c3e000e41d42ca0780c0d10f44100b020a0000036070b0f8110b15000d03d141c90700c840d0340700703520020511000400740c0900038403c41c0001c2d0240c01c1220040031042d0141c0700c103020702c40703900c4042e038102c00080c0c0240600d14090740003e0074150b251400c0c5041c000103440d00400c16028291010143c50690300011583da540e1458030703941e000140c400c4444514003002c1c03002101060084a0076140b020341488104d44507603031207070303c1c190b5940080c00e2013543c28001c025441d03030b003030250540e1440c443c0311007502d81c00c1500400040300c641142d0f60351100b040690400208480c0b03001e81d0300c2400101c0d490b141c450703403007402600c039001c441d03d02e0365155183c8000030080020b6000038143d001c40a0342103c0c02410f95100890807440161500400703e00d001c0001c00303503403070041400f018280c810301d4503661103603a40010034a440074103060b82c01c2607902d0f00010301250800300b140d03900705802440c1600d40d025141e1500b80000116018000040e81224002442078404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 4141698 1250 4140448 4140457
    0x109020405091e0708070510020a0501060608010f0504051005040b0103060302030f0a05010c05040b0706020d0608010218040e030a0503040f0507080304060302031501030204080c0904150204030602090a06170f0408 93
    0xc0c0052003280761580c4555214401c1d0142d400304003041034100c003010000007030010203583e040001402000d061208002d04403030300750911811071194108210025000b070013100001d100ca51a404034950501d514501e03010364a400041c0101d00c0d240400507058040c0c0c0d480e0048807030070703180010712225103001240686000c0d00069010b11800c0c0c0b9064254600140d040f282c24000e4000b00801c052404040310188901d220303c61502a05000c0c03540400d078641e00a0074500002800010360551b54480c10b03003640c000441c2442c080600d07140c0c0003801c3c14903010304180c5011a40c0a1072805080d5803010382507000142010300341244c83c00840007007242c1007000078060700009080f6900d0380d684201c0200a0b500485048e000300c9064100821654028026103041d80d004402401200049105001010070300034000d0307030a0504d00e2803500190b00707240f0091001d540182d0015079562000380c20320103103aa050b4445420000580001240081e003106a0790f080028218840344580b11820301c1c01c1103009 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 4142948 1250 4141698 4141703
    0x30706090215041202040e031608030c071703060a05010305060a09090218010b0c16030308040308041a010602030a141806031005100e030c01020616050a09080d0309020102060a02040f0302060c0109 86
    0xc1c0014003042d0204c8000d202240d2a100305c505003e200c0707002e1b101c540c89002e00924011810050201400050000f00c060342c0c0c030440e480440d604020168584182003100c480b100e51030b0000c0003060200d0f0342021010440500002e080501c0300741410008101c5040c85840f42e01e00c21075841128030119902d40a84000b800c0c1c40241c60540f550311920303482c5d110360150191016911407a20000c0380c00c100f4000c410200e90f01615100407659841d1019242c1aa0060044030000b207004c451031099840c80300f440f4003901890703005585800d07806030041c0c0110703a030035003541f005c013400d00070345c058000c1104070892040c2041d21b1450300d9440c0d004186010041a40046500c09451003100c0d00559002c0310481000808a084034030240011005a840d0401135882d840c0e034003241e1200307240c264001d1000304070401482c0b074196420359555410074100400c0c0c0c280701000035140c4d100001550b134101f00e01a00440800800c601c2d00346484014000082c031840000c0c0034900200f87d00703090107421b40c440301c0042e8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 4144198 1250 4142948 4142989
    0x2010302120a0209130b0603010501030504060f0e03030106170c030601030207030c0c0b0d0605010507050d03020a02070e01090f060501020706090e0402040204030f0605010e0106030e060402040e030c1b040c03020901020307060902 100
    0x51242581c400f0350008010540100c800000b6034800d6105401402c41201015001a255900b0180110094007000700103441c26611080e01e4075044081c1d10840c0b89014005015640303950400000500219102820030906402141401070100300c140840b6000b9030b090030010f07a0350840346001d03225420300358005406c000c1130b0400000d4102e1118000c100b16840c0c2401040b04a0303c802c01074641c0d0042080103040c69100c6082d000019029034000c007410301c1d4600440f0300e81035480c080d401022000760065218540c40710a81e103807c4c00c071070180070007a2409001500040d401d0140082020380700348111040707040c4901c04136080d519540e04a070091500510001c510340000d01740000900028403613090045000301c00060b01520900c5801003803206500900055103490b000c12001d8031400b8043e021a00003080401d02c41d0310100105440c081000c440003998111607c1000700304c803100f013681803e2600420400000d43c2e4003004540c1c42c03641c41000058081450b00100c0c503c4a0403d0412000c3c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 4145448 1250 4144198 4144201
    0x9030f0712020f090f041103010f021606050106031b03150b07030203070b0601020115031103010b100809010c080105090f07020f0115051302190807110712020102100c080a02070201030212 82
    0x3581221071544086000b43c4a800c02c8039410002e10031007280480701c1500703100341c40d00070800080c008107581c144600014000300f40003001040d01c004a03070000f1100340a400c80300307640c00708200d42800f6540c01002c05003070404c14410840001482500c08250403000c00d5680c940d03030b0b0b0054007886481400740907001c403000d49844e054503010350740b6440341c83c041d1003540701100011059072050084120031240c44180d21016441d5542d41300301c642491001640c59503c4515075061511240d070312102d0321001c0d40d119001c508100f060380d030840e020000c419080081d610014409515038100b1590481c00d1251032079160382d2000401c2781041d4100d54251465404c100e44c0f0b4107041c905650300425540f0445030490f94401203c80c4004078440e20720105060b19040101054660048034503030742c0008141860301040042603030040c03d19591f500306030412404444004150b59040100112010010804000d20b54030418080c000040c0242814501da400080310421a48a90140c494204010444103002d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 4146698 1250 4145448 4145459
    0xd0b0d0b04120c20040525050906040b0a1715010203070201050a0309170c0d030504050703110307170307140604050705041e090501050105010e030a031403070302040302060c06010e1609050609030f07 87
    0x2641d40c000314510a6040c0310100f80d01406101f012500f0300c1c840085040b001c68501c81c191019000b80011036442002071000254030203441005040c0c035034083d515691100c60580d0201c0d4001c03409043e4220017010300d1982d003460398000084903000e94090034802d0310740c3c03441d040440140c243c8000041940d40000106040b0b12040c00140c00313100c444074140ca00e405882c85080b0308031034044501401a0703100703040400c00f24020711031940480001a0980742402c3d15200300d90000444aa0a4102d5620008911301841040c1c80c0003148805500003401c0b1504058644540d02d54040c011140300d1560b0740c0c100c01049006001c0c0945252031004180485500c0b42440c5001b07010074070810b808120504441d14072850003140c640b02495140d1503040c4841480e40c0d180c1c802c0d07000100440c0a140c1d00304404005a43c4240c007403c03544241000810350380d8100ba011541c1031801070050320003054041d414843c82c0b6000030006059501c10748809846803191400285465488885a16180540100444c0d03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 4147948 1250 4146698 4146743
    0x30602070501090b130203030f130509090304050406060504030809150d090305030a06080d14030604060306020d0504020a0b0906042102040216050601120308010501030b01020c030d050d0b0d0b04120c 87
    0x181c4c0a18001e03582640c0e900102200075150400c000d500d42c0081109030300d84c135100c001900070700c040404c5200415841d4004264061800c1d91200c92517800841c040280d407400e4080c4d07170060304640c0b52050400d49540c0e1040b815005148205200700c000c130450300000d02c40b6074103440c081c10702201c060088003c54100601a6031040c0c61080c0500d080c0310003c80d29240009044010017507590741c4021140907007024110075000940300b01e501c651942ca000010401c240058402805590000980e6007064810848000910b078007400c0000d9003840540f41d59a00c82017514100c2c0c8c1421031b1070782540341e000c40000a03c44038080003540070303101048130400010440c03440b414142c031413000c85000341d03240c2091032a142035441d8020009400e100060041c0c3d442600105100300c1d06004071008644010002804c00b90b40309010f0000481c00b1076040304460140c024000e00c1e0105542040443e031031398488000c034440040000d00b401104410901071140700d400c51400941c1c10540c50f0300200880014100d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 4149198 1250 4147948 4147961
    0x519020a0210120609050708071b0c03080a020607020a0302030405040207050102040f03080310090b0f010e0105070605010306050727030b0402060c030304060f050a0e07050f0303041d010602070e07020303060108060a030602070501 100
    0x601c003624104d804114203500740301d401d0003178800c0c0d00caa00d4143c0c1d03a00d2041f100181c0101c00855181c2c10804c1c0d8000180c40e0410102c0510720a00c1010b0b10340320f14500c02490201c00a1003582190300240c2c0100220b41c021046405079030090fa400b583d522020304003140644125030013803038038506101000080c006c031040514080e110f0114410a49640e8a031030a06955080e910700d0b80c81021201444c18960040501c01c0d080c51044c100b05040100d207449007000c80300264000e80746180c982c4200500c0550066051114107911054080705240302c2ca0f00f090114441c1c003008100031700c0384001c1415961800103403503030186150100d990780c1c9400c2c9001005080348440303201d1045d09010100b15000f01500883c0d18141c1110020806107181c503040180c0602c42c040c1803038140c0070801011842400498070302e240d41c0b0401d600b90300103524040d4028a4003185600010840fa0740704280190190f02000f2280c01140034680b004283d00c1d00400a01c880d416035200400f0130340700040080c100541908100c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 4150448 1250 4149198 4149227
    0x1602010206010e0f06060304060603020402070c06020f120301140109080a0c030203070501050304080a0305060402090415030b090f0709050403020c0a03050109030801050f01020a080c0c09070203070606080304060519020a0210 98
    0x40d405641c3e80c2c0c00780d9415403003d031038440d008a6402d0000ba10307410100c014541c003d00900c004110241d40c1e2700850103da03c45c0d2025212000c2129090100b0350301084004120241c0c0341c020034200d000383c000c8a6043c08103004203002101e0781d82d440d034042c0e0321496905000d0145041910042c10191800c04120107040c44124064098030000103842d6008100307480c403d0707400c0079035985400f16105044000342002888140d11035820f1095819985030b620590f00442e6024001c10300b000d003182003126000360014002921a40440c0c0c3d40c41d80a0000304910045a850340300c042095207443c901642400035126045030420b560410000910378150003200c0924040d864003080e80c1d8852062254180300740f03150381c3c0564400c0580c40000f5028000415000c2030304000d4503690940c020000da084035050780c04c03100607400807840383c0500009201e204000d000c0040110b2901c0e24000b8050124040d000c14030740706c1e480c42d494540c0d82600901c0b000c1003041c0d00034610900100b1508018105d502c118900 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 4151698 1250 4150448 4150453
    0x20106080102070804052808010f0b030102031317090402030c0a0e01030b0a06050f04030b010807150207050102060f06010c050f01060f05010c02030a0609050a0510050403110a120f0905030316020102 87
    0x2402803010300c215001e0340d401809079407400b41400180074045841c103010303442c0c1080f103441780714001100c01c0008024210031000400c8107001816007005480c45200d1103440383e4410000c1c040348856071040c1c4d0f0f4550f03900111603402c0520b510a00c2080340200c02c50305811500001c104106c41400400501c000b01103a140d05101c0846030b0011800c481404814540200700b07034000b8000980070300e000d882d220b031109a10500e015201e91f1100d0030f40c202a03000c82003540c00003c060281100350b00b6150395445061005115940c60240003e5a848003e0141840102d0f9200800e241e640700e452040c0b00b040c1c201c07040351a80384141842c90300820243c41014611350300c80e031001c2013541c8a8850041281c1c1c0040040015030300c0c1e0b1302c810008043d41c201c211441d00c1054141030014006000b031450040c480e4034000340516082c100038216401682c0314110700d400400b05040064070000d0102d41e50700c0a840d025100e02103820042c1c5582410390481541844042000c04054200010000500e4400e909 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 4152948 1250 4151698 4151711
    0x170c04090608030702090408090604080703080c010c0815010c1a070f08060102030403230c0a0602010906060906050306070e061e07020a06030506010503150f060301030b06090c041d040203012a0201 86
    0x39469201d01604c4802588164004089400300710f0718000342881900080030316242c1680e5200d070034034119040d030049400a0002c0f4a03050060828420a51008502d08105003180b80c101c9603541c01914880c200742c140100c03480001d00f800310305000410490052000c0d0005400c01c20805860f04170106045800203114070001a05944048255001c0301c2e4003076840405440d03035810b1030389035810280d81c00829201b9500710003101d580301c6035141e00402c62900005201442410078506a0303046410682103c1c0c02d1000400081e2400929554030180da0320b040f030350701c4041100141c0c2611881300e00d900c2a01c001c5005169504203000102403003842200d40c003d8240c0d40390400e030280ca9044403181c2c0441c40600c0040c5200101d00450943d038440245000070b03502d003440c001100f981081c0c009075880503c8000300700003420403069842d0083c940c0c00886040074505860301400061f45281844102103410115046440075080141c090072041100e11581d1141e285144142d54200302c401c005609212 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 4154198 1250 4152948 4152959
    0x70c03080c1b0102030a020c15090303121005040204030f080913020d060501170603120307051312030e090907050105070203030403050307060209030d110c0405040302150403050408070518060907170c040906 90
    0x30446e103806c000c40d005031440301003183c100b250001e601d015014806904104611155030144000d089040e00c04444108509000e02e03100d10f040c9484d00203d004a05c10801880400d804000e010038560f4480c12050703480c1c080d10007080341d441514149001d001d0000c143c500b842038941c0c0000c41aa2400c0c3d1341d40300007200f08070080d11100f4050b05c904c2d8054000f400480301e42d07008c00b80210f0380045542404c925060a0100703001d880c40481d800300b00d128642c0b0362024100740d405a80c045000b03a085600c0074450510085031900c4450500c641410700100085400854800380160ba0083d6000303020b60b80c4642c002d08042019600480c01c043c0b00b070241c907004184080c014200d07800c001d0320a200070241c00d20101c00780802044054405d030b042d40302c0c07000040080d030306081078207128911070760320350352901c0c0360200031403400500350031291180e135080c205000002640c1c0c0c0180d0b4002c804451a18090b03c1d903c005440c06001480321101240181d020040c006a40b2401842241c3c2c0c0f100c1f00700907842d40c90707 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 4155448 1250 4154198 4154203
    0x1020315011404030204110c03030f1006030219050904140103050c01080606040602030414040207020306040c0501030e0106050603061306050a0605040e0105040e060a090c05060c0615010e030a08070c03080c1b0102 93
    0x74a80e110707500b0a2000b0301c054105540720082a08424110924240400c2e10052031358000301c1e16401144030b40f608200900c001d4000b0000280340390b0030103504108c00b6a036403584070b02c004840340c42000004200b100159843ea0400c1c000880c01400004141d6120b003000d0381c5909003110b01e140490000c1000c2172440c10841e040380c2c21101ca650203142480d0406107056040664907400e503600640038800c28002d82d500f4070055000394852811a5001891324001405455412040561036454900100419160441204d230b100104450303111503403050860003c010840740d004076810969440010071919003080c0100152441d011101c2c4150780e0703d50401003611207100d900310a940107000828590b18140d0000066584224100413040380c480002c281660400c0b201982180d00181c00d0060140c00703034030742c02007142007847c00d4506000c1010100e5a0b540800100a081010000320366051140a60408000e594031008132030741d40061000680c2e650300080000100000401008882507000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 4156698 1250 4155448 4155467
    0x302030409060f120b04020612010905060906061e030408040f0f08010f0203070e0f030708010c031d010504050a02011202041e03020102010c0c0308011502010608010504050105090f070303080109020903100603050102031501 97
    0x261160131800070030a640d000082000904200e070081014003080003a2000c1850060190402001c00240d9140690410040c80c0d000f134001b5000e21010000441e20094900603401c080d540b10b0a02c0e546e0f0344562802d12054443da5001006485d000c2e6404070303a890341d4101d8101246c101000038130450412900c018220311003541c401c008207044480000d07540c00c20000d0b90104100040c15555825603d450721804c3d078103da801d00d80007039a2982c8815207030004144804284440100811541c541030351900d03662810f0400190600604034042e00c0070036903e80440b009850b00c0d405240c2680d00c191076420400c903280c00100e002d0750800300c00c8a4454030413481c1e02c2e84550150340b80c401c035929180b0508401c03407020b0203100c115520b510020034949000d000380c60041d03101c0d0000092615001f603a840c1081840381020116812001c0c0400121390702c00421419256900d41c010b9954000500180c039140388200400c407018200075001050003010744c05144500c00082c10861404009401195003228 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 4157948 1250 4156698 4156709
    0x6090a1109010e0102010209030d020d11010902090103030c08040314030304060e1902040c0201060506040f1a040e0408090f0d06050106020106060309020a03080c150f061008060102100c09050604030302030409060f 93
    0xa00340070301480e80d84110b12052040c030041c0001444c0684180c042403d01c424420b03c0005a88407200c1c0c0c03500a50301c007000d01038102e034400c02089285c1c030541c00691100c0040c400a41040301c034059a406018000003103400950303100c8449010404815080354480c5c10454040e16040c1c81c141800c44800301c040b4210004000c003c4070f012909d036859007001700901c045288441117640e942d502140d55255040248013804140200c80f9083d890309110f102d240c880061038a000d080140800c0260b01403035075545811592254485894019407004203e206104880455010140358001130602c5083c0d8410740c16610705900074400c0d2521003205400380c9520110094002d1240c0b0001c001082d800c070080e2001111039010340740444203440381000d0003402502c1114160380d0880a0010518005030400c030825098180313100d46240ca140007035203407190705d08100c3d00c0a440b511808400752041d0201001381c01c1c000c040755100c9449050080d9660418003c00030f44030304c1d100c1c02007840c90b52000a28100ca2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 4159198 1250 4157948 4157981
    0x10302010c0311031903150b0703090905040501110403030e1002070f18110c1005070201150504020901030b040f0204031103060c0f0c03091c0b070804050303060f030a050307060506090a 81
    0x1e80d070364200e074003060018000c1041d000900c901002c0c0c03400891607007401d03c4c4554000c03442140e40d185942d100b801c580c1c000602841c0405c40d000000303400c4240c0c9421a00035100026240d0340b1420451301502e001c800f0300c68121350000d4040105508505583e41403641616200081d01c0101e01c00e0340d80382414050612080f03400d800c01c0040701181205642500c5c00300002080004001c66003150070740000b2000700c0140c0102002d0103046190388075465200750148003e024120402c0340e05161180180601e034041e07900003d901e11564000d0f0094440303076201800400841e112051640001c4d0000d002c2212951000048103006150004030b05010b58130501801380790074030b03403034001030141e0140141d500d060009000e041d6440e642c0d04002c1d84086126080d8000d0f40880b882c00440d1428000c14071800c1c80300352400d000100f00d0010640b070340450192030038014548900d000a29000285400803c1407000159840c2041b40c0d03904000e00031030054a4140c1640c6401c41031005550440c82c0040110 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 4160448 1250 4159198 4159217
    0x90506090903040b07050304050405040302030702010215061005180307090b03070b0708030708040309030f030f0917120307090e09030903060601020d05030a090f0605040303050f0604021612030608070806010501020d030501030201 100
    0x2052a00014805c0301d00c5034007200d1a003a070f40c5010a00341c4504940507000340e0408200c586c20740d6014410141d0b0000750b99034801c000d02e41000042c00d01c4503011000d504011022071074084103001e2542452003201d0080840704400d680309040c1c0c000d03101d401c408901034090208006246140070060310030080c0d1260b000c904660303c0120489281c50020010350810101c0e04001020a25004006103114002c2d910811843c0203640c001e0114400b0b5800211200300706a60310f03103001c501140c04817198060a01d00c42c0e5030740321020100e850070307141e8200302d603413190803010310480e41c200000400d13100c40c00341d043eaa051b5460000580e00c0d41c00c41000311010410400002d445c1e107189502c1035085612070000c11503001126103864013240c0c13040320b0850219689600f03002d8565100d012955000e44215029440e11100b160004e03010a035111004000350901c4a811f2811030003a000740026150300e03001c0302d50031550390f00156034030f52003881130038054011031103403c458901c00d000b210705072030b0103840b0420318 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 4161698 1250 4160448 4160459
    0x602030603010207080301090207060b0109060e1201020903070609140301050c040e04030309060c020102070506010f05030d081305010c0909050609060901121722050301150e0c040503010606030609050609090304 92
    0x195000518103941950300300681c6000810802c040c6018042013500140c03900c4907490032804a034061001a8180300c903a80b42000306035405844030a0300e00703041e1003e0095041d82900503029000341407103245c1c107005048010170940d51000c1500c00b1105200401000580e02000b49400c94205541c0521908002c100510090711070000054019200785400582c09038162900d1703007125400c000320340040c0d40014807038003070080400c109805810600000d6600900d03000019a64204000000702070004e03860001c0c42d01c0300020b21508416030003074000d110100480c0d50003081081b40c0c1c00741d2942c062404020400a080103003c091062a000d801c020303403a42000001c00410004030380448901843c94000061303845050040e0400d00150b99044040c06c80041402c000300f019900000d000b0b03072400c5048104032400d41c01100071641000150403654070b400440348020311954008680660030400300160040d0326612000032510000e10800407030f1240810400011420b543c1b608250380144400e000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 4162948 1250 4161698 4161701
    0x30a02010f0507060606050301180e0d030903030603050303070302210411010e04020706060b04080114040506040308040218040302060601030b0102030a0c080a050903070b0306030d0903051f0e010e060108010b0102030a05030406 99
    0x20010150300b0100d00304440f0703545890581d8102e4009034001440440104140512082d103145441c1c90301c2e006000308001c1514455403070b240458144100f5480d80c402c1014980240e01860265400c2019030340e0301e140c4000041c003c0c0d40101128103840c400081e11413000000315483d54010fa0f0b0004414440c080743d200110b40d0b060301c04042c154482d17030810101e00081e03103502c12940204000720085880d03034a06012103086944101c04204500d01c41010800042c8012a056a029526050400071a1564000f28841d1440000c01004a40c03181040c0000d06400040f0603110b940241e80c10300c682030f80b010049880380126901c29000c00c0d00001c14070002100c40025182031081441c01c14213090707000380000d19101107540040c106103000810f0201c242400c0c0101c122440060801c44069450341d0742d540ea0b2107030441c14070340f01c001030020200c80845081d0401460059503500034042c00c03c03607502e001d40310002881006a19881e0103040c032010b500202c01d44800d0701407910ba06055580d546c50303000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 4164198 1250 4162948 4162967
    0x90604080d06180c030f0902010e060a1106040b04020306010b07050604060e030903010908040306050105040b0907110c12060609010f06090603050603030702100503070809010615030b0d170d05010f05030a0201 91
    0x101055160800401c40d401c0151032407183d019000d2002c0303080c06514502508540c03094141c540d456040c0300c1d2aa0150b41c005641c00b45441054030103958030703100d192088804141c04400c60000d8022041070200f4402e001c000c06000714004c60581c0c0e5282d0340c403d00f440c41403041890007001e940014000501042056103c4403030080780c801940c4c41c1480d000000390860340302c0ae1044030090008602803052103150303c220303800b4180668042011301d8401e000140c542200a10300e50401407003001c1490200f0080c082d94211000142800005541007164261140c0c001c441d210b000e0103240e03000250503803284005c04111507041d140c0085550400d00124007400c001008660940700030040f190058407469840310b1250301d1660b602e0f8503800c16400080c8220006000c50b6016814850305012074001025100300010f81d504001820141c50408200e0303400c01d82401901c42060001c1d401072003581034000b458521780c0080d082144e40e80300d601921001500307005040d0142d000204000040d40602d0010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 4165448 1250 4164198 4164217
    0x10c030e0d0614070207090b03010204080307080c071206020403031b020109090902011806050a0f02030a05090f010c0204090309060e060c120309030c07090606030b0108070206070518060c0c0109050909060408 91
    0x450f0780c40100402d0244000d00f51030310030069014034010801c81c9010b1069000b219404c070300940ca0304d0702d40900c07540d403801091400f905400001400707070000c500c01c001101c020b06514850040e09502410010029005031100f80c0200e1444100780301243d07041c3c0c01000803d0ba050f160200760504140410f0001c1c86103079422418884c80d201340485084039040c5403c001e210564590f6a01c484a07200280448104540802590b0050040707404440e00102035400981c0142c130390425101071500101d40346a85501d001c0d40140c034143d09031040c1517004207600309452803078481a01c12011003003403120501c10300c4130455060b000000c0e85c43c24940c44000440e005051181180e003050b041c000140e09100e03440c0c0c07215050507a00d9500b000100e4040c02880300046090030000c52524046030003945512004203004200440000c15030714420a031140d415001c2d101030040c0e9201c0900d420015910100300090303e010507580b80300059107103805040107100d1b01007540941459150380d030300d5411940003885034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 4166698 1250 4165448 4165451
    0x3030b24031302090a0203060f030f030d0209010302190e010e0d0b040602070203030f0309010608060709030302030909040303060b0a0203030604060801020301030503271f030c08060a051309050102030103030507050c010c030e0d06 100
    0x1010b0160741e5102c100d03806420007490043c1d41e03081c00300c104202002d0f03461002c0d01a811000c294911441c010095500c03a140228016945100340d4004030000d00c5940044040c4281038543c111405604c0854844502400c0c6c85042004017100100031015241080041141ca00740c800680000d01c2c9030042d0500700d08c00340480e414029500010000382c1c1040741c0d8440c06a65405040000310f40c10494140c0080c1d20381030110384c1c5400c68900a4030383c813441c40315601800100010a041600c2580b1000051200303001081d100c41a0010094590703200340c034240e10440c20034502060010040c400c0b0b03812079500100a520b0520703006d40700342c44840040b03140c140f007415002151a035500c43c20283c2c085020103400025540d03c242d000a8100ca24041c100410040d107a0100122078913052102c0003901c0d07040b81c402c1c012010711030804004d0210510000c0155002000000802d5000009818007521410649101840c00c800445891601301400b4000403503044c0d8084180c00c14485104a00c4c0c0070300c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 4167948 1250 4166698 4166731
    0xb0d0209040f061103060109060f021005010b0c06010504110a120e01060905040b070207030308010501050d0f020a09030309080d050f0705030910020c030d09350a03020a03030b2403 79
    0x5804080110703015204801280845000c12185200342c1c0b0040080b0684d03503085050810008043c18041e006040038004c00d485d440201034000c0001d036200d88200030302481070750f85a81790320b88a0f4014078840512417280c900040b480e4a4140900f000902144250609011400808507078000415400ca004560746118101c0c00d010300b801040c01078102d407400030443d810945020030311000c1c0180340004541000d0b400344006540302c031410341182c5092a000303417203040600000300200601c0c07480c8000248005400c840f83e5400a40000459000341c40f84002140e444c00320a89501d290640b000004004000414240c190100580f50060041c0220717818002840c002c030362541c2c4604101d00250f40103140b10061303490300300041e18440c6201e2818001c0d551501d02ca4010100e58450b250440000c0c0130040513100c0440c1c02ca8185048201048404503501400d0194440e80000d500b500001e0401c04001250300300f8201140300300c202070185074505a62041e4004160701701401c2130f0601d00d000d20 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 4169198 1250 4167948 4167953
    0x80313050d03050709050904050d23030f0402031501030b0f2d10090c08010b160209010b040303081005060706090804051003020408010b0307030f080d0b0d030201020a030e031c0b0d 79
    0x101d01407241d01540c800140a04000401402108055106074441c0760078604100c0000c0c4007141c602d00c610002e007011034000f2090001c2d80ca80205803680c4840030100403040014100809990b0750066000750180d5600550100c480300d15801c0c24000980a41c282c0b101040001d92441841644001704940c034030348102d0407c8000794a11404a0140307100e880030000c1c00508000680300070000d00407004200440d0702200c80140c0251814814501e0102000c140c2c1401c0706101042200c0d00340d8000d105003803640c2c540303202030303060741007404240d0014400b9000107040d540f02c02d01500c10b481c0010030a0b1b04055090b61404064590010120f41c0c0c0c41081c000003c1c25180d030900215000c4013520003503212410302d0b00c554212002480710038420362060408001080d0070b00000c6510b19049142240d4070f0b4540e91012010300244c035075180d000500c0180d81014158198090054403250350740038050f001c800031266607a8000c6901c46107102d450000c030b05031900c56640c00344000f5500a440329002d1a0580c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 4170448 1250 4169198 4169203
    0x1020a1401020a0e0103060501021506060d020a0801080123010509060409060507051b0105060a1e0b03070c060c08010302030c06070302010e01060303090e010b03040803130501090b04031d010e03060408031305 91
    0x2403100300d030103030b4011a904800719001584296449030a03e0208846071074800000e5841280240c81d81c5a11030190200b00d00391121401c5507400c4048140c259520084035030018120f21013489504d802d0f501c3c0c05a0103003c118800503102c4580400b420f4030030325900f0708080008600300501040d40c07040d80c070403184001444a011356403154005842d6152519034503d03203141540e8064048a1980c0d140c1001c00805564040b2840c0aa40705c1c042545e07028214403041020a01c0250003078100000701008000409034496199100d40b40f1031142400784101c034003001d442072907081c04002c4d0325400200001490b400d014001d003218034040e100200d20400c42d10303022403c58969030030035400150307151018002e050006540758010415602620b24601c2c0c0307074448030010700024091005000d466400da005203d4250040e040c0250018a0034203e0f01b00761401034038454010880304134050b20364641541960150070410402c1d0b0002d400381041d55155940c107002ca074401006e54800190111807000810002c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 4171698 1250 4170448 4170473
    0x6040f0f0c11070e16020a0c08010b040b03010519020a0504030c030b0906010803030702030d110c01021c0506030705010c1401110706061d0408070201030507020c1314010812031501020a 81
    0x1400240c201c1001d003000703000030603900344646254800c400400031301d40074490040d070203510213a54204803c030a11080341410200c1c44090f00440940c030000c120402c0c1944000035110342120104210154501818280c801c126807080207c4001d40490402c041107030000d00e0603079000c1c5099841c090300c03a541c9202c0c81103950800c0d603c803003412040044481c410804c0b2030150034040000c60541c074290000035924854892038001c2c5d03030744071880035507245081000e98030400c51010096440d0807203102c00010307038100c1285009070b940c10074020a21506000c41e03044c007550010794804034449103a89800c0000541041c200e034040d9a60801200a01c4030b800c0075244192007040c001c2480e5207032000000b18540c6d60281e8036031281404052200059a0b002190101e540c20700740802c040e03503010070603030400c00b4006040307410041e9130454000d955a20f40c806d90340342c100c011900096980350103030140c2d10440903858840c00351040010414080690201d289040414030403200014525510341c41040c03007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 4172948 1250 4171698 4171721
    0x804150c020c1503040203061609030c06050306010306090e070603150306050708040c050414071805030609070f0b07021c060204090c030501060806010806130c0c05010c0c021302090306010306020306040f 89
    0x304200b824034226951600780d68180c070a15085040540010351034410260002124440d401140c0000602580c0000d0040d038001c044030440c1d0f44ea40901a00a40c4100c8526000a2420002280c81e000e103102c0c0f50420303000c4200400c90745041c40402d0380200001c0f004002846030074000000000c12500443c1d00ca240c41c3d03501e5101c90704061070130a10600c0c00d500514410703800d050305078208107045207a07550f0000c41407401c0103400a0314190400714a141d900f141d90140911410000204000a0b0f440304407a0b18900c1c0310342e25503a403040350b0224090f005c0300039032100f2282029203100228600a850040c002d2000601c0d15946000301001c484e05600782c140849c1c0c4802c0100415500400110ba00603400e090080b52450304000140c0f203115103072110162540e0740c4c02070003406c1d4800c0c0c0481025a030b100c0001c0140524811014195161285d002ca104801410038507200e81c0a60080d40d100310300c041c00400c02a4207564036000a504000e04a81d0060b94885d01d0203004c90b51070180140c0c3e00d0303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 4174198 1250 4172948 4172953
    0x10605060f070b0a05040b04030e0d0209040c080d020c060a11030f0310030204050603030c0a150e030f03010f080f03040302011b020d060603050705040c05040e09070e0a050105190501020c010804150c02 88
    0x84289031104a030800141304084035860300c4200004103840c3c448280d846175051800d65851100c880c0046c01e00100030b00069000422401084104039205031004292000c500450762803000074801240d42c1c070001d101180d000b1400b4411892818000c0001d004001c00241c203172401d03c6080803a00c88590400c803030b00006484403c50810550405118a40c0c0080c030640c007540c54403800d82c104a030356810144000f080b912404101081c01d40e880d900c214014050141580e50307a080900613150b07540c000380280d0a28580c20000041e054900203443c064400324280654103180c5103400540e444008040c0d80420496219003240061b554006001e6009104010004090341141041071420302190419030040303251492554075280c00c0b0b401d0f40c0444a218080c100681c3e11191400d00f801d6981c2e0145401032410410b1112002c50750300201c0c162442a103082a00001814819061301c4242c0300e511301581010440308529442604110780c40b43c05496140e45a10301c045da0740c4100c0d03000c3c001020058 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 4175448 1250 4174198 4174207
    0x60702010207120311120a060504060305010911030106061205041707051c020105070923030604030c11060301050d0305030a0b0a090b010201110306090106050318100501080c090103080f070302010605060f 89
    0x4015100d1040c40103d4034982040555440c544094084c4200b458101ca06028a800a6060009500030b003018090207401400740323656901e003160280c0b9142a0803030300d50751440d00c07598140c1014402c80d800c0f030703581c0d541e05803030305c6150700c122001440081c0040d500800f1810500b410010050000d0220301d125900502503114034180c18200d00c04000d04035001c40e4180307001d0054040c0c0c810008400e54a950501075109007452070346092254024500340c2d054046d420801060541181c10060445c1c052802e90103003524030b07803c004140c402402502e0307000f04501c0303190000c40d20460285504c0207a2100c0010303a10300f80000a4882c2c2000d5200305080c3c1d480700c50f910f0071964203010310320aa905a206490842c1000400604905014050b441c10058003000041903c091010301f2221200e00e0b20590f5080b42c2903804c3e4a0242000340201c54a5103d1100200314508050022904aa400c44610390400003881143c84a0340d1003040240e08564907a0800b09503903a030070005002ca00807011820b42e59 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 4176698 1250 4175448 4175453
    0x3060405070f0f0f09030b0109021e070b0c03061809030a0201060503070302060d020a02030f07080a030506060c0606040c090314060105010f050c0705010f051b060403021c090e0604060305060702010207 88
    0xa03990001c21407010001081c816075082c41d00480907405144607030618088914528008460000f0154406000094443d00004801e0160342c0105040a4202d03a454101490580c3c1020103124142c030092001d01788030001840302444c0390180d174120030010684601c0203540e400c0540c0940703054680f4138198000050100c0380300e809204100081c001a40a402254903640024409000d0789590088540d00010301074507862007441103614010242c0000c6850b519281800c803c580c0140c07900c8000300740741c0000700310549000c0c000d07501d145c100c8070010000380e6034680a00c40a03240707103032200c2c05000094402200017005028103010b40c0400030014243e9624140005041e6a40711a102c0c041c040c3c00c000c0c0c0c00da00813010500c502514001e081c401000f442100c402c603064428141c40440b10800c0040000564401290660180d40241d08403070000400c031b02c0b549103c10380c0509070b10204504000401c2403004440170301303910400c001e0000890b140d40e42c8425062070012944500140d50001e400b404 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 4177948 1250 4176698 4176701
    0xc020c0f04090201050f0a02120403030c020306060a03080720120a050c1002030409020c0703060603080306030c270a09050a0507060215010e270d090518040f08070606030204090305030604 82
    0x48120302200c05010741c03950380d00064800e00c00e014548a1407480001c07510384d4640204840e0500303079103a00344140d48550f41e08006002c5030085408a1180c001d0001141c05c80c94514150819241c01000da5807824090b41d480304010700708006241d10841d80c4281901096451749848400040d0207030240049610503d0001d04001000f10640e12036280b05680341005540003041e00c0903112000001603440703201d00682850404503a0000b803400e8106540070080210000103180517031b2040e022102820803000400200d03062800c40c0d220500f4484182d034151806086c13410703801445100000808900710303100d040c241a1060000d84807a4000d0504012003581049841c02e20708804401c8201035060030940e4a45100240c44e040c2056450340b0801c44918110300c2d41d890340e4242c201210805079000c28007810303c0403d8070038207100f801c1000103800ba0844141d440392086900c4502958426001d54039078400b0b0300b000c0401d03140035540398400300060b2901d03c5004d41c1140a500d40a450f4588501000b0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 4179198 1250 4177948 4177969
    0xa0603022a060402130e03070807050609060103021c0305070605010b090901060201020906040603050c12040c050406050d08040302040203040f05060703060311010c0201140d14010b03070314010806040b04060207060c020c 96
    0x1071401c4095045165850408129607400035411118030039403454059066004c0e20400781c28215a000004030fa00400041c0b00c000c2009900c51020f0722280c5d80c0b11080d13152541e000340b0010b904210089240c4000034541204810035034840c0c1440390138031000b6210441211400d802c19080750b0343c0001c24040f640b621681090040100344000d5241120200202d4810b0181e840f0324402d03d525000407502d100364040699a08031220350607025140b8281c113080c61484030501c0707902d009924082d000b15190170400b44580305a504145e005191034603540c01d00c002940700800035a12170000300c000c10000b0305d0070f01c8100d01400983e50b020481a085092400313040c500605404d05008a117040324005076000b00082c0e050300c10310740000d9110040300d42000080c04e51b4040c0041d243d501c040022030102d03d58005580641c0c1c8540c0d04022226683c11288c65400c42030145400b694044000240003800c50b1003029801031240c1400742c102413144d0748050a60340c10720004400360f04501503486c0300c1c2c10040b4010 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 4180448 1250 4179198 4179247
    0x11040509010b031b0702010c050a05010c030e0705010816021c020606010824040902040b03070306090c121e0602070204050903090103110a050d050406020c0a05030a090806060105030106030b01030b0a060302 90
    0x1d5140d424a100c01c4c2210458500404450520200d040310a5a0051004800300c0e60000c0682e00034844501d826030080c411184590040781ca0024904021900003413034001740c81040e140c4030102c0d12000d001d0307000c08034129601402c51283e50341d0181c0829140141d000300300c05507002000d050030a10000342c0701c0c410003081100c3c0d08044050031600a0340720b182c080c00d86d1405807000502c581a5002090140080003680c0c3d80500c1050340000c20032a01342c1c07101d4880ca0003440160f600c207032a0f5464113074407002140e010341080340c5c40c029840303a90a40c2901c880c0c918860907006160046035404039007520021180c41c02280c00210707460585581500803800d42080c1451600d01c0c0c0906500c0c05807183c01107a144040c0107a80310001410443c0d984d040b0380d4640fc0d9034045501c0b0160328940f0035038a9201c05200350004031344200c00079441400040103070154505840313a5003140e080038400c400030a240014241010346405100003651512811003003d070150f0340e40980c1d01c1c81402c0240c1c81c0e00c5080d8920303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 4181698 1250 4180448 4180469
    0x106030c0c0c060c0f0c0b0c010506030a020901060807020a050d03020c010e070602030313020d05010f0204150302030105091b0d060b03061e06030402090606040308040816080f06040201211104050901 87
    0x240004040841c40d40c103449090070200103069003410141710400b03603640010302905034500086203010b0f00c440549280844c54009021540d2050705061325030740d072000029080b02d2440c0c0144061030041c00580d510061900c1201d07520007c0717469081c50400401d407841c0c0401c0e4005080c01c1d8182080c080c0301e03030b8003050a0003420321500d0000001d58922000f8200800030500302e01480440d0f95000c000c140454005000303020030011240c00310000e40c418071502c0f00c40314103400d0441e140340c02402075904946c4010071100701555540d0207140c001944894110484000704080071070340f040c174800c0d05e010f0403100e040c10b40c0b00c1ca012b006101200142507010398009540840c42070707a50f903480741241d034000d0341640e051015440c1d8902059450246800082001c80b001c9800f041c0303c200080d85c08040c288000d004840240e0700c01c861760b260740c0c6845843e00c15801080c0010059401180c0c600d50790781003180034a0380303c0f002141070011144401c121600701400080d04104030724201d8080e41c094a04e1819 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 4182948 1250 4181698 4181717
    0x10305060f0120010905070906090b09010e0a050c120a06030209060102031e0c010e060106020c090f01060203030f040302070f03050a0203060901020c0703030e01020309040c030e0607050405010c0305090a0b0c060106030c 96
    0xc0c015414094603043c3d2114020320200d42e0b41030a4003c40580c6902500329103000d62103400520103010740c3e0042901407490301c10310a15601e042c8071600e049940692003003489459054000303000d00001820f20304104010402c1a801c10a0b8a200381d00c2142c201c0030000c0c846044d4810800c107540c001e08500e046500503c01041094400d807100c1c0c05800c03140380d80071303982c1100e9842a40900501103103200940115400050016004240221500000c4808038890758905004184096080c0600760059009000007030700b00c403282c16500c2c0c002d8000d00445000c15610449020b10300415001280d00f40c01069141c0c0031801c4c00c014140d002071688000307500304801d00d4580c0da601c0906100150401014002c030040d40d0b4000c1c81100e042c4e000c060400d10210100380c0b03004e03003e07000c0c8104016141c411080010811032082040d602501ea05940c0d101044242c1d8404030f417113410407040c4030350200c06440000f4000000038000c0a10601180141c0010f41c544030707028049640c58001c03c0c05002001c10b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 4184198 1250 4182948 4182979
    0x606030f03090d050c040204061e0516030302030703090203030301150305090c01020c0904031101021204021c08040b13150e1002060609010b0c01020c0708070f0b1606050402060c010207060204030201030506 90
    0x94a4100d0b0040d070301d40d1508007060902c2c6140800041010350030034400240460441d038410307400584800c1c80700d54107410f8031031004126082d204166104003441c0000b9003d400080c402d80045800428502c1d002c11250140c0d00060f0a40d0300a912040b401d1035002c41c945130032038041c0202782c1d2007118400542500100c80c00043d440302c09030103502c0d01c15a40c4000040130580602e0100c604034401000031501c440840240f90703003010081d43d051780724580090003120705601d0021030f25641a4850314040c00c0601c0c3c0940c0d0a1103820030743c80c1d0f401d982d003001030200d600d41c1c0f81e030301010403003102c0e9442040c02c1d81c082c0103001a07445032580820071904154200040f40c0c599100e414111124031004581d945400c00500d4024010548044844d010343c0030b0004000c400002e020013560303804400061340b6030740d61020344040d10030b070002c03041e0b0b914445506101140460303010651040c006050503240c0040003401c6803c9170b02010007141c20580c003207028015568180304d4283c2c402419514240d00d1403031710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 4185448 1250 4184198 4184203
    0x3020a0501030902120601030302210a020c090703090f0501050a110f040b090622050102060a02040e0402060c03040810020d0c050304020d02040902030106152003040308040b090102031201030b04050606030f 90
    0x140540e40c14903481c0d0321008119210071045440a06804081d2035080d6102c0c038000b9211001140c0c07050400c41c010000380162164070048904040054000b02500d500e414240030487e0301c000c0000090555503151000494942e101c281c41b90f91080c000069030340351403000c440843d0300741c0061910112082c05000b0720b4503030b984202c03800d4461400c00b80d6281c1d50548001141c5104242e0425104142c6840150225481041040684900742c0039600e690740c0310340403542203005038400c640f5040e20140100c0c0140c10400000c10780448240141c0e4903064603081c1d110705e440030707080c02545166030004034900c2500941c42588905009032920600c2c50520340c0024005031504140039100d15640c440c800c0c110750782584420000c121b84400804101c0402802074080b07800300c81054419858010031080b40030002c0100c6003500d0344040400d040c20b0500c1c22440454212841840c15403208106964982e0101c03a5514002d51052405450714541890100c1c03c264000d00024026400f001c0c0c203d00d0602c02 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 4186698 1250 4185448 4185469
    0xc0307060504111806040c081302010e0d0606060206150a03030c150b040509010e010b030a0804030f0501060506040902070203010b0102010510090b03010902060a02060612030705060a0b01020a05120c070608010302 93
    0x403100c0400c09403124140702100c01441244298031400c00001240c10346034000d0494802c0c4e20488003081084004842641c12030740454070352400540e9802e0580041d8011540304c401a88041c1415000c8446070b629201181d200c0e0b040301d00568088010071546803200000c20a20031010340340340010a00c1d541d00986010a0340d8001018403002e0b801e404d490094960085071034500c018030520030360606a8450f4001c0c1004280100103500342402d403196410300160b040300d950340c0003405901e0145103450360007103c11041d0040743c4a54803031800007401d47d02e04010348050008401e005945d6035082c81050f0071525588031440c15641420b0400051585003a80502106e80d510004500305003107000090041c400164000e44c00103001c94084071080d070010382c15104210583c3c041c030090540040d0b4a68034003820030010700c81d600400000d058107403d9004014031407010b00403614201d05541d00e0700d041030004226a5030320240480c007410350700350400c801001402c150528900d0795045030041174102d0305 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 4187948 1250 4186698 4186703
    0x20607030506011214060a090605030a06020306061303081207030b030d030c020106030204060b090301060f030f020d060b0603090a0c060f05040306090c05060c010605011707050a0f0e0303070b0f0c0c0307 89
    0x1664400224030f40d0080d90211990200440d080044e1180c000b45e942c000042641c5190117010071102c01b043e03240b1588215415500d0040042140d01c0c03807990b031640070b503000a1905400543c14044000401000800980514400c01c107054035240c0c000c0c3c0401449600030241c01c2051308003040b4985a40303021584107110a041e10700410b00070001c007070990150240390300081d0810314250000a40044500c040c2200d2034040b4001d118440d51a100c041d80c0c081c0d940005004500810396842c014a410f8800441080c0f1810010415141e0300700005c081d0b400448500a150300035842980030420b0881040000c1d11642c1402c228080607000020901e00841c04002c0503150b03181480002d201c200110b800082c14001e12555990000d618054060012441030a003c03c021280d54140510b540e90303800d1003242950740381808c105101008403071703060030b50340b1319420b000c070014100e90a501c0c240010119140203a042115170705004030200ca190710020309030b8944040600c640b00c14900d020049448154 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 4189198 1250 4187948 4187951
    0x302031302010f02010e030d0209040b06090604090203090123040c06020d0c02040e0c06040305030a030b0906011409040912030603030801080304030302120a050c0709050105011209080d0e030d060f03050d030c02060703 95
    0x10f803c1d074060780108010241c0c1010751002150071407010a0b180c0041c811940c0c1554180700400404062080c0c43c0203003203c40d6405641404140080c000e2071340610341c441003460001c600102e00d4125041160034203140180f040b0080c1041100b031110036544000206206c2c401002031200031240142540c8490b080248100d45940c40080030030000c1002d20b9034804003d0229a85990380e192183c2d40f940141d800c000071a080201c516244d24051461b18403a00040c0c54802040e0108a01074900364407202807541e016a55041d00e602182d242196611202c00c44d888c005411819410007400917001688000f040f6403041105000190703020841003481180810215107556900800391610b000301861110188070744180020a9005c039001a41200c1c42030701d45a0110748410f0042c0261002100080e250300320802c0721106286096012800002d5000142d03801c00f500320480d4800c0c0c03a00c941c4000e80300031280c030701841880707018030080f40c18410754101000f94101d0360502071340701d040007001e440c01e05 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 4190448 1250 4189198 4189217
    0x70605070309090608060105130605030c04020a031503060203060f060304050a02010c0302070b0d0203180307020f010e06070b040b040201020c01020a0b04060b0d080304120207050303090312070f0506070c030f030203130201 97
    0x500030026075014045840c0e0522144c1d0329050740a03510a0244580c078400e190850100000402d1485080f00f41e440180190225900040c24000694030203840081019510302030000c00d046800401000387d071082d031001d656800d00e04200100d903403020004500c1441c04005200006400080c4002d4a50f82070820141c0034103542002d90801e8040c3c3d0040600d50380025880c210440c0303d80c003c0d44241703042d02000d040900841d981503580e000e5018020742050404600014960141c034080c1d078001c00c01000f140c500381d400d9842060f40c200550b0100d90182d54142840115078040c040350200550030720080a80002c103445021500c080039101504580e43c07008504402d8440b6110003485540114004e0351340d0410340b03400d40342c182c41e01350707508010701580c0f1010540f85000700403100e500100070028800d407142d985031000706901c49441219100100c1050100141d01400140c0c0700b04d5450722003042011903070a02034001880303910b0140416204101b0400c01c0801d000540300c0054084c601500c80 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 4191698 1250 4190448 4190453
    0xc03090f040b0a0909050709091101030f020c0109080c06090a020604091a0d03050c06010b0307090b030901020903010c0207060306060c0f1202010e0f0d090f06050301050607110616140a0507060507 86
    0x1407400d8121030f908040b4003031001c40c00103550f81042c03100c14400d41c100c6002c50f586441003012110f0380da800a104800007105c101496100350004408010002c2c80103103007800d40302007d400c49031030460855011307801042004030203400f8014180d100c1603840182c2200c64056001550310711842c002c0c20352083c1d0300c40d01e042c141032515800010034040600740d925092286c0c20060003d401585d40340d07610748507590001c144c0d40d02c210182d0b4000d11640d1600d411150900c40344071825003000301143d00c10740d801c0c81485500c2c0d4090040d040c0d2407046401402d0540d05240004098500c15045101401030444150001071030ba2491100c00b9900030023400520204460103c0c09401d1800b2998524420761141145d1100041240000785403503880d41030200b07070345502d901c80780c20f2123110340e40100d5401e10040040e400c09100a11040b440b030820400540380d040700040e0303650443c640c07001c0030100d4030704400c007001a000cc1c07200007211408005e101945180c3d803550f0f40c4241c0307070040d1f108010012801004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 4192948 1250 4191698 4191701
    0x50115050c0a0c1701050a1a0f010216060f0f0507030210020304030e040603081801080402090a05040213060303020102030f01050f0a03030e040e0102070b060306070804050a020108060607120e1002030c03090f04 92
    0x72040d0f07115040051059035500780e21400781044244504951800c4045565050315100704505040480038007032402d403409042010100301e000075a41503014118090b43d0804500121a0142a081d110105240703140c120040014030350340414014081d003000200c000c242c000a1004040004250169985e6074034902190340e40d4030362060640050512f0004001c011442c00903200c5d80c011f0f107483c41e640b20149401100e1003102a64061342003031124010409211003500001d41c064006828a0f0280001412000c115425980240c0050350f0200600c030300f0020302c944550040604680c0080402070100c0000d203180b5482c40001c091020707600c0c03031803400d880f580c06c03100404074168021500d40c0c1c20f60503d00c51000003203c50300e12a0040c2d01c00124120300404c3c14601139500800108140c8185a00541d10094041d0071603a0001c818882c90340043c01d29880d004e1040007a6440900750000c0c002403101e0b8151714500a07055401c203001c40414110000103607020302004035010350410103207102080 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 4194198 1250 4192948 4192963
    0x30c0f0904020304030c03030c022806020f03040309050a141f0201060f030515130f1e0209010909031806020d03090204020405030d0903030905030601050906090a0b0405090c0112050115050c 83
    0x241c11600201c01c002c285500b00002144260181d101171101013040d0804a03120364505800012103060030041e51440c4841f140303036a840707500ca01001441c0c074284d07000004103500210780850005801003414080d41c18000c110b40c00819150a669060021180c001601d68136240300d91034500d02c0d0202c119080034802d4000a00a1103685e00000c44580c40c0d082c22625022071703400d4a01054404000704941c409407101e00e8103602d81254000c240603200390740c2c490051146015004112003c1d90444c1c001d03a0761801c90a0080170b22030301c0000d0190044c41c02803c40c1c6c1000c5000300308500c1d450390070804179401083d9440081d0311442c000a1405052002400034025500080e4051042500c4030208a030003d015506480c0292592034074260f550081594414090040c9038010b14804085003a0303051000f881c035000b51007441c0c04a10203d995000c03e0481d0382c100c030036010a9002c0d5510692a50300001074081000e100d150078040d641c10700e49541e00c002207450300b240c10170030000b41003003d441d424088030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 4195448 1250 4194198 4194217
    0x6080f0403020a0b0a20040b090105030405010603020901090506030d0e01051b030c030301090608061501050a08040303020c0f0606040b0a031101080903120108010b1002060405150603070503030409090c05090705030c0f 95
    0x10019810815010310040c11800203c101c1c0102c800200c1c102941c6d5a01a5800c032405520f0984c64809600d00445030b580002e030046985640300c900100060b901c00808901078405100002028941902050302d00100a051101844040d171400c102990b441002c90302000181c14040301d0081100c081c0c64a144203513003420201303010100000c211082c1036001201150251000c58501c3d440d00307820264030450101c00280440c40410080c0c0c10b6a01034206160b01601904006080405070502541424664040360305541c0120042004501e041d10903040d03105026107200d40c0c0141995500642e001d46600003e0600503210b00140c0407540c20022a24600343d10a0510300701e594851b107880c06048a04c0d00c05114036071280d090700340c180c800511280702d2500b11001b0591003170710403400703640400d000d0720903034040c01440c0b07021400d600c0c02c0005000030441020002850300e254280140c180f983d039001188103142a50522444503072042c2501d81201718001c3e15a5507850b128480314644c800c46100 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 4196698 1250 4195448 4195463
    0x9010510050c0f0c0108061804031407020613150507020901030803040f02100905010219030509010e0a0504020a17060d02090106081302040501060c0b0c030606160c0b040e010f05030706080f0403020a 87
    0x300f110001040140c401802030b202e0301010b4031100704002c4950040900078140103001c200080109200780103130309840c80c200c580e041ca4800940c000c282d0750b5004084459907a43d085000b0005408004014400c220300c514020303040c24941d900103802620103200141c1205401720114090000b0091420690340e4000d01c80081c500c413242d406480108284180350160007a10540060980c070110340604d4142d050b503c0d5454140e07594010b50710041200c4000c5e80055605101003402d032586d1000380585420f60b1079102c4039002c14a081030340000c0c01010740303004601090304040107868918845054a06c9130034854210b5403000389154070148140800f0394080c1c1000c00000d00f041c0c22041c1000c04500030185a10642e8554500d45903e01c015180250842020880005e0a41c080c40d01c9a1540b440703080d00c1e22000b0355802c903004240c1c1250f000700346190100c0d0010403160510214080080c034040d00038003005032500178054040340c8020200302c2c820040030002820140309203c0c000c10380340d12a03a03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 4197948 1250 4196698 4196713
    0x702070f05010c051216050d02030307090302040c0e0303040621020a08010e07050c060403081501020a1101140c030c0106170106120311010902030d0203031e0606040303030e0708030703020c01090501080609010510050c 95
    0x43c03004207075100103587d18012520403102a52021046a201d001031303450744c890300c0385151b003400010803004100100b08041d000005040d5902440240002d226507640d595401c4040003540100010120b281c816043c4104280d96040760415509411564480584030a41e912150159624451401903246a0003288200402c151f0400c0c0c2c064002c00090990b401310250780c8006a07901c9207003000240c40d0002d044140b070900e45c440e0b000805a4102d010a06003080d030000c0506156801c41c01900010303075183c7d0020f0010406c441d083d00c58510b0010b00034081a46403d00720104074804840c040e042181c034948503c2e441d6401d4000c410181d030b0140494980440c4941c009469030002d80b036000802201003c2c1d03090341100304080174082c410041406140918566068008001c42c4a2244050003855000234984d0b5080c8003030300d81c0902a40207004200c40c8000010310f0351905402041c14854804284072042d1507140c3c4044c10340303c0035540344c0e03040081c0b44410b031a10300603610181c195100c4c010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 4199198 1250 4197948 4197967
    0x30806060d09060603030e04051b0315030106030f050d05030f010501140f07060902010e0a0311100318030507020307060314070c020a0f0b040302030105010501170712230f0702070f05010c0512 84
    0x20704c20400c4900954a030203c000d001c108200699000f1390b0080a809048400c078010015070200840d00007100c030710011030302c58000300401c0c01e55209910070f4500101d84628001400000d201c01c6100c0e40c1d4601d01540f03585000c840c1c0101212060240358104403405034060301050790801100d000f0703540454601c1e2926201d10345840a0700c0048022800070b031000b100f0200700d082c038192040950744e010781503591345220681403110b45250546040105621050a9030364281546441d584980c000c0e51203d60340c440b0360040c1491319205070322000030945010300000c04a0310790b240c0d807508007400d07141603000d440301800010007085807a048091911036480b00041d510000da4020012070f40309400a01440c0c3e038034001500d60700b11903400e005c9007401100024a1007480351010034180f842c0d8140000c0d0900c00850b1080548c1c2e4aa280d50549140460500840f004180c05c5154494040e100929610741400301040c81d0b14003500c1201e05008d0100c070501e040000c140704c00700b1036111501c00c0395100c41221 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 4200448 1250 4199198 4199201
    0x7021b010212030f0603070801021c0b0604120305040303020606060a090303050702030f0d020a02030c060304030e010c06020d050705070501050a0b01120213050303070c0302100203071a0405100f0c0212030f04030806060d0906 98
    0x103541c85c9100e88110040000d2400060003a5501c901d2240f1700c01c6c106111844241c0301501e9400096036001004010204020b503122032048542c41c001d0b9140b648860442ca0040c0c03802c040640454410001070290985840c0c0c440c2100003034a9141ca485034640c2c0452002c05d140034482028071a06000e00401e00f0403a41d030002d21044494000c03802c0b20f03100000719003440181d00c01603401800140090b1404072a65002d04075a9203031500c5040011b19104000c03040d0404c40d80c1c1984d8480000e10006840801d20409018042d0003501c2040200300b00071000b40003230001d1600004400690b500490580c1c10b24031900709020040a002d42640d58403440d0340303003069840115000480c4130780c0008546100c400d200005650716030764400195068051404141444940020000c85a0784030f411172542941c9140d01511200b44107161000c02c1c0d0f0040034201030b0800c5858600d20074a61014005c0001030b4010288858000b13402d81402c40903910303014045055440380c05c40c8000c00505142c807a0040100d20b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 4201698 1250 4200448 4200451
    0xb0d06060608061908061302011403010806041106090a090c05070b0108060105040c020d050409021b0a0c0302030613030206130201030914030712030603030e040b03010b04060905100603020307021b010212030f 91
    0x3c50b0764004444d0031002849900b0900d005a03400c5a2100300054081504260152041e0780141800c1e407e15281240300c50140d4003d810a11440d003100051204110fa505a180f5000c00c2c12038083d0704114100c80899102c03407042c400d04290741e40321040c2a02d1140540100c810141d0454100c0c089980c5a08699907610b5083c4103803030003207250540180f4064404076642d0442d501d55900d061500f85861507100180d004504402c202c101004141085040c0c100b20b544403c0b4410096101700d03e10f14010182002d400804001c00e0700f0249440c2070003e03030301140b080c2d03100d10188041c01c150300791800100d005100111000f4103002c60000042c0c62208000080e1003502d115000070b1178909113030041102602c5071448010701199403a03c401100e03103003035080140c00c0340d00a800000c0c20540600040d0580b001d541c0118401d179a150f05100c0c01c0f01c6605007100c040c21080c1410740c5542440c54001703590300e1440501a01000013480c0c44010781c0c2c424484610074825501e0383c15200e0a00684102c5003000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 4202948 1250 4201698 4201711
    0xb030a060603020f0306040201170c0f04080105101505070308041b06170a06030206030601110c0405010f06030509070302060f0c0a0602030403030c020f070303050a051803010c0215010e040203030a030b0d06060608 93
    0xf1348080720705145030000340d080c4a158180c3d603c4c040180b291024003440341014003c4881d0324410301203140030280c1038014000501006002080034140010060340800e065045001100d140000d81e0f0b15840d0064121850190b1510740b244555485080800722130054010b81081c404100c070b40011281da00c90843c1d5800d000c0d05100c02da0b1a190314181c041103e10511000350003001c1803002401c2507000b802001e408481820030f03124070450f201c00060403214260019030591440240038410030764540b0030300703911000880c0105411801c41c2c00207200c6001e0340b0303689204160006080140c1c03010901c040b0300250f50026066450342810710b0068060324050307825400520480c0f0481d0b447d500e00081c4070b0308880c0c00d07840d454903262000300102c3c0d19500151100c000303900e0031245100c0d640c809116841c10001240d0150030310003401e10500214280c10b81c001c1c1c01d0003540c58148400341c0d0b4040300f2207104c0540f030708001480c0d900040100d5140311501c03001915007841c01c1c100089003504a403e4034131444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 4204198 1250 4202948 4202959
    0xd0e010c021203071b06080103060c030b03010c050a030e03030f0105040902010c080315040c05190f0e030f010501030302011b020304090915050f09010b15160804050604080102090f06040302130902040b030a06060302 94
    0x5d00e031007100710900c00584225800a4000c600400c0420520351020780d034a1a070f40340100310f2290040c0800d0130b480c1c0099009002400008201e00000d5146c0b15288031203005001544c51030030201070907080c0c1030041c02190b1140f69143c01240c210ba020300d5179500059800072100303450b031a01012036102c101e05160624015410101903407800f40c03041e401c5a40000c0031060b445821110800c0c11660101a286d220050280da624000403580c1d080000031b0350301c41c3c820004030f442d60452500900392070315102c2d07032503100480d810101c0c50300790048141c1701601c00d28100000d40801a003403548504550b41c00074000586484244144400104034851044502c04001e10a03e07034000103100200d10341000740b8040d08420b0000c501030b5290010786824680c060007099003001e0b29800012000e500560103101c550f98002400542d90404548440c0310540482c1e20030304143c0780d90045034006282000300b40c50140d5a240341011581c6552190303034598005000c580c0350400700d15001008050b1800240d1256 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 4205448 1250 4204198 4204223
    0xd11070b1606050405030c0102070b0612070e0103030c03020712060207020306010605030105010c060914161401050418050907030804080309030c040b0d08070609020402030f01051906020d0e010c02120307 89
    0xc812404440c2000151112510640607a4441e040102809442268135010030000043d00013003d0010f000218003c20850341c03142092820002c400e00071910060168020420030045130f85030340001d0741101d4040c2040c4004110341c2c40c00301c0c1004010340026940c44117400082041c401140d001e0300713900f4803e908665041c0d03290142a60f00380005d00c20240041e0401e4107500004001d81c10401042d032088040c1c208884000961a041c0810361202040109100b40200441c4100083c1240ac40c1e0742801c0145c9018105488401100c0380401506005521280840c011810802401c3d000f16001005a5200c6844480d210740720b5001440b032038424400c50f0001034040c40c19104541450301e0040615a4a0b65181c0d100f00c1c00e80c100040039200c03580c4d20500c07100541c039a1300003184500120000c0401c158142420000c50094000c070342462200b25000074491140c0024890101d0700040c180084840c030300b500100ca000d48004d80c02904280066200040840000301412150384140900d0404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 4206698 1250 4205448 4205459
    0x10303050405010809060907170109050304090902090c0304020d02040207020d020312030106090801180303090c0e0c04050103050f040c03020f060d020c030301090605060a0207030206090111030307020705010806040e06060603060a080d1107 104
    0x22841b05840c0000035410444041180081404040364507002e03000000c01c0440c1c080c2c0324941543c000e54003204816845002c1d10046241c100b60203580158101c000d54114140768020030180301c403400c4000c1c000c540c0046c03544255070742d0b4010988425402400c640518810f12806801b035002841000c002c103030920400305210f00f040c011582da614860001c02c1031046240c80840240a100000b40c0700040a000b0105105000c9082184104e13648009a80d41d03515220006044540041c20f0314140019142480300080c00204003808403601201c90b5524508070760b00280c3c0510030190349001480c8001007521880c1c1010010310304032100303440100309107a5140300380100f40c4505111000141c1101c04184014a468005080064810316005440500d20640e05295910a88400016030700c80241041590391211006038012400da07003d2080ca1170041d035150b5a000c018284c0b520806001c0b00180d0144c485900b41d070005d042c1c0030200e0384c00c416800800b800c2c80c00c6810101d401401480c01c04181c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 4207948 1250 4206698 4206703
    0x209031f05060409050a060903050c030f040e1302060d0e030c0102070b04062d0203090a120c11010306050d0305030405030903061e011509090902040e10020a08010e0103021011030d05010303050405010809 89
    0x740c0c2c00801602d041ba00782d60320000105182d0350102e0500805200b01340404c00200003802c2049140c00d407090f030b118105008401d15810017040b8010031005509102c0050f120031040c2e40d001c0864400c04184031040d40713905402c0d4051900102c1d140d61012641400340600c00150781e004038002d41040009a451103481000d00100300802c01c0d041107108101952030103c1d90007076601c05603900542e020200103641e40386040d0b0094980d000050488001d01050147e00220704841210901b02007040c0d0b49060003060f28110804400303000e1000100020b010b0140c18170840c0e806080c0101036820078a410581c0f041d8505150304500c0b03041c0350000c004292887c0c14000c080d055421510350804845c500440c60016056021003281c1003a00c8004692074107408020121003211500d40c00368036086030840040c01032505920091441c400d05004001507103aa50000c00141218981401c42d03501060040e03295102d000e6070889002d1500d0000414540e11801500a0f12070903070312540070b80c80b44a45283e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 4209198 1250 4207948 4207961
    0x50f0301060b030601080a09020303280306080c0607050a06020408070e0a0b0901030b070e1008060102010e070f150903050d0302040510080708010e070c0602040b03060a050307080604080d0209031f050604 89
    0x402c0804100040768040d801220070503030240b500743d404116406542e003c40d08541241e0540401c90b051416100e524442040c07040c265031020b0320781048003e181c0304d1110b503075030161111203006100000e40007040c07000c24001e0401c0b95421141c15076549a0f40c42010f503072440b641c41486c0d640c0b0200c0c1d0100d8080a040d005401420200408034184c0381d085072517500721503101902120510004e19070040d203039203070410990000501600c404480b803501d4400682511070000291305590030018041c81900000c0ca0000e0960701500549000c0f103040300000d50300b0044542014246201f0903560017100c1c5e5240d001001907900c2611325840100050000b03580003541501d00b00c1c041001800140458400d2106096010a19141c07612540c41c0980b114012030784140c000301c0c2c010000008201d0141000c1a07500c00401041d4010900d403403901c0c98440e107411018200030b08000000580030b1085c41540c0585114940050a45548800c026410f0340000503c55800380894105400200c0c80c0c0740038458078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 4210448 1250 4209198 4209209
    0x20a06090b0702090601030f0c0806030606010c0312020a18090603050c0406030b040b060114040801060503060105030a080406050a020c0a1202120706020d0c020a030f0302060906160903060b130f06050f030106 91
    0x905082c41c07a801c02103d03a000804030b43c101580c94000170080d603502d00901c568051292241002d82c01c0c503074103040c142100108641e040c400c4448000002907400030a8003a41c0f07140c00741c01a200d0516110440b00504030500401581a07091070100c0c4002140c2c0c045001c03a03100710201c54403111004d062205403251480042e01c07074480100010f000c542c1c80400d49070b1100c0c1c145080c4036541d4522031035804a8026400170007540c0e5440b4002d1106050400956015081c100e004202800f429a583c019038070590154208002011a8041d140c1b0f000b088034859107140117140c4411240c581c1420405070424900c20f0f4400c040e554100e20014801140107001d031149035014140d00010780a0941e07600b4030070001260406070083c00080828101c504a14900b4420780c042d2010f42440a0044c0c07905a002d03102c00d25004920908000d1123800020001c21a9030040e00494403407800b4001443c51143c001e4504200c5041c0f078410007060a155014500f139680840d40c03071120a04520907d822034003180541c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 4211698 1250 4210448 4210469
    0x30807060506010207030c0801060e090a0803220b010608190b09010618080f03030105010206070201020301080a1103011407021006140d060506030307050a1506080d09030204020a030b0307030f020a0609 88
    0x9020119000341c2280340c0c001c80600442e01c03216a80d0747c80601100c40d43d4045d07041650355803024071401c1c50040240e504902c80d0720041010400c1b54940b03590600c4007500c5490151000301001d400b09041c0c4006040458110000b01c2d265a510000500f02c00000c680e0501c00702e0150b00b21a0740200244254000c5100203000030340c603607081030003d55680d840202e00f020a9281076100003081001045407980030001d40303025540329407510002918000d0054902c40070b5900501c018886000b0004004841d9900088039024080218000c03a0040207902a0783d482203038030004200c849600040d95000c086416103041250603925544600307001d0804040f29800f030103031503070310340070031000c5d080725030007950081c00d0b80e01c0e140d099a516440c0030b04038101110903210000003400c01c3c03e45449400018186d10b806842030740c50b843c80040c049081800700910a0ba40840c4d4094541e02c283d11411840038058216034a00741c503401e059140f4090564101e101d1880d031500812464800d1b5000c0c01140c605005 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 4212948 1250 4211698 4211707
    0x120302100b060c0109080a0e010c050c04020703030b0d0303060e0601050a0e04150b04030303050a0f0203040506070f021006060804020901090b010503010306020d15030f05011a01050904020d150b120108070308 91
    0x303090015001d810501e940c0894240040c10f01c48800384a0003801a1140e07081c40d603030780c00000c2c0142c0315030484c059a40c18807a107103c00a0200e50041241e0070030003012180180d46132618581034005098002d00d01c2d0b004024032101004040d09a803280c002d0350302042d8510071301da4503840119110704c00c0795031542c006541220300380d605007403a402000602a114110160343c0341c031070074003000e030b50003981c4250700081c2c480c030500044002900c600c00195031000d0096155103025114695600d901a107040f0400211502d8000f000d482400b101c5810b21008405128040e590040244800f40c151400d901c5050603100008211401e48610340c401003041e143d0605503031840c1c468200035000040d034060101c0d00c0344403224543c0440600507014612600c0c20f500118000c0c104242120f00c89002c902060085034503400a81c2c2e04042601c100d108200e90150707172a00360b0036192002d450001411001202007050200d20501020080d01c0007804001c131036034003a03a84080c000e40e5025144400381c640d030000c00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 4214198 1250 4212948 4212973
    0x201030504051504030f090602011503020f0a1503020417030a020a0b0702030f120103110f09010b0c0c120604031106070905060a020c101e09050f040203040f0b04050a0606120302 78
    0x3001254400d0248003a500740b507107110500c0c0f0012004842c100d000443da420501945904019240042c0c21584001c00c54a802c040d5508070141e45400043d107d080e01c03900d00d201ca680c41d641541d016042403581e800801016500c00f5020790454041c0e0041c03104244183c0c81c0f580000000e903103c10a042d030040107181d03803548400040c0e001c0503103e0030440c0010000c000030114004003c001604d00d020103100558510300300024a24408031300c0c14492101e800c55006a9a02c14000e1419a00007441d800c0e9501030815089249c180c000900d03d82241c411280c2103282200421440c0c8558020384650b544c8696000100e42c5411003141c1035004a1003114050000703040c214080d188000c07448c011590340001d0440001ca070800d18042c044001340010304800d54100030354080f07252840e15410074032007060030031300000c1c070840b0440c00c4180500d034088000b905004403040e548040030b070481d1011080b810141080e40c1c032014440d030140d5003207060403030000d01100051780e00c0340b6032a0568043d086901480 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 4215448 1250 4214198 4214201
    0x7051203040807050106150e01081509060103020c01111b0601030507060309060f050907030c0801060608160e0904060f050106080105030303070804060b0a0f080c150f070501021b0f01050105100507020103 89
    0x2401c141c509103028000200091000d204000c06041702c640c5c91f040c111185c1e60b00030a50b190b042c440720b0400c1802c83c14000502c049544c5913004100448040c1e0083e0b40b1034004070002e01800380540d4441d0300302150250084038460003068880294100d41c00741c20102941580d64541c280f00c024500e50200c038040000700c0c800c0e8412012a445214085896002070404405030b80007540d04124640004030108100442d00300c111000700103130b0000b030020720b00d40750000c2c0200400500b038000100f0302c00d2005000f60b120b80c2d07060080c4003000300b07405a2070602e414004001c0088002001d41540307010000700b8414000c0700b489040b554010025803650342c44500440744c503000a4001c80b440358030341d010b0000507921100054040d01b102c0070207510175881d14540c603241c05000207035207004039498441500403c050070300300c401151800c2c0c80b45035a1155460000e009100d000c0c1c40c10074042800c070a1084c548404141c0104420510000740500e0340c0382c0c403c110420380d903070749107c021070400c00c5480c0041d4017a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 4216698 1250 4215448 4215451
    0x50711060a0f0b04020c0d0206060319030503100e010e090d020604080f071502030a0b0913020105160302030f0a030b040f0b0a050d020a03020405040803040b010f0b0403150b03070b0c01060b07051203 87
    0xa82c00c080b9242c1800d0b0045030a03600590728150041c0c01c2001c2142c0c52642c10010749a002074100c005100f481280401d18900620007180501084400000207200b178500d22034103070091000c910903006943c0c0d0b0706092082c55509440c00b0105008000042007458800a51035005a400034039444c540102150381c0c082c958001d8400301c442506402c0444200d440c1840914810305035040c002c940d1840c0b41d8200105240001d0468590a207602d1411002d0303644001500d0707050307500015072110300100d1300b026407560041c95941920003400040f82c50f20b8940c181c10104240c041600d05200440c058400c0000b0340d200896442d0700810000c10030841d5190455442d90094006081d806d4810740769000325084e0741040b034064030740c1c1c0781c0003042c04100f000d624801c81c010b028001d40d8031139090420250039460b104030311000e13000a002108644200c0256884603c04c15402000c03200b5540d603503e0412807a40080710000c11a51804c031000411070183d004441c002540b1101030702c0d064010404e282c040d40c10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 4217948 1250 4216698 4216721
    0x708060f030601030506060a0504090f020405060604080601030c17030307120b040e01060e01030b07020604030c02090a11031602010e12040905070311070b0105090612030304020103110d0c0e0301050711060a 90
    0x94648038059a10240005030107180500b019250510b0315a06021100009900c0580203a1410380d214021504a210400c1c04a90445003c01e0315180d450005a4034011500704070001d00656000004001801036600100ea02c5106015894420103107015100d0100b110341101040081602c4401001254000e04c8a90802000000c14000c039000045c01c42d07400e604808a090844c50040c414010341c030503203076070040e401e200600243c5000d50b402401803001c054028056502031001ca0500401b5030090703450b40312891400c90b22840c1030192100569030700d0100f20007551030040400001d001c08240d08107100440c1000501d0325207000250002401c000700030804055694a01e008201c03822801400080e0188005440c10b50419003000000500541514400c003645c268402d106500442541d50154090130006001009030622103490700c11101c2244005242c44110f81c6000e800c600e400001e0f52060b4020440c1d9a65010162850740035001c1c03208840d8407100000d0715142c05900680d40010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 4219198 1250 4217948 4217959
    0x90b0f0601030e10091103071a0706020405040203070f08010f0605090d05010e06090a03030f0212041401060308030c04060e030c0d120306030210090302010201050a05150d02010203160302150f0c03070806 89
    0x543e8500d0711414105620103d88030315407140d210100b4890045000782c00400120041c00c001842e00b0350002622421450700d0560740000f090902c1401100c1d81501c00420019200307643d03c2c0b910810003004940341c00c46500118480600104024010099031026901c1588032035140020070410040c2c0301d0f03843c0c03e04450750340d00c03640031741d00c440c1080c41000c1c02010a8401003003014460310f805070903101858030550384035105104014a04c84030350141600305405c4018005003240a1520030b02601c159040504880c01c0041440100b4203120300170411280b040e40c444900403080d80402d510780902c02c0d409544002944070307080200301c030f10014062920b40c03410005141650390740400d1a00d11054442004600c0704a01081503580a003e41035029051142c00c1000d490325075040c2c4246d0004200181c09841c11076588030469008008641181c504c1011103030310f40700c01e4a0300a540b2940213000c00d05801c04180804c1840c40000b010030700800d80101c64030308580d101001180c0c141c000800d40e0f039001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 4220448 1250 4219198 4219211
    0x607050c04090f030f0201020a020d05090d021009080f01021c020903071802030106080105030c130b010c0c090501081507020303040b150d05010b12030a1409012001020c10090b0f060103 81
    0x1640c03207110b018446441002d0461554080e0700b405443e0b0134440c12008196401000003808295011448065000203400c0181d114944840810100740745c80100039000000c0281d05019950000140d4003107501e40360480b50b1816458600350700703074001c4c298045e83d1040981200d2050062507000f82c00d4040014080310b101d956a0b20301c0f04d810314007117001090350950000050255662100c200f40c05040150002c041c0c245144000c41da101c54840320b24640d036a034500c0d002c0000e038441d081103c841c270f07081b8200ca02080c0c0c03500c01c4003000b01800c0c03048400c540301e485500c1d50520240304036280b1500541d00590708540e25070300c5140442c0f00c01440c0c18802440d003049140b0a07075842700040f440a0242c4000a003100b03040c0140320307421046e1884054941d20a100c840421340e80211004031121034030300c0e1780d5100d40c0c11a0058a80d0240c601710700c50155086203030a81020b02c15405400a40d24010480307000070f40201045089495a100142c1810000303c000342001e01054110380d0484410302d000500e8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 4221698 1250 4220448 4220473
    0x513050604030309020301050612030304060504060b0a03030908060105010e090c07050102040905040809010207060207051e1f080a0c050301030b01060503090a06020310030203060109021201050d030e03070b0405011106040302060105060705 104
    0x1031440495049020a5840d0140400e43c18244076455000005482103082c00c6c08501d00259030340030083c80102540c0c1c44400040030410300360001e0511020141180c941d83e074980c60090088101c0c0d010f80c038414861721700009019882034001e4001c101c4060989006500d4003401603069074880e110540d5150340800c00020030901702c1c440c891140340549041c4c0e03100c03e1940002800c002c1e041d030007242113511280041c0b1207a03403000d100024a10040b4080840404410042501c016800b803640340807d244c10f007098640d41d080410b039031013040020b804024103020100709940381e00007800007606140c403c10042c0702e81303409000155080b8410a040b10351240560703407440103070791007100d0310005031a1b001e03020003c50a0400c030181c05800a18025420000c410a8085c0640014820795200303210380c10305a03040c1401080064142000581943c070306580761484401a03038020300c2440c1c000342d039400800c0c2c3d0b0b080c2c0100320b0500441d859400381110740d10704010040c003600036074415501c0d40140c1130103204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 4222948 1250 4221698 4221703
    0x10c0f050706050913060503030d09060902060408010203040c060504060504090203070c0c080c032a01030504030c0c0b0406110c151e0c010c020105070c030207060c060905010e100b010e06040504051305 88
    0xc02d4142d4540e82da0b00b520b40300b84111059281d0006100d1424907070207110b10355000c4280c526000d41031100041801c5c4034240b01003e0410610040d4000a001501013040c40041d0021032080d8003851005002c1643d40c0011121440303144034100000d0000c1c00180002c1c41103400554101203036142030017142003144c8601c003044003d584250219481142850310505051000030003404110300056a030444655011401031485201e4070704140d5500005000c040c020301184038280e42160030031020544034000b1084030b42c454042c03040800c2d64010803c0045000003101c2003031000140c00403030032500311b041c80d000302c0e00428240902000368844401410769000081c000900d008000441d01480c286806400c5880141400e0104513220751081d000c281c00147d0036086407060314004100c407089060500080441d40d0740100154200120241104030000e10b5001c4119884404c11841c11090019500340440d00142500300d40140410403a07450700c0d511003648240e1013106644901c032130707030380340b60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 4224198 1250 4222948 4222963
    0x50f07121109100f030b04020f18061605010207021804030c11040f090302030403060c09050604031101051b06040201080105010315090509030705010504050a0b1605030402040c0905041b1106070e010c0f05 89
    0x13207414212014042e8075028954200c00c0a45085250810b049014041c5116906546607500900a4400080d46901d000c4900003404e40c40401d08103031032407030243d020754032540080c1d00c500908411000b03120300d082c43c1d650140d54152246181082c86645c0c0c3e201070340724035140542c09696108000300f034409900628503a41d00c42e9010316540c9055160640c00c1700e11214900040000e09074050000d0703280e4004a41c240d9030400c00c420080b455190048645204805084501f100d990007200a19100011003e008074403d0300d41c90071036a00c580c0110100c44040d0040c01ea0140f036501d04202a03034140e80f140350051031b110b05480c649851a1030715800e484081d0b50481e0654021261b00c014000d00745010350300600a00101990030000d09002805804058070192280c2d0b65009594070450140100c880201805441400b0f998100004030380d540007840b000002113100c0d40e14091f2f09200100301c451084030b05844444090410300c00440300080740f1101114070120066001d004900200031a5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 4225448 1250 4224198 4224229
    0x8030a030606080f04080912010207170405040b090c0d09020a0302100906020607050a0f0305061306060801090b04090203071403030f0408010203060f0108060904060b04020702060f030402010201050f07121109 91
    0x1103011442e00304001d1580703500401c803040e60340f005020b0000040e00e0782d0481d01c4070070301140c4808078130049860301c900a200b04080109080d04054100410030601005030044550884003009000500070600903407420869100182280401185580452031703440490464005441d00d600307962a80e000c0346810030712682d801301160384944200a001d6040007803a0b405002454000d01704003c0810242c09103e8000c1240d083c50303203a00004805480e0150b90702e0a90b98035100500800742d5070b1002a10700e6030280103d094440c1082c0f8602024101402047d00c0e640d070280c028450b151074000c4013544c2c40c03c480c00b1503034180000c000c102841041c060141015160f84000141c0c2e0741009c0d001c1210121240010f5414081d001c010400e4668885640e00e0b88a600301034041421400c86000800a00c02e007076009510403004500d001e8481d00c3e4501a601c964400e030020072060702d0301c000100c2d0014048441c0c8000603444241140702c00c076940c2100741d070700300344611441c1410310f40b00000d0f150003000301d643c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 4226698 1250 4225448 4225451
    0x90c1b010209040507050c03032205030d0b0103060f0305060606030604090c060305010f090501030302100504170708071b0e0408070302010f0e0a060f06060207140a09060e01080c0105041401030902030708030a03 92
    0xc02c002c600e0140708864000707080b810001c1c44c1105c0c0c1249591203000c0281902001511403100040840e6422040499154480c040d07a030758620b4403040c0c0c0010007031800464002841c000010510b000e162000c031040d079030000000c0c601ca503252000c21805510040c030641e085a26000300500203a9202c210784080d2440741c801080d00d40c14a0074100035080c159101259090804004201007070300440c14001c02070403d48003107250350f2542007203146200c0d41800e1040311500001d40741c00788075a0601420002d4071a0354501c1d0180310203185205809441c3c0110200c500950005c9000520200010300f6081d20034000491a000180c504070210341729101040002e40000d189502000030520841c0100c00f80039004000050815500039a181010f001d2103c5500591071441a20b59816016a00400c1c4404043c0120741d200c3d50b460400078001c1c800d5644520500010303048541c011815981a50210b580c00314103040c042004402a010003402030348c0601400c0b2003c0f44c0d600f028002040300c100c541c4c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 4227948 1250 4226698 4226707
    0x1401030503040e1303050405100908030d0b0a09060b03010b130e150301050a140c0706020403060f02070302070801020a0509150d06060e0307060806030303040f1b030f060c0e0f090c1b0102 82
    0x107041040326002080c1c00304d8104403145040020350404103681c140d40e000e5a40b442c2a0300d00720400c0d40c1044440e00800381c00d1201080c0c3c3d12a1410070307001416801c000345d0307005c2d40f2566544181d0b41035a040340108204d041d402d01c014030080b15260702a04203410220880c04003a80d076011165641030301039400c80a69800240e40b040e0a003000d0142c0741d040024410100281c0c22466141054808003400d2040c60880008550050200f80d4056501031500324204000a240c80c1e0b200c04000d601404044002d130003880000100c100d03042c400c0e83c00d1016203480f081d1811a00c602008210460b40c90351001c00403007844540c01c0301803070f445131001a000d1510b0740100905108200351030407502d41d014400b00b0a805041103130545002c0f007500c0e00107030301080c805104885071900040a00c01c0700711014442d402e440b000070502100c10003000e82c590041008014010f41008201e0f00c1c8a8411070b0340c1d8111000f4030340c00c60030b4100869031070380c400c06a08034103040000d00b2905482c42440481140d009a40106 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 4229198 1250 4227948 4227959
    0xf040f090903140c0705010806040b060c010905070e1603020304020a0305030c0a020108060a060219020a1205060f010b03090606010f0e031002030405010501120213020a02160b0a080f010501091404140103050304 92
    0x1610f61000d000e010014509012044e00e0300c9903220800c0c01130b035040082c42000328010ba00d4942281555030700c000c0050781c0701c61500d50b02d903008021400e800d407558401e5850000b8850414001c07240140180c2031a08124003030004264041d42c4082c2041703820002c40300d40000462810700290146400308409002c0310a4203000041c174402000d01850310030326108008002c1242c000607440348613a0401d502121000c071500000740455a182d1100c084692440750820070080041072182c0310703450f88404084980d03210118541c060004607500d500c258028008a0003d602918040201d41c1151400203400980d0b203004c2802c0034050440412015004014042001002e000b040e01402259250558040351900003c002a140390380d0035110b264006015003070184280081740c2c11251104000c01d401d42e603180c1d0344a0603030241c0003000c00104c3d440d01003168100700c21760950403508144d454105a03414220840e075000140d1071038581c4190b4804158040c5040c050300d1500842c0541c014640722803904 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 4230448 1250 4229198 4229207
    0x509041a2703030906100803040501140d0e1c0201060302010e0f030703060f20070b0c0304060f05040b04050c0d08040501030c0201020405100903051204030f0b090c030609010606030c02160b0f040f090903 89
    0x11b80416000c032114102031084180010503181142d00c2482c05510302010103540301d81900c95044802490ba00304180200d003010005405076081c4d039507091660700a400000100e080f10360502000303000030820341c100d0215142103010407280120040c15154103035030703c1d42c951089422503400210303a585c503108880760082e03c1222902081106660a501d0301c02c690391104d108120090401c000e10001101250600a20350b001c0074030052400c1c2c3c2005281440c0c20300a1090004a4086401c0d01c01c420310400c9030f0500410102029620040e2282464103140054015040144040742199400d1100041d25565041c1034060a0b56644a2982da85e00714144075090103003075540d00e1100c000401042000800d107404409140741c00448141d2191039120f080c50802860481e0300b0b40c14401c94050044007841075111701c0c202c03900c984007004400c100340b400340d80380d00c41c840503107181c007e50354820010450020000c0c007401c2c002070120361400340c465146080c010303826040403c03001ea64114140416410 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 4231698 1250 4230448 4230451
    0x501030605090d050c0d050a021203010306021b0a020f0105090301090218040209070503070905040209061c0501050f03070503030f13030c03031106060103020f0703030e030d06120b010509041a2703030906 89
    0x7145000c03841e05030769941050365510b2607500c06081040c0023540e03103542c62092002d054050030103681e00303690396500c1c00e03e00003a400a511600301c2003241044104c0034500041e100405a5000d0142d001d4001c2000055581760422803d03d50195203a040c0030005a995064061a020762080780d400c030b41c00c0c240103015a01c40c00a050f20305007c0100180294079410446c40c0c021507000700c0d005a40c074246c05000c141103008881c511804055000402030302c00b0b0a50304418140c4009648040c805075080c0d0415684425600c030369901030f0010000345220b010204000c000d0391017104103a601c1e9603601e5540d40d0781c2101a520940000307a0384040028010024050710380c104009180a60420342a0031010700315200d00c075402001e160391601c440b0780710001807090368215844800308000995941980800352104102c08540e088100303400030682d480c22114450041c1d0304403408424411a0302622015007070080d0560100382d29185181020300840200c088043c0711241c00766440e81440703200745141c08070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 4232948 1250 4231698 4231723
    0x5030301210c03080705070b0301150f0203030c071103010b030a0302061005010905100c050f03190201150b040b0a021203040c06080906191508010c0c0c090e07030206030403030b0301050103060509 86
    0x34940c1c0d5a07008103166032402001e070f07a00700148540d2041c00b0701d020792405406511a0704548008400042c00c400c2420000301c5524650301c5841d0a4031580c04101d80700c0c40b0880340c05038241814401d1402103003c425615460310310107000000c6188100c00000e20305083d051003200182d20100402c0307200c18040f240b403802440c080c24968406420320000801c04400d42e002d00c4200075030000c0344010320901300401d40d62060380009881c0d60724080f15224170104907a0400602542c20004045230550640d8004421105d412281d03605250810a4003100740e0b21201c0d034401148540c4211001c8006c1030380007140a1171203a80442d0713403170f0b103040805440c410000384448082e820030b1040240750154012503c100303040d8128006140200a1039001440d51075401030900e030b40c601801155007035088a8a000c04600035040390743c044c4d50304c1045a05603101000c0d40811500003e00070070042c02c2030009103401c5403083c00d0108603481c0d09000f003821114241e00c1541c00ea51074030140200c030704060124011260 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 4234198 1250 4232948 4232999
    0x1090801050601050a081302040c0203040503070609080303010b09060f03010603060e09030702010c1101110303040b0901050609010305030403060b0d080c060109060b0901080f070c0206180a0501030b0904020f01030f0905030301 99
    0x1a1200c0040c049000d920442d00c00d0042c0a4001001f8a401164078855194020401c110007060003800035526001800b5550083c0b04205001c2110790286008004603141100111b185a0902c1308900f8aa002103140a40020b4148902c031007110340a40030714080d2000741c0c0c0c00151039107088822162801c0103005140d0a4004100341c1c00980d910000c0404d0190700001001d280507405801211170b1070f011101c07011107001c04824802004104801c070343c00fa03a0f8290007881103888810070460126020b200080c640c1d0300801c4104001502ca802c0f08200600c000c094184000040e2250481c507407014601c0511504024018018401c0344c1c45040042c00e184200142000d81e50340020b0640d000107051316004541c101d001611040c4210f00e0342124a901804442e1101420041c0c0d09103045d41c0d50a40f889400a5440403425520070720035000f0301040140703680c40d29201c45d004e0090519118149030704054a0305000e91328842a400f0b21400503200e1002160740350303d8410360750a0444d84901d44000c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 4235448 1250 4234198 4234201
    0x509100207050c040509030d0c030b0306090d121a040617150c0d0207050a0203030a0f0206130b040303051305010c09030b39120703060302030c010201060803030106030c120509010b0109080105 84
    0x340c00083c9608480b03000c0c1d8000502c0d8a44400c03162035400781d200c8000c040d50410b03401c00305595040d081001c14400c2501164943d44451444a8807041480040e00000d0341100185190100c150001c00d4994811242a500c0b40c40c900701081c251000c5402000c420044032a403076960003800c000c2580500110713030004c107103810010b2000b01070340304000e00c04900c41c0e0041007020a001c018010311206035401000c0b6640c4650414000d0036240032960910094042c0c200000d1a0303040e605005a601c40e40046200d00f1039070360b070b682a07009020142402c00ca81c2005841580050800d100b03880d40e00c2d24644035040c907a4a1840c000d440c0440c010301034841d84900c2c00c0380010800c03124100c0c40428540d02d8846001014049450900e40513040341a840b4054a00c09d00c0a0b2941591100d81602d00913401c0e81c039061040d5005a003a12194400c0000c83c4d4030030801040071900c01ea004030016a4240390104101d0902072400d0b054400541311000585d6482035007802c90f41e08441c6003401042003500a0005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 4236698 1250 4235448 4235453
    0x3120906020c120c2707210c02011e050109060503030c0721060213050108060301021206190b0705010204080c010f0206071b0503030a050601020f0a020a030f060e0304090509100207 79
    0x440c81440072140c0103860aa50801c4807903024445070b145090003a03c48221080c070050307544411176074910008a01810400428001841007492a500500804081e092418030190400083c5804d40c4008119583c800301030504411401441c500003a44000215042d4149041a411100309600c2584a1352081111f05442c140200f080f500b19a5600d503015048541d004c2071020300144128000c008a01c0041c04140d904440c040d58816a1002ea94112071640c803401890b00f00c1c0f00310a00081440380c00000644e4506c0e14901e504d60541e02c040c44190601c2c1d441000c1c88079a0080b038000c0f03485035000305080c04298403c1000703119110302440c0c011808155031401949810001c2c09680c1000307105c0c0e1a84000483e0940310328822980982220b58910301026488020b08050f51024010300072800007403036800001456240081c0c00806503401c240c51980c407020112105401102d525031240040c4443c694240b020340003c00f48002c0c04a001e18004549900b00308000c103000e421a8810301200d4003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 4237948 1250 4236698 4236703
    0x6030d020c060310080303090106080d0306030201050711010504080a0605010801150b03010b030c0403020d0302030a20071202040f0204170f010c050f090d0501110403060f020a0e0121050403090312090602 89
    0x1440e0042c0d4181d41d8136240c100043c00305201c40d8102c1c64442c4000404d10814960550295044890300010740b2114114210214141c40f01071101a001400501001000c2003050103510305090050400300c0c5404c0d0b607050003d0078410018400d5944a82d036600401c484c4c6001c3c01401c03001600c061405075600c0c107092913200c4502060092000e1050003000181c191141c2008a6028540041400035204014a0020f42d254003945030742c800039004c1c400c02e886002065141203140d00c0414054103c0c2030414581c0800060f4540702030f80c2c030586550f5140301c203070200e100500140c03096598145000c0da003001c1261510745d100049001c0c40e89010004428198481300340c919040401c1e018a42c0c0e4801c0200140540d43d807850041c206510340341101c2d1212602d00c009204881c0300748018460411002006805c9000e01c006103004540d5038030f4418035943c800e500c1c9048652502d903014400300c202003200b401300c3d103040341c04501240700c0140a10a00c40036080340d035120316070383c43c01e213101906200c0004d4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 4239198 1250 4237948 4237963
    0x1090209090c07030201060e0a0c0f02010e07050d050c09130b07020a0308040b04030e0a060f031113030308040c031b0e0c072a030b0a020a0315060507020f0607080307020a0b06030d02 80
    0x2804002c010a00a08041c400c2d00034000400a03ea01500b030b0b400c05007800d50080c40b5041c3c0b110046041c400b07604030214010b00848000503014405400c04038070348401d1200842c0480c804403000e004240c044401d0743c0d100d120035401042c1d60101003405102620740412098000350000d000d5612202194001075480014280e2003a40000600c0300c45e00d035450280d8403121304d411142c1e40607501e0070000c904103a01c60070003c60000790323540c14400d20302d0060180d1118415070350402d0480705602800d00100e03010320390068200d0b20980203c20b4041d81c0b6211004801042c140d01240d00c01000420042c030350760503248070f0304048060140c0780380a0690340d070142c20060074041640c4281c604901e07a85181204010b02000b150403101042c540d01d01360140100951102030000d001c2494440002024950540c0450076624640c0720340d460a5880c0e02040440d40661207803980c04502003082c040091700c51030196002c1c9025400a00001d0140d1600004203a0020421406a849488186540ca90004d60711 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 4240448 1250 4239198 4239211
    0x30601030c090207060209091f0f0501051801050c07090204060801090605030a030f050904140415020a02030d0504150903020102030a0e030913020304081608040801060803040f0902090301141302090109020909 91
    0x1a0350780d004d860088007074040d0030303e81c0b6807244c060010020124040c05501050841261100030542e40342c81d800700e02c483c0c080c0251400103200b032015071035001d11002408000303917050415074100030b680d5900510f403103404e820036000b50741c02041c100000e030f4000300000c0c054400340c90700b4007056040c5804a0750341e50f185000030f0f0800c41c8014000f15002e000e40100c40c20490043c2090205490f00040d050400d80e0554080b10280519403101007550407601c2920303881140d56001d9441c00720070800b548083c09002c0c10a45040c00c4000c08415900c40074810083e1441c030a070000358480c5040d8010740111074507600b50000641081043c14800da48112510121204081c001a200e80365402e00000c1406145600e0030310b802e800e4010000e0100c2c440c060800c40b80008000e122290310380301980d4480c0a41e21800081c1c000404090085240d0b42d0054000480080c000080841807054050311070542501c4050b200014140380f0f0040d8203007056100c0c00f600f01c6680a52070a481b17440890300e002c1005050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 4241698 1250 4240448 4240451
    0x3010612060b0d02060301080109020102061509060118080709060e07020705060a030f0b100305010305160509010302060304020111010f050601021207021c02030a050102030702150604050702070306110408030f0406030b030601030c09 101
    0x2481030680d21401d0f4107410a80203444c00343c8960319030f03030018028000100b050f03001d480b803500040c118000303a240301c1120160150000c0d0345929080b0040d91803499804110310344010982d0041000c4504110712001400040302c04101c191811140425043c00a0300e000e0864100c54800d124030f031100c408690398281d4503d400909083e007035250710000c2626042d06035001c0c1c2c81e0a981c03100d041d0b0680200e4140ca01410a5401c00385480c10703100340c500e10620a16030000d010400400162510102865201d801070506054095400004a084901c0c404010424035070740e0050200d0355074100110070b1645003440030540341001d070382c000600c045003105850b551107011002e5182151400c0c130007c01c0e61503020009540307170700b0500c10180d2924900038440c1016401540010380f0362810303026080c01503002e1f40142550600b542ca40c0e2000c1c0051040a0300000d00402000a10400c1000280040c00c600c142443c0c5072824101e009090311010dc0c440c600c00d900c20801840071501c0e100d9080220b0750030420 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 4242948 1250 4241698 4241711
    0x30601031506030203030705070504050105180a05130210080114010c0c09020c03160605010608060603130210050903070803030405060108010b010f030209190e04020f0105180d050a0b04050307110301061206 90
    0x241e4002605142e0002034040c013004c20413030100000081d000b011b40d80111811302060f80c0300c40611011548c141083c0c418240500045055024540e00440d0000203181e1081c03d0110942c011481b0501c0b00c0b0201000210403100400c140e103040030040500401c2407800f003021310f240752500c4d0118142402600e000303940c0042c026402402c1002241c0501d64030b5460040c40114a01b010170051509100340e0000c03546550000e00c03140360441c2182d21a007148400603500e0342164007403100c0c1100420501d024044d08004454403503600b049448001e0011000955584c501403030324504144060f40514566070400069105507a00021b012a507a084c07440c005894081150000c1c0c13903588080074204410b200c420000c10042d502c4200f90744142d00039599901048015001101c032441000c0d510309400d039600e6105082454030300c1c1c683e0b02503809442100e50f4005141c41d040d48291003698102c90310790000418200b000601120340142c04001c0707000700140d92401d50490249a0102401041580d5500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 4244198 1250 4242948 4242983
    0x30402090627130b0408040f080705100302070303060504020408030c0c0913020d06110d0506100905030706050c010b0307090c090807030201080106030f02120705091203090a0504110409020c0102090108060f03060103 94
    0x30b25065101d400040803135460070241410700055101e402a06114604140c0104080c0c1e0300060700030498401030043e403481152850101e0003500f01d604201e0030562104c9000400c1c0e51580050320203403541002035070f41d641e1492003151400300c1030805c06002d140301100b0407001c86908041c03d412240c054074000304000346468000024125018040c20315400031924022024140e448180302c1d49060b54000e2091100600645111199214865240e40f1920302805264800c0303000d041c0c0e180c40c02001240650300000024180741890b0002d035000c9a81d085480f0007154848095001801d500000d0000d80d0f045070002006c0752814050081130585540800f40082099030481e1002c1070000e070040b81c9810079800040c0154810783e8007500c6401c00101d2550034900200132103641130402003210140ba403030b00c810320001d4106003d0f02d9100c088240000250300940c2d0008000b00c0340c504000694070101c00d1b0000d4452000030b04520b029002000c00604c0641b000200ea034103403500003034200305841101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 4245448 1250 4244198 4244221
    0xc03060607020d0f03170c030906060f0a0b0403050d090f0806060118080d0206010312090806160203040e07050705070b070f0b040204060f06090806070203030601020d050304030e060708030402090627 87
    0x110041488a0351441e130418168003c002c101a9290b41649a415840344160aa6140022340c0d200e80036803c2035000c82d960385014000d8031240d0710080c101561640c0d484941e0b5881d500951300540d03442d0094100420400d40c40007001000d080c1d9403c4925403941440591075892000500060510640050304002110721040d4540204000c8007102d41142e850007000f5280c1c1000c1c8021110b04042e002d0348004140101401015a070400009010580c2e034601d01c0880000c0c0b37034402c02c0c25400200400b0900e51080c411480c0b00d506c032380d22815502c0c0710034504549401015445981d4421044c13080b18000317042d031800c0032406604000480e641c4e860b03900000d402401d00c0e43c00312141d03103000800055440e4200c400f1808848024080d54503a544080c01a81c491004440d200e006030007504068031894020006141c0044c041e242034461100d0307520100781d9590010380e081e122081c01208110840c0743c5410744507404242900e0742030405043d90b1090fa00c4002381c1e114140b402405000013030140d00c98 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 4246698 1250 4245448 4245469
    0x507050d050123030d0c030c060213120c06030207080d020c010e100c0207090b060901080c0d020301030c080f0d090b0d0f02070303050603071220120a030201050118050c0306060702 79
    0x14500030001c5507558000c041c5240501401d18003454090b49403014980b5005c80d1007026040e69403204200d020003035504841340c100703519044446542c01d200941d55404000a16809000103100d1111148a20709142080d400790354042c80405004018240005207104280c481008a5450168481c500c40d01c0042c050010070b83d8411140c821781000c014802000d4208070103000c0140c003a2500e180d1280c41c00005e5544180905801003020488403009502c90f400042d405607200620300d00f40010203404206070390003a0b00c00d50b814140094140987c402c24020014450450743c02420090302c01d21000d80b8030b81c150711a0b80030140001c2109481d4581d203400c040d46c0300c07000700021552129540340c00b0b0024075046e00e803c1c0c020b205061010404d03030301c0000d2210781c043c1c2042a040e84504c0b0005002205554800d8950b0405004406403401080400150141e1403003600045855130608400005c0401c41001d4200254207110500c00c10100d074038100c98000d9030503580c1560328040f41c0081070030b4202 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 4247948 1250 4246698 4246717
    0x90111011d031b12030105100504030501060b0702011d030601060f0306050d15050105010207060509040203040f1a040b0c09150a090b030a05010602070b030903180a12031106060105040e010306050705 87
    0x1103040c061000d0201000800c3c20716002074105188211030002207030345088000110350030150800050010b40f40c0f0310a4258407079400c0c54102c2c5415160b580303a0f402c0d14040e5201c8503c1d0440801c0b400215a0030405502c0f8200c11a5600000e11078100c00183e640e0f0300c103205200600071100c800c3c603040c502c03a8202c4000b40c003020b0002c030701d801d451b49851034449000c0146071109500d00800402c0320340c4081b460704103d0b00d55a50302800c0c07450a2082100030b41c005401102c0ca4881010345500085100c082c6054040e91040f0b8201545481d080481d02031100400c14010341e18100000c403042c1d62403464000129000308281030322036107140c1741942c00c4000d0b0b80051551141c040100440c0134616001030307040c4c030443d50a5805843e03841715240c1072400f00359500507413504244080e4800014401146540380402082d0314803007540c0c0d0b0882003c50105c090142c0010350789150203a881d04003000010b801c40020f18040349001e00e0302c0e84910b504a030600008001c141c980f40400c9000b0710030302c2554007940 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 4249198 1250 4247948 4247981
    0x40204020d1802040e0d050a26040303020a0806010305090717030409060b040303020106050a0308030f07031b0201061d0108070e0a0204090c0503040210030b030d11030708030a050906090105090309011101 89
    0x3880c80000c4251003400c0b00128415800c00d1524100142c0208141c030311007442d0b4441604000c00030005540f46044d60703d0040359000c007840380c032080e90780c0c0c03090300760040703001c1d4400594031b15850310001c007080f000030400c60515040c41b041c0407408030006010380c2180d0380c0c003040124000850b1105410b600c41c9502001201d81407000106817900c00100400849200390001c0181c02d64520a00842c0b802521010780b5000c024400607405e00c1c40c40007c0c69001210b4940001c0240d68505000345000b0850440c0c0d0040c2c0d950541484030958014100e0701441da88a0003c01e51361400c1c5400d1b0b5240107034016810100703640342c042a1944040d80543d0702801100205204112034210000c0040c1c1049806911400980d80951440e5019100355021404003501400ca06159001c0a5401c0b04800ca08604a44801c010031400708100310040c50185407418004240b034200701c0c0d4442c0c034103000680004500d904d840240b1161484c0003084400e014401c0c00c1c1100c0001280300d482e4010541510801d9928 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 4250448 1250 4249198 4249211
    0x1503020d0308160905030a020409020301020d050a06050a05010305010513020c0a080301060201140601030203040f080c03070b04080403020a06020609030711120303041101030e030705060a02070204020702030304090f110702010f08040204020d 105
    0x60700442c55920440d00c0c0548a4000c602ca0350701283c5504042c86000d80642003d070300c1c4005428a0381003014a82e00140000d8509070030f04440d0070490f80300711200c40200e5501c1009002078a42a80050000c3c0400d01c1c050110b941000d001030560b210505611002641c00982c43e089804180300004d6200d800c0302401d5100d607914100680a4001c035003a804400c400840010000c0d8000d10a5902903034210301039402d0214140c1d035081c881d40c400d0401800b01c0c4000d22070348001404940040c1e2046201303a20244d00c0d00e2640c0705105821030190003400541d0072502c00c01c60800c03000401d450060340c2154007401c4680c071140101d144012130010341c00c010b000000810042c0202282100318071402a60704000e5040c036500100d40fa40950a4002c000d508140045002920030303401800d001400200010b14008a50380020300e1584558042420340d51030381042181c001040c0b09603092091020701c0d40b85030414541c0000c1000c0c4c41d0ae140d420620258402090564541c0c1e8162500c40780e00c2c4008000c01c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 4251698 1250 4250448 4250453
    0x50d020a080303090303160801030308060d050f0f010e0105010f060512040201090306090503090307080c13020d1d0a0506060d08070201030504050a020604090911100509010c061b0909050604090201121503020d 91
    0x5943c006c44002003d00c00c1f00601c2d481091180455604076501a651303a01d0644882040240300c118840050b41c491280d00259106c5260a000c07094184040038000603015803204031450a50300f0591100907075082e0885c0410419070050200e03854142d48403c5884160b42d00d100580b070158140d000900610710f0485000c04014002004000b404400c80444914907a035200c0e0582d02c80e01035a0f0144c108492800c406401c4041c2c0e00540401d606190340402d1440c001c0524543d802c002c0d2000d100954401c8a641c000d00109101c01908000c05a0310940303107001d203031990710181c400c0d010002d0425654100082c14804c05115100c85582e00074645541c6690701d0003150060030304610140c80c41c80b5903000c45046403500b2101d5404800041d01c4050601c4401001912130341802041030722090303125007503800808541e02d502505081e01da1100302c146401c144003a070403180003e1459000303501c2e01850701c000d07070303003080840c3c0c90580722500104407445080030039035580b50941e00c025040007891485604 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 4252948 1250 4251698 4251703
    0xf01020d050603100903050a030902030703080a0203040608010e01300c03060b040b04020304020a03060e15070504140103090c09020a0903080c010203010303020609060709180212070e0a0605090604050d020a08030309 94
    0x16a82c00c800701c850f121480070180c400c6612821004000ca02d00300446074016000c0e8220700011400202694220ba03600d40f1002410b03407080260b0001a00000380a0205070382100640303002d030040709041100f541c11724503080366040341c00000a00100020310074009401040b07820f0402290700907841d049840e07603841c0c6080070b81003403103000e4492828104e070540c15051034800d480c410364000700900310282c42c40d00e07920002c10341813542d07210354000c644071038421141d002e40560041079130b82d603007690302c900c1c0c20500110303086c1040800341018100380c03180b008207110041c0a41603440404005a46400c005815909189594801000f108000c5284000c0c0481076009d94100e074001d40036110075a0340e00d4592074850804880c8075020605036042848000d03201804402c000080c2c6030010700e801c038001c0710000380355801c840403000504400b080e150541045085480103000905100c0e090120b0000040e1086c002ca002d49805100c59420704000d564449039004024400c000c1540d03039a0510450b0540c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 4254198 1250 4252948 4252951
    0x20a0c0302010501080c0607020405040f021203130e0c180102070504090516060503060604030b09011104080a03020d03150605030603030403020d03080a05060603011203050a020c0301110703090e0105030d050a020f01020d05 97
    0x2000740d4a080700002d15030001050050440038010120344c90802942d003004001c0601900644000b411140c0340401a1203940702c1e0500050f01f1070040d900d448800b1140003010205801001004128a00740100740c1d1080741a17444801e00030315248010850440101e150901c1c0e0751020703912504043e403107010f001d80810416000285a01c50b610680c1c0c4416064645100c02d5030040d421281c10030041012500900c2116041500a0004902034200c081c04003990b4011707030416012500500b6201c001c141e0108124604058281014046420b0b4002c110f0a0f2455602c030b0b003402d0040000002d9010350f003d104507806198001e181c4000b65099043c02001007400701c84401c081441d04010a1841c503003042902e040b101088072018645841e0f07036046030f1540001c821801036200301041000c0583d401e00511050344150440c4580f00c000728240105803c026501c04200010701c0c40040c001034801040c441c1c3d0f03900707a5061241e5a8403446004074601442507800e0810ba510100b24180c6100c45900001d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 4255448 1250 4254198 4254203
    0x2040902090c0d06050d0206090913061a120a0309060c0c0803030103030302091c0b06130e0708100b0109080c100c060c020304030c060206060102060712090b011e0e0411041104050301020a0c 83
    0x1041300c0c5445106001c4e9081503400d001e0b5206c0380501a042d180e107049551158002d403503404581d510082c9565410a41c0c4004154205e1070402d840071a40f1410880540000110180d00609a1a000392005030241c081d44c0240420451402822824041014280c20040225000300d03a40e82da0340b0f01f001030003500100402446a154442c0030403002040b0320004000039002007000503544c0304c031420040d0035400d12800a0340d0980710342e400002d80c8010722030b58006010390806400104800750f9800120b402c80f01081d818800d0703110301480307841c10005001803240380c2515001910001c1b44000d0b44c0c3d10014074001461241046400c1e40c1e4143c1c044060b004880c442c01d01c00e0951038a803102a40c607041d0444409005910010000740214424403081002a1350808002480c44c41e6449114002800b40c1019140e6141c80c50141c4143c5d24405100004014101a1000a04060b0f4170701209428040030b0034071880d01d928464240f010554111030041800070300842d03503014442c10240400c0c5e2001000d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 4256698 1250 4255448 4255451
    0xc0203120c040303080f0108070b1605010c0e0103050a02040e010b090301110a0f0206070302040803120c04090c0806130b0a0303050c0705040504110109150509040f02041509031209050603040201080402040902090c0d 94
    0xc01c03c100c0da00c0b03242d1b6059402c21009801c920307007400c0c2d450030144c000750b40382203c3d110fa01481d040411003e218458002943d5a0b542c1040e01c1e1070303000035055410150800c036240b44100010401c85102a040c0c0d8195030300d12500c541d98810800000340903003400101030810043c00a05130702000d4104030000e20301400d94090703a42c03e55510505904030300403840f0300b1000742c00800000400e80303000d00380190301c0a42d00c450b46040c41c0d2690b1941c0300703c801d03000301c081c0458000e13418001070f49000d0701400c0180344404000e021142d0850003084040507a8440241400400f20300c02c0111101404800080c220107441040540b03410b0030b1000020144449150100740d00c6070020035001011003940c0050040364840c6031411108200344402800e151800780c1d0550b80c24080030070061445250715401c4502c0750760b08100b86085007098440741403400c00f182d061100103002004135884e0041526401502400c00c13100546e200e0021030080c0c115000003e520140035402c0107c60728004002c1c03c80c00e00c02c03010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 4257948 1250 4256698 4256701
    0x80105060310051c06110c07081209010f030e01090309060305060102010911011b0b0a0603140c0306010e09010207050f010e010f110304060207031202070f0201030c1d040c0203120c04030308 83
    0xd10030144400d440080c60994580401d01444c20081e5014901c4500840c40310f09902084e12504103d55040040340c108070300000c4c5954a8040030000315014160100250a1500c07400c80ca1001074800c0264490520807080a0079981d18040d5000c49440d441c158020b0002c2c0b101c900c0e0081510416001e081e01107890b010104216510501c107924815a000d010303a0942119103006486600040d17a8503102900c8030074203280001c4003489810300514032180003142160451501c021070f00688501c40c1042e9203c400740c403129a900103001c03070441c1d2000300d03450f0036510349100d000e02900c12140098903a11541d00300100d440c2d0154403054400501a000700024901c0031108029107a03c0300c3c1587e0365103424408540030071010781c0240041880303030500c01c000000d61103c0b0f00c243c0e01b00b28016113840400580103001c2d541c00d0b018035106025035103402404650725243e0581140800b03944079002d036a03201000311402e4020400c0700c0784124444070300405494050241e081c19401f901040b400a1070280 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 4259198 1250 4257948 4257959
    0x20604030807081005010305060319052107030801060e060403021905090a020406020a020f01020a0c03110112020f031b040518010305070503010209101805060a0c0605100605070602030604020706060e070801 90
    0x2070144d0041c0c9059030096440c514000c011005400c0290100d5410301039018494114030700141c508404510036005041c03291021010f1070100d1032001c0c0d41c4062810100709040000341c0c006000c50645d040b508003503090f400c480d00814054021a08000d4010007851100c01031081c1024030002182d00c100c4880741c40f60385840e80001a8002c502c1020056030088090000524000008101020044c412200b540c103031a11405501000d991003a5640000c1c140807124a59000e274180302d4540140ad4103500c0c0000224010134140710082440c414082680e41d600b06495180040307500408004041c6000c0c0d0b01e40ea441b140c02c42100b07210484040c440c141d030004483c1410300030394405420052644403183d02178202030750541c2031280382c0d03140810b00e140007140f80d541d6240682804038003170340e42d03201a031290325040c001c980d0040c010a0b81990001020403005038031000726941c45920180140e01da458030703800310340a4060380100603c858108000072a020002251040c450380003951074407080d99940303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 4260448 1250 4259198 4259207
    0x12010603020a0c060906020c0a030c0506060105090a120311010507050a020c03010b0603190e070306020c0d021203130c05030105070201020c0607030b01091205030d090b01140a05030607030c020a060c020604030807 93
    0x108600b90108900d111102d0104000303501c080b1001c1c0c0146005450400380c0d030080c47c1010264101140410b4040c50160188603003080a81c2d409202802c00600d00760261000444041c400c4c425003421000c04040c40b020184101e408205500c560300c006d01a60400b80009800e61304008020070051145000300c40440c601405000c04070840507007a47d10f5912207103107090b403441800034800c442c142c41d10341c40602c001081190301f0046010380d500580ba02040d0803e5402d01480407000310031544400001d54040c18100d0880307400800201980076600e03176920301800700d625143e21090303041d4a8031303040010050f010340080001080900695141e6500e0400a404456480350038031300003070800d101441820103517203041100d50301600480341086200d800070403c4e1b03000710000711410f40070580100051010707401e050f0065041111003400050a00010a0740c0c0d0200400c041c040607107070806c182a45009112654015401c540140b080f64010480a0f6440c002a90120002a0701b840001d0308039205 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 4261698 1250 4260448 4260457
    0x111002060118050c070804030f03030b121e010f05090303090105011706060d020406030203030d06050a0803040e0c030402151908010b090d060b031204030b01030507060e010207030b190c03021201060302 88
    0x10a5115400c255802c40382d07400a110080c1030041c070180c1001702001040401d00500003c41c071441100b07441e41242d10300102a525488110782c020308a80d540c3e9000d4000100340822120665a0001000b14003007004501500c034000c000520140303402e0a20511240200003035101c2c0304640004e100b20790f42c81a66442c91540081c4281d15508083d020a8503482e080006050440c0000c0c0040381e5941c0701c1e00001c0c250791051041300d4959a550204210508003402060010300010001e035060500d8101c1c0e8444030b2500030049014100c0c00000a0210340e01c000b0b41a15403110510080d0b11450204a4180c4107600c0c2401c4401242c0120000121045c15804071880200050070040760011950f8034a405442c404082c1e590501500750003205030030154002d4801113010301c900030070b0365240d41403a40c1000511780101d1308121190402c0549070760001940401c680d0310061001030f03030b41d404119500c02e051460501481c1030030700030005c1c04561b143d001b90500d080740000050b1540da82c0c07107090341240308 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 4262948 1250 4261698 4261709
    0xc0609070e04110604030b010909050d0e03150405030c070b030f0a0501120209100e0709050111010b09040b070306050312030402010201050601020c150d0207020d030503010807090e1207050102161110020601 90
    0x551000180003030f10030450900559005030460341065141e581d00c03003001400742c00c024451a542e02c0000d003408010002d40300001413505042c2440928040071035215841c402c8580c0c50000d0500209040220810440d9545103000c0280c0d4a0603031508003203141c2e41e200b034604803000000180402c2d80c0318407038801e980c12617500b40c08202100ea915824810713844001080c0c10200d540f080710005905105203070705403117131007036903155802c4d00d003007400160120803883c0b0805d100d0380c503080c0b002240e51103100c1d080d03400c1074000b000424a031303654440450103031100360046034050041030408410352050ba800b950040e0b200f600281b1003a40d900c1e004a0ba902d6412601c580e12551100e60703d10701d2400c0d000241403101240c04058501111030700428001181c0903811400100000010031402c20140f203c40003030000c0032020702804a541d02241c2d80d5000070718000910071030000d842c0f01081000d5040700c07800703c0070032460802d901440c10919456962501c8140c0a8220355080c0e0842c2440498800d040c1e40 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 4264198 1250 4262948 4262969
    0xe010b0906030103030807181401020708030315010c080408010f060302100206040b04060b040e0304030c09110703090501080601090915080105090312010905090705030f0d020c010e01050a030504110a06050c060907 93
    0x20b2858900300d41b00d100c0900754105100707081c100c9035103190100c00d0380005015110036014800783d0000c002032800c82c0d261300c0041990018001d100b140703c48500c1c0600707246402d190141441510707040010941c0300c1ca5116410070b40c60600007120b66280c541020044a0080314202410740c40c04105980310a000c40e002040c078500c20002400041c16684801ca0107480039100056400001e031060745154000d800035a0061106142008502400d006042940c81c0c002c1c80c20b410802c4607900504000d19a01a541c103229044c000903150386d00c80c80000d0024041580103000009074003a800f0507480b1180580d084039400c040c001480502c00100300d40003211001c0c5400c0c02603180c03220f454024400030f45000594011141d000485075402c00c92201400c1e030290103003030029a4410003902c2c103030307004076002c0c14441d20b5800c11a40d603030408243c8040001a04000c1020383e12407412007081c191340038030260b000c8201e09010403585e034420003504200607490101c42c284d4075000c07041555525503202d00344125 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 4265448 1250 4264198 4264201
    0xc0d030c180602100509070b04030317090a030210020a0e0901090207020a05010201020a0509040207020406090203100906060905010503010303030f2409050604050903030105060f0702030d030c081f121103070303090e010b090603 99
    0x9403640f00c507a004c41b031101520700840c1c07994a0441e00340e20036841034000401401040b21078280807004d0a402144c4803008101d010026036019441e40000b603402c5079001d9020606850043c0190100022040b000b40800b05179030310f81c112a402500440010303030140c141e4203408030b03031940144200e50600c4e4058482c1400c00300001c0810006c2d51005d03604903002500e03020700080030803280c0081e40c010740c068006106c2e240e00307205000046482c150f02c02410040c0100041029907005002c8906403a05480c01040500f807907071600015002d00c452070781850f4000d03500250040341444032402a81d01c07100050003a521031600b00300903280c2c107540f80c880c6034004000402c59441c100d4000c0412911141485081102030340010f81080c41d10096140400c0d12441e00d1401c40ea80701c1a01580310714410740054140744111480c0d61050381c140611100c0c0030140d03d02100f845600c0c0520191080014204d0300c81350f0303d030300e00140802c4039407007441c014003810000440c1e180c4c46401a202e400300042c02040c00c6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 4266698 1250 4265448 4265473
    0x200303060f03030f04060305010312030209010503070503131703070f02070b09010804030210021201050a2c100f0902040f120305031303030f02071a060102010606020a11060c0d030c180602 82
    0x4071006441c503203502d84401c00c8604c1c00701e442e2801401c010305181d1400105c641c50740c140020504a40d440360000c1610400c819502d82ea08401507942148407481c1c1543c8030b5071a600c0709040c10b02c041d0000f408840140507040b104466410095214032180d5603090795907404001c081ea5200038500402141a00500c1280030551040300038070750040c0240304a448000803000c001e170490b4001002c902040c1c05810042c4103c2c03c00c0303d5414010000070703030310100c4d0382c45803410190303a9001c035800d0b081960f1282004c03803030150900440c034000d0180b0b80030745442c0c01c0e0341c0d51004000358002d1045200b0140c44d03200c00111400024440c0e0130590701601c80c40d10f95a600f070214a241415080c0c11801e05988615621500d0310501c040e085c41840b4203441884c9a0310320065200f000c100030b11075411603050440a126071580401c8012045070b02c502c100c81000c0e00e81c000954140078207001c614803403159a81c0c180101c0d40c160400241034100351136a000c160807202d41990589185c0c02100d000d81d1042d04103114 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 4267948 1250 4266698 4266709
    0x504060e04120512010f06030506100c020f040e0d0302030a06080c03100203071b060203070306050f0a05011101141e0108070e0c030a06170d080c030912071103060403050a20030306 79
    0x502c14101c1c40c100340b0b8201038841e4002c80c08000c0e0443c00c202e0842000030301c19150140b00d03403a0003400c100c03141c7c182164000380051190410082c000c1c084d1652403501e228603103840d005000c02007800410780b410412000c00c000c00035001290545900c074100400018140b002150002c3c074001e000e40a8002c0010a40003403029601c0030307141408000010000002500f540400c01504c3c91003902c0250366400c00d120024141c4d68170f80c1040303124518039110884940c1e5000544007c6400a0802c1da500050b40c203102e500604010f000559214100c00401920b8074880c800e1548800d564400c4441690701c42d054076507075801600488024008100100300e2200c0420301a507408110a00702107402a281c401750941ea0014a59000386c07948032404010409030425130032688014028a01800c6103810f460703050f9920407910710007440410029a0500384400081d55170b0448002508540140c01d0600d4000d11540c07110105000184200110341943d80341010103d503600f405100071400d50325104100304 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 4269198 1250 4267948 4267973
    0x71703100b0406050d0c030b010504050d060f090c050306070302070f020918070f0513020c03030103020d02060705010c080703110c061f030501050c040501030e0703080403030302070215160c0504060e04 88
    0x40c000400c0000e500304848004101401c901d0351915110802c444016058803174101d140d009040c18100b0740100f50b41d00100b47c0f01140c5089074003500c080c0741820110010002c02003501400741c10034043c0000d1004008101089070015011078500c1c0e52040e100310100d0198110007444403503801245000362410404582c0c00c407a0b101e28541d80030f80301a085610344422039101c1e8071603522020301003149242488a80004680200d4107614081712260b000c3d8480c40140802489102d00d1030800056403980c00c1a14420382e030000003004000304050020300814030072188400064141070030b0700341c0700c0d20100544a1a0050500610454441c04420342400101421078040b643c250b980001c00f00d5000d008443c040d1350000d000d04c1e0307140d08001c00182960448503851006a0000da01003001a000c681140c04481c5c05180c01611746109100098001c001d0b410502d00003400424141c200480f15000f5408541c170500c0c4409285658409100c1558254407494420b5400d0a000501084d107540030b14 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 4270448 1250 4269198 4269211
    0x503010e04081207030e1204080304030b10030c0902040f120203030304020f04180b060f0306010602031204050109080406170f0601050a05030606070209040c080607030b0f120a02101112071703 84
    0xc0c10503040b90074003090f04030221400070000341c4800301030054200c1440042c184221852841c1c1c0f03880c1c02d188009641e0f209a12000306065131200001e201003444079008001b8540c0074502403805651460614013a40050113159454589220300140039011103040d02c0130541d025015504664032a000c0140403038407903d4070768029884000d03100c14095001c1c0401880e604c5280348038114101071081c001e81c0c0760300704c2c039107030207540000b00503c0300640002c01d460710b500ca101c203014025600d0b49007a030b02406d5080f4004080f5200824046a03580d004003111410310458403d40e40140d07188400dc4000e00c1e019030700755012810030844a6032903440b40c0000e40d40100c01a05a502d4281c00307038045400321008807002e840a8014030170900040f04280482c60b040903540c5000d11011803604001100f5006410140c1d100d0342014031501a5143c3c24031100c014507400800f14000ba2a8041024003031540388a4020528010b0008201001c4d420200303944d03070346404c181c100c3c07240c50b102120391101e0350019160 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 4271698 1250 4270448 4270463
    0x51003080307032a0201050a0203060102032205060304060c020606010c03050a030b0109050907050304050d02010203040c06121401060504060e0604030b060108060d060204060302091305070c02010f0e030f070f08030304030503010e04 101
    0x510002e10004028244002d004c500400054682000080c01c54901410390321040b80100b040c03118580e4000251100e450354030268070001c00000c0309401c4a0b40741c950006401c440c0100401042c4900c0e644840c0042c3e20b180c080d80c0d41595200011141400c00ca031000b00850800c2c0203030145284264032a03c1850010304080440b5600d40c1c00040825204448080005500201700f1003040001e01c2005800080350000707500b141055500d4040d0641103008141c20042d105040009181c195004442c0d040100201074000b541c5580c1c000703140f80e1081c09000c01041d2445c18241c0507003040c10496084076084401a40b07103031580001101c5003030020704000d501c14440d1800e64045070f041d2000b08000c142688006951b04000000d2080401e2030452003604281303010200b09002c0d070404401120f007507091134090141084071400303552540e44551007a03010b103d0101040e80c1da0030f0000703000c426035007581c410700394180e91100542e076280b05c22200240080c0c000d200421000030500d8100f074100d48140c05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 4272948 1250 4271698 4271711
    0x106050301110309010b09040b0103020f010c06020a020a0c1706060904050a0210080604060f0302100e03010f15030c0801050c07030302090a030b130b010e13110315040b04050c030105100308030703 86
    0x6800d42e441220041ca420b1400814000424003d2103030000c0a01c060300c1d16074441c40d00f81c458040403034052002900641604940f08150f0b1310402070000d40d42d5018204544800c1d000348001d6507180e5250040715015100c103000300f941251b010020a01c07495110007001c180d51001c090040464001d002114180715101c02080181d0720200400000c11040d136850400d480d042007008140d40240d80b09105400c5020014000b6864500741c0340903c14850034070940204050000c00c2c010015111480c05c10b51400c0c150701686000c001d00001100d008846980496499070083e608a0b24259142c4040f240c04010580019020760050007505100418894000e90b880d250989500c1c01103c050041021001e1481300b0400c4190f9400d0140c5101c03411401c40e0b191000345041a419011005400714034002e200c0c2c501079504000c5259605410042520749090900e0840344a04042d90100c407640500c9001c049541014031070684669030901c444c8000034a107840710880b541c4041d0045007051340b40d28 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 4274198 1250 4272948 4272959
    0x607060b030a0606060206071803110103050601090312030204060e030601080a02090408070c0e0117070501120209040204170a0212010b0a06050a0201020d0915060e0402150a020a05010e030a030606050307021e0106 93
    0x4544c400521054024064074504410002c1c0803d51212240381c80020545080c00403500311110703089510820b0030001a20745030320380182c5290301c0c2503100400042071424070344c0402c0d174140c01500c00c8880540360314650010420805072501001d0013401c1142d408000c015015241c1407070102e41043c062901180303000c08540380c40c0b000d00420b030050f200207080c0600401001c90008600760071400501c02804081e0300b00400284500e0040481e009002e40100d00106640e40d158101c40080490308004184180411f1019482d05d50412090f0f110b101071001268a04606001c0c5080c2c40380024a0300f41c0c12403c0040a441a40003001b0700802c40d1f42c01e00c260740c00c40a09106001017507001c0e40184005a0058441c40152145a0052440554004e0620005881e00380c02d000076102051036141d101d0801e201e00b24584800020041c081d0340c2030246004400c9000b00003045450900d540901a0390f48a44041e9070320700c002e55030000141e0081c015280d240c04c8002403c031840c1d80c483c001007142e40d03980 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 4275448 1250 4274198 4274201
    0x4030c0b100f0603090507050906010e0301091a0c040b04120c030203060405070503070603110306040905030705030708040806070503090309090a1b0201060e010e10090203070203070206030406021e090607060b030a06 94
    0xc03154040d40950a010901a14000501260082181d46011701c203080356070f0760305915022280321b824012030300c003404100582e0140b5000d240204003d0300030130501c00c560811300500d040d4840d010071541030f0140841d072845400000c407070907100740407903ca1a06182143c032203550703442ca19050314220042400800183c1c0c0910034980124000c6004103d0641031408043c04c00079241e21402c140b51070506290024030300001643d82c40721044400188506640c2041800c5102d0030200801034000050b0b44010440c241001d0700070355040500300e60317441d0346078002500c0612050381c074015664418071210b42503107422050290700100c208070104210450680d0b03501080c03650800000903075181c0200703000d1011140041801007035005050401410001c2c0d4450040d526801491100c0780c0001c00504d03207500030000c60700c0c0c4e941d003e070007030740d0720320f000e007804002500701c00364191220901c081071050305407802040d15861040240041c0c501003041eaa200001e04002c40e02c0c0ea09400707550101c2d40458020f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 4276698 1250 4275448 4275451
    0x5070c090e100c0503070c020607020406080106180b041404110d050715030e011b1d0d030c060f050103080d021b060a050f01060203030f0c0a0e12010c03140c030f04030c0b 75
    0x4a0081200c00018424035041c0e0b403d4880d10410003005108200705198004401951356805460041c2d0325a800d001082c09441c00d9002803603198200040040e4058418100004030f42c003080c41000a60325280c00c01090302d28640903056081c1c00710000c6004100007401c00c00300c80e03900500004928015988250410a00d9408003421040b0f403150381709440d030075000e00f12041111400030484100c080c0d101044800c0602c1d2000208140311084c0b007100e41a16020035403101000f05120300c40f500518005040900541c0120b60250a00c0b103002c04410250196605a075845009a0b041c240c0c0328807084001e4104e00c500e00704605a01d10040840e07034043c000309005004460001c0b650345020900e0002c6164103034003810441d4410403c028200192010154002d1040c00c0300554600c0340c0700c412201e454041082540c402c41c500f001d490301000550051101c90901d440600800380d01001c14103446004451403001c03903004200181c2d80c004a130003103d9200b4802c0c202160200819254089242c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 4277948 1250 4276698 4276721
    0xc0c0907020120030c030103030c1b080a020a0e1003060e07090f0501090b010c0503091e09070c05070602030f04050402090406170703110f0303090d03020f01020c0c04050a060506040605070c09 84
    0x54a043e0f0089001c1c4512070100e80b604500d4886245041184540c14140f005101c060300b00180e03c16902e0030020320352092038400ca0301007241c03140c41e034403111881e4640e041c03104228440d2140800001d0308840418581c0e2180e40c4031140000100d103561101c0b406849440d000389510701400c10081030f800150320a1740300890003a100010a0f41c1131807000030407100c86002d80d50510402d05421000201d00108aa004003015500d0700d0300c0020303407500000003800070803000754018803907010030800744d0340924450300903401102200c1089076585000e0740c581c446c8652451038403d0402091005003002c3c0c0007040394001c003402c0083c91944d00d80070002c01506188242c00241c0000b00108103000004039000d250b107100301c901c00303402c03250003000170f680e40300390b4041a000c0e00c01032a107501414000c0c400c1c0d50120788068001d640ea4498109090f44481004101d03a00c42c030300d084049420404d052050b01d06640380940800d2030b143c01c0290a03a240c0d0030110b421a00e0484041e004501d02036980141101802e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 4279198 1250 4277948 4277951
    0xd031b08130602061501080c030a0b03030702060a08100501030513061104051c060507030b06030a0506040b0303160309080606060307080901090f0305030402031b100c02030f071202030609060106020c0103020c0c09070201 96
    0x207105d07a152844444d0154880d0400c503401e42440010003036001200d41003a404500050a8202c2c900071030b00790f000b181c001a41c0170358081416044943c020105034030443c01d1603200381446407a100190103c50b8180c4040c0b5040c0c615008080000300164840b0b50103080a061907401d00d5a1100081c2000d000e0500481e1400d0f4925030500800105004541d04014281800e0008941c01e901051007408020704411540e0b4030741c40400c0c02c9844540c00b00c00c0601c000b03802c0d03a03138506011300501d10491000c1022000204802e174001035400c030106c2c100380128401071070680355445003c4121042000502a0012035683d402039000042404403182c0d0741d80e1180d02d519403a4645801014140f0002030441c0305035050400090f111661800701404000c8400d0604003203d800c4c07800400e00d049075a6000048501ca101d401103034a070084a424410980700300c0c00c031541341c4c4e01c40c1149600c505080c03141401592101d14011625030090b00036011500302c007000c59070440062400103001010984021000d81d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 4280448 1250 4279198 4279201
    0x20c0a03050415050405030a0602091f050417060402030a03050307110609010504060501050405040201020c15040504090501020306030c060703081b09060307090801060b070807080a030b03070306020301090b0d031b0813060206 98
    0x1c6100a00f6150008034209181850314281c0442d80315a10311000900c40f5600184003030403965040c040e0b8094000d81c4403110056402c040001e412540a17001d844079000040581d00707110800010f07141e202e164054090000c0c17450030f41e41916584c00c003822000604c55000110400d4034003c000e02ca10804280001189604290610030121101038204c540039034140f06c00c00000d070b40c00080c80c442090742520308410001451710b0b15800c50185403c066405418180200d05112054011b035004003002c4040e04d05114040741004001e00c140c64008011031a5000040d0b034a8024000320b152070394022901d01e18080d00c840020320540d00449546020030103c1c001071000c06801d1203000301408039455903600d002525201c2100600422100502e080c0c00010f890850034400d030001c540304a0b020303040b9400551a441c0480103234009000c3c9165023807400401d00c9d40e600e4a12043c0001c030f9015254002c0b43c9000d00400240c1041021003a90380e120104529414144502c0051004100650140619 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 4281698 1250 4280448 4280459
    0xc010b09060f030c090702011503140606030703020d0f0507030204020705010504050606030d0c060b060c0d02060411010e0a0e060f060a0903171e0a0329010e030609060a0c0201020c0a030504 83
    0x10380079082a010b4031051142c11402c3d00d00040446000c0700407520019540c0c0d4200089014101b10040b03c43d100340642000001c11007018106030030307411100d05807081c80d070340d05041c9640c51010740f001a51014100e60050045003d1110f100341c41da01400503100b4440e100e8010030281c2e80585001c942c10780d9550100300c00e0100030301100350401c50480161040704160b40e4010a054600d940241c8040d580d020100000d075600c138100d510488024080e6140c04a0109000c2e490340011034040e00d0404041902c5059584910301041180d0740040500300e1007800c2c50035000a120b001088103400c4030344007441d00015541c2e0405404000c0c820340e0344507902400c40ca050054084090320764041c5800034442c1c0703022005a0010381308500409038405498501d180411805000b070340e141000d1400c3c0c941844034880707039030b074846011000703003a200d044a00b03042009142c3c1e5407104507036825280c1c10000c085048254540c200c0605e14031544005401c1c042d191940c2402e04401c400c04401082c030001d0300700003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 4282948 1250 4281698 4281709
    0x5090613030b060906010203090f0a030b010b07050d020606030a06050a0b040f0b0f0315010608090a0c0303050a0306080f1203100305030d050402120f060c03040201030609020d0509010b0a03030207030f020402040b0c010b 96
    0x50010081e13920200c10308244001039602d02455941510410745280b294007242c40386400900250f07004500d040301c0e56910080d8500590050206803064020412003001c17003070000a54a016100160051001402d50f489280040001618200c3c005480c2e031070300000c1d50380c0c078000c0c610502a2030400288011003501007060044201000c2e41c02600880c0701c1022610103416420304681035801c04681caa6102c0c04e100e070a01e0203107540245080c61a51010050642c404042d20f05e00b401031303d040046686821020750b0320780c4554401c8901da0f01c00c05204e80301040c0034003d140c00200c4820441c50b41c68803a5229402c5410825100e070340720355140d0821081d442c0c01c00b54060401c0e42c0320050105000d407941c40503240c81004001008058001001c00c013103900c0b91b0f020000030104a01d045440750069140f28015207001d540040c2998240110a54607145c154440411079034160010030b40706165540c0c400201c6239051061b6403160b424080052202082030041071651004000041c180e03407d04208003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 4284198 1250 4282948 4282951
    0x7060b0102071a120405150a02070203010b0d2f0406030b0a0c05070503040308030402010c060207050f0616091413060806010f0801091101121d030705011103160f05090613030b 77
    0x38849a00c50042d0020f140080c02c0b40c0d441009010901c03040d0b5140d0805070b20b008040207050000204e80d40030030a900303141c1ea0150500901c00c4000b40103541e800020805c1d44141c0b0b02014002c070b1002170010030110302a0400c0d85800c0c968019400001c0658400101143c000398000c0e10810318480c00c000340c5001b1403080e501c005055042c164100225a01e5103552800b4030301009048100010120741560b02400403440c42c0d5601c4801990340b64079625005495050340c0e150312081d4032038000403031a15410150321238964001030f9244114585488100d04c0059841400d01d5003003070004520340d034852168000d0002401d40d01c00240455450320701c01c1021001e09601590480e454011600002141e2003014a9140000d10b00f100039003000c030321020020401208154804080d44c41840120076011001e4040c184c0650000c00c00030b40d100100e40b8140c0300403100d4910741e1404480c50050a40030343d1400304000c4507841d200382044904400300b0300c1c6a00203244441784130140082007040200700e41c84075 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 4285448 1250 4284198 4284209
    0x5030d0306090e030a0e09070504050402030420010e0108070c020105090312130f050a050103020d0b0d0308070f05030121030c120504090e03070c05040e0a150b0108010f03110907030204080307060b010207 89
    0x6510b0034000c008011b0498500d00e0f0140d01c540c4011001c01e031410f02c198180c902808000703004555a061500c2c1c0f07500d091480403409895407000c14515191980550109201c1e0700040c0c440c401d8954840c1400c40d0781440b001000c0b81803110502100700c90f610200001c2c1040d484503d405641d802440c0d986440300c1c0030750b030302000079900d4690080c055a00d40c00740e0402240d40c03e09015072140129103072a000782c00301e41c0e6029080200b21582405040e440841c41c2c0c001d80c4a61110407040603980400c45891009010752408440c3c1c150740e019264921007015420a07003e443c0009014030142e490744c8014000070326034000203001040a01c01d2481d2486013200e5040210001e500d0407002d9510a0503032038407440b6581c45507541750040f000c0c1036014843c108082e5400020307030340c021250a1110008207801c549950000e5959000420b203404c4002c41402540d400c84044043d0741d00c1902044140d0100130100f104041c0c007804005000c12007040540341c0a40324400125401a103000024034120711070303020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 4286698 1250 4285448 4285453
    0x118020108060a060507030e06090d05070303180803070f030c12030e06010e010e06010804020f060a0815040b0303070b0910061203031401060f050705030403051e070501020105040809060901020705030d0306090e 92
    0x3c0051302d81102c110303454594141454018004040d0004489001d0300310210b40011390845060f041010120320001582d2090b1100a4180c02c03d140b03403020b00c041c038000d44101d54010000b01c40440e103002030280702c09101e0f280ca070007001c099a0300c4c01031a0054003880000f00e51140542ca07901c403c144001d9000d401c3d01c94098003258500f11030200561000b03451281440310401c00b003402c1d910ba000c00403281040180c8050307561084158010020f02007181c04005094011a1300300061606001d03144030014020000e604006240e1100e03006408040c006070604d2180a042d19418085405054010102d11065144074200381c10044c058070b10107402c207146010903000512000c1d40045207425140c05600e00075480c0c5409241c903510354891030304040c00501c81c0d05c0e91079140c044504604030110395503a0686800c41c0d1794000580c02d80b00e003600c009000070303c140010216400c0080290882c2041441110029641e0b10040b90410f14041c0000d40029103540c0e007070100511030b011700300b03203902c08000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 4287948 1250 4286698 4286719
    0xf010503010b0607021012020309070806060d08030115050c0a030302030103050d090e130302030d0204080c03070902090307050108090a06050106050316080c040b0a05190306060e030a1a09030c011802010806 90
    0x500f980700340e91000b031080304206080c0b040f1078881d6146114000101d0021541e2741840c2104da41c0d20b00791849004a80d110702c02c00031300c49082c24043c0c043c00980c0402241d0440e420f0142910b160780c9280901810000244914190202e0400081c52918042d480c0140e50b0750540c00c105040c40040c8072518280248440304203c0c0383d58421020368403940d0010b1258460b0341a2600700e0840c41006001710440d40045004500b00c500841d120407c81030403030460f0030316540c48080398164060305010652641002c10204425400340040c07aa109000e4810b6a4040307e4541e2074204640c0281c100c1e07000034401000300440100405008010702031a4245446245400c0c0d1080da9036211700d000d00e40301e103800031072111440340c010020f03921040e04c44048d50903143e21040d0018001c00c032501c00e00f070009010b800e0000c000d08003c40c1d034480164100304a80c0c020859104c2c01e0b8000100607040740c81c0f0b440200702e0003030803030001e2041030a1021181003070100003404d400010000c400161500384615002c01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 4289198 1250 4287948 4287971
    0x30509030f0d060e01050d200609030102030115021509070b0306010e0409050d140403020f060702181608010f0501120c0e040c080115032306011b0f03020f060606070303050408070c030b0f01050301 86
    0x484102c3c00301c40b0b0703a400042148d402c02041441c018a07840c1a059800400040354100d5400805081840c09500b264240c40e0149460f42400600355880c1403240c00c030980034001e20806000460f401441030504480107218500480c04460007040c0950321504500041241c0035403100c80182c0303c007940d03554176040a044d03400113101c5085080c3d4072803007880c0000d0300e881151138441c00c0d84d59500c144044c91001d4540782c1e0800110440301813510340000d0304000046811060310001405990f0180c1d2101d850440c00c114080042444421a4040c00350010600f941903950b801500180502940d6064607549002c030110030a04100c54840241070a103034800c02c0300170940709c0900b285520744210300c030a911040300590398480f1001c200d030406d442c0c10494400340000341e200c0070b002600c40e03800c0340d201c03100d490ba10039128942680e00301da00c40010404074011900c02e81140d50814010713415585051000d0791455215070140d8800c40d45241e0075070800c80c44000b030050980c010301d410340c002d2114510300b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 4290448 1250 4289198 4289213
    0x9010906050714070b030a0c050412080c07080105090c010905040c02030703140403020a06030203090c04060602030313060f0c0c050d0203040302060403021e040903090503012a030509030f0d060e01050d 88
    0x80c01040104000822008107003c0000295048015031900340c802c21501d4240c1c40e0f4541c0d004403030005079039040c1404490003d120303004450844940c826041041d1a0b1a90344011070307440307101501001d1148e00c04c0400d802c0030a2040c00e020745800001030980d00002c030009041c12005a21852003245081c3d540d05a040c0c001c8120b035171850741460300e03a1302c0c1031017841c0343c0c91113000d1034202940149110001182c59a0958000c5010b18203482c21141501580c40030030003501e00b00d02031100160000c0c80030900001040c28900140b40c802c1c1e4020840001201c0000201d50402601400081101200c0e00500c03005000f9000001414401740d864103007036030040ba8040c4100c0c80000e00038414001040204403007000b0240f00c16400034418042e008107420001d010361041d0082c540303e0f5203844400721500303000707046900003180d0320407d25000c402c0ca4007060b002410700920301401400104007900c04002c2e8440204001c404d0601c002440c0c1c0d0402070720341e02e1040142c0000d805403e1035501c3c8404103816 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 4291698 1250 4290448 4290467
    0x81b04020f04060c0c090501060207030c0b13030b0c16080306100906080c090f0301090605040b0a020403030c06020c0111030901050702060a0605011b050c1201021c020708030a2c0303060f04020901 86
    0x3c9040c5203894003984d1402440038042a800203108920388000402e2095001c10240212401103441ea11030a803110410355a5100c0c2c4400718000340364003d02000014841d220141d8401c1e04106800e00f42100340201400d0302c0020141144d00080000400c100c03071a001101d00500e0810342760480c0c3c001c5c14440c000c3e01d245009071924200c04008203006800b0b07985c080d030201002601800a101d070704250725010001d03000558088983c0703030b0101c3c0041d6000381684203031000c90341c1550b00d200c0740f2071540d03c801c8000d6000c180700d04190354880c2199a10815200c004501441c0c01e00e000103001d142000000342009405840c4140c558203000d41040380e80e90000084043c5420080b001080c0c03041482c000d03140074424004690007040081d4000f5400a040d03000c0c00020540c46c04200b8104c4007002c13940228855040000c20380074050001c11007541003903000399501c41c07800f0502550904240d002c04510052403607900290b41c0004100625401c0c03603400301d04203a405460a606203010b01c0c0000c9c028642 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 4292948 1250 4291698 4291709
    0x2090d0b090109080a02011a120304050d0204020c011b08070201050103020109030b0702010b040e010209040e0a0308010b0c030702060313021206010b040605090307030204020703020303010f0f0305210c0106081b04020f04 96
    0x1240c00030480d000c40a500c51400541c1c032a40c03066940301c001702d0282c0a02140100d01c40800300215205600d42032241c103003401c51000714091482c0078140b004010100c0705c64801603030055400c0c45660f510074824818000b1031892500400d4031030003001001011044000c00f80b40459050500400060b604194000141c0741d109503082c200e139583e100100d0040070341100342540541824075420602c0019070007007c0082c81600d0602401d49aa1496aa030390001030006000542000042050010400c003a082e403d83c400203a1b4540096500090f03100d0b002901c02070000a4070107407800842c9407100ea00040c00064034061b283c0c41d80f40280074909030103070744900d01c240140004c040800380c0e414464040610750040046403070700013a050095998100340542d00e00443c81e19408552100112111011260304c08020150860401d515900800f038141c2000b000344400e00c005071103d07000f03024010161403580c1c0184a0990810408451926a03034003050045104201600194107158200c80a0302d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 4294198 1250 4292948 4292963
    0x308090607051b100806310501031b080a0b06090702070b03040609110603010305070902090402210405010507180e0403020a0203160f060e06070314090406030606090e0102090d 77
    0x10400004a50280704070340c4014001c1c05042c04030902494000c02601003024150350002506045100586aa100684005610990000d0030760800340d8405500040d00035060441e00512692814482c01d0b11030a0700b0848035400f028100121160040c07126900a040140060090805689172540281c8010b0003050003005564001000036008000d03540051943da0b08281c0e9900e0641840d900420700b6001c22182c0c0c81006c0d00071646442d02d881624166038001001d0a5024600b40100f0700a5020b6110385411130380030b0180c03071400944404803800101880c0101c1001e8a070514100342141d00007044241401401d910752044107001500c80b070180d81000d81110815111030a061b4500b0a417180e00a515220b07081c81403000002101400e82286c403200c410098840d1111015542c01c00d400d4038540e0005c3e014000d00010034454007210440182d196031162900900f81e010605440240e0019905d140c2c42e030b6020841e2000c02c1c0700350811582244000c50501c81d40b140000c2100302c1e000c0c005090070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 4295448 1250 4294198 4294207
    0x30204060e010806030f0f060a0e01140a0f0b0d030c0209010812090906040f0903020a05060108060601050a05030a06080708010b030c0402030c04060f14040603061d010608010b0c0a020303030c03041b0b040308 91
    0x17a102007103140d080c002518121207146000700103065440c0411200306006900302020003090100501400c3c0b41224403040380700c05a9284150b04000301081b160544405840c0e0754222601d884d15055200860b0207075071010b072255403900500c01059410703800820694007015142403070701c81032002d48110751003c840c511010b45407000020045d10307110f000705a080c1d16040d41303070041540008036007250700e00c21003e6503420382e0380300c0446445403030885e44107020413010809051102e201d84001c590201ca09000024a9615296403615040300e0350403d0b00142e5682c42e6802c0700e490100508440008106c8065140d460200340f481d42c0750045103c1d0606000c62002202d103000c1c041c4030849140549601e80301d0700c880d07079040020054072a0340b0410100080403805116500341080311141030300d0307907a282c41c2c80c40d92038003030009070a50154182c02464000c0b048980c0c01a0f905000440c00390074041c1486840f41441e050031101c62441400544441014140c20001a800300041d9021a60041c4186855 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 4296698 1250 4295448 4295461
    0xc0301050f03010e030a11100203060d0b06010309050703050709060e04050a020f061c02190f170601050c0a0507090501080d0206040201121e05010e1302010905090a0e030408030702030d030204060e0108 88
    0x36140c5035144c0d22490001280315107109500c000d150000c15841c808850200c1070341c18241c1c04034072090701c0883c3c04c20f5405902502244400c2c020580110041c0340026114245886290400350320b41c0046515030401c650801c002132840c010346000d032160800000190a1941d6582d58403c10000c00a0050b00b00d080d08105950700c11342a110356424009034a0210440d0707170b0b11a0000c0d402166081c2c0103011040c00d08200e20310652215a030040c450f210002c003104a400b91102d140001410141004030401c8040400b01040c4401c820681c0304000034a899400d00f00340005566058000200e580c2c4a500703410000c6600240550f001a02801d100310080d0301151030802904452005000c0400b03c03030400c0300d010b03900c3d074003882c103c800300b10a00000791641031540c185202050f0010b4001071004409200c2486c000c0308850308441c40c24400540d00505861050035034000d40d000b1111a040886e1030320a40c2824840c04159034609d01e400c518080c14110702800207c0144002070410a40d180066a0b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 4297948 1250 4296698 4296701
    0x2060f09010b060d021207030c0c0f021c030804020307060503040203100f020403021f02010b0a0b0904110c01060e011a030135010e01090303060902040501021c0207030f0309030203010c080c0301050f0301 89
    0x15500d00542015541c0c012801314001035401807204640d2040200002904d0500c83d101d0700c4120842540c40341150b0141d6150781c869030000d0103041c4c0e4003011828030f400c20012400840940d0354481e4440303440c0b9103024010541480280e07440401405010000c000059401183e602c2c140880400001028152409a40000e00807500020740284440d8150b83c1e83c100003c10844500840d80c0c0203100b02da07904828425003090910801c82d040e0301c1885895690720303158120301c40d84004281481d051046003010300d825143d5a070f000120f00540e00c0018002c8501109410031550005100b4514552400194040d90001c031205290800380d81d25001070304110246075000c2c3d140c02480207200b540116140e0500a145030041200801d00e415030025900d03165000792011980160080d08401081800b00303035811914201460840c0220300c000b0000420780303d107856080c1d00036600e448110307055206043c212407142c2345a50074804010300300f0491b540400c088078155181542c005c5070342c00400000c00e0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 4299198 1250 4297948 4297961
    0x3031f050a0b0f0310030c0b0c0d0207180e030d0504060203040201140306010504030b090307020a0f080d0207030809150d020304050a02010f03050405060402010f0201021201140a1707030b0411030303090c040609060602060f0901 99
    0x34004c7d0303592600041c2141600c07014200d00b0312004251a069041c04000740c0c1d84004038802d8914601084100300c4607000c00354812019096040c05803880c03c88a1203201701103030380840b01240c0060303001c001d10040d568031045022000c071048442d68914200400042d2913401684001040700040800048071000705000366545c440d40a0301c0310004680700c0902c0c820080f240e02a0f880e0500c101c0c294083c0e49480040d220381200d0304054942d141c00360300410301c00b154105c11130801c2c10510411103041120002d00c011449180031b080508064462403000600003945007114500b01410031051001180c80031425903001030382424000c1419845001c140d019000b424008100d03440701c18000505031804240c3c071029114100c80c81c03c10a031715818401144180c0a40c0d1051540c80071105000040b0380766032250f00079010b080550702004c441c400107031841d4400c456501c61600580d10f03202041c10107010b440080c0400c1d2009010361402c2040c02565600001c0010341c409500d0300220315488001c0d84501c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 4300448 1250 4299198 4299203
    0x110d0201050702060a020d020c0307030c0b0306030304030804060e0102010c03050f0f06010219030215010b12010605070510050103060b0103050606030603030708070813060c0302070b0405010c030c02030f03031f050a0b0f031003 99
    0x98956a03404406520384001c0601f0f000035004900304810343d0301d4085805815a0351144070300c45030506110001c3c45941000303064581601c0200808408101c85001400061035155500d91500111400084c2592803521a440c240b6040200b4030210082c00d1126580c0504151a8000f4942d40c02c00105c0c9400341c010700441c100d1131007401c0c0109140d804101c1c160780012203840030402d0707640c07030209404038422030800c6680154144010300020344100000c24a09000d00125041c07000d45002810446500f0b9104581560703903800012030958140c000e40c0d82c480310445c0d106065141420100391079101c0e40c5001480d00600003104010410f100c0103603000d01c0d074013240215640c0e842c0c0d90058000180d4850a90140c800c0710000952180b06600700c0d410b807101a9101401d4804c2031343c3c00c0d55004500d01c01240c0c0b60144600079045034108001440c4109058055540440800c0d0310200300e0312000d82000d802880e0540042c0700c910000011070345038080c0404c0550b5240d8510410303010742c0c0903a8000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 4301698 1250 4300448 4300459
    0x18150c0803010f170604050309091009020a08061003060e0105060a0c0c03050102070314041401050a021c020304090605030f0303040201080415020708070b060f03120c01060b0c031207020a110d0201050702 89
    0x8500d070f9409585a00a880710b60f61640e140c40d407243c0c5281e42c0d40204a800030510750003081003027858200080007681100e09103603820030b0b654840c803510041c1e0304040492000903031003004128503868041118000c05010b400d082200314140f2310415200c00050164902a4400148507032603e807044101d07a00254201c0301350042103459281c094041c2d84500c0040d40064826800b0071886034844003240c00b110401d881c0e03c07040e00001c0e00191425048456400d041d4040e010601c07a5800c074804049480c20403a038003540d0740d04d003080e8201c81115860740006010b948400207412000d00c0001c00c89412540900340f9221903a2240350000140700d0a13910003201c0c9001055240c1009110406015928032455a025050380c41c0410301ca11021240001d65050344100303001c803500c03104000100380a0342c4150012442c503490341d02000c0329034030204400c129607000250450321061460031031a0054058405009031504c2512040c000b00e84507032540e4070500c140340350102107a0140e402c551106034003401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 4302948 1250 4301698 4301701
    0xc0203070b030601080609010b07020f0d05010903020f061e0f13050a0503040306050a0b0f120102041505030103120302090d0303020a03020706110705060603010b01020d0305060f06120a0c18150c0803 87
    0x3070854240c00988003240803903c0da80114130149000d4000c14140e8140b030305070ba801d05109400304100030650041040e0800c032040c1040c1d01091082c02203c1c15180240c000346000c2c508100c07100c0c6080c00041050071074118402030030b01b0002007801c0007a001000c0074000802502d40190142d01c103071040200404911813a01500d04004001c03024004503800b5000801c06943c40340b01030700580310f13800343c801e9001c2114014800d0310324190180007182e6204800040c11715032640d0044170300182c02d00c3c042c400706101000400402c140759002841d0303003556140a43c1000e11100201e01c034882d20301d000030207040c1c02058050140f4465030603550200e810a9041c060b1510080003030b015540440e00680f0140102000100242014018105001010b9008000000c1c044408900030a4094070741580091140b0b5404031a85d1010040c140c18601c4107848006418655810b20807580032010540074042c000c520440c09200c0d003a0000300701c0d07568584003601921107030021102c140c0c4120004025540100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 4304198 1250 4302948 4302959
    0x15090606080f010801020f030a150305010203070c02031212010b07140d050403050d0215010603020702040902030607020609070905040308040201051803010906020a0e0307050604090c0504090504030c020103050105060306010c0803070c020307 105
    0x41118010354040c0b000351040e0340c03101a060b00382d00c00e01011244450080011a100d03000302d03482020314511205410301c85a880f517a440e42680c0c015503c0400003846010124103525043c8812008041c030314810a00e000420754000b00e0380d500510844501709000f213807038018810941c8040d441c1840c04815641d4680e07520b94003410702c0c0c015001c04d83d02c51240b088040151400000c0c41c03082c600b101800b60106a1030002c0441c0a544802c1080781c10540b1140c0c54030040c1c800b0010f83e0b01912940e0003038800ba20b000030310f83d80342050550007081e016040900b400040390300076407550340064081c60101d40d40e680c01c543c1b102ea100541d40149425601e480d00074000c1c80308a501901c2207902603505e040070301021004040d52582c4a000d16503004804200070411500c3d142d2290146140d941011402c0950341c449600880e4401c4400350089078202d45180308540c0c0c5403142c107025000442e100c0d402c5040c10f90008200c203681000080c283c80c0002302207800203000310300d40d5105903030003400c542406880d01c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 4305448 1250 4304198 4304207
    0x715021006030c031104090b0c0f0d05010e0a05100605070b060409051c030609140606070201030605090c03090c09150d0c12030207030c090b03030f1e07080909010503030a02070915090606 82
    0x5100580345d1040e200c0d00306482c4d15040c00f954002c243c0008440f50203450b03078030078480503600c50181200d40d40820008142040b1060081c02d001b00030101e100807240c0b07845d80052041d10001081c5c01d02070f11203a641800309542003019180b40a400c458000b180f82d03600c0b40410700524910501800d5441070103054108990704030044500702d00e2071382d0180704e400d5940d050141502d0565890003c080300040000e0700508107000039001c5980140340116125a41301d0115a20a40907034601c02c03501c40010800c020306108109600b80c0d60000d032500c407000d1901001c84405e0143c3c104026201c0d585040c0c11809000c408518000580005014041780183ca85400396403491240310171240b00c1611100007038a000c4074860b1105100c405005545040080520110560b10407205820005600d04040740d00c0a1030304041d0480718032941c2c0d00c59681440400304101e41d20305901c00351180e84104200240c803075021501d0021a00c035680f01140c084480c5901610003d0260814040c641c41e26500198003980f1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 4306698 1250 4305448 4305473
    0xf0705030d0e0606030c09040609080f031503030301031109040c081009020102060f010f0317040f180e01060317071a04060914030c060f061201060806060a05040905071502100603 78
    0x501e08100586180c240000c3e440708011211aa030513044003800030310a00784694101c0e8000c0c03044100040141d050ba580f24141d4114121020740000301200b0042c142000c1c482040842030200c2c0114110341c910755036103c42000c00a8103d01078090400458104045691084080c29802c016101c900102c013045a009109207482a80148281c10105524115195003903058520108807170880d1030071074950801441780215080b100400c108000100602050b4140d0003a0840ca58404805c49011805100340c580410340311030742d40d240c988104000b950f911030841c00c004d160b034a02e42c0c898110b400c045103000310721109010304503010010402009102d5001e103070380611404100103030008030340b9404d9681c0561a04202150301c10404141c0300d844403402543d00400042850902d8a0080c0c401030a481c100d0b4031030141a403242061104c01d1a165602c80c015160a80d800c118080158030350b695034410510903039440722030550b0b01c1c0d403541c2e100f88400e8030b03501a110f20a2008641d24607110416200 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 4307948 1250 4306698 4306717
    0x20a05060f0601090f0b0f0c03210a05070305070801140d0602030a020903070608010305030304080714030d0c0207050103020c070902070501090b040b07020106050103020a080a0b06040510080f010b0702010906030504080f070503 99
    0x5844e40442c18511500e400ca0036250b40d44100c900700781e136200a03601c5507071182c540c00230184824402c074002581741800294162613241001103042c180044950103480002d41003806160401c001c0024071030f805880309046524880801d80350040450210b00844070036070020784128000420032990844c66001068010019020ac4901c03980c2c0c1d802c2161050001e000081c102e420800118010420303000c0a08403090207070300ca40f410080c0603114689550700040c090041c444d101c00800c800181c040c040440180401c0c02e05528150000c2006920752051740244a9680e60104a00701800025440442e0bd6a88580700482070301f418101118490411100c40c0010342c203000c40400d440d40b20303000b580d16013065600e0f94503c4e51243d54400b030241ca85840f406400a20910000480340d490101c2c0703440c0b0701c042d52500b0000f07051030050756a040780142c000008003031080102d080182d0303100143c441219590328000450f9100e03490860b00780d00c10050042415540410904203000001c0001d140003030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 4309198 1250 4307948 4307957
    0x4081605010903051015050a03050a0501060e060303070f05010e060702030c061006050708030702010908180909060705040e07030b040603080901030f05010515070303111303140f030a030903020a05060f0601 90
    0x664030001118090b4050000522940040d011000744070f41ea5006a00b828015094034a005921500402d100701c07500e60080c2c95651001080a041c40400e2040c640a080c00c8140704000d0b14000c40405c2d0b8038451800c0083c4005200401403007840f6080d4070200810001006032102c904213007100940d25003100c7d14004040c040c4501007100c1d0320700012003100315003071502c9441c1000380c10b4403601d10981000700030600b0341d52a1b42c113900008100000030211314900700d9014000540480c18040c0446004080c07400560045062109558100007941c0494521030b4050750b00d42c1d128142100508100c0c2c4d5802d4002e81041d9021003042410406002c442d40280c1c0e00304a1200c01d842480141c0c2d10a1241c01d800c1641500b81c40b035600e10744401041041e02130304000c1514a02c51030f05401c40d80c40104800d0181d410208180100303c1c007001100c22008400000b0206202443da4103512031190500072414195603030214070404d0300034448008010b402900b83c480c6480d1140c0d000c204010216a105d0005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 4310448 1250 4309198 4309243
    0x10e12030f0a0612031101022208010c0504080c042408010501030312200901050f0c03030a0506010f0f0804020a080a1a13030903020405060a050907020109050606040b030a020f060c030408 82
    0xc05846614219071840d41d00744c003010301e02d4a003501c41001c80e60352050555000c0010036048079020f0303070b0500d80302c0310a0003100d00c4525000d201030849498944800420104200401c48003a0000d9411068001180c00180341500e085a50b03002203551021415030001000d0002050007040d0702003412240640c5445001a5a000c40c0c1011144441b440003030f00304180280d0004510710a01604582c141070500603c0e00381e070005041040d400110305a04254000401c00c006a5218003400703400100a0034403903900744507080050201103a94040c3d10400c880720000400350742d22600008010141e501c01d03107038a11000d050584032600b4504034611991107040c0410744101002181c0c1d40b010350180d41381407600c0e0031682000302406002c1e24640c0d01c803a01400c007203526942c044c4402d00998060700002011031251a06e24200600200160700c158039040004900d9100419072658455044035410082c40c0203000041d01805000d911140512000c603011514030381c001a601e4011001100840c0407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 4311698 1250 4310448 4310461
    0x70e0c0304150c0203120a020f040306020403021507031b0201020c0402030c030403030501080d050d05090a050f0303040303200306040203060d080a0f170c040e040f0503030a09020405060409020a120203010e12030f 93
    0x207641240f070010300103900820002030f981c8114401c21f5004400e003c0301620b0140e400884030002d0700907800644003590300050400031898120311825040c00520b03840c50a00003942c5029001481620815080400507450581160310a202580782c4d00070040c0219141e04080403450801e42080f9800c0f00442d24000c00030800e1000001d041000c001e5960790a450405c00c645c608024200c0609110701074491201c000700018014800d0020b0860300d00021500d0f481c1904009041e80d0000d00400032030f0080c42807501024004908036036201c0c605a401603034079150903000c20050f4181e81c2c0042e2044501082d00143e590b840040d00e01403900559624100030045803018020110a075822031b000d074400c2000700b20500b01023407030070b03840342c0580c0f06217624186944800342540c3c021104031960541c2d44501c0400c5182038410140c2041003070341c0400c0b0791000c0342e0107d8026000c900030340c0c640860003032210007155001d4108002104510080c0c0f9081e06024458400b140c00c10f075003000907090420005141c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 4312948 1250 4311698 4311701
    0x4031d040b100e030703080706020a0215010302010c0201031107061e060501030209090103020405040807080705060a050702010b09040206031003150203070206090303040c030b1003050d0906110a03050318070e0c030415 95
    0x84950010103441c462060000e00f9101d040c443d110310b54050007242c0001000c5031000019021030340c09241c01580d6512000c1000b81010316140d036001146075100014000f46c5d81c00390a6034007081c3c1c2800c00240c02c0240300002079090189007030080c041428000680c2281d8841d0441d460f941d508580d0a00400352500015010790142c00d046039006290706004101500d4290015a00305002e010f089280c10629101e204880d88410300c207a40540c489c2c410300070b041040780301d12603111b0344138402006465200000105104809000640300c3c8001002245070581c51071542001198003005202980002040c0d4601039002242e50302e002d8001d2000103080340d10040b0480f0308c40d580c0300444407a47e03400c6a03580b101110000e0001e2800d010000c1011001843c1085600811081c1d52903040442c0d141420041c04c1c01402c0810b45429000b0410701c200081d0003105aa4010b80c1d2408118980310030106228600342090344103400d4260785805000110241000840c012402446991084490296180d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 4314198 1250 4312948 4312961
    0x20c0a0303140c0f0306191e080706090803190302090409060501030606060503041a090a020603010806060906040614040b030109060213060e0301140103020105030403020a0209100e090606010801050607061404031d04 94
    0x302c1160802c006205451f00001004804801c6091682003a4a42c00407282d11211031709100300c3d40f01c5040301404401801c000c4000284080d1500e02c0403981800685a180c5c019042d41c081c90f020f00e4091503840d107000c0d0301699511407024004000d5149c1c1e038100500940f40a00c015600c440c9490008078140d4032130001c6a2185030008940401c0340c00800b9a140024401041030360700e03008400383c42005036204002903008000042c002c0259061510800c04a24070240c4490f01c41d6103051420054215074062410051700115030008404024002003400b4001d0440020200707032001030407030b5081a503910884c041d0f40807551345415004c1c2e00710030300d030880d803504c01c03217860740740040c0b004000540c800c2c001190302500c24819145045a540c0c04181807800594020030740c00010325040c800310341e800002d15840000c040c01408503041000001e0b00ba0351040c06028040e6200064040034003101e0380294403000c032410303400c03162072400f400e0040c5291901c03013100300c0103000518519043d01d05030041743c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 4315448 1250 4314198 4314217
    0xf071802040305070e07050405040617010b01110c10020c04050906070f0201020906071e02030f0106060f09030f0b061809010603060e1c030b040b0a1508090708060415020c0a0303140c 80
    0x201026405c12032050604c0800078200d20801030204004560754a89014400060002c1f104503c0c811414000c0c403400d485600303081c10304001c505454180c3c0c03c48001800280740700242c9100b40b00003030100b802c07810b200c245804503820904000070b01c85c2d01100020618030613806035031405004001403030102c0c240d108020740c4650014040c090f0130003007440440020703040980703245101070000055020a05144113103054840c10396440070200241d98100807484402c542d1450f050000328116580e01c01000e40b02d00c0301a028004200014520380c0340c03800d142c200c07403180010890b11440d0154280e4040c104a000440309030f0b003400d00f0021040e0001490b03090350101007140410f180d4035000110300030715200c3d48455116450f041030500c0c6171610f815801c06040f551074209555128a540600b621801403e901d01031b1b170010390200f0001c030001c6481d507005039000c2c0707070310061869038031542010740500224400103000d481807180406405a100034801d090560002c0426640d030700c540c40146c02485240e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 4316554 1106 4315448 4315453
    0x4021b0a0201030b0a080304030b090a08040e060f010305091506040609020d060306060b120a020c030702040519050108010203090d0507020a0b0403030804050733030605030f071802040305 82
    0x1a000031120035201401782500c2c0611140d40c902c88c9100c0070380002514004111448801d010780c03040190040c10542d141c0f600c4030001d1050b0001622040d2141c0044884840b80754000d0003042d118128150141c800e10300b40d400d05550340c2034000d00d040e0744160303144808100008944045c250158801c0b000051540c11072908208840f490780001c8034144050001c0381042d48510350300740d8040111940542c5a2010280c06850743c003600d08000e500605202c10030645441e0601a07d007070340c600b40c80900c800c2e42d07140f070498200d110035141550107400503245034900d00c0c014030051007102c4c4051f0840400c50303a240d018040f260084e402c101c0c000742461081c08140030080244402404400c0e00f00c00c2e03040f800c4848090010041c040701d21148090480d60102580a0f034801300003801c0240c00c0c4c410914501c1852520303000745000c0c42e60880701002c141c2040d42940d01c02c3d202641e520200 = true := by decide +kernel

theorem cover : BRFrame.Cov 4136698 4316554 := by
  have h0 := BRFrame.cov_init 4136698
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 4136698 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 4136698 ≤ n) (h2 : n < 4316554) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
