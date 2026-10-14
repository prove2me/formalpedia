-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2971
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:16:57.589996+00:00
-- url     : https://prove2.me/submissions/b5dff9ae-728f-4117-bc48-0b0ee5f5e278

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 534172661 ≤ n < 534352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 534173911 1250 534172661 534172673
    0x2a090e061c03210608060a06260a0f0b18010b030709110904061502011a031c0210020a120b01020d08060906010c1b081501121113020711010f0c03020a11010c 69
    0xd01d441c83d090078041049401e00513064580f08006058982607414100c007000030a411201c0d840341d803014611452034115507140c02d903107000d0f105040201208085075448042c803031114583c502848444400400c01022540164203941903802640c0c2e264000400400c00083c1507848a880c0c40714041d032060030242d01a0004045031042c1e80302e08c904d152103501c255415a0b0a201d104840c18090422100221062011030741e60099a96291031144041c2001c1815a0007040761108110f80398a082d50b4a0580000c010703d03d80034861891005070410030248055800491042c40e0300026940304a17541d42e0301000c102414030064012814822000d00f00b42c00f2566440c0700701404044a103000044502e04010a0300c0c015000301040018403e078001488045038042a007407400340c102469402554582c0300003501207805030142441c45100080d510700b003107040010b80940e103100741ca82002c2d0000c001c50584117110240002001030f0003041d070a00000320451407202882c40706142c1884503140a582d44 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 534175161 1250 534173911 534173957
    0xd02041e0e0d02030a091a0c07150207061403190b030d0c050705030f100504060b090a1a0102030a0c06020f0705190b0106170a0509012a090e061c03 65
    0x100300c0c4540c0758990000200001c00182c094296648003c524120000c080140f44000c14025250000107900e1080e46802e0400183c403290640030307050741c130405c3d9a4400d180c161190941c96501500076854001000d03030048400d162600d4000101518598800c1c03442c3c0c104165034941d490300b40f55a80e01590483c0c80030090558444003070f4503030140b10242d500f4141c0c0390404541c045482644004a00031b00b0701804038154031100f40955010603079480f107180600240c14403811080d040380c840810402c103a42c45400210310000e0280300f10110a030396000490722880380c0c228410108004000c403000203100d5078024001d0744010882035003894220303643c050070000c0600818184407a03500d01d0509000060000740d004050a0800c41e5003482d0707003030403580c001c01d0003004002840c0c3d03100009030701c0c64001e400140c0158508544108880d0015254805282c600103009000500419011940c00300064030103000d104010f00591070140950301d200d4850b142928101c1c200319082102507040e010705e02c04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 534176411 1250 534175161 534175211
    0xd0309092301080a23190f06051f0b0708040e0f010e090102120402060a20010e0f0a0f0227040f121805040513020a03050c01020d1d0d0204 61
    0x508259440c503021450030901070f00044959000810000d002a04d000d525200c0c21200000d40341c0e444001003a058100304101c0c040d10002140e064504d070800a0000c3c42c1c1c0e102c0e0b8891181082251a865040d00c401d070b0110214a4018042e000188441c40405014081c240c0c03003038002516050300d134504107002400075921410344081c1c0000500041d94144036071540808102d0007141064402c1013180c2200d5006031002e8024140000c440c0310041c403074106517102c2d2040404610752000114152030080441c0c80303201c203080c005d002c410300d40713403002050040d0000d0708801d555103804030700e4080194a40400088407c816170022005502079000244640300728010342c40080d50314064180b04900f41a03910900781041030000344440314095056188064a1040d0390000d0386170b4030108050440000c404000c0e41c4905c1210300001004000903040403c2442a0700b42c03290700592030420b43e0784a15041b5009003140c2c0201c40f243c050b0820207091960b00d80001c1012401c01e444003000160a502048 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 534177661 1250 534176411 534176441
    0x90321091a060406080f030901030510030b15012a06050a060f060207061704020d0b0601050c1009020a0b03011d0603010b060f0306191406090303120115081f050d030909 74
    0x10030003145000e01c138a900a00c1864080c1c141070760002c4006841e0700c21501d10740c1c1450b079140e010404580741110034002550744801c00c4801800d100b44200c640010f24201c150002d015101c1494822401000c8076004010030511542d140116a0300d80005e0f08005014103001030340d4040c0041d104103131300b0098000f041d440e0041c006550a015000340b1001d4a2400c500030700b4400418000141c595941081c500c40e00001400b1081d01c54078012100c6100301c1c030f40000780e48500100c2c51160091a071107540d00510840380322544641c1c401d0440c40301e00003407042642c61003c416100020702002e1140c10760288004000058542c0d1502c001141c40d00180b514031012400803080050078102080100784401c80c030298220080d250441e01110f02c0d040c40f00e654000d200c0801d12040e503072420070a070b5060080016031004a581c4824081008a07214104207000901142c041103225108005600240000f403a000e581c990030301c0d041c000d011410300307001c40400c000c40340c0c000f1300c800e0140304074202c01400036 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 534178911 1250 534177661 534177713
    0x501020705060f2a090d1110170a050112021c02063103020f0d03090b04030f02010f0e092e08011e0b06220b0a03020301060f020109032109 61
    0xd8075000101442c44c001240f42800152014403040b40c2e002651400c0b1000c0fa6519140c8806190802c44590680c46154012880151201400350080d1207943e135050485c40e0682280e030360600002c103440d420320170103540d0321440c008580503050902c0310206403049a102c0c0c01d00c03c800c9902142040c2d00482040c0e00c0800320480320310080041024484840da029864a520f19055800091407090680f00451080c5264000c880c1090b005032424001482182d004a03100daa483c1030012410300d605404074001006600440122401521580f41d01940a04000314503542c640070b80010903d603426001a0344a40000038104010038441c800207040d0342e50002ca404509503c9031001072405200c1e0741406810045054032070f0710b55105039100c081014154000c4020704440d0742000000540211203d040d0002e10401c2c80c54254000f10b040700c83c3d640e43c1440311548280c0480c225460201c00a0024148400700070103840c610302d211802c0140080005007000095540b0301000c0c51007075502c81c41805403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 534180161 1250 534178911 534178921
    0x5240d0504020a05030a02090a1a060705010204140603040816020112052a0c0a061a060d020c06010f03231e070f0f0602060a020a09090c0815060406050d090501020705060f 75
    0x1a28880101300a40c01020f04000707075030000321000b0005290030051a80d46160500c140b03810103800702e00714000b910341a40c401c40360a1a038040d511134000e4609104090500e0512410f0420440741318940110120341045011803030840c0b15480000140d040020104940303a4140360b501ca028060407124610907454840d09042019841c00618054542041801b050300b0303000c00412120034060780104001050b0031701d841000707888880440b0b5075800c6907020a07004803180076a4000c0607058010011201140e0361f90b502c05070486803902000340794400c9503c0c00d0412120b02c032490b15000c984c000c141c64085048071039560051482d484c0022040d0b20404082001908880b0a0000380c05114502c1841505154006c1e540d1f810240c05400307400e50029035030b06020f00c240d00090261940131018448a045e901d0020542d40050b529070a80f109038442021392407510303204640480315262034a90402d440081d04c000280003861041d21155020020100011010312445200fa10314001003401c90910b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 534181411 1250 534180161 534180169
    0xd0e0102122106062b060308031009200a030c02150903090a05030c1f0c080a080906160219020a030503040b0309160609170102130b0301171605240d050402 68
    0x101400c0c0303501800d4200040e206005c2d0959641d29401c0c04101c00056822009403014000c1000384c0c0003405c407420120902c5a00f180510201040310340c4402d040c85099a1100d090103840d15242400302c3c03606040028400e0715001b9001401e5400c4d01e801680c01c420703041050002c113100c003203d00440365000041c6207100c900d440c044400c060030040d0010501c0000c1a40840ca40360200f0303c1c2040d004202803203000a586c4200e011020742c982c00920b554445024460180c001c04084c0c400d00d03094041d4000103400c1d0381e8800b50000032000c50350700520754001561030004145807a11001d90b0014088a000b01c0441c03810070090005104490500e5600d2a111160fa4146400d2024260314001b50309002c0103815882041e050586001c00c4103039801500b1440d0301070080c824021922030f24440b2280016001c0000c070007641c1240d0060b01204100030103140340580f5112400410035500c105154140700c14200120380424141e5490541c0781321400f401e0108071960020900c0582c410b490300200011420 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 534182661 1250 534181411 534181477
    0x100b1305040b04020d020d05010e01061719080d0603050a050309040b060f04090c05070b10060905030f120f090604030f030315060215060102010204050a0b030402040c0503090d0e010212 81
    0x2544801008541050707500c4400840d000f03030010744245812245d80301903640d00302e034032490b050b400030081042c24030301100940a0300c06071141060980300c071050301d50f41c05070205014000c1c801000c40c10130302070302c0c0350349101d8242c12440d42458650707961000440041c4007041440301c1b00703000750f0007035031948039050800c420f480b0104012406260705004540110340f02c01e0503141aa40c80140224400241581c00c951a000d907003006415520308505205240003003203152420341e01c00360340b0071610503120020316923201c0390586074100ba44d010690b0000e00a20202c0681003003260043d07450310300b803070600000c2d0061300960411f071100c00d541465481010742601ca03031000c6068075218039205618050010303441e1603c400a0503640001000001d900340c2c404c0d1304aa000d040300a00d0100c0ca90b441d203000c0400c03904101d0301240684d04d000c414810313407402403060720700c00c0c00b82000902d089462001c0407190010546012070642c072800c01410b201c800d0140203090820009036913011070504484401d50155 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 534183911 1250 534182661 534182689
    0x8060603070501350a020a0206090c0109030b060d020a080f28020907110717011a03190614010b0a030b0f0105030a1e051510030c020601060809030c100b 67
    0x240c0300d1001044681d801003000d8180f443c0d084800540701500540000f1801040321004404081001c100541e108555007d80303203500c0150308071240c565902c1d013542d660380f103824040c601140840004000182d0300d601c0b8258070441c050000c031078000301c0b5400700e4200885a0404e0b03113160030008644000810400403403402160a64424600712200c0803403810068203094007030300560580b4006480a070198110412041c401c40440b600550750341c0c02d4208a000740803a03900d295007090380c01d00a40a0221602c0749100004020742100c0c1a50306608801880c007400031151030703440d41140201d1045d0305280324000c01d60000c2240d501c4545100080443da00c51b02264441e45080c01801840d036800425240d02202c2c1090015003201c40444042c9008002e80d03041611505060030890107404104d00c0554294082c0c95001400ba03407190305909640813007014a006030322000040225a108191194202c3e8107041681c0c903000303007204400e08045508925490550f1a001d1021040c2000d0000b0300c040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 534185161 1250 534183911 534183913
    0x2071a01030803071103070218090d050f040510170f040b1f05060a030e0303090a0c0b0c190204020712020c03060a0209030a1103030c1006150807050a03091b030c08060603 75
    0x150304665450809010240100007001901708000382d20309401c0084071302c0f20760014640f0040034141d421a200c200c1c0200c0300480913000722000b8400d150f000f10140c84018503072820080c00c0504000501030a0000d1825900c1000003910314800d009041c0c0071103030f0040c03142106034011854282001401418003800b03500c03501d180301c140c21040103062040e0b101503030f0007200c849540d0250311004402920100c0c0b0595200d010000038002c1c403040c001a070340c44480c4124181142240e4448440d03401d80500300030700c01135800110742c03150041c402c48040d8001c82e03c002c0c001414420103440700d0502e0f00128010300c000d03a11603510700042d80760410045511902c000000c0d480d051494010a8944075158401080c0b4036a2803010005640c2c2841624807e0303513100c0481e00840341800c00d00c006002148640d0801a05070007140d4241813050312401e205403142d0720344514041031098102c0050280d03480559610112030ba217442e9023007980c1c40d8040103600800c452070009080c4100f10f800c100b0003410f142d00c6 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 534186411 1250 534185161 534185213
    0x102131a071403091909050a0209031b01053919021c060c0203031504021e031009020d02071505010602120a11030304031d0904110f0301021c0207 64
    0x11030040c45049800c00c5520020030b410311514015010716601801e110b05134000c140348250340988540300b00020459440c50014040c54841d0701083c0704900c5a5480d00f50140c106444580c039400300f2140d01c40e1f480d0810b141480c50440301200114800d600c9100b2031442c1614030000030384c0412004900101c02121501070f00802000d0319074140407048050000b40034200e041003400042c05c202c1d04040742c054000c1c10503c5000070b031000c006d49070b034402c0b5060111003c01d00307142003041c03c0500c00d0b01c0c603400c0075141c0043c1c000b04081a0580f41d400003041e850b00720b560010040342c0b40c0c01500107071900910840000d070301d69450f0b150985620b1880202004158a0000108030895000a500006500140707445559200c106c104407540c00700c0000c004a2803200106000030598411035403a114100694002d070000040020408842002e40b4050481241c5502c540030f5032805120b2602d210000a000502c1e000d8004404000703601407146107106d56a020401d40180306140416428100000710481a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 534187661 1250 534186411 534186449
    0x10e0303180f0a1715011406070206090301110319140606280203030403142d0405043e25020613030606080a0302030714011d010213 58
    0x5528007a000c808950418840d840c1071a0391244106108801400340202040946489840020740d0301c0000d044580d22650024041c0c1141141d901c03410780301c144001d480c200c00100100301d03064100c00d8041c0d81c80f403800c03c1000c005039400d20840c2d0002c0050751400d5103034601400150b407420072480c100f21a00d420710141441c680c2d450b4407045d922940071505203468482c3e4000300c6150000c2c0705c0110815881c60b9560074070f4190000b014603c182c0c42662804449112200c3c1c080d428060303034401216a0180d910811719800310044044040c00050018904181d55900080c094524080341c40b07841c1c022192900c40300008001c0004201065103e65040070811001640c880e807040c000e400600708004001e00081145550311843e0481d00184000d4845004d0003121490718801d100031540303285050781c001240480450880c000d2a0503401039410002c00762954000744e174403012116a20b541e100c03903105444285403504c03807060041b14001a111000100c0151031045581c00c000201c400740d1000e01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 534188911 1250 534187661 534187663
    0xc1214070f05012a15140c07030c030c032708010f0b03100509031b06070207140a03030c050c1c03080c1321080d0905060c0c03032403120a02010b010e03 67
    0xc0b00c0c00c0560360800c1a41380342d080060000d03280c5500400400100346162105a03903a040100c846460302158001503e4a400c1880144a40c0c2c41c0200481d0741201181d010a0207080311007401e078000e041c4800c2d070850601503295031034849085240700003403a0340c060011140c00d220744000c51001110400c0400704000000703a07505030181c8050b0030107440c1e0300002c07150101071041d0385085240300c48050f07016110383c1e0929200d0104a58440c01403003038010000c5c0000401ca1031a40103400030f0072041d803842c1161400c0b502035084d00d0003030382c06115826405186448124401514000707401080f42180c0203450300400203100074101c103103140310610244000040c2460144102d81e1944a820484684407184101881200001034800c082c081960f050383c40240d004152098491001d445043d0342c4c120a22049000e034840145295106000044080c1a40303241c05950041f403546000c0c40361010782c002450502c10600100340941c01141c1d10a01d2602405890142400ad00b8040c01c0382603038038040703 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 534190161 1250 534188911 534188927
    0xa0611060903040f05061605010f0915050c09040e160605030912030f1311030607030b180103050d11070f0303020d08070804030c021917031e12060d0c1214070f0501 72
    0x100d8801d00d00001d800d40035513040c41d0f0011f0226802002409048208100c00e0010075044034151460442140180c55007156407103040d100e14940807040b814844000180001801690406581803260310408003122240310000001403c40380d640c0c41c0d503803a01407c1c1c1c505084128001c441c60074020f005105da07180d91507104a034800c4021450780741514460801c260600002c02007076406000e00f400384804c256040c5c010707030b0410704250346842e0b00b4200302e030900d01050000d22001d401c81d0031038404048243d1045050340e20001c01b0008070b991040c0c4907541d0f182d8002095200b2805030303214001d00f06410f03400c09038a660200086c10250920328050314090210500300070000e10426400c10005285448400c3c1c07880075090034218a95005004054140c0e03c0e031250303c405026040e40c10140403d51020800c6400c2c01c020f1100741c01107620b400c41448480010010101e0f4410302c01c0c0030209000800309160141c0c0c60103001d031526601040c550711414250607800c040c1060f1560301c4c0070701c000c1e40c00a0310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 534191411 1250 534190161 534190169
    0x64e0c030b070f17130f15060510020304030812060612010603090c060c0209040b0702011b020c03100207080d0e0a060e16080313030308180a030804030e0109030c03030c110a0611060903040f 83
    0xa40c0c0e174050041c81c24107514500030348010803403c00c5061003145003880b98040c5054610640340d200c242591060305030b80c1d88c041c1d0320004124100801c005002c0071186d0500d0ba03002034000c1c00203401c01c40c829007000000a0242c205400081e036941507135007404400100c020042c4654142200c1c00c240721b0300814220031f0001e0014180c82d450602007036059100f5805010041c0d4110b818036072a00c2800e82c000d440d44540d070350781c910a12400c42d9901c6d070100ca5200702e842a41e40205600e10b024510225080030384542604030010340034040035180820000d0195400415041e0003800c01440c0c603e00d000c00c044000d8201c1081d6500074098a1380c56002016110242e039090300f0a22150f5072011500c00281e0403c4954880500407050300608048c1c02c07030b0031240110f00c00d48134040703c07000364030045502e01d24500c40075140d0310b21800c007080840d00400408a1881c002d20284640101c044049000041c441c0c0c003502c0062028681d0201608007880310a4202006001440c5420314180240c0da00000b1130103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 534192661 1250 534191411 534191431
    0x50613050910080601080309120d0203070f032102032211040b031c030c080c03060307091e0e030309010f1a01030b011101090501064e0c030b070f17 65
    0xc0407840c03031500845418018807010f02102d03813640e12019055280c0e04080da0540c0100c1c009102d030341c1ca0342d03008102c00400c10081d6009600f80125078650700780f404035206041d028031811841024981c50909000c05070940e10780405a42ca05103400c800740718002074104c41e4080e0455213400703000074a001c0c417030000d020411074010550009c140002410480c900203d040c14016401c6c0d00d107001c5400d908403e6998a00303446040942e9181d501c0582580301c1201d1080d030503003016806000424066100413558404c1d5040b2103009129001e00c1e800700c80104e081c0800c16070022040042c00d103803d00405070b0380c1050f080f06019090001540014100d1240c140300d05042c1c68080d04109644200004003402039040c0082c4160740440c20900e0003030038140a00b8000e03004801d10081c7c000c080c03420a0344021418100f9418010510241c1c0711120240c0105551554440201d48081660f80882c071001d5030240030030710b4407410b20310740203410842005090000d021100c2c0c50a4142d800300548194042c104074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 534193911 1250 534192661 534192679
    0xf0601080603240a0506030a241b1107050102010605010504031103030f0714011407080a050c09030f0f0d1704030804110604121104051902090a0305030703020a030905061305 76
    0xd00000c0c20b0401c10011944110b507039030f01004010142e41e4005000701062282080141c07225002e05807105044000644188280c0c0c80625148000b0340052100c2409603c0000b5070080280720207240c402c6d007080c507000040940c203520300030020900000004010900080219a150100180c071030301441c071002c0e100b02c048140c0300107907450500c00c5805150003220a240d5401d02482c00412985102030303001c074190310300b030804986003014001007402080c2c95210b180c0c065a0f80380c441005440010045107007076505001c68525500c0400054407641e0b01c51016004034841103c4140c600f5003024800c1e8100700c1c0d41c1c501c200c11410b128040f16041500351404e122640c0e21814024507000104040342c3d04003000140008041e044100d110b0b6506100b81426400e0782d402204000a8035403c6d200c081d03c0184030101403410b0206503004042480700504141c52055a98032101d04540040c0f0065015030400c540c80f03010945c1c002d00c104041d0004031402401c010380031079030340d10120b5107000e0280241d01c40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 534195161 1250 534193911 534193921
    0x15030f02040501062f0f0703031101050c0304151808030c0a11010c05071b0b070809100f0806220204060f18030c060f03020702030d0f030b090115051c181103060f060108 74
    0x40c40f1481002800c0802c81f03202940d03902d8001c01190f5440c0032210a0351030800880c101c00c0950703044900446e048801c0080450411010740c0c002d00502009071801030340f60520740001060000918403d41507a4582c50303c40d401e80c44040d140c1c81d90001c0001690b450840c4c04401d198100301a40c0919070031031040b054050324510010380382e0840390170600c440c8001043d220104001c03000105400c100c2541c401d8152422502c3c00c4e00c1000c155070181d0041001c1c04002a154148882103410325200000040d0b546449988801d040740e11540100700094444500b9160283e081440c0b207818030b402c0c66407139510074907544581303403c110f850240d0004c10000d00500e0b0080b503c00d40540301700d90380080c1959844410401c0c060100041c221800307001c213040c0030f4500316a00d0b00c820014100c0b03603152003400007008681400c030b40319404000540070300f00350320440d410095441d104203071082564003800c4803948001d09044a0094907075a00c3c500c01e500500070803c04d20b401d409040c0d0060360a0070a98915151 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 534196411 1250 534195161 534195163
    0x60408031906091e0207020a1e0302190510092d1701051b09090109020d021c05040302100c02031804110c1005010e010302030601150315030f02040501062f 68
    0x122500003440e071401c0000114214960b50f0140b0703040205200f038060301c050400042c1050340140c3c040a503014001140c00c00c44001c00c0c41203c64500c540210888655840f80c0c005075031040c503019140d01c01c00c50307000144454202500b80d95040c003000d0030b0902c9014545030340e083c448080392440728010b00d0f0050030700700340d03104001628024010a1b03850b104480b42d52000e2500130030b0202c46000645040d404800030501003801103e00b0044040d021000507070a2140403006980311007000040c403135080205460400314000490002043c5403004a003a080a0800a1520a002100c2c100346480c0a2210a00036000003c944408416540801c00c2103001c0300004e00500021103490741a450000d08080030780404900e501403903480110801141e41c031640307001d50042090000a40550107080140840e01030b00841c03403a0f401003841c01240548921049605400340d592044601c035003d240c9020462500d030080501602e4580341040c42e1452400700c0c031a103184800902000102441c0e044840301c0c0c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 534197661 1250 534196411 534196441
    0x3070c0f15020c01050a0e07060320271503070305070908070602011d0d0801030b0a1b050910031a0d050f011401062c09130c08030d0b011106040803 65
    0x500001005044411801070202035400300e0030304140e83d46001c00040c2c00100341d100305454a245000140354003030030244186c00a1040f601008074941c040406408400c0c00c82c0018645030107e004080000d0611180403000f82c000003206600c00d02c7c0b00f4548822000089082d079a00000a03d40494030780c9442e0019207a401940c5c00501050140810200b18950150440310b004250404160303003102801242c0ea80320680685038000040300e4800420104500c2c10134740b03400841c1d21400003003042c80004001c10086400d001103001c50000308400c80c961409d045900300c40500e9003824014013484a0101c24a030a000d440b1a214038038100b841c405100d01001100722048a9a0080066030303202e0403c04002c0c4800d119050001d48050144100d0080d14030081d016411250a9504103501340404c11010748801421814601c51070240e10b008103409019040003058840c001d540d903040d00c201c1e104165210310082d58140320140350500c0c1c0d0044005042d551164019025985907225041112541c0d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 534198911 1250 534197661 534197663
    0x818040b040903020f1612110a0b070507050406050409150c050d021612110309060d110304030306031e05070918200405010906050d1104060b04030602040302030c0405040803070c0f 79
    0x62400002c0820150000f440010203202142104d440180741140307841003050a0050019200c2d5001e11080041c1c0d8085201d028003034010a0f107101907071115900e07802d5800401d42a552940144410422400c1c07901c100800f40c80165000d00183c60039441d60f071002c40700e03100310540c460760700c05040da40c4610404c1078518040704000255641c031514281285a81122901581d06021040c410700807140129492101030038801d0141d800d001c81319003001841e4004141c2d840c441a11940c21803d020000e00c002e601c501d101e078a00040a034110300f0000c0c10700b0607a0000342100c0ca041181003001c00c00c00a9030b001107030305905000c600e440075440e001582c01c030ba80c80001c0c121401d0000180f800001d021102c03540c120151070410540ea40c07102c00c0c1c0c040d10360504c942500980f1400ae500d01142194010341c031780b98809080450100d0382d5400d488001d901560007641d101e5808a018011440d041c4002103a084040300c052085040c1a203c049132440080c01035000e01000b018241c1c10448142d28410303000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 534200161 1250 534198911 534198919
    0x1020c09060a0f09091101170a0b060f030c1b0d09051e040603031709190807031710060908030406050a120f182a120602090310021201120818040b 64
    0x11a40e100c107104094202c0305030841e1040c40c61505808154407807032100e169003058016034411521a001909e0042c1001c641c19504104204545c551980c4400c0c0158080c40708000d541c4da03901e05154072121450b0800605040c15003000c050710892503803010201080c1c5030121800e00880003240100c81421231182d401640081c100300001085c181c01c07100c1c440302402924400446507444011940d101d000010214051690640c400c00109500300c0241c42c5aa2103030901070700850002d02c40545650044480c042041072070b079424411a64001c2030310006040740b000450500e410302101400b1401001454810020820b01d2460120043d812614a108070007500308101241450b001084002c0604140c4030310100f51180c00310405481300c040144001c01107920155400c00a5220f0010356803501914059020711140d441070317500b80b000c1114854000d00040e0b640a80040308050400142d2000004182c4425540e021501c450200e4000b400640500340740030781301d00009402001d55806450300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 534201411 1250 534200161 534200189
    0x9021812010516110d0c081c0501060e0102060118050402060403060203010603092f1003060914010302031e060a0c05040801140a06050a05010512070309080d23040201020c09060a 78
    0x39094041d40050300498441c0c4655038950300071041611100c0e000d41c020b41c0590b11881d002c0681e10311401c0306000ba80d200c0c1c610185498494200f801c001d000c00000c00d2080340e601ca00410031f480c0c000503862070a06007030002d40780744d44c503007a0160300d5031002e054100303040d0361030b0b400003011540c0c0c0d0800c0382c0c05550300c20421522540c40d00d40080041c41801070807940607065021a030340d500b0305c110781b4a110710b10b003070420f10784d05c0d00540c00e126840c540b225401c1c06068039260007241c0b00c1c0c90340c0940301c6c0c0b405840c1141c5405600d140101842d109408901c2d02e0b0301d0300c150b000c0b80c512480104205602005a880215402c4484501201d0601c076a90051032954602041003c98000006006010f905200424030615444908001e80310342076100c1c46010440810020040042e0092140d074440100d0400148120040e01d0b040d84541c04400080011030303640203c00c0d4000c20400caa110800c091590b105081e28042c0d0001c1d58844200c40414891180c901c0020b200703540d680c49100140101145a180b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 534202661 1250 534201411 534201439
    0x40e0a080c15010909050303040204111c0b1005040503300d090201140c1b030a05031c050a050c0703051c020c01020c12130509070e090411041401030309090218 70
    0x144030040c0a10b40340e0b01c541104000a205003460140b02c00c81c1d90000c01861540e210369082000a19042075078003c46038050160b5507442050400001c2145106107004c603155a8100800403c960303020503220600034103100c28400794600055221218103085600c880c100d433220251040c421103c0d21102820318006041031000119030008050103100388c035600d0205a1000d0326451364003901024880c0c5030b001c0043e05400c140c0c0c0c0761044507200e0380a0300780c900220f540d468003801d40d404414680c40800034610400308031151445074590140c0000703000c0001d03003800311460000e40700310240902009408500c03810803900b540b5040c000f85240310300442d520211204505c3c043d410454564007503015000605524003210801c54904540f400070420000b420300003000740f6100c02038500130822003869001082c41d00c4426403180030340e001e01c0410b6210030701c800800003500c9100110710300c41100d0341c00400c00290000c10712000d482c5c2c50381c0007580340c102c03040001b5600030001ca03034140d011403082c40c681 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 534203911 1250 534202661 534202663
    0x90a030c060206090105160f1202030106031e09030206152e1805060901111203040b041509050d08060315010e2e090c030207151d120306040e0a080c 65
    0x2800c48410b9000c1d240d81d95102d24400d0300303c0d035003101c8a603007001c028025076a030715118482540030a45a4144810b500d06604615012600f00341c00c0080425520070b01e24001604100c1c0000c0345106c0d000302401808a503a80082d11414040e049140311401c4c128503981960314291401a00d00d968054188159000c0c2000d030450f029000c0c100001c0317010700010383d4090020805040c2a0341d8043c052034504801c450046508003086405501c4600401644141e41038110f0002c60140b0f00560701128282014106216403000d140000c980c0d15142c508a0710000e60080b54440394204103081c0003069070b903443e0119007054070000d0044092543e1100201d90b0380f9140010b035005504400022001c10b0603c000b0b010407a00381c40c030003407422030011010860310358940c000c400808890714000d42008041e58038000c00030340346188102c4094a90760303002c0390071016507400c01d0001030000050a4a0740402c0c040d00c15444080c11300c41c00784d501c0d0f503c0f0300030200c02080300d15840c50b48802c62541c0c90510138902 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 534205161 1250 534203911 534203933
    0xa03020709050c2a070323010605010f0804060b0307090e0307110405091002070c0b03090a032c060d24140a06140c0a0512120f09060f0c090a03 63
    0x700d030720318000100e0780201c00300e010b592a8000c0d405001c503200b0050a510b40d84598440f254081c588110b40700400010916203514004401c840200001112503103d001d00b0740340560010781c1001141c1d052080000c0c1c0c0014000d801c80d0f005500020111481c00220b8202819604003031003440c2000120300c0c400c070000009105141c06a4001c001001040b0204800d41d001a148442e19900c07010f001c0c04180910360007849410b00c5126107100d42561035428924507042141c620180342c10104e44001031540060032104100c0f6940c00030b022401040010342c0c400e00119a071240a840042039007409461280c2c4041c41c0c2c20030940e0900c0440a401142c060303011101d004031314551040340038141103400c2050414040d550b0640360080b14810087c90b0111035084415400e80307602c10b035002e800102e2014031403a0726044034241c0e4a0354842124114030901030003c0c0c81c0c10300c401d5043c01048401400411600d1704245e841580d84481d89030308841c401c8a01410500a5002c80740741000020850001c1e12 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 534206411 1250 534205161 534205169
    0x120e100204080a031d100f0509090c030702060a0b090c07050f0304090e1b010507030e030c130e0c060f070b0628032a0e07022d12040f12060b030a030207 67
    0x5480c07803040300c00c1c0e070602c01900c400c2081c0382c0040d86c00f08814030890150103e1188400146440f40c1800748100014100e0001511000b01c0c0001c00428402019414002d0a601c8070f5041002c1c000e145c1400d0110714802d400910380e6941403804182c44007088030512a0700641c808910440e921240c864140400030316551510009a11801d0305800300c246541d8001010f200050312018202125a1030640d5041c14060b50030f0fa250081b15468005540c0300420049400004200002d180001d20681440c04010b002201d01c14402800355680d21000b0004030340b40039a0014504980ea103400b0701045036400d840040c6407408840c03c035004040100c5511503011070b40a0301807400b2000809089090a140f00300c040118502201c4d000d008184640d030000350810b8261044420415075400c084680802e1038040b4402781c40c621000f400740b414108400514621741e0008245001d02d410001e000c1e90606100d100c0c000c8085125140a210f8264410440c0700005401c2c1d030070324106407030000d45414441c09 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 534207661 1250 534206411 534206417
    0x3120e12040f06080c030106050d0204350106080303040f050705030604110307050d02011704030912030e030c090610110a02060c03070302060a0203060f040504050a02040213030c0e07120e100204080a03 88
    0x8800102913104030340c0540150784680e080c80c550b0f4203104c000c56950b40440e0411143c0d50302084001010410404c02008202003a600500f03074444094014504990144201c100c6a0501d43d061020040100469400a80c0502000282070141c50301c113081003429030005525005020821007032105030802080d6010003101035a400540700c40400c040e010b400c0c5000b0340010041c809810501024138100e58015010b4204014044c0e9140450800314820546c00c42c00659120003000d6141002c0060b603e011030102d0b00300100c1e01d0680017003420070802d401a141007151043d2410600041445400c103d540c020b880d16503507500000446581e176000c60301c120014803c0c0c0c40000c00c540c40300d100b9603000340c0c801452071460304483e400b008043d10000d80103480310f0007400340c07201c0103940b2480140781055080c160002c0c030a1a40c2081e1207081816801000440300c14020480000d90005480041d1115044006407618111161030720740203544404000c00c41c0b0010b00412260f400003400b07007000d417180e6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 534208911 1250 534207661 534207689
    0x4171e070c080712122f0a02060d020702031b100c030c080a080114030105010315020f160b190c1b1a0f061e090f0718060903110d030c03120e1204 64
    0x4241295040144401402c0c1b1104821b0003090070303640b000d00d0b021310074501c4c4121554103080e9000102c56030300044540101c02e90001d040c5045040074820104c4480c0c861015800e82c44102d804191035444440c0f40108204040200310304050060f41080201e030b42080c00d140e1603940401c40944103103404c0c02010002e42e8804c5d590002440c2c14026141a02c0c0e10001005620703c0104800c00a03401132003030000510014072101100c80440c00b02c1341c2c01d1900419000b0006e0504240d00d242a03503904400e810080e00301400302030110740101118903a180d19070034240c00c00946080142d80c035a01000301c1880d80d0203400a210851240301c4400e07015401c01c40e240c003030400146110080c0071902d82d02098112004400003041030603402c107402e40c00851030400c02251421380d0380b00ca031070004940206011403c624010720038080701c2442050800760544110200e4049910041e2120b002030200500300940c050103074000e80d19541003802100c4c8044d007202cdc28041c1d6a40d1000c80e6070840d01440501c07203e03032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 534210161 1250 534208911 534208943
    0xe0a060806060a091a151308191203140403020115080a1703090c0616060b1c060b060c0304080a0203060a05040c0b031b04090504171e070c080712 64
    0x8107030240035120061030100041d203003150010242281c8004241d44078004049900750340c4640d5034103542141c10f040e0f115520081182036858001c1c03584c001c10030340d511407074072061041d8000011808894201503a26100803070710a00700c02800f01c2007008004480030703070240020103805402000c8480c0d1002c2071206800d44131007203030343e81c0c3c04c4984010b01010700318007020200c600d214004640080780c05c42030311006150900803c40c00d502903c00002080120f40115090004a1081c180d6100044030702c0b050000031f0000091301c0084c106400b6241d595a01c4d40b1040a1352028100d4040e1558041039a4860360355412454884684d5a42070740030340988000501c03800c02c18411188500c0d80107079040a1107042c1034510140e900010406001107075241d40300191588054090310007403801c52404107080c50701d4078050052101d000124550a54144020b07a500c800406088201c2c0b080c2105850b140c9c03030a81030007007550071182c0c03240707a25026109d80450000c0a60b640d403010741c1d000300940340050b114 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 534211411 1250 534210161 534210163
    0x3020913090f150e03070201050d0b0d080c100204060504090b040603140d03051b03040308190524030106080705060706021e07030f0206070807080a020c06011e0501090302062a070e0a0608 82
    0x41c21308003c24070f40080244900542c010700260011104044000030403000342804520010b00d205003d540e1010042111280c0c1d0404021440c1703440b090307100640c2441d00c2d03d500178095004a015002246803186460386a54980c2e510000040d43c01500206220740f1540c01d16403104681c201e07280c0041e05103070004445058044101d225408404041c82c519039940d2401c5a0310311002c0d04448082d000100303000b883e480c8030300400b40507620348581c101000314983d503541c002980f24008240280d0519404004809001c5160b408403003054a1090b500c5401d464440000d10800c0040c41d20985548a505005507400780505102c500c25180c03c3c2c0c8099681d001070780c2e6020100c400800040005002400d440c2c4103c1c0308a41102a400c00941000d412302042d900b0320000342c01210301c81903d1280b00115440014055004010030308044507100c1c00c5402044091280c0030108582481e00340c205410a02005481c010350301c0004240c0f0141500c0d40410a1035086c141c5441e803000303003402404500500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 534212661 1250 534211411 534211421
    0x503010b0904081209070e0705040906080607080c220f1a18130b030a060917130909020f1e0f0f01080402041e150e09010b1003020913090f15 62
    0x50405802402c01e020000c240741d141c000203040100d18046e02100103006228001a14040c070555107805442d0385c1401418170403142107910404050340031000f804149504082c126800202d012400780c0c0d12003d0702d841c0c0400000084540e4140004540e00041e04094158074406031904855000340301c441c0f480a0245600468411080d2a07002046407082c6290140d001c0507452440384001c5541c4d10b0304030020342014804c15003660042d80b1844401c0400441b55910180d81c850000d20310300b41201d2141b003410101c02070140c000c0e21030380c8004840c00d55662502c90341a4030b00090202440c842d944604c401c400750306a203014010104800701100328030300898150407190041c0e41c1c58482d503032240c0821000e04128103a904400303034006420f291281060142c2c1140c0903040d0031400c030003840c0c07040a100c0000c0007007640010341d25107440c4840c03c1d0b0b542d40e8a0400d281007071501588588000000801045a004821021500e04000b5204000b40b403040140594015903c1c400231540d061108406e4503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 534213911 1250 534212661 534212663
    0x10b0d0519030c020616030801051005090f06070b01180506030703081c0b09130308060a0305070512010e01020406030903030b010806130e0c09070206090d0e010c0206072a0503010b0904 81
    0x50030807000400c85070300300311601005a0081c40c04a000004503000304400790b011003440b8505600d950072550500d5040a1880d00420043e1100f12039558591001481806034079003281c81050005407103500c56a45006072161160040030441e4556903400d4510f01c00411401101d02050525000401600c0c0c04a1140120303030b08a06454500407140b0f507501002c10b841c1d840308002c15610103000c8200c2c0c0781c0c1982c4074450403408020007042002414003810404c4c005101c20310a03c00750a0a00001d0400f0842104680068035003200e81e070800a6014050300070120300304072941c40450009030540d45500910000b41c040e480820000103440011140500704840007a04030b420190340c800d5604050740402e0032801182c0590300d81c00f2484000a09101044e6034850041c1d200d801402020761040c01441103d09403410100310a803a0040003034100c601001000c2d2203a80003007182c03000e06c9843c41807400c3c200100004030581c25128560711108c22028001c0d98007940c40c2041e481d95506060807403901817 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 534215161 1250 534213911 534213913
    0x2030f0a0203210c0a080307170112030503040317130c06170c0903030403171201230f1215040b070504210c0305070605041d190e07050a060908010b0d05 67
    0x804030f800c40303980e50884050b09400200030030090f010035483c0510141048501c00c1c440c1503074904021000412846100e45910309014024004204144110302d102c0c1d48a030349424034540783da079142001d6580760140443e140340381402c0d80c108425819135031100c41d18030388211000c811036911910101c542c1014007071602040d400a402248075124200058554800020b0481c0d180603126078a4a440015000c50000312140c04144058410300704520b03203000d41551400d9800b9180c3c01c5080c0c3e40710749880c040003405080c4500100740d42d5200d02c1c0518010350f0b0020202d6081c072035002205c01541c882198283c0d401903030b050104d0740c036501c600304903011030f50110408444079650246940d032905185800301c480d9654150000000b820a00043c0000c0c4590b4888a4036945000501e24145010301c50054107840690b04018890a603042d01202c030780c08040f0001401c000e54624a031030190725400180d401141404005103131680412501d058591010080c048030301e85905000c0c007807045a40007402 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 534216411 1250 534215161 534215173
    0x15080411060c0706051201080a03090b07030302090a140102010e0706230d11030a0608030301062c1c1401140c070c1203110d020a0206180a0512060402030f0a0203 71
    0x3262148104094800380100410314003424a40c089241c10141d9200101041c130104d00c184000ca140da01e403600411958000c1c1c50303100d040d0365004040d03a038140201500c0500c04a94001454883c1d410703603200d03407000f406480101e0303156405001c8440fa1036141d58015030031303d0045209980c1c04a643c100311140750312401d544003e0b4115808404c140b81718510160302050020607807280c1a4010503a10201200f80c3c00e80d6401c0203400441a26a141c016905941c810001000740c9544060300424600816042000f041e61000c220b00e00455060251030384640341c00c140b0292070300050040b0301950300c1100f50080929182c072034203080e44d0303540c6a448800b074600300004035100b80c100c0c0240b0110744074100103880b450300c03084098144180c984080d0300041c0c440840382e507600b40800c40d50000060340e00091203031800c00c0c1d002a10f64403440e05c405c082d00c4a023008001180d26004994800340100901d00404d1005032b0003042c0d40d8020441d4181e02c68810480d0200c80c601000c9a91030360250090040d1403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 534217661 1250 534216411 534216413
    0x105131505060705030c01060f0e07030908090f0f040e0105180a080d0e0a0c080d09060e100e120105040f0203010b0a080d05070c0315090b06040204060207030b07031103150a150804 79
    0x40c0d401c41c3d40180d41d5400204050300c07003000e088c41008060070f580c0340180b20050610390754080360080104400241490320286801241482d0700381d8480c1c1108940748003410501c90082001a003030030040641140c100702c2d110740048010342102c0d10031100c1d982c0c840d40b0110181d108941e10700c045100546080c00800203000450119045030420303288040481c0c645400580d0b80025907112544a04941e401c06111013900340d03800320b0040010080fa1a044244107024000203088079840300c0c1d40001d0080100500c1c6403500c0e045288280104150000c101d245014100715405100501c0e0403803203075280841400d12807400121403826a40c5640003030240d9404104190380c15131003480c0c15034014401400000010780700001042c4103840024010594921301e02e00301c00056405481c00744614010b00007130206e01e03800607105045076000480402c09883c3c43d4806d800a190001034000408030000402c82040c80003008071a050006560090880760ba4080c00c0150200615821000800d01d0300460 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 534218911 1250 534217661 534217669
    0xa08060915060f03040b0a0e06070e040e0708011a0a1503110f0a0509100f14130509091c0e0d020d030306180c1b0201080f07050f040e0105131505 64
    0x40c1c1d016550342012107060407460001401504035282d454495800041000b04000d410203a05420211000060250180540d0f42649800d0010000c1d010000222240242c0c1c1e0b466400c080710505000c801e42e02401c0d29143c80b24081c0c400925010807078566400b10030752600305913500d6001c5134003069104004401805e0201c0190107002160030032080d0a1080e1060515410020301000e600d6443c0d482d5200f441c4820f001842c00320700d555009100440e003003122203503004076910b6520404141d40582e2901c0640d180484007190f60002e540150440c410002004000542a40c0039005981f07101803003914160216108010504c4141d00500e40707a8440307005040c240c1820401c103100b41004291503488620600c0403400584a00000c075480e140e0f0b42c8010389c1c2280c20000441c0340350300c1445919006400107094483e015211006120380100000da400c0c4c890825110440894180d00d1380c1ca80d9100c1ca10315942e1000e0140c2407040ca00a0301c040a10710b4179110721641d100d40c0e0841002d000340390800300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 534220161 1250 534218911 534218929
    0x150506030405101b1425030c0510141312030e03070b07170907060c0210021c050d0b01020f0d050304020d0b0a050f090313051216030f0308090a030207090c1e02010b04110a0806 77
    0x4070107002183e0123010006800340401841c5d0218524006440c201e1012050000304001d000d0381400448d04011b032000c1108850a4888400c1c21300780072407411180f00501d0b1451040c4503002d000c14240b1070901c564035034000c500310380000742c841d58448180c44038100152500c03214490180400d110101179801030408600512019035a07005031014500039001c00c1c41c03c074600c1220301e000240e00041c420221103061146c3c0004250070320040c1040f4402d00c01907030351000e21601030000e0043c00320000e030440d0f60f40340055a45541c04601d5040c1400d1106010000e0070081d1902d034020359603400003c1854400000380c42003400c0100f10400880d04e89003c1c44500030450307490090394011911005003030703000b0511202c0154030900100c42c80c01c205d428000e00250010f0008c64441c0c00484107240826800602e420030740703846030300c005209443c0d0b080c04e8a54031540400e0340a49121000900d01954066018200c1c80138151000d00100c464400280c0d0a4031070a2402c401145450b000b09a07981800307030b44 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 534221411 1250 534220161 534220163
    0x30a0b0f011b17120907050102011802031e03090a0308070b0610020604020d030207091a0a06030b0d120e15031b0306010f1103040308190201060504150506030405101b1425 75
    0x140f81d1601074049000d0070f19142c210707103111180d80880c0040101d56070901c030341c5c064840c02000080c0550750682c002a00d0b4104004030703541900501000c003501c10380038001c40d00720040040c4894007059aa142051881c0c10284054032807940380e000244460400f511340d00015566a405070005a49907030810040c04296001130701180329260001c14000f40c0d0344544e41100a00b10042e6a41c0100075080001c000300c0c0c5e1308150100341c241f1030900000c1c0c8440441d40c50803540072240c4070841035010390882e2840074101100340d216510741c0010410446660085000b0f0000c181e559481042c02281d40009100948405000800c5c100042600c0b034461000b032800b100070242520b203010b669440d403082941240082d0021b0717988641e41e45a0b101c1e0244070750300003041c081e24148200314a6112204a2201c2c510440e030160308000002003c1020501a0781e4a03209011002c0041003629503000421050580c0c2d1980802c400c0200c82c000000b403202900c0c90542140c00b103618003000880651342d00b1481d028 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 534222661 1250 534221411 534221453
    0x906130201210534020606120c0a240905090a1d0703060203010f090b0d0f08070b01082404150b010909091212020c060402090714030a0b0f011b 63
    0x200042120460f0300072140600038070350b00c107200c070061078140125103c01003d40f50311966403140d03030541c40b9802280c4942e01c124200e030403180040d04401c030380d800c0071038204c0c0b002c0e8001030210001ca941080d0f8012030001424600304000c4000442c0c000b500d203820316010f040d501c05504400142c958181d6080880d91603410a581900e14000304410740c50603440e81c000703c85e07254002c0010322404034440790034001492000010301030307061160013081c0e805000301c101910480c1c2d141ca2441c00c0c01031000841700916409414079406c0d60351009110744520361150002c20260002000c4031a40403c500700d03a001e5078022109498000318062000008c0c1100410581444050000040c06d0481c0e841150f56030b03070081041080ba000c07102d00052101561b1100c40d00110700c18040c0841001000980b02d910036030659034685036480320380e8107440c1c01440b0f40d000a403110002040001030903054001180985080d2100c0411401e600019107000ea80c4880d0604480c49822020012800071904031020f10f010b40b0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 534223911 1250 534222661 534222707
    0x11a070f080d050f010b030106031a0306090d12020a0503010b09040b060703180f0602100507020f0f030c010b010905100f0e120618030f09010818010e0a03080906130201 74
    0x590303500385500904005581c44035001c121120714404a001c0d269000c000b5807802c0070150305265402000703000c103010701410035a0b01e01800401300f03040710044643c1c1c03000604450003440c2ca090216030b580f450f0801c4400044080001912107540ca000b51051a035881c0c1f0741f50f041d40e0a10b07002040b40d800c101c000a90241e1181185d1603580c0380e80000700025402580d1b201c825408005405401c2c4603a9400020f80d6038002008000140e404140c0d560794440d481004039054850700c1d8101e24050942800f22114002c0402d11048080004018109401c800000f4400500600019507030380c2482e208858212030103064103080203214002d5138042c599641804442002c0050200c0c889d25030414100f001d41d4010410701600d5801c00f442442e885500c200103501d089030900c0e0710085402980c461a051188800114510342401501a4118000781c0020800840c041402640e2484102da041c0c01040240d03000c07522510010407001d03c500041031401080212a0f8011220710382d1054110300d80265034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 534225161 1250 534223911 534223913
    0x71403070923010b0405090604091112030a021002031e09212d09010e0604092a0201060b16080904060b0409111305240a050304110105070b011a07 64
    0x1034850619041607441e091400c4019141c0780c0b070303401d40c410703080303078064090034041001a0744e81c4680d40e950205056402103010350f003a2811301e0031901000e81681c0d011003100c1c50042100400800f8100b0000f9a034215440203000c003005c0d404900c801c3d50aa20105e04040d503050442911090042c0c2000c0190112941005010802c011204602550041584001400c002902e02e002d400100c4446400e801c04203001c08021440b200744201c0303503a00e062166a07504200c56941c4d0300d040c3c400410402c5018454041341d1404407064400c4400c5418605503c81c24071b03c10144148194010b4400e80594603140c40c1c02a03844280e01001c1d45411214101c0c00c01900140b178071a4018000200700b20a000360301c8600780391021080d15001c50041d140d04e6070a101c0402000740700c0e901e0780211402503c1d40031020541c841c0d07030241490300c5484820040c500052141e01c41340c1c08030040d8412401f49074896402000c1c070300111041d108038a00505002c10840051112403103101800b00c80f403071003120321460000b00b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 534226411 1250 534225161 534225179
    0xb0a0903050f0406030b181905090c030f010501090c050f0715060302040e06040c140d1e0c06090f050a031a1f080109020a0b09130e070302090f0a0e06070207140307 72
    0x10303070880d074002503d4410a540904002002e85503450f0400d11039219841c01c9140122410a02c242c8c04940c07584950111319102c4060104d56110b4801a090310705604400b900ba5028040a11a4190151501240c0c040c014841d07000d0715202403030a1101b51404420303468075101044085804088282e031800000010390b1117110b0300b811100000080d000301d141c5800c0140780c0718000d0740001c2103c1e580500f040030950740c08048407110783d4084202d103102504c5221040307450308800802031000d82c0036403001c11602d070055000001c42d51001cac0590407071a12041444082406480300400341810b1003800c0d4840c070f10186206502030300748000c00d840c1000e40703928031901d00e030f181c1e005440fa07940d207019407000e505001c0e0003038000e8407001410b64030341006040440c0180600b004146c04a958503008505441014029000107503002810821503091001c40c03840b1480c001e4030701c440c284d0f10b4031140c1131500501180c218400c56580d0098040baa190407034919040c02074a20441e4180a2404041400343c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 534227661 1250 534226411 534226417
    0x50a0309030e0918010509190f1e05030c01050702120d09030c0209100f12050303060105210403050a0305070c0c1403010204090c08071b0203210d0603060f0609090b0a0903050f 77
    0x10b490009484000d031341a105401c44e540139081400941000c102400c0c200d0582c400e074070000c0e502020700b101c07540a0381080300401c1d00ca02c20b0358044038284d850034010300c14000301030b200030b0004000030452500c8406060f80d43d1104070f022452007040074840a8420f44244e4010249103000b418407aa80303142d240c1c0041c03c11081210440911410003c061040384c072a03640d020042c1081e2540c4d015262019219203540380401003589041200004069000380659090000350310744003c034014990805140203015a00b0002880000074546400039402c1c9102d42110104250440b41b45504a42031250125002030420042e603003640d0208400200d5980714802c541c020182c6035903204841c203110200800700501c0d25050041d86001000260240e68041110000010701d00f07003284103601c1c01e010300c00482c0264400085100d1510f100082880f10980002c498900a104100806030301c1c1c40e42d40341110307078107040a0411090280010890802503001082c56400303811310605000c2d0b50740b1018200e40c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 534228911 1250 534227661 534227671
    0x9020301110d1508070e090f0f0a0201082a0a0315080703020a060203040303020319030914060a050c0705100c09050904110114040602101d010f05010f15050a0309030e09 74
    0x1100266031024070200788945003003280c883c1c03584801e440c98608003d5403031030700e030180c00d043c0d60342803001c519403010401c000c0c402c40703d9007001d56106010394150281c0318114180d00341d0100e140c400005070448030300329480d10400b60b203440c15a444000040c40e00c071542c00c00b10300c40003407680c0d600055004110041c00b4900070300a42c401000c02c0c50940c1305008116a82d43d11003402d5600501c402d00001e50084141d60402c2a004000350140311483c9046000d0819204080c02c41104030905440a60b0045503481c400c010711a824483c980f20b11030701a0f114420004003601542100036424100255500021948401458a00441501c400015801030401e039001c5808907203224921100b075801103260119688402349a85c249881c10501944504a42600d500783c80d544034070441100f1440c0c1c54070010441004000c00c92000c00300ca01d040200001e0203a642c1c2c2d2048024000341144260545200346d20055079110700b04220b6841c1507000d4200b00408030207005600d140340c4031a03214043d18034824 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 534230161 1250 534228911 534228941
    0xc0f0f0903070e04080409110702040f050a15080a020d151d06060303070314031b1c06090b06040302220507082a0406050a03020d020706090c0f06200109020301 70
    0x6405400101840c002c0560701c0502440c030500c040102050344801900d044a41c4410080745201408503500f51a10900700001c0d44a0311b00300040360744228640c05544194800310040004025003051144925002d2260002d2075018030360f420014101114013460319445041d051807181414201202a600c01d0b624000c0310310500c1042900d600000c119007a0003030815400742d464000c00f5200140140403101c0014905000000030900080b081e0050881c60328060114940f1041200d002c1c0741d00090900002298500b0020f01143e00c6015100b9524417500c010010341c5414034650900c11903101881e024482101d417910751100d031f01f516004840c400c01c00c40e0ba41c17040c00e1030b1021481d8080012908440414040742164191a00340041224140e4442d414500c0d100d041703050041300030b4421036040c40985400031130000108150354100b41ea0082c42500f1034429103898005000310b106d483d104100014070444ca6500a0945290440c80500c584030000310320503a00741c020909540f0300c2c9002c02d4034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 534231411 1250 534230161 534230167
    0x2030405060106052701120e0714061201050d0804030b090a06050a020a140306061b0708070816030303020f0708070f060510050f1e0a06050a0306060c0302150c0f0f 72
    0x8204040c0030003409840f450074a141004100e000381070a0b100307040e860302c130010342e09250201d50b6030003102c9030240105441c3d000e0102408000e1519203408d168450200c011604120030240f510301007094500032940490110881c2e0310341001c00c55084000d000650703103520204404404115540401c502c00d01c100030081c8a4114945011001c5030b8008061081562050000084640e07000f100d0f24000b0f104003450366142c5d200c440020703102d0700c01e03100c01065442c0807a1003a140c100b0b02050050894480105803a074480c2c0d01e15400e6114043e9144828209208030001d20009019030302410f04c20f0310906002d41050040d079a550000d60000b0810b071100080c81200a00f0010203004030365024880200c8650070301c0c606004510011894411603201d81c510481e411001c04007102542039134100140f09100141da00c13100904242e00007010400000c0c01d006000c1503040c010000421140d0b80b55004041d803a040394003101c884c01d0040c0143c2c601c03100800030100380ca201d01006c1c2c50300e08040c00403660f03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 534232661 1250 534231411 534231413
    0x20111091014032a040e0f0402060d020703110105070e01140705120409020337020304060e0d08070f030b10030507090b04081b0a062001270303050f0903180a090e01020304 75
    0x4c0d00b01c0084e040720301000400080c0a0100070006441c0c114601c080c6220700f0751250320020740b60380a20b0240b0001240302040030303414507500800380d00340c0e002040e0081085440b007010440b100c200e03c0d01a64041907255682d1480b0b0074409000345052805038041d01e142e000041c500380079640c4250b0184406980210030f12158031540c44030040308810a001072134800d8008074001040820540c80d40c4826030703000c8006001c0c801d554010a00c06201c64081c0d4000e0003e040024051120581d4180c001404008001001c18080d208418071480d000346000a17145116000324003520f4003d150004114a0000001d92902d007100603002070700c01d66014103600c25800f8654681c0d000c0d0f4105040c490940c0340401c02c8501d030042c2c80c6284003403040b4604c080401d21b143c062400741c0100c41000906c40c100043c1c2c405004040c00c441c04c0e02c1440381c2d9091095840f0107005010216017511180345c0c1e03420411032440e07280780202a4a8022201034003500c0095582c070700c01c0045039081710302842d184e500001004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 534233911 1250 534232661 534232711
    0x70804031107031101050a0302090607030906091a180112061712030c041502070e25020319030506040603020a17300313061803090602011109101403 65
    0x61090500e03006010b0a0710f580c44001c1d28800184010b41400740015486156130f2103601220105400900304954502d003908e001428140b81f84a0200000c803148004220318041d180c40c9200006200c64a908000ca84030304a1902e440030043c01f414001203060003400c1341000d02480c0000c0c0620100ba10214003101c42e401d0504442080b5480300c080d080082108050b084800c3ea02520708180c3c002c1c86002130027205034540482500400c010b06800c0040092441440300402200364141c1c110140c1c1121409040e41d0302d01646402c6010650340d046102d185a100e9800743c2d5000300010000318025550f50049084840c03140c10851011411010307001c5600e00c100085901d5030301d038003a05480c5a00500d141020320045140c940c108032000404540c0c00c01000380032503021504413404000c11000d0030340008502e80e421400318041140c181001407a1030041c82580b0307424103c82c1c9124a4041c441e002c02840e081e10342e0b00d040c24031a00c8003240720546070050146201d80840401c4807040b0181c00710617 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 534235161 1250 534233911 534233927
    0x1f15080412210b130c021b01111504030e0901030209070c06020f1602100908030406050705100c0e0a0e01050d0609060e0609060103060e031e13051009050103110910050a021507080403 80
    0x10a01c1c00c5c0c149035407101040e0b80050303c50903000c1841140e010048003074004031a5400540940456403048048200720041c1d480d040c0342c0118480d44404010030315660038007400a00034480a50b11001c0b15000a400902514040e03400504c1204010318013151004415001d40001d0707089000f000c0c4240640c4114104095032000c0307000c0a003007104545241c265400d540e0b2040f400707404104030000c6040340c10004100180190300c000d0840a201c00c030643c000080c94003440798641c0d449100d0100300020100740e800b0880d4103982003e00011488800340d1204000340107101804c0758002c0d5100d07444118010305209050003100d050024140e85d503d141490703016110500c8111655400c10003402000f100e5140240000c1706060700030544580e100348140b1103640c2c29611440d00642c0c08050198074541c456040401d4a030240c8041290903000a0500410f004901c01c051700b00240710320941b0b40500960240407101000c2c81103500d07000c6d40400010300802e064070100003040a540074001003507041800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 534236411 1250 534235161 534235189
    0xf0604090503040b22031e0501150627051c08040305030f040512010b030a1118041511030613110f0706021b0109020102060718030b1f15080412210b 65
    0x601d805d01415501e9841c40d100320034403002212001344d03200500300b210a420a0103100b40350400490307244c0e520344025020500c021800f0601d92003100b03c00700769206021170042038520140c92070107034008407a031040240c3d61080d8161035140c001d00c000000130784104024110b12500b0200d0355201ca00d858140284510a030740030050503410b0840006140e100001c9545903182c1240b0300004400035070b8003080142d6142415031400c08a900108030500c81c8007000d906d100d40b054001000440d00203a510040e9000582c0c800d40d01840402c45092444180e401c140c3c05161410b540902d0010f45c4110a0400c0d407000320b040390030940116240140401540d41c02c44103100f0342c4000e02440c0055070000f512118002e00450512044510300d00e0019030000c9880051584035412102504004400d90b440e02241150b8a0500740311410101d40114044000d942c0c1c41c40c161100c0752070342c490795104030f40942c000041004007d10140c01400700341c80c0c0c0407034142da0b1001200c0001c8005805d810711030009a0868 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 534237661 1250 534236411 534236467
    0x50a091b06050a1812390b0f090306090a05100501030b0f0a060504020a05030a0605060703140a2d030c0e0f040b18041212090b0f0604090503040b 64
    0x250070415640c1000071030b01c03a00d001e460b08402c071086080145501000e00d8200041c01d4120150050401105294000c48103c0792106c0d0000b5500d42858980507803c000c4080b00140c4001c902082060b5007403000e885580200140141001d4004022a1521314200c6e00a916503010000d044103111041c03081100c000c6c1e0150f002d101640c1191503005007140081d203130092040710603001425518030b544c40b000140900070411b41d5200520000104142c00c103403880e100045c54800001018074044040718030311540341d100c0039108000880c01c01c215070400e41c0c3c100c0510403100d900d40c01d424100c0c82500d06036400060032007000302507510010f040b603c1000c04007042c851900b440b4040d60342c07030705138211f20300c9803c4801188203082c001c0442d06048014411401c0d40410406200c200405100018280109503407421741c0709041c500100d0540c3c40c180700180a0b104010f021881d41e080300010181d02c40000b810104407103045684181c5540d00903409400501d50103d850024409420341c20295035080740 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 534238911 1250 534237661 534237713
    0x4081207180603020a1e1202040b04030b01090504050604020d05010e071206290d080706020d050714091008041b140a09142e060c0b06121f060306050a09 67
    0x10402030040d4008851041041907040380d60303103a192287e0100d0321a80e10340a0203544943c0e6410000c0702c1c58100d4001224600e54100c0041031928403031203028403454001c00107200a0b00d1343d40038024035801112098481d5500c411a600c4101010000a00102540b041512a002c41810500200c40305019200c000061005003071250f00a0711a5410302c0c039004075045880d9a61380c1c5032188061003048030042420b400070400c20b00801c0750354012881002292151000c00c40804c1c08114176110710506550300a10900c0c08007941031045800320f80c841e00ca2401c100c04064001346641012100398041c0300442c116601c5400241010389000008002100041c00851f1a460004c0200c40d00101400310010f640c01019980d024020b0a42c82e214074038520301d0712a01d807196002490313141c0c001e0301a607420b5005404588242002c1c0c1030700210141d2403000c1c000b0349072490f03001c05c0340c0034030424481c0c0320035180c0c40048080380c45441118090b403e0320b40006159051403402d0008001511011030070020bd403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 534240161 1250 534238911 534238927
    0xe040b010906201204140108010e0f04020d051b040b06161202010605150408060c0c150432061023040603080d0f1109030d03050408120718060302 64
    0x40858030a84005052038680c07540003c1c00401c108035034001d0300b01c0074802c160100d00f241150758001c0099583e991a100906580e80c2c0041d18040c000f8814200300c086840c0010314041d5003030043d80d400502c02000854006401d40ba03607442c003002c02c1705020b46d0860300d55443c580c525140c80741001c1c50406031070b443d04000303c0e0096240e040e0200407001e0b10306c60241c0311031020035101794400c101418000300144808042d51035000d0140c2c2140c0551041445010082409040000d0035071b210500208000c111004c5c440381d4150f080c0c3c00150084950040d90314031803521905840c42120410303510100e2880b2800d641e510710b40340440181c100078121810650030300400030696012012541042800352400b00000c4c0420000c00d100d40c0082e11811000c2046002c4800642103000402945a010300c02034914202c420a90f2059600c2d0300e034180c0c080b19081440c0c9010344c000e10381c05401070700c141e800c14030b4a0a4110b807030700d800c807144000183e507010380303124401210309007201600ca030f890114100001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 534241411 1250 534240161 534240167
    0x1906140d0b0a060305150a11070809040e0c0a090c200d081b0403150e01110406030c0c140601050910031707021f08090f03120f1b0403050303070e040b01 67
    0x403080c05841010610300080000e007698104000660b0b010045030036031200003040410401c030580e0420b40c61350a06803000111010002903500981c3c10110440c0f5000b0399004000045c461710040d0b0321f07540569168036400c4d0b520618654024210b10b403004c2500030112000400714000c0805400a2240780c40344c0e203451580004a501e2401741500300b0040369280c078030b0110f2003224140d130100c080140c0040c000c420049042e0440040d850203200902002081c50021420303100c1154554054002c144010001688039801681c034050650411400310300e4651680302d00345251001e1003889a00c1a401005181004030880364030508154400c0d02c10b1f800d590300d1420100c05040900c80041c2c000c107a400555542040d82c4480710003100c5548211782c00c42030b000e0408802202e82e101d1380d02910204800d01800401100d08241e041d48011040d640c9039540140003002c050440810161564124050000c0380001400594015802141c4920304048000c01484141c42c0240c000c40c200b11041c030b103d0360 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 534242661 1250 534241411 534241429
    0xc0f0105041703040c1a0a0807110d030506120f010c090e130f03140c01151d06190503030a0e091e180316110a08070b0a0c02030a0b190614 61
    0x45001903140e660713111030401060510050f0415040f80c01000008001c040e140401014414402e440300d40030390351503101c20340304060440f2454500da00300c0700540c29181c1c8241c0c019a44600014120070f01d5810940c400c904d00b503001812100c080c1e41d00c2e103180320000e03007146800300281102a500d080d00c0c0350600d4100c60720401d403000140300d84100740d085c02c01c0601905070083e034051318095460315018801e1803280078100c6a520402c05c00c0b4080e00c0401d13100d413078080401d41c0f41391070805804107444080600c10002c04150301214070400a00380454607540034130040c211122155110002c1c1c820071002c029241b50b020b40700841035898020884205881b0810065200c2400c48c0360a4414400c0741c0d0942c118412110103881d001c2000c8500d40800ca1143c682401c40202a20344d001255142c510301c550390070881c06844034069040c85044007061040c68100065403019081d540640d04c0b0350388003007000c081a40c00e5111242c0403212505071504511510000b0180450300e2403444681c2404035411003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 534243911 1250 534242661 534242693
    0x50f01080a261210051504060e0a1a190c0f02100908030f1c05010303080408030a061e05032104140d050703030503073f150b0c0f010504 60
    0x1c401d04800c1034482c45040b010b00e050701d422100c090b5590144080b84800202d003216203201404034128045000d040c0200615800d0341010001c80c68941080c0d010740c2c2c81508813903881c7c4d12504214010445640048404100d14115000103854241d01d5100d00302414041510108000c80c042d1260301140750b8051424440381c041d511160711a0410380c0403aa0820b454105000364800095070f4200010b0140c010301030b8410350140807941e846450620401e030350080c4005000107a544004c10040b079444c1d002035403c4064a000016015941c149804002d40d10b8501030407202d150788401c0006040900c40c0b8540f05041d45080700710002d600b01031107007a01607402002ca41e01512542d40003107484003005141501d800004a0702c80c60380d40d150003807941c1c0c01211140b00250108203070300c02001c252000e1a03000e88504021583c90122690b103442c0c0f50a043d02d5000c9020344070401000311000d15030300324019000c1071039aa41d4500000c038107285403003221909944160314240070007001c5059168420850 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 534245161 1250 534243911 534243923
    0x212040b0a020a050a140712020904080901051c1e0e1002090a23040605180705091807021509030a0903080c070515030f0a051302040c020712030302030406050f01080a 73
    0x5050a60707401c91815040c01801001c5100303400302c1c001802075000e205001c0c0d1310402e084550264540e07040d0310b0801908c6070020b400c040c1e41c402040000300a000a0b1082907410b1500c0e600f4066682841502000720880c1c1c541c40a43d200074910b48806c10b1059501c031501ca92405000c40041c1e4000140c3e40c850b410f01e40190a54041042c2c4880c0e5104400f00780104a0b219966800c01d40f49290360300384a5002c03030114812441c140c00040e0500301900445207030031081100040c030784c0c1c40400943d050380c41245942c1c4c0c85050f9034004107110106500d00350055142e40e0007842161601c840951091901906a5007960307c01e2220000031a0710002c02c4003075a5220003407030703264016510414a400e880c0c0d00300603800700350540d00c0d8011080e2103001e107220300b2101903030149540301d422907041141d0007540c0b000c55040e00002c00381c001d030609810140c04411284100c030101541d440422148809000084000070f40000502c000e10980f0300407507801c10780b0444260702c154503003050aaa1652040001404 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 534246411 1250 534245161 534245167
    0xd1a0c0d11210c09030a030302030a42030b0403050d0b011d1201060e2809080304140703060203090d02070504180312020c10020c0f0601141c05100b100212040b 70
    0x1045869000e0701e401c001302038101c5a1184207403502a02030340081b540c110000e442c0c41005040b404034540d40d41000d80381451120b40034100e4a0030041c1e40f0304c24546041d1081c054120002c0020b0b544220544150700a985142e02d5092025040058450031070300701c0e040001c21200240f81102c0340b0f4209156202c200c41114001503041d03603a42c05015141e2100300c84010311000c1041d45200082450000d00d103100d861400841c051038950101c48560034040e101400070300000c1c0010300840840072604044208440710207a070317070360b4900aa034000c58144215400004240600303d404102c035401411003120305000161510b204414180a00c09000e0300f040000314800600000c1681141c1c40803055005641140200012800c040d51150355044841e00c2550311186d803440c400b0480314140c034201c0000b5003a0300070080811590804014881702001c010580310000501d08020b003001607007001401080b1407a80004004c4090400c0740c8810a54010001d40c040000c1a101110143d8070403181c490b803 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 534247661 1250 534246411 534246421
    0xc04060e01020c04050a1407320904050c2508180a030b1626070e0103180609020406050a0608060118050d1a01080111090d1a0c0d1121 59
    0x403503d03101d000c4494000345000e00b4081840704035040090364410300c0e02107541a03142c401044880c00c1c810300080e00524100c2c1021641600f00d100c464581946500000342882c60141c0000e084480607680100380c40c0002805c05000c0c0301889039148a01d200c0c62014865143d61303180c841c9503103d2000b01030043c0380e04a090300b4055443c11701c180099a00700c05644014036016080b1101031742004001c0010980c050000010b41c2004a51000703107031800111041142c8a42400790350700b00b55091103905058030f408030030f001042c0c2045a02d4846010f12008540008a4014041101c070940c01c4940070798806034060203a142c0000005402000a2810103804000c0c2405803104000540110307900400c00b40240050146549105080070400d05440003181d030388013101404c9860901c1d20a4203164140900c19141c600703801d10650440c05042c040c00c0f0407150514500300e8440071500100350060204068503000564450a424bc81a9008440c5400039035642d00340000d0722181c6460755110f0b0031b00018 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 534248911 1250 534247661 534247663
    0x20703020a140117070906170105011d041b0e0a06080c1e0d0c1e0801120f110d08040f06050a0c0b06011205160e09061f0c120f0e090c04060e0102 64
    0x703849600c810542c0c00c80f803d0150b80100901801c1c1f0494001843c079a1030030401c2d01c603c0101504032201610f4000c601070503a9403240c440c1001186296005584103034400b0b21010021000c0d4052205030384281d030841d0360608001098030b40750000010488040104283c0504042c00c0310101c028a06c81846040060071001010780f040000c0151540e0401911700841c079004411025440d50a4100203803658200381c040b10410f070244901d01d5040c907440d0791074000c203030101445600ea500030580b0f9801082808081418034680031b0045420b44c000160400480390041d0f81080a00303500d02e000d901c0d0892050000b0460100b040d0080d110303168810105007641e00800400ea08045c05040521803031900c016000641c4201820080204036101201000ca250060304a4440c0d40c00601086002d03244003209920001e089001c0d03c18454030459400100c2e090a0650448190130b0303982d03c45110840300c1c020aa0400c00ea000b50050411a003480761000164090350203403461480c040d290281c0c501c0040b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 534250161 1250 534248911 534248927
    0x70c030213020a030b0d05060118091b05010210060501050d020a0e101e080f0c0705160f170a02100e0301140112170f1602011e0206010f06020703020a1401 68
    0x95111124900d8a220310001d0b80282c02d1140254030f0401c00d2224402c00e02102e2a444880100903400050040c08029116545201c10b0000564000b400321032507550f02d2a031640e00040c2c8604040c02c500704202640e41000317051a002c040f5042404100d140100103405409070303950380044c680d008030780c11841078842c2d40c0c0c149160800802043c6a20419a406013151034106007200e01151180050202103004222850140780441201205551102c80c101c40d0354021200880d010701962200c2d040f940072040108014002208520700c81500e0603520783d1020a031002c0e202c035550013211b400005603664904103500710302c05042c05030752640d10400081c010003441c03140e407220040c000c1c0040744450b4000c0100b201140328403150500301103a09c00d003c07164021400c0c80101c0c03403420010343c2c00020342c60100c003140f5031044c1080284404d0b261001c60510b81d0400250700140d000e2401003010420000a841c02081c0302c4c0050501d83d82144c002c1858400640500380d00c1003420800c1e05081d034800e640c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 534251411 1250 534250161 534250163
    0x40303020d020a1e020f030d0b0613080c0405060d0210080c09040c0c0209060301090206031504110307020d1710090b0d020411120c0310090507170703061701061505070c03 75
    0x708554421014002030468007a41c42200e40000d01600303c88001e5000007050381603080c5120086017003200340109a03019061f122540d681010f42444000203035001055854050524030300641b0400c510002404211388000700424400c80b891580c40c809625605150341841c1864a420b05850350703100c01c0098548245c4c8240358001d0b141c040c2d861190703688541e20000052003140c808240f51035010415090380c2c01c0c5040a907100c0d5042010944250701080326440022004e00042406150145100070725007040f00c10740c0160304035001c5d001103150300c09202001540c4a065107100c5080010080e10114540e00078003c200c0e60b54001320f207840c2c2d82c01440c850010b074020b00502c0b0090a421440c80b40b900310b43c0003407040b412100d0116100310600b2080c0c82c0b0560181d10141c240d00e203410b4180d0080c10000d45580c00b400585502c1f06230922015440c507205030140e48002c29030a1405170b046240410200c0c407540e0f075900d4001c00740403050341008003a00b81a41413070301507110030712400c0c00340c00f00a441e80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 534252661 1250 534251411 534251437
    0x1220090c0408070902030f0c0a090f0311040e070e0a1a060d0c020f030c120a0309150c35060a090c020606010801120f03031a03031c0b0d1a04030302 65
    0x1005200c5032460010400d481d481c80030b8034500c0b507030703044c503002a07002c00d5518120f2210400d0000c0c6d45413030740c6c2c2c010303011b420803515110903120b603124100b00700d2801d50b800549000c0701c00c0222036503c0c2058025a20018040c10050840c14600310862402c082c002e000000c1c1d0a0706c520009040c40785041c810020910010030b00c955540018418400070110401103030003500410384000c3c1541004802e9442d80401c210250982c1d503d450741c0500c507603011a228074103046e030ba400c1e070601041d001c07440c0c1e108110380c202000495056803a030107000c07484000d0207200804a43c80e204040c591107004e000400c2e050b04120303000561254000125201010b800114a01d03280c0a0308011090380001c40e00d00681c02070300d6000a990f2600c010b183e40032510f08020740540102c1030800e000a00c0382d40305940200c03078041d60515151081c4000380c150b03400744820032056031054501e81e24402c02480b5030000315408403040100548550345180c841c02c10001e0130802d01074160005014503000360120752205003000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 534253911 1250 534252661 534252679
    0x180302120f0709050601030e0a0f082116080112031e2a1101111e010b040204120b130b0f0c0f0412030906050309070b0c01020702030d0c03030b0303041220 68
    0x43c1204005000407143c0798002424032014080c882c20119410140c070340c00044480c090405038461050a5004801000403062110340c00100382e460301403054011800f580a100030b81c112490000c0500b201038020211095590001c40300113070b00001440c2c03559032402510308000c56451000d03100a250100c06282c140941544e42407003810301c1c6038104400d441540c3d440d054445070001121aa140d074815600700e907004441e800354100c00745403003594860b40b0300c0000c50007a00e1180402d0980c0c205a00ca900c8800c1c9803415807081245095260354010080052150318a10640720240380c1c0b0b40c00b40c00400000c52803008913402050034011210f0552300300501590350f550f941445070b8042007214043e40001d5203201c0201d2224400d0003140d0252110784024805c85040044031001984000c20403a0599802c110341d4005880500c038592420030390381c954506880079414094107503810b07511081c0c840d80040106001c2c108a0a000d07000e8950400c0080882da0209852103440d41c081c503007410390103644a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 534255161 1250 534253911 534253919
    0x30102070b191107020603070809010e0d051c0903050f0708090a030b061c120e0d06050702070503060a0212010603110d15060f17011502031308061006180302120f07 72
    0x1600050032010b10868040080c400311500e8080c0601403118000d510180400114030018800e49989170080c0403800000344084200107200d14100c3c0302c0600b440032841c007040400c01c00c1d56986071141100d004180511640326640c0c0c0c02002032180b4002000c036288041111800d10401e035050740d0308004050481484580c6030305110200780d4040b22034900c01c0c10000c00752140382e030510f04c1ca465080e50250000710110000c400c02c3c1c94113501c0102a5400072014401c000208550b401001d000721000d402411b0220305017030600d42004002084020f11900402043c00ea400e08416064112811880c0020f0f441c01781072000301940c82010040404941848076421100824034400300440d00203031038158420891090a880400100c880c2c251403080350b000411030346410b414000600f041c9441500e10b445080c00114a81d1007003034000c3c0080b940588104580074071031480c02c0700a031420f401c0c41410750a0126000505042070700000703020344130316a00c41800741008c10009060070805800d9842660321 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 534256411 1250 534255161 534255181
    0xf0c0102031306180b0a0b0d02150d05010b1611130c09080105060406050a0b0703140d05060310090519080903010915060b030403020a030f09050d0302030c0615030c0f030102070b 78
    0x5010041da201440c00d607441d0300d071340821004441415840301200c503c1e552900c50800c020594024802e40080c0c0902441005a84102d10766080b03810094125444070307400c1b00d005048a00507081955402401c02c00000044100d0b1041c45065a01c401214251821080441c800c03654020b42841500e0030302c15a0340115821889090655040d04002c001a607603020402007520b445200c2d10b500a42c4200040c88080e084000604215001c1e0070554991090b03205014203661150510601d025550001e0040502c2d01b0b001400403603452200601151005d40c03503c43e103907e8020f01c00000f107402a0061010090300e10117a40d003040c0c3c000c0007001001d01c1d43c208800003030b6142aa400c401407428101007210751120046e40c0c017941e0140d005150180c1c00d0b9030203070f4083c20a10407110a100c0c2c0741000044ea0740c2e8425003c40f600b0b10a50144d13442d0100740102900c2d014000d0240d0b0503094440302c031140c9549000540c55401c03041258800c11120302c4001182c0244500c00d0064400e401000c00c2042d4100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 534257661 1250 534256411 534256441
    0x15090a050c040204060507022412160f0f110703060c033303022103070804091406010e06070c0b0a0203040503070906060507020d110d0b07030c08060d0201050f0c010203 74
    0x2005405466255441d1070401049110710700540000c05d0080c45800c015060141482d007000c0e03961074519403014204c1489078030342c0c2c108034a03044d152031114080044001f006140d0750300310340b80b03401d1590b40b0a6000c0400340080345100000810000f04c4550068100c000304246d4005641200040121804141c4018080c006d988410300c0340c03403030310010420b031010351540984010442c840c000b4600d07819039082103140346500035209500040300b03840f222039020070700050208a101e0f200c459902e5142c0003404064510300703288071400ca29a401000f110f40d810110701040b00a08a03010b996030641ca1604250303003815500003103030100020075038401c003c0d000402030058a00480840d0b503656550040c40c001c2d6000340c0560030019000303001c1c0c01c00600b010301a02408038030039010140c8025111021030201e0f011150207a4490f2080320074000742981500c40c01034800484d1400306810300d488804503465245070b00000703042040011750480c0d40702ea124140c8400c00680b2009558030304043ca20440405 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 534258911 1250 534257661 534257663
    0x110d151103090d21022a01060303080a090213180f05010b181005010e1315030212070602280f1212060e06010e010201060b0a0314010905010509040f0515090a 69
    0x80704a80040e04200c0c013495019a4500d07020480c2450b03810120703041e030065080700454032540e00811640c04071142c11100300a2450b000800001070940c658140103262020140266010500c0c0c80b08660160b00d44100c0201000354214000c13450a126135060045a403402e8000750811001d40360f00c170100b00c410f4000515000041703a902c1140c0c4a104411007841c40180c03050354082c10b100d0000c02c42035004141040343c03034100504001c0701e119100340100074bc5680c02a147c9103003920010034411460480f1038206120f009100411a0a0030918041c0d9a1000f02500740c810900785603903081d4503000030107403100390790b440660308608540900c1c14140c141c102d04640382c08684108140c082c529014481c1d0303800c4590585464005494000065a181c8040c0001c03a0465403a0b0102007202d4003214000c0074000501d503000101c4010150508070020410707040b0003801801c000c01008641e0b2105101d682060300022840319208080c9080c0380b41000d084410b5850102c40400c20210280c0414851041 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 534260161 1250 534258911 534258913
    0xc090b040306051009020901080114150f1308120d1512030f02060606032401020709240b12070818061312020a03050d0903050c01051f06030207110d15110309 69
    0x4c5915100c00e802680686005140011107540040044a15003e0200704c506c80180c83c41d41100100c0c01098800da02140214070422000a034031201c00c1e01219062004004a001400d01c41d04c3d180c2c090041c40c440c11400f4500070391282548210501101082002000607200328282d181803440c000e072a030303655030034640054000c0030002361150424000b00ca10403d042035110030000480c001c1e00d070403207100310500e81c1144a6072001180d0701515101d000216a48600c0c0c9101c414020511404580d165403c0091a1170041c0404072024007583c0000350080c074103040151150303035000d035036001c0c0c080b00c5e501441c40ca110345018020004541c44140d24424010b48500b000d11f0780d143c200b0303030742c52030904001400075504104010400b840f0381e001e4031190784a40381040c0b802c0c00c8201c603c0e00b9114155142480b03200f12840802c40195040b200400401c001c0c181541010131039103640816407000b1120340e0180444010001c01c00034a48494400528500c00410034601c0c42070303541010390801ca5080c1c0c42 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 534261411 1250 534260161 534260191
    0x2031f081f060b0a2604081b0a0b040c180608030307050f0f030f010603050f06030606010e0f041a030f0f100b0109030209041103070906210f08030108060f070302070203030d0c090b04030605 83
    0xe28203480c64840c80755800070821f52400c04075001c1d2020391038001088807464015a64200001641d009150340158003e000100100b8141034155111b107a0310094104024030300b5804010304180401505c1c2c0c800c00c103091241e1110121801c40318540b190450016413260300204001512085082c00f5042e10410b035420403a80d511060b0341c8000b10b00030b8860941c190300c414001a00c5620800e0f0140176007001404007040e079400c1401140607680d100990020b0507401070108030755802c04000202011070104002c115035840c1410f03054844802e02012480c6d03985403410808070343d001e01000001958041c0c40350296150500342800e0198520040500ca802034480024030300501e40107d1003a200400f004c85054400c10744640507034000d120040f6200c144900064002c5141400036600920704140601b90a240c5001140d0b60760000034820701c1410b10500020000d0389001080d20340410428a00042d00303028190b049d20340c0c00c040d50103c820050000340101c104480e641000b4041c41883c0300703000e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 534262661 1250 534261411 534261467
    0xb06061204030f020c010f050913020d0f020d2a080402060720040605040218061308070602060405010b04090b16020f060108011d0a0f08070602120a02031f081f060b0a 73
    0x1f075840c18200400700056028004500140790480b0905d80c035040400c0c00501d032828070780d060343c10b40c0c0c000d090b420261540443c410035030107114015207050b5500120154151413000c4c110030192808590710b07600b0025402d00190464036204111960142c0080301c40344a03140451001202196111599000d5402d205000549041900039500c42c0081d4440c80807140548100740502c5403c2003070301005a40101d0b100054181c024010003015202c1e070b902420580c9007606103182510385002600340100d00d084501004180010450341e001b03640e809610907400e400c080d04914041102da0045014080c0800000f481d043c15800381080410301c40c0e10000c20300385029960b4a0301440320020740340d0019442c540c1c000071041e800030f2500c1e500c10040181404030800c1e102650f0035040300ca110300650f000040c42032039000d07103586651500b0401d060095803801c00c002c458a450001c608801000c0f030b00c80b007284c03070049240c208601906c035903004541c45000d541c5004042d02c141c074240170040c44c64888400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 534263911 1250 534262661 534262667
    0xb030c0906030f1905160309050a0c0b12010e01030201050301030602180301050c0307020d2a17071b12050d1818020a140f1c06180506010306051c0b06061204030f020c01 74
    0x20300c506c10300003156030716401c0400103801500c100441182c00b030083c80c106a0008081c0000c617805428041c011a86a03004044003200c0e01c40d0603000164101c040200410060f0782c04030899040d80d41c0000d000d030710303044080d40e40e42001c40307180c11045c1d06500381800c103e01003c105024500c100e503076600301c03a10030350000d50a6400002451401800c00c003203940c0300f01417060020380c03092814804e10f58040d2065900c020041160001002101c200c0b41c03003011010740702c1070420300c3c1c40507007214045080141c04540e00d25688109900210003072040865210500c4c801101c13011000b0201e030254008500700b025881c200a5000003015404550078040809141455405441c00c50302801300c4c080c80d0040119041e8460804d0761229500244c50307480c003264070b09080902140e140c19140e4041160f043c4400058140e541c20342100f800b94000440b244010700300b114101c440250407030303c0c40546482c1d00010413003e01c108008801a110800e0074402090342c0048018000d400c250300b0307500d0040000b4011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 534265161 1250 534263911 534263921
    0x30e010b0123030603030c0706020a0302390a0513020919050102060f1911130e070c15110a0206070201140f150a030507090608160e010b030c0906030f19 67
    0x194040b0400184050300d8500c80350066411800003400c90f810b14410707100c880d25003006e5401100c01604002122403c150301048162100411008481860000d0452601e000c0c000c031440b03000d00d40446201e25900b900c0d4a0650806490050510002e0500d4204240e02a500501402c0d02036a05520307090300b01e01c0400c0301c010031b5070720503030103000180c840741580c4080c1100a4944846110f150713000d14101c4600d072149020f00049554502d84a55002001c0d40004000d0340c041055080b070141041079907540580b6460307100e907201c0b00d03441100c104003040760002d200960b81d0301165030000501d0030383c00382c00240c0b95200d4070b0143c2c028800307681031420b005c0a00700e06440722000b0071540c038049405a1058210540c0514015150910140d9203846140c54045180e020812440e81d4440030f0100c0e600a220b01d0500e40178000440c04034524111081d46071580521588a92490110129100025034411141490700c01030045480341007448100449010076101103449950318550f50b442c2085501030303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 534266411 1250 534265161 534265187
    0xc0c01080a090515150d0308190501050a050d110d0605010e18060609090a0b0c041d1306020309160306050a0b040e07150504090e01051501020a0c0b1c0c030e010b01 72
    0x9010542ca454a00c00040701c0041d016110328164600c20761702a440d02100c44101c40c0c0607544515140c18026044890a2039107032805103820708080052085450305100182210019611101050107504140e4410303e903104100c8d501821841018051280c2c9800c0b941c10381c0d42140c1400456191004003841000806003030300850f0f0030101c001041c514000c00c1241d404900c6000390350061599035201541e04a080747c440d8081032010070240880fa610080d8030b000c00021150503080c0f4205401e80b100e144400920040c801038000000070040701083c0095200b4032a010301412506440340340000161004960300e4980d18035000e102a1586013a01800b41c14804084c0500001414030510f05c00c2d800c0e04014030403c1c41801c00c00005c411103284240c0c1c2e07110365440000641c50400300100c00e0b02d2000c0088042c11544489a01e0b00030071880ea11110031195a880c40e190f840b442104c0c8421040340c0c042c075120030030307142042215006425800800f000007103500200328045052006541880c29526 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 534267661 1250 534266411 534266413
    0x1401170106122c0d0305150117070e0d0807060c0804020607060c11150f06060a021c230a030b0402030c040603180203030705070602060f070f08040f080c0c01080a0905 73
    0x781150000302d94411010300c00a01482000b0b0000700b00d4030101c1c03029001101555030b100318480c0e06580c0c0e040c8555a00405e01150b1000b00039076140000b4402d00071000e060441840482c049500b4500460000c00c803508081c15120101e80a42402545a00041425118113041071000c1007100c0c480d501c06485103500070034060803c105611410000e00000c04503000340460340c0181d80100108000300c404d04403904d201110245043e2600e0300c5403080181403240104828041c504034241c02140d48011510031201c99859140180411210002581c1e440050020603050306500d030500c540040c912444103803030602140d44a10b05000403848201ca00e1054147e040c4400d0115a1194001c0c10700e420f4900c1c421010440e080c1c000038210307800041c0840c1c8076486004c081102c15010b201c42a80995440030422542c9400840944004298809001003140e4035000808020908c2284684143c1000c6140d07112100c100e02c9c0d40e82ca00005011501040c61100012001c05031400b4290790168808 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 534268911 1250 534267661 534267677
    0x1807051b0303061c170318010e0106060c021009030b0709061e0e042f130b1602220608070f121208060a08030a1e0203070201091a131401170106 63
    0x15107444d0366054010000c84003003c0d85003d84504079074860140d170040d000381e00a0400d114407004e500782141ea10f085580070b1a41058003c1154641040250005a405072203074800009900c0003280c5801d2581c10041020300c04800340901d9603840030444042d5441c0f83c82d1541842848030012102d41c015090304800200b07103c40202c0e0b5070030142c1100c3c40d407030440c0b0414030301b1803880ca0490041c81c0342c2d4000c40e1030040740840d1006241150200c030b48001d02c540d5501600d02424120f0350b480c841c0044102070302032031803a410741c40502040c0d8118084141c82160400950341c44545e0b6a40300c0c1034a200e0105e286032260710204000c070311401e03025181070b44040c0c05005810003540541d942e0100404050b0311100f111800900c0303203010320007032204103003e0381e40c507045106440c0e80c41800302c813000c0c60004550041c41040b0060340c0068440f02611484042071365920712503101241d1500c81d241a40040b46e1040000113801480c4550300a5040c1d001d0301e0304000041d59614003aa810000d10861002034416 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 534270161 1250 534268911 534268939
    0x1030605030c09010314010b060c0c0405220b0705040905190b0a1d060621090601062f0c04060e09070b070c0b361f02070509061807051b030306 63
    0x11030658214034a840c400440c440070400005440e54010042b0a000c540011080d170a60b46071a110307140d4494030344801d1200a2a080c00c10f201910042e01000b09081964008550040d0042096070010300d2100d10505c2140781069070110981550110a4aa5411302842000f24038241081c0015036945159482e451046010781c2c046242300038114a40003031f8100240d60045002c5810b000128860b050550114101355000717501e00079059203c04108941c1803006518901c40619404a40d82c5241d100c0d00d10074107201c00d450910070003030303007442d4494507100c000a9420b0132203a11030321548940040d510015a24a40d0031003501c1528001003500c1c003d05414400c00029101824800780308000b441c2890400108512988284080c2104240140c0c83c0c4550320380303071031003031450031000c505602d00c1801c0020001a42d41c504501031136100b01d0f04900050360702d443d034048000d401c0c414201c442d821414a040040d106a001a1802440c00f910241011285000108882c0100005408040e00d0303402 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 534271411 1250 534270161 534270173
    0x60c0e06121b0703050406020d08041e0606090501140406080c01020319051327270212030406091a0c0c010c02030a1403090f0102010b03030403020d02150406030b01030605030c090103 80
    0xc02048142d4040e450528141c014030b4090070000344680c803120703501c506080b0302130315111441078081c0c1007200d40d20420001840030038002ca170141c482c400340319170310f03c05113482d1001d440305400c0500450700e0000001150007114101808800c0c0545040012170b0315424120744509070a42c4081c0942e004000d100103007071907000d14891402680c038005080c0001c00ca10030025290a92028101c1103d41090603041d02d030816084007941c051010410086d10807a44102482d094003c591248d080010f00610a54451002c001c20941c0f02c941580d42c1c1e162524000b501103011401400950085d09d1074020b108541c80c403c550300440f4003402468a9540d05004486018051404981501800d58080c00285a00b50110b1105c1c020b8005540c42c1c0c00601d0520244202c0e58101c2c504680c108064580e00382c60200880f4243d03074041d07800604080d42800030440c07031043c42c500050f0300000000c0006185615034880f44d12001e09a0b414000c00317075a10304041c0e0300ca1212100d039500c413103000010400124 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 534272661 1250 534271411 534271447
    0x120309131a120f010509060a14040f150213030b2a030103020609011b0506091903090b0a090b0301090506040b0904030f1d040c090905010803030705071b21060c0e06 72
    0x6100d00c1103c0c51403010007602e074291030007600ea104180d84814140400e240c014001c07064016a241c1d0050b1076450162103007068141c070003070040d0000c640341840320540003c54048441e42d41045540e811119500e141000d06e0b04000c40300d2412440003881d0300442c440403143d0400c1c020003030300159810f5034250b07020810641c1c0000c2103103045c442e00100204080d21003680000c8000e00550240096261900003a411b00211b500444d410320441d45603000007075081071154064814452100d9150a502002601e0781e1400c1d40001202850220001035544031503044103110b0b01054600f8031800f8206010f019114409550007000318085042c04008a4456140b10035660b0410988060742500c03540881e0840d000303400d0304c200040550509101c0c038038007401950700519003500118514942010001c14038011400d0040004110300c03200201404000c440e800a880e4814085c2c0040513140103070800e80307481c601c044030340b02e003000c440c00c448501801ca8940000009070001d840d192240c03006280b61a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 534273911 1250 534272661 534272689
    0x810110a0f0e0a0b0a020c1012050408070b090d020c10090501120f021b0105090a030f05130807060816170601030b03030c03040e2a0702010c0302010b120309131a 71
    0x102d0b42d8640d21561070040050080403c01c80c520368541403008020f04100d80880d01501a0603007002c203d1807035a12071009443d202c4014000179182d100d514016015110b03000000e0200a030038810b0013500040881c003a82070429039000c450741401b8080620180c404524100008640640300c00c000550084500c2c4152545a02c40040c1000000f00100220f0700003000c0b00c4281000071008007460002482a039400411840080c1190306441d0341c02004922080401d0081000202c1d5241b009040c0d042c1d41000760401c81c003a0b4640c1c5859042c024054034045806611544814820b080d000d0b0085901c005c0c1c118400c045040300381d07601d90040d4041c0560054154161104008405412805002a00190a1100700a0613608007203610741c551410701d111108441e190800724150140f09641214401d80d03083c203100c0100401c6050aa00600c034884005400c0ba40c2c8054889000401000030464588200c41c90f81e00d400d80b024144080351300790395440a040c800401c10001c00c0c13a010b01004044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 534275161 1250 534273911 534273917
    0x160303140d0e0f0c0112060506030112020d120806010f1d060a05071707032606040f090b1302040e07050a051e0307090203010905010b03070e040903030b12070810110a0f 74
    0xa070350b030000d089140014030030140368603410250995002d90b03481651350380501140740090010506040c0010394a11040c49107140402d1711410400454441c1d100c03156100750013401911004100101c040c040703000c201d451a002502a040030310f0181c0c0180003840000e03501c4030041c40b5214541c0180071580d0f006215403028413209201600c00612012000145121500c4120303866a000d49805071590400b128590940f17880d1008400b4010b5000310a9a8804000c450114004444565900040c020118050b02c041452410031002d600d00c1c40b03a0400062080c0d030704016070308a15405d5519030119005030b80d484500090200a60710b001840c0c490030300c0d10f06010402240c0c50704002450080d85a01c003180482e00800104007204141c42039034018900480e005240d4a0321010003080e19208102c258440d580c4c074403800c03060505c654400760350142c02802c183d1030351005296980c0e4860181c49120520300c16030501501030303142e901821440c1d0004000030750504401034002d8030280751082100e010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 534276411 1250 534275161 534275171
    0x8040b060118230411030f2d06131505011101060e01120c05040b0a21080d1a040e0607050c010f091a0a090c0b0f0708071103160303140d 60
    0x15940b1600300c0100030111110880700c5000c2caa00f18410407002807003464400c0f413509448030285c030344a500f141d9206051159284003950f410340700c0d0503400410100805002c2811300c400d422098403103411f03805a00d04803000c01c0d158142c10060f4040d04e00201d2a0b2085a4518004200c4c40d40100480780e4560200e00c008a02d045e145e40120901c007070264012880f568501c03a405040c450742107038810141000381e03000d0080c40d07410b0021500c10380b250701ca0703550652000b1300c14210026226564150442e8014416503450102c01c9070304001e001d00390fa041110002c0319103884070520b8070780300b00da0381280d80300040d103960b545030308068806401140d0607585a5403034220400000105204081c041d030310490644800c9101643c210100313150081403001210318086402010500d001d11401c00c841590550b40d580c0c1c1e0b0014451151409100c60040c10075a021810b802085100220280d1004e416012209200e94500200060b0400c03444050b003c82c003401c038112103410749080181042c00e0030800100f0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 534277661 1250 534276411 534276437
    0x20c150405030a0c150219110319050304020301020c0d02070f050a0510050f07050d020d17070e0f0f0406030f17190509120607020106170c15070201030b1203030406060905040308040b0601 82
    0x5c10390b8021950030403099000c50349080015003001e1303204803501d2280300071410485010301208110003c00c809005002d030110000e42107540c00d40446001c4071280c02030343c2810260310b102a42d074200da40506e0f000d01c42c032818081024209000050103d443c02003130340b0031800e20008103541c1a804801c8010008508100c00804180700704804040364142d5030061404001e400b600410310b80100d09000610f54040062114042e4070001c1c0980c1000100c68107488940840005008002c649611640050400341d001043c01921100d46008a0041c0000d010b10035003e0b43c0d0311454410040c2d4103503402d0441001100061180014100303596014200d00d4012910680051416a0440d06440140c1d103070070302032002c0d9414822840c0c00050540040a00c0c165180028070007141759900d03d03880d0320003c00c1003030643e031003500a40d176510006807a012a4803990610180c903684200c030150b03076450500c140000d1068051007130601c5660140e540c01c010352125521580c4c0034002603c01410440b40b421085 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 534278911 1250 534277661 534277703
    0x2090901030b07022416090f08030316020c01020601030b0402060f0c010b040606030501080c22060f060905030303010501080f07112508070302061902030c0709020c150405030a0c 78
    0x9001c1d42c018115844140740962000f450f10008100e0203075100403403540508030340e20f5100080e03000586e0102c0642d401d40400801c4640c0d11855000280302c402e80c090002e804040800114080c01101c541c00c80019002c0e40160b030344801a0851500592041c0700400124a0404d801508648014400f920340180d10340f01e41c1160300190032001099640c0c21641c1001d03e421b11a400041003242014002585848038054803500226080c5005060421200030f02c40c1e02c0c817411040f4002d684400b044103d80b6044200e02016141c01110b010036400000810a45000002d43e4120f61059441044542d210400c1c030812180181100060040c02c00300700c920090309000b000303d00300000b05486000c40c00800e810001b011245c0c1700c0d1440b604000720900258949104440440d4540101074010b030100c4201240341d407013481c11604440c0039499022079034600c00c0d001000311540500441e0b600d400c61505600280e481900e009200307520030407041c60364502441c0301c126618001c090b110628440e0308104 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 534280161 1250 534278911 534278929
    0xd1a07120606051c0b090115090911031602030c070b0a020f070314160342020310050121150902040b07140d08060427060f0b0402180f01030209 63
    0x200c0c0c007042e004180b04c0d400e000440007003402140d40e00e00901c0f0010740718001c1498220f041c05841d9581c9410401080100d0260001c480100380ba02d204020030304800c3c84000c1550000c0e144c00350711100040000c032685100005031404580460007402400f032605010301d84940c400050001540213032250402d056100381b250038015802104268a400f1104449c14140068444603003454100c12509102090966034041040c0440032442990301c07180c2c4041076071040410a514040c24098020705090100ca60003560241c02040010511a9154001560a401054120380082a0640800100d420b041e00300154a0030803241c1031918a0304c44110358141e902c181c008210118001038403070204007d08240b1100140c241c00036005501c00104010010702024007007d100c0c68076060f030382000c50444811401c0f05050034903528121080b514042002c2c08c1c0010100000d145892642c0f0410b0400f030088402c43c80d5280141409080504100b0580b50740c10390138241090b9003403001c0e0040e503c81180f0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 534281411 1250 534280161 534280169
    0x1609032a030b1015030204080703151d1014011410030608070b04150e1503060301140916050f28080a0b1f0302060d0203040510021809060d1a071206 65
    0x1c01c80f032003410310343c0644242020b15501030405104010401802501127211410340750310490365100724140e0040c21000d030a045034195141c03560f0100d518240750000421094160342c42600707019440b40681200c200d007809108600f44082154910015850b00803280c500c0c00307909080c0010302c0307922002c90925141d05a0861046440b00003401d00c046003001004c50701c01c8007245801c0e13110b18440d501142032080503c00b604850440400415202d541c213401464060090a800f28158035054000554859940441074403000000c00c2c0440c89091612511300048070140070400c40300c400e015140c15190ba1840700210a4118100c04914060284290b001d40e5010703450308403490501883d0380a0881c40f44803541e041600302e900400041e140c2c08140d4103003000340074006803695601c7c1441741c1810311500a002c4150300c001280006544020340448048205540c284030039507504091010b0080c207810302030841c00f90141044815a00c48604c00da010781c0d1460442040c1201205000c140c40403500 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 534282661 1250 534281411 534281431
    0xb0702060d1b02030c12190c08040306090312050f0f162003070b070e0a030803040602070b09030309070602060603070e0712050c090405070e010e010e040902060c061609032a030b 78
    0x140865180402c100ca1b40c03040c06d009000030700d060740440318152650b0550950606014a814655040c002c2c074200b50b40040d81c101005019032070891600030241c000f8002c0e90049649013201040d11040415036480c82604807210501064903082003c1902c031070300030214800c20065000562002000d04030b4110058450030003142c8580b014641080003100080201c0e0411102c050030703c0c4c07143e4800d40e141d400c8a4100054581d00d40707482c20508040e11404c03002500d0540c41d00188041604008010351080308000c0556001d15101c1c0320803a181d04094406950540c010038061000300f1120383c0441d007141003410911441001d030100340055403030850f2907500032040868035046030300709800b44680c002954549598441405000a4285280c0208250401203441e60f81400c944031580800c070794540041480340c0305e9109050040d615030f0221400f0b4022400380341c401c201c96000e40c3d1110306507507008040810000f5500024490300c03a081c4805a80002070381c02c0000032a107440201c078054141c1207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 534283911 1250 534282661 534282667
    0x30e0f01021602030d0f0c080f0906030907030b0c1206060a02011803092103080a15080a0c030215070c090b04020f0304110102060108030415120f0e150906010b0702060d1b0203 77
    0x801051706005881500c50107000c0542e981e001c08942c01589030b5a41740d8441310b244d03101d003815000d07603805002e00411182c10604c00018056101c50006845049038450802942181d803403003002106800341d41d19101840000f40045069450310401610003660144000520200302480840700c1c607031012400d41c0031400d05842401800310100080c0b0441d40900c004218064040c3d60003400a1001000300c100c45035100004070145c44040911001000c0d12411220440740c00d0034105010f260340d1000300e200c0e402003442c106039500c0700415504c0c010f03003003414031020340d10307114148024240050345d5551042d4200140c0100c0a00f0402542c0510300421208002c0c440e10800079241c4041038111610590050004010110032102c1185040c0350a180007490506801a11405803c14280700550b440c10446a2145400009003082900070070b44124095500d50301c1d406900c4034028010440301200c01c010f02c5016040a20060500c01000700c0d000440500100303406483c40345106030789005030000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 534285161 1250 534283911 534283913
    0xc0d17070501320112060e0f030a051305030a0c0e070306090516170c0a0e1206090c0907030b090a090212070f0617100e04030c05030a03150e06030c01030e0f010216 72
    0x2c100751140c04840c83c0410002075041c0348488400c143c0c00308008203407075250711207891040c0c4244000c50b0180030300c50403203440341c9102002a2a50b0001d03540b03841200c60b1000000356500d40000e1034100e80c0e070450307451000e060420305103185250000b490309091544807a00040c1e00303a06481241d11490740c5503030780001003070345182c01009044030840e20412840c014080c0101e220640c003c490441585041c05a0062050030200300b9035480000405800d0003044100035410101103298130303142c801101c0b10301c600d6031111002d60460f5241c401b0076411400800006003019840d80c004400c4900082c521403100310354a00042c0342110b2500000c01c400ca0b4031900b00540b90f0040790100814441d02503d0003113240068007100001024443d00800001c8030012405160040076103200030f60300141070b607036034800400000c0d010340044043d511600d100392100050101d80001c106002d0f4030300402070004481c100f001140504a1090340c0307034140c000c44200d0800243c00340700070581000351103025035032a00c02e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 534286411 1250 534285161 534285221
    0x4050907030c080f09010902180f0117071a16050f0d0905090606030406140f041a04050c0d08042d080f0607080a021303140105090c0d17070501 63
    0x54195418141018100c5202c00e8104100d50784c03114000c0601ea541744c1d1180441c80c00340c0318200003c1c0d0401c041128060004c00c0d12001345114400400e942401c82e6030710302c2000c40c0300032000820384d504e03046001d043c0705040440c0150751204c1441032013207052403482e42403a0081d5a014000300c0f041c0c0c2c01002c2c81c3c00b5152040c0048a0705017a94100740b10014544400f040c080e0b90010b15141c45407000000140800003668401c88520302002c074210004e20b0404038404120805480565510640c402c02c01d010280c1c9103100d40c4515808005040c1c400c28140c140000307901000c0c03003154cd01c1014400400c022210200214010030322000e800c10300609054a40702c1401c0a80000319107070081c0180c40c000440004030b07540c0082c06807801a034650f458840c58802805640c884074001c038500d91002042c0000c40840c100501d0203480204a291039106c071042d502e0b111407031000d4000c00c802c520140450311801003d0005400c8210342c40c40c144451380d44608445031504035078031480c4480344500c2d031030300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 534287661 1250 534286411 534286429
    0x109090b09010e0d180b031003050712111020031209190215070819020d09030c0b07050a05010608011e05070905040b182809020907051b120405 63
    0x10110020000c41541e042c403d9100c00c0300844c280f081c01000d4000110185038006810014030749050002c0d240e082c940350990200b480e0b440f00355281e00c80c03031801190200e00200e011212903405203030840c50440c00020f10092f800c41802d60f1080c03228220b1641400aa001c9108000442c0180070359034600140c035034400c02a00184c101207080c0d0083d14058038920070b18580801d20381e0100c0c0c0e61800524410a20101440350700c0000f0500000482c400258411521b9044460004c60b02522046210b4120803109c0001744e10015000b416001000c001c10382c0c80200400940303015600b0340d24105510749502c0c1c2074445a1780a11101d81d52400d401906546540707402d039191000400520540c24003030030080084949001c0c961040d940c4000c029402d9885009007110490001c601c11190714203514601281481000540c42e03a00c00c3d00980d00c4810464460450900d0b07000300301c803c490f00c8861044810760840280030305401942e072010b00d09203404010700103600403030b11004c590715800c100a1140d43c2c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 534288911 1250 534287661 534287671
    0xd0f0219051b03030c0a06020403030e040e0a061805010221060109060206060112091e0b011215050703090c0807060311040e0711070b0d0902040c0e060f030603150109090b 75
    0xe018220400061400b29084400300c20441c6940049940b03140040c1c1940320701407400080c1e1184000780810062035801800c2201e0203500e45003070300540301c400e010503602d5500718690103422554040000946d00d9004001250b108049080103030000d503100ea0880e4851031401c07164466142e010b81100c400548140c2c0e10000a00c2c0c030208040c80c08202942c4c07200c0241405041c090007042c0d07141c1c201c200742c1c0186041d0350001e03501c0c809a03110059548074015482000c1c0c900794403a03800130456110210101d082d080e406040c00d000c13503a04007414402800081c100000b01921410000d0210308950319a801821a00002e80700e550f182c880050108c9507a54060040d0359400d100c1040800301c0071a00d41c0c0e1007007841c01c042c0914039040c4010741c1825600d810000714dc01c00070548d400b08400c00d90003148094801c1c0c80030440400e00700006d980030010b11411541c001810007007003101198a002568200d030000d0200c4150b42c00c1e00c0000e07c0542d00980024080e1503440b45500e05101d0311220b000c2d001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 534290161 1250 534288911 534288943
    0x4060f11013e07080307030c02152401020f0c0613031a0108060601090e0c090d0b070504090e03070f0201051c2d05040305220b03090c01021005280e0d0f02 68
    0x7100f15981e80610900004000c2c500741070360340403100030680c02849040c01c0220501d0140314907113808150510840b601c1c02c0b025205c140c02500d20091540001600507640e09441c005102203200700082141c0b99201c0400c0c1f03d047c0c1c50700c0100000003100d40c18a1004040e419441b09823640c1014100762400c8001408527041050031071080001100c00c220f0690401d1003940c01503900c00e812408600402c8a1840003480346101100300300640c4d034090090015203402c9903051250412030080c42d03a503402090b40240800c04410200001076015800408803202210000f590440100038920115205003080740c3c5006c04c1966006508941c047c8128804c411071070041040b820541c0b002003090082851400c55002408540307030780d055040261000030072440c04c1c62507072490008810b603150780c4083c82d174501501c05c4240319a0440078034001c052044250018900f82c94104030b00400b902c00501242075403c2ea40c4c2d50150621000c14030401e20800c4440d144d884960707104001c02441c003500518079a80d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 534291411 1250 534290161 534290167
    0x303071a071d040902180f1803040b0a0e030f010203010801051005100905010e03030c0105010b0d060f14060901141b0c040204030f06020714071502060601030204060f11013e 76
    0x40500241202e07440603081c1d400207403000951010800c4820018a040711030b4900381300b08a001000500607610904000300303c902400c4d201011140e40e0300503401000903e039400d00c480041548100c183c0141100c000b0300b01c1e108c80110000301400c90740281c105225070b9440788108588a048114440d004280c00d8078a880c401c6400a80102420031a01a550401c01101c4056846680070401c0c1d0301407072040f40082020b541e45041540c100c0d4880a81030322000c1c10300c440001c100315500c44842c1180d10000b9401c043c00445010031500d0b038445c1520a042c040e075510080c440f010594090205804820800b0800c555040001031800750980340d050b01c154010401800090f441d03a02c0205001da0294000da2902e1261800d2a0390078240101c9851510441000082072003245240d07403090b1950f80c00380c81e51a280d910046040e403003580a01c0000c5099140901d1101d07215001e07400540d0f00700390000a0039030b034429842206408007402c0c1d003494561486035500f50b01c9204c40702d4800d83d00152900c0e00d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 534292661 1250 534291411 534291437
    0x70602090f06191d04140610030c080708100f0b070317190f060503030f12060405010509070804030201060902160b060603060a1a090d08040602060612030f09010e0303071a07 76
    0x142450141e2283e410806203c03a00c1d604141110041d40c204800100144408110800d410f61002c401702c40d002d1003074040403d00c91615009200703100d4136943c1079480300c20fa591002c1c001c1da40b6032030182c40c20211401c460310003c0c040400b5100c000161100502059032105141801480444261101c84046c01d00405020000001000d81e070194000d140c00400d00e804003400c0107000380b0071680090341500000404006c00c0080000034041040e0f088500322050302c1d4041032104860003406410380020307002c13021490707a500805050340d10038824400801c25a403100181403e0f600300503101625001909a01c1d010000c8200116900c40016295982189800c40008109140510800c203145002c41050340c0541c0d0300b081101c07000f030740c0586030028415852622481c00c0d8080c1c410b00005000d0740c8049601ca11781a99103060303844c04100250b040080600d44030700903900448440f0f040c04061040c680c0c040d1818000f501066008144500c9404084070313540320114002881034081080d0200120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 534293911 1250 534292661 534292687
    0x40e2809051e071205010f11071506030506070503331008090a1b0b042c13020405070306180c020d05070c0b0d091a10150221040506070602090f06 64
    0x140c1101c6004081440b6041d0742c0c1442401040c184c50f01c3c240340c7d810071070201c18900c0b178503000701410341c0304500140c0052012045441200c42da40401041d64001303201007110036101ea8047c0d81c000c00b560085842c0d007080030290301090030080c6400100200c14004c1140c2e01e142843c2d000c50140c2d00740c10140203524140402c43d403034000c103260040030b5411014650008184051084000c0c1000b0241a0768990700c070920200022414000c1c000a480c000817486544415142054040da000101c803c2e02c02c056542000042c18000b0602404c241e03540130002482180c0c141510b9050904c814001100c45007488001e051460003003518050000030010318001416010040040714003011142d070b01c50300c02c0e020500c06800200000307000e05040b20301e10700b060140c071440540644008418900c0c81507940d50307141088a09002540096008410449845240c000c0307400f102d07141c10b20b00645803945880010758150850391068500d6680451010142d061580e440f00720104120381c070034149140d40c4128 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 534295161 1250 534293911 534293923
    0xd120b0d0b0721060f141c1511190f0c080706020d061e050109141c080a0207090506090103230109020a0b0904060905010b040e2809051e 60
    0x80100c1803810024107050300c01c07008008000038821a20f030401c000156010080c000c24003035000403100a00000460b50300f4a00280034980d0b0150065050301c0852400c188070700070641c02500c000c0c03010601040b2003201441071f0700902c40030f80c03142c5898003070702c400100e5041102c1031044280002d000c0d4000f0305640045145c1040c82c1c0c411515669007060b40307003640181c01090030001c001400d011001c125500c0070041c680380c400c1c0d98844042c08580c0c0f8001101e20714654402c42e043c0854038071402c50740f07040c40d144425070003042c606100c0c41300e2016a205000c5900c6010720b40016009000c3c01c2c003210440380990b941000c0210313565161541551242c4000c1580285040d1100840f0b42d40d030901108290400e10000d900200309204150f075a109220701a48000702e190b1249280c12000319514180b0b1003183d040e81c100c040d103071781060b0820250105001010b03205058040d806041c81120340b0103070040700c2c8840394a4001080d004024900941b0307001d0040c140c1016040c02d85000804003400003a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 534296411 1250 534295161 534295163
    0x50f030c06072108061f0801120303110a110601080604050c060a11100c030e01020f0d0b19080d1209030804170c06041a01060c0b0105060703030b060c0d120b0d 70
    0x54181d0b90446441d02d07805080050050808104104100007840c0e50005807840c803400090b280f00454080492075840b9051a03503041c2d50100322031400510507240c12076400d400103407103420002600b04a803024400c0700c0d0400d02814000440c0b40c5081c54400809011507070041544100601280c1000c4d0780340d5494888074000217001e4400404d200e030440e072261802404a403045000d89001c46040c00c0e1000103040b0041c00840400c5c1001c0c2800d1020340b05200701c0e030700301c10444c800394100041841018080c280e141a0564071201e5003021025900c100342c0f600d001840c1d404010300c0301d514010b1019055111411b14003003160b180101c03810100f80c01c00207480d40700313070302020900c03900003988030030492070080400f10640307445070b1403c100c1001125034824403c0400040e101d401a030ba80d500440c3c14a4600034000e01248922004002504081c0003034408a4401d04011034044020804141c40d80c106610110030f544c49550b030514429009041a003050001c0402880000580d5000c1541d100308018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 534297661 1250 534296411 534296419
    0x4050a03052503020a050c0d031b0507182406120b011b0606051206040215030709050414041a01080309010834110114011202010207090c0315050f030c 66
    0x56066903100034406006003a4038406681c41d240b034203810001c1d92029255001ca80d140300300c1e40c0914140c1342c500c01c4001d00b90303030540da000a1b50359100030751210740710851412070b01d501c164034010540300842419140751051140380002d5000f07012100c503001180000f05540b90007004041800f4041e400341e00d40c0405105140003107020801c0030012a07101c40403203c41e07032070110301000d41e104000f01900441c0031210225158140c1c070a082c1c007501c0c1c40e0801a94002e42c064060744040816061000c090741c0c0c044074604050482d9641d800c04a0140ca680450600340c811034070742004200070001840810741e42031840181150340c10070302050f540e0710451050b02d050254500000d043d0303045034902c841c04c940d43d190402c160919550740b400300d911951640000410410450422564414400d51019100300301c080544c99181114110b4005042c4406034114082c9900100702000c40c1c2c01030340c0252001c1d41c0c00040d40115464482a4540190003962052000035005452070341c00081000300d60304115 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 534298911 1250 534297661 534297667
    0x1b02060a0b1c21120608060f072006010608090d08100501050d11180306070203070804171632100f110d02031c050f0103030f0306170d1704050a0305 65
    0xf0400da28207000d00c2101c0342a402c1e0101000712400e0b8440c25005050344101000d00c1856151014140c4868049481c10719040c02200000e940c103220f01040710b08070701c2c4090403a4030001c121603020f00303122098000c0c501040c4500c06104001d501006040000d202e0b07071034003820904005400c88403d000610880e8100240031404044c1034042d6403120100c0780c2d02c6003aa541e511a14940f00304054007045645110380622000110a580044201e41c412644040c80e0b5241c241042c42000f6892040280301c8003e00c20001c00d0643c00d003404500c03401400101d401040059804c00b90719800d0040d14800507a080c0011164881c65102d0b41203107000141c8070b051062000801c610102c07907100c04181d90959900c41d20304410f003103d40100060030341444070b0810340b80b140382c010106070a83d0300036210040c81c44100001040072070f1086400480c9012285404141940e49000b14514a07551603010140d9410800119542c55004000c43d1404082440c2c0c003146e0b0314040d100c080e00d5811811000d0b090007000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 534300161 1250 534298911 534298913
    0x170c0c010605060408010b030f071805070309050a060614060705070e090a08041d0c0c030d0e030d06140a15021c0302040e0712110903100b12011b02060a0b1c 69
    0x3074000318094100902540e0311070b903492640340c0c0a4440d00c01c429010f80500400d441c020203000c15140145c500800340e000c80d0580d200c003900000d0800510202c109a0b5502c0948002403050000342903250040c070003c1501b500f82500c2c6090052401003903840b4103400c0015000080c00461107a00703c3d4044003480b00190380300102241814950b40c001003800d40c000401044802c18041810080114074503428019035410f1818a194411010118220790041c006070100f102160001d034021220403080d02d046c81401e8500d031040e0b481d16005040c4d00f40c804090700f0828104242c160004080070700038841d00402040010f51105442c511801d0542c540b1b0f49542c20540c06501100d0052500b113100541034585800d00821844008114082060a01c3e07400540701141c072060750603465006029000e1031070100600310040c00400d0019811110310034002c0504031080c0b09200c0b843d80340301d200141c5140808002800c040008200c800054904a020326031902d454940602208400c3d0ac02c0c9052115 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 534301411 1250 534300161 534300163
    0xf0d0e010c0c1203020303040512034c1404090b010e10030b04060509011b0203092704030f0f230c010914031905091813060203010308090907170c0c 65
    0x7150043c5290791500800401010b500100461142c0d0095040d20340040203562003200f9440242ca84051219040384141c0c480c00b501074080aa0801d150340d8808840641e005213003544030b22403c05a4800c4a0715402c0007110384843d03110000700b10454082242060b00d942e02003500606000720f84512016138000341002d005d07840441c000d035070084000e404511f02840c218000d040229406003041d42010341491003001c101d03a10030f903180740c0c80e00035505140081c0103011200300074428030320620301d030041e00b25241c410b01e4400d00d020301e02a41d200d054600c00000c01030a600c55180c0c007101002401c0150b51603542d150b0488820003c0122400d540d03a00041030034601502800c203014040c4040c94101d881c2014000000706141c0e420aa0380e075000d0f000a540640e89409104042a00490085100100d40d017001c4100c60b4070403103c4c0c2205030802040c3e21010f0490300240c0080310400c1001802c5041460b0441a059000d2100d20f4100c010240716603422041c0b0101801184000e500420781d00ca030008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 534302661 1250 534301411 534301433
    0x130c02070825060e09040303020d240501020d08010815061f020604020f040c090b1e030f04030806090405030a1103190504030b0108060730060b0304050f0d0e010c 71
    0x196040850361564040400310900540104040702440310780c14000403094007844116010203002003045c401c660310394034150065486031401c44145580d601590345094010201d528640c3e84801c50015020305000002e40360048071207907002400300a0740108800440050482d0710702c050140c0211040c0c440700c4c08903090b003a005400a810806150700301e194107900248080c4594000c13a504a011103000c810701007201d2034104010000390058206000d043d02c010024145440741407090040d215000c1d42c1e6403016001034509140c2d02e0201d030207001c1817513031006020350171020454911055040966481e81e683c49035410300c0c0b0034001c0d18103000016010501c160ba5000000361100c070a5280384082c02403155109010854041c1c44e460008540c0010010b021442205035482d510304462407184d40700140f01c0305190b9035180c0c02910300301e0b10030404c03503000764002003000205158503402c282c6890703418030038000f0981005a01141c48035052540c42401991800300c00e08200303150007418100038801316 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 534303911 1250 534302661 534302669
    0x105040905010306020a030f0e0703110d05010504240b06070f0303140703020702120303072708070f170c0609010c0606090e0604150b090601050a032c010c02010209130c0207 76
    0x107103004000810301805400602100115070707010410140c10458001c11503050400140e007640c0714000a000140d815410503403401c400501c10009400c4075602c040c01d4520840741183c01b0041c0100e607882407801021006e8081802860a0212038541008a01c042c003035000054046102e240203601814000c3d031180503214940c041444071450001d1000d4040c0d40022412030154001e540085140e19010003500c1c0242e408d56070f81c90708501c079600484280c01d130045082640840c003100000d10460104003140c0140b03071110340c42c00c4592400300c1e000951410400c04c10600d4100442032149503031510100c42600f03009081007483d000c12401d099005081680141031101c2c03500d44210500040007640c82d1189100b56060382802e00e6030710341142550009012140c110801e000070400c55805900903182c1580c1500c1c001980c6c1030140500c014200c808480d541c080303180d000308503d80340703c00c0c043c19090f040c00d40001c3d468419004041030313001c2411031903140d032a582c03240c0c4840e04502c00d2120b14014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 534305161 1250 534303911 534303929
    0x309020a06030c1209080307201006030c06180b03100512011a1212070f020d0f21080a020d090b150901050a05030a110a050a1d010906120f02010504 65
    0x481e1107581c09002041c04090a0000c40c030001a11009840c580c0a94105254064805411520f4184090707981c0700765031070020007040c03819909020303c08081190381c111040840c1e0115225165040881130718005800000411004d2496400c074070903628a01030440c1e000050703160703403030784c0e018020b14941d0480d4000c00e1744419410060b41c8103c0d015080220850210310003070b0f84401141d801c0100d001d082e42c090030f0b1660008845240c03814159000341c00094010301c54031110442690000344480241c000445031340c90080012400d100000600d00403031a10400140031781d600d04400603217a48001014600342a400007002a100d4401c0e411921b80e0640c010380c0c1448a00700701035010314800e1078484880c01142c3c000000140d9161148000b0100c030800f41c050508411561a1a10b0b10740f10181c0090300001d0248000400c1d49034a00300c1401042400d007200030720416005031201c00c90040e4800350300c103401c1800030300840b00b4181c44113092541c004400748001550380700589030344c06581c1c054110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 534306411 1250 534305161 534305179
    0x3090d0c090c110c0d0309090c0536031b090901020f03010b04090b040506060706050402030a080313060e0a0b1602120f0408010b0a2105030d050c0405150901020d030c030902 76
    0x403864000c0c0052141e156044180c5103139503604005e01031225908000036001440c044810442c011b582c1d88900002e000798070341107151804060702280d06030030000b107481c0c03102a0364049403070214403580c041401610440180606803c12600c44180c140e1051a140c0300340a41710110366010000d5040710b0072421a40410f503200d6940760342c03105240d006842460100e41c10021407280c80d140a1151900c540710081c010350511045880c2c150081500a00482c0c1500ca582c0124011610a801031442aa146c49040d00d158400e407a0070019101e4041d000a40c40e0300c85408000002d00c401003555020021a00c5103441103c401d078124584103045030340c010003074000a442d5030681c0c00b40000300143d0385c0300d0000344401011a410300c83c00718a41e11400b0500340a401c01c50500c110f90060f00400c450040007260708041c064140034080310000e840385900e000b8001400c20179410640c0c288001e40102005050030024640d0010f034840404210410400d6580c0c4c21641900f40650301900395140c01401c4660 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 534307661 1250 534306411 534306431
    0xc22020901110f0f070e04030503070c03030b09040605010513090c0e041b0e0f010b0306010806060f0403050102030c07050111040b030604053c010504090215070503040e0a0614090903090d0c09 84
    0x40c1314a01210061154000d100700400ca4440d403200140c0515456520302d0301e1a07950101c00c40d140302007208200c1c00c0645840100d1800c3c0d0f142d00c1c1241c0180e010300d90005039941b600b0b081112000309200d010300c2c4039052000c0040400d1000c940c11084440c00061207130503544074940b00303111a1032000c00481009403500e002c00c25074401568948956225200642503903203e40c40d02e075441c0012243c817800500c48600081e0300e410038201415003a5901d0000340c2c00c0507280d0b95114260703002103407811403500300800c030403082c80000d01801c1030000700e040b0410300d0182016910109440000c00050281d9210030101d03101400700c0e6000b40075050381401784018000d00320484050700a502440c01d451004140005c074280c54a480346043c001d070f00400c540946403001c548003445800110007078445000500002400000402c1da1a100c0c100103a400119281001140314503003001802d51801200780301c040018072038001088424203030080310f114002500718502060b44c50b8494101c00221801d203681c81d4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 534308911 1250 534307661 534307663
    0xa0204090506060412031101150605180f0109030f022205060102010b0109060c031107080601060c12020615060c010b10090801051f033507050c22020901110f 69
    0x2056414200c0c081c0400c1e201c180802180f40070f14010304900c1c0600b4030903200000e00903003524154843c40c4d400856190481c0310507000681241c0d1224001c500b000034824806480441001d41b910012a200c908a86030b520000304041e0381400f00904080b0009180400e560b1740008940070060180c4006541050f1001c0340c40140000395070281c05982440c1000b0b01540c0160204d805a035582c0d0345034800341e1a44d8804550b800392203800300c0d0311402400c1004c280403200780b000703030302030003080c0c5601e40561810b1030701d0694045840c0030081150411020f20500b180042c00072180b00c0d1048601a441c0e024031018640140b0307100d48003503400284c0030382a007081900110340f0011111880020000380c0e07544185610303501d581c0300f41541035500c01c187c02c2c4001910011865903c0d40350306403121711600c050243c4100c10072080a0407140510201d07504040006c10031250684603c01c1d02c5407541076074060301000c20441c0380d2009100a5401042520040e482003c45915520a5400f10760411140c40280c3d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 534310161 1250 534308911 534308917
    0x10020a050102030c040513060612150f0b0a08090f030403060f14101409010819261918060806030a080301030b01030c0816060318021e030f010b0a030b0408120a02 71
    0x107028400480300c2013000701c0c05115100032160180c50307000ac91b88460704014024000e24072041641844540d011504210611035031010300303509415140c1d52842540081d00003040100040c00c9640211f03906030700d1420100507201103030761003507003c100c482c41c281a000c00741c160328007140303e65101541007010310b440028030001120b00c5a01170418054180742030050750301090061803519440307003506514040f1141400120340c0d0041ea14800d1030051030701c004014400030b8000f0b2081010110343e0940540555000c8000c60301c1c142098448444c0001d02c01541c1c8800d4400c0c0743c02d008101002841d07981b0f003400400c4000d54800c100c1c1380d8079a182d181030b07100c1c14420300064079241511079012030481c1d00010340c0d4083d20381220710420400d103814801c601500b054500000c00c1c2c1c40415140c401070b03c1d07030064904001002811000300c8008041814a088002c200d2002903a0400e04510b42c00d48604009005480e0010644400c503500d074144070b241d600c2442d0a030041c00b880c7d1010080f10072035031b40c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 534311411 1250 534310161 534310169
    0x50a0c0e010e010c1106041a0d0f09021305040606050d051509010603020a0b0c07090c05070506060a0609091802060a05070c0e0c0307031e0c0c0c05030d080610020a050102030c04 78
    0x18030044448008011101c039110002c0e0342d400304218090840108078044005d00740b52500518251a00b6111190342c1069004609020f60b80782005c00d140100d00b00c075000c0c050900c1090a42017100001c40d800003a46c140842c100100f040b50340d80049000c1c84203035000030018020180c11000c40340050f240c059500e680340a5528903007902e04020603002001800b4140840750000d1201d4006400d1808040c2d25500000c18030a8510071504002050480c070300984d4008246a1038494880d246410024100314006003170900c10303400b02c0c4051003865003060342042900c844500000d5400b86a811002c003407024214040d60010000c01d0a04030194888002d00d40a4803850520710550759580542c59000400c0e100720303000703840030303c0082c1c4007900c03d44c003040c0500c2c8803104038007000303815410100444207882400000119483c040c14240100640e0f404010032043e0000d10f101c400900000b0030440c009028148640c00340b20704280003c1c82001151522a04400219501e042c01c00f0110307180c2c0e1007845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 534312661 1250 534311411 534311417
    0x60f090703150f1706090c062b02071b0612090201020a0f080703120204050a09090303020d0e0319023403060606031407114b012708090a0801050a0c 65
    0x3a6030607510801141150060f12408001c0c5400c0303140c0e000700310381d94104e02780e03507014202420b10410214552803014210b507039000600503074609603400c040004500d10680461180210342041119503880340d494007481e2181e120010b42c51a5510040b424101402c1c000b0b41800614941442880135090082c03403424400c2d245d064400d40c0c203001c2075059000300d1003102d40c0301186100420841c0c1168101820192091600600d092217582041040304c0d00450b044915520105821188020700c5501c1c10702442e8600081545440103d0030146041000f00c20042c1045044490100d82c400a0902e801035030340814180411915148000c4c02032a845c00c02825480a0074041a2400e028a40480100c0c1c214800352448501c0c3c1c40d10781c4101e00c0d14101102c1c0460b01109401c2c05c081d11200075a0314240b11044030405200048203190a42d2400e50f1003100007800581007411003034020110020b40c0b6071118540351030740500c0002074001003090707120810725400d110400854010345d520102180107603803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 534313911 1250 534312661 534312689
    0x80c010b090c190509130b010927150308030a0e120403050a1205040b13050f120d0305090102090d060c1403010f0b03250906030e06060f090703150f 65
    0x30030040303074050503942030b190540d0030403044100c1c40b4408459949000242801481c1c081248045040c1c400a162180780d074542d1029090030070746e4090201e000511a611180030b43d9009080c015115610501ea2148640d640c0c1c0d0100500c40104c000300c030000e43d0021491605ca14003100358401510745003020f01d00034003c0d0510b0641086150080d0780036250071000070401407203955142c80c15841a842c0c040c1c00e105040c04005021031054009005988610302c10524103403900d0b0502626113854017a1030710a40c0f03110460031102da00000c0c4106210958038022070300780c4401402c2070080c8500e5850542020081001d0810f003c0e080d0088030000035155034a01c0c4210030351481050074042806043c006600100040009019140c0034640142c1070f0032800c2114000b4850a0041d06460704030100030504403503041004542500c280c15260f81032074060001803902c0c000045107000c00c0001d00744134216420104103840d210f64085203040003454200041551074080c03108000c64a44641da508401c0c00c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 534315161 1250 534313911 534313931
    0x18040b1b0901260901020a120e030906070305040f2c0708011502160608060907020f0d200105010303120c1106012601020307050706060503160614090904080c01 70
    0x9050014151109105090101c0c03440110f07440241e101031043d0003064012240041d401460b80319010b4503c01d000169200090200580681018000c81401a1400040460804000c0100c2d02c0d888030455007184d9410407458195480d0289422500c2c07803509003840812a4841e0240c50341c0c0300150719051643d800642d03124081d4490007202c41000003400c803070040250141e024003132120b04005005849840300240c0d0442091f45507540501c0010f0010428082036042c4107905640200c5503102800d10700d40700500f4640d88035074851211080102c20f031510014990120a4403100c100920024406540c1d00c2c02d0080001c0c404000d1024014a40510222003500407415447c0f0125044c0103410030744c2ca001e252125203070010100303140b540c1000840c001340c4413081c40103500c00c042c02d40300c103070b12001241844c0048901a400c528026804800c903e21001c00c203651010842e1a186420310f09086901c1500c1258044c2c5411030b500020003a041c00308000c07100020303050300c0750804002c0100c0152 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 534316411 1250 534315161 534315181
    0xa030e090601091406070605040b060411030403021b040b0607120806060403150b0102010e070927031d03030d0c0203090f060f07030e18040b07080a0507121a18040b 72
    0x141c900e2030104242000410290321901603441c1035100042009040c00da068031040291401140c00700d800d11900000c105d540e183c00e10440030f8041d1925502c5085280541c0e01035501d503140035170704441c1c0400030502c191030f03500e40d040106100c0307011b043e190301c0340000c3c68040020000b04200d01c1c00710300c0d1a00080c00506241d8191f404aa401c012080100c100b5440142d0003000c42d00d82e40c0b811075481d041c280001c070fa410042480207009011b40002d00c06c06d02440c1c10052a01e030907a83c0c000d084c01e03ca009000c29801803c42d070010301d0314440b12001901c80c500282c80d42c442c0c1c0c803031241c800f404c000b2035060142d00403000d460541c0088d2568012442c040040107802d20503440d09240f10b075400e0100b040802d210326603890307034004003600c0700588901840c580d0182e04811a0100c60410019042165407035009a0b16504500300040502040c24504005000100c3e808414a40341e990340700640207a0088445c000407420005d80300e458141c8040d0318ae00072469048130291980c055a00101d806040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 534317661 1250 534316411 534316429
    0x20307030b0111030a0c1505040b04030201050c27030f01060b1b51070e010804022b0618030f0c0c060c11040e0c030c01111c110d020a030e 61
    0x6040000f0b0b628117050242e007aa10b8a0510700280c3d03171075503a0f82c010a0807800340d11070907008071b004104030080c0d8981460300a0030740c4c0c802451408038401c28407410400d0704413a08181c031003090002d480400c855421340403a00d010004110b003404d56080c0b180002d80c61100200a0481d2030507600c885c0a4a240480a00d03511a080c4001014008500c8840c2141038080c28a41080038150320440c1c02a072045401100040b002c000e908003490640300c148905160080030700303601a402070810110303038586500021072045016084e80c3d841c0c156040d141c1d0821010f84030700340d01b80d54801404c108446c988000f8801400c10078508401286c0000d2019250f2806400c0340ca0710254010715000049041210490f01004181c200f00d40c0300311103030694001569580540c848113540030000340000c070b001d5800c01d45401c2140d18004e044c04a06140d1501c11340c000b00303c030b40c4800101c0500142041031243d00301e588003500d02c0107036030b14003915840e041000d502107a21080070340643d982021241c141420000c00403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 534318911 1250 534317661 534317687
    0x32f09043203220312050d06060c11151612020606011404063b150703020601050405090f0a03050409050f060f01270e06040606020a170d0915020307030b01 68
    0x54814042648101c44000c030244203c2c2e000d800e034000c0280c0d030343d072101d07224084104924003081010420b983c08801c2c9210f41802480d00d80752103005020147c80310b099440310301100c1c60044a500248200c2c04040d00e04650405001204c0d401c0714058074200340c2000c1044031046001070080401140d0558071030a280d04205100174040c52070b0514000c0103842c003510080d059090240c1d5044030190507007856030301080c400f00380c241d400000044e000401049060f0480315492549060210b00003013030340006c210381940c000b40d0340041c05841c0c1404075031414805207a0301d074591141160b00001c00d984003002c0d104580c0240014402500e400040e80040030741165540d8101891100c685c04a62090001d00504282e401c0c00c1c40344055a504003a0320a81544c102c4e080d40001f01c2c041c0306880c20140300c4d05006011030b02c00361140b16810f545c0c46000c818240072954060802182c46880c2d82019400b0484c07a82d8000304e01101c041d040c00c0e4100c0a03410481d18480480e1a04103c5040303940a14080c142c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 534320161 1250 534318911 534318913
    0x50907030c1d010c020d11031e0709020d09020a060521130803040201120204120203120408070b07061812020c03060408030c0a030609020a03150602010204032f090432 73
    0xb641d5502c81100d02501d42e090341604000c600d844100141e2200b49140d038000c1c1c0105641d104041e0818181440c3c0f03d1000c0c0003501004001034400030802c40400c014040d241400c00c05030307440c000003160710050320407d80d02075030004540400040301504540101500340c1d5199140d0704500449104c40315004040320042c0c5208101e81d511000909540c0040d035001384141801d0324001011219102260440d0f000742c442540b03003180c5002545010041e601c042c101c0315170401d00e01810401445c0e01c620944c4105d12044001007040010400242c0202407001c4806200806400c841d0034850300c0340b4429000c444c098020340006240ca0f0802058041c4269040a03040e861030321060141e0003140e00c84a41101055650000131035201c3d011b000502c00842541d03804101c20440c3c2844071a0500c147d4001c2040d68810401040021180e42d05c030406105584004060300c1112180c818840070060b4400d94440342d110100302c10011144107160343c40316543d0041100c0403440c01c4c1030107516000ca21043c01c3e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 534321411 1250 534320161 534320177
    0x2701060503130b0c070f050c031912050a09080a12170702060403082707030605010e0106020601140d051510050604210f0503030a020414011d04111b07050907030c 71
    0x85080500403a03040b40040342c0b00e41c6401455211801c2d22580c030201100c0c1f90700861030003401403404202d414198a880c002020100300b85581302c015a811450401c03092200114002c3d06aa026400c0d1800520210041ea00b040049142814074054901c80751008204940448400017142c000501d00c50f507561b400038242d9494a44041ea4030990080083c03030460f1854008007103201c0d0034441703505020001001803402c6411450302d40159001600240b601001d458010000f8590004503a81180e502442c150240b4406101041300e5847e001400303846071040304405944000d1403175103a1b10903001c0c1100c0e284055100c0c1d0811002d071003288110341000e503080705042c64031400b00d80350841e900e1282010483c44061591503d040d504215012400c0550114080282c440d400810b44e18a44e070902e0148850490180b00322102c20314003610b1400b840e5035114441c600302c0c404088911003215084202d03d40020240031942d01da45a02509004205d010003003000382d8040d000c0c44024041c00d40324044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 534322661 1250 534321411 534321413
    0x30b06010210021204032f010204030b06060a02150910051f060504052103070f03170906160807020c031207020a05091b030a0b100f0201150312120b270106050313 71
    0xb01fa078400c5040190104003511300780145414411003691030a5400000340c0c45514500703007040444030050940b030190504020310b01c050340d03020503000c40c00552340e030b8a10280d84603d50624500001d01d059292107070b1070319007402050200f012500d400c02c9001054100b00c1c2da150441140c1d10700032440b400d40c00140c0c070301c3c000d8a04142ca510f0b0711441d003020012a8104601c60b155880001003c01c1c040d80815100041c0752020344940b010140c0c00844500182450301f0b080011240b416298003035401001904004110300500c2071045181e5060020101d8811003058078401e0190703445a03000700c1c81045120300000c1c4506200d81d070144a103611004408a1090300342e07550300d8179400140310b9416566508080c0d1255551004002d040d01d220780e0b145401302c1000000a030841f85615000c1c800c040c0f40c030004100140504801989060749490000c090f04046180100903108400b125644030380d508042040d401e0406003c0e04079208036101d08a0301e640c3e106400d07106440306443e4017844000301c16080c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 534323911 1250 534322661 534322667
    0x90f090903020327090115050f210f0601032702060702011101020708070209060d02031c11030d020a0f110d0302091507060e0601080d05030109090309050307030b0601021002120403 79
    0x140d08540030b40152031070900960709241c4d8140d69070341004c413556400c4c0d401a00c0e07410700d1055213015000c120390130f4201c000c1c00900034106006040e51541800c8002484031394020810050000742080010300c104207040020520403012030864416000a01e404000b6030b00181d001480c1814000b40c2c590807103040080e400303001d40d0740e200900503418000b5205000700741400920082030030314001e041140e01c42c0090310400c0031041d00034150501c151003400340318000d41e4011628241030302e4561014090908181d6054a1502404204910038000802d881d80c01000503002045809d8955072081450768818006503a1a55100c0706018030b90702a140c0c0081d558000c3c0d00800e40360400400001e404040c807406041c481d404004c0c1140c9903a00c4104124801e5010800300e409449010040c0840c000400c000600380c0c04140b1609021030b8980312541c6c181401140701c5009000040c06490544c1d0700e90820080309030081e1400c3d03005209081019a644480b482a04c1158146464010345903c40703403412 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 534325161 1250 534323911 534323921
    0xb04110702300706030b101115060a05181815011208040f06050a0e010201110f0d0b090c12060a0303080c0a0201061502150604020306091303020a050d0e0f01090f09 72
    0x510102d041c2c100007440307240e0b003c102d50300060484d03950109045002005001d818840711249400f0300160001c070480b400e4020034110340c007824101100c0e001c0c0c3e54260006140d818103502050704049519401e2540e950788185a6104005a044690303a0000300e402d2140e40717404ad03810010307441c1880c02c010301011804d035004c0c070161130083ca03040d41425100c1609140c040c550f50300c004042940000c2900c0515000610b00801322801d00007000611442c41d8071030b10300d1140b10300803544048000303114012168039034400000070302d0103030405006180c44070001100e84d0040c41458003000100780040c2d064508600b5201c07e49a06d030380c3d00d0350944c131000d070007100c00d0300000d90707070390655488107804100f14132445141105182d15030b00820400d082ca51581313001000180030940075600420401c25283c4070b29400d1a002a0700350084a00ca076070700d050032400c0000c3d01000030460f0141d2b0751060103160380243c0003070641d24129146e202101e14917006440c0c03128244140c4000c00c0f403202d810801e4030210b03800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 534326411 1250 534325161 534325219
    0x80304050106091b030509060f06150715091502031603050423061609050607023102090906102703020d050303011a0705060c030a110a030b04110702 65
    0x407500b5902c440d01d802c15540340540c81a500b09103040305007803440e4580210313900301e1001c001408d02800c12000509221800905a5002d60407540382c19050405100c1140e501a401011002410940c051540c006d00181801039076080c0840c000c0840c0d90041e4801c5901541a9544240c01541c40c500c061300603010040c070641c2c06010314480c1000307205e5595007901203010250041c06945c504101a13074900900507407014104403202000b8081500c0c0c54081b42e40c01134044510041e0010301c0c03098046a0141a1072224000c80203070020803500c0180d401801031203030202c91045a0703564090922000d200021910400540a81c408003400c50131916010000060017001480d02c1d03071a9000b0a031450b288034011640c03075200000420901e141d122860303140007081440e0918103440f80e00c443e581da46000d040d594400800001282c1c0150196001c0002c1c46007201c421500c481010744044e000b85089100c05010754141075003800d03111381480031502e620f54000e0180607828010900e4440115500c00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 534327661 1250 534326411 534326413
    0x10b060c060f060f030a0b0403081b160c080304030c080106060302090916050f0c0703020901060203070201020a060f0605150306010e0103021e2101030f120810151202040801090c0b030c040308030405 87
    0x311000d1309441c24013a01400314002c2d10b41d804281040d24005020280090801c0250982c02c0340080c00c901ea510100e403211703007507140c840319080c0325070a0038038408240717600100306031100140000801100d060180d0450341d060000700111071f951041a02684a010f2405a001d081c41c030000c0c1890610381304144021a040c5000c41c1170009004035040e40750b0045102e142c1c01d5000a008208520340070b01498050850741c8051800d00340d095001030f540e200b002200402d42a203c02846d161441140c0c04400101401028054100f40c0a01010010341c0f060783c09078000f4041c1c00b2041200d500034000ca440607080c82401a48150500d0041c19158106200c0003483c0e01400d24031008000b008145c0d81e029500508011b404805649013010000942840040a03c02c0040820102c65203808150f41115540d803070094608680d51000c6848402c00c0520039102e51000c140460109415407000c0c182c540b0600440e09620b45803490180240005c48099140312010001403002507150000386401c644500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 534328911 1250 534327661 534327679
    0x151918150b0a090c030609111e1204030f11100f0f0b2d151908041101030939050a0302030a021504030c14040b061204030f05040f0b0c010b060c060f06 66
    0x115500042c0c443c200c100d0000c02c8004605002d030a80840b002484e0420070712809e6150500001c0d14000071308000b040901801000e5016425080c001c50340064403032002c1043c4c414104409058000134410746029492441c6040003903011804607101d5892003810050400c02d41e000a0f000801d02d0000c140f488000300c4d40c4541102e01a40c0710071802119206d41071003115152810241c2d802200315420010a0410040500f408040b80b644030300c44660340d41c203103800b08000042c0c0c20600010200e0444006c074a800110f090b040100b400c9003031030f0107229003140d0f2003880b80c0d80b0300400000100701d020281d415001000c0150061900a1002510b5090342101c0c40c180396907a00e484000f004254400c0c02607082140d500303011894503204103084080c00321409810b0540c5041e13020400e8000500040a026480021010a0b8020002c0c0c800800720a940103056a03200c10ba02c0105e5005000400120340c00c00e1b104212514002c030940700715050110080000b5502c2003503100d4440c00241c00c180d0080122 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 534330161 1250 534328911 534328919
    0x903060c0212030c0901180308070b040807081801020c15030a022a03091912030804051006091505041103220f06051005040b03151918150b0a090c0306 66
    0x4080a113102d030341320703803011500c2c0d43c20742002500741c010065402580150540302880080c8031002035950301c68100752110662341da50325004006100c2e080010703000007000714080d0f1342d011310ba100ba1820b40720203900340c0784145511800c0c0440c68410501100c0500c09c180001a0041d4003607001e003074803064010103101e00d02c1d0301d200d2020454540182091081d0000a1110800c0c18940c1c600191806080e8184060b203242c440c0044c0440380f000d40003001c025200700418144001005040103e200d41341040254503a03400c1c40200801442c681620070505100c070008981c60107115800c0030995543c1550325660320514550208800c250405c0d480554121000d8007044607a50500545071007104005198141255407482a00d80780e40494400c030b060aa1003041a240031440030b5480300007400303050003601ca43d02c1c440700d400030341040300d06c140349080d00880601590101c1400f84e00d0107002c030003100741502c641c0c14003a900d40e000a56000f062100c02084400242d9001c20f0b0400d0040c0380c001012515 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 534331411 1250 534330161 534330193
    0x2040e120a1e050a1b02151603080903031623040f06110c0307120609050d020109022706010804080c1203071103070c03020d171c05160903060c02 64
    0x412000000034841282400c514106100e48240194aa041041c02d10303591880082000344d40c005e86004038855441c50504540719122000c03144a503500d14962500407100a000440382c550b9802d40c00204540081129000c02104880c00741e0310710703000c0b001c01d400809001d5902d40d0000000402c940d074004a40d2403d481598007502c050107006d44c204505500d40360b4020800402c04810003c5900160300e101c00643c1c001406108490409904c54403142407418000000c0400d081c1c00f41040c020380d411100d00c103906502101d28207200711100e80400c222480035022901c0d0030804180001300c07900c0071605a41c0903902030b6a005218840842c0b900c40d920035143c2c213201c0004c44030301c0c00b03680103c1802041900021420102480391004500340050340d100c03050112054440030b0301414034032400000340b049041c00102061710006409955440021054419514030b03203001e0745a43c6050301240032052032402040c40c400c0f00e940c500381160b040d5202c40d00103060003a018810740c414144a4040d00d42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 534332661 1250 534331411 534331417
    0xf0903151009110c0a11040e030d05070201050f09070506030a2c06011208040b0d02040f0f18020301052413030803040c09050106021e03040e0103060218030c0d02040e12 74
    0x40585a22940c1807a0240341c10955100b043c90502c911070a112042d02c10100082c410300c0700740c00001c1d000e51040280302050041c4204e024042c0d090000190642c442d100f5034103c14012652503008110326962010341410780b80064484151582143e9410400c1d494a40051038114030001130000c1c07480c8299040c490f04518201ca280000004665802030701d000a01c43d490060aa1105105200005035240c0e1041d11481c02824008036000c1a40c182c04007807035050710f003d270540030344c140c0c051a183c8030146d46007101c078404c0c00405c046d0007410f454180f000c0c2c001d5a0407107801400e1190082070285066001e21200c041003d0402814409034510010901129004500441049d0b41c0d906040c200540360300e400c0c5c2c2010140c2811300c0c0040100c2507000400c05041c2c000c0d20006080c00b902400e1450844c8250350018500040b28000030040c8441a4010300b21903421060025605414006044d1501c00000903030382c1c0320401c80c8110026003480d821607485c1c102c6490659a00001a82c0190b000760 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 534333911 1250 534332661 534332671
    0x30216140601060806032806020a18140f0405072102040303080c07050d0c03050c01050123150d0f06090c0e0909070e061011010501090c0f0903080f090315 68
    0x200320350200e0900014103211041c094140d91030601d8492503d04007180d0344651842c50401c10030107c411803101e460200c06c82c0203c45078090810b556403035080f1001042d286d8554040c028011046800048a050726801c2d03520100015100d0304000070341804200c000d013001040d0005100101c55040309180d0442c8006141c801903610058940d030442c00c1c024503240006040300000b0f0810030400021507400244501281d241d0b1401e22004000d51508980d10b00403100342041960a0400106202040b8203140d101030018041c20f00c10701c43c0b101c04009440c80781c6062001a0141044042c12184c0c03190015242162440004102260380b9101c8000f202c61100740c01d00099540701034a101403074140206074100c90603000900c000e81c1056000e10003004003030300b07040c03054030028450b0080750b0241d15662140700d0300e41c00821082da92043e40401818004000c540015100f0f4908036800d400b8108074010384c0d803c40d590300d0618981c03c001c2c00140d808080c10651520035811911400241103416510034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 534335161 1250 534333911 534333923
    0x40e0c031b0d0f241e0b070524010e090102120a0b0d05060906101d070507060902041a0112021e070c080303041b1205032d12010e0f0403020a0b07030216 67
    0x1c1c15071509091a44085600692005050f8249500e08941000030b101c0c16141e840035103a030f40b8102441c15510780304102c106581382c0e030704110640b204120018a681d0489402035042510ba580d1141407500700d10580d11010713f004001c1001c40c50b000c4c1258050810703460040c24144c98a80c1603200e85292150840d4132501c1c076445a41006030001c0d0b0841c0300c0c8014103080080b03124500a400c00202d03e554010045000c00c00003095034824098a60000e40da140d030090000c0050320040d1520900801c80904113078003007480144490404101032084941d0418124544004000300c41c0b0b540400b5440b8000551314081242004241000244011406103204060fa54a08482d4041d404105003580c3d000e1880d820350a050200810f0001c000c032201c0200075410594040004c8440d500030700ca4921400d48412404200394030b02e8442d0003006c50503a042c1c000c0d00c48031651a0301501c00c0303102c0e04440090041c0c008140b8000021088040344ea04134400303080160a0405909210003041168002a115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 534336411 1250 534335161 534335201
    0x7121104050a060c050d050a09090501030b060f1027030c0b03070906020303070906050706110414031006050303120411100c021305060f06250305040e0c031b0d0f 71
    0x2140c0780440441006080c24103104d0041c1120761581900d6114801d1918280700c40054045040340c850300050003c1d1405180812065840f401d02141d05202210058045c140f12107411029107003084411446900795031b507003003c10300141225480c01c42e9014074020404440140840010301c074000e47d03400b07001c000d95819140d20f401240100741c1c0e5416841081990410400d020b099a4000d0745038059600c14141507540d00168a070100060400101c6164500c0c0d001c94080380b500d0b50b1044aa0821000300c00f20b03030309603000400c10000c440035407007441d6059000304070440091821201140e801030250b0406119580d9a0000c16001500b60400200003030b069205541185446514001841e000000c10030a03494802d002c140006989410b081c407514010541c00403038507810300e11281040d010706502c0103042191078040c003250018090020740d402100002a0000e84400503248540c0d1171140d0440240080d483c06060755100706626000d46485110404802d9618022440202151811551 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 534337661 1250 534336411 534336419
    0x60d020a0f17010b18010e1905040e1c0e060c01090507030606090507090303110703200f011d010804140613031107050d0809030106170f0c150307030507121104 70
    0x942c01c50640400d40903041071006001680c2000b003035641410b03080114815100a010050720364903045042c05510041c40c000c19085180507030040c208458042e6030502111502554194540800100c10300d40d40582e0408884034130300c6000010314444000c0e10b05490280070514042c00d4503604902a0350035030201c4010000c000301c80c4075250052040840401c42c0e418503210027095042c0c2440b019080004101c03100b0000c100521240d4001e6601c85046210311003c138040c40e05000c40a810741d07104446540c1080c00c0c2e9405242312542c809902150100d464681d04015264100041c000f911215241a08040540c10400c081c030700628075081c030f246c1a500103160043c010100680c280c8500d8101e40c004100b291500660011841d41c0b121400307481c0c00c00c4074042401003c40c0e600481403000c4003c12000485408908241c008a0074003d0b181d18a030418180117101113100d2004110b06002c0001481c0079109031302c1240c200c0d4291501e02c0d156400e00c0c401c0026910600781d120311400000400300 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 534338911 1250 534337661 534337667
    0x30c050a0f020316031a090102041724010b0409020c03040306140f0a1509051509070507120e09010e0a0905012306120604120c0206040303110c040b0a090b060d020a0f 73
    0x540340003130007080041d41c29680c510281c102d01007032a5030030610000102d41c07105000c3d01590050a0401c087e19500107002032080e40ea0000701c43d4202c0040c0c0350030243c1800d406c00580f0340707058801081d0998905450010741d94000d5224081409013400f041c000880015002d01070040c82c0e072065031440a160a00300445100c00002034400400d50b071610845206100240314440120790312046c0015460baa4520f070918060070520321258050344900400c480d145c1c1040107000708034011100000710120107181a01da86068290b4141c0c000280c4004000300011003482680c03000e48a803000c260110140d884c01d080d19116035140040c552000c4100c2c61840d841000f55030301100c1150407400c2c000341c2e00105074803004050310103803400f1034908030168a05e000e48010400c56502404195980390303030341001041034242440032070303c90040340790010591410340a040c1e40b07030b03030020041200c2c985080810030003031411004450300070780c0c14011022184e1551026000030b0840351110b0f01d110041440c02 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 534340161 1250 534338911 534338923
    0x60f0e0f060301140612030c0a03051b07081b010c06050f15040203010b070b061809060703291e12061b0c0c040504020a090f0605040e0a05030d0504030c050a0f0203 72
    0x41c50003680341c044082400351401c012250014016101c92425840752560a8110310a0300e65060701f901c21045e920b4101980700c0c000b000b441e040c1201741d040200c600c2414503104c0e5030764070580c0705681c4444402c501d0080c042c0305c5000030f85070504110070140125503480c4103841c0b01700c4940b440c40c40310108010f165001c04030f20052090080381c1c1145191b0401c051a400d0307014241c0054986441c01c0c00045030b607203d040e0500880101d5008030b2030286003250310107a80f41421078800c1c2c0003904002e400910181440100000c01d00000750740d00e103c1c4070800501107803990070f80c44266911500b03901c950132a1211210b11100c01d0f4001c015050702d10300f464940384092001601013030000020007050b19141804181c80c500350408031400305103503c840c00015180b40300c40d00400741c0146405542860102140c2c4404c0448a095a00f409a0340546040d02d0720707405210b10103000c03038008014030448455207601150307006220b8101105140b4554031945e1130700c588644110354640142c40072005520707042000d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 534341411 1250 534340161 534340171
    0x62106010611190b04020301090c0e0a06050d0515091c090e1f0902091f022a0a1701020f16110418030f1e1d0406080718060f0e0f 57
    0x42510901c1890460030034140300703c0141880042e0400310f4110354080d04540c42c940e4000c1c5460580a0b142c50382040d800405840c2c20300b682d460310000152078244010b413085441d800c4006802c03d4112040c03a500c0446005003a04240d01032000040d11380d5941040100b000051030381c51000490a014955603005000380801c0e0440e02d080200c00b40c40d040303800c801c1050350704a19015031076140045c040f6031004400c10011901140340080c00d800030f82c0c00905141c103101010b070403040c0030201a1070143c04120403240c203600241408070520102d04c003600e0f0000c0f09060380000610705801075043c49015006440d031841d00588200f45c94090214000c00c400c44000221403c00002c03c094006d121000a0074030000c00f8400250425401640103104241c561805d00b029860030010050008058030140301d0440105c001c030302c100300070764103080c85036505544181004041003404c01c040c4003091000701c040d02114a45441c000305a81410704180340003444000ca0b9481e0606064181c0c20030f140000305 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 534342661 1250 534341411 534341413
    0x9090a050723010c0302070302090103080306130b13150509040f03140405130b2e0f14030105012a0302100c0219061a03190201030c1b030503062106010611 68
    0xa410b2803400c0414002041014242800000e1403d1894241c1c01c250181d400a0b50008004000005005904000f14400e03039089640d4001c0b582c8021440701110417640b1030341d4008942c0304d0000b0106030aa4803175030442c80700072407601100780c0d228005004a24112021079484990008072020160403080800341c10741c07103144a500f05410711001c2488400040028500316442d105107150545620700041112040e42c0450242800307a01d9070140e401401105090003d20304880740206640700341440442000d0260140340340d80d191400441e140d0410280e200421018802c4812450f5801140c81d200b039803007500030b02280d038a2424450211030342000ea00095400c181d20901c210506107070000b15441e4001000180d4004840d0741d0942c102015604540510403940500090b49650100142c82e0303100b6a000c0c800c52489840807540546c110744c002d01000500d140140001380500095644500e000d4a200e2160907480b2001d18500228004140a900700000600900350720050f0424501c009034 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 534343911 1250 534342661 534342689
    0x191502061006120f0f05071106010510091401021e0a031e0507120905031504020f040b0607110f0a03060b090705040b09090405104106040b0f09090a0507 67
    0x40a82a03910303d0f484400c3d900d550300703900c880e070084030350050003032680302d000c1044a454140400b6185000d081303072481c1181b0400c00001800c1c940b030707480301100700c0b4290b9076080814900450040e0206081c9030b00d0f419400303208480c82000201c07584011100e0f80c100010103001c401d90030080e041640528480000390068281c1000d101d410800303c60780b195000741c40c6484102c144104441c0a03109800440c1e241c00b810100c00000810002d03624010345c000c031904591104040c007080111454821052b400000902807900420340c01a020328040202901c00c0140401440015440e018603400842d051070b074421031421141000c0441c0b5034400801d052161419003461b0581c2c0343d40c014008035070b1003030314000b00180802c102405034000c00021540700344414807000314040e00c585100d029002042c880d0802d594101d2001d07038145041032401042c0105952544c40600c4040c110014859411103e040d0f8240155112118a244030f040404080c20710410039150850810209a1000403000140 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 534345161 1250 534343911 534343919
    0x90b010203041203080702010605060c0a050f03030417070c030206030109020c06071d10020c060a020601080f030406120b040e0f1f09020a21050f0703060b01020313050f1915020610 79
    0x40f0480600007074050800e48903076a140c480c1203000d080d03d40c01c401d800c128082a19122181c002030400d13142c51058042c0c0b0287e000000310303d40c1c1c2c1e0204490240c450310305a44d003a1844841c0100914000b80940050000f2036160f40104801e03510a0f40303c5903025a0004000d1040d103010311205410a15038909260f088078848001311000a0503203c1c54880c68a140c03800107810700802c400c00c4102c80140c0410745440303006e41e010303465074001d10800507140038907088078003da003011040310b05884094442070b0500094500104c010248400e003540c02581c0c85000b8050840100300305000000c0607c000c01c0b00801c1d02c5150342c0922040c60341c0010843c285126000141e86150340e9805840b0070b000310412007820b14903810340109000b107014203140a020b480300354000f070108a40003034034000c02040c041e41031100300490b41c0348503610b40c14210640500040c005442c102030100759090300101440070700155075180b40c0c41112580d00c80044a0421504091010f805000040d0301c08502d1083c1c0301910701d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 534346411 1250 534345161 534345179
    0x1081009090f0309210b130204090c05030d090617150d1b140603041515080a020a0506070b070e040b0a090f0e0a1509060219050703030e0f2a03010c09090b01020304 72
    0xc214006c0c000042000018400902d06451440c403d030014003d0101e0718035414084549083c50140c20700901071a109000c505015002c9007044550036036901000003c0708116805054002d1b00c0c3d46000308034900c01d09103030350340c6003c038400181c0201744d11405040c1c08001d00c0303084542c0e6032040c044089456040d0480d6620071003a02d40c0290051080700f030401c1c0480000c0300600d80c0e0114680030100b2507a0102d10820001358030b5030014401e940c003440e0152500200702550045000007000002c0c1000040c8000e4400d20300c10b400114042e101040300d031074980020703443c64600d40164200e40ea40d005400301e085140d0040f10107144604001d0034451660b51640140328004030501d001180d00d440b0350320101701c4c00b58121a90f8034460301c2c0f00c5810303150004c0000c01c583d21007142580000e0a000003020201400704612810303070004030027024106c0b49488150541650700490140c4004420011401500c00380202e00c140d00080e66014001810641c1c500c040300c141c0e02e0900d0441d40107010034403458013 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 534347661 1250 534346411 534346469
    0x319140d090b040e1e040b041103010b0607060b03100f02090a17030a230a08070f0e011d0612010905010305120a0e01030506060903010e0c04181101081009090f0309 72
    0x2c16031001d840c0d50792071071940c1e1017404c11801c0c03020784070548500300003d0022540005004503c14400780602c00d401a0402d800e0360401e02a0f6070b440b54080229100140440e0300c04c03a0480c4000d0140c1381403032896100740040380c0305104503450450f00044c00640741e10308200321130060641c1d81c00000c21041a0040705a0703038000c0200002c00d00034014030351400303204441980035040401d500b5243c1e81e89040f5030b005140344010b03600c07000410100d18840c6203490044240c2150101e06a407505009141c4440d610818070140d035550741c100d40300b04901c00704071441d90410b50180c0410080440c6135407440c580503140151548022201c0383c0c1c18032244400c0c1c0e6104602a68a020903e00801c068440c00e000405a100c2e00420603415860082926010b007404210030b5503600781110204022924008100126188024000c0a0f01c18500e903244a0f503011701042904440784059a600f4146c56868007400c650881d00259180e608903d07074401096800350364000503001c0c003602c0f041c1c0003500c80286900c000e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 534348911 1250 534347661 534347669
    0x3061703160b07050d0903020a0c240e011b06060501090510020715110610050a090603020a03060e0f1e061e16050d09080c010e010c1407020319140d090b04 68
    0x10140901203500140f103a0117843e000945040100007500e4141340103940c9000e2010f0845d00b480e5504800540c0c2841c42c1c0c1012654900e010302190b00e03421220703040f07601e41d0194150a060205003001521030100b0305ea00c1c64070b0644205000940d80f418040090700d510810b0b4080ca01c074103401407201030300640c081104400c9504403400c060040355021130980c0c0240c0c4017215450503100e80d004006002440018001c103c2d081500d004440580715500c18080c0c031844c0c000a9000078002c5030400004003103500403400e280610301a6404030740315841c1c0703504182d0385052101107440d20b52045a0b04600a210075034000c000900141403048451070b044400b01002810440c44504129078104224060b42c06c50381c148943c294104601d541c00d10b010919500300303148102075580b8003142d44a603028140304d00c160300b01c51912000f006120f05181e200c1c260f840580126014055081141c0414220f569250b28451003071001a145409003500710345841501000b0f1010003108150401003401d0030000c40e42130f2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 534350161 1250 534348911 534348923
    0xd230f041a060d0b090309040f060f03080706020403120206070311090a0608100b1c0e0d140c030d05040b0a050708010303050f0c1f2003010302130507030b09070306170316 75
    0x5030303204000248402c81114025159180003070800a0005c000300041444100131641000500903000c1000100e507058001c1d446041a0403030148046001c15020780302d0b61384107800140c581354a990300d0b510558201c0020001582c00542841612a01401181c6880b01c4100c95070f41081040b4000a00e0500188500d60501131514042103c603910021040060314860810a07941e100a200290588401c0c0600c00c81031481e00019502841c1c0100341e0602000099885c04440d0990b060b10f010b2981c0411349400340352008108001c8c6290302805128801c5001d00c3c03610001d0701d4180b5040050b41e000500000411815000500000ea000429180318038603221020b034580a404510b64680030105540b03889412a401f20001c146070307550400f140654442c41c00303640a03010030480b04014002804020b611880b000604000340300f40ba40025407081031850041030610703000020480321201a0303504800681c0300d02043c400540c9980140114070b0fa868001e626100c0a4111130b0000c0d24015002090 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 534351411 1250 534350161 534350213
    0x203060f0f010302040c05130807060f0c05060c1c0606050304020108130b0c0906120118060602030a0801060f03020d0f1d07052101090203070906150e030d080a020d230f04 75
    0x8031b036120300e041d5051464406403694032141c84100391580d81019104241c0002c841b00e8105000500c02c042c2d00883e03071743c820003e005a80f58003140c0e229541260103100d0807020040604041060340b40500002404c20f074032803c2d520700b0280001032181d1801820703203040c2d21030100c403100003403250800c556114403007251103900c0c1d01c0f480c0001500c61040f65004e040d129181c00011605001c101d00200e840c102c8c0800030880303940c0d00c0506980324082d040401c00400c4100f4010408140103015105030f286143c64014034002042110608946101e4503942807640d03210152041880d1100d0b00e18002c0101d04014502e062801c0c0000302e00035a41075145902440803801c40b0103110094200c40c925540c018103440040e5120b0401c94018030030351041e022812039150081c4802c0d8040e110b9141c2016025019090b00070487c5d2051342d04610103411002c150350f007003101c02d66500c0700c3d00c00e2040410400c1040302611150420141415001414910248101000744800621190301400c0515290b05d0a800d03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 534352517 1106 534351411 534351431
    0x60c0a03120c230a0309080a051306030b0607110301020403080c0604061404030c0204050702070b2b02091c0606050301092a030b3d030203060f0f01030204 68
    0x480458040054001e03643d0b000130145000507003804100380e000e540d04e90a113640190b86250000320f010030481c04a400c044200c2006058070b20303040c400382803000c00240041c411602c0090445004001c0c046041d00c084d0140c074011a0001601c40d20380000b01c2450b6214581160212141c41c81c0c001c11009c1d008514410341c0c0034a416541d444402d03c526800d0000804001e400c10056200301140020926400b80052440340000c04481c4002c804002149010762041c0c48409a858014800d0052a40702c658420a50901000955030300c4510b82c240040200410340045416508150b014000d01841208401e41c081d0324840c42c0b4800010041c1c40208184103000c020282c50a03040440c6260a1003020740000101d5106540c414a801e9203c2400080e443c80c40e03500c9202691344200f09514041c842980c3c050842038814015203890704e0011812541400001d210b43d5407444811 = true := by decide +kernel

theorem cover : BRFrame.Cov 534172661 534352517 := by
  have h0 := BRFrame.cov_init 534172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 534172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 534172661 ≤ n) (h2 : n < 534352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
